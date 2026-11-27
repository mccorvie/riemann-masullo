module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Averaging quotient tests along the norm fibers

On a radial Hardy–Sobolev vector, integrating a compact quotient test along
norm-one fibers produces the test for positive Haar convolution.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.SLocalRadialAction

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

local notation "P" => ℝ≥0ˣ

local instance : BorelSpace P := borelSpace_units_of_continuousInv₀ _

variable (F : Type*) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "J" => SIdeleQuotient F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "N" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "W(" a "," b "," s ")" =>
  CompactIntervalSobolev μ (fun x : J ↦ Real.log ((Units.val (N x) : ℝ≥0) : ℝ)) a b s

local instance : MeasurableSpace J₁ := borel _

/-- Paper: Step I of Theorem 12.4.1.1, pp. 515–516. On a radial vector the
actual quotient test action is positive Haar convolution with the norm-one
fiber integral of the test. The fiber integral includes its Haar mass.
Deviation: This gives the radial quotient action before the cutoff composition. -/
public theorem testAction_ae_normOneAverage
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (τ : P →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (φ : BruhatCompactSupport J) (f : P → ℂ) (hf : Measurable f)
    (u : W(a,b,s)) (hu : (u : J → ℂ) =ᵐ[μ] fun g ↦ f (N g)) :
    (hardySobolevTestAction μ N a b s hab hs φ u : J → ℂ) =ᵐ[μ]
      fun x ↦ lcaConvolution positiveRealHaar
        (fun t ↦ ∫ k : J₁, φ.val (k.val * QuotientGroup.mk (τ t)) ∂η) f (N x) := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : SecondCountableTopology P := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (η).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  let j (p : J₁ × P) : J := p.1.val * QuotientGroup.mk (τ p.2)
  have hj : Measurable j :=
    ((continuous_subtype_val.comp continuous_fst).mul
      ((show Continuous (QuotientGroup.mk : Iₛ → J) from continuous_quotient_mk').comp
        (τ.continuous.comp continuous_snd))).measurable
  have hjNorm (p : J₁ × P) : N (j p) = p.2 := by
    change sIdeleQuotientNorm F S (p.1.val * QuotientGroup.mk (τ p.2)) = p.2
    rw [map_mul, MonoidHom.mem_ker.mp p.1.property, one_mul]
    exact (sIdeleQuotientNorm_mk F S (τ p.2)).trans (hτ p.2)
  have hprod : ((η).prod positiveRealHaar).map j = μ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  have hφ : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  have hφc : HasCompactSupport φ.val := φ.property.2
  have hφBound := hφ.bounded_above_of_compact_support hφc
  filter_upwards [hardySobolevTestAction_apply μ N a b s hab hs φ u,
    hardySobolevConvolution_apply μ N a b s hab hs φ.val hφ.measurable.aemeasurable
      hφc hφBound u] with x hx hIntegrable
  rw [hx]
  unfold lcaConvolution
  let k (g : J) : ℂ := φ.val g * f ((N g)⁻¹ * N x)
  have htranslate : Continuous (fun g : J ↦ (N g)⁻¹ * N x) :=
    (N).continuous.inv.mul continuous_const
  have hk : Measurable k := hφ.measurable.mul (hf.comp htranslate.measurable)
  have hshift : MeasurePreserving (fun g : J ↦ g⁻¹ * x) μ μ :=
    (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
  have hEq : (fun g ↦ φ.val g * u (g⁻¹ * x)) =ᵐ[μ] k := by
    filter_upwards [hshift.quasiMeasurePreserving.ae hu] with g hg
    simpa only [k, map_mul, map_inv] using congrArg (φ.val g * ·) hg
  have hInt : Integrable k μ := hIntegrable.1.congr hEq
  have hkProd : Integrable (k ∘ j) ((η).prod positiveRealHaar) := by
    apply Integrable.comp_aemeasurable _ hj.aemeasurable
    rwa [hprod]
  calc
    (∫ g, φ.val g * u (g⁻¹ * x) ∂μ) = ∫ g, k g ∂μ := integral_congr_ae hEq
    _ = ∫ p, (k ∘ j) p ∂((η).prod positiveRealHaar) := by
      rw [← hprod]
      simpa only [Function.comp_apply] using
        (integral_map hj.aemeasurable hk.aestronglyMeasurable)
    _ = ∫ t, ∫ z, (k ∘ j) (z, t) ∂η ∂positiveRealHaar :=
      integral_prod_symm _ hkProd
    _ = _ := by
      refine integral_congr_ae (.of_forall fun t ↦ ?_)
      simp only [Function.comp_apply, k, hjNorm, integral_mul_const]
      rfl

end

end RiemannMasullo.SLocalRadialAction
