module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Support

/-! # Additive tests from norm-one fiber averages

A compact quotient test gives an intrinsic positive Haar profile. Dividing
that profile by positive radius gives an additive test supported away from
zero, with the norm-one Haar mass included.
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
local notation "η" => sLocalNormOneQuotientMeasure F S

local instance : MeasurableSpace J₁ := borel _

/-- Paper: Theorem 3.3.1.1(3), p. 129. The norm-one fiber average of a compact
quotient test is continuous, supported on the norm-image of the test support,
and integrable against positive Haar measure.
Deviation: State the regularity and support of the test profile obtained
from the norm-product measure. The average includes its full Haar mass. -/
public theorem normOneAverage_continuous_tsupport
    (τ : P →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (φ : BruhatCompactSupport J) :
    let χ (t : P) := ∫ k : J₁, φ.val (k.val * QuotientGroup.mk (τ t)) ∂η
    Continuous χ ∧ tsupport χ ⊆ (N : J → P) '' tsupport φ.val ∧
      Integrable χ positiveRealHaar := by
  intro χ
  let : BorelSpace J₁ := ⟨rfl⟩
  let : SecondCountableTopology P := Units.isEmbedding_val₀.secondCountableTopology
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (η).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure_of_lebesgue
  let j (k : J₁) (t : P) : J := k.val * QuotientGroup.mk (τ t)
  have hφ : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  have hφc : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hjRight : Continuous fun t : P ↦ (QuotientGroup.mk (τ t) : J) :=
    (show Continuous (QuotientGroup.mk : Iₛ → J) from continuous_quotient_mk').comp
      τ.continuous
  have hφFiber (t : P) : Continuous fun k : J₁ ↦ φ.val (j k t) :=
    hφ.comp (continuous_subtype_val.mul continuous_const)
  have hφAlong (k : J₁) : Continuous fun t : P ↦ φ.val (j k t) :=
    hφ.comp (continuous_const.mul hjRight)
  have hχ : Continuous χ := by
    change Continuous (fun t : P ↦ ∫ k : J₁, φ.val (j k t) ∂η)
    exact MeasureTheory.continuous_of_dominated
      (fun t ↦ (hφFiber t).measurable.aestronglyMeasurable)
      (fun t ↦ Eventually.of_forall fun k ↦ hC (j k t))
      (integrable_const C) (Eventually.of_forall hφAlong)
  have hjNorm (k : J₁) (t : P) : N (j k t) = t := by
    change sIdeleQuotientNorm F S (k.val * QuotientGroup.mk (τ t)) = t
    rw [map_mul, MonoidHom.mem_ker.mp k.property, one_mul]
    exact (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  have hImage : IsCompact ((N : J → P) '' tsupport φ.val) := hφc.image (N).continuous
  have hts : tsupport χ ⊆ (N : J → P) '' tsupport φ.val := by
    refine closure_minimal (fun t ht ↦ ?_) hImage.isClosed
    by_contra hOutside
    have hz (k : J₁) : φ.val (j k t) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hk ↦ hOutside ⟨j k t, hk, hjNorm k t⟩)
    apply Function.mem_support.mp ht
    change (∫ k : J₁, φ.val (j k t) ∂η) = 0
    simp only [hz, integral_zero]
  have hχc : HasCompactSupport χ := hImage.of_isClosed_subset (isClosed_tsupport χ) hts
  exact ⟨hχ, hts, hχ.integrable_of_hasCompactSupport hχc⟩

/-- Paper: Theorem 3.3.1.1(3), p. 129. The norm-one fiber integral of a quotient
function is independent of the continuous S-idele norm section.
Deviation: Record pointwise section independence of the fiber integral. -/
public theorem normOneAverage_eq_of_sections
    (τ σ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (hσ : RightInverse σ (sIdeleNorm F S))
    (φ : J → ℂ) (t : ℝ≥0ˣ) :
    (∫ k : J₁, φ (k.val * QuotientGroup.mk (τ t)) ∂η) =
      ∫ k : J₁, φ (k.val * QuotientGroup.mk (σ t)) ∂η := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : (η).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let a : J := QuotientGroup.mk (τ t)
  let b : J := QuotientGroup.mk (σ t)
  have ha : sIdeleQuotientNorm F S a = t := (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  have hb : sIdeleQuotientNorm F S b = t := (sIdeleQuotientNorm_mk F S (σ t)).trans (hσ t)
  let d : J₁ := ⟨a / b, (MonoidHom.div_mem_ker_iff _).mpr (ha.trans hb.symm)⟩
  let ψ (k : J₁) := φ (k.val * b)
  calc
    (∫ k : J₁, φ (k.val * a) ∂η) = ∫ k : J₁, ψ (d * k) ∂η := by
      refine integral_congr_ae (.of_forall fun k ↦ ?_)
      change φ (k.val * a) = φ ((a / b * k.val) * b)
      rw [mul_comm (a / b) k.val, mul_assoc, div_mul_cancel]
    _ = _ := integral_mul_left_eq_self (μ := η) ψ d


/-- A continuous compactly supported test for `dt/t` is radius times a continuous
compactly supported test for Lebesgue measure. Its additive support stays in the positive
ray. -/
private theorem exists_positiveAdditiveProfile (χ : ℝ≥0ˣ → ℂ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioi (0 : ℝ) ∧ Integrable ψ ∧
      ∀ t : ℝ≥0ˣ, χ t = ((t.val : ℝ) : ℂ) * ψ (t.val : ℝ) := by
  let e : ℝ≥0ˣ ≃ₜ Ioi (0 : ℝ) := Nonneg.unitsHomeomorphPos ℝ
  let θ : Ioi (0 : ℝ) → ℂ := fun x ↦ (x.val : ℂ)⁻¹ * χ (e.symm x)
  have hθ : Continuous θ :=
    ((Complex.continuous_ofReal.comp continuous_subtype_val).inv₀
      (fun x : Ioi (0 : ℝ) ↦ Complex.ofReal_ne_zero.mpr x.property.ne')).mul
      (hχ.comp e.symm.continuous)
  have hθc : HasCompactSupport θ := (hχc.comp_homeomorph e.symm).mul_left
  let ψ : ℝ → ℂ := Subtype.val.extend θ 0
  have hψ : Continuous ψ := HasCompactSupport.continuous_extend_zero isOpen_Ioi hθ hθc
  have hψc : HasCompactSupport ψ := hθc.extend_zero continuous_subtype_val
  have hψpos : tsupport ψ ⊆ Ioi (0 : ℝ) :=
    (hθc.tsupport_extend_zero_subset continuous_subtype_val).trans (Subtype.coe_image_subset _ _)
  refine ⟨ψ, hψ, hψc, hψpos, hψ.integrable_of_hasCompactSupport hψc, ?_⟩
  intro t
  have hψat : ψ (e t).val = θ (e t) :=
    Subtype.val_injective.extend_apply θ 0 (e t)
  change χ t = ((e t).val : ℂ) * ψ (e t).val
  rw [hψat]
  change χ t = ((e t).val : ℂ) * (((e t).val : ℂ)⁻¹ * χ (e.symm (e t)))
  rw [e.symm_apply_apply, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (e t).property.ne'), one_mul]


/-- Paper: Theorem 12.4.1.1, Step I, pp. 515–516. A compact quotient test has
an additive radial profile after averaging along the norm-one fibers. The
profile is continuous, integrable, and compactly supported in the positive ray.
Deviation: The fiber integral retains the norm-one Haar mass. The radius
factor compensates for the change from positive Haar to Lebesgue measure. -/
public theorem exists_normOneAdditiveTest
    (τ : P →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (φ : BruhatCompactSupport J) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioi (0 : ℝ) ∧ Integrable ψ ∧
      ∀ t : P, (∫ k : J₁, φ.val (k.val * QuotientGroup.mk (τ t)) ∂η) =
        ((t.val : ℝ) : ℂ) * ψ (t.val : ℝ) := by
  let χ (t : P) := ∫ k : J₁, φ.val (k.val * QuotientGroup.mk (τ t)) ∂η
  obtain ⟨hχ, hχs, _⟩ := normOneAverage_continuous_tsupport F S τ hτ φ
  have hφc : IsCompact (tsupport φ.val) := φ.property.2
  have hχc : HasCompactSupport χ :=
    (hφc.image (N).continuous).of_isClosed_subset (isClosed_tsupport χ) hχs
  exact exists_positiveAdditiveProfile χ hχ hχc

end

end RiemannMasullo.SLocalRadialAction
