module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # The weighted theta generator under the quotient cutoff action -/

public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

/-- Change the convolution input on a Haar null set and then apply a
multiplier for a measure absolutely continuous with respect to Haar. -/
private theorem cutoff_convolution_ae_of_representative
    {G : Type*} [Group G] [MeasurableSpace G] {μ ν : Measure G}
    (hν : ν ≪ μ)
    (htrans : ∀ x : G, QuasiMeasurePreserving (fun y : G ↦ y⁻¹ * x) μ μ)
    {φ u v a c : G → ℂ} {ρ : G → ℝ}
    (hu : u =ᵐ[μ] v)
    (ha : a =ᵐ[μ] fun x ↦ ∫ y, φ y * u (y⁻¹ * x) ∂μ)
    (hc : c =ᵐ[ν] fun x ↦ (ρ x : ℂ) * a x) :
    c =ᵐ[ν] fun x ↦ (ρ x : ℂ) * ∫ y, φ y * v (y⁻¹ * x) ∂μ := by
  have hconv (x : G) :
      (∫ y, φ y * u (y⁻¹ * x) ∂μ) = ∫ y, φ y * v (y⁻¹ * x) ∂μ :=
    integral_congr_ae (((htrans x).ae_eq_comp hu).mono
      fun y hy ↦ congrArg (φ y * ·) hy)
  exact hc.trans ((hν.ae_eq (ha.trans (ae_of_all _ hconv))).mono
    fun x hx ↦ congrArg ((ρ x : ℂ) * ·) hx)

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "N" => continuousSIdeleQuotientNorm F S

/-- Paper: Theorem 12.4.1.1, p. 515. On each Chapter 11 theta generator,
the weighted quotient test action followed by a spatial multiplier has the
pointwise Haar convolution of the homogeneous theta representative as its
almost-everywhere formula.
Deviation: The logarithmic Sobolev base interval is `{0}`. The test action
and spatial cutoff act on a single weighted generator before compression. -/
theorem sLocalPWThetaSobolevMap_cutoff_testAction_apply
    {s : ℝ} (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (f : sAdelePolarSubspace F S)
    (φ : BruhatCompactSupport Jₛ) (ρ : Jₛ → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) :
    let ν : Measure Jₛ := intervalSobolevMeasure μJ (logSIdeleQuotientNorm F S) 0 0 s
    let v : Lp ℂ 2 ν := sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f
    let A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := hardySobolevTestAction μJ N 0 0 s le_rfl hs φ
    let M := lpCutoffMultiplier ν ρ hm hb
    let u := modulationWeight N a (sLocalHomogeneousAdelicThetaLinearMap F S ω f.val)
    (M (A v) : Jₛ → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * lcaConvolution μJ φ.val u x := by
  intro ν v A M u
  have hv : (v : Jₛ → ℂ) =ᵐ[μJ] u :=
    sLocalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) ha ω f
  have hA : (A v : Jₛ → ℂ) =ᵐ[μJ] lcaConvolution μJ φ.val v :=
    hardySobolevTestAction_apply μJ N 0 0 s le_rfl hs φ v
  have hM : (M (A v) : Jₛ → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * (A v) x :=
    lpCutoffMultiplier_apply ν ρ hm hb (A v)
  have hν : ν ≪ μJ := withDensity_absolutelyContinuous _ _
  have htrans (x : Jₛ) : QuasiMeasurePreserving (fun y : Jₛ ↦ y⁻¹ * x) μJ μJ :=
    (quasiMeasurePreserving_mul_right μJ x).comp (quasiMeasurePreserving_inv μJ)
  exact cutoff_convolution_ae_of_representative hν htrans hv hA hM

end RiemannMasullo
