module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Ring

/-! # Character selection by convolution on the S-local quotient -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

/-- Convolution of functions in distinct character types for the same
subgroup vanishes. Both functions transform by the inverse character
under right translation. -/
theorem lcaConvolution_eq_zero_of_distinct_rightCharacters
    {G H : Type*} [CommGroup G] [Group H] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulRightInvariant] (ι : H →* G)
    (α β : H →* Circle) (hne : α ≠ β) (f g : G → ℂ)
    (hf : ∀ x h, f (x * ι h) = (α h : ℂ)⁻¹ * f x)
    (hg : ∀ x h, g (x * ι h) = (β h : ℂ)⁻¹ * g x) (x : G) :
    lcaConvolution μ f g x = 0 := by
  obtain ⟨h, hh⟩ : ∃ h, α h ≠ β h := by
    by_contra! heq
    exact hne (MonoidHom.ext heq)
  let c : ℂ := (α h : ℂ)⁻¹ * (β h : ℂ)
  have hc : c ≠ 1 := by
    intro hc
    apply hh
    apply Subtype.ext
    have ha : (α h : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hm := congrArg ((α h : ℂ) * ·) hc
    simpa only [c, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, mul_one] using hm.symm
  let F (y : G) := f y * g (y⁻¹ * x)
  have hShift (y : G) : F (y * ι h) = c * F y := by
    have harg : (y * ι h)⁻¹ * x = (y⁻¹ * x) * ι h⁻¹ := by
      rw [map_inv, mul_inv, mul_right_comm]
    dsimp only [F]
    rw [harg, hf y h, hg (y⁻¹ * x) h⁻¹, map_inv, Circle.coe_inv, inv_inv]
    dsimp only [c]
    ring
  have hI : (∫ y, F y ∂μ) = c * (∫ y, F y ∂μ) := by
    rw [← integral_const_mul]
    exact (integral_mul_right_eq_self (μ := μ) F (ι h)).symm.trans
      (integral_congr_ae (ae_of_all _ hShift))
  have hz : (c - 1) * (∫ y, F y ∂μ) = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "N" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local instance instNormOneMeasurableAngularConvolutionSupport : MeasurableSpace J₁ := borel _

/-- Reindexing the norm-one average gives the inverse-character covariance
of the S-local homogeneous theta function. -/
theorem sLocalHomogeneousAdelicThetaLinearMap_mul_normOne
    (χ : PontryaginDual J₁) (f : Bₛ) (q : Jₛ) (h : J₁) :
    sLocalHomogeneousAdelicThetaLinearMap F S χ f (q * h.val) =
      (χ h : ℂ)⁻¹ * sLocalHomogeneousAdelicThetaLinearMap F S χ f q := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : (η).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, sLocalHomogeneousAdelicThetaLinearMap_apply,
    ← integral_const_mul]
  let A (k : J₁) := sLocalAdelicThetaOnClasses F S f ((q * h.val) * k.val) * (χ k : ℂ)
  change (∫ k, A k ∂η) = _
  rw [← integral_mul_right_eq_self (μ := η) A h⁻¹]
  apply integral_congr_ae (ae_of_all _ fun k ↦ ?_)
  change sLocalAdelicThetaOnClasses F S f ((q * h.val) * (k.val * h.val⁻¹)) *
    (χ (k * h⁻¹) : ℂ) =
    (χ h : ℂ)⁻¹ * (sLocalAdelicThetaOnClasses F S f (q * k.val) * (χ k : ℂ))
  have hk : (q * h.val) * (k.val * h.val⁻¹) = q * k.val := by
    rw [show (q * h.val) * (k.val * h.val⁻¹) = (q * k.val) * (h.val * h.val⁻¹) by ac_rfl,
      mul_inv_cancel, mul_one]
  rw [hk, map_mul χ k h⁻¹, map_inv χ h, Circle.coe_mul, Circle.coe_inv]
  ring

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientHaarMeasureSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1

/-- Paper: Theorem 12.4.1.1, pp. 515–518. Quotient convolution by a
homogeneous test vanishes on the half-density theta generators of
each distinct norm-one type. -/
theorem sLocalTrace_lcaConvolution_halfDensityTheta_eq_zero_of_ne_normOne
    (φ : Jₛ → ℂ) (α β : PontryaginDual J₁) (hne : α ≠ β)
    (hφ : ∀ (x : Jₛ) (h : J₁), φ (x * h.val) = (α h : ℂ)⁻¹ * φ x)
    (f : Bₛ) (q : Jₛ) :
    lcaConvolution μJ φ (fun y ↦ (Real.sqrt ((N y).val : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap F S β f y) q = 0 := by
  let v (y : Jₛ) := (Real.sqrt ((N y).val : ℝ) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap F S β f y
  have hv (y : Jₛ) (h : J₁) : v (y * h.val) = (β h : ℂ)⁻¹ * v y := by
    have hn : N (y * h.val) = N y := by
      rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
    simp only [v, hn, sLocalHomogeneousAdelicThetaLinearMap_mul_normOne]
    ring
  have hne' : α.toMonoidHom ≠ β.toMonoidHom := by
    intro heq
    apply hne
    exact ContinuousMonoidHom.ext fun h ↦ DFunLike.congr_fun heq h
  exact lcaConvolution_eq_zero_of_distinct_rightCharacters μJ (MonoidHom.ker N).subtype
    α.toMonoidHom β.toMonoidHom hne' φ v hφ hv q

end RiemannMasullo
