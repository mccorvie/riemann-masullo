module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.MomentFourier
public import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.Tactic

/-! The centered Mellin-line multiplier and the project weighted L² statement. -/

@[expose] public noncomputable section
open MeasureTheory Filter Complex Set Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace RiemannMasullo.CardinalMoment

/-- At width zero, removing the basepoint tilt leaves precisely the physical weight
used in Proposition 3. -/
theorem widthZero_density (a θ x : ℝ) :
    intervalSobolevDensity a a (2*θ) x = Real.exp (2*a*x)*symbol θ x := by
  simp [intervalSobolevDensity,symbol]

/-- The angular Fourier integral of the derivative is `it` times the value integral.
Thus multiplying the centered line value by `t = z-w` corresponds to `-i H′` in
the physical variable. A common Fourier normalizing scalar cancels. -/
theorem centered_value_firstMoment (H : ℝ → ℂ) (hH : Differentiable ℝ H)
    (hiH : Integrable H) (hiD : Integrable (deriv H)) (t : ℝ) :
    (∫ x, conj (wave t x)*(-I*deriv H x)) = (t:ℂ)*(∫ x, conj (wave t x)*H x) := by
  have hconj (x : ℝ) : conj (wave t x) = wave (-t) x := by
    simp only [wave,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg]
    ring_nf
  simp_rw [hconj]
  let a : ℂ := (↑(-t):ℂ)*I
  have hc : Continuous (wave (-t)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_wave _ x).continuousAt
  have hi (U : ℝ → ℂ) (hU : Integrable U) : Integrable (fun x ↦ wave (-t) x*U x) := by
    refine hU.norm.mono' (hc.aestronglyMeasurable.mul hU.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    simp only [norm_mul,norm_wave,one_mul,le_refl]
  have hcomp : Integrable (fun x ↦ (a*wave (-t) x)*H x) :=
    ((hi H hiH).const_mul a).congr (.of_forall fun x ↦ (mul_assoc _ _ _).symm)
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := wave (-t)) (u' := fun x ↦ a*wave (-t) x) (v := H) (v' := deriv H)
    (fun x _ ↦ hasDerivAt_wave (-t) x) (fun x _ ↦ (hH x).hasDerivAt)
    (hi (deriv H) hiD) hcomp (hi H hiH)
  simp only [mul_assoc,integral_const_mul] at hh
  have hmove (x : ℝ) : wave (-t) x*(-I*deriv H x) = -I*(wave (-t) x*deriv H x) := by ring
  simp_rw [hmove]
  rw [integral_const_mul,hh]
  dsimp [a]
  push_cast
  linear_combination -(t:ℂ)*(∫ x, wave (-t) x*H x)*Complex.I_sq

/-- The actual real log-line measure of the project, with the exponential tilt removed. -/
abbrev physicalMeasure (θ : ℝ) : Measure ℝ :=
  intervalSobolevMeasure volume id 0 0 (2*θ)

private theorem physicalMeasure_eq (θ : ℝ) :
    physicalMeasure θ = volume.withDensity (fun x ↦ ENNReal.ofReal (symbol θ x)) := by
  unfold physicalMeasure intervalSobolevMeasure
  simp [widthZero_density]

private theorem physicalL2_norm {θ : ℝ} (H : ℝ → ℂ) (hc : Continuous H)
    (hi : Integrable (fun x ↦ symbol θ x*‖H x‖^2)) :
    ∃ h : MemLp H 2 (physicalMeasure θ), ‖h.toLp H‖^2 = ∫ x, symbol θ x*‖H x‖^2 := by
  rw [physicalMeasure_eq]
  let ρ (x : ℝ) := ENNReal.ofReal (symbol θ x)
  have hs : Measurable ρ := (continuous_iff_continuousAt.mpr
    fun x ↦ (hasDerivAt_symbol θ x).continuousAt).measurable.ennreal_ofReal
  have hlt : ∀ᵐ x ∂volume, ρ x < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have h : MemLp H 2 (volume.withDensity ρ) := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    apply (integrable_withDensity_iff hs hlt).2
    exact hi.congr (.of_forall fun x ↦ by
      simp only [ρ,ENNReal.toReal_ofReal (symbol_pos θ x).le,mul_comm])
  refine ⟨h,?_⟩
  let f := h.toLp H
  calc
    ‖f‖^2 = RCLike.re ⟪f,f⟫_ℂ := (inner_self_eq_norm_sq _).symm
    _ = ∫ x, ‖f x‖^2 ∂volume.withDensity ρ := by
      rw [L2.inner_def,← integral_re (L2.integrable_inner f f)]
      simp_rw [inner_self_eq_norm_sq]
    _ = ∫ x, ‖H x‖^2 ∂volume.withDensity ρ := by
      apply integral_congr_ae
      filter_upwards [h.coeFn_toLp] with x hx
      rw [show f x = H x from hx]
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul hs hlt]
      exact integral_congr_ae (.of_forall fun x ↦ by simp [ρ,ENNReal.toReal_ofReal (symbol_pos θ x).le])

/-- First moment of a finite centered cardinal in the actual Chapter 9 weighted L²
measure. The Fourier integral equality records that the strong vector represents
multiplication by `z-w` on the Mellin line. -/
theorem finite_cardinal_physical_firstMoment (A : Finset ℝ) (w θ : ℝ) (hθ : 1 ≤ θ) (c H : ℝ → ℂ)
    (hrep : ∀ x, symbol θ x • H x = centeredPolynomial A w c x)
    (hcard : ∀ z ∈ A, z ≠ w → (∫ x, conj (wave (z-w) x)*H x) = 0) :
    ∃ (u : MemLp (fun x ↦ -I*deriv H x) 2 (physicalMeasure θ))
      (v : MemLp H 2 (physicalMeasure (θ-1))),
      (∀ z : ℝ, (∫ x, conj (wave (z-w) x)*(-I*deriv H x)) =
        (↑(z-w):ℂ)*(∫ x, conj (wave (z-w) x)*H x)) ∧
      ‖u.toLp (fun x ↦ -I*deriv H x)‖^2 = (∫ x, symbolCurvature θ x*‖H x‖^2)/2 ∧
      θ*‖v.toLp H‖^2 ≤ ‖u.toLp (fun x ↦ -I*deriv H x)‖^2 ∧
      ‖u.toLp (fun x ↦ -I*deriv H x)‖^2 ≤ θ*(2*θ-1)*‖v.toLp H‖^2 := by
  obtain ⟨hd,hc,hiH,hiD,hwH,hwD,_⟩ := finite_profile_regular A w θ hθ c H hrep
  have hweak : Integrable (fun x ↦ symbol (θ-1) x*‖H x‖^2) := by
    have hmc : Continuous (symbol (θ-1)) := continuous_iff_continuousAt.mpr
      fun x ↦ (hasDerivAt_symbol (θ-1) x).continuousAt
    refine hwH.mono' (hmc.mul (hd.continuous.norm.pow 2)).aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (symbol_pos _ _).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (symbol_decr_exponent θ x) (sq_nonneg _)
  have hDnorm (x : ℝ) : ‖-I*deriv H x‖ = ‖deriv H x‖ := by simp
  obtain ⟨u,hu⟩ := physicalL2_norm (θ := θ) (fun x ↦ -I*deriv H x) (continuous_const.mul hc)
    (by simpa only [hDnorm] using hwD)
  obtain ⟨v,hv⟩ := physicalL2_norm H hd.continuous hweak
  simp only [hDnorm] at hu
  refine ⟨u,v,fun z ↦ centered_value_firstMoment H hd hiH hiD (z-w),?_⟩
  rw [hu,hv]
  exact finite_cardinal_firstMoment A w θ hθ c H hrep hcard

end RiemannMasullo.CardinalMoment
