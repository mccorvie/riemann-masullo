module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The exponential vector of the reflected half-line -/

public noncomputable section

open MeasureTheory Set

namespace RiemannMasullo


local notation "e(" a ")" =>
  Set.indicator (Ici a) (fun y : ℝ ↦ Real.exp ((a - y) / 2))

private theorem normalizedHalflineExponential_mul_shift (a t y : ℝ) :
    e(a) y * e(a) (y - t) =
      (Ici (max a (a + t))).indicator (fun x ↦ Real.exp (a + t / 2) * Real.exp (-x)) y := by
  have hshift : a ≤ y - t ↔ a + t ≤ y := by
    constructor <;> intro h <;> linarith
  have hexp : Real.exp ((a - y) / 2) * Real.exp ((a - (y - t)) / 2) =
      Real.exp (a + t / 2) * Real.exp (-y) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  by_cases hy : a ≤ y <;> by_cases ht : a + t ≤ y <;>
    simp [Set.indicator, max_le_iff, hshift, hy, ht, hexp]

private theorem normalizedHalflineExponential_overlap_exponent (a t : ℝ) :
    a + t / 2 + -(max a (a + t)) = -|t| / 2 := by
  rcases le_or_gt 0 t with ht | ht
  · have h : a ≤ a + t := by linarith
    rw [max_eq_right h, abs_of_nonneg ht]
    ring
  · have h : a + t ≤ a := by linarith
    rw [max_eq_left h, abs_of_neg ht]
    ring

/-- Every shifted product of the normalized half-line exponential is
integrable against Lebesgue measure. -/
theorem integrable_normalizedHalflineExponential_mul_shift (a t : ℝ) :
    Integrable (fun y ↦ e(a) y * e(a) (y - t)) := by
  simp_rw [normalizedHalflineExponential_mul_shift]
  rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
  exact (integrableOn_exp_neg_Ioi (max a (a + t))).const_mul _

/-- The normalized exponential on a right half-line has autocorrelation
`exp (-|t|/2)`, independent of the position of the half-line. -/
theorem integral_normalizedHalflineExponential_mul_shift (a t : ℝ) :
    (∫ y : ℝ, e(a) y * e(a) (y - t)) = Real.exp (-|t| / 2) := by
  simp_rw [normalizedHalflineExponential_mul_shift]
  rw [integral_indicator measurableSet_Ici, ← restrict_Ioi_eq_restrict_Ici, integral_const_mul,
    integral_exp_neg_Ioi, ← Real.exp_add, normalizedHalflineExponential_overlap_exponent]

/-- A sharp upper cutoff keeps the overlap up to the cutoff point. At or
below the start of the overlap the truncated integral is zero. -/
theorem integral_normalizedHalflineExponential_mul_shift_Iic (a t c : ℝ) :
    (∫ y : ℝ in Iic c, e(a) y * e(a) (y - t)) =
      if max a (a + t) ≤ c then Real.exp (-|t| / 2) - Real.exp (a + t / 2 - c) else 0 := by
  simp_rw [normalizedHalflineExponential_mul_shift, setIntegral_indicator measurableSet_Ici]
  rw [Set.inter_comm, Ici_inter_Iic]
  by_cases hc : max a (a + t) ≤ c
  · rw [ite_eq_left hc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hc, intervalIntegral.integral_comp_neg,
      integral_exp, mul_sub, ← Real.exp_add, ← Real.exp_add,
      normalizedHalflineExponential_overlap_exponent, sub_eq_add_neg (a + t / 2) c]
  · rw [ite_eq_right hc, Icc_eq_empty hc, setIntegral_empty]

/-- Pairing a convolution against the normalized half-line exponential
reduces to integrating the convolution kernel against its autocorrelation. -/
theorem integral_normalizedHalflineExponential_convolution_pairing (a : ℝ)
    (k : ℝ → ℂ) (hk : Integrable k) :
    (∫ x : ℝ, (e(a) x : ℂ) * (∫ t : ℝ, k t * (e(a) (x - t) : ℂ))) =
      ∫ t : ℝ, k t * (Real.exp (-|t| / 2) : ℂ) := by
  let F (x t : ℝ) : ℂ := k t * ((e(a) x * e(a) (x - t) : ℝ) : ℂ)
  have he : Measurable (e(a)) :=
    (Real.continuous_exp.comp
      ((continuous_const.sub continuous_id).div_const 2)).measurable.indicator
      measurableSet_Ici
  have he₀ (x : ℝ) : 0 ≤ e(a) x := by
    by_cases hx : x ∈ Ici a
    · rw [indicator_of_mem hx]
      exact (Real.exp_pos _).le
    · simp only [indicator_of_notMem hx, le_rfl]
  have hK : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ k z.2)
      ((volume : Measure ℝ).prod volume) :=
    hk.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hE : Measurable (fun z : ℝ × ℝ ↦ e(a) z.1 * e(a) (z.1 - z.2)) :=
    (he.comp measurable_fst).mul (he.comp (measurable_fst.sub measurable_snd))
  have hF : AEStronglyMeasurable (Function.uncurry F) ((volume : Measure ℝ).prod volume) :=
    hK.mul (Complex.measurable_ofReal.comp hE).aestronglyMeasurable
  have hNorm (t : ℝ) :
      (∫ x : ℝ, ‖F x t‖) = ‖k t‖ * Real.exp (-|t| / 2) := by
    calc
      _ = ∫ x : ℝ, ‖k t‖ * (e(a) x * e(a) (x - t)) := by
        apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [F, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (he₀ x) (he₀ (x - t)))]
      _ = _ := by rw [integral_const_mul, integral_normalizedHalflineExponential_mul_shift]
  have hFI : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod volume) := by
    refine (integrable_prod_iff' hF).2 ⟨ae_of_all _ (fun t ↦ ?_), ?_⟩
    · exact ((integrable_normalizedHalflineExponential_mul_shift a t).ofReal).const_mul (k t)
    · change Integrable (fun t : ℝ ↦ ∫ x : ℝ, ‖F x t‖)
      simp_rw [hNorm]
      refine hk.norm.mono' (hk.norm.aestronglyMeasurable.mul ?_) (ae_of_all _ fun t ↦ ?_)
      · exact (Real.continuous_exp.comp (continuous_abs.neg.div_const 2)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg t)) (by norm_num)))
  calc
    _ = ∫ x : ℝ, ∫ t : ℝ, F x t := by
      apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      rw [← integral_const_mul]
      apply integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      simp only [F, Complex.ofReal_mul]
      ring
    _ = ∫ t : ℝ, ∫ x : ℝ, F x t := integral_integral_swap hFI
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      change (∫ x : ℝ, k t * ((e(a) x * e(a) (x - t) : ℝ) : ℂ)) = _
      rw [integral_const_mul, integral_complex_ofReal,
        integral_normalizedHalflineExponential_mul_shift]

end RiemannMasullo
