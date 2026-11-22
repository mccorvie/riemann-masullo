module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

public section

open Filter Set
open scoped Topology ContDiff

namespace SchwartzMap

/-- A Schwartz function on the line agreeing with the decaying exponential on the positive ray. -/
private noncomputable def expNegCutoff : SchwartzMap ℝ ℝ := by
  let f (t : ℝ) := Real.smoothTransition (t + 1) * Real.exp (-1 * t)
  have hf : ContDiff ℝ ∞ f := by
    exact (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  refine ⟨f, hf, fun k n ↦ ?_⟩
  let d (x : ℝ) := ‖x‖ ^ k * ‖iteratedDeriv n f x‖
  have hd : Continuous d := (continuous_norm.pow k).mul
    (hf.continuous_iteratedDeriv n (by simp)).norm
  obtain ⟨B, hB⟩ := isCompact_Icc (α := ℝ) (a := -1) (b := 0) |>.exists_bound_of_continuousOn hd.continuousOn
  refine ⟨max B (k.factorial : ℝ), fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : 0 < x
  · have he : f =ᶠ[𝓝 x] fun t ↦ Real.exp (-1 * t) := by
      filter_upwards [lt_mem_nhds hx] with t ht
      simp [f, Real.smoothTransition.one_of_one_le (show 1 ≤ t + 1 by linarith)]
    rw [he.iteratedDeriv_eq n, iteratedDeriv_exp_const_mul]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, neg_mul,
      Real.norm_eq_abs, abs_of_nonneg hx.le, Real.exp_neg, abs_inv, abs_of_pos (Real.exp_pos _)]
    apply le_trans _ (le_max_right _ _)
    rw [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos x)]
    have h := (div_le_iff₀ (by positivity : 0 < (k.factorial : ℝ))).mp
      (Real.pow_div_factorial_le_exp x hx.le k)
    linarith
  · by_cases hl : x < -1
    · have he : f =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
        filter_upwards [gt_mem_nhds hl] with t ht
        simp [f, Real.smoothTransition.zero_of_nonpos (show t + 1 ≤ 0 by linarith)]
      rw [he.iteratedDeriv_eq n]
      simp
    · exact ((le_abs_self (d x)).trans (hB x ⟨le_of_not_gt hl, le_of_not_gt hx⟩)).trans (le_max_left _ _)

/-- The radial Gaussian with positive real coefficient, as a Schwartz function. -/
noncomputable def gaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (ha : 0 < a) : SchwartzMap E ℝ :=
  compCLM ℝ (g := fun x : E ↦ a * ‖x‖ ^ 2) (by fun_prop) (by
    refine ⟨1, max 1 a⁻¹, fun x ↦ ?_⟩
    rw [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h₁ : 1 ≤ max 1 a⁻¹ := le_max_left _ _
    have h₂ : 1 ≤ max 1 a⁻¹ * a := (inv_le_iff_one_le_mul₀ ha).mp (le_max_right _ _)
    nlinarith [mul_le_mul_of_nonneg_right h₂ (sq_nonneg ‖x‖), sq_nonneg (‖x‖ - 1)]) expNegCutoff

@[simp] theorem gaussian_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (ha : 0 < a) (x : E) : gaussian a ha x = Real.exp (-a * ‖x‖ ^ 2) := by
  change Real.smoothTransition (a * ‖x‖ ^ 2 + 1) * Real.exp (-1 * (a * ‖x‖ ^ 2)) = _
  rw [Real.smoothTransition.one_of_one_le (by nlinarith [mul_nonneg ha.le (sq_nonneg ‖x‖)]), one_mul]
  congr 1
  ring

end SchwartzMap
