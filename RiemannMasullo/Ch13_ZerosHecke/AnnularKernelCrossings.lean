module

public import RiemannMasullo.Ch13_ZerosHecke.AnnularPrimeTrapezoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential moment cancellation for the annular prime kernel

In logarithmic coordinates the kernel has two knots, at zero and minus the
logarithm of two. Fixing the side of each knot gives an exact linear combination
of the three exponential moments. The error is quadratic in the shift and is
supported on shifts that can reach a knot.
-/

namespace RiemannMasullo

open Real

@[expose] public noncomputable section

/-- The contribution of a single knot in logarithmic coordinates. -/
def annularKernelLogKnot (r : ℝ) : ℝ :=
  if 0 < r then exp r + exp (-r) - 2 else 0

private theorem annular_exp_log_two (r : ℝ) :
    exp (r + log 2) = 2 * exp r := by
  rw [exp_add, exp_log (by norm_num : (0 : ℝ) < 2), mul_comm]

private theorem annular_symmetric_log_two (r : ℝ) :
    exp (r + log 2) + exp (-(r + log 2)) - 2 =
      2 * exp r + exp (-r) / 2 - 2 := by
  rw [exp_neg (r + log 2), annular_exp_log_two, exp_neg]
  field_simp

/-- The exact two-knot representation of the annular kernel in log coordinates. -/
theorem annularPrimeKernel_logKnots (r : ℝ) :
    annularPrimeKernel (exp r) = 1 - 3 * exp r / 2 +
      annularKernelLogKnot (r + log 2) - annularKernelLogKnot r / 2 := by
  have hL : 0 < r + log 2 ↔ 1 / 2 < exp r := by
    rw [← one_lt_exp_iff, annular_exp_log_two]
    constructor <;> intro h <;> linarith
  by_cases hhalf : exp r ≤ 1 / 2
  · have hr : ¬0 < r := fun h ↦ by linarith [one_lt_exp_iff.mpr h]
    have hshift : ¬0 < r + log 2 := fun h ↦ (not_lt.mpr hhalf) (hL.mp h)
    simp only [annularPrimeKernel, ite_eq_left hhalf, annularKernelLogKnot,
      ite_eq_right hshift, ite_eq_right hr, add_zero, zero_div, sub_zero]
  · have hshift : 0 < r + log 2 := hL.mpr (lt_of_not_ge hhalf)
    by_cases hone : exp r ≤ 1
    · have hr : ¬0 < r := not_lt.mpr (exp_le_one_iff.mp hone)
      simp only [annularPrimeKernel, ite_eq_right hhalf, ite_eq_left hone, annularKernelLogKnot,
        ite_eq_left hshift, ite_eq_right hr, zero_div, sub_zero]
      rw [annular_symmetric_log_two, exp_neg]
      field_simp
      ring
    · have hr : 0 < r := one_lt_exp_iff.mp (lt_of_not_ge hone)
      simp only [annularPrimeKernel, ite_eq_right hhalf, ite_eq_right hone, annularKernelLogKnot,
        ite_eq_left hshift, ite_eq_left hr, annular_symmetric_log_two]
      ring

/-- Freeze the side of each knot at `r`, then evaluate that expression at shift `h`. -/
def annularKernelFrozen (r h : ℝ) : ℝ :=
  1 - 3 * exp (r + h) / 2 +
    (if 0 < r + log 2 then exp (r + log 2 + h) + exp (-(r + log 2 + h)) - 2 else 0) -
    (if 0 < r then exp (r + h) + exp (-(r + h)) - 2 else 0) / 2

/-- The frozen expression recovers the kernel at shift zero. -/
theorem annularKernelFrozen_zero (r : ℝ) :
    annularKernelFrozen r 0 = annularPrimeKernel (exp r) := by
  rw [annularPrimeKernel_logKnots]
  simp only [annularKernelFrozen, annularKernelLogKnot, add_zero]

private theorem annular_shifted_log_two (r h : ℝ) :
    exp (r + log 2 + h) + exp (-(r + log 2 + h)) - 2 =
      2 * exp (r + h) + exp (-(r + h)) / 2 - 2 := by
  rw [show r + log 2 + h = (r + h) + log 2 by ring, annular_symmetric_log_two]

/-- Beyond the upper knot the frozen expression vanishes for every shift. -/
theorem annularKernelFrozen_eq_zero_of_pos {r : ℝ} (hr : 0 < r) (h : ℝ) :
    annularKernelFrozen r h = 0 := by
  have hL : 0 < r + log 2 := add_pos hr (log_pos (by norm_num))
  simp only [annularKernelFrozen, ite_eq_left hr, ite_eq_left hL, annular_shifted_log_two]
  ring

/-- The baseline depends on a shifted measure only through its three exponential
moments, at exponents zero, one and minus one. -/
theorem annularKernelFrozen_three_moments (r : ℝ) :
    ∃ a b c : ℝ, ∀ h : ℝ, annularKernelFrozen r h = a + b * exp h + c * exp (-h) := by
  by_cases hr : 0 < r
  · exact ⟨0, 0, 0, fun h ↦ by simp [annularKernelFrozen_eq_zero_of_pos hr]⟩
  by_cases hL : 0 < r + log 2
  · refine ⟨-1, exp r / 2, exp (-r) / 2, fun h ↦ ?_⟩
    simp only [annularKernelFrozen, ite_eq_left hL, ite_eq_right hr, zero_div, sub_zero]
    rw [annular_shifted_log_two]
    simp only [exp_add, neg_add_rev]
    ring
  · refine ⟨1, -3 * exp r / 2, 0, fun h ↦ ?_⟩
    simp only [annularKernelFrozen, ite_eq_right hr, ite_eq_right hL, exp_add]
    ring

private theorem annular_symmetric_exp_bounds (x : ℝ) :
    0 ≤ exp x + exp (-x) - 2 ∧ exp x + exp (-x) - 2 ≤ x^2 * exp |x| := by
  let t := |x|
  have hrewrite : exp x + exp (-x) - 2 = exp t * (1 - exp (-t))^2 := by
    have hsym : exp x + exp (-x) = exp t + exp (-t) := by
      dsimp only [t]
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, neg_neg, add_comm]
    rw [hsym, exp_neg]
    field_simp
    ring
  have hneg : exp (-t) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  have hsmall : 1 - exp (-t) ≤ t := by linarith [add_one_le_exp (-t)]
  rw [hrewrite]
  constructor
  · positivity
  · calc _ ≤ exp t * t^2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hneg) hsmall 2) (exp_pos _).le
         _ = _ := by simp only [t, sq_abs, mul_comm]

private theorem annularKnot_crossing_bound (r h : ℝ) :
    |annularKernelLogKnot (r + h) -
      (if 0 < r then exp (r + h) + exp (-(r + h)) - 2 else 0)| ≤
      h^2 * exp |h| * (if |r| ≤ |h| then 1 else 0) := by
  have hbound (hh : |r + h| ≤ |h|) :
      exp (r + h) + exp (-(r + h)) - 2 ≤ h^2 * exp |h| := by
    apply (annular_symmetric_exp_bounds (r+h)).2.trans
    have hs : (r+h)^2 ≤ h^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (r+h)) hh 2
    exact mul_le_mul hs (exp_le_exp.mpr hh) (exp_pos _).le (sq_nonneg _)
  have hnn : 0 ≤ h^2 * exp |h| * (if |r| ≤ |h| then 1 else 0) := by split_ifs <;> positivity
  by_cases h₁ : 0 < r <;> by_cases h₂ : 0 < r+h
  · simpa only [annularKernelLogKnot, ite_eq_left h₁, ite_eq_left h₂, sub_self, abs_zero] using hnn
  · have hh : |r+h| ≤ |h| := by rw [abs_of_nonpos (le_of_not_gt h₂)]; linarith [neg_le_abs h]
    have hr : |r| ≤ |h| := by rw [abs_of_pos h₁]; linarith [neg_le_abs h]
    simpa only [annularKernelLogKnot, ite_eq_right h₂, ite_eq_left h₁, ite_eq_left hr, zero_sub, abs_neg,
      abs_of_nonneg (annular_symmetric_exp_bounds (r+h)).1, mul_one] using hbound hh
  · have hh : |r+h| ≤ |h| := by rw [abs_of_pos h₂]; linarith [le_abs_self h]
    have hr : |r| ≤ |h| := by rw [abs_of_nonpos (le_of_not_gt h₁)]; linarith [le_abs_self h]
    simpa only [annularKernelLogKnot, ite_eq_left h₂, ite_eq_right h₁, ite_eq_left hr, sub_zero,
      abs_of_nonneg (annular_symmetric_exp_bounds (r+h)).1, mul_one] using hbound hh
  · simpa only [annularKernelLogKnot, ite_eq_right h₁, ite_eq_right h₂, sub_self, abs_zero] using hnn

/-- The frozen three-moment expression is exact away from the two knots. When a
shift can reach a knot, its error is bounded by a quadratic term at that knot. -/
theorem annularPrimeKernel_crossing_bound (r h : ℝ) :
    |annularPrimeKernel (exp (r+h)) - annularKernelFrozen r h| ≤
      h^2 * exp |h| * ((if |r + log 2| ≤ |h| then 1 else 0) +
        (if |r| ≤ |h| then 1 / 2 else 0)) := by
  let Δ (a : ℝ) := annularKernelLogKnot (a+h) -
    (if 0 < a then exp (a+h) + exp (-(a+h)) - 2 else 0)
  have heq : annularPrimeKernel (exp (r+h)) - annularKernelFrozen r h =
      Δ (r+log 2) - Δ r / 2 := by
    rw [annularPrimeKernel_logKnots]
    dsimp only [Δ, annularKernelFrozen]
    rw [show r+h+log 2 = r+log 2+h by ring]
    ring
  rw [heq]
  calc _ ≤ |Δ (r+log 2)| + |Δ r| / 2 := by
           simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
             abs_sub (Δ (r+log 2)) (Δ r / 2)
       _ ≤ h^2 * exp |h| * (if |r + log 2| ≤ |h| then 1 else 0) +
             (h^2 * exp |h| * (if |r| ≤ |h| then 1 else 0)) / 2 :=
           add_le_add (annularKnot_crossing_bound (r+log 2) h)
             (div_le_div_of_nonneg_right (annularKnot_crossing_bound r h) (by norm_num))
       _ = _ := by split_ifs <;> ring

end

end RiemannMasullo
