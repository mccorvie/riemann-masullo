module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons

public section

namespace RiemannMasullo.Selberg

open MeasureTheory Set

/-- Card 23. For v > 0, the Gaussian integral approximation √π/(2v) exceeds the positive mesh sum
by an amount between zero and min(1, √π/(2v)).
Titchmarsh, §10.11, pp. 270–271, elementary alternative to harmonic expansion. -/
theorem theta_error (v : ℝ) (hv : 0 < v) :
    0 ≤ gaussC/v - theta v ∧ gaussC/v - theta v ≤ min 1 (gaussC/v) := by
  let f (x : ℝ) := Real.exp (-(v ^ 2) * x ^ 2)
  have hanti : AntitoneOn f (Ici 0) := by
    intro x hx y _ hxy
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx hxy 2) (neg_nonpos.mpr (sq_nonneg v))
  have hint : IntegrableOn f (Ioi 0) :=
    (integrable_exp_neg_mul_sq (sq_pos_of_pos hv)).integrableOn
  have hpos (x : ℝ) : 0 ≤ f x := (Real.exp_pos _).le
  have hmass : ∫ x in Ioi 0, f x = gaussC / v := by
    rw [integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hv.le, gaussC]
    ring
  have htheta : ∑' n : ℕ, f (n + 1 : ℕ) = theta v := by
    simp only [f, theta, mul_pow, neg_mul, mul_comm (v ^ 2)]
  have hsum := hanti.summable_of_integrableOn_Ioi_zero hint (fun x _ ↦ hpos x)
  have hright := hanti.tsum_add_one_le_integral hint (fun x _ ↦ hpos x)
  have hleft := hanti.integral_le_tsum hsum (fun x _ ↦ hpos x)
  rw [htheta, hmass] at hright
  rw [hmass, hsum.tsum_eq_zero_add, htheta] at hleft
  have hzero : f 0 = 1 := by simp [f]
  have hnonneg : 0 ≤ theta v := htheta ▸ tsum_nonneg (fun n ↦ hpos (n + 1 : ℕ))
  exact ⟨sub_nonneg.mpr hright, le_min (by linarith) (sub_le_self _ hnonneg)⟩

end RiemannMasullo.Selberg
