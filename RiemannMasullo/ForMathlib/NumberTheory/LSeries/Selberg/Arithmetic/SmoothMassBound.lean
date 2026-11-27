module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.NumberTheory.EulerProduct.Basic

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Card 4. The sum of the reciprocals of the r-supported positive integers through B is bounded
by the Euler product `smoothMass r`.
Titchmarsh, §10.13, p. 273, finite geometric majorant. -/
theorem smooth_mass_bound (r B : ℕ) (hr : 0 < r) :
    (∑ d ∈ (D B).filter (smooth r), (d : ℝ)⁻¹) ≤ smoothMass r := by
  let f : ℕ →* ℝ := invMonoidWithZeroHom.toMonoidHom.comp (Nat.castRingHom ℝ).toMonoidHom
  have hprime {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hsum := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) hprime r.primeFactors).2
  rw [Finset.filter_true_of_mem fun _ hp ↦ ((Nat.mem_primeFactors_of_ne_zero hr.ne').mp hp).1]
    at hsum
  unfold smooth
  rw [← Finset.sum_subtype_eq_sum_filter]
  exact sum_le_hasSum _ (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) hsum

end RiemannMasullo.Selberg
