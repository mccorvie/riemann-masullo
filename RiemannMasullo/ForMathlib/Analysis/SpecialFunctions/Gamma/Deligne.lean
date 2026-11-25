module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Integer shifts of the Deligne gamma factors

The recurrences `Γ_ℝ(z + 2) = Γ_ℝ(z) · z / (2π)` and `Γ_ℂ(z + 1) = Γ_ℂ(z) · z / (2π)` hold away
from `z = 0`. For the reciprocals they hold everywhere, because Mathlib's gamma function takes
the value `0` at its poles. Iterating gives the reciprocal of a Deligne gamma factor as the
reciprocal of a shifted one times an explicit polynomial, with no exceptional point. The
polynomial is bounded above by a power of `‖z‖`, and below by a constant on a right half-plane.

The last four lemmas (`norm_prod_add_mul_div_two_pi_le`, `pow_le_norm_prod_add_mul_div_two_pi`,
`norm_div_pow_le_norm_prod_add_mul_div_two_pi`, `pow_le_norm_prod_add_mul_div_two_pi_of_im`)
are about such a polynomial alone, a product of `m` linear factors `(z + c j) / (2π)` with
`c ≥ 0`; no gamma function occurs in them. They stand here because the shift identities are
their only use.
-/

public section

open Complex Finset

namespace RiemannMasullo

/-- `Γ_ℝ(z)⁻¹ = Γ_ℝ(z + 2)⁻¹ · z / (2π)` at every `z`, the pole `z = 0` included. -/
theorem inv_Gammaℝ_eq_inv_Gammaℝ_add_two_mul (z : ℂ) :
    (Gammaℝ z)⁻¹ = (Gammaℝ (z + 2))⁻¹ * (z / (2 * Real.pi)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Gammaℝ_def]
  · have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Gammaℝ_add_two hz, div_div, mul_div_assoc, mul_inv, mul_assoc,
      inv_mul_cancel₀ (div_ne_zero hz (mul_ne_zero two_ne_zero hπ)), mul_one]

/-- `Γ_ℂ(z)⁻¹ = Γ_ℂ(z + 1)⁻¹ · z / (2π)` at every `z`, the pole `z = 0` included. -/
theorem inv_Gammaℂ_eq_inv_Gammaℂ_add_one_mul (z : ℂ) :
    (Gammaℂ z)⁻¹ = (Gammaℂ (z + 1))⁻¹ * (z / (2 * Real.pi)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Gammaℂ_def]
  · have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Gammaℂ_add_one hz, div_div, mul_div_assoc, mul_inv, mul_assoc,
      inv_mul_cancel₀ (div_ne_zero hz (mul_ne_zero two_ne_zero hπ)), mul_one]

/-- The reciprocal of `Γ_ℝ` at `z` is its reciprocal at `z + 2m` times the product of the `m`
linear factors `(z + 2j) / (2π)`, at every `z`. -/
theorem inv_Gammaℝ_eq_inv_Gammaℝ_add_mul_prod (z : ℂ) (m : ℕ) :
    (Gammaℝ z)⁻¹ =
      (Gammaℝ (z + 2 * m))⁻¹ * ∏ j ∈ range m, ((z + 2 * j) / (2 * Real.pi)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, inv_Gammaℝ_eq_inv_Gammaℝ_add_two_mul (z + 2 * m), prod_range_succ]
    have h : z + 2 * (m : ℂ) + 2 = z + 2 * ((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    ring

/-- The reciprocal of `Γ_ℂ` at `z` is its reciprocal at `z + m` times the product of the `m`
linear factors `(z + j) / (2π)`, at every `z`. -/
theorem inv_Gammaℂ_eq_inv_Gammaℂ_add_mul_prod (z : ℂ) (m : ℕ) :
    (Gammaℂ z)⁻¹ = (Gammaℂ (z + m))⁻¹ * ∏ j ∈ range m, ((z + j) / (2 * Real.pi)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, inv_Gammaℂ_eq_inv_Gammaℂ_add_one_mul (z + m), prod_range_succ]
    have h : z + (m : ℂ) + 1 = z + ((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    ring

/-- A product of `m` linear factors `(z + c j) / (2π)` with `0 ≤ c` has norm at most
`(‖z‖ + c m) ^ m`. -/
theorem norm_prod_add_mul_div_two_pi_le (z : ℂ) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    ‖∏ j ∈ range m, ((z + c * j) / (2 * Real.pi))‖ ≤ (‖z‖ + c * m) ^ m := by
  rw [norm_prod]
  calc ∏ j ∈ range m, ‖(z + c * j) / (2 * Real.pi)‖
      ≤ ∏ _j ∈ range m, (‖z‖ + c * m) := by
        refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j hj ↦ ?_
        have hj' : (j : ℝ) ≤ m := by exact_mod_cast (mem_range.mp hj).le
        have h2π : (1 : ℝ) ≤ ‖(2 * Real.pi : ℂ)‖ := by
          rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
          linarith [Real.two_le_pi]
        rw [norm_div]
        refine (div_le_self (norm_nonneg _) h2π).trans ((norm_add_le _ _).trans ?_)
        have hcj : ‖(c : ℂ) * (j : ℂ)‖ = c * j := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, Complex.norm_natCast]
        rw [hcj]
        gcongr
    _ = (‖z‖ + c * m) ^ m := by rw [prod_const, card_range]

/-- If `0 ≤ c` and `δ ≤ Re z` with `0 ≤ δ`, a product of `m` linear factors `(z + c j) / (2π)`
has norm at least `(δ / (2π)) ^ m`. -/
theorem pow_le_norm_prod_add_mul_div_two_pi {z : ℂ} {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hz : δ ≤ z.re) (m : ℕ) :
    (δ / (2 * Real.pi)) ^ m ≤ ‖∏ j ∈ range m, ((z + c * j) / (2 * Real.pi))‖ := by
  rw [norm_prod]
  calc (δ / (2 * Real.pi)) ^ m = ∏ _j ∈ range m, (δ / (2 * Real.pi)) := by
        rw [prod_const, card_range]
    _ ≤ ∏ j ∈ range m, ‖(z + c * j) / (2 * Real.pi)‖ := by
        refine prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ ?_
        have h2π : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
          rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        rw [norm_div, h2π]
        gcongr
        refine le_trans ?_ (Complex.re_le_norm _)
        have hre : (z + (c : ℂ) * (j : ℂ)).re = z.re + c * j := by simp
        rw [hre]
        nlinarith [mul_nonneg hc (Nat.cast_nonneg (α := ℝ) j)]

/-- If `0 ≤ c` and `0 ≤ Re z`, a product of `m` linear factors `(z + c j) / (2π)` has norm at
least `(‖z‖ / (2π)) ^ m`. -/
theorem norm_div_pow_le_norm_prod_add_mul_div_two_pi {z : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hz : 0 ≤ z.re) (m : ℕ) :
    (‖z‖ / (2 * Real.pi)) ^ m ≤ ‖∏ j ∈ range m, ((z + c * j) / (2 * Real.pi))‖ := by
  rw [norm_prod]
  calc (‖z‖ / (2 * Real.pi)) ^ m = ∏ _j ∈ range m, (‖z‖ / (2 * Real.pi)) := by
        rw [prod_const, card_range]
    _ ≤ ∏ j ∈ range m, ‖(z + c * j) / (2 * Real.pi)‖ := by
        refine prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ ?_
        have h2π : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
          rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        rw [norm_div, h2π]
        gcongr
        have hcj : 0 ≤ c * j := mul_nonneg hc (Nat.cast_nonneg j)
        rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
          Complex.normSq_apply, Complex.normSq_apply]
        have hre : (z + (c : ℂ) * (j : ℂ)).re = z.re + c * j := by simp
        have him : (z + (c : ℂ) * (j : ℂ)).im = z.im := by simp
        rw [hre, him]
        nlinarith

/-- If `δ ≤ |Im z|` with `0 ≤ δ`, a product of `m` linear factors `(z + c j) / (2π)` with real
`c` has norm at least `(δ / (2π)) ^ m`. -/
theorem pow_le_norm_prod_add_mul_div_two_pi_of_im {z : ℂ} {c δ : ℝ} (hδ : 0 ≤ δ)
    (hz : δ ≤ |z.im|) (m : ℕ) :
    (δ / (2 * Real.pi)) ^ m ≤ ‖∏ j ∈ range m, ((z + c * j) / (2 * Real.pi))‖ := by
  rw [norm_prod]
  calc (δ / (2 * Real.pi)) ^ m = ∏ _j ∈ range m, (δ / (2 * Real.pi)) := by
        rw [prod_const, card_range]
    _ ≤ ∏ j ∈ range m, ‖(z + c * j) / (2 * Real.pi)‖ := by
        refine prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ ?_
        have h2π : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
          rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        rw [norm_div, h2π]
        gcongr
        refine le_trans ?_ (Complex.abs_im_le_norm _)
        have him : (z + (c : ℂ) * (j : ℂ)).im = z.im := by simp
        rw [him]
        exact hz

end RiemannMasullo
