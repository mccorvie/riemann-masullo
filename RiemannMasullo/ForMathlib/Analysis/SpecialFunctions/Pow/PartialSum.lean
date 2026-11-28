module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Partial sums of complex powers

A first derivative estimate controls the error when replacing the sum of the first
`N` complex powers by its integral. On the fourth-power grid in the first Hecke
Riesz mean the exponent is `4 * (1 + ρ)`.
-/

public section

namespace RiemannMasullo

open Complex Finset Set
open scoped Interval

private theorem norm_cpow_unit_interval_error {z : ℂ} (hz : 1 ≤ z.re) {N k : ℕ}
    (hk : k < N) :
    ‖((k : ℂ) + 1) ^ z -
      ∫ x : ℝ in (k : ℝ) + 1..(k : ℝ) + 2, (x : ℂ) ^ z‖ ≤
      ‖z‖ * ((N : ℝ) + 1) ^ (z.re - 1) := by
  let C := ‖z‖ * ((N : ℝ) + 1) ^ (z.re - 1)
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hkN : (k : ℝ) + 2 ≤ N + 1 := by exact_mod_cast (by omega : k + 2 ≤ N + 1)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hderiv (x : ℝ) (hx : x ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) :
      HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ z) (z * (x : ℂ) ^ (z - 1)) x :=
    hasDerivAt_ofReal_cpow_const (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) k]) hz0
  have hbound (x : ℝ) (hx : x ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) :
      ‖z * (x : ℂ) ^ (z - 1)‖ ≤ C := by
    have hx0 : 0 < x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) k]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx0.le (hx.2.trans hkN) (sub_nonneg.mpr hz)) (norm_nonneg _)
  have hi := intervalIntegral.intervalIntegrable_cpow (μ := MeasureTheory.volume) (a := (k : ℝ) + 1) (b := (k : ℝ) + 2)
    (r := z) (Or.inl (by linarith : 0 ≤ z.re))
  have hi' := intervalIntegral.integral_sub
    (intervalIntegrable_const (c := ((k : ℂ) + 1) ^ z)) hi
  have heq : ((k : ℂ) + 1) ^ z -
      (∫ x : ℝ in (k : ℝ) + 1..(k : ℝ) + 2, (x : ℂ) ^ z) =
      ∫ x : ℝ in (k : ℝ) + 1..(k : ℝ) + 2, (((k : ℂ) + 1) ^ z - (x : ℂ) ^ z) := by
    rw [hi', intervalIntegral.integral_const, show (k : ℝ) + 2 - (k + 1) = 1 by ring, one_smul]
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (k : ℝ) + 1) (b := (k : ℝ) + 2) (C := C)
    (f := fun x : ℝ ↦ ((k : ℂ) + 1) ^ z - (x : ℂ) ^ z) (by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      have hx' : x ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2) := ⟨hx.1.le, hx.2⟩
      have hdiff := (convex_Icc ((k : ℝ) + 1) ((k : ℝ) + 2)).norm_image_sub_le_of_norm_deriv_le
        (fun t ht ↦ (hderiv t ht).differentiableAt)
        (fun t ht ↦ (hderiv t ht).deriv ▸ hbound t ht) hx'
        (left_mem_Icc.mpr (by linarith))
      simp only [ofReal_add, ofReal_natCast, ofReal_one] at hdiff
      apply hdiff.trans
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.1])]
      exact (mul_le_mul_of_nonneg_left (by linarith [hx.2] : -((k : ℝ) + 1 - x) ≤ 1) hC).trans_eq
        (mul_one _))
  simpa [show (k : ℝ) + 2 - (k + 1) = 1 by ring] using h

/-- The partial sum of complex powers on the positive integers differs from its
integral between `1` and `N + 1` by at most `N ‖z‖ (N + 1)^(Re z - 1)`. -/
theorem norm_sum_natCast_add_one_cpow_sub_integral_le {z : ℂ} (hz : 1 ≤ z.re) (N : ℕ) :
    ‖(∑ k ∈ range N, ((k : ℂ) + 1) ^ z) -
      (((N : ℂ) + 1) ^ (z + 1) - 1) / (z + 1)‖ ≤
      N * (‖z‖ * ((N : ℝ) + 1) ^ (z.re - 1)) := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ ↦ (n : ℝ) + 1)
    (n := N) (f := fun x : ℝ ↦ (x : ℂ) ^ z) (μ := MeasureTheory.volume)
    (fun _ _ ↦ intervalIntegral.intervalIntegrable_cpow (Or.inl (by linarith : 0 ≤ z.re)))
  rw [integral_cpow (Or.inl (by linarith : -1 < z.re))] at hi
  simp only [Nat.cast_zero, zero_add, ofReal_one, ofReal_add, ofReal_natCast, one_cpow] at hi
  rw [← hi, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ range N, ‖z‖ * ((N : ℝ) + 1) ^ (z.re - 1) := by
        apply sum_le_sum
        intro k hk
        simpa only [Nat.cast_add, Nat.cast_one, show (k : ℝ) + 1 + 1 = k + 2 by ring] using
          norm_cpow_unit_interval_error hz (mem_range.mp hk)
    _ = _ := by simp [nsmul_eq_mul]

/-- Dividing the partial sum by the upper endpoint power gives the Mellin multiplier
`1 / (z + 1)`. The estimate is uniform in the integer cutoff and explicit in `z`. -/
theorem norm_sum_natCast_add_one_cpow_div_sub_inv_le {z : ℂ} (hz : 1 ≤ z.re) (N : ℕ) :
    ‖(∑ k ∈ range N, ((k : ℂ) + 1) ^ z) / ((N : ℂ) + 1) ^ (z + 1) - (z + 1)⁻¹‖ ≤
      (‖z‖ + ‖(z + 1)⁻¹‖) / ((N : ℝ) + 1) := by
  let Y := (N : ℝ) + 1
  let W := ((N : ℂ) + 1) ^ (z + 1)
  let A := ∑ k ∈ range N, ((k : ℂ) + 1) ^ z
  have hY : 1 ≤ Y := by dsimp [Y]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hz' : z + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at h'
    linarith
  have hWnorm : ‖W‖ = Y ^ (z.re + 1) := by
    change ‖((N : ℂ) + 1) ^ (z + 1)‖ = _
    rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos hY0,
      add_re, ofReal_re]
  have hW : W ≠ 0 := norm_ne_zero_iff.mp (hWnorm ▸ (Real.rpow_pos_of_pos hY0 _).ne')
  have herr : ‖A - (W - 1) / (z + 1)‖ ≤ N * (‖z‖ * Y ^ (z.re - 1)) :=
    norm_sum_natCast_add_one_cpow_sub_integral_le hz N
  change ‖A / W - (z + 1)⁻¹‖ ≤ _
  have hid : A / W - (z + 1)⁻¹ = (A - (W - 1) / (z + 1) - (z + 1)⁻¹) / W := by
    field_simp
    ring
  rw [hid, norm_div, hWnorm, div_le_div_iff₀ (Real.rpow_pos_of_pos hY0 _) hY0]
  have hf : 1 ≤ Y ^ (z.re - 1) := Real.one_le_rpow hY (by linarith)
  have hN : (N : ℝ) ≤ Y := by dsimp [Y]; linarith
  have hA := (norm_sub_le (A - (W - 1) / (z + 1)) ((z + 1)⁻¹)).trans
    (add_le_add_left herr _)
  have hpow : Y ^ (z.re + 1) = (Y ^ (z.re - 1) * Y) * Y := by
    rw [show z.re + 1 = ((z.re - 1) + 1) + 1 by ring,
      Real.rpow_add hY0, Real.rpow_add hY0, Real.rpow_one]
  rw [hpow, ← mul_assoc (‖z‖ + ‖(z + 1)⁻¹‖) (Y ^ (z.re - 1) * Y) Y]
  apply mul_le_mul_of_nonneg_right _ hY0.le
  have hbig : 1 ≤ Y ^ (z.re - 1) * Y := one_le_mul_of_one_le_of_one_le hf hY
  calc
    _ ≤ N * (‖z‖ * Y ^ (z.re - 1)) + ‖(z + 1)⁻¹‖ := hA
    _ ≤ Y * (‖z‖ * Y ^ (z.re - 1)) + ‖(z + 1)⁻¹‖ * (Y ^ (z.re - 1) * Y) :=
      add_le_add (mul_le_mul_of_nonneg_right hN (by positivity))
        (le_mul_of_one_le_right (norm_nonneg _) hbig)
    _ = _ := by ring

/-- The normalized complex power sum converges to the multiplier of the corresponding
Fourier mode on a logarithmic grid. -/
theorem tendsto_sum_natCast_add_one_cpow_div_cpow {z : ℂ} (hz : 1 ≤ z.re) :
    Filter.Tendsto (fun N : ℕ ↦ (∑ k ∈ range N, ((k : ℂ) + 1) ^ z) / ((N : ℂ) + 1) ^ (z + 1))
      Filter.atTop (nhds (z + 1)⁻¹) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun N ↦ norm_sum_natCast_add_one_cpow_div_sub_inv_le hz N)
  exact tendsto_const_nhds.div_atTop
    (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop : Filter.Tendsto (Nat.cast : ℕ → ℝ) _ _)
      tendsto_const_nhds)


end RiemannMasullo
