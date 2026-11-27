module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-! # Finite strip jet energy

The triangular Leibniz product is bounded in the unweighted finite jet norm. If the
off-diagonal coefficient sum is at most half the real diagonal coefficient, the
product is coercive in that same energy.
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

namespace RiemannMasullo.HigherStripEnergy

/-- Zero padding matters: natural subtraction alone would repeat the zeroth entry. -/
private def shift (x : ℕ → ℝ) (k j : ℕ) : ℝ := if k ≤ j then x (j - k) else 0

private theorem shift_sq (x : ℕ → ℝ) (n k : ℕ) :
    ∑ j ∈ range n, (shift x k j) ^ 2 ≤ ∑ j ∈ range n, (x j) ^ 2 := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp [shift]
    | succ k =>
      calc
        ∑ j ∈ range (n + 1), (shift x (k + 1) j) ^ 2 =
            ∑ j ∈ range n, (shift x k j) ^ 2 := by
              rw [sum_range_succ']; simp [shift]
        _ ≤ ∑ j ∈ range n, (x j) ^ 2 := ih k
        _ ≤ ∑ j ∈ range (n + 1), (x j) ^ 2 := by
              rw [sum_range_succ]; exact le_add_of_nonneg_right (sq_nonneg _)

private theorem shift_cross (x : ℕ → ℝ) (n k : ℕ) :
    ∑ j ∈ range n, x j * shift x k j ≤ ∑ j ∈ range n, (x j) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ range n, ((x j) ^ 2 + (shift x k j) ^ 2) / 2 := by
      apply sum_le_sum; intro j _; nlinarith [sq_nonneg (x j - shift x k j)]
    _ ≤ _ := by
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul, sum_add_distrib]
      linarith [shift_sq x n k]

/-- Pointwise coercivity in the order-`m` strip jet energy. The arrays are indexed
by naturals for convenience; no value at an index above `m` is used. `hprod` is the
usual binomial Leibniz expansion, not a differentiability hypothesis. -/
theorem leibniz_re_lower (m : ℕ) (κ ψ prodJet : ℕ → ℂ)
    (hprod : ∀ j ≤ m, prodJet j =
      ∑ k ∈ range (j + 1), (j.choose k : ℂ) * ψ k * κ (j - k))
    (hcoeff : (∑ r ∈ range m, (m.choose (r + 1) : ℝ) * ‖ψ (r + 1)‖) ≤
      (ψ 0).re / 2) :
    (ψ 0).re / 2 * (∑ j ∈ range (m + 1), ‖κ j‖ ^ 2) ≤
      ∑ j ∈ range (m + 1), (conj (κ j) * prodJet j).re := by
  let x (j : ℕ) := ‖κ j‖
  let E := ∑ j ∈ range (m + 1), (x j) ^ 2
  let c (r : ℕ) := (m.choose (r + 1) : ℝ) * ‖ψ (r + 1)‖
  let q (j k : ℕ) := (j.choose k : ℂ) * ψ k * κ (j - k)
  let err (j r : ℕ) := -(conj (κ j) * q j (r + 1)).re
  have hc (r : ℕ) : 0 ≤ c r := by dsimp [c]; positivity
  have hrow (j : ℕ) (hj : j ≤ m) :
      prodJet j = (∑ r ∈ range m, q j (r + 1)) + ψ 0 * κ j := by
    calc
      prodJet j = ∑ k ∈ range (j + 1), q j k := hprod j hj
      _ = ∑ k ∈ range (m + 1), q j k := by
        apply sum_subset (range_mono (Nat.succ_le_succ hj))
        intro k _ hk
        have hjk : j < k := by simp only [mem_range] at hk; omega
        simp [q, Nat.choose_eq_zero_of_lt hjk]
      _ = _ := by rw [sum_range_succ']; simp [q]
  have hdiag (j : ℕ) : (conj (κ j) * (ψ 0 * κ j)).re = (ψ 0).re * (x j) ^ 2 := by
    rw [show conj (κ j) * (ψ 0 * κ j) = ψ 0 * (conj (κ j) * κ j) by ring,
      ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.normSq_eq_norm_sq, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, x]
  have herr (j r : ℕ) (hj : j ≤ m) : err j r ≤ c r * (x j * shift x (r + 1) j) := by
    by_cases hk : r + 1 ≤ j
    · have hchoose : (j.choose (r + 1) : ℝ) ≤ (m.choose (r + 1) : ℝ) := by
        exact_mod_cast Nat.choose_le_choose (r + 1) hj
      calc
        err j r ≤ |(conj (κ j) * q j (r + 1)).re| := neg_le_abs _
        _ ≤ ‖conj (κ j) * q j (r + 1)‖ := Complex.abs_re_le_norm _
        _ = (j.choose (r + 1) : ℝ) * ‖ψ (r + 1)‖ * (x j * shift x (r + 1) j) := by
          simp only [q, norm_mul, Complex.norm_conj, Complex.norm_natCast, shift, ite_eq_left hk, x]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose (norm_nonneg _))
          simp only [shift, ite_eq_left hk, x]
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · simp [err, q, shift, hk, Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]
  have hcol (r : ℕ) : ∑ j ∈ range (m + 1), err j r ≤ c r * E := by
    calc
      _ ≤ ∑ j ∈ range (m + 1), c r * (x j * shift x (r + 1) j) := by
        apply sum_le_sum; intro j hj; exact herr j r (mem_range_succ_iff.mp hj)
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (shift_cross x _ _) (hc r)
  have htotal : (∑ j ∈ range (m + 1), ∑ r ∈ range m, err j r) ≤ (ψ 0).re / 2 * E := by
    calc
      _ = ∑ r ∈ range m, ∑ j ∈ range (m + 1), err j r := sum_comm
      _ ≤ ∑ r ∈ range m, c r * E := sum_le_sum fun r _ => hcol r
      _ ≤ _ := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right hcoeff (sum_nonneg fun j _ ↦ sq_nonneg (x j))
  have hexpand : (∑ j ∈ range (m + 1), (conj (κ j) * prodJet j).re) =
      (ψ 0).re * E - ∑ j ∈ range (m + 1), ∑ r ∈ range m, err j r := by
    dsimp only [E]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro j hj
    rw [hrow j (mem_range_succ_iff.mp hj), mul_add, mul_sum, Complex.add_re, Complex.re_sum, hdiag]
    simp only [err, sum_neg_distrib]; ring
  rw [hexpand]
  change (ψ 0).re / 2 * E ≤ _
  linarith


/-- Upper energy bound for the binomial Leibniz product of two finite jets. -/
theorem leibniz_norm_sq_upper (m : ℕ) (κ ψ prodJet : ℕ → ℂ)
    (hprod : ∀ j ≤ m, prodJet j =
      ∑ k ∈ range (j + 1), (j.choose k : ℂ) * ψ k * κ (j - k)) :
    (∑ j ∈ range (m + 1), ‖prodJet j‖ ^ 2) ≤
      (∑ k ∈ range (m + 1), (m.choose k : ℝ) * ‖ψ k‖) ^ 2 *
        ∑ j ∈ range (m + 1), ‖κ j‖ ^ 2 := by
  let s := range (m + 1)
  let c (k : ℕ) := (m.choose k : ℝ) * ‖ψ k‖
  let x (j : ℕ) := ‖κ j‖
  let C := ∑ k ∈ s, c k
  let E := ∑ j ∈ s, (x j) ^ 2
  have hc (k : ℕ) : 0 ≤ c k := by dsimp [c]; positivity
  have hC : 0 ≤ C := sum_nonneg fun k _ => hc k
  have hrow (j : ℕ) (hj : j ≤ m) : ‖prodJet j‖ ≤ ∑ k ∈ s, c k * shift x k j := by
    rw [hprod j hj]
    calc
      _ ≤ ∑ k ∈ range (j + 1), ‖(j.choose k : ℂ) * ψ k * κ (j - k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range (j + 1), c k * shift x k j := by
        apply sum_le_sum; intro k hk
        have hkm := mem_range_succ_iff.mp hk
        have hchoose : (j.choose k : ℝ) ≤ (m.choose k : ℝ) := by
          exact_mod_cast Nat.choose_le_choose k hj
        simp only [norm_mul, Complex.norm_natCast, shift, ite_eq_left hkm, c, x]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by
        apply sum_subset (range_mono (Nat.succ_le_succ hj))
        intro k _ hk
        have hkj : ¬k ≤ j := fun h => hk (mem_range_succ_iff.mpr h)
        simp [shift, hkj]
  have hrow_sq (j : ℕ) (hj : j ≤ m) : ‖prodJet j‖ ^ 2 ≤
      C * ∑ k ∈ s, c k * (shift x k j) ^ 2 := by
    calc
      _ ≤ (∑ k ∈ s, c k * shift x k j) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hrow j hj) 2
      _ ≤ _ := by
        apply sum_sq_le_sum_mul_sum_of_sq_le_mul s (f := c)
          (g := fun k => c k * (shift x k j) ^ 2)
        · exact fun k _ => hc k
        · exact fun k _ => mul_nonneg (hc k) (sq_nonneg _)
        · intro k _; exact le_of_eq (by ring)
  change (∑ j ∈ s, ‖prodJet j‖ ^ 2) ≤ C ^ 2 * E
  calc
    _ ≤ ∑ j ∈ s, C * ∑ k ∈ s, c k * (shift x k j) ^ 2 :=
      sum_le_sum fun j hj => hrow_sq j (mem_range_succ_iff.mp hj)
    _ = C * ∑ k ∈ s, c k * ∑ j ∈ s, (shift x k j) ^ 2 := by
      rw [← mul_sum, sum_comm]; simp only [mul_sum]
    _ ≤ C * ∑ k ∈ s, c k * E := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (shift_sq x (m + 1) k) (hc k)
    _ = C ^ 2 * E := by rw [← sum_mul]; change C * (C * E) = C ^ 2 * E; ring

end RiemannMasullo.HigherStripEnergy
