module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # A smooth partition of unity on a bounded interval of the line

For every width `δ > 0` and every radius `R` there are finitely many smooth functions on the
line, with values in `[-1, 1]`, each vanishing outside an interval of half-length `δ`, whose sum
is one on `[-R, R]` (`exists_smooth_partition_Icc`). They are differences of translates of the
smooth step `Real.smoothTransition`, so the sum telescopes. -/

@[expose] public section

open Real
open scoped ContDiff

namespace RiemannMasullo

/-- For every width `δ > 0` and every radius `R` there are finitely many smooth functions
`η k` on the line, bounded by one in absolute value, with `η k` vanishing outside the interval
of half-length `δ` around a centre `t k`, whose sum is one on `[-R, R]`. -/
theorem exists_smooth_partition_Icc {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ (J : ℕ) (η : ℕ → ℝ → ℝ) (t : ℕ → ℝ), (∀ k, ContDiff ℝ ∞ (η k)) ∧
      (∀ k r, |η k r| ≤ 1) ∧ (∀ k r, η k r ≠ 0 → |r - t k| ≤ δ) ∧
      ∀ r, |r| ≤ R → ∑ k ∈ Finset.range J, η k r = 1 := by
  let J₀ : ℕ := ⌈R / δ⌉₊ + 1
  have hJ₀ : R / δ + 1 ≤ J₀ := by
    have := Nat.le_ceil (R / δ)
    push_cast [J₀]
    linarith
  let g (r : ℝ) (k : ℕ) : ℝ := smoothTransition (r / δ + J₀ - k)
  refine ⟨2 * J₀, fun k r ↦ g r k - g r (k + 1), fun k ↦ (k + 1 - J₀ : ℝ) * δ,
    fun k ↦ ?_, fun k r ↦ ?_, fun k r hne ↦ ?_, fun r hr ↦ ?_⟩
  · exact (smoothTransition.contDiff.comp (by fun_prop)).sub
      (smoothTransition.contDiff.comp (by fun_prop))
  · have h1 := smoothTransition.nonneg (r / δ + J₀ - k)
    have h2 := smoothTransition.le_one (r / δ + J₀ - k)
    have h3 := smoothTransition.nonneg (r / δ + J₀ - (k + 1 : ℕ))
    have h4 := smoothTransition.le_one (r / δ + J₀ - (k + 1 : ℕ))
    change |smoothTransition (r / δ + J₀ - k) - smoothTransition (r / δ + J₀ - (k + 1 : ℕ))| ≤ 1
    rw [abs_le]
    constructor <;> linarith
  · change smoothTransition (r / δ + J₀ - k) - smoothTransition (r / δ + J₀ - (k + 1 : ℕ)) ≠ 0
      at hne
    have hu0 : 0 < r / δ + J₀ - k := by
      by_contra h
      have h' := not_lt.mp h
      rw [smoothTransition.zero_of_nonpos h', smoothTransition.zero_of_nonpos
        (by push_cast; linarith)] at hne
      exact hne (sub_self 0)
    have hu2 : r / δ + J₀ - k < 2 := by
      by_contra h
      have h' := not_lt.mp h
      rw [smoothTransition.one_of_one_le (by linarith), smoothTransition.one_of_one_le
        (by push_cast; linarith)] at hne
      exact hne (sub_self 1)
    have hrd : r = r / δ * δ := (div_mul_cancel₀ r hδ.ne').symm
    rw [abs_le]
    constructor <;> nlinarith
  · have hsum : ∑ k ∈ Finset.range (2 * J₀), (g r k - g r (k + 1)) = g r 0 - g r (2 * J₀) :=
      Finset.sum_range_sub' (g r) (2 * J₀)
    have hrδ : |r / δ| ≤ R / δ := by
      rw [abs_div, abs_of_pos hδ]
      exact div_le_div_of_nonneg_right hr hδ.le
    have h0 : g r 0 = 1 := by
      change smoothTransition (r / δ + J₀ - (0 : ℕ)) = 1
      refine smoothTransition.one_of_one_le ?_
      push_cast
      linarith [neg_abs_le (r / δ)]
    have h1 : g r (2 * J₀) = 0 := by
      change smoothTransition (r / δ + J₀ - ((2 * J₀ : ℕ) : ℝ)) = 0
      refine smoothTransition.zero_of_nonpos ?_
      push_cast
      linarith [le_abs_self (r / δ)]
    rw [hsum, h0, h1, sub_zero]

end RiemannMasullo
