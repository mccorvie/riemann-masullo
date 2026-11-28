module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-! # A sharp finite bound for fourth-power deficits

The first input bounds the negative side of a centered function. The second bounds the
one-sided cost of replacing it by the sampled function. Both hypotheses concern real values
at cutoffs at least one. -/

public section

namespace RiemannMasullo

/-- A first-mean lower bound at exponent `b + 1` and a replacement error of order
`x * √x` give the exact cumulative exponent `4*b + 5` on fourth powers. -/
theorem sum_fourthPower_negPart_le_of_pointwise (full prime : ℝ → ℝ) {b C E : ℝ}
    (hb : 1 / 2 ≤ b) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hlower : ∀ x : ℝ, 1 ≤ x → -full x ≤ C * x ^ (b + 1))
    (hreplace : ∀ x : ℝ, 1 ≤ x → full x - prime x ≤ E * (x * Real.sqrt x))
    (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, max (-(prime ((j : ℝ) ^ 4))) 0 ≤
      (C + E) * (J : ℝ) ^ (4 * b + 5) := by
  have hb₁ : 0 ≤ b + 1 := by linarith
  have hsample {j : ℕ} (hj : j ∈ Finset.Icc 1 J) :
      max (-(prime ((j : ℝ) ^ 4))) 0 ≤ (C + E) * (J : ℝ) ^ (4 * (b + 1)) := by
    let x := (j : ℝ) ^ 4
    have hj₁ : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hx : 1 ≤ x := one_le_pow₀ hj₁
    have hpow : x * Real.sqrt x ≤ x ^ (b + 1) := by
      calc
        x * Real.sqrt x = x ^ ((1 : ℝ) + 1 / 2) := by
          rw [Real.rpow_add (zero_lt_one.trans_le hx), Real.rpow_one, Real.sqrt_eq_rpow]
        _ ≤ x ^ (b + 1) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hlocal : max (-prime x) 0 ≤ (C + E) * x ^ (b + 1) := by
      refine max_le ?_ (mul_nonneg (add_nonneg hC hE) (Real.rpow_nonneg (by linarith) _))
      nlinarith only [hlower x hx, hreplace x hx, mul_le_mul_of_nonneg_left hpow hE]
    have hs : x ^ (b + 1) = (j : ℝ) ^ (4 * (b + 1)) := by
      rw [Real.rpow_mul (Nat.cast_nonneg j)]
      dsimp [x]
      norm_cast
    apply hlocal.trans
    apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hE)
    rw [hs]
    exact Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast (Finset.mem_Icc.mp hj).2)
      (by positivity)
  calc
    ∑ j ∈ Finset.Icc 1 J, max (-(prime ((j : ℝ) ^ 4))) 0 ≤
        ∑ _j ∈ Finset.Icc 1 J, (C + E) * (J : ℝ) ^ (4 * (b + 1)) :=
      Finset.sum_le_sum fun _ hj ↦ hsample hj
    _ = (J : ℝ) * ((C + E) * (J : ℝ) ^ (4 * (b + 1))) := by simp [Nat.card_Icc]
    _ = (C + E) * (J : ℝ) ^ (4 * b + 5) := by
      rw [show 4 * b + 5 = 4 * (b + 1) + 1 by ring,
        Real.rpow_add_of_nonneg (Nat.cast_nonneg J) (by positivity) zero_le_one, Real.rpow_one]
      ring

end RiemannMasullo
