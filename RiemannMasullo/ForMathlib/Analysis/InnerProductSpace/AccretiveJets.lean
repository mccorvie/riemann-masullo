module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Data.Nat.Factorial.Basic

/-! # Accretive operators on jets

Let `P` be a bounded operator of a complex Hilbert space with `c * ‖P g‖ ^ 2 ≤ re ⟪g, P g⟫`
and `‖P† g‖ ≤ ‖P g‖`: for instance the Laplace transform at rate `c` of a unitary group, that
is, convolution with the one-sided exponential `p x = exp (-c * x)`, `x > 0`. Multiplying a
convolution `p ⋆ f` by `x ^ j` gives `∑ i ≤ j, (j ! / i !) • P ^ (j - i + 1) (x ^ i f)`, because
`y ^ m * p y` is `m !` times the `(m + 1)`-fold convolution power of `p`. So on the moments
`g i = x ^ i f` the operator acts by a lower triangular matrix whose diagonal entries are `P`.

`two_thirds_mul_sum_le_re_sum_inner_jet` says that this triangular operator is still accretive,
with the constant `2 / 3`, as soon as `4 * k ≤ c`, where `k` is the highest moment: the terms
below the diagonal are absorbed. `two_thirds_mul_sum_le_re_sum_inner_jet_add` is the same for
the sum of a forward and a backward transform, with the signs that the backward one carries. -/

@[expose] public section

open Finset
open scoped InnerProductSpace

namespace RiemannMasullo

/-- A geometric sum with ratio one quarter, written from the top. -/
theorem sum_range_quarter_pow_sub_le (n : ℕ) :
    ∑ i ∈ range n, ((1 : ℝ) / 4) ^ (n - i) ≤ 1 / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have h : ∀ i ∈ range n, ((1 : ℝ) / 4) ^ (n + 1 - i) = 1 / 4 * (1 / 4) ^ (n - i) := by
      intro i hi
      rw [Nat.succ_sub (mem_range.mp hi).le, pow_succ']
    rw [sum_congr rfl h, ← mul_sum, Nat.add_sub_cancel_left, pow_one]
    linarith

/-- A triangular sum with geometric weights is at most one third of the diagonal sum. -/
theorem sum_triangle_quarter_pow_le (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (n : ℕ) :
    ∑ j ∈ range n, ∑ i ∈ range j, ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2) ≤
      1 / 3 * ∑ j ∈ range n, A j := by
  have key : ∀ n : ℕ,
      ∑ j ∈ range n, ∑ i ∈ range j, ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2) +
        2 / 3 * ∑ i ∈ range n, ((1 : ℝ) / 4) ^ (n - i) * A i ≤ 1 / 3 * ∑ j ∈ range n, A j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : ∀ i ∈ range n,
          ((1 : ℝ) / 4) ^ (n + 1 - i) * A i = 1 / 4 * ((1 / 4) ^ (n - i) * A i) := by
        intro i hi
        rw [Nat.succ_sub (mem_range.mp hi).le, pow_succ']
        ring
      have h2 : ∑ i ∈ range n, ((1 : ℝ) / 4) ^ (n - i) * ((A n + A i) / 2) =
          A n / 2 * ∑ i ∈ range n, ((1 : ℝ) / 4) ^ (n - i) +
            1 / 2 * ∑ i ∈ range n, ((1 : ℝ) / 4) ^ (n - i) * A i := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ ↦ by ring
      rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_congr rfl h1, ← mul_sum, h2,
        Nat.add_sub_cancel_left, pow_one]
      have hG := mul_le_mul_of_nonneg_left (sum_range_quarter_pow_sub_le n)
        (div_nonneg (hA n) (by norm_num : (0 : ℝ) ≤ 2))
      linarith
  have hT : 0 ≤ ∑ i ∈ range n, ((1 : ℝ) / 4) ^ (n - i) * A i :=
    sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (hA i)
  linarith [key n]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- An accretive operator with constant `c` has norm at most `c⁻¹`. -/
theorem norm_apply_le_of_accretive (P : G →L[ℂ] G) {c : ℝ} (hc : 0 < c)
    (hP : ∀ g, c * ‖P g‖ ^ 2 ≤ (⟪g, P g⟫_ℂ).re) (g : G) : ‖P g‖ ≤ c⁻¹ * ‖g‖ := by
  have h1 : c * ‖P g‖ ^ 2 ≤ ‖g‖ * ‖P g‖ := (hP g).trans (re_inner_le_norm (𝕜 := ℂ) g (P g))
  rcases (norm_nonneg (P g)).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : c * ‖P g‖ ≤ ‖g‖ := by
      refine le_of_mul_le_mul_right ?_ hpos
      calc c * ‖P g‖ * ‖P g‖ = c * ‖P g‖ ^ 2 := by ring
        _ ≤ ‖g‖ * ‖P g‖ := h1
    rw [le_inv_mul_iff₀ hc]
    exact h2

/-- The powers of an accretive operator with constant `c` decay like `c⁻¹ ^ n`. -/
theorem norm_pow_apply_le_of_accretive (P : G →L[ℂ] G) {c : ℝ} (hc : 0 < c)
    (hP : ∀ g, c * ‖P g‖ ^ 2 ≤ (⟪g, P g⟫_ℂ).re) (n : ℕ) (v : G) :
    ‖(P ^ n) v‖ ≤ c⁻¹ ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (P ^ (n + 1)) v = P ((P ^ n) v) := by rw [pow_succ']; rfl
    rw [h, pow_succ', mul_assoc]
    exact (norm_apply_le_of_accretive P hc hP _).trans
      (mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr hc.le))

/-- Pairings against higher powers of an accretive operator whose adjoint it dominates are
controlled by the first power on both sides. -/
theorem norm_inner_pow_add_two_le (P : G →L[ℂ] G) {c : ℝ} (hc : 0 < c)
    (hP : ∀ g, c * ‖P g‖ ^ 2 ≤ (⟪g, P g⟫_ℂ).re)
    (hP' : ∀ g, ‖ContinuousLinearMap.adjoint P g‖ ≤ ‖P g‖) (m : ℕ) (u v : G) :
    ‖⟪u, (P ^ (m + 2)) v⟫_ℂ‖ ≤ c⁻¹ ^ m * (‖P u‖ * ‖P v‖) := by
  have h : (P ^ (m + 2)) v = P ((P ^ m) (P v)) := by
    rw [pow_succ' P (m + 1), pow_succ P m]
    rfl
  rw [h, ← ContinuousLinearMap.adjoint_inner_left]
  calc ‖⟪ContinuousLinearMap.adjoint P u, (P ^ m) (P v)⟫_ℂ‖
      ≤ ‖ContinuousLinearMap.adjoint P u‖ * ‖(P ^ m) (P v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖P u‖ * (c⁻¹ ^ m * ‖P v‖) :=
      mul_le_mul (hP' u) (norm_pow_apply_le_of_accretive P hc hP m (P v)) (norm_nonneg _)
        (norm_nonneg _)
    _ = c⁻¹ ^ m * (‖P u‖ * ‖P v‖) := by ring

/-- The terms below the diagonal: for `i < j ≤ k` and `4 * k ≤ c`, the pairing of `g j` with
`(j ! / i !) • P ^ (j - i + 1) (g i)` is at most `(1 / 4) ^ (j - i)` times the mean of the two
diagonal terms. -/
theorem norm_descFactorial_mul_inner_pow_le (P : G →L[ℂ] G) {c : ℝ} (k : ℕ) (hc : 0 < c)
    (hk : 4 * (k : ℝ) ≤ c) (hP : ∀ g, c * ‖P g‖ ^ 2 ≤ (⟪g, P g⟫_ℂ).re)
    (hP' : ∀ g, ‖ContinuousLinearMap.adjoint P g‖ ≤ ‖P g‖) {e : ℂ} (he : ‖e‖ ≤ 1)
    {i j : ℕ} (hij : i < j) (hjk : j ≤ k) (u v : G) :
    ‖(j.descFactorial (j - i) : ℂ) * e * ⟪u, (P ^ (j - i + 1)) v⟫_ℂ‖ ≤
      ((1 : ℝ) / 4) ^ (j - i) * ((c * ‖P u‖ ^ 2 + c * ‖P v‖ ^ 2) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m, j - i = m + 1 := ⟨j - i - 1, by omega⟩
  rw [hm]
  have hinner := norm_inner_pow_add_two_le P hc hP hP' m u v
  have hd : (j.descFactorial (m + 1) : ℝ) ≤ (k : ℝ) ^ (m + 1) := by
    calc (j.descFactorial (m + 1) : ℝ) ≤ (j : ℝ) ^ (m + 1) := by
          exact_mod_cast Nat.descFactorial_le_pow j (m + 1)
      _ ≤ (k : ℝ) ^ (m + 1) := by gcongr
  have hkc : (k : ℝ) * c⁻¹ ≤ 1 / 4 := by
    rw [mul_inv_le_iff₀ hc]
    linarith
  have hpow : (k : ℝ) ^ (m + 1) * c⁻¹ ^ (m + 1) ≤ (1 / 4) ^ (m + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hkc _
  have hmean : c * (‖P u‖ * ‖P v‖) ≤ (c * ‖P u‖ ^ 2 + c * ‖P v‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖P u‖ - ‖P v‖), mul_nonneg hc.le (sq_nonneg (‖P u‖ - ‖P v‖))]
  have hprod : 0 ≤ ‖P u‖ * ‖P v‖ := by positivity
  have hcm : c⁻¹ ^ m = c * c⁻¹ ^ (m + 1) := by
    rw [pow_succ]
    field_simp
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  calc (j.descFactorial (m + 1) : ℝ) * ‖e‖ * ‖⟪u, (P ^ (m + 1 + 1)) v⟫_ℂ‖
      ≤ (k : ℝ) ^ (m + 1) * 1 * (c⁻¹ ^ m * (‖P u‖ * ‖P v‖)) := by
        gcongr
    _ = (k : ℝ) ^ (m + 1) * c⁻¹ ^ (m + 1) * (c * (‖P u‖ * ‖P v‖)) := by
        rw [hcm]
        ring
    _ ≤ (1 / 4) ^ (m + 1) * ((c * ‖P u‖ ^ 2 + c * ‖P v‖ ^ 2) / 2) :=
        mul_le_mul hpow hmean (mul_nonneg hc.le hprod) (by positivity)

/-- An accretive operator stays accretive on jets. If `c * ‖P g‖ ^ 2 ≤ re ⟪g, P g⟫`,
`‖P† g‖ ≤ ‖P g‖` and `4 * k ≤ c`, then the lower triangular operator with entries
`(j ! / i !) * e (j - i) • P ^ (j - i + 1)`, `i ≤ j ≤ k`, where `e 0 = 1` and `‖e m‖ ≤ 1`,
satisfies the same inequality with the constant `2 / 3`. -/
theorem two_thirds_mul_sum_le_re_sum_inner_jet (P : G →L[ℂ] G) {c : ℝ} (k : ℕ) (hc : 0 < c)
    (hk : 4 * (k : ℝ) ≤ c) (hP : ∀ g, c * ‖P g‖ ^ 2 ≤ (⟪g, P g⟫_ℂ).re)
    (hP' : ∀ g, ‖ContinuousLinearMap.adjoint P g‖ ≤ ‖P g‖)
    (e : ℕ → ℂ) (he₀ : e 0 = 1) (he : ∀ m, ‖e m‖ ≤ 1) (g : ℕ → G) :
    2 / 3 * ∑ j ∈ range (k + 1), c * ‖P (g j)‖ ^ 2 ≤
      (∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1),
        (j.descFactorial (j - i) : ℂ) * e (j - i) * ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ).re := by
  set A : ℕ → ℝ := fun j ↦ c * ‖P (g j)‖ ^ 2 with hA
  have hA₀ : ∀ j, 0 ≤ A j := fun j ↦ by positivity
  have hrow : ∀ j ∈ range (k + 1),
      A j - ∑ i ∈ range j, ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2) ≤
        (∑ i ∈ range (j + 1),
          (j.descFactorial (j - i) : ℂ) * e (j - i) * ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ).re := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [sum_range_succ, Complex.add_re, Complex.re_sum]
    have hdiag : A j ≤ ((j.descFactorial (j - j) : ℂ) * e (j - j) *
        ⟪g j, (P ^ (j - j + 1)) (g j)⟫_ℂ).re := by
      simpa [he₀] using hP (g j)
    have hoff : -∑ i ∈ range j, ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2) ≤
        ∑ i ∈ range j,
          ((j.descFactorial (j - i) : ℂ) * e (j - i) * ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ).re := by
      rw [← sum_neg_distrib]
      refine sum_le_sum fun i hi ↦ ?_
      have hb : ‖(j.descFactorial (j - i) : ℂ) * e (j - i) *
          ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ‖ ≤ ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2) :=
        norm_descFactorial_mul_inner_pow_le P k hc hk hP hP' (he (j - i))
          (mem_range.mp hi) hjk (g j) (g i)
      generalize (j.descFactorial (j - i) : ℂ) * e (j - i) *
        ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ = z at hb ⊢
      have hre := Complex.abs_re_le_norm z
      linarith [neg_abs_le z.re]
    linarith
  calc 2 / 3 * ∑ j ∈ range (k + 1), A j
      ≤ ∑ j ∈ range (k + 1), A j -
          ∑ j ∈ range (k + 1), ∑ i ∈ range j, ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2) := by
        linarith [sum_triangle_quarter_pow_le A hA₀ (k + 1)]
    _ = ∑ j ∈ range (k + 1),
          (A j - ∑ i ∈ range j, ((1 : ℝ) / 4) ^ (j - i) * ((A j + A i) / 2)) := by
        rw [sum_sub_distrib]
    _ ≤ ∑ j ∈ range (k + 1), (∑ i ∈ range (j + 1),
          (j.descFactorial (j - i) : ℂ) * e (j - i) * ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ).re :=
        sum_le_sum hrow
    _ = _ := by rw [Complex.re_sum]

/-- The sum of a forward and a backward accretive operator stays accretive on jets, with the
alternating signs that the moments of the backward one carry. -/
theorem two_thirds_mul_sum_le_re_sum_inner_jet_add (P Q : G →L[ℂ] G) {c₁ c₂ : ℝ} (k : ℕ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hk₁ : 4 * (k : ℝ) ≤ c₁) (hk₂ : 4 * (k : ℝ) ≤ c₂)
    (hP : ∀ g, c₁ * ‖P g‖ ^ 2 ≤ (⟪g, P g⟫_ℂ).re) (hQ : ∀ g, c₂ * ‖Q g‖ ^ 2 ≤ (⟪g, Q g⟫_ℂ).re)
    (hP' : ∀ g, ‖ContinuousLinearMap.adjoint P g‖ ≤ ‖P g‖)
    (hQ' : ∀ g, ‖ContinuousLinearMap.adjoint Q g‖ ≤ ‖Q g‖) (g : ℕ → G) :
    2 / 3 * ∑ j ∈ range (k + 1), (c₁ * ‖P (g j)‖ ^ 2 + c₂ * ‖Q (g j)‖ ^ 2) ≤
      (∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1), (j.descFactorial (j - i) : ℂ) *
        (⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ +
          (-1) ^ (j - i) * ⟪g j, (Q ^ (j - i + 1)) (g i)⟫_ℂ)).re := by
  have h1 := two_thirds_mul_sum_le_re_sum_inner_jet P k hc₁ hk₁ hP hP' (fun _ ↦ 1) rfl
    (fun _ ↦ by simp) g
  have h2 := two_thirds_mul_sum_le_re_sum_inner_jet Q k hc₂ hk₂ hQ hQ' (fun m ↦ (-1) ^ m)
    (by simp) (fun m ↦ by simp) g
  have hsplit : (∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1), (j.descFactorial (j - i) : ℂ) *
        (⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ +
          (-1) ^ (j - i) * ⟪g j, (Q ^ (j - i + 1)) (g i)⟫_ℂ)) =
      (∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1),
        (j.descFactorial (j - i) : ℂ) * (1 : ℂ) * ⟪g j, (P ^ (j - i + 1)) (g i)⟫_ℂ) +
      ∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1),
        (j.descFactorial (j - i) : ℂ) * (-1) ^ (j - i) * ⟪g j, (Q ^ (j - i + 1)) (g i)⟫_ℂ := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hsplit, Complex.add_re, sum_add_distrib, mul_add]
  exact add_le_add h1 h2

end RiemannMasullo
