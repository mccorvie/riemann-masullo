module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_DirichletZeroCount
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Arbitrarily close critical-line zeros of primitive Dirichlet L-functions

The refutation of the uniform constant after (10.3.1.18), p. 451 (`ERRATA.md`, F214; issue
#1169) needs two distinct critical-line zeros that lie arbitrarily close together. On `main`
that input is Selberg's count for the Riemann zeta function
(`spectralLineJet_rational_critical_zero_count` in `Sec3_Printed.lean`, issue #6742). PR #7538
shows that it is enough to have such pairs for some primitive Dirichlet character, which may
depend on the distance (`PrimitiveDirichletLCloseCriticalZeros` there).

This file proves that statement (`primitiveDirichletL_closeCriticalZeros`) from one theorem of
the literature, stated as a `Classical input:` with `sorry`:

* `conreyIwaniecSoundararajan_simpleCriticalZeros`: Conrey–Iwaniec–Soundararajan, *Critical
  zeros of Dirichlet L-functions*, arXiv:1105.1177, Theorem 1, (1.5), p. 2. On average over the
  primitive characters of modulus about `Q`, at least `14/25` of the zeros with `|γ| ≤ T` are
  simple zeros on the critical line, for `(log Q)^6 ≤ T ≤ (log Q)^A`.

The lower bound for the zero count that the argument also needs,
`2π N(T, χ) ≥ ⌊T/4⌋ (log (T/4)/2 - c) - 8 (log T/2 + log q + c)`, is proved in
`Sec3_DirichletZeroCount.lean` (`DirichletZeroCount.dirichletStripZeroCount_lower`), together with
the definitions of `N(T, χ)` and `N₀'(T, χ)`.

The argument. Fix one smooth weight `Ψ` supported in `[1, 4]` and take `T = (log Q)^6`. Every
character of the family has `N(T, χ) ≥ c T log T`, so by (1.5) some single character `χ` has at
least `(14/25) c T log T` simple critical-line zeros with `|γ| ≤ T`. A prime in `(Q, 2Q + 2]`
(Bertrand) makes the family nonempty. Those zeros have distinct ordinates in an interval of
length `2T`, so two of them are within `O(1 / log T)` of each other.

Nothing here is a statement of the paper. The file uses no formalization of the Riemann
hypothesis.
-/

@[expose] public section

open Complex Set
open scoped ContDiff

namespace RiemannMasullo

open scoped Classical in
/-- Classical input: J. B. Conrey, H. Iwaniec and K. Soundararajan, *Critical zeros of
Dirichlet L-functions*, arXiv:1105.1177 (v1, 2011), Theorem 1, (1.5), p. 2, with the sums
(1.4). Let `Ψ` be a non-negative smooth function, compactly supported on `ℝ⁺`, and
`A ≥ 6`. For `Q` sufficiently large and `(log Q)^6 ≤ T ≤ (log Q)^A`,
`N₀'(T, Q) ≥ (14/25) N(T, Q)`, where `N(T, Q) = ∑_q Ψ(q/Q)/φ(q) ∑*_{χ mod q} N(T, χ)` over the
primitive characters, and `N₀'(T, Q)` is the same sum with `N₀'(T, χ)`.

The sum over `q ≥ 1` has finitely many nonzero terms; here it is written over `q = n + 1` with
`n < M`, for any `M` beyond which the weight vanishes. Not a statement of the paper and not a
gap in it: a published theorem of which this project has no formal proof. It is the arithmetic
input for `primitiveDirichletL_closeCriticalZeros`. -/
theorem conreyIwaniecSoundararajan_simpleCriticalZeros (Ψ : ℝ → ℝ) (_hΨ : ∀ x, 0 ≤ Ψ x)
    (_hΨsmooth : ContDiff ℝ ∞ Ψ) (_hΨsupp : HasCompactSupport Ψ) (_hΨpos : tsupport Ψ ⊆ Ioi 0)
    (A : ℝ) (_hA : 6 ≤ A) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T : ℝ, Real.log Q ^ 6 ≤ T → T ≤ Real.log Q ^ A →
      ∀ M : ℕ, (∀ n : ℕ, M ≤ n → Ψ ((n + 1 : ℕ) / Q) = 0) →
        14 / 25 * ∑ n ∈ Finset.range M, Ψ ((n + 1 : ℕ) / Q) / (n + 1).totient *
            ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
              (dirichletStripZeroCount χ T : ℝ) ≤
          ∑ n ∈ Finset.range M, Ψ ((n + 1 : ℕ) / Q) / (n + 1).totient *
            ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
              (dirichletSimpleCriticalZeroCount χ T : ℝ) := by
  sorry

/-- A finite set of at least two reals in `[-T, T]` has two distinct points within
`2T / (card - 1)` of each other. -/
private theorem exists_close_pair_of_card (S : Finset ℝ) {T : ℝ} (hT : 0 < T)
    (hS : ∀ x ∈ S, |x| ≤ T) {m : ℕ} (hm : S.card = m + 2) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |x - y| ≤ 2 * T / (m + 1) := by
  set w : ℝ := 2 * T / (m + 1) with hw
  have hw0 : 0 < w := by positivity
  have hmw : (m + 1 : ℝ) * w = 2 * T := by rw [hw]; field_simp
  let bin : ℝ → ℕ := fun x ↦ min ⌊(x + T) / w⌋₊ m
  have hbin (x : ℝ) (hx : |x| ≤ T) : (bin x : ℝ) * w ≤ x + T ∧ x + T ≤ (bin x + 1) * w := by
    have hxT := abs_le.mp hx
    have hr0 : 0 ≤ (x + T) / w := div_nonneg (by linarith) hw0.le
    have hfl := Nat.floor_le hr0
    have hlt := Nat.lt_floor_add_one ((x + T) / w)
    rcases le_total ⌊(x + T) / w⌋₊ m with h | h
    · have hb : bin x = ⌊(x + T) / w⌋₊ := min_eq_left h
      rw [hb]
      constructor
      · calc (⌊(x + T) / w⌋₊ : ℝ) * w ≤ (x + T) / w * w := by gcongr
          _ = x + T := div_mul_cancel₀ _ hw0.ne'
      · calc x + T = (x + T) / w * w := (div_mul_cancel₀ _ hw0.ne').symm
          _ ≤ (⌊(x + T) / w⌋₊ + 1) * w := by gcongr
    · have hb : bin x = m := min_eq_right h
      rw [hb]
      have hmr : (m : ℝ) ≤ (x + T) / w := le_trans (by exact_mod_cast h) hfl
      constructor
      · calc (m : ℝ) * w ≤ (x + T) / w * w := by gcongr
          _ = x + T := div_mul_cancel₀ _ hw0.ne'
      · linarith
  have hmaps : Set.MapsTo bin S (Finset.range (m + 1)) := fun x _ ↦ by
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (min_le_right _ _)
  obtain ⟨x, hx, y, hy, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hm, Finset.card_range]; omega) hmaps
  refine ⟨x, hx, y, hy, hne, ?_⟩
  obtain ⟨h1, h2⟩ := hbin x (hS x hx)
  obtain ⟨h3, h4⟩ := hbin y (hS y hy)
  rw [heq] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

/-- Modulo a prime `p > 2` there is a primitive Dirichlet character. -/
private theorem exists_isPrimitive_of_prime {p : ℕ} [NeZero p] (hp : p.Prime) (h2 : 2 < p) :
    ∃ χ : DirichletCharacter ℂ p, χ.IsPrimitive := by
  have : Fact (2 < p) := ⟨h2⟩
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (ZMod.neg_one_ne_one (n := p))
  refine ⟨χ, ?_⟩
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply (isUnit_one.neg))
  have hc : χ.conductor ≠ 1 := fun h ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  rcases hp.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with h | h
  · exact absurd h hc
  · exact h

/-- A smooth non-negative weight, compactly supported in `ℝ⁺`, positive exactly on `(1, 4)`. -/
private theorem exists_weight : ∃ Ψ : ℝ → ℝ, (∀ x, 0 ≤ Ψ x) ∧ ContDiff ℝ ∞ Ψ ∧
    HasCompactSupport Ψ ∧ tsupport Ψ ⊆ Ioi 0 ∧ (∀ x, 1 < x → x < 4 → 0 < Ψ x) ∧
    (∀ x, 0 < Ψ x → 1 < x ∧ x < 4) := by
  let f : ContDiffBump (5 / 2 : ℝ) := ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩
  have hball (x : ℝ) : x ∈ Metric.ball (5 / 2 : ℝ) f.rOut ↔ 1 < x ∧ x < 4 := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change -(3 / 2 : ℝ) < x - 5 / 2 ∧ x - 5 / 2 < 3 / 2 ↔ _
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  refine ⟨f, fun x ↦ f.nonneg, f.contDiff (n := ⊤), f.hasCompactSupport, ?_,
    fun x h1 h4 ↦ f.pos_of_mem_ball ((hball x).mpr ⟨h1, h4⟩), fun x hx ↦ ?_⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    change -(3 / 2 : ℝ) ≤ x - 5 / 2 ∧ x - 5 / 2 ≤ 3 / 2 at hx
    exact show (0 : ℝ) < x by linarith [hx.1]
  · have : x ∈ Function.support f := hx.ne'
    rw [f.support_eq] at this
    exact (hball x).mp this

open scoped LSeries.notation in
/-- The family bound: a primitive character of modulus `q ∈ (Q, 4Q)` with `q ≥ 2` has
`N(T, χ) ≥ (⌊T/4⌋ (log (T/4)/2 - A) - 8 (log T/2 + log (4Q) + A)) / (2π)` for `T ≥ 16`, where
`A = 1 + 3K + B` collects the absolute constants of `dirichletStripZeroCount_lower`. -/
private theorem family_zero_count_lower {Q T : ℝ} (hT : 16 ≤ T) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (h4 : (q : ℝ) < 4 * Q) :
    let B := ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖
    let A := 1 + 3 * ((Real.log Real.pi + Real.log 4 + 1) / 2 + B) + B
    ((⌊T / 4⌋₊ : ℝ) * (Real.log (T / 4) / 2 - A) - 8 * (Real.log T / 2 + Real.log (4 * Q) + A)) /
        (2 * Real.pi) ≤ dirichletStripZeroCount χ T := by
  intro B A
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have h := hχ
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at h
    omega
  have hmain := DirichletZeroCount.dirichletStripZeroCount_lower χ hχ hχ1 (T := T / 2)
    (by linarith)
  simp only at hmain
  rw [show 2 * (T / 2) = T by ring, show T / 2 / 2 = T / 4 by ring] at hmain
  have hB0 : 0 ≤ B := tsum_nonneg fun _ ↦ norm_nonneg _
  have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ (Real.log Real.pi + Real.log 4 + 1) / 2 + B := by positivity
  have hq : Real.log q ≤ Real.log (4 * Q) :=
    Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) h4.le
  have hfl : (0 : ℝ) ≤ ⌊T / 4⌋₊ := Nat.cast_nonneg _
  rw [div_le_iff₀ (by positivity)]
  have e1 : (⌊T / 4⌋₊ : ℝ) * (Real.log (T / 4) / 2 - A) ≤
      (⌊T / 4⌋₊ : ℝ) * (Real.log (T / 4) / 2 - (2 * ((Real.log Real.pi + Real.log 4 + 1) / 2 + B) +
        Real.log 2 / 2)) := by
    apply mul_le_mul_of_nonneg_left _ hfl
    simp only [A]; linarith
  have e2 : 8 * (Real.log (T) / 2 + Real.log q + (1 / 2 + B + Real.log 2 / 2 +
      ((Real.log Real.pi + Real.log 4 + 1) / 2 + B))) ≤
      8 * (Real.log T / 2 + Real.log (4 * Q) + A) := by
    simp only [A]; linarith
  have e3 := mul_comm (dirichletStripZeroCount χ T : ℝ) (2 * Real.pi)
  linarith

/-- With `T = (log Q)^6`, the family bound times `14/25` exceeds `1 + 2T/δ` once `log Q` is
large. -/
private theorem eventually_many_zeros {A : ℝ} (hA : 0 ≤ A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ℓ₀ : ℝ, 2 ≤ ℓ₀ ∧ ∀ Q : ℝ, 0 < Q → ℓ₀ ≤ Real.log Q →
      2 * Real.log Q ^ 6 / δ < 14 / 25 * (((⌊Real.log Q ^ 6 / 4⌋₊ : ℝ) *
        (Real.log (Real.log Q ^ 6 / 4) / 2 - A) - 8 * (Real.log (Real.log Q ^ 6) / 2 +
          Real.log (4 * Q) + A)) / (2 * Real.pi)) - 1 := by
  set c₁ : ℝ := Real.log 4 / 2 + A
  set c₂ : ℝ := 8 * (4 + Real.log 4 + A)
  set L₀ : ℝ := (8 * ((2 / δ + 2) * (50 * Real.pi / 14) + c₂) + c₁) / 3
  refine ⟨max 2 (Real.exp L₀), le_max_left _ _, fun Q hQ hℓ ↦ ?_⟩
  set ℓ := Real.log Q
  have hℓ2 : 2 ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓL : L₀ ≤ Real.log ℓ :=
    (Real.le_log_iff_exp_le (by linarith)).mpr ((le_max_right _ _).trans hℓ)
  set T := ℓ ^ 6 with hT
  have hTℓ : ℓ ≤ T := by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hT64 : 64 ≤ T := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ ℓ ^ 6 := by gcongr
  have hlogT : Real.log T = 6 * Real.log ℓ := by rw [hT, Real.log_pow]; norm_num
  have hlogℓ : Real.log ℓ ≤ ℓ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hfloor : T / 8 ≤ (⌊T / 4⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (T / 4); linarith
  have hlog4 : Real.log (T / 4) = 6 * Real.log ℓ - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), hlogT]
  have hlogQ : Real.log (4 * Q) = Real.log 4 + ℓ := by
    rw [Real.log_mul (by norm_num) hQ.ne']
  have hc1 : 0 ≤ 3 * Real.log ℓ - c₁ := by
    have : 0 ≤ (2 / δ + 2) * (50 * Real.pi / 14) := by positivity
    have : 0 ≤ c₂ := by positivity
    have hL0 : 3 * L₀ = 8 * ((2 / δ + 2) * (50 * Real.pi / 14) + c₂) + c₁ := by
      simp only [L₀]; ring
    linarith
  have hmainT : T / 8 * (3 * Real.log ℓ - c₁) ≤
      (⌊T / 4⌋₊ : ℝ) * (Real.log (T / 4) / 2 - A) := by
    rw [hlog4]
    have : Real.log 4 / 2 + A = c₁ := rfl
    calc T / 8 * (3 * Real.log ℓ - c₁) ≤ (⌊T / 4⌋₊ : ℝ) * (3 * Real.log ℓ - c₁) :=
          mul_le_mul_of_nonneg_right hfloor hc1
      _ = _ := by rw [← this]; ring
  have herr : 8 * (Real.log T / 2 + Real.log (4 * Q) + A) ≤ T * c₂ := by
    rw [hlogT, hlogQ]
    have : 8 * (6 * Real.log ℓ / 2 + (Real.log 4 + ℓ) + A) ≤ 8 * (4 * ℓ + Real.log 4 + A) := by
      nlinarith
    have h2 : 8 * (4 * ℓ + Real.log 4 + A) ≤ T * c₂ := by
      simp only [c₂]; nlinarith
    linarith
  set Y : ℝ := (2 / δ + 2) * (50 * Real.pi / 14)
  have hL : Y ≤ (3 * Real.log ℓ - c₁) / 8 - c₂ := by
    simp only [L₀] at hℓL; simp only [Y]; linarith
  set X := (⌊T / 4⌋₊ : ℝ) * (Real.log (T / 4) / 2 - A) -
    8 * (Real.log T / 2 + Real.log (4 * Q) + A)
  have hX : T * Y ≤ X := by
    have h1 : T * Y ≤ T * ((3 * Real.log ℓ - c₁) / 8 - c₂) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    simp only [X]
    nlinarith
  have hmono : 14 / 25 * (T * Y / (2 * Real.pi)) ≤ 14 / 25 * (X / (2 * Real.pi)) := by
    gcongr
  have hval : 14 / 25 * (T * Y / (2 * Real.pi)) = T * (2 / δ + 2) := by
    simp only [Y]; field_simp; ring
  have h2T : 2 * T / δ = T * (2 / δ) := by ring
  rw [h2T]
  linarith

open scoped Classical in
/-- The weighted average of (1.5): if every character of the family with positive weight has
`(14/25) N(T, χ) ≥ K`, and the family has a primitive character of positive weight, then some
primitive character has `N₀'(T, χ) ≥ K`. -/
private theorem exists_many_simple_zeros (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (M : ℕ) (T K : ℝ)
    (hcis : 14 / 25 * ∑ n ∈ Finset.range M, w n *
        ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
          (dirichletStripZeroCount χ T : ℝ) ≤
      ∑ n ∈ Finset.range M, w n *
        ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
          (dirichletSimpleCriticalZeroCount χ T : ℝ))
    (hfam : ∀ n (χ : DirichletCharacter ℂ (n + 1)), χ.IsPrimitive → 0 < w n →
      K ≤ 14 / 25 * (dirichletStripZeroCount χ T : ℝ))
    {n₀ : ℕ} (hn₀ : n₀ < M) (hw₀ : 0 < w n₀) {χ₀ : DirichletCharacter ℂ (n₀ + 1)}
    (hχ₀ : χ₀.IsPrimitive) :
    ∃ n, ∃ χ : DirichletCharacter ℂ (n + 1), χ.IsPrimitive ∧
      K ≤ dirichletSimpleCriticalZeroCount χ T := by
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  have hlt : ∑ n ∈ Finset.range M, w n *
        ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
          (dirichletSimpleCriticalZeroCount χ T : ℝ) <
      ∑ n ∈ Finset.range M, w n *
        ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
          (14 / 25 * (dirichletStripZeroCount χ T : ℝ)) := by
    apply Finset.sum_lt_sum
    · intro n _
      rcases (hw n).eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ (hw n)
        apply Finset.sum_le_sum
        intro χ hχ
        have hχ' := (Finset.mem_filter.mp hχ).2
        exact ((hno n χ hχ').trans_le (hfam n χ hχ' hpos)).le
    · refine ⟨n₀, Finset.mem_range.mpr hn₀, mul_lt_mul_of_pos_left ?_ hw₀⟩
      apply Finset.sum_lt_sum
      · intro χ hχ
        have hχ' := (Finset.mem_filter.mp hχ).2
        exact ((hno n₀ χ hχ').trans_le (hfam n₀ χ hχ' hw₀)).le
      · exact ⟨χ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχ₀⟩,
          (hno n₀ χ₀ hχ₀).trans_le (hfam n₀ χ₀ hχ₀ hw₀)⟩
  have hrw : ∑ n ∈ Finset.range M, w n *
        ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
          (14 / 25 * (dirichletStripZeroCount χ T : ℝ)) =
      14 / 25 * ∑ n ∈ Finset.range M, w n *
        ∑ χ : DirichletCharacter ℂ (n + 1) with χ.IsPrimitive,
          (dirichletStripZeroCount χ T : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [← Finset.mul_sum]
    ring
  rw [hrw] at hlt
  exact (hcis.trans_lt hlt).false

/-- At least `K > 1` simple critical-line zeros with `|γ| ≤ T` include two whose ordinates
differ by at most `2T / (K - 1)`. -/
private theorem exists_close_zeros_of_count {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {T K : ℝ} (hT : 0 < T) (hK : 1 < K) (hKN : K ≤ dirichletSimpleCriticalZeroCount χ T) :
    ∃ t u : ℝ, t ≠ u ∧ |t - u| ≤ 2 * T / (K - 1) ∧
      χ.LFunction ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 ∧
      χ.LFunction ((1 / 2 : ℂ) + (u : ℂ) * Complex.I) = 0 := by
  set Z : Set ℝ := {γ : ℝ | |γ| ≤ T ∧ analyticOrderAt χ.LFunction ((1 / 2 : ℂ) + γ * I) = 1}
  have hZK : K ≤ Z.ncard := hKN
  have hcard : 2 ≤ Z.ncard := by
    have : 1 < Z.ncard := by exact_mod_cast hK.trans_le hZK
    omega
  have hfin : Z.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨m, hm⟩ : ∃ m, hfin.toFinset.card = m + 2 :=
    ⟨Z.ncard - 2, by rw [← Set.ncard_eq_toFinset_card Z hfin]; omega⟩
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := exists_close_pair_of_card hfin.toFinset hT
    (fun x hx ↦ ((Set.Finite.mem_toFinset hfin).mp hx).1) hm
  have hzero (γ : ℝ) (hγ : γ ∈ hfin.toFinset) :
      χ.LFunction ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
    have h1 := ((Set.Finite.mem_toFinset hfin).mp hγ).2
    exact (analyticOrderAt_ne_zero.mp (by rw [h1]; exact one_ne_zero)).2
  refine ⟨x, y, hne, hxy.trans ?_, hzero x hx, hzero y hy⟩
  have hmK : K ≤ (m + 2 : ℝ) := by
    have : (Z.ncard : ℝ) = m + 2 := by
      rw [Set.ncard_eq_toFinset_card Z hfin, hm]; push_cast; ring
    rw [← this]; exact hZK
  apply div_le_div_of_nonneg_left (by positivity) (by linarith)
  linarith

/-- **Arbitrarily close critical-line zeros of primitive Dirichlet L-functions.** For every
`δ > 0` some primitive Dirichlet character has two distinct zeros on the critical line whose
ordinates differ by less than `δ`; the character depends on `δ`.

The statement is, word for word, the proposition `PrimitiveDirichletLCloseCriticalZeros` of
PR #7538, from which that PR refutes the uniform constant after (10.3.1.18), p. 451
(`ERRATA.md`, F214). It is proved here from the classical input
`conreyIwaniecSoundararajan_simpleCriticalZeros` (arXiv:1105.1177, Theorem 1) and the proved
lower bound `DirichletZeroCount.dirichletStripZeroCount_lower` for the zero count, in place of
Selberg's theorem (`spectralLineJet_rational_critical_zero_count`, issue #6742). -/
theorem primitiveDirichletL_closeCriticalZeros :
    ∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.IsPrimitive ∧
      ∃ t u : ℝ, t ≠ u ∧ |t - u| < δ ∧
        χ.LFunction ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 ∧
        χ.LFunction ((1 / 2 : ℂ) + (u : ℂ) * Complex.I) = 0 := by
  classical
  intro δ hδ
  set B : ℝ := ∑' n, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖
  set A : ℝ := 1 + 3 * ((Real.log Real.pi + Real.log 4 + 1) / 2 + B) + B with hAdef
  have hA : 0 ≤ A := by
    have hB0 : 0 ≤ B := tsum_nonneg fun _ ↦ norm_nonneg _
    have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
    have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  obtain ⟨Ψ, hΨnn, hΨsmooth, hΨsupp, hΨtsupp, hΨpos, hΨwin⟩ := exists_weight
  obtain ⟨Q₀, hQ₀⟩ := conreyIwaniecSoundararajan_simpleCriticalZeros Ψ hΨnn hΨsmooth hΨsupp
    hΨtsupp 6 le_rfl
  obtain ⟨ℓ₀, hℓ₀2, hbig⟩ := eventually_many_zeros hA δ hδ
  -- the scale
  set Q : ℝ := max (max Q₀ 3) (Real.exp ℓ₀) with hQ
  have hQ₀Q : Q₀ ≤ Q := le_trans (le_max_left _ _) (le_max_left _ _)
  have hQ3 : 3 ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
  have hQpos : 0 < Q := by linarith
  have hℓ : ℓ₀ ≤ Real.log Q := (Real.le_log_iff_exp_le hQpos).mpr (le_max_right _ _)
  set T : ℝ := Real.log Q ^ 6 with hT
  have hT64 : 64 ≤ T := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ Real.log Q ^ 6 := by gcongr; linarith
  have hT0 : 0 < T := by linarith
  set K : ℝ := 14 / 25 * (((⌊T / 4⌋₊ : ℝ) * (Real.log (T / 4) / 2 - A) -
    8 * (Real.log T / 2 + Real.log (4 * Q) + A)) / (2 * Real.pi)) with hK
  have hKbig : 2 * T / δ < K - 1 := hbig Q hQpos hℓ
  have hK1 : 1 < K := by
    have : 0 < 2 * T / δ := by positivity
    linarith
  -- the truncation of the sum over moduli
  set M : ℕ := ⌈4 * Q⌉₊ with hM
  have hMvanish : ∀ n : ℕ, M ≤ n → Ψ ((n + 1 : ℕ) / Q) = 0 := by
    intro n hn
    by_contra hne
    have h4 := (hΨwin _ (lt_of_le_of_ne (hΨnn _) (Ne.symm hne))).2
    have hn' : 4 * Q ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    rw [div_lt_iff₀ hQpos] at h4
    push_cast at h4
    linarith
  have hcis := hQ₀ Q hQ₀Q T le_rfl
    (by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]) M hMvanish
  -- every character of positive weight has many zeros
  have hfam : ∀ n (χ : DirichletCharacter ℂ (n + 1)), χ.IsPrimitive →
      0 < Ψ ((n + 1 : ℕ) / Q) / (n + 1).totient →
      K ≤ 14 / 25 * (dirichletStripZeroCount χ T : ℝ) := by
    intro n χ hχ hpos
    have hΨ : 0 < Ψ ((n + 1 : ℕ) / Q) := by
      by_contra h
      have h0 : Ψ ((n + 1 : ℕ) / Q) = 0 := le_antisymm (not_lt.mp h) (hΨnn _)
      rw [h0, zero_div] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨h1, h4⟩ := hΨwin _ hΨ
    rw [lt_div_iff₀ hQpos, one_mul] at h1
    rw [div_lt_iff₀ hQpos] at h4
    have hq2 : 2 ≤ n + 1 := by
      have : (2 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
      exact_mod_cast this.le
    have := family_zero_count_lower (T := T) (Q := Q) (by linarith) χ hχ hq2 h4
    simp only at this
    rw [hK]
    linarith
  -- a prime of the family, and a primitive character modulo it
  obtain ⟨p, hp, hQp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈Q⌉₊
    (Nat.ceil_pos.mpr hQpos).ne'
  obtain ⟨n₀, rfl⟩ : ∃ n₀, p = n₀ + 1 := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  have hQn₀ : Q < ((n₀ + 1 : ℕ) : ℝ) := lt_of_le_of_lt (Nat.le_ceil Q) (by exact_mod_cast hQp)
  have hn₀4 : ((n₀ + 1 : ℕ) : ℝ) < 4 * Q := by
    have : ((n₀ + 1 : ℕ) : ℝ) ≤ 2 * ⌈Q⌉₊ := by exact_mod_cast hp2
    linarith [Nat.ceil_lt_add_one hQpos.le]
  have hp2' : 2 < n₀ + 1 := by
    have : (2 : ℝ) < ((n₀ + 1 : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨χ₀, hχ₀⟩ := exists_isPrimitive_of_prime hp hp2'
  have hn₀M : n₀ < M := by
    have h : 4 * Q ≤ (M : ℝ) := Nat.le_ceil _
    have : ((n₀ : ℕ) : ℝ) < M := by push_cast at hn₀4; linarith
    exact_mod_cast this
  have hw₀ : 0 < Ψ ((n₀ + 1 : ℕ) / Q) / (n₀ + 1).totient := by
    have htot : (0 : ℝ) < (n₀ + 1).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos n₀)
    refine div_pos (hΨpos _ ?_ ?_) htot
    · rw [lt_div_iff₀ hQpos, one_mul]; exact hQn₀
    · rw [div_lt_iff₀ hQpos]; exact hn₀4
  -- one character with many simple zeros, and two close ones among them
  obtain ⟨n, χ, hχ, hKN⟩ := exists_many_simple_zeros
    (fun n ↦ Ψ ((n + 1 : ℕ) / Q) / (n + 1).totient)
    (fun n ↦ div_nonneg (hΨnn _) (Nat.cast_nonneg _)) M T K hcis hfam hn₀M hw₀ hχ₀
  obtain ⟨t, u, hne, htu, ht, hu⟩ := exists_close_zeros_of_count χ hT0 hK1 hKN
  refine ⟨n + 1, inferInstance, χ, hχ, t, u, hne, htu.trans_lt ?_, ht, hu⟩
  rw [div_lt_iff₀ (by linarith)]
  rw [div_lt_iff₀ hδ] at hKbig
  linarith

end RiemannMasullo
