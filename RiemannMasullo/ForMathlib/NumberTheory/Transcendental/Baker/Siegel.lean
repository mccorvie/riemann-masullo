module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.IntPoly
import Mathlib.NumberTheory.SiegelsLemma

/-! # Siegel lemma, over the integers and for algebraic coefficients

Ported from HOL Light, Baker/siegel.ml (jrh13/hol-light, commit 1a0c0e6). -/

@[expose] public section

namespace RiemannMasullo.Baker

section SiegelInt

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The case `0 < M < N` of the Siegel lemma, from Mathlib's
`Int.Matrix.exists_ne_zero_int_vec_norm_le`. -/
private theorem siegel_aux_main {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ) (U : ℝ)
    (B : ℕ) (hU : 1 ≤ U) (hA : ∀ i j, |(A i j : ℝ)| ≤ U)
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α)
    (hB : ((Fintype.card β : ℝ) * U) ^ Fintype.card α <
      ((B : ℝ) + 1) ^ (Fintype.card β - Fintype.card α)) :
    ∃ t : β → ℤ, t ≠ 0 ∧ A.mulVec t = 0 ∧ ∀ j, |(t j : ℝ)| ≤ B := by
  obtain ⟨t, ht0, hAt, hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hn hm
  refine ⟨t, ht0, hAt, fun j => ?_⟩
  set N := Fintype.card β
  set M := Fintype.card α
  have hNM : (0 : ℝ) < (N : ℝ) - M := by
    have : (M : ℝ) < N := by exact_mod_cast hn
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hX : (0 : ℝ) ≤ (N : ℝ) * U := by nlinarith
  have hnA : ‖A‖ ≤ U := by
    rw [Matrix.norm_le_iff (zero_le_one.trans hU)]
    intro i j
    rw [Int.norm_eq_abs]
    exact hA i j
  have h1 : ‖t‖ ≤ ((N : ℝ) * U) ^ ((M : ℝ) / ((N : ℝ) - M)) :=
    hnorm.trans (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left (max_le hU hnA) (by positivity)) (by positivity))
  have h2 : ((N : ℝ) * U) ^ ((M : ℝ) / ((N : ℝ) - M)) < (B : ℝ) + 1 := by
    have h3 := Real.rpow_lt_rpow (pow_nonneg hX M) hB (one_div_pos.mpr hNM)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), Nat.cast_sub hn.le, mul_one_div_cancel hNM.ne',
      Real.rpow_one, mul_one_div] at h3
    exact h3
  have h4 : |(t j : ℝ)| < (B : ℝ) + 1 := by
    have := norm_le_pi_norm t j
    rw [Int.norm_eq_abs] at this
    linarith
  have h5 : |t j| < (B : ℤ) + 1 := by exact_mod_cast h4
  have h6 : |t j| ≤ (B : ℤ) := by omega
  exact_mod_cast h6

end SiegelInt

/-- HOL Light: Baker/siegel.ml, SIEGEL_LEMMA. Siegel's lemma: `M` integer linear equations in `N`
unknowns with coefficients bounded by `U` have a nonzero integer solution bounded by `B` as soon
as `(N U) ^ M < (B + 1) ^ (N - M)`.

Deviation: the coefficients `u i j` and the solution `x j` are integers (HOL: reals with
`integer`), and the equations `∑ j ∈ unk, u i j * x j = 0` are stated in `ℤ`; HOL's
`!i j. i IN eqs /\ j IN unk ==> ...` is curried as `∀ i ∈ eqs, ∀ j ∈ unk, ...`. Proved from Mathlib's
`Int.Matrix.exists_ne_zero_int_vec_norm_le`, not by HOL's direct pigeonhole argument. -/
theorem siegel_lemma {E J : Type*} (u : E → J → ℤ) (eqs : Finset E) (unk : Finset J) (U : ℝ)
    (B : ℕ) (hunk : unk ≠ ∅) (hU : 1 ≤ U)
    (hu : ∀ i ∈ eqs, ∀ j ∈ unk, |(u i j : ℝ)| ≤ U)
    (hB : ((unk.card : ℝ) * U) ^ eqs.card < ((B : ℝ) + 1) ^ (unk.card - eqs.card)) :
    ∃ x : J → ℤ, (∀ j ∈ unk, |(x j : ℝ)| ≤ B) ∧ ¬ (∀ j ∈ unk, x j = 0) ∧
      ∀ i ∈ eqs, ∑ j ∈ unk, u i j * x j = 0 := by
  classical
  obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.mpr hunk
  have hN : 1 ≤ unk.card := Finset.card_pos.mpr ⟨j0, hj0⟩
  have hX : (1 : ℝ) ≤ (unk.card : ℝ) * U := by
    have : (1 : ℝ) ≤ unk.card := by exact_mod_cast hN
    nlinarith
  rcases Nat.lt_or_ge eqs.card unk.card with hlt | hge
  · rcases Nat.eq_zero_or_pos eqs.card with h0 | hpos
    · -- no equations
      have hB1 : 1 ≤ B := by
        by_contra hB0
        have : B = 0 := by omega
        rw [this, h0] at hB
        simp at hB
      refine ⟨fun _ => 1, fun j _ => by simpa using (by exact_mod_cast hB1 : (1 : ℝ) ≤ B),
        fun h => one_ne_zero (h j0 hj0), fun i hi => ?_⟩
      rw [Finset.card_eq_zero.mp h0] at hi
      simp at hi
    · obtain ⟨t, ht0, hAt, htB⟩ := siegel_aux_main (fun (i : eqs) (j : unk) => u i j) U B hU
        (fun i j => hu i i.2 j j.2) (by simpa using hlt) (by simpa using hpos)
        (by simpa using hB)
      refine ⟨fun j => if hj : j ∈ unk then t ⟨j, hj⟩ else 0, fun j hj => ?_, fun h => ?_,
        fun i hi => ?_⟩
      · simpa [hj] using htB ⟨j, hj⟩
      · refine ht0 (funext fun j => ?_)
        simpa [j.2] using h j j.2
      · have := congrFun hAt ⟨i, hi⟩
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
        rw [← this, ← Finset.sum_coe_sort unk]
        exact Finset.sum_congr rfl fun j _ => by simp [j.2]
  · exfalso
    rw [Nat.sub_eq_zero_of_le hge, pow_zero] at hB
    exact absurd hB (not_lt.mpr (one_le_pow₀ hX))

/-- HOL Light: Baker/siegel.ml, SIEGEL_LEMMA_HALF. Siegel's lemma with `N ≥ 2 M`: there is a
nonzero integer solution bounded by `N U`.

Deviation: integer coefficients and solution, equations stated in `ℤ`, as in `siegel_lemma`. -/
theorem siegel_lemma_half {E J : Type*} (u : E → J → ℤ) (eqs : Finset E) (unk : Finset J)
    (U : ℝ) (hunk : unk ≠ ∅) (hU : 1 ≤ U)
    (hu : ∀ i ∈ eqs, ∀ j ∈ unk, |(u i j : ℝ)| ≤ U)
    (hcard : 2 * eqs.card ≤ unk.card) :
    ∃ x : J → ℤ, (∀ j ∈ unk, |(x j : ℝ)| ≤ (unk.card : ℝ) * U) ∧ ¬ (∀ j ∈ unk, x j = 0) ∧
      ∀ i ∈ eqs, ∑ j ∈ unk, u i j * x j = 0 := by
  have hN : 1 ≤ unk.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hunk)
  have hX : (1 : ℝ) ≤ (unk.card : ℝ) * U := by
    have : (1 : ℝ) ≤ unk.card := by exact_mod_cast hN
    nlinarith
  have hX0 : (0 : ℝ) ≤ (unk.card : ℝ) * U := zero_le_one.trans hX
  obtain ⟨x, hx1, hx2, hx3⟩ := siegel_lemma u eqs unk U ⌊(unk.card : ℝ) * U⌋₊ hunk hU hu
    (lt_of_le_of_lt (pow_le_pow_right₀ hX (by omega))
      (pow_lt_pow_left₀ (Nat.lt_floor_add_one _) hX0 (by omega)))
  exact ⟨x, fun j hj => (hx1 j hj).trans (Nat.floor_le hX0), hx2, hx3⟩

/-- HOL Light: Baker/siegel.ml, POWER_REDUCTION. Reduction of powers: `(a_d theta) ^ e` is an
integer combination of the powers `theta ^ s`, `s < d`, with coefficients bounded by
`(2 h) ^ e`.

Deviation: integer coefficients `a j`, `K s` (HOL: reals with `integer`). -/
theorem power_reduction (a : ℕ → ℤ) (d : ℕ) (h : ℝ) (theta : ℂ) (hd : 1 ≤ d)
    (hah : ∀ j, |(a j : ℝ)| ≤ h) (had : a d ≠ 0)
    (hroot : ∑ j ∈ Finset.range (d + 1), (a j : ℂ) * theta ^ j = 0) (e : ℕ) :
    ∃ K : ℕ → ℤ, (∀ s, |(K s : ℝ)| ≤ (2 * h) ^ e) ∧
      ((a d : ℂ) * theta) ^ e = ∑ s ∈ Finset.range (d - 1 + 1), (K s : ℂ) * theta ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hh : 0 ≤ h := (abs_nonneg _).trans (hah 0)
  have hroot' : (a (m + 1) : ℂ) * theta ^ (m + 1) =
      -∑ j ∈ Finset.range (m + 1), (a j : ℂ) * theta ^ j := by
    rw [Finset.sum_range_succ] at hroot
    linear_combination hroot
  induction e with
  | zero =>
    refine ⟨fun s => if s = 0 then 1 else 0, fun s => ?_, ?_⟩
    · by_cases hs : s = 0 <;> simp [hs]
    · rw [Finset.sum_range_succ']
      simp
  | succ e ih =>
    obtain ⟨K, hK1, hK2⟩ := ih
    refine ⟨fun s => (if s = 0 then 0 else a (m + 1) * K (s - 1)) - K m * a s, fun s => ?_, ?_⟩
    · have hp : (0 : ℝ) ≤ (2 * h) ^ e := pow_nonneg (by linarith) _
      have h1 : |((if s = 0 then 0 else a (m + 1) * K (s - 1) : ℤ) : ℝ)| ≤ h * (2 * h) ^ e := by
        by_cases hs : s = 0
        · simpa [hs] using mul_nonneg hh hp
        · simp only [hs, ↓reduceIte, Int.cast_mul, abs_mul]
          exact mul_le_mul (hah _) (hK1 _) (abs_nonneg _) hh
      have h2 : |((K m * a s : ℤ) : ℝ)| ≤ (2 * h) ^ e * h := by
        rw [Int.cast_mul, abs_mul]
        exact mul_le_mul (hK1 _) (hah _) (abs_nonneg _) hp
      rw [Int.cast_sub, pow_succ]
      calc |((if s = 0 then 0 else a (m + 1) * K (s - 1) : ℤ) : ℝ) - ((K m * a s : ℤ) : ℝ)|
          ≤ |((if s = 0 then 0 else a (m + 1) * K (s - 1) : ℤ) : ℝ)| + |((K m * a s : ℤ) : ℝ)| :=
            abs_sub _ _
        _ ≤ h * (2 * h) ^ e + (2 * h) ^ e * h := add_le_add h1 h2
        _ = (2 * h) ^ e * (2 * h) := by ring
    · have e1 : ∑ s ∈ Finset.range (m + 1),
          (((if s = 0 then 0 else a (m + 1) * K (s - 1)) - K m * a s : ℤ) : ℂ) * theta ^ s =
          (a (m + 1) : ℂ) * ∑ s ∈ Finset.range m, (K s : ℂ) * theta ^ (s + 1) -
            (K m : ℂ) * ∑ j ∈ Finset.range (m + 1), (a j : ℂ) * theta ^ j := by
        simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
        congr 1
        · rw [Finset.sum_range_succ', Finset.mul_sum]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
            Int.cast_zero, zero_mul, add_zero]
          exact Finset.sum_congr rfl fun s _ => by push_cast; ring
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by push_cast; ring
      have e2 : theta * ∑ s ∈ Finset.range m, (K s : ℂ) * theta ^ s =
          ∑ s ∈ Finset.range m, (K s : ℂ) * theta ^ (s + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e1, pow_succ, hK2, Finset.sum_range_succ, ← e2]
      linear_combination (K m : ℂ) * hroot'

/-- HOL Light: Baker/siegel.ml, INTPOLY_REDUCE. An `intpoly` in roots `theta r` of integer
polynomials, multiplied by `∏ (leading coefficient) ^ n r`, is an integer combination of the
monomials `∏ theta r ^ s r` with `s r < d r`.

Deviation: integer coefficients `a r j`, `K s`; the index set `cartesian_product v (\r. 0..d r - 1)`
is `cartesianProduct V fun r => Finset.range (d r - 1 + 1)` (see `mem_cartesianProduct`). -/
theorem intpoly_reduce {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (theta : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (h : ℕ → ℝ) (hg : intpoly V n b g)
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ (∀ j, |(a r j : ℝ)| ≤ h r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0) :
    ∃ K : (ℕ → ℕ) → ℤ,
      (∀ s, |(K s : ℝ)| ≤ b * ∏ r ∈ V, (2 * h r) ^ n r) ∧
      (∏ r ∈ V, (a r (d r) : ℂ) ^ n r) * g theta =
        ∑ s ∈ cartesianProduct V fun r => Finset.range (d r - 1 + 1),
          (K s : ℂ) * ∏ r ∈ V, theta r ^ s r := by
  classical
  obtain ⟨s, c, e, he, hc, hgx⟩ := hg
  have hex : ∀ r e', ∃ K : ℕ → ℤ, r ∈ V → (∀ s, |(K s : ℝ)| ≤ (2 * h r) ^ e') ∧
      ((a r (d r) : ℂ) * theta r) ^ e' =
        ∑ s ∈ Finset.range (d r - 1 + 1), (K s : ℂ) * theta r ^ s := by
    intro r e'
    by_cases hr : r ∈ V
    · obtain ⟨K, hK⟩ := power_reduction (a r) (d r) (h r) (theta r) (ha r hr).1 (ha r hr).2.1
        (ha r hr).2.2.1 (ha r hr).2.2.2 e'
      exact ⟨K, fun _ => hK⟩
    · exact ⟨fun _ => 0, fun h => absurd h hr⟩
  choose R hR using hex
  have hh : ∀ r ∈ V, 0 ≤ h r := fun r hr => (abs_nonneg _).trans ((ha r hr).2.1 0)
  refine ⟨fun sg => ∑ k ∈ s, c k * ∏ r ∈ V, (a r (d r) ^ (n r - e k r) * R r (e k r) (sg r)),
    fun sg => ?_, ?_⟩
  · have hP : 0 ≤ ∏ r ∈ V, (2 * h r) ^ n r :=
      Finset.prod_nonneg fun r hr => pow_nonneg (by linarith [hh r hr]) _
    calc |((∑ k ∈ s, c k * ∏ r ∈ V, (a r (d r) ^ (n r - e k r) * R r (e k r) (sg r)) : ℤ) : ℝ)|
        ≤ ∑ k ∈ s, |(c k : ℝ)| * ∏ r ∈ V, (2 * h r) ^ n r := by
          rw [Int.cast_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          rw [Int.cast_mul, abs_mul, Int.cast_prod, Finset.abs_prod]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine Finset.prod_le_prod₀ (fun r _ => abs_nonneg _) fun r hr => ?_
          have h2 : (2 * h r) ^ n r = (2 * h r) ^ (n r - e k r) * (2 * h r) ^ e k r := by
            rw [← pow_add, Nat.sub_add_cancel (he k hk r hr)]
          rw [h2, Int.cast_mul, abs_mul, Int.cast_pow, abs_pow]
          exact mul_le_mul
            (pow_le_pow_left₀ (abs_nonneg _) (((ha r hr).2.1 _).trans (by linarith [hh r hr])) _)
            ((hR r (e k r) hr).1 _) (abs_nonneg _) (pow_nonneg (by linarith [hh r hr]) _)
      _ = (∑ k ∈ s, |(c k : ℝ)|) * ∏ r ∈ V, (2 * h r) ^ n r := by rw [Finset.sum_mul]
      _ ≤ b * ∏ r ∈ V, (2 * h r) ^ n r := mul_le_mul_of_nonneg_right hc hP
  · rw [hgx, Finset.mul_sum]
    simp only [Int.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have key := vsum_cproduct_cartesian_product V (fun r => Finset.range (d r - 1 + 1))
      (fun r i => ((a r (d r) : ℂ) ^ (n r - e k r) * (R r (e k r) i : ℂ)) * theta r ^ i)
    have hrhs : ∑ sg ∈ cartesianProduct V fun r => Finset.range (d r - 1 + 1),
        ((c k * ∏ r ∈ V, (a r (d r) ^ (n r - e k r) * R r (e k r) (sg r)) : ℤ) : ℂ) *
          ∏ r ∈ V, theta r ^ sg r =
        (c k : ℂ) * ∑ sg ∈ cartesianProduct V fun r => Finset.range (d r - 1 + 1),
          ∏ r ∈ V, ((a r (d r) : ℂ) ^ (n r - e k r) * (R r (e k r) (sg r) : ℂ)) *
            theta r ^ sg r := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun sg _ => ?_
      rw [Int.cast_mul, Int.cast_prod, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_congr rfl fun r _ => by push_cast; ring
    rw [hrhs, key, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    have h1 : ∑ i ∈ Finset.range (d r - 1 + 1),
        ((a r (d r) : ℂ) ^ (n r - e k r) * (R r (e k r) i : ℂ)) * theta r ^ i =
        (a r (d r) : ℂ) ^ (n r - e k r) * ((a r (d r) : ℂ) * theta r) ^ e k r := by
      rw [(hR r (e k r) hr).2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (he k hk r hr)]

/-- HOL Light: Baker/siegel.ml, ALGEBRAIC_SIEGEL. Siegel's lemma for linear equations whose
coefficients are `intpoly`s in algebraic numbers `theta r`, each a root of an integer polynomial
`∑ j ≤ d r, a r j * X ^ j` of degree `d r ≥ 1` with coefficients bounded by `h r`.

Deviation: integer coefficients `a r j` and solution `x j` (HOL: reals with `integer`); the
hypothesis on `g` is curried as `∀ i ∈ eqs, ∀ j ∈ unk, ...`. -/
theorem algebraic_siegel {E J : Type*} {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ}
    (g : E → J → (ℕ → ℂ) → ℂ) (eqs : Finset E) (unk : Finset J)
    (theta : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (h : ℕ → ℝ)
    (hunk : unk ≠ ∅)
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ (∀ j, |(a r j : ℝ)| ≤ h r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hg : ∀ i ∈ eqs, ∀ j ∈ unk, intpoly V n b (g i j))
    (hcard : 2 * ((∏ r ∈ V, d r) * eqs.card) ≤ unk.card) :
    ∃ x : J → ℤ,
      (∀ j ∈ unk, |(x j : ℝ)| ≤
        (unk.card : ℝ) * max 1 (b * ∏ r ∈ V, (2 * h r) ^ n r)) ∧
      ¬ (∀ j ∈ unk, x j = 0) ∧
      ∀ i ∈ eqs, ∑ j ∈ unk, (x j : ℂ) * g i j theta = 0 := by
  classical
  have hex : ∀ i j, ∃ K : (ℕ → ℕ) → ℤ, i ∈ eqs → j ∈ unk →
      (∀ s, |(K s : ℝ)| ≤ b * ∏ r ∈ V, (2 * h r) ^ n r) ∧
      (∏ r ∈ V, (a r (d r) : ℂ) ^ n r) * g i j theta =
        ∑ s ∈ cartesianProduct V fun r => Finset.range (d r - 1 + 1),
          (K s : ℂ) * ∏ r ∈ V, theta r ^ s r := by
    intro i j
    by_cases hij : i ∈ eqs ∧ j ∈ unk
    · obtain ⟨K, hK⟩ := intpoly_reduce theta a d h (hg i hij.1 j hij.2) ha
      exact ⟨K, fun _ _ => hK⟩
    · exact ⟨fun _ => 0, fun hi hj => absurd ⟨hi, hj⟩ hij⟩
  choose K hK using hex
  set box := cartesianProduct V fun r => Finset.range (d r - 1 + 1) with hbox
  have hboxcard : box.card = ∏ r ∈ V, d r := by
    rw [hbox, card_cartesian_product]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Finset.card_range, Nat.sub_add_cancel (ha r hr).1]
  obtain ⟨x, hx1, hx2, hx3⟩ := siegel_lemma_half
    (fun (p : E × (ℕ → ℕ)) (j : J) => K p.1 j p.2) (eqs ×ˢ box) unk
    (max 1 (b * ∏ r ∈ V, (2 * h r) ^ n r)) hunk (le_max_left _ _)
    (fun p hp j hj => le_max_of_le_right ((hK p.1 j (Finset.mem_product.mp hp).1 hj).1 p.2))
    (by rw [Finset.card_product, hboxcard, mul_comm eqs.card]; exact hcard)
  refine ⟨x, hx1, hx2, fun i hi => ?_⟩
  have hA : (∏ r ∈ V, (a r (d r) : ℂ) ^ n r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r hr =>
      pow_ne_zero _ (Int.cast_ne_zero.mpr (ha r hr).2.2.1)
  refine (mul_eq_zero.mp ?_).resolve_left hA
  rw [Finset.mul_sum]
  calc ∑ j ∈ unk, (∏ r ∈ V, (a r (d r) : ℂ) ^ n r) * ((x j : ℂ) * g i j theta)
      = ∑ j ∈ unk, ∑ s ∈ box, (x j : ℂ) * ((K i j s : ℂ) * ∏ r ∈ V, theta r ^ s r) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [mul_left_comm, (hK i j hi hj).2, Finset.mul_sum]
    _ = ∑ s ∈ box, ((∑ j ∈ unk, K i j s * x j : ℤ) : ℂ) * ∏ r ∈ V, theta r ^ s r := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Int.cast_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        rw [hx3 (i, s) (Finset.mem_product.mpr ⟨hi, hs⟩)]
        simp

end RiemannMasullo.Baker
