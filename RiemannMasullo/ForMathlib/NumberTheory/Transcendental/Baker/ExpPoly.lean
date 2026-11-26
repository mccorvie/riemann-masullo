module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Uniqueness of exponential polynomials; polynomials of distinct degrees

Ported from HOL Light, Baker/expoly.ml (jrh13/hol-light, commit 1a0c0e6), together with the generic
lemmas `COMPLEX_POLYFUN_SHIFT` and `COMPLEX_POLYFUN_TRUNCATE` of Baker/lemmas.ml.

If `∑ i, P i l * w i ^ l = 0` for all `l < ∑ i, (deg (P i) + 1)`, with pairwise distinct nonzero
nodes `w i`, then all `P i` vanish (this replaces the determinant Lemma 3 of Baker, *Transcendental
Number Theory*, Ch. 3). Also the shift `x ↦ x + 1` of polynomials and the linear independence of
polynomials of pairwise distinct exact degrees (which replaces Baker's Lemma 2). -/

@[expose] public section

namespace RiemannMasullo.Baker

open Finset Polynomial

/-- HOL Light: Baker/lemmas.ml, COMPLEX_POLYFUN_TRUNCATE. A polynomial function whose coefficients
are cut off above `n` is the polynomial function of degree bound `n`. -/
theorem complex_polyfun_truncate (M n : ℕ) (c : ℕ → ℂ) (x : ℂ) (hnM : n ≤ M) :
    ∑ t ∈ Finset.range (M + 1), (if t ≤ n then c t else 0) * x ^ t =
      ∑ t ∈ Finset.range (n + 1), c t * x ^ t := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (M + 1) :=
    Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [ite_eq_left (by simpa [Nat.lt_succ_iff] using ht)]
  · intro t _ ht
    rw [ite_eq_right (by simpa [Nat.lt_succ_iff] using ht), zero_mul]

/-- HOL Light: Baker/lemmas.ml, COMPLEX_POLYFUN_SHIFT. The coefficients of the shifted polynomial
function `x ↦ ∑ k, c k * (x + β) ^ k`, by the binomial theorem. -/
theorem complex_polyfun_shift (m : ℕ) (c : ℕ → ℂ) (β x : ℂ) :
    ∑ k ∈ Finset.range (m + 1), c k * (x + β) ^ k =
      ∑ t ∈ Finset.range (m + 1),
        (∑ k ∈ Finset.range (m + 1), (Nat.choose k t : ℂ) * β ^ (k - t) * c k) * x ^ t := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hsub : Finset.range (k + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset_range.2 (by simpa using hk)
  rw [add_pow, Finset.mul_sum, ← Finset.sum_subset hsub]
  · exact Finset.sum_congr rfl fun t _ => by ring
  · intro t _ ht
    have : k < t := by simpa [Nat.lt_succ_iff] using ht
    simp [Nat.choose_eq_zero_of_lt this]

/-- HOL Light: Baker/expoly.ml, COMPLEX_POLYFUN_SHIFT1. The coefficients of the polynomial
function shifted by one. -/
theorem complex_polyfun_shift1 (M : ℕ) (c : ℕ → ℂ) (x : ℂ) :
    ∑ t ∈ Finset.range (M + 1), c t * (x + 1) ^ t =
      ∑ t ∈ Finset.range (M + 1),
        (∑ k ∈ Finset.range (M + 1), (Nat.choose k t : ℂ) * c k) * x ^ t := by
  simpa using complex_polyfun_shift M c 1 x

/-- The polynomial with coefficients `c 0, …, c d`. -/
private noncomputable def expolyPoly (d : ℕ) (c : ℕ → ℂ) : ℂ[X] :=
  ∑ t ∈ Finset.range (d + 1), C (c t) * X ^ t

private theorem expoly_eval (d : ℕ) (c : ℕ → ℂ) (x : ℂ) :
    (expolyPoly d c).eval x = ∑ t ∈ Finset.range (d + 1), c t * x ^ t := by
  simp [expolyPoly, eval_finsetSum]

private theorem expoly_coeff (d : ℕ) (c : ℕ → ℂ) (t : ℕ) :
    (expolyPoly d c).coeff t = if t ≤ d then c t else 0 := by
  simp [expolyPoly, coeff_C_mul, coeff_X_pow]

/-- Polynomial form of the core statement, by induction on the total number `N` of coefficients
via the difference operator `u l ↦ u (l + 1) - w a * u l`. -/
private theorem expoly_core {A : Type*} [DecidableEq A] :
    ∀ (N : ℕ) (s : Finset A) (w : A → ℂ) (e : A → ℕ) (P : A → ℂ[X]),
      ∑ i ∈ s, e i = N → (∀ i ∈ s, w i ≠ 0) → (∀ i ∈ s, ∀ j ∈ s, w i = w j → i = j) →
      (∀ i ∈ s, (P i).degree < (e i : WithBot ℕ)) →
      (∀ l : ℕ, l < N → ∑ i ∈ s, (P i).eval (l : ℂ) * w i ^ l = 0) → ∀ i ∈ s, P i = 0 := by
  intro N
  induction N with
  | zero =>
    intro s w e P hsum _ _ hdeg _ i hi
    have h0 : e i = 0 := (Finset.sum_eq_zero_iff.1 hsum) i hi
    have := hdeg i hi
    rw [h0] at this
    exact degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 this)
  | succ N ih =>
    intro s w e P hsum hw0 hinj hdeg hvan
    obtain ⟨a, ha, hea⟩ : ∃ a ∈ s, e a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at hsum
      omega
    have hcomp : ∀ Q : ℂ[X], Q ≠ 0 → (Q.comp (X + C 1)).degree = Q.degree ∧
        (Q.comp (X + C 1)).leadingCoeff = Q.leadingCoeff := by
      intro Q hQ
      have hlc : (Q.comp (X + C 1)).leadingCoeff = Q.leadingCoeff := by
        rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
          leadingCoeff_X_add_C, one_pow, mul_one]
      have hne : Q.comp (X + C 1) ≠ 0 := by
        rw [← leadingCoeff_ne_zero, hlc]
        exact leadingCoeff_ne_zero.2 hQ
      refine ⟨?_, hlc⟩
      rw [degree_eq_natDegree hne, degree_eq_natDegree hQ, natDegree_comp, natDegree_X_add_C,
        mul_one]
    have hcomple : ∀ Q : ℂ[X], (Q.comp (X + C 1)).degree ≤ Q.degree := by
      intro Q
      by_cases hQ : Q = 0
      · simp [hQ]
      · exact (hcomp Q hQ).1.le
    have hCmul : ∀ (z : ℂ) (Q : ℂ[X]), (C z * Q).degree ≤ Q.degree := by
      intro z Q
      by_cases hz : z = 0
      · simp [hz]
      · exact (degree_C_mul hz).le
    set P' : A → ℂ[X] := fun i => C (w i) * (P i).comp (X + C 1) - C (w a) * P i with hP'
    have hres := ih s w (Function.update e a (e a - 1)) P' ?_ hw0 hinj ?_ ?_
    · -- all the differenced parts vanish
      have hne : ∀ i ∈ s, i ≠ a → P i = 0 := by
        intro i hi hia
        by_contra hPi
        have h1 : C (w i) * (P i).comp (X + C 1) = C (w a) * P i := sub_eq_zero.1 (hres i hi)
        have h2 := congrArg leadingCoeff h1
        rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C,
          (hcomp _ hPi).2] at h2
        exact hia (hinj i hi a ha (mul_right_cancel₀ (leadingCoeff_ne_zero.2 hPi) h2))
      have hstep : ∀ x : ℂ, (P a).eval (x + 1) = (P a).eval x := by
        intro x
        have h1 := congrArg (eval x) (hres a ha)
        simp only [hP', eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_zero] at h1
        have h2 : w a * ((P a).eval (x + 1) - (P a).eval x) = 0 := by linear_combination h1
        exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (hw0 a ha))
      have h0 : (P a).eval 0 = 0 := by
        have h1 := hvan 0 (Nat.succ_pos N)
        rw [Finset.sum_eq_single a (fun i hi hia => by simp [hne i hi hia])
          (fun h => absurd ha h)] at h1
        simpa using h1
      have hnat : ∀ n : ℕ, (P a).eval (n : ℂ) = 0 := by
        intro n
        induction n with
        | zero => simpa using h0
        | succ n ihn => rw [Nat.cast_succ, hstep, ihn]
      have hPa : P a = 0 := by
        apply eq_of_infinite_eval_eq
        refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono ?_
        rintro _ ⟨n, rfl⟩
        simp [hnat n]
      intro i hi
      by_cases hia : i = a
      · rw [hia, hPa]
      · exact hne i hi hia
    · rw [Finset.sum_update_of_mem ha, Finset.sdiff_singleton_eq_erase]
      have := Finset.add_sum_erase s e ha
      omega
    · intro i hi
      by_cases hia : i = a
      · subst hia
        rw [Function.update_self]
        have hrw : P' i = C (w i) * ((P i).comp (X + C 1) - P i) := by simp [hP', mul_sub]
        by_cases hPi : P i = 0
        · rw [hrw, hPi]
          simp
        · have hlt : ((P i).comp (X + C 1) - P i).degree < (P i).degree :=
            degree_sub_lt_right (hcomp _ hPi).1 hPi (hcomp _ hPi).2
          have hnat : (P i).natDegree < e i :=
            (natDegree_lt_iff_degree_lt hPi).2 (hdeg i hi)
          calc (P' i).degree ≤ ((P i).comp (X + C 1) - P i).degree := by
                rw [hrw]; exact hCmul _ _
            _ < (P i).degree := hlt
            _ ≤ ((P i).natDegree : WithBot ℕ) := degree_le_natDegree
            _ ≤ ((e i - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.le_sub_one_of_lt hnat
      · rw [Function.update_of_ne hia]
        refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
        · exact lt_of_le_of_lt ((hCmul _ _).trans (hcomple _)) (hdeg i hi)
        · exact lt_of_le_of_lt (hCmul _ _) (hdeg i hi)
    · intro l hl
      have h1 := hvan (l + 1) (by omega)
      have h2 := hvan l (by omega)
      have : ∑ i ∈ s, (P' i).eval (l : ℂ) * w i ^ l =
          ∑ i ∈ s, (P i).eval ((l + 1 : ℕ) : ℂ) * w i ^ (l + 1) -
            w a * ∑ i ∈ s, (P i).eval (l : ℂ) * w i ^ l := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hP', eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X, Nat.cast_succ]
        ring
      rw [this, h1, h2]
      ring

/-- HOL Light: Baker/expoly.ml, EXPOLY_UNIQUENESS. If the exponential polynomial
`l ↦ ∑ i ∈ s, P i l * w i ^ l`, with pairwise distinct nonzero nodes `w i` and polynomial parts
`P i` of degree at most `e i` given by coefficients `c i`, vanishes at the first
`∑ i ∈ s, (e i + 1)` natural numbers, then all coefficients vanish.

Deviation: the finite set `s` is a `Finset`, so HOL's hypothesis `FINITE s` is dropped; the
conjunctions of hypotheses are curried. -/
theorem expoly_uniqueness {A : Type*} (s : Finset A) (w : A → ℂ) (e : A → ℕ) (c : A → ℕ → ℂ)
    (hw0 : ∀ i ∈ s, w i ≠ 0) (hinj : ∀ i ∈ s, ∀ j ∈ s, w i = w j → i = j)
    (hvan : ∀ l : ℕ, l < ∑ i ∈ s, (e i + 1) →
      ∑ i ∈ s, (∑ t ∈ Finset.range (e i + 1), c i t * (l : ℂ) ^ t) * w i ^ l = 0) :
    ∀ i ∈ s, ∀ t, t ≤ e i → c i t = 0 := by
  classical
  have hres := expoly_core (∑ i ∈ s, (e i + 1)) s w (fun i => e i + 1)
    (fun i => expolyPoly (e i) (c i)) rfl hw0 hinj ?_ ?_
  · intro i hi t ht
    have := congrArg (fun Q : ℂ[X] => Q.coeff t) (hres i hi)
    simpa [expoly_coeff, ht] using this
  · intro i _
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [expoly_coeff, ite_eq_right (by omega)]
  · intro l hl
    simpa only [expoly_eval] using hvan l hl

/-- HOL Light: Baker/expoly.ml, EXPOLY_UNIQUENESS_UNIFORM. The uniqueness of exponential
polynomials when all polynomial parts have the same degree bound `d`.

Deviation: `s` is a `Finset` (no `FINITE s`, `CARD s` is `s.card`); hypotheses are curried. -/
theorem expoly_uniqueness_uniform {A : Type*} (s : Finset A) (w : A → ℂ) (d : ℕ) (c : A → ℕ → ℂ)
    (hw0 : ∀ i ∈ s, w i ≠ 0) (hinj : ∀ i ∈ s, ∀ j ∈ s, w i = w j → i = j)
    (hvan : ∀ l : ℕ, l < s.card * (d + 1) →
      ∑ i ∈ s, (∑ t ∈ Finset.range (d + 1), c i t * (l : ℂ) ^ t) * w i ^ l = 0) :
    ∀ i ∈ s, ∀ t, t ≤ d → c i t = 0 :=
  expoly_uniqueness s w (fun _ => d) c hw0 hinj
    (fun l hl => hvan l (by simpa [Finset.sum_const] using hl))

/-- HOL Light: Baker/expoly.ml, EXPOLY_UNIQUENESS_POLYFUN. The uniqueness of exponential
polynomials whose polynomial parts are given as polynomial functions `P i` of degree at most
`e i`.

Deviation: `s` is a `Finset` (no `FINITE s`); hypotheses are curried. -/
theorem expoly_uniqueness_polyfun {A : Type*} (s : Finset A) (w : A → ℂ) (e : A → ℕ)
    (P : A → ℂ → ℂ)
    (hw0 : ∀ i ∈ s, w i ≠ 0) (hinj : ∀ i ∈ s, ∀ j ∈ s, w i = w j → i = j)
    (hP : ∀ i ∈ s, ∃ c : ℕ → ℂ, ∀ x, P i x = ∑ t ∈ Finset.range (e i + 1), c t * x ^ t)
    (hvan : ∀ l : ℕ, l < ∑ i ∈ s, (e i + 1) → ∑ i ∈ s, P i (l : ℂ) * w i ^ l = 0) :
    ∀ i ∈ s, ∀ x, P i x = 0 := by
  classical
  choose! c hc using hP
  have hres := expoly_uniqueness s w e c hw0 hinj (fun l hl => by
    rw [← hvan l hl]
    exact Finset.sum_congr rfl fun i hi => by rw [hc i hi])
  intro i hi x
  rw [hc i hi]
  exact Finset.sum_eq_zero fun t ht => by
    rw [hres i hi t (by simpa [Nat.lt_succ_iff] using ht), zero_mul]

/-- HOL Light: Baker/expoly.ml, EXPOLY_UNIQUENESS_NODES. If an exponential polynomial with nonzero
nodes and some nonzero coefficient vanishes at the first `∑ i ∈ s, (e i + 1)` natural numbers,
then two of its nodes are equal.

Deviation: `s` is a `Finset` (no `FINITE s`); hypotheses are curried. -/
theorem expoly_uniqueness_nodes {A : Type*} (s : Finset A) (w : A → ℂ) (e : A → ℕ)
    (c : A → ℕ → ℂ) (hw0 : ∀ i ∈ s, w i ≠ 0)
    (hvan : ∀ l : ℕ, l < ∑ i ∈ s, (e i + 1) →
      ∑ i ∈ s, (∑ t ∈ Finset.range (e i + 1), c i t * (l : ℂ) ^ t) * w i ^ l = 0)
    (hc : ∃ i t, i ∈ s ∧ t ≤ e i ∧ c i t ≠ 0) :
    ∃ i j, i ∈ s ∧ j ∈ s ∧ i ≠ j ∧ w i = w j := by
  by_contra hcon
  obtain ⟨i, t, hi, ht, hne⟩ := hc
  refine hne (expoly_uniqueness s w e c hw0 (fun i hi j hj hij => ?_) hvan i hi t ht)
  by_contra hne'
  exact hcon ⟨i, j, hi, hj, hne', hij⟩

/-- HOL Light: Baker/expoly.ml, COMPLEX_POLYFUN_DISTINCT_DEGREES. Polynomial functions with
pairwise distinct exact degrees `deg i ≤ N`, given by coefficient families `p i`, are linearly
independent.

Deviation: `s` is a `Finset` (no `FINITE s`); hypotheses are curried. -/
theorem complex_polyfun_distinct_degrees {A : Type*} (s : Finset A) (p : A → ℕ → ℂ)
    (deg : A → ℕ) (N : ℕ) (a : A → ℂ)
    (hp : ∀ i ∈ s, deg i ≤ N ∧ p i (deg i) ≠ 0 ∧ ∀ k, deg i < k → p i k = 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, deg i = deg j → i = j)
    (hsum : ∀ x : ℂ, ∑ i ∈ s, a i * ∑ k ∈ Finset.range (N + 1), p i k * x ^ k = 0) :
    ∀ i ∈ s, a i = 0 := by
  classical
  have hcoef : ∀ k, k ≤ N → ∑ i ∈ s, a i * p i k = 0 := by
    intro k hk
    have hpoly : expolyPoly N (fun k => ∑ i ∈ s, a i * p i k) = 0 := by
      apply Polynomial.funext
      intro x
      rw [expoly_eval, eval_zero, ← hsum x]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => by ring
    have := congrArg (fun Q : ℂ[X] => Q.coeff k) hpoly
    simpa [expoly_coeff, hk] using this
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hi0, hai0⟩ := hcon
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (s.filter fun i => a i ≠ 0) deg
    ⟨i0, Finset.mem_filter.2 ⟨hi0, hai0⟩⟩
  obtain ⟨his, hai⟩ := Finset.mem_filter.1 hi
  have h1 := hcoef (deg i) (hp i his).1
  rw [Finset.sum_eq_single i ?_ (fun h => absurd his h)] at h1
  · exact (mul_ne_zero hai (hp i his).2.1) h1
  · intro j hj hji
    by_cases haj : a j = 0
    · rw [haj, zero_mul]
    · have hle := hmax j (Finset.mem_filter.2 ⟨hj, haj⟩)
      have hlt : deg j < deg i :=
        lt_of_le_of_ne hle fun h => hji (hinj j hj i his h)
      rw [(hp j hj).2.2 _ hlt, mul_zero]

/-- HOL Light: Baker/expoly.ml, COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN. Polynomial functions `P i`
of pairwise distinct exact degrees `deg i` are linearly independent.

Deviation: `s` is a `Finset` (no `FINITE s`); hypotheses are curried. -/
theorem complex_polyfun_distinct_degrees_fun {A : Type*} (s : Finset A) (P : A → ℂ → ℂ)
    (deg : A → ℕ) (a : A → ℂ)
    (hP : ∀ i ∈ s, ∃ c : ℕ → ℂ, c (deg i) ≠ 0 ∧
      ∀ x, P i x = ∑ k ∈ Finset.range (deg i + 1), c k * x ^ k)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, deg i = deg j → i = j)
    (hsum : ∀ x : ℂ, ∑ i ∈ s, a i * P i x = 0) :
    ∀ i ∈ s, a i = 0 := by
  classical
  choose! c hc0 hc using hP
  have hle : ∀ i ∈ s, deg i ≤ ∑ j ∈ s, deg j := fun i hi =>
    Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hi
  refine complex_polyfun_distinct_degrees s (fun i k => if k ≤ deg i then c i k else 0) deg
    (∑ j ∈ s, deg j) a (fun i hi => ⟨hle i hi, ?_, ?_⟩) hinj ?_
  · simpa using hc0 i hi
  · intro k hk
    rw [ite_eq_right (by omega)]
  · intro x
    refine Eq.trans ?_ (hsum x)
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [complex_polyfun_truncate _ _ _ _ (hle i hi), hc i hi]

end RiemannMasullo.Baker
