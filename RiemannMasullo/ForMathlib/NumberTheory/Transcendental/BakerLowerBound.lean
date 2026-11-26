module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Baker's lower bound for independent logarithms, from the Baker core

A port of the step from `BAKER_CORE_EXISTS` to `BAKER_LOWER_BOUND_INDEPENDENT` in the HOL Light
formalization of Baker's theorem (`Baker/` in `jrh13/hol-light` at `1a0c0e6`: `theorem.ml`,
lines 51–241, and `ALGEBRAIC_ROOT_LOWER_BOUND_POW` of `simple.ml`). BSD-style licence; see
`External/ATTRIBUTION.md`.

`BakerCoreExists` is the statement of `BAKER_CORE_EXISTS` (`Baker/explicit.ml`), translated
literally: indices are natural numbers, `1..n` is `Finset.Icc 1 n` and `0..d` is
`Finset.range (d + 1)`, and `intpoly` is `IntPoly`. It is the core of Baker's method and is
not proved here. `lowerBound_independent_of_bakerCore` is `BAKER_LOWER_BOUND_INDEPENDENT`
proved from it: for logarithms `lg 1, …, lg n` of algebraic numbers, linearly independent
over the rationals, there is `C` with `B⁻ᶜ ≤ ‖β 0 + β 1 lg 1 + ⋯ + β n lg n‖` for all
`B ≥ 2` and all algebraic `β 0, …, β n`, not all zero, of degree at most `Dx` and height at
most `B`.

`bakerFeldmanIndependentThree_of_bakerCore` specializes it to three logarithms and rational
coefficients, in the form of `BakerFeldmanIndependentThree` of #7584. -/

@[expose] public section

namespace RiemannMasullo.Baker

open Finset

/-- HOL Light's `intpoly v n b g` (`Baker/intpoly.ml`): `g` is a polynomial with integer
coefficients in the variables `x r`, `r ∈ v`, of degree at most `n r` in `x r`, whose
coefficients have absolute sum at most `b`. The terms are indexed by a finite set of
numbers. -/
def IntPoly (v : Finset ℕ) (n : ℕ → ℕ) (b : ℝ) (g : (ℕ → ℂ) → ℂ) : Prop :=
  ∃ (s : Finset ℕ) (c : ℕ → ℝ) (e : ℕ → ℕ → ℕ),
    (∀ k ∈ s, (∃ z : ℤ, c k = z) ∧ ∀ r ∈ v, e k r ≤ n r) ∧
    ∑ k ∈ s, |c k| ≤ b ∧
    ∀ x, g x = ∑ k ∈ s, (c k : ℂ) * ∏ r ∈ v, x r ^ e k r

/-- The statement of HOL Light's `BAKER_CORE_EXISTS` (`Baker/explicit.ml`, at `1a0c0e6`),
the core of Baker's method: for logarithms `lg 1, …, lg n` of algebraic numbers that are
linearly independent over the integers, and integer polynomials `g 0, …, g n` of bounded
degrees and size in the values `θ r = exp (lg r)` and `m` further algebraic numbers of
degree at most `Dx` and height at most `B`, the linear form
`g 0 θ + g 1 θ lg 1 + ⋯ + g n θ lg n` is at least `B⁻ᶜ` in norm when `g n θ ≠ 0`.
It is not proved in this file. -/
def BakerCoreExists : Prop :=
  ∀ (n m : ℕ) (lg : ℕ → ℂ) (a : ℕ → ℕ → ℝ) (d : ℕ → ℕ) (H : ℕ → ℝ) (e : ℕ → ℕ)
    (G0 : ℝ) (Dx : ℕ),
    1 ≤ n → 1 ≤ Dx → 1 ≤ G0 →
    (∀ r ∈ Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, (∃ z : ℤ, a r j = z) ∧ |a r j| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0) →
    (∀ b : ℕ → ℝ, (∀ r ∈ Icc 1 n, ∃ z : ℤ, b r = z) →
      ∑ r ∈ Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Icc 1 n, b r = 0) →
    ∃ C : ℕ, ∀ (B : ℝ) (θ : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ) (ax : ℕ → ℕ → ℝ),
      2 ≤ B →
      (∀ r ∈ Icc 1 n, θ r = Complex.exp (lg r)) →
      (∀ r ∈ Icc (n + 1) (n + m), 1 ≤ dx r ∧ dx r ≤ Dx ∧
        (∀ j, (∃ z : ℤ, ax r j = z) ∧ |ax r j| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
        ∑ j ∈ range (dx r + 1), (ax r j : ℂ) * θ r ^ j = 0) →
      (∀ j ≤ n, IntPoly (Icc 1 (n + m)) e G0 (g j)) →
      g n θ ≠ 0 →
      (B ^ C)⁻¹ ≤ ‖g 0 θ + ∑ r ∈ Icc 1 n, g r θ * lg r‖

/-- HOL Light's `INTPOLY_VAR`: a variable is an integer polynomial. -/
theorem intPoly_var (v : Finset ℕ) (n : ℕ → ℕ) (b : ℝ) (r : ℕ) (hr : r ∈ v) (hn : 1 ≤ n r)
    (hb : 1 ≤ b) : IntPoly v n b (fun x ↦ x r) := by
  refine ⟨{0}, fun _ ↦ 1, fun _ i ↦ if i = r then 1 else 0, ?_, ?_, ?_⟩
  · intro k _
    refine ⟨⟨1, by simp⟩, fun i _ ↦ ?_⟩
    show (if i = r then 1 else 0) ≤ n i
    split_ifs with h
    · exact h ▸ hn
    · exact Nat.zero_le _
  · simpa using hb
  · intro x
    have h (i : ℕ) : x i ^ (if i = r then 1 else 0) = if i = r then x i else 1 := by
      split_ifs <;> simp
    simp only [sum_singleton, Complex.ofReal_one, one_mul, h, prod_ite_eq', hr, ite_true]

/-- HOL Light's `ALGEBRAIC_ROOT_LOWER_BOUND_POW` (`Baker/simple.ml`): a nonzero root of an
integer polynomial whose coefficients are at most `B ≥ 2` in absolute value has norm at
least `B⁻²`. -/
theorem inv_sq_le_norm_of_root (a : ℕ → ℝ) (d : ℕ) (B : ℝ) (z : ℂ) (hB : 2 ≤ B)
    (ha : ∀ i, (∃ k : ℤ, a i = k) ∧ |a i| ≤ B) (hd : a d ≠ 0)
    (hroot : ∑ i ∈ range (d + 1), (a i : ℂ) * z ^ i = 0) (hz : z ≠ 0) :
    (B ^ 2)⁻¹ ≤ ‖z‖ := by
  by_contra hlt
  rw [not_le] at hlt
  have hB0 : 0 < B := by linarith
  have hB2 : 4 ≤ B ^ 2 := by nlinarith
  set t := ‖z‖ with ht
  have ht0 : 0 < t := norm_pos_iff.mpr hz
  have ht4 : t < 1 / 4 := hlt.trans_le (by
    rw [one_div]; exact inv_anti₀ (by norm_num) hB2)
  have hBt : B * t < 1 / B := by
    calc B * t < B * (B ^ 2)⁻¹ := mul_lt_mul_of_pos_left hlt hB0
      _ = 1 / B := by field_simp
  -- the lowest nonzero coefficient
  have hex : ∃ i, a i ≠ 0 := ⟨d, hd⟩
  classical
  let k := Nat.find hex
  have hk : a k ≠ 0 := Nat.find_spec hex
  have hkd : k ≤ d := Nat.find_min' hex hd
  have hlow : ∀ i < k, a i = 0 := fun i hi ↦ not_not.mp (Nat.find_min hex hi)
  -- split the sum at k
  have hsplit : ∑ i ∈ range (d + 1), (a i : ℂ) * z ^ i =
      (a k : ℂ) * z ^ k + ∑ i ∈ Ico (k + 1) (d + 1), (a i : ℂ) * z ^ i := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ d + 1),
      sum_eq_zero (fun i hi ↦ by simp [hlow i (mem_Ico.mp hi).2]), zero_add,
      sum_eq_sum_Ico_succ_bot (by omega : k < d + 1)]
  rw [hsplit, add_eq_zero_iff_eq_neg] at hroot
  -- norms
  have hak : 1 ≤ |a k| := by
    obtain ⟨m, hm⟩ := (ha k).1
    rw [hm] at hk ⊢
    have : m ≠ 0 := by exact_mod_cast hk
    exact_mod_cast Int.one_le_abs this
  have hnorm := congrArg norm hroot
  rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hsum : ‖∑ i ∈ Ico (k + 1) (d + 1), (a i : ℂ) * z ^ i‖ ≤ B * (t ^ (k + 1) / (1 - t)) := by
    calc ‖∑ i ∈ Ico (k + 1) (d + 1), (a i : ℂ) * z ^ i‖
        ≤ ∑ i ∈ Ico (k + 1) (d + 1), ‖(a i : ℂ) * z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Ico (k + 1) (d + 1), B * t ^ i := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (ha i).2 (by positivity)
      _ = B * ∑ i ∈ Ico (k + 1) (d + 1), t ^ i := by rw [mul_sum]
      _ ≤ B * (t ^ (k + 1) / (1 - t)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one ht0.le (by linarith)) hB0.le
  have htk : 0 < t ^ k := pow_pos ht0 k
  have key : t ^ k ≤ B * (t ^ (k + 1) / (1 - t)) := by
    calc t ^ k = 1 * t ^ k := (one_mul _).symm
      _ ≤ |a k| * t ^ k := mul_le_mul_of_nonneg_right hak htk.le
      _ = _ := hnorm
      _ ≤ _ := hsum
  -- divide by t ^ k
  have h1t : 0 < 1 - t := by linarith
  have key' : 1 - t ≤ B * t := by
    rw [← mul_div_assoc, le_div_iff₀ h1t, pow_succ] at key
    exact le_of_mul_le_mul_left (by linarith) htk
  have hB' : 1 / B ≤ 1 / 2 := by
    rw [one_div_le_one_div hB0 (by norm_num)]; exact hB
  linarith

/-- HOL Light's `BAKER_CORE_EXISTS_PREFIX` in the form used below: the core applied to the
prefix `lg 1, …, lg r0` of an independent family, with `r0 + 1` further variables and the
size bounds `e = 1`, `G0 = 1`. -/
private theorem bakerCore_prefix (hcore : BakerCoreExists) (n : ℕ) (lg : ℕ → ℂ)
    (a : ℕ → ℕ → ℝ) (d : ℕ → ℕ) (H : ℕ → ℝ) (Dx : ℕ) (hDx : 1 ≤ Dx)
    (hlg : ∀ r ∈ Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, (∃ z : ℤ, a r j = z) ∧ |a r j| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0)
    (hind : ∀ b : ℕ → ℝ, (∀ r ∈ Icc 1 n, ∃ z : ℤ, b r = z) →
      ∑ r ∈ Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Icc 1 n, b r = 0)
    (r0 : ℕ) (h1 : 1 ≤ r0) (hr0 : r0 ≤ n) :
    ∃ C : ℕ, ∀ (B : ℝ) (θ : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ) (ax : ℕ → ℕ → ℝ),
      2 ≤ B →
      (∀ r ∈ Icc 1 r0, θ r = Complex.exp (lg r)) →
      (∀ r ∈ Icc (r0 + 1) (r0 + (r0 + 1)), 1 ≤ dx r ∧ dx r ≤ Dx ∧
        (∀ j, (∃ z : ℤ, ax r j = z) ∧ |ax r j| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
        ∑ j ∈ range (dx r + 1), (ax r j : ℂ) * θ r ^ j = 0) →
      (∀ j ≤ r0, IntPoly (Icc 1 (r0 + (r0 + 1))) (fun _ ↦ 1) 1 (g j)) →
      g r0 θ ≠ 0 →
      (B ^ C)⁻¹ ≤ ‖g 0 θ + ∑ r ∈ Icc 1 r0, g r θ * lg r‖ := by
  have hsub : Icc 1 r0 ⊆ Icc 1 n := Icc_subset_Icc le_rfl hr0
  refine hcore r0 (r0 + 1) lg a d H (fun _ ↦ 1) 1 Dx h1 hDx le_rfl
    (fun r hr ↦ hlg r (hsub hr)) ?_
  intro b hb hsum r hr
  classical
  let b' : ℕ → ℝ := fun r ↦ if r ≤ r0 then b r else 0
  have hb' : ∀ r ∈ Icc 1 n, ∃ z : ℤ, b' r = z := by
    intro r hr'
    by_cases h : r ≤ r0
    · obtain ⟨z, hz⟩ := hb r (mem_Icc.mpr ⟨(mem_Icc.mp hr').1, h⟩)
      exact ⟨z, by simp [b', h, hz]⟩
    · exact ⟨0, by simp [b', h]⟩
  have hsum' : ∑ r ∈ Icc 1 n, (b' r : ℂ) * lg r = 0 := by
    rw [← sum_subset hsub (fun r hrn hr0' ↦ ?_)]
    · rw [← hsum]
      refine sum_congr rfl fun r hr' ↦ ?_
      simp [b', (mem_Icc.mp hr').2]
    · have : ¬ r ≤ r0 := fun h ↦ hr0' (mem_Icc.mpr ⟨(mem_Icc.mp hrn).1, h⟩)
      simp [b', this]
  have := hind b' hb' hsum' r (hsub hr)
  simpa [b', (mem_Icc.mp hr).2] using this

/-- HOL Light's `BAKER_LOWER_BOUND_INDEPENDENT` (`Baker/theorem.ml`, at `1a0c0e6`), proved
from the Baker core `BakerCoreExists`: for logarithms `lg 1, …, lg n` of algebraic numbers,
linearly independent over the integers, there is `C` such that for all `B ≥ 2` and all
algebraic `β 0, …, β n`, not all zero, of degree at most `Dx` and height at most `B`,
`B⁻ᶜ ≤ ‖β 0 + β 1 lg 1 + ⋯ + β n lg n‖`. As in HOL Light, take the largest `r0` with
`β r0 ≠ 0`: if `r0 = 0` the root bound applies, and otherwise the core for the prefix
`lg 1, …, lg r0`, with the `β j` as further variables and the coordinate projections as
the polynomials. -/
theorem lowerBound_independent_of_bakerCore (hcore : BakerCoreExists) (n : ℕ) (lg : ℕ → ℂ)
    (a : ℕ → ℕ → ℝ) (d : ℕ → ℕ) (H : ℕ → ℝ) (Dx : ℕ) (_hn : 1 ≤ n) (hDx : 1 ≤ Dx)
    (hlg : ∀ r ∈ Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, (∃ z : ℤ, a r j = z) ∧ |a r j| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0)
    (hind : ∀ b : ℕ → ℝ, (∀ r ∈ Icc 1 n, ∃ z : ℤ, b r = z) →
      ∑ r ∈ Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Icc 1 n, b r = 0) :
    ∃ C : ℕ, ∀ (B : ℝ) (β : ℕ → ℂ) (db : ℕ → ℕ) (ab : ℕ → ℕ → ℝ),
      2 ≤ B →
      (∀ j ≤ n, 1 ≤ db j ∧ db j ≤ Dx ∧ (∀ i, (∃ z : ℤ, ab j i = z) ∧ |ab j i| ≤ B) ∧
        ab j (db j) ≠ 0 ∧ ∑ i ∈ range (db j + 1), (ab j i : ℂ) * β j ^ i = 0) →
      ¬ (∀ j ≤ n, β j = 0) →
      (B ^ C)⁻¹ ≤ ‖β 0 + ∑ r ∈ Icc 1 n, β r * lg r‖ := by
  classical
  have hpre : ∀ r0, ∃ C : ℕ, 1 ≤ r0 → r0 ≤ n →
      ∀ (B : ℝ) (θ : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ) (ax : ℕ → ℕ → ℝ),
      2 ≤ B →
      (∀ r ∈ Icc 1 r0, θ r = Complex.exp (lg r)) →
      (∀ r ∈ Icc (r0 + 1) (r0 + (r0 + 1)), 1 ≤ dx r ∧ dx r ≤ Dx ∧
        (∀ j, (∃ z : ℤ, ax r j = z) ∧ |ax r j| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
        ∑ j ∈ range (dx r + 1), (ax r j : ℂ) * θ r ^ j = 0) →
      (∀ j ≤ r0, IntPoly (Icc 1 (r0 + (r0 + 1))) (fun _ ↦ 1) 1 (g j)) →
      g r0 θ ≠ 0 →
      (B ^ C)⁻¹ ≤ ‖g 0 θ + ∑ r ∈ Icc 1 r0, g r θ * lg r‖ := by
    intro r0
    by_cases h : 1 ≤ r0 ∧ r0 ≤ n
    · obtain ⟨C, hC⟩ := bakerCore_prefix hcore n lg a d H Dx hDx hlg hind r0 h.1 h.2
      exact ⟨C, fun _ _ ↦ hC⟩
    · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ h⟩
  choose C hC using hpre
  refine ⟨2 + ∑ r0 ∈ Icc 1 n, C r0, ?_⟩
  intro B β db ab hB hβ hne
  have hB1 : 1 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  -- the largest index of a nonzero coefficient
  push Not at hne
  have hS : ((range (n + 1)).filter (fun j ↦ β j ≠ 0)).Nonempty := by
    obtain ⟨j, hj, hβj⟩ := hne
    exact ⟨j, mem_filter.mpr ⟨mem_range.mpr (by omega), hβj⟩⟩
  set r0 := ((range (n + 1)).filter (fun j ↦ β j ≠ 0)).max' hS with hr0def
  have hr0mem := ((range (n + 1)).filter (fun j ↦ β j ≠ 0)).max'_mem hS
  rw [← hr0def, mem_filter, mem_range] at hr0mem
  have hr0n : r0 ≤ n := by omega
  have hβr0 : β r0 ≠ 0 := hr0mem.2
  have hzero : ∀ j, r0 < j → j ≤ n → β j = 0 := by
    intro j hj hjn
    by_contra hβj
    have := ((range (n + 1)).filter (fun j ↦ β j ≠ 0)).le_max' j
      (mem_filter.mpr ⟨mem_range.mpr (by omega), hβj⟩)
    rw [← hr0def] at this
    omega
  -- the linear form only involves the prefix
  have hΛ : β 0 + ∑ r ∈ Icc 1 n, β r * lg r = β 0 + ∑ r ∈ Icc 1 r0, β r * lg r := by
    congr 1
    refine (sum_subset (Icc_subset_Icc le_rfl hr0n) fun r hrn hr ↦ ?_).symm
    have : r0 < r := by
      by_contra h
      exact hr (mem_Icc.mpr ⟨(mem_Icc.mp hrn).1, by omega⟩)
    simp [hzero r this (mem_Icc.mp hrn).2]
  rw [hΛ]
  have hmono : ∀ c ≤ 2 + ∑ r0 ∈ Icc 1 n, C r0,
      (B ^ (2 + ∑ r0 ∈ Icc 1 n, C r0))⁻¹ ≤ (B ^ c)⁻¹ := fun c hc ↦
    inv_anti₀ (pow_pos hBpos _) (pow_le_pow_right₀ hB1 hc)
  rcases Nat.eq_zero_or_pos r0 with h0 | hpos
  · -- only `β 0` is nonzero
    rw [h0] at hβr0 ⊢
    simp only [Icc_eq_empty_of_lt zero_lt_one, sum_empty, add_zero]
    obtain ⟨-, -, hab, hlead, hroot⟩ := hβ 0 (Nat.zero_le n)
    exact (hmono 2 (Nat.le_add_right _ _)).trans
      (inv_sq_le_norm_of_root (ab 0) (db 0) B (β 0) hB hab hlead hroot hβr0)
  · -- the core for the prefix `lg 1, …, lg r0`
    let θ : ℕ → ℂ := fun r ↦ if r ≤ r0 then Complex.exp (lg r) else β (r - (r0 + 1))
    let g : ℕ → (ℕ → ℂ) → ℂ := fun j x ↦ x (r0 + 1 + j)
    have hθ : ∀ j, θ (r0 + 1 + j) = β j := fun j ↦ by
      simp only [θ]
      split_ifs with h
      · omega
      · congr 1
        omega
    have hcore' := hC r0 hpos hr0n B θ g (fun r ↦ db (r - (r0 + 1))) (fun r ↦ ab (r - (r0 + 1)))
      hB (fun r hr ↦ by simp [θ, (mem_Icc.mp hr).2]) ?_ ?_ ?_
    · refine (hmono (C r0) ?_).trans ?_
      · exact (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_Icc.mpr ⟨hpos, hr0n⟩)).trans
          (Nat.le_add_left _ _)
      · have heq : g 0 θ + ∑ r ∈ Icc 1 r0, g r θ * lg r =
            β 0 + ∑ r ∈ Icc 1 r0, β r * lg r := by
          show θ (r0 + 1 + 0) + ∑ r ∈ Icc 1 r0, θ (r0 + 1 + r) * lg r = _
          rw [hθ 0]
          exact congrArg _ (sum_congr rfl fun r _ ↦ by rw [hθ r])
        rw [← heq]
        exact hcore'
    · intro r hr
      obtain ⟨hr1, hr2⟩ := mem_Icc.mp hr
      have hj : r - (r0 + 1) ≤ n := by omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := hβ (r - (r0 + 1)) hj
      refine ⟨h1, h2, h3, h4, ?_⟩
      have : θ r = β (r - (r0 + 1)) := by
        simp only [θ]
        split_ifs with h
        · omega
        · rfl
      rw [this]
      exact h5
    · intro j hj
      exact intPoly_var _ _ _ _ (mem_Icc.mpr ⟨by omega, by omega⟩) le_rfl le_rfl
    · simpa [g, hθ] using hβr0

/-- The independent lower bound for three logarithms and rational coefficients, from the
Baker core: the case `n = 3`, `Dx = 1` of `lowerBound_independent_of_bakerCore`, with the
logarithms indexed by `Fin 3`, the coefficients by `Fin 4`, and the polynomials as
`Polynomial ℤ`. Its statement is the body of `BakerFeldmanIndependentThree` in
`Ch07_SchauderBasesZeta/Sec3b_Isolated.lean` (#7584). -/
theorem bakerFeldmanIndependentThree_of_bakerCore (hcore : BakerCoreExists) :
    ∀ (l : Fin 3 → ℂ) (p : Fin 3 → Polynomial ℤ) (H : Fin 3 → ℝ),
      (∀ i, 0 < (p i).natDegree ∧ 1 ≤ H i ∧ (∀ j, |((p i).coeff j : ℝ)| ≤ H i) ∧
        Polynomial.aeval (Complex.exp (l i)) (p i) = 0) → LinearIndependent ℚ l →
      ∃ d : ℕ, ∀ B : ℝ, 2 ≤ B → ∀ β : Fin 4 → ℂ,
        (∀ i, ∃ q : Polynomial ℤ, q.natDegree = 1 ∧ Polynomial.aeval (β i) q = 0 ∧
          ∀ j, |(q.coeff j : ℝ)| ≤ B) → β ≠ 0 →
        1 / B ^ d ≤ ‖β 0 + ∑ i : Fin 3, β i.succ * l i‖ := by
  intro l p H hp hlin
  have hI : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  -- an integer polynomial vanishing at `x`, as a finite sum
  have hsum (q : Polynomial ℤ) (x : ℂ) (hx : Polynomial.aeval x q = 0) :
      ∑ j ∈ range (q.natDegree + 1), (((q.coeff j : ℝ)) : ℂ) * x ^ j = 0 := by
    rw [← hx, Polynomial.aeval_eq_sum_range]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [zsmul_eq_mul, Complex.ofReal_intCast]
  have hlead (q : Polynomial ℤ) (hq : 0 < q.natDegree) : ((q.coeff q.natDegree : ℤ) : ℝ) ≠ 0 := by
    have : q ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hq
    exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr this
  let idx : ℕ → Fin 3 := fun r ↦ ⟨(r - 1) % 3, Nat.mod_lt _ (by norm_num)⟩
  have hC0 := lowerBound_independent_of_bakerCore hcore 3 (fun r ↦ l (idx r))
    (fun r j ↦ ((p (idx r)).coeff j : ℝ)) (fun r ↦ (p (idx r)).natDegree) (fun r ↦ H (idx r)) 1
    (by norm_num) le_rfl ?_ ?_
  · obtain ⟨C, hC⟩ := hC0
    refine ⟨C, fun B hB β hβ hne ↦ ?_⟩
    choose q hq1 hq0 hqB using hβ
    let jdx : ℕ → Fin 4 := fun j ↦ ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩
    have h := hC B (fun j ↦ β (jdx j)) (fun _ ↦ 1) (fun j i ↦ ((q (jdx j)).coeff i : ℝ)) hB
      ?_ ?_
    · rw [one_div]
      convert h using 2
      rw [hI, sum_insert (by decide), sum_insert (by decide), sum_singleton, Fin.sum_univ_three]
      rw [show jdx 0 = 0 by decide, show jdx 1 = Fin.succ 0 by decide,
        show jdx 2 = Fin.succ 1 by decide, show jdx 3 = Fin.succ 2 by decide,
        show idx 1 = 0 by decide, show idx 2 = 1 by decide, show idx 3 = 2 by decide]
      ring
    · intro j _
      refine ⟨le_rfl, le_rfl, fun i ↦ ⟨⟨_, rfl⟩, hqB _ i⟩, ?_, ?_⟩
      · simpa [hq1] using hlead (q (jdx j)) (by rw [hq1]; norm_num)
      · simpa [hq1] using hsum (q (jdx j)) _ (hq0 (jdx j))
    · intro hall
      apply hne
      funext i
      fin_cases i
      · exact hall 0 (by norm_num)
      · exact hall 1 (by norm_num)
      · exact hall 2 (by norm_num)
      · exact hall 3 (by norm_num)
  · intro r _
    obtain ⟨h1, h2, h3, h4⟩ := hp (idx r)
    exact ⟨h1, h2, fun j ↦ ⟨⟨_, rfl⟩, h3 j⟩, hlead _ h1, hsum _ _ h4⟩
  · intro b hb hb0 r hr
    obtain ⟨z1, hz1⟩ := hb 1 (by decide)
    obtain ⟨z2, hz2⟩ := hb 2 (by decide)
    obtain ⟨z3, hz3⟩ := hb 3 (by decide)
    have h0 := Fintype.linearIndependent_iff.mp hlin ![(z1 : ℚ), z2, z3] (by
      rw [hI, sum_insert (by decide), sum_insert (by decide), sum_singleton, hz1, hz2, hz3]
        at hb0
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Rat.smul_def, Rat.cast_intCast]
      simpa [idx, Complex.ofReal_intCast, add_assoc] using hb0)
    have e1 : z1 = 0 := by
      have h : (z1 : ℚ) = 0 := h0 0
      exact_mod_cast h
    have e2 : z2 = 0 := by
      have h : (z2 : ℚ) = 0 := h0 1
      exact_mod_cast h
    have e3 : z3 = 0 := by
      have h : (z3 : ℚ) = 0 := h0 2
      exact_mod_cast h
    rw [hI] at hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · simp [hz1, e1]
    · simp [hz2, e2]
    · simp [hz3, e3]

end RiemannMasullo.Baker
