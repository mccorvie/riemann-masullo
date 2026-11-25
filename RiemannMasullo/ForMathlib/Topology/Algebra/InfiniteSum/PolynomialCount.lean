module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Polynomial count and polynomial decay give summability

A family indexed by a set whose members are counted polynomially by a size function is
summable as soon as its terms decay like the inverse of the size to the power "exponent of the
count plus two".

* `summable_of_encard_le_of_norm_le`: a set `S` of indices, a size `m ≥ 0` on `S`, at most
  `C * (T + 1) ^ k` indices of `S` of size at most `T`, terms at most `K / (1 + m z) ^ (k + 2)`
  on `S` and zero off `S`.
* `summable_prod_int_of_encard_le_of_norm_le`: the same for pairs of an index of `S` and an
  integer, with the size `h ω + |k|` and terms at most `K / (1 + h ω + |k|) ^ (d + 3)`.

The count is stated with `Set.encard` and a bound of the form `((C * (T + 1) ^ k : ℕ) : ℕ∞)`,
as in `idelicExplicitFormula_normOneFourier_count`. The argument is a summation by shells: the
indices of level `⌈m z⌉₊ = j` number at most
`C * (j + 1) ^ k`, each term is at most a constant times `(j + 1) ^ (-(k + 2))`, and
`∑ (j + 1) ^ (-2)` converges. It is the step that the printed proof of Lemma B.4.4.8 of
Masullo's draft (p. 624) leaves out, as its footnote 26 says. The same argument is private in
`RiemannMasullo/AppB_AnalyticNT/Sec4b.lean`
(`summable_bruhatMellin_of_polynomialCount_of_polyCount_decay`,
`idelicExplicitFormula_summable_spectral_characters_shells`).
-/

@[expose] public section

open Filter Function Set
open scoped Topology

namespace RiemannMasullo

/-- **Polynomial count and polynomial decay give summability.** Let `S` be a set of indices
and `m` a size function, nonnegative on `S`, such that for every natural number `T` at most
`C * (T + 1) ^ k` indices of `S` have size at most `T`. If `‖g z‖ ≤ K / (1 + m z) ^ (k + 2)` on
`S` and `g` vanishes off `S`, then `g` is summable. The exponent of the decay is the exponent
of the count plus two. -/
theorem summable_of_encard_le_of_norm_le {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (S : Set ι) (m : ι → ℝ) (hm : ∀ z ∈ S, 0 ≤ m z) (C k : ℕ) (K : ℝ) (g : ι → E)
    (hcount : ∀ T : ℕ, {z ∈ S | m z ≤ (T : ℝ)}.encard ≤ ((C * (T + 1) ^ k : ℕ) : ℕ∞))
    (hdecay : ∀ z ∈ S, ‖g z‖ ≤ K / (1 + m z) ^ (k + 2))
    (hzero : ∀ z ∉ S, g z = 0) : Summable g := by
  classical
  refine Summable.of_norm ?_
  have hseries : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  -- one term, with the level `⌈m z⌉₊` in the base
  have hterm : ∀ z ∈ S, ‖g z‖ ≤ |K| * 2 ^ (k + 2) / ((⌈m z⌉₊ : ℝ) + 1) ^ (k + 2) := by
    intro z hz
    have h0 := hm z hz
    have h1 : (0 : ℝ) < 1 + m z := by linarith
    have h2 : (⌈m z⌉₊ : ℝ) + 1 ≤ 2 * (1 + m z) := by
      have := Nat.ceil_lt_add_one h0
      linarith
    have h3 : ((⌈m z⌉₊ : ℝ) + 1) ^ (k + 2) ≤ 2 ^ (k + 2) * (1 + m z) ^ (k + 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h2 _
    refine (hdecay z hz).trans ?_
    rw [div_le_div_iff₀ (pow_pos h1 _) (by positivity)]
    calc K * ((⌈m z⌉₊ : ℝ) + 1) ^ (k + 2) ≤ |K| * ((⌈m z⌉₊ : ℝ) + 1) ^ (k + 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * (2 ^ (k + 2) * (1 + m z) ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg K)
      _ = |K| * 2 ^ (k + 2) * (1 + m z) ^ (k + 2) := by ring
  -- the number of indices of one level
  have hcard : ∀ (j : ℕ) (v : Finset ι), (∀ z ∈ v, z ∈ S ∧ ⌈m z⌉₊ = j) →
      (v.card : ℝ) ≤ C * ((j : ℝ) + 1) ^ k := by
    intro j v hv
    have hsub : (v : Set ι) ⊆ {z ∈ S | m z ≤ (j : ℝ)} := fun z hz ↦ by
      have hj : ⌈m z⌉₊ ≤ j := (hv z hz).2.le
      exact ⟨(hv z hz).1, (Nat.le_ceil (m z)).trans (by exact_mod_cast hj)⟩
    have h1 : ((v.card : ℕ) : ℕ∞) ≤ ((C * (j + 1) ^ k : ℕ) : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard]
      exact (Set.encard_mono hsub).trans (hcount j)
    have h2 : v.card ≤ C * (j + 1) ^ k := by exact_mod_cast h1
    exact_mod_cast h2
  refine summable_of_sum_le (fun z ↦ norm_nonneg _)
    (c := C * (|K| * 2 ^ (k + 2)) * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2) fun u ↦ ?_
  have hfilter : ∑ z ∈ u, ‖g z‖ = ∑ z ∈ u.filter (· ∈ S), ‖g z‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hz : z ∈ S
    · simp [hz]
    · simp [hz, hzero z hz]
  rw [hfilter, ← Finset.sum_fiberwise_of_maps_to
    (t := (u.filter (· ∈ S)).image fun z ↦ ⌈m z⌉₊) (g := fun z ↦ ⌈m z⌉₊)
    (fun z hz ↦ Finset.mem_image_of_mem _ hz)]
  calc ∑ j ∈ (u.filter (· ∈ S)).image fun z ↦ ⌈m z⌉₊,
        ∑ z ∈ (u.filter (· ∈ S)).filter (fun z ↦ ⌈m z⌉₊ = j), ‖g z‖
      ≤ ∑ j ∈ (u.filter (· ∈ S)).image fun z ↦ ⌈m z⌉₊,
          C * (|K| * 2 ^ (k + 2)) * (1 / ((j : ℝ) + 1) ^ 2) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hj : (j : ℝ) + 1 ≠ 0 := by positivity
        have hv : ∀ z ∈ (u.filter (· ∈ S)).filter (fun z ↦ ⌈m z⌉₊ = j),
            z ∈ S ∧ ⌈m z⌉₊ = j := fun z hz ↦
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2, (Finset.mem_filter.mp hz).2⟩
        calc ∑ z ∈ (u.filter (· ∈ S)).filter (fun z ↦ ⌈m z⌉₊ = j), ‖g z‖
            ≤ ∑ _z ∈ (u.filter (· ∈ S)).filter (fun z ↦ ⌈m z⌉₊ = j),
                (|K| * 2 ^ (k + 2) / ((j : ℝ) + 1) ^ (k + 2)) :=
              Finset.sum_le_sum fun z hz ↦ by
                have := hterm z (hv z hz).1
                rwa [(hv z hz).2] at this
          _ = (((u.filter (· ∈ S)).filter (fun z ↦ ⌈m z⌉₊ = j)).card : ℝ) *
                (|K| * 2 ^ (k + 2) / ((j : ℝ) + 1) ^ (k + 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ C * ((j : ℝ) + 1) ^ k * (|K| * 2 ^ (k + 2) / ((j : ℝ) + 1) ^ (k + 2)) :=
              mul_le_mul_of_nonneg_right (hcard j _ hv) (by positivity)
          _ = C * (|K| * 2 ^ (k + 2)) * (1 / ((j : ℝ) + 1) ^ 2) := by
              rw [pow_add ((j : ℝ) + 1) k 2]
              field_simp
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hseries.sum_le_tsum _ fun j _ ↦ by positivity)
        (by positivity)

/-- **Summation over a counted family and the integers.** Let `S` be a set of indices and `h`
a size function, nonnegative on `S`, such that for every natural number `T` at most
`C * (T + 1) ^ d` indices of `S` have size at most `T`. If
`‖g (ω, k)‖ ≤ K / (1 + h ω + |k|) ^ (d + 3)` for `ω ∈ S` and all integers `k`, and `g (ω, k)`
vanishes for `ω ∉ S`, then `g` is summable over the pairs. The pairs with `h ω + |k| ≤ T`
number at most `C * (T + 1) ^ d * (2 T + 1)`, so the exponent is the exponent of that count
plus two. -/
theorem summable_prod_int_of_encard_le_of_norm_le {Ω E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (S : Set Ω) (h : Ω → ℝ) (hh : ∀ ω ∈ S, 0 ≤ h ω) (C d : ℕ) (K : ℝ)
    (hcount : ∀ T : ℕ, {ω ∈ S | h ω ≤ (T : ℝ)}.encard ≤ ((C * (T + 1) ^ d : ℕ) : ℕ∞))
    (g : Ω × ℤ → E)
    (hdecay : ∀ ω ∈ S, ∀ k : ℤ, ‖g (ω, k)‖ ≤ K / (1 + h ω + |(k : ℝ)|) ^ (d + 3))
    (hzero : ∀ ω ∉ S, ∀ k : ℤ, g (ω, k) = 0) : Summable g := by
  refine summable_of_encard_le_of_norm_le (S ×ˢ (univ : Set ℤ))
    (fun z ↦ h z.1 + |(z.2 : ℝ)|) ?_ (2 * C) (d + 1) K g (fun T ↦ ?_) ?_ ?_
  · rintro ⟨ω, k⟩ ⟨hω, -⟩
    exact add_nonneg (hh ω hω) (abs_nonneg _)
  · have hIcc : (Finset.Icc (-(T : ℤ)) T).card = 2 * T + 1 := by
      rw [Int.card_Icc]
      omega
    have hsub : {z ∈ S ×ˢ (univ : Set ℤ) | h z.1 + |(z.2 : ℝ)| ≤ (T : ℝ)} ⊆
        {ω ∈ S | h ω ≤ (T : ℝ)} ×ˢ (↑(Finset.Icc (-(T : ℤ)) T) : Set ℤ) := by
      rintro ⟨ω, k⟩ ⟨⟨hω, -⟩, hle⟩
      have hle' : h ω + |(k : ℝ)| ≤ (T : ℝ) := hle
      have h0 := hh ω hω
      have hk : |(k : ℝ)| ≤ T := by linarith
      refine ⟨⟨hω, by linarith [abs_nonneg (k : ℝ)]⟩, ?_⟩
      rw [Finset.mem_coe, Finset.mem_Icc]
      rw [abs_le] at hk
      constructor
      · exact_mod_cast hk.1
      · exact_mod_cast hk.2
    calc {z ∈ S ×ˢ (univ : Set ℤ) | h z.1 + |(z.2 : ℝ)| ≤ (T : ℝ)}.encard
        ≤ ({ω ∈ S | h ω ≤ (T : ℝ)} ×ˢ (↑(Finset.Icc (-(T : ℤ)) T) : Set ℤ)).encard :=
          Set.encard_mono hsub
      _ = {ω ∈ S | h ω ≤ (T : ℝ)}.encard * ((2 * T + 1 : ℕ) : ℕ∞) := by
          rw [Set.encard_prod, Set.encard_coe_eq_coe_finsetCard, hIcc]
      _ ≤ ((C * (T + 1) ^ d : ℕ) : ℕ∞) * ((2 * T + 1 : ℕ) : ℕ∞) :=
          mul_le_mul' (hcount T) le_rfl
      _ ≤ ((2 * C * (T + 1) ^ (d + 1) : ℕ) : ℕ∞) := by
          rw [← Nat.cast_mul]
          refine Nat.cast_le.mpr ?_
          calc C * (T + 1) ^ d * (2 * T + 1) ≤ C * (T + 1) ^ d * (2 * (T + 1)) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = 2 * C * (T + 1) ^ (d + 1) := by ring
  · rintro ⟨ω, k⟩ ⟨hω, -⟩
    have := hdecay ω hω k
    rwa [add_assoc] at this
  · rintro ⟨ω, k⟩ hz
    exact hzero ω (fun hω ↦ hz ⟨hω, mem_univ _⟩) k

end RiemannMasullo
