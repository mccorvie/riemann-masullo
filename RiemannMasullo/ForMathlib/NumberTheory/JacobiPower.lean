module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Squarefree coefficients of powers of a prime sum -/

public noncomputable section

open Finset

namespace RiemannMasullo.JacobiPower

section Subsets

variable {ι : Type*} [DecidableEq ι]

private def toggle (i : ι) (s : Finset ι) : Finset ι := if i ∈ s then s.erase i else insert i s

private theorem toggle_twice (i : ι) (s : Finset ι) : toggle i (toggle i s) = s := by
  by_cases h : i ∈ s <;> simp [toggle, h]

private theorem mem_toggle (i : ι) (s : Finset ι) : i ∈ toggle i s ↔ i ∉ s := by
  by_cases h : i ∈ s <;> simp [toggle, h]

private theorem card_le_toggle_succ (i : ι) (s : Finset ι) : s.card ≤ (toggle i s).card + 1 := by
  by_cases h : i ∈ s
  · rw [toggle, ite_eq_left h, card_erase_add_one h]
  · rw [toggle, ite_eq_right h, card_insert_of_notMem h]
    omega

variable [Fintype ι]

private theorem sum_toggle (i : ι) (f : Finset ι → ℝ) :
    ∑ s, f (toggle i s) = ∑ s, f s := by
  let e : Equiv.Perm (Finset ι) := ⟨toggle i, toggle i, toggle_twice i, toggle_twice i⟩
  exact Equiv.sum_comp e f

private def subsetCoefficient (b : ι → ℝ) : ℕ → Finset ι → ℝ
  | 0, s => if s = ∅ then 1 else 0
  | k + 1, s => ∑ i, b i * subsetCoefficient b k (toggle i s)

private theorem subset_support (b : ι → ℝ) (k : ℕ) (s : Finset ι)
    (hs : subsetCoefficient b k s ≠ 0) : s.card ≤ k := by
  induction k generalizing s with
  | zero =>
    by_contra! h
    exact hs (ite_eq_right (Finset.card_pos.mp h).ne_empty)
  | succ k ih =>
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    exact (card_le_toggle_succ i s).trans (Nat.succ_le_succ (ih _ (right_ne_zero_of_mul hi)))

private theorem toggle_product (z : ι → ℝ) (hz : ∀ i, z i ^ 2 = 1) (i : ι) (s : Finset ι) :
    (∏ j ∈ toggle i s, z j) = z i * ∏ j ∈ s, z j := by
  by_cases h : i ∈ s
  · rw [toggle, ite_eq_left h, ← mul_prod_erase s z h, ← mul_assoc, ← pow_two, hz, one_mul]
  · simp [toggle, h]

private theorem subset_expansion (z b : ι → ℝ) (hz : ∀ i, z i ^ 2 = 1) (k : ℕ) :
    (∑ i, b i * z i) ^ k = ∑ s : Finset ι, subsetCoefficient b k s * ∏ j ∈ s, z j := by
  induction k with
  | zero => simp [subsetCoefficient, ite_mul]
  | succ k ih =>
    rw [pow_succ', ih, sum_mul]
    calc
      _ = ∑ i, ∑ s : Finset ι, b i * subsetCoefficient b k (toggle i s) * ∏ j ∈ s, z j := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        calc
          _ = ∑ s : Finset ι, b i * subsetCoefficient b k s * ∏ j ∈ toggle i s, z j :=
            sum_congr rfl fun s _ ↦ by rw [toggle_product z hz]; ring
          _ = _ := by
            simpa only [toggle_twice] using
              (sum_toggle i (fun s ↦ b i * subsetCoefficient b k s * ∏ j ∈ toggle i s, z j)).symm
      _ = _ := by rw [sum_comm]; simp only [subsetCoefficient, sum_mul]

private theorem toggle_count (f : Finset ι → ℝ) :
    ∑ s : Finset ι, ∑ i ∈ (univ.filter (fun i ↦ i ∉ s)), f (toggle i s) ^ 2 =
      ∑ s : Finset ι, (s.card : ℝ) * f s ^ 2 := by
  simp only [sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ i, ∑ s : Finset ι, if i ∈ s then f s ^ 2 else 0 := by
      apply sum_congr rfl
      intro i _
      simpa only [mem_toggle] using sum_toggle i (fun s ↦ if i ∈ s then f s ^ 2 else 0)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [← sum_filter]
      simp

private theorem subset_step_energy (b : ι → ℝ) (f : Finset ι → ℝ) (k : ℕ)
    (hs : ∀ s, f s ≠ 0 → s.card ≤ k) :
    (∑ s : Finset ι, (∑ i, b i * f (toggle i s)) ^ 2) ≤
      (4 * ((k : ℝ) + 1)) * (∑ i, b i ^ 2) * ∑ s, f s ^ 2 := by
  let A := ∑ i, b i ^ 2
  let E := ∑ s, f s ^ 2
  let up (s : Finset ι) := ∑ i ∈ s, b i * f (toggle i s)
  let dn (s : Finset ι) := ∑ i ∈ (univ.filter (fun i ↦ i ∉ s)), b i * f (toggle i s)
  have hA : 0 ≤ A := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hE : 0 ≤ E := sum_nonneg fun _ _ ↦ sq_nonneg _
  have split (s : Finset ι) : (∑ i, b i * f (toggle i s)) = up s + dn s := by
    simpa [up, dn] using
      (sum_filter_add_sum_filter_not (s := (univ : Finset ι)) (fun i ↦ i ∈ s)
        (fun i ↦ b i * f (toggle i s))).symm
  have hup (s : Finset ι) : up s ^ 2 ≤ ((k : ℝ) + 1) * ∑ i, b i ^ 2 * f (toggle i s) ^ 2 := by
    by_cases h : s.card ≤ k + 1
    · have hc : (s.card : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast h
      calc
        _ ≤ (s.card : ℝ) * ∑ i ∈ s, (b i * f (toggle i s)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        _ ≤ ((k : ℝ) + 1) * ∑ i, (b i * f (toggle i s)) ^ 2 :=
          mul_le_mul hc (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _)
            (sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
        _ = _ := by simp only [mul_pow]
    · have hzero (i : ι) : f (toggle i s) = 0 := by
        by_contra hn
        exact h ((card_le_toggle_succ i s).trans (Nat.succ_le_succ (hs _ hn)))
      simp [up, hzero]
  have hdn (s : Finset ι) : dn s ^ 2 ≤ A * ∑ i ∈ (univ.filter (fun i ↦ i ∉ s)), f (toggle i s) ^ 2 := by
    apply (sum_mul_sq_le_sq_mul_sq _ b (fun i ↦ f (toggle i s))).trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ ↦ sq_nonneg _)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ sq_nonneg _
  have hsum_up : (∑ s, up s ^ 2) ≤ ((k : ℝ) + 1) * (A * E) := by
    apply (sum_le_sum fun s _ ↦ hup s).trans_eq
    rw [← mul_sum, sum_comm]
    congr 1
    have ht (i : ι) : ∑ s, f (toggle i s) ^ 2 = E := sum_toggle i (fun s ↦ f s ^ 2)
    simp only [← mul_sum, ht, A, sum_mul]
  have hsum_dn : (∑ s, dn s ^ 2) ≤ A * ((k : ℝ) * E) := by
    apply (sum_le_sum fun s _ ↦ hdn s).trans
    rw [← mul_sum, toggle_count]
    apply mul_le_mul_of_nonneg_left _ hA
    dsimp [E]
    rw [mul_sum]
    apply sum_le_sum
    intro s _
    by_cases h : f s = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs s h) (sq_nonneg _)
  calc
    _ ≤ ∑ s, 2 * (up s ^ 2 + dn s ^ 2) := sum_le_sum fun s _ ↦ by
      rw [split]
      nlinarith only [sq_nonneg (up s - dn s)]
    _ = 2 * ((∑ s, up s ^ 2) + ∑ s, dn s ^ 2) := by rw [← mul_sum, sum_add_distrib]
    _ ≤ 2 * ((((k : ℝ) + 1) * (A * E)) + A * ((k : ℝ) * E)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsum_up hsum_dn) (by norm_num)
    _ ≤ _ := by
      change _ ≤ 4 * ((k : ℝ) + 1) * A * E
      nlinarith only [mul_nonneg hA hE]

private theorem subset_energy (b : ι → ℝ) (k : ℕ) :
    ∑ s : Finset ι, subsetCoefficient b k s ^ 2 ≤
      (4 : ℝ) ^ k * k.factorial * (∑ i, b i ^ 2) ^ k := by
  induction k with
  | zero => simp [subsetCoefficient, ite_pow]
  | succ k ih =>
    apply (subset_step_energy b (subsetCoefficient b k) k (subset_support b k)).trans
    calc
      _ ≤ 4 * ((k : ℝ) + 1) * (∑ i, b i ^ 2) *
          (4 ^ k * (k.factorial : ℝ) * (∑ i, b i ^ 2) ^ k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [Nat.factorial_succ]; push_cast; ring

end Subsets
private def kernel (P : Finset ℕ) (s : Finset P) : ℕ := ∏ p ∈ s, (p : ℕ)

private def kernels (P : Finset ℕ) : Finset ℕ := univ.image (kernel P)

private theorem kernel_factors (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    (kernel P s).primeFactors = s.map (Function.Embedding.subtype (· ∈ P)) := by
  let e := Function.Embedding.subtype (· ∈ P)
  have he : kernel P s = ∏ p ∈ s.map e, p := by simp [kernel, e]
  rw [he]
  apply Nat.primeFactors_prod
  intro p h
  obtain ⟨i, _, rfl⟩ := mem_map.mp h
  exact hp i i.property

private theorem kernel_injective (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) :
    Function.Injective (kernel P) := by
  intro s t h
  apply map_injective (Function.Embedding.subtype (· ∈ P))
  rw [← kernel_factors P hp, ← kernel_factors P hp, h]

/-- The coefficient of the squarefree kernel of each ordered prime word of length `k`,
summed across all words with that kernel. -/
def coefficient (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ) : ℕ → ℝ :=
  Function.extend (kernel P) (subsetCoefficient (fun p : P ↦ b p) k) (fun _ ↦ 0)

private theorem coefficient_at (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ)
    (hp : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    coefficient k P b (kernel P s) = subsetCoefficient (fun p : P ↦ b p) k s :=
  (kernel_injective P hp).extend_apply _ _ _

private theorem coefficient_outside (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ) (n : ℕ)
    (h : n ∉ kernels P) : coefficient k P b n = 0 :=
  Function.extend_apply' _ _ _ (fun ⟨s, hs⟩ ↦ h (mem_image.mpr ⟨s, mem_univ _, hs⟩))

private theorem sum_weighted (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ) (hp : ∀ p ∈ P, Nat.Prime p)
    (T : Finset ℕ) (hT : ∀ n, coefficient k P b n ≠ 0 → n ∈ T) (g : ℕ → ℝ) :
    ∑ n ∈ T, coefficient k P b n * g n =
      ∑ s : Finset P, subsetCoefficient (fun p : P ↦ b p) k s * g (kernel P s) := by
  calc
    _ = ∑ n ∈ T ∪ kernels P, coefficient k P b n * g n :=
      sum_subset subset_union_left fun n _ h ↦ by
        rw [show coefficient k P b n = 0 from by_contra fun hn ↦ h (hT n hn), zero_mul]
    _ = ∑ n ∈ kernels P, coefficient k P b n * g n :=
      (sum_subset subset_union_right fun n _ h ↦ by rw [coefficient_outside k P b n h, zero_mul]).symm
    _ = _ := by
      rw [kernels, sum_image (fun _ _ _ _ he ↦ kernel_injective P hp he)]
      exact sum_congr rfl fun s _ ↦ by rw [coefficient_at k P b hp s]

/-- Every nonzero coefficient has a positive odd squarefree index bounded by the
`k`-th power of the prime cutoff. -/
theorem coefficient_support (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, Odd p) (hN : ∀ p ∈ P, p ≤ N)
    {n : ℕ} (hne : coefficient k P b n ≠ 0) : Odd n ∧ Squarefree n ∧ 0 < n ∧ n ≤ N ^ k := by
  have hn : n ∈ kernels P := by
    by_contra h
    exact hne (coefficient_outside k P b n h)
  obtain ⟨s, _, rfl⟩ := mem_image.mp hn
  rw [coefficient_at k P b hp s] at hne
  have hc := subset_support (fun p : P ↦ b p) k s hne
  have hsq := Nat.squarefree_prod_primeFactors (kernel P s)
  rw [kernel_factors P hp, prod_map] at hsq
  have hbound : kernel P s ≤ N ^ s.card :=
    prod_le_pow_card s (fun p : P ↦ (p : ℕ)) N (fun p _ ↦ hN p p.property)
  refine ⟨prod_induction _ Odd (fun _ _ ↦ Odd.mul) odd_one (fun p _ ↦ hodd p p.property),
    hsq, Nat.pos_of_ne_zero hsq.ne_zero, ?_⟩
  by_cases h : 1 ≤ N
  · exact hbound.trans (pow_le_pow_right₀ h hc)
  · cases k with
    | zero => simpa only [Nat.le_zero.mp hc] using hbound
    | succ k =>
      obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      exact (h ((hp i i.property).one_le.trans (hN i i.property))).elim

private theorem jacobi_kernel (a : ℕ) (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p)
    (s : Finset P) :
    (jacobiSym a (kernel P s) : ℝ) = ∏ p ∈ s, (jacobiSym a (p : ℕ) : ℝ) := by
  change (jacobiSym a (∏ p ∈ s, (p : ℕ)) : ℝ) = _
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s h ih =>
    rw [prod_insert h, prod_insert h, jacobiSym.mul_right' a (hp p p.property).ne_zero
      (prod_ne_zero_iff.mpr fun (i : P) _ ↦ (hp i i.property).ne_zero), Int.cast_mul, ih]

/-- Raising the prime sum to any natural power gives the fixed squarefree coefficients
at each numerator coprime to all primes in the sum. -/
theorem expansion (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ) (a : ℕ) (hp : ∀ p ∈ P, Nat.Prime p)
    (hcop : ∀ p ∈ P, Nat.Coprime a p) (T : Finset ℕ)
    (hT : ∀ n, coefficient k P b n ≠ 0 → n ∈ T) :
    (∑ p ∈ P, b p * (jacobiSym a p : ℝ)) ^ k =
      ∑ n ∈ T, coefficient k P b n * (jacobiSym a n : ℝ) := by
  let z (p : P) : ℝ := jacobiSym a (p : ℕ)
  have hz (p : P) : z p ^ 2 = 1 := by
    have h := jacobiSym.sq_one (a := (a : ℤ)) (b := (p : ℕ)) (by
      rw [Int.gcd_natCast_natCast]
      exact hcop p p.property)
    dsimp only [z]
    exact_mod_cast h
  rw [sum_weighted k P b hp T hT (fun n ↦ (jacobiSym a n : ℝ))]
  simp only [jacobi_kernel a P hp]
  have h := subset_expansion z (fun p : P ↦ b p) hz k
  dsimp only [z] at h
  rwa [sum_coe_sort P (fun p ↦ b p * (jacobiSym a p : ℝ))] at h

/-- The coefficient energy on any finite set is at most `4^k k!` times the `k`-th
power of the prime energy. -/
theorem energy (k : ℕ) (P : Finset ℕ) (b : ℕ → ℝ) (hp : ∀ p ∈ P, Nat.Prime p) (T : Finset ℕ) :
    ∑ n ∈ T, coefficient k P b n ^ 2 ≤
      (4 : ℝ) ^ k * k.factorial * (∑ p ∈ P, b p ^ 2) ^ k := by
  let U := T ∪ kernels P
  have hU (n : ℕ) (h : coefficient k P b n ≠ 0) : n ∈ U :=
    mem_union_right _ (by_contra fun hn ↦ h (coefficient_outside k P b n hn))
  calc
    _ ≤ ∑ n ∈ U, coefficient k P b n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg subset_union_left fun _ _ _ ↦ sq_nonneg _
    _ = ∑ s : Finset P, subsetCoefficient (fun p : P ↦ b p) k s ^ 2 := by
      simp only [pow_two]
      rw [sum_weighted k P b hp U hU (coefficient k P b)]
      simp only [coefficient_at k P b hp]
    _ ≤ _ := by
      have h := subset_energy (fun p : P ↦ b p) k
      rwa [sum_coe_sort P (fun p ↦ b p ^ 2)] at h

end RiemannMasullo.JacobiPower
