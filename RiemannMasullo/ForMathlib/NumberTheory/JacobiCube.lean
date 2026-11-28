module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Squarefree coefficients of a cubic prime sum -/

public noncomputable section

open scoped BigOperators

namespace RiemannMasullo.JacobiCube

/-- Products of three distinct members of the prime set. -/
def tripleProducts (P : Finset ℕ) : Finset ℕ :=
  (P.powersetCard 3).image (fun t ↦ ∏ p ∈ t, p)

/-- Possible squarefree kernels of ordered triples from the prime set. -/
def supportSet (P : Finset ℕ) : Finset ℕ := P ∪ tripleProducts P

/-- The coefficient at the squarefree kernel of an ordered prime triple. A singleton
receives the three placements of each repeated prime, counting the constant triple once. -/
def coefficient (P : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ∈ P then b n * (3 * (∑ p ∈ P, b p ^ 2) - 2 * b n ^ 2)
  else if n ∈ tripleProducts P then 6 * ∏ p ∈ n.primeFactors, b p else 0

private def elementary (P : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ P.powersetCard k, ∏ p ∈ t, b p

private theorem elementary_insert (P : Finset ℕ) (b : ℕ → ℝ) (k i : ℕ) (hi : i ∉ P) :
    elementary (insert i P) b (k + 1) =
      elementary P b (k + 1) + b i * elementary P b k := by
  have hnot (t : Finset ℕ) (ht : t ∈ P.powersetCard k) : i ∉ t :=
    fun h ↦ hi ((Finset.mem_powersetCard.mp ht).1 h)
  have hd : Disjoint (P.powersetCard (k + 1)) ((P.powersetCard k).image (insert i)) := by
    refine Finset.disjoint_left.mpr ?_
    rintro t ht him
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp him
    exact hi ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _))
  have hinj : Set.InjOn (insert i) (↑(P.powersetCard k) : Set (Finset ℕ)) := by
    intro x hx y hy he
    simpa [Finset.erase_insert (hnot x hx), Finset.erase_insert (hnot y hy)] using
      congrArg (fun t : Finset ℕ ↦ t.erase i) he
  unfold elementary
  rw [Finset.powersetCard_succ_insert hi, Finset.sum_union hd, Finset.sum_image hinj, Finset.mul_sum]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun t ht ↦ Finset.prod_insert (hnot t ht))

private theorem square_cube_identities (P : Finset ℕ) (b : ℕ → ℝ) :
    (∑ p ∈ P, b p) ^ 2 = (∑ p ∈ P, b p ^ 2) + 2 * elementary P b 2 ∧
    (∑ p ∈ P, b p) ^ 3 = 3 * (∑ p ∈ P, b p) * (∑ p ∈ P, b p ^ 2) -
      2 * (∑ p ∈ P, b p ^ 3) + 6 * elementary P b 3 := by
  induction P using Finset.induction_on with
  | empty =>
    have h2 : (∅ : Finset ℕ).powersetCard 2 = ∅ := Finset.powersetCard_eq_empty.mpr (by decide)
    have h3 : (∅ : Finset ℕ).powersetCard 3 = ∅ := Finset.powersetCard_eq_empty.mpr (by decide)
    simp [elementary, h2, h3]
  | @insert i P hi ih =>
    have h1 : elementary P b 1 = ∑ p ∈ P, b p := by
      simp [elementary, Finset.powersetCard_one]
    simp only [Finset.sum_insert hi]
    constructor
    · rw [elementary_insert P b 1 i hi, h1]
      linear_combination ih.1
    · rw [elementary_insert P b 2 i hi]
      linear_combination ih.2 + 3 * b i * ih.1

private theorem cube_split (P : Finset ℕ) (b : ℕ → ℝ) :
    (∑ p ∈ P, b p) ^ 3 =
      (∑ p ∈ P, b p * (3 * (∑ q ∈ P, b q ^ 2) - 2 * b p ^ 2)) +
      6 * elementary P b 3 := by
  rw [(square_cube_identities P b).2]
  congr 1
  calc
    _ = (∑ p ∈ P, (b p * (3 * (∑ q ∈ P, b q ^ 2)) - 2 * b p ^ 3)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ = _ := Finset.sum_congr rfl fun _ _ ↦ by ring

private theorem triple_factors {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {t : Finset ℕ}
    (ht : t ∈ P.powersetCard 3) : (∏ p ∈ t, p).primeFactors = t :=
  Nat.primeFactors_prod fun p h ↦ hp p ((Finset.mem_powersetCard.mp ht).1 h)

private theorem triple_not_mem {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {t : Finset ℕ}
    (ht : t ∈ P.powersetCard 3) : (∏ p ∈ t, p) ∉ P := by
  intro hm
  have h := triple_factors hp ht
  rw [(hp _ hm).primeFactors] at h
  have hcard := (Finset.mem_powersetCard.mp ht).2
  rw [← h, Finset.card_singleton] at hcard
  contradiction

private theorem sum_support (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) (f : ℕ → ℝ) :
    ∑ n ∈ supportSet P, f n =
      (∑ n ∈ P, f n) + ∑ t ∈ P.powersetCard 3, f (∏ p ∈ t, p) := by
  have hd : Disjoint P (tripleProducts P) := by
    refine Finset.disjoint_left.mpr ?_
    rintro n hn h3
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h3
    exact triple_not_mem hp ht hn
  rw [supportSet, Finset.sum_union hd, tripleProducts, Finset.sum_image]
  intro s hs t ht he
  exact (triple_factors hp hs).symm.trans ((congrArg Nat.primeFactors he).trans (triple_factors hp ht))

private theorem coefficient_triple {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) (b : ℕ → ℝ)
    {t : Finset ℕ} (ht : t ∈ P.powersetCard 3) :
    coefficient P b (∏ p ∈ t, p) = 6 * ∏ p ∈ t, b p := by
  have hm : (∏ p ∈ t, p) ∈ tripleProducts P := Finset.mem_image_of_mem _ ht
  simp only [coefficient, ite_eq_right (triple_not_mem hp ht), ite_eq_left hm, triple_factors hp ht]

private theorem coefficient_outside {P : Finset ℕ} {b : ℕ → ℝ} {n : ℕ}
    (hn : n ∉ supportSet P) : coefficient P b n = 0 := by
  have hh := Finset.notMem_union.mp hn
  simp [coefficient, hh.1, hh.2]

/-- The nonzero coefficients are supported on positive odd squarefree integers up to the
cube of a bound for the primes. -/
theorem coefficient_support (P : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, Odd p) (hN : ∀ p ∈ P, p ≤ N)
    {n : ℕ} (hne : coefficient P b n ≠ 0) : Odd n ∧ Squarefree n ∧ 0 < n ∧ n ≤ N ^ 3 := by
  have hn : n ∈ supportSet P := by
    by_contra h
    exact hne (coefficient_outside h)
  rcases Finset.mem_union.mp hn with hn | h3
  · exact ⟨hodd n hn, (hp n hn).squarefree, (hp n hn).pos, (hN n hn).trans (Nat.le_pow (by decide))⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h3
    obtain ⟨htP, hc⟩ := Finset.mem_powersetCard.mp ht
    have hsq := Nat.squarefree_prod_primeFactors (∏ p ∈ t, p)
    rw [triple_factors hp ht] at hsq
    exact ⟨Finset.prod_induction _ Odd (fun _ _ ↦ Odd.mul) odd_one (fun p h ↦ hodd p (htP h)),
      hsq, Nat.pos_of_ne_zero hsq.ne_zero, hc ▸ Finset.prod_le_pow_card t id N (fun p h ↦ hN p (htP h))⟩

private theorem jacobi_product (a : ℕ) (t : Finset ℕ) (hp : ∀ p ∈ t, Nat.Prime p) :
    (jacobiSym a (∏ p ∈ t, p) : ℝ) = ∏ p ∈ t, (jacobiSym a p : ℝ) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hps (p : ℕ) (h : p ∈ s) := hp p (Finset.mem_insert_of_mem h)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      jacobiSym.mul_right' a (hp i (Finset.mem_insert_self _ _)).ne_zero
        (Finset.prod_ne_zero_iff.mpr fun p h ↦ (hps p h).ne_zero), Int.cast_mul, ih hps]

/-- Cubing the Jacobi prime sum and collecting by squarefree kernel gives these fixed
coefficients whenever the numerator is coprime to the chosen primes. -/
theorem expansion (P : Finset ℕ) (b : ℕ → ℝ) (a : ℕ) (hp : ∀ p ∈ P, Nat.Prime p)
    (hcop : ∀ p ∈ P, Nat.Coprime a p) (T : Finset ℕ)
    (hT : ∀ n, coefficient P b n ≠ 0 → n ∈ T) :
    (∑ p ∈ P, b p * (jacobiSym a p : ℝ)) ^ 3 =
      ∑ n ∈ T, coefficient P b n * (jacobiSym a n : ℝ) := by
  let J (p : ℕ) : ℝ := jacobiSym a p
  have hJ (p : ℕ) (h : p ∈ P) : J p ^ 2 = 1 := by
    have he := jacobiSym.sq_one (a := (a : ℤ)) (b := p) (by
      rw [Int.gcd_natCast_natCast]
      exact hcop p h)
    dsimp only [J]
    exact_mod_cast he
  have hA : (∑ p ∈ P, (b p * J p) ^ 2) = ∑ p ∈ P, b p ^ 2 :=
    Finset.sum_congr rfl fun p h ↦ by rw [mul_pow, hJ p h, mul_one]
  have hsupport : (∑ n ∈ supportSet P, coefficient P b n * J n) =
      ∑ n ∈ T, coefficient P b n * J n := by
    calc
      _ = ∑ n ∈ supportSet P ∪ T, coefficient P b n * J n := Finset.sum_subset
        Finset.subset_union_left fun n _ h ↦ by rw [coefficient_outside h, zero_mul]
      _ = _ := (Finset.sum_subset Finset.subset_union_right fun n _ h ↦ by
        rw [show coefficient P b n = 0 from by_contra fun hn ↦ h (hT n hn), zero_mul]).symm
  change (∑ p ∈ P, b p * J p) ^ 3 = _
  rw [← hsupport, sum_support P hp, cube_split P (fun p ↦ b p * J p), hA]
  unfold elementary
  congr 1
  · refine Finset.sum_congr rfl fun p h ↦ ?_
    rw [coefficient, ite_eq_left h, mul_pow, hJ p h, mul_one]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [coefficient_triple hp b ht, Finset.prod_mul_distrib]
    have hJt : J (∏ p ∈ t, p) = ∏ p ∈ t, J p :=
      jacobi_product a t fun p h ↦ hp p ((Finset.mem_powersetCard.mp ht).1 h)
    rw [hJt]
    ring

/-- The squared coefficient energy is at most fifteen times the cube of the prime energy. -/
theorem energy (P : Finset ℕ) (b : ℕ → ℝ) (hp : ∀ p ∈ P, Nat.Prime p) (T : Finset ℕ) :
    ∑ n ∈ T, coefficient P b n ^ 2 ≤ 15 * (∑ p ∈ P, b p ^ 2) ^ 3 := by
  let A := ∑ p ∈ P, b p ^ 2
  have hle (p : ℕ) (h : p ∈ P) : b p ^ 2 ≤ A :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (b i)) h
  have hsing : (∑ p ∈ P, coefficient P b p ^ 2) ≤ 9 * A ^ 3 := by
    calc
      _ ≤ ∑ p ∈ P, b p ^ 2 * (3 * A) ^ 2 := by
        refine Finset.sum_le_sum fun p h ↦ ?_
        rw [coefficient, ite_eq_left h, mul_pow]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply pow_le_pow_left₀ (by change 0 ≤ 3 * A - 2 * b p ^ 2; linarith [hle p h, sq_nonneg (b p)])
        change 3 * A - 2 * b p ^ 2 ≤ 3 * A
        linarith [sq_nonneg (b p)]
      _ = _ := by rw [← Finset.sum_mul]; change A * (3 * A) ^ 2 = _; ring
  have hminor : 6 * elementary P (fun p ↦ b p ^ 2) 3 ≤ A ^ 3 := by
    rw [show A ^ 3 = _ from cube_split P (fun p ↦ b p ^ 2)]
    apply le_add_of_nonneg_left
    refine Finset.sum_nonneg fun p h ↦ mul_nonneg (sq_nonneg _) ?_
    have hh := Finset.single_le_sum (f := fun p ↦ (b p ^ 2) ^ 2) (fun i _ ↦ sq_nonneg _) h
    linarith [sq_nonneg (b p ^ 2)]
  have htrip : (∑ t ∈ P.powersetCard 3, coefficient P b (∏ p ∈ t, p) ^ 2) ≤ 6 * A ^ 3 := by
    calc
      _ = 36 * elementary P (fun p ↦ b p ^ 2) 3 := by
        unfold elementary
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht ↦ ?_
        rw [coefficient_triple hp b ht, Finset.prod_pow]
        ring
      _ ≤ _ := by linarith
  calc
    _ = ∑ n ∈ T ∩ supportSet P, coefficient P b n ^ 2 := (Finset.sum_subset
      Finset.inter_subset_left fun n hn h ↦ by
        have hout : n ∉ supportSet P := fun hs ↦ h (Finset.mem_inter.mpr ⟨hn, hs⟩)
        rw [coefficient_outside hout, zero_pow (by decide : 2 ≠ 0)]).symm
    _ ≤ ∑ n ∈ supportSet P, coefficient P b n ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      Finset.inter_subset_right fun _ _ _ ↦ sq_nonneg _
    _ ≤ _ := by rw [sum_support P hp]; change _ ≤ 15 * A ^ 3; linarith

end RiemannMasullo.JacobiCube
