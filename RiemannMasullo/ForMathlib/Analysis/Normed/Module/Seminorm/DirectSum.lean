module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

@[expose] public noncomputable section

open scoped DirectSum

namespace RiemannMasullo

variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

/-- The sum of the coordinate seminorms on a direct sum, evaluated using finite support. -/
def directSumSeminorm (p : ∀ i, Seminorm 𝕜 (X i)) : Seminorm 𝕜 (⨁ i, X i) := by
  refine Seminorm.of (fun x ↦ x.sum fun i ↦ p i) (fun x y ↦ ?_) (fun a x ↦ ?_)
  · rw [DFinsupp.sum_of_support_subset DFinsupp.support_add (fun i _ ↦ map_zero (p i)),
      DFinsupp.sum_of_support_subset Finset.subset_union_left (fun i _ ↦ map_zero (p i)),
      DFinsupp.sum_of_support_subset Finset.subset_union_right (fun i _ ↦ map_zero (p i)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ ↦ map_add_le_add (p i) (x i) (y i)
  · rw [DFinsupp.sum_of_support_subset (DFinsupp.support_smul a x) (fun i _ ↦ map_zero (p i))]
    simp only [DFinsupp.smul_apply, map_smul_eq_mul, Finset.mul_sum, DFinsupp.sum]

/-- The seminorm sum can be evaluated over any finite set containing the support. -/
theorem directSumSeminorm_apply (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i) (s : Finset ι)
    (hs : x.support ⊆ s) :
    directSumSeminorm p x = ∑ i ∈ s, p i (x i) := by
  exact DFinsupp.sum_of_support_subset hs fun i _ ↦ map_zero (p i)

/-- On a single summand the seminorm sum restricts to the corresponding seminorm. -/
@[simp]
theorem directSumSeminorm_lof (p : ∀ i, Seminorm 𝕜 (X i)) (i : ι) (x : X i) :
    directSumSeminorm p (DirectSum.lof 𝕜 ι X i x) = p i x := by
  exact DFinsupp.sum_single_index (h := fun i ↦ p i) (map_zero (p i))

/-- Any finite coordinate sum is bounded by the sum over the whole direct sum. -/
theorem sum_le_directSumSeminorm (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i)
    (s : Finset ι) : (∑ i ∈ s, p i (x i)) ≤ directSumSeminorm p x := by
  rw [directSumSeminorm_apply p x (s ∪ x.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun i _ _ ↦ apply_nonneg (p i) (x i))

end RiemannMasullo
