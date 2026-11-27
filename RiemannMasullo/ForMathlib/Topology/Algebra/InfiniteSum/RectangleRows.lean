module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace RiemannMasullo

/-- If a bounded linear map selects one row of a rectangular series, Cauchy
convergence of the rectangles bounds every individual term of that row. -/
theorem norm_row_bounded_of_cauchy_rectangles
    {X E : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ × ℕ → X) (b : ℕ × ℕ → E) (i : ℕ) (L : X →L[ℂ] E)
    (hL : ∀ p, L (a p) = if p.1 = i then b p else 0)
    (hc : CauchySeq (fun p : ℕ × ℕ ↦ ∑ q ∈ (Finset.Iic p.1).product (Finset.Iic p.2), a q)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖b (i, n)‖ ≤ B := by
  classical
  let R (p : ℕ × ℕ) := ∑ q ∈ (Finset.Iic p.1).product (Finset.Iic p.2), a q
  let S (n : ℕ) := ∑ j ∈ Finset.Iic n, b (i, j)
  have hmap (m n : ℕ) (hm : i ≤ m) : L (R (m, n)) = S n := by
    change L (∑ q ∈ (Finset.Iic m).product (Finset.Iic n), a q) = S n
    rw [map_sum, Finset.product_eq_sprod, Finset.sum_product]
    rw [Finset.sum_eq_single i]
    · simp only [hL, ite_true]
      rfl
    · intro k _ hk
      apply Finset.sum_eq_zero
      intro j _
      simp only [hL, ite_eq_right hk]
    · intro hi
      exact False.elim (hi (Finset.mem_Iic.mpr hm))
  have ht : Tendsto (fun n : ℕ ↦ (n + i, n)) atTop atTop := by
    apply tendsto_atTop.2
    intro p
    refine eventually_atTop.2 ⟨max p.1 p.2, fun n hn ↦ ?_⟩
    exact ⟨by omega, by omega⟩
  have hS : CauchySeq S := by
    have h := L.uniformContinuous.comp_cauchySeq (hc.comp_tendsto ht)
    change CauchySeq (fun n ↦ L (R (n + i, n))) at h
    simpa only [hmap _ _ (Nat.le_add_left _ _)] using h
  obtain ⟨B, hB⟩ := hS.norm_bddAbove
  have hSn (n : ℕ) : ‖S n‖ ≤ max B 0 := (hB (mem_range_self n)).trans (le_max_left _ _)
  refine ⟨2 * max B 0, by positivity, ?_⟩
  intro n
  cases n with
  | zero =>
    have h := hSn 0
    simpa [S] using h.trans (by nlinarith [le_max_right B 0])
  | succ n =>
    have hdiff : b (i, n + 1) = S (n + 1) - S n := by
      simp only [S, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]
      abel
    rw [hdiff]
    exact (norm_sub_le _ _).trans ((add_le_add (hSn _) (hSn _)).trans_eq (by ring))

/-- The row bound applies to any injectively numbered family, without requiring
that every grid position be occupied. The selecting map may take values in a
normed space different from the space of the original series. -/
theorem norm_fiber_bounded_of_cauchy_rectangles
    {X E Z : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : Z ↪ ℕ × ℕ) (a : Z → X) (b : Z → E) (i : ℕ) (L : X →L[ℂ] E)
    (hL : ∀ z, L (a z) = if (e z).1 = i then b z else 0)
    (hc : CauchySeq (fun p : ℕ × ℕ ↦
      ∑ z ∈ ((Finset.Iic p.1).product (Finset.Iic p.2)).preimage e e.injective.injOn, a z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, (e z).1 = i → ‖b z‖ ≤ B := by
  classical
  let A := Function.extend e a (fun _ ↦ 0)
  let B := Function.extend e b (fun _ ↦ 0)
  have hAe (z : Z) : A (e z) = a z := e.injective.extend_apply _ _ z
  have hBe (z : Z) : B (e z) = b z := e.injective.extend_apply _ _ z
  have hAoff (p : ℕ × ℕ) (hp : p ∉ range e) : A p = 0 :=
    Function.extend_apply' _ _ _ hp
  have hBoff (p : ℕ × ℕ) (hp : p ∉ range e) : B p = 0 :=
    Function.extend_apply' _ _ _ hp
  have hsum (p : ℕ × ℕ) :
      (∑ z ∈ ((Finset.Iic p.1).product (Finset.Iic p.2)).preimage e e.injective.injOn, a z) =
        ∑ q ∈ (Finset.Iic p.1).product (Finset.Iic p.2), A q := by
    simpa only [hAe] using Finset.sum_preimage e _ e.injective.injOn A (fun q _ hq ↦ hAoff q hq)
  have hAc : CauchySeq (fun p : ℕ × ℕ ↦ ∑ q ∈ (Finset.Iic p.1).product (Finset.Iic p.2), A q) := by
    simpa only [hsum] using hc
  obtain ⟨C, hC, hbound⟩ := norm_row_bounded_of_cauchy_rectangles A B i L (by
    intro p
    by_cases hp : p ∈ range e
    · obtain ⟨z, rfl⟩ := hp
      rw [hAe, hBe, hL]
    · rw [hAoff p hp, hBoff p hp, map_zero, ite_self]) hAc
  refine ⟨C, hC, fun z hz ↦ ?_⟩
  have h := hbound (e z).2
  rw [← hz, Prod.mk.eta, hBe] at h
  exact h

end RiemannMasullo
