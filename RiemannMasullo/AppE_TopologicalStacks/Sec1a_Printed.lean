module

public import RiemannMasullo.AppE_TopologicalStacks.Sec1a
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Appendix E.1.1: the elaborated coarseness statement is false

Definition E.1.1.1(2), p. 828, takes the k-closed subsets of the original space `X` and asks
for the coarsest topology on the same carrier in which those subsets are closed. In
`isCoarsest_compactlyGenerated` the candidate topology is a local instance inside the set
comprehension, so `IsKClosed` tests compact Hausdorff probes into that candidate rather than
into the original topology. The elaborated statement is false. The paper's statement, with
the original topology written explicitly, is proved below as
`Printed.isCoarsest_compactlyGenerated_original`. Nothing imports this file.
-/

@[expose] public section

open Set Topology TopologicalSpace

namespace RiemannMasullo

/-- The statement elaborated by `isCoarsest_compactlyGenerated`. The bound topology is a local
instance, so `IsKClosed` is k-closedness for that topology. -/
def Printed.isCoarsest_compactlyGenerated.{u, w} : Prop :=
  ∀ {X : Type w} [tX : TopologicalSpace X],
    IsGreatest {t : TopologicalSpace X | ∀ s : Set X, IsKClosed.{u} s → IsClosed[t] s}
      (@TopologicalSpace.compactlyGenerated.{u, w} X tX)

/-- Some compact Hausdorff space has a subset that is not closed. -/
private theorem Printed.isCoarsest_compactlyGenerated_false_exists_not_closed.{u} :
    ∃ (K : CompHaus.{u}) (A : Set K), ¬ IsClosed A := by
  by_contra! h
  let K := CompHaus.of (ULift.{u} (OnePoint ℕ))
  have : DiscreteTopology K := discreteTopology_iff_forall_isClosed.2 (h K)
  have : Finite K := finite_of_compact_of_discrete
  have : Infinite K := Infinite.of_injective
    (fun n : ℕ ↦ (ULift.up (n : OnePoint ℕ) : ULift.{u} (OnePoint ℕ)))
    fun a b hab ↦ OnePoint.coe_injective (congrArg ULift.down hab)
  exact not_finite K

/-- The elaborated statement is false. On discrete `Bool`, the indiscrete topology passes the
test that Lean writes down: every map into it is continuous, so a proper nonempty subset is
not k-closed, and the k-closed sets are `∅` and `univ`. The greatest-element clause would then
make the indiscrete topology finer than the discrete one. -/
theorem Printed.isCoarsest_compactlyGenerated_false.{u} :
    ¬ Printed.isCoarsest_compactlyGenerated.{u, 0} := by
  classical
  intro h
  obtain ⟨K, A, hA⟩ := Printed.isCoarsest_compactlyGenerated_false_exists_not_closed.{u}
  have hmem : (⊤ : TopologicalSpace Bool) ∈
      {t : TopologicalSpace Bool | ∀ s : Set Bool, IsKClosed.{u} s → IsClosed[t] s} := by
    intro s hs
    by_cases h1 : true ∈ s <;> by_cases h0 : false ∈ s
    · have : s = univ := by ext b; cases b <;> simp [h0, h1]
      rw [this]; exact @isClosed_univ Bool ⊤
    · exfalso
      have hs' : s = {true} := by
        ext b; cases b <;> simp [h0, h1]
      let g := @ContinuousMap.mk K Bool _ ⊤ (fun k ↦ decide (k ∈ A)) continuous_top
      have hpre : g ⁻¹' s = A := by
        ext k
        simp only [g, mem_preimage, ContinuousMap.coe_mk, hs', mem_singleton_iff,
          decide_eq_true_eq]
      exact hA (hpre ▸ hs K g)
    · exfalso
      have hs' : s = {false} := by
        ext b; cases b <;> simp [h0, h1]
      let g := @ContinuousMap.mk K Bool _ ⊤ (fun k ↦ !decide (k ∈ A)) continuous_top
      have hpre : g ⁻¹' s = A := by
        ext k
        simp only [g, mem_preimage, ContinuousMap.coe_mk, hs', mem_singleton_iff]
        by_cases hk : k ∈ A <;> simp [hk]
      exact hA (hpre ▸ hs K g)
    · have : s = ∅ := by ext b; cases b <;> simp [h0, h1]
      rw [this]; exact @isClosed_empty Bool ⊤
  have hle : (⊤ : TopologicalSpace Bool) ≤
      @TopologicalSpace.compactlyGenerated.{u, 0} Bool ⊥ :=
    (h (X := Bool) (tX := ⊥)).2 hmem
  have hcg : @TopologicalSpace.compactlyGenerated.{u, 0} Bool ⊥ ≤ ⊥ := by
    let : TopologicalSpace Bool := ⊥
    have : DiscreteTopology Bool := ⟨rfl⟩
    rw [← DiscreteTopology.eq_bot (α := Bool)]
    exact continuous_id_iff_le.mp (continuous_compactlyGenerated_to_original (X := Bool))
  have htop : (⊤ : TopologicalSpace Bool) = ⊥ := le_bot_iff.mp (hle.trans hcg)
  have hopen : IsOpen[⊤] ({true} : Set Bool) := by
    rw [htop]
    exact @isOpen_discrete Bool ⊥ ⟨rfl⟩ _
  rcases (isOpen_top_iff (α := Bool) (U := {true})).1 hopen with h' | h'
  · simp at h'
  · have : false ∈ ({true} : Set Bool) := h' ▸ mem_univ false
    cases this

/-- Definition E.1.1.1(2), p. 828, with k-closedness taken in the original topology.
This is the statement `isCoarsest_compactlyGenerated` was meant to make. -/
theorem Printed.isCoarsest_compactlyGenerated_original.{u, w}
    (X : Type w) [tX : TopologicalSpace X] :
    IsGreatest {t : TopologicalSpace X | ∀ s : Set X, @IsKClosed.{u, w} X tX s → IsClosed[t] s}
      (@TopologicalSpace.compactlyGenerated.{u, w} X tX) := by
  have key (s : Set X) :
      IsClosed[@TopologicalSpace.compactlyGenerated.{u, w} X tX] s ↔ @IsKClosed.{u, w} X tX s :=
    isClosed_compactlyGenerated_iff s
  refine ⟨fun s hs => (key s).2 hs, fun t' ht => ?_⟩
  rw [TopologicalSpace.le_def]
  intro s hs
  have hc : IsClosed[@TopologicalSpace.compactlyGenerated.{u, w} X tX] sᶜ :=
    (@isClosed_compl_iff X (@TopologicalSpace.compactlyGenerated.{u, w} X tX) s).2 hs
  exact (@isClosed_compl_iff X t' s).1 (ht sᶜ ((key sᶜ).1 hc))

/-- `isCoarsest_compactlyGenerated` is the statement refuted above. The proof is that
declaration, so the two say the same thing. -/
private theorem Printed.isCoarsest_compactlyGenerated_of_library.{u, w} :
    Printed.isCoarsest_compactlyGenerated.{u, w} :=
  @RiemannMasullo.isCoarsest_compactlyGenerated.{u, w}

end RiemannMasullo
