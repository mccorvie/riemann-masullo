module

public import RiemannMasullo.AppE_TopologicalStacks.Sec1a
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Appendix E.1.1: an earlier Lean statement of the coarseness of the k-topology was false

Definition E.1.1.1(2), p. 828, takes the k-closed subsets of the original space `X` and asks
for the coarsest topology on the same carrier in which those subsets are closed. The first
Lean statement of `isCoarsest_compactlyGenerated` bound the candidate topology as a local
instance inside the set comprehension, so that `IsKClosed` tested compact Hausdorff probes
into the candidate, not into the original topology. That statement is false, as proved below.
It was the project's statement and not the paper's: the paper's statement, with the original
topology written explicitly, is `isCoarsest_compactlyGenerated` in `Sec1a.lean` and is proved
there. The declarations here are therefore not in the namespace `Printed`. Found by #7528.
Nothing imports this file.
-/

@[expose] public section

open Set Topology TopologicalSpace

namespace RiemannMasullo

/-- The statement that `isCoarsest_compactlyGenerated` first made in Lean. The bound topology
is a local instance, so `IsKClosed` is k-closedness for that topology.
Reconstruction: This is not a statement of the paper. It is an earlier Lean reading of
Definition E.1.1.1(2), p. 828, kept with the proof that it is false. -/
def isCoarsest_compactlyGenerated_candidateProbes.{u, w} : Prop :=
  ∀ {X : Type w} [tX : TopologicalSpace X],
    IsGreatest {t : TopologicalSpace X | ∀ s : Set X, IsKClosed.{u} s → IsClosed[t] s}
      (@TopologicalSpace.compactlyGenerated.{u, w} X tX)

/-- Some compact Hausdorff space has a subset that is not closed. -/
private theorem isCoarsest_compactlyGenerated_candidateProbes_false_exists_not_closed.{u} :
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
theorem isCoarsest_compactlyGenerated_candidateProbes_false.{u} :
    ¬ isCoarsest_compactlyGenerated_candidateProbes.{u, 0} := by
  classical
  intro h
  obtain ⟨K, A, hA⟩ := isCoarsest_compactlyGenerated_candidateProbes_false_exists_not_closed.{u}
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

end RiemannMasullo
