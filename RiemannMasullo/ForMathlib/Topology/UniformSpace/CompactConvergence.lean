module

public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Completion

/-!
# Completeness for compact convergence
-/

public section

open Set Topology UniformSpace

namespace RiemannMasullo

/-- The uniform structure of compact convergence makes the continuous maps into a
uniform additive group whenever their target is one. -/
theorem isUniformAddGroup_continuousMap (X E : Type*) [TopologicalSpace X]
    [AddGroup E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C(X, E) := by
  let includeMap : C(X, E) →+ UniformOnFun X E {K | IsCompact K} :=
    { toFun := ContinuousMap.toUniformOnFunIsCompact
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact IsUniformInducing.isUniformAddGroup includeMap
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing

/-- A closed set of continuous maps is complete for compact convergence if the closure
of its image under evaluation at each point is complete. -/
theorem isComplete_continuousMap_of_isComplete_eval
    {X E : Type*} [TopologicalSpace X] [CompactlyCoherentSpace X] [UniformSpace E]
    {s : Set C(X, E)} (hs : IsClosed s)
    (heval : ∀ x : X, IsComplete (closure ((fun f : C(X, E) ↦ f x) '' s))) :
    IsComplete s := by
  let j : C(E, Completion E) := ⟨(↑), Completion.continuous_coe E⟩
  have hj : IsUniformInducing j := Completion.isUniformInducing_coe E
  let J : C(X, E) → C(X, Completion E) := j.comp
  have hJ : IsUniformInducing J := ContinuousMap.isUniformInducing_comp j hj
  apply hJ.isComplete_iff.mp
  apply IsClosed.isComplete
  rw [← closure_subset_iff_isClosed]
  intro f hf
  -- Point evaluations of a limit still lie in the image of the original target.
  have lifts (x : X) : ∃ y : E, j y = f x := by
    let A := closure ((fun g : C(X, E) ↦ g x) '' s)
    have hA : IsClosed (j '' A) := (hj.isComplete_iff.mpr (heval x)).isClosed
    have hx : f x ∈ j '' A := by
      apply closure_minimal (t := (fun g : C(X, Completion E) ↦ g x) ⁻¹' (j '' A))
        _ (hA.preimage (continuous_eval_const x)) hf
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g x, subset_closure ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨y, _, hy⟩ := hx
    exact ⟨y, hy⟩
  choose g hg using lifts
  let G : C(X, E) := ⟨g, hj.isInducing.continuous_iff.mpr (by
    convert f.continuous using 1
    exact funext hg)⟩
  have hG : J G = f := ContinuousMap.ext hg
  refine ⟨G, ?_, hG⟩
  rw [← hs.closure_eq, hJ.isInducing.closure_eq_preimage_closure_image]
  change J G ∈ closure (J '' s)
  rwa [hG]

end RiemannMasullo
