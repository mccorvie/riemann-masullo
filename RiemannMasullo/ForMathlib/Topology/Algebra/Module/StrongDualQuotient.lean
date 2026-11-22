module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

public section
open Bornology Set Topology
open scoped UniformConvergence
namespace RiemannMasullo

/-- If the strong dual of a space is complete, so is the strong dual of each quotient.
In the space of all functions with bounded convergence, continuity and linearity on the
quotient can both be tested by pulling back to the original space. -/
theorem completeSpace_strongDual_quotient {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup E] [CompleteSpace (StrongDual 𝕜 E)]
    (K : Submodule 𝕜 E) : CompleteSpace (StrongDual 𝕜 (E ⧸ K)) := by
  let A := {s : Set E | IsVonNBounded 𝕜 s}
  let B := {s : Set (E ⧸ K) | IsVonNBounded 𝕜 s}
  let R (f : (E ⧸ K) →ᵤ[B] 𝕜) : E →ᵤ[A] 𝕜 :=
    UniformOnFun.ofFun A (UniformOnFun.toFun B f ∘ K.mkQL)
  have hR : Continuous R :=
    (UniformOnFun.precomp_uniformContinuous (f := K.mkQL) (𝔖 := B) (𝔗 := A) (fun _ hs ↦ hs.image K.mkQL)).continuous
  let ie := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 A
  let iq := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 B
  let : CompleteSpace (UniformConvergenceCLM (RingHom.id 𝕜) 𝕜 A) := inferInstanceAs (CompleteSpace (StrongDual 𝕜 E))
  let : T2Space (E →ᵤ[A] 𝕜) := UniformOnFun.t2Space_of_covering sUnion_isVonNBounded_eq_univ
  have hclosed := ie.isComplete_range.isClosed
  change CompleteSpace (UniformConvergenceCLM (RingHom.id 𝕜) 𝕜 B)
  rw [completeSpace_iff_isComplete_range iq]
  apply IsClosed.isComplete
  convert hclosed.preimage hR using 1
  ext f
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.comp K.mkQL, rfl⟩
  · rintro ⟨l, hl⟩
    have he (x : E) : l x = UniformOnFun.toFun B f (K.mkQ x) :=
      congrArg (fun z : E →ᵤ[A] 𝕜 ↦ UniformOnFun.toFun A z x) hl
    have h0 : UniformOnFun.toFun B f 0 = 0 := by simpa only [map_zero] using (he 0).symm
    have hk : K ≤ l.ker := fun x hx ↦ by
      exact (he x).trans ((congrArg (UniformOnFun.toFun B f) ((Submodule.Quotient.mk_eq_zero K).2 hx)).trans h0)
    refine ⟨K.liftQL l hk, ?_⟩
    apply (UniformOnFun.toFun B).injective
    funext x
    obtain ⟨a, rfl⟩ := K.mkQ_surjective x
    exact he a


variable {E 𝕜 : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E]

/-- The transpose of a quotient has the closed annihilator of the kernel as its range. -/
theorem range_transpose_mkQL (K : Submodule 𝕜 E) :
    range (fun l : StrongDual 𝕜 (E ⧸ K) ↦ l.comp K.mkQL) =
      ⋂ x : K, {l : StrongDual 𝕜 E | l x = 0} := by
  ext l
  rw [mem_iInter]
  constructor
  · rintro ⟨m, rfl⟩ x
    change m (K.mkQ x.val) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr x.property, map_zero]
  · intro hl
    refine ⟨K.liftQL l (fun x hx ↦ hl ⟨x, hx⟩), ?_⟩
    ext x
    rfl

/-- Vanishing on each element of the kernel is a closed condition for bounded convergence. -/
theorem isClosed_range_transpose_mkQL [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] (K : Submodule 𝕜 E) :
    IsClosed (range (fun l : StrongDual 𝕜 (E ⧸ K) ↦ l.comp K.mkQL)) := by
  rw [range_transpose_mkQL]
  exact isClosed_iInter fun x ↦ isClosed_eq (continuous_eval_const x.val) continuous_const

end RiemannMasullo
