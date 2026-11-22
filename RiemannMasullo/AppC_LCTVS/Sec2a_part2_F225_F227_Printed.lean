module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2

/-! # Appendix C.2.3: printed claims on tensor operators, limits and bornological spaces -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Topology UniformSpace
open scoped TensorProduct

universe u v i j

/-- Paper: Remark C.2.3.2, p. 677. As printed: every finite-rank continuous linear
operator from the dual of a Hausdorff locally convex space with the μ-topology to a Hausdorff
locally convex space with its weak topology is represented by a tensor. This is the
image inclusion omitted by `tensorDualOperator_finiteRank` and
`tensorDualOperator_continuous_mu`. See ERRATA F225. -/
def Printed.tensorDualOperator_represents_finiteRank : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E]
    (F : Type v) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [T2Space F]
    (T : StrongDual ℂ E →ₗ[ℂ] F),
    FiniteDimensional ℂ (LinearMap.range T) →
    @Continuous _ (WeakSpace ℂ F) (completionCompactDualTopology E) _
      (fun φ ↦ toWeakSpace ℂ F (T φ)) →
    ∃ z : E ⊗[ℂ] F, tensorDualOperator z = T

/-- Paper: Remark C.2.3.2, p. 677. Take E to be the finitely supported complex
sequences with the ℓ² norm and F to be ℂ. In the completion of E the vector with
coordinates 2⁻ⁿ, n ≥ 0, defines a rank-one evaluation on E′, μ-continuous by the
singleton compact set. Each tensor with scalar second factor evaluates at a finitely
supported vector. The coordinate functionals distinguish that vector from (2⁻ⁿ). -/
theorem Printed.tensorDualOperator_represents_finiteRank_false :
    ¬ Printed.tensorDualOperator_represents_finiteRank := by
  sorry

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- The map induced on completed inductive tensors by two continuous linear maps. -/
def Printed.completedInductiveTensorMap {E F A B : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    (f : E →L[ℂ] A) (g : F →L[ℂ] B) :
    Completion (InductiveTensor E F) →ₗ[ℂ] Completion (InductiveTensor A B) :=
  let T : InductiveTensor E F →L[ℂ] InductiveTensor A B :=
    ⟨inductiveTensorMap f.toLinearMap g.toLinearMap, inductiveTensorMap_continuous f g⟩
  T.completion.toLinearMap

/-- Paper: Proposition C.2.3.13(2), p. 683. As printed: the canonical map (C.2.3.27)
from the locally convex direct limit of the completed inductive tensor stages to the
completed inductive tensor of the two Hausdorff limits is a topological embedding.
This is the embedding clause. See `completedInductiveTensor_isQuotientMap_stageSpan`,
`completedInductiveTensor_stages_dense` and ERRATA F226. -/
def Printed.completedInductiveTensor_directLimits_isEmbedding : Prop :=
  ∀ (I : Type i) (J : Type j) [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]
    (X : I → Type u) (Y : J → Type v)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h))
    [@T2Space _ (lcDirectLimitTopology f)] [@T2Space _ (lcDirectLimitTopology g)],
    let u := Module.DirectLimit.of ℂ I X f
    let v := Module.DirectLimit.of ℂ J Y g
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    let Z (p : I × J) := Completion (InductiveTensor (X p.1) (Y p.2))
    let transition (p q : I × J) (h : p ≤ q) : Z p →ₗ[ℂ] Z q :=
      Printed.completedInductiveTensorMap
        ⟨f p.1 q.1 h.1, hf p.1 q.1 h.1⟩ ⟨g p.2 q.2 h.2, hg p.2 q.2 h.2⟩
    letI := lcDirectLimitTopology transition
    ∃ T : Module.DirectLimit Z transition →ₗ[ℂ]
        Completion (InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g)),
      (∀ p z, T (Module.DirectLimit.of ℂ (I × J) Z transition p z) =
        Completion.map (inductiveTensorMap (u p.1) (v p.2)) z) ∧ IsEmbedding T

/-- Paper: Proposition C.2.3.13(2), p. 683. Take Xₙ to be the finitely supported
complex sequences with the ℓ² norm modulo the span of the first n coordinate
vectors, with the quotient maps as transitions. Take Y to be the single stage ℂ.
The X-limit and the target are zero. The completed stages are ℓ² modulo the same
coordinate spans, so the class of (2⁻ⁿ) in their limit is nonzero and maps to zero. -/
theorem Printed.completedInductiveTensor_directLimits_isEmbedding_false :
    ¬ Printed.completedInductiveTensor_directLimits_isEmbedding := by
  sorry

/-- A locally convex space is bornological if each seminorm bounded on its von Neumann
bounded sets is continuous. -/
def Printed.IsBornologicalTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] :
    Prop :=
  ∀ p : Seminorm ℂ E, (∀ s : Set E, IsVonNBounded ℂ s → BddAbove (p '' s)) → Continuous p

/-- Paper: Proposition C.2.3.13(3), p. 683. As printed: the completed inductive
tensor product of two Hausdorff bornological locally convex complex spaces is
bornological. This is the bornological half. The barrelled half is
`completedInductiveTensor_barrelled`. See ERRATA F227. -/
def Printed.completedInductiveTensor_bornological : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E]
    (F : Type v) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [T2Space F],
    Printed.IsBornologicalTVS E → Printed.IsBornologicalTVS F →
      Printed.IsBornologicalTVS (Completion (InductiveTensor E F))

/-- Paper: Proposition C.2.3.13(3), p. 683. Let S be stationary in ω₁ with stationary
complement and let X = S ∪ {ω₁} have the subspace topology from ω₁ + 1. Take E = C(X, ℂ)
with compact convergence and F = ℂ. The Lindelöf space X is realcompact, so E is
bornological by the Nachbin–Shirota theorem. Its completion is C(S, ℂ) × ℂ with
compact convergence on S. Each continuous function on S is eventually constant.
The norm of its eventual value is a seminorm bounded on bounded sets, since countably
many stabilization ordinals have a countable supremum. It is discontinuous, since
one can set the function to zero on any prescribed compact set and to one on a tail. -/
theorem Printed.completedInductiveTensor_bornological_false :
    ¬ Printed.completedInductiveTensor_bornological := by
  sorry

end RiemannMasullo
