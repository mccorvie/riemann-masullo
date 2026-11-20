module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Locally convex topological vector spaces

Masullo, Appendix C, §C.1. The scalars are complex unless the paper specifies real scalars.
We use `PolynormableSpace ℂ E` for the characterization of local convexity by continuous
complex seminorms (§C.1.2.1). Boundedness is von Neumann boundedness.

The elementary notions on pp. 657–658 are Mathlib's `Convex ℝ`, `Balanced ℂ`,
`Absorbent ℂ`, convex and balanced hulls, their closures, and the Minkowski functional `gauge`.
-/

@[expose] public noncomputable section

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum

namespace RiemannMasullo

universe u

/-- Paper: Remark C.1.1.1, p. 657. A circled set is stable under each complex scalar
in the closed unit disc. -/
theorem balanced_iff_closedUnitDisc {E : Type*} [AddCommGroup E] [Module ℂ E] (A : Set E) :
    Balanced ℂ A ↔ ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ x ∈ A, z • x ∈ A :=
  balanced_iff_smul_mem

/-- Paper: Remark C.1.1.2, p. 658. The balanced hull of the closed real hyperbola
has just the origin on the axes, whereas its closure contains both axes. -/
theorem balancedHull_hyperbola :
    let A : Set (ℝ × ℝ) := {p | p.1 * p.2 = 1}
    balancedHull ℝ (closure A) = balancedHull ℝ A ∧
      balancedHull ℝ A = {p | 0 < p.1 * p.2 ∧ p.1 * p.2 ≤ 1} ∪ {0} ∧
      closure (balancedHull ℝ A) = {p | 0 ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ 1} := by sorry

/-- Paper: Remark C.1.2.1, p. 658. The uniformity of a uniform additive group is the
canonical additive uniformity of its topology. -/
theorem uniformSpace_eq_additiveUniformity (E : Type*) [AddCommGroup E] [uE : UniformSpace E]
    [IsUniformAddGroup E] : uE = IsTopologicalAddGroup.rightUniformSpace E := by sorry

/-- Paper: §C.1.2.1, p. 658. In a topology defined by seminorms, positive integer
rescalings of finite intersections of their closed unit balls give a basis at zero.
The topology is Hausdorff exactly when the common kernel is zero. -/
theorem seminorms_nhds_basis_and_hausdorff {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (p : SeminormFamily ℂ E ι) (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun a : Finset ι × ℕ ↦ 0 < a.2)
      (fun a ↦ {x | ∀ i ∈ a.1, p i x ≤ (a.2 : ℝ)⁻¹}) ∧
      (T2Space E ↔ ∀ x : E, (∀ i, p i x = 0) → x = 0) := by sorry

section Nets

variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J K : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  [Preorder K] [Nonempty K] [IsDirectedOrder K]

/-- Paper: Definition C.1.3.1(1–2), p. 659. A net is a function on a nonempty directed
preorder. It converges to a point exactly when its differences from that point are
eventually in every zero-neighborhood. -/
theorem tendsto_net_iff_sub_mem (f : J → E) (x : E) :
    Tendsto f atTop (𝓝 x) ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, x - f j ∈ U := by
  rw [← tendsto_const_sub_iff x, sub_self, tendsto_iff_forall_eventually_mem]
  simp only [eventually_atTop]

/-- Paper: Definition C.1.3.1(3), p. 659. A net is Cauchy when every zero-neighborhood
contains all pairwise differences on some tail. -/
theorem cauchySeq_iff_sub_mem (f : J → E) :
    CauchySeq f ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, ∀ k ≥ j₀, f j - f k ∈ U := by
  rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto, and_iff_right atTop_neBot,
    prod_atTop_atTop_eq, tendsto_iff_forall_eventually_mem]
  simp only [eventually_atTop_prod_self']

/-- Paper: Definition C.1.3.1(3), p. 659. Two Cauchy nets are equivalent when their
difference on the product directed set converges to zero. -/
def EquivalentCauchyNets (f : J → E) (g : K → E) : Prop :=
  CauchySeq f ∧ CauchySeq g ∧ Tendsto (fun p : J × K ↦ f p.1 - g p.2) atTop (𝓝 0)

/-- Paper: Definition C.1.3.1(3), p. 659. Two convergent nets in a Hausdorff space
are equivalent exactly when their limits coincide. -/
theorem equivalentCauchyNets_iff_of_tendsto [T2Space E] {f : J → E} {g : K → E} {x y : E}
    (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y)) :
    EquivalentCauchyNets f g ↔ x = y := by sorry

/-- Paper: Definition C.1.3.1(4), p. 659. For a Hausdorff subset, uniform completeness
means that every Cauchy net with values in it has a limit in it.
Deviation: Nets indexed in the universe of the ambient space suffice to test completeness. -/
theorem isComplete_iff_cauchyNets (A : Set E) [T2Space A] :
    IsComplete A ↔ ∀ (I : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
      (f : I → A), CauchySeq (fun i ↦ (f i : E)) →
        ∃ x ∈ A, Tendsto (fun i ↦ (f i : E)) atTop (𝓝 x) := by sorry

end Nets

/-- Paper: Definition C.1.3.1(5), p. 659. A complex Fréchet space is locally convex,
metrizable, and complete for its additive uniformity. Metrizability includes Hausdorffness. -/
def IsFrechetTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  ∃ h : IsTopologicalAddGroup E, letI := h
    PolynormableSpace ℂ E ∧ MetrizableSpace E ∧
      @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)

/-- Paper: Definition C.1.3.1(5), p. 659. Every complex Banach space is Fréchet. -/
theorem isFrechetTVS_of_banach (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] : IsFrechetTVS E := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := E)]
  infer_instance

-- TODO(paper-gap): The reference for construction of the completion by Cauchy nets is “[?]”.

/-- Paper: Remark C.1.3.2, p. 659. Every Cauchy net has an equivalent net indexed by a
family of subsets of the space ordered by reverse inclusion. -/
theorem exists_equivalentCauchyNets_powerset {E J : Type*} [AddCommGroup E] [UniformSpace E]
    [IsUniformAddGroup E] [Preorder J] [Nonempty J] [IsDirectedOrder J] (f : J → E)
    (hf : CauchySeq f) :
    ∃ (S : Set (Set E)) (_ : Nonempty Sᵒᵈ) (_ : IsDirectedOrder Sᵒᵈ) (g : Sᵒᵈ → E),
      EquivalentCauchyNets f g := by sorry

-- TODO(paper-gap): The arithmetic Schwartz–Bruhat spaces of Remark C.1.3.3 require Appendix D.

/-- Paper: Remark C.1.3.4, p. 660. The quotient of a Fréchet space by a closed linear
subspace is Fréchet in the quotient topology. -/
theorem isFrechetTVS_quotient {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (M : Submodule ℂ E) (hM : IsClosed (M : Set E)) :
    IsFrechetTVS (E ⧸ M) := by sorry

/-- Paper: Remark C.1.3.4, p. 660. A complete Hausdorff locally convex space can have
an incomplete quotient by a closed subspace. Both completeness predicates use the
additive uniformity. -/
theorem exists_incomplete_quotient :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E)
      (_ : IsTopologicalAddGroup E) (_ : PolynormableSpace ℂ E) (_ : T2Space E),
      @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) ∧
        ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧
          ¬ @CompleteSpace (E ⧸ M) (IsTopologicalAddGroup.rightUniformSpace (E ⧸ M)) := by sorry

/-- Paper: §C.1.4, p. 660. A set is bounded when a nonzero complex multiple of it
fits inside every prescribed zero-neighborhood. -/
theorem isVonNBounded_iff_rescale {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ U ∈ 𝓝 (0 : E), ∃ c : ℂ, c ≠ 0 ∧ c • B ⊆ U := by
  constructor
  · intro hB U hU
    obtain ⟨c, hc, hmaps⟩ :=
      (eventually_mem_nhdsWithin.and (hB hU).eventually_nhdsNE_zero).exists
    exact ⟨c, hc, hmaps.image_subset⟩
  · intro hB
    apply (nhds_basis_balanced ℂ E).isVonNBounded_iff.mpr
    rintro U ⟨hU, hbal⟩
    obtain ⟨c, hc, hsub⟩ := hB U hU
    have hinv : B ⊆ c⁻¹ • U := (smul_set_subset_iff₀ hc).mp hsub
    exact Absorbs.of_norm ⟨‖c⁻¹‖, fun d hd ↦ hinv.trans (hbal.smul_mono hd)⟩

/-- Paper: Proposition C.1.4.1, p. 661. A subset of a Hausdorff locally convex space is
bounded exactly when its image under every continuous linear functional is bounded. -/
theorem isVonNBounded_iff_dual_image {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ l : StrongDual ℂ E, IsBounded (l '' B) := by sorry

/-- Paper: Definition C.1.4.2, p. 661. A set is relatively compact if its closure in
the ambient space is compact. -/
def IsRelativelyCompact {E : Type*} [TopologicalSpace E] (A : Set E) : Prop :=
  IsCompact (closure A)

/-- Paper: Definition C.1.4.2, p. 661. A set is precompact if its image in the
completion has compact closure. -/
def IsPrecompactInCompletion {E : Type*} [UniformSpace E] (A : Set E) : Prop :=
  IsRelativelyCompact ((fun x : E ↦ (x : UniformSpace.Completion E)) '' A)

/-- Paper: Definition C.1.4.2, p. 661. Relative compactness of a closed subset of a
Hausdorff space agrees with compactness. -/
theorem isRelativelyCompact_iff_of_isClosed {E : Type*} [TopologicalSpace E] [T2Space E]
    {A : Set E} (hA : IsClosed A) : IsRelativelyCompact A ↔ IsCompact A := by
  rw [IsRelativelyCompact, hA.closure_eq]

/-- Paper: Remark C.1.4.3, p. 661. Compactness of the closure in the completion is
equivalent to total boundedness in the original space. -/
theorem isPrecompactInCompletion_iff_totallyBounded {E : Type*} [UniformSpace E] [T2Space E]
    (A : Set E) : IsPrecompactInCompletion A ↔ TotallyBounded A := by sorry

section Hilbert

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Example C.1.4.4, p. 661. An infinite-dimensional Hilbert space with its
weak topology is incomplete, although its closed bounded subsets are complete (p. 662). -/
theorem weakHilbert_incomplete (hinf : ¬ FiniteDimensional ℂ H) :
    letI := IsTopologicalAddGroup.rightUniformSpace (WeakSpace ℂ H)
    ¬ CompleteSpace (WeakSpace ℂ H) ∧ QuasiCompleteSpace ℂ (WeakSpace ℂ H) := by sorry

/-- Paper: Example C.1.4.5, p. 661. In the strong operator topology on an infinite-dimensional
Hilbert space there is an unbounded Cauchy net without a limit. Closed bounded sets of
operators are nevertheless complete (p. 662). -/
theorem strongOperator_exists_unbounded_cauchy (hinf : ¬ FiniteDimensional ℂ H) :
    let B := H →Lₚₜ[ℂ] H
    letI := IsTopologicalAddGroup.rightUniformSpace B
    QuasiCompleteSpace ℂ B ∧ ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J)
      (_ : IsDirectedOrder J) (f : J → B), CauchySeq f ∧ ¬ IsVonNBounded ℂ (range f) ∧
        ¬ ∃ T, Tendsto f atTop (𝓝 T) := by sorry

/-- Paper: Example C.1.4.6(1–2), p. 662. A separable Hilbert space and the operator-norm
space of bounded endomorphisms of any Hilbert space are quasi-complete. -/
theorem hilbert_quasiComplete_examples :
    (SeparableSpace H → IsFrechetTVS H ∧ QuasiCompleteSpace ℂ H) ∧
      CompleteSpace (H →L[ℂ] H) ∧ QuasiCompleteSpace ℂ (H →L[ℂ] H) := by sorry

end Hilbert

-- TODO(paper-gap): Example C.1.4.6(3) refers to Theorem D.1.5.7 on Schwartz–Bruhat spaces.
-- TODO(paper-gap): Remark C.1.4.7 uses nuclear locally convex spaces from §C.2.4.

section InductiveLimits

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {ι : Type*} {X : ι → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

/-- Paper: §C.1.5, p. 663. The final locally convex topology on a complex vector space
is generated by all seminorms that are continuous on each source. On an algebraic direct
sum or direct limit the maps are the canonical linear maps from its summands or stages. -/
@[instance_reducible]
def locallyConvexFinalTopology (i : ∀ k, X k →ₗ[ℂ] E) : TopologicalSpace E :=
  let p : SeminormFamily ℂ E {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} := Subtype.val
  p.moduleFilterBasis.topology

/-- Paper: §C.1.5, p. 663. For the identity map from a locally convex space the final
locally convex topology recovers the given topology. -/
theorem locallyConvexFinalTopology_id [t : TopologicalSpace E] [PolynormableSpace ℂ E] :
    locallyConvexFinalTopology (X := fun _ : Unit ↦ E) (fun _ ↦ LinearMap.id) = t := by sorry

/-- Paper: Proposition C.1.5.1, p. 664. In a countable locally convex direct sum of
normed spaces, the intersection of suitably rescaled zero-neighborhoods is a zero-neighborhood.
Deviation: Both sequences are indexed starting at zero. -/
theorem exists_rescale_directSum_nhds (Y : ℕ → Type*) [∀ k, NormedAddCommGroup (Y k)]
    [∀ k, NormedSpace ℂ (Y k)] :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
    ∀ V : ℕ → Set (⨁ k, Y k), (∀ k, V k ∈ 𝓝 0) →
      ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧ (⋂ k, (ρ k : ℂ) • V k) ∈ 𝓝 0 := by sorry

end InductiveLimits

section CountableLimits

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

/-- Paper: §C.1.5, p. 664. The maps into the limit identify the algebraic stages with a
rising union, and the limit carries their final locally convex topology. The stage
injections need only be continuous. -/
structure IsInjectiveLCLimit (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E) : Prop where
  injective : ∀ k, Function.Injective (i k)
  compatible : ∀ k, (i (k+1)).comp (j k) = i k
  exhaustive : ∀ x : E, ∃ k, x ∈ range (i k)
  topology_eq : tE = locallyConvexFinalTopology (fun k ↦ (i k).toLinearMap)

/-- Paper: §C.1.5, p. 664. A constant sequence with identity transition maps presents
the original locally convex space as its limit. -/
theorem isInjectiveLCLimit_const [PolynormableSpace ℂ E] :
    IsInjectiveLCLimit (X := fun _ ↦ E) (fun _ ↦ ContinuousLinearMap.id ℂ E)
      (fun _ ↦ ContinuousLinearMap.id ℂ E) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. A strict countable limit of complete Hausdorff
locally convex spaces is complete. If the stages are Fréchet and each inclusion
is proper, the limit is nonmetrizable.
Deviation: Stated here after introducing the inductive limit. -/
theorem strictLCLimit_complete_nonmetrizable [IsTopologicalAddGroup E]
    [∀ k, T2Space (X k)] [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (hc : ∀ k, @CompleteSpace (X k) (IsTopologicalAddGroup.rightUniformSpace (X k)))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) ∧
      ((∀ k, IsFrechetTVS (X k)) → (∀ k, ¬ Function.Surjective (j k)) → ¬ MetrizableSpace E) := by
  sorry

/-- Paper: Definition C.1.5.2, p. 664. An LF-space is Hausdorff and is a countable
locally convex inductive limit of Fréchet spaces.
Deviation: We use the equivalent injective presentation justified just after the definition
by quotienting the stages by the kernels of their maps to the limit. -/
def IsLFSpace (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ (X : ℕ → Type u) (_ : ∀ k, AddCommGroup (X k)) (_ : ∀ k, Module ℂ (X k))
    (_ : ∀ k, TopologicalSpace (X k)), (∀ k, IsFrechetTVS (X k)) ∧
      ∃ (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E), IsInjectiveLCLimit j i

/-- Paper: Example C.1.4.6(4), p. 662. A strict LF-space is exhausted by increasing
Fréchet subspaces and has their final locally convex topology.
Deviation: The stages are their images in the limit with the subspace topology, using
the embedding property stated in the example. -/
def IsStrictLFSpace (E : Type*) [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ S : ℕ → Submodule ℂ E, Monotone S ∧ (∀ k, IsFrechetTVS (S k)) ∧
    (∀ x : E, ∃ k, x ∈ S k) ∧ t = locallyConvexFinalTopology (fun k ↦ (S k).subtype)

/-- Paper: Definition C.1.5.2, p. 664. A Fréchet space is an LF-space via its constant
defining sequence. -/
theorem isLFSpace_of_isFrechetTVS (hE : IsFrechetTVS E) : IsLFSpace E := by sorry

/-- Paper: Example C.1.4.6(4), p. 662. Strict LF-spaces are LF-spaces and a closed
quotient of an LF-space is LF.
Deviation: Hausdorffness in Definition C.1.5.2 requires the subspace defining the
quotient to be closed. -/
theorem lfSpace_quotient_properties :
    (IsStrictLFSpace E → IsLFSpace E) ∧
      (IsLFSpace E → ∀ M : Submodule ℂ E, IsClosed (M : Set E) → IsLFSpace (E ⧸ M)) := by sorry

/-- Paper: Example C.1.4.6(4), p. 663. A Hausdorff quotient of a strict LF-space can
fail to be strict. -/
theorem exists_quotient_not_strictLF :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E),
      IsStrictLFSpace E ∧ ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧
        ¬ IsStrictLFSpace (E ⧸ M) := by sorry

/-- Paper: Proposition C.1.5.3, p. 664. In a strict limit with closed stage embeddings
a subset is bounded exactly when it is the image of a bounded subset of a single stage. -/
theorem isVonNBounded_iff_bounded_stage [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsClosedEmbedding (j k)) (B : Set E) :
    IsVonNBounded ℂ B ↔ ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ i k '' A = B := by sorry

/-- Paper: Lemma C.1.5.4, p. 665. If a Hausdorff topological vector space is exhausted
by rising images of Fréchet spaces under continuous linear injections, every continuous
linear map into it from a Fréchet space factors continuously through one stage.
Deviation: The sequence is indexed starting at zero. -/
theorem frechet_factorization [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    (hX : ∀ k, IsFrechetTVS (X k)) (i : ∀ k, X k →L[ℂ] E) (hi : ∀ k, Function.Injective (i k))
    (hr : ∀ k, range (i k) ⊆ range (i (k+1))) (hcov : ∀ x : E, ∃ k, x ∈ range (i k))
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hF : IsFrechetTVS F)
    (u : F →L[ℂ] E) : ∃ k, ∃ v : F →L[ℂ] X k, (i k).comp v = u := by sorry

-- TODO(paper-gap): On p. 665 the second Baire argument only establishes a dense union.

/-- Paper: Theorem C.1.5.5, p. 665. A continuous linear surjection onto an LF-space
is open if its Hausdorff source is exhausted by rising continuous linear images of
Fréchet spaces. -/
theorem isOpenMap_of_surjective_toLF (hE : IsLFSpace E)
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hX : ∀ k, IsFrechetTVS (X k)) (u : ∀ k, X k →L[ℂ] F)
    (hr : ∀ k, range (u k) ⊆ range (u (k+1))) (hcov : ∀ x : F, ∃ k, x ∈ range (u k))
    (q : F →L[ℂ] E) (hq : Function.Surjective q) : IsOpenMap q := by sorry

/-- Paper: Definition C.1.5.6, p. 666. Take the final locally convex topology on the
subspace from its intersections with the stages. Each intersection has the topology
induced from its own stage. -/
@[instance_reducible]
def limitSubspaceTopology (i : ∀ k, X k →L[ℂ] E) (F : Submodule ℂ E) : TopologicalSpace F :=
  let inclusion (k : ℕ) : F.comap (i k).toLinearMap →ₗ[ℂ] F :=
    (i k).toLinearMap.restrict (fun _ hx ↦ hx)
  locallyConvexFinalTopology inclusion

/-- Paper: Definition C.1.5.6, p. 666. A closed subspace of an LF-space is a limit
subspace if its inherited topology agrees with the locally convex inductive limit
topology from the chosen defining sequence. -/
def IsLimitSubspace (i : ∀ k, X k →L[ℂ] E) (F : Submodule ℂ E) : Prop :=
  IsClosed (F : Set E) ∧ (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F

/-- Paper: Definition C.1.5.6, p. 666. The whole LF-space is a limit subspace for
every injective defining sequence. -/
theorem isLimitSubspace_top [T2Space E] (hX : ∀ k, IsFrechetTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i) :
    IsLimitSubspace i ⊤ := by sorry

/-- Paper: Example C.1.5.7, p. 666. Some countable locally convex direct sum of Banach
spaces has a closed linear subspace which, in its subspace topology, is not an LF-space. -/
theorem exists_closed_subspace_not_LF :
    ∃ (Y : ℕ → Type) (_ : ∀ k, NormedAddCommGroup (Y k)) (_ : ∀ k, NormedSpace ℂ (Y k))
      (_ : ∀ k, CompleteSpace (Y k)),
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
      ∃ F : Submodule ℂ (⨁ k, Y k), IsClosed (F : Set (⨁ k, Y k)) ∧ ¬ IsLFSpace F := by sorry

-- TODO(paper-gap): Footnotes 2–4 on p. 667 leave the explicit Köthe space, the two
-- strong topologies, and the justification for the subspace example unspecified.

/-- Paper: Definition C.1.5.8, p. 667. The map σ on the direct sum is the identity
minus the shift that sends the kth summand to the next one by its transition map. -/
def directSumDifference (j : ∀ k, X k →L[ℂ] X (k+1)) : (⨁ k, X k) →ₗ[ℂ] (⨁ k, X k) :=
  LinearMap.id - DirectSum.toModule ℂ ℕ _ (fun k ↦
    (DirectSum.lof ℂ ℕ X (k+1)).comp (j k).toLinearMap)

/-- Paper: Definition C.1.5.8, p. 667. The zeroth coordinate is unchanged and
coordinate k+1 subtracts the image of coordinate k under the kth transition map. -/
theorem directSumDifference_apply (j : ∀ k, X k →L[ℂ] X (k+1)) (x : ⨁ k, X k) :
    directSumDifference j x 0 = x 0 ∧
      ∀ k, directSumDifference j x (k+1) = x (k+1) - j k (x k) := by sorry

/-- Paper: Definition C.1.5.8, p. 667. A countable system of Hausdorff locally convex
spaces is acyclic when σ is a closed topological embedding of its locally convex direct sum. -/
def IsAcyclicSystem (j : ∀ k, X k →L[ℂ] X (k+1)) : Prop :=
  letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  IsClosedEmbedding (directSumDifference j)

/-- Paper: §C.1.5.1 (after Definition C.1.5.8), p. 667. A strict sequence of Fréchet
spaces is acyclic. -/
theorem isAcyclicSystem_of_strict_frechet (hX : ∀ k, IsFrechetTVS (X k))
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k)) : IsAcyclicSystem j := by sorry

end CountableLimits

section Lifting

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: Definition C.1.5.9, p. 667. A set in the target can be lifted when it is
contained in the image of a bounded set in the source. Such a set is itself bounded. -/
def HasBoundedLift (f : E →L[ℂ] F) (B : Set F) : Prop :=
  ∃ A : Set E, IsVonNBounded ℂ A ∧ B ⊆ f '' A

/-- Paper: Definition C.1.5.9, p. 667. A continuous linear map lifts bounded sets if
each bounded set in its target has a bounded lift. -/
def LiftsBoundedSets (f : E →L[ℂ] F) : Prop :=
  ∀ B : Set F, IsVonNBounded ℂ B → HasBoundedLift f B

/-- Paper: Definition C.1.5.9, p. 667. A bounded lift can be chosen with image exactly
the specified set. -/
theorem hasBoundedLift_iff_image (f : E →L[ℂ] F) (B : Set F) :
    HasBoundedLift f B ↔ ∃ A : Set E, IsVonNBounded ℂ A ∧ f '' A = B := by sorry

/-- Paper: Definition C.1.5.9, p. 667. The identity map lifts bounded subsets. -/
theorem liftsBoundedSets_id : LiftsBoundedSets (ContinuousLinearMap.id ℂ E) := by sorry

end Lifting

/-- Paper: §C.1.5.1 (Schwartz spaces), p. 667. For each continuous seminorm there is
a zero-neighborhood with precompact image in the corresponding normed quotient.
Deviation: A continuous seminorm is the gauge of its closed unit ball. Total boundedness
for its pseudometric expresses precompactness in the Hausdorff normed quotient. -/
def IsSchwartzTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  PolynormableSpace ℂ E ∧ ∀ p : Seminorm ℂ E, Continuous p → ∃ V ∈ 𝓝 (0 : E),
    @TotallyBounded E p.toSeminormedAddCommGroup.toUniformSpace V

/-- Paper: §C.1.5.1 (Schwartz spaces), p. 667. A normed complex space is Schwartz
exactly when it is finite-dimensional.
Deviation: Sanity check using the norm seminorm in the definition. -/
theorem isSchwartzTVS_iff_finiteDimensional (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsSchwartzTVS E ↔ FiniteDimensional ℂ E := by sorry

-- TODO(paper-gap): Example C.1.5.10 requires nuclear locally convex spaces from §C.2.4.

/-- Paper: Theorem C.1.5.11, p. 668. In a strict countable limit of Schwartz Fréchet
spaces, a stepwise closed subspace inherits the limit topology exactly when the quotient
map lifts bounded sets.
Deviation: This is the general form stated immediately after (1)–(2) on the same page.
For a closed subspace, equality of these topologies is the limit subspace condition.
The specialization to nuclear stages uses Example C.1.5.10. -/
theorem limitSubspaceTopology_eq_iff_liftsBoundedSets
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] {X : ℕ → Type*}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)] [∀ k, TopologicalSpace (X k)]
    (hX : ∀ k, IsFrechetTVS (X k)) (hS : ∀ k, IsSchwartzTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) (F : Submodule ℂ E) (hF : ∀ k, IsClosed (i k ⁻¹' (F : Set E))) :
    (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F ↔
      LiftsBoundedSets F.mkQL := by sorry

-- TODO(paper-gap): The sentence after C.1.5.11 reverses the implication of Example C.1.5.10.
-- TODO(paper-gap): Remark C.1.5.12 and Corollary C.1.5.13 require nuclearity from §C.2.4.

section Duality

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
  [∀ k, ContinuousSMul ℂ (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
variable {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E}

/-- Paper: Lemma C.1.6.1, p. 669. Restriction identifies the weak dual of a Hausdorff
inductive limit with the projective limit of the stage weak duals. The same holds for
strong duals if every bounded set comes from a bounded set in one stage.
Deviation: The projective limit is expressed as the compatible families in the product.
Unique extension identifies the image and the embeddings give its subspace topology. -/
theorem dual_of_injectiveLCLimit (h : IsInjectiveLCLimit j i) :
    (∀ l : (k : ℕ) → StrongDual ℂ (X k), (∀ k, (l (k+1)).comp (j k) = l k) →
      ∃! L : StrongDual ℂ E, ∀ k, L.comp (i k) = l k) ∧
    IsEmbedding (fun (L : WeakDual ℂ E) k ↦ StrongDual.toWeakDual (L.toStrongDual.comp (i k))) ∧
    ((∀ B : Set E, IsVonNBounded ℂ B →
      ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ B = i k '' A) →
      IsEmbedding (fun (L : StrongDual ℂ E) k ↦ L.comp (i k))) := by sorry

/-- Paper: Remark C.1.6.2, p. 670. The strong dual has the projective limit topology
exactly when every bounded set is in the closure, in the limit, of the image of a
bounded set in one stage. -/
theorem strongDual_isEmbedding_iff_closure_bounded_stage (h : IsInjectiveLCLimit j i) :
    IsEmbedding (fun (L : StrongDual ℂ E) k ↦ L.comp (i k)) ↔
      ∀ B : Set E, IsVonNBounded ℂ B →
        ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ B ⊆ closure (i k '' A) := by sorry

end Duality

end RiemannMasullo
