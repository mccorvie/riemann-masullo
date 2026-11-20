module

public import RiemannMasullo.AppC_LCTVS.Sec2a
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Topological tensor products

Masullo, Appendix C, §C.2.3. Each tensor product has Mathlib's algebraic tensor product
as carrier, with an explicit family of complex seminorms. Its completion is
`UniformSpace.Completion` for the corresponding additive uniformity.
-/

@[expose] public noncomputable section

open Set Filter Topology TopologicalSpace Bornology UniformSpace TensorProduct
open scoped TensorProduct DirectSum UniformConvergence ComplexOrder

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section Seminorms

variable (X : Type*) [AddCommGroup X] [Module ℂ X] {ι : Type*}

/-- Paper: §C.2.3, p. 676. A type synonym distinguishes vector spaces equipped with
different tensor topologies on the same algebraic carrier. -/
def WithGeneratingSeminorms (_p : SeminormFamily ℂ X ι) := X

variable (p : SeminormFamily ℂ X ι)

instance : AddCommGroup (WithGeneratingSeminorms X p) := inferInstanceAs (AddCommGroup X)

instance : Module ℂ (WithGeneratingSeminorms X p) := inferInstanceAs (Module ℂ X)

instance : TopologicalSpace (WithGeneratingSeminorms X p) := p.moduleFilterBasis.topology

/-- Paper: §C.2.3, p. 676. The specified seminorms generate the topology on the synonym. -/
theorem withGeneratingSeminorms_spec :
    @WithSeminorms ℂ (WithGeneratingSeminorms X p) ι inferInstance inferInstance inferInstance p
      inferInstance := ⟨rfl⟩

instance : PolynormableSpace ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).toPolynormableSpace

instance : IsTopologicalAddGroup (WithGeneratingSeminorms X p) :=
  p.moduleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup

instance : UniformSpace (WithGeneratingSeminorms X p) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (WithGeneratingSeminorms X p) :=
  isUniformAddGroup_of_addCommGroup

end Seminorms

section DualForms

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: (C.2.3.1)–(C.2.3.2), p. 676. The two dual variables determine the
linear functional on tensors obtained by multiplying their evaluations. -/
def tensorDualForm (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) : Module.Dual ℂ (E ⊗[ℂ] F) :=
  TensorProduct.dualDistrib ℂ E F (φ.toLinearMap ⊗ₜ[ℂ] ψ.toLinearMap)

/-- Paper: (C.2.3.2), p. 676. Evaluation on a pure tensor is the product of its two evaluations. -/
theorem tensorDualForm_tmul (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) (x : E) (y : F) :
    tensorDualForm φ ψ (x ⊗ₜ[ℂ] y) = φ x * ψ y := by sorry

variable [hE : PolynormableSpace ℂ E] [sE : T2Space E]
  [hF : PolynormableSpace ℂ F] [sF : T2Space F]

include hE sE hF sF in
/-- Paper: (C.2.3.1), p. 676. Jointly continuous bilinear forms on the two weak duals
are exactly the forms represented by a unique algebraic tensor. -/
theorem tensorDualForm_represents_iff (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ) :
    Continuous (fun p : WeakDual ℂ E × WeakDual ℂ F ↦ B p.1 p.2) ↔
      ∃! z : E ⊗[ℂ] F, ∀ φ ψ, B φ ψ = tensorDualForm φ ψ z := by sorry

/-- Paper: Remark C.2.3.1, p. 676. If closed bounded sets are compact, the Mackey
topology on the dual is the topology of precompact convergence. -/
theorem mackeyDual_eq_precompact {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [PolynormableSpace ℂ X] [T2Space X]
    (h : ∀ A : Set X, IsClosed A → IsVonNBounded ℂ A → IsCompact A) :
    mackeyTopology (topDualPairing ℂ X) =
      polarTopology (topDualPairing ℂ X) {A | TotallyBounded A} := by sorry

-- TODO(later): needs §C.2.4 for the nuclear Montel assertion of Remark C.2.3.1.
-- TODO(later): needs §D.1 for its adelic Schwartz–Bruhat space examples.

include hE sE hF sF in
/-- Paper: (C.2.3.3), p. 676. A separately continuous bilinear form on the weak duals
corresponds to a unique continuous operator from the Mackey dual to F, by evaluation. -/
theorem mackeyDual_represents_separatelyContinuous
    (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ) :
    (∀ φ, Continuous (B φ)) ∧ (∀ ψ, Continuous (B.flip ψ)) ↔
      ∃! T : StrongDual ℂ E →ₗ[ℂ] F,
        @Continuous _ _ (mackeyTopology (topDualPairing ℂ E)) _ T ∧
        ∀ φ ψ, B φ ψ = ψ (T φ) := by sorry

end DualForms

section Injective

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: (C.2.3.7), p. 677. The injective seminorm tests a tensor against pairs
of functionals in the absolute polars of two zero-neighborhoods. -/
def injectiveTensorSeminorm (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) :
    Seminorm ℂ (E ⊗[ℂ] F) :=
  ⨆ φ : StrongDual.polar ℂ U.val, ⨆ ψ : StrongDual.polar ℂ V.val,
    (normSeminorm ℂ ℂ).comp (tensorDualForm φ.val ψ.val)

variable (E F) in
/-- Paper: (C.2.3.4), p. 676. The injective tensor product has the topology of uniform
convergence on products of equicontinuous sets in the two duals, expressed by (C.2.3.7). -/
abbrev InjectiveTensor :=
  WithGeneratingSeminorms (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)

variable [hE : PolynormableSpace ℂ E] [sE : T2Space E]
  [hF : PolynormableSpace ℂ F] [sF : T2Space F]

include hE sE hF sF in
/-- Paper: (C.2.3.4), p. 676. The injective tensor topology is Hausdorff. -/
@[instance]
theorem injectiveTensor_t2 : T2Space (InjectiveTensor E F) := by sorry

include hE sE hF sF in
/-- Paper: (C.2.3.4), p. 676. Evaluation realizes the injective topology as uniform
convergence on products from the equicontinuous compactologies. -/
theorem injectiveTensor_isEmbedding_dualForms :
    let S := image2 Set.prod (equicontinuousCompactology E) (equicontinuousCompactology F)
    IsEmbedding (fun z : InjectiveTensor E F ↦ UniformOnFun.ofFun S
      (fun v : WeakDual ℂ E × WeakDual ℂ F ↦ tensorDualForm v.1 v.2 z)) := by sorry

/-- Paper: Remark C.2.3.2, p. 677. The topology μ tests the extensions of dual
functionals on compact subsets of the additive completion. -/
@[instance_reducible]
def completionCompactDualTopology (X : Type*) [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X] :
    TopologicalSpace (StrongDual ℂ X) :=
  let S : Set (Set (Completion X)) := {K | IsCompact K}
  TopologicalSpace.induced (fun φ : StrongDual ℂ X ↦
    UniformOnFun.ofFun S (φ.fromCompletion : Completion X → ℂ))
    (UniformOnFun.topologicalSpace (Completion X) ℂ S)

section Mu
variable {X : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
  [lc : PolynormableSpace ℂ X] [sep : T2Space X] [complete : CompleteSpace X]

include sep complete in
/-- Paper: Remark C.2.3.2, p. 677. For a complete space, μ equals precompact convergence. -/
theorem completionCompactDualTopology_eq_precompact :
    completionCompactDualTopology X =
      polarTopology (topDualPairing ℂ X) {A | TotallyBounded A} := by sorry

include sep complete in
/-- Paper: Remark C.2.3.2, p. 677. For a complete metrizable space, μ is the finest
locally convex topology agreeing with the weak dual topology on all equicontinuous sets. -/
theorem completionCompactDualTopology_isLeast [met : MetrizableSpace X] :
    IsLeast {t : TopologicalSpace (StrongDual ℂ X) |
      @PolynormableSpace ℂ _ _ _ _ t ∧
      ∀ A : Set (WeakDual ℂ X), EquicontinuousAt (fun φ : A ↦ (φ.val : X → ℂ)) 0 →
        t.induced (fun φ : A ↦ WeakDual.toStrongDual φ.val) = (inferInstance : TopologicalSpace A)}
      (completionCompactDualTopology X) := by sorry
end Mu

/-- Paper: (C.2.3.5)–(C.2.3.6), p. 677. Contracting a tensor against the first
dual variable gives a finite-rank operator from the dual of E to F. -/
def tensorDualOperator : E ⊗[ℂ] F →ₗ[ℂ] StrongDual ℂ E →ₗ[ℂ] F :=
  (dualTensorHom ℂ (StrongDual ℂ E) F).comp
    (TensorProduct.map (topDualPairing ℂ E).flip LinearMap.id)

/-- Paper: (C.2.3.6), p. 677. A pure tensor sends a functional to its value at the
first factor times the second factor. -/
theorem tensorDualOperator_tmul (x : E) (y : F) (φ : StrongDual ℂ E) :
    tensorDualOperator (x ⊗ₜ[ℂ] y) φ = φ x • y := by sorry

include hE sE hF sF in
/-- Paper: Remark C.2.3.2, p. 677. The canonical operator representation is injective. -/
theorem tensorDualOperator_injective : Function.Injective (tensorDualOperator (E := E) (F := F)) :=
  by sorry

/-- Paper: Remark C.2.3.2, p. 677. The operator associated to each tensor has
finite-dimensional image. -/
theorem tensorDualOperator_finiteRank (z : E ⊗[ℂ] F) :
    FiniteDimensional ℂ (LinearMap.range (tensorDualOperator z)) := by sorry

include hE sE in
/-- Paper: Remark C.2.3.2, p. 677. Testing the associated operators on the equicontinuous
compactology gives the injective topology. -/
theorem tensorDualOperator_isEmbedding {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [UniformSpace Y] [IsUniformAddGroup Y] [PolynormableSpace ℂ Y] [T2Space Y] :
    IsEmbedding (fun z : InjectiveTensor E Y ↦ UniformOnFun.ofFun (equicontinuousCompactology E)
      (fun φ : WeakDual ℂ E ↦ tensorDualOperator z φ)) := by sorry

/-- Paper: Remark C.2.3.2, p. 677. Each represented operator is continuous for μ. -/
theorem tensorDualOperator_continuous_mu {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [PolynormableSpace ℂ X] [T2Space X]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] (z : X ⊗[ℂ] F) :
    @Continuous _ F (completionCompactDualTopology X) _ (tensorDualOperator z) := by sorry

-- TODO(paper-gap): For incomplete E, evaluation at a point of its completion can be a
-- μ-continuous rank-one operator outside the image of (C.2.3.5).
-- TODO(paper-gap): Remark C.2.3.3 refers to a Pták open mapping theorem without stating
-- the map, the hypotheses on the target, or the conclusion in full.

include hE hF in
/-- Paper: (C.2.3.7), p. 677. On a given tensor the injective seminorm is the
supremum of the absolute evaluations on the two polars. -/
theorem injectiveTensorSeminorm_apply
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) (z : E ⊗[ℂ] F) :
    injectiveTensorSeminorm U V z =
      ⨆ φ : StrongDual.polar ℂ U.val, ⨆ ψ : StrongDual.polar ℂ V.val,
        ‖tensorDualForm φ.val ψ.val z‖ := by sorry

end Injective

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Paper: Example C.2.3.4, p. 677. For normed factors the injective norm is the
injective seminorm for the two closed unit balls. -/
abbrev injectiveTensorNorm (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] : Seminorm ℂ (E ⊗[ℂ] F) :=
  injectiveTensorSeminorm ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩

/-- Paper: Example C.2.3.4, p. 677. The tensor operator is bounded on the normed dual,
and its operator norm is the injective norm of the tensor. -/
theorem injectiveTensorNorm_eq_opNorm (z : E ⊗[ℂ] F) :
    ∃ T : StrongDual ℂ E →L[ℂ] F, T.toLinearMap = tensorDualOperator z ∧
      injectiveTensorNorm E F z = ‖T‖ := by sorry

/-- Paper: Example C.2.3.4, p. 677. The unit-ball seminorm alone generates the ε-topology. -/
theorem injectiveTensorNorm_withSeminorms :
    WithSeminorms (E := InjectiveTensor E F) (fun _ : Unit ↦ injectiveTensorNorm E F) := by sorry

end Normed

/-- Paper: (C.2.3.9), p. 678. This is Mathlib’s tensor map with its source and target
given the injective topologies. -/
def injectiveTensorMap {E F G H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    (f : E →ₗ[ℂ] G) (g : F →ₗ[ℂ] H) : InjectiveTensor E F →ₗ[ℂ] InjectiveTensor G H :=
  TensorProduct.map f g

section Maps

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [lcE : PolynormableSpace ℂ E] [sE : T2Space E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [lcF : PolynormableSpace ℂ F] [sF : T2Space F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [lcG : PolynormableSpace ℂ G] [sG : T2Space G]
  [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [lcH : PolynormableSpace ℂ H] [sH : T2Space H]
variable (f : E →L[ℂ] G) (g : F →L[ℂ] H)

include lcE lcF lcG lcH sE sF sG sH

/-- Paper: (C.2.3.9), p. 678. The injective tensor map applies its two factors
to the corresponding entries of a pure tensor. -/
theorem injectiveTensorMap_tmul (x : E) (y : F) :
    injectiveTensorMap f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] g y := by sorry

/-- Paper: (C.2.3.9), p. 678. Tensoring two continuous linear maps is continuous
for the injective topologies. -/
theorem injectiveTensorMap_continuous :
    Continuous (injectiveTensorMap f.toLinearMap g.toLinearMap) := by sorry

/-- Paper: Lemma C.2.3.5(1), p. 678. Tensoring two embeddings gives an embedding. -/
theorem injectiveTensorMap_isEmbedding (hf : IsEmbedding f) (hg : IsEmbedding g) :
    IsEmbedding (injectiveTensorMap f.toLinearMap g.toLinearMap) := by sorry

/-- Paper: Lemma C.2.3.5(1), p. 678. The extension to the completions is an embedding. -/
theorem completedInjectiveTensorMap_isEmbedding (hf : IsEmbedding f) (hg : IsEmbedding g) :
    IsEmbedding (Completion.map (injectiveTensorMap f.toLinearMap g.toLinearMap)) := by sorry

/-- Paper: Lemma C.2.3.5(2), p. 678. Tensoring dense embeddings gives a map with dense image. -/
theorem injectiveTensorMap_denseRange (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfd : DenseRange f) (hgd : DenseRange g) :
    DenseRange (injectiveTensorMap f.toLinearMap g.toLinearMap) := by sorry

end Maps

section Isometries

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] H)

/-- Paper: Lemma C.2.3.5(1), p. 678. Tensoring isometric embeddings preserves the injective norm. -/
theorem injectiveTensorMap_isometry (z : E ⊗[ℂ] F) :
    injectiveTensorNorm G H (TensorProduct.map f.toLinearMap g.toLinearMap z) =
      injectiveTensorNorm E F z := by sorry

/-- Paper: Lemma C.2.3.5(1), p. 678. The induced map of the completions in the
injective norms is an isometry. -/
theorem completedInjectiveTensorMap_isometry :
    letI := (injectiveTensorNorm E F).toSeminormedAddCommGroup
    letI := (injectiveTensorNorm G H).toSeminormedAddCommGroup
    Isometry (Completion.map (TensorProduct.map f.toLinearMap g.toLinearMap)) := by sorry

end Isometries

section CompletionFactors

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [lcE : PolynormableSpace ℂ E] [sE : T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [lcF : PolynormableSpace ℂ F] [sF : T2Space F]

include sE sF in
/-- Paper: Lemma C.2.3.5(2), p. 678. Completing the factors induces an isomorphism
on completed injective tensor products. -/
theorem completedInjectiveTensor_completionFactors :
    IsHomeomorph (Completion.map (injectiveTensorMap
      (Completion.toComplL : E →L[ℂ] Completion E).toLinearMap
      (Completion.toComplL : F →L[ℂ] Completion F).toLinearMap)) := by sorry

end CompletionFactors

section Associativity

variable (E F G : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [AddCommGroup G] [Module ℂ G]
  [TopologicalSpace G] [PolynormableSpace ℂ E] [T2Space E] [PolynormableSpace ℂ F] [T2Space F]
  [PolynormableSpace ℂ G] [T2Space G]

/-- Paper: Lemma C.2.3.5(3), p. 678. The algebraic associator is a homeomorphism
between the two iterated injective tensor products. -/
theorem injectiveTensor_assoc :
    @IsHomeomorph (InjectiveTensor (InjectiveTensor E F) G) (InjectiveTensor E (InjectiveTensor F G))
      _ _ (TensorProduct.assoc ℂ E F G) := by sorry

end Associativity

section Products

variable {I J : Type*} (E : I → Type*) (F : J → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] [∀ j, TopologicalSpace (F j)]
  [∀ i, PolynormableSpace ℂ (E i)] [∀ i, T2Space (E i)]
  [∀ j, PolynormableSpace ℂ (F j)] [∀ j, T2Space (F j)]

/-- Paper: Lemma C.2.3.6(1), p. 678. The tensor products of coordinate projections identify
the injective tensor product of finite products with the product of the pairwise tensors. -/
theorem injectiveTensor_finiteProducts [Finite I] [Finite J] :
    IsHomeomorph (fun (z : InjectiveTensor (∀ i, E i) (∀ j, F j)) (ij : I × J) ↦
      injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2) z) := by sorry

/-- Paper: Lemma C.2.3.6(2), p. 678. On completed injective tensor products the
coordinate map is a linear topological isomorphism for arbitrary products. -/
theorem completedInjectiveTensor_products :
    IsHomeomorph (fun (z : Completion (InjectiveTensor (∀ i, E i) (∀ j, F j))) (ij : I × J) ↦
      Completion.map (injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2)) z) := by sorry

end Products

section Projective

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: (C.2.3.14), p. 679. The projective tensor topology is generated by the seminorms
whose pullbacks along the canonical bilinear map are jointly continuous at zero.
Deviation: This seminorm construction realizes the stated universal property. -/
abbrev ProjectiveTensor :=
  WithGeneratingSeminorms (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)

variable {E F} [lcE : PolynormableSpace ℂ E] [sE : T2Space E]
  [lcF : PolynormableSpace ℂ F] [sF : T2Space F]

/-- Paper: (C.2.3.14), p. 679. A linear map out of the projective tensor product is
continuous exactly when its associated bilinear map is jointly continuous. -/
theorem continuous_projectiveTensor_iff {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [PolynormableSpace ℂ G] (T : ProjectiveTensor E F →ₗ[ℂ] G) :
    Continuous T ↔ Continuous (fun v : E × F ↦ T (v.1 ⊗ₜ[ℂ] v.2)) := by sorry

/-- Paper: (C.2.3.15), p. 679. The convex circled hulls of pure tensors from pairs
of basic zero-neighborhoods form a zero-neighborhood basis. -/
theorem projectiveTensor_zero_basis {I J : Type*} {a : I → Prop} {b : J → Prop}
    {U : I → Set E} {V : J → Set F} (hU : (𝓝 0).HasBasis a U) (hV : (𝓝 0).HasBasis b V) :
    (𝓝 (0 : ProjectiveTensor E F)).HasBasis (fun ij : I × J ↦ a ij.1 ∧ b ij.2)
      (fun ij ↦ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) (U ij.1) (V ij.2))) := by sorry

/-- Paper: §C.2.3.2, p. 679. Rebracketing the projective tensor product is a linear
topological isomorphism. -/
theorem projectiveTensor_assoc {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [PolynormableSpace ℂ G] [T2Space G] :
    @IsHomeomorph (ProjectiveTensor (ProjectiveTensor E F) G)
      (ProjectiveTensor E (ProjectiveTensor F G)) _ _ (TensorProduct.assoc ℂ E F G) := by sorry

/-- Paper: §C.2.3.2, p. 679. The projective tensor product of Hausdorff factors is Hausdorff. -/
@[instance]
theorem projectiveTensor_t2 : T2Space (ProjectiveTensor E F) := by sorry

-- TODO(paper-gap): The claimed projective analogue of Lemma C.2.3.5 on p. 679 fails
-- for embeddings. Even finite-dimensional isometric inclusions can lose isometry.

/-- Paper: (C.2.3.16), p. 679. Every member of the completed projective tensor of Fréchet
spaces is an absolutely weighted sum of pure tensors from two null sequences.
Deviation: The sequences are reindexed from zero. -/
theorem completedProjectiveTensor_exists_series (hE : IsFrechetTVS E) (hF : IsFrechetTVS F)
    (z : Completion (ProjectiveTensor E F)) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F), Summable (fun n ↦ ‖c n‖) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasSum (fun n ↦ (Completion.coe' (α := ProjectiveTensor E F) (c n • (x n ⊗ₜ[ℂ] y n)))) z := by sorry

/-- Paper: (C.2.3.16), p. 679. Conversely, every series of the displayed form converges.
Deviation: The sequences are reindexed from zero. -/
theorem completedProjectiveTensor_summable_series (hE : IsFrechetTVS E) (hF : IsFrechetTVS F)
    (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F) (hc : Summable (fun n ↦ ‖c n‖))
    (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 0)) :
    Summable (fun n ↦ (Completion.coe' (α := ProjectiveTensor E F) (c n • (x n ⊗ₜ[ℂ] y n)))) := by sorry

end Projective

/-- Paper: Proposition C.2.3.7, p. 679. Tensoring linear maps gives the algebraic
map underlying the projective tensor map. -/
def projectiveTensorMap {E F G H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    (f : E →ₗ[ℂ] G) (g : F →ₗ[ℂ] H) : ProjectiveTensor E F →ₗ[ℂ] ProjectiveTensor G H :=
  TensorProduct.map f g

section ProjectiveCompletion

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E] [AddCommGroup F] [Module ℂ F] [UniformSpace F]
  [IsUniformAddGroup F] [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: §C.2.3.2, p. 679. Completing the two factors induces an isomorphism on
completed projective tensors. -/
theorem completedProjectiveTensor_completionFactors :
    IsHomeomorph (Completion.map (projectiveTensorMap
      (Completion.toComplL : E →L[ℂ] Completion E).toLinearMap
      (Completion.toComplL : F →L[ℂ] Completion F).toLinearMap)) := by sorry

end ProjectiveCompletion

section ProjectiveQuotients

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] [T2Space G]
  [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [PolynormableSpace ℂ H] [T2Space H]
variable (f : E →L[ℂ] G) (g : F →L[ℂ] H) (hf : IsQuotientMap f) (hg : IsQuotientMap g)

/-- Paper: Proposition C.2.3.7, p. 679. The projective tensor map sends a pure tensor
to the tensor of the two images. -/
theorem projectiveTensorMap_tmul (x : E) (y : F) :
    projectiveTensorMap f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] g y := by sorry

/-- Paper: §C.2.3.2, p. 679. Tensoring continuous linear maps gives a continuous
projective tensor map, hence a map of additive completions. -/
theorem projectiveTensorMap_continuous :
    Continuous (projectiveTensorMap f.toLinearMap g.toLinearMap) := by sorry

include hf hg

/-- Paper: §C.2.3.2, p. 679. Tensoring quotient maps gives a projective quotient map. -/
theorem projectiveTensorMap_isQuotientMap :
    IsQuotientMap (projectiveTensorMap f.toLinearMap g.toLinearMap) := by sorry

/-- Paper: Proposition C.2.3.7, p. 679. The extension to completions is a quotient map
onto its range with the subspace topology. -/
theorem completedProjectiveTensorMap_isQuotientMap_range :
    IsQuotientMap (rangeFactorization (Completion.map
      (projectiveTensorMap f.toLinearMap g.toLinearMap))) := by sorry

/-- Paper: Proposition C.2.3.7, p. 679. If both domains are metrizable, the
completed projective tensor map is surjective. -/
theorem completedProjectiveTensorMap_surjective [MetrizableSpace E] [MetrizableSpace F] :
    Function.Surjective (Completion.map (projectiveTensorMap f.toLinearMap g.toLinearMap)) := by sorry

end ProjectiveQuotients

section Comparison

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ E] [T2Space E]
  [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: §C.2.3.2, p. 679. The identity from the projective to the injective
tensor product is continuous. -/
theorem continuous_projectiveTensor_to_injectiveTensor :
    @Continuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by sorry

-- TODO(later): needs §C.2.4 for equality when either factor is nuclear.

/-- Paper: Remark C.2.3.8, p. 679. The absolute polars of products of equicontinuous
sets of functionals form a basis of zero-neighborhoods, as specified on p. 680. -/
theorem injectiveTensor_zero_basis :
    (𝓝 (0 : InjectiveTensor E F)).HasBasis
      (fun AB : Set (StrongDual ℂ E) × Set (StrongDual ℂ F) ↦
        EquicontinuousAt (fun φ : AB.1 ↦ (φ.val : E → ℂ)) 0 ∧
        EquicontinuousAt (fun ψ : AB.2 ↦ (ψ.val : F → ℂ)) 0)
      (fun AB ↦ {z | ∀ φ ∈ AB.1, ∀ ψ ∈ AB.2, ‖tensorDualForm φ ψ z‖ ≤ 1}) := by sorry

/-- Paper: Remark C.2.3.8, p. 679. An equicontinuous set in the ε-dual is exactly a subset
of the bipolar of the pure functionals from two equicontinuous sets in the factor duals.
Deviation: The bipolar test on p. 680 is written out as two polar inequalities. -/
theorem injectiveTensor_equicontinuous_iff (D : Set (StrongDual ℂ (InjectiveTensor E F))) :
    EquicontinuousAt (fun l : D ↦ (l.val : InjectiveTensor E F → ℂ)) 0 ↔
      ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
        EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 ∧
        EquicontinuousAt (fun ψ : B ↦ (ψ.val : F → ℂ)) 0 ∧
        ∀ l ∈ D, ∀ z : InjectiveTensor E F,
          (∀ φ ∈ A, ∀ ψ ∈ B, ‖tensorDualForm φ ψ z‖ ≤ 1) → ‖l z‖ ≤ 1 := by sorry

end Comparison

section DirectSums

variable {I : Type*} [DecidableEq I] (E : I → Type*) (F : Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, PolynormableSpace ℂ (E i)] [∀ i, T2Space (E i)]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsNormableSpace ℂ F] [T2Space F]

/-- Paper: Proposition C.2.3.9(1), p. 680. With a normable fixed factor the canonical
distributivity map for an arbitrary locally convex direct sum is a homeomorphism. -/
theorem projectiveTensor_directSum :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I E)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I (fun i ↦ ProjectiveTensor (E i) F))
    @IsHomeomorph (⨁ i, ProjectiveTensor (E i) F) (ProjectiveTensor (⨁ i, E i) F)
      _ _ (TensorProduct.directSumLeft ℂ ℂ E F).symm := by sorry

/-- Paper: Proposition C.2.3.9(1), p. 680. The direct sum of the completed tensors is
isomorphic to the completed tensor of the direct sum. Its isomorphism extends the stage maps. -/
theorem completedProjectiveTensor_directSum :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I E)
    let Y := fun i ↦ Completion (ProjectiveTensor (E i) F)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I Y)
    ∃ e : (⨁ i, Y i) ≃L[ℂ] Completion (ProjectiveTensor (⨁ i, E i) F),
      ∀ i (z : Y i), e (DirectSum.lof ℂ I Y i z) =
        Completion.map (projectiveTensorMap (DirectSum.lof ℂ I E i) (LinearMap.id (M := F))) z :=
  by sorry

end DirectSums

section Limits

variable {I : Type*} [Preorder I] [DecidableEq I] {X : I → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]

/-- Paper: (C.2.3.19), p. 680. The algebraic direct limit is given the final locally
convex topology of its canonical stage maps, as in §C.1.5. -/
abbrev lcDirectLimitTopology (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) :=
  locallyConvexFinalTopology (Module.DirectLimit.of ℂ I X f)

/-- Paper: (C.2.3.19), p. 680. A system consisting of a single locally convex
space has that space as its locally convex direct limit. -/
theorem lcDirectLimitTopology_singleton (V : Type*) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [PolynormableSpace ℂ V] :
    let f : ∀ i j : Unit, i ≤ j → V →ₗ[ℂ] V := fun _ _ _ ↦ LinearMap.id
    letI := lcDirectLimitTopology (X := fun _ : Unit ↦ V) f
    IsHomeomorph (Module.DirectLimit.of ℂ Unit (fun _ ↦ V) f ()) := by sorry

variable [Nonempty I] [IsDirectedOrder I] [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
variable (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
  (hf : ∀ i j h, Continuous (f i j h))

include hf in
/-- Paper: Proposition C.2.3.9(2), p. 680. A projective tensor product with a fixed
normable factor commutes with filtered locally convex direct limits. -/
theorem projectiveTensor_directLimit (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [IsNormableSpace ℂ F] [T2Space F] :
    letI := lcDirectLimitTopology f
    letI : ∀ i, TopologicalSpace (X i ⊗[ℂ] F) := fun i ↦
      (inferInstance : TopologicalSpace (ProjectiveTensor (X i) F))
    letI := lcDirectLimitTopology (fun i j h ↦ (f i j h).rTensor F)
    @IsHomeomorph _ (ProjectiveTensor (Module.DirectLimit X f) F)
      _ _ (TensorProduct.fromDirectLimit f F) := by sorry

end Limits

section CountableLimits

variable {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, IsNormableSpace ℂ (X n)] [∀ n, T2Space (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, IsNormableSpace ℂ (Y n)] [∀ n, T2Space (Y n)]

/-- Paper: Proposition C.2.3.10, p. 681. For two countable systems of normable spaces,
the projective topology on the tensor of their limits is final for the pairwise tensor maps.
Deviation: The two topologies are compared on the canonically identified algebraic colimit. -/
theorem projectiveTensor_countableDirectLimits
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h)) :
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    (inferInstance : TopologicalSpace (ProjectiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g))) =
      locallyConvexFinalTopology (fun ij : ℕ × ℕ ↦ projectiveTensorMap
        (Module.DirectLimit.of ℂ ℕ X f ij.1) (Module.DirectLimit.of ℂ ℕ Y g ij.2)) := by sorry

end CountableLimits

section Sequential

variable {E F G : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] [T2Space G]

/-- Paper: Proposition C.2.3.11, p. 681. A separately sequentially continuous bilinear
map is jointly sequentially continuous if the first factor is Fréchet. -/
theorem seqContinuous_bilinear_of_frechet (hE : IsFrechetTVS E) (A : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (h₁ : ∀ y, SeqContinuous (A.flip y)) (h₂ : ∀ x, SeqContinuous (A x)) :
    SeqContinuous (fun v : E × F ↦ A v.1 v.2) := by sorry

-- The proof on p. 682 calls A(x, ·) continuous. The stated sequential continuity
-- already ensures that the image of the convergent sequence in that argument is bounded.

end Sequential

-- TODO(paper-gap): The one-way property before (C.2.3.22) omits separate continuity of the
-- canonical pairing. Even the finest locally convex vector topology satisfies that implication.

section Inductive

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: (C.2.3.22), p. 682. The inductive tensor product has the finest locally convex
topology for which the canonical bilinear map is separately continuous.
Deviation: The seminorms impose separate continuity of the canonical pairing, as needed
for the two-sided mapping property used in Corollary C.2.3.12. -/
abbrev InductiveTensor :=
  WithGeneratingSeminorms (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      (∀ x : E, Continuous (fun y : F ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : F, Continuous (fun x : E ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)

variable {E F} [PolynormableSpace ℂ E] [T2Space E] [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: (C.2.3.22), p. 682. A linear map on the inductive tensor product is continuous
exactly when its associated bilinear map is continuous in each argument. -/
theorem continuous_inductiveTensor_iff {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [PolynormableSpace ℂ G] [T2Space G] (T : InductiveTensor E F →ₗ[ℂ] G) :
    Continuous T ↔ (∀ x : E, Continuous (fun y : F ↦ T (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : F, Continuous (fun x : E ↦ T (x ⊗ₜ[ℂ] y))) := by sorry

/-- Paper: §C.2.3.4, p. 682. The identity from the inductive to the projective tensor
product is continuous. -/
theorem continuous_inductiveTensor_to_projectiveTensor :
    @Continuous (InductiveTensor E F) (ProjectiveTensor E F) _ _ id := by sorry

/-- Paper: (C.2.3.23), p. 682. The inductive tensor topology of Hausdorff factors is Hausdorff. -/
@[instance]
theorem inductiveTensor_t2 : T2Space (InductiveTensor E F) := by sorry

/-- Paper: Corollary C.2.3.12, p. 682. For Fréchet factors the identity from the inductive
to the projective tensor product is a linear topological isomorphism. -/
theorem inductiveTensor_to_projectiveTensor_of_frechet (hE : IsFrechetTVS E) (hF : IsFrechetTVS F) :
    @IsHomeomorph (InductiveTensor E F) (ProjectiveTensor E F) _ _ id := by sorry

/-- Paper: Corollary C.2.3.12, p. 682. The induced identity map on completions is
also a linear topological isomorphism. -/
theorem completedInductiveTensor_to_projectiveTensor_of_frechet
    (hE : IsFrechetTVS E) (hF : IsFrechetTVS F) :
    IsHomeomorph (@Completion.map (InductiveTensor E F) _ (ProjectiveTensor E F) _ id) := by sorry

end Inductive

/-- Paper: (C.2.3.25)–(C.2.3.27), p. 683. The tensor map between inductive tensor products
acts by the given linear maps on the two factors. -/
def inductiveTensorMap {E F G H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    (f : E →ₗ[ℂ] G) (g : F →ₗ[ℂ] H) : InductiveTensor E F →ₗ[ℂ] InductiveTensor G H :=
  TensorProduct.map f g

section InductiveMaps

variable {E F G H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    [PolynormableSpace ℂ E] [PolynormableSpace ℂ F] [PolynormableSpace ℂ G] [PolynormableSpace ℂ H]
    [T2Space E] [T2Space F] [T2Space G] [T2Space H] (f : E →L[ℂ] G) (g : F →L[ℂ] H)

/-- Paper: (C.2.3.25)–(C.2.3.27), p. 683. The inductive tensor map sends a pure
tensor to the tensor of its images. -/
theorem inductiveTensorMap_tmul (x : E) (y : F) :
    inductiveTensorMap f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] g y := by sorry

/-- Paper: (C.2.3.25)–(C.2.3.27), p. 683. The inductive tensor map is continuous
whenever its two factors are, so it induces the indicated maps of completions. -/
theorem inductiveTensorMap_continuous :
    Continuous (inductiveTensorMap f.toLinearMap g.toLinearMap) := by sorry

end InductiveMaps

section InductiveProduct

variable {I : Type*} (X : I → Type*) (F : Type*)
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)] [AddCommGroup F] [Module ℂ F]
  [TopologicalSpace F]

/-- Paper: Proposition C.2.3.13(1), p. 683. Completed inductive tensoring with a Fréchet
space commutes with arbitrary products via the coordinate projections.
Deviation: The unused second index set and family in the printed hypotheses are omitted. -/
theorem completedInductiveTensor_product (hF : IsFrechetTVS F) :
    IsHomeomorph (fun (z : Completion (InductiveTensor (∀ i, X i) F)) i ↦
      Completion.map (inductiveTensorMap (LinearMap.proj i) (LinearMap.id (M := F))) z) := by sorry

end InductiveProduct

section InductiveLimits

variable {I J : Type*} [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J] {X : I → Type*} {Y : J → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
  [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
  [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
variable (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
  (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
  (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h))
  (hX : @T2Space _ (lcDirectLimitTopology f)) (hY : @T2Space _ (lcDirectLimitTopology g))

include hf hg hX hY

/-- Paper: Proposition C.2.3.13(2), p. 683. The inductive tensor topology on two
Hausdorff limits is the locally convex final topology for the pairwise stages.
Deviation: The canonical algebraic identification in (C.2.3.26) is used to compare topologies. -/
theorem inductiveTensor_directLimits :
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    (inferInstance : TopologicalSpace (InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g))) =
      locallyConvexFinalTopology (fun ij : I × J ↦ inductiveTensorMap
        (Module.DirectLimit.of ℂ I X f ij.1) (Module.DirectLimit.of ℂ J Y g ij.2)) := by sorry

/-- Paper: Proposition C.2.3.13(2), p. 683. The subspace spanned by the images of the
completed stages has the final locally convex topology of those stages.
Deviation: The canonical map from their locally convex direct sum is a quotient onto
its range. This expresses the subspace assertion preceding (C.2.3.27). -/
theorem completedInductiveTensor_isQuotientMap_stageSpan :
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    let Z := fun ij : I × J ↦ Completion (InductiveTensor (X ij.1) (Y ij.2))
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ (I × J) Z)
    ∃ T : (⨁ ij, Z ij) →ₗ[ℂ] Completion (InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g)),
      (∀ ij z, T (DirectSum.lof ℂ (I × J) Z ij z) =
        Completion.map (inductiveTensorMap (Module.DirectLimit.of ℂ I X f ij.1)
          (Module.DirectLimit.of ℂ J Y g ij.2)) z) ∧ IsQuotientMap (rangeFactorization T) := by sorry

-- TODO(paper-gap): In (C.2.3.27) the limit of the completed stages can have a nonzero
-- kernel even when both original limits are Hausdorff. See the tail spaces in the report.

/-- Paper: Proposition C.2.3.13(2), p. 683. The images of the completed pairwise
stages have dense union in the completed inductive tensor of the limits. -/
theorem completedInductiveTensor_stages_dense :
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    Dense (⋃ ij : I × J, range (Completion.map (inductiveTensorMap
      (Module.DirectLimit.of ℂ I X f ij.1) (Module.DirectLimit.of ℂ J Y g ij.2)))) := by sorry

-- TODO(later): needs §C.2.4 for the strict nuclear Fréchet case of (C.2.3.27).

end InductiveLimits

section Permanence

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ E] [T2Space E]
  [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: Proposition C.2.3.13(3), p. 683. The completed inductive tensor of two
barrelled spaces is barrelled. -/
theorem completedInductiveTensor_barrelled [BarrelledSpace ℂ E] [BarrelledSpace ℂ F] :
    BarrelledSpace ℂ (Completion (InductiveTensor E F)) := by sorry

-- TODO(paper-gap): The bornological assertion of C.2.3.13(3), with scalar second factor,
-- would make the completion of every bornological space bornological. For a stationary,
-- costationary S in ω₁ containing the successors, C_c(ω₁) restricted to S is bornological
-- for compact convergence, but its completion C_k(S) has a bounded discontinuous tail functional.

end Permanence

-- TODO(later): needs §C.2.4 for Proposition C.2.3.14 (pp. 684–685), including nuclearity
-- of both Fréchet spaces in the embedding and of all the strict countable stages of F.

end RiemannMasullo
