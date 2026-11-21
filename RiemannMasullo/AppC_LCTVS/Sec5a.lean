module

public import RiemannMasullo.AppC_LCTVS.Sec4
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.Paracompact
public import RiemannMasullo.ForMathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Sets.Compacts
public import RiemannMasullo.ForMathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Data.Finsupp.ToDFinsupp
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Partial
import RiemannMasullo.ForMathlib.Analysis.Calculus.Deriv.Weak
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
import RiemannMasullo.ForMathlib.Topology.Compactness.LocallyCompact
import RiemannMasullo.ForMathlib.Topology.Compactness.Paracompact
import RiemannMasullo.ForMathlib.Topology.ContinuousMap.LocallyConvex
import RiemannMasullo.ForMathlib.Topology.ContinuousMap.Sigma
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.MeanValue
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Vector-valued continuous and differentiable functions

Masullo, Appendix C, §C.5.1. Mathlib supplies topological support, compactly supported
continuous maps as a vector space, and the compact-open topology on continuous maps.
The topology of the compactly supported space is specified explicitly.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped CompactlySupported DirectSum

namespace RiemannMasullo

section CompactSupport

variable {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

-- TODO(paper-gap): The p. 720 preamble infers a continuous one-point extension from
-- boundedness and asserts incompleteness of the scalar compactly supported space for all X.

/-- Paper: Definition C.5.1.1, p. 721. The fixed-support stage consists of compactly
supported continuous maps that vanish off the given compact set. -/
def compactSupportStage (K : Compacts X) : Submodule ℂ C_c(X, E) :=
  ⨅ (x : X) (_ : x ∉ (K : Set X)), LinearMap.ker
    ({ toFun := fun f ↦ f x
       map_add' := fun f g ↦ CompactlySupportedContinuousMap.add_apply x f g
       map_smul' := fun c f ↦ CompactlySupportedContinuousMap.smul_apply c f x } : C_c(X, E) →ₗ[ℂ] E)

/-- Paper: Definition C.5.1.1, p. 721. On a fixed-support stage, uniform convergence
is induced by restriction to the compact set, where the compact-open topology is uniform. -/
@[instance_reducible]
def compactSupportStageTopology (K : Compacts X) :
    TopologicalSpace (compactSupportStage (E := E) K) :=
  TopologicalSpace.induced
    (fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(K : Set X), X))) inferInstance

/-- Paper: Definition C.5.1.1, p. 721. The topology on compactly supported maps is
the final locally convex topology of the compact support stages with uniform convergence. -/
@[instance_reducible]
def compactSupportLCTopology (X E : Type*) [TopologicalSpace X] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] :
    TopologicalSpace C_c(X, E) :=
  letI (K : Compacts X) : TopologicalSpace (compactSupportStage (E := E) K) :=
    compactSupportStageTopology K
  locallyConvexFinalTopology (fun K : Compacts X ↦ (compactSupportStage (E := E) K).subtype)

variable [T2Space X] [LocallyCompactSpace X] [T2Space E] [PolynormableSpace ℂ E]

/-- Paper: Definition C.5.1.1, p. 721. For a compact set in a Hausdorff space, vanishing
off the set is equivalent to having topological support contained in it. -/
theorem mem_compactSupportStage_iff (K : Compacts X) (f : C_c(X, E)) :
    f ∈ compactSupportStage K ↔ tsupport (f : X → E) ⊆ (K : Set X) := by
  rw [tsupport, K.isCompact.isClosed.closure_subset_iff, Function.support_subset_iff']
  simp only [compactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

/-- Paper: Definition C.5.1.1, p. 721. Whole-space restriction on a compact domain
identifies the fixed-support topology with the topology on continuous maps. -/
theorem compactSupportStageTopology_univ [CompactSpace X] :
    let K : Compacts X := ⟨univ, isCompact_univ⟩
    compactSupportStageTopology (E := E) K =
      TopologicalSpace.induced
        (fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) inferInstance := by
  intro K
  let restrictUniv : C(X, E) ≃ₜ C(↥(univ : Set X), E) :=
    (Homeomorph.Set.univ X).symm.arrowCongr (Homeomorph.refl E)
  change TopologicalSpace.induced
    (restrictUniv ∘ fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) _ = _
  rw [← induced_compose, ← restrictUniv.isInducing.eq_induced]

private theorem isEmbedding_compactSupportStage_toContinuousMap (K : Compacts X) :
    letI := compactSupportStageTopology (E := E) K
    IsEmbedding (fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) := by
  let := compactSupportStageTopology (E := E) K
  let inclusion (f : compactSupportStage (E := E) K) := f.val.toContinuousMap
  have hCont : Continuous inclusion := by
    apply ContinuousMap.continuous_compactOpen.mpr
    intro L hL U hU
    let val : ↥(K : Set X) → X := Subtype.val
    let restrict : compactSupportStage (E := E) K → C(↥(K : Set X), E) :=
      fun f ↦ f.val.toContinuousMap.comp ⟨val, continuous_subtype_val⟩
    have hRestrict : Continuous restrict := continuous_induced_dom
    have hPreimage : IsCompact (val ⁻¹' L) :=
      K.isCompact.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hL
    have hZero (f : compactSupportStage (E := E) K) {x : X} (hx : x ∉ (K : Set X)) :
        f.val x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hs ↦
        hx ((mem_compactSupportStage_iff K f.val).mp f.property hs)
    -- Off the supporting set, the compact-open condition only tests the value zero.
    have hMapsTo (f : compactSupportStage (E := E) K) :
        MapsTo (inclusion f) L U ↔
          MapsTo (restrict f) (val ⁻¹' L) U ∧
            ∀ x ∈ L, x ∉ (K : Set X) → (0 : E) ∈ U := by
      constructor
      · intro hf
        refine ⟨fun x hx ↦ hf hx, fun x hx hxK ↦ ?_⟩
        rw [← hZero f hxK]
        exact hf hx
      · rintro ⟨hf, hOutside⟩ x hx
        change f.val x ∈ U
        by_cases hxK : x ∈ (K : Set X)
        · exact hf (show ⟨x, hxK⟩ ∈ val ⁻¹' L from hx)
        · rw [hZero f hxK]
          exact hOutside x hx hxK
    simp_rw [hMapsTo]
    exact ((ContinuousMap.isOpen_setOfPred_mapsTo hPreimage hU).preimage hRestrict).inter
      isOpen_const
  let val : C(↥(K : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨IsInducing.of_comp hCont (ContinuousMap.continuous_precomp val) ⟨rfl⟩, ?_⟩
  intro f g h
  exact Subtype.ext (DFunLike.ext _ _ fun x ↦ congrArg (fun u : C(X, E) ↦ u x) h)

/-- Paper: Definition C.5.1.1, p. 721. For compact X, the inductive limit topology
agrees with the topology induced by the inclusion into continuous maps. -/
theorem compactSupportLCTopology_of_compact [CompactSpace X] :
    compactSupportLCTopology X E =
      TopologicalSpace.induced (CompactlySupportedContinuousMap.toContinuousMap :
        C_c(X, E) → C(X, E)) inferInstance := by
  let inclusion : C_c(X, E) →ₗ[ℂ] C(X, E) :=
    { toFun := CompactlySupportedContinuousMap.toContinuousMap
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let : TopologicalSpace C_c(X, E) := induced inclusion inferInstance
  let := polynormableSpace_continuousMap ℂ X E
  let : PolynormableSpace ℂ C_c(X, E) := PolynormableSpace.induced inclusion
  let (K : Compacts X) := compactSupportStageTopology (E := E) K
  have hStage (K : Compacts X) : Continuous (compactSupportStage (E := E) K).subtype :=
    continuous_induced_rng.mpr (isEmbedding_compactSupportStage_toContinuousMap (E := E) K).continuous
  -- Every map belongs to the whole-space stage.
  let K : Compacts X := ⟨univ, isCompact_univ⟩
  let lift : C_c(X, E) → compactSupportStage (E := E) K :=
    fun f ↦ ⟨f, (mem_compactSupportStage_iff K f).mpr (subset_univ _)⟩
  have hLift : Continuous lift := by
    change Continuous[_, compactSupportStageTopology (E := E) K] lift
    rw [compactSupportStageTopology_univ]
    exact continuous_induced_rng.mpr continuous_induced_dom
  have hContinuous : (fun p : Seminorm ℂ C_c(X, E) ↦
      ∀ K, Continuous (p ∘ (compactSupportStage (E := E) K).subtype)) =
      (fun p : Seminorm ℂ C_c(X, E) ↦ Continuous p) := by
    funext p
    exact propext ⟨fun hp ↦ (hp K).comp hLift, fun hp K ↦ hp.comp (hStage K)⟩
  change (SeminormFamily.moduleFilterBasis
    (Subtype.val : {p : Seminorm ℂ C_c(X, E) //
      ∀ K, Continuous (p ∘ (compactSupportStage (E := E) K).subtype)} → _)).topology =
    induced inclusion inferInstance
  rw [hContinuous]
  exact (PolynormableSpace.withSeminorms ℂ C_c(X, E)).withSeminorms_eq.symm

section

omit [T2Space X] [LocallyCompactSpace X] [T2Space E]

omit [PolynormableSpace ℂ E] in
private theorem continuous_of_continuous_comp_compactSupportStage
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    (f : C_c(X, E) →ₗ[ℂ] F)
    (hf : ∀ K : Compacts X, Continuous[compactSupportStageTopology (E := E) K, _]
      (f ∘ (compactSupportStage (E := E) K).subtype)) :
    Continuous[compactSupportLCTopology X E, _] f := by
  let := compactSupportLCTopology X E
  let (K : Compacts X) := compactSupportStageTopology (E := E) K
  let P : SeminormFamily ℂ C_c(X, E)
      {p : Seminorm ℂ C_c(X, E) // ∀ K : Compacts X,
        Continuous (p ∘ (compactSupportStage (E := E) K).subtype)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have := hP.isTopologicalAddGroup
  apply (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp
  intro p
  exact hP.continuous_seminorm ⟨p.val.comp f, fun K ↦ p.property.comp (hf K)⟩

omit [PolynormableSpace ℂ E] in
private theorem continuous_compactSupportStage_eval (K : Compacts X) (x : X) :
    Continuous[compactSupportStageTopology (E := E) K, _]
      (fun f : compactSupportStage (E := E) K ↦ f.val x) := by
  let := compactSupportStageTopology (E := E) K
  by_cases hx : x ∈ (K : Set X)
  · let restrict (f : compactSupportStage (E := E) K) : C(↥(K : Set X), E) :=
      f.val.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
    have hr : Continuous restrict := continuous_induced_dom
    exact (continuous_eval_const (⟨x, hx⟩ : ↥(K : Set X))).comp hr
  · apply continuous_const.congr
    intro f
    have hf := f.property
    simp only [compactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker] at hf
    exact (hf x hx).symm

private theorem continuous_compactSupport_eval (x : X) :
    Continuous[compactSupportLCTopology X E, _] (fun f : C_c(X, E) ↦ f x) := by
  let ev : C_c(X, E) →ₗ[ℂ] E :=
    { toFun := fun f ↦ f x
      map_add' := fun f g ↦ CompactlySupportedContinuousMap.add_apply x f g
      map_smul' := fun c f ↦ CompactlySupportedContinuousMap.smul_apply c f x }
  exact continuous_of_continuous_comp_compactSupportStage ev
    (fun K ↦ continuous_compactSupportStage_eval K x)

end

/-- Paper: Definition C.5.1.1, p. 721. Continuous seminorms generate the locally
convex inductive limit topology on compactly supported maps. -/
theorem compactSupportLCTopology_polynormable :
    letI := compactSupportLCTopology X E
    PolynormableSpace ℂ C_c(X, E) := by
  let := compactSupportLCTopology X E
  let (K : Compacts X) := compactSupportStageTopology (E := E) K
  let P : SeminormFamily ℂ C_c(X, E)
      {p : Seminorm ℂ C_c(X, E) // ∀ K : Compacts X,
        Continuous (p ∘ (compactSupportStage (E := E) K).subtype)} := Subtype.val
  exact (show WithSeminorms P from ⟨rfl⟩).toPolynormableSpace

/-- Paper: Lemma C.5.1.3(1), p. 721. The inductive limit topology on compactly supported
continuous maps is Hausdorff. -/
theorem compactSupportLCTopology_t2 :
    @T2Space C_c(X, E) (compactSupportLCTopology X E) := by
  let := compactSupportLCTopology X E
  exact T2Space.of_injective_continuous (f := fun f : C_c(X, E) ↦ (f : X → E))
    DFunLike.coe_injective (continuous_pi fun x ↦ continuous_compactSupport_eval x)

private theorem continuous_compactSupport_toContinuousMap :
    Continuous[compactSupportLCTopology X E, _]
      (CompactlySupportedContinuousMap.toContinuousMap : C_c(X, E) → C(X, E)) := by
  let (K : Compacts X) := compactSupportStageTopology (E := E) K
  let := polynormableSpace_continuousMap ℂ X E
  let inclusion : C_c(X, E) →ₗ[ℂ] C(X, E) :=
    { toFun := CompactlySupportedContinuousMap.toContinuousMap
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact continuous_of_continuous_comp_compactSupportStage inclusion
    (fun K ↦ (isEmbedding_compactSupportStage_toContinuousMap (E := E) K).continuous)

/-- Paper: Lemma C.5.1.3(1), p. 721. The fixed-support stage embeds with its
uniform-convergence topology into the inductive limit. -/
theorem isEmbedding_compactSupportStage (K : Compacts X) :
    letI := compactSupportLCTopology X E
    letI := compactSupportStageTopology (E := E) K
    IsEmbedding ((compactSupportStage (E := E) K).subtype : _ → C_c(X, E)) := by
  let := compactSupportLCTopology X E
  let (L : Compacts X) := compactSupportStageTopology (E := E) L
  let restrict : compactSupportStage (E := E) K →ₗ[ℂ] C(↥(K : Set X), E) :=
    { toFun := fun f ↦ f.val.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have := isTopologicalAddGroup_induced restrict
  let P : SeminormFamily ℂ C_c(X, E)
      {p : Seminorm ℂ C_c(X, E) // ∀ L : Compacts X,
        Continuous (p ∘ (compactSupportStage (E := E) L).subtype)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  refine IsEmbedding.of_comp (hP.continuous_of_continuous_comp _ fun p ↦ p.property K)
    (continuous_compactSupport_toContinuousMap (X := X) (E := E)) ?_
  exact isEmbedding_compactSupportStage_toContinuousMap K

/-- Paper: Lemma C.5.1.3(1), p. 721. The continuous maps supported in a fixed compact
set form a closed subset in the inductive limit topology. -/
theorem isClosed_compactSupportStage (K : Compacts X) :
    letI := compactSupportLCTopology X E
    IsClosed (compactSupportStage (E := E) K : Set C_c(X, E)) := by
  let := compactSupportLCTopology X E
  simp only [compactSupportStage, Submodule.coe_iInf]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_compactSupport_eval (E := E) x) continuous_const

private theorem continuous_compactSupport_of_mem_stage {A : Type*} [TopologicalSpace A]
    (f : A → C_c(X, E)) (K : Compacts X) (hK : ∀ a, f a ∈ compactSupportStage K)
    (hf : Continuous (fun a ↦ (f a).toContinuousMap)) :
    Continuous[_, compactSupportLCTopology X E] f := by
  let := compactSupportLCTopology X E
  let := compactSupportStageTopology (E := E) K
  let lift (a : A) : compactSupportStage (E := E) K := ⟨f a, hK a⟩
  have hlift : Continuous lift :=
    (isEmbedding_compactSupportStage_toContinuousMap (E := E) K).isInducing.continuous_iff.mpr hf
  exact (isEmbedding_compactSupportStage (E := E) K).continuous.comp hlift

omit [T2Space X] [LocallyCompactSpace X] [T2Space E] [PolynormableSpace ℂ E] in
private theorem mem_compactSupportStage_iff_eq_zero (K : Compacts X) (f : C_c(X, E)) :
    f ∈ compactSupportStage K ↔ ∀ x ∉ (K : Set X), f x = 0 := by
  simp only [compactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

private theorem continuous_compactSupport_sigma_restrict_stage {I : Type*} (Y : I → Type*)
    [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, LocallyCompactSpace (Y i)]
    (K : Compacts (Σ i, Y i)) (i : I) (r : compactSupportStage (E := E) K → C_c(Y i, E))
    (hr : ∀ f y, r f y = f.val ⟨i, y⟩) :
    Continuous[compactSupportStageTopology K, compactSupportLCTopology (Y i) E] r := by
  let := compactSupportStageTopology (E := E) K
  let L : Compacts (Y i) := ⟨Sigma.mk i ⁻¹' (K : Set (Σ j, Y j)),
    IsClosedEmbedding.sigmaMk.isCompact_preimage K.isCompact⟩
  apply continuous_compactSupport_of_mem_stage r L
  · intro f
    apply (mem_compactSupportStage_iff_eq_zero L _).2
    intro y hy
    rw [hr]
    exact (mem_compactSupportStage_iff_eq_zero K _).1 f.property _ hy
  · have hc := (ContinuousMap.continuous_precomp
      (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, (Σ j, Y j)))).comp
        (isEmbedding_compactSupportStage_toContinuousMap (E := E) K).continuous
    exact hc.congr fun f ↦ ContinuousMap.ext fun y ↦ (hr f y).symm

private theorem continuous_compactSupport_sigma_single {I : Type*} (Y : I → Type*)
    [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, LocallyCompactSpace (Y i)]
    (j : I) (T : C_c(Y j, E) →ₗ[ℂ] C_c((Σ i, Y i), E))
    (hsame : ∀ f y, T f ⟨j, y⟩ = f y)
    (hother : ∀ f i, i ≠ j → ∀ y, T f ⟨i, y⟩ = 0) :
    Continuous[compactSupportLCTopology (Y j) E, compactSupportLCTopology (Σ i, Y i) E] T := by
  let := compactSupportLCTopology (Σ i, Y i) E
  have := compactSupportLCTopology_polynormable (X := Σ i, Y i) (E := E)
  apply continuous_of_continuous_comp_compactSupportStage
  intro K
  let := compactSupportStageTopology (E := E) K
  let L : Compacts (Σ i, Y i) :=
    ⟨Sigma.mk j '' (K : Set (Y j)), K.isCompact.image continuous_sigmaMk⟩
  apply continuous_compactSupport_of_mem_stage _ L
  · intro f
    apply (mem_compactSupportStage_iff_eq_zero L _).2
    rintro ⟨i, y⟩ hy
    by_cases hij : i = j
    · subst i
      rw [Function.comp_apply, hsame]
      exact (mem_compactSupportStage_iff_eq_zero K _).1 f.property y (fun h ↦ hy ⟨y, h, rfl⟩)
    · exact hother f.val i hij y
  · apply continuous_continuousMap_sigma_of_components
    intro i
    by_cases hij : i = j
    · subst i
      apply (isEmbedding_compactSupportStage_toContinuousMap (E := E) K).continuous.congr
      intro f
      exact ContinuousMap.ext fun y ↦ (hsame f.val y).symm
    · apply (continuous_const (y := (0 : C(Y i, E)))).congr
      intro f
      exact ContinuousMap.ext fun y ↦ (hother f.val i hij y).symm

/-- Paper: Lemma C.5.1.3(2), p. 721. Restriction to each summand identifies compactly
supported maps on a topological disjoint union with the locally convex direct sum. -/
theorem compactSupport_sigma {I : Type*} (Y : I → Type*) [∀ i, TopologicalSpace (Y i)]
    [∀ i, T2Space (Y i)] [∀ i, LocallyCompactSpace (Y i)] :
    letI := compactSupportLCTopology (Σ i, Y i) E
    letI (i : I) := compactSupportLCTopology (Y i) E
    letI : DecidableEq I := Classical.decEq I
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I (fun i ↦ C_c(Y i, E)))
    ∃ e : C_c((Σ i, Y i), E) ≃L[ℂ] (⨁ i, C_c(Y i, E)),
      ∀ f i y, (e f i) y = f ⟨i, y⟩ := by
  classical
  let := compactSupportLCTopology (Σ i, Y i) E
  let (i : I) := compactSupportLCTopology (Y i) E
  let D := ⨁ i, C_c(Y i, E)
  let lof := DirectSum.lof ℂ I (fun i ↦ C_c(Y i, E))
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  let P : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ lof i)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have := hP.toPolynormableSpace
  have := hP.isTopologicalAddGroup
  let (i : I) := compactSupportLCTopology_polynormable (X := Y i) (E := E)
  let (i : I) := PolynormableSpace.isTopologicalAddGroup ℂ C_c(Y i, E)
  have hlof (i : I) : Continuous (lof i) := hP.continuous_of_continuous_comp _ fun p ↦ p.property i
  obtain ⟨e, he⟩ := exists_compactSupport_sigma_linearEquiv ℂ Y E
  have forward : Continuous e := by
    apply continuous_of_continuous_comp_compactSupportStage e.toLinearMap
    intro K
    let := compactSupportStageTopology (E := E) K
    obtain ⟨s, t, hs, _, hst⟩ := K.isCompact.sigma_exists_finite_sigma_eq
    -- A compact stage meets only finitely many components.
    have hsupp (f : compactSupportStage (E := E) K) : (e f.val).support ⊆ hs.toFinset := by
      intro i hi
      by_contra hout
      apply DFinsupp.mem_support_iff.mp hi
      apply DFunLike.ext
      intro y
      rw [he]
      apply (mem_compactSupportStage_iff_eq_zero K _).1 f.property
      exact fun hk ↦ hout (hs.mem_toFinset.mpr ((hst.symm ▸ hk : ⟨i, y⟩ ∈ s.sigma t).1))
    apply (continuous_finsetSum hs.toFinset (fun i _ ↦ (hlof i).comp
      (continuous_compactSupport_sigma_restrict_stage Y K i (fun f ↦ e f.val i)
        (fun f y ↦ he f.val i y)))).congr
    intro f
    calc
      ∑ i ∈ hs.toFinset, lof i (e f.val i) =
          ∑ i ∈ (e f.val).support, lof i (e f.val i) :=
        (Finset.sum_subset (hsupp f) (fun i _ hi ↦ by
          rw [DFinsupp.notMem_support_iff.mp hi, map_zero])).symm
      _ = e f.val := DirectSum.sum_support_of _
  have hinv (g : D) (i : I) (y : Y i) : e.symm g ⟨i, y⟩ = g i y := by
    rw [← he, e.apply_symm_apply]
  have backward : Continuous e.symm := by
    have := compactSupportLCTopology_polynormable (X := Σ i, Y i) (E := E)
    apply (PolynormableSpace.withSeminorms ℂ C_c((Σ i, Y i), E)).continuous_of_continuous_comp
      e.symm.toLinearMap
    intro p
    apply hP.continuous_seminorm ⟨p.val.comp e.symm.toLinearMap, fun j ↦ ?_⟩
    apply p.property.comp (continuous_compactSupport_sigma_single Y j
      (e.symm.toLinearMap.comp (lof j)) (fun f y ↦ ?_) (fun f i hi y ↦ ?_))
    · change e.symm (lof j f) ⟨j, y⟩ = f y
      rw [hinv, DirectSum.lof_apply]
    · change e.symm (lof j f) ⟨i, y⟩ = 0
      rw [hinv, show lof j f i = 0 from DFinsupp.single_eq_of_ne hi]
      rfl
  exact ⟨⟨e, forward, backward⟩, he⟩

omit [T2Space X] [LocallyCompactSpace X] [T2Space E] [PolynormableSpace ℂ E] in
/-- Along a sequence visiting each compact set finitely often, a single continuous seminorm
dominates any prescribed sequence of continuous evaluation seminorms. -/
private theorem exists_compactSupport_seminorm_dominating_evals (x : ℕ → X)
    (hx : ∀ K : Set X, IsCompact K → (x ⁻¹' K).Finite)
    (q : ℕ → Seminorm ℂ E) (hq : ∀ n, Continuous (q n)) :
    ∃ Q : Seminorm ℂ C_c(X, E), Continuous[compactSupportLCTopology X E, _] Q ∧
      ∀ (f : C_c(X, E)) n, q n (f (x n)) ≤ Q f := by
  classical
  let := compactSupportLCTopology X E
  let (K : Compacts X) := compactSupportStageTopology (E := E) K
  have hfin (f : C_c(X, E)) : (support fun n ↦ f (x n)).Finite :=
    (hx _ f.hasCompactSupport).subset fun _ hn ↦ subset_tsupport f hn
  -- Compact support makes the evaluation sequence a vector in the algebraic direct sum.
  let v : C_c(X, E) →ₗ[ℂ] (⨁ _ : ℕ, E) :=
    { toFun := fun f ↦ (Finsupp.ofSupportFinite _ (hfin f)).toDFinsupp
      map_add' := fun f g ↦ DFinsupp.ext fun n ↦ CompactlySupportedContinuousMap.add_apply _ f g
      map_smul' := fun c f ↦ DFinsupp.ext fun n ↦ CompactlySupportedContinuousMap.smul_apply c f _ }
  let Q := (directSumSeminorm q).comp v
  let P : SeminormFamily ℂ C_c(X, E)
      {p : Seminorm ℂ C_c(X, E) // ∀ K : Compacts X,
        Continuous (p ∘ (compactSupportStage (E := E) K).subtype)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  refine ⟨Q, hP.continuous_seminorm ⟨Q, fun K ↦ ?_⟩, fun f n ↦ ?_⟩
  · let s := (hx K K.isCompact).toFinset
    have hs (f : compactSupportStage (E := E) K) : (v f.val).support ⊆ s := by
      intro n hn
      apply (hx K K.isCompact).mem_toFinset.mpr
      by_contra hout
      have hf := f.property
      simp only [compactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker] at hf
      exact (DFinsupp.mem_support_iff.mp hn) (hf (x n) hout)
    apply (continuous_finsetSum s fun n _ ↦
      (hq n).comp (continuous_compactSupportStage_eval K (x n))).congr
    exact fun f ↦ (directSumSeminorm_apply q (v f.val) s (hs f)).symm
  · change q n ((v f) n) ≤ directSumSeminorm q (v f)
    simpa only [Finset.sum_singleton] using sum_le_directSumSeminorm q (v f) {n}

/-- Paper: Lemma C.5.1.3(4), p. 721. For a paracompact domain, the supports of all maps
in a bounded family in the inductive limit lie in a single compact set. -/
theorem compactSupport_bounded_subset_stage [ParacompactSpace X] :
    letI := compactSupportLCTopology X E
    ∀ B : Set C_c(X, E), IsVonNBounded ℂ B →
      ∃ K : Compacts X, B ⊆ (compactSupportStage (E := E) K : Set C_c(X, E)) := by
  classical
  let := compactSupportLCTopology X E
  let := compactSupportLCTopology_polynormable (X := X) (E := E)
  intro B hB
  by_contra hstage
  let S := {x : X | ∃ f ∈ B, f x ≠ 0}
  have hS (K : Set X) (hK : IsCompact K) : ¬ S ⊆ K := by
    intro hSK
    apply hstage
    refine ⟨⟨K, hK⟩, fun f hf ↦ ?_⟩
    apply (mem_compactSupportStage_iff _ f).mpr
    exact hK.isClosed.closure_subset_iff.mpr fun y hy ↦ hSK ⟨f, hf, hy⟩
  obtain ⟨x, hxS, hx⟩ := exists_seq_finite_preimage_of_not_subset_compact hS
  choose f hf hfx using hxS
  -- Normalize a separating seminorm to reach n on the nth selected function.
  have hsep (n : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧ (n : ℝ) ≤ q (f n (x n)) := by
    obtain ⟨p, hp⟩ := (PolynormableSpace.withSeminorms ℂ E).separating_of_T1 _ (hfx n)
    have hpos : 0 < p.val (f n (x n)) := lt_of_le_of_ne (apply_nonneg _ _) hp.symm
    let w : NNReal := ⟨(n : ℝ) / p.val (f n (x n)), div_nonneg (Nat.cast_nonneg n) hpos.le⟩
    refine ⟨w • p.val, ?_, ?_⟩
    · exact (continuous_const.mul p.property : Continuous (fun z ↦ (w : ℝ) * p.val z))
    · change (n : ℝ) ≤ ((n : ℝ) / p.val (f n (x n))) * p.val (f n (x n))
      rw [div_mul_cancel₀ _ hpos.ne']
  choose q hq hlarge using hsep
  obtain ⟨Q, hQ, hdom⟩ := exists_compactSupport_seminorm_dominating_evals x hx q hq
  have hbounded := (PolynormableSpace.withSeminorms ℂ C_c(X, E)).isVonNBounded_iff_seminorm_bounded.mp hB
  obtain ⟨R, _, hR⟩ := hbounded ⟨Q, hQ⟩
  obtain ⟨n, hn⟩ := exists_nat_gt R
  exact (not_lt_of_ge hn.le) (((hlarge n).trans (hdom (f n) n)).trans_lt (hR (f n) (hf n)))

/-- Paper: Lemma C.5.1.3(5), p. 721. Compactly supported continuous maps are dense
among continuous maps for the compact-open topology. -/
theorem denseRange_compactSupport_toContinuousMap :
    DenseRange (CompactlySupportedContinuousMap.toContinuousMap : C_c(X, E) → C(X, E)) := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact denseRange_toContinuousMap_of_real_smul

/-- Paper: Lemma C.5.1.3(6), p. 721. The compact-open continuous-map space of a
quasi-complete locally convex target has its topology generated by continuous seminorms. -/
theorem continuousMap_polynormable :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → PolynormableSpace ℂ C(X, E) := by
  intro _
  exact polynormableSpace_continuousMap ℂ X E

/-- Paper: Lemma C.5.1.3(6), p. 721. The compact-open continuous-map space of a
quasi-complete locally convex target is quasi-complete. Mathlib supplies Hausdorffness. -/
theorem continuousMap_quasiComplete :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → QuasiCompleteSpace ℂ C(X, E) := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  intro hE
  refine ⟨fun {s} hb hs ↦ isComplete_continuousMap_of_isComplete_eval hs fun x ↦ ?_⟩
  exact hE.quasiComplete (hb.image (ContinuousMap.evalCLM ℂ x)).closure isClosed_closure

private theorem isClosed_range_compactSupportStage_toContinuousMap (K : Compacts X) :
    IsClosed (range fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) := by
  have hrange : (range fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) =
      {f : C(X, E) | MapsTo f (K : Set X)ᶜ {0}} := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩ x hx
      have hs := (mem_compactSupportStage_iff K g.val).mp g.property
      exact image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h)
    · intro hf
      have hs : tsupport f ⊆ (K : Set X) := by
        rw [tsupport, K.isCompact.isClosed.closure_subset_iff, Function.support_subset_iff']
        exact fun x hx ↦ hf hx
      let g : C_c(X, E) := ⟨f, K.isCompact.of_isClosed_subset (isClosed_tsupport f) hs⟩
      exact ⟨⟨g, (mem_compactSupportStage_iff K g).mpr hs⟩, rfl⟩
  rw [hrange]
  exact ContinuousMap.isClosed_setOfPred_mapsTo isClosed_singleton _

/-- Paper: Lemma C.5.1.3(3), p. 721. For a paracompact domain and quasi-complete
target, the inductive limit of compact support stages is quasi-complete. -/
theorem compactSupport_quasiComplete [ParacompactSpace X] :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    letI := compactSupportLCTopology X E
    letI := compactSupportLCTopology_polynormable (X := X) (E := E)
    letI := PolynormableSpace.isTopologicalAddGroup ℂ C_c(X, E)
    letI := IsTopologicalAddGroup.rightUniformSpace C_c(X, E)
    QuasiCompleteSpace ℂ E → QuasiCompleteSpace ℂ C_c(X, E) := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have := isUniformAddGroup_continuousMap X E
  let := compactSupportLCTopology X E
  let := compactSupportLCTopology_polynormable (X := X) (E := E)
  let := PolynormableSpace.isTopologicalAddGroup ℂ C_c(X, E)
  let := IsTopologicalAddGroup.rightUniformSpace C_c(X, E)
  have : IsUniformAddGroup C_c(X, E) := isUniformAddGroup_of_addCommGroup
  intro hE
  refine ⟨fun {B} hb hclosed ↦ ?_⟩
  obtain ⟨K, hK⟩ := compactSupport_bounded_subset_stage B hb
  let inclusion : C_c(X, E) →L[ℂ] C(X, E) :=
    { toFun := CompactlySupportedContinuousMap.toContinuousMap
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_compactSupport_toContinuousMap }
  let stage := compactSupportStage (E := E) K
  have : IsUniformAddGroup stage := .comap stage.subtype
  let j := inclusion.toLinearMap.comp stage.subtype
  have hj : IsClosedEmbedding j := by
    refine ⟨?_, isClosed_range_compactSupportStage_toContinuousMap K⟩
    change @IsEmbedding _ _ (induced stage.subtype (compactSupportLCTopology X E)) _ j
    have ht : compactSupportStageTopology (E := E) K =
        induced stage.subtype (compactSupportLCTopology X E) := by
      let := compactSupportStageTopology (E := E) K
      exact (isEmbedding_compactSupportStage (E := E) K).isInducing.eq_induced
    rw [← ht]
    exact isEmbedding_compactSupportStage_toContinuousMap K
  let S : Set stage := Subtype.val ⁻¹' B
  have hS : Subtype.val '' S = B := Subtype.coe_image_of_subset hK
  have hjS : j '' S = inclusion '' B := by
    rw [← hS, image_image]
    rfl
  have complete : IsComplete (j '' S) := (continuousMap_quasiComplete hE).quasiComplete
    (hjS ▸ hb.image inclusion) (hj.isClosedMap _ (hclosed.preimage continuous_subtype_val))
  rw [← hS]
  exact Subtype.isComplete_iff.mp ((AddMonoidHom.isUniformInducing_of_isInducing
    (f := j) hj.isInducing).isComplete_iff.mp complete)

/-- Paper: Example C.5.1.5, p. 722. Positive integer translates of a nonzero continuous
map supported in the unit interval converge to zero in the compact-open topology.
Deviation: The same formulation covers the scalar example and its Fréchet-valued version. -/
theorem compactSupport_translate_tendsto_compactOpen (f : C_c(ℝ, E)) (hf : f ≠ 0)
    (hK : tsupport (f : ℝ → E) ⊆ Icc 0 1)
    (g : ℕ → C_c(ℝ, E)) (hg : ∀ n x, g n x = f (x - n)) :
    Tendsto (fun n ↦ (g n).toContinuousMap) atTop (𝓝 0) := by
  apply ContinuousMap.tendsto_nhds_compactOpen.mpr
  intro K hcompact U _ hU
  obtain ⟨R, hR⟩ := hcompact.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  have hneg : x - n < 0 := sub_neg.mpr ((hR hx).trans_lt (hN.trans_le (Nat.cast_le.mpr hn)))
  have hout : x - n ∉ tsupport (f : ℝ → E) := fun hs ↦ hneg.not_ge (hK hs).1
  change g n x ∈ U
  rw [hg, image_eq_zero_of_notMem_tsupport hout]
  exact hU hx

/-- Paper: Example C.5.1.5, p. 722. Positive integer translates of a nonzero continuous
map supported in the unit interval have no limit in the inductive limit topology.
Deviation: The same formulation covers the scalar example and its Fréchet-valued version. -/
theorem compactSupport_translate_no_inductiveLimit (hE : IsFrechetTVS E)
    (f : C_c(ℝ, E)) (hf : f ≠ 0) (hK : tsupport (f : ℝ → E) ⊆ Icc 0 1)
    (g : ℕ → C_c(ℝ, E)) (hg : ∀ n x, g n x = f (x - n)) :
    letI := compactSupportLCTopology ℝ E
    ¬ ∃ a : C_c(ℝ, E), Tendsto g atTop (𝓝 a) := by
  let := compactSupportLCTopology ℝ E
  let := compactSupportLCTopology_polynormable (X := ℝ) (E := E)
  let := PolynormableSpace.isTopologicalAddGroup ℂ C_c(ℝ, E)
  rintro ⟨a, ha⟩
  obtain ⟨K, hKr⟩ := compactSupport_bounded_subset_stage (range g) (ha.isVonNBounded_range ℂ)
  obtain ⟨R, hR⟩ := K.isCompact.bddAbove
  obtain ⟨y, hy⟩ : ∃ y : ℝ, f y ≠ 0 := by
    by_contra! h
    exact hf (CompactlySupportedContinuousMap.ext h)
  have hy0 : 0 ≤ y := (hK (subset_tsupport f hy)).1
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hnz : g n (y + n) ≠ 0 := by simpa only [hg, add_sub_cancel_right] using hy
  have hmem := (mem_compactSupportStage_iff K (g n)).mp (hKr (mem_range_self n))
    (subset_tsupport (g n) hnz)
  exact (hn.trans_le (le_add_of_nonneg_left hy0)).not_ge (hR hmem)

-- TODO(paper-gap): The last sentence of Example C.5.1.5 extends the distinction to
-- compact manifolds, where the two topologies agree.

end CompactSupport

section Differentials

variable {k V E : Type*} [RCLike k] [NormedAlgebra k ℂ]
  [NormedAddCommGroup V] [NormedSpace k V]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local instance : Module k (PettisWeakCompletion E) :=
  Module.compHom (PettisWeakCompletion E) (algebraMap k ℂ)

/-- Paper: Definition C.5.1.6, p. 723. Weak differentiability means that every
continuous complex-linear functional gives a scalar differentiable function.
Deviation: The definitions also accept a general normed source over the base field. -/
def WeaklyDifferentiableOn (k : Type*) [RCLike k] [NormedAlgebra k ℂ]
    [NormedSpace k V] (f : V → E) (Ω : Set V) : Prop :=
  ∀ φ : StrongDual ℂ E, DifferentiableOn k (φ ∘ f) Ω

/-- Paper: Definition C.5.1.6, p. 723. A weak differential represents all scalar
differentials when evaluated on continuous complex-linear functionals.
Deviation: The differential is specified by its graph property on an ambient function. -/
def HasWeakDifferentialOn (k : Type*) [RCLike k] [NormedAlgebra k ℂ]
    [NormedSpace k V] {Ω : Set V} (f : V → E) (D : Ω × V → PettisWeakCompletion E) : Prop :=
  ∀ (φ : StrongDual ℂ E) (x : Ω), ∃ L : V →L[k] ℂ,
    HasFDerivWithinAt (φ ∘ f) L Ω x ∧
      ∀ v, (show Module.Dual ℂ (StrongDual ℂ E) from D (x, v)) φ = L v

/-- Paper: Definition C.5.1.6, p. 723. Weak continuous differentiability requires a
weak differential that is jointly continuous for the pointwise topology of the weak completion. -/
def WeaklyContDiffOn (k : Type*) [RCLike k] [NormedAlgebra k ℂ]
    [NormedSpace k V] (f : V → E) (Ω : Set V) : Prop :=
  ∃ D : Ω × V → PettisWeakCompletion E, HasWeakDifferentialOn k f D ∧ Continuous D

/-- Paper: Definition C.5.1.6, p. 723. On an open set, weak differentiability is
equivalent to existence of a unique weak differential. -/
theorem weaklyDifferentiableOn_iff_existsUnique {Ω : Set V} (hΩ : IsOpen Ω) (f : V → E) :
    WeaklyDifferentiableOn k f Ω ↔
      ∃! D : Ω × V → PettisWeakCompletion E, HasWeakDifferentialOn k f D := by
  constructor
  · intro hf
    let D (p : Ω × V) : Module.Dual ℂ (StrongDual ℂ E) :=
      { toFun := fun φ ↦ fderivWithin k (φ ∘ f) Ω p.1 p.2
        map_add' := fun φ ψ ↦ by
          change fderivWithin k ((φ ∘ f) + (ψ ∘ f)) Ω p.1 p.2 = _
          rw [fderivWithin_add (hΩ.uniqueDiffOn p.1 p.1.property)
            (hf φ p.1 p.1.property) (hf ψ p.1 p.1.property)]
          rfl
        map_smul' := fun c φ ↦ by
          change fderivWithin k (c • (φ ∘ f)) Ω p.1 p.2 = _
          rw [fderivWithin_const_smul (hΩ.uniqueDiffOn p.1 p.1.property)
            (hf φ p.1 p.1.property)]
          rfl }
    refine ⟨D, fun φ x ↦ ⟨_, (hf φ x x.property).hasFDerivWithinAt, fun _ ↦ rfl⟩, ?_⟩
    intro D' hD'
    funext ⟨x, v⟩
    apply LinearMap.ext
    intro φ
    obtain ⟨L, hL, heval⟩ := hD' φ x
    rw [heval, ← hL.fderivWithin (hΩ.uniqueDiffOn x x.property)]
    rfl
  · rintro ⟨D, hD, _⟩ φ x hx
    obtain ⟨L, hL, _⟩ := hD φ ⟨x, hx⟩
    exact hL.differentiableWithinAt

/-- Paper: Definition C.5.1.6, p. 723. Weak continuous differentiability on an open
set means continuous differentiability of each scalar evaluation.
The source is finite-dimensional, as in the paper (k^d): for an infinite-dimensional normed
source, joint continuity of the scalar derivatives does not give continuity in operator norm. -/
theorem weaklyContDiffOn_iff_scalar [FiniteDimensional k V] {Ω : Set V} (hΩ : IsOpen Ω)
    (f : V → E) :
    WeaklyContDiffOn k f Ω ↔ ∀ φ : StrongDual ℂ E, ContDiffOn k 1 (φ ∘ f) Ω := by
  have hEval {D : Ω × V → PettisWeakCompletion E}
      (hD : HasWeakDifferentialOn k f D) (φ : StrongDual ℂ E) (x : Ω) (v : V) :
      (WeakBilin.eval _ φ : PettisWeakCompletion E →L[ℂ] ℂ) (D (x, v)) =
        fderivWithin k (φ ∘ f) Ω x v := by
    obtain ⟨L, hL, heval⟩ := hD φ x
    rw [hL.fderivWithin (hΩ.uniqueDiffOn x x.property)]
    exact heval v
  constructor
  · rintro ⟨D, hD, hDc⟩ φ
    have hDiff : DifferentiableOn k (φ ∘ f) Ω := by
      intro x hx
      obtain ⟨_, hL, _⟩ := hD φ ⟨x, hx⟩
      exact hL.differentiableWithinAt
    have hCont : ContinuousOn (fderivWithin k (φ ∘ f) Ω) Ω := by
      apply continuousOn_clm_apply.mpr
      intro v
      apply continuousOn_iff_continuous_domRestrict.mpr
      change Continuous (fun x : Ω ↦ fderivWithin k (φ ∘ f) Ω x v)
      let ev : PettisWeakCompletion E →L[ℂ] ℂ := WeakBilin.eval _ φ
      exact (ev.continuous.comp (hDc.comp (continuous_id.prodMk continuous_const))).congr
        (fun x ↦ hEval hD φ x v)
    simpa using (contDiffOn_succ_iff_fderivWithin (n := 0) hΩ.uniqueDiffOn).2
      ⟨hDiff, by simp, contDiffOn_zero.mpr hCont⟩
  · intro hf
    have hDiff : WeaklyDifferentiableOn k f Ω := fun φ ↦ (hf φ).differentiableOn (by simp)
    obtain ⟨D, hD, _⟩ := (weaklyDifferentiableOn_iff_existsUnique hΩ f).mp hDiff
    refine ⟨D, hD, WeakBilin.continuous_of_continuous_eval _ ?_⟩
    intro φ
    have hCont : Continuous (fun x : Ω ↦ fderivWithin k (φ ∘ f) Ω x) :=
      continuousOn_iff_continuous_domRestrict.mp
        ((hf φ).continuousOn_fderivWithin hΩ.uniqueDiffOn le_rfl)
    exact ((hCont.comp continuous_fst).clm_apply continuous_snd).congr
      (fun p ↦ (hEval hD φ p.1 p.2).symm)

/-- Paper: Definition C.5.1.8(1), p. 724. The continuous differential in the weak
completion is linear in the direction and has a vanishing normalized remainder there. -/
def HasWeakCompletionDifferentialOn {Ω : Set V} (f : V → E)
    (D : Ω × V → PettisWeakCompletion E) : Prop :=
  Continuous D ∧ ∀ x : Ω,
    (∃ L : V →ₗ[k] PettisWeakCompletion E, ∀ v, D (x, v) = L v) ∧
    Tendsto (fun y : V ↦ ((‖y - (x : V)‖⁻¹ : ℝ) : ℂ) •
      (toPettisWeakCompletion E (f y) - toPettisWeakCompletion E (f x) - D (x, y - (x : V))))
      (𝓝[Ω \ {(x : V)}] (x : V)) (𝓝 0)

/-- Paper: Definition C.5.1.8(2), p. 724. Weak directional derivatives are the limits
of directional difference quotients on the punctured line inside the domain. -/
def HasWeakDirectionalDerivativesOn {Ω : Set V} (f : V → E)
    (D : Ω × V → PettisWeakCompletion E) : Prop :=
  ∀ (x : Ω) (v : V),
    Tendsto (fun h : k ↦ algebraMap k ℂ h⁻¹ •
      toPettisWeakCompletion E (f ((x : V) + h • v) - f x))
      (𝓝[{h : k | h ≠ 0 ∧ (x : V) + h • v ∈ Ω}] 0) (𝓝 (D (x, v)))

/-- Paper: Definition C.5.1.8(2), p. 724. Gâteaux differentiability in the weak
completion means that every directional limit exists there. -/
def WeakGateauxDifferentiableOn (Ω : Set V) (f : V → E) : Prop :=
  ∃ D : Ω × V → PettisWeakCompletion E, HasWeakDirectionalDerivativesOn (k := k) f D

/-- Paper: Definition C.5.1.8(3), p. 724. A strong continuous differential is a
jointly continuous vector-valued lift of the differential in the weak completion. -/
def HasStrongDifferentialOn {Ω : Set V} (f : V → E) (D : Ω × V → E) : Prop :=
  Continuous D ∧ HasWeakCompletionDifferentialOn (k := k) f (toPettisWeakCompletion E ∘ D)

/-- Paper: Definition C.5.1.8(3), p. 724. Strong continuous differentiability means
that such a differential exists and takes values in the original space. -/
def VectorContDiffOn (Ω : Set V) (f : V → E) : Prop :=
  ∃ D : Ω × V → E, HasStrongDifferentialOn (k := k) f D

/-- Paper: Definition C.5.1.8, p. 724. The identity on the complex line has the
identity differential and the expected directional limits in the weak completion. -/
theorem vectorDifferentials_complex_id :
    let D : ↥(univ : Set ℂ) × ℂ → PettisWeakCompletion ℂ :=
      fun xv ↦ toPettisWeakCompletion ℂ xv.2
    HasWeakCompletionDifferentialOn (k := ℂ) id D ∧
      HasWeakDirectionalDerivativesOn (k := ℂ) id D ∧
      WeakGateauxDifferentiableOn (k := ℂ) univ (id : ℂ → ℂ) ∧
      HasStrongDifferentialOn (k := ℂ) (Ω := (univ : Set ℂ)) id Prod.snd ∧
      VectorContDiffOn (k := ℂ) univ (id : ℂ → ℂ) := by
  let L := toPettisWeakCompletion ℂ
  let D (p : ↥(univ : Set ℂ) × ℂ) := L p.2
  have hc : HasWeakCompletionDifferentialOn (k := ℂ) id D := by
    refine ⟨(continuous_toPettisWeakCompletion (E := ℂ)).comp continuous_snd, fun x ↦ ?_⟩
    refine ⟨⟨L, fun _ ↦ rfl⟩, ?_⟩
    simpa [D, L, map_sub] using
      (tendsto_const_nhds (x := (0 : PettisWeakCompletion ℂ))
        (f := 𝓝[(univ : Set ℂ) \ {(x : ℂ)}] (x : ℂ)))
  have hd : HasWeakDirectionalDerivativesOn (k := ℂ) id D := by
    intro x v
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hn : h ≠ 0 := hh.1
    change L v = algebraMap ℂ ℂ h⁻¹ • L ((x : ℂ) + h • v - x)
    rw [add_sub_cancel_left, map_smul]
    exact (inv_smul_smul₀ hn (L v)).symm
  have hs : HasStrongDifferentialOn (k := ℂ) (Ω := (univ : Set ℂ)) id Prod.snd :=
    ⟨continuous_snd, hc⟩
  exact ⟨hc, hd, ⟨D, hd⟩, hs, ⟨Prod.snd, hs⟩⟩

variable {d : ℕ}

local notation "W" => EuclideanSpace k (Fin d)

/-- Paper: Lemma C.5.1.12, p. 725. The scalar weak differential and the differential
from the weak-completion remainder agree, with the same continuously varying values.
Deviation: In (C.5.1.14) the base point is the first argument and the direction the second. -/
theorem hasWeakCompletionDifferentialOn_iff {Ω : Set W} (hΩ : IsOpen Ω) (f : W → E)
    (D : Ω × W → PettisWeakCompletion E) :
    HasWeakCompletionDifferentialOn (k := k) f D ↔
      HasWeakDifferentialOn k f D ∧ Continuous D := by
  let ev (φ : StrongDual ℂ E) : PettisWeakCompletion E →ₗ[k] ℂ :=
    { toFun := fun z ↦ (show Module.Dual ℂ (StrongDual ℂ E) from z) φ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c z ↦ by
        change algebraMap k ℂ c * _ = c • _
        rw [Algebra.smul_def] }
  let rem (x : Ω) (y : W) : PettisWeakCompletion E :=
    ((‖y - (x : W)‖⁻¹ : ℝ) : ℂ) •
      (toPettisWeakCompletion E (f y) - toPettisWeakCompletion E (f x) - D (x, y - (x : W)))
  have scalar (x : Ω) (φ : StrongDual ℂ E) (L : W →L[k] ℂ)
      (heval : ∀ v, ev φ (D (x, v)) = L v) :
      HasFDerivWithinAt (φ ∘ f) L Ω x ↔
        Tendsto (fun y ↦ ev φ (rem x y)) (𝓝[Ω \ {(x : W)}] (x : W)) (𝓝 0) := by
    rw [← hasFDerivWithinAt_sdiff_singleton_self, hasFDerivWithinAt_iff_tendsto]
    conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
    change _ ↔ Tendsto (fun y ↦ ‖((‖y - (x : W)‖⁻¹ : ℝ) : ℂ) *
      (φ (f y) - φ (f x) - ev φ (D (x, y - (x : W))))‖) _ _
    simp only [heval, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), Function.comp_apply]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨fun φ x ↦ ?_, hc⟩
    obtain ⟨⟨A, hA⟩, hrem⟩ := h x
    let L : W →L[k] ℂ := ((ev φ).comp A).toContinuousLinearMap
    have heval (v : W) : ev φ (D (x, v)) = L v := by
      rw [hA]
      rfl
    refine ⟨L, (scalar x φ L heval).2 ?_, heval⟩
    exact ((WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).1 hrem) φ
  · rintro ⟨h, hc⟩
    refine ⟨hc, fun x ↦ ?_⟩
    have eval_eq (φ : StrongDual ℂ E) (v : W) :
        ev φ (D (x, v)) = fderivWithin k (φ ∘ f) Ω x v := by
      obtain ⟨L, hL, heval⟩ := h φ x
      rw [hL.fderivWithin (hΩ.uniqueDiffOn x x.property)]
      exact heval v
    constructor
    · refine ⟨{ toFun := fun v ↦ D (x, v)
                map_add' := fun v w ↦ ?_
                map_smul' := fun c v ↦ ?_ }, fun _ ↦ rfl⟩
      · apply LinearMap.ext
        intro φ
        change ev φ (D (x, v + w)) = ev φ (D (x, v) + D (x, w))
        rw [map_add, eval_eq, eval_eq, eval_eq, map_add]
      · apply LinearMap.ext
        intro φ
        change ev φ (D (x, c • v)) = algebraMap k ℂ c * ev φ (D (x, v))
        rw [eval_eq, eval_eq, map_smul, Algebra.smul_def]
    · apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).2
      intro φ
      obtain ⟨L, hL, heval⟩ := h φ x
      exact (scalar x φ L heval).1 hL

/-- Paper: Lemma C.5.1.12, p. 725. A continuous differential in the weak completion
gives the weak Gâteaux derivatives, with derivative zero in the zero direction. -/
theorem HasWeakCompletionDifferentialOn.hasWeakDirectionalDerivativesOn {Ω : Set W}
    (hΩ : IsOpen Ω) {f : W → E} {D : Ω × W → PettisWeakCompletion E}
    (hD : HasWeakCompletionDifferentialOn (k := k) f D) :
    HasWeakDirectionalDerivativesOn (k := k) f D := by
  intro x v
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).2
  intro φ
  obtain ⟨L, hL, heval⟩ := ((hasWeakCompletionDifferentialOn_iff hΩ f D).1 hD).1 φ x
  have hline := ((hL.hasFDerivAt (hΩ.mem_nhds x.property)).hasLineDerivAt v).tendsto_slope_zero
  have hfilter : 𝓝[{h : k | h ≠ 0 ∧ (x : W) + h • v ∈ Ω}] 0 ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono _ fun _ ht ↦ ht.1
  change Tendsto (fun h : k ↦ algebraMap k ℂ h⁻¹ * φ (f ((x : W) + h • v) - f x))
    _ (𝓝 ((show Module.Dual ℂ (StrongDual ℂ E) from D (x, v)) φ))
  rw [heval]
  simpa only [Function.comp_apply, Algebra.smul_def, map_sub] using hline.mono_left hfilter

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

-- TODO(paper-gap): C.5.1.13(1) gives one bounded set of quotients on all of Ω.
-- The scalar map x ↦ x² on ℝ contradicts (C.5.1.19).

/-- Paper: Lemma C.5.1.13(1), p. 726. A weakly continuously differentiable
vector-valued map is continuous for the given topology.
Deviation: Only the continuity consequence holds on an arbitrary open domain. -/
theorem WeaklyContDiffOn.continuousOn {Ω : Set W} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : W → E}
    (hf : WeaklyContDiffOn k f Ω) : ContinuousOn f Ω := by
  obtain ⟨D, hD, _⟩ := hf
  intro x hx
  apply Filter.tendsto_of_seq_tendsto
  intro u hu
  have hux : Tendsto u atTop (𝓝 x) := hu.mono_right nhdsWithin_le_nhds
  let r (n : ℕ) : ℂ := ‖u n - x‖
  let q (n : ℕ) := (r n)⁻¹ • (f (u n) - f x)
  have hr (n : ℕ) : ‖r n‖ = ‖u n - x‖ := by
    simp [r]
  -- Each scalar derivative bounds the normalized increments along the sequence.
  have hq : IsVonNBounded ℂ (range q) := by
    apply (isVonNBounded_iff_dual_image _).2
    intro φ
    obtain ⟨L, hL, _⟩ := hD φ ⟨x, hx⟩
    obtain ⟨C, hC, hbound⟩ := (hL.hasFDerivAt (hΩ.mem_nhds hx)).isBigO_sub.exists_pos
    have hev : ∀ᶠ n in atTop, ‖φ (q n)‖ ≤ C := by
      filter_upwards [hux.eventually hbound.bound] with n hn
      simp only [q, map_smul, map_sub, norm_smul, norm_inv, hr]
      by_cases hzero : u n = x
      · simp [hzero, hC.le]
      · have hpos : 0 < ‖u n - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
        exact (inv_mul_le_iff₀ hpos).mpr (by simpa [mul_comm, Function.comp_apply] using hn)
    obtain ⟨M, hM⟩ := (isBoundedUnder_of_eventually_le hev).bddAbove_range
    refine isBounded_iff_forall_norm_le.mpr ⟨M, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact hM (mem_range_self n)
  have hrt : Tendsto r atTop (𝓝 0) := by
    have hz : Tendsto (fun n ↦ ‖u n - x‖) atTop (𝓝 0) := by
      simpa using (hux.sub (tendsto_const_nhds (x := x))).norm
    simpa [r, Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hz
  apply tendsto_sub_nhds_zero_iff.mp
  apply (hq.smul_tendsto_zero (Eventually.of_forall fun n ↦ mem_range_self n) hrt).congr
  intro n
  change r n • ((r n)⁻¹ • (f (u n) - f x)) = f (u n) - f x
  by_cases hn : u n = x
  · simp [hn]
  · exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn))) _

/-- Paper: Lemma C.5.1.13(2), p. 726. A jointly continuous vector-valued weak
differential is a strong continuous differential. -/
theorem hasStrongDifferentialOn_of_weak {Ω : Set W} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : W → E}
    {D : Ω × W → E} (hD : HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D))
    (hc : Continuous D) : HasStrongDifferentialOn (k := k) f D := by
  refine ⟨hc, (hasWeakCompletionDifferentialOn_iff hΩ f _).2 ⟨hD, ?_⟩⟩
  exact (continuous_toPettisWeakCompletion (E := E)).comp hc

/-- Paper: Lemma C.5.1.13(2), p. 726. Directional difference quotients converge in
the given vector topology to the jointly continuous vector-valued weak differential. -/
theorem tendsto_directional_of_weakDifferential {Ω : Set W} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : W → E}
    {D : Ω × W → E} (hD : HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D))
    (hc : Continuous D) (x : Ω) (v : W) :
    Tendsto (fun h : k ↦ algebraMap k ℂ h⁻¹ • (f ((x : W) + h • v) - f x))
      (𝓝[{h : k | h ≠ 0 ∧ (x : W) + h • v ∈ Ω}] 0) (𝓝 (D (x, v))) := by
  let line (t : k) := (x : W) + t • v
  have hline (t : k) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id' t).smul_const v).const_add (x : W)
  have hlim : Tendsto line (𝓝 0) (𝓝 (x : W)) := by
    simpa [line] using (hline 0).continuousAt.tendsto
  apply ((PolynormableSpace.withSeminorms ℂ E).tendsto_nhds _ _).2
  intro p ε hε
  -- Joint continuity bounds the variation of the differential in this seminorm.
  have hc' : Continuous (fun y : Ω ↦ p.val (D (y, v) - D (x, v))) :=
    p.property.comp ((hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
  have hnear : ∀ᶠ y : Ω in 𝓝 x, p.val (D (y, v) - D (x, v)) < ε / 2 :=
    hc'.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hε)
  obtain ⟨r, hr, hcontrol⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hlim.eventually (hΩ.mem_nhds x.property)).and
      (hlim.eventually (Metric.ball_mem_nhds (x : W) hr)))
  let B := Metric.ball (0 : k) δ
  have hin (t : k) (ht : t ∈ B) : line t ∈ Ω := (hball t ht).1
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : k) hδ),
    self_mem_nhdsWithin] with h hb hh
  have hn : h ≠ 0 := hh.1
  obtain ⟨φ, hφ, heq⟩ := exists_dual_norm_eq_seminorm p.val p.property
    (algebraMap k ℂ h⁻¹ • (f (line h) - f x) - D (x, v))
  -- Apply the scalar mean-value estimate after subtracting the tangent at zero.
  let g (t : k) := φ (f (line t)) - t • φ (D (x, v))
  have hderiv (t : k) (ht : t ∈ B) :
      HasDerivAt g (φ (D (⟨line t, hin t ht⟩, v) - D (x, v))) t := by
    obtain ⟨L, hL, heval⟩ := hD φ ⟨line t, hin t ht⟩
    have hL' := (hL.hasFDerivAt (hΩ.mem_nhds (hin t ht))).comp_hasDerivAt t (hline t)
    have he : φ (D (⟨line t, hin t ht⟩, v)) = L v := heval v
    simpa [g, Function.comp_def, Pi.sub_def, map_sub, he] using
      hL'.sub ((hasDerivAt_id' t).smul_const (φ (D (x, v))))
  have hmean := (convex_ball (0 : k) δ).norm_image_sub_le_of_norm_deriv_le
    (fun t ht ↦ (hderiv t ht).differentiableAt) (fun t ht ↦ by
      rw [(hderiv t ht).deriv]
      exact (hφ _).trans (hcontrol (y := ⟨line t, hin t ht⟩) (hball t ht).2).le)
    (Metric.mem_ball_self hδ) hb
  change p.val (algebraMap k ℂ h⁻¹ • (f (line h) - f x) - D (x, v)) < ε
  rw [← heq]
  have hscalar : φ (algebraMap k ℂ h⁻¹ • (f (line h) - f x) - D (x, v)) =
      h⁻¹ • (g h - g 0) := by
    simp [g, line, map_sub, Algebra.smul_def, mul_sub, hn, sub_right_comm]
  rw [hscalar, norm_smul, norm_inv]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hn)).2 (by simpa [mul_comm] using hmean)

end Differentials

section PartialDifferentials

variable {k E : Type*} [RCLike k] [NormedAlgebra k ℂ] {d : ℕ}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local notation "V" => EuclideanSpace k (Fin d)

/-- Paper: Definition C.5.1.14, p. 728. Every scalar evaluation has a derivative
along the specified standard coordinate line at every point of the domain. -/
def WeaklyPartialDifferentiableOn (i : Fin d) (f : V → E) (Ω : Set V) : Prop :=
  ∀ (φ : StrongDual ℂ E) (x : Ω),
    DifferentiableWithinAt k (fun t : k ↦ φ (f ((x : V) + t • EuclideanSpace.single i 1)))
      {t | (x : V) + t • EuclideanSpace.single i 1 ∈ Ω} 0

/-- Paper: Definition C.5.1.14, p. 728. The weak partial derivative evaluated at a
functional is the ordinary partial derivative of the scalar evaluation. -/
def HasWeakPartialOn {Ω : Set V} (i : Fin d) (f : V → E)
    (D : Ω → PettisWeakCompletion E) : Prop :=
  ∀ (φ : StrongDual ℂ E) (x : Ω),
    HasDerivWithinAt (fun t : k ↦ φ (f ((x : V) + t • EuclideanSpace.single i 1)))
      ((show Module.Dual ℂ (StrongDual ℂ E) from D x) φ)
      {t | (x : V) + t • EuclideanSpace.single i 1 ∈ Ω} 0

/-- Paper: Definition C.5.1.14, p. 728. On an open set, weak differentiability in a
coordinate direction is equivalent to existence of a unique weak partial derivative. -/
theorem weaklyPartialDifferentiableOn_iff_existsUnique {Ω : Set V} (hΩ : IsOpen Ω)
    (i : Fin d) (f : V → E) :
    WeaklyPartialDifferentiableOn i f Ω ↔
      ∃! D : Ω → PettisWeakCompletion E, HasWeakPartialOn i f D := by
  let line (x : Ω) (t : k) := (x : V) + t • EuclideanSpace.single i 1
  let S (x : Ω) := line x ⁻¹' Ω
  have huniq (x : Ω) : UniqueDiffWithinAt k (S x) 0 := by
    have hc : Continuous (line x) := continuous_const.add (continuous_id.smul continuous_const)
    exact (hΩ.preimage hc).uniqueDiffWithinAt (by simp [line])
  constructor
  · intro hf
    let D (x : Ω) : Module.Dual ℂ (StrongDual ℂ E) :=
      { toFun := fun φ ↦ derivWithin (fun t ↦ φ (f (line x t))) (S x) 0
        map_add' := fun φ ψ ↦ by
          change derivWithin ((fun t ↦ φ (f (line x t))) + (fun t ↦ ψ (f (line x t)))) (S x) 0 = _
          exact derivWithin_add (hf φ x) (hf ψ x)
        map_smul' := fun c φ ↦ by
          change derivWithin (c • (fun t ↦ φ (f (line x t)))) (S x) 0 = _
          exact derivWithin_const_smul c (hf φ x) }
    refine ⟨D, fun φ x ↦ (hf φ x).hasDerivWithinAt, ?_⟩
    intro D' hD'
    funext x
    apply LinearMap.ext
    intro φ
    exact ((hD' φ x).derivWithin (huniq x)).symm
  · rintro ⟨D, hD, _⟩ φ x
    exact (hD φ x).differentiableWithinAt

/-- Paper: Lemma C.5.1.15, p. 728. A weak differential is jointly continuous
exactly when each weak coordinate partial exists and is continuous. -/
theorem weaklyContDiffOn_iff_continuous_weakPartials {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    WeaklyContDiffOn k f Ω ↔
      ∀ i : Fin d, ∃ D : Ω → PettisWeakCompletion E, HasWeakPartialOn i f D ∧ Continuous D := by
  classical
  let e (i : Fin d) := EuclideanSpace.single i (1 : k)
  constructor
  · rintro ⟨D, hD, hc⟩ i
    refine ⟨fun x ↦ D (x, e i), ?_, hc.comp (continuous_id.prodMk continuous_const)⟩
    intro φ x
    obtain ⟨L, hL, heval⟩ := hD φ x
    rw [heval (e i)]
    exact hL.hasLineDerivWithinAt (e i)
  · intro h
    choose P hP hPc using h
    let D (p : Ω × V) : PettisWeakCompletion E := ∑ i, algebraMap k ℂ (p.2 i) • P i p.1
    refine ⟨D, ?_, continuous_finsetSum _ fun i _ ↦ ?_⟩
    · intro φ x
      let ev : PettisWeakCompletion E →L[ℂ] ℂ := WeakBilin.eval _ φ
      let a (i : Fin d) (y : V) := if hy : y ∈ Ω then ev (P i ⟨y, hy⟩) else 0
      have hval (i : Fin d) (y : Ω) : a i y = ev (P i y) := dite_eq_left y.property
      have hc (i : Fin d) : ContinuousAt (a i) (x : V) := by
        apply ContinuousOn.continuousAt (s := Ω) _ (hΩ.mem_nhds x.property)
        apply continuousOn_iff_continuous_domRestrict.mpr
        change Continuous (fun y : Ω ↦ a i y)
        simp_rw [hval]
        exact ev.continuous.comp (hPc i)
      have ha (i : Fin d) : ∀ᶠ y in 𝓝 (x : V),
          HasLineDerivAt k (φ ∘ f) (a i y) y (e i) := by
        filter_upwards [hΩ.mem_nhds x.property] with y hy
        have hp : HasLineDerivWithinAt k (φ ∘ f) (ev (P i ⟨y, hy⟩)) Ω y (e i) := hP i φ ⟨y, hy⟩
        simpa only [a, dite_eq_left hy] using hp.hasLineDerivAt (hΩ.mem_nhds hy)
      refine ⟨_, (hasFDerivAt_of_continuous_coordinate_derivatives a ha hc).hasFDerivWithinAt,
        fun v ↦ ?_⟩
      change ev (∑ i, algebraMap k ℂ (v i) • P i x) = _
      rw [map_sum]
      simp only [map_smul, sum_apply, ContinuousLinearMap.smulRight_apply, hval, Algebra.smul_def]
      rfl
    · exact ((continuous_algebraMap k ℂ).comp
        ((EuclideanSpace.proj (𝕜 := k) i).continuous.comp continuous_snd)).smul
        ((hPc i).comp continuous_fst)

/-- Paper: Lemma C.5.1.16(1), p. 729. Evaluating a weak directional limit at a
continuous functional gives the scalar line derivative in that direction. -/
theorem HasWeakDirectionalDerivativesOn.hasDerivWithinAt
    {W : Type*} [NormedAddCommGroup W] [NormedSpace k W] {Ω : Set W}
    {f : W → E} {D : Ω × W → PettisWeakCompletion E}
    (hD : HasWeakDirectionalDerivativesOn (k := k) f D)
    (φ : StrongDual ℂ E) (x : Ω) (v : W) :
    HasDerivWithinAt (fun t : k ↦ φ (f ((x : W) + t • v)))
      ((show Module.Dual ℂ (StrongDual ℂ E) from D (x, v)) φ)
      ((fun t : k ↦ (x : W) + t • v) ⁻¹' Ω) 0 := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have h := (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).1 (hD x v) φ
  change Tendsto (fun h : k ↦ algebraMap k ℂ h⁻¹ * φ (f ((x : W) + h • v) - f x))
    (𝓝[{h : k | h ≠ 0 ∧ (x : W) + h • v ∈ Ω}] 0)
    (𝓝 ((show Module.Dual ℂ (StrongDual ℂ E) from D (x, v)) φ)) at h
  have hs : ((fun t : k ↦ (x : W) + t • v) ⁻¹' Ω) \ {0} =
      {t : k | t ≠ 0 ∧ (x : W) + t • v ∈ Ω} := by
    ext t
    simp [and_comm]
  rw [hs, slope_fun_def]
  simpa only [sub_zero, vsub_eq_sub, zero_smul, add_zero, Algebra.smul_def,
    map_sub] using! h

/-- Paper: Lemma C.5.1.16(1), p. 729. Weak Gâteaux differentiability gives weak
differentiability in each standard coordinate direction. -/
theorem WeakGateauxDifferentiableOn.weaklyPartialDifferentiableOn {Ω : Set V}
    (hΩ : IsOpen Ω) {f : V → E} (hf : WeakGateauxDifferentiableOn (k := k) Ω f) (i : Fin d) :
    WeaklyPartialDifferentiableOn i f Ω := by
  obtain ⟨D, hD⟩ := hf
  intro φ x
  exact (hD.hasDerivWithinAt φ x (EuclideanSpace.single i 1)).differentiableWithinAt

/-- Continuity of a weak directional derivative on the coordinate slices suffices to
identify all its values with the scalar Fréchet differentials. -/
theorem HasWeakDirectionalDerivativesOn.hasWeakDifferentialOn {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : V → E} {D : Ω × V → PettisWeakCompletion E}
    (hD : HasWeakDirectionalDerivativesOn (k := k) f D)
    (hc : ∀ i : Fin d, Continuous (fun x : Ω ↦ D (x, EuclideanSpace.single i 1))) :
    HasWeakDifferentialOn k f D := by
  have hf : WeaklyContDiffOn k f Ω := (weaklyContDiffOn_iff_continuous_weakPartials hΩ hd f).2
    fun i ↦ ⟨_, fun φ x ↦ hD.hasDerivWithinAt φ x (EuclideanSpace.single i 1), hc i⟩
  obtain ⟨_, hA, _⟩ := hf
  intro φ x
  obtain ⟨L, hL, _⟩ := hA φ x
  refine ⟨L, hL, fun v ↦ ?_⟩
  have hline : HasLineDerivWithinAt k (φ ∘ f)
      ((show Module.Dual ℂ (StrongDual ℂ E) from D (x, v)) φ) Ω x v := hD.hasDerivWithinAt φ x v
  exact (hline.hasLineDerivAt (hΩ.mem_nhds x.property)).unique
    ((hL.hasFDerivAt (hΩ.mem_nhds x.property)).hasLineDerivAt v)

/-- Paper: Lemma C.5.1.16(2), p. 729. A jointly continuous weak Gâteaux derivative
is the weak differential. -/
theorem hasWeakDifferentialOn_of_continuous_directional {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : V → E} {D : Ω × V → PettisWeakCompletion E}
    (hD : HasWeakDirectionalDerivativesOn (k := k) f D) (hc : Continuous D) :
    HasWeakDifferentialOn k f D := by
  exact hD.hasWeakDifferentialOn hΩ hd fun _ ↦ hc.comp (continuous_id.prodMk continuous_const)

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.5.1.16(3), p. 729. An E-valued weak Gâteaux derivative continuous
in the base point for each direction is the strong continuous differential. -/
theorem hasStrongDifferentialOn_of_basepoint_continuous_directional {Ω : Set V}
    (hΩ : IsOpen Ω) (hd : 1 ≤ d) {f : V → E} {D : Ω × V → E}
    (hD : HasWeakDirectionalDerivativesOn (k := k) f (toPettisWeakCompletion E ∘ D))
    (hc : ∀ v : V, Continuous (fun x : Ω ↦ D (x, v))) :
    HasStrongDifferentialOn (k := k) f D := by
  classical
  have hp : ∀ i : Fin d, ∃ P : Ω → PettisWeakCompletion E,
      HasWeakPartialOn i f P ∧ Continuous P := by
    intro i
    refine ⟨fun x ↦ toPettisWeakCompletion E (D (x, EuclideanSpace.single i 1)), ?_,
      (continuous_toPettisWeakCompletion (E := E)).comp (hc _)⟩
    exact fun φ x ↦ hD.hasDerivWithinAt φ x _
  obtain ⟨A, hA, hAc⟩ := (weaklyContDiffOn_iff_continuous_weakPartials hΩ hd f).2 hp
  have hweak : HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D) := by
    intro φ x
    obtain ⟨L, hL, hLA⟩ := hA φ x
    refine ⟨L, hL, fun v ↦ ?_⟩
    have hline := hD.hasDerivWithinAt φ x v
    have hline' := hL.hasLineDerivWithinAt v
    have hu : UniqueDiffWithinAt k ((fun t : k ↦ (x : V) + t • v) ⁻¹' Ω) 0 := by
      apply (hΩ.preimage (continuous_const.add (continuous_id.smul continuous_const))).uniqueDiffWithinAt
      simpa using x.property
    exact (hline.derivWithin hu).symm.trans (hline'.derivWithin hu)
  have hinj : Function.Injective (toPettisWeakCompletion E) := by
    intro a b hab
    apply (toWeakSpace ℂ E).injective
    apply (isEmbedding_toPettisWeakCompletion (E := E)).injective
    simpa using hab
  have hformula (x : Ω) (v : V) :
      D (x, v) = ∑ i : Fin d, algebraMap k ℂ (v i) • D (x, EuclideanSpace.single i 1) := by
    apply hinj
    apply LinearMap.ext
    intro φ
    obtain ⟨L, _, hL⟩ := hweak φ x
    change φ (D (x, v)) = φ (∑ i : Fin d, algebraMap k ℂ (v i) • D (x, EuclideanSpace.single i 1))
    simp only [map_sum, map_smul]
    have hv (w : V) : φ (D (x, w)) = L w := hL w
    simp only [hv]
    have hcoord : (∑ i : Fin d, (v i) • EuclideanSpace.single i (1 : k)) = v := by
      ext j
      simp [PiLp.single_apply, Pi.single_apply, Finset.sum_ite_eq']
    calc
      L v = L (∑ i : Fin d, (v i) • EuclideanSpace.single i (1 : k)) := by rw [hcoord]
      _ = ∑ i : Fin d, algebraMap k ℂ (v i) • L (EuclideanSpace.single i 1) := by
        simp [map_sum, map_smul, Algebra.smul_def, smul_eq_mul]
  apply hasStrongDifferentialOn_of_weak hΩ hd hweak
  apply (continuous_finsetSum _ fun i _ ↦ ?_).congr
  · exact fun p ↦ (hformula p.1 p.2).symm
  · exact ((continuous_algebraMap k ℂ).comp
      ((EuclideanSpace.proj (𝕜 := k) i).continuous.comp continuous_snd)).smul
      ((hc _).comp continuous_fst)

/-- Paper: Lemma C.5.1.17(1), p. 730. Precomposition with a differentiable map
preserves weak differentiability. -/
theorem WeaklyDifferentiableOn.comp {Ω₁ Ω₂ : Set V} (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂)
    {f : V → E} {g : V → V} (hf : WeaklyDifferentiableOn k f Ω₂)
    (hg : DifferentiableOn k g Ω₁) (hmap : MapsTo g Ω₁ Ω₂) :
    WeaklyDifferentiableOn k (f ∘ g) Ω₁ := by
  intro φ
  exact (hf φ).comp hg hmap

-- TODO(paper-gap): In C.5.1.17(2), taking f to be the scalar inclusion and g(t) =
-- t² sin(1/t) (with g(0) = 0) disproves continuous differentiability of the composite.

/-- Paper: Lemma C.5.1.17(2), p. 730. The chain rule identifies the weak differential of
the composite with the image of the vector-valued differential composed with the inner one.
Deviation: For the printed differentiability assumption on the inner map, the chain rule
survives while the claimed continuity of the composite differential fails. -/
theorem HasStrongDifferentialOn.comp_weak {Ω₁ Ω₂ : Set V}
    (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) {f : V → E} {g : V → V} {D : Ω₂ × V → E}
    (hD : HasStrongDifferentialOn (k := k) f D)
    (hg : DifferentiableOn k g Ω₁) (hmap : MapsTo g Ω₁ Ω₂) :
    HasWeakDifferentialOn k (f ∘ g) (fun xv : Ω₁ × V ↦
      toPettisWeakCompletion E (D (⟨g xv.1, hmap xv.1.property⟩,
        fderivWithin k g Ω₁ xv.1 xv.2))) := by
  intro φ x
  have hf := ((hasWeakCompletionDifferentialOn_iff (k := k) hΩ₂ f _).1 hD.2).1
  obtain ⟨L, hL, heval⟩ := hf φ ⟨g x, hmap x.property⟩
  refine ⟨L.comp (fderivWithin k g Ω₁ x), hL.comp (x : V) (hg x x.property).hasFDerivWithinAt hmap, ?_⟩
  intro v
  exact heval (fderivWithin k g Ω₁ x v)

-- TODO(paper-gap): For Lemma C.5.1.19, f(x) = x and γ(t) = t² sin(1/t²), extended by
-- zero, give a differentiable curve with a discontinuous, non-Lebesgue-integrable derivative.

/-- Paper: Lemma C.5.1.19, p. 731. Evaluation of the vector-valued chain-rule
expression gives the derivative of the scalar composite along a real curve.
Deviation: The pointwise identity survives the printed curve regularity. The continuity
and Pettis integral assertions require more than the stated assumptions. -/
theorem HasStrongDifferentialOn.hasDerivWithinAt_curve
    [NormedSpace ℝ V] [IsScalarTower ℝ k V] [IsScalarTower ℝ k ℂ]
    {a₀ b₀ a b : ℝ} (hab : a ≤ b) (hinterval : Icc a b ⊆ Ioo a₀ b₀)
    {Ω U : Set V} (hΩ : IsOpen Ω) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f : V → E} {D : U × V → E} (hD : HasStrongDifferentialOn (k := k) f D)
    {γ : ℝ → V} (hγ : DifferentiableOn ℝ γ (Ioo a₀ b₀))
    (hγΩ : MapsTo γ (Ioo a₀ b₀) Ω) (hγU : MapsTo γ (Icc a b) U)
    (hd : 1 ≤ d) (φ : StrongDual ℂ E) {t : ℝ} (ht : t ∈ Icc a b) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      HasDerivWithinAt (φ ∘ f ∘ γ)
        (φ (D (⟨γ t, hγU ht⟩, derivWithin γ (Ioo a₀ b₀) t)))
        (Ioo a₀ b₀) t := by
  intro _
  -- The curve hypothesis uses the canonical real normed-space instance on V.
  clear ‹NormedSpace ℝ V›
  have hweak := ((hasWeakCompletionDifferentialOn_iff (k := k) hU f _).1 hD.2).1
  obtain ⟨L, hL, heval⟩ := hweak φ ⟨γ t, hγU ht⟩
  have hf := (hL.hasFDerivAt (hU.mem_nhds (hγU ht))).restrictScalars ℝ
  have hcurve := (hγ t (hinterval ht)).hasDerivWithinAt
  exact (hf.comp_hasDerivWithinAt t hcurve).congr_deriv (heval _).symm

/-- Paper: Theorem C.5.1.21(1, 2), p. 732. Strong continuous differentiability
is equivalent to a weak differential with a jointly continuous vector-valued lift. -/
theorem vectorContDiffOn_iff_weakDifferential {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    VectorContDiffOn (k := k) Ω f ↔
      ∃ D : Ω × V → E, HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D) ∧
        Continuous D := by
  constructor
  · rintro ⟨D, hD⟩
    -- Lemma C.5.1.12 turns the strong remainder into the scalar weak differential.
    exact ⟨D, ((hasWeakCompletionDifferentialOn_iff hΩ f _).1 hD.2).1, hD.1⟩
  · rintro ⟨D, hD, hc⟩
    -- Lemma C.5.1.13(2): a continuous E-valued weak differential is strong.
    exact ⟨D, hasStrongDifferentialOn_of_weak hΩ hd hD hc⟩

/-- Paper: Theorem C.5.1.21(1, 3), p. 732. Strong continuous differentiability
is equivalent to weak coordinate partials with continuous vector-valued lifts. -/
theorem vectorContDiffOn_iff_weakPartials {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    VectorContDiffOn (k := k) Ω f ↔
      ∀ i : Fin d, ∃ D : Ω → E, HasWeakPartialOn i f (toPettisWeakCompletion E ∘ D) ∧
        Continuous D := by
  rw [vectorContDiffOn_iff_weakDifferential hΩ hd f]
  let e (i : Fin d) := EuclideanSpace.single i (1 : k)
  constructor
  · rintro ⟨D, hD, hc⟩ i
    refine ⟨fun x ↦ D (x, e i), ?_, hc.comp (continuous_id.prodMk continuous_const)⟩
    intro φ x
    obtain ⟨L, hL, heval⟩ := hD φ x
    change HasLineDerivWithinAt k (φ ∘ f) (φ (D (x, e i))) Ω (x : V) (e i)
    rw [show φ (D (x, e i)) = L (e i) from heval (e i)]
    exact hL.hasLineDerivWithinAt (e i)
  · intro h
    choose P hP hPc using h
    obtain ⟨_, hWeak, _⟩ := (weaklyContDiffOn_iff_continuous_weakPartials hΩ hd f).2
      (fun i ↦ ⟨_, hP i, continuous_toPettisWeakCompletion.comp (hPc i)⟩)
    let D (p : Ω × V) : E := ∑ i, algebraMap k ℂ (p.2 i) • P i p.1
    refine ⟨D, ?_, continuous_finsetSum _ fun i _ ↦ ?_⟩
    · intro φ x
      obtain ⟨L, hL, _⟩ := hWeak φ x
      refine ⟨L, hL, fun v ↦ ?_⟩
      have hpartial (i : Fin d) : φ (P i x) = L (e i) := by
        have hp : HasLineDerivWithinAt k (φ ∘ f) (φ (P i x)) Ω (x : V) (e i) :=
          hP i φ x
        have hx := hΩ.mem_nhds x.property
        exact (hp.hasLineDerivAt hx).unique ((hL.hasFDerivAt hx).hasLineDerivAt (e i))
      have hcoord : (∑ i, v i • e i) = v := by
        simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using
          (EuclideanSpace.basisFun (Fin d) k).sum_repr v
      change φ (∑ i, algebraMap k ℂ (v i) • P i x) = L v
      calc
        _ = L (∑ i, v i • e i) := by
          simp only [map_sum, map_smul, hpartial, Algebra.smul_def, Algebra.algebraMap_self_apply]
        _ = L v := congrArg L hcoord
    · exact ((continuous_algebraMap k ℂ).comp
        ((EuclideanSpace.proj (𝕜 := k) i).continuous.comp continuous_snd)).smul
        ((hPc i).comp continuous_fst)

/-- Paper: Theorem C.5.1.21(1, 4), p. 732. Strong continuous differentiability
is equivalent to jointly continuous vector-valued lifts of the weak directional limits. -/
theorem vectorContDiffOn_iff_weakDirectional {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    VectorContDiffOn (k := k) Ω f ↔
      ∃ D : Ω × V → E,
        HasWeakDirectionalDerivativesOn (k := k) f (toPettisWeakCompletion E ∘ D) ∧
          Continuous D := by
  constructor
  · rintro ⟨D, hc, hD⟩
    exact ⟨D, hD.hasWeakDirectionalDerivativesOn hΩ, hc⟩
  · rintro ⟨D, hD, hc⟩
    exact ⟨D, hasStrongDifferentialOn_of_basepoint_continuous_directional hΩ hd hD
      (fun _ ↦ hc.comp (continuous_id.prodMk continuous_const))⟩

open scoped Uniformity in
omit [ContinuousSMul ℂ E] [T2Space E] in
/-- Scalar `C¹` extensions bound the vector difference quotients on any closed ball
in the extension domain, giving uniform continuity on the part where they agree with
the scalar evaluations. -/
private theorem uniformContinuousOn_of_scalar_extensions
    {Ω S : Set k} (hΩ : IsOpen Ω) {x : k} {r : ℝ} (hball : Metric.closedBall x r ⊆ Ω)
    (hS : S ⊆ Metric.closedBall x r) {f : k → E}
    (hf : ∀ φ : StrongDual ℂ E, ∃ g : k → ℂ, ContDiffOn k 1 g Ω ∧ EqOn g (φ ∘ f) S) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    UniformContinuousOn f S := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let c (p : k × k) : ℂ := algebraMap k ℂ (p.2 - p.1)
  let q (p : k × k) : E := (c p)⁻¹ • (f p.2 - f p.1)
  let D := q '' (S ×ˢ S)
  have hD : IsVonNBounded ℂ D := by
    apply isVonNBounded_of_dual_bounded
    intro φ
    obtain ⟨g, hg, heq⟩ := hf φ
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).image_of_continuousOn
      ((hg.continuousOn_deriv_of_isOpen hΩ le_rfl).mono hball)).isBounded.exists_norm_le
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    rcases eq_or_ne v u with rfl | hne
    · simp [q]
    have hmean := (convex_closedBall x r).norm_image_sub_le_of_norm_deriv_le
      (f := g) (C := max C 0)
      (fun w hw ↦ (hg.differentiableOn_one w (hball hw)).differentiableAt
        (hΩ.mem_nhds (hball hw)))
      (fun w hw ↦ (hC _ (mem_image_of_mem _ hw)).trans (le_max_left _ _)) (hS hu) (hS hv)
    have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    change ‖φ ((algebraMap k ℂ (v - u))⁻¹ • (f v - f u))‖ ≤ max C 0
    rw [map_smul, map_sub φ, norm_smul, norm_inv, norm_algebraMap',
      ← show g v = φ (f v) from heq hv, ← show g u = φ (f u) from heq hu]
    exact (inv_mul_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hmean)
  let l := 𝓤 k ⊓ 𝓟 (S ×ˢ S)
  have hc' : Tendsto (fun p : k × k ↦ p.2 - p.1) l (𝓝 0) := by
    apply Tendsto.mono_left _ (inf_le_left : l ≤ 𝓤 k)
    rw [uniformity_eq_comap_nhds_zero]
    exact tendsto_comap
  have hc : Tendsto c l (𝓝 0) := by
    simpa only [c, Function.comp_def, map_zero] using
      ((continuous_algebraMap k ℂ).tendsto 0).comp hc'
  have hq : ∀ᶠ p in l, q p ∈ D :=
    mem_of_superset (le_principal_iff.mp (inf_le_right : l ≤ 𝓟 (S ×ˢ S)))
      fun p hp ↦ mem_image_of_mem q hp
  rw [UniformContinuousOn, uniformity_eq_comap_nhds_zero E, tendsto_comap_iff]
  apply (hD.smul_tendsto_zero hq hc).congr
  rintro ⟨u, v⟩
  rcases eq_or_ne v u with rfl | hne
  · simp [q]
  · have hne' : c (u, v) ≠ 0 := by
      simpa only [c, map_zero] using (algebraMap k ℂ).injective.ne (sub_ne_zero.mpr hne)
    exact smul_inv_smul₀ hne' _

/-- Paper: Lemma C.5.1.22, p. 732. If all scalar evaluations extend with one
continuous derivative, the vector-valued function extends uniquely as a continuous map
on the open domain and that extension is weakly continuously differentiable.
Deviation: Uniqueness is on the domain of extension. Values outside it are immaterial. -/
theorem exists_weaklyContDiffOn_extension_puncture {Ω : Set k} (hΩ : IsOpen Ω)
    {x₀ : k} (hx₀ : x₀ ∈ Ω) (f : k → E)
    (hf : ∀ φ : StrongDual ℂ E, ContDiffOn k 1 (φ ∘ f) (Ω \ {x₀}) ∧
      ∃ g : k → ℂ, ContDiffOn k 1 g Ω ∧ EqOn g (φ ∘ f) (Ω \ {x₀})) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      ∃ F : k → E, ContinuousOn F Ω ∧ EqOn F f (Ω \ {x₀}) ∧ WeaklyContDiffOn k F Ω ∧
        ∀ G : k → E, ContinuousOn G Ω → EqOn G f (Ω \ {x₀}) → EqOn G F Ω := by
  classical
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  intro hcomplete
  let S := Ω \ {x₀}
  have hS : IsOpen S := hΩ.sdiff isClosed_singleton
  have hlocal {x : k} {r : ℝ} {T : Set k} (hball : Metric.closedBall x r ⊆ Ω)
      (hT : T ⊆ Metric.closedBall x r) (hTS : T ⊆ S) : UniformContinuousOn f T :=
    uniformContinuousOn_of_scalar_extensions hΩ hball hT fun φ ↦
      (hf φ).2.imp fun _ ⟨hg, heq⟩ ↦ ⟨hg, heq.mono hTS⟩
  have hcont : ContinuousOn f S := by
    intro x hx
    obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds hx)
    exact ((hlocal (hb.trans sdiff_subset) Subset.rfl hb).continuousOn x
      (Metric.mem_closedBall_self hr.le)).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x hr))
  let l := 𝓝[S] x₀
  have hl : l.NeBot := by
    change (𝓝[Ω ∩ {x₀}ᶜ] x₀).NeBot
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds hx₀))]
    infer_instance
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx₀)
  let T := Metric.closedBall x₀ r ∩ S
  have hT : T ∈ l :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ hr)) self_mem_nhdsWithin
  have hu := hlocal hb (T := T) inter_subset_left inter_subset_right
  have hc : Cauchy (map f l) := by
    refine cauchy_map_iff.mpr ⟨hl, hu.mono_left (le_inf ?_ ?_)⟩
    · exact (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds).trans cauchy_nhds.2
    · rw [← prod_principal_principal]
      exact Filter.prod_mono (le_principal_iff.mpr hT) (le_principal_iff.mpr hT)
  have htb : TotallyBounded (f '' T) := by
    rw [← range_domRestrict, ← image_univ]
    have hsub : TotallyBounded (univ : Set T) :=
      (totallyBounded_preimage isUniformEmbedding_subtype_val.isUniformInducing
        (isCompact_closedBall x₀ r).totallyBounded).subset (fun y _ ↦ y.property.1)
    exact hsub.image hu.restrict
  obtain ⟨v, _, hv⟩ := hcomplete.quasiComplete (htb.isVonNBounded ℂ).closure
    isClosed_closure (map f l) hc (le_principal_iff.mpr (mem_map.mpr
      (mem_of_superset hT fun x hx ↦ subset_closure (mem_image_of_mem f hx))))
  let F := update f x₀ v
  have hF : ContinuousOn F Ω := continuousOn_update_iff.mpr ⟨hcont, fun _ ↦ hv⟩
  have heq : EqOn F f S := fun x hx ↦ update_of_ne hx.2 _ _
  have hdense : Ω ⊆ closure S := by
    intro x hx
    rcases eq_or_ne x x₀ with rfl | hne
    · exact mem_closure_iff_nhdsWithin_neBot.mpr hl
    · exact subset_closure ⟨hx, hne⟩
  refine ⟨F, hF, heq, (weaklyContDiffOn_iff_scalar hΩ F).mpr ?_, ?_⟩
  · intro φ
    obtain ⟨g, hg, hgEq⟩ := (hf φ).2
    have hscalar : EqOn (φ ∘ F) g S := fun x hx ↦
      (congrArg φ (heq hx)).trans (hgEq hx).symm
    exact hg.congr (hscalar.of_subset_closure (φ.continuous.comp_continuousOn hF)
      hg.continuousOn sdiff_subset hdense)
  · intro G hG hg
    exact (hg.trans heq.symm).of_subset_closure hG hF sdiff_subset hdense

end PartialDifferentials

section HigherDifferentiability

variable {k E : Type*} [RCLike k] [NormedAlgebra k ℂ] {d : ℕ}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local notation "V" => EuclideanSpace k (Fin d)

/-- Paper: Definition C.5.1.23, p. 733. At order zero one bounded set
contains all normalized differences of points at distance at most one. At successor
order each weak partial has a continuous vector-valued lift of the preceding order. -/
def VectorContDiffOrderOn (f : V → E) (Ω : Set V) : ℕ → Prop
  | 0 => IsVonNBounded ℂ
      { z : E | ∃ x ∈ Ω, ∃ y ∈ Ω, x ≠ y ∧ ‖y - x‖ ≤ 1 ∧
        z = ((‖y - x‖⁻¹ : ℝ) : ℂ) • (f y - f x) }
  | m + 1 => ∀ i : Fin d, ∃ g : V → E,
      HasWeakPartialOn i f (fun x : Ω ↦ toPettisWeakCompletion E (g x)) ∧
        ContinuousOn g Ω ∧ VectorContDiffOrderOn g Ω m

/-- Paper: Definition C.5.1.23, p. 734. Smoothness in the sense of
this definition requires every order, including its bounded-difference order zero. -/
def VectorSmoothOn (f : V → E) (Ω : Set V) : Prop :=
  ∀ m : ℕ, VectorContDiffOrderOn f Ω m

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Definition C.5.1.23, p. 734. The zero map has every order of differentiability. -/
theorem vectorContDiffOrderOn_zero (Ω : Set V) (m : ℕ) :
    VectorContDiffOrderOn (0 : V → E) Ω m := by
  induction m with
  | zero =>
    show IsVonNBounded ℂ _
    refine (Bornology.isVonNBounded_singleton (0 : E)).subset ?_
    rintro z ⟨x, -, y, -, -, -, rfl⟩
    simp
  | succ m ih =>
    intro i
    refine ⟨0, ?_, continuousOn_const, ih⟩
    intro φ x
    simp only [Pi.zero_apply, map_zero]
    exact hasDerivWithinAt_const _ _ _

/-- Paper: Definition C.5.1.23, p. 734. The order condition is preserved by addition. -/
theorem VectorContDiffOrderOn.add {Ω : Set V} {m : ℕ} {f g : V → E}
    (hf : VectorContDiffOrderOn f Ω m) (hg : VectorContDiffOrderOn g Ω m) :
    VectorContDiffOrderOn (f + g) Ω m := by
  induction m generalizing f g with
  | zero =>
    unfold VectorContDiffOrderOn at hf hg ⊢
    refine (hf.add hg).subset ?_
    rintro z ⟨x, hx, y, hy, hxy, hd, rfl⟩
    refine ⟨_, ⟨x, hx, y, hy, hxy, hd, rfl⟩, _, ⟨x, hx, y, hy, hxy, hd, rfl⟩, ?_⟩
    simp only [Pi.add_apply, ← smul_add]
    congr 1
    abel
  | succ m ih =>
    intro i
    obtain ⟨gf, hgf, cf, of⟩ := hf i
    obtain ⟨gg, hgg, cg, og⟩ := hg i
    refine ⟨gf + gg, ?_, cf.add cg, ih of og⟩
    intro φ x
    simp only [Pi.add_apply, map_add]
    convert ((hgf φ x).hasFDerivWithinAt.add (hgg φ x).hasFDerivWithinAt).hasDerivWithinAt
      using 1
    simp
    rfl

/-- Paper: Definition C.5.1.23, p. 734. The order condition is preserved by complex
scalar multiplication. -/
theorem VectorContDiffOrderOn.smul {Ω : Set V} {m : ℕ} {f : V → E}
    (c : ℂ) (hf : VectorContDiffOrderOn f Ω m) : VectorContDiffOrderOn (c • f) Ω m := by
  induction m generalizing f with
  | zero =>
    unfold VectorContDiffOrderOn at hf ⊢
    refine (hf.image (c • ContinuousLinearMap.id ℂ E)).subset ?_
    rintro z ⟨x, hx, y, hy, hxy, hd, rfl⟩
    refine ⟨_, ⟨x, hx, y, hy, hxy, hd, rfl⟩, ?_⟩
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply,
      ← smul_sub]
    exact smul_comm _ _ _
  | succ m ih =>
    intro i
    obtain ⟨gf, hgf, cf, of⟩ := hf i
    refine ⟨c • gf, ?_, cf.const_smul c, ih of⟩
    intro φ x
    simp only [Pi.smul_apply, map_smul]
    convert ((hgf φ x).hasFDerivWithinAt.const_smul c).hasDerivWithinAt using 1
    simp
    rfl

/-- Paper: Definition C.5.1.23, p. 734. The order condition defines a submodule of
ambient functions. Restriction of this submodule gives the space on the open set. -/
def vectorContDiffOrderSubmodule (Ω : Set V) (m : ℕ) : Submodule ℂ (V → E) where
  carrier := { f | VectorContDiffOrderOn f Ω m }
  zero_mem' := vectorContDiffOrderOn_zero Ω m
  add_mem' := VectorContDiffOrderOn.add
  smul_mem' := fun c _ hf ↦ VectorContDiffOrderOn.smul c hf

/-- Paper: Definition C.5.1.23, p. 734. The order-m space consists of the restrictions
of ambient maps with the order-m property on the open set. -/
def vectorContDiffOrderSpace (Ω : Set V) (m : ℕ) : Submodule ℂ (Ω → E) :=
  (vectorContDiffOrderSubmodule (E := E) Ω m).map (LinearMap.pi fun x : Ω ↦ LinearMap.proj (x : V))

/-- Paper: Definition C.5.1.23, p. 734. The smooth space is the intersection
of the order-m spaces for all natural numbers m. -/
def vectorSmoothSpace (Ω : Set V) : Submodule ℂ (Ω → E) :=
  ⨅ m : ℕ, vectorContDiffOrderSpace (E := E) Ω m

/-- Paper: Definition C.5.1.23, p. 734. Constant vector-valued functions are smooth. -/
theorem vectorSmoothOn_const (Ω : Set V) (z : E) :
    VectorSmoothOn (fun _ : V ↦ z) Ω := by
  have key : ∀ (m : ℕ) (z : E), VectorContDiffOrderOn (fun _ : V ↦ z) Ω m := by
    intro m
    induction m with
    | zero =>
      intro z
      show IsVonNBounded ℂ _
      refine (Bornology.isVonNBounded_singleton (0 : E)).subset ?_
      rintro w ⟨x, -, y, -, -, -, rfl⟩
      simp
    | succ m ih =>
      intro z i
      refine ⟨fun _ ↦ 0, ?_, continuousOn_const, ih 0⟩
      intro φ x
      simp only [map_zero]
      exact hasDerivWithinAt_const _ _ _
  exact fun m ↦ key m z

/-- Paper: Definition C.5.1.23, p. 734. Restricting a constant map gives a member of
the smooth submodule and of every finite-order submodule. -/
theorem const_mem_vectorSmoothSpace (Ω : Set V) (z : E) :
    (fun _ : Ω ↦ z) ∈ vectorSmoothSpace Ω ∧
      ∀ m : ℕ, (fun _ : Ω ↦ z) ∈ vectorContDiffOrderSpace Ω m ∧
        (fun _ : V ↦ z) ∈ vectorContDiffOrderSubmodule Ω m := by
  have h3 (m : ℕ) : (fun _ : V ↦ z) ∈ vectorContDiffOrderSubmodule Ω m :=
    vectorSmoothOn_const Ω z m
  have h2 (m : ℕ) : (fun _ : Ω ↦ z) ∈ vectorContDiffOrderSpace Ω m :=
    Submodule.mem_map.mpr ⟨_, h3 m, rfl⟩
  exact ⟨Submodule.mem_iInf _ |>.mpr h2, fun m ↦ ⟨h2 m, h3 m⟩⟩

-- TODO(paper-gap): C.5.1.24 is false with the global bound at order zero.
-- On ℝ, x ↦ x² is weakly C¹ even under the recursive scalar reading, and fails order zero.

-- TODO(paper-gap): In C.5.1.25, the prose identifies scalar smoothness with the usual
-- concept. Under that reading x ↦ x² on ℝ disproves the reverse implication.

/-- The scalar weak partial gives the derivative along the corresponding coordinate line. -/
private theorem hasDerivAt_coordinateLine {Ω : Set V} (hΩ : IsOpen Ω) {i : Fin d}
    {f a : V → ℂ}
    (ha : HasWeakPartialOn i f (fun x : Ω ↦ toPettisWeakCompletion ℂ (a x)))
    (x : V) (t : k) (ht : x + t • EuclideanSpace.single i 1 ∈ Ω) :
    HasDerivAt (fun s : k ↦ f (x + s • EuclideanSpace.single i 1))
      (a (x + t • EuclideanSpace.single i 1)) t := by
  let e : V := EuclideanSpace.single i 1
  let y : Ω := ⟨x + t • e, ht⟩
  have hnear : {s : k | (y : V) + s • e ∈ Ω} ∈ 𝓝 0 :=
    (hΩ.preimage (continuous_const.add (continuous_id.smul continuous_const))).mem_nhds
      (by
        change (y : V) + (0 : k) • e ∈ Ω
        simpa only [zero_smul, add_zero] using y.property)
  have h : HasDerivAt (fun s : k ↦ f ((y : V) + s • e)) (a y) 0 :=
    (ha (ContinuousLinearMap.id ℂ ℂ) y).hasDerivAt hnear
  have h' : HasDerivAt (fun s : k ↦ f ((y : V) + s • e)) (a y) (-t + t) := by
    simpa only [neg_add_cancel] using h
  refine (h'.comp_const_add (-t) t).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s ↦ by
    change f (x + s • e) = f ((x + t • e) + (-t + s) • e)
    rw [add_assoc, ← add_smul, ← add_assoc, add_neg_cancel, zero_add]

/-- Two scalar orders suffice to represent a coordinate derivative at a point in a
quasi-complete target. -/
private theorem exists_vector_partial_at {Ω : Set V} (hΩ : IsOpen Ω) {f : V → E}
    (hf : ∀ φ : StrongDual ℂ E, VectorContDiffOrderOn (φ ∘ f) Ω 2)
    (i : Fin d) (x : Ω) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      ∃ z : E, ∀ φ : StrongDual ℂ E,
        HasDerivAt (fun t : k ↦ φ (f ((x : V) + t • EuclideanSpace.single i 1))) (φ z) 0 := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  intro hcomplete
  let line (t : k) := (x : V) + t • EuclideanSpace.single i 1
  let S := line ⁻¹' Ω
  have hline : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have hS : IsOpen S := hΩ.preimage hline
  have hzero : 0 ∈ S := by simp [S, line, x.property]
  have hscalar (φ : StrongDual ℂ E) : ContDiffOn k 2 (φ ∘ f ∘ line) S := by
    obtain ⟨a, ha, _, ha₁⟩ := hf φ i
    obtain ⟨b, hb, hbc, _⟩ := ha₁ i
    have h₁ (t : k) (ht : t ∈ S) : HasDerivAt (φ ∘ f ∘ line) (a (line t)) t :=
      hasDerivAt_coordinateLine hΩ ha x t ht
    have h₂ (t : k) (ht : t ∈ S) : HasDerivAt (a ∘ line) (b (line t)) t :=
      hasDerivAt_coordinateLine hΩ hb x t ht
    have ha' : ContDiffOn k 1 (a ∘ line) S := by
      apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hS).mpr
      refine ⟨fun t ht ↦ (h₂ t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      apply contDiffOn_zero.mpr
      exact (hbc.comp hline.continuousOn (fun _ ht ↦ ht)).congr
        (fun t ht ↦ (h₂ t ht).deriv)
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hS).mpr
    exact ⟨fun t ht ↦ (h₁ t ht).differentiableAt.differentiableWithinAt, by simp,
      ha'.congr (fun t ht ↦ (h₁ t ht).deriv)⟩
  -- Keep the real parameter in the line's domain with a cutoff equal to one near zero.
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hzero)
  let bump : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let u (t : ℝ) : k := (t * bump t) • (1 : k)
  have huS (t : ℝ) : u t ∈ S := by
    by_cases ht : ‖t‖ < r
    · apply hrS
      rw [Metric.mem_ball, dist_zero_right, show ‖u t‖ = ‖t‖ * bump t by
        simp [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]]
      exact (mul_le_of_le_one_right (norm_nonneg _) bump.le_one).trans_lt ht
    · have hb : bump t = 0 := bump.zero_of_le_dist (by simpa using le_of_not_gt ht)
      simpa only [u, hb, mul_zero, zero_smul] using hzero
  have hu : ContDiff ℝ 2 u := (contDiff_id.mul bump.contDiff).smul contDiff_const
  have hderiv : HasDerivAt u (1 : k) 0 := by
    have h : HasDerivAt (fun t : ℝ ↦ t • (1 : k)) (1 : k) 0 := by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const (1 : k)
    apply h.congr_of_eventuallyEq
    filter_upwards [bump.eventuallyEq_one] with t ht
    change bump t = 1 at ht
    simp only [u, ht, mul_one]
  have hu0 : u 0 = 0 := by simp [u]
  obtain ⟨z, hz⟩ := exists_hasDerivAt_eval_zero_of_contDiff (F := f ∘ line ∘ u)
    (fun φ ↦ (hscalar φ).restrict_scalars ℝ |>.comp_contDiff hu huS) hcomplete
  refine ⟨z, fun φ ↦ ?_⟩
  have hφ := ((hscalar φ).differentiableOn (by simp) 0 hzero).differentiableAt (hS.mem_nhds hzero)
  have hcomp := hφ.hasDerivAt.scomp_of_eq 0 hderiv hu0.symm
  have heq : φ z = deriv (φ ∘ f ∘ line) 0 := by
    simpa only [one_smul] using (hz φ).unique hcomp
  exact hφ.hasDerivAt.congr_deriv heq.symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] in
/-- The recursive order conditions depend only on the values on the domain. -/
private theorem vectorContDiffOrderOn_congr {Ω : Set V} {f g : V → E} {m : ℕ}
    (hf : VectorContDiffOrderOn f Ω m) (heq : EqOn g f Ω) :
    VectorContDiffOrderOn g Ω m := by
  cases m with
  | zero =>
    refine hf.subset ?_
    rintro _ ⟨x, hx, y, hy, hxy, hdist, rfl⟩
    exact ⟨x, hx, y, hy, hxy, hdist, by rw [heq hx, heq hy]⟩
  | succ m =>
    intro i
    obtain ⟨a, ha, hc, hm⟩ := hf i
    refine ⟨a, fun φ x ↦ (ha φ x).congr (fun t ht ↦ congrArg φ (heq ht)) ?_, hc, hm⟩
    simpa only [zero_smul, add_zero] using congrArg φ (heq x.property)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- Order zero follows from scalar order zero by weak boundedness. -/
private theorem vectorContDiffOrderOn_zero_of_scalar {Ω : Set V} {f : V → E}
    (hf : ∀ φ : StrongDual ℂ E, VectorContDiffOrderOn (φ ∘ f) Ω 0) :
    VectorContDiffOrderOn f Ω 0 := by
  apply (isVonNBounded_iff_dual_image _).mpr
  intro φ
  apply ((NormedSpace.isVonNBounded_iff ℂ).mp (hf φ)).subset
  rintro _ ⟨_, ⟨x, hx, y, hy, hxy, hdist, rfl⟩, rfl⟩
  exact ⟨x, hx, y, hy, hxy, hdist, by simp⟩

omit [PolynormableSpace ℂ E] [T2Space E] in
/-- Bounded normalized differences imply continuity on the domain. -/
private theorem continuousOn_of_vectorContDiffOrderOn_zero {Ω : Set V} {f : V → E}
    (hf : VectorContDiffOrderOn f Ω 0) : ContinuousOn f Ω := by
  intro x hx
  apply tendsto_sub_nhds_zero_iff.mp
  have ht : Tendsto (fun y : V ↦ (‖y - x‖ : ℂ)) (𝓝[Ω] x) (𝓝 0) := by
    have h : Continuous fun y : V ↦ (‖y - x‖ : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_id.sub continuous_const).norm
    simpa using (h.tendsto x).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ y in 𝓝[Ω] x, ‖y - x‖ < 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x zero_lt_one)] with y hy
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  let q (y : V) := ((‖y - x‖⁻¹ : ℝ) : ℂ) • (f y - f x)
  let B : Set E := {z | ∃ a ∈ Ω, ∃ b ∈ Ω, a ≠ b ∧ ‖b - a‖ ≤ 1 ∧
    z = ((‖b - a‖⁻¹ : ℝ) : ℂ) • (f b - f a)}
  have hb : IsVonNBounded ℂ (insert 0 B) := (isVonNBounded_insert (0 : E)).mpr hf
  have hq : ∀ᶠ y in 𝓝[Ω] x, q y ∈ insert 0 B := by
    filter_upwards [self_mem_nhdsWithin, hnear] with y hy hdist
    rcases eq_or_ne x y with rfl | hne
    · exact mem_insert_iff.mpr (Or.inl (by simp [q]))
    · exact mem_insert_of_mem _ ⟨x, hx, y, hy, hne, hdist.le, rfl⟩
  apply (hb.smul_tendsto_zero hq ht).congr
  intro y
  change (‖y - x‖ : ℂ) • (((‖y - x‖⁻¹ : ℝ) : ℂ) • (f y - f x)) = f y - f x
  rcases eq_or_ne y x with rfl | hne
  · simp
  · rw [Complex.ofReal_inv, smul_inv_smul₀ (by simpa using sub_ne_zero.mpr hne)]

-- Retain the dimension hypothesis from the paper. The proof also works in dimension zero.
set_option linter.unusedVariables false in
/-- Paper: Corollary C.5.1.25, p. 734. In a quasi-complete space, the all-order
condition is equivalent to the same all-order condition on every scalar evaluation.
Deviation: The scalar side uses Definition C.5.1.23, including its order-zero
boundedness condition. Ordinary scalar smoothness alone does not suffice. -/
theorem vectorSmoothOn_iff_scalar {Ω : Set V} (hΩ : IsOpen Ω) (hd : 1 ≤ d) (f : V → E) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      (VectorSmoothOn f Ω ↔ ∀ φ : StrongDual ℂ E, VectorSmoothOn (φ ∘ f) Ω) := by
  classical
  let := IsTopologicalAddGroup.rightUniformSpace E
  intro hcomplete
  constructor
  · intro hf φ m
    have hm := hf m
    clear hf
    induction m generalizing f with
    | zero =>
      refine (hm.image φ).subset ?_
      rintro _ ⟨x, hx, y, hy, hxy, hdist, rfl⟩
      exact ⟨_, ⟨x, hx, y, hy, hxy, hdist, rfl⟩, by simp⟩
    | succ m ih =>
      intro i
      obtain ⟨g, hg, hc, hgₘ⟩ := hm i
      exact ⟨φ ∘ g, fun ψ x ↦ hg (ψ.comp φ) x, φ.continuous.comp_continuousOn hc, ih g hgₘ⟩
  · intro hf m
    induction m generalizing f with
    | zero => exact vectorContDiffOrderOn_zero_of_scalar (fun φ ↦ hf φ 0)
    | succ m ih =>
      intro i
      choose a ha using fun x : Ω ↦ exists_vector_partial_at hΩ (fun φ ↦ hf φ 2) i x hcomplete
      let g (x : V) := if hx : x ∈ Ω then a ⟨x, hx⟩ else 0
      have hg (φ : StrongDual ℂ E) (x : Ω) :
          HasDerivAt (fun t : k ↦ φ (f ((x : V) + t • EuclideanSpace.single i 1))) (φ (g x)) 0 := by
        simpa only [g, dite_eq_left x.property] using ha x φ
      have hgs (φ : StrongDual ℂ E) : VectorSmoothOn (φ ∘ g) Ω := by
        intro n
        obtain ⟨b, hb, _, hn⟩ := hf φ (n + 1) i
        apply vectorContDiffOrderOn_congr hn
        intro x hx
        have hz := hasDerivAt_coordinateLine hΩ hb x 0 (by simpa using hx)
        rw [zero_smul, add_zero] at hz
        exact (hg φ ⟨x, hx⟩).unique hz
      exact ⟨g, fun φ x ↦ (hg φ x).hasDerivWithinAt,
        continuousOn_of_vectorContDiffOrderOn_zero
          (vectorContDiffOrderOn_zero_of_scalar (fun φ ↦ hgs φ 0)),
        ih g hgs⟩

end HigherDifferentiability

-- TODO(paper-gap): Definition C.5.1.26 specifies uniform convergence of values, while
-- Remark C.5.1.28 uses derivatives and polynomial weights. These topologies differ even
-- for E = ℂ, and Theorem C.5.1.30(1–3) fails for the printed uniform topology.
-- This pass ends at §C.5.1.4. See the issue report for §C.5.1.5 and its counterexamples.

end RiemannMasullo
