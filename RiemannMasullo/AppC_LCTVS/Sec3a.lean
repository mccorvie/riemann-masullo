module

public import RiemannMasullo.AppC_LCTVS.Sec2b
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Basic
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.UniformSpace.Ascoli
import RiemannMasullo.ForMathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Nuclear operators and the trace on Hilbert spaces

Masullo, Appendix C, §§C.3.1–C.3.4.
-/

@[expose] public noncomputable section

open Bornology Filter Function Set Topology TopologicalSpace UniformSpace
open scoped CStarAlgebra InnerProductSpace TensorProduct UniformConvergence UniformConvergenceCLM

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : ContinuousSMul ℝ E :=
  MulAction.continuousSMul_compHom (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal

section BanachOperators

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F]

/-- Paper: §C.3.1, p. 693. The series criterion of (C.2.4.2) expresses nuclearity
between Banach spaces using summable coefficients and two norm-null sequences. -/
def IsBanachNuclear (A : E →L[ℂ] F) : Prop :=
  ∃ (c : ℕ → ℂ) (φ : ℕ → E →L[ℂ] ℂ) (y : ℕ → F),
    Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (A x)

/-- Paper: §C.3.1, p. 693. A rank-one map has a nuclear series.
Deviation: This is a check of the series definition in the rank-one case. -/
theorem isBanachNuclear_smulRight (φ : E →L[ℂ] ℂ) (y : F) :
    IsBanachNuclear (φ.smulRight y) := by
  have hne := eventually_ne_atTop (0 : ℕ)
  refine ⟨fun n ↦ if n = 0 then 1 else 0, fun n ↦ if n = 0 then φ else 0,
    fun n ↦ if n = 0 then y else 0, ?_, ?_, ?_, ?_⟩
  · simpa only [apply_ite, norm_one, norm_zero] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  · exact tendsto_const_nhds.congr' (hne.mono fun _ hn ↦ (ite_eq_right hn).symm)
  · exact tendsto_const_nhds.congr' (hne.mono fun _ hn ↦ (ite_eq_right hn).symm)
  · intro x
    rw [ContinuousLinearMap.smulRight_apply]
    refine (hasSum_ite_eq (0 : ℕ) (φ x • y)).congr_fun ?_
    intro n
    by_cases hn : n = 0 <;> simp [hn]

end BanachOperators

section LocallyConvexOperators

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

local notation:25 X " →Lᵦ " Y => X →Lᵤ[ℂ, Set.ofPred (fun s : Set X ↦ IsVonNBounded ℂ s)] Y

-- Keep the section hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
open scoped ComplexOrder in
/-- Paper: (C.3.1.1), p. 693. The algebraic tensor-to-finite-rank map is continuous
for the projective tensor topology and uniform convergence on bounded sets. -/
theorem continuous_tensorToFiniteRank_bounded :
    Continuous (fun z : ProjectiveTensor (StrongDual ℂ E) F ↦
      (tensorToFiniteRank z : E →Lᵦ F)) := by
  let T : ProjectiveTensor (StrongDual ℂ E) F →ₗ[ℂ] (E →L[ℂ] F) := tensorToFiniteRank
  change Continuous T
  have hzero :
      ContinuousAt (fun p : StrongDual ℂ E × F ↦ tensorToFiniteRank (p.1 ⊗ₜ[ℂ] p.2)) 0 := by
    have hsmul : ContinuousAt (fun p : ℂ × F ↦ p.1 • p.2) 0 :=
      (continuous_fst.smul continuous_snd).continuousAt
    rw [ContinuousAt, Prod.fst_zero, TensorProduct.zero_tmul, map_zero,
      ContinuousLinearMap.nhds_zero_eq]
    rw [show (0 : StrongDual ℂ E × F) = (0, 0) from rfl, nhds_prod_eq]
    simp only [tendsto_iInf, tendsto_principal]
    intro s hs U hU
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp
      (hsmul.tendsto (by simpa only [Prod.fst_zero, zero_smul] using hU))
    exact ((ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hs hV).prod_mk
      (show ∀ᶠ y in 𝓝 (0 : F), y ∈ W from hW)).mono fun p hp x hx ↦
        hVW (show (p.1 x, p.2) ∈ V ×ˢ W from ⟨hp.1 hx, hp.2⟩)
  let : Module ℝ F := Module.restrictScalars ℝ ℂ F
  let : IsScalarTower ℝ ℂ F := IsScalarTower.restrictScalars ℝ ℂ F
  let : LocallyConvexSpace ℂ F := LocallyConvexSpace.ofBasisZero ℂ F
    (fun (p : Seminorm ℂ F) ↦ p.ball 0 1) (fun p ↦ Continuous p)
    (PolynormableSpace.hasBasis_zero_ball ℂ F) fun p _ ↦
      convex_of_nonneg_surjective_algebraMap ℂ
        (fun z hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) (p.convex_ball 0 1)
  -- Pull each operator seminorm back to a generating projective tensor seminorm.
  let hOperators := PolynormableSpace.withSeminorms ℂ (E →L[ℂ] F)
  let hProjective := withGeneratingSeminorms_spec (StrongDual ℂ E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (StrongDual ℂ E ⊗[ℂ] F) //
      ContinuousAt (fun v : StrongDual ℂ E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  refine hOperators.continuous_of_continuous_comp T fun i ↦
    hProjective.continuous_seminorm ⟨_, ?_⟩
  exact (hOperators.continuous_seminorm i).continuousAt.comp hzero

/-- Paper: (C.3.1.1), p. 693. The projective tensor of the strong dual and the
target maps continuously to operators with the bounded convergence topology. -/
def projectiveTensorToOperators :
    ProjectiveTensor (StrongDual ℂ E) F →L[ℂ] (E →Lᵦ F) :=
  ⟨tensorToFiniteRank, continuous_tensorToFiniteRank_bounded⟩

/-- Paper: (C.3.1.1), p. 693. On elementary tensors this map evaluates the functional
and scales the target vector. -/
theorem projectiveTensorToOperators_tmul (φ : StrongDual ℂ E) (y : F) (x : E) :
    projectiveTensorToOperators (φ ⊗ₜ[ℂ] y) x = φ x • y := rfl

omit [PolynormableSpace ℂ E] [T2Space E] [IsUniformAddGroup F] [T2Space F] in
/-- A linear map from a barrelled space is continuous if all its scalar compositions
with continuous functionals are continuous. -/
private theorem continuous_of_dual_compositions [BarrelledSpace ℂ E] (T : E →ₗ[ℂ] F)
    (hT : ∀ ψ : StrongDual ℂ F, Continuous (fun x ↦ ψ (T x))) : Continuous T := by
  refine (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp T fun ⟨q, hq⟩ ↦ ?_
  let A := {ψ : StrongDual ℂ F // ∀ y, ‖ψ y‖ ≤ q y}
  have : Nonempty A := ⟨⟨0, fun y ↦ by simp⟩⟩
  let p (ψ : A) := (normSeminorm ℂ ℂ).comp (ψ.val.toLinearMap.comp T)
  have hle (ψ : A) : p ψ ≤ q.comp T := fun x ↦ ψ.property (T x)
  have hb : BddAbove (range p) := ⟨q.comp T, forall_mem_range.mpr hle⟩
  have heq : (⨆ ψ, p ψ) = q.comp T := by
    apply le_antisymm
    · exact ciSup_le hle
    · intro x
      let : SeminormedAddCommGroup (WithLocalSeminorm q) := inferInstance
      obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℂ (show WithLocalSeminorm q from T x)
      have hgq (y : F) : ‖g (show WithLocalSeminorm q from y)‖ ≤ q y :=
        (g.le_opNorm y).trans (mul_le_of_le_one_left (apply_nonneg q y) hg)
      let g' : F →ₗ[ℂ] ℂ := g.toLinearMap
      have hgc : Continuous g' :=
        (PolynormableSpace.withSeminorms ℂ F).continuous_normedSpace_rng ℂ g'
          ⟨{⟨q, hq⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp g' ≤ q from hgq)⟩
      let ψ : A := ⟨⟨g', hgc⟩, hgq⟩
      have hpx : p ψ x = q (T x) := by
        change ‖g (show WithLocalSeminorm q from T x)‖ = q (T x)
        rw [hgx]
        exact Complex.norm_real _ |>.trans (Real.norm_of_nonneg (apply_nonneg q (T x)))
      exact hpx ▸ le_ciSup hb ψ x
  rw [← heq, Seminorm.coe_iSup_eq hb]
  exact Seminorm.continuous_iSup p (fun ψ ↦ (hT ψ.val).norm) hb

omit [T2Space E] in
/-- With complete target and complete strong dual of a barrelled source, the space
of continuous linear maps is complete for uniform convergence on bounded sets. -/
private theorem completeSpace_boundedOperators [CompleteSpace F] [BarrelledSpace ℂ E]
    [CompleteSpace (StrongDual ℂ E)] : CompleteSpace (E →Lᵦ F) := by
  let S : Set (Set E) := {s | IsVonNBounded ℂ s}
  let j : (E →Lᵦ F) → (E →ᵤ[S] F) := UniformOnFun.ofFun S ∘ DFunLike.coe
  let i : StrongDual ℂ E → (E →ᵤ[S] ℂ) := UniformOnFun.ofFun S ∘ DFunLike.coe
  have hj := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) F S
  have hi := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) ℂ S
  change IsUniformInducing j at hj
  change IsUniformInducing i at hi
  have : T2Space (E →ᵤ[S] ℂ) := T2Space.of_injective_continuous
    (UniformOnFun.toFun S).injective
    (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).continuous
  have hclosed : IsClosed (range i) := hi.isComplete_range.isClosed
  rw [completeSpace_iff_isComplete_range hj]
  apply IsClosed.isComplete
  rw [← closure_subset_iff_isClosed]
  intro f hf
  have hpoint : IsClosed {f : E →ᵤ[S] F | UniformOnFun.toFun S f ∈
      range (fun T : E →ₗ[ℂ] F ↦ (T : E → F))} :=
    (LinearMap.isClosed_range_coe E F (RingHom.id ℂ)).preimage
      (UniformOnFun.uniformContinuous_toFun (𝔖 := S) sUnion_isVonNBounded_eq_univ).continuous
  obtain ⟨T, hTf⟩ := hpoint.closure_subset_iff.mpr (by
    rintro _ ⟨A, rfl⟩
    exact ⟨A.toLinearMap, rfl⟩) hf
  have hT (ψ : StrongDual ℂ F) : Continuous (fun x ↦ ψ (T x)) := by
    let k := fun f : E →ᵤ[S] F ↦ UniformOnFun.ofFun S (ψ ∘ UniformOnFun.toFun S f)
    have hk : Continuous k := (UniformOnFun.postcomp_uniformContinuous ψ.uniformContinuous).continuous
    have hki : IsClosed (k ⁻¹' range i) := hclosed.preimage hk
    obtain ⟨φ, hφ⟩ := hki.closure_subset_iff.mpr (by
      rintro _ ⟨A, rfl⟩
      exact ⟨ψ.comp A, rfl⟩) hf
    have heq : (fun x ↦ ψ (T x)) = φ := by
      change (T : E → F) = UniformOnFun.toFun S f at hTf
      rw [show (fun x ↦ ψ (T x)) = ψ ∘ (T : E → F) from rfl, hTf]
      exact (UniformOnFun.ofFun S).injective hφ.symm
    rw [heq]
    exact φ.continuous
  exact ⟨⟨T, continuous_of_dual_compositions T hT⟩, (UniformOnFun.ofFun S).congr_arg hTf⟩

/-- An equicontinuous set of functionals sends a common zero-neighborhood into
any prescribed scalar zero-neighborhood. -/
private theorem dual_mem_nhds_of_equicontinuous {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (B : Set (StrongDual ℂ X))
    (hB : EquicontinuousAt (fun φ : B ↦ (φ.val : X → ℂ)) 0)
    {W : Set ℂ} (hW : W ∈ 𝓝 0) : {x : X | ∀ φ ∈ B, φ x ∈ W} ∈ 𝓝 0 := by
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hW
  filter_upwards [(Metric.uniformity_basis_dist.equicontinuousAt_iff_right.mp hB) r hr]
    with x hx
  intro φ hφ
  exact hrW (by simpa only [Metric.mem_ball, map_zero, dist_comm 0 (φ x)] using hx ⟨φ, hφ⟩)

/-- Testing the tensor against two equicontinuous dual sets is controlled by
uniform convergence of the associated operator on a bounded set of the source. -/
private theorem projectiveTensorToOperators_isUniformInducing_of_homeomorph
    [PolynormableSpace ℂ (StrongDual ℂ E)]
    (hI : IsHomeomorph (show ProjectiveTensor (StrongDual ℂ E) F →
      InjectiveTensor (StrongDual ℂ E) F from id)) :
    IsUniformInducing (projectiveTensorToOperators (E := E) (F := F)) := by
  let D := StrongDual ℂ E
  let P := ProjectiveTensor D F
  let I := InjectiveTensor D F
  let T : P →L[ℂ] (E →Lᵦ F) := projectiveTensorToOperators
  let S : Set (Set E) := {s | IsVonNBounded ℂ s}
  have hform (φ : StrongDual ℂ D) (ψ : StrongDual ℂ F) (z : P) :
      tensorDualForm φ ψ z = φ (ψ.comp (T z)) := by
    let post : (E →Lᵦ F) →L[ℂ] D := ψ.postcompUniformConvergenceCLM S
    have heq : tensorDualForm φ ψ = φ.toLinearMap.comp (post.toLinearMap.comp T.toLinearMap) := by
      apply TensorProduct.ext'
      intro f y
      have hψ : ψ.comp (T (f ⊗ₜ[ℂ] y)) = ψ y • f := by
        apply ContinuousLinearMap.ext
        intro x
        change ψ (projectiveTensorToOperators (f ⊗ₜ[ℂ] y) x) = ψ y * f x
        rw [projectiveTensorToOperators_tmul, map_smul, smul_eq_mul, mul_comm]
      change tensorDualForm φ ψ (f ⊗ₜ[ℂ] y) = φ (ψ.comp (T (f ⊗ₜ[ℂ] y)))
      rw [tensorDualForm_tmul, hψ, map_smul, smul_eq_mul, mul_comm]
    exact DFunLike.congr_fun heq z
  apply AddMonoidHom.isUniformInducing_of_isInducing (f := T)
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm
  · exact (by simpa only [map_zero] using T.continuous.tendsto 0 :
      Tendsto T (𝓝 0) (𝓝 0)).le_comap
  · let j : P → I := fun z ↦ z
    have hj : IsInducing j := hI.isInducing
    rw [hj.nhds_eq_comap (0 : P)]
    change comap T (𝓝 0) ≤ comap j (𝓝 (0 : I))
    rw [((injectiveTensor_zero_basis (E := D) (F := F)).comap j).ge_iff]
    rintro ⟨A, C⟩ ⟨hA, hC⟩
    have hS : DirectedOn (· ⊆ ·) S := directedOn_of_sup_mem fun _ _ ↦ IsVonNBounded.union
    have hD := UniformConvergenceCLM.hasBasis_nhds_zero (RingHom.id ℂ) ℂ S
      ⟨∅, isVonNBounded_empty ℂ E⟩ hS
    obtain ⟨⟨B, W⟩, ⟨hB, hW⟩, hBW⟩ := hD.mem_iff.mp
      (dual_mem_nhds_of_equicontinuous A hA (Metric.ball_mem_nhds 0 one_pos))
    have hTsmall := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hB
      (dual_mem_nhds_of_equicontinuous C hC hW)
    rw [Filter.mem_comap]
    refine ⟨_, hTsmall, fun z hz φ hφ ψ hψ ↦ ?_⟩
    rw [hform]
    have hp := hBW (show ∀ x ∈ B, (ψ.comp (T z)) x ∈ W from fun _ hx ↦ hz hx ψ hψ) φ hφ
    exact (mem_ball_zero_iff.mp hp).le

section TensorOperatorUniverse

universe u v

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
  [PolynormableSpace ℂ X] [T2Space X]
  [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
  [PolynormableSpace ℂ Y] [T2Space Y]

/-- View the target in a universe allowed by the nuclearity test and transport the
induced topology along the resulting tensor and operator maps. -/
private theorem projectiveTensorToOperators_isUniformInducing (h : IsNuclearTVS (StrongDual ℂ X)) :
    IsUniformInducing (projectiveTensorToOperators (E := X) (F := Y)) := by
  let D := StrongDual ℂ X
  have : T2Space D := h.1
  have : PolynormableSpace ℂ D := h.2.1
  let L := ULift.{u} Y
  let e : Y ≃L[ℂ] L := ContinuousLinearEquiv.ulift.symm
  have : PolynormableSpace ℂ L := PolynormableSpace.induced e.symm.toLinearEquiv.toLinearMap
  have : IsTopologicalAddGroup L := PolynormableSpace.isTopologicalAddGroup ℂ L
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  have hI : IsHomeomorph (show ProjectiveTensor D L → InjectiveTensor D L from id) := by
    have hn := (isNuclearTVS_iff_localBanach_series D).mp h
    exact ((isNuclearTVS_iff_localBanach_series.{v, u} D).mpr hn).2.2 L
      inferInstance inferInstance inferInstance inferInstance inferInstance
  let one : D →L[ℂ] D := ContinuousLinearMap.id ℂ D
  let lift := projectiveTensorMap one.toLinearMap e.toContinuousLinearMap.toLinearMap
  let down := projectiveTensorMap one.toLinearMap e.symm.toContinuousLinearMap.toLinearMap
  have hLift (φ : D) (y : Y) : lift (φ ⊗ₜ[ℂ] y) = φ ⊗ₜ[ℂ] e y :=
    TensorProduct.map_tmul _ _ _ _
  have hDown (φ : D) (y : L) : down (φ ⊗ₜ[ℂ] y) = φ ⊗ₜ[ℂ] e.symm y :=
    TensorProduct.map_tmul _ _ _ _
  have hleft : Function.LeftInverse down lift := by
    have hm : down.comp lift = (LinearMap.id : ProjectiveTensor D Y →ₗ[ℂ] _) := by
      apply TensorProduct.ext'
      intro φ y
      change down (lift (φ ⊗ₜ[ℂ] y)) = φ ⊗ₜ[ℂ] y
      rw [hLift, hDown, e.symm_apply_apply]
    exact DFunLike.congr_fun hm
  have hlift : IsUniformInducing lift := AddMonoidHom.isUniformInducing_of_isInducing
    (hleft.isEmbedding (projectiveTensorMap_continuous one e.symm.toContinuousLinearMap)
      (projectiveTensorMap_continuous one e.toContinuousLinearMap)).isInducing
  let S : Set (Set X) := {s | IsVonNBounded ℂ s}
  let post := e.toContinuousLinearMap.postcompUniformConvergenceCLM (σ := RingHom.id ℂ) S
  let T : ProjectiveTensor D Y →L[ℂ] (X →Lᵦ Y) := projectiveTensorToOperators
  let T' : ProjectiveTensor D L →L[ℂ] (X →Lᵦ L) := projectiveTensorToOperators
  have hcomp : post ∘ T = T' ∘ lift := by
    apply congr_arg (fun f : ProjectiveTensor D Y →ₗ[ℂ] (X →Lᵦ L) ↦ (f : _ → _))
      (show post.toLinearMap.comp T.toLinearMap = T'.toLinearMap.comp lift from ?_)
    apply TensorProduct.ext'
    intro φ y
    apply ContinuousLinearMap.ext
    intro x
    change e (T (φ ⊗ₜ[ℂ] y) x) = T' (lift (φ ⊗ₜ[ℂ] y)) x
    rw [hLift]
    change e (φ x • y) = φ x • e y
    exact map_smul e _ _
  apply IsUniformInducing.of_comp T.uniformContinuous post.uniformContinuous
  rw [hcomp]
  exact (projectiveTensorToOperators_isUniformInducing_of_homeomorph hI).comp hlift

end TensorOperatorUniverse

/-- A complete barrelled space with complete nuclear strong dual has the Heine–Borel
property. Evaluation embeds it as a closed subspace of the bidual, where bounded
sets of evaluations are contained in compact polars. -/
private theorem montelSpace_of_nuclearStrongDual [CompleteSpace E] [ContinuousSMul ℂ E]
    [BarrelledSpace ℂ E] [CompleteSpace (StrongDual ℂ E)]
    (h : IsNuclearTVS (StrongDual ℂ E)) : MontelSpace ℂ E := by
  let D := StrongDual ℂ E
  let : PolynormableSpace ℂ D := h.2.1
  let : T2Space D := h.1
  let : ContinuousSMul ℂ D := PolynormableSpace.continuousSMul ℂ D
  let : MontelSpace ℂ D := ⟨fun S hS hbounded ↦
    ((isPrecompactInCompletion_iff_totallyBounded S).mp
      (isPrecompactInCompletion_of_isNuclearTVS D h hbounded)).isCompact_of_isClosed hS⟩
  let j : E →ₗ[ℂ] StrongDual ℂ D := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ)
  have hj : IsEmbedding j := isEmbedding_strongBidual_eval
  have hjUniform : IsUniformInducing j :=
    AddMonoidHom.isUniformInducing_of_isInducing (β := StrongDual ℂ D) (f := j) hj.isInducing
  have hjClosed : IsClosedEmbedding j := ⟨hj, hjUniform.isComplete_range.isClosed⟩
  refine ⟨fun B hB hbounded ↦ ?_⟩
  let U : Set D := {φ | ∀ x ∈ B, φ x ∈ Metric.ball 0 1}
  have hU : U ∈ 𝓝 (0 : D) :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo hbounded (Metric.ball_mem_nhds 0 one_pos)
  refine (hjClosed.isCompact_preimage (isCompact_strongDual_polar hU)).of_isClosed_subset hB ?_
  intro x hx φ hφ
  exact (mem_ball_zero_iff.mp (hφ x hx)).le

omit [T2Space E] in
/-- Transposing a finite-rank operator on the strong dual exchanges its tensor factors,
using evaluation to identify the strong bidual with the original space. -/
private theorem tensorToFiniteRank_transpose [PolynormableSpace ℂ (StrongDual ℂ E)]
    (e : E ≃ₗ[ℂ] StrongDual ℂ (StrongDual ℂ E))
    (he : ∀ (x : E) (φ : StrongDual ℂ E), e x φ = φ x)
    (z : StrongDual ℂ (StrongDual ℂ E) ⊗[ℂ] StrongDual ℂ E)
    (x : E) (φ : StrongDual ℂ E) :
    φ (tensorToFiniteRank ((TensorProduct.map LinearMap.id e.symm.toLinearMap)
      (TensorProduct.comm ℂ _ _ z)) x) =
      tensorToFiniteRank (E := StrongDual ℂ E) (F := StrongDual ℂ E) z φ x := by
  induction z using TensorProduct.inductionOn with
  | tmul l ψ =>
    simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, tensorToFiniteRank_tmul]
    change φ (ψ x • e.symm l) = (l φ • ψ) x
    rw [map_smul, smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [← he, e.apply_symm_apply]
  | add z w hz hw =>
    simp only [map_add, add_apply, hz, hw]

/-- Paper: Remark C.3.1.1, p. 693. If the strong dual of a complete barrelled
space is complete and nuclear, finite-rank endomorphisms approximate the identity
uniformly on bounded subsets of the source. -/
theorem id_mem_closure_boundedFiniteRank_of_nuclearStrongDual [CompleteSpace E]
    [BarrelledSpace ℂ E] [CompleteSpace (StrongDual ℂ E)] (h : IsNuclearTVS (StrongDual ℂ E)) :
    (ContinuousLinearMap.id ℂ E : E →Lᵦ E) ∈
      closure (range (projectiveTensorToOperators (E := E) (F := E))) := by
  let D := StrongDual ℂ E
  let : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  let : PolynormableSpace ℂ D := h.2.1
  let : T2Space D := h.1
  let : MontelSpace ℂ E := montelSpace_of_nuclearStrongDual h
  let j := ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)
  have hj : IsEmbedding j := isEmbedding_strongBidual_eval
  let e := LinearEquiv.ofBijective j ⟨hj.injective, surjective_strongBidual_eval⟩
  let I : E →Lᵦ E := ContinuousLinearMap.id ℂ E
  have htr : 𝓝 I = comap (fun T : E →Lᵦ E ↦ T - I) (𝓝 0) := by
    simpa only [sub_eq_add_neg] using (nhds_translation_add_neg I).symm
  let S : Set (Set E) := {B | IsVonNBounded ℂ B}
  have hS : DirectedOn (· ⊆ ·) S := directedOn_of_sup_mem fun _ _ ↦ IsVonNBounded.union
  have hbasis := UniformConvergenceCLM.hasBasis_nhds_zero (RingHom.id ℂ) E S
    ⟨∅, isVonNBounded_empty ℂ E⟩ hS
  rw [show (ContinuousLinearMap.id ℂ E : E →Lᵦ E) = I from rfl]
  refine (mem_closure_iff_nhds_basis (htr ▸ hbasis.comap _)).mpr ?_
  rintro ⟨B, U⟩ ⟨hB, hU⟩
  -- Test the error in the bidual on a bounded set of functionals.
  have hj0 : 𝓝 (0 : E) = comap j (𝓝 (0 : StrongDual ℂ D)) := by
    simpa only [map_zero] using hj.isInducing.nhds_eq_comap (0 : E)
  rw [hj0] at hU
  obtain ⟨⟨A, r⟩, ⟨hA, hr⟩, hsmall⟩ :=
    ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (σ := RingHom.id ℂ) (E := D) Metric.nhds_basis_ball).comap j).mem_iff.mp hU
  let V : Set D := {φ | ∀ x ∈ B, φ x ∈ Metric.ball 0 r}
  have hV : V ∈ 𝓝 (0 : D) :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo hB (Metric.ball_mem_nhds 0 hr)
  let J := ContinuousLinearMap.id ℂ D
  have hnear : ∀ᶠ T : D →L[ℂ] D in 𝓝 J, ∀ φ ∈ A, (T - J) φ ∈ V := by
    rw [← nhds_translation_add_neg J]
    exact preimage_mem_comap
      (ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA hV)
  have hd := dense_finiteRank_boundedConvergence_of_isNuclearTVS D h D J
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ :=
    ((mem_closure_iff_frequently.mp hd).and_eventually hnear).exists
  -- The transposed approximant has the same scalar errors on these two bounded sets.
  let w : ProjectiveTensor (StrongDual ℂ E) E :=
    TensorProduct.map LinearMap.id e.symm.toLinearMap (TensorProduct.comm ℂ _ _ z)
  refine ⟨projectiveTensorToOperators w, ⟨w, rfl⟩, ?_⟩
  intro x hx
  apply hsmall
  intro φ hφ
  have hzx := hz φ hφ x hx
  change φ (tensorToFiniteRank w x - x) ∈ Metric.ball 0 r
  rw [map_sub, tensorToFiniteRank_transpose e (fun _ _ ↦ rfl) z]
  exact hzx

/-- Postcomposition carries bounded convergence approximation of the identity by
finite-rank operators to approximation of any continuous linear map. -/
private theorem denseRange_projectiveTensorToOperators
    (h : (ContinuousLinearMap.id ℂ E : E →Lᵦ E) ∈
      closure (range (projectiveTensorToOperators (E := E) (F := E)))) :
    DenseRange (projectiveTensorToOperators (E := E) (F := F)) := by
  intro A
  let S : Set (Set E) := {s | IsVonNBounded ℂ s}
  let post : (E →Lᵦ E) →L[ℂ] (E →Lᵦ F) := A.postcompUniformConvergenceCLM S
  let map := TensorProduct.map (LinearMap.id : StrongDual ℂ E →ₗ[ℂ] StrongDual ℂ E) A.toLinearMap
  have hmap : ∀ z : ProjectiveTensor (StrongDual ℂ E) E,
      post (projectiveTensorToOperators z) = projectiveTensorToOperators (map z) := by
    apply DFunLike.congr_fun (f := post.toLinearMap.comp projectiveTensorToOperators.toLinearMap)
      (g := projectiveTensorToOperators.toLinearMap.comp map)
    apply TensorProduct.ext'
    intro φ y
    ext x
    change A (projectiveTensorToOperators (φ ⊗ₜ[ℂ] y) x) =
      projectiveTensorToOperators (map (φ ⊗ₜ[ℂ] y)) x
    simp [map, projectiveTensorToOperators_tmul]
    rfl
  have hsub : post '' range (projectiveTensorToOperators (E := E) (F := E)) ⊆
      range (projectiveTensorToOperators (E := E) (F := F)) := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨map z, (hmap z).symm⟩
  have hA : post (ContinuousLinearMap.id ℂ E) = A := by
    ext x
    rfl
  rw [← hA]
  exact closure_mono hsub (image_closure_subset_closure_image post.continuous (mem_image_of_mem _ h))

/-- Paper: Remark C.3.1.1, p. 693. For complete spaces, with barrelled source
and complete nuclear strong dual, the completed projective tensor is linearly
homeomorphic to the bounded convergence operator space by the canonical map. -/
theorem completedProjectiveTensorToOperators_equiv [CompleteSpace E] [CompleteSpace F]
    [BarrelledSpace ℂ E] [CompleteSpace (StrongDual ℂ E)] (h : IsNuclearTVS (StrongDual ℂ E)) :
    CompleteSpace (E →Lᵦ F) ∧
      ∃ e : Completion (ProjectiveTensor (StrongDual ℂ E) F) ≃L[ℂ] (E →Lᵦ F),
        ∀ z : ProjectiveTensor (StrongDual ℂ E) F, e z = projectiveTensorToOperators z := by
  have := completeSpace_boundedOperators (E := E) (F := F)
  refine ⟨inferInstance, ?_⟩
  have : T2Space (E →Lᵦ F) :=
    UniformConvergenceCLM.t2Space (RingHom.id ℂ) F _ sUnion_isVonNBounded_eq_univ
  let T : ProjectiveTensor (StrongDual ℂ E) F →L[ℂ] (E →Lᵦ F) := projectiveTensorToOperators
  have he : IsUniformInducing T.fromCompletion :=
    Completion.isUniformInducing_extension (projectiveTensorToOperators_isUniformInducing h)
  have hclosed : IsClosed (range T.fromCompletion) := he.isComplete_range.isClosed
  have hdense : DenseRange T := denseRange_projectiveTensorToOperators
      (id_mem_closure_boundedFiniteRank_of_nuclearStrongDual h)
  have hsurj : Function.Surjective T.fromCompletion := fun A ↦
    hclosed.closure_subset_iff.mpr (by
      rintro _ ⟨z, rfl⟩
      exact ⟨z, T.fromCompletion_apply_coe z⟩) (hdense A)
  have hhome : IsHomeomorph T.fromCompletion :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨he.isInducing, he.injective⟩, hsurj⟩
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph
    (LinearEquiv.ofBijective T.fromCompletion.toLinearMap hhome.bijective) hhome,
    T.fromCompletion_apply_coe⟩

/-- Paper: §C.3.1, p. 693. A Banach disc is a bounded balanced convex set whose
linear span, equipped with the Minkowski seminorm of the disc, is separated and complete.
In the paper's Hausdorff setting, boundedness implies the separation condition. -/
structure IsBanachDisc (B : Set F) : Prop where
  bounded : IsVonNBounded ℂ B
  balanced : Balanced ℂ ((↑) ⁻¹' B : Set (Submodule.span ℂ B))
  convex : Convex ℝ ((↑) ⁻¹' B : Set (Submodule.span ℂ B))
  absorbent : Absorbent ℝ ((↑) ⁻¹' B : Set (Submodule.span ℂ B))
  separated : T2Space (WithLocalSeminorm (gaugeSeminorm balanced convex absorbent))
  complete : CompleteSpace (WithLocalSeminorm (gaugeSeminorm balanced convex absorbent))

/-- Paper: §C.3.1, p. 693. The closed unit ball of a Banach space is a Banach disc.
Deviation: This is a check of the disc definition. -/
theorem isBanachDisc_closedUnitBall {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] : IsBanachDisc (Metric.closedBall (0 : X) 1) := by
  let B := Metric.closedBall (0 : X) 1
  let S := Submodule.span ℂ B
  have hball : ((↑) ⁻¹' B : Set S) = Metric.closedBall (0 : S) 1 := rfl
  have hb : Balanced ℂ ((↑) ⁻¹' B : Set S) := by
    rw [hball]
    exact balanced_closedBall_zero
  have hc : Convex ℝ ((↑) ⁻¹' B : Set S) := by
    rw [hball]
    exact convex_closedBall 0 1
  have ha : Absorbent ℝ ((↑) ⁻¹' B : Set S) := by
    rw [hball]
    exact absorbent_nhds_zero (Metric.closedBall_mem_nhds 0 one_pos)
  let p := gaugeSeminorm hb hc ha
  have hp (z : S) : p z = ‖z‖ := by
    change gauge ((↑) ⁻¹' B : Set S) z = ‖z‖
    rw [hball, gauge_closedBall zero_le_one, div_one]
  let f : WithLocalSeminorm p → X := fun x ↦ (x : S).val
  have hf : Isometry f := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    exact (hp ((x : S) - (y : S))).symm
  have hB : Absorbent ℂ B := absorbent_nhds_zero (Metric.closedBall_mem_nhds 0 one_pos)
  have hspan : S = ⊤ := (hB.mono Submodule.subset_span).submodule_eq_top
  have hsurj : Function.Surjective f := fun x ↦ ⟨⟨x, by simp [hspan]⟩, rfl⟩
  exact ⟨NormedSpace.isVonNBounded_closedBall ℂ X 1, hb, hc, ha,
    T2Space.of_injective_continuous (fun _ _ h ↦ Subtype.ext h) hf.continuous,
    (hf.isUniformInducing.completeSpace_congr hsurj).mpr inferInstance⟩

/-- Paper: §C.3.1, p. 694. Nuclearity means that some balanced convex zero-neighborhood
maps into a Banach disc and that the induced operator from the local Banach space
to the disc span, equipped with its Minkowski norm, has a nuclear series. -/
def IsNuclearOperator (A : E →L[ℂ] F) : Prop :=
  ∃ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U)
    (B : Set F) (hB : IsBanachDisc B),
    MapsTo A U B ∧
      ∃ T : LocalBanach (gaugeSeminorm bU cU (absorbent_nhds_zero hU)) →L[ℂ]
        WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent),
        IsBanachNuclear T ∧ ∀ x : E,
          let xU : WithLocalSeminorm (gaugeSeminorm bU cU (absorbent_nhds_zero hU)) := x
          let yB : Submodule.span ℂ B := T xU
          (yB : F) = A x

/-- The image of the scalar closed unit ball under multiplication by a fixed vector
is a Banach disc, since its span is finite-dimensional and its gauge is a norm. -/
private theorem isBanachDisc_toSpanSingleton (y : F) :
    IsBanachDisc (ContinuousLinearMap.toSpanSingleton ℂ y '' Metric.closedBall (0 : ℂ) 1) := by
  let D := Metric.closedBall (0 : ℂ) 1
  let f := ContinuousLinearMap.toSpanSingleton ℂ y
  let B := f '' D
  let S := Submodule.span ℂ B
  have hS : S = f.toLinearMap.range := by
    have hD : Absorbent ℂ D := absorbent_nhds_zero (Metric.closedBall_mem_nhds 0 one_pos)
    have hspan : Submodule.span ℂ D = ⊤ :=
      (hD.mono Submodule.subset_span).submodule_eq_top
    change Submodule.span ℂ (f.toLinearMap '' D) = _
    rw [Submodule.span_image, hspan, Submodule.map_top]
  let g := f.codRestrict S (fun z ↦ hS.symm ▸ LinearMap.mem_range_self f.toLinearMap z)
  have hg : Function.Surjective g := by
    intro z
    have hz : (z : F) ∈ f.toLinearMap.range := hS ▸ z.property
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩
  have himage : ((↑) ⁻¹' B : Set S) = g '' D := by
    ext z
    constructor
    · rintro ⟨w, hw, heq⟩
      exact ⟨w, hw, Subtype.ext heq⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have bB : Balanced ℂ ((↑) ⁻¹' B : Set S) :=
    himage ▸ balanced_closedBall_zero.image g.toLinearMap
  have cB : Convex ℝ ((↑) ⁻¹' B : Set S) :=
    himage ▸ (convex_closedBall (0 : ℂ) 1).linear_image (g.toLinearMap.restrictScalars ℝ)
  have aB : Absorbent ℝ ((↑) ⁻¹' B : Set S) :=
    himage ▸ Absorbent.image_of_surjective
      (f := g.toLinearMap.restrictScalars ℝ) hg
      (absorbent_nhds_zero (Metric.closedBall_mem_nhds 0 one_pos))
  -- Boundedness makes the gauge a norm, and the span is finite-dimensional.
  let pB := gaugeSeminorm bB cB aB
  have hb : IsVonNBounded ℝ ((↑) ⁻¹' B : Set S) :=
    himage ▸ ((isCompact_closedBall (0 : ℂ) 1).image g.continuous).isVonNBounded ℝ
  let : NormedAddCommGroup (WithLocalSeminorm pB) :=
    NormedAddCommGroup.ofSeparation fun z hz ↦ (gauge_eq_zero aB hb).mp hz
  let : FiniteDimensional ℂ (WithLocalSeminorm pB) :=
    Module.Finite.of_surjective (show ℂ →ₗ[ℂ] WithLocalSeminorm pB from g.toLinearMap) hg
  exact ⟨(NormedSpace.isVonNBounded_closedBall ℂ ℂ 1).image f, bB, cB, aB,
    inferInstance, FiniteDimensional.completeSpace ℂ (WithLocalSeminorm pB)⟩

/-- Paper: §C.3.1, p. 694. A continuous rank-one operator is nuclear.
Deviation: This is a check of the local factorization definition. -/
theorem isNuclearOperator_smulRight (φ : E →L[ℂ] ℂ) (y : F) :
    IsNuclearOperator (φ.smulRight y) := by
  let B := ContinuousLinearMap.toSpanSingleton ℂ y '' Metric.closedBall (0 : ℂ) 1
  have hB : IsBanachDisc B := isBanachDisc_toSpanSingleton y
  -- The source gauge is the seminorm x ↦ ‖φ x‖, so φ extends to the completion.
  let q := (normSeminorm ℂ ℂ).comp φ.toLinearMap
  let U := q.ball 0 1
  have hU : U ∈ 𝓝 (0 : E) := by
    exact (Seminorm.continuous_iff (p := q) one_pos).mp φ.continuous.norm
  let pU := gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1) (absorbent_nhds_zero hU)
  let ψ := (show WithLocalSeminorm pU →ₗ[ℂ] ℂ from φ.toLinearMap).mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * gauge U x
    rw [one_mul]
    exact ge_of_eq (congrFun (q.restrictScalars ℝ).gauge_ball x))
  let yB : Submodule.span ℂ B :=
    ⟨y, Submodule.subset_span ⟨1, by simp [Metric.mem_closedBall], by simp⟩⟩
  refine ⟨U, hU, q.balanced_ball_zero 1, q.convex_ball 0 1, B, hB, ?_,
    ψ.fromCompletion.smulRight yB, isBanachNuclear_smulRight _ _, ?_⟩
  · intro x hx
    refine ⟨φ x, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖φ x‖ < 1 from q.mem_ball_zero.mp hx).le
  · intro x
    let xU : WithLocalSeminorm pU := x
    change (↑(show Submodule.span ℂ B from ψ.fromCompletion xU • yB) : F) = φ x • y
    rw [ψ.fromCompletion_apply_coe]
    rfl

/-- Paper: (C.3.1.3), p. 694. A nuclear presentation is a pointwise operator sum
of rank-one maps with summable coefficients, equicontinuous functionals and
vectors in a common Banach disc.
Deviation: All three families use the same summation index, starting at zero. -/
structure NuclearPresentation (A : E →L[ℂ] F) where
  coeff : ℕ → ℂ
  functional : ℕ → E →L[ℂ] ℂ
  disc : Set F
  isBanachDisc : IsBanachDisc disc
  vector : ℕ → Submodule.span ℂ disc
  vector_mem : ∀ n, (vector n : F) ∈ disc
  summable_coeff : Summable (fun n ↦ ‖coeff n‖)
  equicontinuous : EquicontinuousAt (fun n x ↦ functional n x) 0
  hasSum : ∀ x, HasSum (fun n ↦ (coeff n * functional n x) • (vector n : F)) (A x)

-- Keep the section hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (C.3.1.3), p. 694. A rank-one map can be presented with one term and
the given functional, with any prescribed nonzero coefficient for that term.
Deviation: This is a check of the normalization in the presentation definition. -/
theorem nuclearPresentation_smulRight (φ : E →L[ℂ] ℂ) (y : F) (c : ℂ) (hc : c ≠ 0) :
    ∃ r : NuclearPresentation (φ.smulRight y),
      r.coeff 0 = c ∧ r.functional 0 = φ ∧ (r.vector 0 : F) = c⁻¹ • y ∧
        ∀ n, r.coeff (n + 1) = 0 := by
  let z : F := c⁻¹ • y
  let B := ContinuousLinearMap.toSpanSingleton ℂ z '' Metric.closedBall (0 : ℂ) 1
  have hz : z ∈ B := ⟨1, by simp [Metric.mem_closedBall], by simp⟩
  let r : NuclearPresentation (φ.smulRight y) :=
    { coeff := fun n ↦ if n = 0 then c else 0
      functional := fun _ ↦ φ
      disc := B
      isBanachDisc := isBanachDisc_toSpanSingleton z
      vector := fun _ ↦ ⟨z, Submodule.subset_span hz⟩
      vector_mem := fun _ ↦ hz
      summable_coeff := by
        simpa only [apply_ite, norm_zero] using (hasSum_ite_eq (0 : ℕ) ‖c‖).summable
      equicontinuous :=
        ((equicontinuousAt_unique (F := fun (_ : Unit) x ↦ φ x)).mpr
          φ.continuous.continuousAt).comp (fun _ ↦ ())
      hasSum := by
        intro x
        rw [ContinuousLinearMap.smulRight_apply]
        refine (hasSum_ite_eq (0 : ℕ) (φ x • y)).congr_fun ?_
        intro n
        by_cases hn : n = 0
        · simp only [hn, ite_true, z, mul_comm c, mul_smul, smul_inv_smul₀ hc]
        · simp [hn] }
  exact ⟨r, by simp [r], rfl, rfl, fun n ↦ by simp [r]⟩

omit [IsUniformAddGroup F] [T2Space F] in
/-- The inclusion of a Banach disc's gauge space into the ambient space is continuous. -/
private theorem continuous_banachDisc_subtype {B : Set F} (hB : IsBanachDisc B) :
    Continuous (fun z : WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent) ↦
      (show Submodule.span ℂ B from z).val) := by
  let G := WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent)
  let i : G →ₗ[ℂ] F := (Submodule.span ℂ B).subtype
  let hF := PolynormableSpace.withSeminorms ℂ F
  refine hF.continuous_of_continuous_comp i fun j ↦ ?_
  obtain ⟨R, _, hR⟩ := hF.isVonNBounded_iff_seminorm_bounded.mp hB.bounded j
  refine Seminorm.continuous' (r := R) (mem_of_superset (Metric.ball_mem_nhds (0 : G) one_pos) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzB : (show Submodule.span ℂ B from z) ∈ ((↑) ⁻¹' B : Set (Submodule.span ℂ B)) :=
    setOfPred_gauge_lt_one_subset_self hB.convex hB.absorbent.zero_mem hB.absorbent hz
  rw [Seminorm.mem_closedBall_zero]
  exact (hR (i z) hzB).le

/-- In a Banach-space series with bounded factors, summable coefficients can absorb the
rescaling needed to make the two factors norm-null. -/
private theorem isBanachNuclear_of_bounded_series {X Y : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℂ X] [SeminormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : X →L[ℂ] Y) (c : ℕ → ℂ) (φ : ℕ → X →L[ℂ] ℂ) (y : ℕ → Y)
    (hc : Summable (fun n ↦ ‖c n‖)) (hφ : ∃ C, ∀ n, ‖φ n‖ ≤ C)
    (hy : ∀ n, ‖y n‖ ≤ 1) (hT : ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T x)) :
    IsBanachNuclear T := by
  -- Add a positive geometric series so that every tail is strictly positive.
  let a (n : ℕ) := ‖c n‖ + (1 / 2 : ℝ) ^ n
  have ha : Summable a := hc.add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have ha_pos (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let t (n : ℕ) := ∑' k : ℕ, a (k + n)
  have ht_add (n : ℕ) : t n = a n + t (n + 1) := by
    simpa only [t, zero_add, Nat.add_right_comm, Nat.add_assoc] using
      ((summable_nat_add_iff n).mpr ha).tsum_eq_zero_add
  have ht_pos (n : ℕ) : 0 < t n :=
    ((summable_nat_add_iff n).mpr ha).tsum_pos (fun k ↦ (ha_pos (k + n)).le) 0 (ha_pos (0 + n))
  let s (n : ℕ) := Real.sqrt (Real.sqrt (t n))
  have hs_pos (n : ℕ) : 0 < s n := Real.sqrt_pos_of_pos (Real.sqrt_pos_of_pos (ht_pos n))
  have hs_sq (n : ℕ) : s n * s n = Real.sqrt (t n) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs_lim : Tendsto s atTop (𝓝 0) := by
    simpa only [s, t, Real.sqrt_zero] using (tendsto_sum_nat_add a).sqrt.sqrt
  let d (n : ℕ) : ℂ := s n
  have hd_ne (n : ℕ) : d n ≠ 0 := Complex.ofReal_ne_zero.mpr (hs_pos n).ne'
  have hd_norm (n : ℕ) : ‖d n‖ = s n := by
    dsimp [d]
    rw [Complex.norm_real, Real.norm_of_nonneg (hs_pos n).le]
  refine ⟨fun n ↦ c n / (d n * d n), fun n ↦ d n • φ n, fun n ↦ d n • y n, ?_, ?_, ?_, ?_⟩
  · -- The rescaled coefficient norms are dominated by a telescoping series.
    have hbound (n : ℕ) : ‖c n‖ / Real.sqrt (t n) ≤
        2 * (Real.sqrt (t n) - Real.sqrt (t (n + 1))) := by
      have hle : Real.sqrt (t (n + 1)) ≤ Real.sqrt (t n) :=
        Real.sqrt_le_sqrt (by linarith [ht_add n, ha_pos n])
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos (ht_pos n))]
      have hdiff := mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hle)
      nlinarith [Real.mul_self_sqrt (ht_pos n).le, Real.mul_self_sqrt (ht_pos (n + 1)).le,
        ht_add n, show ‖c n‖ ≤ a n from le_add_of_nonneg_right (by positivity)]
    refine summable_of_sum_range_le (c := 2 * Real.sqrt (t 0)) (fun n ↦ norm_nonneg _) fun N ↦ ?_
    calc
      _ ≤ ∑ n ∈ Finset.range N, 2 * (Real.sqrt (t n) - Real.sqrt (t (n + 1))) :=
        Finset.sum_le_sum fun n _ ↦ by rw [norm_div, norm_mul, hd_norm, hs_sq]; exact hbound n
      _ ≤ _ := by
        rw [← Finset.mul_sum, Finset.sum_range_sub']
        linarith [Real.sqrt_nonneg (t N)]
  · obtain ⟨C, hC⟩ := hφ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n ↦ s n * C) atTop (𝓝 0) by simpa using hs_lim.mul_const C)
      (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    rw [norm_smul, hd_norm]
    exact mul_le_mul_of_nonneg_left (hC n) (hs_pos n).le
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs_lim
      (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    rw [norm_smul, hd_norm]
    exact mul_le_of_le_one_right (hs_pos n).le (hy n)
  · intro x
    refine (hT x).congr_fun fun n ↦ ?_
    simp only [smul_apply, smul_smul, smul_eq_mul]
    congr 1
    calc
      _ = (c n / (d n * d n) * (d n * d n)) * φ n x := by ring
      _ = c n * φ n x := by rw [div_mul_cancel₀ _ (mul_ne_zero (hd_ne n) (hd_ne n))]

/-- Paper: Lemma C.3.1.2, p. 694. A continuous linear operator is nuclear exactly
when it has a nuclear presentation. -/
theorem isNuclearOperator_iff_nonempty_presentation (A : E →L[ℂ] F) :
    IsNuclearOperator A ↔ Nonempty (NuclearPresentation A) := by
  constructor
  · rintro ⟨U, hU, bU, cU, B, hB, _, T, ⟨c, φ, y, hc, hφ, hy, hT⟩, hA⟩
    let p := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
    let G := WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent)
    let i : E →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
    have hi : Continuous i :=
      (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng (LocalBanach p) i
        ⟨{⟨p, continuous_gauge cU hU⟩}, 1, by
          simpa using (show (normSeminorm ℂ _).comp i ≤ p from
            fun x ↦ (localBanach_norm_coe p x).le)⟩
    let j : G →L[ℂ] F := ⟨(Submodule.span ℂ B).subtype, continuous_banachDisc_subtype hB⟩
    obtain ⟨R, hR, hyR⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_lt
    obtain ⟨C, _, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    let r : ℂ := R
    have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have hr_norm : ‖r‖ = R := by
      dsimp [r]
      rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
    refine ⟨⟨fun n ↦ c n * r, fun n ↦ (φ n).comp ⟨i, hi⟩, B, hB,
      fun n ↦ (r⁻¹ • y n : G), ?_, ?_, ?_, ?_⟩⟩
    · intro n
      apply setOfPred_gauge_lt_one_subset_self hB.convex hB.absorbent.zero_mem hB.absorbent
      change ‖(r⁻¹ • y n : G)‖ < 1
      rw [norm_smul, norm_inv, hr_norm, inv_mul_lt_iff₀ hR, mul_one]
      exact hyR _ (mem_range_self n)
    · simpa only [norm_mul] using hc.mul_right ‖r‖
    · refine Metric.equicontinuousAt_of_continuity_modulus (fun x ↦ C * ‖i x‖) ?_ _
        (Eventually.of_forall fun x n ↦ ?_)
      · have hi0 : Tendsto i (𝓝 0) (𝓝 0) := by simpa only [map_zero] using hi.tendsto 0
        simpa only [norm_zero, mul_zero] using hi0.norm.const_mul C
      · change dist (φ n (i 0)) (φ n (i x)) ≤ C * ‖i x‖
        rw [map_zero i, map_zero, dist_zero_left]
        exact ((φ n).le_opNorm (i x)).trans
          (mul_le_mul_of_nonneg_right (hφC _ (mem_range_self n)) (norm_nonneg _))
    · intro x
      have hs := j.hasSum (hT (i x))
      rw [show j (T (i x)) = A x from hA x] at hs
      refine hs.congr_fun fun n ↦ ?_
      change (c n * r * φ n (i x)) • j (r⁻¹ • y n) =
        j ((c n * φ n (i x)) • y n)
      rw [map_smul, map_smul, smul_smul, mul_right_comm (c n) r, mul_inv_cancel_right₀ hr]
  · rintro ⟨r⟩
    have hseminorm := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae
      (fun n ↦ (r.functional n).toLinearMap)).out 1 4
    obtain ⟨p, hp, hφ⟩ := (hseminorm.mp r.equicontinuous) ()
    -- Scale the source gauge so the resulting operator has norm strictly less than one.
    let C := (∑' n, ‖r.coeff n‖) + 1
    have hC : 0 < C := by dsimp [C]; positivity
    let q : Seminorm ℂ E := C.toNNReal • p
    have hq (x : E) : q x = C * p x := by
      change (C.toNNReal • p) x = _
      rw [smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hC.le]
    have hq_cont : Continuous q := by
      change Continuous (fun x ↦ q x)
      simp_rw [hq]
      exact hp.const_mul C
    let U := q.ball 0 1
    have hU : U ∈ 𝓝 0 := (Seminorm.continuous_iff one_pos).mp hq_cont
    let bU := q.balanced_ball_zero 1
    let cU := q.convex_ball 0 1
    let pU := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
    let X := LocalBanach pU
    let i : E →ₗ[ℂ] X := Completion.toComplL.toLinearMap.comp LinearMap.id
    have hi : DenseRange i := Completion.denseRange_coe (α := WithLocalSeminorm pU)
    have hi_norm (x : E) : ‖i x‖ = q x :=
      (localBanach_norm_coe pU x).trans (congrFun (q.restrictScalars ℝ).gauge_ball x)
    let G := WithLocalSeminorm
      (gaugeSeminorm r.isBanachDisc.balanced r.isBanachDisc.convex r.isBanachDisc.absorbent)
    let : CompleteSpace G := r.isBanachDisc.complete
    let j : G →L[ℂ] F := ⟨(Submodule.span ℂ r.disc).subtype,
      continuous_banachDisc_subtype r.isBanachDisc⟩
    let y (n : ℕ) : G := r.vector n
    have hy (n : ℕ) : ‖y n‖ ≤ 1 := gauge_le_one_of_mem
      (show (r.vector n) ∈ ((↑) ⁻¹' r.disc : Set (Submodule.span ℂ r.disc)) from r.vector_mem n)
    have hbound (n : ℕ) (x : E) : ‖r.functional n x‖ ≤ C⁻¹ * ‖i x‖ := by
      rw [hi_norm, hq, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
      exact hφ n x
    let ψ (n : ℕ) : X →L[ℂ] ℂ := (r.functional n).toLinearMap.extendOfNorm i
    have hψ (n : ℕ) : ‖ψ n‖ ≤ C⁻¹ :=
      LinearMap.opNorm_extendOfNorm_le hi (inv_nonneg.mpr hC.le) (hbound n)
    have hψi (n : ℕ) (x : E) : ψ n (i x) = r.functional n x :=
      LinearMap.extendOfNorm_eq hi ⟨C⁻¹, hbound n⟩ x
    let term (n : ℕ) : X →L[ℂ] G := r.coeff n • (ψ n).smulRight (y n)
    have hterm (n : ℕ) : ‖term n‖ ≤ ‖r.coeff n‖ * C⁻¹ := by
      change ‖r.coeff n • (ψ n).smulRight (y n)‖ ≤ _
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_of_le_one_right (norm_nonneg _) (hy n)).trans (hψ n)) (norm_nonneg _)
    have hterm_norm : Summable (fun n ↦ ‖term n‖) :=
      (r.summable_coeff.mul_right C⁻¹).of_nonneg_of_le (fun n ↦ norm_nonneg _) hterm
    let T : X →L[ℂ] G := ∑' n, term n
    have hseries (x : X) : HasSum (fun n ↦ (r.coeff n * ψ n x) • y n) (T x) := by
      simpa only [term, ContinuousLinearMap.apply_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_smul] using
        (ContinuousLinearMap.apply ℂ G x).hasSum hterm_norm.of_norm.hasSum
    have hA (x : E) : j (T (i x)) = A x := by
      have hjy (n : ℕ) : j (y n) = (r.vector n : F) := rfl
      apply HasSum.unique _ (r.hasSum x)
      simpa only [map_smul, hψi, hjy] using j.hasSum (hseries (i x))
    refine ⟨U, hU, bU, cU, r.disc, r.isBanachDisc, ?_, T,
      isBanachNuclear_of_bounded_series T r.coeff ψ y r.summable_coeff ⟨C⁻¹, hψ⟩ hy hseries, hA⟩
    intro x hx
    rw [← hA x]
    apply setOfPred_gauge_lt_one_subset_self r.isBanachDisc.convex
      r.isBanachDisc.absorbent.zero_mem r.isBanachDisc.absorbent
    change ‖T (i x)‖ < 1
    have hT : ‖T‖ ≤ (∑' n, ‖r.coeff n‖) * C⁻¹ := by
      refine (norm_tsum_le_tsum_norm hterm_norm).trans ?_
      rw [← r.summable_coeff.tsum_mul_right]
      exact hterm_norm.tsum_le_tsum hterm (r.summable_coeff.mul_right C⁻¹)
    have hT_one : ‖T‖ < 1 := hT.trans_lt (by
      rw [mul_inv_lt_iff₀ hC, one_mul]
      exact lt_add_one _)
    exact ((T.le_opNorm (i x)).trans
      (mul_le_of_le_one_right (norm_nonneg _) (by simpa only [hi_norm] using
        (q.mem_ball_zero.mp hx).le))).trans_lt hT_one

/-- Paper: Lemma C.3.1.2, p. 694. A nuclear operator admits a presentation with
functionals tending to zero uniformly on one zero-neighborhood and vectors
tending to zero for the gauge norm of their disc. -/
theorem exists_nuclearPresentation_tendsto_zero (A : E →L[ℂ] F) (hA : IsNuclearOperator A) :
    ∃ (r : NuclearPresentation A) (U : Set E), U ∈ 𝓝 0 ∧
      TendstoUniformlyOn (fun n x ↦ r.functional n x) 0 atTop U ∧
      Tendsto (fun n ↦ gauge ((↑) ⁻¹' r.disc : Set (Submodule.span ℂ r.disc)) (r.vector n))
        atTop (𝓝 0) := by
  obtain ⟨U, hU, bU, cU, B, hB, _, T, ⟨c, φ, y, hc, hφ, hy, hT⟩, hA⟩ := hA
  let p := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  let G := WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent)
  let i : E →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hi : Continuous i :=
    (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng (LocalBanach p) i
      ⟨{⟨p, continuous_gauge cU hU⟩}, 1, by
        simpa using (show (normSeminorm ℂ _).comp i ≤ p from
          fun x ↦ (localBanach_norm_coe p x).le)⟩
  let j : G →L[ℂ] F := ⟨(Submodule.span ℂ B).subtype, continuous_banachDisc_subtype hB⟩
  obtain ⟨R, hR, hyR⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_lt
  obtain ⟨C, _, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
  let r : ℂ := R
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hr_norm : ‖r‖ = R := by
    dsimp [r]
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  let pres : NuclearPresentation A :=
    { coeff := fun n ↦ c n * r
      functional := fun n ↦ (φ n).comp ⟨i, hi⟩
      disc := B
      isBanachDisc := hB
      vector := fun n ↦ (r⁻¹ • y n : G)
      vector_mem := by
        intro n
        apply setOfPred_gauge_lt_one_subset_self hB.convex hB.absorbent.zero_mem hB.absorbent
        change ‖(r⁻¹ • y n : G)‖ < 1
        rw [norm_smul, norm_inv, hr_norm, inv_mul_lt_iff₀ hR, mul_one]
        exact hyR _ (mem_range_self n)
      summable_coeff := by simpa only [norm_mul] using hc.mul_right ‖r‖
      equicontinuous := by
        refine Metric.equicontinuousAt_of_continuity_modulus (fun x ↦ C * ‖i x‖) ?_ _
          (Eventually.of_forall fun x n ↦ ?_)
        · have hi0 : Tendsto i (𝓝 0) (𝓝 0) := by simpa only [map_zero] using hi.tendsto 0
          simpa only [norm_zero, mul_zero] using hi0.norm.const_mul C
        · change dist (φ n (i 0)) (φ n (i x)) ≤ C * ‖i x‖
          rw [map_zero i, map_zero, dist_zero_left]
          exact ((φ n).le_opNorm (i x)).trans
            (mul_le_mul_of_nonneg_right (hφC _ (mem_range_self n)) (norm_nonneg _))
      hasSum := by
        intro x
        have hs := j.hasSum (hT (i x))
        rw [show j (T (i x)) = A x from hA x] at hs
        refine hs.congr_fun fun n ↦ ?_
        change (c n * r * φ n (i x)) • j (r⁻¹ • y n) =
          j ((c n * φ n (i x)) • y n)
        rw [map_smul, map_smul, smul_smul, mul_right_comm (c n) r, mul_inv_cancel_right₀ hr] }
  refine ⟨pres, U, hU, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hnorm : Tendsto (fun n ↦ ‖φ n‖) atTop (𝓝 0) := by
      simpa using hφ.norm
    filter_upwards [(Metric.tendsto_nhds.mp hnorm) ε hε] with n hn x hx
    have hiU : ‖i x‖ ≤ 1 := by
      change ‖((show WithLocalSeminorm p from x) : LocalBanach p)‖ ≤ 1
      exact (localBanach_norm_coe p (show WithLocalSeminorm p from x)).le.trans
        (gauge_le_one_of_mem hx)
    have hn' : ‖φ n‖ < ε := by simpa [Real.dist_eq] using hn
    change dist 0 (φ n (i x)) < ε
    rw [dist_zero_left]
    exact ((φ n).le_opNorm (i x)).trans_lt
      ((mul_le_of_le_one_right (norm_nonneg _) hiU).trans_lt hn')
  · change Tendsto (fun n ↦ ‖(r⁻¹ • y n : G)‖) atTop (𝓝 0)
    simpa using (hy.const_smul r⁻¹).norm

end LocallyConvexOperators

section NormedTensor

open scoped NNReal

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The cost of a finite decomposition is the sum of the products of the factor norms. -/
private def tensorDecompositionCost (l : List (X × Y)) : ℝ :=
  (l.map fun p ↦ ‖p.1‖ * ‖p.2‖).sum

omit [NormedSpace ℂ X] [NormedSpace ℂ Y] in
/-- Each term contributing to the cost of a decomposition is nonnegative. -/
private theorem tensorDecompositionCost_nonneg (l : List (X × Y)) :
    0 ≤ tensorDecompositionCost l := by
  refine List.sum_nonneg fun x hx ↦ ?_
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  positivity

/-- Finite lists of pairs representing a given algebraic tensor. -/
private def TensorDecompositions (z : X ⊗[ℂ] Y) :=
  {l : List (X × Y) // (l.map fun p ↦ p.1 ⊗ₜ[ℂ] p.2).sum = z}

/-- Concatenation represents addition of tensors. -/
private def TensorDecompositions.append {z w : X ⊗[ℂ] Y}
    (l : TensorDecompositions z) (m : TensorDecompositions w) : TensorDecompositions (z + w) :=
  ⟨l.val ++ m.val, by rw [List.map_append, List.sum_append, l.property, m.property]⟩

/-- Every algebraic tensor has a finite pure-tensor decomposition. -/
private instance (z : X ⊗[ℂ] Y) : Nonempty (TensorDecompositions z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact ⟨⟨[(x, y)], by simp⟩⟩
  | add z w hz hw => exact ⟨hz.some.append hw.some⟩

/-- The costs of all decompositions of a tensor are bounded below by zero. -/
private theorem bddBelow_tensorDecompositionCost (z : X ⊗[ℂ] Y) :
    BddBelow (range fun l : TensorDecompositions z ↦ tensorDecompositionCost l.val) :=
  ⟨0, forall_mem_range.mpr fun l ↦ tensorDecompositionCost_nonneg l.val⟩

/-- The projective seminorm is the infimum of the costs of finite pure-tensor decompositions. -/
private def banachProjectiveSeminorm : Seminorm ℂ (X ⊗[ℂ] Y) := by
  refine Seminorm.ofSMulLE
    (fun z ↦ ⨅ l : TensorDecompositions z, tensorDecompositionCost l.val) ?_ ?_ ?_
  · refine le_antisymm (ciInf_le (bddBelow_tensorDecompositionCost 0) ⟨[], rfl⟩) ?_
    exact le_ciInf fun l ↦ tensorDecompositionCost_nonneg l.val
  · intro z w
    refine le_ciInf_add_ciInf fun l m ↦ ciInf_le_of_le (bddBelow_tensorDecompositionCost (z + w))
      (l.append m) ?_
    simp [tensorDecompositionCost, TensorDecompositions.append]
  · intro c z
    rw [Real.mul_iInf_of_nonneg (norm_nonneg c)]
    refine le_ciInf fun l ↦ ciInf_le_of_le (bddBelow_tensorDecompositionCost (c • z))
      ⟨l.val.map (fun p ↦ (c • p.1, p.2)), ?_⟩ ?_
    · simp only [List.map_map, Function.comp_def, ← TensorProduct.smul_tmul']
      have hm := List.smul_sum (r := c) (l := l.val.map fun p ↦ p.1 ⊗ₜ[ℂ] p.2)
      rw [l.property, List.map_map] at hm
      exact hm.symm
    · simp only [tensorDecompositionCost, List.map_map, Function.comp_def, norm_smul,
        mul_assoc, List.sum_map_mul_left, le_refl]

/-- Tensors of small projective seminorm admit finite decompositions of small cost. -/
private theorem exists_decomposition_of_projectiveSeminorm_lt (z : X ⊗[ℂ] Y) {r : ℝ}
    (hr : banachProjectiveSeminorm z < r) :
    ∃ l : List (X × Y), (l.map fun p ↦ p.1 ⊗ₜ[ℂ] p.2).sum = z ∧
      tensorDecompositionCost l < r := by
  change (⨅ l : TensorDecompositions z, tensorDecompositionCost l.val) < r at hr
  obtain ⟨l, hl⟩ := (ciInf_lt_iff (bddBelow_tensorDecompositionCost z)).mp hr
  exact ⟨l.val, l.property, hl⟩

/-- The projective seminorm is bounded on an elementary tensor by the product of norms. -/
private theorem projectiveSeminorm_tmul_le (x : X) (y : Y) :
    banachProjectiveSeminorm (x ⊗ₜ[ℂ] y) ≤ ‖x‖ * ‖y‖ := by
  change (⨅ l : TensorDecompositions (x ⊗ₜ[ℂ] y), tensorDecompositionCost l.val) ≤ _
  simpa only [tensorDecompositionCost, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] using
    ciInf_le (bddBelow_tensorDecompositionCost (x ⊗ₜ[ℂ] y)) ⟨[(x, y)], by simp⟩

/-- A seminorm bounded on pure tensors by the product of norms is bounded by the
projective seminorm with the same constant. -/
private theorem seminorm_le_banachProjectiveSeminorm (q : Seminorm ℂ (X ⊗[ℂ] Y)) {C : ℝ}
    (hC : 0 ≤ C) (hq : ∀ x y, q (x ⊗ₜ[ℂ] y) ≤ C * (‖x‖ * ‖y‖)) (z : X ⊗[ℂ] Y) :
    q z ≤ C * banachProjectiveSeminorm z := by
  have hlist (l : List (X × Y)) : q ((l.map fun p ↦ p.1 ⊗ₜ[ℂ] p.2).sum) ≤
      C * tensorDecompositionCost l := by
    induction l with
    | nil => simp [tensorDecompositionCost]
    | cons p l ih =>
      simp only [tensorDecompositionCost, List.map_cons, List.sum_cons, mul_add] at ih ⊢
      exact (map_add_le_add q _ _).trans (add_le_add (hq p.1 p.2) ih)
  change q z ≤ C * ⨅ l : TensorDecompositions z, tensorDecompositionCost l.val
  rw [Real.mul_iInf_of_nonneg hC]
  refine le_ciInf fun l ↦ le_of_eq_of_le (congrArg q l.property.symm) (hlist l.val)

/-- A vector divided by its norm, with the zero vector mapped to zero. -/
private def normalizedFactor (x : X) : X := (‖x‖ : ℂ)⁻¹ • x

/-- A normalized factor lies in the closed unit ball. -/
private theorem norm_normalizedFactor_le_one (x : X) : ‖normalizedFactor x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, normalizedFactor]
  · rw [normalizedFactor, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Multiplying a normalized factor by the original norm restores the vector. -/
private theorem norm_smul_normalizedFactor (x : X) : (‖x‖ : ℂ) • normalizedFactor x = x := by
  by_cases hx : x = 0
  · simp [hx, normalizedFactor]
  · exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)) x

/-- The projective seminorm belongs to the family defining the projective tensor topology. -/
private theorem banachProjectiveSeminorm_continuousAt_tmul :
    ContinuousAt (fun v : X × Y ↦ banachProjectiveSeminorm (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
  have h : Continuous (fun v : X × Y ↦ ‖v.1‖ * ‖v.2‖) :=
    continuous_fst.norm.mul continuous_snd.norm
  rw [ContinuousAt, Prod.fst_zero, Prod.snd_zero, TensorProduct.zero_tmul, map_zero]
  have h' : Tendsto (fun v : X × Y ↦ ‖v.1‖ * ‖v.2‖) (𝓝 0) (𝓝 0) := by
    simpa only [Prod.fst_zero, Prod.snd_zero, norm_zero, mul_zero] using h.tendsto (0 : X × Y)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h'
    (fun v : X × Y ↦ apply_nonneg banachProjectiveSeminorm (v.1 ⊗ₜ[ℂ] v.2))
    (fun v ↦ projectiveSeminorm_tmul_le v.1 v.2)

/-- A generating seminorm of the projective topology is bounded by a multiple of the
projective seminorm. -/
private theorem bound_of_projective_generator (q : Seminorm ℂ (X ⊗[ℂ] Y))
    (hq : ContinuousAt (fun v : X × Y ↦ q (v.1 ⊗ₜ[ℂ] v.2)) 0) :
    ∃ C : ℝ≥0, ∀ z, q z ≤ C * banachProjectiveSeminorm z := by
  have h : {v : X × Y | q (v.1 ⊗ₜ[ℂ] v.2) < 1} ∈ 𝓝 0 :=
    hq.preimage_mem_nhds (t := Iio 1) (by simpa using Iio_mem_nhds (α := ℝ) one_pos)
  obtain ⟨δ, hδ, hδq⟩ := Metric.mem_nhds_iff.mp h
  let a : ℂ := ((δ / 2 : ℝ) : ℂ)
  have ha : ‖a‖ = δ / 2 := by simp [a, abs_of_pos hδ]
  have ha₀ : 0 < ‖a‖ := by rw [ha]; positivity
  refine ⟨‖a‖₊⁻¹ * ‖a‖₊⁻¹, seminorm_le_banachProjectiveSeminorm q (by positivity) ?_⟩
  intro x y
  let x' := normalizedFactor x
  let y' := normalizedFactor y
  have hball : (a • x', a • y') ∈ Metric.ball (0 : X × Y) δ := by
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, norm_smul, norm_smul, ha]
    exact ⟨(mul_le_of_le_one_right (by positivity) (norm_normalizedFactor_le_one x)).trans_lt
        (by linarith),
      (mul_le_of_le_one_right (by positivity) (norm_normalizedFactor_le_one y)).trans_lt
        (by linarith)⟩
  have hunit : q (x' ⊗ₜ[ℂ] y') ≤ ‖a‖⁻¹ * ‖a‖⁻¹ := by
    have hlt : q ((a • x') ⊗ₜ[ℂ] (a • y')) < 1 := hδq hball
    rw [TensorProduct.smul_tmul_smul, map_smul_eq_mul, norm_mul] at hlt
    calc
      _ ≤ 1 / (‖a‖ * ‖a‖) :=
        (le_div_iff₀ (mul_pos ha₀ ha₀)).mpr (by simpa only [mul_comm] using hlt.le)
      _ = _ := by rw [one_div, mul_inv]
  calc
    q (x ⊗ₜ[ℂ] y) = (‖x‖ * ‖y‖) * q (x' ⊗ₜ[ℂ] y') := by
      conv_lhs => rw [← norm_smul_normalizedFactor x, ← norm_smul_normalizedFactor y]
      rw [TensorProduct.smul_tmul_smul, map_smul_eq_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg x),
        Real.norm_of_nonneg (norm_nonneg y)]
    _ ≤ _ := by
      change _ ≤ (‖a‖⁻¹ * ‖a‖⁻¹) * (‖x‖ * ‖y‖)
      rw [mul_comm (‖a‖⁻¹ * ‖a‖⁻¹)]
      exact mul_le_mul_of_nonneg_left hunit (by positivity)

/-- The identity from the projective tensor topology to the projective seminorm topology. -/
private def toProjectiveSeminorm :
    ProjectiveTensor X Y →L[ℂ] WithLocalSeminorm (banachProjectiveSeminorm (X := X) (Y := Y)) := by
  let hP := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  let W := WithLocalSeminorm (banachProjectiveSeminorm (X := X) (Y := Y))
  let i : ProjectiveTensor X Y →ₗ[ℂ] W := LinearMap.id
  refine ⟨i, (norm_withSeminorms ℂ W).continuous_of_continuous_comp i fun _ ↦ ?_⟩
  exact hP.continuous_seminorm ⟨_, banachProjectiveSeminorm_continuousAt_tmul⟩

/-- The identity from the projective seminorm topology to the projective tensor topology. -/
private def fromProjectiveSeminorm :
    WithLocalSeminorm (banachProjectiveSeminorm (X := X) (Y := Y)) →L[ℂ] ProjectiveTensor X Y := by
  let hP := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  refine ⟨LinearMap.id, hP.continuous_of_continuous_comp _ fun ⟨q, hq⟩ ↦ ?_⟩
  obtain ⟨C, hC⟩ := bound_of_projective_generator q hq
  let W := WithLocalSeminorm (banachProjectiveSeminorm (X := X) (Y := Y))
  exact Seminorm.continuous_of_le (q := C • normSeminorm ℂ W)
    ((continuous_norm (E := W)).const_smul C) hC

/-- Approximate a completed tensor at geometric accuracy and decompose successive
differences into finite lists of pure tensors with summable total cost. -/
private theorem exists_summable_tensorDecompositions
    (z : LocalBanach (banachProjectiveSeminorm (X := X) (Y := Y))) :
    ∃ l : ℕ → List (X × Y), Summable (fun n ↦ tensorDecompositionCost (l n)) ∧
      HasSum (fun n ↦ ((show WithLocalSeminorm banachProjectiveSeminorm from
        ((l n).map fun p ↦ p.1 ⊗ₜ[ℂ] p.2).sum) : LocalBanach banachProjectiveSeminorm)) z := by
  let W := WithLocalSeminorm (banachProjectiveSeminorm (X := X) (Y := Y))
  let ε (n : ℕ) := (1 / 2 : ℝ) ^ n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεS : Summable ε := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  choose a ha using fun n ↦ Completion.denseRange_coe.exists_dist_lt z (hε n)
  let v : ℕ → W
    | 0 => 0
    | n + 1 => a n
  have hv : Tendsto (fun n ↦ (v n : Completion W)) atTop (𝓝 z) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Tendsto ε atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ dist_nonneg) (fun n ↦ (by simpa only [v, dist_comm] using (ha n).le))
  let d (n : ℕ) := v (n + 1) - v n
  choose l hl hlcost using fun n ↦ exists_decomposition_of_projectiveSeminorm_lt
    (show X ⊗[ℂ] Y from d n) (lt_add_of_pos_right _ (hε n))
  have hd (n : ℕ) : ‖d (n + 1)‖ ≤ ε n + ε (n + 1) := by
    change ‖a (n + 1) - a n‖ ≤ _
    rw [← Completion.norm_coe, Completion.coe_sub, ← dist_eq_norm]
    exact (dist_triangle_right (a (n + 1) : Completion W) (a n) z).trans
      (add_le_add (by simpa only [dist_comm] using (ha (n + 1)).le)
        (by simpa only [dist_comm] using (ha n).le) |>.trans_eq (add_comm _ _))
  have hshift := (summable_nat_add_iff 1).mpr hεS
  have hs : Summable (fun n ↦ tensorDecompositionCost (l n)) := by
    apply (summable_nat_add_iff 1).mp
    refine (hεS.add (hshift.add hshift)).of_nonneg_of_le
      (fun n ↦ tensorDecompositionCost_nonneg (l (n + 1))) fun n ↦ ?_
    exact ((hlcost (n + 1)).le.trans (add_le_add_left (hd n) _)).trans_eq (add_assoc _ _ _)
  have hdS : Summable (fun n ↦ (d n : Completion W)) :=
    hs.of_norm_bounded fun n ↦ by
      rw [Completion.norm_coe]
      change banachProjectiveSeminorm (show X ⊗[ℂ] Y from d n) ≤ _
      have hle := ciInf_le (bddBelow_tensorDecompositionCost (show X ⊗[ℂ] Y from d n))
        ⟨l n, hl n⟩
      exact hle
  refine ⟨l, hs, (hdS.hasSum_iff_tendsto_nat.mpr ?_).congr_fun (fun n ↦ ?_)⟩
  · refine hv.congr fun n ↦ ?_
    simp only [d, Completion.coe_sub]
    rw [Finset.sum_range_sub (fun k ↦ (v k : Completion W)), show v 0 = 0 from rfl,
      Completion.coe_zero, sub_zero]
  · exact congrArg (fun t : W ↦ (t : Completion W)) (hl n)

end NormedTensor

section BanachTensor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

-- Keep the completeness hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (C.3.1.1), p. 693. For Banach spaces the canonical map from the algebraic
tensor product with the projective topology is continuous for the operator norm on its target. -/
theorem continuous_tensorToFiniteRank_opNorm :
    Continuous (fun z : ProjectiveTensor (StrongDual ℂ E) F ↦
      (tensorToFiniteRank z : E →L[ℂ] F)) := by
  -- Mathlib's operator norm induces the existing bounded-convergence topology.
  exact continuous_tensorToFiniteRank_bounded

/-- Paper: (C.3.1.2), p. 693. The canonical map extends to the completed
projective tensor of the dual and the target Banach space. -/
def completedProjectiveTensorToOperators :
    Completion (ProjectiveTensor (StrongDual ℂ E) F) →L[ℂ] (E →L[ℂ] F) :=
  (show ProjectiveTensor (StrongDual ℂ E) F →L[ℂ] (E →L[ℂ] F) from
    ⟨tensorToFiniteRank, continuous_tensorToFiniteRank_opNorm⟩).fromCompletion

/-- Paper: (C.3.1.2), p. 693. On the image of an algebraic tensor the extended
map agrees with the original finite-rank map. -/
theorem completedProjectiveTensorToOperators_coe (z : ProjectiveTensor (StrongDual ℂ E) F) :
    completedProjectiveTensorToOperators z = tensorToFiniteRank z :=
  ContinuousLinearMap.fromCompletion_apply_coe _ z

local notation "D" => StrongDual ℂ E
local notation "P" => ProjectiveTensor (StrongDual ℂ E) F
local notation "W" => WithLocalSeminorm (banachProjectiveSeminorm (X := D) (Y := F))

/-- A nuclear series lifts to a sum of elementary tensors in the completion. -/
private theorem mem_range_of_isBanachNuclear (A : E →L[ℂ] F) (hA : IsBanachNuclear A) :
    A ∈ range completedProjectiveTensorToOperators := by
  obtain ⟨c, φ, y, hc, hφ, hy, hA⟩ := hA
  obtain ⟨B, hB, hφB⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
  obtain ⟨C, _, hyC⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
  let t (n : ℕ) : W := c n • (φ n ⊗ₜ[ℂ] y n)
  have ht : Summable (fun n ↦ (t n : Completion W)) :=
    (hc.mul_right (B * C)).of_norm_bounded (fun n ↦ by
      rw [Completion.norm_coe]
      change ‖c n • (show W from φ n ⊗ₜ[ℂ] y n)‖ ≤ _
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ((projectiveSeminorm_tmul_le (φ n) (y n)).trans
        (mul_le_mul (hφB _ (mem_range_self n)) (hyC _ (mem_range_self n))
          (norm_nonneg _) hB.le)) (norm_nonneg _))
  let j : W →L[ℂ] P := fromProjectiveSeminorm
  refine ⟨j.completion (∑' n, (t n : Completion W)), ?_⟩
  ext x
  let ev := (ContinuousLinearMap.apply ℂ F) x
  have hs := (ev.comp (completedProjectiveTensorToOperators.comp j.completion)).hasSum ht.hasSum
  refine (hs.congr_fun fun n ↦ ?_).unique (hA x)
  change (c n * φ n x) • y n = completedProjectiveTensorToOperators (j.completion (t n)) x
  rw [ContinuousLinearMap.completion_apply_coe, completedProjectiveTensorToOperators_coe]
  change (c n * φ n x) • y n = tensorToFiniteRank (c n • (φ n ⊗ₜ[ℂ] y n)) x
  rw [map_smul, smul_apply, tensorToFiniteRank_tmul, mul_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A series of finite pure-tensor decompositions of summable total cost flattens to
a series of rank-one maps with summable coefficients and unit-ball factors. -/
private theorem isBanachNuclear_of_summable_tensorDecompositions
    (T : Completion W →L[ℂ] (E →L[ℂ] F))
    (hT : ∀ (φ : D) (y : F) (x : E),
      T ((show W from φ ⊗ₜ[ℂ] y) : Completion W) x = φ x • y)
    (z : Completion W) (l : ℕ → List (D × F))
    (hl : Summable (fun n ↦ tensorDecompositionCost (l n)))
    (hz : HasSum (fun n ↦ ((show W from ((l n).map fun p ↦ p.1 ⊗ₜ[ℂ] p.2).sum) :
      Completion W)) z) :
    IsBanachNuclear (T z) := by
  classical
  let I := Σ n : ℕ, Fin (l n).length
  let p (i : I) : D × F := (l i.1).get i.2
  let b (i : I) : W := (p i).1 ⊗ₜ[ℂ] (p i).2
  let cost (i : I) : ℝ := ‖(p i).1‖ * ‖(p i).2‖
  have hcost : Summable cost := (summable_sigma_of_nonneg
    (fun i : I ↦ by dsimp [cost]; positivity)).mpr ⟨fun _ ↦ (hasSum_fintype _).summable, by
      convert hl using 1
      funext n
      rw [tsum_fintype, ← List.sum_ofFn]
      change (List.ofFn ((fun v : D × F ↦ ‖v.1‖ * ‖v.2‖) ∘ (l n).get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]
      rfl⟩
  have hbS : Summable (fun i ↦ (b i : Completion W)) := hcost.of_norm_bounded fun i ↦
    (Completion.norm_coe (b i)).le.trans (projectiveSeminorm_tmul_le (p i).1 (p i).2)
  have hb : HasSum (fun i ↦ (b i : Completion W)) z :=
    hz.sigma_of_hasSum (fun n ↦ by
      convert hasSum_fintype (fun i : Fin (l n).length ↦ (b ⟨n, i⟩ : Completion W)) using 1
      let coe : W →L[ℂ] Completion W := Completion.toComplL
      change coe ((l n).map fun p ↦ p.1 ⊗ₜ[ℂ] p.2).sum =
        ∑ i : Fin (l n).length, coe (b ⟨n, i⟩)
      rw [← map_sum]
      congr 1
      symm
      rw [← List.sum_ofFn]
      change (List.ofFn ((fun v : D × F ↦ v.1 ⊗ₜ[ℂ] v.2) ∘ (l n).get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]) hbS
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  let r (n : ℕ) := extend e p 0 n
  let c (n : ℕ) : ℂ := (‖(r n).1‖ : ℂ) * (‖(r n).2‖ : ℂ)
  let φ (n : ℕ) : D := normalizedFactor (r n).1
  let y (n : ℕ) : F := normalizedFactor (r n).2
  refine isBanachNuclear_of_bounded_series (T z) c φ y ?_
    ⟨1, fun n ↦ norm_normalizedFactor_le_one (r n).1⟩
    (fun n ↦ norm_normalizedFactor_le_one (r n).2) fun x ↦ ?_
  · have h := (summable_extend_zero he).mpr hcost
    refine h.congr fun n ↦ ?_
    simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [r, he.extend_apply, cost]
    · simp only [r, extend_apply' _ _ _ h, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero,
        norm_zero, zero_mul]
  · have hs := (((ContinuousLinearMap.apply ℂ F) x).comp T).hasSum hb
    have hterm : HasSum (fun i : I ↦ (p i).1 x • (p i).2) (T z x) :=
      hs.congr_fun fun i ↦ (hT (p i).1 (p i).2 x).symm
    refine ((hasSum_extend_zero he).mpr hterm).congr_fun fun n ↦ ?_
    have heq : extend e (fun i ↦ (p i).1 x • (p i).2) 0 n = (r n).1 x • (r n).2 := by
      by_cases h : ∃ i, e i = n
      · obtain ⟨i, rfl⟩ := h
        simp only [r, he.extend_apply]
      · simp only [r, extend_apply' _ _ _ h, Pi.zero_apply, Prod.snd_zero, smul_zero]
    rw [heq]
    calc
      _ = (((‖(r n).1‖ : ℂ) • φ n) x) • ((‖(r n).2‖ : ℂ) • y n) := by
        simp only [c, smul_apply, smul_eq_mul, smul_smul]
        congr 1
        ring
      _ = _ := by
        rw [show (‖(r n).1‖ : ℂ) • φ n = (r n).1 from norm_smul_normalizedFactor _,
          show (‖(r n).2‖ : ℂ) • y n = (r n).2 from norm_smul_normalizedFactor _]

/-- Every completed projective tensor maps to an operator with a nuclear series. -/
private theorem isBanachNuclear_of_mem_range (A : E →L[ℂ] F)
    (hA : A ∈ range completedProjectiveTensorToOperators) : IsBanachNuclear A := by
  obtain ⟨z, rfl⟩ := hA
  let i : P →L[ℂ] W := toProjectiveSeminorm
  let j : W →L[ℂ] P := fromProjectiveSeminorm
  have hji : j.completion (i.completion z) = z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (j.completion.continuous.comp i.completion.continuous) continuous_id
    | ih v => rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]; rfl
  obtain ⟨l, hl, hz⟩ := exists_summable_tensorDecompositions (i.completion z)
  let T := completedProjectiveTensorToOperators.comp j.completion
  rw [← hji]
  refine isBanachNuclear_of_summable_tensorDecompositions T (fun φ y x ↦ ?_) (i.completion z) l hl hz
  let v : W := φ ⊗ₜ[ℂ] y
  change completedProjectiveTensorToOperators (j.completion (v : Completion W)) x = _
  rw [ContinuousLinearMap.completion_apply_coe, completedProjectiveTensorToOperators_coe]
  exact tensorToFiniteRank_tmul φ y x

/-- Paper: §C.3.1, p. 693. Nuclear operators between Banach spaces are the
image of the completed projective tensor. -/
theorem isBanachNuclear_iff_mem_range (A : E →L[ℂ] F) :
    IsBanachNuclear A ↔ A ∈ range completedProjectiveTensorToOperators := by
  exact ⟨mem_range_of_isBanachNuclear A, isBanachNuclear_of_mem_range A⟩

/-- Paper: §C.3.1, p. 694. The local and Banach-space definitions of a
nuclear operator agree for Banach spaces. -/
theorem isNuclearOperator_iff_isBanachNuclear (A : E →L[ℂ] F) :
    IsNuclearOperator A ↔ IsBanachNuclear A := by
  constructor
  · rintro ⟨U, hU, bU, cU, B, hB, _, T, ⟨c, φ, y, hc, hφ, hy, hT⟩, hA⟩
    let p := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
    let G := WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent)
    let i₀ : E →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
    let i : E →L[ℂ] LocalBanach p :=
      ⟨i₀, (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng (LocalBanach p) i₀
        ⟨{⟨p, continuous_gauge cU hU⟩}, 1, by
          simpa using (show (normSeminorm ℂ _).comp i₀ ≤ p from
            fun x ↦ (localBanach_norm_coe p x).le)⟩⟩
    let j : G →L[ℂ] F := ⟨(Submodule.span ℂ B).subtype, continuous_banachDisc_subtype hB⟩
    let precomp := (ContinuousLinearMap.compL ℂ E (LocalBanach p) ℂ).flip i
    refine ⟨c, ⇑precomp ∘ φ, ⇑j ∘ y, hc, ?_, ?_, ?_⟩
    · simpa only [map_zero] using (precomp.continuous.tendsto 0).comp hφ
    · simpa only [map_zero] using (j.continuous.tendsto 0).comp hy
    · intro x
      have hs := j.hasSum (hT (i x))
      rw [show j (T (i x)) = A x from hA x] at hs
      change HasSum (fun n ↦ (c n * φ n (i x)) • j (y n)) (A x)
      simpa only [map_smul] using hs
  · rintro ⟨c, φ, y, hc, hφ, hy, hA⟩
    apply (isNuclearOperator_iff_nonempty_presentation A).mpr
    obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    have hφ_bound : ∃ C : ℝ, ∀ n, ‖φ n‖ ≤ C := ⟨C, fun n ↦ hC _ (mem_range_self n)⟩
    obtain ⟨R, hR, hyR⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
    let r : ℂ := R
    have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have hr_norm : ‖r‖ = R := by
      dsimp [r]
      rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
    let B := Metric.closedBall (0 : F) 1
    have hyB (n : ℕ) : r⁻¹ • y n ∈ B := by
      change dist (r⁻¹ • y n) 0 ≤ 1
      rw [dist_zero_right, norm_smul, norm_inv, hr_norm, inv_mul_le_iff₀ hR, mul_one]
      exact hyR _ (mem_range_self n)
    refine ⟨{
      coeff := fun n ↦ c n * r
      functional := φ
      disc := B
      isBanachDisc := isBanachDisc_closedUnitBall
      vector := fun n ↦ ⟨r⁻¹ • y n, Submodule.subset_span (hyB n)⟩
      vector_mem := hyB
      summable_coeff := by simpa only [norm_mul] using hc.mul_right ‖r‖
      equicontinuous := ((NormedSpace.equicontinuous_tfae φ).out 6 1).mp hφ_bound
      hasSum := ?_ }⟩
    intro x
    refine (hA x).congr_fun fun n ↦ ?_
    change (c n * r * φ n x) • (r⁻¹ • y n) = (c n * φ n x) • y n
    rw [smul_smul, mul_right_comm (c n) r, mul_inv_cancel_right₀ hr]

end BanachTensor

section NuclearTrace

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

omit [T2Space E] in
/-- Inserting an operator into the scalar series of a presentation gives a continuous
additive functional for the topology of uniform convergence on bounded sets. -/
private theorem nuclearPresentation_traceFunctional {A : E →L[ℂ] E} (r : NuclearPresentation A) :
    ∃ L : (E →L[ℂ] E) →+ ℂ, Continuous L ∧
      (∀ (φ : StrongDual ℂ E) (y : E), L (tensorToFiniteRank (φ ⊗ₜ[ℂ] y)) = φ (A y)) ∧
      Summable (fun n ↦ ‖r.coeff n * r.functional n (r.vector n)‖) ∧
      HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n)) (L (ContinuousLinearMap.id ℂ E)) := by
  have hseminorm := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae
    (fun n ↦ (r.functional n).toLinearMap)).out 1 4
  obtain ⟨p, hp, hφ⟩ := (hseminorm.mp r.equicontinuous) ()
  let term (B : E →L[ℂ] E) (n : ℕ) := r.coeff n * r.functional n (B (r.vector n))
  have hs (B : E →L[ℂ] E) : Summable (fun n ↦ ‖term B n‖) := by
    obtain ⟨C, _, hC⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
      (r.isBanachDisc.bounded.image B) ⟨p, hp⟩
    refine (r.summable_coeff.mul_right C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    simp only [term, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((hφ n _).trans (hC _ (mem_image_of_mem B (r.vector_mem n))).le) (norm_nonneg _)
  let L : (E →L[ℂ] E) →+ ℂ := {
    toFun := fun B ↦ ∑' n, term B n
    map_zero' := by simp [term]
    map_add' := fun B D ↦ by
      simpa [term, mul_add] using ((hs B).of_norm.tsum_add (hs D).of_norm) }
  let I := ContinuousLinearMap.id ℂ E
  refine ⟨L, ?_, ?_, hs I, (hs I).of_norm.hasSum⟩
  · apply continuous_of_continuousAt_zero L
    rw [ContinuousAt, L.map_zero, Metric.tendsto_nhds]
    intro ε hε
    let C := (∑' n, ‖r.coeff n‖) + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hU := (Seminorm.continuous_iff (p := p) (div_pos hε hC)).mp hp
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ)
      r.isBanachDisc.bounded hU] with B hB
    rw [dist_zero_right]
    calc
      ‖L B‖ ≤ ∑' n, ‖term B n‖ := norm_tsum_le_tsum_norm (hs B)
      _ ≤ ∑' n, ‖r.coeff n‖ * (ε / C) := (hs B).tsum_le_tsum (fun n ↦ by
        simp only [term, norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (hφ n _).trans (p.mem_ball_zero.mp (hB (r.vector_mem n))).le)
          (r.summable_coeff.mul_right _)
      _ = (∑' n, ‖r.coeff n‖) * (ε / C) := r.summable_coeff.tsum_mul_right _
      _ < C * (ε / C) := mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε hC)
      _ = ε := by field_simp
  · intro φ y
    apply (hs (tensorToFiniteRank (φ ⊗ₜ[ℂ] y))).of_norm.hasSum.unique
    refine (φ.hasSum (r.hasSum y)).congr_fun fun n ↦ ?_
    simp only [term, tensorToFiniteRank_tmul, map_smul, smul_eq_mul]
    ring
/-- Inserting an endomorphism on the vector side of a nuclear presentation gives an
absolutely convergent scalar series, continuous in that endomorphism for precompact convergence. -/
private theorem NuclearPresentation.exists_tracePairing {A : E →L[ℂ] E}
    (r : NuclearPresentation A) :
    ∃ L : PrecompactConvergenceCLM E E →L[ℂ] ℂ,
      ∀ T : PrecompactConvergenceCLM E E,
        Summable (fun n ↦ ‖r.coeff n * r.functional n (T (r.vector n))‖) ∧
        HasSum (fun n ↦ r.coeff n * r.functional n (T (r.vector n))) (L T) := by
  obtain ⟨d, hd, hd₀, hdiv⟩ := exists_pos_tendsto_zero_summable_div
    r.summable_coeff (fun n ↦ norm_nonneg _)
  let c (n : ℕ) : ℂ := r.coeff n / (d n : ℂ)
  let y (n : ℕ) : E := (d n : ℂ) • (r.vector n : E)
  have hc : Summable (fun n ↦ ‖c n‖) := by
    simpa only [c, norm_div, Complex.norm_real, Real.norm_of_nonneg (hd _).le] using hdiv
  have hy : Tendsto y atTop (𝓝 0) := r.isBanachDisc.bounded.smul_tendsto_zero
    (Eventually.of_forall r.vector_mem) (by
      simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).comp hd₀)
  let K := insert (0 : E) (range y)
  have hK : IsCompact K := hy.isCompact_insert_range
  have hyK (n : ℕ) : y n ∈ K := mem_insert_of_mem _ (mem_range_self n)
  have hseminorm := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae
    (fun n ↦ (r.functional n).toLinearMap)).out 1 4
  obtain ⟨p, hp, hφ⟩ := (hseminorm.mp r.equicontinuous) ()
  let term (T : PrecompactConvergenceCLM E E) (n : ℕ) := c n * r.functional n (T (y n))
  have hterm (T : PrecompactConvergenceCLM E E) (n : ℕ) :
      ‖term T n‖ ≤ ‖c n‖ * p (T (y n)) := by
    change ‖c n * r.functional n (T (y n))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hφ n _) (norm_nonneg _)
  have hs (T : PrecompactConvergenceCLM E E) : Summable (fun n ↦ ‖term T n‖) := by
    obtain ⟨C, _, hC⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
      (hK.isVonNBounded ℂ) ⟨p.comp T.toLinearMap, hp.comp T.continuous⟩
    refine (hc.mul_right C).of_nonneg_of_le (fun n ↦ norm_nonneg _) fun n ↦ ?_
    exact (hterm T n).trans (mul_le_mul_of_nonneg_left (hC _ (hyK n)).le (norm_nonneg _))
  let L : PrecompactConvergenceCLM E E →ₗ[ℂ] ℂ :=
    { toFun := fun T ↦ ∑' n, term T n
      map_add' := fun T S ↦ by
        change (∑' n, term (T + S) n) = (∑' n, term T n) + ∑' n, term S n
        rw [← (hs T).of_norm.tsum_add (hs S).of_norm]
        exact tsum_congr fun n ↦ by simp [term, mul_add]
      map_smul' := fun a T ↦ by
        change (∑' n, term (a • T) n) = a * ∑' n, term T n
        rw [← tsum_mul_left]
        exact tsum_congr fun n ↦ by simp [term, smul_eq_mul, mul_left_comm] }
  have hL : Continuous L := by
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    let M := (∑' n, ‖c n‖) + 1
    have hM : 0 < M := by dsimp [M]; positivity
    have hδ : 0 < ε / M := div_pos hε hM
    have hnear := UniformConvergenceCLM.eventually_nhds_zero_mapsTo (RingHom.id ℂ)
      (𝔖 := {s | IsPrecompactInCompletion s})
      ((isPrecompactInCompletion_iff_totallyBounded K).mpr hK.totallyBounded)
      ((Seminorm.continuous_iff hδ).mp hp)
    filter_upwards [hnear] with T hT
    rw [dist_zero_right]
    calc
      ‖L T‖ ≤ ∑' n, ‖c n‖ * (ε / M) := by
        refine tsum_of_norm_bounded (hc.mul_right (ε / M)).hasSum fun n ↦ ?_
        exact (hterm T n).trans (mul_le_mul_of_nonneg_left
          (p.mem_ball_zero.mp (hT (hyK n))).le (norm_nonneg _))
      _ < ε := by
        rw [tsum_mul_right, mul_div_left_comm]
        simpa only [mul_one] using
          mul_lt_mul_of_pos_left ((div_lt_one hM).mpr (lt_add_one _)) hε
  refine ⟨⟨L, hL⟩, fun T ↦ ?_⟩
  have heq (n : ℕ) : term T n = r.coeff n * r.functional n (T (r.vector n)) := by
    simp only [term, c, y, map_smul, smul_eq_mul, ← mul_assoc]
    rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hd n).ne')]
  exact ⟨(hs T).congr (fun n ↦ congrArg norm (heq n)),
    (hs T).of_norm.hasSum.congr_fun (fun n ↦ (heq n).symm)⟩

omit [T2Space E] in
/-- On a rank-one test map, the scalar series obtained by inserting it in a nuclear presentation
depends only on the presented operator. -/
private theorem NuclearPresentation.hasSum_tracePairing_tmul {A : E →L[ℂ] E}
    (r : NuclearPresentation A) (φ : StrongDual ℂ E) (x : E) :
    HasSum (fun n ↦ r.coeff n * r.functional n (tensorToFiniteRank (φ ⊗ₜ[ℂ] x) (r.vector n)))
      (φ (A x)) := by
  refine (φ.hasSum (r.hasSum x)).congr_fun fun n ↦ ?_
  rw [tensorToFiniteRank_tmul, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Paper: Proposition C.3.2.1, p. 694. On a space with the approximation property,
every presentation of the same nuclear endomorphism gives an absolutely convergent
scalar series with the same sum. -/
theorem exists_nuclearTrace_hasSum (hE : HasApproximationProperty E) (A : E →L[ℂ] E)
    (hA : IsNuclearOperator A) :
    ∃! z : ℂ, ∀ r : NuclearPresentation A,
      Summable (fun n ↦ ‖r.coeff n * r.functional n (r.vector n)‖) ∧
      HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n)) z := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation A).mp hA
  obtain ⟨L, hL⟩ := r.exists_tracePairing
  let I : PrecompactConvergenceCLM E E := ContinuousLinearMap.id ℂ E
  refine ⟨L I, fun s ↦ ?_, fun z hz ↦ (hz r).2.unique (hL I).2⟩
  obtain ⟨M, hM⟩ := s.exists_tracePairing
  have hclosed : IsClosed {T : PrecompactConvergenceCLM E E | L T = M T} :=
    isClosed_eq L.continuous M.continuous
  have hLM : L I = M I := by
    refine hclosed.closure_subset_iff.mpr ?_ (hE I)
    rintro _ ⟨t, rfl⟩
    let j := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) E
      {s : Set E | IsPrecompactInCompletion s}
    change L (j (tensorToFiniteRank t)) = M (j (tensorToFiniteRank t))
    induction t using TensorProduct.inductionOn with
    | tmul φ x =>
      exact ((hL _).2.unique (r.hasSum_tracePairing_tmul φ x)).trans
        ((hM _).2.unique (s.hasSum_tracePairing_tmul φ x)).symm
    | add t u ht hu => simp only [map_add, ht, hu]
  rw [hLM]
  exact hM I

/-- Paper: (C.3.2.2), p. 694. The nuclear trace is the sum of the scalar series
from any nuclear presentation on a space with the approximation property. -/
def nuclearTrace (hE : HasApproximationProperty E) (A : E →L[ℂ] E) (hA : IsNuclearOperator A) : ℂ :=
  (exists_nuclearTrace_hasSum hE A hA).exists.choose

/-- Paper: (C.3.2.2), p. 694. The trace of a rank-one operator is the value
of its functional at its spanning vector.
Deviation: This is a check of the trace formula on one term. -/
theorem nuclearTrace_smulRight (hE : HasApproximationProperty E) (φ : E →L[ℂ] ℂ) (y : E) :
    nuclearTrace hE (φ.smulRight y) (isNuclearOperator_smulRight φ y) = φ y := by
  obtain ⟨r, hc, hφ, hy, htail⟩ := nuclearPresentation_smulRight φ y 1 one_ne_zero
  have htrace := ((exists_nuclearTrace_hasSum hE (φ.smulRight y)
    (isNuclearOperator_smulRight φ y)).exists.choose_spec r).2
  refine htrace.unique ((hasSum_ite_eq (0 : ℕ) (φ y)).congr_fun ?_)
  intro n
  cases n with
  | zero => simp [hc, hφ, hy]
  | succ n => simp [htail]

/-- The gauge of the image of a set under a complex-linear equivalence, at an image point,
is the gauge of the set at the original point. -/
private theorem gauge_image_linearEquiv {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (φ : M ≃ₗ[ℂ] N) (s : Set M) (x : M) :
    gauge (φ '' s) (φ x) = gauge s x := by
  unfold gauge
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ ↦ ?_
  simp only [Set.mem_smul_set, Set.exists_mem_image]
  refine exists_congr fun y ↦ and_congr_right fun _ ↦ ?_
  rw [show r • φ y = φ (r • y) from (LinearMap.map_smul_of_tower φ.toLinearMap r y).symm]
  exact φ.injective.eq_iff

/-- The image of a Banach disc under an injective continuous linear map is a Banach disc:
the map restricts to a linear equivalence of the spans that preserves the gauges. -/
private theorem IsBanachDisc.image_of_injective {Y Z : Type*}
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z]
    [PolynormableSpace ℂ Z] [T2Space Z]
    {B : Set Y} (hB : IsBanachDisc B) (T : Y →L[ℂ] Z) (hT : Injective T) :
    IsBanachDisc (T '' B) := by
  let S := Submodule.span ℂ B
  let S' := Submodule.span ℂ (T '' B)
  have hSS : S.map T.toLinearMap = S' := (Submodule.span_image T.toLinearMap).symm
  let φ : S ≃ₗ[ℂ] S' :=
    (Submodule.equivMapOfInjective T.toLinearMap hT S).trans (LinearEquiv.ofEq _ _ hSS)
  have himage : ((↑) ⁻¹' (T '' B) : Set S') = φ '' ((↑) ⁻¹' B : Set S) := by
    ext z
    constructor
    · rintro ⟨b, hb, hbz⟩
      exact ⟨⟨b, Submodule.subset_span hb⟩, hb, Subtype.ext hbz⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have bB : Balanced ℂ ((↑) ⁻¹' (T '' B) : Set S') :=
    himage ▸ hB.balanced.image φ.toLinearMap
  have cB : Convex ℝ ((↑) ⁻¹' (T '' B) : Set S') :=
    himage ▸ hB.convex.linear_image (φ.toLinearMap.restrictScalars ℝ)
  have aB : Absorbent ℝ ((↑) ⁻¹' (T '' B) : Set S') :=
    himage ▸ Absorbent.image_of_surjective (f := φ.toLinearMap.restrictScalars ℝ)
      φ.surjective hB.absorbent
  let p := gaugeSeminorm hB.balanced hB.convex hB.absorbent
  let p' := gaugeSeminorm bB cB aB
  have hnorm (z : S') : p' z = p (φ.symm z) := by
    change gauge _ z = gauge _ (φ.symm z)
    rw [himage, ← gauge_image_linearEquiv φ, φ.apply_symm_apply]
  let ψ : WithLocalSeminorm p' → WithLocalSeminorm p := fun z ↦ (φ.symm (show S' from z) : S)
  have hψ : Isometry ψ := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    change p (φ.symm (show S' from x) - φ.symm (show S' from y)) =
      p' ((show S' from x) - (show S' from y))
    rw [← map_sub]
    exact (hnorm _).symm
  have hinj : Injective ψ := fun a b h ↦ φ.symm.injective h
  have hsurj : Surjective ψ := fun z ↦ ⟨(φ (show S from z) : S'), φ.symm_apply_apply _⟩
  have := hB.separated
  exact ⟨hB.bounded.image T, bB, cB, aB,
    T2Space.of_injective_continuous hinj hψ.continuous,
    (hψ.isUniformInducing.completeSpace_congr hsurj).mpr hB.complete⟩

/-- Precomposition acts on the functionals of a nuclear presentation, while injective
postcomposition acts on its vectors and Banach disc. -/
private def NuclearPresentation.comp_comp {W X Y Z : Type*}
    [AddCommGroup W] [Module ℂ W] [UniformSpace W] [IsUniformAddGroup W]
    [PolynormableSpace ℂ W] [T2Space W]
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z]
    [PolynormableSpace ℂ Z] [T2Space Z]
    {A : X →L[ℂ] Y} (r : NuclearPresentation A) (S : W →L[ℂ] X) (R : Y →L[ℂ] Z)
    (hR : Injective R) : NuclearPresentation (R.comp (A.comp S)) where
  coeff := r.coeff
  functional n := (r.functional n).comp S
  disc := R '' r.disc
  isBanachDisc := r.isBanachDisc.image_of_injective R hR
  vector n := ⟨R (r.vector n), Submodule.subset_span ⟨_, r.vector_mem n, rfl⟩⟩
  vector_mem n := ⟨_, r.vector_mem n, rfl⟩
  summable_coeff := r.summable_coeff
  equicontinuous U hU := by
    have h := (S.continuous.tendsto' 0 0 (map_zero S)).eventually (r.equicontinuous U hU)
    simpa only [ContinuousLinearMap.comp_apply, map_zero] using h
  hasSum x := by
    simpa only [ContinuousLinearMap.comp_apply, map_smul] using R.hasSum (r.hasSum (S x))

/-- Precomposing a nuclear operator with a continuous linear map and postcomposing it with
an injective continuous linear map gives a nuclear operator. -/
private theorem isNuclearOperator_comp_comp {W X Y Z : Type*}
    [AddCommGroup W] [Module ℂ W] [UniformSpace W] [IsUniformAddGroup W]
    [PolynormableSpace ℂ W] [T2Space W]
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z]
    [PolynormableSpace ℂ Z] [T2Space Z]
    {A : X →L[ℂ] Y} (hA : IsNuclearOperator A) (S : W →L[ℂ] X) (R : Y →L[ℂ] Z)
    (hR : Injective R) :
    IsNuclearOperator (R.comp (A.comp S)) := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation A).mp hA
  exact (isNuclearOperator_iff_nonempty_presentation _).mpr ⟨r.comp_comp S R hR⟩

/-- The Minkowski gauge is unchanged by a linear equivalence. -/
private theorem gauge_eq_of_linearEquiv_image {S S' : Type*} [AddCommGroup S] [Module ℂ S]
    [AddCommGroup S'] [Module ℂ S'] (e : S ≃ₗ[ℂ] S') (s : Set S) (x : S) :
    gauge (e '' s) (e x) = gauge s x := by
  open scoped Pointwise in
  have hmem (r : ℝ) : e x ∈ r • (e '' s) ↔ x ∈ r • s := by
    constructor
    · intro h
      rcases h with ⟨z, hz, hxz⟩
      rcases hz with ⟨y, hy, rfl⟩
      have : e x = e (r • y) := by
        rw [← hxz]
        exact (LinearMap.map_smul_of_tower e.toLinearMap r y).symm
      exact ⟨y, hy, (e.injective this).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e y, ⟨y, hy, rfl⟩, (LinearMap.map_smul_of_tower e.toLinearMap r y).symm⟩
  have hset : {r : ℝ | 0 < r ∧ e x ∈ r • (e '' s)} = {r : ℝ | 0 < r ∧ x ∈ r • s} := by
    ext r
    simp only [Set.mem_ofPred_eq, hmem]
  rw [gauge, gauge, hset]

/-- The image of a Banach disc under a continuous linear automorphism is a Banach disc,
because the automorphism identifies the two gauge spaces isometrically. -/
private theorem isBanachDisc_image {B : Set E} (hB : IsBanachDisc B) (T : E ≃L[ℂ] E) :
    IsBanachDisc (T '' B) := by
  let S := Submodule.span ℂ B
  let S' := Submodule.span ℂ (T '' B)
  let e : E ≃ₗ[ℂ] E := T.toLinearEquiv
  have hmap : S.map e.toLinearMap = S' := by
    rw [Submodule.map_span]
    rfl
  let φ : S ≃ₗ[ℂ] S' := e.ofSubmodules S S' hmap
  let preB : Set S := (↑) ⁻¹' B
  let preB' : Set S' := (↑) ⁻¹' (T '' B)
  have hset : preB' = φ '' preB := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨b, hb, hbz⟩
      exact ⟨⟨b, Submodule.subset_span hb⟩, hb, Subtype.ext hbz⟩
    · rintro ⟨x, hx, rfl⟩
      change (φ x : E) ∈ T '' B
      exact ⟨(x : E), hx, rfl⟩
  have b' : Balanced ℂ preB' := by
    rw [hset]
    exact hB.balanced.image φ.toLinearMap
  have c' : Convex ℝ preB' := by
    rw [hset]
    exact hB.convex.linear_image (φ.toLinearMap.restrictScalars ℝ)
  have a' : Absorbent ℝ preB' := by
    rw [hset]
    exact Absorbent.image_of_surjective (f := φ.toLinearMap.restrictScalars ℝ) φ.surjective
      hB.absorbent
  let p := gaugeSeminorm hB.balanced hB.convex hB.absorbent
  let q := gaugeSeminorm b' c' a'
  have hgauge (x : S) : gauge preB' (φ x) = gauge preB x := by
    rw [hset]
    exact gauge_eq_of_linearEquiv_image φ preB x
  let f : WithLocalSeminorm p → WithLocalSeminorm q := fun x => φ x
  let g : WithLocalSeminorm q → WithLocalSeminorm p := fun y => φ.symm y
  have hnorm (x : WithLocalSeminorm p) : ‖f x‖ = ‖x‖ := by
    have hqx : ‖f x‖ = q (f x) := rfl
    have hpx : ‖x‖ = p x := rfl
    rw [hqx, hpx]
    change gauge preB' (φ x) = gauge preB x
    exact hgauge x
  let iso : WithLocalSeminorm p ≃ᵢ WithLocalSeminorm q :=
    { toFun := f
      invFun := g
      left_inv := fun x => φ.symm_apply_apply x
      right_inv := fun y => φ.apply_symm_apply y
      isometry_toFun := Isometry.of_dist_eq fun x y => by
        rw [dist_eq_norm, dist_eq_norm]
        have hsub : f x - f y = f (x - y) := (map_sub φ x y).symm
        rw [hsub]
        exact hnorm (x - y) }
  exact {
    bounded := hB.bounded.image (T : E →L[ℂ] E)
    balanced := b'
    convex := c'
    absorbent := a'
    separated := by
      letI : T2Space (WithLocalSeminorm p) := hB.separated
      exact iso.toHomeomorph.t2Space
    complete := iso.completeSpace_iff.mp hB.complete }

/-- Conjugating a nuclear presentation by a continuous linear automorphism gives a
presentation of the conjugate operator with the same scalar trace series. -/
private theorem nuclearPresentation_conj (A : E →L[ℂ] E) (r : NuclearPresentation A)
    (T : E ≃L[ℂ] E) :
    ∃ r' : NuclearPresentation
        (T.symm.toContinuousLinearMap.comp (A.comp T.toContinuousLinearMap)),
      ∀ n, r'.coeff n * r'.functional n (r'.vector n) =
        r.coeff n * r.functional n (r.vector n) := by
  let disc' := T.symm '' r.disc
  have hdisc : IsBanachDisc disc' := isBanachDisc_image r.isBanachDisc T.symm
  let S := Submodule.span ℂ r.disc
  let S' := Submodule.span ℂ disc'
  let e : E ≃ₗ[ℂ] E := T.symm.toLinearEquiv
  have hmap : S.map e.toLinearMap = S' := by
    rw [Submodule.map_span]
    rfl
  let φ : S ≃ₗ[ℂ] S' := e.ofSubmodules S S' hmap
  refine ⟨{
    coeff := r.coeff
    functional := fun n => (r.functional n).comp T.toContinuousLinearMap
    disc := disc'
    isBanachDisc := hdisc
    vector := fun n => φ (r.vector n)
    vector_mem := fun n => ⟨(r.vector n : E), r.vector_mem n, rfl⟩
    summable_coeff := r.summable_coeff
    equicontinuous := ?_
    hasSum := ?_ }, ?_⟩
  · intro U hU
    have hT : Tendsto T (𝓝 (0 : E)) (𝓝 (0 : E)) := by
      simpa [map_zero T] using T.continuous.tendsto (0 : E)
    simpa [map_zero T] using hT.eventually (r.equicontinuous U hU)
  · intro x
    refine (T.symm.toContinuousLinearMap.hasSum (r.hasSum (T x))).congr_fun fun n => ?_
    rw [map_smul]
    congr 1
  · intro n
    have hv : (φ (r.vector n) : E) = T.symm (r.vector n : E) := by
      rw [LinearEquiv.ofSubmodules_apply]
      exact congrFun (ContinuousLinearEquiv.coe_toLinearEquiv T.symm) _
    rw [hv, ContinuousLinearMap.comp_apply]
    exact congrArg (fun z => r.coeff n * (r.functional n) z)
      (T.apply_symm_apply (r.vector n : E))

/-- Paper: Proposition C.3.2.1, p. 694. Nuclearity is preserved by
conjugation by a continuous linear automorphism. -/
theorem isNuclearOperator_conj (A : E →L[ℂ] E) (hA : IsNuclearOperator A) (T : E ≃L[ℂ] E) :
    IsNuclearOperator (T.symm.toContinuousLinearMap.comp (A.comp T.toContinuousLinearMap)) :=
  isNuclearOperator_comp_comp hA T.toContinuousLinearMap T.symm.toContinuousLinearMap
    T.symm.injective

/-- Paper: Proposition C.3.2.1, p. 694. The nuclear trace is invariant
under conjugation by a continuous linear automorphism. -/
theorem nuclearTrace_conj (hE : HasApproximationProperty E) (A : E →L[ℂ] E) (hA : IsNuclearOperator A)
    (T : E ≃L[ℂ] E) :
    nuclearTrace hE A hA =
      nuclearTrace hE _ (isNuclearOperator_conj A hA T) := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation A).mp hA
  obtain ⟨r', hr'⟩ := nuclearPresentation_conj A r T
  have hAtr := ((exists_nuclearTrace_hasSum hE A hA).exists.choose_spec r).2
  have hBtr := ((exists_nuclearTrace_hasSum hE _
    (isNuclearOperator_conj A hA T)).exists.choose_spec r').2
  exact HasSum.unique hAtr (hBtr.congr_fun fun n => (hr' n).symm)

/-- Paper: Lemma C.3.2.2, p. 695. Both compositions of a nuclear map and
a continuous linear injection in the opposite direction are nuclear.
Deviation: The right-hand composition's nuclearity is made explicit to type its trace.
The two approximation-property hypotheses are needed for the trace assertion. -/
theorem isNuclearOperator_factor_comps (T : E →L[ℂ] F) (hT : Injective T)
    (A₀ : F →L[ℂ] E) (hA₀ : IsNuclearOperator A₀) :
    IsNuclearOperator (A₀.comp T) ∧ IsNuclearOperator (T.comp A₀) := by
  have h₁ := isNuclearOperator_comp_comp hA₀ T (ContinuousLinearMap.id ℂ E) injective_id
  have h₂ := isNuclearOperator_comp_comp hA₀ (ContinuousLinearMap.id ℂ F) T hT
  rw [ContinuousLinearMap.id_comp] at h₁
  rw [ContinuousLinearMap.comp_id] at h₂
  exact ⟨h₁, h₂⟩

/-- Paper: Lemma C.3.2.2, p. 695. A nuclear map followed by an injection has
the same trace as the reverse composition when both spaces have the approximation property.
Deviation: The given endomorphism is written as its factorization. -/
theorem nuclearTrace_factor_comps (hE : HasApproximationProperty E) (hF : HasApproximationProperty F)
    (T : E →L[ℂ] F) (hT : Injective T) (A₀ : F →L[ℂ] E) (hA₀ : IsNuclearOperator A₀) :
    nuclearTrace hE (A₀.comp T) (isNuclearOperator_factor_comps T hT A₀ hA₀).1 =
      nuclearTrace hF (T.comp A₀) (isNuclearOperator_factor_comps T hT A₀ hA₀).2 := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation A₀).mp hA₀
  let rE : NuclearPresentation (A₀.comp T) := r.comp_comp T (ContinuousLinearMap.id ℂ E) injective_id
  let rF : NuclearPresentation (T.comp A₀) := r.comp_comp (ContinuousLinearMap.id ℂ F) T hT
  have h := isNuclearOperator_factor_comps T hT A₀ hA₀
  have hsumE := ((exists_nuclearTrace_hasSum hE (A₀.comp T) h.1).exists.choose_spec rE).2
  have hsumF := ((exists_nuclearTrace_hasSum hF (T.comp A₀) h.2).exists.choose_spec rF).2
  -- Both series have terms `r.coeff n * r.functional n (T (r.vector n))`.
  exact hsumE.unique hsumF

end NuclearTrace

section HilbertOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Lemma C.3.3.1(1), p. 697. Every subset bounded in the strong operator
topology on a separable Hilbert space is metrizable with its subspace topology. -/
theorem metrizableSpace_bounded_pointwiseOperators [SeparableSpace H]
    (S : Set (H →Lₚₜ[ℂ] H)) (hS : IsVonNBounded ℂ S) : MetrizableSpace S := by
  have hbounded (x : H) : IsVonNBounded ℂ (range fun T : S ↦ T.val x) := by
    let ev := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H x
    change IsVonNBounded ℂ (range (ev ∘ (Subtype.val : S → _)))
    rw [range_comp, Subtype.range_coe]
    exact hS.image ev
  have heq := (PolynormableSpace.banach_steinhaus
    (𝓕 := fun T : S ↦ (T.val : H →L[ℂ] H)) hbounded).equicontinuous
  let restrict (T : S) (n : ℕ) := T.val (denseSeq H n)
  have hcont : Continuous restrict := continuous_pi fun n ↦
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H (denseSeq H n)).continuous.comp
      continuous_subtype_val
  have hind : IsInducing restrict := by
    rw [isInducing_iff_nhds]
    intro T
    refine le_antisymm (hcont.tendsto T).le_comap (tendsto_id'.mp ?_)
    apply IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
    intro x
    -- Equicontinuity extends convergence from the dense sequence to all vectors.
    have hclosed := heq.isClosed_setOfPred_tendsto
      (l := comap restrict (𝓝 (restrict T))) (T.val : H →L[ℂ] H).continuous
    apply hclosed.closure_subset_iff.mpr ?_ (denseRange_denseSeq H x)
    rintro _ ⟨n, rfl⟩
    exact tendsto_pi_nhds.mp (tendsto_comap (f := restrict) (x := 𝓝 (restrict T))) n
  let : PseudoMetrizableSpace S := hind.pseudoMetrizableSpace
  infer_instance

-- Lemma C.3.3.1(2): Hausdorffness is Mathlib's PointwiseConvergenceCLM instance.
-- Local convexity and quasi-completeness are already stated in Sec2a as
-- pointwiseConvergenceCLM_withSeminorms and hilbert_pointwiseOperators_quasiComplete.

/-- Paper: §C.3.4, p. 697. Hilbert spaces have the approximation property. -/
theorem hilbert_approximationProperty : HasApproximationProperty H := by
  classical
  apply (id_mem_closure_finiteRank_iff_dense H).mp
  let S := {s : Set H | IsPrecompactInCompletion s}
  have hpre (s : Set H) : s ∈ S ↔ TotallyBounded s := isPrecompactInCompletion_iff_totallyBounded s
  have hS : S.Nonempty := ⟨∅, (hpre ∅).2 totallyBounded_empty⟩
  have hdir : DirectedOn (· ⊆ ·) S := directedOn_of_sup_mem fun s t hs ht ↦
    (hpre _).2 (((hpre s).1 hs).union ((hpre t).1 ht))
  have hb := UniformConvergenceCLM.hasBasis_nhds_zero_of_basis (RingHom.id ℂ) H S hS hdir
    (Metric.nhds_basis_ball (x := (0 : H)))
  apply (mem_closure_iff_nhds_basis (hb.nhds_of_zero (ContinuousLinearMap.id ℂ H))).mpr
  rintro ⟨s, ε⟩ ⟨hs, hε⟩
  -- Projection onto the span of a finite ε-net approximates the identity on s.
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp ((hpre s).mp hs) ε hε
  let V := Submodule.span ℂ t
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ ht
  let b := stdOrthonormalBasis ℂ V
  refine ⟨V.starProjection, ⟨∑ i, (innerSL ℂ (b i : H)) ⊗ₜ[ℂ] (b i : H), ?_⟩, ?_⟩
  · change tensorToFiniteRank _ = V.starProjection
    rw [map_sum, b.starProjection_eq_sum_rankOne]
    rfl
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    change dist (V.starProjection x - x) 0 < ε
    rw [dist_zero_right, ← dist_eq_norm, dist_comm, V.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (Submodule.subset_span hy : y ∈ V)).trans_lt hxy

/-- Paper: §C.3.4, p. 697. On an infinite-dimensional Hilbert space finite-rank operators
are not dense in operator norm.
Deviation: This checks that operator-norm density is strictly stronger than the approximation property. -/
theorem hilbert_not_denseRange_finiteRank_opNorm (hinf : ¬ FiniteDimensional ℂ H) :
    ¬ DenseRange (X := H →L[ℂ] H) (fun z ↦ tensorToFiniteRank z) := by
  intro h
  apply hinf
  apply FiniteDimensional.of_isCompactOperator_id
  apply isClosed_setOfPred_isCompactOperator.closure_subset_iff.mpr ?_
    (h (ContinuousLinearMap.id ℂ H))
  rintro _ ⟨z, rfl⟩
  change IsCompactOperator (tensorToFiniteRank z)
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ y)).comp_clm φ
  | add z w hz hw =>
    rw [map_add]
    exact hz.add hw

/-- Paper: Lemma C.3.4.1(1), p. 697. The diagonal of a nuclear endomorphism
is absolutely summable in any Hilbert basis, including an uncountable basis.
Deviation: Mathlib's inner product is linear in the second argument. -/
theorem summable_norm_hilbertDiagonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    Summable (fun i ↦ ‖⟪b i, T (b i)⟫_ℂ‖) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
  obtain ⟨R, _, hyR⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
  -- Bound the absolute diagonal of each rank-one term by Cauchy–Schwarz.
  have hdiag (n : ℕ) :
      (Summable fun i ↦ ‖φ n (b i)‖ * ‖⟪b i, y n⟫_ℂ‖) ∧
        (∑' i, ‖φ n (b i)‖ * ‖⟪b i, y n⟫_ℂ‖) ≤ ‖φ n‖ * ‖y n‖ := by
    let u := (InnerProductSpace.toDual ℂ H).symm (φ n)
    have hu (i : ι) : ‖b.repr u i‖ = ‖φ n (b i)‖ := by
      rw [b.repr_apply_apply, norm_inner_symm (𝕜 := ℂ)]
      exact congrArg norm InnerProductSpace.toDual_symm_apply
    have hp : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
      simpa using Real.HolderConjugate.two_two
    have hCS := lp.tsum_mul_le_mul_norm hp (b.repr u) (b.repr (y n))
    simp only [hu] at hCS
    simpa only [b.repr_apply_apply, LinearIsometryEquiv.norm_map, u] using hCS
  let a (n : ℕ) (i : ι) : ℝ := ‖c n‖ * (‖φ n (b i)‖ * ‖⟪b i, y n⟫_ℂ‖)
  have ha_nonneg (n : ℕ) (i : ι) : 0 ≤ a n i :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have ha_row (n : ℕ) : Summable (a n) := (hdiag n).1.mul_left _
  have ha_bound (n : ℕ) : (∑' i, a n i) ≤ ‖c n‖ * (C * R) := by
    rw [show (∑' i, a n i) = ‖c n‖ * ∑' i, ‖φ n (b i)‖ * ‖⟪b i, y n⟫_ℂ‖ from
      (hdiag n).1.tsum_mul_left _]
    refine mul_le_mul_of_nonneg_left ((hdiag n).2.trans ?_) (norm_nonneg _)
    exact mul_le_mul (hφC _ (mem_range_self n)) (hyR _ (mem_range_self n))
      (norm_nonneg _) hC.le
  have ha : Summable (Function.uncurry a) :=
    (summable_prod_of_nonneg (f := Function.uncurry a) (fun p ↦ ha_nonneg p.1 p.2)).mpr
      ⟨ha_row, Summable.of_nonneg_of_le (fun n ↦ tsum_nonneg (ha_nonneg n))
        ha_bound (hc.mul_right (C * R))⟩
  -- Sum the majorant in the other order to control the diagonal of the full operator.
  have ha_swap : Summable (fun p : ι × ℕ ↦ a p.2 p.1) := ha.prod_symm
  refine Summable.of_nonneg_of_le (g := fun i ↦ ‖⟪b i, T (b i)⟫_ℂ‖)
    (fun i ↦ norm_nonneg ⟪b i, T (b i)⟫_ℂ) (fun i ↦ ?_) ha_swap.prod
  refine ((innerSL ℂ (b i)).hasSum (hsum (b i))).norm_le_of_bounded
    (ha_swap.prod_factor i).hasSum (fun n ↦ ?_)
  simp only [a, innerSL_apply_apply, inner_smul_right, norm_mul, mul_assoc, le_refl]

-- TODO(paper-gap): Lemma C.3.4.1(2) is false. For diag(1, -1) on ℂ², the sum
-- of absolute diagonal entries is 2 in the coordinate basis and 0 in the
-- orthonormal basis formed by the normalized sum and difference of its vectors.

/-- Summing the diagonal of a nuclear series gives the sum of the functional values
on the corresponding vectors, weighted by the coefficients. -/
private theorem tsum_hilbertDiagonal_eq_series {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (a : ℕ → ℂ) (φ : ℕ → H →L[ℂ] ℂ) (y : ℕ → H)
    (hcost : Summable (fun n ↦ ‖a n‖ * (‖φ n‖ * ‖y n‖)))
    (hT : ∀ x, HasSum (fun n ↦ (a n * φ n x) • y n) (T x)) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' n, a n * φ n (y n) := by
  let f (n : ℕ) (i : ι) := a n * (φ n (b i) * ⟪b i, y n⟫_ℂ)
  have hrow (n : ℕ) :
      (Summable fun i ↦ ‖φ n (b i) * ⟪b i, y n⟫_ℂ‖) ∧
        ∑' i, ‖φ n (b i) * ⟪b i, y n⟫_ℂ‖ ≤ ‖φ n‖ * ‖y n‖ := by
    let z := (InnerProductSpace.toDual ℂ H).symm (φ n)
    have hz (x : H) : ⟪z, x⟫_ℂ = φ n x := InnerProductSpace.toDual_symm_apply
    have hzn : ‖z‖ = ‖φ n‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
    have h := lp.tsum_mul_le_mul_norm
      (by simpa using Real.HolderConjugate.two_two) (b.repr z) (b.repr (y n))
    simpa only [b.repr_apply_apply, b.repr.norm_map, norm_inner_symm (𝕜 := ℂ) (b _) z,
      hz, hzn, norm_mul] using h
  have hnorm (n : ℕ) (i : ι) : ‖f n i‖ = ‖a n‖ * ‖φ n (b i) * ⟪b i, y n⟫_ℂ‖ :=
    norm_mul _ _
  -- The nuclear costs dominate the sum of the absolute row sums.
  have habs : Summable (fun p : ℕ × ι ↦ ‖f p.1 p.2‖) := by
    refine (summable_prod_of_nonneg (fun p ↦ norm_nonneg (f p.1 p.2))).mpr ⟨?_, ?_⟩
    · intro n
      simpa only [hnorm] using (hrow n).1.mul_left ‖a n‖
    · refine hcost.of_norm_bounded fun n ↦ ?_
      simp only [hnorm, tsum_mul_left]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (tsum_nonneg fun _ ↦ norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hrow n).2 (norm_nonneg _)
  have hdiag (i : ι) : (∑' n, f n i) = ⟪b i, T (b i)⟫_ℂ := by
    have h := (innerSL ℂ (b i)).hasSum (hT (b i))
    exact (h.congr_fun fun n ↦ by
      simp only [f, innerSL_apply_apply, inner_smul_right, mul_assoc]).tsum_eq
  have htrace (n : ℕ) : (∑' i, f n i) = a n * φ n (y n) := by
    have h := (φ n).hasSum (b.hasSum_repr (y n))
    exact ((h.mul_left (a n)).congr_fun fun i ↦ by
      simp only [f, map_smul, smul_eq_mul, b.repr_apply_apply,
        mul_comm (⟪b i, y n⟫_ℂ)]).tsum_eq
  calc
    _ = ∑' i, ∑' n, f n i := tsum_congr fun i ↦ (hdiag i).symm
    _ = ∑' n, ∑' i, f n i := habs.of_norm.tsum_comm
    _ = _ := tsum_congr htrace

/-- Paper: Lemma C.3.4.1(3), p. 697. The sum of the diagonal entries of a
nuclear endomorphism is independent of the Hilbert basis.
Deviation: Mathlib's inner product is linear in the second argument. -/
theorem tsum_hilbertDiagonal_eq {ι κ : Type*} (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' j, ⟪c j, T (c j)⟫_ℂ := by
  obtain ⟨a, φ, y, ha, hφ, hy, hseries⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  obtain ⟨C, hCpos, hC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
  obtain ⟨R, _, hR⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
  have hcost : Summable (fun n ↦ ‖a n‖ * (‖φ n‖ * ‖y n‖)) := by
    refine (ha.mul_right (C * R)).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hC _ (mem_range_self n)) (hR _ (mem_range_self n))
        (norm_nonneg _) hCpos.le) (norm_nonneg _)
  exact (tsum_hilbertDiagonal_eq_series b T a φ y hcost hseries).trans
    (tsum_hilbertDiagonal_eq_series c T a φ y hcost hseries).symm

/-- Paper: Lemma C.3.4.4(1), p. 698. The nuclear endomorphisms of a Hilbert space
contain zero and are closed under addition and complex scalar multiplication. -/
theorem nuclearEndomorphisms_submodule_axioms :
    IsNuclearOperator (0 : H →L[ℂ] H) ∧
      (∀ {A B : H →L[ℂ] H}, IsNuclearOperator A → IsNuclearOperator B → IsNuclearOperator (A + B)) ∧
      (∀ (c : ℂ) {A : H →L[ℂ] H}, IsNuclearOperator A → IsNuclearOperator (c • A)) := by
  let S := (completedProjectiveTensorToOperators (E := H) (F := H)).toLinearMap.range
  have hmem (A : H →L[ℂ] H) : IsNuclearOperator A ↔ A ∈ S :=
    (isNuclearOperator_iff_isBanachNuclear A).trans (isBanachNuclear_iff_mem_range A)
  refine ⟨(hmem 0).mpr S.zero_mem, ?_, ?_⟩
  · intro A B hA hB
    exact (hmem (A + B)).mpr (S.add_mem ((hmem A).mp hA) ((hmem B).mp hB))
  · intro c A hA
    exact (hmem (c • A)).mpr (S.smul_mem c ((hmem A).mp hA))

variable (H) in
/-- Paper: Definition C.3.4.2, p. 697. The space of nuclear endomorphisms is
the complex submodule of bounded endomorphisms satisfying nuclearity. -/
def nuclearEndomorphisms : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsNuclearOperator T}
  zero_mem' := nuclearEndomorphisms_submodule_axioms.1
  add_mem' := nuclearEndomorphisms_submodule_axioms.2.1
  smul_mem' := nuclearEndomorphisms_submodule_axioms.2.2

/-- Paper: Definition C.3.4.2, p. 697. The rank-one map from a functional
and a vector belongs to the submodule of nuclear endomorphisms.
Deviation: This is a check of the submodule's carrier. -/
theorem smulRight_mem_nuclearEndomorphisms (φ : H →L[ℂ] ℂ) (y : H) :
    φ.smulRight y ∈ nuclearEndomorphisms H :=
  isNuclearOperator_smulRight φ y

/-- Paper: Definition C.3.4.2(1), p. 697. The Hilbert-space trace sums the
diagonal entries of a nuclear operator using a choice of Hilbert basis.
Deviation: Mathlib's inner product is linear in the second argument. -/
def hilbertTrace (T : nuclearEndomorphisms H) : ℂ :=
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  ∑' i, ⟪b i, T.val (b i)⟫_ℂ

/-- Paper: Definition C.3.4.2(1), p. 697. The Hilbert-space trace of a rank-one
operator evaluates its functional at its spanning vector.
Deviation: This is a check of the trace formula and inner-product convention. -/
theorem hilbertTrace_smulRight (φ : H →L[ℂ] ℂ) (y : H) :
    hilbertTrace ⟨φ.smulRight y, smulRight_mem_nuclearEndomorphisms φ y⟩ = φ y := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  change ∑' i, ⟪b i, φ.smulRight y (b i)⟫_ℂ = φ y
  have h := φ.hasSum (b.hasSum_repr y)
  simp only [map_smul, smul_eq_mul, b.repr_apply_apply] at h
  refine (h.congr_fun fun i ↦ ?_).tsum_eq
  rw [ContinuousLinearMap.smulRight_apply, inner_smul_right, mul_comm]

/-- Paper: Definition C.3.4.2(1), p. 697. The Hilbert-space trace is the
nuclear trace from Proposition C.3.2.1 on the same endomorphism. -/
theorem hilbertTrace_eq_nuclearTrace (T : nuclearEndomorphisms H) :
    hilbertTrace T = nuclearTrace hilbert_approximationProperty T.val T.property := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation T.val).mp T.property
  obtain ⟨C, hC₀, hC⟩ :=
    ((NormedSpace.equicontinuous_tfae r.functional).out 1 7).mp r.equicontinuous
  obtain ⟨D, hD⟩ :=
    ((NormedSpace.isVonNBounded_iff ℂ).mp r.isBanachDisc.bounded).exists_norm_le
  have hcost : Summable (fun n ↦ ‖r.coeff n‖ * (‖r.functional n‖ * ‖(r.vector n : H)‖)) := by
    refine (r.summable_coeff.mul_right (C * D)).of_nonneg_of_le (fun n ↦ by positivity) ?_
    intro n
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hC n) (hD _ (r.vector_mem n)) (norm_nonneg _) hC₀) (norm_nonneg _)
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have htrace := ((exists_nuclearTrace_hasSum hilbert_approximationProperty
    T.val T.property).exists.choose_spec r).2
  exact (tsum_hilbertDiagonal_eq_series b T.val r.coeff r.functional
    (fun n ↦ (r.vector n : H)) hcost r.hasSum).trans htrace.tsum_eq

/-- Paper: Definition C.3.4.2(2), p. 697. The trace norm of a nuclear operator
sums the real diagonal entries of the positive square root of its adjoint
times itself, using a choice of Hilbert basis. -/
def traceNorm (T : nuclearEndomorphisms H) : ℝ :=
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  ∑' i, (⟪b i, CFC.sqrt (T.val.adjoint * T.val) (b i)⟫_ℂ).re

/-- The positive square root of `A.adjoint * A` is nuclear if `A` is nuclear. -/
private theorem isNuclearOperator_sqrt_adjoint_mul (A : H →L[ℂ] H)
    (hA : IsNuclearOperator A) : IsNuclearOperator (CFC.sqrt (A.adjoint * A)) := by
  generalize hB : CFC.sqrt (A.adjoint * A) = B
  have hB_pos : 0 ≤ B := by
    rw [← hB]
    exact CFC.sqrt_nonneg _
  have hB_adj : B.adjoint = B :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hB_pos).isSelfAdjoint.adjoint_eq
  have hA_pos : 0 ≤ A.adjoint * A :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self A)
  have hB_sq : B * B = A.adjoint * A := by
    simpa only [hB] using CFC.sqrt_mul_sqrt_self (A.adjoint * A) hA_pos
  have hB_comp : B.comp B = A.adjoint.comp A :=
    calc
      B.comp B = B * B := (ContinuousLinearMap.mul_def B B).symm
      _ = A.adjoint * A := hB_sq
      _ = A.adjoint.comp A := ContinuousLinearMap.mul_def A.adjoint A
  have hB_norm (x : H) : ‖B x‖ ≤ ‖A x‖ := by
    have h := B.apply_norm_eq_sqrt_inner_adjoint_right x
    rw [hB_adj, hB_comp] at h
    exact (h.trans (A.apply_norm_eq_sqrt_inner_adjoint_right x).symm).le
  obtain ⟨S, _, hS⟩ := exists_contraction_comp_eq_of_norm_le A B hB_norm
  rw [← hS]
  obtain ⟨a, φ, y, ha, hφ, hy, hseries⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr
    ⟨a, φ, S ∘ y, ha, hφ, ?_, fun x ↦ ?_⟩
  · simpa only [map_zero] using (S.continuous.tendsto 0).comp hy
  · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
      S.hasSum (hseries x)

/-- Paper: Definition C.3.4.2(2), p. 697. The trace norm is the sum of the
diagonal series for the positive square root in every Hilbert basis. -/
theorem hasSum_traceNorm_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : nuclearEndomorphisms H) :
    HasSum (fun i ↦ (⟪b i, CFC.sqrt (T.val.adjoint * T.val) (b i)⟫_ℂ).re) (traceNorm T) := by
  let B := CFC.sqrt (T.val.adjoint * T.val)
  have hB : IsNuclearOperator B := isNuclearOperator_sqrt_adjoint_mul T.val T.property
  let c := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  change HasSum (fun i ↦ (⟪b i, B (b i)⟫_ℂ).re) (∑' j, (⟪c j, B (c j)⟫_ℂ).re)
  have hc := Complex.reCLM.hasSum (summable_norm_hilbertDiagonal c B hB).of_norm.hasSum
  have hb := Complex.reCLM.hasSum (summable_norm_hilbertDiagonal b B hB).of_norm.hasSum
  simp only [Complex.reCLM_apply] at hc hb
  rw [hc.tsum_eq, ← tsum_hilbertDiagonal_eq b c B hB]
  exact hb

/-- A bounded endomorphism and the positive square root of its Gram operator
each factor through the other by bounded postcomposition. -/
private theorem exists_factors_sqrt_adjoint_mul (T : H →L[ℂ] H) :
    ∃ U V : H →L[ℂ] H,
      U * CFC.sqrt (T.adjoint * T) = T ∧ V * T = CFC.sqrt (T.adjoint * T) := by
  let S := CFC.sqrt (T.adjoint * T)
  have hS : S * S = T.adjoint * T :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      T.isPositive_adjoint_comp_self)
  have hadj : S.adjoint = S :=
    IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (show 0 ≤ S from CFC.sqrt_nonneg _))
  have hnorm (x : H) : ‖T x‖ = ‖S x‖ := by
    rw [T.apply_norm_eq_sqrt_inner_adjoint_right, S.apply_norm_eq_sqrt_inner_adjoint_right]
    change Real.sqrt (RCLike.re ⟪x, (T.adjoint * T) x⟫_ℂ) =
      Real.sqrt (RCLike.re ⟪x, (S.adjoint * S) x⟫_ℂ)
    rw [hadj, hS]
  -- Extend the factor from the range of A to its closure, then project onto it.
  have factor (A D : H →L[ℂ] H) (h : ∀ x, ‖D x‖ = ‖A x‖) :
      ∃ U : H →L[ℂ] H, U * A = D := by
    let W := A.toLinearMap.range.topologicalClosure
    let i : H →ₗ[ℂ] W := A.toLinearMap.codRestrict W
      (fun x ↦ A.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩)
    have hi : DenseRange i := by
      have hincl : DenseRange (Set.inclusion A.toLinearMap.range.le_topologicalClosure) :=
        (denseRange_inclusion_iff _).2 subset_rfl
      exact hincl.comp (show Function.Surjective A.toLinearMap.rangeRestrict from
        fun ⟨x, y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩).denseRange (continuous_inclusion _)
    let j := D.toLinearMap.extendOfNorm i
    have hj (x : H) : j (i x) = D x :=
      LinearMap.extendOfNorm_eq hi ⟨1, fun x ↦ by simpa [i] using (h x).le⟩ x
    refine ⟨j.comp W.orthogonalProjectionOnto, ?_⟩
    ext x
    change j (W.orthogonalProjectionOnto (A x)) = D x
    exact (congrArg j (W.orthogonalProjectionOnto_mem_subspace_eq_self (i x))).trans (hj x)
  obtain ⟨U, hU⟩ := factor S T hnorm
  obtain ⟨V, hV⟩ := factor T S (fun x ↦ (hnorm x).symm)
  exact ⟨U, V, hU, hV⟩

/-- Paper: Lemma C.3.4.4(1), p. 698. Postcomposition by a bounded endomorphism
preserves nuclearity by applying the endomorphism to the vector sequence. -/
private theorem isNuclearOperator_postcomp_hilbert {T : H →L[ℂ] H}
    (hT : IsNuclearOperator T) (U : H →L[ℂ] H) : IsNuclearOperator (U * T) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr
    ⟨c, φ, U ∘ y, hc, hφ, (U.continuous.tendsto' 0 0 (map_zero U)).comp hy, fun x ↦ ?_⟩
  change HasSum (fun n ↦ (c n * φ n x) • U (y n)) (U (T x))
  simpa only [map_smul] using U.hasSum (hsum x)

/-- If the images of a Hilbert basis under a self-adjoint operator have
square-summable norms, its square has a nuclear rank-one expansion. -/
private theorem isNuclearOperator_square_of_summable_basis {ι : Type*}
    (b : HilbertBasis ι ℂ H) (B : H →L[ℂ] H) (hB : B.adjoint = B)
    (hs : Summable (fun i ↦ ‖B (b i)‖ ^ 2)) : IsNuclearOperator (B * B) := by
  classical
  -- Only the support of the square-summable family contributes to the expansion.
  let cost (i : ι) := ‖B (b i)‖ ^ 2
  let I := Function.support cost
  have : Countable I := hs.countable_support
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  let r : ℕ → H := extend e (fun i ↦ B (b i.val)) 0
  let y (n : ℕ) := normalizedFactor (r n)
  let c (n : ℕ) : ℂ := (‖r n‖ : ℂ) ^ 2
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine isBanachNuclear_of_bounded_series (B * B) c (fun n ↦ innerSL ℂ (y n)) y ?_
    ⟨1, fun n ↦ (innerSL_apply_norm ℂ _).trans_le (norm_normalizedFactor_le_one _)⟩
    (fun n ↦ norm_normalizedFactor_le_one _) fun x ↦ ?_
  · have h := (summable_extend_zero he).mpr (hs.subtype (fun i ↦ i ∈ I))
    refine h.congr fun n ↦ ?_
    rcases em (∃ i, e i = n) with ⟨i, rfl⟩ | hn
    · simp [r, c, he.extend_apply]
    · simp [r, c, extend_apply' _ _ _ hn]
  · let term (i : ι) := ⟪B (b i), x⟫_ℂ • B (b i)
    have hterm : HasSum term ((B * B) x) := by
      refine (B.hasSum (b.hasSum_repr (B x))).congr_fun fun i ↦ ?_
      simp only [term, map_smul, b.repr_apply_apply, ← B.adjoint_inner_left, hB]
    have hsupport : Function.support term ⊆ I := by
      intro i hi
      by_contra h
      have hz : B (b i) = 0 := by simpa [I, cost, Function.mem_support] using h
      exact hi (by simp [term, hz])
    have hsub := (hasSum_subtype_iff_of_support_subset hsupport).mpr hterm
    refine ((hasSum_extend_zero he).mpr hsub).congr_fun fun n ↦ ?_
    have heq : extend e (term ∘ Subtype.val) 0 n = ⟪r n, x⟫_ℂ • r n := by
      rcases em (∃ i, e i = n) with ⟨i, rfl⟩ | hn
      · simp only [r, he.extend_apply, term, Function.comp_apply]
      · simp [r, extend_apply' _ _ _ hn]
    rw [heq]
    symm
    calc
      _ = ⟪(‖r n‖ : ℂ) • y n, x⟫_ℂ • ((‖r n‖ : ℂ) • y n) := by
        rw [show (‖r n‖ : ℂ) • y n = r n from norm_smul_normalizedFactor _]
      _ = _ := by
        simp only [inner_smul_left, Complex.conj_ofReal, smul_smul, innerSL_apply_apply, c]
        congr 1
        ring

/-- Paper: Definition C.3.4.2(2), p. 697. Nuclearity is equivalent to finiteness
of the positive-square-root diagonal sum in any given Hilbert basis. -/
theorem isNuclearOperator_iff_summable_traceNorm_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) :
    IsNuclearOperator T ↔
      Summable (fun i ↦ (⟪b i, CFC.sqrt (T.adjoint * T) (b i)⟫_ℂ).re) := by
  let S := CFC.sqrt (T.adjoint * T)
  have hS : 0 ≤ S := CFC.sqrt_nonneg _
  obtain ⟨U, V, hU, hV⟩ := exists_factors_sqrt_adjoint_mul T
  change U * S = T at hU
  change V * T = S at hV
  change IsNuclearOperator T ↔ Summable (fun i ↦ (⟪b i, S (b i)⟫_ℂ).re)
  constructor
  · intro hT
    have hSn : IsNuclearOperator S := hV ▸ isNuclearOperator_postcomp_hilbert hT V
    exact (summable_norm_hilbertDiagonal b S hSn).of_nonneg_of_le
      (fun i ↦ (ContinuousLinearMap.nonneg_iff_isPositive.mp hS).re_inner_nonneg_right (b i))
      (fun i ↦ Complex.re_le_norm _)
  · intro hs
    let B := CFC.sqrt S
    have hsq : B * B = S := CFC.sqrt_mul_sqrt_self _ hS
    have hB : B.adjoint = B :=
      IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (show 0 ≤ B from CFC.sqrt_nonneg _))
    have hb : Summable (fun i ↦ ‖B (b i)‖ ^ 2) := hs.congr fun i ↦ by
      rw [B.apply_norm_sq_eq_inner_adjoint_right]
      change _ = (⟪b i, (B.adjoint * B) (b i)⟫_ℂ).re
      rw [hB, hsq]
    have hSn : IsNuclearOperator S := hsq ▸ isNuclearOperator_square_of_summable_basis b B hB hb
    exact hU ▸ isNuclearOperator_postcomp_hilbert hSn U

open InnerProductSpace in
/-- Paper: Definition C.3.4.2(2), p. 697. A rank-one map has trace norm equal
to the product of the functional and vector norms.
Deviation: This is a check of the square root and trace norm normalization. -/
theorem traceNorm_smulRight (φ : H →L[ℂ] ℂ) (y : H) :
    traceNorm ⟨φ.smulRight y, smulRight_mem_nuclearEndomorphisms φ y⟩ = ‖φ‖ * ‖y‖ := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  change ∑' i, (⟪b i, CFC.sqrt ((φ.smulRight y).adjoint * φ.smulRight y) (b i)⟫_ℂ).re = _
  by_cases hφ : φ = 0
  · simp [hφ, CFC.sqrt_zero]
  let u := (toDual ℂ H).symm φ
  have hu : ‖u‖ = ‖φ‖ := (toDual ℂ H).symm.norm_map φ
  have hu₀ : ‖u‖ ≠ 0 := hu ▸ norm_ne_zero_iff.mpr hφ
  let c := ‖y‖ / ‖u‖
  have hc : c * ‖u‖ = ‖y‖ := div_mul_cancel₀ _ hu₀
  have hT : φ.smulRight y = rankOne ℂ y u := by
    ext x
    rw [ContinuousLinearMap.smulRight_apply, rankOne_apply, toDual_symm_apply]
  have hmul (v w : H) :
      rankOne ℂ v w * rankOne ℂ w v = (‖w‖ ^ 2 : ℝ) • rankOne ℂ v v := by
    rw [ContinuousLinearMap.mul_def, comp_rankOne, rankOne_apply, inner_self_eq_norm_sq_to_K]
    ext x
    simp only [rankOne_apply, smul_apply]
    change ⟪v, x⟫_ℂ • ((‖w‖ : ℂ) ^ 2 • v) = _
    rw [← Complex.ofReal_pow, Complex.coe_smul]
    exact smul_comm (⟪v, x⟫_ℂ) (‖w‖ ^ 2 : ℝ) v
  have hsqrt :
      CFC.sqrt ((φ.smulRight y).adjoint * φ.smulRight y) = c • rankOne ℂ u u := by
    apply CFC.sqrt_unique
    · rw [hT, adjoint_rankOne, hmul, smul_mul_assoc, mul_smul_comm, hmul,
        smul_smul, smul_smul]
      congr 1
      calc
        c * c * ‖u‖ ^ 2 = (c * ‖u‖) ^ 2 := by ring
        _ = ‖y‖ ^ 2 := by rw [hc]
    · exact smul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self u))
  rw [hsqrt]
  have hsum := ((b.hasSum_inner_mul_inner u u).mapL Complex.reCLM).mul_left c
  have hvalue : c * Complex.reCLM ⟪u, u⟫_ℂ = ‖φ‖ * ‖y‖ := by
    change c * RCLike.re ⟪u, u⟫_ℂ = _
    rw [← norm_sq_eq_re_inner, pow_two, ← mul_assoc, hc, hu, mul_comm]
  rw [← hvalue]
  refine (hsum.congr_fun fun i ↦ ?_).tsum_eq
  simp only [smul_apply, rankOne_apply, ← Complex.coe_smul, inner_smul_right,
    Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Paper: Lemma C.3.4.3, p. 698. Composing a strongly convergent sequence of
endomorphisms on the right by a fixed compact operator gives convergence
in operator norm. -/
theorem tendsto_compact_comp_of_pointwise {A Q : H →L[ℂ] H} {Qm : ℕ → H →L[ℂ] H}
    (hA : IsCompactOperator A) (hQ : ∀ x, Tendsto (fun m ↦ Qm m x) atTop (𝓝 (Q x))) :
    Tendsto (fun m ↦ (Qm m).comp A) atTop (𝓝 (Q.comp A)) := by
  obtain ⟨K, hK, hAK⟩ := hA.image_closedBall_subset_compact 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heq : Equicontinuous (fun m x ↦ Qm m x) :=
    (PolynormableSpace.banach_steinhaus (𝓕 := Qm)
      (fun x ↦ (hQ x).isVonNBounded_range ℂ)).equicontinuous
  have hrestrict : Equicontinuous (fun m (x : K) ↦ Qm m x) :=
    (equicontinuous_restrict_iff _).mpr (heq.equicontinuousOn K)
  have hunif : TendstoUniformly (fun m (x : K) ↦ Qm m x) (fun x ↦ Q x) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp <|
      (hrestrict.tendsto_uniformFun_iff_pi atTop (fun x ↦ Q x)).mpr
        (tendsto_pi_nhds.mpr fun x ↦ hQ x)
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformly_iff.mp hunif (ε / 2) (half_pos hε)] with m hm
  rw [dist_eq_norm]
  refine (ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le fun x hx ↦ ?_).trans_lt
    (half_lt_self hε)
  have hAx : A x ∈ K := hAK (mem_image_of_mem A (mem_closedBall_zero_iff.mpr hx.le))
  change ‖Qm m (A x) - Q (A x)‖ ≤ ε / 2
  rw [← dist_eq_norm, dist_comm]
  exact (hm ⟨A x, hAx⟩).le

/-- Paper: Lemma C.3.4.4(1), p. 698. Left multiplication by a bounded operator
preserves nuclearity. -/
theorem mul_mem_nuclearEndomorphisms_left (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    A * T.val ∈ nuclearEndomorphisms H :=
  isNuclearOperator_postcomp_hilbert T.property A

/-- Paper: Lemma C.3.4.4(1), p. 698. Right multiplication by a bounded operator
preserves nuclearity. -/
theorem mul_mem_nuclearEndomorphisms_right (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    T.val * A ∈ nuclearEndomorphisms H := by
  change IsNuclearOperator (T.val.comp A)
  simpa only [ContinuousLinearMap.id_comp] using
    isNuclearOperator_comp_comp T.property A (ContinuousLinearMap.id ℂ H) injective_id

/-- An operator and the positive square root of its Gram operator have equal pointwise norms. -/
private theorem norm_sqrt_adjoint_mul_apply (T : H →L[ℂ] H) (x : H) :
    ‖CFC.sqrt (T.adjoint * T) x‖ = ‖T x‖ := by
  let S := CFC.sqrt (T.adjoint * T)
  have hS : S.adjoint = S :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)).isSelfAdjoint.adjoint_eq
  have hsq : S * S = T.adjoint * T :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      T.isPositive_adjoint_comp_self)
  change ‖S x‖ = ‖T x‖
  rw [S.apply_norm_eq_sqrt_inner_adjoint_right, T.apply_norm_eq_sqrt_inner_adjoint_right, hS,
    ← ContinuousLinearMap.mul_def, hsq, ContinuousLinearMap.mul_def]

/-- Taking a second positive square root writes the trace norm as a sum of squared norms. -/
private theorem hasSum_norm_sq_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : nuclearEndomorphisms H) :
    HasSum (fun i ↦ ‖CFC.sqrt (CFC.sqrt (T.val.adjoint * T.val)) (b i)‖ ^ 2) (traceNorm T) := by
  let S := CFC.sqrt (T.val.adjoint * T.val)
  let B := CFC.sqrt S
  have hB : B.adjoint = B :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)).isSelfAdjoint.adjoint_eq
  refine (hasSum_traceNorm_diagonal b T).congr_fun fun i ↦ ?_
  change ‖B (b i)‖ ^ 2 = (⟪b i, S (b i)⟫_ℂ).re
  rw [B.apply_norm_sq_eq_inner_adjoint_right, hB, ← ContinuousLinearMap.mul_def,
    CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)]
  rfl

set_option maxHeartbeats 800000 in
/-- The real diagonal sum of a nuclear operator composed on the left by a contraction
is bounded by its trace norm. -/
private theorem exists_hasSum_re_hilbertDiagonal_mul_le_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : nuclearEndomorphisms H) (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
    ∃ r, HasSum (fun i ↦ (⟪b i, (U * T.val) (b i)⟫_ℂ).re) r ∧ r ≤ traceNorm T := by
  let S := CFC.sqrt (T.val.adjoint * T.val)
  let B := CFC.sqrt S
  have hB : B.adjoint = B :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)).isSelfAdjoint.adjoint_eq
  have hsq : B * B = S := CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
  obtain ⟨W, hW, hWT⟩ := exists_contraction_comp_eq_of_norm_le S T.val
    (fun x ↦ (norm_sqrt_adjoint_mul_apply T.val x).ge)
  have hWT' : W * S = T.val := hWT
  let A := U * W
  have hA : ‖A‖ ≤ 1 :=
    (norm_mul_le U W).trans ((mul_le_of_le_one_left (norm_nonneg W) hU).trans hW)
  have hT : HasSum (fun i ↦ ‖B (b i)‖ ^ 2) (traceNorm T) := hasSum_norm_sq_traceNorm b T
  have hfactor : A * (B * B) = U * T.val := by
    calc
      A * (B * B) = A * S := congrArg (A * ·) hsq
      _ = U * (W * S) := mul_assoc U W S
      _ = U * T.val := congrArg (U * ·) hWT'
  clear_value A B
  have hparseval (x : H) : HasSum (fun i ↦ ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
    simpa [b.repr_apply_apply] using
      (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))
  -- Summing the squared entries of A * B by columns gives the bound for its adjoint.
  let a (j i : ι) := ‖⟪b i, A (B (b j))⟫_ℂ‖ ^ 2
  have hcol (j : ι) : HasSum (a j) (‖A (B (b j))‖ ^ 2) := hparseval (A (B (b j)))
  have hbound (j : ι) : ‖A (B (b j))‖ ^ 2 ≤ ‖B (b j)‖ ^ 2 := by
    have h := (ContinuousLinearMap.opNorm_le_iff (show (0 : ℝ) ≤ 1 by norm_num)).mp hA (B (b j))
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (by simpa only [one_mul] using h)
  have ha : Summable (Function.uncurry a) := by
    refine (summable_prod_of_nonneg (fun p ↦ sq_nonneg _)).mpr ⟨fun j ↦ (hcol j).summable, ?_⟩
    refine hT.summable.of_nonneg_of_le (fun j ↦ tsum_nonneg fun i ↦ sq_nonneg _) (fun j ↦ ?_)
    rw [(hcol j).tsum_eq]
    exact hbound j
  have hrow (i : ι) : HasSum (fun j ↦ a j i) (‖B (A.adjoint (b i))‖ ^ 2) := by
    refine (hparseval (B (A.adjoint (b i)))).congr_fun fun j ↦ ?_
    change ‖⟪b i, A (B (b j))⟫_ℂ‖ ^ 2 = ‖⟪b j, B (A.adjoint (b i))⟫_ℂ‖ ^ 2
    have hentry := B.adjoint_inner_right (b j) (A.adjoint (b i))
    rw [hB] at hentry
    rw [hentry, A.adjoint_inner_right]
    exact congrArg (fun r : ℝ ↦ r ^ 2) (norm_inner_symm (𝕜 := ℂ) (b i) (A (B (b j))))
  have hrow_sum : Summable (fun i ↦ ‖B (A.adjoint (b i))‖ ^ 2) :=
    ha.prod_symm.prod.congr fun i ↦ (hrow i).tsum_eq
  have hrow_bound : (∑' i, ‖B (A.adjoint (b i))‖ ^ 2) ≤ traceNorm T := by
    calc
      _ = ∑' i, ∑' j, a j i := tsum_congr fun i ↦ (hrow i).tsum_eq.symm
      _ = ∑' j, ∑' i, a j i := ha.tsum_comm
      _ ≤ traceNorm T := by
        rw [hT.tsum_eq.symm]
        exact ha.prod.tsum_le_tsum (fun j ↦ (hcol j).tsum_eq ▸ hbound j) hT.summable
  have hdiag := (summable_norm_hilbertDiagonal b _ (mul_mem_nuclearEndomorphisms_left U T)).of_norm
  have hreal := Complex.reCLM.hasSum hdiag.hasSum
  simp only [Complex.reCLM_apply] at hreal
  refine ⟨_, hreal, (hasSum_le (fun i ↦ ?_) hreal ((hT.add hrow_sum.hasSum).div_const 2)).trans ?_⟩
  · rw [← hfactor]
    change (⟪b i, A (B (B (b i)))⟫_ℂ).re ≤ _
    rw [← A.adjoint_inner_left, ← B.adjoint_inner_left, hB]
    exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by
      nlinarith [sq_nonneg (‖B (b i)‖ - ‖B (A.adjoint (b i))‖)]))
  · linarith

/-- The positive square root of the Gram operator scales by the absolute value of the scalar. -/
private theorem sqrt_adjoint_mul_smul (c : ℂ) (T : H →L[ℂ] H) :
    CFC.sqrt ((c • T).adjoint * (c • T)) = ‖c‖ • CFC.sqrt (T.adjoint * T) := by
  apply CFC.sqrt_unique
  · have hT : 0 ≤ T.adjoint * T :=
      ContinuousLinearMap.nonneg_iff_isPositive.mpr T.isPositive_adjoint_comp_self
    rw [smul_mul_smul_comm, ← pow_two, CFC.sqrt_mul_sqrt_self _ hT]
    change ‖c‖ ^ 2 • (T.adjoint * T) = star (c • T) * (c • T)
    rw [star_smul, smul_mul_smul_comm, ← Complex.coe_smul, ← Complex.normSq_eq_norm_sq,
      mul_comm]
    change (Complex.normSq c : ℂ) • (T.adjoint * T) =
      (c * (starRingEnd ℂ) c) • (T.adjoint * T)
    rw [Complex.mul_conj]
  · exact smul_nonneg (norm_nonneg _) (CFC.sqrt_nonneg _)

/-- Paper: Lemma C.3.4.4(1), p. 698. The trace norm satisfies the normed-space
axioms on the complex vector space of nuclear endomorphisms. -/
theorem traceNorm_normedSpaceCore :
    letI : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    NormedSpace.Core ℂ (nuclearEndomorphisms H) := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro T
    change 0 ≤ traceNorm T
    rw [← (hasSum_norm_sq_traceNorm b T).tsum_eq]
    exact tsum_nonneg fun i ↦ sq_nonneg _
  · intro c T
    change traceNorm (c • T) = ‖c‖ * traceNorm T
    refine (hasSum_traceNorm_diagonal b (c • T)).unique
      (((hasSum_traceNorm_diagonal b T).mul_left ‖c‖).congr_fun fun i ↦ ?_)
    change (⟪b i, CFC.sqrt ((c • T.val).adjoint * (c • T.val)) (b i)⟫_ℂ).re =
      ‖c‖ * (⟪b i, CFC.sqrt (T.val.adjoint * T.val) (b i)⟫_ℂ).re
    rw [sqrt_adjoint_mul_smul]
    simp only [smul_apply, ← Complex.coe_smul, inner_smul_right,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  · intro T D
    change traceNorm (T + D) ≤ traceNorm T + traceNorm D
    let X := T + D
    let S := CFC.sqrt (X.val.adjoint * X.val)
    obtain ⟨U, hU, hUX⟩ := exists_contraction_comp_eq_of_norm_le X.val S
      (fun x ↦ (norm_sqrt_adjoint_mul_apply X.val x).le)
    have hUX' : U * (T.val + D.val) = S := hUX
    obtain ⟨r, hr, hrle⟩ := exists_hasSum_re_hilbertDiagonal_mul_le_traceNorm b T U hU
    obtain ⟨s, hs, hsle⟩ := exists_hasSum_re_hilbertDiagonal_mul_le_traceNorm b D U hU
    have hsum : HasSum (fun i ↦ (⟪b i, S (b i)⟫_ℂ).re) (r + s) := by
      refine (hr.add hs).congr_fun fun i ↦ ?_
      rw [← hUX', mul_add, add_apply, inner_add_right, Complex.add_re]
    rw [(hasSum_traceNorm_diagonal b X).unique hsum]
    exact add_le_add hrle hsle
  · intro T
    change traceNorm T = 0 ↔ T = 0
    constructor
    · intro hz
      let S := CFC.sqrt (T.val.adjoint * T.val)
      let B := CFC.sqrt S
      have hsum : HasSum (fun i ↦ ‖B (b i)‖ ^ 2) 0 := hz ▸ hasSum_norm_sq_traceNorm b T
      have hb (i) : B (b i) = 0 := by
        have hi := hsum.summable.le_tsum i (fun j _ ↦ sq_nonneg _)
        rw [hsum.tsum_eq] at hi
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg (B (b i))])
      have hzero (x : H) : B x = 0 := by
        have h := B.hasSum (b.hasSum_repr x)
        simpa only [map_smul, hb, smul_zero, tsum_zero] using h.tsum_eq.symm
      apply Subtype.ext
      ext x
      change T.val x = 0
      apply norm_eq_zero.mp
      rw [← norm_sqrt_adjoint_mul_apply]
      change ‖S x‖ = 0
      rw [show S = B * B from (CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)).symm]
      exact norm_eq_zero.mpr (hzero _)
    · rintro rfl
      exact (hasSum_traceNorm_diagonal b (0 : nuclearEndomorphisms H)).unique (by
        simp [CFC.sqrt_zero])

-- TODO(paper-gap): The equality in (C.3.4.3) is false. For A = diag(1, 0) and
-- T swapping the first coordinate into the second and killing the second, AT = 0
-- while TA = T has trace norm 1. The two separate upper bounds hold.

/-- Paper: Lemma C.3.4.4(2), p. 698. The trace norm of a left product is at
most the operator norm of the left factor times the trace norm of the right factor.
Deviation: The invalid equality in (C.3.4.3) is recorded above. -/
theorem traceNorm_mul_left_le (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    traceNorm ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩ ≤ ‖A‖ * traceNorm T := by
  let S : H →L[ℂ] H := (‖A‖ : ℂ) • T.val
  have hGram : (A * T.val).adjoint * (A * T.val) ≤ S.adjoint * S := by
    apply (ContinuousLinearMap.norm_map_le_norm_map_iff_le (A * T.val) S).mp
    intro x
    simpa [S, norm_smul, Complex.norm_real, abs_of_nonneg (norm_nonneg A)] using
      A.le_opNorm (T.val x)
  have hAbs : CFC.abs (A * T.val) ≤ ‖A‖ • CFC.abs T.val := by
    have h := CFC.sqrt_le_sqrt _ _ hGram
    change CFC.abs (A * T.val) ≤ CFC.abs S at h
    simpa [S, CFC.abs_smul, Complex.norm_real, abs_of_nonneg (norm_nonneg A)] using h
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  refine hasSum_le (fun i ↦ ?_) (hasSum_traceNorm_diagonal b
    ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩)
    ((hasSum_traceNorm_diagonal b T).mul_left ‖A‖)
  have h := (ContinuousLinearMap.le_def.mp hAbs).re_inner_nonneg_right (b i)
  simpa [CFC.abs, ContinuousLinearMap.star_eq_adjoint, inner_sub_right,
    inner_smul_right_eq_smul, sub_nonneg] using h

/-- Moving a bounded factor across a nuclear factor preserves the real diagonal sum. -/
private theorem tsum_re_hilbertDiagonal_mul_comm {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : nuclearEndomorphisms H) (A : H →L[ℂ] H) :
    (∑' i, (⟪b i, (T.val * A) (b i)⟫_ℂ).re) =
      ∑' i, (⟪b i, (A * T.val) (b i)⟫_ℂ).re := by
  obtain ⟨a, φ, y, ha, hφ, hy, hseries⟩ :=
    (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  have hcost (f : ℕ → H →L[ℂ] ℂ) (z : ℕ → H)
      (hf : Tendsto f atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 0)) :
      Summable (fun n ↦ ‖a n‖ * (‖f n‖ * ‖z n‖)) := by
    obtain ⟨C, hC, hfC⟩ := (Metric.isBounded_range_of_tendsto f hf).exists_pos_norm_le
    obtain ⟨R, _, hzR⟩ := (Metric.isBounded_range_of_tendsto z hz).exists_pos_norm_le
    refine (ha.mul_right (C * R)).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hfC _ (mem_range_self n)) (hzR _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  let precomp := (ContinuousLinearMap.compL ℂ H H ℂ).flip A
  have hφA : Tendsto (fun n ↦ (φ n).comp A) atTop (𝓝 0) := by
    change Tendsto (⇑precomp ∘ φ) atTop (𝓝 0)
    simpa only [map_zero] using (precomp.continuous.tendsto 0).comp hφ
  have hyA : Tendsto (A ∘ y) atTop (𝓝 0) := by
    simpa only [map_zero] using (A.continuous.tendsto 0).comp hy
  have hright := tsum_hilbertDiagonal_eq_series b (T.val * A) a
    (fun n ↦ (φ n).comp A) y (hcost _ _ hφA hy) (fun x ↦ hseries (A x))
  have hleft := tsum_hilbertDiagonal_eq_series b (A * T.val) a
    φ (A ∘ y) (hcost _ _ hφ hyA) (fun x ↦ by
      simpa only [map_smul, Function.comp_apply, mul_apply_eq_comp,
        ContinuousLinearMap.comp_apply] using A.hasSum (hseries x))
  have h₁ := (summable_norm_hilbertDiagonal b _ (mul_mem_nuclearEndomorphisms_right A T)).of_norm
  have h₂ := (summable_norm_hilbertDiagonal b _ (mul_mem_nuclearEndomorphisms_left A T)).of_norm
  change (∑' i, Complex.reCLM ⟪b i, (T.val * A) (b i)⟫_ℂ) =
    ∑' i, Complex.reCLM ⟪b i, (A * T.val) (b i)⟫_ℂ
  rw [← Complex.reCLM.map_tsum h₁, ← Complex.reCLM.map_tsum h₂, hright, hleft]
  rfl

/-- Paper: Lemma C.3.4.4(2), p. 698. The trace norm of a right product is at
most the operator norm of the right factor times the trace norm of the left factor.
Deviation: The invalid equality in (C.3.4.3) is recorded above. -/
theorem traceNorm_mul_right_le (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    traceNorm ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩ ≤ ‖A‖ * traceNorm T := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  let X : nuclearEndomorphisms H := ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩
  change traceNorm X ≤ ‖A‖ * traceNorm T
  let S := CFC.sqrt (X.val.adjoint * X.val)
  have hS := hasSum_traceNorm_diagonal b X
  change HasSum (fun i ↦ (⟪b i, S (b i)⟫_ℂ).re) (traceNorm X) at hS
  by_cases hA : A = 0
  · have hX : X.val = 0 := by simp [X, hA]
    have hS₀ : S = 0 := by simp [S, hX, CFC.sqrt_zero]
    rw [hS₀] at hS
    simp only [hA, norm_zero, zero_mul, zero_apply, inner_zero_right, Complex.zero_re] at hS ⊢
    exact (hS.unique hasSum_zero).le
  obtain ⟨U, hU, hUX⟩ := exists_contraction_comp_eq_of_norm_le X.val S
    (fun x ↦ (norm_sqrt_adjoint_mul_apply X.val x).le)
  let Y : nuclearEndomorphisms H := ⟨U * T.val, mul_mem_nuclearEndomorphisms_left U T⟩
  have hSY : Y.val * A = S := by
    change U * T.val * A = S
    rw [mul_assoc]
    exact hUX
  let V : H →L[ℂ] H := ‖A‖⁻¹ • (A * U)
  have hV : ‖V‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg A),
      inv_mul_le_one₀ (norm_pos_iff.mpr hA)]
    exact (norm_mul_le A U).trans (mul_le_of_le_one_right (norm_nonneg A) hU)
  have hY : A * Y.val = ‖A‖ • (V * T.val) := by
    change A * (U * T.val) = ‖A‖ • ((‖A‖⁻¹ • (A * U)) * T.val)
    rw [← mul_assoc, smul_mul_assoc, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hA), one_smul]
  obtain ⟨r, hr, hrle⟩ := exists_hasSum_re_hilbertDiagonal_mul_le_traceNorm b T V hV
  have hsum : HasSum (fun i ↦ (⟪b i, (A * Y.val) (b i)⟫_ℂ).re) (‖A‖ * r) := by
    refine (hr.mul_left ‖A‖).congr_fun fun i ↦ ?_
    simp only [hY, smul_apply, ← Complex.coe_smul, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hS.tsum_eq, ← hSY, tsum_re_hilbertDiagonal_mul_comm b Y A, hsum.tsum_eq]
  exact mul_le_mul_of_nonneg_left hrle (norm_nonneg A)

/-- Paper: Lemma C.3.4.4(3), p. 698. The trace is complex linear. -/
theorem hilbertTrace_linear :
    ∃ f : nuclearEndomorphisms H →ₗ[ℂ] ℂ, ∀ T, f T = hilbertTrace T := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have hs (T : nuclearEndomorphisms H) :
      Summable (fun i ↦ ⟪b i, T.val (b i)⟫_ℂ) :=
    (summable_norm_hilbertDiagonal b T.val T.property).of_norm
  refine ⟨{ toFun := hilbertTrace
            map_add' := ?_
            map_smul' := ?_ }, fun _ ↦ rfl⟩
  · intro T S
    change (∑' i, ⟪b i, (T.val + S.val) (b i)⟫_ℂ) =
      (∑' i, ⟪b i, T.val (b i)⟫_ℂ) + ∑' i, ⟪b i, S.val (b i)⟫_ℂ
    simp only [add_apply, inner_add_right]
    exact (hs T).tsum_add (hs S)
  · intro c T
    change (∑' i, ⟪b i, (c • T.val) (b i)⟫_ℂ) =
      c • ∑' i, ⟪b i, T.val (b i)⟫_ℂ
    simp only [smul_apply, inner_smul_right, smul_eq_mul]
    exact (hs T).tsum_mul_left c

/-- Paper: Lemma C.3.4.4(3), p. 698. The modulus of the trace is bounded by the trace
norm, which gives continuity for the trace norm.

Deviation: The inequality prints the undefined norm subscript r. The continuity assertion in
the same sentence uses the trace norm defined in Definition C.3.4.2(2), which is the bound here.
-/
theorem norm_hilbertTrace_le (T : nuclearEndomorphisms H) :
    ‖hilbertTrace T‖ ≤ traceNorm T := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  let z := hilbertTrace T
  -- Rotate the trace onto the nonnegative real axis.
  let c : ℂ := star z / (‖z‖ : ℂ)
  have hc : ‖c‖ ≤ 1 := by
    dsimp only [c]
    rw [norm_div, Complex.star_def, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg z)]
    exact div_self_le_one _
  have hcz : (c * z).re = ‖z‖ := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two, mul_self_div_self, Complex.ofReal_re]
  let U : H →L[ℂ] H := c • ContinuousLinearMap.id ℂ H
  have hU : ‖U‖ ≤ 1 := by
    dsimp only [U]
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans hc
  obtain ⟨r, hr, hr_le⟩ := exists_hasSum_re_hilbertDiagonal_mul_le_traceNorm b T U hU
  have htrace : HasSum (fun i ↦ ⟪b i, T.val (b i)⟫_ℂ) z :=
    (summable_norm_hilbertDiagonal b T.val T.property).of_norm.hasSum
  have hreal : HasSum (fun i ↦ (⟪b i, (U * T.val) (b i)⟫_ℂ).re) (c * z).re := by
    simpa only [U, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_smul_right, Complex.reCLM_apply] using
      Complex.reCLM.hasSum (htrace.mul_left c)
  rw [← hcz, hreal.unique hr]
  exact hr_le

/-- Paper: Lemma C.3.4.4(4), p. 698. The canonical image of the algebraic tensor
of the dual and the Hilbert space consists of nuclear operators. -/
theorem tensorToFiniteRank_mem_nuclearEndomorphisms (z : StrongDual ℂ H ⊗[ℂ] H) :
    tensorToFiniteRank z ∈ nuclearEndomorphisms H := by
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    convert smulRight_mem_nuclearEndomorphisms φ y using 1
    ext x
    exact tensorToFiniteRank_tmul φ y x
  | add z w hz hw => rw [map_add]; exact add_mem hz hw

/-- The trace norm of a nuclear series is bounded by the sum of its rank-one costs. -/
private theorem traceNorm_le_tsum_rankOne_cost (T : nuclearEndomorphisms H)
    (a : ℕ → ℂ) (φ : ℕ → H →L[ℂ] ℂ) (y : ℕ → H)
    (hcost : Summable (fun n ↦ ‖a n‖ * (‖φ n‖ * ‖y n‖)))
    (hseries : ∀ x, HasSum (fun n ↦ (a n * φ n x) • y n) (T.val x)) :
    traceNorm T ≤ ∑' n, ‖a n‖ * (‖φ n‖ * ‖y n‖) := by
  let S := CFC.sqrt (T.val.adjoint * T.val)
  obtain ⟨U, hU, hUS⟩ := exists_contraction_comp_eq_of_norm_le T.val S
    (fun x ↦ (norm_sqrt_adjoint_mul_apply T.val x).le)
  have hnorm (n : ℕ) : ‖U (y n)‖ ≤ ‖y n‖ :=
    (U.le_opNorm (y n)).trans (mul_le_of_le_one_left (norm_nonneg _) hU)
  have hle (n : ℕ) : ‖a n‖ * (‖φ n‖ * ‖U (y n)‖) ≤ ‖a n‖ * (‖φ n‖ * ‖y n‖) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg _))
      (norm_nonneg _)
  have hcostU : Summable (fun n ↦ ‖a n‖ * (‖φ n‖ * ‖U (y n)‖)) :=
    hcost.of_nonneg_of_le (fun _ ↦ by positivity) hle
  have hseriesS (x : H) : HasSum (fun n ↦ (a n * φ n x) • U (y n)) (S x) := by
    rw [← hUS]
    simpa only [ContinuousLinearMap.comp_apply, map_smul] using U.hasSum (hseries x)
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have hS := isNuclearOperator_sqrt_adjoint_mul T.val T.property
  have hre := Complex.reCLM.hasSum (summable_norm_hilbertDiagonal b S hS).of_norm.hasSum
  simp only [Complex.reCLM_apply] at hre
  rw [(hasSum_traceNorm_diagonal b T).unique hre,
    tsum_hilbertDiagonal_eq_series b S a φ (fun n ↦ U (y n)) hcostU hseriesS]
  have hentry (n : ℕ) : ‖a n * φ n (U (y n))‖ ≤ ‖a n‖ * (‖φ n‖ * ‖y n‖) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ((φ n).le_opNorm (U (y n))) (norm_nonneg _)).trans (hle n)
  exact (Complex.re_le_norm _).trans
    ((hcost.of_norm_bounded hentry).hasSum.norm_le_of_bounded hcost.hasSum hentry)

/-- Paper: Lemma C.3.4.4(4), p. 698. Finite-rank operators from the canonical
tensor map approximate every nuclear endomorphism in trace norm. -/
theorem exists_tensorToFiniteRank_traceNorm_sub_lt (T : nuclearEndomorphisms H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : StrongDual ℂ H ⊗[ℂ] H,
      traceNorm (T - ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩) < ε := by
  obtain ⟨a, φ, y, ha, hφ, hy, hseries⟩ := (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
  obtain ⟨R, _, hyR⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
  let cost (n : ℕ) := ‖a n‖ * (‖φ n‖ * ‖y n‖)
  have hcost : Summable cost := by
    have hnonneg (n : ℕ) : 0 ≤ cost n := by
      dsimp [cost]
      positivity
    refine (ha.mul_right (C * R)).of_nonneg_of_le hnonneg fun n ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hφC _ (mem_range_self n)) (hyR _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add cost).eventually_lt_const hε).exists
  let z : StrongDual ℂ H ⊗[ℂ] H := ∑ n ∈ Finset.range N, a n • (φ n ⊗ₜ[ℂ] y n)
  refine ⟨z, lt_of_le_of_lt (traceNorm_le_tsum_rankOne_cost _
    (fun n ↦ a (n + N)) (fun n ↦ φ (n + N)) (fun n ↦ y (n + N))
    ((summable_nat_add_iff N).mpr hcost) ?_) hN⟩
  intro x
  change HasSum (fun n ↦ (a (n + N) * φ (n + N) x) • y (n + N))
    (T.val x - tensorToFiniteRank z x)
  simpa only [z, map_sum, sum_apply, map_smul, smul_apply, tensorToFiniteRank_tmul, mul_smul] using
    (hasSum_nat_add_iff' N).mpr (hseries x)

/-- Paper: Lemma C.3.4.4(4), p. 698. On a separable Hilbert space there is a
countable trace-norm dense set of nuclear endomorphisms.
Deviation: Density is expressed by approximation in every positive trace-norm radius. -/
theorem exists_countable_traceNorm_dense [SeparableSpace H] :
    ∃ S : Set (nuclearEndomorphisms H), S.Countable ∧
      ∀ (T : nuclearEndomorphisms H) (ε : ℝ), 0 < ε → ∃ A ∈ S, traceNorm (T - A) < ε := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let : NormedAddCommGroup (nuclearEndomorphisms H) :=
    NormedAddCommGroup.ofCore (traceNorm_normedSpaceCore (H := H))
  let : SeminormedAddCommGroup (nuclearEndomorphisms H) :=
    (inferInstance : NormedAddCommGroup (nuclearEndomorphisms H)).toSeminormedAddCommGroup
  let : MetricSpace (nuclearEndomorphisms H) := NormedAddCommGroup.toMetricSpace
  let : PseudoMetricSpace (nuclearEndomorphisms H) := MetricSpace.toPseudoMetricSpace
  let : UniformSpace (nuclearEndomorphisms H) := PseudoMetricSpace.toUniformSpace
  let : TopologicalSpace (nuclearEndomorphisms H) := UniformSpace.toTopologicalSpace
  let : NormedSpace ℂ (nuclearEndomorphisms H) :=
    NormedSpace.ofCore (traceNorm_normedSpaceCore (H := H))
  let : SeparableSpace (StrongDual ℂ H) :=
    (InnerProductSpace.toDual ℂ H).surjective.denseRange.separableSpace
      (InnerProductSpace.toDual ℂ H).isometry.continuous
  have hdist (T A : nuclearEndomorphisms H) : dist T A = traceNorm (T - A) := by
    rw [dist_eq_norm]
    rfl
  let f : StrongDual ℂ H × H → nuclearEndomorphisms H := fun p =>
    ⟨p.1.smulRight p.2, smulRight_mem_nuclearEndomorphisms p.1 p.2⟩
  have hf : Continuous f := by
    apply IsBoundedBilinearMap.continuous (𝕜 := ℂ)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y z
      ext t
      simp [f, add_smul]
    · intro c x y
      ext t
      simp [f, mul_smul]
    · intro x y z
      ext t
      simp [f, smul_add]
    · intro c x y
      ext t
      simp only [f, Submodule.coe_smul, smul_apply, ContinuousLinearMap.smulRight_apply]
      exact smul_comm _ _ _
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x y
      change traceNorm ⟨x.smulRight y, smulRight_mem_nuclearEndomorphisms x y⟩ ≤ 1 * ‖x‖ * ‖y‖
      simpa using (traceNorm_smulRight x y).le
  let V := Submodule.span ℂ (range f)
  have hV : IsSeparable (V : Set (nuclearEndomorphisms H)) := (isSeparable_range hf).span
  have hmem (z : StrongDual ℂ H ⊗[ℂ] H) :
      (⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩ :
        nuclearEndomorphisms H) ∈ V := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      apply Submodule.subset_span
      refine ⟨(x, y), ?_⟩
      ext t
      simp [f, tensorToFiniteRank_tmul]
    | add x y hx hy =>
      convert V.add_mem hx hy using 1 <;> ext t <;> simp
  have hd : Dense (V : Set (nuclearEndomorphisms H)) := by
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro T
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T hε
    refine ⟨⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩, hmem z, ?_⟩
    rw [hdist]
    exact hz
  obtain ⟨S, hS, hSc⟩ := hV
  refine ⟨S, hS, ?_⟩
  intro T ε hε
  have hT : T ∈ closure S := closure_minimal hSc isClosed_closure (hd T)
  obtain ⟨A, hAS, hA⟩ := Metric.mem_closure_iff.mp hT ε hε
  rw [hdist] at hA
  exact ⟨A, hAS, hA⟩

-- TODO(paper-gap): The proof on p. 699 sums distinct eigenvalues to compute the
-- trace norm. Multiplicities are required, as shown by the identity on ℂ².
-- The argument below uses a rank-one expansion instead.

/-- The trace norm is nonnegative. -/
private theorem traceNorm_nonneg (T : nuclearEndomorphisms H) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using (traceNorm_normedSpaceCore (H := H)).norm_nonneg T

/-- The trace norm of zero is zero. -/
private theorem traceNorm_zero : traceNorm (0 : nuclearEndomorphisms H) = 0 := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using ((traceNorm_normedSpaceCore (H := H)).norm_eq_zero_iff
    (0 : nuclearEndomorphisms H)).mpr rfl

/-- The trace norm satisfies the triangle inequality. -/
private theorem traceNorm_add_le (T D : nuclearEndomorphisms H) :
    traceNorm (T + D) ≤ traceNorm T + traceNorm D := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using (traceNorm_normedSpaceCore (H := H)).norm_triangle T D

/-- The trace norm of a finite sum is at most the sum of the trace norms. -/
private theorem traceNorm_sum_le {α : Type*} (s : Finset α) (T : α → nuclearEndomorphisms H) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [traceNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

omit [CompleteSpace H] in
/-- A finite-rank endomorphism is a finite sum of rank-one maps. -/
private theorem exists_eq_sum_smulRight_of_finiteDimensional_range
    (F : H →L[ℂ] H) (hF : FiniteDimensional ℂ F.toLinearMap.range) :
    ∃ (n : ℕ) (φ : Fin n → H →L[ℂ] ℂ) (y : Fin n → H),
      F = ∑ i, (φ i).smulRight (y i) := by
  let V := F.toLinearMap.range
  have : FiniteDimensional ℂ V := hF
  let b := Module.finBasis ℂ V
  let φ (i : Fin (Module.finrank ℂ V)) : H →L[ℂ] ℂ :=
    (b.coord i).toContinuousLinearMap.comp
      (F.codRestrict V fun x ↦ LinearMap.mem_range_self F.toLinearMap x)
  let y (i : Fin (Module.finrank ℂ V)) : H := b i
  refine ⟨Module.finrank ℂ V, φ, y, ?_⟩
  ext x
  let Fx : V := F.codRestrict V (fun z ↦ LinearMap.mem_range_self F.toLinearMap z) x
  have hsum : ((∑ i, b.repr Fx i • b i : V) : H) = Fx :=
    congrArg Subtype.val (b.sum_repr Fx)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  have hFx : (Fx : H) = F x := by
    simp [Fx]
  calc
    F x = ∑ i, b.repr Fx i • (b i : H) := by rw [← hFx, ← hsum]
    _ = ∑ i, φ i x • y i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hcoord : φ i x = b.repr Fx i := by
        simp only [φ, Fx, LinearMap.coe_toContinuousLinearMap',
          ContinuousLinearMap.comp_apply]
        rfl
      simp [hcoord, y]
    _ = (∑ i, (φ i).smulRight (y i)) x := by
      simp [ContinuousLinearMap.smulRight_apply, sum_apply]

/-- Paper: Lemma C.3.4.4(5), p. 698. The products of a strongly null net and
a fixed finite-rank right factor are nuclear and tend to zero in trace norm.
Deviation: A net is indexed by a nonempty directed preorder. -/
theorem tendsto_traceNorm_mul_finiteRank {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] (P : ι → H →L[ℂ] H) (hP : ∀ x, Tendsto (fun i ↦ P i x) atTop (𝓝 0))
    (F : H →L[ℂ] H) (hF : FiniteDimensional ℂ F.toLinearMap.range) :
    ∃ hm : ∀ i, P i * F ∈ nuclearEndomorphisms H,
      Tendsto (fun i ↦ traceNorm ⟨P i * F, hm i⟩) atTop (𝓝 0) := by
  obtain ⟨n, φ, y, hFeq⟩ := exists_eq_sum_smulRight_of_finiteDimensional_range F hF
  have hmem (i : ι) (k : Fin n) :
      (φ k).smulRight (P i (y k)) ∈ nuclearEndomorphisms H :=
    smulRight_mem_nuclearEndomorphisms (φ k) (P i (y k))
  let S (i : ι) : nuclearEndomorphisms H :=
    ∑ k, ⟨(φ k).smulRight (P i (y k)), hmem i k⟩
  have hS (i : ι) : (S i).val = P i * F := by
    rw [hFeq, ContinuousLinearMap.mul_def]
    ext x
    simp only [S, Submodule.coe_sum, sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, map_sum, map_smul]
  have hm (i : ι) : P i * F ∈ nuclearEndomorphisms H := by
    rw [← hS i]
    exact (S i).property
  have heq (i : ι) : (⟨P i * F, hm i⟩ : nuclearEndomorphisms H) = S i :=
    Subtype.ext (hS i).symm
  refine ⟨hm, ?_⟩
  -- Each rank-one cost is a constant times a strongly null orbit, so the sum tends to zero.
  have hle (i : ι) : traceNorm ⟨P i * F, hm i⟩ ≤ ∑ k, ‖φ k‖ * ‖P i (y k)‖ := by
    rw [heq i]
    refine (traceNorm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [traceNorm_smulRight]
  have hlim : Tendsto (fun i ↦ ∑ k, ‖φ k‖ * ‖P i (y k)‖) atTop (𝓝 0) := by
    have hterm (k : Fin n) : Tendsto (fun i ↦ ‖φ k‖ * ‖P i (y k)‖) atTop (𝓝 0) := by
      have hy : Tendsto (fun i ↦ ‖P i (y k)‖) atTop (𝓝 ‖(0 : H)‖) := by
        refine Tendsto.congr ?_ ((continuous_norm.tendsto (0 : H)).comp (hP (y k)))
        intro i
        rfl
      simp only [norm_zero] at hy
      simpa using Tendsto.const_mul (‖φ k‖) hy
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun k _ ↦ hterm k)
  exact squeeze_zero (fun i ↦ traceNorm_nonneg _) hle hlim

end HilbertOperators

end RiemannMasullo
