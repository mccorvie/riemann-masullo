module

public import RiemannMasullo.AppC_LCTVS.Sec2b
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Analysis.Normed.Module.HahnBanach

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

/-- Paper: Remark C.3.1.1, p. 693. If the strong dual of a complete barrelled
space is complete and nuclear, finite-rank endomorphisms approximate the identity
uniformly on bounded subsets of the source. -/
theorem id_mem_closure_boundedFiniteRank_of_nuclearStrongDual [CompleteSpace E]
    [BarrelledSpace ℂ E] [CompleteSpace (StrongDual ℂ E)] (h : IsNuclearTVS (StrongDual ℂ E)) :
    (ContinuousLinearMap.id ℂ E : E →Lᵦ E) ∈
      closure (range (projectiveTensorToOperators (E := E) (F := E))) := by sorry

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

/-- Paper: §C.3.1, p. 694. A continuous rank-one operator is nuclear.
Deviation: This is a check of the local factorization definition. -/
theorem isNuclearOperator_smulRight (φ : E →L[ℂ] ℂ) (y : F) :
    IsNuclearOperator (φ.smulRight y) := by sorry

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

/-- Paper: (C.3.1.3), p. 694. A rank-one map can be presented with one term and
the given functional, with any prescribed nonzero coefficient for that term.
Deviation: This is a check of the normalization in the presentation definition. -/
theorem nuclearPresentation_smulRight (φ : E →L[ℂ] ℂ) (y : F) (c : ℂ) (hc : c ≠ 0) :
    ∃ r : NuclearPresentation (φ.smulRight y),
      r.coeff 0 = c ∧ r.functional 0 = φ ∧ (r.vector 0 : F) = c⁻¹ • y ∧
        ∀ n, r.coeff (n + 1) = 0 := by sorry

/-- Paper: Lemma C.3.1.2, p. 694. A continuous linear operator is nuclear exactly
when it has a nuclear presentation. -/
theorem isNuclearOperator_iff_nonempty_presentation (A : E →L[ℂ] F) :
    IsNuclearOperator A ↔ Nonempty (NuclearPresentation A) := by sorry

/-- Paper: Lemma C.3.1.2, p. 694. A nuclear operator admits a presentation with
functionals tending to zero uniformly on one zero-neighborhood and vectors
tending to zero for the gauge norm of their disc. -/
theorem exists_nuclearPresentation_tendsto_zero (A : E →L[ℂ] F) (hA : IsNuclearOperator A) :
    ∃ (r : NuclearPresentation A) (U : Set E), U ∈ 𝓝 0 ∧
      TendstoUniformlyOn (fun n x ↦ r.functional n x) 0 atTop U ∧
      Tendsto (fun n ↦ gauge ((↑) ⁻¹' r.disc : Set (Submodule.span ℂ r.disc)) (r.vector n))
        atTop (𝓝 0) := by sorry

end LocallyConvexOperators

section BanachTensor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Paper: (C.3.1.2), p. 693. On Banach spaces the canonical tensor map is continuous
for the operator norm on its target. -/
theorem continuous_tensorToFiniteRank_opNorm :
    Continuous (fun z : ProjectiveTensor (StrongDual ℂ E) F ↦
      (tensorToFiniteRank z : E →L[ℂ] F)) := by sorry

/-- Paper: (C.3.1.2), p. 693. The canonical map extends to the completed
projective tensor of the dual and the target Banach space. -/
def completedProjectiveTensorToOperators :
    Completion (ProjectiveTensor (StrongDual ℂ E) F) →L[ℂ] (E →L[ℂ] F) :=
  (show ProjectiveTensor (StrongDual ℂ E) F →L[ℂ] (E →L[ℂ] F) from
    ⟨tensorToFiniteRank, continuous_tensorToFiniteRank_opNorm⟩).fromCompletion

/-- Paper: (C.3.1.2), p. 693. On the image of an algebraic tensor the extended
map agrees with the original finite-rank map. -/
theorem completedProjectiveTensorToOperators_coe (z : ProjectiveTensor (StrongDual ℂ E) F) :
    completedProjectiveTensorToOperators z = tensorToFiniteRank z := by sorry

/-- Paper: §C.3.1, p. 693. Nuclear operators between Banach spaces are the
image of the completed projective tensor. -/
theorem isBanachNuclear_iff_mem_range (A : E →L[ℂ] F) :
    IsBanachNuclear A ↔ A ∈ range completedProjectiveTensorToOperators := by sorry

/-- Paper: §C.3.1, p. 694. The local and Banach-space definitions of a
nuclear operator agree for Banach spaces. -/
theorem isNuclearOperator_iff_isBanachNuclear (A : E →L[ℂ] F) :
    IsNuclearOperator A ↔ IsBanachNuclear A := by sorry

end BanachTensor

section NuclearTrace

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

local notation "ApproxProp" X => DenseRange (tensorToFiniteRank (E := X) (F := X) :
  StrongDual ℂ X ⊗[ℂ] X → PrecompactConvergenceCLM X X)

/-- Paper: Proposition C.3.2.1, p. 694. On a space with the approximation property,
every presentation of the same nuclear endomorphism gives an absolutely convergent
scalar series with the same sum. -/
theorem exists_nuclearTrace_hasSum (hE : ApproxProp E) (A : E →L[ℂ] E)
    (hA : IsNuclearOperator A) :
    ∃! z : ℂ, ∀ r : NuclearPresentation A,
      Summable (fun n ↦ ‖r.coeff n * r.functional n (r.vector n)‖) ∧
      HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n)) z := by sorry

/-- Paper: (C.3.2.2), p. 694. The nuclear trace is the sum of the scalar series
from any nuclear presentation on a space with the approximation property. -/
def nuclearTrace (hE : ApproxProp E) (A : E →L[ℂ] E) (hA : IsNuclearOperator A) : ℂ :=
  (exists_nuclearTrace_hasSum hE A hA).exists.choose

/-- Paper: (C.3.2.2), p. 694. The trace of a rank-one operator is the value
of its functional at its spanning vector.
Deviation: This is a check of the trace formula on one term. -/
theorem nuclearTrace_smulRight (hE : ApproxProp E) (φ : E →L[ℂ] ℂ) (y : E) :
    nuclearTrace hE (φ.smulRight y) (isNuclearOperator_smulRight φ y) = φ y := by sorry

/-- Paper: Proposition C.3.2.1, p. 694. Nuclearity is preserved by
conjugation by a continuous linear automorphism. -/
theorem isNuclearOperator_conj (A : E →L[ℂ] E) (hA : IsNuclearOperator A) (T : E ≃L[ℂ] E) :
    IsNuclearOperator (T.symm.toContinuousLinearMap.comp (A.comp T.toContinuousLinearMap)) := by sorry

/-- Paper: Proposition C.3.2.1, p. 694. The nuclear trace is invariant
under conjugation by a continuous linear automorphism. -/
theorem nuclearTrace_conj (hE : ApproxProp E) (A : E →L[ℂ] E) (hA : IsNuclearOperator A)
    (T : E ≃L[ℂ] E) :
    nuclearTrace hE A hA =
      nuclearTrace hE _ (isNuclearOperator_conj A hA T) := by sorry

/-- Paper: Lemma C.3.2.2, p. 695. Both compositions of a nuclear map and
a continuous linear injection in the opposite direction are nuclear.
Deviation: The right-hand composition's nuclearity is made explicit to type its trace.
The two approximation-property hypotheses are needed for the trace assertion. -/
theorem isNuclearOperator_factor_comps (T : E →L[ℂ] F) (hT : Injective T)
    (A₀ : F →L[ℂ] E) (hA₀ : IsNuclearOperator A₀) :
    IsNuclearOperator (A₀.comp T) ∧ IsNuclearOperator (T.comp A₀) := by sorry

/-- Paper: Lemma C.3.2.2, p. 695. A nuclear map followed by an injection has
the same trace as the reverse composition when both spaces have the approximation property.
Deviation: The given endomorphism is written as its factorization. -/
theorem nuclearTrace_factor_comps (hE : ApproxProp E) (hF : ApproxProp F)
    (T : E →L[ℂ] F) (hT : Injective T) (A₀ : F →L[ℂ] E) (hA₀ : IsNuclearOperator A₀) :
    nuclearTrace hE (A₀.comp T) (isNuclearOperator_factor_comps T hT A₀ hA₀).1 =
      nuclearTrace hF (T.comp A₀) (isNuclearOperator_factor_comps T hT A₀ hA₀).2 := by sorry

end NuclearTrace

section HilbertOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Lemma C.3.3.1(1), p. 697. Every subset bounded in the strong operator
topology on a separable Hilbert space is metrizable with its subspace topology. -/
theorem metrizableSpace_bounded_pointwiseOperators [SeparableSpace H]
    (S : Set (H →Lₚₜ[ℂ] H)) (hS : IsVonNBounded ℂ S) : MetrizableSpace S := by sorry

-- Lemma C.3.3.1(2): Hausdorffness is Mathlib's PointwiseConvergenceCLM instance.
-- Local convexity and quasi-completeness are already stated in Sec2a as
-- pointwiseConvergenceCLM_withSeminorms and hilbert_pointwiseOperators_quasiComplete.

/-- Paper: §C.3.4, p. 697. Hilbert spaces have the approximation property. -/
theorem hilbert_approximationProperty :
    DenseRange (tensorToFiniteRank (E := H) (F := H) :
      StrongDual ℂ H ⊗[ℂ] H → PrecompactConvergenceCLM H H) := by sorry

/-- Paper: Lemma C.3.4.1(1), p. 697. The diagonal of a nuclear endomorphism
is absolutely summable in any Hilbert basis, including an uncountable basis.
Deviation: Mathlib's inner product is linear in the second argument. -/
theorem summable_norm_hilbertDiagonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    Summable (fun i ↦ ‖⟪b i, T (b i)⟫_ℂ‖) := by sorry

-- TODO(paper-gap): Lemma C.3.4.1(2) is false. For diag(1, -1) on ℂ², the sum
-- of absolute diagonal entries is 2 in the coordinate basis and 0 in the
-- orthonormal basis formed by the normalized sum and difference of its vectors.

/-- Paper: Lemma C.3.4.1(3), p. 697. The sum of the diagonal entries of a
nuclear endomorphism is independent of the Hilbert basis.
Deviation: Mathlib's inner product is linear in the second argument. -/
theorem tsum_hilbertDiagonal_eq {ι κ : Type*} (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' j, ⟪c j, T (c j)⟫_ℂ := by sorry

/-- Paper: Lemma C.3.4.4(1), p. 698. The nuclear endomorphisms of a Hilbert space
contain zero and are closed under addition and complex scalar multiplication. -/
theorem nuclearEndomorphisms_submodule_axioms :
    IsNuclearOperator (0 : H →L[ℂ] H) ∧
      (∀ {A B : H →L[ℂ] H}, IsNuclearOperator A → IsNuclearOperator B → IsNuclearOperator (A + B)) ∧
      (∀ (c : ℂ) {A : H →L[ℂ] H}, IsNuclearOperator A → IsNuclearOperator (c • A)) := by sorry

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
    φ.smulRight y ∈ nuclearEndomorphisms H := by sorry

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
    hilbertTrace ⟨φ.smulRight y, smulRight_mem_nuclearEndomorphisms φ y⟩ = φ y := by sorry

/-- Paper: Definition C.3.4.2(1), p. 697. The Hilbert-space trace is the
nuclear trace from Proposition C.3.2.1 on the same endomorphism. -/
theorem hilbertTrace_eq_nuclearTrace (T : nuclearEndomorphisms H) :
    hilbertTrace T = nuclearTrace hilbert_approximationProperty T.val T.property := by sorry

/-- Paper: Definition C.3.4.2(2), p. 697. The trace norm of a nuclear operator
sums the real diagonal entries of the positive square root of its adjoint
times itself, using a choice of Hilbert basis. -/
def traceNorm (T : nuclearEndomorphisms H) : ℝ :=
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  ∑' i, (⟪b i, CFC.sqrt (T.val.adjoint * T.val) (b i)⟫_ℂ).re

/-- Paper: Definition C.3.4.2(2), p. 697. The trace norm is the sum of the
diagonal series for the positive square root in every Hilbert basis. -/
theorem hasSum_traceNorm_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : nuclearEndomorphisms H) :
    HasSum (fun i ↦ (⟪b i, CFC.sqrt (T.val.adjoint * T.val) (b i)⟫_ℂ).re) (traceNorm T) := by sorry

/-- Paper: Definition C.3.4.2(2), p. 697. Nuclearity is equivalent to finiteness
of the positive-square-root diagonal sum in any given Hilbert basis. -/
theorem isNuclearOperator_iff_summable_traceNorm_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) :
    IsNuclearOperator T ↔
      Summable (fun i ↦ (⟪b i, CFC.sqrt (T.adjoint * T) (b i)⟫_ℂ).re) := by sorry

/-- Paper: Definition C.3.4.2(2), p. 697. A rank-one map has trace norm equal
to the product of the functional and vector norms.
Deviation: This is a check of the square root and trace norm normalization. -/
theorem traceNorm_smulRight (φ : H →L[ℂ] ℂ) (y : H) :
    traceNorm ⟨φ.smulRight y, smulRight_mem_nuclearEndomorphisms φ y⟩ = ‖φ‖ * ‖y‖ := by sorry

/-- Paper: Lemma C.3.4.3, p. 698. Composing a strongly convergent sequence of
endomorphisms on the right by a fixed compact operator gives convergence
in operator norm. -/
theorem tendsto_compact_comp_of_pointwise {A Q : H →L[ℂ] H} {Qm : ℕ → H →L[ℂ] H}
    (hA : IsCompactOperator A) (hQ : ∀ x, Tendsto (fun m ↦ Qm m x) atTop (𝓝 (Q x))) :
    Tendsto (fun m ↦ (Qm m).comp A) atTop (𝓝 (Q.comp A)) := by sorry

/-- Paper: Lemma C.3.4.4(1), p. 698. Left multiplication by a bounded operator
preserves nuclearity. -/
theorem mul_mem_nuclearEndomorphisms_left (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    A * T.val ∈ nuclearEndomorphisms H := by sorry

/-- Paper: Lemma C.3.4.4(1), p. 698. Right multiplication by a bounded operator
preserves nuclearity. -/
theorem mul_mem_nuclearEndomorphisms_right (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    T.val * A ∈ nuclearEndomorphisms H := by sorry

/-- Paper: Lemma C.3.4.4(1), p. 698. The trace norm satisfies the normed-space
axioms on the complex vector space of nuclear endomorphisms. -/
theorem traceNorm_normedSpaceCore :
    letI : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    NormedSpace.Core ℂ (nuclearEndomorphisms H) := by sorry

-- TODO(paper-gap): The equality in (C.3.4.3) is false. For A = diag(1, 0) and
-- T swapping the first coordinate into the second and killing the second, AT = 0
-- while TA = T has trace norm 1. The two separate upper bounds hold.

/-- Paper: Lemma C.3.4.4(2), p. 698. The trace norm of a left product is at
most the operator norm of the left factor times the trace norm of the right factor.
Deviation: The invalid equality in (C.3.4.3) is recorded above. -/
theorem traceNorm_mul_left_le (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    traceNorm ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩ ≤ ‖A‖ * traceNorm T := by sorry

/-- Paper: Lemma C.3.4.4(2), p. 698. The trace norm of a right product is at
most the operator norm of the right factor times the trace norm of the left factor.
Deviation: The invalid equality in (C.3.4.3) is recorded above. -/
theorem traceNorm_mul_right_le (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    traceNorm ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩ ≤ ‖A‖ * traceNorm T := by sorry

/-- Paper: Lemma C.3.4.4(3), p. 698. The trace is complex linear. -/
theorem hilbertTrace_linear :
    ∃ f : nuclearEndomorphisms H →ₗ[ℂ] ℂ, ∀ T, f T = hilbertTrace T := by sorry

/-- Paper: Lemma C.3.4.4(3), p. 698. The modulus of the trace is bounded by
the trace norm, which gives continuity for the trace norm. -/
theorem norm_hilbertTrace_le (T : nuclearEndomorphisms H) :
    ‖hilbertTrace T‖ ≤ traceNorm T := by sorry

/-- Paper: Lemma C.3.4.4(4), p. 698. The canonical image of the algebraic tensor
of the dual and the Hilbert space consists of nuclear operators. -/
theorem tensorToFiniteRank_mem_nuclearEndomorphisms (z : StrongDual ℂ H ⊗[ℂ] H) :
    tensorToFiniteRank z ∈ nuclearEndomorphisms H := by sorry

/-- Paper: Lemma C.3.4.4(4), p. 698. Finite-rank operators from the canonical
tensor map approximate every nuclear endomorphism in trace norm. -/
theorem exists_tensorToFiniteRank_traceNorm_sub_lt (T : nuclearEndomorphisms H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : StrongDual ℂ H ⊗[ℂ] H,
      traceNorm (T - ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩) < ε :=
  by sorry

/-- Paper: Lemma C.3.4.4(4), p. 698. On a separable Hilbert space there is a
countable trace-norm dense set of nuclear endomorphisms.
Deviation: Density is expressed by approximation in every positive trace-norm radius. -/
theorem exists_countable_traceNorm_dense [SeparableSpace H] :
    ∃ S : Set (nuclearEndomorphisms H), S.Countable ∧
      ∀ (T : nuclearEndomorphisms H) (ε : ℝ), 0 < ε → ∃ A ∈ S, traceNorm (T - A) < ε := by sorry

-- TODO(paper-gap): The proof on p. 699 sums distinct eigenvalues to compute the
-- trace norm. Multiplicities are required, as shown by the identity on ℂ².

/-- Paper: Lemma C.3.4.4(5), p. 698. The products of a strongly null net and
a fixed finite-rank right factor are nuclear and tend to zero in trace norm.
Deviation: A net is indexed by a nonempty directed preorder. -/
theorem tendsto_traceNorm_mul_finiteRank {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] (P : ι → H →L[ℂ] H) (hP : ∀ x, Tendsto (fun i ↦ P i x) atTop (𝓝 0))
    (F : H →L[ℂ] H) (hF : FiniteDimensional ℂ F.toLinearMap.range) :
    ∃ hm : ∀ i, P i * F ∈ nuclearEndomorphisms H,
      Tendsto (fun i ↦ traceNorm ⟨P i * F, hm i⟩) atTop (𝓝 0) := by sorry

end HilbertOperators

end RiemannMasullo
