module

public import RiemannMasullo.AppC_LCTVS.Sec2b
import all RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.AppC_LCTVS.Sec2a_part2
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion

/-! # Bounded subsets of completed locally convex tensor products -/

public section

open Set Filter Topology TopologicalSpace Bornology UniformSpace TensorProduct
open scoped TensorProduct

namespace RiemannMasullo

/-- A countable strict locally convex union need not have complete stages. In its
completion, every bounded set is the image of a bounded set of one completed stage. -/
lemma IsInjectiveLCLimit.completion_bounded_stage
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, UniformSpace (X n)] [∀ n, IsUniformAddGroup (X n)] [∀ n, PolynormableSpace ℂ (X n)]
    [UniformContinuousConstSMul ℂ E] [∀ n, UniformContinuousConstSMul ℂ (X n)]
    {j : ∀ n, X n →L[ℂ] X (n+1)} {i : ∀ n, X n →L[ℂ] E}
    (h : IsInjectiveLCLimit j i) (hi : ∀ n, IsEmbedding (i n))
    (B : Set (Completion E)) (hB : IsVonNBounded ℂ B) :
    ∃ n, ∃ A : Set (Completion (X n)), IsVonNBounded ℂ A ∧ (i n).completion '' A = B := by
  classical
  let Z (n : ℕ) := Completion (X n)
  let J (n : ℕ) : Z n →L[ℂ] Z (n+1) := (j n).completion
  let I (n : ℕ) : Z n →L[ℂ] Completion E := (i n).completion
  have hcomp (n : ℕ) : I (n+1) ∘ J n = I n := by
    refine Completion.ext ((I _).continuous.comp (J _).continuous) (I _).continuous fun z ↦ ?_
    change (i (n+1)).completion ((j n).completion ↑z) = (i n).completion ↑z
    rw [(j n).completion_apply_coe, (i (n+1)).completion_apply_coe, (i n).completion_apply_coe]
    exact congrArg (Completion.coe' (α := E)) (DFunLike.congr_fun (h.compatible n) z)
  have hI (n : ℕ) : IsUniformEmbedding (I n) :=
    (Completion.isUniformInducing_extension ((Completion.isUniformInducing_coe E).comp
      (AddMonoidHom.isUniformInducing_of_isInducing (hi n).isInducing))).isUniformEmbedding
  have hJ (n : ℕ) : IsClosedEmbedding (J n) := by
    apply IsClosedEmbedding.of_comp (hI (n+1)).isEmbedding
    rw [hcomp]; exact (hI n).isClosedEmbedding
  let S (n : ℕ) := (I n).toLinearMap.range
  have hmono : Monotone S := monotone_nat_of_le_succ fun n ↦ by
    rintro _ ⟨z, rfl⟩
    exact ⟨J n z, congrFun (hcomp n) z⟩
  let W : Submodule ℂ (Completion E) := ⨆ n, S n
  let u (n : ℕ) : Z n →ₗ[ℂ] W := (I n).toLinearMap.codRestrict W
    (fun z ↦ le_iSup S n (show I n z ∈ S n from ⟨z, rfl⟩))
  let c := (Completion.toComplL : E →L[ℂ] Completion E)
  let d : E →ₗ[ℂ] W := c.toLinearMap.codRestrict W fun x ↦ by
    obtain ⟨n, z, rfl⟩ := h.exhaustive x
    exact le_iSup S n ⟨(z : Z n), (i n).completion_apply_coe z⟩
  -- Use the final topology here, not the a priori subspace topology from the completion.
  let : TopologicalSpace W := locallyConvexFinalTopology u
  have hW := finalTopology_withSeminorms u
  let : IsTopologicalAddGroup W := hW.isTopologicalAddGroup
  let : PolynormableSpace ℂ W := hW.toPolynormableSpace
  let : UniformSpace W := IsTopologicalAddGroup.rightUniformSpace W
  let : IsUniformAddGroup W := isUniformAddGroup_of_addCommGroup
  let : ∀ n, PolynormableSpace ℂ (Z n) := fun _ ↦ polynormableSpace_completion
  let : PolynormableSpace ℂ (Completion E) := polynormableSpace_completion
  let U (n : ℕ) : Z n →L[ℂ] W := ⟨u n, continuous_finalTopology_stage u n⟩
  let v : W →L[ℂ] Completion E := ⟨W.subtype, continuous_finalTopology_lift u W.subtype
    (fun n ↦ (I n).continuous)⟩
  let : T2Space W := T2Space.of_injective_continuous Subtype.val_injective v.continuous
  have hlim : IsInjectiveLCLimit J U := by
    refine ⟨fun n _ _ he ↦ (hI n).injective (congrArg v he), ?_, ?_, rfl⟩
    · intro n
      apply ContinuousLinearMap.ext
      intro z
      exact Subtype.ext (congrFun (hcomp n) z)
    · intro z
      obtain ⟨n, a, ha⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp z.property
      exact ⟨n, a, Subtype.ext ha⟩
  have hcomplete (n : ℕ) : @CompleteSpace (Z n) (IsTopologicalAddGroup.rightUniformSpace (Z n)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]; infer_instance
  let : CompleteSpace W := (strictLCLimit_complete_nonmetrizable hcomplete hlim
    (fun n ↦ (hJ n).isEmbedding)).1
  have hd : Continuous d := by
    have hd' (n : ℕ) : Continuous (d ∘ i n) := by
      have he : d ∘ i n = U n ∘ Completion.coe' := funext fun z ↦
        Subtype.ext ((i n).completion_apply_coe z).symm
      rw [he]; exact (U n).continuous.comp (Completion.continuous_coe _)
    have hsem : WithSeminorms
        (Subtype.val : {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ i n)} → _) := ⟨h.topology_eq⟩
    exact hW.continuous_of_continuous_comp d fun p ↦
      hsem.continuous_seminorm ⟨p.val.comp d, fun n ↦ (hW.continuous_seminorm p).comp (hd' n)⟩
  let D : E →L[ℂ] W := ⟨d, hd⟩
  let : UniformContinuousConstSMul ℂ W := uniformContinuousConstSMul_of_continuousConstSMul ℂ W
  have hvD : v ∘ D.fromCompletion = id := by
    apply Completion.ext (v.continuous.comp D.fromCompletion.continuous) continuous_id
    intro x
    simp only [Function.comp_apply, ContinuousLinearMap.fromCompletion_apply_coe]; rfl
  obtain ⟨n, A, hA, he⟩ := (isVonNBounded_iff_bounded_stage hlim hJ _).mp
    (hB.image D.fromCompletion)
  refine ⟨n, A, hA, ?_⟩
  calc
    (i n).completion '' A = v '' (U n '' A) := (Set.image_image v (U n) A).symm
    _ = B := by rw [he, ← Set.image_comp, hvD, Set.image_id]

/-- Nuclearity compares the two tensor topologies also for factors in different
carrier universes: lift the test space and retract along its linear homeomorphism. -/
lemma IsNuclearTVS.tensorComparison.{u, v} {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y] (hX : IsNuclearTVS.{v} X) :
    @IsHomeomorph (ProjectiveTensor X Y) (InjectiveTensor X Y) _ _ id := by
  let := hX.1
  let := hX.2.1
  let L := ULift.{u} Y
  let e : L ≃L[ℂ] Y := ContinuousLinearEquiv.ulift
  have : PolynormableSpace ℂ L := e.toHomeomorph.isInducing.polynormableSpace
    (f := e.toLinearEquiv.toLinearMap)
  have h := hX.2.2 L inferInstance inferInstance inferInstance inferInstance inferInstance
  have hc : @Continuous (InjectiveTensor X L) (ProjectiveTensor X L) _ _ id :=
    h.isInducing.continuous_iff.mpr (@continuous_id (InjectiveTensor X L) _)
  let one := ContinuousLinearMap.id ℂ X
  have hback : @Continuous (InjectiveTensor X Y) (ProjectiveTensor X Y) _ _ id := by
    refine (((projectiveTensorMap_continuous one e.toContinuousLinearMap).comp hc).comp
      (injectiveTensorMap_continuous one e.symm.toContinuousLinearMap)).congr fun z ↦ ?_
    change X ⊗[ℂ] Y at z
    change (TensorProduct.map LinearMap.id e.toLinearMap)
      ((TensorProduct.map LinearMap.id e.symm.toLinearMap) z) = z
    rw [TensorProduct.map_map, LinearMap.id_comp, show e.toLinearMap.comp e.symm.toLinearMap =
      LinearMap.id from LinearMap.ext e.apply_symm_apply, TensorProduct.map_id]
    rfl
  exact (⟨Equiv.refl (X ⊗[ℂ] Y), continuous_projectiveTensor_to_injectiveTensor X Y, hback⟩ :
    ProjectiveTensor X Y ≃ₜ InjectiveTensor X Y).isHomeomorph

/-- A nuclear right factor also identifies the projective and injective tensor topologies. -/
lemma IsNuclearTVS.tensorComparison_right.{u, v} {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (hY : IsNuclearTVS.{u} Y) :
    @IsHomeomorph (ProjectiveTensor X Y) (InjectiveTensor X Y) _ _ id := by
  let := hY.1
  let := hY.2.1
  have hc : @Continuous (InjectiveTensor Y X) (ProjectiveTensor Y X) _ _ id :=
    hY.tensorComparison.isInducing.continuous_iff.mpr (@continuous_id (InjectiveTensor Y X) _)
  let S : ProjectiveTensor Y X →ₗ[ℂ] ProjectiveTensor X Y := (TensorProduct.comm ℂ Y X).toLinearMap
  have hpoly : PolynormableSpace ℂ (ProjectiveTensor X Y) :=
    (projectiveTensor_withSeminorms X Y).toPolynormableSpace
  have hswap : @Continuous (ProjectiveTensor Y X) (ProjectiveTensor X Y) _ _
      (TensorProduct.comm ℂ Y X) := by
    change Continuous S
    apply (continuous_projectiveTensor_iff (E := Y) (F := X) (G := ProjectiveTensor X Y) S).mpr
    exact (continuous_projectiveTensor_tmul (E := X) (F := Y)).comp continuous_swap
  have hback : @Continuous (InjectiveTensor X Y) (ProjectiveTensor X Y) _ _ id :=
    (hswap.comp (hc.comp (continuous_injectiveTensor_comm X Y))).congr fun z ↦
      (TensorProduct.comm ℂ X Y).symm_apply_apply z
  exact (⟨Equiv.refl (X ⊗[ℂ] Y), continuous_projectiveTensor_to_injectiveTensor X Y, hback⟩ :
    ProjectiveTensor X Y ≃ₜ InjectiveTensor X Y).isHomeomorph

private theorem norm_le_seminorm_of_ball_subset {X : Type*} [AddCommGroup X] [Module ℂ X]
    (q : Seminorm ℂ X) (L : X →ₗ[ℂ] ℂ) {r : ℝ} (hr : 0 < r)
    (h : ∀ x, q x < r → ‖L x‖ ≤ 1) (x : X) :
    ‖L x‖ ≤ q x / r := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let v := q x / r + ε
  have hv : 0 < v := add_pos_of_nonneg_of_pos (div_nonneg (apply_nonneg q x) hr.le) hε
  let c : ℂ := (v⁻¹ : ℝ)
  have hcn : ‖c‖ = v⁻¹ := Complex.norm_of_nonneg (inv_nonneg.mpr hv.le)
  have hq : q (c • x) < r := by
    rw [map_smul_eq_mul, hcn, inv_mul_eq_div, div_lt_iff₀ hv]
    dsimp only [v]
    rw [mul_add, mul_div_cancel₀ _ hr.ne']
    exact lt_add_of_pos_right _ (mul_pos hr hε)
  have hx := h _ hq
  rw [map_smul, norm_smul, hcn, inv_mul_eq_div, div_le_iff₀ hv, one_mul] at hx
  exact hx

private theorem tensorDualForm_commute {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    (u : StrongDual ℂ E) (v : StrongDual ℂ F) (z : E ⊗[ℂ] F) :
    tensorDualForm u v z = tensorDualForm v u (TensorProduct.comm ℂ E F z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rw [TensorProduct.comm_tmul, tensorDualForm_tmul, tensorDualForm_tmul, mul_comm]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The injective topology uses only the evaluations that represent the
generating seminorms of both factors. -/
theorem injectiveTensor_isEmbedding_of_generating_evaluations {E F H I J : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    {p : SeminormFamily ℂ E I} {q : SeminormFamily ℂ F J}
    (hp : WithSeminorms p) (hq : WithSeminorms q)
    {A : I → Type*} {B : J → Type*}
    (a : ∀ i, A i → StrongDual ℂ E) (b : ∀ j, B j → StrongDual ℂ F)
    (ha : ∀ i x {M : ℝ}, 0 ≤ M → (∀ s, ‖a i s x‖ ≤ M) → p i x ≤ M)
    (hb : ∀ j y {M : ℝ}, 0 ≤ M → (∀ t, ‖b j t y‖ ≤ M) → q j y ≤ M)
    (φ : InjectiveTensor E F →ₗ[ℂ] H) (hφ : Continuous φ)
    (hbound : ∀ i j, ∃ r : Seminorm ℂ H, Continuous r ∧ ∀ s t z,
      ‖tensorDualForm (a i s) (b j t) z‖ ≤ r (φ z)) :
    IsEmbedding φ := by
  classical
  choose r hr hrt using hbound
  let T := InjectiveTensor E F
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  have : T2Space T := injectiveTensor_t2
  have : IsTopologicalAddGroup T := inferInstance
  have hi : IsInducing φ := by
    apply (IsTopologicalAddGroup.isInducing_iff_nhds_zero (f := φ)).mpr
    refine le_antisymm (hφ.continuousAt.tendsto.mono_right ?_ |> tendsto_iff_comap.mp) ?_
    · rw [map_zero]
    let pn (UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0}) :
        Seminorm ℂ T := injectiveTensorSeminorm UV.1 UV.2
    rw [((SeminormFamily.withSeminorms_iff_nhds_eq_iInf pn).mp (withGeneratingSeminorms_spec _ _))]
    refine le_iInf fun ⟨U, V⟩ ↦ ?_
    refine ((Metric.nhds_basis_ball (x := (0 : ℝ))).comap (pn (U, V))).ge_iff.mpr fun ε hε ↦ ?_
    obtain ⟨⟨s, ρ⟩, hρ, hs⟩ := hp.hasBasis_zero_ball.mem_iff.mp U.property
    obtain ⟨⟨t, σ⟩, hσ, ht⟩ := hq.hasBasis_zero_ball.mem_iff.mp V.property
    let R : Seminorm ℂ H := (s ×ˢ t).sup (fun ij ↦ r ij.1 ij.2)
    have hR : Continuous R := by
      exact Seminorm.continuous_finsetSup fun ij _ ↦ hr ij.1 ij.2
    have hN := R.ball_mem_nhds hR (show 0 < ε * ρ * σ by positivity)
    refine Filter.mem_of_superset (Filter.preimage_mem_comap hN) fun z hz ↦ ?_
    have hzR : R (φ z) < ε * ρ * σ := R.mem_ball_zero.mp hz
    have hM : 0 ≤ R (φ z) := apply_nonneg _ _
    change E ⊗[ℂ] F at z
    change injectiveTensorSeminorm U V z ∈ Metric.ball 0 ε
    rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (apply_nonneg (injectiveTensorSeminorm U V) z)]
    suffices hh : injectiveTensorSeminorm U V z ≤ R (φ z) / ρ / σ by
      apply hh.trans_lt
      exact (div_lt_iff₀ hσ).mpr ((div_lt_iff₀ hρ).mpr (by simpa [mul_right_comm] using hzR))
    rw [injectiveTensorSeminorm_apply]
    let : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    let : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    apply ciSup_le
    intro L
    apply ciSup_le
    intro M
    have hL (x : E) : ‖L.val x‖ ≤ (s.sup p) x / ρ :=
      norm_le_seminorm_of_ball_subset _ L.val.toLinearMap hρ
        (fun x hx ↦ L.property x (hs ((s.sup p).mem_ball_zero.mpr hx))) x
    have hM' (y : F) : ‖M.val y‖ ≤ (t.sup q) y / σ :=
      norm_le_seminorm_of_ball_subset _ M.val.toLinearMap hσ
        (fun y hy ↦ M.property y (ht ((t.sup q).mem_ball_zero.mpr hy))) y
    have hEval (i) (hi : i ∈ s) (j) (hj : j ∈ t) (u : A i) (v : B j) :
        ‖tensorDualForm (a i u) (b j v) z‖ ≤ R (φ z) :=
      (hrt i j u v z).trans (Seminorm.le_finset_sup_apply (p := fun ij : I × J ↦ r ij.1 ij.2)
        (x := φ z) (i := (i, j)) (Finset.mem_product.mpr ⟨hi, hj⟩))
    rw [← tensorDualOperator_eval]
    refine (hM' _).trans (div_le_div_of_nonneg_right ?_ hσ.le)
    apply Seminorm.finset_sup_apply_le
    · positivity
    · intro j hj
      refine hb j _ (by positivity) fun v ↦ ?_
      rw [tensorDualOperator_eval, tensorDualForm_commute, ← tensorDualOperator_eval]
      refine (hL _).trans (div_le_div_of_nonneg_right ?_ hρ.le)
      apply Seminorm.finset_sup_apply_le hM
      intro i hi
      refine ha i _ hM fun u ↦ ?_
      rw [tensorDualOperator_eval, ← tensorDualForm_commute]
      exact hEval i hi j hj u v
  exact ⟨hi, hi.injective⟩

/-- When both projective tensor topologies agree with the injective ones,
tensoring a pair of embeddings remains an embedding. -/
theorem projectiveTensorMap_isEmbedding_of_comparisons {E F G H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] [T2Space G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [PolynormableSpace ℂ H] [T2Space H]
    (f : E →L[ℂ] G) (g : F →L[ℂ] H) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (h₁ : @IsHomeomorph (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id)
    (h₂ : @IsHomeomorph (ProjectiveTensor G H) (InjectiveTensor G H) _ _ id) :
    IsEmbedding (projectiveTensorMap f.toLinearMap g.toLinearMap) := by
  have h := h₂.homeomorph.symm.isEmbedding.comp
    ((injectiveTensorMap_isEmbedding f g hf hg).comp h₁.isEmbedding)
  have he : (h₂.homeomorph.symm ∘ injectiveTensorMap f.toLinearMap g.toLinearMap ∘ id :
      ProjectiveTensor E F → ProjectiveTensor G H) = projectiveTensorMap f.toLinearMap g.toLinearMap :=
    funext fun z ↦ h₂.homeomorph.symm_apply_apply (projectiveTensorMap f.toLinearMap g.toLinearMap z)
  rw [← he]
  exact h

section Stages

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [PolynormableSpace ℂ F] [T2Space F]
  {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
  {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]

/-- Fréchet stage maps induce continuous maps from the projective stage tensor to the
inductive tensor of the ambient spaces. -/
lemma continuous_projectiveStage_inductiveTensor (f : X →L[ℂ] E) (g : Y →L[ℂ] F)
    (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y) :
    Continuous (show ProjectiveTensor X Y → InductiveTensor E F from TensorProduct.map f.toLinearMap g.toLinearMap) := by
  have h : @Continuous (ProjectiveTensor X Y) (InductiveTensor X Y) _ _ id :=
    (inductiveTensor_to_projectiveTensor_of_frechet hX hY).isInducing.continuous_iff.mpr
      (@continuous_id (ProjectiveTensor X Y) _)
  exact (inductiveTensorMap_continuous f g).comp h

/-- For nuclear Fréchet stages, the injective tensor embedding detects the original
stage topology even in the finer inductive tensor of the ambient spaces. -/
lemma isEmbedding_projectiveStage_inductiveTensor (f : X →L[ℂ] E) (g : Y →L[ℂ] F)
    (hf : IsEmbedding f) (hg : IsEmbedding g) (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y)
    (hc : @IsHomeomorph (ProjectiveTensor X Y) (InjectiveTensor X Y) _ _ id) :
    IsEmbedding (show ProjectiveTensor X Y → InductiveTensor E F from TensorProduct.map f.toLinearMap g.toLinearMap) := by
  have h : @Continuous (InductiveTensor E F) (InjectiveTensor E F) _ _ id :=
    (continuous_projectiveTensor_to_injectiveTensor E F).comp continuous_inductiveTensor_to_projectiveTensor
  exact IsEmbedding.of_comp (continuous_projectiveStage_inductiveTensor f g hX hY) h
    ((injectiveTensorMap_isEmbedding f g hf hg).comp hc.isEmbedding)

end Stages

/-- The composite transition to any later stage. -/
private lemma IsInjectiveLCLimit.transition_to {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] {j : ∀ n, X n →L[ℂ] X (n+1)} {i : ∀ n, X n →L[ℂ] E}
    (h : IsInjectiveLCLimit j i) {a b : ℕ} (hab : a ≤ b) :
    ∃ f : X a →L[ℂ] X b, (i b).comp f = i a := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨ContinuousLinearMap.id ℂ _, rfl⟩
  | succ n _ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨(j n).comp f, by rw [← ContinuousLinearMap.comp_assoc, h.compatible, hf]⟩

section Diagonal

universe u v

variable {E : Type*} {F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  {X : ℕ → Type u} {Y : ℕ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]
  {j : ∀ n, X n →L[ℂ] X (n+1)} {i : ∀ n, X n →L[ℂ] E}
  {k : ∀ n, Y n →L[ℂ] Y (n+1)} {l : ∀ n, Y n →L[ℂ] F}

/-- The inductive tensor of two countable locally convex limits of Fréchet stages
has the final locally convex topology of the diagonal projective tensor stages. -/
lemma inductiveTensor_topology_eq_diagonal_projective [PolynormableSpace ℂ E] [T2Space E]
    [PolynormableSpace ℂ F] [T2Space F] (h : IsInjectiveLCLimit j i) (h' : IsInjectiveLCLimit k l)
    (hX : ∀ n, IsFrechetTVS (X n)) (hY : ∀ n, IsFrechetTVS (Y n)) :
    (inferInstance : TopologicalSpace (InductiveTensor E F)) = locallyConvexFinalTopology
      (fun n ↦ (show ProjectiveTensor (X n) (Y n) →ₗ[ℂ] InductiveTensor E F from
        TensorProduct.map (i n).toLinearMap (l n).toLinearMap)) := by
  let : ∀ n, MetrizableSpace (X n) := fun n ↦ (hX n).choose_spec.2.1
  let : ∀ n, MetrizableSpace (Y n) := fun n ↦ (hY n).choose_spec.2.1
  let : ∀ n, PolynormableSpace ℂ (X n) := fun n ↦ (hX n).choose_spec.1
  let : ∀ n, PolynormableSpace ℂ (Y n) := fun n ↦ (hY n).choose_spec.1
  let T := InductiveTensor E F
  let stage (n : ℕ) : ProjectiveTensor (X n) (Y n) →ₗ[ℂ] T :=
    TensorProduct.map (i n).toLinearMap (l n).toLinearMap
  let gen (p : Seminorm ℂ T) := (∀ x : E, Continuous (fun y : F ↦ p (x ⊗ₜ[ℂ] y))) ∧
    (∀ y : F, Continuous (fun x : E ↦ p (x ⊗ₜ[ℂ] y)))
  suffices heq : gen = fun p : Seminorm ℂ T ↦ ∀ n, Continuous (p ∘ stage n) by
    change (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype gen → _)).topology = _
    rw [heq]; rfl
  funext p
  apply propext
  constructor
  · intro hp n
    have ht : WithSeminorms (E := T) (Subtype.val : Subtype gen → _) := ⟨rfl⟩
    exact (ht.continuous_seminorm ⟨p, hp⟩).comp
      (continuous_projectiveStage_inductiveTensor (i n) (l n) (hX n) (hY n))
  · intro hp
    -- Each rectangle of stages factors through the diagonal stage at its larger index.
    have hpair (a b : ℕ) : Continuous (fun z : X a × Y b ↦ p (i a z.1 ⊗ₜ[ℂ] l b z.2)) := by
      let n := max a b
      obtain ⟨f, hf⟩ := h.transition_to (le_max_left a b)
      obtain ⟨g, hg⟩ := h'.transition_to (le_max_right a b)
      refine ((hp n).comp (continuous_projectiveTensor_tmul.comp
        (f.continuous.prodMap g.continuous))).congr fun z ↦ ?_
      change p (i n (f z.1) ⊗ₜ[ℂ] l n (g z.2)) = _
      rw [show i n (f z.1) = i a z.1 from DFunLike.congr_fun hf _,
        show l n (g z.2) = l b z.2 from DFunLike.congr_fun hg _]
    constructor
    · intro x
      obtain ⟨a, x, rfl⟩ := h.exhaustive x
      have hF : WithSeminorms (Subtype.val : {q : Seminorm ℂ F // ∀ n, Continuous (q ∘ l n)} → _) :=
        ⟨h'.topology_eq⟩
      exact hF.continuous_seminorm ⟨p.comp (TensorProduct.mk ℂ E F (i a x)),
        fun b ↦ (hpair a b).comp (continuous_const.prodMk continuous_id)⟩
    · intro y
      obtain ⟨b, y, rfl⟩ := h'.exhaustive y
      have hE : WithSeminorms (Subtype.val : {q : Seminorm ℂ E // ∀ n, Continuous (q ∘ i n)} → _) :=
        ⟨h.topology_eq⟩
      exact hE.continuous_seminorm ⟨p.comp ((TensorProduct.mk ℂ E F).flip (l b y)),
        fun a ↦ (hpair a b).comp (continuous_id.prodMk continuous_const)⟩

/-- Paper: Proposition C.2.3.13(2), p. 683, together with Proposition C.1.5.3,
p. 664. Every bounded set in the **completed** inductive tensor of two strict countable
limits of nuclear Fréchet stages comes from a bounded set in a single completed
projective tensor stage. Only the first family's stages need be nuclear. -/
lemma completedInductiveTensor_bounded_projectiveStage [PolynormableSpace ℂ E] [T2Space E]
    [PolynormableSpace ℂ F] [T2Space F] (h : IsInjectiveLCLimit j i) (h' : IsInjectiveLCLimit k l)
    (hj : ∀ n, IsEmbedding (j n)) (hk : ∀ n, IsEmbedding (k n))
    (hX : ∀ n, IsFrechetTVS (X n)) (hY : ∀ n, IsFrechetTVS (Y n))
    (hn : ∀ n, IsNuclearTVS.{v} (X n)) {B : Set (Completion (InductiveTensor E F))}
    (hB : IsVonNBounded ℂ B) :
    ∃ n, ∃ A : Set (Completion (ProjectiveTensor (X n) (Y n))), IsVonNBounded ℂ A ∧
      (@Completion.map (ProjectiveTensor (X n) (Y n)) _ (InductiveTensor E F) _
        (TensorProduct.map (i n).toLinearMap (l n).toLinearMap)) '' A = B := by
  let : ∀ n, MetrizableSpace (X n) := fun n ↦ (hX n).choose_spec.2.1
  let : ∀ n, MetrizableSpace (Y n) := fun n ↦ (hY n).choose_spec.2.1
  let : ∀ n, PolynormableSpace ℂ (X n) := fun n ↦ (hX n).choose_spec.1
  let : ∀ n, PolynormableSpace ℂ (Y n) := fun n ↦ (hY n).choose_spec.1
  let : ∀ n, IsTopologicalAddGroup (X n) := fun n ↦ (hX n).choose
  let : ∀ n, IsTopologicalAddGroup (Y n) := fun n ↦ (hY n).choose
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  let Z (n : ℕ) := ProjectiveTensor (X n) (Y n)
  let T := InductiveTensor E F
  let U (n : ℕ) : Z n →L[ℂ] T := ⟨TensorProduct.map (i n).toLinearMap (l n).toLinearMap,
    continuous_projectiveStage_inductiveTensor (i n) (l n) (hX n) (hY n)⟩
  let J (n : ℕ) : Z n →L[ℂ] Z (n+1) := ⟨projectiveTensorMap (j n).toLinearMap (k n).toLinearMap,
    projectiveTensorMap_continuous (j n) (k n)⟩
  have hU (n : ℕ) : IsEmbedding (U n) := isEmbedding_projectiveStage_inductiveTensor (i n) (l n)
    (h.isEmbedding_stage hj n) (h'.isEmbedding_stage hk n) (hX n) (hY n) (hn n).tensorComparison
  have hc (n : ℕ) : (U (n+1)).comp (J n) = U n := by
    apply ContinuousLinearMap.coe_injective
    apply TensorProduct.ext'
    intro x y
    change i (n+1) (j n x) ⊗ₜ[ℂ] l (n+1) (k n y) = i n x ⊗ₜ[ℂ] l n y
    rw [show i (n+1) (j n x) = i n x from DFunLike.congr_fun (h.compatible n) x,
      show l (n+1) (k n y) = l n y from DFunLike.congr_fun (h'.compatible n) y]
  let S (n : ℕ) := (U n).toLinearMap.range
  have hmono : Monotone S := monotone_nat_of_le_succ fun n ↦ by
    rintro _ ⟨z, rfl⟩
    exact ⟨J n z, DFunLike.congr_fun (hc n) z⟩
  have hex (z : E ⊗[ℂ] F) : ∃ n, z ∈ S n := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨a, x, rfl⟩ := h.exhaustive x
      obtain ⟨b, y, rfl⟩ := h'.exhaustive y
      obtain ⟨f, hf⟩ := h.transition_to (le_max_left a b)
      obtain ⟨g, hg⟩ := h'.transition_to (le_max_right a b)
      refine ⟨max a b, f x ⊗ₜ[ℂ] g y, ?_⟩
      change i _ (f x) ⊗ₜ[ℂ] l _ (g y) = _
      rw [show i _ (f x) = i a x from DFunLike.congr_fun hf x,
        show l _ (g y) = l b y from DFunLike.congr_fun hg y]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨max a b, (S _).add_mem (hmono (le_max_left a b) ha) (hmono (le_max_right a b) hb)⟩
  have hlim : IsInjectiveLCLimit J U := ⟨fun n ↦ (hU n).injective, hc, hex,
    inductiveTensor_topology_eq_diagonal_projective h h' hX hY⟩
  let : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
  let : ∀ n, UniformContinuousConstSMul ℂ (Z n) := fun n ↦ uniformContinuousConstSMul_of_continuousConstSMul ℂ (Z n)
  exact hlim.completion_bounded_stage hU B hB

end Diagonal

section CompactRectangles
open Filter
open scoped Pointwise ComplexOrder


/-- Approximate points of a compact set by a common finite net from a dense subgroup. -/
private lemma rect_finite_net {T X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {j : T → X} (hj : DenseRange j)
    {K : Set X} (hK : IsCompact K) {D : Set X} (hD : D ∈ 𝓝 0) :
    ∃ a : K → T, (range a).Finite ∧ ∀ z, j (a z) - z.1 ∈ D := by
  let O (t : T) : Set X := {z | j t - z ∈ interior D}
  have hO (t : T) : IsOpen (O t) := isOpen_interior.preimage (continuous_const.sub continuous_id)
  have hcover : K ⊆ ⋃ t, O t := by
    intro z _
    apply mem_iUnion.mpr
    change ∃ t, j t ∈ (fun q : X ↦ q - z) ⁻¹' interior D
    apply hj.mem_nhds (x := z)
    exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by
      simpa only [Pi.sub_apply, id_eq, sub_self] using interior_mem_nhds.mpr hD)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hO hcover
  choose a has ha using fun z : K ↦ mem_iUnion₂.mp (hs z.2)
  exact ⟨a, s.finite_toSet.subset (range_subset_iff.mpr has), fun z ↦ interior_subset (ha z)⟩

/-- Uniform version of the controlled successive approximations in §C.2.3.  At each level
only finitely many approximants are needed for an entire compact set. -/
private lemma rect_controlled_approximation {T : Type*} [AddCommGroup T] [UniformSpace T]
    [IsUniformAddGroup T] {K : Set (Completion T)} (hK : IsCompact K) {W A : ℕ → Set T}
    (hW : (𝓝 0).HasAntitoneBasis W) (hA : ∀ n, A n ∈ 𝓝 0) :
    ∃ a : ℕ → K → T, (∀ n, (range (a n)).Finite) ∧
      (∀ z : K, Tendsto (fun n ↦ Completion.coe' (a n z)) atTop (𝓝 z.1)) ∧
      ∀ n z, a (n + 1) z - a n z ∈ A n := by
  let j : T →+ Completion T := Completion.toCompl
  have hj : IsDenseInducing j := Completion.isDenseInducing_coe
  have hlift (n : ℕ) : ∃ P ∈ 𝓝 (0 : Completion T), j ⁻¹' P ⊆ A n := by
    have h := hA n
    rwa [hj.nhds_eq_comap, map_zero j, mem_comap] at h
  choose P hP hPA using hlift
  have hsmall (n : ℕ) : ∃ D ∈ 𝓝 (0 : Completion T),
      (∀ x ∈ D, ∀ y ∈ D, x - y ∈ P n) ∧ D ⊆ closure (j '' W n) := by
    have hsub : (fun v : Completion T × Completion T ↦ v.1 - v.2) ⁻¹' P n ∈
        𝓝 ((0 : Completion T), 0) :=
      (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds (by simpa using hP n)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hsub
    have hcl : closure (j '' W n) ∈ 𝓝 (0 : Completion T) := by
      simpa only [map_zero] using hj.closure_image_mem_nhds (hW.1.mem_of_mem (i := n) trivial)
    refine ⟨(U ∩ V) ∩ closure (j '' W n), inter_mem (inter_mem hU hV) hcl, ?_, fun _ h ↦ h.2⟩
    exact fun x hx y hy ↦ hUV (a := (x, y)) ⟨hx.1.1, hy.1.2⟩
  choose D hD hsub hcl using hsmall
  choose a hfin ha using fun n ↦ rect_finite_net hj.dense hK (inter_mem (hD n) (hD (n - 1)))
  refine ⟨a, hfin, fun z ↦ tendsto_sub_nhds_zero_iff.mp ?_, fun n z ↦ hPA n ?_⟩
  · refine tendsto_def.mpr fun S hS ↦ ?_
    obtain ⟨C, hC, hc, hCS⟩ := exists_mem_nhds_isClosed_subset hS
    have hpre : j ⁻¹' C ∈ 𝓝 (0 : T) :=
      Completion.continuous_toCompl.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using hC)
    obtain ⟨N, hN⟩ := hW.mem_iff.mp hpre
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ hCS (closure_minimal ?_ hc (hcl n (ha n z).1))⟩
    exact image_subset_iff.mpr ((hW.antitone hn).trans hN)
  · change j (a (n + 1) z - a n z) ∈ P n
    rw [map_sub, ← sub_sub_sub_cancel_right (j (a (n + 1) z)) (j (a n z)) z.1]
    exact hsub n _ (by simpa using (ha (n + 1) z).2) _ (ha n z).1

/-- A finite collection in the absolutely convex hull of a rectangle only needs finitely
many points from each factor. -/
private lemma rect_finite_support {E F T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : E → F → T) {U : Set E} {V : Set F} {K : Set T} (hK : K.Finite)
    (hsub : K ⊆ absConvexHull ℂ (image2 f U V)) :
    ∃ (P : Set E) (Q : Set F), P.Finite ∧ Q.Finite ∧ P ⊆ U ∧ Q ⊆ V ∧
      K ⊆ absConvexHull ℂ (image2 f P Q) := by
  let H (P : Set E) (Q : Set F) := absConvexHull ℂ (image2 f P Q)
  have mono {P P' : Set E} {Q Q' : Set F} (h : P ⊆ P') (h' : Q ⊆ Q') : H P Q ⊆ H P' Q' :=
    absConvexHull_mono (image2_subset h h')
  let S := {w | ∃ (P : Set E) (Q : Set F), P.Finite ∧ Q.Finite ∧ P ⊆ U ∧ Q ⊆ V ∧ w ∈ H P Q}
  have hS : H U V ⊆ S := by
    apply absConvexHull_min
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact ⟨{x}, {y}, finite_singleton _, finite_singleton _, singleton_subset_iff.mpr hx,
        singleton_subset_iff.mpr hy, subset_absConvexHull (mem_image2_of_mem (mem_singleton _) (mem_singleton _))⟩
    constructor
    · apply balanced_iff_smul_mem.mpr
      rintro a ha w ⟨P, Q, hP, hQ, hPU, hQV, hw⟩
      exact ⟨P, Q, hP, hQ, hPU, hQV, balanced_absConvexHull.smul_mem ha hw⟩
    · rintro w ⟨P, Q, hP, hQ, hPU, hQV, hw⟩ w' ⟨P', Q', hP', hQ', hPU', hQV', hw'⟩ a b ha hb hab
      exact ⟨P ∪ P', Q ∪ Q', hP.union hP', hQ.union hQ', union_subset hPU hPU',
        union_subset hQV hQV', convex_absConvexHull
          (mono subset_union_left subset_union_left hw) (mono subset_union_right subset_union_right hw') ha hb hab⟩
  induction K, hK using Set.Finite.induction_on with
  | empty => exact ⟨∅, ∅, finite_empty, finite_empty, empty_subset _, empty_subset _, empty_subset _⟩
  | @insert w K _ _ ih =>
    obtain ⟨P, Q, hP, hQ, hPU, hQV, hw⟩ := hS (hsub (mem_insert w K))
    obtain ⟨P', Q', hP', hQ', hPU', hQV', hK'⟩ := ih ((subset_insert w K).trans hsub)
    exact ⟨P ∪ P', Q ∪ Q', hP.union hP', hQ.union hQ', union_subset hPU hPU', union_subset hQV hQV',
      insert_subset (mono subset_union_left subset_union_left hw)
        (hK'.trans (mono subset_union_right subset_union_right))⟩

/-- An unrestricted rectangle of pure tensors accounts for the first approximation. -/
private lemma rect_unrestricted {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (z : E ⊗[ℂ] F) :
    z ∈ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) (univ : Set E) (univ : Set F)) := by
  suffices h : ∀ c : ℂ, c • z ∈ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) univ univ) by
    simpa only [one_smul] using h 1
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    intro c
    rw [smul_tmul']
    exact subset_absConvexHull (mem_image2_of_mem trivial trivial)
  | add x y hx hy =>
    intro c
    have hh : (0 : ℂ) ≤ 1 / 2 := by simp
    have h := convex_absConvexHull (hx (2*c)) (hy (2*c)) (a := 1/2) (b := 1/2) hh hh (by norm_num)
    simpa only [smul_smul, show (1/2 : ℂ) * (2*c) = c by ring, ← smul_add] using h

/-- The dyadic weights of all levels together fit inside a single convex hull. -/
private lemma rect_dyadic {T : Type*} [AddCommGroup T] [Module ℂ T] {S : Set T}
    (hS : Convex ℂ S) (h0 : 0 ∈ S) (a : ℕ → T)
    (ha : ∀ n, ((2 : ℂ) ^ (n+1)) • (a (n+1) - a n) ∈ S) :
    ∀ N k : ℕ, ((2 : ℂ) ^ k) • (a (k+N) - a k) ∈ S := by
  have hh : (0 : ℂ) ≤ 1 / 2 := by simp
  intro N
  induction N with
  | zero => simpa using fun _ : ℕ ↦ h0
  | succ N ih =>
    intro k
    have h := hS (ih (k+1)) (ha k) (a := 1/2) (b := 1/2) hh hh (by norm_num)
    have hpow : (1 / 2 : ℂ) * (2 ^ (k+1)) = 2 ^ k := by rw [pow_succ]; ring
    simpa only [smul_smul, hpow, ← smul_add, sub_add_sub_cancel, Nat.add_right_comm k 1 N, Nat.add_assoc] using h

/-- Adjoining the limit point to finite blocks supported in a shrinking base gives a compact set. -/
private lemma rect_compact_blocks {X : Type*} [TopologicalSpace X] {x : X}
    {U D : ℕ → Set X} (hU : (𝓝 x).HasAntitoneBasis U) (hf : ∀ n, (D n).Finite)
    (hs : ∀ n, D n ⊆ U n) : IsCompact (insert x (⋃ n, D n)) := by
  classical
  refine isCompact_of_finite_subcover fun {ι} O hO hcov ↦ ?_
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov (mem_insert x _))
  obtain ⟨N, hN⟩ := hU.mem_iff.mp ((hO i).mem_nhds hi)
  let K := ⋃ n ∈ Iio N, D n
  have hK : K.Finite := (finite_lt_nat N).biUnion fun n _ ↦ hf n
  have hKsub : K ⊆ insert x (⋃ n, D n) := by
    intro t ht
    obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp ht
    exact mem_insert_of_mem _ (mem_iUnion.mpr ⟨n, hn⟩)
  obtain ⟨s, hs'⟩ := hK.isCompact.elim_finite_subcover O hO (hKsub.trans hcov)
  refine ⟨insert i s, ?_⟩
  rintro t (rfl | ht)
  · exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hi⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp ht
  by_cases h : N ≤ n
  · exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hN (hU.antitone h (hs n hn))⟩
  · obtain ⟨j, hj, ht'⟩ := mem_iUnion₂.mp (hs' (mem_iUnion₂.mpr ⟨n, lt_of_not_ge h, hn⟩))
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, ht'⟩

section Rectangle

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The compact rectangle theorem for the completed projective tensor of complex Fréchet spaces:
every relatively compact set lies in the closed absolutely convex hull of pure tensors from
a single pair of compact sets. -/
lemma completedProjectiveTensor_compact_rectangle [UniformContinuousConstSMul ℂ (ProjectiveTensor E F)] (hE : IsFrechetTVS E) (hF : IsFrechetTVS F)
    {B : Set (Completion (ProjectiveTensor E F))} (hB : IsRelativelyCompact B) :
    ∃ (A : Set E) (C : Set F), IsCompact A ∧ IsCompact C ∧
      B ⊆ closedAbsConvexHull ℂ (image2 (fun x y ↦
        Completion.coe' (α := ProjectiveTensor E F) (x ⊗ₜ[ℂ] y)) A C) := by
  classical
  obtain ⟨_, hpolE, hmetrE, _⟩ := hE
  obtain ⟨_, hpolF, hmetrF, _⟩ := hF
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 (0 : F)).exists_antitone_basis
  let T := ProjectiveTensor E F
  let W (n : ℕ) : Set T := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) (U n) (V n))
  have hW : (𝓝 (0 : T)).HasAntitoneBasis W := by
    refine ⟨(projectiveTensor_zero_basis hU.1 hV.1).to_hasBasis ?_ ?_, fun _ _ h ↦
      absConvexHull_mono (image2_subset (hU.antitone h) (hV.antitone h))⟩
    · rintro ⟨i, k⟩ _
      exact ⟨max i k, trivial, absConvexHull_mono (image2_subset
        (hU.antitone (le_max_left _ _)) (hV.antitone (le_max_right _ _)))⟩
    · exact fun n _ ↦ ⟨(n, n), ⟨trivial, trivial⟩, Subset.rfl⟩
  let K := closure B
  let r (n : ℕ) : ℂ := 2 ^ (n+2)
  have hsmall (n : ℕ) : (fun t : T ↦ r n • t) ⁻¹' W n ∈ 𝓝 (0 : T) :=
    (continuous_const_smul (r n)).continuousAt.preimage_mem_nhds (by
      rw [smul_zero]
      exact hW.1.mem_of_mem (i := n) trivial)
  obtain ⟨a, hfin, hlim, hdiff⟩ := rect_controlled_approximation (K := K) hB hW hsmall
  -- The scaled differences at level n form a finite set in the hull of U n ⊗ V n.
  let d (n : ℕ) (z : K) : T := r n • (a (n+1) z - a n z)
  have hd (n : ℕ) : (range (d n)).Finite := by
    refine (((hfin (n+1)).image2 (· - ·) (hfin n)).image (fun t : T ↦ r n • t)).subset ?_
    exact range_subset_iff.mpr fun z ↦ ⟨_, mem_image2_of_mem (mem_range_self z) (mem_range_self z), rfl⟩
  choose P Q hP hQ hPU hQV hdPQ using fun n ↦ rect_finite_support (TensorProduct.tmul ℂ)
    (hd n) (show range (d n) ⊆ W n from range_subset_iff.mpr (hdiff n))
  -- The initial net is finite too, but has no smallness constraint on its factors.
  let d₀ (z : K) : T := (2 : ℂ) • a 0 z
  have hd₀ : (range d₀).Finite := ((hfin 0).image ((2 : ℂ) • ·)).subset
    (range_subset_iff.mpr fun z ↦ ⟨_, mem_range_self z, rfl⟩)
  obtain ⟨P₀, Q₀, hP₀, hQ₀, _, _, hd₀PQ⟩ := rect_finite_support (TensorProduct.tmul ℂ)
    hd₀ (fun t _ ↦ rect_unrestricted t)
  let A := P₀ ∪ insert 0 (⋃ n, P n)
  let C := Q₀ ∪ insert 0 (⋃ n, Q n)
  refine ⟨A, C, hP₀.isCompact.union (rect_compact_blocks hU hP hPU),
    hQ₀.isCompact.union (rect_compact_blocks hV hQ hQV), ?_⟩
  let H : Set T := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) A C)
  have hmem₀ (z : K) : d₀ z ∈ H := absConvexHull_mono (image2_subset
    (show P₀ ⊆ A from subset_union_left) (show Q₀ ⊆ C from subset_union_left)) (hd₀PQ (mem_range_self z))
  have hmem (n : ℕ) (z : K) : d n z ∈ H := absConvexHull_mono (image2_subset
    (((subset_iUnion P n).trans (subset_insert _ _)).trans subset_union_right)
    (((subset_iUnion Q n).trans (subset_insert _ _)).trans subset_union_right)) (hdPQ n (mem_range_self z))
  have h0 : (0 : T) ∈ H := by
    have h : (0 : E) ⊗ₜ[ℂ] (0 : F) ∈ H := subset_absConvexHull
      (mem_image2_of_mem (Or.inr (mem_insert _ _)) (Or.inr (mem_insert _ _)))
    change (0 : E ⊗[ℂ] F) ∈ H
    simpa only [zero_tmul] using h
  have haH (n : ℕ) (z : K) : a n z ∈ H := by
    let b : ℕ → T := fun k ↦ Nat.casesOn k 0 (fun j ↦ a j z)
    have hb (k : ℕ) : ((2 : ℂ) ^ (k+1)) • (b (k+1) - b k) ∈ H := by
      cases k with
      | zero => simpa [b, d₀] using hmem₀ z
      | succ k => exact hmem k z
    simpa [b] using rect_dyadic (S := H) convex_absConvexHull h0 b hb (n+1) 0
  let j : T →ₗ[ℂ] Completion T := Completion.toComplL.toLinearMap
  let S := closedAbsConvexHull ℂ (image2 (fun x y ↦ j (x ⊗ₜ[ℂ] y)) A C)
  have hS : AbsConvex ℂ S := absConvex_convexClosedHull
  have hjH : H ⊆ j ⁻¹' S := by
    apply absConvexHull_min _ ⟨hS.1.mulActionHom_preimage (f := j.toDistribMulActionHom.toMulActionHom),
      hS.2.linear_preimage j⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact subset_closedAbsConvexHull (mem_image2_of_mem hx hy)
  intro z hz
  let z' : K := ⟨z, subset_closure hz⟩
  exact (show IsClosed S from isClosed_closedAbsConvexHull).mem_of_tendsto (hlim z')
    (Eventually.of_forall fun n ↦ hjH (haH n z'))

/-- Bounded rectangle form of the compact rectangle theorem. -/
lemma completedProjectiveTensor_bounded_rectangle [UniformContinuousConstSMul ℂ (ProjectiveTensor E F)] (hE : IsFrechetTVS E) (hF : IsFrechetTVS F)
    {B : Set (Completion (ProjectiveTensor E F))} (hB : IsRelativelyCompact B) :
    ∃ (A : Set E) (C : Set F), IsVonNBounded ℂ A ∧ IsVonNBounded ℂ C ∧
      B ⊆ closedAbsConvexHull ℂ (image2 (fun x y ↦
        Completion.coe' (α := ProjectiveTensor E F) (x ⊗ₜ[ℂ] y)) A C) := by
  obtain ⟨A, C, hA, hC, hsub⟩ := completedProjectiveTensor_compact_rectangle hE hF hB
  obtain ⟨_, _, _, _⟩ := hE
  obtain ⟨_, _, _, _⟩ := hF
  exact ⟨A, C, hA.isVonNBounded ℂ, hC.isVonNBounded ℂ, hsub⟩

end Rectangle

end CompactRectangles

section Diagonal

universe u v

variable {E : Type*} {F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  {X : ℕ → Type u} {Y : ℕ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]
  {j : ∀ n, X n →L[ℂ] X (n+1)} {i : ∀ n, X n →L[ℂ] E}
  {k : ∀ n, Y n →L[ℂ] Y (n+1)} {l : ∀ n, Y n →L[ℂ] F}

open scoped ComplexOrder

/-- A relatively compact set in the completed inductive tensor of strict
limits of nuclear Fréchet spaces is controlled by a bounded rectangle. -/
lemma completedInductiveTensor_bounded_rectangle [PolynormableSpace ℂ E] [T2Space E]
    [PolynormableSpace ℂ F] [T2Space F] [UniformContinuousConstSMul ℂ (InductiveTensor E F)]
    (h : IsInjectiveLCLimit j i) (h' : IsInjectiveLCLimit k l)
    (hj : ∀ n, IsEmbedding (j n)) (hk : ∀ n, IsEmbedding (k n))
    (hX : ∀ n, IsFrechetTVS (X n)) (hY : ∀ n, IsFrechetTVS (Y n))
    (hn : ∀ n, IsNuclearTVS.{v} (X n)) {B : Set (Completion (InductiveTensor E F))}
    (hB : IsCompact (closure B)) :
    ∃ P : Set E, ∃ Q : Set F, IsVonNBounded ℂ P ∧ IsVonNBounded ℂ Q ∧
      B ⊆ closure (absConvexHull ℂ (image2 (fun x y ↦ Completion.coe' (α := InductiveTensor E F)
        (x ⊗ₜ[ℂ] y)) P Q)) := by
  let T := InductiveTensor E F
  let : ∀ n, PolynormableSpace ℂ (X n) := fun n ↦ (hX n).choose_spec.1
  let : ∀ n, PolynormableSpace ℂ (Y n) := fun n ↦ (hY n).choose_spec.1
  let : ∀ n, MetrizableSpace (X n) := fun n ↦ (hX n).choose_spec.2.1
  let : ∀ n, MetrizableSpace (Y n) := fun n ↦ (hY n).choose_spec.2.1
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  let : ∀ n, IsTopologicalAddGroup (X n) := fun n ↦ (hX n).choose
  let : ∀ n, IsTopologicalAddGroup (Y n) := fun n ↦ (hY n).choose
  let : PolynormableSpace ℂ (Completion T) := polynormableSpace_completion
  obtain ⟨n,D,-,hD⟩ := completedInductiveTensor_bounded_projectiveStage h h' hj hk hX hY hn (hB.isVonNBounded ℂ)
  let S := ProjectiveTensor (X n) (Y n)
  let : UniformContinuousConstSMul ℂ S := uniformContinuousConstSMul_of_continuousConstSMul ℂ S
  let I : S →L[ℂ] T := ⟨TensorProduct.map (i n).toLinearMap (l n).toLinearMap,
    continuous_projectiveStage_inductiveTensor (i n) (l n) (hX n) (hY n)⟩
  have hI : IsEmbedding I := isEmbedding_projectiveStage_inductiveTensor (i n) (l n)
    (h.isEmbedding_stage hj n) (h'.isEmbedding_stage hk n) (hX n) (hY n) (hn n).tensorComparison
  have hcomp : IsEmbedding I.completion := (Completion.isUniformInducing_extension
    ((Completion.isUniformInducing_coe T).comp (AddMonoidHom.isUniformInducing_of_isInducing
      (f := I.toLinearMap.toAddMonoidHom) hI.isInducing))).isUniformEmbedding.isEmbedding
  change I.completion '' D = closure B at hD
  have hc : IsCompact D := hcomp.isInducing.isCompact_iff.mpr (hD.symm ▸ hB)
  obtain ⟨A,C,hA,hC,hsub⟩ := completedProjectiveTensor_bounded_rectangle (hX n) (hY n) (by change IsCompact (closure D); rwa [hc.isClosed.closure_eq])
  let M := image2 (fun x y ↦ Completion.coe' (α := T) (x ⊗ₜ[ℂ] y)) (i n '' A) (l n '' C)
  let U := closedAbsConvexHull ℂ M
  have hU : AbsConvex ℂ U := absConvex_convexClosedHull
  have hpre : AbsConvex ℂ (I.completion ⁻¹' U) :=
    ⟨hU.1.mulActionHom_preimage (f := I.completion.toLinearMap.toDistribMulActionHom.toMulActionHom),
      hU.2.linear_preimage I.completion.toLinearMap⟩
  refine ⟨i n '' A, l n '' C, hA.image (i n), hC.image (l n), subset_closure.trans ?_⟩
  rw [← hD, ← closedAbsConvexHull_eq_closure_absConvexHull]
  apply image_subset_iff.mpr
  refine hsub.trans (closedAbsConvexHull_min ?_ hpre (isClosed_closedAbsConvexHull.preimage I.completion.continuous))
  rintro _ ⟨x,hx,y,hy,rfl⟩
  change I.completion (Completion.coe' (α := S) (x ⊗ₜ[ℂ] y)) ∈ U
  rw [I.completion_apply_coe (show S from x ⊗ₜ[ℂ] y)]
  apply subset_closedAbsConvexHull
  exact mem_image2_of_mem (mem_image_of_mem (i n) hx) (mem_image_of_mem (l n) hy)

end Diagonal

end RiemannMasullo