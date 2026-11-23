module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
import Mathlib.Analysis.Normed.Lp.lpSpace

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

/-- A non-complete normed space refutes the representation claim. -/
private theorem tensorDualOperator_represents_finiteRank_false_of_not_complete
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] (hE : ¬ CompleteSpace E) :
    ¬ Printed.tensorDualOperator_represents_finiteRank.{u, v} := by
  intro H
  have hex : ∃ h : Completion E, h ∉ Set.range ((↑) : E → Completion E) := by
    by_contra hc
    push Not at hc
    exact hE (((Completion.isUniformInducing_coe E).completeSpace_congr
      fun h ↦ hc h).mpr inferInstance)
  obtain ⟨h, hh⟩ := hex
  let ev : StrongDual ℂ E →ₗ[ℂ] ℂ :=
    { toFun := fun φ ↦ φ.fromCompletion h
      map_add' := fun φ ψ ↦ congrArg (fun T : Completion E →L[ℂ] ℂ ↦ T h)
        (ContinuousLinearMap.fromCompletion_unique (φ + ψ)
          (φ.fromCompletion + ψ.fromCompletion) fun e ↦ by simp)
      map_smul' := fun c φ ↦ congrArg (fun T : Completion E →L[ℂ] ℂ ↦ T h)
        (ContinuousLinearMap.fromCompletion_unique (c • φ)
          (c • φ.fromCompletion) fun e ↦ by simp) }
  let T : StrongDual ℂ E →ₗ[ℂ] ULift.{v} ℂ :=
    (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).symm.toLinearMap ∘ₗ ev
  have hfin : FiniteDimensional ℂ (LinearMap.range T) := by
    have : FiniteDimensional ℂ (ULift.{v} ℂ) :=
      Module.Finite.equiv (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).symm
    infer_instance
  have hcont' : @Continuous _ (WeakSpace ℂ (ULift.{v} ℂ)) (completionCompactDualTopology E) _
      (fun φ ↦ toWeakSpace ℂ (ULift.{v} ℂ) (T φ)) := by
    let : TopologicalSpace (StrongDual ℂ E) := completionCompactDualTopology E
    let K : Set (Set (Completion E)) := {A | IsCompact A}
    have hext : Continuous (fun φ : StrongDual ℂ E ↦
        UniformOnFun.ofFun K (φ.fromCompletion : Completion E → ℂ)) := continuous_induced_dom
    have heval : Continuous (fun φ : StrongDual ℂ E ↦ φ.fromCompletion h) :=
      (UniformOnFun.uniformContinuous_eval_of_mem (β := ℂ) K (Set.mem_singleton h)
        isCompact_singleton).continuous.comp hext
    exact (toWeakSpaceCLM ℂ (ULift.{v} ℂ)).continuous.comp (continuous_uliftUp.comp heval)
  obtain ⟨z, hz⟩ := H E (ULift.{v} ℂ) T hfin hcont'
  let L : E ⊗[ℂ] ULift.{v} ℂ →ₗ[ℂ] E :=
    (TensorProduct.rid ℂ E).toLinearMap ∘ₗ
      TensorProduct.map LinearMap.id (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).toLinearMap
  have key : ∀ (w : E ⊗[ℂ] ULift.{v} ℂ) (φ : StrongDual ℂ E),
      (tensorDualOperator w φ).down = φ (L w) := by
    intro w φ
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      rw [tensorDualOperator_tmul]
      simp [L, mul_comm]
    | add a b ha hb => simp [ha, hb]
  have heq : ∀ φ : StrongDual ℂ E, φ.fromCompletion h = φ (L z) := by
    intro φ
    rw [← key z φ, hz]
    rfl
  obtain ⟨ψ, hψ⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ)
    (x := h) (y := ((L z : E) : Completion E)) fun e ↦ hh ⟨_, e.symm⟩
  have hφ : (ψ.comp (Completion.toComplL (S := ℂ))).fromCompletion = ψ :=
    ContinuousLinearMap.fromCompletion_unique _ _ fun e ↦ rfl
  apply hψ
  have := heq (ψ.comp (Completion.toComplL (S := ℂ)))
  rw [hφ] at this
  exact this

/-- The finitely supported vectors of ℓ²(ℕ) (index lifted to `Type u`) are not complete. -/
private theorem tensorDualOperator_represents_finiteRank_false_span_not_complete :
    ¬ CompleteSpace (Submodule.span ℂ
      (Set.range fun i : ULift.{u} ℕ ↦ lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (1 : ℂ)) :
        Submodule ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2)) := by
  set D := Submodule.span ℂ
    (Set.range fun i : ULift.{u} ℕ ↦ lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (1 : ℂ)) with hD
  intro hc
  have hcl : IsClosed (D : Set (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2)) :=
    (completeSpace_coe_iff_isComplete.mp hc).isClosed
  have hmem : Memℓp (fun i : ULift.{u} ℕ ↦ (1 / 2 : ℂ) ^ i.down) 2 := by
    refine memℓp_gen ?_
    have hs : Summable (fun n : ℕ ↦ ((1 / 4 : ℝ)) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (Equiv.ulift.{u}.symm.summable_iff).mp ?_
    convert hs using 1
    funext n
    simp only [Function.comp_apply, Equiv.ulift_symm_down, norm_pow, norm_div, norm_one,
      Complex.norm_ofNat, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  let x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := ⟨_, hmem⟩
  have hxD : x ∈ D := by
    refine hcl.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
      (Filter.Eventually.of_forall fun s ↦ D.sum_mem fun i _ ↦ ?_)
    have : lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (x i) =
        x i • lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (1 : ℂ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact D.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfin : ∀ y ∈ D, (Function.support (y : ULift.{u} ℕ → ℂ)).Finite := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine (Set.finite_singleton i).subset ?_
      rw [lp.coeFn_single]
      exact Pi.support_single_subset
    | zero =>
      rw [lp.coeFn_zero, Function.support_zero]
      exact Set.finite_empty
    | add a b _ _ ha hb =>
      rw [lp.coeFn_add]
      exact (ha.union hb).subset (Function.support_add _ _)
    | smul c a _ ha =>
      rw [lp.coeFn_smul]
      exact ha.subset (Function.support_const_smul_subset c _)
  have hsupp : Function.support (x : ULift.{u} ℕ → ℂ) = Set.univ := by
    ext i
    simp [x]
  exact Set.infinite_univ (hsupp ▸ hfin x hxD)

/-- Paper: Remark C.2.3.2, p. 677. Take E to be the finitely supported complex
sequences with the ℓ² norm and F to be ℂ. In the completion of E the vector with
coordinates 2⁻ⁿ, n ≥ 0, defines a rank-one evaluation on E′, μ-continuous by the
singleton compact set. Each tensor with scalar second factor evaluates at a finitely
supported vector. The coordinate functionals distinguish that vector from (2⁻ⁿ). -/
theorem Printed.tensorDualOperator_represents_finiteRank_false :
    ¬ Printed.tensorDualOperator_represents_finiteRank :=
  tensorDualOperator_represents_finiteRank_false_of_not_complete _
    tensorDualOperator_represents_finiteRank_false_span_not_complete

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

/-- Coordinates of the tail projection that zeroes the first `m` coordinates of ℓ². -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_proj_apply
    (m : ℕ) (y : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) (k : ULift.{u} ℕ) :
    ((ContinuousLinearMap.id ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) -
      ∑ n ∈ Finset.range m, (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n)).smulRight
        (lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n) (1 : ℂ))) y : _) k =
      if k.down < m then 0 else y k := by
  rw [sub_apply, sum_apply, lp.coeFn_sub,
    lp.coeFn_sum, Pi.sub_apply, Finset.sum_apply]
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, lp.coeFn_smul,
    Pi.smul_apply, lp.coeFn_single, smul_eq_mul]
  have : ∀ n ∈ Finset.range m, lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n) y *
      Pi.single (M := fun _ : ULift.{u} ℕ ↦ ℂ) (ULift.up n) (1 : ℂ) k = if n = k.down then y k else 0 := by
    intro n _
    by_cases h : n = k.down
    · subst h
      simp
      rfl
    · have hk : k ≠ ULift.up n := fun e ↦ h (by rw [e])
      simp [h, hk]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  split_ifs <;> simp

/-- Elements of the span of the coordinate vectors of ℓ² vanish beyond some index. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_eventually_zero
    (y : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2)
    (hy : y ∈ Submodule.span ℂ (Set.range fun n : ULift.{u} ℕ ↦
      lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 n (1 : ℂ))) :
    ∃ N : ℕ, ∀ k : ULift.{u} ℕ, N ≤ k.down → y k = 0 := by
  have hfin : (Function.support (y : ULift.{u} ℕ → ℂ)).Finite := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine (Set.finite_singleton i).subset ?_
      rw [lp.coeFn_single]
      exact Pi.support_single_subset
    | zero =>
      rw [lp.coeFn_zero, Function.support_zero]
      exact Set.finite_empty
    | add a b _ _ ha hb =>
      rw [lp.coeFn_add]
      exact (ha.union hb).subset (Function.support_add _ _)
    | smul c a _ ha =>
      rw [lp.coeFn_smul]
      exact ha.subset (Function.support_const_smul_subset c _)
  obtain ⟨N, hN⟩ := (hfin.image ULift.down).bddAbove
  refine ⟨N + 1, fun k hk ↦ ?_⟩
  by_contra hne
  have := hN ⟨k, hne, rfl⟩
  omega

/-- A single-stage system over `PUnit` has a Hausdorff locally convex direct limit. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_t2_single
    (V : Type v) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V]
    [T2Space V] :
    @T2Space (Module.DirectLimit (fun _ : PUnit.{j + 1} ↦ V) (fun _ _ _ ↦ LinearMap.id))
      (lcDirectLimitTopology (X := fun _ : PUnit.{j + 1} ↦ V) (fun _ _ _ ↦ LinearMap.id)) := by
  let f : ∀ a b : PUnit.{j + 1}, a ≤ b → V →ₗ[ℂ] V := fun _ _ _ ↦ LinearMap.id
  let : TopologicalSpace (Module.DirectLimit (fun _ : PUnit.{j + 1} ↦ V) f) :=
    lcDirectLimitTopology (X := fun _ : PUnit.{j + 1} ↦ V) f
  let L := Module.DirectLimit (fun _ : PUnit.{j + 1} ↦ V) f
  let e := Module.DirectLimit.of ℂ PUnit.{j + 1} (fun _ ↦ V) f
  let g : L →ₗ[ℂ] V :=
    Module.DirectLimit.lift ℂ PUnit.{j + 1} (fun _ ↦ V) f (fun _ ↦ LinearMap.id)
      (fun _ _ _ _ ↦ rfl)
  have hge (x : V) : g (e PUnit.unit x) = x :=
    Module.DirectLimit.lift_of (G := fun _ ↦ V) (f := f) (fun _ ↦ LinearMap.id)
      (fun _ _ _ _ ↦ rfl) x
  have hinj : Function.Injective g := by
    intro z w hzw
    obtain ⟨⟨⟩, x, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨⟨⟩, y, rfl⟩ := Module.DirectLimit.exists_of w
    rw [hge, hge] at hzw
    rw [hzw]
  let P : SeminormFamily ℂ L {p : Seminorm ℂ L // ∀ k, Continuous (p ∘ e k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have hV := PolynormableSpace.withSeminorms ℂ V
  have := hV.isTopologicalAddGroup
  have hg : Continuous g := hV.continuous_of_continuous_comp _ fun q ↦ by
    have hq : ∀ k, Continuous (((q.1).comp g) ∘ e k) := by
      rintro ⟨⟩
      have : ((q.1).comp g) ∘ e PUnit.unit = q.1 := funext fun x ↦ by simp [hge]
      rw [this]
      exact q.2
    exact hP.continuous_seminorm ⟨(q.1).comp g, hq⟩
  exact T2Space.of_injective_continuous hinj hg

/-- The completed inductive tensor map is continuous and acts on the dense image by the
inductive tensor map. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_map
    {E F A B : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    (f : E →L[ℂ] A) (g : F →L[ℂ] B) :
    Continuous (Printed.completedInductiveTensorMap f g) ∧
      ∀ t : InductiveTensor E F, Printed.completedInductiveTensorMap f g (t : Completion _) =
        ((inductiveTensorMap f.toLinearMap g.toLinearMap t : InductiveTensor A B) :
          Completion _) := by
  let T : InductiveTensor E F →L[ℂ] InductiveTensor A B :=
    ⟨inductiveTensorMap f.toLinearMap g.toLinearMap, inductiveTensorMap_continuous f g⟩
  have h : Printed.completedInductiveTensorMap f g = T.completion.toLinearMap := rfl
  rw [h]
  exact ⟨T.completion.continuous, fun t ↦ ContinuousLinearMap.completion_apply_coe T t⟩

/-- The completed inductive tensor stages of two directed systems form a directed system. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_directed
    {I : Type i} {J : Type j} [Preorder I] [Preorder J] (X : I → Type u) (Y : J → Type v)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h)) :
    DirectedSystem (fun p : I × J ↦ Completion (InductiveTensor (X p.1) (Y p.2)))
      (fun (p q : I × J) (h : p ≤ q) z ↦ Printed.completedInductiveTensorMap
        ⟨f p.1 q.1 h.1, hf p.1 q.1 h.1⟩ ⟨g p.2 q.2 h.2, hg p.2 q.2 h.2⟩ z) := by
  constructor
  · intro p z
    have h : p ≤ p := le_rfl
    obtain ⟨hc, hcoe⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f p.1 p.1 h.1, hf p.1 p.1 h.1⟩ ⟨g p.2 p.2 h.2, hg p.2 p.2 h.2⟩
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq hc continuous_id
    | ih t =>
      rw [hcoe]
      congr 1
      change TensorProduct.map (f p.1 p.1 h.1) (g p.2 p.2 h.2) t = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [TensorProduct.map_tmul, DirectedSystem.map_self (f := (f · · ·)),
          DirectedSystem.map_self (f := (g · · ·))]
      | add a b ha hb => rw [map_add, ha, hb]
  · intro r q p hpq hqr z
    obtain ⟨hc1, hcoe1⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f p.1 q.1 hpq.1, hf p.1 q.1 hpq.1⟩ ⟨g p.2 q.2 hpq.2, hg p.2 q.2 hpq.2⟩
    obtain ⟨hc2, hcoe2⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f q.1 r.1 hqr.1, hf q.1 r.1 hqr.1⟩ ⟨g q.2 r.2 hqr.2, hg q.2 r.2 hqr.2⟩
    obtain ⟨hc3, hcoe3⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f p.1 r.1 (hpq.trans hqr).1, hf p.1 r.1 (hpq.trans hqr).1⟩
      ⟨g p.2 r.2 (hpq.trans hqr).2, hg p.2 r.2 (hpq.trans hqr).2⟩
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (hc2.comp hc1) hc3
    | ih t =>
      rw [hcoe1, hcoe2, hcoe3]
      congr 1
      change TensorProduct.map (f q.1 r.1 hqr.1) (g q.2 r.2 hqr.2)
        (TensorProduct.map (f p.1 q.1 hpq.1) (g p.2 q.2 hpq.2) t) =
          TensorProduct.map (f p.1 r.1 (hpq.trans hqr).1) (g p.2 r.2 (hpq.trans hqr).2) t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
          DirectedSystem.map_map (f := (f · · ·)), DirectedSystem.map_map (f := (g · · ·))]
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- The completion of a space with a single point has a single point. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_completion_zero
    {α : Type*} {_ : UniformSpace α} {_ : Zero α} (h : ∀ x : α, x = 0) (c : Completion α) :
    c = 0 := by
  induction c using Completion.induction_on with
  | hp => exact isClosed_eq continuous_id continuous_const
  | ih x => rw [h x, Completion.coe_zero]

/-- Functoriality of completions for a functional evaluated after two maps. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_key
    {E C C' : Type*} [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module ℂ E]
    [UniformContinuousConstSMul ℂ E] [UniformSpace C] [AddCommGroup C] [IsUniformAddGroup C]
    [Module ℂ C] [UniformContinuousConstSMul ℂ C] [UniformSpace C'] [AddCommGroup C']
    [IsUniformAddGroup C'] [Module ℂ C'] [UniformContinuousConstSMul ℂ C']
    (J : E →L[ℂ] C) (Ψ : C → C') (Φ : Completion C → Completion C') (hΦc : Continuous Φ)
    (hΦ : ∀ t : C, Φ t = (Ψ t : Completion C')) (ℓ : C' →L[ℂ] ℂ) (κ : E →L[ℂ] ℂ)
    (h : ∀ x, ℓ (Ψ (J x)) = κ x) (c : Completion E) :
    ℓ.fromCompletion (Φ (J.completion c)) = κ.fromCompletion c := by
  induction c using Completion.induction_on with
  | hp =>
    exact isClosed_eq (ℓ.fromCompletion.continuous.comp (hΦc.comp J.completion.continuous))
      κ.fromCompletion.continuous
  | ih x =>
    rw [ContinuousLinearMap.completion_apply_coe, hΦ, ContinuousLinearMap.fromCompletion_apply_coe,
      ContinuousLinearMap.fromCompletion_apply_coe, h]

/-- If the limit of the first system is zero and some completed stage has an element that
no transition kills, the printed embedding claim fails for the two systems. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_of_nonvanishing
    (H : Printed.completedInductiveTensor_directLimits_isEmbedding.{u, v, i, j})
    (I : Type i) (J : Type j) [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]
    (X : I → Type u) (Y : J → Type v)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h))
    [@T2Space _ (lcDirectLimitTopology f)] [@T2Space _ (lcDirectLimitTopology g)]
    (hXsub : ∀ z : Module.DirectLimit X f, z = 0) (p0 : I × J)
    (w : Completion (InductiveTensor (X p0.1) (Y p0.2)))
    (hw : ∀ (q : I × J) (h : p0 ≤ q), Printed.completedInductiveTensorMap
      ⟨f p0.1 q.1 h.1, hf p0.1 q.1 h.1⟩ ⟨g p0.2 q.2 h.2, hg p0.2 q.2 h.2⟩ w ≠ 0) : False := by
  have hdir := completedInductiveTensor_directLimits_isEmbedding_false_directed X Y f g hf hg
  obtain ⟨T, hT, hemb⟩ := H I J X Y f g hf hg
  have hT0 : T (Module.DirectLimit.of ℂ _ _ _ p0 w) = T 0 := by
    rw [map_zero, hT]
    have hzero : ∀ r : Module.DirectLimit X f ⊗[ℂ] Module.DirectLimit Y g, r = 0 := by
      intro r
      induction r using TensorProduct.inductionOn with
      | tmul x y => rw [hXsub x, TensorProduct.zero_tmul]
      | add r₁ r₂ h₁ h₂ => rw [h₁, h₂, add_zero]
    exact completedInductiveTensor_directLimits_isEmbedding_false_completion_zero hzero _
  obtain ⟨-, hinj⟩ := hemb
  have : IsDirectedOrder (I × J) := ⟨fun a b ↦ by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    obtain ⟨d, had, hbd⟩ := exists_ge_ge a.2 b.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩⟩
  obtain ⟨q, hq, hqz⟩ := Module.DirectLimit.of.zero_exact (hinj hT0)
  exact hw q hq hqz

/-- The printed embedding claim fails for the tail stages of the finitely supported vectors
of ℓ², with projections as transitions, against the single stage ℂ. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_main :
    ¬ Printed.completedInductiveTensor_directLimits_isEmbedding.{u, v, i, j} := by
  intro H
  let P : ℕ → lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := fun m ↦
    ContinuousLinearMap.id ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) -
      ∑ n ∈ Finset.range m, (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n)).smulRight
        (lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n) (1 : ℂ))
  have hP : ∀ m y k, (P m y : ULift.{u} ℕ → ℂ) k = if k.down < m then 0 else y k :=
    completedInductiveTensor_directLimits_isEmbedding_false_proj_apply
  have hPP : ∀ n m y, n ≤ m → P m (P n y) = P m y := by
    intro n m y hnm
    ext k
    rw [hP, hP, hP]
    split_ifs <;> first | rfl | omega
  let D : Submodule ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) := Submodule.span ℂ
    (Set.range fun n : ULift.{u} ℕ ↦ lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 n (1 : ℂ))
  let Xs : ULift.{i} ℕ → Submodule ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) :=
    fun n ↦ D.map (P n.down).toLinearMap
  let X : ULift.{i} ℕ → Type u := fun n ↦ Xs n
  have hmaps : ∀ n m : ULift.{i} ℕ, n ≤ m → ∀ y ∈ Xs n, P m.down y ∈ Xs m := by
    rintro n m hnm _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hPP _ _ _ hnm).symm⟩
  let f : ∀ n m : ULift.{i} ℕ, n ≤ m → X n →ₗ[ℂ] X m := fun n m h ↦
    (P m.down).toLinearMap.restrict (hmaps n m h)
  have hfapply : ∀ n m h (x : X n), ((f n m h x : Xs m) : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) =
      P m.down (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) := fun _ _ _ _ ↦ rfl
  have hfc : ∀ n m h, Continuous (f n m h) := fun n m h ↦
    ((P m.down).continuous.comp continuous_subtype_val).subtype_mk _
  have : DirectedSystem X (f · · ·) := by
    constructor
    · rintro n ⟨_, ⟨x, hx, rfl⟩⟩
      exact Subtype.ext (hPP _ _ _ le_rfl)
    · intro a b c hab hbc x
      exact Subtype.ext (hPP _ _ _ hbc)
  have hXsub : ∀ z : Module.DirectLimit X f, z = 0 := by
    intro z
    obtain ⟨n, x, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨N, hN⟩ :=
      completedInductiveTensor_directLimits_isEmbedding_false_eventually_zero y hy
    let m : ULift.{i} ℕ := ⟨max n.down N⟩
    have hnm : n ≤ m := (le_max_left n.down N : n.down ≤ max n.down N)
    have hzero : f n m hnm x = 0 := by
      apply Subtype.ext
      rw [hfapply n m hnm x, ← hyx]
      change P m.down (P n.down y) = 0
      rw [hPP _ _ _ (le_max_left _ _)]
      ext k
      rw [hP]
      split_ifs with hk
      · rfl
      · have hk' : ¬ k.down < max n.down N := hk
        exact hN k (by omega)
    rw [← Module.DirectLimit.of_f (hij := hnm), hzero, map_zero]
  have hXT2 : @T2Space _ (lcDirectLimitTopology f) := by
    let := lcDirectLimitTopology f
    exact T2Space.of_injective_continuous (Y := PUnit.{1}) (f := fun _ ↦ PUnit.unit)
      (fun a b _ ↦ (hXsub a).trans (hXsub b).symm) continuous_const
  let g : ∀ a b : PUnit.{j + 1}, a ≤ b → ULift.{v} ℂ →ₗ[ℂ] ULift.{v} ℂ :=
    fun _ _ _ ↦ LinearMap.id
  have : DirectedSystem (fun _ : PUnit.{j + 1} ↦ ULift.{v} ℂ) (g · · ·) := by
    constructor <;> intros <;> rfl
  have hYT2 : @T2Space _ (lcDirectLimitTopology g) :=
    completedInductiveTensor_directLimits_isEmbedding_false_t2_single (ULift.{v} ℂ)
  have hgc : ∀ a b h, Continuous (g a b h) := fun _ _ _ ↦ continuous_id
  -- the vector (2⁻ⁿ) of ℓ²
  have hmem : Memℓp (fun k : ULift.{u} ℕ ↦ (1 / 2 : ℂ) ^ k.down) 2 := by
    refine memℓp_gen ?_
    have hs : Summable (fun n : ℕ ↦ ((1 / 4 : ℝ)) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (Equiv.ulift.{u}.symm.summable_iff).mp ?_
    convert hs using 1
    funext n
    simp only [Function.comp_apply, Equiv.ulift_symm_down, norm_pow, norm_div, norm_one,
      Complex.norm_ofNat, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  let a : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := ⟨_, hmem⟩
  have hP0 : ∀ y, P 0 y = y := fun y ↦ by
    ext k
    rw [hP]
    simp
  have hsmem : ∀ N, P 0 (∑ k ∈ Finset.range N,
      lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up k) (a (ULift.up k))) ∈ Xs ⟨0⟩ :=
    fun N ↦ ⟨_, D.sum_mem fun k _ ↦ by
      have : lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up k) (a (ULift.up k)) =
          a (ULift.up k) • lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up k) (1 : ℂ) := by
        rw [← lp.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact D.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩), rfl⟩
  let s : ℕ → X ⟨0⟩ := fun N ↦ ⟨_, hsmem N⟩
  have hs : Filter.Tendsto (fun N ↦ ((s N : Xs ⟨0⟩) : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2))
      Filter.atTop (𝓝 a) := by
    have h := (Equiv.ulift.{u}.symm.hasSum_iff).mpr (lp.hasSum_single (by norm_num) a)
    convert h.tendsto_sum_nat using 1
    funext N
    exact hP0 _
  have hcs : CauchySeq (fun N ↦ ((s N : X ⟨0⟩) : Completion (X ⟨0⟩))) := by
    have h1 : CauchySeq s := by
      unfold CauchySeq
      rw [← (isUniformEmbedding_subtype_val.isUniformInducing).cauchy_map_iff, Filter.map_map]
      exact hs.cauchySeq
    exact (Completion.uniformContinuous_coe _).comp_cauchySeq h1
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcs
  let ι : X ⟨0⟩ →L[ℂ] lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := (Xs ⟨0⟩).subtypeL
  have hιb : ι.fromCompletion b = a := by
    refine tendsto_nhds_unique ((ι.fromCompletion.continuous.tendsto b).comp hb) ?_
    convert hs using 1
    funext N
    simp only [Function.comp_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hJc : @Continuous (X ⟨0⟩) (InductiveTensor (X ⟨0⟩) (ULift.{v} ℂ)) _ _
      (fun x : X ⟨0⟩ ↦ x ⊗ₜ[ℂ] (ULift.up 1 : ULift.{v} ℂ)) :=
    (withGeneratingSeminorms_spec (X ⟨0⟩ ⊗[ℂ] ULift.{v} ℂ)
      (fun p : {p : Seminorm ℂ (X ⟨0⟩ ⊗[ℂ] ULift.{v} ℂ) //
        (∀ x : X ⟨0⟩, Continuous (fun y : ULift.{v} ℂ ↦ p (x ⊗ₜ[ℂ] y))) ∧
        (∀ y : ULift.{v} ℂ, Continuous (fun x : X ⟨0⟩ ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
      ).continuous_of_continuous_comp
      ((TensorProduct.mk ℂ (X ⟨0⟩) (ULift.{v} ℂ)).flip (ULift.up 1)) fun p ↦ p.2.2 (ULift.up 1)
  let Jm : X ⟨0⟩ →L[ℂ] InductiveTensor (X ⟨0⟩) (ULift.{v} ℂ) :=
    ⟨(TensorProduct.mk ℂ (X ⟨0⟩) (ULift.{v} ℂ)).flip (ULift.up 1), hJc⟩
  let p0 : ULift.{i} ℕ × PUnit.{j + 1} := (⟨0⟩, PUnit.unit)
  let w : Completion (InductiveTensor (X p0.1) (ULift.{v} ℂ)) := Jm.completion b
  refine completedInductiveTensor_directLimits_isEmbedding_false_of_nonvanishing H
    (ULift.{i} ℕ) PUnit.{j + 1} X (fun _ ↦ ULift.{v} ℂ) f g hfc hgc hXsub p0 w ?_
  intro q hq hqz
  let m := q.1.down
  let bil : X q.1 →ₗ[ℂ] ULift.{v} ℂ →ₗ[ℂ] ℂ := (LinearMap.mul ℂ ℂ).compl₁₂
    ((lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).toLinearMap ∘ₗ (Xs q.1).subtype)
    (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).toLinearMap
  let ℓl : InductiveTensor (X q.1) (ULift.{v} ℂ) →ₗ[ℂ] ℂ := TensorProduct.lift bil
  have hℓ : ∀ (x : X q.1) (c : ULift.{v} ℂ),
      ℓl (x ⊗ₜ[ℂ] c) = (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) (ULift.up m) * c.down :=
    fun _ _ ↦ rfl
  have hℓc : Continuous ℓl := by
    refine (continuous_inductiveTensor_iff ℓl).mpr ⟨fun x ↦ ?_, fun c ↦ ?_⟩
    · simp_rw [hℓ]
      exact continuous_const.mul continuous_uliftDown
    · simp_rw [hℓ]
      exact ((lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).continuous.comp
        continuous_subtype_val).mul continuous_const
  let ℓ : InductiveTensor (X q.1) (ULift.{v} ℂ) →L[ℂ] ℂ := ⟨ℓl, hℓc⟩
  obtain ⟨hc, hcoe⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
    ⟨f p0.1 q.1 hq.1, hfc p0.1 q.1 hq.1⟩ ⟨g p0.2 q.2 hq.2, hgc p0.2 q.2 hq.2⟩
  let κ : X ⟨0⟩ →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).comp ι
  have hκ : κ.fromCompletion b = (a : ULift.{u} ℕ → ℂ) (ULift.up m) := by
    have : κ.fromCompletion =
        (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).comp ι.fromCompletion :=
      ContinuousLinearMap.fromCompletion_unique _ _ fun x ↦ by
        simp only [κ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rw [this, ContinuousLinearMap.comp_apply, hιb]
    rfl
  have hstep : ∀ x : X ⟨0⟩, ℓ (inductiveTensorMap (f p0.1 q.1 hq.1) (g p0.2 q.2 hq.2) (Jm x)) =
      κ x := by
    intro x
    change ℓl (f p0.1 q.1 hq.1 x ⊗ₜ[ℂ] g p0.2 q.2 hq.2 (ULift.up 1)) = _
    rw [hℓ, hfapply p0.1 q.1 hq.1 x]
    change (P m (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) : ULift.{u} ℕ → ℂ) (ULift.up m) * 1 =
      (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) (ULift.up m)
    rw [hP]
    simp
  have key := completedInductiveTensor_directLimits_isEmbedding_false_key Jm _ _ hc hcoe ℓ κ
    hstep b
  rw [hqz, map_zero, hκ] at key
  have hne : (a : ULift.{u} ℕ → ℂ) (ULift.up m) ≠ 0 := by
    change (1 / 2 : ℂ) ^ m ≠ 0
    exact pow_ne_zero _ (by norm_num)
  exact hne key.symm

/-- Paper: Proposition C.2.3.13(2), p. 683. Take Xₙ to be the finitely supported
complex sequences with the ℓ² norm modulo the span of the first n coordinate
vectors, with the quotient maps as transitions. Take Y to be the single stage ℂ.
The X-limit and the target are zero. The completed stages are ℓ² modulo the same
coordinate spans, so the class of (2⁻ⁿ) in their limit is nonzero and maps to zero. -/
theorem Printed.completedInductiveTensor_directLimits_isEmbedding_false :
    ¬ Printed.completedInductiveTensor_directLimits_isEmbedding :=
  completedInductiveTensor_directLimits_isEmbedding_false_main

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
