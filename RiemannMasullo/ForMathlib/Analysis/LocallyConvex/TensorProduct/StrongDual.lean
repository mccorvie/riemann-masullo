module
public import RiemannMasullo.AppC_LCTVS.Sec3a
import Mathlib.Analysis.LocallyConvex.StrongTopology
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion

/-! # Strong duality for completed tensors with bounded rectangles -/

public section

open Filter Function Set Topology UniformSpace Bornology
open scoped TensorProduct
namespace RiemannMasullo
section KernelDuality
variable {X Y V : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
  [PolynormableSpace ℂ X] [T2Space X] [BarrelledSpace ℂ X]
  [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
  [PolynormableSpace ℂ Y] [T2Space Y]
  [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V]
  [PolynormableSpace ℂ V]

private theorem kernel_continuous_of_zero {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [AddCommGroup B] [Module ℂ B]
    [TopologicalSpace B] [IsTopologicalAddGroup B] (t : A →ₗ[ℂ] B) (h : ContinuousAt t 0) :
    Continuous t := continuous_of_continuousAt_zero t h

omit [T2Space X] [IsUniformAddGroup Y] [T2Space Y] in
/-- Separate continuity on a barrelled first factor gives continuity into the
space of operators with the topology of uniform convergence on bounded sets. -/
private theorem strongCurry_continuous (b : X →ₗ[ℂ] Y →L[ℂ] V)
    (hb : ∀ y, Continuous (fun x ↦ b x y)) : Continuous b := by
  apply continuous_of_continuousAt_zero b
  rw [ContinuousAt, map_zero, ContinuousLinearMap.nhds_zero_eq]
  simp only [tendsto_iInf, tendsto_principal]
  intro B hB U hU
  let M (y : B) : X →L[ℂ] V := ⟨((ContinuousLinearMap.applyₗ V (RingHom.id ℂ) y.val).toLinearMap.comp b), hb y.val⟩
  have heq := (PolynormableSpace.banach_steinhaus (𝓕 := M) fun x ↦
    (hB.image (b x)).subset (by rintro _ ⟨y, rfl⟩; exact ⟨y.val, y.property, rfl⟩)).equicontinuous 0
  have hbase := ((𝓝 (0 : V)).basis_sets.comap (fun x : V × V ↦ x.2 - x.1))
  rw [← uniformity_eq_comap_nhds_zero] at hbase
  filter_upwards [hbase.equicontinuousAt_iff_right.mp heq U hU] with x hx
  intro y hy
  have h := hx (⟨y, hy⟩ : B)
  change M ⟨y, hy⟩ x - M ⟨y, hy⟩ 0 ∈ U at h
  rwa [map_zero, sub_zero] at h

omit [IsUniformAddGroup X] [PolynormableSpace ℂ X] [BarrelledSpace ℂ X] [T2Space X]
  [IsUniformAddGroup Y] [PolynormableSpace ℂ Y] [T2Space Y] in
/-- The curried pullback from the strong dual is continuous: bounded
rectangles have bounded image under a continuous operator-valued map. -/
private theorem strongCurry_precomp (D : X →L[ℂ] (Y →L[ℂ] V)) :
    ∃ K : StrongDual ℂ V →L[ℂ] (X →L[ℂ] StrongDual ℂ Y),
      ∀ φ x y, K φ x y = φ (D x y) := by
  let P (φ : StrongDual ℂ V) := (φ.postcomp Y).comp D
  let L : StrongDual ℂ V →ₗ[ℂ] (X →L[ℂ] StrongDual ℂ Y) :=
    { toFun := P
      map_add' := fun _ _ ↦ ContinuousLinearMap.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl
      map_smul' := fun _ _ ↦ ContinuousLinearMap.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl }
  suffices hL : Continuous L from ⟨⟨L, hL⟩, fun _ _ _ ↦ rfl⟩
  refine kernel_continuous_of_zero (A := StrongDual ℂ V) (B := X →L[ℂ] StrongDual ℂ Y) L ?_
  rw [ContinuousAt, map_zero, ContinuousLinearMap.nhds_zero_eq (σ := RingHom.id ℂ) (E := X) (F := StrongDual ℂ Y)]
  simp only [tendsto_iInf, tendsto_principal]
  intro A hA U hU
  obtain ⟨⟨B,W⟩, ⟨hB,hW⟩, hBU⟩ := ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mp hU
  have hAB := ContinuousLinearMap.isVonNBounded_image2_apply (hA.image D) hB
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hAB hW] with φ hφ
  intro x hx
  apply hBU
  intro y hy
  exact hφ ⟨D x, ⟨x, hx, rfl⟩, y, hy, rfl⟩

omit [IsUniformAddGroup Y] in
/-- Evaluation on pure tensors gives the strong-dual-to-operators map. It is a
linear bijection without assuming any bounded-rectangle property. -/
private theorem strongCurry_inductiveTensor [UniformContinuousConstSMul ℂ (InductiveTensor X Y)] :
    ∃ K : StrongDual ℂ (Completion (InductiveTensor X Y)) →L[ℂ] (X →L[ℂ] StrongDual ℂ Y),
      Bijective K ∧ ∀ φ x y, K φ x y = φ (Completion.coe' (α := InductiveTensor X Y)
        (x ⊗ₜ[ℂ] y)) := by
  let W := InductiveTensor X Y
  let j : W →L[ℂ] Completion W := Completion.toComplL
  have hs := (continuous_inductiveTensor_iff (LinearMap.id : W →ₗ[ℂ] W)).mp continuous_id
  let b : X →ₗ[ℂ] (Y →L[ℂ] W) :=
    { toFun := fun x ↦ ⟨TensorProduct.mk ℂ X Y x, hs.1 x⟩
      map_add' := fun x x' ↦ ContinuousLinearMap.ext fun y ↦ TensorProduct.add_tmul _ _ y
      map_smul' := fun c x ↦ ContinuousLinearMap.ext fun y ↦ TensorProduct.smul_tmul' c x y }
  let D : X →L[ℂ] (Y →L[ℂ] W) := ⟨b, strongCurry_continuous b hs.2⟩
  let : PolynormableSpace ℂ (Completion W) := polynormableSpace_completion
  obtain ⟨K,hK⟩ := strongCurry_precomp ((j.postcomp Y).comp D)
  refine ⟨K, ⟨?_, ?_⟩, hK⟩
  · intro φ ψ he
    have hc : φ.comp j = ψ.comp j := by
      apply ContinuousLinearMap.coe_injective
      apply TensorProduct.ext'
      intro x y
      change φ (j (x ⊗ₜ[ℂ] y)) = ψ (j (x ⊗ₜ[ℂ] y))
      exact (hK φ x y).symm.trans ((congrArg (fun A : X →L[ℂ] StrongDual ℂ Y ↦ A x y) he).trans (hK ψ x y))
    exact DFunLike.coe_injective (Completion.denseRange_coe.equalizer φ.continuous ψ.continuous (congrArg DFunLike.coe hc))
  · intro A
    let T : W →ₗ[ℂ] ℂ := TensorProduct.lift ((ContinuousLinearMap.coeLM ℂ).comp A.toLinearMap)
    let L : W →L[ℂ] ℂ := ⟨T, (continuous_inductiveTensor_iff T).mpr ⟨fun x ↦ (A x).continuous,
      fun y ↦ (continuous_eval_const y).comp A.continuous⟩⟩
    refine ⟨L.fromCompletion, ContinuousLinearMap.ext fun x ↦ ContinuousLinearMap.ext fun y ↦ ?_⟩
    exact (hK _ x y).trans (L.fromCompletion_apply_coe (x ⊗ₜ[ℂ] y))

open scoped ComplexOrder in
/-- Bounded rectangles determining the bounded disks of the completed tensor
suffice for the inverse of currying to be strongly continuous. -/
private theorem strongCurry_equiv_of_bounded_rectangles [UniformContinuousConstSMul ℂ (InductiveTensor X Y)]
    (hB : ∀ B : Set (Completion (InductiveTensor X Y)), IsVonNBounded ℂ B →
      ∃ A : Set X, ∃ C : Set Y, IsVonNBounded ℂ A ∧ IsVonNBounded ℂ C ∧
        B ⊆ closure (absConvexHull ℂ (image2 (fun x y ↦ Completion.coe' (α := InductiveTensor X Y)
          (x ⊗ₜ[ℂ] y)) A C))) :
    ∃ L : (X →L[ℂ] StrongDual ℂ Y) ≃L[ℂ] StrongDual ℂ (Completion (InductiveTensor X Y)),
      ∀ T x y, L T (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) = T x y := by
  obtain ⟨K, hK, h⟩ := strongCurry_inductiveTensor (X := X) (Y := Y)
  let e := (LinearEquiv.ofBijective K.toLinearMap hK).symm
  have he (T : X →L[ℂ] StrongDual ℂ Y) : K (e T) = T := e.symm_apply_apply T
  have hval T x y := (h (e T) x y).symm.trans (congrArg (fun M : X →L[ℂ] StrongDual ℂ Y ↦ M x y) (he T))
  suffices hc : Continuous e from ⟨⟨e, hc, K.continuous⟩, hval⟩
  change Continuous e.toLinearMap
  refine kernel_continuous_of_zero (A := X →L[ℂ] StrongDual ℂ Y)
    (B := StrongDual ℂ (Completion (InductiveTensor X Y))) e.toLinearMap ?_
  rw [ContinuousAt, map_zero, ContinuousLinearMap.nhds_zero_eq_of_basis (E := Completion (InductiveTensor X Y))
    (σ := RingHom.id ℂ) Metric.nhds_basis_closedBall]
  simp only [tendsto_iInf, tendsto_principal]
  intro B hb r hr
  obtain ⟨A,C,hA,hC,hsub⟩ := hB B hb
  let ball := Metric.closedBall (0 : ℂ) r
  have hC0 : {φ : StrongDual ℂ Y | MapsTo φ C ball} ∈ 𝓝 0 :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo hC (Metric.closedBall_mem_nhds _ hr)
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA hC0] with T hT
  have hpre : AbsConvex ℂ (e T ⁻¹' ball) :=
    ⟨balanced_closedBall_zero.mulActionHom_preimage (e T).toLinearMap.toDistribMulActionHom.toMulActionHom,
      ((convex_RCLike_iff_convex_real (K := ℂ)).mpr (convex_closedBall (0 : ℂ) r)).linear_preimage (e T).toLinearMap⟩
  have hs : image2 (fun x y ↦ Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) A C ⊆ e T ⁻¹' ball := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    change e T _ ∈ ball
    rw [hval]
    exact hT hx hy
  exact hsub.trans (closure_minimal (absConvexHull_min hs hpre) (Metric.isClosed_closedBall.preimage (e T).continuous))

open scoped ComplexOrder in
/-- The projective-kernel identification follows by composing the nuclear
operator theorem with the strong dual form of currying. -/
theorem dualKernel_of_bounded_rectangles {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    [TopologicalSpace Z] [CompleteSpace X] [CompleteSpace (StrongDual ℂ X)]
    [CompleteSpace (StrongDual ℂ Y)] [PolynormableSpace ℂ (StrongDual ℂ Y)]
    [UniformContinuousConstSMul ℂ (InductiveTensor X Y)]
    [UniformContinuousConstSMul ℂ (ProjectiveTensor (StrongDual ℂ X) (StrongDual ℂ Y))]
    (hn : IsNuclearTVS (StrongDual ℂ X))
    (hB : ∀ B : Set (Completion (InductiveTensor X Y)), IsVonNBounded ℂ B →
      ∃ A : Set X, ∃ C : Set Y, IsVonNBounded ℂ A ∧ IsVonNBounded ℂ C ∧
        B ⊆ closure (absConvexHull ℂ (image2 (fun x y ↦ Completion.coe' (α := InductiveTensor X Y)
          (x ⊗ₜ[ℂ] y)) A C)))
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) :
    ∃ E : Completion (ProjectiveTensor (StrongDual ℂ X) (StrongDual ℂ Y)) ≃L[ℂ] StrongDual ℂ Z,
      ∀ (S : StrongDual ℂ X) (T : StrongDual ℂ Y) (x : X) (y : Y),
        E (Completion.coe' (α := ProjectiveTensor (StrongDual ℂ X) (StrongDual ℂ Y)) (S ⊗ₜ[ℂ] T))
          (e (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) = S x * T y := by
  obtain ⟨_, J, hJ⟩ := completedProjectiveTensorToOperators_equiv (F := StrongDual ℂ Y) hn
  obtain ⟨K, hK⟩ := strongCurry_equiv_of_bounded_rectangles hB
  let L := e.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  refine ⟨(J.trans K).trans L, fun S T x y ↦ ?_⟩
  let w : ProjectiveTensor (StrongDual ℂ X) (StrongDual ℂ Y) := S ⊗ₜ[ℂ] T
  let v := Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)
  change K (J (Completion.coe' w)) (e.symm (e v)) = _
  rw [e.symm_apply_apply, hJ]
  exact hK (projectiveTensorToOperators w) x y

end KernelDuality
end RiemannMasullo
