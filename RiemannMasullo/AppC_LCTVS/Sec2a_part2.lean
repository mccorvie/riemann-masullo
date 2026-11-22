module

public import RiemannMasullo.AppC_LCTVS.Sec2a
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.UniformSpace.Ascoli
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WeakSpace
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WithSeminorms
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.Pi
import RiemannMasullo.ForMathlib.LinearAlgebra.TensorProduct.DirectLimit
import RiemannMasullo.ForMathlib.Topology.Algebra.GroupCompletion

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
    tensorDualForm φ ψ (x ⊗ₜ[ℂ] y) = φ x * ψ y :=
  TensorProduct.dualDistrib_apply φ.toLinearMap ψ.toLinearMap x y

/-- Joint continuity forces the first variable to depend on finitely many evaluations. -/
private theorem tensorDualForm_finite_evaluations
    (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ)
    (hB : Continuous (fun p : WeakDual ℂ E × WeakDual ℂ F ↦ B p.1 p.2)) :
    ∃ s : Finset E, ∀ φ : WeakDual ℂ E, (∀ x ∈ s, φ x = 0) → B φ = 0 := by
  classical
  have hprod : {p : WeakDual ℂ E × WeakDual ℂ F | ‖B p.1 p.2‖ < 1} ∈
      𝓝 ((0 : WeakDual ℂ E), (0 : WeakDual ℂ F)) := by
    have hc := hB.continuousAt (x := ((0 : WeakDual ℂ E), (0 : WeakDual ℂ F)))
    have hzero : B (0 : WeakDual ℂ E) (0 : WeakDual ℂ F) = 0 := by simp
    have hb : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (B 0 0) := by
      rw [hzero]
      exact Metric.ball_mem_nhds 0 one_pos
    simpa only [Metric.ball, dist_zero_right, Set.preimage_ofPred_eq] using hc.preimage_mem_nhds hb
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hprod
  let p := (topDualPairing ℂ E).toSeminormFamily
  change U ∈ 𝓝 (0 : WeakBilin (topDualPairing ℂ E)) at hU
  obtain ⟨⟨s, r⟩, hr, hWU⟩ :=
    (topDualPairing ℂ E).weakBilin_withSeminorms.hasBasis_zero_ball.mem_iff.mp hU
  refine ⟨s, fun φ hφ ↦ LinearMap.ext fun ψ ↦ ?_⟩
  change B φ ψ = 0
  -- Scale the second variable into the neighborhood. The first can be scaled arbitrarily.
  have hsmul : Continuous (fun c : ℂ ↦ c • ψ) := continuous_id.smul continuous_const
  have hscaled : (fun c : ℂ ↦ c • ψ) ⁻¹' V ∈ 𝓝 (0 : ℂ) := by
    have hV' : V ∈ 𝓝 ((0 : ℂ) • ψ) := by rwa [zero_smul]
    exact (hsmul.continuousAt (x := 0)).preimage_mem_nhds hV'
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hscaled
  obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt ℂ hε
  have hcV : c • ψ ∈ V := hεV (mem_ball_zero_iff.mpr hcε)
  have hzero : B φ (c • ψ) = 0 := by
    by_contra hn
    let d : ℂ := (B φ (c • ψ))⁻¹
    have hdU : d • φ ∈ U := by
      apply hWU
      change (d • φ).toStrongDual ∈ (s.sup p).ball 0 r
      rw [Seminorm.mem_ball_zero]
      refine Seminorm.finset_sup_apply_lt hr fun x hx ↦ ?_
      change ‖(d • φ).toStrongDual x‖ < r
      simpa [hφ x hx] using hr
    have hnrm : ‖B (d • φ) (c • ψ)‖ < 1 :=
      hUV (show (d • φ, c • ψ) ∈ U ×ˢ V from ⟨hdU, hcV⟩)
    rw [show B (d • φ) = d • B φ from map_smul B d φ,
      LinearMap.smul_apply, smul_eq_mul] at hnrm
    change ‖(B φ (c • ψ))⁻¹ * B φ (c • ψ)‖ < 1 at hnrm
    rw [inv_mul_cancel₀ hn, norm_one] at hnrm
    exact lt_irrefl _ hnrm
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  exact (mul_eq_zero.mp (by simpa using hzero : c * B φ ψ = 0)).resolve_left hc0

/-- A jointly continuous weak-dual form is represented by a finite sum of pure tensors. -/
private theorem tensorDualForm_exists
    (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ)
    (hB : Continuous (fun p : WeakDual ℂ E × WeakDual ℂ F ↦ B p.1 p.2)) :
    ∃ z : E ⊗[ℂ] F, ∀ φ ψ, B φ ψ = tensorDualForm φ ψ z := by
  classical
  obtain ⟨s, hs⟩ := tensorDualForm_finite_evaluations B hB
  let a : WeakDual ℂ E →ₗ[ℂ] (s → ℂ) :=
    LinearMap.pi fun i : s ↦ (topDualPairing ℂ E).flip (i : E)
  have ha (φ : WeakDual ℂ E) (i : s) : a φ i = φ i := rfl
  have hker : a.ker ≤ B.ker := by
    intro φ hφ
    exact hs φ (fun x hx ↦ congrFun (LinearMap.mem_ker.mp hφ) ⟨x, hx⟩)
  obtain ⟨sectionMap, hsection⟩ :=
    a.rangeRestrict.exists_rightInverse_of_surjective a.range_rangeRestrict
  let project := a.range.subtype.leftInverse
  let liftEval := sectionMap.comp project
  have hlift (φ : WeakDual ℂ E) : a (liftEval (a φ)) = a φ := by
    have hp := LinearMap.leftInverse_apply_of_inj a.range.ker_subtype (a.rangeRestrict φ)
    have h := DFunLike.congr_fun hsection (a.rangeRestrict φ)
    change a.rangeRestrict (sectionMap (a.rangeRestrict φ)) = a.rangeRestrict φ at h
    change a (sectionMap (project (a φ))) = a φ
    rw [show project (a φ) = a.rangeRestrict φ from hp]
    exact congrArg Subtype.val h
  let b := Pi.basisFun ℂ s
  let φs (i : s) := liftEval (b i)
  have hslices (i : s) : Continuous (B (φs i)) :=
    hB.comp (continuous_const.prodMk continuous_id)
  choose y hy using fun i : s ↦
    (topDualPairing ℂ F).dualEmbedding_surjective
      (⟨B (φs i), hslices i⟩ : StrongDual ℂ (WeakDual ℂ F))
  have hy' (i : s) (ψ : WeakDual ℂ F) : B (φs i) ψ = ψ (y i) :=
    (DFunLike.congr_fun (hy i) ψ).symm
  refine ⟨∑ i : s, (i : E) ⊗ₜ[ℂ] y i, fun φ ψ ↦ ?_⟩
  have hsum : (∑ i : s, φ i • φs i) = liftEval (a φ) := by
    have hb := b.sum_repr (a φ)
    simp only [b, Pi.basisFun_repr, ha] at hb
    simpa only [map_sum, map_smul, RingHom.id_apply, φs] using congrArg liftEval hb
  have hφ : B φ = B (liftEval (a φ)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hker
    rw [LinearMap.mem_ker, map_sub, hlift, sub_self]
  change B φ ψ = tensorDualForm φ.toStrongDual ψ.toStrongDual _
  rw [hφ, ← hsum, map_sum, map_sum]
  simp [tensorDualForm_tmul, hy']

/-- Two tensors are equal if they agree on all pairs of continuous functionals. -/
private theorem tensorDualForm_ext [SeparatingDual ℂ E] [SeparatingDual ℂ F]
    {z w : E ⊗[ℂ] F} (h : ∀ φ ψ, tensorDualForm φ ψ z = tensorDualForm φ ψ w) : z = w := by
  classical
  let b := Module.Free.chooseBasis ℂ F
  let e := TensorProduct.equivFinsuppOfBasisRight (M := E) b
  have hcontract (φ : StrongDual ℂ E) :
      (TensorProduct.lid ℂ F) (TensorProduct.map φ.toLinearMap LinearMap.id z) =
      (TensorProduct.lid ℂ F) (TensorProduct.map φ.toLinearMap LinearMap.id w) := by
    let L := (TensorProduct.lid ℂ F).toLinearMap.comp
      (TensorProduct.map φ.toLinearMap LinearMap.id)
    change L z = L w
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro ψ
    have hL : ψ.toLinearMap.comp L = tensorDualForm φ ψ := by
      apply TensorProduct.ext'
      intro x y
      simp [L, tensorDualForm_tmul]
    exact (DFunLike.congr_fun hL z).trans ((h φ ψ).trans (DFunLike.congr_fun hL w).symm)
  apply e.injective
  ext i
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  let L := (TensorProduct.lid ℂ F).toLinearMap.comp
    (TensorProduct.map φ.toLinearMap LinearMap.id)
  let coord : (E ⊗[ℂ] F) →ₗ[ℂ] E := (Finsupp.lapply i).comp e.toLinearMap
  have hL : φ.toLinearMap.comp coord = (b.coord i).comp L := by
    apply TensorProduct.ext'
    intro x y
    simp [coord, e, L, Module.Basis.coord_apply, mul_comm]
  exact (DFunLike.congr_fun hL z).trans
    ((congrArg (b.coord i) (hcontract φ)).trans (DFunLike.congr_fun hL w).symm)

variable [hE : PolynormableSpace ℂ E] [sE : T2Space E]
  [hF : PolynormableSpace ℂ F] [sF : T2Space F]

include hE sE hF sF in
/-- Paper: (C.2.3.1), p. 676. Jointly continuous bilinear forms on the two weak duals
are exactly the forms represented by a unique algebraic tensor. -/
theorem tensorDualForm_represents_iff (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ) :
    Continuous (fun p : WeakDual ℂ E × WeakDual ℂ F ↦ B p.1 p.2) ↔
      ∃! z : E ⊗[ℂ] F, ∀ φ ψ, B φ ψ = tensorDualForm φ ψ z := by
  constructor
  · intro hB
    let := polynormableSpace_separatingDual ℂ E
    let := polynormableSpace_separatingDual ℂ F
    obtain ⟨z, hz⟩ := tensorDualForm_exists B hB
    exact ⟨z, hz, fun w hw ↦ tensorDualForm_ext fun φ ψ ↦ (hw φ ψ).symm.trans (hz φ ψ)⟩
  · rintro ⟨z, hz, huniq⟩
    have heq : (fun p : WeakDual ℂ E × WeakDual ℂ F ↦ B p.1 p.2) =
        fun p ↦ tensorDualForm p.1.toStrongDual p.2.toStrongDual z :=
      funext fun p ↦ hz p.1 p.2
    rw [heq]
    clear heq hz huniq
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [tensorDualForm_tmul]
        exact ((WeakDual.eval_continuous x).comp continuous_fst).mul
          ((WeakDual.eval_continuous y).comp continuous_snd)
    | add z w hz hw =>
        simp only [map_add]
        exact hz.add hw

/-- A family that contains a superset of each test set induces a finer polar topology. -/
private theorem polarTopology_le_of_cofinal {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {S T : Set (Set X)}
    (h : ∀ A ∈ T, ∃ D ∈ S, A ⊆ D) :
    polarTopology (topDualPairing ℂ X) S ≤ polarTopology (topDualPairing ℂ X) T := by
  have hc := (UniformOnFun.uniformContinuous_ofFun_toFun (β := ℂ) T S fun A hA ↦ by
    obtain ⟨D, hD, hAD⟩ := h A hA
    exact ⟨{D}, singleton_subset_iff.mpr hD, finite_singleton D, by simpa using hAD⟩).continuous
  let : TopologicalSpace (StrongDual ℂ X) := polarTopology (topDualPairing ℂ X) S
  have hi : Continuous (fun f : StrongDual ℂ X ↦ UniformOnFun.ofFun S (fun x ↦ f x)) :=
    continuous_induced_dom
  exact (hc.comp hi).le_induced

/-- Paper: Remark C.2.3.1, p. 676. If closed bounded sets are compact, the Mackey
topology on the dual is the topology of precompact convergence. -/
theorem mackeyDual_eq_precompact {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [PolynormableSpace ℂ X] [T2Space X]
    (h : ∀ A : Set X, IsClosed A → IsVonNBounded ℂ A → IsCompact A) :
    mackeyTopology (topDualPairing ℂ X) =
      polarTopology (topDualPairing ℂ X) {A | TotallyBounded A} := by
  let : SeparatingDual ℂ X := polynormableSpace_separatingDual ℂ X
  let : Module ℝ X := Module.restrictScalars ℝ ℂ X
  let : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  refine le_antisymm (polarTopology_le_of_cofinal ?_) (polarTopology_le_of_cofinal ?_)
  · intro A hA
    change TotallyBounded A at hA
    let D := closedAbsConvexHull ℂ A
    have hD : AbsConvex ℂ D := absConvex_convexClosedHull
    have hb : IsVonNBounded ℂ D := by
      let hp := PolynormableSpace.withSeminorms ℂ X
      refine hp.isVonNBounded_iff_seminorm_bddAbove.mpr fun p ↦ ?_
      obtain ⟨r, hr⟩ := hp.isVonNBounded_iff_seminorm_bddAbove.mp (hA.isVonNBounded ℂ) p
      have hsub : D ⊆ p.val.closedBall 0 r := by
        refine closedAbsConvexHull_min (fun x hx ↦ p.val.mem_closedBall_zero.mpr ?_)
          ⟨p.val.balanced_closedBall_zero r, convex_RCLike_iff_convex_real.mpr
            (p.val.convex_closedBall 0 r)⟩ ?_
        · exact hr (mem_image_of_mem _ hx)
        · rw [Seminorm.closedBall_zero_eq]
          exact isClosed_le p.property continuous_const
      refine ⟨r, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact p.val.mem_closedBall_zero.mp (hsub hx)
    have hcompact := (h D isClosed_closedAbsConvexHull hb).image (toWeakSpaceCLM ℂ X).continuous
    exact ⟨D, ⟨hD, image_id D ▸ hcompact⟩, subset_closedAbsConvexHull⟩
  · intro A hA
    obtain ⟨_, hcompact⟩ := hA
    change IsCompact (X := WeakSpace ℂ X) A at hcompact
    have hclosed : IsClosed A := hcompact.isClosed.preimage (toWeakSpaceCLM ℂ X).continuous
    have hbounded : IsVonNBounded ℂ A := by
      apply isVonNBounded_of_dual_bounded
      intro f
      exact (NormedSpace.image_isVonNBounded_iff ℂ).mp
        ((hcompact.isVonNBounded ℂ).image (WeakBilin.eval (topDualPairing ℂ X).flip f))
    exact ⟨A, (h A hclosed hbounded).totallyBounded, Subset.rfl⟩

-- TODO(later): needs §C.2.4 for the nuclear Montel assertion of Remark C.2.3.1.
-- TODO(later): needs §D.1 for its adelic Schwartz–Bruhat space examples.

omit sF in
/-- A continuous seminorm is attained in absolute value by evaluations on an absolutely
convex, weak-star compact set of continuous linear functionals. -/
private theorem exists_mackey_test_set
    (p : Seminorm ℂ F) (hp : Continuous p) :
    ∃ D : Set (WeakDual ℂ F), AbsConvex ℂ D ∧ IsCompact D ∧
      ∀ y : F, ∃ ψ ∈ D, ‖ψ y‖ = p y := by
  -- Use the seminorm on a copy of F while keeping the original topology on F.
  let e : ULift.{0} F ≃ₗ[ℂ] F := ULift.moduleEquiv
  let q := p.comp e.toLinearMap
  let : SeminormedAddCommGroup (ULift.{0} F) := q.toSeminormedAddCommGroup
  let : TopologicalSpace (ULift.{0} F) :=
    q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let : NormedSpace ℂ (ULift.{0} F) := ⟨fun c x ↦ (map_smul_eq_mul q c x).le⟩
  let : IsTopologicalAddGroup F := PolynormableSpace.isTopologicalAddGroup ℂ F
  have he : Continuous e.symm := by
    refine (Metric.continuous_iff' (f := fun y : F ↦ e.symm y)).mpr fun y ε hε ↦ ?_
    have hc : Continuous (fun x : F ↦ p (x - y)) :=
      hp.comp (continuous_id.sub continuous_const)
    have hsmall := hc.continuousAt (x := y).eventually_lt continuousAt_const
      (show p (y - y) < ε by simpa)
    filter_upwards [hsmall] with x hx
    rw [dist_eq_norm, ← map_sub]
    change p (e (e.symm (x - y))) < ε
    rwa [e.apply_symm_apply]
  let pull : WeakDual ℂ (ULift.{0} F) →ₗ[ℂ] WeakDual ℂ F :=
    (ContinuousLinearMap.precomp ℂ (⟨e.symm.toLinearMap, he⟩ : F →L[ℂ] ULift.{0} F)).toLinearMap
  have hpull : Continuous pull :=
    WeakDual.continuous_of_continuous_eval fun y ↦ WeakDual.eval_continuous (e.symm y)
  let D₀ : Set (WeakDual ℂ (ULift.{0} F)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
  have hD₀ : AbsConvex ℂ D₀ := by
    change AbsConvex ℂ (Metric.closedBall (0 : StrongDual ℂ (ULift.{0} F)) 1)
    exact ⟨balanced_closedBall_zero,
      convex_RCLike_iff_convex_real.mpr (convex_closedBall _ _)⟩
  have hcompact : IsCompact D₀ := WeakDual.isCompact_closedBall (0 : StrongDual ℂ (ULift.{0} F)) 1
  refine ⟨pull '' D₀, ⟨hD₀.1.image pull, hD₀.2.linear_image pull⟩, hcompact.image hpull, fun y ↦ ?_⟩
  obtain ⟨g, hg, hgy⟩ := exists_dual_vector'' ℂ (e.symm y)
  refine ⟨pull g.toWeakDual, ⟨g.toWeakDual, ?_, rfl⟩, ?_⟩
  · change g ∈ Metric.closedBall 0 1
    simpa only [mem_closedBall_zero_iff] using hg
  · change ‖g (e.symm y)‖ = p y
    rw [hgy]
    change ‖((‖e.symm y‖ : ℝ) : ℂ)‖ = p y
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    change p (e (e.symm y)) = p y
    rw [e.apply_symm_apply]

omit hE sE sF in
/-- A linear map with a weakly continuous transpose is continuous from the Mackey dual. -/
private theorem continuous_mackeyDual_of_transpose
    (T : StrongDual ℂ E →ₗ[ℂ] F) (S : WeakDual ℂ F →ₗ[ℂ] E)
    (hS : @Continuous (WeakDual ℂ F) (WeakSpace ℂ E) _ _ S)
    (hST : ∀ (φ : StrongDual ℂ E) (ψ : WeakDual ℂ F), φ (S ψ) = ψ (T φ)) :
    @Continuous _ _ (mackeyTopology (topDualPairing ℂ E)) _ T := by
  let K : Set (Set E) := {A | AbsConvex ℂ A ∧ IsCompact (X := WeakSpace ℂ E) A}
  let ev (φ : StrongDual ℂ E) := UniformOnFun.ofFun K φ
  let : TopologicalSpace (StrongDual ℂ E) := mackeyTopology (topDualPairing ℂ E)
  let : IsTopologicalAddGroup F := PolynormableSpace.isTopologicalAddGroup ℂ F
  refine continuous_iff_continuousAt.mpr fun φ₀ ↦ ?_
  suffices h : Tendsto (fun φ ↦ T φ - T φ₀) (𝓝 φ₀) (𝓝 0) by
    simpa [ContinuousAt] using h.add_const (T φ₀)
  refine (PolynormableSpace.hasBasis_zero_ball ℂ F).tendsto_right_iff.mpr fun p hp ↦ ?_
  obtain ⟨D, hD, hcompact, hnorm⟩ := exists_mackey_test_set p hp
  have hKD : S '' D ∈ K := ⟨⟨hD.1.image S, hD.2.linear_image S⟩, hcompact.image hS⟩
  have hev : Continuous ev := continuous_induced_dom
  have hnear := UniformOnFun.gen_mem_nhds ℂ K (ev φ₀) hKD
    (Metric.uniformity_basis_dist.mem_iff.mpr ⟨1, one_pos, Subset.rfl⟩)
  filter_upwards [hev.continuousAt.preimage_mem_nhds hnear] with φ hφ
  obtain ⟨ψ, hψ, hEq⟩ := hnorm (T φ - T φ₀)
  have hlt : dist (φ₀ (S ψ)) (φ (S ψ)) < 1 := hφ (S ψ) (mem_image_of_mem S hψ)
  rw [dist_comm, dist_eq_norm] at hlt
  change ‖(φ - φ₀) (S ψ)‖ < 1 at hlt
  rw [hST (φ - φ₀) ψ, map_sub T, hEq] at hlt
  rwa [Seminorm.mem_ball_zero]

omit hE sE in
open scoped Pointwise in
/-- A Mackey-continuous scalar functional on the dual is evaluation at a primal vector. -/
private theorem exists_mackeyDual_eval (l : StrongDual ℂ E →ₗ[ℂ] ℂ)
    (hl : @Continuous _ _ (mackeyTopology (topDualPairing ℂ E)) _ l) :
    ∃ x : E, ∀ φ : StrongDual ℂ E, l φ = φ x := by
  let K : Set (Set E) := {A | AbsConvex ℂ A ∧ IsCompact (X := WeakSpace ℂ E) A}
  have hzero : ({0} : Set E) ∈ K :=
    ⟨⟨balanced_zero, convex_singleton _⟩, isCompact_singleton⟩
  have hdir : DirectedOn (· ⊆ ·) K := by
    intro A hA D hD
    rcases A.eq_empty_or_nonempty with rfl | hAn
    · exact ⟨D, hD, empty_subset _, Subset.rfl⟩
    rcases D.eq_empty_or_nonempty with rfl | hDn
    · exact ⟨A, hA, Subset.rfl, empty_subset _⟩
    refine ⟨A + D, ⟨⟨hA.1.1.add hD.1.1, hA.1.2.add hD.1.2⟩, hA.2.add hD.2⟩, ?_, ?_⟩
    · intro x hx
      simpa only [add_zero] using add_mem_add hx (hD.1.1.zero_mem hDn)
    · intro x hx
      simpa only [zero_add] using add_mem_add (hA.1.1.zero_mem hAn) hx
  let : TopologicalSpace (StrongDual ℂ E) := mackeyTopology (topDualPairing ℂ E)
  let ev (φ : StrongDual ℂ E) := UniformOnFun.ofFun K φ
  have hn : {φ : StrongDual ℂ E | ‖l φ‖ < 1} ∈ 𝓝 0 := by
    simpa only [map_zero, Metric.ball, dist_zero_right, Set.preimage_ofPred_eq] using
      hl.continuousAt (x := 0).preimage_mem_nhds (Metric.ball_mem_nhds (l 0) one_pos)
  change _ ∈ @nhds _ (TopologicalSpace.induced ev inferInstance) 0 at hn
  rw [nhds_induced] at hn
  obtain ⟨⟨A, ε⟩, ⟨hA, hε⟩, hbound⟩ :=
    ((UniformOnFun.hasBasis_nhds_of_basis E ℂ K (ev 0) ⟨{0}, hzero⟩ hdir
      Metric.uniformity_basis_dist).comap ev).mem_iff.mp hn
  obtain ⟨D, hD, hAD, h0D⟩ := hdir A hA {0} hzero
  have hb (φ : StrongDual ℂ E) (hφ : ∀ x ∈ D, ‖φ x‖ < ε) : ‖l φ‖ < 1 := by
    apply hbound
    intro x hx
    change dist (φ x) (0 : ℂ) < ε
    simpa only [dist_zero_right] using hφ x (hAD hx)
  -- Separate the scaled functional from the image of the compact disk in the algebraic dual.
  let P := (Module.Dual.eval ℂ (StrongDual ℂ E)).flip
  let j := (topDualPairing ℂ E).flip
  have hj : @Continuous (WeakSpace ℂ E) (WeakBilin P) _ _ j :=
    WeakBilin.continuous_of_continuous_eval P fun φ ↦
      WeakBilin.eval_continuous (topDualPairing ℂ E).flip φ
  let : T2Space (WeakBilin P) := (WeakBilin.isEmbedding (B := P)
    (fun _ _ h ↦ LinearMap.ext fun φ ↦ DFunLike.congr_fun h φ)).t2Space
  let : Module ℝ (WeakBilin P) := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ (WeakBilin P) := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ (WeakBilin P) := P.weakBilin_withSeminorms.toLocallyConvexSpace
  let scaled : WeakBilin P := (ε : ℂ) • l
  have hmem : scaled ∈ j '' D := by
    by_contra hnmem
    obtain ⟨g, r, hgr, hrl⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) (E := WeakBilin P)
      (convex_RCLike_iff_convex_real.mp (hD.1.2.linear_image j))
      (hD.2.image hj).isClosed hnmem
    obtain ⟨φ, rfl⟩ := P.dualEmbedding_surjective g
    have hnorm (x : E) (hx : x ∈ D) : ‖φ x‖ < r := by
      obtain ⟨c, hc, hcφ⟩ := RCLike.exists_norm_eq_mul_self (φ x)
      have hcx := hgr (j (c • x))
        (mem_image_of_mem j (hD.1.1 c hc.le (smul_mem_smul_set hx)))
      change (φ (c • x)).re < r at hcx
      rw [map_smul, smul_eq_mul, ← hcφ] at hcx
      change (((‖φ x‖ : ℝ) : ℂ)).re < r at hcx
      rwa [Complex.ofReal_re] at hcx
    have hr : 0 < r := by simpa using hnorm 0 (h0D (mem_singleton 0))
    change r < ((ε : ℂ) * l φ).re at hrl
    rw [Complex.re_ofReal_mul] at hrl
    have hlt : r < ε * ‖l φ‖ :=
      hrl.trans_le (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hε.le)
    have hφ : l φ ≠ 0 := by
      intro he
      simp [he, hr.not_gt] at hlt
    have hbad := hb ((l φ)⁻¹ • φ) fun x hx ↦ by
      change ‖(l φ)⁻¹ * φ x‖ < ε
      rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.mpr hφ)]
      exact (hnorm x hx).trans hlt
    simp [map_smul, smul_eq_mul, hφ] at hbad
  obtain ⟨x, _, hx⟩ := hmem
  refine ⟨(ε : ℂ)⁻¹ • x, fun φ ↦ ?_⟩
  have hxφ : φ x = (ε : ℂ) * l φ := DFunLike.congr_fun hx φ
  have hε₀ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  rw [map_smul, smul_eq_mul, hxφ, inv_mul_cancel_left₀ hε₀]

omit hE sE hF sF in
/-- A family of continuous weak-dual slices of a bilinear form gives a linear map
into the primal space by weak dual representation. -/
private theorem exists_weakDual_slice_operator [SeparatingDual ℂ F]
    (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ) (hB : ∀ φ, Continuous (B φ)) :
    ∃ T : StrongDual ℂ E →ₗ[ℂ] F, ∀ φ ψ, B φ ψ = ψ (T φ) := by
  have hsep : (topDualPairing ℂ F).SeparatingRight :=
    fun x h ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
      fun ψ ↦ (h ψ).trans (map_zero ψ).symm
  let repr := (topDualPairing ℂ F).rightDualEquiv hsep
  let slices : StrongDual ℂ E →ₗ[ℂ] StrongDual ℂ (WeakDual ℂ F) :=
    { toFun := fun φ ↦ ⟨B φ, hB φ⟩
      map_add' := fun φ φ' ↦ ContinuousLinearMap.ext fun ψ ↦
        DFunLike.congr_fun (map_add B φ.toWeakDual φ'.toWeakDual) ψ
      map_smul' := fun c φ ↦ ContinuousLinearMap.ext fun ψ ↦
        DFunLike.congr_fun (map_smul B c φ.toWeakDual) ψ }
  refine ⟨repr.symm.toLinearMap.comp slices, fun φ ψ ↦ ?_⟩
  exact (DFunLike.congr_fun (repr.apply_symm_apply (slices φ)) ψ).symm

include hE sE hF sF in
/-- Paper: (C.2.3.3), p. 676. A separately continuous bilinear form on the weak duals
corresponds to a unique continuous operator from the Mackey dual to F, by evaluation. -/
theorem mackeyDual_represents_separatelyContinuous
    (B : WeakDual ℂ E →ₗ[ℂ] WeakDual ℂ F →ₗ[ℂ] ℂ) :
    (∀ φ, Continuous (B φ)) ∧ (∀ ψ, Continuous (B.flip ψ)) ↔
      ∃! T : StrongDual ℂ E →ₗ[ℂ] F,
        @Continuous _ _ (mackeyTopology (topDualPairing ℂ E)) _ T ∧
        ∀ φ ψ, B φ ψ = ψ (T φ) := by
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let : SeparatingDual ℂ F := polynormableSpace_separatingDual ℂ F
  constructor
  · rintro ⟨hB, hflip⟩
    obtain ⟨T, hT⟩ := exists_weakDual_slice_operator B hB
    obtain ⟨S, hS⟩ := exists_weakDual_slice_operator B.flip hflip
    have hST (φ : StrongDual ℂ E) (ψ : WeakDual ℂ F) : φ (S ψ) = ψ (T φ) :=
      (hS ψ φ).symm.trans (hT φ ψ)
    have hSw : @Continuous (WeakDual ℂ F) (WeakSpace ℂ E) _ _ S := by
      refine WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ E).flip fun φ ↦ ?_
      change Continuous (fun ψ : WeakDual ℂ F ↦ φ (S ψ))
      simpa only [hST] using WeakDual.eval_continuous (𝕜 := ℂ) (E := F) (T φ)
    refine ⟨T, ⟨continuous_mackeyDual_of_transpose T S hSw hST, hT⟩, ?_⟩
    rintro T' ⟨_, hT'⟩
    exact LinearMap.ext fun φ ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
      fun ψ ↦ (hT' φ ψ).symm.trans (hT φ ψ)
  · rintro ⟨T, ⟨hT, hB⟩, _⟩
    refine ⟨fun φ ↦ ?_, fun ψ ↦ ?_⟩
    · change Continuous (fun ψ : WeakDual ℂ F ↦ B φ ψ)
      simpa only [hB] using WeakDual.eval_continuous (𝕜 := ℂ) (E := F) (T φ)
    · let l := ψ.toStrongDual.toLinearMap.comp T
      have hslice : @Continuous _ _ (mackeyTopology (topDualPairing ℂ E)) _ l := by
        let : TopologicalSpace (StrongDual ℂ E) := mackeyTopology (topDualPairing ℂ E)
        exact ψ.toStrongDual.continuous.comp hT
      obtain ⟨x, hx⟩ := exists_mackeyDual_eval l hslice
      have heq : (fun φ : WeakDual ℂ E ↦ B.flip ψ φ) = fun φ ↦ φ x :=
        funext fun φ ↦ (hB φ ψ).trans (hx φ.toStrongDual)
      change Continuous (fun φ : WeakDual ℂ E ↦ B.flip ψ φ)
      rw [heq]
      exact WeakDual.eval_continuous (𝕜 := ℂ) (E := E) x

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

open scoped Pointwise in
include hE hF in
omit sE sF in
/-- Paper: (C.2.3.7), p. 677. The generating injective seminorm bounds each
evaluation against a pair of functionals in the two polars. -/
private theorem norm_tensorDualForm_le_injectiveTensorSeminorm
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0})
    (φ : StrongDual.polar ℂ U.val) (ψ : StrongDual.polar ℂ V.val) (z : E ⊗[ℂ] F) :
    ‖tensorDualForm φ.val ψ.val z‖ ≤ injectiveTensorSeminorm U V z := by
  let D := StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val
  let p (f : D) := (normSeminorm ℂ ℂ).comp (tensorDualForm f.1.val f.2.val)
  have hb : BddAbove (range p) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
        obtain ⟨a, x', hx', rfl⟩ : ∃ a : ℂ, x ∈ a • U.val :=
          by simpa using (absorbent_nhds_zero (𝕜 := ℂ) U.property x).exists
        obtain ⟨b, y', hy', rfl⟩ : ∃ b : ℂ, y ∈ b • V.val :=
          by simpa using (absorbent_nhds_zero (𝕜 := ℂ) V.property y).exists
        refine ⟨‖a‖ * ‖b‖, forall_mem_range.mpr fun f ↦ ?_⟩
        have hφ := (StrongDual.mem_polar_iff ℂ _).mp f.1.property x' hx'
        have hψ := (StrongDual.mem_polar_iff ℂ _).mp f.2.property y' hy'
        change ‖tensorDualForm f.1.val f.2.val ((a • x') ⊗ₜ[ℂ] (b • y'))‖ ≤ _
        rw [tensorDualForm_tmul, norm_mul, map_smul, map_smul, norm_smul, norm_smul]
        exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) hφ)
          (mul_le_of_le_one_right (norm_nonneg _) hψ)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    | add w₁ w₂ h₁ h₂ =>
        obtain ⟨C₁, h₁⟩ := h₁
        obtain ⟨C₂, h₂⟩ := h₂
        exact ⟨C₁ + C₂, forall_mem_range.mpr fun f ↦
          (map_add_le_add (p f) w₁ w₂).trans
            (add_le_add (h₁ (mem_range_self f)) (h₂ (mem_range_self f)))⟩
  unfold injectiveTensorSeminorm
  rw [← ciSup_prod hb]
  exact le_ciSup hb (φ, ψ) z

include hE sE hF sF in
/-- Paper: (C.2.3.4), p. 676. The injective tensor topology is Hausdorff. -/
@[instance]
theorem injectiveTensor_t2 : T2Space (InjectiveTensor E F) := by
  classical
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let : SeparatingDual ℂ F := polynormableSpace_separatingDual ℂ F
  have hT1 : T1Space (InjectiveTensor E F) :=
    (withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).T1_of_separating fun z hz ↦ by
      change E ⊗[ℂ] F at z
      by_contra! h
      apply hz
      apply tensorDualForm_ext
      intro φ ψ
      let U : {U : Set E // U ∈ 𝓝 0} :=
        ⟨φ ⁻¹' Metric.closedBall 0 1, φ.continuous.continuousAt.preimage_mem_nhds
          (by simpa using Metric.closedBall_mem_nhds (φ 0) one_pos)⟩
      let V : {V : Set F // V ∈ 𝓝 0} :=
        ⟨ψ ⁻¹' Metric.closedBall 0 1, ψ.continuous.continuousAt.preimage_mem_nhds
          (by simpa using Metric.closedBall_mem_nhds (ψ 0) one_pos)⟩
      have hφ : φ ∈ StrongDual.polar ℂ U.val :=
        (StrongDual.mem_polar_iff ℂ _).mpr fun _ hx ↦ mem_closedBall_zero_iff.mp hx
      have hψ : ψ ∈ StrongDual.polar ℂ V.val :=
        (StrongDual.mem_polar_iff ℂ _).mpr fun _ hy ↦ mem_closedBall_zero_iff.mp hy
      have hle := norm_tensorDualForm_le_injectiveTensorSeminorm U V ⟨φ, hφ⟩ ⟨ψ, hψ⟩ z
      exact (norm_le_zero_iff.mp (hle.trans_eq (h (U, V)))).trans
        (map_zero (tensorDualForm φ ψ)).symm
  infer_instance

/-- The weak-dual polar of a zero-neighborhood is a member of the compactology. -/
private theorem weakDual_polar_mem_compactology {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [ContinuousConstSMul ℂ X] {U : Set X} (hU : U ∈ 𝓝 0) :
    WeakDual.polar ℂ U ∈ equicontinuousCompactology X := by
  let B : X →ₗ[ℂ] WeakDual ℂ X →ₗ[ℂ] ℂ :=
    (topDualPairing ℂ X).flip.compl₂ WeakDual.toStrongDual.toLinearMap
  refine ⟨?_, LinearMap.polar_AbsConvex (B := B) U, WeakDual.isClosed_polar _ _⟩
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let c : ℂ := (ε / 2 : ℝ)
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast (half_pos hε).ne'
  have hnear : (fun x : X ↦ c⁻¹ • x) ⁻¹' U ∈ 𝓝 (0 : X) := by
    apply (continuous_const_smul c⁻¹).continuousAt.preimage_mem_nhds
    simpa only [smul_zero] using hU
  filter_upwards [hnear] with x hx φ
  have hφ : ‖φ.val (c⁻¹ • x)‖ ≤ 1 := φ.property _ hx
  have hx' : x = c • (c⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [map_zero, dist_zero_left, hx', map_smul, norm_smul]
  have hnorm : ‖c‖ = ε / 2 := by
    dsimp only [c]
    rw [Complex.norm_real, Real.norm_of_nonneg (half_pos hε).le]
  exact (mul_le_of_le_one_right (norm_nonneg _) hφ).trans_lt (hnorm ▸ half_lt_self hε)

/-- Each member of the compactology is contained in the polar of a zero-neighborhood. -/
private theorem subset_polar_of_mem_compactology {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {A : Set (WeakDual ℂ X)} (hA : A ∈ equicontinuousCompactology X) :
    ∃ U : {U : Set X // U ∈ 𝓝 0}, A ⊆ WeakDual.polar ℂ U.val := by
  have hnear := Metric.equicontinuousAt_iff_right.mp hA.1 1 one_pos
  refine ⟨⟨_, hnear⟩, fun φ hφ x hx ↦ ?_⟩
  have h := hx (⟨φ, hφ⟩ : A)
  change ‖φ x‖ ≤ 1
  simpa only [map_zero, dist_zero_left] using h.le

include hE sE hF sF in
/-- Paper: (C.2.3.4), p. 676. Evaluation realizes the injective topology as uniform
convergence on products from the equicontinuous compactologies. -/
theorem injectiveTensor_isEmbedding_dualForms :
    let S := image2 Set.prod (equicontinuousCompactology E) (equicontinuousCompactology F)
    IsEmbedding (fun z : InjectiveTensor E F ↦ UniformOnFun.ofFun S
      (fun v : WeakDual ℂ E × WeakDual ℂ F ↦ tensorDualForm v.1 v.2 z)) := by
  classical
  let D := WeakDual ℂ E × WeakDual ℂ F
  let S := image2 Set.prod (equicontinuousCompactology E) (equicontinuousCompactology F)
  let T : InjectiveTensor E F →+ (D →ᵤ[S] ℂ) :=
    { toFun := fun z ↦ UniformOnFun.ofFun S (fun v ↦ tensorDualForm v.1 v.2 z)
      map_zero' := funext fun v ↦ map_zero (tensorDualForm v.1 v.2)
      map_add' := fun z w ↦ funext fun v ↦ map_add (tensorDualForm v.1 v.2) z w }
  change IsEmbedding T
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let : SeparatingDual ℂ F := polynormableSpace_separatingDual ℂ F
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_, ?_⟩
  swap
  · intro z w h
    exact tensorDualForm_ext fun φ ψ ↦ congrFun h (φ.toWeakDual, ψ.toWeakDual)
  let p₀ (UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0}) :=
    injectiveTensorSeminorm UV.1 UV.2
  let p : SeminormFamily ℂ (InjectiveTensor E F) _ := p₀
  have hp : WithSeminorms p := withGeneratingSeminorms_spec (E ⊗[ℂ] F) p₀
  refine le_antisymm ?_ ?_
  · rw [UniformOnFun.nhds_eq_of_basis ℂ S Metric.uniformity_basis_dist (0 : D →ᵤ[S] ℂ)]
    simp only [Filter.comap_iInf, Filter.comap_principal, le_iInf_iff, Filter.le_principal_iff]
    rintro _ ⟨A, hA, B, hB, rfl⟩ r hr
    obtain ⟨U, hU⟩ := subset_polar_of_mem_compactology hA
    obtain ⟨V, hV⟩ := subset_polar_of_mem_compactology hB
    refine Filter.mem_of_superset ((p (U, V)).ball_mem_nhds (hp.continuous_seminorm _) hr)
      (fun z hz v hv ↦ ?_)
    change dist (0 : ℂ) (tensorDualForm v.1 v.2 z) < r
    rw [dist_zero_left]
    exact (norm_tensorDualForm_le_injectiveTensorSeminorm U V
      ⟨v.1.toStrongDual, hU hv.1⟩ ⟨v.2.toStrongDual, hV hv.2⟩ z).trans_lt
        ((p (U, V)).mem_ball_zero.mp hz)
  · rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    refine le_iInf fun ⟨U, V⟩ ↦ ?_
    refine ((Metric.nhds_basis_ball (x := (0 : ℝ))).comap (p (U, V))).ge_iff.mpr fun r hr ↦ ?_
    have hS : WeakDual.polar ℂ U.val ×ˢ WeakDual.polar ℂ V.val ∈ S :=
      ⟨_, weakDual_polar_mem_compactology U.property, _,
        weakDual_polar_mem_compactology V.property, rfl⟩
    have hnear := UniformOnFun.gen_mem_nhds ℂ S (0 : D →ᵤ[S] ℂ) hS
      (Metric.uniformity_basis_dist.mem_of_mem (half_pos hr))
    refine Filter.mem_comap.mpr ⟨_, hnear, fun z hz ↦ ?_⟩
    change E ⊗[ℂ] F at z
    let P := StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val
    let q (v : P) := (normSeminorm ℂ ℂ).comp (tensorDualForm v.1.val v.2.val)
    have hq : BddAbove (range q) := ⟨p₀ (U, V), forall_mem_range.mpr fun v z ↦
      norm_tensorDualForm_le_injectiveTensorSeminorm U V v.1 v.2 z⟩
    let : Nonempty P := ⟨⟨⟨0, StrongDual.zero_mem_polar _ _⟩, ⟨0, StrongDual.zero_mem_polar _ _⟩⟩⟩
    have hle : p₀ (U, V) z ≤ r / 2 := by
      change injectiveTensorSeminorm U V z ≤ r / 2
      rw [injectiveTensorSeminorm, ← ciSup_prod hq, Seminorm.iSup_apply hq]
      refine ciSup_le fun v ↦ le_of_lt ?_
      have hv := hz (x := (v.1.val.toWeakDual, v.2.val.toWeakDual)) ⟨v.1.property, v.2.property⟩
      change dist (0 : ℂ) (tensorDualForm v.1.val v.2.val z) < r / 2 at hv
      simpa only [q, Seminorm.comp_apply, coe_normSeminorm, dist_zero_left] using hv
    change p₀ (U, V) z ∈ Metric.ball 0 r
    rw [mem_ball_zero_iff, Real.norm_of_nonneg (apply_nonneg _ _)]
    exact hle.trans_lt (half_lt_self hr)

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
      polarTopology (topDualPairing ℂ X) {A | TotallyBounded A} := by
  let K : Set (Set X) := {A | IsCompact A}
  let Kc : Set (Set (Completion X)) := {A | IsCompact A}
  let e : X ≃ᵤ Completion X := Completion.UniformCompletion.completeEquivSelf.symm
  have he (x : X) : e x = (x : Completion X) :=
    AbstractCompletion.compare_coe AbstractCompletion.ofComplete Completion.cPkg x
  let u : (X →ᵤ[K] ℂ) ≃ᵤ (Completion X →ᵤ[Kc] ℂ) :=
    UniformOnFun.congrLeft e.toEquiv
      (fun _ hA ↦ hA.image e.continuous)
      (fun _ hA ↦ e.toHomeomorph.isCompact_preimage.mpr hA)
  calc
    completionCompactDualTopology X = polarTopology (topDualPairing ℂ X) K := by
      let ev (φ : StrongDual ℂ X) : X →ᵤ[K] ℂ := UniformOnFun.ofFun K φ
      have hEval (φ : StrongDual ℂ X) :
          u (ev φ) = UniformOnFun.ofFun Kc (φ.fromCompletion : Completion X → ℂ) := by
        funext y
        obtain ⟨x, rfl⟩ := e.surjective y
        change φ (e.symm (e x)) = φ.fromCompletion (e x)
        rw [e.symm_apply_apply, he, ContinuousLinearMap.fromCompletion_apply_coe]
      change TopologicalSpace.induced
        (fun φ : StrongDual ℂ X ↦ UniformOnFun.ofFun Kc (φ.fromCompletion : Completion X → ℂ))
        inferInstance = TopologicalSpace.induced ev inferInstance
      simp_rw [← hEval]
      exact (induced_compose (f := ev) (g := u)).symm.trans
        (congrArg (TopologicalSpace.induced ev) u.isUniformInducing.isInducing.eq_induced.symm)
    _ = polarTopology (topDualPairing ℂ X) {A | TotallyBounded A} := by
      refine le_antisymm (polarTopology_le_of_cofinal ?_) (polarTopology_le_of_cofinal ?_)
      · intro A hA
        exact ⟨closure A, hA.closure.isCompact_of_isClosed isClosed_closure, subset_closure⟩
      · intro A hA
        exact ⟨A, hA.totallyBounded, Subset.rfl⟩

include sep complete in
open scoped CompactConvergenceCLM in
/-- On a complete Hausdorff space, testing the extended functionals on compact sets
gives the compact convergence topology on the original functionals. -/
private theorem completionCompactDualTopology_eq_compact :
    completionCompactDualTopology X = (inferInstance : TopologicalSpace (X →L_c[ℂ] ℂ)) := by
  let e := (Completion.UniformCompletion.completeEquivSelf : Completion X ≃ᵤ X).symm.toHomeomorph
  have he (x : X) : e x = (x : Completion X) := by
    apply e.symm.injective
    exact (e.symm_apply_apply x).trans (Completion.cPkg.compare_coe AbstractCompletion.ofComplete x).symm
  let K : Set (Set X) := {A | IsCompact A}
  let L : Set (Set (Completion X)) := {A | IsCompact A}
  let E : (X →ᵤ[K] ℂ) ≃ᵤ (Completion X →ᵤ[L] ℂ) :=
    UniformOnFun.congrLeft e.toEquiv (fun _ h ↦ h.image e.continuous)
      (fun _ h ↦ e.isCompact_preimage.mpr h)
  rw [UniformConvergenceCLM.topologicalSpace_eq (RingHom.id ℂ) ℂ K]
  change induced (fun φ : StrongDual ℂ X ↦ UniformOnFun.ofFun L φ.fromCompletion)
    inferInstance = induced (fun φ : StrongDual ℂ X ↦ UniformOnFun.ofFun K φ) inferInstance
  have h : (fun φ : StrongDual ℂ X ↦ UniformOnFun.ofFun L φ.fromCompletion) =
      E ∘ (fun φ : StrongDual ℂ X ↦ UniformOnFun.ofFun K φ) := by
    funext φ
    change φ.fromCompletion = (fun x ↦ φ (e.symm x))
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply, he, ContinuousLinearMap.fromCompletion_apply_coe]
  rw [h, ← induced_compose]
  exact congrArg (induced (fun φ : StrongDual ℂ X ↦ UniformOnFun.ofFun K φ))
    E.isUniformInducing.isInducing.eq_induced.symm

omit lc sep complete in
open scoped CompactConvergenceCLM in
/-- Compact convergence induces pointwise convergence on an equicontinuous family. -/
private theorem compactDualTopology_induced (A : Set (WeakDual ℂ X))
    (hA : EquicontinuousAt (fun φ : A ↦ (φ.val : X → ℂ)) 0) :
    (inferInstance : TopologicalSpace (X →L_c[ℂ] ℂ)).induced
      (fun φ : A ↦ WeakDual.toStrongDual φ.val) = (inferInstance : TopologicalSpace A) := by
  let f : A → X → ℂ := fun φ ↦ φ.val
  have hEq : Equicontinuous f :=
    equicontinuous_of_equicontinuousAt_zero
      (fun φ : A ↦ φ.val.toStrongDual.toAddMonoidHom) hA
  have hweak : IsInducing f :=
    (show IsInducing (fun φ : WeakDual ℂ X ↦ (φ : X → ℂ)) from ⟨rfl⟩).comp
      IsInducing.subtypeVal
  let K : Set (Set X) := {A | IsCompact A}
  have hcompact : IsInducing (UniformOnFun.ofFun K ∘ f) :=
    (EquicontinuousOn.isInducing_uniformOnFun_iff_pi sUnion_isCompact_eq_univ
      (fun _ h ↦ h) (fun k _ ↦ hEq.equicontinuousOn k)).mpr hweak
  let j : A → (X →L_c[ℂ] ℂ) := fun φ ↦ φ.val.toStrongDual
  change induced j inferInstance = _
  rw [UniformConvergenceCLM.topologicalSpace_eq (RingHom.id ℂ) ℂ K, induced_compose]
  exact hcompact.eq_induced.symm

omit lc sep complete in
/-- A seminorm continuous on a weak-dual polar admits finite simultaneous evaluation
approximations there for all algebraic functionals dominated by the seminorm. -/
private theorem finite_approx_on_polar (p : Seminorm ℂ (StrongDual ℂ X))
    (q : Seminorm ℂ X) (hq : Continuous q)
    (hp : Continuous (fun φ : WeakDual.polar ℂ (q.closedBall 0 1) ↦ p φ.val.toStrongDual))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Set X, D.Finite ∧ ∀ l : Module.Dual ℂ (StrongDual ℂ X),
      (∀ φ, ‖l φ‖ ≤ p φ) → ∃ x ∈ D, ∀ φ ∈ WeakDual.polar ℂ (q.closedBall 0 1),
        ‖l φ.toStrongDual - φ x‖ ≤ ε := by
  classical
  let e : ULift.{0} X ≃ₗ[ℂ] X := ULift.moduleEquiv
  let q' := q.comp e.toLinearMap
  let : SeminormedAddCommGroup (ULift.{0} X) := q'.toSeminormedAddCommGroup
  let : TopologicalSpace (ULift.{0} X) :=
    q'.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let : NormedSpace ℂ (ULift.{0} X) := ⟨fun c y ↦ (map_smul_eq_mul q' c y).le⟩
  have he : Continuous e.symm := by
    refine (Metric.continuous_iff' (f := fun y : X ↦ e.symm y)).mpr fun y r hr ↦ ?_
    have hc : Continuous (fun x : X ↦ q (x - y)) := hq.comp (continuous_id.sub continuous_const)
    filter_upwards [hc.continuousAt (x := y).eventually_lt continuousAt_const
      (show q (y - y) < r by simpa)] with x hx
    rw [dist_eq_norm, ← map_sub]
    change q (e (e.symm (x - y))) < r
    rwa [e.apply_symm_apply]
  let Y := StrongDual ℂ (ULift.{0} X)
  let : SeminormedAddCommGroup Y :=
    inferInstanceAs (SeminormedAddCommGroup (StrongDual ℂ (ULift.{0} X)))
  let : NormedAddCommGroup Y := NormedAddCommGroup.ofSeparation fun g hg ↦ by
    apply ContinuousLinearMap.ext
    intro y
    exact norm_le_zero_iff.mp (by simpa [hg] using g.le_opNorm y)
  let : NormedSpace ℂ Y := inferInstanceAs (NormedSpace ℂ (StrongDual ℂ (ULift.{0} X)))
  let j : Y →ₗ[ℂ] StrongDual ℂ X :=
    (ContinuousLinearMap.precomp ℂ (⟨e.symm.toLinearMap, he⟩ : X →L[ℂ] ULift.{0} X)).toLinearMap
  let P := WeakDual.polar ℂ (q.closedBall 0 1)
  have hunit (g : Y) (hg : ‖g‖ ≤ 1) : (j g).toWeakDual ∈ P := by
    intro x hx
    change ‖g (e.symm x)‖ ≤ 1
    calc
      ‖g (e.symm x)‖ ≤ ‖g‖ * ‖e.symm x‖ := g.le_opNorm _
      _ ≤ 1 * 1 := mul_le_mul hg (q.mem_closedBall_zero.mp hx) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hcover (φ : WeakDual ℂ X) (hφ : φ ∈ P) :
      ∃ g : Y, ‖g‖ ≤ 1 ∧ j g = φ.toStrongDual := by
    have hbound (x : X) : ‖φ x‖ ≤ q x := by
      refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
      have hr' := (apply_nonneg q x).trans_lt hr
      have hu : (r : ℂ)⁻¹ • x ∈ q.closedBall 0 1 := by
        apply q.mem_closedBall_zero.mpr
        rw [map_smul_eq_mul, norm_inv, Complex.norm_of_nonneg hr'.le, ← div_eq_inv_mul,
          div_le_iff₀ hr', one_mul]
        exact hr.le
      have h : ‖φ ((r : ℂ)⁻¹ • x)‖ ≤ 1 := hφ _ hu
      rw [map_smul, norm_smul, norm_inv, Complex.norm_of_nonneg hr'.le, ← div_eq_inv_mul,
        div_le_iff₀ hr', one_mul] at h
      exact h
    let f := φ.toStrongDual.toLinearMap.comp e.toLinearMap
    have hf (z : ULift.{0} X) : ‖f z‖ ≤ 1 * ‖z‖ := by
      change ‖φ (e z)‖ ≤ 1 * q (e z)
      simpa only [one_mul] using hbound (e z)
    refine ⟨f.mkContinuous 1 hf, f.mkContinuous_norm_le zero_le_one hf, ?_⟩
    ext x
    exact congrArg φ (e.apply_symm_apply x)
  -- Restriction of the seminorm to the normed dual is continuous on its unit ball.
  let B := Metric.closedBall (0 : Y) 1
  let pull (g : B) : P :=
    ⟨(j g.val).toWeakDual, hunit g.val (mem_closedBall_zero_iff.mp g.property)⟩
  have hpull : Continuous pull := by
    apply Continuous.subtype_mk
    apply WeakDual.continuous_of_continuous_eval
    intro x
    exact (ContinuousLinearMap.apply ℂ ℂ (e.symm x)).continuous.comp continuous_subtype_val
  have hpc : Continuous (fun g : B ↦ p (j g.val)) := hp.comp hpull
  let pp := p.comp j
  have hpp : Continuous pp := by
    refine Seminorm.continuous' (r := 1) ?_
    let z : B := ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    have hnear : {g : B | pp g.val < 1} ∈ 𝓝 z :=
      hpc.continuousAt.preimage_mem_nhds (show Iio 1 ∈ 𝓝 (pp z.val) by
        simp only [z, map_zero]; exact Iio_mem_nhds one_pos)
    rw [nhds_subtype] at hnear
    obtain ⟨W, hW, hsub⟩ := Filter.mem_comap.mp hnear
    filter_upwards [hW, Metric.closedBall_mem_nhds (0 : Y) one_pos] with g hg hB
    exact pp.mem_closedBall_zero.mpr (hsub (a := ⟨g, hB⟩) hg).le
  obtain ⟨C, hC, hbound⟩ := pp.bound_of_continuous_normedSpace hpp
  -- Continuity at zero on the polar gives finitely many evaluations whose joint
  -- kernel has small seminorm on the unit ball.
  let z : P := ⟨0, by intro x hx; simp⟩
  have hnear : {φ : P | p φ.val.toStrongDual < ε / 2} ∈ 𝓝 z :=
    hp.continuousAt.preimage_mem_nhds (show Iio (ε / 2) ∈ 𝓝 (p z.val.toStrongDual) by
      simp only [z, map_zero]; exact Iio_mem_nhds (half_pos hε))
  rw [nhds_subtype] at hnear
  obtain ⟨W, hW, hsub⟩ := Filter.mem_comap.mp hnear
  change W ∈ 𝓝 (0 : WeakBilin (topDualPairing ℂ X)) at hW
  obtain ⟨⟨s, r⟩, hr, hs⟩ :=
    (topDualPairing ℂ X).weakBilin_withSeminorms.hasBasis_zero_ball.mem_iff.mp hW
  let ev : X →ₗ[ℂ] StrongDual ℂ Y :=
    (ContinuousLinearMap.apply ℂ ℂ (E' := ULift.{0} X)).toLinearMap.comp e.symm.toLinearMap
  let V : Submodule ℂ (StrongDual ℂ Y) := Submodule.span ℂ (ev '' (s : Set X))
  let T : Submodule ℂ Y := ⨅ x : s, (ev x).toLinearMap.ker
  have hsmall (g : T) (hg : ‖g‖ ≤ 1) : p (j g.val) ≤ ε / 2 := by
    have hPg := hunit g.val hg
    have hball : j g.val ∈ (s.sup (topDualPairing ℂ X).toSeminormFamily).ball 0 r := by
      refine (s.sup (topDualPairing ℂ X).toSeminormFamily).mem_ball_zero.mpr
        (Seminorm.finset_sup_apply_lt hr fun x hx ↦ ?_)
      have hzero : (ev x) g.val = 0 :=
        LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp g.property ⟨x, hx⟩)
      change ‖(ev x) g.val‖ < r
      simpa only [hzero, norm_zero] using hr
    exact (hsub (a := ⟨(j g.val).toWeakDual, hPg⟩) (hs hball)).le
  let R := C + ε / 2
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image ev)
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  have hcompact : IsCompact (Metric.closedBall (0 : V) R) := isCompact_closedBall _ _
  have hballs : Metric.closedBall (0 : V) R ⊆ ⋃ v : V, Metric.ball v (ε / 2) := by
    intro v _
    exact mem_iUnion.mpr ⟨v, Metric.mem_ball_self (half_pos hε)⟩
  obtain ⟨F, hF⟩ := hcompact.elim_finite_subcover _ (fun _ ↦ Metric.isOpen_ball) hballs
  have hV : V ≤ ev.range :=
    Submodule.span_le.mpr (fun _ ⟨x, _, hx⟩ ↦ ⟨x, hx⟩)
  choose x hx using fun v : V ↦ show ∃ x, ev x = v.val from hV v.property
  refine ⟨x '' (F : Set V), F.finite_toSet.image x, fun l hl ↦ ?_⟩
  let lj := l.comp j
  let f := lj.mkContinuous C (fun g ↦ (hl (j g)).trans (hbound g))
  let ft := lj.comp T.subtype
  -- Extend the small restriction on the joint kernel. The remaining functional is
  -- in the span of the finite set of evaluations.
  have hft (g : T) : ‖ft g‖ ≤ (ε / 2) * ‖g‖ := by
    by_cases hg : g = 0
    · simp [hg]
    have hg' : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have hnorm : ‖((‖g‖ : ℝ) : ℂ)⁻¹ • g‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Complex.norm_of_nonneg hg'.le, inv_mul_cancel₀ hg'.ne']
    have hscale := (hl (j ((((‖g‖ : ℝ) : ℂ)⁻¹ • g : T)).val)).trans (hsmall _ hnorm)
    change ‖ft (((‖g‖ : ℂ)⁻¹) • g)‖ ≤ ε / 2 at hscale
    rw [map_smul, norm_smul, norm_inv, Complex.norm_of_nonneg hg'.le, ← div_eq_inv_mul,
      div_le_iff₀ hg'] at hscale
    exact hscale
  obtain ⟨b, hb, hbnd⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm T ft
    (p := (Real.toNNReal (ε / 2)) • normSeminorm ℂ Y)
    (continuous_norm.const_smul _) (fun g ↦ by
      simpa [smul_apply, NNReal.smul_def, Real.toNNReal_of_nonneg (half_pos hε).le] using hft g)
  have hbn : ‖b‖ ≤ ε / 2 := b.opNorm_le_bound (half_pos hε).le fun g ↦ by
    simpa [smul_apply, NNReal.smul_def, Real.toNNReal_of_nonneg (half_pos hε).le] using hbnd g
  have hker : T ≤ (f - b).toLinearMap.ker := fun g hg ↦ by
    apply LinearMap.mem_ker.mpr
    exact sub_eq_zero.mpr (hb ⟨g, hg⟩).symm
  have hspan := mem_span_of_iInf_ker_le_ker hker
  have hfb : f - b ∈ V := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
    have heq : f - b = ∑ i : s, c i • ev i := by
      apply ContinuousLinearMap.coe_injective
      simpa using hc.symm
    rw [heq]
    exact V.sum_mem fun i _ ↦ V.smul_mem _ (Submodule.subset_span ⟨i, i.property, rfl⟩)
  let v : V := ⟨f - b, hfb⟩
  have hv : v ∈ Metric.closedBall (0 : V) R := by
    change dist (f - b) (0 : StrongDual ℂ Y) ≤ R
    rw [dist_zero_right]
    exact (norm_sub_le _ _).trans (add_le_add (lj.mkContinuous_norm_le hC.le _) hbn)
  obtain ⟨w, hw, hd⟩ := mem_iUnion₂.mp (hF hv)
  refine ⟨x w, mem_image_of_mem x hw, fun φ hφ ↦ ?_⟩
  obtain ⟨g, hg, hj⟩ := hcover φ hφ
  have hnorm : ‖f - ev (x w)‖ ≤ ε := by
    rw [hx w, show f - w.val = (f - b - w.val) + b by abel]
    have hvw : ‖(f - b) - w.val‖ < ε / 2 := by
      change dist (f - b) w.val < ε / 2 at hd
      simpa only [dist_eq_norm] using hd
    exact (norm_add_le _ _).trans (by linarith)
  calc
    ‖l φ.toStrongDual - φ (x w)‖ = ‖(f - ev (x w)) g‖ := by
      change ‖l φ.toStrongDual - φ.toStrongDual (x w)‖ = ‖l (j g) - (j g) (x w)‖
      rw [hj]
    _ ≤ ‖f - ev (x w)‖ * ‖g‖ := (f - ev (x w)).le_opNorm _
    _ ≤ ε := (mul_le_of_le_one_right (norm_nonneg (f - ev (x w))) hg).trans hnorm

include complete in
omit sep in
open scoped NNReal Uniformity in
/-- Finite evaluation approximations on each seminorm polar give a common compact set
of representing vectors for the functionals dominated by the dual seminorm. -/
private theorem compact_eval_of_finite_approx [MetrizableSpace X]
    (p : Seminorm ℂ (StrongDual ℂ X))
    (h : ∀ (q : Seminorm ℂ X), Continuous q → ∀ ε : ℝ, 0 < ε →
      ∃ D : Set X, D.Finite ∧ ∀ l : Module.Dual ℂ (StrongDual ℂ X),
        (∀ φ, ‖l φ‖ ≤ p φ) → ∃ x ∈ D, ∀ φ ∈ WeakDual.polar ℂ (q.closedBall 0 1),
          ‖l φ.toStrongDual - φ x‖ ≤ ε) :
    ∃ K : Set X, IsCompact K ∧ ∀ l : Module.Dual ℂ (StrongDual ℂ X),
      (∀ φ, ‖l φ‖ ≤ p φ) → ∃ x ∈ K, ∀ φ : StrongDual ℂ X, l φ = φ x := by
  classical
  have hbasis : (𝓝 (0 : X)).HasBasis (fun q : Seminorm ℂ X ↦ Continuous q)
      (fun q ↦ q.closedBall 0 1) := by
    apply (PolynormableSpace.hasBasis_zero_ball ℂ X).to_hasBasis
    · intro q hq
      refine ⟨(2 : ℝ≥0) • q, hq.const_smul _, fun x hx ↦ ?_⟩
      rw [Seminorm.mem_closedBall_zero, smul_apply] at hx
      change 2 * q x ≤ 1 at hx
      exact q.mem_ball_zero.mpr (by linarith)
    · intro q hq
      exact ⟨q, hq, q.ball_subset_closedBall _ _⟩
  obtain ⟨q, hq, hU⟩ := hbasis.exists_antitone_subbasis
  let U (n : ℕ) := (q n).closedBall 0 1
  let P (n : ℕ) := WeakDual.polar ℂ (U n)
  have hP : Monotone P := fun _ _ hnm φ hφ x hx ↦ hφ x (hU.2 hnm hx)
  let δ (n : ℕ) : ℝ := (1 / 2) ^ (n + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδhalf (n : ℕ) : δ n ≤ 1 / 2 := by
    simpa [δ] using pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (show 1 ≤ n + 1 by omega)
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num)).mul_const (1 / 2)
  choose D hD happrox using fun n ↦ h (q n) (hq n) (δ n) (hδpos n)
  let S := {l : Module.Dual ℂ (StrongDual ℂ X) | ∀ φ, ‖l φ‖ ≤ p φ}
  choose a ha herror using fun (l : S) n ↦ happrox n l.val l.property
  have hdiff (l : S) (k m n : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
      a l m - a l n ∈ U k := by
    obtain ⟨ψ, hψ, heq⟩ := exists_dual_norm_eq_seminorm (q k) (hq k) (a l m - a l n)
    have hmem : ψ.toWeakDual ∈ P k := fun y hy ↦
      (hψ y).trans ((q k).mem_closedBall_zero.mp hy)
    apply (q k).mem_closedBall_zero.mpr
    have hm' := herror l m ψ.toWeakDual (hP hm hmem)
    have hn' := herror l n ψ.toWeakDual (hP hn hmem)
    change ‖l.val ψ - ψ (a l m)‖ ≤ δ m at hm'
    change ‖l.val ψ - ψ (a l n)‖ ≤ δ n at hn'
    rw [← heq, map_sub]
    calc
      ‖ψ (a l m) - ψ (a l n)‖ ≤
          ‖ψ (a l m) - l.val ψ‖ + ‖l.val ψ - ψ (a l n)‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ δ m + δ n := add_le_add ((norm_sub_rev _ _).trans_le hm') hn'
      _ ≤ 1 := by linarith [hδhalf m, hδhalf n]
  have hUniform : (𝓤 X).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {z : X × X | z.2 - z.1 ∈ U n}) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact hU.1.comap _
  have hcauchy (l : S) : CauchySeq (a l) :=
    hUniform.cauchySeq_iff.mpr fun k _ ↦ ⟨k, fun _ hm _ hn ↦ hdiff l k _ _ hn hm⟩
  choose x hx using fun l ↦ cauchySeq_tendsto_of_complete (hcauchy l)
  have hclose (l : S) (n : ℕ) : a l n - x l ∈ U n := by
    have hclosed : IsClosed (U n) := by
      rw [show U n = {y | q n y ≤ 1} from (q n).closedBall_zero_eq]
      exact isClosed_le (hq n) continuous_const
    have hlim : Tendsto (fun m ↦ a l n - a l m) atTop (𝓝 (a l n - x l)) :=
      tendsto_const_nhds.sub (hx l)
    exact hclosed.mem_of_tendsto hlim
      (eventually_atTop.mpr ⟨n, fun m hm ↦ hdiff l n n m le_rfl hm⟩)
  have htot : TotallyBounded (range x) := by
    refine hUniform.totallyBounded_iff.mpr fun n _ ↦ ⟨D n, hD n, ?_⟩
    rintro _ ⟨l, rfl⟩
    exact mem_iUnion₂.mpr ⟨a l n, ha l n, hclose l n⟩
  refine ⟨closure (range x), htot.closure.isCompact_of_isClosed isClosed_closure, fun l hl ↦ ?_⟩
  let s : S := ⟨l, hl⟩
  refine ⟨x s, subset_closure (mem_range_self s), fun φ ↦ ?_⟩
  have hφnear : φ ⁻¹' Metric.closedBall 0 1 ∈ 𝓝 (0 : X) :=
    φ.continuous.continuousAt.preimage_mem_nhds (by simpa using Metric.closedBall_mem_nhds (0 : ℂ) one_pos)
  obtain ⟨n, hn⟩ := hU.mem_iff.mp hφnear
  have hφmem : φ.toWeakDual ∈ P n := fun y hy ↦ mem_closedBall_zero_iff.mp (hn hy)
  have hlim : Tendsto (fun m ↦ ‖l φ - φ (a s m)‖) atTop (𝓝 ‖l φ - φ (x s)‖) :=
    (tendsto_const_nhds.sub ((φ.continuous.tendsto (x s)).comp (hx s))).norm
  have hz : ‖l φ - φ (x s)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hlim hδzero
      (eventually_atTop.mpr ⟨n, fun m hm ↦ herror s m φ.toWeakDual (hP hm hφmem)⟩)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

include sep complete in
open scoped CompactConvergenceCLM in
/-- Paper: Remark C.2.3.2, p. 677. For a complete metrizable space, μ is the finest
locally convex topology agreeing with the weak dual topology on all equicontinuous sets. -/
theorem completionCompactDualTopology_isLeast [met : MetrizableSpace X] :
    IsLeast {t : TopologicalSpace (StrongDual ℂ X) |
      @PolynormableSpace ℂ _ _ _ _ t ∧
      ∀ A : Set (WeakDual ℂ X), EquicontinuousAt (fun φ : A ↦ (φ.val : X → ℂ)) 0 →
        t.induced (fun φ : A ↦ WeakDual.toStrongDual φ.val) = (inferInstance : TopologicalSpace A)}
      (completionCompactDualTopology X) := by
  rw [completionCompactDualTopology_eq_compact]
  let K : Set (Set X) := {A | IsCompact A}
  have hμ : PolynormableSpace ℂ (X →L_c[ℂ] ℂ) :=
    (uniformConvergenceCLM_withSeminorms K (fun _ h ↦ h.isVonNBounded ℂ)
      (by rw [show ⋃₀ K = univ from sUnion_isCompact_eq_univ, Submodule.span_univ]; simp)
      (fun _ : Unit ↦ normSeminorm ℂ ℂ)
      (norm_withSeminorms ℂ ℂ)).toPolynormableSpace
  refine ⟨⟨hμ, compactDualTopology_induced⟩, ?_⟩
  rintro t ⟨ht, hagree⟩
  let : TopologicalSpace (StrongDual ℂ X) := t
  let : PolynormableSpace ℂ (StrongDual ℂ X) := ht
  change (inferInstance : TopologicalSpace (X →L_c[ℂ] ℂ)) ≤ t
  rw [← induced_id (t := t)]
  apply Continuous.le_induced
  refine (PolynormableSpace.withSeminorms ℂ (StrongDual ℂ X)).continuous_of_continuous_comp
    (show (X →L_c[ℂ] ℂ) →ₗ[ℂ] StrongDual ℂ X from LinearMap.id) ?_
  rintro ⟨p, hp⟩
  obtain ⟨C, hC, hrepr⟩ := compact_eval_of_finite_approx p fun q hq ε hε ↦ by
    have hU : q.closedBall 0 1 ∈ 𝓝 (0 : X) :=
      mem_of_superset (q.ball_mem_nhds hq one_pos) (q.ball_subset_closedBall _ _)
    let P := WeakDual.polar ℂ (q.closedBall 0 1)
    have hP : Continuous (fun φ : P ↦ φ.val.toStrongDual) :=
      (show IsInducing (fun φ : P ↦ φ.val.toStrongDual) from
        ⟨(hagree P (weakDual_polar_mem_compactology hU).1).symm⟩).continuous
    exact finite_approx_on_polar p q hq (hp.comp hP) hε
  change Continuous (fun φ : X →L_c[ℂ] ℂ ↦ p φ)
  refine Seminorm.continuous' (p := (show Seminorm ℂ (X →L_c[ℂ] ℂ) from p)) (r := 1) ?_
  have hnear := CompactConvergenceCLM.hasBasis_nhds_zero_of_basis
    (Metric.nhds_basis_ball (x := (0 : ℂ))) (E := X) (σ := RingHom.id ℂ)
  filter_upwards [hnear.mem_of_mem (i := (C, 1)) ⟨hC, one_pos⟩] with φ hφ
  obtain ⟨l, hl, heq⟩ := exists_dual_norm_eq_seminorm p hp φ
  obtain ⟨x, hx, hEval⟩ := hrepr l.toLinearMap hl
  apply (show Seminorm ℂ (X →L_c[ℂ] ℂ) from p).mem_closedBall_zero.mpr
  calc
    p (show StrongDual ℂ X from φ) = ‖l φ‖ := heq.symm
    _ = ‖φ x‖ := congrArg norm (hEval φ)
    _ ≤ 1 := (mem_ball_zero_iff.mp (hφ x hx)).le
end Mu

/-- Paper: (C.2.3.5)–(C.2.3.6), p. 677. Contracting a tensor against the first
dual variable gives a finite-rank operator from the dual of E to F. -/
def tensorDualOperator : E ⊗[ℂ] F →ₗ[ℂ] StrongDual ℂ E →ₗ[ℂ] F :=
  (dualTensorHom ℂ (StrongDual ℂ E) F).comp
    (TensorProduct.map (topDualPairing ℂ E).flip LinearMap.id)

/-- Paper: (C.2.3.6), p. 677. A pure tensor sends a functional to its value at the
first factor times the second factor. -/
theorem tensorDualOperator_tmul (x : E) (y : F) (φ : StrongDual ℂ E) :
    tensorDualOperator (x ⊗ₜ[ℂ] y) φ = φ x • y := by
  rfl

include hE sE hF sF in
/-- Paper: Remark C.2.3.2, p. 677. The canonical operator representation is injective. -/
theorem tensorDualOperator_injective : Function.Injective (tensorDualOperator (E := E) (F := F)) := by
  let := polynormableSpace_separatingDual ℂ E
  let := polynormableSpace_separatingDual ℂ F
  intro z w h
  apply tensorDualForm_ext
  intro φ ψ
  have hform : tensorDualForm φ ψ =
      ψ.toLinearMap.comp ((LinearMap.applyₗ (R := ℂ) φ).comp tensorDualOperator) := by
    apply TensorProduct.ext'
    intro x y
    change tensorDualForm φ ψ (x ⊗ₜ[ℂ] y) = ψ (tensorDualOperator (x ⊗ₜ[ℂ] y) φ)
    simp [tensorDualForm_tmul, tensorDualOperator, dualTensorHom_apply, LinearMap.flip_apply]
  rw [hform]
  change ψ (tensorDualOperator z φ) = ψ (tensorDualOperator w φ)
  rw [h]

/-- Paper: Remark C.2.3.2, p. 677. The operator associated to each tensor has
finite-dimensional image. -/
theorem tensorDualOperator_finiteRank (z : E ⊗[ℂ] F) :
    FiniteDimensional ℂ (LinearMap.range (tensorDualOperator z)) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, LinearMap.range_zero]
    infer_instance
  | tmul x y =>
    refine Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ y) ?_
    rintro _ ⟨φ, rfl⟩
    rw [tensorDualOperator_tmul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  | add z w hz hw =>
    refine Submodule.finiteDimensional_of_le
      (S₂ := LinearMap.range (tensorDualOperator z) ⊔ LinearMap.range (tensorDualOperator w)) ?_
    rintro _ ⟨φ, rfl⟩
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨φ, rfl⟩ ⟨φ, rfl⟩

omit hE sE hF sF in
/-- A scalar evaluation of a contracted tensor is the corresponding dual form. -/
private theorem tensorDualOperator_eval (z : E ⊗[ℂ] F) (φ : StrongDual ℂ E)
    (ψ : StrongDual ℂ F) : ψ (tensorDualOperator z φ) = tensorDualForm φ ψ z := by
  let L : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ :=
    ψ.toLinearMap.comp ((LinearMap.applyₗ φ).comp tensorDualOperator)
  have hL : L = tensorDualForm φ ψ := by
    apply TensorProduct.ext'
    intro x y
    simp [L, tensorDualOperator, tensorDualForm_tmul, smul_eq_mul]
  exact DFunLike.congr_fun hL z

include hE hF in
omit sE sF in
open scoped Pointwise in
/-- Bounds on all scalar evaluations over two polars are exactly bounds on the
corresponding injective seminorm. -/
private theorem injectiveTensorSeminorm_le_iff
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0})
    (z : E ⊗[ℂ] F) (r : ℝ) :
    injectiveTensorSeminorm U V z ≤ r ↔
      ∀ φ ∈ StrongDual.polar ℂ U.val, ∀ ψ ∈ StrongDual.polar ℂ V.val,
        ‖tensorDualForm φ ψ z‖ ≤ r := by
  classical
  let D := StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val
  let p (f : D) := (normSeminorm ℂ ℂ).comp (tensorDualForm f.1.val f.2.val)
  have hbound (z : E ⊗[ℂ] F) : ∃ C : ℝ, ∀ f : D, p f z ≤ C := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        obtain ⟨a, x', hx', rfl⟩ : ∃ a : ℂ, x ∈ a • U.val := by
          simpa using (absorbent_nhds_zero (𝕜 := ℂ) U.property x).exists
        obtain ⟨b, y', hy', rfl⟩ : ∃ b : ℂ, y ∈ b • V.val := by
          simpa using (absorbent_nhds_zero (𝕜 := ℂ) V.property y).exists
        refine ⟨‖a‖ * ‖b‖, fun f ↦ ?_⟩
        change ‖tensorDualForm f.1.val f.2.val ((a • x') ⊗ₜ[ℂ] (b • y'))‖ ≤ _
        simp only [tensorDualForm_tmul, map_smul, norm_mul, norm_smul]
        exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _)
          ((StrongDual.mem_polar_iff ℂ _).mp f.1.property _ hx'))
          (mul_le_of_le_one_right (norm_nonneg _)
            ((StrongDual.mem_polar_iff ℂ _).mp f.2.property _ hy'))
          (by positivity) (norm_nonneg _)
    | add z w hz hw =>
        obtain ⟨Cz, hz⟩ := hz
        obtain ⟨Cw, hw⟩ := hw
        exact ⟨Cz + Cw, fun f ↦ (map_add_le_add (p f) z w).trans (add_le_add (hz f) (hw f))⟩
  have hb (z : E ⊗[ℂ] F) : BddAbove (range fun f : D ↦ p f z) := by
    obtain ⟨C, hC⟩ := hbound z
    exact ⟨C, forall_mem_range.mpr hC⟩
  have hp : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr hb
  have hsup : injectiveTensorSeminorm U V z = ⨆ f : D, p f z := by
    unfold injectiveTensorSeminorm
    rw [← ciSup_prod hp, Seminorm.iSup_apply hp]
  let : Nonempty D := ⟨⟨⟨0, StrongDual.zero_mem_polar _ _⟩, ⟨0, StrongDual.zero_mem_polar _ _⟩⟩⟩
  rw [hsup]
  exact ⟨fun h φ hφ ψ hψ ↦ (le_ciSup (hb z) (⟨φ, hφ⟩, ⟨ψ, hψ⟩)).trans h,
    fun h ↦ ciSup_le fun f ↦ h f.1.val f.1.property f.2.val f.2.property⟩

include hE sE in
/-- Paper: Remark C.2.3.2, p. 677. Testing the associated operators on the equicontinuous
compactology gives the injective topology. -/
theorem tensorDualOperator_isEmbedding {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [UniformSpace Y] [IsUniformAddGroup Y] [PolynormableSpace ℂ Y] [T2Space Y] :
    IsEmbedding (fun z : InjectiveTensor E Y ↦ UniformOnFun.ofFun (equicontinuousCompactology E)
      (fun φ : WeakDual ℂ E ↦ tensorDualOperator z φ)) := by
  classical
  let S := equicontinuousCompactology E
  let T₀ : (E ⊗[ℂ] Y) →+ (WeakDual ℂ E →ᵤ[S] Y) :=
    { toFun := fun z ↦ UniformOnFun.ofFun S (fun φ ↦ tensorDualOperator z φ)
      map_zero' := funext fun φ ↦ by
        change tensorDualOperator (0 : E ⊗[ℂ] Y) φ.toStrongDual = 0
        rw [map_zero, LinearMap.zero_apply]
      map_add' := fun z w ↦ funext fun φ ↦ by
        change tensorDualOperator (z + w) φ.toStrongDual =
          tensorDualOperator z φ.toStrongDual + tensorDualOperator w φ.toStrongDual
        simp only [map_add, LinearMap.add_apply] }
  let T : InjectiveTensor E Y →+ (WeakDual ℂ E →ᵤ[S] Y) := T₀
  change IsEmbedding T
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let : SeparatingDual ℂ Y := polynormableSpace_separatingDual ℂ Y
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_, ?_⟩
  swap
  · intro z w h
    apply tensorDualForm_ext
    intro φ ψ
    exact (tensorDualOperator_eval z φ ψ).symm.trans
      ((congrArg ψ (congrFun h φ.toWeakDual)).trans (tensorDualOperator_eval w φ ψ))
  let N := {U : Set E // U ∈ 𝓝 0}
  let P (U : N) := WeakDual.polar ℂ U.val
  have hP (U : N) : P U ∈ S := by
    let B : E →ₗ[ℂ] WeakDual ℂ E →ₗ[ℂ] ℂ :=
      (topDualPairing ℂ E).flip.compl₂ WeakDual.toStrongDual.toLinearMap
    refine ⟨?_, LinearMap.polar_AbsConvex (B := B) U.val, WeakDual.isClosed_polar _ _⟩
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    let c : ℂ := (ε / 2 : ℝ)
    have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast (half_pos hε).ne'
    have hnear : (fun x : E ↦ c⁻¹ • x) ⁻¹' U.val ∈ 𝓝 (0 : E) := by
      apply (continuous_const_smul c⁻¹).continuousAt.preimage_mem_nhds
      simpa only [smul_zero] using U.property
    filter_upwards [hnear] with x hx φ
    have hφ : ‖φ.val (c⁻¹ • x)‖ ≤ 1 := φ.property _ hx
    have hx' : x = c • (c⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [map_zero, dist_zero_left, hx', map_smul, norm_smul]
    have hnorm : ‖c‖ = ε / 2 := by
      dsimp only [c]
      rw [Complex.norm_real, Real.norm_of_nonneg (half_pos hε).le]
    exact (mul_le_of_le_one_right (norm_nonneg _) hφ).trans_lt (hnorm ▸ half_lt_self hε)
  have hcof (A : Set (WeakDual ℂ E)) (hA : A ∈ S) : ∃ U : N, A ⊆ P U := by
    have hnear := Metric.equicontinuousAt_iff_right.mp hA.1 1 one_pos
    refine ⟨⟨_, hnear⟩, fun φ hφ x hx ↦ ?_⟩
    have h := hx (⟨φ, hφ⟩ : A)
    change ‖φ x‖ ≤ 1
    simpa only [map_zero, dist_zero_left] using h.le
  have hne : S.Nonempty := ⟨P ⟨univ, univ_mem⟩, hP _⟩
  have hdir : DirectedOn (· ⊆ ·) S := by
    intro A hA B hB
    obtain ⟨U, hU⟩ := hcof A hA
    obtain ⟨V, hV⟩ := hcof B hB
    let W : N := ⟨U.val ∩ V.val, inter_mem U.property V.property⟩
    exact ⟨P W, hP W, fun _ hφ x hx ↦ hU hφ x hx.1, fun _ hφ x hx ↦ hV hφ x hx.2⟩
  let p₀ : SeminormFamily ℂ (E ⊗[ℂ] Y) (N × {V : Set Y // V ∈ 𝓝 0}) :=
    fun UV ↦ injectiveTensorSeminorm UV.1 UV.2
  let p : SeminormFamily ℂ (InjectiveTensor E Y) (N × {V : Set Y // V ∈ 𝓝 0}) := p₀
  have hp : WithSeminorms p := withGeneratingSeminorms_spec (E ⊗[ℂ] Y) p₀
  let hb := (uniformOnFun_zero_basis (F := Y) S hne hdir (𝓝 (0 : Y)).basis_sets).comap T
  refine le_antisymm (hb.ge_iff.mpr ?_) ?_
  · rintro ⟨A, W⟩ ⟨hA, hW⟩
    obtain ⟨U, hU⟩ := hcof A hA
    obtain ⟨q, hq, hqW⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ Y).mem_iff.mp hW
    let V : {V : Set Y // V ∈ 𝓝 0} :=
      ⟨q.closedBall 0 1, Filter.mem_of_superset (q.ball_mem_nhds hq one_pos)
        (q.ball_subset_closedBall _ _)⟩
    refine Filter.mem_of_superset ((p (U, V)).ball_mem_nhds (hp.continuous_seminorm _) one_pos)
      (fun z hz φ hφ ↦ hqW ((q.mem_ball_zero).mpr ?_))
    have norming (x : Y) :
        ∃ ψ ∈ StrongDual.polar ℂ V.val, ‖ψ x‖ = q x := by
      have algebraic (G : Type _) [AddCommGroup G] [Module ℂ G] (q : Seminorm ℂ G) (x : G) :
          ∃ g : G →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ q y) ∧ ‖g x‖ = q x := by
        let : SeminormedAddCommGroup G := q.toSeminormedAddCommGroup
        let : NormedSpace ℂ G := ⟨fun c y ↦ (map_smul_eq_mul q c y).le⟩
        obtain ⟨g, hg, hx⟩ := exists_dual_vector'' ℂ x
        refine ⟨g.toLinearMap, fun y ↦ (g.le_opNorm y).trans
          (mul_le_of_le_one_left (apply_nonneg q y) hg), ?_⟩
        change ‖g x‖ = q x
        rw [hx]
        change ‖(q x : ℂ)‖ = q x
        rw [Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x)]
      obtain ⟨g, hg, hx⟩ := algebraic Y q x
      have hgcont : Continuous g :=
        (PolynormableSpace.withSeminorms ℂ Y).continuous_normedSpace_rng ℂ g
          ⟨{⟨q, hq⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp g ≤ q from hg)⟩
      exact ⟨⟨g, hgcont⟩, fun y hy ↦ (hg y).trans (q.mem_closedBall_zero.mp hy), hx⟩
    change q (tensorDualOperator z φ.toStrongDual) < 1
    change E ⊗[ℂ] Y at z
    obtain ⟨ψ, hψ, heq⟩ := norming (tensorDualOperator z φ.toStrongDual)
    rw [← heq, tensorDualOperator_eval z φ.toStrongDual ψ]
    have hz' := (p (U, V)).mem_ball_zero.mp hz
    exact ((injectiveTensorSeminorm_le_iff U V z _).mp le_rfl _ (hU hφ) ψ hψ).trans_lt hz'
  · rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    refine le_iInf fun ⟨U, V⟩ ↦ ?_
    refine ((Metric.nhds_basis_ball (x := (0 : ℝ))).comap (p (U, V))).ge_iff.mpr fun r hr ↦ ?_
    let c : ℂ := (r / 2 : ℝ)
    have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast (half_pos hr).ne'
    let W := (fun y : Y ↦ c⁻¹ • y) ⁻¹' V.val
    have hW : W ∈ 𝓝 (0 : Y) := by
      apply (continuous_const_smul c⁻¹).continuousAt.preimage_mem_nhds
      simpa only [smul_zero] using V.property
    refine Filter.mem_of_superset (hb.mem_of_mem (i := (P U, W)) ⟨hP U, hW⟩) fun z hz ↦ ?_
    change E ⊗[ℂ] Y at z
    have hle : p₀ (U, V) z ≤ r / 2 := (injectiveTensorSeminorm_le_iff U V z _).mpr
      fun φ hφ ψ hψ ↦ by
        have hy : c⁻¹ • tensorDualOperator z φ ∈ V.val := hz (x := φ.toWeakDual) hφ
        have hψy := (StrongDual.mem_polar_iff ℂ _).mp hψ _ hy
        rw [← tensorDualOperator_eval]
        calc
          ‖ψ (tensorDualOperator z φ)‖ =
              ‖ψ (c • (c⁻¹ • tensorDualOperator z φ))‖ := by
                rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
          _ ≤ ‖c‖ := by
            rw [map_smul, norm_smul]
            exact mul_le_of_le_one_right (norm_nonneg _) hψy
          _ = r / 2 := by
            dsimp only [c]
            rw [Complex.norm_real, Real.norm_of_nonneg (half_pos hr).le]
    change p₀ (U, V) z ∈ Metric.ball (0 : ℝ) r
    rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (apply_nonneg _ _)]
    exact hle.trans_lt (half_lt_self hr)

/-- Paper: Remark C.2.3.2, p. 677. Each represented operator is continuous for μ. -/
theorem tensorDualOperator_continuous_mu {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [PolynormableSpace ℂ X] [T2Space X]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] (z : X ⊗[ℂ] F) :
    @Continuous _ F (completionCompactDualTopology X) _ (tensorDualOperator z) := by
  let : TopologicalSpace (StrongDual ℂ X) := completionCompactDualTopology X
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    let K : Set (Set (Completion X)) := {A | IsCompact A}
    have hext : Continuous (fun φ : StrongDual ℂ X ↦
        UniformOnFun.ofFun K (φ.fromCompletion : Completion X → ℂ)) := continuous_induced_dom
    have hsingleton : ({(x : Completion X)} : Set (Completion X)) ∈ K := isCompact_singleton
    have heval : Continuous (fun φ : StrongDual ℂ X ↦ φ x) := by
      have h := UniformOnFun.uniformContinuous_eval_of_mem (β := ℂ) K
        (mem_singleton (x : Completion X)) hsingleton
      simpa only [Function.comp_def, Function.eval, UniformOnFun.toFun_ofFun,
        ContinuousLinearMap.fromCompletion_apply_coe] using h.continuous.comp hext
    change Continuous (fun φ : StrongDual ℂ X ↦ tensorDualOperator (x ⊗ₜ[ℂ] y) φ)
    simp_rw [tensorDualOperator_tmul]
    exact continuous_smul.comp (heval.prodMk continuous_const)
  | add z w hz hw =>
    rw [map_add, LinearMap.coe_add]
    exact hz.add hw

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
        ‖tensorDualForm φ.val ψ.val z‖ := by
  let D := StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val
  let p (v : D) := (normSeminorm ℂ ℂ).comp (tensorDualForm v.1.val v.2.val)
  have hp : BddAbove (range p) := ⟨injectiveTensorSeminorm U V, forall_mem_range.mpr fun v w ↦
    norm_tensorDualForm_le_injectiveTensorSeminorm U V v.1 v.2 w⟩
  rw [injectiveTensorSeminorm, ← ciSup_prod hp, Seminorm.iSup_apply hp]
  exact ciSup_prod (Seminorm.bddAbove_range_iff.mp hp z)

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
      injectiveTensorNorm E F z = ‖T‖ := by
  let U : {U : Set E // U ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  let V : {V : Set F // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  have htest (r : ℝ) : injectiveTensorNorm E F z ≤ r ↔
      ∀ (φ : StrongDual ℂ E), ‖φ‖ ≤ 1 → ∀ (ψ : StrongDual ℂ F), ‖ψ‖ ≤ 1 →
        ‖ψ (tensorDualOperator z φ)‖ ≤ r := by
    simpa only [U, V, NormedSpace.polar_closedBall one_pos, inv_one, mem_closedBall_zero_iff,
      ← tensorDualOperator_eval] using injectiveTensorSeminorm_le_iff U V z r
  have hunit (φ : StrongDual ℂ E) (hφ : ‖φ‖ ≤ 1) :
      ‖tensorDualOperator z φ‖ ≤ injectiveTensorNorm E F z := by
    obtain ⟨ψ, hψ, heval⟩ := exists_dual_vector'' ℂ (tensorDualOperator z φ)
    simpa only [heval, RCLike.norm_coe_norm] using (htest _).mp le_rfl φ hφ ψ hψ
  let T := (tensorDualOperator z).mkContinuousOfExistsBound
    (LinearMap.bound_of_ball_bound one_pos _ _ fun φ hφ ↦ hunit φ (mem_ball_zero_iff.mp hφ).le)
  refine ⟨T, rfl, le_antisymm ((htest _).mpr ?_) ?_⟩
  · intro φ hφ ψ hψ
    change ‖ψ (T φ)‖ ≤ ‖T‖
    calc
      ‖ψ (T φ)‖ ≤ ‖ψ‖ * ‖T φ‖ := ψ.le_opNorm _
      _ ≤ ‖T φ‖ := mul_le_of_le_one_left (norm_nonneg _) hψ
      _ ≤ ‖T‖ := T.unit_le_opNorm φ hφ
  · exact ContinuousLinearMap.opNorm_le_of_unit_norm (apply_nonneg _ _)
      fun φ hφ ↦ hunit φ hφ.le

/-- Scaling out both arguments of the evaluation functional attached to a pure tensor
term of continuous functionals. -/
private theorem tensorDualForm_smul (a b : ℂ) (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) :
    tensorDualForm (a • φ) (b • ψ) = (a * b) • tensorDualForm φ ψ := by
  apply TensorProduct.ext'
  intro x y
  simp only [tensorDualForm_tmul, smul_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A functional in the polar of a zero-neighborhood of a normed space is a positive multiple
of a functional in the polar of the closed unit ball. -/
private theorem exists_scaled_polar_mem (U : {U : Set E // U ∈ 𝓝 0}) (ε : ℝ) (hε : 0 < ε)
    (hball : Metric.ball (0 : E) ε ⊆ U.val) (φ : StrongDual.polar ℂ U.val) :
    ∃ φ₀ : StrongDual.polar ℂ (Metric.closedBall (0 : E) 1),
      φ.val = ((2 : ℂ) / ((ε : ℝ) : ℂ)) • φ₀.val := by
  have hεc : ((ε : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
  refine ⟨⟨(((ε / 2) : ℝ) : ℂ) • φ.val,
    (StrongDual.mem_polar_iff ℂ _).mpr (fun x hx ↦ ?_)⟩, ?_⟩
  · have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hmem : (((ε / 2) : ℝ) : ℂ) • x ∈ Metric.ball (0 : E) ε := by
      rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by linarith) hx1) (by linarith)
    have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ (hball hmem)
    rw [map_smul] at hφ
    have hφ' := hφ
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)] at hφ'
    rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    exact hφ'
  · have hco : (((ε / 2) : ℝ) : ℂ) = ((ε : ℝ) : ℂ) / 2 := by
      norm_num [Complex.ofReal_div]
    have hscal : ((2 : ℂ) / ((ε : ℝ) : ℂ)) * (((ε / 2) : ℝ) : ℂ) = 1 := by
      rw [hco, div_mul_div_comm]
      field_simp
    rw [smul_smul, hscal, one_smul]

/-- Each evaluation against functionals in the two polars of zero-neighborhoods is bounded by
a positive multiple of the injective norm. -/
private theorem exists_le_injectiveTensorNorm
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : StrongDual.polar ℂ U.val) (ψ : StrongDual.polar ℂ V.val)
        (z : E ⊗[ℂ] F), ‖tensorDualForm φ.val ψ.val z‖ ≤ C * injectiveTensorNorm E F z := by
  obtain ⟨ε, hε, hballU⟩ := Metric.mem_nhds_iff.mp U.property
  obtain ⟨δ, hδ, hballV⟩ := Metric.mem_nhds_iff.mp V.property
  have hC : 0 < 4 / (ε * δ) := div_pos (by norm_num) (mul_pos hε hδ)
  refine ⟨4 / (ε * δ), hC, ?_⟩
  intro φ ψ z
  obtain ⟨φ₀, hφ⟩ := exists_scaled_polar_mem U ε hε hballU φ
  obtain ⟨ψ₀, hψ⟩ := exists_scaled_polar_mem V δ hδ hballV ψ
  have hbound := norm_tensorDualForm_le_injectiveTensorSeminorm
    ⟨Metric.closedBall (0 : E) 1, Metric.closedBall_mem_nhds 0 one_pos⟩
    ⟨Metric.closedBall (0 : F) 1, Metric.closedBall_mem_nhds 0 one_pos⟩ φ₀ ψ₀ z
  have hscal : ‖((2 : ℂ) / ((ε : ℝ) : ℂ)) * ((2 : ℂ) / ((δ : ℝ) : ℂ))‖ = 4 / (ε * δ) := by
    rw [norm_mul]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos hδ]
    norm_num
    field_simp
    norm_num
  calc ‖tensorDualForm φ.val ψ.val z‖
      = ‖((2 : ℂ) / ((ε : ℝ) : ℂ)) * ((2 : ℂ) / ((δ : ℝ) : ℂ)) *
          tensorDualForm φ₀.val ψ₀.val z‖ := by
          rw [hφ, hψ, tensorDualForm_smul]
          simp
    _ = (4 / (ε * δ)) * ‖tensorDualForm φ₀.val ψ₀.val z‖ := by
          rw [norm_mul, hscal]
    _ ≤ (4 / (ε * δ)) * injectiveTensorNorm E F z :=
          mul_le_mul_of_nonneg_left hbound hC.le

/-- Each injective seminorm of a normed pair is bounded by a positive multiple of the
injective norm. -/
private theorem injectiveTensorSeminorm_le_const_mul
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : E ⊗[ℂ] F,
      injectiveTensorSeminorm U V z ≤ C * injectiveTensorNorm E F z := by
  obtain ⟨C, hC, hper⟩ := exists_le_injectiveTensorNorm U V
  refine ⟨C, hC, fun z ↦ ?_⟩
  have hb : BddAbove (range fun v : StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val ↦
      (normSeminorm ℂ ℂ).comp (tensorDualForm v.1.val v.2.val)) := by
    rw [Seminorm.bddAbove_range_iff]
    intro w
    exact ⟨C * injectiveTensorNorm E F w, forall_mem_range.mpr fun v ↦ hper v.1 v.2 w⟩
  unfold injectiveTensorSeminorm
  rw [← ciSup_prod hb, Seminorm.iSup_apply hb]
  have hne : Nonempty (StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val) :=
    ⟨(⟨0, StrongDual.zero_mem_polar ℂ U.val⟩, ⟨0, StrongDual.zero_mem_polar ℂ V.val⟩)⟩
  refine ciSup_le fun v ↦ ?_
  exact hper v.1 v.2 z

/-- On a finite family of zero-neighborhood pairs the injective seminorms are uniformly
bounded by a positive multiple of the injective norm. -/
private theorem hfinbound :
    ∀ s : Finset ({U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0}), ∃ C : ℝ, 0 < C ∧
      ∀ UV ∈ s, ∀ z : InjectiveTensor E F,
        injectiveTensorSeminorm UV.1 UV.2 z ≤ C * injectiveTensorNorm E F z := by
  intro s
  classical
  refine ⟨∑ UV ∈ s, (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose + 1, ?_, ?_⟩
  · refine add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun UV _ ↦
        (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose_spec.1.le) one_pos
  · intro UV hUV z
    have hspec := (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose_spec
    refine hspec.2 z |>.trans (mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ z))
    calc (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose
        ≤ ∑ UV ∈ s, (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose :=
          Finset.single_le_sum (f := fun UV : _ × _ ↦
            (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose)
            (fun UV _ ↦ (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose_spec.1.le) hUV
      _ ≤ (∑ UV ∈ s, (injectiveTensorSeminorm_le_const_mul UV.1 UV.2).choose) + 1 :=
          le_add_of_nonneg_right zero_le_one

/-- Paper: Example C.2.3.4, p. 677. The unit-ball seminorm alone generates the ε-topology. -/
theorem injectiveTensorNorm_withSeminorms :
    WithSeminorms (E := InjectiveTensor E F) (fun _ : Unit ↦ injectiveTensorNorm E F) := by
  have htop := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  refine SeminormFamily.withSeminorms_of_nhds _ ?_
  refine le_antisymm ?_ ?_
  · -- The single-seminorm filter is finer: its basis balls are neighborhoods.
    intro U hU
    rcases (FilterBasis.mem_filter_iff _).1 hU with ⟨t, ht, hts⟩
    obtain ⟨s, r, hr, rfl⟩ := (SeminormFamily.basisSets_iff _).mp ht
    exact Filter.mem_of_superset
      (SeminormFamily.basisSets_mem_nhds _ (fun _ ↦ htop.continuous_seminorm
        (⟨Metric.closedBall (0 : E) 1, Metric.closedBall_mem_nhds 0 one_pos⟩,
          ⟨Metric.closedBall (0 : F) 1, Metric.closedBall_mem_nhds 0 one_pos⟩)) _ ht) hts
  · -- Every neighborhood contains a ball of the injective norm.
    intro U hU
    obtain ⟨⟨s, r⟩, hr, hBU⟩ := htop.hasBasis_zero_ball.mem_iff.mp hU
    obtain ⟨C, hC, hfin⟩ := hfinbound (E := E) (F := F) s
    rw [FilterBasis.mem_filter_iff]
    refine ⟨(({()} : Finset Unit)).sup (fun _ : Unit ↦ injectiveTensorNorm E F) |>.ball 0
      (r / (2 * C)),
      SeminormFamily.basisSets_mem _ {()} (div_pos hr (by linarith : (0 : ℝ) < 2 * C)), ?_⟩
    have hsup1 : (({()} : Finset Unit)).sup (fun _ : Unit ↦ injectiveTensorNorm E F) =
        injectiveTensorNorm E F := Finset.sup_singleton
    intro z hz
    rw [hsup1] at hz
    refine hBU ((s.sup (fun UV : _ × _ ↦ injectiveTensorSeminorm UV.1 UV.2)).mem_ball_zero.mpr
      (Seminorm.finset_sup_apply_lt hr ?_))
    intro UV hUV
    have hz' : injectiveTensorNorm E F z < r / (2 * C) :=
      (injectiveTensorNorm E F).mem_ball_zero.mp hz
    calc injectiveTensorSeminorm UV.1 UV.2 z ≤ C * injectiveTensorNorm E F z := hfin UV hUV z
      _ < C * (r / (2 * C)) := mul_lt_mul_of_pos_left hz' hC
      _ = r / 2 := by field_simp
      _ < r := by linarith

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
    injectiveTensorMap f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] g y :=
  TensorProduct.map_tmul _ _ _ _

omit lcE lcF lcG lcH sE sF sG sH in
open scoped Pointwise in
/-- Paper: (C.2.3.7), p. 677. The evaluation seminorms from two zero-neighborhood
polars form a bounded family in the pointwise order on seminorms. -/
private theorem injectiveTensorSeminorm_bddAbove {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [ContinuousSMul ℂ Y]
    (U : {U : Set X // U ∈ 𝓝 0}) (V : {V : Set Y // V ∈ 𝓝 0}) :
    BddAbove (range fun v : StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val ↦
      (normSeminorm ℂ ℂ).comp (tensorDualForm v.1.val v.2.val)) := by
  refine Seminorm.bddAbove_range_iff.mpr fun z ↦ ?_
  suffices ∃ C : ℝ, ∀ (φ : StrongDual.polar ℂ U.val) (ψ : StrongDual.polar ℂ V.val),
      ‖tensorDualForm φ.val ψ.val z‖ ≤ C by
    obtain ⟨C, hC⟩ := this
    exact ⟨C, forall_mem_range.mpr fun v ↦ hC v.1 v.2⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨a, hx⟩ : ∃ a : ℂ, x ∈ a • U.val := by
        simpa using (absorbent_nhds_zero (𝕜 := ℂ) U.property x).exists
      obtain ⟨b, hy⟩ : ∃ b : ℂ, y ∈ b • V.val := by
        simpa using (absorbent_nhds_zero (𝕜 := ℂ) V.property y).exists
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      refine ⟨‖a‖ * ‖b‖, fun φ ψ ↦ ?_⟩
      have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hx'
      have hψ := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hy'
      simp only [tensorDualForm_tmul, map_smul, norm_mul, norm_smul]
      exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) hφ)
        (mul_le_of_le_one_right (norm_nonneg _) hψ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
  | add z w hz hw =>
      obtain ⟨C, hC⟩ := hz
      obtain ⟨D, hD⟩ := hw
      exact ⟨C + D, fun φ ψ ↦ by
        rw [map_add]
        exact (norm_add_le _ _).trans (add_le_add (hC φ ψ) (hD φ ψ))⟩

-- Retain the Hausdorff assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (C.2.3.9), p. 678. Tensoring two continuous linear maps is continuous
for the injective topologies. -/
theorem injectiveTensorMap_continuous :
    Continuous (injectiveTensorMap f.toLinearMap g.toLinearMap) := by
  let M := injectiveTensorMap f.toLinearMap g.toLinearMap
  refine (withGeneratingSeminorms_spec (G ⊗[ℂ] H) _).continuous_of_continuous_comp M
    fun ⟨U, V⟩ ↦ ?_
  let U' : {U : Set E // U ∈ 𝓝 0} :=
    ⟨f ⁻¹' U.val, f.continuous.continuousAt.preimage_mem_nhds (by simpa using U.property)⟩
  let V' : {V : Set F // V ∈ 𝓝 0} :=
    ⟨g ⁻¹' V.val, g.continuous.continuousAt.preimage_mem_nhds (by simpa using V.property)⟩
  refine Seminorm.continuous_of_le
    ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U', V')) fun z ↦ ?_
  change E ⊗[ℂ] F at z
  let T := TensorProduct.map f.toLinearMap g.toLinearMap
  change injectiveTensorSeminorm U V (T z) ≤ injectiveTensorSeminorm U' V' z
  have hTarget := injectiveTensorSeminorm_bddAbove U V
  have hSource := injectiveTensorSeminorm_bddAbove U' V'
  unfold injectiveTensorSeminorm
  rw [← ciSup_prod hTarget, ← ciSup_prod hSource,
    Seminorm.iSup_apply hTarget, Seminorm.iSup_apply hSource]
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  let φ' : StrongDual.polar ℂ U'.val :=
    ⟨φ.val.comp f, (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦
      (StrongDual.mem_polar_iff ℂ _).mp φ.property (f x) hx⟩
  let ψ' : StrongDual.polar ℂ V'.val :=
    ⟨ψ.val.comp g, (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
      (StrongDual.mem_polar_iff ℂ _).mp ψ.property (g y) hy⟩
  have hform : (tensorDualForm φ.val ψ.val).comp T = tensorDualForm φ'.val ψ'.val := by
    apply TensorProduct.ext'
    intro x y
    simp [T, tensorDualForm_tmul, φ', ψ']
  change ‖tensorDualForm φ.val ψ.val (T z)‖ ≤ _
  rw [show tensorDualForm φ.val ψ.val (T z) = tensorDualForm φ'.val ψ'.val z from
    DFunLike.congr_fun hform z]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp hSource z) (φ', ψ')

omit lcE lcF lcG lcH sE sF sG sH in
/-- For a linear embedding, all functionals in a zero-neighborhood polar extend to
functionals in a common zero-neighborhood polar in the target. -/
private theorem exists_polar_extensions {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (a : X →L[ℂ] Y) (ha : IsEmbedding a) (U : {U : Set X // U ∈ 𝓝 0}) :
    ∃ V : {V : Set Y // V ∈ 𝓝 0}, ∀ φ : StrongDual.polar ℂ U.val,
      ∃ ψ : StrongDual.polar ℂ V.val, ∀ x, ψ.val (a x) = φ.val x := by
  have hnhds : 𝓝 (0 : X) = (𝓝 (0 : Y)).comap a := by
    simpa only [map_zero] using ha.isInducing.nhds_eq_comap (0 : X)
  have hU : U.val ∈ (𝓝 (0 : Y)).comap a := hnhds ▸ U.property
  obtain ⟨p, hp, hsub⟩ :=
    ((PolynormableSpace.hasBasis_zero_ball ℂ Y).comap a).mem_iff.mp hU
  refine ⟨⟨p.ball 0 1, Seminorm.ball_mem_nhds hp one_pos⟩, fun φ ↦ ?_⟩
  let e := LinearEquiv.ofInjective a.toLinearMap ha.injective
  let l := φ.val.toLinearMap.comp e.symm.toLinearMap
  have hbound (x : X) : ‖φ.val x‖ ≤ p (a x) := by
    by_contra! h
    obtain ⟨r, hr, hφ⟩ := exists_between h
    have hr₀ : 0 < r := (apply_nonneg p (a x)).trans_lt hr
    have hnorm : ‖(r : ℂ)⁻¹‖ = r⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hr₀.le]
    have hx : (r : ℂ)⁻¹ • x ∈ a ⁻¹' p.ball 0 1 := by
      change a ((r : ℂ)⁻¹ • x) ∈ p.ball 0 1
      rw [Seminorm.mem_ball_zero, map_smul, map_smul_eq_mul, hnorm,
        inv_mul_lt_iff₀ hr₀, mul_one]
      exact hr
    have hle := (StrongDual.mem_polar_iff ℂ U.val).mp φ.property _ (hsub hx)
    rw [map_smul, norm_smul, hnorm, inv_mul_le_iff₀ hr₀, mul_one] at hle
    exact (not_lt_of_ge hle) hφ
  obtain ⟨ψ, hψ, hle⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    a.toLinearMap.range l hp (fun y ↦ by
      change ‖φ.val (e.symm y)‖ ≤ p y
      have he := congrArg Subtype.val (e.apply_symm_apply y)
      change a (e.symm y) = (y : Y) at he
      rw [← he]
      exact hbound (e.symm y))
  refine ⟨⟨ψ, (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
    (hle y).trans (Seminorm.mem_ball_zero _ |>.mp hy).le⟩, fun x ↦ ?_⟩
  have heq := hψ (e x)
  change ψ (a x) = φ.val (e.symm (e x)) at heq
  simpa only [e.symm_apply_apply] using heq

/-- Paper: Lemma C.2.3.5(1), p. 678. Tensoring two embeddings gives an embedding. -/
theorem injectiveTensorMap_isEmbedding (hf : IsEmbedding f) (hg : IsEmbedding g) :
    IsEmbedding (injectiveTensorMap f.toLinearMap g.toLinearMap) := by
  let M := injectiveTensorMap f.toLinearMap g.toLinearMap
  apply IsInducing.isEmbedding
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  refine le_antisymm (tendsto_iff_comap.mp
    ((injectiveTensorMap_continuous f g).tendsto' 0 0 (map_zero M))) ?_
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf _ |>.mp
    (withGeneratingSeminorms_spec (E ⊗[ℂ] F) _)]
  refine le_iInf fun ⟨U, V⟩ ↦ ?_
  obtain ⟨U', hU'⟩ := exists_polar_extensions f hf U
  obtain ⟨V', hV'⟩ := exists_polar_extensions g hg V
  have hle (z : InjectiveTensor E F) :
      injectiveTensorSeminorm U V z ≤ injectiveTensorSeminorm U' V' (M z) := by
    change E ⊗[ℂ] F at z
    have hb := injectiveTensorSeminorm_bddAbove U V
    conv_lhs => unfold injectiveTensorSeminorm
    rw [← ciSup_prod hb, Seminorm.iSup_apply hb]
    have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    obtain ⟨φ', hφ⟩ := hU' φ
    obtain ⟨ψ', hψ⟩ := hV' ψ
    have hform : (tensorDualForm φ'.val ψ'.val).comp (TensorProduct.map
        f.toLinearMap g.toLinearMap) = tensorDualForm φ.val ψ.val := by
      apply TensorProduct.ext'
      intro x y
      simp [tensorDualForm_tmul, hφ, hψ]
    change ‖tensorDualForm φ.val ψ.val z‖ ≤ _
    rw [← DFunLike.congr_fun hform z]
    exact norm_tensorDualForm_le_injectiveTensorSeminorm U' V' φ' ψ' (M z)
  refine (NormedAddGroup.nhds_zero_basis_norm_lt.comap _).ge_iff.mpr fun r hr ↦ ?_
  refine Filter.mem_comap.mpr ⟨(injectiveTensorSeminorm U' V').ball 0 r,
    Seminorm.ball_mem_nhds
      ((withGeneratingSeminorms_spec (G ⊗[ℂ] H) _).continuous_seminorm (U', V')) hr,
    fun z hz ↦ ?_⟩
  change E ⊗[ℂ] F at z
  change ‖injectiveTensorSeminorm U V z‖ < r
  rw [Real.norm_of_nonneg (apply_nonneg _ _)]
  exact (hle z).trans_lt (Seminorm.mem_ball_zero _ |>.mp hz)

omit lcE lcF lcG lcH sE sF sG sH in
/-- A linear functional bounded by `1` on the open unit ball of a seminorm is bounded by that
seminorm everywhere. -/
private theorem norm_le_seminorm_of_forall_ball {X : Type*} [AddCommGroup X] [Module ℂ X]
    (q : Seminorm ℂ X) (φ : X →ₗ[ℂ] ℂ) (h : ∀ x, q x < 1 → ‖φ x‖ ≤ 1) (x : X) :
    ‖φ x‖ ≤ q x := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : 0 < q x + ε := by linarith [apply_nonneg q x]
  let c : ℂ := ((q x + ε)⁻¹ : ℝ)
  have hcnorm : ‖c‖ = (q x + ε)⁻¹ := by
    simp only [c, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  have hqlt : q (c • x) < 1 := by
    rw [map_smul_eq_mul, hcnorm]
    calc
      (q x + ε)⁻¹ * q x < (q x + ε)⁻¹ * (q x + ε) :=
        mul_lt_mul_of_pos_left (lt_add_of_pos_right _ hε) (inv_pos.mpr ht)
      _ = 1 := inv_mul_cancel₀ ht.ne'
  have hφ : (q x + ε)⁻¹ * ‖φ x‖ ≤ 1 := by
    have hle := h (c • x) hqlt
    rwa [map_smul, norm_smul, hcnorm] at hle
  calc
    ‖φ x‖ = (q x + ε) * ((q x + ε)⁻¹ * ‖φ x‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    _ ≤ (q x + ε) * 1 := mul_le_mul_of_nonneg_left hφ ht.le
    _ = q x + ε := mul_one _

omit lcE lcF lcH sE sF sG sH in
/-- An embedding pulls some continuous seminorm ball on the target back into a given
neighborhood of zero. -/
private theorem exists_continuous_seminorm_preimage_ball_subset (hf : IsEmbedding f)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    ∃ q : Seminorm ℂ G, Continuous q ∧ f ⁻¹' q.ball 0 1 ⊆ U := by
  have hU' : U ∈ comap f (𝓝 (0 : G)) := by
    have hcomap := hf.isInducing.nhds_eq_comap (0 : E)
    rw [map_zero] at hcomap
    rwa [hcomap] at hU
  obtain ⟨W, hW, hWU⟩ := mem_comap.mp hU'
  obtain ⟨sr, hsr, hball⟩ :=
    (PolynormableSpace.withSeminorms ℂ G).hasBasis_zero_ball.mem_iff.mp hW
  have : IsTopologicalAddGroup G :=
    (PolynormableSpace.withSeminorms ℂ G).isTopologicalAddGroup
  cases sr with
  | mk s r =>
    have hr : 0 < r := by simpa using hsr
    let q₀ : Seminorm ℂ G := s.sup fun p : {p : Seminorm ℂ G // Continuous p} => p.1
    have hq₀ : Continuous (q₀ : G → ℝ) :=
      Seminorm.continuous_finsetSup fun p (_hp : p ∈ s) => p.2
    have hsub : q₀.ball 0 r ⊆ W := by simpa using hball
    let c : NNReal := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
    have hc0 : 0 < c := by
      rw [← NNReal.coe_pos]
      change 0 < r⁻¹
      exact inv_pos.mpr hr
    refine ⟨c • q₀, ?_, ?_⟩
    · change Continuous fun y : G => (c • q₀) y
      have hmul : ∀ y, (c • q₀) y = (c : ℝ) * q₀ y := by
        intro y
        rw [smul_apply, NNReal.smul_def, smul_eq_mul]
      simp only [hmul]
      exact continuous_const.mul hq₀
    · intro x hx
      have hballEq : (c • q₀).ball 0 1 = q₀.ball 0 r := by
        rw [Seminorm.ball_smul q₀ hc0]
        apply congrArg (fun t => q₀.ball 0 t)
        calc
          (1 : ℝ) / c = (c : ℝ)⁻¹ := one_div _
          _ = (r⁻¹)⁻¹ := by congr 1
          _ = r := inv_inv r
      rw [hballEq] at hx
      exact hWU (hsub hx)

omit lcE lcF lcH sE sF sG sH in
set_option backward.isDefEq.respectTransparency false in
/-- Hahn-Banach extension of a functional dominated by a continuous seminorm along an embedding. -/
private theorem exists_dual_extension_of_le_comp (hf : IsEmbedding f) {q : Seminorm ℂ G}
    (hq : Continuous q) {φ : StrongDual ℂ E} (hφ : ∀ x, ‖φ x‖ ≤ q (f x)) :
    ∃ ψ : StrongDual ℂ G, (∀ x, ψ (f x) = φ x) ∧ ∀ y, ‖ψ y‖ ≤ q y := by
  let S : Submodule ℂ G := LinearMap.range f.toLinearMap
  let e : E ≃ₗ[ℂ] S := LinearEquiv.ofInjective f.toLinearMap hf.injective
  let φS : Module.Dual ℂ S := φ.toLinearMap.comp e.symm.toLinearMap
  have hb : ∀ s : S, ‖φS s‖ ≤ q s := by
    intro s
    have hs : f (e.symm s) = (s : G) :=
      LinearEquiv.ofInjective_symm_apply (f := f.toLinearMap) (h := hf.injective) s
    simp only [φS, LinearMap.comp_apply]
    exact (hφ (e.symm s)).trans_eq (congrArg q hs)
  obtain ⟨ψ, hψ, hle⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm S φS hq hb
  refine ⟨ψ, fun x => ?_, hle⟩
  have hcoe : (e x : G) = f x :=
    LinearEquiv.ofInjective_apply (f := f.toLinearMap) (h := hf.injective) x
  have hψx : ψ (e x) = φS (e x) := hψ (e x)
  have hφS : φS (e x) = φ x := by
    unfold φS
    rw [LinearMap.comp_apply]
    have hxs : e.symm.toLinearMap (e x) = x := by
      simp
    rw [hxs]
    rfl
  calc
    ψ (f x) = ψ (e x) := by rw [← hcoe]
    _ = φS (e x) := hψx
    _ = φ x := hφS

include lcE lcF lcG lcH in
omit sE sF sG sH in
set_option backward.isDefEq.respectTransparency false in
/-- Each injective seminorm on the source is dominated by a continuous seminorm of the tensor map. -/
private theorem injectiveTensorSeminorm_le_of_isEmbedding (hf : IsEmbedding f) (hg : IsEmbedding g)
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) :
    ∃ q : Seminorm ℂ (InjectiveTensor G H), Continuous q ∧
      ∀ z : InjectiveTensor E F,
        injectiveTensorSeminorm U V z ≤
          q (injectiveTensorMap f.toLinearMap g.toLinearMap z) := by
  obtain ⟨qG, hqG, hqGU⟩ := exists_continuous_seminorm_preimage_ball_subset f hf U.property
  obtain ⟨qH, hqH, hqHV⟩ := exists_continuous_seminorm_preimage_ball_subset g hg V.property
  let W : {W : Set G // W ∈ 𝓝 0} :=
    ⟨qG.closedBall 0 1, mem_of_superset (qG.ball_mem_nhds hqG one_pos)
      (qG.ball_subset_closedBall 0 1)⟩
  let Z : {Z : Set H // Z ∈ 𝓝 0} :=
    ⟨qH.closedBall 0 1, mem_of_superset (qH.ball_mem_nhds hqH one_pos)
      (qH.ball_subset_closedBall 0 1)⟩
  let q₀ : SeminormFamily ℂ (G ⊗[ℂ] H)
      ({W : Set G // W ∈ 𝓝 0} × {Z : Set H // Z ∈ 𝓝 0}) :=
    fun WZ => injectiveTensorSeminorm WZ.1 WZ.2
  let qFam : SeminormFamily ℂ (InjectiveTensor G H) _ := q₀
  have hqFam : WithSeminorms qFam := withGeneratingSeminorms_spec (G ⊗[ℂ] H) q₀
  refine ⟨qFam (W, Z), hqFam.continuous_seminorm (W, Z), ?_⟩
  intro z
  change injectiveTensorSeminorm U V z ≤ injectiveTensorSeminorm W Z
    ((TensorProduct.map f.toLinearMap g.toLinearMap) z)
  let T := TensorProduct.map f.toLinearMap g.toLinearMap
  refine (injectiveTensorSeminorm_le_iff U V z _).mpr fun φ hφ ψ hψ => ?_
  have hφle : ∀ x, ‖φ x‖ ≤ qG (f x) := by
    intro x
    refine norm_le_seminorm_of_forall_ball (qG.comp f.toLinearMap) φ.toLinearMap ?_ x
    intro y hy
    have hymem : y ∈ f ⁻¹' qG.ball 0 1 := by
      rw [Set.mem_preimage, Seminorm.mem_ball_zero]
      simpa [Seminorm.comp_apply] using hy
    exact (StrongDual.mem_polar_iff ℂ _).mp hφ y (hqGU hymem)
  have hψle : ∀ y, ‖ψ y‖ ≤ qH (g y) := by
    intro y
    refine norm_le_seminorm_of_forall_ball (qH.comp g.toLinearMap) ψ.toLinearMap ?_ y
    intro x hx
    have hxmem : x ∈ g ⁻¹' qH.ball 0 1 := by
      rw [Set.mem_preimage, Seminorm.mem_ball_zero]
      simpa [Seminorm.comp_apply] using hx
    exact (StrongDual.mem_polar_iff ℂ _).mp hψ x (hqHV hxmem)
  obtain ⟨α, hα, hαle⟩ := exists_dual_extension_of_le_comp f hf hqG hφle
  obtain ⟨β, hβ, hβle⟩ := exists_dual_extension_of_le_comp g hg hqH hψle
  have hαmem : α ∈ StrongDual.polar ℂ W.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun y hy => (hαle y).trans (qG.mem_closedBall_zero.mp hy)
  have hβmem : β ∈ StrongDual.polar ℂ Z.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun y hy => (hβle y).trans (qH.mem_closedBall_zero.mp hy)
  have hform : (tensorDualForm α β).comp T = tensorDualForm φ ψ := by
    apply TensorProduct.ext'
    intro x y
    simp only [T, LinearMap.comp_apply, TensorProduct.map_tmul, tensorDualForm_tmul]
    rw [show α (f.toLinearMap x) = φ x from hα x,
      show β (g.toLinearMap y) = ψ y from hβ y]
  rw [show tensorDualForm φ ψ z = tensorDualForm α β (T z) from
    (DFunLike.congr_fun hform z).symm]
  exact norm_tensorDualForm_le_injectiveTensorSeminorm W Z ⟨α, hαmem⟩ ⟨β, hβmem⟩ (T z)

/-- Paper: Lemma C.2.3.5(1), p. 678. The extension to the completions is an embedding:
a uniform embedding extends to an embedding of the completions. -/
theorem completedInjectiveTensorMap_isEmbedding (hf : IsEmbedding f) (hg : IsEmbedding g) :
    IsEmbedding (Completion.map (injectiveTensorMap f.toLinearMap g.toLinearMap)) := by
  let T := injectiveTensorMap f.toLinearMap g.toLinearMap
  have hInd : IsInducing T := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    have htend : Tendsto T (𝓝 (0 : InjectiveTensor E F)) (𝓝 (0 : InjectiveTensor G H)) := by
      simpa [map_zero] using (injectiveTensorMap_continuous f g).tendsto 0
    refine le_antisymm htend.le_comap ?_
    let p₀ : SeminormFamily ℂ (E ⊗[ℂ] F)
        ({U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0}) :=
      fun UV => injectiveTensorSeminorm UV.1 UV.2
    let p : SeminormFamily ℂ (InjectiveTensor E F) _ := p₀
    have hp : WithSeminorms p := withGeneratingSeminorms_spec (E ⊗[ℂ] F) p₀
    rw [hp.hasBasis_zero_ball.ge_iff]
    rintro ⟨s, r⟩ hr
    have hdom : ∀ i, ∃ q : Seminorm ℂ (InjectiveTensor G H), Continuous q ∧
        ∀ z, p i z ≤ q (T z) := by
      intro i
      obtain ⟨q, hq, hqle⟩ := injectiveTensorSeminorm_le_of_isEmbedding f g hf hg i.1 i.2
      exact ⟨q, hq, fun z => hqle z⟩
    classical
    choose q hqC hqle using hdom
    let Q : Seminorm ℂ (InjectiveTensor G H) := s.sup q
    have hQC : Continuous (Q : InjectiveTensor G H → ℝ) :=
      Seminorm.continuous_finsetSup fun i (_hi : i ∈ s) => hqC i
    refine mem_comap.mpr ⟨Q.ball 0 r, Q.ball_mem_nhds hQC hr, ?_⟩
    intro z hz
    have hz' : Q (T z) < r := by
      simpa [Set.mem_preimage, Seminorm.mem_ball_zero] using hz
    rw [Seminorm.mem_ball_zero]
    refine Seminorm.finset_sup_apply_lt hr fun i hi => ?_
    calc
      p i z ≤ q i (T z) := hqle i z
      _ ≤ Q (T z) := Seminorm.le_finset_sup_apply hi
      _ < r := hz'
  have hUE : IsUniformEmbedding T :=
    AddMonoidHom.isUniformEmbedding_of_isEmbedding hInd.isEmbedding
  exact (Completion.isUniformInducing_extension
      ((Completion.isUniformInducing_coe (α := InjectiveTensor G H)).comp
        hUE.isUniformInducing)).isUniformEmbedding.isEmbedding

omit lcE lcF sE sF sG sH in
open scoped Pointwise in
/-- The pure tensor map into the injective tensor product is continuous in each factor. -/
private theorem injectiveTensor_tmul_separatelyContinuous :
    (∀ x : G, Continuous (Y := InjectiveTensor G H) (fun y : H ↦ x ⊗ₜ[ℂ] y)) ∧
    (∀ y : H, Continuous (Y := InjectiveTensor G H) (fun x : G ↦ x ⊗ₜ[ℂ] y)) := by
  let : IsTopologicalAddGroup G := PolynormableSpace.isTopologicalAddGroup ℂ G
  let : IsTopologicalAddGroup H := PolynormableSpace.isTopologicalAddGroup ℂ H
  let : ContinuousSMul ℂ G := (PolynormableSpace.withSeminorms ℂ G).continuousSMul
  let : ContinuousSMul ℂ H := (PolynormableSpace.withSeminorms ℂ H).continuousSMul
  let t : G →ₗ[ℂ] H →ₗ[ℂ] InjectiveTensor G H := TensorProduct.mk ℂ G H
  have hunit (U : {U : Set G // U ∈ 𝓝 0}) (V : {V : Set H // V ∈ 𝓝 0})
      {x : G} (hx : x ∈ U.val) {y : H} (hy : y ∈ V.val) :
      injectiveTensorSeminorm U V (x ⊗ₜ[ℂ] y) ≤ 1 := by
    refine (injectiveTensorSeminorm_le_iff U V _ _).2 fun φ hφ ψ hψ ↦ ?_
    rw [tensorDualForm_tmul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ((StrongDual.mem_polar_iff ℂ _).1 hψ y hy)).trans
      ((StrongDual.mem_polar_iff ℂ _).1 hφ x hx)
  constructor
  · intro x
    change Continuous (t x)
    refine (withGeneratingSeminorms_spec (G ⊗[ℂ] H) _).continuous_of_continuous_comp (t x)
      fun ⟨U, V⟩ ↦ ?_
    obtain ⟨a, x', hx', rfl⟩ : ∃ a : ℂ, x ∈ a • U.val :=
      by simpa using (absorbent_nhds_zero (𝕜 := ℂ) U.property x).exists
    refine Seminorm.continuous' (r := ‖a‖) (Filter.mem_of_superset V.property fun y hy ↦ ?_)
    rw [Seminorm.mem_closedBall_zero]
    change injectiveTensorSeminorm U V ((a • x') ⊗ₜ[ℂ] y) ≤ ‖a‖
    rw [← TensorProduct.smul_tmul', map_smul_eq_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hunit U V hx' hy)
  · intro y
    change Continuous (t.flip y)
    refine (withGeneratingSeminorms_spec (G ⊗[ℂ] H) _).continuous_of_continuous_comp (t.flip y)
      fun ⟨U, V⟩ ↦ ?_
    obtain ⟨b, y', hy', rfl⟩ : ∃ b : ℂ, y ∈ b • V.val :=
      by simpa using (absorbent_nhds_zero (𝕜 := ℂ) V.property y).exists
    refine Seminorm.continuous' (r := ‖b‖) (Filter.mem_of_superset U.property fun x hx ↦ ?_)
    rw [Seminorm.mem_closedBall_zero]
    change injectiveTensorSeminorm U V (x ⊗ₜ[ℂ] (b • y')) ≤ ‖b‖
    rw [TensorProduct.tmul_smul, map_smul_eq_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hunit U V hx hy')

-- Retain the existing signature. Only density is needed for this conclusion.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Lemma C.2.3.5(2), p. 678. Tensoring dense embeddings gives a map with dense image. -/
theorem injectiveTensorMap_denseRange (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfd : DenseRange f) (hgd : DenseRange g) :
    DenseRange (injectiveTensorMap f.toLinearMap g.toLinearMap) := by
  let : ContinuousSMul ℂ (InjectiveTensor G H) :=
    (withGeneratingSeminorms_spec (G ⊗[ℂ] H) _).continuousSMul
  let M := injectiveTensorMap f.toLinearMap g.toLinearMap
  let S := M.range.topologicalClosure
  intro z
  change z ∈ S
  change G ⊗[ℂ] H at z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨hsecond, hfirst⟩ := injectiveTensor_tmul_separatelyContinuous (G := G) (H := H)
      refine hfd.induction_on x (M.range.isClosed_topologicalClosure.preimage (hfirst y)) fun a ↦ ?_
      refine hgd.induction_on y (M.range.isClosed_topologicalClosure.preimage (hsecond (f a))) fun b ↦ ?_
      exact M.range.le_topologicalClosure ⟨a ⊗ₜ[ℂ] b, TensorProduct.map_tmul _ _ _ _⟩
  | add z w hz hw => exact S.add_mem hz hw

end Maps

section Isometries

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
/-- Paper: Example C.2.3.4, p. 677. The injective norm is bounded by a real number exactly
when every evaluation on a pair of dual unit-ball functionals is bounded by that number. -/
private theorem injectiveTensorNorm_le_iff (z : E ⊗[ℂ] F) (r : ℝ) :
    injectiveTensorNorm E F z ≤ r ↔
      ∀ (φ : StrongDual ℂ E), ‖φ‖ ≤ 1 → ∀ (ψ : StrongDual ℂ F), ‖ψ‖ ≤ 1 →
        ‖tensorDualForm φ ψ z‖ ≤ r := by
  simpa only [injectiveTensorNorm, NormedSpace.polar_closedBall one_pos, inv_one,
    mem_closedBall_zero_iff] using injectiveTensorSeminorm_le_iff
      ⟨Metric.closedBall (0 : E) 1, Metric.closedBall_mem_nhds 0 one_pos⟩
      ⟨Metric.closedBall (0 : F) 1, Metric.closedBall_mem_nhds 0 one_pos⟩ z r

variable (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] H)

/-- Paper: Lemma C.2.3.5(1), p. 678. Tensoring isometric embeddings preserves the injective norm. -/
theorem injectiveTensorMap_isometry (z : E ⊗[ℂ] F) :
    injectiveTensorNorm G H (TensorProduct.map f.toLinearMap g.toLinearMap z) =
      injectiveTensorNorm E F z := by
  let T := TensorProduct.map f.toLinearMap g.toLinearMap
  have eval_map (Φ : StrongDual ℂ G) (Ψ : StrongDual ℂ H) :
      tensorDualForm Φ Ψ (T z) =
        tensorDualForm (Φ.comp f.toContinuousLinearMap) (Ψ.comp g.toContinuousLinearMap) z := by
    have h : (tensorDualForm Φ Ψ).comp T =
        tensorDualForm (Φ.comp f.toContinuousLinearMap) (Ψ.comp g.toContinuousLinearMap) := by
      apply TensorProduct.ext'
      intro x y
      simp [T, tensorDualForm_tmul]
    exact DFunLike.congr_fun h z
  refine le_antisymm ((injectiveTensorNorm_le_iff (T z) _).mpr ?_)
    ((injectiveTensorNorm_le_iff z _).mpr ?_)
  · intro Φ hΦ Ψ hΨ
    rw [eval_map]
    have hΦ' : ‖Φ.comp f.toContinuousLinearMap‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
        simpa using Φ.le_of_opNorm_le hΦ (f x)
    have hΨ' : ‖Ψ.comp g.toContinuousLinearMap‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by
        simpa using Ψ.le_of_opNorm_le hΨ (g y)
    exact (injectiveTensorNorm_le_iff z _).mp le_rfl _ hΦ' _ hΨ'
  · intro φ hφ ψ hψ
    obtain ⟨Φ, hΦ, hΦbound⟩ := exists_dual_extension_of_le_comp f.toContinuousLinearMap
      f.isometry.isEmbedding (q := normSeminorm ℂ G) continuous_norm (φ := φ)
      (fun x ↦ by simpa using φ.le_of_opNorm_le hφ x)
    obtain ⟨Ψ, hΨ, hΨbound⟩ := exists_dual_extension_of_le_comp g.toContinuousLinearMap
      g.isometry.isEmbedding (q := normSeminorm ℂ H) continuous_norm (φ := ψ)
      (fun y ↦ by simpa using ψ.le_of_opNorm_le hψ y)
    have hΦcomp : Φ.comp f.toContinuousLinearMap = φ := ContinuousLinearMap.ext hΦ
    have hΨcomp : Ψ.comp g.toContinuousLinearMap = ψ := ContinuousLinearMap.ext hΨ
    have h := (injectiveTensorNorm_le_iff (T z) _).mp le_rfl
      Φ (Φ.opNorm_le_bound zero_le_one (fun x ↦ by simpa using hΦbound x))
      Ψ (Ψ.opNorm_le_bound zero_le_one (fun y ↦ by simpa using hΨbound y))
    rwa [eval_map, hΦcomp, hΨcomp] at h

/-- Paper: Lemma C.2.3.5(1), p. 678. The induced map of the completions in the
injective norms is an isometry. -/
theorem completedInjectiveTensorMap_isometry :
    letI := (injectiveTensorNorm E F).toSeminormedAddCommGroup
    letI := (injectiveTensorNorm G H).toSeminormedAddCommGroup
    Isometry (Completion.map (TensorProduct.map f.toLinearMap g.toLinearMap)) := by
  let T := TensorProduct.map f.toLinearMap g.toLinearMap
  let := (injectiveTensorNorm E F).toSeminormedAddCommGroup
  let := (injectiveTensorNorm G H).toSeminormedAddCommGroup
  apply Isometry.completion_map
  exact AddMonoidHomClass.isometry_of_norm T (injectiveTensorMap_isometry f g)

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
      (Completion.toComplL : F →L[ℂ] Completion F).toLinearMap)) := by
  have : PolynormableSpace ℂ (Completion E) := polynormableSpace_completion
  have : PolynormableSpace ℂ (Completion F) := polynormableSpace_completion
  let f : E →L[ℂ] Completion E := Completion.toComplL
  let g : F →L[ℂ] Completion F := Completion.toComplL
  let T := injectiveTensorMap f.toLinearMap g.toLinearMap
  have hf : IsEmbedding f := (Completion.isUniformEmbedding_coe E).isEmbedding
  have hg : IsEmbedding g := (Completion.isUniformEmbedding_coe F).isEmbedding
  have hT : IsUniformEmbedding T :=
    AddMonoidHom.isUniformEmbedding_of_isEmbedding (injectiveTensorMap_isEmbedding f g hf hg)
  have hmap : IsUniformEmbedding (Completion.map T) :=
    (Completion.isUniformInducing_extension
      ((Completion.isUniformInducing_coe (α := InjectiveTensor (Completion E) (Completion F))).comp
        hT.isUniformInducing)).isUniformEmbedding
  have hd : DenseRange T := injectiveTensorMap_denseRange f g hf hg
    Completion.denseRange_coe Completion.denseRange_coe
  have hdmap : DenseRange (Completion.map T) := by
    apply DenseRange.of_comp
      (g := ((↑) : InjectiveTensor E F → Completion (InjectiveTensor E F)))
    simpa only [Function.comp_def, Completion.map_coe hT.uniformContinuous] using
      Completion.denseRange_coe.comp hd (Completion.continuous_coe _)
  have hclosed := hmap.isUniformInducing.isComplete_range.isClosed
  refine isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hmap.isEmbedding, fun y ↦ ?_⟩
  change y ∈ range (Completion.map T)
  rw [← hclosed.closure_eq]
  exact hdmap y

end CompletionFactors

section Associativity

variable (E F G : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [AddCommGroup G] [Module ℂ G]
  [TopologicalSpace G] [PolynormableSpace ℂ E] [T2Space E] [PolynormableSpace ℂ F] [T2Space F]
  [PolynormableSpace ℂ G] [T2Space G]

omit [T2Space E] [T2Space F] in
/-- Swapping the factors interchanges the two polar tests of every injective seminorm. -/
private theorem continuous_injectiveTensor_comm :
    @Continuous (InjectiveTensor E F) (InjectiveTensor F E) _ _ (TensorProduct.comm ℂ E F) := by
  let C : InjectiveTensor E F →ₗ[ℂ] InjectiveTensor F E := (TensorProduct.comm ℂ E F).toLinearMap
  refine (withGeneratingSeminorms_spec (F ⊗[ℂ] E) _).continuous_of_continuous_comp C
    fun ⟨V, U⟩ ↦ ?_
  refine Seminorm.continuous_of_le
    ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, V)) fun t ↦ ?_
  change injectiveTensorSeminorm V U (C t) ≤ injectiveTensorSeminorm U V t
  refine (injectiveTensorSeminorm_le_iff V U _ _).2 fun ψ hψ φ hφ ↦ ?_
  have h : (tensorDualForm ψ φ).comp C = tensorDualForm φ ψ := by
    apply TensorProduct.ext'
    intro x y
    change tensorDualForm ψ φ (y ⊗ₜ[ℂ] x) = tensorDualForm φ ψ (x ⊗ₜ[ℂ] y)
    simp only [tensorDualForm_tmul, mul_comm]
  rw [show tensorDualForm ψ φ (C t) = tensorDualForm φ ψ t from DFunLike.congr_fun h t]
  exact norm_tensorDualForm_le_injectiveTensorSeminorm U V ⟨φ, hφ⟩ ⟨ψ, hψ⟩ t

omit [T2Space E] [T2Space F] [T2Space G] in
/-- A target zero-neighborhood contains a finite intersection of injective seminorm
balls. Contracting against a functional in the first polar pulls these tests back to
injective seminorms on the source. -/
private theorem continuous_injectiveTensor_assoc :
    @Continuous (InjectiveTensor (InjectiveTensor E F) G) (InjectiveTensor E (InjectiveTensor F G))
      _ _ (TensorProduct.assoc ℂ E F G) := by
  let P := InjectiveTensor E F
  let Q := InjectiveTensor F G
  let A : InjectiveTensor P G →ₗ[ℂ] InjectiveTensor E Q := (TensorProduct.assoc ℂ E F G).toLinearMap
  refine (withGeneratingSeminorms_spec (E ⊗[ℂ] Q) _).continuous_of_continuous_comp A
    fun ⟨U, V⟩ ↦ ?_
  let p (YZ : {Y : Set F // Y ∈ 𝓝 0} × {Z : Set G // Z ∈ 𝓝 0}) :=
    injectiveTensorSeminorm YZ.1 YZ.2
  obtain ⟨⟨J, δ⟩, hδ, hJV⟩ :=
    (withGeneratingSeminorms_spec (F ⊗[ℂ] G) p).hasBasis_zero_ball.mem_iff.mp V.property
  let W (Y : {Y : Set F // Y ∈ 𝓝 0}) : {W : Set P // W ∈ 𝓝 0} :=
    ⟨(injectiveTensorSeminorm U Y).ball 0 1, Seminorm.ball_mem_nhds
      ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, Y)) one_pos⟩
  let c (φ : StrongDual ℂ E) : P →ₗ[ℂ] F := (LinearMap.applyₗ φ).comp tensorDualOperator
  have hbound (φ : StrongDual ℂ E) (hφ : φ ∈ StrongDual.polar ℂ U.val)
      (YZ : {Y : Set F // Y ∈ 𝓝 0} × {Z : Set G // Z ∈ 𝓝 0}) (t : InjectiveTensor P G) :
      p YZ ((c φ).rTensor G t) ≤ injectiveTensorSeminorm (W YZ.1) YZ.2 t := by
    refine (injectiveTensorSeminorm_le_iff YZ.1 YZ.2 _ _).2 fun ψ hψ χ hχ ↦ ?_
    have htest (x : P) : ‖tensorDualForm φ ψ x‖ ≤ injectiveTensorSeminorm U YZ.1 x :=
      norm_tensorDualForm_le_injectiveTensorSeminorm U YZ.1 ⟨φ, hφ⟩ ⟨ψ, hψ⟩ x
    let l : StrongDual ℂ P := ⟨tensorDualForm φ ψ, by
      refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
        (show P →ₗ[ℂ] ℂ from tensorDualForm φ ψ) fun _ ↦ ?_
      exact Seminorm.continuous_of_le
        ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, YZ.1)) htest⟩
    have hl : l ∈ StrongDual.polar ℂ (W YZ.1).val :=
      (StrongDual.mem_polar_iff ℂ _).2 fun x hx ↦
        (htest x).trans ((injectiveTensorSeminorm U YZ.1).mem_ball_zero.mp hx).le
    have h : (tensorDualForm ψ χ).comp ((c φ).rTensor G) = tensorDualForm l χ := by
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, tensorDualForm_tmul]
      exact congrArg (· * χ y) (tensorDualOperator_eval x φ ψ)
    rw [show tensorDualForm ψ χ ((c φ).rTensor G t) = tensorDualForm l χ t
      from DFunLike.congr_fun h t]
    exact norm_tensorDualForm_le_injectiveTensorSeminorm (W YZ.1) YZ.2 ⟨l, hl⟩ ⟨χ, hχ⟩ t
  let s (YZ : {Y : Set F // Y ∈ 𝓝 0} × {Z : Set G // Z ∈ 𝓝 0}) :
      Seminorm ℂ (InjectiveTensor P G) := injectiveTensorSeminorm (W YZ.1) YZ.2
  have hs : Continuous (J.sup s : Seminorm ℂ (InjectiveTensor P G)) :=
    Seminorm.continuous_finsetSup fun YZ _ ↦ by
      change Continuous (fun t : InjectiveTensor P G ↦ injectiveTensorSeminorm (W YZ.1) YZ.2 t)
      exact (withGeneratingSeminorms_spec (P ⊗[ℂ] G) _).continuous_seminorm (W YZ.1, YZ.2)
  apply Seminorm.continuous' (r := 1)
  refine mem_of_superset (Seminorm.ball_mem_nhds hs hδ) fun t ht ↦ ?_
  rw [Seminorm.mem_closedBall_zero]
  change injectiveTensorSeminorm U V (A t) ≤ 1
  refine (injectiveTensorSeminorm_le_iff U V _ _).2 fun φ hφ l hl ↦ ?_
  have h : (tensorDualForm φ l).comp A = l.toLinearMap.comp ((c φ).rTensor G) := by
    apply TensorProduct.ext_threefold
    intro x y z
    let yz : Q := y ⊗ₜ[ℂ] z
    change tensorDualForm φ l (x ⊗ₜ[ℂ] yz) = l (φ x • yz)
    rw [tensorDualForm_tmul, map_smul, smul_eq_mul]
  rw [show tensorDualForm φ l (A t) = l ((c φ).rTensor G t) from DFunLike.congr_fun h t]
  apply (StrongDual.mem_polar_iff ℂ _).mp hl _ (hJV ?_)
  refine (J.sup p).mem_ball_zero.mpr (Seminorm.finset_sup_apply_lt hδ fun YZ hYZ ↦ ?_)
  calc
    p YZ ((c φ).rTensor G t) ≤ s YZ t := hbound φ hφ YZ t
    _ ≤ (J.sup s) t := Seminorm.le_finset_sup_apply hYZ
    _ < δ := (J.sup s).mem_ball_zero.mp ht

-- Retain the Hausdorff assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma C.2.3.5(3), p. 678. The algebraic associator is a homeomorphism
between the two iterated injective tensor products. -/
theorem injectiveTensor_assoc :
    @IsHomeomorph (InjectiveTensor (InjectiveTensor E F) G) (InjectiveTensor E (InjectiveTensor F G))
      _ _ (TensorProduct.assoc ℂ E F G) := by
  let e : InjectiveTensor (InjectiveTensor E F) G ≃ₗ[ℂ] InjectiveTensor E (InjectiveTensor F G) :=
    TensorProduct.assoc ℂ E F G
  refine (⟨e.toEquiv, continuous_injectiveTensor_assoc E F G, ?_⟩ :
    InjectiveTensor (InjectiveTensor E F) G ≃ₜ InjectiveTensor E (InjectiveTensor F G)).isHomeomorph
  -- Reverse the reassociation by rotating the factors through outer swaps.
  let C₁ := TensorProduct.comm ℂ E (InjectiveTensor F G)
  let C₂ := TensorProduct.comm ℂ F (InjectiveTensor G E)
  let C₃ := TensorProduct.comm ℂ G (InjectiveTensor E F)
  let a₁ := TensorProduct.assoc ℂ F G E
  let a₂ := TensorProduct.assoc ℂ G E F
  let reverse := C₁.trans (a₁.trans (C₂.trans (a₂.trans C₃)))
  have hreverse : reverse.toLinearMap = e.symm.toLinearMap := by
    apply TensorProduct.ext_threefold'
    intro x y z
    rfl
  have hc := (continuous_injectiveTensor_comm G (InjectiveTensor E F)).comp
    ((continuous_injectiveTensor_assoc G E F).comp
      ((continuous_injectiveTensor_comm F (InjectiveTensor G E)).comp
        ((continuous_injectiveTensor_assoc F G E).comp
          (continuous_injectiveTensor_comm E (InjectiveTensor F G)))))
  exact hc.congr (DFunLike.congr_fun hreverse)

end Associativity

section Products

variable {I J : Type*} (E : I → Type*) (F : J → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] [∀ j, TopologicalSpace (F j)]
  [∀ i, PolynormableSpace ℂ (E i)] [∀ i, T2Space (E i)]
  [∀ j, PolynormableSpace ℂ (F j)] [∀ j, T2Space (F j)]

/-- Every functional in the polar of a product zero-neighborhood is determined by the
same finite set of coordinates. -/
private theorem product_polar_eq_sum_single {K : Type*} (X : K → Type*)
    [DecidableEq K] [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] (U : {U : Set (∀ k, X k) // U ∈ 𝓝 0}) :
    ∃ s : Finset K, ∀ φ ∈ StrongDual.polar ℂ U.val, ∀ x : ∀ k, X k,
      (∑ k ∈ s, φ (Pi.single k (x k))) = φ x := by
  have hU : U.val ∈ Filter.pi (fun k ↦ 𝓝 ((0 : ∀ k, X k) k)) := by
    simpa only [nhds_pi] using U.property
  obtain ⟨s, W, hW, hWU⟩ := Filter.mem_pi'.mp hU
  refine ⟨s, fun φ hφ x ↦ ?_⟩
  let y : ∀ k, X k := ∑ k ∈ s, Pi.single k (x k)
  have hy : ∀ k ∈ s, (x - y) k = 0 := by
    intro k hk
    dsimp only [Pi.sub_apply, y]
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem k hk, Pi.single_eq_same, sub_self]
    exact fun i _ hi ↦ Pi.single_eq_of_ne hi.symm _
  have hzero : φ (x - y) = 0 := by
    by_contra hne
    let c : ℂ := 2 / φ (x - y)
    have hmem : c • (x - y) ∈ U.val := hWU fun k hk ↦ by
      change c • (x - y) k ∈ W k
      rw [hy k hk, smul_zero]
      exact mem_of_mem_nhds (hW k)
    have hle := (StrongDual.mem_polar_iff ℂ _).mp hφ _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hle
    norm_num [Complex.norm_two] at hle
  rw [map_sub, sub_eq_zero] at hzero
  rw [← map_sum]
  exact hzero.symm

/-- The injective topology on the algebraic tensor product of products is induced by
the pairwise coordinate projections. -/
private theorem injectiveTensor_products_isUniformInducing :
    IsUniformInducing (fun (z : InjectiveTensor (∀ i, E i) (∀ j, F j)) (ij : I × J) ↦
      injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2) z) := by
  classical
  let A := InjectiveTensor (∀ i, E i) (∀ j, F j)
  let B (ij : I × J) := InjectiveTensor (E ij.1) (F ij.2)
  let P : A →ₗ[ℂ] (∀ ij, B ij) := LinearMap.pi fun ij ↦
    injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2)
  change IsUniformInducing P
  apply AddMonoidHom.isUniformInducing_of_isInducing
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  have hP : Continuous P := by
    apply continuous_pi
    intro ij
    exact injectiveTensorMap_continuous
      (ContinuousLinearMap.proj ij.1 : (∀ i, E i) →L[ℂ] E ij.1)
      (ContinuousLinearMap.proj ij.2 : (∀ j, F j) →L[ℂ] F ij.2)
  refine le_antisymm ((hP.tendsto' 0 0 (map_zero P)).le_comap) ?_
  let Neighborhoods := {U : Set (∀ i, E i) // U ∈ 𝓝 0} × {V : Set (∀ j, F j) // V ∈ 𝓝 0}
  let p : SeminormFamily ℂ A Neighborhoods := fun UV ↦ injectiveTensorSeminorm UV.1 UV.2
  have hp : WithSeminorms p := withGeneratingSeminorms_spec _ _
  rw [hp.hasBasis_zero_ball.ge_iff]
  rintro ⟨S, r⟩ hr
  have htest (UV : Neighborhoods) : {z : A | p UV z < r} ∈ comap P (𝓝 0) := by
    obtain ⟨s, hs⟩ := product_polar_eq_sum_single E UV.1
    obtain ⟨t, ht⟩ := product_polar_eq_sum_single F UV.2
    let L (ij : I × J) : B ij →ₗ[ℂ] A :=
      injectiveTensorMap (LinearMap.single ℂ E ij.1) (LinearMap.single ℂ F ij.2)
    let lift (w : ∀ ij, B ij) : A := ∑ ij ∈ s ×ˢ t, L ij (w ij)
    have hL (ij : I × J) : Continuous (L ij) :=
      injectiveTensorMap_continuous (ContinuousLinearMap.single ℂ E ij.1)
        (ContinuousLinearMap.single ℂ F ij.2)
    have hlift : Continuous lift :=
      continuous_finsetSum _ fun ij _ ↦ (hL ij).comp (continuous_apply ij)
    have hzero : lift 0 = 0 := by simp [lift]
    have hbound (z : A) : p UV z ≤ p UV (lift (P z)) := by
      refine (injectiveTensorSeminorm_le_iff UV.1 UV.2 z _).mpr fun φ hφ ψ hψ ↦ ?_
      let f := tensorDualForm φ ψ
      let A₀ := (∀ i, E i) ⊗[ℂ] (∀ j, F j)
      let project (ij : I × J) : A₀ →ₗ[ℂ] E ij.1 ⊗[ℂ] F ij.2 :=
        TensorProduct.map (LinearMap.proj ij.1) (LinearMap.proj ij.2)
      let insert (ij : I × J) : (E ij.1 ⊗[ℂ] F ij.2) →ₗ[ℂ] A₀ :=
        TensorProduct.map (LinearMap.single ℂ E ij.1) (LinearMap.single ℂ F ij.2)
      have hf : (∑ ij ∈ s ×ˢ t, f.comp ((insert ij).comp (project ij))) = f := by
        apply TensorProduct.ext'
        intro x y
        rw [LinearMap.sum_apply]
        change (∑ ij ∈ s ×ˢ t, φ (Pi.single ij.1 (x ij.1)) * ψ (Pi.single ij.2 (y ij.2))) =
          φ x * ψ y
        rw [Finset.sum_product]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, hs φ hφ x, ht ψ hψ y]
      have heval : f (lift (P z)) = f z := by
        let z₀ : A₀ := z
        change f (∑ ij ∈ s ×ˢ t, insert ij (project ij z₀)) = f z₀
        rw [map_sum]
        have hfz := DFunLike.congr_fun hf z₀
        rw [LinearMap.sum_apply] at hfz
        exact hfz
      change ‖f z‖ ≤ _
      rw [← heval]
      exact norm_tensorDualForm_le_injectiveTensorSeminorm UV.1 UV.2 ⟨φ, hφ⟩ ⟨ψ, hψ⟩ _
    refine mem_comap.mpr ⟨lift ⁻¹' (p UV).ball 0 r,
      (hlift.tendsto' 0 0 hzero).eventually
        ((p UV).ball_mem_nhds (hp.continuous_seminorm UV) hr), ?_⟩
    exact fun z hz ↦ (hbound z).trans_lt ((p UV).mem_ball_zero.mp hz)
  refine mem_of_superset ((Filter.biInter_finset_mem S).mpr fun UV _ ↦ htest UV) ?_
  exact fun z hz ↦ (S.sup p).mem_ball_zero.mpr
    (Seminorm.finset_sup_apply_lt hr fun UV hUV ↦ (mem_iInter₂.mp hz UV hUV : p UV z < r))

/-- Paper: Lemma C.2.3.6(1), p. 678. The tensor products of coordinate projections identify
the injective tensor product of finite products with the product of the pairwise tensors. -/
theorem injectiveTensor_finiteProducts [Finite I] [Finite J] :
    IsHomeomorph (fun (z : InjectiveTensor (∀ i, E i) (∀ j, F j)) (ij : I × J) ↦
      injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2) z) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  refine isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(injectiveTensor_products_isUniformInducing E F).isInducing.isEmbedding, ?_⟩
  let e := (TensorProduct.piLeft ℂ (∀ j, F j) E).trans
    (LinearEquiv.piCongrRight fun i ↦ TensorProduct.piRight ℂ ℂ (E i) F)
  have he : e.toLinearMap = LinearMap.pi (fun i ↦ LinearMap.pi fun j ↦
      TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)) := by
    apply TensorProduct.ext'
    intro x y
    funext i j
    simp [e]
  intro w
  let w' (i : I) (j : J) : E i ⊗[ℂ] F j := w (i, j)
  refine ⟨e.symm w', funext fun ij ↦ ?_⟩
  have h := DFunLike.congr_fun he (e.symm w')
  rw [LinearEquiv.coe_toLinearMap, e.apply_symm_apply] at h
  exact (congrFun (congrFun h ij.1) ij.2).symm

omit [∀ i, PolynormableSpace ℂ (E i)] [∀ i, T2Space (E i)]
  [∀ j, PolynormableSpace ℂ (F j)] [∀ j, T2Space (F j)] in
/-- A tensor can realize any prescribed finite set of pairwise tensor coordinates, so
the coordinate map has dense range in the product. -/
private theorem injectiveTensor_products_denseRange :
    DenseRange (fun (z : InjectiveTensor (∀ i, E i) (∀ j, F j)) (ij : I × J) ↦
      injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2) z) := by
  classical
  intro w
  refine mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  rw [nhds_pi] at hU
  obtain ⟨s, W, hW, hWU⟩ := Filter.mem_pi'.mp hU
  let A := (∀ i, E i) ⊗[ℂ] (∀ j, F j)
  let project (ij : I × J) : A →ₗ[ℂ] E ij.1 ⊗[ℂ] F ij.2 :=
    TensorProduct.map (LinearMap.proj ij.1) (LinearMap.proj ij.2)
  let insert (ij : I × J) : (E ij.1 ⊗[ℂ] F ij.2) →ₗ[ℂ] A :=
    TensorProduct.map (LinearMap.single ℂ E ij.1) (LinearMap.single ℂ F ij.2)
  let w₀ (ij : I × J) : E ij.1 ⊗[ℂ] F ij.2 := w ij
  let z : A := ∑ ij ∈ s, insert ij (w₀ ij)
  have hcompose (ij kl : I × J) : project ij (insert kl (w₀ kl)) =
      TensorProduct.map (LinearMap.proj ij.1 ∘ₗ LinearMap.single ℂ E kl.1)
        (LinearMap.proj ij.2 ∘ₗ LinearMap.single ℂ F kl.2) (w₀ kl) :=
    TensorProduct.map_map (LinearMap.proj ij.1 : (∀ i, E i) →ₗ[ℂ] E ij.1)
      (LinearMap.proj ij.2 : (∀ j, F j) →ₗ[ℂ] F ij.2)
      (LinearMap.single ℂ E kl.1) (LinearMap.single ℂ F kl.2) (w₀ kl)
  have hmatch (ij : I × J) (hij : ij ∈ s) : project ij z = w₀ ij := by
    simp only [z, map_sum]
    rw [Finset.sum_eq_single_of_mem ij hij]
    · rw [hcompose, LinearMap.proj_comp_single_same, LinearMap.proj_comp_single_same,
        TensorProduct.map_id, LinearMap.id_apply]
    · intro kl _ hne
      rw [hcompose]
      rcases ne_or_eq ij.1 kl.1 with h | h
      · rw [LinearMap.proj_comp_single_ne _ _ _ _ h, TensorProduct.map_zero_left,
          LinearMap.zero_apply]
      · have h' : ij.2 ≠ kl.2 := fun he ↦ hne (Prod.ext h.symm he.symm)
        rw [LinearMap.proj_comp_single_ne _ _ _ _ h', TensorProduct.map_zero_right,
          LinearMap.zero_apply]
  refine ⟨fun ij ↦ project ij z, hWU (fun ij hij ↦ ?_), ⟨z, rfl⟩⟩
  change project ij z ∈ W ij
  have hw := mem_of_mem_nhds (hW ij)
  rw [hmatch ij hij]
  exact hw

/-- Paper: Lemma C.2.3.6(2), p. 678. On completed injective tensor products the
coordinate map is a linear topological isomorphism for arbitrary products. -/
theorem completedInjectiveTensor_products :
    IsHomeomorph (fun (z : Completion (InjectiveTensor (∀ i, E i) (∀ j, F j))) (ij : I × J) ↦
      Completion.map (injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2)) z) := by
  let P (z : InjectiveTensor (∀ i, E i) (∀ j, F j)) (ij : I × J) :=
    injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2) z
  let C (w : ∀ ij : I × J, InjectiveTensor (E ij.1) (F ij.2)) (ij : I × J) :=
    (w ij : Completion (InjectiveTensor (E ij.1) (F ij.2)))
  have hP : IsUniformInducing P := injectiveTensor_products_isUniformInducing E F
  have hC : IsUniformInducing C := by
    have h (ij : I × J) := (Completion.isUniformInducing_coe
      (α := InjectiveTensor (E ij.1) (F ij.2))).comap_uniformity
    rw [isUniformInducing_iff, Pi.uniformity, Filter.comap_iInf, Pi.uniformity]
    simp_rw [Filter.comap_comap, ← h, Filter.comap_comap]
    rfl
  have hext := Completion.isUniformInducing_extension (hC.comp hP)
  have hmap : Completion.extension (C ∘ P) =
      fun z ij ↦ Completion.map (injectiveTensorMap (LinearMap.proj ij.1) (LinearMap.proj ij.2)) z := by
    refine Completion.extension_unique (hC.comp hP).uniformContinuous
      (uniformContinuous_pi.mpr fun _ ↦ Completion.uniformContinuous_map) fun z ↦ ?_
    funext ij
    rw [Completion.map_coe ((uniformContinuous_pi.mp hP.uniformContinuous) ij)]
    rfl
  rw [← hmap]
  have hd : DenseRange (C ∘ P) := (DenseRange.piMap fun _ ↦ Completion.denseRange_coe).comp
    (injectiveTensor_products_denseRange E F) hC.uniformContinuous.continuous
  have hclosed := hext.isComplete_range.isClosed
  refine isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hext.isUniformEmbedding.isEmbedding, ?_⟩
  intro y
  change y ∈ range (Completion.extension (C ∘ P))
  rw [← hclosed.closure_eq]
  refine Dense.mono ?_ hd y
  rintro w ⟨z, hz⟩
  exact ⟨(z : Completion _), (Completion.extension_coe (hC.comp hP).uniformContinuous z).trans hz⟩

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

/-- The seminorms with jointly continuous pullback at zero generate the projective topology. -/
private theorem projectiveTensor_withSeminorms (X Y : Type*)
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] :
    WithSeminorms (E := ProjectiveTensor X Y) (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val) := ⟨rfl⟩

/-- Pure tensors depend jointly continuously on their factors at zero in the projective topology. -/
private theorem continuousAt_projectiveTensor_tmul_zero (X Y : Type*)
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] :
    @ContinuousAt (X × Y) (ProjectiveTensor X Y) _ _ (fun v ↦ v.1 ⊗ₜ[ℂ] v.2) 0 := by
  let tmul : X × Y → ProjectiveTensor X Y := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
  have hzero : tmul 0 = 0 := TensorProduct.zero_tmul _ _
  change Tendsto tmul (𝓝 0) (𝓝 (tmul 0))
  rw [hzero,
    (SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp (projectiveTensor_withSeminorms X Y),
    tendsto_iInf]
  intro p
  rw [tendsto_comap_iff]
  have hp := p.property.tendsto
  change Tendsto (p.val ∘ tmul) (𝓝 0) (𝓝 (p.val (tmul 0))) at hp
  rwa [hzero, show p.val (0 : ProjectiveTensor X Y) = 0 from map_zero p.val] at hp

variable {E F} [lcE : PolynormableSpace ℂ E] [sE : T2Space E]
  [lcF : PolynormableSpace ℂ F] [sF : T2Space F]

omit sE sF in
/-- The canonical bilinear map into the projective tensor product is jointly continuous. -/
private theorem continuous_projectiveTensor_tmul :
    @Continuous (E × F) (ProjectiveTensor E F) _ _ (fun v ↦ v.1 ⊗ₜ[ℂ] v.2) := by
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : IsTopologicalAddGroup F := PolynormableSpace.isTopologicalAddGroup ℂ F
  let tmul : E × F → ProjectiveTensor E F := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
  have hzero : ContinuousAt tmul 0 := continuousAt_projectiveTensor_tmul_zero E F
  -- Scale the fixed factor into the rectangle where the generating seminorm is bounded.
  have hleft (y : F) : Continuous (fun x : E ↦ tmul (x, y)) := by
    let L : E →ₗ[ℂ] ProjectiveTensor E F := (TensorProduct.mk ℂ E F).flip y
    refine (projectiveTensor_withSeminorms E F).continuous_of_continuous_comp L fun p ↦ ?_
    let q := p.val.comp L
    have hsmall : {v : E × F | p.val (tmul v) < 1} ∈ 𝓝 ((0 : E), (0 : F)) := by
      exact p.property.preimage_mem_nhds (Iio_mem_nhds (by simp))
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hsmall
    obtain ⟨c, hc, hc_ne⟩ := ((absorbent_nhds_zero (𝕜 := ℂ) hV).eventually_nhdsNE_zero y
      |>.and eventually_mem_nhdsWithin).exists
    refine q.continuous (r := 1 / ‖c‖) (mem_of_superset hU fun x hx ↦ ?_)
    rw [Seminorm.mem_ball_zero]
    change p.val (x ⊗ₜ[ℂ] y) < 1 / ‖c‖
    have hbound := hUV (show (x, c • y) ∈ U ×ˢ V from ⟨hx, hc⟩)
    change p.val (x ⊗ₜ[ℂ] (c • y)) < 1 at hbound
    rw [TensorProduct.tmul_smul, map_smul_eq_mul] at hbound
    exact (lt_div_iff₀' (norm_pos_iff.mpr hc_ne)).mpr hbound
  have hright (x : E) : Continuous (fun y : F ↦ tmul (x, y)) := by
    let L : F →ₗ[ℂ] ProjectiveTensor E F := TensorProduct.mk ℂ E F x
    refine (projectiveTensor_withSeminorms E F).continuous_of_continuous_comp L fun p ↦ ?_
    let q := p.val.comp L
    have hsmall : {v : E × F | p.val (tmul v) < 1} ∈ 𝓝 ((0 : E), (0 : F)) := by
      exact p.property.preimage_mem_nhds (Iio_mem_nhds (by simp))
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hsmall
    obtain ⟨c, hc, hc_ne⟩ := ((absorbent_nhds_zero (𝕜 := ℂ) hU).eventually_nhdsNE_zero x
      |>.and eventually_mem_nhdsWithin).exists
    refine q.continuous (r := 1 / ‖c‖) (mem_of_superset hV fun y hy ↦ ?_)
    rw [Seminorm.mem_ball_zero]
    change p.val (x ⊗ₜ[ℂ] y) < 1 / ‖c‖
    have hbound := hUV (show (c • x, y) ∈ U ×ˢ V from ⟨hc, hy⟩)
    change p.val ((c • x) ⊗ₜ[ℂ] y) < 1 at hbound
    rw [← TensorProduct.smul_tmul', map_smul_eq_mul] at hbound
    exact (lt_div_iff₀' (norm_pos_iff.mpr hc_ne)).mpr hbound
  refine continuous_iff_continuousAt.mpr fun a ↦ ?_
  let d : E × F → E × F := fun v ↦ v - a
  have hd : ContinuousAt d a := (continuous_id.sub continuous_const).continuousAt
  have hda : d a = 0 := sub_self a
  have hdiff := hzero.comp_of_eq hd hda
  have h₁ := (hleft a.2).continuousAt.comp (continuous_fst.continuousAt.comp hd)
  have h₂ := (hright a.1).continuousAt.comp (continuous_snd.continuousAt (x := a))
  refine ((hdiff.add h₁).add h₂).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v ↦ ?_)
  change v.1 ⊗ₜ[ℂ] v.2 = ((v.1 - a.1) ⊗ₜ[ℂ] (v.2 - a.2) +
    (v.1 - a.1) ⊗ₜ[ℂ] a.2) + a.1 ⊗ₜ[ℂ] v.2
  rw [← tmul_add, sub_add_cancel, ← add_tmul, sub_add_cancel]

-- Retain the Hausdorff assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (C.2.3.14), p. 679. A linear map out of the projective tensor product is
continuous exactly when its associated bilinear map is jointly continuous. -/
theorem continuous_projectiveTensor_iff {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [PolynormableSpace ℂ G] (T : ProjectiveTensor E F →ₗ[ℂ] G) :
    Continuous T ↔ Continuous (fun v : E × F ↦ T (v.1 ⊗ₜ[ℂ] v.2)) := by
  refine ⟨fun h ↦ h.comp continuous_projectiveTensor_tmul, fun h ↦ ?_⟩
  refine (PolynormableSpace.withSeminorms ℂ G).continuous_of_continuous_comp T fun q ↦ ?_
  exact (projectiveTensor_withSeminorms E F).continuous_seminorm
    ⟨q.val.comp T, (q.property.comp h).continuousAt⟩

omit lcE sE lcF sF in
open scoped Pointwise in
/-- The absolutely convex hull of pure tensors from two zero-neighborhoods contains
the unit ball of its gauge, a defining seminorm of the projective topology. -/
private theorem projectiveTensor_hull_mem_nhds [ContinuousSMul ℂ E] [ContinuousSMul ℂ F]
    {U : Set E} {V : Set F} (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) :
    absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V) ∈ 𝓝 (0 : ProjectiveTensor E F) := by
  let C := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V)
  have htensor {x : E} {y : F} (hx : x ∈ U) (hy : y ∈ V) : x ⊗ₜ[ℂ] y ∈ C :=
    subset_absConvexHull (mem_image2_of_mem hx hy)
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : Module ℝ F := Module.restrictScalars ℝ ℂ F
  let : Module ℝ (E ⊗[ℂ] F) := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ F := IsScalarTower.restrictScalars ℝ ℂ F
  let : IsScalarTower ℝ ℂ (E ⊗[ℂ] F) := IsScalarTower.restrictScalars ℝ ℂ _
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let : ContinuousSMul ℝ F := IsScalarTower.continuousSMul ℂ
  have hconvex : Convex ℝ C := convex_absConvexHull.lift ℝ
  have habsorb : Absorbent ℝ C := by
    have hscalar : Tendsto (fun r : ℝ ↦ r) (𝓝 0) (𝓝 0) := tendsto_id
    have hscale (z : E ⊗[ℂ] F) : ∀ᶠ r : ℝ in 𝓝 0, r • z ∈ C := by
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        obtain ⟨t, ht, ht₀⟩ := ((absorbent_nhds_zero (𝕜 := ℝ) hV).eventually_nhdsNE_zero y
          |>.and eventually_mem_nhdsWithin).exists
        have hx : Tendsto (fun r : ℝ ↦ r / t) (𝓝 0) (𝓝 0) := by
          simpa only [zero_div] using hscalar.div_const t
        filter_upwards [(hx.zero_smul_const x).eventually hU] with r hr
        convert htensor hr ht using 1
        rw [← smul_tmul', tmul_smul, smul_smul, div_mul_cancel₀ _ ht₀]
      | add z w hz hw =>
        have hdouble : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝 0) (𝓝 0) := by
          simpa only [mul_zero] using hscalar.const_mul 2
        filter_upwards [hdouble.eventually hz, hdouble.eventually hw] with r hrz hrw
        have h := hconvex hrz hrw (a := 1 / 2) (b := 1 / 2)
          (by norm_num) (by norm_num) (by norm_num)
        have hhalf : (1 / 2 : ℝ) * (2 * r) = r := by ring
        simpa only [smul_smul, hhalf, ← smul_add] using h
    exact absorbent_iff_eventually_nhdsNE_zero.mpr fun z ↦ (hscale z).filter_mono nhdsWithin_le_nhds
  let p := gaugeSeminorm (𝕜 := ℂ) balanced_absConvexHull hconvex habsorb
  have hp : ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
    change Tendsto (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2))
      (𝓝 0) (𝓝 (p ((0 : E) ⊗ₜ[ℂ] (0 : F))))
    rw [zero_tmul, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt ℂ hε
    have hc₀ : c ≠ 0 := norm_pos_iff.mp hc
    have hUV : (c • U) ×ˢ V ∈ 𝓝 (0 : E × F) := by
      change _ ∈ 𝓝 ((0 : E), (0 : F))
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (by simpa using smul_mem_nhds_smul₀ hc₀ hU) hV
    refine mem_of_superset hUV ?_
    rintro ⟨_, y⟩ ⟨⟨x, hx, rfl⟩, hy⟩
    have hle : p (x ⊗ₜ[ℂ] y) ≤ 1 := gauge_le_one_of_mem (htensor hx hy)
    change dist (p ((c • x) ⊗ₜ[ℂ] y)) 0 < ε
    rw [dist_zero_right, Real.norm_of_nonneg (apply_nonneg p _), ← smul_tmul', map_smul_eq_mul]
    exact (mul_le_of_le_one_right (norm_nonneg c) hle).trans_lt hcε
  refine mem_of_superset (Seminorm.ball_mem_nhds
    ((projectiveTensor_withSeminorms E F).continuous_seminorm ⟨p, hp⟩) one_pos) ?_
  exact fun _ hz ↦
    setOfPred_gauge_lt_one_subset_self hconvex habsorb.zero_mem habsorb (p.mem_ball_zero.mp hz)

-- Retain the Hausdorff assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (C.2.3.15), p. 679. The convex circled hulls of pure tensors from pairs
of basic zero-neighborhoods form a zero-neighborhood basis. -/
theorem projectiveTensor_zero_basis {I J : Type*} {a : I → Prop} {b : J → Prop}
    {U : I → Set E} {V : J → Set F} (hU : (𝓝 0).HasBasis a U) (hV : (𝓝 0).HasBasis b V) :
    (𝓝 (0 : ProjectiveTensor E F)).HasBasis (fun ij : I × J ↦ a ij.1 ∧ b ij.2)
      (fun ij ↦ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) (U ij.1) (V ij.2))) := by
  let : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  let : ContinuousSMul ℂ F := PolynormableSpace.continuousSMul ℂ F
  have hprod : (𝓝 (0 : E × F)).HasBasis (fun ij : I × J ↦ a ij.1 ∧ b ij.2)
      (fun ij ↦ (U ij.1) ×ˢ (V ij.2)) := by
    change (𝓝 ((0 : E), (0 : F))).HasBasis _ _
    rw [nhds_prod_eq]
    exact hU.prod hV
  let tmul : E × F → ProjectiveTensor E F := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
  have htmul : Tendsto tmul (𝓝 0) (𝓝 0) := by
    have h := (continuousAt_projectiveTensor_tmul_zero E F).tendsto
    change Tendsto tmul (𝓝 0) (𝓝 (tmul 0)) at h
    rwa [show tmul 0 = 0 from zero_tmul _ _] at h
  refine (PolynormableSpace.hasBasis_zero_ball ℂ (ProjectiveTensor E F)).to_hasBasis ?_ ?_
  · intro p hp
    obtain ⟨ij, hij, hsub⟩ := hprod.mem_iff.mp (htmul.eventually (p.ball_mem_nhds hp one_pos))
    refine ⟨ij, hij, absConvexHull_min ?_
      ⟨p.balanced_ball_zero 1, convex_RCLike_iff_convex_real.mpr (p.convex_ball 0 1)⟩⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hsub (a := (x, y)) ⟨hx, hy⟩
  · intro ij hij
    exact (PolynormableSpace.hasBasis_zero_ball ℂ (ProjectiveTensor E F)).mem_iff.mp
      (projectiveTensor_hull_mem_nhds (hU.mem_of_mem hij.1) (hV.mem_of_mem hij.2))

section ProjectiveAssoc

open scoped Pointwise

private theorem convex_real_of_absConvex {X : Type*} [AddCommGroup X] [Module ℂ X]
    {S : Set X} (hS : AbsConvex ℂ S) : Convex ℝ S :=
  (convex_RCLike_iff_convex_real (K := ℂ) (E := X)).1 hS.2

private theorem balanced_real_of_balanced_complex {X : Type*} [AddCommGroup X] [Module ℂ X]
    {S : Set X} (hS : Balanced ℂ S) : Balanced ℝ S := by
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := mem_smul_set.mp hx
  have hy' : (a : ℂ) • y ∈ S :=
    hS (a : ℂ) (by simpa [Complex.norm_real] using ha) (smul_mem_smul_set hy)
  simpa [Complex.coe_smul] using hy'

/-- A linear image sends the absolutely convex hull of pure tensors into an absolutely convex set
as soon as it does so on those pure tensors. -/
private theorem image_absConvexHull_pure_subset {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] (L : X ⊗[ℂ] Y →ₗ[ℂ] Z) {U : Set X} {V : Set Y} {S : Set Z}
    (hS : AbsConvex ℂ S) (h : ∀ x ∈ U, ∀ y ∈ V, L (x ⊗ₜ[ℂ] y) ∈ S) :
    ∀ t ∈ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V), L t ∈ S := by
  have hpre : AbsConvex ℂ (L ⁻¹' S) :=
    ⟨hS.1.mulActionHom_preimage (f := L.toDistribMulActionHom.toMulActionHom), hS.2.linear_preimage L⟩
  intro t ht
  exact absConvexHull_min (by rw [image2_subset_iff]; exact h) hpre ht

/-- The seminorms whose pure-tensor pullback is continuous at zero generate the projective
topology, so a linear map out of it is continuous once that pullback is continuous at zero. -/
private theorem continuous_projectiveTensor_of_continuousAt_tmul {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    {ι : Type*} {qFam : SeminormFamily ℂ Z ι} (hq : WithSeminorms qFam)
    (T : ProjectiveTensor X Y →ₗ[ℂ] Z)
    (hT : ContinuousAt (fun v : X × Y ↦ T (v.1 ⊗ₜ[ℂ] v.2)) 0) : Continuous T := by
  let : IsTopologicalAddGroup (ProjectiveTensor X Y) :=
    (withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
      (fun r : {r : Seminorm ℂ (X ⊗[ℂ] Y) //
        ContinuousAt (fun v : X × Y ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ r.1)).isTopologicalAddGroup
  refine hq.continuous_of_continuous_comp T fun i ↦ ?_
  let fam : SeminormFamily ℂ (X ⊗[ℂ] Y)
      {r : Seminorm ℂ (X ⊗[ℂ] Y) //
        ContinuousAt (fun v : X × Y ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0} := Subtype.val
  refine (withGeneratingSeminorms_spec (X ⊗[ℂ] Y) fam).continuous_seminorm ⟨(qFam i).comp T, ?_⟩
  have hcomp : ContinuousAt (fun v : X × Y ↦ qFam i (T (v.1 ⊗ₜ[ℂ] v.2))) 0 :=
    ((hq.continuous_seminorm i).continuousAt (x := 0)).comp_of_eq hT <| by
      simp only [Prod.fst_zero, Prod.snd_zero, TensorProduct.zero_tmul]
      exact map_zero T
  change ContinuousAt (fun v : X × Y ↦ qFam i (T (v.1 ⊗ₜ[ℂ] v.2))) 0
  exact hcomp

/-- Every projective zero-neighbourhood contains the absolutely convex hull of a product of
zero-neighbourhoods of the factors. -/
private theorem projectiveTensor_nhds_superset_absConvexHull {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    {W : Set (ProjectiveTensor X Y)} (hW : W ∈ 𝓝 (0 : ProjectiveTensor X Y)) :
    ∃ U : Set X, ∃ V : Set Y, U ∈ 𝓝 (0 : X) ∧ V ∈ 𝓝 (0 : Y) ∧
      absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V) ⊆ W := by
  let ι := {p : Seminorm ℂ (X ⊗[ℂ] Y) //
    ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0}
  let fam : SeminormFamily ℂ (X ⊗[ℂ] Y) ι := Subtype.val
  have hfam := withGeneratingSeminorms_spec (X ⊗[ℂ] Y) fam
  obtain ⟨⟨s, r⟩, hr, hball⟩ := hfam.hasBasis_zero_ball.mem_iff.mp hW
  have hpure : {v : X × Y | ∀ i ∈ s, fam i (v.1 ⊗ₜ[ℂ] v.2) < r} ∈ 𝓝 (0 : X × Y) := by
    rw [← Filter.eventually_iff, Finset.eventually_all s]
    intro i _hi
    have hcont : Tendsto (fun v : X × Y ↦ fam i (v.1 ⊗ₜ[ℂ] v.2)) (𝓝 0) (𝓝 0) := by
      simpa [ContinuousAt, Prod.fst_zero, Prod.snd_zero, TensorProduct.zero_tmul, map_zero] using
        (i.property : ContinuousAt (fun v : X × Y ↦ fam i (v.1 ⊗ₜ[ℂ] v.2)) 0)
    rw [tendsto_def] at hcont
    exact Filter.eventually_iff.mpr (hcont (Iio r) (Iio_mem_nhds hr))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpure
  let q : Seminorm ℂ (X ⊗[ℂ] Y) := s.sup fam
  refine ⟨U, V, hU, hV, (absConvexHull_min ?_ ?_).trans hball⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_image2.mp hz
    have hlt : ∀ i ∈ s, fam i (x ⊗ₜ[ℂ] y) < r := hUV (a := (x, y)) ⟨hx, hy⟩
    change (s.sup fam) (x ⊗ₜ[ℂ] y) < r
    exact Seminorm.finset_sup_apply_lt hr hlt
  · exact ⟨q.balanced_ball_zero r,
      (convex_RCLike_iff_convex_real (K := ℂ)).2 (q.convex_ball 0 r)⟩

/-- Absolutely convex hulls of products of zero-neighbourhoods are projective zero-neighbourhoods. -/
private theorem projectiveTensor_absConvexHull_mem_nhds {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    {U : Set X} {V : Set Y} (hU : U ∈ 𝓝 (0 : X)) (hV : V ∈ 𝓝 (0 : Y)) :
    absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V) ∈ 𝓝 (0 : ProjectiveTensor X Y) := by
  let : ContinuousSMul ℝ X := MulAction.continuousSMul_compHom
    (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal
  let : ContinuousSMul ℝ Y := MulAction.continuousSMul_compHom
    (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal
  obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ X).mem_iff.mp hU
  obtain ⟨q, hq, hqV⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ Y).mem_iff.mp hV
  let U0 := p.ball 0 1
  let V0 := q.ball 0 1
  let S : Set (ProjectiveTensor X Y) :=
    absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U0 V0)
  have hU0 : U0 ∈ 𝓝 (0 : X) := p.ball_mem_nhds hp one_pos
  have hV0 : V0 ∈ 𝓝 (0 : Y) := q.ball_mem_nhds hq one_pos
  have hAbs : AbsConvex ℂ S := absConvex_absConvexHull
  have hConv : Convex ℝ S := convex_real_of_absConvex hAbs
  have hBal : Balanced ℝ S := balanced_real_of_balanced_complex hAbs.1
  have h0 : (0 : ProjectiveTensor X Y) ∈ S := subset_absConvexHull
    ⟨0, by simp [U0], 0, by simp [V0],
      TensorProduct.zero_tmul _ _⟩
  have hSabs : Absorbent ℝ S := by
    intro z
    suffices h : ∃ r : ℝ, 0 < r ∧ z ∈ r • S by
      obtain ⟨r, hr, hz⟩ := h
      exact Absorbs.of_norm ⟨r, fun a ha ↦ singleton_subset_iff.mpr
        (hBal.smul_mono (by rwa [Real.norm_of_nonneg hr.le]) hz)⟩
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨r, hr, u, hu, rfl⟩ :=
        (absorbent_nhds_zero (𝕜 := ℝ) hU0).gauge_set_nonempty (x := x)
      obtain ⟨s, hs, v, hv, rfl⟩ :=
        (absorbent_nhds_zero (𝕜 := ℝ) hV0).gauge_set_nonempty (x := y)
      refine ⟨r * s, mul_pos hr hs, u ⊗ₜ[ℂ] v, subset_absConvexHull ⟨u, hu, v, hv, rfl⟩, ?_⟩
      change ((r * s : ℝ) : ℂ) • (u ⊗ₜ[ℂ] v) = ((r : ℂ) • u) ⊗ₜ[ℂ] ((s : ℂ) • v)
      rw [Complex.ofReal_mul, TensorProduct.smul_tmul_smul]
    | add z w hz hw =>
      obtain ⟨r, hr, hz⟩ := hz
      obtain ⟨s, hs, hw⟩ := hw
      exact ⟨r + s, add_pos hr hs, hConv.add_smul hr.le hs.le ▸ add_mem_add hz hw⟩
  let g := gaugeSeminorm hAbs.1 hConv hSabs
  have hg_eq (z : ProjectiveTensor X Y) : g z = gauge S z := by
    simp [g, gaugeSeminorm, Seminorm.of]
    rfl
  have hAt : ContinuousAt (fun v : X × Y ↦ g (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
    rw [ContinuousAt]
    have hlim : g ((0 : X) ⊗ₜ[ℂ] (0 : Y)) = 0 := by
      rw [TensorProduct.zero_tmul]; exact map_zero g
    simp only [Prod.fst_zero, Prod.snd_zero, hlim]
    rw [Metric.tendsto_nhds]
    intro ε hε
    refine mem_of_superset (prod_mem_nhds (p.ball_mem_nhds hp (half_pos hε))
        (q.ball_mem_nhds hq one_pos)) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_ofPred, Real.dist_0_eq_abs]
    let c : ℂ := (ε / 2 : ℝ)
    have hc0 : c ≠ 0 := by
      change (ε / 2 : ℝ) ≠ (0 : ℂ)
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    have hnorm : ‖c‖ = ε / 2 := by
      have hε2 : 0 ≤ ε / 2 := by positivity
      rw [show c = ((ε / 2 : ℝ) : ℂ) by simp [c], Complex.norm_real, Real.norm_of_nonneg hε2]
    have hx' : p (c⁻¹ • x) < 1 := by
      rw [Seminorm.mem_ball_zero] at hx
      rw [map_smul_eq_mul, norm_inv, hnorm, inv_mul_lt_iff₀ (by positivity)]
      simpa using hx
    have hy' : q y < 1 := by
      rw [Seminorm.mem_ball_zero] at hy
      exact hy
    have hmem : (c⁻¹ • x) ⊗ₜ[ℂ] y ∈ S :=
      subset_absConvexHull ⟨_, (p.mem_ball_zero).mpr hx', _, (q.mem_ball_zero).mpr hy', rfl⟩
    have hle : g ((c⁻¹ • x) ⊗ₜ[ℂ] y) ≤ 1 :=
      (hg_eq _).trans_le (gauge_le_one_of_mem hmem)
    have hscale : x ⊗ₜ[ℂ] y = c • ((c⁻¹ • x) ⊗ₜ[ℂ] y) := by
      rw [← TensorProduct.smul_tmul', smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [hscale]
    have hpull : g (c • ((c⁻¹ • x) ⊗ₜ[ℂ] y)) = ‖c‖ * g ((c⁻¹ • x) ⊗ₜ[ℂ] y) :=
      map_smul_eq_mul g c ((c⁻¹ • x) ⊗ₜ[ℂ] y)
    rw [hpull, hnorm]
    have hnonneg : 0 ≤ ε / 2 * g ((c⁻¹ • x) ⊗ₜ[ℂ] y) :=
      mul_nonneg (by positivity) (apply_nonneg g _)
    rw [abs_of_nonneg hnonneg]
    exact (mul_le_of_le_one_right (by positivity) hle).trans_lt (half_lt_self hε)
  let fam : SeminormFamily ℂ (X ⊗[ℂ] Y)
      {r : Seminorm ℂ (X ⊗[ℂ] Y) //
        ContinuousAt (fun v : X × Y ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0} := Subtype.val
  have hg : Continuous (g : ProjectiveTensor X Y → ℝ) :=
    (withGeneratingSeminorms_spec (X ⊗[ℂ] Y) fam).continuous_seminorm ⟨g, hAt⟩
  have hball : g.ball 0 1 ⊆ S := by
    intro z hz
    rw [Seminorm.mem_ball_zero] at hz
    exact setOfPred_gauge_lt_one_subset_self hConv h0 hSabs (by
      rw [Set.mem_ofPred, ← hg_eq]
      simpa [Seminorm.mem_ball_zero] using hz)
  exact mem_of_superset (mem_of_superset (g.ball_mem_nhds hg one_pos) hball)
    (absConvexHull_mono (image2_subset hpU hqV))

end ProjectiveAssoc

omit sE sF in
private theorem continuousAt_projective_assoc_reassoc {G : Type*}
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] :
    @ContinuousAt (ProjectiveTensor E F × G) (ProjectiveTensor E (ProjectiveTensor F G)) _ _
      ((TensorProduct.assoc ℂ E F G :
        ProjectiveTensor (ProjectiveTensor E F) G → ProjectiveTensor E (ProjectiveTensor F G)) ∘
      fun v : ProjectiveTensor E F × G ↦ v.1 ⊗ₜ[ℂ] v.2) 0 := by
  rw [ContinuousAt, tendsto_def]
  intro W hW
  obtain ⟨U, A, hU, hA, hUA⟩ :=
    projectiveTensor_nhds_superset_absConvexHull (X := E) (Y := ProjectiveTensor F G) hW
  obtain ⟨V, B, hV, hB, hVB⟩ :=
    projectiveTensor_nhds_superset_absConvexHull (X := F) (Y := G) hA
  refine mem_of_superset (prod_mem_nhds
      (projectiveTensor_absConvexHull_mem_nhds (X := E) (Y := F) hU hV) hB) ?_
  rintro ⟨t, g⟩ ⟨ht, hg⟩
  apply hUA
  refine image_absConvexHull_pure_subset
      ((TensorProduct.assoc ℂ E F G).toLinearMap.comp
        ((TensorProduct.mk ℂ (E ⊗[ℂ] F) G).flip g))
      absConvex_absConvexHull ?_ t ht
  intro x hx y hy
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  refine subset_absConvexHull ⟨x, hx, y ⊗ₜ[ℂ] g, ?_, rfl⟩
  exact hVB (subset_absConvexHull ⟨y, hy, g, hg, rfl⟩)

omit lcE sE sF in
private theorem continuousAt_projective_assoc_symm_reassoc {G : Type*}
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] :
    @ContinuousAt (E × ProjectiveTensor F G) (ProjectiveTensor (ProjectiveTensor E F) G) _ _
      (((TensorProduct.assoc ℂ E F G).symm :
        ProjectiveTensor E (ProjectiveTensor F G) → ProjectiveTensor (ProjectiveTensor E F) G) ∘
      fun v : E × ProjectiveTensor F G ↦ v.1 ⊗ₜ[ℂ] v.2) 0 := by
  rw [ContinuousAt, tendsto_def]
  intro W hW
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    projectiveTensor_nhds_superset_absConvexHull (X := ProjectiveTensor E F) (Y := G) hW
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    projectiveTensor_nhds_superset_absConvexHull (X := E) (Y := F) hA
  refine mem_of_superset (prod_mem_nhds hU
      (projectiveTensor_absConvexHull_mem_nhds (X := F) (Y := G) hV hB)) ?_
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  apply hAB
  refine image_absConvexHull_pure_subset
      ((TensorProduct.assoc ℂ E F G).symm.toLinearMap.comp
        (TensorProduct.mk ℂ E (F ⊗[ℂ] G) x))
      absConvex_absConvexHull ?_ z hz
  intro y hy g hg
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
  refine subset_absConvexHull ⟨x ⊗ₜ[ℂ] y, ?_, g, hg, rfl⟩
  exact hUV (subset_absConvexHull ⟨x, hx, y, hy, rfl⟩)

/-- Paper: §C.2.3.2, p. 679. Rebracketing the projective tensor product is a linear
topological isomorphism. -/
theorem projectiveTensor_assoc {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [PolynormableSpace ℂ G] [T2Space G] :
    @IsHomeomorph (ProjectiveTensor (ProjectiveTensor E F) G)
      (ProjectiveTensor E (ProjectiveTensor F G)) _ _ (TensorProduct.assoc ℂ E F G) := by
  let e : ProjectiveTensor (ProjectiveTensor E F) G ≃
      ProjectiveTensor E (ProjectiveTensor F G) :=
    { toFun := TensorProduct.assoc ℂ E F G
      invFun := (TensorProduct.assoc ℂ E F G).symm
      left_inv := (TensorProduct.assoc ℂ E F G).left_inv
      right_inv := (TensorProduct.assoc ℂ E F G).right_inv }
  let famRight : SeminormFamily ℂ (ProjectiveTensor E (ProjectiveTensor F G))
      {r : Seminorm ℂ (E ⊗[ℂ] ProjectiveTensor F G) //
        ContinuousAt (fun v : E × ProjectiveTensor F G ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0} :=
    Subtype.val
  let famLeft : SeminormFamily ℂ (ProjectiveTensor (ProjectiveTensor E F) G)
      {r : Seminorm ℂ (ProjectiveTensor E F ⊗[ℂ] G) //
        ContinuousAt (fun v : ProjectiveTensor E F × G ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0} :=
    Subtype.val
  refine e.isHomeomorph_iff.mpr ⟨?_, ?_⟩
  · exact continuous_projectiveTensor_of_continuousAt_tmul
      (X := ProjectiveTensor E F) (Y := G) (withGeneratingSeminorms_spec _ famRight)
      (TensorProduct.assoc ℂ E F G).toLinearMap continuousAt_projective_assoc_reassoc
  · exact continuous_projectiveTensor_of_continuousAt_tmul
      (X := E) (Y := ProjectiveTensor F G) (withGeneratingSeminorms_spec _ famLeft)
      (TensorProduct.assoc ℂ E F G).symm.toLinearMap
      continuousAt_projective_assoc_symm_reassoc

/-- Paper: §C.2.3.2, p. 679. The projective tensor product of Hausdorff factors is Hausdorff. -/
@[instance]
theorem projectiveTensor_t2 : T2Space (ProjectiveTensor E F) := by
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let : SeparatingDual ℂ F := polynormableSpace_separatingDual ℂ F
  let eval : ProjectiveTensor E F → (StrongDual ℂ E × StrongDual ℂ F → ℂ) :=
    fun z v ↦ tensorDualForm v.1 v.2 z
  refine T2Space.of_injective_continuous (f := eval)
    (fun _ _ h ↦ tensorDualForm_ext fun φ ψ ↦ congrFun h (φ, ψ)) ?_
  refine continuous_pi fun v ↦ (continuous_projectiveTensor_iff
    (tensorDualForm v.1 v.2 : ProjectiveTensor E F →ₗ[ℂ] ℂ)).2 ?_
  exact ((v.1.continuous.comp continuous_fst).mul (v.2.continuous.comp continuous_snd)).congr
    fun xy ↦ (tensorDualForm_tmul v.1 v.2 xy.1 xy.2).symm

-- TODO(paper-gap): The claimed projective analogue of Lemma C.2.3.5 on p. 679 fails
-- for embeddings. Even finite-dimensional isometric inclusions can lose isometry.

omit lcE sE lcF sF [TopologicalSpace E] [TopologicalSpace F] in
open scoped Pointwise in
/-- A tensor in a scaled absolutely convex hull has a finite expansion with coefficient
norms totaling at most the norm of the scale. -/
private theorem projectiveTensor_finite_expansion {U : Set E} {V : Set F}
    (r : ℂ) {w : E ⊗[ℂ] F}
    (hw : w ∈ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V)) :
    ∃ (k : ℕ) (c : Fin k → ℂ) (x : Fin k → E) (y : Fin k → F),
      (∀ i, x i ∈ U ∧ y i ∈ V) ∧ (∑ i, ‖c i‖) ≤ ‖r‖ ∧
        (∑ i, c i • (x i ⊗ₜ[ℂ] y i)) = r • w := by
  classical
  let T := E ⊗[ℂ] F
  let : Module ℝ T := Module.restrictScalars ℝ ℂ T
  let : IsScalarTower ℝ ℂ T := IsScalarTower.restrictScalars ℝ ℂ T
  let S : Set T := image2 (TensorProduct.tmul ℂ) U V
  change (w : T) ∈ absConvexHull ℂ S at hw
  rw [absConvexHull_eq_convexHull_balancedHull] at hw
  have hsub : convexHull ℂ (balancedHull ℂ S) ⊆ convexHull ℝ (balancedHull ℂ S) :=
    convexHull_min (subset_convexHull ℝ _) ((convex_RCLike_iff_convex_real (K := ℂ)).mpr
      (convex_convexHull ℝ _))
  have hw' := hsub hw
  obtain ⟨ι, hι, a, t, ha, hasum, ht, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hw'
  let := hι
  choose b hb ht' using fun i ↦ mem_balancedHull_iff.mp (ht i)
  choose u hu htu using fun i ↦ mem_smul_set.mp (ht' i)
  choose x hx y hy hxy using fun i ↦ mem_image2.mp (hu i)
  let e := (Fintype.equivFin ι).symm
  let c (i : ι) := r * (a i : ℂ) * b i
  refine ⟨Fintype.card ι, c ∘ e, x ∘ e, y ∘ e, fun i ↦ ⟨hx _, hy _⟩, ?_, ?_⟩
  · rw [show (∑ i, ‖(c ∘ e) i‖) = ∑ i, ‖c i‖ from e.sum_comp (fun i ↦ ‖c i‖)]
    calc
      ∑ i, ‖c i‖ ≤ ∑ i, ‖r‖ * a i := Finset.sum_le_sum fun i _ ↦ by
        rw [show ‖c i‖ = ‖r‖ * a i * ‖b i‖ by
          simp [c, Complex.norm_real, Real.norm_of_nonneg (ha i)]]
        exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (ha i)) (hb i)
      _ = ‖r‖ := by rw [← Finset.mul_sum, hasum, mul_one]
  · rw [show (∑ i, (c ∘ e) i • ((x ∘ e) i ⊗ₜ[ℂ] (y ∘ e) i)) =
        ∑ i, c i • (x i ⊗ₜ[ℂ] y i) from e.sum_comp (fun i ↦ c i • (x i ⊗ₜ[ℂ] y i))]
    calc
      ∑ i, c i • (x i ⊗ₜ[ℂ] y i) = ∑ i, r • (a i • t i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hxy i, ← htu i]
        change (r * (a i : ℂ) * b i) • u i = r • ((a i : ℂ) • (b i • u i))
        simp only [mul_smul]
      _ = r • (∑ i, a i • t i) := Finset.smul_sum.symm
      _ = r • (w : T) := congrArg (fun v : T ↦ r • v) hsum

omit lcE sE lcF sF in
/-- A point in the completion can be approximated so that each successive difference lies
in a prescribed zero-neighborhood of the algebraic projective tensor. -/
private theorem projectiveTensor_controlled_approximation
    (z : Completion (ProjectiveTensor E F)) {W A : ℕ → Set (ProjectiveTensor E F)}
    (hW : (𝓝 0).HasAntitoneBasis W) (hA : ∀ n, A n ∈ 𝓝 0) :
    ∃ a : ℕ → ProjectiveTensor E F, Tendsto (fun n ↦ Completion.coe' (a n)) atTop (𝓝 z) ∧
      ∀ n, a (n + 1) - a n ∈ A n := by
  let T := ProjectiveTensor E F
  let j : T →+ Completion T := Completion.toCompl
  have hj : IsDenseInducing j := Completion.isDenseInducing_coe
  have hlift (n : ℕ) : ∃ P ∈ 𝓝 (0 : Completion T), j ⁻¹' P ⊆ A n := by
    have h := hA n
    rw [hj.nhds_eq_comap, map_zero j, mem_comap] at h
    exact h
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
  have hnear (n : ℕ) : ∃ a : T, j a - z ∈ D n ∩ D (n - 1) := by
    change ∃ a : T, j a ∈ (fun q : Completion T ↦ q - z) ⁻¹' (D n ∩ D (n - 1))
    apply hj.dense.mem_nhds (x := z)
    rw [← nhds_translation_sub z]
    exact preimage_mem_comap (inter_mem (hD n) (hD (n - 1)))
  choose a ha using hnear
  refine ⟨a, tendsto_sub_nhds_zero_iff.mp ?_, fun n ↦ hPA n ?_⟩
  · refine tendsto_def.mpr fun S hS ↦ ?_
    obtain ⟨C, hC, hc, hCS⟩ := exists_mem_nhds_isClosed_subset hS
    have hpre : j ⁻¹' C ∈ 𝓝 (0 : T) :=
      Completion.continuous_toCompl.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using hC)
    obtain ⟨N, hN⟩ := hW.mem_iff.mp hpre
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ hCS (closure_minimal ?_ hc (hcl n (ha n).1))⟩
    exact image_subset_iff.mpr ((hW.antitone hn).trans hN)
  · change j (a (n + 1) - a n) ∈ P n
    rw [map_sub, ← sub_sub_sub_cancel_right (j (a (n + 1))) (j (a n)) z]
    exact hsub n _ (by simpa using (ha (n + 1)).2) _ (ha n).1

omit sE sF in
/-- Absolutely summable coefficients give a summable series of pure tensors when both
families of factors tend to zero along the cofinite filter. -/
private theorem completedProjectiveTensor_summable_cofinite {ι : Type*}
    (c : ι → ℂ) (x : ι → E) (y : ι → F) (hc : Summable (fun i ↦ ‖c i‖))
    (hxy : Tendsto (fun i ↦ (x i, y i)) cofinite (𝓝 0)) :
    Summable (fun i ↦ (Completion.coe' (α := ProjectiveTensor E F) (c i • (x i ⊗ₜ[ℂ] y i)))) := by
  let T := ProjectiveTensor E F
  let t (i : ι) : T := x i ⊗ₜ[ℂ] y i
  have ht : Tendsto t cofinite (𝓝 0) := by
    have h := (continuous_projectiveTensor_tmul (E := E) (F := F)).continuousAt (x := 0)
    have h' := h.tendsto.comp hxy
    rw [show ((0 : E × F).1 ⊗ₜ[ℂ] (0 : E × F).2 : ProjectiveTensor E F) = 0 from
      zero_tmul _ _] at h'
    exact h'
  apply summable_iff_cauchySeq_finset.mpr
  suffices h : CauchySeq (fun s : Finset ι ↦ ∑ i ∈ s, c i • t i) by
    have h' : CauchySeq (fun s : Finset ι ↦ Completion.toCompl (∑ i ∈ s, c i • t i)) :=
      (Completion.uniformContinuous_coe T).comp_cauchySeq h
    simp only [map_sum] at h'
    exact h'
  refine cauchySeq_finset_iff_sum_vanishing.mpr fun S hS ↦ ?_
  obtain ⟨p, hp, hpS⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ T).mem_iff.mp hS
  have hpt : Tendsto (fun i ↦ p (t i)) cofinite (𝓝 0) :=
    (hp.tendsto' 0 0 (map_zero p)).comp ht
  obtain ⟨M, hM⟩ := hpt.bddAbove_range_of_cofinite
  have hmajor := hc.mul_left (max M 0)
  obtain ⟨s, hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp (summable_iff_cauchySeq_finset.mp hmajor)
    (Iio 1) (Iio_mem_nhds zero_lt_one)
  refine ⟨s, fun u hu ↦ hpS (p.mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
  calc
    p (∑ i ∈ u, c i • t i) ≤ ∑ i ∈ u, p (c i • t i) :=
      Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
    _ ≤ ∑ i ∈ u, max M 0 * ‖c i‖ := Finset.sum_le_sum fun i _ ↦ by
      rw [map_smul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hM (mem_range_self i)).trans (le_max_left _ _)) (norm_nonneg _)

/-- Paper: (C.2.3.16), p. 679. Every member of the completed projective tensor of Fréchet
spaces is an absolutely weighted sum of pure tensors from two null sequences.
Deviation: The sequences are reindexed from zero. -/
theorem completedProjectiveTensor_exists_series (hE : IsFrechetTVS E) (hF : IsFrechetTVS F)
    (z : Completion (ProjectiveTensor E F)) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F), Summable (fun n ↦ ‖c n‖) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasSum (fun n ↦ (Completion.coe' (α := ProjectiveTensor E F) (c n • (x n ⊗ₜ[ℂ] y n)))) z := by
  classical
  let : MetrizableSpace E := hE.2.2.1
  let : MetrizableSpace F := hF.2.2.1
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 (0 : F)).exists_antitone_basis
  let T := ProjectiveTensor E F
  let j : T →+ Completion T := Completion.toCompl
  let W (n : ℕ) : Set T := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) (U n) (V n))
  have hmono {m n : ℕ} (hmn : m ≤ n) : W n ⊆ W m :=
    absConvexHull_mono (image2_subset (hU.antitone hmn) (hV.antitone hmn))
  have hW : (𝓝 (0 : T)).HasAntitoneBasis W := by
    refine ⟨(projectiveTensor_zero_basis hU.1 hV.1).to_hasBasis ?_ ?_, fun _ _ ↦ hmono⟩
    · rintro ⟨i, k⟩ _
      exact ⟨max i k, trivial,
        absConvexHull_mono (image2_subset (hU.antitone (le_max_left _ _)) (hV.antitone (le_max_right _ _)))⟩
    · exact fun n _ ↦ ⟨(n, n), ⟨trivial, trivial⟩, Subset.rfl⟩
  let r (n : ℕ) : ℂ := (1 / 2) ^ n
  have hr (n : ℕ) : r n ≠ 0 := by
    change ((1 / 2 : ℂ) ^ n) ≠ 0
    positivity
  let A (n : ℕ) : Set T := (fun w : T ↦ (r n)⁻¹ • w) ⁻¹' W n
  let : ContinuousSMul ℂ T := PolynormableSpace.continuousSMul ℂ T
  have hA (n : ℕ) : A n ∈ 𝓝 (0 : T) :=
    (continuous_const_smul (r n)⁻¹).continuousAt.preimage_mem_nhds (by
      rw [smul_zero]
      exact hW.1.mem_of_mem (i := n) trivial)
  obtain ⟨a, ha, hadiff⟩ := projectiveTensor_controlled_approximation z hW hA
  let b : ℕ → T := fun n ↦ Nat.casesOn n 0 a
  have hb : Tendsto (fun n ↦ j (b n)) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).mp ha
  -- The first approximant contributes one unrestricted finite block.
  have hblocks (n : ℕ) : ∃ (k : ℕ) (c : Fin k → ℂ) (x : Fin k → E) (y : Fin k → F),
      (∀ m, n = m + 1 → (∀ i, x i ∈ U m ∧ y i ∈ V m) ∧ (∑ i, ‖c i‖) ≤ ‖r m‖) ∧
        (∑ i, c i • (x i ⊗ₜ[ℂ] y i) : T) = b (n + 1) - b n := by
    cases n with
    | zero =>
      obtain ⟨k, x, y, h⟩ := TensorProduct.exists_sum_tmul_eq (a 0)
      refine ⟨k, fun _ ↦ 1, x, y, by simp, ?_⟩
      simp only [one_smul]
      change (∑ i, x i ⊗ₜ[ℂ] y i) = a 0 - (0 : T)
      rw [sub_zero]
      exact h.symm
    | succ n =>
      let w : E ⊗[ℂ] F := a (n + 1) - a n
      obtain ⟨k, c, x, y, hxy, hnorm, hsum⟩ :=
        projectiveTensor_finite_expansion (r n) (w := (r n)⁻¹ • w) (hadiff n)
      refine ⟨k, c, x, y, fun m hm ↦ ?_, ?_⟩
      · obtain rfl : n = m := Nat.succ.inj hm
        exact ⟨hxy, hnorm⟩
      · exact hsum.trans (smul_inv_smul₀ (hr n) w)
  choose k c x y hsmall hsum using hblocks
  let ι := Σ n, Fin (k n)
  let coeff (i : ι) := c i.1 i.2
  let left (i : ι) := x i.1 i.2
  let right (i : ι) := y i.1 i.2
  have hc : Summable (fun i ↦ ‖coeff i‖) := by
    refine (summable_sigma_of_nonneg (fun i ↦ norm_nonneg (coeff i))).mpr ⟨fun n ↦ (hasSum_fintype _).summable, ?_⟩
    apply (summable_nat_add_iff 1).mp
    simp only [tsum_fintype]
    have hrSum : Summable (fun n ↦ ‖r n‖) := by
      simp only [r, norm_pow]
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_of_nonneg (norm_nonneg (_ : ℂ)), norm_div, norm_one]
      norm_num
    exact hrSum.of_nonneg_of_le
      (fun n ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _) (fun n ↦ (hsmall (n + 1) n rfl).2)
  have hindex : Tendsto (Sigma.fst : ι → ℕ) cofinite atTop := by
    refine tendsto_atTop.mpr fun N ↦ eventually_cofinite.mpr ?_
    refine ((finite_lt_nat N).biUnion
      (t := fun n ↦ range (fun i : Fin (k n) ↦ (⟨n, i⟩ : ι))) fun n _ ↦ finite_range _).subset ?_
    rintro ⟨n, i⟩ hi
    exact mem_iUnion₂.mpr ⟨n, Nat.lt_of_not_ge hi, i, rfl⟩
  have hxy : Tendsto (fun i ↦ (left i, right i)) cofinite (𝓝 0) := by
    rw [show (0 : E × F) = (0, 0) from rfl, nhds_prod_eq]
    refine (hU.1.prod hV.1).tendsto_right_iff.mpr ?_
    rintro ⟨N, M⟩ _
    filter_upwards [tendsto_atTop.mp hindex (max N M + 1)] with i hi
    rcases i with ⟨_ | n, i⟩
    · exact (Nat.not_succ_le_zero _ hi).elim
    · have hn := Nat.le_of_succ_le_succ hi
      obtain ⟨hx, hy⟩ := (hsmall (n + 1) n rfl).1 i
      exact ⟨hU.antitone ((le_max_left N M).trans hn) hx,
        hV.antitone ((le_max_right N M).trans hn) hy⟩
  let f (i : ι) := j (coeff i • (left i ⊗ₜ[ℂ] right i))
  have hf : Summable f := completedProjectiveTensor_summable_cofinite coeff left right hc hxy
  have hfiber (n : ℕ) : HasSum (fun i ↦ f ⟨n, i⟩) (j (b (n + 1)) - j (b n)) := by
    rw [← map_sub, ← hsum n]
    let g (i : Fin (k n)) : T := c n i • (x n i ⊗ₜ[ℂ] y n i)
    change HasSum (fun i ↦ j (g i)) (j (∑ i, g i))
    rw [map_sum]
    exact hasSum_fintype _
  have hgroup := hf.hasSum.sigma hfiber
  have hgroup' : HasSum (fun n ↦ j (b (n + 1)) - j (b n)) z := by
    apply hgroup.summable.hasSum_iff_tendsto_nat.mpr
    have htel (n : ℕ) :
        (∑ i ∈ Finset.range n, (j (b (i + 1)) - j (b i))) = j (b n) := by
      rw [Finset.sum_range_sub (fun i ↦ j (b i)), show j (b 0) = 0 from map_zero j, sub_zero]
    simpa only [htel] using hb
  have htotal := hgroup'.sigma_of_hasSum hfiber hf
  -- Embed the countable union of finite blocks into ℕ, padding unused indices with zeros.
  let encode : ι → ℕ := Encodable.encode
  have he : Function.Injective encode := Encodable.encode_injective
  let cn := Function.extend encode coeff 0
  let xy := Function.extend encode (fun i ↦ (left i, right i)) 0
  have hcn : Summable (fun n ↦ ‖cn n‖) := by
    refine (he.summable_iff (fun n hn ↦ ?_)).mp ?_
    · simp [cn, Function.extend_apply' _ _ _ hn]
    · simpa only [Function.comp_def, cn, he.extend_apply] using hc
  have hxyn : Tendsto xy atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    refine tendsto_def.mpr fun S hS ↦ eventually_cofinite.mpr ?_
    refine ((eventually_cofinite.mp (hxy.eventually_mem hS)).image encode).subset ?_
    intro n hn
    by_cases hn' : n ∈ range encode
    · obtain ⟨i, rfl⟩ := hn'
      change xy (encode i) ∉ S at hn
      simp only [xy, he.extend_apply] at hn
      exact ⟨i, hn, rfl⟩
    · change xy n ∉ S at hn
      simp only [xy, Function.extend_apply' _ _ _ hn', Pi.zero_apply] at hn
      exact (hn (mem_of_mem_nhds hS)).elim
  have hxyn' : Tendsto xy atTop (𝓝 (0 : E) ×ˢ 𝓝 (0 : F)) := by
    rw [← nhds_prod_eq]
    exact hxyn
  refine ⟨cn, fun n ↦ (xy n).1, fun n ↦ (xy n).2, hcn, hxyn'.fst, hxyn'.snd, ?_⟩
  refine (he.hasSum_iff (fun n hn ↦ ?_)).mp ?_
  · change j (cn n • ((xy n).1 ⊗ₜ[ℂ] (xy n).2)) = 0
    simp only [cn, Function.extend_apply' _ _ _ hn, Pi.zero_apply, zero_smul]
    exact map_zero j
  · simp only [Function.comp_def, cn, xy, he.extend_apply]
    exact htotal

-- Fréchet completeness of the factors is not used: the completion is already complete.
set_option linter.unusedVariables false in
/-- Paper: (C.2.3.16), p. 679. Conversely, every series of the displayed form converges.
Deviation: The sequences are reindexed from zero. -/
theorem completedProjectiveTensor_summable_series (hE : IsFrechetTVS E) (hF : IsFrechetTVS F)
    (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F) (hc : Summable (fun n ↦ ‖c n‖))
    (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 0)) :
    Summable (fun n ↦ (Completion.coe' (α := ProjectiveTensor E F) (c n • (x n ⊗ₜ[ℂ] y n)))) := by
  let P := ProjectiveTensor E F
  have : UniformContinuousConstSMul ℂ P :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ P
  have : PolynormableSpace ℂ (Completion P) := polynormableSpace_completion
  let tmul : E × F → P := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
  let z (n : ℕ) : Completion P := Completion.coe' (c n • tmul (x n, y n))
  change Summable z
  -- Joint continuity of pure tensors at zero makes `xₙ ⊗ yₙ` a null sequence.
  have htmul : Tendsto (fun n ↦ tmul (x n, y n)) atTop (𝓝 (0 : P)) := by
    have h :=
      ((continuousAt_projectiveTensor_tmul_zero E F).tendsto.comp (hx.prodMk_nhds hy))
    have h0 : ((0 : E × F).1 ⊗ₜ[ℂ] (0 : E × F).2 : P) = 0 := by
      simp [Prod.fst_zero, Prod.snd_zero, TensorProduct.zero_tmul]
    rw [h0] at h
    exact h.congr fun _ ↦ rfl
  rw [summable_iff_vanishing]
  intro U hU
  obtain ⟨q, hq, hqU⟩ :=
    (PolynormableSpace.hasBasis_zero_ball ℂ (Completion P)).mem_iff.mp hU
  have hcoe : Tendsto (fun n ↦ (tmul (x n, y n) : Completion P)) atTop (𝓝 0) := by
    have h := ((Completion.continuous_coe (α := P)).tendsto (0 : P)).comp htmul
    simp only [Completion.coe_zero] at h
    exact h.congr fun _ ↦ rfl
  have hb : Tendsto (fun n ↦ q (tmul (x n, y n) : Completion P)) atTop (𝓝 0) := by
    have h := (hq.tendsto (0 : Completion P)).comp hcoe
    simp only [map_zero q] at h
    exact h.congr fun _ ↦ rfl
  obtain ⟨M, hMpos, hM⟩ := (Metric.isBounded_range_of_tendsto _ hb).exists_pos_norm_le
  have hbound (n : ℕ) : q (tmul (x n, y n) : Completion P) ≤ M := by
    have hle := hM _ (mem_range_self n)
    rwa [Real.norm_of_nonneg (apply_nonneg q _)] at hle
  have hqz (n : ℕ) : q (z n) ≤ M * ‖c n‖ := by
    have hsmul : (z n) = c n • (tmul (x n, y n) : Completion P) := by
      simp [z]
    rw [hsmul, map_smul_eq_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg (c n))
  have htri (t : Finset ℕ) : q (∑ n ∈ t, z n) ≤ ∑ n ∈ t, q (z n) := by
    induction t using Finset.cons_induction with
    | empty => simp [map_zero]
    | cons a s ha ih =>
      rw [Finset.sum_cons ha, Finset.sum_cons ha]
      exact (map_add_le_add q _ _).trans (add_le_add le_rfl ih)
  obtain ⟨s, hs⟩ := summable_iff_vanishing.mp hc (Metric.ball (0 : ℝ) (1 / M))
    (Metric.ball_mem_nhds 0 (one_div_pos.mpr hMpos))
  refine ⟨s, fun t ht ↦ ?_⟩
  have htail : ∑ n ∈ t, ‖c n‖ < 1 / M := by
    have hmem := hs t ht
    rw [Metric.mem_ball, dist_zero_right,
      Real.norm_of_nonneg (Finset.sum_nonneg fun n _ ↦ norm_nonneg _)] at hmem
    exact hmem
  have hlt : q (∑ n ∈ t, z n) < 1 :=
    calc
      q (∑ n ∈ t, z n) ≤ ∑ n ∈ t, q (z n) := htri t
      _ ≤ ∑ n ∈ t, M * ‖c n‖ := Finset.sum_le_sum fun n _ ↦ hqz n
      _ = M * ∑ n ∈ t, ‖c n‖ := by rw [← Finset.mul_sum]
      _ < M * (1 / M) := mul_lt_mul_of_pos_left htail hMpos
      _ = 1 := mul_one_div_cancel hMpos.ne'
  exact hqU (q.mem_ball_zero.mpr hlt)

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

omit [T2Space E] [T2Space F] in
/-- The canonical bilinear map to the completed projective tensor product extends
jointly continuously to both completed factors. -/
private theorem exists_completedProjectiveTensor_bilinear :
    ∃ B : Completion E →ₗ[ℂ] Completion F →ₗ[ℂ] Completion (ProjectiveTensor E F),
      Continuous (fun v : Completion E × Completion F ↦ B v.1 v.2) ∧
      ∀ (x : E) (y : F), B x y =
        Completion.coe' (α := ProjectiveTensor E F) (x ⊗ₜ[ℂ] y) := by
  let G := Completion (ProjectiveTensor E F)
  let L : E →ₗ[ℂ] F →ₗ[ℂ] G :=
    (TensorProduct.mk ℂ E F).compr₂
      (Completion.toComplL : ProjectiveTensor E F →L[ℂ] G).toLinearMap
  let A : E →+ F →+ G := LinearMap.toAddMonoidHom'.comp L.toAddMonoidHom
  have hA : Continuous (fun v : E × F ↦ A v.1 v.2) :=
    (Completion.continuous_coe (ProjectiveTensor E F)).comp continuous_projectiveTensor_tmul
  let de : IsDenseInducing ((↑) : E → Completion E) := Completion.isDenseInducing_coe
  let df : IsDenseInducing ((↑) : F → Completion F) := Completion.isDenseInducing_coe
  let b := (de.prodMap df).extend (fun v : E × F ↦ A v.1 v.2)
  have hb : Continuous b :=
    IsDenseInducing.extend_Z_bilin (e := Completion.toCompl) (f := Completion.toCompl) de df hA
  have hcoe (x : E) (y : F) : b (x, y) = L x y :=
    (de.prodMap df).extend_eq hA (x, y)
  -- Each bilinearity identity extends from the dense image by continuity.
  refine ⟨LinearMap.mk₂ ℂ (fun x y ↦ b (x, y)) ?_ ?_ ?_ ?_, hb, hcoe⟩
  · intro x x' y
    refine Completion.induction_on₃ x x' y (isClosed_eq ?_ ?_) fun a a' c ↦ ?_
    · exact hb.comp ((continuous_fst.add continuous_snd.fst).prodMk continuous_snd.snd)
    · exact (hb.comp (continuous_fst.prodMk continuous_snd.snd)).add
        (hb.comp (continuous_snd.fst.prodMk continuous_snd.snd))
    · rw [← Completion.coe_add a a']
      simp only [hcoe, map_add, LinearMap.add_apply]
  · intro c x y
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a d ↦ ?_
    · exact hb.comp ((continuous_fst.const_smul c).prodMk continuous_snd)
    · exact hb.fun_const_smul c
    · rw [← Completion.coe_smul c a]
      simp only [hcoe, map_smul, LinearMap.smul_apply]
  · intro x y y'
    refine Completion.induction_on₃ x y y' (isClosed_eq ?_ ?_) fun a d d' ↦ ?_
    · exact hb.comp (continuous_fst.prodMk (continuous_snd.fst.add continuous_snd.snd))
    · exact (hb.comp (continuous_fst.prodMk continuous_snd.fst)).add
        (hb.comp (continuous_fst.prodMk continuous_snd.snd))
    · rw [← Completion.coe_add d d']
      simp only [hcoe, map_add]
  · intro c x y
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a d ↦ ?_
    · exact hb.comp (continuous_fst.prodMk (continuous_snd.const_smul c))
    · exact hb.fun_const_smul c
    · rw [← Completion.coe_smul c d]
      simp only [hcoe, map_smul]

/-- Paper: §C.2.3.2, p. 679. Completing the two factors induces an isomorphism on
completed projective tensors. -/
theorem completedProjectiveTensor_completionFactors :
    IsHomeomorph (Completion.map (projectiveTensorMap
      (Completion.toComplL : E →L[ℂ] Completion E).toLinearMap
      (Completion.toComplL : F →L[ℂ] Completion F).toLinearMap)) := by
  let X := ProjectiveTensor E F
  let Y := ProjectiveTensor (Completion E) (Completion F)
  let : PolynormableSpace ℂ (Completion E) := polynormableSpace_completion
  let : PolynormableSpace ℂ (Completion F) := polynormableSpace_completion
  let : PolynormableSpace ℂ (Completion X) := polynormableSpace_completion
  let T : X →ₗ[ℂ] Y := projectiveTensorMap
    (Completion.toComplL : E →L[ℂ] Completion E).toLinearMap
    (Completion.toComplL : F →L[ℂ] Completion F).toLinearMap
  have ht (x : E) (y : F) : T (x ⊗ₜ[ℂ] y) = (x : Completion E) ⊗ₜ[ℂ] (y : Completion F) :=
    TensorProduct.map_tmul _ _ _ _
  let forward : X →L[ℂ] Y := ⟨T, (continuous_projectiveTensor_iff T).2 (by
    simp only [ht]
    exact continuous_projectiveTensor_tmul.comp
      ((Completion.continuous_coe E).prodMap (Completion.continuous_coe F)))⟩
  obtain ⟨B, hB, hcoe⟩ := exists_completedProjectiveTensor_bilinear E F
  let backward : Y →L[ℂ] Completion X :=
    ⟨TensorProduct.lift B,
      (continuous_projectiveTensor_iff (TensorProduct.lift B : Y →ₗ[ℂ] Completion X)).2 hB⟩
  have hb (x : Completion E) (y : Completion F) : backward (x ⊗ₜ[ℂ] y) = B x y :=
    TensorProduct.lift.tmul (f' := B) x y
  change IsHomeomorph forward.completion
  refine isHomeomorph_iff_exists_inverse.mpr
    ⟨forward.completion.continuous, backward.fromCompletion, ?_, ?_,
      backward.fromCompletion.continuous⟩
  · have hleft : backward.toLinearMap.comp T =
        (Completion.toComplL : X →L[ℂ] Completion X).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      change backward (T (x ⊗ₜ[ℂ] y)) = _
      rw [ht, hb]
      exact hcoe x y
    refine Completion.ext' (backward.fromCompletion.continuous.comp forward.completion.continuous)
      continuous_id fun z : X ↦ ?_
    simp only [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.fromCompletion_apply_coe]
    exact DFunLike.congr_fun hleft z
  · have hright : forward.completion.toLinearMap.comp backward.toLinearMap =
        (Completion.toComplL : Y →L[ℂ] Completion Y).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      change forward.completion (backward (x ⊗ₜ[ℂ] y)) = Completion.coe' (α := Y) (x ⊗ₜ[ℂ] y)
      rw [hb]
      refine Completion.induction_on₂ x y
        (isClosed_eq (forward.completion.continuous.comp hB)
          ((Completion.continuous_coe Y).comp continuous_projectiveTensor_tmul)) fun a b ↦ ?_
      rw [hcoe]
      exact (forward.completion_apply_coe (a ⊗ₜ[ℂ] b)).trans
        (congrArg (Completion.coe' (α := Y)) (ht a b))
    refine Completion.ext' (forward.completion.continuous.comp backward.fromCompletion.continuous)
      continuous_id fun z : Y ↦ ?_
    simp only [ContinuousLinearMap.fromCompletion_apply_coe]
    exact DFunLike.congr_fun hright z

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
    projectiveTensorMap f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] g y :=
  TensorProduct.map_tmul _ _ x y

omit [PolynormableSpace ℂ E] [T2Space E] [PolynormableSpace ℂ F] [T2Space F]
  [PolynormableSpace ℂ G] [T2Space G] [PolynormableSpace ℂ H] [T2Space H] in
/-- A linear map between two spaces with generating seminorms is continuous when each
generating seminorm of the target pulls back to a generating seminorm of the source. -/
private theorem continuous_withGeneratingSeminorms_of_comp {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ι ι' : Type*} {p : SeminormFamily ℂ X ι}
    {q : SeminormFamily ℂ Y ι'} (T : X →ₗ[ℂ] Y) (h : ∀ j, ∃ i, (q j).comp T = p i) :
    @Continuous (WithGeneratingSeminorms X p) (WithGeneratingSeminorms Y q) _ _ T := by
  let T' : WithGeneratingSeminorms X p →ₗ[ℂ] WithGeneratingSeminorms Y q := T
  refine (withGeneratingSeminorms_spec Y q).continuous_of_continuous_comp T' fun j ↦ ?_
  obtain ⟨i, hi⟩ := h j
  refine (continuous_congr fun x ↦ ?_).mp ((withGeneratingSeminorms_spec X p).continuous_seminorm i)
  show p i x = q j (T x)
  rw [← hi]
  rfl

/-- Paper: §C.2.3.2, p. 679. Tensoring continuous linear maps gives a continuous
projective tensor map, hence a map of additive completions. -/
theorem projectiveTensorMap_continuous :
    Continuous (projectiveTensorMap f.toLinearMap g.toLinearMap) := by
  refine continuous_withGeneratingSeminorms_of_comp (TensorProduct.map f.toLinearMap g.toLinearMap)
    fun q ↦ ⟨⟨q.val.comp (TensorProduct.map f.toLinearMap g.toLinearMap), ?_⟩, rfl⟩
  have hfg : Continuous (fun v : E × F ↦ (f v.1, g v.2)) := by fun_prop
  change ContinuousAt ((fun w : G × H ↦ q.val (w.1 ⊗ₜ[ℂ] w.2)) ∘ fun v : E × F ↦ (f v.1, g v.2)) 0
  exact ContinuousAt.comp_of_eq q.property hfg.continuousAt (by simp)

/-- A linear image of an absolutely convex set is absolutely convex. -/
private theorem absConvex_linear_image {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {S : Set X} (hS : AbsConvex ℂ S) (L : X →ₗ[ℂ] Y) : AbsConvex ℂ (L '' S) :=
  ⟨hS.1.image L, hS.2.linear_image L⟩

/-- The absolutely convex hull of a linear image sits inside the image of the hull. -/
private theorem absConvexHull_subset_linear_image {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (L : X →ₗ[ℂ] Y) (S : Set X) :
    absConvexHull ℂ (L '' S) ⊆ L '' absConvexHull ℂ S :=
  absConvexHull_min (image_mono subset_absConvexHull)
    (absConvex_linear_image absConvex_absConvexHull L)

include hf hg

/-- Paper: §C.2.3.2, p. 679. Tensoring quotient maps gives a projective quotient map. -/
theorem projectiveTensorMap_isQuotientMap :
    IsQuotientMap (projectiveTensorMap f.toLinearMap g.toLinearMap) := by
  let T := projectiveTensorMap f.toLinearMap g.toLinearMap
  have hsurj : Function.Surjective T := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨a, ha⟩ := hf.surjective x
      obtain ⟨b, hb⟩ := hg.surjective y
      exact ⟨a ⊗ₜ[ℂ] b, by rw [projectiveTensorMap_tmul, ha, hb]⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add T x y⟩
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : IsTopologicalAddGroup F := PolynormableSpace.isTopologicalAddGroup ℂ F
  have hfOpen : IsOpenMap f :=
    (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hf).isOpenMap
  have hgOpen : IsOpenMap g :=
    (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hg).isOpenMap
  -- (C.2.3.15): a basic projective neighborhood is the absolutely convex hull of a product of
  -- factor neighborhoods, and a quotient map sends those to neighborhoods.
  have hopen : IsOpenMap T := by
    rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero, le_map_iff]
    intro W hW
    obtain ⟨U, V, hU, hV, hUV⟩ := projectiveTensor_nhds_superset_absConvexHull hW
    have hFU : f '' U ∈ 𝓝 (0 : G) := by
      simpa [map_zero f] using hfOpen.image_mem_nhds hU
    have hGV : g '' V ∈ 𝓝 (0 : H) := by
      simpa [map_zero g] using hgOpen.image_mem_nhds hV
    have heq : T '' image2 (TensorProduct.tmul ℂ) U V =
        image2 (TensorProduct.tmul ℂ) (f '' U) (g '' V) :=
      image_image2_distrib fun x y => projectiveTensorMap_tmul f g x y
    refine mem_of_superset (projectiveTensor_absConvexHull_mem_nhds hFU hGV) ?_
    rw [← heq]
    exact (absConvexHull_subset_linear_image T _).trans (image_mono hUV)
  exact IsOpenMap.isQuotientMap hopen (projectiveTensorMap_continuous f g) hsurj

/-- Paper: Proposition C.2.3.7, p. 679. The extension to completions is a quotient map
onto its range with the subspace topology. -/
theorem completedProjectiveTensorMap_isQuotientMap_range :
    IsQuotientMap (rangeFactorization (Completion.map
      (projectiveTensorMap f.toLinearMap g.toLinearMap))) := by
  exact isQuotientMap_rangeFactorization_completion_map
    (projectiveTensorMap f.toLinearMap g.toLinearMap).toAddMonoidHom
    (projectiveTensorMap_isQuotientMap f g hf hg)

/-- Paper: Proposition C.2.3.7, p. 679. If both domains are metrizable, the
completed projective tensor map is surjective. -/
theorem completedProjectiveTensorMap_surjective [MetrizableSpace E] [MetrizableSpace F] :
    Function.Surjective (Completion.map (projectiveTensorMap f.toLinearMap g.toLinearMap)) := by
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 (0 : F)).exists_antitone_basis
  let X := ProjectiveTensor E F
  have : (𝓝 (0 : X)).IsCountablyGenerated :=
    (projectiveTensor_zero_basis hU.toHasBasis hV.toHasBasis).isCountablyGenerated
  let : FirstCountableTopology X := ⟨fun x ↦ by
    rw [← map_add_left_nhds_zero x]
    infer_instance⟩
  let T : X →+ ProjectiveTensor G H := (projectiveTensorMap f.toLinearMap g.toLinearMap).toAddMonoidHom
  have hT : IsOpenQuotientMap T :=
    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap (projectiveTensorMap_isQuotientMap f g hf hg)
  exact completion_map_surjective_of_isOpenQuotientMap T hT

end ProjectiveQuotients

section Comparison

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ E] [T2Space E]
  [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: §C.2.3.2, p. 679. The identity from the projective to the injective
tensor product is continuous. -/
theorem continuous_projectiveTensor_to_injectiveTensor :
    @Continuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  have hinj := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  have hproj := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  refine hinj.continuous_of_continuous_comp
    (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F) fun UV ↦ ?_
  have key : ContinuousAt (fun v : E × F ↦ injectiveTensorSeminorm UV.1 UV.2 (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
    have h0 : injectiveTensorSeminorm UV.1 UV.2 ((0 : E × F).1 ⊗ₜ[ℂ] (0 : E × F).2) = 0 := by
      simp
    rw [ContinuousAt, h0]
    refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun v ↦ ha.trans_le (apply_nonneg _ _), fun a ha ↦ ?_⟩
    let c : ℂ := ((2 / a : ℝ) : ℂ)
    have hA : {x : E | c • x ∈ UV.1.val} ∈ 𝓝 (0 : E) :=
      (continuous_const_smul c).continuousAt.preimage_mem_nhds (by simpa using UV.1.property)
    rw [nhds_prod_eq]
    refine Filter.mem_of_superset (Filter.prod_mem_prod hA UV.2.property) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    show injectiveTensorSeminorm UV.1 UV.2 (x ⊗ₜ[ℂ] y) < a
    have hle : injectiveTensorSeminorm UV.1 UV.2 (x ⊗ₜ[ℂ] y) ≤ a / 2 := by
      refine (injectiveTensorSeminorm_le_iff UV.1 UV.2 _ _).2 fun φ hφ ψ hψ ↦ ?_
      have h1 : ‖φ (c • x)‖ ≤ 1 := (StrongDual.mem_polar_iff ℂ _).1 hφ _ hx
      have h2 : ‖ψ y‖ ≤ 1 := (StrongDual.mem_polar_iff ℂ _).1 hψ _ hy
      have hc : ‖c‖ = 2 / a := by simp [c, abs_of_pos ha]
      rw [tensorDualForm_tmul, norm_mul]
      rw [map_smul, smul_eq_mul, norm_mul, hc] at h1
      have : ‖φ x‖ ≤ a / 2 := by
        have : 2 / a * ‖φ x‖ ≤ 1 := h1
        rw [div_mul_eq_mul_div, div_le_iff₀ ha] at this
        linarith
      calc ‖φ x‖ * ‖ψ y‖ ≤ a / 2 * 1 := mul_le_mul this h2 (norm_nonneg _) (by positivity)
        _ = a / 2 := mul_one _
    linarith
  exact hproj.continuous_seminorm ⟨injectiveTensorSeminorm UV.1 UV.2, key⟩


-- TODO(later): needs §C.2.4 for equality when either factor is nuclear.

/-- Paper: Remark C.2.3.8, p. 679. The absolute polars of products of equicontinuous
sets of functionals form a basis of zero-neighborhoods, as specified on p. 680. -/
theorem injectiveTensor_zero_basis :
    (𝓝 (0 : InjectiveTensor E F)).HasBasis
      (fun AB : Set (StrongDual ℂ E) × Set (StrongDual ℂ F) ↦
        EquicontinuousAt (fun φ : AB.1 ↦ (φ.val : E → ℂ)) 0 ∧
        EquicontinuousAt (fun ψ : AB.2 ↦ (ψ.val : F → ℂ)) 0)
      (fun AB ↦ {z | ∀ φ ∈ AB.1, ∀ ψ ∈ AB.2, ‖tensorDualForm φ ψ z‖ ≤ 1}) := by
  let p (UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0}) :
      Seminorm ℂ (InjectiveTensor E F) :=
    injectiveTensorSeminorm UV.1 UV.2
  have hp : WithSeminorms p := withGeneratingSeminorms_spec (E ⊗[ℂ] F) p
  refine hp.hasBasis_zero_ball.to_hasBasis' ?_ ?_
  · rintro ⟨s, r⟩ hr
    change 0 < r at hr
    obtain ⟨a, ha, har⟩ := NormedField.exists_norm_lt ℂ hr
    have ha₀ := norm_pos_iff.mp ha
    let U : Set E := ⋂ UV ∈ s, UV.1.val
    have hU : U ∈ 𝓝 (0 : E) := s.iInter_mem_sets.mpr fun UV _ ↦ UV.1.property
    let W : Set E := (fun x : E ↦ a⁻¹ • x) ⁻¹' U
    have hW : W ∈ 𝓝 (0 : E) :=
      (continuous_const_smul a⁻¹).continuousAt.preimage_mem_nhds (by simpa only [smul_zero] using hU)
    let V : Set F := ⋂ UV ∈ s, UV.2.val
    have hV : V ∈ 𝓝 (0 : F) := s.iInter_mem_sets.mpr fun UV _ ↦ UV.2.property
    refine ⟨(StrongDual.polar ℂ W, StrongDual.polar ℂ V),
      ⟨(weakDual_polar_mem_compactology hW).1, (weakDual_polar_mem_compactology hV).1⟩, ?_⟩
    intro z hz
    change z ∈ (s.sup p).ball 0 r
    refine (Seminorm.mem_ball_zero _).mpr
      ((Seminorm.finset_sup_apply_le ha.le fun UV hUV ↦ ?_).trans_lt har)
    refine (injectiveTensorSeminorm_le_iff UV.1 UV.2 z ‖a‖).mpr fun φ hφ ψ hψ ↦ ?_
    have hφ' : a⁻¹ • φ ∈ StrongDual.polar ℂ W :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦ by
        have hx' : a⁻¹ • x ∈ U := hx
        simpa only [smul_apply, map_smul] using
          (StrongDual.mem_polar_iff ℂ _).mp hφ _ (mem_iInter₂.mp hx' UV hUV)
    have hψ' : ψ ∈ StrongDual.polar ℂ V :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
        (StrongDual.mem_polar_iff ℂ _).mp hψ _ (mem_iInter₂.mp hy UV hUV)
    have hform : tensorDualForm φ ψ = a • tensorDualForm (a⁻¹ • φ) ψ := by
      apply TensorProduct.ext'
      intro x y
      simp [tensorDualForm_tmul, smul_eq_mul, ← mul_assoc, ha₀]
    change ∀ φ ∈ StrongDual.polar ℂ W, ∀ ψ ∈ StrongDual.polar ℂ V,
      ‖tensorDualForm φ ψ z‖ ≤ 1 at hz
    rw [hform]
    change ‖a • tensorDualForm (a⁻¹ • φ) ψ z‖ ≤ ‖a‖
    rw [norm_smul]
    exact mul_le_of_le_one_right ha.le (hz _ hφ' _ hψ')
  · rintro ⟨A, B⟩ ⟨hA, hB⟩
    let U : {U : Set E // U ∈ 𝓝 0} := ⟨_, Metric.equicontinuousAt_iff_right.mp hA 1 one_pos⟩
    let V : {V : Set F // V ∈ 𝓝 0} := ⟨_, Metric.equicontinuousAt_iff_right.mp hB 1 one_pos⟩
    refine Filter.mem_of_superset
      ((p (U, V)).ball_mem_nhds (hp.continuous_seminorm (U, V)) one_pos) ?_
    intro z hz φ hφ ψ hψ
    refine (injectiveTensorSeminorm_le_iff U V z 1).mp
      ((p (U, V)).mem_ball_zero.mp hz).le φ ?_ ψ ?_
    · refine (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦ ?_
      simpa only [map_zero, dist_zero_left] using (hx (⟨φ, hφ⟩ : A)).le
    · refine (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦ ?_
      simpa only [map_zero, dist_zero_left] using (hy (⟨ψ, hψ⟩ : B)).le

/-- Paper: Remark C.2.3.8, p. 679. An equicontinuous set in the ε-dual is exactly a subset
of the bipolar of the pure functionals from two equicontinuous sets in the factor duals.
Deviation: The bipolar test on p. 680 is written out as two polar inequalities. -/
theorem injectiveTensor_equicontinuous_iff (D : Set (StrongDual ℂ (InjectiveTensor E F))) :
    EquicontinuousAt (fun l : D ↦ (l.val : InjectiveTensor E F → ℂ)) 0 ↔
      ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
        EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 ∧
        EquicontinuousAt (fun ψ : B ↦ (ψ.val : F → ℂ)) 0 ∧
        ∀ l ∈ D, ∀ z : InjectiveTensor E F,
          (∀ φ ∈ A, ∀ ψ ∈ B, ‖tensorDualForm φ ψ z‖ ≤ 1) → ‖l z‖ ≤ 1 := by
  let basis := injectiveTensor_zero_basis E F
  constructor
  · intro hD
    have h := Metric.equicontinuousAt_iff_right.mp hD 1 one_pos
    obtain ⟨⟨A, B⟩, ⟨hA, hB⟩, hsub⟩ := basis.mem_iff.mp h
    exact ⟨A, B, hA, hB, fun l hl z hz ↦ by
      simpa only [map_zero, dist_zero_left] using (hsub hz ⟨l, hl⟩).le⟩
  · rintro ⟨A, B, hA, hB, hD⟩
    let U : Set (InjectiveTensor E F) := {z | ∀ φ ∈ A, ∀ ψ ∈ B, ‖tensorDualForm φ ψ z‖ ≤ 1}
    have hU : U ∈ 𝓝 0 := basis.mem_of_mem (i := (A, B)) ⟨hA, hB⟩
    have heq := (weakDual_polar_mem_compactology hU).1
    exact heq.comp (fun l : D ↦ ⟨StrongDual.toWeakDual l.val, fun z hz ↦ hD l.val l.property z hz⟩)

end Comparison

section DirectSums

/-- A generating projective seminorm, tested on the unit ball in the normed factor, is bounded
by a single continuous seminorm on the other factor. -/
private theorem projectiveTensor_seminorm_unitBall_bound {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℂ Y]
    (p : Seminorm ℂ (X ⊗[ℂ] Y))
    (hp : ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0) :
    ∃ q : Seminorm ℂ X, Continuous q ∧ ∀ x y, ‖y‖ < 1 → p (x ⊗ₜ[ℂ] y) ≤ q x := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ X
  have h : {v : X × Y | p (v.1 ⊗ₜ[ℂ] v.2) < 1} ∈ 𝓝 0 :=
    hp.preimage_mem_nhds (show Iio (1 : ℝ) ∈ 𝓝 (p ((0 : X × Y).1 ⊗ₜ[ℂ]
      (0 : X × Y).2)) by simpa using Iio_mem_nhds (α := ℝ) one_pos)
  rw [show (0 : X × Y) = ((0 : X), (0 : Y)) from rfl, nhds_prod_eq] at h
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨r, hr, hrV⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hV
  obtain ⟨c, hc, hcr⟩ := NormedField.exists_norm_lt ℂ hr
  let B := {y : Y // ‖y‖ < 1}
  let s (y : B) : Seminorm ℂ X := p.comp ((TensorProduct.mk ℂ X Y).flip y.val)
  have hbound (x : X) (hx : x ∈ U) (y : B) : s y x ≤ 1 / ‖c‖ := by
    have hy : c • y.val ∈ V := hrV (by
      change ‖c • y.val‖ < r
      rw [norm_smul]
      exact (mul_lt_of_lt_one_right hc y.property).trans hcr)
    rw [le_div_iff₀' hc]
    change ‖c‖ * p (x ⊗ₜ[ℂ] y.val) ≤ 1
    rw [← map_smul_eq_mul, ← tmul_smul]
    exact (hUV (a := (x, c • y.val)) ⟨hx, hy⟩).le
  have hs : BddAbove (range s) := Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero hU)
    fun x hx ↦ ⟨1 / ‖c‖, forall_mem_range.mpr (hbound x hx)⟩
  let q : Seminorm ℂ X := ⨆ y, s y
  have : Nonempty B := ⟨⟨0, by simp⟩⟩
  refine ⟨q, Seminorm.continuous' (r := 1 / ‖c‖) ?_, fun x y hy ↦ ?_⟩
  · refine mem_of_superset hU fun x hx ↦ ?_
    rw [Seminorm.mem_closedBall_zero, Seminorm.iSup_apply hs]
    exact ciSup_le (hbound x hx)
  · exact (le_ciSup hs ⟨y, hy⟩ : s ⟨y, hy⟩ ≤ q) x

variable {I : Type*} [DecidableEq I] (E : I → Type*) (F : Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, PolynormableSpace ℂ (E i)] [∀ i, T2Space (E i)]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsNormableSpace ℂ F] [T2Space F]

-- Retain the Hausdorff assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Proposition C.2.3.9(1), p. 680. With a normable fixed factor the canonical
distributivity map for an arbitrary locally convex direct sum is a homeomorphism. -/
theorem projectiveTensor_directSum :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I E)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I (fun i ↦ ProjectiveTensor (E i) F))
    @IsHomeomorph (⨁ i, ProjectiveTensor (E i) F) (ProjectiveTensor (⨁ i, E i) F)
      _ _ (TensorProduct.directSumLeft ℂ ℂ E F).symm := by
  classical
  let X := ⨁ i, E i
  let Y (i : I) := ProjectiveTensor (E i) F
  let D := ⨁ i, Y i
  let lofX := DirectSum.lof ℂ I E
  let lofY := DirectSum.lof ℂ I Y
  let : TopologicalSpace X := locallyConvexFinalTopology lofX
  let : TopologicalSpace D := locallyConvexFinalTopology lofY
  let e : ProjectiveTensor X F ≃ₗ[ℂ] D := TensorProduct.directSumLeft ℂ ℂ E F
  have hX : WithSeminorms (E := X)
      (Subtype.val : {p : Seminorm ℂ X // ∀ i, Continuous (p ∘ lofX i)} → Seminorm ℂ X) := ⟨rfl⟩
  have hD : WithSeminorms (E := D)
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ lofY i)} → Seminorm ℂ D) := ⟨rfl⟩
  let : IsTopologicalAddGroup X := hX.isTopologicalAddGroup
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  have hlofX (i : I) : Continuous (lofX i) := by
    have := PolynormableSpace.isTopologicalAddGroup ℂ (E i)
    exact hX.continuous_of_continuous_comp _ fun p ↦ p.property i
  change IsHomeomorph e.symm
  refine e.symm.isHomeomorph_iff.mpr ⟨?_, ?_⟩
  · refine (projectiveTensor_withSeminorms X F).continuous_of_continuous_comp
      e.symm.toLinearMap fun p ↦ ?_
    refine hD.continuous_seminorm ⟨p.val.comp e.symm.toLinearMap, fun i ↦ ?_⟩
    let q : Seminorm ℂ (E i ⊗[ℂ] F) := (p.val.comp e.symm.toLinearMap).comp (lofY i)
    have hq : ContinuousAt (fun v : E i × F ↦ q (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
      have hc : ContinuousAt (fun v : E i × F ↦ (lofX i v.1, v.2)) 0 :=
        ((hlofX i).comp continuous_fst).continuousAt.prodMk continuous_snd.continuousAt
      have hp := p.property.comp_of_eq hc (show (lofX i 0, (0 : F)) = 0 by simp)
      change ContinuousAt (fun v : E i × F ↦ p.val (e.symm (lofY i (v.1 ⊗ₜ[ℂ] v.2)))) 0
      have heq (x : E i) (y : F) : e.symm (lofY i (x ⊗ₜ[ℂ] y)) = lofX i x ⊗ₜ[ℂ] y :=
        TensorProduct.directSumLeft_symm_lof_tmul ℂ ℂ i x y
      simp only [heq]
      exact hp
    exact (projectiveTensor_withSeminorms (E i) F).continuous_seminorm ⟨q, hq⟩
  · refine hD.continuous_of_continuous_comp e.toLinearMap fun p ↦ ?_
    refine (projectiveTensor_withSeminorms X F).continuous_seminorm ⟨p.val.comp e.toLinearMap, ?_⟩
    let : SeminormedAddCommGroup F := IsNormableSpace.toSeminormedAddCommGroup ℂ F
    let : NormedSpace ℂ F := IsNormableSpace.toNormedSpace ℂ F
    let s (i : I) : Seminorm ℂ (E i ⊗[ℂ] F) := p.val.comp (lofY i)
    have hs (i : I) : ContinuousAt (fun v : E i × F ↦ s i (v.1 ⊗ₜ[ℂ] v.2)) 0 :=
      (p.property i).continuousAt.comp (continuousAt_projectiveTensor_tmul_zero (E i) F)
    choose q hq hbound using fun i ↦ projectiveTensor_seminorm_unitBall_bound (s i) (hs i)
    let r := directSumSeminorm q
    have hr : Continuous r := by
      refine hX.continuous_seminorm ⟨r, fun i ↦ ?_⟩
      change Continuous (fun x ↦ directSumSeminorm q (DirectSum.lof ℂ I E i x))
      simpa only [directSumSeminorm_lof] using hq i
    -- All summands are controlled on the same unit ball in the fixed factor.
    have htotal (x : X) (y : F) (hy : ‖y‖ < 1) : p.val (e (x ⊗ₜ[ℂ] y)) ≤ r x := by
      let f : X →ₗ[ℂ] D := e.toLinearMap.comp ((TensorProduct.mk ℂ X F).flip y)
      have hsum : (∑ i ∈ x.support, lofX i (x i)) = x := DirectSum.sum_support_of x
      have hsum' : f x = ∑ i ∈ x.support, f (lofX i (x i)) := by rw [← map_sum, hsum]
      change p.val (f x) ≤ r x
      calc
        p.val (f x) ≤ ∑ i ∈ x.support, p.val (f (lofX i (x i))) := by
          rw [hsum']
          exact Finset.le_sum_of_subadditive p.val (map_zero p.val).le
            (map_add_le_add p.val) x.support (fun i ↦ f (lofX i (x i)))
        _ ≤ r x := by
          rw [show r x = ∑ i ∈ x.support, q i (x i) from directSumSeminorm_apply q x _ Subset.rfl]
          apply Finset.sum_le_sum
          intro i _
          change p.val (e (lofX i (x i) ⊗ₜ[ℂ] y)) ≤ q i (x i)
          rw [show e (lofX i (x i) ⊗ₜ[ℂ] y) = lofY i (x i ⊗ₜ[ℂ] y) from
            TensorProduct.directSumLeft_tmul_lof ℂ ℂ i (x i) y]
          exact hbound i (x i) y hy
    have hball : ∀ᶠ v : X × F in 𝓝 0, ‖v.2‖ < 1 := by
      have h : {y : F | ‖y‖ < 1} ∈ 𝓝 (0 : X × F).2 :=
        NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem one_pos
      exact continuous_snd.continuousAt.preimage_mem_nhds h
    have hr0 : Tendsto (fun v : X × F ↦ r v.1) (𝓝 0) (𝓝 0) := by
      have h : Continuous (fun v : X × F ↦ r v.1) := hr.comp continuous_fst
      have ht := h.continuousAt.tendsto (x := (0 : X × F))
      change Tendsto (fun v : X × F ↦ r v.1) (𝓝 0) (𝓝 (r 0)) at ht
      rwa [map_zero] at ht
    change ContinuousAt (fun v : X × F ↦ p.val (e (v.1 ⊗ₜ[ℂ] v.2))) 0
    have hzero : p.val (e ((0 : X × F).1 ⊗ₜ[ℂ] (0 : X × F).2)) = 0 := by
      rw [Prod.fst_zero, TensorProduct.zero_tmul]
      exact (congrArg p.val e.map_zero).trans (map_zero p.val)
    rw [ContinuousAt, hzero]
    exact squeeze_zero' (Eventually.of_forall fun v ↦ apply_nonneg p.val _)
      (hball.mono fun v hv ↦ htotal v.1 v.2 hv) hr0

/-- The generating seminorms for the final locally convex topology are tested on each stage. -/
private theorem finalTopology_withSeminorms {K Z : Type*} {V : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ k, AddCommGroup (V k)] [∀ k, Module ℂ (V k)]
    [∀ k, TopologicalSpace (V k)] (j : ∀ k, V k →ₗ[ℂ] Z) :
    letI := locallyConvexFinalTopology j
    WithSeminorms (E := Z) (Subtype.val : {p : Seminorm ℂ Z // ∀ k, Continuous (p ∘ j k)} → _) := by
  let := locallyConvexFinalTopology j
  exact ⟨rfl⟩

/-- Each stage map into the final locally convex topology is continuous. -/
private theorem continuous_finalTopology_stage {K Z : Type*} {V : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ k, AddCommGroup (V k)] [∀ k, Module ℂ (V k)]
    [∀ k, TopologicalSpace (V k)] [∀ k, IsTopologicalAddGroup (V k)]
    (j : ∀ k, V k →ₗ[ℂ] Z) (k : K) :
    letI := locallyConvexFinalTopology j
    Continuous (j k) := by
  let := locallyConvexFinalTopology j
  exact (finalTopology_withSeminorms j).continuous_of_continuous_comp _ fun p ↦ p.property k

/-- A linear map on a space with the final locally convex topology is continuous if all
its restrictions to the defining stages are continuous. -/
private theorem continuous_finalTopology_lift {K Z W : Type*} {V : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, TopologicalSpace (V i)] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [PolynormableSpace ℂ W] (u : ∀ i, V i →ₗ[ℂ] Z) (T : Z →ₗ[ℂ] W)
    (h : ∀ i, Continuous (T ∘ u i)) :
    letI := locallyConvexFinalTopology u
    Continuous T := by
  let := locallyConvexFinalTopology u
  have hs := finalTopology_withSeminorms u
  have := hs.isTopologicalAddGroup
  exact (PolynormableSpace.withSeminorms ℂ W).continuous_of_continuous_comp T fun p ↦
    hs.continuous_seminorm ⟨p.val.comp T, fun i ↦ p.property.comp (h i)⟩

/-- Coordinate projections are continuous on the locally convex direct sum. -/
private theorem continuous_lcDirectSum_component {K : Type*} [DecidableEq K] (V : K → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, TopologicalSpace (V i)]
    [∀ i, PolynormableSpace ℂ (V i)] (i : K) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ K V)
    Continuous (DirectSum.component ℂ K V i) := by
  let lof := DirectSum.lof ℂ K V
  let := locallyConvexFinalTopology lof
  apply continuous_finalTopology_lift lof
  intro k
  change Continuous ((DirectSum.component ℂ K V i).comp (DirectSum.lof ℂ K V k))
  by_cases h : k = i
  · subst k
    simp only [DirectSum.component_comp_lof_same, LinearMap.id_coe, continuous_id]
  · rw [DirectSum.component_comp_lof, dite_eq_right h]
    exact continuous_const

/-- A Cauchy filter in a locally convex direct sum of complete spaces converges.
Its coordinate limits have finite support, as seen by testing a seminorm that takes
value one on each nonzero limit coordinate. -/
private theorem completeSpace_lcDirectSum {K : Type*} [DecidableEq K] (V : K → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, UniformSpace (V i)]
    [∀ i, IsUniformAddGroup (V i)] [∀ i, PolynormableSpace ℂ (V i)]
    [∀ i, T2Space (V i)] [∀ i, CompleteSpace (V i)] :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ K V)
    letI := (finalTopology_withSeminorms (DirectSum.lof ℂ K V)).isTopologicalAddGroup
    @CompleteSpace (⨁ i, V i) (IsTopologicalAddGroup.rightUniformSpace _) := by
  classical
  let D := ⨁ i, V i
  let lof := DirectSum.lof ℂ K V
  let := locallyConvexFinalTopology lof
  have hD := finalTopology_withSeminorms lof
  have : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let := IsTopologicalAddGroup.rightUniformSpace D
  have : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
  have : PolynormableSpace ℂ D := hD.toPolynormableSpace
  let pr := DirectSum.component ℂ K V
  have hpr := continuous_lcDirectSum_component V
  constructor
  intro l hl
  have : l.NeBot := hl.1
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, V i, ∀ i, Tendsto (pr i) l (𝓝 (v i)) := by
    choose v hv using fun i ↦ CompleteSpace.complete (hl.map
      ((pr i).toAddMonoidHom.uniformContinuous_of_continuousAt_zero (hpr i).continuousAt))
    exact ⟨v, hv⟩
  -- Finite sums of coordinate seminorms stay close to the coordinatewise limit.
  have approx (q : ∀ i, Seminorm ℂ (V i)) (hq : ∀ i, Continuous (q i)) :
      ∀ᶠ x : D in l, ∀ s : Finset K, (∑ i ∈ s, q i (x i - v i)) ≤ 1/2 := by
    let p := directSumSeminorm q
    have hp : Continuous p := hD.continuous_seminorm ⟨p, fun i ↦ by
      change Continuous (fun a ↦ directSumSeminorm q (DirectSum.lof ℂ K V i a))
      simpa only [directSumSeminorm_lof] using hq i⟩
    have ht := (IsUniformAddGroup.cauchy_iff_tendsto l).mp hl
    obtain ⟨S, hS, hSS⟩ := l.basis_sets.prod_self.mem_iff.mp
      (ht.2 (p.ball_mem_nhds hp (show (0 : ℝ) < 1/2 by norm_num)))
    filter_upwards [hS] with x hx
    intro s
    have htend : Tendsto (fun y : D ↦ ∑ i ∈ s, q i (x i - y i)) l
        (𝓝 (∑ i ∈ s, q i (x i - v i))) :=
      tendsto_finsetSum _ fun i _ ↦ (hq i).continuousAt.tendsto.comp ((hv i).const_sub (x i))
    apply le_of_tendsto htend
    filter_upwards [hS] with y hy
    exact (sum_le_directSumSeminorm q (x-y) s).trans (p.mem_ball_zero.mp (hSS (a := (x,y)) ⟨hx,hy⟩)).le
  have hsep (i : K) : ∃ q : Seminorm ℂ (V i), Continuous q ∧ (v i ≠ 0 → q (v i) = 1) := by
    by_cases h : v i = 0
    · exact ⟨0, continuous_zero, fun hn ↦ (hn h).elim⟩
    have := polynormableSpace_separatingDual ℂ (V i)
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_eq_one (R := ℂ) h
    exact ⟨(normSeminorm ℂ ℂ).comp φ.toLinearMap, φ.continuous.norm, fun _ ↦ by
      change ‖φ (v i)‖ = 1
      simp [hφ]⟩
  choose q hq hsep using hsep
  obtain ⟨a, ha⟩ := (approx q hq).exists
  let z : D := DFinsupp.mk a.support fun i ↦ v i
  have hz (i : K) : z i = v i := by
    rw [show z i = _ from DFinsupp.mk_apply]
    split_ifs with hi
    · rfl
    · by_contra h
      have := ha {i}
      have hai : a i = 0 := DFinsupp.notMem_support_iff.mp hi
      simp [hai, hsep i (Ne.symm h)] at this
      linarith
  refine ⟨z, (Filter.tendsto_sub_const_iff z).mp ?_⟩
  rw [sub_self]
  apply (PolynormableSpace.hasBasis_zero_ball ℂ D).tendsto_right_iff.mpr
  intro p hp
  let r (i : K) := p.comp (lof i)
  have hr i : Continuous (r i) := hp.comp (continuous_finalTopology_stage lof i)
  filter_upwards [approx r hr] with x hx
  let d := x - z
  have hsum := Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p)
    d.support (fun i ↦ lof i (d i))
  rw [show (∑ i ∈ d.support, lof i (d i)) = d from DirectSum.sum_support_of d] at hsum
  apply p.mem_ball_zero.mpr
  refine hsum.trans_lt ((le_trans ?_ (hx d.support)).trans_lt (by norm_num))
  apply Finset.sum_le_sum
  intro i _
  change p (lof i (x i - z i)) ≤ p (lof i (x i - v i))
  rw [hz]

/-- Completing a locally convex direct sum completes its summands. The equivalence
is specified on every completed summand, for any given realization of the original sum. -/
private theorem lcDirectSum_completion_equiv {K B : Type*} [DecidableEq K] (V : K → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, UniformSpace (V i)]
    [∀ i, IsUniformAddGroup (V i)] [∀ i, PolynormableSpace ℂ (V i)]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B] [PolynormableSpace ℂ B]
    (e : (⨁ i, V i) ≃ₗ[ℂ] B)
    (he : letI := locallyConvexFinalTopology (DirectSum.lof ℂ K V); IsHomeomorph e) :
    let Z := fun i ↦ Completion (V i)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ K Z)
    ∃ h : (⨁ i, Z i) ≃L[ℂ] Completion B, ∀ i (z : Z i),
      h (DirectSum.lof ℂ K Z i z) = Completion.map (e.toLinearMap.comp (DirectSum.lof ℂ K V i)) z := by
  let Z (i : K) := Completion (V i)
  let D := ⨁ i, Z i
  let u := DirectSum.lof ℂ K V
  let v := DirectSum.lof ℂ K Z
  let := locallyConvexFinalTopology u
  let := locallyConvexFinalTopology v
  have hD := finalTopology_withSeminorms v
  have : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let := IsTopologicalAddGroup.rightUniformSpace D
  have : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
  have : ∀ i, PolynormableSpace ℂ (Z i) := fun i ↦ polynormableSpace_completion
  have : PolynormableSpace ℂ D := hD.toPolynormableSpace
  have : PolynormableSpace ℂ (Completion B) := polynormableSpace_completion
  have : CompleteSpace D := completeSpace_lcDirectSum Z
  have : T2Space D := T2Space.of_injective_continuous (f := fun x : D ↦ (fun i ↦ x i))
    (fun _ _ h ↦ DFinsupp.ext (congrFun h)) (continuous_pi (continuous_lcDirectSum_component Z))
  let stage (i : K) : V i →L[ℂ] B := ⟨e.toLinearMap.comp (u i),
    he.continuous.comp (continuous_finalTopology_stage u i)⟩
  let H := DirectSum.toModule ℂ K (Completion B) fun i ↦ (stage i).completion.toLinearMap
  have hH (i : K) (z : Z i) : H (v i z) = (stage i).completion z := DirectSum.toModule_lof ℂ i z
  let forward : D →L[ℂ] Completion B := ⟨H, continuous_finalTopology_lift v H fun i ↦ by
    simpa only [Function.comp_def, hH] using (stage i).completion.continuous⟩
  let k := DirectSum.lmap (fun i ↦ (Completion.toComplL : V i →L[ℂ] Z i).toLinearMap)
  have hk (i : K) (x : V i) : k (u i x) = v i (x : Z i) := DirectSum.lmap_lof _ i x
  have hkc : Continuous k := continuous_finalTopology_lift u k fun i ↦ by
    simpa only [Function.comp_def, hk] using
      (continuous_finalTopology_stage v i).comp (Completion.continuous_coe (V i))
  let back : B →L[ℂ] D := ⟨k.comp e.symm.toLinearMap, hkc.comp (e.isHomeomorph_iff.mp he).2⟩
  have hback (i : K) (x : V i) : back (stage i x) = v i (x : Z i) := by
    change k (e.symm (e (u i x))) = _
    rw [e.symm_apply_apply, hk]
  have hleft : back.fromCompletion.toLinearMap.comp H = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro z
    change back.fromCompletion (H (v i z)) = v i z
    rw [hH]
    refine Completion.induction_on z (isClosed_eq (back.fromCompletion.continuous.comp
      (stage i).completion.continuous) (continuous_finalTopology_stage v i)) fun x ↦ ?_
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.fromCompletion_apply_coe, hback]
  have hright : H.comp k = (Completion.toComplL : B →L[ℂ] Completion B).toLinearMap.comp e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change H (k (u i x)) = _
    rw [hk, hH, ContinuousLinearMap.completion_apply_coe]
    rfl
  refine ⟨ContinuousLinearEquiv.equivOfInverse forward back.fromCompletion
    (fun z ↦ DFunLike.congr_fun hleft z) ?_, hH⟩
  intro z
  refine Completion.induction_on z (isClosed_eq (forward.continuous.comp back.fromCompletion.continuous)
    continuous_id) fun b ↦ ?_
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  change H (k (e.symm b)) = _
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, Completion.coe_toComplL, e.apply_symm_apply] using
    DFunLike.congr_fun hright (e.symm b)

/-- Paper: Proposition C.2.3.9(1), p. 680. The direct sum of the completed tensors is
isomorphic to the completed tensor of the direct sum. Its isomorphism extends the stage maps. -/
theorem completedProjectiveTensor_directSum :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I E)
    let Y := fun i ↦ Completion (ProjectiveTensor (E i) F)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I Y)
    ∃ e : (⨁ i, Y i) ≃L[ℂ] Completion (ProjectiveTensor (⨁ i, E i) F),
      ∀ i (z : Y i), e (DirectSum.lof ℂ I Y i z) =
        Completion.map (projectiveTensorMap (DirectSum.lof ℂ I E i) (LinearMap.id (M := F))) z :=
  by
  let u := DirectSum.lof ℂ I E
  let := locallyConvexFinalTopology u
  let V (i : I) := ProjectiveTensor (E i) F
  let B := ProjectiveTensor (⨁ i, E i) F
  let e : (⨁ i, V i) ≃ₗ[ℂ] B := (TensorProduct.directSumLeft ℂ ℂ E F).symm
  obtain ⟨h, hh⟩ := lcDirectSum_completion_equiv V e (projectiveTensor_directSum E F)
  refine ⟨h, fun i z ↦ (hh i z).trans ?_⟩
  have he : e.toLinearMap.comp (DirectSum.lof ℂ I V i) =
      projectiveTensorMap (u i) (LinearMap.id (M := F)) := by
    apply TensorProduct.ext'
    exact fun x y ↦ TensorProduct.directSumLeft_symm_lof_tmul ℂ ℂ i x y
  rw [he]

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
    IsHomeomorph (Module.DirectLimit.of ℂ Unit (fun _ ↦ V) f ()) := by
  intro f
  letI := lcDirectLimitTopology (X := fun _ : Unit ↦ V) f
  let L := Module.DirectLimit (fun _ : Unit ↦ V) f
  let e := Module.DirectLimit.of ℂ Unit (fun _ ↦ V) f
  let g : L →ₗ[ℂ] V :=
    Module.DirectLimit.lift ℂ Unit (fun _ ↦ V) f (fun _ ↦ LinearMap.id) (fun _ _ _ _ ↦ rfl)
  have hge (x : V) : g (e () x) = x :=
    Module.DirectLimit.lift_of (G := fun _ ↦ V) (f := f) (fun _ ↦ LinearMap.id) (fun _ _ _ _ ↦ rfl) x
  have heg (z : L) : e () (g z) = z := by
    obtain ⟨⟨⟩, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [hge]
  -- The final topology is generated by the seminorms that are continuous on the stage.
  let P : SeminormFamily ℂ L {p : Seminorm ℂ L // ∀ k, Continuous (p ∘ e k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have hV := PolynormableSpace.withSeminorms ℂ V
  have := hV.isTopologicalAddGroup
  have he : Continuous (e ()) := hP.continuous_of_continuous_comp _ fun s ↦ s.property ()
  have hg : Continuous g := hV.continuous_of_continuous_comp _ fun q ↦ by
    have hq : ∀ k, Continuous (((q.1).comp g) ∘ e k) := by
      rintro ⟨⟩
      have : ((q.1).comp g) ∘ e () = q.1 := funext fun x ↦ by simp [hge]
      rw [this]
      exact q.2
    exact hP.continuous_seminorm ⟨(q.1).comp g, hq⟩
  exact (Homeomorph.mk ⟨e (), g, hge, heg⟩ he hg).isHomeomorph

variable [Nonempty I] [IsDirectedOrder I] [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
variable (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
  (hf : ∀ i j h, Continuous (f i j h))

/-- A family uniformly bounded on a neighborhood in each stage of an exhaustive final
system has a common continuous seminorm bound on the limit. -/
private theorem finalTopology_seminorm_majorant {K Z A : Type*} [Nonempty A] {V : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, PolynormableSpace ℂ (V i)]
    (u : ∀ i, V i →ₗ[ℂ] Z) (hu : ∀ z, ∃ i x, u i x = z) (s : A → Seminorm ℂ Z)
    (hs : ∀ i, ∃ U ∈ 𝓝 (0 : V i), ∃ c : ℝ, ∀ x ∈ U, ∀ k, s k (u i x) ≤ c) :
    letI := locallyConvexFinalTopology u
    ∃ t : Seminorm ℂ Z, Continuous t ∧ ∀ k, s k ≤ t := by
  let := locallyConvexFinalTopology u
  choose U hU c hc using hs
  have hb : BddAbove (range s) := Seminorm.bddAbove_range_iff.mpr fun z ↦ by
    obtain ⟨i, x, rfl⟩ := hu z
    have hi : BddAbove (range fun k ↦ (s k).comp (u i)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero (hU i)) fun x hx ↦
        ⟨c i, forall_mem_range.mpr (hc i x hx)⟩
    exact Seminorm.bddAbove_range_iff.mp hi x
  refine ⟨⨆ k, s k, (finalTopology_withSeminorms u).continuous_seminorm ⟨_, fun i ↦ ?_⟩,
    le_ciSup hb⟩
  have := PolynormableSpace.isTopologicalAddGroup ℂ (V i)
  apply Seminorm.continuous' (p := (⨆ k, s k).comp (u i)) (r := c i)
  refine mem_of_superset (hU i) fun x hx ↦ ?_
  rw [Seminorm.mem_closedBall_zero, Seminorm.comp_apply, Seminorm.iSup_apply hb]
  exact ciSup_le (hc i x hx)

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
      _ _ (TensorProduct.fromDirectLimit f F) := by
  let L := Module.DirectLimit X f
  let u := Module.DirectLimit.of ℂ I X f
  let := lcDirectLimitTopology f
  let Y (i : I) := ProjectiveTensor (X i) F
  let w : ∀ i, Y i →ₗ[ℂ] _ := Module.DirectLimit.of ℂ I (fun i ↦ X i ⊗[ℂ] F)
    (fun i j h ↦ (f i j h).rTensor F)
  let := locallyConvexFinalTopology w
  let e : ProjectiveTensor L F ≃ₗ[ℂ] _ := TensorProduct.directLimitLeft f F
  have : ∀ i, IsTopologicalAddGroup (X i) := fun i ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  have hu := continuous_finalTopology_stage u
  have hL := finalTopology_withSeminorms u
  have hW := finalTopology_withSeminorms w
  have : IsTopologicalAddGroup L := hL.isTopologicalAddGroup
  change IsHomeomorph e.symm
  refine e.symm.isHomeomorph_iff.mpr ⟨?_, ?_⟩
  · refine (projectiveTensor_withSeminorms L F).continuous_of_continuous_comp e.symm.toLinearMap fun p ↦ ?_
    refine hW.continuous_seminorm ⟨p.val.comp e.symm.toLinearMap, fun i ↦ ?_⟩
    refine (projectiveTensor_withSeminorms (X i) F).continuous_seminorm
      ⟨(p.val.comp e.symm.toLinearMap).comp (w i), ?_⟩
    have hprod := ((hu i).comp continuous_fst).prodMk (continuous_snd (X := X i) (Y := F))
    change ContinuousAt (fun a : X i × F ↦ p.val (e.symm (w i (a.1 ⊗ₜ[ℂ] a.2)))) 0
    have he (x : X i) (y : F) : e.symm (w i (x ⊗ₜ[ℂ] y)) = u i x ⊗ₜ[ℂ] y :=
      directLimitLeft_symm_of_tmul f F x y
    simp only [he]
    exact p.property.comp_of_eq (hprod.continuousAt (x := 0)) (by simp)
  · refine hW.continuous_of_continuous_comp e.toLinearMap fun p ↦ ?_
    let r := p.val.comp e.toLinearMap
    refine (projectiveTensor_withSeminorms L F).continuous_seminorm ⟨r, ?_⟩
    let := IsNormableSpace.toSeminormedAddCommGroup ℂ F
    let := IsNormableSpace.toNormedSpace ℂ F
    have hstage (i : I) : ContinuousAt (fun v : X i × F ↦ p.val (w i (v.1 ⊗ₜ[ℂ] v.2))) 0 :=
      (p.property i).continuousAt.comp (continuousAt_projectiveTensor_tmul_zero _ _)
    choose q hq hbound using fun i ↦ projectiveTensor_seminorm_unitBall_bound (p.val.comp (w i)) (hstage i)
    let B := {y : F // ‖y‖ < 1}
    let s (y : B) := r.comp ((TensorProduct.mk ℂ L F).flip y.val)
    have hs (i : I) (x : X i) (y : B) : s y (u i x) ≤ q i x := by
      change p.val (e ((u i x) ⊗ₜ[ℂ] y.val)) ≤ _
      rw [show e ((u i x) ⊗ₜ[ℂ] y.val) = w i (x ⊗ₜ[ℂ] y.val) from directLimitLeft_tmul_of f F x y.val]
      exact hbound i x y.val y.property
    have : Nonempty B := ⟨⟨0, by simp⟩⟩
    obtain ⟨t, ht, hst⟩ := finalTopology_seminorm_majorant u Module.DirectLimit.exists_of s fun i ↦
      ⟨(q i).ball 0 1, (q i).ball_mem_nhds (hq i) one_pos, 1, fun x hx y ↦
        (hs i x y).trans ((q i).mem_ball_zero.mp hx).le⟩
    have hball : ∀ᶠ v : L × F in 𝓝 0, ‖v.2‖ < 1 := by
      have h : {y : F | ‖y‖ < 1} ∈ 𝓝 (0 : L × F).2 :=
        NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem one_pos
      exact continuous_snd.continuousAt.preimage_mem_nhds h
    change Tendsto (fun v : L × F ↦ r (v.1 ⊗ₜ[ℂ] v.2)) (𝓝 0) (𝓝 _)
    simp only [Prod.fst_zero, TensorProduct.zero_tmul]
    change Tendsto _ _ (𝓝 (r (0 : ProjectiveTensor L F)))
    rw [map_zero]
    have hdom : ∀ᶠ v : L × F in 𝓝 0, r (v.1 ⊗ₜ[ℂ] v.2) ≤ t v.1 :=
      hball.mono fun v hv ↦ hst ⟨v.2, hv⟩ v.1
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ apply_nonneg r _) hdom
      ((ht.comp continuous_fst).tendsto' 0 0 (map_zero t))

end Limits

/-- Row and column weights dominate any countable matrix of nonnegative bounds. -/
private theorem exists_row_column_weights (c : ℕ → ℕ → ℝ) (hc : ∀ i j, 0 ≤ c i j) :
    ∃ a b : ℕ → ℝ, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ ∀ i j, c i j ≤ a i * b j := by
  let a i := 1 + ∑ j ∈ Finset.range (i+1), c i j
  let b j := 1 + ∑ i ∈ Finset.range j, c i j
  have ha i : 1 ≤ a i := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hc i j)
  have hb j : 1 ≤ b j := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hc i j)
  refine ⟨a, b, fun i ↦ one_pos.trans_le (ha i), fun j ↦ one_pos.trans_le (hb j), fun i j ↦ ?_⟩
  rcases le_or_gt j i with h | h
  · have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.range (i+1)) ↦ hc i k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    exact (hs.trans (le_add_of_nonneg_left zero_le_one)).trans
      (le_mul_of_one_le_right (zero_le_one.trans (ha i)) (hb j))
  · have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.range j) ↦ hc k j)
      (Finset.mem_range.mpr h)
    exact (hs.trans (le_add_of_nonneg_left zero_le_one)).trans
      (le_mul_of_one_le_left (zero_le_one.trans (hb j)) (ha i))

section CountableLimits

variable {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, IsNormableSpace ℂ (X n)] [∀ n, T2Space (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, IsNormableSpace ℂ (Y n)] [∀ n, T2Space (Y n)]

-- The proof only uses continuity of the stage maps into the final topologies.
set_option linter.unusedVariables false in
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
        (Module.DirectLimit.of ℂ ℕ X f ij.1) (Module.DirectLimit.of ℂ ℕ Y g ij.2)) := by
  let u := Module.DirectLimit.of ℂ ℕ X f
  let v := Module.DirectLimit.of ℂ ℕ Y g
  let := lcDirectLimitTopology f
  let := lcDirectLimitTopology g
  let L := Module.DirectLimit X f
  let M := Module.DirectLimit Y g
  let T := ProjectiveTensor L M
  let stage (ij : ℕ × ℕ) := projectiveTensorMap (u ij.1) (v ij.2)
  let : ∀ i, SeminormedAddCommGroup (X i) := fun i ↦ IsNormableSpace.toSeminormedAddCommGroup ℂ _
  let : ∀ i, NormedSpace ℂ (X i) := fun i ↦ IsNormableSpace.toNormedSpace ℂ _
  let : ∀ i, SeminormedAddCommGroup (Y i) := fun i ↦ IsNormableSpace.toSeminormedAddCommGroup ℂ _
  let : ∀ i, NormedSpace ℂ (Y i) := fun i ↦ IsNormableSpace.toNormedSpace ℂ _
  have hu := continuous_finalTopology_stage u
  have hv := continuous_finalTopology_stage v
  have : PolynormableSpace ℂ L := (finalTopology_withSeminorms u).toPolynormableSpace
  have : PolynormableSpace ℂ M := (finalTopology_withSeminorms v).toPolynormableSpace
  let gen (p : Seminorm ℂ T) := ContinuousAt (fun z : L × M ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0
  suffices h : gen = fun p : Seminorm ℂ T ↦ ∀ ij, Continuous (p ∘ stage ij) by
    change (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype gen → _)).topology = _
    rw [h]
    rfl
  funext p
  apply propext
  constructor
  · intro hp ij
    refine (projectiveTensor_withSeminorms (X ij.1) (Y ij.2)).continuous_seminorm
      ⟨p.comp (stage ij), ?_⟩
    have hprod := ((hu ij.1).comp continuous_fst).prodMk ((hv ij.2).comp continuous_snd)
    exact hp.comp_of_eq (hprod.continuousAt (x := 0)) (by simp)
  · intro hp
    have hstage (i j : ℕ) : ContinuousAt (fun z : X i × Y j ↦ p (stage (i,j) (z.1 ⊗ₜ[ℂ] z.2))) 0 :=
      (hp (i,j)).continuousAt.comp (continuousAt_projectiveTensor_tmul_zero _ _)
    choose q hq hbound using fun i j ↦
      projectiveTensor_seminorm_unitBall_bound (p.comp (stage (i,j))) (hstage i j)
    choose c hc hnorm using fun i j ↦ (q i j).bound_of_continuous_normedSpace (hq i j)
    obtain ⟨a, b, ha, hb, hab⟩ := exists_row_column_weights c fun i j ↦ (hc i j).le
    let B := (j : ℕ) × {y : Y j // ‖y‖ < 1}
    have : Nonempty B := ⟨⟨0, 0, by simp⟩⟩
    let s (k : B) := (b k.1).toNNReal⁻¹ • p.comp ((TensorProduct.mk ℂ L M).flip (v k.1 k.2.val))
    have hs (k : B) (x : L) : s k x = (b k.1)⁻¹ * p (x ⊗ₜ[ℂ] v k.1 k.2.val) := by
      change (↑((b k.1).toNNReal⁻¹) : ℝ) * _ = _
      rw [NNReal.coe_inv, Real.coe_toNNReal _ (hb _).le]
      rfl
    obtain ⟨t, ht, hst⟩ := finalTopology_seminorm_majorant u Module.DirectLimit.exists_of s fun i ↦ by
      refine ⟨{x | ‖x‖ < 1}, NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem one_pos, a i, ?_⟩
      rintro x hx ⟨j, y, hy⟩
      rw [hs, inv_mul_le_iff₀ (hb j), mul_comm (b j)]
      exact (hbound i j x y hy).trans ((hnorm i j x).trans
        ((mul_le_of_le_one_right (hc i j).le (le_of_lt hx)).trans (hab i j)))
    let A := {x : L // t x ≤ 1}
    have : Nonempty A := ⟨⟨0, by simp⟩⟩
    let r (x : A) := p.comp (TensorProduct.mk ℂ L M x.val)
    obtain ⟨w, hw, hrw⟩ := finalTopology_seminorm_majorant v Module.DirectLimit.exists_of r fun j ↦ by
      refine ⟨{y | ‖y‖ < 1}, NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem one_pos, b j, ?_⟩
      intro y hy x
      have h := (hst (⟨j, y, hy⟩ : B) x.val).trans x.property
      rw [hs, inv_mul_le_iff₀ (hb j), mul_one] at h
      exact h
    have hpcont : Continuous (p : T → ℝ) := by
      apply Seminorm.continuous' (r := 1)
      refine mem_of_superset (projectiveTensor_absConvexHull_mem_nhds
        (t.ball_mem_nhds ht one_pos) (w.ball_mem_nhds hw one_pos)) ?_
      apply absConvexHull_min _ ⟨p.balanced_closedBall_zero _, (convex_RCLike_iff_convex_real (K := ℂ)).2
        (p.convex_closedBall 0 1)⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact p.mem_closedBall_zero.mpr ((hrw ⟨x, (t.mem_ball_zero.mp hx).le⟩ y).trans
        (w.mem_ball_zero.mp hy).le)
    exact hpcont.continuousAt.comp (continuousAt_projectiveTensor_tmul_zero _ _)

end CountableLimits

section Sequential

variable {E F G : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] [T2Space G]

/-- Paper: Proposition C.2.3.11, p. 681. A separately sequentially continuous bilinear
map is jointly sequentially continuous if the first factor is Fréchet. -/
theorem seqContinuous_bilinear_of_frechet (hE : IsFrechetTVS E) (A : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (h₁ : ∀ y, SeqContinuous (A.flip y)) (h₂ : ∀ x, SeqContinuous (A x)) :
    SeqContinuous (fun v : E × F ↦ A v.1 v.2) := by
  have : IsTopologicalAddGroup E := hE.choose
  have : MetrizableSpace E := hE.2.2.1
  have : PolynormableSpace ℂ E := hE.2.1
  have : BarrelledSpace ℂ E := isFrechetTVS_barrelled hE
  have := PolynormableSpace.isTopologicalAddGroup ℂ G
  let := IsTopologicalAddGroup.rightUniformSpace E
  let := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  intro u a hu
  let T (n : ℕ) : E →L[ℂ] G := ⟨A.flip (u n).2, (h₁ _).continuous⟩
  have hpoint (x : E) : Tendsto (fun n ↦ T n x) atTop (𝓝 (A x a.2)) :=
    h₂ x (continuous_snd.continuousAt.tendsto.comp hu)
  have heq := (PolynormableSpace.banach_steinhaus (𝓕 := T)
    (fun x ↦ (hpoint x).isVonNBounded_range ℂ)).equicontinuous (0 : E)
  have hzero : Tendsto (fun n ↦ T n ((u n).1 - a.1)) atTop (𝓝 0) := by
    have hx : Tendsto (fun n ↦ (u n).1 - a.1) atTop (𝓝 0) := by
      simpa using (continuous_fst.continuousAt.tendsto.comp hu).sub_const a.1
    intro V hV
    have hb := ((𝓝 (0 : G)).basis_sets.comap (fun x : G × G ↦ x.2 - x.1))
    rw [← uniformity_eq_comap_nhds_zero] at hb
    have h := hb.equicontinuousAt_iff_right.mp heq V hV
    change ∀ᶠ n in atTop, T n ((u n).1 - a.1) ∈ V
    filter_upwards [hx.eventually h] with n hn
    simpa [Function.comp_def] using hn n
  simpa [Function.comp_def, T, map_sub, LinearMap.flip_apply] using hzero.add (hpoint a.1)

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
      (∀ y : F, Continuous (fun x : E ↦ T (x ⊗ₜ[ℂ] y))) := by
  have hsp := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      (∀ x : E, Continuous (fun y : F ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : F, Continuous (fun x : E ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  constructor
  · intro hT
    constructor
    · intro x
      have : @Continuous F (InductiveTensor E F) _ _ (fun y : F ↦ x ⊗ₜ[ℂ] y) :=
        hsp.continuous_of_continuous_comp (TensorProduct.mk ℂ E F x) fun p ↦ p.2.1 x
      exact hT.comp this
    · intro y
      have : @Continuous E (InductiveTensor E F) _ _ (fun x : E ↦ x ⊗ₜ[ℂ] y) :=
        hsp.continuous_of_continuous_comp ((TensorProduct.mk ℂ E F).flip y) fun p ↦ p.2.2 y
      exact hT.comp this
  · rintro ⟨h1, h2⟩
    refine (PolynormableSpace.withSeminorms ℂ G).continuous_of_continuous_comp T fun q ↦ ?_
    have hq : Continuous (fun x : InductiveTensor E F ↦ (q.1.comp T) x) :=
      hsp.continuous_seminorm ⟨q.1.comp T, fun x ↦ (q.2.comp (h1 x)), fun y ↦ (q.2.comp (h2 y))⟩
    exact hq


omit [T2Space E] [T2Space F] in
/-- A seminorm on the tensor product whose values on pure tensors are jointly continuous
at zero is continuous in each factor separately. -/
private theorem separatelyContinuous_of_continuousAt_tmul {q : Seminorm ℂ (E ⊗[ℂ] F)}
    (hq : ContinuousAt (fun v : E × F ↦ q (v.1 ⊗ₜ[ℂ] v.2)) 0) :
    (∀ x : E, Continuous (fun y : F ↦ q (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : F, Continuous (fun x : E ↦ q (x ⊗ₜ[ℂ] y))) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  have h0 : (fun v : E × F ↦ q (v.1 ⊗ₜ[ℂ] v.2)) ⁻¹' Iio 1 ∈ 𝓝 ((0 : E), (0 : F)) :=
    hq.preimage_mem_nhds (Iio_mem_nhds (by simp))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 h0
  constructor
  · intro x
    obtain ⟨c, hc⟩ := ((absorbent_nhds_zero (𝕜 := ℂ) hU) x).eventually.exists
    obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.1 (hc (mem_singleton x))
    have hcont := Seminorm.continuous' (p := q.comp (TensorProduct.mk ℂ E F (c • a)))
      (r := ‖c‖) (Filter.mem_of_superset hV fun y hy ↦ ?_)
    · exact hcont
    have h1 : q (a ⊗ₜ[ℂ] y) < 1 := hUV (Set.mk_mem_prod ha hy)
    simp only [Seminorm.mem_closedBall_zero, Seminorm.comp_apply, TensorProduct.mk_apply,
      ← TensorProduct.smul_tmul', map_smul_eq_mul]
    exact mul_le_of_le_one_right (norm_nonneg c) h1.le
  · intro y
    obtain ⟨c, hc⟩ := ((absorbent_nhds_zero (𝕜 := ℂ) hV) y).eventually.exists
    obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.1 (hc (mem_singleton y))
    have hcont := Seminorm.continuous' (p := q.comp ((TensorProduct.mk ℂ E F).flip (c • b)))
      (r := ‖c‖) (Filter.mem_of_superset hU fun x hx ↦ ?_)
    · exact hcont
    have h1 : q (x ⊗ₜ[ℂ] b) < 1 := hUV (Set.mk_mem_prod hx hb)
    simp only [Seminorm.mem_closedBall_zero, Seminorm.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, TensorProduct.tmul_smul, map_smul_eq_mul]
    exact mul_le_of_le_one_right (norm_nonneg c) h1.le

/-- Paper: §C.2.3.4, p. 682. The identity from the inductive to the projective tensor
product is continuous. -/
theorem continuous_inductiveTensor_to_projectiveTensor :
    @Continuous (InductiveTensor E F) (ProjectiveTensor E F) _ _ id :=
  continuous_withGeneratingSeminorms_of_comp (LinearMap.id : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)
    fun q ↦ ⟨⟨q.val, separatelyContinuous_of_continuousAt_tmul q.property⟩, rfl⟩

/-- Paper: (C.2.3.23), p. 682. The inductive tensor topology of Hausdorff factors is Hausdorff. -/
@[instance]
theorem inductiveTensor_t2 : T2Space (InductiveTensor E F) :=
  T2Space.of_injective_continuous (X := InductiveTensor E F) (Y := ProjectiveTensor E F)
    (f := id) Function.injective_id continuous_inductiveTensor_to_projectiveTensor

/-- Paper: Corollary C.2.3.12, p. 682. For Fréchet factors the identity from the inductive
to the projective tensor product is a linear topological isomorphism. -/
theorem inductiveTensor_to_projectiveTensor_of_frechet (hE : IsFrechetTVS E) (hF : IsFrechetTVS F) :
    @IsHomeomorph (InductiveTensor E F) (ProjectiveTensor E F) _ _ id := by
  let e : InductiveTensor E F ≃ₗ[ℂ] ProjectiveTensor E F := LinearEquiv.refl ℂ _
  change IsHomeomorph e
  refine e.isHomeomorph_iff.mpr ⟨continuous_inductiveTensor_to_projectiveTensor, ?_⟩
  apply (continuous_projectiveTensor_iff e.symm.toLinearMap).mpr
  have h := (continuous_inductiveTensor_iff (LinearMap.id : InductiveTensor E F →ₗ[ℂ] InductiveTensor E F)).mp continuous_id
  have : MetrizableSpace E := hE.2.2.1
  have : MetrizableSpace F := hF.2.2.1
  let A : E →ₗ[ℂ] F →ₗ[ℂ] InductiveTensor E F := TensorProduct.mk ℂ E F
  exact (seqContinuous_bilinear_of_frechet hE A
    (fun y ↦ (h.2 y).seqContinuous) (fun x ↦ (h.1 x).seqContinuous)).continuous

/-- Paper: Corollary C.2.3.12, p. 682. The induced identity map on completions is
also a linear topological isomorphism. -/
theorem completedInductiveTensor_to_projectiveTensor_of_frechet
    (hE : IsFrechetTVS E) (hF : IsFrechetTVS F) :
    IsHomeomorph (@Completion.map (InductiveTensor E F) _ (ProjectiveTensor E F) _ id) := by
  let e : InductiveTensor E F ≃ₗ[ℂ] ProjectiveTensor E F := LinearEquiv.refl ℂ _
  have h : IsHomeomorph e := inductiveTensor_to_projectiveTensor_of_frechet hE hF
  let u : InductiveTensor E F ≃ᵤ ProjectiveTensor E F :=
    { e.toEquiv with
      uniformContinuous_toFun := e.toAddMonoidHom.uniformContinuous_of_continuousAt_zero h.continuous.continuousAt
      uniformContinuous_invFun := e.symm.toAddMonoidHom.uniformContinuous_of_continuousAt_zero
        (e.isHomeomorph_iff.mp h).2.continuousAt }
  exact (Completion.mapEquiv u).toHomeomorph.isHomeomorph

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
    inductiveTensorMap f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] y) = f x ⊗ₜ[ℂ] g y := by
  rfl

/-- Paper: (C.2.3.25)–(C.2.3.27), p. 683. The inductive tensor map is continuous
whenever its two factors are, so it induces the indicated maps of completions. -/
theorem inductiveTensorMap_continuous :
    Continuous (inductiveTensorMap f.toLinearMap g.toLinearMap) :=
  continuous_withGeneratingSeminorms_of_comp (TensorProduct.map f.toLinearMap g.toLinearMap)
    fun q ↦ ⟨⟨q.val.comp (TensorProduct.map f.toLinearMap g.toLinearMap),
      fun x ↦ (q.property.1 (f x)).comp g.continuous,
      fun y ↦ (q.property.2 (g y)).comp f.continuous⟩, rfl⟩

end InductiveMaps

/-- Separate continuity against a Baire factor forces a common finite set of active
product coordinates for a tensor seminorm. -/
private theorem inductiveTensor_finite_active_coordinates {I : Type*} [DecidableEq I]
    {X : I → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [BaireSpace F]
    (p : Seminorm ℂ ((∀ i, X i) ⊗[ℂ] F))
    (h₁ : ∀ x : ∀ i, X i, Continuous (fun y : F ↦ p (x ⊗ₜ[ℂ] y)))
    (h₂ : ∀ y : F, Continuous (fun x : ∀ i, X i ↦ p (x ⊗ₜ[ℂ] y))) :
    ∃ s : Finset I, ∀ x : ∀ i, X i, (∀ i ∈ s, x i = 0) → ∀ y : F, p (x ⊗ₜ[ℂ] y) = 0 := by
  classical
  let A : Set I := {i | ∃ (a : X i) (b : F), p (Pi.single i a ⊗ₜ[ℂ] b) ≠ 0}
  let r (y : F) := p.comp ((TensorProduct.mk ℂ (∀ i, X i) F).flip y)
  choose s hs using fun y ↦ product_seminorm_tail (r y) (h₂ y)
  have hfinite : A.Finite := by
    by_contra hinf
    let k := Set.Infinite.natEmbedding A hinf
    choose a b hn using fun n : ℕ ↦ (k n).property
    let q (n : ℕ) := p.comp (TensorProduct.mk ℂ _ F (Pi.single (k n).val (a n)))
    choose φ hφ hnorm using fun n ↦ exists_dual_norm_eq_seminorm (q n)
      (h₁ (Pi.single (k n).val (a n))) (b n)
    let K (n : ℕ) := (φ n).ker
    have := PolynormableSpace.isTopologicalAddGroup ℂ F
    have : NeBot (𝓝[{c : ℂ | IsUnit c}] 0) := NormedField.nhdsWithin_isUnit_neBot
    have hd (n : ℕ) : Dense (K n : Set F)ᶜ := by
      rw [← interior_eq_empty_iff_dense_compl]
      by_contra h
      have htop := (K n).eq_top_of_nonempty_interior' (nonempty_iff_ne_empty.mpr h)
      have hz : b n ∈ K n := by
        rw [htop]
        exact Submodule.mem_top
      exact hn n ((hnorm n).symm.trans (norm_eq_zero.mpr hz))
    obtain ⟨y, hy⟩ := (dense_iInter_of_isOpen_nat (fun n ↦ (φ n).isClosed_ker.isOpen_compl) hd).nonempty
    have hmem (n : ℕ) : (k n).val ∈ s y := by
      by_contra h
      have hzero := hs y (Pi.single (k n).val (a n)) fun i hi ↦
        Pi.single_eq_of_ne (fun (he : i = (k n).val) ↦ h (he ▸ hi)) _
      have hpos := hφ n y
      change ‖(φ n) y‖ ≤ r y (Pi.single (k n).val (a n)) at hpos
      rw [hzero, norm_le_zero_iff] at hpos
      exact (mem_iInter.mp hy n) hpos
    let emb : ℕ ↪ I := k.trans (Function.Embedding.subtype _)
    exact Set.infinite_range_of_injective emb.injective
      ((s y).finite_toSet.subset (range_subset_iff.mpr hmem))
  refine ⟨hfinite.toFinset, fun x hx y ↦ ?_⟩
  let z : ∀ i, X i := ∑ i ∈ s y, Pi.single i (x i)
  have hdiff : r y (x - z) = 0 := hs y _ fun i hi ↦ by
    simp only [z, Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem i hi, Pi.single_eq_same, sub_self]
    exact fun j _ hj ↦ Pi.single_eq_of_ne hj.symm _
  have hz : r y z ≤ 0 := by
    apply (Finset.le_sum_of_subadditive (r y) (map_zero _).le (map_add_le_add _) (s y)
      (fun i ↦ Pi.single i (x i))).trans
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : i ∈ A
    · simp [hx i (hfinite.mem_toFinset.mpr hi)]
    · exact le_of_eq (not_ne_iff.mp fun hn ↦ hi ⟨x i, y, hn⟩)
  have hle := map_add_le_add (r y) (x-z) z
  rw [sub_add_cancel, hdiff, zero_add] at hle
  exact le_antisymm (hle.trans hz) (apply_nonneg _ _)

/-- The coordinate tensor maps induce the inductive tensor topology when the fixed
factor is Fréchet. Each continuous seminorm can be tested after finite reconstruction. -/
private theorem inductiveTensor_product_isUniformInducing {I : Type*} (X : I → Type*) (F : Type*)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hF : IsFrechetTVS F) :
    IsUniformInducing (fun (z : InductiveTensor (∀ i, X i) F) i ↦
      inductiveTensorMap (LinearMap.proj i) (LinearMap.id (M := F)) z) := by
  classical
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ := hF
  let := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace F := hcomplete
  have : (uniformity F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  have : BaireSpace F := BaireSpace.of_completelyPseudoMetrizable
  let A := InductiveTensor (∀ i, X i) F
  let B (i : I) := InductiveTensor (X i) F
  let P : A →ₗ[ℂ] (∀ i, B i) := LinearMap.pi fun i ↦
    inductiveTensorMap (LinearMap.proj i) (LinearMap.id (M := F))
  let L (i : I) : B i →ₗ[ℂ] A := inductiveTensorMap (LinearMap.single ℂ X i) LinearMap.id
  have hP : Continuous P := continuous_pi fun i ↦ inductiveTensorMap_continuous
    (ContinuousLinearMap.proj i : (∀ i, X i) →L[ℂ] X i) (ContinuousLinearMap.id ℂ F)
  have hL (i : I) : Continuous (L i) := inductiveTensorMap_continuous
    (ContinuousLinearMap.single ℂ X i) (ContinuousLinearMap.id ℂ F)
  change IsUniformInducing P
  apply AddMonoidHom.isUniformInducing_of_isInducing
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm ((hP.tendsto' 0 0 (map_zero P)).le_comap) ?_
  apply (PolynormableSpace.hasBasis_zero_ball ℂ A).ge_iff.mpr
  intro p hp
  have h := (continuous_inductiveTensor_iff (LinearMap.id : A →ₗ[ℂ] A)).mp continuous_id
  obtain ⟨s, hs⟩ := inductiveTensor_finite_active_coordinates p
    (fun x ↦ hp.comp (h.1 x)) (fun y ↦ hp.comp (h.2 y))
  let lift : (∀ i, B i) →ₗ[ℂ] A := ∑ i ∈ s, (L i).comp (LinearMap.proj i)
  have hlift : Continuous lift := by
    change Continuous (fun w ↦ lift w)
    simp only [lift, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact continuous_finsetSum _ fun i _ ↦ (hL i).comp (continuous_apply i)
  let D : ((∀ i, X i) ⊗[ℂ] F) →ₗ[ℂ] ((∀ i, X i) ⊗[ℂ] F) := LinearMap.id - lift.comp P
  have hzero (z : A) : p (D z) = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      let xs : ∀ i, X i := ∑ i ∈ s, Pi.single i (x i)
      have htail : ∀ i ∈ s, (x - xs) i = 0 := by
        intro i hi
        simp only [Pi.sub_apply, xs, Finset.sum_apply]
        rw [Finset.sum_eq_single_of_mem i hi, Pi.single_eq_same, sub_self]
        exact fun k _ hk ↦ Pi.single_eq_of_ne hk.symm _
      have hd : D (x ⊗ₜ[ℂ] y) = (x - xs) ⊗ₜ[ℂ] y := by
        change x ⊗ₜ[ℂ] y - (show (∀ i, X i) ⊗[ℂ] F from lift (P (x ⊗ₜ[ℂ] y))) = _
        rw [TensorProduct.sub_tmul, sub_right_inj, show xs ⊗ₜ[ℂ] y =
          ∑ i ∈ s, Pi.single i (x i) ⊗ₜ[ℂ] y from TensorProduct.sum_tmul _ _ _]
        change lift (P (x ⊗ₜ[ℂ] y)) = ∑ i ∈ s, L i (P (x ⊗ₜ[ℂ] y) i)
        exact LinearMap.sum_apply _ _ _
      rw [hd]
      exact hs _ htail y
    | add z w hz hw =>
      apply le_antisymm _ (apply_nonneg _ _)
      rw [map_add]
      exact (map_add_le_add p _ _).trans (by rw [hz, hw, add_zero])
  refine mem_comap.mpr ⟨lift ⁻¹' p.ball 0 1, (hlift.tendsto' 0 0 (map_zero lift)).eventually
    (p.ball_mem_nhds hp one_pos), fun z hz ↦ ?_⟩
  have hd : (show A from D z) + lift (P z) = z := sub_add_cancel _ _
  have hle := map_add_le_add p (show A from D z) (lift (P z))
  rw [hd, hzero, zero_add] at hle
  exact p.mem_ball_zero.mpr (hle.trans_lt (p.mem_ball_zero.mp hz))

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
      Completion.map (inductiveTensorMap (LinearMap.proj i) (LinearMap.id (M := F))) z) := by
  classical
  let A := InductiveTensor (∀ i, X i) F
  let B (i : I) := InductiveTensor (X i) F
  let P : A →ₗ[ℂ] (∀ i, B i) := LinearMap.pi fun i ↦
    inductiveTensorMap (LinearMap.proj i) (LinearMap.id (M := F))
  have hP : IsUniformInducing P := inductiveTensor_product_isUniformInducing X F hF
  have hd : DenseRange P := by
    intro w
    apply mem_closure_iff_nhds.mpr
    intro U hU
    rw [nhds_pi] at hU
    obtain ⟨s, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
    let L (i : I) : B i →ₗ[ℂ] A := inductiveTensorMap (LinearMap.single ℂ X i) LinearMap.id
    let z : A := ∑ i ∈ s, L i (w i)
    refine ⟨P z, hsub (fun i hi ↦ ?_), z, rfl⟩
    suffices h : P z i = w i by
      rw [h]
      exact mem_of_mem_nhds (hW i)
    let proj := LinearMap.proj (R := ℂ) (φ := X)
    have hcomp (j : I) : P (L j (w j)) i =
        ((proj i).comp (LinearMap.single ℂ X j)).rTensor F (w j) :=
      (LinearMap.rTensor_comp_apply F _ _ _).symm
    simp only [z, map_sum, Finset.sum_apply, hcomp]
    let w₀ (j : I) : X j ⊗[ℂ] F := w j
    change (∑ j ∈ s, ((proj i).comp (LinearMap.single ℂ X j)).rTensor F (w₀ j)) = w₀ i
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [proj, LinearMap.proj_comp_single_same]
    · intro j _ hj
      simp [proj, LinearMap.proj_comp_single_ne ℂ X _ _ hj.symm]
  let C (w : ∀ i, B i) (i : I) := (w i : Completion (B i))
  have hC : IsUniformInducing C := by
    have h (i : I) := (Completion.isUniformInducing_coe (α := B i)).comap_uniformity
    rw [isUniformInducing_iff, Pi.uniformity, Filter.comap_iInf, Pi.uniformity]
    simp_rw [Filter.comap_comap, ← h, Filter.comap_comap]
    rfl
  let pkg : AbstractCompletion A := {
    space := ∀ i, Completion (B i)
    coe := C ∘ P
    uniformStruct := inferInstance
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := hC.comp hP
    dense := (DenseRange.piMap fun _ ↦ Completion.denseRange_coe).comp hd hC.uniformContinuous.continuous }
  let e : Completion A ≃ᵤ (∀ i, Completion (B i)) := Completion.cPkg.compareEquiv pkg
  have he : (fun (z : Completion A) i ↦ Completion.map (inductiveTensorMap
      (LinearMap.proj i) (LinearMap.id (M := F))) z) = e := by
    refine Completion.ext (continuous_pi fun _ ↦ Completion.continuous_map) e.continuous fun z ↦ ?_
    change _ = Completion.cPkg.compare pkg (Completion.cPkg.coe z)
    rw [AbstractCompletion.compare_coe]
    funext i
    exact Completion.map_coe (uniformContinuous_pi.mp hP.uniformContinuous i) z
  rw [he]
  exact e.toHomeomorph.isHomeomorph

end InductiveProduct

/-- A surjective sum of stage maps presents the final locally convex topology as a quotient. -/
private theorem isQuotientMap_finalTopology_sum {K W : Type*} [DecidableEq K] {V : K → Type*}
    [AddCommGroup W] [Module ℂ W] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, PolynormableSpace ℂ (V i)]
    (stage : ∀ i, V i →ₗ[ℂ] W) (hs : Function.Surjective (DirectSum.toModule ℂ K W stage)) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ K V)
    letI := locallyConvexFinalTopology stage
    IsQuotientMap (DirectSum.toModule ℂ K W stage) := by
  let u := DirectSum.lof ℂ K V
  let := locallyConvexFinalTopology u
  let := locallyConvexFinalTopology stage
  have : ∀ i, IsTopologicalAddGroup (V i) := fun i ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  have hD := finalTopology_withSeminorms u
  have := hD.isTopologicalAddGroup
  have := hD.toPolynormableSpace
  have := (finalTopology_withSeminorms stage).toPolynormableSpace
  let q := DirectSum.toModule ℂ K W stage
  have hq (i : K) (x : V i) : q (u i x) = stage i x := DirectSum.toModule_lof ℂ i x
  have hqc : Continuous q := continuous_finalTopology_lift u q fun i ↦ by
    simpa only [Function.comp_def, hq] using continuous_finalTopology_stage stage i
  have : PolynormableSpace ℂ ((⨁ i, V i) ⧸ q.ker) := polynormableSpace_quotient q.ker
  let e := q.quotKerEquivOfSurjective hs
  have he : Continuous e := q.ker.isQuotientMap_mkQL.continuous_iff.mpr hqc
  have he' : Continuous e.symm := by
    apply continuous_finalTopology_lift stage e.symm.toLinearMap
    intro i
    have h (x : V i) : e.symm (stage i x) = q.ker.mkQ (u i x) := by
      rw [← hq]
      exact q.quotKerEquivOfSurjective_symm_apply hs _
    exact (q.ker.mkQL.continuous.comp (continuous_finalTopology_stage u i)).congr fun x ↦ (h x).symm
  exact (Homeomorph.mk e.toEquiv he he').isQuotientMap.comp q.ker.isQuotientMap_mkQL

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
        (Module.DirectLimit.of ℂ I X f ij.1) (Module.DirectLimit.of ℂ J Y g ij.2)) := by
  let u := Module.DirectLimit.of ℂ I X f
  let v := Module.DirectLimit.of ℂ J Y g
  let := locallyConvexFinalTopology u
  let := locallyConvexFinalTopology v
  let T := InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g)
  let stage (ij : I × J) := inductiveTensorMap (u ij.1) (v ij.2)
  have : ∀ i, IsTopologicalAddGroup (X i) := fun i ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  have : ∀ j, IsTopologicalAddGroup (Y j) := fun j ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  have hu := continuous_finalTopology_stage u
  have hv := continuous_finalTopology_stage v
  have : PolynormableSpace ℂ (Module.DirectLimit X f) := (finalTopology_withSeminorms u).toPolynormableSpace
  have : PolynormableSpace ℂ (Module.DirectLimit Y g) := (finalTopology_withSeminorms v).toPolynormableSpace
  let gen (p : Seminorm ℂ T) := (∀ x, Continuous (fun y ↦ p (x ⊗ₜ[ℂ] y))) ∧
    (∀ y, Continuous (fun x ↦ p (x ⊗ₜ[ℂ] y)))
  suffices h : gen = fun p : Seminorm ℂ T ↦ ∀ ij, Continuous (p ∘ stage ij) by
    change (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype gen → _)).topology = _
    rw [h]
    rfl
  funext p
  apply propext
  constructor
  · intro hp ij
    have hgen : WithSeminorms (E := T) (Subtype.val : Subtype gen → _) := ⟨rfl⟩
    exact (hgen.continuous_seminorm ⟨p, hp⟩).comp
      (inductiveTensorMap_continuous ⟨u ij.1, hu _⟩ ⟨v ij.2, hv _⟩)
  · intro hp
    have slices (i : I) (j : J) :=
      (continuous_inductiveTensor_iff
        (LinearMap.id : InductiveTensor (X i) (Y j) →ₗ[ℂ] _)).mp continuous_id
    constructor
    · intro x
      obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of x
      exact (finalTopology_withSeminorms v).continuous_seminorm
        ⟨p.comp (TensorProduct.mk ℂ _ _ (u i a)), fun j ↦ (hp (i,j)).comp ((slices i j).1 a)⟩
    · intro y
      obtain ⟨j, b, rfl⟩ := Module.DirectLimit.exists_of y
      exact (finalTopology_withSeminorms u).continuous_seminorm
        ⟨p.comp ((TensorProduct.mk ℂ _ _).flip (v j b)), fun i ↦ (hp (i,j)).comp ((slices i j).2 b)⟩

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
          (Module.DirectLimit.of ℂ J Y g ij.2)) z) ∧ IsQuotientMap (rangeFactorization T) := by
  let u := Module.DirectLimit.of ℂ I X f
  let v := Module.DirectLimit.of ℂ J Y g
  let := lcDirectLimitTopology f
  let := lcDirectLimitTopology g
  let B := InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g)
  let V (ij : I × J) := InductiveTensor (X ij.1) (Y ij.2)
  let stage (ij : I × J) := inductiveTensorMap (u ij.1) (v ij.2)
  let D := ⨁ ij, V ij
  let lof := DirectSum.lof ℂ (I × J) V
  let := locallyConvexFinalTopology lof
  have hD := finalTopology_withSeminorms lof
  have : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  have : PolynormableSpace ℂ D := hD.toPolynormableSpace
  let := IsTopologicalAddGroup.rightUniformSpace D
  have : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
  let q : D →ₗ[ℂ] B := DirectSum.toModule ℂ _ B stage
  have hq (ij) (z : V ij) : q (lof ij z) = stage ij z := DirectSum.toModule_lof ℂ ij z
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨i, j, b, hb⟩ := exists_pairwise_tensor_stage f g z
    exact ⟨lof (i,j) b, (hq _ _).trans hb⟩
  have hquot : IsQuotientMap q := by
    have ht : (inferInstance : TopologicalSpace B) = locallyConvexFinalTopology stage :=
      inductiveTensor_directLimits f g hf hg hX hY
    change @IsQuotientMap D B _ (inferInstance : TopologicalSpace B) q
    rw [ht]
    exact isQuotientMap_finalTopology_sum stage hsurj
  let Q : D →L[ℂ] B := ⟨q, hquot.continuous⟩
  obtain ⟨e, he⟩ := lcDirectSum_completion_equiv V (LinearEquiv.refl ℂ D)
    (show IsHomeomorph (id : D → D) from (Homeomorph.refl D).isHomeomorph)
  let := locallyConvexFinalTopology (DirectSum.lof ℂ (I × J) (fun ij ↦ Completion (V ij)))
  let T := Q.completion.toLinearMap.comp e.toLinearMap
  refine ⟨T, ?_, ?_⟩
  · intro ij z
    change Q.completion (e (DirectSum.lof ℂ _ _ ij z)) = Completion.map (stage ij) z
    rw [he]
    have hu : UniformContinuous (lof ij) :=
      (lof ij).toAddMonoidHom.uniformContinuous_of_continuousAt_zero (continuous_finalTopology_stage lof ij).continuousAt
    change Completion.map Q (Completion.map (lof ij) z) = _
    refine (congrFun (Completion.map_comp Q.uniformContinuous hu) z).trans ?_
    exact congrArg (fun k : V ij → B ↦ Completion.map k z) (funext (hq ij))
  · have hQ : IsQuotientMap (rangeFactorization Q.completion) :=
      isQuotientMap_rangeFactorization_completion_map q.toAddMonoidHom hquot
    let eqRange : range T = range Q.completion := e.surjective.range_comp Q.completion
    let transport := Homeomorph.setCongr eqRange.symm
    exact transport.isQuotientMap.comp (hQ.comp e.toHomeomorph.isQuotientMap)

-- TODO(paper-gap): In (C.2.3.27) the limit of the completed stages can have a nonzero
-- kernel even when both original limits are Hausdorff. See the tail spaces in the report.

/-- Paper: Proposition C.2.3.13(2), p. 683. The images of the completed pairwise
stages have dense union in the completed inductive tensor of the limits. -/
theorem completedInductiveTensor_stages_dense :
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    Dense (⋃ ij : I × J, range (Completion.map (inductiveTensorMap
      (Module.DirectLimit.of ℂ I X f ij.1) (Module.DirectLimit.of ℂ J Y g ij.2)))) := by
  let u := Module.DirectLimit.of ℂ I X f
  let v := Module.DirectLimit.of ℂ J Y g
  let := lcDirectLimitTopology f
  let := lcDirectLimitTopology g
  let T := InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g)
  let stage (ij : I × J) := inductiveTensorMap (u ij.1) (v ij.2)
  have : ∀ i, IsTopologicalAddGroup (X i) := fun i ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  have : ∀ j, IsTopologicalAddGroup (Y j) := fun j ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  have : PolynormableSpace ℂ (Module.DirectLimit X f) := (finalTopology_withSeminorms u).toPolynormableSpace
  have : PolynormableSpace ℂ (Module.DirectLimit Y g) := (finalTopology_withSeminorms v).toPolynormableSpace
  have hc (ij : I × J) : UniformContinuous (stage ij) := by
    apply (stage ij).toAddMonoidHom.uniformContinuous_of_continuousAt_zero
    exact (inductiveTensorMap_continuous ⟨u ij.1, continuous_finalTopology_stage u _⟩
      ⟨v ij.2, continuous_finalTopology_stage v _⟩).continuousAt
  apply (Completion.denseRange_coe (α := T)).mono
  rintro _ ⟨z, rfl⟩
  obtain ⟨i, j, b, hb⟩ := exists_pairwise_tensor_stage f g z
  refine mem_iUnion.mpr ⟨(i, j), Completion.coe' (α := InductiveTensor (X i) (Y j)) b, ?_⟩
  exact (Completion.map_coe (hc (i,j)) (show InductiveTensor (X i) (Y j) from b)).trans
    (congrArg (Completion.coe' (α := T)) hb)

-- TODO(later): needs §C.2.4 for the strict nuclear Fréchet case of (C.2.3.27).

end InductiveLimits

section Permanence

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ E] [T2Space E]
  [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: Proposition C.2.3.13(3), p. 683. The completed inductive tensor of two
barrelled spaces is barrelled. -/
theorem completedInductiveTensor_barrelled [BarrelledSpace ℂ E] [BarrelledSpace ℂ F] :
    BarrelledSpace ℂ (Completion (InductiveTensor E F)) := by
  let T := InductiveTensor E F
  let j : T →L[ℂ] Completion T := Completion.toComplL
  have hs := (continuous_inductiveTensor_iff (LinearMap.id : T →ₗ[ℂ] T)).mp continuous_id
  constructor
  intro p hp
  let q := p.comp j.toLinearMap
  have hq : @Continuous T ℝ _ _ q := by
    have hgen := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun r : {r : Seminorm ℂ (E ⊗[ℂ] F) //
        (∀ x : E, Continuous (fun y : F ↦ r (x ⊗ₜ[ℂ] y))) ∧
        (∀ y : F, Continuous (fun x : E ↦ r (x ⊗ₜ[ℂ] y)))} ↦ r.val)
    refine hgen.continuous_seminorm ⟨q, ?_, ?_⟩
    · intro x
      exact (q.comp (TensorProduct.mk ℂ E F x)).continuous_of_lowerSemicontinuous
        (hp.comp (j.continuous.comp (hs.1 x)))
    · intro y
      exact (q.comp ((TensorProduct.mk ℂ E F).flip y)).continuous_of_lowerSemicontinuous
        (hp.comp (j.continuous.comp (hs.2 y)))
  have hball : q.closedBall 0 1 ∈ 𝓝 (0 : T) := by
    rw [q.closedBall_zero_eq]
    exact hq.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by simp))
  have hcl := Completion.isDenseInducing_coe.closure_image_mem_nhds hball
  apply p.continuous' (r := 1)
  rw [Completion.coe_zero] at hcl
  refine mem_of_superset hcl (closure_minimal ?_ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    rw [Seminorm.mem_closedBall_zero] at hx ⊢
    exact hx
  · rw [Seminorm.closedBall_zero_eq]
    exact hp.isClosed_preimage 1

-- TODO(paper-gap): The bornological assertion of C.2.3.13(3), with scalar second factor,
-- would make the completion of every bornological space bornological. For a stationary,
-- costationary S in ω₁ containing the successors, C_c(ω₁) restricted to S is bornological
-- for compact convergence, but its completion C_k(S) has a bounded discontinuous tail functional.

end Permanence

-- TODO(later): needs §C.2.4 for Proposition C.2.3.14 (pp. 684–685), including nuclearity
-- of both Fréchet spaces in the embedding and of all the strict countable stages of F.

end RiemannMasullo
