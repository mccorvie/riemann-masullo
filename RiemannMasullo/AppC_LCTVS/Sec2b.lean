module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
public import Mathlib.Analysis.LocallyConvex.Montel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Nuclear spaces and the finest locally convex topology

Masullo, Appendix C, §§C.2.4–C.2.5. At the end we state the results of §C.1 that
require nuclearity. As in the preceding sections, `PolynormableSpace ℂ` expresses
local convexity for the complex vector topology.
-/

@[expose] public noncomputable section

open Set Filter Topology Bornology UniformSpace TensorProduct MeasureTheory
open scoped TensorProduct DirectSum UniformConvergence UniformConvergenceCLM Cardinal

namespace RiemannMasullo

universe v u w

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : ContinuousSMul ℝ E :=
  MulAction.continuousSMul_compHom (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal

/-! ## Nuclear spaces -/

-- The continuity of (C.2.4.1) is already stated in `continuous_projectiveTensor_to_injectiveTensor`.

/-- Paper: Definition C.2.4.1, p. 685. A Hausdorff locally convex space is nuclear
when the linear identity from the projective to the injective tensor product is a
homeomorphism for every Hausdorff locally convex test space.
Deviation: The test-space universe is at least the universe of the given space and
can be raised by an independent universe parameter. -/
def IsNuclearTVS.{test, carrier} (E : Type carrier) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  T2Space E ∧ PolynormableSpace ℂ E ∧
    ∀ (F : Type (max test carrier)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
      (_ : PolynormableSpace ℂ F) (_ : T2Space F),
      @IsHomeomorph (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id

section FiniteDimensionalNuclearity

open scoped Pointwise

variable {E : Type*} {F : Type w} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]

/-- Paper: (C.2.3.7), p. 677. Evaluations against the two polars are bounded on each
tensor, and their supremum is the generating injective seminorm. -/
private theorem injectiveSeminorm_eq_ciSup
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) (z : E ⊗[ℂ] F) :
    let D := (StrongDual.polar ℂ U.val : Type _) × (StrongDual.polar ℂ V.val : Type _)
    BddAbove (range fun f : D ↦ ‖tensorDualForm f.1.val f.2.val z‖) ∧
      injectiveTensorSeminorm U V z = ⨆ f : D, ‖tensorDualForm f.1.val f.2.val z‖ := by
  intro D
  have hbound (z : E ⊗[ℂ] F) :
      ∃ C : ℝ, ∀ (φ : StrongDual.polar ℂ U.val) (ψ : StrongDual.polar ℂ V.val),
        ‖tensorDualForm φ.val ψ.val z‖ ≤ C := by
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
        gcongr
        · exact mul_le_of_le_one_right (norm_nonneg _) hφ
        · exact mul_le_of_le_one_right (norm_nonneg _) hψ
    | add z₁ z₂ h₁ h₂ =>
        obtain ⟨C₁, h₁⟩ := h₁
        obtain ⟨C₂, h₂⟩ := h₂
        refine ⟨C₁ + C₂, fun φ ψ ↦ ?_⟩
        rw [map_add]
        exact (norm_add_le _ _).trans (add_le_add (h₁ φ ψ) (h₂ φ ψ))
  have hBdd (z : E ⊗[ℂ] F) :
      BddAbove (range fun f : StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val ↦
        ‖tensorDualForm f.1.val f.2.val z‖) := by
    obtain ⟨C, hC⟩ := hbound z
    exact ⟨C, forall_mem_range.mpr fun f ↦ hC f.1 f.2⟩
  have hSeminorm : BddAbove (range fun f : D ↦
      (normSeminorm ℂ ℂ).comp (tensorDualForm f.1.val f.2.val)) :=
    Seminorm.bddAbove_range_iff.mpr hBdd
  refine ⟨hBdd z, ?_⟩
  unfold injectiveTensorSeminorm
  rw [← ciSup_prod hSeminorm, Seminorm.iSup_apply hSeminorm]
  rfl

/-- Paper: §C.2.3.2, p. 679. Each injective generator is a projective generator,
by scaling one of the two zero-neighborhoods in the polar bound. -/
private theorem injectiveSeminorm_continuousAt_tmul
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) :
    ContinuousAt (fun v : E × F ↦ injectiveTensorSeminorm U V (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  rw [ContinuousAt, show injectiveTensorSeminorm U V ((0 : E × F).1 ⊗ₜ[ℂ]
    (0 : E × F).2) = 0 by simp, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt ℂ hε
  have hV : c • V.val ∈ 𝓝 (0 : F) := by
    simpa using smul_mem_nhds_smul₀ (norm_pos_iff.mp hc) V.property
  have hUV : U.val ×ˢ (c • V.val) ∈ 𝓝 (0 : E × F) :=
    (nhds_prod_eq (x := (0 : E)) (y := (0 : F))).symm ▸ prod_mem_prod U.property hV
  filter_upwards [hUV] with z hz
  rw [dist_zero_right, Real.norm_of_nonneg (apply_nonneg _ _)]
  refine lt_of_le_of_lt ?_ hcε
  rw [(injectiveSeminorm_eq_ciSup U V _).2]
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  obtain ⟨y, hy, hcy⟩ := hz.2
  have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hz.1
  have hψ := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hy
  rw [tensorDualForm_tmul, ← hcy, map_smul, norm_mul, norm_smul]
  calc
    _ ≤ 1 * (‖c‖ * 1) := by gcongr
    _ = ‖c‖ := by simp

/-- Paper: §C.2.3.2, p. 679. Tensoring with a fixed vector is continuous for the
projective topology. -/
private theorem continuous_projectiveTensor_tmul_left (x : E) :
    Continuous (show F → ProjectiveTensor E F from TensorProduct.mk ℂ E F x) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  refine hP.continuous_of_continuous_comp (TensorProduct.mk ℂ E F x) fun ⟨p, hp⟩ ↦ ?_
  have h : {z : E × F | p (z.1 ⊗ₜ[ℂ] z.2) < 1} ∈ 𝓝 0 :=
    hp.preimage_mem_nhds (show Iio (1 : ℝ) ∈ 𝓝 (p ((0 : E × F).1 ⊗ₜ[ℂ]
      (0 : E × F).2)) by simpa using Iio_mem_nhds one_pos)
  rw [show (0 : E × F) = ((0 : E), (0 : F)) from rfl, nhds_prod_eq] at h
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨a, ha⟩ : ∃ a : ℂ, x ∈ a • U := by
    simpa using (absorbent_nhds_zero (𝕜 := ℂ) hU x).exists
  obtain ⟨x', hx', rfl⟩ := ha
  apply Seminorm.continuous' (r := ‖a‖)
  refine Filter.mem_of_superset hV fun y hy ↦ ?_
  rw [Seminorm.mem_closedBall_zero]
  change p ((a • x') ⊗ₜ[ℂ] y) ≤ ‖a‖
  rw [← smul_tmul', map_smul_eq_mul]
  have hp' : p (x' ⊗ₜ[ℂ] y) < 1 := hUV (a := (x', y)) ⟨hx', hy⟩
  exact mul_le_of_le_one_right (norm_nonneg _) hp'.le

/-- Paper: (C.2.3.6), p. 677. Contracting the first factor with a continuous
functional is continuous for the injective topology. -/
private theorem continuous_injectiveTensor_contract (φ : StrongDual ℂ E) :
    Continuous (show InjectiveTensor E F → F from
      (TensorProduct.lid ℂ F).toLinearMap.comp (φ.toLinearMap.rTensor F)) := by
  let T : E ⊗[ℂ] F →ₗ[ℂ] F :=
    (TensorProduct.lid ℂ F).toLinearMap.comp (φ.toLinearMap.rTensor F)
  have hT (ψ : StrongDual ℂ F) (z : E ⊗[ℂ] F) :
      ψ (T z) = tensorDualForm φ ψ z := by
    have hEq : ψ.toLinearMap.comp T = tensorDualForm φ ψ := by
      apply TensorProduct.ext'
      intro x y
      simp [T, LinearMap.comp_apply, tensorDualForm_tmul, smul_eq_mul]
    exact DFunLike.congr_fun hEq z
  refine (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp
    (show InjectiveTensor E F →ₗ[ℂ] F from T) fun ⟨q, hq⟩ ↦ ?_
  let p := (normSeminorm ℂ ℂ).comp φ.toLinearMap
  let U : {U : Set E // U ∈ 𝓝 0} :=
    ⟨p.closedBall 0 1, Filter.mem_of_superset (p.ball_mem_nhds φ.continuous.norm one_pos)
      (p.ball_subset_closedBall _ _)⟩
  let V : {V : Set F // V ∈ 𝓝 0} :=
    ⟨q.closedBall 0 1, Filter.mem_of_superset (q.ball_mem_nhds hq one_pos)
      (q.ball_subset_closedBall _ _)⟩
  have hφ : φ ∈ StrongDual.polar ℂ U.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun _ hx ↦ (Seminorm.mem_closedBall_zero _).mp hx
  refine Seminorm.continuous_of_le
    ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, V)) fun z ↦ ?_
  change E ⊗[ℂ] F at z
  change q (T z) ≤ injectiveTensorSeminorm U V z
  have norming (G : Type w) [AddCommGroup G] [Module ℂ G] (p : Seminorm ℂ G) (x : G) :
      ∃ g : G →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ p y) ∧ ‖g x‖ = p x := by
    let : SeminormedAddCommGroup G := p.toSeminormedAddCommGroup
    let : NormedSpace ℂ G := ⟨fun c y ↦ (map_smul_eq_mul p c y).le⟩
    obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℂ x
    refine ⟨g.toLinearMap, fun y ↦ (g.le_opNorm y).trans
      (mul_le_of_le_one_left (apply_nonneg p y) hg), ?_⟩
    change ‖g x‖ = p x
    rw [hgx]
    change ‖(p x : ℂ)‖ = p x
    rw [Complex.norm_real, Real.norm_of_nonneg (apply_nonneg p x)]
  obtain ⟨g, hg, hgz⟩ := norming F q (T z)
  have hgcont : Continuous g :=
    (PolynormableSpace.withSeminorms ℂ F).continuous_normedSpace_rng ℂ g
      ⟨{⟨q, hq⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp g ≤ q from hg)⟩
  let ψ : StrongDual ℂ F := ⟨g, hgcont⟩
  have hψ : ψ ∈ StrongDual.polar ℂ V.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦ (hg y).trans ((q.mem_closedBall_zero).mp hy)
  obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup U V z
  rw [← hgz, show g (T z) = ψ (T z) from rfl, hT ψ z, hSup]
  exact le_ciSup hBdd (⟨φ, hφ⟩, ⟨ψ, hψ⟩)

end FiniteDimensionalNuclearity

/-- Paper: Definition C.2.4.1, p. 685. A finite-dimensional Hausdorff locally convex
space is nuclear.
Deviation: This is a check against the finite-dimensional case used on p. 692. -/
theorem isNuclearTVS_of_finiteDimensional (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E] [FiniteDimensional ℂ E] :
    IsNuclearTVS.{v, u} E := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  let b := Module.finBasis ℂ E
  let φ i : StrongDual ℂ E := (b.coord i).toContinuousLinearMap
  let T i : E ⊗[ℂ] F →ₗ[ℂ] F :=
    (TensorProduct.lid ℂ F).toLinearMap.comp ((φ i).toLinearMap.rTensor F)
  -- Reconstruct the tensor from its finitely many basis coordinates.
  have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
    let S i : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F :=
      (TensorProduct.mk ℂ E F (b i)).comp (T i)
    have hS : (∑ i, S i) = (LinearMap.id : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F) := by
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.sum_apply, S, LinearMap.comp_apply, T, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, TensorProduct.mk_apply, LinearMap.id_coe, id_eq]
      change (∑ i, b i ⊗ₜ[ℂ] (b.repr x i • y)) = x ⊗ₜ[ℂ] y
      simp_rw [tmul_smul, smul_tmul']
      rw [← sum_tmul, b.sum_repr]
    have hc : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from
        fun z ↦ ∑ i, S i z) :=
      continuous_finsetSum _ fun i _ ↦
        (continuous_projectiveTensor_tmul_left (F := F) (b i)).comp
          (continuous_injectiveTensor_contract (F := F) (φ i))
    refine hc.congr fun z ↦ ?_
    change E ⊗[ℂ] F at z
    change (∑ i, S i z) = z
    rw [← LinearMap.sum_apply, hS]
    rfl
  -- Each injective seminorm occurs in the projective generating family.
  have hfwd : Continuous (show ProjectiveTensor E F → InjectiveTensor E F from id) := by
    let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
    exact hI.continuous_of_continuous_comp (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)
      (fun ⟨U, V⟩ ↦ hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩)
  let e : ProjectiveTensor E F ≃ₜ InjectiveTensor E F :=
    ⟨Equiv.refl (E ⊗[ℂ] F), hfwd, hback⟩
  exact e.isHomeomorph

section LocalBanach

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Paper: §C.2.4.2, p. 686. Equip the carrier with the seminorm used to construct
the local Banach space. -/
def WithLocalSeminorm (_p : Seminorm ℂ E) := E

instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithLocalSeminorm p) :=
  p.toSeminormedAddCommGroup

instance (p : Seminorm ℂ E) : Module ℂ (WithLocalSeminorm p) :=
  inferInstanceAs (Module ℂ E)

instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithLocalSeminorm p) where
  norm_smul_le c x := le_of_eq (map_smul_eq_mul p c x)

/-- Paper: §C.2.4.2, p. 686. The separated completion for a seminorm is its local
Banach space. For a balanced convex absorbing set we use its Minkowski seminorm. -/
abbrev LocalBanach (p : Seminorm ℂ E) := Completion (WithLocalSeminorm p)

/-- Paper: §C.2.4.2, p. 686. The canonical image in the local Banach space has norm
given by the chosen seminorm. -/
theorem localBanach_norm_coe (p : Seminorm ℂ E) (x : WithLocalSeminorm p) :
    ‖(x : LocalBanach p)‖ = p x :=
  Completion.norm_coe x

/-- Paper: Theorem C.2.4.2(2), p. 686. When the target seminorm is dominated by the
source seminorm, the linear identity extends to a map of the two local Banach spaces. -/
def localBanachMap (p q : Seminorm ℂ E) (h : q ≤ p) : LocalBanach p →L[ℂ] LocalBanach q :=
  let f : WithLocalSeminorm p →ₗ[ℂ] WithLocalSeminorm q := LinearMap.id
  (f.mkContinuousOfExistsBound ⟨1, fun x ↦ (h x).trans_eq (one_mul (p x)).symm⟩).completion

/-- Paper: Theorem C.2.4.2(2), p. 686. The comparison of local Banach spaces sends
the canonical image of each vector to its canonical image for the smaller seminorm. -/
theorem localBanachMap_coe (p q : Seminorm ℂ E) (h : q ≤ p) (x : WithLocalSeminorm p) :
    localBanachMap p q h x = ((show WithLocalSeminorm q from x) : LocalBanach q) := by
  rw [localBanachMap, ContinuousLinearMap.completion_apply_coe]
  rfl

end LocalBanach

section Characterizations

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: §C.2.4.2, p. 686. The canonical map into the local Banach space of a
continuous seminorm is continuous for the original topology. -/
private theorem exists_localBanach_inclusion {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [PolynormableSpace ℂ X] (p : Seminorm ℂ X) (hp : Continuous p) :
    ∃ f : X →L[ℂ] LocalBanach p, ∀ x : X, f x = (show WithLocalSeminorm p from x) := by
  let f : X →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
  refine ⟨⟨f, ?_⟩, fun _ ↦ rfl⟩
  exact (PolynormableSpace.withSeminorms ℂ X).continuous_normedSpace_rng _ f
    ⟨{⟨p, hp⟩}, 1, by
      simpa using (show (normSeminorm ℂ _).comp f ≤ p from
        fun x ↦ (localBanach_norm_coe p x).le)⟩

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. Contracting an algebraic tensor against a
functional on a local Banach space is bounded by the injective seminorm of the tensor. -/
private theorem norm_localBanach_contraction_le {F : Type*} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [PolynormableSpace ℂ F] {p : Seminorm ℂ E} {s : Seminorm ℂ F}
    (V : {V : Set E // V ∈ 𝓝 0}) (W : {W : Set F // W ∈ 𝓝 0})
    (i : E →L[ℂ] LocalBanach p) (j : F →L[ℂ] LocalBanach s)
    (hi : ∀ x ∈ V.val, ‖i x‖ ≤ 1) (hj : ∀ y ∈ W.val, ‖j y‖ ≤ 1)
    (φ : LocalBanach p →L[ℂ] ℂ) (z : E ⊗[ℂ] F) :
    ‖((TensorProduct.lid ℂ (LocalBanach s)).toLinearMap.comp
      (TensorProduct.map (φ.comp i).toLinearMap j.toLinearMap)) z‖ ≤
        ‖φ‖ * injectiveTensorSeminorm V W z := by
  let contract (ψ : LocalBanach p →L[ℂ] ℂ) :=
    (TensorProduct.lid ℂ (LocalBanach s)).toLinearMap.comp
      (TensorProduct.map (ψ.comp i).toLinearMap j.toLinearMap)
  change ‖contract φ z‖ ≤ _
  have unit (ψ : LocalBanach p →L[ℂ] ℂ) (hψ : ‖ψ‖ ≤ 1) :
      ‖contract ψ z‖ ≤ injectiveTensorSeminorm V W z := by
    obtain ⟨g, hg, hgz⟩ := exists_dual_vector'' ℂ (contract ψ z)
    have hψV : ψ.comp i ∈ StrongDual.polar ℂ V.val :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦
        (ψ.le_opNorm (i x)).trans (by simpa using mul_le_mul hψ (hi x hx) (norm_nonneg _) zero_le_one)
    have hgW : g.comp j ∈ StrongDual.polar ℂ W.val :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
        (g.le_opNorm (j y)).trans (by simpa using mul_le_mul hg (hj y hy) (norm_nonneg _) zero_le_one)
    have heq : g.toLinearMap.comp (contract ψ) = tensorDualForm (ψ.comp i) (g.comp j) := by
      apply TensorProduct.ext'
      intro x y
      simp [contract, tensorDualForm_tmul, smul_eq_mul]
    have heqz := DFunLike.congr_fun heq z
    change g (contract ψ z) = _ at heqz
    rw [hgz] at heqz
    obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup V W z
    rw [hSup]
    have h := le_ciSup hBdd (⟨ψ.comp i, hψV⟩, ⟨g.comp j, hgW⟩)
    change ‖tensorDualForm (ψ.comp i) (g.comp j) z‖ ≤ _ at h
    rw [← heqz] at h
    change ‖(‖contract ψ z‖ : ℂ)‖ ≤ _ at h
    simpa only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using h
  by_cases hφ : φ = 0
  · subst φ
    have hz : contract 0 = 0 := by ext x y; simp [contract]
    simp [hz]
  let a : ℂ := ‖φ‖
  have ha : a ≠ 0 := by simpa [a] using hφ
  have hnorm : ‖a‖ = ‖φ‖ := by simp [a]
  let ψ := a⁻¹ • φ
  have hψ : ‖ψ‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ)]
  have heq : contract φ = a • contract ψ := by
    apply TensorProduct.ext'
    intro x y
    simp [contract, ψ, smul_smul, ha]
  rw [heq, LinearMap.smul_apply, norm_smul, hnorm]
  exact mul_le_mul_of_nonneg_left (unit ψ hψ) (norm_nonneg _)

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. A local nuclear series bounds each projective
seminorm with the injective seminorm from the source neighborhood and the second factor. -/
private theorem projectiveSeminorm_le_of_localBanach_series {F : Type*}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    {p q : Seminorm ℂ E} {s : Seminorm ℂ F} (hq : q ≤ p)
    (V : {V : Set E // V ∈ 𝓝 0}) (W : {W : Set F // W ∈ 𝓝 0})
    (i : E →L[ℂ] LocalBanach p) (j : F →L[ℂ] LocalBanach s)
    (hi : ∀ x : E, i x = (show WithLocalSeminorm p from x))
    (hj : ∀ y : F, j y = (show WithLocalSeminorm s from y))
    (hiV : ∀ x ∈ V.val, p x ≤ 1) (hjW : ∀ y ∈ W.val, s y ≤ 1)
    (r : Seminorm ℂ (E ⊗[ℂ] F)) (hr : ∀ x y, r (x ⊗ₜ[ℂ] y) ≤ q x * s y)
    (c : ℕ → ℂ) (φ : ℕ → LocalBanach p →L[ℂ] ℂ) (b : ℕ → LocalBanach q)
    (hc : Summable (fun n ↦ ‖c n‖)) (hφ : Tendsto φ atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hseries : ∀ x, HasSum (fun n ↦ (c n * φ n x) • b n) (localBanachMap p q hq x)) :
    ∃ C : ℝ, ∀ z, r z ≤ C * injectiveTensorSeminorm V W z := by
  let κ : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach r := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hκ (z : E ⊗[ℂ] F) : ‖κ z‖ = r z := localBanach_norm_coe r z
  -- Extend the pure-tensor map to both local completions, with values in the completion for r.
  let B₀ : WithLocalSeminorm q →L[ℂ] WithLocalSeminorm s →L[ℂ] LocalBanach r :=
    ((LinearMap.compr₂ (TensorProduct.mk ℂ E F) κ :
        WithLocalSeminorm q →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] LocalBanach r)).mkContinuous₂ 1
      (fun x y ↦ by
        change ‖κ (x ⊗ₜ[ℂ] y)‖ ≤ 1 * q x * s y
        rw [hκ, one_mul]
        exact hr x y)
  let B₁ := B₀.fromCompletion
  let B : LocalBanach q →L[ℂ] LocalBanach s →L[ℂ] LocalBanach r :=
    ((B₁.flip.fromCompletion).flip)
  have hB₀ : ‖B₀‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hB (x : LocalBanach q) (y : LocalBanach s) : ‖B x y‖ ≤ ‖x‖ * ‖y‖ := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      induction y using Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih y =>
        change ‖(B₁.flip.fromCompletion (y : LocalBanach s)) (x : LocalBanach q)‖ ≤ _
        rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe, Completion.norm_coe]
        exact (B₀.le_opNorm₂ x y).trans
          (by calc
            ‖B₀‖ * ‖x‖ * ‖y‖ ≤ 1 * ‖x‖ * ‖y‖ := by gcongr
            _ = _ := by rw [one_mul])
  let D (n : ℕ) : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach s :=
    (TensorProduct.lid ℂ (LocalBanach s)).toLinearMap.comp
      (TensorProduct.map ((φ n).comp i).toLinearMap j.toLinearMap)
  have hD (n) (z : E ⊗[ℂ] F) :
      ‖D n z‖ ≤ ‖φ n‖ * injectiveTensorSeminorm V W z :=
    norm_localBanach_contraction_le E V W i j
      (fun x hx ↦ by rw [hi, localBanach_norm_coe]; exact hiV x hx)
      (fun y hy ↦ by rw [hj, localBanach_norm_coe]; exact hjW y hy) (φ n) z
  -- Transport the local series across the extended bilinear map on each pure tensor.
  have hs (z : E ⊗[ℂ] F) : HasSum (fun n ↦ c n • B (b n) (D n z)) (κ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hs := (hseries (i x)).map (B.flip (j y)) (B.flip (j y)).continuous
      have heq : B (localBanachMap p q hq (i x)) (j y) = κ (x ⊗ₜ[ℂ] y) := by
        rw [hi, hj, localBanachMap_coe]
        let x' : WithLocalSeminorm q := x
        let y' : WithLocalSeminorm s := y
        change B₁.flip.fromCompletion (y' : LocalBanach s) (x' : LocalBanach q) = _
        rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      rw [← heq]
      refine hs.congr_fun fun n ↦ ?_
      simp [D, smul_smul, ContinuousLinearMap.flip_apply]
    | add z z' hz hz' => simpa only [map_add, smul_add] using hz.add hz'
  obtain ⟨A, hA⟩ := (show Tendsto (fun n ↦ ‖φ n‖) atTop (𝓝 0) by simpa using hφ.norm).bddAbove_range
  obtain ⟨M, hM⟩ := (show Tendsto (fun n ↦ ‖b n‖) atTop (𝓝 0) by simpa using hb.norm).bddAbove_range
  refine ⟨(∑' n, ‖c n‖) * (M * A), fun z ↦ ?_⟩
  have hAz : 0 ≤ A := (norm_nonneg (φ 0)).trans (hA (mem_range_self 0))
  have hMz : 0 ≤ M := (norm_nonneg (b 0)).trans (hM (mem_range_self 0))
  rw [← hκ, mul_assoc]
  apply (hs z).norm_le_of_bounded (hc.hasSum.mul_right _)
  intro n
  rw [norm_smul]
  calc
    _ ≤ ‖c n‖ * (‖b n‖ * ‖D n z‖) := by gcongr; exact hB _ _
    _ ≤ ‖c n‖ * (M * (A * injectiveTensorSeminorm V W z)) := by
      gcongr
      · exact hM (mem_range_self n)
      · exact (hD n z).trans (mul_le_mul_of_nonneg_right (hA (mem_range_self n)) (apply_nonneg _ _))
    _ = _ := by ring

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. A generating projective seminorm is bounded
on pure tensors by the product of two continuous seminorms on the factors. -/
private theorem exists_projectiveSeminorm_pure_bound {F : Type*} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [PolynormableSpace ℂ F] (r : Seminorm ℂ (E ⊗[ℂ] F))
    (hr : ContinuousAt (fun v : E × F ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0) :
    ∃ (q : Seminorm ℂ E) (s : Seminorm ℂ F), Continuous q ∧ Continuous s ∧
      ∀ x y, r (x ⊗ₜ[ℂ] y) ≤ q x * s y := by
  have h : {v : E × F | r (v.1 ⊗ₜ[ℂ] v.2) < 1} ∈ 𝓝 0 :=
    hr.preimage_mem_nhds (show Iio (1 : ℝ) ∈ 𝓝 (r ((0 : E × F).1 ⊗ₜ[ℂ] (0 : E × F).2)) by
      simpa using Iio_mem_nhds one_pos)
  rw [show (0 : E × F) = ((0 : E), (0 : F)) from rfl, nhds_prod_eq] at h
  obtain ⟨U, hU, W, hW, hUW⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨q, hq, hqU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
  obtain ⟨s, hs, hsW⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ F).mem_iff.mp hW
  refine ⟨q, s, hq, hs, fun x y ↦ ?_⟩
  have bound (a b : ℝ) (ha : q x < a) (hb : s y < b) :
      r (x ⊗ₜ[ℂ] y) ≤ a * b := by
    have ha₀ := (apply_nonneg q x).trans_lt ha
    have hb₀ := (apply_nonneg s y).trans_lt hb
    have hx : (a : ℂ)⁻¹ • x ∈ q.ball 0 1 := by
      rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg ha₀.le, inv_mul_lt_iff₀ ha₀, mul_one]
    have hy : (b : ℂ)⁻¹ • y ∈ s.ball 0 1 := by
      rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hb₀.le, inv_mul_lt_iff₀ hb₀, mul_one]
    have hlt : r (((a : ℂ)⁻¹ • x) ⊗ₜ[ℂ] ((b : ℂ)⁻¹ • y)) < 1 :=
      hUW (a := ((a : ℂ)⁻¹ • x, (b : ℂ)⁻¹ • y)) ⟨hqU hx, hsW hy⟩
    have hscaled := hlt.le
    rw [TensorProduct.smul_tmul_smul, map_smul_eq_mul, norm_mul, norm_inv, norm_inv,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha₀.le,
      Real.norm_of_nonneg hb₀.le,
      show a⁻¹ * b⁻¹ = (a * b)⁻¹ by simp [mul_inv_rev, mul_comm]] at hscaled
    rw [inv_mul_le_iff₀ (mul_pos ha₀ hb₀), mul_one] at hscaled
    exact hscaled
  have bound' (a : ℝ) (ha : q x < a) : r (x ⊗ₜ[ℂ] y) ≤ a * s y := by
    have ht : Tendsto (fun b : ℝ ↦ a * b) (𝓝[>] (s y)) (𝓝 (a * s y)) :=
      (continuous_const.mul continuous_id).continuousAt.mono_left inf_le_left
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin (a := s y) (s := Ioi (s y))] with b hb
    exact bound a b ha hb
  have ht : Tendsto (fun a : ℝ ↦ a * s y) (𝓝[>] (q x)) (𝓝 (q x * s y)) :=
    (continuous_id.mul continuous_const).continuousAt.mono_left inf_le_left
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin (a := q x) (s := Ioi (q x))] with a ha
  exact bound' a ha

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. Local nuclear series imply continuity of
the identity from the injective topology to the projective topology. -/
private theorem continuous_injectiveTensor_to_projectiveTensor_of_localSeries
    (h : ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
      ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
        let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
        let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
        let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
        ∃ (c : ℕ → ℂ) (φ : ℕ → LocalBanach p →L[ℂ] ℂ) (y : ℕ → LocalBanach q),
          Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
            ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T x))
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
  let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) // ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦
      p.val)
  refine hP.continuous_of_continuous_comp (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F)
    fun ⟨r, hr⟩ ↦ ?_
  obtain ⟨q, s, hq, hs, hrs⟩ := exists_projectiveSeminorm_pure_bound E r hr
  let U := q.ball 0 1
  let W : {W : Set F // W ∈ 𝓝 0} := ⟨s.ball 0 1, s.ball_mem_nhds hs one_pos⟩
  have hU : U ∈ 𝓝 0 := q.ball_mem_nhds hq one_pos
  obtain ⟨V, hV, bV, cV, hVU, c, φ, b, hc, hφ, hb, hseries⟩ :=
    h U hU (q.balanced_ball_zero 1) (q.convex_ball 0 1)
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
  have := PolynormableSpace.isTopologicalAddGroup (𝕜 := ℂ) (E := E)
  obtain ⟨i, hi⟩ := exists_localBanach_inclusion p (continuous_gauge cV hV)
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion s hs
  have hqeq : gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1)
      (absorbent_nhds_zero hU) = q :=
    DFunLike.coe_injective (q.restrictScalars ℝ).gauge_ball
  have hle := gauge_mono (absorbent_nhds_zero hV) hVU
  have hrs' : ∀ x y, r (x ⊗ₜ[ℂ] y) ≤
      gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1) (absorbent_nhds_zero hU) x * s y := by
    rw [hqeq]
    exact hrs
  let V' : {V : Set E // V ∈ 𝓝 0} := ⟨V, hV⟩
  obtain ⟨C, hC⟩ := projectiveSeminorm_le_of_localBanach_series E hle V' W i j hi hj
    (fun x hx ↦ gauge_le_one_of_mem hx) (fun y hy ↦ (s.mem_ball_zero.mp hy).le)
    r hrs' c φ b hc hφ hb hseries
  let s' : Seminorm ℂ (InjectiveTensor E F) := injectiveTensorSeminorm V' W
  refine Seminorm.continuous_of_le (q := C.toNNReal • s') ?_ fun z ↦ (hC z).trans ?_
  · exact (hI.continuous_seminorm (V', W)).const_smul C.toNNReal
  · exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (apply_nonneg _ _)

/-- Paper: Theorem C.2.4.2(2), p. 686. An absolutely summing local Banach
comparison bounds sums of norms by the weak sums tested against the dual unit ball.
Deviation: This intermediate condition is used to derive the nuclear series. -/
def IsAbsolutelySummingLocalBanachMap {p q : Seminorm ℂ E} (h : q ≤ p) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) (x : Fin n → LocalBanach p) (M : ℝ), 0 ≤ M →
      (∀ φ : LocalBanach p →L[ℂ] ℂ, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ≤ M) →
      ∑ i, ‖localBanachMap p q h (x i)‖ ≤ C * M

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. In a nuclear space, each local Banach
space admits a comparison from a smaller neighborhood with an absolute
summability bound. -/
theorem exists_localBanachMap_absolutelySumming (h : IsNuclearTVS.{v, u} E)
    (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U) :
    ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
      let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
      let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
      IsAbsolutelySummingLocalBanachMap E
        (show q ≤ p from gauge_mono (absorbent_nhds_zero hV) hVU) := by
  classical
  have := PolynormableSpace.isTopologicalAddGroup (𝕜 := ℂ) (E := E)
  let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  let F := ULift.{v} (LocalBanach q →L[ℂ] ℂ)
  have : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion q (continuous_gauge cU hU)
  let B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x f ↦ f.down (j x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  let r := (normSeminorm ℂ ℂ).comp (TensorProduct.lift B)
  have hr : ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0 := by
    have hEval := (ContinuousLinearMap.apply ℂ (E' := LocalBanach q) ℂ).continuous₂
    exact (hEval.comp ((j.continuous.comp continuous_fst).prodMk
      (continuous_uliftDown.comp continuous_snd))).norm.continuousAt
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun r : {r : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ r.val)
  let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
    let e := (h.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
    refine e.continuous_symm.congr fun z ↦ ?_
    exact e.apply_symm_apply z
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous hI r
    ((hP.continuous_seminorm ⟨r, hr⟩).comp hback)
  -- One pair of neighborhoods suffices by intersecting the finitely many pairs.
  let A := U ∩ ⋂ UV ∈ S, (UV.1.val : Set E)
  have hA : A ∈ 𝓝 0 := inter_mem hU (S.iInter_mem_sets.mpr fun UV _ ↦ UV.1.property)
  obtain ⟨p₀, hp₀, hV⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hA
  let V := p₀.ball 0 1
  have hV₀ : V ∈ 𝓝 0 := p₀.ball_mem_nhds hp₀ one_pos
  have bV : Balanced ℂ V := p₀.balanced_ball_zero 1
  have cV : Convex ℝ V := p₀.convex_ball 0 1
  have hVU : V ⊆ U := hV.trans inter_subset_left
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV₀)
  let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV₀) hVU)
  let W : Set F := ⋂ UV ∈ S, (UV.2.val : Set F)
  have hW : W ∈ 𝓝 0 := S.iInter_mem_sets.mpr fun UV _ ↦ UV.2.property
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
  let V' : {V : Set E // V ∈ 𝓝 0} := ⟨V, hV₀⟩
  let W' : {W : Set F // W ∈ 𝓝 0} := ⟨W, hW⟩
  have hVW (UV) (hUV : UV ∈ S) :
      injectiveTensorSeminorm UV.1 UV.2 ≤ injectiveTensorSeminorm V' W' := by
    intro z
    obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup V' W' z
    rw [(injectiveSeminorm_eq_ciSup UV.1 UV.2 z).2, hSup]
    have : Nonempty (StrongDual.polar ℂ UV.1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ UV.2.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    have hφ : φ.val ∈ StrongDual.polar ℂ V :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦
        (StrongDual.mem_polar_iff ℂ _).mp φ.property x
          (mem_iInter₂.mp (hV hx).2 UV hUV)
    have hψ : ψ.val ∈ StrongDual.polar ℂ W :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
        (StrongDual.mem_polar_iff ℂ _).mp ψ.property y (mem_iInter₂.mp hy UV hUV)
    exact le_ciSup hBdd (⟨φ.val, hφ⟩, ⟨ψ.val, hψ⟩)
  have hrVW (z : E ⊗[ℂ] F) : r z ≤ C * injectiveTensorSeminorm V' W' z :=
    (hC z).trans (mul_le_mul_of_nonneg_left ((Finset.sup_le hVW) z) C.coe_nonneg)
  have extend (φ : StrongDual.polar ℂ V) :
      ∃ g : LocalBanach p →L[ℂ] ℂ, ‖g‖ ≤ 1 ∧
        ∀ x : WithLocalSeminorm p, g (x : LocalBanach p) = φ.val x := by
    have bound (x : WithLocalSeminorm p) : ‖φ.val x‖ ≤ ‖x‖ := by
      change ‖φ.val x‖ ≤ gauge V x
      apply le_csInf (absorbent_nhds_zero hV₀).gauge_set_nonempty
      rintro a ⟨ha, y, hy, hxy⟩
      let x' : E := x
      change (a • y : E) = x' at hxy
      change ‖φ.val x'‖ ≤ a
      have hmap : φ.val (a • y) = a • φ.val y := φ.val.toLinearMap.map_smul_of_tower a y
      rw [← hxy, hmap, norm_smul, Real.norm_of_nonneg ha.le]
      exact mul_le_of_le_one_right ha.le ((StrongDual.mem_polar_iff ℂ _).mp φ.property y hy)
    let f := (show WithLocalSeminorm p →ₗ[ℂ] ℂ from φ.val.toLinearMap).mkContinuous 1
      (fun x ↦ (bound x).trans_eq (one_mul _).symm)
    refine ⟨f.fromCompletion, f.fromCompletion.opNorm_le_bound zero_le_one fun x ↦ ?_,
      fun x ↦ f.fromCompletion_apply_coe x⟩
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe, one_mul]
      exact bound x
  have bound (n : ℕ) (x : Fin n → WithLocalSeminorm p) (M : ℝ)
      (hMx : ∀ g : LocalBanach p →L[ℂ] ℂ, ‖g‖ ≤ 1 →
        ∑ i, ‖g (x i : LocalBanach p)‖ ≤ M) :
      ∑ i, ‖T (x i : LocalBanach p)‖ ≤ (C * (2 / δ)) * M := by
    -- Evaluate the tensor against norming functionals for the images of the given family.
    choose g hg hgx using fun i : Fin n ↦ exists_dual_vector'' ℂ (T (x i : LocalBanach p))
    let x' (i : Fin n) : E := x i
    let z : E ⊗[ℂ] F := ∑ i : Fin n, x' i ⊗ₜ[ℂ] (ULift.up (g i) : F)
    have hrz : r z = ∑ i, ‖T (x i : LocalBanach p)‖ := by
      change ‖TensorProduct.lift B z‖ = _
      have hterm (i : Fin n) :
          TensorProduct.lift B (x' i ⊗ₜ[ℂ] (ULift.up (g i) : F)) =
            (‖T (x i : LocalBanach p)‖ : ℂ) := by
        change g i (j (x' i)) = _
        have hji : j (x' i) = T (x i : LocalBanach p) :=
          (hj (x' i)).trans (localBanachMap_coe p q _ (x i)).symm
        exact (congrArg (g i) hji).trans (hgx i)
      rw [show TensorProduct.lift B z = ∑ i, (‖T (x i : LocalBanach p)‖ : ℂ) by
        exact (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ ↦ hterm i)]
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    have heps : injectiveTensorSeminorm V' W' z ≤ M * (2 / δ) := by
      rw [(injectiveSeminorm_eq_ciSup V' W' z).2]
      have : Nonempty (StrongDual.polar ℂ V'.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      have : Nonempty (StrongDual.polar ℂ W'.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      apply ciSup_le
      rintro ⟨φ, ψ⟩
      obtain ⟨f, hf, hfx⟩ := extend ⟨φ.val, φ.property⟩
      have hψ (i : Fin n) : ‖ψ.val (ULift.up (g i))‖ ≤ 2 / δ := by
        let a : ℂ := (δ / 2 : ℝ)
        have ha : ‖a‖ = δ / 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hmem : a • (ULift.up (g i) : F) ∈ W :=
          hδW (by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, ha, ULift.norm_up]
            nlinarith [hg i, mul_le_mul_of_nonneg_left (hg i) (show 0 ≤ δ / 2 by positivity)])
        have hnorm := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hmem
        rw [map_smul, norm_smul, ha] at hnorm
        exact (le_div_iff₀ hδ).mpr (by nlinarith)
      change ‖tensorDualForm φ.val ψ.val z‖ ≤ _
      simp only [z, map_sum, tensorDualForm_tmul]
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ i, ‖f (x i : LocalBanach p)‖ * (2 / δ) := by
          apply Finset.sum_le_sum
          intro i _
          change ‖φ.val (x' i) * ψ.val (ULift.up (g i))‖ ≤ _
          rw [norm_mul, ← hfx (x i)]
          exact mul_le_mul_of_nonneg_left (hψ i) (norm_nonneg _)
        _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hMx f hf) (by positivity)
    rw [← hrz]
    exact (hrVW z).trans (by
      calc
        _ ≤ (C : ℝ) * (M * (2 / δ)) := mul_le_mul_of_nonneg_left heps C.coe_nonneg
        _ = _ := by ring)
  refine ⟨V, hV₀, bV, cV, hVU, (C : ℝ) * (2 / δ), by positivity, fun n x M _ hMx ↦ ?_⟩
  -- Pass the estimate to the completion using the sum of the approximation errors.
  have hd : DenseRange (fun ys : Fin n → WithLocalSeminorm p ↦ fun i ↦ (ys i : LocalBanach p)) :=
    DenseRange.piMap fun _ ↦ Completion.denseRange_coe
  have hclose : ∀ y : Fin n → LocalBanach p, ∑ i, ‖T (y i)‖ ≤
      ((C : ℝ) * (2 / δ)) * (M + ∑ i, ‖y i - x i‖) := by
    intro y
    refine hd.induction_on y ?_ (fun ys ↦ ?_)
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · refine bound n ys _ fun g hg ↦ ?_
      have hdiff (i : Fin n) :
          ‖g (ys i : LocalBanach p)‖ ≤ ‖g (x i)‖ + ‖(ys i : LocalBanach p) - x i‖ := by
        calc
          _ ≤ ‖g (x i)‖ + ‖g ((ys i : LocalBanach p) - x i)‖ := by
            rw [map_sub]
            calc
              _ = ‖g (x i) + (g (ys i : LocalBanach p) - g (x i))‖ := by
                rw [add_comm, sub_add_cancel]
              _ ≤ _ := norm_add_le _ _
          _ ≤ _ := add_le_add le_rfl ((g.le_opNorm _).trans
            (mul_le_of_le_one_left (norm_nonneg _) hg))
      exact (Finset.sum_le_sum fun i _ ↦ hdiff i).trans
        (by rw [Finset.sum_add_distrib]; exact add_le_add (hMx g hg) le_rfl)
  simpa using hclose x

omit [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. Three successive absolutely summing local
Banach comparisons give the null-sequence series for their composite.
Pietsch factorization gives a 2-summing map into a Hilbert space followed by a
bounded map for each comparison. Composing adjacent factors gives two
Hilbert–Schmidt maps between Hilbert spaces. Their composite gives an absolutely
summable rank-one expansion, which can be rescaled to have norm-null factors. -/
theorem localBanachMap_hasSeries_of_three_absolutelySumming
    {p₀ p₁ p₂ p₃ : Seminorm ℂ E} (h₁ : p₀ ≤ p₁) (h₂ : p₁ ≤ p₂) (h₃ : p₂ ≤ p₃)
    (s₁ : IsAbsolutelySummingLocalBanachMap E h₁) (s₂ : IsAbsolutelySummingLocalBanachMap E h₂)
    (s₃ : IsAbsolutelySummingLocalBanachMap E h₃) :
    ∃ (c : ℕ → ℂ) (φ : ℕ → LocalBanach p₃ →L[ℂ] ℂ) (y : ℕ → LocalBanach p₀),
      Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
        ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (localBanachMap p₃ p₀ (h₁.trans (h₂.trans h₃)) x) := by
  sorry

/-- Paper: Theorem C.2.4.2(2), p. 686. Nuclearity is equivalent to the existence,
inside each balanced convex zero-neighborhood, of another such neighborhood for
which the canonical local Banach space map is nuclear.
Deviation: Nuclearity of the Banach space map is expressed by the null-sequence
series characterization (C.2.4.2), with convergence at every input. -/
theorem isNuclearTVS_iff_localBanach_series :
    IsNuclearTVS.{v, u} E ↔
      ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
        ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
          let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
          let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
          let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
          ∃ (c : ℕ → ℂ) (φ : ℕ → LocalBanach p →L[ℂ] ℂ) (y : ℕ → LocalBanach q),
            Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
              ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T x) := by
  constructor
  · intro h U hU bU cU
    obtain ⟨V₁, hV₁, bV₁, cV₁, h₁, s₁⟩ := exists_localBanachMap_absolutelySumming E h U hU bU cU
    obtain ⟨V₂, hV₂, bV₂, cV₂, h₂, s₂⟩ := exists_localBanachMap_absolutelySumming E h V₁ hV₁ bV₁ cV₁
    obtain ⟨V₃, hV₃, bV₃, cV₃, h₃, s₃⟩ := exists_localBanachMap_absolutelySumming E h V₂ hV₂ bV₂ cV₂
    exact ⟨V₃, hV₃, bV₃, cV₃, h₃.trans (h₂.trans h₁),
      localBanachMap_hasSeries_of_three_absolutelySumming E _ _ _ s₁ s₂ s₃⟩
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F _ _ _ _ _
    let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
    have hfwd : Continuous (show ProjectiveTensor E F → InjectiveTensor E F from id) :=
      hI.continuous_of_continuous_comp (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)
        fun ⟨U, V⟩ ↦ hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩
    let e : ProjectiveTensor E F ≃ₜ InjectiveTensor E F :=
      ⟨Equiv.refl (E ⊗[ℂ] F), hfwd, continuous_injectiveTensor_to_projectiveTensor_of_localSeries E h F⟩
    exact e.isHomeomorph

omit [T2Space E] in
/-- Paper: (C.2.4.1), p. 685. Each injective generator is continuous for the
projective topology, so the tensor comparison is uniformly continuous. -/
private theorem uniformContinuous_tensorComparison
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    @UniformContinuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
  let f : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F := LinearMap.id
  apply uniformContinuous_addMonoidHom_of_continuous (f := f)
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun z : E × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  exact (withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_of_continuous_comp f
    fun ⟨U, V⟩ ↦ hP.continuous_seminorm
      ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩

omit [T2Space E] in
/-- Paper: Definition C.2.4.1, p. 685. The tensor comparison is a homeomorphism
exactly when its map on completions is a homeomorphism. -/
private theorem isHomeomorph_completedTensorComparison_iff
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) ↔
      @IsHomeomorph (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
  have hforward := uniformContinuous_tensorComparison E F
  let g : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F := LinearMap.id
  constructor
  · intro h
    have hcomm : (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) ∘
        (Completion.coe' : ProjectiveTensor E F → Completion (ProjectiveTensor E F)) =
        (fun z : ProjectiveTensor E F ↦
          (Completion.coe' : InjectiveTensor E F → Completion (InjectiveTensor E F)) z) := by
      funext z
      exact Completion.map_coe hforward z
    have hind := h.isInducing.comp Completion.isDenseInducing_coe.isInducing
    have hback : Continuous g := hind.continuous_iff.mpr (by
      rw [hcomm]
      exact @Completion.continuous_coe (InjectiveTensor E F) _)
    exact (⟨Equiv.refl (E ⊗[ℂ] F), hforward.continuous, hback⟩ :
      ProjectiveTensor E F ≃ₜ InjectiveTensor E F).isHomeomorph
  · intro h
    have hback : Continuous g := h.isInducing.continuous_iff.mpr
      (@continuous_id (InjectiveTensor E F) _)
    let e : ProjectiveTensor E F ≃ᵤ InjectiveTensor E F :=
      ⟨Equiv.refl (E ⊗[ℂ] F), hforward,
        uniformContinuous_addMonoidHom_of_continuous hback⟩
    exact (Completion.mapEquiv e).toHomeomorph.isHomeomorph

/-- Paper: Theorem C.2.4.2(3), p. 686. Each projective generator can be pulled back
from the projective tensor with the local Banach space of a continuous seminorm on
the second factor. If the comparison there is a homeomorphism, the generator is
continuous for the injective topology on the original tensor product. -/
private theorem continuous_projectiveSeminorm_of_localBanach
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [T2Space F]
    (h : ∀ s : Seminorm ℂ F,
      @IsHomeomorph (ProjectiveTensor E (LocalBanach s)) (InjectiveTensor E (LocalBanach s)) _ _ id)
    (r : Seminorm ℂ (E ⊗[ℂ] F))
    (hr : ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0) :
    @Continuous (InjectiveTensor E F) ℝ _ _ r := by
  obtain ⟨q, s, hq, hs, hbound⟩ := exists_projectiveSeminorm_pure_bound E r hr
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion s hs
  let κ : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach r := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hκ (z : E ⊗[ℂ] F) : ‖κ z‖ = r z := localBanach_norm_coe r z
  -- Extend the pure-tensor map in the second factor, with values in the completion for r.
  let B₀ : WithLocalSeminorm q →L[ℂ] WithLocalSeminorm s →L[ℂ] LocalBanach r :=
    ((TensorProduct.mk ℂ E F).compr₂ κ :
      WithLocalSeminorm q →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] LocalBanach r).mkContinuous₂ 1
      (fun x y ↦ by
        change ‖κ (x ⊗ₜ[ℂ] y)‖ ≤ 1 * q x * s y
        rw [hκ, one_mul]
        exact hbound x y)
  let B := B₀.flip.fromCompletion
  have hcoe (x : E) (y : WithLocalSeminorm s) :
      B (y : LocalBanach s) x = κ (x ⊗ₜ[ℂ] y) := by
    change B₀.flip.fromCompletion (y : LocalBanach s) x = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hB (x : E) (y : LocalBanach s) : ‖B y x‖ ≤ q x * ‖y‖ := by
    induction y using Completion.induction_on with
    | hp =>
      apply isClosed_le
      · exact ((ContinuousLinearMap.apply ℂ (LocalBanach r)
          (show WithLocalSeminorm q from x)).continuous.comp B.continuous).norm
      · exact continuous_const.mul continuous_norm
    | ih y =>
      rw [hcoe, hκ, localBanach_norm_coe s]
      exact hbound x y
  let L : E ⊗[ℂ] LocalBanach s →ₗ[ℂ] LocalBanach r :=
    TensorProduct.lift (LinearMap.mk₂ ℂ (fun x y ↦ B y x)
      (fun _ _ _ ↦ map_add _ _ _) (fun _ _ _ ↦ map_smul _ _ _)
      (fun _ _ _ ↦ by rw [map_add]; rfl) (fun _ _ _ ↦ by rw [map_smul]; rfl))
  let p := (normSeminorm ℂ (LocalBanach r)).comp L
  have hp : ContinuousAt (fun z : E × LocalBanach s ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0 := by
    have ht : Tendsto (fun z : E × LocalBanach s ↦ q z.1 * ‖z.2‖) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun z : E × LocalBanach s ↦ q z.1 * ‖z.2‖) :=
        (hq.comp continuous_fst).mul continuous_snd.norm
      simpa [ContinuousAt] using hcont.continuousAt (x := 0)
    have hzero : p ((0 : E) ⊗ₜ[ℂ] (0 : LocalBanach s)) = 0 := by simp
    change Tendsto _ _ (𝓝 (p ((0 : E) ⊗ₜ[ℂ] (0 : LocalBanach s))))
    rw [hzero]
    exact squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun z ↦ by
      change ‖L (z.1 ⊗ₜ[ℂ] z.2)‖ ≤ _
      rw [show L (z.1 ⊗ₜ[ℂ] z.2) = B z.2 z.1 from TensorProduct.lift.tmul _ _]
      exact hB z.1 z.2) ht
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] LocalBanach s)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] LocalBanach s) //
      ContinuousAt (fun z : E × LocalBanach s ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  have hpP := hP.continuous_seminorm ⟨p, hp⟩
  have hpI : @Continuous (InjectiveTensor E (LocalBanach s)) ℝ _ _ p :=
    (h s).isQuotientMap.continuous_iff.mpr hpP
  have : PolynormableSpace ℂ (LocalBanach s) := (norm_withSeminorms ℂ _).toPolynormableSpace
  let T := injectiveTensorMap (ContinuousLinearMap.id ℂ E).toLinearMap j.toLinearMap
  have hL : L.comp T = κ := by
    apply TensorProduct.ext'
    intro x y
    change L (TensorProduct.map LinearMap.id j.toLinearMap (x ⊗ₜ[ℂ] y)) = κ (x ⊗ₜ[ℂ] y)
    rw [TensorProduct.map_tmul, TensorProduct.lift.tmul]
    change B (j y) x = κ (x ⊗ₜ[ℂ] y)
    rw [hj, hcoe]
  have heq : (fun z : InjectiveTensor E F ↦ p (T z)) = r := by
    funext z
    change ‖(L.comp T) z‖ = r z
    rw [hL]
    exact hκ z
  rw [← heq]
  exact hpI.comp (injectiveTensorMap_continuous (ContinuousLinearMap.id ℂ E) j)

/-- Paper: Theorem C.2.4.2(3), p. 686. Nuclearity can be tested on the completed
projective to injective comparison against Banach spaces. -/
theorem isNuclearTVS_iff_completedTensor_banach :
    IsNuclearTVS.{v, u} E ↔
      ∀ (F : Type (max v u)) (_ : NormedAddCommGroup F) (_ : NormedSpace ℂ F) (_ : CompleteSpace F),
        IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) := by
  constructor
  · intro h F _ _ _
    have : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
    exact (isHomeomorph_completedTensorComparison_iff E F).mpr
      (h.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance)
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F _ _ _ _ _
    have hlocal (s : Seminorm ℂ F) :
        @IsHomeomorph (ProjectiveTensor E (LocalBanach s)) (InjectiveTensor E (LocalBanach s)) _ _ id := by
      have : PolynormableSpace ℂ (LocalBanach s) := (norm_withSeminorms ℂ _).toPolynormableSpace
      exact (isHomeomorph_completedTensorComparison_iff E (LocalBanach s)).mp
        (h (LocalBanach s) inferInstance inferInstance inferInstance)
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun z : E × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
    have hback : @Continuous (InjectiveTensor E F) (ProjectiveTensor E F) _ _ id :=
      hP.continuous_of_continuous_comp
        (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F)
        fun ⟨r, hr⟩ ↦ continuous_projectiveSeminorm_of_localBanach E hlocal r hr
    exact (⟨Equiv.refl (E ⊗[ℂ] F), (uniformContinuous_tensorComparison E F).continuous, hback⟩ :
      ProjectiveTensor E F ≃ₜ InjectiveTensor E F).isHomeomorph

/-- Paper: Theorem C.2.4.2(4), p. 686. Nuclearity is equivalent to the canonical
comparison on completed tensors being a homeomorphism against all Hausdorff locally
convex spaces. -/
theorem isNuclearTVS_iff_completedTensor :
    IsNuclearTVS.{v, u} E ↔
      ∀ (F : Type (max v u)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
        (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) := by
  constructor
  · rintro ⟨_, _, h⟩ F aF mF tF lcF hF
    let e : ProjectiveTensor E F ≃ InjectiveTensor E F :=
      ⟨id, id, fun _ ↦ rfl, fun _ ↦ rfl⟩
    have he := e.isHomeomorph_iff.mp (h F aF mF tF lcF hF)
    have hu : @UniformContinuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id :=
      uniformContinuous_addMonoidHom_of_continuous
        (α := ProjectiveTensor E F) (β := InjectiveTensor E F)
        (f := (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)) he.1
    have hu' : @UniformContinuous (InjectiveTensor E F) (ProjectiveTensor E F) _ _ id :=
      uniformContinuous_addMonoidHom_of_continuous
        (α := InjectiveTensor E F) (β := ProjectiveTensor E F)
        (f := (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F)) he.2
    let eu : ProjectiveTensor E F ≃ᵤ InjectiveTensor E F := ⟨e, hu, hu'⟩
    exact (Completion.mapEquiv eu).toHomeomorph.isHomeomorph
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F aF mF tF lcF hF
    have hc : @Continuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
      let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
        (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
          injectiveTensorSeminorm UV.1 UV.2)
      let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
        (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
          ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
      exact hI.continuous_of_continuous_comp
        (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)
        fun ⟨U, V⟩ ↦ hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩
    have hu : @UniformContinuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id :=
      uniformContinuous_addMonoidHom_of_continuous
        (α := ProjectiveTensor E F) (β := InjectiveTensor E F)
        (f := (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)) hc
    let coeP := Completion.coe' (α := ProjectiveTensor E F)
    let coeI := Completion.coe' (α := InjectiveTensor E F)
    let completedComparison := @Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id
    have hcoe : completedComparison ∘ coeP = coeI ∘ (id : ProjectiveTensor E F → InjectiveTensor E F) :=
      funext (Completion.map_coe (α := ProjectiveTensor E F) (β := InjectiveTensor E F) hu)
    have hi : IsInducing (completedComparison ∘ coeP) :=
      (h F aF mF tF lcF hF).isInducing.comp
        (Completion.isUniformInducing_coe (ProjectiveTensor E F)).isInducing
    rw [hcoe] at hi
    have hid : @IsInducing (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id :=
      (Completion.isUniformInducing_coe (InjectiveTensor E F)).isInducing.of_comp_iff.mp hi
    exact isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨⟨hid, Function.injective_id⟩, Function.surjective_id⟩

end Characterizations

-- Remark C.2.4.3 (p. 686) records other authors' notation for the local Banach space.

section WeakDual

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.2.4.4, p. 687. The local Banach space at a balanced convex
zero-neighborhood in the weak dual is finite-dimensional. -/
theorem finiteDimensional_weakDual_localBanach (U : Set (WeakDual ℂ E)) (hU : U ∈ 𝓝 0)
    (hb : Balanced ℂ U) (hc : Convex ℝ U) :
    FiniteDimensional ℂ (LocalBanach (gaugeSeminorm hb hc (absorbent_nhds_zero hU))) := by
  classical
  let p := gaugeSeminorm hb hc (absorbent_nhds_zero hU)
  let i : WeakDual ℂ E →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
  let evaluations := (topDualPairing ℂ E).toSeminormFamily
  change U ∈ 𝓝 (0 : WeakBilin (topDualPairing ℂ E)) at hU
  obtain ⟨⟨s, r⟩, hr, hsU⟩ :=
    (topDualPairing ℂ E).weakBilin_withSeminorms.hasBasis_zero_ball.mem_iff.mp hU
  let a : WeakDual ℂ E →ₗ[ℂ] (s → ℂ) :=
    LinearMap.pi fun x : s ↦ (topDualPairing ℂ E).flip (x : E)
  have hkerU : (a.ker : Set (WeakDual ℂ E)) ⊆ U := by
    intro φ hφ
    apply hsU
    change φ.toStrongDual ∈ (s.sup evaluations).ball 0 r
    rw [Seminorm.mem_ball_zero]
    refine Seminorm.finset_sup_apply_lt hr fun x hx ↦ ?_
    have hzero : φ x = 0 := congrFun (LinearMap.mem_ker.mp hφ) ⟨x, hx⟩
    change ‖φ x‖ < r
    simpa only [hzero, norm_zero] using hr
  -- Every positive dilate of U contains the kernel of the evaluation map.
  have hker : a.ker ≤ i.ker := by
    intro φ hφ
    let φ' : WithLocalSeminorm p := φ
    have hiφ : ‖i φ‖ = p φ := localBanach_norm_coe p φ'
    rw [LinearMap.mem_ker, ← norm_eq_zero, hiφ]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (apply_nonneg p φ)
    rw [zero_add]
    exact gauge_le_of_mem hε.le
      ⟨ε⁻¹ • φ, hkerU ((a.ker.restrictScalars ℝ).smul_mem ε⁻¹ hφ), smul_inv_smul₀ hε.ne' φ⟩
  have : FiniteDimensional ℂ (WeakDual ℂ E ⧸ a.ker) :=
    FiniteDimensional.of_injective a.quotKerEquivRange.toLinearMap a.quotKerEquivRange.injective
  have hker' : a.ker ≤ i.rangeRestrict.ker := by rwa [LinearMap.ker_rangeRestrict]
  have : FiniteDimensional ℂ i.range :=
    FiniteDimensional.of_surjective (a.ker.liftQ i.rangeRestrict hker') (by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict])
  -- The image in the completion is both dense and closed.
  have hdense : DenseRange i := Completion.denseRange_coe (α := WithLocalSeminorm p)
  apply FiniteDimensional.of_surjective i.range.subtype
  intro z
  have hz := hdense z
  rw [← LinearMap.coe_range, i.range.isClosed_of_finiteDimensional.closure_eq] at hz
  exact ⟨⟨z, hz⟩, rfl⟩

/-- Paper: Lemma C.2.4.4, p. 687. The weak dual of a Hausdorff locally convex space
is nuclear. -/
theorem isNuclearTVS_weakDual : IsNuclearTVS.{v, u} (WeakDual ℂ E) := by sorry

end WeakDual

/-- Paper: Remark C.2.4.5, p. 687. Some Hausdorff locally convex spaces have a weak
dual that fails quasi-completeness. -/
theorem exists_weakDual_not_quasiComplete :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E)
      (_ : PolynormableSpace ℂ E) (_ : T2Space E),
      letI := IsTopologicalAddGroup.rightUniformSpace (WeakDual ℂ E)
      ¬ QuasiCompleteSpace ℂ (WeakDual ℂ E) := by sorry

-- TODO(paper-gap): Footnote 15 leaves the argument for the particular strong dual
-- of a Fréchet space cited in Remark C.2.4.5 unfinished.
-- TODO(later): needs §C.4.1–C.4.2 for the Pettis integral in the weak completion
-- in Lemma C.2.4.6. The scalar identity in (C.2.4.4) is recorded below.

/-- Paper: Lemma C.2.4.6, p. 687. A point in the closed convex hull of a compact
set is represented on continuous functionals by a Radon probability measure on
that set.
Deviation: This states the scalar integral identity in the lemma. The vector-valued
Pettis assertion is deferred to §C.4. -/
theorem closedConvexHull_exists_radon_barycenter
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] (K : Set E) (hK : IsCompact K)
    {x : E} (hx : x ∈ closure (convexHull ℝ K)) :
    letI : MeasurableSpace K := borel K
    ∃ μ : Measure K, μ.Regular ∧ μ.InnerRegular ∧ μ univ = 1 ∧
      ∀ ℓ : StrongDual ℂ E,
        Integrable (fun y : K ↦ ℓ y.val) μ ∧ ℓ x = ∫ y : K, ℓ y.val ∂μ := by sorry

/-- Paper: Remark C.2.4.7, p. 688. For a compact set in a Banach space whose span is
infinite-dimensional, the inverse to the point-evaluation embedding cannot extend
to a continuous linear map on the span of the evaluations. -/
theorem not_exists_continuousLinear_extension_evalInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : Set E) (hK : IsCompact K) (hKspan : ¬ FiniteDimensional ℂ (Submodule.span ℂ K)) :
    let δ : K → WeakDual ℂ C(K, ℂ) := fun y ↦
      StrongDual.toWeakDual (ContinuousMap.evalCLM ℂ y)
    let V := Submodule.span ℂ (range δ)
    ¬ ∃ T : V →L[ℂ] E, ∀ y : K, T ⟨δ y, Submodule.subset_span (mem_range_self y)⟩ = y.val := by sorry

section IntegralForms

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: Proposition C.2.4.8, p. 688. An integral bilinear form is the restriction
of a continuous linear functional on the injective tensor product to pure tensors. -/
def IsIntegralBilinearForm (b : E → F → ℂ) : Prop :=
  ∃ l : StrongDual ℂ (InjectiveTensor E F), ∀ x y, l (x ⊗ₜ[ℂ] y) = b x y

/-- Paper: Proposition C.2.4.8, p. 688. A product of two continuous linear
functionals is an integral bilinear form.
Deviation: This is a check on the definition using a rank-one form. -/
theorem isIntegralBilinearForm_mul (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) :
    IsIntegralBilinearForm (fun x y ↦ φ x * ψ y) := by sorry

/-- Paper: Proposition C.2.4.8, p. 688. A continuous bilinear form is integral
exactly when a positive Radon measure of mass at most one on a product of weakly
closed equicontinuous sets represents it by integrating products of evaluations. -/
theorem isIntegralBilinearForm_iff_radon
    [PolynormableSpace ℂ E] [T2Space E] [PolynormableSpace ℂ F] [T2Space F]
    (b : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hb : Continuous (fun z : E × F ↦ b z.1 z.2)) :
    IsIntegralBilinearForm (fun x y ↦ b x y) ↔
      ∃ (A : Set (WeakDual ℂ E)) (B : Set (WeakDual ℂ F)),
        IsClosed A ∧ IsClosed B ∧ IsCompact A ∧ IsCompact B ∧
        EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 ∧
        EquicontinuousAt (fun ψ : B ↦ (ψ.val : F → ℂ)) 0 ∧
        letI : MeasurableSpace (A × B) := borel (A × B)
        ∃ μ : Measure (A × B), μ.Regular ∧ μ.InnerRegular ∧ μ univ ≤ 1 ∧
          ∀ x y, Integrable (fun z : A × B ↦ z.1.val x * z.2.val y) μ ∧
            b x y = ∫ z : A × B, z.1.val x * z.2.val y ∂μ := by sorry

end IntegralForms

/-- Paper: Theorem C.2.4.9, p. 688. Nuclearity is equivalent to the existence
of a smaller balanced convex zero-neighborhood for each such neighborhood
so that the comparison map between local Banach spaces induces an integral form. -/
theorem isNuclearTVS_iff_localBanach_integral
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] :
    IsNuclearTVS.{v, u} E ↔
      ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
        ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
          let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
          let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
          let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
          IsIntegralBilinearForm (fun (x : LocalBanach p) (φ : StrongDual ℂ (LocalBanach q)) ↦
            φ (T x)) := by sorry


section Permanence

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Lemma C.2.4.10(1), p. 689. A linear subspace of a nuclear space is
nuclear for its subspace topology. -/
theorem isNuclearTVS_submodule (hE : IsNuclearTVS.{v, u} E) (S : Submodule ℂ E) :
    IsNuclearTVS.{v, u} S := by sorry

/-- Paper: Lemma C.2.4.10(1), p. 689. A Hausdorff quotient of a nuclear space is nuclear. -/
theorem isNuclearTVS_quotient (hE : IsNuclearTVS.{v, u} E) (S : Submodule ℂ E)
    [T2Space (E ⧸ S)] : IsNuclearTVS.{v, u} (E ⧸ S) := by sorry

/-- Paper: Lemma C.2.4.10(2), p. 689. A product of nuclear spaces is nuclear for
the product topology. -/
theorem isNuclearTVS_pi {I : Type w} {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, IsNuclearTVS.{max v w, u} (X i)) : IsNuclearTVS.{v, max u w} (∀ i, X i) := by sorry

/-- Paper: Lemma C.2.4.10(2), p. 689. The locally convex direct sum of a countable
family of nuclear spaces is nuclear. -/
theorem isNuclearTVS_directSum {I : Type w} [Countable I] [DecidableEq I] {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, IsNuclearTVS.{max v w, u} (X i)) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I X)
    IsNuclearTVS.{v, max u w} (⨁ i, X i) := by sorry

/-- Paper: Lemma C.2.4.10(3), p. 689. The projective tensor product of two nuclear
spaces is nuclear. -/
theorem isNuclearTVS_projectiveTensor {F : Type w}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsNuclearTVS.{max v w, u} E) (hF : IsNuclearTVS.{max v u, w} F) :
    IsNuclearTVS.{v, max u w} (ProjectiveTensor E F) := by sorry

/-- Paper: Lemma C.2.4.11, p. 689. A Fréchet space is nuclear exactly when its
strong dual is nuclear. -/
theorem isNuclearTVS_strongDual_iff (hE : IsFrechetTVS E) :
    IsNuclearTVS.{v, u} (StrongDual ℂ E) ↔ IsNuclearTVS.{v, u} E := by sorry

/-- Paper: Lemma C.2.4.12(1), p. 689. A Hausdorff locally convex inductive limit
of a sequence of nuclear spaces is nuclear. The transition maps may have kernels. -/
theorem isNuclearTVS_directLimit {X : ℕ → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hX : ∀ i, IsNuclearTVS.{v} (X i))
    (h : @T2Space _ (lcDirectLimitTopology f)) :
    letI := lcDirectLimitTopology f
    IsNuclearTVS.{v} (Module.DirectLimit X f) := by sorry

/-- Paper: Lemma C.2.4.12(2), p. 689. The projective limit of nuclear spaces
is nuclear, with the topology on compatible families induced from the product. -/
theorem isNuclearTVS_projectiveLimit {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {X : I → Type u} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)] (f : ∀ i j, i ≤ j → X j →ₗ[ℂ] X i)
    [DirectedSystem (ι := Iᵒᵈ) X (fun {i j} h ↦ f j i h)]
    (hf : ∀ i j h, Continuous (f i j h)) (hX : ∀ i, IsNuclearTVS.{max v w, u} (X i)) :
    let L : Submodule ℂ (∀ i, X i) := ⨅ i, ⨅ j, ⨅ h : i ≤ j,
      LinearMap.ker (LinearMap.proj i - (f i j h).comp (LinearMap.proj j))
    IsNuclearTVS.{v, max u w} L := by sorry

/-- Paper: Remark C.2.4.13, p. 689. Hausdorffness can fail in locally convex
inductive limits, even for a sequence with nuclear stages.
Deviation: The stages are the countable product of complex lines. -/
theorem exists_directLimit_not_t2 :
    let X := fun _ : ℕ ↦ ℕ → ℂ
    ∃ f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j,
      DirectedSystem X (f · · ·) ∧ (∀ i j h, Continuous (f i j h)) ∧
        ¬ @T2Space _ (lcDirectLimitTopology f) := by sorry

-- Remark C.2.4.14 (p. 689) gives references and explains their Hausdorff convention.

end Permanence

section Approximation

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
  [IsTopologicalAddGroup F]

/-- Paper: (C.2.4.6)–(C.2.4.7), p. 689. The canonical map from the algebraic tensor
of the continuous dual with the target sends a pure tensor to a rank-one operator. -/
def tensorToFiniteRank : StrongDual ℂ E ⊗[ℂ] F →ₗ[ℂ] E →L[ℂ] F :=
  TensorProduct.lift
    { toFun := fun φ ↦ ContinuousLinearMap.smulRightₗ φ
      map_add' := fun φ ψ ↦ LinearMap.ext fun y ↦ ContinuousLinearMap.ext fun x ↦
        add_smul (φ x) (ψ x) y
      map_smul' := fun c φ ↦ LinearMap.ext fun y ↦ ContinuousLinearMap.ext fun x ↦
        mul_smul c (φ x) y }

/-- Paper: (C.2.4.7), p. 689. On a pure tensor the canonical map evaluates the
dual factor on the input and scales the target factor by the result. -/
theorem tensorToFiniteRank_tmul (φ : StrongDual ℂ E) (y : F) (x : E) :
    tensorToFiniteRank (φ ⊗ₜ[ℂ] y) x = φ x • y := rfl

/-- Paper: (C.2.4.6), p. 689. The canonical map from the dual tensor is injective. -/
theorem tensorToFiniteRank_injective :
    Function.Injective (tensorToFiniteRank (E := E) (F := F)) := by sorry

end Approximation

section ApproximationProperty

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.2.4.15(1)–(2), p. 689. The identity is approximable by finite-rank
maps uniformly on precompact sets exactly when those maps are dense among endomorphisms. -/
theorem id_mem_closure_finiteRank_iff_dense :
    (ContinuousLinearMap.id ℂ E : PrecompactConvergenceCLM E E) ∈
      closure (range (tensorToFiniteRank (E := E) (F := E) :
        StrongDual ℂ E ⊗[ℂ] E → PrecompactConvergenceCLM E E)) ↔
    DenseRange (tensorToFiniteRank (E := E) (F := E) :
      StrongDual ℂ E ⊗[ℂ] E → PrecompactConvergenceCLM E E) := by sorry

/-- Paper: Lemma C.2.4.15(2)–(3), p. 689. Density of finite-rank maps for the
precompact convergence topology on endomorphisms is equivalent to the corresponding
density for all targets. -/
theorem dense_finiteRank_iff_forall_targets :
    DenseRange (tensorToFiniteRank (E := E) (F := E) :
      StrongDual ℂ E ⊗[ℂ] E → PrecompactConvergenceCLM E E) ↔
      ∀ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
        (_ : IsTopologicalAddGroup F) (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        DenseRange (tensorToFiniteRank (E := E) (F := F) :
          StrongDual ℂ E ⊗[ℂ] F → PrecompactConvergenceCLM E F) := by sorry

/-- Paper: Lemma C.2.4.15(2), (4), pp. 689–690. Density of finite-rank maps for
the precompact convergence topology on endomorphisms is equivalent to the corresponding
density for all sources. -/
theorem dense_finiteRank_iff_forall_sources :
    DenseRange (tensorToFiniteRank (E := E) (F := E) :
      StrongDual ℂ E ⊗[ℂ] E → PrecompactConvergenceCLM E E) ↔
      ∀ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : UniformSpace F)
        (_ : IsUniformAddGroup F) (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        DenseRange (tensorToFiniteRank (E := F) (F := E) :
          StrongDual ℂ F ⊗[ℂ] E → PrecompactConvergenceCLM F E) := by sorry

/-- Paper: Lemma C.2.4.16(1), p. 690. A bounded set in a nuclear space has
compact closure in the completion. -/
theorem isPrecompactInCompletion_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E)
    {S : Set E} (hS : IsVonNBounded ℂ S) : IsPrecompactInCompletion S := by sorry

/-- Paper: Lemma C.2.4.16(1), p. 690. For a nuclear source, uniform convergence
on bounded sets and on precompact sets give the same topology on the operator space. -/
theorem precompactConvergenceCLM_eq_bounded_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E)
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F] [T2Space F] :
    (inferInstance : TopologicalSpace (PrecompactConvergenceCLM E F)) =
      (inferInstance : TopologicalSpace (E →L[ℂ] F)) := by sorry

/-- Paper: Lemma C.2.4.16(2), p. 690. Finite-rank endomorphisms of a nuclear
space are dense for uniform convergence on precompact sets. -/
theorem dense_finiteRank_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E) :
    DenseRange (tensorToFiniteRank (E := E) (F := E) :
      StrongDual ℂ E ⊗[ℂ] E → PrecompactConvergenceCLM E E) := by sorry

/-- Paper: Remark C.2.4.17, p. 690. For a nuclear source, finite-rank maps are
dense in the strong operator space with uniform convergence on bounded sets. -/
theorem dense_finiteRank_boundedConvergence_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E)
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F] [T2Space F] :
    DenseRange (tensorToFiniteRank (E := E) (F := F)) := by sorry

/-- Paper: Remark C.2.4.17, p. 690. Bounded subsets of a quasi-complete nuclear
space have compact closure in the space itself. -/
theorem isCompact_closure_of_isNuclearTVS [QuasiCompleteSpace ℂ E]
    (hE : IsNuclearTVS.{v, u} E) {S : Set E} (hS : IsVonNBounded ℂ S) :
    IsCompact (closure S) := by sorry

end ApproximationProperty

/-- Paper: Theorem C.2.4.18, p. 690. A jointly continuous bilinear form with
nuclear first factor is an absolutely weighted sum of products of two equicontinuous
sequences of functionals. The series converges uniformly on bounded sets in the product.
Deviation: The second pairing in (C.2.4.8) uses the second space and its dual. -/
theorem schwartz_kernel_series {E : Type u} {F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    (hE : IsNuclearTVS.{v, u} E) (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (hB : Continuous (fun z : E × F ↦ B z.1 z.2)) :
    ∃ (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → StrongDual ℂ F) (c : ℕ → ℂ),
      EquicontinuousAt (fun n : ℕ ↦ (φ n : E → ℂ)) 0 ∧
      EquicontinuousAt (fun n : ℕ ↦ (ψ n : F → ℂ)) 0 ∧ Summable (fun n ↦ ‖c n‖) ∧
      let S := {A : Set (E × F) | IsVonNBounded ℂ A}
      HasSum (fun n ↦ UniformOnFun.ofFun S (fun z : E × F ↦ c n * φ n z.1 * ψ n z.2))
        (UniformOnFun.ofFun S (fun z : E × F ↦ B z.1 z.2)) := by sorry

-- TODO(paper-gap): After (C.2.4.9), continuity into the strong dual need not imply
-- joint continuity of the associated form, even for a complete nuclear space.
-- TODO(later): needs §D.1.4–D.1.5 for the Schwartz–Bruhat spaces in Theorem C.2.4.19.

/-! ## The finest locally convex topology -/

section FinestLocallyConvex

variable (E : Type u) [AddCommGroup E] [Module ℂ E]

/-- Paper: Proposition C.2.5.1(1), p. 691. The vector space with its finest locally
convex topology is the type synonym generated by all seminorms on the carrier. -/
abbrev FinestLocallyConvex := WithGeneratingSeminorms E (id : Seminorm ℂ E → Seminorm ℂ E)

/-- Paper: Proposition C.2.5.1(1), p. 691. All seminorms generate the finest locally
convex topology. -/
theorem finestLocallyConvex_withSeminorms :
    WithSeminorms (E := FinestLocallyConvex E) (id : Seminorm ℂ E → Seminorm ℂ E) :=
  withGeneratingSeminorms_spec E _

/-- Paper: Proposition C.2.5.1(1), p. 691. The finest locally convex topology is
Hausdorff.
Deviation: The Hausdorff property is used throughout the proposition. -/
theorem finestLocallyConvex_t2 : T2Space (FinestLocallyConvex E) := by sorry

/-- Paper: Proposition C.2.5.1(1), p. 691. The topology generated by all seminorms
equals the final locally convex topology of the inclusions of finite-dimensional
subspaces, each with its unique Hausdorff vector topology. -/
theorem finestLocallyConvex_eq_finiteDimensionalFinalTopology :
    (inferInstance : TopologicalSpace (FinestLocallyConvex E)) =
      locallyConvexFinalTopology
        (X := fun S : {S : Submodule ℂ E // FiniteDimensional ℂ S} ↦ FinestLocallyConvex S.val)
        (fun S ↦ S.val.subtype) := by sorry

/-- Paper: Proposition C.2.5.1(2), p. 691. Every linear map from a space with
the finest locally convex topology to a Hausdorff locally convex space is continuous. -/
theorem continuous_of_finestLocallyConvex {M : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] [PolynormableSpace ℂ M] [T2Space M]
    (T : FinestLocallyConvex E →ₗ[ℂ] M) : Continuous T := by sorry

/-- Paper: Proposition C.2.5.1(2), p. 691. Every algebraic functional on the
space with its finest locally convex topology belongs to the continuous dual. -/
theorem finestLocallyConvex_dual_surjective :
    Function.Surjective (fun φ : StrongDual ℂ (FinestLocallyConvex E) ↦ φ.toLinearMap) := by sorry

variable {E}

/-- Paper: Proposition C.2.5.1(3), p. 691. Every linear subspace of a space with
the finest locally convex topology is closed. -/
theorem finestLocallyConvex_submodule_isClosed (S : Submodule ℂ (FinestLocallyConvex E)) :
    IsClosed (S : Set (FinestLocallyConvex E)) := by sorry

/-- Paper: Proposition C.2.5.1(3), p. 691. Every linear subspace is the image
of a continuous linear projection that restricts to the identity on the subspace. -/
theorem finestLocallyConvex_submodule_closedComplemented
    (S : Submodule ℂ (FinestLocallyConvex E)) : S.ClosedComplemented := by sorry

/-- Paper: Proposition C.2.5.1(3), p. 691. A linear subspace inherits its own
finest locally convex topology. -/
theorem finestLocallyConvex_submodule_topology (S : Submodule ℂ (FinestLocallyConvex E)) :
    (inferInstance : TopologicalSpace S) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex S)) := by sorry

/-- Paper: Proposition C.2.5.1(3), p. 691. The quotient topology is the finest
locally convex topology on the quotient vector space. -/
theorem finestLocallyConvex_quotient_topology (S : Submodule ℂ (FinestLocallyConvex E)) :
    (inferInstance : TopologicalSpace (FinestLocallyConvex E ⧸ S)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (FinestLocallyConvex E ⧸ S))) := by sorry

/-- Paper: Proposition C.2.5.1(3), p. 691. The finest locally convex topology
is complete. -/
theorem finestLocallyConvex_completeSpace : CompleteSpace (FinestLocallyConvex E) := by sorry

/-- Paper: Proposition C.2.5.1(4), p. 692. A set is bounded for the finest
locally convex topology precisely when it lies in a finite-dimensional subspace
and is bounded in that subspace's Euclidean topology. -/
theorem finestLocallyConvex_isVonNBounded_iff (B : Set (FinestLocallyConvex E)) :
    IsVonNBounded ℂ B ↔
      ∃ S : Submodule ℂ (FinestLocallyConvex E),
        FiniteDimensional ℂ S ∧ B ⊆ S ∧ IsVonNBounded ℂ ((Subtype.val : S → _) ⁻¹' B) := by
  classical
  constructor
  · intro hB
    have hP := finestLocallyConvex_withSeminorms E
    rw [hP.isVonNBounded_iff_seminorm_bounded] at hB
    obtain ⟨A, hAB, hspan, hA⟩ := exists_linearIndependent ℂ B
    have hfinite : A.Finite := by
      by_contra hinf
      -- Assign the values 0, 1, 2, … to independent vectors of B.
      let e := (show A.Infinite from hinf).natEmbedding A
      let x : ℕ → FinestLocallyConvex E := Subtype.val ∘ e
      have hx : LinearIndependent ℂ x := hA.comp e e.injective
      let b := Module.Basis.span hx
      let f := b.constr ℂ (fun n : ℕ ↦ (n : ℂ))
      obtain ⟨g, hg⟩ := f.exists_extend
      let p : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp g
      obtain ⟨r, -, hr⟩ := hB p
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have hgn : g (x n) = (n : ℂ) := by
        have h := LinearMap.congr_fun hg (b n)
        simpa only [f, b, LinearMap.comp_apply, Submodule.subtype_apply,
          Module.Basis.coe_span_apply, Module.Basis.constr_basis] using h
      have hnr := hr (x n) (hAB (e n).property)
      change ‖g (x n)‖ < r at hnr
      rw [hgn, Complex.norm_natCast] at hnr
      exact lt_asymm hn hnr
    let S := Submodule.span ℂ A
    refine ⟨S, FiniteDimensional.span_of_finite ℂ hfinite, ?_, ?_⟩
    · change B ⊆ (Submodule.span ℂ A : Set _)
      rw [hspan]
      exact Submodule.subset_span
    · have hSP := S.isEmbedding_subtype.isInducing.withSeminorms hP
      rw [hSP.isVonNBounded_iff_seminorm_bounded]
      intro p
      obtain ⟨r, hr, h⟩ := hB p
      exact ⟨r, hr, fun y hy ↦ h y hy⟩
  · rintro ⟨S, -, hBS, hB⟩
    have hsub : B ⊆ S.subtypeL '' ((Subtype.val : S → _) ⁻¹' B) :=
      fun x hx ↦ ⟨⟨x, hBS hx⟩, hx, rfl⟩
    exact (hB.image S.subtypeL).subset hsub

/-- Paper: Proposition C.2.5.1(5), p. 692. A set is sequentially closed for the
finest locally convex topology precisely when each finite-dimensional section is closed. -/
theorem finestLocallyConvex_isSeqClosed_iff (C : Set (FinestLocallyConvex E)) :
    IsSeqClosed C ↔ ∀ S : Submodule ℂ (FinestLocallyConvex E), FiniteDimensional ℂ S →
      IsClosed ((Subtype.val : S → _) ⁻¹' C) := by sorry

/-- Paper: Proposition C.2.5.1(6), p. 692. With its finest locally convex topology,
a countably generated vector space is a strict LF-space. -/
theorem finestLocallyConvex_isStrictLFSpace (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsStrictLFSpace (FinestLocallyConvex E) := by sorry

/-- Paper: Proposition C.2.5.1(6), p. 692. With its finest locally convex topology,
a countably generated vector space is nuclear. -/
theorem finestLocallyConvex_isNuclearTVS (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsNuclearTVS.{v, u} (FinestLocallyConvex E) := by sorry

/-- Paper: Proposition C.2.5.1(6), p. 692. In countable dimension the finest locally
convex topology has the Heine–Borel property. -/
theorem finestLocallyConvex_montelSpace (hE : Module.rank ℂ E ≤ ℵ₀) :
    MontelSpace ℂ (FinestLocallyConvex E) := by sorry

/-- Paper: Proposition C.2.5.1(6), p. 692. In countable dimension the evaluation
map from the finest locally convex space onto its strong bidual is a homeomorphism.
Together with the Heine–Borel property this states the paper's Montel conclusion. -/
theorem finestLocallyConvex_strongBidual (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsHomeomorph (ContinuousLinearMap.applyₗ (E := FinestLocallyConvex E) ℂ (RingHom.id ℂ)) := by sorry

/-- Paper: Proposition C.2.5.1(6), p. 692. The strong dual of a countably generated
space with the finest locally convex topology is Fréchet. -/
theorem finestLocallyConvex_strongDual_isFrechetTVS (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsFrechetTVS (StrongDual ℂ (FinestLocallyConvex E)) := by sorry

-- TODO(paper-gap): In the proof of C.2.5.1(6), an infinite-dimensional countably
-- generated space with the finest locally convex topology need not be Fréchet.

/-- Paper: Proposition C.2.5.1(6), p. 692. The strong dual of a countably generated
space with the finest locally convex topology is nuclear. -/
theorem finestLocallyConvex_strongDual_isNuclearTVS (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsNuclearTVS.{v, u} (StrongDual ℂ (FinestLocallyConvex E)) := by sorry

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- Paper: Lemma C.2.5.2, p. 692. The projective tensor topology of two countably
generated spaces with the finest locally convex topologies is again the finest
locally convex topology, which is complete by Proposition C.2.5.1(3). -/
theorem finestLocallyConvex_projectiveTensor (hE : Module.rank ℂ E ≤ ℵ₀)
    (hF : Module.rank ℂ F ≤ ℵ₀) :
    (inferInstance : TopologicalSpace (ProjectiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (E ⊗[ℂ] F))) := by sorry

/-- Paper: Lemma C.2.5.2, p. 692. The injective tensor topology of two countably
generated spaces with the finest locally convex topologies is again the finest
locally convex topology, which is complete by Proposition C.2.5.1(3). -/
theorem finestLocallyConvex_injectiveTensor (hE : Module.rank ℂ E ≤ ℵ₀)
    (hF : Module.rank ℂ F ≤ ℵ₀) :
    (inferInstance : TopologicalSpace (InjectiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (E ⊗[ℂ] F))) := by sorry

/-- Paper: Lemma C.2.5.2, p. 692. The inductive tensor topology of two countably
generated spaces with the finest locally convex topologies is again the finest
locally convex topology, which is complete by Proposition C.2.5.1(3). -/
theorem finestLocallyConvex_inductiveTensor (hE : Module.rank ℂ E ≤ ℵ₀)
    (hF : Module.rank ℂ F ≤ ℵ₀) :
    (inferInstance : TopologicalSpace (InductiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (E ⊗[ℂ] F))) := by sorry

end FinestLocallyConvex

/-! ## Deferred from §C.1 -/

section Deferred

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Remark C.1.4.7, p. 663. A strict countable inductive limit of nuclear
Fréchet spaces is nuclear.
Deviation: The stages are represented by their increasing images in the limit. -/
theorem isNuclearTVS_of_strictLF_stages [T2Space E]
    (S : ℕ → Submodule ℂ E) (hS : Monotone S)
    (hFrechet : ∀ n, IsFrechetTVS (S n)) (hNuclear : ∀ n, IsNuclearTVS.{v} (S n))
    (hexhaustive : ∀ x : E, ∃ n, x ∈ S n)
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology (fun n ↦ (S n).subtype)) :
    IsNuclearTVS.{v} E := by sorry

/-- Paper: Remark C.1.4.7, p. 663. A nuclear strict LF-space has the Heine–Borel
property. Each stage in a strict presentation is nuclear by Remark C.1.5.12. -/
theorem montelSpace_of_nuclear_strictLF (hLF : IsStrictLFSpace E) (hE : IsNuclearTVS.{v} E) :
    MontelSpace ℂ E := by sorry

/-- Paper: Remark C.1.4.7, p. 663. Evaluation from a nuclear strict LF-space to
the strong bidual is a homeomorphism. Along with the Heine–Borel property, this
states the paper's Montel conclusion. -/
theorem strongBidual_of_nuclear_strictLF [ContinuousSMul ℂ E]
    (hLF : IsStrictLFSpace E) (hE : IsNuclearTVS.{v} E) :
    IsHomeomorph (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)) := by sorry

/-- Paper: Example C.1.5.10, p. 668. A nuclear locally convex space is Schwartz. -/
theorem isSchwartzTVS_of_isNuclearTVS (hE : IsNuclearTVS.{v} E) : IsSchwartzTVS E := by sorry

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
  [∀ n, TopologicalSpace (X n)] {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] E}

/-- Paper: Theorem C.1.5.11, p. 668. In a strict countable limit of nuclear Fréchet
spaces a closed subspace is a limit subspace exactly when its quotient map lifts bounded sets. -/
theorem isLimitSubspace_iff_liftsBoundedSets_of_nuclear
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hNuclear : ∀ n, IsNuclearTVS.{v} (X n))
    (F : Submodule ℂ E) (hF : IsClosed (F : Set E)) :
    IsLimitSubspace i F ↔ LiftsBoundedSets F.mkQL := by sorry

-- TODO(paper-gap): The paragraph after Theorem C.1.5.11 reverses the implication
-- of Example C.1.5.10. Nuclear spaces are Schwartz.

/-- Paper: Remark C.1.5.12, p. 668. Every strict defining sequence of a nuclear
strict LF-space has nuclear stages. By Remark C.1.4.7 nuclearity of the limit follows
from any one strict presentation by nuclear Fréchet stages. -/
theorem isNuclearTVS_strictLF_stage
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hE : IsNuclearTVS.{v} E) (n : ℕ) :
    IsNuclearTVS.{v} (X n) := by sorry

/-- Paper: Corollary C.1.5.13, p. 668. If a strict countable limit of nuclear
Fréchet spaces has a quotient of the same kind by a closed subspace, the quotient
map lifts bounded sets. The kernel is a limit subspace and itself a nuclear strict LF-space.
Deviation: For the quotient, strict LF plus nuclearity expresses the nuclear stage
condition by Remarks C.1.4.7 and C.1.5.12. -/
theorem liftsBoundedSets_quotient_of_nuclear_strictLF
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hNuclear : ∀ n, IsNuclearTVS.{v} (X n))
    (F : Submodule ℂ E) (hF : IsClosed (F : Set E))
    (hQ : IsStrictLFSpace (E ⧸ F)) (hNuclearQ : IsNuclearTVS.{v} (E ⧸ F)) :
    LiftsBoundedSets F.mkQL ∧ IsLimitSubspace i F ∧ IsStrictLFSpace F ∧ IsNuclearTVS.{v} F := by sorry

end Deferred

end RiemannMasullo
