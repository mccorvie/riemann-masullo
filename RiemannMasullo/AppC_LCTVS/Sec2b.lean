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
    ‖(x : LocalBanach p)‖ = p x := by sorry

/-- Paper: Theorem C.2.4.2(2), p. 686. When the target seminorm is dominated by the
source seminorm, the linear identity extends to a map of the two local Banach spaces. -/
def localBanachMap (p q : Seminorm ℂ E) (h : q ≤ p) : LocalBanach p →L[ℂ] LocalBanach q :=
  let f : WithLocalSeminorm p →ₗ[ℂ] WithLocalSeminorm q := LinearMap.id
  (f.mkContinuousOfExistsBound ⟨1, fun x ↦ (h x).trans_eq (one_mul (p x)).symm⟩).completion

/-- Paper: Theorem C.2.4.2(2), p. 686. The comparison of local Banach spaces sends
the canonical image of each vector to its canonical image for the smaller seminorm. -/
theorem localBanachMap_coe (p q : Seminorm ℂ E) (h : q ≤ p) (x : WithLocalSeminorm p) :
    localBanachMap p q h x = ((show WithLocalSeminorm q from x) : LocalBanach q) := by sorry

end LocalBanach

section Characterizations

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

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
              ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T x) := by sorry

/-- Paper: Theorem C.2.4.2(3), p. 686. Nuclearity can be tested on the completed
projective to injective comparison against Banach spaces. -/
theorem isNuclearTVS_iff_completedTensor_banach :
    IsNuclearTVS.{v, u} E ↔
      ∀ (F : Type (max v u)) (_ : NormedAddCommGroup F) (_ : NormedSpace ℂ F) (_ : CompleteSpace F),
        IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) := by sorry

/-- Paper: Theorem C.2.4.2(4), p. 686. Nuclearity is equivalent to the canonical
comparison on completed tensors being a homeomorphism against all Hausdorff locally
convex spaces. -/
theorem isNuclearTVS_iff_completedTensor :
    IsNuclearTVS.{v, u} E ↔
      ∀ (F : Type (max v u)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
        (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) := by sorry

end Characterizations

-- Remark C.2.4.3 (p. 686) records other authors' notation for the local Banach space.

section WeakDual

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.2.4.4, p. 687. The local Banach space at a balanced convex
zero-neighborhood in the weak dual is finite-dimensional. -/
theorem finiteDimensional_weakDual_localBanach (U : Set (WeakDual ℂ E)) (hU : U ∈ 𝓝 0)
    (hb : Balanced ℂ U) (hc : Convex ℝ U) :
    FiniteDimensional ℂ (LocalBanach (gaugeSeminorm hb hc (absorbent_nhds_zero hU))) := by sorry

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
    WithSeminorms (E := FinestLocallyConvex E) (id : Seminorm ℂ E → Seminorm ℂ E) := by sorry

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
        FiniteDimensional ℂ S ∧ B ⊆ S ∧ IsVonNBounded ℂ ((Subtype.val : S → _) ⁻¹' B) := by sorry

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
