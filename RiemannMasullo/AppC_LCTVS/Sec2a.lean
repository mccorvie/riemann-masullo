module

public import RiemannMasullo.AppC_LCTVS.Sec1
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.Algebra.Module.UniformConvergence
import Mathlib.Topology.Baire.CompleteMetrizable
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.BanachSteinhaus
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Mapping spaces and topologies of a duality

Masullo, Appendix C, §§C.2.1–C.2.2. The family `S` specifies which sets are used to test
uniform convergence. We use Mathlib's `UniformOnFun` for functions, `UniformConvergenceCLM`
for continuous linear maps, and `WeakBilin` and `LinearMap.polar` for a bilinear pairing.
As in §C.1, `PolynormableSpace ℂ` expresses local convexity of the complex vector topology.
-/

@[expose] public noncomputable section

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise

namespace RiemannMasullo

section Functions

variable {X F : Type*} [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
variable (S : Set (Set X)) (hne : S.Nonempty) (hdir : DirectedOn (· ⊆ ·) S)

include hne hdir in
/-- Paper: (C.2.1.1)–(C.2.1.2), p. 670. A basic zero-neighborhood consists of the functions
that map one member of the directed family into a basic zero-neighborhood in the target. -/
theorem uniformOnFun_zero_basis {ι : Type*} {p : ι → Prop} {V : ι → Set F}
    (hV : (𝓝 0).HasBasis p V) :
    (𝓝 (0 : X →ᵤ[S] F)).HasBasis (fun a : Set X × ι ↦ a.1 ∈ S ∧ p a.2)
      (fun a ↦ {f | MapsTo (UniformOnFun.toFun S f) a.1 (V a.2)}) := by
  exact UniformOnFun.hasBasis_nhds_zero_of_basis S hne hdir hV

-- TODO(paper-gap): Uniqueness on p. 670 needs translations by all functions in F^X.
-- Invariance under just the constant translations by F does not determine the topology.

include hne hdir in
/-- Paper: §C.2.1, p. 670. Passing to a cofinal subfamily leaves the topology of
uniform convergence unchanged. -/
theorem uniformOnFun_topology_eq_of_cofinal (S' : Set (Set X)) (hsub : S' ⊆ S)
    (hcof : ∀ T ∈ S, ∃ T' ∈ S', T ⊆ T') :
    UniformOnFun.topologicalSpace X F S' = UniformOnFun.topologicalSpace X F S := by
  apply le_antisymm
  · apply continuous_id_iff_le.mp
    exact (UniformOnFun.uniformContinuous_ofFun_toFun F S S' fun T hT ↦ by
      obtain ⟨T', hT', hTT'⟩ := hcof T hT
      exact ⟨{T'}, singleton_subset_iff.mpr hT', finite_singleton T', by simpa using hTT'⟩).continuous
  · exact continuous_id_iff_le.mp
      (UniformOnFun.uniformContinuous_ofFun_toFun_of_subset F S' S hsub).continuous

include hne hdir in
/-- Paper: §C.2.1, p. 670. The induced topology makes a subspace a topological vector
space precisely when every member maps each test set into a bounded subset of F.
Addition is already continuous for the induced additive uniformity. -/
theorem uniformOnFun_submodule_continuousSMul_iff [ContinuousSMul ℂ F]
    (L : Submodule ℂ (X →ᵤ[S] F)) :
    ContinuousSMul ℂ L ↔ ∀ f ∈ L, ∀ T ∈ S, IsVonNBounded ℂ (UniformOnFun.toFun S f '' T) := by
  refine ⟨?_, UniformOnFun.continuousSMul_submodule_of_image_bounded ℂ X F L⟩
  intro hL f hf T hT V hV
  have hTV : {g : X →ᵤ[S] F | MapsTo (UniformOnFun.toFun S g) T V} ∈ 𝓝 0 :=
    (uniformOnFun_zero_basis S hne hdir (𝓝 (0 : F)).basis_sets).mem_of_mem (i := (T, V))
      ⟨hT, hV⟩
  have hsmul : Tendsto (fun c : ℂ ↦ ((c • (⟨f, hf⟩ : L) : L) : X →ᵤ[S] F)) (𝓝 0) (𝓝 0) :=
    (continuous_subtype_val.comp (continuous_id.smul continuous_const)).tendsto' _ _ (by simp)
  apply (absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV)).2
  filter_upwards [hsmul.eventually_mem hTV] with c hc
  rintro _ ⟨x, hx, rfl⟩
  exact hc hx

variable [TopologicalSpace X] [PolynormableSpace ℂ F] [T2Space F]
variable (L : Submodule ℂ (X →ᵤ[S] F)) (hdense : Dense (⋃₀ S))
variable (hc : ∀ f ∈ L, Continuous (UniformOnFun.toFun S f))
variable (hb : ∀ f ∈ L, ∀ T ∈ S, IsVonNBounded ℂ (UniformOnFun.toFun S f '' T))

include hne hdir hdense hc hb in
/-- Paper: Lemma C.2.1.1, p. 670. Uniform convergence on the given sets separates the
continuous functions in the subspace when the union is dense. -/
theorem uniformOnFun_submodule_t2 : T2Space L := by
  -- Restriction to the dense union is injective on continuous functions.
  let restrict : L → (⋃₀ S → F) := fun f ↦ (⋃₀ S).domRestrict (UniformOnFun.toFun S f)
  apply T2Space.of_injective_continuous (f := restrict)
  · intro f g hfg
    apply Subtype.ext
    refine Continuous.ext_on hdense (hc f f.property) (hc g g.property) ?_
    intro x hx
    exact congrFun hfg ⟨x, hx⟩
  · exact UniformOnFun.uniformContinuous_restrict_toFun.continuous.comp continuous_subtype_val

open scoped ComplexOrder in
include hne hdir hdense hc hb in
/-- Paper: Lemma C.2.1.1, p. 670. The induced topology on the subspace is a locally convex
vector topology when each of its functions has bounded image on each test set. -/
theorem uniformOnFun_submodule_polynormable : PolynormableSpace ℂ L := by
  let : Module ℝ F := Module.restrictScalars ℝ ℂ F
  let : IsScalarTower ℝ ℂ F := IsScalarTower.restrictScalars ℝ ℂ F
  let : Module ℝ L := Module.restrictScalars ℝ ℂ L
  let : IsScalarTower ℝ ℂ L := IsScalarTower.restrictScalars ℝ ℂ L
  have : ContinuousSMul ℂ L := UniformOnFun.continuousSMul_submodule_of_image_bounded ℂ X F L hb
  have hRealSMul : ContinuousSMul ℝ L := IsScalarTower.continuousSMul ℂ
  have : LocallyConvexSpace ℝ F := (PolynormableSpace.withSeminorms ℂ F).toLocallyConvexSpace
  have : LocallyConvexSpace ℂ L := by
    have hBasis := (uniformOnFun_zero_basis S hne hdir
      (LocallyConvexSpace.convex_basis_zero ℝ F)).comap (Subtype.val : L → X →ᵤ[S] F)
    have hZero : 𝓝 (0 : L) = comap (Subtype.val : L → X →ᵤ[S] F) (𝓝 0) := by
      rw [nhds_subtype]
      rfl
    rw [← hZero] at hBasis
    refine LocallyConvexSpace.ofBasisZero ℂ L _ _ hBasis ?_
    rintro ⟨T, V⟩ ⟨_, _, hV⟩
    apply convex_of_nonneg_surjective_algebraMap ℂ
      (fun z hz ↦ RCLike.nonneg_iff_exists_ofReal.mp (show 0 ≤ z from hz))
    intro f hf g hg a b ha hb' hab x hx
    exact hV (hf hx) (hg hx) ha hb' hab
  exact @LocallyConvexSpace.toPolynormableSpace ℂ L _ _ _ _ ‹Module ℝ L› _ hRealSMul _ _ _

end Functions

section MappingSpaces

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]
variable (S : Set (Set E)) (hb : ∀ T ∈ S, IsVonNBounded ℂ T)
  (hdense : Dense (Submodule.span ℂ (⋃₀ S) : Set E))

include hb hdense in
/-- Paper: Lemma C.2.1.2, p. 671. The topology of uniform convergence on bounded sets from
the given family is Hausdorff if their union spans a dense subspace. -/
theorem uniformConvergenceCLM_t2_of_dense_span : T2Space (E →Lᵤ[ℂ, S] F) := by
  let restrict : (E →Lᵤ[ℂ, S] F) → (⋃₀ S → F) := fun f ↦ (⋃₀ S).domRestrict f
  apply T2Space.of_injective_continuous (f := restrict)
  · intro f g hfg
    exact ContinuousLinearMap.ext_on hdense fun x hx ↦ congrFun hfg ⟨x, hx⟩
  · exact UniformOnFun.uniformContinuous_restrict_toFun.continuous.comp
      (UniformConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) F S).continuous

include hb hdense in
/-- Paper: Lemma C.2.1.2, p. 671. The same family gives a locally convex vector topology on
continuous linear maps into a Hausdorff locally convex target. -/
theorem uniformConvergenceCLM_polynormable : PolynormableSpace ℂ (E →Lᵤ[ℂ, S] F) := by sorry

/-- Paper: (C.2.1.4), p. 671. Take the supremum of a continuous target seminorm after
evaluation at each point of a bounded test set. -/
def mappingSeminorm (T : {T : Set E // IsVonNBounded ℂ T})
    (p : {p : Seminorm ℂ F // Continuous p}) : Seminorm ℂ (E →L[ℂ] F) :=
  ⨆ x : T.val, p.val.comp ((ContinuousLinearMap.coeLM ℂ (R := ℂ) (M := E) (N₃ := F)).flip (x : E))

/-- Paper: (C.2.1.4), p. 671. The value of the mapping seminorm at f is the supremum of
p(f(x)) on the test set. -/
theorem mappingSeminorm_apply (T : {T : Set E // IsVonNBounded ℂ T})
    (p : {p : Seminorm ℂ F // Continuous p}) (f : E →L[ℂ] F) :
    mappingSeminorm T p f = ⨆ x : T.val, p.val (f x) := by
  unfold mappingSeminorm
  apply Seminorm.iSup_apply
  apply Seminorm.bddAbove_range_iff.mpr
  intro g
  obtain ⟨r, _, hr⟩ :=
    ((PolynormableSpace.withSeminorms ℂ F).image_isVonNBounded_iff_seminorm_bounded g).mp
      (T.2.image g) p
  exact ⟨r, forall_mem_range.mpr fun x ↦ (hr x x.2).le⟩

include hb hdense in
/-- Paper: (C.2.1.4), p. 671. The seminorms indexed by test sets and generating target
seminorms generate the topology of uniform convergence on S. -/
theorem uniformConvergenceCLM_withSeminorms {ι : Type*} (p : SeminormFamily ℂ F ι)
    (hp : WithSeminorms p) :
    WithSeminorms (E := E →Lᵤ[ℂ, S] F) (fun a : S × ι ↦
      mappingSeminorm ⟨a.1.val, hb _ a.1.property⟩ ⟨p a.2, hp.continuous_seminorm a.2⟩) := by
  let q : SeminormFamily ℂ (E →Lᵤ[ℂ, S] F) (S × ι) := fun a ↦
    mappingSeminorm ⟨a.1.val, hb _ a.1.property⟩ ⟨p a.2, hp.continuous_seminorm a.2⟩
  have hq (a : S × ι) (f : E →Lᵤ[ℂ, S] F) :
      q a f = ⨆ x : a.1.val, p a.2 (f x) :=
    mappingSeminorm_apply _ _ f
  change WithSeminorms q
  rw [q.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · rw [((Metric.nhds_basis_ball (x := (0 : ℝ))).comap (q a)).ge_iff]
    intro r hr
    rw [← (q a).ball_zero_eq_preimage_ball]
    -- A smaller ball leaves room for the supremum to attain its upper bound.
    have hball : (p a.2).ball 0 (r / 2) ∈ 𝓝 0 :=
      Seminorm.ball_mem_nhds (hp.continuous_seminorm a.2) (half_pos hr)
    filter_upwards [UniformConvergenceCLM.eventually_nhds_zero_mapsTo
      (RingHom.id ℂ) a.1.property hball] with f hf
    apply (q a).mem_ball_zero.mpr
    rw [hq]
    exact (Real.iSup_le (fun x ↦ ((p a.2).mem_ball_zero.mp (hf x.2)).le)
      (half_pos hr).le).trans_lt (half_lt_self hr)
  · rw [UniformConvergenceCLM.nhds_zero_eq_of_basis (RingHom.id ℂ) F S hp.hasBasis_zero_ball]
    simp only [le_iInf_iff, le_principal_iff]
    intro T hT ir hr
    have hball (i : ι) : (q (⟨T, hT⟩, i)).ball 0 ir.2 ∈ ⨅ a, comap (q a) (𝓝 0) := by
      rw [(q (⟨T, hT⟩, i)).ball_zero_eq_preimage_ball]
      apply mem_iInf_of_mem (f := fun a ↦ comap (q a) (𝓝 (0 : ℝ))) (⟨T, hT⟩, i)
      exact preimage_mem_comap (Metric.ball_mem_nhds (0 : ℝ) hr)
    have hFin : (⋂ i ∈ ir.1, (q (⟨T, hT⟩, i)).ball 0 ir.2) ∈
        ⨅ a, comap (q a) (𝓝 0) := ir.1.iInter_mem_sets.mpr fun i _ ↦ hball i
    refine mem_of_superset hFin ?_
    intro f hf x hx
    apply (ir.1.sup p).mem_ball_zero.mpr
    apply Seminorm.finset_sup_apply_lt hr
    intro i hi
    obtain ⟨r, _, hbound⟩ :=
      (hp.image_isVonNBounded_iff_seminorm_bounded f).mp ((hb T hT).image f) i
    have hxle : p i (f x) ≤ q (⟨T, hT⟩, i) f := by
      rw [hq]
      exact le_ciSup (f := fun y : T ↦ p i (f y))
        ⟨r, forall_mem_range.mpr fun y ↦ (hbound y y.2).le⟩ ⟨x, hx⟩
    exact hxle.trans_lt ((q (⟨T, hT⟩, i)).mem_ball_zero.mp (mem_iInter₂.mp hf i hi))

-- Example C.2.1.3 (p. 671) comments on the prevalence of these topologies.

/-- Paper: Definition C.2.1.4, p. 671. The S-dual is the continuous dual with uniform
convergence on S.
Deviation: The type alias also makes sense outside the paper's directed families of
bounded sets with dense linear span. -/
abbrev SDual (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (S : Set (Set E)) := E →Lᵤ[ℂ, S] ℂ

/-- Paper: Definition C.2.1.4, p. 671. Testing on finite subsets gives the weak dual topology. -/
theorem sDual_finite_eq_weak :
    (inferInstance : TopologicalSpace (SDual E {T | T.Finite})) =
      (inferInstance : TopologicalSpace (WeakDual ℂ E)) := by
  have h := (PointwiseConvergenceCLM.equivWeakDual ℂ E).toHomeomorph.isInducing.eq_induced
  exact h.trans (@induced_id (WeakDual ℂ E) inferInstance)

/-- Paper: Definition C.2.1.4, p. 671. Testing on all von Neumann bounded sets gives the
strong dual topology. -/
theorem sDual_bounded_eq_strong :
    (inferInstance : TopologicalSpace (SDual E {T | IsVonNBounded ℂ T})) =
      (inferInstance : TopologicalSpace (StrongDual ℂ E)) := rfl

-- The convex-closure identity recalled on p. 671 is Mathlib's `Convex.toWeakSpace_closure`.

/-- Paper: Definition C.2.1.5, p. 671. In the S-topology on continuous linear maps, a
zero-neighborhood basis tests images of members of S against zero-neighborhoods in F.
The three choices in the definition are finite, precompact, and von Neumann bounded sets. -/
theorem uniformConvergenceCLM_zero_basis (hne : S.Nonempty) (hdir : DirectedOn (· ⊆ ·) S) :
    (𝓝 (0 : E →Lᵤ[ℂ, S] F)).HasBasis
      (fun a : Set E × Set F ↦ a.1 ∈ S ∧ a.2 ∈ 𝓝 0)
      (fun a ↦ {f | MapsTo f a.1 a.2}) :=
  UniformConvergenceCLM.hasBasis_nhds_zero (RingHom.id ℂ) F S hne hdir

/-- Paper: Definition C.2.1.5(2), p. 671. The γ-topology on continuous linear maps tests
uniform convergence on all subsets with compact closure in the completion of the source.
For scalar-valued maps this gives the γ-dual of Definition C.2.1.4. -/
abbrev PrecompactConvergenceCLM (E F : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :=
  E →Lᵤ[ℂ, {T | IsPrecompactInCompletion T}] F

/-- Paper: Definition C.2.1.5(2), p. 671. For a complete Hausdorff source, precompact
convergence agrees with uniform convergence on compact sets. -/
theorem precompactConvergenceCLM_eq_compact [CompleteSpace E] :
    (inferInstance : TopologicalSpace (PrecompactConvergenceCLM E F)) =
      (inferInstance : TopologicalSpace (E →Lᵤ[ℂ, {T | IsCompact T}] F)) := by
  let precompact : Set (Set E) := {T | IsPrecompactInCompletion T}
  let compact : Set (Set E) := {T | IsCompact T}
  have hpre (T : Set E) : T ∈ precompact ↔ TotallyBounded T :=
    isPrecompactInCompletion_iff_totallyBounded T
  have hne : precompact.Nonempty := ⟨∅, (hpre ∅).2 totallyBounded_empty⟩
  have hdir : DirectedOn (· ⊆ ·) precompact :=
    directedOn_of_sup_mem fun A B hA hB ↦
      (hpre (A ∪ B)).2 (TotallyBounded.union ((hpre A).1 hA) ((hpre B).1 hB))
  have hsub : compact ⊆ precompact := fun T hT ↦
    (hpre T).2 (show IsCompact T from hT).totallyBounded
  have hcof : ∀ T ∈ precompact, ∃ K ∈ compact, T ⊆ K := by
    intro T hT
    have hclosure : TotallyBounded (closure T) := totallyBounded_closure.2 ((hpre T).1 hT)
    exact ⟨closure T, hclosure.isCompact_of_isClosed isClosed_closure, subset_closure⟩
  have h := uniformOnFun_topology_eq_of_cofinal (F := F) precompact hne hdir compact hsub hcof
  change UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F precompact =
    UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F compact
  rw [UniformConvergenceCLM.topologicalSpace_eq, UniformConvergenceCLM.topologicalSpace_eq]
  exact congrArg (TopologicalSpace.induced (fun f : E →L[ℂ] F ↦ (f : E → F))) h.symm

end MappingSpaces

section OperatorNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Paper: Remark C.2.1.6, p. 671. The operator norm is the supremum of the image norms
over the closed unit ball of the source. -/
theorem opNorm_eq_sup_closedUnitBall (f : E →L[ℂ] F) :
    ‖f‖ = ⨆ x : Metric.closedBall (0 : E) 1, ‖f x‖ := by
  rw [← f.sSup_unitClosedBall_eq_norm, sSup_image']

/-- Paper: Remark C.2.1.6, p. 671. The operator-norm balls form a zero-neighborhood basis
for uniform convergence on all bounded subsets of a normed space. -/
theorem boundedConvergenceCLM_opNorm_basis :
    let S := {T : Set E | IsVonNBounded ℂ T}
    (𝓝 (0 : E →Lᵤ[ℂ, S] F)).HasBasis (fun r : ℝ ↦ 0 < r)
      (fun r ↦ {f | ‖(UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S).symm f‖ < r}) := by
  -- Mathlib equips ordinary continuous linear maps with the bounded-convergence topology.
  change (𝓝 (0 : E →L[ℂ] F)).HasBasis (fun r : ℝ ↦ 0 < r) (fun r ↦ {f | ‖f‖ < r})
  exact NormedAddGroup.nhds_zero_basis_norm_lt

end OperatorNorm

section Equicontinuity

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: Remark C.2.1.6, p. 671. Composing each generating seminorm of F with each
single-point evaluation generates the pointwise topology on continuous linear maps. -/
theorem pointwiseConvergenceCLM_withSeminorms {ι : Type*} (p : SeminormFamily ℂ F ι)
    (hp : WithSeminorms p) :
    WithSeminorms (fun a : E × ι ↦ (p a.2).comp
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) F a.1).toLinearMap) := by
  let coeToPi := LinearMap.pi fun x : E ↦
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) F x).toLinearMap
  have hcoe : IsInducing coeToPi :=
    (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) E F).isInducing
  have hpi := withSeminorms_pi fun _ : E ↦ hp
  exact (hcoe.withSeminorms hpi).congr_equiv (Equiv.sigmaEquivProd E ι).symm

/-- Paper: §C.2.1, p. 672. For a quasi-complete source, a pointwise bounded family of
operators is bounded for uniform convergence on each member of a directed bounded cover. -/
theorem uniformConvergenceCLM_bounded_of_pointwise [QuasiCompleteSpace ℂ E]
    (S : Set (Set E)) (hdir : DirectedOn (· ⊆ ·) S) (hcover : ⋃₀ S = univ)
    (hb : ∀ T ∈ S, IsVonNBounded ℂ T) (H : Set (E →L[ℂ] F))
    (hH : IsVonNBounded ℂ ((UniformConvergenceCLM.ofFun (RingHom.id ℂ) F {T | T.Finite}) '' H)) :
    IsVonNBounded ℂ ((UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S) '' H) := by
  have hpoint (x : E) : IsVonNBounded ℂ (range fun f : H ↦ f.val x) := by
    have hx := UniformConvergenceCLM.isVonNBounded_image2_apply hH
      (show {x} ∈ {T : Set E | T.Finite} from finite_singleton x)
    apply hx.subset
    rintro _ ⟨f, rfl⟩
    exact mem_image2_of_mem (mem_image_of_mem _ f.property) (mem_singleton x)
  have hS : S.Nonempty := by
    have hz : (0 : E) ∈ ⋃₀ S := hcover.symm ▸ mem_univ _
    obtain ⟨T, hT, _⟩ := mem_sUnion.mp hz
    exact ⟨T, hT⟩
  apply (uniformConvergenceCLM_zero_basis S hS hdir).isVonNBounded_iff.mpr
  rintro ⟨T, V⟩ ⟨hT, hV⟩
  have h := isVonNBounded_image2_apply_of_pointwise (fun f : H ↦ f.val) hpoint (hb T hT)
  filter_upwards [h hV, eventually_ne_cobounded (0 : ℂ)] with c hc hc₀
  rintro _ ⟨f, hf, rfl⟩
  rw [mem_smul_set_iff_inv_smul_mem₀ hc₀]
  intro x hx
  have hf' : f ∈ range (fun f : H ↦ f.val) := ⟨⟨f, hf⟩, rfl⟩
  exact (mem_smul_set_iff_inv_smul_mem₀ hc₀ V (f x)).mp (hc (mem_image2_of_mem hf' hx))

-- Retain the existing hypotheses. The argument works for any cover of a barrelled source.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Lemma C.2.1.7, p. 672. For a barrelled source and quasi-complete target, uniform
convergence on a directed cover by bounded subsets gives a quasi-complete mapping space. -/
theorem uniformConvergenceCLM_quasiComplete [BarrelledSpace ℂ E] [QuasiCompleteSpace ℂ F]
    (S : Set (Set E)) (hdir : DirectedOn (· ⊆ ·) S) (hcover : ⋃₀ S = univ)
    (hb : ∀ T ∈ S, IsVonNBounded ℂ T) : QuasiCompleteSpace ℂ (E →Lᵤ[ℂ, S] F) := by
  refine ⟨fun {A} hA hAc ↦ completeSpace_coe_iff_isComplete.mp ⟨fun {l} hl ↦ ?_⟩⟩
  have := hl.1
  let g : A → E →L[ℂ] F := fun a ↦ (UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S).symm a.val
  have hind := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) F S
  have heval (x : E) : UniformContinuous (fun f : E →Lᵤ[ℂ, S] F ↦ f x) :=
    (UniformOnFun.uniformContinuous_eval hcover x).comp hind.uniformContinuous
  have hbounded (x : E) : IsVonNBounded ℂ (range fun a : A ↦ g a x) := by
    let ev : (E →Lᵤ[ℂ, S] F) →L[ℂ] F :=
      ⟨{ toFun := fun f ↦ f x
         map_add' := fun _ _ ↦ rfl
         map_smul' := fun _ _ ↦ rfl }, (heval x).continuous⟩
    change IsVonNBounded ℂ (range (ev ∘ (Subtype.val : A → _)))
    rw [range_comp, Subtype.range_coe]
    exact hA.image ev
  -- Quasi-completeness of the target gives a limit at each point.
  have hlimit (x : E) : ∃ y, Tendsto (fun a : A ↦ g a x) l (𝓝 y) := by
    let gx : A → F := fun a ↦ g a x
    have hc : Cauchy (l.map gx) := hl.map ((heval x).comp uniformContinuous_subtype_val)
    have hmem : l.map gx ≤ 𝓟 (closure (range gx)) := by
      rw [le_principal_iff, mem_map]
      exact Eventually.of_forall fun a ↦ subset_closure (mem_range_self a)
    obtain ⟨y, _, hy⟩ := QuasiCompleteSpace.quasiComplete (hbounded x).closure isClosed_closure
      _ hc hmem
    exact ⟨y, hy⟩
  choose f hf using hlimit
  have hpoint : Tendsto (fun a x ↦ g a x) l (𝓝 f) := tendsto_pi_nhds.mpr hf
  -- Banach–Steinhaus makes the pointwise limit continuous.
  let G : E →L[ℂ] F := ⟨linearMapOfTendsto f (fun a ↦ (g a).toLinearMap) hpoint,
    hpoint.continuous_of_equicontinuous (PolynormableSpace.banach_steinhaus hbounded).equicontinuous⟩
  let G' := UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S G
  have hG : Tendsto (Subtype.val : A → E →Lᵤ[ℂ, S] F) l (𝓝 G') := by
    apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn _ _ S).mpr
    intro T hT
    have hc := hl.map (hind.uniformContinuous.comp uniformContinuous_subtype_val)
    have hu : UniformCauchySeqOn (fun a x ↦ g a x) l T := fun U hU ↦
      cauchy_map_iff'.mp hc (UniformOnFun.gen_mem_uniformity F S hT hU)
    exact hu.tendstoUniformlyOn_of_tendsto fun x _ ↦ hf x
  have hGA := hAc.mem_of_tendsto hG (Eventually.of_forall Subtype.property)
  exact ⟨⟨G', hGA⟩, tendsto_subtype_rng.mpr hG⟩

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Remark C.2.1.8, p. 672. The strong operator topology on the bounded operators
of any Hilbert space is quasi-complete. -/
theorem hilbert_pointwiseOperators_quasiComplete : QuasiCompleteSpace ℂ (H →Lₚₜ[ℂ] H) := by
  constructor
  intro s hs hclosed
  -- Uniform boundedness turns the bounds on evaluations into an operator-norm bound.
  have hnorm : Bornology.IsBounded (α := H →L[ℂ] H) s := by
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun f : s ↦ (f.val : H →L[ℂ] H)) fun x ↦ by
      let ev := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H x
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp ((NormedSpace.isVonNBounded_iff ℂ).mp
        (hs.image ev))
      exact ⟨M, fun f ↦ hM (ev f.val) (mem_image_of_mem ev f.property)⟩
    exact isBounded_iff_forall_norm_le.mpr ⟨C, fun f hf ↦ hC ⟨f, hf⟩⟩
  -- The image is closed in the complete product of copies of H.
  have hcoe := PointwiseConvergenceCLM.isUniformEmbedding_coeFn (RingHom.id ℂ) H H
  apply hcoe.isUniformInducing.isComplete_iff.mp
  apply IsClosed.isComplete
  apply ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hnorm
  rw [hcoe.isEmbedding.isInducing.eq_induced] at hclosed
  exact isClosed_induced_iff'.mp hclosed

-- The operator-norm completeness and quasi-completeness in Remark C.2.1.8 are already
-- stated in §C.1 as the last two conclusions of `hilbert_quasiComplete_examples`.

/-- Paper: Remark C.2.1.8, p. 672. Every complex Fréchet space is barrelled. -/
theorem isFrechetTVS_barrelled {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsFrechetTVS X) : BarrelledSpace ℂ X := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hcomplete
  have : (uniformity X).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero X]
    infer_instance
  have : BaireSpace X := BaireSpace.of_completelyPseudoMetrizable
  exact BaireSpace.instBarrelledSpace

variable (A : Set (E →L[ℂ] F))
  (heq : EquicontinuousAt (fun f : A ↦ (f.val : E → F)) 0)

/-- Paper: §C.2.1, p. 672. Equicontinuity at zero means there is one source
zero-neighborhood that every map sends into the prescribed target zero-neighborhood. -/
theorem equicontinuousAt_zero_iff_mapsTo :
    EquicontinuousAt (fun f : A ↦ (f.val : E → F)) 0 ↔
      ∀ V ∈ 𝓝 (0 : F), ∃ U ∈ 𝓝 (0 : E), ∀ f ∈ A, MapsTo f U V := by
  have hb : (uniformity F).HasBasis (fun V : Set F ↦ V ∈ 𝓝 (0 : F))
      (fun V ↦ (fun x : F × F ↦ x.2 - x.1) ⁻¹' V) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact (𝓝 (0 : F)).basis_sets.comap _
  rw [hb.equicontinuousAt_iff_right]
  refine forall₂_congr fun V _ ↦ ?_
  simp only [mem_preimage, map_zero, sub_zero, Filter.eventually_iff_exists_mem]
  constructor
  · rintro ⟨U, hU, h⟩
    exact ⟨U, hU, fun f hf x hx ↦ h x hx ⟨f, hf⟩⟩
  · rintro ⟨U, hU, h⟩
    exact ⟨U, hU, fun x hx f ↦ h f f.2 hx⟩

-- Retain the paper's dense-span hypothesis. Boundedness follows test set by test set.
set_option linter.unusedVariables false in
include heq in
/-- Paper: Lemma C.2.1.9(1), p. 672. An equicontinuous set is bounded for uniform
convergence on bounded test sets whose union spans a dense subspace. -/
theorem equicontinuous_isVonNBounded_uniformConvergenceCLM
    (S : Set (Set E)) (hb : ∀ T ∈ S, IsVonNBounded ℂ T)
    (hdense : Dense (Submodule.span ℂ (⋃₀ S) : Set E)) :
    IsVonNBounded ℂ ((UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S) '' A) := by
  apply UniformConvergenceCLM.isVonNBounded_iff.mpr
  intro T hT V hV
  obtain ⟨U, hU, hmaps⟩ := (equicontinuousAt_zero_iff_mapsTo A).mp heq V hV
  apply (absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV)).mpr
  filter_upwards [(hb T hT hU).eventually_nhds_zero (mem_of_mem_nhds hU)] with c hc
  rintro _ ⟨_, ⟨f, hf, rfl⟩, x, hx, rfl⟩
  change c • f x ∈ V
  rw [← map_smul]
  exact hmaps f hf (hc hx)

include heq in
set_option linter.unusedSectionVars false in
/-- Paper: Lemma C.2.1.9(2), p. 672. Pointwise and precompact convergence induce the
same topology on each equicontinuous set of operators. -/
theorem equicontinuous_induced_pointwise_eq_precompact :
    TopologicalSpace.induced (Subtype.val : A → E →L[ℂ] F)
        (inferInstance : TopologicalSpace (E →Lₚₜ[ℂ] F)) =
      TopologicalSpace.induced (Subtype.val : A → E →L[ℂ] F)
        (inferInstance : TopologicalSpace (PrecompactConvergenceCLM E F)) := by
  have hu : UniformEquicontinuous (fun f : A ↦ (f.val : E → F)) :=
    uniformEquicontinuous_of_equicontinuousAt_zero (fun f : A ↦ f.val) heq
  let pointwise : A → E →Lₚₜ[ℂ] F :=
    UniformConvergenceCLM.ofFun (RingHom.id ℂ) F {s | s.Finite} ∘ Subtype.val
  let precompact : A → PrecompactConvergenceCLM E F :=
    UniformConvergenceCLM.ofFun (RingHom.id ℂ) F {s | IsPrecompactInCompletion s} ∘ Subtype.val
  change TopologicalSpace.induced pointwise inferInstance =
    TopologicalSpace.induced precompact inferInstance
  refine TopologicalSpace.ext_nhds fun f ↦ eq_of_forall_le_iff fun l ↦ ?_
  rw [nhds_induced, nhds_induced, ← tendsto_iff_comap, ← tendsto_iff_comap,
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto,
    UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn]
  constructor
  · intro h s hs U hU
    have hs' := (isPrecompactInCompletion_iff_totallyBounded s).1 hs
    obtain ⟨V, hV, hVsymm, hVU⟩ := comp_comp_symm_mem_uniformity_sets hU
    obtain ⟨W, hW, hWV⟩ := (uniformity E).basis_sets.uniformEquicontinuous_iff_left.mp hu V hV
    -- Pointwise convergence controls all the centers of a finite cover at once.
    obtain ⟨t, ht, hcover⟩ := hs' W hW
    have htend : ∀ᶠ g in l, ∀ y ∈ t, (f.val y, g.val y) ∈ V :=
      ht.eventually_all.mpr fun y _ ↦ (Uniform.tendsto_nhds_right.mp (h y)).eventually_mem hV
    filter_upwards [htend] with g hg x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact hVU (SetRel.prodMk_mem_comp (SetRel.prodMk_mem_comp (hWV x y hxy f) (hg y hy))
      (SetRel.symm V (hWV x y hxy g)))
  · intro h x
    exact (h {x} ((isPrecompactInCompletion_iff_totallyBounded {x}).2
      (totallyBounded_singleton x))).tendsto_at (mem_singleton x)

end Equicontinuity

section Bornologies

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: §C.2.2.1, p. 673. A bornology in the paper is a nonempty upward-directed
family of weakly bounded sets in which every nonzero rescaling of a member is contained
in a member. -/
def IsPolarBornology {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (S : Set (Set E)) : Prop :=
  S.Nonempty ∧ DirectedOn (· ⊆ ·) S ∧
    (∀ T ∈ S, IsVonNBounded ℂ (toWeakSpace ℂ E '' T)) ∧
    ∀ T ∈ S, ∀ c : ℂ, c ≠ 0 → ∃ U ∈ S, c • T ⊆ U

/-- Paper: §C.2.2.1, p. 673. The finite subsets form a bornology in the sense of the paper. -/
theorem isPolarBornology_finite : IsPolarBornology {T : Set E | T.Finite} := by
  refine ⟨⟨∅, Set.finite_empty⟩, directedOn_of_sup_mem (fun _ _ ↦ Set.Finite.union), ?_, ?_⟩
  · intro T hT
    exact (Set.Finite.image (toWeakSpace ℂ E) hT).isVonNBounded
  · intro T hT c _
    exact ⟨c • T, Set.Finite.smul_set hT, Subset.rfl⟩

/-- Paper: §C.2.2.1, p. 673. The precompact subsets form a bornology. -/
theorem isPolarBornology_precompact :
    IsPolarBornology {T : Set E | IsPrecompactInCompletion T} := by
  have hprecompact (T : Set E) : IsPrecompactInCompletion T ↔ TotallyBounded T := by
    have hcoe := (UniformSpace.Completion.isUniformEmbedding_coe E).isUniformInducing
    unfold IsPrecompactInCompletion IsRelativelyCompact
    rw [← totallyBounded_image_iff hcoe, ← totallyBounded_closure]
    exact ⟨IsCompact.totallyBounded, fun h ↦ h.isCompact_of_isClosed isClosed_closure⟩
  simp_rw [hprecompact]
  refine ⟨⟨∅, totallyBounded_empty⟩, directedOn_of_sup_mem (fun _ _ ↦ TotallyBounded.union),
    ?_, ?_⟩
  · intro T hT
    exact (TotallyBounded.isVonNBounded ℂ hT).image (toWeakSpaceCLM ℂ E)
  · intro T hT c _
    have hc :=
      (uniformContinuousConstSMul_of_continuousConstSMul ℂ E).uniformContinuous_const_smul c
    exact ⟨c • T, TotallyBounded.image hT hc, Subset.rfl⟩

/-- Paper: §C.2.2.1, p. 673. The von Neumann bounded subsets form a bornology. -/
theorem isPolarBornology_bounded : IsPolarBornology {T : Set E | IsVonNBounded ℂ T} := by
  refine ⟨⟨∅, isVonNBounded_empty ℂ E⟩,
    directedOn_of_sup_mem (fun _ _ ↦ IsVonNBounded.union), ?_, ?_⟩
  · intro T hT
    exact hT.image (toWeakSpaceCLM ℂ E)
  · intro T hT c _
    exact ⟨c • T, hT.image (c • ContinuousLinearMap.id ℂ E), Subset.rfl⟩

/-- Paper: (C.2.2.4), p. 673. A linear functional is continuous precisely when it belongs
to the absolute polar of some member of a given zero-neighborhood basis. -/
theorem continuous_iff_mem_polar_of_basis {ι : Type*} {p : ι → Prop} {U : ι → Set E}
    (hU : (𝓝 0).HasBasis p U) (l : Module.Dual ℂ E) :
    Continuous l ↔ ∃ i, p i ∧ l ∈ (Module.Dual.eval ℂ E).polar (U i) := by
  constructor
  · intro hl
    have h : l ⁻¹' Metric.closedBall 0 1 ∈ 𝓝 (0 : E) :=
      hl.continuousAt.preimage_mem_nhds (by simpa using Metric.closedBall_mem_nhds (0 : ℂ) one_pos)
    obtain ⟨i, hi, hsub⟩ := hU.mem_iff.1 h
    refine ⟨i, hi, (LinearMap.polar_mem_iff _ _ _).2 fun x hx ↦ ?_⟩
    simpa using hsub hx
  · rintro ⟨i, hi, hl⟩
    have hp : Continuous ((normSeminorm ℂ ℂ).comp l) := by
      refine Seminorm.continuous' (r := 1) (Filter.mem_of_superset (hU.mem_of_mem hi) ?_)
      intro x hx
      simpa [Seminorm.mem_closedBall] using (LinearMap.polar_mem_iff _ _ _).1 hl x hx
    refine continuous_of_continuousAt_zero l ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have h := hp.tendsto 0
    rw [map_zero] at h
    exact h

end Bornologies

section Duality

open scoped ComplexOrder

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)

/-- Paper: Theorem C.2.2.1, p. 673. For a separating bilinear pairing the absolute bipolar
of a set is the weak closure of the convex circled hull after adjoining zero. The displayed
formula also applies to the empty set. -/
theorem bipolar_eq_weakClosure_absConvexHull [TopologicalSpace E] [PolynormableSpace ℂ E]
    [T2Space E] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    (hB : B.Nondegenerate) (A : Set E) :
    B.flip.polar (B.polar A) =
      closure (X := WeakBilin B) (absConvexHull ℂ (insert 0 A)) := by
  let C : Set (WeakBilin B) := closure (X := WeakBilin B) (absConvexHull ℂ (insert 0 A))
  have hsub : insert 0 A ⊆ C := subset_absConvexHull.trans (subset_closure (X := WeakBilin B))
  apply Subset.antisymm
  · intro x hx
    by_contra hxC
    let : Module ℝ (WeakBilin B) := Module.restrictScalars ℝ ℂ _
    let : IsScalarTower ℝ ℂ (WeakBilin B) := IsScalarTower.restrictScalars ℝ ℂ _
    let : LocallyConvexSpace ℝ (WeakBilin B) := B.weakBilin_withSeminorms.toLocallyConvexSpace
    have hC : AbsConvex ℂ C := AbsConvex.closure (E := WeakBilin B) absConvex_absConvexHull
    obtain ⟨f, r, hfr, hrx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (E := WeakBilin B) (hC.2.lift ℝ) isClosed_closure hxC
    obtain ⟨y, hy⟩ := (B.rightDualEquiv hB.2).surjective f
    change WeakBilin.eval B y = f at hy
    subst f
    -- Rotate each pairing value on C to the nonnegative real axis.
    have hnorm (z : WeakBilin B) (hz : z ∈ C) : ‖B z y‖ < r := by
      obtain ⟨c, hc, hcz⟩ := RCLike.exists_norm_eq_mul_self (B z y)
      have h := hfr (c • z) (balanced_iff_smul_mem.mp hC.1 hc.le hz)
      rw [map_smul, smul_eq_mul] at h
      change RCLike.re (c * B z y) < r at h
      simpa only [← hcz, RCLike.ofReal_re] using h
    have hr : 0 < r := (norm_nonneg _).trans_lt (hnorm 0 (hsub (mem_insert _ _)))
    have hscale (z : E) : ‖B z ((r : ℂ)⁻¹ • y)‖ = ‖B z y‖ / r := by
      rw [map_smul, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, div_eq_inv_mul]
    have hy' : (r : ℂ)⁻¹ • y ∈ B.polar A := by
      intro z hz
      rw [hscale, div_le_iff₀ hr, one_mul]
      exact (hnorm z (hsub (mem_insert_of_mem _ hz))).le
    have hbound := hx _ hy'
    change ‖B x ((r : ℂ)⁻¹ • y)‖ ≤ 1 at hbound
    rw [hscale, div_le_iff₀ hr, one_mul] at hbound
    change r < (B x y).re at hrx
    exact (hrx.trans_le (Complex.re_le_norm _)).not_ge hbound
  · exact closure_minimal (X := WeakBilin B)
      (absConvexHull_min (insert_subset (B.flip.zero_mem_polar _) (B.subset_bipolar A))
        (LinearMap.polar_AbsConvex _)) (B.flip.polar_isClosed (B.polar A))

/-- Paper: §C.2.2.1, p. 674. A weakly bounded test set defines a seminorm by taking the
supremum of the absolute values of the pairing over that set. -/
def polarSeminorm (A : {A : Set F // IsVonNBounded (E := WeakBilin B.flip) ℂ A}) :
    Seminorm ℂ E :=
  ⨆ y : A.val, (normSeminorm ℂ ℂ).comp (B.flip (y : F))

/-- Paper: §C.2.2.1, p. 674. The closed unit ball of the seminorm of a weakly bounded set
is exactly its absolute polar. -/
theorem polarSeminorm_closedUnitBall
    (A : {A : Set F // IsVonNBounded (E := WeakBilin B.flip) ℂ A}) :
    (polarSeminorm B A).closedBall 0 1 = B.flip.polar A.val := by
  have hbounded : BddAbove (range fun y : A.val ↦ (normSeminorm ℂ ℂ).comp (B.flip (y : F))) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro x
    obtain ⟨r, hr⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).mp
      (A.property.image (WeakBilin.eval B.flip x))
    exact ⟨r, forall_mem_range.mpr fun y ↦ hr (y : F) y.property⟩
  rw [polarSeminorm, Seminorm.closedBall_iSup hbounded 0 one_pos]
  ext x
  simp only [mem_iInter, Seminorm.mem_closedBall_zero, LinearMap.polar_mem_iff,
    Seminorm.comp_apply, coe_normSeminorm]
  exact ⟨fun h y hy ↦ h ⟨y, hy⟩, fun h y ↦ h y y.property⟩

/-- Paper: §C.2.2.1, p. 674. The polar topology on E tests the functions
y ↦ B(x,y) for uniform convergence on the chosen subsets of F. -/
@[instance_reducible]
def polarTopology (S : Set (Set F)) : TopologicalSpace E :=
  TopologicalSpace.induced (fun x ↦ UniformOnFun.ofFun S (fun y ↦ B x y))
    (UniformOnFun.topologicalSpace F ℂ S)

/-- Paper: §C.2.2.1, p. 673. Testing a pairing on finite subsets gives its weak topology. -/
theorem polarTopology_finite_eq_weak :
    polarTopology B {A | A.Finite} = WeakBilin.instTopologicalSpace B := by
  rw [polarTopology, (UniformOnFun.isEmbedding_toFun_finite F ℂ).eq_induced, induced_compose]
  rfl

/-- Paper: §C.2.2.2, p. 674. A topology on E is consistent with the pairing if its
continuous linear functionals are exactly the evaluations against elements of F. -/
def IsConsistentWithDuality (t : TopologicalSpace E) : Prop :=
  ∀ l : Module.Dual ℂ E, @Continuous E ℂ t _ l ↔ l ∈ range B.flip

/-- Paper: §C.2.2.2, p. 674. The weak topology of a separating pairing is consistent. -/
theorem weakTopology_isConsistentWithDuality (hB : B.Nondegenerate) :
    IsConsistentWithDuality B (WeakBilin.instTopologicalSpace B) := by
  intro l
  constructor
  · intro hl
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B
      (⟨l, hl⟩ : StrongDual ℂ (WeakBilin B))
    refine ⟨y, LinearMap.ext fun x ↦ ?_⟩
    exact congrArg (fun φ : StrongDual ℂ (WeakBilin B) ↦ φ x) hy
  · rintro ⟨y, rfl⟩
    exact WeakBilin.eval_continuous B y

/-- Paper: §C.2.2.2, p. 674. The Mackey topology on E is uniform convergence on the
convex circled subsets of F which are compact for the opposite weak topology. -/
@[instance_reducible]
def mackeyTopology : TopologicalSpace E :=
  polarTopology B {A | AbsConvex ℂ A ∧ IsCompact (X := WeakBilin B.flip) A}

/-- For a consistent topology, the elements of the paired space dominated by a continuous
seminorm form a weakly compact set. -/
private theorem isCompact_dualSeminormBall [t : TopologicalSpace E] [PolynormableSpace ℂ E]
    (h : IsConsistentWithDuality B t) (p : Seminorm ℂ E) (hp : Continuous p) :
    IsCompact (X := WeakBilin B.flip) {y | ∀ x, ‖B x y‖ ≤ p x} := by
  let D : Set (E → ℂ) := univ.pi fun x ↦ Metric.closedBall 0 (p x)
  let ev : WeakBilin B.flip → (E → ℂ) := fun y x ↦ B x y
  have hD : IsCompact D := isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  have hev : IsInducing ev := ⟨rfl⟩
  apply hev.isCompact_iff.mpr
  have himage : ev '' {y | ∀ x, ‖B x y‖ ≤ p x} =
      D ∩ range ((↑) : Module.Dual ℂ E → E → ℂ) := by
    ext f
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fun x _ ↦ mem_closedBall_zero_iff.mpr (hy x), ⟨B.flip y, rfl⟩⟩
    · rintro ⟨hf, l, rfl⟩
      have hb (x : E) : ‖l x‖ ≤ p x := mem_closedBall_zero_iff.mp (hf x (mem_univ x))
      have hl : Continuous l := by
        let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
        apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ ℂ) l
        exact fun _ ↦ Seminorm.continuous_of_le hp hb
      obtain ⟨y, rfl⟩ := (h l).mp hl
      exact ⟨y, hb, rfl⟩
  rw [himage]
  exact hD.inter_right (LinearMap.isClosed_range_coe E ℂ (RingHom.id ℂ))

/-- Under a consistent topology, each continuous seminorm is attained by evaluating against
an absolutely convex weakly compact set of the paired space. -/
private theorem exists_mackeyDisk [t : TopologicalSpace E] [PolynormableSpace ℂ E]
    (h : IsConsistentWithDuality B t) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ A : Set F, AbsConvex ℂ A ∧ IsCompact (X := WeakBilin B.flip) A ∧
      ∀ x : E, ∃ y ∈ A, ‖B x y‖ = p x := by
  let A : Set F := {y | ∀ x, ‖B x y‖ ≤ p x}
  refine ⟨A, ?_, isCompact_dualSeminormBall B h p hp, ?_⟩
  · let q (x : E) : Seminorm ℂ F := (normSeminorm ℂ ℂ).comp (B x)
    have hA : A = ⋂ x, (q x).closedBall 0 (p x) := by
      ext y
      simp [A, q]
    rw [hA]
    exact ⟨balanced_iInter fun x ↦ (q x).balanced_closedBall_zero (p x),
      convex_iInter fun x ↦ convex_RCLike_iff_convex_real.mpr ((q x).convex_closedBall 0 (p x))⟩
  · intro x
    obtain ⟨φ, hφ, hφx⟩ := exists_dual_norm_eq_seminorm p hp x
    obtain ⟨y, hy⟩ := (h φ.toLinearMap).mp φ.continuous
    refine ⟨y, fun z ↦ ?_, ?_⟩
    · rw [← LinearMap.flip_apply B, hy]
      exact hφ z
    · rw [← LinearMap.flip_apply B, hy]
      exact hφx

/-- Every Mackey-continuous linear functional is an evaluation against the paired space. -/
private theorem mem_range_flip_of_mackeyContinuous (l : Module.Dual ℂ E)
    (hl : @Continuous _ _ (mackeyTopology B) _ l) : l ∈ range B.flip := by
  let K : Set (Set F) := {A | AbsConvex ℂ A ∧ IsCompact (X := WeakBilin B.flip) A}
  have hzero : ({0} : Set F) ∈ K :=
    ⟨⟨balanced_zero, convex_singleton _⟩, isCompact_singleton⟩
  have hdir : DirectedOn (· ⊆ ·) K := by
    intro A hA D hD
    rcases A.eq_empty_or_nonempty with rfl | hAn
    · exact ⟨D, hD, empty_subset _, Subset.rfl⟩
    rcases D.eq_empty_or_nonempty with rfl | hDn
    · exact ⟨A, hA, Subset.rfl, empty_subset _⟩
    refine ⟨A + D, ⟨⟨hA.1.1.add hD.1.1, hA.1.2.add hD.1.2⟩, hA.2.add hD.2⟩, ?_, ?_⟩
    · intro y hy
      simpa only [add_zero] using add_mem_add hy (hD.1.1.zero_mem hDn)
    · intro y hy
      simpa only [zero_add] using add_mem_add (hA.1.1.zero_mem hAn) hy
  let : TopologicalSpace E := mackeyTopology B
  let ev (x : E) := UniformOnFun.ofFun K (B x)
  have hn : {x : E | ‖l x‖ < 1} ∈ 𝓝 0 := by
    simpa only [map_zero, Metric.ball, dist_zero_right, Set.preimage_ofPred_eq] using
      hl.continuousAt (x := 0).preimage_mem_nhds (Metric.ball_mem_nhds (l 0) one_pos)
  change _ ∈ @nhds _ (TopologicalSpace.induced ev inferInstance) 0 at hn
  rw [nhds_induced] at hn
  obtain ⟨⟨A, ε⟩, ⟨hA, hε⟩, hbound⟩ :=
    ((UniformOnFun.hasBasis_nhds_of_basis F ℂ K (ev 0) ⟨{0}, hzero⟩ hdir
      Metric.uniformity_basis_dist).comap ev).mem_iff.mp hn
  obtain ⟨D, hD, hAD, h0D⟩ := hdir A hA {0} hzero
  let P := (Module.Dual.eval ℂ E).flip
  let j := B.flip
  let : TopologicalSpace F := WeakBilin.instTopologicalSpace B.flip
  have hj : @Continuous F (Module.Dual ℂ E) (WeakBilin.instTopologicalSpace B.flip)
      (WeakBilin.instTopologicalSpace P) j :=
    WeakBilin.continuous_of_continuous_eval P fun x ↦ WeakBilin.eval_continuous B.flip x
  have hP : P.Nondegenerate := ⟨LinearMap.SeparatingLeft.id, LinearMap.SeparatingLeft.eval⟩
  let : TopologicalSpace (Module.Dual ℂ E) := WeakBilin.instTopologicalSpace P
  let : PolynormableSpace ℂ (Module.Dual ℂ E) := P.weakBilin_withSeminorms.toPolynormableSpace
  let : T2Space (WeakBilin P) := (WeakBilin.isEmbedding (B := P) fun _ _ h ↦ h).t2Space
  let : T2Space (Module.Dual ℂ E) := inferInstanceAs (T2Space (WeakBilin P))
  -- The bipolar of the image of the disk is the disk itself in the algebraic dual.
  have heq : P.flip.polar (P.polar (j '' D)) = j '' D := by
    let C : Set (WeakBilin P) := j '' D
    have hzero' : 0 ∈ C := ⟨0, h0D (mem_singleton 0), map_zero j⟩
    have hconv : AbsConvex ℂ C := ⟨hD.1.1.image j, hD.1.2.linear_image j⟩
    have hclosed : IsClosed C := (hD.2.image hj).isClosed
    let : TopologicalSpace E := WeakBilin.instTopologicalSpace P.flip
    let : PolynormableSpace ℂ E := P.flip.weakBilin_withSeminorms.toPolynormableSpace
    let : T2Space E := (WeakBilin.isEmbedding
      (LinearMap.ker_eq_bot.mp (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp hP.2))).t2Space
    calc
      _ = closure (X := WeakBilin P) (absConvexHull ℂ (insert 0 C)) :=
        bipolar_eq_weakClosure_absConvexHull P hP _
      _ = C := by rw [insert_eq_of_mem hzero', hconv.absConvexHull_eq, hclosed.closure_eq]
  let c : ℂ := (ε / 2 : ℝ)
  have hc : ‖c‖ = ε / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (half_pos hε).le]
  have hcl : c • l ∈ j '' D := by
    rw [← heq]
    intro x hx
    have hxD (y : F) (hy : y ∈ D) : ‖B x y‖ ≤ 1 := hx (j y) (mem_image_of_mem j hy)
    have hl' : ‖l (c • x)‖ < 1 := hbound fun y hy ↦ by
      change dist (B (c • x) y) (B 0 y) < ε
      rw [map_zero B, LinearMap.zero_apply, dist_zero_right, map_smul, LinearMap.smul_apply,
        smul_eq_mul, norm_mul, hc]
      exact (mul_le_of_le_one_right (half_pos hε).le (hxD y (hAD hy))).trans_lt (half_lt_self hε)
    change ‖(c • l) x‖ ≤ 1
    rw [LinearMap.smul_apply, ← map_smul]
    exact hl'.le
  obtain ⟨y, _, hy⟩ := hcl
  have hc₀ : c ≠ 0 := norm_pos_iff.mp (hc ▸ half_pos hε)
  refine ⟨c⁻¹ • y, ?_⟩
  change B.flip y = c • l at hy
  rw [map_smul, hy, inv_smul_smul₀ hc₀]

/-- Paper: Mackey–Arens Theorem (§C.2.2.2), p. 674. A Hausdorff locally convex topology on E
is consistent exactly when it is finer than the weak topology and coarser than the Mackey
topology. In Lean's order on topologies the finer topology is the smaller element. -/
theorem isConsistentWithDuality_iff_mackey_le_le_weak (hB : B.Nondegenerate)
    [t : TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E] :
    IsConsistentWithDuality B t ↔
      mackeyTopology B ≤ t ∧ t ≤ WeakBilin.instTopologicalSpace B := by
  constructor
  · intro h
    refine ⟨?_, continuous_id_iff_le.mp (WeakBilin.continuous_of_continuous_eval B fun y ↦
      (h (B.flip y)).mpr (mem_range_self y))⟩
    let K : Set (Set F) := {A | AbsConvex ℂ A ∧ IsCompact (X := WeakBilin B.flip) A}
    let ev (x : E) := UniformOnFun.ofFun K (B x)
    let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
    apply continuous_id_iff_le.mp
    apply (@continuous_iff_continuousAt E E (mackeyTopology B) t id).mpr
    intro x
    suffices hx : Tendsto (fun z : E ↦ z - x) (@nhds E (mackeyTopology B) x) (𝓝 0) by
      change Tendsto (fun z : E ↦ z) (@nhds E (mackeyTopology B) x) (@nhds E t x)
      simpa only [sub_add_cancel, zero_add] using hx.add_const x
    change Tendsto _ (@nhds E (TopologicalSpace.induced ev inferInstance) x) _
    rw [nhds_induced]
    refine (PolynormableSpace.hasBasis_zero_ball ℂ E).tendsto_right_iff.mpr fun p hp ↦ ?_
    obtain ⟨A, hA, hcompact, hattain⟩ := exists_mackeyDisk B h p hp
    have hnear := UniformOnFun.gen_mem_nhds ℂ K (ev x) (s := A) ⟨hA, hcompact⟩
      (Metric.uniformity_basis_dist.mem_iff.mpr ⟨1, one_pos, Subset.rfl⟩)
    filter_upwards [preimage_mem_comap hnear] with z hz
    obtain ⟨y, hy, hEq⟩ := hattain (z - x)
    have hlt : dist (B x y) (B z y) < 1 := hz y hy
    rw [dist_comm, dist_eq_norm, ← LinearMap.sub_apply, ← map_sub, hEq] at hlt
    exact p.mem_ball_zero.mpr hlt
  · rintro ⟨hM, hw⟩ l
    exact ⟨fun hl ↦ mem_range_flip_of_mackeyContinuous B l
        (@Continuous.comp E E ℂ (mackeyTopology B) t _ id l hl (continuous_id_iff_le.mpr hM)),
      fun hl ↦ @Continuous.comp E E ℂ t (WeakBilin.instTopologicalSpace B) _ id l
        ((weakTopology_isConsistentWithDuality B hB l).mpr hl) (continuous_id_iff_le.mpr hw)⟩

/-- Paper: §C.2.2.2, p. 674. The strong topology of the duality is uniform convergence
on all subsets of the opposite member that are bounded for its weak topology. -/
@[instance_reducible]
def strongDualityTopology : TopologicalSpace E :=
  polarTopology B {A | IsVonNBounded (E := WeakBilin B.flip) ℂ A}

/-- Paper: §C.2.2.2, p. 674. The strong topology is finer than the Mackey topology. -/
theorem strongDualityTopology_le_mackeyTopology (hB : B.Nondegenerate) :
    strongDualityTopology B ≤ mackeyTopology B := by
  have hsub : {A : Set F | AbsConvex ℂ A ∧ IsCompact (X := WeakBilin B.flip) A} ⊆
      {A | IsVonNBounded (E := WeakBilin B.flip) ℂ A} :=
    fun A hA ↦ IsCompact.isVonNBounded (E := WeakBilin B.flip) ℂ hA.2
  exact induced_mono (UniformSpace.toTopologicalSpace_mono (UniformOnFun.mono le_rfl hsub))

-- TODO(paper-gap): On p. 674 barrelledness of E does not imply β(E',E) = τ(E',E).
-- For the Banach space c₀, the norm dual of its strong dual ℓ¹ is ℓ∞, strictly larger than c₀.

/-- Paper: §C.2.2.2, p. 674. A Hausdorff locally convex space is barrelled precisely when
every closed, convex, circled, absorbent set is a neighborhood of zero. -/
theorem barrelledSpace_iff_barrels_mem_nhds [TopologicalSpace E] [PolynormableSpace ℂ E]
    [T2Space E] :
    BarrelledSpace ℂ E ↔
      ∀ U : Set E, IsClosed U → AbsConvex ℂ U → Absorbent ℂ U → U ∈ 𝓝 0 := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  constructor
  · intro h U hClosed hConvex hAbsorbent
    let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
    have hConvexReal : Convex ℝ U := hConvex.2.lift ℝ
    have hAbsorbentReal : Absorbent ℝ U := by
      intro x
      apply (hAbsorbent x).restrict_scalars
      change Tendsto (fun r : ℝ ↦ (r : ℂ) * 1) (cobounded ℝ) (cobounded ℂ)
      simpa only [mul_one] using Complex.isometry_ofReal.antilipschitzWith.tendsto_cobounded
    let p := gaugeSeminorm hConvex.1 hConvexReal hAbsorbentReal
    -- Each nonnegative sublevel of the gauge is an intersection of closed dilates.
    have hp : LowerSemicontinuous p := by
      rw [lowerSemicontinuous_iff_isClosed_preimage]
      intro r
      change IsClosed {x : E | gauge U x ≤ r}
      by_cases hr : 0 ≤ r
      · rw [setOfPred_gauge_le_eq hConvexReal hAbsorbentReal.zero_mem hAbsorbentReal hr]
        exact isClosed_iInter fun t ↦ isClosed_iInter fun ht ↦
          hClosed.smul_of_ne_zero (hr.trans_lt ht).ne'
      · rw [show {x : E | gauge U x ≤ r} = ∅ from
          eq_empty_iff_forall_notMem.mpr fun x hx ↦ hr ((gauge_nonneg x).trans hx)]
        exact isClosed_empty
    refine Filter.mem_of_superset
      ((Seminorm.continuous_iff (p := p) one_pos).mp (p.continuous_of_lowerSemicontinuous hp)) ?_
    rw [p.ball_zero_eq]
    exact setOfPred_gauge_lt_one_subset_self hConvexReal hAbsorbentReal.zero_mem hAbsorbentReal
  · intro h
    refine ⟨fun p hp ↦ Seminorm.continuous' (r := 1) (h (p.closedBall 0 1) ?_ ?_ ?_)⟩
    · rw [p.closedBall_zero_eq]
      exact hp.isClosed_preimage 1
    · exact ⟨p.balanced_closedBall_zero 1,
        convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 1)⟩
    · exact p.absorbent_closedBall_zero one_pos

end Duality

section Compactology

open scoped ComplexOrder

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Lemma C.2.2.2, p. 675. The equicontinuous compactology consists of all
weak-star closed, convex, circled, equicontinuous subsets of the continuous dual. -/
def equicontinuousCompactology : Set (Set (WeakDual ℂ E)) :=
  {A | EquicontinuousAt (fun l : A ↦ (l.val : E → ℂ)) 0 ∧ AbsConvex ℂ A ∧ IsClosed A}

variable [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.2.2.2, p. 675. The polar of every zero-neighborhood belongs to the
equicontinuous compactology. -/
theorem polar_mem_equicontinuousCompactology (U : Set E) (hU : U ∈ 𝓝 0) :
    StrongDual.toWeakDual '' (StrongDual.polar ℂ U) ∈ equicontinuousCompactology E := by
  let B : E →ₗ[ℂ] WeakDual ℂ E →ₗ[ℂ] ℂ :=
    (topDualPairing ℂ E).flip.compl₂ WeakDual.toStrongDual.toLinearMap
  have hpolar : StrongDual.toWeakDual '' StrongDual.polar ℂ U = B.polar U :=
    StrongDual.toWeakDual.image_eq_preimage_symm _
  rw [hpolar]
  refine ⟨?_, LinearMap.polar_AbsConvex (B := B) U, ?_⟩
  · rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨a, ha, haε⟩ := NormedField.exists_norm_lt ℂ hε
    have hnear : a • U ∈ 𝓝 (0 : E) := by
      simpa using smul_mem_nhds_smul₀ (norm_pos_iff.mp ha) hU
    filter_upwards [hnear] with x hx φ
    obtain ⟨y, hy, rfl⟩ := hx
    change dist (φ.val 0) (φ.val (a • y)) < ε
    rw [map_zero, dist_zero_left, map_smul, norm_smul]
    exact (mul_le_of_le_one_right ha.le (φ.property y hy)).trans_lt haε
  · rw [B.polar_eq_biInter_preimage]
    exact isClosed_biInter fun x _ ↦
      Metric.isClosed_closedBall.preimage (WeakDual.eval_continuous x)

omit [T2Space E] in
/-- The bipolar of a closed absolutely convex zero-neighborhood is contained in it. -/
lemma topDual_bipolar_subset (U : Set E) (hU : U ∈ 𝓝 0) (hc : IsClosed U)
    (ha : AbsConvex ℂ U) :
    (topDualPairing ℂ E).polar (StrongDual.polar ℂ U) ⊆ U := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  intro x hx
  by_contra hxU
  obtain ⟨f, r, hfr, hrx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (ha.2.lift ℝ) hc hxU
  have hnorm (z : E) (hz : z ∈ U) : ‖f z‖ < r := by
    obtain ⟨c, hc, hcz⟩ := RCLike.exists_norm_eq_mul_self (f z)
    have h := hfr (c • z) (balanced_iff_smul_mem.mp ha.1 hc.le hz)
    rw [map_smul, smul_eq_mul] at h
    change RCLike.re (c * f z) < r at h
    simpa only [← hcz, RCLike.ofReal_re] using h
  have hr : 0 < r := (norm_nonneg _).trans_lt (hnorm 0 (mem_of_mem_nhds hU))
  have hf : (r : ℂ)⁻¹ • f ∈ StrongDual.polar ℂ U := by
    intro z hz
    change ‖(r : ℂ)⁻¹ * f z‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      ← div_eq_inv_mul, div_le_iff₀ hr, one_mul]
    exact (hnorm z hz).le
  have hbound := hx _ hf
  change ‖(r : ℂ)⁻¹ * f x‖ ≤ 1 at hbound
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      ← div_eq_inv_mul, div_le_iff₀ hr, one_mul] at hbound
  change r < (f x).re at hrx
  exact (hrx.trans_le (Complex.re_le_norm _)).not_ge hbound

/-- The polar of a zero-neighborhood is weakly closed, absolutely convex and equicontinuous. -/
lemma topDual_polar_equicontinuousCompactology (U : Set E) (hU : U ∈ 𝓝 0) :
    StrongDual.toWeakDual '' (StrongDual.polar ℂ U) ∈ equicontinuousCompactology E := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let A : Set (WeakDual ℂ E) := StrongDual.toWeakDual '' (StrongDual.polar ℂ U)
  have hA : A = (topDualPairing ℂ E).flip.polar U := by
    ext l
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hl
      exact ⟨WeakDual.toStrongDual l, hl, WeakDual.toWeakDual_toStrongDual l⟩
  change EquicontinuousAt (fun l : A ↦ (l.val : E → ℂ)) 0 ∧ AbsConvex ℂ A ∧ IsClosed A
  refine ⟨?_, hA ▸ LinearMap.polar_AbsConvex _, hA ▸ LinearMap.polar_isClosed _ _⟩
  apply (equicontinuousAt_zero_iff_mapsTo (E := E) (F := ℂ) A).2
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  let c : ℂ := (ε / 2 : ℝ)
  have hc : c ≠ 0 := by simp [c, ne_of_gt hε]
  refine ⟨c • U, (set_smul_mem_nhds_zero_iff hc).2 hU, ?_⟩
  intro f hf x hx
  obtain ⟨y, hy, rfl⟩ := hx
  apply hεV
  have hfy : ‖f y‖ ≤ 1 := by
    have hf' : f ∈ (topDualPairing ℂ E).flip.polar U := hA ▸ hf
    exact hf' y hy
  rw [Metric.mem_ball, dist_zero_right, map_smul, smul_eq_mul, norm_mul]
  have hc' : ‖c‖ = ε / 2 := by simp [c, hε.le]
  rw [hc']
  nlinarith [norm_nonneg (f y)]

/-- Paper: Lemma C.2.2.2, p. 675. The polars in E of the members of the equicontinuous
compactology form a zero-neighborhood basis for the original topology on E. -/
theorem nhds_zero_hasBasis_equicontinuousCompactology :
    (𝓝 (0 : E)).HasBasis (· ∈ equicontinuousCompactology E)
      (fun A ↦ (topDualPairing ℂ E).polar (WeakDual.toStrongDual '' A)) := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  have : LocallyConvexSpace ℂ E := by
    apply LocallyConvexSpace.ofBasisZero ℂ E _ _ (LocallyConvexSpace.convex_basis_zero ℝ E)
    intro s hs
    apply convex_of_nonneg_surjective_algebraMap ℂ
      (fun z hz ↦ RCLike.nonneg_iff_exists_ofReal.mp (show 0 ≤ z from hz))
    exact hs.2
  refine ⟨fun V ↦ ⟨?_, ?_⟩⟩
  · intro hV
    obtain ⟨U, ⟨hU, hclosed, habs⟩, hUV⟩ := (nhds_hasBasis_absConvex_closed ℂ E).mem_iff.mp hV
    refine ⟨StrongDual.toWeakDual '' (StrongDual.polar ℂ U),
      topDual_polar_equicontinuousCompactology E U hU, ?_⟩
    have heq : WeakDual.toStrongDual '' (StrongDual.toWeakDual '' (StrongDual.polar ℂ U)) =
        StrongDual.polar ℂ U := by
      ext f
      constructor
      · rintro ⟨l, ⟨g, hg, rfl⟩, rfl⟩
        simpa only [StrongDual.toStrongDual_toWeakDual] using hg
      · intro hf
        exact ⟨StrongDual.toWeakDual f, ⟨f, hf, rfl⟩, StrongDual.toStrongDual_toWeakDual f⟩
    rw [heq]
    exact (topDual_bipolar_subset E U hU hclosed habs).trans hUV
  · rintro ⟨A, hA, hAV⟩
    apply mem_of_superset _ hAV
    have hb : (uniformity ℂ).HasBasis (fun V : Set ℂ ↦ V ∈ 𝓝 (0 : ℂ))
        (fun V ↦ (fun x : ℂ × ℂ ↦ x.2 - x.1) ⁻¹' V) := by
      rw [uniformity_eq_comap_nhds_zero]
      exact (𝓝 (0 : ℂ)).basis_sets.comap _
    have heq := hb.equicontinuousAt_iff_right.mp hA.1
    obtain ⟨U, hU, hmaps⟩ := eventually_iff_exists_mem.mp
      (heq (Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 one_pos))
    apply mem_of_superset hU
    intro x hx f hf
    obtain ⟨l, hl, rfl⟩ := hf
    have h := hmaps x hx ⟨l, hl⟩
    change ‖WeakDual.toStrongDual l x‖ ≤ 1
    simpa only [mem_preimage, map_zero, sub_zero, Metric.mem_closedBall, dist_zero_right,
      WeakDual.toStrongDual_apply] using h

end Compactology

end RiemannMasullo
