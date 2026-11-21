module

public import RiemannMasullo.AppC_LCTVS.Sec1
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.Algebra.Module.UniformConvergence

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
      mappingSeminorm ⟨a.1.val, hb _ a.1.property⟩ ⟨p a.2, hp.continuous_seminorm a.2⟩) := by sorry

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
      (inferInstance : TopologicalSpace (E →Lᵤ[ℂ, {T | IsCompact T}] F)) := by sorry

end MappingSpaces

section OperatorNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Paper: Remark C.2.1.6, p. 671. The operator norm is the supremum of the image norms
over the closed unit ball of the source. -/
theorem opNorm_eq_sup_closedUnitBall (f : E →L[ℂ] F) :
    ‖f‖ = ⨆ x : Metric.closedBall (0 : E) 1, ‖f x‖ := by sorry

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
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) F a.1).toLinearMap) := by sorry

/-- Paper: §C.2.1, p. 672. For a quasi-complete source, a pointwise bounded family of
operators is bounded for uniform convergence on each member of a directed bounded cover. -/
theorem uniformConvergenceCLM_bounded_of_pointwise [QuasiCompleteSpace ℂ E]
    (S : Set (Set E)) (hdir : DirectedOn (· ⊆ ·) S) (hcover : ⋃₀ S = univ)
    (hb : ∀ T ∈ S, IsVonNBounded ℂ T) (H : Set (E →L[ℂ] F))
    (hH : IsVonNBounded ℂ ((UniformConvergenceCLM.ofFun (RingHom.id ℂ) F {T | T.Finite}) '' H)) :
    IsVonNBounded ℂ ((UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S) '' H) := by sorry

/-- Paper: Lemma C.2.1.7, p. 672. For a barrelled source and quasi-complete target, uniform
convergence on a directed cover by bounded subsets gives a quasi-complete mapping space. -/
theorem uniformConvergenceCLM_quasiComplete [BarrelledSpace ℂ E] [QuasiCompleteSpace ℂ F]
    (S : Set (Set E)) (hdir : DirectedOn (· ⊆ ·) S) (hcover : ⋃₀ S = univ)
    (hb : ∀ T ∈ S, IsVonNBounded ℂ T) : QuasiCompleteSpace ℂ (E →Lᵤ[ℂ, S] F) := by sorry

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Remark C.2.1.8, p. 672. The strong operator topology on the bounded operators
of any Hilbert space is quasi-complete. -/
theorem hilbert_pointwiseOperators_quasiComplete : QuasiCompleteSpace ℂ (H →Lₚₜ[ℂ] H) := by sorry

-- The operator-norm completeness and quasi-completeness in Remark C.2.1.8 are already
-- stated in §C.1 as the last two conclusions of `hilbert_quasiComplete_examples`.

/-- Paper: Remark C.2.1.8, p. 672. Every complex Fréchet space is barrelled. -/
theorem isFrechetTVS_barrelled {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsFrechetTVS X) : BarrelledSpace ℂ X := by sorry

variable (A : Set (E →L[ℂ] F))
  (heq : EquicontinuousAt (fun f : A ↦ (f.val : E → F)) 0)

/-- Paper: §C.2.1, p. 672. Equicontinuity at zero means there is one source
zero-neighborhood that every map sends into the prescribed target zero-neighborhood. -/
theorem equicontinuousAt_zero_iff_mapsTo :
    EquicontinuousAt (fun f : A ↦ (f.val : E → F)) 0 ↔
      ∀ V ∈ 𝓝 (0 : F), ∃ U ∈ 𝓝 (0 : E), ∀ f ∈ A, MapsTo f U V := by sorry

include heq in
/-- Paper: Lemma C.2.1.9(1), p. 672. An equicontinuous set is bounded for uniform
convergence on bounded test sets whose union spans a dense subspace. -/
theorem equicontinuous_isVonNBounded_uniformConvergenceCLM
    (S : Set (Set E)) (hb : ∀ T ∈ S, IsVonNBounded ℂ T)
    (hdense : Dense (Submodule.span ℂ (⋃₀ S) : Set E)) :
    IsVonNBounded ℂ ((UniformConvergenceCLM.ofFun (RingHom.id ℂ) F S) '' A) := by sorry

include heq in
/-- Paper: Lemma C.2.1.9(2), p. 672. Pointwise and precompact convergence induce the
same topology on each equicontinuous set of operators. -/
theorem equicontinuous_induced_pointwise_eq_precompact :
    TopologicalSpace.induced (Subtype.val : A → E →L[ℂ] F)
        (inferInstance : TopologicalSpace (E →Lₚₜ[ℂ] F)) =
      TopologicalSpace.induced (Subtype.val : A → E →L[ℂ] F)
        (inferInstance : TopologicalSpace (PrecompactConvergenceCLM E F)) := by sorry

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
    Continuous l ↔ ∃ i, p i ∧ l ∈ (Module.Dual.eval ℂ E).polar (U i) := by sorry

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
    polarTopology B {A | A.Finite} = WeakBilin.instTopologicalSpace B := by sorry

/-- Paper: §C.2.2.2, p. 674. A topology on E is consistent with the pairing if its
continuous linear functionals are exactly the evaluations against elements of F. -/
def IsConsistentWithDuality (t : TopologicalSpace E) : Prop :=
  ∀ l : Module.Dual ℂ E, @Continuous E ℂ t _ l ↔ l ∈ range B.flip

/-- Paper: §C.2.2.2, p. 674. The weak topology of a separating pairing is consistent. -/
theorem weakTopology_isConsistentWithDuality (hB : B.Nondegenerate) :
    IsConsistentWithDuality B (WeakBilin.instTopologicalSpace B) := by sorry

/-- Paper: §C.2.2.2, p. 674. The Mackey topology on E is uniform convergence on the
convex circled subsets of F which are compact for the opposite weak topology. -/
@[instance_reducible]
def mackeyTopology : TopologicalSpace E :=
  polarTopology B {A | AbsConvex ℂ A ∧ IsCompact (X := WeakBilin B.flip) A}

/-- Paper: Mackey–Arens Theorem (§C.2.2.2), p. 674. A Hausdorff locally convex topology on E
is consistent exactly when it is finer than the weak topology and coarser than the Mackey
topology. In Lean's order on topologies the finer topology is the smaller element. -/
theorem isConsistentWithDuality_iff_mackey_le_le_weak (hB : B.Nondegenerate)
    [t : TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E] :
    IsConsistentWithDuality B t ↔
      mackeyTopology B ≤ t ∧ t ≤ WeakBilin.instTopologicalSpace B := by sorry

/-- Paper: §C.2.2.2, p. 674. The strong topology of the duality is uniform convergence
on all subsets of the opposite member that are bounded for its weak topology. -/
@[instance_reducible]
def strongDualityTopology : TopologicalSpace E :=
  polarTopology B {A | IsVonNBounded (E := WeakBilin B.flip) ℂ A}

/-- Paper: §C.2.2.2, p. 674. The strong topology is finer than the Mackey topology. -/
theorem strongDualityTopology_le_mackeyTopology (hB : B.Nondegenerate) :
    strongDualityTopology B ≤ mackeyTopology B := by sorry

-- TODO(paper-gap): On p. 674 barrelledness of E does not imply β(E',E) = τ(E',E).
-- For the Banach space c₀, the norm dual of its strong dual ℓ¹ is ℓ∞, strictly larger than c₀.

/-- Paper: §C.2.2.2, p. 674. A Hausdorff locally convex space is barrelled precisely when
every closed, convex, circled, absorbent set is a neighborhood of zero. -/
theorem barrelledSpace_iff_barrels_mem_nhds [TopologicalSpace E] [PolynormableSpace ℂ E]
    [T2Space E] :
    BarrelledSpace ℂ E ↔
      ∀ U : Set E, IsClosed U → AbsConvex ℂ U → Absorbent ℂ U → U ∈ 𝓝 0 := by sorry

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
    StrongDual.toWeakDual '' (StrongDual.polar ℂ U) ∈ equicontinuousCompactology E := by sorry

/-- Paper: Lemma C.2.2.2, p. 675. The polars in E of the members of the equicontinuous
compactology form a zero-neighborhood basis for the original topology on E. -/
theorem nhds_zero_hasBasis_equicontinuousCompactology :
    (𝓝 (0 : E)).HasBasis (· ∈ equicontinuousCompactology E)
      (fun A ↦ (topDualPairing ℂ E).polar (WeakDual.toStrongDual '' A)) := by sorry

end Compactology

end RiemannMasullo
