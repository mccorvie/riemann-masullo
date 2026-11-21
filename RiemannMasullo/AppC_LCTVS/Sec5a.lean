module

public import RiemannMasullo.AppC_LCTVS.Sec4
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Vector-valued continuous and differentiable functions

Masullo, Appendix C, §C.5.1. Mathlib supplies topological support, compactly supported
continuous maps as a vector space, and the compact-open topology on continuous maps.
The topology of the compactly supported space is specified explicitly.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped CompactlySupported DirectSum

namespace RiemannMasullo

section CompactSupport

variable {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

-- TODO(paper-gap): The p. 720 preamble infers a continuous one-point extension from
-- boundedness and asserts incompleteness of the scalar compactly supported space for all X.

/-- Paper: Definition C.5.1.1, p. 721. The fixed-support stage consists of compactly
supported continuous maps that vanish off the given compact set. -/
def compactSupportStage (K : Compacts X) : Submodule ℂ C_c(X, E) :=
  ⨅ (x : X) (_ : x ∉ (K : Set X)), LinearMap.ker
    ({ toFun := fun f ↦ f x
       map_add' := fun f g ↦ CompactlySupportedContinuousMap.add_apply x f g
       map_smul' := fun c f ↦ CompactlySupportedContinuousMap.smul_apply c f x } : C_c(X, E) →ₗ[ℂ] E)

/-- Paper: Definition C.5.1.1, p. 721. On a fixed-support stage, uniform convergence
is induced by restriction to the compact set, where the compact-open topology is uniform. -/
@[instance_reducible]
def compactSupportStageTopology (K : Compacts X) :
    TopologicalSpace (compactSupportStage (E := E) K) :=
  TopologicalSpace.induced
    (fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(K : Set X), X))) inferInstance

/-- Paper: Definition C.5.1.1, p. 721. The topology on compactly supported maps is
the final locally convex topology of the compact support stages with uniform convergence. -/
@[instance_reducible]
def compactSupportLCTopology (X E : Type*) [TopologicalSpace X] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] :
    TopologicalSpace C_c(X, E) :=
  letI (K : Compacts X) : TopologicalSpace (compactSupportStage (E := E) K) :=
    compactSupportStageTopology K
  locallyConvexFinalTopology (fun K : Compacts X ↦ (compactSupportStage (E := E) K).subtype)

variable [T2Space X] [LocallyCompactSpace X] [T2Space E] [PolynormableSpace ℂ E]

/-- Paper: Definition C.5.1.1, p. 721. For a compact set in a Hausdorff space, vanishing
off the set is equivalent to having topological support contained in it. -/
theorem mem_compactSupportStage_iff (K : Compacts X) (f : C_c(X, E)) :
    f ∈ compactSupportStage K ↔ tsupport (f : X → E) ⊆ (K : Set X) := by
  rw [tsupport, K.isCompact.isClosed.closure_subset_iff, Function.support_subset_iff']
  simp only [compactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

/-- Paper: Definition C.5.1.1, p. 721. Whole-space restriction on a compact domain
identifies the fixed-support topology with the topology on continuous maps. -/
theorem compactSupportStageTopology_univ [CompactSpace X] :
    let K : Compacts X := ⟨univ, isCompact_univ⟩
    compactSupportStageTopology (E := E) K =
      TopologicalSpace.induced
        (fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) inferInstance := by
  intro K
  let restrictUniv : C(X, E) ≃ₜ C(↥(univ : Set X), E) :=
    (Homeomorph.Set.univ X).symm.arrowCongr (Homeomorph.refl E)
  change TopologicalSpace.induced
    (restrictUniv ∘ fun f : compactSupportStage (E := E) K ↦ f.val.toContinuousMap) _ = _
  rw [← induced_compose, ← restrictUniv.isInducing.eq_induced]

/-- Paper: Definition C.5.1.1, p. 721. For compact X, the inductive limit topology
agrees with the topology induced by the inclusion into continuous maps. -/
theorem compactSupportLCTopology_of_compact [CompactSpace X] :
    compactSupportLCTopology X E =
      TopologicalSpace.induced (CompactlySupportedContinuousMap.toContinuousMap :
        C_c(X, E) → C(X, E)) inferInstance := by sorry

/-- Paper: Lemma C.5.1.3(1), p. 721. The inductive limit topology on compactly supported
continuous maps is Hausdorff. -/
theorem compactSupportLCTopology_t2 :
    @T2Space C_c(X, E) (compactSupportLCTopology X E) := by sorry

/-- Paper: Lemma C.5.1.3(1), p. 721. The fixed-support stage embeds with its
uniform-convergence topology into the inductive limit. -/
theorem isEmbedding_compactSupportStage (K : Compacts X) :
    letI := compactSupportLCTopology X E
    letI := compactSupportStageTopology (E := E) K
    IsEmbedding ((compactSupportStage (E := E) K).subtype : _ → C_c(X, E)) := by sorry

/-- Paper: Lemma C.5.1.3(1), p. 721. The continuous maps supported in a fixed compact
set form a closed subset in the inductive limit topology. -/
theorem isClosed_compactSupportStage (K : Compacts X) :
    letI := compactSupportLCTopology X E
    IsClosed (compactSupportStage (E := E) K : Set C_c(X, E)) := by sorry

/-- Paper: Lemma C.5.1.3(2), p. 721. Restriction to each summand identifies compactly
supported maps on a topological disjoint union with the locally convex direct sum. -/
theorem compactSupport_sigma {I : Type*} (Y : I → Type*) [∀ i, TopologicalSpace (Y i)]
    [∀ i, T2Space (Y i)] [∀ i, LocallyCompactSpace (Y i)] :
    letI := compactSupportLCTopology (Σ i, Y i) E
    letI (i : I) := compactSupportLCTopology (Y i) E
    letI : DecidableEq I := Classical.decEq I
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I (fun i ↦ C_c(Y i, E)))
    ∃ e : C_c((Σ i, Y i), E) ≃L[ℂ] (⨁ i, C_c(Y i, E)),
      ∀ f i y, (e f i) y = f ⟨i, y⟩ := by sorry

/-- Paper: Definition C.5.1.1, p. 721. Continuous seminorms generate the locally
convex inductive limit topology on compactly supported maps. -/
theorem compactSupportLCTopology_polynormable :
    letI := compactSupportLCTopology X E
    PolynormableSpace ℂ C_c(X, E) := by sorry

/-- Paper: Lemma C.5.1.3(3), p. 721. For a paracompact domain and quasi-complete
target, the inductive limit of compact support stages is quasi-complete. -/
theorem compactSupport_quasiComplete [ParacompactSpace X] :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    letI := compactSupportLCTopology X E
    letI := compactSupportLCTopology_polynormable (X := X) (E := E)
    letI := PolynormableSpace.isTopologicalAddGroup ℂ C_c(X, E)
    letI := IsTopologicalAddGroup.rightUniformSpace C_c(X, E)
    QuasiCompleteSpace ℂ E → QuasiCompleteSpace ℂ C_c(X, E) := by sorry

/-- Paper: Lemma C.5.1.3(4), p. 721. For a paracompact domain, the supports of all maps
in a bounded family in the inductive limit lie in a single compact set. -/
theorem compactSupport_bounded_subset_stage [ParacompactSpace X] :
    letI := compactSupportLCTopology X E
    ∀ B : Set C_c(X, E), IsVonNBounded ℂ B →
      ∃ K : Compacts X, B ⊆ (compactSupportStage (E := E) K : Set C_c(X, E)) := by sorry

/-- Paper: Lemma C.5.1.3(5), p. 721. Compactly supported continuous maps are dense
among continuous maps for the compact-open topology. -/
theorem denseRange_compactSupport_toContinuousMap :
    DenseRange (CompactlySupportedContinuousMap.toContinuousMap : C_c(X, E) → C(X, E)) := by sorry

/-- Paper: Lemma C.5.1.3(6), p. 721. The compact-open continuous-map space of a
quasi-complete locally convex target has its topology generated by continuous seminorms. -/
theorem continuousMap_polynormable :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → PolynormableSpace ℂ C(X, E) := by sorry

/-- Paper: Lemma C.5.1.3(6), p. 721. The compact-open continuous-map space of a
quasi-complete locally convex target is quasi-complete. Mathlib supplies Hausdorffness. -/
theorem continuousMap_quasiComplete :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → QuasiCompleteSpace ℂ C(X, E) := by sorry

/-- Paper: Example C.5.1.5, p. 722. Positive integer translates of a nonzero continuous
map supported in the unit interval converge to zero in the compact-open topology.
Deviation: The same formulation covers the scalar example and its Fréchet-valued version. -/
theorem compactSupport_translate_tendsto_compactOpen (f : C_c(ℝ, E)) (hf : f ≠ 0)
    (hK : tsupport (f : ℝ → E) ⊆ Icc 0 1)
    (g : ℕ → C_c(ℝ, E)) (hg : ∀ n x, g n x = f (x - n)) :
    Tendsto (fun n ↦ (g n).toContinuousMap) atTop (𝓝 0) := by sorry

/-- Paper: Example C.5.1.5, p. 722. Positive integer translates of a nonzero continuous
map supported in the unit interval have no limit in the inductive limit topology.
Deviation: The same formulation covers the scalar example and its Fréchet-valued version. -/
theorem compactSupport_translate_no_inductiveLimit (hE : IsFrechetTVS E)
    (f : C_c(ℝ, E)) (hf : f ≠ 0) (hK : tsupport (f : ℝ → E) ⊆ Icc 0 1)
    (g : ℕ → C_c(ℝ, E)) (hg : ∀ n x, g n x = f (x - n)) :
    letI := compactSupportLCTopology ℝ E
    ¬ ∃ a : C_c(ℝ, E), Tendsto g atTop (𝓝 a) := by sorry

-- TODO(paper-gap): The last sentence of Example C.5.1.5 extends the distinction to
-- compact manifolds, where the two topologies agree.

end CompactSupport

section Differentials

variable {k V E : Type*} [RCLike k] [NormedAlgebra k ℂ]
  [NormedAddCommGroup V] [NormedSpace k V]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local instance : Module k (PettisWeakCompletion E) :=
  Module.compHom (PettisWeakCompletion E) (algebraMap k ℂ)

/-- Paper: Definition C.5.1.6, p. 723. Weak differentiability means that every
continuous complex-linear functional gives a scalar differentiable function.
Deviation: The definitions also accept a general normed source over the base field. -/
def WeaklyDifferentiableOn (k : Type*) [RCLike k] [NormedAlgebra k ℂ]
    [NormedSpace k V] (f : V → E) (Ω : Set V) : Prop :=
  ∀ φ : StrongDual ℂ E, DifferentiableOn k (φ ∘ f) Ω

/-- Paper: Definition C.5.1.6, p. 723. A weak differential represents all scalar
differentials when evaluated on continuous complex-linear functionals.
Deviation: The differential is specified by its graph property on an ambient function. -/
def HasWeakDifferentialOn (k : Type*) [RCLike k] [NormedAlgebra k ℂ]
    [NormedSpace k V] {Ω : Set V} (f : V → E) (D : Ω × V → PettisWeakCompletion E) : Prop :=
  ∀ (φ : StrongDual ℂ E) (x : Ω), ∃ L : V →L[k] ℂ,
    HasFDerivWithinAt (φ ∘ f) L Ω x ∧
      ∀ v, (show Module.Dual ℂ (StrongDual ℂ E) from D (x, v)) φ = L v

/-- Paper: Definition C.5.1.6, p. 723. Weak continuous differentiability requires a
weak differential that is jointly continuous for the pointwise topology of the weak completion. -/
def WeaklyContDiffOn (k : Type*) [RCLike k] [NormedAlgebra k ℂ]
    [NormedSpace k V] (f : V → E) (Ω : Set V) : Prop :=
  ∃ D : Ω × V → PettisWeakCompletion E, HasWeakDifferentialOn k f D ∧ Continuous D

/-- Paper: Definition C.5.1.6, p. 723. On an open set, weak differentiability is
equivalent to existence of a unique weak differential. -/
theorem weaklyDifferentiableOn_iff_existsUnique {Ω : Set V} (hΩ : IsOpen Ω) (f : V → E) :
    WeaklyDifferentiableOn k f Ω ↔
      ∃! D : Ω × V → PettisWeakCompletion E, HasWeakDifferentialOn k f D := by sorry

/-- Paper: Definition C.5.1.6, p. 723. Weak continuous differentiability on an open
set means continuous differentiability of each scalar evaluation. -/
theorem weaklyContDiffOn_iff_scalar {Ω : Set V} (hΩ : IsOpen Ω) (f : V → E) :
    WeaklyContDiffOn k f Ω ↔ ∀ φ : StrongDual ℂ E, ContDiffOn k 1 (φ ∘ f) Ω := by sorry

/-- Paper: Definition C.5.1.8(1), p. 724. The continuous differential in the weak
completion is linear in the direction and has a vanishing normalized remainder there. -/
def HasWeakCompletionDifferentialOn {Ω : Set V} (f : V → E)
    (D : Ω × V → PettisWeakCompletion E) : Prop :=
  Continuous D ∧ ∀ x : Ω,
    (∃ L : V →ₗ[k] PettisWeakCompletion E, ∀ v, D (x, v) = L v) ∧
    Tendsto (fun y : V ↦ ((‖y - (x : V)‖⁻¹ : ℝ) : ℂ) •
      (toPettisWeakCompletion E (f y) - toPettisWeakCompletion E (f x) - D (x, y - (x : V))))
      (𝓝[Ω \ {(x : V)}] (x : V)) (𝓝 0)

/-- Paper: Definition C.5.1.8(2), p. 724. Weak directional derivatives are the limits
of directional difference quotients on the punctured line inside the domain. -/
def HasWeakDirectionalDerivativesOn {Ω : Set V} (f : V → E)
    (D : Ω × V → PettisWeakCompletion E) : Prop :=
  ∀ (x : Ω) (v : V),
    Tendsto (fun h : k ↦ algebraMap k ℂ h⁻¹ •
      toPettisWeakCompletion E (f ((x : V) + h • v) - f x))
      (𝓝[{h : k | h ≠ 0 ∧ (x : V) + h • v ∈ Ω}] 0) (𝓝 (D (x, v)))

/-- Paper: Definition C.5.1.8(2), p. 724. Gâteaux differentiability in the weak
completion means that every directional limit exists there. -/
def WeakGateauxDifferentiableOn (Ω : Set V) (f : V → E) : Prop :=
  ∃ D : Ω × V → PettisWeakCompletion E, HasWeakDirectionalDerivativesOn (k := k) f D

/-- Paper: Definition C.5.1.8(3), p. 724. A strong continuous differential is a
jointly continuous vector-valued lift of the differential in the weak completion. -/
def HasStrongDifferentialOn {Ω : Set V} (f : V → E) (D : Ω × V → E) : Prop :=
  Continuous D ∧ HasWeakCompletionDifferentialOn (k := k) f (toPettisWeakCompletion E ∘ D)

/-- Paper: Definition C.5.1.8(3), p. 724. Strong continuous differentiability means
that such a differential exists and takes values in the original space. -/
def VectorContDiffOn (Ω : Set V) (f : V → E) : Prop :=
  ∃ D : Ω × V → E, HasStrongDifferentialOn (k := k) f D

/-- Paper: Definition C.5.1.8, p. 724. The identity on the complex line has the
identity differential and the expected directional limits in the weak completion. -/
theorem vectorDifferentials_complex_id :
    let D : ↥(univ : Set ℂ) × ℂ → PettisWeakCompletion ℂ :=
      fun xv ↦ toPettisWeakCompletion ℂ xv.2
    HasWeakCompletionDifferentialOn (k := ℂ) id D ∧
      HasWeakDirectionalDerivativesOn (k := ℂ) id D ∧
      WeakGateauxDifferentiableOn (k := ℂ) univ (id : ℂ → ℂ) ∧
      HasStrongDifferentialOn (k := ℂ) (Ω := (univ : Set ℂ)) id Prod.snd ∧
      VectorContDiffOn (k := ℂ) univ (id : ℂ → ℂ) := by sorry

variable {d : ℕ}

local notation "W" => EuclideanSpace k (Fin d)

/-- Paper: Lemma C.5.1.12, p. 725. The scalar weak differential and the differential
from the weak-completion remainder agree, with the same continuously varying values.
Deviation: In (C.5.1.14) the base point is the first argument and the direction the second. -/
theorem hasWeakCompletionDifferentialOn_iff {Ω : Set W} (hΩ : IsOpen Ω) (f : W → E)
    (D : Ω × W → PettisWeakCompletion E) :
    HasWeakCompletionDifferentialOn (k := k) f D ↔
      HasWeakDifferentialOn k f D ∧ Continuous D := by sorry

/-- Paper: Lemma C.5.1.12, p. 725. A continuous differential in the weak completion
gives the weak Gâteaux derivatives, with derivative zero in the zero direction. -/
theorem HasWeakCompletionDifferentialOn.hasWeakDirectionalDerivativesOn {Ω : Set W}
    (hΩ : IsOpen Ω) {f : W → E} {D : Ω × W → PettisWeakCompletion E}
    (hD : HasWeakCompletionDifferentialOn (k := k) f D) :
    HasWeakDirectionalDerivativesOn (k := k) f D := by sorry

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

-- TODO(paper-gap): C.5.1.13(1) gives one bounded set of quotients on all of Ω.
-- The scalar map x ↦ x² on ℝ contradicts (C.5.1.19).

/-- Paper: Lemma C.5.1.13(1), p. 726. A weakly continuously differentiable
vector-valued map is continuous for the given topology.
Deviation: Only the continuity consequence holds on an arbitrary open domain. -/
theorem WeaklyContDiffOn.continuousOn {Ω : Set W} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : W → E}
    (hf : WeaklyContDiffOn k f Ω) : ContinuousOn f Ω := by sorry

/-- Paper: Lemma C.5.1.13(2), p. 726. A jointly continuous vector-valued weak
differential is a strong continuous differential. -/
theorem hasStrongDifferentialOn_of_weak {Ω : Set W} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : W → E}
    {D : Ω × W → E} (hD : HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D))
    (hc : Continuous D) : HasStrongDifferentialOn (k := k) f D := by sorry

/-- Paper: Lemma C.5.1.13(2), p. 726. Directional difference quotients converge in
the given vector topology to the jointly continuous vector-valued weak differential. -/
theorem tendsto_directional_of_weakDifferential {Ω : Set W} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : W → E}
    {D : Ω × W → E} (hD : HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D))
    (hc : Continuous D) (x : Ω) (v : W) :
    Tendsto (fun h : k ↦ algebraMap k ℂ h⁻¹ • (f ((x : W) + h • v) - f x))
      (𝓝[{h : k | h ≠ 0 ∧ (x : W) + h • v ∈ Ω}] 0) (𝓝 (D (x, v))) := by sorry

end Differentials

section PartialDifferentials

variable {k E : Type*} [RCLike k] [NormedAlgebra k ℂ] {d : ℕ}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local notation "V" => EuclideanSpace k (Fin d)

/-- Paper: Definition C.5.1.14, p. 728. Every scalar evaluation has a derivative
along the specified standard coordinate line at every point of the domain. -/
def WeaklyPartialDifferentiableOn (i : Fin d) (f : V → E) (Ω : Set V) : Prop :=
  ∀ (φ : StrongDual ℂ E) (x : Ω),
    DifferentiableWithinAt k (fun t : k ↦ φ (f ((x : V) + t • EuclideanSpace.single i 1)))
      {t | (x : V) + t • EuclideanSpace.single i 1 ∈ Ω} 0

/-- Paper: Definition C.5.1.14, p. 728. The weak partial derivative evaluated at a
functional is the ordinary partial derivative of the scalar evaluation. -/
def HasWeakPartialOn {Ω : Set V} (i : Fin d) (f : V → E)
    (D : Ω → PettisWeakCompletion E) : Prop :=
  ∀ (φ : StrongDual ℂ E) (x : Ω),
    HasDerivWithinAt (fun t : k ↦ φ (f ((x : V) + t • EuclideanSpace.single i 1)))
      ((show Module.Dual ℂ (StrongDual ℂ E) from D x) φ)
      {t | (x : V) + t • EuclideanSpace.single i 1 ∈ Ω} 0

/-- Paper: Definition C.5.1.14, p. 728. On an open set, weak differentiability in a
coordinate direction is equivalent to existence of a unique weak partial derivative. -/
theorem weaklyPartialDifferentiableOn_iff_existsUnique {Ω : Set V} (hΩ : IsOpen Ω)
    (i : Fin d) (f : V → E) :
    WeaklyPartialDifferentiableOn i f Ω ↔
      ∃! D : Ω → PettisWeakCompletion E, HasWeakPartialOn i f D := by sorry

/-- Paper: Lemma C.5.1.15, p. 728. A weak differential is jointly continuous
exactly when each weak coordinate partial exists and is continuous. -/
theorem weaklyContDiffOn_iff_continuous_weakPartials {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    WeaklyContDiffOn k f Ω ↔
      ∀ i : Fin d, ∃ D : Ω → PettisWeakCompletion E, HasWeakPartialOn i f D ∧ Continuous D :=
  by sorry

/-- Paper: Lemma C.5.1.16(1), p. 729. Weak Gâteaux differentiability gives weak
differentiability in each standard coordinate direction. -/
theorem WeakGateauxDifferentiableOn.weaklyPartialDifferentiableOn {Ω : Set V}
    (hΩ : IsOpen Ω) {f : V → E} (hf : WeakGateauxDifferentiableOn (k := k) Ω f) (i : Fin d) :
    WeaklyPartialDifferentiableOn i f Ω := by sorry

/-- Paper: Lemma C.5.1.16(2), p. 729. A jointly continuous weak Gâteaux derivative
is the weak differential. -/
theorem hasWeakDifferentialOn_of_continuous_directional {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) {f : V → E} {D : Ω × V → PettisWeakCompletion E}
    (hD : HasWeakDirectionalDerivativesOn (k := k) f D) (hc : Continuous D) :
    HasWeakDifferentialOn k f D := by sorry

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.5.1.16(3), p. 729. An E-valued weak Gâteaux derivative continuous
in the base point for each direction is the strong continuous differential. -/
theorem hasStrongDifferentialOn_of_basepoint_continuous_directional {Ω : Set V}
    (hΩ : IsOpen Ω) (hd : 1 ≤ d) {f : V → E} {D : Ω × V → E}
    (hD : HasWeakDirectionalDerivativesOn (k := k) f (toPettisWeakCompletion E ∘ D))
    (hc : ∀ v : V, Continuous (fun x : Ω ↦ D (x, v))) :
    HasStrongDifferentialOn (k := k) f D := by sorry

/-- Paper: Lemma C.5.1.17(1), p. 730. Precomposition with a differentiable map
preserves weak differentiability. -/
theorem WeaklyDifferentiableOn.comp {Ω₁ Ω₂ : Set V} (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂)
    {f : V → E} {g : V → V} (hf : WeaklyDifferentiableOn k f Ω₂)
    (hg : DifferentiableOn k g Ω₁) (hmap : MapsTo g Ω₁ Ω₂) :
    WeaklyDifferentiableOn k (f ∘ g) Ω₁ := by sorry

-- TODO(paper-gap): In C.5.1.17(2), taking f to be the scalar inclusion and g(t) =
-- t² sin(1/t) (with g(0) = 0) disproves continuous differentiability of the composite.

/-- Paper: Lemma C.5.1.17(2), p. 730. The chain rule identifies the weak differential of
the composite with the image of the vector-valued differential composed with the inner one.
Deviation: For the printed differentiability assumption on the inner map, the chain rule
survives while the claimed continuity of the composite differential fails. -/
theorem HasStrongDifferentialOn.comp_weak {Ω₁ Ω₂ : Set V}
    (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) {f : V → E} {g : V → V} {D : Ω₂ × V → E}
    (hD : HasStrongDifferentialOn (k := k) f D)
    (hg : DifferentiableOn k g Ω₁) (hmap : MapsTo g Ω₁ Ω₂) :
    HasWeakDifferentialOn k (f ∘ g) (fun xv : Ω₁ × V ↦
      toPettisWeakCompletion E (D (⟨g xv.1, hmap xv.1.property⟩,
        fderivWithin k g Ω₁ xv.1 xv.2))) := by sorry

-- TODO(paper-gap): For Lemma C.5.1.19, f(x) = x and γ(t) = t² sin(1/t²), extended by
-- zero, give a differentiable curve with a discontinuous, non-Lebesgue-integrable derivative.

/-- Paper: Lemma C.5.1.19, p. 731. Evaluation of the vector-valued chain-rule
expression gives the derivative of the scalar composite along a real curve.
Deviation: The pointwise identity survives the printed curve regularity. The continuity
and Pettis integral assertions require more than the stated assumptions. -/
theorem HasStrongDifferentialOn.hasDerivWithinAt_curve
    [NormedSpace ℝ V] [IsScalarTower ℝ k V] [IsScalarTower ℝ k ℂ]
    {a₀ b₀ a b : ℝ} (hab : a ≤ b) (hinterval : Icc a b ⊆ Ioo a₀ b₀)
    {Ω U : Set V} (hΩ : IsOpen Ω) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f : V → E} {D : U × V → E} (hD : HasStrongDifferentialOn (k := k) f D)
    {γ : ℝ → V} (hγ : DifferentiableOn ℝ γ (Ioo a₀ b₀))
    (hγΩ : MapsTo γ (Ioo a₀ b₀) Ω) (hγU : MapsTo γ (Icc a b) U)
    (hd : 1 ≤ d) (φ : StrongDual ℂ E) {t : ℝ} (ht : t ∈ Icc a b) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      HasDerivWithinAt (φ ∘ f ∘ γ)
        (φ (D (⟨γ t, hγU ht⟩, derivWithin γ (Ioo a₀ b₀) t)))
        (Ioo a₀ b₀) t := by sorry

/-- Paper: Theorem C.5.1.21(1, 2), p. 732. Strong continuous differentiability
is equivalent to a weak differential with a jointly continuous vector-valued lift. -/
theorem vectorContDiffOn_iff_weakDifferential {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    VectorContDiffOn (k := k) Ω f ↔
      ∃ D : Ω × V → E, HasWeakDifferentialOn k f (toPettisWeakCompletion E ∘ D) ∧
        Continuous D := by sorry

/-- Paper: Theorem C.5.1.21(1, 3), p. 732. Strong continuous differentiability
is equivalent to weak coordinate partials with continuous vector-valued lifts. -/
theorem vectorContDiffOn_iff_weakPartials {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    VectorContDiffOn (k := k) Ω f ↔
      ∀ i : Fin d, ∃ D : Ω → E, HasWeakPartialOn i f (toPettisWeakCompletion E ∘ D) ∧
        Continuous D := by sorry

/-- Paper: Theorem C.5.1.21(1, 4), p. 732. Strong continuous differentiability
is equivalent to jointly continuous vector-valued lifts of the weak directional limits. -/
theorem vectorContDiffOn_iff_weakDirectional {Ω : Set V} (hΩ : IsOpen Ω)
    (hd : 1 ≤ d) (f : V → E) :
    VectorContDiffOn (k := k) Ω f ↔
      ∃ D : Ω × V → E,
        HasWeakDirectionalDerivativesOn (k := k) f (toPettisWeakCompletion E ∘ D) ∧
          Continuous D := by sorry

/-- Paper: Lemma C.5.1.22, p. 732. If all scalar evaluations extend with one
continuous derivative, the vector-valued function extends uniquely as a continuous map
on the open domain and that extension is weakly continuously differentiable.
Deviation: Uniqueness is on the domain of extension. Values outside it are immaterial. -/
theorem exists_weaklyContDiffOn_extension_puncture {Ω : Set k} (hΩ : IsOpen Ω)
    {x₀ : k} (hx₀ : x₀ ∈ Ω) (f : k → E)
    (hf : ∀ φ : StrongDual ℂ E, ContDiffOn k 1 (φ ∘ f) (Ω \ {x₀}) ∧
      ∃ g : k → ℂ, ContDiffOn k 1 g Ω ∧ EqOn g (φ ∘ f) (Ω \ {x₀})) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      ∃ F : k → E, ContinuousOn F Ω ∧ EqOn F f (Ω \ {x₀}) ∧ WeaklyContDiffOn k F Ω ∧
        ∀ G : k → E, ContinuousOn G Ω → EqOn G f (Ω \ {x₀}) → EqOn G F Ω := by sorry

end PartialDifferentials

section HigherDifferentiability

variable {k E : Type*} [RCLike k] [NormedAlgebra k ℂ] {d : ℕ}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local notation "V" => EuclideanSpace k (Fin d)

/-- Paper: Definition C.5.1.23, p. 733. At order zero one bounded set
contains all normalized differences of points at distance at most one. At successor
order each weak partial has a continuous vector-valued lift of the preceding order. -/
def VectorContDiffOrderOn (f : V → E) (Ω : Set V) : ℕ → Prop
  | 0 => IsVonNBounded ℂ
      { z : E | ∃ x ∈ Ω, ∃ y ∈ Ω, x ≠ y ∧ ‖y - x‖ ≤ 1 ∧
        z = ((‖y - x‖⁻¹ : ℝ) : ℂ) • (f y - f x) }
  | m + 1 => ∀ i : Fin d, ∃ g : V → E,
      HasWeakPartialOn i f (fun x : Ω ↦ toPettisWeakCompletion E (g x)) ∧
        ContinuousOn g Ω ∧ VectorContDiffOrderOn g Ω m

/-- Paper: Definition C.5.1.23, p. 734. Smoothness in the sense of
this definition requires every order, including its bounded-difference order zero. -/
def VectorSmoothOn (f : V → E) (Ω : Set V) : Prop :=
  ∀ m : ℕ, VectorContDiffOrderOn f Ω m

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Definition C.5.1.23, p. 734. The zero map has every order of differentiability. -/
theorem vectorContDiffOrderOn_zero (Ω : Set V) (m : ℕ) :
    VectorContDiffOrderOn (0 : V → E) Ω m := by
  induction m with
  | zero =>
    show IsVonNBounded ℂ _
    refine (Bornology.isVonNBounded_singleton (0 : E)).subset ?_
    rintro z ⟨x, -, y, -, -, -, rfl⟩
    simp
  | succ m ih =>
    intro i
    refine ⟨0, ?_, continuousOn_const, ih⟩
    intro φ x
    simp only [Pi.zero_apply, map_zero]
    exact hasDerivWithinAt_const _ _ _

/-- Paper: Definition C.5.1.23, p. 734. The order condition is preserved by addition. -/
theorem VectorContDiffOrderOn.add {Ω : Set V} {m : ℕ} {f g : V → E}
    (hf : VectorContDiffOrderOn f Ω m) (hg : VectorContDiffOrderOn g Ω m) :
    VectorContDiffOrderOn (f + g) Ω m := by
  induction m generalizing f g with
  | zero =>
    unfold VectorContDiffOrderOn at hf hg ⊢
    refine (hf.add hg).subset ?_
    rintro z ⟨x, hx, y, hy, hxy, hd, rfl⟩
    refine ⟨_, ⟨x, hx, y, hy, hxy, hd, rfl⟩, _, ⟨x, hx, y, hy, hxy, hd, rfl⟩, ?_⟩
    simp only [Pi.add_apply, ← smul_add]
    congr 1
    abel
  | succ m ih =>
    intro i
    obtain ⟨gf, hgf, cf, of⟩ := hf i
    obtain ⟨gg, hgg, cg, og⟩ := hg i
    refine ⟨gf + gg, ?_, cf.add cg, ih of og⟩
    intro φ x
    simp only [Pi.add_apply, map_add]
    convert ((hgf φ x).hasFDerivWithinAt.add (hgg φ x).hasFDerivWithinAt).hasDerivWithinAt
      using 1
    simp
    rfl

/-- Paper: Definition C.5.1.23, p. 734. The order condition is preserved by complex
scalar multiplication. -/
theorem VectorContDiffOrderOn.smul {Ω : Set V} {m : ℕ} {f : V → E}
    (c : ℂ) (hf : VectorContDiffOrderOn f Ω m) : VectorContDiffOrderOn (c • f) Ω m := by
  induction m generalizing f with
  | zero =>
    unfold VectorContDiffOrderOn at hf ⊢
    refine (hf.image (c • ContinuousLinearMap.id ℂ E)).subset ?_
    rintro z ⟨x, hx, y, hy, hxy, hd, rfl⟩
    refine ⟨_, ⟨x, hx, y, hy, hxy, hd, rfl⟩, ?_⟩
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply,
      ← smul_sub]
    exact smul_comm _ _ _
  | succ m ih =>
    intro i
    obtain ⟨gf, hgf, cf, of⟩ := hf i
    refine ⟨c • gf, ?_, cf.const_smul c, ih of⟩
    intro φ x
    simp only [Pi.smul_apply, map_smul]
    convert ((hgf φ x).hasFDerivWithinAt.const_smul c).hasDerivWithinAt using 1
    simp
    rfl

/-- Paper: Definition C.5.1.23, p. 734. The order condition defines a submodule of
ambient functions. Restriction of this submodule gives the space on the open set. -/
def vectorContDiffOrderSubmodule (Ω : Set V) (m : ℕ) : Submodule ℂ (V → E) where
  carrier := { f | VectorContDiffOrderOn f Ω m }
  zero_mem' := vectorContDiffOrderOn_zero Ω m
  add_mem' := VectorContDiffOrderOn.add
  smul_mem' := fun c _ hf ↦ VectorContDiffOrderOn.smul c hf

/-- Paper: Definition C.5.1.23, p. 734. The order-m space consists of the restrictions
of ambient maps with the order-m property on the open set. -/
def vectorContDiffOrderSpace (Ω : Set V) (m : ℕ) : Submodule ℂ (Ω → E) :=
  (vectorContDiffOrderSubmodule (E := E) Ω m).map (LinearMap.pi fun x : Ω ↦ LinearMap.proj (x : V))

/-- Paper: Definition C.5.1.23, p. 734. The smooth space is the intersection
of the order-m spaces for all natural numbers m. -/
def vectorSmoothSpace (Ω : Set V) : Submodule ℂ (Ω → E) :=
  ⨅ m : ℕ, vectorContDiffOrderSpace (E := E) Ω m

/-- Paper: Definition C.5.1.23, p. 734. Constant vector-valued functions are smooth. -/
theorem vectorSmoothOn_const (Ω : Set V) (z : E) :
    VectorSmoothOn (fun _ : V ↦ z) Ω := by
  have key : ∀ (m : ℕ) (z : E), VectorContDiffOrderOn (fun _ : V ↦ z) Ω m := by
    intro m
    induction m with
    | zero =>
      intro z
      show IsVonNBounded ℂ _
      refine (Bornology.isVonNBounded_singleton (0 : E)).subset ?_
      rintro w ⟨x, -, y, -, -, -, rfl⟩
      simp
    | succ m ih =>
      intro z i
      refine ⟨fun _ ↦ 0, ?_, continuousOn_const, ih 0⟩
      intro φ x
      simp only [map_zero]
      exact hasDerivWithinAt_const _ _ _
  exact fun m ↦ key m z

/-- Paper: Definition C.5.1.23, p. 734. Restricting a constant map gives a member of
the smooth submodule and of every finite-order submodule. -/
theorem const_mem_vectorSmoothSpace (Ω : Set V) (z : E) :
    (fun _ : Ω ↦ z) ∈ vectorSmoothSpace Ω ∧
      ∀ m : ℕ, (fun _ : Ω ↦ z) ∈ vectorContDiffOrderSpace Ω m ∧
        (fun _ : V ↦ z) ∈ vectorContDiffOrderSubmodule Ω m := by sorry

-- TODO(paper-gap): C.5.1.24 is false with the global bound at order zero.
-- On ℝ, x ↦ x² is weakly C¹ even under the recursive scalar reading, and fails order zero.

-- TODO(paper-gap): In C.5.1.25, the prose identifies scalar smoothness with the usual
-- concept. Under that reading x ↦ x² on ℝ disproves the reverse implication.

/-- Paper: Corollary C.5.1.25, p. 734. In a quasi-complete space, the all-order
condition is equivalent to the same all-order condition on every scalar evaluation.
Deviation: The scalar side uses Definition C.5.1.23, including its order-zero
boundedness condition. Ordinary scalar smoothness alone does not suffice. -/
theorem vectorSmoothOn_iff_scalar {Ω : Set V} (hΩ : IsOpen Ω) (hd : 1 ≤ d) (f : V → E) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      (VectorSmoothOn f Ω ↔ ∀ φ : StrongDual ℂ E, VectorSmoothOn (φ ∘ f) Ω) := by sorry

end HigherDifferentiability

-- TODO(paper-gap): Definition C.5.1.26 specifies uniform convergence of values, while
-- Remark C.5.1.28 uses derivatives and polynomial weights. These topologies differ even
-- for E = ℂ, and Theorem C.5.1.30(1–3) fails for the printed uniform topology.
-- This pass ends at §C.5.1.4. See the issue report for §C.5.1.5 and its counterexamples.

end RiemannMasullo
