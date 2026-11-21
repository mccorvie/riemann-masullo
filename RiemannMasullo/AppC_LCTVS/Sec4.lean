module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Star
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Integration in the sense of Pettis

Masullo, Appendix C, §C.4. We use the continuous-seminorm formulation of local convexity
from §C.1. The complex absolutely convex hull is the real convex hull of the complex balanced hull.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped Pointwise ENNReal

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section WeakCompletion

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: Remark C.4.1.3, p. 710. The algebraic dual of the continuous dual
carries the topology of pointwise convergence on the continuous dual. -/
abbrev PettisWeakCompletion :=
  WeakBilin (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ]
    Module.Dual ℂ (StrongDual ℂ E))

/-- Paper: (C.4.1.1), p. 709. The canonical map into the weak completion
takes each vector to evaluation at that vector. -/
def toPettisWeakCompletion : E →ₗ[ℂ] PettisWeakCompletion E :=
  (topDualPairing ℂ E).flip

/-- Paper: (C.4.1.1), p. 709. Evaluating the image of a vector at a
continuous functional returns that functional's value on the vector. -/
theorem toPettisWeakCompletion_apply (x : E) (φ : StrongDual ℂ E) :
    (show Module.Dual ℂ (StrongDual ℂ E) from toPettisWeakCompletion E x) φ = φ x := by
  rfl

variable {E}
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.4.1.1, p. 709. The canonical weak-completion map embeds
the weak topology on the source into the topology of pointwise convergence. -/
theorem isEmbedding_toPettisWeakCompletion :
    IsEmbedding (fun x : WeakSpace ℂ E ↦ toPettisWeakCompletion E ((toWeakSpace ℂ E).symm x)) := by
  letI := polynormableSpace_separatingDual ℂ E
  exact IsInducing.isEmbedding ⟨induced_compose.symm⟩

/-- Paper: Lemma C.4.1.1(1), p. 709. The canonical map into the weak
completion is also continuous for the given topology on the source. -/
theorem continuous_toPettisWeakCompletion :
    Continuous (toPettisWeakCompletion E) := by
  exact WeakBilin.continuous_of_continuous_eval _ fun φ ↦ φ.continuous

variable [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: Lemma C.4.1.1(2), p. 709. Precomposition by a continuous linear map
is continuous between the continuous duals with their weak-star topologies. -/
theorem continuous_weakDual_precomp (T : E →L[ℂ] F) :
    Continuous (fun φ : WeakDual ℂ F ↦
      StrongDual.toWeakDual ((WeakDual.toStrongDual φ).comp T)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro x
  exact WeakDual.eval_continuous (T x)

-- TODO(paper-gap): The pointwise topology on the target tests against E₂′.

/-- Paper: Lemma C.4.1.1(2), p. 709. The algebraic transpose of precomposition
by a continuous linear map is continuous between the weak completions.
Deviation: The target pointwise topology uses the continuous dual of the target. -/
theorem continuous_weakCompletion_transpose (T : E →L[ℂ] F) :
    Continuous (fun a : PettisWeakCompletion E ↦
      (show PettisWeakCompletion F from
        a.comp (ContinuousLinearMap.precomp ℂ T : StrongDual ℂ F →L[ℂ] StrongDual ℂ E).toLinearMap)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro φ
  exact WeakBilin.eval_continuous (B := LinearMap.id) ((ContinuousLinearMap.precomp ℂ T :
    StrongDual ℂ F →L[ℂ] StrongDual ℂ E) φ)

/-- Paper: Lemma C.4.1.1(2), p. 709. Evaluation intertwines a continuous
linear map with the algebraic transpose of its continuous dual map. -/
theorem toPettisWeakCompletion_natural (T : E →L[ℂ] F) (x : E) :
    toPettisWeakCompletion F (T x) =
      (show PettisWeakCompletion F from
        (toPettisWeakCompletion E x).comp
          (ContinuousLinearMap.precomp ℂ T : StrongDual ℂ F →L[ℂ] StrongDual ℂ E).toLinearMap) := by
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] in
/-- Paper: Lemma C.4.1.2, p. 710. Evaluations at vectors are dense in the pointwise topology
on the algebraic dual of the continuous dual. -/
private theorem denseRange_toPettisWeakCompletion : DenseRange (toPettisWeakCompletion E) := by
  classical
  intro a
  -- Evaluation realizes the prescribed values on each finite span of functionals.
  have matchFinite (s : Finset (StrongDual ℂ E)) :
      ∃ x : E, ∀ φ ∈ s, φ x = (show Module.Dual ℂ (StrongDual ℂ E) from a) φ := by
    let W := Submodule.span ℂ (s : Set (StrongDual ℂ E))
    let : AddCommGroup W := inferInstance
    let F : E →ₗ[ℂ] Module.Dual ℂ W := W.subtype.dualMap.comp (toPettisWeakCompletion E)
    have hF : Injective F.flip := by
      intro φ ψ h
      apply Subtype.ext
      exact ContinuousLinearMap.ext fun x ↦ LinearMap.congr_fun h x
    have hsurj : Surjective F := (LinearMap.flip_injective_iff₂ (B := F)).mp hF
    obtain ⟨x, hx⟩ := hsurj (W.subtype.dualMap a)
    exact ⟨x, fun φ hφ ↦ LinearMap.congr_fun hx ⟨φ, Submodule.subset_span hφ⟩⟩
  choose x hx using matchFinite
  apply mem_closure_of_tendsto (f := fun s ↦ toPettisWeakCompletion E (x s)) (b := atTop)
  · apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).2
    intro φ
    exact tendsto_atTop_of_eventually_const (i₀ := {φ}) fun s hs ↦
      hx s φ (Finset.singleton_subset_iff.mp hs)
  · exact Eventually.of_forall fun s ↦ mem_range_self (x s)

/-- Paper: Lemma C.4.1.2, p. 710. Completing the weak space gives the
pointwise-topologized algebraic dual, compatibly with the canonical map. -/
theorem completion_weakSpace_eq_pettisWeakCompletion :
    letI := IsTopologicalAddGroup.rightUniformSpace (WeakSpace ℂ E)
    haveI : IsUniformAddGroup (WeakSpace ℂ E) := isUniformAddGroup_of_addCommGroup
    ∃ e : Completion (WeakSpace ℂ E) ≃L[ℂ] PettisWeakCompletion E,
      ∀ x : E, e (toWeakSpace ℂ E x) = toPettisWeakCompletion E x := by
  let := IsTopologicalAddGroup.rightUniformSpace (WeakSpace ℂ E)
  let := isUniformAddGroup_of_addCommGroup (G := WeakSpace ℂ E)
  let := IsTopologicalAddGroup.rightUniformSpace (PettisWeakCompletion E)
  let := isUniformAddGroup_of_addCommGroup (G := PettisWeakCompletion E)
  -- The algebraic dual is closed in the complete product of scalar coordinate spaces.
  let eval : PettisWeakCompletion E →+ (StrongDual ℂ E → ℂ) :=
    ⟨⟨fun a φ ↦ (show Module.Dual ℂ (StrongDual ℂ E) from a) φ, rfl⟩, fun _ _ ↦ rfl⟩
  have hev : IsUniformInducing eval := AddMonoidHom.isUniformInducing_of_isInducing ⟨rfl⟩
  let : CompleteSpace (PettisWeakCompletion E) :=
    hev.completeSpace (LinearMap.isClosed_range_coe _ _ _).isComplete
  let : T2Space (PettisWeakCompletion E) :=
    (WeakBilin.isEmbedding (B := LinearMap.id) injective_id).t2Space
  -- Extend evaluation. Its range is dense and complete, hence it is surjective.
  let jLin := (toPettisWeakCompletion E).comp (toWeakSpace ℂ E).symm.toLinearMap
  have hj : IsInducing jLin := ⟨induced_compose.symm⟩
  let j : WeakSpace ℂ E →L[ℂ] PettisWeakCompletion E := ⟨jLin, hj.continuous⟩
  have hi : IsUniformInducing j := AddMonoidHom.isUniformInducing_of_isInducing hj
  have he : IsUniformInducing j.fromCompletion := Completion.isUniformInducing_extension hi
  have hr : DenseRange j.fromCompletion := by
    apply Dense.mono _ denseRange_toPettisWeakCompletion
    rintro _ ⟨x, rfl⟩
    exact ⟨(toWeakSpace ℂ E x : Completion (WeakSpace ℂ E)), j.fromCompletion_apply_coe _⟩
  have hs : Surjective j.fromCompletion := by
    rw [← range_eq_univ, ← he.isComplete_range.isClosed.closure_eq, hr.closure_range]
  have hh : IsHomeomorph j.fromCompletion :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨he.isUniformEmbedding.isEmbedding, hs⟩
  exact ⟨.ofIsHomeomorph (.ofBijective j.fromCompletion.toLinearMap hh.bijective) hh,
    fun x ↦ j.fromCompletion_apply_coe (toWeakSpace ℂ E x)⟩

-- The first closure assertion of C.4.1.2(1) is Mathlib's Convex.toWeakSpace_closure.

/-- Paper: Lemma C.4.1.2(1), p. 710. If the closure of a convex set in the
given topology is compact, its image is the closure in the weak completion. -/
theorem image_closure_eq_closure_weakCompletion {s : Set E} (hs : Convex ℝ s)
    (hc : IsCompact (closure s)) :
    toPettisWeakCompletion E '' closure s = closure (toPettisWeakCompletion E '' s) := by
  haveI : T2Space (PettisWeakCompletion E) :=
    (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ] _))
      Function.injective_id).t2Space
  exact image_closure_of_isCompact hc
    (continuous_toPettisWeakCompletion (E := E)).continuousOn

/-- Paper: Lemma C.4.1.2(2), p. 710. Evaluation into the weak completion of a
normed space factors through Mathlib's isometric inclusion into the normed bidual. -/
theorem toPettisWeakCompletion_eq_inclusionInDoubleDual {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℂ B] (x : B) :
    toPettisWeakCompletion B x =
      (show PettisWeakCompletion B from
        (NormedSpace.inclusionInDoubleDualLi (E := B) ℂ x).toLinearMap) := by
  rfl

end WeakCompletion

section Integrals

variable {X : Type*} [MeasurableSpace X]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Definition C.4.2.1, p. 710. The scalar integrals can use a positive
measure or a finite complex measure.
Deviation: The two Mathlib measure types are accepted by separate constructors. -/
inductive PettisMeasure (X : Type*) [MeasurableSpace X] where
  | positive (μ : Measure X)
  | complex (μ : ComplexMeasure X)

/-- Paper: Definition C.4.2.1, p. 710. Measurability and absolute
integrability use the positive measure or the variation of the complex measure. -/
def PettisMeasure.variation : PettisMeasure X → Measure X
  | .positive μ => μ
  | .complex μ => μ.variation

/-- Paper: (C.4.2.1), p. 710. Scalar integration uses the Bochner integral
for positive measures and the vector-measure integral with complex multiplication
for complex measures. -/
def PettisMeasure.scalarIntegral (μ : PettisMeasure X) (f : X → ℂ) : ℂ :=
  match μ with
  | .positive ν => ∫ x, f x ∂ν
  | .complex ν => ν.integral f (ContinuousLinearMap.mul ℝ ℂ)

/-- Paper: Definition C.4.2.1, p. 710. For a complex point mass the variation
is the point mass weighted by the modulus, while the integral uses the complex weight.
Deviation: This is a sanity check for the measure representation. -/
theorem pettisMeasure_complex_dirac [MeasurableSingletonClass X] (x : X) (c : ℂ) (f : X → ℂ) :
    let μ : PettisMeasure X := .complex (VectorMeasure.dirac x c)
    μ.variation = ENNReal.ofReal ‖c‖ • Measure.dirac x ∧
      μ.scalarIntegral f = c * f x := by
  refine ⟨?_, ?_⟩
  · change (VectorMeasure.dirac x c).variation = _
    rw [VectorMeasure.variation_dirac, ofReal_norm]
  · change (VectorMeasure.dirac x c).integral f (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [VectorMeasure.integral_dirac]
    simp [mul_comm]

/-- Paper: Definition C.4.2.1(1), p. 710. A function is weakly measurable
when every continuous linear functional gives a scalar measurable function.
Deviation: Almost-everywhere measurability on the Borel space represents measurability
for the completed measure. -/
def PettisWeaklyMeasurable (μ : PettisMeasure X) (f : X → E) : Prop :=
  ∀ φ : StrongDual ℂ E, AEMeasurable (fun x ↦ φ (f x)) μ.variation

/-- Paper: Definition C.4.2.1(2), p. 710. A function is weakly integrable when
every continuous linear functional gives an integrable scalar function. -/
def PettisWeaklyIntegrable (μ : PettisMeasure X) (f : X → E) : Prop :=
  ∀ φ : StrongDual ℂ E, Integrable (fun x ↦ φ (f x)) μ.variation

/-- Paper: (C.4.2.1), p. 710. The scalar integrals of a weakly integrable
function are additive in the continuous functional. -/
theorem pettisScalarIntegral_add (μ : PettisMeasure X) (f : X → E)
    (hf : PettisWeaklyIntegrable μ f) (φ ψ : StrongDual ℂ E) :
    μ.scalarIntegral (fun x ↦ (φ + ψ) (f x)) =
      μ.scalarIntegral (fun x ↦ φ (f x)) + μ.scalarIntegral (fun x ↦ ψ (f x)) := by
  cases μ with
  | positive ν => exact integral_add (hf φ) (hf ψ)
  | complex ν => exact VectorMeasure.integral_fun_add (hf φ) (hf ψ)

/-- Paper: (C.4.2.1), p. 710. The scalar integrals of a weakly integrable
function are complex homogeneous in the continuous functional. -/
theorem pettisScalarIntegral_smul (μ : PettisMeasure X) (f : X → E)
    (hf : PettisWeaklyIntegrable μ f) (c : ℂ) (φ : StrongDual ℂ E) :
    μ.scalarIntegral (fun x ↦ (c • φ) (f x)) =
      c • μ.scalarIntegral (fun x ↦ φ (f x)) := by
  cases μ with
  | positive ν => exact integral_smul c (fun x ↦ φ (f x))
  | complex ν =>
    simp only [PettisMeasure.scalarIntegral, VectorMeasure.integral_eq_setToFun]
    apply setToFun_smul _ _ c (fun x ↦ φ (f x))
    intro a s z
    simp [VectorMeasure.transpose, mul_left_comm]

/-- Paper: (C.4.2.1), p. 710. The weak integral is the algebraic linear
functional on the continuous dual obtained by scalar integration. -/
def pettisWeakIntegral (μ : PettisMeasure X) (f : X → E)
    (hf : PettisWeaklyIntegrable μ f) : PettisWeakCompletion E :=
  (show Module.Dual ℂ (StrongDual ℂ E) from
    { toFun := fun φ ↦ μ.scalarIntegral (fun x ↦ φ (f x))
      map_add' := pettisScalarIntegral_add μ f hf
      map_smul' := pettisScalarIntegral_smul μ f hf })

/-- Paper: (C.4.2.1), p. 710. Evaluating the weak integral gives the scalar
integral of the functional applied to the integrand. -/
theorem pettisWeakIntegral_apply (μ : PettisMeasure X) (f : X → E)
    (hf : PettisWeaklyIntegrable μ f) (φ : StrongDual ℂ E) :
    (show Module.Dual ℂ (StrongDual ℂ E) from pettisWeakIntegral μ f hf) φ =
      μ.scalarIntegral (fun x ↦ φ (f x)) := rfl

/-- Paper: Definition C.4.2.1(3), p. 710. A weakly integrable function has
Pettis integral `a` if evaluation at `a` represents its weak integral. -/
def HasPettisIntegral (μ : PettisMeasure X) (f : X → E) (a : E) : Prop :=
  ∃ hf : PettisWeaklyIntegrable μ f, toPettisWeakCompletion E a = pettisWeakIntegral μ f hf

/-- Paper: Definition C.4.2.1(3), p. 710. A function is Pettis integrable
if a vector represents its weak integral. -/
def PettisIntegrable (μ : PettisMeasure X) (f : X → E) : Prop :=
  ∃ a, HasPettisIntegral μ f a

/-- Paper: Definition C.4.2.1(3), p. 710. The Pettis integral is the
representing vector, defined for Pettis integrable functions. -/
def pettisIntegral (μ : PettisMeasure X) (f : X → E)
    (hf : PettisIntegrable μ f) : E :=
  Classical.choose hf

/-- Paper: Definition C.4.2.1(3), p. 710. The chosen Pettis integral
represents the weak integral. -/
theorem hasPettisIntegral_pettisIntegral (μ : PettisMeasure X) (f : X → E)
    (hf : PettisIntegrable μ f) :
    HasPettisIntegral μ f (pettisIntegral μ f hf) :=
  Classical.choose_spec hf

/-- Paper: Definition C.4.2.1(3), p. 710. The representing vector is unique
in a Hausdorff locally convex space. -/
theorem HasPettisIntegral.unique
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    {μ : PettisMeasure X} {f : X → E} {a b : E}
    (ha : HasPettisIntegral μ f a) (hb : HasPettisIntegral μ f b) :
    a = b := by
  obtain ⟨hf, ha⟩ := ha
  obtain ⟨_, hb⟩ := hb
  let := polynormableSpace_separatingDual ℂ E
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun φ ↦ ?_
  have h := ha.trans hb.symm
  exact congrArg (fun z : PettisWeakCompletion E ↦
    (show Module.Dual ℂ (StrongDual ℂ E) from z) φ) h

/-- Paper: Definition C.4.2.1(1), p. 710. For complex-valued functions on a
positive measure space, weak measurability is scalar almost-everywhere measurability.
Deviation: This is a sanity check for the definition. -/
theorem pettisWeaklyMeasurable_complex_iff (μ : Measure X) (f : X → ℂ) :
    PettisWeaklyMeasurable (.positive μ) f ↔ AEMeasurable f μ :=
  ⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), fun h φ ↦ φ.continuous.measurable.comp_aemeasurable h⟩

/-- Paper: Definition C.4.2.1(2)–(3), p. 710. The weak and Pettis constructions
specialize to scalar integrability and scalar integration for complex-valued functions.
Deviation: This is a sanity check for the definitions. -/
theorem pettisIntegral_complex_iff (μ : PettisMeasure X) (f : X → ℂ) (a : ℂ) :
    (PettisWeaklyIntegrable μ f ↔ Integrable f μ.variation) ∧
      (PettisIntegrable μ f ↔ Integrable f μ.variation) ∧
      (HasPettisIntegral μ f a ↔ Integrable f μ.variation ∧ a = μ.scalarIntegral f) := by
  have hW : PettisWeaklyIntegrable μ f ↔ Integrable f μ.variation :=
    ⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), fun h φ ↦ φ.integrable_comp h⟩
  have hφ (φ : StrongDual ℂ ℂ) (z : ℂ) : φ z = φ 1 * z := by
    have h := φ.map_smul z 1
    simp only [smul_eq_mul, mul_one] at h
    rw [h, mul_comm]
  have hS (hf : PettisWeaklyIntegrable μ f) (φ : StrongDual ℂ ℂ) :
      μ.scalarIntegral (fun x ↦ φ (f x)) = φ 1 * μ.scalarIntegral f := by
    have e : (fun x ↦ φ (f x)) = fun x ↦ (φ 1 • ContinuousLinearMap.id ℂ ℂ) (f x) := by
      funext x
      rw [hφ φ (f x)]
      simp
    rw [e, pettisScalarIntegral_smul μ f hf]
    rfl
  have hP (b : ℂ) :
      HasPettisIntegral μ f b ↔ Integrable f μ.variation ∧ b = μ.scalarIntegral f := by
    constructor
    · rintro ⟨hf, h⟩
      exact ⟨hW.1 hf, congrArg (fun z : PettisWeakCompletion ℂ ↦
        (show Module.Dual ℂ (StrongDual ℂ ℂ) from z) (ContinuousLinearMap.id ℂ ℂ)) h⟩
    · rintro ⟨hi, rfl⟩
      refine ⟨hW.2 hi, LinearMap.ext fun φ ↦ ?_⟩
      change φ (μ.scalarIntegral f) = μ.scalarIntegral (fun x ↦ φ (f x))
      rw [hS (hW.2 hi) φ, hφ φ]
  exact ⟨hW, ⟨fun ⟨b, h⟩ ↦ ((hP b).1 h).1, fun hi ↦ ⟨_, (hP _).2 ⟨hi, rfl⟩⟩⟩, hP a⟩

/-- Paper: Remark C.4.2.2, p. 710. The Bochner integral of an integrable
Banach-space-valued function is also its Pettis integral. -/
theorem Integrable.hasPettisIntegral {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B] {μ : Measure X} {f : X → B}
    (hf : Integrable f μ) : HasPettisIntegral (.positive μ) f (∫ x, f x ∂μ) := by
  refine ⟨fun φ ↦ φ.integrable_comp hf, ?_⟩
  refine LinearMap.ext fun φ ↦ ?_
  exact (φ.integral_comp_comm hf).symm

-- TODO(paper-gap): The converse in Remark C.4.2.2 (p. 711) fails even on
-- discrete ℕ with finite measure and values in ℓ². See the issue report.

end Integrals

section Criteria

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

open scoped ComplexOrder in
/-- Paper: Lemma C.4.3.1, p. 711. The weak integral lies in the closed
absolutely convex hull of the image, scaled by the total variation mass.
Deviation: The hull includes zero for the empty domain, as in the bipolar convention. -/
theorem pettisWeakIntegral_mem_smul_closedAbsConvexHull
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hi : PettisWeaklyIntegrable (.complex μ) f) :
    pettisWeakIntegral (.complex μ) f hi ∈
      (μ.variation univ).toReal •
        closure (convexHull ℝ (balancedHull ℂ (insert 0 (range (toPettisWeakCompletion E ∘ f))))) := by
  let D := StrongDual ℂ E
  let B : Module.Dual ℂ D →ₗ[ℂ] D →ₗ[ℂ] ℂ := .id
  let S := range (toPettisWeakCompletion E ∘ f)
  let C := closure (convexHull ℝ (balancedHull ℂ (insert 0 S)))
  let v := pettisWeakIntegral (.complex μ) f hi
  let d := (μ.variation univ).toReal
  have hB : B.Nondegenerate := LinearMap.Nondegenerate.id
  have hbip : B.flip.polar (B.polar S) = C := by
    -- Give both sides of the algebraic duality their weak topologies.
    let : TopologicalSpace (Module.Dual ℂ D) := inferInstanceAs (TopologicalSpace (WeakBilin B))
    let : TopologicalSpace D := inferInstanceAs (TopologicalSpace (WeakBilin B.flip))
    have : PolynormableSpace ℂ (Module.Dual ℂ D) := B.weakBilin_withSeminorms.toPolynormableSpace
    have : PolynormableSpace ℂ D := B.flip.weakBilin_withSeminorms.toPolynormableSpace
    have : T2Space (Module.Dual ℂ D) := (WeakBilin.isEmbedding (B := B) Function.injective_id).t2Space
    have : T2Space D := (WeakBilin.isEmbedding (LinearMap.ker_eq_bot.mp
      (LinearMap.separatingLeft_iff_ker_eq_bot.mp (LinearMap.flip_separatingLeft.mpr hB.2)))).t2Space
    rw [bipolar_eq_weakClosure_absConvexHull B hB S]
    congr 1
    refine (absConvexHull_eq_convexHull_balancedHull ℂ (s := insert 0 S)).trans ?_
    exact le_antisymm
      (convexHull_min (subset_convexHull ..) (convex_RCLike_iff_convex_real.2 (convex_convexHull ..)))
      (convexHull_min (subset_convexHull ..) ((convex_convexHull ℂ _).lift ℝ))
  have hzero : (0 : PettisWeakCompletion E) ∈ C :=
    subset_closure (subset_convexHull _ _ (subset_balancedHull _ (mem_insert _ _)))
  by_cases hz : μ.variation univ = 0
  · have hμ : μ = 0 := VectorMeasure.variation_eq_zero.mp (Measure.measure_univ_eq_zero.mp hz)
    subst μ
    have hv : v = 0 := by
      apply LinearMap.ext
      intro φ
      change (0 : ComplexMeasure X).integral (fun x ↦ φ (f x)) (ContinuousLinearMap.mul ℝ ℂ) = 0
      simp
    exact ⟨0, hzero, (smul_zero _).trans hv.symm⟩
  have hd : 0 < d := ENNReal.toReal_pos hz (measure_ne_top _ _)
  refine ⟨d⁻¹ • v, ?_, smul_inv_smul₀ hd.ne' _⟩
  change d⁻¹ • v ∈ C
  rw [← hbip]
  intro φ hφ
  change ‖d⁻¹ • μ.integral (fun x ↦ φ (f x)) (ContinuousLinearMap.mul ℝ ℂ)‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), inv_mul_le_iff₀ hd, mul_one]
  have h := VectorMeasure.norm_integral_le_of_norm_le_const (μ := μ)
    (B := ContinuousLinearMap.mul ℝ ℂ) (f := fun x ↦ φ (f x))
    (ae_of_all _ fun x ↦ show ‖φ (f x)‖ ≤ 1 from hφ _ ⟨x, rfl⟩)
  simpa [d, Measure.real] using h

/-- Paper: Theorem C.4.3.2(1), p. 712. The closed convex hull of the image in
the weak completion consists of the weak integrals against Radon probability measures. -/
theorem closedConvexHull_eq_pettisWeakIntegrals_probability [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    let hull := closedConvexHull ℝ (range (toPettisWeakCompletion E ∘ f))
    hull = {a | ∃ μ : Measure X, μ.Regular ∧ μ univ = 1 ∧
      ∃ hi : PettisWeaklyIntegrable (.positive μ) f,
        pettisWeakIntegral (.positive μ) f hi = a} := by
  let B : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ] Module.Dual ℂ (StrongDual ℂ E) := .id
  have : T2Space (PettisWeakCompletion E) :=
    (WeakBilin.isEmbedding (B := B) Function.injective_id).t2Space
  let g (φ : StrongDual ℂ E) : BoundedContinuousFunction X ℂ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x ↦ φ (f x), φ.continuous.comp hf⟩
  have hi (μ : Measure X) [IsFiniteMeasure μ] : PettisWeaklyIntegrable (.positive μ) f :=
    fun φ ↦ (g φ).integrable (μ := μ)
  let barycenter (p : ProbabilityMeasure X) : PettisWeakCompletion E :=
    pettisWeakIntegral (.positive (p : Measure X)) f (hi p)
  have hcont : Continuous barycenter := by
    apply WeakBilin.continuous_of_continuous_eval B
    intro φ
    rw [continuous_iff_continuousAt]
    intro p
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
      (tendsto_id (x := 𝓝 p)) (g φ)
  have hconv : Convex ℝ (range barycenter) := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ a b ha hb hab
    let μ := ENNReal.ofReal a • (p : Measure X)
    let ν := ENNReal.ofReal b • (q : Measure X)
    let r : ProbabilityMeasure X := ⟨μ + ν, ⟨by simp [μ, ν, ← ENNReal.ofReal_add ha hb, hab]⟩⟩
    refine ⟨r, LinearMap.ext fun φ ↦ ?_⟩
    change ∫ x, g φ x ∂(μ + ν) =
      a • (∫ x, g φ x ∂(p : Measure X)) + b • (∫ x, g φ x ∂(q : Measure X))
    have hp : Integrable (g φ) (p : Measure X) := hi p φ
    have hq : Integrable (g φ) (q : Measure X) := hi q φ
    rw [integral_add_measure (hp.smul_measure ENNReal.ofReal_ne_top)
      (hq.smul_measure ENNReal.ofReal_ne_top)]
    simp [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  have hsubset : range (toPettisWeakCompletion E ∘ f) ⊆ range barycenter := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩,
      LinearMap.ext fun φ ↦ integral_dirac (g φ) x⟩
  apply le_antisymm
  · intro a ha
    obtain ⟨p, rfl⟩ := closedConvexHull_min hsubset hconv (isCompact_range hcont).isClosed ha
    -- Use a regular representative of the probability measure with the same moments.
    obtain ⟨ν, hνreg, hνfin, hν⟩ := (p : Measure X).exists_regular_eq_of_compactSpace
    refine ⟨ν, hνreg, ?_, hi ν, LinearMap.ext fun φ ↦ ?_⟩
    · apply (ENNReal.toReal_eq_one_iff _).mp
      simpa [measureReal_def] using (hν (1 : BoundedContinuousFunction X ℝ)).symm
    · change (∫ x, g φ x ∂ν) = ∫ x, g φ x ∂(p : Measure X)
      apply Complex.ext
      · let gre := BoundedContinuousFunction.mkOfCompact
          ⟨fun x ↦ (g φ x).re, Complex.continuous_re.comp (g φ).continuous⟩
        exact (integral_re (hi ν φ)).symm.trans ((hν gre).symm.trans (integral_re (hi p φ)))
      · let gim := BoundedContinuousFunction.mkOfCompact
          ⟨fun x ↦ (g φ x).im, Complex.continuous_im.comp (g φ).continuous⟩
        exact (integral_im (hi ν φ)).symm.trans ((hν gim).symm.trans (integral_im (hi p φ)))
  · rintro _ ⟨μ, _, hμ, h, rfl⟩
    have : IsProbabilityMeasure μ := ⟨hμ⟩
    -- A separating functional would give a scalar bound violated by its own integral.
    by_contra hnot
    obtain ⟨l, r, hl, hr⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      convex_closedConvexHull isClosed_closedConvexHull hnot
    obtain ⟨φ, rfl⟩ := B.dualEmbedding_surjective l
    have hle : ∀ x, (φ (f x)).re ≤ r := fun x ↦
      (hl _ (subset_closedConvexHull (mem_range_self x))).le
    have hφi : Integrable (fun x ↦ φ (f x)) μ := h φ
    have hb := integral_mono hφi.re (integrable_const r) hle
    rw [integral_re hφi, integral_const, probReal_univ, one_smul] at hb
    change r < RCLike.re (∫ x, φ (f x) ∂μ) at hr
    exact hr.not_ge hb

/-- Paper: Theorem C.4.3.2(1), p. 712. The closed convex hull of the
image in the weak completion is compact. -/
theorem isCompact_closedConvexHull_weakCompletion_range [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    IsCompact (closedConvexHull ℝ (range (toPettisWeakCompletion E ∘ f))) := by
  let : UniformSpace (PettisWeakCompletion E) :=
    IsTopologicalAddGroup.rightUniformSpace (PettisWeakCompletion E)
  let : IsUniformAddGroup (PettisWeakCompletion E) := isUniformAddGroup_of_addCommGroup
  -- The algebraic dual is a closed subspace of the complete product of scalar spaces.
  let eval : PettisWeakCompletion E →+ (StrongDual ℂ E → ℂ) :=
    (LinearMap.ltoFun ℂ (StrongDual ℂ E) ℂ ℂ).toAddMonoidHom
  have hev : IsUniformInducing eval := AddMonoidHom.isUniformInducing_of_isInducing ⟨rfl⟩
  let : CompleteSpace (PettisWeakCompletion E) :=
    hev.completeSpace (LinearMap.isClosed_range_coe _ _ _).isComplete
  let : ContinuousSMul ℝ (PettisWeakCompletion E) := IsScalarTower.continuousSMul ℂ
  have hCompact := isCompact_range (continuous_toPettisWeakCompletion.comp hf)
  rw [closedConvexHull_eq_closure_convexHull]
  exact hCompact.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure

/-- Paper: Theorem C.4.3.2(2), p. 712. The closed absolutely convex hull of the
image in the weak completion consists of the weak integrals against complex
Radon measures of total variation at most one.
Deviation: The hull includes zero for the empty domain, as in the bipolar convention. -/
theorem closedAbsConvexHull_eq_pettisWeakIntegrals_unitBall [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    let hull := closure (convexHull ℝ (balancedHull ℂ (insert 0 (range (toPettisWeakCompletion E ∘ f)))))
    hull = {a | ∃ μ : ComplexMeasure X, μ.variation.Regular ∧ μ.variation univ ≤ 1 ∧
      ∃ hi : PettisWeaklyIntegrable (.complex μ) f,
        pettisWeakIntegral (.complex μ) f hi = a} := by sorry

set_option linter.unusedSectionVars false in
/-- Paper: Theorem C.4.3.2(2), p. 712. The closed absolutely convex hull of the
image in the weak completion is compact.
Deviation: The hull includes zero for the empty domain, as in the bipolar convention. -/
theorem isCompact_closedAbsConvexHull_weakCompletion_range [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    IsCompact (closure (convexHull ℝ
      (balancedHull ℂ (insert 0 (range (toPettisWeakCompletion E ∘ f)))))) := by
  let K := Metric.closedBall (0 : ℂ) 1 • insert 0 (range f)
  have hK : IsCompact K := (isCompact_closedBall _ _).smul_set ((isCompact_range hf).insert 0)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have hrange : range (toPettisWeakCompletion E ∘ (Subtype.val : K → E)) =
      balancedHull ℂ (insert 0 (range (toPettisWeakCompletion E ∘ f))) := by
    rw [range_comp, Subtype.range_coe]
    change (toPettisWeakCompletion E) '' image2 (· • ·) _ _ = _
    rw [image_image2_distrib_right (f' := (· • ·))
      (fun c x ↦ (toPettisWeakCompletion E).map_smul c x),
      image_insert_eq, (toPettisWeakCompletion E).map_zero, ← range_comp]
    ext z
    rw [mem_balancedHull_iff (𝕜 := ℂ) (E := PettisWeakCompletion E)]
    simp only [image2_smul, Set.mem_smul, Metric.mem_closedBall, dist_zero_right, mem_smul_set]
  let : ContinuousSMul ℝ (PettisWeakCompletion E) := IsScalarTower.continuousSMul ℂ
  rw [← hrange, ← closedConvexHull_eq_closure_convexHull]
  exact isCompact_closedConvexHull_weakCompletion_range Subtype.val continuous_subtype_val

-- TODO(paper-gap): The level comparison in Remark C.4.3.4 is a preorder.
-- Distinct vectors can lie at the same level.

-- TODO(paper-gap): In (C.4.3.3) the mass of the support needs to be taken
-- with respect to total variation. The integrability criterion still makes sense.

/-- Paper: Theorem C.4.3.5, p. 713. A continuous compactly supported function
into a quasi-complete space is Pettis integrable against a finite complex Radon measure. -/
theorem pettisIntegrable_of_continuous_hasCompactSupport
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hc : HasCompactSupport f) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → PettisIntegrable (.complex μ) f := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  intro hE
  have : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let L := toPettisWeakCompletion E
  have hL : Continuous L := continuous_toPettisWeakCompletion (E := E)
  have : T2Space (PettisWeakCompletion E) :=
    (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ] _))
      Function.injective_id).t2Space
  have hi : PettisWeaklyIntegrable (.complex μ) f := fun φ ↦
    show Integrable (fun x ↦ φ (f x)) μ.variation from
    (φ.continuous.comp hf).integrable_of_hasCompactSupport (hc.comp_left φ.map_zero)
  let K := Metric.closedBall (0 : ℂ) 1 • insert 0 (range f)
  let H := closure (convexHull ℝ K)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).smul_set ((hc.isCompact_range hf).insert 0)
  have hH : IsCompact H := isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ)
    hK.totallyBounded.convexHull
  have hconv : Convex ℝ (L '' H) := (convex_convexHull ℝ K).closure.linear_image (L.restrictScalars ℝ)
  have hsub : closure (convexHull ℝ (balancedHull ℂ (insert 0 (range (L ∘ f))))) ⊆ L '' H := by
    apply closure_minimal _ (hH.image hL).isClosed
    apply convexHull_min _ hconv
    intro z hz
    obtain ⟨r, hr, a, ha, rfl⟩ := mem_balancedHull_iff.mp hz
    have hA : insert 0 (range (L ∘ f)) ⊆ L '' insert 0 (range f) := by
      rintro _ (rfl | ⟨x, rfl⟩)
      · exact ⟨0, mem_insert _ _, L.map_zero⟩
      · exact ⟨f x, mem_insert_of_mem _ ⟨x, rfl⟩, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hA ha
    refine ⟨r • b, subset_closure (subset_convexHull _ _ ?_), L.map_smul _ _⟩
    exact ⟨r, by simpa using hr, b, hb, rfl⟩
  obtain ⟨v, hv, he⟩ := pettisWeakIntegral_mem_smul_closedAbsConvexHull μ f hf hi
  obtain ⟨u, _, rfl⟩ := hsub hv
  refine ⟨(μ.variation univ).toReal • u, hi, ?_⟩
  exact ((L.restrictScalars ℝ).map_smul _ _).trans he

/-- Paper: Lemma C.4.3.7, p. 714. A weakly integrable function with values
in a reflexive Banach space is Pettis integrable. -/
theorem pettisIntegrable_of_reflexive
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (hB : Surjective (NormedSpace.inclusionInDoubleDual ℂ B))
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → B) (hf : PettisWeaklyIntegrable (.complex μ) f) :
    PettisIntegrable (.complex μ) f := by
  -- Test each functional against f as an element of L¹ of the variation measure.
  let T : StrongDual ℂ B →ₗ[ℂ] Lp ℂ 1 μ.variation :=
    { toFun := fun φ ↦ (hf φ).toL1 _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hrep (φ : StrongDual ℂ B) : ⇑(T φ) =ᵐ[μ.variation] fun x ↦ φ (f x) :=
    (hf φ).coeFn_toL1
  have hT : Continuous T := by
    apply T.continuous_of_seq_closed_graph
    intro u φ y hu hy
    apply Lp.ext
    -- Pointwise convergence and L¹ convergence must yield the same limit in measure.
    have hpoint : TendstoInMeasure μ.variation (fun n x ↦ u n (f x)) atTop (fun x ↦ φ (f x)) := by
      apply tendstoInMeasure_of_tendsto_ae (μ := μ.variation)
        (fun n ↦ (hf (u n)).aestronglyMeasurable)
      exact Eventually.of_forall fun x ↦
        ((NormedSpace.inclusionInDoubleDual ℂ B (f x)).continuous.tendsto φ).comp hu
    have hlim := (tendstoInMeasure_of_tendsto_Lp hy).congr_left (fun n ↦ hrep (u n))
    exact (tendstoInMeasure_ae_unique hlim hpoint).trans (hrep φ).symm
  let L : Module.Dual ℂ (StrongDual ℂ B) := pettisWeakIntegral (.complex μ) f hf
  have hL : Continuous L := by
    apply ((VectorMeasure.continuous_integral (μ := μ)
      (B := ContinuousLinearMap.mul ℝ ℂ)).comp hT).congr
    intro φ
    exact VectorMeasure.integral_congr_ae (hrep φ)
  obtain ⟨b, hb⟩ := hB (⟨L, hL⟩ : StrongDual ℂ (StrongDual ℂ B))
  exact ⟨b, hf, congrArg ContinuousLinearMap.toLinearMap hb⟩

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: Lemma C.4.3.8, p. 714. A continuous linear map preserves weak
integrability, and its transposed continuous dual map transports the weak integral. -/
theorem pettisWeakIntegral_comp_continuousLinearMap
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : PettisWeaklyIntegrable (.complex μ) f) (T : E →L[ℂ] F) :
    ∃ hTf : PettisWeaklyIntegrable (.complex μ) (T ∘ f),
      pettisWeakIntegral (.complex μ) (T ∘ f) hTf =
        (show PettisWeakCompletion F from
          (pettisWeakIntegral (.complex μ) f hf).comp
            (ContinuousLinearMap.precomp ℂ T : StrongDual ℂ F →L[ℂ] StrongDual ℂ E).toLinearMap) :=
  ⟨fun φ ↦ hf (φ.comp T), rfl⟩

/-- Paper: Lemma C.4.3.8, p. 714. A continuous linear map takes a Pettis
integral to the Pettis integral of the composed function. -/
theorem HasPettisIntegral.comp_continuousLinearMap
    {μ : ComplexMeasure X} [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    {f : X → E} {a : E} (hf : HasPettisIntegral (.complex μ) f a) (T : E →L[ℂ] F) :
    HasPettisIntegral (.complex μ) (T ∘ f) (T a) := by
  obtain ⟨hf, h⟩ := hf
  refine ⟨fun φ ↦ hf (φ.comp T), LinearMap.ext fun φ ↦ ?_⟩
  exact congrArg (fun z : PettisWeakCompletion E ↦
    (show Module.Dual ℂ (StrongDual ℂ E) from z) (φ.comp T)) h

-- TODO(paper-gap): Lemma C.4.3.9 compares a nonnegative seminorm with an
-- integral against a complex measure. Even for a signed measure, f = 1 and
-- μ = -δ on a point give 1 ≤ -1. The bound needs the total variation measure.

/-- Paper: Lemma C.4.3.11, p. 715. An operator-valued function that is weakly
measurable on each vector and has integrable operator norm admits a bounded
operator whose values are the Pettis integrals on those vectors. The operator norm
is absolutely integrable with respect to the variation of the complex measure. -/
theorem exists_hasPettisIntegral_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → H →L[ℂ] H)
    (hf : ∀ u, PettisWeaklyMeasurable (.complex μ) (fun x ↦ f x u))
    (hnorm : Integrable (fun x ↦ ‖f x‖) μ.variation) :
    ∃ A : H →L[ℂ] H, ∀ u, HasPettisIntegral (.complex μ) (fun x ↦ f x u) (A u) := by
  have hpoint (u : H) (φ : StrongDual ℂ H) (x : X) :
      ‖φ (f x u)‖ ≤ (‖φ‖ * ‖u‖) * ‖f x‖ := calc
    ‖φ (f x u)‖ ≤ ‖φ‖ * ‖f x u‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (‖f x‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((f x).le_opNorm u) (norm_nonneg _)
    _ = _ := by ring
  have hi (u : H) : PettisWeaklyIntegrable (.complex μ) (fun x ↦ f x u) :=
    fun φ ↦ (hnorm.const_mul (‖φ‖ * ‖u‖)).mono' (hf u φ).aestronglyMeasurable
      (Eventually.of_forall (hpoint u φ))
  -- Use Riesz representation on the conjugate of a bidual functional.
  have hH : Surjective (NormedSpace.inclusionInDoubleDual ℂ H) := by
    intro l
    let d := InnerProductSpace.toDual ℂ H
    let g : StrongDual ℂ H := (starL ℂ (A := ℂ)).toContinuousLinearMap.comp
      (l.comp d.toLinearIsometry.toContinuousLinearMap)
    obtain ⟨z, hz⟩ := d.surjective g
    refine ⟨z, ContinuousLinearMap.ext fun φ ↦ ?_⟩
    obtain ⟨y, rfl⟩ := d.surjective φ
    change inner ℂ y z = l (d y)
    rw [← inner_conj_symm]
    change starRingEnd ℂ (d z y) = l (d y)
    rw [hz]
    change starRingEnd ℂ (starRingEnd ℂ (l (d y))) = l (d y)
    simp
  choose a ha using fun u ↦ pettisIntegrable_of_reflexive hH μ (fun x ↦ f x u) (hi u)
  have heval (u : H) (φ : StrongDual ℂ H) :
      φ (a u) = (PettisMeasure.complex μ).scalarIntegral (fun x ↦ φ (f x u)) := by
    obtain ⟨_, h⟩ := ha u
    exact congrArg (fun z : PettisWeakCompletion H ↦
      (show Module.Dual ℂ (StrongDual ℂ H) from z) φ) h
  let L : H →ₗ[ℂ] H :=
    { toFun := a
      map_add' := fun u v ↦ by
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
        intro φ
        simp only [map_add, heval]
        exact VectorMeasure.integral_fun_add (hi u φ) (hi v φ)
      map_smul' := fun c u ↦ by
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
        intro φ
        simp only [RingHom.id_apply, map_smul, heval]
        exact pettisScalarIntegral_smul (.complex μ) (fun x ↦ f x u) (hi u) c φ }
  -- Bound the representing vectors by integrating against the variation of μ.
  let C := ∫ x, ‖f x‖ ∂μ.variation
  have hC : 0 ≤ C := integral_nonneg fun x ↦ norm_nonneg _
  have hL (u : H) : ‖L u‖ ≤ C * ‖u‖ := by
    apply NormedSpace.norm_le_dual_bound (𝕜 := ℂ) _ (mul_nonneg hC (norm_nonneg _))
    intro φ
    change ‖φ (a u)‖ ≤ _
    rw [heval]
    change ‖μ.integral (fun x ↦ φ (f x u)) (ContinuousLinearMap.mul ℝ ℂ)‖ ≤ _
    calc
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ‖ * ∫ x, ‖φ (f x u)‖ ∂μ.variation :=
        VectorMeasure.norm_integral_le_integral_norm
      _ ≤ ∫ x, ‖φ (f x u)‖ ∂μ.variation :=
        mul_le_of_le_one_left (integral_nonneg fun x ↦ norm_nonneg _)
          (ContinuousLinearMap.opNorm_mul_le ℝ ℂ)
      _ ≤ ∫ x, (‖φ‖ * ‖u‖) * ‖f x‖ ∂μ.variation :=
        integral_mono (hi u φ).norm (hnorm.const_mul _) (hpoint u φ)
      _ = _ := by
        rw [integral_const_mul]
        ring
  exact ⟨L.mkContinuous C hL, ha⟩

-- TODO(paper-gap): The proof of C.4.3.12 uses |μ(X)| where a uniform estimate
-- needs |μ|(X). The integrability of each function is already assumed.

/-- Paper: Lemma C.4.3.12, p. 716. Uniform convergence of a net of continuous
Pettis integrable functions implies convergence of their Pettis integrals
against the fixed finite complex measure. -/
theorem tendsto_pettisIntegral_of_tendstoUniformly
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : ι → X → E) (g : X → E) (hf : ∀ i, Continuous (f i)) (hg : Continuous g)
    (hfi : ∀ i, PettisIntegrable (.complex μ) (f i))
    (hgi : PettisIntegrable (.complex μ) g) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    TendstoUniformly f g atTop →
      Tendsto (fun i ↦ pettisIntegral (.complex μ) (f i) (hfi i)) atTop
        (𝓝 (pettisIntegral (.complex μ) g hgi)) := by sorry

end Criteria

section Fubini

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

-- TODO(paper-gap): Footnote 20 assumes a product of complete measures is
-- complete on the product σ-algebra. In general the product needs completion.

/-- Paper: Lemma C.4.4.1, p. 717. Pettis integrable sections of a weakly
integrable function have weakly integrable outer integrals in either order.
Both iterated weak integrals agree with the product weak integral.
Deviation: Almost-everywhere scalar measurability incorporates completion, and the product
on X × Y is μ.prod ν, as in the hypothesis and proof. -/
theorem pettisWeakIntegral_prod
    (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]
    (f : X × Y → E) (hf : PettisWeaklyIntegrable (.positive (μ.prod ν)) f)
    (hx : ∀ x, PettisIntegrable (.positive ν) (fun y ↦ f (x, y)))
    (hy : ∀ y, PettisIntegrable (.positive μ) (fun x ↦ f (x, y))) :
    let fx := fun x ↦ pettisIntegral (.positive ν) (fun y ↦ f (x, y)) (hx x)
    let fy := fun y ↦ pettisIntegral (.positive μ) (fun x ↦ f (x, y)) (hy y)
    ∃ hfx : PettisWeaklyIntegrable (.positive μ) fx,
      ∃ hfy : PettisWeaklyIntegrable (.positive ν) fy,
        pettisWeakIntegral (.positive (μ.prod ν)) f hf =
          pettisWeakIntegral (.positive μ) fx hfx ∧
        pettisWeakIntegral (.positive (μ.prod ν)) f hf =
          pettisWeakIntegral (.positive ν) fy hfy := by sorry

-- TODO(paper-gap): The image asserted in Remark C.4.4.2 can also contain zero
-- from outside the support. Its compactness still follows by adjoining zero.

end Fubini

section Weil

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Subgroup G}

local instance pettisWeilQuotientMeasurableSpace : MeasurableSpace (G ⧸ H) := borel _

-- Theorem C.4.4.3 is weilQuotientMeasure_existsUnique and weilQuotientIntegral_L1
-- from §D.1.2, with the exceptional set in the L¹ formula measured on the quotient.

-- TODO(paper-gap): A quotient-null set of exceptional cosets can lift to a
-- set of infinite regular Haar measure on G in Theorem C.4.4.3.

-- TODO(paper-gap): Lemma C.4.4.4 fails for general regular Haar measures.
-- With G = D × ℝ for an uncountable discrete group D and H = D × {0},
-- a closed graph assigning each d a distinct point of a Lebesgue-null set
-- has infinite Haar measure on G but zero iterated integral of its indicator.
-- With σ-finiteness of the group measure the result is integrable_of_weilNormIntegral.

-- TODO(paper-gap): Footnote 21 leaves the convention on completion of Haar
-- measures open. Here scalar tests use almost-everywhere Borel measurability.

/-- Paper: Lemma C.4.4.5(1)–(2), p. 718. Pettis integrable coset sections of
a weakly integrable function descend to a unique weakly integrable quotient
function. Its weak integral equals the original weak integral. -/
theorem existsUnique_pettisWeakIntegral_weil
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    (hH : IsClosed (H : Set G)) {μG : Measure G} {μH : Measure H}
    {ν : Measure (G ⧸ H)} [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
    (hν : IsWeilQuotientMeasure H μG μH ν) (f : G → E)
    (hf : PettisWeaklyIntegrable (.positive μG) f)
    (hsec : ∀ g : G, PettisIntegrable (.positive μH) (fun h : H ↦ f (g * h))) :
    ∃! F : G ⧸ H → E,
      (∀ g : G, F (QuotientGroup.mk g) =
        pettisIntegral (.positive μH) (fun h : H ↦ f (g * h)) (hsec g)) ∧
      ∃ hF : PettisWeaklyIntegrable (.positive ν) F,
        pettisWeakIntegral (.positive μG) f hf = pettisWeakIntegral (.positive ν) F hF := by sorry

end Weil

end RiemannMasullo
