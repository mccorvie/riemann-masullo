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
    (show Module.Dual ℂ (StrongDual ℂ E) from toPettisWeakCompletion E x) φ = φ x := by sorry

variable {E}
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.4.1.1, p. 709. The canonical weak-completion map embeds
the weak topology on the source into the topology of pointwise convergence. -/
theorem isEmbedding_toPettisWeakCompletion :
    IsEmbedding (fun x : WeakSpace ℂ E ↦ toPettisWeakCompletion E ((toWeakSpace ℂ E).symm x)) :=
  by sorry

/-- Paper: Lemma C.4.1.1(1), p. 709. The canonical map into the weak
completion is also continuous for the given topology on the source. -/
theorem continuous_toPettisWeakCompletion :
    Continuous (toPettisWeakCompletion E) := by sorry

variable [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]

/-- Paper: Lemma C.4.1.1(2), p. 709. Precomposition by a continuous linear map
is continuous between the continuous duals with their weak-star topologies. -/
theorem continuous_weakDual_precomp (T : E →L[ℂ] F) :
    Continuous (fun φ : WeakDual ℂ F ↦
      StrongDual.toWeakDual ((WeakDual.toStrongDual φ).comp T)) := by sorry

-- TODO(paper-gap): The pointwise topology on the target tests against E₂′.

/-- Paper: Lemma C.4.1.1(2), p. 709. The algebraic transpose of precomposition
by a continuous linear map is continuous between the weak completions.
Deviation: The target pointwise topology uses the continuous dual of the target. -/
theorem continuous_weakCompletion_transpose (T : E →L[ℂ] F) :
    Continuous (fun a : PettisWeakCompletion E ↦
      (show PettisWeakCompletion F from
        a.comp (ContinuousLinearMap.precomp ℂ T : StrongDual ℂ F →L[ℂ] StrongDual ℂ E).toLinearMap)) := by sorry

/-- Paper: Lemma C.4.1.1(2), p. 709. Evaluation intertwines a continuous
linear map with the algebraic transpose of its continuous dual map. -/
theorem toPettisWeakCompletion_natural (T : E →L[ℂ] F) (x : E) :
    toPettisWeakCompletion F (T x) =
      (show PettisWeakCompletion F from
        (toPettisWeakCompletion E x).comp
          (ContinuousLinearMap.precomp ℂ T : StrongDual ℂ F →L[ℂ] StrongDual ℂ E).toLinearMap) := by sorry

/-- Paper: Lemma C.4.1.2, p. 710. Completing the weak space gives the
pointwise-topologized algebraic dual, compatibly with the canonical map. -/
theorem completion_weakSpace_eq_pettisWeakCompletion :
    letI := IsTopologicalAddGroup.rightUniformSpace (WeakSpace ℂ E)
    haveI : IsUniformAddGroup (WeakSpace ℂ E) := isUniformAddGroup_of_addCommGroup
    ∃ e : Completion (WeakSpace ℂ E) ≃L[ℂ] PettisWeakCompletion E,
      ∀ x : E, e (toWeakSpace ℂ E x) = toPettisWeakCompletion E x := by sorry

-- The first closure assertion of C.4.1.2(1) is Mathlib's Convex.toWeakSpace_closure.

/-- Paper: Lemma C.4.1.2(1), p. 710. If the closure of a convex set in the
given topology is compact, its image is the closure in the weak completion. -/
theorem image_closure_eq_closure_weakCompletion {s : Set E} (hs : Convex ℝ s)
    (hc : IsCompact (closure s)) :
    toPettisWeakCompletion E '' closure s = closure (toPettisWeakCompletion E '' s) := by sorry

/-- Paper: Lemma C.4.1.2(2), p. 710. Evaluation into the weak completion of a
normed space factors through Mathlib's isometric inclusion into the normed bidual. -/
theorem toPettisWeakCompletion_eq_inclusionInDoubleDual {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℂ B] (x : B) :
    toPettisWeakCompletion B x =
      (show PettisWeakCompletion B from
        (NormedSpace.inclusionInDoubleDualLi (E := B) ℂ x).toLinearMap) := by sorry

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
      μ.scalarIntegral f = c * f x := by sorry

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
      c • μ.scalarIntegral (fun x ↦ φ (f x)) := by sorry

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
      μ.scalarIntegral (fun x ↦ φ (f x)) := by sorry

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
    HasPettisIntegral μ f (pettisIntegral μ f hf) := by sorry

/-- Paper: Definition C.4.2.1(3), p. 710. The representing vector is unique
in a Hausdorff locally convex space. -/
theorem HasPettisIntegral.unique
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    {μ : PettisMeasure X} {f : X → E} {a b : E}
    (ha : HasPettisIntegral μ f a) (hb : HasPettisIntegral μ f b) :
    a = b := by sorry

/-- Paper: Definition C.4.2.1(1), p. 710. For complex-valued functions on a
positive measure space, weak measurability is scalar almost-everywhere measurability.
Deviation: This is a sanity check for the definition. -/
theorem pettisWeaklyMeasurable_complex_iff (μ : Measure X) (f : X → ℂ) :
    PettisWeaklyMeasurable (.positive μ) f ↔ AEMeasurable f μ := by sorry

/-- Paper: Definition C.4.2.1(2)–(3), p. 710. The weak and Pettis constructions
specialize to scalar integrability and scalar integration for complex-valued functions.
Deviation: This is a sanity check for the definitions. -/
theorem pettisIntegral_complex_iff (μ : PettisMeasure X) (f : X → ℂ) (a : ℂ) :
    (PettisWeaklyIntegrable μ f ↔ Integrable f μ.variation) ∧
      (PettisIntegrable μ f ↔ Integrable f μ.variation) ∧
      (HasPettisIntegral μ f a ↔ Integrable f μ.variation ∧ a = μ.scalarIntegral f) := by sorry

/-- Paper: Remark C.4.2.2, p. 710. The Bochner integral of an integrable
Banach-space-valued function is also its Pettis integral. -/
theorem Integrable.hasPettisIntegral {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B] {μ : Measure X} {f : X → B}
    (hf : Integrable f μ) : HasPettisIntegral (.positive μ) f (∫ x, f x ∂μ) := by sorry

-- TODO(paper-gap): The converse in Remark C.4.2.2 (p. 711) fails even on
-- discrete ℕ with finite measure and values in ℓ². See the issue report.

end Integrals

section Criteria

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.4.3.1, p. 711. The weak integral lies in the closed
absolutely convex hull of the image, scaled by the total variation mass.
Deviation: The hull includes zero for the empty domain, as in the bipolar convention. -/
theorem pettisWeakIntegral_mem_smul_closedAbsConvexHull
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hi : PettisWeaklyIntegrable (.complex μ) f) :
    pettisWeakIntegral (.complex μ) f hi ∈
      (μ.variation univ).toReal •
        closure (convexHull ℝ (balancedHull ℂ (insert 0 (range (toPettisWeakCompletion E ∘ f))))) := by sorry

/-- Paper: Theorem C.4.3.2(1), p. 712. The closed convex hull of the image in
the weak completion consists of the weak integrals against Radon probability measures. -/
theorem closedConvexHull_eq_pettisWeakIntegrals_probability [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    let hull := closedConvexHull ℝ (range (toPettisWeakCompletion E ∘ f))
    hull = {a | ∃ μ : Measure X, μ.Regular ∧ μ univ = 1 ∧
      ∃ hi : PettisWeaklyIntegrable (.positive μ) f,
        pettisWeakIntegral (.positive μ) f hi = a} := by sorry

/-- Paper: Theorem C.4.3.2(1), p. 712. The closed convex hull of the
image in the weak completion is compact. -/
theorem isCompact_closedConvexHull_weakCompletion_range [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    IsCompact (closedConvexHull ℝ (range (toPettisWeakCompletion E ∘ f))) := by sorry

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

/-- Paper: Theorem C.4.3.2(2), p. 712. The closed absolutely convex hull of the
image in the weak completion is compact.
Deviation: The hull includes zero for the empty domain, as in the bipolar convention. -/
theorem isCompact_closedAbsConvexHull_weakCompletion_range [CompactSpace X]
    (f : X → E) (hf : Continuous f) :
    IsCompact (closure (convexHull ℝ
      (balancedHull ℂ (insert 0 (range (toPettisWeakCompletion E ∘ f)))))) := by sorry

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
    QuasiCompleteSpace ℂ E → PettisIntegrable (.complex μ) f := by sorry

/-- Paper: Lemma C.4.3.7, p. 714. A weakly integrable function with values
in a reflexive Banach space is Pettis integrable. -/
theorem pettisIntegrable_of_reflexive
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (hB : Surjective (NormedSpace.inclusionInDoubleDual ℂ B))
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → B) (hf : PettisWeaklyIntegrable (.complex μ) f) :
    PettisIntegrable (.complex μ) f := by sorry

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
  by sorry

/-- Paper: Lemma C.4.3.8, p. 714. A continuous linear map takes a Pettis
integral to the Pettis integral of the composed function. -/
theorem HasPettisIntegral.comp_continuousLinearMap
    {μ : ComplexMeasure X} [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    {f : X → E} {a : E} (hf : HasPettisIntegral (.complex μ) f a) (T : E →L[ℂ] F) :
    HasPettisIntegral (.complex μ) (T ∘ f) (T a) := by sorry

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
    ∃ A : H →L[ℂ] H, ∀ u, HasPettisIntegral (.complex μ) (fun x ↦ f x u) (A u) := by sorry

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
