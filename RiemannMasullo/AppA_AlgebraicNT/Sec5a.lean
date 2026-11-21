module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Maximal averages on the real line and D-sequences

Masullo, §§A.5.1–A.5.2, pp. 566–578.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Pointwise

namespace RiemannMasullo

/-- Paper: (A.5.1.1), p. 566. Centered averages of a continuous real-valued function
converge to its value as the radius decreases to zero. -/
theorem tendsto_centeredAverage_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun r : ℝ ↦ (2 * r)⁻¹ * ∫ y in x - r..x + r, f y)
      (𝓝[>] 0) (𝓝 (f x)) := by
  have hradius : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hleft : Tendsto (fun r : ℝ ↦ x - r) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub hradius
  have hright : Tendsto (fun r : ℝ ↦ x + r) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add hradius
  have herror := intervalIntegral.integral_sub_linear_isLittleO_of_tendsto_ae
    (l' := 𝓝 x) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hf.continuousAt.tendsto.mono_left inf_le_left) hleft hright
  have hlength (r : ℝ) : x + r - (x - r) = 2 * r := by ring
  have hquot :
      Tendsto (fun r : ℝ ↦ ((∫ y in x - r..x + r, f y) - (2 * r) * f x) / (2 * r))
        (𝓝[>] 0) (𝓝 0) := by
    simpa only [Pi.sub_apply, hlength, smul_eq_mul] using herror.tendsto_div_nhds_zero
  have hlim := hquot.add (tendsto_const_nhds (x := f x))
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r hr
  have hne : 2 * r ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt (mem_Ioi.mp hr))
  rw [sub_div, mul_comm (2 * r) (f x), mul_div_cancel_right₀ _ hne, sub_add_cancel,
    div_eq_mul_inv, mul_comm]

/-- Paper: (A.5.1.2), p. 566. The centered maximal function takes the supremum of
the averages of the absolute value over intervals of all positive radii.
Deviation: The supremum over all radii expresses the intended operator behind the printed
“lim sup”. Extended nonnegative integrals also define the formula on locally integrable inputs. -/
def realCenteredMaximal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ r : Ioi (0 : ℝ), (ENNReal.ofReal (2 * (r : ℝ)))⁻¹ *
    ∫⁻ y in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖f y‖ₑ

/-- Paper: (A.5.1.2), p. 566. The centered maximal function of a constant
is its absolute value at every point. -/
theorem realCenteredMaximal_const (c : ℂ) (x : ℝ) :
    realCenteredMaximal (fun _ ↦ c) x = ‖c‖ₑ := by
  -- Each average of the constant `‖c‖ₑ` over an interval of length `2r` is `‖c‖ₑ`.
  have h : ∀ r : Ioi (0 : ℝ), (ENNReal.ofReal (2 * (r : ℝ)))⁻¹ *
      ∫⁻ _ in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖c‖ₑ = ‖c‖ₑ := by
    rintro ⟨r, hr⟩
    have hr' : (0 : ℝ) < r := hr
    rw [setLIntegral_const, Real.volume_Ioc, show x + r - (x - r) = 2 * r by ring,
      mul_comm, mul_assoc, ENNReal.mul_inv_cancel (by simp [hr']) ENNReal.ofReal_ne_top, mul_one]
  simp only [realCenteredMaximal, h, ciSup_const]

-- TODO(paper-gap): In Theorem A.5.1.1(1), the all-radii maximal function need not be finite
-- anywhere. For f(x) = |x| both local hypotheses hold and the averages grow without bound.

-- Local integrability suffices for measurability.
set_option linter.unusedVariables false in
/-- Paper: Theorem A.5.1.1(1), p. 566. Under the two local integrability hypotheses,
the centered maximal function is measurable. Input measurability is for completed
Lebesgue measure.
Deviation: The separate almost-everywhere finiteness claim fails for the all-radii operator. -/
theorem realCenteredMaximal_measurable {f : ℝ → ℂ} (hf : AEMeasurable f volume)
    (hlocal : LocallyIntegrable f volume)
    (hlog : LocallyIntegrable (fun x ↦ (max (Real.log ‖f x‖) 0 : ℝ) • f x) volume) :
    Measurable (realCenteredMaximal f) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun y ↦ ‖f y‖) volume a b :=
    (IntegrableOn.intervalIntegrable
      (hlocal.integrableOn_isCompact (k := uIcc a b) isCompact_uIcc)).norm
  have hprimitive := intervalIntegral.continuous_primitive hint 0
  apply LowerSemicontinuous.measurable
  unfold realCenteredMaximal
  apply lowerSemicontinuous_iSup
  intro r
  apply Continuous.lowerSemicontinuous
  have hr : 0 < (r : ℝ) := r.property
  have havg : Continuous (fun x : ℝ ↦ ∫ y in x - (r : ℝ)..x + (r : ℝ), ‖f y‖) := by
    have hright : Continuous (fun x : ℝ ↦ x + (r : ℝ)) := continuous_id.add continuous_const
    have hleft : Continuous (fun x : ℝ ↦ x - (r : ℝ)) := continuous_id.sub continuous_const
    convert (hprimitive.comp hright).sub (hprimitive.comp hleft) using 1
    ext x
    exact (intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)).symm
  have hlintegral (x : ℝ) :
      (∫⁻ y in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖f y‖ₑ) =
        ENNReal.ofReal (∫ y in x - (r : ℝ)..x + (r : ℝ), ‖f y‖) := by
    have hab : x - (r : ℝ) ≤ x + (r : ℝ) := by linarith
    rw [intervalIntegral.integral_of_le hab,
      ofReal_integral_eq_lintegral_ofReal (hint _ _).1 (Eventually.of_forall fun y ↦ norm_nonneg _)]
    simp only [ofReal_norm]
  simp only [hlintegral]
  exact (ENNReal.continuous_const_mul (by simp [hr])).comp (ENNReal.continuous_ofReal.comp havg)

/-- Paper: Theorem A.5.1.1(2), p. 566. The level set of the centered maximal function
has measure at most three times the L¹ norm divided by the positive level. -/
theorem realCenteredMaximal_weak_one {f : ℝ → ℂ} (hf : AEMeasurable f volume)
    (h₁ : Integrable f volume) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < realCenteredMaximal f x} ≤
      ENNReal.ofReal (3 / a) * eLpNorm f 1 volume := by sorry

/-- Paper: Theorem A.5.1.1(3), p. 566. For a finite exponent p greater than one,
the p-th moment of the centered maximal function has the displayed strong-type bound. -/
theorem realCenteredMaximal_strong {f : ℝ → ℂ} (hf : AEMeasurable f volume) {p : ℝ}
    (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, realCenteredMaximal f x ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * 3 * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by sorry

/-- Paper: Theorem A.5.1.3, p. 568. Centered averages of a locally integrable
function converge to its value at almost every point of the real line. -/
theorem ae_tendsto_centeredAverage {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun r : ℝ ↦ ((2 * r)⁻¹ : ℝ) • ∫ y in x - r..x + r, f y)
        (𝓝[>] 0) (𝓝 (f x)) := by sorry

section DSequences

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

/-- Paper: Definition A.5.2.1, p. 569. A D-sequence consists of decreasing Haar-measurable
sets containing the identity, of positive finite measure, with a uniform strict bound
for the measure of each set multiplied by its inverse. -/
def IsDSequence (μ : Measure G) (U : ℕ → Set G) : Prop :=
  (∀ k, 1 ∈ U k ∧ NullMeasurableSet (U k) μ ∧ 0 < μ (U k) ∧ μ (U k) < ∞) ∧
    Antitone U ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k, 0 < μ (U k * (U k)⁻¹) ∧
      μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k)

variable [TopologicalSpace G]

/-- Paper: Definition A.5.2.1, p. 569. A D′-sequence is a D-sequence whose
members are cofinal in the neighborhoods of the identity. -/
def IsDPrimeSequence (μ : Measure G) (U : ℕ → Set G) : Prop :=
  IsDSequence μ U ∧ ∀ W ∈ 𝓝 (1 : G), ∃ k, U k ⊆ W

/-- Paper: Remark A.5.2.2, p. 569. A D″-sequence is a D′-sequence with a specified
family of Haar-measurable sets whose difference sets fit inside the corresponding members.
Their measures control those of the original sets by one positive constant. -/
def IsDDoublePrimeSequence (μ : Measure G) (U V : ℕ → Set G) : Prop :=
  IsDPrimeSequence μ U ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k, NullMeasurableSet (V k) μ ∧ V k * (V k)⁻¹ ⊆ U k ∧
      μ (U k) ≤ ENNReal.ofReal C * μ (V k)

end DSequences

section TopologicalGroups

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G)

/-- Paper: Proposition A.5.2.3(1), p. 570. A first-countable locally profinite
group has a D″-sequence of compact open subgroups. Each auxiliary set is the
pointwise square of the corresponding subgroup, and the mass comparison has constant one.
Deviation: Local profiniteness is expressed by total disconnectedness together with
the ambient Hausdorff local compactness. The stated comparison constant one is for
the D″ condition. The proof's choice of doubling constant one violates strictness. -/
theorem exists_isDDoublePrimeSequence_of_totallyDisconnected [FirstCountableTopology G]
    [TotallyDisconnectedSpace G] [μ.IsHaarMeasure] :
    ∃ K : ℕ → OpenSubgroup G,
      let U : ℕ → Set G := fun k ↦ (K k : Set G)
      let V : ℕ → Set G := fun k ↦ U k * U k
      IsDDoublePrimeSequence μ U V ∧ ∀ k, IsCompact (U k) ∧ μ (U k) ≤ μ (V k) := by sorry

variable (H : OpenSubgroup G) (U : ℕ → Set H)

local notation "inclusion" => (fun x : H ↦ (x : G))

/-- Paper: Proposition A.5.2.3(2), p. 570. A sequence in an open subgroup is a
D-sequence for the restricted Haar measure exactly when its images form one in the group. -/
theorem isDSequence_openSubgroup_iff [μ.IsHaarMeasure] :
    IsDSequence (μ.comap inclusion) U ↔ IsDSequence μ (fun k ↦ inclusion '' U k) := by sorry

/-- Paper: Proposition A.5.2.3(2), p. 570. The D′ condition transfers in both
directions under the inclusion of an open subgroup, with the restricted Haar measure. -/
theorem isDPrimeSequence_openSubgroup_iff [μ.IsHaarMeasure] :
    IsDPrimeSequence (μ.comap inclusion) U ↔
      IsDPrimeSequence μ (fun k ↦ inclusion '' U k) := by sorry

/-- Paper: Proposition A.5.2.3(2), p. 570. Openness agrees in the open subgroup
and in the ambient group. -/
theorem isOpen_sequence_openSubgroup_iff :
    (∀ k, IsOpen (U k)) ↔ ∀ k, IsOpen (inclusion '' U k) := by sorry

/-- Paper: Proposition A.5.2.3(2), p. 570. Inversion symmetry agrees in the open
subgroup and in the ambient group. -/
theorem inv_eq_sequence_openSubgroup_iff :
    (∀ k, (U k)⁻¹ = U k) ↔ ∀ k, (inclusion '' U k)⁻¹ = inclusion '' U k := by sorry

/-- Paper: Remark A.5.2.4, p. 570. The constant singleton of the identity
is an open, symmetric D-sequence on a countable discrete abelian group. -/
theorem isDSequence_singleton_one [Countable G] [DiscreteTopology G] [μ.IsHaarMeasure] :
    IsDSequence μ (fun _ ↦ ({1} : Set G)) := by
  have hpos : 0 < μ ({1} : Set G) := (isOpen_discrete _).measure_pos μ (singleton_nonempty 1)
  have hfin : μ ({1} : Set G) < ∞ := isCompact_singleton.measure_lt_top
  refine ⟨fun _ ↦ ⟨rfl, (measurableSet_singleton 1).nullMeasurableSet, hpos, hfin⟩,
    antitone_const, 2, two_pos, fun _ ↦ ?_⟩
  simp only [inv_singleton, inv_one, singleton_mul_singleton, mul_one]
  refine ⟨hpos, ?_⟩
  rw [ENNReal.ofReal_ofNat, two_mul]
  exact ENNReal.lt_add_right hfin.ne hpos.ne'

/-- Paper: Remark A.5.2.4, p. 570. The constant singleton of the identity
forms a D′-sequence on a countable discrete abelian group. -/
theorem isDPrimeSequence_singleton_one [Countable G] [DiscreteTopology G] [μ.IsHaarMeasure] :
    IsDPrimeSequence μ (fun _ ↦ ({1} : Set G)) := by sorry

/-- Paper: Remark A.5.2.4, p. 570. The constant singleton of the identity, paired
with itself, is a D″-sequence on a countable discrete abelian group. -/
theorem isDDoublePrimeSequence_singleton_one [Countable G] [DiscreteTopology G]
    [μ.IsHaarMeasure] :
    IsDDoublePrimeSequence μ (fun _ ↦ ({1} : Set G)) (fun _ ↦ ({1} : Set G)) := by sorry

end TopologicalGroups

section Products

variable {G₁ G₂ : Type*}
  [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
  [LocallyCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
  [LocallyCompactSpace G₂] [MeasurableSpace G₂] [BorelSpace G₂]

local instance : MeasurableSpace (G₁ × G₂) := borel _

variable {μ₁ : Measure G₁} {μ₂ : Measure G₂} {μ : Measure (G₁ × G₂)}
  [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ.IsHaarMeasure]
  {U : ℕ → Set G₁} {V : ℕ → Set G₂}

variable (hμ : ∀ (s : Set G₁) (t : Set G₂), MeasurableSet s → MeasurableSet t →
  μ (s ×ˢ t) = μ₁ s * μ₂ t)

include hμ in
/-- Paper: Lemma A.5.2.5, p. 570. The termwise Cartesian product of D-sequences is a
D-sequence for product Haar measure.
Deviation: The product Haar measure is specified by its values on Borel rectangles.
This formulation also covers groups whose Haar measure is outside the scope of
Mathlib's `Measure.prod` construction. -/
theorem IsDSequence.prod (hU : IsDSequence μ₁ U) (hV : IsDSequence μ₂ V) :
    IsDSequence μ (fun k ↦ U k ×ˢ V k) := by sorry

include hμ in
/-- Paper: Lemma A.5.2.5, p. 570. The termwise Cartesian product of D′-sequences is a
D′-sequence for product Haar measure, specified by its values on Borel rectangles. -/
theorem IsDPrimeSequence.prod (hU : IsDPrimeSequence μ₁ U) (hV : IsDPrimeSequence μ₂ V) :
    IsDPrimeSequence μ (fun k ↦ U k ×ˢ V k) := by sorry

/-- Paper: Lemma A.5.2.5, p. 570. The product of two open members is open. -/
theorem isOpen_prod_sequence (k : ℕ) (hU : IsOpen (U k)) (hV : IsOpen (V k)) :
    IsOpen (U k ×ˢ V k) := hU.prod hV

/-- Paper: Lemma A.5.2.5, p. 570. The product of two symmetric members is symmetric. -/
theorem inv_eq_prod_sequence (k : ℕ) (hU : (U k)⁻¹ = U k) (hV : (V k)⁻¹ = V k) :
    (U k ×ˢ V k)⁻¹ = U k ×ˢ V k := by
  rw [Set.inv_prod, hU, hV]

end Products

section QuotientGroups

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

local instance : MeasurableSpace (G ⧸ H) := borel _
local notation "q" => (QuotientGroup.mk' H)

variable [DiscreteTopology H] (hH : IsClosed (H : Set G))
  {μ : Measure G} [μ.IsHaarMeasure]
  {μH : Measure H} [μH.IsHaarMeasure] {ν : Measure (G ⧸ H)}
  (hν : IsWeilQuotientMeasure H μ μH ν) (hcount : μH {1} = 1)
  {E : Set G} (hE : MeasurableSet E) (hEc : IsCompact (closure E))
  (hE₁ : 1 ∈ interior E)
  (hbij : Bijective (fun x : E ↦ (QuotientGroup.mk' H) (x : G)))
  {U : ℕ → Set (G ⧸ H)} (hU : ∀ k, MeasurableSet (U k)) (hmono : Antitone U)

local notation "lifted" => (fun k ↦ Set.inter (q ⁻¹' U k) E)

include hH hν hcount hE hEc hE₁ hbij hU hmono in
/-- Paper: Proposition A.5.2.6, p. 570. A decreasing Borel family on the
quotient is a D-sequence exactly when its lifts to the fundamental domain form one. -/
theorem isDSequence_quotient_iff :
    IsDSequence ν U ↔ IsDSequence μ lifted := by sorry

include hH hν hcount hE hEc hE₁ hbij hU hmono in
/-- Paper: Proposition A.5.2.6, p. 571. The D′ condition is equivalent for the
quotient sequence and for the lifts through the fundamental domain. -/
theorem isDPrimeSequence_quotient_iff :
    IsDPrimeSequence ν U ↔ IsDPrimeSequence μ lifted := by sorry

include hbij in
/-- Paper: Proposition A.5.2.6, p. 571. For a symmetric fundamental domain,
the quotient family is symmetric exactly when the lifted family is symmetric. -/
theorem inv_eq_sequence_quotient_iff (hEsymm : E⁻¹ = E) :
    (∀ k, (U k)⁻¹ = U k) ↔ ∀ k, (lifted k)⁻¹ = lifted k := by sorry

-- TODO(paper-gap): The D″ equivalence claimed in the proof of A.5.2.6 fails.
-- For ℤ → ℤ/3ℤ take the symmetric domain {-1, 0, 1} and U₀ = V₀ = ℤ/3ℤ.
-- The difference set of the lifts contains 2, which is outside the domain.

end QuotientGroups

/-- Paper: Theorem A.5.2.8, p. 571. A continuous map between Polish spaces sends a
Borel subset on which it is injective to a Borel set. -/
theorem measurableSet_image_of_continuous_injOn_polish {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Continuous f) {E : Set X} (hE : MeasurableSet E)
    (hinj : InjOn f E) :
    MeasurableSet (f '' E) := by sorry

/-- Paper: Lemma A.5.2.10, p. 572. A Borel partial transversal to a free proper action
of a countable discrete abelian group extends to a Borel transversal.
Deviation: The group acts on X, as specified by the quotient and proof. -/
theorem exists_borel_orbit_transversal {X H : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [CommGroup H] [TopologicalSpace H] [DiscreteTopology H]
    [Countable H] [MulAction H X] [ProperSMul H X] [IsCancelSMul H X]
    {E : Set X} (hE : MeasurableSet E)
    (hinj : InjOn (Quotient.mk (MulAction.orbitRel H X)) E) :
    ∃ F : Set X, MeasurableSet F ∧ E ⊆ F ∧
      Bijective (fun x : F ↦ Quotient.mk (MulAction.orbitRel H X) (x : X)) := by sorry

section Ideles

set_option maxSynthPendingDepth 8

open NumberField InfinitePlace.Completion
open NumberField.Units.dirichletUnitTheorem
open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
local notation "N₁" => MonoidHom.ker (ideleNorm F)
local notation "atInfinity" => Units.map (RingHom.toMonoidHom (RingHom.fst _ _))

variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

-- Equations (A.5.2.7)–(A.5.2.10) recall the domains already defined in §A.2.3.

/-- Paper: (A.5.2.11)–(A.5.2.12), p. 574. Translate the regulator
parallelotope by minus one half of the sum of its basis vectors.
Deviation: As in §A.2.3, logarithmic coordinates omit one infinite place. -/
def centeredRegulatorParallelotope : Set (logSpace F) :=
  (-∑ i, (1 / 2 : ℝ) • Units.logEmbeddingQuot F (b i)) +ᵥ regulatorParallelotope F b

/-- Paper: (A.5.2.11)–(A.5.2.12), p. 574. On one basis direction the centered
parallelotope includes coefficients from minus one half up to one half, excluding the latter. -/
theorem centeredRegulatorParallelotope_basis_line (i : Fin (Units.rank F)) (t : ℝ) :
    t • Units.logEmbeddingQuot F (b i) ∈ centeredRegulatorParallelotope F b ↔
      t ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by sorry

variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)

local notation "atPlace" => Units.map (RingHom.toMonoidHom (Pi.evalRingHom InfinitePlace.Completion v₀))

/-- Paper: (A.5.2.14), p. 575. The centered angular sector has width two pi
divided by the number of roots of unity.
Deviation: We use the principal argument, so the two intervals in the paper are one
half-open interval centered at zero. -/
def inCenteredTorsionSector (x : v₀.Completionˣ) : Prop :=
  (σ (extensionEmbedding v₀ x.val)).arg ∈
    Ico (-Real.pi / (Units.torsionOrder F : ℝ)) (Real.pi / (Units.torsionOrder F : ℝ))

/-- Paper: (A.5.2.14), p. 575. At a real place the centered angular sector
picks out the positive component. -/
theorem inCenteredTorsionSector_real (hv : v₀.IsReal) (x : v₀.Completionˣ) :
    inCenteredTorsionSector F v₀ σ x ↔ 0 < extensionEmbeddingOfIsReal hv x.val := by sorry

/-- Paper: (A.5.2.14), p. 575. The centered archimedean domain is cut out by
the centered regulator parallelotope and the centered angular sector. -/
def centeredInfiniteIdeleDomain : Set N∞ :=
  {g | (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ infiniteIdeleLog F g.val w.val) ∈
    centeredRegulatorParallelotope F b ∧ inCenteredTorsionSector F v₀ σ (atPlace g.val)}

/-- Paper: (A.5.2.13), p. 575. The norm-one integral ideles whose
archimedean component lies in the centered domain form the set B_F¹. -/
def centeredIntegralIdeleDomain : Set N₁ :=
  {g | g.val ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range ∧
    atInfinity g.val ∈ (N∞).subtype '' centeredInfiniteIdeleDomain F b v₀ σ}

/-- Paper: (A.5.2.13), p. 575. The identity idele belongs to the centered integral domain. -/
theorem one_mem_centeredIntegralIdeleDomain :
    1 ∈ centeredIntegralIdeleDomain F b v₀ σ := by sorry

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "sRank(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S - 1)
local notation "unitAtS" => MonoidHom.comp (Units.map (RingHom.toMonoidHom (adeleProjection F S)))
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

variable (bₛ : Module.Basis (Fin sRank(F, S)) ℤ (Additive (Oₛ(F, S)ˣ ⧸ CommGroup.torsion Oₛ(F, S)ˣ)))

/-- Paper: (A.5.2.18), p. 575. The S-regulator parallelotope consists of sums
of the basis logarithms with coefficients in the centered half-open unit interval.
Deviation: As in §A.2.4, the integral basis is taken modulo torsion. -/
def centeredSRegulatorParallelotope : Set (InfinitePlace F ⊕ S → ℝ) :=
  {y | ∃ t : Fin sRank(F, S) → ℝ, (∀ i, t i ∈ Ico (-1 / 2 : ℝ) (1 / 2)) ∧
    y = ∑ i, t i • sIdeleLog F S (unitAtS (bₛ i).toMul.out)}

/-- Paper: (A.5.2.18), p. 575. Each basis logarithm contributes a half-open
interval on its own line in the centered parallelotope. -/
theorem centeredSRegulatorParallelotope_basis_line (i : Fin sRank(F, S)) (t : ℝ) :
    t • sIdeleLog F S (unitAtS (bₛ i).toMul.out) ∈ centeredSRegulatorParallelotope F S bₛ ↔
      t ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by sorry

/-- Paper: (A.5.2.15)–(A.5.2.18), p. 575. The centered S-local domain is cut
out by the centered S-parallelotope and the centered angular sector at the chosen place. -/
def centeredSLocalIdeleDomain : Set Nₛ :=
  {g | sIdeleLog F S g.val ∈ centeredSRegulatorParallelotope F S bₛ ∧
    inCenteredTorsionSector F v₀ σ (atPlace (atInfinity g.val))}

/-- Paper: (A.5.2.15), p. 575. The identity S-idele belongs to the centered S-local domain. -/
theorem one_mem_centeredSLocalIdeleDomain :
    1 ∈ centeredSLocalIdeleDomain F v₀ σ S bₛ := by sorry

/-- Paper: Lemma A.5.2.12(1), p. 575. The class-representative translates of
the centered integral domain meet every principal orbit in exactly one point. -/
theorem centeredIntegralIdeleDomain_fundamental
    (r : CommRing.Pic (𝓞 F) → N₁) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c) (g : N₁) :
    ∃! a : Fˣ, (IdeleGroup.unitEmbedding (𝓞 F) F a)⁻¹ * g.val ∈
      (N₁).subtype '' (⋃ c, r c • centeredIntegralIdeleDomain F b v₀ σ) := by sorry

/-- Paper: Lemma A.5.2.12(2), p. 575. The centered S-local domain meets each
orbit of the diagonal S-units in the norm-one S-ideles in exactly one point. -/
theorem centeredSLocalIdeleDomain_fundamental
    (g : Nₛ) :
    ∃! a : Oₛ(F, S)ˣ, (unitAtS a)⁻¹ * g.val ∈
      (Nₛ).subtype '' centeredSLocalIdeleDomain F v₀ σ S bₛ := by sorry

-- TODO(paper-gap): Lemma A.5.2.12(3) omits the outside-S unit factor from the domain.
-- For ℚ with S = {∞}, a tuple with archimedean component 1 and nontrivial outside unit
-- component cannot be moved into the embedded B_F,S¹ by a diagonal unit.
-- The prescribed ideal-class representatives also have trivial S-ideal class.

/-- Paper: Lemma A.5.2.13(1), p. 576. The interior of the centered archimedean
domain contains the identity and is therefore a neighborhood of it. -/
theorem interior_centeredInfiniteIdeleDomain_mem_nhds :
    interior (centeredInfiniteIdeleDomain F b v₀ σ) ∈ 𝓝 (1 : N∞) := by sorry

/-- Paper: Lemma A.5.2.13(1), p. 576. The interior of the centered archimedean
domain is invariant under inversion. -/
theorem inv_interior_centeredInfiniteIdeleDomain :
    (interior (centeredInfiniteIdeleDomain F b v₀ σ))⁻¹ =
      interior (centeredInfiniteIdeleDomain F b v₀ σ) := by sorry

/-- Paper: (A.5.2.19)–(A.5.2.20), p. 576. Pull back the shrinking open log cubes
in regulator coordinates to the norm-one archimedean ideles. -/
def infiniteIdeleLogNeighborhood (k : ℕ) : Set N∞ :=
  {g | ∃ t : Fin (Units.rank F) → ℝ,
    (∀ i, t i ∈ Ioo (-(1 / ((k : ℝ) + 1))) (1 / ((k : ℝ) + 1))) ∧
    ∀ w : {w : InfinitePlace F // w ≠ w₀},
      infiniteIdeleLog F g.val w.val = ∑ i, t i * Units.logEmbeddingQuot F (b i) w}

/-- Paper: (A.5.2.19)–(A.5.2.20), p. 576. A norm-one archimedean idele belongs
to every one of the log neighborhoods exactly when all its logarithmic coordinates vanish. -/
theorem mem_all_infiniteIdeleLogNeighborhood_iff (g : N∞) :
    (∀ k, g ∈ infiniteIdeleLogNeighborhood F b k) ↔ infiniteIdeleLog F g.val = 0 := by sorry

/-- Paper: Lemma A.5.2.13(2), p. 576. Each shrinking log cube pulls back
to an inversion-invariant subset of the archimedean norm-one group. -/
theorem inv_infiniteIdeleLogNeighborhood (k : ℕ) :
    (infiniteIdeleLogNeighborhood F b k)⁻¹ = infiniteIdeleLogNeighborhood F b k := by sorry

-- TODO(paper-gap): The D′ and D″ assertions of Lemma A.5.2.13(2) fail. All the
-- preimages in (A.5.2.19) contain the log kernel, including the nonidentity element −1.

local notation "finiteAtS" => Units.map (RingHom.toMonoidHom (RingHom.snd _ _))
local notation "finiteGlobal" => Units.map (RingHom.toMonoidHom (RingHom.snd (InfiniteAdeleRing F)
  (FiniteAdeleRing (𝓞 F) F)))

/-- Paper: (A.5.2.21), p. 576. Take the product of the archimedean log neighborhood
and the selected finite unit set inside the norm-one S-ideles.
Deviation: The finite sets are supplied via their images in the units at the finite places of S. -/
def sLocalIdeleLogNeighborhood
    (B : ℕ → Set (((v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) → v.val.adicCompletion F)ˣ))
    (k : ℕ) : Set Nₛ :=
  {g | atInfinity g.val ∈ (N∞).subtype '' infiniteIdeleLogNeighborhood F b k ∧
    finiteAtS g.val ∈ B k}

/-- Paper: (A.5.2.21), p. 576. The identity belongs to the product neighborhood
exactly when the selected finite set contains its identity. -/
theorem one_mem_sLocalIdeleLogNeighborhood_iff
    (B : ℕ → Set (((v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) → v.val.adicCompletion F)ˣ)) (k : ℕ) :
    1 ∈ sLocalIdeleLogNeighborhood F b S B k ↔ 1 ∈ B k := by sorry

/-- Paper: Lemma A.5.2.14(1), p. 576. With a symmetric finite factor,
the product neighborhood in the norm-one S-ideles is symmetric.
Deviation: The D′ condition fails for the printed sequence. -/
theorem inv_sLocalIdeleLogNeighborhood
    (B : ℕ → Set (((v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) → v.val.adicCompletion F)ˣ))
    (k : ℕ) (hB : (B k)⁻¹ = B k) :
    (sLocalIdeleLogNeighborhood F b S B k)⁻¹ =
      sLocalIdeleLogNeighborhood F b S B k := by sorry

-- TODO(paper-gap): Lemma A.5.2.14(1) inherits the nonshrinking log kernel.
-- For ℚ(i) the persistent circle also has nontrivial image in J_F,S¹ for S = S∞,
-- contradicting the D′ claim in Lemma A.5.2.14(2).
-- TODO(paper-gap): Lemma A.5.2.15 uses (A.5.2.22), which is undefined at k = 0
-- and uses intervals that are not invariant under inversion.

/-- Paper: (A.5.2.23), p. 577. Take the product of the archimedean log neighborhood
and the selected finite unit set inside the global norm-one ideles.
The finite sets are supplied as their images in the finite ideles. -/
def ideleLogNeighborhood (B : ℕ → Set (FiniteAdeleRing (𝓞 F) F)ˣ) (k : ℕ) : Set N₁ :=
  {g | atInfinity g.val ∈ (N∞).subtype '' infiniteIdeleLogNeighborhood F b k ∧
    finiteGlobal g.val ∈ B k}

/-- Paper: (A.5.2.23), p. 577. The identity belongs to the global product neighborhood
exactly when the chosen finite unit set contains its identity. -/
theorem one_mem_ideleLogNeighborhood_iff
    (B : ℕ → Set (FiniteAdeleRing (𝓞 F) F)ˣ) (k : ℕ) :
    1 ∈ ideleLogNeighborhood F b B k ↔ 1 ∈ B k := by sorry

/-- Paper: Lemma A.5.2.16(1), p. 577. With a symmetric finite factor,
the product neighborhood in the global norm-one ideles is symmetric.
Deviation: The D′ condition fails for the printed sequence. -/
theorem inv_ideleLogNeighborhood (B : ℕ → Set (FiniteAdeleRing (𝓞 F) F)ˣ)
    (k : ℕ) (hB : (B k)⁻¹ = B k) :
    (ideleLogNeighborhood F b B k)⁻¹ = ideleLogNeighborhood F b B k := by sorry

-- TODO(paper-gap): The D′ assertions of Lemma A.5.2.16 fail. Over ℚ(i) every set
-- contains the archimedean circle, whose images in the class groups are nontrivial.

end Ideles

/-- Paper: (A.5.2.22) and (A.5.2.24), p. 577. Multiply the image of the printed
interval under a norm section by the corresponding norm-one set in the ambient group.
Deviation: The formula is defined only at positive indices. -/
def normSectionNeighborhood {G : Type*} [Group G] (τ : ℝ≥0ˣ →* G)
    (U : ℕ → Set G) (k : ℕ+) : Set G :=
  (τ '' {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ioo (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ))}) * U k

/-- Paper: (A.5.2.22) and (A.5.2.24), p. 577. If the selected kernel set
contains the identity, applying the norm recovers exactly the printed interval
in the positive reals. -/
theorem norm_image_normSectionNeighborhood {G : Type*} [Group G] (n : G →* ℝ≥0ˣ)
    (τ : ℝ≥0ˣ →* G) (hτ : RightInverse τ n) (U : ℕ → Set G) (k : ℕ+)
    (hU₁ : 1 ∈ U k) (hU : U k ⊆ n.ker) :
    n '' normSectionNeighborhood τ U k =
      {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ioo (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ))} := by sorry

-- TODO(paper-gap): Lemma A.5.2.17 has the same interval problems as A.5.2.15 and
-- retains the log kernel in each norm-one factor and in its class-group images.
-- TODO(paper-gap): Definition A.5.2.18 calls the affected families open symmetric
-- D′-sequences. The displayed families do not have those properties.
-- TODO(paper-gap): Remark A.5.2.19 gives constant 1 when the log rank is zero.
-- This contradicts the strict upper bound in (A.5.2.1) for any set containing 1.

end RiemannMasullo
