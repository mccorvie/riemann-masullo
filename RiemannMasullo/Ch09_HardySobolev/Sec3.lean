module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3b
public import RiemannMasullo.AppC_LCTVS.Sec4

/-!
# Module structures over test functions and approximate units

Masullo, §9.3, pp. 419–432.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal UniformConvergenceCLM

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

section RegularizedAction

-- TODO(prerequisite): §9.2 provides the weighted Hilbert model for compact base
-- intervals. The closed unbounded intervals in §9.3 need a Hilbert model and action.

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "logMod" => (fun x ↦ Real.log ((m x).val : ℝ))
local notation "W" => (fun a b s ↦ CompactIntervalSobolev μ logMod a b s)
set_option quotPrecheck false in
local notation "Lβ" E => E →Lᵤ[ℂ, {s : Set E | Bornology.IsVonNBounded ℂ s}] E

/-- Paper: Definition 9.3.1.1, p. 419. Left translation acts jointly continuously
on the compact-interval Hardy–Sobolev Hilbert space, with the translated function
as its almost-everywhere representative.
Deviation: This records the regular representation used in the definition, in the
weighted L² model of §9.2. -/
theorem exists_hardySobolevTranslation (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃ ρ : G →* (W a b s →L[ℂ] W a b s),
      (∀ g u, (ρ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x)) ∧
      Continuous (fun p : G × W a b s ↦ ρ p.1 p.2) := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. Choose the regular representation characterized
by the left-translation formula. -/
def hardySobolevTranslation (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    G →* (W a b s →L[ℂ] W a b s) :=
  (exists_hardySobolevTranslation μ m a b s hab hs).choose

/-- Paper: Definition 9.3.1.1, p. 419. The action has the left-translation formula
on representatives almost everywhere. -/
theorem hardySobolevTranslation_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (g : G) (u : W a b s) :
    (hardySobolevTranslation μ m a b s hab hs g u : G → ℂ) =ᵐ[μ]
      fun x ↦ u (g⁻¹ * x) := by sorry

section Pettis

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
variable (ρ : G →* (E →L[ℂ] E))

/-- Paper: Remark 9.3.1.2, p. 419. Integrating a test function against continuous
left translation gives a continuous endomorphism and is linear in the test function.
Deviation: The operator integral is taken on each vector, as in (9.3.2.2) and §C.4.3.
The complete representation space is a parameter. -/
theorem exists_bruhatRegularizedAction [CompleteSpace E]
    (_hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ E,
      ∀ φ u, HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u) (A φ u) := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. A test function acts by integrating
its scalar multiples of left translations against Haar measure.
Deviation: The Pettis integral is specified on each input vector. Instantiate the
representation with the action on the decay space or the Hardy–Sobolev space. -/
def bruhatRegularizedAction [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ E :=
  (exists_bruhatRegularizedAction μ ρ hρ).choose

/-- Paper: Definition 9.3.1.1, p. 419. The action on each vector represents
the Pettis integral of the test function times its orbit. -/
theorem bruhatRegularizedAction_apply [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ : BruhatCompactSupport G) (u : E) :
    HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u)
      (bruhatRegularizedAction μ ρ hρ φ u) := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. Convolution of test kernels acts as
composition of their integrated endomorphisms.
Deviation: The convolution is represented by its pointwise formula in the test space. -/
theorem bruhatRegularizedAction_convolution [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ ψ : BruhatCompactSupport G) :
    ∃ θ : BruhatCompactSupport G, θ.val = lcaConvolution μ φ.val ψ.val ∧
      ∀ u, bruhatRegularizedAction μ ρ hρ θ u =
        bruhatRegularizedAction μ ρ hρ φ (bruhatRegularizedAction μ ρ hρ ψ u) := by sorry

end Pettis

/-- Paper: Definition 9.3.1.1, p. 419. The regularized action on the
Hardy–Sobolev space integrates the left translation of its square-integrable classes.
Deviation: Use the compact-interval weighted model of §9.2. -/
def hardySobolevTestAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ (W a b s) :=
  bruhatRegularizedAction μ (hardySobolevTranslation μ m a b s hab hs)
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2

/-- Paper: (9.3.1.2), p. 419. The test action on the weighted Hilbert space
acts by the Haar convolution formula almost everywhere. -/
theorem hardySobolevTestAction_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (u : W a b s) :
    (hardySobolevTestAction μ m a b s hab hs φ u : G → ℂ) =ᵐ[μ]
      lcaConvolution μ φ.val u := by sorry

/-- Paper: Remark 9.3.1.2, p. 419. Convolution by a test function defines
a continuous endomorphism of the exponential-decay space and depends linearly on the test.
Deviation: Evaluating the Pettis integral at each group element gives this pointwise formula. -/
theorem exists_modulatedExponentialDecayTestAction
    (_hm : IsModulation m) (_hms : Surjective m)
    (I : Set ℝ) (_hInt : OrdConnected I) (_hne : I.Nonempty) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I),
      ∀ φ u, (A φ u).val = lcaConvolution μ φ.val u.val := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. The regularized action on the
exponential-decay space acts by convolution of the test function with the input. -/
def modulatedExponentialDecayTestAction (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I) :=
  (exists_modulatedExponentialDecayTestAction μ m hm hms I hInt hne).choose

/-- Paper: (9.3.1.2), p. 419. The test action on the exponential-decay space
has the usual pointwise Haar convolution formula. -/
theorem modulatedExponentialDecayTestAction_apply (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (φ : BruhatCompactSupport G) (u : ModulatedExponentialDecay m I) :
    (modulatedExponentialDecayTestAction μ m hm hms I hInt hne φ u).val =
      lcaConvolution μ φ.val u.val := by sorry

/-- Paper: Lemma 9.3.1.3, p. 419. The test action on the Hardy–Sobolev
space is continuous into the topology of uniform convergence on bounded sets.
Deviation: The weighted Hilbert model is for a compact base interval. -/
theorem continuous_hardySobolevTestAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    Continuous (hardySobolevTestAction μ m a b s hab hs) := by sorry

/-- Paper: Lemma 9.3.1.3, p. 419. The test action on the exponential-decay
space is continuous into the topology of uniform convergence on bounded sets. -/
theorem continuous_modulatedExponentialDecayTestAction (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    Continuous (modulatedExponentialDecayTestAction μ m hm hms I hInt hne) := by sorry

-- TODO(paper-gap): Lemma 9.3.1.5's bound is zero at the identity for s > 0.
-- The singleton polynomial-growth claim also omits the exponential twist for b ≠ 0.
-- Borel measurability need not hold for arbitrary continuous operator seminorms.

/-- Paper: Lemma 9.3.1.5, p. 421. The operator norm of left translation is a
measurable function of the translating element.
Deviation: This retains the measurable operator-norm case established on p. 422. -/
theorem measurable_hardySobolevTranslation_norm (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    Measurable (fun g ↦ ‖hardySobolevTranslation μ m a b s hab hs g‖) := by sorry

end RegularizedAction

section ApproximateUnits

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

-- TODO(paper-gap): Lemma 9.3.2.1 does not extend from ordinary Schwartz–Bruhat kernels for
-- b ≠ 0. Its single-isotype family cannot converge strongly to the identity on two isotypes.

/-- Paper: Lemma 9.3.2.1, p. 422. On the zero line there is a unique
operator-norm-continuous extension from test functions to Schwartz–Bruhat kernels,
given on each vector by integration of its left translates.
Deviation: This is the separately stated zero-line case of (9.3.2.2) in the proof on
pp. 422–423. The test-space restriction is specified by the same Pettis formula as (9.3.1.2). -/
theorem existsUnique_schwartzBruhat_zeroLineAction (s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    ∃! A : SchwartzBruhat G →L[ℂ] (W →L[ℂ] W),
      ∀ φ u, HasPettisIntegral (.positive μ)
        (fun g ↦ φ.val g • hardySobolevTranslation μ m 0 0 s le_rfl hs g u) (A φ u) := by sorry

/-- Paper: Corollary 9.3.2.3(1), p. 425. The frequency band attached to a character
consists of its twists by imaginary powers of the module with exponents in the given interval.
Deviation: The band is a subset of the full dual, as in the construction in the proof. -/
def modulatedFrequencyBand (m : G →ₜ* ℝ≥0ˣ) (χ : PontryaginDual G) (α β : ℝ) :
    Set (PontryaginDual G) :=
  {ψ | ∃ t ∈ Icc α β, ∀ g, ψ g = χ g * Circle.exp (t * Real.log ((m g).val : ℝ))}

/-- Paper: Corollary 9.3.2.3(1), p. 425. A band consisting of exponent zero
contains exactly its starting character.
Deviation: Sanity check on the frequency band. -/
theorem modulatedFrequencyBand_zero (χ : PontryaginDual G) :
    modulatedFrequencyBand m χ 0 0 = {χ} := by sorry

local instance instDualMeasurableSpaceSec3 : MeasurableSpace (PontryaginDual G) := borel _

variable (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)

set_option quotPrecheck false in
local notation "Fourier" => (lcaFourier_unitary μ ν hν).exists.choose

/-- Paper: Corollary 9.3.2.3(1), p. 425. There is a Sobolev function whose
Fourier transform has a smooth representative supported in the outer frequency band
and equal to one in the inner band.
Deviation: The proof uses the full dual rather than the printed norm-one dual for
the support. The transform is the Plancherel transform and the support condition
is on a representative. -/
theorem exists_modulatedSobolev_fourierCutoff
    (_hm : IsModulation m) (_hms : Surjective m)
    (s : ℝ) (_hs : 0 ≤ s) (χ : PontryaginDual G) (α β ε : ℝ)
    (_hαβ : α < β) (_hε : 0 < ε) (_hband : α + ε < β - ε) :
    ∃ (u : Lp ℂ 2 μ) (v : PontryaginDual G → ℂ),
      MemLp (u : G → ℂ) 2 (sobolevMeasure μ (modulatedSobolevWeight m) s) ∧
      (Fourier u : PontryaginDual G → ℂ) =ᵐ[ν] v ∧
      IsBruhatSmooth v ∧ tsupport v ⊆ modulatedFrequencyBand m χ α β ∧
      EqOn v 1 (modulatedFrequencyBand m χ (α + ε) (β - ε)) := by sorry

/-- Paper: Corollary 9.3.2.3(2), p. 425. Functions whose Plancherel transform has
a compactly supported representative are dense in the logarithmically weighted Sobolev norm.
Deviation: A Haar L² class sharing the weighted class's representative is made explicit. -/
theorem dense_modulatedSobolev_fourierCompactSupport
    (_hm : IsModulation m) (_hms : Surjective m) (s : ℝ) (_hs : 0 ≤ s) :
    Dense {f : ModulatedSobolev m μ s | ∃ (u : Lp ℂ 2 μ) (v : PontryaginDual G → ℂ),
      (u : G → ℂ) =ᵐ[μ] (f : G → ℂ) ∧
      (Fourier u : PontryaginDual G → ℂ) =ᵐ[ν] v ∧ HasCompactSupport v} := by sorry

-- TODO(paper-gap): Lemma 9.3.2.4 includes identically zero Mellin components and
-- also fails for nonzero components, e.g. exp(z²) sin(z²) on the positive reals.

-- TODO(paper-gap): Lemma 9.3.2.5 gives an empty coefficient family for a Gaussian
-- with nowhere-zero Mellin transform, although the algebraic convolution ideal is proper.

-- TODO(paper-gap): Theorem 9.3.2.6 leaves φ and χ unbound. The kernels in (9.3.2.10)
-- become more restrictive as T increases. With a zero at the origin the projectors
-- all kill the same nonzero vector normal to the evaluation kernel.

end ApproximateUnits

section Trace

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "weightDensity" => (fun a b s x ↦
  intervalSobolevDensity a b s (Real.log ((m x).val : ℝ)))
local notation "weightedMeasure" => (fun a b s ↦
  μ.withDensity (fun x ↦ ENNReal.ofReal (weightDensity a b s x)))
set_option quotPrecheck false in
local notation "W" => (fun a b s ↦
  CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) a b s)

/-- Paper: §9.3.3.1, p. 426. A bounded measurable compactly supported kernel
acts by convolution on the Hardy–Sobolev space.
Deviation: Haar measurability is explicit. The existing weighted L² model
is available for compact base intervals. -/
theorem exists_hardySobolevConvolution (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (φ : G → ℂ) (_hφ : AEMeasurable φ μ) (_hc : HasCompactSupport φ)
    (_hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) :
    ∃ A : W a b s →L[ℂ] W a b s, ∀ u,
      ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
        A u x = lcaConvolution μ φ u x := by sorry

/-- Paper: §9.3.3.1, p. 426. The integrated regular representation for a bounded
measurable compactly supported symbol is the operator given by convolution. -/
def hardySobolevConvolution (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) :
    W a b s →L[ℂ] W a b s :=
  (exists_hardySobolevConvolution μ m a b s hab hs φ hφ hc hb).choose

/-- Paper: §9.3.3.1, p. 426. Applying the integrated operator gives the stated
convolution integral almost everywhere, with integrability of the integrand. -/
theorem hardySobolevConvolution_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) (u : W a b s) :
    ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
      hardySobolevConvolution μ m a b s hab hs φ hφ hc hb u x = lcaConvolution μ φ u x := by sorry

section Cutoffs

set_option quotPrecheck false in
local notation "moduleValue" => (fun x ↦ ((m x).val : ℝ))

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff is an inversion-symmetric
nonnegative function of the module with supremum one. Its profile is smooth off a
finite set with finite one-sided limits of every derivative, and it vanishes
outside the larger annulus and equals one on the smaller annulus.
Deviation: The symbol is real-valued, and the uniform norm requirement is expressed
by a supremum over its range. The interval of smoothness of the profile is the positive axis. -/
structure IsModulatedCutoff (Λ ε : ℝ) (ρ : G → ℝ) : Prop where
  radius_pos : 0 < Λ
  width_pos : 0 < ε
  outer_left_sub_width_pos : 0 < Λ⁻¹ - ε
  outer_left_sub_width_lt : Λ⁻¹ - ε < Λ - ε
  nonneg : ∀ x, 0 ≤ ρ x
  abs_le_one : ∀ x, |ρ x| ≤ 1
  sup_eq_one : sSup (range ρ) = 1
  profile : ∃ (q : ℝ → ℝ) (jumps : Finset ℝ),
    (∀ x, ρ x = q (moduleValue x)) ∧ (↑jumps : Set ℝ) ⊆ Ioi 0 ∧
    ContDiffOn ℝ ∞ q (Ioi 0 \ (↑jumps : Set ℝ)) ∧
    ∀ c ∈ jumps, ∀ n : ℕ, ∃ l r : ℝ,
      Tendsto (iteratedDeriv n q) (𝓝[<] c) (𝓝 l) ∧
      Tendsto (iteratedDeriv n q) (𝓝[>] c) (𝓝 r)
  inv_eq : ∀ x, ρ x = ρ x⁻¹
  support_subset : tsupport ρ ⊆ moduleValue ⁻¹' Icc Λ⁻¹ Λ
  eq_one : EqOn ρ 1 (moduleValue ⁻¹' Icc (Λ⁻¹ + ε) (Λ - ε))

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff equals one at the identity
whenever the inner module band contains one.
Deviation: Sanity check on the plateau condition. -/
theorem IsModulatedCutoff.apply_one {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) (_h₁ : Λ⁻¹ + ε ≤ 1) (_h₂ : 1 ≤ Λ - ε) :
    ρ 1 = 1 := by sorry

/-- Paper: Definition 9.3.3.1, p. 427. The piecewise smooth profile gives a
measurable function on the group.
Deviation: This is the measurability needed to act on weighted L². -/
theorem IsModulatedCutoff.measurable {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    Measurable ρ := by sorry

/-- Paper: Definition 9.3.3.1, p. 427. A smooth cutoff is a cutoff whose
complex-valued realization on the group is Bruhat smooth. -/
def IsSmoothModulatedCutoff (Λ ε : ℝ) (ρ : G → ℝ) : Prop :=
  IsModulatedCutoff m Λ ε ρ ∧ IsBruhatSmooth (fun x ↦ (ρ x : ℂ))

/-- Paper: Definition 9.3.3.1, p. 427. A smooth cutoff is continuous on the
group, including at module values where the piecewise smooth definition permits jumps.
Deviation: Sanity check on the smoothness requirement. -/
theorem IsSmoothModulatedCutoff.continuous {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsSmoothModulatedCutoff m Λ ε ρ) :
    Continuous ρ := by sorry

/-- Paper: Definition 9.3.3.1, p. 427. A positive real modulation admits a
smooth cutoff with outer radius two and width one quarter.
Deviation: Sanity check that both cutoff predicates are inhabited. -/
theorem exists_smoothModulatedCutoff_radius_two (_hm : IsModulation m) (_hms : Surjective m) :
    ∃ ρ : G → ℝ, IsSmoothModulatedCutoff m 2 (1 / 4) ρ := by sorry

/-- Paper: Remark 9.3.3.2, pp. 427–428. Multiplication by a measurable symbol
bounded in absolute value by one defines a contractive endomorphism.
Deviation: This uses an arbitrary L² measure so the same construction applies to each
Hardy–Sobolev weight. -/
theorem exists_lpCutoffMultiplier (ν : Measure G) (ρ : G → ℝ) (_hm : Measurable ρ)
    (_hb : ∀ x, |ρ x| ≤ 1) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ‖T‖ ≤ 1 ∧
      ∀ u, (T u : G → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * u x := by sorry

/-- Paper: Definition 9.3.3.1, p. 427. The cutoff operator is pointwise multiplication
on the space of square-integrable classes.
Deviation: Its measure is a parameter. Applying the operator to the weighted
measure gives the Hardy–Sobolev cutoff. -/
def lpCutoffMultiplier (ν : Measure G) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (exists_lpCutoffMultiplier ν ρ hm hb).choose

/-- Paper: (9.3.3.2), p. 427. Representatives of the cutoff operator agree
almost everywhere with the product by the symbol. -/
theorem lpCutoffMultiplier_apply (ν : Measure G) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) (u : Lp ℂ 2 ν) :
    (lpCutoffMultiplier ν ρ hm hb u : G → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * u x := by sorry

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff gives a truncation operator
on square-integrable classes for the chosen measure. -/
def modulatedCutoffOperator (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  lpCutoffMultiplier ν ρ hρ.measurable hρ.abs_le_one

/-- Paper: (9.3.3.2), p. 427. The truncation multiplies by the cutoff on almost
every representative value. -/
theorem modulatedCutoffOperator_apply (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) (u : Lp ℂ 2 ν) :
    (modulatedCutoffOperator m ν hρ u : G → ℂ) =ᵐ[ν]
      fun x ↦ (ρ x : ℂ) * u x := by sorry

/-- Paper: Definition 9.3.3.3, p. 428. The absolute cutoff associated to a set
of module values is the indicator of its inverse image.
Deviation: Use the same formula for the positive, negative and two-sided cutoffs
with `Ici Λ⁻¹`, `Iic Λ`, and `Icc Λ⁻¹ Λ`, respectively. -/
def modulatedAbsoluteCutoff (J : Set ℝ) : G → ℝ :=
  (moduleValue ⁻¹' J).indicator 1

/-- Paper: (9.3.3.4)–(9.3.3.5), p. 428. The two-sided absolute cutoff is the
product of the two one-sided cutoffs. -/
theorem modulatedAbsoluteCutoff_Icc (Λ : ℝ) :
    modulatedAbsoluteCutoff m (Icc Λ⁻¹ Λ) =
      modulatedAbsoluteCutoff m (Ici Λ⁻¹) * modulatedAbsoluteCutoff m (Iic Λ) := by sorry

/-- Paper: Definition 9.3.3.3, p. 428. The two-sided cutoff of radius two
takes value one at the identity.
Deviation: Sanity check at a point inside the band. -/
theorem modulatedAbsoluteCutoff_radius_two_apply_one :
    modulatedAbsoluteCutoff m (Icc (1 / 2) 2) 1 = 1 := by sorry

/-- Paper: Definition 9.3.3.3, p. 428. Each measurable module band has a
measurable indicator with values bounded in absolute value by one.
Deviation: These are the side conditions for applying the common multiplier. -/
theorem modulatedAbsoluteCutoff_measurable_bounded (J : Set ℝ) (_hJ : MeasurableSet J) :
    Measurable (modulatedAbsoluteCutoff m J) ∧ ∀ x, |modulatedAbsoluteCutoff m J x| ≤ 1 := by sorry

/-- Paper: Definition 9.3.3.3, p. 428. The absolute cutoff operator is
multiplication by the indicator of the chosen set of module values. -/
def modulatedAbsoluteCutoffOperator (ν : Measure G) (J : Set ℝ) (hJ : MeasurableSet J) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  lpCutoffMultiplier ν (modulatedAbsoluteCutoff m J)
    (modulatedAbsoluteCutoff_measurable_bounded m J hJ).1
    (modulatedAbsoluteCutoff_measurable_bounded m J hJ).2

/-- Paper: (9.3.3.6)–(9.3.3.7), p. 428. The absolute cutoff retains the input
on the chosen band and vanishes outside it, as an identity of L² representatives. -/
theorem modulatedAbsoluteCutoffOperator_apply (ν : Measure G) (J : Set ℝ)
    (hJ : MeasurableSet J) (u : Lp ℂ 2 ν) :
    (modulatedAbsoluteCutoffOperator m ν J hJ u : G → ℂ) =ᵐ[ν]
      fun x ↦ (modulatedAbsoluteCutoff m J x : ℂ) * u x := by sorry

-- TODO(paper-gap): Remark 9.3.3.4 calls the projectors injective and their symbols
-- bounded below away from zero almost everywhere. Each one-sided cutoff kills
-- functions supported on its excluded half of the module axis.
-- The two-sided cutoff is zero almost everywhere for Λ ≤ 1 on the positive reals.

end Cutoffs

variable (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
variable (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
  (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
variable {Λ ε : ℝ} {ρ : G → ℝ}

local notation "A" => hardySobolevConvolution μ m a b s hab hs φ hφ hc hb
local notation "truncation" => modulatedCutoffOperator m (weightedMeasure a b s)

-- TODO(paper-gap): Theorem 9.3.3.5(1) assumes neither measurability of φ nor
-- existence of a differentiation limit at the identity. The diagonal smoothening
-- can fail for a bounded Borel φ oscillating on sufficiently separated annuli.

/-- Paper: Theorem 9.3.3.5(1), p. 429. Truncated convolution is Hilbert–Schmidt
and is represented by the displayed square-integrable kernel.
Deviation: This retains the Hilbert–Schmidt conclusion for measurable symbols
on compact base intervals. The source density in the denominator accounts for
integration against the weighted measure. -/
theorem truncatedHardySobolevConvolution_hilbertSchmidt
    (_hm : IsModulation m) (_hms : Surjective m)
    (hρ : IsModulatedCutoff m Λ ε ρ) (_hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let ν := weightedMeasure a b s
    let k : G × G → ℂ := fun p ↦
      (ρ p.1 : ℂ) * φ (p.1 * p.2⁻¹) / (weightDensity a b s p.2 : ℂ)
    (truncation hρ).comp A ∈ hilbertSchmidtOperators (W a b s) (W a b s) ∧
      MemLp k 2 (ν.prod ν) ∧
      ∀ u : W a b s, ∀ᵐ x ∂ν,
        Integrable (fun y ↦ k (x, y) * u y) ν ∧
          (truncation hρ).comp A u x = ∫ y, k (x, y) * u y ∂ν := by sorry

/-- Paper: Theorem 9.3.3.5(2), p. 429. For smooth compactly supported symbols
and smooth cutoffs, the truncated convolution operator is nuclear, and its trace
equals the integral over the diagonal.
Deviation: The diagonal is written relative to Haar measure after the weighted L²
density cancels. The base interval is compact, as in the available Hilbert model. -/
theorem truncatedHardySobolevConvolution_trace
    (_hm : IsModulation m) (_hms : Surjective m)
    (hφsmooth : IsBruhatSmooth φ) (hρ : IsSmoothModulatedCutoff m Λ ε ρ)
    (_hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let T := (truncation hρ.1).comp A
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * φ 1) μ ∧
      hilbertTrace ⟨T, hT⟩ = ∫ x, (ρ x : ℂ) * φ 1 ∂μ := by sorry

-- TODO(paper-gap): Theorem 9.3.3.5(3) uses a point value and the nuclear trace.
-- For general bounded symbols the point value can change without affecting convolution.

/-- Paper: Theorem 9.3.3.5(3), p. 429. For the smooth trace in part (2), the
difference from twice the logarithmic radius times the kernel Haar mass and φ(1)
tends to zero if εΛ tends to zero.
Deviation: This takes the nuclear trace under the smoothness hypotheses of part (2).
A Haar splitting makes the normalization of the kernel Haar measure explicit. The
base interval is compact. -/
theorem truncatedHardySobolevConvolution_trace_tendsto
    (_hm : IsModulation m)
    (_hφsmooth : IsBruhatSmooth φ)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (_hμ : μ = (μ₁.prod positiveRealHaar).map
      (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ)
    (_hε : Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0))
    (_hρlim : ∀ x, Tendsto (fun Λ ↦ ρ Λ x) atTop (𝓝 1))
    (_hcutoff : ∀ᶠ Λ in atTop, IsSmoothModulatedCutoff m Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ Λ in atTop, ∃ (hρ : IsSmoothModulatedCutoff m Λ (ε Λ) (ρ Λ)),
        let T := (truncation hρ.1).comp A
        ∃ hT : IsNuclearOperator T, traces Λ = hilbertTrace ⟨T, hT⟩) ∧
      Tendsto (fun Λ ↦ traces Λ - (2 * Real.log Λ * μ₁.real univ : ℝ) * φ 1)
        atTop (𝓝 0) := by sorry

end Trace

end RiemannMasullo
