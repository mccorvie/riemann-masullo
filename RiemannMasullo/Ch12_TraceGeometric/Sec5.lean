module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Trace formula: the Main Theorem

Masullo, §12.5, pp. 519–520. Zeros of the completed Hecke L-functions are listed
through a norm section, as in Theorem B.4.4.7: a quasi-character c = χ|·|^s with
χ trivial on the section has abscissa σ(c) = Re s.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "interiorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b

local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}

local notation "traceIdentity(" τ ", " φ ", " α ")" =>
  (∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = (φ).val (archClass(w) u)) ∧
      (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u = (φ).val (finiteClass(v) u)) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v)) ∧
      HasSum (fun z : interiorZeros(τ, α) ↦ zeroTerm(φ, z))
        (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
          classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v))))

-- Page 519 introduces tests with φ(1) = 0 and states the theorem for φ(C_F¹) = 0.
-- TODO(paper-gap): Page 520 leaves χ free. Theorem 11.3.2.1 also requires
-- support above norm one. In (11.3.1.4), the signed differences sum to the
-- S-local restriction minus the original kernel. A quotient lift and comparison
-- of the separate shell integrals are missing (ERRATA I292).
-- TODO(paper-gap): Theorem 12.4.1.1 divides by the S-local norm-one volume.
-- Section 12.3 lacks the comparison of this local limit with the global Haar
-- diagonal and the two polar Mellin terms (ERRATA M25).

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For a test vanishing on the norm-one
classes, the zero terms omitted by a positive-width open strip sum to zero.
Gap: The global to S-local comparison on p. 520 must account for every omitted
zero, including zeros on the edges. The all-zero identity of Theorem B.4.4.7
alone gives no such cancellation. -/
theorem traceFormula_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (_hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 := by sorry

/-- Paper: Theorem B.4.4.7, p. 623, applied to Theorem 12.5.1.1, pp. 519–520.
Evaluating the full explicit formula at a test and removing a zero subseries of
sum zero gives the strip identity. -/
theorem traceFormula_of_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (α : ℝ)
    (_hTail : HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) :
    traceIdentity(τ, φ, α) := by sorry

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For compactly supported Bruhat tests
vanishing on the norm-one classes, the pole terms minus the interior zero sum
equal the global norm-one volume times the sum of the local principal values.
Deviation: The half-width is positive as in §1.8.4, p. 53. The global volume
and the normalized complex denominator ‖1 − u‖² follow Theorem B.4.4.7 and
(12.4.1.26). The all-width conclusion uses `traceFormula_exteriorZeros`. -/
theorem traceFormula (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α) :
    traceIdentity(τ, φ, α) :=
  traceFormula_of_exteriorZeros τ hτ φ α (traceFormula_exteriorZeros τ hτ φ hφ hα)

section SmoothenedDiagonal

local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripTensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))

local notation "geomDiagonal(" hα ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x, x))
local notation "quotientTrace(" hα ", " hs ", " φ ")" =>
  (hilbertTrace (H := spectralSobolevQuotient F (1 / 2) (hStrip(hα)) hs₀(hs))
    ⟨spectralConvolution (F := F) (1 / 2) (hStrip(hα)) hs₀(hs) φ,
      spectralStripConvolution_nuclear (F := F) (1 / 2) hα hs₁(hs) φ⟩)

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is
Haar-integrable and its integral is minus the strip quotient trace.
Gap: Theorem 10.4.2.8 gives a cutoff trace limit. Identifying it with this
Haar diagonal requires the input Sobolev weight and justification for
removing the cutoff (ERRATA I341 and I351).
Deviation: Definition 10.4.3.7 uses the tensor for convolution after projection.
The right side is the trace computed by `spectralStripConvolution_trace`. It
counts the closed strip with `spectralStripMultiplicity`. When the two edges
contain no zeros this recovers the interior sum in (12.5.1.4). -/
theorem integral_smoothenedStripGeometricKernel_diagonal (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ g : C₁, φ.val g = 0) {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable geomDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧
      (∫ x, geomDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽) = -quotientTrace(hα.le, hs, φ) := by sorry

end SmoothenedDiagonal

end RiemannMasullo
