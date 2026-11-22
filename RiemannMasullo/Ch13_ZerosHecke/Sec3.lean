module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # The divisor of the Hecke L-function

Masullo, §13.3.1, p. 522. The two sides of the proposed trace formula are
continuous on the Mellin-jet test subspace. The printed equality and codimension
claim are recorded in `Sec3_Printed.lean`.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "sectionCharacters(" τ ")" => {χ : U𝔽 // ∀ t, χ (τ t) = 1}

-- TODO(paper-gap): §§13.1 and 13.2 are headings with no text on p. 522.
-- TODO(paper-gap): Footnote 1 to Theorem 13.3.1.1 says “Correct statement.” The
-- cited `traceFormula` uses a positive-width strip, full zero orders and tests
-- vanishing on the norm-one classes. The manuscript gives no derivation of the
-- changes to the zero weights, test space or local coefficients.

/-- Paper: (13.3.1.1), p. 522. The spectral multiplicity is the order of the
completed Hecke zero capped at the degree of the number field. -/
def criticalTraceMultiplicity (χ : U𝔽) (s : ℂ) (_hs : 0 < ord(χ, s)) : ℕ :=
  min (ord(χ, s)).toNat (Module.finrank ℚ F)

/-- Paper: (13.3.1.1), p. 522. A zero whose order exceeds the field degree is
counted with weight equal to the degree. -/
theorem criticalTraceMultiplicity_of_degree_le (χ : U𝔽) (s : ℂ) (hs : 0 < ord(χ, s))
    (_h : Module.finrank ℚ F ≤ (ord(χ, s)).toNat) :
    criticalTraceMultiplicity χ s hs = Module.finrank ℚ F := by sorry

local notation "momentIntegrand(" χ ", " k ", " φ ")" =>
  (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g)

/-- Paper: (13.3.1.2), p. 522. A fixed character and jet order give a linear
functional by integration against the character times a power of the log norm. -/
theorem criticalTraceMoment_isLinearMap (χ : U𝔽) (k : ℕ) :
    IsLinearMap ℂ (fun φ : D𝔽 ↦ ∫ g, momentIntegrand(χ, k, φ) g ∂μ𝔽) := by sorry

/-- Paper: (13.3.1.2), p. 522. The test subspace is the common kernel of the
first `[F : ℚ]` log-norm moments for each unitary character trivial on the section.
Deviation: The degree bounds the jet orders in each character, with no finite
codimension imposed on the common kernel. -/
def criticalTraceTestSubmodule (τ : ℝ≥0ˣ →ₜ* C𝔽) : Submodule ℂ D𝔽 :=
  ⨅ (χ : sectionCharacters(τ)) (k : Fin (Module.finrank ℚ F)),
    ((criticalTraceMoment_isLinearMap χ.val k.val).mk' _).ker

/-- Paper: (13.3.1.2), p. 522. Membership in the test subspace is equivalent to
the printed Mellin-derivative conditions at `−i x₀(χ)` for all unitary characters.
The continuous norm section and the exponent along it are given explicitly. -/
theorem mem_criticalTraceTestSubmodule_iff (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : D𝔽) :
    φ ∈ criticalTraceTestSubmodule τ ↔
      ∀ (χ : U𝔽) (x : ℝ),
        (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)) →
        ∀ k : Fin (Module.finrank ℚ F),
          iteratedDeriv k.val (fun s : ℂ ↦
            ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s *
              (∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ)
                ∂normOneIdeleClassTamagawaMeasure F) ∂positiveRealHaar)
            (-((x : ℂ) * Complex.I)) = 0 := by sorry

/-- Paper: Theorem 13.3.1.1, p. 522. The rational Mellin-jet test subspace has
codimension at least two, as witnessed by the trivial character and the character
modulo four on the norm-one classes.
Deviation: This replaces the printed codimension one over `ℚ` by a lower bound. -/
theorem criticalTraceTestSubmodule_rat_codimension_ge_two
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (_hτ : RightInverse τ (ideleClassNorm ℚ)) :
    2 ≤ Module.rank ℂ (BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ) ⧸
      criticalTraceTestSubmodule τ) := by sorry

local notation "lineZeros(" τ ")" =>
  {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2) ∧ z.2.re = 1 / 2}
local notation "mellinAt(" φ ", " χ ", " s ")" =>
  (∫ g : C𝔽, (φ : D𝔽).val g * ideleClassNormTwist (F := F) χ s g ∂μ𝔽)
local notation "zeroTerm(" φ ", " z ")" =>
  ((criticalTraceMultiplicity (z).val.1.val (z).val.2 (z).property.1 : ℂ) *
    mellinAt(φ, (z).val.1.val, (z).val.2 - 1 / 2))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3), p. 522. The capped zero sum over the
critical line converges and gives a continuous linear functional on the test subspace.
Deviation: A norm section lists each quasi-character once by a unitary character
trivial on the section and a complex norm exponent. -/
theorem criticalTraceSpectral_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        HasSum (fun z : lineZeros(τ) ↦ zeroTerm(φ.val, z)) (L φ) := by sorry

local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b)
local notation "finiteUnitMass(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F (v : V)
    (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℂ)
local notation "archTests" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTests" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "restrictsAtInfinity(" a ", " φ ")" =>
  (∀ w u, ((a : archTests) w).val u = (φ : D𝔽).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "restrictsAtFinite(" b ", " φ ")" =>
  (∀ v u, ((b : finiteTests) v).val u = (φ : D𝔽).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. The finite-place
series converges, and the polar terms minus the local principal values form a
continuous linear functional on the test subspace. The local tests are pulled back
along the maps from the local multiplicative groups to the idele classes. -/
theorem criticalTraceGeometric_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        ∃ (a : archTests) (b : finiteTests),
          restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
          HasSum (fun v : V ↦ finiteTerm(v, b v))
            (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
              (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L φ) := by sorry

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. On the Mellin-jet
test subspace the full zero divisor pairs against the test by the idelic explicit formula.
Deviation: This is the restriction of `idelicExplicitFormula` to the jet subspace.
It sums all completed zeros with full orders and uses the norm-one Tamagawa volume and
the canonical local factors. The capped critical-line equality is refuted in `Sec3_Printed.lean`. -/
theorem hasSum_fullDivisor_on_criticalTraceTests (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : criticalTraceTestSubmodule τ) :
    let zeros := {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2)}
    let classVolume := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
    ∃ (a : archTests) (b : finiteTests),
      restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v) / finiteUnitMass(v)) ∧
      HasSum (fun z : zeros ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
          mellinAt(φ.val, z.val.1.val, z.val.2 - 1 / 2))
        (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) - classVolume *
          ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v))) := by sorry

-- TODO(paper-gap): The inference to the divisor statement cites “Theorem ??”
-- without identifying the theorem to be combined with Theorem 13.3.1.1.
-- TODO(paper-gap): Theorem 13.3.1.2 has only a title. Footnotes 2 and 3 ask for
-- the statement, proof, and an approximation by tests tending to e^(−s|log t|)
-- for Re(s) > 1.

end RiemannMasullo
