module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch11_ShellStructure.Sec3

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch11_ShellStructure.Sec1a

/-! # False printed claims from §11.3 -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instIdeleMeasurableSpaceSec1a instMeasurableSpaceAdicUnitsSec3a

/-- Paper: §11.3.1.1, p. 493. As printed, every primary stratum is the full
preimage of its rational stratum under the relative idelic norm. -/
def Printed.primaryDivisorialStratum_eq_norm_preimage : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v ∈ S, ∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
    ∀ k : ℕ, divisorialStratum F (primaryDivisorialPlaces F S k) =
      (relativeIdeleNormRat F) ⁻¹'
        divisorialStratum ℚ ((Finset.range k).image (primaryDivisorialPrime S))

/-- Paper: §11.3.1.1, p. 493. Take F = ℚ(i), exclude the fibre over 2 and
use the stage with rational primes 3 and 5. At the two places over 5 take
components 5 and 5⁻¹ respectively and put one at every other place.
The rational norm is the identity, although neither component over 5 is a unit. -/
theorem Printed.primaryDivisorialStratum_eq_norm_preimage_false :
    ¬ Printed.primaryDivisorialStratum_eq_norm_preimage := by sorry

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "I(" F ")" => IdeleGroup (𝓞 F) F
local notation "C(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "N(" F ")" => (ideleNorm F).ker
local notation "classOf(" F ")" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "above(" F ", " p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "πclass(" F ", " v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "unitMass(" F ", " v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v).real ((v).adicCompletionIntegers F).units
local notation "ramificationIndex(" v ")" => (v).asIdeal.ramificationIdx (𝓞 ℚ)

/-- Paper: §11.3.1.1(2), p. 494. As printed, the Poisson evaluation of
the half-shifted Euler-zero sum uses unweighted point evaluations at powers
of the uniformizers. The prime lies outside the base of p. 491, so it is
unramified in the field and the character is unramified above it. -/
def Printed.orbitalEulerSum_eq_poisson : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C(F))
    (φ : BruhatCompactSupport C(F)) (p : Vℚ),
    (∀ v ∈ above(F, p), ramificationIndex(v) = 1) →
    (∀ v ∈ above(F, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ π : ∀ v : V(F), (v.adicCompletion F)ˣ,
      (∀ v ∈ above(F, p), Valued.v.IsUniformizer (π v : v.adicCompletion F)) →
      let zeros := {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(F, p) z = 0}
      HasSum (fun z : zeros ↦ (orbitalEulerMultiplicity χ above(F, p) z.val : ℂ) *
        nuclearityTestMellin χ φ (z.val - 1 / 2))
        (∑ v ∈ above(F, p), (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(F, v) : ℂ) *
          ∑' n : ℤ, φ.val (πclass(F, v, π v) ^ n))

/-- Paper: §11.3.1.1(2), p. 494. Over ℚ take the trivial character, the
prime 2 and a radial bump supported at norms in (3/2, 5/2) with value one
at 2. There is just one point evaluation, at the inverse uniformizer.
The local unit mass and the norm-one class mass are both one. The half
shift weights the Poisson value by 2⁻¹ᐟ², which the printed sum omits. -/
theorem Printed.orbitalEulerSum_eq_poisson_false :
    ¬ Printed.orbitalEulerSum_eq_poisson := by sorry

/-- Paper: Theorem 11.3.2.1, (11.3.2.1)–(11.3.2.2), p. 495.
The printed orbital integral uses the section weight and equates a layer
to the term for its displayed place.
Deviation: Bind the displayed place in the indicated layer. Make existence
of the spectral tensor used to specify the §10.4 strip kernel explicit.
The counterexample uses a layer consisting of a single place. -/
def Printed.orbitalTracesOnPaleyWienerLevels : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C(F))
    (φ : BruhatCompactSupport C(F)) (S : Finset V(F)),
    (∀ v ∈ S, ∀ w : V(F), w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
    (∀ v ∉ S, ramificationIndex(v) = 1) →
    (∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    (∀ u : outsideIntegralIdeleUnits F S, ∀ x : C(F), φ.val (classOf(F) u.val * x) = φ.val x) →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    tsupport φ.val ⊆ {x : C(F) | 1 < ((ideleClassNorm F x).val : ℝ)} →
    ∀ (s α : ℝ) (hs : 1 < s) (hα : 0 ≤ α) (τ : ℝ≥0ˣ →* I(F)),
      Continuous τ → RightInverse τ (ideleNorm F) →
      ∀ (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
        (w : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : CommRing.Pic (𝓞 F) → N(F)),
        r 1 = 1 → (∀ c, ideleIdealClass F (r c).val = c) →
        ∀ (k : ℕ) (v : V(F)),
          v ∈ primaryDivisorialPlaces F S (k + 1) \ primaryDivisorialPlaces F S k →
          ∀ (π : (v.adicCompletion F)ˣ), Valued.v.IsUniformizer (π : v.adicCompletion F) →
            ∃ hK,
              let K := globalStripGeometricKernel (F := F) (1 / 2) hα hs φ hK
              let E := ideleFundamentalDomain F b w σ r
              let lift := fun xy : I(F) × I(F) ↦
                (orbitalSectionWeight E τ xy : ℂ) * K (classOf(F) xy.1, classOf(F) xy.2)
              (∑' ξ : Fˣ, ∫ t, ∫ g in E,
                divisorialKernelDifference S k lift
                  (τ t, IdeleGroup.unitEmbedding (𝓞 F) F ξ * g.val * τ t)
                ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
                (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(F, v) : ℂ) *
                  ∑' n : ℤ, φ.val (πclass(F, v, π) ^ n)

/-- Paper: Theorem 11.3.2.1, p. 495. Take F = ℚ, the trivial character,
the archimedean base, the standard norm section and the first layer at 2.
Choose a nonnegative smooth log-norm bump with value one at norm 2,
supported at norms in (3/2, 5/2). The section weight is zero everywhere,
while the single place on the right contributes log 2. -/
theorem Printed.orbitalTracesOnPaleyWienerLevels_false :
    ¬ Printed.orbitalTracesOnPaleyWienerLevels := by sorry

end RiemannMasullo
