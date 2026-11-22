module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

/-! # §7.3.1 Statements that are false as printed -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 3

local notation "chart(" field ", " places ", " χ ")" =>
  quasiCharacterNormTwist (sIdeleQuotientNorm field places)
  (isProperMap_sIdeleQuotientNorm field places).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "period(" places ", " v ")" =>
  (2 * Real.pi / Real.log ((v : places).val.asIdeal.absNorm : ℝ))
local notation "phase(" field ", " places ", " χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(places, v) ∧
    sLocalFiniteRestriction v (chart(field, places, χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" field ", " places ", " v ", " u ")" =>
  (‖(↑(u) : (v : places).val.adicCompletion field)‖ = ((v : places).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Theorem 7.3.1.2(2), p. 341.
Each listed coefficient is called an eigendistribution of its center. The finite
sets S and T specify the finite parts of the printed S and S₀, both of which
contain all infinite places. Pullback to tests expresses the weight equation. -/
def Printed.sLocalOrbitalPrincipalParts_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F))),
    IsSaturatedPlaceSet S →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) → T ⊆ S →
    ∀ (ω : PontryaginDual (sIdeleQuotientNorm F S).ker) (c : QuasiCharacter (SIdeleQuotient F S)),
      normOneRestriction (sIdeleQuotientNorm F S) c =
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω →
      0 < sLocalRhoPoleOrder c →
      ∀ k : ℕ, sLocalRhoPoleOrder c - ((sLocalArchPolePlaces c).card +
          sLocalFinitePoleMultiplicity T c) < k → k ≤ sLocalRhoPoleOrder c →
        sLocalPrincipalPartCoeff c k ∈ sLocalEigendistributions c

/-- Paper: Theorem 7.3.1.2(2), p. 341.
For ℚ take S = {∞,2,3}, S₀ = {∞,2}, and c = 1. The real Gaussian times the
integer indicators has a triple pole with leading coefficient 2/(log 2 · log 3).
Dilation of norm 2 multiplies the zeta germ by 2^s and changes the selected
second-order coefficient by (log 2) times the leading coefficient. -/
theorem Printed.sLocalOrbitalPrincipalParts_eigendistributions_false :
    ¬ Printed.sLocalOrbitalPrincipalParts_eigendistributions := by sorry

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phases at two places over the same rational prime differ by a unique
integer multiple of the period for that prime. The integer norm of the rational place is p. -/
def Printed.sLocalOrbitalPhase_sub : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let Jₛ := SIdeleQuotient F S
    IsSaturatedPlaceSet S →
    ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (χ : PontryaginDual Jₛ) (v w : S),
      v.val ∈ sLocalPrimaryPlaces S p → w.val ∈ sLocalPrimaryPlaces S p →
      ∀ (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ),
        uniformizerNorm(F, S, v, uᵥ) → uniformizerNorm(F, S, w, u_w) →
        ∀ (tᵥ t_w : ℝ), phase(F, S, χ, v, uᵥ, tᵥ) → phase(F, S, χ, w, u_w, t_w) →
          ∀ c : QuasiCharacter Jₛ, (∃ s, c = chart(F, S, χ) s) →
            v ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            w ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            ∃! n : ℤ, tᵥ - t_w = (n : ℝ) * (2 * Real.pi / Real.log (p.asIdeal.absNorm : ℝ))

/-- Paper: Discussion after (7.3.1.11), p. 344.
Take F = ℚ(∛2), p = 5, and S consisting of the places over 5 together with the archimedean
places. Modulo 5, X³ - 2 factors as (X - 3)(X² + 3X + 4), with irreducible quadratic
and discriminant of X³ - 2 prime to 5. The local residue sizes are 5 and 25.
With T = 2π/log 5 and χ = |·|^(3iT/4), take the common pole c = 1.
The local phases are 3T/4 and T/4, so their difference is T/2. -/
theorem Printed.sLocalOrbitalPhase_sub_false : ¬ Printed.sLocalOrbitalPhase_sub := by sorry

open Classical in
/-- Paper: Definition 7.3.1.4, equations (7.3.1.6)–(7.3.1.7), p. 343.
As printed: on the primary pole locus, the natural-number count of contributing
places equals the sum of the signed meromorphic orders of the restricted local
Tate factors. See `sLocalPrimaryPoleMultiplicity` and ERRATA F119. -/
def Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 ℚ)),
    IsSaturatedPlaceSet S → (sLocalPrimaryPlaces S p).Nonempty →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ c : QuasiCharacter (SIdeleQuotient F S),
      0 < sLocalPrimaryPoleMultiplicity p c →
      let twist := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous c
      ((sLocalPrimaryPoleMultiplicity p c : ℤ) : WithTop ℤ) =
        ∑ v ∈ S.attach.filter (fun v ↦ v.val ∈ sLocalPrimaryPlaces S p),
          meromorphicOrderAt
            (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (twist z))) 0

/-- Paper: Definition 7.3.1.4, equations (7.3.1.6)–(7.3.1.7), p. 343.
Take F = ℚ, S with just the finite place over 2, p = 2, and c = 1.
The local numerator has a simple pole and the reflected denominator is
regular and nonzero at c, giving signed order −1. The primary count is 1. -/
theorem Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders_false :
    ¬ Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders := by sorry

end RiemannMasullo
