module

public import RiemannMasullo.Ch08_PeriodicOrbits.Sec1

/-! # Printed claims from §8.1 that fail -/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set
open scoped BigOperators NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 1000000

universe u

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "J₁(" F ", " S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "PicTrivial(" F ", " S ")" => Subsingleton (CommRing.Pic ((S : Set V(F)).integer F))
local notation "fullFibre(" S ", " p ")" => (∀ v ∉ S, HeightOneSpectrum.under (𝓞 ℚ) v ≠ p)
local notation "zeroExtension(" g ")" => Function.extend Units.val g (fun _ ↦ 0)

local notation "pureTensorsExtend(" F ", " S ", " T ")" =>
  (∀ (a : sLocalOrbitalArchimedeanFlatTests F)
    (g : ∀ v : {v : S // v.val ∈ T}, ℬ(v.val.val.adicCompletion F))
    (h : ∀ v : {v : S // v.val ∉ T}, SchwartzBruhat (v.val.val.adicCompletion F)ˣ),
    ∃ f : ℬ(SAdeleRing F S), ∀ (x : SAdeleRing F S),
      f (Multiplicative.ofAdd x) = a.val (Multiplicative.ofAdd x.1) *
        (∏ v : {v : S // v.val ∈ T}, g v (Multiplicative.ofAdd (x.2 v.val))) *
        (∏ v : {v : S // v.val ∉ T}, zeroExtension(h v) (x.2 v.val)))

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.2), p. 382.
The printed inclusion says in particular that every pure tensor with full
multiplicative Schwartz factors outside the primary fibre extends by zero to an
additive S-adelic Schwartz–Bruhat test. -/
def Printed.sLocalPrimaryOrbitalSupportTests_inclusion : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (p : Vℚ),
    fullFibre(S, p) → PicTrivial(F, S) →
    ∀ (ω : PontryaginDual C₁(F)), NormOneCharacterUnramifiedOutside ω S →
      pureTensorsExtend(F, S, sLocalPrimaryPlaces S p)

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.2), p. 382.
Use ℚ with S = {∞, 2, 3}, p = 2 and the trivial character. Use a nonzero smooth
real test supported in (1, 2), the indicator of ℤ₂, and the multiplicative 3-adic
test h(3ᵏu) = exp(−k²) for k ∈ ℤ and u ∈ ℤ₃ˣ. At a point where the real test is
nonzero and the 2-adic coordinate is 1, the zero extension of the product fails
local constancy at the 3-adic origin. See ERRATA R11. -/
theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false :
    ¬ Printed.sLocalPrimaryOrbitalSupportTests_inclusion.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.4), p. 382.
The printed inclusion says in particular that every pure tensor with full
multiplicative Schwartz factors away from v extends by zero to an additive
S-adelic Schwartz–Bruhat test. -/
def Printed.sLocalPlaceOrbitalSupportTests_inclusion : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (v : S),
    PicTrivial(F, S) →
    ∀ (ω : PontryaginDual C₁(F)), NormOneCharacterUnramifiedOutside ω S →
      pureTensorsExtend(F, S, ({v.val} : Finset V(F)))

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.4), p. 382.
Use ℚ with S = {∞, 2, 3}, v = 2 and the trivial character. Take a nonzero smooth
real test supported in (1, 2), the indicator of ℤ₂, and the unit-invariant
3-adic test with profile k ↦ exp(−k²). The 3-adic slice is nonzero on 3ᵏ for
every k, but zero at the origin, so it fails local constancy there. -/
theorem Printed.sLocalPlaceOrbitalSupportTests_inclusion_false :
    ¬ Printed.sLocalPlaceOrbitalSupportTests_inclusion.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.1), p. 382.
The canonical primary comparison is a continuous linear equivalence.
Deviation: This gives the isomorphism assertion after the test-space and source
denominator corrections, so that the comparison is defined. -/
def Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (p : Vℚ),
    fullFibre(S, p) → PicTrivial(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S),
      let T := sLocalPrimaryPlaces S p
      let hT := sLocalPrimaryPlaces_subset S p
      let η := sLocalNormOneCharacter S ω hω
      ∃ e : (↥(sLocalOrbitalSupportTests S T) ⧸ sLocalOrbitalSupportRelations hT η)
          ≃L[ℂ] SLocalPrimaryOrbitalQuotient p η,
        e.toLinearMap = (sLocalOrbitalSupportComparison hT η).toLinearMap

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.1), p. 382.
For ℚ with S = {∞, 2}, p = 2 and the trivial character, the zeta transform
of the real Gaussian times 1_{ℤ₂} has a double pole at zero. Restricted tests
have at most a simple pole there, and PV₂ lowers the pole order by one.
Thus this Gaussian class lies outside the comparison's range. -/
theorem Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism_false :
    ¬ Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.3), p. 382.
The canonical single-place comparison is a continuous linear equivalence.
Deviation: This gives the isomorphism assertion after the test-space and source
denominator corrections, so that the comparison is defined. -/
def Printed.sLocalPlaceOrbitalSupportComparison_isomorphism : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (v : S),
    PicTrivial(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S),
      let T : Finset V(F) := {v.val}
      let hT : T ⊆ S := Finset.singleton_subset_iff.mpr v.property
      let η := sLocalNormOneCharacter S ω hω
      ∃ e : (↥(sLocalOrbitalSupportTests S T) ⧸ sLocalOrbitalSupportRelations hT η)
          ≃L[ℂ] (SLocalHomogeneousThetaSpace F S η ⧸
            (sLocalHomogeneousThetaPrincipalValue hT η).range),
        e.toLinearMap = (sLocalOrbitalSupportComparison hT η).toLinearMap

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.3), p. 382.
For ℚ with S = {∞, 2}, v = 2 and the trivial character, the real Gaussian
times 1_{ℤ₂} gives the same double-pole obstruction as in part (1). -/
theorem Printed.sLocalPlaceOrbitalSupportComparison_isomorphism_false :
    ¬ Printed.sLocalPlaceOrbitalSupportComparison_isomorphism.{u} := by sorry

end RiemannMasullo
