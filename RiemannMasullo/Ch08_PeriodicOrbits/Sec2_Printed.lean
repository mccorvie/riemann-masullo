module

public import RiemannMasullo.Ch08_PeriodicOrbits.Sec2

/-! # §8.2. Statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField Topology
open scoped NNReal NumberField.AdeleRing

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global norm-one orbit map is a quotient map
for the adelic subspace topology on the target. See ERRATA R12. -/
def Printed.adeleNormOneOrbitMap_isQuotientMap : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F], IsQuotientMap (adeleNormOneOrbitMap F)

/-- Paper: Lemma 8.2.0.3(2), p. 385. Over ℚ, let U be the norm-one orbit points
with real component zero and all finite components in the local unit groups.
The preimage of U is open because the real-zero base point is isolated among the
base points and the integral finite ideles form an open subgroup. Replacing the
p-coordinate of the real-zero base point by p gives points outside U that tend
to that base point. They are norm-one translates via ideles with real coordinate p. -/
theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false :
    ¬ Printed.adeleNormOneOrbitMap_isQuotientMap.{0} := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally
compact in the adelic subspace topology. See ERRATA R13. -/
def Printed.adeleNormOneOrbitUnion_locallyCompactSpace : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F], LocallyCompactSpace (adeleNormOneOrbitUnion F)

/-- Paper: Lemma 8.2.0.3, p. 385. Over ℚ, take the real-zero base point. In any
basic neighbourhood choose infinitely many distinct unrestricted primes p₁, p₂, …
and replace the components at p₁, …, pₙ by p₁, …, pₙ. These are norm-one translates
using ideles with real coordinate p₁⋯pₙ. Their limit in the adeles has infinitely
many finite nonunit components and lies outside the orbit union. A compact
neighbourhood would be closed in the ambient Hausdorff space and contain this limit. -/
theorem Printed.adeleNormOneOrbitUnion_locallyCompactSpace_false :
    ¬ Printed.adeleNormOneOrbitUnion_locallyCompactSpace.{0} := by
  sorry

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point of the full S-local
finite-place orbit admits a full-idele transporter into the half-open section,
unique up to embedded local valuation-ring units. See ERRATA R1. -/
def Printed.sAdeleFiniteOrbit_transporter : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (v : S)
    (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ), Continuous τ → RightInverse τ (sIdeleNorm F S) →
    ∀ x ∈ sAdeleFullOrbit F S (some (.inr v)),
      ∃ g : (SAdeleRing F S)ˣ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
        ∀ h : (SAdeleRing F S)ˣ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
          g⁻¹ * h ∈ (embeddedFiniteLocalUnits F v.val).map
            (Units.map (adeleProjection F S).toMonoidHom)

/-- Paper: Proposition 8.2.0.4(1), p. 386. Over ℚ take the real and 2-adic places,
the section t ↦ (t, 1), and x = (1, 0). Both (1, 1) and (1, 2) are transporters
because they fix x and x is at the included left endpoint. Their ratio has
2-adic component 2, which fails to be a valuation-ring unit. -/
theorem Printed.sAdeleFiniteOrbit_transporter_false :
    ¬ Printed.sAdeleFiniteOrbit_transporter.{0} := by
  sorry

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point of the full global
finite-place orbit admits a full-idele transporter into the half-open section,
unique up to embedded local valuation-ring units. See ERRATA R1. -/
def Printed.adeleFiniteOrbit_transporter : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ), Continuous τ → RightInverse τ (ideleNorm F) →
    ∀ x ∈ adeleFullOrbit F (some (.inr v)),
      ∃ g : 𝔸[F]ˣ, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
        ∀ h : 𝔸[F]ˣ, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
          g⁻¹ * h ∈ embeddedFiniteLocalUnits F v

/-- Paper: Proposition 8.2.0.4(2), p. 386. Over ℚ take the norm section with real
coordinate t and finite coordinates 1, and take x to be the 2-adic-zero base
point. Both 1 and the idele with 2-adic coordinate 2 and all other coordinates 1
fix x at the included left endpoint. Their ratio is outside the embedded local
valuation-ring units. -/
theorem Printed.adeleFiniteOrbit_transporter_false :
    ¬ Printed.adeleFiniteOrbit_transporter.{0} := by
  sorry

end RiemannMasullo
