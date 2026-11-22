module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a

/-! # Chapter 5.3: printed properties of the local difference -/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField Set

local notation "Fᵥ[" F "," v "]" => HeightOneSpectrum.adicCompletion F v
local notation "vval[" F "," v "]" =>
  (Valued.v : Valuation Fᵥ[F, v] (WithZero (Multiplicative ℤ)))

/-- Paper: Lemma 5.3.1.1, p. 240. As printed: at every finite place of every
number field the difference on the full local Schwartz–Bruhat space is independent
of the choice of uniformizer, and its range is the kernel of evaluation at zero.
These are the independence and range clauses. See `finitePlaceDifference_eq_of_unitInvariant`,
`finitePlaceDifference_range_on_unitInvariants`, and ERRATA F213. -/
def Printed.finitePlaceDifference_uniformizerIndependent_and_range : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : Fᵥ[F, v]ˣ), vval[F, v].IsUniformizer π.val →
    (∀ (π' : Fᵥ[F, v]ˣ), vval[F, v].IsUniformizer π'.val →
      finitePlaceDifference v π = finitePlaceDifference v π') ∧
    range (finitePlaceDifference v π) = {f | f (Multiplicative.ofAdd 0) = 0}

/-- Paper: Lemma 5.3.1.1, p. 240. At the place 3 of ℚ take f to be the
indicator of 1 + 3ℤ₃. The differences for the uniformizers 3 and −3 give
values −1 and 0 at 3. The function f vanishes at zero. For any uniformizer π,
an equation f = Pᵥ(h) forces h(x) = Σ_{j ≥ 0} f(π^(-j)x) for x ≠ 0 by
telescoping and compact support. It follows that h(πʲ) = 1 and h(2πʲ) = 0
for all j ≥ 0, contradicting local constancy at zero. -/
theorem Printed.finitePlaceDifference_uniformizerIndependent_and_range_false :
    ¬ Printed.finitePlaceDifference_uniformizerIndependent_and_range := by sorry

end RiemannMasullo
