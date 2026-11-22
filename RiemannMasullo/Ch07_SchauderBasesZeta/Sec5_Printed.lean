module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec5

/-! # False claims printed in §7.5 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option Elab.async false

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "ω[" F ", " χ "]" => (χ : U[F]).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C[F])

/-- Paper: Theorem 7.5.0.1, p. 374.
The printed quotient map is a topological linear isomorphism with a translation
difference for every selected finite place. -/
def Printed.strongCoprimality : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (S : Finset V[F])
    (π : (v : V[F]) → (v.adicCompletion F)ˣ),
    (∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) →
    let ω := ω[F, χ]
    let j := (exists_strongCoprimalityThetaEmbedding ω).choose
    let D := strongCoprimalityDenominator ω S
    let E := strongCoprimalityDifferenceRange ω S π
    ∃ e : (StrongCoprimalityThetaSpace ω ⧸ D) ≃L[ℂ] (StrongCoprimalityDecaySpace ω ⧸ E),
      ∀ x : StrongCoprimalityThetaSpace ω,
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x)

/-- Paper: Theorem 7.5.0.1, p. 374.
Over ℚ take the even quadratic character modulo 5, S = {(5)}, and the uniformizer 5.
In the splitting of the idele classes by the positive norm, this character has value
one on the uniformizer class. Its nontrivial restriction to the 5-adic units makes
the local unit average zero on this isotype. Weil principal value then acts as the
identity, giving a zero source quotient. The χ-weighted Haar integral annihilates the
printed difference and is nonzero on the product of the inverse compact character
with exp(−(log t)²) in the positive norm coordinate t. Thus the target is nonzero. -/
theorem Printed.strongCoprimality_false : ¬ Printed.strongCoprimality := by sorry

/-- Paper: Remark 7.5.0.2, p. 379.
The printed strong dual is a Hausdorff quotient of a closed subspace of a finite
locally convex sum of rapidly decreasing sequence spaces. -/
def Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual (ideleClassNorm F).ker)
    (p : V[ℚ]),
    let S := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    ∃ n : ℕ, let E := Fin n → RapidDecaySequence 1
      ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
        IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
          Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω S) ≃L[ℂ] (W ⧸ D))

/-- Paper: Remark 7.5.0.2, p. 379.
Over ℚ with trivial character and p = 2, the primary quotient is the smooth
periodic space for period log 2. Its Fourier sequence space has strong dual
consisting of polynomially growing sequences. This dual is meagre in itself:
the closed sets of sequences bounded by m(1 + |n|)^m, for m ≥ 1, cover it
and have empty interior. A closed subspace of a finite product of Schwartz
sequence spaces, quotiented by a closed subspace, is Fréchet and hence Baire. -/
theorem Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient_false :
    ¬ Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient := by sorry

end RiemannMasullo
