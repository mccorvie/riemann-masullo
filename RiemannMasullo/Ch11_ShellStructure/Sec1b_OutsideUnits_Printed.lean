module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec1b

/-!
# Printed outside-unit product claims in §11.1.2

The corresponding idele test and theta function are in `Sec1b.lean`.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped BigOperators Classical NNReal NumberField.AdeleRing nonZeroDivisors

namespace RiemannMasullo

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "I[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ(" A ")" => SchwartzBruhat (Multiplicative A)
local notation "classOf[" F "]" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. As printed: replacing the
integer indicator at every finite place outside S by the integer-unit
indicator gives a Schwartz–Bruhat function on the additive adeles. The
local test has the tensor form and the two polar vanishing conditions from
p. 482. The definition `sLocalCarvingIdeleTest` uses the product on the
ideles (ERRATA F204). -/
def Printed.sLocalCarvingOutsideUnits_schwartzBruhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ f : sAdelePolarSubspace F S,
      (∃ (arch : ℬ(InfiniteAdeleRing F))
         (fv : (v : S) → ℬ(v.val.adicCompletion F)),
        ∀ x : SAdeleRing F S, f.val (Multiplicative.ofAdd x) =
          arch (Multiplicative.ofAdd x.1) * ∏ v : S, fv v (Multiplicative.ofAdd (x.2 v))) →
      ∃ h : ℬ(𝔸[F]), ∀ x : 𝔸[F],
        h (Multiplicative.ofAdd x) =
          {y : 𝔸[F] | ∀ v ∉ S, Valued.v (y.2 v) = 1}.indicator
            (fun y ↦ f.val (Multiplicative.ofAdd (adeleProjection F S y))) x

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. Take `F = ℚ`, the trivial
character, and `S = ∅` (only the real place in the paper). The real test
`x exp(−x²)` vanishes at zero and has zero integral. At the identity adele the product
is `exp(−1)`. Adeles obtained by changing only the p-coordinate to p tend
to the identity as p runs through distinct primes, but their products are
zero. This contradicts continuity of a Schwartz–Bruhat function. -/
theorem Printed.sLocalCarvingOutsideUnits_schwartzBruhat_false :
    ¬ Printed.sLocalCarvingOutsideUnits_schwartzBruhat := by sorry

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. As printed: the unaveraged
product with the open lower norm cutoff defines a function of the idele
class. This is the descent claimed for the displayed generators, including
those of the space whose tests only satisfy the Fourier vanishing condition.
The formula `sLocalCarvingTheta_spec` instead uses the principal orbit sum
at each representative (ERRATA F205). -/
def Printed.sLocalCarvingCutoffProduct_descends : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ (Λ : ℝ), 0 < Λ →
      ∀ f : ℬ(SAdeleRing F S), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 →
        ∃ h : C[F] → ℂ, ∀ g : I[F],
          h (classOf[F] g) =
            {u : I[F] | Λ⁻¹ < ((ideleNorm F u).val : ℝ)}.indicator
              (sLocalCarvingIdeleTest S f) g

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. Take `F = ℚ`, the trivial
character, `S = ∅` (only the real place in the paper), `Λ = 2`, and the
real test `x exp(−x²)`. The principal ideles 1 and 2 give the same class and both
have norm one. The displayed product takes value `exp(−1)` on 1 and
zero on 2 because its 2-adic coordinate is not a unit. -/
theorem Printed.sLocalCarvingCutoffProduct_descends_false :
    ¬ Printed.sLocalCarvingCutoffProduct_descends := by sorry

end RiemannMasullo
