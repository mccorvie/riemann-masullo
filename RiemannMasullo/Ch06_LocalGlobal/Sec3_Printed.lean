module

public import RiemannMasullo.Ch06_LocalGlobal.Sec3

/-! # Chapter 6.3: statements that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "ℬ(" F ")" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "shift(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "twist(" χ ", " s ")" => ideleClassNormTwist χ s
local notation "ω(" F ", " χ ")" => (χ : PontryaginDual C𝔽(F)).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽(F))
local notation "Z(" f ", " χ ")" => (fun s ↦ globalIdelicZFunction f (twist(χ, s)))
local notation "E(" χ ", " S ")" => reciprocalPartialHeckeEulerProduct χ S
local notation "ζ̂(" F ")" => continuedCompletedHeckeL (1 : PontryaginDual C𝔽(F))
local notation "zeroAdele(" F ")" => Multiplicative.ofAdd (0 : 𝔸[F])
local notation "mass(" F ")" => ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
local notation "printedEuler(" χ ", " S ", " z ")" =>
  (∏ v ∈ Finset.filter (fun v ↦ (twist(χ, 0)).IsUnramifiedAt v) S,
    (1 - (v.asIdeal.absNorm : ℂ) ^ z))

local notation "EntireMultiple(" h ", " g ")" =>
  (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ h =ᶠ[codiscrete ℂ] fun s ↦ g s * u s)

open Classical in
/-- Paper: Theorems 6.3.2.1(2) and 6.3.2.2(2), (6.3.2.5)–(6) and (6.3.2.21)–(22),
p. 304 and p. 310. As printed: the two displayed terminal maps onto ℂ² are surjective for every
character. The formulas are evaluated on test representatives, which cover the respective
theta spaces. This is the right-exactness part. See `globalConverse_nontrivial_exact`,
`globalPrincipalValueConverse_nontrivial_exact` and ERRATA F78. -/
def Printed.globalConverse_polarCoordinates_surjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)),
    let δ : ℂ := if ω(F, χ) = 1 then 1 else 0
    (Surjective fun f : ℬ(F) ↦ (-mass(F) * f (zeroAdele(F)) * δ,
      mass(F) * adeleSchwartzFourier f (zeroAdele(F)) * δ)) ∧
    ∀ (S : Finset (Places(F))) (t : ℝ),
      (ω(F, χ) = 1 → twist(χ, 0) = twist((1 : PontryaginDual C𝔽(F)), shift(t))) →
      Surjective fun f : ℬ(F) ↦
        (-printedEuler(χ, S, shift(t)) * mass(F) * f (zeroAdele(F)) * δ,
          printedEuler(χ, S, -1 + shift(t)) * mass(F) *
            adeleSchwartzFourier f (zeroAdele(F)) * δ)

/-- Paper: Theorems 6.3.2.1(2) and 6.3.2.2(2), p. 304 and p. 310. Take F = ℚ and the even
quadratic idele class character modulo 5, which is nontrivial on the norm-one classes. The
Kronecker delta is zero, so both coordinate maps are identically zero for every removal set. -/
theorem Printed.globalConverse_polarCoordinates_surjective_false :
    ¬ Printed.globalConverse_polarCoordinates_surjective := by sorry

-- F79: the full class-group Mellin integral is the class mass times Z.
-- The sequence isomorphism on p. 304 leaves its terminal isomorphism unspecified.
-- Multiplication by that mass on both residue coordinates intertwines the maps.
-- See `homogeneousTheta_classMellin_eq_mass_mul`.

/-- Paper: Theorems 6.3.2.1–2, (6.3.2.8), (6.3.2.20), (6.3.2.24), p. 304 and p. 310.
As printed: the Mellin transforms of polar-free tests are divisible by the displayed
generators, including after Euler-factor removal. The short sequences use the factor
`(s-it₀)(1-s-it₀)` on shifted completed zeta, and the range in (6.3.2.20) uses the unshifted
`s(s-1)ζ̂_F(s)`. This is the inclusion of each Mellin image in its asserted ideal. See
`globalConverse_normTwist_meromorphic_exact`, `globalPrincipalValueConverse_normTwist`
and ERRATA F80. -/
def Printed.globalConverse_normTwist_printedGenerator_divides : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (t : ℝ),
    twist(χ, 0) = twist((1 : PontryaginDual C𝔽(F)), shift(t)) →
    let G := fun s : ℂ ↦ (s - shift(t)) * (1 - s - shift(t)) * ζ̂(F) (s + shift(t))
    (∀ f : adelePolarSubspace F, EntireMultiple(Z(f.val, χ), G)) ∧
    ∀ (S : Finset (Places(F))) (f : adelePolarSubspace F),
      let H := Z(adelePrincipalValue F S f.val, χ)
      EntireMultiple(H, fun s ↦ E(χ, S) s * G s) ∧
        EntireMultiple(H, fun s ↦ E(χ, S) s * s * (s - 1) * ζ̂(F) s)

/-- Paper: Theorems 6.3.2.1–2, (6.3.2.8), (6.3.2.20), (6.3.2.24), p. 304 and p. 310.
Over ℚ let E be the trivial standard Gaussian and T its translation operator for the idele
with real component 2 and all finite components 1. The test `(T-1)(T-2)E` is polar-free, and
its untwisted transform is `(2^s-1)(2^s-2)Z(E,s)`, nonzero near zero. For sufficiently small
nonzero t₀ its shifted transform at `s=it₀` is nonzero, although the printed generator vanishes
there. This also applies with an empty removal set. The unshifted generator in (6.3.2.20)
forces a zero at any completed zeta zero ρ, while the same test's shifted transform is nonzero
at ρ for a choice of t₀ avoiding its discrete zero set. -/
theorem Printed.globalConverse_normTwist_printedGenerator_divides_false :
    ¬ Printed.globalConverse_normTwist_printedGenerator_divides := by sorry

/-- Paper: Theorems 6.3.2.1–2, (6.3.2.8), (6.3.2.25)–(26), p. 304 and p. 310. As printed:
the pair of residues maps the middle term, obtained by intersecting the shifted completed
zeta ideal with the entire Schwartz–Bergman space, onto ℂ². The Euler multiplier accounts for
removal in (6.3.2.25); its empty product recovers (6.3.2.8). This is right exactness of the
displayed middle term. See `globalConverse_normTwist_meromorphic_exact`,
`globalPrincipalValueConverse_normTwist_divided_exact` and ERRATA F81. -/
def Printed.globalConverse_normTwist_bergmanMiddle_residues_surjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (t : ℝ),
    twist(χ, 0) = twist((1 : PontryaginDual C𝔽(F)), shift(t)) →
    ∀ S : Finset (Places(F)),
      let G := fun s : ℂ ↦ E(χ, S) s * ζ̂(F) (s + shift(t))
      Surjective fun b : {b : B // EntireMultiple(b.val, G)} ↦
        (complexResidue b.val.val (-shift(t)), complexResidue b.val.val (1 - shift(t)))

/-- Paper: Theorems 6.3.2.1–2, (6.3.2.8), (6.3.2.25)–(26), p. 304 and p. 310.
Take ℚ, the trivial character, t₀ = 0 and no removed primes. Every element of the printed
middle term is entire and both of its residues are zero. In particular (1, 0) has no preimage.
The standard Gaussian's Mellin transform has poles at 0 and 1. -/
theorem Printed.globalConverse_normTwist_bergmanMiddle_residues_surjective_false :
    ¬ Printed.globalConverse_normTwist_bergmanMiddle_residues_surjective := by sorry

/-- Paper: Theorem 6.3.2.2(1), range after (6.3.2.20), p. 310. As printed: every entire
multiple of the printed principal-value generator lies in the Schwartz–Bergman space.
This is the asserted containment, with equality as meromorphic functions. See
`globalPrincipalValueConverse_normTwist` and ERRATA F82. -/
def Printed.globalPrincipalValueConverse_normTwist_ideal_subset_bergman : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (t : ℝ),
    twist(χ, 0) = twist((1 : PontryaginDual C𝔽(F)), shift(t)) →
    ∀ (S : Finset (Places(F))) (u : ℂ → ℂ), Differentiable ℂ u →
      ∃ b : B, b.val =ᶠ[codiscrete ℂ] fun s ↦ E(χ, S) s * s * (s - 1) * ζ̂(F) s * u s

/-- Paper: Theorem 6.3.2.2(1), range after (6.3.2.20), p. 310. Take ℚ, the trivial
character, no removal, and the entire multiplier `exp(s^4)`. On `s = 2 + it` its modulus
is `exp(t^4-24t²+16)`. The Euler product bounds the ordinary zeta modulus below by
`ζ(4)/ζ(2)` and Stirling's formula gives only exponential decay of the gamma factor. The
resulting product grows on the vertical line and violates the Schwartz–Bergman condition. -/
theorem Printed.globalPrincipalValueConverse_normTwist_ideal_subset_bergman_false :
    ¬ Printed.globalPrincipalValueConverse_normTwist_ideal_subset_bergman := by sorry

open Classical in
/-- Paper: Theorem 6.3.2.2(2), (6.3.2.22)–(6.3.2.26), p. 310. As printed: the
sequence isomorphism under the full class-group Mellin integral intertwines the displayed
terminal coordinates with the two ordinary residues. Its terminal isomorphism is fixed for
all tests in the sequence. See `globalPrincipalValueConverse_normTwist_residues` and
ERRATA F83. -/
def Printed.globalPrincipalValueConverse_normTwist_printedResidues : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (t : ℝ),
    twist(χ, 0) = twist((1 : PontryaginDual C𝔽(F)), shift(t)) →
    ∀ S : Finset (Places(F)), ∃ A : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
      ∀ f : ℬ(F), ∃ M : ℂ → ℂ, Meromorphic M ∧
        (∀ s : ℂ, 1 < s.re →
          M s = ∫ g : C𝔽(F),
            homogeneousAdelicTheta (ω(F, χ)) (adelePrincipalValue F S f) g * twist(χ, s) g
              ∂ideleClassTamagawaMeasure F) ∧
        (complexResidue M (-shift(t)), complexResidue M (1 - shift(t))) =
          A (-printedEuler(χ, S, shift(t)) * mass(F) * f (zeroAdele(F)),
            printedEuler(χ, S, -1 + shift(t)) * mass(F) *
              adeleSchwartzFourier f (zeroAdele(F)))

/-- Paper: Theorem 6.3.2.2(2), (6.3.2.22)–(6.3.2.26), p. 310. Take ℚ, remove 2, and
set t₀ = π/log 2 in the pure norm twist. Use (1-2πx²) exp(-πx²) at infinity and the integer
indicators at finite places. Its polar values are (1,0), and the rational class mass is 1.
The printed Euler factors are 2 and 3/2, so the printed pair is (-2,0). The full Mellin
continuation has Euler factors 0 and 1/2 at the two shifted poles and hence residue pair
(0,0). Injectivity of the terminal isomorphism gives the contradiction. -/
theorem Printed.globalPrincipalValueConverse_normTwist_printedResidues_false :
    ¬ Printed.globalPrincipalValueConverse_normTwist_printedResidues := by sorry

/-- Paper: Theorem 6.3.2.2(2), (6.3.2.21), (6.3.2.24)–(26), p. 310. As printed: in
Mellin coordinates the ordinary residue pair is onto ℂ² and its kernel is the image of the
pole-free term. This is exactness at the middle and right, expressed on representatives
of the principal-value Mellin image. See `globalPrincipalValueConverse_normTwist_divided_exact`
and ERRATA F84. -/
def Printed.globalPrincipalValueConverse_normTwist_ordinaryResidues_exact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (t : ℝ),
    twist(χ, 0) = twist((1 : PontryaginDual C𝔽(F)), shift(t)) →
    ∀ S : Finset (Places(F)),
      let H := fun f : ℬ(F) ↦ Z(adelePrincipalValue F S f, χ)
      let R := fun f : ℬ(F) ↦ (complexResidue (H f) (-shift(t)), complexResidue (H f) (1 - shift(t)))
      Surjective R ∧ ∀ f : ℬ(F), R f = 0 ↔
        ∃ f₀ : adelePolarSubspace F, H f =ᶠ[codiscrete ℂ] H f₀.val

/-- Paper: Theorem 6.3.2.2(2), (6.3.2.21), (6.3.2.24)–(26), p. 310. Take ℚ, the
trivial character and remove 2. The factor `1 - 2^{-s}` cancels the first pole for every
test, so (1, 0) has no preimage. For the test with real component `(1-2πx²) exp(-πx²)`
and integer indicators at every finite place, the value at zero is one and the Fourier
value there is zero. The removed transform has two zero residues and takes value `-log 2`
at zero. If a polar-free test had the same removed transform, cancelling the Euler factor
would equate its entire transform with the original transform having residue -1 at zero. -/
theorem Printed.globalPrincipalValueConverse_normTwist_ordinaryResidues_exact_false :
    ¬ Printed.globalPrincipalValueConverse_normTwist_ordinaryResidues_exact := by sorry

end RiemannMasullo
