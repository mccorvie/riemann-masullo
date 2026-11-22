module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4

/-!
# Chapter 5.4: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding results are in `Sec4.lean` and the errata are recorded in `ERRATA.md`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

local notation "Test(" A ")" => SchwartzBruhat (Multiplicative (A))
local notation "normℂ(" t ")" => (((t : ℝ≥0ˣ).val : ℝ) : ℂ)
local notation "restrict₁(" F ", " S ", " χ ")" => ((χ : PontryaginDual (SIdeleQuotient F S)).comp
  (⟨(sIdeleQuotientNorm F S).ker.subtype, continuous_subtype_val⟩ :
    (sIdeleQuotientNorm F S).ker →ₜ* SIdeleQuotient F S))
local notation "ρₛ(" field ", " places ", " χ ", " s ")" =>
  sLocalRhoFactor (F := field) (S := places)
    (quasiCharacterNormTwist (sIdeleQuotientNorm field places)
      (isProperMap_sIdeleQuotientNorm field places).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ)) (s))

local notation "rightInterval" => Ioi (0 : ℝ)
local notation "leftInterval" => Iio (1 : ℝ)
local notation "rightHalf" => Complex.re ⁻¹' rightInterval
local notation "leftHalf" => Complex.re ⁻¹' leftInterval
local notation "overlap" => Complex.re ⁻¹' Ioo (0 : ℝ) 1
local notation "B⁺" => SchwartzBergman rightInterval
local notation "B⁻" => SchwartzBergman leftInterval
local notation "Eω(" field ", " places ", " I ", " ω ")" =>
  ↥(sLocalDecayIsotype (F := field) (S := places) (I) (ω))

/-- Paper: Theorem 5.4.1.1(1), p. 266.
As printed: the Fourier coordinate of the zeta pair is equivariant with multiplier
`t^(1-s) · ω̄(k)` for translation by the class `τ(t)k`. This records the second
coordinate on the common strip where the printed range `Re s > 0` meets the Fourier
coordinate’s domain `Re s < 1`. Character inversion expresses conjugation.
Remark 5.4.1.2 and Proposition 5.4.1.4 repeat this multiplier. The repaired declarations are
`sLocalZetaPair_translate` and `exists_sLocalZetaPair_action`. See ERRATA F60. -/
def Printed.sLocalZetaPair_translate : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let A := SAdeleRing F S
    let J := SIdeleQuotient F S
    let m := sIdeleQuotientNorm F S
    ∀ (τ : ℝ≥0ˣ →ₜ* J) (hτ : RightInverse τ m) (ω : PontryaginDual m.ker),
      let χ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S) τ hτ ω).exists.choose
      ∀ (u : Aˣ) (t : ℝ≥0ˣ) (k : m.ker) (f : Test(A)),
        (QuotientGroup.mk u : J) = τ t * k.val →
        let U := sLocalZetaPair (F := F) (S := S) χ
        let p := U (Submodule.Quotient.mk f)
        let q := U (Submodule.Quotient.mk (schwartzBruhatUnitTranslate (R := A) u f))
        EqOn q.2.val (fun s ↦ normℂ(t) ^ (1 - s) * ((ω⁻¹) k : ℂ) * p.2.val s) overlap

/-- Paper: Theorem 5.4.1.1(1), p. 266.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `ω = 1`.
Use `f(x) = exp(−πx²)` and the positive real idele `u = 2`. At `s = 1/4` the Fourier
coordinate is nonzero. Fourier scaling multiplies it by `2^(1/4)`, while the printed
rule multiplies it by `2^(3/4)`. The same mismatch applies to the polar-free case on p. 267
using a nonzero even nonnegative smooth bump supported in `1/2 < |x| < 3/2`, whose first
zeta coordinate is positive at `s = 1/4` and whose second is nonzero by the functional equation.
-/
theorem Printed.sLocalZetaPair_translate_false : ¬ Printed.sLocalZetaPair_translate := by
  sorry

/-- Paper: Remark 5.4.1.2, p. 266.
As printed: for a unitary lift of section frequency `x`, the reflected Fourier coordinate
in the lift's chart is the normalized Fourier coordinate evaluated at `s − ix`. This records
the second vertical translation in the remark. `existsUnique_sLocalZetaPair` gives the chart
values, and `sLocalCech_left_commutes` gives the unreflected transforms. See ERRATA F61. -/
def Printed.sLocalZetaPair_reflectedShift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let J := SIdeleQuotient F S
    ∀ (τ : ℝ≥0ˣ →ₜ* J) (hτ : RightInverse τ (sIdeleQuotientNorm F S))
      (χ : PontryaginDual J) (x : ℝ),
      (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = normℂ(t) ^ ((x : ℂ) * Complex.I)) →
      let χ₀ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S)
        τ hτ (restrict₁(F, S, χ))).exists.choose
      ∀ f : Test(SAdeleRing F S),
        let p := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
        let p₀ := sLocalZetaPair (F := F) (S := S) χ₀ (Submodule.Quotient.mk f)
        EqOn p.2.val (fun s ↦ p₀.2.val (s - (x : ℂ) * Complex.I)) leftHalf

/-- Paper: Remark 5.4.1.2, p. 266.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and the lift
`χ(g) = |g|^i` of the trivial norm-one character, so `x = 1`. For the self-dual Gaussian
`f(y) = exp(−πy²)`, write `Z(z) = π^(−z/2) Γ(z/2)` for its norm-twist zeta function.
At `s = 1 − ε + i` with `ε > 0`, the printed shift gives `Z(ε)` while the lifted
Fourier coordinate is `Z(ε − 2i)`. The former has a pole as `ε` tends to zero and the
latter has a finite limit.
-/
theorem Printed.sLocalZetaPair_reflectedShift_false : ¬ Printed.sLocalZetaPair_reflectedShift := by
  sorry

/-- Paper: Theorem 5.4.2.2(2), p. 276.
As printed: radial inversion with the factor `t⁻¹` and the norm-one coordinate fixed sends
every function of the conjugate isotype with weights in `1 − I` back into the same weighted
isotype. This records the source and membership assertion in the prose, which uses `1 − I`
at both ends. The displayed type uses `I` at both ends.
`existsUnique_sLocalCechRadialReflection` exchanges the two intervals. See ERRATA F62. -/
def Printed.sLocalCechRadialReflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (_hτ : RightInverse τ (sIdeleQuotientNorm F S)),
    let E := Eω(F, S, leftInterval, restrict₁(F, S, χ⁻¹))
    ∀ f : E, ∃ j : E,
      ∀ (t : ℝ≥0ˣ) (k : (sIdeleQuotientNorm F S).ker),
        j.val.val (τ t * k.val) = normℂ(t)⁻¹ * f.val.val (τ t⁻¹ * k.val)

/-- Paper: Theorem 5.4.2.2(2), p. 276.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `χ = 1`.
Use `f(t) = exp(−1/t) / t`. For every `a < 1`, the twist `t^a f(t)` is Schwartz in
`log t`, since the power at infinity is `a−1 < 0` and the exponential dominates at zero.
The radial image is `exp(−t)`. Its weight-zero twist tends to `1` as `t` tends to zero,
and hence is outside the target with weights `a < 1`.
-/
theorem Printed.sLocalCechRadialReflection_false : ¬ Printed.sLocalCechRadialReflection := by
  sorry

/-- Paper: Theorem 5.4.2.2(3), p. 276.
As printed: reflection followed by multiplication by the local correcting factor gives
a linear topological isomorphism from the right half-plane Schwartz–Bergman space to the
reflected half-plane Schwartz–Bergman space. `sLocalCechBergman_exact` uses the product on the
overlap where it is holomorphic. See ERRATA F63. -/
def Printed.sLocalCechBergman_reflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)),
    ∃ J : B⁺ ≃L[ℂ] B⁻, ∀ p : B⁺,
      EqOn (J p).val (fun s ↦ ρₛ(F, S, χ, s) * p.val (1 - s)) leftHalf

/-- Paper: Theorem 5.4.2.2(3), p. 276.
Take `F = ℚ`, `S` consisting of the real place, and `χ = 1`. Use `p(s) = exp(s²)` on
the right half-plane. The factor `π^((1−2s)/2) Γ(s/2) / Γ((1−s)/2)` has a simple pole
at zero, where `p(1) = e`. The product is unbounded as `s` approaches zero through
positive real arguments, so no holomorphic output exists on the reflected half-plane.
-/
theorem Printed.sLocalCechBergman_reflection_false : ¬ Printed.sLocalCechBergman_reflection := by
  sorry

local notation "mellinAt(" τ ", " f ", " z ")" =>
  (∫ t : ℝ≥0ˣ, (f) ((τ) t) * normℂ(t) ^ (z) ∂positiveRealHaar)

/-- Paper: Theorem 5.4.2.2(4)–(5), (5.4.2.6), p. 276.
As printed: the right square commutes on every input of the two upper weighted isotypes.
On the overlap, the top-then-right path has second term `ρ(s) Q(s)` by the conjugation of
the multiplier by Mellin in (4). The down-then-right path has second term `ρ(s) Q(1−s)`
by (3). Here `Q` denotes the second Mellin transform. We read “similarly” in (1) as using
the printed shift for both transforms and express the two paths after Mellin evaluation,
with the first projection as in (5) on p. 277. See `existsUnique_sLocalCechDifference`
for the repaired difference and ERRATA F64.
-/
def Printed.sLocalCech_right_commutes : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (_hτ : RightInverse τ (sIdeleQuotientNorm F S)) (x : ℝ),
    (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = normℂ(t) ^ ((x : ℂ) * Complex.I)) →
    ∀ (M₁ : Eω(F, S, rightInterval, restrict₁(F, S, χ)) ≃L[ℂ] B⁺)
      (M₂ : Eω(F, S, rightInterval, restrict₁(F, S, χ⁻¹)) ≃L[ℂ] B⁺),
      (∀ f s, s ∈ rightHalf → (M₁ f).val s = mellinAt(τ, f.val.val, s + (x : ℂ) * Complex.I)) →
      (∀ f s, s ∈ rightHalf → (M₂ f).val s = mellinAt(τ, f.val.val, s + (x : ℂ) * Complex.I)) →
      ∀ f g, EqOn
        (fun s ↦ (M₁ f).val s - ρₛ(F, S, χ, s) * (M₂ g).val s)
        (fun s ↦ (M₁ f).val s - ρₛ(F, S, χ, s) * (M₂ g).val (1 - s)) overlap

/-- Paper: Theorem 5.4.2.2(4)–(5), (5.4.2.6), p. 276.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `χ = 1`,
so both Mellin transforms have shift zero. Set the first input to zero and the second
to the inverse Mellin image of `Q(s) = exp((s−2)²)` on the right half-plane.
At `s = 1/4`, `Q(1/4)` and `Q(3/4)` differ and `ρ(1/4) ≠ 0`. Both arguments are in
the overlap and the two paths give different values there.
-/
theorem Printed.sLocalCech_right_commutes_false : ¬ Printed.sLocalCech_right_commutes := by
  sorry

end RiemannMasullo
