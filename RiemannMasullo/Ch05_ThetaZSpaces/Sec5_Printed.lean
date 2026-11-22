module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5

/-!
# Chapter 5.5: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding results are in `Sec5.lean` and the errata are recorded in `ERRATA.md`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing

/-- Paper: Lemma 5.5.2.1, (5.5.2.3), p. 280.
As printed: evaluation at zero and Fourier evaluation at zero on the global theta
quotient are the normalized eigendistributions of weights one and the idelic norm,
respectively. `globalThetaPolarValues_eq_eigendistributions` includes the values on the
standard Gaussian as scalar factors. See ERRATA F65. -/
def Printed.globalThetaPolarValues_eq_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (x : GlobalAdelicThetaSpace F),
    let C := IdeleClassGroup (𝓞 F) F
    globalThetaPolarValues (F := F) x =
      (globalThetaEigendistribution (F := F) (1 : QuasiCharacter C) x,
        globalThetaEigendistribution (F := F) (ideleClassNormTwist (1 : PontryaginDual C) 1) x)

/-- Paper: Lemma 5.5.2.1, (5.5.2.3), p. 280.
Take `F = ℚ(i)` and the theta class of the trivial-character standard adelic Gaussian
`E`. The complex Gaussian factor is `(2π)⁻¹ exp(−2π|z|²)`, and the finite factors are
the integer-ring indicators. Both normalized eigendistributions take value `1` on the
class. Evaluation at zero gives `1/(2π)`. Fourier evaluation at zero gives `1/(4π)`,
since the complex integral against `2 dx dy` is `1/(2π)` and the finite integer rings
have product additive mass `1/2`. -/
theorem Printed.globalThetaPolarValues_eq_eigendistributions_false :
    ¬ Printed.globalThetaPolarValues_eq_eigendistributions := by
  sorry

/-- Paper: Remark 5.5.2.2, p. 281.
The pointwise reading of “indeed, this series diverges” asserts divergence for every
global test function after evaluating its translates by nonzero field elements at zero.
The series of functionals itself diverges, as one sees by testing on a function nonzero at zero.
`summable_globalZeroEval_orbit_iff` gives the condition for convergence. See ERRATA F66. -/
def Printed.globalZeroEval_orbit_diverges : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : SchwartzBruhat (Multiplicative 𝔸[F])),
    ¬ Summable (fun a : Fˣ ↦ f (Multiplicative.ofAdd
      ((algebraMap F 𝔸[F]) ((a⁻¹ : Fˣ) : F) * 0)))

/-- Paper: Remark 5.5.2.2, p. 281.
Take `F = ℚ` and the zero Schwartz–Bruhat test. Every summand is zero, so the family
is summable with sum zero. The same holds for any test vanishing at the zero adele. -/
theorem Printed.globalZeroEval_orbit_diverges_false : ¬ Printed.globalZeroEval_orbit_diverges := by
  sorry

/-- Paper: Remark 5.5.3.3, p. 285.
As printed: if the weights range over a connected set containing an interval with
nonempty one-dimensional interior, the corresponding eigendistributions have trivial
joint kernel on the ordinary S-local theta quotient. An interval is expressed by a
nondegenerate real segment in a complex norm coordinate. The declaration
`sLocalThetaEigendistributions_separate_of_accumulation` tests every norm chart.
See ERRATA F67. -/
def Printed.sLocalThetaEigendistributions_separate_of_interval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let J := SIdeleQuotient F S
    ∀ (W : Set (QuasiCharacter J)), IsConnected W →
      (∃ (χ : PontryaginDual J) (a b : ℂ), a ≠ b ∧
        let chart := quasiCharacterNormTwist (G := J) (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous
          ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
        chart '' segment ℝ a b ⊆ W) →
      ∀ x : SLocalAdelicThetaSpace F S,
        (∀ c ∈ W, sLocalThetaEigendistribution c x = 0) → x = 0

/-- Paper: Remark 5.5.3.3, p. 285.
Take `F = ℚ`, `S = {∞, 5}`, and let `W` be the image of the real segment `[2,3]`
in the norm chart of the trivial character. Tensor an even smooth real bump equal to
one at `±1` and supported in `1/2 < |x| < 3/2` with the quadratic character modulo `5`
on `ℤ₅ˣ`, extended by zero. At the identity only the S-units `±1` contribute to
theta, giving value two. The norm-one idele `(1, 2)` acts by negation on the test
and its theta class. Every weight in `W` takes value one on that idele, so each
corresponding eigendistribution kills the class. -/
theorem Printed.sLocalThetaEigendistributions_separate_of_interval_false :
    ¬ Printed.sLocalThetaEigendistributions_separate_of_interval := by
  sorry

end RiemannMasullo
