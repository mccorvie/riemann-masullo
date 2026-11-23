module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

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

/-- At a field with one complex place, the Gaussian already contradicts the first coordinate. -/
private theorem globalThetaPolarValues_gaussian_contradiction (F : Type) [Field F] [NumberField F]
    (hF : InfinitePlace.nrComplexPlaces F = 1)
    (hall : Printed.globalThetaPolarValues_eq_eigendistributions) : False := by
  let χ : PontryaginDual (IdeleClassGroup (𝓞 F) F) := 1
  let f := adelicStandardGaussian χ
  let q := (LinearMap.ker (adelicThetaLinearMap F)).mkQL
  have h := congrArg Prod.fst (hall F (q f))
  have hp := congrArg Prod.fst (globalThetaPolarValues_mk f)
  have he := globalThetaEigendistribution_mk (F := F) 1 f
  have ht : ideleClassNormTwist χ 0 = 1 := by
    ext g
    change (1 : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ) = 1
    simp
  have hn := adelicNormalizedEigendistribution_gaussian (F := F) χ 0
  rw [ht] at hn
  have hval : f (Multiplicative.ofAdd 0) = (1 : ℂ) := hp.symm.trans (h.trans (he.trans hn))
  have hzero := adelicStandardGaussian_trivial_zero (F := F)
  rw [hF, pow_one] at hzero
  have hinv : (2 * (Real.pi : ℂ))⁻¹ = 1 := hzero.symm.trans hval
  have heq := inv_eq_one.mp hinv
  have hre : 2 * Real.pi = 1 := by exact_mod_cast heq
  linarith [Real.pi_gt_three]

/-- Paper: Lemma 5.5.2.1, (5.5.2.3), p. 280.
Take `F = ℚ(i)` and the theta class of the trivial-character standard adelic Gaussian
`E`. The complex Gaussian factor is `(2π)⁻¹ exp(−2π|z|²)`, and the finite factors are
the integer-ring indicators. Both normalized eigendistributions take value `1` on the
class. Evaluation at zero gives `1/(2π)`. Fourier evaluation at zero gives `1/(4π)`,
since the complex integral against `2 dx dy` is `1/(2π)` and the finite integer rings
have product additive mass `1/2`. -/
theorem Printed.globalThetaPolarValues_eq_eigendistributions_false :
    ¬ Printed.globalThetaPolarValues_eq_eigendistributions := by
  let F := CyclotomicField 4 ℚ
  have : NeZero (4 : ℕ) := ⟨by decide⟩
  have : IsCyclotomicExtension {4} ℚ F := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ
    exact Subsingleton.elim _ _
  have : NumberField F := IsCyclotomicExtension.numberField {4} ℚ F
  apply globalThetaPolarValues_gaussian_contradiction F
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4) F]
  decide

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

/-- Paper: §6.3.2, following (6.3.2.2), p. 304. As printed: the two polar evaluations on
the global theta quotient equal the normalized eigendistributions of weights one and the
idelic norm. This repeats (5.5.2.3), which is `Printed.globalThetaPolarValues_eq_eigendistributions`
above; the same counterexample refutes both. See `globalThetaPolarValues_eq_eigendistributions`
and ERRATA F77. -/
def Printed.globalConverse_polarValues_eq_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (x : GlobalAdelicThetaSpace F),
    globalThetaPolarValues (F := F) x =
      (globalThetaEigendistribution (F := F) 1 x,
        globalThetaEigendistribution (ideleClassNormTwist
          (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 1) x)

/-- Paper: §6.3.2, following (6.3.2.2), p. 304. Take F = ℚ(i) and the class of the trivial
standard Gaussian E. Both normalized generators take value 1 there. The complex factor is
`(2π)⁻¹ exp(-2π|z|²)`, so E(0) = (2π)⁻¹. Its complex integral against `2 dx dy` is also
`(2π)⁻¹`, and the product of the finite integer-ring masses is 1/2. The Fourier evaluation
is therefore `(4π)⁻¹`. -/
theorem Printed.globalConverse_polarValues_eq_eigendistributions_false :
    ¬ Printed.globalConverse_polarValues_eq_eigendistributions :=
  Printed.globalThetaPolarValues_eq_eigendistributions_false

end RiemannMasullo
