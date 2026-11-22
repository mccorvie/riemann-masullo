module

public import RiemannMasullo.AppB_AnalyticNT.Sec4a

/-!
# Appendix B.4.1: statements that are false as printed

The printed claim is kept as a proposition with a separate refutation statement.
Nothing imports this file.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped SchwartzMap

namespace RiemannMasullo

/-- Paper: Lemma B.4.1.7, p. 611. As printed: for every number field, continuous
character unramified at a given prime, and Schwartz test function of exponential decay,
the sum of its Mellin transform over the local frequencies equals the negative
normalized logarithmic-derivative integral on any positive vertical line, for every
choice of logarithm. This is the second equality in (B.4.1.20), repeated in
(B.4.1.35). The first equality is `hasSum_localEulerFactor_mellinSamples`.
The one-sided integral formula is `hasSum_localEulerFactor_cauchyIntegral`.
See ERRATA F18. -/
def Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)),
    (ideleClassNormTwist χ 0).IsUnramifiedAt v →
    ∀ (f : 𝓢(ℝ, ℂ)), ExponentialDecay f →
      ∀ a > (0 : ℝ), ∀ ℓ : ℂ,
        let c := (ideleClassNormTwist χ 0).localValue v
        Complex.exp ℓ = c →
          let q : ℂ := v.asIdeal.absNorm
          let logq : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
          let Φ := mellin (fun t : ℝ ↦ f (Real.log t))
          let twoPiI := 2 * (Real.pi : ℂ) * Complex.I
          (∑' m : ℤ, Φ ((ℓ + twoPiI * (m : ℂ)) / logq)) =
            -verticalLineIntegral (fun s ↦ Φ s * (logq / (1 - c⁻¹ * q ^ s))) a / twoPiI

/-- Paper: Lemma B.4.1.7, p. 611. Take the rational field, the prime `(2)`,
the trivial character, logarithm zero, and the vertical line at `a = 1`.
Choose a smooth logarithmic profile supported in `(-log 2 / 2, log 2 / 2)` with
value one at zero. The frequency sum equals the two-sided lattice sum times
`log 2`, and only the index zero contributes. The right-line integral samples only
the strictly positive powers of two, so it vanishes. -/
theorem Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_false :
    ¬ Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral := by
  sorry

end RiemannMasullo
