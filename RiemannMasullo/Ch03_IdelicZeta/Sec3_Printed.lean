module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3

/-! # Chapter 3.3: the printed vertical-line estimate for the correcting factor -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter NumberField IsDedekindDomain Topology
open scoped Asymptotics

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132. As printed: on each fixed
vertical line of positive real part σ, the kth complex derivative of the S-local
correcting factor in any unitary norm-twist chart is big-O of
`|τ|^(σ - 1/2) |log |τ||^k` as `|τ| → ∞`. The finite set parameter lists the finite
places of S. `sLocalRhoFactor_iteratedDeriv_analyticOn` records (3.3.1.10).
See ERRATA F16. -/
def Printed.sLocalRhoFactor_iteratedDeriv_isBigO : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (k : ℕ) (σ : ℝ), 0 < σ →
    let circleToComplex : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let ρ := fun z : ℂ ↦ sLocalRhoFactor (F := F) (S := S)
      (quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous (circleToComplex.comp χ) z)
    (fun t : ℝ ↦ iteratedDeriv k ρ ((σ : ℂ) + (t : ℂ) * Complex.I))
      =O[comap (fun t : ℝ ↦ |t|) atTop]
        (fun t : ℝ ↦ |t| ^ (σ - 1 / 2) * |Real.log (|t|)| ^ k)

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132. Take F = ℚ(i), S consisting
of the complex place, the trivial character, k = 0 and σ = 1. The factor is
`(2π)^(1 - 2s) Γ(s) / Γ(1 - s)`, of modulus `|τ| / (2π)` for nonzero τ by the
Gamma recurrence and conjugation. The printed bound would give `O(|τ|^(1/2))`. -/
theorem Printed.sLocalRhoFactor_iteratedDeriv_isBigO_false :
    ¬ Printed.sLocalRhoFactor_iteratedDeriv_isBigO := by sorry

end RiemannMasullo
