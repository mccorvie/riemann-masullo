module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a

/-! # Chapter 2.2: the printed adelic Riemann–Roch identity -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing

local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh02Sec2aAdeleMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace 𝔸[F] := borel _

/-- Paper: Theorem 2.2.3.2, p. 82. As printed: the adelic Riemann–Roch identity
holds for the Fourier transform using the character of Examples A.3.1.5, A.3.1.6,
A.3.1.8 and A.3.1.9. Negating the finite coordinates of the input to
`adeleStandardCharacter` restores the printed finite sign and keeps the real sign.
`adelicTheta_riemannRoch` uses the character with opposite signs. See ERRATA F13. -/
def Printed.adelicTheta_riemannRoch : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]),
    ∃ fhat : ℬ[F],
      (∀ y : 𝔸[F], fhat (Multiplicative.ofAdd y) =
        tamagawaFourier (additiveTamagawaMeasure F)
          (fun a : 𝔸[F] ↦ adeleStandardCharacter F (a.1, -a.2))
          (fun x ↦ f (Multiplicative.ofAdd x)) y) ∧
      ∀ g : IdeleClassGroup (𝓞 F) F,
        let n : ℝ := (ideleClassNorm F g : ℝ≥0)
        let z := Multiplicative.ofAdd (0 : 𝔸[F])
        adelicTheta f g = n⁻¹ • adelicTheta fhat g⁻¹ + n⁻¹ • fhat z - f z

/-- Paper: Theorem 2.2.3.2, p. 82. Over ℚ, take g = 1 and let f be a real smooth
bump supported in `(1/2, 3/2)` with f∞(1) = 1, times `1_{1+3ℤ₃}` at 3 and `1_{ℤₚ}`
elsewhere. Including the zero terms, the left side sums f∞ over the integers congruent
to 1 modulo 3 and gives 1. The printed Fourier sum equals the sum of the corrected
Fourier transform of f with its finite inputs negated. By Poisson summation for the
corrected character, this sums f∞ over integers congruent to −1 modulo 3 and gives 0. -/
theorem Printed.adelicTheta_riemannRoch_false : ¬ Printed.adelicTheta_riemannRoch := by sorry

end RiemannMasullo
