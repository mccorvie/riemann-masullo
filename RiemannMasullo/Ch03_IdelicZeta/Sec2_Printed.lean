module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-! # Chapter 3.2: the printed global idelic functional equation -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory NumberField
open scoped NumberField.AdeleRing

local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh03Sec2AdeleMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace 𝔸[F] := borel _

/-- Paper: Theorem 3.2.2.1(1)(b), p. 124. As printed: the global functional equation
holds for the Fourier transform using the character of Examples A.3.1.5, A.3.1.6,
A.3.1.8 and A.3.1.9. Negating the finite coordinates of the input to
`adeleStandardCharacter` implements the printed signs. The corrected identity is
`globalIdelicZFunction_functionalEquation`. See ERRATA F13. -/
def Printed.globalIdelicZFunction_functionalEquation : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]),
    ∃ fhat : ℬ[F],
      (∀ y : 𝔸[F], fhat (Multiplicative.ofAdd y) =
        tamagawaFourier (additiveTamagawaMeasure F)
          (fun a : 𝔸[F] ↦ adeleStandardCharacter F (a.1, -a.2))
          (fun x ↦ f (Multiplicative.ofAdd x)) y) ∧
      ∀ c : HeckeCharacter (𝓞 F) F,
        globalIdelicZFunction f c = globalIdelicZFunction fhat
          (dualQuasiCharacter (G := IdeleClassGroup (𝓞 F) F) (ideleClassNorm F)
            (isProperMap_ideleClassNorm F).continuous c)

/-- Paper: Theorem 3.2.2.1(1)(b), p. 124. Over ℚ take the quadratic Hecke character
of the odd Dirichlet character modulo 3, twisted by the squared idelic norm. Take f
with a nonnegative real bump near 1, finite factor `1_{1+3ℤ₃}` at 3, and `1_{ℤₚ}`
elsewhere. Its zeta integral is nonzero by the local integrals and the absolutely
convergent Euler product. The printed transform is the corrected transform multiplied
in its argument by the idele with real coordinate 1 and finite coordinates −1.
The dual character takes value −1 on this idele, so the right side acquires a minus
sign by change of variables and meromorphic continuation. -/
theorem Printed.globalIdelicZFunction_functionalEquation_false :
    ¬ Printed.globalIdelicZFunction_functionalEquation := by sorry

end RiemannMasullo
