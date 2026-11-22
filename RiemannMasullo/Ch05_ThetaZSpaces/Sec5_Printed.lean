module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5

/-! # Chapter 5.5: statements that are false as printed -/

@[expose] public noncomputable section

open NumberField

namespace RiemannMasullo

/-- Paper: §6.3.2, following (6.3.2.2), p. 304. As printed: the two polar evaluations on
the global theta quotient equal the normalized eigendistributions of weights one and the
idelic norm. This repeats (5.5.2.3). See `globalThetaPolarValues_eq_eigendistributions` and
ERRATA F77. -/
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
    ¬ Printed.globalConverse_polarValues_eq_eigendistributions := by sorry

end RiemannMasullo
