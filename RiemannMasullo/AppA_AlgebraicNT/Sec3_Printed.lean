module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # Appendix A.3: the printed S-local measure equality -/

@[expose] public noncomputable section

namespace RiemannMasullo

open NumberField IsDedekindDomain

/-- Paper: Lemma A.3.1.3, second equality of (A.3.1.3), p. 556. As printed: for every
finite set of places S containing all infinite places, the additive measure of quotient
covolume one equals the product of the local Tamagawa measures over S. The finite set
parameter lists the finite places of S. `sAdditiveTamagawaMeasure_eq_covolumeOne` gives
the equality when S contains all ramified places. See ERRATA F10. -/
def Printed.sAdditiveTamagawaMeasure_eq_covolumeOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    sAdditiveCovolumeOneMeasure F S = sAdditiveTamagawaMeasure F S

/-- Paper: Lemma A.3.1.3, second equality of (A.3.1.3), p. 556. For F = ℚ(i) and
no finite places in S, the diagonal lattice is ℤ[i] in ℂ. Its fundamental square
`[0, 1) × [0, 1)` has mass one for the covolume-one measure and mass two for the complex
Tamagawa measure `2 dx dy`. -/
theorem Printed.sAdditiveTamagawaMeasure_eq_covolumeOne_false :
    ¬ Printed.sAdditiveTamagawaMeasure_eq_covolumeOne := by sorry

end RiemannMasullo
