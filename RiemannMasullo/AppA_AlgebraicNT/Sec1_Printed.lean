module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1

/-!
# Appendix A.1: statements that are false as printed

A statement of the paper that turned out to be false is kept here as a proposition, exactly as
printed, together with a proof of its negation. The repaired statements are in `Sec1.lean`, and
`ERRATA.md` has the entries. Nothing imports this file.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open NumberField IsDedekindDomain

/-- Paper: Lemma A.1.5.1, last sentence, p. 543. As printed: "In particular, 𝔸_{F,S}/O_{F,S} is
naturally a ℚ-vector space." For every number field and every finite set of finite places, the
quotient of the S-adeles by the diagonal S-integers carries a rational vector space structure.
False: see `Printed.sAdeleQuotient_isRatVectorSpace_false` and ERRATA F2. The repaired lemma is
`sAdele_additive_quotient`, which omits this sentence. -/
def Printed.sAdeleQuotient_isRatVectorSpace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let p := adeleProjection F S
    let d := (p.comp (integralAdelesOutside F S).subtype).comp (integralAdeleDiagonal F S)
    Nonempty (Module ℚ (SAdeleRing F S ⧸ d.toAddMonoidHom.range))

/-- Paper: Lemma A.1.5.1, last sentence, p. 543. The printed statement is false. For the
rational field and no finite places the quotient is ℝ/ℤ, where the class of 1/2 is a nonzero
element of order two, and a rational vector space has no such element. -/
theorem Printed.sAdeleQuotient_isRatVectorSpace_false :
    ¬ Printed.sAdeleQuotient_isRatVectorSpace := by sorry

end RiemannMasullo
