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
    ¬ Printed.sAdeleQuotient_isRatVectorSpace := by
  intro h
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅
  let p := adeleProjection ℚ S
  let d := (p.comp (integralAdelesOutside ℚ S).subtype).comp (integralAdeleDiagonal ℚ S)
  let diag := p.comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))
  let q := (QuotientAddGroup.mk' d.toAddMonoidHom.range).comp diag.toAddMonoidHom
  let : Module ℚ (SAdeleRing ℚ S ⧸ d.toAddMonoidHom.range) := (h ℚ S).some
  -- An additive map between rational vector spaces commutes with halving.
  have hone : q 1 = 0 := (QuotientAddGroup.eq_zero_iff (diag 1)).2
    ⟨1, (map_one d).trans (map_one diag).symm⟩
  have hhalf : q (1 / 2) = 0 := by
    simpa only [smul_eq_mul, mul_one, hone, smul_zero] using map_rat_smul q (1 / 2) 1
  -- Thus 1/2 would be an S-integer, hence an integer since S has no finite places.
  obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff (diag (1 / 2))).1 hhalf
  have hxhalf : x.val = 1 / 2 := diag.injective hx
  have hxint := x.property
  simp only [S, Finset.coe_empty, integer_empty, Algebra.mem_bot] at hxint
  obtain ⟨z, hz⟩ := hxint
  have heq := (Rat.ringOfIntegersEquiv_apply_coe z).trans (hz.trans hxhalf)
  have hden := congrArg Rat.den heq
  norm_num only [Rat.den_intCast] at hden

end RiemannMasullo
