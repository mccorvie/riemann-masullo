module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b

/-! # Appendix A.2.4: the printed cover of the norm-one ideles -/

@[expose] public noncomputable section

namespace RiemannMasullo

open NumberField IsDedekindDomain

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F

/-- Paper: Remark A.2.4.5, p. 555. As printed: for all sufficiently large S the
S-ideal class group is trivial and the diagonal S-unit translates of the S-idelic domain
cover all norm-one ideles. The finite set parameter lists the finite places of S.
By Proposition A.2.4.4(4) on the same page, the union of these translates is the
norm-one subgroup invertible outside S (`sIdeleFundamentalDomain_cover` in the
trivial-class case). Writing this subgroup as its image in the ideles eliminates
the choice of a fundamental domain. See ERRATA F6. -/
def Printed.sIdeleFundamentalDomain_cover : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ T : Finset (Primes(F)), ∀ S : Finset (Primes(F)), T ⊆ S →
      Subsingleton (CommRing.Pic Oₛ(F, S)) ∧
      let inclusion := Units.map (integralAdelesOutside F S).subtype.toMonoidHom
      ((ideleNorm F).comp inclusion).ker.map inclusion = (ideleNorm F).ker

/-- Paper: Remark A.2.4.5, p. 555. Over ℚ the S-class group is trivial for every
finite S, because S-integers are a localization of ℤ. For any claimed threshold T,
take S = T and pick a rational prime p outside S. Its principal idele has norm one
and its inverse is nonintegral at p, as in `exists_rat_prime_idele_outside`.
Every element of the subgroup on the left lies in the range of the inclusion. -/
theorem Printed.sIdeleFundamentalDomain_cover_false :
    ¬ Printed.sIdeleFundamentalDomain_cover := by sorry

end RiemannMasullo
