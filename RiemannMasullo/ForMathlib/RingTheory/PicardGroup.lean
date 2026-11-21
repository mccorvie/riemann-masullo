module

public import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Localization.Algebra

@[expose] public section

noncomputable section

namespace RiemannMasullo

open CommRing IsDedekindDomain
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The Picard class of a nonzero integral ideal is represented by that ideal as a module. -/
private theorem equivPic_mk0_eq_picMk (I : (Ideal R)⁰) :
    ∃ (_ : Module.Invertible R (I : Ideal R)),
      ClassGroup.equivPic R (ClassGroup.mk0 I) = Pic.mk R (I : Ideal R) := by
  let J := FractionalIdeal.unitsMulEquivSubmodule (FractionalIdeal.mk0 (FractionRing R) I)
  have hJ : J.val = IsLocalization.coeSubmodule (FractionRing R) (I : Ideal R) := by
    change (↑(↑(FractionalIdeal.mk0 (FractionRing R) I) : FractionalIdeal R⁰ (FractionRing R)) :
      Submodule R (FractionRing R)) = _
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeToSubmodule_coeIdeal]
  let g := (Algebra.linearMap R (FractionRing R)).comp (I : Ideal R).subtype
  have hg : Function.Injective g :=
    (IsFractionRing.injective R (FractionRing R)).comp (I : Ideal R).subtype_injective
  have hgJ : LinearMap.range g = J.val := by
    rw [hJ, IsLocalization.coeSubmodule, LinearMap.range_comp, Submodule.range_subtype]
  let e : (I : Ideal R) ≃ₗ[R] J := (LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ hgJ)
  let : Module.Invertible R (I : Ideal R) := Module.Invertible.congr e.symm
  refine ⟨inferInstance, ?_⟩
  have hPic : ClassGroup.equivPic R (ClassGroup.mk0 I) = Pic.mk R J := by
    rw [ClassGroup.mk0, MonoidHom.comp_apply, ClassGroup.equivPic_apply,
      ← ClassGroup.Quot_mk_eq_mk]
    rfl
  exact hPic.trans (Pic.mk_eq_mk_iff.mpr ⟨e.symm⟩)

variable (M : Submonoid R) (A : Type*) [CommRing A] [IsDedekindDomain A]
  [Algebra R A] [IsLocalization M A]

include M in
/-- The Picard class of a nonzero ideal maps to the class of its extension under localization. -/
theorem picMapAlgebra_equivPic_mk0_of_isLocalization
    (I : (Ideal R)⁰) (J : (Ideal A)⁰) (h : (I : Ideal R).map (algebraMap R A) = J) :
    Pic.mapAlgebra R A (ClassGroup.equivPic R (ClassGroup.mk0 I)) =
      ClassGroup.equivPic A (ClassGroup.mk0 J) := by
  obtain ⟨_, hI⟩ := equivPic_mk0_eq_picMk I
  obtain ⟨_, hJ⟩ := equivPic_mk0_eq_picMk J
  rw [hI, hJ]
  exact Pic.mk_eq_mk_iff.mpr
    ⟨(TensorProduct.AlgebraTensorModule.congr (.refl ..) (Pic.mk.linearEquiv ..)) ≪≫ₗ
      (IsLocalizedModule.isBaseChange M A (Algebra.idealMap A (I : Ideal R))).equiv ≪≫ₗ
      LinearEquiv.ofEq _ _ h⟩

include M in
/-- Base change to a localization of a Dedekind domain is surjective on Picard groups. -/
theorem picMapAlgebra_surjective_of_isLocalization : Function.Surjective (Pic.mapAlgebra R A) := by
  intro x
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective ((ClassGroup.equivPic A).symm x)
  let I := (J : Ideal A).under R
  have himage : I.map (algebraMap R A) = (J : Ideal A) := IsLocalization.map_under M A J
  have hI : I ≠ ⊥ := by
    intro he
    apply nonZeroDivisors.ne_zero J.property
    rw [← himage, he, Ideal.map_bot]
    rfl
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  refine ⟨ClassGroup.equivPic R (ClassGroup.mk0 I₀), ?_⟩
  rw [picMapAlgebra_equivPic_mk0_of_isLocalization M A I₀ J himage, hJ,
    MulEquiv.apply_symm_apply]

end RiemannMasullo
