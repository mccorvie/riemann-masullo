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
/-- Base change to a localization of a Dedekind domain is surjective on Picard groups. -/
theorem picMapAlgebra_surjective_of_isLocalization : Function.Surjective (Pic.mapAlgebra R A) := by
  intro x
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective ((ClassGroup.equivPic A).symm x)
  obtain ⟨_, hPicJ⟩ := equivPic_mk0_eq_picMk J
  let I := (J : Ideal A).under R
  have himage : I.map (algebraMap R A) = (J : Ideal A) := IsLocalization.map_under M A J
  have hI : I ≠ ⊥ := by
    intro he
    apply nonZeroDivisors.ne_zero J.property
    rw [← himage, he, Ideal.map_bot]
    rfl
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  obtain ⟨_, hPicI⟩ := equivPic_mk0_eq_picMk I₀
  let e := (IsLocalizedModule.isBaseChange M A (Algebra.idealMap A I)).equiv.trans
    (LinearEquiv.ofEq _ _ himage)
  refine ⟨ClassGroup.equivPic R (ClassGroup.mk0 I₀), ?_⟩
  calc
    _ = Pic.mapAlgebra R A (Pic.mk R (I₀ : Ideal R)) := congrArg _ hPicI
    _ = Pic.mk A (J : Ideal A) := Pic.mk_eq_mk_iff.mpr
      ⟨(TensorProduct.AlgebraTensorModule.congr (.refl ..) (Pic.mk.linearEquiv ..)) ≪≫ₗ e⟩
    _ = x := hPicJ.symm.trans (by rw [hJ, MulEquiv.apply_symm_apply])

end RiemannMasullo
