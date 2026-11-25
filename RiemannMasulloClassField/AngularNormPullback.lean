module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Topology.Algebra.PontryaginDual
public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueCore
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Angular characters of an idèle-class norm pullback

For a finite Galois extension, each nonempty fibre on finite-order characters has
size equal to the order of the abelianized Galois group. This gives the
finite-exceptional-character step in the cubic application of Proposition 10.2.2.2
described by fpet19 in the discussion of issue #7485.
-/

public noncomputable section

open NumberField Function Set
open scoped NNReal

namespace RiemannMasullo

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
local notation "C[" E "]" => NumberField.IdeleClassGroup (𝓞 E) E
local notation "U[" E "]" => PontryaginDual C[E]

/-- Pull a character back by the relative idèle-class norm and restrict it to
the norm-one idèle classes of the extension field. -/
@[expose] def angularNormPullback [Algebra K L] [FiniteDimensional K L] :
    U[K] →* PontryaginDual (ideleClassNorm L).ker :=
  (PontryaginDual.map
    (⟨(ideleClassNorm L).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm L).ker →ₜ* C[L])).toMonoidHom.comp
    (PontryaginDual.map (IdeleClassGroup.normContinuousMonoidHom K L)).toMonoidHom

/-- Evaluate the angular pullback on a norm-one idèle class. -/
@[simp] theorem angularNormPullback_apply [Algebra K L] [FiniteDimensional K L]
    (χ : U[K]) (x : (ideleClassNorm L).ker) :
    angularNormPullback K L χ x = χ (IdeleClassGroup.normContinuousMonoidHom K L x.val) := rfl

/-- A finite-order character trivial on the norm-one subgroup factors through
the divisible group of positive reals and is therefore trivial. -/
private theorem finiteOrderCharacter_eq_one_of_trivial_on_normOne
    (χ : U[L]) (hχ : IsOfFinOrder χ) (h : ∀ x : (ideleClassNorm L).ker, χ x.val = 1) :
    χ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  let m := ideleClassNorm L
  let σ := (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 L) L)).comp
    (canonicalIdeleNormSection L)
  have hσ : RightInverse σ m := canonicalIdeleNormSection_rightInverse L
  ext1 x
  let r := m x
  let u := Units.map (NNReal.rpowMonoidHom (n : ℝ)⁻¹) r
  have hu : u ^ n = r := Units.ext (NNReal.rpow_inv_natCast_pow _ hn.ne')
  have hx : x / σ u ^ n ∈ m.ker := by
    rw [MonoidHom.mem_ker, map_div, map_pow, hσ, hu]
    change r / r = 1
    simp
  have ht := h ⟨x / σ u ^ n, hx⟩
  change χ (x / σ u ^ n) = 1 at ht
  have hy : χ (σ u) ^ n = 1 :=
    (ContinuousMonoidHom.pow_apply χ n (σ u)).symm.trans (DFunLike.congr_fun hpow (σ u))
  rwa [map_div, map_pow, hy, div_one] at ht

variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private theorem normPullback_ker_card :
    Nat.card (PontryaginDual.map (IdeleClassGroup.normContinuousMonoidHom K L)).toMonoidHom.ker =
      Nat.card (Group.Abelianization (Gal(L / K))) := by
  let f := IdeleClassGroup.normContinuousMonoidHom K L
  let H := f.toMonoidHom.range
  let Q := C[K] ⧸ H
  let T := (PontryaginDual.map f).toMonoidHom.ker
  have : H.FiniteIndex := GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex
  have : Finite Q := inferInstanceAs (Finite (C[K] ⧸ H))
  have : DiscreteTopology Q :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotient_discreteTopology
  let q : C[K] →ₜ* Q := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  let e : T ≃ (Q →* Circle) :=
    { toFun := fun χ ↦ QuotientGroup.lift H χ.val.toMonoidHom (by
        rintro _ ⟨b, rfl⟩
        exact DFunLike.congr_fun χ.property b)
      invFun := fun χ ↦
        ⟨(⟨χ, continuous_of_discreteTopology⟩ : Q →ₜ* Circle).comp q, by
          ext1 b
          change χ (QuotientGroup.mk' H (f b)) = 1
          have hb : QuotientGroup.mk' H (f b) = 1 :=
            (QuotientGroup.eq_one_iff (N := H) (f b)).mpr ⟨b, rfl⟩
          rw [hb, map_one]⟩
      left_inv := fun χ ↦ Subtype.ext (PontryaginDual.ext (fun _ ↦ rfl))
      right_inv := fun χ ↦ MonoidHom.ext fun z ↦ by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
        rfl }
  calc
    Nat.card T = Nat.card (Q →* Circleˣ) :=
      Nat.card_congr (e.trans MonoidHom.toHomUnitsMulEquiv.toEquiv)
    _ = Nat.card Q := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q Circle
    _ = _ := GlobalClassFieldTheory.Reciprocity.ideleClassNorm_index_eq_galoisAbelianization_card K L

/-- The fibre through a finite-order idèle-class character consists of exactly
as many finite-order characters as there are elements of the abelianized Galois group. -/
theorem angularNormPullback_fiber_card (η : U[K]) (hη : IsOfFinOrder η) :
    Nat.card {χ : U[K] // IsOfFinOrder χ ∧ angularNormPullback K L χ = angularNormPullback K L η} =
      Nat.card (Group.Abelianization (Gal(L / K))) := by
  let f := PontryaginDual.map (IdeleClassGroup.normContinuousMonoidHom K L)
  let T := f.toMonoidHom.ker
  have hc : Nat.card T = Nat.card (Group.Abelianization (Gal(L / K))) := normPullback_ker_card K L
  have hpos : 0 < Nat.card (Group.Abelianization (Gal(L / K))) :=
    Nat.card_pos (α := (Gal(L / K)) ⧸ commutator (Gal(L / K)))
  have : Finite T := (Nat.card_pos_iff.mp (hc.symm ▸ hpos)).2
  let B := {χ : U[K] // IsOfFinOrder χ ∧ angularNormPullback K L χ = angularNormPullback K L η}
  let e : B ≃ T :=
    { toFun := fun χ ↦ ⟨χ.val / η, by
        apply finiteOrderCharacter_eq_one_of_trivial_on_normOne L
        · apply f.toMonoidHom.isOfFinOrder
          rw [div_eq_mul_inv]
          exact χ.property.1.mul hη.inv
        · intro x
          change (χ.val / η) (IdeleClassGroup.normContinuousMonoidHom K L x.val) = 1
          exact div_eq_one.mpr (DFunLike.congr_fun χ.property.2 x)⟩
      invFun := fun θ ↦ ⟨θ.val * η, by
        constructor
        · exact (f.toMonoidHom.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite θ)).mul hη
        · have h : angularNormPullback K L θ.val = 1 := by
            ext1 x
            exact DFunLike.congr_fun θ.property x.val
          rw [map_mul, h, one_mul]⟩
      left_inv := fun χ ↦ Subtype.ext (div_mul_cancel _ _)
      right_inv := fun θ ↦ Subtype.ext (mul_div_cancel_right _ _) }
  exact (Nat.card_congr e).trans hc

/-- Only finitely many finite-order characters have a prescribed angular norm pullback. -/
theorem angularNormPullback_fiber_finite (ω : PontryaginDual (ideleClassNorm L).ker) :
    {χ : U[K] | IsOfFinOrder χ ∧ angularNormPullback K L χ = ω}.Finite := by
  let B := {χ : U[K] | IsOfFinOrder χ ∧ angularNormPullback K L χ = ω}
  change B.Finite
  rcases B.eq_empty_or_nonempty with h | ⟨η, hη⟩
  · rw [h]
    exact finite_empty
  · obtain ⟨hfin, rfl⟩ := hη
    exact (Nat.card_pos_iff.mp ((angularNormPullback_fiber_card K L η hfin).symm ▸
      (Nat.card_pos (α := (Gal(L / K)) ⧸ commutator (Gal(L / K)))))).2

end RiemannMasullo
