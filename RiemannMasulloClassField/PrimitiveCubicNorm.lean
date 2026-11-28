module

public import RiemannMasulloClassField.AngularNormPullback
public import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-! # Primitive Dirichlet characters on a cubic splitting field

For the component arithmetic of Proposition 10.2.2.2 (pp. 446–447), each nonempty
angular norm fibre for the splitting field of X³ − 2 consists of two primitive
Dirichlet characters across all positive conductors.
-/

public noncomputable section

open NumberField
open scoped commutatorElement

namespace RiemannMasullo

local notation "L" => Polynomial.SplittingField (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ))
local notation "Uℚ" => PontryaginDual (NumberField.IdeleClassGroup (𝓞 ℚ) ℚ)
local notation "PrimitiveLabels" => (N : ℕ+) × {χ : DirichletCharacter ℂ (N : ℕ) //
  DirichletCharacter.IsPrimitive χ}
local instance : NumberField L := ⟨⟩

/-- Exactly two primitive Dirichlet characters have the same angular norm pullback as a
given primitive character on the splitting field of X³ − 2. -/
theorem primitiveDirichlet_X_cube_sub_two_angularNorm_fiber_card (η : PrimitiveLabels) :
    Nat.card {χ : PrimitiveLabels //
      angularNormPullback ℚ L (primitiveDirichletHeckeEquiv χ).val =
        angularNormPullback ℚ L (primitiveDirichletHeckeEquiv η).val} = 2 := by
  have : IsGalois ℚ L := ⟨⟩
  let angular := angularNormPullback ℚ L
  let e := primitiveDirichletHeckeEquiv
  let sameComponent (ψ : Uℚ) := angular ψ = angular (e η).val
  calc
    Nat.card {χ : PrimitiveLabels // sameComponent (e χ).val} =
        Nat.card {ψ : {χ : Uℚ // IsOfFinOrder χ} // sameComponent ψ.val} :=
      Nat.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl))
    _ = Nat.card {χ : Uℚ // IsOfFinOrder χ ∧ sameComponent χ} :=
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter IsOfFinOrder sameComponent)
    _ = Nat.card (Group.Abelianization (Gal(L / ℚ))) :=
      angularNormPullback_fiber_card ℚ L _ (e η).property
    _ = 2 := by
      obtain ⟨g⟩ := splittingField_X_cube_sub_two_galoisGroup
      apply (Nat.card_congr g.abelianizationCongr.toEquiv).trans
      change (commutator (Equiv.Perm (Fin 3))).index = 2
      suffices h : commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) by
        rw [h, alternatingGroup.index_eq_two]
      apply le_antisymm alternatingGroup.commutator_perm_le
      intro x hx
      have h : ∀ x : Equiv.Perm (Fin 3), x.sign = 1 → ∃ a b : Equiv.Perm (Fin 3), ⁅a,b⁆ = x := by
        decide
      obtain ⟨a, b, rfl⟩ := h x (Equiv.Perm.mem_alternatingGroup.mp hx)
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

end RiemannMasullo
