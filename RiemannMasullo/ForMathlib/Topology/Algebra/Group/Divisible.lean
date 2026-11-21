module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Subgroup

@[expose] public noncomputable section

open Topology

namespace RiemannMasullo

/-- An open divisible subgroup of an abelian topological group splits off as a
topological direct factor, with discrete complementary factor given by the quotient. -/
theorem exists_continuousAddEquiv_prod_quotient_of_open {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] (H : AddSubgroup A)
    (hH : IsOpen (H : Set A)) [DivisibleBy H ℤ] :
    Nonempty (A ≃ₜ+ H × (A ⧸ H)) := by
  have := QuotientAddGroup.discreteTopology hH
  have := (Module.Baer.of_divisible H).injective
  obtain ⟨rₗ, hrₗ⟩ := Module.Injective.out H.subtype.toIntLinearMap
    Subtype.val_injective (LinearMap.id : H →ₗ[ℤ] H)
  let r := rₗ.toAddMonoidHom
  have hr (x : H) : r x.val = x := hrₗ x
  have hCont : Continuous r := by
    refine continuous_of_continuousAt_zero r (ContinuousOn.continuousAt ?_ (hH.mem_nhds H.zero_mem))
    rw [continuousOn_iff_continuous_domRestrict]
    have hId : (H : Set A).domRestrict r = id := funext hr
    rw [hId]
    exact continuous_id
  let s := QuotientAddGroup.lift H (AddMonoidHom.id A - H.subtype.comp r) (by
    intro x hx
    change x - (r x).val = 0
    rw [hr ⟨x, hx⟩, sub_self])
  have hs (x : A) : s (QuotientAddGroup.mk x) = x - (r x).val := rfl
  refine ⟨{
    toFun := fun x ↦ (r x, QuotientAddGroup.mk x)
    invFun := fun y ↦ y.1.val + s y.2
    left_inv := fun x ↦ by
      change (r x).val + s (QuotientAddGroup.mk x) = x
      rw [hs, add_comm, sub_add_cancel]
    right_inv := ?_
    map_add' := fun x y ↦ Prod.ext (map_add r x y) (map_add (QuotientAddGroup.mk' H) x y)
    continuous_toFun := hCont.prodMk QuotientAddGroup.continuous_mk
    continuous_invFun := (continuous_subtype_val.comp continuous_fst).add
      (continuous_of_discreteTopology.comp continuous_snd) }⟩
  rintro ⟨y, q⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  change (r (y.val + s (QuotientAddGroup.mk x)), (QuotientAddGroup.mk' H) _) = _
  rw [hs]
  apply Prod.ext
  · simp [map_add, map_sub, hr]
  · have hzero (z : H) : (QuotientAddGroup.mk' H) z.val = 0 :=
      (QuotientAddGroup.eq_zero_iff z.val).2 z.property
    change (QuotientAddGroup.mk' H) (y.val + (x - (r x).val)) = (QuotientAddGroup.mk' H) x
    simp only [map_add, map_sub, hzero, sub_zero, zero_add]

end RiemannMasullo
