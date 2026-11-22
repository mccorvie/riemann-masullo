module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Continuous actions and splittings on kernel quotients -/

public section

namespace RiemannMasullo

/-- A discrete subgroup acting by continuous linear endomorphisms descends to a
jointly continuous action on the quotient by an invariant kernel. -/
theorem exists_ker_quotientAction {R U X Y : Type*} [Ring R] [Group U] [TopologicalSpace U]
    [AddCommGroup X] [Module R X] [TopologicalSpace X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] (N : Subgroup U) [DiscreteTopology N]
    (A : X →L[R] Y) (ρ : U →* (X →L[R] X))
    (hinv : ∀ (g : N) (f : X), f ∈ A.ker → ρ g.val f ∈ A.ker) :
    let V := X ⧸ A.ker
    ∃ r : N →* (V →L[R] V),
      (∀ (g : N) (f : X), r g (A.ker.mkQ f) = A.ker.mkQ (ρ g.val f)) ∧
      Continuous (fun z : N × V ↦ r z.1 z.2) := by
  let r₀ := ρ.comp N.subtype
  let act (g : N) := A.ker.liftQL (A.ker.mkQL.comp (r₀ g)) fun x hx ↦
    (Submodule.Quotient.mk_eq_zero A.ker).mpr (hinv g x hx)
  have happ (g : N) (x : X) : act g (A.ker.mkQ x) = A.ker.mkQ (r₀ g x) := rfl
  let r : N →* ((X ⧸ A.ker) →L[R] (X ⧸ A.ker)) :=
    { toFun := act
      map_one' := by
        apply ContinuousLinearMap.ext
        intro v
        obtain ⟨x, rfl⟩ := A.ker.mkQ_surjective v
        rw [happ, map_one]
        rfl
      map_mul' := fun g k ↦ by
        apply ContinuousLinearMap.ext
        intro v
        obtain ⟨x, rfl⟩ := A.ker.mkQ_surjective v
        rw [mul_apply_eq_comp, happ, happ, happ, map_mul, mul_apply_eq_comp] }
  exact ⟨r, happ, continuous_prod_of_discrete_left.mpr fun g ↦ (act g).continuous⟩

/-- A continuous linear map with a continuous linear right inverse identifies its
kernel quotient continuously and linearly with its target. -/
theorem exists_ker_quotientEquiv_of_rightInverse {R X Y : Type*} [Ring R]
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [AddCommGroup Y] [Module R Y] [TopologicalSpace Y]
    (A : X →L[R] Y) (J : Y →L[R] X) (hJ : ∀ y, A (J y) = y) :
    ∃ e : (X ⧸ A.ker) ≃L[R] Y, ∀ x, e (A.ker.mkQ x) = A x := by
  have hr : Function.RightInverse J A := hJ
  let e := A.toLinearMap.quotKerEquivOfSurjective hr.surjective
  have he : Continuous e := A.ker.isQuotientMap_mkQL.continuous_iff.mpr A.continuous
  have hi : Continuous e.symm := (A.ker.mkQL.continuous.comp J.continuous).congr fun y ↦
    (A.toLinearMap.quotKerEquivOfSurjective_symm_apply hr.surjective (J y)).symm.trans
      (congrArg e.symm (hJ y))
  exact ⟨⟨e, he, hi⟩, fun _ ↦ rfl⟩

end RiemannMasullo
