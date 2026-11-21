module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

namespace RiemannMasullo

/-- A continuous additive equivalence that carries the first summand onto the first
summand induces equivalences of the first summands and of the second summands. -/
theorem continuousAddEquiv_factors_of_snd_eq_zero
    {A B A' B' : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass A'] [AddZeroClass B']
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    (e : A × B ≃ₜ+ A' × B') (he : ∀ a, (e (a, 0)).2 = 0)
    (he' : ∀ a', (e.symm (a', 0)).2 = 0) :
    Nonempty (A ≃ₜ+ A') ∧ Nonempty (B ≃ₜ+ B') := by
  have hfst (a : A) : ((e (a, 0)).1, 0) = e (a, 0) := Prod.ext rfl (he a).symm
  have hfst' (a' : A') : ((e.symm (a', 0)).1, 0) = e.symm (a', 0) :=
    Prod.ext rfl (he' a').symm
  have hsnd (a : A) (b : B) : (e (a, b)).2 = (e (0, b)).2 := by
    have hadd : (a, b) = (a, 0) + (0, b) := by simp
    rw [hadd, map_add, Prod.snd_add, he, zero_add]
  have hsnd' (a' : A') (b' : B') : (e.symm (a', b')).2 = (e.symm (0, b')).2 := by
    have hadd : (a', b') = (a', 0) + (0, b') := by simp
    rw [hadd, map_add, Prod.snd_add, he', zero_add]
  refine ⟨⟨{
    toFun := fun a ↦ (e (a, 0)).1
    invFun := fun a' ↦ (e.symm (a', 0)).1
    left_inv := fun a ↦ by simp only [hfst, ContinuousAddEquiv.symm_apply_apply]
    right_inv := fun a' ↦ by simp only [hfst', ContinuousAddEquiv.apply_symm_apply]
    map_add' := fun a b ↦ by simpa using congrArg Prod.fst (map_add e (a, 0) (b, 0))
    continuous_toFun := (e.continuous_toFun.comp (continuous_id.prodMk continuous_const)).fst
    continuous_invFun := (e.continuous_invFun.comp (continuous_id.prodMk continuous_const)).fst
  }⟩, ⟨{
    toFun := fun b ↦ (e (0, b)).2
    invFun := fun b' ↦ (e.symm (0, b')).2
    left_inv := fun b ↦ by
      dsimp only
      rw [← hsnd' (e (0, b)).1, Prod.eta, ContinuousAddEquiv.symm_apply_apply]
    right_inv := fun b' ↦ by
      dsimp only
      rw [← hsnd (e.symm (0, b')).1, Prod.eta, ContinuousAddEquiv.apply_symm_apply]
    map_add' := fun a b ↦ by simpa using congrArg Prod.snd (map_add e (0, a) (0, b))
    continuous_toFun := (e.continuous_toFun.comp (continuous_const.prodMk continuous_id)).snd
    continuous_invFun := (e.continuous_invFun.comp (continuous_const.prodMk continuous_id)).snd
  }⟩⟩

end RiemannMasullo
