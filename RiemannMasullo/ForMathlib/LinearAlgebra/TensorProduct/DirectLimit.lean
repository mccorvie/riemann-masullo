module

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

public section

open scoped TensorProduct

namespace RiemannMasullo

/-- A tensor of two directed colimits comes from a single pair of stages. -/
theorem exists_pairwise_tensor_stage {R I J : Type*} [CommSemiring R] [Preorder I] [Preorder J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]
    {X : I → Type*} {Y : J → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
    [∀ j, AddCommMonoid (Y j)] [∀ j, Module R (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[R] X j) (g : ∀ i j, i ≤ j → Y i →ₗ[R] Y j)
    (z : Module.DirectLimit X f ⊗[R] Module.DirectLimit Y g) :
    ∃ (i : I) (j : J) (b : X i ⊗[R] Y j), TensorProduct.map (Module.DirectLimit.of R I X f i)
      (Module.DirectLimit.of R J Y g j) b = z := by
  let u := Module.DirectLimit.of R I X f
  let v := Module.DirectLimit.of R J Y g
  obtain ⟨i, a, ha⟩ := Module.DirectLimit.exists_of
    (TensorProduct.directLimitLeft f (Module.DirectLimit Y g) z)
  obtain ⟨j, b, hb⟩ := Module.DirectLimit.exists_of (TensorProduct.directLimitRight g (X i) a)
  have hleft := (TensorProduct.directLimitLeft f _).injective
    ((TensorProduct.directLimitLeft_rTensor_of f _ a).trans ha)
  have hright : (v j).lTensor (X i) b = a := by
    apply (TensorProduct.directLimitRight g (X i)).injective
    refine Eq.trans ?_ hb
    clear hb
    induction b using TensorProduct.inductionOn with
    | tmul x y => exact TensorProduct.directLimitRight_tmul_of g (X i) x y
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨i, j, b, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hright]
  exact hleft

end RiemannMasullo
