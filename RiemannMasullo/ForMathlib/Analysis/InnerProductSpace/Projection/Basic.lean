module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Factorization through the range of a continuous linear map -/

public section

open Set Topology

namespace RiemannMasullo

/-- A continuous linear map whose pointwise norm is bounded by that of `T` factors through
`T` by a contraction, provided the codomain of `T` is Hilbert and that of `A` is complete. -/
theorem exists_contraction_comp_eq_of_norm_le {𝕜 E H F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] H) (A : E →L[𝕜] F) (h : ∀ x, ‖A x‖ ≤ ‖T x‖) :
    ∃ S : H →L[𝕜] F, ‖S‖ ≤ 1 ∧ S.comp T = A := by
  let K := T.toLinearMap.range.topologicalClosure
  let e : E →ₗ[𝕜] K := T.toLinearMap.codRestrict K fun x ↦
    T.toLinearMap.range.le_topologicalClosure (LinearMap.mem_range_self _ x)
  have he : DenseRange e := by
    apply IsInducing.subtypeVal.dense_iff.mpr
    intro x
    rw [← range_comp]
    exact x.property
  have hbound (x : E) : ‖A.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    rw [one_mul, ← Submodule.norm_coe]
    exact h x
  let S := A.toLinearMap.extendOfNorm e
  refine ⟨S.comp K.orthogonalProjectionOnto, ?_, ?_⟩
  · calc
      _ ≤ ‖S‖ * ‖K.orthogonalProjectionOnto‖ := S.opNorm_comp_le _
      _ ≤ 1 * 1 := mul_le_mul (LinearMap.opNorm_extendOfNorm_le he zero_le_one hbound)
        K.orthogonalProjectionOnto_norm_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · ext x
    change S (K.orthogonalProjectionOnto (e x : H)) = A x
    rw [K.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact LinearMap.extendOfNorm_eq he ⟨1, hbound⟩ x

end RiemannMasullo
