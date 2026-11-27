module
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public noncomputable section
open Set
open scoped InnerProductSpace
namespace RiemannMasullo

/-- A mutually orthogonal family of fibers admits a bounded projection that
retains every generating vector in one fiber and annihilates all other fibers. -/
theorem exists_projection_of_orthogonal_fibers
    {I J H : Type*} [DecidableEq I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : J → H) (label : J → I)
    (horth : ∀ j k, label j ≠ label k → ⟪u j, u k⟫_ℂ = 0) (i : I) :
    ∃ P : H →L[ℂ] H, ∀ j, P (u j) = if label j = i then u j else 0 := by
  classical
  let K := (Submodule.span ℂ (u '' {j | label j = i})).topologicalClosure
  refine ⟨K.starProjection, fun j ↦ ?_⟩
  by_cases hj : label j = i
  · rw [ite_eq_left hj]
    exact K.starProjection_eq_self_iff.mpr
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, hj, rfl⟩))
  · rw [ite_eq_right hj]
    apply K.starProjection_apply_eq_zero_iff.mpr
    have hK : K ≤ (ℂ ∙ u j)ᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      apply Submodule.span_le.mpr
      rintro v ⟨k, hk, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (horth j k (fun h ↦ hj (h.trans hk)))
    exact (K.mem_orthogonal' _).mpr fun v hv ↦
      Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self _) (hK hv)

end RiemannMasullo
