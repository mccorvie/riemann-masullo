module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualReflectedPolarComplement

/-! # Stability of the polar trace correction under frequency smoothing -/

public noncomputable section

open scoped InnerProductSpace

namespace RiemannMasullo

/-- Changing the frequency multiplier changes the difference of the two
compressed traces only through its action on the reflected polar vector. -/
theorem norm_hilbertTrace_smoothPolarDifference_sub_inner_le
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (T : H →L[ℂ] K) (M : K →L[ℂ] K)
    (C : nuclearEndomorphisms H) (hC : C.val = A.comp (T.adjoint.comp (M.comp T)))
    (V B : Submodule ℂ H) [V.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hVB : V ≤ B) (u : H) (e : K) (hu : ‖u‖ = 1) (hK : B ⊓ Vᗮ = ℂ ∙ u)
    (hTu : T u = e) (hAdj : T.adjoint e = u) (hT : ‖T‖ ≤ 1) :
    ‖(hilbertTrace (Isolated.nuclearCompress B.starProjection C) -
      hilbertTrace (Isolated.nuclearCompress V.starProjection C)) - ⟪u, A u⟫_ℂ‖ ≤
      ‖A‖ * ‖M e - e‖ := by
  rw [Isolated.hilbertTrace_nuclearCompress_sub_eq_inner_of_complement_line C V B hVB u hu hK,
    hC]
  change ‖⟪u, A (T.adjoint (M (T u)))⟫_ℂ - ⟪u, A u⟫_ℂ‖ ≤ ‖A‖ * ‖M e - e‖
  have hDiff : A (T.adjoint (M e)) - A u = A (T.adjoint (M e - e)) := by
    rw [map_sub, map_sub, hAdj]
  rw [hTu, ← inner_sub_right, hDiff]
  calc
    _ ≤ ‖u‖ * ‖A (T.adjoint (M e - e))‖ := norm_inner_le_norm _ _
    _ = ‖A (T.adjoint (M e - e))‖ := by rw [hu, one_mul]
    _ ≤ ‖A‖ * ‖T.adjoint (M e - e)‖ := A.le_opNorm _
    _ ≤ ‖A‖ * ‖M e - e‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
      calc
        _ ≤ ‖T.adjoint‖ * ‖M e - e‖ := T.adjoint.le_opNorm _
        _ = ‖T‖ * ‖M e - e‖ :=
          congrArg (· * ‖M e - e‖) (ContinuousLinearMap.adjoint.norm_map T)
        _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hT

end RiemannMasullo
