module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRetraction

/-! # Preservation of nuclear trace and trace norm by unitary conjugation -/

public noncomputable section
namespace RiemannMasullo
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem traceNorm_nonneg_explicit (A : E →L[ℂ] E) (hA : IsNuclearOperator A) :
    0 ≤ traceNorm ⟨A,hA⟩ := (norm_nonneg (hilbertTrace ⟨A,hA⟩)).trans (norm_hilbertTrace_le _)

/-- Unitary conjugation preserves nuclearity, trace norm, and Hilbert trace. -/
theorem nuclear_trace_unitary (U : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (hA : IsNuclearOperator A) :
    ∃ hB : IsNuclearOperator (U.toLinearIsometry.toContinuousLinearMap.comp (A.comp U.symm.toLinearIsometry.toContinuousLinearMap)),
      traceNorm ⟨_,hB⟩ = traceNorm ⟨A,hA⟩ ∧ hilbertTrace ⟨_,hB⟩ = hilbertTrace ⟨A,hA⟩ := by
  let J := U.toLinearIsometry.toContinuousLinearMap
  let Q := U.symm.toLinearIsometry.toContinuousLinearMap
  have hQJ : Q.comp J = ContinuousLinearMap.id ℂ E := by
    apply ContinuousLinearMap.ext
    intro x
    exact U.symm_apply_apply x
  have hJQ : J.comp Q = ContinuousLinearMap.id ℂ F := by
    apply ContinuousLinearMap.ext
    intro x
    exact U.apply_symm_apply x
  have hnorm : ‖J‖ * ‖Q‖ ≤ 1 := by
    exact (mul_le_mul U.toLinearIsometry.norm_toContinuousLinearMap_le
      U.symm.toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  obtain ⟨hB,hb,ht⟩ := nuclear_trace_retraction J Q hQJ A hA
  have hback : Q.comp ((J.comp (A.comp Q)).comp J) = A := by
    simp only [← ContinuousLinearMap.comp_assoc, hQJ, ContinuousLinearMap.id_comp]
    rw [ContinuousLinearMap.comp_assoc, hQJ, ContinuousLinearMap.comp_id]
  obtain ⟨hA',hb',_⟩ := nuclear_trace_retraction Q J hJQ (J.comp (A.comp Q)) hB
  refine ⟨hB, le_antisymm ?_ ?_, ht⟩
  · exact hb.trans ((mul_le_mul_of_nonneg_right hnorm (traceNorm_nonneg_explicit A hA)).trans_eq (one_mul _))
  · have hnorm' : ‖Q‖ * ‖J‖ ≤ 1 := by simpa only [mul_comm] using hnorm
    have hle := hb'.trans ((mul_le_mul_of_nonneg_right hnorm'
      (traceNorm_nonneg_explicit (J.comp (A.comp Q)) hB)).trans_eq (one_mul _))
    simpa only [hback] using! hle

end RiemannMasullo
