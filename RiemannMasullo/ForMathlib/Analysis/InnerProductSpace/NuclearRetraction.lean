module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-! # Nuclear traces through Hilbert-space sections

A bounded section and retraction preserve the trace of the transported nuclear
operator. The trace-norm bound is explicit for later orthogonal compressions.
-/

public noncomputable section
open Filter Function
open scoped Topology
namespace RiemannMasullo
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem nuclear_precomp (A : E →L[ℂ] E) (hA : IsNuclearOperator A)
    (Q : F →L[ℂ] E) : IsNuclearOperator (A.comp Q) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, fun n ↦ (φ n).comp Q, y, hc, ?_, hy, fun x ↦ hs (Q x)⟩
  have hcont : Continuous (fun f : E →L[ℂ] ℂ ↦ f.comp Q) := by fun_prop
  simpa only [ContinuousLinearMap.zero_comp, Function.comp_def] using!
    (hcont.tendsto (0 : E →L[ℂ] ℂ)).comp hφ

/-- A nuclear operator has the same Hilbert trace after transport through a
bounded section and retraction. The section need not be onto. -/
theorem nuclear_trace_retraction (J : E →L[ℂ] F) (Q : F →L[ℂ] E)
    (hQJ : Q.comp J = ContinuousLinearMap.id ℂ E)
    (A : E →L[ℂ] E) (hA : IsNuclearOperator A) :
    ∃ hB : IsNuclearOperator (J.comp (A.comp Q)),
      traceNorm ⟨_, hB⟩ ≤ (‖J‖ * ‖Q‖) * traceNorm ⟨A, hA⟩ ∧
      hilbertTrace ⟨_, hB⟩ = hilbertTrace ⟨A, hA⟩ := by
  have hJ : Injective J := by
    intro x y h
    have he (z : E) : Q (J z) = z := congrArg (fun f : E →L[ℂ] E ↦ f z) hQJ
    simpa only [he] using congrArg Q h
  have hAQ := nuclear_precomp A hA Q
  have hrev : (A.comp Q).comp J = A := by
    rw [ContinuousLinearMap.comp_assoc, hQJ, ContinuousLinearMap.comp_id]
  obtain ⟨hn, hb⟩ := traceNorm_sandwich_le A hA Q J
  refine ⟨hn, hb, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  have ht := nuclearTrace_factor_comps (hilbert_approximationProperty (H := E))
    (hilbert_approximationProperty (H := F)) J hJ (A.comp Q) hAQ
  simpa only [hrev] using ht.symm

end RiemannMasullo
