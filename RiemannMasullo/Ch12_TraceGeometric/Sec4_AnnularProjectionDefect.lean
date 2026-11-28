module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RightSupportedTraceCompression
import RiemannMasullo.Ch10_TraceSpectral.Sec4a

/-! # Trace defect under a change of Sobolev density -/

public noncomputable section

open Filter
open scoped Topology

namespace RiemannMasullo

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem nuclear_postcomp_between_hilbert (U : F →L[ℂ] E)
    (T : nuclearEndomorphisms F) : IsNuclearOperator (U.comp T.val) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ :=
    (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr
    ⟨c, φ, U ∘ y, hc, hφ, (U.continuous.tendsto' 0 0 (map_zero U)).comp hy, fun x ↦ ?_⟩
  change HasSum (fun n ↦ (c n * φ n x) • U (y n)) (U (T.val x))
  simpa only [map_smul] using U.hasSum (hsum x)

/-- For an idempotent, the trace of a two-sided compression equals the trace
of the single left compression. -/
theorem hilbertTrace_nuclearCompress_eq_left_of_idempotent
    (P : E →L[ℂ] E) (hP : P * P = P) (T : nuclearEndomorphisms E) :
    hilbertTrace (Isolated.nuclearCompress P T) =
      hilbertTrace ⟨P * T.val, mul_mem_nuclearEndomorphisms_left P T⟩ := by
  let A : nuclearEndomorphisms E := ⟨P * T.val, mul_mem_nuclearEndomorphisms_left P T⟩
  have hLeft : (⟨P * A.val, mul_mem_nuclearEndomorphisms_left P A⟩ :
      nuclearEndomorphisms E) = A := by
    apply Subtype.ext
    change P * (P * T.val) = P * T.val
    rw [← mul_assoc, hP]
  have hRight : (⟨A.val * P, mul_mem_nuclearEndomorphisms_right P A⟩ :
      nuclearEndomorphisms E) = Isolated.nuclearCompress P T := rfl
  simpa only [hLeft, hRight, A] using (spectralRestriction_cyclic P A).symm

/-- When an annular operator is transferred to a second Hilbert space by a
continuous inclusion and a bounded lift of its output, the original trace
and the discrepancy between the two projections give the compressed trace.
`hOutput` says the lift followed by inclusion fixes the original output. -/
theorem hilbertTrace_nuclearCompress_eq_add_projectionDefect
    (J : E →L[ℂ] F) (hJ : Function.Injective J) (L : F →L[ℂ] E)
    (P : E →L[ℂ] E) (hP : P * P = P) (Q : F →L[ℂ] F)
    (T : nuclearEndomorphisms F) (hRight : T.val * Q = T.val)
    (hOutput : (J.comp L) * T.val = T.val) :
    ∃ hTransfer : IsNuclearOperator ((L.comp T.val).comp J),
      let D := (J.comp P - Q.comp J).comp L
      hilbertTrace (Isolated.nuclearCompress P ⟨_, hTransfer⟩) =
        hilbertTrace T + hilbertTrace ⟨D * T.val, mul_mem_nuclearEndomorphisms_left D T⟩ := by
  let R := L.comp T.val
  have hR := nuclear_postcomp_between_hilbert L T
  let C : nuclearEndomorphisms E :=
    ⟨R.comp J, (isNuclearOperator_factor_comps J hJ R hR).1⟩
  refine ⟨C.property, ?_⟩
  intro D
  let A := (P.comp L).comp T.val
  have hA := nuclear_postcomp_between_hilbert (P.comp L) T
  obtain ⟨hAJ, hJA⟩ := isNuclearOperator_factor_comps J hJ A hA
  let U : nuclearEndomorphisms E := ⟨A.comp J, hAJ⟩
  let V : nuclearEndomorphisms F := ⟨J.comp A, hJA⟩
  have hSwap : hilbertTrace U = hilbertTrace V := by
    rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
    exact nuclearTrace_factor_comps hilbert_approximationProperty hilbert_approximationProperty
      J hJ A hA
  have hPC : (⟨P * C.val, mul_mem_nuclearEndomorphisms_left P C⟩ :
      nuclearEndomorphisms E) = U := rfl
  let R₀ : nuclearEndomorphisms F := ⟨Q * T.val, mul_mem_nuclearEndomorphisms_left Q T⟩
  let Δ : nuclearEndomorphisms F := ⟨D * T.val, mul_mem_nuclearEndomorphisms_left D T⟩
  have hV : V = R₀ + Δ := by
    apply Subtype.ext
    ext x
    change J (P (L (T.val x))) =
      Q (T.val x) + (J (P (L (T.val x))) - Q (J (L (T.val x))))
    have hx : J (L (T.val x)) = T.val x :=
      DFunLike.congr_fun hOutput x
    rw [hx]
    abel
  have hQ : (⟨T.val * Q, mul_mem_nuclearEndomorphisms_right Q T⟩ :
      nuclearEndomorphisms F) = T := Subtype.ext hRight
  have hR₀ : hilbertTrace R₀ = hilbertTrace T := by
    simpa only [hQ, R₀] using spectralRestriction_cyclic Q T
  change hilbertTrace (Isolated.nuclearCompress P C) = hilbertTrace T + hilbertTrace Δ
  rw [hilbertTrace_nuclearCompress_eq_left_of_idempotent P hP C, hPC, hSwap, hV]
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := F)
  rw [← htr, map_add, htr, htr, hR₀]

end RiemannMasullo
