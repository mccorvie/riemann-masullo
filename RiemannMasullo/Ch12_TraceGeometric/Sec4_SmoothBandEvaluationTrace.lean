module

public import RiemannMasullo.AppC_LCTVS.Sec3a
import RiemannMasullo.Ch10_TraceSpectral.Sec4a

/-! # Trace correction for a smooth band operator at a vanishing evaluation -/

public noncomputable section

namespace RiemannMasullo

/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 515–519.
Reconstruction: Let `N` be a nuclear operator whose image is fixed by a bounded frequency
cutoff `T`. If `N` acts by the scalar `c` on the evaluation `e`, compressing
`N * T` to the kernel of `e` subtracts just `c * e (T u)` from its trace.
Here `P` is the projection along a vector `u` normalized by `e u = 1`.
In the even rational band, `e` is evaluation at the origin and the image of
`N` lies in the interior plateau of the cutoff because dilation shrinks the
band and the smoothed spatial mask has small Fourier support. -/
theorem hilbertTrace_smoothBand_evaluationCompression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : nuclearEndomorphisms H) (T : H →L[ℂ] H)
    (e : H →L[ℂ] ℂ) (u : H) (hu : e u = 1) (c : ℂ)
    (hBand : T * N.val = N.val) (hEval : ∀ x, e (N.val x) = c * e x) :
    let P := ContinuousLinearMap.id ℂ H - e.smulRight u
    let A : nuclearEndomorphisms H := ⟨N.val * T, mul_mem_nuclearEndomorphisms_right T N⟩
    let B : nuclearEndomorphisms H := ⟨P * A.val, mul_mem_nuclearEndomorphisms_left P A⟩
    hilbertTrace ⟨B.val * P, mul_mem_nuclearEndomorphisms_right P B⟩ =
      hilbertTrace N - c * e (T u) := by
  intro P A B
  have hP_apply (x : H) : P x = x - e x • u := rfl
  have hP : P * P = P := by
    ext x
    change P (P x) = P x
    rw [hP_apply (P x), hP_apply x, map_sub, map_smul, hu, smul_eq_mul,
      mul_one, sub_self, zero_smul, sub_zero]
  have hTraceA : hilbertTrace A = hilbertTrace N := by
    have hFixed :
        (⟨T * N.val, mul_mem_nuclearEndomorphisms_left T N⟩ : nuclearEndomorphisms H) = N :=
      Subtype.ext hBand
    exact (spectralRestriction_cyclic T N).symm.trans (congrArg hilbertTrace hFixed)
  have hTraceB :
      hilbertTrace (⟨B.val * P, mul_mem_nuclearEndomorphisms_right P B⟩ :
        nuclearEndomorphisms H) = hilbertTrace B := by
    have hFixed :
        (⟨P * B.val, mul_mem_nuclearEndomorphisms_left P B⟩ : nuclearEndomorphisms H) = B := by
      apply Subtype.ext
      change P * (P * A.val) = P * A.val
      rw [← mul_assoc, hP]
    exact (spectralRestriction_cyclic P B).symm.trans (congrArg hilbertTrace hFixed)
  let R : nuclearEndomorphisms H := ⟨(e.comp A.val).smulRight u, isNuclearOperator_smulRight _ _⟩
  have hSplit : B + R = A := by
    apply Subtype.ext
    ext x
    change P (A.val x) + e (A.val x) • u = A.val x
    rw [hP_apply, sub_add_cancel]
  have hTraceR : hilbertTrace R = c * e (T u) := by
    change hilbertTrace ⟨(e.comp A.val).smulRight u, _⟩ = _
    rw [hilbertTrace_smulRight]
    exact hEval (T u)
  obtain ⟨trace, hTrace⟩ := hilbertTrace_linear (H := H)
  have hTraceSum := congrArg trace hSplit
  rw [map_add, hTrace, hTrace, hTrace, hTraceA, hTraceR] at hTraceSum
  rw [hTraceB, ← hTraceSum, add_sub_cancel_right]

end RiemannMasullo
