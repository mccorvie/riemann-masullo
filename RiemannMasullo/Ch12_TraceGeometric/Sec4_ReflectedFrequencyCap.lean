module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RightSupportedTraceCompression
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space.SupportProjection

/-! # Trace compression for a bounded reflected frequency profile -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "logBand(" B ")" =>
  l2IndicatorMultiplier volume (Ici (-Real.log B)) measurableSet_Ici

/-- The reflected multiplier at a finite frequency cap is fixed by the
real half-line projection on its input. -/
theorem reflectedFrequencyMultiplier_comp_logBand
    (M : FlatL2 →L[ℂ] FlatL2) (b : ℝ → ℂ)
    (hM : ∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x)
    (B : ℝ) (hB : 0 < B) (hCap : ∀ t > B, b t = 0) :
    M.comp logBand(B) = M := by
  ext u : 1
  apply Lp.ext
  filter_upwards [hM (logBand(B) u), hM u,
    l2IndicatorMultiplier_ae volume (Ici (-Real.log B)) measurableSet_Ici u]
    with x h₁ h₂ hP
  change M (logBand(B) u) x = M u x
  rw [h₁, h₂, hP]
  by_cases hx : x ∈ Ici (-Real.log B)
  · rw [indicator_of_mem hx]
  · have hxlt : x < -Real.log B := lt_of_not_ge hx
    have hb : B < Real.exp (-x) := calc
      B = Real.exp (Real.log B) := (Real.exp_log hB).symm
      _ < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
    simp only [hCap _ hb, zero_mul]

/-- When the same reflected map intertwines the band projection and the
real half-line projection, a nuclear cutoff action has the trace of its
compression to that band. -/
theorem hilbertTrace_nuclearCompress_eq_of_reflectedFrequencyCap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2) (b : ℝ → ℂ)
    (hM : ∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x)
    (B : ℝ) (hB : 0 < B) (hCap : ∀ t > B, b t = 0)
    (P A : H →L[ℂ] H) (hInter : logBand(B).comp T = T.comp P)
    (C : nuclearEndomorphisms H) (hC : C.val = A.comp (T.adjoint.comp (M.comp T))) :
    hilbertTrace (Isolated.nuclearCompress P C) = hilbertTrace C := by
  let D := T.adjoint.comp (M.comp T)
  have hMP := reflectedFrequencyMultiplier_comp_logBand M b hM B hB hCap
  have hD : D.comp P = D := by
    ext u : 1
    change T.adjoint (M (T (P u))) = T.adjoint (M (T u))
    have h₁ : logBand(B) (T u) = T (P u) :=
      DFunLike.congr_fun hInter u
    have h₂ : M (logBand(B) (T u)) = M (T u) :=
      DFunLike.congr_fun hMP (T u)
    rw [← h₁, h₂]
  apply hilbertTrace_nuclearCompress_eq_of_right_mul P C
  change C.val.comp P = C.val
  change C.val = A.comp D at hC
  rw [hC, ContinuousLinearMap.comp_assoc, hD]

end RiemannMasullo
