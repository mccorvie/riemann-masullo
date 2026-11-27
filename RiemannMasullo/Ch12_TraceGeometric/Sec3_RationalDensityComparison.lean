module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalWidthLoss
import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalZeroDensity
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A two-sided density bound for the rational principal divisor -/

public noncomputable section
open Set
namespace RiemannMasullo.RationalWidthLoss

/-- The ordinary positive-height zero count transfers, with multiplicity, to the
right side of the genuine rational principal divisor at every fixed positive
distance from the critical line. -/
theorem exists_rightDensity_power {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ HasRightDensity (1/2+δ) (1-δ^2/16) C := by
  obtain ⟨B,hB,h⟩ := ZetaZeroDensity.positiveHeightZetaDensity_power
    (d := δ/2) (by positivity) (by linarith)
  have he : 1/2+2*(δ/2)=1/2+δ := by ring
  have hq : 1-(δ/2)^2/4=1-δ^2/16 := by ring
  rw [he,hq] at h
  have hu : 0 ≤ 1-δ^2/16 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ')]
  apply hasRightDensity_of_positiveHeight hu hB
  intro T hT S hS
  have hlog : 1 ≤ Real.log (2*T) := (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_three])
  exact (h T hT S hS).trans (le_mul_of_one_le_right (mul_nonneg hB (Real.rpow_nonneg (by linarith) _)) (one_le_pow₀ hlog))

end RiemannMasullo.RationalWidthLoss
