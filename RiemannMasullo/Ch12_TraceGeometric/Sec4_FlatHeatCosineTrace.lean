module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatBandDilation
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCompactCosineShift
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatDilationTrace

/-!
# The Gaussian average of the real-even cosine trace

At a fixed heat variance each dilation samples its exact common frequency band.
This identifies the Fourier cutoffs in the rational real-even flat calculation of
mrshu on issue #7354.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped CompactlySupported NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "H" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

private theorem frequencyBandProjection_eq_cutoff (B : ℝ) :
    (frequencyBand B).starProjection = spatialCutoff 0 B := by
  ext f : 1
  exact Lp.ext ((frequencyBand_starProjection_ae_eq B f).trans (spatialCutoff_apply 0 B f).symm)

/-- At every real shift the genuine trace of the compressed compact dilation action
followed by log dilation is the exact finite cosine trace on the overlap band. -/
theorem hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator
    (B h L z : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    hilbertTrace (nuclearAfterLogDilation z (compactCosineTraceOperator 0 B h L φ)) =
      hilbertTrace (compactCosineTraceOperator 0 (min B (Real.exp z * B)) h L
        (compactRadialTranslate φ (expRadialUnit z))) := by
  let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
  apply hilbertTrace_frequencyBand_comp_dilation B (Real.exp z) (Real.exp_pos z) T
  · intro f
    rw [compactCosineTraceOperator_frequencyBand_eq, frequencyBandProjection_eq_cutoff]
    rfl
  · intro f
    rw [compactCosineTraceOperator_shift_frequencyBand_eq, frequencyBandProjection_eq_cutoff]
    rfl

/-- At every nonnegative variance, the two-sided heat trace of the finite ambient
band equals the Gaussian average of its literal translated finite cosine traces. -/
theorem hilbertTrace_logHeatSandwich_compactCosineTraceOperator
    (τ : ℝ≥0) (B h L : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    hilbertTrace (logHeatSandwich τ (compactCosineTraceOperator 0 B h L φ)) =
      ∫ z, hilbertTrace (compactCosineTraceOperator 0 (min B (Real.exp z * B)) h L
        (compactRadialTranslate φ (expRadialUnit z))) ∂gaussianReal 0 (τ + τ) := by
  rw [hilbertTrace_logHeatSandwich_eq_integral_dilationTrace]
  exact integral_congr_ae (.of_forall fun z ↦
    hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator B h L z φ)

end RiemannMasullo.FlatPolar
