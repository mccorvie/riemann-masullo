module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHaarHeat
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveRayCosine
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Transport of two-sided logarithmic heat to the physical cosine chart

The positive-ray inverse cosine transform sends a frequency dilation with
logarithmic parameter z to physical dilation with parameter −z. Centered Gaussian
heat consequently commutes with this unitary. The physical log-Haar diagonal
therefore integrates to the frequency-side two-sided heat trace.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "H₊" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "C₊" => positiveRayInverseCosineEquiv

/-- The true inverse cosine transform reverses the real logarithmic dilation parameter. -/
theorem positiveRayInverseCosine_logDilation (z : ℝ) (f : H₊) :
    positiveRayInverseCosine (logDilation z f) =
      logDilation (-z) (positiveRayInverseCosine f) := by
  simpa only [logDilation, Real.exp_neg] using
    positiveRayInverseCosine_dilation (Real.exp z) (Real.exp_pos z) f

/-- Operator equality for conjugation of a frequency dilation into physical space. -/
theorem cosineConjugate_logDilation (z : ℝ) :
    (C₊ : H₊ →L[ℂ] H₊).comp ((logDilation z : H₊ →L[ℂ] H₊).comp (C₊.symm : H₊ →L[ℂ] H₊)) =
      (logDilation (-z) : H₊ →L[ℂ] H₊) := by
  apply ContinuousLinearMap.ext
  intro f
  change C₊ (logDilation z (C₊.symm f)) = logDilation (-z) f
  calc
    _ = logDilation (-z) (C₊ (C₊.symm f)) := positiveRayInverseCosine_logDilation z _
    _ = _ := by rw [LinearIsometryEquiv.apply_symm_apply]

/-- Symmetry of the centered Gaussian makes the true inverse cosine transform
commute with the genuine logarithmic heat at every nonnegative variance. -/
theorem positiveRayInverseCosine_logHeat (τ : ℝ≥0) (f : H₊) :
    positiveRayInverseCosine (logHeat τ f) = logHeat τ (positiveRayInverseCosine f) := by
  let μ := gaussianReal 0 τ
  let C := positiveRayInverseCosine.toContinuousLinearMap
  have hi : Integrable (fun t ↦ logDilation t f) μ :=
    Integrable.of_bound (continuous_logDilation f).aestronglyMeasurable ‖f‖
      (.of_forall fun t ↦ ((logDilation t).norm_map f).le)
  change C (logHeat τ f) = logHeat τ (positiveRayInverseCosine f)
  simp only [logHeat_apply]
  rw [← C.integral_comp_comm hi]
  calc
    _ = ∫ t, logDilation (-t) (positiveRayInverseCosine f) ∂μ :=
      integral_congr_ae (.of_forall fun t ↦ positiveRayInverseCosine_logDilation t f)
    _ = _ := by
      have hμ : μ.map (fun t : ℝ ↦ -t) = μ := by
        simpa [μ] using gaussianReal_map_neg (μ := 0) (v := τ)
      rw [← integral_map measurable_neg.aemeasurable
        (continuous_logDilation (positiveRayInverseCosine f)).aestronglyMeasurable, hμ]

/-- The unitary conjugation of frequency-side logarithmic heat is physical logarithmic heat. -/
theorem cosineConjugate_logHeat (τ : ℝ≥0) :
    (C₊ : H₊ →L[ℂ] H₊).comp ((logHeat τ).comp (C₊.symm : H₊ →L[ℂ] H₊)) = logHeat τ := by
  apply ContinuousLinearMap.ext
  intro f
  change C₊ (logHeat τ (C₊.symm f)) = logHeat τ f
  calc
    _ = logHeat τ (C₊ (C₊.symm f)) := positiveRayInverseCosine_logHeat τ _
    _ = _ := by rw [LinearIsometryEquiv.apply_symm_apply]

private theorem cosineSymm_logHeat (τ : ℝ≥0) (f : H₊) :
    C₊.symm (logHeat τ f) = logHeat τ (C₊.symm f) := by
  apply C₊.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  calc
    logHeat τ f = logHeat τ (C₊ (C₊.symm f)) := by rw [LinearIsometryEquiv.apply_symm_apply]
    _ = C₊ (logHeat τ (C₊.symm f)) := (positiveRayInverseCosine_logHeat τ _).symm

/-- A frequency-side nuclear operator in the physical positive-ray cosine chart. -/
def cosinePhysicalNuclear (A : nuclearEndomorphisms H₊) : nuclearEndomorphisms H₊ :=
  ⟨(C₊ : H₊ →L[ℂ] H₊).comp (A.val.comp (C₊.symm : H₊ →L[ℂ] H₊)),
    isNuclearOperator_conj A.val A.property C₊.toContinuousLinearEquiv.symm⟩

/-- The physical operator is unitary conjugation by the positive-ray inverse cosine transform. -/
theorem cosinePhysicalNuclear_val (A : nuclearEndomorphisms H₊) :
    (cosinePhysicalNuclear A).val =
      (C₊ : H₊ →L[ℂ] H₊).comp (A.val.comp (C₊.symm : H₊ →L[ℂ] H₊)) := rfl

/-- The actual Hilbert trace is invariant under the cosine chart change. -/
theorem hilbertTrace_cosinePhysicalNuclear (A : nuclearEndomorphisms H₊) :
    hilbertTrace (cosinePhysicalNuclear A) = hilbertTrace A := by
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  exact (nuclearTrace_conj hilbert_approximationProperty A.val A.property
    C₊.toContinuousLinearEquiv.symm).symm

/-- Taking two-sided heat of a nuclear operator commutes with conjugating into the
physical cosine chart, as an equality of the full nuclear operators. -/
theorem logHeatSandwich_cosinePhysicalNuclear (τ : ℝ≥0) (A : nuclearEndomorphisms H₊) :
    logHeatSandwich τ (cosinePhysicalNuclear A) = cosinePhysicalNuclear (logHeatSandwich τ A) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  change logHeat τ (C₊ (A.val (C₊.symm (logHeat τ f)))) =
    C₊ (logHeat τ (A.val (logHeat τ (C₊.symm f))))
  rw [cosineSymm_logHeat]
  exact (positiveRayInverseCosine_logHeat τ _).symm

/-- The canonical physical log-Haar diagonal of the conjugated nuclear operator
is integrable and equals the frequency-side heat trace at every positive variance. -/
theorem haarHeatKernel_cosinePhysical_diagonal_trace {τ : ℝ≥0} (hτ : 0 < τ)
    (A : nuclearEndomorphisms H₊) :
    Integrable (fun s ↦ haarHeatKernel τ ((C₊ : H₊ →L[ℂ] H₊).comp
      (A.val.comp (C₊.symm : H₊ →L[ℂ] H₊))) s s) ∧
    (∫ s, haarHeatKernel τ ((C₊ : H₊ →L[ℂ] H₊).comp
      (A.val.comp (C₊.symm : H₊ →L[ℂ] H₊))) s s) = hilbertTrace (logHeatSandwich τ A) := by
  obtain ⟨hi, he⟩ := haarHeatKernel_diagonal_trace hτ (cosinePhysicalNuclear A)
  rw [logHeatSandwich_cosinePhysicalNuclear, hilbertTrace_cosinePhysicalNuclear] at he
  exact ⟨hi, he⟩

end RiemannMasullo.FlatPolar
