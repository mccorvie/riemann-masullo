module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPhysicalHeat
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatMeanZeroHeat
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# The compact dilation action in physical positive-ray coordinates

The genuine inverse cosine transform sends the integrated frequency dilation
to the Haar integral of the reciprocal physical dilations. Both mean-zero band
projections become the orthogonal projection onto the transformed subspace.
-/

open MeasureTheory Set
open scoped CompactlySupported NNReal

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "H₊" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "C₊" => positiveRayInverseCosineEquiv

private theorem physicalDilationRatio_pos (a : ℝ≥0ˣ) : 0 < (a.val : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)

/-- The reciprocal dilations form a Bochner-integrable weighted orbit for every
compactly supported continuous complex test and every positive-ray L² vector. -/
theorem integrable_compactInverseDilation (φ : C_c(ℝ≥0ˣ, ℂ)) (f : H₊) :
    Integrable (fun a : ℝ≥0ˣ ↦ φ a • positiveRayDilation (a.val : ℝ)⁻¹
      (inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero))) f) positiveRealHaar := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hc : Continuous (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)⁻¹) :=
    (NNReal.continuous_coe.comp Units.continuous_val).inv₀ (fun a ↦ (physicalDilationRatio_pos a).ne')
  have hd : Continuous (fun a : ℝ≥0ˣ ↦ positiveRayDilation (a.val : ℝ)⁻¹
      (inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero))) f) :=
    (positiveRayDilation_continuous f).comp (hc.subtype_mk fun a ↦ inv_pos.mpr (physicalDilationRatio_pos a))
  exact (φ.continuous.smul hd).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right

/-- The actual cosine change of chart of the compact dilation action integrates
reciprocal unitary dilations against the original multiplicative Haar test. -/
theorem positiveRayInverseCosine_compactDilationAction (φ : C_c(ℝ≥0ˣ, ℂ)) (f : H₊) :
    C₊ (compactDilationAction φ (C₊.symm f)) =
      ∫ a : ℝ≥0ˣ, φ a • positiveRayDilation (a.val : ℝ)⁻¹
        (inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero))) f ∂positiveRealHaar := by
  change positiveRayInverseCosine (compactDilationAction φ (C₊.symm f)) = _
  rw [compactDilationAction_apply, ← positiveRayInverseCosine.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with a
  rw [map_smul, positiveRayInverseCosine_dilation]
  change φ a • positiveRayDilation (a.val : ℝ)⁻¹ _ (C₊ (C₊.symm f)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- The bounded operator realizing the compact integral of the reciprocal physical dilations. -/
def compactInverseDilationAction (φ : C_c(ℝ≥0ˣ, ℂ)) : H₊ →L[ℂ] H₊ :=
  (C₊ : H₊ →L[ℂ] H₊).comp ((compactDilationAction φ).comp (C₊.symm : H₊ →L[ℂ] H₊))

/-- Application of the bounded physical action to a vector is its Bochner integral. -/
theorem compactInverseDilationAction_apply (φ : C_c(ℝ≥0ˣ, ℂ)) (f : H₊) :
    compactInverseDilationAction φ f =
      ∫ a : ℝ≥0ˣ, φ a • positiveRayDilation (a.val : ℝ)⁻¹
        (inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero))) f ∂positiveRealHaar :=
  positiveRayInverseCosine_compactDilationAction φ f

/-- The orthogonal projection in physical space onto the cosine image of the genuine
mean-zero frequency band. -/
def physicalMeanZeroBandProjection (B : ℝ) : H₊ →L[ℂ] H₊ :=
  ((meanZeroFrequencyBand B).map (C₊.toLinearEquiv : H₊ →ₗ[ℂ] H₊)).starProjection

/-- The transported frequency projection is exactly the physical orthogonal projection. -/
theorem physicalMeanZeroBandProjection_apply (B : ℝ) (f : H₊) :
    physicalMeanZeroBandProjection B f = C₊ ((meanZeroFrequencyBand B).starProjection (C₊.symm f)) :=
  Submodule.starProjection_map_apply C₊ (meanZeroFrequencyBand B) f

/-- In physical space, both projections are the orthogonal mean-zero band projections.
The ordinary spatial cutoff acts after the compact reciprocal dilation action. -/
theorem cosinePhysicalNuclear_meanZeroCompact_val (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    (cosinePhysicalNuclear (meanZeroCompactCosineTraceOperator h L B φ)).val =
      (physicalMeanZeroBandProjection B).comp ((spatialCutoff h L).comp
        ((compactInverseDilationAction φ).comp (physicalMeanZeroBandProjection B))) := by
  rw [cosinePhysicalNuclear_val, meanZeroCompactCosineTraceOperator_val, spatialCutoffInChart_inverseCosine]
  apply ContinuousLinearMap.ext
  intro f
  let P := (meanZeroFrequencyBand B).starProjection
  let S := spatialCutoff h L
  let D := compactDilationAction φ
  change C₊ (P (C₊.symm (S (C₊ (D (P (C₊.symm f))))))) =
    physicalMeanZeroBandProjection B
      (S (C₊ (D (C₊.symm (physicalMeanZeroBandProjection B f)))))
  simp only [physicalMeanZeroBandProjection_apply, LinearIsometryEquiv.symm_apply_apply, P]

/-- The finite operator written on physical vectors entirely in terms of the projected
input, reciprocal dilations, spatial cutoff and projected output. -/
theorem cosinePhysicalNuclear_meanZeroCompact_apply (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) (f : H₊) :
    (cosinePhysicalNuclear (meanZeroCompactCosineTraceOperator h L B φ)).val f =
      physicalMeanZeroBandProjection B (spatialCutoff h L
        (∫ a : ℝ≥0ˣ, φ a • positiveRayDilation (a.val : ℝ)⁻¹
          (inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero))) (physicalMeanZeroBandProjection B f) ∂positiveRealHaar)) := by
  rw [cosinePhysicalNuclear_meanZeroCompact_val]
  simp only [ContinuousLinearMap.comp_apply, compactInverseDilationAction_apply]

/-- The Haar diagonal formed from the position-space cutoff, reciprocal dilation
action and projected input and output integrates to the original frequency-side
heat trace for every positive variance. -/
theorem haarHeatKernel_physicalMeanZeroCompact_diagonal_trace {τ : ℝ≥0} (hτ : 0 < τ)
    (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let Q := physicalMeanZeroBandProjection B
    let T := Q.comp ((spatialCutoff h L).comp ((compactInverseDilationAction φ).comp Q))
    Integrable (fun s ↦ haarHeatKernel τ T s s) ∧
      (∫ s, haarHeatKernel τ T s s) = hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)) := by
  dsimp only
  rw [← cosinePhysicalNuclear_meanZeroCompact_val]
  exact haarHeatKernel_cosinePhysical_diagonal_trace hτ (meanZeroCompactCosineTraceOperator h L B φ)

end RiemannMasullo.FlatPolar
