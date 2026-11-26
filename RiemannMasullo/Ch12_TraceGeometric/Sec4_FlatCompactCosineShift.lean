module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCompactCosineTrace
public import Mathlib.Topology.Algebra.Field
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Multiplicative shifts of the finite real-even trace

A final normalized dilation translates the compact test in its Haar parameter.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported NNReal Topology

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- The positive unit corresponding to a real translation in logarithmic coordinates. -/
def expRadialUnit (z : ℝ) : ℝ≥0ˣ :=
  (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso z)

@[simp] theorem expRadialUnit_coe (z : ℝ) : ((expRadialUnit z).val : ℝ) = Real.exp z := rfl

@[simp] theorem expRadialUnit_zero : expRadialUnit 0 = 1 := by
  apply Units.ext
  apply NNReal.eq
  exact Real.exp_zero

theorem continuous_expRadialUnit : Continuous expRadialUnit :=
  (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.toHomeomorph.continuous

/-- The radial translate by a positive unit, in coordinates `φ(a / r)`. -/
def compactRadialTranslate (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) : C_c(ℝ≥0ˣ, ℂ) :=
  φ.comp (Homeomorph.divRight r).toCocompactMap

@[simp] theorem compactRadialTranslate_apply (φ : C_c(ℝ≥0ˣ, ℂ)) (r a : ℝ≥0ˣ) :
    compactRadialTranslate φ r a = φ (a / r) := rfl

@[simp] theorem compactRadialTranslate_one (φ : C_c(ℝ≥0ˣ, ℂ)) :
    compactRadialTranslate φ 1 = φ := by
  ext a
  simp

private theorem unitRatio_pos (a : ℝ≥0ˣ) : 0 < (a.val : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)

private theorem positiveUnitDilation_mul (a r : ℝ≥0ˣ) (f : H) :
    positiveRayDilation a.val (unitRatio_pos a) (positiveRayDilation r.val (unitRatio_pos r) f) =
      positiveRayDilation (a * r).val (unitRatio_pos _) f := by
  apply Lp.ext
  filter_upwards [positiveRayDilation_apply a.val (unitRatio_pos a) (positiveRayDilation r.val (unitRatio_pos r) f),
    (positiveRayScale_quasiMeasurePreserving a.val (unitRatio_pos a)).ae_eq_comp
      (positiveRayDilation_apply r.val (unitRatio_pos r) f),
    positiveRayDilation_apply (a * r).val (unitRatio_pos _) f] with x ha hr har
  change positiveRayDilation r.val _ f (a.val * x) = (Real.sqrt r.val : ℂ) * f (r.val * (a.val * x)) at hr
  rw [ha, hr, har]
  change (Real.sqrt a.val : ℂ) * ((Real.sqrt r.val : ℂ) * _) = (Real.sqrt ((a.val : ℝ) * r.val) : ℂ) * _
  rw [Real.sqrt_mul (unitRatio_pos a).le, Complex.ofReal_mul, ← mul_assoc]
  congr 2
  change (r.val : ℝ) * ((a.val : ℝ) * x) = ((a.val : ℝ) * (r.val : ℝ)) * x
  ring

/-- The normalized multiplicative Haar measure absorbs the translation of a compact
test without a density factor. -/
theorem integral_compactRadialTranslate_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) (F : ℝ≥0ˣ → E) :
    (∫ b : ℝ≥0ˣ, compactRadialTranslate φ r b • F b ∂positiveRealHaar) =
      ∫ a : ℝ≥0ˣ, φ a • F (a * r) ∂positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have h := integral_mul_left_eq_self (μ := positiveRealHaar)
    (fun b ↦ compactRadialTranslate φ r b • F b) r
  rw [← h]
  apply integral_congr_ae
  filter_upwards with a
  simp only [compactRadialTranslate_apply, mul_comm r a, mul_div_cancel_right]

/-- The translate realizes a final normalized unitary dilation on the Hilbert space. -/
theorem compactDilationAction_compactRadialTranslate (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) :
    compactDilationAction (compactRadialTranslate φ r) =
      (compactDilationAction φ).comp
        (positiveRayDilation r.val (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr r.ne_zero)) : H →L[ℂ] H) := by
  ext f : 1
  simp only [ContinuousLinearMap.comp_apply, compactDilationAction_apply]
  trans ∫ a : ℝ≥0ˣ, φ a • positiveRayDilation (a * r).val (unitRatio_pos _) f ∂positiveRealHaar
  · exact integral_compactRadialTranslate_smul φ r (fun b ↦ positiveRayDilation b.val (unitRatio_pos b) f)
  apply integral_congr_ae
  filter_upwards with a
  exact congrArg (φ a • ·) (positiveUnitDilation_mul a r f).symm

/-- The finite nuclear representative with translated test realizes the cutoff of
the original compact operator followed on the input side by the dilation. -/
theorem compactCosineTraceOperator_shift_frequencyBand_eq (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) :
    let E := (frequencyBand B).starProjection
    let D := (positiveRayDilation r.val (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr r.ne_zero)) : H →L[ℂ] H)
    (compactCosineTraceOperator 0 B h L (compactRadialTranslate φ r)).val =
      E.comp ((spatialCutoffInChart positiveRayInverseCosine h L).comp (((compactDilationAction φ).comp D).comp E)) := by
  rw [compactCosineTraceOperator_frequencyBand_eq, compactDilationAction_compactRadialTranslate]

/-- Integration against the original test produces atoms at the multiplied dilation `a r`. -/
theorem hilbertTrace_compactCosineTraceOperator_shift (h L j B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) :
    hilbertTrace (compactCosineTraceOperator h L j B (compactRadialTranslate φ r)) =
      ∫ a : ℝ≥0ˣ, φ a * hilbertTrace (finiteCosineTraceOperator h L j B (a * r).val) ∂positiveRealHaar := by
  rw [hilbertTrace_compactCosineTraceOperator]
  exact integral_compactRadialTranslate_smul φ r (fun b ↦ hilbertTrace (finiteCosineTraceOperator h L j B b.val))

/-- Every continuous radial coefficient, averaged against a fixed compact test,
varies continuously under multiplicative translation. -/
theorem continuous_compactRadialShiftIntegral (φ : C_c(ℝ≥0ˣ, ℂ))
    {F : ℝ≥0ˣ → ℂ} (hF : Continuous F) :
    Continuous (fun r : ℝ≥0ˣ ↦ ∫ a : ℝ≥0ˣ, φ a * F (a * r) ∂positiveRealHaar) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := tsupport φ) φ.hasCompactSupport
  · exact ((φ.continuous.comp continuous_snd).mul
      (hF.comp (continuous_snd.mul continuous_fst))).continuousOn
  · intro r a _ ha
    simp [image_eq_zero_of_notMem_tsupport ha]

/-- At fixed cutoffs the translated genuine Hilbert trace is continuous in its shift. -/
theorem continuous_hilbertTrace_compactCosineTraceOperator_shift (h L j B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    Continuous (fun r ↦ hilbertTrace (compactCosineTraceOperator h L j B (compactRadialTranslate φ r))) := by
  simp_rw [hilbertTrace_compactCosineTraceOperator_shift]
  exact continuous_compactRadialShiftIntegral φ (continuous_hilbertTrace_finiteCosineTraceOperator h L j B)

end RiemannMasullo.FlatPolar
