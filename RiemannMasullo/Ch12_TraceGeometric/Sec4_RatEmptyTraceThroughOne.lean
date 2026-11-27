module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RatEmptyActualCompression
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Crossing the real dilation seam with a vanishing test

A linear zero of the physical test at dilation one cancels the singular
band bound. The convergence uses the actual rational quotient compression
with its half-density and Haar factors, without excising a neighborhood of one
and without a principal-value convention. -/

public noncomputable section
open Filter MeasureTheory Set Topology Real
open scoped Interval

namespace RiemannMasullo

variable {a b C : ℝ} {w : ℝ → ℝ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

/-- The zero of the weight cancels the singular summand in the uniform band bound. -/
private theorem throughOne_band_bound {g R : ℝ} (hg : 0 < g) (hne : g ≠ 1)
    (hC : 0 ≤ C) (hw : |w g| ≤ C * |g - 1|) :
    |w g| * |realPWBandDiagonalMass R g| ≤
      (C * g / π + C * |g - 1| / π) * (π / 2 + 2) := by
  have hm : |1 / g - 1| = |g - 1| / g := by
    rw [show 1 / g - 1 = (1 - g) / g by field_simp, abs_div, abs_of_pos hg, abs_sub_comm (1 : ℝ)]
  have hp : 1 ≤ 1 / g + 1 := by linarith [one_div_pos.mpr hg]
  have hp' : (π * |1 / g + 1|)⁻¹ ≤ π⁻¹ := by
    rw [abs_of_pos (lt_of_lt_of_le zero_lt_one hp)]
    apply inv_anti₀ pi_pos
    nlinarith [mul_le_mul_of_nonneg_left hp pi_pos.le]
  calc
    _ ≤ (C * |g - 1|) * (((π * |1 / g - 1|)⁻¹ + (π * |1 / g + 1|)⁻¹) * (π / 2 + 2)) :=
      mul_le_mul hw (abs_realPWBandDiagonalMass_le _ _) (abs_nonneg _) (by positivity)
    _ = ((C * |g - 1|) * (π * |1 / g - 1|)⁻¹ + (C * |g - 1|) * (π * |1 / g + 1|)⁻¹) * (π / 2 + 2) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply add_le_add
      · rw [hm]
        exact le_of_eq (by field_simp [abs_ne_zero.mpr (sub_ne_zero.mpr hne), hg.ne', pi_ne_zero])
      · simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp' (show 0 ≤ C * |g - 1| by positivity)

/-- Weighted band-minus-polar mass, with no separation of the interval from one. -/
theorem tendsto_integral_realPWLevelDiagonalMass_throughOne {R : ι → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hC : 0 ≤ C) (hcancel : ∀ g ∈ Icc a b, |w g| ≤ C * |g - 1|)
    (hR : Tendsto R l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * (realPWBandDiagonalMass (R i) g - realPWPolarDiagonalMass (R i) g)) l
      (𝓝 (∫ g in a..b, w g * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g))) := by
  let B := fun g : ℝ ↦ (C * g / π + C * |g - 1| / π) * (π / 2 + 2)
  let P := fun g : ℝ ↦ |g| / π * ((|1 / g + 1| + |1 / g - 1|) * (π / 2 + 2) + 2)
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hP : ContinuousOn P (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hi : ContinuousOn (fun g : ℝ ↦ 1 / g) (Icc a b) :=
      continuousOn_const.div continuousOn_id fun g hg ↦ (ha.trans_le hg.1).ne'
    exact (continuous_abs.continuousOn.div_const π).mul
      ((((hi.add continuousOn_const).abs.add (hi.sub continuousOn_const).abs).mul continuousOn_const).add continuousOn_const)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun g ↦ B g + |w g| * P g) ?_ ?_ ((hB.intervalIntegrable a b).add (hw.abs.mul_continuousOn hP)) ?_
  · exact Eventually.of_forall fun i ↦ hw.def'.aestronglyMeasurable.mul
      ((measurable_realPWBandDiagonalMass _).sub (measurable_realPWPolarDiagonalMass _)).aestronglyMeasurable
  · refine Eventually.of_forall fun i ↦ ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with g hne
    intro hg
    rw [uIoc_of_le hab] at hg
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |w g| * (|realPWBandDiagonalMass (R i) g| + |realPWPolarDiagonalMass (R i) g|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (throughOne_band_bound (ha.trans hg.1) hne hC (hcancel g (Ioc_subset_Icc_self hg)))
          (mul_le_mul_of_nonneg_left (abs_realPWPolarDiagonalMass_le _ _) (abs_nonneg _))
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with g hne
    intro hg
    rw [uIoc_of_le hab] at hg
    exact ((tendsto_realPWBandDiagonalMass hR (ha.trans hg.1) hne).sub
      (tendsto_realPWPolarDiagonalMass hR (ha.trans hg.1))).const_mul (w g)

/-- With the half-density and multiplicative Haar factors restored, this is the
average of flat level-compression traces. Only a linear zero of the test is used. -/
theorem tendsto_integral_realPWLevelCompressionTrace_throughOne {Y L : ι → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) (hC : 0 ≤ C)
    (hcancel : ∀ g ∈ Icc a b, |w g| ≤ C * |g - 1|)
    (hY : ∀ i, 0 < Y i) (hL : ∀ i, 0 ≤ L i) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, (w g : ℂ) * realPWLevelCompressionTrace (Y i) (L i) g / (g : ℂ)) l
      (𝓝 ((∫ g in a..b, w g * (√g * g)⁻¹ *
        ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g) : ℝ) : ℂ)) := by
  let v := fun g : ℝ ↦ w g * (√g * g)⁻¹
  have hv : ContinuousOn v (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hw.mul ((Real.continuous_sqrt.continuousOn.mul continuousOn_id).inv₀ fun g hg ↦
      mul_ne_zero (Real.sqrt_pos.mpr (ha.trans_le hg.1)).ne' (ha.trans_le hg.1).ne')
  have hvc : ∀ g ∈ Icc a b, |v g| ≤ (C * (√a * a)⁻¹) * |g - 1| := by
    intro g hg
    have hg0 := ha.trans_le hg.1
    have hmono : √a * a ≤ √g * g :=
      mul_le_mul (Real.sqrt_le_sqrt hg.1) hg.1 ha.le (Real.sqrt_nonneg _)
    dsimp [v]
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr hg0) hg0)), mul_right_comm C]
    exact mul_le_mul (hcancel g hg) (inv_anti₀ (mul_pos (Real.sqrt_pos.mpr ha) ha) hmono)
      (by positivity) (by positivity)
  have h := tendsto_integral_realPWLevelDiagonalMass_throughOne ha hab hv.intervalIntegrable
    (show 0 ≤ C * (√a * a)⁻¹ by positivity) hvc hYL
  refine ((Complex.continuous_ofReal.tendsto _).comp h).congr' ?_
  filter_upwards [hYL.eventually_gt_atTop 0] with i hi
  simp only [Function.comp_apply]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with g hne hg
  rw [uIoc_of_le hab] at hg
  have hg0 := ha.trans hg.1
  rw [realPWLevelCompressionTrace_eq (hY i) hg0 (hL i),
    integral_realPWLevelDiagonal hg0 hne (hY i).ne' (right_ne_zero_of_mul hi.ne')]
  dsimp [v]
  push_cast
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

end RiemannMasullo

namespace RiemannMasullo.RatEmptyRealLevelBridge

open NumberField IsDedekindDomain
open scoped NNReal NumberField.AdeleRing

local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "Ω" => PontryaginDual (MonoidHom.ker N)

private def positiveRadius (g : ℝ) (hg : 0 < g) : ℝ≥0ˣ :=
  Units.mk0 g.toNNReal (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt hg))

/-- Trace of the actual quotient dilation compression, as a function of its
physical radius. Outside positive radii the function is extended by zero. -/
def actualCompressionTrace (ω : Ω) {B L : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (g : ℝ) : ℂ :=
  if hg : 0 < g then
    let a := positiveRadius g hg
    let h := actualCompression_hilbertTrace ω hB hL a
    hilbertTrace ⟨actualCompression ω B L a, h.choose⟩
  else 0

/-- For each positive radius, the actual Hilbert trace equals the flat
Hilbert trace, including at the central dilation. -/
theorem actualCompressionTrace_eq_flat (ω : Ω) {B L g : ℝ} (hB : 0 < B)
    (hL : 0 ≤ L) (hg : 0 < g) :
    actualCompressionTrace ω hB hL g = realPWLevelCompressionTrace B L g := by
  rw [actualCompressionTrace, dite_eq_left hg, realPWLevelCompressionTrace_eq hB hg hL]
  have h := (actualCompression_hilbertTrace ω hB hL (positiveRadius g hg)).choose_spec
  simpa only [positiveRadius, Units.val_mk0, Real.coe_toNNReal g hg.le] using h

/-- Crossing the dilation seam for the true rational quotient compression.
The weight is allowed on both sides of one and must vanish there to linear order. -/
theorem tendsto_integral_actualCompressionTrace_throughOne
    {a b C : ℝ} {w : ℝ → ℝ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {B L : ι → ℝ} (ω : Ω)
    (ha : 0 < a) (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) (hC : 0 ≤ C)
    (hcancel : ∀ g ∈ Icc a b, |w g| ≤ C * |g - 1|)
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 ≤ L i) (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, (w g : ℂ) * actualCompressionTrace ω (hB i) (hL i) g / (g : ℂ)) l
      (𝓝 ((∫ g in a..b, w g * (√g * g)⁻¹ *
        ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g) : ℝ) : ℂ)) := by
  refine (tendsto_integral_realPWLevelCompressionTrace_throughOne ha hab hw hC hcancel hB hL hBL
    ).congr' (Eventually.of_forall fun i ↦ ?_)
  apply intervalIntegral.integral_congr
  intro g hg
  rw [uIcc_of_le hab] at hg
  dsimp only
  rw [actualCompressionTrace_eq_flat ω (hB i) (hL i) (ha.trans_le hg.1)]

end RiemannMasullo.RatEmptyRealLevelBridge
