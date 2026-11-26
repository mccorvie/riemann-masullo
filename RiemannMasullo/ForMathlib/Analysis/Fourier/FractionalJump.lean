module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.HeatKernel
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Bernstein
import Mathlib.MeasureTheory.Integral.Prod

/-! # The positive jump measure of a fractional Bessel operator

For `0 ≤ θ < 1`, subordination of the heat kernel produces a positive jump measure with
Fourier symbol `(1 + ξ²)^θ - 1` and second moment exactly `2θ`. We construct the measure
as a marginal of a positive heat mixture, so its singularity at the origin is handled
by measure theory rather than by assigning a value to a divergent pointwise density.

These are the measure and integrability inputs for the fractional Sobolev geometric-block
argument in #7406. The scalar subordination formula is proved in `Pow.Bernstein`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Real
namespace RiemannMasullo

/-- The positive heat-mixture density for the jump part of `(1 - Δ)^θ`. -/
def fractionalHeatDensity (θ u x : ℝ) : ℝ :=
  (θ / Real.Gamma (1 - θ) * Real.exp (-u) * u ^ (-1 - θ)) * realHeatKernel u x

/-- The heat-mixture measure, retaining the time variable. -/
def fractionalHeatMeasure (θ : ℝ) : Measure (ℝ × ℝ) :=
  ((volume.restrict (Ioi 0)).prod volume).withDensity
    (fun p ↦ ENNReal.ofReal (fractionalHeatDensity θ p.1 p.2))

instance (θ : ℝ) : SigmaFinite (fractionalHeatMeasure θ) := by
  unfold fractionalHeatMeasure
  infer_instance

/-- The jump measure of the one-dimensional fractional Bessel operator. -/
def fractionalJumpMeasure (θ : ℝ) : Measure ℝ :=
  (fractionalHeatMeasure θ).map Prod.snd

instance (θ : ℝ) : SFinite (fractionalJumpMeasure θ) := by
  unfold fractionalJumpMeasure
  infer_instance

/-- The heat-mixture density is jointly measurable. -/
@[fun_prop]
theorem measurable_fractionalHeatDensity (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ fractionalHeatDensity θ p.1 p.2) := by
  unfold fractionalHeatDensity
  fun_prop

/-- The heat-mixture density is nonnegative throughout the fractional range. -/
theorem fractionalHeatDensity_nonneg {θ u : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hu : 0 ≤ u) (x : ℝ) : 0 ≤ fractionalHeatDensity θ u x := by
  unfold fractionalHeatDensity
  have hG := (Real.Gamma_pos_of_pos (show 0 < 1 - θ by linarith)).le
  exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hθ₀ hG) (Real.exp_pos _).le)
    (Real.rpow_nonneg hu _)) (realHeatKernel_nonneg _ _)

private theorem fractionalHeat_time_sq {θ u : ℝ} (hu : 0 < u) :
    (θ / Real.Gamma (1 - θ) * Real.exp (-u) * u ^ (-1 - θ)) * (2 * u) =
      (2 * θ / Real.Gamma (1 - θ)) * (Real.exp (-u) * u ^ (-θ)) := by
  have hp : u ^ (-1 - θ) * u = u ^ (-θ) := by
    rw [← Real.rpow_add_one hu.ne']
    congr 1
    ring
  calc
    _ = (2 * θ / Real.Gamma (1 - θ)) * (Real.exp (-u) * (u ^ (-1 - θ) * u)) := by ring
    _ = _ := by rw [hp]

private theorem fractionalHeat_outer_sq_integrable {θ : ℝ} (hθ : θ < 1) :
    IntegrableOn (fun u : ℝ ↦ (2 * θ / Real.Gamma (1 - θ)) *
      (Real.exp (-u) * u ^ (-θ))) (Ioi 0) := by
  have hi := (Real.GammaIntegral_convergent (show 0 < 1 - θ by linarith)).const_mul
    (2 * θ / Real.Gamma (1 - θ))
  simpa only [IntegrableOn, sub_sub_cancel_left] using hi

private theorem integrable_fractionalHeatDensity_mul_sq {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    Integrable (fun p : ℝ × ℝ ↦ fractionalHeatDensity θ p.1 p.2 * p.2 ^ 2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [fractionalHeatDensity, mul_assoc] using
      (integrable_realHeatKernel_mul_sq hu).const_mul
        (θ / Real.Gamma (1 - θ) * Real.exp (-u) * u ^ (-1 - θ))
  · apply (fractionalHeat_outer_sq_integrable hθ₁).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have he (x : ℝ) : ‖fractionalHeatDensity θ u x * x ^ 2‖ =
        (θ / Real.Gamma (1 - θ) * Real.exp (-u) * u ^ (-1 - θ)) *
          (realHeatKernel u x * x ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (fractionalHeatDensity_nonneg hθ₀ hθ₁ hu.le x) (sq_nonneg _))]
      simp only [fractionalHeatDensity, mul_assoc]
    simp_rw [he]
    rw [integral_const_mul, integral_realHeatKernel_mul_sq hu]
    exact (fractionalHeat_time_sq hu).symm

private theorem fractionalHeatMeasure_integrable_iff {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (f : ℝ × ℝ → ℝ) :
    Integrable f (fractionalHeatMeasure θ) ↔
      Integrable (fun p ↦ fractionalHeatDensity θ p.1 p.2 * f p)
        ((volume.restrict (Ioi 0)).prod volume) := by
  unfold fractionalHeatMeasure
  rw [integrable_withDensity_iff (measurable_fractionalHeatDensity θ).ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integrable_congr
  have hu : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod volume), 0 < p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hu] with p hp
  rw [ENNReal.toReal_ofReal (fractionalHeatDensity_nonneg hθ₀ hθ₁ hp.le _), mul_comm]

private theorem integral_fractionalHeatMeasure {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂fractionalHeatMeasure θ) =
      ∫ p : ℝ × ℝ, fractionalHeatDensity θ p.1 p.2 * f p
        ∂((volume.restrict (Ioi 0)).prod volume) := by
  unfold fractionalHeatMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_fractionalHeatDensity θ).ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  have hu : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod volume), 0 < p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hu] with p hp
  rw [ENNReal.toReal_ofReal (fractionalHeatDensity_nonneg hθ₀ hθ₁ hp.le _), smul_eq_mul]

/-- The fractional jump measure has finite second moment. -/
theorem integrable_sq_fractionalJumpMeasure {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    Integrable (fun x : ℝ ↦ x ^ 2) (fractionalJumpMeasure θ) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact (fractionalHeatMeasure_integrable_iff hθ₀ hθ₁ _).mpr
    (integrable_fractionalHeatDensity_mul_sq hθ₀ hθ₁)

/-- The exact second moment is `2θ`. -/
theorem integral_sq_fractionalJumpMeasure {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    (∫ x : ℝ, x ^ 2 ∂fractionalJumpMeasure θ) = 2 * θ := by
  unfold fractionalJumpMeasure
  rw [integral_map (by fun_prop) (by fun_prop), integral_fractionalHeatMeasure hθ₀ hθ₁,
    integral_prod _ (integrable_fractionalHeatDensity_mul_sq hθ₀ hθ₁)]
  have he (u : ℝ) (hu : u ∈ Ioi 0) :
      (∫ x : ℝ, fractionalHeatDensity θ u x * x ^ 2) =
        (2 * θ / Real.Gamma (1 - θ)) * (Real.exp (-u) * u ^ (-θ)) := by
    simp only [fractionalHeatDensity, mul_assoc, integral_const_mul,
      integral_realHeatKernel_mul_sq hu]
    simpa only [mul_assoc] using fractionalHeat_time_sq hu
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul]
  have hG := Real.Gamma_eq_integral (show 0 < 1 - θ by linarith)
  simp only [sub_sub_cancel_left] at hG
  rw [← hG]
  have hn := (Real.Gamma_pos_of_pos (show 0 < 1 - θ by linarith)).ne'
  field_simp


private theorem integrable_fractionalHeatDensity_mul_one_sub_cos {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ fractionalHeatDensity θ p.1 p.2 *
      (1 - Real.cos (ξ * p.2))) ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · exact .of_forall fun u ↦ by
      simpa only [fractionalHeatDensity, mul_assoc] using
        (integrable_realHeatKernel_mul_one_sub_cos u ξ).const_mul
          (θ / Real.Gamma (1 - θ) * Real.exp (-u) * u ^ (-1 - θ))
  · apply ((integrableOn_fractionalPowerKernel hθ₁ (sq_nonneg ξ)).const_mul
      (θ / Real.Gamma (1 - θ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have he (x : ℝ) : ‖fractionalHeatDensity θ u x * (1 - Real.cos (ξ * x))‖ =
        (θ / Real.Gamma (1 - θ) * Real.exp (-u) * u ^ (-1 - θ)) *
          (realHeatKernel u x * (1 - Real.cos (ξ * x))) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (fractionalHeatDensity_nonneg hθ₀ hθ₁ hu.le _) (sub_nonneg.mpr (Real.cos_le_one _))) ]
      simp only [fractionalHeatDensity, mul_assoc]
    simp_rw [he]
    rw [integral_const_mul, integral_realHeatKernel_mul_one_sub_cos hu]
    ring_nf

/-- The compensated cosine is integrable against the singular jump measure. -/
theorem integrable_one_sub_cos_fractionalJumpMeasure {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (ξ : ℝ) :
    Integrable (fun x : ℝ ↦ 1 - Real.cos (ξ * x)) (fractionalJumpMeasure θ) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact (fractionalHeatMeasure_integrable_iff hθ₀ hθ₁ _).mpr
    (integrable_fractionalHeatDensity_mul_one_sub_cos hθ₀ hθ₁ ξ)

/-- The jump measure has exactly the fractional Bessel Fourier symbol. -/
theorem integral_one_sub_cos_fractionalJumpMeasure {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (ξ : ℝ) :
    (∫ x : ℝ, (1 - Real.cos (ξ * x)) ∂fractionalJumpMeasure θ) =
      (1 + ξ ^ 2) ^ θ - 1 := by
  unfold fractionalJumpMeasure
  rw [integral_map (by fun_prop) (by fun_prop), integral_fractionalHeatMeasure hθ₀ hθ₁,
    integral_prod _ (integrable_fractionalHeatDensity_mul_one_sub_cos hθ₀ hθ₁ ξ)]
  have he (u : ℝ) (hu : u ∈ Ioi 0) :
      (∫ x : ℝ, fractionalHeatDensity θ u x * (1 - Real.cos (ξ * x))) =
        θ / Real.Gamma (1 - θ) *
          (Real.exp (-u) * (1 - Real.exp (-(ξ ^ 2 * u))) * u ^ (-1 - θ)) := by
    simp only [fractionalHeatDensity, mul_assoc, integral_const_mul,
      integral_realHeatKernel_mul_one_sub_cos hu]
    rw [mul_comm u (ξ ^ 2)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    fractionalPower_eq_integral hθ₁ (sq_nonneg ξ)]

end RiemannMasullo
