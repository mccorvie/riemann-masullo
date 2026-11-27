module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian averaging with an expanding amplitude bound

A shrinking log-Gaussian averages a locally convergent family even when its
global envelope grows with an independent spatial window.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace RiemannMasullo

private theorem gaussianWindow_integral_exp (v : ℝ≥0) (b : ℝ) :
    (∫ z : ℝ, Real.exp (b * z) ∂gaussianReal 0 v) =
      Real.exp ((v : ℝ) * b ^ 2 / 2) := by
  simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) b

private theorem gaussianWindow_measurable (d : ℝ) :
    MeasurableSet {z : ℝ | d ≤ |z|} := measurableSet_le measurable_const continuous_abs.measurable

/-- A Gaussian tail with a fixed exponential weight. The constant is uniform for all variances
in (0,1]. Taking b = -1/2 gives the weight in the log-dilation trace. -/
theorem gaussianWindow_tail_bound (v : ℝ≥0) (hv : 0 < (v : ℝ)) (hv₁ : (v : ℝ) ≤ 1)
    (b d : ℝ) (hd : 0 < d) :
    (∫ z in {z : ℝ | d ≤ |z|}, Real.exp (b * z) ∂gaussianReal 0 v) ≤
      2 * Real.exp (b ^ 2) * Real.exp (-(d ^ 2) / (4 * (v : ℝ))) := by
  let a : ℝ := d / (2 * (v : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let g (z : ℝ) := Real.exp (-a * d) *
      (Real.exp ((b + a) * z) + Real.exp ((b - a) * z))
  have hg : Integrable g (gaussianReal 0 v) :=
    ((integrable_exp_mul_gaussianReal (b + a)).add
      (integrable_exp_mul_gaussianReal (b - a))).const_mul _
  have hg₀ : ∀ z, 0 ≤ g z := fun z ↦ by dsimp [g]; positivity
  have hdom : ∀ z ∈ {z : ℝ | d ≤ |z|}, Real.exp (b * z) ≤ g z := by
    intro z hz
    change d ≤ |z| at hz
    rcases (le_abs.mp hz) with h | h
    · calc
        Real.exp (b * z) ≤ Real.exp (-a * d + (b + a) * z) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]
        _ = Real.exp (-a * d) * Real.exp ((b + a) * z) := Real.exp_add _ _
        _ ≤ g z := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_nonneg _)) (Real.exp_nonneg _)
    · calc
        Real.exp (b * z) ≤ Real.exp (-a * d + (b - a) * z) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg ha (show 0 ≤ -z - d by linarith)]
        _ = Real.exp (-a * d) * Real.exp ((b - a) * z) := Real.exp_add _ _
        _ ≤ g z := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hquad (c : ℝ) (hc : c ^ 2 ≤ 2 * b ^ 2 + 2 * a ^ 2) :
      Real.exp (-a * d) * Real.exp ((v : ℝ) * c ^ 2 / 2) ≤
        Real.exp (b ^ 2) * Real.exp (-(d ^ 2) / (4 * (v : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hsq : -a * d + (v : ℝ) * a ^ 2 = -(d ^ 2) / (4 * (v : ℝ)) := by
      dsimp [a]
      field_simp
      ring
    have hb := mul_le_mul_of_nonneg_right hv₁ (sq_nonneg b)
    nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hc)]
  calc
    (∫ z in {z : ℝ | d ≤ |z|}, Real.exp (b * z) ∂gaussianReal 0 v) ≤
        ∫ z in {z : ℝ | d ≤ |z|}, g z ∂gaussianReal 0 v :=
      setIntegral_mono_on (integrable_exp_mul_gaussianReal b).integrableOn hg.integrableOn
        (gaussianWindow_measurable d) hdom
    _ ≤ ∫ z, g z ∂gaussianReal 0 v := setIntegral_le_integral hg (ae_of_all _ hg₀)
    _ = Real.exp (-a * d) *
        (Real.exp ((v : ℝ) * (b + a) ^ 2 / 2) + Real.exp ((v : ℝ) * (b - a) ^ 2 / 2)) := by
          dsimp only [g]
          rw [integral_const_mul, integral_add (integrable_exp_mul_gaussianReal _)
            (integrable_exp_mul_gaussianReal _), gaussianWindow_integral_exp, gaussianWindow_integral_exp]
    _ ≤ 2 * Real.exp (b ^ 2) * Real.exp (-(d ^ 2) / (4 * (v : ℝ))) := by
      rw [mul_add]
      linarith [hquad (b + a) (by nlinarith [sq_nonneg (b - a)]),
        hquad (b - a) (by nlinarith [sq_nonneg (b + a)])]

/-- The logarithmic heat measure at variance zero has no mass outside a positive window. -/
theorem gaussianWindow_tail_zero (b d : ℝ) (hd : 0 < d) :
    (∫ z in {z : ℝ | d ≤ |z|}, Real.exp (b * z) ∂gaussianReal 0 0) = 0 := by
  classical
  rw [gaussianReal_zero_var, setIntegral_dirac]
  simp [not_le.mpr hd]

/-- A growing cutoff times the exponentially weighted contribution from outside every fixed window
vanishes when the variance times its logarithm tends to zero. Zero variances are allowed. -/
theorem gaussianWindow_scaled_tail_tendsto {ι : Type*} {l : Filter ι} (R : ι → ℝ) (v : ι → ℝ≥0)
    (hR : Tendsto R l atTop) (hv : Tendsto (fun i ↦ (v i : ℝ)) l (𝓝 0))
    (hwindow : Tendsto (fun i ↦ (v i : ℝ) * Real.log (R i)) l (𝓝 0))
    (b d : ℝ) (hd : 0 < d) :
    Tendsto (fun i ↦ R i * ∫ z in {z : ℝ | d ≤ |z|}, Real.exp (b * z) ∂gaussianReal 0 (v i))
      l (𝓝 0) := by
  let C := 2 * Real.exp (b ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun i ↦ C * (R i)⁻¹) l (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using (tendsto_inv_atTop_zero.comp hR).const_mul C
  have hRpos := hR.eventually_gt_atTop 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [hRpos] with i hi
    exact mul_nonneg hi.le (integral_nonneg fun _ ↦ Real.exp_nonneg _)
  · filter_upwards [hRpos, hv.eventually_lt_const zero_lt_one,
      hwindow.eventually_lt_const (show (0 : ℝ) < d ^ 2 / 8 by positivity)] with i hi hvi hiw
    by_cases hzero : v i = 0
    · rw [hzero, gaussianWindow_tail_zero b d hd, mul_zero]
      exact mul_nonneg hC (inv_nonneg.mpr hi.le)
    · have ht : 0 < (v i : ℝ) := (NNReal.coe_pos).2 (pos_iff_ne_zero.mpr hzero)
      have he : -(d ^ 2) / (4 * (v i : ℝ)) ≤ -(Real.log (R i) + Real.log (R i)) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (v i : ℝ))).2
        linarith only [hiw]
      calc
        _ ≤ R i * (C * Real.exp (-(d ^ 2) / (4 * (v i : ℝ)))) :=
          mul_le_mul_of_nonneg_left (gaussianWindow_tail_bound (v i) ht hvi.le b d hd) hi.le
        _ ≤ R i * (C * Real.exp (-(Real.log (R i) + Real.log (R i)))) := by
          gcongr
        _ = C * (R i)⁻¹ := by
          rw [Real.exp_neg, Real.exp_add, Real.exp_log hi]
          field_simp

private theorem gaussianWindow_average_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (v : ℝ≥0) (R C b d ε : ℝ) (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (F : ℝ → E) (u : E) (hFm : AEStronglyMeasurable F (gaussianReal 0 v))
    (hglob : ∀ᵐ z ∂gaussianReal 0 v, ‖F z‖ ≤ C * R * Real.exp (b * z))
    (hloc : ∀ z, |z| < d → ‖F z - u‖ ≤ ε) :
    ‖(∫ z, F z ∂gaussianReal 0 v) - u‖ ≤
      ε + C * (R * ∫ z in {z : ℝ | d ≤ |z|}, Real.exp (b * z) ∂gaussianReal 0 v) +
        ‖u‖ * (R * ∫ z in {z : ℝ | d ≤ |z|}, Real.exp (0 * z) ∂gaussianReal 0 v) := by
  classical
  let s := {z : ℝ | d ≤ |z|}
  have hs : MeasurableSet s := gaussianWindow_measurable d
  let tail (c z : ℝ) := s.indicator (fun x ↦ Real.exp (c * x)) z
  have hit (c : ℝ) : Integrable (tail c) (gaussianReal 0 v) :=
    (integrable_exp_mul_gaussianReal c).indicator hs
  have het (c : ℝ) : (∫ z, tail c z ∂gaussianReal 0 v) =
      ∫ z in s, Real.exp (c * z) ∂gaussianReal 0 v := integral_indicator hs
  have hF : Integrable F (gaussianReal 0 v) :=
    ((integrable_exp_mul_gaussianReal b).const_mul (C * R)).mono' hFm hglob
  have ha := (hit b).const_mul (C * R)
  have hb := (hit 0).const_mul (‖u‖ * R)
  have hc : Integrable (fun _ : ℝ ↦ ε) (gaussianReal 0 v) := integrable_const _
  have hsum : Integrable (fun z ↦ ε + C * R * tail b z) (gaussianReal 0 v) := hc.add ha
  have huR : ‖u‖ ≤ ‖u‖ * R := le_mul_of_one_le_right (norm_nonneg _) hR
  calc
    ‖(∫ z, F z ∂gaussianReal 0 v) - u‖ =
        ‖∫ z, F z - u ∂gaussianReal 0 v‖ := by rw [integral_sub hF (integrable_const u)]; simp
    _ ≤ ∫ z, (ε + (C * R) * tail b z) + (‖u‖ * R) * tail 0 z ∂gaussianReal 0 v := by
      apply norm_integral_le_of_norm_le (hsum.add hb)
      filter_upwards [hglob] with z hz
      change ‖F z - u‖ ≤ ε + C * R * tail b z + ‖u‖ * R * tail 0 z
      by_cases hz' : z ∈ s
      · simp only [tail, indicator_of_mem hz', zero_mul, Real.exp_zero, mul_one]
        linarith [norm_sub_le (F z) u]
      · have hzd : |z| < d := lt_of_not_ge hz'
        simpa only [tail, indicator_of_notMem hz', mul_zero, add_zero] using hloc z hzd
    _ = _ := by
      rw [integral_add hsum hb, integral_add hc ha, integral_const_mul,
        integral_const_mul, het b, het 0]
      simp only [integral_const, probReal_univ, one_smul]
      ring

/-- Gaussian averages recover a value u under joint local convergence at zero and an a.e.
exponential bound. This works for real and complex functions, and Banach-valued functions. -/
theorem gaussianWindow_average_tendsto {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {l : Filter ι} (R : ι → ℝ) (v : ι → ℝ≥0)
    (hR : Tendsto R l atTop) (hv : Tendsto (fun i ↦ (v i : ℝ)) l (𝓝 0))
    (hwindow : Tendsto (fun i ↦ (v i : ℝ) * Real.log (R i)) l (𝓝 0))
    (F : ι → ℝ → E) (u : E) (C b : ℝ)
    (hFm : ∀ᶠ i in l, AEStronglyMeasurable (F i) (gaussianReal 0 (v i)))
    (hglob : ∀ᶠ i in l, ∀ᵐ z ∂gaussianReal 0 (v i), ‖F i z‖ ≤ C * R i * Real.exp (b * z))
    (hloc : ∀ ε > 0, ∃ d > 0, ∀ᶠ i in l, ∀ z, |z| < d → ‖F i z - u‖ ≤ ε) :
    Tendsto (fun i ↦ ∫ z, F i z ∂gaussianReal 0 (v i)) l (𝓝 u) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨d, hd, hlocal⟩ := hloc (ε / 2) (half_pos hε)
  have hscale (c : ℝ) := gaussianWindow_scaled_tail_tendsto R v hR hv hwindow c d hd
  have hsmall := ((hscale b).const_mul C).add ((hscale 0).const_mul ‖u‖)
  simp only [mul_zero, add_zero] at hsmall
  filter_upwards [hR.eventually_ge_atTop 1, hFm, hglob, hlocal,
    hsmall.eventually_lt_const (half_pos hε)] with i hi hmi hgi hli hsi
  rw [dist_eq_norm]
  have he := gaussianWindow_average_error (v i) (R i) C b d (ε / 2) hi (half_pos hε).le
    (F i) u hmi hgi hli
  change _ + _ < ε / 2 at hsi
  linarith

end RiemannMasullo
