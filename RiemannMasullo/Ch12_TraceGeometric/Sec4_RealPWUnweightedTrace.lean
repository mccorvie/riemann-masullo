module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The real-place trace through `g = 1`, without weight

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, in the fixed-bandwidth model of the real
place of `ℚ` of #7354, without weight. This is the setting of A. Connes, *Trace formula in
noncommutative geometry and the zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31,
for `k = ℚ` and `S = {∞}`.

The earlier files ask the test function to vanish near `g = 1`. Here it has only to vanish at
`g = 1`, at a linear rate. That is the class of test functions of Theorem 12.5.1.1, p. 519.

* `realPWSharpTrace_zero_zero_eq_sinc`. With the closed-form kernel of
  `Sec4_RealPWUnweightedKernel`, the sharp trace of the dilation by `g⁻¹` is an explicit
  integral of `sinc`.
* `abs_integral_sinc_le`. The integral of `sinc` over `[0, T]` is bounded uniformly in `T`.
* `norm_realPWSharpTrace_zero_zero_le`. So the sharp trace is bounded by a multiple of
  `g ^ (1/2) (1 / |g - 1| + 1)`, uniformly in the cutoff.
* `exists_realPWTestCutoff_trace_limit_through_one`. The traces on the whole band converge to
  the integral of the test function against the real-term density
  `(1/2) (1 / |g - 1| + 1 / (g + 1)) g ^ (1/2)`, on both sides of `g = 1` at once.
* `exists_realPWTestCutoff_level_trace_limit_through_one`. On the level of band vectors
  vanishing at the origin the limit is that minus the integral of the test function against
  `min (g ^ (1/2), g ^ (-1/2))`.

* `realPWSharpTrace_zero_zero_scale`. The sharp trace depends on the bandwidth `Y` and the
  cutoff `L` only through the product `Y L`. So the limits above are limits as `Y L → ∞`, which
  includes Connes's regime `Y = L → ∞`.

Not treated here: test functions with `ψ 1 ≠ 0`, for which the trace grows like the logarithm
of the cutoff. A weight.

Reconstruction: The paper does not state this. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

/-- The integral of `sin t / t` over `[1, T]` is bounded by `3`. -/
theorem abs_integral_sin_div_le {T : ℝ} (hT : 1 ≤ T) :
    |∫ t in (1 : ℝ)..T, Real.sin t / t| ≤ 3 := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hpos : ∀ x ∈ uIcc (1 : ℝ) T, 0 < x := fun x hx ↦ by
    rw [uIcc_of_le hT] at hx
    exact zero_lt_one.trans_le hx.1
  have hu : ∀ x ∈ uIcc (1 : ℝ) T, HasDerivAt (fun y : ℝ ↦ y⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx ↦ hasDerivAt_inv (hpos x hx).ne'
  have hv : ∀ x ∈ uIcc (1 : ℝ) T, HasDerivAt (fun y : ℝ ↦ -Real.cos y) (Real.sin x) x :=
    fun x _ ↦ by
      have h := (Real.hasDerivAt_cos x).neg
      rw [neg_neg] at h
      exact h
  have hsqc : ContinuousOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (uIcc (1 : ℝ) T) :=
    (continuous_pow 2).continuousOn.inv₀ fun x hx ↦ (pow_pos (hpos x hx) 2).ne'
  have hu' : IntervalIntegrable (fun x : ℝ ↦ -(x ^ 2)⁻¹) volume 1 T :=
    hsqc.neg.intervalIntegrable
  have hv' : IntervalIntegrable Real.sin volume 1 T := Real.continuous_sin.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hcongr : ∫ t in (1 : ℝ)..T, Real.sin t / t = ∫ x in (1 : ℝ)..T, x⁻¹ * Real.sin x := by
    congr 1
    funext t
    rw [div_eq_inv_mul]
  have h1 : |T⁻¹ * -Real.cos T| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hT0]
    calc T⁻¹ * |Real.cos T| ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ hT) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h2 : |(1 : ℝ)⁻¹ * -Real.cos 1| ≤ 1 := by
    rw [inv_one, one_mul, abs_neg]
    exact Real.abs_cos_le_one _
  have hsq : ∫ x in (1 : ℝ)..T, (x ^ 2)⁻¹ = 1 - T⁻¹ := by
    have hd : ∀ x ∈ uIcc (1 : ℝ) T, HasDerivAt (fun y : ℝ ↦ -y⁻¹) ((x ^ 2)⁻¹) x :=
      fun x hx ↦ by
        have h := (hasDerivAt_inv (hpos x hx).ne').neg
        rw [neg_neg] at h
        exact h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hsqc.intervalIntegrable]
    simp
    ring
  have h3 : |∫ x in (1 : ℝ)..T, -(x ^ 2)⁻¹ * -Real.cos x| ≤ 1 := by
    have hb : ∀ᵐ x ∂volume, x ∈ Ioc (1 : ℝ) T → ‖-(x ^ 2)⁻¹ * -Real.cos x‖ ≤ (x ^ 2)⁻¹ :=
      ae_of_all _ fun x hx ↦ by
        rw [neg_mul_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (sq_nonneg x)]
        exact mul_le_of_le_one_right (inv_nonneg.mpr (sq_nonneg x)) (Real.abs_cos_le_one _)
    have h := intervalIntegral.norm_integral_le_of_norm_le hT hb hsqc.intervalIntegrable
    rw [Real.norm_eq_abs, hsq] at h
    have : 0 ≤ T⁻¹ := inv_nonneg.mpr hT0.le
    linarith
  rw [hcongr, hparts]
  calc |T⁻¹ * -Real.cos T - (1 : ℝ)⁻¹ * -Real.cos 1 - ∫ x in (1 : ℝ)..T, -(x ^ 2)⁻¹ * -Real.cos x|
      ≤ |T⁻¹ * -Real.cos T - (1 : ℝ)⁻¹ * -Real.cos 1| +
          |∫ x in (1 : ℝ)..T, -(x ^ 2)⁻¹ * -Real.cos x| := abs_sub _ _
    _ ≤ (|T⁻¹ * -Real.cos T| + |(1 : ℝ)⁻¹ * -Real.cos 1|) + 1 :=
        add_le_add (abs_sub _ _) h3
    _ ≤ (1 + 1) + 1 := by linarith
    _ = 3 := by norm_num

/-- The integral of `sinc` over `[0, T]` is bounded uniformly in `T`. -/
theorem abs_integral_sinc_le (T : ℝ) : |∫ t in (0 : ℝ)..T, Real.sinc t| ≤ 4 := by
  wlog hT : 0 ≤ T generalizing T
  · have h := this (-T) (by linarith)
    have h1 := intervalIntegral.integral_comp_neg (f := Real.sinc) (a := 0) (b := -T)
    simp only [Real.sinc_neg, neg_zero, neg_neg] at h1
    rw [intervalIntegral.integral_symm, ← h1, abs_neg]
    exact h
  have hbd : ∀ a b : ℝ, ∀ x ∈ Set.uIoc a b, ‖Real.sinc x‖ ≤ 1 := fun a b x _ ↦ by
    rw [Real.norm_eq_abs]
    exact Real.abs_sinc_le_one x
  by_cases hT1 : T ≤ 1
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (hbd 0 T)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT, one_mul] at h
    linarith
  · have hT1' : 1 ≤ T := (not_le.mp hT1).le
    have hsplit : ∫ t in (0 : ℝ)..T, Real.sinc t =
        (∫ t in (0 : ℝ)..1, Real.sinc t) + ∫ t in (1 : ℝ)..T, Real.sinc t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (Real.continuous_sinc.intervalIntegrable _ _)
        (Real.continuous_sinc.intervalIntegrable _ _)).symm
    have h01 : |∫ t in (0 : ℝ)..1, Real.sinc t| ≤ 1 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (hbd 0 1)
      simpa using h
    have h1T : ∫ t in (1 : ℝ)..T, Real.sinc t = ∫ t in (1 : ℝ)..T, Real.sin t / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT1'] at ht
      exact Real.sinc_of_ne_zero (zero_lt_one.trans_le ht.1).ne'
    rw [hsplit, h1T]
    calc |(∫ t in (0 : ℝ)..1, Real.sinc t) + ∫ t in (1 : ℝ)..T, Real.sin t / t|
        ≤ |∫ t in (0 : ℝ)..1, Real.sinc t| + |∫ t in (1 : ℝ)..T, Real.sin t / t| :=
          abs_add_le _ _
      _ ≤ 1 + 3 := add_le_add h01 (abs_integral_sin_div_le hT1')
      _ = 4 := by norm_num

/-- The integral of `sinc (c x)` over `[-L, L]` is bounded by `8 / |c|`, uniformly in `L`. -/
theorem abs_integral_sinc_mul_le {c : ℝ} (hc : c ≠ 0) (L : ℝ) :
    |∫ x in (-L)..L, Real.sinc (c * x)| ≤ 8 / |c| := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.sinc) hc, smul_eq_mul, abs_mul, abs_inv]
  have hsplit : ∫ x in (c * -L)..(c * L), Real.sinc x =
      (∫ x in (c * -L)..0, Real.sinc x) + ∫ x in (0 : ℝ)..(c * L), Real.sinc x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Real.continuous_sinc.intervalIntegrable _ _)
      (Real.continuous_sinc.intervalIntegrable _ _)).symm
  have hleft : ∫ x in (c * -L)..0, Real.sinc x = ∫ x in (0 : ℝ)..(c * L), Real.sinc x := by
    have h1 := intervalIntegral.integral_comp_neg (f := Real.sinc) (a := 0) (b := c * L)
    simp only [Real.sinc_neg, neg_zero] at h1
    rw [h1, mul_neg]
  rw [hsplit, hleft, ← two_mul, abs_mul, abs_two]
  have h := abs_integral_sinc_le (c * L)
  have hc0 : 0 < |c| := abs_pos.mpr hc
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hc0.le)

/-- The integrand of the real term of (12.4.1.1), p. 514, summed over the two signs of the
dilation, on both sides of `g = 1`. -/
def realTermDensity (g : ℝ) : ℝ :=
  1 / 2 * (|g - 1|⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ)

section Trace

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀
local notation "evv" => RealPWBand.evaluationVector Y hμ₀

/-- Without weight the sharp trace of the dilation by `g⁻¹` is an explicit integral of `sinc`. -/
theorem realPWSharpTrace_zero_zero_eq_sinc (hY : 0 < Y) (g : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    realPWSharpTrace Y 0 0 hs g L =
      ((g ^ (-(1 / 2 : ℝ)) * Y * ((∫ x in (-L)..L, Real.sinc (2 * π * Y * (g⁻¹ - 1) * x)) +
        ∫ x in (-L)..L, Real.sinc (2 * π * Y * (g⁻¹ + 1) * x)) : ℝ) : ℂ) := by
  have hc (c : ℝ) : Continuous fun x : ℝ ↦ Real.sinc (c * x) :=
    Real.continuous_sinc.comp (by fun_prop)
  have hpt : ∀ x : ℝ, sharpIntervalMask L x * realPWSharpDensity Y 0 0 hs g x =
      (Icc (-L) L).indicator (fun x : ℝ ↦ ((g ^ (-(1 / 2 : ℝ)) * Y *
        (Real.sinc (2 * π * Y * (g⁻¹ - 1) * x) + Real.sinc (2 * π * Y * (g⁻¹ + 1) * x)) : ℝ) :
          ℂ)) x := by
    intro x
    by_cases hx : x ∈ Icc (-L) L
    · have hm : sharpIntervalMask L x = 1 := by simp [sharpIntervalMask, hx]
      rw [hm, one_mul, indicator_of_mem hx, realPWSharpDensity_zero_zero Y hs,
        realPWBand_evaluation_evaluationVector Y hs hY, bandKernel,
        show 2 * π * Y * (g⁻¹ * x - x) = 2 * π * Y * (g⁻¹ - 1) * x by ring,
        show 2 * π * Y * (g⁻¹ * x + x) = 2 * π * Y * (g⁻¹ + 1) * x by ring]
      push_cast
      ring
    · have hm : sharpIntervalMask L x = 0 := by simp [sharpIntervalMask, hx]
      rw [hm, zero_mul, indicator_of_notMem hx]
  change ∫ x, sharpIntervalMask L x * realPWSharpDensity Y 0 0 hs g x = _
  rw [integral_congr_ae (ae_of_all _ hpt), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (neg_le_self hL),
    intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hc _).intervalIntegrable _ _)
      ((hc _).intervalIntegrable _ _)]

/-- Without weight the sharp trace of the dilation by `g⁻¹` is bounded by a multiple of
`g ^ (1/2) (1 / |g - 1| + 1)`, uniformly in the cutoff. -/
theorem norm_realPWSharpTrace_zero_zero_le (hY : 0 < Y) {g : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1)
    {L : ℝ} (hL : 0 ≤ L) :
    ‖realPWSharpTrace Y 0 0 hs g L‖ ≤ 2 * g ^ (1 / 2 : ℝ) * (|g - 1|⁻¹ + 1) := by
  have hπ : 0 < π := Real.pi_pos
  have hr0 : 0 < g ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hg0 _
  have hr : g ^ (1 / 2 : ℝ) = g ^ (-(1 / 2 : ℝ)) * g := by
    rw [← Real.rpow_add_one hg0.ne']
    norm_num
  have hg1' : 0 < |g - 1| := abs_pos.mpr (sub_ne_zero.mpr hg1)
  have habs1 : |2 * π * Y * (g⁻¹ - 1)| = 2 * π * Y * (|g - 1| / g) := by
    have h : g⁻¹ - 1 = -(g - 1) / g := by
      field_simp
      ring
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π * Y), h, abs_div, abs_neg,
      abs_of_pos hg0]
  have habs2 : |2 * π * Y * (g⁻¹ + 1)| = 2 * π * Y * ((g + 1) / g) := by
    have h : g⁻¹ + 1 = (g + 1) / g := by
      field_simp
      ring
    rw [abs_of_pos (by positivity : 0 < 2 * π * Y * (g⁻¹ + 1)), h]
  have hc1 : 2 * π * Y * (g⁻¹ - 1) ≠ 0 := by
    rw [← abs_pos, habs1]
    positivity
  have hc2 : 2 * π * Y * (g⁻¹ + 1) ≠ 0 := by
    rw [← abs_pos, habs2]
    positivity
  have h1 := abs_integral_sinc_mul_le hc1 L
  have h2 := abs_integral_sinc_mul_le hc2 L
  rw [habs1] at h1
  rw [habs2] at h2
  have e1 : g ^ (-(1 / 2 : ℝ)) * Y * (8 / (2 * π * Y * (|g - 1| / g))) =
      4 / π * (g ^ (-(1 / 2 : ℝ)) * g) * |g - 1|⁻¹ := by
    field_simp
    ring
  have e2 : g ^ (-(1 / 2 : ℝ)) * Y * (8 / (2 * π * Y * ((g + 1) / g))) =
      4 / π * (g ^ (-(1 / 2 : ℝ)) * g) * (g + 1)⁻¹ := by
    have : g + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hinv : (g + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h4π : 4 / π ≤ 2 := by
    rw [div_le_iff₀ hπ]
    linarith [Real.two_le_pi]
  rw [realPWSharpTrace_zero_zero_eq_sinc Y hs hY g hL, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (mul_pos hr0 hY), hr]
  have hrg : 0 ≤ g ^ (-(1 / 2 : ℝ)) * g := (mul_pos hr0 hg0).le
  calc g ^ (-(1 / 2 : ℝ)) * Y * |(∫ x in (-L)..L, Real.sinc (2 * π * Y * (g⁻¹ - 1) * x)) +
        ∫ x in (-L)..L, Real.sinc (2 * π * Y * (g⁻¹ + 1) * x)|
      ≤ g ^ (-(1 / 2 : ℝ)) * Y * (8 / (2 * π * Y * (|g - 1| / g)) +
          8 / (2 * π * Y * ((g + 1) / g))) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2))
          (mul_pos hr0 hY).le
    _ = 4 / π * (g ^ (-(1 / 2 : ℝ)) * g) * (|g - 1|⁻¹ + (g + 1)⁻¹) := by
        rw [mul_add, e1, e2]
        ring
    _ ≤ 2 * (g ^ (-(1 / 2 : ℝ)) * g) * (|g - 1|⁻¹ + 1) := by
        have hA : 0 ≤ |g - 1|⁻¹ := inv_nonneg.mpr hg1'.le
        have hB : 0 ≤ (g + 1)⁻¹ := inv_nonneg.mpr (by linarith)
        exact mul_le_mul (mul_le_mul_of_nonneg_right h4π hrg) (by linarith)
          (by linarith) (by positivity)

end Trace

/-- Without weight the sharp trace of a dilation depends on the bandwidth `Y` and the cutoff
`L` only through the product `Y L`. -/
theorem realPWSharpTrace_zero_zero_scale (hs : (0 : ℝ) ≤ 0) {Y : ℝ} (hY : 0 < Y) (g : ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    realPWSharpTrace Y 0 0 hs g L = realPWSharpTrace 1 0 0 hs g (Y * L) := by
  have key : ∀ c : ℝ, Y * ∫ x in (-L)..L, Real.sinc (2 * π * Y * c * x) =
      ∫ t in (-(Y * L))..(Y * L), Real.sinc (2 * π * 1 * c * t) := by
    intro c
    have h := intervalIntegral.integral_comp_mul_left (a := -L) (b := L)
      (f := fun t : ℝ ↦ Real.sinc (2 * π * 1 * c * t)) hY.ne'
    have hf : (fun x : ℝ ↦ Real.sinc (2 * π * 1 * c * (Y * x))) =
        fun x : ℝ ↦ Real.sinc (2 * π * Y * c * x) := by
      funext x
      congr 1
      ring
    rw [hf] at h
    rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hY.ne', one_mul, mul_neg]
  rw [realPWSharpTrace_zero_zero_eq_sinc Y hs hY g hL,
    realPWSharpTrace_zero_zero_eq_sinc 1 hs one_pos g (mul_nonneg hY.le hL), ← key, ← key]
  push_cast
  ring

/-- For `g > 1` the limit of the sharp trace without weight is the real-term density. -/
theorem realPWSharpTraceLimit_eq_realTermDensity_of_one_lt {g : ℝ} (hg : 1 < g) :
    realPWSharpTraceLimit 0 g = ((realTermDensity g : ℝ) : ℂ) := by
  rw [realPWSharpTraceLimit_of_lt_half (by norm_num) hg, realTermDensity,
    abs_of_pos (by linarith)]

/-- For `0 < g < 1` the limit of the sharp trace of the reciprocal dilation is the real-term
density at `g`. -/
theorem realPWSharpTraceLimit_inv_eq_realTermDensity_of_lt_one {g : ℝ} (hg0 : 0 < g)
    (hg1 : g < 1) : realPWSharpTraceLimit 0 g⁻¹ = ((realTermDensity g : ℝ) : ℂ) := by
  rw [realPWSharpTraceLimit_zero_inv hg0 hg1, realTermDensity, abs_of_neg (by linarith), neg_sub,
    add_comm g 1]

section Limit

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀
local notation "evv" => RealPWBand.evaluationVector Y hμ₀

/-- Reconstruction: without weight, for every `g > 0` other than `1`, the sharp trace of the
dilation by `g⁻¹` tends to the real-term density at `g` as the cutoff is removed. -/
theorem tendsto_realPWSharpTrace_zero_zero (hY : 0 < Y) {g : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) :
    Tendsto (fun L ↦ realPWSharpTrace Y 0 0 hs g L) atTop
      (𝓝 ((realTermDensity g : ℝ) : ℂ)) := by
  rcases lt_or_gt_of_ne hg1 with h | h
  · have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr h
    obtain ⟨-, hlim⟩ := exists_bound_and_tendsto_realPWSharpTrace (Y := Y) (α := 0) (s := 0)
      hY le_rfl hs hinv g⁻¹
    have h1 : Tendsto (fun L : ℝ ↦ L / g) atTop atTop := tendsto_id.atTop_div_const hg0
    have h2 := (continuous_star.tendsto _).comp ((hlim g⁻¹ ⟨le_rfl, le_rfl⟩).comp h1)
    rw [realPWSharpTraceLimit_inv_eq_realTermDensity_of_lt_one hg0 h, ← starRingEnd_apply,
      Complex.conj_ofReal] at h2
    exact h2.congr fun L ↦ (realPWSharpTrace_zero_zero_eq_star_inv Y hs hg0 L).symm
  · obtain ⟨-, hlim⟩ := exists_bound_and_tendsto_realPWSharpTrace (Y := Y) (α := 0) (s := 0)
      hY le_rfl hs h g
    have h2 := hlim g ⟨le_rfl, le_rfl⟩
    rwa [realPWSharpTraceLimit_eq_realTermDensity_of_one_lt h] at h2

/-- Reconstruction: without weight, the sharp trace integrated against a function `ψ` supported
in `[a, b]` with `0 < a`, which vanishes at `g = 1` at a linear rate, converges to the integral
of `ψ` against the real-term density. The support may contain `g = 1`: the bound
`norm_realPWSharpTrace_zero_zero_le` and the linear vanishing of `ψ` give a dominating
constant. -/
theorem tendsto_integral_realPWSharpTrace_zero_zero (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g, ‖ψ g‖ ≤ K * |g - 1|) :
    Tendsto (fun L ↦ ∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) atTop
      (𝓝 (∫ g, ψ g * ((realTermDensity g : ℝ) : ℂ))) := by
  have hψ1 : ψ 1 = 0 := by
    have h := hK 1
    rw [sub_self, abs_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  let M : ℝ := 2 * |K| * (1 + |b|) * (2 + |b|)
  have hM0 : 0 ≤ M := by positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun g ↦ (Icc a b).indicator (fun _ ↦ M) g) (.of_forall fun L ↦ ?_) ?_ ?_
    (ae_of_all _ fun g ↦ ?_)
  · exact hψ.aestronglyMeasurable.mul (measurable_realPWSharpTrace hs L).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    refine ae_of_all _ fun g ↦ ?_
    by_cases hg : g ∈ Icc a b
    · rw [indicator_of_mem hg]
      by_cases hg1 : g = 1
      · rw [hg1, hψ1, zero_mul, norm_zero]
        exact hM0
      · have hg0 : 0 < g := ha0.trans_le hg.1
        have hτ := norm_realPWSharpTrace_zero_zero_le Y hs hY hg0 hg1 hL
        have hd : 0 < |g - 1| := abs_pos.mpr (sub_ne_zero.mpr hg1)
        have hbb : g ≤ |b| := hg.2.trans (le_abs_self b)
        have hroot : g ^ (1 / 2 : ℝ) ≤ 1 + |b| := by
          rcases le_or_gt g 1 with h1 | h1
          · have := Real.rpow_le_one hg0.le h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
            linarith [abs_nonneg b]
          · have := Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num : (1 / 2 : ℝ) ≤ 1)
            rw [Real.rpow_one] at this
            linarith
        have hdist : |g - 1| ≤ 1 + |b| := abs_le.mpr ⟨by linarith [abs_nonneg b], by linarith⟩
        have hroot0 : 0 ≤ g ^ (1 / 2 : ℝ) := Real.rpow_nonneg hg0.le _
        have hψb : ‖ψ g‖ ≤ |K| * |g - 1| :=
          (hK g).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hd.le)
        rw [norm_mul]
        calc ‖ψ g‖ * ‖realPWSharpTrace Y 0 0 hs g L‖
            ≤ (|K| * |g - 1|) * (2 * g ^ (1 / 2 : ℝ) * (|g - 1|⁻¹ + 1)) :=
              mul_le_mul hψb hτ (norm_nonneg _) (by positivity)
          _ = 2 * |K| * g ^ (1 / 2 : ℝ) * (1 + |g - 1|) := by
              field_simp
          _ ≤ 2 * |K| * (1 + |b|) * (1 + (1 + |b|)) := by
              gcongr
          _ = M := by ring
    · rw [indicator_of_notMem hg, hψ0 g hg, zero_mul, norm_zero]
  · exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (hs := measure_Icc_lt_top.ne))
  · by_cases hg : g ∈ Icc a b
    · by_cases hg1 : g = 1
      · simp only [hg1, hψ1, zero_mul]
        exact tendsto_const_nhds
      · exact (tendsto_realPWSharpTrace_zero_zero Y hs hY (ha0.trans_le hg.1) hg1).const_mul _
    · simp only [hψ0 g hg, zero_mul]
      exact tendsto_const_nhds

/-- The integral of the squared modulus of the pointwise values of a band vector is the square
of its norm. -/
theorem integral_star_evaluation_mul_self (f : V₀) :
    ∫ x, star (ev x f) * ev x f ∂μ₀ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous 0 0
  have h1 : ⟪f, f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [← h1]
  change _ = ⟪(f.val : Lp ℂ 2 μ₀), (f.val : Lp ℂ 2 μ₀)⟫_ℂ
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [RealPWBand.evaluation_ae Y hμ₀ hμac f] with x hx
  rw [← hx]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

/-- Reconstruction: without weight, for a continuous test function `ψ` of the dilation
supported in `[a, b]` with `0 < a` and vanishing at `g = 1` at a linear rate, the traces of the
sharp cutoffs of its action on the even band converge to the integral of `ψ` against the
real-term density `(1/2) (1 / |g - 1| + 1 / (g + 1)) g ^ (1/2)`.
Paper: this is the real term of Theorem 12.4.1.1, pp. 514–517, on the whole space, for the
test functions of Theorem 12.5.1.1, p. 519, which vanish at norm one. It is the case `k = ℚ`,
`S = {∞}`, `h(1) = 0` of A. Connes, *Trace formula in noncommutative geometry and the zeros of
the Riemann zeta function*, §VII, Theorem 4, p. 31.
Deviation: The limit is taken in the spatial cutoff at fixed bandwidth. Connes takes both
cutoffs equal and lets them tend to infinity. -/
theorem exists_realPWTestCutoff_trace_limit_through_one (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g, ‖ψ g‖ ≤ K * |g - 1|) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L (f : V₀), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) ∧
        (T L).val f = (V₀).orthogonalProjectionOnto r) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g * ((realTermDensity g : ℝ) : ℂ))) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_nuclear Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) =
      fun L ↦ ∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L := funext hT2
  rw [h]
  exact tendsto_integral_realPWSharpTrace_zero_zero Y hs hY ha0 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0 hK

/-- Reconstruction: without weight, as the cutoff is removed, the diagonal entry of the cutoff
action of `ψ` at the normalized evaluation vector at the origin tends to the integral of
`ψ g min (g, 1) g ^ (-1/2)`. The test function may be supported on both sides of `g = 1`, and
it need not vanish there. -/
theorem tendsto_realPWZeroLevelCorrection_zero_zero (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    Tendsto (fun L ↦ (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWZeroLevelCorrection Y 0 0 hs ψ L)
      atTop (𝓝 (∫ g, ψ g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) := by
  have hE0 := realPWEvaluationVector_zero_ne_zero Y 0 0 hs hY le_rfl (by norm_num)
  have hN : ev 0 (evv 0) = ((‖evv 0‖ ^ 2 : ℝ) : ℂ) := by
    have h3 : ev 0 (evv 0) = ⟪evv 0, evv 0⟫_ℂ := by
      rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [h3, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hN0 : ((‖evv 0‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hE0))
  have hκ : ∀ g ∈ Icc a b, ∫ x, star (ev x (evv 0)) * ev (g⁻¹ * x) (evv 0) ∂μ₀ =
      ((min g 1 : ℝ) : ℂ) * ((‖evv 0‖ ^ 2 : ℝ) : ℂ) := by
    intro g hg
    have hg0 := ha0.trans_le hg.1
    rcases lt_trichotomy g 1 with h | h | h
    · rw [integral_star_evaluationVector_zero_mul_dilate_of_lt_one Y hs hY hg0 h, hN,
        min_eq_left h.le]
    · subst h
      simp only [inv_one, one_mul, min_self, Complex.ofReal_one]
      exact integral_star_evaluation_mul_self Y hs (evv 0)
    · rw [integral_star_evaluationVector_zero_mul_dilate Y 0 0 hs hY h (evv 0), hN,
        min_eq_right h.le, Complex.ofReal_one, one_mul]
  have h2 := (tendsto_realPWTestCorrection Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 (evv 0)
    (fun g ↦ ((min g 1 : ℝ) : ℂ) * ((‖evv 0‖ ^ 2 : ℝ) : ℂ)) hκ).const_mul
    (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹
  have h3 : (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ *
      (∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (((min g 1 : ℝ) : ℂ) * ((‖evv 0‖ ^ 2 : ℝ) : ℂ)))) =
      ∫ g, ψ g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * (ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((min g 1 : ℝ) : ℂ) * ((‖evv 0‖ ^ 2 : ℝ) : ℂ)))) =
      ψ g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    rw [Complex.ofReal_mul]
    field_simp
  rw [h3] at h2
  exact h2

/-- Reconstruction: without weight, for the same test functions, the traces of the cutoffs
compressed to the level of band vectors vanishing at the origin converge to the limit on the
whole band minus the integral of `ψ g min (g, 1) g ^ (-1/2)`. The term removed is
`g ^ (-1/2)` for `g > 1` and `g ^ (1/2)` for `g < 1`. -/
theorem exists_realPWTestCutoff_level_trace_limit_through_one (hY : 0 < Y) {a b : ℝ}
    (ha0 : 0 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g, ‖ψ g‖ ≤ K * |g - 1|) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L (f : V₀), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((realPWZeroLevel Y 0 0 hs).starProjection f))) ∧
        (T L).val f =
          (realPWZeroLevel Y 0 0 hs).starProjection ((V₀).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 ((∫ g, ψ g * ((realTermDensity g : ℝ) : ℂ)) -
          ∫ g, ψ g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_level_nuclear Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) = fun L ↦
      (∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) -
        (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWZeroLevelCorrection Y 0 0 hs ψ L := funext hT2
  rw [h]
  have h1 := tendsto_integral_realPWSharpTrace_zero_zero Y hs hY ha0 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0 hK
  exact h1.sub (tendsto_realPWZeroLevelCorrection_zero_zero Y hs hY ha0 ψ hψc hψ0)

end Limit

end RiemannMasullo.Isolated
