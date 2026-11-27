module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWSineIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The logarithm term of the real-place trace, without weight

Paper: Theorem 12.4.1.1, pp. 514–517, the real term with the term `φ(1) log(λλ')`, in the
fixed-bandwidth model of the real place of `ℚ` of #7354, without weight. This is A. Connes,
*Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*, §VII,
Theorem 4, p. 31, for `k = ℚ` and `S = {∞}`, on the whole space.

`Sec4_RealPWUnweightedTrace` treats test functions that vanish at `g = 1`. Here the test
function `ψ` is arbitrary at `g = 1`, and the trace grows like `ψ 1 log (2πYL)`.

The comparison profile `logTermProfile` is `g ^ (-3/2)` on `[1/2, 2]`. Its trace is explicit:
the change of variable `w = g⁻¹ ± 1` turns it into integrals of the sine mean
(`integral_logTermProfile_mul_realPWSharpTrace`), whose growth is known
(`tendsto_sincMeanInt_sub_log`). The difference of `ψ` and `ψ 1` times the profile vanishes at
`g = 1` and is covered by `Sec4_RealPWUnweightedTrace`.

* `exists_realPWTestCutoff_trace_sub_log_limit`. On the whole band the trace minus
  `ψ 1 log (2πYL)` converges.
* `exists_realPWTestCutoff_level_trace_sub_log_limit`. On the level of band vectors vanishing
  at the origin the logarithmic term is the same, and the constant is smaller by the integral
  of `ψ` against `min (g ^ (1/2), g ^ (-1/2))`.

Reconstruction: The paper does not state this for the model.

Not treated here: a weight. The comparison of the finite part with the principal value of
Connes and of (12.4.1.1). The value of the constant `sincLogConstant / π`, classically Euler's
constant. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

/-- The mean is even. -/
theorem sincMean_neg (t : ℝ) : sincMean (-t) = sincMean t := by
  unfold sincMean
  congr 1
  funext s
  rw [neg_mul, Real.sinc_neg]

/-- The integral of the mean is odd. -/
theorem sincMeanInt_neg (T : ℝ) : sincMeanInt (-T) = -sincMeanInt T := by
  unfold sincMeanInt
  have h1 := intervalIntegral.integral_comp_neg (f := sincMean) (a := 0) (b := T)
  simp only [sincMean_neg, neg_zero] at h1
  rw [intervalIntegral.integral_symm, ← h1]

/-- The integral of the scaled mean over an interval, in terms of `sincMeanInt`. -/
theorem integral_mul_sincMean {Y L : ℝ} (hY : 0 < Y) (hL : 0 < L) (p q : ℝ) :
    ∫ w in p..q, Y * L * sincMean (2 * π * Y * L * w) =
      (sincMeanInt (2 * π * Y * L * q) - sincMeanInt (2 * π * Y * L * p)) / (2 * π) := by
  have hπ := Real.pi_pos
  have hΛ : 2 * π * Y * L ≠ 0 := by positivity
  have h2 := intervalIntegral.integral_comp_mul_left (a := p) (b := q) (f := sincMean) hΛ
  have h3 : ∫ t in (2 * π * Y * L * p)..(2 * π * Y * L * q), sincMean t =
      sincMeanInt (2 * π * Y * L * q) - sincMeanInt (2 * π * Y * L * p) := by
    unfold sincMeanInt
    exact (intervalIntegral.integral_interval_sub_left
      (continuous_sincMean.intervalIntegrable _ _)
      (continuous_sincMean.intervalIntegrable _ _)).symm
  rw [intervalIntegral.integral_const_mul, h2, smul_eq_mul, h3]
  field_simp

/-- The change of variable `w = x⁻¹ + d` on `[1/2, 2]`. -/
theorem integral_inv_sq_mul_comp_inv_add {F : ℝ → ℝ} (hF : Continuous F) (d : ℝ) :
    ∫ x in (1 / 2 : ℝ)..2, (x ^ 2)⁻¹ * F (x⁻¹ + d) = ∫ w in (1 / 2 + d)..(2 + d), F w := by
  have hpos : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, 0 < x := fun x hx ↦ by
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  have hf : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, HasDerivAt (fun y : ℝ ↦ y⁻¹ + d) (-(x ^ 2)⁻¹) x :=
    fun x hx ↦ (hasDerivAt_inv (hpos x hx).ne').add_const d
  have hf' : ContinuousOn (fun x : ℝ ↦ -(x ^ 2)⁻¹) (uIcc (1 / 2 : ℝ) 2) :=
    ((continuous_pow 2).continuousOn.inv₀ fun x hx ↦ (pow_pos (hpos x hx) 2).ne').neg
  have h := intervalIntegral.integral_comp_mul_deriv hf hf' hF
  have e1 : ((1 / 2 : ℝ))⁻¹ + d = 2 + d := by norm_num
  have e2 : (2 : ℝ)⁻¹ + d = 1 / 2 + d := by norm_num
  rw [e1, e2, intervalIntegral.integral_symm (1 / 2 + d) (2 + d)] at h
  have hl : ∫ x in (1 / 2 : ℝ)..2, (F ∘ fun y : ℝ ↦ y⁻¹ + d) x * -(x ^ 2)⁻¹ =
      -∫ x in (1 / 2 : ℝ)..2, (x ^ 2)⁻¹ * F (x⁻¹ + d) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    simp only [Function.comp]
    ring
  rw [hl] at h
  exact neg_injective h

/-- The comparison profile for the logarithm term: `g ^ (-3/2)` on `[1/2, 2]` and zero
elsewhere. It equals `1` at `g = 1`. -/
def logTermProfile (g : ℝ) : ℝ :=
  (Icc (1 / 2 : ℝ) 2).indicator (fun g ↦ g ^ (-(3 / 2 : ℝ))) g

/-- The comparison profile is within `12 |g - 1|` of `1`. -/
theorem abs_one_sub_logTermProfile_le (g : ℝ) : |1 - logTermProfile g| ≤ 12 * |g - 1| := by
  by_cases hg : g ∈ Icc (1 / 2 : ℝ) 2
  · have hd : ∀ x ∈ Icc (1 / 2 : ℝ) 2, HasDerivWithinAt (fun y : ℝ ↦ y ^ (-(3 / 2 : ℝ)))
        (-(3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ) - 1)) (Icc (1 / 2 : ℝ) 2) x := fun x hx ↦
      (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : (0 : ℝ) < x).ne')).hasDerivWithinAt
    have hb : ∀ x ∈ Icc (1 / 2 : ℝ) 2, ‖-(3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ) - 1)‖ ≤ 12 := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      have h1 : x ^ (-(3 / 2 : ℝ) - 1) ≤ (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by norm_num)
      have h2 : (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ) - 1) ≤ 8 := by
        have h3 : (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ) - 1) = (2 : ℝ) ^ (5 / 2 : ℝ) := by
          rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
            ← Real.rpow_neg (by norm_num)]
          norm_num
        have h4 : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        have h5 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
        linarith
      rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
        Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
      linarith
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
      (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 2 by constructor <;> norm_num) hg
    rw [Real.one_rpow, Real.norm_eq_abs, Real.norm_eq_abs] at h
    rw [logTermProfile, indicator_of_mem hg, abs_sub_comm]
    exact h
  · rw [logTermProfile, indicator_of_notMem hg, sub_zero, abs_one]
    have hg' : g < 1 / 2 ∨ 2 < g := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hcon.1, hcon.2⟩
    rcases hg' with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith

/-- A function that is Lipschitz at `g = 1` differs from its value at `1` times the comparison
profile by a term that vanishes at a linear rate. -/
theorem norm_sub_mul_logTermProfile_le {ψ : ℝ → ℂ} {K : ℝ}
    (hK : ∀ g, ‖ψ g - ψ 1‖ ≤ K * |g - 1|) (g : ℝ) :
    ‖ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)‖ ≤ (K + 12 * ‖ψ 1‖) * |g - 1| := by
  have h1 : ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ) =
      (ψ g - ψ 1) + ψ 1 * (((1 - logTermProfile g : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h1]
  calc ‖(ψ g - ψ 1) + ψ 1 * (((1 - logTermProfile g : ℝ) : ℂ))‖
      ≤ ‖ψ g - ψ 1‖ + ‖ψ 1 * (((1 - logTermProfile g : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ K * |g - 1| + ‖ψ 1‖ * (12 * |g - 1|) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (hK g)
          (mul_le_mul_of_nonneg_left (abs_one_sub_logTermProfile_le g) (norm_nonneg _))
    _ = (K + 12 * ‖ψ 1‖) * |g - 1| := by ring

section Profile

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- Without weight the sharp trace integrated against the comparison profile is an explicit
combination of values of `sincMeanInt`. -/
theorem integral_logTermProfile_mul_realPWSharpTrace (hY : 0 < Y) {L : ℝ} (hL : 0 < L) :
    ∫ g, ((logTermProfile g : ℝ) : ℂ) * realPWSharpTrace Y 0 0 hs g L =
      (((sincMeanInt (2 * π * Y * L * 1) + sincMeanInt (2 * π * Y * L * (1 / 2)) +
        (sincMeanInt (2 * π * Y * L * 3) - sincMeanInt (2 * π * Y * L * (3 / 2)))) /
          (2 * π) : ℝ) : ℂ) := by
  let Kf : ℝ → ℝ := fun w ↦ Y * L * sincMean (2 * π * Y * L * w)
  have hKf : Continuous Kf :=
    continuous_const.mul (continuous_sincMean.comp (continuous_const.mul continuous_id))
  have hpt : ∀ g : ℝ, ((logTermProfile g : ℝ) : ℂ) * realPWSharpTrace Y 0 0 hs g L =
      (Icc (1 / 2 : ℝ) 2).indicator (fun g : ℝ ↦ (((g ^ 2)⁻¹ * Kf (g⁻¹ + -1) +
        (g ^ 2)⁻¹ * Kf (g⁻¹ + 1) : ℝ) : ℂ)) g := by
    intro g
    by_cases hg : g ∈ Icc (1 / 2 : ℝ) 2
    · have hg0 : 0 < g := by linarith [hg.1]
      have hpow : g ^ (-(3 / 2 : ℝ)) * g ^ (-(1 / 2 : ℝ)) = (g ^ 2)⁻¹ := by
        rw [← Real.rpow_add hg0, show (-(3 / 2 : ℝ)) + -(1 / 2) = -2 by norm_num,
          Real.rpow_neg hg0.le, Real.rpow_two]
      rw [logTermProfile, indicator_of_mem hg, indicator_of_mem hg,
        realPWSharpTrace_zero_zero_eq_sinc Y hs hY g hL.le, integral_sinc_mul_eq_sincMean,
        integral_sinc_mul_eq_sincMean, ← Complex.ofReal_mul, ← hpow]
      congr 1
      change _ = (g ^ (-(3 / 2 : ℝ)) * g ^ (-(1 / 2 : ℝ))) *
          (Y * L * sincMean (2 * π * Y * L * (g⁻¹ + -1))) +
        (g ^ (-(3 / 2 : ℝ)) * g ^ (-(1 / 2 : ℝ))) *
          (Y * L * sincMean (2 * π * Y * L * (g⁻¹ + 1)))
      rw [show 2 * π * Y * (g⁻¹ - 1) * L = 2 * π * Y * L * (g⁻¹ + -1) by ring,
        show 2 * π * Y * (g⁻¹ + 1) * L = 2 * π * Y * L * (g⁻¹ + 1) by ring]
      ring
    · rw [logTermProfile, indicator_of_notMem hg, indicator_of_notMem hg, Complex.ofReal_zero,
        zero_mul]
  have hpos : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, 0 < x := fun x hx ↦ by
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  have hinvc : ContinuousOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (uIcc (1 / 2 : ℝ) 2) :=
    (continuous_pow 2).continuousOn.inv₀ fun x hx ↦ (pow_pos (hpos x hx) 2).ne'
  have hinv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (uIcc (1 / 2 : ℝ) 2) :=
    continuousOn_id.inv₀ fun x hx ↦ (hpos x hx).ne'
  have hi (d : ℝ) : IntervalIntegrable (fun g : ℝ ↦ (g ^ 2)⁻¹ * Kf (g⁻¹ + d)) volume (1 / 2) 2 :=
    (hinvc.mul (hKf.comp_continuousOn (hinv.add continuousOn_const))).intervalIntegrable
  rw [integral_congr_ae (ae_of_all _ hpt), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_ofReal, intervalIntegral.integral_add (hi _) (hi _),
    integral_inv_sq_mul_comp_inv_add hKf, integral_inv_sq_mul_comp_inv_add hKf,
    integral_mul_sincMean hY hL, integral_mul_sincMean hY hL,
    show (1 / 2 : ℝ) + -1 = -(1 / 2) by norm_num, show (2 : ℝ) + -1 = 1 by norm_num,
    show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num,
    mul_neg, sincMeanInt_neg]
  congr 1
  ring

/-- Without weight the sharp trace integrated against the comparison profile is
`log (2πYL)` plus the constant `sincLogConstant / π` plus a term that tends to zero. -/
theorem tendsto_integral_logTermProfile_sub_log (hY : 0 < Y) :
    Tendsto (fun L ↦ (∫ g, ((logTermProfile g : ℝ) : ℂ) * realPWSharpTrace Y 0 0 hs g L) -
        ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop (𝓝 ((sincLogConstant / π : ℝ) : ℂ)) := by
  have hπ := Real.pi_pos
  have hE := tendsto_sincMeanInt_sub_log
  have hΛ (c : ℝ) (hc : 0 < c) : Tendsto (fun L : ℝ ↦ 2 * π * Y * L * c) atTop atTop := by
    have h : (fun L : ℝ ↦ 2 * π * Y * L * c) = fun L ↦ (2 * π * Y * c) * L := by
      funext L
      ring
    rw [h]
    exact tendsto_id.const_mul_atTop (by positivity)
  have h1 := hE.comp (hΛ 1 one_pos)
  have h2 := hE.comp (hΛ (1 / 2) (by norm_num))
  have h3 := hE.comp (hΛ 3 (by norm_num))
  have h4 := hE.comp (hΛ (3 / 2) (by norm_num))
  have hsum := ((h1.add h2).add (h3.sub h4)).div_const (2 * π)
  have hlimval : (sincLogConstant + sincLogConstant + (sincLogConstant - sincLogConstant)) /
      (2 * π) = sincLogConstant / π := by
    field_simp
    ring
  rw [hlimval] at hsum
  refine Tendsto.congr' ?_ ((Complex.continuous_ofReal.tendsto _).comp hsum)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hΛ0 : 0 < 2 * π * Y * L := by positivity
  have hlog : Real.log (3 / 2 : ℝ) = Real.log 3 + Real.log (1 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [integral_logTermProfile_mul_realPWSharpTrace Y hs hY hL, ← Complex.ofReal_sub]
  simp only [Function.comp_apply]
  congr 1
  rw [Real.log_mul hΛ0.ne' one_ne_zero, Real.log_mul hΛ0.ne' (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.log_mul hΛ0.ne' (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_mul hΛ0.ne' (by norm_num : (3 / 2 : ℝ) ≠ 0), Real.log_one, hlog]
  field_simp
  ring

/-- Without weight, a function supported in `[a, b]` with `0 < a` times the sharp trace is
integrable in the dilation. -/
theorem integrable_mul_realPWSharpTrace_zero_zero (hY : 0 < Y) {L : ℝ} (hL : 0 ≤ L) {a b : ℝ}
    (ha0 : 0 < a) {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) :
    Integrable (fun g ↦ φ g * realPWSharpTrace Y 0 0 hs g L) := by
  refine (hφ.norm.mul_const (a ^ (-(1 / 2 : ℝ)) * Y * (4 * L))).mono'
    (hφ.aestronglyMeasurable.mul (measurable_realPWSharpTrace hs L).aestronglyMeasurable)
    (ae_of_all _ fun g ↦ ?_)
  by_cases hg : g ∈ Icc a b
  · have hg0 : 0 < g := ha0.trans_le hg.1
    have hS : ∀ c : ℝ, |∫ x in (-L)..L, Real.sinc (c * x)| ≤ 2 * L := by
      intro c
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -L) (b := L) (C := 1)
        (f := fun x ↦ Real.sinc (c * x)) (fun x _ ↦ by
          rw [Real.norm_eq_abs]
          exact Real.abs_sinc_le_one _)
      have hLL : |L - -L| = 2 * L := by
        rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]
        ring
      rw [Real.norm_eq_abs, hLL, one_mul] at h
      exact h
    have hr : g ^ (-(1 / 2 : ℝ)) ≤ a ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ha0 hg.1 (by norm_num)
    have hr0 : 0 < g ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hg0 _
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [realPWSharpTrace_zero_zero_eq_sinc Y hs hY g hL, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (mul_pos hr0 hY)]
    calc g ^ (-(1 / 2 : ℝ)) * Y * |(∫ x in (-L)..L, Real.sinc (2 * π * Y * (g⁻¹ - 1) * x)) +
          ∫ x in (-L)..L, Real.sinc (2 * π * Y * (g⁻¹ + 1) * x)|
        ≤ a ^ (-(1 / 2 : ℝ)) * Y * (2 * L + 2 * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hr hY.le)
            ((abs_add_le _ _).trans (add_le_add (hS _) (hS _))) (abs_nonneg _)
            (mul_nonneg (Real.rpow_nonneg ha0.le _) hY.le)
      _ = a ^ (-(1 / 2 : ℝ)) * Y * (4 * L) := by ring
  · rw [hφ0 g hg, zero_mul, norm_zero, zero_mul]

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀
local notation "evv" => RealPWBand.evaluationVector Y hμ₀

/-- The comparison profile is integrable. -/
theorem integrable_logTermProfile : Integrable fun g ↦ ((logTermProfile g : ℝ) : ℂ) := by
  have h : Integrable logTermProfile := by
    unfold logTermProfile
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (continuousOn_id.rpow_const fun g hg ↦
      Or.inl (by linarith [hg.1] : (0 : ℝ) < g).ne').integrableOn_Icc
  exact h.ofReal

/-- Reconstruction: without weight, the sharp trace integrated against a function `ψ`
supported in `[a, b]` with `0 < a`, which near `g = 1` differs from `ψ 1` times the comparison
profile by a term that vanishes at a linear rate, is `ψ 1 log (2πYL)` plus a constant plus a
term that tends to zero. The constant is `ψ 1 sincLogConstant / π` plus the integral of
`ψ` minus `ψ 1` times the profile against the real-term density. -/
theorem tendsto_integral_realPWSharpTrace_sub_log (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g, ‖ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)‖ ≤ K * |g - 1|) :
    Tendsto (fun L ↦ (∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) -
        ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop
      (𝓝 (ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
        ∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ))) := by
  let m : ℝ → ℂ := fun g ↦ ((logTermProfile g : ℝ) : ℂ)
  let ψ' : ℝ → ℂ := fun g ↦ ψ g - ψ 1 * m g
  have hmi : Integrable m := integrable_logTermProfile
  have hm0 : ∀ g ∉ Icc (1 / 2 : ℝ) 2, m g = 0 := fun g hg ↦ by
    change ((logTermProfile g : ℝ) : ℂ) = 0
    rw [logTermProfile, indicator_of_notMem hg, Complex.ofReal_zero]
  have hψ'i : Integrable ψ' := hψ.sub (hmi.const_mul _)
  have hψ'0 : ∀ g ∉ Icc (min a (1 / 2)) (max b 2), ψ' g = 0 := by
    intro g hg
    have h1 : g ∉ Icc a b := fun h ↦
      hg ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
    have h2 : g ∉ Icc (1 / 2 : ℝ) 2 := fun h ↦
      hg ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩
    change ψ g - ψ 1 * m g = 0
    rw [hψ0 g h1, hm0 g h2, mul_zero, sub_zero]
  have hmin : 0 < min a (1 / 2) := lt_min ha0 (by norm_num)
  have h1 := tendsto_integral_realPWSharpTrace_zero_zero Y hs hY hmin ψ' hψ'i hψ'0 hK
  have h2 := (tendsto_integral_logTermProfile_sub_log Y hs hY).const_mul (ψ 1)
  refine (h2.add h1).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hI1 := integrable_mul_realPWSharpTrace_zero_zero Y hs hY hL.le hmin hψ'i hψ'0
  have hI2 := integrable_mul_realPWSharpTrace_zero_zero Y hs hY hL.le
    (by norm_num : (0 : ℝ) < 1 / 2) hmi hm0
  have hsplit : ∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L =
      (∫ g, ψ' g * realPWSharpTrace Y 0 0 hs g L) +
        ψ 1 * ∫ g, m g * realPWSharpTrace Y 0 0 hs g L := by
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change ψ g * _ = (ψ g - ψ 1 * m g) * _ + ψ 1 * (m g * _)
    ring
  rw [hsplit]
  ring

/-- Reconstruction: without weight, for a continuous test function `ψ` of the dilation
supported in `[a, b]` with `0 < a`, the traces of the sharp cutoffs of its action on the even
band are `ψ 1 log (2πYL)` plus a constant plus a term that tends to zero. Here `ψ 1` need not
vanish. The hypothesis `hK` says that `ψ` is Lipschitz at `g = 1`.
Paper: this is Theorem 12.4.1.1, pp. 514–517, on the whole space, with the term
`φ(1) log(λλ')` of (12.4.1.3). It is the case `k = ℚ`, `S = {∞}` of A. Connes, *Trace formula
in noncommutative geometry and the zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31.
Deviation: The finite part is written with the comparison profile `logTermProfile`, and the
constant `sincLogConstant / π` is defined by an integral. Connes writes the finite part as a
principal value normalized by a Fourier transform. The two forms are not compared here.
Classically `sincLogConstant / π` is Euler's constant, which is not proved here. -/
theorem exists_realPWTestCutoff_trace_sub_log_limit (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g, ‖ψ g - ψ 1‖ ≤ K * |g - 1|) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L (f : V₀), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) ∧
        (T L).val f = (V₀).orthogonalProjectionOnto r) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) - ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop
        (𝓝 (ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
          ∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) *
            ((realTermDensity g : ℝ) : ℂ))) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_nuclear Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L) - ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) =
      fun L ↦ (∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) -
        ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ) := funext fun L ↦ by rw [hT2 L]
  rw [h]
  exact tendsto_integral_realPWSharpTrace_sub_log Y hs hY ha0 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0
    (norm_sub_mul_logTermProfile_le hK)

/-- Reconstruction: without weight, for the same test functions, the traces of the cutoffs
compressed to the level of band vectors vanishing at the origin have the same logarithmic
term, and the constant is smaller by the integral of `ψ g min (g, 1) g ^ (-1/2)`. -/
theorem exists_realPWTestCutoff_level_trace_sub_log_limit (hY : 0 < Y) {a b : ℝ}
    (ha0 : 0 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g, ‖ψ g - ψ 1‖ ≤ K * |g - 1|) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L (f : V₀), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((realPWZeroLevel Y 0 0 hs).starProjection f))) ∧
        (T L).val f =
          (realPWZeroLevel Y 0 0 hs).starProjection ((V₀).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) - ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop
        (𝓝 (ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
          (∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ)) -
            ∫ g, ψ g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_level_nuclear Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L) - ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) =
      fun L ↦ ((∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) -
        ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) -
          (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWZeroLevelCorrection Y 0 0 hs ψ L :=
    funext fun L ↦ by
      rw [hT2 L]
      ring
  rw [h]
  exact (tendsto_integral_realPWSharpTrace_sub_log Y hs hY ha0 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0
    (norm_sub_mul_logTermProfile_le hK)).sub
      (tendsto_realPWZeroLevelCorrection_zero_zero Y hs hY ha0 ψ hψc hψ0)

end Profile

end RiemannMasullo.Isolated
