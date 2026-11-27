module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The sine integral

Auxiliary to the logarithm term of the real-place trace without weight
(`Sec4_RealPWUnweightedTrace`, A. Connes, *Trace formula in noncommutative geometry and the
zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31, for `k = ℚ`, `S = {∞}`).

* `sincInt` is the sine integral, the integral of `sinc` over `[0, T]`.
* `tendsto_sincInt`. It tends to `π / 2`. The existence of the limit is integration by parts.
  The value is read off from the limit of the sharp trace of one dilation, which the earlier
  files compute from the Taylor coefficients at the origin.
* `abs_sincInt_sub_le_two_div`. It is within `2 / T` of `π / 2`.
* `sincMean t` is the integral of `sinc (t s)` over `s` in `[-1, 1]`, and `sincMeanInt` its
  integral over `[0, T]`. `tendsto_sincMeanInt_sub_log`: the latter is `π log T` plus the
  constant `sincLogConstant` plus a term that tends to zero. Classically the constant is `π`
  times Euler's constant. That value is not proved here. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

/-- The sine integral: the integral of `sinc` over `[0, T]`. -/
def sincInt (T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, Real.sinc t

/-- The sine integral is odd. -/
theorem sincInt_neg (T : ℝ) : sincInt (-T) = -sincInt T := by
  unfold sincInt
  have h1 := intervalIntegral.integral_comp_neg (f := Real.sinc) (a := 0) (b := T)
  simp only [Real.sinc_neg, neg_zero] at h1
  rw [intervalIntegral.integral_symm, ← h1]

/-- The integral of `sin t / t` over `[A, B]` is at most `2 / A`. -/
theorem abs_integral_sin_div_le_two_div {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    |∫ t in A..B, Real.sin t / t| ≤ 2 / A := by
  have hB : 0 < B := hA.trans_le hAB
  have hpos : ∀ x ∈ uIcc A B, 0 < x := fun x hx ↦ by
    rw [uIcc_of_le hAB] at hx
    exact hA.trans_le hx.1
  have hu : ∀ x ∈ uIcc A B, HasDerivAt (fun y : ℝ ↦ y⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx ↦ hasDerivAt_inv (hpos x hx).ne'
  have hv : ∀ x ∈ uIcc A B, HasDerivAt (fun y : ℝ ↦ -Real.cos y) (Real.sin x) x :=
    fun x _ ↦ by
      have h := (Real.hasDerivAt_cos x).neg
      rw [neg_neg] at h
      exact h
  have hsqc : ContinuousOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (uIcc A B) :=
    (continuous_pow 2).continuousOn.inv₀ fun x hx ↦ (pow_pos (hpos x hx) 2).ne'
  have hu' : IntervalIntegrable (fun x : ℝ ↦ -(x ^ 2)⁻¹) volume A B :=
    hsqc.neg.intervalIntegrable
  have hv' : IntervalIntegrable Real.sin volume A B := Real.continuous_sin.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hcongr : ∫ t in A..B, Real.sin t / t = ∫ x in A..B, x⁻¹ * Real.sin x := by
    congr 1
    funext t
    rw [div_eq_inv_mul]
  have h1 : |B⁻¹ * -Real.cos B| ≤ B⁻¹ := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hB]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hB.le) (Real.abs_cos_le_one _)
  have h2 : |A⁻¹ * -Real.cos A| ≤ A⁻¹ := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hA]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hA.le) (Real.abs_cos_le_one _)
  have hsq : ∫ x in A..B, (x ^ 2)⁻¹ = A⁻¹ - B⁻¹ := by
    have hd : ∀ x ∈ uIcc A B, HasDerivAt (fun y : ℝ ↦ -y⁻¹) ((x ^ 2)⁻¹) x :=
      fun x hx ↦ by
        have h := (hasDerivAt_inv (hpos x hx).ne').neg
        rw [neg_neg] at h
        exact h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hsqc.intervalIntegrable]
    ring
  have h3 : |∫ x in A..B, -(x ^ 2)⁻¹ * -Real.cos x| ≤ A⁻¹ - B⁻¹ := by
    have hb : ∀ᵐ x ∂volume, x ∈ Ioc A B → ‖-(x ^ 2)⁻¹ * -Real.cos x‖ ≤ (x ^ 2)⁻¹ :=
      ae_of_all _ fun x _ ↦ by
        rw [neg_mul_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (sq_nonneg x)]
        exact mul_le_of_le_one_right (inv_nonneg.mpr (sq_nonneg x)) (Real.abs_cos_le_one _)
    have h := intervalIntegral.norm_integral_le_of_norm_le hAB hb hsqc.intervalIntegrable
    rwa [Real.norm_eq_abs, hsq] at h
  rw [hcongr, hparts]
  calc |B⁻¹ * -Real.cos B - A⁻¹ * -Real.cos A - ∫ x in A..B, -(x ^ 2)⁻¹ * -Real.cos x|
      ≤ |B⁻¹ * -Real.cos B - A⁻¹ * -Real.cos A| +
          |∫ x in A..B, -(x ^ 2)⁻¹ * -Real.cos x| := abs_sub _ _
    _ ≤ (|B⁻¹ * -Real.cos B| + |A⁻¹ * -Real.cos A|) + (A⁻¹ - B⁻¹) :=
        add_le_add (abs_sub _ _) h3
    _ ≤ (B⁻¹ + A⁻¹) + (A⁻¹ - B⁻¹) := by linarith
    _ = 2 / A := by ring

/-- Two values of the sine integral beyond `A > 0` differ by at most `2 / A`. -/
theorem abs_sincInt_sub_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    |sincInt B - sincInt A| ≤ 2 / A := by
  have hsub : sincInt B - sincInt A = ∫ t in A..B, Real.sinc t := by
    unfold sincInt
    exact intervalIntegral.integral_interval_sub_left
      (Real.continuous_sinc.intervalIntegrable _ _) (Real.continuous_sinc.intervalIntegrable _ _)
  have hcongr : ∫ t in A..B, Real.sinc t = ∫ t in A..B, Real.sin t / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hAB] at ht
    exact Real.sinc_of_ne_zero (hA.trans_le ht.1).ne'
  rw [hsub, hcongr]
  exact abs_integral_sin_div_le_two_div hA hAB

/-- The sine integral has a limit at infinity. -/
theorem exists_tendsto_sincInt : ∃ ℓ : ℝ, Tendsto sincInt atTop (𝓝 ℓ) := by
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε ↦ ?_⟩
  have hA : 0 < 2 / ε + 1 := by positivity
  refine ⟨sincInt '' Ici (2 / ε + 1), image_mem_map (Ici_mem_atTop _), ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  wlog hab : a ≤ b generalizing a b
  · rw [dist_comm]
    exact this b hb a ha (le_of_not_ge hab)
  rw [dist_comm, Real.dist_eq]
  have ha' : 2 / ε + 1 ≤ a := ha
  calc |sincInt b - sincInt a| ≤ 2 / a := abs_sincInt_sub_le (hA.trans_le ha') hab
    _ ≤ 2 / (2 / ε + 1) := div_le_div_of_nonneg_left zero_le_two hA ha'
    _ < ε := by
        rw [div_lt_iff₀ hA]
        have : ε * (2 / ε + 1) = 2 + ε := by
          field_simp
        linarith

/-- The integral of `sinc (c x)` over `[-L, L]` in terms of the sine integral. -/
theorem integral_sinc_mul_eq {c : ℝ} (hc : c ≠ 0) (L : ℝ) :
    ∫ x in (-L)..L, Real.sinc (c * x) = 2 * sincInt (c * L) / c := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.sinc) hc, smul_eq_mul]
  have hsplit : ∫ x in (c * -L)..(c * L), Real.sinc x =
      (∫ x in (c * -L)..0, Real.sinc x) + ∫ x in (0 : ℝ)..(c * L), Real.sinc x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Real.continuous_sinc.intervalIntegrable _ _)
      (Real.continuous_sinc.intervalIntegrable _ _)).symm
  have hleft : ∫ x in (c * -L)..0, Real.sinc x = ∫ x in (0 : ℝ)..(c * L), Real.sinc x := by
    have h1 := intervalIntegral.integral_comp_neg (f := Real.sinc) (a := 0) (b := c * L)
    simp only [Real.sinc_neg, neg_zero] at h1
    rw [h1, mul_neg]
  rw [hsplit, hleft, sincInt]
  field_simp
  ring

/-- The limit of the integral of `sinc (c x)` over `[-L, L]`, given the limit of the sine
integral. -/
theorem tendsto_integral_sinc_mul {ℓ : ℝ} (hℓ : Tendsto sincInt atTop (𝓝 ℓ)) {c : ℝ}
    (hc : c ≠ 0) :
    Tendsto (fun L ↦ ∫ x in (-L)..L, Real.sinc (c * x)) atTop (𝓝 (2 * ℓ / |c|)) := by
  have h : (fun L ↦ ∫ x in (-L)..L, Real.sinc (c * x)) =
      fun L ↦ 2 * sincInt (|c| * L) / |c| := by
    funext L
    rw [integral_sinc_mul_eq hc]
    rcases lt_or_gt_of_ne hc with h | h
    · rw [abs_of_neg h, show c * L = -(-c * L) by ring, sincInt_neg]
      ring
    · rw [abs_of_pos h]
  rw [h]
  exact ((hℓ.comp (tendsto_id.const_mul_atTop (abs_pos.mpr hc))).const_mul 2).div_const _

/-- The Dirichlet integral: the sine integral tends to `π / 2`. The value is read off from the
limit of the sharp trace of the dilation by `1/2`, which is known from the Taylor coefficients
at the origin. -/
theorem tendsto_sincInt : Tendsto sincInt atTop (𝓝 (π / 2)) := by
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_sincInt
  have hs : (0 : ℝ) ≤ 0 := le_rfl
  have hπ : 0 < π := Real.pi_pos
  have hlim := tendsto_realPWSharpTrace_zero_zero 1 hs one_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  have e1 : 2 * π * 1 * ((2 : ℝ)⁻¹ - 1) = -π := by ring
  have e2 : 2 * π * 1 * ((2 : ℝ)⁻¹ + 1) = 3 * π := by ring
  have hc1 : 2 * π * 1 * ((2 : ℝ)⁻¹ - 1) ≠ 0 := by
    rw [e1]
    exact (neg_neg_of_pos hπ).ne
  have hc2 : 2 * π * 1 * ((2 : ℝ)⁻¹ + 1) ≠ 0 := by
    rw [e2]
    positivity
  have h1 := tendsto_integral_sinc_mul hℓ hc1
  have h2 := tendsto_integral_sinc_mul hℓ hc2
  rw [e1, abs_neg, abs_of_pos hπ] at h1
  rw [e2, abs_of_pos (by positivity : 0 < 3 * π)] at h2
  have hform : Tendsto (fun L ↦ realPWSharpTrace 1 0 0 hs 2 L) atTop
      (𝓝 (((2 : ℝ) ^ (-(1 / 2 : ℝ)) * 1 * (2 * ℓ / π + 2 * ℓ / (3 * π)) : ℝ) : ℂ)) := by
    refine Tendsto.congr' ?_ ((Complex.continuous_ofReal.tendsto _).comp
      ((h1.add h2).const_mul ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * 1)))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    rw [realPWSharpTrace_zero_zero_eq_sinc 1 hs one_pos 2 hL, e1, e2]
    rfl
  have heq := Complex.ofReal_injective (tendsto_nhds_unique hlim hform)
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hr : (2 : ℝ) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * 2 := by
    rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [realTermDensity, show (2 : ℝ) - 1 = 1 by norm_num, abs_one, hr] at heq
  have hℓ2 : ℓ = π / 2 := by
    have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (4 / 3) =
        (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (8 * ℓ / (3 * π)) := by
      have e : 2 * ℓ / π + 2 * ℓ / (3 * π) = 8 * ℓ / (3 * π) := by
        field_simp
        ring
      rw [← e]
      linarith
    have h4 := mul_left_cancel₀ hr0.ne' h3
    field_simp at h4
    linarith
  rw [← hℓ2]
  exact hℓ

/-- The sine integral is within `2 / T` of `π / 2`. -/
theorem abs_sincInt_sub_le_two_div {T : ℝ} (hT : 0 < T) : |sincInt T - π / 2| ≤ 2 / T := by
  have hev : ∀ᶠ B in atTop, |sincInt B - sincInt T| ≤ 2 / T := by
    filter_upwards [eventually_ge_atTop T] with B hB using abs_sincInt_sub_le hT hB
  have hlim : Tendsto (fun B ↦ |sincInt B - sincInt T|) atTop (𝓝 |π / 2 - sincInt T|) :=
    (tendsto_sincInt.sub_const _).abs
  have h := le_of_tendsto hlim hev
  rwa [abs_sub_comm] at h

/-- The integral of `sinc (t s)` over `s` in `[-1, 1]`. It is `2 Si(t) / t`, with value `2` at
`t = 0`, and it is continuous. -/
def sincMean (t : ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, Real.sinc (t * s)

/-- The mean is continuous. -/
theorem continuous_sincMean : Continuous sincMean :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t s : ℝ ↦ Real.sinc (t * s))
    (Real.continuous_sinc.comp (continuous_fst.mul continuous_snd)) (-1) 1

/-- Away from zero the mean is twice the sine integral divided by the argument. -/
theorem sincMean_of_ne_zero {t : ℝ} (ht : t ≠ 0) : sincMean t = 2 * sincInt t / t := by
  unfold sincMean
  rw [integral_sinc_mul_eq ht 1, mul_one]

/-- The integral of `sinc (c x)` over `[-L, L]` is `L` times the mean at `c L`. -/
theorem integral_sinc_mul_eq_sincMean (c L : ℝ) :
    ∫ x in (-L)..L, Real.sinc (c * x) = L * sincMean (c * L) := by
  by_cases hL : L = 0
  · subst hL
    simp
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1)
    (f := fun x : ℝ ↦ Real.sinc (c * x)) hL
  unfold sincMean
  have hf : (fun s : ℝ ↦ Real.sinc (c * L * s)) = fun s ↦ Real.sinc (c * (L * s)) := by
    funext s
    rw [mul_assoc]
  rw [hf, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL, one_mul, mul_neg_one, mul_one]

/-- The integral of the mean over `[0, T]`. -/
def sincMeanInt (T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, sincMean t

/-- The constant in the logarithmic growth of `sincMeanInt`. Classically it is `π` times
Euler's constant. That value is not proved here. -/
def sincLogConstant : ℝ :=
  sincMeanInt 1 + 2 * ∫ t in Ioi (1 : ℝ), (sincInt t - π / 2) / t

/-- The sine integral is continuous. -/
theorem continuous_sincInt : Continuous sincInt :=
  intervalIntegral.continuous_primitive
    (fun a b ↦ Real.continuous_sinc.intervalIntegrable a b) 0

/-- The difference of the sine integral and its limit, divided by the argument, is integrable
at infinity. -/
theorem integrableOn_sincInt_sub_div :
    IntegrableOn (fun t : ℝ ↦ (sincInt t - π / 2) / t) (Ioi 1) := by
  have hdom : IntegrableOn (fun t : ℝ ↦ 2 * t ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2
  have hcont : ContinuousOn (fun t : ℝ ↦ (sincInt t - π / 2) / t) (Ioi 1) :=
    ((continuous_sincInt.sub continuous_const).continuousOn).div continuousOn_id
      fun t ht ↦ (zero_lt_one.trans ht).ne'
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hb := abs_sincInt_sub_le_two_div ht0
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, Real.rpow_neg ht0.le, Real.rpow_two]
  calc |sincInt t - π / 2| / t ≤ (2 / t) / t := div_le_div_of_nonneg_right hb ht0.le
    _ = 2 * (t ^ 2)⁻¹ := by
        field_simp

/-- The integral of the mean grows like `π log T`, with the constant `sincLogConstant`. -/
theorem tendsto_sincMeanInt_sub_log :
    Tendsto (fun T ↦ sincMeanInt T - π * Real.log T) atTop (𝓝 sincLogConstant) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi 1 integrableOn_sincInt_sub_div tendsto_id
  have h2 := (h1.const_mul 2).const_add (sincMeanInt 1)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hpos : ∀ t ∈ uIcc (1 : ℝ) T, 0 < t := fun t ht ↦ by
    rw [uIcc_of_le hT] at ht
    exact zero_lt_one.trans_le ht.1
  have hsplit : sincMeanInt T = sincMeanInt 1 + ∫ t in (1 : ℝ)..T, sincMean t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (continuous_sincMean.intervalIntegrable _ _)
      (continuous_sincMean.intervalIntegrable _ _)).symm
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ (sincInt t - π / 2) / t) volume 1 T :=
    (((continuous_sincInt.sub continuous_const).continuousOn).div continuousOn_id
      fun t ht ↦ (hpos t ht).ne').intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume 1 T :=
    (continuousOn_id.inv₀ fun t ht ↦ (hpos t ht).ne').intervalIntegrable
  have hcongr : ∫ t in (1 : ℝ)..T, sincMean t =
      ∫ t in (1 : ℝ)..T, (2 * ((sincInt t - π / 2) / t) + π * t⁻¹) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := (hpos t ht).ne'
    change sincMean t = 2 * ((sincInt t - π / 2) / t) + π * t⁻¹
    rw [sincMean_of_ne_zero ht0]
    field_simp
    ring
  change sincMeanInt 1 + 2 * ∫ t in (1 : ℝ)..T, (sincInt t - π / 2) / t =
    sincMeanInt T - π * Real.log T
  rw [hsplit, hcongr, intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul π),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos one_pos hT0, div_one]
  ring

/-- The integral over `w` in `[0, β]` of `Y` times the integral of `sinc (2πY w x)` over
`[-L, L]`, in terms of the integral of the mean. -/
theorem integral_bandwidth_mul_integral_sinc {Y L : ℝ} (hY : 0 < Y) (hL : 0 < L) (β : ℝ) :
    ∫ w in (0 : ℝ)..β, Y * ∫ x in (-L)..L, Real.sinc (2 * π * Y * w * x) =
      sincMeanInt (2 * π * Y * L * β) / (2 * π) := by
  have hπ : 0 < π := Real.pi_pos
  have h1 : ∀ w : ℝ, Y * ∫ x in (-L)..L, Real.sinc (2 * π * Y * w * x) =
      Y * L * sincMean (2 * π * Y * L * w) := by
    intro w
    rw [integral_sinc_mul_eq_sincMean, show 2 * π * Y * w * L = 2 * π * Y * L * w by ring]
    ring
  have hΛ : 2 * π * Y * L ≠ 0 := by positivity
  have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := β) (f := sincMean) hΛ
  rw [intervalIntegral.integral_congr (fun w _ ↦ h1 w), intervalIntegral.integral_const_mul, h2,
    mul_zero, smul_eq_mul, sincMeanInt]
  field_simp

end RiemannMasullo.Isolated
