module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod

/-! # The Dirichlet integral

The integral of `sinc t = sin t / t` over `[0, R]`, the sine integral, tends to `π / 2` as
`R → ∞`. The proof writes `1 / t` as `∫ s in Ioi 0, exp (-t * s)` and exchanges the two
integrals, which gives the explicit remainder of `integral_sinc_eq_sub` and the bound
`|∫ t in 0..R, sinc t - π / 2| ≤ 2 / R`.

The file also has the integral of `sinc` against a cosine, and the integral of the sine
integral itself over an interval, through the antiderivative `u * ∫ v in 0..u, sinc v + cos u`.
-/

open Filter MeasureTheory Set Topology Real

@[expose] public noncomputable section

namespace RiemannMasullo

/-- An antiderivative of `sin t * exp (-t * s)` in `t`. -/
private theorem hasDerivAt_exp_neg_mul_sin (s t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ -(exp (-t * s) * (s * sin t + cos t)) / (1 + s ^ 2))
      (sin t * exp (-t * s)) t := by
  have he : HasDerivAt (fun t : ℝ ↦ exp (-t * s)) (exp (-t * s) * (-1 * s)) t :=
    ((hasDerivAt_id t).neg.mul_const s).exp
  have hs : HasDerivAt (fun t : ℝ ↦ s * sin t + cos t) (s * cos t + -sin t) t :=
    ((hasDerivAt_sin t).const_mul s).add (hasDerivAt_cos t)
  have h := ((he.mul hs).neg.div_const (1 + s ^ 2))
  convert h using 1
  have hs2 : (1 + s ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The inner integral in `t`. -/
private theorem integral_sin_mul_exp_neg (s R : ℝ) :
    ∫ t in (0 : ℝ)..R, sin t * exp (-t * s) =
      (1 + s ^ 2)⁻¹ - exp (-R * s) * (s * sin R + cos R) / (1 + s ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_exp_neg_mul_sin s t) (by
      apply Continuous.intervalIntegrable
      fun_prop)]
  simp
  ring

/-- The remainder integrand is dominated by `2 exp (-R s)`. -/
private theorem norm_sinc_remainder_le (R s : ℝ) :
    ‖exp (-R * s) * (s * sin R + cos R) / (1 + s ^ 2)‖ ≤ 2 * exp (-R * s) := by
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hnum : |s * sin R + cos R| ≤ 2 * (1 + s ^ 2) := by
    have h1 : |s * sin R + cos R| ≤ |s| + 1 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ (abs_cos_le_one R))
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg s) (abs_sin_le_one R)
    nlinarith [sq_nonneg (|s| - 1), sq_abs s, abs_nonneg s]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (exp_pos _), abs_of_pos hpos,
    div_le_iff₀ hpos]
  calc exp (-R * s) * |s * sin R + cos R| ≤ exp (-R * s) * (2 * (1 + s ^ 2)) :=
        mul_le_mul_of_nonneg_left hnum (exp_pos _).le
    _ = 2 * exp (-R * s) * (1 + s ^ 2) := by ring

/-- The remainder integrand is continuous. -/
private theorem continuous_sinc_remainder (R : ℝ) :
    Continuous fun s : ℝ ↦ exp (-R * s) * (s * sin R + cos R) / (1 + s ^ 2) := by
  have h1 : Continuous fun s : ℝ ↦ exp (-R * s) * (s * sin R + cos R) := by fun_prop
  have h2 : Continuous fun s : ℝ ↦ 1 + s ^ 2 := by fun_prop
  exact h1.div h2 fun s ↦ by positivity

/-- The remainder integrand is integrable on the half-line. -/
private theorem integrableOn_sinc_remainder {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun s : ℝ ↦ exp (-R * s) * (s * sin R + cos R) / (1 + s ^ 2)) (Ioi 0) :=
  Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hR).const_mul 2)
    (continuous_sinc_remainder R).aestronglyMeasurable
    (ae_of_all _ fun s ↦ norm_sinc_remainder_le R s)

/-- The integral of `sinc` over `[0, R]` as `π / 2` minus an exponentially damped remainder. -/
theorem integral_sinc_eq_sub {R : ℝ} (hR : 0 < R) :
    ∫ t in (0 : ℝ)..R, sinc t = π / 2 -
      ∫ s in Ioi (0 : ℝ), exp (-R * s) * (s * sin R + cos R) / (1 + s ^ 2) := by
  have hcont : Continuous (Function.uncurry fun t s : ℝ ↦ sin t * exp (-t * s)) := by
    unfold Function.uncurry
    fun_prop
  -- `sinc t` as an integral in `s`
  have h2 (t : ℝ) (ht : t ∈ Ioc 0 R) : sinc t = ∫ s in Ioi (0 : ℝ), sin t * exp (-t * s) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ht.1) 0,
      sinc_of_ne_zero ht.1.ne']
    simp only [mul_zero, exp_zero]
    field_simp
  -- integrability on the product
  have hint : Integrable (Function.uncurry fun t s : ℝ ↦ sin t * exp (-t * s))
      ((volume.restrict (Ioc 0 R)).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      change Integrable (fun s : ℝ ↦ sin t * exp (-t * s)) (volume.restrict (Ioi 0))
      exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ht.1) 0).const_mul _
    · refine Integrable.mono' (integrable_const (1 : ℝ))
        hcont.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hval : ∫ s in Ioi (0 : ℝ), ‖Function.uncurry (fun t s : ℝ ↦ sin t * exp (-t * s))
          (t, s)‖ = |sin t| * t⁻¹ := by
        have : ∀ s : ℝ, ‖Function.uncurry (fun t s : ℝ ↦ sin t * exp (-t * s)) (t, s)‖ =
            |sin t| * exp (-t * s) := fun s ↦ by
          simp [Function.uncurry, abs_of_pos (exp_pos _)]
        simp_rw [this]
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ht.1) 0]
        simp only [mul_zero, exp_zero]
        field_simp
      rw [hval, norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs,
        abs_of_pos ht.1, ← div_eq_mul_inv, div_le_one ht.1]
      exact abs_sin_le_abs.trans (abs_of_pos ht.1).le
  rw [intervalIntegral.integral_of_le hR.le, setIntegral_congr_fun measurableSet_Ioc h2,
    integral_integral_swap hint]
  have hinner (s : ℝ) : ∫ t in Ioc 0 R, sin t * exp (-t * s) =
      (1 + s ^ 2)⁻¹ - exp (-R * s) * (s * sin R + cos R) / (1 + s ^ 2) := by
    rw [← intervalIntegral.integral_of_le hR.le, integral_sin_mul_exp_neg]
  simp_rw [hinner]
  have h1 : IntegrableOn (fun s : ℝ ↦ (1 + s ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  rw [integral_sub h1 (integrableOn_sinc_remainder hR), integral_Ioi_inv_one_add_sq,
    arctan_zero, sub_zero]

/-- The integral of `sinc` over `[0, R]` is within `2 / R` of `π / 2`. -/
theorem abs_integral_sinc_sub_le {R : ℝ} (hR : 0 < R) :
    |(∫ t in (0 : ℝ)..R, sinc t) - π / 2| ≤ 2 / R := by
  rw [integral_sinc_eq_sub hR, sub_sub_cancel_left, abs_neg, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hR).const_mul 2)
    (ae_of_all _ fun s ↦ norm_sinc_remainder_le R s)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hR) 0]
  simp only [mul_zero, exp_zero]
  field_simp

/-- **The Dirichlet integral.** `∫ t in 0..R, sinc t` tends to `π / 2` as `R → ∞`. -/
theorem tendsto_integral_sinc_atTop :
    Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..R, sinc t) atTop (𝓝 (π / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun R : ℝ ↦ 2 / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.norm_eq_abs]
  exact abs_integral_sinc_sub_le hR

/-- The integral of `sinc` over `[0, R]` is odd in `R`. -/
theorem integral_sinc_neg (R : ℝ) :
    ∫ t in (0 : ℝ)..(-R), sinc t = -∫ t in (0 : ℝ)..R, sinc t := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R) sinc
  simp only [sinc_neg, neg_zero] at h
  rw [h, intervalIntegral.integral_symm]

/-- The integral of `sinc` over `[0, R]` is bounded, uniformly in `R`. -/
theorem abs_integral_sinc_le (R : ℝ) : |∫ t in (0 : ℝ)..R, sinc t| ≤ π / 2 + 2 := by
  have hsmall (R : ℝ) : |∫ t in (0 : ℝ)..R, sinc t| ≤ |R| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := R)
      (f := sinc) (C := 1) fun x _ ↦ by simpa using abs_sinc_le_one x
    simpa using h
  have hpos (R : ℝ) (hR : 0 ≤ R) : |∫ t in (0 : ℝ)..R, sinc t| ≤ π / 2 + 2 := by
    rcases le_or_gt R 1 with h1 | h1
    · have := hsmall R
      rw [abs_of_nonneg hR] at this
      linarith [pi_pos]
    · have h2 := abs_integral_sinc_sub_le (R := R) (by linarith)
      have h3 : 2 / R ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have h4 := abs_sub_abs_le_abs_sub (∫ t in (0 : ℝ)..R, sinc t) (π / 2)
      rw [abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at h4
      linarith
  rcases le_total 0 R with hR | hR
  · exact hpos R hR
  · have := hpos (-R) (by linarith)
    rwa [integral_sinc_neg, abs_neg] at this

/-- `∫ x in 0..L, c * sinc (c * x)` is the integral of `sinc` over `[0, c * L]`. -/
theorem integral_mul_sinc_mul (c L : ℝ) :
    ∫ x in (0 : ℝ)..L, c * sinc (c * x) = ∫ t in (0 : ℝ)..(c * L), sinc t := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := L) sinc c
  rw [smul_eq_mul, mul_zero] at h
  rw [← h, intervalIntegral.integral_const_mul]

/-- Along `c * R` with `c > 0` and `R → ∞` the integral of `sinc` tends to `π / 2`. -/
theorem tendsto_integral_sinc_mul_of_pos {ι : Type*} {l : Filter ι} {R : ι → ℝ}
    (hR : Tendsto R l atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(c * R i), sinc t) l (𝓝 (π / 2)) :=
  tendsto_integral_sinc_atTop.comp (hR.const_mul_atTop hc)

/-- Along `c * R` with `c < 0` and `R → ∞` the integral of `sinc` tends to `-π / 2`. -/
theorem tendsto_integral_sinc_mul_of_neg {ι : Type*} {l : Filter ι} {R : ι → ℝ}
    (hR : Tendsto R l atTop) {c : ℝ} (hc : c < 0) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(c * R i), sinc t) l (𝓝 (-(π / 2))) := by
  have h := (tendsto_integral_sinc_mul_of_pos hR (neg_pos.mpr hc)).neg
  refine h.congr fun i ↦ ?_
  rw [← integral_sinc_neg]
  congr 1
  ring


/-! ### Products with a cosine -/

/-- `c * sinc (c * x) = sin (c * x) / x` away from `x = 0`. -/
theorem mul_sinc_mul (c : ℝ) {x : ℝ} (hx : x ≠ 0) : c * sinc (c * x) = sin (c * x) / x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [sinc_of_ne_zero (mul_ne_zero hc hx)]
    field_simp

/-- A product of a `sinc` and a cosine as a sum of two `sinc`s. -/
theorem mul_sinc_mul_cos (α β x : ℝ) :
    α * sinc (α * x) * cos (β * x) =
      ((α + β) * sinc ((α + β) * x) + (α - β) * sinc ((α - β) * x)) / 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [mul_zero, sinc_zero, cos_zero, mul_one]
    ring
  · rw [mul_sinc_mul α hx, mul_sinc_mul (α + β) hx, mul_sinc_mul (α - β) hx, add_mul, sub_mul,
      sin_add, sin_sub]
    field_simp
    ring

/-- The integral of a `sinc` against a cosine. -/
theorem integral_mul_sinc_mul_cos (α β L : ℝ) :
    ∫ x in (0 : ℝ)..L, α * sinc (α * x) * cos (β * x) =
      ((∫ t in (0 : ℝ)..((α + β) * L), sinc t) + ∫ t in (0 : ℝ)..((α - β) * L), sinc t) / 2 := by
  simp_rw [mul_sinc_mul_cos]
  have hc (c : ℝ) : IntervalIntegrable (fun x : ℝ ↦ c * sinc (c * x)) volume 0 L :=
    (continuous_const.mul (continuous_sinc.comp (by fun_prop))).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hc _) (hc _),
    integral_mul_sinc_mul, integral_mul_sinc_mul]

/-! ### The integral of the sine integral -/

/-- `t * sinc t = sin t`. -/
theorem self_mul_sinc (t : ℝ) : t * sinc t = sin t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [sinc_of_ne_zero ht]
    field_simp

/-- An antiderivative of the integral of `sinc`. -/
theorem hasDerivAt_mul_integral_sinc_add_cos (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u * (∫ v in (0 : ℝ)..u, sinc v) + cos u)
      (∫ v in (0 : ℝ)..t, sinc v) t := by
  have h1 : HasDerivAt (fun u : ℝ ↦ ∫ v in (0 : ℝ)..u, sinc v) (sinc t) t :=
    (continuous_sinc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := ((hasDerivAt_id' t).fun_mul h1).fun_add (hasDerivAt_cos t)
  refine h.congr_deriv ?_
  rw [self_mul_sinc]
  ring

/-- The sine integral `u ↦ ∫ v in 0..u, sinc v` is continuous. -/
theorem continuous_integral_sinc : Continuous fun u : ℝ ↦ ∫ v in (0 : ℝ)..u, sinc v :=
  intervalIntegral.continuous_primitive (fun _ _ ↦ continuous_sinc.intervalIntegrable _ _) 0

/-- The integral over `ζ ∈ [-1, 1]` of the integral of `sinc` up to `k (c + ζ)`. -/
theorem integral_integral_sinc_add {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    ∫ ζ in (-1 : ℝ)..1, ∫ v in (0 : ℝ)..(k * (c + ζ)), sinc v =
      (c + 1) * (∫ v in (0 : ℝ)..(k * (c + 1)), sinc v) -
        (c - 1) * (∫ v in (0 : ℝ)..(k * (c - 1)), sinc v) +
        (cos (k * (c + 1)) - cos (k * (c - 1))) / k := by
  have h1 : ∫ ζ in (-1 : ℝ)..1, ∫ v in (0 : ℝ)..(k * (c + ζ)), sinc v =
      ∫ ζ in (-1 : ℝ)..1, (fun u : ℝ ↦ ∫ v in (0 : ℝ)..u, sinc v) (k * ζ + k * c) := by
    refine intervalIntegral.integral_congr fun ζ _ ↦ ?_
    rw [show k * (c + ζ) = k * ζ + k * c by ring]
  have h2 := intervalIntegral.integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    (fun u : ℝ ↦ ∫ v in (0 : ℝ)..u, sinc v) hk (k * c)
  have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := k * -1 + k * c) (b := k * 1 + k * c)
    (fun t _ ↦ hasDerivAt_mul_integral_sinc_add_cos t)
    (continuous_integral_sinc.intervalIntegrable _ _)
  refine h1.trans (h2.trans ?_)
  rw [h3, show k * 1 + k * c = k * (c + 1) by ring, show k * -1 + k * c = k * (c - 1) by ring,
    smul_eq_mul]
  field_simp
  ring

/-- The same with `c - ζ` in place of `c + ζ`. -/
theorem integral_integral_sinc_sub {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    ∫ ζ in (-1 : ℝ)..1, ∫ v in (0 : ℝ)..(k * (c - ζ)), sinc v =
      (c + 1) * (∫ v in (0 : ℝ)..(k * (c + 1)), sinc v) -
        (c - 1) * (∫ v in (0 : ℝ)..(k * (c - 1)), sinc v) +
        (cos (k * (c + 1)) - cos (k * (c - 1))) / k := by
  rw [← integral_integral_sinc_add hk c]
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun ζ : ℝ ↦ ∫ v in (0 : ℝ)..(k * (c + ζ)), sinc v)
  simp only [neg_neg] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun ζ _ ↦ ?_
  rw [sub_eq_add_neg]

end RiemannMasullo
