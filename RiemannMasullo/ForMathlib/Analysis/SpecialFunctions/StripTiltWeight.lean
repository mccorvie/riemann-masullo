module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # The tilt mixture weight of a strip

For `α > 0` and `β ≥ 0` the function

`stripTiltWeight α β x = ∫ σ in (-α)..α, exp (2 * σ * x) * (α - |σ|) ^ β`

is the density, in a logarithmic variable `x`, of the mixture over `σ ∈ [-α, α]` of the
exponentially tilted weights `exp (2 * σ * x)`, taken with the boundary weight `(α - |σ|) ^ β`.

The main result, `stripTiltWeight_comparable`, says that it is comparable, uniformly in `x`,
to `max (exp (-(2 * α * x))) (exp (2 * α * x)) * (1 + x ^ 2) ^ (-(β + 1) / 2)`: the larger
endpoint weight, damped by the power of `x` that the vanishing of `(α - |σ|) ^ β` at the
endpoints produces. `stripTiltWeight_sum_pow_comparable` is the form with the polynomial
factor `∑ j ≤ k, x ^ (2 * j)`, which turns the exponent `-(β + 1) / 2` into `s / 2` when
`β = 2 * k - 1 - s`.

The proof folds `[-α, α]` onto `[0, α]` by the distance to the boundary and rescales the
resulting Laplace integral of `t ^ β` to frequency one. These steps are adapted from the proof
of `stripDirichletWeight_comparable` in pull request #7471, which treats the exponent `1 - s`.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory

namespace RiemannMasullo

/-- The tilt mixture weight of the strip `|σ| < α` with boundary exponent `β`: the integral
over `σ ∈ [-α, α]` of the exponential tilt `exp (2 * σ * x)` against `(α - |σ|) ^ β`. -/
def stripTiltWeight (α β x : ℝ) : ℝ :=
  ∫ σ in (-α)..α, exp (2 * σ * x) * (α - |σ|) ^ β

/-- The defining formula of `stripTiltWeight`. -/
theorem stripTiltWeight_def (α β x : ℝ) :
    stripTiltWeight α β x = ∫ σ in (-α)..α, exp (2 * σ * x) * (α - |σ|) ^ β :=
  rfl

/-- For `0 ≤ β` the integrand of `stripTiltWeight` is continuous in `σ`. -/
theorem continuous_stripTiltWeight_integrand {β : ℝ} (hβ : 0 ≤ β) (α x : ℝ) :
    Continuous fun σ : ℝ ↦ exp (2 * σ * x) * (α - |σ|) ^ β :=
  ((continuous_const.mul continuous_id).mul continuous_const).rexp.mul
    ((continuous_const.sub continuous_abs).rpow_const fun _ ↦ Or.inr hβ)

/-- For `0 ≤ β` the integrand of `stripTiltWeight` is interval integrable on every interval. -/
theorem intervalIntegrable_stripTiltWeight_integrand {β : ℝ} (hβ : 0 ≤ β) (α x a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ ↦ exp (2 * σ * x) * (α - |σ|) ^ β) volume a b :=
  (continuous_stripTiltWeight_integrand hβ α x).intervalIntegrable a b

/-- For `0 ≤ β` the tilt mixture weight is continuous in `x`. -/
theorem continuous_stripTiltWeight {β : ℝ} (hβ : 0 ≤ β) (α : ℝ) :
    Continuous (stripTiltWeight α β) := by
  have h : Continuous (Function.uncurry fun x σ : ℝ ↦ exp (2 * σ * x) * (α - |σ|) ^ β) :=
    ((continuous_const.mul continuous_snd).mul continuous_fst).rexp.mul
      ((continuous_const.sub continuous_snd.abs).rpow_const fun _ ↦ Or.inr hβ)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h (-α) α

/-- The tilt mixture weight is even in `x`. -/
theorem stripTiltWeight_neg (α β x : ℝ) :
    stripTiltWeight α β (-x) = stripTiltWeight α β x := by
  have h := intervalIntegral.integral_comp_neg (a := -α) (b := α)
    (f := fun σ : ℝ ↦ exp (2 * σ * x) * (α - |σ|) ^ β)
  rw [neg_neg] at h
  rw [stripTiltWeight_def, stripTiltWeight_def, ← h]
  refine intervalIntegral.integral_congr fun σ _ ↦ ?_
  simp only [abs_neg]
  congr 2
  ring

/-- For `0 < α` and `0 ≤ β` the tilt mixture weight is positive. -/
theorem stripTiltWeight_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (x : ℝ) :
    0 < stripTiltWeight α β x := by
  refine intervalIntegral.integral_pos (by linarith)
    (continuous_stripTiltWeight_integrand hβ α x).continuousOn (fun σ hσ ↦ ?_)
    ⟨0, ⟨by linarith, hα.le⟩, ?_⟩
  · exact mul_nonneg (exp_pos _).le
      (rpow_nonneg (sub_nonneg.mpr (abs_le.mpr ⟨hσ.1.le, hσ.2⟩)) _)
  · simpa using rpow_pos_of_pos hα β

/-- Folding `[-α, α]` onto `[0, α]` by the distance `t = α - |σ|` to the boundary: the tilt
mixture weight is `exp (2 * α * x)` times a two-sided Laplace integral of `t ^ β`. -/
private theorem stripTiltWeight_eq_factor {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : ℝ) :
    stripTiltWeight α β x = exp (2 * α * x) *
      ∫ t in (0 : ℝ)..α, (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ β := by
  let g (σ : ℝ) := exp (2 * σ * x) * (α - |σ|) ^ β
  have hg : Continuous g := continuous_stripTiltWeight_integrand hβ α x
  have ha : (∫ σ in -α..(0 : ℝ), g σ) = ∫ t in (0 : ℝ)..α, g (t - α) := by
    rw [intervalIntegral.integral_comp_sub_right, zero_sub, sub_self]
  have hb : (∫ σ in (0 : ℝ)..α, g σ) = ∫ t in (0 : ℝ)..α, g (α - t) := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have hleft : IntervalIntegrable (fun t ↦ g (t - α)) volume 0 α :=
    (hg.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun t ↦ g (α - t)) volume 0 α :=
    (hg.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  change (∫ σ in -α..α, g σ) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (-α) 0)
    (hg.intervalIntegrable 0 α), ha, hb, ← intervalIntegral.integral_add hleft hright,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le hα] at ht
  dsimp only [g]
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonneg (sub_nonneg.mpr ht.2)]
  simp only [show α - -(t - α) = t by ring, show α - (α - t) = t by ring]
  rw [← add_mul, ← mul_assoc, mul_add, ← exp_add, ← exp_add]
  have h₁ : 2 * α * x + -2 * x * t = 2 * (α - t) * x := by ring
  have h₂ : 2 * α * x + -2 * x * (2 * α - t) = 2 * (t - α) * x := by ring
  rw [h₁, h₂, add_comm]

/-- For `0 ≤ x` the two-sided Laplace integral lies between the one-sided one and twice it. -/
private theorem stripTiltWeight_laplace_compare {α β x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..α, t ^ β * exp (-2 * x * t)) ≤
        (∫ t in (0 : ℝ)..α, (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ β) ∧
      (∫ t in (0 : ℝ)..α, (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ β) ≤
        2 * ∫ t in (0 : ℝ)..α, t ^ β * exp (-2 * x * t) := by
  have hp : Continuous fun t : ℝ ↦ t ^ β := continuous_id.rpow_const fun _ ↦ Or.inr hβ
  have he : Continuous fun t : ℝ ↦ exp (-2 * x * t) := (continuous_const.mul continuous_id).rexp
  have he' : Continuous fun t : ℝ ↦ exp (-2 * x * (2 * α - t)) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).rexp
  have hfI := (hp.mul he).intervalIntegrable (μ := volume) 0 α
  have hgI := ((he.add he').mul hp).intervalIntegrable (μ := volume) 0 α
  constructor
  · refine intervalIntegral.integral_mono_on hα hfI hgI fun t ht ↦ ?_
    rw [mul_comm (t ^ β)]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (exp_pos _).le)
      (rpow_nonneg ht.1 _)
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hα hgI (hfI.const_mul 2) fun t ht ↦ ?_
    have hE : exp (-2 * x * (2 * α - t)) ≤ exp (-2 * x * t) :=
      exp_le_exp.mpr (by nlinarith [mul_nonneg hx (sub_nonneg.mpr ht.2)])
    have hp₀ : 0 ≤ t ^ β := rpow_nonneg ht.1 _
    calc (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ β
        ≤ (exp (-2 * x * t) + exp (-2 * x * t)) * t ^ β :=
          mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hE) hp₀
      _ = 2 * (t ^ β * exp (-2 * x * t)) := by ring

/-- Rescaling the one-sided Laplace integral of `t ^ β` to frequency one. -/
private theorem stripTiltWeight_laplace_scale {α β x : ℝ} (hα : 0 ≤ α) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..α, t ^ β * exp (-2 * x * t)) =
      (x ^ (β + 1))⁻¹ * ∫ t in (0 : ℝ)..(x * α), t ^ β * exp (-2 * t) := by
  have hp : x ^ β ≠ 0 := (rpow_pos_of_pos hx _).ne'
  have he : (∫ t in (0 : ℝ)..α, t ^ β * exp (-2 * x * t)) =
      (x ^ β)⁻¹ * ∫ t in (0 : ℝ)..α, (fun u : ℝ ↦ u ^ β * exp (-2 * u)) (x * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hα] at ht
    dsimp only
    rw [Real.mul_rpow hx.le ht.1, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hp, one_mul,
      mul_assoc]
  rw [he, intervalIntegral.integral_comp_mul_left (fun u : ℝ ↦ u ^ β * exp (-2 * u)) hx.ne',
    mul_zero, smul_eq_mul, ← mul_assoc, rpow_add_one hx.ne', mul_inv]

/-- The one-sided Laplace integral of `t ^ β` over `[0, α]` at frequency `2 * x`, `0 ≤ x`,
is comparable to `(1 + x ^ 2) ^ (-(β + 1) / 2)`. -/
private theorem stripTiltWeight_laplace_bounds {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ x : ℝ, 0 ≤ x →
      l * (1 + x ^ 2) ^ (-(β + 1) / 2) ≤ (∫ t in (0 : ℝ)..α, t ^ β * exp (-2 * x * t)) ∧
      (∫ t in (0 : ℝ)..α, t ^ β * exp (-2 * x * t)) ≤ u * (1 + x ^ 2) ^ (-(β + 1) / 2) := by
  let f (x t : ℝ) := t ^ β * exp (-2 * x * t)
  have hfc (x : ℝ) : Continuous (f x) :=
    (continuous_id.rpow_const fun _ ↦ Or.inr hβ).mul (continuous_const.mul continuous_id).rexp
  have hf (x b : ℝ) : IntervalIntegrable (f x) volume 0 b := (hfc x).intervalIntegrable _ _
  have hn (x t : ℝ) (ht : 0 ≤ t) : 0 ≤ f x t := mul_nonneg (rpow_nonneg ht _) (exp_pos _).le
  have hanti (x y : ℝ) (hxy : x ≤ y) :
      (∫ t in (0 : ℝ)..α, f y t) ≤ ∫ t in (0 : ℝ)..α, f x t := by
    refine intervalIntegral.integral_mono_on hα.le (hf y α) (hf x α) fun t ht ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hxy ht.1]))
      (rpow_nonneg ht.1 _)
  have hf₁ : f 1 = fun t : ℝ ↦ t ^ β * exp (-2 * t) := by
    funext t
    simp only [f, mul_one]
  let L := ∫ t in (0 : ℝ)..α, f 1 t
  have hL : 0 < L := by
    refine intervalIntegral.integral_pos hα (hfc 1).continuousOn
      (fun t ht ↦ hn 1 t ht.1.le) ⟨α, ⟨hα.le, le_rfl⟩, ?_⟩
    exact mul_pos (rpow_pos_of_pos hα _) (exp_pos _)
  let U := ∫ t in Ioi (0 : ℝ), f 1 t
  have hU₀ : IntegrableOn (f 1) (Ioi (0 : ℝ)) := by
    rw [hf₁]
    simpa only [rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := β) (b := 2)
        (by linarith) (by norm_num) (by norm_num))
  have hcompare (b : ℝ) (hb : 0 ≤ b) : (∫ t in (0 : ℝ)..b, f 1 t) ≤ U := by
    rw [intervalIntegral.integral_of_le hb]
    exact setIntegral_mono_set hU₀
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht ↦ hn 1 t ht.le))
      (Filter.Eventually.of_forall fun _ ht ↦ ht.1)
  have hU : 0 < U := hL.trans_le (hcompare α hα.le)
  let B := ∫ t in (0 : ℝ)..α, f 0 t
  have hLB : L ≤ B := hanti 0 1 zero_le_one
  have hB : 0 < B := hL.trans_le hLB
  have hq : 0 < (β + 1) / 2 := by linarith
  have hneg (x : ℝ) : (1 + x ^ 2) ^ (-(β + 1) / 2) = ((1 + x ^ 2) ^ ((β + 1) / 2))⁻¹ := by
    rw [neg_div, rpow_neg (by positivity)]
  have htwo : 0 < (2 : ℝ) ^ ((β + 1) / 2) := rpow_pos_of_pos two_pos _
  refine ⟨L, 2 ^ ((β + 1) / 2) * (B + U), hL, by positivity, fun x hx ↦ ?_⟩
  change _ ≤ (∫ t in (0 : ℝ)..α, f x t) ∧ (∫ t in (0 : ℝ)..α, f x t) ≤ _
  have hbase : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hP : 0 < (1 + x ^ 2) ^ ((β + 1) / 2) := rpow_pos_of_pos (by linarith) _
  rw [hneg x]
  by_cases hx₁ : x ≤ 1
  · have hP₁ : 1 ≤ (1 + x ^ 2) ^ ((β + 1) / 2) := one_le_rpow hbase hq.le
    have hP₂ : (1 + x ^ 2) ^ ((β + 1) / 2) ≤ 2 ^ ((β + 1) / 2) :=
      rpow_le_rpow (by linarith) (by nlinarith) hq.le
    constructor
    · calc L * ((1 + x ^ 2) ^ ((β + 1) / 2))⁻¹ ≤ L * 1 :=
            mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hP₁) hL.le
        _ = L := mul_one L
        _ ≤ _ := hanti x 1 hx₁
    · calc (∫ t in (0 : ℝ)..α, f x t) ≤ B := hanti 0 x hx
        _ ≤ B + U := by linarith
        _ = 1 * (B + U) := (one_mul _).symm
        _ ≤ 2 ^ ((β + 1) / 2) * ((1 + x ^ 2) ^ ((β + 1) / 2))⁻¹ * (B + U) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← div_eq_mul_inv, le_div_iff₀ hP, one_mul]
          exact hP₂
        _ = _ := by ring
  · have h₁x : 1 ≤ x := (le_of_not_ge hx₁)
    have hx' : 0 < x := by linarith
    have hQ : 0 < x ^ (β + 1) := rpow_pos_of_pos hx' _
    have he : (x ^ 2) ^ ((β + 1) / 2) = x ^ (β + 1) := by
      rw [← rpow_natCast, ← rpow_mul hx'.le]
      congr 1
      push_cast
      ring
    have hQP : x ^ (β + 1) ≤ (1 + x ^ 2) ^ ((β + 1) / 2) := by
      rw [← he]
      exact rpow_le_rpow (by positivity) (by linarith) hq.le
    have hPQ : (1 + x ^ 2) ^ ((β + 1) / 2) ≤ 2 ^ ((β + 1) / 2) * x ^ (β + 1) := by
      rw [← he, ← mul_rpow zero_le_two (sq_nonneg x)]
      exact rpow_le_rpow (by positivity) (by nlinarith) hq.le
    have hscale : (∫ t in (0 : ℝ)..α, f x t) =
        (x ^ (β + 1))⁻¹ * ∫ t in (0 : ℝ)..(x * α), f 1 t := by
      rw [hf₁]
      exact stripTiltWeight_laplace_scale hα.le hx'
    have hL' : L ≤ ∫ t in (0 : ℝ)..(x * α), f 1 t := by
      have hspan : α ≤ x * α := by nlinarith
      rw [← intervalIntegral.integral_add_adjacent_intervals (hf 1 α)
        ((hfc 1).intervalIntegrable α (x * α))]
      exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hspan
        fun t ht ↦ hn 1 t (hα.le.trans ht.1))
    have hU' : (∫ t in (0 : ℝ)..(x * α), f 1 t) ≤ U := hcompare (x * α) (by positivity)
    rw [hscale]
    constructor
    · calc L * ((1 + x ^ 2) ^ ((β + 1) / 2))⁻¹
          ≤ L * (x ^ (β + 1))⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hQ hQP) hL.le
        _ = (x ^ (β + 1))⁻¹ * L := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hL' (inv_pos.mpr hQ).le
    · calc (x ^ (β + 1))⁻¹ * ∫ t in (0 : ℝ)..(x * α), f 1 t
          ≤ (x ^ (β + 1))⁻¹ * (B + U) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_pos.mpr hQ).le
        _ ≤ 2 ^ ((β + 1) / 2) * ((1 + x ^ 2) ^ ((β + 1) / 2))⁻¹ * (B + U) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← div_eq_mul_inv, le_div_iff₀ hP, inv_mul_le_iff₀ hQ, mul_comm]
          exact hPQ
        _ = _ := by ring

/-- For `0 < α` and `0 ≤ β` the tilt mixture weight is comparable, uniformly in `x`, to the
larger endpoint weight times `(1 + x ^ 2) ^ (-(β + 1) / 2)`. The constants depend on `α` and
`β` only. -/
theorem stripTiltWeight_comparable {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x : ℝ,
      c * (max (exp (-(2 * α * x))) (exp (2 * α * x)) * (1 + x ^ 2) ^ (-(β + 1) / 2)) ≤
        stripTiltWeight α β x ∧
      stripTiltWeight α β x ≤
        C * (max (exp (-(2 * α * x))) (exp (2 * α * x)) * (1 + x ^ 2) ^ (-(β + 1) / 2)) := by
  obtain ⟨l, u, hl, hu, h⟩ := stripTiltWeight_laplace_bounds hα hβ
  have hpos (x : ℝ) (hx : 0 ≤ x) :
      l * (exp (2 * α * x) * (1 + x ^ 2) ^ (-(β + 1) / 2)) ≤ stripTiltWeight α β x ∧
        stripTiltWeight α β x ≤
          2 * u * (exp (2 * α * x) * (1 + x ^ 2) ^ (-(β + 1) / 2)) := by
    obtain ⟨h₁, h₂⟩ := stripTiltWeight_laplace_compare hα.le hβ hx
    obtain ⟨h₃, h₄⟩ := h x hx
    have hE : 0 ≤ exp (2 * α * x) := (exp_pos _).le
    rw [stripTiltWeight_eq_factor hα.le hβ]
    constructor
    · calc l * (exp (2 * α * x) * (1 + x ^ 2) ^ (-(β + 1) / 2))
          = exp (2 * α * x) * (l * (1 + x ^ 2) ^ (-(β + 1) / 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (h₃.trans h₁) hE
    · calc exp (2 * α * x) *
            ∫ t in (0 : ℝ)..α, (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ β
          ≤ exp (2 * α * x) * (2 * (u * (1 + x ^ 2) ^ (-(β + 1) / 2))) :=
            mul_le_mul_of_nonneg_left
              (h₂.trans (mul_le_mul_of_nonneg_left h₄ zero_le_two)) hE
        _ = _ := by ring
  have hall (x : ℝ) :
      l * (max (exp (-(2 * α * x))) (exp (2 * α * x)) * (1 + x ^ 2) ^ (-(β + 1) / 2)) ≤
        stripTiltWeight α β x ∧
      stripTiltWeight α β x ≤ 2 * u *
        (max (exp (-(2 * α * x))) (exp (2 * α * x)) * (1 + x ^ 2) ^ (-(β + 1) / 2)) := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_right (exp_le_exp.mpr (by nlinarith [mul_nonneg hα.le hx]))]
      exact hpos x hx
    · have hx' : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
      rw [max_eq_left (exp_le_exp.mpr (by nlinarith [mul_nonneg hα.le hx'])),
        ← stripTiltWeight_neg α β x]
      have he : -(2 * α * x) = 2 * α * (-x) := by ring
      simpa only [he, neg_sq] using hpos (-x) hx'
  refine ⟨l, 2 * u, hl, ?_, hall⟩
  have hw : 0 < max (exp (-(2 * α * 0))) (exp (2 * α * 0)) *
      (1 + (0 : ℝ) ^ 2) ^ (-(β + 1) / 2) := by positivity
  exact le_of_mul_le_mul_right ((hall 0).1.trans (hall 0).2) hw

/-- For `0 ≤ y` the partial geometric sum `∑ j ≤ k, y ^ j` is at most `(1 + y) ^ k`. -/
private theorem stripTiltWeight_sum_pow_le (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), y ^ j ≤ (1 + y) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ (1 + y) k]
    have h : y ^ (k + 1) ≤ (1 + y) ^ k * y := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy (by linarith) k) hy
    nlinarith

/-- For `0 ≤ y`, `(1 + y) ^ k` is at most `2 ^ k` times the partial geometric sum
`∑ j ≤ k, y ^ j`. -/
private theorem stripTiltWeight_le_sum_pow (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    (1 + y) ^ k ≤ 2 ^ k * ∑ j ∈ Finset.range (k + 1), y ^ j := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      y ^ j ≤ ∑ i ∈ Finset.range (k + 1), y ^ i :=
    Finset.single_le_sum (f := fun i ↦ y ^ i) (fun i _ ↦ pow_nonneg hy i) hj
  rcases le_total y 1 with h | h
  · calc (1 + y) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * y ^ 0 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hterm 0 (by simp)) (by positivity)
  · calc (1 + y) ^ k ≤ (2 * y) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * y ^ k := mul_pow 2 y k
      _ ≤ _ := mul_le_mul_of_nonneg_left (hterm k (by simp)) (by positivity)

/-- The tilt mixture weight with the polynomial factor `∑ j ≤ k, x ^ (2 * j)`: when
`β = 2 * k - 1 - s` is nonnegative, the product is comparable, uniformly in `x`, to the
larger endpoint weight times the Sobolev factor `(1 + x ^ 2) ^ (s / 2)`. The constants
depend on `α`, `β` and `k` only. -/
theorem stripTiltWeight_sum_pow_comparable {α β s : ℝ} {k : ℕ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hs : β = 2 * k - 1 - s) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x : ℝ,
      c * (max (exp (2 * (-α) * x)) (exp (2 * α * x)) * (1 + x ^ 2) ^ (s / 2)) ≤
        (∑ j ∈ Finset.range (k + 1), x ^ (2 * j)) * stripTiltWeight α β x ∧
      (∑ j ∈ Finset.range (k + 1), x ^ (2 * j)) * stripTiltWeight α β x ≤
        C * (max (exp (2 * (-α) * x)) (exp (2 * α * x)) * (1 + x ^ 2) ^ (s / 2)) := by
  obtain ⟨c, C, hc, hcC, h⟩ := stripTiltWeight_comparable hα hβ
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨c / 2 ^ k, C, by positivity,
    (div_le_self hc.le (one_le_pow₀ one_le_two)).trans hcC, fun x ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := h x
  have hE : exp (2 * (-α) * x) = exp (-(2 * α * x)) := by
    congr 1
    ring
  have hS : ∑ j ∈ Finset.range (k + 1), x ^ (2 * j) =
      ∑ j ∈ Finset.range (k + 1), (x ^ 2) ^ j := by
    simp only [pow_mul]
  have hpow : (1 + x ^ 2) ^ (s / 2) = (1 + x ^ 2) ^ k * (1 + x ^ 2) ^ (-(β + 1) / 2) := by
    rw [← rpow_natCast (1 + x ^ 2) k, ← rpow_add (by positivity)]
    congr 1
    rw [hs]
    ring
  have hS₀ : 0 ≤ ∑ j ∈ Finset.range (k + 1), (x ^ 2) ^ j :=
    Finset.sum_nonneg fun j _ ↦ by positivity
  have hup := stripTiltWeight_sum_pow_le (x ^ 2) (sq_nonneg x) k
  have hlow : (1 + x ^ 2) ^ k / 2 ^ k ≤ ∑ j ∈ Finset.range (k + 1), (x ^ 2) ^ j :=
    (div_le_iff₀' h2k).mpr (stripTiltWeight_le_sum_pow (x ^ 2) (sq_nonneg x) k)
  rw [hE, hS, hpow]
  constructor
  · calc c / 2 ^ k * (max (exp (-(2 * α * x))) (exp (2 * α * x)) *
          ((1 + x ^ 2) ^ k * (1 + x ^ 2) ^ (-(β + 1) / 2)))
        = (1 + x ^ 2) ^ k / 2 ^ k * (c * (max (exp (-(2 * α * x))) (exp (2 * α * x)) *
            (1 + x ^ 2) ^ (-(β + 1) / 2))) := by ring
      _ ≤ _ := mul_le_mul hlow h₁ (by positivity) hS₀
  · calc (∑ j ∈ Finset.range (k + 1), (x ^ 2) ^ j) * stripTiltWeight α β x
        ≤ (1 + x ^ 2) ^ k * (C * (max (exp (-(2 * α * x))) (exp (2 * α * x)) *
            (1 + x ^ 2) ^ (-(β + 1) / 2))) :=
          mul_le_mul hup h₂ (stripTiltWeight_pos hα hβ x).le (by positivity)
      _ = _ := by ring

end RiemannMasullo
