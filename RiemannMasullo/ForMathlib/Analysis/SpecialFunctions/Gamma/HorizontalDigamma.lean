module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.HorizontalLogNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # First-order horizontal asymptotics of the digamma function

The secant bounds for the horizontal logarithm of Gamma first give
`Re ψ(x + it) - log x → 0`. The recurrence for `ψ` and the Taylor remainder for
the logarithm then bound the successive differences of the corrected error by
`(3 + t²) / x³`. Summing those differences gives an explicit quadratic error
for any fixed complex shift. Compare the classical expansion DLMF 5.11.2.
-/

public noncomputable section

open Filter
open scoped Topology

namespace RiemannMasullo

private def horizontalDigammaError (t x : ℝ) : ℝ :=
  (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re - Real.log x + 1 / (2 * x)

private theorem log_step_error {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (x + 1) - Real.log x - 1 / x + 1 / (2 * x ^ 2)| ≤ 2 / x ^ 3 := by
  have hpos : 0 < x := by linarith
  have hhalf : 1 / x ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hx
  have hinv : 0 < 1 / x := one_div_pos.mpr hpos
  have hh : |-(1 / x)| < 1 := by rw [abs_neg, abs_of_pos hinv]; linarith
  have H := Real.abs_log_sub_add_sum_range_le hh 2
  rw [abs_neg, abs_of_pos hinv] at H
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    Nat.cast_zero, Nat.cast_one, zero_add, add_zero, pow_one, div_one, Nat.reduceAdd] at H
  have hl : Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    rw [← Real.log_div (by positivity) hpos.ne']
    congr 1
    field_simp
  have hd : 0 < 1 - 1 / x := by linarith
  calc
    _ = |(-(1 / x) + (-(1 / x)) ^ 2 / 2) + Real.log (1 - -(1 / x))| := by
      rw [hl, sub_neg_eq_add]; congr 1; ring
    _ ≤ (1 / x) ^ 3 / (1 - 1 / x) := by simpa using H
    _ ≤ 2 / x ^ 3 := by
      rw [div_le_iff₀ hd, one_div_pow]
      have ht := mul_le_mul_of_nonneg_left (show 1 ≤ 2 * (1 - 1 / x) by linarith)
        (show 0 ≤ 1 / x ^ 3 by positivity)
      linarith [show 1 / x ^ 3 * (2 * (1 - 1 / x)) = 2 / x ^ 3 * (1 - 1 / x) by ring]

private theorem horizontalDigammaError_step (t : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    |horizontalDigammaError t x - horizontalDigammaError t (x + 1)| ≤ (3 + t ^ 2) / x ^ 3 := by
  have hp : 0 < x := by linarith
  have hp1 : 0 < x + 1 := by linarith
  have hD : 0 < x ^ 2 + t ^ 2 := by positivity
  let z : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  have hr : z.re = x := by simp [z]
  have hi : z.im = t := by simp [z]
  have hz : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n he
    have := congrArg Complex.re he
    simp only [hr, Complex.neg_re, Complex.natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hz1 : ((x + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I = z + 1 := by
    dsimp [z]; push_cast; ring
  have hn : z⁻¹.re = x / (x ^ 2 + t ^ 2) := by
    rw [Complex.inv_re, hr, Complex.normSq_apply, hr, hi]
    ring
  have hstep : horizontalDigammaError t x - horizontalDigammaError t (x + 1) =
      (Real.log (x + 1) - Real.log x - 1 / x + 1 / (2 * x ^ 2)) +
      (1 / x - x / (x ^ 2 + t ^ 2)) - 1 / (2 * x ^ 2 * (x + 1)) := by
    unfold horizontalDigammaError
    rw [hz1, Complex.digamma_apply_add_one z hz, Complex.add_re, hn]
    dsimp only [z]
    field_simp [hp.ne', hp1.ne', hD.ne']
    ring
  have he : 1 / x - x / (x ^ 2 + t ^ 2) = t ^ 2 / (x * (x ^ 2 + t ^ 2)) := by
    field_simp [hp.ne', hD.ne']; ring
  have hb : |1 / x - x / (x ^ 2 + t ^ 2)| ≤ t ^ 2 / x ^ 3 := by
    rw [he, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith [mul_nonneg hp.le (sq_nonneg t)]
  have hc : |1 / (2 * x ^ 2 * (x + 1))| ≤ 1 / x ^ 3 := by
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    nlinarith [sq_nonneg x, pow_pos hp 3]
  rw [hstep]
  calc
    _ ≤ (|Real.log (x + 1) - Real.log x - 1 / x + 1 / (2 * x ^ 2)| +
          |1 / x - x / (x ^ 2 + t ^ 2)|) + |1 / (2 * x ^ 2 * (x + 1))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (2 / x ^ 3 + t ^ 2 / x ^ 3) + 1 / x ^ 3 := by gcongr; exact log_step_error hx
    _ = _ := by ring

/-- Once the zeroth-order horizontal asymptotic is known, the Gamma recurrence
and the elementary logarithm remainder give an explicit quadratic error. -/
private theorem digamma_re_horizontal_quadratic_of_tendsto (t : ℝ)
    (hzero : Tendsto (fun x : ℝ ↦
      (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re - Real.log x) atTop (𝓝 0))
    {x : ℝ} (hx : 2 ≤ x) :
    |(Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re - Real.log x + 1 / (2*x)| ≤
      (2 * (3 + t ^ 2)) / x ^ 2 := by
  let E := horizontalDigammaError t
  let B := 2 * (3 + t ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hstep (y : ℝ) (hy : 2 ≤ y) :
      |E y - E (y+1)| ≤ B * (1/y^2 - 1/(y+1)^2) := by
    have hp : 0 < y := by linarith
    have hp1 : 0 < y+1 := by linarith
    have hh : 1 / y^3 ≤ 2 * (1 / y^2 - 1 / (y+1)^2) := by
      field_simp
      nlinarith [sq_nonneg (y-1), sq_nonneg y,
        mul_nonneg (sub_nonneg.mpr hy) (pow_nonneg hp.le 3), pow_pos hp 3]
    calc
      _ ≤ (3 + t^2) / y^3 := horizontalDigammaError_step t hy
      _ ≤ (3 + t^2) * (2 * (1/y^2 - 1/(y+1)^2)) := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 3 + t^2)
      _ = _ := by dsimp [B]; ring
  have hsum (n : ℕ) : |E x - E (x+n)| ≤ B * (1/x^2 - 1/(x+n)^2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hstep (x+n) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
      push_cast
      rw [← add_assoc]
      calc
        _ ≤ |E x - E (x+n)| + |E (x+n) - E (x+n+1)| := abs_sub_le _ _ _
        _ ≤ B*(1/x^2 - 1/(x+n)^2) + B*(1/(x+n)^2 - 1/(x+n+1)^2) := add_le_add ih hh
        _ = _ := by ring
  have hhalf : Tendsto (fun y : ℝ ↦ 1 / (2*y)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_inv_rev] using
      (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ ↦ y⁻¹) atTop (𝓝 0)).div_const 2
  have hE : Tendsto E atTop (𝓝 0) := by
    change Tendsto (fun y : ℝ ↦
      (Complex.digamma ((y : ℂ) + (t : ℂ) * Complex.I)).re - Real.log y + 1 / (2*y)) atTop _
    simpa only [zero_add] using hzero.add hhalf
  have hn : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦ |E x - E (x + n)|) atTop (𝓝 |E x|) := by
    simpa only [sub_zero, Function.comp_def] using ((hE.comp hn).const_sub (E x)).abs
  apply le_of_tendsto hlim
  refine Eventually.of_forall fun n ↦ (hsum n).trans ?_
  change B * (1/x^2 - 1/(x+n)^2) ≤ B / x^2
  rw [div_eq_mul_one_div B]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hB

private theorem tendsto_log_norm_horizontal (c : ℂ) :
    Tendsto (fun x : ℝ ↦ Real.log ‖(x : ℂ) + c‖ - Real.log x) atTop (𝓝 0) := by
  let r (x : ℝ) : ℂ := 1 + (x⁻¹ : ℝ) * c
  have hi : Tendsto (fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp tendsto_inv_atTop_zero
  have hr : Tendsto r atTop (𝓝 1) := by simpa [r] using (hi.mul_const c).const_add 1
  have hn : Tendsto (fun x : ℝ ↦ ‖r x‖) atTop (𝓝 1) := by simpa using hr.norm
  have hl : Tendsto (fun x : ℝ ↦ Real.log ‖r x‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (one_ne_zero : (1:ℝ) ≠ 0)).tendsto.comp hn
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ), hn.eventually (lt_mem_nhds zero_lt_one)]
    with x hx hrx
  have he : (x : ℂ) + c = (x : ℂ) * r x := by
    dsimp only [r]
    rw [Complex.ofReal_inv, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.ne'), one_mul]
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le, Real.log_mul hx.ne' hrx.ne']
  ring

/-- Coarse horizontal asymptotic from log-convexity of the modulus of Euler's
Gamma sequence on each fixed horizontal ray. -/
private theorem tendsto_re_digamma_horizontal_sub_log (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (Complex.digamma ((x : ℂ) + (t : ℂ)*Complex.I)).re - Real.log x)
      atTop (𝓝 0) := by
  let c := (t : ℂ) * Complex.I
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_log_norm_horizontal (c-1))
    (tendsto_log_norm_horizontal c) ?_ ?_
  · filter_upwards [eventually_gt_atTop (|t|+1)] with x hx
    have h := (HeckePoisson.gammaLine_digamma_secants t x hx).1
    have he : (x : ℂ) + (c - 1) = HeckePoisson.gammaLine t (x-1) := by
      dsimp only [HeckePoisson.gammaLine, c]; push_cast; ring
    change Real.log ‖(x:ℂ)+(c-1)‖ - Real.log x ≤ _
    rw [he]
    exact sub_le_sub_right h _
  · filter_upwards [eventually_gt_atTop (|t|+1)] with x hx
    exact sub_le_sub_right (HeckePoisson.gammaLine_digamma_secants t x hx).2 _

/-- Explicit uniform error on a fixed horizontal ray. -/
theorem digamma_re_horizontal_quadratic (t : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    |(Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re - Real.log x + 1 / (2*x)| ≤
      (2 * (3 + t ^ 2)) / x ^ 2 :=
  digamma_re_horizontal_quadratic_of_tendsto t (tendsto_re_digamma_horizontal_sub_log t) hx

private theorem log_shift_quadratic {x b : ℝ} (hx : 0 < x) (hb : 2 * |b| ≤ x) :
    |Real.log (x+b) - Real.log x - b/x| ≤ 2*b^2/x^2 := by
  have hr : |b/x| ≤ 1/2 := by rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]; linarith
  have hxb : 0 < x+b := by linarith [neg_le_abs b]
  have hl : Real.log (x+b) - Real.log x = Real.log (1+b/x) := by
    rw [← Real.log_div hxb.ne' hx.ne']; congr 1; field_simp
  have hh : |-(b/x)| < 1 := by rw [abs_neg]; linarith
  have H := Real.abs_log_sub_add_sum_range_le hh 1
  rw [abs_neg] at H
  have hd : 0 < 1 - |b/x| := by linarith
  calc
    _ = |-(b/x) + Real.log (1 - -(b/x))| := by rw [hl, sub_neg_eq_add]; congr 1; ring
    _ ≤ |b/x|^2/(1-|b/x|) := by simpa using H
    _ ≤ 2 * |b/x|^2 := by
      rw [div_le_iff₀ hd]
      nlinarith [mul_nonneg (sq_nonneg (|b/x|)) (show 0 ≤ 1 - 2 * |b/x| by linarith)]
    _ = _ := by rw [sq_abs, div_pow]; ring

/-- Explicit second-order bound for a fixed complex translation of the positive
real ray. The threshold ensures that the real part of the argument is at least two. -/
theorem digamma_re_shifted_horizontal_quadratic (c : ℂ) {x : ℝ} (hx : 4 + 2*|c.re| ≤ x) :
    |(Complex.digamma ((x : ℂ)+c)).re - Real.log x - (c.re-1/2)/x| ≤
      (8*(3+c.im^2) + 2*c.re^2 + |c.re|)/x^2 := by
  let y := x+c.re
  have hp : 0 < x := by linarith [abs_nonneg c.re]
  have hhalf : x/2 ≤ y := by dsimp [y]; linarith [neg_le_abs c.re]
  have hy : 2 ≤ y := by linarith [abs_nonneg c.re]
  have hyp : 0 < y := by linarith
  have h1 : |horizontalDigammaError c.im y| ≤ 8*(3+c.im^2)/x^2 := by
    calc
      _ ≤ 2*(3+c.im^2)/y^2 := digamma_re_horizontal_quadratic c.im hy
      _ ≤ 2*(3+c.im^2)/(x/2)^2 := by gcongr
      _ = _ := by ring
  have h2 : |Real.log y - Real.log x - c.re/x| ≤ 2*c.re^2/x^2 :=
    log_shift_quadratic hp (by linarith)
  have h3 : |1/(2*x) - 1/(2*y)| ≤ |c.re|/x^2 := by
    have he : 1/(2*x) - 1/(2*y) = c.re/(2*x*y) := by
      field_simp [hp.ne', hyp.ne']; dsimp [y]; ring
    rw [he, abs_div, abs_of_pos (by positivity : 0 < 2*x*y)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hp)
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hhalf)]
  have hxy : (y : ℂ) + (c.im : ℂ)*Complex.I = (x : ℂ)+c := by
    dsimp only [y]; rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
  have he : (Complex.digamma ((x : ℂ)+c)).re - Real.log x - (c.re-1/2)/x =
      horizontalDigammaError c.im y + (Real.log y - Real.log x - c.re/x) +
        (1/(2*x) - 1/(2*y)) := by
    unfold horizontalDigammaError
    rw [hxy]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  calc
    _ ≤ (|horizontalDigammaError c.im y| + |Real.log y - Real.log x - c.re/x|) +
        |1/(2*x)-1/(2*y)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (8*(3+c.im^2)/x^2 + 2*c.re^2/x^2) + |c.re|/x^2 :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- The scaled archimedean contribution for a fixed complex shift and positive real scale. -/
theorem tendsto_mul_re_digamma_scaled_sub_log (c : ℂ) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun a : ℝ ↦ a * ((Complex.digamma ((k * a : ℝ) + c)).re - Real.log (k * a)))
      atTop (𝓝 ((c.re - 1 / 2) / k)) := by
  let B := 8 * (3 + c.im ^ 2) + 2 * c.re ^ 2 + |c.re|
  let d := c.re - 1 / 2
  let f (x : ℝ) := (Complex.digamma ((x : ℂ) + c)).re - Real.log x
  have hzero : Tendsto (fun x : ℝ ↦ x * f x - d) atTop (𝓝 0) := by
    have hbound : Tendsto (fun x : ℝ ↦ B * x⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).const_mul B
    apply squeeze_zero_norm' _ hbound
    filter_upwards [eventually_ge_atTop (4 + 2 * |c.re|)] with x hx
    have hp : 0 < x := by linarith [abs_nonneg c.re]
    have he : x * f x - d = x * (f x - d / x) := by field_simp
    rw [he, norm_mul, Real.norm_of_nonneg hp.le, Real.norm_eq_abs]
    have hquad : |f x - d / x| ≤ B / x ^ 2 := digamma_re_shifted_horizontal_quadratic c hx
    exact (mul_le_mul_of_nonneg_left hquad hp.le).trans_eq (by field_simp)
  have hlim : Tendsto (fun x : ℝ ↦ x * f x) atTop (𝓝 d) := by
    simpa only [sub_add_cancel, zero_add] using hzero.add_const d
  have hscale : Tendsto (fun a : ℝ ↦ k * a) atTop atTop := tendsto_id.const_mul_atTop hk
  apply ((hlim.comp hscale).div_const k).congr
  intro a
  change k * a * _ / k = _
  field_simp
  rfl

end RiemannMasullo
