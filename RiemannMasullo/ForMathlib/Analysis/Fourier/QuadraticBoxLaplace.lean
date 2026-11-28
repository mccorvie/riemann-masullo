module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Laplace products of uniform intervals with quadratic radii

The radius of the first interval is one half. Indices in the Lean statements start at zero.
-/

open Filter MeasureTheory
open scoped BigOperators Topology Interval

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The box radii whose first `N` terms sum to `1 - 1 / (N + 1)`. -/
def quadraticBoxRadius (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem quadraticBoxRadius_pos (n : ℕ) : 0 < quadraticBoxRadius n := by
  unfold quadraticBoxRadius
  positivity

theorem sum_range_quadraticBoxRadius (N : ℕ) :
    ∑ n ∈ Finset.range N, quadraticBoxRadius n = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, quadraticBoxRadius, Nat.cast_succ]
    have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
    have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    field_simp
    ring

/-- The total support radius of the independent sum is one. -/
theorem hasSum_quadraticBoxRadius : HasSum quadraticBoxRadius 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ (quadraticBoxRadius_pos n).le)]
  simp only [sum_range_quadraticBoxRadius]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The bilateral Laplace transform of the uniform probability on the real interval `[-1,1]`. -/
def unitIntervalLaplaceFactor (z : ℂ) : ℂ :=
  (∫ x in (-1 : ℝ)..1, Complex.exp (z * x)) / 2

@[simp] theorem unitIntervalLaplaceFactor_zero : unitIntervalLaplaceFactor 0 = 1 := by
  norm_num [unitIntervalLaplaceFactor, intervalIntegral.integral_const]

private theorem unitIntervalLaplaceFactor_eq {z : ℂ} (hz : z ≠ 0) :
    unitIntervalLaplaceFactor z = (Complex.exp z - Complex.exp (-z)) / z / 2 := by
  rw [unitIntervalLaplaceFactor, integral_exp_mul_complex hz]
  simp

private theorem abs_le_one_of_mem_box {x : ℝ} (hx : x ∈ Set.uIoc (-1 : ℝ) 1) :
    |x| ≤ 1 := by
  rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  exact abs_le.mpr ⟨hx.1.le, hx.2⟩

/-- The elementary strip bound from the integral over the uniform interval. -/
theorem norm_unitIntervalLaplaceFactor_le (z : ℂ) :
    ‖unitIntervalLaplaceFactor z‖ ≤ Real.exp |z.re| := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ ↦ Complex.exp (z * x)) (a := -1) (b := 1) (C := Real.exp |z.re|)
    (fun x hx ↦ by
      rw [Complex.norm_exp, show (z * (x : ℂ)).re = z.re * x by simp]
      apply Real.exp_le_exp.mpr
      calc
        z.re * x ≤ |z.re * x| := le_abs_self _
        _ = |z.re| * |x| := abs_mul _ _
        _ ≤ |z.re| * 1 := mul_le_mul_of_nonneg_left (abs_le_one_of_mem_box hx) (abs_nonneg _)
        _ = |z.re| := mul_one _)
  rw [unitIntervalLaplaceFactor, norm_div]
  norm_num at hb ⊢
  linarith

/-- In the high-frequency range the oscillating interval contributes an extra factor one half. -/
theorem norm_unitIntervalLaplaceFactor_le_half {z : ℂ} (him : 2 ≤ |z.im|) :
    ‖unitIntervalLaplaceFactor z‖ ≤ Real.exp |z.re| / 2 := by
  have hnorm : 2 ≤ ‖z‖ := him.trans (Complex.abs_im_le_norm _)
  have hz : z ≠ 0 := by rintro rfl; norm_num at him
  have he : ‖Complex.exp z - Complex.exp (-z)‖ ≤ 2 * Real.exp |z.re| := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
    linarith [Real.exp_le_exp.mpr (le_abs_self z.re),
      Real.exp_le_exp.mpr (neg_le_abs z.re)]
  rw [unitIntervalLaplaceFactor_eq hz, norm_div, norm_div]
  norm_num
  apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)).mpr
  apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnorm (Real.exp_pos |z.re|).le]

/-- Each individual normalized interval transform is zero-free off the imaginary axis. -/
theorem unitIntervalLaplaceFactor_ne_zero {z : ℂ} (hz : z.re ≠ 0) :
    unitIntervalLaplaceFactor z ≠ 0 := by
  have h : z ≠ 0 := fun hz' ↦ hz (by simp [hz'])
  rw [unitIntervalLaplaceFactor_eq h]
  refine div_ne_zero (div_ne_zero (sub_ne_zero.mpr ?_) h) (by norm_num)
  intro heq
  have hnorm := congrArg (fun w : ℂ ↦ ‖w‖) heq
  simp only [Complex.norm_exp, Complex.neg_re, Real.exp_eq_exp] at hnorm
  exact hz (by linarith)

/-- The unit-box factor approaches one at the origin at least linearly in norm. -/
theorem norm_unitIntervalLaplaceFactor_sub_one {z : ℂ} (hsmall : ‖z‖ ≤ 1) :
    ‖unitIntervalLaplaceFactor z - 1‖ ≤ 2 * ‖z‖ := by
  let f : ℝ → ℂ := fun x ↦ Complex.exp (z * x)
  have hsubst : unitIntervalLaplaceFactor z - 1 =
      (∫ x in (-1 : ℝ)..1, (f x - 1)) / 2 := by
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous f).intervalIntegrable ..)
      (intervalIntegrable_const)]
    simp [f, unitIntervalLaplaceFactor, intervalIntegral.integral_const]
    ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ ↦ f x - 1) (a := -1) (b := 1) (C := 2 * ‖z‖)
    (fun x hx ↦ by
      have hzx : ‖z * (x : ℂ)‖ ≤ ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa using mul_le_mul_of_nonneg_left (abs_le_one_of_mem_box hx) (norm_nonneg z)
      exact (Complex.norm_exp_sub_one_le (hzx.trans hsmall)).trans (by linarith))
  rw [hsubst, norm_div]
  norm_num at hb ⊢
  linarith

/-- The explicit entire product defining the transform of the quadratic-width box law. -/
def quadraticBoxLaplace (z : ℂ) : ℂ :=
  ∏' n : ℕ, unitIntervalLaplaceFactor ((quadraticBoxRadius n : ℂ) * z)

private theorem summable_norm_quadraticBox_deviation (z : ℂ) :
    Summable fun n : ℕ ↦ ‖unitIntervalLaplaceFactor ((quadraticBoxRadius n : ℂ) * z) - 1‖ := by
  have hr := hasSum_quadraticBoxRadius.summable
  have ht := hr.tendsto_atTop_zero.mul_const ‖z‖
  have ht' : Tendsto (fun n ↦ quadraticBoxRadius n * ‖z‖) atTop (𝓝 0) := by simpa using ht
  have hs := ht'.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  apply (hr.mul_left (2 * ‖z‖)).of_norm_bounded_eventually_nat
  filter_upwards [hs] with n hn
  have hnorm : ‖(quadraticBoxRadius n : ℂ) * z‖ = quadraticBoxRadius n * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (quadraticBoxRadius_pos n)]
  have hh := norm_unitIntervalLaplaceFactor_sub_one (z := (quadraticBoxRadius n : ℂ) * z)
    (hnorm.trans_le hn)
  rw [Real.norm_of_nonneg (norm_nonneg _), hnorm] at *
  linarith

/-- The normalized interval factors have a convergent unordered product. -/
theorem multipliable_quadraticBoxLaplace (z : ℂ) :
    Multipliable fun n : ℕ ↦ unitIntervalLaplaceFactor ((quadraticBoxRadius n : ℂ) * z) := by
  simpa using multipliable_one_add_of_summable (summable_norm_quadraticBox_deviation z)

/-- The transform of the quadratic-width box law is nonzero throughout both open half-planes. -/
theorem quadraticBoxLaplace_ne_zero {z : ℂ} (hz : z.re ≠ 0) : quadraticBoxLaplace z ≠ 0 := by
  let f (n : ℕ) := unitIntervalLaplaceFactor ((quadraticBoxRadius n : ℂ) * z)
  have hfactor (n : ℕ) : (1 : ℂ) + (f n - 1) ≠ 0 := by
    rw [show (1 : ℂ) + (f n - 1) = f n by ring]
    apply unitIntervalLaplaceFactor_ne_zero
    simpa using mul_ne_zero (quadraticBoxRadius_pos n).ne' hz
  simpa [f, quadraticBoxLaplace] using
    tprod_one_add_ne_zero_of_summable hfactor (summable_norm_quadraticBox_deviation z)

@[simp] theorem quadraticBoxLaplace_zero : quadraticBoxLaplace 0 = 1 := by
  simp [quadraticBoxLaplace]

private theorem quadraticBoxRadius_two_le (t : ℝ) (n : ℕ)
    (hn : n < ⌊Real.sqrt |t| / 2⌋₊) : 2 ≤ quadraticBoxRadius n * |t| := by
  have hfloor := Nat.floor_le (show 0 ≤ Real.sqrt |t| / 2 by positivity)
  have hcast : (n : ℝ) + 1 ≤ (⌊Real.sqrt |t| / 2⌋₊ : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hn
  have hside : 2 * ((n : ℝ) + 1) ≤ Real.sqrt |t| := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ((n : ℝ) + 1)) hside 2
  have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have hnum : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ |t| := by
    nlinarith [Real.sq_sqrt (abs_nonneg t), sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  rw [quadraticBoxRadius, one_div_mul_eq_div]
  exact (le_div_iff₀ hden).2 hnum

/-- Quadratically decreasing interval radii yield square-root exponential decay of a convergent
product when each factor gains one half above twice its reciprocal radius. -/
private theorem norm_tprod_le_exp_neg_sqrt_of_quadraticBoxRadius (B t : ℝ) (hB : 0 ≤ B) (f : ℕ → ℂ) (hf : Multipliable f)
    (hbound : ∀ n, ‖f n‖ ≤ Real.exp (B * quadraticBoxRadius n))
    (hhalf : ∀ n, 2 ≤ quadraticBoxRadius n * |t| → ‖f n‖ ≤ Real.exp (B * quadraticBoxRadius n) / 2) :
    ‖∏' n, f n‖ ≤ 2 * Real.exp B * Real.exp (-(Real.log 2 / 2) * Real.sqrt |t|) := by
  let N := ⌊Real.sqrt |t| / 2⌋₊
  let discount (n : ℕ) : ℝ := if n < N then Real.log 2 else 0
  have hfactor (n : ℕ) : ‖f n‖ ≤ Real.exp (B * quadraticBoxRadius n - discount n) := by
    by_cases hn : n < N
    · simpa [discount, hn, Real.exp_sub, Real.exp_log (by norm_num : 0 < (2 : ℝ))] using
        hhalf n (quadraticBoxRadius_two_le t n hn)
    · simpa [discount, hn] using hbound n
  have hdisc {m : ℕ} (hm : N ≤ m) : ∑ n ∈ Finset.range m, discount n = N * Real.log 2 := by
    have heq : ∑ n ∈ Finset.range N, discount n = ∑ n ∈ Finset.range m, discount n :=
      Finset.sum_subset (Finset.range_mono hm) fun n _ hn ↦ by
        simp only [Finset.mem_range] at hn
        simp [discount, hn]
    rw [← heq]
    calc
      ∑ n ∈ Finset.range N, discount n = ∑ _n ∈ Finset.range N, Real.log 2 :=
        Finset.sum_congr rfl fun n hn ↦ by simp [discount, Finset.mem_range.mp hn]
      _ = N * Real.log 2 := by simp
  have hprod : ‖∏' n, f n‖ ≤ Real.exp (B - N * Real.log 2) := by
    apply le_of_tendsto hf.tendsto_prod_tprod_nat.norm
    filter_upwards [eventually_ge_atTop N] with m hm
    calc
      ‖∏ n ∈ Finset.range m, f n‖ = ∏ n ∈ Finset.range m, ‖f n‖ := norm_prod _ _
      _ ≤ ∏ n ∈ Finset.range m, Real.exp (B * quadraticBoxRadius n - discount n) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun n _ ↦ hfactor n)
      _ = Real.exp (B * (∑ n ∈ Finset.range m, quadraticBoxRadius n) - N * Real.log 2) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hdisc hm]
      _ ≤ Real.exp (B - N * Real.log 2) := by
        apply Real.exp_le_exp.2
        exact sub_le_sub_right (by simpa using
          mul_le_mul_of_nonneg_left (show ∑ n ∈ Finset.range m, quadraticBoxRadius n ≤ 1 by
            rw [sum_range_quadraticBoxRadius]; exact sub_le_self _ (by positivity)) hB) _
  have hfloor : Real.sqrt |t| / 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    ‖∏' n, f n‖ ≤ Real.exp (B - N * Real.log 2) := hprod
    _ ≤ Real.exp (Real.log 2 + B + (-(Real.log 2 / 2) * Real.sqrt |t|)) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hlog (sub_nonneg.mpr hfloor.le)]
    _ = 2 * Real.exp B * Real.exp (-(Real.log 2 / 2) * Real.sqrt |t|) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : 0 < (2 : ℝ))]

/-- The quadratic-width box product has Gevrey-two decay on every closed vertical strip.
The exponential rate is absolute. Only the prefactor depends on the strip. -/
theorem norm_quadraticBoxLaplace_le (z : ℂ) :
    ‖quadraticBoxLaplace z‖ ≤
      2 * Real.exp |z.re| * Real.exp (-(Real.log 2 / 2) * Real.sqrt |z.im|) := by
  apply norm_tprod_le_exp_neg_sqrt_of_quadraticBoxRadius |z.re| z.im (abs_nonneg _)
    _ (multipliable_quadraticBoxLaplace z)
  · intro n
    simpa [Complex.mul_re, abs_mul, abs_of_pos (quadraticBoxRadius_pos n), mul_comm] using
      norm_unitIntervalLaplaceFactor_le ((quadraticBoxRadius n : ℂ) * z)
  · intro n hn
    have him : 2 ≤ |((quadraticBoxRadius n : ℂ) * z).im| := by
      simpa [Complex.mul_im, abs_mul, abs_of_pos (quadraticBoxRadius_pos n)] using hn
    simpa [Complex.mul_re, abs_mul, abs_of_pos (quadraticBoxRadius_pos n), mul_comm] using
      norm_unitIntervalLaplaceFactor_le_half him

private theorem quadraticBox_factor_lower (z : ℂ) :
    |z.re| / ‖z‖ ≤ ‖(Complex.exp z - Complex.exp (-z)) / z / 2‖ := by
  have hr := Real.self_le_sinh_iff.mpr (abs_nonneg z.re)
  rw [← Real.abs_sinh, Real.sinh_eq, abs_div] at hr
  norm_num at hr
  have hnorm := abs_norm_sub_norm_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at hnorm
  rw [norm_div, norm_div]
  norm_num
  calc
    |z.re| / ‖z‖ ≤ (‖Complex.exp z - Complex.exp (-z)‖ / 2) / ‖z‖ :=
      div_le_div_of_nonneg_right (by linarith) (norm_nonneg z)
    _ = _ := by ring

private theorem quadraticBox_exp_remainder (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 / 3 := by
  have h := Complex.exp_bound' (x := z) (n := 3) (by norm_num; linarith)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  convert h using 1
  ring

private theorem quadraticBox_factor_deviation (z : ℂ) (hz : z ≠ 0) (hsmall : ‖z‖ ≤ 1) :
    ‖(Complex.exp z - Complex.exp (-z)) / z / 2 - 1‖ ≤ ‖z‖ ^ 2 / 3 := by
  let E (u : ℂ) := Complex.exp u - (1 + u + u ^ 2 / 2)
  have hE (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖E u‖ ≤ ‖u‖ ^ 3 / 3 :=
    quadraticBox_exp_remainder u hu
  have ha := hE z hsmall
  have hb := hE (-z) (by simpa using hsmall)
  rw [norm_neg] at hb
  have heq : (Complex.exp z - Complex.exp (-z)) / z / 2 - 1 = (E z - E (-z)) / z / 2 := by
    dsimp [E]
    field_simp
    ring
  rw [heq, norm_div, norm_div]
  norm_num
  calc
    ‖E z - E (-z)‖ / ‖z‖ / 2 ≤ (2 * (‖z‖ ^ 3 / 3)) / ‖z‖ / 2 := by
      gcongr
      linarith [norm_sub_le (E z) (E (-z))]
    _ = _ := by
      field_simp [norm_ne_zero_iff.mpr hz]

private theorem quadraticBox_exp_neg_two_le {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    Real.exp (-(2 * u)) ≤ 1 - u := by
  have hp : 0 < 1 + 2 * u := by linarith
  calc
    Real.exp (-(2 * u)) = 1 / Real.exp (2 * u) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + 2 * u) := one_div_le_one_div_of_le hp (by linarith [Real.add_one_le_exp (2 * u)])
    _ ≤ 1 - u := (div_le_iff₀ hp).mpr (by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu')])

private theorem quadraticBox_factor_tail (z : ℂ) (hz : z ≠ 0) (hsmall : ‖z‖ ≤ 1) :
    Real.exp (-(‖z‖ ^ 2)) ≤ ‖(Complex.exp z - Complex.exp (-z)) / z / 2‖ := by
  have hd := quadraticBox_factor_deviation z hz hsmall
  have hrev := norm_sub_norm_le (1 : ℂ) ((Complex.exp z - Complex.exp (-z)) / z / 2)
  rw [norm_one, norm_sub_rev] at hrev
  have hs : ‖z‖ ^ 2 ≤ 1 := by nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hsmall)]
  have he := quadraticBox_exp_neg_two_le (u := ‖z‖ ^ 2 / 2) (by positivity) (by linarith)
  rw [show 2 * (‖z‖ ^ 2 / 2) = ‖z‖ ^ 2 by ring] at he
  linarith [sq_nonneg ‖z‖]

private theorem quadraticBox_tail_square_step (x : ℝ) (hx : 0 < x) :
    (1 / (x * (x + 1))) ^ 2 ≤ 1 / (3 * x ^ 3) - 1 / (3 * (x + 1) ^ 3) := by
  have heq :
      1 / (3 * x ^ 3) - 1 / (3 * (x + 1) ^ 3) - (1 / (x * (x + 1))) ^ 2 =
        1 / (3 * x ^ 3 * (x + 1) ^ 3) := by
    field_simp
    ring
  exact sub_nonneg.mp (heq.symm ▸ (show 0 ≤ 1 / (3 * x ^ 3 * (x + 1) ^ 3) by positivity))

private theorem quadraticBox_sum_tail_squares (r : ℕ → ℝ)
    (hr : ∀ n, r n = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) (N k : ℕ) :
    ∑ i ∈ Finset.range k, r (N + i) ^ 2 ≤
      1 / (3 * ((N : ℝ) + 1) ^ 3) - 1 / (3 * (((N + k : ℕ) : ℝ) + 1) ^ 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hstep := quadraticBox_tail_square_step (((N + k : ℕ) : ℝ) + 1) (by positivity)
    rw [hr]
    simp only [Nat.cast_add, Nat.cast_succ] at ih hstep ⊢
    rw [show (N : ℝ) + k + 1 + 1 = N + k + 2 by ring] at hstep
    rw [show (N : ℝ) + (k + 1) + 1 = N + k + 2 by ring]
    linarith

/-- On a bounded complex window the transform is uniformly bounded away from zero
once the real part is separated from the imaginary axis. The exponential accounts for
all the intervals after the first ceiling of the square root of the window radius. -/
theorem quadraticBoxLaplace_lower_on_box {w : ℂ} {d R : ℝ} (hd : 0 < d)
    (hdw : d ≤ |w.re|) (hwR : ‖w‖ ≤ R) (hR : 1 ≤ R) :
    (d / R) ^ ⌈Real.sqrt R⌉₊ * Real.exp (-(Real.sqrt R / 3)) ≤ ‖quadraticBoxLaplace w‖ := by
  let r := quadraticBoxRadius
  let N := ⌈Real.sqrt R⌉₊
  let f (n : ℕ) := unitIntervalLaplaceFactor ((r n : ℂ) * w)
  have hr (n : ℕ) : r n = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := rfl
  have hw : w ≠ 0 := by
    intro heq
    simp [heq] at hdw
    linarith
  have hRp : 0 < R := by linarith
  have hrp (n : ℕ) : 0 < r n := quadraticBoxRadius_pos n
  have hh (n : ℕ) : (r n : ℂ) * w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (hrp n).ne') hw
  have hnorm (n : ℕ) : ‖(r n : ℂ) * w‖ = r n * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hrp n)]
  have hhead (n : ℕ) : d / R ≤ ‖f n‖ := by
    have hbound := quadraticBox_factor_lower ((r n : ℂ) * w)
    rw [← unitIntervalLaplaceFactor_eq (hh n), hnorm] at hbound
    simp only [Complex.re_ofReal_mul, abs_mul, abs_of_pos (hrp n)] at hbound
    calc
      d / R ≤ |w.re| / R := div_le_div_of_nonneg_right hdw hRp.le
      _ ≤ |w.re| / ‖w‖ := div_le_div_of_nonneg_left (abs_nonneg w.re) (norm_pos_iff.mpr hw) hwR
      _ = r n * |w.re| / (r n * ‖w‖) := by field_simp [(hrp n).ne']
      _ ≤ ‖f n‖ := hbound
  have hceil : Real.sqrt R ≤ (N : ℝ) := Nat.le_ceil _
  have hsq : R ≤ (N : ℝ) ^ 2 := by
    simpa [Real.sq_sqrt hRp.le] using pow_le_pow_left₀ (Real.sqrt_nonneg R) hceil 2
  have htail (n : ℕ) (hn : N ≤ n) : Real.exp (-(R ^ 2 * (r n) ^ 2)) ≤ ‖f n‖ := by
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    have hbound : R ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
      refine hsq.trans ?_
      rw [pow_two]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have hsmall : ‖(r n : ℂ) * w‖ ≤ 1 := by
      rw [hnorm, hr, one_div_mul_eq_div]
      exact (div_le_iff₀ hden).mpr (by simpa using hwR.trans hbound)
    have h := quadraticBox_factor_tail ((r n : ℂ) * w) (hh n) hsmall
    rw [← unitIntervalLaplaceFactor_eq (hh n), hnorm] at h
    refine le_trans (Real.exp_le_exp.mpr ?_) h
    have hwr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwR 2) (sq_nonneg (r n))
    nlinarith
  have hfirst : (d / R) ^ N ≤ ∏ n ∈ Finset.range N, ‖f n‖ := by
    simpa only [Finset.prod_const, Finset.card_range] using Finset.prod_le_prod₀
      (s := Finset.range N) (f := fun _ ↦ d / R) (g := fun n ↦ ‖f n‖)
      (fun _ _ ↦ div_nonneg hd.le hRp.le) (fun n _ ↦ hhead n)
  have hRsum : R ^ 2 / (3 * ((N : ℝ) + 1) ^ 3) ≤ Real.sqrt R / 3 := by
    have hcube := pow_le_pow_left₀ (Real.sqrt_nonneg R) (show Real.sqrt R ≤ (N : ℝ) + 1 by linarith) 3
    have h4 : R ^ 2 = Real.sqrt R * Real.sqrt R ^ 3 := by
      conv_lhs => rw [← Real.sq_sqrt hRp.le]
      ring
    rw [div_le_iff₀ (by positivity : 0 < 3 * ((N : ℝ) + 1) ^ 3), h4]
    linarith [mul_le_mul_of_nonneg_left hcube (Real.sqrt_nonneg R)]
  have hlast (k : ℕ) : Real.exp (-(Real.sqrt R / 3)) ≤
      ∏ i ∈ Finset.range k, ‖f (N + i)‖ := by
    have hs := quadraticBox_sum_tail_squares r hr N k
    have hss : ∑ i ∈ Finset.range k, r (N + i) ^ 2 ≤ 1 / (3 * ((N : ℝ) + 1) ^ 3) :=
      hs.trans (sub_le_self _ (by positivity))
    calc
      Real.exp (-(Real.sqrt R / 3)) ≤ Real.exp (-(R ^ 2 * ∑ i ∈ Finset.range k, r (N + i) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hss (sq_nonneg R)
        rw [mul_one_div] at h
        linarith
      _ = ∏ i ∈ Finset.range k, Real.exp (-(R ^ 2 * r (N + i) ^ 2)) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
      _ ≤ ∏ i ∈ Finset.range k, ‖f (N + i)‖ :=
        Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) (fun i _ ↦ htail _ (Nat.le_add_right N i))
  apply ge_of_tendsto (multipliable_quadraticBoxLaplace w).tendsto_prod_tprod_nat.norm
  filter_upwards [eventually_ge_atTop N] with m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  change (d / R) ^ N * Real.exp (-(Real.sqrt R / 3)) ≤ ‖∏ n ∈ Finset.range (N + k), f n‖
  rw [Finset.prod_range_add, norm_mul, norm_prod, norm_prod]
  exact mul_le_mul hfirst (hlast k) (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

end RiemannMasullo
