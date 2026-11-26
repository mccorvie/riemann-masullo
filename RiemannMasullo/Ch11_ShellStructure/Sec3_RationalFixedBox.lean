module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Tactic
public import Mathlib.Topology.Sequences
public import RiemannMasullo.ForMathlib.Analysis.Fourier.LpSpace

/-! # Genuine rational fixed-box logarithmic stages

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. In the rational trivial-angular
integer-indicator channel, the stages are actual real Schwartz theta images
with both polar constraints, finite principal-value differences and input band
`X / ∏ p`. Scaled Poisson gives one common fixed support at the output. Finite
Euler differences give bounded Mellin tests on the Hilbert closures, so the
nested fixed-box stages have zero intersection as the prime mesh shrinks.
This module does not identify the closed quotient with the orbital cardinal
mode span or assert bounds for basis lifts. -/

public noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate FourierTransform InnerProductSpace SchwartzMap Topology

namespace RiemannMasullo.RationalPacket

/-- Rational theta sum for the integer-indicator finite test, on the positive norm ray.
The integer zero contributes nothing on polar sources. -/
def theta (f : 𝓢(ℝ, ℂ)) (r : ℝ) : ℂ := ∑' n : ℤ, f ((n : ℝ) * r)

/-- Pull back an actual real Schwartz source by positive multiplicative dilation. -/
def dilate (r : ℝ) (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 r hr.ne')) f

@[simp] theorem dilate_apply (r : ℝ) (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilate r hr f x = f (r*x) := by
  simp [dilate, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, mul_comm]

/-- The real Fourier band rescales by `r`, with the inverse Haar factor. -/
theorem fourier_dilate {r : ℝ} (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (s : ℝ) :
    (𝓕 (dilate r hr f)) s = r⁻¹ • (𝓕 f) (s/r) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let h (x : ℝ) := Complex.exp (↑(-2 * Real.pi * x * (s/r)) * Complex.I) • f x
  have hcalc (x : ℝ) :
      Complex.exp (↑(-2 * Real.pi * x * s) * Complex.I) • dilate r hr f x = h (r*x) := by
    rw [dilate_apply]
    dsimp only [h]
    congr 3
    field_simp
  simp_rw [hcalc]
  simpa [h, abs_of_pos hr] using Measure.integral_comp_mul_left h r

/-- Exact scaled real Poisson summation for the rational theta profile. -/
theorem theta_eq_poisson (f : 𝓢(ℝ, ℂ)) {r : ℝ} (hr : 0 < r) :
    theta f r = (r⁻¹ : ℝ) • (∑' n : ℤ, (𝓕 f) ((n : ℝ) / r)) := by
  have hp := (dilate r hr f).tsum_eq_tsum_fourier 0
  simp only [zero_add, AddCircle.coe_zero, fourier_eval_zero, mul_one, dilate_apply,
    fourier_dilate hr, Complex.real_smul, tsum_mul_left] at hp
  simpa only [theta, mul_comm r, Complex.real_smul] using hp

/-- The polar theta profile of a compact Fourier band vanishes below its
reciprocal radius. This uses absence of the zero Fourier term, not signed cancellation. -/
theorem theta_eq_zero_of_lt {f : 𝓢(ℝ, ℂ)} {X r : ℝ} (hr : 0 < r)
    (h0 : (𝓕 f) 0 = 0) (hsupp : ∀ y : ℝ, X < |y| → (𝓕 f) y = 0)
    (hsmall : r * X < 1) : theta f r = 0 := by
  rw [theta_eq_poisson f hr]
  have hterm (n : ℤ) : (𝓕 f) ((n : ℝ) / r) = 0 := by
    by_cases hn : n = 0
    · simpa [hn] using h0
    · apply hsupp
      rw [abs_div, abs_of_pos hr, lt_div_iff₀ hr, mul_comm]
      exact hsmall.trans_le (by exact_mod_cast Int.one_le_abs hn)
  simp [hterm]


private theorem theta_term_bound (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0)
    {r : ℝ} (hr : 0 < r) (n : ℤ) :
    ‖f ((n : ℝ) * r)‖ ≤ (SchwartzMap.seminorm ℝ 2 0 f / r ^ 2) *
      (1 / (n : ℝ) ^ 2) := by
  by_cases hn : n = 0
  · simp [hn, h0]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnr : 0 < (n : ℝ) ^ 2 * r ^ 2 :=
      mul_pos (sq_pos_of_ne_zero hnR) (sq_pos_of_ne_zero hr.ne')
    have h := f.norm_pow_mul_le_seminorm ℝ 2 ((n : ℝ)*r)
    rw [Real.norm_eq_abs, sq_abs, mul_pow, mul_comm _ ‖f _‖] at h
    convert (le_div_iff₀ hnr).2 h using 1
    field_simp

private theorem theta_term_summable (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0)
    {r : ℝ} (hr : 0 < r) : Summable (fun n : ℤ ↦ f ((n : ℝ) * r)) := by
  have hs := Real.summable_one_div_int_pow.mpr (show 1 < (2 : ℕ) by decide)
  exact (hs.mul_left (SchwartzMap.seminorm ℝ 2 0 f / r ^ 2)).of_norm_bounded
    (theta_term_bound f h0 hr)

private theorem theta_bound (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {r : ℝ} (hr : 0 < r) :
    ‖theta f r‖ ≤ (SchwartzMap.seminorm ℝ 2 0 f * (∑' n : ℤ, 1 / (n : ℝ) ^ 2)) / r ^ 2 := by
  have hs := Real.summable_one_div_int_pow.mpr (show 1 < (2 : ℕ) by decide)
  have h := tsum_of_norm_bounded ((hs.mul_left (SchwartzMap.seminorm ℝ 2 0 f / r ^ 2)).hasSum)
    (theta_term_bound f h0 hr)
  rw [tsum_mul_left] at h
  simpa only [theta, div_mul_eq_mul_div] using h

private theorem measurable_theta_exp_scale (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {a : ℝ}
    (ha : 0 < a) : Measurable (fun x : ℝ ↦ theta f (Real.exp x * a)) := by
  apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset ℤ))
    (f := fun (s : Finset ℤ) x ↦ ∑ n ∈ s, f ((n : ℝ) * (Real.exp x * a)))
  · intro s
    exact Finset.measurable_sum s (fun n _ ↦ (f.continuous.comp
      (continuous_const.mul (Real.continuous_exp.mul continuous_const))).measurable)
  · exact tendsto_pi_nhds.mpr (fun x ↦ (theta_term_summable f h0
      (mul_pos (Real.exp_pos x) ha)).hasSum)

private theorem theta_sub (f g : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (hg : g 0 = 0)
    {r : ℝ} (hr : 0 < r) : theta (f-g) r = theta f r - theta g r := by
  simpa only [theta, sub_apply] using
    (theta_term_summable f hf hr).tsum_sub (theta_term_summable g hg hr)

private theorem theta_dilate {p : ℝ} (hp : 0 < p) (f : 𝓢(ℝ, ℂ)) (r : ℝ) :
    theta (dilate p hp f) r = theta f (p*r) := by
  unfold theta
  congr 1
  funext n
  rw [dilate_apply]
  congr 1
  ring

/-- The half-twisted rational theta profile after the finite principal-value
product. Expand the product into its signed subset sum on the true log ray. -/
def stage (T : Finset ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) * ∑ U ∈ T.powerset,
    (-1 : ℂ) ^ U.card * theta f (Real.exp x * ∏ p ∈ U, (p : ℝ))

/-- A positive real dilation translates the log profile and rescales its half twist. -/
theorem stage_dilate_real (T : Finset ℕ) {r : ℝ} (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    stage T (dilate r hr f) x =
      (Real.exp (-(Real.log r)/2) : ℂ) * stage T f (x + Real.log r) := by
  have hexp : (Real.exp (-(Real.log r)/2) : ℂ) *
      (Real.exp ((x + Real.log r)/2) : ℂ) = (Real.exp (x/2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  unfold stage
  rw [← mul_assoc, hexp]
  simp only [theta_dilate hr, Real.exp_add, Real.exp_log hr, mul_left_comm, mul_comm]

theorem stage_add (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) (f g : 𝓢(ℝ, ℂ))
    (hf : f 0 = 0) (hg : g 0 = 0) (x : ℝ) :
    stage T (f+g) x = stage T f x + stage T g x := by
  unfold stage
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  let a := Real.exp x * ∏ p ∈ U, (p : ℝ)
  have ha : 0 < a := mul_pos (Real.exp_pos _) (Finset.prod_pos fun p hp ↦ by
    exact_mod_cast zero_lt_one.trans_le (hT p ((Finset.mem_powerset.mp hU) hp)))
  have he : theta (f+g) a = theta f a + theta g a := by
    simpa only [theta, add_apply] using
      (theta_term_summable f hf ha).tsum_add (theta_term_summable g hg ha)
  rw [he, mul_add]

theorem stage_smul (T : Finset ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    stage T (c • f) x = c • stage T f x := by
  have he (a : ℝ) : theta (c • f) a = c * theta f a := by
    simp only [theta, smul_apply, smul_eq_mul, tsum_mul_left]
  unfold stage
  simp only [he, smul_eq_mul]
  simp_rw [mul_left_comm ((-1 : ℂ) ^ _), ← Finset.mul_sum, mul_left_comm c]

@[simp] theorem stage_zero (T : Finset ℕ) (x : ℝ) : stage T 0 x = 0 := by
  simp only [stage, theta, zero_apply, tsum_zero, mul_zero, Finset.sum_const_zero]

/-- Adding a prime to the rational stage applies its actual principal-value
dilation difference to the half-twisted profile. -/
theorem stage_insert (T : Finset ℕ) {p : ℕ} (hp : 0 < p) (hmem : p ∉ T)
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    stage (insert p T) f x =
      stage T f x - (Real.exp (-(Real.log p)/2) : ℂ) * stage T f (x + Real.log p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hterm (U : Finset ℕ) (hU : U ∈ T.powerset) :
      (-1 : ℂ) ^ (insert p U).card *
        theta f (Real.exp x * ∏ q ∈ insert p U, (q : ℝ)) =
      -((-1 : ℂ) ^ U.card * theta f (Real.exp (x+Real.log p) * ∏ q ∈ U, (q : ℝ))) := by
    have hpu : p ∉ U := fun h ↦ hmem (Finset.mem_powerset.mp hU h)
    rw [Finset.card_insert_of_notMem hpu, pow_succ, Finset.prod_insert hpu,
      Real.exp_add, Real.exp_log hpR, mul_assoc (Real.exp x)]
    ring
  have hexp : (Real.exp (-(Real.log p)/2) : ℂ) *
      (Real.exp ((x+Real.log p)/2) : ℂ) = (Real.exp (x/2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  unfold stage
  rw [Finset.sum_powerset_insert hmem, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib,
    ← mul_assoc, hexp]
  ring

/-- A single new finite-place factor can be moved back to an actual difference
of real Schwartz sources, before theta summation. -/
theorem stage_difference_dilate (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
    {p : ℕ} (hp : 0 < p) (hmem : p ∉ T) (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (x : ℝ) :
    stage T (f - dilate (p : ℝ) (by exact_mod_cast hp) f) x = stage (insert p T) f x := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let P (U : Finset ℕ) : ℝ := ∏ q ∈ U, (q : ℝ)
  have hpositive (U : Finset ℕ) (hU : U ⊆ T) : 0 < P U :=
    Finset.prod_pos fun q hq ↦ by exact_mod_cast zero_lt_one.trans_le (hT q (hU hq))
  let g := dilate (p : ℝ) hpR f
  have hg : g 0 = 0 := by simp [g, hf]
  have hterm (U : Finset ℕ) (hU : U ∈ T.powerset) :
      (-1 : ℂ) ^ U.card * theta (f-g) (Real.exp x * P U) =
        (-1 : ℂ) ^ U.card * theta f (Real.exp x * P U) -
        (-1 : ℂ) ^ U.card * theta f (Real.exp (x+Real.log p) * P U) := by
    rw [theta_sub f g hf hg (mul_pos (Real.exp_pos x) (hpositive U (Finset.mem_powerset.mp hU))),
      mul_sub]
    dsimp only [g]
    rw [theta_dilate hpR, Real.exp_add, Real.exp_log hpR]
    congr 3
    ring
  have hexp : (Real.exp (-(Real.log p)/2) : ℂ) *
      (Real.exp ((x+Real.log p)/2) : ℂ) = (Real.exp (x/2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [stage_insert T hp hmem f x]
  change stage T (f-g) x = _
  unfold stage
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← mul_assoc, hexp, mul_sub]

/-- Undo the half twist in the Mellin pairing on the imaginary axis. -/
def dampedStage (T : Finset ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (-x/2) : ℂ) * stage T f x

/-- The new principal-value factor contributes its exact Fourier multiplier
to the damped log profile. The Fourier argument is minus the Mellin argument
divided by `2π`. -/
theorem fourier_dampedStage_insert (T : Finset ℕ) {p : ℕ} (hp : 0 < p) (hmem : p ∉ T)
    (f : 𝓢(ℝ, ℂ)) (hi : Integrable (dampedStage T f)) (ξ : ℝ) :
    𝓕 (dampedStage (insert p T) f) ξ =
      (1 - (Real.fourierChar (Real.log p * ξ) : ℂ)) * 𝓕 (dampedStage T f) ξ := by
  let g := dampedStage T f
  let l := Real.log (p : ℝ)
  let g' (x : ℝ) := g (x+l)
  have hg' : Integrable g' := hi.comp_add_right l
  have hd : dampedStage (insert p T) f = fun x ↦ g x - g' x := by
    funext x
    have hExp : (Real.exp (-x/2) : ℂ) * (Real.exp (-l/2) : ℂ) =
        (Real.exp (-(x+l)/2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    simp only [dampedStage, stage_insert T hp hmem, g, g', l, mul_sub]
    rw [← mul_assoc, hExp]
  have hFourier (u : ℝ → ℂ) (hu : Integrable u) :
      Integrable (fun x ↦ Real.fourierChar (-(x * ξ)) • u x) := by
    have hc : Continuous (fun x : ℝ ↦ (Real.fourierChar (-(x*ξ)) : ℂ)) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        ((continuous_id.mul continuous_const).neg))
    simpa only [Circle.smul_def, smul_eq_mul] using
      hu.bdd_mul hc.aestronglyMeasurable (ae_of_all _ (fun x ↦ (Circle.norm_coe
        (Real.fourierChar (-(x*ξ)))).le))
  have hshift : 𝓕 g' ξ = Real.fourierChar (l*ξ) • 𝓕 g ξ := by
    let k (x : ℝ) := Real.fourierChar (-(x*ξ)) • g x
    have he (x : ℝ) : Real.fourierChar (-(x*ξ)) • g' x =
        Real.fourierChar (l*ξ) • k (x+l) := by
      dsimp only [g', k]
      rw [← mul_smul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [Real.fourier_real_eq]
    simp_rw [he]
    simp only [Circle.smul_def, smul_eq_mul]
    rw [integral_const_mul, integral_add_right_eq_self]
    rw [Real.fourier_real_eq]
  calc
    _ = 𝓕 g ξ - 𝓕 g' ξ := by
      rw [hd]
      simp only [Real.fourier_real_eq, smul_sub]
      exact integral_sub (hFourier g hi) (hFourier g' hg')
    _ = _ := by rw [hshift, Circle.smul_def, smul_eq_mul, sub_mul, one_mul]

/-- For a prime added to the stage, the true damped profile has zero Fourier
values on the entire orbital mesh `ℤ / log p`. -/
theorem fourier_dampedStage_zero_on_mesh (T : Finset ℕ) {p : ℕ} (hp : 1 < p)
    (hmem : p ∉ T) (f : 𝓢(ℝ, ℂ)) (hi : Integrable (dampedStage T f)) (j : ℤ) :
    𝓕 (dampedStage (insert p T) f) ((j : ℝ) / Real.log p) = 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hℓ := (Real.log_pos hpR).ne'
  have hcancel : Real.log (p : ℝ) * ((j : ℝ) / Real.log p) = (j : ℝ) := by
    field_simp
  rw [fourier_dampedStage_insert T (zero_lt_one.trans hp) hmem f hi, hcancel,
    Real.fourierChar_apply]
  have hphase : Complex.exp (↑(2 * Real.pi * (j : ℝ)) * Complex.I) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I j using 2
    push_cast
    ring
  rw [hphase, sub_self, zero_mul]

/-- Paper: (11.3.1.3), p. 494. In the rational integer-tail channel the
shrinking real input band `X / ∏ p` keeps the same output support `[−log X,∞)`
at every stage after applying the earlier principal values. -/
theorem stage_eq_zero_before_box {f : 𝓢(ℝ, ℂ)} {X x : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hprimes : ∀ p ∈ T, 1 ≤ p) (h0 : (𝓕 f) 0 = 0)
    (hsupp : ∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0)
    (hx : x < -Real.log X) : stage T f x = 0 := by
  let P (S : Finset ℕ) : ℝ := ∏ p ∈ S, (p : ℝ)
  have hP (S : Finset ℕ) (hS : S ⊆ T) : 0 < P S :=
    Finset.prod_pos fun p hp ↦ by exact_mod_cast (zero_lt_one.trans_le (hprimes p (hS hp)))
  have hx' : Real.exp x * X < 1 := by
    rw [← lt_div_iff₀ hX, one_div, ← Real.exp_log hX, ← Real.exp_neg]
    exact Real.exp_lt_exp.mpr hx
  unfold stage
  suffices hsum : (∑ U ∈ T.powerset, (-1 : ℂ) ^ U.card * theta f (Real.exp x * P U)) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro U hU
  have hu : U ⊆ T := Finset.mem_powerset.mp hU
  have hp_le : P U ≤ P T :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hu
      (by intro p hp; positivity)
      (by intro p hp _; exact_mod_cast hprimes p hp)
  have hmul : (Real.exp x * P U) * (X / P T) < 1 := by
    calc
      _ ≤ (Real.exp x * P T) * (X / P T) := by gcongr
      _ = Real.exp x * X := by field_simp [(hP T fun _ h ↦ h).ne']
      _ < 1 := hx'
  rw [theta_eq_zero_of_lt (mul_pos (Real.exp_pos _) (hP U hu)) h0 hsupp hmul, mul_zero]

private theorem dampedStage_eq_sum (T : Finset ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dampedStage T f x = ∑ U ∈ T.powerset, (-1 : ℂ) ^ U.card *
      theta f (Real.exp x * ∏ p ∈ U, (p : ℝ)) := by
  unfold dampedStage stage
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, show -x/2+x/2 = 0 by ring,
    Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem measurable_dampedStage (T : Finset ℕ) (hT : ∀ p ∈ T, 1 ≤ p)
    (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) : Measurable (dampedStage T f) := by
  rw [show dampedStage T f = _ from funext (dampedStage_eq_sum T f)]
  apply Finset.measurable_sum
  intro U hU
  apply Measurable.const_mul
  apply measurable_theta_exp_scale f h0
  exact Finset.prod_pos fun p hp ↦ by exact_mod_cast zero_lt_one.trans_le (hT p ((Finset.mem_powerset.mp hU) hp))

private theorem dampedStage_abs_bound (T : Finset ℕ) (hT : ∀ p ∈ T, 1 ≤ p)
    (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖dampedStage T f x‖ ≤ C * Real.exp (-2*x) := by
  let c := SchwartzMap.seminorm ℝ 2 0 f * (∑' n : ℤ, 1 / (n : ℝ) ^ 2)
  have hc : 0 ≤ c := mul_nonneg (apply_nonneg ..) (tsum_nonneg fun _ ↦ by positivity)
  refine ⟨(T.powerset.card : ℝ) * c, by positivity, fun x ↦ ?_⟩
  rw [dampedStage_eq_sum]
  calc
    _ ≤ ∑ U ∈ T.powerset, ‖(-1 : ℂ) ^ U.card *
        theta f (Real.exp x * ∏ p ∈ U, (p : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ T.powerset, c * Real.exp (-2*x) := by
      apply Finset.sum_le_sum
      intro U hU
      let a : ℝ := ∏ p ∈ U, (p : ℝ)
      have ha : 1 ≤ a := Finset.one_le_prod₀ fun p hp ↦ by
        exact_mod_cast hT p ((Finset.mem_powerset.mp hU) hp)
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      change ‖theta f (Real.exp x * a)‖ ≤ _
      have he : c / (Real.exp x)^2 = c * Real.exp (-2*x) := by
        rw [show -2*x = -(x+x) by ring, Real.exp_neg, Real.exp_add, ← pow_two, div_eq_mul_inv]
      rw [← he]
      refine (theta_bound f h0 (mul_pos (Real.exp_pos x) (zero_lt_one.trans_le ha))).trans ?_
      apply div_le_div_of_nonneg_left hc (by positivity)
      have h := le_mul_of_one_le_right (Real.exp_pos x).le ha
      exact pow_le_pow_left₀ (Real.exp_pos x).le h 2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]

private theorem integrable_of_supported_exp {F : Type*} [NormedAddCommGroup F]
    {g : ℝ → F} (hg : AEStronglyMeasurable g volume) {a β C : ℝ} (hβ : β < 0)
    (hs : ∀ x < a, g x = 0) (hb : ∀ x, ‖g x‖ ≤ C * Real.exp (β*x)) :
    Integrable g volume := by
  have hi : Integrable ((Ioi (a-1)).indicator (fun x : ℝ ↦ C * Real.exp (β*x))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 ((integrableOn_exp_mul_Ioi hβ (a-1)).const_mul C)
  apply hi.mono' hg
  filter_upwards with x
  by_cases hx : x ∈ Ioi (a-1)
  · rw [indicator_of_mem hx]
    exact hb x
  · have hxa : x < a := by
      have hn : ¬ a - 1 < x := hx
      exact (not_lt.mp hn).trans_lt (by linarith)
    rw [indicator_of_notMem hx, hs x hxa, norm_zero]

/-- The actual log theta stages lie in L², and their Mellin pairing at
the imaginary line is an honest Fourier transform of an L¹ density. -/
theorem stage_memLp_and_dampedStage_integrable {f : 𝓢(ℝ, ℂ)} {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ p ∈ T, 1 ≤ p) (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0)
    (hsupp : ∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0) :
    MemLp (stage T f) 2 volume ∧ Integrable (dampedStage T f) volume := by
  obtain ⟨C, hC, hB⟩ := dampedStage_abs_bound T hT f hf
  have hd := measurable_dampedStage T hT f hf
  have hz := fun x hx ↦ stage_eq_zero_before_box hX T hT h0 hsupp (x := x) hx
  have he (x : ℝ) : stage T f x = (Real.exp (x/2) : ℂ) * dampedStage T f x := by
    unfold dampedStage
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, show x/2 + -x/2 = 0 by ring, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  have hm : Measurable (stage T f) := by
    rw [show stage T f = _ from funext he]
    exact Continuous.measurable (by fun_prop : Continuous (fun x : ℝ ↦ (Real.exp (x/2) : ℂ))) |>.mul hd
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 ?_,
    integrable_of_supported_exp hd.aestronglyMeasurable (a := -Real.log X) (by norm_num)
      (fun x hx ↦ by simp [dampedStage, hz x hx]) hB⟩
  apply integrable_of_supported_exp (hm.norm.pow_const 2).aestronglyMeasurable
    (a := -Real.log X) (β := -3) (C := C^2)
    (by norm_num) (fun x hx ↦ by simp [hz x hx])
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h : ‖stage T f x‖ ≤ C * Real.exp (-(3/2)*x) := by
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (x/2) * (C * Real.exp (-2*x)) := mul_le_mul_of_nonneg_left (hB x) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq ?_
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

private theorem exists_mesh_point_within (t θ a : ℝ) (ha : 0 < a) :
    ∃ j : ℤ, dist (θ + (j : ℝ) * a) t < a := by
  let j := ⌊(t - θ) / a⌋
  have hlo : (j : ℝ) * a ≤ t - θ := (le_div_iff₀ ha).mp (Int.floor_le _)
  have hhi : t - θ < ((j : ℝ) + 1) * a := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one _)
  refine ⟨j, ?_⟩
  rw [Real.dist_eq, abs_of_nonpos (by linarith : θ + (j : ℝ)*a - t ≤ 0)]
  linarith


/-- An integrable L² Mellin density is zero if its Fourier samples vanish on
all of a family of refining shifted meshes. This is the uniqueness step for
the intersection of the rational fixed-box packet stages. -/
private theorem ae_eq_zero_of_packet_fourier_samples {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2)
    (θ a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hsmall : Tendsto a atTop (𝓝 0))
    (hsample : ∀ n (j : ℤ), (𝓕 f) (θ n + (j : ℝ)*a n) = 0) : f =ᵐ[volume] 0 := by
  have hcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h₁
  have hzero (t : ℝ) : (𝓕 f) t = 0 := by
    choose j hj using fun n ↦ exists_mesh_point_within t (θ n) (a n) (ha n)
    have hgrid : Tendsto (fun n ↦ θ n + (j n : ℝ)*a n) atTop (𝓝 t) := by
      refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
      exact ((tendsto_order.1 hsmall).2 ε hε).mono fun n hn ↦ (hj n).trans hn
    have h : Tendsto (fun n ↦ (𝓕 f) (θ n + (j n : ℝ)*a n)) atTop (𝓝 ((𝓕 f) t)) :=
      (hcont.tendsto t).comp hgrid
    have hc : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 ((𝓕 f) t)) :=
      h.congr (fun n ↦ hsample n (j n))
    exact tendsto_nhds_unique hc tendsto_const_nhds
  have h := (memLp_two_fourier_and_eLpNorm_eq h₁ h₂).2
  rw [show 𝓕 f = 0 from funext hzero, eLpNorm_zero] at h
  exact (eLpNorm_eq_zero_iff two_ne_zero).mp h.symm

private def lowerSupport (a : ℝ) : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  { f | ∀ᵐ x ∂volume, x < a → f x = 0 }

private theorem isClosed_lowerSupport (a : ℝ) : IsClosed (lowerSupport a) := by
  apply IsSeqClosed.isClosed
  intro f g hf hlim
  obtain ⟨φ, -, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ, x < a → f n x = 0 := ae_all_iff.mpr hf
  filter_upwards [hall, hφ] with x hx hconv hxa
  have heq : (fun n ↦ f (φ n) x) = fun _ : ℕ ↦ (0 : ℂ) := funext fun n ↦ hx (φ n) hxa
  exact tendsto_nhds_unique hconv (heq.symm ▸ tendsto_const_nhds)

private def mellinWindow (a : ℝ) : ℝ → ℂ :=
  (Ici a).indicator (fun x ↦ (Real.exp (-x/2) : ℂ))

private theorem measurable_mellinWindow (a : ℝ) : Measurable (mellinWindow a) := by
  apply Measurable.indicator _ measurableSet_Ici
  fun_prop

private theorem memLp_mellinWindow (a : ℝ) : MemLp (mellinWindow a) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (measurable_mellinWindow a).aestronglyMeasurable).2
  have hi : IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Ici a) := by
    rw [IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    simpa only [IntegrableOn, neg_one_mul] using
      (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) a)
  apply (hi.integrable_indicator measurableSet_Ici).congr
  filter_upwards with x
  by_cases hx : x ∈ Ici a
  · simp only [mellinWindow, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
    congr 1
    ring
  · simp [mellinWindow, hx]

private theorem norm_mellinWindow_le (a x : ℝ) : ‖mellinWindow a x‖ ≤ Real.exp (-a/2) := by
  by_cases hx : a ≤ x
  · rw [mellinWindow, indicator_of_mem (mem_Ici.mpr hx), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  · simp [mellinWindow, hx, (Real.exp_pos _).le]

private def mellinDensity (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) := mellinWindow a x * f x

private theorem mellinDensity_integrable (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Integrable (mellinDensity a f) :=
  (memLp_mellinWindow a).integrable_mul (Lp.memLp f)

private theorem mellinDensity_memLp (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (mellinDensity a f) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := Real.exp (-a/2))
    ((measurable_mellinWindow a).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards with x
  change ‖mellinWindow a x * f x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_mellinWindow_le a x) (norm_nonneg _)

private def mellinProfile (a ξ : ℝ) (x : ℝ) : ℂ :=
  mellinWindow a x * (Real.fourierChar (x*ξ) : ℂ)

private theorem mellinProfile_memLp (a ξ : ℝ) : MemLp (mellinProfile a ξ) 2 volume := by
  have hc : Continuous (fun x : ℝ ↦ (Real.fourierChar (x*ξ) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))
  refine (memLp_mellinWindow a).of_le ((measurable_mellinWindow a).aestronglyMeasurable.mul
    hc.aestronglyMeasurable) ?_
  filter_upwards with x
  simp [mellinProfile, Circle.norm_coe]

/-- The closed-stage Mellin coefficient on the imaginary line is a bounded
functional, represented by the exponential window times the Fourier character. -/
def mellinSample (a ξ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
  innerSL ℂ ((mellinProfile_memLp a ξ).toLp (mellinProfile a ξ))

private theorem conj_mellinWindow (a x : ℝ) : conj (mellinWindow a x) = mellinWindow a x := by
  by_cases hx : x ∈ Ici a
  · rw [mellinWindow, indicator_of_mem hx, Complex.conj_ofReal]
  · simp [mellinWindow, hx]

private theorem mellinSample_apply (a ξ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : mellinSample a ξ f = 𝓕 (mellinDensity a f) ξ := by
  change inner ℂ ((mellinProfile_memLp a ξ).toLp (mellinProfile a ξ)) f = _
  rw [L2.inner_def, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [(mellinProfile_memLp a ξ).coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply, Circle.smul_def, smul_eq_mul]
  simp only [mellinProfile, mellinDensity, map_mul, conj_mellinWindow, Real.fourierChar_apply,
    ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [show (↑(- (2 * Real.pi * (x*ξ))) : ℂ) * Complex.I =
    -(↑(2 * Real.pi * (x*ξ)) * Complex.I) by push_cast; ring]
  ring

/-- When the function vanishes below the window, the Mellin sample is the Fourier transform
of the exponentially damped function. -/
theorem mellinSample_eq_fourier_damped (a ξ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : ∀ᵐ x ∂volume, x < a → f x = 0) :
    mellinSample a ξ f = 𝓕 (fun x : ℝ ↦ (Real.exp (-x / 2) : ℂ) * f x) ξ := by
  rw [mellinSample_apply]
  apply Real.fourier_congr_ae
  filter_upwards [hf] with x hx
  by_cases h : a ≤ x
  · simp [mellinDensity, mellinWindow, h]
  · simp [mellinDensity, mellinWindow, h, hx (lt_of_not_ge h)]

/-- The genuine rational test family at the box `X / ∏ p`. The pair of polar
conditions is imposed before applying the rational theta sum and the earlier factors. -/
def stageGenerators (X : ℝ) (T : Finset ℕ) : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  { F | ∃ f : 𝓢(ℝ, ℂ), f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
      (∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0) ∧
      F =ᵐ[volume] stage T f }

/-- Membership in the genuine generator family is an actual polar Schwartz
representation in the specified Fourier box. -/
theorem mem_stageGenerators_iff {X : ℝ} {T : Finset ℕ} {F : Lp ℂ 2 (volume : Measure ℝ)} :
    F ∈ stageGenerators X T ↔
      ∃ f : 𝓢(ℝ, ℂ), f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
        (∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0) ∧
        (F : ℝ → ℂ) =ᵐ[volume] stage T f := Iff.rfl

/-- The polar generator family is already a linear subspace. -/
def stageSubmodule (X : ℝ) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := stageGenerators X T
  zero_mem' := by
    refine ⟨0, by simp, by simp, fun _ _ ↦ by simp, ?_⟩
    exact (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).trans
      (ae_of_all _ fun x ↦ (stage_zero T x).symm)
  add_mem' := by
    rintro F G ⟨f, hf, hf0, hfBand, hF⟩ ⟨g, hg, hg0, hgBand, hG⟩
    refine ⟨f+g, by simp [hf, hg], by simp [hf0, hg0], fun y hy ↦ by
      simp [hfBand y hy, hgBand y hy], ?_⟩
    filter_upwards [hF, hG, Lp.coeFn_add F G] with x hx hy hz
    rw [hz, Pi.add_apply, hx, hy, stage_add T hT f g hf hg]
  smul_mem' := by
    rintro c F ⟨f, hf, hf0, hfBand, hF⟩
    refine ⟨c • f, by simp [hf], by simp [hf0], fun y hy ↦ by
      simp [hfBand y hy], ?_⟩
    filter_upwards [hF, Lp.coeFn_smul c F] with x hx hy
    rw [hy, Pi.smul_apply, hx, stage_smul]

/-- The actual closed Hilbert subspace at the Fourier radius `X / ∏_{q∈T} q`. -/
def closedStageSubmodule (X : ℝ) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) :
    ClosedSubmodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  toSubmodule := (stageSubmodule X T hT).topologicalClosure
  isClosed' := isClosed_closure

theorem mem_closedStageSubmodule_iff (X : ℝ) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) (F : Lp ℂ 2 (volume : Measure ℝ)) :
    F ∈ closedStageSubmodule X T hT ↔ F ∈ closure (stageGenerators X T) := Iff.rfl

/-- Inserting a new finite factor preserves membership in the previous actual box:
its input is realized by a Schwartz dilation difference in the wider box. -/
theorem stageGenerators_insert_subset {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 ≤ p) :
    stageGenerators X (insert p T) ⊆ stageGenerators X T := by
  by_cases hmem : p ∈ T
  · rw [Finset.insert_eq_of_mem hmem]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast zero_lt_one.trans_le hp
  have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hP : 0 < ∏ q ∈ T, (q : ℝ) :=
    Finset.prod_pos fun q hq ↦ by exact_mod_cast zero_lt_one.trans_le (hT q hq)
  rintro F ⟨f, hzero, hFourier0, hband, hF⟩
  let g := dilate (p : ℝ) hpR f
  have hlinear (ξ : ℝ) : (𝓕 (f-g)) ξ = (𝓕 f) ξ - (𝓕 g) ξ := by
    change SchwartzMap.fourierTransformCLM ℂ (f-g) ξ =
      SchwartzMap.fourierTransformCLM ℂ f ξ - SchwartzMap.fourierTransformCLM ℂ g ξ
    rw [map_sub, sub_apply]
  refine ⟨f-g, by simp [g, hzero], ?_, ?_, ?_⟩
  · rw [hlinear]
    simp [g, hFourier0, fourier_dilate hpR]
  · intro ξ hξ
    rw [hlinear]
    rw [Finset.prod_insert hmem] at hband
    have hh : X / ((p : ℝ) * ∏ q ∈ T, (q : ℝ)) ≤ X / ∏ q ∈ T, (q : ℝ) :=
      div_le_div_of_nonneg_left hX.le hP (le_mul_of_one_le_left hP.le hp₁)
    rw [hband ξ (hh.trans_lt hξ)]
    have hscale : X / ((p : ℝ) * ∏ q ∈ T, (q : ℝ)) < |ξ / p| := by
      rw [abs_div, abs_of_pos hpR, mul_comm (p : ℝ), ← div_div]
      exact div_lt_div_of_pos_right hξ hpR
    simp only [g, fourier_dilate hpR, hband _ hscale, smul_zero, sub_zero]
  · filter_upwards [hF] with x hx
    rw [hx, show g = _ from rfl,
      stage_difference_dilate T hT (zero_lt_one.trans_le hp) hmem f hzero]

private theorem closure_stageGenerators_supported {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ p ∈ T, 1 ≤ p) :
    closure (stageGenerators X T) ⊆ lowerSupport (-Real.log X) := by
  apply closure_minimal _ (isClosed_lowerSupport _)
  rintro F ⟨f, -, h0, hsupp, hF⟩
  filter_upwards [hF] with x hx hxa
  exact hx.trans (stage_eq_zero_before_box hX T hT h0 hsupp hxa)

/-- The closed stage retains its common lower logarithmic support bound. -/
theorem closedStage_ae_zero_before_box {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hF : F ∈ closedStageSubmodule X T hT) :
    ∀ᵐ x ∂volume, x < -Real.log X → F x = 0 :=
  closure_stageGenerators_supported hX T hT ((mem_closedStageSubmodule_iff X T hT F).mp hF)

theorem mellinSample_stage_zeros {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 < p) (hpT : p ∈ T)
    (j : ℤ) {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ closure (stageGenerators X T)) :
    mellinSample (-Real.log X) ((j : ℝ) / Real.log p) F = 0 := by
  apply closure_minimal (s := stageGenerators X T)
    (t := {F | mellinSample (-Real.log X) ((j : ℝ) / Real.log p) F = 0}) ?_ ?_ hF
  · rintro G ⟨f, hf, hf0, hsupp, hG⟩
    have hD : mellinDensity (-Real.log X) G =ᵐ[volume] dampedStage T f := by
      filter_upwards [hG] with x hx
      by_cases hxa : -Real.log X ≤ x
      · simp [mellinDensity, mellinWindow, dampedStage, hxa, hx]
      · have hz := stage_eq_zero_before_box hX T hT hf0 hsupp (not_le.mp hxa)
        simp [mellinDensity, mellinWindow, dampedStage, hxa, hz]
    have hdiv : ∀ y : ℝ, X / (∏ q ∈ T.erase p, (q : ℝ)) < |y| → (𝓕 f) y = 0 := by
      intro y hy
      apply hsupp y
      have hpT' : T.erase p ⊆ T := Finset.erase_subset _ _
      have hprod : (∏ q ∈ T.erase p, (q : ℝ)) ≤ ∏ q ∈ T, (q : ℝ) :=
        Finset.prod_le_prod_of_subset_of_one_le₀ hpT' (fun _ _ ↦ by positivity)
          (fun q hq _ ↦ by exact_mod_cast hT q hq)
      have hpos : 0 < ∏ q ∈ T.erase p, (q : ℝ) :=
        Finset.prod_pos fun q hq ↦ by exact_mod_cast zero_lt_one.trans_le (hT q (hpT' hq))
      exact (div_le_div_of_nonneg_left hX.le hpos hprod).trans_lt hy
    have hi := (stage_memLp_and_dampedStage_integrable hX (T.erase p)
      (fun q hq ↦ hT q (Finset.erase_subset _ _ hq)) hf hf0 hdiv).2
    change mellinSample (-Real.log X) ((j : ℝ) / Real.log p) G = 0
    rw [mellinSample_apply]
    trans 𝓕 (dampedStage T f) ((j : ℝ) / Real.log p)
    · simp only [Real.fourier_real_eq]
      apply integral_congr_ae
      filter_upwards [hD] with x hx
      rw [hx]
    · have hz := fourier_dampedStage_zero_on_mesh (T.erase p) hp (Finset.notMem_erase _ _) f hi j
      simpa only [Finset.insert_erase hpT] using hz
  · exact isClosed_singleton.preimage (mellinSample _ _).continuous

/-- If the actual rational stages contain a sequence of increasingly fine prime
meshes, their fixed-box Hilbert closures have zero intersection. This uses the
arithmetic theta formula and both polar conditions, not a dense-grid hypothesis
on the images of arbitrary L² functions. -/
theorem eq_zero_of_mem_all_closed_stages {X : ℝ} (hX : 0 < X) (T : ℕ → Finset ℕ)
    (hT : ∀ n q, q ∈ T n → 1 ≤ q) (p : ℕ → ℕ) (hp : ∀ n, 1 < p n)
    (hpT : ∀ n, p n ∈ T n) (hmesh : Tendsto (fun n ↦ (Real.log (p n : ℝ))⁻¹) atTop (𝓝 0))
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : ∀ n, F ∈ closure (stageGenerators X (T n))) : F = 0 := by
  let a := -Real.log X
  have hpos (n : ℕ) : 0 < (Real.log (p n : ℝ))⁻¹ := by
    exact inv_pos.mpr (Real.log_pos (by exact_mod_cast hp n))
  have hD : mellinDensity a F =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_packet_fourier_samples (mellinDensity_integrable a F)
      (mellinDensity_memLp a F) (fun _ ↦ 0) _ hpos hmesh
    intro n j
    simpa only [zero_add, ← div_eq_mul_inv, ← mellinSample_apply] using
      (mellinSample_stage_zeros hX (T n) (hT n) (hp n) (hpT n) j (hF n))
  have hS := closure_stageGenerators_supported hX (T 0) (hT 0) (hF 0)
  apply Lp.ext
  filter_upwards [hS, hD, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hd hz
  rw [hz, Pi.zero_apply]
  by_cases ha : x < a
  · exact hx ha
  · have he : (Real.exp (-x/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    simp only [mellinDensity, mellinWindow, indicator_of_mem (show x ∈ Ici a from le_of_not_gt ha),
      Pi.zero_apply] at hd
    exact (mul_eq_zero.mp hd).resolve_left he

/-- The principal-value stage boxes shrink together while their common output
support stays fixed. -/
def closedStages (X : ℝ) (p : ℕ → ℕ) (n : ℕ) : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  closure (stageGenerators X ((Finset.range n).image p))

/-- The genuine rational fixed-box stages form a decreasing chain with zero
intersection for any sequence of increasing prime norms escaping to infinity. -/
theorem closedStages_decreasing_and_separating {X : ℝ} (hX : 0 < X) (p : ℕ → ℕ)
    (hp : ∀ n, 1 < p n) (hmesh : Tendsto (fun n ↦ (Real.log (p n : ℝ))⁻¹) atTop (𝓝 0)) :
    Antitone (closedStages X p) ∧ ∀ F, (∀ n, F ∈ closedStages X p n) → F = 0 := by
  have hP (n q : ℕ) (hq : q ∈ (Finset.range n).image p) : 1 ≤ q := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hp j).le
  refine ⟨?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    unfold closedStages
    rw [Finset.range_add_one, Finset.image_insert]
    exact closure_mono (stageGenerators_insert_subset hX _ (hP n) (hp n).le)
  · intro F hF
    apply eq_zero_of_mem_all_closed_stages hX (fun n ↦ (Finset.range (n+1)).image p)
      (fun n ↦ hP (n+1)) p hp _ hmesh (fun n ↦ hF (n+1))
    intro n
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩

end RiemannMasullo.RationalPacket
