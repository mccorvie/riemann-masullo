module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith

/-! # Three prescribed moments of a translated compact real profile -/

open MeasureTheory Set
open scoped ContDiff

@[expose] public noncomputable section

namespace RiemannMasullo

private theorem integrable_real_mul_of_compact {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {v : ℝ → ℂ} (hv : Continuous v) :
    Integrable (fun x ↦ (f x : ℂ) * v x) := by
  have hc' : HasCompactSupport (fun x ↦ (f x : ℂ)) :=
    hc.comp_left (g := Complex.ofReal) rfl
  exact ((Complex.continuous_ofReal.comp hf).mul hv).integrable_of_hasCompactSupport
    hc'.mul_right

/-- Integration by parts with the project's positive-exponent bilateral Laplace convention. -/
theorem bilateralLaplace_real_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    bilateralLaplace (fun x ↦ Complex.ofReal (deriv f x)) z =
      -z * bilateralLaplace (fun x ↦ (f x : ℂ)) z := by
  let E (x : ℝ) := Complex.exp (z * x)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have dE (x : ℝ) : HasDerivAt E (z * E x) x := by
    have hz : HasDerivAt (fun y : ℝ ↦ z * (y : ℂ)) z x := by
      simpa using (((hasDerivAt_id x).ofReal_comp).const_mul z)
    simpa [E, mul_comm] using! (Complex.hasDerivAt_exp (z * x)).comp x hz
  have df := contDiff_infty_iff_deriv.mp hf
  have hint := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x ↦ (f x : ℂ)) (v := E) (u' := fun x ↦ Complex.ofReal (deriv f x))
    (v' := fun x ↦ z * E x)
    (fun x _ ↦ (df.1 x).hasDerivAt.ofReal_comp) (fun x _ ↦ dE x)
    (integrable_real_mul_of_compact hf.continuous hc (continuous_const.mul hE))
    (integrable_real_mul_of_compact df.2.continuous hc.deriv hE)
    (integrable_real_mul_of_compact hf.continuous hc hE)
  have hmove : (∫ x, (f x : ℂ) * (z * E x)) =
      z * bilateralLaplace (fun x ↦ (f x : ℂ)) z := by
    rw [bilateralLaplace, ← integral_const_mul]
    congr 1
    funext x
    dsimp [E]
    ring
  change _ = -bilateralLaplace (fun x ↦ Complex.ofReal (deriv f x)) z at hint
  rw [hmove] at hint
  linear_combination hint

/-- Translating a bilateral Laplace profile multiplies its transform by an exponential. -/
theorem bilateralLaplace_translate (f : ℝ → ℂ) (a : ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ f (x - a)) z = Complex.exp (z * a) * bilateralLaplace f z := by
  unfold bilateralLaplace
  rw [← integral_add_right_eq_self (fun x : ℝ ↦ f (x - a) * Complex.exp (z * x)) a,
    ← integral_const_mul]
  congr 1
  funext x
  simp [mul_add, Complex.exp_add]
  ring

/-- Translating the odd derivative combination moves support from `[-1,1]` to `[2,4]`. -/
def translatedMomentDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (deriv f)) (x - 3) - deriv f (x - 3) / 4

/-- The transform multiplier for translating the third-order operator
`(D² − 1/4)D` by three with the positive bilateral Laplace convention. -/
def translatedIntervalMultiplier (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  -Complex.exp (3 * z) * z * (z ^ 2 - 1 / 4) * G z

theorem contDiff_translatedMomentDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (translatedMomentDerivative f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hd₂ := (contDiff_infty_iff_deriv.mp hd).2
  have hd₃ := (contDiff_infty_iff_deriv.mp hd₂).2
  exact (hd₃.comp (contDiff_id.sub contDiff_const)).sub
    ((hd.comp (contDiff_id.sub contDiff_const)).div_const 4)

theorem tsupport_translatedMomentDerivative_subset {f : ℝ → ℝ}
    (hs : tsupport f ⊆ Set.Icc (-1) 1) : tsupport (translatedMomentDerivative f) ⊆ Set.Icc 2 4 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  have hx' : x - 3 ∉ tsupport f := fun h ↦ hnot (by
    rcases hs h with ⟨hl, hu⟩
    constructor <;> linarith)
  have h1 : x - 3 ∉ tsupport (deriv f) := fun h ↦ hx' (tsupport_deriv_subset h)
  have h2 : x - 3 ∉ tsupport (deriv (deriv f)) := fun h ↦ h1 (tsupport_deriv_subset h)
  have h3 : x - 3 ∉ tsupport (deriv (deriv (deriv f))) := fun h ↦ h2 (tsupport_deriv_subset h)
  exact hx (by simp [translatedMomentDerivative, image_eq_zero_of_notMem_tsupport h1,
    image_eq_zero_of_notMem_tsupport h3])

/-- All three paired moments of the translated derivative come from this exact multiplier. -/
theorem bilateralLaplace_translatedMomentDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    bilateralLaplace (fun x ↦ (translatedMomentDerivative f x : ℂ)) z =
      translatedIntervalMultiplier (bilateralLaplace (fun x ↦ (f x : ℂ))) z := by
  unfold translatedIntervalMultiplier
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hd₂ := (contDiff_infty_iff_deriv.mp hd).2
  have hd₃ := (contDiff_infty_iff_deriv.mp hd₂).2
  let f₁ (x : ℝ) : ℂ := Complex.ofReal (deriv f x)
  let f₃ (x : ℝ) : ℂ := Complex.ofReal (deriv (deriv (deriv f)) x)
  change bilateralLaplace (fun x ↦ ((deriv (deriv (deriv f)) (x - 3) - deriv f (x - 3) / 4 : ℝ) : ℂ)) z = _
  push_cast
  convert (bilateralLaplace_translate (fun x ↦ f₃ x - f₁ x / 4) 3 z).trans ?_ using 1
  have hE : Continuous (fun x : ℝ ↦ Complex.exp (z * x)) := by fun_prop
  have hi₁ := integrable_real_mul_of_compact hd.continuous hc.deriv hE
  have hi₃ := integrable_real_mul_of_compact hd₃.continuous hc.deriv.deriv.deriv hE
  have hsub : bilateralLaplace (fun x ↦ f₃ x - f₁ x / 4) z =
      bilateralLaplace f₃ z - (1 / 4 : ℂ) * bilateralLaplace f₁ z := by
    unfold bilateralLaplace
    rw [← integral_const_mul, ← integral_sub hi₃ (hi₁.const_mul _)]
    congr 1
    funext x
    dsimp [f₁, f₃]
    ring
  rw [hsub]
  dsimp [f₁, f₃]
  rw [bilateralLaplace_real_deriv hd₂ hc.deriv.deriv, bilateralLaplace_real_deriv hd hc.deriv,
    bilateralLaplace_real_deriv hf hc]
  norm_num [mul_comm z (3 : ℂ)]
  ring

/-- The two polar evaluations and the central evaluation all vanish. -/
theorem translatedIntervalMultiplier_polar_central (G : ℂ → ℂ) :
    translatedIntervalMultiplier G (-(1 / 2)) = 0 ∧
    translatedIntervalMultiplier G 0 = 0 ∧ translatedIntervalMultiplier G (1 / 2) = 0 := by
  norm_num [translatedIntervalMultiplier]

/-- A transform that detects every off-axis point still detects every such point
in the open critical strip after applying the translated polynomial multiplier. -/
theorem translatedIntervalMultiplier_ne_zero (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, z.re ≠ 0 → G z ≠ 0) (z : ℂ)
    (hz₀ : 0 < |z.re|) (hz₁ : |z.re| < 1 / 2) :
    translatedIntervalMultiplier G z ≠ 0 := by
  have hre : z.re ≠ 0 := abs_pos.mp hz₀
  have hz : z ≠ 0 := fun h ↦ hre (by simp [h])
  have hpol : z ^ 2 - 1 / 4 ≠ 0 := by
    intro h
    have hsq : z ^ 2 = (1 / 2 : ℂ) ^ 2 := by rw [sub_eq_zero.mp h]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h <;> rw [h] at hz₁ <;> norm_num at hz₁
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hz)
    hpol) (hG z hre)

private theorem norm_intervalPolynomial_le (z : ℂ) :
    ‖z‖ * ‖z ^ 2 - 1 / 4‖ ≤ (‖z‖ + 1) ^ 3 := by
  have hpol : ‖z ^ 2 - 1 / 4‖ ≤ (‖z‖ + 1) ^ 2 := by
    calc
      ‖z ^ 2 - 1 / 4‖ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ ^ 2 + 1 / 4 := by norm_num [norm_pow, norm_div, Complex.norm_ofNat]
      _ ≤ (‖z‖ + 1) ^ 2 := by nlinarith [norm_nonneg z]
  calc
    ‖z‖ * ‖z ^ 2 - 1 / 4‖ ≤ (‖z‖ + 1) * (‖z‖ + 1) ^ 2 :=
      mul_le_mul (by linarith : ‖z‖ ≤ ‖z‖ + 1) hpol (norm_nonneg _) (by positivity)
    _ = (‖z‖ + 1) ^ 3 := by ring

/-- Multiplication by the translated cubic preserves square-root exponential decay on
every closed vertical strip, with an explicit loss of a factor two in the decay rate. -/
theorem translatedIntervalMultiplier_strip_bound (G : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ z : ℂ, |z.re| ≤ B →
      ‖G z‖ ≤ 2 * Real.exp B * Real.exp (-(Real.log 2 / 2) * Real.sqrt |z.im|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ B →
      ‖translatedIntervalMultiplier G z‖ ≤ C * Real.exp (-(Real.log 2 / 4) * Real.sqrt |z.im|) := by
  let d := Real.log 2 / 12
  have hd : 0 < d := by dsimp [d]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  let D := B + 1 + 2 / d ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Real.exp (3 * B) * D ^ 3 * (2 * Real.exp B), by positivity, ?_⟩
  intro z hz
  let u := Real.sqrt |z.im|
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = |z.im| := Real.sq_sqrt (abs_nonneg _)
  have hexp : 1 ≤ Real.exp (d * u) := Real.one_le_exp (mul_nonneg hd.le hu)
  have him : |z.im| ≤ (2 / d ^ 2) * Real.exp (d * u) := by
    have htaylor := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) 2
    norm_num at htaylor
    calc
      |z.im| ≤ (2 * Real.exp (d * u)) / d ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hd), ← husq]
        nlinarith only [htaylor]
      _ = (2 / d ^ 2) * Real.exp (d * u) := by ring
  have hnorm : ‖z‖ + 1 ≤ D * Real.exp (d * u) := by
    have hbase := mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ B + 1)
    dsimp [D]
    nlinarith only [Complex.norm_le_abs_re_add_abs_im z, hz, him, hbase]
  have hcubic : ‖z‖ * ‖z ^ 2 - 1 / 4‖ ≤ (D * Real.exp (d * u)) ^ 3 :=
    (norm_intervalPolynomial_le z).trans (pow_le_pow_left₀ (by positivity) hnorm 3)
  have htrans : ‖Complex.exp (3 * z)‖ ≤ Real.exp (3 * B) := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    simpa [Complex.mul_re] using
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hz) (by norm_num : (0 : ℝ) ≤ 3))
  have hcombine : Real.exp (d * u) ^ 3 * Real.exp (-(Real.log 2 / 2) * u) =
      Real.exp (-(Real.log 2 / 4) * u) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  calc
    ‖translatedIntervalMultiplier G z‖ =
        ‖Complex.exp (3 * z)‖ * (‖z‖ * ‖z ^ 2 - 1 / 4‖) * ‖G z‖ := by
      simp [translatedIntervalMultiplier, mul_assoc]
    _ ≤ Real.exp (3 * B) * (D * Real.exp (d * u)) ^ 3 *
        (2 * Real.exp B * Real.exp (-(Real.log 2 / 2) * u)) :=
      mul_le_mul (mul_le_mul htrans hcubic (by positivity) (Real.exp_pos _).le)
        (hG z hz) (norm_nonneg _) (by positivity)
    _ = (Real.exp (3 * B) * D ^ 3 * (2 * Real.exp B)) *
        (Real.exp (d * u) ^ 3 * Real.exp (-(Real.log 2 / 2) * u)) := by ring
    _ = _ := by rw [hcombine]

/-- Quantitative preservation of nonvanishing for the translated cubic on a finite window
away from the central line and both polar evaluations. -/
theorem translatedIntervalMultiplier_norm_lower {G : ℂ → ℂ} {z : ℂ} {d η L : ℝ}
    (hd : 0 ≤ d) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hz₀ : d ≤ |z.re|) (hz₁ : |z.re| ≤ 1/2 - η) (hG : L ≤ ‖G z‖) :
    Real.exp (-(3/2)) * d * (η * (1 - η)) * L ≤ ‖translatedIntervalMultiplier G z‖ := by
  have hη₁ : η ≤ 1/2 := by linarith [abs_nonneg z.re]
  have hz : d ≤ ‖z‖ := hz₀.trans (Complex.abs_re_le_norm _)
  have hleft : 0 ≤ 1/2 - z.re := by linarith [le_abs_self z.re]
  have hright : 0 ≤ 1/2 + z.re := by linarith [neg_le_abs z.re]
  have hminus : 1/2 - z.re ≤ ‖z - 1/2‖ := by
    calc
      _ ≤ |(z - 1/2).re| := by
        have := neg_le_abs ((z - 1/2).re)
        norm_num at this ⊢
        linarith
      _ ≤ _ := Complex.abs_re_le_norm _
  have hplus : 1/2 + z.re ≤ ‖z + 1/2‖ := by
    calc
      _ ≤ |(z + 1/2).re| := by
        have := le_abs_self ((z + 1/2).re)
        norm_num at this ⊢
        linarith
      _ ≤ _ := Complex.abs_re_le_norm _
  have hpol : η * (1 - η) ≤ ‖z ^ 2 - 1/4‖ := by
    rw [show z ^ 2 - 1/4 = (z - 1/2) * (z + 1/2) by ring, norm_mul]
    refine le_trans ?_ (mul_le_mul hminus hplus hright (norm_nonneg _))
    have hsq := pow_le_pow_left₀ (abs_nonneg z.re) hz₁ 2
    rw [sq_abs] at hsq
    nlinarith
  have htrans : Real.exp (-(3/2)) ≤ ‖Complex.exp (3 * z)‖ := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    simp only [Complex.mul_re]
    norm_num
    linarith [neg_le_abs z.re]
  simp only [translatedIntervalMultiplier, norm_mul, norm_neg]
  exact mul_le_mul (mul_le_mul (mul_le_mul htrans hz hd (norm_nonneg _)) hpol
      (mul_nonneg hη (by linarith)) (by positivity)) hG hL (by positivity)

end RiemannMasullo
