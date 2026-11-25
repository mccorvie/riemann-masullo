module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # Bilateral Laplace transforms of compactly supported functions

For the convention `∫ x, f x * exp (z * x)`, convolution multiplies transforms and the
angular-frequency inversion factor at the origin is `1 / (2 * π)`. A single integration by
parts gives uniform decay on each closed vertical strip. A normalized smooth autocorrelation
has real transform in `[0, 1]` on the imaginary axis.
-/

public noncomputable section

open Complex Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology FourierTransform SchwartzMap

namespace RiemannMasullo

private theorem weighted_integrable {f : ℝ → ℂ} (hs : Continuous f) (hc : HasCompactSupport f)
    (z : ℂ) : Integrable (fun x : ℝ ↦ f x * Complex.exp (z*x)) :=
  (hs.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right

/-- The product rule for the repository's plus-sign bilateral transform. -/
theorem bilateralLaplace_convolution (f g : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hg : Continuous g)
    (hd : HasCompactSupport g) (z : ℂ) :
    bilateralLaplace (f ⋆[mul ℝ ℂ] g) z = bilateralLaplace f z * bilateralLaplace g z := by
  let F (x : ℝ) := f x * Complex.exp (z*x)
  let G (x : ℝ) := g x * Complex.exp (z*x)
  have ht (x : ℝ) : (f ⋆[mul ℝ ℂ] g) x * Complex.exp (z*x) = (F ⋆[mul ℝ ℂ] G) x := by
    simp only [convolution_def, mul_apply', ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp only [F, G, mul_mul_mul_comm (f y) _ (g (x-y)), ← Complex.exp_add, Complex.ofReal_sub]
    congr 2
    ring
  unfold bilateralLaplace
  simp_rw [ht]
  exact integral_convolution (mul ℝ ℂ) (weighted_integrable hf hc z) (weighted_integrable hg hd z)

/-- Translation of a compact test has the positive exponential multiplier. -/
theorem bilateralLaplace_translate (f : ℝ → ℂ) (a : ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ f (x-a)) z = Complex.exp (z*a) * bilateralLaplace f z := by
  unfold bilateralLaplace
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (fun x : ℝ ↦ f (x-a)*Complex.exp (z*x)) a]
  apply integral_congr_ae
  filter_upwards with x
  simp only [add_sub_cancel_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-- A weighted difference of two compact profiles has the corresponding transform. -/
theorem bilateralLaplace_sub_const_mul (f g : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hg : Continuous g) (hd : HasCompactSupport g)
    (c z : ℂ) : bilateralLaplace (fun x ↦ f x-c*g x) z =
      bilateralLaplace f z-c*bilateralLaplace g z := by
  unfold bilateralLaplace
  simp only [sub_mul, mul_assoc c]
  rw [integral_sub (weighted_integrable hf hc z) ((weighted_integrable hg hd z).const_mul c),
    integral_const_mul]

/-- The bilateral Laplace transform of a continuous compactly supported function is entire. -/
theorem differentiable_bilateralLaplace_of_hasCompactSupport {v : ℝ → ℂ} (hv : Continuous v)
    (hc : HasCompactSupport v) : Differentiable ℂ (bilateralLaplace v) := by
  intro z
  apply (hasDerivAt_bilateralLaplace (α := |z.re|+1) ?_ (lt_add_one _)).differentiableAt
  apply Continuous.memLp_of_hasCompactSupport
  · exact (by fun_prop : Continuous fun x : ℝ ↦ Real.exp ((|z.re|+1)*|x|)).smul hv
  · apply hc.mono
    intro x hx hx0
    exact hx (by simp [hx0])

/-- A real even function has real bilateral transform on the imaginary axis. -/
theorem bilateralLaplace_im_eq_zero_of_even {v : ℝ → ℝ} (he : ∀ x, v (-x) = v x) (t : ℝ) :
    (bilateralLaplace (fun x ↦ (v x : ℂ)) (t*I)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold bilateralLaplace
  rw [← integral_conj]
  conv_rhs => rw [← integral_neg_eq_self (fun x : ℝ ↦ (v x : ℂ) * Complex.exp (t*I*x)) volume]
  apply integral_congr_ae
  filter_upwards with x
  simp only [he, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
    Complex.ofReal_neg, mul_neg, neg_mul]

/-- The norm of the transform on a closed strip is bounded by one weighted integral. -/
theorem norm_bilateralLaplace_le_weighted_integral {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (R : ℝ) (z : ℂ) (hz : |z.re| ≤ R) :
    ‖bilateralLaplace f z‖ ≤ ∫ x : ℝ, ‖f x‖ * Real.exp (R * |x|) := by
  let m (x : ℝ) := ‖f x‖ * Real.exp (R * |x|)
  have hm : Integrable m := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hf.norm.mul (by fun_prop)
    · apply hc.mono
      intro x hx hx0
      exact hx (by simp [m, hx0])
  apply norm_integral_le_of_norm_le hm
  filter_upwards with x
  change ‖f x * Complex.exp (z * x)‖ ≤ ‖f x‖ * Real.exp (R * |x|)
  rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  calc z.re * x ≤ |z.re * x| := le_abs_self _
    _ = |z.re| * |x| := abs_mul _ _
    _ ≤ R * |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

private theorem bilateralLaplace_integration_by_parts {G : ℝ → ℂ} (hs : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (w : ℂ) :
    w * bilateralLaplace G w = -bilateralLaplace (deriv G) w := by
  let E (x : ℝ) := Complex.exp (w*x)
  have hE (x : ℝ) : HasDerivAt E (w * E x) x := by
    convert (((hasDerivAt_id' (x : ℂ)).const_mul w).cexp).comp_ofReal using 1
    ring
  have hec : Continuous E := continuous_iff_continuousAt.mpr fun x ↦ (hE x).continuousAt
  have hg : Integrable (G * E) :=
    (hs.continuous.mul hec).integrable_of_hasCompactSupport hc.mul_right
  have hgd : Integrable (deriv G * E) :=
    ((hs.continuous_deriv (by simp)).mul hec).integrable_of_hasCompactSupport hc.deriv.mul_right
  have hge : Integrable (G * (fun x ↦ w * E x)) :=
    (hs.continuous.mul (continuous_const.mul hec)).integrable_of_hasCompactSupport hc.mul_right
  have heq := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := G) (u' := deriv G) (v := E) (v' := fun x ↦ w * E x)
    (fun x _ ↦ (hs.differentiable (by simp) x).hasDerivAt) (fun x _ ↦ hE x) hge hgd hg
  calc
    w * bilateralLaplace G w = ∫ x, G x * (w * E x) := by
      unfold bilateralLaplace
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [E]
      ring
    _ = -bilateralLaplace (deriv G) w := heq

/-- One integration by parts bounds the height times the transform by a single explicit
constant throughout any prescribed closed vertical strip. -/
theorem abs_im_mul_norm_bilateralLaplace_le {G : ℝ → ℂ} (hs : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (B : ℝ) (w : ℂ) (hw : |w.re| ≤ B) :
    |w.im| * ‖bilateralLaplace G w‖ ≤ ∫ x : ℝ, ‖deriv G x‖ * Real.exp (B*|x|) := by
  have hdc := hs.continuous_deriv (by simp)
  calc
    |w.im| * ‖bilateralLaplace G w‖ ≤ ‖w‖ * ‖bilateralLaplace G w‖ :=
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm w) (norm_nonneg _)
    _ = ‖bilateralLaplace (deriv G) w‖ := by
      rw [← norm_mul, bilateralLaplace_integration_by_parts hs hc, norm_neg]
    _ ≤ _ := norm_bilateralLaplace_le_weighted_integral hdc hc.deriv B w hw

/-- Uniform decay at both vertical ends of a closed strip for any compactly supported
continuously differentiable kernel. -/
theorem bilateralLaplace_tends_zero_uniform_closedStrip {G : ℝ → ℂ} (hs : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
      ∀ w : ℂ, |w.re| ≤ B → T ≤ |w.im| → ‖bilateralLaplace G w‖ < ε := by
  let M := ∫ x : ℝ, ‖deriv G x‖ * Real.exp (B*|x|)
  have hM : 0 ≤ M := integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  intro ε hε
  refine ⟨(M+1)/ε, by positivity, fun w hr ht ↦ ?_⟩
  by_contra! hn
  have hh := mul_le_mul ht hn hε.le (abs_nonneg _)
  rw [div_mul_cancel₀ _ hε.ne'] at hh
  have hb : |w.im| * ‖bilateralLaplace G w‖ ≤ M := abs_im_mul_norm_bilateralLaplace_le hs hc B w hr
  linarith

/-- For a compact smooth complex kernel, imaginary-axis Laplace moments are
integrable as a function of angular frequency. Their integral equals `2π F(0)`.
The change of variables from Mathlib's Fourier transform is `t = -2πs`. -/
theorem bilateralLaplace_inversion_zero {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) :
    Integrable (fun t : ℝ ↦ bilateralLaplace F ((t : ℂ) * I)) ∧
      F 0 = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, bilateralLaplace F ((t : ℂ) * I) := by
  let D (t : ℝ) := bilateralLaplace F ((t : ℂ) * I)
  have hπ : 0 < 2 * Real.pi := by positivity
  have hfour : (𝓕 F) = (fun s : ℝ ↦ D (-(2 * Real.pi) * s)) := by
    funext s
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul, mul_comm _ (F y)]
    congr 2
    push_cast
    ring
  have hFourInt : Integrable (𝓕 F) := (𝓕 (hcF.toSchwartzMap hF)).integrable
  have hD : Integrable D :=
    (integrable_comp_mul_left_iff D (neg_ne_zero.mpr hπ.ne')).mp (hfour ▸ hFourInt)
  refine ⟨hD, ?_⟩
  have hzero := (hF.continuous.integrable_of_hasCompactSupport hcF).fourierInv_fourier_eq
    hFourInt (hF.continuous.continuousAt (x := 0))
  rw [Real.fourierInv_eq_fourier_neg, neg_zero, Real.fourier_real_eq_integral_exp_smul] at hzero
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at hzero
  rw [← hzero, hfour, Measure.integral_comp_mul_left, abs_inv, abs_neg, abs_of_pos hπ,
    Complex.real_smul]


/-- A real autocorrelation of a nonnegative normalized bump, including its physical sign,
evenness, mass, and a real transform in [0,1] along the imaginary axis. -/
theorem exists_normalized_smooth_autocorrelation :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ (∀ x, 0 ≤ G x) ∧
      (∀ x, G (-x) = G x) ∧ 0 < G 0 ∧ (∫ x, G x) = 1 ∧
      bilateralLaplace (fun x ↦ (G x : ℂ)) 0 = 1 ∧
      ∀ t : ℝ, ∃ c ∈ Set.Icc (0 : ℝ) 1,
        bilateralLaplace (fun x ↦ (G x : ℂ)) ((t : ℂ)*I) = c := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : ℝ → ℝ := b.normed volume
  let r (x : ℝ) := g (-x)
  let G := g ⋆[mul ℝ ℝ] r
  have hgs : ContDiff ℝ ∞ g := b.contDiff_normed
  have hgc : HasCompactSupport g := b.hasCompactSupport_normed
  have hrs : ContDiff ℝ ∞ r := hgs.comp contDiff_neg
  have hrc : HasCompactSupport r := hgc.comp_homeomorph (Homeomorph.neg ℝ)
  have hgp : ∀ x, 0 ≤ g x := b.nonneg_normed
  have h0g : g 0 ≠ 0 := by
    change (0 : ℝ) ∈ Function.support (b.normed volume)
    rw [b.support_normed_eq]
    simpa using b.rOut_pos
  have hGi (x : ℝ) : G x = ∫ y, g y * g (y-x) := by
    simp only [G, convolution_def, mul_apply', r, neg_sub]
  have hmassg : ∫ x, g x = 1 := b.integral_normed
  have hmass : ∫ x, G x = 1 := by
    calc
      _ = (∫ x, g x)*(∫ x, r x) :=
        integral_convolution (mul ℝ ℝ) (hgs.continuous.integrable_of_hasCompactSupport hgc)
          (hrs.continuous.integrable_of_hasCompactSupport hrc)
      _ = 1 := by
        rw [show (∫ x, r x) = ∫ x, g x from integral_neg_eq_self g volume, hmassg, one_mul]
  refine ⟨G, hrc.contDiff_convolution_right _ hgs.continuous.locallyIntegrable hrs,
    hgc.convolution _ hrc, fun x ↦ ?_, fun x ↦ ?_, ?_, hmass, ?_, fun t ↦ ?_⟩
  · rw [hGi]
    exact integral_nonneg fun y ↦ mul_nonneg (hgp _) (hgp _)
  · rw [hGi, hGi]
    conv_rhs => rw [← integral_add_right_eq_self (fun y : ℝ ↦ g y*g (y-x)) x]
    simp only [sub_neg_eq_add, add_sub_cancel_right, mul_comm]
  · rw [hGi]
    simp only [sub_zero]
    exact (hgs.continuous.mul hgs.continuous).integral_pos_of_hasCompactSupport_nonneg_ne_zero
      hgc.mul_right (fun x ↦ mul_self_nonneg _) (mul_ne_zero h0g h0g)
  · simp [bilateralLaplace, integral_complex_ofReal, hmass]
  · let f (x : ℝ) : ℂ := g x
    let d (x : ℝ) : ℂ := r x
    have he : (fun x ↦ (G x : ℂ)) = f ⋆[mul ℝ ℂ] d := by
      funext x
      simp only [G, convolution_def, mul_apply', f, d, ← integral_complex_ofReal, Complex.ofReal_mul]
    have hf : Continuous f := Complex.continuous_ofReal.comp hgs.continuous
    have hc : HasCompactSupport f := hgc.comp_left Complex.ofReal_zero
    have hd : Continuous d := Complex.continuous_ofReal.comp hrs.continuous
    have hdc : HasCompactSupport d := hrc.comp_left Complex.ofReal_zero
    have href : bilateralLaplace d ((t : ℂ)*I) =
        starRingEnd ℂ (bilateralLaplace f ((t : ℂ)*I)) := by
      unfold bilateralLaplace
      rw [← integral_conj]
      conv_rhs => rw [← integral_neg_eq_self
        (fun y : ℝ ↦ starRingEnd ℂ (f y*Complex.exp ((t : ℂ)*I*y))) volume]
      apply integral_congr_ae
      filter_upwards with y
      simp [d, r, f, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
    have hbound : ‖bilateralLaplace f ((t : ℂ)*I)‖ ≤ 1 := by
      unfold bilateralLaplace
      calc
        _ ≤ ∫ x : ℝ, ‖f x*Complex.exp ((t : ℂ)*I*x)‖ := norm_integral_le_integral_norm _
        _ = ∫ x, g x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [f, Complex.norm_exp, Complex.mul_re, Complex.mul_im, Real.norm_eq_abs,
            abs_of_nonneg (hgp x)]
        _ = 1 := hmassg
    refine ⟨‖bilateralLaplace f ((t : ℂ)*I)‖^2, ⟨sq_nonneg _, ?_⟩, ?_⟩
    · nlinarith [sq_nonneg (1-‖bilateralLaplace f ((t : ℂ)*I)‖), norm_nonneg (bilateralLaplace f ((t : ℂ)*I))]
    · rw [he, bilateralLaplace_convolution f d hf hc hd hdc, href, Complex.mul_conj,
        Complex.sq_norm]

end RiemannMasullo
