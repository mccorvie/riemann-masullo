module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactLaplace
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! # A compact Laplace kernel with positive real part in a strip

Dividing an even autocorrelation by `cosh (R * x)` makes the real part of its transform
nonnegative on both vertical edges. The strip maximum principle gives strict positivity
inside, and Schwarz's lemma supplies an explicit sector bound on every narrower strip.
-/

public noncomputable section

open Complex Metric Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RiemannMasullo

private theorem sector_of_cayley_bound {w : ℂ} {H q : ℝ} (hH : 0 < H)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ‖w - H‖ ≤ q * ‖w + H‖) :
    ‖w‖ ≤ ((1 + q ^ 2) / (1 - q ^ 2)) * w.re := by
  have hden : 0 < 1 - q ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hq1) (by linarith : 0 < 1 + q)]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mpr h
  rw [mul_pow] at hsq
  have hminus : ‖w - (H : ℂ)‖ ^ 2 = ‖w‖ ^ 2 + H ^ 2 - 2 * H * w.re := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hplus : ‖w + (H : ℂ)‖ ^ 2 = ‖w‖ ^ 2 + H ^ 2 + 2 * H * w.re := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hminus, hplus] at hsq
  have ham : 2 * H * ‖w‖ ≤ ‖w‖ ^ 2 + H ^ 2 := by nlinarith [sq_nonneg (‖w‖ - H)]
  have hprod : (2 * H) * (‖w‖ * (1 - q ^ 2)) ≤ (2 * H) * ((1 + q ^ 2) * w.re) := by
    nlinarith only [mul_le_mul_of_nonneg_left ham hden.le, hsq]
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * H)).mp hprod

/-- A positive real part and a real central value give a sector estimate on a smaller disk.
The multiplicative constant depends only on the ratio of the two radii. -/
private theorem norm_le_mul_re_of_positive_disk {f : ℂ → ℂ} {c z : ℂ} {H B R : ℝ}
    (hB : 0 ≤ B) (hBR : B < R) (hz : dist z c ≤ B)
    (hf : DifferentiableOn ℂ f (ball c R)) (hpos : ∀ w ∈ ball c R, 0 < (f w).re)
    (hc : f c = (H : ℂ)) :
    ‖f z‖ ≤ ((1 + (B/R)^2) / (1 - (B/R)^2)) * (f z).re := by
  have hR := hB.trans_lt hBR
  have hH : 0 < H := by simpa [hc] using hpos c (mem_ball_self hR)
  let g (w : ℂ) := (f w - H) / (f w + H)
  have hne (w : ℂ) (hw : w ∈ ball c R) : f w + H ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at he'
    linarith [hpos w hw]
  have hd : DifferentiableOn ℂ g (ball c R) :=
    (hf.sub_const _).div (hf.add_const _) hne
  have hgc : g c = 0 := by simp [g, hc]
  have hm : MapsTo g (ball c R) (closedBall (g c) 1) := by
    intro w hw
    rw [mem_closedBall, hgc, dist_zero_right]
    change ‖(f w - H) / (f w + H)‖ ≤ 1
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, sub_zero]
    nlinarith only [mul_nonneg hH.le (hpos w hw).le]
  have hzR : z ∈ ball c R := hz.trans_lt hBR
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm hzR
  rw [hgc, dist_zero_right] at hsch
  have hq : 0 ≤ B/R := div_nonneg hB hR.le
  have hq1 : B/R < 1 := (div_lt_one hR).mpr hBR
  apply sector_of_cayley_bound hH hq hq1
  apply (div_le_iff₀ (norm_pos_iff.mpr (hne z hzR))).mp
  simpa [g, norm_div, one_div, div_eq_inv_mul] using hsch.trans
    (mul_le_mul_of_nonneg_left hz (by positivity))

/-- A single bound works for every height of a closed substrip of a positive-real
holomorphic function whose values on the imaginary axis are real. -/
private theorem norm_le_mul_re_on_substrip {f : ℂ → ℂ} {R B : ℝ} (hB : 0 ≤ B) (hBR : B < R)
    (hf : Differentiable ℂ f) (hpos : ∀ w : ℂ, |w.re| < R → 0 < (f w).re)
    (him : ∀ t : ℝ, (f (t*I)).im = 0) (r t : ℝ) (hr : |r| ≤ B) :
    ‖f (r + t*I)‖ ≤ ((1 + (B/R)^2) / (1 - (B/R)^2)) * (f (r + t*I)).re := by
  let c : ℂ := (t : ℂ)*I
  have hcre : c.re = 0 := by simp [c]
  have hc : f c = ((f c).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [c] using him t
  apply norm_le_mul_re_of_positive_disk hB hBR (c := c) _ hf.differentiableOn _ hc
  · simpa [c, dist_eq_norm, Real.norm_eq_abs] using hr
  · intro w hw
    apply hpos
    have hh := Complex.abs_re_le_norm (w-c)
    simp only [Complex.sub_re, hcre, sub_zero] at hh
    exact hh.trans_lt (by simpa [dist_eq_norm] using hw)


/-- Boundary positivity propagates to a vertical strip for any holomorphic function bounded
there. Applying the strip maximum principle to the negative exponential requires only a
constant bound at infinity. -/
private theorem re_nonneg_on_strip_of_bounded_edges {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : Differentiable ℂ f) (hbound : ∃ M : ℝ, ∀ w : ℂ, |w.re| < R → ‖f w‖ ≤ M)
    (hedge : ∀ w : ℂ, |w.re| = R → 0 ≤ (f w).re) (z : ℂ) (hz : |z.re| ≤ R) :
    0 ≤ (f z).re := by
  let g (w : ℂ) := Complex.exp (-(f w))
  have hd : Differentiable ℂ g := Complex.differentiable_exp.comp hf.neg
  have he (w : ℂ) (hw : |w.re| = R) : ‖g w‖ ≤ 1 := by
    simpa [g, Complex.norm_exp] using hedge w hw
  have hnorm : ‖g z‖ ≤ 1 := by
    apply PhragmenLindelof.vertical_strip (a := -R) (b := R) hd.diffContOnCl _
      (fun w hw ↦ he w (by rw [hw, abs_neg, abs_of_pos hR]))
      (fun w hw ↦ he w (by rw [hw, abs_of_pos hR]))
      (abs_le.mp hz).1 (abs_le.mp hz).2
    obtain ⟨M, hM⟩ := hbound
    refine ⟨0, div_pos Real.pi_pos (by linarith), M, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    rw [eventually_inf_principal]
    apply Filter.Eventually.of_forall
    intro w hw
    have hw' : |w.re| < R := abs_lt.mpr hw
    have hb : -(f w).re ≤ M :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hM w hw'))
    simpa [g, Complex.norm_exp] using Real.exp_le_exp.mpr hb
  simpa [g, Complex.norm_exp] using hnorm

/-- Strict positivity at one interior point makes the real part strictly positive throughout
the connected open strip once its real part is known to be nonnegative there. -/
private theorem re_pos_on_strip_of_re_nonneg {f : ℂ → ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (hne : ∃ w : ℂ, |w.re| < R ∧ 0 < (f w).re)
    (hpos : ∀ w : ℂ, |w.re| < R → 0 ≤ (f w).re)
    (z : ℂ) (hz : |z.re| < R) : 0 < (f z).re := by
  by_contra! h
  have hzero := le_antisymm h (hpos z hz)
  let U := Complex.re ⁻¹' Ioo (-R) R
  let g (w : ℂ) := Complex.exp (-(f w))
  have hgn (w : ℂ) : ‖g w‖ = Real.exp (-(f w).re) := by simp [g, Complex.norm_exp]
  have hzmax : ‖g z‖ = 1 := by simp [hgn, hzero]
  have hm : IsMaxOn (norm ∘ g) U z := by
    apply isMaxOn_iff.mpr
    intro w hw
    change ‖g w‖ ≤ ‖g z‖
    rw [hzmax, hgn, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (hpos w (abs_lt.mpr hw))
  have hconn : IsPreconnected U := ((convex_halfSpace_re_gt (-R)).inter
    (convex_halfSpace_re_lt R)).isPreconnected
  have hopen : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hd : Differentiable ℂ g := Complex.differentiable_exp.comp hf.neg
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hconn hopen hd.differentiableOn
    (abs_lt.mp hz : z ∈ U) hm
  obtain ⟨w, hw, hp⟩ := hne
  have hval : ‖g w‖ = ‖g z‖ := heq (abs_lt.mp hw)
  rw [hzmax, hgn] at hval
  exact ((Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hp)).ne) hval


private theorem sector_laplace_re {v : ℝ → ℝ} (hv : Continuous v) (hc : HasCompactSupport v)
    (r t : ℝ) :
    (bilateralLaplace (fun x ↦ (v x : ℂ)) (r + t*I)).re =
    ∫ x : ℝ, v x * Real.exp (r*x) * Real.cos (t*x) := by
  have hint : Integrable (fun x : ℝ ↦ (v x : ℂ) * Complex.exp (((r : ℂ) + t*I)*x)) := by
    exact ((Complex.continuous_ofReal.comp hv).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hc.comp_left Complex.ofReal_zero).mul_right
  change RCLike.re (∫ x : ℝ, (v x : ℂ) * Complex.exp (((r : ℂ) + t*I)*x)) = _
  rw [← integral_re hint]
  apply integral_congr_ae
  filter_upwards with x
  change ((v x : ℂ) * Complex.exp (((r : ℂ) + t*I)*x)).re = _
  simp [Complex.exp_re, mul_assoc]

private theorem sector_edge_cosine {u : ℝ → ℝ} (hu : Continuous u) (hc : HasCompactSupport u)
    (he : ∀ x, u (-x) = u x) (R t : ℝ) :
    ∫ x : ℝ, u x / Real.cosh (R*x) * Real.exp (R*x) * Real.cos (t*x) =
    ∫ x : ℝ, u x * Real.cos (t*x) := by
  let g (r x : ℝ) := u x / Real.cosh (R*x) * Real.exp (r*x) * Real.cos (t*x)
  have hi (r : ℝ) : Integrable (g r) := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [g]
      have hne (x : ℝ) : Real.cosh (R*x) ≠ 0 := (Real.cosh_pos _).ne'
      fun_prop (disch := first | exact hne | exact hne _)
    · apply hc.mono
      intro x hx hx0
      exact hx (by simp [g, hx0])
  have hneg : (∫ x, g (-R) x) = ∫ x, g R x := by
    conv_rhs => rw [← integral_neg_eq_self (g R) volume]
    apply integral_congr_ae
    filter_upwards with x
    simp [g, he, neg_mul, mul_neg]
  have hsum : (∫ x, g R x) + (∫ x, g (-R) x) = 2 * ∫ x, u x * Real.cos (t*x) := by
    rw [← integral_add (hi _) (hi _), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [g]
    rw [neg_mul]
    have hsumexp : Real.exp (R*x) + Real.exp (-(R*x)) = 2 * Real.cosh (R*x) := by
      rw [Real.cosh_eq]
      ring
    calc
      _ = u x / Real.cosh (R*x) * Real.cos (t*x) *
            (Real.exp (R*x) + Real.exp (-(R*x))) := by ring
      _ = _ := by rw [hsumexp]; field_simp [(Real.cosh_pos _).ne']
  rw [hneg] at hsum
  change (∫ x, g R x) = _
  linarith


/-- Dividing an even nonnegative compact numerator with nonnegative cosine transform by a hyperbolic cosine
produces a Laplace transform of strictly positive real part on an open strip, with an explicit
sector on each closed substrip. Positivity of the numerator at the origin gives positive mass. -/
private theorem cosh_kernel_laplace_sector {u : ℝ → ℝ} (hu : Continuous u) (hc : HasCompactSupport u)
    (he : ∀ x, u (-x) = u x) (hnonneg : ∀ x, 0 ≤ u x) (h0 : 0 < u 0)
    (hcos : ∀ t : ℝ, 0 ≤ ∫ x : ℝ, u x * Real.cos (t*x))
    {R : ℝ} (hR : 0 < R) :
    let k := bilateralLaplace (fun x : ℝ ↦ ((u x / Real.cosh (R*x) : ℝ) : ℂ))
    (∀ z : ℂ, |z.re| < R → 0 < (k z).re) ∧
    ∀ B : ℝ, 0 ≤ B → B < R → ∀ r t : ℝ, |r| ≤ B →
      ‖k (r + t*I)‖ ≤ ((1 + (B/R)^2) / (1 - (B/R)^2)) * (k (r + t*I)).re := by
  let v (x : ℝ) := u x / Real.cosh (R*x)
  let k := bilateralLaplace (fun x ↦ (v x : ℂ))
  have hv : Continuous v :=
    hu.div (by fun_prop) (fun _ ↦ (Real.cosh_pos _).ne')
  have hc' : HasCompactSupport v := by
    apply hc.mono
    intro x hx hx0
    exact hx (by simp [v, hx0])
  have he' (x : ℝ) : v (-x) = v x := by simp [v, he]
  have h0' : v 0 ≠ 0 := by simpa [v] using h0.ne'
  have hvC := Complex.continuous_ofReal.comp hv
  have hcC := hc'.comp_left Complex.ofReal_zero
  have hd : Differentiable ℂ k := differentiable_bilateralLaplace_of_hasCompactSupport hvC hcC
  have hb : ∃ M : ℝ, ∀ z : ℂ, |z.re| < R → ‖k z‖ ≤ M :=
    ⟨∫ x : ℝ, ‖(v x : ℂ)‖ * Real.exp (R * |x|), fun z hz ↦
      norm_bilateralLaplace_le_weighted_integral hvC hcC R z hz.le⟩
  have hed (z : ℂ) (hz : |z.re| = R) : 0 ≤ (k z).re := by
    have hrep := Complex.re_add_im z
    change 0 ≤ (bilateralLaplace (fun x ↦ (v x : ℂ)) z).re
    rw [← hrep, sector_laplace_re hv hc']
    rcases (abs_eq hR.le).mp hz with hr | hr
    · rw [hr]
      exact (hcos _).trans_eq (sector_edge_cosine hu hc he R z.im).symm
    · rw [hr]
      simpa only [v, neg_mul, Real.cosh_neg] using
        (hcos _).trans_eq (sector_edge_cosine hu hc he (-R) z.im).symm
  have hn (z : ℂ) (hz : |z.re| < R) : 0 ≤ (k z).re :=
    re_nonneg_on_strip_of_bounded_edges hR hd hb hed z hz.le
  have him (t : ℝ) : (k (t*I)).im = 0 := bilateralLaplace_im_eq_zero_of_even he' t
  have hvpos : 0 < ∫ x, v x :=
    hv.integral_pos_of_hasCompactSupport_nonneg_ne_zero hc'
      (fun x ↦ div_nonneg (hnonneg x) (Real.cosh_pos _).le) h0'
  have hk0 : 0 < (k 0).re := by
    simpa [k, bilateralLaplace, integral_complex_ofReal] using hvpos
  have hpos := re_pos_on_strip_of_re_nonneg hd ⟨0, by simpa using hR, hk0⟩ hn
  exact ⟨hpos, fun B hB hBR r t hr ↦ norm_le_mul_re_on_substrip hB hBR hd hpos him r t hr⟩

/-- A compact nonnegative smooth physical kernel with a Laplace transform confined to a
uniform right-hand sector on every smaller strip. The numerator is the self-convolution of
a smooth even bump. -/
theorem exists_compact_smooth_strip_sector {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ → ℝ, ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧ (∀ x, K (-x) = K x) ∧
      (∀ x, 0 ≤ K x) ∧ 0 < K 0 ∧
      (∀ z : ℂ, |z.re| < R → 0 < (bilateralLaplace (fun x ↦ (K x : ℂ)) z).re) ∧
      ∀ B : ℝ, 0 ≤ B → B < R → ∀ r t : ℝ, |r| ≤ B →
        ‖bilateralLaplace (fun x ↦ (K x : ℂ)) (r + t*I)‖ ≤
          ((1 + (B/R)^2) / (1 - (B/R)^2)) *
            (bilateralLaplace (fun x ↦ (K x : ℂ)) (r + t*I)).re := by
  obtain ⟨u, hus, huc, hun, hue, h0, -, -, haxis⟩ := exists_normalized_smooth_autocorrelation
  have hcos (t : ℝ) : 0 ≤ ∫ x : ℝ, u x * Real.cos (t*x) := by
    obtain ⟨c, hc, he⟩ := haxis t
    have h := congrArg Complex.re he
    have heq := sector_laplace_re hus.continuous huc 0 t
    simp only [Complex.ofReal_zero, zero_add, zero_mul, Real.exp_zero, mul_one] at heq
    rw [← heq, h]
    exact hc.1
  let K (x : ℝ) := u x / Real.cosh (R*x)
  have hks : ContDiff ℝ ∞ K := hus.div (by simp_rw [Real.cosh_eq]; fun_prop)
    (fun _ ↦ (Real.cosh_pos _).ne')
  have hkc : HasCompactSupport K := by
    apply huc.mono
    intro x hx hx0
    exact hx (by simp [K, hx0])
  exact ⟨K, hks, hkc, (fun x ↦ by simp [K, hue]), (fun x ↦ div_nonneg (hun x) (Real.cosh_pos _).le),
    (by simpa [K] using h0), cosh_kernel_laplace_sector hus.continuous huc hue hun h0 hcos hR⟩

end RiemannMasullo
