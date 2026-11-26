module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.Ch01_Introduction.Sec4
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaGrowth
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Archimedean gamma integrals and normalized principal values

This evaluates the two positive vertical lines in Appendix B §4b on an even compact test.
The Gauss integral for digamma and Mellin inversion give the physical kernel at each real
or complex place, and character orthogonality identifies its actual restricted local test.
-/

@[expose] public noncomputable section

section

open Filter MeasureTheory Set
open scoped _root_.SchwartzMap Topology

namespace RiemannMasullo.ArchPV

private def diff (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)) / (1 - Complex.exp (-(t : ℂ)))

private def ordinate (A : ℂ) (k y : ℝ) : ℂ := A + ((k*y : ℝ) : ℂ) * Complex.I

private theorem re_ordinate (A : ℂ) (k y : ℝ) : (ordinate A k y).re = A.re := by
  simp [ordinate]

private theorem norm_phase (k y t : ℝ) :
    ‖Complex.exp (-(((k*y : ℝ) : ℂ) * Complex.I) * t)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Swapping the vertical and Gauss integrals is absolutely justified for a Schwartz weight.
The frequency scale is arbitrary, and the result keeps the reference value of digamma at one. -/
private theorem schwartz_digamma_fubini (W : 𝓢(ℝ, ℂ)) (A : ℂ) (hA : 0 < A.re) (k : ℝ) :
    let V (t : ℝ) :=
      (Complex.exp (-(t : ℂ)) * (∫ y : ℝ, W y) -
        Complex.exp (-A * t) * (∫ y : ℝ, W y * Complex.exp (-(((k*y : ℝ) : ℂ) * Complex.I) * t))) /
          (1 - Complex.exp (-(t : ℂ)))
    Integrable (fun y : ℝ ↦ W y * (Complex.digamma (A + ((k*y : ℝ) : ℂ) * Complex.I) - Complex.digamma 1)) ∧
    IntegrableOn V (Ioi 0) ∧
      (∫ y : ℝ, W y * (Complex.digamma (A + ((k*y : ℝ) : ℂ) * Complex.I) - Complex.digamma 1)) =
        ∫ t in Ioi (0 : ℝ), V t := by
  intro V
  let ν := (volume : Measure ℝ).restrict (Ioi 0)
  let B (p : ℝ × ℝ) : ℂ := W p.1 * diff (ordinate A k p.1) p.2
  have hm : Measurable B := by unfold B diff ordinate; fun_prop
  have hK (y : ℝ) : Integrable (diff (ordinate A k y)) ν ∧
      (∫ t, diff (ordinate A k y) t ∂ν) = Complex.digamma (ordinate A k y) - Complex.digamma 1 := by
    obtain ⟨hi, he⟩ := Complex.gauss_logDeriv_Gamma_difference (u := 1) (v := ordinate A k y)
      (by norm_num) (by rwa [re_ordinate])
    constructor
    · change IntegrableOn (fun t : ℝ ↦ (Complex.exp (-(t : ℂ)) - Complex.exp (-ordinate A k y * t)) /
        (1 - Complex.exp (-(t : ℂ)))) (Ioi 0)
      simpa only [neg_one_mul] using hi
    · simpa only [ν, diff, neg_one_mul, Complex.digamma_def] using he
  have hYn (y : ℝ) : ‖ordinate A k y‖ ≤ ‖A‖ + |k| * |y| := by
    apply (norm_add_le _ _).trans
    simp [Real.norm_eq_abs]
  let c := 4 + 4*(2+‖A‖) + 4/min A.re 1
  have hline (y : ℝ) : (∫ t, ‖diff (ordinate A k y) t‖ ∂ν) ≤ c + 4 * |k| * |y| := by
    have hb := Complex.integral_norm_gaussDifference_one_le hA (ordinate A k y) (by rw [re_ordinate])
    have hlt := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + ‖ordinate A k y‖)
    change (∫ t, ‖diff (ordinate A k y) t‖ ∂ν) ≤ _ at hb
    dsimp only [c]
    linarith [hYn y]
  have hpow : Integrable (fun y : ℝ ↦ |y| * ‖W y‖) := by
    simpa only [Real.norm_eq_abs, pow_one] using W.integrable_pow_mul volume 1
  have hb : Integrable B (volume.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    refine ⟨.of_forall fun y ↦ (hK y).1.const_mul (W y), ?_⟩
    apply ((W.integrable.norm.const_mul c).add (hpow.const_mul (4 * |k|))).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with y
    change ‖∫ t, ‖W y * diff (ordinate A k y) t‖ ∂ν‖ ≤ _
    simp only [Complex.norm_mul, integral_const_mul, Real.norm_eq_abs]
    have hnn : 0 ≤ ∫ t, ‖diff (ordinate A k y) t‖ ∂ν := integral_nonneg fun t ↦ norm_nonneg _
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) hnn)]
    change _ ≤ c * ‖W y‖ + 4 * |k| * (|y| * ‖W y‖)
    nlinarith only [mul_le_mul_of_nonneg_left (hline y) (norm_nonneg (W y))]
  have hvec (t : ℝ) : (∫ y : ℝ, B (y,t)) = V t := by
    let E (y : ℝ) := Complex.exp (-(((k*y : ℝ) : ℂ) * Complex.I) * t)
    have he (y : ℝ) : Complex.exp (-ordinate A k y * t) = Complex.exp (-A*t) * E y := by
      rw [← Complex.exp_add]
      congr 1
      unfold ordinate
      ring
    have hI : Integrable (fun y : ℝ ↦ W y * E y) := by
      refine W.integrable.norm.mono' (by dsimp [E]; fun_prop) (.of_forall fun y ↦ ?_)
      simp only [E, Complex.norm_mul, norm_phase, mul_one, le_refl]
    have hrewrite (y : ℝ) : B (y,t) =
        (Complex.exp (-(t : ℂ)) * W y - Complex.exp (-A*t) * (W y * E y)) /
          (1 - Complex.exp (-(t : ℂ))) := by
      simp only [B,diff,he]
      ring
    simp_rw [hrewrite]
    rw [integral_div, integral_sub (W.integrable.const_mul _) (hI.const_mul _),
      integral_const_mul, integral_const_mul]
  have hleft (y : ℝ) : (∫ t, B (y,t) ∂ν) = W y * (Complex.digamma (ordinate A k y) - Complex.digamma 1) := by
    change (∫ t, W y * diff (ordinate A k y) t ∂ν) = _
    rw [integral_const_mul, (hK y).2]
  refine ⟨hb.integral_prod_left.congr (.of_forall hleft), hb.integral_prod_right.congr (.of_forall hvec), ?_⟩
  calc
    _ = ∫ y : ℝ, ∫ t, B (y,t) ∂ν := integral_congr_ae (.of_forall fun y ↦ (hleft y).symm)
    _ = ∫ t, (∫ y : ℝ, B (y,t)) ∂ν := integral_integral_swap hb
    _ = _ := integral_congr_ae (.of_forall hvec)

end RiemannMasullo.ArchPV

end

section

open MeasureTheory Set
open scoped _root_.SchwartzMap

namespace RiemannMasullo.ArchPV

private def physicalDifference (H : ℝ → ℂ) (k : ℝ) (B : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(t : ℂ)) * H 0 - H (k*t) * Complex.exp (-B * t)) /
    (1 - Complex.exp (-(t : ℂ)))

private def phase (k y t : ℝ) : ℂ := Complex.exp (-(((k*y : ℝ) : ℂ) * Complex.I) * t)

/-- One gamma derivative evaluated using a right-half-plane Gauss integral and Fourier sampling.
Here D is the logarithm of the real or complex local gamma scale. -/
private theorem singleLine (W : 𝓢(ℝ, ℂ)) (A B : ℂ) (hA : 0 < A.re) (k : ℝ)
    (C D : ℂ) (hC : C ≠ 0) (H : ℝ → ℂ)
    (hzero : (∫ y : ℝ, W y) = C * H 0)
    (hsamp : ∀ t : ℝ, Complex.exp (-A * t) * (∫ y : ℝ, W y * phase k y t) =
      C * (H (k*t) * Complex.exp (-B * t))) :
    IntegrableOn (physicalDifference H k B) (Ioi 0) ∧
    (∫ y : ℝ, W y * ((k : ℂ) * Complex.digamma (A + ((k*y : ℝ) : ℂ) * Complex.I) - D)) / C =
      k * (∫ t in Ioi (0 : ℝ), physicalDifference H k B t) +
        ((k : ℂ) * Complex.digamma 1 - D) * H 0 := by
  let T (y : ℝ) := W y * (Complex.digamma (A + ((k*y : ℝ) : ℂ) * Complex.I) - Complex.digamma 1)
  obtain ⟨hT, hV, he⟩ := schwartz_digamma_fubini W A hA k
  let V (t : ℝ) := (Complex.exp (-(t : ℂ)) * (∫ y : ℝ, W y) -
      Complex.exp (-A*t) * (∫ y : ℝ, W y * phase k y t)) / (1 - Complex.exp (-(t : ℂ)))
  change Integrable T at hT
  change IntegrableOn V (Ioi 0) at hV
  change (∫ y, T y) = ∫ t in Ioi (0 : ℝ), V t at he
  have hv (t : ℝ) : V t = C * physicalDifference H k B t := by
    dsimp only [V, physicalDifference]
    rw [hzero, hsamp]
    ring
  have hI : IntegrableOn (physicalDifference H k B) (Ioi 0) := by
    refine (hV.const_mul C⁻¹).congr (.of_forall fun t ↦ ?_)
    change C⁻¹ * V t = physicalDifference H k B t
    rw [hv, inv_mul_cancel_left₀ hC]
  refine ⟨hI, ?_⟩
  have hfreq (y : ℝ) :
      W y * ((k : ℂ) * Complex.digamma (A + ((k*y : ℝ) : ℂ) * Complex.I) - D) =
      (k : ℂ) * T y + ((k : ℂ) * Complex.digamma 1 - D) * W y := by unfold T; ring
  simp_rw [hfreq]
  rw [integral_add (hT.const_mul _) (W.integrable.const_mul _), integral_const_mul, integral_const_mul,
    he, hzero]
  simp_rw [hv]
  rw [integral_const_mul]
  field_simp

/-- The reference kernel at one accounts for the full delta term at the identity. -/
private theorem pairedLine (W W' : 𝓢(ℝ, ℂ)) (A A' B B' : ℂ) (hA : 0 < A.re) (hA' : 0 < A'.re)
    (k : ℝ) (C D : ℂ) (hC : C ≠ 0) (H : ℝ → ℂ)
    (hzero : (∫ y : ℝ, W y) = C * H 0) (hzero' : (∫ y : ℝ, W' y) = C * H 0)
    (hsamp : ∀ t : ℝ, Complex.exp (-A * t) *
      (∫ y : ℝ, W y * Complex.exp (-(((k*y : ℝ) : ℂ) * Complex.I) * t)) =
      C * (H (k*t) * Complex.exp (-B * t)))
    (hsamp' : ∀ t : ℝ, Complex.exp (-A' * t) *
      (∫ y : ℝ, W' y * Complex.exp (-(((k*y : ℝ) : ℂ) * Complex.I) * t)) =
      C * (H (-(k*t)) * Complex.exp (-B' * t))) :
    IntegrableOn (heckeArchimedeanDigammaKernel k B B' H) (Ioi 0) ∧
    ((∫ y : ℝ, W y * ((k : ℂ) * Complex.digamma (A + ((k*y : ℝ) : ℂ) * Complex.I) - D)) +
      (∫ y : ℝ, W' y * ((k : ℂ) * Complex.digamma (A' + ((k*y : ℝ) : ℂ) * Complex.I) - D))) / C =
      (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k B B' H t) - 2 * D * H 0 := by
  let H' (x : ℝ) := H (-x)
  have hzero₂ : (∫ y : ℝ, W' y) = C * H' 0 := by simpa [H'] using hzero'
  obtain ⟨hI, h⟩ := singleLine W A B hA k C D hC H hzero hsamp
  obtain ⟨hI', h'⟩ := singleLine W' A' B' hA' k C D hC H' hzero₂ hsamp'
  let Ref := heckeArchimedeanDigammaKernel 1 1 1 (fun _ ↦ 1)
  obtain ⟨hr, hre⟩ := heckeArchimedeanDigammaKernel_one
  have hR (t : ℝ) : heckeArchimedeanDigammaKernel k B B' H t =
      (k : ℂ) * (physicalDifference H k B t + physicalDifference H' k B' t) +
      ((k : ℂ) * H 0) * Ref t := by
    simp only [physicalDifference, Ref, heckeArchimedeanDigammaKernel, H', neg_zero,
      Complex.ofReal_one, one_mul, neg_one_mul, one_mul, mul_one, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hK : IntegrableOn (heckeArchimedeanDigammaKernel k B B' H) (Ioi 0) :=
    (((hI.add hI').const_mul (k : ℂ)).add (hr.const_mul ((k : ℂ)*H 0))).congr (.of_forall fun t ↦ (hR t).symm)
  refine ⟨hK, ?_⟩
  rw [add_div, h, h']
  simp_rw [hR]
  have hsumI : IntegrableOn (fun t ↦ physicalDifference H k B t + physicalDifference H' k B' t) (Ioi 0) := hI.add hI'
  have hRefI : IntegrableOn Ref (Ioi 0) := hr
  rw [integral_add (hsumI.const_mul (k : ℂ)) (hRefI.const_mul ((k : ℂ) * H 0)), integral_const_mul, integral_const_mul,
    integral_add hI hI']
  change (k : ℂ) * _ + _ + ((k : ℂ) * _ + _) = _ + ((k : ℂ) * H 0) *
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1 1 1 (fun _ ↦ 1) t) - _
  rw [hre, Complex.digamma_one]
  simp only [H', neg_zero]
  ring

end RiemannMasullo.ArchPV

end

section

open Filter MeasureTheory Set
open scoped _root_.SchwartzMap Topology ContDiff
namespace RiemannMasullo.ArchPV

/-- The norm-side Mellin transform is the bilateral transform with its literal log coordinate. -/
private theorem mellin_log_eq_Laplace (H : ℝ → ℂ) (s : ℂ) :
    mellin (fun t : ℝ ↦ H (Real.log t)) s = bilateralLaplace H s := by
  rw [mellin, ← integral_comp_exp, bilateralLaplace]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (H x)]
  congr 2
  ring

private theorem laplace_even (H : ℝ → ℂ) (he : ∀ x, H (-x) = H x) (s : ℂ) :
    bilateralLaplace H (-s) = bilateralLaplace H s := by
  rw [← mellin_log_eq_Laplace, ← mellin_log_eq_Laplace, ← mellin_comp_inv]
  congr 1
  ext t
  simp [Real.log_inv,he]

/-- The inverse Fourier sample at x is exp(b*x) H(x), including x=0. -/
private theorem exists_schwartz_Laplace_samples (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ))
    (hH : ExponentialDecay H) (b : ℝ) :
    ∃ W : 𝓢(ℝ, ℂ), (∀ y : ℝ, W y = bilateralLaplace H ((b : ℂ) + y * Complex.I)) ∧
      ∀ x : ℝ, (∫ y : ℝ, W y * Complex.exp (-((y : ℂ) * Complex.I) * x)) =
        (2 * (Real.pi : ℂ)) * (H x * Complex.exp ((b : ℂ) * x)) := by
  have hweight (c : ℝ) :
      ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = (Real.exp (c*x) : ℂ) * H x := by
    let G (x : ℝ) := (Real.exp (c*x) : ℂ) * H x
    have hc : HasCompactSupport G := hS.mul_left
    have hs : ContDiff ℝ (∞) G := by
      exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).mul (H.smooth _)
    exact ⟨hc.toSchwartzMap hs, fun _ ↦ rfl⟩
  obtain ⟨W, hW⟩ := exists_schwartz_verticalTrace_mellin_of_weighted_schwartz H (b-1) (b+1) (by linarith)
    (fun c _ ↦ hweight c) b ⟨by linarith, by linarith⟩
  let s (y : ℝ) : ℂ := (b : ℂ) + y * Complex.I
  have hval (y : ℝ) : W y = mellin (fun t : ℝ ↦ H (Real.log t)) (s y) := congrFun hW y
  refine ⟨W, fun y ↦ (hval y).trans (mellin_log_eq_Laplace _ _), ?_⟩
  intro x
  have hi : Complex.VerticalIntegrable (mellin (fun t : ℝ ↦ H (Real.log t))) b :=
    W.integrable.congr (.of_forall hval)
  have hx := Real.exp_pos x
  have hInv := mellinInv_mellin_eq b (fun t : ℝ ↦ H (Real.log t)) hx
    (mellinConvergent_of_exponentialDecay H hH b) hi
    (H.continuous.continuousAt.comp (Real.continuousAt_log hx.ne'))
  rw [Real.log_exp] at hInv
  have he : (∫ y : ℝ, W y * Complex.exp (-s y * (x : ℂ))) / (2 * (Real.pi : ℂ)) = H x := by
    rw [← hInv, mellinInv, Complex.real_smul]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [div_eq_inv_mul, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le, Real.log_exp, smul_eq_mul, mul_comm (x : ℂ)]
    rw [mul_comm, hval]
  have hp (y : ℝ) : W y * Complex.exp (-s y * (x : ℂ)) =
      Complex.exp (-(b : ℂ)*x) * (W y * Complex.exp (-((y : ℂ)*Complex.I)*x)) := by
    rw [mul_left_comm _ (W y), ← Complex.exp_add]
    congr 2
    unfold s
    ring
  simp_rw [hp] at he
  rw [integral_const_mul] at he
  have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hm := (div_eq_iff hne).mp he
  have hcancel : Complex.exp ((b : ℂ)*x) * Complex.exp (-(b : ℂ)*x) = 1 := by
    rw [← Complex.exp_add]
    simp [neg_mul]
  calc
    _ = Complex.exp ((b : ℂ)*x) * (Complex.exp (-(b : ℂ)*x) * _) := by rw [← mul_assoc, hcancel, one_mul]
    _ = _ := by rw [hm]; ring

end RiemannMasullo.ArchPV

end

section

open MeasureTheory Set
open scoped _root_.SchwartzMap
namespace RiemannMasullo.ArchPV

/-- Writing the scale explicitly treats the two Deligne gamma factors in the same formula. -/
private def gammaAtom (k Q : ℝ) (b s : ℂ) : ℂ :=
  Complex.exp (-(Real.log Q : ℂ) * ((k : ℂ) * (s+b))) * Complex.Gamma ((k : ℂ)*(s+b))

private theorem gammaAtom_real (b s : ℂ) : gammaAtom (1/2) Real.pi b s = Complex.Gammaℝ (s+b) := by
  rw [gammaAtom, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  congr 1 <;> congr 1 <;> ring

private theorem gammaAtom_complex (b s : ℂ) : gammaAtom 1 (2*Real.pi) b s = Complex.Gammaℂ (s+b) / 2 := by
  have hn : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  rw [gammaAtom, Complex.Gammaℂ_def, Complex.cpow_def_of_ne_zero hn]
  have hlog : Complex.log (2 * (Real.pi : ℂ)) = (Real.log (2*Real.pi) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  rw [hlog]
  simp only [Complex.ofReal_one,one_mul,neg_mul,mul_comm (Real.log (2*Real.pi) : ℂ)]
  ring

private theorem logDeriv_gammaAtom (k Q : ℝ) (b s : ℂ) (h : 0 < ((k : ℂ)*(s+b)).re) :
    logDeriv (gammaAtom k Q b) s = (k : ℂ) * Complex.digamma ((k : ℂ)*(s+b)) - k*(Real.log Q : ℂ) := by
  let z (w : ℂ) := (k : ℂ)*(w+b)
  let E (w : ℂ) := Complex.exp (-(Real.log Q : ℂ) * z w)
  have hz : HasDerivAt z k s := by simpa [z] using ((hasDerivAt_id s).add_const b).const_mul (k : ℂ)
  have he := (hz.const_mul (-(Real.log Q : ℂ))).cexp
  have hg := (Complex.differentiableAt_Gamma _ (fun n ↦ by
    intro heq
    have hzero : (z s).re ≤ 0 := by rw [heq]; simp
    exact (not_lt_of_ge hzero) h)).hasDerivAt.comp s hz
  have hen : E s ≠ 0 := Complex.exp_ne_zero _
  have hgn : Complex.Gamma (z s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h
  change logDeriv (fun w ↦ E w * (Complex.Gamma ∘ z) w) s = _
  rw [logDeriv_fun_mul s hen hgn he.differentiableAt hg.differentiableAt, logDeriv_apply, he.deriv,
    logDeriv_apply, hg.deriv, Complex.digamma_def, logDeriv_apply]
  change E s * (-(Real.log Q : ℂ) * k) / E s +
    (deriv Complex.Gamma (z s) * k) / Complex.Gamma (z s) =
    _ * (deriv Complex.Gamma (z s) / Complex.Gamma (z s)) - _
  field_simp
  ring

/-- For an even compact logarithmic test, these are the literal two positive vertical lines.
The identity retains the full kernel and its value at identity. -/
private theorem gammaAtom_paired_vertical {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (Q : ℝ)
    (b b' : ℂ) (hb : 0 ≤ b.re) (hb' : 0 ≤ b'.re)
    (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ)) (hH : ExponentialDecay H)
    (hev : ∀ x, H (-x) = H x) :
    IntegrableOn (heckeArchimedeanDigammaKernel k ((k : ℂ)*(1/2+b)) ((k : ℂ)*(1/2+b')) H) (Ioi 0) ∧
    (verticalLineIntegral (fun s ↦ bilateralLaplace H (s-1/2) * logDeriv (gammaAtom k Q b) s) a +
      verticalLineIntegral (fun s ↦ bilateralLaplace H (1/2-s) * logDeriv (gammaAtom k Q b') s) a) /
        (2 * (Real.pi : ℂ) * Complex.I) =
      (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k ((k : ℂ)*(1/2+b)) ((k : ℂ)*(1/2+b')) H t) -
        2 * ((k : ℂ)*(Real.log Q : ℂ)) * H 0 := by
  let d : ℝ := a-1/2
  let C : ℂ := 2*Real.pi
  have hC : C ≠ 0 := by dsimp only [C]; exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  obtain ⟨W, hW, hInv⟩ := exists_schwartz_Laplace_samples H hS hH d
  have hW0 : (∫ y : ℝ, W y) = C * H 0 := by simpa [C] using hInv 0
  have hr (v : ℂ) (hv : 0 ≤ v.re) : 0 < ((k : ℂ) * (a + v)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,Complex.add_re]
    positivity
  have hsamp (v : ℂ) (t : ℝ) : Complex.exp (-((k : ℂ)*(a+v))*t) *
      (∫ y : ℝ, W y * Complex.exp (-(((k*y : ℝ) : ℂ)*Complex.I)*t)) =
      C*(H (k*t) * Complex.exp (-((k : ℂ)*(1/2+v))*t)) := by
    have hphase (y : ℝ) : -(((k*y : ℝ) : ℂ)*Complex.I)*(t : ℂ) =
      -((y : ℂ)*Complex.I)*((k*t : ℝ) : ℂ) := by push_cast; ring
    simp_rw [hphase]
    rw [hInv (k*t)]
    have hExp : Complex.exp (-((k : ℂ)*(a+v))*t) * Complex.exp ((d : ℂ)*((k*t : ℝ) : ℂ)) =
        Complex.exp (-((k : ℂ)*(1/2+v))*t) := by
      rw [← Complex.exp_add]; dsimp only [d]; push_cast; congr 1; ring
    change _ = (2 * (Real.pi : ℂ)) * _
    rw [← hExp]
    ring
  have hsamp' (t : ℝ) : Complex.exp (-((k : ℂ)*(a+b'))*t) *
      (∫ y : ℝ, W y * Complex.exp (-(((k*y : ℝ) : ℂ)*Complex.I)*t)) =
      C*(H (-(k*t)) * Complex.exp (-((k : ℂ)*(1/2+b'))*t)) := by rw [hev]; exact hsamp b' t
  obtain ⟨hI,hpair⟩ := pairedLine W W _ _ _ _ (hr b hb) (hr b' hb') k C
    ((k : ℂ)*(Real.log Q : ℂ)) hC H hW0 hW0 (hsamp b) hsamp'
  refine ⟨hI, ?_⟩
  let s (y : ℝ) : ℂ := a+y*Complex.I
  have harg (y : ℝ) : s y - 1/2 = (d : ℂ)+y*Complex.I := by dsimp [s,d];push_cast;ring
  have hplus (y : ℝ) : bilateralLaplace H (s y-1/2) = W y := by rw [harg, hW]
  have hminus (y : ℝ) : bilateralLaplace H (1/2-s y) = W y := by
    rw [← neg_sub (s y), laplace_even H hev, hplus]
  have hD (v : ℂ) (hv : 0 ≤ v.re) (y : ℝ) : logDeriv (gammaAtom k Q v) (s y) =
      (k : ℂ)*Complex.digamma ((k : ℂ)*(a+v) + ((k*y : ℝ) : ℂ)*Complex.I) - k*(Real.log Q : ℂ) := by
    have hw : (k : ℂ)*(s y+v) = (k : ℂ)*(a+v) + ((k*y : ℝ) : ℂ)*Complex.I := by
      dsimp only [s]; push_cast;ring
    rw [logDeriv_gammaAtom, hw]
    rw [hw]
    simpa using hr v hv
  change (Complex.I * (∫ y : ℝ, bilateralLaplace H (s y-1/2) * logDeriv (gammaAtom k Q b) (s y)) +
    Complex.I * (∫ y : ℝ, bilateralLaplace H (1/2-s y) * logDeriv (gammaAtom k Q b') (s y))) /
      (C * Complex.I) = _
  simp_rw [hplus,hminus,hD b hb,hD b' hb']
  have hcancel (x y : ℂ) : (Complex.I*x+Complex.I*y)/(C*Complex.I)=(x+y)/C := by
    field_simp [Complex.I_ne_zero,hC]
  rw [hcancel,hpair]

end RiemannMasullo.ArchPV

end

section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology
set_option quotPrecheck false

namespace RiemannMasullo.ArchPV
variable {F : Type*} [Field F] [NumberField F]
local notation "C₀" => IdeleClassGroup (𝓞 F) F
local notation "U₀" => PontryaginDual C₀
local notation "Chars(" τ ")" => {η : U₀ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}

local instance kernelsInstance1 : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance kernelsInstance2 : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance kernelsInstance3 : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance kernelsInstance4 : MeasurableSpace (MonoidHom.ker (ideleClassNorm F)) := borel _
attribute [local instance] Classical.propDecidable

/-- The physical Gauss integral at a real or complex place, including its local identity term. -/
def localKernelTerm (χ : U₀) (w : InfinitePlace F) (H : ℝ → ℂ) : ℂ :=
  if hw : w.IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
      ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) H t) -
        (Real.log Real.pi : ℂ) * H 0
  else
    let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
      (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2) (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) H t) -
        2 * (Real.log (2 * Real.pi) : ℂ) * H 0

private theorem localKernelTerm_zero (η : U₀) (w : InfinitePlace F) :
    localKernelTerm η w 0 = 0 := by
  unfold localKernelTerm
  split <;> simp [heckeArchimedeanDigammaKernel]

/-- The archimedean computations use the ordinary local test selected by the global restriction
map. The moment hypotheses state that the single isotype is the logarithmic profile H. -/
private theorem localKernelTerm_eq_neg_PV (τ : ℝ≥0ˣ →ₜ* C₀) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C₀) (H : 𝓢(ℝ, ℂ)) (hH : ExponentialDecay H)
    (hM : ∀ (η : Chars(τ)) (s : ℂ), (∫ g : C₀, φ.val g * ideleClassNormTwist η.val s g *
      ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-(1/2 : ℂ))) ∂ideleClassTamagawaMeasure F) /
        ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) =
      if η = χ then mellin (fun t : ℝ ↦ H (Real.log t)) (s - 1 / 2) else 0)
    (w : InfinitePlace F) :
    localKernelTerm χ.val w H = -infiniteConnesWeilPrincipalValue w
      ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose φ) := by
  classical
  let T (η : Chars(τ)) : 𝓢(ℝ, ℂ) := if η = χ then H else 0
  have hz : ExponentialDecay (0 : 𝓢(ℝ, ℂ)) := by
    have hD (j : ℕ) : iteratedDeriv j ((0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 0 := by
      ext x
      simp
    constructor <;> intro j a ha <;> rw [hD] <;> exact Asymptotics.isBigO_zero _ _
  have hT (η : Chars(τ)) : ExponentialDecay (T η) := by
    by_cases h : η = χ
    · simpa [T,h] using hH
    · simpa [T,h] using hz
  have hN (η : Chars(τ)) (s : ℂ) : (∫ g : C₀, φ.val g * ideleClassNormTwist η.val s g *
      ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-1/2 : ℂ)) ∂ideleClassTamagawaMeasure F) /
        ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) =
      mellin (fun t : ℝ ↦ T η (Real.log t)) (s - 1 / 2) := by
    by_cases h : η = χ
    · simpa [h, T, neg_div] using hM η s
    · simpa [h, T, neg_div, mellin] using hM η s
  let A := (idelicExplicitFormula_infiniteTestMap (F := F) w).choose φ
  have hA (u : w.Completionˣ) : A.val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u) :=
    (idelicExplicitFormula_infiniteTestMap (F := F) w).choose_spec φ u
  have hA1 : A.val 1 = φ.val 1 := by rw [hA, map_one]
  have hsum : HasSum (fun η : Chars(τ) ↦ localKernelTerm η.val w (T η))
      (-infiniteConnesWeilPrincipalValue w A) := by
    by_cases hw : w.IsReal
    · have hlocal := idelicExplicitFormula_infiniteMatching_realLocal w hw A
      have h := idelicExplicitFormula_infiniteMatching_realCharacterSum τ hτ φ w hw T hT hN
      simp only [← hA, ← hA1] at h
      simp only at hlocal
      rw [hlocal] at h
      exact h
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hlocal := idelicExplicitFormula_infiniteMatching_complexLocal w hc A
      have h := idelicExplicitFormula_infiniteMatching_complexCharacterSum τ hτ φ w hc T hT hN
      simp only [← hA, ← hA1] at h
      simp only at hlocal
      rw [hlocal] at h
      exact h
  have hone : HasSum (fun η : Chars(τ) ↦ localKernelTerm η.val w (T η))
      (localKernelTerm χ.val w H) := by
    have h := hasSum_single (f := fun η : Chars(τ) ↦ localKernelTerm η.val w (T η)) χ
      (fun η h ↦ by simpa only [T, ite_eq_right h, FunLike.coe_zero] using localKernelTerm_zero η.val w)
    simpa [T] using h
  exact hone.unique hsum

end RiemannMasullo.ArchPV

end

section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology
set_option quotPrecheck false

namespace RiemannMasullo.ArchPV
variable {F : Type*} [Field F] [NumberField F]
local notation "C₀" => IdeleClassGroup (𝓞 F) F
local notation "U₀" => PontryaginDual C₀
local notation "Chars(" τ ")" => {η : U₀ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "N(" g ")" => (((ideleClassNorm F g).val : ℝ))
local notation "volC" => ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
local instance characterInstance1 : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance characterInstance2 : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance characterInstance3 : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance characterInstance4 : MeasurableSpace (MonoidHom.ker (ideleClassNorm F)) := borel _
attribute [local instance] Classical.propDecidable

private theorem volume_ne : volC ≠ 0 := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have hs : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨(ENNReal.ofReal_pos.mpr (by positivity)).ne', ENNReal.ofReal_ne_top⟩)

/-- Single-character orthogonality for the literal inverse-character log-norm test in §12.5. -/
private theorem singleCharacterMoments (τ : ℝ≥0ˣ →ₜ* C₀) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C₀) (H : ℝ → ℂ)
    (hφ : ∀ g, φ.val g = (χ.val⁻¹ g : ℂ) * H (Real.log N(g)))
    (η : Chars(τ)) (s : ℂ) :
    (∫ g : C₀, φ.val g * ideleClassNormTwist η.val s g *
      ((N(g) : ℂ) ^ (-(1/2 : ℂ))) ∂ideleClassTamagawaMeasure F) / volC =
        if η = χ then mellin (fun t : ℝ ↦ H (Real.log t)) (s-1/2) else 0 := by
  let : BorelSpace C₀ := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let T (g : C₀) := φ.val g * ideleClassNormTwist η.val (s-1/2) g
  have hT (g : C₀) : φ.val g * ideleClassNormTwist η.val s g * ((N(g) : ℂ) ^ (-(1/2 : ℂ))) = T g := by
    change φ.val g * ((η.val g : ℂ) * ((N(g):ℂ)^s)) * _ = φ.val g * ((η.val g : ℂ) * ((N(g):ℂ)^(s-1/2)))
    have hn : (N(g) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
    rw [sub_eq_add_neg,Complex.cpow_add _ _ hn]; ring
  have hIntro (g : C₀) : φ.val g = introTraceTest χ.val (fun t ↦ H (Real.log t)) g := by
    rw [hφ, introTraceTest, show χ.val⁻¹ g = (χ.val g)⁻¹ from rfl,Circle.coe_inv_eq_conj]
    rfl
  simp_rw [hT]
  split_ifs with he
  · subst η
    have h := (introTraceTest_mellin χ.val (fun t ↦ H (Real.log t)) φ hIntro (s-1/2)).2
    change (∫ g, T g ∂ideleClassTamagawaMeasure F) = volC * _ at h
    rw [h,mul_div_cancel_left₀ _ volume_ne]
    rfl
  · have hne : η.val ≠ χ.val := fun h ↦ he (Subtype.ext h)
    obtain ⟨u, hu⟩ : ∃ u, η.val u ≠ χ.val u := not_forall.mp fun h ↦ hne (DFunLike.ext _ _ h)
    let y : (ideleClassNorm F).ker := ⟨u * (τ (ideleClassNorm F u))⁻¹, by
      change ideleClassNorm F _ = 1
      rw [map_mul,map_inv,hτ,mul_inv_cancel]⟩
    have hχy : χ.val y.val = χ.val u := by simp [y,χ.property]
    have hηy : η.val y.val = η.val u := by simp [y,η.property]
    let z : ℂ := star (χ.val y.val : ℂ) * (η.val y.val : ℂ)
    have hz : z ≠ 1 := by
      intro heq
      have hp : (χ.val y.val : ℂ) * star (χ.val y.val : ℂ) = 1 := by simp [← Circle.coe_inv_eq_conj]
      have hh : (η.val y.val : ℂ) = (χ.val y.val : ℂ) := by
        dsimp only [z] at heq
        linear_combination (χ.val y.val : ℂ)*heq - (η.val y.val : ℂ)*hp
      exact hu (Subtype.ext (by simpa only [hηy,hχy] using hh))
    have htranslate (g : C₀) : T (y.val * g) = z * T g := by
      rw [mul_comm y.val g]
      have hchar : ideleClassNormTwist η.val (s-1/2) y.val = (η.val y.val : ℂ) := by
        change (η.val y.val : ℂ) * ((N(y.val):ℂ)^(s-1/2)) = _
        simp [show ideleClassNorm F y.val = 1 from y.property]
      simp only [T,z,map_mul,hchar,hIntro,introTraceTest_mul_normOne]
      ring
    have hsame : (∫ g, T g ∂ideleClassTamagawaMeasure F) = z * ∫ g, T g ∂ideleClassTamagawaMeasure F := by
      calc
        _ = ∫ g, T (y.val*g) ∂ideleClassTamagawaMeasure F := (integral_mul_left_eq_self (μ := ideleClassTamagawaMeasure F) T y.val).symm
        _ = _ := by rw [← integral_const_mul]; exact integral_congr_ae (.of_forall htranslate)
    have hzero : (∫ g, T g ∂ideleClassTamagawaMeasure F) = 0 :=
      (mul_eq_zero.mp (show (1-z) * (∫ g, T g ∂ideleClassTamagawaMeasure F) = 0 by linear_combination hsame)).resolve_left
        (fun h ↦ hz (sub_eq_zero.mp h).symm)
    rw [hzero, zero_div]

end RiemannMasullo.ArchPV

end

section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology
set_option quotPrecheck false

namespace RiemannMasullo.ArchPV
variable {F : Type*} [Field F] [NumberField F]
local notation "C₀" => IdeleClassGroup (𝓞 F) F
local notation "U₀" => PontryaginDual C₀
local notation "Chars(" τ ")" => {η : U₀ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
attribute [local instance] Classical.propDecidable

/-- The literal factor in the defining product of the all-field Hecke gamma factor. -/
def placeGamma (χ : U₀) (w : InfinitePlace F) (s : ℂ) : ℂ :=
  if hw : w.IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    Complex.Gammaℝ (s + p.1 + p.2.val)
  else
    let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    Complex.Gammaℂ (s + p.1 + (p.2.natAbs : ℂ)/2)/2

/-- The global Hecke gamma factor is the product of the place factors used in the two vertical integrals. -/
theorem heckeGammaFactor_eq_prod (χ : U₀) (s : ℂ) :
    heckeGammaFactor χ s = ∏ w : InfinitePlace F, placeGamma χ w s := by rw [heckeGammaFactor]; rfl

private theorem invLocal (χ : U₀) (w : InfinitePlace F) (u : w.Completionˣ) :
    infinitePlaceRestriction F w (ideleClassNormTwist χ⁻¹ 0) u =
    (infinitePlaceRestriction F w (ideleClassNormTwist χ 0) u)⁻¹ := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F w u
  change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
  simp only [Complex.cpow_zero, mul_one]
  rfl

private theorem realParams (χ : U₀) (w : InfinitePlace F) (hw : w.IsReal) :
    (realHeckeCharacter_parameters χ⁻¹ w hw).exists.choose =
    (-(realHeckeCharacter_parameters χ w hw).exists.choose.1,
      (realHeckeCharacter_parameters χ w hw).exists.choose.2) := by
  have h := (realHeckeCharacter_parameters χ w hw).exists.choose_spec
  apply (realHeckeCharacter_parameters χ⁻¹ w hw).unique (realHeckeCharacter_parameters χ⁻¹ w hw).exists.choose_spec
  refine ⟨by simpa using h.1, fun x ↦ ?_⟩
  dsimp only
  rw [invLocal,h.2 x,mul_inv,Complex.cpow_neg]
  congr 1
  rw [← inv_pow]
  split <;> simp

private theorem complexParams (χ : U₀) (w : InfinitePlace F) (hw : w.IsComplex) :
    (complexHeckeCharacter_parameters χ⁻¹ w hw).exists.choose =
    (-(complexHeckeCharacter_parameters χ w hw).exists.choose.1,
     -(complexHeckeCharacter_parameters χ w hw).exists.choose.2) := by
  have h := (complexHeckeCharacter_parameters χ w hw).exists.choose_spec
  apply (complexHeckeCharacter_parameters χ⁻¹ w hw).unique
    (complexHeckeCharacter_parameters χ⁻¹ w hw).exists.choose_spec
  refine ⟨by simpa using h.1, fun x ↦ ?_⟩
  dsimp only
  rw [invLocal,h.2 x,mul_inv,Complex.cpow_neg,zpow_neg]

/-- The actual two local vertical integrals, scaled by the full complex orientation. -/
def placeGammaLines (χ : U₀) (w : InfinitePlace F) (H : ℝ → ℂ) (a : ℝ) : ℂ :=
  (verticalLineIntegral (fun s ↦ bilateralLaplace H (s-1/2) * logDeriv (placeGamma χ w) s) a +
   verticalLineIntegral (fun s ↦ bilateralLaplace H (1/2-s) * logDeriv (placeGamma χ⁻¹ w) s) a) /
    (2*(Real.pi : ℂ)*Complex.I)

/-- Independent evaluation of the paired lines for both possible archimedean completions. -/
theorem placeGammaLines_eq_localKernel (χ : U₀) (w : InfinitePlace F) {a : ℝ} (ha : 0 < a)
    (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ)) (hH : ExponentialDecay H)
    (hev : ∀ x, H (-x) = H x) :
    placeGammaLines χ w H a = localKernelTerm χ w H := by
  classical
  unfold placeGammaLines localKernelTerm
  split
  · rename_i hw
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    let m : ℂ := p.2.val
    have hl : p.1.re = 0 := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
    have hshift (u : ℂ) (hu : u.re = 0) : 0 ≤ (u+m).re := by simp [m,hu]
    have h₁ : placeGamma χ w = gammaAtom (1/2) Real.pi (p.1+m) := by
      ext s
      rw [gammaAtom_real,placeGamma,dite_eq_left hw]
      exact congrArg Complex.Gammaℝ (add_assoc _ _ _)
    have h₂ : placeGamma χ⁻¹ w = gammaAtom (1/2) Real.pi (-p.1+m) := by
      ext s
      rw [gammaAtom_real,placeGamma,dite_eq_left hw]
      dsimp only
      rw [realParams χ w hw]
      exact congrArg Complex.Gammaℝ (add_assoc _ _ _)
    rw [h₁,h₂]
    have h := (gammaAtom_paired_vertical ha (show (0 : ℝ)<1/2 by norm_num) Real.pi (p.1+m)
      (-p.1+m) (hshift _ hl) (hshift _ (by simp [hl])) H hS hH hev).2
    convert h using 1
    change (∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (1/2) ((1/2+p.1+m)/2)
      ((1/2-p.1+m)/2) H t) - (Real.log Real.pi : ℂ)*H 0 = _
    congr 1
    · congr 1; ext t; congr 1 <;> push_cast <;> ring
    · push_cast; ring
  · rename_i hw
    have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let p := (complexHeckeCharacter_parameters χ w hc).exists.choose
    let m : ℂ := (p.2.natAbs : ℂ)/2
    have hl : p.1.re = 0 := (complexHeckeCharacter_parameters χ w hc).exists.choose_spec.1
    have hshift (u : ℂ) (hu : u.re=0) : 0 ≤ (u+m).re := by simp [m,hu]; positivity
    have h₁ : placeGamma χ w = gammaAtom 1 (2*Real.pi) (p.1+m) := by
      ext s
      simp [placeGamma,hw,gammaAtom_complex,p,m,add_assoc]
    have h₂ : placeGamma χ⁻¹ w = gammaAtom 1 (2*Real.pi) (-p.1+m) := by
      ext s
      rw [gammaAtom_complex,placeGamma,dite_eq_right hw]
      dsimp only
      rw [complexParams χ w hc]
      simp only [Int.natAbs_neg,add_assoc,p,m]
    rw [h₁,h₂]
    have h := (gammaAtom_paired_vertical ha (show (0 : ℝ)<1 by norm_num) (2*Real.pi) (p.1+m)
      (-p.1+m) (hshift _ hl) (hshift _ (by simp [hl])) H hS hH hev).2
    simpa only [Complex.ofReal_one, one_mul, ← add_assoc, ← sub_eq_add_neg] using h

end RiemannMasullo.ArchPV

end

section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology
set_option quotPrecheck false

namespace RiemannMasullo.ArchPV
variable {F : Type*} [Field F] [NumberField F]
local notation "C₀" => IdeleClassGroup (𝓞 F) F
local notation "U₀" => PontryaginDual C₀
local notation "Chars(" τ ")" => {η : U₀ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}

local instance allplacesInstance1 : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance allplacesInstance2 : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance allplacesInstance3 : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance allplacesInstance4 : MeasurableSpace (MonoidHom.ker (ideleClassNorm F)) := borel _
attribute [local instance] Classical.propDecidable

/-- The actual archimedean principal value equals minus the two oriented gamma integrals
for every archimedean place and every even compactly supported logarithmic test. -/
theorem actualPV_eq_neg_gammaLines (τ : ℝ≥0ˣ →ₜ* C₀) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C₀) (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ))
    (hH : ExponentialDecay H) (hev : ∀ x, H (-x) = H x)
    (hφ : ∀ g, φ.val g = (χ.val⁻¹ g : ℂ) * H (Real.log ((ideleClassNorm F g).val : ℝ)))
    (w : InfinitePlace F) {a : ℝ} (ha : 0 < a) :
    infiniteConnesWeilPrincipalValue w ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose φ) =
      -placeGammaLines χ.val w H a := by
  have h := localKernelTerm_eq_neg_PV τ hτ χ φ H hH (singleCharacterMoments τ hτ χ φ H hφ) w
  rw [placeGammaLines_eq_localKernel χ.val w ha H hS hH hev,h,neg_neg]

end RiemannMasullo.ArchPV

end

section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology
set_option quotPrecheck false
namespace RiemannMasullo.ArchPV
variable {F : Type*} [Field F] [NumberField F]
local notation "C₀" => IdeleClassGroup (𝓞 F) F
local notation "U₀" => PontryaginDual C₀
local notation "Chars(" τ ")" => {η : U₀ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
attribute [local instance] Classical.propDecidable

private theorem placeGamma_atom (χ : U₀) (w : InfinitePlace F) :
    ∃ k Q : ℝ, ∃ b : ℂ, 0<k ∧ 0≤b.re ∧ placeGamma χ w = gammaAtom k Q b := by
  by_cases hw : w.IsReal
  · let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    have h : p.1.re = 0 := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
    refine ⟨1/2,Real.pi,p.1+p.2.val,by norm_num,by simp [h],?_⟩
    ext s
    rw [placeGamma,dite_eq_left hw,gammaAtom_real];exact congrArg Complex.Gammaℝ (add_assoc _ _ _)
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let p := (complexHeckeCharacter_parameters χ w hc).exists.choose
    have h : p.1.re = 0 := (complexHeckeCharacter_parameters χ w hc).exists.choose_spec.1
    refine ⟨1,2*Real.pi,p.1+(p.2.natAbs : ℂ)/2,zero_lt_one,?_,?_⟩
    · simp [h];positivity
    · ext s;rw [placeGamma,dite_eq_right hw,gammaAtom_complex];simp [p,add_assoc]

private theorem placeGamma_right (χ : U₀) (w : InfinitePlace F) {s : ℂ} (hs : 0<s.re) :
    placeGamma χ w s ≠ 0 ∧ DifferentiableAt ℂ (placeGamma χ w) s := by
  obtain ⟨k,Q,b,hk,hb,h⟩ := placeGamma_atom χ w
  rw [h]
  have hp : 0<((k : ℂ)*(s+b)).re := by simpa using mul_pos hk (add_pos_of_pos_of_nonneg hs hb)
  have hc : DifferentiableAt ℂ (fun z : ℂ ↦ (k : ℂ)*(z+b)) s := by fun_prop
  refine ⟨?_,?_⟩
  · rw [gammaAtom]
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero_of_re_pos hp)
  · have hg : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.Gamma ((k : ℂ)*(z+b))) s :=
      (Complex.hasDerivAt_Gamma_of_re_pos hp).differentiableAt.comp s hc
    have he : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.exp (-(Real.log Q : ℂ)*((k : ℂ)*(z+b)))) s := by fun_prop
    change DifferentiableAt ℂ (fun z : ℂ ↦ Complex.exp (-(Real.log Q : ℂ)*((k : ℂ)*(z+b))) * Complex.Gamma ((k : ℂ)*(z+b))) s
    exact he.mul hg

private theorem local_integrable (W : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0<a) (χ : U₀) (w : InfinitePlace F) :
    Integrable (fun y : ℝ ↦ W y*logDeriv (placeGamma χ w) ((a : ℂ)+y*Complex.I)) := by
  obtain ⟨k,Q,b,hk,hb,h⟩ := placeGamma_atom χ w
  let A : ℂ := (k : ℂ)*((a : ℂ)+b)
  have hA : 0<A.re := by simp [A,Complex.mul_re];positivity
  have hψ := (schwartz_digamma_fubini W A hA k).1
  have hi := (hψ.mul_const (k : ℂ)).add (W.integrable (μ := volume) |>.mul_const ((k : ℂ)*(Complex.digamma 1-(Real.log Q : ℂ))))
  refine hi.congr (.of_forall fun y ↦ ?_)
  have he : (k : ℂ)*((a+y*Complex.I)+b)=A+((k*y : ℝ):ℂ)*Complex.I := by dsimp only [A];push_cast;ring
  simp only [h,Pi.add_apply,logDeriv_gammaAtom _ _ _ _ (by rw [he];simpa using hA),he]
  ring

/-- Finite-product splitting for exactly the paired vertical integrals of the global gamma factor. -/
theorem globalGammaLines_eq_sum (χ : U₀) (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ))
    (hH : ExponentialDecay H) (hev : ∀ x, H (-x)=H x) {a : ℝ} (ha : 0<a) :
    (verticalLineIntegral (fun s ↦ bilateralLaplace H (s-1/2)*logDeriv (heckeGammaFactor χ) s) a +
      verticalLineIntegral (fun s ↦ bilateralLaplace H (1/2-s)*logDeriv (heckeGammaFactor χ⁻¹) s) a) /
        (2*(Real.pi : ℂ)*Complex.I) = ∑ w : InfinitePlace F, placeGammaLines χ w H a := by
  classical
  let s (y : ℝ) : ℂ := a+y*Complex.I
  obtain ⟨W,hW,_⟩ := exists_schwartz_Laplace_samples H hS hH (a-1/2)
  have hp (y : ℝ) : bilateralLaplace H (s y-1/2) = W y := by
    rw [hW];congr 1;dsimp only [s];push_cast;ring
  have hm (y : ℝ) : bilateralLaplace H (1/2-s y) = W y := by rw [← neg_sub (s y),laplace_even H hev,hp]
  have hprod (ψ : U₀) : heckeGammaFactor ψ = fun z ↦ ∏ w, placeGamma ψ w z :=
    funext (heckeGammaFactor_eq_prod ψ)
  have hx (ψ : U₀) (y : ℝ) : W y*logDeriv (heckeGammaFactor ψ) (s y) =
      ∑ w, W y*logDeriv (placeGamma ψ w) (s y) := by
    have hpos : 0<(s y).re := by simpa [s] using ha
    rw [hprod,logDeriv_fun_prod (fun w _ ↦ (placeGamma_right ψ w hpos).1) (fun w _ ↦ (placeGamma_right ψ w hpos).2),Finset.mul_sum]
  simp only [placeGammaLines,verticalLineIntegral]
  change (Complex.I*(∫ y : ℝ, bilateralLaplace H (s y-1/2)*logDeriv (heckeGammaFactor χ) (s y))+
    Complex.I*(∫ y : ℝ, bilateralLaplace H (1/2-s y)*logDeriv (heckeGammaFactor χ⁻¹) (s y))) /
      (2*(Real.pi : ℂ)*Complex.I)=∑ w : InfinitePlace F,
      (Complex.I*(∫ y : ℝ, bilateralLaplace H (s y-1/2)*logDeriv (placeGamma χ w) (s y))+
       Complex.I*(∫ y : ℝ, bilateralLaplace H (1/2-s y)*logDeriv (placeGamma χ⁻¹ w) (s y))) / _
  simp_rw [hp,hm,hx χ,hx χ⁻¹]
  rw [integral_finsetSum _ (fun w _ ↦ local_integrable W ha χ w),
    integral_finsetSum _ (fun w _ ↦ local_integrable W ha χ⁻¹ w),Finset.mul_sum,Finset.mul_sum,
    ← Finset.sum_add_distrib,Finset.sum_div]

local instance globalInstance1 : T2Space C₀ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance globalInstance2 : LocallyCompactSpace C₀ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

/-- Actual sum of restricted archimedean principal values against the genuine global
gamma factor at a and its contragredient. -/
theorem globalGammaLines_eq_neg_sum_actualPV (τ : ℝ≥0ˣ →ₜ* C₀) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C₀) (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ))
    (hH : ExponentialDecay H) (hev : ∀ x, H (-x)=H x)
    (hφ : ∀ g, φ.val g = (χ.val⁻¹ g : ℂ) * H (Real.log ((ideleClassNorm F g).val : ℝ)))
    {a : ℝ} (ha : 0<a) :
    (verticalLineIntegral (fun s ↦ bilateralLaplace H (s-1/2)*logDeriv (heckeGammaFactor χ.val) s) a +
      verticalLineIntegral (fun s ↦ bilateralLaplace H (1/2-s)*logDeriv (heckeGammaFactor χ.val⁻¹) s) a) /
        (2*(Real.pi : ℂ)*Complex.I) = -∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w
          ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose φ) := by
  rw [globalGammaLines_eq_sum χ.val H hS hH hev ha,← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun w _ ↦ by rw [actualPV_eq_neg_gammaLines τ hτ χ φ H hS hH hev hφ w ha,neg_neg])

end RiemannMasullo.ArchPV

end

section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology
set_option quotPrecheck false
namespace RiemannMasullo.ArchPV
variable {F : Type*} [Field F] [NumberField F]
local notation "C₀" => IdeleClassGroup (𝓞 F) F
local notation "U₀" => PontryaginDual C₀
local notation "Chars(" τ ")" => {η : U₀ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local instance primefreeInstance1 : T2Space C₀ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance primefreeInstance2 : LocallyCompactSpace C₀ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

open scoped Asymptotics
open Filter

/-- A compactly supported Schwartz function has exponential decay to every derivative order. -/
theorem exponentialDecay_of_compact (f : _root_.SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ExponentialDecay f := by
  have hc (n : ℕ) : HasCompactSupport (iteratedDeriv n (f : ℝ → ℂ)) := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hbound {l : Filter ℝ} (hl : l ≤ cocompact ℝ) (n : ℕ) (g : ℝ → ℝ) :
      iteratedDeriv n (f : ℝ → ℂ) =O[l] g := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [(hasCompactSupport_iff_eventuallyEq.mp (hc n)).filter_mono
      (hl.trans cocompact_le_coclosedCompact)] with x hx
    simpa only [hx,Pi.zero_apply,norm_zero,one_mul] using norm_nonneg (g x)
  exact ⟨fun n A _ ↦ hbound atTop_le_cocompact n _, fun n A _ ↦ hbound atBot_le_cocompact n _⟩

/-- The signed completed divisor sum of an even test supported inside the prime-free interval
equals its conductor part minus the sum of the genuine restricted principal values. -/
theorem hasSum_short_actualPV (τ : ℝ≥0ˣ →ₜ* C₀) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C₀) (H : 𝓢(ℝ, ℂ)) (hS : HasCompactSupport (H : ℝ → ℂ))
    (hH : ExponentialDecay H) (hev : ∀ x, H (-x)=H x)
    (hφ : ∀ g, φ.val g = (χ.val⁻¹ g : ℂ) * H (Real.log ((ideleClassNorm F g).val : ℝ)))
    (hshort : ∀ x : ℝ, Real.log 2 ≤ |x| → H x = 0)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hAgree : ∀ s : {s : ℂ | 1<s.re}, L s = completedHeckeL χ.val s) :
    HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ)*bilateralLaplace H (ρ-1/2))
      ((heckeLogDiscriminantConductor χ.val : ℂ)* H 0 -
        ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w
          ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose φ)) := by
  have h := hasSum_heckeExplicitFormula_gammaLines_of_shortSupport χ.val H hH hshort L hL hAgree
  simp_rw [mellin_log_eq_Laplace] at h
  rw [globalGammaLines_eq_neg_sum_actualPV τ hτ χ φ H hS hH hev hφ (by norm_num : (0 : ℝ)<3/2)] at h
  simpa only [sub_eq_add_neg] using h

end RiemannMasullo.ArchPV

end
