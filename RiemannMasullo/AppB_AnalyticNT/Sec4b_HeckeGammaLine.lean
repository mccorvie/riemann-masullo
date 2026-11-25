module

public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeOuterLogDeriv
import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalCauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The two archimedean contours as a real critical-line integral -/

public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set
open scoped Asymptotics ComplexConjugate ContDiff FourierTransform SchwartzMap Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "BL(" H ", " z ")" =>
  bilateralLaplace (fun x : ℝ ↦ ((H : ℝ → ℝ) x : ℂ)) (z : ℂ)
local notation "line(" a ", " t ")" => ((a : ℂ) + (t : ℂ) * I)

private theorem realLaplace_conj (H : ℝ → ℝ) (z : ℂ) :
    BL(H, conj z) = conj (BL(H, z)) := by
  rw [bilateralLaplace, bilateralLaplace, ← integral_conj]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

private theorem evenLaplace_neg (H : ℝ → ℝ) (he : ∀ x, H (-x) = H x) (z : ℂ) :
    BL(H, -z) = BL(H, z) := by
  let f (x : ℝ) := (H x : ℂ) * Complex.exp (z * x)
  calc
    _ = ∫ x : ℝ, f (-x) := by
      apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [f, he, Complex.ofReal_neg, mul_neg, neg_mul]
    _ = _ := integral_neg_eq_self f volume

private theorem logarithmicGamma_inv_conj (χ : U𝔽) (s : ℂ) :
    logDeriv (heckeGammaFactor χ⁻¹) (conj s) = conj (logDeriv (heckeGammaFactor χ) s) := by
  have hf : heckeGammaFactor χ⁻¹ = conj ∘ heckeGammaFactor χ ∘ conj := by
    funext z
    simpa only [Function.comp_apply, Complex.conj_conj] using heckeGammaFactor_inv_conj χ (conj z)
  simp only [hf, logDeriv_apply, deriv_conj_conj, Function.comp_apply, Complex.conj_conj, map_div₀]

private theorem smoothCompact_mellin (H : ℝ → ℝ) (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    ∃ f : 𝓢(ℝ, ℂ), ExponentialDecay f ∧ ∀ z : ℂ,
      mellin (fun x ↦ f (Real.log x)) z = BL(H, z) := by
  have hsupport : HasCompactSupport (fun x : ℝ ↦ (H x : ℂ)) := hc.comp_left Complex.ofReal_zero
  let f : 𝓢(ℝ, ℂ) := hsupport.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs)
  have hfc : (f : ℝ → ℂ) = fun x : ℝ ↦ (H x : ℂ) := rfl
  have hder (n : ℕ) : HasCompactSupport (iteratedDeriv n (f : ℝ → ℂ)) := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero, hfc] using hsupport
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have bound {l : Filter ℝ} (hl : l ≤ cocompact ℝ) (n : ℕ) (g : ℝ → ℝ) :
      iteratedDeriv n (f : ℝ → ℂ) =O[l] g := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [(hasCompactSupport_iff_eventuallyEq.mp (hder n)).filter_mono
      (hl.trans cocompact_le_coclosedCompact)] with x hx
    simpa only [hx, Pi.zero_apply, norm_zero, one_mul] using norm_nonneg (g x)
  refine ⟨f, ⟨fun n _ _ ↦ bound atTop_le_cocompact n _, fun n _ _ ↦ bound atBot_le_cocompact n _⟩, ?_⟩
  intro z
  rw [mellin, bilateralLaplace, ← integral_comp_exp]
  apply integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  change Real.exp y • (((Real.exp y : ℝ) : ℂ) ^ (z-1) • (H (Real.log (Real.exp y)) : ℂ)) =
    (H y : ℂ) * Complex.exp (z * (y : ℂ))
  rw [Real.log_exp, Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add, show (y : ℂ) + y * (z - 1) = z * y by ring, mul_comm]

private theorem gammaTrace_integrable (χ : U𝔽) (H : ℝ → ℝ) (hs : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (a : ℝ) (ha : 0 < a) :
    Integrable fun t : ℝ ↦ BL(H, line(a,t) - 1/2) * logDeriv (heckeGammaFactor χ) (line(a,t)) := by
  obtain ⟨f, hf, hm⟩ := smoothCompact_mellin H hs hc
  simpa only [Complex.VerticalIntegrable, hm] using (heckeExplicitFormula_gammaLines_verticalIntegrable χ f hf a ha).1

/-- Paper: Equation (B.4.2.4), p. 615. Reconstruction: for a real even compact profile the two upward
gamma contours divided by `2πi` give the real part of one absolutely convergent integral
divided by `π`, at every positive abscissa. -/
theorem heckeGammaLines_eq_integral_re (χ : U𝔽) (H : ℝ → ℝ)
    (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (he : ∀ x, H (-x) = H x)
    (a : ℝ) (ha : 0 < a) :
    (verticalLineIntegral (fun z ↦ BL(H, z-1/2) * logDeriv (heckeGammaFactor χ) z) a +
      verticalLineIntegral (fun z ↦ BL(H, 1/2-z) * logDeriv (heckeGammaFactor χ⁻¹) z) a) /
        (2 * (Real.pi : ℂ) * I) =
      (((1 / Real.pi) * ∫ t : ℝ, (BL(H, line(a,t) - 1/2) *
        logDeriv (heckeGammaFactor χ) (line(a,t))).re : ℝ) : ℂ) := by
  let A (t : ℝ) := BL(H, line(a,t) - 1/2) * logDeriv (heckeGammaFactor χ) (line(a,t))
  let B (t : ℝ) := BL(H, 1/2 - line(a,t)) * logDeriv (heckeGammaFactor χ⁻¹) (line(a,t))
  have hi : Integrable A := gammaTrace_integrable χ H hs hc a ha
  have hb (t : ℝ) : B (-t) = conj (A t) := by
    have hl : (a : ℂ) + ((-t : ℝ) : ℂ) * I = conj (line(a,t)) := by simp [map_add, map_mul]
    have hz : (1/2 : ℂ) - conj (line(a,t)) = -conj (line(a,t) - 1/2) := by
      simp only [map_sub, map_div₀, map_one, map_ofNat]
      ring
    simp only [A, B, hl, hz, evenLaplace_neg H he, realLaplace_conj,
      logarithmicGamma_inv_conj, map_mul]
  have hB : ∫ t : ℝ, B t = conj (∫ t : ℝ, A t) := by
    rw [← integral_neg_eq_self B, ← integral_conj]
    exact integral_congr_ae (ae_of_all _ hb)
  change (I * (∫ t : ℝ, A t) + I * (∫ t : ℝ, B t)) / _ =
    (((1 / Real.pi) * ∫ t : ℝ, (A t).re : ℝ) : ℂ)
  have hre : (∫ t : ℝ, (A t).re) = (∫ t : ℝ, A t).re := integral_re hi
  rw [hB, ← mul_add, Complex.add_conj, hre]
  push_cast
  field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

private theorem gammaLine_horizontal_bound (χ : U𝔽) (H : ℝ → ℝ)
    (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ y : ℝ in comap abs atTop, ∀ σ ∈ Icc (1/2 : ℝ) (3/2),
      ‖(line(σ,y) - 1) * (BL(H, line(σ,y) - 1/2) *
        logDeriv (heckeGammaFactor χ) (line(σ,y)))‖ ≤ M / |y| := by
  obtain ⟨f, hf, hm⟩ := smoothCompact_mellin H hs hc
  obtain ⟨C, hC, hheight⟩ := mellin_heightBound_of_exponentialDecay f hf 0 1
    zero_lt_one 3 (by decide)
  obtain ⟨D, hD, hgamma⟩ := heckeGammaFactor_logDeriv_bound_of_re_ge χ (1/2) (by norm_num)
  refine ⟨20 * C * D, by positivity, ?_⟩
  have hy : ∀ᶠ y : ℝ in comap abs atTop, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [hy] with y hy σ hσ
  have hypos : 0 < |y| := zero_lt_one.trans_le hy
  have hn : y ≠ 0 := abs_pos.mp hypos
  have hx : 0 ≤ σ := by linarith [hσ.1]
  have hnorm : ‖line(σ,y)‖ ≤ 3 * |y| := by
    have ht := norm_add_le (σ : ℂ) ((y : ℂ) * I)
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hx] at ht
    linarith [hσ.2]
  have hfac : ‖line(σ,y) - 1‖ ≤ 4 * |y| := by
    have ha := norm_sub_le (line(σ,y)) 1
    rw [norm_one] at ha
    linarith
  have hΓ : ‖logDeriv (heckeGammaFactor χ) (line(σ,y))‖ ≤ D * (5 * |y|) := by
    apply (hgamma _ (by simpa using hσ.1)).trans
    apply mul_le_mul_of_nonneg_left _ hD.le
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + ‖line(σ,y)‖)
    linarith
  have hshift : line(σ,y) - 1/2 = (((σ - 1/2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    push_cast
    ring
  have hH : ‖BL(H, line(σ,y) - 1/2)‖ ≤ C / |y| ^ 3 := by
    rw [hshift, ← hm]
    exact hheight (σ - 1/2) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ y hn
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (4 * |y|) * ((C / |y| ^ 3) * (D * (5 * |y|))) :=
      mul_le_mul hfac (mul_le_mul hH hΓ (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = 20 * C * D / |y| := by field_simp; ring

private theorem gammaLine_integral_shift (χ : U𝔽) (H : ℝ → ℝ)
    (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    let A (z : ℂ) := BL(H, z-1/2) * logDeriv (heckeGammaFactor χ) z
    (∫ t : ℝ, A (line((3/2 : ℝ),t))) = ∫ t : ℝ, A (line((1/2 : ℝ),t)) := by
  intro A
  let Φ (z : ℂ) := (z - 1) * A z
  obtain ⟨f, hf, hm⟩ := smoothCompact_mellin H hs hc
  have hd : Differentiable ℂ (bilateralLaplace (fun x : ℝ ↦ (H x : ℂ))) := by
    rw [← funext hm]
    exact differentiable_mellin_of_exponentialDecay f hf
  have hΓ : DifferentiableOn ℂ (heckeGammaFactor χ) (Complex.re ⁻¹' Ioi (0 : ℝ)) :=
    fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hw).differentiableWithinAt
  have hΦ : DifferentiableOn ℂ Φ (Complex.re ⁻¹' Ioo (1/4 : ℝ) 2) := by
    intro w hw
    have hp : 0 < w.re := lt_trans (by norm_num : (0 : ℝ) < 1/4) hw.1
    have ha := hΓ.analyticAt ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hp)
    have hlog : DifferentiableAt ℂ (logDeriv (heckeGammaFactor χ)) w :=
      (ha.deriv.div ha (heckeGammaFactor_ne_zero_of_re_pos χ hp)).differentiableAt
    exact ((differentiableAt_id.sub_const 1).mul
      (((hd _).comp w (differentiableAt_id.sub_const (1/2))).mul hlog)).differentiableWithinAt
  obtain ⟨M, hM, hdecay⟩ := gammaLine_horizontal_bound χ H hs hc
  have hcancel (a : ℝ) (ha : a ≠ 1) (t : ℝ) :
      Φ (line(a,t)) / (line(a,t) - 1) = A (line(a,t)) := by
    have hne : line(a,t) ≠ 1 := fun h ↦ ha (by simpa using congrArg Complex.re h)
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hne)
  have hi (a : ℝ) (ha : 0 < a) (hn : a ≠ 1) :
      Complex.VerticalIntegrable (fun w ↦ Φ w / (w-1)) a := by
    simpa only [Complex.VerticalIntegrable, hcancel a hn] using gammaTrace_integrable χ H hs hc a ha
  have h := verticalCauchyIntegral_sub_eq (z := 1) hΦ (c := 1/2) (d := 3/2)
    (by norm_num) (by norm_num) (by norm_num [Set.mem_Ioo]) hM hdecay
    (hi _ (by norm_num) (by norm_num)) (hi _ (by norm_num) (by norm_num))
  have hzero : Φ 1 = 0 := by simp [Φ]
  rw [hzero, mul_zero] at h
  have h₃ := hcancel (3/2) (by norm_num)
  have h₁ := hcancel (1/2) (by norm_num)
  exact sub_eq_zero.mp (by simpa only [h₃, h₁] using h)

private theorem realLaplace_axis (H : ℝ → ℝ) (he : ∀ x, H (-x) = H x) (t : ℝ) :
    ((BL(H, (t : ℂ)*I)).re : ℂ) = BL(H, (t : ℂ)*I) := by
  apply Complex.conj_eq_iff_re.mp
  rw [← realLaplace_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
    evenLaplace_neg H he]

/-- Paper: Proposition B.2.1.9(2), p. 598, and Equation (B.4.2.4), p. 615.
Reconstruction: for a real even smooth compact profile the normalized pair of genuine Euler-line gamma
integrals is the real critical-line integral. Its weight is the real value of the bilateral
Laplace transform on the imaginary axis. -/
theorem heckeGammaLines_eq_criticalLine (χ : U𝔽) (H : ℝ → ℝ)
    (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (he : ∀ x, H (-x) = H x) :
    let W (t : ℝ) := (BL(H, (t : ℂ)*I)).re * (logDeriv (heckeGammaFactor χ) (line((1/2 : ℝ),t))).re
    Integrable W ∧
    (verticalLineIntegral (fun z ↦ BL(H, z-1/2) * logDeriv (heckeGammaFactor χ) z) (3/2) +
      verticalLineIntegral (fun z ↦ BL(H, 1/2-z) * logDeriv (heckeGammaFactor χ⁻¹) z) (3/2)) /
        (2 * (Real.pi : ℂ) * I) = (((1 / Real.pi) * ∫ t : ℝ, W t : ℝ) : ℂ) := by
  intro W
  let A (z : ℂ) := BL(H, z-1/2) * logDeriv (heckeGammaFactor χ) z
  have hpoint (t : ℝ) : (A (line((1/2 : ℝ),t))).re = W t := by
    have hz : line((1/2 : ℝ),t) - 1/2 = (t : ℂ) * I := by push_cast; ring
    dsimp only [A, W]
    rw [hz, ← realLaplace_axis H he t, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hi (a : ℝ) (ha : 0 < a) : Integrable (fun t : ℝ ↦ A (line(a,t))) :=
    gammaTrace_integrable χ H hs hc a ha
  have hre (a : ℝ) (ha : 0 < a) : (∫ t : ℝ, (A (line(a,t))).re) = (∫ t : ℝ, A (line(a,t))).re :=
    integral_re (hi a ha)
  refine ⟨(hi (1/2) (by norm_num)).re.congr (ae_of_all _ hpoint), ?_⟩
  rw [heckeGammaLines_eq_integral_re χ H hs hc he (3/2) (by norm_num)]
  congr 2
  change (∫ t : ℝ, (A (line((3/2 : ℝ),t))).re) = _
  rw [hre _ (by norm_num), gammaLine_integral_shift χ H hs hc, ← hre _ (by norm_num)]
  exact integral_congr_ae (ae_of_all _ hpoint)

end RiemannMasullo
