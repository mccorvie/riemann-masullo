module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic

/-! # Continuation of positive Laplace integrals -/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace RiemannMasullo

/-- A nonnegative measure with one positive exponential moment has exponential moments
throughout the positive real radius of any disk of holomorphic continuation of its transform
about zero. The initial agreement with the transform is only needed in a neighborhood of zero. -/
theorem integrable_exp_of_laplace_continuation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → ℝ) (hT : Measurable T) (hT₀ : ∀ a, 0 ≤ T a)
    {s r x : ℝ} (hs : 0 < s) (hM : Integrable (fun a ↦ Real.exp (s * T a)) μ)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 r))
    (heq : G =ᶠ[𝓝 (0 : ℂ)] fun z ↦ ∫ a, Complex.exp (z * (T a : ℂ)) ∂μ)
    (hx : 0 ≤ x) (hxr : x < r) : Integrable (fun a ↦ Real.exp (x * T a)) μ := by
  let b (n : ℕ) (a : α) := T a ^ n / (n.factorial : ℝ)
  let m (n : ℕ) := ∫ a, b n a ∂μ
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n ↦ (m n : ℂ))
  have hb (n a) : 0 ≤ b n a := by dsimp [b]; positivity [hT₀ a]
  have hbm (n) : Measurable (b n) := (hT.pow_const n).div_const _
  have hm (n) : 0 ≤ m n := integral_nonneg (hb n)
  have hexp (u : ℝ) (a : α) : HasSum (fun n ↦ b n a * u ^ n) (Real.exp (u * T a)) := by
    rw [Real.exp_eq_exp_ℝ]
    convert NormedSpace.expSeries_div_hasSum_exp (u * T a) using 1
    funext n
    simp only [b, mul_pow]
    ring
  have hint (n) : Integrable (b n) μ := by
    refine (hM.mul_const ((s ^ n)⁻¹)).mono' (hbm n).aestronglyMeasurable (ae_of_all _ fun a ↦ ?_)
    rw [Real.norm_of_nonneg (hb n a), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hs n)]
    exact (hexp s a).tsum_eq ▸ (hexp s a).summable.le_tsum n (fun k _ ↦ by positivity [hb k a])
  have hmass (u : ℝ) (hu : 0 ≤ u) :
      (∫⁻ a, ENNReal.ofReal (Real.exp (u * T a)) ∂μ) = ∑' n, ENNReal.ofReal (m n * u ^ n) := by
    calc
      _ = ∫⁻ a, ∑' n, ENNReal.ofReal (b n a * u ^ n) ∂μ := by
        apply lintegral_congr fun a ↦ ?_
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity [hb n a]) (hexp u a).summable,
          (hexp u a).tsum_eq]
      _ = ∑' n, ∫⁻ a, ENNReal.ofReal (b n a * u ^ n) ∂μ :=
        lintegral_tsum (fun n ↦ ((hbm n).mul measurable_const).ennreal_ofReal.aemeasurable)
      _ = _ := tsum_congr fun n ↦ by
        rw [← ofReal_integral_eq_lintegral_ofReal ((hint n).mul_const (u ^ n))
          (ae_of_all _ fun a ↦ by positivity [hb n a]), integral_mul_const]
  have hs₁ : Summable (fun n ↦ m n * s ^ n) := by
    have hf : (∑' n, ENNReal.ofReal (m n * s ^ n)) ≠ ∞ := by
      rw [← hmass s hs.le]
      exact (lintegral_ofReal_ne_top_iff_integrable hM.1 (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mpr hM
    have h := NNReal.summable_coe.mpr (ENNReal.summable_toNNReal_of_tsum_ne_top hf)
    change Summable (fun n ↦ (ENNReal.ofReal (m n * s ^ n)).toReal) at h
    simpa only [fun n ↦ ENNReal.toReal_ofReal (mul_nonneg (hm n) (pow_nonneg hs.le n))] using h
  let S : ℝ≥0 := ⟨s, hs.le⟩
  have hS_coe : (S : ℝ) = s := rfl
  have hS : 0 < S := hs
  have hp : HasFPowerSeriesOnBall (fun z : ℂ ↦ ∫ a, Complex.exp (z * (T a : ℂ)) ∂μ) p 0 S := by
    refine ⟨p.le_radius_of_summable (r := S) ?_, by exact_mod_cast hS, ?_⟩
    · simpa only [p, hS_coe, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
        Real.norm_of_nonneg (hm _)] using hs₁
    intro z hz
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hz
    have hs' : ‖z‖ ≤ s := hz.le
    have hB := hasSum_integral_of_summable_integral_norm (μ := μ)
      (F := fun n a ↦ (b n a : ℂ) * z ^ n) (fun n ↦ (hint n).ofReal.mul_const _) ?_
    · simp only [integral_mul_const, integral_complex_ofReal] at hB
      change HasSum (fun n ↦ (m n : ℂ) * z ^ n) _ at hB
      have hC (a : α) : (∑' n, (b n a : ℂ) * z ^ n) = Complex.exp (z * (T a : ℂ)) := by
        rw [Complex.exp_eq_exp_ℂ, ← (NormedSpace.expSeries_div_hasSum_exp (z * (T a : ℂ))).tsum_eq]
        refine tsum_congr fun n ↦ ?_
        simp only [b, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, mul_pow]
        ring
      simp_rw [hC] at hB
      simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hB
    · apply hs₁.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      intro n
      simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb n _), norm_pow, integral_mul_const]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs' n) (hm n)
  obtain ⟨r', hxr', hr'r⟩ := exists_between hxr
  let R : ℝ≥0 := ⟨r', hx.trans hxr'.le⟩
  have hR : 0 < R := hx.trans_lt hxr'
  have hGR := (hG.mono (Metric.closedBall_subset_ball hr'r)).hasFPowerSeriesOnBall hR
  have hGp := hGR.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hp.hasFPowerSeriesAt heq
  rw [hGp] at hGR
  have hxR : (x : ℂ) ∈ Metric.eball 0 (R : ℝ≥0∞) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_of_nonneg hx]
    exact hxr'
  have hsum := Complex.hasSum_re (hGR.hasSum hxR)
  have hxs : Summable (fun n ↦ m n * x ^ n) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] using hsum.summable
  apply (lintegral_ofReal_ne_top_iff_integrable (hT.const_mul x).exp.aestronglyMeasurable
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mp
  rw [hmass x hx, ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity [hm n]) hxs]
  exact ENNReal.ofReal_ne_top

/-- A positive Laplace integral that converges at a point to the left of `c` also
converges at every real point to the left of `c` inside a disk on which it continues
holomorphically. Agreement with the continuation is required only near `c`. -/
theorem integrable_exp_neg_of_laplace_continuation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → ℝ) (hT : Measurable T) (hT₀ : ∀ a, 0 ≤ T a)
    {c₀ c r x : ℝ} (hc : c₀ < c) (hM : Integrable (fun a ↦ Real.exp (-c₀ * T a)) μ)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball (c : ℂ) r))
    (heq : G =ᶠ[𝓝 (c : ℂ)] fun z ↦ ∫ a, Complex.exp (-z * (T a : ℂ)) ∂μ)
    (hx : x ≤ c) (hxr : c - x < r) : Integrable (fun a ↦ Real.exp (-x * T a)) μ := by
  let w (a : α) : ℝ≥0 := ⟨Real.exp (-c * T a), Real.exp_nonneg _⟩
  have hw : Measurable w := (hT.const_mul (-c)).exp.subtype_mk
  let ν := μ.withDensity (fun a ↦ (w a : ℝ≥0∞))
  have hTilt (u : ℝ) : Integrable (fun a ↦ Real.exp (u * T a)) ν ↔
      Integrable (fun a ↦ Real.exp ((u - c) * T a)) μ := by
    rw [integrable_withDensity_iff_integrable_coe_smul hw]
    have he (a : α) : (w a : ℝ) • Real.exp (u * T a) = Real.exp ((u - c) * T a) := by
      change Real.exp (-c * T a) * Real.exp (u * T a) = _
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [he]
  have hν : Integrable (fun a ↦ Real.exp ((c - c₀) * T a)) ν := by
    apply (hTilt _).mpr
    convert hM using 1
    funext a
    congr 1
    ring
  let R (z : ℂ) := (c : ℂ) - z
  have hR : Differentiable ℂ R := by dsimp [R]; fun_prop
  have hG' : DifferentiableOn ℂ (G ∘ R) (Metric.ball (0 : ℂ) r) := by
    apply hG.comp hR.differentiableOn
    intro z hz
    simp only [Metric.mem_ball, dist_eq_norm, R, sub_zero] at hz ⊢
    rwa [show (c : ℂ) - z - c = -z by ring, norm_neg]
  have hR' : Tendsto R (𝓝 (0 : ℂ)) (𝓝 (c : ℂ)) := by
    simpa [R] using (hR.continuous.continuousAt (x := (0 : ℂ))).tendsto
  have hEq' : G ∘ R =ᶠ[𝓝 (0 : ℂ)] fun z ↦ ∫ a, Complex.exp (z * (T a : ℂ)) ∂ν := by
    filter_upwards [heq.comp_tendsto hR'] with z hz
    change G (R z) = ∫ a, Complex.exp (-R z * (T a : ℂ)) ∂μ at hz
    change G (R z) = _
    rw [hz, integral_withDensity_eq_integral_smul hw]
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    change Complex.exp (-R z * (T a : ℂ)) = (w a : ℝ) • Complex.exp (z * (T a : ℂ))
    rw [Complex.real_smul]
    change Complex.exp (-R z * (T a : ℂ)) = (Real.exp (-c * T a) : ℂ) * _
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    congr 1
    dsimp [R]
    ring
  have hi := integrable_exp_of_laplace_continuation ν T hT hT₀ (sub_pos.mpr hc) hν hG' hEq'
    (sub_nonneg.mpr hx) hxr
  convert (hTilt _).mp hi using 1
  funext a
  congr 1
  ring

private theorem analyticOnNhd_laplaceIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → ℝ) (hT : Measurable T) (a : ℝ)
    (hD : ∀ u : ℝ, a < u → Integrable (fun y ↦ Real.exp (-u * T y)) μ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ y, Complex.exp (-z * (T y : ℂ)) ∂μ) {z | a < z.re} := by
  let N (y : α) := Real.exp (-T y)
  have hN (y : α) : 0 < N y := Real.exp_pos _
  have hpow (z : ℂ) (y : α) : (N y : ℂ) ^ z = Complex.exp (-z * (T y : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hN y).ne'),
      ← Complex.ofReal_log (hN y).le, show Real.log (N y) = -T y by simp [N], Complex.ofReal_neg]
    congr 1
    ring
  have hint (z : ℂ) (hz : z.re ∈ Ioi a) : Integrable (fun y ↦ (1 : ℂ) * (N y : ℂ) ^ z) μ := by
    simp only [one_mul, hpow]
    have hm : Measurable (fun y ↦ Complex.exp (-z * (T y : ℂ))) :=
      Complex.continuous_exp.measurable.comp (hT.complex_ofReal.const_mul (-z))
    refine (hD _ hz).mono' hm.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
    simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, le_refl]
  have h := analyticOnNhd_integral_mul_cpow_of_integrable μ (fun _ ↦ (1 : ℂ)) N
    hT.neg.exp hN isOpen_Ioi hint
  change AnalyticOnNhd ℂ _ (Complex.re ⁻¹' Ioi a)
  simpa only [one_mul, hpow] using h

/-- A positive Laplace integral converges at the left endpoint of a real interval
if its transform admits holomorphic continuation on a convex open neighborhood of
the interval, agreeing with the integral near its right endpoint. -/
theorem integrable_exp_neg_of_laplace_continuation_on_segment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → ℝ) (hT : Measurable T) (hT₀ : ∀ a, 0 ≤ T a)
    {a b c₀ : ℝ} (hab : a < b) (hc₀ : c₀ < b)
    (hM : Integrable (fun y ↦ Real.exp (-c₀ * T y)) μ)
    {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hSeg : ∀ y ∈ Icc a b, (y : ℂ) ∈ U)
    {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G U)
    (heq : G =ᶠ[𝓝 (b : ℂ)] fun z ↦ ∫ y, Complex.exp (-z * (T y : ℂ)) ∂μ) :
    Integrable (fun y ↦ Real.exp (-a * T y)) μ := by
  let D (u : ℝ) := Integrable (fun y ↦ Real.exp (-u * T y)) μ
  have hmono : Monotone D := by
    intro u v huv hu
    refine hu.mono' (hT.const_mul (-v)).exp.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right (neg_le_neg huv) (hT₀ y)
  let S := {u : ℝ | a ≤ u ∧ D u}
  have hS : S.Nonempty := ⟨b, hab.le, hmono hc₀.le hM⟩
  have hSb : BddBelow S := ⟨a, fun _ hu ↦ hu.1⟩
  let σ := sInf S
  have haσ : a ≤ σ := le_csInf hS (fun _ hu ↦ hu.1)
  have hσb : σ < b := (csInf_le hSb (show max a c₀ ∈ S from
    ⟨le_max_left _ _, hmono (le_max_right _ _) hM⟩)).trans_lt (max_lt hab hc₀)
  have hD (u : ℝ) (hu : σ < u) : D u := by
    obtain ⟨v, hv, hvu⟩ := exists_lt_of_csInf_lt hS hu
    exact hmono hvu.le hv.2
  let H := {z : ℂ | σ < z.re}
  let L (z : ℂ) := ∫ y, Complex.exp (-z * (T y : ℂ)) ∂μ
  have hL : AnalyticOnNhd ℂ L H := analyticOnNhd_laplaceIntegral μ T hT σ hD
  let V := U ∩ H
  have hV : IsOpen V := hU.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hbV : (b : ℂ) ∈ V := ⟨hSeg b ⟨hab.le, le_rfl⟩, by simpa [H] using hσb⟩
  have hEq : EqOn G L V :=
    (hG.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq (hL.mono inter_subset_right)
      (hUc.inter (convex_halfSpace_re_gt σ)).isPreconnected hbV heq
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hSeg σ ⟨haσ, hσb.le⟩))
  let c := σ + r / 8
  have hdist : dist (c : ℂ) (σ : ℂ) = r / 8 := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show c - σ = r / 8 by dsimp [c]; ring, abs_of_pos (by positivity)]
  have hσc : σ < c := by dsimp [c]; linarith
  have hcV : (c : ℂ) ∈ V :=
    ⟨hball (Metric.mem_ball.mpr (by rw [hdist]; linarith)), by simpa [H] using hσc⟩
  have hcball : Metric.ball (c : ℂ) (r / 2) ⊆ U := by
    intro z hz
    apply hball (Metric.mem_ball.mpr ?_)
    linarith [dist_triangle z (c : ℂ) (σ : ℂ), Metric.mem_ball.mp hz]
  let x := max a (σ - r / 4)
  have hx : x ≤ σ := max_le haσ (sub_le_self _ (by positivity))
  have hNear : G =ᶠ[𝓝 (c : ℂ)] L := by
    filter_upwards [hV.eventually_mem hcV] with z hz
    exact hEq hz
  have hxD : D x := integrable_exp_neg_of_laplace_continuation μ T hT hT₀
    (c₀ := (σ + c) / 2) (by linarith) (hD _ (by linarith))
    (hG.differentiableOn.mono hcball) hNear
    (hx.trans hσc.le) (by dsimp [c]; linarith [le_max_right a (σ - r / 4)])
  have hσx : σ ≤ x := csInf_le hSb ⟨le_max_left _ _, hxD⟩
  have hσa : σ = a := le_antisymm (by
    by_contra! h
    exact (not_lt_of_ge hσx) (max_lt h (sub_lt_self _ (by positivity)))) haσ
  have hxa : x = a := by dsimp [x]; rw [hσa, max_eq_left (sub_le_self _ (by positivity))]
  exact hxa ▸ hxD

/-- A meromorphic continuation of a positive Laplace integral to a right half-plane
has no poles there if it is holomorphic along the real part of that half-plane. -/
theorem meromorphicOrderAt_nonneg_of_positive_laplace_continuation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T : α → ℝ) (hT : Measurable T) (hT₀ : ∀ a, 0 ≤ T a)
    {a b : ℝ} (hab : a < b) (hM : Integrable (fun y ↦ Real.exp (-b * T y)) μ)
    {G : ℂ → ℂ} (hG : MeromorphicOn G {z | a < z.re})
    (hReal : ∀ x : ℝ, a < x → AnalyticAt ℂ G (x : ℂ))
    (heq : EqOn G (fun z ↦ ∫ y, Complex.exp (-z * (T y : ℂ)) ∂μ) {z | b < z.re})
    {z : ℂ} (hz : a < z.re) : 0 ≤ meromorphicOrderAt G z := by
  let L (z : ℂ) := ∫ y, Complex.exp (-z * (T y : ℂ)) ∂μ
  have hGerm (x : ℝ) (hx : b < x) : G =ᶠ[𝓝 (x : ℂ)] L := by
    have hOpen : IsOpen {z : ℂ | b < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hOpen.eventually_mem (show (x : ℂ) ∈ {z : ℂ | b < z.re} by simpa)] with w hw
    exact heq hw
  have hD (x : ℝ) (hx : a < x) : Integrable (fun y ↦ Real.exp (-x * T y)) μ := by
    let y := max x b + 1
    have hyx : x < y := (le_max_left _ _).trans_lt (lt_add_one _)
    have hyb : b < y := (le_max_right _ _).trans_lt (lt_add_one _)
    let K := Complex.ofReal '' Icc x y
    have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
    have hKc : Convex ℝ K := (convex_Icc x y).linear_image Complex.ofRealLI.toLinearMap
    have hKU : K ⊆ {w : ℂ | AnalyticAt ℂ G w} := by
      rintro _ ⟨t, ht, rfl⟩
      exact hReal t (hx.trans_le ht.1)
    obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ G) hKU
    have hU : Set.MapsTo Complex.ofReal (Icc x y) (Metric.thickening r K) :=
      fun t ht ↦ Metric.self_subset_thickening hr _ ⟨t, ht, rfl⟩
    exact integrable_exp_neg_of_laplace_continuation_on_segment μ T hT hT₀ hyx hyb hM
      Metric.isOpen_thickening (hKc.thickening r) (fun t ht ↦ hU ht)
      (fun w hw ↦ hrU (Metric.thickening_subset_cthickening r K hw)) (hGerm y hyb)
  have hL : AnalyticOnNhd ℂ L {z | a < z.re} := analyticOnNhd_laplaceIntegral μ T hT a hD
  have hdiff := hG.sub hL.meromorphicOn
  let x := b + 1
  have hx : b < x := lt_add_one _
  have hx' : (x : ℂ) ∈ {w : ℂ | a < w.re} := by simpa using hab.trans hx
  have h₁ : meromorphicOrderAt (G - L) (x : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    exact ((hGerm x hx).filter_mono nhdsWithin_le_nhds).mono fun w hw ↦ sub_eq_zero.mpr hw
  have h₂ := hdiff.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt a).isPreconnected hx' hz h₁
  have h₃ : G =ᶠ[𝓝[≠] z] L := (meromorphicOrderAt_eq_top_iff.mp h₂).mono
    fun w hw ↦ sub_eq_zero.mp hw
  exact (meromorphicOrderAt_congr h₃).symm ▸ (hL z hz).meromorphicOrderAt_nonneg

end RiemannMasullo
