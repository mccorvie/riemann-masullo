module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWPolarThreshold
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Density of Schwartz functions in the weighted real band, and the closure of the core

Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30).

For `0 ≤ α < 1 / 2` the band vectors given by even Schwartz functions with Fourier transform
supported in `[-Y, Y]` are dense in the weighted even band (`dense_realPWBand_schwartz`). With
`Sec4_RealPWPolarThreshold` this gives the closure of the polar-free core exactly. It is the
kernel of the evaluation at the origin (`closure_realPWBandPolarFreeCore_eq`).

The approximant of a band vector `f` is `x ↦ f (a x) m (x)`. The dilation by `a < 1` moves the
Fourier transform of `f` into `[-a Y, a Y]`. The factor `m` is the inverse Fourier transform of
a normalized bump supported in `(-ε, ε)`, so the Fourier transform of the product is the
convolution of the two, which is smooth and supported in `[-(a Y + ε), a Y + ε]`
(`exists_schwartz_eq_mul_dilate_realPWBand`). As `a → 1` and `ε → 0` the product tends to `f`
in the weighted norm. On a bounded interval this is dominated convergence, since the weight is
integrable there for `α < 1 / 2`. Outside it the contractions by a factor in `[1 / 2, 1]` are
bounded on the weighted space by one constant, so the tails are uniformly small.

Reconstruction: The paper does not state this. The core is that of the order-zero model of the
rational real place.

Not treated here: the width one half, where the weight is no longer integrable at the
origin. -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace Pointwise

namespace RiemannMasullo.Isolated

/-- The pointwise values of a band vector are the inverse Fourier transform of an integrable
function that vanishes outside the open band. This is the Paley–Wiener theorem applied to the
entire extension of the band vector. -/
theorem exists_integrable_spectrum_realPWBand {Y : ℝ} (hY : 0 < Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (hμac : μ ≪ volume) (f : RealPWBand.space Y hμ) :
    ∃ F : ℝ → ℂ, Integrable F ∧ (∀ ξ ∉ Ioo (-Y) Y, F ξ = 0) ∧
      ∀ x : ℝ, RealPWBand.evaluation Y hμ x f = 𝓕⁻ F x := by
  obtain ⟨g, hg, htr, C, hC, hb⟩ := RealPWBand.exists_entire_evaluation Y hY.le hμ f
  have hae := RealPWBand.evaluation_ae Y hμ hμac f
  have hmem : MemLp (fun x : ℝ ↦ g x) 2 volume := by
    have h1 : MemLp (fun x ↦ RealPWBand.evaluation Y hμ x f) 2 μ :=
      (Lp.memLp (f.val : Lp ℂ 2 μ)).ae_eq hae.symm
    have h2 : (fun x : ℝ ↦ g x) = fun x ↦ RealPWBand.evaluation Y hμ x f := funext htr
    rw [h2]
    exact h1.mono_measure hμ
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  let A := 2 * Real.pi * Y
  have hA : 0 < A := mul_pos hπ hY
  obtain ⟨F₀, hF₀, hrep⟩ := (paleyWiener_interval A hA g hg).mpr
    ⟨⟨C + 1, by linarith, fun z ↦ (hb z).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)⟩, hmem⟩
  have hfin : IsFiniteMeasure (volume.restrict (Ioo (-A) A)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hF₁ : IntegrableOn F₀ (Ioo (-A) A) := hF₀.integrable one_le_two
  let h : ℝ → ℂ := (Ioo (-A) A).indicator F₀
  have hh : Integrable h := (integrable_indicator_iff measurableSet_Ioo).mpr hF₁
  let F : ℝ → ℂ := fun ξ ↦ ((2 * Real.pi : ℝ) : ℂ) * h (2 * Real.pi * ξ)
  refine ⟨F, (hh.comp_mul_left' hπ.ne').const_mul _, fun ξ hξ ↦ ?_, fun x ↦ ?_⟩
  · have hout : 2 * Real.pi * ξ ∉ Ioo (-A) A := by
      intro hin
      apply hξ
      constructor
      · have := hin.1
        change -(2 * Real.pi * Y) < 2 * Real.pi * ξ at this
        nlinarith
      · have := hin.2
        change 2 * Real.pi * ξ < 2 * Real.pi * Y at this
        nlinarith
    change ((2 * Real.pi : ℝ) : ℂ) * (Ioo (-A) A).indicator F₀ (2 * Real.pi * ξ) = 0
    rw [indicator_of_notMem hout, mul_zero]
  · rw [← htr x, hrep x, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq]
    let G : ℝ → ℂ := fun t ↦ Complex.exp (Complex.I * t * x) * h t
    have h1 : (fun v : ℝ ↦ 𝐞 (-(v * -x)) • F v) =
        fun v ↦ ((2 * Real.pi : ℝ) : ℂ) * G (2 * Real.pi * v) := by
      funext v
      change 𝐞 (-(v * -x)) • (((2 * Real.pi : ℝ) : ℂ) * h (2 * Real.pi * v)) =
        ((2 * Real.pi : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((2 * Real.pi * v : ℝ) : ℂ) * x) * h (2 * Real.pi * v))
      rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
      have he : Complex.exp (((2 * Real.pi * -(v * -x) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (Complex.I * ((2 * Real.pi * v : ℝ) : ℂ) * x) := by
        congr 1
        push_cast
        ring
      rw [he]
      ring
    rw [h1, integral_const_mul, Measure.integral_comp_mul_left G (2 * Real.pi),
      abs_of_pos (inv_pos.mpr hπ), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hπ.ne', Complex.ofReal_one, one_mul]
    have h2 : G = (Ioo (-A) A).indicator fun t ↦ F₀ t * Complex.exp (Complex.I * t * x) := by
      funext t
      by_cases ht : t ∈ Ioo (-A) A
      · change Complex.exp (Complex.I * t * x) * (Ioo (-A) A).indicator F₀ t = _
        rw [indicator_of_mem ht, indicator_of_mem ht, mul_comm]
      · change Complex.exp (Complex.I * t * x) * (Ioo (-A) A).indicator F₀ t = _
        rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
    rw [h2, integral_indicator measurableSet_Ioo]

open scoped Convolution in
/-- A band vector, dilated by `a < 1` and multiplied by the inverse Fourier transform `m` of a
normalized bump of width `ε`, is a Schwartz function with Fourier transform in the band, as soon
as `a Y + ε ≤ Y`. The multiplier `m` is even, bounded by one, and within `2 π ε |x|` of one. -/
theorem exists_schwartz_eq_mul_dilate_realPWBand {Y : ℝ} (hY : 0 < Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (hμac : μ ≪ volume) (f : RealPWBand.space Y hμ) {a ε : ℝ}
    (ha0 : 0 < a) (hε : 0 < ε) (hεa : a * Y + ε ≤ Y) :
    ∃ (g : 𝓢(ℝ, ℂ)) (m : ℝ → ℂ), (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧
      (∀ x, g x = RealPWBand.evaluation Y hμ (a * x) f * m x) ∧ (∀ x, ‖m x‖ ≤ 1) ∧
      (∀ x, m (-x) = m x) ∧ ∀ x, ‖m x - 1‖ ≤ 2 * Real.pi * ε * |x| := by
  obtain ⟨F, hF, hF0, hFu⟩ := exists_integrable_spectrum_realPWBand hY hμ hμac f
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the dilated spectrum
  let Fa : ℝ → ℂ := fun ξ ↦ ((a⁻¹ : ℝ) : ℂ) * F (a⁻¹ * ξ)
  have hFa : Integrable Fa := (hF.comp_mul_left' (inv_ne_zero ha0.ne')).const_mul _
  have hFa0 : ∀ ξ ∉ Icc (-(a * Y)) (a * Y), Fa ξ = 0 := by
    intro ξ hξ
    have hout : a⁻¹ * ξ ∉ Ioo (-Y) Y := by
      intro hin
      apply hξ
      have h1 := mul_lt_mul_of_pos_left hin.1 ha0
      have h2 := mul_lt_mul_of_pos_left hin.2 ha0
      rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at h1 h2
      exact ⟨by linarith, h2.le⟩
    change ((a⁻¹ : ℝ) : ℂ) * F (a⁻¹ * ξ) = 0
    rw [hF0 _ hout, mul_zero]
  have hFaF (x : ℝ) : 𝓕 Fa (-x) = RealPWBand.evaluation Y hμ (a * x) f := by
    rw [hFu (a * x), Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq, Real.fourier_real_eq]
    let G : ℝ → ℂ := fun w ↦ 𝐞 (-(w * -(a * x))) • F w
    have h1 : (fun v : ℝ ↦ 𝐞 (-(v * -x)) • Fa v) =
        fun v ↦ ((a⁻¹ : ℝ) : ℂ) * G (a⁻¹ * v) := by
      funext v
      change 𝐞 (-(v * -x)) • (((a⁻¹ : ℝ) : ℂ) * F (a⁻¹ * v)) =
        ((a⁻¹ : ℝ) : ℂ) * (𝐞 (-(a⁻¹ * v * -(a * x))) • F (a⁻¹ * v))
      have he : -(a⁻¹ * v * -(a * x)) = -(v * -x) := by
        field_simp
      rw [he, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul]
      ring
    rw [h1, integral_const_mul, Measure.integral_comp_mul_left G a⁻¹, inv_inv, abs_of_pos ha0,
      Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha0.ne',
      Complex.ofReal_one, one_mul]
  -- the bump
  let Bε : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  let ρ : ℝ → ℂ := fun t ↦ ((Bε.normed volume t : ℝ) : ℂ)
  have hρi : Integrable ρ := Bε.integrable_normed.ofReal
  have hρ1 : ∫ t, ρ t = 1 := by
    change ∫ t, ((Bε.normed volume t : ℝ) : ℂ) = 1
    rw [integral_complex_ofReal, Bε.integral_normed, Complex.ofReal_one]
  have hρc : HasCompactSupport ρ := Bε.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ :=
    Complex.ofRealCLM.contDiff.comp Bε.contDiff_normed
  have hρ0 : ∀ t : ℝ, ε ≤ |t| → ρ t = 0 := by
    intro t ht
    have hns : t ∉ Function.support (Bε.normed volume) := by
      rw [Bε.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
      exact not_lt.mpr ht
    have hz : Bε.normed volume t = 0 := Function.notMem_support.mp hns
    change ((Bε.normed volume t : ℝ) : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  have hρn (t : ℝ) : ‖ρ t‖ = Bε.normed volume t := by
    change ‖((Bε.normed volume t : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (Bε.nonneg_normed t)]
  have hρe (t : ℝ) : ρ (-t) = ρ t := by
    change ((Bε.normed volume (-t) : ℝ) : ℂ) = ((Bε.normed volume t : ℝ) : ℂ)
    rw [Bε.normed_neg]
  -- the convolution
  let b : ℝ → ℂ := Fa ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ρ
  have hbs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
    hρc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hFa.locallyIntegrable hρs
  have hFac : HasCompactSupport Fa :=
    HasCompactSupport.intro isCompact_Icc fun ξ hξ ↦ hFa0 ξ hξ
  have hbc : HasCompactSupport b := hFac.convolution (ContinuousLinearMap.mul ℝ ℂ) hρc
  have hb0 : ∀ ξ ∉ Icc (-Y) Y, b ξ = 0 := by
    intro ξ hξ
    by_contra hne
    have hmem : ξ ∈ Function.support Fa + Function.support ρ :=
      support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ) (Function.mem_support.mpr hne)
    obtain ⟨r, hr, t, ht, rfl⟩ := Set.mem_add.mp hmem
    have hr' : r ∈ Icc (-(a * Y)) (a * Y) := by
      by_contra h
      exact hr (hFa0 r h)
    have ht' : |t| < ε := by
      by_contra h
      exact ht (hρ0 t (not_lt.mp h))
    have ht'' := abs_lt.mp ht'
    exact hξ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  let bS : 𝓢(ℝ, ℂ) := hbc.toSchwartzMap hbs
  have hbS : (bS : ℝ → ℂ) = b := rfl
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ bS
  have hFg : 𝓕 g = bS := FourierTransform.fourier_fourierInv_eq _
  let m : ℝ → ℂ := fun x ↦ 𝓕 ρ (-x)
  have hmx (x : ℝ) : m x = ∫ v, 𝐞 (v * x) • ρ v := by
    change 𝓕 ρ (-x) = _
    rw [Real.fourier_real_eq]
    refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    change 𝐞 (-(v * -x)) • ρ v = 𝐞 (v * x) • ρ v
    rw [mul_neg, neg_neg]
  have hconv : b = Fa ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ρ := rfl
  refine ⟨g, m, fun ξ hξ ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [hFg]
    exact hb0 ξ hξ
  · change (𝓕⁻ bS : 𝓢(ℝ, ℂ)) x = _
    rw [SchwartzMap.fourierInv_coe, hbS, Real.fourierInv_eq_fourier_neg, hconv,
      Real.fourier_mul_convolution_eq hFa hρi, hFaF]
  · rw [hmx]
    calc ‖∫ v, 𝐞 (v * x) • ρ v‖ ≤ ∫ v, ‖𝐞 (v * x) • ρ v‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ v, Bε.normed volume v := by
          refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
          change ‖𝐞 (v * x) • ρ v‖ = _
          rw [Circle.norm_smul, hρn]
      _ = 1 := Bε.integral_normed
  · rw [hmx, hmx, ← integral_neg_eq_self]
    refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    change 𝐞 (-v * -x) • ρ (-v) = 𝐞 (v * x) • ρ v
    rw [neg_mul_neg, hρe]
  · have hsub : m x - 1 = ∫ v, (𝐞 (v * x) • ρ v - ρ v) := by
      have hint : Integrable fun v : ℝ ↦ 𝐞 (v * x) • ρ v := by
        refine hρi.norm.mono' ?_ (ae_of_all _ fun v ↦ ?_)
        · exact ((Real.continuous_fourierChar.comp
            (continuous_id.mul continuous_const)).aestronglyMeasurable).smul
            hρi.aestronglyMeasurable
        · change ‖𝐞 (v * x) • ρ v‖ ≤ ‖ρ v‖
          rw [Circle.norm_smul]
      rw [integral_sub hint hρi, hρ1, hmx]
    rw [hsub]
    calc ‖∫ v, (𝐞 (v * x) • ρ v - ρ v)‖ ≤ ∫ v, ‖𝐞 (v * x) • ρ v - ρ v‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v, (2 * Real.pi * ε * |x|) * Bε.normed volume v := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
            (Bε.integrable_normed.const_mul _) (ae_of_all _ fun v ↦ ?_)
          change ‖𝐞 (v * x) • ρ v - ρ v‖ ≤ 2 * Real.pi * ε * |x| * Bε.normed volume v
          by_cases hv : ε ≤ |v|
          · rw [hρ0 v hv, smul_zero, sub_zero, norm_zero]
            exact mul_nonneg (by positivity) (Bε.nonneg_normed v)
          · have hv' : |v| ≤ ε := (not_le.mp hv).le
            have h1 : 𝐞 (v * x) • ρ v - ρ v =
                (Complex.exp (Complex.I * ((2 * Real.pi * (v * x) : ℝ) : ℂ)) - 1) * ρ v := by
              rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm Complex.I]
              ring
            rw [h1, norm_mul, hρn]
            refine mul_le_mul_of_nonneg_right ?_ (Bε.nonneg_normed v)
            refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (v * x))).trans ?_
            rw [Real.norm_eq_abs, abs_mul (2 * Real.pi), abs_mul v, abs_of_pos hπ]
            calc 2 * Real.pi * (|v| * |x|) ≤ 2 * Real.pi * (ε * |x|) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv' (abs_nonneg x)) hπ.le
              _ = 2 * Real.pi * ε * |x| := by ring
      _ = 2 * Real.pi * ε * |x| := by
          rw [integral_const_mul, Bε.integral_normed, mul_one]

variable {Y α s : ℝ}

/-- One constant bounds the weighted integral of every contraction by a factor in `[1/2, 1]` of
a nonnegative measurable integrable function. -/
private theorem exists_integral_contraction_le (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 → ∀ Φ : ℝ → ℝ, Measurable Φ →
      (∀ x, 0 ≤ Φ x) → Integrable Φ (realPWIntervalMeasure α s) →
        Integrable (fun x ↦ Φ (a * x)) (realPWIntervalMeasure α s) ∧
          ∫ x, Φ (a * x) ∂realPWIntervalMeasure α s ≤
            E * ∫ x, Φ x ∂realPWIntervalMeasure α s := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hb2 : 0 ≤ 1 + Real.log 2 + Real.log 2 ^ 2 := by positivity
  refine ⟨Real.exp (2 * α * Real.log 2) * (1 + Real.log 2 + Real.log 2 ^ 2) ^ (s / 2) * 2,
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hb2 _)) zero_le_two,
    fun a ha ha1 Φ hΦm hΦ0 hΦ ↦ ?_⟩
  have ha0 : 0 < a := by linarith
  let t := a⁻¹
  have ht : 1 ≤ t := (one_le_inv₀ ha0).mpr ha1
  have ht2 : t ≤ 2 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) ha
    rwa [one_div, inv_inv] at h
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog2 : Real.log t ≤ Real.log 2 := Real.log_le_log ht0 ht2
  have hb1 : 0 ≤ 1 + Real.log t + Real.log t ^ 2 := by positivity
  let C := Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hb1 _)
  have hCE : C * t ≤ Real.exp (2 * α * Real.log 2) *
      (1 + Real.log 2 + Real.log 2 ^ 2) ^ (s / 2) * 2 := by
    have h1 : Real.exp (2 * α * Real.log t) ≤ Real.exp (2 * α * Real.log 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog2 (by positivity))
    have h2 : (1 + Real.log t + Real.log t ^ 2) ^ (s / 2) ≤
        (1 + Real.log 2 + Real.log 2 ^ 2) ^ (s / 2) :=
      Real.rpow_le_rpow hb1 (by nlinarith) (by positivity)
    exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hb1 _) (Real.exp_nonneg _)) ht2 ht0.le
      (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hb2 _))
  let k := ENNReal.ofReal C * ENNReal.ofReal t
  have hmap : Measure.map (a * ·) (realPWIntervalMeasure α s) ≤
      k • realPWIntervalMeasure α s := by
    have h := map_mul_realPWIntervalMeasure_le (α := α) (s := s) hα hs ht
    rwa [show t⁻¹ = a from inv_inv a] at h
  have hk : k ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hkr : k.toReal = C * t := by
    dsimp [k]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal ht0.le]
  have hmul : Measurable (a * ·) := measurable_const_mul _
  have hImap : Integrable Φ (Measure.map (a * ·) (realPWIntervalMeasure α s)) :=
    (hΦ.smul_measure hk).mono_measure hmap
  have hcomp : Integrable (Φ ∘ (a * ·)) (realPWIntervalMeasure α s) :=
    (integrable_map_measure hΦm.aestronglyMeasurable hmul.aemeasurable).mp hImap
  refine ⟨hcomp, ?_⟩
  have hI0 : 0 ≤ ∫ x, Φ x ∂realPWIntervalMeasure α s := integral_nonneg hΦ0
  calc ∫ x, Φ (a * x) ∂realPWIntervalMeasure α s
      = ∫ y, Φ y ∂Measure.map (a * ·) (realPWIntervalMeasure α s) :=
        (integral_map hmul.aemeasurable hΦm.aestronglyMeasurable).symm
    _ ≤ ∫ y, Φ y ∂(k • realPWIntervalMeasure α s) :=
        integral_mono_measure hmap (ae_of_all _ hΦ0) (hΦ.smul_measure hk)
    _ = C * t * ∫ y, Φ y ∂realPWIntervalMeasure α s := by
        rw [integral_smul_measure, hkr, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hCE hI0

/-- The integral of an integrable function over the complement of a large interval is small. -/
private theorem exists_tail_integral_lt {μ : Measure ℝ} (U : ℝ → ℝ) (hU : Integrable U μ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∫ x, ({y : ℝ | (k : ℝ) < |y|}.indicator U) x ∂μ < δ := by
  have hlim : Tendsto (fun k : ℕ ↦ ∫ x, ({y : ℝ | (k : ℝ) < |y|}.indicator U) x ∂μ)
      atTop (𝓝 (∫ _, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖U x‖) (fun k ↦ ?_) hU.norm
      (fun k ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · exact hU.aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const continuous_abs.measurable)
    · exact norm_indicator_le_norm_self _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with k hk
      refine (indicator_of_notMem ?_ _).symm
      change ¬ ((k : ℝ) < |x|)
      exact not_lt.mpr ((Nat.le_ceil _).trans (Nat.cast_le.mpr hk))
  rw [integral_zero] at hlim
  exact ((tendsto_order.1 hlim).2 δ hδ).exists

/-- Reconstruction: for `0 ≤ α < 1/2` the band vectors whose pointwise representative is an even
Schwartz function with Fourier transform zero outside `[-Y, Y]` are dense in the weighted even
band. The approximant of `f` is `x ↦ f (a x) m(x)` with `a < 1` close to one and `m` the inverse
Fourier transform of a narrow normalized bump. -/
theorem exists_schwartz_realPWBand_norm_sub_lt (hα : 0 ≤ α) (hα' : α < 1 / 2) (hs : 0 ≤ s)
    (hY : 0 < Y) (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) {η : ℝ}
    (hη : 0 < η) :
    ∃ (g : 𝓢(ℝ, ℂ)) (f' : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)),
      Function.Even (g : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧
      (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f') = g ∧
      ‖f - f'‖ < η := by
  have hμ := volume_le_realPWIntervalMeasure α s hs
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  let u : ℝ → ℂ := fun x ↦ RealPWBand.evaluation Y hμ x f
  have huc : Continuous u := (RealPWBand.contDiff_evaluation Y hμ f 0).continuous
  have hue : ∀ x, u (-x) = u x := RealPWBand.evaluation_even Y hμ f
  have hum : MemLp u 2 (realPWIntervalMeasure α s) :=
    (Lp.memLp (f.val : Lp ℂ 2 (realPWIntervalMeasure α s))).ae_eq
      (RealPWBand.evaluation_ae Y hμ hμac f).symm
  let U : ℝ → ℝ := fun x ↦ ‖u x‖ ^ 2
  have hUi : Integrable U (realPWIntervalMeasure α s) :=
    (memLp_two_iff_integrable_sq_norm huc.aestronglyMeasurable).mp hum
  have hUc : Continuous U := (continuous_norm.comp huc).pow 2
  obtain ⟨E, hE0, hE⟩ := exists_integral_contraction_le (α := α) (s := s) hα hs
  -- the tail
  have hE2 : 0 < 2 + 2 * E := by positivity
  obtain ⟨k, hk⟩ := exists_tail_integral_lt U hUi (div_pos (half_pos (pow_pos hη 2)) hE2)
  let S : Set ℝ := {y | (k : ℝ) < |y|}
  have hSm : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  let Φ : ℝ → ℝ := S.indicator U
  have hΦm : Measurable Φ := hUc.measurable.indicator hSm
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x ↦ indicator_nonneg (fun y _ ↦ sq_nonneg _) x
  have hΦi : Integrable Φ (realPWIntervalMeasure α s) := hUi.indicator hSm
  have htail : (2 + 2 * E) * ∫ x, Φ x ∂realPWIntervalMeasure α s < η ^ 2 / 2 := by
    have h := (lt_div_iff₀ hE2).mp hk
    rwa [mul_comm] at h
  -- the bounded part
  let R : ℝ := 2 * k
  let I : Set ℝ := Icc (-R) R
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (huc.continuousOn (s := I))
  have hμI : realPWIntervalMeasure α s I < ⊤ := by
    have hint : IntegrableOn (fun x ↦ |x| ^ (0 : ℝ) * realPWIntervalWeight α s x) I :=
      integrableOn_abs_rpow_mul_realPWIntervalWeight hα hs (by linarith)
    have h := hint.lintegral_lt_top
    change (volume.withDensity fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x)) I < ⊤
    rw [withDensity_apply _ measurableSet_Icc]
    simpa only [Real.rpow_zero, one_mul] using h
  -- the sequence of dilations and bump widths
  let r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hr0 : ∀ n, 0 < r n := fun n ↦ by positivity
  have hr1 : ∀ n, r n ≤ 1 := fun n ↦ by
    change 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ℕ → ℝ := fun n ↦ 1 - r n / 2
  let ε : ℕ → ℝ := fun n ↦ Y * r n / 2
  have ha0 : ∀ n, 1 / 2 ≤ a n := fun n ↦ by
    change 1 / 2 ≤ 1 - r n / 2
    linarith [hr1 n]
  have ha1 : ∀ n, a n < 1 := fun n ↦ by
    change 1 - r n / 2 < 1
    linarith [hr0 n]
  have hap : ∀ n, 0 < a n := fun n ↦ lt_of_lt_of_le (by norm_num) (ha0 n)
  have hε : ∀ n, 0 < ε n := fun n ↦ by
    change 0 < Y * r n / 2
    have := hr0 n
    positivity
  have hεa : ∀ n, a n * Y + ε n ≤ Y := fun n ↦ by
    change (1 - r n / 2) * Y + Y * r n / 2 ≤ Y
    exact le_of_eq (by ring)
  choose g m hgb hgm hm1 hme hmc using fun n ↦
    exists_schwartz_eq_mul_dilate_realPWBand hY hμ hμac f (hap n) (hε n) (hεa n)
  have hgle : ∀ n x, ‖g n x‖ ≤ ‖u (a n * x)‖ := fun n x ↦ by
    rw [hgm, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hm1 n x)
  -- pointwise convergence
  have hpt : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (u x)) := by
    intro x
    have h1 : Tendsto (fun n ↦ u (a n * x)) atTop (𝓝 (u x)) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hrt.div_const 2)).mul_const x
      rw [show (1 - (0 : ℝ) / 2) * x = x by ring] at h
      exact (huc.tendsto x).comp h
    have h2 : Tendsto (fun n ↦ m n x) atTop (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ hmc n x) ?_
      have h := (((hrt.const_mul Y).div_const 2).const_mul (2 * Real.pi)).mul_const |x|
      rw [show 2 * Real.pi * (Y * 0 / 2) * |x| = 0 by ring] at h
      exact h
    have h := h1.mul h2
    rw [mul_one] at h
    exact h.congr fun n ↦ (hgm n x).symm
  have hB : Tendsto (fun n ↦ ∫ x in I, ‖u x - g n x‖ ^ 2 ∂realPWIntervalMeasure α s)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := (realPWIntervalMeasure α s).restrict I) (F := fun n x ↦ ‖u x - g n x‖ ^ 2)
      (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * M) ^ 2) (fun n ↦ ?_) ?_ (fun n ↦ ?_) ?_
    · rwa [integral_zero] at h
    · exact (((huc.sub (g n).continuous).norm).pow 2).aestronglyMeasurable
    · exact integrableOn_const hμI.ne
    · refine (ae_restrict_mem measurableSet_Icc).mono fun x hx ↦ ?_
      have hax : a n * x ∈ I := by
        have h1 : |a n * x| ≤ R := by
          rw [abs_mul, abs_of_pos (hap n)]
          calc a n * |x| ≤ 1 * |x| :=
                mul_le_mul_of_nonneg_right (ha1 n).le (abs_nonneg x)
            _ = |x| := one_mul _
            _ ≤ R := abs_le.mpr hx
        exact abs_le.mp h1
      have h1 : ‖u x - g n x‖ ≤ 2 * M := by
        calc ‖u x - g n x‖ ≤ ‖u x‖ + ‖g n x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hM x hx) ((hgle n x).trans (hM _ hax))
          _ = 2 * M := by ring
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · refine ae_of_all _ fun x ↦ ?_
      have h := (((hpt x).const_sub (u x)).norm).pow 2
      rwa [sub_self, norm_zero, zero_pow two_ne_zero] at h
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hB).2 (η ^ 2 / 2) (half_pos (pow_pos hη 2))).exists
  -- the approximant
  have hge : Function.Even (g n : ℝ → ℂ) := fun x ↦ by
    rw [hgm, hgm, mul_neg, hme]
    exact congrArg (· * m n x) (hue (a n * x))
  have hga : MemLp (fun x ↦ u (a n * x)) 2 (realPWIntervalMeasure α s) :=
    memLp_realPWIntervalMeasure_dilation hs (hap n) hum
  have hgL : MemLp (g n : ℝ → ℂ) 2 (realPWIntervalMeasure α s) :=
    hga.mono (g n).continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ hgle n x)
  obtain ⟨f', hf'⟩ :=
    RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y (g n) hge (hgb n) hμ hgL
  refine ⟨g n, f', hge, hgb n, hf', ?_⟩
  have hnorm : ‖f - f'‖ ^ 2 = ∫ x, ‖u x - g n x‖ ^ 2 ∂realPWIntervalMeasure α s :=
    norm_sq_realPWBand_of_evaluation_eq hs (f - f') (fun x ↦ u x - g n x) (by
      funext x
      rw [map_sub, congrFun hf' x])
  have hpw : ∀ x, ‖u x - g n x‖ ^ 2 ≤
      I.indicator (fun x ↦ ‖u x - g n x‖ ^ 2) x + (2 * Φ x + 2 * Φ (a n * x)) := by
    intro x
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx]
      linarith [hΦ0 x, hΦ0 (a n * x)]
    · rw [indicator_of_notMem hx, zero_add]
      have hxR : 2 * (k : ℝ) < |x| := by
        by_contra h
        exact hx (abs_le.mp (not_lt.mp h))
      have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
      have hxS : x ∈ S := by
        change (k : ℝ) < |x|
        linarith
      have haxS : a n * x ∈ S := by
        change (k : ℝ) < |a n * x|
        rw [abs_mul, abs_of_pos (hap n)]
        have := mul_le_mul_of_nonneg_right (ha0 n) (abs_nonneg x)
        linarith
      have hΦx : Φ x = ‖u x‖ ^ 2 := indicator_of_mem hxS U
      have hΦax : Φ (a n * x) = ‖u (a n * x)‖ ^ 2 := indicator_of_mem haxS U
      rw [hΦx, hΦax]
      have h1 : ‖u x - g n x‖ ≤ ‖u x‖ + ‖u (a n * x)‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (hgle n x))
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖u x‖ - ‖u (a n * x)‖)]
  have hIint : IntegrableOn (fun x ↦ ‖u x - g n x‖ ^ 2) I (realPWIntervalMeasure α s) := by
    have h : MemLp (fun x ↦ u x - g n x) 2 (realPWIntervalMeasure α s) := hum.sub hgL
    exact ((memLp_two_iff_integrable_sq_norm
      (huc.sub (g n).continuous).aestronglyMeasurable).mp h).integrableOn
  have hΦa := hE (a n) (ha0 n) (ha1 n).le Φ hΦm hΦ0 hΦi
  have hi1 : Integrable (fun x ↦ I.indicator (fun x ↦ ‖u x - g n x‖ ^ 2) x)
      (realPWIntervalMeasure α s) := hIint.integrable_indicator measurableSet_Icc
  have hi2 : Integrable (fun x ↦ 2 * Φ x) (realPWIntervalMeasure α s) := hΦi.const_mul 2
  have hi3 : Integrable (fun x ↦ 2 * Φ (a n * x)) (realPWIntervalMeasure α s) :=
    hΦa.1.const_mul 2
  have hi23 : Integrable (fun x ↦ 2 * Φ x + 2 * Φ (a n * x)) (realPWIntervalMeasure α s) :=
    hi2.add hi3
  have hmain : ∫ x, ‖u x - g n x‖ ^ 2 ∂realPWIntervalMeasure α s ≤
      ∫ x in I, ‖u x - g n x‖ ^ 2 ∂realPWIntervalMeasure α s +
        (2 + 2 * E) * ∫ x, Φ x ∂realPWIntervalMeasure α s := by
    calc ∫ x, ‖u x - g n x‖ ^ 2 ∂realPWIntervalMeasure α s
        ≤ ∫ x, (I.indicator (fun x ↦ ‖u x - g n x‖ ^ 2) x + (2 * Φ x + 2 * Φ (a n * x)))
            ∂realPWIntervalMeasure α s :=
          integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _) (hi1.add hi23)
            (ae_of_all _ hpw)
      _ = ∫ x in I, ‖u x - g n x‖ ^ 2 ∂realPWIntervalMeasure α s +
            (2 * ∫ x, Φ x ∂realPWIntervalMeasure α s +
              2 * ∫ x, Φ (a n * x) ∂realPWIntervalMeasure α s) := by
          rw [integral_add hi1 hi23, integral_indicator measurableSet_Icc,
            integral_add hi2 hi3, integral_const_mul, integral_const_mul]
      _ ≤ _ := by linarith [hΦa.2]
  have hlt : ‖f - f'‖ ^ 2 < η ^ 2 := by
    rw [hnorm]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hη.le hlt

/-- Reconstruction: for `0 ≤ α < 1/2` the band vectors given by even Schwartz functions with
Fourier transform zero outside `[-Y, Y]` are dense in the weighted even band. -/
theorem dense_realPWBand_schwartz (hα : 0 ≤ α) (hα' : α < 1 / 2) (hs : 0 ≤ s) (hY : 0 < Y) :
    Dense {f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) |
      ∃ g : 𝓢(ℝ, ℂ), Function.Even (g : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧
        (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) = g} := by
  intro f
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
    exists_schwartz_realPWBand_norm_sub_lt hα hα' hs hY f hη
  exact ⟨f', ⟨g, hge, hgb, hgf⟩, by rwa [dist_eq_norm]⟩

/-- Reconstruction: for `0 ≤ α < 1/2` the closure of the polar-free core of the weighted even
band is the kernel of the evaluation at the origin. The condition of integral zero is lost in
the closure and the condition of vanishing at the origin is all that remains. -/
theorem closure_realPWBandPolarFreeCore_eq (hα : 0 ≤ α) (hα' : α < 1 / 2) (hs : 0 ≤ s)
    (hY : 0 < Y) :
    closure (realPWBandPolarFreeCore Y α hs) =
      {f | RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0} := by
  apply Set.Subset.antisymm
  · refine closure_minimal (fun f hf ↦ ?_) (isClosed_eq
      (RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0).continuous
      continuous_const)
    obtain ⟨g, -, -, h0, -, hfg⟩ := hf
    change RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0
    rw [← h0]
    exact congrFun hfg 0
  · intro f hf
    change RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0 at hf
    rw [← closure_closure, Metric.mem_closure_iff]
    intro η hη
    by_cases hex : ∃ (g₀ : 𝓢(ℝ, ℂ))
        (e₀ : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)),
        Function.Even (g₀ : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g₀) ξ = 0) ∧
        (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x e₀) =
          g₀ ∧ g₀ 0 ≠ 0
    · obtain ⟨g₀, e₀, he₀, hb₀, hev₀, hne⟩ := hex
      let L := RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0
      let K : ℝ := 1 + ‖L‖ * (‖g₀ 0‖⁻¹ * ‖e₀‖)
      have hK : 0 < K := by positivity
      obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
        exists_schwartz_realPWBand_norm_sub_lt hα hα' hs hY f (div_pos hη hK)
      let c : ℂ := g 0 / g₀ 0
      let g₂ : 𝓢(ℝ, ℂ) := g - c • g₀
      let f₂ := f' - c • e₀
      have hg₂ (x : ℝ) : g₂ x = g x - c * g₀ x := rfl
      have hg₂e : Function.Even (g₂ : ℝ → ℂ) := fun x ↦ by
        rw [hg₂, hg₂, hge x, he₀ x]
      have hg₂b : ∀ ξ ∉ Icc (-Y) Y, (𝓕 g₂) ξ = 0 := fun ξ hξ ↦ by
        change (𝓕 (g - c • g₀)) ξ = 0
        rw [FourierTransform.fourier_sub, FourierTransform.fourier_smul, sub_apply, smul_apply,
          hgb ξ hξ, hb₀ ξ hξ, smul_zero, sub_zero]
      have hg₂0 : g₂ 0 = 0 := by
        rw [hg₂, div_mul_cancel₀ _ hne, sub_self]
      have hf₂ : (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x
          f₂) = g₂ := by
        funext x
        change RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x
          (f' - c • e₀) = g x - c * g₀ x
        rw [map_sub, map_smul, congrFun hgf x, congrFun hev₀ x, smul_eq_mul]
      refine ⟨f₂, mem_closure_realPWBandPolarFreeCore_of_schwartz hα hα' hs hY g₂ hg₂e hg₂b
        hg₂0 f₂ hf₂, ?_⟩
      have hg0 : ‖g 0‖ ≤ ‖L‖ * ‖f - f'‖ := by
        have h : g 0 = -L (f - f') := by
          change g 0 = -(RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0
            (f - f'))
          rw [map_sub, hf, zero_sub, neg_neg]
          exact (congrFun hgf 0).symm
        rw [h, norm_neg]
        exact L.le_opNorm _
      have hc : ‖c‖ ≤ ‖L‖ * ‖f - f'‖ * ‖g₀ 0‖⁻¹ := by
        change ‖g 0 / g₀ 0‖ ≤ _
        rw [norm_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hg0 (inv_nonneg.mpr (norm_nonneg _))
      rw [dist_eq_norm]
      calc ‖f - f₂‖ = ‖(f - f') + c • e₀‖ := by
            congr 1
            change f - (f' - c • e₀) = _
            abel
        _ ≤ ‖f - f'‖ + ‖c‖ * ‖e₀‖ := (norm_add_le _ _).trans (by rw [norm_smul])
        _ ≤ ‖f - f'‖ + (‖L‖ * ‖f - f'‖ * ‖g₀ 0‖⁻¹) * ‖e₀‖ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
        _ = K * ‖f - f'‖ := by
            change _ = (1 + ‖L‖ * (‖g₀ 0‖⁻¹ * ‖e₀‖)) * ‖f - f'‖
            ring
        _ < K * (η / K) := mul_lt_mul_of_pos_left hclose hK
        _ = η := mul_div_cancel₀ _ hK.ne'
    · push Not at hex
      obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
        exists_schwartz_realPWBand_norm_sub_lt hα hα' hs hY f hη
      have hg0 : g 0 = 0 := hex g f' hge hgb hgf
      exact ⟨f', mem_closure_realPWBandPolarFreeCore_of_schwartz hα hα' hs hY g hge hgb hg0
        f' hgf, by rwa [dist_eq_norm]⟩

end RiemannMasullo.Isolated
