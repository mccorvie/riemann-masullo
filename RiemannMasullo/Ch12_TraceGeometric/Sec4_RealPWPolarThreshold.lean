module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWJetTrials
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.PSeries
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Which polar condition survives completion in the weighted real band

Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30).

The polar-free core consists of the band vectors given by even Schwartz functions with Fourier
transform supported in `[-Y, Y]`, value zero at the origin and integral zero. The level is its
closure in the weighted band. This file determines what becomes of the condition on the
integral, in terms of the width `α` of the weight.

* Below width one half the condition is lost. The closure contains every band vector given by
  an even Schwartz function of the band that vanishes at the origin
  (`mem_closure_realPWBandPolarFreeCore_of_schwartz`), and some of these have nonzero integral
  (`exists_mem_closure_realPWBandPolarFreeCore_integral_ne_zero`). The reason is that the
  dilates `x ↦ h (x / t) / t` keep their integral while their weighted norm tends to zero.
* At width one half with `s ≤ 1` the condition is lost as well
  (`mem_closure_realPWBandPolarFreeCore_of_schwartz_half`,
  `exists_mem_closure_realPWBandPolarFreeCore_integral_ne_zero_half`). A single dilate no longer
  has small norm. The sum over `n < N` of the dilates by `2 ^ n`, with weights proportional to
  `1 / (n + 1)`, keeps integral one and has square norm of order one over the `N`-th harmonic
  number.
* Above width one half, and at width one half for `s > 1`, the condition survives. The
  reciprocal of the weight is integrable (`integrable_inv_realPWIntervalWeight`,
  `integrable_inv_realPWIntervalWeight_half`), so the integral is a continuous linear functional
  on the band and vanishes on the closure (`exists_realPWBand_integralFunctional_of_integrable`).
  Up to width three halves it is a condition of its own
  (`exists_realPWBand_notMem_closure_polarFreeCore_of_integrable`).

Reconstruction: The paper does not state this. The core is that of the order-zero model of the
rational real place.

So for `s ≥ 0` the condition is lost exactly when `α < 1 / 2`, or `α = 1 / 2` and `s ≤ 1`.

For `α < 1 / 2` the closure is exactly the kernel of evaluation at the origin. That is proved
in `Sec4_RealPWBandDensity`, from the density of Schwartz functions in the band.

Not treated here: the closure at width one half for `s ≤ 1`. The last statement of the list for
`α ≥ 3 / 2`. -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- An even Schwartz function with Fourier transform supported in `[-Y, Y]` and integral one:
the inverse Fourier transform of an even bump. -/
private theorem exists_evenSchwartz_band_integral_one {Y : ℝ} (hY : 0 < Y) :
    ∃ φ : 𝓢(ℝ, ℂ), Function.Even (φ : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 φ) ξ = 0) ∧
      ∫ x, φ x = 1 := by
  let B : ContDiffBump (0 : ℝ) := ⟨Y / 2, Y, by positivity, by linarith⟩
  let b : 𝓢(ℝ, ℂ) := (B.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  have hb (x : ℝ) : b x = (B x : ℂ) := rfl
  have hbg (x : ℝ) : b (-x) = b x := by simp only [hb, B.neg]
  have hinv : 𝓕⁻ (b : ℝ → ℂ) = 𝓕 (b : ℝ → ℂ) := by
    rw [Real.fourierInv_eq_fourier_comp_neg, show (fun x ↦ b (-x)) = (b : ℝ → ℂ) from funext hbg]
  let φ : 𝓢(ℝ, ℂ) := 𝓕⁻ b
  have hF : 𝓕 φ = b := FourierTransform.fourier_fourierInv_eq _
  refine ⟨φ, fun x ↦ ?_, fun ξ hξ ↦ ?_, ?_⟩
  · change (𝓕⁻ b : 𝓢(ℝ, ℂ)) (-x) = (𝓕⁻ b : 𝓢(ℝ, ℂ)) x
    simp only [SchwartzMap.fourierInv_coe]
    rw [Real.fourierInv_eq_fourier_neg, neg_neg, hinv]
  · rw [hF, hb]
    have hz : B ξ = 0 := B.zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]
      change Y ≤ |ξ|
      by_contra h
      exact hξ (abs_le.mp (not_le.mp h).le))
    rw [hz, Complex.ofReal_zero]
  · have h0 : (𝓕 φ) 0 = ∫ x, φ x := by
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
      simp
    rw [← h0, hF, hb, B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le),
      Complex.ofReal_one]

/-- The dilate `x ↦ φ (x / t)` of a Schwartz function. -/
private def schwartzDilate (t : ℝ) (ht : t ≠ 0) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 t⁻¹ (inv_ne_zero ht))) φ

private theorem schwartzDilate_apply (t : ℝ) (ht : t ≠ 0) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzDilate t ht φ x = φ (x * t⁻¹) := rfl

private theorem schwartzDilate_even (t : ℝ) (ht : t ≠ 0) (φ : 𝓢(ℝ, ℂ))
    (he : Function.Even (φ : ℝ → ℂ)) : Function.Even (schwartzDilate t ht φ : ℝ → ℂ) := fun x ↦ by
  rw [schwartzDilate_apply, schwartzDilate_apply, neg_mul, he]

private theorem integral_schwartzDilate {t : ℝ} (ht : 0 < t) (φ : 𝓢(ℝ, ℂ)) :
    ∫ x, schwartzDilate t ht.ne' φ x = t • ∫ x, φ x := by
  have h := MeasureTheory.Measure.integral_comp_mul_right (fun u : ℝ ↦ φ u) t⁻¹
  rw [inv_inv, abs_of_pos ht] at h
  exact h

private theorem fourier_schwartzDilate {t : ℝ} (ht : 0 < t) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (schwartzDilate t ht.ne' φ)) ξ = t • (𝓕 φ) (t * ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_real_eq,
    Real.fourier_real_eq]
  have h := MeasureTheory.Measure.integral_comp_mul_right
    (fun u : ℝ ↦ 𝐞 (-(u * (t * ξ))) • φ u) t⁻¹
  rw [inv_inv, abs_of_pos ht] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
  simp only [schwartzDilate_apply]
  congr 3
  field_simp

private theorem schwartzDilate_band {t Y : ℝ} (ht : 1 ≤ t) (hY : 0 ≤ Y) (φ : 𝓢(ℝ, ℂ))
    (hb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 φ) ξ = 0) :
    ∀ ξ ∉ Icc (-Y) Y, (𝓕 (schwartzDilate t (zero_lt_one.trans_le ht).ne' φ)) ξ = 0 := by
  intro ξ hξ
  rw [fourier_schwartzDilate (zero_lt_one.trans_le ht), hb, smul_zero]
  intro h
  apply hξ
  rcases le_total 0 ξ with h0 | h0
  · exact ⟨by linarith, by nlinarith [h.2]⟩
  · exact ⟨by nlinarith [h.1], by linarith⟩

/-- An even Schwartz function with Fourier transform supported in `[-Y, Y]` that vanishes at the
origin and has integral one. -/
private theorem exists_evenSchwartz_band_zero_integral_one {Y : ℝ} (hY : 0 < Y) :
    ∃ k : 𝓢(ℝ, ℂ), Function.Even (k : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 k) ξ = 0) ∧ k 0 = 0 ∧
      ∫ x, k x = 1 := by
  obtain ⟨φ, he, hb, hi⟩ := exists_evenSchwartz_band_integral_one hY
  have h2 : (1 : ℝ) ≤ 2 := by norm_num
  refine ⟨schwartzDilate 2 two_ne_zero φ - φ, fun x ↦ ?_, fun ξ hξ ↦ ?_, ?_, ?_⟩
  · simp only [sub_apply]
    rw [schwartzDilate_even 2 two_ne_zero φ he x, he x]
  · rw [FourierTransform.fourier_sub, sub_apply,
      schwartzDilate_band h2 hY.le φ hb ξ hξ, hb ξ hξ, sub_zero]
  · simp [schwartzDilate_apply]
  · have hI : ∫ x, (schwartzDilate 2 two_ne_zero φ - φ) x =
        (∫ x, schwartzDilate 2 two_ne_zero φ x) - ∫ x, φ x := by
      simp only [sub_apply]
      exact integral_sub (schwartzDilate 2 two_ne_zero φ).integrable φ.integrable
    rw [hI, integral_schwartzDilate two_pos, hi]
    simp only [Complex.real_smul]
    norm_num

section Core

variable {Y α s : ℝ}

/-- The polar-free core of the weighted band: the band vectors represented by an even Schwartz
function with Fourier transform supported in `[-Y, Y]` that vanishes at the origin and has
integral zero. -/
@[expose] def realPWBandPolarFreeCore (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Set (RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :=
  {f | ∃ g : 𝓢(ℝ, ℂ), Function.Even (g : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧ g 0 = 0 ∧
    ∫ x, g x = 0 ∧
    (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) = (g : ℝ → ℂ)}

/-- The squared norm of a band vector is the weighted integral of its pointwise values. -/
theorem norm_sq_realPWBand_of_evaluation_eq (hs : 0 ≤ s)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) (u : ℝ → ℂ)
    (hu : (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) = u) :
    ‖f‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂realPWIntervalMeasure α s := by
  have hae := RealPWBand.evaluation_ae Y (volume_le_realPWIntervalMeasure α s hs)
    (realPWIntervalMeasure_absolutelyContinuous α s) f
  rw [hu] at hae
  have h1 := L2.integral_sq_norm (𝕜 := ℂ) (f.val : Lp ℂ 2 (realPWIntervalMeasure α s))
  change ‖(f.val : Lp ℂ 2 (realPWIntervalMeasure α s))‖ ^ 2 = _
  rw [← h1]
  exact integral_congr_ae (hae.mono fun x hx ↦ by simp only [hx])

/-- The polynomial factor of the dilation constant is dominated by an exponential of small
rate. -/
private theorem one_add_sq_rpow_le_exp (hs : 0 ≤ s) (m : ℕ) (hm : 1 ≤ m) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (1 + ℓ + ℓ ^ 2) ^ (s / 2) ≤ Real.exp (s * Real.log m) * Real.exp (s / m * ℓ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hme : (m : ℝ) * Real.exp (ℓ / m) = Real.exp (Real.log m + ℓ / m) := by
    rw [Real.exp_add, Real.exp_log hm0]
  have hbase : 1 + ℓ + ℓ ^ 2 ≤ Real.exp (2 * Real.log m + 2 * ℓ / m) := by
    have h1 : ℓ / m + 1 ≤ Real.exp (ℓ / m) := Real.add_one_le_exp _
    have h2 : (m : ℝ) + ℓ ≤ m * Real.exp (ℓ / m) := by
      have h := mul_le_mul_of_nonneg_left h1 hm0.le
      rw [mul_add, mul_one, mul_div_cancel₀ ℓ hm0.ne'] at h
      linarith
    have h3 : Real.exp (2 * Real.log m + 2 * ℓ / m) = ((m : ℝ) * Real.exp (ℓ / m)) ^ 2 := by
      rw [hme, sq, ← Real.exp_add]
      congr 1
      ring
    rw [h3]
    calc 1 + ℓ + ℓ ^ 2 ≤ ((m : ℝ) + ℓ) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_left₀ (by linarith) h2 2
  have hpow : (1 + ℓ + ℓ ^ 2) ^ (s / 2) ≤
      Real.exp ((2 * Real.log m + 2 * ℓ / m) * (s / 2)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  refine hpow.trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  field_simp

/-- Below width one half the dilation constant divided by the dilation factor is arbitrarily
small. -/
private theorem exists_dilation_factor_lt (hα' : α < 1 / 2) (hs : 0 ≤ s) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t : ℝ, 1 ≤ t ∧ Real.exp (2 * α * Real.log t) *
      (1 + Real.log t + Real.log t ^ 2) ^ (s / 2) / t < ε := by
  have hgap : 0 < 1 - 2 * α := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (s / (1 - 2 * α))
  let m : ℕ := max m₀ 1
  have hm1 : 1 ≤ m := le_max_right _ _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmbig : s / (1 - 2 * α) < m := hm₀.trans_le (by exact_mod_cast le_max_left m₀ 1)
  have hδ : 0 < 1 - 2 * α - s / m := by
    have h1 : s < (1 - 2 * α) * m := by rwa [div_lt_iff₀ hgap, mul_comm] at hmbig
    have h2 : s / m < 1 - 2 * α := by rwa [div_lt_iff₀ hm0]
    linarith
  let δ := 1 - 2 * α - s / m
  let A := Real.exp (s * Real.log m)
  have hlim : Tendsto (fun ℓ : ℝ ↦ A * Real.exp (-(δ * ℓ))) atTop (𝓝 (A * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hδ)).const_mul A
  rw [mul_zero] at hlim
  obtain ⟨ℓ, hℓε, hℓ0⟩ := ((hlim.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 0)).exists
  refine ⟨Real.exp ℓ, Real.one_le_exp hℓ0, ?_⟩
  rw [Real.log_exp]
  refine lt_of_le_of_lt ?_ hℓε
  have hP := one_add_sq_rpow_le_exp hs m hm1 hℓ0
  calc Real.exp (2 * α * ℓ) * (1 + ℓ + ℓ ^ 2) ^ (s / 2) / Real.exp ℓ
      ≤ Real.exp (2 * α * ℓ) * (Real.exp (s * Real.log m) * Real.exp (s / m * ℓ)) /
          Real.exp ℓ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = A * Real.exp (-(δ * ℓ)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add]
        congr 1
        ring

/-- A dilation by `t ≥ 1` increases the weighted square integral by at most the dilation
constant times `t`. -/
private theorem integral_norm_sq_dilate_le (hα : 0 ≤ α) (hs : 0 ≤ s) {t : ℝ} (ht : 1 ≤ t)
    (G : ℝ → ℂ) (hG : Continuous G) (hm : MemLp G 2 (realPWIntervalMeasure α s)) :
    ∫ x, ‖G (x * t⁻¹)‖ ^ 2 ∂realPWIntervalMeasure α s ≤
      (Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2) * t) *
        ∫ x, ‖G x‖ ^ 2 ∂realPWIntervalMeasure α s := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  let a := t⁻¹
  have ha : 0 < a := inv_pos.mpr ht0
  let C := Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCa : Real.exp (2 * |α * Real.log a|) * (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2) =
      C := by
    have h1 : Real.log a = -Real.log t := Real.log_inv t
    rw [h1, mul_neg, abs_neg, abs_neg, neg_sq, abs_of_nonneg (mul_nonneg hα hlog),
      abs_of_nonneg hlog, ← mul_assoc]
  let W := fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x)
  have hW : Measurable W := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hmul : Measurable (a * ·) := measurable_const_mul a
  let k := ENNReal.ofReal C * ENNReal.ofReal t
  have hmap : Measure.map (a * ·) (realPWIntervalMeasure α s) ≤ k • realPWIntervalMeasure α s := by
    apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.map_apply hmul hS, smul_apply, realPWIntervalMeasure,
      withDensity_apply _ (hmul hS), withDensity_apply _ hS]
    change (∫⁻ x in (a * ·) ⁻¹' S, W x) ≤ k * ∫⁻ x in S, W x
    calc
      _ ≤ ∫⁻ x in (a * ·) ⁻¹' S, ENNReal.ofReal C * W (a * x) := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (realPWIntervalWeight α s x) ≤
          ENNReal.ofReal C * ENNReal.ofReal (realPWIntervalWeight α s (a * x))
        rw [← ENNReal.ofReal_mul hC, ← hCa]
        exact ENNReal.ofReal_le_ofReal (realPWIntervalWeight_le_dilation hs ha x)
      _ = ENNReal.ofReal C * ∫⁻ y in S, W y ∂Measure.map (a * ·) volume := by
        rw [setLIntegral_map hS hW hmul]
        exact lintegral_const_mul _ (hW.comp hmul)
      _ = _ := by
        rw [Real.map_volume_mul_left ha.ne', setLIntegral_smul_measure, smul_eq_mul, ← mul_assoc,
          inv_inv, abs_of_pos ht0]
  have hI : Integrable (fun x ↦ ‖G x‖ ^ 2) (realPWIntervalMeasure α s) :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hm
  have hk : k ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hc2 : Continuous fun y : ℝ ↦ ‖G y‖ ^ 2 := hG.norm.pow 2
  have hkr : k.toReal = C * t := by
    dsimp [k]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal ht0.le]
  calc ∫ x, ‖G (x * t⁻¹)‖ ^ 2 ∂realPWIntervalMeasure α s
      = ∫ y, ‖G y‖ ^ 2 ∂Measure.map (a * ·) (realPWIntervalMeasure α s) := by
        rw [integral_map hmul.aemeasurable hc2.aestronglyMeasurable]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [a, mul_comm]
    _ ≤ ∫ y, ‖G y‖ ^ 2 ∂(k • realPWIntervalMeasure α s) :=
        integral_mono_measure hmap (ae_of_all _ fun _ ↦ sq_nonneg _) (hI.smul_measure hk)
    _ = _ := by
        rw [integral_smul_measure, hkr, smul_eq_mul]

/-- Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30). Below width one half, the closure of the
polar-free core contains every band vector that is represented by an even Schwartz function
with Fourier transform in the band and vanishing at the origin, whatever its integral. The
condition that the integral vanishes does not survive the closure.
Reconstruction: The paper does not state this. The core is the one of the order-zero model. -/
theorem mem_closure_realPWBandPolarFreeCore_of_schwartz (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hs : 0 ≤ s) (hY : 0 < Y) (g : 𝓢(ℝ, ℂ)) (he : Function.Even (g : ℝ → ℂ))
    (hb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) (h0 : g 0 = 0)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs))
    (hf : (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) =
      (g : ℝ → ℂ)) :
    f ∈ closure (realPWBandPolarFreeCore Y α hs) := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let μ := realPWIntervalMeasure α s
  obtain ⟨k, hke, hkb, hk0, hki⟩ := exists_evenSchwartz_band_zero_integral_one hY
  have hmem (ψ : 𝓢(ℝ, ℂ)) (hψ : Function.Even (ψ : ℝ → ℂ)) : MemLp (ψ : ℝ → ℂ) 2 μ := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (ψ.continuous.continuousOn (s := Icc (-4 : ℝ) 4))
    refine memLp_realPWIntervalMeasure_of_evenSchwartz_order hα hs ψ hψ 0
      (by norm_num; linarith) ⟨C, fun x hx ↦ ?_⟩
    simpa using hC x (abs_le.mp hx)
  have hkm := hmem k hke
  let c : ℂ := ∫ x, g x
  let I₀ : ℝ := ∫ x, ‖k x‖ ^ 2 ∂μ
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun _ ↦ sq_nonneg _
  let N : ℝ := ‖c‖ ^ 2 * I₀
  have hN : 0 ≤ N := mul_nonneg (sq_nonneg _) hI₀
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t, ht1, htε⟩ := exists_dilation_factor_lt hα' hs (ε := ε ^ 2 / (N + 1))
    (div_pos (sq_pos_of_pos hε) (by linarith))
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  let kt : 𝓢(ℝ, ℂ) := (t⁻¹ : ℂ) • schwartzDilate t ht0.ne' k
  let gt : 𝓢(ℝ, ℂ) := g - c • kt
  have hktx (x : ℝ) : kt x = (t⁻¹ : ℂ) * k (x * t⁻¹) := rfl
  have hgtx (x : ℝ) : gt x = g x - c * kt x := rfl
  have hkte : Function.Even (kt : ℝ → ℂ) := fun x ↦ by
    rw [hktx, hktx, neg_mul, hke]
  have hgte : Function.Even (gt : ℝ → ℂ) := fun x ↦ by
    rw [hgtx, hgtx, he x, hkte x]
  have hktb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 kt) ξ = 0 := fun ξ hξ ↦ by
    change (𝓕 ((t⁻¹ : ℂ) • schwartzDilate t ht0.ne' k)) ξ = 0
    rw [FourierTransform.fourier_smul, smul_apply, schwartzDilate_band ht1 hY.le k hkb ξ hξ,
      smul_zero]
  have hgtb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 gt) ξ = 0 := fun ξ hξ ↦ by
    change (𝓕 (g - c • kt)) ξ = 0
    rw [FourierTransform.fourier_sub, sub_apply, FourierTransform.fourier_smul, smul_apply,
      hb ξ hξ, hktb ξ hξ, smul_zero, sub_zero]
  have hgt0 : gt 0 = 0 := by
    rw [hgtx, hktx, zero_mul, hk0, h0, mul_zero, mul_zero, sub_zero]
  have hkti : ∫ x, kt x = 1 := by
    have h1 : ∫ x, kt x = (t⁻¹ : ℂ) * ∫ x, schwartzDilate t ht0.ne' k x :=
      integral_const_mul _ _
    rw [h1, integral_schwartzDilate ht0, hki, Complex.real_smul, mul_one,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ ht0.ne', Complex.ofReal_one]
  have hgti : ∫ x, gt x = 0 := by
    have h1 : ∫ x, gt x = (∫ x, g x) - c * ∫ x, kt x := by
      have h2 : Integrable (fun x ↦ c * kt x) := kt.integrable.const_mul c
      rw [← integral_const_mul, ← integral_sub g.integrable h2]
      rfl
    rw [h1, hkti, mul_one, sub_self]
  obtain ⟨ft, hft⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y gt hgte hgtb hμ
    (hmem gt hgte)
  refine ⟨ft, ⟨gt, hgte, hgtb, hgt0, hgti, hft⟩, ?_⟩
  have hdiff : (fun x ↦ RealPWBand.evaluation Y hμ x (f - ft)) = fun x ↦ c * kt x := by
    funext x
    rw [map_sub, congrFun hf x, congrFun hft x, hgtx, sub_sub_cancel]
  have hnorm := norm_sq_realPWBand_of_evaluation_eq hs (f - ft) _ hdiff
  let E := Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2)
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpt (x : ℝ) : ‖c * kt x‖ ^ 2 = ‖c‖ ^ 2 * (t⁻¹) ^ 2 * ‖k (x * t⁻¹)‖ ^ 2 := by
    rw [hktx, norm_mul, norm_mul, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
    ring
  have hbound : ‖f - ft‖ ^ 2 ≤ E / t * N := by
    rw [hnorm]
    simp only [hpt]
    rw [integral_const_mul]
    have h3 := integral_norm_sq_dilate_le hα hs ht1 (k : ℝ → ℂ) k.continuous hkm
    calc ‖c‖ ^ 2 * (t⁻¹) ^ 2 * ∫ x, ‖k (x * t⁻¹)‖ ^ 2 ∂realPWIntervalMeasure α s
        ≤ ‖c‖ ^ 2 * (t⁻¹) ^ 2 * (E * t * I₀) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = E / t * N := by
          dsimp [N]
          field_simp
  have hlt : ‖f - ft‖ ^ 2 < ε ^ 2 := by
    have h4 : E / t * N ≤ ε ^ 2 / (N + 1) * N := mul_le_mul_of_nonneg_right htε.le hN
    have h5 : ε ^ 2 / (N + 1) * N < ε ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith [sq_pos_of_pos hε]
    exact (hbound.trans h4).trans_lt h5
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- Below width one half the closure of the polar-free core contains a band vector, represented
by an even Schwartz function vanishing at the origin, whose integral is not zero. -/
theorem exists_mem_closure_realPWBandPolarFreeCore_integral_ne_zero (hα : 0 ≤ α)
    (hα' : α < 1 / 2) (hs : 0 ≤ s) (hY : 0 < Y) :
    ∃ (g : 𝓢(ℝ, ℂ)) (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)),
      f ∈ closure (realPWBandPolarFreeCore Y α hs) ∧
      (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) =
        (g : ℝ → ℂ) ∧ g 0 = 0 ∧ ∫ x, g x ≠ 0 := by
  obtain ⟨k, hke, hkb, hk0, hki⟩ := exists_evenSchwartz_band_zero_integral_one hY
  have hkm : MemLp (k : ℝ → ℂ) 2 (realPWIntervalMeasure α s) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (k.continuous.continuousOn (s := Icc (-4 : ℝ) 4))
    refine memLp_realPWIntervalMeasure_of_evenSchwartz_order hα hs k hke 0
      (by norm_num; linarith) ⟨C, fun x hx ↦ ?_⟩
    simpa using hC x (abs_le.mp hx)
  obtain ⟨f, hf⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y k hke hkb
    (volume_le_realPWIntervalMeasure α s hs) hkm
  exact ⟨k, f, mem_closure_realPWBandPolarFreeCore_of_schwartz hα hα' hs hY k hke hkb hk0 f hf,
    hf, hk0, by rw [hki]; exact one_ne_zero⟩

end Core

section AboveThreshold

variable {Y α s : ℝ}

/-- Above width one half the reciprocal of the weight of (9.2.1.30) is integrable. -/
theorem integrable_inv_realPWIntervalWeight (hα : 1 / 2 < α) (hs : 0 ≤ s) :
    Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹) := by
  have h2α : 0 ≤ 2 * α := by linarith
  have hlow (x : ℝ) : ((1 + |x|) / 2) ^ (2 * α) ≤ realPWIntervalWeight α s x := by
    by_cases hx : x = 0
    · subst hx
      have h1 : realPWIntervalWeight α s 0 = 1 := by simp [realPWIntervalWeight]
      rw [h1, abs_zero, add_zero]
      exact Real.rpow_le_one (by norm_num) (by norm_num) h2α
    · rw [realPWIntervalWeight_eq α s hx]
      have hlogf : 1 ≤ (1 + Real.log |x| ^ 2) ^ (s / 2) :=
        Real.one_le_rpow (by nlinarith [sq_nonneg (Real.log |x|)]) (by positivity)
      have hax : 0 < |x| := abs_pos.mpr hx
      have hmax : ((1 + |x|) / 2) ^ (2 * α) ≤ max (|x| ^ (2 * α)) (|x| ^ (-(2 * α))) := by
        rcases le_total 1 |x| with h1 | h1
        · exact (Real.rpow_le_rpow (by positivity) (by linarith) h2α).trans (le_max_left _ _)
        · have ha : ((1 + |x|) / 2) ^ (2 * α) ≤ 1 :=
            Real.rpow_le_one (by positivity) (by linarith) h2α
          have hb : 1 ≤ |x| ^ (-(2 * α)) :=
            Real.one_le_rpow_of_pos_of_le_one_of_nonpos hax h1 (by linarith)
          exact (ha.trans hb).trans (le_max_right _ _)
      calc ((1 + |x|) / 2) ^ (2 * α)
          ≤ max (|x| ^ (2 * α)) (|x| ^ (-(2 * α))) * 1 := by rw [mul_one]; exact hmax
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogf (le_max_of_le_left (by positivity))
  have hfin : (Module.finrank ℝ ℝ : ℝ) < 2 * α := by
    rw [Module.finrank_self]
    push_cast
    linarith
  have hint : Integrable (fun x : ℝ ↦ (2 : ℝ) ^ (2 * α) * (1 + ‖x‖) ^ (-(2 * α))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) hfin).const_mul _
  refine hint.mono' (measurable_realPWIntervalWeight α s).inv.aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have hw : 0 < realPWIntervalWeight α s x :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hw.le)]
  have hpos : 0 < ((1 + |x|) / 2) ^ (2 * α) := by positivity
  calc (realPWIntervalWeight α s x)⁻¹ ≤ (((1 + |x|) / 2) ^ (2 * α))⁻¹ :=
        inv_anti₀ hpos (hlow x)
    _ = 2 ^ (2 * α) * (1 + ‖x‖) ^ (-(2 * α)) := by
        rw [Real.norm_eq_abs, Real.div_rpow (by positivity) (by norm_num), inv_div,
          Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- At width one half the reciprocal of the weight of (9.2.1.30) is integrable when the
logarithmic order exceeds one. -/
theorem integrable_inv_realPWIntervalWeight_half (hs1 : 1 < s) :
    Integrable (fun x ↦ (realPWIntervalWeight (1 / 2) s x)⁻¹) := by
  have hs : 0 ≤ s := by linarith
  let w := realPWIntervalWeight (1 / 2) s
  have hw1 (x : ℝ) : 1 ≤ w x := one_le_realPWIntervalWeight (1 / 2) s hs x
  have hmeas : Measurable fun x ↦ (w x)⁻¹ := (measurable_realPWIntervalWeight (1 / 2) s).inv
  let G : ℝ → ℝ := fun x ↦ -(1 / (s - 1)) * (1 + Real.log x) ^ (1 - s)
  let G' : ℝ → ℝ := fun x ↦ x⁻¹ * (1 + Real.log x) ^ (-s)
  have hderiv : ∀ x ∈ Ici (1 : ℝ), HasDerivAt G (G' x) x := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hb : 0 < 1 + Real.log x := by
      have := Real.log_nonneg hx
      linarith
    have h1 : HasDerivAt (fun y ↦ 1 + Real.log y) x⁻¹ x :=
      (Real.hasDerivAt_log hx0.ne').const_add 1
    have h2 := (h1.rpow_const (p := 1 - s) (Or.inl hb.ne')).const_mul (-(1 / (s - 1)))
    have he : (1 : ℝ) - s - 1 = -s := by ring
    have hs0 : s - 1 ≠ 0 := by linarith
    have hG'x : G' x =
        -(1 / (s - 1)) * (x⁻¹ * (1 - s) * (1 + Real.log x) ^ (1 - s - 1)) := by
      change x⁻¹ * (1 + Real.log x) ^ (-s) = _
      rw [he]
      field_simp
      ring
    rw [hG'x]
    exact h2
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ ↦ 1 + Real.log x) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 Real.tendsto_log_atTop
    have h2 := (tendsto_rpow_neg_atTop (show 0 < s - 1 by linarith)).comp h1
    have h3 := h2.const_mul (-(1 / (s - 1)))
    rw [mul_zero] at h3
    refine h3.congr fun x ↦ ?_
    simp only [G, Function.comp_apply, neg_sub]
  have hG'nn : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ G' x := fun x hx ↦
    mul_nonneg (inv_nonneg.mpr (zero_le_one.trans (le_of_lt hx)))
      (Real.rpow_nonneg (by have := Real.log_nonneg (le_of_lt hx); linarith) _)
  have hG' : IntegrableOn G' (Ioi 1) := integrableOn_Ioi_deriv_of_nonneg' hderiv hG'nn hlim
  have htail : ∀ x ∈ Ioi (1 : ℝ), (w x)⁻¹ ≤ 2 ^ (s / 2) * G' x := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hL : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hwx : x * (1 + Real.log x ^ 2) ^ (s / 2) ≤ w x := by
      change _ ≤ realPWIntervalWeight (1 / 2) s x
      rw [realPWIntervalWeight_eq (1 / 2) s hx0.ne', abs_of_pos hx0]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine le_trans ?_ (le_max_left _ _)
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    have hpow : (1 + Real.log x) ^ s ≤ 2 ^ (s / 2) * (1 + Real.log x ^ 2) ^ (s / 2) := by
      have h1 : (1 + Real.log x) ^ s = ((1 + Real.log x) ^ (2 : ℝ)) ^ (s / 2) := by
        rw [← Real.rpow_mul (by linarith)]
        congr 1
        ring
      rw [h1, ← Real.mul_rpow (by norm_num) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      rw [Real.rpow_two]
      nlinarith [sq_nonneg (Real.log x - 1)]
    have hbase : 0 < 1 + Real.log x := by linarith
    have hpos : 0 < x * (1 + Real.log x ^ 2) ^ (s / 2) := by positivity
    have hA : 0 < (1 + Real.log x ^ 2) ^ (s / 2) := by positivity
    have hB : 0 < (1 + Real.log x) ^ s := Real.rpow_pos_of_pos hbase s
    have key : ((1 + Real.log x ^ 2) ^ (s / 2))⁻¹ ≤ 2 ^ (s / 2) * ((1 + Real.log x) ^ s)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hB, inv_mul_le_iff₀ hA]
      linarith [hpow]
    calc (w x)⁻¹ ≤ (x * (1 + Real.log x ^ 2) ^ (s / 2))⁻¹ := inv_anti₀ hpos hwx
      _ = x⁻¹ * ((1 + Real.log x ^ 2) ^ (s / 2))⁻¹ := mul_inv _ _
      _ ≤ x⁻¹ * (2 ^ (s / 2) * ((1 + Real.log x) ^ s)⁻¹) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hx0.le)
      _ = 2 ^ (s / 2) * (x⁻¹ * (1 + Real.log x) ^ (-s)) := by
          rw [Real.rpow_neg hbase.le]
          ring
  have hI1 : IntegrableOn (fun x ↦ (w x)⁻¹) (Ioi 1) := by
    refine (hG'.const_mul (2 ^ (s / 2))).mono' hmeas.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_)
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (hw1 x)))]
    exact htail x hx
  have hI2 : IntegrableOn (fun x ↦ (w x)⁻¹) (Icc (-1) 1) :=
    Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne hmeas.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (hw1 x)))]
        exact inv_le_one_of_one_le₀ (hw1 x))
  have hI3 : IntegrableOn (fun x ↦ (w x)⁻¹) (Iio (-1)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := fun x ↦ (w x)⁻¹) (s := Ioi 1)
    have hpre : (Neg.neg ⁻¹' Ioi (1 : ℝ)) = Iio (-1) := by
      ext x
      simp [lt_neg]
    have hcomp : ((fun x ↦ (w x)⁻¹) ∘ Neg.neg) = fun x ↦ (w x)⁻¹ := funext fun x ↦ by
      change (realPWIntervalWeight (1 / 2) s (-x))⁻¹ = (realPWIntervalWeight (1 / 2) s x)⁻¹
      rw [realPWIntervalWeight_even]
    rw [hpre, hcomp] at h
    exact h.mpr hI1
  have huniv : (univ : Set ℝ) = Iio (-1) ∪ Icc (-1) 1 ∪ Ioi 1 := by
    ext x
    simp only [mem_univ, mem_union, mem_Iio, mem_Icc, mem_Ioi, true_iff]
    rcases lt_or_ge x (-1) with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt x 1 with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr h'
  rw [← integrableOn_univ, huniv]
  exact (hI3.union hI2).union hI1

/-- When the reciprocal of the weight is integrable it is a vector of the weighted space. -/
private theorem memLp_inv_realPWIntervalWeight (hs : 0 ≤ s)
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) :
    MemLp (fun x ↦ (((realPWIntervalWeight α s x)⁻¹ : ℝ) : ℂ)) 2 (realPWIntervalMeasure α s) := by
  have hmeas : Measurable fun x ↦ (((realPWIntervalWeight α s x)⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_realPWIntervalWeight α s).inv
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable, realPWIntervalMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_realPWIntervalWeight α s).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine hint.congr (ae_of_all _ fun x ↦ ?_)
  have hw : 0 < realPWIntervalWeight α s x :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  change (realPWIntervalWeight α s x)⁻¹ = (ENNReal.ofReal (realPWIntervalWeight α s x)).toReal •
    ‖(((realPWIntervalWeight α s x)⁻¹ : ℝ) : ℂ)‖ ^ 2
  rw [ENNReal.toReal_ofReal hw.le, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hw.le),
    smul_eq_mul]
  field_simp

/-- Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30). When the reciprocal of the weight is integrable,
every band vector is integrable, the integral is a continuous linear functional on the band, and
it vanishes on the closure of the polar-free core. The condition that the integral vanishes
survives the closure. The hypothesis holds above width one half
(`integrable_inv_realPWIntervalWeight`) and at width one half for `s > 1`
(`integrable_inv_realPWIntervalWeight_half`).
Reconstruction: The paper does not state this. -/
theorem exists_realPWBand_integralFunctional_of_integrable (hs : 0 ≤ s)
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) :
    ∃ I : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) →L[ℂ] ℂ,
      (∀ f, Integrable (fun x ↦
          RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) ∧
        I f = ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) ∧
      ∀ f ∈ closure (realPWBandPolarFreeCore Y α hs), I f = 0 := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let μ := realPWIntervalMeasure α s
  let w := realPWIntervalWeight α s
  have hw (x : ℝ) : 0 < w x := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  have hWm : Measurable fun x ↦ ENNReal.ofReal (w x) :=
    (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hWlt : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (w x) < ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hV := memLp_inv_realPWIntervalWeight hs hint
  let V : Lp ℂ 2 μ := hV.toLp _
  let I : RealPWBand.space Y hμ →L[ℂ] ℂ := (innerSL ℂ V).comp (RealPWBand.space Y hμ).subtypeL
  have hI (f : RealPWBand.space Y hμ) :
      Integrable (fun x ↦ RealPWBand.evaluation Y hμ x f) ∧
        I f = ∫ x, RealPWBand.evaluation Y hμ x f := by
    have hae := RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) f
    have hinner : ∀ᵐ x ∂μ, ⟪V x, (f.val : Lp ℂ 2 μ) x⟫_ℂ =
        ((w x)⁻¹ : ℝ) • RealPWBand.evaluation Y hμ x f := by
      filter_upwards [hae, hV.coeFn_toLp] with x h1 h2
      rw [show V x = (((w x)⁻¹ : ℝ) : ℂ) from h2, ← h1, RCLike.inner_apply, Complex.conj_ofReal,
        Complex.real_smul, mul_comm]
    have hInt : Integrable (fun x ↦ ((w x)⁻¹ : ℝ) • RealPWBand.evaluation Y hμ x f) μ :=
      (L2.integrable_inner (𝕜 := ℂ) V (f.val : Lp ℂ 2 μ)).congr hinner
    have hsimp (x : ℝ) : (ENNReal.ofReal (w x)).toReal •
        (((w x)⁻¹ : ℝ) • RealPWBand.evaluation Y hμ x f) = RealPWBand.evaluation Y hμ x f := by
      rw [ENNReal.toReal_ofReal (hw x).le, smul_smul, mul_inv_cancel₀ (hw x).ne', one_smul]
    have hconv := (integrable_withDensity_iff_integrable_smul' hWm hWlt).mp hInt
    refine ⟨hconv.congr (ae_of_all _ hsimp), ?_⟩
    change ⟪V, (f.val : Lp ℂ 2 μ)⟫_ℂ = _
    rw [L2.inner_def, integral_congr_ae hinner]
    change ∫ x, ((w x)⁻¹ : ℝ) • RealPWBand.evaluation Y hμ x f
      ∂((volume : Measure ℝ).withDensity fun x ↦ ENNReal.ofReal (w x)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hWm hWlt]
    exact integral_congr_ae (ae_of_all _ hsimp)
  refine ⟨I, hI, fun f hf ↦ ?_⟩
  have hclosed : IsClosed {f : RealPWBand.space Y hμ | I f = 0} :=
    isClosed_eq I.continuous continuous_const
  refine closure_minimal (fun f hf ↦ ?_) hclosed hf
  obtain ⟨g, -, -, -, hgi, hfg⟩ := hf
  change I f = 0
  rw [(hI f).2, hfg]
  exact hgi

/-- Above width one half every band vector is integrable, the integral is a continuous linear
functional on the band, and it vanishes on the closure of the polar-free core. -/
theorem exists_realPWBand_integralFunctional (hα : 1 / 2 < α) (hs : 0 ≤ s) :
    ∃ I : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) →L[ℂ] ℂ,
      (∀ f, Integrable (fun x ↦
          RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) ∧
        I f = ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) ∧
      ∀ f ∈ closure (realPWBandPolarFreeCore Y α hs), I f = 0 :=
  exists_realPWBand_integralFunctional_of_integrable hs (integrable_inv_realPWIntervalWeight hα hs)

/-- At width one half, for `s > 1`, every band vector is integrable, the integral is a
continuous linear functional on the band, and it vanishes on the closure of the polar-free
core. -/
theorem exists_realPWBand_integralFunctional_half (hs : 0 ≤ s) (hs1 : 1 < s) :
    ∃ I : RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) →L[ℂ] ℂ,
      (∀ f, Integrable (fun x ↦
          RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) x f) ∧
        I f = ∫ x,
          RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) x f) ∧
      ∀ f ∈ closure (realPWBandPolarFreeCore Y (1 / 2) hs), I f = 0 :=
  exists_realPWBand_integralFunctional_of_integrable hs
    (integrable_inv_realPWIntervalWeight_half hs1)

/-- Below width three halves, when the reciprocal of the weight is integrable, there is a band
vector that vanishes at the origin and is not in the closure of the polar-free core: the
vanishing of the integral is a condition of its own. -/
theorem exists_realPWBand_notMem_closure_polarFreeCore_of_integrable (hα : 0 ≤ α)
    (hα' : α < 3 / 2) (hs : 0 ≤ s) (hY : 0 < Y)
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) :
    ∃ f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs),
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0 ∧
        f ∉ closure (realPWBandPolarFreeCore Y α hs) := by
  obtain ⟨k, hke, hkb, hk0, hki⟩ := exists_evenSchwartz_band_zero_integral_one hY
  obtain ⟨C, -, hC⟩ := k.decay 0 1
  have hfd (x : ℝ) : ‖fderiv ℝ (k : ℝ → ℂ) x‖ ≤ C := by
    have h := hC x
    rwa [pow_zero, one_mul, norm_iteratedFDeriv_one] at h
  have hlip (x : ℝ) : ‖k x‖ ≤ C * |x| ^ 1 := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := (k : ℝ → ℂ))
      (s := univ) (fun y _ ↦ k.differentiableAt) (fun y _ ↦ hfd y) convex_univ
      (mem_univ (0 : ℝ)) (mem_univ x)
    rwa [hk0, sub_zero, sub_zero, Real.norm_eq_abs, ← pow_one |x|] at h
  have hkm : MemLp (k : ℝ → ℂ) 2 (realPWIntervalMeasure α s) :=
    memLp_realPWIntervalMeasure_of_evenSchwartz_order hα hs k hke 1
      (by push_cast; linarith) ⟨C, fun x _ ↦ hlip x⟩
  obtain ⟨f, hf⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y k hke hkb
    (volume_le_realPWIntervalMeasure α s hs) hkm
  obtain ⟨I, hI, hIc⟩ := exists_realPWBand_integralFunctional_of_integrable (Y := Y) hs hint
  refine ⟨f, by rw [congrFun hf 0, hk0], fun hmem ↦ ?_⟩
  have h1 := hIc f hmem
  rw [(hI f).2, hf, hki] at h1
  exact one_ne_zero h1

/-- Between widths one half and three halves there is a band vector that vanishes at the origin
and is not in the closure of the polar-free core. -/
theorem exists_realPWBand_notMem_closure_polarFreeCore (hα : 1 / 2 < α) (hα' : α < 3 / 2)
    (hs : 0 ≤ s) (hY : 0 < Y) :
    ∃ f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs),
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0 ∧
        f ∉ closure (realPWBandPolarFreeCore Y α hs) :=
  exists_realPWBand_notMem_closure_polarFreeCore_of_integrable (by linarith) hα' hs hY
    (integrable_inv_realPWIntervalWeight hα hs)

/-- At width one half, for `s > 1`, there is a band vector that vanishes at the origin and is not
in the closure of the polar-free core. -/
theorem exists_realPWBand_notMem_closure_polarFreeCore_half (hs : 0 ≤ s) (hs1 : 1 < s)
    (hY : 0 < Y) :
    ∃ f : RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs),
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) 0 f = 0 ∧
        f ∉ closure (realPWBandPolarFreeCore Y (1 / 2) hs) :=
  exists_realPWBand_notMem_closure_polarFreeCore_of_integrable (by norm_num) (by norm_num) hs hY
    (integrable_inv_realPWIntervalWeight_half hs1)

end AboveThreshold

section CriticalEndpoint

variable {Y α s : ℝ}

/-- A Schwartz function that vanishes at the origin is bounded by a multiple of `|x|`. -/
private theorem exists_schwartz_norm_le_mul_abs (ψ : 𝓢(ℝ, ℂ)) (h0 : ψ 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖ψ x‖ ≤ C * |x| := by
  obtain ⟨C, hCpos, hC⟩ := ψ.decay 0 1
  have hfd (x : ℝ) : ‖fderiv ℝ (ψ : ℝ → ℂ) x‖ ≤ C := by
    have h := hC x
    rwa [pow_zero, one_mul, norm_iteratedFDeriv_one] at h
  refine ⟨C, hCpos.le, fun x ↦ ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := (ψ : ℝ → ℂ))
    (s := univ) (fun y _ ↦ ψ.differentiableAt) (fun y _ ↦ hfd y) convex_univ
    (mem_univ (0 : ℝ)) (mem_univ x)
  rwa [h0, sub_zero, sub_zero, Real.norm_eq_abs] at h

/-- Below width three halves an even Schwartz function that vanishes at the origin is square
integrable for the weighted measure. -/
private theorem memLp_of_evenSchwartz_zero (hα : 0 ≤ α) (hα' : α < 3 / 2) (hs : 0 ≤ s)
    (ψ : 𝓢(ℝ, ℂ)) (he : Function.Even (ψ : ℝ → ℂ)) (h0 : ψ 0 = 0) :
    MemLp (ψ : ℝ → ℂ) 2 (realPWIntervalMeasure α s) := by
  obtain ⟨C, -, hC⟩ := exists_schwartz_norm_le_mul_abs ψ h0
  exact memLp_realPWIntervalMeasure_of_evenSchwartz_order hα hs ψ he 1 (by push_cast; linarith)
    ⟨C, fun x _ ↦ by simpa using hC x⟩

/-- The image of the weighted measure under a contraction by `t ≥ 1` is at most the dilation
constant times `t` times the measure. -/
theorem map_mul_realPWIntervalMeasure_le (hα : 0 ≤ α) (hs : 0 ≤ s) {t : ℝ}
    (ht : 1 ≤ t) :
    Measure.map (t⁻¹ * ·) (realPWIntervalMeasure α s) ≤
      (ENNReal.ofReal (Real.exp (2 * α * Real.log t) *
        (1 + Real.log t + Real.log t ^ 2) ^ (s / 2)) * ENNReal.ofReal t) •
          realPWIntervalMeasure α s := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  let a := t⁻¹
  have ha : 0 < a := inv_pos.mpr ht0
  let C := Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCa : Real.exp (2 * |α * Real.log a|) * (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2) =
      C := by
    have h1 : Real.log a = -Real.log t := Real.log_inv t
    rw [h1, mul_neg, abs_neg, abs_neg, neg_sq, abs_of_nonneg (mul_nonneg hα hlog),
      abs_of_nonneg hlog, ← mul_assoc]
  let W := fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x)
  have hW : Measurable W := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hmul : Measurable (a * ·) := measurable_const_mul a
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply hmul hS, smul_apply, realPWIntervalMeasure,
    withDensity_apply _ (hmul hS), withDensity_apply _ hS]
  change (∫⁻ x in (a * ·) ⁻¹' S, W x) ≤ (ENNReal.ofReal C * ENNReal.ofReal t) * ∫⁻ x in S, W x
  calc
    _ ≤ ∫⁻ x in (a * ·) ⁻¹' S, ENNReal.ofReal C * W (a * x) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (realPWIntervalWeight α s x) ≤
        ENNReal.ofReal C * ENNReal.ofReal (realPWIntervalWeight α s (a * x))
      rw [← ENNReal.ofReal_mul hC, ← hCa]
      exact ENNReal.ofReal_le_ofReal (realPWIntervalWeight_le_dilation hs ha x)
    _ = ENNReal.ofReal C * ∫⁻ y in S, W y ∂Measure.map (a * ·) volume := by
      rw [setLIntegral_map hS hW hmul]
      exact lintegral_const_mul _ (hW.comp hmul)
    _ = _ := by
      rw [Real.map_volume_mul_left ha.ne', setLIntegral_smul_measure, smul_eq_mul, ← mul_assoc,
        inv_inv, abs_of_pos ht0]

/-- A dilation by `t ≥ 1` of a nonnegative continuous integrable function is integrable for the
weighted measure, with integral at most the dilation constant times `t` times the integral. -/
private theorem integrable_dilate_le (hα : 0 ≤ α) (hs : 0 ≤ s) {t : ℝ} (ht : 1 ≤ t)
    (Φ : ℝ → ℝ) (hΦc : Continuous Φ) (hΦ0 : ∀ x, 0 ≤ Φ x)
    (hΦ : Integrable Φ (realPWIntervalMeasure α s)) :
    Integrable (fun x ↦ Φ (x * t⁻¹)) (realPWIntervalMeasure α s) ∧
      ∫ x, Φ (x * t⁻¹) ∂realPWIntervalMeasure α s ≤
        (Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2) * t) *
          ∫ x, Φ x ∂realPWIntervalMeasure α s := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  let C := Real.exp (2 * α * Real.log t) * (1 + Real.log t + Real.log t ^ 2) ^ (s / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let k := ENNReal.ofReal C * ENNReal.ofReal t
  have hmap : Measure.map (t⁻¹ * ·) (realPWIntervalMeasure α s) ≤ k • realPWIntervalMeasure α s :=
    map_mul_realPWIntervalMeasure_le hα hs ht
  have hk : k ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hkr : k.toReal = C * t := by
    dsimp [k]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal ht0.le]
  have hmul : Measurable (t⁻¹ * ·) := measurable_const_mul _
  have hImap : Integrable Φ (Measure.map (t⁻¹ * ·) (realPWIntervalMeasure α s)) :=
    (hΦ.smul_measure hk).mono_measure hmap
  have hcomp : Integrable (Φ ∘ (t⁻¹ * ·)) (realPWIntervalMeasure α s) :=
    (integrable_map_measure hΦc.aestronglyMeasurable hmul.aemeasurable).mp hImap
  have hfun : (fun x ↦ Φ (x * t⁻¹)) = Φ ∘ (t⁻¹ * ·) := funext fun x ↦ by
    simp only [Function.comp_apply, mul_comm]
  refine ⟨hfun ▸ hcomp, ?_⟩
  calc ∫ x, Φ (x * t⁻¹) ∂realPWIntervalMeasure α s
      = ∫ y, Φ y ∂Measure.map (t⁻¹ * ·) (realPWIntervalMeasure α s) := by
        rw [integral_map hmul.aemeasurable hΦc.aestronglyMeasurable]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [mul_comm]
    _ ≤ ∫ y, Φ y ∂(k • realPWIntervalMeasure α s) :=
        integral_mono_measure hmap (ae_of_all _ hΦ0) (hΦ.smul_measure hk)
    _ = _ := by
        rw [integral_smul_measure, hkr, smul_eq_mul]

/-- At width one half, for `s ≤ 1`, the weight is at most `y ^ 2` outside the unit interval. -/
private theorem realPWIntervalWeight_half_le_sq (hs1 : s ≤ 1) {y : ℝ} (hy : 1 ≤ |y|) :
    realPWIntervalWeight (1 / 2) s y ≤ y ^ 2 := by
  have ha : 0 < |y| := zero_lt_one.trans_le hy
  have hy0 : y ≠ 0 := abs_pos.mp ha
  rw [realPWIntervalWeight_eq (1 / 2) s hy0, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    Real.rpow_one, Real.rpow_neg_one]
  have hmax : max |y| |y|⁻¹ = |y| := max_eq_left ((inv_le_one_of_one_le₀ hy).trans hy)
  rw [hmax]
  have hL : 0 ≤ Real.log |y| := Real.log_nonneg hy
  have hlog : Real.log |y| ≤ |y| - 1 := Real.log_le_sub_one_of_pos ha
  have hbase : 1 ≤ 1 + Real.log |y| ^ 2 := by nlinarith [sq_nonneg (Real.log |y|)]
  have h1 : (1 + Real.log |y| ^ 2) ^ (s / 2) ≤ (1 + Real.log |y| ^ 2) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have h2 : (1 + Real.log |y| ^ 2) ^ ((1 : ℝ) / 2) ≤ |y| := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (1 + Real.log |y| ^ 2) ≤ Real.sqrt (|y| ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [mul_self_le_mul_self hL hlog])
      _ = |y| := Real.sqrt_sq ha.le
  calc |y| * (1 + Real.log |y| ^ 2) ^ (s / 2) ≤ |y| * |y| :=
        mul_le_mul_of_nonneg_left (h1.trans h2) ha.le
    _ = y ^ 2 := by rw [← sq, sq_abs]

/-- At width one half, for `s ≤ 1`, the function `|y| ‖k y‖` is integrable for the weighted
measure when the Schwartz function `k` is bounded by a multiple of `|y|`. -/
private theorem integrable_abs_mul_norm_half (hs : 0 ≤ s) (hs1 : s ≤ 1) (k : 𝓢(ℝ, ℂ))
    {C₁ : ℝ} (hC₁ : ∀ x, ‖k x‖ ≤ C₁ * |x|) :
    Integrable (fun y ↦ |y| * ‖k y‖) (realPWIntervalMeasure (1 / 2) s) := by
  let w := realPWIntervalWeight (1 / 2) s
  have hw0 (y : ℝ) : 0 ≤ w y := zero_le_one.trans (one_le_realPWIntervalWeight (1 / 2) s hs y)
  have hwm : Measurable w := measurable_realPWIntervalWeight (1 / 2) s
  rw [realPWIntervalMeasure, integrable_withDensity_iff_integrable_smul' hwm.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hI1 : IntegrableOn (fun y : ℝ ↦ |y| ^ (2 : ℝ) * w y) (Icc (-1) 1) :=
    integrableOn_abs_rpow_mul_realPWIntervalWeight (by norm_num) hs (by norm_num)
  have hI2 : Integrable (fun y : ℝ ↦ ‖y‖ ^ 3 * ‖k y‖) := k.integrable_pow_mul volume 3
  have hdom : Integrable (fun y : ℝ ↦
      C₁ * (Icc (-1 : ℝ) 1).indicator (fun y ↦ |y| ^ (2 : ℝ) * w y) y + ‖y‖ ^ 3 * ‖k y‖) :=
    (((integrable_indicator_iff measurableSet_Icc).mpr hI1).const_mul C₁).add hI2
  have hmeas : Measurable fun y : ℝ ↦ (ENNReal.ofReal (w y)).toReal • (|y| * ‖k y‖) :=
    hwm.ennreal_ofReal.ennreal_toReal.smul
      (continuous_abs.measurable.mul k.continuous.norm.measurable)
  refine hdom.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
  have hnn : 0 ≤ w y * (|y| * ‖k y‖) :=
    mul_nonneg (hw0 y) (mul_nonneg (abs_nonneg y) (norm_nonneg _))
  rw [ENNReal.toReal_ofReal (hw0 y), smul_eq_mul, Real.norm_of_nonneg hnn]
  have h3nn : 0 ≤ ‖y‖ ^ 3 * ‖k y‖ := by positivity
  by_cases hy : |y| ≤ 1
  · rw [indicator_of_mem (show y ∈ Icc (-1 : ℝ) 1 from abs_le.mp hy), Real.rpow_two]
    have h1 : w y * (|y| * ‖k y‖) ≤ w y * (|y| * (C₁ * |y|)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC₁ y) (abs_nonneg y)) (hw0 y)
    have h2 : w y * (|y| * (C₁ * |y|)) = C₁ * (|y| ^ 2 * w y) := by ring
    linarith
  · have hy1 : 1 ≤ |y| := (not_le.mp hy).le
    have hmem : y ∉ Icc (-1 : ℝ) 1 := fun h ↦ hy (abs_le.mpr h)
    rw [indicator_of_notMem hmem, mul_zero, zero_add]
    have hw2 : w y ≤ y ^ 2 := realPWIntervalWeight_half_le_sq hs1 hy1
    calc w y * (|y| * ‖k y‖) ≤ y ^ 2 * (|y| * ‖k y‖) :=
          mul_le_mul_of_nonneg_right hw2 (mul_nonneg (abs_nonneg y) (norm_nonneg _))
      _ = ‖y‖ ^ 3 * ‖k y‖ := by
          rw [Real.norm_eq_abs, ← sq_abs y]
          ring

/-- The value of a finite sum of Schwartz functions at a point. -/
private theorem schwartz_sum_apply {ι : Type*} (S : Finset ι) (ψ : ι → 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∑ n ∈ S, ψ n) x = ∑ n ∈ S, ψ n x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- The square of a finite sum, written with the partial sums of the earlier terms. -/
private theorem sq_sum_range_eq (v : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, v n) ^ 2 =
      ∑ n ∈ Finset.range N, (v n ^ 2 + 2 * v n * ∑ m ∈ Finset.range n, v m) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    ring

private theorem sum_four_pow_le (n : ℕ) : ∑ m ∈ Finset.range n, (4 : ℝ) ^ m ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n]

/-- The logarithmic factor of the dilation by `2 ^ n` is at most `n + 1` when `s ≤ 1`. -/
private theorem dilationLogFactor_le (hs1 : s ≤ 1) (n : ℕ) :
    (1 + Real.log ((2 : ℝ) ^ n) + Real.log ((2 : ℝ) ^ n) ^ 2) ^ (s / 2) ≤ n + 1 := by
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.log_pow]
  have hℓ0 : 0 ≤ (n : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg n) hl0
  have hℓn : (n : ℝ) * Real.log 2 ≤ n := by
    have := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have hbase : 1 ≤ 1 + (n : ℝ) * Real.log 2 + ((n : ℝ) * Real.log 2) ^ 2 := by nlinarith
  calc (1 + (n : ℝ) * Real.log 2 + ((n : ℝ) * Real.log 2) ^ 2) ^ (s / 2)
      ≤ (1 + (n : ℝ) * Real.log 2 + ((n : ℝ) * Real.log 2) ^ 2) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    _ = Real.sqrt (1 + (n : ℝ) * Real.log 2 + ((n : ℝ) * Real.log 2) ^ 2) :=
        (Real.sqrt_eq_rpow _).symm
    _ ≤ Real.sqrt ((1 + (n : ℝ) * Real.log 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 + (n : ℝ) * Real.log 2 := Real.sqrt_sq (by linarith)
    _ ≤ n + 1 := by linarith

/-- At width one half, for `s ≤ 1`, there are even Schwartz functions of the band that vanish
at the origin, have integral one, and have arbitrarily small weighted norm: the sum of the
dilates by `2 ^ n` of one such function, with weights proportional to `1 / (n + 1)`. -/
private theorem exists_small_unit_integral_half (hs : 0 ≤ s) (hs1 : s ≤ 1) (hY : 0 < Y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : 𝓢(ℝ, ℂ), Function.Even (κ : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 κ) ξ = 0) ∧ κ 0 = 0 ∧
      ∫ x, κ x = 1 ∧ MemLp (κ : ℝ → ℂ) 2 (realPWIntervalMeasure (1 / 2) s) ∧
      ∫ x, ‖κ x‖ ^ 2 ∂realPWIntervalMeasure (1 / 2) s < ε := by
  classical
  let μ := realPWIntervalMeasure (1 / 2) s
  have hα : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hα' : (1 / 2 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨k, hke, hkb, hk0, hki⟩ := exists_evenSchwartz_band_zero_integral_one hY
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_schwartz_norm_le_mul_abs k hk0
  have hkm : MemLp (k : ℝ → ℂ) 2 μ := memLp_of_evenSchwartz_zero hα hα' hs k hke hk0
  have hk2 : Integrable (fun x ↦ ‖k x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm k.continuous.aestronglyMeasurable).mp hkm
  have hk2c : Continuous fun y : ℝ ↦ ‖k y‖ ^ 2 := k.continuous.norm.pow 2
  let Φ : ℝ → ℝ := fun y ↦ |y| * ‖k y‖
  have hΦc : Continuous Φ := continuous_abs.mul k.continuous.norm
  have hΦ0 : ∀ y, 0 ≤ Φ y := fun y ↦ mul_nonneg (abs_nonneg y) (norm_nonneg _)
  have hΦi : Integrable Φ μ := integrable_abs_mul_norm_half hs hs1 k hC₁
  let A₀ : ℝ := ∫ x, ‖k x‖ ^ 2 ∂μ
  let I₁ : ℝ := ∫ y, Φ y ∂μ
  have hA₀ : 0 ≤ A₀ := integral_nonneg fun _ ↦ sq_nonneg _
  have hI₁ : 0 ≤ I₁ := integral_nonneg hΦ0
  let K : ℝ := A₀ + 2 * C₁ * I₁
  have hK : 0 ≤ K := add_nonneg hA₀ (mul_nonneg (mul_nonneg (by norm_num) hC₁0) hI₁)
  obtain ⟨N, hN⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
    (eventually_gt_atTop (K / ε))).exists
  let H : ℝ := ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)
  have hNH : K / ε < H := hN
  have hH : 0 < H := lt_of_le_of_lt (div_nonneg hK hε.le) hNH
  have hKH : K / H < ε := by
    rw [div_lt_iff₀ hH]
    rw [div_lt_iff₀ hε] at hNH
    linarith [mul_comm ε H]
  let t : ℕ → ℝ := fun n ↦ 2 ^ n
  have ht1 (n : ℕ) : 1 ≤ t n := one_le_pow₀ (by norm_num)
  have ht0 (n : ℕ) : 0 < t n := zero_lt_one.trans_le (ht1 n)
  have ht2 (n : ℕ) : t n ^ 2 = 4 ^ n := by
    change ((2 : ℝ) ^ n) ^ 2 = 4 ^ n
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  let a : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) / H
  have hn1 (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha0 (n : ℕ) : 0 ≤ a n := div_nonneg (div_nonneg zero_le_one (hn1 n).le) hH.le
  have haH (n : ℕ) : a n * ((n : ℝ) + 1) = 1 / H := by
    change 1 / ((n : ℝ) + 1) / H * ((n : ℝ) + 1) = 1 / H
    have := (hn1 n).ne'
    field_simp
  have hasum : ∑ n ∈ Finset.range N, a n = 1 := by
    change ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) / H = 1
    rw [← Finset.sum_div]
    exact div_self hH.ne'
  let κ : ℕ → 𝓢(ℝ, ℂ) := fun n ↦ ((t n)⁻¹ : ℂ) • schwartzDilate (t n) (ht0 n).ne' k
  have hκx (n : ℕ) (x : ℝ) : κ n x = ((t n)⁻¹ : ℂ) * k (x * (t n)⁻¹) := rfl
  let F : 𝓢(ℝ, ℂ) := ∑ n ∈ Finset.range N, (a n : ℂ) • κ n
  have hFx (x : ℝ) : F x = ∑ n ∈ Finset.range N, (a n : ℂ) * κ n x := by
    change (∑ n ∈ Finset.range N, (a n : ℂ) • κ n) x = _
    rw [schwartz_sum_apply]
    rfl
  have hFe : Function.Even (F : ℝ → ℂ) := fun x ↦ by
    rw [hFx, hFx]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [hκx, hκx, neg_mul, hke]
  have hF0 : F 0 = 0 := by
    rw [hFx]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    rw [hκx, zero_mul, hk0, mul_zero, mul_zero]
  have hFb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 F) ξ = 0 := by
    refine Finset.sum_induction (fun n ↦ (a n : ℂ) • κ n)
      (fun ψ : 𝓢(ℝ, ℂ) ↦ ∀ ξ ∉ Icc (-Y) Y, (𝓕 ψ) ξ = 0) ?_ ?_ ?_
    · intro ψ₁ ψ₂ h1 h2 ξ hξ
      rw [FourierTransform.fourier_add, add_apply, h1 ξ hξ, h2 ξ hξ, add_zero]
    · intro ξ hξ
      have h0 : (0 : 𝓢(ℝ, ℂ)) = (0 : ℂ) • k := (zero_smul ℂ k).symm
      rw [h0, FourierTransform.fourier_smul, zero_smul]
      rfl
    · intro n _ ξ hξ
      change (𝓕 ((a n : ℂ) • (((t n)⁻¹ : ℂ) • schwartzDilate (t n) (ht0 n).ne' k))) ξ = 0
      rw [FourierTransform.fourier_smul, smul_apply, FourierTransform.fourier_smul, smul_apply,
        schwartzDilate_band (ht1 n) hY.le k hkb ξ hξ, smul_zero, smul_zero]
  have hκi (n : ℕ) : ∫ x, κ n x = 1 := by
    have h1 : ∫ x, κ n x = ((t n)⁻¹ : ℂ) * ∫ x, schwartzDilate (t n) (ht0 n).ne' k x :=
      integral_const_mul _ _
    rw [h1, integral_schwartzDilate (ht0 n), hki, Complex.real_smul, mul_one,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ (ht0 n).ne',
      Complex.ofReal_one]
  have hFi : ∫ x, F x = 1 := by
    have h1 : ∫ x, F x = ∑ n ∈ Finset.range N, (a n : ℂ) * ∫ x, κ n x := by
      simp only [hFx]
      rw [integral_finsetSum _ fun n _ ↦ (κ n).integrable.const_mul _]
      exact Finset.sum_congr rfl fun n _ ↦ integral_const_mul _ _
    rw [h1]
    simp only [hκi, mul_one]
    rw [← Complex.ofReal_sum, hasum, Complex.ofReal_one]
  have hFm : MemLp (F : ℝ → ℂ) 2 μ := memLp_of_evenSchwartz_zero hα hα' hs F hFe hF0
  let u : ℕ → ℝ → ℝ := fun n x ↦ (t n)⁻¹ * ‖k (x * (t n)⁻¹)‖
  have hκn (n : ℕ) (x : ℝ) : ‖κ n x‖ = u n x := by
    rw [hκx, norm_mul, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (ht0 n).le)]
  have hu0 (n : ℕ) (x : ℝ) : 0 ≤ u n x :=
    mul_nonneg (inv_nonneg.mpr (ht0 n).le) (norm_nonneg _)
  have huL (n : ℕ) (x : ℝ) : u n x ≤ C₁ * |x| * ((t n)⁻¹) ^ 2 := by
    have h := hC₁ (x * (t n)⁻¹)
    rw [abs_mul, abs_of_pos (inv_pos.mpr (ht0 n))] at h
    calc u n x ≤ (t n)⁻¹ * (C₁ * (|x| * (t n)⁻¹)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (ht0 n).le)
      _ = C₁ * |x| * ((t n)⁻¹) ^ 2 := by ring
  have hΦu (m : ℕ) (x : ℝ) : |x| * u m x = Φ (x * (t m)⁻¹) := by
    change |x| * ((t m)⁻¹ * ‖k (x * (t m)⁻¹)‖) = |x * (t m)⁻¹| * ‖k (x * (t m)⁻¹)‖
    rw [abs_mul, abs_of_pos (inv_pos.mpr (ht0 m))]
    ring
  let T : ℕ → ℝ → ℝ := fun n x ↦ a n ^ 2 * u n x ^ 2 +
    2 * (a n * C₁ * ((t n)⁻¹) ^ 2) * ∑ m ∈ Finset.range n, a m * Φ (x * (t m)⁻¹)
  have hpt (x : ℝ) : ‖F x‖ ^ 2 ≤ ∑ n ∈ Finset.range N, T n x := by
    have h1 : ‖F x‖ ≤ ∑ n ∈ Finset.range N, a n * u n x := by
      rw [hFx]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha0 n), hκn]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [sq_sum_range_eq] at h2
    refine h2.trans (Finset.sum_le_sum fun n _ ↦ ?_)
    have h3 : (a n * u n x) * ∑ m ∈ Finset.range n, a m * u m x ≤
        (a n * C₁ * ((t n)⁻¹) ^ 2) * ∑ m ∈ Finset.range n, a m * Φ (x * (t m)⁻¹) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun m _ ↦ ?_
      rw [← hΦu m x]
      have h4 : a n * u n x ≤ a n * (C₁ * |x| * ((t n)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left (huL n x) (ha0 n)
      calc a n * u n x * (a m * u m x)
          ≤ a n * (C₁ * |x| * ((t n)⁻¹) ^ 2) * (a m * u m x) :=
            mul_le_mul_of_nonneg_right h4 (mul_nonneg (ha0 m) (hu0 m x))
        _ = a n * C₁ * ((t n)⁻¹) ^ 2 * (a m * (|x| * u m x)) := by ring
    change (a n * u n x) ^ 2 + 2 * (a n * u n x) * ∑ m ∈ Finset.range n, a m * u m x ≤
      a n ^ 2 * u n x ^ 2 +
        2 * (a n * C₁ * ((t n)⁻¹) ^ 2) * ∑ m ∈ Finset.range n, a m * Φ (x * (t m)⁻¹)
    rw [mul_pow]
    linarith
  have hexp (n : ℕ) : Real.exp (2 * (1 / 2) * Real.log (t n)) = t n := by
    rw [show (2 : ℝ) * (1 / 2) * Real.log (t n) = Real.log (t n) by ring, Real.exp_log (ht0 n)]
  have hD (n : ℕ) : (1 + Real.log (t n) + Real.log (t n) ^ 2) ^ (s / 2) ≤ (n : ℝ) + 1 :=
    dilationLogFactor_le hs1 n
  have hDnn (n : ℕ) : 0 ≤ (1 + Real.log (t n) + Real.log (t n) ^ 2) ^ (s / 2) := by
    have := Real.log_nonneg (ht1 n)
    positivity
  have hu2 (n : ℕ) : Integrable (fun x ↦ u n x ^ 2) μ ∧
      ∫ x, u n x ^ 2 ∂μ ≤ ((n : ℝ) + 1) * A₀ := by
    obtain ⟨hi, hle⟩ := integrable_dilate_le hα hs (ht1 n) (fun y ↦ ‖k y‖ ^ 2) hk2c
      (fun _ ↦ sq_nonneg _) hk2
    have hfun : (fun x ↦ u n x ^ 2) = fun x ↦ ((t n)⁻¹) ^ 2 * ‖k (x * (t n)⁻¹)‖ ^ 2 :=
      funext fun x ↦ mul_pow _ _ 2
    rw [hfun]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul]
    rw [hexp n] at hle
    have ht := (ht0 n).ne'
    calc ((t n)⁻¹) ^ 2 * ∫ x, ‖k (x * (t n)⁻¹)‖ ^ 2 ∂μ
        ≤ ((t n)⁻¹) ^ 2 * (t n * (1 + Real.log (t n) + Real.log (t n) ^ 2) ^ (s / 2) * t n * A₀) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = (1 + Real.log (t n) + Real.log (t n) ^ 2) ^ (s / 2) * A₀ := by
          field_simp
      _ ≤ ((n : ℝ) + 1) * A₀ := mul_le_mul_of_nonneg_right (hD n) hA₀
  have hΦm (m : ℕ) : Integrable (fun x ↦ Φ (x * (t m)⁻¹)) μ ∧
      ∫ x, Φ (x * (t m)⁻¹) ∂μ ≤ t m ^ 2 * (((m : ℝ) + 1) * I₁) := by
    obtain ⟨hi, hle⟩ := integrable_dilate_le hα hs (ht1 m) Φ hΦc hΦ0 hΦi
    refine ⟨hi, hle.trans ?_⟩
    rw [hexp m]
    calc t m * (1 + Real.log (t m) + Real.log (t m) ^ 2) ^ (s / 2) * t m * I₁
        = t m ^ 2 * ((1 + Real.log (t m) + Real.log (t m) ^ 2) ^ (s / 2) * I₁) := by ring
      _ ≤ t m ^ 2 * (((m : ℝ) + 1) * I₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hD m) hI₁) (sq_nonneg _)
  have hSi (n : ℕ) : Integrable (fun x ↦ ∑ m ∈ Finset.range n, a m * Φ (x * (t m)⁻¹)) μ :=
    integrable_finsetSum _ fun m _ ↦ (hΦm m).1.const_mul _
  have hTi (n : ℕ) : Integrable (T n) μ :=
    ((hu2 n).1.const_mul _).add ((hSi n).const_mul _)
  have hTb (n : ℕ) : ∫ x, T n x ∂μ ≤ a n * (K / H) := by
    have hsplit : ∫ x, T n x ∂μ = a n ^ 2 * ∫ x, u n x ^ 2 ∂μ +
        2 * (a n * C₁ * ((t n)⁻¹) ^ 2) *
          ∑ m ∈ Finset.range n, a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ := by
      change ∫ x, (a n ^ 2 * u n x ^ 2 +
        2 * (a n * C₁ * ((t n)⁻¹) ^ 2) * ∑ m ∈ Finset.range n, a m * Φ (x * (t m)⁻¹)) ∂μ = _
      rw [integral_add ((hu2 n).1.const_mul _) ((hSi n).const_mul _), integral_const_mul,
        integral_const_mul, integral_finsetSum _ fun m _ ↦ (hΦm m).1.const_mul _]
      congr 2
      exact Finset.sum_congr rfl fun m _ ↦ integral_const_mul _ _
    rw [hsplit]
    have hfirst : a n ^ 2 * ∫ x, u n x ^ 2 ∂μ ≤ a n * (A₀ / H) := by
      calc a n ^ 2 * ∫ x, u n x ^ 2 ∂μ ≤ a n ^ 2 * (((n : ℝ) + 1) * A₀) :=
            mul_le_mul_of_nonneg_left (hu2 n).2 (sq_nonneg _)
        _ = a n * (a n * ((n : ℝ) + 1)) * A₀ := by ring
        _ = a n * (A₀ / H) := by rw [haH]; ring
    have hsum : ∑ m ∈ Finset.range n, a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ ≤ I₁ / H * t n ^ 2 := by
      calc ∑ m ∈ Finset.range n, a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ
          ≤ ∑ m ∈ Finset.range n, I₁ / H * (4 : ℝ) ^ m := Finset.sum_le_sum fun m _ ↦ by
            calc a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ ≤ a m * (t m ^ 2 * (((m : ℝ) + 1) * I₁)) :=
                  mul_le_mul_of_nonneg_left (hΦm m).2 (ha0 m)
              _ = a m * ((m : ℝ) + 1) * I₁ * t m ^ 2 := by ring
              _ = I₁ / H * 4 ^ m := by rw [haH, ht2]; ring
        _ = I₁ / H * ∑ m ∈ Finset.range n, (4 : ℝ) ^ m := (Finset.mul_sum _ _ _).symm
        _ ≤ I₁ / H * 4 ^ n :=
            mul_le_mul_of_nonneg_left (sum_four_pow_le n) (div_nonneg hI₁ hH.le)
        _ = I₁ / H * t n ^ 2 := by rw [ht2]
    have hcoef : 0 ≤ 2 * (a n * C₁ * ((t n)⁻¹) ^ 2) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (ha0 n) hC₁0) (sq_nonneg _))
    have hsecond : 2 * (a n * C₁ * ((t n)⁻¹) ^ 2) *
        ∑ m ∈ Finset.range n, a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ ≤ a n * (2 * C₁ * I₁ / H) := by
      have ht := (ht0 n).ne'
      calc 2 * (a n * C₁ * ((t n)⁻¹) ^ 2) * ∑ m ∈ Finset.range n, a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ
          ≤ 2 * (a n * C₁ * ((t n)⁻¹) ^ 2) * (I₁ / H * t n ^ 2) :=
            mul_le_mul_of_nonneg_left hsum hcoef
        _ = a n * (2 * C₁ * I₁ / H) := by
            field_simp
    calc a n ^ 2 * ∫ x, u n x ^ 2 ∂μ + 2 * (a n * C₁ * ((t n)⁻¹) ^ 2) *
          ∑ m ∈ Finset.range n, a m * ∫ x, Φ (x * (t m)⁻¹) ∂μ
        ≤ a n * (A₀ / H) + a n * (2 * C₁ * I₁ / H) := add_le_add hfirst hsecond
      _ = a n * (K / H) := by
          change _ = a n * ((A₀ + 2 * C₁ * I₁) / H)
          ring
  have hfinal : ∫ x, ‖F x‖ ^ 2 ∂μ ≤ K / H := by
    calc ∫ x, ‖F x‖ ^ 2 ∂μ ≤ ∫ x, ∑ n ∈ Finset.range N, T n x ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)
            (integrable_finsetSum _ fun n _ ↦ hTi n) (ae_of_all _ hpt)
      _ = ∑ n ∈ Finset.range N, ∫ x, T n x ∂μ := integral_finsetSum _ fun n _ ↦ hTi n
      _ ≤ ∑ n ∈ Finset.range N, a n * (K / H) := Finset.sum_le_sum fun n _ ↦ hTb n
      _ = K / H := by rw [← Finset.sum_mul, hasum, one_mul]
  exact ⟨F, hFe, hFb, hF0, hFi, hFm, hfinal.trans_lt hKH⟩

/-- If the band contains even Schwartz functions vanishing at the origin, with integral one and
arbitrarily small norm, then the closure of the polar-free core contains every band vector
given by an even Schwartz function of the band that vanishes at the origin. -/
private theorem mem_closure_polarFreeCore_of_small (hs : 0 ≤ s)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ κ : 𝓢(ℝ, ℂ), Function.Even (κ : ℝ → ℂ) ∧
      (∀ ξ ∉ Icc (-Y) Y, (𝓕 κ) ξ = 0) ∧ κ 0 = 0 ∧ ∫ x, κ x = 1 ∧
      MemLp (κ : ℝ → ℂ) 2 (realPWIntervalMeasure α s) ∧
      ∫ x, ‖κ x‖ ^ 2 ∂realPWIntervalMeasure α s < ε)
    (g : 𝓢(ℝ, ℂ)) (he : Function.Even (g : ℝ → ℂ))
    (hb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) (h0 : g 0 = 0)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs))
    (hf : (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) =
      (g : ℝ → ℂ)) :
    f ∈ closure (realPWBandPolarFreeCore Y α hs) := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let μ := realPWIntervalMeasure α s
  have hgm : MemLp (g : ℝ → ℂ) 2 μ := by
    have hae := RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) f
    rw [hf] at hae
    exact (Lp.memLp (f.val : Lp ℂ 2 μ)).ae_eq hae.symm
  let c : ℂ := ∫ x, g x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hden : 0 < ‖c‖ ^ 2 + 1 := by positivity
  obtain ⟨κ, hκe, hκb, hκ0, hκi, hκm, hκs⟩ := hsmall (ε ^ 2 / (‖c‖ ^ 2 + 1))
    (div_pos (sq_pos_of_pos hε) hden)
  let gt : 𝓢(ℝ, ℂ) := g - c • κ
  have hgtx (x : ℝ) : gt x = g x - c * κ x := rfl
  have hgte : Function.Even (gt : ℝ → ℂ) := fun x ↦ by
    rw [hgtx, hgtx, he x, hκe x]
  have hgtb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 gt) ξ = 0 := fun ξ hξ ↦ by
    change (𝓕 (g - c • κ)) ξ = 0
    rw [FourierTransform.fourier_sub, sub_apply, FourierTransform.fourier_smul, smul_apply,
      hb ξ hξ, hκb ξ hξ, smul_zero, sub_zero]
  have hgt0 : gt 0 = 0 := by rw [hgtx, h0, hκ0, mul_zero, sub_zero]
  have hgti : ∫ x, gt x = 0 := by
    have h1 : ∫ x, gt x = (∫ x, g x) - c * ∫ x, κ x := by
      have h2 : Integrable (fun x ↦ c * κ x) := κ.integrable.const_mul c
      rw [← integral_const_mul, ← integral_sub g.integrable h2]
      rfl
    rw [h1, hκi, mul_one, sub_self]
  have hgtm : MemLp (gt : ℝ → ℂ) 2 μ := hgm.sub (hκm.const_smul c)
  obtain ⟨ft, hft⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y gt hgte hgtb hμ hgtm
  refine ⟨ft, ⟨gt, hgte, hgtb, hgt0, hgti, hft⟩, ?_⟩
  have hdiff : (fun x ↦ RealPWBand.evaluation Y hμ x (f - ft)) = fun x ↦ c * κ x := by
    funext x
    rw [map_sub, congrFun hf x, congrFun hft x, hgtx, sub_sub_cancel]
  have hnorm := norm_sq_realPWBand_of_evaluation_eq hs (f - ft) _ hdiff
  have hpt (x : ℝ) : ‖c * κ x‖ ^ 2 = ‖c‖ ^ 2 * ‖κ x‖ ^ 2 := by rw [norm_mul, mul_pow]
  have hlt : ‖f - ft‖ ^ 2 < ε ^ 2 := by
    rw [hnorm]
    simp only [hpt]
    rw [integral_const_mul]
    have hI0 : 0 ≤ ∫ x, ‖κ x‖ ^ 2 ∂realPWIntervalMeasure α s :=
      integral_nonneg fun _ ↦ sq_nonneg _
    calc ‖c‖ ^ 2 * ∫ x, ‖κ x‖ ^ 2 ∂realPWIntervalMeasure α s
        ≤ ‖c‖ ^ 2 * (ε ^ 2 / (‖c‖ ^ 2 + 1)) := mul_le_mul_of_nonneg_left hκs.le (sq_nonneg _)
      _ < ε ^ 2 := by
          rw [← mul_div_assoc, div_lt_iff₀ hden]
          nlinarith [sq_pos_of_pos hε, sq_nonneg ‖c‖]
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30). At width one half with `s ≤ 1`, the closure of
the polar-free core contains every band vector that is represented by an even Schwartz function
with Fourier transform in the band and vanishing at the origin, whatever its integral. As below
width one half, the condition that the integral vanishes does not survive the closure.
Reconstruction: The paper does not state this. -/
theorem mem_closure_realPWBandPolarFreeCore_of_schwartz_half (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hY : 0 < Y) (g : 𝓢(ℝ, ℂ)) (he : Function.Even (g : ℝ → ℂ))
    (hb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) (h0 : g 0 = 0)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs))
    (hf : (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) x f) =
      (g : ℝ → ℂ)) :
    f ∈ closure (realPWBandPolarFreeCore Y (1 / 2) hs) :=
  mem_closure_polarFreeCore_of_small hs
    (fun _ hε ↦ exists_small_unit_integral_half hs hs1 hY hε) g he hb h0 f hf

/-- At width one half with `s ≤ 1` the closure of the polar-free core contains a band vector,
represented by an even Schwartz function vanishing at the origin, whose integral is not zero. -/
theorem exists_mem_closure_realPWBandPolarFreeCore_integral_ne_zero_half (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (hY : 0 < Y) :
    ∃ (g : 𝓢(ℝ, ℂ)) (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs)),
      f ∈ closure (realPWBandPolarFreeCore Y (1 / 2) hs) ∧
      (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) x f) =
        (g : ℝ → ℂ) ∧ g 0 = 0 ∧ ∫ x, g x ≠ 0 := by
  obtain ⟨k, hke, hkb, hk0, hki⟩ := exists_evenSchwartz_band_zero_integral_one hY
  have hkm : MemLp (k : ℝ → ℂ) 2 (realPWIntervalMeasure (1 / 2) s) :=
    memLp_of_evenSchwartz_zero (by norm_num) (by norm_num) hs k hke hk0
  obtain ⟨f, hf⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y k hke hkb
    (volume_le_realPWIntervalMeasure (1 / 2) s hs) hkm
  exact ⟨k, f, mem_closure_realPWBandPolarFreeCore_of_schwartz_half hs hs1 hY k hke hkb hk0 f hf,
    hf, hk0, by rw [hki]; exact one_ne_zero⟩

end CriticalEndpoint

end RiemannMasullo.Isolated
