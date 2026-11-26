module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWJetTrials
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
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
* Above width one half the condition survives. The reciprocal of the weight is integrable
  (`integrable_inv_realPWIntervalWeight`), so the integral is a continuous linear functional on
  the band and vanishes on the closure (`exists_realPWBand_integralFunctional`). Between one
  half and three halves it is a condition of its own
  (`exists_realPWBand_notMem_closure_polarFreeCore`).

Reconstruction: The paper does not state this. The core is that of the order-zero model of the
rational real place.

Not treated here: the width `α = 1 / 2` itself, where the answer depends on `s`. That the
closure below one half is exactly the kernel of evaluation at the origin, which needs the
density of Schwartz functions in that kernel. The last statement for `α ≥ 3 / 2`. -/

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
def realPWBandPolarFreeCore (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Set (RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :=
  {f | ∃ g : 𝓢(ℝ, ℂ), Function.Even (g : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧ g 0 = 0 ∧
    ∫ x, g x = 0 ∧
    (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) = (g : ℝ → ℂ)}

/-- The squared norm of a band vector is the weighted integral of its pointwise values. -/
private theorem norm_sq_realPWBand_of_evaluation_eq (hs : 0 ≤ s)
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

/-- Above width one half the reciprocal of the weight is a vector of the weighted space. -/
private theorem memLp_inv_realPWIntervalWeight (hα : 1 / 2 < α) (hs : 0 ≤ s) :
    MemLp (fun x ↦ (((realPWIntervalWeight α s x)⁻¹ : ℝ) : ℂ)) 2 (realPWIntervalMeasure α s) := by
  have hmeas : Measurable fun x ↦ (((realPWIntervalWeight α s x)⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_realPWIntervalWeight α s).inv
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable, realPWIntervalMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_realPWIntervalWeight α s).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine (integrable_inv_realPWIntervalWeight hα hs).congr (ae_of_all _ fun x ↦ ?_)
  have hw : 0 < realPWIntervalWeight α s x :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  change (realPWIntervalWeight α s x)⁻¹ = (ENNReal.ofReal (realPWIntervalWeight α s x)).toReal •
    ‖(((realPWIntervalWeight α s x)⁻¹ : ℝ) : ℂ)‖ ^ 2
  rw [ENNReal.toReal_ofReal hw.le, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hw.le),
    smul_eq_mul]
  field_simp

/-- Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30). Above width one half every band vector is
integrable, the integral is a continuous linear functional on the band, and it vanishes on the
closure of the polar-free core. The condition that the integral vanishes survives the closure.
Reconstruction: The paper does not state this. -/
theorem exists_realPWBand_integralFunctional (hα : 1 / 2 < α) (hs : 0 ≤ s) :
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
  have hV := memLp_inv_realPWIntervalWeight hα hs
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

/-- Between widths one half and three halves there is a band vector that vanishes at the origin
and is not in the closure of the polar-free core: the vanishing of the integral is a
condition of its own. -/
theorem exists_realPWBand_notMem_closure_polarFreeCore (hα : 1 / 2 < α) (hα' : α < 3 / 2)
    (hs : 0 ≤ s) (hY : 0 < Y) :
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
    memLp_realPWIntervalMeasure_of_evenSchwartz_order (by linarith) hs k hke 1
      (by push_cast; linarith) ⟨C, fun x _ ↦ hlip x⟩
  obtain ⟨f, hf⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y k hke hkb
    (volume_le_realPWIntervalMeasure α s hs) hkm
  obtain ⟨I, hI, hIc⟩ := exists_realPWBand_integralFunctional (Y := Y) hα hs
  refine ⟨f, by rw [congrFun hf 0, hk0], fun hmem ↦ ?_⟩
  have h1 := hIc f hmem
  rw [(hI f).2, hf, hki] at h1
  exact one_ne_zero h1

end AboveThreshold

end RiemannMasullo.Isolated
