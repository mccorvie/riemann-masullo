module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWProjectionConcentration
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Function.LocalL2Convergence

/-! # Off-diagonal decay of the real-place sharp density, uniformly in the dilation

`Sec4_RealPWProjectionConcentration` proves that the sharp density of the rational real-place
cutoff dilation decays at both ends of the line, for one dilation `g > 1` at a time
(`realPWSharpDensity_decay`). This file proves the same decay with one radius for all `g` in a
compact interval `[a, b]` with `1 < a` (`realPWSharpDensity_decay_uniform`).

Nothing new enters the estimate. The concentration of the normalized evaluation vectors in two
windows around `x` and `-x` (`realPWIntervalBand_twoWindowConcentration`) does not involve the
dilation. The contracted point `g⁻¹ x` is at distance at least `(1 - a⁻¹) x` from `x`, and the
constants that compare the weight at `x` and at `g⁻¹ x` are bounded on the interval. So
`tendsto_weighted_eval_zero_of_twoWindows` of `ForMathlib/MeasureTheory/Function/LocalL2Convergence`
applies along the product of the filter at infinity in `x` with the principal filter of the
interval, and a limit along that product filter is a limit that is uniform on the interval.

The uniform decay is the estimate needed to pass from the sharp trace at one dilation
(`exists_realPWIntervalBand_sharpTrace_limit`) to its average against a test function of the
dilation, which is not done here. -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology SchwartzMap FourierTransform

namespace RiemannMasullo.Isolated

/-- The normalized evaluation vector has weighted square integral at most one. This is a copy
of the private lemma `realPWNormalizedEval_sq` of `Sec4_RealPWSharpCutoff`. -/
private theorem realPWNormalizedEval_sq_copy (Y α s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    Integrable (fun t ↦ realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) ∧
      (∫ t, realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) ≤ 1 := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ x
  let z := ((‖e‖⁻¹ : ℝ) : ℂ) • e
  let μ := realPWIntervalMeasure α s
  have hzNorm : ‖z‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg e))]
    exact inv_mul_le_one
  have hEval := RealPWBand.evaluation_ae Y hμ
    (realPWIntervalMeasure_absolutelyContinuous α s) z
  have hSq : (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) =ᵐ[μ]
      (fun t ↦ ‖z.val t‖ ^ 2) :=
    hEval.mono fun _ h ↦ congrArg (fun v : ℂ ↦ ‖v‖ ^ 2) h
  have hInt : Integrable (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) μ :=
    ((Lp.memLp z.val).integrable_norm_pow (by norm_num)).congr hSq.symm
  let ρ (t : ℝ) := ENNReal.ofReal (realPWIntervalWeight α s t)
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight α s)
  have hρf : ∀ᵐ t ∂volume, ρ t < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hρw (t : ℝ) : (ρ t).toReal = realPWIntervalWeight α s t :=
    ENNReal.toReal_ofReal ((zero_le_one : (0 : ℝ) ≤ 1).trans
      (one_le_realPWIntervalWeight α s hs t))
  refine ⟨?_, ?_⟩
  · simpa only [hρw, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' hρ hρf).mp hInt
  · have hh := integral_withDensity_eq_integral_toReal_smul hρ hρf
      (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖ ^ 2)
    simp only [hρw, smul_eq_mul] at hh
    rw [← hh]
    change (∫ t, ‖realPWNormalizedEval Y α s hs x t‖ ^ 2 ∂μ) ≤ 1
    rw [integral_congr_ae hSq, L2.integral_sq_norm (𝕜 := ℂ)]
    exact pow_le_pow_left₀ (norm_nonneg z) hzNorm 2 |>.trans_eq (one_pow _)

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. The weighted value of the normalized
evaluation vector at `x`, taken at the contracted point `g⁻¹ x`, tends to zero as `x` grows,
uniformly for `g` in a compact interval `[a, b]` of dilations above one. The limit is along the
product of the filter at infinity in `x` with the principal filter of the interval, which is
uniform convergence on the interval.
Reconstruction: The paper does not state this. It is the fixed-dilation estimate behind
`realPWSharpDensity_decay`, made uniform: the concentration of the evaluation vectors in two
windows does not involve the dilation, and the contracted point leaves both windows at a rate
that is bounded below on the interval. -/
theorem tendsto_realPWNormalizedEval_dilation_uniform {Y α s : ℝ} (hY : 0 < Y) (ha : 0 ≤ α)
    (hs : 0 ≤ s) {a b : ℝ} (hab : 1 < a) :
    Tendsto (fun i : ℝ × ℝ ↦ (Real.sqrt (realPWIntervalWeight α s (i.2⁻¹ * i.1)) : ℂ) *
        realPWNormalizedEval Y α s hs i.1 (i.2⁻¹ * i.1))
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
  let w := realPWIntervalWeight α s
  let hμ := volume_le_realPWIntervalMeasure α s hs
  have hw (x : ℝ) : 0 < w x := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  have ha0 : 0 < a := zero_lt_one.trans hab
  obtain ⟨φ, _, hone, _⟩ := exists_evenSchwartz_fourierInv_plateau Y 1 hY.le zero_lt_one
  obtain ⟨B, hB, henv⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  let G (t : ℝ) := B * (1 + |t|)⁻¹
  have hK : ∀ᶠ i : ℝ × ℝ in atTop ×ˢ 𝓟 (Icc a b), i.2 ∈ Icc a b :=
    tendsto_snd.eventually (eventually_principal.2 fun _ h ↦ h)
  have hX (X : ℝ) : ∀ᶠ i : ℝ × ℝ in atTop ×ˢ 𝓟 (Icc a b), X ≤ i.1 :=
    tendsto_fst.eventually (eventually_ge_atTop X)
  refine tendsto_weighted_eval_zero_of_twoWindows (ι := ℝ × ℝ) (a := fun i ↦ i.1)
    (b := fun i ↦ -i.1) (y := fun i ↦ i.2⁻¹ * i.1)
    (f := fun i ↦ realPWNormalizedEval Y α s hs i.1) (φ := φ) (w := w) (G := G) (C := 1)
    hw (measurable_realPWIntervalWeight α s) ?_
    (fun i ↦ (realPWNormalizedEval_sq_copy Y α s hs i.1).2)
    (fun ε hε ↦ (realPWIntervalBand_twoWindowConcentration hY ha hs ε hε).imp
      fun R hR ↦ hR.prod_inl _) ?_ ?_ φ.continuous.aestronglyMeasurable ?_ hB ?_
  · intro i
    let f := realPWNormalizedEval Y α s hs i.1
    have hf : Continuous f := (RealPWBand.contDiff_evaluation Y hμ _ 0).continuous
    apply (memLp_two_iff_integrable_sq_norm
      (((Complex.continuous_ofReal.measurable.comp
        (Real.continuous_sqrt.measurable.comp (measurable_realPWIntervalWeight α s))).mul
          hf.measurable).aestronglyMeasurable)).mpr
    convert (realPWNormalizedEval_sq_copy Y α s hs i.1).1 using 1
    ext t
    change ‖(Real.sqrt (w t) : ℂ) * f t‖ ^ 2 = w t * ‖f t‖ ^ 2
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw t).le]
  · refine tendsto_atTop.2 fun M ↦ ?_
    have h1 : 0 < 1 - a⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hab)
    filter_upwards [hK, hX (max 0 (M / (1 - a⁻¹)))] with i hi hx
    have hx0 : 0 ≤ i.1 := (le_max_left _ _).trans hx
    have hinv : i.2⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hi.1
    have hM : M ≤ (1 - a⁻¹) * i.1 := by
      have h := (le_max_right 0 (M / (1 - a⁻¹))).trans hx
      rwa [div_le_iff₀ h1, mul_comm] at h
    have hprod := mul_nonneg (sub_nonneg.mpr hinv) hx0
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by nlinarith)]
    nlinarith
  · refine tendsto_atTop.2 fun M ↦ ?_
    filter_upwards [hK, hX (max 0 M)] with i hi hx
    have hg0 : 0 < i.2 := ha0.trans_le hi.1
    have hx0 : 0 ≤ i.1 := (le_max_left _ _).trans hx
    have hM : M ≤ i.1 := (le_max_right _ _).trans hx
    have hp : 0 ≤ i.2⁻¹ * i.1 := mul_nonneg (inv_nonneg.mpr hg0.le) hx0
    rw [Real.dist_eq, sub_neg_eq_add, abs_of_nonneg (by linarith)]
    linarith
  · intro i
    exact RealPWBand.evaluation_reproduces Y hμ _ φ.integrable hone (i.2⁻¹ * i.1)
  · filter_upwards [hK, hX (4 * b)] with i hi hx
    have hg0 : 0 < i.2 := ha0.trans_le hi.1
    have hx' : 4 ≤ i.2⁻¹ * i.1 := by
      rw [← div_eq_inv_mul, le_div_iff₀ hg0]
      exact (mul_le_mul_of_nonneg_left hi.2 (by norm_num)).trans hx
    refine ae_of_all _ fun t ↦ ?_
    rw [← Real.sqrt_div (hw (i.2⁻¹ * i.1)).le (w (i.2⁻¹ * i.1 + t)), mul_comm]
    exact henv (i.2⁻¹ * i.1) hx' t

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. The sharp density of the real-place cutoff
dilation tends to zero at both ends of the line, uniformly for the dilation `g` in a compact
interval `[a, b]` above one: one radius serves every `g` of the interval.
Reconstruction: The paper does not state this. `realPWSharpDensity_decay` is the statement for
one dilation, with a radius that may depend on it. -/
theorem realPWSharpDensity_decay_uniform {Y α s : ℝ} (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s)
    {a b : ℝ} (hab : 1 < a) :
    ∀ ε > 0, ∃ R ≥ 0, ∀ g ∈ Icc a b, ∀ x ∉ Icc (-R) R,
      ‖realPWSharpDensity Y α s hs g x‖ ≤ ε := by
  let w := realPWIntervalWeight α s
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ
  have hw (x : ℝ) : 0 < w x := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  have ha0 : 0 < a := zero_lt_one.trans hab
  obtain ⟨φ, _, hone, _⟩ := exists_evenSchwartz_fourierInv_plateau Y 1 hY.le zero_lt_one
  obtain ⟨B, hB, henv⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  let G (t : ℝ) := B * (1 + |t|)⁻¹
  let A := Real.sqrt (∫ t, G t ^ 2)
  let D := Real.exp (2 * (α * Real.log b)) * (1 + Real.log b + Real.log b ^ 2) ^ (s / 2)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hq : 0 ≤ 1 + Real.log b + Real.log b ^ 2 := by nlinarith [sq_nonneg (Real.log b + 1 / 2)]
  have hD0 : 0 ≤ D := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hq _)
  have hA : ∀ x, 4 ≤ x → Real.sqrt (w x) * ‖e x‖ ≤ A := by
    intro x hx
    have h := Real.sqrt_le_sqrt (realPWIntervalWeight_mul_evaluationVector_norm_sq_le
      Y α s hs φ hone G hB x (ae_of_all _ fun t ↦ by rw [mul_comm]; exact henv x hx t))
    change Real.sqrt (w x * ‖e x‖ ^ 2) ≤ _ at h
    rwa [Real.sqrt_mul (hw x).le, Real.sqrt_sq (norm_nonneg _)] at h
  have hD : ∀ g ∈ Icc a b, ∀ x, Real.sqrt (w x) ≤ Real.sqrt D * Real.sqrt (w (g⁻¹ * x)) := by
    intro g hg x
    have hg0 : 0 < g := ha0.trans_le hg.1
    have hlog0 : 0 ≤ Real.log g := Real.log_nonneg (hab.le.trans hg.1)
    have hlogb : Real.log g ≤ Real.log b := Real.log_le_log hg0 hg.2
    have h := realPWIntervalWeight_le_dilation (α := α) hs (inv_pos.mpr hg0) x
    rw [Real.log_inv] at h
    have hD' : Real.exp (2 * |α * -Real.log g|) *
        (1 + |-Real.log g| + (-Real.log g) ^ 2) ^ (s / 2) ≤ D := by
      rw [mul_neg, abs_neg, abs_neg, neg_sq, abs_of_nonneg (mul_nonneg ha hlog0),
        abs_of_nonneg hlog0]
      have hmono : α * Real.log g ≤ α * Real.log b := mul_le_mul_of_nonneg_left hlogb ha
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
        (Real.rpow_le_rpow (by nlinarith) (by nlinarith) (by positivity))
        (Real.rpow_nonneg (by nlinarith) _) (Real.exp_pos _).le
    rw [← Real.sqrt_mul hD0]
    exact Real.sqrt_le_sqrt (h.trans (mul_le_mul_of_nonneg_right hD' (hw _).le))
  have hT := tendsto_realPWNormalizedEval_dilation_uniform (b := b) hY ha hs hab
  intro ε hε
  have hden : 0 < A * Real.sqrt D + 1 := by positivity
  have hδ : 0 < ε / (A * Real.sqrt D + 1) := div_pos hε hden
  have hev := (Metric.tendsto_nhds.mp hT) _ hδ
  rw [eventually_prod_principal_iff] at hev
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨max (max X 4) 0, le_max_right _ _, fun g hg x hx ↦ ?_⟩
  have hg0 : 0 < g := ha0.trans_le hg.1
  have hgr : g ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hab.le.trans hg.1) (by norm_num)
  have hgr0 : 0 ≤ g ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hg0.le _
  have key : ∀ x, max (max X 4) 0 < x → ‖realPWSharpDensity Y α s hs g x‖ ≤ ε := by
    intro x hx
    have hxX : X ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx.le
    have hx4 : 4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx.le
    have hsmall := hX x hxX g hg
    rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hsmall
    let N := ‖realPWNormalizedEval Y α s hs x (g⁻¹ * x)‖
    have hN0 : 0 ≤ N := norm_nonneg _
    have hev : ‖RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)‖ = ‖e x‖ * N := by
      by_cases h0 : ‖e x‖ = 0
      · have hz : e x = 0 := norm_eq_zero.mp h0
        rw [hz, map_zero, norm_zero, norm_zero, zero_mul]
      · change _ = ‖e x‖ * ‖RealPWBand.evaluation Y hμ (g⁻¹ * x) (((‖e x‖⁻¹ : ℝ) : ℂ) • e x)‖
        rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), ← mul_assoc, mul_inv_cancel₀ h0,
          one_mul]
    have hd : ‖realPWSharpDensity Y α s hs g x‖ =
        g ^ (-(1 / 2 : ℝ)) * ((Real.sqrt (w x) * ‖e x‖) * (Real.sqrt (w x) * N)) := by
      change ‖((w x * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw x).le hgr0), hev]
      have hsq := Real.mul_self_sqrt (hw x).le
      linear_combination (-(g ^ (-(1 / 2 : ℝ)) * (‖e x‖ * N))) * hsq
    have hQ : Real.sqrt (w x) * N ≤ Real.sqrt D * (ε / (A * Real.sqrt D + 1)) := by
      calc Real.sqrt (w x) * N ≤ (Real.sqrt D * Real.sqrt (w (g⁻¹ * x))) * N :=
            mul_le_mul_of_nonneg_right (hD g hg x) hN0
        _ = Real.sqrt D * (Real.sqrt (w (g⁻¹ * x)) * N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsmall.le (Real.sqrt_nonneg _)
    rw [hd]
    calc g ^ (-(1 / 2 : ℝ)) * ((Real.sqrt (w x) * ‖e x‖) * (Real.sqrt (w x) * N))
        ≤ 1 * (A * (Real.sqrt D * (ε / (A * Real.sqrt D + 1)))) :=
          mul_le_mul hgr (mul_le_mul (hA x hx4) hQ
            (mul_nonneg (Real.sqrt_nonneg _) hN0) hA0)
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
              (mul_nonneg (Real.sqrt_nonneg _) hN0)) zero_le_one
      _ = A * Real.sqrt D * ε / (A * Real.sqrt D + 1) := by ring
      _ ≤ ε := by
        rw [div_le_iff₀ hden]
        nlinarith [mul_nonneg hA0 (Real.sqrt_nonneg D)]
  have heven : realPWSharpDensity Y α s hs g (-x) = realPWSharpDensity Y α s hs g x := by
    have hwEven : w (-x) = w x := by simp only [w, realPWIntervalWeight, abs_neg]
    change ((w (-x) * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        RealPWBand.evaluation Y hμ (g⁻¹ * -x) (e (-x)) =
      ((w x * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)
    rw [hwEven, mul_neg, show e (-x) = e x from RealPWBand.evaluationVector_even Y hμ x,
      RealPWBand.evaluation_even]
  by_cases hpos : max (max X 4) 0 < x
  · exact key x hpos
  · have hneg : max (max X 4) 0 < -x := by
      by_contra hn
      exact hx ⟨by linarith [not_lt.mp hn], not_lt.mp hpos⟩
    rw [← heven]
    exact key (-x) hneg

end RiemannMasullo.Isolated
