module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWFixedBandwidthTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUniformDecay
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # The real-place trace for a test function of the dilation

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, in the fixed-bandwidth model of the real
place of `ℚ` of #7354.

`Sec4_RealPWFixedBandwidthTrace` computes, for one dilation `g > 1`, the limit of the trace of
the sharp cutoff to `[-L, L]` of the half-density dilation by `g⁻¹`, compressed to the weighted
even band. This file integrates over the dilation.

* `tendsto_integral_realPWSharpTrace`. For an integrable `ψ` that vanishes outside `[a, b]`
  with `1 < a`, the integral of `ψ g` against the trace for the dilation `g` converges, as the
  cutoff is removed, to the integral of `ψ g` against the limit for `g`.
* `exists_realPWTestCutoff_nuclear`. For continuous `ψ`, the operator
  `f ↦ P (x ↦ 1_[-L, L] (x) ∫ ψ g g ^ (-1/2) f (g⁻¹ x) dg)`, with `P` the orthogonal projection
  onto the band, is nuclear, and its trace is that integral of traces. With `ψ g = φ g / g`
  this is the cutoff of the convolution with `φ` for the multiplicative Haar measure. Here `ψ`
  vanishes outside `[a, b]` with `0 < a`, so its support may lie on either side of `g = 1`.
* `exists_realPWTestCutoff_trace_limit` combines the two.
* `realPWSharpTraceLimit_of_lt_half`. Below width one half the limit for the dilation `g` is
  `(1/2) (1 / (g - 1) + 1 / (g + 1)) g ^ (1/2)`, the integrand of the real term of (12.4.1.1)
  summed over the two signs.

The interchange of the limit with the integral over `g` is dominated convergence. The trace for
the dilation `g` is the trace of a cutoff smoothed by a kernel `η`, known in closed form, plus
the integral of the diagonal against the difference of the sharp and the smoothed cutoff
(`realPWSharpTrace_eq_smooth_add`). One kernel serves all `g ≥ a`. The second term is bounded
uniformly in `g` and `L` by the uniform decay of the diagonal
(`realPWSharpDensity_decay_uniform`) and a uniform bound for its integral over a bounded
interval (`exists_setIntegral_norm_realPWSharpDensity_le`).

Reconstruction: The paper does not state this. The operator is the one of the model, on the
whole weighted band. For `α < 1/2` the level of the model is the smaller space of band vectors
vanishing at the origin (#7770). The trace on that level is computed in
`Sec4_RealPWLevelTrace`.

Not treated here: the limit of the trace for test functions whose support meets `g = 1` or
`g < 1`. Without weight the case `g < 1` is in `Sec4_RealPWUnweightedLowerTrace`. The
comparison with the adelic operator of the paper. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

variable {Y α s : ℝ}

/-- The trace of the sharp cutoff to `[-L, L]` of the dilation by `g⁻¹` on the weighted even
band, written as the integral of its diagonal. -/
def realPWSharpTrace (Y α s : ℝ) (hs : 0 ≤ s) (g L : ℝ) : ℂ :=
  ∫ x, sharpIntervalMask L x * realPWSharpDensity Y α s hs g x

/-- The limit of the sharp trace of the dilation by `g⁻¹` as the cutoff is removed. -/
def realPWSharpTraceLimit (α g : ℝ) : ℂ :=
  ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((g⁻¹ : ℝ) : ℂ) ^ (2 * realPWOriginJetCount α) /
    (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2)

/-- The diagonal of the dilation by `g⁻¹` is integrable on bounded intervals. -/
theorem integrableOn_realPWSharpDensity (hY : 0 ≤ Y) (ha : 0 ≤ α) (hs : 0 ≤ s) {g : ℝ}
    (hg : 1 < g) (R : ℝ) : IntegrableOn (realPWSharpDensity Y α s hs g) (Icc (-R) R) := by
  obtain ⟨_, hi, -⟩ := realPWCutoff_exists_nuclear_of_integrable_mask Y α s hs hY ha g hg
    (integrable_sharpIntervalMask R) ⟨1, fun x ↦ by
      by_cases hx : x ∈ Icc (-R) R <;> simp [sharpIntervalMask, hx]⟩
  have he : (fun x ↦ sharpIntervalMask R x * realPWSharpDensity Y α s hs g x) =
      (Icc (-R) R).indicator (realPWSharpDensity Y α s hs g) := by
    funext x
    by_cases hx : x ∈ Icc (-R) R <;> simp [sharpIntervalMask, hx]
  rw [he, integrable_indicator_iff measurableSet_Icc] at hi
  exact hi

/-- The sharp trace as a function of the dilation is measurable. -/
theorem measurable_realPWSharpTrace (hs : 0 ≤ s) (L : ℝ) :
    Measurable (fun g ↦ realPWSharpTrace Y α s hs g L) := by
  have hμ := volume_le_realPWIntervalMeasure α s hs
  have hK : Continuous (fun p : ℝ × ℝ ↦ RealPWBand.evaluation Y hμ p.1
      (RealPWBand.evaluationVector Y hμ p.2)) :=
    ((RealPWBand.continuous_evaluation Y hμ).comp continuous_fst).clm_apply
      ((RealPWBand.continuous_evaluationVector Y hμ).comp continuous_snd)
  have h1 : Measurable (fun p : ℝ × ℝ ↦ sharpIntervalMask L p.2) :=
    (measurable_one.indicator measurableSet_Icc).comp measurable_snd
  have h2 : Measurable (fun p : ℝ × ℝ ↦
      ((realPWIntervalWeight α s p.2 * p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (((measurable_realPWIntervalWeight α s).comp measurable_snd).mul
        (measurable_fst.pow_const _))
  have h3 : Measurable (fun p : ℝ × ℝ ↦ RealPWBand.evaluation Y hμ (p.1⁻¹ * p.2)
      (RealPWBand.evaluationVector Y hμ p.2)) :=
    hK.measurable.comp ((measurable_fst.inv.mul measurable_snd).prodMk measurable_snd)
  have hF : Measurable (fun p : ℝ × ℝ ↦
      sharpIntervalMask L p.2 * realPWSharpDensity Y α s hs p.1 p.2) := h1.mul (h2.mul h3)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The sharp trace of the dilation by `g⁻¹` is the trace of the cutoff smoothed by `η`, which
is known in closed form, plus the integral of the diagonal against the difference of the two
cutoffs. One kernel `η` serves every `g` with `c ≤ (1 - g⁻¹) Y`. -/
theorem realPWSharpTrace_eq_smooth_add (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) {g : ℝ}
    (hg : 1 < g) (η : 𝓢(ℝ, ℂ)) (heven : Function.Even (η : ℝ → ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hmargin : c ≤ (1 - g⁻¹) * Y) (hη : Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c)
    (L : ℝ) :
    Integrable (fun x ↦ (sharpIntervalMask L x - smoothIntervalMask η L x) *
      realPWSharpDensity Y α s hs g x) ∧
    realPWSharpTrace Y α s hs g L =
      ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L 0 *
        ((g⁻¹ : ℝ) : ℂ) ^ (2 * realPWOriginJetCount α) / (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2) +
      ∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) *
        realPWSharpDensity Y α s hs g x := by
  have hμ := volume_le_realPWIntervalMeasure α s hs
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  let n := realPWOriginJetCount α
  have hg0 : 0 < g := zero_lt_one.trans hg
  have hq : ‖g⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hg0.le)]
    exact inv_lt_one_of_one_lt₀ hg
  obtain ⟨_, hAi, -⟩ := realPWCutoff_exists_nuclear_of_integrable_mask Y α s hs hY.le ha g hg
    (integrable_sharpIntervalMask L) ⟨1, fun x ↦ by
      by_cases hx : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, hx]⟩
  obtain ⟨T, hBi, hBt, -, hBact⟩ :=
    realPWCutoff_exists_nuclear_of_integrable_mask Y α s hs hY.le ha g hg
      (integrable_smoothIntervalMask η η.integrable L)
      ⟨∫ t, ‖η t‖, norm_smoothIntervalMask_le η.integrable L⟩
  have hzero (f : RealPWBand.space Y hμ) : ∀ k < 2 * n,
      iteratedDeriv k (fun x ↦ RealPWBand.evaluation Y hμ x f) 0 = 0 :=
    realPWInterval_forcedOriginJets Y α s ha hs n (fun j hj ↦ realPWOriginJetCount_min α hj) f
  have hTact : ∀ (f : RealPWBand.space Y hμ) (x : ℝ),
      RealPWBand.evaluation Y hμ x (T.val f) =
        ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L x *
          RealPWBand.evaluation Y hμ (g⁻¹ * x) f := by
    intro f
    obtain ⟨r, hr⟩ := exists_realPW_smoothIntervalMask_mul_dilate_evaluation hY hs
      (inv_pos.mpr hg0) hc hmargin η heven hη L ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) f
    exact hBact f r hr
  have hclosed : hilbertTrace T =
      ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L 0 *
        ((g⁻¹ : ℝ) : ℂ) ^ (2 * n) / (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2) :=
    hilbertTrace_eq_of_even_multiplier_dilation T
      (fun f x ↦ RealPWBand.evaluation Y hμ x f)
      (fun x ↦ ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L x) g⁻¹ hq n
      (fun f k ↦ RealPWBand.contDiff_evaluation Y hμ f k)
      (fun k ↦ contDiff_const.mul
        (RealPWBand.contDiff_smoothIntervalMask_of_fourier_support η hc hη L k))
      (RealPWBand.evaluation_even Y hμ) hzero hTact
      (fun j ↦ RealPWBand.evaluationJet Y hμ (2 * (n + j)) 0)
      (realPWInterval_evaluationJet_tail_linearIndependent hY ha hs)
      (fun f hf ↦ RealPWBand.eq_zero_of_evaluationJet_tail Y hY.le hμ hμac n f
        (fun j hj ↦ hzero f (2 * j) (by omega)) hf)
      (fun j f ↦ RealPWBand.evaluationJet_apply Y hμ (2 * (n + j)) 0 f)
  have hgap : Integrable (fun x ↦ (sharpIntervalMask L x - smoothIntervalMask η L x) *
      realPWSharpDensity Y α s hs g x) :=
    (hAi.sub hBi).congr (ae_of_all _ fun x ↦ by
      simp only [Pi.sub_apply]
      ring)
  refine ⟨hgap, ?_⟩
  rw [← hclosed, hBt, ← integral_add hBi hgap]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  ring

/-- One constant bounds the weight at `x` by the weight at `g⁻¹ x`, for all `g` between `1`
and `b`. -/
theorem exists_realPWIntervalWeight_le_dilation (ha : 0 ≤ α) (hs : 0 ≤ s) (b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g ∈ Icc 1 b, ∀ x : ℝ,
      realPWIntervalWeight α s x ≤ K * realPWIntervalWeight α s (g⁻¹ * x) := by
  have hbaseb : 0 ≤ 1 + Real.log b + Real.log b ^ 2 := by
    nlinarith [sq_nonneg (Real.log b + 1 / 2)]
  refine ⟨Real.exp (2 * α * Real.log b) * (1 + Real.log b + Real.log b ^ 2) ^ (s / 2),
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hbaseb _), fun g hg x ↦ ?_⟩
  have hg1 : 1 ≤ g := hg.1
  have hg0 : 0 < g := zero_lt_one.trans_le hg1
  have hlog : 0 ≤ Real.log g := Real.log_nonneg hg1
  have hlogb : Real.log g ≤ Real.log b := Real.log_le_log hg0 hg.2
  have hbase : 0 ≤ 1 + Real.log g + Real.log g ^ 2 := by positivity
  have hw0 : 0 ≤ realPWIntervalWeight α s (g⁻¹ * x) :=
    zero_le_one.trans (one_le_realPWIntervalWeight α s hs _)
  have h := realPWIntervalWeight_le_dilation (α := α) (s := s) hs (inv_pos.mpr hg0) x
  have hl : Real.log g⁻¹ = -Real.log g := Real.log_inv g
  rw [hl, mul_neg, abs_neg, abs_neg, neg_sq, abs_of_nonneg (mul_nonneg ha hlog),
    abs_of_nonneg hlog] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hw0)
  have h1 : Real.exp (2 * (α * Real.log g)) ≤ Real.exp (2 * α * Real.log b) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (1 + Real.log g + Real.log g ^ 2) ^ (s / 2) ≤
      (1 + Real.log b + Real.log b ^ 2) ^ (s / 2) :=
    Real.rpow_le_rpow hbase (by nlinarith) (div_nonneg hs zero_le_two)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hbase _) (Real.exp_nonneg _)

/-- One constant bounds the weight at `x` by the weight at `g⁻¹ x`, for all `g` in a compact
interval of positive numbers. -/
theorem exists_realPWIntervalWeight_le_dilation_of_pos (hs : 0 ≤ s) {a : ℝ} (ha0 : 0 < a)
    (b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g ∈ Icc a b, ∀ x : ℝ,
      realPWIntervalWeight α s x ≤ K * realPWIntervalWeight α s (g⁻¹ * x) := by
  let M := max |Real.log a| |Real.log b|
  have hM1 : |Real.log a| ≤ M := le_max_left _ _
  have hM2 : |Real.log b| ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM1
  have hbaseM : 0 ≤ 1 + M + M ^ 2 := by positivity
  refine ⟨Real.exp (2 * (|α| * M)) * (1 + M + M ^ 2) ^ (s / 2),
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hbaseM _), fun g hg x ↦ ?_⟩
  have hg0 : 0 < g := ha0.trans_le hg.1
  have hlogM : |Real.log g| ≤ M := by
    have h1 : Real.log a ≤ Real.log g := Real.log_le_log ha0 hg.1
    have h2 : Real.log g ≤ Real.log b := Real.log_le_log hg0 hg.2
    have h3 := neg_abs_le (Real.log a)
    have h4 := le_abs_self (Real.log b)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hw0 : 0 ≤ realPWIntervalWeight α s (g⁻¹ * x) :=
    zero_le_one.trans (one_le_realPWIntervalWeight α s hs _)
  have h := realPWIntervalWeight_le_dilation (α := α) (s := s) hs (inv_pos.mpr hg0) x
  have hl : Real.log g⁻¹ = -Real.log g := Real.log_inv g
  rw [hl, mul_neg, abs_neg, abs_neg, neg_sq, abs_mul] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hw0)
  have hbase : 0 ≤ 1 + |Real.log g| + Real.log g ^ 2 := by positivity
  have h1 : Real.exp (2 * (|α| * |Real.log g|)) ≤ Real.exp (2 * (|α| * M)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg α])
  have h2 : (1 + |Real.log g| + Real.log g ^ 2) ^ (s / 2) ≤ (1 + M + M ^ 2) ^ (s / 2) :=
    Real.rpow_le_rpow hbase
      (by nlinarith [abs_nonneg (Real.log g), sq_abs (Real.log g)]) (div_nonneg hs zero_le_two)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hbase _) (Real.exp_nonneg _)

/-- On a bounded interval the diagonal of the dilation by `g⁻¹` is bounded in `L¹` uniformly
for `g` between `1` and `b`. -/
theorem exists_setIntegral_norm_realPWSharpDensity_le (hY : 0 ≤ Y) (ha : 0 ≤ α) (hs : 0 ≤ s)
    (b R : ℝ) :
    ∃ D : ℝ, ∀ g ∈ Icc 1 b,
      ∫ x in Icc (-R) R, ‖realPWSharpDensity Y α s hs g x‖ ≤ D := by
  have hμ := volume_le_realPWIntervalMeasure α s hs
  let w := realPWIntervalWeight α s
  let e := RealPWBand.evaluationVector Y hμ
  have hw0 (x : ℝ) : 0 ≤ w x := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  let n := realPWOriginJetCount α
  let k := 2 * n
  have hk : -1 < (↑(2 * k) : ℝ) - 2 * α := by
    dsimp only [k, n]
    push_cast
    nlinarith only [realPWOriginJetCount_spec α]
  have hjet (f : RealPWBand.space Y hμ) : ∀ j < k,
      iteratedDeriv j (fun x ↦ RealPWBand.evaluation Y hμ x f) 0 = 0 :=
    realPWInterval_forcedOriginJets Y α s ha hs n (fun j hj ↦ realPWOriginJetCount_min α hj) f
  let S : Set ℝ := Icc (-R) R
  let Ψ : ℝ → ℝ := S.indicator fun x ↦ w x * ‖e x‖ ^ 2
  have hΨ0 (x : ℝ) : 0 ≤ Ψ x :=
    indicator_nonneg (fun y _ ↦ mul_nonneg (hw0 y) (sq_nonneg _)) x
  have hΨ : Integrable Ψ := by
    have h := integrable_realPWIntervalWeight_mask_eval_norm_sq Y α s hY ha hs k hk hjet
      zero_lt_one le_rfl (integrable_sharpIntervalMask R) ⟨1, fun x ↦ by
        by_cases hx : x ∈ Icc (-R) R <;> simp [sharpIntervalMask, hx]⟩
    refine h.congr (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ Icc (-R) R
    · simp [Ψ, S, w, e, sharpIntervalMask, hx]
    · simp [Ψ, S, sharpIntervalMask, hx]
  let I := ∫ x, Ψ x
  have hI0 : 0 ≤ I := integral_nonneg hΨ0
  obtain ⟨Kb, hKb0, hKdil⟩ := exists_realPWIntervalWeight_le_dilation (α := α) ha hs b
  refine ⟨1 / 2 * (I + Kb * (b * I)), fun g hg ↦ ?_⟩
  have hg1 : 1 ≤ g := hg.1
  have hg0 : 0 < g := zero_lt_one.trans_le hg1
  have hwdil (x : ℝ) : w x ≤ Kb * w (g⁻¹ * x) := hKdil g hg x
  have hΨg : Integrable (fun x ↦ Ψ (g⁻¹ * x)) := hΨ.comp_mul_left' (inv_ne_zero hg0.ne')
  have hbound : Integrable (fun x ↦ 1 / 2 * (Ψ x + Kb * Ψ (g⁻¹ * x))) :=
    (hΨ.add (hΨg.const_mul Kb)).const_mul _
  have hpt : ∀ x ∈ S, ‖realPWSharpDensity Y α s hs g x‖ ≤
      1 / 2 * (Ψ x + Kb * Ψ (g⁻¹ * x)) := by
    intro x hx
    have hxR : |x| ≤ R := abs_le.mpr hx
    have hgx : g⁻¹ * x ∈ S := by
      have h1 : |g⁻¹ * x| ≤ R := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hg0)]
        calc g⁻¹ * |x| ≤ 1 * |x| :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hg1) (abs_nonneg x)
          _ = |x| := one_mul _
          _ ≤ R := hxR
      exact abs_le.mp h1
    have hΨx : Ψ x = w x * ‖e x‖ ^ 2 := indicator_of_mem hx _
    have hΨgx : Ψ (g⁻¹ * x) = w (g⁻¹ * x) * ‖e (g⁻¹ * x)‖ ^ 2 := indicator_of_mem hgx _
    have hev : ‖RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)‖ ≤ ‖e (g⁻¹ * x)‖ * ‖e x‖ := by
      have h : RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x) = ⟪e (g⁻¹ * x), e x⟫_ℂ := by
        rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
      rw [h]
      exact norm_inner_le_norm _ _
    have hamp : g ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hg1 (by norm_num)
    have hamp0 : 0 ≤ g ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hg0.le _
    have hnorm : ‖realPWSharpDensity Y α s hs g x‖ ≤ w x * (‖e (g⁻¹ * x)‖ * ‖e x‖) := by
      change ‖((w x * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hw0 x) hamp0)]
      calc w x * g ^ (-(1 / 2 : ℝ)) * ‖RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)‖
          ≤ w x * 1 * (‖e (g⁻¹ * x)‖ * ‖e x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hamp (hw0 x)) hev (norm_nonneg _)
              (mul_nonneg (hw0 x) zero_le_one)
        _ = w x * (‖e (g⁻¹ * x)‖ * ‖e x‖) := by ring
    have h2 : w x * ‖e (g⁻¹ * x)‖ ^ 2 ≤ Kb * (w (g⁻¹ * x) * ‖e (g⁻¹ * x)‖ ^ 2) := by
      calc w x * ‖e (g⁻¹ * x)‖ ^ 2 ≤ Kb * w (g⁻¹ * x) * ‖e (g⁻¹ * x)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hwdil x) (sq_nonneg _)
        _ = _ := by ring
    rw [hΨx, hΨgx]
    have h3 : w x * (‖e (g⁻¹ * x)‖ * ‖e x‖) ≤
        1 / 2 * (w x * ‖e x‖ ^ 2 + w x * ‖e (g⁻¹ * x)‖ ^ 2) := by
      nlinarith [mul_nonneg (hw0 x) (sq_nonneg (‖e (g⁻¹ * x)‖ - ‖e x‖))]
    linarith
  calc ∫ x in S, ‖realPWSharpDensity Y α s hs g x‖
      ≤ ∫ x in S, 1 / 2 * (Ψ x + Kb * Ψ (g⁻¹ * x)) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hbound.integrableOn
          ((ae_restrict_mem measurableSet_Icc).mono hpt)
    _ ≤ ∫ x, 1 / 2 * (Ψ x + Kb * Ψ (g⁻¹ * x)) :=
        setIntegral_le_integral hbound (ae_of_all _ fun x ↦
          mul_nonneg (by norm_num) (add_nonneg (hΨ0 x) (mul_nonneg hKb0 (hΨ0 _))))
    _ = 1 / 2 * (I + Kb * (g * I)) := by
        rw [integral_const_mul, integral_add hΨ (hΨg.const_mul Kb), integral_const_mul,
          Measure.integral_comp_mul_left Ψ g⁻¹, inv_inv, abs_of_pos hg0, smul_eq_mul]
    _ ≤ 1 / 2 * (I + Kb * (b * I)) := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hg.2 hI0) hKb0
        linarith

/-- For dilations in a compact interval to the right of `1`, the sharp traces of the dilation
by `g⁻¹` are bounded uniformly in the dilation and the cutoff, and for each dilation they
converge as the cutoff is removed. -/
theorem exists_bound_and_tendsto_realPWSharpTrace (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s)
    {a : ℝ} (ha1 : 1 < a) (b : ℝ) :
    (∃ B : ℝ, ∀ g ∈ Icc a b, ∀ L, ‖realPWSharpTrace Y α s hs g L‖ ≤ B) ∧
      ∀ g ∈ Icc a b, Tendsto (fun L ↦ realPWSharpTrace Y α s hs g L) atTop
        (𝓝 (realPWSharpTraceLimit α g)) := by
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hainv : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
  let c := (1 - a⁻¹) * Y / 2
  have hc : 0 < c := half_pos (mul_pos (sub_pos.mpr hainv) hY)
  obtain ⟨η, he, hm, hη, hmoment⟩ := exists_evenSchwartz_smoothingKernel c hc
  have hmargin : ∀ g, a ≤ g → c ≤ (1 - g⁻¹) * Y := by
    intro g hg
    have h0 : g⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hg
    have h1 : (1 - a⁻¹) * Y ≤ (1 - g⁻¹) * Y :=
      mul_le_mul_of_nonneg_right (by linarith) hY.le
    exact (half_le_self (mul_nonneg (sub_nonneg.mpr hainv.le) hY.le)).trans h1
  let M := ∫ t, ‖η t‖
  have hM0 : 0 ≤ M := integral_nonneg fun _ ↦ norm_nonneg _
  let A := 2 * ∫ t, |t| * ‖η t‖
  obtain ⟨R, -, hR⟩ := realPWSharpDensity_decay_uniform (Y := Y) (α := α) (s := s) (b := b)
    hY ha hs ha1 1 one_pos
  obtain ⟨D, hD⟩ := exists_setIntegral_norm_realPWSharpDensity_le (Y := Y) (α := α) hY.le ha
    hs b R
  have hS1 := fun (g : ℝ) (hg : g ∈ Icc a b) (L : ℝ) ↦
    realPWSharpTrace_eq_smooth_add hY ha hs (ha1.trans_le hg.1) η he hc.le
      (hmargin g hg.1) hη L
  -- the error term is bounded uniformly in the dilation and the cutoff
  have hE : ∀ g ∈ Icc a b, ∀ L, ‖∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) *
      realPWSharpDensity Y α s hs g x‖ ≤ M * D + A := by
    intro g hg L
    have hg1 : 1 < g := ha1.trans_le hg.1
    have hgap := integrable_and_integral_norm_sharpIntervalMask_sub_smoothIntervalMask η
      η.integrable hm hmoment L
    have hint := (hS1 g hg L).1
    have hloc := integrableOn_realPWSharpDensity (Y := Y) hY.le ha hs hg1 R
    have hin : ∫ x in Icc (-R) R, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
        realPWSharpDensity Y α s hs g x‖ ≤ M * D := by
      calc ∫ x in Icc (-R) R, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
            realPWSharpDensity Y α s hs g x‖
          ≤ ∫ x in Icc (-R) R, M * ‖realPWSharpDensity Y α s hs g x‖ :=
            setIntegral_mono_on hint.norm.integrableOn (hloc.norm.const_mul M)
              measurableSet_Icc fun x _ ↦ by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_right
                  (norm_sharpIntervalMask_sub_smoothIntervalMask_le η η.integrable hm L x)
                  (norm_nonneg _)
        _ = M * ∫ x in Icc (-R) R, ‖realPWSharpDensity Y α s hs g x‖ := integral_const_mul _ _
        _ ≤ M * D := mul_le_mul_of_nonneg_left (hD g ⟨ha1.le.trans hg.1, hg.2⟩) hM0
    have hout : ∫ x in (Icc (-R) R)ᶜ, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
        realPWSharpDensity Y α s hs g x‖ ≤ A := by
      calc ∫ x in (Icc (-R) R)ᶜ, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
            realPWSharpDensity Y α s hs g x‖
          ≤ ∫ x in (Icc (-R) R)ᶜ, ‖sharpIntervalMask L x - smoothIntervalMask η L x‖ :=
            setIntegral_mono_on hint.norm.integrableOn hgap.1.norm.integrableOn
              measurableSet_Icc.compl fun x hx ↦ by
                rw [norm_mul]
                exact mul_le_of_le_one_right (norm_nonneg _) (hR g hg x hx)
        _ ≤ ∫ x, ‖sharpIntervalMask L x - smoothIntervalMask η L x‖ :=
            setIntegral_le_integral hgap.1.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
        _ ≤ A := hgap.2
    calc ‖∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) *
          realPWSharpDensity Y α s hs g x‖
        ≤ ∫ x, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
          realPWSharpDensity Y α s hs g x‖ := norm_integral_le_integral_norm _
      _ = (∫ x in Icc (-R) R, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
            realPWSharpDensity Y α s hs g x‖) +
          ∫ x in (Icc (-R) R)ᶜ, ‖(sharpIntervalMask L x - smoothIntervalMask η L x) *
            realPWSharpDensity Y α s hs g x‖ :=
          (integral_add_compl measurableSet_Icc hint.norm).symm
      _ ≤ M * D + A := add_le_add hin hout
  -- the closed-form term is bounded uniformly as well
  let ρ := (1 - a⁻¹ ^ 2)⁻¹
  have hden : 0 < 1 - a⁻¹ ^ 2 := by
    have : a⁻¹ ^ 2 < 1 := pow_lt_one₀ (inv_nonneg.mpr ha0.le) hainv (by norm_num)
    linarith
  have hmain : ∀ g ∈ Icc a b, ∀ L, ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L 0 *
      ((g⁻¹ : ℝ) : ℂ) ^ (2 * realPWOriginJetCount α) / (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2)‖ ≤ M * ρ := by
    intro g hg L
    have hg1 : 1 ≤ g := ha1.le.trans hg.1
    have hg0 : 0 < g := zero_lt_one.trans_le hg1
    have hq0 : 0 ≤ g⁻¹ := inv_nonneg.mpr hg0.le
    have hq1 : g⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hg1
    have hqa : g⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hg.1
    have hdeng : 1 - a⁻¹ ^ 2 ≤ 1 - g⁻¹ ^ 2 := by
      have := pow_le_pow_left₀ hq0 hqa 2
      linarith
    have hcast : (1 : ℂ) - ((g⁻¹ : ℝ) : ℂ) ^ 2 = ((1 - g⁻¹ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [norm_div, norm_mul, norm_mul, norm_pow, hcast, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hg0.le _),
      Real.norm_of_nonneg hq0, Real.norm_of_nonneg (hden.le.trans hdeng)]
    have h1 : g ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hg1 (by norm_num)
    have h2 : ‖smoothIntervalMask η L 0‖ ≤ M := norm_smoothIntervalMask_le η.integrable L 0
    have h3 : g⁻¹ ^ (2 * realPWOriginJetCount α) ≤ 1 := pow_le_one₀ hq0 hq1
    have hnum : g ^ (-(1 / 2 : ℝ)) * ‖smoothIntervalMask η L 0‖ *
        g⁻¹ ^ (2 * realPWOriginJetCount α) ≤ M := by
      calc g ^ (-(1 / 2 : ℝ)) * ‖smoothIntervalMask η L 0‖ *
            g⁻¹ ^ (2 * realPWOriginJetCount α) ≤ 1 * M * 1 :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
              (pow_nonneg hq0 _) (mul_nonneg zero_le_one hM0)
        _ = M := by ring
    calc g ^ (-(1 / 2 : ℝ)) * ‖smoothIntervalMask η L 0‖ *
          g⁻¹ ^ (2 * realPWOriginJetCount α) / (1 - g⁻¹ ^ 2)
        ≤ M / (1 - a⁻¹ ^ 2) := div_le_div₀ hM0 hnum hden hdeng
      _ = M * ρ := div_eq_mul_inv _ _
  have hτ : ∀ g ∈ Icc a b, ∀ L, ‖realPWSharpTrace Y α s hs g L‖ ≤ M * ρ + (M * D + A) := by
    intro g hg L
    rw [(hS1 g hg L).2]
    exact (norm_add_le _ _).trans (add_le_add (hmain g hg L) (hE g hg L))
  -- the limit for one dilation
  have hlimit : ∀ g ∈ Icc a b, Tendsto (fun L ↦ realPWSharpTrace Y α s hs g L) atTop
      (𝓝 (realPWSharpTraceLimit α g)) := by
    intro g hg
    have hg1 : 1 < g := ha1.trans_le hg.1
    have h1 := (((tendsto_smoothIntervalMask η η.integrable 0).const_mul
      ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).mul_const
        (((g⁻¹ : ℝ) : ℂ) ^ (2 * realPWOriginJetCount α))).div_const
          (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2)
    have h2 := realPWSharpCutoff_error_tendsto η (realPWSharpDensity Y α s hs g) η.integrable
      hm hmoment (aestronglyMeasurable_realPWSharpDensity Y α s hs g)
      (fun R _ ↦ integrableOn_realPWSharpDensity hY.le ha hs hg1 R)
      (realPWSharpDensity_decay hY ha hs hg1)
    have h3 := h1.add h2
    rw [hm, mul_one, add_zero] at h3
    exact h3.congr fun L ↦ ((hS1 g hg L).2).symm
  exact ⟨⟨M * ρ + (M * D + A), hτ⟩, hlimit⟩

/-- Reconstruction: the sharp trace of the dilation by `g⁻¹`, integrated against a function of
`g` supported in `[a, b]` with `1 < a`, converges as the cutoff is removed to the integral of
the limits for the single dilations. For `ψ g = φ g / g` this is the integral of `φ` against
the multiplicative Haar measure. -/
theorem tendsto_integral_realPWSharpTrace (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) {a b : ℝ}
    (ha1 : 1 < a) (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    Tendsto (fun L ↦ ∫ g, ψ g * realPWSharpTrace Y α s hs g L) atTop
      (𝓝 (∫ g, ψ g * realPWSharpTraceLimit α g)) := by
  obtain ⟨⟨B, hτ⟩, hlimit⟩ := exists_bound_and_tendsto_realPWSharpTrace hY ha hs ha1 b
  refine tendsto_integral_filter_of_dominated_convergence
    (fun g ↦ ‖ψ g‖ * B) (.of_forall fun L ↦ ?_)
    (.of_forall fun L ↦ ae_of_all _ fun g ↦ ?_) (hψ.norm.mul_const _)
    (ae_of_all _ fun g ↦ ?_)
  · exact hψ.aestronglyMeasurable.mul (measurable_realPWSharpTrace hs L).aestronglyMeasurable
  · by_cases hg : g ∈ Icc a b
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hτ g hg L) (norm_nonneg _)
    · rw [hψ0 g hg, zero_mul, norm_zero, zero_mul]
  · by_cases hg : g ∈ Icc a b
    · exact (hlimit g hg).const_mul (ψ g)
    · simp only [hψ0 g hg, zero_mul]
      exact tendsto_const_nhds

/-- Below width one half no jet is forced to vanish at the origin. -/
theorem realPWOriginJetCount_eq_zero {α : ℝ} (hα : α < 1 / 2) : realPWOriginJetCount α = 0 := by
  by_contra h
  have h1 := realPWOriginJetCount_min α (j := 0) (Nat.pos_of_ne_zero h)
  norm_num at h1
  linarith

/-- Below width one half the limit of the sharp trace of the dilation by `g⁻¹`, for `g > 1`,
is `(1/2) (1 / (g - 1) + 1 / (g + 1)) g ^ (1/2)`. This is the integrand of the real term of
(12.4.1.1), p. 514, summed over the two signs of the dilation. -/
theorem realPWSharpTraceLimit_of_lt_half {α g : ℝ} (hα : α < 1 / 2) (hg : 1 < g) :
    realPWSharpTraceLimit α g =
      ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hg0 : 0 < g := zero_lt_one.trans hg
  have hr : g ^ (1 / 2 : ℝ) = g ^ (-(1 / 2 : ℝ)) * g := by
    rw [← Real.rpow_add_one hg0.ne']
    norm_num
  have h1 : g - 1 ≠ 0 := by linarith
  have h2 : g + 1 ≠ 0 := by linarith
  have hreal : g ^ (-(1 / 2 : ℝ)) / (1 - g⁻¹ ^ 2) =
      1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) := by
    rw [hr]
    have h3 : (1 : ℝ) - g⁻¹ ^ 2 ≠ 0 := by
      have : g⁻¹ ^ 2 < 1 :=
        pow_lt_one₀ (inv_nonneg.mpr hg0.le) (inv_lt_one_of_one_lt₀ hg) (by norm_num)
      linarith
    have hg' : g ≠ 0 := hg0.ne'
    rw [div_eq_iff h3]
    field_simp
    ring
  rw [realPWSharpTraceLimit, realPWOriginJetCount_eq_zero hα, mul_zero, pow_zero, mul_one,
    ← hreal]
  push_cast
  ring

section TestOperator

variable (Y α s : ℝ) (hs : 0 ≤ s)

local notation "μw" => realPWIntervalMeasure α s
local notation "hμw" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hμw
local notation "ev" => RealPWBand.evaluation Y hμw
local notation "evv" => RealPWBand.evaluationVector Y hμw

/-- The vector whose pairing with a band vector `f` is the sharp cutoff at `x` of the
half-density dilate of `f` by `g⁻¹`, weighted by `ψ g`. -/
def realPWTestIntegrand (ψ : ℝ → ℂ) (L : ℝ) (p : ℝ × ℝ) : V :=
  star (ψ p.2 * ((p.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * sharpIntervalMask L p.1) •
    evv (p.2⁻¹ * p.1)

/-- The vector family of the sharp cutoff of the action of a test function `ψ` of the
dilation: the integral over the dilation of `realPWTestIntegrand`. -/
def realPWTestRightFamily (ψ : ℝ → ℂ) (L : ℝ) (x : ℝ) : V :=
  ∫ g, realPWTestIntegrand Y α s hs ψ L (x, g)

/-- The sharp mask has norm at most one. -/
theorem sharpIntervalMask_norm_le_one (L x : ℝ) : ‖sharpIntervalMask L x‖ ≤ 1 := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

/-- The sharp mask is idempotent. -/
theorem sharpIntervalMask_mul_self (L x : ℝ) :
    sharpIntervalMask L x * sharpIntervalMask L x = sharpIntervalMask L x := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

/-- The sharp mask is measurable. -/
theorem sharpIntervalMask_measurable (L : ℝ) : Measurable (sharpIntervalMask L) :=
  measurable_one.indicator measurableSet_Icc

/-- The evaluation vector at a contracted point is bounded by a multiple of `|x| ^ k`, where
`k` is the number of jets that the weight forces to vanish at the origin. -/
theorem exists_norm_realPWEvaluationVector_dilate_le (hY : 0 ≤ Y) (ha : 0 ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, 1 ≤ g → ∀ x : ℝ,
      ‖evv (g⁻¹ * x)‖ ≤ C * |x| ^ (2 * realPWOriginJetCount α) := by
  let k := 2 * realPWOriginJetCount α
  have hjet : ∀ (f : V) (j : ℕ), j < k → iteratedDeriv j (fun t ↦ ev t f) 0 = 0 := fun f ↦
    realPWInterval_forcedOriginJets Y α s ha hs _ (fun j hj ↦ realPWOriginJetCount_min α hj) f
  obtain ⟨C, hC, hb⟩ := RealPWBand.exists_norm_evaluationVector_le_abs_pow Y hY hμw k hjet
  have hglob (y : ℝ) : ‖evv y‖ ≤ Real.sqrt (2 * Y) := by
    rw [← (InnerProductSpace.toDual ℂ V).norm_map (evv y), RealPWBand.toDual_evaluationVector]
    exact RealPWBand.norm_evaluation_le Y hY hμw y
  refine ⟨C + Real.sqrt (2 * Y), add_nonneg hC (Real.sqrt_nonneg _), fun g hg x ↦ ?_⟩
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hle : |g⁻¹ * x| ≤ |x| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hg0)]
    exact mul_le_of_le_one_left (abs_nonneg x) (inv_le_one_of_one_le₀ hg)
  by_cases h1 : |g⁻¹ * x| ≤ 1
  · calc ‖evv (g⁻¹ * x)‖ ≤ C * |g⁻¹ * x| ^ k := hb _ h1
      _ ≤ C * |x| ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hle k) hC
      _ ≤ (C + Real.sqrt (2 * Y)) * |x| ^ k :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _))
            (pow_nonneg (abs_nonneg _) k)
  · have hx1 : 1 ≤ |x| := (not_le.mp h1).le.trans hle
    calc ‖evv (g⁻¹ * x)‖ ≤ Real.sqrt (2 * Y) := hglob _
      _ ≤ Real.sqrt (2 * Y) * |x| ^ k :=
          le_mul_of_one_le_right (Real.sqrt_nonneg _) (one_le_pow₀ hx1)
      _ ≤ (C + Real.sqrt (2 * Y)) * |x| ^ k :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (pow_nonneg (abs_nonneg _) k)

/-- The half-density factor times the evaluation vector at a dilated point is bounded by a
multiple of `|x| ^ k`, uniformly for the dilations `g ≥ a`, for any `a > 0`. -/
theorem exists_norm_halfDensity_mul_realPWEvaluationVector_dilate_le (hY : 0 ≤ Y) (ha : 0 ≤ α)
    {a : ℝ} (ha0 : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, a ≤ g → ∀ x : ℝ,
      ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖ ≤
        C * |x| ^ (2 * realPWOriginJetCount α) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_realPWEvaluationVector_dilate_le Y α s hs hY ha
  let k := 2 * realPWOriginJetCount α
  have hA0 : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha0.le _
  refine ⟨a ^ (-(1 / 2 : ℝ)) * (C * a⁻¹ ^ k),
    mul_nonneg hA0 (mul_nonneg hC0 (pow_nonneg (inv_nonneg.mpr ha0.le) _)), fun g hg x ↦ ?_⟩
  have hg0 : 0 < g := ha0.trans_le hg
  have h1 := hC 1 le_rfl (g⁻¹ * x)
  rw [inv_one, one_mul, abs_mul, abs_of_pos (inv_pos.mpr hg0), mul_pow] at h1
  have hamp : ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ a ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hg0.le _)]
    exact Real.rpow_le_rpow_of_nonpos ha0 hg (by norm_num)
  have hinv : g⁻¹ ^ k ≤ a⁻¹ ^ k :=
    pow_le_pow_left₀ (inv_nonneg.mpr hg0.le) (inv_anti₀ ha0 hg) k
  have hx0 : 0 ≤ |x| ^ k := pow_nonneg (abs_nonneg x) k
  calc ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖
      ≤ a ^ (-(1 / 2 : ℝ)) * (C * (g⁻¹ ^ k * |x| ^ k)) :=
        mul_le_mul hamp h1 (norm_nonneg _) hA0
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (C * (a⁻¹ ^ k * |x| ^ k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hinv hx0) hC0) hA0
    _ = _ := by ring

include hs in
/-- The sharp mask times the power of `|x|` that the forced jets provide is integrable for the
weighted measure, also when the weight is not integrable at the origin. -/
theorem integrable_sharpIntervalMask_abs_pow_realPW (ha : 0 ≤ α) (L : ℝ) :
    Integrable (fun x ↦ ‖sharpIntervalMask L x‖ * |x| ^ (2 * (2 * realPWOriginJetCount α)))
      μw := by
  let k := 2 * realPWOriginJetCount α
  have hk : -1 < (((2 * k : ℕ) : ℝ)) - 2 * α := by
    dsimp only [k]
    push_cast
    nlinarith only [realPWOriginJetCount_spec α]
  have hint : IntegrableOn
      (fun x ↦ |x| ^ (((2 * k : ℕ) : ℝ)) * realPWIntervalWeight α s x) (Icc (-L) L) :=
    integrableOn_abs_rpow_mul_realPWIntervalWeight ha hs hk
  have hWm : Measurable fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x) :=
    (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hWlt : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (realPWIntervalWeight α s x) < ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  change Integrable _ (volume.withDensity fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x))
  refine (integrable_withDensity_iff hWm hWlt).2
    ((hint.integrable_indicator measurableSet_Icc).congr (ae_of_all _ fun x ↦ ?_))
  have hw0 := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  change _ = ‖sharpIntervalMask L x‖ * |x| ^ (2 * (2 * realPWOriginJetCount α)) *
    (ENNReal.ofReal (realPWIntervalWeight α s x)).toReal
  rw [ENNReal.toReal_ofReal hw0]
  by_cases hx : x ∈ Icc (-L) L
  · have hm : sharpIntervalMask L x = 1 := by simp [sharpIntervalMask, hx]
    rw [indicator_of_mem hx, hm, norm_one, one_mul, Real.rpow_natCast]
  · have hm : sharpIntervalMask L x = 0 := by simp [sharpIntervalMask, hx]
    rw [indicator_of_notMem hx, hm, norm_zero, zero_mul, zero_mul]

/-- A vector family bounded by the mask times `|x| ^ k` is square integrable for the weighted
measure. -/
private theorem memLp_of_norm_le_mask_pow (ha : 0 ≤ α) (L : ℝ) {W : ℝ → V}
    (hW : AEStronglyMeasurable W μw) {c : ℝ}
    (hb : ∀ x, ‖W x‖ ≤ c * (‖sharpIntervalMask L x‖ * |x| ^ (2 * realPWOriginJetCount α))) :
    MemLp W 2 μw := by
  refine (memLp_two_iff_integrable_sq_norm hW).2
    (((integrable_sharpIntervalMask_abs_pow_realPW α s hs ha L).const_mul (c ^ 2)).mono'
      (hW.norm.pow 2) (ae_of_all _ fun x ↦ ?_))
  have hm0 := norm_nonneg (sharpIntervalMask L x)
  have hm1 := sharpIntervalMask_norm_le_one L x
  have hp0 : 0 ≤ |x| ^ (2 * realPWOriginJetCount α) := pow_nonneg (abs_nonneg x) _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖W x‖ ^ 2 ≤ (c * (‖sharpIntervalMask L x‖ * |x| ^ (2 * realPWOriginJetCount α))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
    _ = c ^ 2 * (‖sharpIntervalMask L x‖ ^ 2 * |x| ^ (2 * (2 * realPWOriginJetCount α))) := by
        ring
    _ ≤ c ^ 2 * (‖sharpIntervalMask L x‖ * |x| ^ (2 * (2 * realPWOriginJetCount α))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_
          (pow_nonneg (abs_nonneg x) _)) (sq_nonneg c)
        nlinarith

/-- The integrand of the right vector family is jointly strongly measurable. -/
private theorem stronglyMeasurable_realPWTestIntegrand {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (L : ℝ) : StronglyMeasurable (realPWTestIntegrand Y α s hs ψ L) := by
  have h1 : Measurable (fun p : ℝ × ℝ ↦
      star (ψ p.2 * ((p.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * sharpIntervalMask L p.1)) :=
    continuous_star.measurable.comp
      (((hψ.comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (measurable_snd.pow_const _))).mul
        ((sharpIntervalMask_measurable L).comp measurable_fst))
  have h2 : StronglyMeasurable (fun p : ℝ × ℝ ↦ evv (p.2⁻¹ * p.1)) :=
    (RealPWBand.continuous_evaluationVector Y hμw).comp_stronglyMeasurable
      (measurable_snd.inv.mul measurable_fst).stronglyMeasurable
  exact h1.stronglyMeasurable.smul h2

/-- The integrand of the right vector family is bounded by `‖ψ g‖` times the mask times
`|x| ^ k`. -/
private theorem norm_realPWTestIntegrand_le {a b : ℝ} {ψ : ℝ → ℂ}
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) {C : ℝ}
    (hC : ∀ g : ℝ, a ≤ g → ∀ x : ℝ, ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖ ≤
      C * |x| ^ (2 * realPWOriginJetCount α)) (x g : ℝ) :
    ‖realPWTestIntegrand Y α s hs ψ L (x, g)‖ ≤
      ‖ψ g‖ * (C * (‖sharpIntervalMask L x‖ * |x| ^ (2 * realPWOriginJetCount α))) := by
  change ‖star (ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * sharpIntervalMask L x) •
    evv (g⁻¹ * x)‖ ≤ _
  by_cases hg : g ∈ Icc a b
  · rw [norm_smul, norm_star, norm_mul, norm_mul]
    calc ‖ψ g‖ * ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖sharpIntervalMask L x‖ *
          ‖evv (g⁻¹ * x)‖
        = ‖ψ g‖ * ‖sharpIntervalMask L x‖ *
            (‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖) := by ring
      _ ≤ ‖ψ g‖ * ‖sharpIntervalMask L x‖ * (C * |x| ^ (2 * realPWOriginJetCount α)) :=
          mul_le_mul_of_nonneg_left (hC g hg.1 x)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  · rw [hψ0 g hg]
    simp

/-- The integrand of the right vector family is integrable in the dilation. -/
private theorem integrable_realPWTestIntegrand {a b : ℝ} {ψ : ℝ → ℂ}
    (hψm : Measurable ψ) (hψi : Integrable ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) {C : ℝ}
    (hC : ∀ g : ℝ, a ≤ g → ∀ x : ℝ, ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖ ≤
      C * |x| ^ (2 * realPWOriginJetCount α)) (x : ℝ) :
    Integrable (fun g ↦ realPWTestIntegrand Y α s hs ψ L (x, g)) :=
  (hψi.norm.mul_const _).mono'
    ((stronglyMeasurable_realPWTestIntegrand Y α s hs hψm L).comp_measurable
      measurable_prodMk_left).aestronglyMeasurable
    (ae_of_all _ fun g ↦ norm_realPWTestIntegrand_le Y α s hs hψ0 L hC x g)

/-- The right vector family is bounded by the mask times `|x| ^ k`. -/
private theorem norm_realPWTestRightFamily_le {a b : ℝ} {ψ : ℝ → ℂ}
    (hψi : Integrable ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) {C : ℝ}
    (hC : ∀ g : ℝ, a ≤ g → ∀ x : ℝ, ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖ ≤
      C * |x| ^ (2 * realPWOriginJetCount α)) (x : ℝ) :
    ‖realPWTestRightFamily Y α s hs ψ L x‖ ≤
      (∫ g, ‖ψ g‖) * C * (‖sharpIntervalMask L x‖ * |x| ^ (2 * realPWOriginJetCount α)) := by
  have h := norm_integral_le_of_norm_le
    (hψi.norm.mul_const (C * (‖sharpIntervalMask L x‖ * |x| ^ (2 * realPWOriginJetCount α))))
    (ae_of_all _ fun g ↦ norm_realPWTestIntegrand_le Y α s hs hψ0 L hC x g)
  rw [integral_mul_const] at h
  exact h.trans (le_of_eq (by ring))

/-- The pairing of the right vector family with a band vector `f` is the cutoff at `x` of the
action of `ψ` on `f`. -/
private theorem inner_realPWTestRightFamily {ψ : ℝ → ℂ} {L : ℝ}
    (hI : ∀ x, Integrable (fun g ↦ realPWTestIntegrand Y α s hs ψ L (x, g))) (x : ℝ)
    (f : V) :
    ⟪realPWTestRightFamily Y α s hs ψ L x, f⟫_ℂ = sharpIntervalMask L x *
      ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f) := by
  have h1 : ⟪f, realPWTestRightFamily Y α s hs ψ L x⟫_ℂ =
      ∫ g, ⟪f, realPWTestIntegrand Y α s hs ψ L (x, g)⟫_ℂ := (integral_inner (hI x) f).symm
  rw [← inner_conj_symm, h1, ← integral_conj, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  change (starRingEnd ℂ) ⟪f, star (ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    sharpIntervalMask L x) • evv (g⁻¹ * x)⟫_ℂ = _
  rw [inner_conj_symm, inner_smul_left, starRingEnd_apply, star_star,
    ← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
  ring

/-- The left vector family of the cutoff: the evaluation vectors under the sharp mask. -/
def realPWTestLeftFamily (L : ℝ) (x : ℝ) : V := sharpIntervalMask L x • evv x

/-- The left vector family is square integrable for the weighted measure. -/
theorem memLp_realPWTestLeftFamily (hY : 0 ≤ Y) (ha : 0 ≤ α) (L : ℝ) :
    MemLp (realPWTestLeftFamily Y α s hs L) 2 μw := by
  obtain ⟨C, -, hC⟩ := exists_norm_realPWEvaluationVector_dilate_le Y α s hs hY ha
  refine memLp_of_norm_le_mask_pow Y α s hs ha L (c := C)
    (((sharpIntervalMask_measurable L).aestronglyMeasurable).smul
      (RealPWBand.continuous_evaluationVector Y hμw).aestronglyMeasurable) fun x ↦ ?_
  have h := hC 1 le_rfl x
  rw [inv_one, one_mul] at h
  change ‖sharpIntervalMask L x • evv x‖ ≤ _
  rw [norm_smul]
  calc ‖sharpIntervalMask L x‖ * ‖evv x‖
      ≤ ‖sharpIntervalMask L x‖ * (C * |x| ^ (2 * realPWOriginJetCount α)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- For a continuous `ψ` supported in `[a, b]` with `0 < a`, the integrand of the right vector
family is integrable in the dilation. -/
theorem integrable_realPWTestIntegrand_of_continuous (hY : 0 ≤ Y) (ha : 0 ≤ α) {a b : ℝ}
    (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L x : ℝ) :
    Integrable (fun g ↦ realPWTestIntegrand Y α s hs ψ L (x, g)) := by
  obtain ⟨C, -, hC⟩ :=
    exists_norm_halfDensity_mul_realPWEvaluationVector_dilate_le Y α s hs hY ha ha0
  exact integrable_realPWTestIntegrand Y α s hs hψc.measurable
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0 L
    hC x

/-- The right vector family is square integrable for the weighted measure. -/
theorem memLp_realPWTestRightFamily (hY : 0 ≤ Y) (ha : 0 ≤ α) {a b : ℝ} (ha0 : 0 < a)
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) :
    MemLp (realPWTestRightFamily Y α s hs ψ L) 2 μw := by
  obtain ⟨C, -, hC⟩ :=
    exists_norm_halfDensity_mul_realPWEvaluationVector_dilate_le Y α s hs hY ha ha0
  exact memLp_of_norm_le_mask_pow Y α s hs ha L
    ((stronglyMeasurable_realPWTestIntegrand Y α s hs hψc.measurable L).integral_prod_right'
      (ν := volume)).aestronglyMeasurable
    (norm_realPWTestRightFamily_le Y α s hs
      (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0 L
      hC)

/-- The pairing of the right vector family with a band vector `f` is the cutoff at `x` of the
action of `ψ` on `f`. -/
theorem inner_realPWTestRightFamily_eq (hY : 0 ≤ Y) (ha : 0 ≤ α) {a b : ℝ} (ha0 : 0 < a)
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L x : ℝ) (f : V) :
    ⟪realPWTestRightFamily Y α s hs ψ L x, f⟫_ℂ = sharpIntervalMask L x *
      ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f) :=
  inner_realPWTestRightFamily Y α s hs
    (integrable_realPWTestIntegrand_of_continuous Y α s hs hY ha ha0 hψc hψ0 L) x f

/-- The integral of the pairing of the two vector families is the integral of `ψ` against the
traces of the cutoffs of the single dilations. -/
theorem integral_inner_realPWTestFamilies (hY : 0 ≤ Y) (ha : 0 ≤ α) {a b : ℝ} (ha0 : 0 < a)
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) :
    ∫ x, ⟪realPWTestRightFamily Y α s hs ψ L x, realPWTestLeftFamily Y α s hs L x⟫_ℂ ∂μw =
      ∫ g, ψ g * realPWSharpTrace Y α s hs g L := by
  have hψm : Measurable ψ := hψc.measurable
  have hψi : Integrable ψ :=
    hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_halfDensity_mul_realPWEvaluationVector_dilate_le Y α s hs hY ha ha0
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_realPWEvaluationVector_dilate_le Y α s hs hY ha
  let k := 2 * realPWOriginJetCount α
  have hC1 : ∀ x, ‖evv x‖ ≤ C₁ * |x| ^ k := by
    intro x
    have h := hC₁ 1 le_rfl x
    rwa [inv_one, one_mul] at h
  let K : ℝ → ℝ → ℂ := fun x g ↦ ψ g * (sharpIntervalMask L x *
    (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x)))
  have hpair : ∀ x, ⟪realPWTestRightFamily Y α s hs ψ L x,
      realPWTestLeftFamily Y α s hs L x⟫_ℂ = ∫ g, K x g := by
    intro x
    rw [inner_realPWTestRightFamily_eq Y α s hs hY ha ha0 hψc hψ0 L x, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change sharpIntervalMask L x * (ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ev (g⁻¹ * x) (sharpIntervalMask L x • evv x))) =
      ψ g * (sharpIntervalMask L x * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ev (g⁻¹ * x) (evv x)))
    rw [map_smul, smul_eq_mul]
    linear_combination (ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x)) *
      sharpIntervalMask_mul_self L x
  have hKm : Measurable (Function.uncurry K) := by
    have hKc : Continuous (fun p : ℝ × ℝ ↦ ev p.1 (evv p.2)) :=
      ((RealPWBand.continuous_evaluation Y hμw).comp continuous_fst).clm_apply
        ((RealPWBand.continuous_evaluationVector Y hμw).comp continuous_snd)
    have h1 : Measurable (fun p : ℝ × ℝ ↦ ψ p.2) := hψm.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × ℝ ↦ sharpIntervalMask L p.1) :=
      (sharpIntervalMask_measurable L).comp measurable_fst
    have h3 : Measurable (fun p : ℝ × ℝ ↦ ((p.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_snd.pow_const _)
    have h4 : Measurable (fun p : ℝ × ℝ ↦ ev (p.2⁻¹ * p.1) (evv p.1)) :=
      hKc.measurable.comp ((measurable_snd.inv.mul measurable_fst).prodMk measurable_fst)
    exact h1.mul (h2.mul (h3.mul h4))
  have hKb : ∀ x g, ‖K x g‖ ≤
      (C * C₁ * (‖sharpIntervalMask L x‖ * |x| ^ (2 * k))) * ‖ψ g‖ := by
    intro x g
    change ‖ψ g * (sharpIntervalMask L x *
      (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x)))‖ ≤ _
    by_cases hg : g ∈ Icc a b
    · have hp0 : 0 ≤ C * |x| ^ k := mul_nonneg hC0 (pow_nonneg (abs_nonneg x) k)
      have hev : ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖ev (g⁻¹ * x) (evv x)‖ ≤
          (C * |x| ^ k) * (C₁ * |x| ^ k) := by
        have h : ev (g⁻¹ * x) (evv x) = ⟪evv (g⁻¹ * x), evv x⟫_ℂ := by
          rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
        rw [h]
        calc ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖⟪evv (g⁻¹ * x), evv x⟫_ℂ‖
            ≤ ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * (‖evv (g⁻¹ * x)‖ * ‖evv x‖) :=
              mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
          _ = (‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖evv (g⁻¹ * x)‖) * ‖evv x‖ := by ring
          _ ≤ (C * |x| ^ k) * (C₁ * |x| ^ k) :=
              mul_le_mul (hC g hg.1 x) (hC1 x) (norm_nonneg _) hp0
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖ψ g‖ * (‖sharpIntervalMask L x‖ *
            (‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖ev (g⁻¹ * x) (evv x)‖))
          ≤ ‖ψ g‖ * (‖sharpIntervalMask L x‖ * ((C * |x| ^ k) * (C₁ * |x| ^ k))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hev (norm_nonneg _))
              (norm_nonneg _)
        _ = _ := by ring
    · rw [hψ0 g hg]
      simp
  have hWm : Measurable fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x) :=
    (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hWlt : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal (realPWIntervalWeight α s x) < ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have : SFinite μw := by
    unfold realPWIntervalMeasure
    infer_instance
  have hKint : Integrable (Function.uncurry K) (Measure.prod μw volume) :=
    (((integrable_sharpIntervalMask_abs_pow_realPW α s hs ha L).const_mul (C * C₁)).mul_prod
      hψi.norm).mono' hKm.aestronglyMeasurable (ae_of_all _ fun z ↦ hKb z.1 z.2)
  calc ∫ x, ⟪realPWTestRightFamily Y α s hs ψ L x, realPWTestLeftFamily Y α s hs L x⟫_ℂ ∂μw
      = ∫ x, (∫ g, K x g) ∂μw := integral_congr_ae (ae_of_all _ hpair)
    _ = ∫ g, (∫ x, K x g ∂μw) := integral_integral_swap hKint
    _ = ∫ g, ψ g * realPWSharpTrace Y α s hs g L := by
        refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
        change ∫ x, ψ g * (sharpIntervalMask L x *
          (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x))) ∂μw = _
        rw [integral_const_mul]
        congr 1
        change ∫ x, sharpIntervalMask L x *
          (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x))
            ∂(volume.withDensity fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x)) = _
        rw [integral_withDensity_eq_integral_toReal_smul hWm hWlt]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        have hw0 := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
        change (ENNReal.ofReal (realPWIntervalWeight α s x)).toReal •
          (sharpIntervalMask L x *
            (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x))) =
          sharpIntervalMask L x *
            (((realPWIntervalWeight α s x * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ev (g⁻¹ * x) (evv x))
        rw [ENNReal.toReal_ofReal hw0, Complex.real_smul]
        push_cast
        ring

/-- The product of the adjoint of the analysis map of the left family with the analysis map of
the right family is the orthogonal projection onto the band of the cutoff of the action of
`ψ`. -/
theorem realPWTest_adjoint_analysis_apply (hY : 0 ≤ Y) (ha : 0 ≤ α) {a b : ℝ} (ha0 : 0 < a)
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ)
    (hU : MemLp (realPWTestLeftFamily Y α s hs L) 2 μw)
    (hR : MemLp (realPWTestRightFamily Y α s hs ψ L) 2 μw) (f : V) :
    (hilbertFamilyAnalysisCLM hU).adjoint (hilbertFamilyAnalysisCLM hR f) =
      (V).orthogonalProjectionOnto (hilbertFamilyAnalysisCLM hR f) := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  apply ext_inner_left ℂ
  intro z
  rw [(hilbertFamilyAnalysisCLM hU).adjoint_inner_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hilbertFamilyAnalysisCLM_apply_ae hU z,
    hilbertFamilyAnalysisCLM_apply_ae hR f, RealPWBand.evaluation_ae Y hμw hμac z]
    with x hax hbx hz
  have hUz : ⟪realPWTestLeftFamily Y α s hs L x, z⟫_ℂ =
      star (sharpIntervalMask L x) * ev x z := by
    change ⟪sharpIntervalMask L x • evv x, z⟫_ℂ = _
    rw [inner_smul_left, starRingEnd_apply, ← InnerProductSpace.toDual_apply_apply,
      RealPWBand.toDual_evaluationVector]
  rw [hax, hbx, ← hz, hUz, inner_realPWTestRightFamily_eq Y α s hs hY ha ha0 hψc hψ0 L x f]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_mul', star_star]
  linear_combination ((∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) *
    star (ev x z)) * sharpIntervalMask_mul_self L x

/-- Reconstruction: the sharp cutoff to `[-L, L]` of the action of a test function `ψ` of the
dilation, compressed to the weighted even band, is nuclear, and its trace is the integral of
`ψ` against the traces of the cutoffs of the single dilations. The operator sends `f` to the
orthogonal projection of `x ↦ 1_[-L, L] (x) ∫ ψ g g ^ (-1/2) f (g⁻¹ x) dg`. The support of `ψ`
may lie on either side of `g = 1`: the dilation need not preserve the band. For
`ψ g = φ g / g` the inner integral is the convolution of `f` with `φ` for the multiplicative
Haar measure, with the half-density factor. -/
theorem exists_realPWTestCutoff_nuclear (hY : 0 < Y) (ha : 0 ≤ α) {a b : ℝ} (ha0 : 0 < a)
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) :
    ∃ T : nuclearEndomorphisms V,
      (∀ f : V, ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) ∧
        T.val f = (V).orthogonalProjectionOnto r) ∧
      hilbertTrace T = ∫ g, ψ g * realPWSharpTrace Y α s hs g L := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  have hU := memLp_realPWTestLeftFamily Y α s hs hY.le ha L
  have hR := memLp_realPWTestRightFamily Y α s hs hY.le ha ha0 hψc hψ0 L
  obtain ⟨ι, bs, _⟩ := exists_hilbertBasis ℂ V
  have := RealPWBand.countable_hilbertBasis Y hμw hμac bs
  let A := hilbertFamilyAnalysisCLM hU
  let B := hilbertFamilyAnalysisCLM hR
  have hA (f : V) : A f =ᵐ[μw] fun x ↦ ⟪realPWTestLeftFamily Y α s hs L x, f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hU f
  have hB (f : V) : B f =ᵐ[μw] fun x ↦ ⟪realPWTestRightFamily Y α s hs ψ L x, f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hR f
  let Ah : hilbertSchmidtOperators V (Lp ℂ 2 μw) :=
    ⟨A, familyAnalysis_mem_hilbertSchmidtOperators bs hU A hA⟩
  let Bh : hilbertSchmidtOperators V (Lp ℂ 2 μw) :=
    ⟨B, familyAnalysis_mem_hilbertSchmidtOperators bs hR B hB⟩
  have hn : IsNuclearOperator (A.adjoint.comp B) :=
    nuclear_hilbertSchmidt_comp ⟨_, mem_hilbertSchmidtOperators_adjoint Ah.property⟩ Bh
  have htrace := hilbertTrace_familyAnalysisProduct bs (realPWTestLeftFamily Y α s hs L)
    (realPWTestRightFamily Y α s hs ψ L) Ah Bh (fun i ↦ hA (bs i)) (fun i ↦ hB (bs i))
  refine ⟨⟨_, hn⟩, fun f ↦ ⟨B f, ?_, ?_⟩,
    htrace.trans (integral_inner_realPWTestFamilies Y α s hs hY.le ha ha0 hψc hψ0 L)⟩
  · filter_upwards [hB f] with x hx
    rw [hx]
    exact inner_realPWTestRightFamily_eq Y α s hs hY.le ha ha0 hψc hψ0 L x f
  · exact realPWTest_adjoint_analysis_apply Y α s hs hY.le ha ha0 hψc hψ0 L hU hR f

/-- Reconstruction: for a continuous test function `ψ` of the dilation supported in `[a, b]`
with `1 < a`, the traces of the sharp cutoffs of its action on the weighted even band converge,
as the cutoff is removed, to the integral of `ψ` against the limits for the single dilations.
Paper: this is the real-place term of Theorem 12.4.1.1, pp. 514–517, in the fixed-bandwidth
model of the real place of `ℚ`, for a test function supported away from `g = 1`. -/
theorem exists_realPWTestCutoff_trace_limit (hY : 0 < Y) (ha : 0 ≤ α) {a b : ℝ}
    (ha1 : 1 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    ∃ T : ℝ → nuclearEndomorphisms V,
      (∀ L (f : V), ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) ∧
        (T L).val f = (V).orthogonalProjectionOnto r) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g * realPWSharpTraceLimit α g)) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_nuclear Y α s hs hY ha (zero_lt_one.trans ha1) ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) =
      fun L ↦ ∫ g, ψ g * realPWSharpTrace Y α s hs g L := funext hT2
  rw [h]
  exact tendsto_integral_realPWSharpTrace hY ha hs ha1 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0

end TestOperator

end RiemannMasullo.Isolated
