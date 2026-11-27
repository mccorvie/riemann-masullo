module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWWeightEstimates
import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerReproducer
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The weighted-band evaluation bound and reduction to concentration -/

public noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace RiemannMasullo.Isolated

private def packetDensity (α s : ℝ) (φ : 𝓢(ℝ, ℂ)) (x t : ℝ) : ℝ :=
  ‖φ t‖ ^ 2 * (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t))

private theorem packetDensity_meas (α s : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Measurable (packetDensity α s φ x) :=
  (φ.continuous.norm.measurable.pow_const 2).mul (measurable_const.div
    ((measurable_realPWIntervalWeight α s).comp (measurable_const.add measurable_id)))

private theorem packetDensity_bound {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ x, 4 ≤ x → ∀ t, ‖packetDensity α s φ x t‖ ≤ g t := by
  obtain ⟨B, hB, h⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  refine ⟨_, hB.integrable_sq, fun t ↦ sq_nonneg _, fun x hx t ↦ ?_⟩
  have hw (y : ℝ) : 0 ≤ realPWIntervalWeight α s y :=
    zero_le_one.trans (one_le_realPWIntervalWeight α s hs y)
  have hr := div_nonneg (hw x) (hw (x+t))
  have hh := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (h x hx t) 2
  simpa only [packetDensity, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hr),
    mul_pow, Real.sq_sqrt hr] using hh

/-- Normalizing the reciprocal energy by the weight at the packet center recovers
exactly the unweighted kernel energy in the limit. -/
theorem tendsto_realPWIntervalWeight_packet_energy {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) : Tendsto (fun x ↦ realPWIntervalWeight α s x *
      ∫ y, ‖φ (y-x)‖ ^ 2 / realPWIntervalWeight α s y) atTop (𝓝 (∫ t, ‖φ t‖ ^ 2)) := by
  obtain ⟨g, hg, _, hb⟩ := packetDensity_bound ha hs φ
  have hc : Tendsto (fun x ↦ ∫ t, packetDensity α s φ x t) atTop (𝓝 (∫ t, ‖φ t‖ ^ 2)) := by
    apply tendsto_integral_filter_of_dominated_convergence g
    · exact Eventually.of_forall fun x ↦ (packetDensity_meas α s φ x).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx using ae_of_all _ (hb x hx)
    · exact hg
    · apply ae_of_all
      intro t
      simpa only [packetDensity, mul_one] using
        (tendsto_realPWIntervalWeight_translation_ratio α s t hs).const_mul (‖φ t‖ ^ 2)
  apply hc.congr' (Eventually.of_forall fun x ↦ ?_)
  rw [← integral_const_mul, ← integral_add_left_eq_self (fun y : ℝ ↦
    realPWIntervalWeight α s x * (‖φ (y-x)‖ ^ 2 / realPWIntervalWeight α s y)) x]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by simp [packetDensity, div_eq_mul_inv, mul_comm, mul_assoc]

/-- Uniform leakage of normalized energy beyond the moving window of radius `R`. -/
theorem eventually_realPWIntervalWeight_packet_leakage {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ R : ℝ in atTop, ∀ x : ℝ, 4 ≤ x →
      realPWIntervalWeight α s x * (∫ y in {y : ℝ | R < |y-x|},
        ‖φ (y-x)‖ ^ 2 / realPWIntervalWeight α s y) < ε := by
  classical
  obtain ⟨g, hg, hg0, hb⟩ := packetDensity_bound ha hs φ
  let S (R : ℝ) := {t : ℝ | R < |t|}
  have hS (R : ℝ) : MeasurableSet (S R) := measurableSet_lt measurable_const continuous_abs.measurable
  have ht : Tendsto (fun R ↦ ∫ t, (S R).indicator g t) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) by simp]
    apply tendsto_integral_filter_of_dominated_convergence g
    · exact Eventually.of_forall fun R ↦ hg.aestronglyMeasurable.indicator (hS R)
    · apply Eventually.of_forall
      intro R
      exact ae_of_all _ fun t ↦ by by_cases h : t ∈ S R <;> simp [Set.indicator, h, Real.norm_of_nonneg (hg0 t), hg0 t]
    · exact hg
    · apply ae_of_all
      intro t
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop |t|] with R hR
      simp [S, Set.indicator, not_lt.mpr hR]
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with R hR
  intro x hx
  have hi := hg.mono' (packetDensity_meas α s φ x).aestronglyMeasurable (ae_of_all _ (hb x hx))
  have hdom := integral_mono (hi.indicator (hS R)) (hg.indicator (hS R))
    (show (S R).indicator (packetDensity α s φ x) ≤ (S R).indicator g from fun t ↦ by
      by_cases h : t ∈ S R
      · simp only [Set.indicator_of_mem h]; exact (le_abs_self _).trans (hb x hx t)
      · simp [Set.indicator, h])
  apply lt_of_eq_of_lt _ (hdom.trans_lt hR)
  let A := {y : ℝ | R < |y-x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (measurable_id.sub measurable_const))
  change realPWIntervalWeight α s x * (∫ y in A, _) = _
  rw [← integral_const_mul, ← integral_indicator hA, ← integral_add_left_eq_self
    (A.indicator (fun y : ℝ ↦ realPWIntervalWeight α s x * (‖φ (y-x)‖ ^ 2 / realPWIntervalWeight α s y))) x]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by by_cases ht : R < |t| <;>
    simp [Set.indicator, A, S, ht, packetDensity, div_eq_mul_inv, mul_assoc, mul_comm]

/-- A translated reciprocal-weight envelope controls the weighted squared norm of
band evaluation, by contractivity of projection of its ambient Riesz packet. -/
theorem realPWIntervalWeight_mul_evaluationVector_norm_sq_le
    (Y α s : ℝ) (hs : 0 ≤ s) (φ : SchwartzMap ℝ ℂ)
    (hone : EqOn (𝓕⁻ (φ : ℝ → ℂ)) 1 (Icc (-Y) Y))
    (G : ℝ → ℝ) (hG : MemLp G 2 volume) (x : ℝ)
    (henv : ∀ᵐ t ∂volume, Real.sqrt (realPWIntervalWeight α s x /
      realPWIntervalWeight α s (x + t)) * ‖φ t‖ ≤ G t) :
    realPWIntervalWeight α s x *
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x‖ ^ 2 ≤
      ∫ t, G t ^ 2 := by
  let w := realPWIntervalWeight α s
  have hw : Measurable w := measurable_realPWIntervalWeight α s
  have hw₁ : ∀ t, 1 ≤ w t := one_le_realPWIntervalWeight α s hs
  have hw₀ (t : ℝ) : 0 ≤ w t := zero_le_one.trans (hw₁ t)
  let hμ := volume_le_realPWIntervalMeasure α s hs
  obtain ⟨r, _, hproj, hr⟩ := RealPWBand.exists_evaluationVector_eq_projected_reproducer
    Y x hw hw₁ hμ φ.integrable (φ.memLp 2 volume) hone
  change w x * ‖RealPWBand.evaluationVector Y hμ x‖ ^ 2 ≤ _
  have hnorm := (RealPWBand.space Y hμ).norm_orthogonalProjectionOnto_apply_le r
  have hshift : (∫ t, ‖φ t‖ ^ 2 / w (x + t)) = ∫ z, ‖φ (z - x)‖ ^ 2 / w z := by
    simpa only [add_sub_cancel_left] using
      integral_add_left_eq_self (fun z ↦ ‖φ (z - x)‖ ^ 2 / w z) x
  let F (t : ℝ) := w x * (‖φ t‖ ^ 2 / w (x + t))
  have hF₀ (t : ℝ) : 0 ≤ F t := mul_nonneg (hw₀ x) (div_nonneg (sq_nonneg _) (hw₀ _))
  have hFG : ∀ᵐ t ∂volume, F t ≤ G t ^ 2 := by
    filter_upwards [henv] with t ht
    change Real.sqrt (w x / w (x + t)) * ‖φ t‖ ≤ G t at ht
    have hsq := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ht 2
    rw [mul_pow, Real.sq_sqrt (div_nonneg (hw₀ _) (hw₀ _))] at hsq
    simpa only [F, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hG₂ : Integrable (fun t ↦ G t ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hden : Measurable (fun t : ℝ ↦ w (x + t)) :=
    hw.comp (measurable_const.add measurable_id)
  have hnum : Measurable (fun t : ℝ ↦ ‖φ t‖ ^ 2 / w (x + t)) :=
    (φ.continuous.norm.measurable.pow_const 2).div hden
  have hFm : Measurable F := measurable_const.mul hnum
  have hFI : Integrable F volume := by
    apply hG₂.mono hFm.aestronglyMeasurable
    filter_upwards [hFG] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF₀ t), abs_of_nonneg (sq_nonneg (G t))] using ht
  calc
    w x * ‖RealPWBand.evaluationVector Y hμ x‖ ^ 2 ≤ w x * ‖r‖ ^ 2 := by
      have he := congrArg (fun v : RealPWBand.space Y hμ ↦ ‖v‖) hproj
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (he.le.trans hnorm) 2) (hw₀ x)
    _ = ∫ t, F t := by rw [hr, ← hshift, ← integral_const_mul]
    _ ≤ _ := integral_mono_ae hFI hG₂ hFG

/-- For the rational interval weight the translation envelope controls both evaluation
factors, so normalized two-window concentration suffices for two-sided decay. -/
theorem realPWSharpDensity_decay_of_twoWindowConcentration
    (Y α s : ℝ) (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) (g : ℝ) (hg : 1 < g)
    (hconcentration : ∀ ε > 0, ∃ R : ℝ, ∀ᶠ x in atTop,
      (∫ t in (Metric.closedBall x R ∪ Metric.closedBall (-x) R)ᶜ,
        realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) < ε) :
    ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R, ‖realPWSharpDensity Y α s hs g x‖ ≤ ε := by
  let w := realPWIntervalWeight α s
  let e := RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs)
  have hw (x : ℝ) : 0 < w x := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  have hg₀ := zero_lt_one.trans hg
  obtain ⟨φ, _, hone, _⟩ := exists_evenSchwartz_fourierInv_plateau Y 1 hY.le zero_lt_one
  obtain ⟨B, hB, henv⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  let G (t : ℝ) := B * (1 + |t|)⁻¹
  refine realPWSharpDensity_decay_of_concentration Y α s hs g hg φ G
    φ.continuous.aestronglyMeasurable hB hconcentration ?_ ?_ ?_ ?_
  · intro x
    exact RealPWBand.evaluation_reproduces Y (volume_le_realPWIntervalMeasure α s hs) _
      φ.integrable hone (g⁻¹ * x)
  · filter_upwards [eventually_ge_atTop (4 * g)] with x hx
    have hx' : 4 ≤ g⁻¹ * x := by
      rw [← div_eq_inv_mul]; exact (le_div_iff₀ hg₀).2 hx
    refine ae_of_all _ fun t ↦ ?_
    change Real.sqrt (w (g⁻¹ * x)) / Real.sqrt (w (g⁻¹ * x + t)) * ‖φ t‖ ≤ G t
    rw [← Real.sqrt_div (hw (g⁻¹ * x)).le (w (g⁻¹ * x + t))]
    rw [mul_comm]
    exact henv (g⁻¹ * x) hx' t
  · let a := g ^ (-(1 / 2 : ℝ))
    have hapos : 0 ≤ a := Real.rpow_nonneg hg₀.le _
    refine ⟨a * Real.sqrt (∫ t, G t ^ 2), mul_nonneg hapos (Real.sqrt_nonneg _), ?_⟩
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have h := Real.sqrt_le_sqrt (realPWIntervalWeight_mul_evaluationVector_norm_sq_le
      Y α s hs φ hone G hB x (ae_of_all _ fun t ↦ by rw [mul_comm]; exact henv x hx t))
    change Real.sqrt (w x * ‖e x‖ ^ 2) ≤ _ at h
    rw [Real.sqrt_mul (hw x).le, Real.sqrt_sq (norm_nonneg _)] at h
    change |Real.sqrt (w x) * (a * ‖e x‖)| ≤ _
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hapos (norm_nonneg _))),
      mul_left_comm]
    exact mul_le_mul_of_nonneg_left h hapos
  · let D := Real.exp (2 * |α * Real.log g⁻¹|) *
      (1 + |Real.log g⁻¹| + Real.log g⁻¹ ^ 2) ^ (s / 2)
    refine ⟨Real.sqrt D, Real.sqrt_nonneg _, Eventually.of_forall fun x ↦ ?_⟩
    change Real.sqrt (w x) / Real.sqrt (w (g⁻¹ * x)) ≤ Real.sqrt D
    rw [← Real.sqrt_div (hw _).le]
    exact Real.sqrt_le_sqrt ((div_le_iff₀ (hw _)).2
      (realPWIntervalWeight_le_dilation hs (inv_pos.mpr hg₀) x))

end RiemannMasullo.Isolated
