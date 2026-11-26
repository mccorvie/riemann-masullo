module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWRieszBounds
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Two-window concentration and off-diagonal decay of actual weighted evaluation -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology SchwartzMap

namespace RiemannMasullo.Isolated

private def outsidePair (x R : ℝ) : Set ℝ :=
  (Metric.closedBall x R ∪ Metric.closedBall (-x) R)ᶜ

private theorem outsidePair_meas (x R : ℝ) : MeasurableSet (outsidePair x R) :=
  (Metric.isClosed_closedBall.union Metric.isClosed_closedBall).measurableSet.compl

private theorem weighted_set_energy {α s : ℝ} (hs : 0 ≤ s) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) :
    (∫ t in S, f t ∂realPWIntervalMeasure α s) = ∫ t in S, realPWIntervalWeight α s t * f t := by
  have hw (t : ℝ) : 0 ≤ realPWIntervalWeight α s t := zero_le_one.trans (one_le_realPWIntervalWeight α s hs t)
  simpa only [realPWIntervalMeasure, Function.comp_apply, ENNReal.toReal_ofReal (hw _),
    smul_eq_mul] using
    setIntegral_withDensity_eq_setIntegral_toReal_smul (μ := volume)
      (ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight α s))
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) f hS

/-- The reciprocal representative itself is tight on the two physical windows. -/
private theorem reciprocal_twoWindow_leakage {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (he : ∀ t, φ (-t) = φ t)
    (r : ℝ → Lp ℂ 2 (realPWIntervalMeasure α s))
    (hr : ∀ x, ∀ᵐ t ∂volume, r x t = star ((2:ℂ)⁻¹ * (φ (t-x) + φ (t+x))) /
      (realPWIntervalWeight α s t : ℂ)) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ᶠ x in atTop, realPWIntervalWeight α s x *
      (∫ t in outsidePair x R, ‖r x t‖^2 ∂realPWIntervalMeasure α s) < η := by
  classical
  let w := realPWIntervalWeight α s
  have hw (t : ℝ) : 0 < w t := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs t)
  have hleak := eventually_realPWIntervalWeight_packet_leakage ha hs φ (show 0 < η/2 by linarith)
  obtain ⟨R,hR⟩ := hleak.exists
  refine ⟨R, ?_⟩
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx
  let D (a t : ℝ) := ‖φ (t+a)‖^2 / w t
  have hi (a : ℝ) : Integrable (D a) := by
    have h := (measurePreserving_add_right volume a).integrable_comp_of_integrable ((φ.memLp 2 volume).integrable_norm_pow (p := 2) (by norm_num))
    apply h.mono' (((φ.continuous.norm.measurable.comp (measurable_id.add measurable_const)).pow_const 2).div (measurable_realPWIntervalWeight α s)).aestronglyMeasurable
    exact ae_of_all _ fun t ↦ by
      change ‖‖φ (t+a)‖^2 / w t‖ ≤ ‖φ (t+a)‖^2
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hw _).le)]
      exact div_le_self (sq_nonneg _) (one_le_realPWIntervalWeight α s hs t)
  let A : Set ℝ := {t | R < |t-x|}
  let B : Set ℝ := {t | R < |t+x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((continuous_id.sub continuous_const).abs.measurable)
  have hB : MeasurableSet B := measurableSet_lt measurable_const ((continuous_id.add continuous_const).abs.measurable)
  have href : (∫ t in B, D x t) = ∫ t in A, D (-x) t := by
    rw [← integral_indicator hB, ← integral_indicator hA, ← integral_neg_eq_self (B.indicator (D x)) volume]
    apply integral_congr_ae
    exact ae_of_all _ fun t ↦ by
      have hneg : -t+x = -(t-x) := by ring
      have hwneg : w (-t) = w t := realPWIntervalWeight_even α s t
      simp only [A, B, D, Set.indicator, Set.mem_ofPred_eq, hneg, abs_neg, hwneg, he,
        ← sub_eq_add_neg]
  have hsubA : outsidePair x R ⊆ A := fun t ht ↦ by simpa [outsidePair,A,Metric.mem_closedBall,Real.dist_eq] using (not_or.mp ht).1
  have hsubB : outsidePair x R ⊆ B := fun t ht ↦ by simpa [outsidePair,B,Metric.mem_closedBall,Real.dist_eq] using (not_or.mp ht).2
  have hdom : (∫ t in outsidePair x R, ‖r x t‖^2 ∂realPWIntervalMeasure α s) ≤
      (∫ t in A, D (-x) t) + ∫ t in B, D x t := by
    rw [weighted_set_energy hs (outsidePair_meas ..)]
    have hint := (Lp.memLp (r x)).integrable_norm_pow (p := 2) (by norm_num)
    have hwi := (integrable_withDensity_iff_integrable_smul'
      (ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight α s))
      (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)).mp hint
    have hww (t : ℝ) :
        (ENNReal.ofReal (realPWIntervalWeight α s t)).toReal = realPWIntervalWeight α s t :=
      ENNReal.toReal_ofReal (zero_le_one.trans (one_le_realPWIntervalWeight α s hs t))
    simp only [Function.comp_apply, hww, smul_eq_mul] at hwi
    calc
      _ ≤ ∫ t in outsidePair x R, D (-x) t + D x t := by
        apply integral_mono_ae hwi.integrableOn ((hi _).add (hi _)).integrableOn
        filter_upwards [ae_restrict_of_ae (hr x)] with t ht
        change w t * ‖r x t‖^2 ≤ D (-x) t + D x t
        rw [ht, norm_div, norm_star, norm_mul, norm_inv, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw _)]
        dsimp only [D]; rw [← sub_eq_add_neg]
        have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (φ (t-x)) (φ (t+x))) 2
        rw [← add_div, show w t * ((2:ℝ)⁻¹ * ‖φ (t-x) + φ (t+x)‖ / w t)^2 =
          ((2:ℝ)⁻¹ * ‖φ (t-x) + φ (t+x)‖)^2 / w t by field_simp [(hw t).ne']]
        apply div_le_div_of_nonneg_right _ (hw t).le
        nlinarith [sq_nonneg (‖φ (t-x)‖ - ‖φ (t+x)‖), sq_nonneg ‖φ (t-x)‖, sq_nonneg ‖φ (t+x)‖]
      _ ≤ _ := by
        rw [integral_add (hi _).integrableOn (hi _).integrableOn]
        apply add_le_add
        · exact setIntegral_mono_set (hi _).integrableOn (ae_of_all _ fun t ↦ div_nonneg (sq_nonneg _) (hw t).le) (ae_of_all _ fun _ ht ↦ hsubA ht)
        · exact setIntegral_mono_set (hi _).integrableOn (ae_of_all _ fun t ↦ div_nonneg (sq_nonneg _) (hw t).le) (ae_of_all _ fun _ ht ↦ hsubB ht)
  rw [href] at hdom
  have hpos : w x * (∫ t in A, D (-x) t) < η/2 := by simpa [A,D,w,sub_eq_add_neg] using hR x hx
  have hh := mul_le_mul_of_nonneg_left hdom (hw x).le
  rw [mul_add] at hh
  linarith

/-- Near-minimizing reciprocal packets project to evaluation with vanishing relative
residual. The resulting concentration is for the physical normalized representative. -/
theorem realPWIntervalBand_twoWindowConcentration {Y α s : ℝ} (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s)
 :
    ∀ ε > 0, ∃ R : ℝ, ∀ᶠ x in atTop,
      (∫ t in (Metric.closedBall x R ∪ Metric.closedBall (-x) R)ᶜ,
        realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖^2) < ε := by
  have hlower (d : ℝ) (hd : 0 < d) : ∀ᶠ x in atTop, Y-d < realPWIntervalWeight α s x *
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x‖^2 :=
    eventually_lt_realPW_weighted_evalVector_sq hY ha hs (Y-d) (by linarith)
  intro ε hε
  let w := realPWIntervalWeight α s
  let μ := realPWIntervalMeasure α s
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let K := RealPWBand.space Y hμ
  let e := RealPWBand.evaluationVector Y hμ
  let d := ε*Y/32
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨φ,r,he,hopt,hr,hp,ht⟩ := exists_nearOptimal_realPWReciprocalProjection hY ha hs hd
  obtain ⟨R,hR⟩ := reciprocal_twoWindow_leakage ha hs φ he r hr hd
  refine ⟨R, ?_⟩
  filter_upwards [hR, hlower d hd, hlower (Y/2) (half_pos hY), (tendsto_order.mp ht).2 _ (lt_add_of_pos_right ((∫ t, ‖φ t‖^2)/2) hd)] with x htail hlow hhalf hupp
  let v := (e x).val
  let q := r x - v
  have hw : 0 < w x := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  have hdecomp := K.starProjection_add_starProjection_orthogonal (r x)
  have hv : K.starProjection (r x) = v := congrArg Subtype.val (hp x).symm
  rw [hv] at hdecomp
  have hq : q = Kᗮ.starProjection (r x) := sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hdecomp.symm)
  have hpy := Submodule.norm_sq_eq_add_norm_sq_projection (r x) K
  rw [← hp x] at hpy
  change ‖r x‖^2 = ‖e x‖^2 + ‖Kᗮ.starProjection (r x)‖^2 at hpy
  rw [← hq] at hpy
  have herr : w x * ‖q‖^2 < 3*d := by
    have hmul := congrArg (fun z : ℝ ↦ w x * z) hpy
    rw [mul_add] at hmul
    linarith
  let S := outsidePair x R
  have hsq (z : Lp ℂ 2 μ) : Integrable (fun t ↦ ‖z t‖^2) μ := (Lp.memLp z).integrable_norm_pow (by norm_num)
  have htbound : (∫ t in S, ‖v t‖^2 ∂μ) ≤ 2 * ((∫ t in S, ‖r x t‖^2 ∂μ) + ‖q‖^2) := by
    have hmono : (∫ t in S, ‖v t‖^2 ∂μ) ≤ ∫ t in S, 2*(‖r x t‖^2 + ‖q t‖^2) ∂μ := by
      apply integral_mono_ae (hsq v).integrableOn (((hsq _).add (hsq q)).const_mul 2).integrableOn
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (r x) v)] with t ht
      change q t = r x t - v t at ht
      have hh : v t = r x t - q t := by rw [ht]; abel
      have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (r x t) (q t)) 2
      rw [← hh] at hb
      change ‖v t‖^2 ≤ 2 * (‖r x t‖^2 + ‖q t‖^2)
      nlinarith [sq_nonneg (‖r x t‖ - ‖q t‖)]
    rw [integral_const_mul, integral_add (hsq _).integrableOn (hsq q).integrableOn] at hmono
    have hh := setIntegral_le_integral (s := S) (hsq q) (ae_of_all _ fun t ↦ sq_nonneg _)
    rw [L2.integral_sq_norm (𝕜 := ℂ)] at hh
    linarith
  have hraw := mul_le_mul_of_nonneg_left htbound hw.le
  have hscaled : w x * (∫ t in S, ‖v t‖^2 ∂μ) < ε * (w x * ‖e x‖^2) := by
    have hh : ε*(Y/2) < ε*(w x * ‖e x‖^2) := mul_lt_mul_of_pos_left (by linarith only [hhalf]) hε
    dsimp only [d] at herr htail
    nlinarith only [hh,hraw,herr,htail,mul_pos hε hY]
  have hnorm : 0 < ‖e x‖^2 := by by_contra! hh; have := mul_nonpos_of_nonneg_of_nonpos hw.le hh; linarith only [this,hhalf,hY]
  have hphys := RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) (e x)
  have hrep : (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖^2) =ᵐ[μ] (fun t ↦ (‖e x‖^2)⁻¹ * ‖v t‖^2) := by
    filter_upwards [hphys] with t ht
    simp only [realPWNormalizedEval,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),mul_pow,inv_pow]
    rw [ht]
  change (∫ t in S, realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖^2) < ε
  rw [← weighted_set_energy (α := α) hs (outsidePair_meas x R)
    (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖^2),
    integral_congr_ae (ae_restrict_of_ae hrep), integral_const_mul]
  rw [← div_eq_inv_mul, div_lt_iff₀ hnorm]
  exact (mul_lt_mul_iff_right₀ hw).mp (by simpa only [mul_left_comm] using hscaled)

/-- The actual real sharp density tends to zero at both ends for a fixed dilation. -/
theorem realPWSharpDensity_decay {Y α s g : ℝ} (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s)
    (hg : 1 < g) : ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R,
      ‖realPWSharpDensity Y α s hs g x‖ ≤ ε :=
  realPWSharpDensity_decay_of_twoWindowConcentration Y α s hY ha hs g hg
    (realPWIntervalBand_twoWindowConcentration hY ha hs)

end RiemannMasullo.Isolated
