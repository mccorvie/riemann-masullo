module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWWeightEstimates
public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerJetTrial
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Actual weighted Schwartz trials for the rational real band -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap

namespace RiemannMasullo.Isolated

/-- An even Schwartz function is in the interval-weighted band ambient space as
soon as its order at zero compensates for the possible density singularity. -/
theorem memLp_realPWIntervalMeasure_of_evenSchwartz_order {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (he : Function.Even (φ : ℝ → ℂ)) (k : ℕ)
    (hk : -1 < (↑(2*k) : ℝ) - 2*α)
    (hlocal : ∃ C : ℝ, ∀ x : ℝ, |x| ≤ 4 → ‖φ x‖ ≤ C * |x| ^ k) :
    MemLp (φ : ℝ → ℂ) 2 (realPWIntervalMeasure α s) := by
  let w := realPWIntervalWeight α s
  let F (x : ℝ) := w x * ‖φ x‖ ^ 2
  let S : Set ℝ := Icc (-4) 4
  have hS : MeasurableSet S := measurableSet_Icc
  have hw (x : ℝ) : 0 ≤ w x := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  have hF₀ (x : ℝ) : 0 ≤ F x := mul_nonneg (hw x) (sq_nonneg _)
  have hm : Measurable F :=
    (measurable_realPWIntervalWeight α s).mul (φ.continuous.norm.pow 2).measurable
  obtain ⟨C, hC⟩ := hlocal
  have hI : IntegrableOn F S := by
    have hP : IntegrableOn (fun x : ℝ ↦ |x| ^ (2*k) * w x) S := by
      simpa only [Real.rpow_natCast] using integrableOn_abs_rpow_mul_realPWIntervalWeight
        (R := 4) ha hs hk
    apply (hP.const_mul (C^2)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [Real.norm_of_nonneg (hF₀ x)]
    calc
      F x ≤ w x * (C * |x| ^ k) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hC x (abs_le.mpr hx)) 2) (hw x)
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm k 2]; ring
  obtain ⟨B, hB, hb⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  have hT : IntegrableOn F Sᶜ := by
    apply hB.integrable_sq.integrableOn.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS.compl] with x hx
    have hx4 : 4 ≤ |x| := by by_contra! h; exact hx (abs_le.mp h.le)
    have hnorm : φ (-|x|) = φ x := by
      rcases le_total 0 x with h|h
      · rw [abs_of_nonneg h, he]
      · rw [abs_of_nonpos h, neg_neg]
    have hweight : w |x| = w x := by simp [w, realPWIntervalWeight]
    have h0 : w 0 = 1 := by simp [w, realPWIntervalWeight]
    have h := hb |x| hx4 (-|x|)
    change ‖φ (-|x|)‖ * Real.sqrt (w |x| / w (|x| + -|x|)) ≤ B * (1 + |-(|x|)|)⁻¹ at h
    rw [hnorm, add_neg_cancel, h0, div_one, hweight, abs_neg, abs_abs] at h
    have hh := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) h 2
    rw [mul_pow, Real.sq_sqrt (hw x), mul_comm] at hh
    rwa [Real.norm_of_nonneg (hF₀ x)]
  have hF : Integrable F := by
    simpa only [union_compl_self, integrableOn_univ] using (integrableOn_union.mpr ⟨hI, hT⟩)
  let ρ (x : ℝ) := ENNReal.ofReal (w x)
  have hρ : Measurable ρ := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hρf : ∀ᵐ x ∂volume, ρ x < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  apply (memLp_two_iff_integrable_sq_norm φ.continuous.aestronglyMeasurable).2
  change Integrable (fun x ↦ ‖φ x‖^2) (volume.withDensity ρ)
  exact (integrable_withDensity_iff_integrable_smul' hρ hρf).2
    (hF.congr (ae_of_all _ fun x ↦ by simp only [F, ρ, ENNReal.toReal_ofReal (hw x), smul_eq_mul]))

/-- The normalized translated jet trial has finite norm in the actual interval weight. -/
theorem memLp_translatedJetTrial_realPWIntervalMeasure {α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (he : Function.Even (φ : ℝ → ℂ))
    (x : ℝ) (n : ℕ) (hn : -1 < (↑(4*n) : ℝ) - 2*α) :
    MemLp (RealPWBand.translatedJetTrial φ x n : ℝ → ℂ) 2 (realPWIntervalMeasure α s) := by
  have hn' : -1 < (↑(2 * (2*n)) : ℝ) - 2*α := by push_cast at hn ⊢; linarith
  apply memLp_realPWIntervalMeasure_of_evenSchwartz_order ha hs _
    (RealPWBand.translatedJetTrial_even φ he x n) (2*n) hn'
  let B := SchwartzMap.seminorm ℝ 0 0 φ
  refine ⟨(|x|⁻¹) ^ (2*n) * (2*B), fun t _ ↦ ?_⟩
  rw [RealPWBand.translatedJetTrial_apply, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_div, div_eq_mul_inv, mul_pow]
  have hpair : ‖φ (t-x) + φ (t+x)‖ ≤ 2*B :=
    (norm_add_le _ _).trans ((add_le_add (φ.norm_le_seminorm ℝ _) (φ.norm_le_seminorm ℝ _)).trans_eq
      (two_mul B).symm)
  exact (mul_le_mul_of_nonneg_left hpair (by positivity)).trans_eq (by ring)

/-- Every even coordinate monomial of allowable degree times an even Schwartz
band function is realized in the actual weighted band. -/
theorem exists_realPWInterval_coordinateTrial {Y α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (he : Function.Even (φ : ℝ → ℂ))
    (hφ : ∀ t ∉ Icc (-Y) Y, (𝓕 φ) t = 0)
    (n : ℕ) (hn : -1 < (↑(4*n) : ℝ) - 2*α) :
    ∃ f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs), ∀ t : ℝ,
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) t f = t ^ (2*n) • φ t := by
  obtain ⟨ψ, hψ, hband⟩ := RealPWBand.exists_coordinatePowerSchwartz Y φ (2*n) hφ
  have heven : Function.Even (ψ : ℝ → ℂ) := fun t ↦ by
    simp only [hψ, he t, (even_two.mul_right n).neg_pow]
  have hn' : -1 < (↑(2 * (2*n)) : ℝ) - 2*α := by push_cast at hn ⊢; linarith
  have hmem : MemLp (ψ : ℝ → ℂ) 2 (realPWIntervalMeasure α s) := by
    apply memLp_realPWIntervalMeasure_of_evenSchwartz_order ha hs ψ heven (2*n) hn'
    refine ⟨SchwartzMap.seminorm ℝ 0 0 φ, fun t _ ↦ ?_⟩
    rw [hψ, norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (φ.norm_le_seminorm ℝ t) (pow_nonneg (abs_nonneg _) _)
  obtain ⟨f, hf⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y ψ heven hband
    (volume_le_realPWIntervalMeasure α s hs) hmem
  exact ⟨f, fun t ↦ (congrFun hf t).trans (hψ t)⟩

/-- The norm of the actual band vector is the density-weighted integral of the
squared norm of its canonical pointwise representative. -/
theorem realPWInterval_norm_sq_eq_weighted_evaluation (Y α s : ℝ) (hs : 0 ≤ s)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    ‖f‖ ^ 2 = ∫ t, realPWIntervalWeight α s t *
      ‖RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) t f‖ ^ 2 := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e (t : ℝ) := RealPWBand.evaluation Y hμ t f
  let ρ (t : ℝ) := ENNReal.ofReal (realPWIntervalWeight α s t)
  have hρ : Measurable ρ := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hρf : ∀ᵐ t ∂volume, ρ t < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hρw (t : ℝ) : (ρ t).toReal = realPWIntervalWeight α s t :=
    ENNReal.toReal_ofReal (zero_le_one.trans (one_le_realPWIntervalWeight α s hs t))
  have he : (fun t ↦ ‖f.val t‖ ^ 2) =ᵐ[realPWIntervalMeasure α s] fun t ↦ ‖e t‖ ^ 2 :=
    (RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) f).symm.mono
      fun _ ht ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) ht
  change ‖f.val‖ ^ 2 = _
  rw [← L2.integral_sq_norm (𝕜 := ℂ), integral_congr_ae he]
  change (∫ t, ‖e t‖ ^ 2 ∂volume.withDensity ρ) = _
  rw [integral_withDensity_eq_integral_toReal_smul hρ hρf]
  simp only [hρw, smul_eq_mul, e]

end RiemannMasullo.Isolated
