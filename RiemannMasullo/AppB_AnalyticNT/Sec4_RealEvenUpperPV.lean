module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The real Connes–Weil principal value above dilation one

The two signs of the Tamagawa real coordinate give the even orbital density.
Their average uses the ordinary principal-value formula of Appendix B.4.4 and
the self-dual real-place measure of Appendix A.3.2.
-/

open Classical Filter Function MeasureTheory NumberField Set
open scoped NNReal ENNReal Topology CompactlySupported

@[expose] public noncomputable section

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

/-- In the isometric real chart the multiplicative Tamagawa measure is `dt / |t|`. -/
private theorem realTamagawa_integral_chart (w : InfinitePlace F) (hw : w.IsReal)
    (g : ℝ → ℂ) :
    (∫ u : w.Completionˣ, g (InfinitePlace.Completion.ringEquivRealOfIsReal hw u.val)
      ∂infiniteLocalMultiplicativeTamagawaMeasure F w) =
      ∫ t : ℝ, |t|⁻¹ • g t := by
  let : MeasurableSpace w.Completion := instMeasurableSpaceCompletion_riemannMasullo F w
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  let d : w.Completion → ENNReal := fun x ↦ (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
  have hfin : ∀ᵐ x ∂(infiniteLocalAdditiveTamagawaMeasure F w).restrict
      (range (Units.val : w.Completionˣ → w.Completion)), d x < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp only [d, hm, pow_one]
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  change (∫ u : w.Completionˣ, g (e u.val)
    ∂((infiniteLocalAdditiveTamagawaMeasure F w).withDensity d).comap Units.val) = _
  rw [← hval.integral_map (g := fun z ↦ g (e z)), hval.map_comap,
    setIntegral_withDensity_eq_setIntegral_toReal_smul hd hfin _ hval.measurableSet_range]
  simp only [d, hm, pow_one, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := range (Units.val :
    w.Completionˣ → w.Completion)) (fun y hy ↦ by
      have hy0 : y = 0 := by
        by_contra hne
        exact hy ⟨Units.mk0 y hne, rfl⟩
      simp [hy0])]
  rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw,
    show (e.symm : ℝ → w.Completion) = m from rfl, integral_map_equiv]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  have hn : ‖m t‖ = |t| := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) t
  change ‖m t‖⁻¹ • g (e (e.symm t)) = |t|⁻¹ • g t
  rw [hn, e.apply_symm_apply]

/-- The definition of positive real Haar measure gives the elementary density `da/a`. -/
private theorem positiveRealHaar_integral_chart (g : ℝ → ℂ) (hg : Measurable g) :
    (∫ a : ℝ≥0ˣ, g (a.val : ℝ) ∂positiveRealHaar) =
      ∫ t in Ioi (0 : ℝ), t⁻¹ • g t := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hval : Measurable (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)) :=
    NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap
  change (∫ a : ℝ≥0ˣ, g (a.val : ℝ) ∂volume.map e) = _
  have hg' : AEStronglyMeasurable (fun a : ℝ≥0ˣ ↦ g (a.val : ℝ)) (volume.map e) :=
    (hg.comp hval).aestronglyMeasurable
  rw [integral_map he.aemeasurable hg']
  change (∫ x : ℝ, g ((Real.exp x).toNNReal : ℝ)) = _
  simp_rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  rw [← integral_comp_log_Ioi_zero (fun x ↦ g (Real.exp x))]
  exact setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ by rw [Real.exp_log ha]

private def signedRealDensity (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  |x|⁻¹ • (f |x| * (Real.sqrt |x| : ℂ) / ((|1 - x| : ℝ) : ℂ))

private def upperRealWeight (a : ℝ) : ℝ := a * Real.sqrt a / (a ^ 2 - 1)

private theorem signedRealDensity_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) {c : ℝ} (hc1 : 1 < c)
    (hz : ∀ a, a < c → f a = 0) : Integrable (signedRealDensity f) := by
  have hcont : Continuous (signedRealDensity f) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : |x| < c
    · refine (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [continuous_abs.continuousAt.eventually (Iio_mem_nhds hx)] with y hy
      simp [signedRealDensity, hz _ hy]
    · have hx0 : |x| ≠ 0 := by linarith [le_of_not_gt hx]
      have hx1 : |1 - x| ≠ 0 := by
        intro h
        have he : x = 1 := (sub_eq_zero.mp (abs_eq_zero.mp h)).symm
        simp [he] at hx
        linarith
      unfold signedRealDensity
      fun_prop (disch := first | assumption | exact_mod_cast hx1)
  apply hcont.integrable_of_hasCompactSupport
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  change IsCompact (closure (support (signedRealDensity f)))
  apply (isCompact_Icc (a := -R) (b := R)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hfx : f |x| ≠ 0 := by
    intro h
    exact hx (by simp [signedRealDensity, h])
  have h := hR |x| (subset_tsupport _ (mem_support.mpr hfx))
  exact abs_le.mp (by simpa [Real.norm_eq_abs] using h)

private theorem signedRealDensity_fold {f : ℝ → ℂ} {c : ℝ} (hc : 1 < c)
    (hz : ∀ a, a < c → f a = 0) {t : ℝ} (ht : 0 < t) :
    (1 / 2 : ℂ) * (signedRealDensity f t + signedRealDensity f (-t)) =
      t⁻¹ • (f t * (upperRealWeight t : ℂ)) := by
  by_cases ht1 : 1 < t
  · have hn : 1 - t < 0 := by linarith
    have hp : 0 < 1 + t := by linarith
    simp only [signedRealDensity, abs_neg, abs_of_pos ht, abs_of_neg hn, abs_of_pos hp,
      upperRealWeight, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_one, sub_neg_eq_add]
    have hc0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hc1 : (1 : ℂ) - t ≠ 0 := by exact_mod_cast hn.ne
    have hc2 : (1 : ℂ) + t ≠ 0 := by exact_mod_cast (by linarith : 0 < 1 + t).ne'
    have hc3 : (t : ℂ) ^ 2 - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith : 0 < t ^ 2 - 1).ne'
    field_simp
    ring
  · have h := hz t (lt_of_le_of_lt (le_of_not_gt ht1) hc)
    simp [signedRealDensity, abs_of_pos ht, h]

private theorem integral_fold_real (D : ℝ → ℂ) (hint : Integrable D) :
    (∫ t : ℝ, D t) = ∫ t in Ioi (0 : ℝ), D t + D (-t) := by
  have hnint : Integrable (fun x : ℝ ↦ D (-x)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hint
  have hneg : (∫ x in (Ioi (0 : ℝ))ᶜ, D x) = ∫ x in Ioi (0 : ℝ), D (-x) := by
    simpa only [compl_Ioi, neg_zero] using (integral_comp_neg_Ioi 0 D).symm
  calc
    _ = (∫ t in Ioi (0 : ℝ), D t) + ∫ t in (Ioi (0 : ℝ))ᶜ, D t :=
      (integral_add_compl measurableSet_Ioi hint).symm
    _ = (∫ t in Ioi (0 : ℝ), D t) + ∫ t in Ioi (0 : ℝ), D (-t) := congrArg (_ + ·) hneg
    _ = _ := (integral_add hint.integrableOn hnint.integrableOn).symm

private theorem upperRealWeight_measurable : Measurable (fun t : ℝ ↦ (upperRealWeight t : ℂ)) := by
  unfold upperRealWeight
  fun_prop

private theorem signedRealDensity_integral_fold (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) {c : ℝ} (hc1 : 1 < c) (hz : ∀ a, a < c → f a = 0) :
    (1 / 2 : ℂ) * (∫ t : ℝ, signedRealDensity f t) =
      ∫ a : ℝ≥0ˣ, f (a.val : ℝ) * (upperRealWeight (a.val : ℝ) : ℂ) ∂positiveRealHaar := by
  let D := signedRealDensity f
  let W (t : ℝ) : ℂ := f t * (upperRealWeight t : ℂ)
  have hint : Integrable D := signedRealDensity_integrable hf hc hc1 hz
  have hW : Measurable W := hf.measurable.mul upperRealWeight_measurable
  calc
    _ = (1 / 2 : ℂ) * (∫ t in Ioi (0 : ℝ), D t + D (-t)) :=
      congrArg ((1 / 2 : ℂ) * ·) (integral_fold_real D hint)
    _ = ∫ t in Ioi (0 : ℝ), (1 / 2 : ℂ) * (D t + D (-t)) :=
      (integral_const_mul (μ := volume.restrict (Ioi (0 : ℝ))) (1 / 2 : ℂ)
        (fun t ↦ D t + D (-t))).symm
    _ = ∫ t in Ioi (0 : ℝ), t⁻¹ • W t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ signedRealDensity_fold hc1 hz ht)
    _ = _ := (positiveRealHaar_integral_chart W hW).symm

/-- Paper: Definition B.4.4.1 and (B.4.4.4), p. 620. At every real place the two signs
of a radius above one give the folded density `a * √a / (a² - 1)` against positive real Haar. -/
theorem realConnesWeilPrincipalValue_eq_upper_realHaar (w : InfinitePlace F) (hw : w.IsReal)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    {c : ℝ} (hc1 : 1 < c) (hz : ∀ a, a < c → f a = 0)
    (test : BruhatCompactSupport w.Completionˣ) (hrad : ∀ u, test.val u = f ‖u.val‖) :
    infiniteConnesWeilPrincipalValue w test =
      ∫ a : ℝ≥0ˣ, f (a.val : ℝ) *
        (((a.val : ℝ) * Real.sqrt (a.val : ℝ) / ((a.val : ℝ) ^ 2 - 1) : ℝ) : ℂ)
        ∂positiveRealHaar := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let g (t : ℝ) : ℂ := f |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ)
  have hn (y : w.Completion) : |e y| = ‖y‖ :=
    j.isometry.norm_map_of_map_zero (map_zero e) y
  have h1 : test.val 1 = 0 := by
    rw [hrad]
    change f ‖(1 : w.Completion)‖ = 0
    rw [norm_one]
    exact hz 1 hc1
  have heq (u : w.Completionˣ) :
      test.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) = g (e u.val) := by
    have hn' : |1 - e u.val| = ‖1 - u.val‖ := by
      simpa only [map_sub, map_one] using hn (1 - u.val)
    change test.val u * _ / _ = f |e u.val| * _ / _
    rw [hrad, hn, hn']
  refine (realConnesWeilPrincipalValue_of_apply_one_zero w hw test h1).trans ?_
  refine Eq.trans (congrArg ((1 / 2 : ℂ) * ·) ?_) (signedRealDensity_integral_fold f hf hc hc1 hz)
  exact (integral_congr_ae (.of_forall heq)).trans (realTamagawa_integral_chart w hw g)

/-- A compact positive-ray profile supported above one extends to a compactly supported
continuous function on the real line. The cutoff at one lies below its support. -/
private theorem exists_upperProfile_extension (H : C_c(ℝ≥0ˣ, ℂ)) {c : ℝ} (hc : 1 < c)
    (hz : ∀ a : ℝ≥0ˣ, (a.val : ℝ) < c → H a = 0) :
    ∃ f : ℝ → ℂ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, x < c → f x = 0) ∧ ∀ a : ℝ≥0ˣ, f (a.val : ℝ) = H a := by
  let lift (x : ℝ) : ℝ≥0ˣ := (Nonneg.unitsHomeomorphPos ℝ).symm
    ⟨max 1 x, lt_of_lt_of_le zero_lt_one (le_max_left _ _)⟩
  have hval (x : ℝ) : ((lift x).val : ℝ) = max 1 x := rfl
  have hcont : Continuous lift :=
    (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp
      ((continuous_const.max continuous_id).subtype_mk _)
  have hzero (x : ℝ) (hx : x < c) : H (lift x) = 0 :=
    hz (lift x) (show max 1 x < c from max_lt hc hx)
  refine ⟨fun x ↦ H (lift x), H.continuous.comp hcont, ?_, hzero, ?_⟩
  · let K : Set ℝ := (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)) '' tsupport (H : ℝ≥0ˣ → ℂ)
    have hK : IsCompact K := H.hasCompactSupport'.image
      (NNReal.continuous_coe.comp Units.continuous_val)
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    have hx1 : 1 ≤ x := by
      by_contra! h
      exact hx (hzero x (h.trans hc))
    exact ⟨lift x, subset_tsupport _ hx, (hval x).trans (max_eq_right hx1)⟩
  · intro a
    by_cases h : 1 ≤ (a.val : ℝ)
    · have he : lift (a.val : ℝ) = a := by
        apply Units.ext
        apply NNReal.eq
        exact (hval _).trans (max_eq_right h)
      exact congrArg H he
    · have h' := (lt_of_not_ge h).trans hc
      exact (hzero _ h').trans (hz a h').symm

/-- The literal real Connes–Weil principal value for an upper compact radial profile.
The same real radius parametrizes the Bruhat test and the compact positive-ray test. -/
theorem realConnesWeilPrincipalValue_eq_upper_compactProfile
    (w : InfinitePlace F) (hw : w.IsReal) (H : C_c(ℝ≥0ˣ, ℂ))
    {c : ℝ} (hc : 1 < c) (hz : ∀ a : ℝ≥0ˣ, (a.val : ℝ) < c → H a = 0)
    (test : BruhatCompactSupport w.Completionˣ)
    (hprofile : ∀ (u : w.Completionˣ) (a : ℝ≥0ˣ), (a.val : ℝ) = ‖u.val‖ → test.val u = H a) :
    infiniteConnesWeilPrincipalValue w test =
      ∫ a : ℝ≥0ˣ, H a *
        (((a.val : ℝ) * Real.sqrt (a.val : ℝ) / ((a.val : ℝ) ^ 2 - 1) : ℝ) : ℂ)
        ∂positiveRealHaar := by
  obtain ⟨g, hg, hgc, hgz, he⟩ := exists_upperProfile_extension H hc hz
  have htest (u : w.Completionˣ) : test.val u = g ‖u.val‖ := by
    let a := (Nonneg.unitsHomeomorphPos ℝ).symm ⟨‖u.val‖, norm_pos_iff.mpr u.ne_zero⟩
    exact (hprofile u a rfl).trans (he a).symm
  simpa only [he] using
    realConnesWeilPrincipalValue_eq_upper_realHaar w hw g hg hgc hc hgz test htest

end RiemannMasullo
