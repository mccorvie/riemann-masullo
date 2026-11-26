module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RatEmptyTraceThroughOne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Finite part of the actual real Haar compression trace across norm one

Subtract the logarithm contributed by the direct band at the identity. The
reflected band and polar rank-one subtraction retain their ordinary limits.
The spatial floor contributes zero whenever its size times the band tends to zero.
-/

public noncomputable section

open Real Set Filter MeasureTheory Topology

namespace RiemannMasullo

/-- Sine integral at the rescaled phase (`c = 2πδ` for the seam reference). -/
private def seamSi (c x : ℝ) : ℝ := ∫ t in (0 : ℝ)..(c*x), sinc t

private theorem seamSi_cont (c : ℝ) : Continuous (seamSi c) :=
  continuous_integral_sinc.comp (continuous_const.mul continuous_id)

/-- The apparent singularity at zero has an absolutely integrable majorant. -/
private theorem seamSi_head_integrable {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x ↦ seamSi c x / x) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Integrable.mono' (integrable_const c) ((seamSi_cont c).measurable.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx' : 0 < x := lt_of_le_of_lt ha hx.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := c*x)
    (f := sinc) (C := 1) fun y _ ↦ by simpa using abs_sinc_le_one y
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx', div_le_iff₀ hx']
  simpa [seamSi, abs_of_pos (mul_pos hc hx')] using h

/-- Absolute convergence after subtracting the limiting sine integral on the tail. -/
private theorem seamSi_tail_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x ↦ (seamSi c x - π/2) / x) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
    (c := 1) zero_lt_one).const_mul (2/c))
    (((seamSi_cont c).measurable.sub measurable_const).div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := lt_trans zero_lt_one hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx', Real.rpow_neg hx'.le, Real.rpow_two]
  calc |seamSi c x - π/2| / x ≤ (2/(c*x))/x :=
         div_le_div_of_nonneg_right (abs_integral_sinc_sub_le (mul_pos hc hx')) hx'.le
    _ = (2/c) * (x^2)⁻¹ := by field_simp [hc.ne', hx'.ne']

/-- Finite part of the post-Fubini singular contribution for a reference interval.
Both integrals in the constant converge absolutely. -/
private theorem tendsto_seamSi_reference {δ : ℝ} (hδ : 0 < δ) :
    let c := 2 * π * δ
    Tendsto (fun R ↦ (2/π) * (∫ x in (0 : ℝ)..R, seamSi c x / x) - log R) atTop
      (𝓝 ((2/π) * ((∫ x in (0 : ℝ)..1, seamSi c x / x) +
        ∫ x in Ioi (1 : ℝ), (seamSi c x - π/2) / x))) := by
  let c := 2 * π * δ
  change Tendsto (fun R ↦ (2/π) * (∫ x in (0 : ℝ)..R, seamSi c x / x) - log R) _ _
  have hc : 0 < c := by dsimp [c]; positivity
  have ht := intervalIntegral_tendsto_integral_Ioi 1 (seamSi_tail_integrable hc) tendsto_id
  apply ((ht.const_add (∫ x in (0 : ℝ)..1, seamSi c x / x)).const_mul (2/π)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have h0 := seamSi_head_integrable hc (a := 0) (b := 1) le_rfl zero_le_one
  have h1 := seamSi_head_integrable hc zero_le_one hR
  have hi : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact (lt_of_lt_of_le zero_lt_one hx.1).ne'
  have hsplit : (∫ x in (1 : ℝ)..R, (seamSi c x - π/2) / x) =
      (∫ x in (1 : ℝ)..R, seamSi c x / x) - π/2 * log R := by
    simp_rw [sub_div, show ∀ x : ℝ, π/2/x = (π/2)*x⁻¹ from fun x ↦ div_eq_mul_inv _ _]
    rw [intervalIntegral.integral_sub h1 (hi.const_mul _), intervalIntegral.integral_const_mul,
      integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hR), div_one]
  dsimp only [id_eq]
  rw [hsplit, ← intervalIntegral.integral_add_adjacent_intervals h0 h1]
  field_simp [Real.pi_ne_zero]; ring

end RiemannMasullo

open Real Set MeasureTheory

namespace RiemannMasullo

private theorem integral_centralPhase_slice (δ x : ℝ) (hx : 0 < x) :
    (∫ c in (-δ)..δ, realBandKernel 1 (c*x)) = (2/π) * (seamSi (2*π*δ) x / x) := by
  let f : ℝ → ℝ := fun c ↦ realBandKernel 1 (c*x)
  have hf : Continuous f := (continuous_realBandKernel 1).comp (continuous_id.mul continuous_const)
  have he : ∀ c, f (-c) = f c := fun c ↦ by simp [f, realBandKernel, neg_mul, mul_neg, sinc_neg]
  have hneg : (∫ c in (-δ)..0, f c) = ∫ c in (0:ℝ)..δ, f c := by
    simpa only [he, neg_zero] using (intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := δ) f).symm
  have hpoint : ∀ c, f c = 2 * sinc (c * (2*π*x)) := fun c ↦ by
    simp only [f, realBandKernel, mul_one]; congr 2; ring
  change (∫ c in (-δ)..δ, f c) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-δ) 0)
    (hf.intervalIntegrable 0 δ), hneg]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_right sinc
    (show 2*π*x ≠ 0 by positivity), zero_mul, smul_eq_mul,
    show δ*(2*π*x) = (2*π*δ)*x by ring]
  unfold seamSi
  field_simp [pi_ne_zero, hx.ne']; ring

/-- The finite central phase integral before Fubini equals the log-centered reference's
unsubtracted sine integral. The interval-integral comparison excludes the endpoint zero. -/
private theorem integral_centralPhase_reference {δ R : ℝ} (_hδ : 0 < δ) (hR : 0 < R) :
    (∫ c in (-δ)..δ, ∫ x in (0:ℝ)..R, realBandKernel 1 (c*x)) =
      (2/π) * ∫ x in (0:ℝ)..R, seamSi (2*π*δ) x / x := by
  have hF : Continuous (Function.uncurry fun c x : ℝ ↦ realBandKernel 1 (c*x)) :=
    (continuous_realBandKernel 1).comp (continuous_fst.mul continuous_snd)
  rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
    ((hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x
  rw [uIoc_of_le hR.le]
  exact fun hx ↦ integral_centralPhase_slice δ x hx.1

end RiemannMasullo

open Real Set Filter MeasureTheory Topology

namespace RiemannMasullo

/-- The central phase, with the harmless totalized value zero at `c = 0`. -/
private def flatSeamKernel (R c : ℝ) : ℝ :=
  (π * c)⁻¹ * ∫ t in (0 : ℝ)..(2 * π * c * R), sinc t

private theorem flatSeam_meas (R : ℝ) : Measurable (flatSeamKernel R) := by
  exact ((measurable_const.mul measurable_id).inv).mul
    (continuous_integral_sinc.measurable.comp (by fun_prop))

private theorem flatSeam_lim (c : ℝ) : Tendsto (fun R ↦ flatSeamKernel R c) atTop
    (𝓝 ((2 * |c|)⁻¹)) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have h := (tendsto_integral_sinc_mul_of_neg (R := id) tendsto_id
        (c := 2 * π * c) (mul_neg_of_pos_of_neg (by positivity) hc)).const_mul ((π*c)⁻¹)
    have e : (π*c)⁻¹ * (-(π/2)) = (2 * |c|)⁻¹ := by
      rw [abs_of_neg hc]; field_simp [pi_ne_zero, hc.ne]
    rw [e] at h
    exact h
  · simp [flatSeamKernel]
  · have h := (tendsto_integral_sinc_mul_of_pos (R := id) tendsto_id
        (c := 2 * π * c) (by positivity)).const_mul ((π*c)⁻¹)
    have e : (π*c)⁻¹ * (π/2) = (2 * |c|)⁻¹ := by
      rw [abs_of_pos hc]; field_simp [pi_ne_zero, hc.ne']
    rw [e] at h
    exact h

private theorem flatSeam_integrable (R a b : ℝ) : IntervalIntegrable (flatSeamKernel R) volume a b := by
  rw [intervalIntegrable_iff]
  refine Integrable.mono' (intervalIntegrable_const (c := 2 * |R|) (a := a) (b := b)).def'
    (flatSeam_meas R).aestronglyMeasurable ?_
  refine Eventually.of_forall fun c ↦ ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp [flatSeamKernel, abs_nonneg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
    (b := 2 * π * c * R) (f := sinc) (C := 1) fun t _ ↦ by simpa using abs_sinc_le_one t
  have hpc : 0 < π * |c| := mul_pos pi_pos (abs_pos.mpr hc)
  rw [flatSeamKernel, norm_mul, Real.norm_eq_abs, abs_inv, abs_mul, abs_of_pos pi_pos,
    inv_mul_eq_div, div_le_iff₀ hpc]
  calc _ ≤ |2 * π * c * R| := by simpa using hb
       _ = _ := by simp [abs_mul, abs_of_pos pi_pos]; ring

variable {δ L : ℝ} {w : ℝ → ℝ}

private theorem flatSeam_rem_bound (hδ : 0 < δ)
    (hw : ∀ c ∈ Icc (-δ) δ, |w c - w 0| ≤ L * |c|) (R : ℝ) {c : ℝ} (hc : c ∈ uIoc (-δ) δ) :
    ‖(w c - w 0) * flatSeamKernel R c‖ ≤ L * (π / 2 + 2) / π := by
  rw [uIoc_of_le (by linarith : -δ ≤ δ)] at hc
  have hL : 0 ≤ L := by
    have h := hw δ ⟨by linarith, le_rfl⟩
    rw [abs_of_pos hδ] at h
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h) hδ
  by_cases hz : c = 0
  · subst c; simp only [sub_self, zero_mul, norm_zero]; positivity
  have hpc : 0 < π * |c| := mul_pos pi_pos (abs_pos.mpr hz)
  rw [Real.norm_eq_abs, abs_mul, flatSeamKernel, abs_mul, abs_inv, abs_mul, abs_of_pos pi_pos,
    inv_mul_eq_div, ← mul_div_assoc, div_le_iff₀ hpc]
  calc _ ≤ (L * |c|) * (π / 2 + 2) := mul_le_mul (hw c ⟨hc.1.le, hc.2⟩)
         (abs_integral_sinc_le _) (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))
       _ = _ := by field_simp [pi_ne_zero]

/-- A first-order modulus at the origin suffices; the weight need not vanish there. -/
private theorem tendsto_flatSeam_remainder (hδ : 0 < δ) (hm : Measurable w)
    (hw : ∀ c ∈ Icc (-δ) δ, |w c - w 0| ≤ L * |c|) :
    Tendsto (fun R ↦ ∫ c in (-δ)..δ, (w c - w 0) * flatSeamKernel R c) atTop
      (𝓝 (∫ c in (-δ)..δ, (w c - w 0) * (2 * |c|)⁻¹)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ L * (π / 2 + 2) / π)
  · exact Eventually.of_forall fun R ↦ ((hm.sub measurable_const).mul (flatSeam_meas R)).aestronglyMeasurable
  · exact Eventually.of_forall fun R ↦ Eventually.of_forall fun c hc ↦ flatSeam_rem_bound hδ hw R hc
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun c _ ↦ (flatSeam_lim c).const_mul (w c - w 0)

/-- Transfer the unweighted reference finite part `A` to the weighted seam. -/
private theorem tendsto_flatSeam_weighted (hδ : 0 < δ) (hm : Measurable w)
    (hw : ∀ c ∈ Icc (-δ) δ, |w c - w 0| ≤ L * |c|) {A : ℝ}
    (href : Tendsto (fun R ↦ (∫ c in (-δ)..δ, flatSeamKernel R c) - log R) atTop (𝓝 A)) :
    Tendsto (fun R ↦ (∫ c in (-δ)..δ, w c * flatSeamKernel R c) - w 0 * log R) atTop
      (𝓝 (w 0 * A + ∫ c in (-δ)..δ, (w c - w 0) * (2 * |c|)⁻¹)) := by
  apply ((href.const_mul (w 0)).add (tendsto_flatSeam_remainder hδ hm hw)).congr
  intro R
  have hi : IntervalIntegrable (fun c ↦ (w c - w 0) * flatSeamKernel R c) volume (-δ) δ := by
    rw [intervalIntegrable_iff]
    refine Integrable.mono' (intervalIntegrable_const (c := L * (π / 2 + 2) / π)
      (a := -δ) (b := δ)).def'
      ((hm.sub measurable_const).mul (flatSeam_meas R)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with c hc using flatSeam_rem_bound hδ hw R hc
  have he : (fun c ↦ w c * flatSeamKernel R c) = fun c ↦
      w 0 * flatSeamKernel R c + (w c - w 0) * flatSeamKernel R c := by funext c; ring
  rw [he, intervalIntegral.integral_add ((flatSeam_integrable R (-δ) δ).const_mul _) hi,
    intervalIntegral.integral_const_mul]
  ring

end RiemannMasullo

open Real Set Filter MeasureTheory Topology

namespace RiemannMasullo

/-- The finite term is the convergent sine-integral remainder for the chosen seam window. -/
def realCentralSeamFinitePart (δ : ℝ) : ℝ :=
  (2 / π) * ((∫ x in (0 : ℝ)..1, seamSi (2 * π * δ) x / x) +
    ∫ x in Ioi (1 : ℝ), (seamSi (2 * π * δ) x - π / 2) / x)

private theorem tendsto_flatSeam_reference {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R ↦ (∫ c in (-δ)..δ, flatSeamKernel R c) - log R) atTop
      (𝓝 (realCentralSeamFinitePart δ)) := by
  refine (tendsto_seamSi_reference hδ).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [← integral_centralPhase_reference hδ hR]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with c hc _
  rw [integral_realBandKernel_mul hc, flatSeamKernel]
  simp only [one_mul]

private theorem integral_flatSeam_scale (R δ : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ c in (-(a * δ))..(a * δ), flatSeamKernel R c) =
      ∫ c in (-δ)..δ, flatSeamKernel (a * R) c := by
  have hk (c : ℝ) : flatSeamKernel (a * R) c = a * flatSeamKernel R (a * c) := by
    unfold flatSeamKernel
    rw [show 2 * π * c * (a * R) = 2 * π * (a * c) * R by ring,
      show π * (a * c) = a * (π * c) by ring, mul_inv_rev a (π * c)]
    calc _ = (a * a⁻¹) * ((π * c)⁻¹ * ∫ t in (0 : ℝ)..(2 * π * (a * c) * R), sinc t) := by
           rw [mul_inv_cancel₀ ha.ne', one_mul]
         _ = _ := by ring
  simp_rw [hk]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (flatSeamKernel R) ha.ne', smul_eq_mul,
    mul_neg, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- Dilating the phase window adds exactly the logarithm of the dilation. -/
theorem realCentralSeamFinitePart_mul {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    realCentralSeamFinitePart (a * δ) = realCentralSeamFinitePart δ + log a := by
  have ht : Tendsto (fun R : ℝ ↦ a * R) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id
  apply tendsto_nhds_unique (tendsto_flatSeam_reference (mul_pos ha hδ))
  refine (((tendsto_flatSeam_reference hδ).comp ht).add_const (log a)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  change ((∫ c in (-δ)..δ, flatSeamKernel (a * R) c) - log (a * R)) + log a = _
  rw [integral_flatSeam_scale R δ ha, log_mul ha.ne' hR.ne']
  ring

/-- The difference of finite reference constants needs no evaluation of either integral. -/
theorem realCentralSeamFinitePart_sub {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') :
    realCentralSeamFinitePart δ' - realCentralSeamFinitePart δ = log (δ' / δ) := by
  have h := realCentralSeamFinitePart_mul (div_pos hδ' hδ) hδ
  rw [div_mul_cancel₀ _ hδ.ne'] at h
  linarith

/-- Exact finite part in the central additive phase variable, allowing a nonzero
weight at one (phase zero). The remainder is an ordinary integrable function. -/
private theorem tendsto_flatSeam_weighted_explicit {δ L : ℝ} {w : ℝ → ℝ}
    (hδ : 0 < δ) (hm : Measurable w)
    (hw : ∀ c ∈ Icc (-δ) δ, |w c - w 0| ≤ L * |c|) :
    Tendsto (fun R ↦ (∫ c in (-δ)..δ, w c * flatSeamKernel R c) - w 0 * log R) atTop
      (𝓝 (w 0 * realCentralSeamFinitePart δ + ∫ c in (-δ)..δ, (w c - w 0) * (2 * |c|)⁻¹)) :=
  tendsto_flatSeam_weighted hδ hm hw (tendsto_flatSeam_reference hδ)

end RiemannMasullo

open Real Set MeasureTheory

namespace RiemannMasullo

@[expose] def centralDilation (c : ℝ) : ℝ := (1 + c)⁻¹

private def centralBandIntegral (R c : ℝ) : ℝ := ∫ x in (0 : ℝ)..R, realBandKernel 1 (c * x)

private theorem centralDilation_mem {c δ : ℝ} (hδ : δ < 1) (hc : c ∈ Icc (-δ) δ) :
    centralDilation c ∈ Icc (centralDilation δ) (centralDilation (-δ)) := by
  obtain ⟨hl, hr⟩ := hc
  unfold centralDilation
  exact ⟨inv_anti₀ (by linarith) (by linarith), inv_anti₀ (by linarith) (by linarith)⟩

/-- The central band term in physical and phase coordinates at finite radius. -/
private theorem integral_centralDilation_substitution {δ : ℝ} (h0 : 0 < δ) (hδ : δ < 1)
    (R : ℝ) {w : ℝ → ℝ} (hw : ContinuousOn w (Icc (centralDilation δ) (centralDilation (-δ)))) :
    (∫ g in centralDilation δ..centralDilation (-δ),
      w g / (sqrt g * g) * centralBandIntegral R (1 / g - 1)) =
    ∫ c in (-δ)..δ, w (centralDilation c) * sqrt (centralDilation c) * centralBandIntegral R c := by
  let F := fun g : ℝ ↦ w g / (sqrt g * g) * centralBandIntegral R (1 / g - 1)
  have hab : -δ ≤ δ := by linarith
  have hp (c : ℝ) (hc : c ∈ uIcc (-δ) δ) : 0 < 1 + c := by
    rw [uIcc_of_le hab] at hc
    linarith [hc.1]
  have hd (c : ℝ) (hc : c ∈ uIcc (-δ) δ) :
      HasDerivAt centralDilation (-(centralDilation c)^2) c := by
    have h := (((hasDerivAt_id c).const_add (1 : ℝ)).inv (hp c hc).ne')
    convert h using 1
    · rfl
    · simp only [centralDilation, inv_pow, id_eq, neg_div, one_div]
  have hu : ContinuousOn centralDilation (uIcc (-δ) δ) := fun c hc ↦
    (hd c hc).continuousAt.continuousWithinAt
  have hk : Continuous (centralBandIntegral R) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun c x : ℝ ↦ realBandKernel 1 (c*x))
      ((continuous_realBandKernel 1).comp (continuous_fst.mul continuous_snd)) 0 R
  have hF : ContinuousOn F (Icc (centralDilation δ) (centralDilation (-δ))) := by
    have pos (g : ℝ) (hg : g ∈ Icc (centralDilation δ) (centralDilation (-δ))) : 0 < g :=
      lt_of_lt_of_le (inv_pos.mpr (by linarith : 0 < 1 + δ)) hg.1
    exact (hw.div (Real.continuous_sqrt.continuousOn.mul continuousOn_id)
      (fun g hg ↦ mul_ne_zero (Real.sqrt_pos.2 (pos g hg)).ne' (pos g hg).ne')).mul
      (hk.comp_continuousOn ((continuousOn_const.div continuousOn_id
        (fun g hg ↦ (pos g hg).ne')).sub continuousOn_const))
  have hs := intervalIntegral.integral_comp_mul_deriv' hd (hu.pow 2).neg
    (hF.mono (by
      rintro g ⟨c, hc, rfl⟩
      exact centralDilation_mem hδ (by simpa [uIcc_of_le hab] using hc)))
  change (∫ g in centralDilation δ..centralDilation (-δ), F g) = _
  rw [intervalIntegral.integral_symm, ← hs, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro c hc
  have hg : 0 < centralDilation c := inv_pos.mpr (hp c hc)
  have he : 1 / centralDilation c - 1 = c := by simp [centralDilation]
  simp only [Function.comp_apply, F, he]
  have e : centralDilation c / sqrt (centralDilation c) = sqrt (centralDilation c) := by
    apply (div_eq_iff (Real.sqrt_pos.2 hg).ne').2
    simpa [pow_two] using (Real.sq_sqrt hg.le).symm
  calc _ = w (centralDilation c) * (centralDilation c / sqrt (centralDilation c)) *
          centralBandIntegral R c := by field_simp [hg.ne', (Real.sqrt_pos.2 hg).ne']
       _ = _ := by rw [e]

/-- A linear modulus at physical dilation one remains linear in the phase coordinate. -/
private theorem centralDilation_weight_bound {δ C : ℝ} (hδ : δ < 1) (hC : 0 ≤ C) {w : ℝ → ℝ}
    (hw : ∀ g ∈ Icc (centralDilation δ) (centralDilation (-δ)), |w g - w 1| ≤ C * |g - 1|)
    {c : ℝ} (hc : c ∈ Icc (-δ) δ) :
    |w (centralDilation c) * sqrt (centralDilation c) - w 1| ≤
      ((C * sqrt ((1-δ)⁻¹) + |w 1|) * (1-δ)⁻¹) * |c| := by
  let g := centralDilation c
  have hp : 0 < 1 + c := by linarith [hc.1]
  have hg : 0 < g := inv_pos.mpr hp
  have hmem := centralDilation_mem hδ hc
  have hmax : g ≤ (1-δ)⁻¹ := by simpa [sub_eq_add_neg, g, centralDilation] using hmem.2
  have hs := Real.sqrt_nonneg g
  have hsq := Real.sq_sqrt hg.le
  have hdiff : |sqrt g - 1| ≤ |g - 1| := by
    have e : g - 1 = (sqrt g - 1) * (sqrt g + 1) := by nlinarith
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ sqrt g + 1)]
    nlinarith [mul_nonneg (abs_nonneg (sqrt g - 1)) hs]
  have ed : g - 1 = -(c * g) := by dsimp [g, centralDilation]; field_simp [hp.ne']; ring
  calc |w g * sqrt g - w 1| = |(w g - w 1) * sqrt g + w 1 * (sqrt g - 1)| := by ring_nf
       _ ≤ |w g - w 1| * sqrt g + |w 1| * |sqrt g - 1| := by
         simpa [abs_mul, abs_of_nonneg hs] using abs_add_le ((w g - w 1) * sqrt g) (w 1 * (sqrt g - 1))
       _ ≤ (C * |g - 1|) * sqrt ((1-δ)⁻¹) + |w 1| * |g - 1| := by
         exact add_le_add (mul_le_mul (hw g hmem) (Real.sqrt_le_sqrt hmax) hs
           (mul_nonneg hC (abs_nonneg _))) (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))
       _ = (C * sqrt ((1-δ)⁻¹) + |w 1|) * g * |c| := by rw [ed, abs_neg, abs_mul, abs_of_pos hg]; ring
       _ ≤ _ := by gcongr

end RiemannMasullo

open Filter MeasureTheory Set Topology Real
open scoped Interval

namespace RiemannMasullo

/-- The reflected summand of the integrated even band kernel. -/
private def realPWReflectedBandMass (R g : ℝ) : ℝ :=
  (π * (1 / g + 1))⁻¹ * ∫ t in (0 : ℝ)..(2 * π * (1 / g + 1) * R), sinc t

private theorem realPWBandDiagonalMass_eq_add_reflected (R g : ℝ) :
    realPWBandDiagonalMass R g =
      (π * (1 / g - 1))⁻¹ * (∫ t in (0 : ℝ)..(2 * π * (1 / g - 1) * R), sinc t) +
        realPWReflectedBandMass R g := rfl

private theorem reflected_meas (R : ℝ) : Measurable (realPWReflectedBandMass R) := by
  unfold realPWReflectedBandMass
  exact (by fun_prop : Measurable (fun g : ℝ ↦ (π * (1 / g + 1))⁻¹)).mul
    (continuous_integral_sinc.measurable.comp (by fun_prop))

private theorem reflected_bound (R g : ℝ) (hg : 0 < g) :
    |realPWReflectedBandMass R g| ≤ π⁻¹ * (π / 2 + 2) := by
  have hp : 0 < 1 / g + 1 := by positivity
  rw [realPWReflectedBandMass, abs_mul, abs_of_pos (inv_pos.mpr (mul_pos pi_pos hp))]
  apply mul_le_mul _ (abs_integral_sinc_le _) (abs_nonneg _) (by positivity)
  apply inv_anti₀ pi_pos
  nlinarith [mul_nonneg pi_pos.le (one_div_pos.mpr hg).le]

private theorem reflected_lim {ι : Type*} {l : Filter ι} {R : ι → ℝ}
    (hR : Tendsto R l atTop) {g : ℝ} (hg : 0 < g) :
    Tendsto (fun i ↦ realPWReflectedBandMass (R i) g) l (𝓝 ((2 * (1 / g + 1))⁻¹)) := by
  have hp : 0 < 1 / g + 1 := by positivity
  have h := (tendsto_integral_sinc_mul_of_pos hR (c := 2 * π * (1 / g + 1))
    (by positivity)).const_mul ((π * (1 / g + 1))⁻¹)
  have e : (π * (1 / g + 1))⁻¹ * (π / 2) = (2 * (1 / g + 1))⁻¹ := by
    generalize 1 / g + 1 = c at hp ⊢
    field_simp [pi_ne_zero, hp.ne']
  rw [e] at h
  exact h

/-- Reflected band minus the rank-one mass, with the half-density and Haar factors.
Neither the test nor its value at the identity needs any cancellation. -/
private theorem tendsto_integral_realPWNoncentralTrace {a b : ℝ} {w : ℝ → ℝ}
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {R : ι → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) (hR : Tendsto R l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * (√g * g)⁻¹ *
      (realPWReflectedBandMass (R i) g - realPWPolarDiagonalMass (R i) g)) l
      (𝓝 (∫ g in a..b, w g * (√g * g)⁻¹ * ((2 * (1 / g + 1))⁻¹ - min 1 g))) := by
  let v := fun g : ℝ ↦ w g * (√g * g)⁻¹
  have hv : ContinuousOn v (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hw.mul ((continuous_sqrt.continuousOn.mul continuousOn_id).inv₀ fun g hg ↦
      mul_ne_zero (sqrt_pos.mpr (ha.trans_le hg.1)).ne' (ha.trans_le hg.1).ne')
  let K := fun g : ℝ ↦ π⁻¹ * (π / 2 + 2) +
    |g| / π * ((|1 / g + 1| + |1 / g - 1|) * (π / 2 + 2) + 2)
  have hK : ContinuousOn K (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hinv : ContinuousOn (fun g : ℝ ↦ 1 / g) (Icc a b) :=
      continuousOn_const.div continuousOn_id fun g hg ↦ (ha.trans_le hg.1).ne'
    have hs : ContinuousOn (fun g : ℝ ↦ |1 / g + 1| + |1 / g - 1|) (Icc a b) :=
      (hinv.add continuousOn_const).abs.add (hinv.sub continuousOn_const).abs
    exact continuousOn_const.add ((continuous_abs.continuousOn.div_const π).mul
      ((hs.mul continuousOn_const).add continuousOn_const))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun g ↦ |v g| * K g) ?_ ?_ ((hv.abs.mul hK).intervalIntegrable) ?_
  · exact Eventually.of_forall fun i ↦ hv.intervalIntegrable.def'.aestronglyMeasurable.mul
      (((reflected_meas (R i)).sub (measurable_realPWPolarDiagonalMass (R i))).aestronglyMeasurable)
  · refine Eventually.of_forall fun i ↦ Eventually.of_forall fun g hg ↦ ?_
    rw [uIoc_of_le hab] at hg
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
      (reflected_bound (R i) g (ha.trans hg.1)) (abs_realPWPolarDiagonalMass_le (R i) g)))
      (abs_nonneg (v g))
  · refine Eventually.of_forall fun g hg ↦ ?_
    rw [uIoc_of_le hab] at hg
    exact ((reflected_lim hR (ha.trans hg.1)).sub
      (tendsto_realPWPolarDiagonalMass hR (ha.trans hg.1))).const_mul (v g)

end RiemannMasullo

open Filter MeasureTheory Set Topology Real NumberField IsDedekindDomain
open scoped Interval NNReal NumberField.AdeleRing

namespace RiemannMasullo.RatEmptyRealLevelBridge

private theorem floor_diagonal_bound {B : ℝ} (hB : 0 < B) (g x : ℝ) :
    ‖realPWLevelDiagonal B g x‖ ≤ 8 * B := by
  have hk (u : ℝ) : |realBandKernel B u| ≤ 2 * B := by
    rw [realBandKernel, abs_mul, abs_of_nonneg (show 0 ≤ 2 * B by positivity)]
    simpa using mul_le_mul_of_nonneg_left (abs_sinc_le_one (2 * π * B * u))
      (show 0 ≤ 2 * B by positivity)
  have hp : |realPWPolarDiagonal B g x| ≤ 4 * B := by
    rw [realPWPolarDiagonal, abs_div, abs_mul, abs_of_pos hB, div_le_iff₀ hB]
    exact (mul_le_mul (hk _) (hk _) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  rw [Real.norm_eq_abs, realPWLevelDiagonal]
  refine (abs_sub _ _).trans ?_
  have hb := (abs_add_le (realBandKernel B (x / g - x)) (realBandKernel B (x / g + x))).trans
    (add_le_add (hk _) (hk _))
  unfold realPWBandDiagonal
  linarith

/-- The removed spatial floor contributes zero in the limit, with no cancellation at one. -/
theorem tendsto_integral_actualCompressionTrace_spatialFloor
    {a b : ℝ} {w : ℝ → ℝ} {ι : Type*} {l : Filter ι} {B h : ι → ℝ}
    (ω : PontryaginDual (MonoidHom.ker (sIdeleQuotientNorm ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))))
    (ha : 0 < a) (hab : a ≤ b) (hw : ContinuousOn w (Icc a b))
    (hB : ∀ i, 0 < B i) (hh : ∀ i, 0 ≤ h i) (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ g in a..b, (w g : ℂ) * actualCompressionTrace ω (hB i) (hh i) g / (g : ℂ))
      l (𝓝 0) := by
  have hc : ContinuousOn (fun g : ℝ ↦ w g * (√g)⁻¹ / g) (Icc a b) :=
    (hw.mul (Real.continuous_sqrt.continuousOn.inv₀ fun g hg ↦
      (Real.sqrt_pos.mpr (ha.trans_le hg.1)).ne')).div continuousOn_id fun g hg ↦
        (ha.trans_le hg.1).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have ht : Tendsto (fun i ↦ (M * 8 * |b - a|) * (B i * h i)) l (𝓝 0) := by
    simpa using hBh.const_mul (M * 8 * |b - a|)
  refine squeeze_zero_norm (fun i ↦ ?_) ht
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M * (8 * B i * h i))
    (fun g hg ↦ ?_)).trans_eq (by ring)
  rw [uIoc_of_le hab] at hg
  have hg' : g ∈ Icc a b := ⟨hg.1.le, hg.2⟩
  have hg0 := ha.trans_le hg'.1
  rw [actualCompressionTrace_eq_flat ω (hB i) (hh i) hg0,
    realPWLevelCompressionTrace_eq (hB i) hg0 (hh i)]
  let D := ∫ x in (0 : ℝ)..h i, realPWLevelDiagonal (B i) g x
  change ‖(w g : ℂ) * (((√g)⁻¹ * D : ℝ) : ℂ) / (g : ℂ)‖ ≤ _
  rw [show (w g : ℂ) * (((√g)⁻¹ * D : ℝ) : ℂ) / (g : ℂ) =
    (((w g * (√g)⁻¹ / g) * D : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, norm_mul]
  have hd : ‖D‖ ≤ 8 * B i * h i := by
    simpa [D, abs_of_nonneg (hh i)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := h i)
        (fun x _ ↦ floor_diagonal_bound (hB i) g x))
  exact mul_le_mul (hM g hg') hd (norm_nonneg _) ((norm_nonneg _).trans (hM g hg'))

end RiemannMasullo.RatEmptyRealLevelBridge

open Filter MeasureTheory Set Topology Real NumberField
open scoped Interval NumberField.AdeleRing

namespace RiemannMasullo.RatEmptyRealLevelBridge

private def centralWeight (w : ℝ → ℝ) (c : ℝ) : ℝ :=
  w (centralDilation c) * sqrt (centralDilation c)

/-- The explicit finite part for the true rational Haar compression trace on the indicated
central physical interval, with the even-band reflection and polar subtraction retained. -/
def actualCentralTraceFinitePart (δ : ℝ) (w : ℝ → ℝ) : ℝ :=
  w 1 * realCentralSeamFinitePart δ +
    (∫ c in (-δ)..δ, (centralWeight w c - w 1) * (2 * |c|)⁻¹) +
    ∫ g in centralDilation δ..centralDilation (-δ), w g * (sqrt g * g)⁻¹ *
      ((2 * (1 / g + 1))⁻¹ - min 1 g)

private theorem actualHaarTrace_finiteRadius
    (ω : PontryaginDual (MonoidHom.ker (sIdeleQuotientNorm ℚ
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))))))
    {δ B L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 < B) (hL : 0 < L)
    {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ g in centralDilation δ..centralDilation (-δ),
      (w g : ℂ) * actualCompressionTrace ω hB hL.le g / (g : ℂ)) =
    ((∫ c in (-δ)..δ, centralWeight w c * flatSeamKernel (B*L) c) +
      (∫ g in centralDilation δ..centralDilation (-δ), w g * (sqrt g * g)⁻¹ *
        (realPWReflectedBandMass (B*L) g - realPWPolarDiagonalMass (B*L) g)) : ℝ) := by
  let a := centralDilation δ
  let b := centralDilation (-δ)
  have ha : 0 < a := inv_pos.mpr (by linarith : 0 < 1 + δ)
  have hab : a ≤ b := inv_anti₀ (by linarith : 0 < 1 + -δ) (by linarith)
  let u (g : ℝ) := w g * (sqrt g * g)⁻¹
  let K (g : ℝ) := centralBandIntegral (B*L) (1 / g - 1)
  let M (g : ℝ) := realPWReflectedBandMass (B*L) g - realPWPolarDiagonalMass (B*L) g
  have hpos (g : ℝ) (hg : g ∈ uIcc a b) : 0 < g := by
    rw [uIcc_of_le hab] at hg
    exact ha.trans_le hg.1
  have hu : ContinuousOn u (uIcc a b) := hw.continuousOn.mul
    ((continuous_sqrt.continuousOn.mul continuousOn_id).inv₀ fun g hg ↦
      mul_ne_zero (sqrt_pos.mpr (hpos g hg)).ne' (hpos g hg).ne')
  have hphase : ContinuousOn (fun g : ℝ ↦ 1 / g - 1) (uIcc a b) :=
    (continuousOn_const.div continuousOn_id fun g hg ↦ (hpos g hg).ne').sub continuousOn_const
  have hK : ContinuousOn K (uIcc a b) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun c x : ℝ ↦ realBandKernel 1 (c*x))
      ((continuous_realBandKernel 1).comp (continuous_fst.mul continuous_snd)) 0 (B*L)).comp_continuousOn hphase
  have hM : ContinuousOn M (uIcc a b) := by
    have hplus : ContinuousOn (fun g : ℝ ↦ 1 / g + 1) (uIcc a b) :=
      (continuousOn_const.div continuousOn_id fun g hg ↦ (hpos g hg).ne').add continuousOn_const
    have hp : ContinuousOn (fun g : ℝ ↦ π * (1 / g + 1)) (uIcc a b) := continuousOn_const.mul hplus
    unfold M realPWReflectedBandMass realPWPolarDiagonalMass
    have him (v : ℝ → ℝ) (hv : ContinuousOn v (uIcc a b)) :
        ContinuousOn (fun g : ℝ ↦ ∫ t in (0 : ℝ)..(2 * π * v g * (B*L)), sinc t) (uIcc a b) :=
      continuous_integral_sinc.comp_continuousOn ((continuousOn_const.mul hv).mul continuousOn_const)
    exact ((hp.inv₀ fun g hg ↦ (mul_pos pi_pos (by have := hpos g hg; positivity)).ne').mul
      (him _ hplus)).sub ((continuousOn_id.div_const π).mul
        (((hplus.mul (him _ hplus)).sub (hphase.mul (him _ hphase))).add
          (((continuous_cos.comp_continuousOn ((continuousOn_const.mul hplus).mul continuousOn_const)).sub
            (continuous_cos.comp_continuousOn ((continuousOn_const.mul hphase).mul continuousOn_const))).div_const _)))
  have hadd : (∫ g in a..b, u g * (K g + M g)) =
      (∫ g in a..b, u g * K g) + (∫ g in a..b, u g * M g) := by
    simp only [mul_add]
    exact intervalIntegral.integral_add ((hu.mul hK).intervalIntegrable)
      ((hu.mul hM).intervalIntegrable)
  have hc : (∫ g in a..b, u g * K g) =
      ∫ c in (-δ)..δ, centralWeight w c * flatSeamKernel (B*L) c := by
    simp only [u, K, ← div_eq_mul_inv]
    rw [integral_centralDilation_substitution hδ0 hδ1 _ hw.continuousOn]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with c hc _
    rw [centralWeight, centralBandIntegral, integral_realBandKernel_mul hc, flatSeamKernel, one_mul]
  change _ = (((∫ c in (-δ)..δ, _) + ∫ g in a..b, u g * M g : ℝ) : ℂ)
  rw [← hc, ← hadd, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with g hg hg'
  have hg0 : 0 < g := hpos g (uIoc_subset_uIcc hg')
  rw [actualCompressionTrace_eq_flat ω hB hL.le hg0, realPWLevelCompressionTrace_eq hB hg0 hL.le,
    integral_realPWLevelDiagonal hg0 hg hB.ne' hL.ne', realPWBandDiagonalMass_eq_add_reflected]
  have hphase0 : 1 / g - 1 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, ← sub_ne_zero]
    intro h
    apply hg
    have e : 1 / g = 1 := by linarith
    simpa only [one_mul] using ((div_eq_iff hg0.ne').mp e).symm
  simp only [u, K, M, centralBandIntegral, integral_realBandKernel_mul hphase0, one_mul]
  push_cast
  ring

/-- Across norm one, subtraction of `w 1 * log (B*L)` gives a finite limit for
actual one-dilation compression traces averaged with the standard Haar density `dg/g`. -/
theorem tendsto_actualHaarTrace_centralFinitePart
    (ω : PontryaginDual (MonoidHom.ker (sIdeleQuotientNorm ℚ
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))))))
    {δ C : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hw1 : ∀ g ∈ Icc (centralDilation δ) (centralDilation (-δ)), |w g - w 1| ≤ C * |g - 1|)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {B L : ι → ℝ}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 < L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ (∫ g in centralDilation δ..centralDilation (-δ),
      (w g : ℂ) * actualCompressionTrace ω (hB i) (hL i).le g / (g : ℂ)) -
        ((w 1 * log (B i * L i) : ℝ) : ℂ)) l (𝓝 (actualCentralTraceFinitePart δ w : ℂ)) := by
  have hd : Measurable centralDilation := by unfold centralDilation; fun_prop
  have hmeas : Measurable (centralWeight w) := (hw.measurable.comp hd).mul
    (continuous_sqrt.measurable.comp hd)
  have hw0 : centralWeight w 0 = w 1 := by simp [centralWeight, centralDilation]
  have hcentral := (tendsto_flatSeam_weighted_explicit hδ0 hmeas
    (fun c hc ↦ by rw [hw0]; exact centralDilation_weight_bound hδ1 hC hw1 hc)).comp hBL
  simp only [hw0] at hcentral
  have ha : 0 < centralDilation δ := inv_pos.mpr (by linarith : 0 < 1 + δ)
  have hab : centralDilation δ ≤ centralDilation (-δ) := inv_anti₀ (by linarith : 0 < 1 + -δ) (by linarith)
  have hnoncentral := tendsto_integral_realPWNoncentralTrace ha hab hw.continuousOn hBL
  have h := (Complex.continuous_ofReal.tendsto _).comp (hcentral.add hnoncentral)
  refine h.congr fun i ↦ ?_
  rw [actualHaarTrace_finiteRadius ω hδ0 hδ1 (hB i) (hL i) hw]
  simp only [Function.comp_apply, Complex.ofReal_add, Complex.ofReal_sub]
  abel

end RiemannMasullo.RatEmptyRealLevelBridge
