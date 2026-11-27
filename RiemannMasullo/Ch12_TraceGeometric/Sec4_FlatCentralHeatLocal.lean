module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Local shift estimate across the identity in reciprocal phase coordinates

For compact twice continuously differentiable radial tests, removing the change of the test at
the singular phase times the logarithm of the cutoff leaves a locally Lipschitz error,
uniformly in every radius at least one. The moving endpoints, the reflected phase and the
overlap radius are all retained. The sine-integral bound controls changes in the band radius at a zero of the direct phase.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Real
open scoped Topology

namespace RiemannMasullo.ThroughOneStability

private theorem phaseKernel_meas (R : ℝ) : Measurable (phaseKernel R) :=
  (measurable_const.mul measurable_id).inv.mul
    (continuous_integral_sinc.measurable.comp
      ((measurable_const.mul measurable_id).mul measurable_const))

private theorem phaseKernel_contAt (R : ℝ) {c : ℝ} (hc : c ≠ 0) :
    ContinuousAt (phaseKernel R) c :=
  ((continuousAt_const.mul continuousAt_id).inv₀ (mul_ne_zero pi_ne_zero hc)).mul
    (continuous_integral_sinc.continuousAt.comp
      ((continuousAt_const.mul continuousAt_id).mul continuousAt_const))

private theorem abs_phaseKernel_radius (R c : ℝ) : |phaseKernel R c| ≤ 2 * |R| := by
  by_cases hc : c = 0
  · simp [hc, phaseKernel]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2*π*c*R)
    (f := sinc) (C := 1) fun t _ ↦ by simpa using abs_sinc_le_one t
  have h' : |∫ t in (0 : ℝ)..(2*π*c*R), sinc t| ≤ |2*π*c*R| := by simpa using h
  rw [phaseKernel, abs_mul, abs_inv]
  calc
    _ ≤ |π*c|⁻¹ * |2*π*c*R| := mul_le_mul_of_nonneg_left h' (by positivity)
    _ = _ := by
      simp only [abs_mul, abs_of_pos pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
      field_simp [pi_ne_zero, (abs_pos.mpr hc).ne']

private theorem phaseKernel_int (R a b : ℝ) : IntervalIntegrable (phaseKernel R) volume a b := by
  rw [intervalIntegrable_iff]
  exact Integrable.mono' (intervalIntegrable_const (a := a) (b := b) (μ := volume) (c := 2 * |R|)).def' (phaseKernel_meas R).aestronglyMeasurable
    (.of_forall fun c ↦ by simpa only [Real.norm_eq_abs] using abs_phaseKernel_radius R c)

/-- Unweighted mass of the direct phase on a symmetric window. -/
def phaseReference (D R : ℝ) : ℝ := ∫ c in (-D)..D, phaseKernel R c

private theorem phaseKernel_even (R c : ℝ) : phaseKernel R (-c) = phaseKernel R c := by
  unfold phaseKernel
  rw [show 2 * π * -c * R = -(2 * π * c * R) by ring, integral_sinc_neg]
  simp

private theorem phaseReference_rescale (D : ℝ) {R : ℝ} (hR : R ≠ 0) :
    phaseReference D R = 2 * ∫ c in (0 : ℝ)..D*R, phaseKernel 1 c := by
  have he (c : ℝ) : phaseKernel R c = R * phaseKernel 1 (c*R) := by
    by_cases hc : c = 0
    · simp [hc, phaseKernel]
    unfold phaseKernel
    rw [mul_one, show 2 * π * (c*R) = 2*π*c*R by ring]
    field_simp [pi_ne_zero, hc, hR]
  have hs := intervalIntegral.integral_add_adjacent_intervals (phaseKernel_int 1 (-(D*R)) 0)
    (phaseKernel_int 1 0 (D*R))
  have hn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := D*R) (phaseKernel 1)
  simp only [phaseKernel_even, neg_zero] at hn
  simp only [phaseReference, he, intervalIntegral.integral_const_mul,
    intervalIntegral.mul_integral_comp_mul_right, neg_mul]
  rw [← hs, ← hn, two_mul]

/-- In log radius the unweighted direct mass has the published reference as its exact increment. -/
theorem phaseReference_exp (D : ℝ) (hD : 0 < D) (u : ℝ) :
    phaseReference D (exp u) = phaseReference D 1 + logReference D u := by
  let G (t : ℝ) := 2 * ∫ c in (0 : ℝ)..D*exp t, phaseKernel 1 c
  let S (t : ℝ) := ∫ x in (0 : ℝ)..2*π*D*exp t, sinc x
  have hc : Continuous S := continuous_integral_sinc.comp (continuous_const.mul continuous_exp)
  have hg (t : ℝ) : HasDerivAt G ((2/π) * S t) t := by
    have hp : D*exp t ≠ 0 := (mul_pos hD (exp_pos t)).ne'
    have hp' := intervalIntegral.integral_hasDerivAt_right (phaseKernel_int 1 0 (D*exp t))
      (phaseKernel_meas 1).stronglyMeasurable.stronglyMeasurableAtFilter
      (phaseKernel_contAt 1 hp)
    apply ((hp'.comp t ((hasDerivAt_exp t).const_mul D)).const_mul 2).congr_deriv
    simp only [phaseKernel, mul_one, S, show 2 * π * (D * exp t) = 2 * π * D * exp t by ring]
    field_simp [pi_ne_zero, hD.ne', (exp_pos t).ne']
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := u)
    (fun t _ ↦ hg t) ((continuous_const.mul hc).intervalIntegrable 0 u)
  rw [intervalIntegral.integral_const_mul] at hi
  rw [phaseReference_rescale _ (exp_pos u).ne', phaseReference_rescale _ one_ne_zero]
  simpa [G, S, logReference, exp_zero] using (eq_add_of_sub_eq' hi.symm)

/-- Uniform absolute error in the unweighted logarithmic normalization on all radii at least one. -/
theorem exists_phaseReference_sub_log_bound {D : ℝ} (hD : 0 < D) :
    ∃ M ≥ (0 : ℝ), ∀ R ≥ (1 : ℝ), |phaseReference D R - log R| ≤ M := by
  let k := 2 / (π * π * D)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  refine ⟨|phaseReference D 1| + k, by positivity, ?_⟩
  intro R hR
  have hp : 0 < R := zero_lt_one.trans_le hR
  let u := log R
  have hu : 0 ≤ u := log_nonneg hR
  let S (t : ℝ) := ∫ x in (0 : ℝ)..2*π*D*exp t, sinc x
  have hc : Continuous S := continuous_integral_sinc.comp (continuous_const.mul continuous_exp)
  have he (t : ℝ) : |(2/π) * S t - 1| ≤ k * exp (-t) := by
    rw [show (2/π)*S t-1 = (2/π)*(S t - π/2) by field_simp, abs_mul,
      abs_of_pos (by positivity : 0 < 2/π)]
    calc (2 / π) * |S t - π / 2| ≤ (2 / π) * (2/(2*π*D*exp t)) :=
           mul_le_mul_of_nonneg_left (abs_integral_sinc_sub_le (by positivity)) (by positivity)
         _ = _ := by dsimp [k]; rw [exp_neg]; field_simp
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun t ↦ (2/π)*S t-1)
    (g := fun t : ℝ ↦ k * exp (-t)) hu (.of_forall fun t _ ↦ by simpa only [Real.norm_eq_abs] using he t)
    ((continuous_const.mul (continuous_exp.comp continuous_neg)).intervalIntegrable 0 u)
  have hi' : |logReference D u - u| ≤ k := by
    rw [intervalIntegral.integral_sub (f := fun t : ℝ ↦ (2/π)*S t) (g := fun _ : ℝ ↦ 1) ((continuous_const.mul hc).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, mul_one, Real.norm_eq_abs] at hi
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg,
      integral_exp, neg_zero, exp_zero] at hi
    exact hi.trans (by nlinarith [mul_nonneg hk (exp_pos (-u)).le])
  have href := phaseReference_exp D hD u
  rw [show exp u = R from exp_log hp] at href
  rw [href, add_sub_assoc]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hi')

/-- The test half-density after translating by log radius and passing to reciprocal phase. -/
def shiftedPhaseProfile (W : ℝ → ℝ) (z c : ℝ) : ℝ :=
  W (-log (1+c) - z) / sqrt (1+c)

private theorem logPhase_coord_bound {D c : ℝ} (hD : 0 < D) (hD' : D < 1)
    (hc : c ∈ Icc (-D) D) : |-log (1+c)| ≤ (1-D)⁻¹ * |c| := by
  have hder (t : ℝ) (ht : t ∈ Icc (-D) D) :
      HasDerivWithinAt (fun t : ℝ ↦ log (1+t)) (1+t)⁻¹ (Icc (-D) D) t := by
    have ht' : 0 < 1+t := by linarith [ht.1]
    simpa using ((((hasDerivAt_id t).const_add 1).log ht'.ne').hasDerivWithinAt)
  have hi := (convex_Icc (-D) D).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := (1-D)⁻¹) hder (fun t ht ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith [ht.1]))]
      exact inv_anti₀ (by linarith) (by linarith [ht.1]))
    (show 0 ∈ Icc (-D) D from ⟨by linarith, hD.le⟩) hc
  simpa [Real.norm_eq_abs] using hi

private theorem sqrtPhase_coord_bounds {D c : ℝ} (hD' : D < 1) (hc : c ∈ Icc (-D) D) :
    (sqrt (1+c))⁻¹ ≤ (sqrt (1-D))⁻¹ ∧
    |(sqrt (1+c))⁻¹ - 1| ≤ (sqrt (1-D))⁻¹ * |c| := by
  have h0 : 0 < 1-D := by linarith
  have hl : 1-D ≤ 1+c := by linarith [hc.1]
  have hp : 0 < sqrt (1+c) := sqrt_pos.mpr (h0.trans_le hl)
  have hs := Real.sq_sqrt (h0.trans_le hl).le
  have hq := inv_anti₀ (sqrt_pos.mpr h0) (sqrt_le_sqrt hl)
  refine ⟨hq, ?_⟩
  have hid : (sqrt (1+c))⁻¹-1 = -c/(sqrt (1+c)*(1+sqrt (1+c))) := by
    field_simp [hp.ne', (by positivity : 1+sqrt (1+c) ≠ 0)]
    linarith
  rw [hid, abs_div, abs_neg, abs_of_pos (show 0 < sqrt (1+c)*(1+sqrt (1+c)) by positivity), div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg c)
  apply le_trans _ hq
  exact inv_anti₀ hp (by nlinarith [sq_nonneg (sqrt (1+c))])

private structure ProfileBounds (D : ℝ) (W : ℝ → ℝ) where
  mixed : ℝ
  base : ℝ
  shift : ℝ
  size : ℝ
  lip : ℝ
  nonneg : 0 ≤ mixed ∧ 0 ≤ base ∧ 0 ≤ shift ∧ 0 ≤ size ∧ 0 ≤ lip
  mixed_le : ∀ z c, c ∈ Icc (-D) D →
    |shiftedPhaseProfile W z c - shiftedPhaseProfile W 0 c - (W (-z) - W 0)| ≤ mixed * |z| * |c|
  base_le : ∀ c ∈ Icc (-D) D, |shiftedPhaseProfile W 0 c - W 0| ≤ base * |c|
  shift_le : ∀ z c, c ∈ Icc (-D) D →
    |shiftedPhaseProfile W z c - shiftedPhaseProfile W 0 c| ≤ shift * |z|
  size_le : ∀ c ∈ Icc (-D) D, |shiftedPhaseProfile W 0 c| ≤ size
  lip_le : ∀ z, |W (-z) - W 0| ≤ lip * |z|

private noncomputable def profileBounds_of_smooth {D : ℝ} (hD : 0 < D) (hD' : D < 1)
    (W V : ℝ → ℝ) {M N K : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hs : ∀ t, |W t| ≤ M) (hW : ∀ t, HasDerivAt W (V t) t)
    (hb : ∀ t, |V t| ≤ N) (hV : ∀ t u, |V t-V u| ≤ K * |t-u|) : ProfileBounds D W := by
  let q (c : ℝ) := (sqrt (1+c))⁻¹
  let x (c : ℝ) := -log (1+c)
  let Q := (sqrt (1-D))⁻¹
  let X := (1-D)⁻¹
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hq (c : ℝ) : 0 ≤ q c := by dsimp [q]; positivity
  have hp (z c : ℝ) : shiftedPhaseProfile W z c = q c * W (x c - z) := by
    simp only [shiftedPhaseProfile, div_eq_inv_mul, q, x]
  have hL (t u : ℝ) : |W t - W u| ≤ N * |t-u| := by
    exact (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ ↦ (hW t).hasDerivWithinAt) (fun t _ ↦ by simpa only [Real.norm_eq_abs] using hb t)
      (mem_univ u) (mem_univ t)
  have hΔ (z : ℝ) : |W (-z) - W 0| ≤ N*|z| := by simpa using hL (-z) 0
  refine ⟨Q*K*X+Q*N, Q*N*X+Q*M, Q*N, Q*M, N, ⟨by positivity, by positivity,
    by positivity, by positivity, hN⟩, ?_, ?_, ?_, ?_, hΔ⟩
  · intro z c hc
    obtain ⟨hqle, hdiff⟩ := sqrtPhase_coord_bounds hD' hc
    have hxl := logPhase_coord_bound hD hD' hc
    have hm := logProfile_mixed_displacement W V K hW hV (x c) z
    rw [hp, hp, sub_zero]
    calc
      _ = |q c*(W (x c-z)-W (x c)-(W (-z)-W 0)) + (q c-1)*(W (-z)-W 0)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ Q*(K*|z| * (X*|c|)) + (Q*|c|)*(N*|z|) := by
        simp only [abs_mul, abs_of_nonneg (hq c)]
        gcongr
        · exact hm.trans (mul_le_mul_of_nonneg_left hxl (by positivity))
        · exact hΔ z
      _ = _ := by ring
  · intro c hc
    obtain ⟨hqle, hdiff⟩ := sqrtPhase_coord_bounds hD' hc
    have hxl := logPhase_coord_bound hD hD' hc
    rw [hp, sub_zero]
    calc
      _ = |q c*(W (x c)-W 0) + (q c-1)*W 0| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ Q*(N*(X*|c|)) + (Q*|c|)*M := by
        simp only [abs_mul, abs_of_nonneg (hq c)]
        gcongr
        · exact (by simpa only [sub_zero] using hL (x c) 0 : |W (x c) - W 0| ≤ N * |x c|).trans
            (mul_le_mul_of_nonneg_left hxl hN)
        · exact hs 0
      _ = _ := by ring
  · intro z c hc
    rw [hp, hp, sub_zero, ← mul_sub, abs_mul, abs_of_nonneg (hq c)]
    exact (mul_le_mul (sqrtPhase_coord_bounds hD' hc).1
      (by simpa using hL (x c-z) (x c)) (abs_nonneg _) hQ).trans_eq (by ring)
  · intro c hc
    rw [hp, abs_mul, abs_of_nonneg (hq c)]
    exact mul_le_mul (sqrtPhase_coord_bounds hD' hc).1 (hs _) (abs_nonneg _) hQ

/-- The ambient positive-ray trace in reciprocal phase coordinates on a fixed window. -/
def fixedPhaseTrace (D : ℝ) (W : ℝ → ℝ) (R z : ℝ) : ℝ :=
  ∫ c in (-D)..D, shiftedPhaseProfile W z c *
    (phaseKernel (R * min 1 (exp z)) c + phaseKernel (R * min 1 (exp z)) (c+2))

private theorem weighted_phaseKernel {C y c : ℝ} (R : ℝ) (hC : 0 ≤ C) (hy : |y| ≤ C * |c|) :
    |y * phaseKernel R c| ≤ C * ((π/2+2)/π) := by
  by_cases hc : c = 0
  · simp [hc, phaseKernel]
    positivity
  rw [phaseKernel, abs_mul, abs_mul, abs_inv, abs_mul, abs_of_pos pi_pos]
  calc
    _ ≤ (C * |c|) * ((π * |c|)⁻¹ * (π/2+2)) := by
      apply mul_le_mul hy _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (abs_integral_sinc_le _) (by positivity)
    _ = _ := by field_simp [pi_ne_zero, (abs_pos.mpr hc).ne']

private def phaseIntegrand (W : ℝ → ℝ) (r z c : ℝ) : ℝ :=
  shiftedPhaseProfile W z c * (phaseKernel r c + phaseKernel r (c+2))

private theorem phaseIntegrand_int {D : ℝ} (hD : 0 < D) (hD' : D < 1)
    {W : ℝ → ℝ} (hW : Continuous W) (r z : ℝ) :
    IntervalIntegrable (phaseIntegrand W r z) volume (-D) D := by
  have hshift : IntervalIntegrable (fun c : ℝ ↦ phaseKernel r (c+2)) volume (-D) D :=
    (IntervalIntegrable.comp_add_right_iff (c := (2:ℝ))).mpr (phaseKernel_int _ _ _)
  refine ((phaseKernel_int r (-D) D).add hshift).continuousOn_mul ?_
  rw [uIcc_of_le (show -D ≤ D by linarith)]
  have hp (c : ℝ) (hc : c ∈ Icc (-D) D) : 0 < 1+c := by linarith [hc.1]
  have ht : ContinuousOn (fun c : ℝ ↦ 1+c) (Icc (-D) D) :=
    continuousOn_const.add continuousOn_id
  have hx := (ht.log fun c hc ↦ (hp c hc).ne').neg.sub (continuousOn_const (c := z))
  exact (hW.comp_continuousOn hx).div (continuous_sqrt.comp_continuousOn ht)
    (fun c hc ↦ (sqrt_pos.mpr (hp c hc)).ne')

private theorem abs_four_add (a b c d : ℝ) :
    |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
  linarith [abs_add_le a b, abs_add_le (a+b) c, abs_add_le (a+b+c) d]

private theorem phase_integrand_regular_bound {D : ℝ} (hD' : D < 1)
    {W : ℝ → ℝ} (P : ProfileBounds D W) (R z s c : ℝ)
    (hs : |s| ≤ |z|) (hc : c ∈ Icc (-D) D) :
    |phaseIntegrand W (R * exp s) z c - phaseIntegrand W R 0 c -
      W (-z) * phaseKernel (R * exp s) c + W 0 * phaseKernel R c| ≤
      (P.mixed * ((π/2+2)/π) + P.base/π + P.shift * ((π/2+2)/π) + P.size/π) * |z| := by
  let r := R * exp s
  let F := shiftedPhaseProfile W
  let H := (π/2+2)/π
  obtain ⟨hm, hb, hh, ha, _⟩ := P.nonneg
  have hg : 1 ≤ |c+2| := (by linarith [hc.1] : 1 ≤ c+2).trans (le_abs_self _)
  have h1 := weighted_phaseKernel r (mul_nonneg hm (abs_nonneg z)) (P.mixed_le z c hc)
  have h2 := (phaseKernel_logShift_zeroWeight (R := R) (z := s) hb (P.base_le c hc)).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))
  have h3 := weighted_phaseKernel (c := c+2) r (mul_nonneg hh (abs_nonneg z))
    ((P.shift_le z c hc).trans (le_mul_of_one_le_right (by positivity) hg))
  have h4 := (phaseKernel_logShift_zeroWeight (R := R) (z := s) (c := c+2) ha
    ((P.size_le c hc).trans (le_mul_of_one_le_right ha hg))).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))
  calc
    _ = |(F z c - F 0 c - (W (-z)-W 0)) * phaseKernel r c +
      (F 0 c - W 0) * (phaseKernel r c - phaseKernel R c) +
      (F z c - F 0 c) * phaseKernel r (c+2) +
      F 0 c * (phaseKernel r (c+2) - phaseKernel R (c+2))| := by
        simp only [phaseIntegrand, F, r]; congr 1; ring
    _ ≤ _ := abs_four_add _ _ _ _
    _ ≤ (P.mixed * |z|) * H + P.base/π * |z| + (P.shift * |z|) * H + P.size/π * |z| :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp [H]; ring

private theorem phase_regular_integral_bound {D : ℝ} (hD : 0 < D) (hD' : D < 1)
    {W : ℝ → ℝ} (hW : Continuous W) (P : ProfileBounds D W) :
    ∃ C ≥ (0 : ℝ), ∀ R z s : ℝ, |s| ≤ |z| →
      |(∫ c in (-D)..D, phaseIntegrand W (R*exp s) z c) -
        (∫ c in (-D)..D, phaseIntegrand W R 0 c) -
        W (-z) * phaseReference D (R*exp s) + W 0 * phaseReference D R| ≤ C * |z| := by
  let C := P.mixed * ((π/2+2)/π) + P.base/π + P.shift * ((π/2+2)/π) + P.size/π
  obtain ⟨hm, hb, hh, ha, _⟩ := P.nonneg
  refine ⟨C*(2*D), by dsimp [C]; positivity, ?_⟩
  intro R z s hs
  let r := R * exp s
  let f := phaseIntegrand W r z
  let g := phaseIntegrand W R 0
  let a (c : ℝ) := W (-z) * phaseKernel r c
  let b (c : ℝ) := W 0 * phaseKernel R c
  have hf : IntervalIntegrable f volume (-D) D := phaseIntegrand_int hD hD' hW _ _
  have hg : IntervalIntegrable g volume (-D) D := phaseIntegrand_int hD hD' hW _ _
  have ha : IntervalIntegrable a volume (-D) D := (phaseKernel_int _ _ _).const_mul _
  have hb : IntervalIntegrable b volume (-D) D := (phaseKernel_int _ _ _).const_mul _
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := -D) (b := D)
    (f := fun c ↦ f c - g c - a c + b c) (C := C * |z|) (fun c hc ↦ by
      rw [uIoc_of_le (show -D ≤ D by linarith)] at hc
      simpa only [Real.norm_eq_abs] using phase_integrand_regular_bound hD' P R z s c hs
        (Ioc_subset_Icc_self hc))
  rw [intervalIntegral.integral_add (f := fun c ↦ f c - g c - a c)
    (g := b) ((hf.sub hg).sub ha) hb, intervalIntegral.integral_sub (f := fun c ↦ f c-g c)
    (g := a) (hf.sub hg) ha, intervalIntegral.integral_sub hf hg, Real.norm_eq_abs] at hi
  simp only [a, b, intervalIntegral.integral_const_mul] at hi
  change |(∫ c in (-D)..D, f c) - (∫ c in (-D)..D, g c) -
    W (-z) * (∫ c in (-D)..D, phaseKernel r c) +
    W 0 * (∫ c in (-D)..D, phaseKernel R c)| ≤ C*(2*D)*|z|
  exact hi.trans_eq (by rw [abs_of_nonneg (by linarith : 0 ≤ D - -D)]; ring)

private theorem phaseReference_logMove {D R : ℝ} (hD : 0 < D) (hR : 0 < R) (s : ℝ) :
    |phaseReference D (R*exp s) - phaseReference D R| ≤ (2/π)*(π/2+2) * |s| := by
  have h1 := phaseReference_exp D hD (log R+s)
  have h0 := phaseReference_exp D hD (log R)
  rw [exp_add, exp_log hR] at h1
  rw [exp_log hR] at h0
  rw [h1, h0, add_sub_add_left_eq_sub]
  simpa using logReference_move D (log R) (log R+s)

/-- The finite radius shift law with its precise singular coefficient. The constants are
uniform in both the original radius and the log shift on the fixed reciprocal phase interval. -/
theorem exists_fixedPhaseTrace_sub_log_le {D : ℝ} (hD : 0 < D) (hD' : D < 1)
    (W V : ℝ → ℝ) {M N K : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hsize : ∀ t, |W t| ≤ M) (hW : ∀ t, HasDerivAt W (V t) t)
    (hder : ∀ t, |V t| ≤ N) (hLip : ∀ t u, |V t - V u| ≤ K * |t-u|) :
    ∃ C ≥ (0 : ℝ), ∀ R ≥ (1 : ℝ), ∀ z : ℝ,
      |fixedPhaseTrace D W R z - fixedPhaseTrace D W R 0 - (W (-z) - W 0) * log R|
        ≤ C * |z| := by
  let P := profileBounds_of_smooth hD hD' W V hM hN hK hsize hW hder hLip
  have hcont : Continuous W := continuous_iff_continuousAt.mpr fun t ↦ (hW t).continuousAt
  obtain ⟨A, hA, hreg⟩ := phase_regular_integral_bound hD hD' hcont P
  obtain ⟨B, hB, href⟩ := exists_phaseReference_sub_log_bound hD
  let U := (2/π)*(π/2+2)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  refine ⟨A + M*U + P.lip*B, by have := P.nonneg.2.2.2.2; positivity, ?_⟩
  intro R hR z
  let s := min 0 z
  have hs : |s| ≤ |z| := by rcases le_total 0 z with h | h <;> simp [s, h]
  have hre : min 1 (exp z) = exp s := by
    rcases le_total 0 z with h | h
    · simp [s, h, one_le_exp_iff.mpr h]
    · simp [s, h, exp_le_one_iff.mpr h]
  let r := R*exp s
  let a := W (-z)
  let b := W 0
  have hreg' : |fixedPhaseTrace D W R z - fixedPhaseTrace D W R 0 -
      a * phaseReference D r + b * phaseReference D R| ≤ A*|z| := by
    simpa only [fixedPhaseTrace, hre, exp_zero, min_self, mul_one, phaseIntegrand, a, b, r]
      using hreg R z s hs
  have hmove := (phaseReference_logMove hD (zero_lt_one.trans_le hR) s).trans
    (mul_le_mul_of_nonneg_left hs hU)
  have hc1 : |a * (phaseReference D r - phaseReference D R)| ≤ M * (U*|z|) := by
    rw [abs_mul]
    exact mul_le_mul (hsize (-z)) hmove (abs_nonneg _) hM
  have hc2 : |(a-b)*(phaseReference D R-log R)| ≤ (P.lip*|z|)*B := by
    rw [abs_mul]
    exact mul_le_mul (P.lip_le z) (href R hR) (abs_nonneg _)
      (mul_nonneg P.nonneg.2.2.2.2 (abs_nonneg z))
  let q := fixedPhaseTrace D W R z - fixedPhaseTrace D W R 0 -
    a * phaseReference D r + b * phaseReference D R
  let v := a * (phaseReference D r - phaseReference D R)
  let t := (a-b)*(phaseReference D R-log R)
  calc
    _ = |q+v+t| := by dsimp [q, v, t, a, b]; congr 1; ring
    _ ≤ |q|+|v|+|t| := by linarith [abs_add_le q v, abs_add_le (q+v) t]
    _ ≤ A*|z| + M*(U*|z|) + (P.lip*|z|)*B := add_le_add (add_le_add hreg' hc1) hc2
    _ = _ := by ring

/-- Compact `C²` data automatically have all the global bounds in the fixed-window law. -/
theorem exists_fixedPhaseTrace_sub_log_le_of_contDiff {D : ℝ} (hD : 0 < D) (hD' : D < 1)
    {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) (hs : HasCompactSupport W) :
    ∃ C ≥ (0 : ℝ), ∀ R ≥ (1 : ℝ), ∀ z : ℝ,
      |fixedPhaseTrace D W R z - fixedPhaseTrace D W R 0 - (W (-z) - W 0) * log R|
        ≤ C * |z| := by
  have hV : ContDiff ℝ 1 (deriv W) := hW.deriv'
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hW.continuous
  obtain ⟨N, hN⟩ := hs.deriv.exists_bound_of_continuous hV.continuous
  obtain ⟨K, hK⟩ := hs.deriv.deriv.exists_bound_of_continuous hV.continuous_deriv_one
  refine exists_fixedPhaseTrace_sub_log_le hD hD' W (deriv W) ((norm_nonneg _).trans (hM 0))
    ((norm_nonneg _).trans (hN 0)) ((norm_nonneg _).trans (hK 0)) hM
    (fun t ↦ ((hW.differentiable (by norm_num)) t).hasDerivAt) hN ?_
  intro t u
  exact (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ ↦ ((hV.differentiable one_ne_zero) v).hasDerivAt.hasDerivWithinAt)
    (fun v _ ↦ hK v) (mem_univ u) (mem_univ t)

/-- The direct and reflected phases integrated between the two translated endpoints of the
original compact radial interval. The coefficient includes its physical half-density. -/
def movingPhaseTrace (δ : ℝ) (w : ℝ → ℝ) (R z : ℝ) : ℝ :=
  ∫ c in (exp (-z)*(1-δ)-1)..(exp (-z)*(1+δ)-1),
    (w (exp (-z)/(1+c)) / sqrt (1+c)) *
      (phaseKernel (R * min 1 (exp z)) c + phaseKernel (R * min 1 (exp z)) (c+2))

/-- Extending the integration interval beyond both moving bounds adds zero for the original
radial test. The statement includes both phase endpoints and the reciprocal Haar half-density. -/
theorem movingPhaseTrace_eq_fixed {δ D : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) (hD' : D < 1)
    {w : ℝ → ℝ} (hs : ∀ g, g ∉ Icc (1+δ)⁻¹ (1-δ)⁻¹ → w g = 0) (R z : ℝ)
    (hl : -D ≤ exp (-z)*(1-δ)-1) (hr : exp (-z)*(1+δ)-1 ≤ D) :
    movingPhaseTrace δ w R z = fixedPhaseTrace D (fun y ↦ w (exp y)) R z := by
  let a := exp (-z)*(1-δ)-1
  let b := exp (-z)*(1+δ)-1
  let r := R * min 1 (exp z)
  let f (c : ℝ) := (w (exp (-z)/(1+c)) / sqrt (1+c)) *
    (phaseKernel r c + phaseKernel r (c+2))
  have hab : a ≤ b := by dsimp [a, b]; nlinarith [mul_pos (exp_pos (-z)) hδ]
  have hDD := hl.trans (hab.trans hr)
  have hp (c : ℝ) (hc : c ∈ Icc (-D) D) : 0 < 1+c := by linarith [hc.1]
  have he (c : ℝ) (hc : c ∈ Icc (-D) D) : exp (-log (1+c)-z) = exp (-z)/(1+c) := by
    rw [show -log (1+c)-z = -z-log (1+c) by ring, exp_sub, exp_log (hp c hc)]
  have hsub : Icc a b ⊆ Icc (-D) D := Icc_subset_Icc hl hr
  have hsupp (c : ℝ) (hc : c ∈ Icc (-D) D \ Icc a b) : f c = 0 := by
    have hz : w (exp (-z)/(1+c)) = 0 := by
      apply hs
      intro hg
      apply hc.2
      obtain ⟨hg1, hg2⟩ := hg
      rw [← one_div, div_le_div_iff₀ (by linarith : 0 < 1+δ) (hp _ hc.1)] at hg1
      rw [← one_div, div_le_div_iff₀ (hp _ hc.1) (by linarith : 0 < 1-δ)] at hg2
      exact ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
    simp [f, hz]
  calc movingPhaseTrace δ w R z = ∫ c in a..b, f c := rfl
       _ = ∫ c in (-D)..D, f c := by
          rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hDD,
            ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
          exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub hsupp).symm
       _ = _ := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hDD]
          intro c hc
          simp only [f, shiftedPhaseProfile, he c hc, r]

/-- A radial test supported in a compact positive interval has compact support in log
coordinates, for any pointed target. -/
theorem hasCompactSupport_comp_exp_of_radialWindow {E : Type*} [Zero E]
    {a b : ℝ} (ha : 0 < a) {w : ℝ → E} (hs : ∀ g, g ∉ Icc a b → w g = 0) :
    HasCompactSupport (fun t : ℝ ↦ w (exp t)) := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal (t := Icc (log a) (log b)) _ isClosed_Icc
  intro t ht
  by_contra hout
  have he : exp t ∉ Icc a b := fun hg ↦ hout
    ⟨by simpa using log_le_log ha hg.1, by simpa using log_le_log (exp_pos t) hg.2⟩
  exact ht (hs _ he)

/-- With the native compact radial support hypothesis the moving-window residual is Lipschitz
in log shift near zero, uniformly over every effective cutoff radius `R ≥ 1`. -/
theorem exists_movingPhaseTrace_sub_log_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w)
    (hs : ∀ g, g ∉ Icc (1+δ)⁻¹ (1-δ)⁻¹ → w g = 0) :
    ∃ C ≥ (0 : ℝ), ∃ d > (0 : ℝ), ∀ R ≥ (1 : ℝ), ∀ z : ℝ, |z| ≤ d →
      |movingPhaseTrace δ w R z - movingPhaseTrace δ w R 0 -
        (w (exp (-z)) - w 1) * log R| ≤ C * |z| := by
  let D := (1+δ)/2
  have hl : δ < D := by dsimp [D]; linarith
  have hD : 0 < D := hδ.trans hl
  have hD' : D < 1 := by dsimp [D]; linarith
  let W (t : ℝ) := w (exp t)
  have hw' : ContDiff ℝ 2 W := hw.comp contDiff_exp
  have ha : 0 < (1+δ)⁻¹ := by positivity
  have hwc : HasCompactSupport W := hasCompactSupport_comp_exp_of_radialWindow ha hs
  obtain ⟨C, hC, hfix⟩ := exists_fixedPhaseTrace_sub_log_le_of_contDiff hD hD' hw' hwc
  have hboth : ∀ᶠ z : ℝ in 𝓝 0, -D < exp (-z)*(1-δ)-1 ∧ exp (-z)*(1+δ)-1 < D := by
    have hleft : Continuous (fun z : ℝ ↦ exp (-z)*(1-δ)-1) := by fun_prop
    have hright : Continuous (fun z : ℝ ↦ exp (-z)*(1+δ)-1) := by fun_prop
    exact (continuousAt_const.eventually_lt hleft.continuousAt (by simpa using neg_lt_neg hl)).and
      (hright.continuousAt.eventually_lt continuousAt_const (by simpa using hl))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hboth
  refine ⟨C, hC, d/2, half_pos hd, ?_⟩
  intro R hR z hz
  have hz' : z ∈ Metric.ball (0:ℝ) d := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
  obtain ⟨hzl, hzr⟩ := hball hz'
  obtain ⟨h0l, h0r⟩ := hball (Metric.mem_ball_self hd)
  rw [movingPhaseTrace_eq_fixed hδ hδ' hD' hs R z hzl.le hzr.le,
      movingPhaseTrace_eq_fixed hδ hδ' hD' hs R 0 h0l.le h0r.le]
  simpa only [W, exp_zero] using hfix R hR z

end RiemannMasullo.ThroughOneStability
