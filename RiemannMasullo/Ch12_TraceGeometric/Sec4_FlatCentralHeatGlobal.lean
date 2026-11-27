module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Global bounds for the sharp sine-integral phases of a translated positive Haar window. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace RiemannMasullo.ThroughOneStability

/-- The totalized direct kernel is bounded by twice its nonnegative cutoff, even at phase zero. -/
theorem abs_phaseKernel_le_scale {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    |phaseKernel s c| ≤ 2 * s := by
  by_cases hc : c = 0
  · simp [phaseKernel, hc, hs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * π * c * s) (f := sinc) (C := 1)
    (fun x _ ↦ by simpa only [Real.norm_eq_abs] using abs_sinc_le_one x)
  have hsi : |∫ t in (0 : ℝ)..2 * π * c * s, sinc t| ≤ |2 * π * c * s| := by
    simpa only [Real.norm_eq_abs, sub_zero, one_mul] using h
  rw [phaseKernel, abs_mul, abs_inv, abs_mul, abs_of_pos pi_pos]
  calc
    _ ≤ (π * |c|)⁻¹ * |2 * π * c * s| := mul_le_mul_of_nonneg_left hsi (by positivity)
    _ = 2 * s := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_pos pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
      field_simp [pi_ne_zero, abs_ne_zero.mpr hc]

/-- Multiplication by the phase gives a uniform bound independently of the cutoff. -/
theorem abs_mul_phaseKernel_le_two (s c : ℝ) : |c| * |phaseKernel s c| ≤ 2 := by
  by_cases hc : c = 0
  · simp [hc]
  calc
    _ = |∫ t in (0 : ℝ)..2 * π * c * s, sinc t| / π := by
      rw [phaseKernel, abs_mul, abs_inv, abs_mul, abs_of_pos pi_pos]
      field_simp [pi_ne_zero, abs_ne_zero.mpr hc]
    _ ≤ 2 := (div_le_iff₀ pi_pos).2 ((abs_integral_sinc_le _).trans (by linarith [pi_gt_three]))

private theorem continuous_inv_abs (e k : ℝ) (he : 0 < e) :
    Continuous fun g : ℝ ↦ (e + |g - k|)⁻¹ :=
  (continuous_const.add ((continuous_id.sub continuous_const).abs)).inv₀
    (fun _ ↦ ne_of_gt (add_pos_of_pos_of_nonneg he (abs_nonneg _)))

private theorem integral_inv_abs_left {e a k : ℝ} (he : 0 < e) (ha : a ≤ k) :
    (∫ g in a..k, (e + |g-k|)⁻¹) = log ((e + (k-a))/e) := by
  calc
    _ = ∫ g in a..k, ((e+k)-g)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro g hg
      rw [uIcc_of_le ha] at hg
      dsimp only
      rw [abs_of_nonpos (sub_nonpos.mpr hg.2)]
      congr 1
      ring
    _ = ∫ x in (e+k)-k..(e+k)-a, x⁻¹ := intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x⁻¹) (e+k)
    _ = _ := by
      rw [integral_inv_of_pos (by linarith) (by linarith)]
      congr 2 <;> ring

private theorem integral_inv_abs_right {e k b : ℝ} (he : 0 < e) (hb : k ≤ b) :
    (∫ g in k..b, (e + |g-k|)⁻¹) = log ((e + (b-k))/e) := by
  calc
    _ = ∫ g in k..b, (g+(e-k))⁻¹ := by
      apply intervalIntegral.integral_congr
      intro g hg
      rw [uIcc_of_le hb] at hg
      dsimp only
      rw [abs_of_nonneg (sub_nonneg.mpr hg.1)]
      congr 1
      ring
    _ = ∫ x in k+(e-k)..b+(e-k), x⁻¹ := intervalIntegral.integral_comp_add_right (fun x : ℝ ↦ x⁻¹) (e-k)
    _ = _ := by
      rw [integral_inv_of_pos (by linarith) (by linarith)]
      congr 2 <;> ring

/-- The reciprocal distance to an arbitrary moving center has at most logarithmic window mass. -/
theorem integral_inv_add_abs_sub_le {a b e : ℝ} (hab : a ≤ b) (he : 0 < e) (k : ℝ) :
    (∫ g in a..b, (e + |g - k|)⁻¹) ≤ 2 * log ((e + (b-a))/e) := by
  let j := max a (min k b)
  have haj : a ≤ j := le_max_left _ _
  have hjb : j ≤ b := max_le hab (min_le_right _ _)
  have hdist (g : ℝ) (hg : g ∈ Icc a b) : |g-j| ≤ |g-k| := by
    rcases le_or_gt k a with h | h
    · have hk : j = a := max_eq_left ((min_le_left k b).trans h)
      rw [hk, abs_of_nonneg (sub_nonneg.mpr hg.1), abs_of_nonneg (sub_nonneg.mpr (h.trans hg.1))]
      linarith
    rcases le_or_gt k b with h' | h'
    · simp [j, min_eq_left h', max_eq_right h.le]
    · have hk : j = b := by simp [j, min_eq_right h'.le, max_eq_right hab]
      rw [hk, abs_of_nonpos (sub_nonpos.mpr hg.2), abs_of_nonpos (sub_nonpos.mpr (hg.2.trans h'.le))]
      linarith
  have hF (s x y : ℝ) := (continuous_inv_abs e s he).intervalIntegrable (μ := volume) x y
  calc
    _ ≤ ∫ g in a..b, (e + |g-j|)⁻¹ :=
      intervalIntegral.integral_mono_on hab (hF k a b) (hF j a b) fun g hg ↦
        inv_anti₀ (add_pos_of_pos_of_nonneg he (abs_nonneg _)) (add_le_add_right (hdist g hg) _)
    _ = (∫ g in a..j, (e + |g-j|)⁻¹) + ∫ g in j..b, (e + |g-j|)⁻¹ :=
      (intervalIntegral.integral_add_adjacent_intervals (hF j a j) (hF j j b)).symm
    _ ≤ _ := by
      rw [integral_inv_abs_left he haj, integral_inv_abs_right he hjb, two_mul]
      apply add_le_add
      · apply log_le_log (by positivity)
        gcongr
      · apply log_le_log (by positivity)
        gcongr

/-- The half-density controls both far ends of the positive Haar axis. Only a reciprocal
distance from the moving seam remains in this bound. -/
theorem sqrt_mul_abs_phasePair_le {g u s R b : ℝ} (hg : 0 < g) (hu : 0 < u) (hgb : g ≤ b)
    (hR : 0 < R) (hs : 0 ≤ s) (hsR : s ≤ R) :
    sqrt ((g*u)⁻¹) * |phaseKernel s ((g*u)⁻¹-1) + phaseKernel s ((g*u)⁻¹+1)| ≤
      4 + (2+2*b) * (R⁻¹ + |g-u⁻¹|)⁻¹ := by
  let x := (g*u)⁻¹
  have hx : 0 < x := inv_pos.mpr (mul_pos hg hu)
  have hxs : sqrt x ≤ 1 + |x-1| := by
    rcases le_or_gt x 1 with h | h
    · exact (Real.sqrt_le_one.mpr h).trans (le_add_of_nonneg_right (abs_nonneg _))
    · rw [abs_of_nonneg (sub_nonneg.mpr h.le)]
      have h' : sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (.inr h.le)
      linarith
  have hxt : sqrt x ≤ x+1 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg x]⟩
  have he : g*(x-1) = u⁻¹-g := by
    dsimp only [x]
    field_simp
  have hdist : |g-u⁻¹| = g*|x-1| := by
    rw [abs_sub_comm g, ← he, abs_mul, abs_of_pos hg]
  let p := |phaseKernel s (x-1)|
  let q := |phaseKernel s (x+1)|
  have hp : |x-1| *p ≤ 2 := abs_mul_phaseKernel_le_two _ _
  have hq : (x+1)*q ≤ 2 := by
    simpa only [abs_of_pos (by linarith : 0 < x+1)] using abs_mul_phaseKernel_le_two s (x+1)
  have hz : 0 < R⁻¹ + |g-u⁻¹| := add_pos_of_pos_of_nonneg (inv_pos.mpr hR) (abs_nonneg _)
  have hnear : p ≤ (2+2*b) * (R⁻¹+|g-u⁻¹|)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hz).mpr
    calc
      p * (R⁻¹+|g-u⁻¹|) = p/R + g*(|x-1| *p) := by rw [hdist]; ring
      _ ≤ 2 + g*2 := add_le_add ((div_le_iff₀ hR).mpr ((abs_phaseKernel_le_scale hs _).trans
        (mul_le_mul_of_nonneg_left hsR (by norm_num)))) (mul_le_mul_of_nonneg_left hp hg.le)
      _ ≤ _ := by linarith
  calc
    _ ≤ sqrt x * (p+q) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (sqrt_nonneg _)
    _ = sqrt x*p + sqrt x*q := mul_add _ _ _
    _ ≤ (1+|x-1|)*p + (x+1)*q := add_le_add
      (mul_le_mul_of_nonneg_right hxs (abs_nonneg _)) (mul_le_mul_of_nonneg_right hxt (abs_nonneg _))
    _ ≤ _ := by rw [add_mul, one_mul]; linarith

/-- The sharp direct and reflected phases at displacement multiplier `u`, integrated against
the positive Haar measure on the original fixed window. -/
def shiftedHaarPhase (w : ℝ → ℝ) (a b s u : ℝ) : ℝ :=
  ∫ g in a..b, (w g / g) * sqrt ((g*u)⁻¹) *
    (phaseKernel s ((g*u)⁻¹-1) + phaseKernel s ((g*u)⁻¹+1))

/-- An explicit bound uniform in every positive displacement multiplier and every cutoff
between zero and `R`. Only a bound for the profile on the fixed interval is needed. -/
theorem shiftedHaarPhase_bound_of_cutoff_le {a b M R s u : ℝ} {w : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hM : 0 ≤ M) (hw : ∀ g ∈ Icc a b, |w g| ≤ M)
    (hR : 1 ≤ R) (hs : 0 ≤ s) (hsR : s ≤ R) (hu : 0 < u) :
    |shiftedHaarPhase w a b s u| ≤
      M/a * (4*(b-a)+(2+2*b)*(2*(log (1+(b-a))+log R))) := by
  have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he : 0 < R⁻¹ := inv_pos.mpr hR'
  have hb : 0 < b := ha.trans_le hab
  have hba := sub_nonneg.mpr hab
  let G (g : ℝ) := (R⁻¹+|g-u⁻¹|)⁻¹
  have hG : Continuous G := continuous_inv_abs _ _ he
  have hweight : 0 ≤ M/a := div_nonneg hM ha.le
  have hcap (g : ℝ) (hg : g ∈ Icc a b) :
      ‖w g / g * sqrt ((g*u)⁻¹) * (phaseKernel s ((g*u)⁻¹-1) + phaseKernel s ((g*u)⁻¹+1))‖ ≤
        M/a * (4+(2+2*b)*G g) := by
    have hg0 : 0 < g := ha.trans_le hg.1
    have h1 : |w g|/g ≤ M/a :=
      (div_le_div_of_nonneg_right (hw g hg) hg0.le).trans (div_le_div_of_nonneg_left hM ha hg.1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos hg0, abs_of_nonneg (sqrt_nonneg _), mul_assoc]
    exact mul_le_mul h1 (sqrt_mul_abs_phasePair_le hg0 hu hg.2 hR' hs hsR)
      (mul_nonneg (sqrt_nonneg _) (abs_nonneg _)) hweight
  have hlog : log ((R⁻¹+(b-a))/R⁻¹) ≤ log (1+(b-a)) + log R := by
    rw [← log_mul (by positivity : 1+(b-a) ≠ 0) hR'.ne']
    have hi : (R⁻¹+(b-a))/R⁻¹ = 1+(b-a)*R := by field_simp
    rw [hi]
    apply log_le_log (by positivity)
    linarith
  have hmass : (∫ g in a..b, G g) ≤ 2*(log (1+(b-a)) + log R) :=
    (integral_inv_add_abs_sub_le hab he u⁻¹).trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
  calc
    _ ≤ ∫ g in a..b, (M/a) * (4+(2+2*b)*G g) := by
      rw [shiftedHaarPhase, ← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le hab (.of_forall fun g hg ↦ hcap g (Ioc_subset_Icc_self hg))
      exact (continuous_const.mul (continuous_const.add (continuous_const.mul hG))).intervalIntegrable _ _
    _ = M/a * (4*(b-a)+(2+2*b)*(∫ g in a..b, G g)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (f := fun _ : ℝ ↦ (4 : ℝ)) (g := fun x : ℝ ↦ (2+2*b)*G x)
        intervalIntegrable_const ((continuous_const.mul hG).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, mul_comm (b-a)]
    _ ≤ _ := by gcongr

/-- The genuine logarithmic displacement has a single uniform logarithmic majorant,
including all shifts of either sign and profiles crossing the reciprocal phase zero. -/
theorem shiftedHaarPhase_global_bound {a b M : ℝ} {w : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hM : 0 ≤ M) (hw : ∀ g ∈ Icc a b, |w g| ≤ M)
    {R : ℝ} (hR : 1 ≤ R) (z : ℝ) :
    |shiftedHaarPhase w a b (R*min 1 (exp z)) (exp z)| ≤
      (M/a * (4*(b-a)+(4+4*b)*(1+log (1+(b-a))))) * (1+log R) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hs : 0 ≤ R*min 1 (exp z) := mul_nonneg hR0 (le_min zero_le_one (exp_pos _).le)
  have hsR : R*min 1 (exp z) ≤ R := mul_le_of_le_one_right hR0 (min_le_left _ _)
  refine (shiftedHaarPhase_bound_of_cutoff_le ha hab hM hw hR hs hsR (exp_pos z)).trans ?_
  have hl := log_nonneg (show 1 ≤ 1+(b-a) by linarith)
  have hr := log_nonneg hR
  have hb := ha.trans_le hab
  have hd : 4*(b-a) ≤ 4*(b-a)*(1+log R) :=
    le_mul_of_one_le_right (by linarith) (by linarith)
  have hz : log (1+(b-a))+log R ≤ (1+log (1+(b-a)))*(1+log R) := by
    nlinarith [mul_nonneg hl hr]
  calc
    _ ≤ M/a * (4*(b-a)*(1+log R)+(2+2*b)*(2*((1+log (1+(b-a)))*(1+log R)))) := by gcongr
    _ = _ := by ring

/-- For a continuous profile the constant can be chosen before either the cutoff or the shift. -/
theorem exists_shiftedHaarPhase_global_bound {a b : ℝ} {w : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) :
    ∃ C ≥ 0, ∀ R ≥ 1, ∀ z : ℝ,
      |shiftedHaarPhase w a b (R*min 1 (exp z)) (exp z)| ≤ C * (1+log R) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  have hba := sub_nonneg.mpr hab
  have hb := ha.trans_le hab
  have hl := log_nonneg (show 1 ≤ 1+(b-a) by linarith)
  refine ⟨M/a * (4*(b-a)+(4+4*b)*(1+log (1+(b-a)))), by positivity, ?_⟩
  intro R hR z
  exact shiftedHaarPhase_global_bound ha hab hM0
    (fun g hg ↦ by simpa only [Real.norm_eq_abs] using hM g hg) hR z

end RiemannMasullo.ThroughOneStability
