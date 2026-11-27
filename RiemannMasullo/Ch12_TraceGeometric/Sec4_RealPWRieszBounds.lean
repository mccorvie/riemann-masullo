module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWActualCutoffs
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWJetTrials
import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerReproducer
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Sharp evaluation bounds at infinity in the actual interval weight -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace SchwartzMap Topology

namespace RiemannMasullo.Isolated

/-- Fold at the midpoint before translating. On the positive half-line both envelopes
are dominated by the one belonging to the nearer center. -/
private theorem folded_packet_limit {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (he : ∀ t, φ (-t) = φ t) (H : ℂ → ℂ → ℝ)
    (hc : Continuous (fun p : ℂ × ℂ ↦ H p.1 p.2)) (hsym : ∀ a b, H a b = H b a)
    (hb : ∀ a b, |H a b| ≤ (‖a‖ + ‖b‖)^2) :
    Tendsto (fun x ↦ realPWIntervalWeight α s x *
      ∫ y, H (φ (y-x)) (φ (y+x)) / realPWIntervalWeight α s y)
      atTop (𝓝 (2 * ∫ t, H (φ t) 0)) := by
  classical
  let w := realPWIntervalWeight α s
  have hw : Measurable w := measurable_realPWIntervalWeight α s
  have hw0 (x : ℝ) : 0 ≤ w x := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  have hwe (x : ℝ) : w (-x) = w x := by simp [w, realPWIntervalWeight]
  obtain ⟨B,hB,hdom⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  have hB0 : 0 ≤ B := by
    have h := hdom 4 le_rfl 0
    simp only [abs_zero, add_zero, inv_one, mul_one] at h
    exact (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)).trans h
  let G (t : ℝ) := B*(1+|t|)⁻¹
  let F (x t : ℝ) := if 0 < x+t then H (φ t) (φ (x+t+x)) * (w x / w (x+t)) else 0
  have hf : Tendsto (fun x ↦ ∫ t, F x t) atTop (𝓝 (∫ t, H (φ t) 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t ↦ 4 * G t ^ 2)
    · apply Eventually.of_forall
      intro x
      apply Measurable.aestronglyMeasurable
      apply Measurable.ite (measurableSet_lt measurable_const (measurable_const.add measurable_id)) _ measurable_const
      exact (hc.measurable.comp (φ.continuous.measurable.prodMk (φ.continuous.measurable.comp
        ((measurable_const.add measurable_id).add measurable_const)))).mul
          (measurable_const.div (hw.comp (measurable_const.add measurable_id)))
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
      apply ae_of_all
      intro t
      by_cases ht : 0 < x+t
      · let q := Real.sqrt (w x / w (x+t))
        have hq : 0 ≤ q := Real.sqrt_nonneg _
        have hqq : q^2 = w x / w (x+t) := Real.sq_sqrt (div_nonneg (hw0 _) (hw0 _))
        have h1 : ‖φ t‖ * q ≤ G t := hdom x hx t
        have h2 := hdom x hx (-(x+t+x))
        rw [he, abs_neg, show x + -(x+t+x) = -(x+t) by ring, realPWIntervalWeight_even] at h2
        have hab : |t| ≤ |x+t+x| := by rw [abs_of_nonneg (show 0 ≤ x+t+x by linarith)]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        have h2' : ‖φ (x+t+x)‖ * q ≤ G t := h2.trans (mul_le_mul_of_nonneg_left
          (inv_anti₀ (by positivity : 0 < 1 + |t|) (by linarith only [hab])) hB0)
        have hsum : (‖φ t‖ + ‖φ (x+t+x)‖)*q ≤ 2*G t := by linarith [add_mul ‖φ t‖ ‖φ (x+t+x)‖ q]
        simp only [F, ite_eq_left ht, Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (hw0 _) (hw0 _))]
        calc
          _ ≤ (‖φ t‖ + ‖φ (x+t+x)‖)^2 * q^2 := by rw [hqq]; exact mul_le_mul_of_nonneg_right (hb _ _) (div_nonneg (hw0 _) (hw0 _))
          _ = ((‖φ t‖ + ‖φ (x+t+x)‖)*q)^2 := (mul_pow ..).symm
          _ ≤ (2*G t)^2 := pow_le_pow_left₀ (by positivity) hsum 2
          _ = _ := by ring
      · simp only [F, ite_eq_right ht, norm_zero]; positivity
    · exact hB.integrable_sq.const_mul 4
    · apply ae_of_all
      intro t
      have htop : Tendsto (fun x : ℝ ↦ x+t+x) atTop atTop := tendsto_atTop.2 fun b ↦ by
        filter_upwards [eventually_ge_atTop (max 0 (b-t))] with x hx
        linarith [le_max_left (0:ℝ) (b-t), le_max_right (0:ℝ) (b-t)]
      have hz := ZeroAtInftyContinuousMapClass.zero_at_infty φ
      rw [cocompact_eq_atBot_atTop] at hz
      have hφ : Tendsto (fun x : ℝ ↦ φ (x+t+x)) atTop (𝓝 0) := (hz.mono_left le_sup_right).comp htop
      have hH := hc.continuousAt.tendsto.comp ((tendsto_const_nhds (x := φ t)).prodMk_nhds hφ)
      have hlim := hH.mul (tendsto_realPWIntervalWeight_translation_ratio α s t hs)
      simp only [mul_one, Function.comp_apply] at hlim
      apply hlim.congr'
      filter_upwards [eventually_gt_atTop (-t)] with x hx
      simp [F, show 0 < x+t by linarith, w]
  apply (hf.const_mul 2).congr' (Eventually.of_forall fun x ↦ ?_)
  let J (y : ℝ) := H (φ (y-x)) (φ (y+x)) / w y
  have hJ (y : ℝ) : J (-y) = J y := by
    dsimp [J]; rw [show -y-x = -(y+x) by ring, show -y+x = -(y-x) by ring, he, he, hwe, hsym]
  have hab (y : ℝ) : J |y| = J y := by rcases le_total 0 y with h|h <;> simp [abs_of_nonneg, abs_of_nonpos, h, hJ]
  have hfold := integral_comp_abs (f := J)
  simp only [hab] at hfold
  change 2 * (∫ t, F x t) = w x * ∫ y, J y
  suffices hEq : (∫ t, F x t) = w x * ∫ y in Ioi 0, J y by rw [hfold, hEq]; ring
  rw [← integral_const_mul, ← integral_indicator measurableSet_Ioi]
  calc
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator (fun y ↦ w x * J y) (x + t) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t ↦ by by_cases h : 0 < x+t <;>
        simp [F, J, Set.indicator, h, div_eq_mul_inv, mul_comm, mul_assoc]
    _ = _ := integral_add_left_eq_self _ x

private theorem tendsto_twoPacket_reproducer_energy {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (he : ∀ t, φ (-t) = φ t) {E : ℝ → ℝ}
    (hE : ∀ x, E x = ∫ y, ‖(2:ℂ)⁻¹ * (φ (y-x) + φ (y+x))‖^2 / realPWIntervalWeight α s y) :
    Tendsto (fun x ↦ realPWIntervalWeight α s x * E x) atTop (𝓝 ((∫ t, ‖φ t‖^2)/2)) := by
  have h := folded_packet_limit ha hs φ he (fun a b ↦ ‖(2:ℂ)⁻¹ * (a+b)‖^2) (by fun_prop)
    (fun a b ↦ by rw [add_comm]) (fun a b ↦ by
      rw [abs_of_nonneg (sq_nonneg _), norm_mul, norm_inv, Complex.norm_two]
      apply pow_le_pow_left₀ (by positivity)
      linarith [norm_add_le a b, norm_nonneg (a+b)])
  simp only [add_zero, norm_mul, norm_inv, Complex.norm_two, mul_pow, integral_const_mul] at h
  simpa only [hE, norm_mul, norm_inv, Complex.norm_two, mul_pow,
    show ∀ z : ℝ, 2 * ((2:ℝ)⁻¹ ^ 2 * z) = z / 2 from fun z ↦ by ring] using h

theorem exists_projected_twoPackets_tendsto_energy (Y : ℝ) {α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (he : ∀ t, φ (-t) = φ t)
    (hone : EqOn (𝓕⁻ (φ : ℝ → ℂ)) 1 (Icc (-Y) Y)) :
    ∃ r : ℝ → Lp ℂ 2 (realPWIntervalMeasure α s),
      (∀ x, ∀ᵐ t ∂volume, r x t = star ((2:ℂ)⁻¹ * (φ (t-x) + φ (t+x))) /
        (realPWIntervalWeight α s t : ℂ)) ∧
      (∀ x, RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x =
        (RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)).orthogonalProjectionOnto (r x)) ∧
      Tendsto (fun x ↦ realPWIntervalWeight α s x * ‖r x‖^2) atTop (𝓝 ((∫ t, ‖φ t‖^2)/2)) := by
  choose r hr hp hn using fun x ↦ RealPWBand.exists_evaluationVector_eq_projected_twoPackets Y x
    (measurable_realPWIntervalWeight α s) (one_le_realPWIntervalWeight α s hs)
    (volume_le_realPWIntervalMeasure α s hs) φ.integrable (φ.memLp 2 volume) hone
  exact ⟨r, hr, hp, tendsto_twoPacket_reproducer_energy ha hs φ he hn⟩

private theorem trialDecay (φ : 𝓢(ℝ, ℂ)) (k : ℕ) : ∃ B : ℝ, ∀ z : ℝ,
    (1 + |z|)^k * ‖φ z‖ ≤ B := by
  let S := (Finset.Iic ((k, 0) : ℕ × ℕ)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) φ
  refine ⟨2 ^ k * S, fun z ↦ ?_⟩
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0))
      (le_refl k) (le_refl 0) φ z

private def farTrialDensity (α s : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ) (x u : ℝ) :=
  if 4 ≤ x+u then realPWIntervalWeight α s (x+u) / realPWIntervalWeight α s x *
    (((x+u)/x)^k * ‖φ u + φ (x+u+x)‖)^2 else 0

private theorem farTrialDensity_meas (α s : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ) (x : ℝ) :
    Measurable (farTrialDensity α s φ k x) := by
  have hw := measurable_realPWIntervalWeight α s
  unfold farTrialDensity
  apply Measurable.ite (measurableSet_le measurable_const (measurable_const.add measurable_id))
  · apply Measurable.mul ((hw.comp (measurable_const.add measurable_id)).div measurable_const)
    apply Continuous.measurable
    fun_prop
  · exact measurable_const

private theorem farTrialDensity_bound {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (k : ℕ) : ∃ g : ℝ → ℝ, Integrable g ∧
    ∀ x : ℝ, 4 ≤ x → ∀ u, ‖farTrialDensity α s φ k x u‖ ≤ g u := by
  obtain ⟨C,N,hC⟩ := realPWIntervalWeight_translation_envelope ha hs
  obtain ⟨B,hB⟩ := trialDecay φ (N+k+1)
  let d (u : ℝ) := (1 + ‖u‖)⁻¹
  have hd : MemLp d 2 volume := by
    apply (integrable_norm_rpow_iff (by dsimp [d]; fun_prop) (by norm_num) (by norm_num)).mp
    have hn (u : ℝ) : ‖d u‖ = (1 + ‖u‖)⁻¹ := Real.norm_of_nonneg (by dsimp [d]; positivity)
    simpa only [hn, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := (2 : ENNReal).toReal) (by simp))
  let A := |C| * (2*B)
  have hD : MemLp (fun u ↦ A * d u) 2 volume := hd.const_smul A
  refine ⟨_, hD.integrable_sq, fun x hx u ↦ ?_⟩
  by_cases ht : 4 ≤ x+u
  · let b := 1+|u|
    have hb : 0 < b := by dsimp [b]; positivity
    have hx' : 1 ≤ x := by linarith
    have hr : 0 ≤ realPWIntervalWeight α s (x+u) / realPWIntervalWeight α s x :=
      div_nonneg (zero_le_one.trans (one_le_realPWIntervalWeight _ _ hs _))
        (zero_le_one.trans (one_le_realPWIntervalWeight _ _ hs _))
    have hratio := hC (x+u) ht (-u)
    rw [add_neg_cancel_right, abs_neg] at hratio
    have hrat : Real.sqrt (realPWIntervalWeight α s (x+u) / realPWIntervalWeight α s x) ≤ |C| * b^N :=
      hratio.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hb.le _))
    have hq : (x+u)/x ≤ b := by
      apply (div_le_iff₀ (by linarith : 0 < x)).2
      dsimp [b]; nlinarith [le_abs_self u, mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hx')]
    have hq0 : 0 ≤ (x+u)/x := div_nonneg (by linarith) (by linarith)
    have hz : |u| ≤ |x+u+x| := by rw [abs_of_nonneg (by linarith : 0 ≤ x+u+x)]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    have htail : b^(N+k+1) * ‖φ (x+u+x)‖ ≤ B :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le (show b ≤ 1 + |x+u+x| by
        dsimp [b]; linarith only [hz]) _) (norm_nonneg _)).trans (hB _)
    have hpair : b^(N+k+1) * ‖φ u + φ (x+u+x)‖ ≤ 2*B := by
      have h := mul_le_mul_of_nonneg_left (norm_add_le (φ u) (φ (x+u+x))) (pow_nonneg hb.le (N+k+1))
      rw [mul_add] at h
      linarith [show b^(N+k+1)*‖φ u‖ ≤ B from hB u]
    have hroot : Real.sqrt (realPWIntervalWeight α s (x+u) / realPWIntervalWeight α s x) *
        (((x+u)/x)^k * ‖φ u + φ (x+u+x)‖) ≤ A * d u := by
      have hmajor := mul_le_mul hrat
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq k) (norm_nonneg (φ u + φ (x+u+x))))
        (mul_nonneg (pow_nonneg hq0 _) (norm_nonneg _))
        (mul_nonneg (abs_nonneg C) (pow_nonneg hb.le _))
      apply hmajor.trans
      change _ ≤ A * (1 + ‖u‖)⁻¹
      rw [Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ hb]
      calc
        _ = |C| * (b^(N+k+1) * ‖φ u + φ (x+u+x)‖) := by change _ * b = _; rw [pow_succ, pow_add]; ring
        _ ≤ A := mul_le_mul_of_nonneg_left hpair (abs_nonneg C)
    have hh := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hq0 _) (norm_nonneg _))) hroot 2
    rw [mul_pow, Real.sq_sqrt hr] at hh
    simpa only [farTrialDensity, ite_eq_left ht, Real.norm_of_nonneg (mul_nonneg hr (sq_nonneg _))] using hh
  · simp only [farTrialDensity, ite_eq_right ht, norm_zero]; positivity

/-- In coordinates centred at the positive translate, the full two-packet energy on
`t ≥ 4` converges, including the opposite translate and the entire jet monomial. -/
private theorem tendsto_farTrialEnergy {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Tendsto (fun x : ℝ ↦ ∫ u : ℝ, if 4 ≤ x+u then realPWIntervalWeight α s (x+u) /
      realPWIntervalWeight α s x * (((x+u)/x)^k * ‖φ u + φ (x+u+x)‖)^2 else 0)
      atTop (𝓝 (∫ u : ℝ, ‖φ u‖^2)) := by
  change Tendsto (fun x ↦ ∫ u, farTrialDensity α s φ k x u) _ _
  obtain ⟨g,hg,hb⟩ := farTrialDensity_bound ha hs φ k
  apply tendsto_integral_filter_of_dominated_convergence g
  · exact Eventually.of_forall fun x ↦ (farTrialDensity_meas α s φ k x).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx using ae_of_all _ (hb x hx)
  · exact hg
  · apply ae_of_all
    intro u
    have hrat := (tendsto_realPWIntervalWeight_translation_ratio α s u hs).inv₀ (by norm_num)
    have hr : Tendsto (fun x ↦ realPWIntervalWeight α s (x+u) / realPWIntervalWeight α s x) atTop (𝓝 1) := by simpa only [inv_div, inv_one] using hrat
    have hq : Tendsto (fun x : ℝ ↦ (x+u)/x) atTop (𝓝 1) := by
      have h : Tendsto (fun x : ℝ ↦ u/x) atTop (𝓝 0) := tendsto_id.const_div_atTop _
      apply (show Tendsto (fun x : ℝ ↦ 1+u/x) atTop (𝓝 1) by simpa using h.const_add 1).congr'
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [add_div, div_self hx.ne']
    have ht : Tendsto (fun x : ℝ ↦ x+u+x) atTop atTop := by
      apply tendsto_atTop.2
      intro r
      filter_upwards [eventually_ge_atTop ((r-u)/2)] with x hx using by linarith
    have hφ := (φ.tendsto_cocompact.mono_left atTop_le_cocompact).comp ht
    have hnorm : Tendsto (fun x : ℝ ↦ ‖φ u + φ (x+u+x)‖) atTop (𝓝 ‖φ u‖) := by
      simpa using (hφ.const_add (φ u)).norm
    have hlim := hr.mul (((hq.pow k).mul hnorm).pow 2)
    apply (show Tendsto _ _ (𝓝 (‖φ u‖^2)) by simpa using hlim).congr'
    filter_upwards [eventually_ge_atTop (4-u)] with x hx
    simp [farTrialDensity, show 4 ≤ x+u by linarith]

/-- The compact piece only needs integrability of the singular scalar, not of the
weight itself. The monomial degree `k` gives the compensating power `2*k`. -/
private theorem tendsto_compactTrialEnergy {α s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (k : ℕ)
    {S : Set ℝ} (hS : IntegrableOn (fun t : ℝ ↦ realPWIntervalWeight α s t * (t^k)^2) S) :
    Tendsto (fun x : ℝ ↦ ∫ t in S, realPWIntervalWeight α s t / realPWIntervalWeight α s x *
      ((t/x)^k * ‖φ (t-x) + φ (t+x)‖)^2) atTop (𝓝 0) := by
  let W := realPWIntervalWeight α s
  let P (t : ℝ) := W t * (t^k)^2
  let F (x t : ℝ) := P t * ‖φ (t-x) + φ (t+x)‖^2
  obtain ⟨B,hB⟩ := trialDecay φ 0
  have hnorm (z : ℝ) : ‖φ z‖ ≤ B := by simpa using hB z
  have hP (t : ℝ) : 0 ≤ P t := mul_nonneg (zero_le_one.trans (one_le_realPWIntervalWeight _ _ hs _)) (sq_nonneg _)
  have hmP : Measurable P := (measurable_realPWIntervalWeight _ _).mul ((measurable_id.pow_const k).pow_const 2)
  have ht : Tendsto (fun x : ℝ ↦ ∫ t in S, F x t) atTop (𝓝 0) := by
    rw [show (0:ℝ) = ∫ _ : ℝ in S, (0:ℝ) by simp]
    apply tendsto_integral_filter_of_dominated_convergence (fun t ↦ P t * (2*B)^2)
    · apply Eventually.of_forall
      intro x
      exact (hmP.mul (show Continuous (fun t : ℝ ↦ ‖φ (t-x) + φ (t+x)‖^2) by fun_prop).measurable).aestronglyMeasurable
    · apply Eventually.of_forall
      intro x
      apply ae_of_all
      intro t
      have hpair := (norm_add_le (φ (t-x)) (φ (t+x))).trans (add_le_add (hnorm _) (hnorm _))
      dsimp only [F]
      rw [Real.norm_of_nonneg (mul_nonneg (hP _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖φ (t-x) + φ (t+x)‖ ≤ 2*B) 2) (hP _)
    · exact hS.mul_const _
    · apply ae_of_all
      intro t
      have hneg : Tendsto (fun x : ℝ ↦ t-x) atTop atBot := by
        apply tendsto_atBot.2
        intro r
        filter_upwards [eventually_ge_atTop (t-r)] with x hx using by linarith
      have hpos : Tendsto (fun x : ℝ ↦ t+x) atTop atTop := by
        apply tendsto_atTop.2
        intro r
        filter_upwards [eventually_ge_atTop (r-t)] with x hx using by linarith
      have h₁ := (φ.tendsto_cocompact.mono_left atBot_le_cocompact).comp hneg
      have h₂ := (φ.tendsto_cocompact.mono_left atTop_le_cocompact).comp hpos
      simpa [F, Function.comp_def] using (((h₁.add h₂).norm.pow 2).const_mul (P t))
  let a (x : ℝ) := ((x^k)^2 * W x)⁻¹
  have hEq (x : ℝ) : (∫ t in S, realPWIntervalWeight α s t / realPWIntervalWeight α s x *
      ((t/x)^k * ‖φ (t-x) + φ (t+x)‖)^2) = a x * ∫ t in S, F x t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun t ↦ by simp only [a, F, P, W, div_eq_mul_inv, mul_inv_rev, mul_pow, inv_pow]; ring
  simp_rw [hEq]
  refine squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hw := one_le_realPWIntervalWeight α s hs x
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (sq_nonneg _) (zero_le_one.trans hw)))
      (integral_nonneg fun t ↦ mul_nonneg (hP t) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have h : 1 ≤ (x^k)^2 * W x := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_pow₀ hx)) (one_le_realPWIntervalWeight _ _ hs _)
    exact mul_le_of_le_one_left (integral_nonneg fun t ↦ mul_nonneg (hP t) (sq_nonneg _))
      ((inv_le_one₀ (zero_lt_one.trans_le h)).2 h)

/-- Sharp eventual upper bound for the actual whole-line, even two-packet trial. -/
private theorem eventually_trialEnergy_lt {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : 𝓢(ℝ, ℂ)) (he : ∀ t : ℝ, φ (-t) = φ t) (n : ℕ)
    (hn : -1 < (↑(4*n) : ℝ) - 2*α) {b : ℝ} (hb : 2 * (∫ t : ℝ, ‖φ t‖^2) < b) :
    ∀ᶠ x : ℝ in atTop, (∫ t : ℝ, realPWIntervalWeight α s t *
      ‖((t/x : ℝ) : ℂ)^(2*n) * (φ (t-x) + φ (t+x))‖^2) / realPWIntervalWeight α s x < b := by
  classical
  let k := 2*n
  let W := realPWIntervalWeight α s
  let J (x t : ℝ) := W t / W x * (((t/x)^k) * ‖φ (t-x) + φ (t+x)‖)^2
  let S : Set ℝ := Ioo (-4) 4
  let T : Set ℝ := Ici 4
  have hS : MeasurableSet S := measurableSet_Ioo
  have hT : MeasurableSet T := measurableSet_Ici
  have hscale (t : ℝ) : W t * (t^k)^2 = |t| ^ ((4*n : ℕ) : ℝ) * W t := by
    rw [Real.rpow_natCast, show 4*n = k*2 by dsimp [k]; omega, pow_mul |t| k 2, ← abs_pow, sq_abs, mul_comm]
  have hcompact : IntegrableOn (fun t : ℝ ↦ W t * (t^k)^2) S := by
    simp_rw [hscale]
    exact (integrableOn_abs_rpow_mul_realPWIntervalWeight (R := 4) ha hs hn).mono_set
      Ioo_subset_Icc_self
  have hc : Tendsto (fun x ↦ ∫ t in S, J x t) atTop (𝓝 0) := tendsto_compactTrialEnergy hs φ k hcompact
  have hf : Tendsto (fun x ↦ ∫ t, T.indicator (J x) t) atTop (𝓝 (∫ u : ℝ, ‖φ u‖^2)) := by
    apply (tendsto_farTrialEnergy ha hs φ k).congr'
    apply Eventually.of_forall
    intro x
    change (∫ u, farTrialDensity α s φ k x u) = ∫ t, T.indicator (J x) t
    calc
      _ = ∫ u : ℝ, T.indicator (J x) (x + u) := by
        apply integral_congr_ae
        apply ae_of_all
        intro u
        by_cases h : 4 ≤ x+u <;> simp [farTrialDensity, Set.indicator, T, J, W, h]
      _ = _ := integral_add_left_eq_self _ x
  have hlim := hc.add (hf.const_mul 2)
  have hev := (tendsto_order.mp hlim).2 b (by simpa using hb)
  filter_upwards [hev] with x hx
  have hJ (t : ℝ) : J x (-t) = J x t := by
    dsimp only [J, W]
    rw [show -t-x = -(t+x) by ring, show -t+x = -(t-x) by ring, he, he, add_comm (φ (t+x))]
    simp only [realPWIntervalWeight, abs_neg, neg_div, k, pow_mul, neg_sq]
  have hnorm (t : ℝ) : ‖((t/x : ℝ) : ℂ)^k * (φ (t-x) + φ (t+x))‖^2 =
      ((t/x)^k * ‖φ (t-x) + φ (t+x)‖)^2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow, mul_pow, sq_abs, ← mul_pow]
  have hpoint (t : ℝ) : (W t * ‖((t/x : ℝ) : ℂ)^k * (φ (t-x) + φ (t+x))‖^2) / W x = J x t := by
    rw [hnorm]
    dsimp only [J]
    ring
  have hrewrite : (∫ t : ℝ, W t * ‖((t/x : ℝ) : ℂ)^k * (φ (t-x) + φ (t+x))‖^2) / W x =
      ∫ t, J x t := by
    rw [← integral_div]
    exact integral_congr_ae (ae_of_all _ hpoint)
  have hmem := memLp_translatedJetTrial_realPWIntervalMeasure ha hs φ he x n hn
  let w (t : ℝ) := ENNReal.ofReal (W t)
  have hwm : Measurable w := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hwf : ∀ᵐ t ∂volume, w t < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hwn (t : ℝ) : (w t).toReal = W t := ENNReal.toReal_ofReal
    (zero_le_one.trans (one_le_realPWIntervalWeight α s hs t))
  have hphys := (integrable_withDensity_iff_integrable_smul' hwm hwf).mp
    (hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hi : Integrable (J x) := by
    apply (hphys.div_const (W x)).congr
    exact ae_of_all _ fun t ↦ by simpa only [hwn, smul_eq_mul,
      RealPWBand.translatedJetTrial_apply, k] using hpoint t
  change (∫ t : ℝ, W t * ‖((t/x : ℝ) : ℂ)^k * (φ (t-x) + φ (t+x))‖^2) / W x < b
  rw [hrewrite]
  have hdecomp (t : ℝ) : J x t = S.indicator (J x) t + T.indicator (J x) t + T.indicator (J x) (-t) := by
    by_cases hp : 4 ≤ t
    · have hn : ¬4 ≤ -t := by linarith
      simp [S, T, Set.indicator, hp, hn, not_lt.mpr hp]
    · by_cases hn : 4 ≤ -t
      · have hh : ¬-4 < t := by linarith
        simp [S, T, Set.indicator, hp, hn, hh, hJ]
      · have hh : -4 < t := by linarith
        simp [S, T, Set.indicator, hp, hn, hh, lt_of_not_ge hp]
  calc
    _ = ∫ t : ℝ, S.indicator (J x) t + T.indicator (J x) t + T.indicator (J x) (-t) :=
      integral_congr_ae (ae_of_all _ hdecomp)
    _ = (∫ t in S, J x t) + 2 * (∫ t : ℝ, T.indicator (J x) t) := by
      calc
        _ = (∫ t, S.indicator (J x) t + T.indicator (J x) t) +
            (∫ t, T.indicator (J x) (-t)) :=
          integral_add ((hi.indicator hS).add (hi.indicator hT)) (hi.indicator hT).comp_neg
        _ = _ := by
          have hST : (∫ t, S.indicator (J x) t + T.indicator (J x) t) =
              (∫ t, S.indicator (J x) t) + (∫ t, T.indicator (J x) t) :=
            integral_add (hi.indicator hS) (hi.indicator hT)
          rw [hST, integral_neg_eq_self, integral_indicator hS]
          ring
    _ < b := hx

/-- A high-order central zero makes the almost-extremizing translated packets admissible.
Their normalized energy and their central value give the sharp lower diagonal bound. -/
theorem eventually_lt_realPW_weighted_evalVector_sq {Y α s : ℝ}
    (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) :
    ∀ b < Y, ∀ᶠ x : ℝ in atTop, b < realPWIntervalWeight α s x *
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x‖ ^ 2 := by
  let n := realPWOriginJetCount α
  have hn : -1 < (↑(4*n) : ℝ) - 2*α := by
    push_cast
    exact realPWOriginJetCount_spec α
  intro b hb
  obtain ⟨c, hc, hcY⟩ := exists_between (max_lt hb hY : max b 0 < Y)
  have hc0 : 0 < c := (le_max_right _ _).trans_lt hc
  have hbc : b < c := (le_max_left _ _).trans_lt hc
  obtain ⟨φ, he, hband, hratio⟩ := exists_evenSchwartz_band_trial hY (sub_pos.mpr hcY)
  rw [sub_sub_cancel] at hratio
  let E := ∫ t : ℝ, ‖φ t‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun t ↦ sq_nonneg _
  change c < ‖φ 0‖ ^ 2 / (2 * E) at hratio
  have hEp : 0 < 2 * E := by
    by_contra! h
    rw [le_antisymm h (by positivity), div_zero] at hratio
    exact (not_lt_of_ge hc0.le) hratio
  have hgap := (lt_div_iff₀ hEp).mp hratio
  obtain ⟨D, hED, hDA⟩ := exists_between ((lt_div_iff₀ hc0).mpr
    (show (2*E) * c < ‖φ 0‖ ^ 2 by simpa only [mul_comm] using hgap))
  have hD := hEp.trans hED
  have hlimx : Tendsto (fun x : ℝ ↦ 2*x) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [eventually_ge_atTop (r/2)] with x hx using by linarith
  have htail := (φ.tendsto_cocompact.mono_left atTop_le_cocompact).comp hlimx
  have hcenter : Tendsto (fun x : ℝ ↦ ‖φ 0 + φ (2*x)‖ ^ 2) atTop (𝓝 (‖φ 0‖ ^ 2)) := by
    simpa [Function.comp_def] using (((tendsto_const_nhds (x := φ 0)).add htail).norm.pow 2)
  have henergy := eventually_trialEnergy_lt ha hs φ he n hn hED
  have hoff : ∀ y ∉ Icc (-Y) Y, (𝓕 φ) y = 0 := by
    intro y hy
    rw [SchwartzMap.fourier_coe]
    by_contra h
    exact hy (Ioo_subset_Icc_self (hband h))
  filter_upwards [(tendsto_order.mp hcenter).1 _ ((lt_div_iff₀ hc0).mp hDA), henergy,
    eventually_gt_atTop (0 : ℝ)] with x hx hJ hx0
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ x
  let u := RealPWBand.translatedJetTrial φ x n
  obtain ⟨f, hf⟩ := RealPWBand.exists_translatedJetTrial_evaluation φ Y x n he hoff hμ (memLp_translatedJetTrial_realPWIntervalMeasure ha hs φ he x n hn)
  have hval : RealPWBand.evaluation Y hμ x f = φ 0 + φ (2*x) :=
    (congrFun hf x).trans (RealPWBand.translatedJetTrial_at_center φ hx0.ne' n)
  have hnorm := realPWInterval_norm_sq_eq_weighted_evaluation Y α s hs f
  have hf' (t : ℝ) : RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) t f = u t :=
    congrFun hf t
  simp only [hf', u, RealPWBand.translatedJetTrial_apply] at hnorm
  rw [← hnorm] at hJ
  have hw := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs x)
  have hJ' := (div_lt_iff₀ hw).mp hJ
  have hCS : ‖φ 0 + φ (2*x)‖ ≤ ‖e‖ * ‖f‖ := by
    rw [← hval, ← RealPWBand.toDual_evaluationVector Y hμ x, InnerProductSpace.toDual_apply_apply]
    exact norm_inner_le_norm _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hCS 2
  rw [mul_pow] at hsq
  have hbound := hx.trans_le (hsq.trans (mul_le_mul_of_nonneg_left hJ'.le (sq_nonneg ‖e‖)))
  apply hbc.trans
  apply (mul_lt_mul_iff_right₀ hD).mp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound

/-- The even-band evaluation vector is the projection of an ambient reciprocal
pair with limiting normalized energy arbitrarily close to the bandwidth. -/
theorem exists_nearOptimal_realPWReciprocalProjection {Y α s : ℝ}
    (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (φ : 𝓢(ℝ, ℂ)) (r : ℝ → Lp ℂ 2 (realPWIntervalMeasure α s)),
      (∀ t, φ (-t) = φ t) ∧ ((∫ t, ‖φ t‖^2)/2 ≤ Y+δ) ∧
      (∀ x, ∀ᵐ t ∂volume, r x t = star ((2:ℂ)⁻¹ * (φ (t-x) + φ (t+x))) /
        (realPWIntervalWeight α s t : ℂ)) ∧
      (∀ x, RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x =
        (RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)).orthogonalProjectionOnto (r x)) ∧
      Tendsto (fun x ↦ realPWIntervalWeight α s x * ‖r x‖^2) atTop (𝓝 ((∫ t, ‖φ t‖^2)/2)) := by
  obtain ⟨φ, he, hold, _, hE⟩ := exists_evenSchwartz_fourierInv_plateau_energy hY hδ
  obtain ⟨r, hr, hp, hlim⟩ := exists_projected_twoPackets_tendsto_energy Y ha hs φ he hold
  exact ⟨φ, r, he, by linarith, hr, hp, hlim⟩

/-- The normalized evaluation energy of the full-line even weighted band tends
to the bandwidth. The lower bound is witnessed by actual weighted jet trials. -/
theorem tendsto_realPWIntervalWeight_evalVector_norm_sq {Y α s : ℝ}
    (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) :
    Tendsto (fun x ↦ realPWIntervalWeight α s x *
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x‖ ^ 2) atTop (𝓝 Y) := by
  refine tendsto_order.2 ⟨eventually_lt_realPW_weighted_evalVector_sq hY ha hs, ?_⟩
  intro b hb
  let δ := (b-Y)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨φ, r, _, hE, _, hp, hlim⟩ := exists_nearOptimal_realPWReciprocalProjection hY ha hs hδ
  have hlt : (∫ t, ‖φ t‖^2)/2 < b := hE.trans_lt (by dsimp [δ]; linarith)
  filter_upwards [(tendsto_order.mp hlim).2 b hlt] with x hx
  let hμ := volume_le_realPWIntervalMeasure α s hs
  have hn := (RealPWBand.space Y hμ).norm_orthogonalProjectionOnto_apply_le (r x)
  rw [← hp x] at hn
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2)
    (zero_le_one.trans (one_le_realPWIntervalWeight α s hs x))).trans_lt hx

end RiemannMasullo.Isolated
