module

public import RiemannMasullo.ForMathlib.Analysis.Complex.LipschitzAnalyticApproximation
public import RiemannMasullo.ForMathlib.Analysis.Complex.SzegoDistance
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Entire predictors for clipped boundary logarithms

Smoothing an analytic polynomial approximation preserves a uniform derivative budget.
The exponential of the resulting majorant gives an entire predictor with controlled
weighted Taylor norm and squared prediction error.
-/

@[expose] public noncomputable section

open Complex Metric MeasureTheory Set Real HardyBoundary HardyTable
open scoped ComplexConjugate Interval NNReal

namespace HardySzego

/-- The boundary log modulus with the modulus clipped from below at `exp (-H)`. -/
def clippedLog (F : ℂ → ℂ) (H : ℝ) (z : ℂ) : ℝ :=
  Real.log (max (Real.exp (-H)) ‖F z‖)

/-- The mean excess negative log above the clipping threshold, with normalized arclength. -/
def clippingLoss (F : ℂ → ℂ) (H : ℝ) : ℝ :=
  circleAverage (fun z ↦ max 0 (-H-Real.log ‖F z‖)) 0 1

private lemma clippedLog_continuous {F : ℂ → ℂ} (hF : ContinuousOn F (sphere 0 1)) (H : ℝ) :
    ContinuousOn (clippedLog F H) (sphere 0 1) :=
  (continuousOn_const.sup hF.norm).log (fun _ _ ↦ ((Real.exp_pos _).trans_le (le_max_left _ _)).ne')

private lemma log_abs_sub_le {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/a := by
  wlog hxy : y ≤ x generalizing x y
  · simpa only [abs_sub_comm (Real.log y),abs_sub_comm y] using this hy hx (le_of_not_ge hxy)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (ha.trans_le hy) hxy)),
    abs_of_nonneg (sub_nonneg.mpr hxy), ← Real.log_div (ha.trans_le hx).ne' (ha.trans_le hy).ne']
  calc
    Real.log (x/y) ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos (ha.trans_le hx) (ha.trans_le hy))
    _ = (x-y)/y := by field_simp [(ha.trans_le hy).ne']
    _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) ha hy

private lemma clippedLog_lipschitz {F : ℂ → ℂ} {D : ℝ} (H : ℝ)
    (hf : ∀ z ∈ sphere (0:ℂ) 1, ∀ w ∈ sphere (0:ℂ) 1, ‖F z-F w‖ ≤ D*‖z-w‖) :
    ∀ z ∈ sphere (0:ℂ) 1, ∀ w ∈ sphere (0:ℂ) 1,
      |clippedLog F H z-clippedLog F H w| ≤ (Real.exp H*D)*‖z-w‖ := by
  intro z hz w hw
  let a := Real.exp (-H)
  have ha : 0 < a := Real.exp_pos _
  have hle : |max a ‖F z‖-max a ‖F w‖| ≤ D*‖z-w‖ := by
    calc
      _ ≤ |‖F z‖-‖F w‖| := by
        simpa only [max_comm a] using abs_max_sub_max_le_abs ‖F z‖ ‖F w‖ a
      _ ≤ ‖F z-F w‖ := abs_norm_sub_norm_le ..
      _ ≤ _ := hf z hz w hw
  refine (log_abs_sub_le ha (le_max_left a ‖F z‖) (le_max_left a ‖F w‖)).trans ?_
  calc
    _ ≤ (D*‖z-w‖)/a := div_le_div_of_nonneg_right hle ha.le
    _ = _ := by simp [a,Real.exp_neg,div_eq_mul_inv]; ring

/-- The positive-part clipping loss equals the mean pointwise increase of the clipped
logarithm. Boundary zeros can be dropped in this equality because their arclength is zero. -/
theorem clippingLoss_eq_circleAverage_sub {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) (H : ℝ) :
    clippingLoss F H = circleAverage (fun z ↦ clippedLog F H z-Real.log ‖F z‖) 0 1 := by
  have hne := (disk_log_integrable hF h0).1
  unfold clippingLoss circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le Real.two_pi_pos.le]
  filter_upwards [hne] with θ hθ
  set x := ‖F (circleMap 0 1 θ)‖
  have hx : 0 < x := norm_pos_iff.mpr hθ
  change max 0 (-H-Real.log x) = Real.log (max (Real.exp (-H)) x)-Real.log x
  by_cases ha : Real.exp (-H) ≤ x
  · rw [max_eq_right ha,sub_self,max_eq_left]
    exact sub_nonpos.mpr (by simpa using Real.log_le_log (Real.exp_pos _) ha)
  · rw [max_eq_left (le_of_not_ge ha),Real.log_exp,max_eq_right]
    exact sub_nonneg.mpr (by simpa using Real.log_le_log hx (le_of_not_ge ha))

/-- The mean change caused by clipping is exactly the excess negative log. -/
theorem circleAverage_clippedLog {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) (H : ℝ) :
    circleAverage (clippedLog F H) 0 1 =
      circleAverage (fun z ↦ Real.log ‖F z‖) 0 1 + clippingLoss F H := by
  have hi := (disk_log_integrable hF h0).2.1
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  have hk := (clippedLog_continuous (hc.mono sphere_subset_closedBall) H).circleIntegrable zero_le_one
  rw [clippingLoss_eq_circleAverage_sub hF h0,circleAverage_fun_sub hk hi]
  ring

/-- Interior Taylor expansion of the native Hardy coefficient vector. -/
theorem hasSum_diskCoefficients {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G (ball 0 1))
    (z : ℂ) (hz : ‖z‖ < 1) : HasSum (fun j : ℕ ↦ diskCoefficients G hG j*z^j) (G z) := by
  apply (Complex.hasSum_taylorSeries_on_ball hG.differentiableOn (show z ∈ ball 0 1 by simpa using hz)).congr_fun
  intro j
  simp [diskCoefficients_apply,smul_eq_mul]
  ring

/-- Parseval for the Taylor coefficients of a disk-algebra function. -/
theorem hasSum_diskCoefficients_sq {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G (ball 0 1)) :
    HasSum (fun j : ℕ ↦ ‖diskCoefficients G hG j‖^2) (circleAverage (fun z ↦ ‖G z‖^2) 0 1) := by
  have hc := hG.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  exact hasSum_sq_of_inner hc (hasSum_diskCoefficients hG)

private lemma diskCoeff_succ {q : ℂ → ℂ} (hq : Differentiable ℂ q) (hd : Differentiable ℂ (deriv q)) (j : ℕ) :
    diskCoefficients (deriv q) hd.diffContOnCl j =
      ((j+1:ℕ):ℂ)*diskCoefficients q hq.diffContOnCl (j+1) := by
  simp only [diskCoefficients_apply, Nat.factorial_succ, Nat.cast_mul, iteratedDeriv_succ']
  have hj : ((j+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp


/-- A boundary derivative square mean controls the weighted Taylor norm. The statement
also proves summability, so a vanishing totalized sum cannot certify a divergent series. -/
theorem weighted_diskCoefficients_sq {q : ℂ → ℂ} (hq : Differentiable ℂ q) :
    let b := diskCoefficients q hq.diffContOnCl
    Summable (fun j : ℕ ↦ ((j:ℝ)+1)^2*‖b j‖^2) ∧
      ∑' j : ℕ, ((j:ℝ)+1)^2*‖b j‖^2 ≤ 2*(circleAverage (fun z ↦ ‖q z‖^2) 0 1+
        circleAverage (fun z ↦ ‖deriv q z‖^2) 0 1) := by
  let b := diskCoefficients q hq.diffContOnCl
  let v (j : ℕ) := (j:ℝ)^2*‖b j‖^2
  have hd := hasSum_diskCoefficients_sq hq.deriv.diffContOnCl
  have hv : HasSum v (circleAverage (fun z ↦ ‖deriv q z‖^2) 0 1) := by
    have hs : HasSum (fun j : ℕ ↦ v (j+1)) (circleAverage (fun z ↦ ‖deriv q z‖^2) 0 1) := by
      apply hd.congr_fun
      intro j
      dsimp only [v,b]
      rw [diskCoeff_succ hq hq.deriv, norm_mul, mul_pow]
      norm_cast
    simpa [v] using (hasSum_nat_add_iff (f := v) 1).mp hs
  have hsum := ((hasSum_diskCoefficients_sq hq.diffContOnCl).add hv).mul_left (2:ℝ)
  have hle (j : ℕ) : ((j:ℝ)+1)^2*‖b j‖^2 ≤ 2*(‖b j‖^2+v j) := by
    calc
      _ ≤ (2*(1+(j:ℝ)^2))*‖b j‖^2 :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((j:ℝ)-1)]) (sq_nonneg _)
      _ = _ := by dsimp [v]; ring
  have hs := hsum.summable.of_nonneg_of_le (fun j ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hle
  exact ⟨hs, (hs.tsum_le_tsum hle hsum.summable).trans_eq hsum.tsum_eq⟩

private lemma sq_budget {H D : ℝ} (hH : 0 ≤ H) :
    2*((Real.exp H)^2+Real.exp H^2*(2*(Real.exp H*D+1)^2)) ≤ 10*(1+D^2)*Real.exp (4*H) := by
  let E := Real.exp H
  have hE : 1 ≤ E := Real.one_le_exp hH
  have h2 : E^2 ≤ E^4 := by
    have h1 := pow_le_pow_right₀ hE (by norm_num : 2 ≤ 4)
    exact h1
  have hd : (E*D+1)^2 ≤ 2*((E*D)^2+1) := by nlinarith [sq_nonneg (E*D-1)]
  have heq : Real.exp (4*H) = E^4 := by exact Real.exp_nat_mul H 4
  rw [heq]
  change 2*(E^2+E^2*(2*(E*D+1)^2)) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg E), mul_nonneg (by positivity : 0 ≤ E^4) (sq_nonneg D)]

private lemma disk_max_bound {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball 0 1)) {A : ℝ}
    (h : ∀ z ∈ sphere (0:ℂ) 1, ‖f z‖ ≤ A) : ∀ z ∈ closedBall (0:ℂ) 1, ‖f z‖ ≤ A := by
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf
  · rwa [frontier_ball _ one_ne_zero]
  · rwa [closure_ball _ one_ne_zero]


private lemma exp_eval_diff (Q : Polynomial ℂ) :
    Differentiable ℂ (fun z ↦ Complex.exp (-Q.eval z)) :=
  fun z ↦ ((Q.hasDerivAt z).neg.cexp).differentiableAt

private lemma re_eval_mean (Q : Polynomial ℂ) :
    circleAverage (fun z ↦ (Q.eval z).re) 0 1 = (Q.eval 0).re := by
  have hd : Differentiable ℂ (fun z ↦ Q.eval z) := fun z ↦ (Q.hasDerivAt z).differentiableAt
  have hm := (hd.diffContOnCl (s := ball (0:ℂ) |(1:ℝ)|)).circleAverage
  exact (Complex.reCLM.circleAverage_comp_comm hd.continuous.continuousOn.circleIntegrable').trans
    (congrArg Complex.re hm)

private lemma center_lower {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    {H ε : ℝ} (hε : 0 ≤ ε) (Q : Polynomial ℂ)
    (hQ : ∀ z ∈ sphere (0:ℂ) 1, (Q.eval z).re ≤ clippedLog F H z+ε) :
    1-‖F 0*Complex.exp (-Q.eval 0)‖^2 ≤
      (distance (diskCoefficients F hF))^2+2*(clippingLoss F H+ε) := by
  let m := circleAverage (fun z ↦ Real.log ‖F z‖) 0 1
  let b := clippingLoss F H+ε
  let J := logGap F
  have hJ : 0 ≤ J := sub_nonneg.mpr (disk_log_integrable hF h0).2.2
  have hb : 0 ≤ b := add_nonneg (circleAverage_nonneg_of_nonneg (fun _ _ ↦ le_max_left _ _)) hε
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  have hk := (clippedLog_continuous (hc.mono sphere_subset_closedBall) H).circleIntegrable zero_le_one
  have hs : CircleIntegrable (fun z ↦ clippedLog F H z+ε) 0 1 := hk.add (circleIntegrable_const ε 0 1)
  have hmean := circleAverage_mono (Complex.continuous_re.comp Q.continuous).continuousOn.circleIntegrable'
    hs (fun z hz ↦ hQ z (by simpa using hz))
  change circleAverage (fun z ↦ (Q.eval z).re) 0 1 ≤ _ at hmean
  rw [re_eval_mean, circleAverage_fun_add hk (circleIntegrable_const ε 0 1), circleAverage_const,
    circleAverage_clippedLog hF h0] at hmean
  have hcent : (Q.eval 0).re ≤ m+b := by dsimp [m,b]; linarith
  have heq : ‖F 0*Complex.exp (-Q.eval 0)‖^2 =
      Real.exp (2*(Real.log ‖F 0‖-(Q.eval 0).re)) := by
    rw [norm_mul,Complex.norm_exp,Complex.neg_re, two_mul,Real.exp_add,Real.exp_sub,
      Real.exp_log (norm_pos_iff.mpr h0),Real.exp_neg]
    ring
  have hbound : Real.exp (-2*J)*Real.exp (-2*b) ≤ ‖F 0*Complex.exp (-Q.eval 0)‖^2 := by
    rw [heq,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -2*(m-Real.log ‖F 0‖)+ -2*b ≤ _
    linarith
  have hE : Real.exp (-2*J) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hL := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2*b)) (Real.exp_pos (-2*J)).le
  have hM := mul_le_mul_of_nonneg_right hE hb
  rw [disk_distance_sq hF h0]
  change _ ≤ 1-Real.exp (-2*J)+2*b
  nlinarith

/-- An entire predictor with controlled weighted Taylor square norm. For every positive
tolerance the squared Hardy error is within twice the clipping loss and tolerance of the
true squared distance to polynomial multiples. The derivative budget is independent of
the tolerance. -/
theorem exists_clipped_predictor {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    {D H ε : ℝ} (hD : 0 ≤ D)
    (hLip : ∀ z ∈ sphere (0:ℂ) 1, ∀ w ∈ sphere (0:ℂ) 1, ‖F z-F w‖ ≤ D*‖z-w‖)
    (hH : 0 ≤ H) (hε : 0 < ε) :
    ∃ (q : ℂ → ℂ) (hq : Differentiable ℂ q),
      (∀ z ∈ closedBall (0:ℂ) 1, ‖q z‖ ≤ Real.exp H) ∧
      Summable (fun j : ℕ ↦ ((j:ℝ)+1)^2*‖diskCoefficients q hq.diffContOnCl j‖^2) ∧
      (∑' j : ℕ, ((j:ℝ)+1)^2*‖diskCoefficients q hq.diffContOnCl j‖^2) ≤
        10*(1+D^2)*Real.exp (4*H) ∧
      circleAverage (fun z ↦ ‖1-q z*F z‖^2) 0 1 ≤
        (distance (diskCoefficients F hF))^2+2*(clippingLoss F H+ε) := by
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  obtain ⟨Q,hQ⟩ := exists_polynomial_re_majorant
    (clippedLog_continuous (hc.mono sphere_subset_closedBall) H)
    (mul_nonneg (Real.exp_pos H).le hD) (clippedLog_lipschitz H hLip) hε
  let E (z : ℂ) := Complex.exp (-Q.eval z)
  let Φ (z : ℂ) := F z*E z
  let c := conj (Φ 0)
  let q (z : ℂ) := c*E z
  have he : Differentiable ℂ E := exp_eval_diff Q
  have hp : DiffContOnCl ℂ Φ (ball 0 1) :=
    ⟨hF.differentiableOn.mul he.differentiableOn,hF.continuousOn.mul he.continuous.continuousOn⟩
  have hq : Differentiable ℂ q := (differentiable_const c).mul he
  have heNorm (z : ℂ) : ‖E z‖ = (Real.exp (Q.eval z).re)⁻¹ := by
    simp only [E,Complex.norm_exp,Complex.neg_re,Real.exp_neg]
  have hmaj (z : ℂ) (hz : z ∈ sphere 0 1) :
      max (Real.exp (-H)) ‖F z‖ ≤ Real.exp (Q.eval z).re := by
    have hb := Real.exp_le_exp.mpr (hQ z hz).1
    rwa [clippedLog,Real.exp_log ((Real.exp_pos _).trans_le (le_max_left _ _))] at hb
  have hp1 : ∀ z ∈ closedBall (0:ℂ) 1, ‖Φ z‖ ≤ 1 := by
    apply disk_max_bound hp
    intro z hz
    rw [show Φ z = _ from rfl,norm_mul,heNorm,← div_eq_mul_inv,div_le_one (Real.exp_pos _)]
    exact (le_max_right _ _).trans (hmaj z hz)
  have hc1 : ‖c‖ ≤ 1 := by simpa [c] using hp1 0 (by simp)
  have hq1 : ∀ z ∈ closedBall (0:ℂ) 1, ‖q z‖ ≤ Real.exp H := by
    apply disk_max_bound hq.diffContOnCl
    intro z hz
    have ht := ((Real.exp_le_exp).mp ((le_max_left _ _).trans (hmaj z hz)))
    calc
      ‖q z‖ = ‖c‖*‖E z‖ := norm_mul _ _
      _ ≤ 1*‖E z‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
      _ = Real.exp (-(Q.eval z).re) := by simp [E,Complex.norm_exp]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hd (z : ℂ) : deriv q z = -q z*Q.derivative.eval z := by
    have hh : HasDerivAt q (-q z*Q.derivative.eval z) z := by
      convert (((Q.hasDerivAt z).neg.cexp).const_mul c) using 1
      dsimp [q,E]
      ring
    exact hh.deriv
  have hqd : circleAverage (fun z ↦ ‖deriv q z‖^2) 0 1 ≤
      Real.exp H^2*(2*(Real.exp H*D+1)^2) := by
    have hu : CircleIntegrable (fun z ↦ ‖Q.derivative.eval z‖^2) 0 1 :=
      (Q.derivative.continuous.norm.pow 2).continuousOn.circleIntegrable'
    calc
      _ ≤ circleAverage (fun z ↦ ((Real.exp H)^2) • ‖Q.derivative.eval z‖^2) 0 1 := by
        apply circleAverage_mono (hq.deriv.continuous.norm.pow 2).continuousOn.circleIntegrable'
          (hu.const_smul (a := (Real.exp H)^2))
        intro z hz
        change ‖deriv q z‖^2 ≤ (Real.exp H)^2*‖Q.derivative.eval z‖^2
        rw [hd,norm_mul,norm_neg,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hq1 z
          (sphere_subset_closedBall (by simpa using hz))) 2) (sq_nonneg _)
      _ ≤ _ := by
        rw [circleAverage_fun_smul,smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (circleAverage_derivative_sq_le Q (fun z hz ↦ (hQ z hz).2.2)) (sq_nonneg _)
  have hqs : circleAverage (fun z ↦ ‖q z‖^2) 0 1 ≤ Real.exp H^2 :=
    circleAverage_mono_on_of_le_circle (hq.continuous.norm.pow 2).continuousOn.circleIntegrable'
      (fun z hz ↦ pow_le_pow_left₀ (norm_nonneg _) (hq1 z (sphere_subset_closedBall (by simpa using hz))) 2)
  obtain ⟨hs,hw⟩ := weighted_diskCoefficients_sq hq
  refine ⟨q,hq,hq1,hs,hw.trans ((mul_le_mul_of_nonneg_left (add_le_add hqs hqd) (by norm_num : (0:ℝ) ≤ 2)).trans (sq_budget (D := D) hH)),?_⟩
  let V (z : ℂ) := c*Φ z
  have hV : DiffContOnCl ℂ V (ball 0 1) :=
    ⟨(differentiable_const c).differentiableOn.mul hp.differentiableOn, continuousOn_const.mul hp.continuousOn⟩
  have hVc := hV.continuousOn
  rw [closure_ball _ one_ne_zero] at hVc
  have hi := (hVc.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hi2 := ((hVc.norm.pow 2).mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hmean : circleAverage V 0 1 = V 0 := (show DiffContOnCl ℂ V (ball 0 |(1:ℝ)|) by simpa using hV).circleAverage
  have hRe : (V 0).re = ‖Φ 0‖^2 := by
    dsimp only [V,c]
    rw [mul_comm,Complex.mul_conj']
    norm_cast
  have hEv : circleAverage (fun z ↦ ‖V z‖^2) 0 1 ≤ ‖Φ 0‖^2 := by
    apply circleAverage_mono_on_of_le_circle hi2
    intro z hz
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      ‖V z‖ = ‖c‖*‖Φ z‖ := norm_mul _ _
      _ ≤ ‖c‖*1 := mul_le_mul_of_nonneg_left (hp1 z (sphere_subset_closedBall (by simpa using hz))) (norm_nonneg _)
      _ = _ := by simp [c]
  have hprod (z : ℂ) : q z*F z = V z := by dsimp [q,V,Φ]; ring
  simp_rw [hprod]
  rw [residual_energy hi hi2,hmean,hRe]
  exact (by linarith only [hEv] : 1-2*‖Φ 0‖^2+_ ≤ 1-‖Φ 0‖^2).trans
    (center_lower hF h0 hε.le Q (fun z hz ↦ (hQ z hz).2.1))


/-- A derivative bound in the open disk gives the required chordal boundary Lipschitz bound.
The derivative may fail to extend to the circle. -/
theorem boundary_lipschitz_of_deriv {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) {D : ℝ}
    (hD : 0 ≤ D) (hd : ∀ z ∈ ball (0:ℂ) 1, ‖deriv F z‖ ≤ D) :
    ∀ z ∈ sphere (0:ℂ) 1, ∀ w ∈ sphere (0:ℂ) 1, ‖F z-F w‖ ≤ D*‖z-w‖ := by
  let K : ℝ≥0 := ⟨D,hD⟩
  have hi : LipschitzOnWith K F (ball 0 1) :=
    (convex_ball (0:ℂ) 1).lipschitzOnWith_of_nnNorm_deriv_le
      (fun z hz ↦ (hF.differentiableOn z hz).differentiableAt (isOpen_ball.mem_nhds hz))
      (fun z hz ↦ show ‖deriv F z‖ ≤ D from hd z hz)
  have hc := LipschitzOnWith.closure hF.continuousOn hi
  rw [closure_ball _ one_ne_zero] at hc
  intro z hz w hw
  simpa [dist_eq_norm, K] using! hc.dist_le_mul z (sphere_subset_closedBall hz) w (sphere_subset_closedBall hw)

end HardySzego
