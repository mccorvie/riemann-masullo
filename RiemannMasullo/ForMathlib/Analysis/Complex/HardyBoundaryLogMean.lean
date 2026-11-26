module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Boundary logarithmic means in the disk algebra

Jensen's inequality and the mean value property bound the boundary energy of a polynomial
multiple. Radial convergence gives integrability of the boundary logarithm for disk-algebra
functions with nonzero center, including functions with boundary zeros.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real MeromorphicOn
open scoped Topology

namespace HardyBoundary

/-- Boundary logarithmic mean minus the logarithm of the center modulus. -/
def logGap (F : ℂ → ℂ) : ℝ := Real.circleAverage (fun z ↦ Real.log ‖F z‖) 0 1-Real.log ‖F 0‖

local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

private theorem circleAverage_mono_ae {u v : ℂ → ℝ} {R : ℝ}
    (hu : CircleIntegrable u 0 R) (hv : CircleIntegrable v 0 R)
    (h : ∀ᵐ θ : ℝ ∂μθ, u (circleMap 0 R θ) ≤ v (circleMap 0 R θ)) :
    circleAverage u 0 R ≤ circleAverage v 0 R := by
  rw [circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hu)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hv) h) (by positivity)

/-- Arithmetic–geometric mean on a circle, allowing an almost-everywhere exponential relation. -/
theorem exp_circleAverage_le {u v : ℂ → ℝ} {R : ℝ}
    (hu : CircleIntegrable u 0 R) (hv : CircleIntegrable v 0 R)
    (h : ∀ᵐ θ : ℝ ∂μθ, Real.exp (u (circleMap 0 R θ)) ≤ v (circleMap 0 R θ)) :
    Real.exp (circleAverage u 0 R) ≤ circleAverage v 0 R := by
  let m := circleAverage u 0 R
  have hc := circleIntegrable_const m 0 R
  have hd : CircleIntegrable (fun z ↦ u z-m) 0 R := hu.sub hc
  have he : CircleIntegrable (fun z ↦ Real.exp m • (u z-m)) 0 R := hd.const_smul (a := Real.exp m)
  have h1 := circleIntegrable_const (Real.exp m) 0 R
  have hlin : CircleIntegrable (fun z ↦ Real.exp m + Real.exp m • (u z-m)) 0 R := h1.add he
  have hbound := circleAverage_mono_ae hlin hv (h.mono (fun θ hθ ↦ by
    refine le_trans ?_ hθ
    set x := u (circleMap 0 R θ)
    calc
      Real.exp m + Real.exp m • (x-m) = Real.exp m * ((x-m)+1) := by rw [smul_eq_mul]; ring
      _ ≤ Real.exp m * Real.exp (x-m) := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = Real.exp x := by rw [← Real.exp_add]; congr 1; ring))
  rw [circleAverage_fun_add h1 he,circleAverage_const,circleAverage_fun_smul,
    circleAverage_fun_sub hu hc,circleAverage_const] at hbound
  simpa [m] using hbound

/-- Jensen's lower bound holds on the observation circle even when the polynomial
has roots on that circle. The nonzero-center branch is the only one needing its logarithm. -/
theorem log_at_center_le_circleAverage {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 |R|)) (h0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ circleAverage (fun z ↦ Real.log ‖f z‖) 0 R := by
  rw [hf.circleAverage_log_norm h0]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro z
  by_cases hz : z ∈ closedBall (0:ℂ) |R|
  · apply mul_nonneg (by exact_mod_cast hf.divisor_nonneg z)
    by_cases hzero : z = 0
    · subst z; simp
    · have hzR : ‖z‖ ≤ R := by simpa [abs_of_pos hR] using hz
      have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hzero
      apply Real.log_nonneg
      simpa [div_eq_mul_inv] using (one_le_div hzp).mpr hzR
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

private theorem polynomial_ae_nonzero {p : Polynomial ℂ} (hp : p ≠ 0) {R : ℝ} (hR : R ≠ 0) :
    ∀ᵐ θ : ℝ ∂μθ, p.eval (circleMap 0 R θ) ≠ 0 := by
  apply ae_restrict_of_ae
  apply ae_iff.mpr
  simp only [not_not]
  have hset : {θ : ℝ | p.eval (circleMap 0 R θ) = 0} = circleMap 0 R ⁻¹' {z | p.IsRoot z} := by
    ext θ
    simp [Polynomial.IsRoot]
  rw [hset]
  exact ((Polynomial.finite_setOfPred_isRoot hp).countable.preimage_circleMap 0 hR).measure_zero volume

/-- The logarithmic mean of F times the modulus at zero of an arbitrary complex polynomial
controls its boundary product energy. The p(0)=0 case includes the zero polynomial. -/
theorem scale_le_product_energy {R : ℝ} (hR : 0 < R) (F : ℂ → ℂ) (p : Polynomial ℂ)
    (hlog : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 R)
    (hF : ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 R θ) ≠ 0)
    (henergy : CircleIntegrable (fun z ↦ ‖F z*p.eval z‖^2) 0 R) :
    Real.exp (2*circleAverage (fun z ↦ Real.log ‖F z‖) 0 R) * ‖p.eval 0‖^2 ≤
      circleAverage (fun z ↦ ‖F z*p.eval z‖^2) 0 R := by
  by_cases h0 : p.eval 0 = 0
  · simpa [h0] using circleAverage_nonneg_of_nonneg (c := (0:ℂ)) (R := R)
      (fun z _ ↦ sq_nonneg ‖F z*p.eval z‖)
  have hp : p ≠ 0 := fun h ↦ h0 (h ▸ Polynomial.eval_zero)
  have hpan : AnalyticOnNhd ℂ (fun z ↦ p.eval z) (closedBall 0 |R|) :=
    (AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)
  have hplog := (hpan.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hsum := hlog.add hplog
  have hInt : CircleIntegrable (fun z ↦ (2:ℝ) • (Real.log ‖F z‖ + Real.log ‖p.eval z‖)) 0 R :=
    hsum.const_smul (a := (2:ℝ))
  have hExp := exp_circleAverage_le hInt henergy (by
    filter_upwards [hF,polynomial_ae_nonzero hp hR.ne'] with θ hθ hpθ
    simp only [smul_eq_mul, two_mul, Real.exp_add,norm_mul,Real.exp_log (norm_pos_iff.mpr hθ),
      Real.exp_log (norm_pos_iff.mpr hpθ)]
    exact (sq _).ge)
  rw [circleAverage_fun_smul,circleAverage_fun_add hlog hplog,smul_eq_mul] at hExp
  apply le_trans _ hExp
  have hJ := log_at_center_le_circleAverage hR hpan h0
  calc
    _ = Real.exp (2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 R + Real.log ‖p.eval 0‖)) := by
      rw [mul_add,Real.exp_add, two_mul (Real.log _),Real.exp_add,Real.exp_log (norm_pos_iff.mpr h0),sq]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Complete the square using the real part of the genuine complex center value. -/
theorem residual_scalar {A b : ℂ} (hA : A ≠ 0) (m : ℝ) :
    1 - Real.exp (-2*(m-Real.log ‖A‖)) ≤
      1 - 2*(A*b).re + Real.exp (2*m)*‖b‖^2 := by
  have hnorm := (Complex.re_le_norm (A*b))
  rw [norm_mul] at hnorm
  have e := Real.exp_pos m
  have hform : Real.exp (-2*(m-Real.log ‖A‖)) = (‖A‖ / Real.exp m)^2 := by
    have h := Real.exp_log (norm_pos_iff.mpr hA)
    rw [show -2*(m-Real.log ‖A‖) = (Real.log ‖A‖ + Real.log ‖A‖) + -(m+m) by ring,
      Real.exp_add,Real.exp_neg,Real.exp_add,Real.exp_add,h]
    field_simp
  rw [hform,two_mul m,Real.exp_add]
  have hcross : (Real.exp m*‖b‖)*(‖A‖/Real.exp m) = ‖A‖*‖b‖ := by field_simp
  nlinarith [sq_nonneg (Real.exp m*‖b‖-‖A‖/Real.exp m)]

private theorem one_sub_sq (z : ℂ) : ‖1-z‖^2 = 1-2*z.re+‖z‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im]
  ring

/-- The boundary residual energy of a function with the supplied circle mean. -/
theorem residual_energy {q : ℂ → ℂ} {R : ℝ} (hq : CircleIntegrable q 0 R)
    (he : CircleIntegrable (fun z ↦ ‖q z‖^2) 0 R) :
    circleAverage (fun z ↦ ‖1-q z‖^2) 0 R =
      1 - 2*(circleAverage q 0 R).re + circleAverage (fun z ↦ ‖q z‖^2) 0 R := by
  have hr : CircleIntegrable (fun z ↦ (q z).re) 0 R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr <|
      Complex.reCLM.integrable_comp ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hq)
  have h2 : CircleIntegrable (fun z ↦ (2:ℝ) • (q z).re) 0 R := hr.const_smul (a := (2:ℝ))
  have h1 := circleIntegrable_const (1:ℝ) 0 R
  have h12 : CircleIntegrable (fun z ↦ 1 - (2:ℝ) • (q z).re) 0 R := h1.sub h2
  simp_rw [one_sub_sq]
  change circleAverage (fun z ↦ (1 - (2:ℝ) • (q z).re) + ‖q z‖^2) _ _ = _
  rw [circleAverage_fun_add h12 he,circleAverage_fun_sub h1 h2,circleAverage_const,
    circleAverage_fun_smul]
  have hreal := Complex.reCLM.circleAverage_comp_comm hq
  change 1-2*circleAverage (Complex.reCLM ∘ q) 0 R + _ = _
  rw [hreal]
  rfl

/-- A boundary-trace formulation. H-infinity traces may be supplied through their
circle mean; disk-algebra clients discharge the mean by the analytic mean-value theorem. -/
theorem boundary_lower {R : ℝ} (hR : 0 < R) (F : ℂ → ℂ) (p : Polynomial ℂ) (h0 : F 0 ≠ 0)
    (hlog : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 R)
    (hF : ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 R θ) ≠ 0)
    (hq : CircleIntegrable (fun z ↦ F z*p.eval z) 0 R)
    (he : CircleIntegrable (fun z ↦ ‖F z*p.eval z‖^2) 0 R)
    (hmean : circleAverage (fun z ↦ F z*p.eval z) 0 R = F 0*p.eval 0) :
    1 - Real.exp (-2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 R - Real.log ‖F 0‖)) ≤
      circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 R := by
  rw [residual_energy hq he,hmean]
  exact (residual_scalar h0 _).trans (add_le_add_right (scale_le_product_energy hR F p hlog hF he) _ :
    1-2*(F 0*p.eval 0).re+_ ≤ 1-2*(F 0*p.eval 0).re+_)

end HardyBoundary

end

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real
open scoped Topology

namespace HardyBoundary

local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

private theorem eval_poly_diff (p : Polynomial ℂ) : Differentiable ℂ (fun z ↦ p.eval z) :=
  differentiableOn_univ.mp (AnalyticOnNhd.eval_polynomial p).differentiableOn

/-- The closed-disk analytic and continuous hypothesis supplies every product mean value. -/
theorem disk_lower (F : ℂ → ℂ) (p : Polynomial ℂ) {R : ℝ} (hR : 0 < R)
    (hF : DiffContOnCl ℂ F (ball 0 R)) (h0 : F 0 ≠ 0)
    (hlog : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 R)
    (hne : ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 R θ) ≠ 0) :
    1-Real.exp (-2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 R-Real.log ‖F 0‖)) ≤
      circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 R := by
  have hprod : DiffContOnCl ℂ (fun z ↦ F z*p.eval z) (ball 0 |R|) := by
    rw [abs_of_pos hR]
    exact hF.smul (eval_poly_diff p).diffContOnCl
  have hc := hprod.continuousOn
  rw [closure_ball _ (abs_ne_zero.mpr hR.ne')] at hc
  have hs := hc.mono sphere_subset_closedBall
  exact boundary_lower hR F p h0 hlog hne hs.circleIntegrable' (hs.norm.pow 2).circleIntegrable'
    hprod.circleAverage

/-- A nonzero germ at the center has almost everywhere nonzero values on each
circle lying in its analytic domain. -/
theorem analytic_circle_ae_nonzero {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ F (closedBall 0 R)) (h0 : F 0 ≠ 0) :
    ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 R θ) ≠ 0 := by
  have hcor := (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
    (convex_closedBall (0:ℂ) R).isPreconnected).resolve_left (fun h ↦ h0 (h (mem_closedBall_self hR.le)))
  have hsp : ∀ᶠ z in codiscreteWithin (sphere (0:ℂ) |R|), F z ≠ 0 :=
    codiscreteWithin_mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall) hcor
  exact ae_restrict_le_codiscreteWithin measurableSet_Ioc <| codiscreteWithin_mono (subset_univ _)
    (circleMap_preimage_codiscrete (c := 0) hR.ne' hsp)

/-- On an interior observation circle the hypotheses on its boundary logarithm
and exceptional zero set follow from holomorphy and the nonzero center. -/
theorem analytic_lower {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ F (closedBall 0 R)) (h0 : F 0 ≠ 0) (p : Polynomial ℂ) :
    1-Real.exp (-2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 R-Real.log ‖F 0‖)) ≤
      circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 R := by
  apply disk_lower F p hR (hf.differentiableOn.diffContOnCl_ball Subset.rfl) h0
  · have hs : AnalyticOnNhd ℂ F (sphere 0 |R|) := hf.mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall)
    exact hs.meromorphicOn.circleIntegrable_log_norm
  · exact analytic_circle_ae_nonzero hR hf h0

/-- With a supplied radial limit of logarithmic means, the unit-circle conclusion requires
no description of the zeros of F on the unit circle. The limiting logarithmic gap is nonnegative. -/
theorem lower_of_radial_log {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 1)) (hint : ∀ᶠ n in atTop, r n ∈ Ioo 0 1)
    {m : ℝ} (hm : Tendsto (fun n ↦ circleAverage (fun z ↦ Real.log ‖F z‖) 0 (r n)) atTop (𝓝 m)) :
    0 ≤ m-Real.log ‖F 0‖ ∧ ∀ p : Polynomial ℂ, 1-Real.exp (-2*(m-Real.log ‖F 0‖)) ≤
      circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 1 := by
  have hreg : ∀ᶠ n in atTop, AnalyticOnNhd ℂ F (closedBall 0 (r n)) :=
    hint.mono fun n hn ↦ (hF.differentiableOn.analyticOnNhd isOpen_ball).mono
      (closedBall_subset_ball hn.2)
  constructor
  · apply sub_nonneg.mpr
    apply ge_of_tendsto hm
    filter_upwards [hint,hreg] with n hn hreg'
    exact log_at_center_le_circleAverage hn.1 (by rwa [abs_of_pos hn.1]) h0
  · intro p
    have hclose := hF.continuousOn
    rw [closure_ball _ one_ne_zero] at hclose
    have hres : ContinuousOn (fun z ↦ ‖1-F z*p.eval z‖^2) (closedBall 0 1) :=
      (continuousOn_const.sub (hclose.mul (eval_poly_diff p).continuous.continuousOn)).norm.pow 2
    have hc : ContinuousOn (circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0) (Icc 0 1) :=
      Real.ContinuousOn.circleAverage (hres.mono (by
        intro z hz
        simpa [Metric.mem_closedBall,dist_eq_norm] using hz.2)) (fun _ h ↦ h.1)
    have hrad : Tendsto r atTop (𝓝[Icc 0 1] 1) :=
      tendsto_nhdsWithin_iff.mpr ⟨hr,hint.mono fun _ hn ↦ ⟨hn.1.le,hn.2.le⟩⟩
    have hE := (hc 1 (right_mem_Icc.mpr (by norm_num))).tendsto.comp hrad
    have hleft : Tendsto (fun n ↦ 1-Real.exp (-2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 (r n) -
        Real.log ‖F 0‖))) atTop (𝓝 (1-Real.exp (-2*(m-Real.log ‖F 0‖)))) :=
      tendsto_const_nhds.sub (Real.continuous_exp.tendsto _ |>.comp
        (tendsto_const_nhds.mul (hm.sub tendsto_const_nhds)))
    apply le_of_tendsto_of_tendsto hleft hE
    filter_upwards [hint,hreg] with n hn ha
    exact analytic_lower hn.1 ha h0 p

end HardyBoundary

end

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real
open scoped Topology ENNReal

namespace HardyBoundary

private theorem finite_log_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (v : ℕ → X → ℂ) (f : X → ℂ) (L K : ℝ) (hK : 0 ≤ K)
    (hf : AEMeasurable f μ) (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ v n x) atTop (𝓝 (f x)))
    (hnz : ∀ n, ∀ᵐ x ∂μ, v n x ≠ 0)
    (hi : ∀ n, Integrable (fun x ↦ L-Real.log ‖v n x‖) μ)
    (hn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ L-Real.log ‖v n x‖)
    (hb : ∀ n, ∫ x, L-Real.log ‖v n x‖ ∂μ ≤ K) :
    (∀ᵐ x ∂μ, f x ≠ 0) ∧ Integrable (fun x ↦ Real.log ‖f x‖) μ ∧
    ∫ x, L-Real.log ‖f x‖ ∂μ ≤ K := by
  classical
  let e (n : ℕ) (x : X) := ENNReal.ofReal (L-Real.log ‖v n x‖)
  let g (x : X) := L-Real.log ‖f x‖
  let b (x : X) : ℝ≥0∞ := if f x = 0 then ⊤ else ENNReal.ofReal (g x)
  have hg : AEMeasurable g μ := aemeasurable_const.sub (Real.measurable_log.comp_aemeasurable hf.norm)
  have hme : ∀ n, AEMeasurable (e n) μ := fun n ↦ ENNReal.continuous_ofReal.aemeasurable.comp_aemeasurable
    ((hi n).aestronglyMeasurable.aemeasurable)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ e n x) atTop (𝓝 (b x)) := by
    filter_upwards [ht,ae_all_iff.mpr hnz] with x hx hxne
    by_cases hfx : f x = 0
    · have hnorm : Tendsto (fun n ↦ ‖v n x‖) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨by simpa [hfx] using hx.norm,Eventually.of_forall fun n ↦ norm_pos_iff.mpr (hxne n)⟩
      have hlog := Real.tendsto_log_nhdsGT_zero.comp hnorm
      have hsub : Tendsto (fun n ↦ L-Real.log ‖v n x‖) atTop atTop :=
        tendsto_const_nhds.add_atTop (tendsto_neg_atBot_atTop.comp hlog)
      simpa only [b,ite_eq_left hfx] using ENNReal.tendsto_ofReal_nhds_top.mpr hsub
    · simpa only [b,g,e,Function.comp_def,ite_eq_right hfx] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_const_nhds.sub ((Real.continuousAt_log (norm_ne_zero_iff.mpr hfx)).tendsto.comp hx.norm))
  have hI : ∫⁻ x, b x ∂μ ≤ ENNReal.ofReal K := by
    calc
      _ = ∫⁻ x, liminf (fun n ↦ e n x) atTop ∂μ := lintegral_congr_ae (hlim.mono fun _ h ↦ h.liminf_eq.symm)
      _ ≤ liminf (fun n ↦ ∫⁻ x, e n x ∂μ) atTop := lintegral_liminf_le' hme
      _ ≤ ENNReal.ofReal K := by
        apply liminf_le_of_frequently_le (Frequently.of_forall fun n ↦ ?_)
        exact (ofReal_integral_eq_lintegral_ofReal (hi n) (hn n)).symm.le.trans (ENNReal.ofReal_le_ofReal (hb n))
  have hbmeas : AEMeasurable b μ := ENNReal.aemeasurable_of_tendsto hme hlim
  have hbfin := ae_lt_top' hbmeas (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI)
  have hne : ∀ᵐ x ∂μ, f x ≠ 0 := hbfin.mono fun x hx hfx ↦ by simp [b,hfx] at hx
  have hgn : 0 ≤ᵐ[μ] g := by
    filter_upwards [ht,hne,ae_all_iff.mpr hn] with x htx hfx hp
    exact ge_of_tendsto (tendsto_const_nhds.sub ((Real.continuousAt_log (norm_ne_zero_iff.mpr hfx)).tendsto.comp htx.norm))
      (Eventually.of_forall hp)
  have hge : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal K := by
    rwa [lintegral_congr_ae (h := (hne.mono fun x hx ↦ show ENNReal.ofReal (g x) = b x by simp [b,hx]))]
  have hgi : Integrable g μ := ⟨hg.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hgn).mpr
    (hge.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hne,?_,?_⟩
  · simpa [g,Pi.sub_def] using (integrable_const L).sub hgi
  · exact (ENNReal.ofReal_le_ofReal_iff hK).mp ((ofReal_integral_eq_lintegral_ofReal hgi hgn).le.trans hge)

local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

private theorem angular_integral (g : ℂ → ℝ) (R : ℝ) :
    ∫ θ, g (circleMap 0 R θ) ∂μθ = (2*π)*circleAverage g 0 R := by
  rw [circleAverage_def,smul_eq_mul,intervalIntegral.integral_of_le Real.two_pi_pos.le]
  field_simp

/-- Logarithmic integrability and the boundary Jensen inequality for a bounded analytic
disk function with an actual almost-everywhere radial boundary trace. -/
theorem bounded_trace_log {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    (B : ℝ) (hB : ∀ z ∈ ball (0:ℂ) 1, ‖F z‖ ≤ B) (r : ℕ → ℝ) (hrn : ∀ n, r n ∈ Ioo 0 1)
    (ht : ∀ᵐ θ : ℝ ∂μθ, Tendsto (fun n ↦ F (circleMap 0 (r n) θ)) atTop (𝓝 (F (circleMap 0 1 θ)))) :
    (∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 1 θ) ≠ 0) ∧ CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 1 ∧
    Real.log ‖F 0‖ ≤ circleAverage (fun z ↦ Real.log ‖F z‖) 0 1 := by
  let L := Real.log (max 1 B)
  have hbound (z : ℂ) (hz : z ∈ ball 0 1) : Real.log ‖F z‖ ≤ L := by
    by_cases he : F z = 0
    · simpa [he,L] using Real.log_nonneg (le_max_left 1 B)
    · exact Real.log_le_log (norm_pos_iff.mpr he) ((hB z hz).trans (le_max_right _ _))
  have hreg (n : ℕ) : AnalyticOnNhd ℂ F (closedBall 0 (r n)) :=
    (hF.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball (hrn n).2)
  have hreg' (n : ℕ) : AnalyticOnNhd ℂ F (closedBall 0 |r n|) := by simpa [abs_of_pos (hrn n).1] using hreg n
  have hlog (n : ℕ) : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 (r n) :=
    ((hreg' n).mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hmem (n : ℕ) (θ : ℝ) : circleMap 0 (r n) θ ∈ ball (0:ℂ) 1 := by
    simpa [Metric.mem_ball,abs_of_pos (hrn n).1] using (hrn n).2
  let v (n : ℕ) (θ : ℝ) := F (circleMap 0 (r n) θ)
  let f (θ : ℝ) := F (circleMap 0 1 θ)
  have hvc (n : ℕ) : Continuous (v n) := hF.continuousOn.comp_continuous (continuous_circleMap _ _) (hmem n)
  have hfc : AEMeasurable f μθ := aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hvc n).aemeasurable) ht
  have hK0 := hbound 0 (mem_ball_self (by norm_num))
  have hK := mul_nonneg Real.two_pi_pos.le (sub_nonneg.mpr hK0)
  have h := finite_log_trace (μ := μθ) v f L ((2*π)*(L-Real.log ‖F 0‖)) hK hfc ht (fun n ↦ analytic_circle_ae_nonzero (hrn n).1 (hreg n) h0)
    (fun n ↦ (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp
      ((circleIntegrable_const L 0 (r n)).sub (hlog n)))
    (fun n ↦ Eventually.of_forall fun θ ↦ sub_nonneg.mpr (hbound _ (hmem n θ)))
    (fun n ↦ by
      change (∫ θ, (fun z ↦ L-Real.log ‖F z‖) (circleMap 0 (r n) θ) ∂μθ) ≤ _
      rw [angular_integral (fun z ↦ L-Real.log ‖F z‖) (r n),circleAverage_fun_sub (circleIntegrable_const L 0 (r n)) (hlog n),circleAverage_const]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (log_at_center_le_circleAverage (hrn n).1 (hreg' n) h0) _) Real.two_pi_pos.le)
  have hlog' : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr h.2.1
  refine ⟨h.1,hlog',?_⟩
  have hb := h.2.2
  change (∫ θ, (fun z ↦ L-Real.log ‖F z‖) (circleMap 0 1 θ) ∂μθ) ≤ _ at hb
  rw [angular_integral (fun z ↦ L-Real.log ‖F z‖) 1,circleAverage_fun_sub (circleIntegrable_const L 0 1) hlog',circleAverage_const] at hb
  linarith [le_of_mul_le_mul_left hb Real.two_pi_pos]

/-- For a function holomorphic in the open unit disk and continuous on its closure,
the genuine boundary logarithm is integrable, the boundary zero set is null,
and the boundary logarithmic mean is at least the logarithm at the center. -/
theorem disk_log_integrable {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0) :
    (∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 1 θ) ≠ 0) ∧ CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 1 ∧
    Real.log ‖F 0‖ ≤ circleAverage (fun z ↦ Real.log ‖F z‖) 0 1 := by
  let r (n : ℕ) : ℝ := 1-(1/2:ℝ)^(n+1)
  have hrn (n : ℕ) : r n ∈ Ioo 0 1 := by
    constructor
    · exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n))
    · exact sub_lt_self _ (by positivity)
  have hdec := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_const (1/2:ℝ)
  have hrt : Tendsto r atTop (𝓝 1) := by
    dsimp [r]
    simpa only [pow_succ,mul_zero,zero_mul,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub hdec
  have hcl := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hcl
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hcl
  apply bounded_trace_log hF.differentiableOn h0 B (fun z hz ↦ hB z (ball_subset_closedBall hz)) r hrn
  apply Eventually.of_forall
  intro θ
  have hmem (R : ℝ) (h : R ∈ Icc 0 1) : circleMap 0 R θ ∈ closedBall (0:ℂ) 1 := by
    simpa [Metric.mem_closedBall,abs_of_nonneg h.1] using h.2
  apply (hcl _ (hmem 1 (by norm_num))).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall fun n ↦ hmem (r n) ⟨(hrn n).1.le,(hrn n).2.le⟩⟩
  simp only [circleMap_zero]
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hrt).mul_const _

/-- The one-sided Hardy estimate on the closed unit disk, with all logarithmic boundary
and polynomial mean-value hypotheses discharged. -/
theorem disk_boundary_lower {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0) :
    0 ≤ circleAverage (fun z ↦ Real.log ‖F z‖) 0 1-Real.log ‖F 0‖ ∧
    ∀ p : Polynomial ℂ, 1-Real.exp (-2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 1-Real.log ‖F 0‖))
      ≤ circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 1 := by
  obtain ⟨hne,hl,hJ⟩ := disk_log_integrable hF h0
  exact ⟨sub_nonneg.mpr hJ,fun p ↦ disk_lower F p (by norm_num) hF h0 hl hne⟩

end HardyBoundary

end

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real
open scoped Topology

namespace HardyBoundary

local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

/-- Any bounded holomorphic function with its genuine a.e. radial trace satisfies the lower
estimate. The trace, interior values, and center are represented by a single function on ℂ. -/
theorem bounded_boundary_lower {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    (B : ℝ) (hB : ∀ z ∈ ball (0:ℂ) 1, ‖F z‖ ≤ B)
    (r : ℕ → ℝ) (hrn : ∀ n, r n ∈ Ioo 0 1) (hr : Tendsto r atTop (𝓝 1))
    (ht : ∀ᵐ θ : ℝ ∂μθ, Tendsto (fun n ↦ F (circleMap 0 (r n) θ)) atTop (𝓝 (F (circleMap 0 1 θ)))) :
    0 ≤ circleAverage (fun z ↦ Real.log ‖F z‖) 0 1-Real.log ‖F 0‖ ∧
    ∀ p : Polynomial ℂ, 1-Real.exp (-2*(circleAverage (fun z ↦ Real.log ‖F z‖) 0 1-Real.log ‖F 0‖))
      ≤ circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 1 := by
  obtain ⟨hne,hl,hJ⟩ := bounded_trace_log hF h0 B hB r hrn ht
  refine ⟨sub_nonneg.mpr hJ,?_⟩
  intro p
  let q (z : ℂ) := F z*p.eval z
  let v (n : ℕ) (θ : ℝ) := q (circleMap 0 (r n) θ)
  let f (θ : ℝ) := q (circleMap 0 1 θ)
  have hp := (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) p).differentiableOn
  have hpc : Continuous (fun z ↦ p.eval z) := (differentiableOn_univ.mp hp).continuous
  have hdiff : DifferentiableOn ℂ q (ball 0 1) := hF.mul (hp.mono (subset_univ _))
  have hmem (n : ℕ) (θ : ℝ) : circleMap 0 (r n) θ ∈ ball (0:ℂ) 1 := by
    simpa [Metric.mem_ball,abs_of_pos (hrn n).1] using (hrn n).2
  have hvc (n : ℕ) : Continuous (v n) := hdiff.continuousOn.comp_continuous (continuous_circleMap _ _) (hmem n)
  obtain ⟨P,hP⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hpc.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_ball_self (by norm_num)))
  have hbd (n : ℕ) (θ : ℝ) : ‖v n θ‖ ≤ B*P := by
    change ‖F _ * p.eval _‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hB _ (hmem n θ)) (hP _ (ball_subset_closedBall (hmem n θ))) (norm_nonneg _) hB0
  have htq : ∀ᵐ θ : ℝ ∂μθ, Tendsto (fun n ↦ v n θ) atTop (𝓝 (f θ)) := by
    filter_upwards [ht] with θ hθ
    apply hθ.mul
    apply hpc.continuousAt.tendsto.comp
    simp only [circleMap_zero]
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const _
  have hm : AEStronglyMeasurable f μθ :=
    (aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hvc n).aemeasurable) htq).aestronglyMeasurable
  have hfbd : ∀ᵐ θ : ℝ ∂μθ, ‖f θ‖ ≤ B*P :=
    htq.mono fun θ hθ ↦ le_of_tendsto hθ.norm (Eventually.of_forall fun n ↦ hbd n θ)
  have hi : CircleIntegrable q 0 1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
    ((integrable_const (B*P)).mono' hm hfbd)
  have hie : CircleIntegrable (fun z ↦ ‖q z‖^2) 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr <|
      (integrable_const ((B*P)^2)).mono' (hm.norm.pow 2) (hfbd.mono fun θ hθ ↦ by
        change ‖(‖f θ‖^2 : ℝ)‖ ≤ _
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f θ‖)]
        exact pow_le_pow_left₀ (norm_nonneg _) hθ 2)
  have hD := tendsto_integral_of_dominated_convergence (μ := μθ) (fun _ ↦ B*P)
    (fun n ↦ (hvc n).aestronglyMeasurable) (integrable_const _) (fun n ↦ Eventually.of_forall (hbd n)) htq
  have hav : Tendsto (fun n ↦ circleAverage q 0 (r n)) atTop (𝓝 (circleAverage q 0 1)) := by
    simp only [circleAverage_def,intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact tendsto_const_nhds.smul hD
  have hmean (n : ℕ) : circleAverage q 0 (r n) = q 0 :=
    (hdiff.diffContOnCl_ball (by rw [abs_of_pos (hrn n).1]; exact closedBall_subset_ball (hrn n).2)).circleAverage
  have hmean1 : circleAverage q 0 1 = q 0 :=
    tendsto_nhds_unique hav (by simp only [hmean]; exact tendsto_const_nhds)
  exact boundary_lower one_pos F p h0 hl hne hi hie hmean1

end HardyBoundary

end
