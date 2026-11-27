module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The difference of two logarithmic derivatives of Gamma

The removable difference of two beta integrals yields Gauss's integral for the
difference of digamma values. See NIST DLMF 5.9.16 and Abramowitz–Stegun 6.3.22.
-/

public noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Complex

private theorem hasDerivAt_gamma_ratio_zero (w : ℂ) (hw : 0 < w.re) :
    HasDerivAt (fun z : ℂ ↦ Gamma w / Gamma (w + z)) (-logDeriv Gamma w) 0 := by
  have hG := (hasDerivAt_Gamma_of_re_pos hw).differentiableAt.hasDerivAt
  have hshift : HasDerivAt (fun z : ℂ ↦ w + z) 1 0 := (hasDerivAt_id' 0).const_add w
  have hD : HasDerivAt (fun z : ℂ ↦ Gamma (w + z)) (deriv Gamma w) 0 := by
    simpa only [Function.comp_def, add_zero, mul_one] using
      (show HasDerivAt Gamma (deriv Gamma w) (w + 0) by simpa only [add_zero] using hG).comp 0 hshift
  have hne := Gamma_ne_zero_of_re_pos hw
  convert (hasDerivAt_const (0 : ℂ) (Gamma w)).div hD (by simpa only [add_zero] using hne) using 1
  simp only [zero_mul, zero_sub, add_zero, logDeriv_apply]
  field_simp

/-- Cancellation of the common simple beta pole at its second argument zero. -/
private theorem tendsto_beta_difference {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Tendsto (fun h : ℝ ↦ betaIntegral u h - betaIntegral v h) (𝓝[>] 0)
      (𝓝 (logDeriv Gamma v - logDeriv Gamma u)) := by
  let D (z : ℂ) := Gamma u / Gamma (u + z) - Gamma v / Gamma (v + z)
  have hd : HasDerivAt D (logDeriv Gamma v - logDeriv Gamma u) 0 := by
    convert (hasDerivAt_gamma_ratio_zero u hu).sub (hasDerivAt_gamma_ratio_zero v hv) using 1
    ring
  have hzero : D 0 = 0 := by simp [D, Gamma_ne_zero_of_re_pos hu, Gamma_ne_zero_of_re_pos hv]
  have hs : Tendsto (fun z : ℂ ↦ z⁻¹ * D z) (𝓝[≠] 0)
      (𝓝 (logDeriv Gamma v - logDeriv Gamma u)) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using hd.tendsto_slope_zero
  have hcast : Tendsto ((↑) : ℝ → ℂ) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [ofReal_zero] using (continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact ofReal_ne_zero.mpr (ne_of_gt hh)
  have h := (tendsto_self_mul_Gamma_nhds_zero.mul hs).comp hcast
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < (y : ℂ).re := hy
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  rw [betaIntegral_eq_Gamma_mul_div u y hu hy', betaIntegral_eq_Gamma_mul_div v y hv hy']
  change ((y : ℂ) * Gamma y) * ((y : ℂ)⁻¹ * D y) = _
  rw [mul_mul_mul_comm, mul_inv_cancel₀ hy0, one_mul]
  unfold D
  ring

private def betaDifferenceKernel (u v : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) ^ (u - 1) - (x : ℂ) ^ (v - 1)) / (1 - (x : ℂ))

private theorem betaDifferenceKernel_integrable {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    IntegrableOn (betaDifferenceKernel u v) (Ioo 0 1) := by
  have hleft : IntervalIntegrable (betaDifferenceKernel u v) volume 0 (1/2) := by
    change IntervalIntegrable (fun x : ℝ ↦ ((x : ℂ)^(u-1) - (x : ℂ)^(v-1))/(1-(x : ℂ))) volume 0 (1/2)
    simpa only [zero_sub, cpow_neg_one, div_eq_mul_inv, sub_mul] using
      (betaIntegral_convergent_left hu 0).sub (betaIntegral_convergent_left hv 0)
  let f (z : ℂ) := z ^ (v-1) - z ^ (u-1)
  have hdiff {x : ℝ} (hx : 0 < x) : DifferentiableAt ℂ f (x : ℂ) := by
    have hpow (a : ℂ) : DifferentiableAt ℂ (fun z : ℂ ↦ z ^ a) (x : ℂ) :=
      (differentiableAt_id (x := (x : ℂ))).cpow_const (ofReal_mem_slitPlane.mpr hx)
    exact (hpow (v-1)).sub (hpow (u-1))
  have hc : ContinuousOn (fun x : ℝ ↦ dslope f 1 (x : ℂ)) (Icc (1/2) 1) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hd : ContinuousAt (dslope f 1) (x : ℂ) := by
      by_cases h : (x : ℂ) = 1
      · rw [h]
        exact continuousAt_dslope_same.mpr (by simpa using hdiff (x := 1) zero_lt_one)
      · exact (continuousAt_dslope_of_ne h).mpr (hdiff (by linarith [hx.1])).continuousAt
    exact hd.comp continuous_ofReal.continuousAt
  have hright : IntegrableOn (betaDifferenceKernel u v) (Ioo (1/2) 1) := by
    refine ((hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro x hx
    have hn : (x : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hx.2)
    dsimp only
    rw [dslope_of_ne _ hn, slope_def_field]
    simp only [f, one_cpow, sub_self, sub_zero, betaDifferenceKernel]
    rw [← neg_div_neg_eq]
    congr 1 <;> ring
  apply ((hleft.1.union hright)).mono_set
  intro x hx
  by_cases hy : x ≤ 1/2
  · exact Or.inl ⟨hx.1,hy⟩
  · exact Or.inr ⟨lt_of_not_ge hy,hx.2⟩

private theorem betaDifference_as_integral {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    (h : ℝ) (hh : 0 < h) :
    betaIntegral u h - betaIntegral v h =
      ∫ x : ℝ in Ioo 0 1, ((1-x)^h : ℝ) • betaDifferenceKernel u v x := by
  have hh' : 0 < (h : ℂ).re := hh
  rw [betaIntegral, betaIntegral, ← intervalIntegral.integral_sub
    (betaIntegral_convergent hu hh') (betaIntegral_convergent hv hh'),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hp : 0 < 1-x := sub_pos.mpr hx.2
  have hn : (1 : ℂ) - x ≠ 0 := by exact_mod_cast hp.ne'
  dsimp only
  rw [Complex.real_smul, ofReal_cpow hp.le, ofReal_sub, ofReal_one,
    cpow_sub _ _ hn, cpow_one, betaDifferenceKernel]
  ring

private theorem integral_betaDifferenceKernel {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ∫ x : ℝ in Ioo 0 1, betaDifferenceKernel u v x = logDeriv Gamma v - logDeriv Gamma u := by
  let K := betaDifferenceKernel u v
  have hK : IntegrableOn K (Ioo 0 1) := betaDifferenceKernel_integrable hu hv
  have hlim : Tendsto (fun h : ℝ ↦ ∫ x : ℝ in Ioo 0 1, ((1-x)^h : ℝ) • K x)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ in Ioo 0 1, K x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖K x‖)
    · exact .of_forall fun h ↦ (show Measurable (fun x : ℝ ↦ (1-x)^h) by fun_prop).aestronglyMeasurable.smul hK.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
      have hw : (1-x)^h ≤ 1 :=
        Real.rpow_le_one (sub_nonneg.mpr hx.2.le) (by linarith [hx.1]) (le_of_lt hh)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)]
      exact mul_le_of_le_one_left (norm_nonneg _) hw
    · exact hK.norm
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
      have hw := (Real.continuous_const_rpow (sub_pos.mpr hx.2).ne').tendsto (0 : ℝ)
      simpa only [Real.rpow_zero, one_smul] using
        (hw.mono_left nhdsWithin_le_nhds).smul (tendsto_const_nhds (x := K x))
  apply tendsto_nhds_unique hlim
  refine (tendsto_beta_difference hu hv).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact betaDifference_as_integral hu hv h hh

private theorem exp_mul_cpow_neg {x : ℝ} (s : ℂ) :
    (Real.exp (-x) : ℂ) * (Real.exp (-x) : ℂ) ^ (s - 1) = exp (-s * x) := by
  have hne : (Real.exp (-x) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  calc
    _ = (Real.exp (-x) : ℂ) ^ s := by rw [cpow_sub s 1 hne, cpow_one]; field_simp
    _ = _ := by
      rw [cpow_def_of_ne_zero hne, ← ofReal_log (Real.exp_pos _).le, Real.log_exp, ofReal_neg]
      congr 1
      ring

/-- Gauss's digamma difference formula on the positive half-plane, with absolute integrability.
Here `logDeriv Gamma` is the usual digamma function. -/
theorem gauss_logDeriv_Gamma_difference {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    IntegrableOn (fun t : ℝ ↦ (exp (-u * t) - exp (-v * t)) / (1 - exp (-(t : ℂ)))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (exp (-u * t) - exp (-v * t)) / (1 - exp (-(t : ℂ)))) =
      logDeriv Gamma v - logDeriv Gamma u := by
  let p (t : ℝ) := Real.exp (-t)
  have hi : p '' Ioi 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)⟩
    · intro hx
      exact ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx.1 hx.2), by simp [p, Real.exp_log hx.1]⟩
  have hj : InjOn p (Ioi 0) := (Real.exp_injective.comp neg_injective).injOn
  have hd (t : ℝ) (_ : t ∈ Ioi 0) : HasDerivWithinAt p (-p t) (Ioi 0) t := by
    simpa only [p, Function.comp_def, mul_neg_one] using
      ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).hasDerivWithinAt
  have hk (t : ℝ) : |-(p t)| • betaDifferenceKernel u v (p t) =
      (exp (-u * t) - exp (-v * t)) / (1 - exp (-(t : ℂ))) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul,
      betaDifferenceKernel, ← mul_div_assoc, mul_sub, exp_mul_cpow_neg, exp_mul_cpow_neg]
    rw [show (p t : ℂ) = exp (-(t : ℂ)) by simp [p]]
  have hfi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hj
    (betaDifferenceKernel u v)).mp (hi ▸ betaDifferenceKernel_integrable hu hv)
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hj
    (betaDifferenceKernel u v)
  simp only [hi, hk, integral_betaDifferenceKernel hu hv] at heq
  exact ⟨by simpa only [hk] using hfi, heq.symm⟩

/-- The scaled Gauss integral for every real `k > 0`. Its arguments and the overall factor
are both scaled by `1/k`. -/
theorem gauss_logDeriv_Gamma_difference_scaled {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun t : ℝ ↦ (exp (-u * t) - exp (-v * t)) / (1 - exp (-(k : ℂ) * t))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (exp (-u * t) - exp (-v * t)) / (1 - exp (-(k : ℂ) * t))) =
      (logDeriv Gamma (v/k) - logDeriv Gamma (u/k)) / k := by
  let K (x : ℝ) := (exp (-(u/k) * x) - exp (-(v/k) * x)) / (1 - exp (-(x : ℂ)))
  have hd (z : ℂ) (hz : 0 < z.re) : 0 < (z/k).re := by
    simpa only [div_ofReal_re] using div_pos hz hk
  obtain ⟨hi, heq⟩ := gauss_logDeriv_Gamma_difference (hd u hu) (hd v hv)
  have he (t : ℝ) : K (k*t) =
      (exp (-u*t) - exp (-v*t)) / (1 - exp (-(k : ℂ) * t)) := by
    unfold K
    rw [ofReal_mul]
    have hm (z : ℂ) : -(z/k) * ((k : ℂ) * t) = -z * t := by
      field_simp [ofReal_ne_zero.mpr hk.ne']
    simp only [hm, neg_mul]
  have hi' : IntegrableOn (fun t ↦ K (k*t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff K 0 hk).mpr (by simpa only [mul_zero, K] using hi)
  have heq' := integral_comp_mul_left_Ioi K 0 hk
  rw [mul_zero, show (∫ x in Ioi 0, K x) = _ from heq, Complex.real_smul,
    ofReal_inv] at heq'
  exact ⟨by simpa only [he] using hi', by simpa only [he, div_eq_inv_mul] using heq'⟩

end Complex
