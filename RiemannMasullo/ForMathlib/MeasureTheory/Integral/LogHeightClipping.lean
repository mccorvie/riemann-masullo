module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.DyadicLogTail
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PoissonLogTail
import Mathlib.Tactic

/-! # Height logarithms and clipping under the Cauchy measure

A dyadic logarithmic tail absorbs an added multiple of the height logarithm. For any finite
measure, the integrated increase from clipping a nonnegative function at a positive floor
is controlled by its logarithmic tail. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Real
open scoped Topology ENNReal

namespace RiemannMasullo.LogQuadrature

private theorem log_height_on_dyadic_box (n : ℕ) {t : ℝ} (ht : |t| ≤ (2:ℝ)^n) :
    Real.log (2+|t|) ≤ 2*((n:ℝ)+1)^2 := by
  have hpow : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hupper : 2 + |t| ≤ (2:ℝ)^(n+2) := by
    rw [pow_add]
    norm_num
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 2+|t|) hupper
  rw [Real.log_pow] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  push_cast at hlog
  calc
    Real.log (2+|t|) ≤ ((n:ℝ)+2)*Real.log 2 := hlog
    _ ≤ ((n:ℝ)+2)*1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 2*((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ), Nat.cast_nonneg (α:=ℝ) n]

/-- A fixed height logarithm can be added to a boundary value with a dyadic
square threshold without changing the scale of its integrated logarithmic tail. -/
theorem integrable_and_hasIntegratedLogTail_of_logHeight_majorant {g v : ℝ → ℝ} (N : ℕ)
    (hm : Measurable v) (hi : Integrable g poissonMeasure)
    (hpoint : ∀ t, |v t| ≤ |g t| + (N:ℝ)*Real.log (2+|t|))
    (ht : ∃ A > 0, ∃ K > 0, ∀ n : ℕ,
      poissonMeasure {t | A*((n:ℝ)+1)^2 < |g t|} ≤ ENNReal.ofReal (K*(1/2:ℝ)^n)) :
    Integrable v poissonMeasure ∧ HasIntegratedLogTail poissonMeasure v := by
  obtain ⟨A,hA,K,hK,ht⟩ := ht
  have hiv : Integrable v poissonMeasure := by
    apply (hi.abs.add (poisson_logMoment.const_mul (N:ℝ))).mono' hm.aestronglyMeasurable
    filter_upwards with t
    exact hpoint t
  refine ⟨hiv, ?_⟩
  apply hasIntegratedLogTail_of_dyadic_sq poissonMeasure hm hiv
  refine ⟨A+2*N, by positivity, K+3/π, by positivity, fun n ↦ ?_⟩
  have hsub : {t | (A+2*(N:ℝ))*((n:ℝ)+1)^2 < |v t|} ⊆
      {t | A*((n:ℝ)+1)^2 < |g t|} ∪ {t | (2:ℝ)^n < |t|} := by
    intro t ht'
    by_contra hn
    simp only [mem_union,mem_ofPred_eq,not_or,not_lt] at hn
    have hh := mul_le_mul_of_nonneg_left (log_height_on_dyadic_box n hn.2) (Nat.cast_nonneg (α:=ℝ) N)
    exact (not_lt_of_ge (calc
      |v t| ≤ |g t| + (N:ℝ) * Real.log (2+|t|) := hpoint t
      _ ≤ A*((n:ℝ)+1)^2 + (N:ℝ)*(2*((n:ℝ)+1)^2) := add_le_add hn.1 hh
      _ = (A+2*(N:ℝ))*((n:ℝ)+1)^2 := by ring)) ht'
  calc
    _ ≤ poissonMeasure ({t | A*((n:ℝ)+1)^2 < |g t|} ∪ {t | (2:ℝ)^n < |t|}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (K*(1/2:ℝ)^n) + ENNReal.ofReal ((3/π)*(1/2:ℝ)^n) :=
      add_le_add (ht n) (poissonMeasure_abs_gt_two_pow n)
    _ = _ := by rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]

private theorem log_floor_pointwise {r Y : ℝ} (hr : 0 ≤ r) (hY : 0 ≤ Y) :
    |Real.log (max r (Real.exp (-Y))) - Real.log r| ≤ |Real.log r|+Y ∧
    Real.log (max r (Real.exp (-Y))) - Real.log r ≤
      if Y ≤ |Real.log r| then |Real.log r| else 0 := by
  by_cases hlow : Real.exp (-Y) ≤ r
  · simp only [max_eq_left hlow,sub_self,abs_zero]
    exact ⟨by positivity, by split_ifs <;> positivity⟩
  · rw [max_eq_right (by linarith : r ≤ Real.exp (-Y)), Real.log_exp]
    rcases hr.eq_or_lt with rfl | hr'
    · simp [abs_of_nonneg hY,hY]
    · have hlog := Real.log_le_log hr' (le_of_not_ge hlow)
      rw [Real.log_exp] at hlog
      rw [abs_of_nonpos (by linarith : Real.log r ≤ 0), abs_of_nonneg (by linarith : 0 ≤ -Y-Real.log r),
        ite_eq_left (by linarith : Y ≤ -Real.log r)]
      constructor <;> linarith

/-- The integrated upward clipping error is bounded by the absolute logarithm
tail. This also handles Lean's total logarithm at the zeros of the input. -/
theorem integral_log_floor_sub_le_abs_tail {μ : Measure ℝ} [IsFiniteMeasure μ] {v : ℝ → ℝ}
    (hm : Measurable v) (hn : ∀ t, 0 ≤ v t) (hi : Integrable (fun t ↦ Real.log (v t)) μ)
    {Y : ℝ} (hY : 0 ≤ Y) :
    (∫ t, (Real.log (max (v t) (Real.exp (-Y))) - Real.log (v t)) ∂μ) ≤
      ∫ t in {t | Y ≤ |Real.log (v t)|}, |Real.log (v t)| ∂μ := by
  classical
  let E := {t | Y ≤ |Real.log (v t)|}
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (Real.measurable_log.comp hm))
  have hv : Integrable (fun t ↦ Real.log (max (v t) (Real.exp (-Y))) - Real.log (v t)) μ := by
    apply (hi.abs.add (integrable_const Y)).mono'
      (((Real.measurable_log.comp (hm.max measurable_const)).sub (Real.measurable_log.comp hm)).aestronglyMeasurable)
    filter_upwards with t
    exact (log_floor_pointwise (hn t) hY).1
  rw [←integral_indicator hE]
  apply integral_mono hv (hi.abs.indicator hE)
  intro t
  simpa only [Set.indicator_apply,E,mem_ofPred_eq] using (log_floor_pointwise (hn t) hY).2

end RiemannMasullo.LogQuadrature
