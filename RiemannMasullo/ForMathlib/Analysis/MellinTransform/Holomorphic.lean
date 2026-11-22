module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

public section

open Complex Filter MeasureTheory Set Metric Topology

namespace RiemannMasullo

/-- Integrating a complex power of a positive measurable function against a fixed weight
is holomorphic in every open strip in which the weighted integrand is integrable. -/
theorem analyticOnNhd_integral_mul_cpow_of_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℂ) (n : α → ℝ) (hn : Measurable n) (hp : ∀ x, 0 < n x)
    {I : Set ℝ} (hI : IsOpen I)
    (hint : ∀ z : ℂ, z.re ∈ I → Integrable (fun x ↦ f x * (n x : ℂ) ^ z) μ) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ x, f x * (n x : ℂ) ^ z ∂μ) (re ⁻¹' I) := by
  let W (z : ℂ) (x : α) := f x * (n x : ℂ) ^ z
  let D (z : ℂ) (x : α) := W z x * log (n x : ℂ)
  have hD (z : ℂ) (x : α) : HasDerivAt (fun w ↦ W w x) (D z x) z := by
    simpa only [W, D, id_eq, mul_assoc, mul_one] using
      (((hasDerivAt_id z).const_cpow (Or.inl (ofReal_ne_zero.mpr (hp x).ne'))).const_mul (f x))
  apply DifferentiableOn.analyticOnNhd _ (hI.preimage continuous_re)
  intro z hz
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hz)
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let a := z.re - 2 * r
  let b := z.re + 2 * r
  have ha : a ∈ I := hsub (by rw [mem_ball, Real.dist_eq, abs_lt]; dsimp [a, r]; constructor <;> linarith)
  have hb : b ∈ I := hsub (by rw [mem_ball, Real.dist_eq, abs_lt]; dsimp [b, r]; constructor <;> linarith)
  have hnorm (w : ℂ) (x : α) : ‖W w x‖ = ‖f x‖ * n x ^ w.re := by
    dsimp only [W]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hp x)]
  have hbound (x : α) (w : ℂ) (hw : w ∈ ball z r) :
      ‖D w x‖ ≤ (‖W a x‖ + ‖W b x‖) / r := by
    rw [← (hD w x).deriv]
    have hdiff : Differentiable ℂ (fun t ↦ W t x) := fun t ↦ (hD t x).differentiableAt
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff.diffContOnCl
    intro t ht
    have hd : |t.re - z.re| ≤ 2 * r := calc
      |t.re - z.re| ≤ dist t z := by simpa only [dist_eq_norm, sub_re] using abs_re_le_norm (t - z)
      _ ≤ dist t w + dist w z := dist_triangle _ _ _
      _ ≤ 2 * r := by rw [mem_sphere.mp ht]; linarith [mem_ball.mp hw]
    rw [hnorm, hnorm, hnorm, ofReal_re, ofReal_re]
    rcases le_total 1 (n x) with h | h
    · exact le_add_of_nonneg_of_le (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _)) (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h (by dsimp [b]; linarith [(abs_le.mp hd).2])) (norm_nonneg _))
    · exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hp x) h (by dsimp [a]; linarith [(abs_le.mp hd).1]))
        (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
  have hmeas : ∀ᶠ t : ℂ in 𝓝 z, AEStronglyMeasurable (W t) μ :=
    Filter.Eventually.mono ((hI.preimage continuous_re).mem_nhds hz) fun t ht ↦ (hint t ht).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z hr) hmeas (hint z hz)
    ((hint z hz).aestronglyMeasurable.mul
      ((measurable_log.comp (continuous_ofReal.measurable.comp hn)).aestronglyMeasurable))
    (ae_of_all _ hbound) (((hint a ha).norm.add (hint b hb).norm).div_const r)
    (ae_of_all _ fun x w _ ↦ hD w x)).2.differentiableAt.differentiableWithinAt

end RiemannMasullo
