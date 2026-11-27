module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 39. Integrating the Fourier transform of an integrable function over [t,t+h] equals the
transform at t of the function multiplied by the length-h window multiplier.
Titchmarsh, §10.10, (10.10.1), p. 269, short-window multiplier. -/
theorem window_transform (f : ℝ → ℂ) (hf : Integrable f) (h t : ℝ) (hh : 0 ≤ h) :
    (∫ u in t..t+h, ft f u) = ft (fun y ↦ f y * mult h y) t := by
  calc
    _ = ∫ u in (0 : ℝ)..h, ft f (t + u) := by
      rw [intervalIntegral.integral_comp_add_left, add_zero]
    _ = ∫ y : ℝ, ∫ u in (0 : ℝ)..h, f y * osc ((t + u) * y) := by
      apply intervalIntegral_integral_swap
      rw [Set.uIoc_of_le hh]
      apply (hf.comp_snd (volume.restrict (Set.Ioc 0 h))).mul_bdd (c := 1)
      · apply Continuous.aestronglyMeasurable
        unfold osc
        fun_prop
      · exact ae_of_all _ fun p ↦ (Complex.norm_exp_I_mul_ofReal ((t + p.1) * p.2)).le
    _ = _ := by
      unfold ft
      apply integral_congr_ae
      refine ae_of_all _ fun y ↦ ?_
      have phase (u : ℝ) : osc ((t + u) * y) = osc (t * y) * osc (u * y) := by
        rw [add_mul, osc, Complex.ofReal_add, mul_add, Complex.exp_add]
        rfl
      simp_rw [phase, ← mul_assoc]
      rw [intervalIntegral.integral_const_mul, mult]
      ring

end RiemannMasullo.Selberg
