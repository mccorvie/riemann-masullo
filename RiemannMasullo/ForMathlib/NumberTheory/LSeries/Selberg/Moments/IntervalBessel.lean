module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.GaussianBessel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma continuous_ft_and_norm_le {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (ft f) ∧ ∀ t, ‖ft f t‖ ≤ ∫ y, ‖f y‖ := by
  have hdom (t : ℝ) : ∀ᵐ y, ‖f y * osc (t * y)‖ ≤ ‖f y‖ :=
    ae_of_all _ fun y ↦ by
      simp only [norm_mul, osc, Complex.norm_exp_I_mul_ofReal, mul_one, le_refl]
  constructor
  · unfold ft
    refine continuous_of_dominated ?_ hdom hf.norm ?_
    · intro t
      apply hf.aestronglyMeasurable.mul
      apply Continuous.aestronglyMeasurable
      unfold osc
      fun_prop
    · apply ae_of_all
      intro y
      unfold osc
      fun_prop
  · exact fun t ↦ norm_integral_le_of_norm_le hf.norm (hdom t)

/-- Card 38. For an integrable complex function with integrable squared norm, its Fourier energy
on (0,U] is at most 2πe times its squared norm integral for U > 0.
Restriction of Titchmarsh §10.10 Plancherel to the Lean domain, p. 269. -/
theorem interval_bessel (f : ℝ → ℂ) (hf : Integrable f) (hf₂ : Integrable (fun y ↦ ‖f y‖^2))
    (U : ℝ) (hU : 0 < U) :
    (∫ t in Ioc (0 : ℝ) U, ‖ft f t‖^2) ≤
      2*Real.pi*Real.exp 1 * ∫ y : ℝ, ‖f y‖^2 := by
  obtain ⟨hcont, hbound⟩ := continuous_ft_and_norm_le hf
  let w (t : ℝ) := Real.exp (-(t / U) ^ 2)
  have hw : Integrable w := by
    simpa [w] using (integrable_exp_neg_mul_sq (b := 1) one_pos).comp_div hU.ne'
  have henergy : Continuous (fun t ↦ ‖ft f t‖ ^ 2) := hcont.norm.pow 2
  have hweighted : Integrable (fun t ↦ w t * ‖ft f t‖ ^ 2) := by
    apply hw.mul_bdd (c := (∫ y, ‖f y‖) ^ 2) henergy.aestronglyMeasurable
    apply ae_of_all
    intro t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) U, Real.exp 1 * (w t * ‖ft f t‖ ^ 2) := by
      apply setIntegral_mono_on henergy.integrableOn_Ioc
        (hweighted.const_mul _).integrableOn measurableSet_Ioc
      intro t ht
      dsimp only [w]
      rw [← mul_assoc, ← Real.exp_add]
      apply le_mul_of_one_le_left (sq_nonneg _)
      rw [Real.one_le_exp_iff, ← sub_eq_add_neg, sub_nonneg]
      exact pow_le_one₀ (div_nonneg ht.1.le hU.le) ((div_le_one hU).2 ht.2)
    _ = Real.exp 1 * ∫ t in Ioc (0 : ℝ) U, w t * ‖ft f t‖ ^ 2 := integral_const_mul _ _
    _ ≤ Real.exp 1 * ∫ t : ℝ, w t * ‖ft f t‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact setIntegral_le_integral hweighted (ae_of_all _ fun t ↦ mul_nonneg
        (Real.exp_pos _).le (sq_nonneg _))
    _ ≤ Real.exp 1 * (2 * Real.pi * ∫ y : ℝ, ‖f y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (gaussian_bessel f hf hf₂ U hU) (Real.exp_pos _).le
    _ = _ := by ring

end RiemannMasullo.Selberg
