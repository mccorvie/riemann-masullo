module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian increments preserving three moments

A signed combination of the centered Gaussian laws of variances `v` and `2v`
has mass one and both of its exponential moments at `±1` equal one.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

public noncomputable section

namespace RiemannMasullo

/-- The signed expectation of an increment with Gaussian variances `v` and `2v`.
The coefficient of the second expectation is chosen to preserve both unit
exponential moments. -/
@[expose] def compensatedGaussianIncrement (v : ℝ≥0) (f : ℝ → ℝ) : ℝ :=
  (1 + Real.exp (-(v : ℝ) / 2)) * (∫ h, f h ∂gaussianReal 0 v) -
    Real.exp (-(v : ℝ) / 2) * (∫ h, f h ∂gaussianReal 0 (2 * v))

private theorem centeredGaussian_unit_moment (v : ℝ≥0) (t : ℝ) (ht : t^2 = 1) :
    (∫ h, Real.exp (t * h) ∂gaussianReal 0 v) = Real.exp ((v : ℝ) / 2) := by
  change mgf id (gaussianReal 0 v) t = _
  rw [mgf_id_gaussianReal]
  simp [ht]

private theorem compensatedGaussian_unit_moment (v : ℝ≥0) :
    (1 + Real.exp (-(v : ℝ) / 2)) * Real.exp ((v : ℝ) / 2) -
      Real.exp (-(v : ℝ) / 2) * Real.exp ((2 * (v : ℝ)) / 2) = 1 := by
  have h₁ : Real.exp (-(v : ℝ) / 2) * Real.exp ((v : ℝ) / 2) = 1 := by
    rw [← Real.exp_add, show -(v : ℝ)/2 + v/2 = 0 by ring, Real.exp_zero]
  have h₂ : Real.exp (-(v : ℝ) / 2) * Real.exp ((2 * (v : ℝ)) / 2) =
      Real.exp ((v : ℝ) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [add_mul, one_mul, h₁, h₂]
  ring

/-- The signed Gaussian expectation acts as evaluation at zero on every linear
combination of the constant and the two exponential functions with exponents `±1`. -/
theorem compensatedGaussianIncrement_const_add_exp (v : ℝ≥0) (c a b : ℝ) :
    compensatedGaussianIncrement v (fun h ↦ c + a * Real.exp h + b * Real.exp (-h)) =
      c + a + b := by
  have hev (w : ℝ≥0) :
      (∫ h, c + a * Real.exp h + b * Real.exp (-h) ∂gaussianReal 0 w) =
        c + (a + b) * Real.exp ((w : ℝ)/2) := by
    have hp : Integrable Real.exp (gaussianReal 0 w) := by
      simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := w) 1)
    have hn : Integrable (fun h ↦ Real.exp (-h)) (gaussianReal 0 w) := by
      simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := w) (-1))
    have hc : Integrable (fun h ↦ c + a * Real.exp h) (gaussianReal 0 w) :=
      (integrable_const c).add (hp.const_mul a)
    rw [integral_add hc (hn.const_mul b),
      integral_add (integrable_const c) (hp.const_mul a), integral_const_mul, integral_const_mul]
    have hep := centeredGaussian_unit_moment w 1 (by norm_num)
    have hen := centeredGaussian_unit_moment w (-1) (by norm_num)
    simp only [one_mul, neg_one_mul] at hep hen
    rw [hep, hen, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  rw [compensatedGaussianIncrement, hev, hev, NNReal.coe_mul, NNReal.coe_ofNat]
  calc _ = c + (a + b) * ((1 + Real.exp (-(v : ℝ) / 2)) * Real.exp ((v : ℝ) / 2) -
        Real.exp (-(v : ℝ) / 2) * Real.exp ((2 * (v : ℝ)) / 2)) := by ring
       _ = _ := by rw [compensatedGaussian_unit_moment]; ring

/-- Compensation preserves every constant, in particular the total mass. -/
theorem compensatedGaussianIncrement_const (v : ℝ≥0) (c : ℝ) :
    compensatedGaussianIncrement v (fun _ ↦ c) = c := by
  simpa using compensatedGaussianIncrement_const_add_exp v c 0 0

/-- The positive unit exponential moment of the signed expectation is one. -/
theorem compensatedGaussianIncrement_exp (v : ℝ≥0) :
    compensatedGaussianIncrement v Real.exp = 1 := by
  simpa using compensatedGaussianIncrement_const_add_exp v 0 1 0

/-- The negative unit exponential moment of the signed expectation is one. -/
theorem compensatedGaussianIncrement_exp_neg (v : ℝ≥0) :
    compensatedGaussianIncrement v (fun h ↦ Real.exp (-h)) = 1 := by
  simpa using compensatedGaussianIncrement_const_add_exp v 0 0 1

/-- Every polynomial moment times `exp (a |h|)` is integrable for a real Gaussian
law, for any real mean and exponential rate, including zero variance. -/
theorem gaussianReal_integrable_abs_pow_mul_exp_abs (μ : ℝ) (v : ℝ≥0) (n : ℕ) (a : ℝ) :
    Integrable (fun h : ℝ ↦ |h|^n * Real.exp (a * |h|)) (gaussianReal μ v) := by
  have hi (t : ℝ) : Integrable (fun h : ℝ ↦ |h|^n * Real.exp (t * h)) (gaussianReal μ v) :=
    integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet (X := fun h : ℝ ↦ h) (by simp) n
  refine ((hi a).add (hi (-a))).mono' (by fun_prop) (Filter.Eventually.of_forall fun h ↦ ?_)
  have he : Real.exp (a * |h|) ≤ Real.exp (a * h) + Real.exp (-a * h) := by
    rcases le_total 0 h with hh | hh
    · rw [abs_of_nonneg hh]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hh, mul_neg, neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  simpa only [Pi.add_apply, Real.norm_of_nonneg (by positivity : 0 ≤ |h|^n * Real.exp (a * |h|)),
    mul_add] using mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg h) n)

end RiemannMasullo
