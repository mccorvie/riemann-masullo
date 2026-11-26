module

public import RiemannMasullo.Ch13_ZerosHecke.CompensatedGaussianMoments

/-!
# Error bounds from three preserved exponential moments

A signed weight with mass one and both unit exponential moments equal to one
preserves the value at zero of a constant plus the two exponentials. A pointwise
comparison with this function bounds the error by the absolute weighted error.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

public noncomputable section

namespace RiemannMasullo

private theorem threeMoment_integral_difference {μ : Measure ℝ} {f B E : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) (hB : Integrable B μ) (hE : Integrable E μ)
    (hbound : ∀ h, |f h - B h| ≤ E h) :
    |(∫ h, f h ∂μ) - ∫ h, B h ∂μ| ≤ ∫ h, E h ∂μ := by
  have hnorm : ∀ᵐ h ∂μ, ‖f h - B h‖ ≤ E h :=
    Filter.Eventually.of_forall fun h ↦ by simpa only [Real.norm_eq_abs] using hbound h
  have hd : Integrable (fun h ↦ f h - B h) μ := hE.mono' (hf.sub hB.aestronglyMeasurable) hnorm
  have hfi' : Integrable (fun h ↦ (f h - B h) + B h) μ := hd.add hB
  have hfi : Integrable f μ := by simpa only [sub_add_cancel] using hfi'
  rw [← integral_sub hfi hB]
  simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hE hnorm

/-- If a signed weight preserves the moments of `1`, `exp h` and `exp (-h)`, then
its integral against a sample differs from the unshifted comparison value by at most
the integral of the pointwise error against the absolute weight. -/
theorem threeMoment_integral_sub_le (μ : Measure ℝ) (w f E : ℝ → ℝ) (A b c : ℝ)
    (hf : AEStronglyMeasurable f μ) (hw : Integrable w μ)
    (hp : Integrable (fun h ↦ w h * Real.exp h) μ)
    (hn : Integrable (fun h ↦ w h * Real.exp (-h)) μ)
    (hE : Integrable (fun h ↦ |w h| * E h) μ)
    (h₀ : (∫ h, w h ∂μ) = 1) (hpos : (∫ h, w h * Real.exp h ∂μ) = 1)
    (hneg : (∫ h, w h * Real.exp (-h) ∂μ) = 1)
    (hbound : ∀ h, |f h - (A + b * Real.exp h + c * Real.exp (-h))| ≤ E h) :
    |(∫ h, w h * f h ∂μ) - (A + b + c)| ≤ ∫ h, |w h| * E h ∂μ := by
  let B (h : ℝ) := A * w h + b * (w h * Real.exp h) + c * (w h * Real.exp (-h))
  have hab : Integrable (fun h ↦ A * w h + b * (w h * Real.exp h)) μ :=
    (hw.const_mul A).add (hp.const_mul b)
  have hB : Integrable B μ := hab.add (hn.const_mul c)
  have hbase : (∫ h, B h ∂μ) = A + b + c := by
    dsimp only [B]
    rw [integral_add hab (hn.const_mul c), integral_add (hw.const_mul A) (hp.const_mul b)]
    simp only [integral_const_mul, h₀, hpos, hneg, mul_one]
  rw [← hbase]
  apply threeMoment_integral_difference (hw.aestronglyMeasurable.mul hf) hB hE
  intro h
  change |w h * f h - B h| ≤ _
  have heq : w h * f h - B h = w h * (f h - (A + b * Real.exp h + c * Real.exp (-h))) := by
    dsimp only [B]; ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound h) (abs_nonneg _)

/-- A pointwise error envelope for comparison with a constant and the two exponentials
bounds the compensated Gaussian expectation by its positive integrals at both variances.
This includes zero variance. -/
theorem compensatedGaussianIncrement_sub_le (v : ℝ≥0) (f E : ℝ → ℝ) (A b c : ℝ)
    (hf : Measurable f) (hE₁ : Integrable E (gaussianReal 0 v))
    (hE₂ : Integrable E (gaussianReal 0 (2 * v)))
    (hbound : ∀ h, |f h - (A + b * Real.exp h + c * Real.exp (-h))| ≤ E h) :
    |compensatedGaussianIncrement v f - (A + b + c)| ≤
      (1 + Real.exp (-(v : ℝ) / 2)) * (∫ h, E h ∂gaussianReal 0 v) +
        Real.exp (-(v : ℝ) / 2) * (∫ h, E h ∂gaussianReal 0 (2 * v)) := by
  let B (h : ℝ) := A + b * Real.exp h + c * Real.exp (-h)
  let d (u : ℝ≥0) := (∫ h, f h ∂gaussianReal 0 u) - ∫ h, B h ∂gaussianReal 0 u
  have herr (u : ℝ≥0) (hE : Integrable E (gaussianReal 0 u)) :
      |d u| ≤ ∫ h, E h ∂gaussianReal 0 u := by
    have hp : Integrable Real.exp (gaussianReal 0 u) := by
      simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := u) 1)
    have hn : Integrable (fun h ↦ Real.exp (-h)) (gaussianReal 0 u) := by
      simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := u) (-1))
    exact threeMoment_integral_difference hf.aestronglyMeasurable
      (((integrable_const A).add (hp.const_mul b)).add (hn.const_mul c)) hE hbound
  let r := Real.exp (-(v : ℝ) / 2)
  have hr : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : 0 ≤ 1 + r := by linarith
  have hbase : compensatedGaussianIncrement v B = A + b + c :=
    compensatedGaussianIncrement_const_add_exp v A b c
  have heq : compensatedGaussianIncrement v f - (A + b + c) = (1 + r) * d v - r * d (2 * v) := by
    rw [← hbase]
    dsimp only [compensatedGaussianIncrement, d, r]
    ring
  rw [heq]
  calc
    _ ≤ |(1 + r) * d v| + |r * d (2 * v)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le ((1 + r) * d v) (r * d (2 * v))
    _ = (1 + r) * |d v| + r * |d (2 * v)| := by rw [abs_mul, abs_mul, abs_of_nonneg hr₁, abs_of_nonneg hr]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (herr v hE₁) hr₁)
      (mul_le_mul_of_nonneg_left (herr (2 * v) hE₂) hr)

end RiemannMasullo
