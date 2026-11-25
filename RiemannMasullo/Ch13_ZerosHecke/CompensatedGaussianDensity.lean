module

public import RiemannMasullo.Ch13_ZerosHecke.ThreeMomentCrossingComparison

/-! # Signed density of the compensated Gaussian increment

For positive variance the two Gaussian laws have densities with respect to
Lebesgue measure. Their signed density retains the cancellation between them
when bounding the error in a three-moment comparison.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

public noncomputable section

namespace RiemannMasullo

/-- The real signed density of the compensated increment at positive variance. -/
@[expose] def compensatedGaussianDensity (v : ℝ≥0) (h : ℝ) : ℝ :=
  (1 + Real.exp (-(v : ℝ) / 2)) * gaussianPDFReal 0 v h -
    Real.exp (-(v : ℝ) / 2) * gaussianPDFReal 0 (2 * v) h

private theorem integrable_gaussianPDFReal_mul {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 v)) :
    Integrable (fun h ↦ gaussianPDFReal 0 v h * f h) := by
  rw [gaussianReal_of_var_ne_zero _ hv] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top))).mp hf

private theorem compensatedGaussianDensity_product {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → ℝ)
    (h₁ : Integrable f (gaussianReal 0 v)) (h₂ : Integrable f (gaussianReal 0 (2*v))) :
    Integrable (fun h ↦ compensatedGaussianDensity v h * f h) ∧
      compensatedGaussianIncrement v f = ∫ h, compensatedGaussianDensity v h * f h := by
  let t := Real.exp (-(v : ℝ) / 2)
  have hv₂ : 2*v ≠ 0 := mul_ne_zero (by norm_num) hv
  have hpos := (integrable_gaussianPDFReal_mul hv h₁).const_mul (1+t)
  have hneg := (integrable_gaussianPDFReal_mul hv₂ h₂).const_mul t
  have hfun : (fun h ↦ compensatedGaussianDensity v h * f h) =
      (fun h ↦ (1 + t) * (gaussianPDFReal 0 v h * f h)) -
        (fun h ↦ t * (gaussianPDFReal 0 (2*v) h * f h)) := by
    ext h
    simp only [compensatedGaussianDensity, t, Pi.sub_apply, sub_mul, mul_assoc]
  rw [hfun]
  refine ⟨hpos.sub hneg, ?_⟩
  change _ = ∫ h, (1 + t) * (gaussianPDFReal 0 v h * f h) - t * (gaussianPDFReal 0 (2*v) h * f h)
  rw [integral_sub hpos hneg, integral_const_mul, integral_const_mul, compensatedGaussianIncrement,
    integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv₂]
  rfl

/-- At positive variance the signed Gaussian increment is integration against
a single real density for every observable integrable against both Gaussian laws. -/
theorem compensatedGaussianIncrement_eq_integral_density (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ)
    (h₁ : Integrable f (gaussianReal 0 v)) (h₂ : Integrable f (gaussianReal 0 (2*v))) :
    compensatedGaussianIncrement v f = ∫ h, compensatedGaussianDensity v h * f h :=
  (compensatedGaussianDensity_product hv f h₁ h₂).2

/-- A pointwise three-moment comparison at positive variance is controlled by its
error integrated against the absolute value of the combined signed density. -/
theorem compensatedGaussianIncrement_sub_le_density (v : ℝ≥0) (hv : v ≠ 0)
    (f E : ℝ → ℝ) (A b c : ℝ) (hf : Measurable f) (hE : Measurable E)
    (hE₁ : Integrable E (gaussianReal 0 v)) (hE₂ : Integrable E (gaussianReal 0 (2*v)))
    (hbound : ∀ h, |f h - (A + b * Real.exp h + c * Real.exp (-h))| ≤ E h) :
    |compensatedGaussianIncrement v f - (A+b+c)| ≤
      ∫ h, |compensatedGaussianDensity v h| * E h := by
  have hp (u : ℝ≥0) : Integrable Real.exp (gaussianReal 0 u) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := u) 1)
  have hn (u : ℝ≥0) : Integrable (fun h ↦ Real.exp (-h)) (gaussianReal 0 u) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := u) (-1))
  let g (h : ℝ) := A + b * Real.exp h + c * Real.exp (-h)
  have hfi (u : ℝ≥0) (hEu : Integrable E (gaussianReal 0 u)) :
      Integrable f (gaussianReal 0 u) := by
    have hg : Integrable g (gaussianReal 0 u) :=
      (((integrable_const A).add ((hp u).const_mul b)).add ((hn u).const_mul c))
    apply (hEu.add hg.abs).mono' hf.aestronglyMeasurable (ae_of_all _ fun h ↦ ?_)
    change ‖f h‖ ≤ E h + |g h|
    rw [Real.norm_eq_abs]
    calc _ = |(f h - g h) + g h| := by rw [sub_add_cancel]
         _ ≤ |f h - g h| + |g h| := abs_add_le _ _
         _ ≤ _ := add_le_add_left (hbound h) _
  have hweight : Integrable (fun h ↦ |compensatedGaussianDensity v h| * E h) := by
    have hd : Measurable (compensatedGaussianDensity v) := by unfold compensatedGaussianDensity; fun_prop
    have ha : Measurable (fun h ↦ |compensatedGaussianDensity v h|) := by
      simpa only [Real.norm_eq_abs] using hd.norm
    exact (compensatedGaussianDensity_product hv E hE₁ hE₂).1.congr'
      ((ha.mul hE).aestronglyMeasurable) (ae_of_all _ (fun h ↦ by
        simp only [Real.norm_eq_abs, abs_mul, abs_abs]))
  have hmass := compensatedGaussianDensity_product hv (fun _ ↦ 1) (integrable_const _) (integrable_const _)
  have hpos := compensatedGaussianDensity_product hv Real.exp (hp _) (hp _)
  have hneg := compensatedGaussianDensity_product hv (fun h ↦ Real.exp (-h)) (hn _) (hn _)
  rw [compensatedGaussianIncrement_eq_integral_density v hv f (hfi _ hE₁) (hfi _ hE₂)]
  apply threeMoment_integral_sub_le volume (compensatedGaussianDensity v) f E A b c
    hf.aestronglyMeasurable (by simpa only [mul_one] using hmass.1) hpos.1 hneg.1 hweight
  · simpa only [mul_one, compensatedGaussianIncrement_const] using hmass.2.symm
  · exact hpos.2.symm.trans (compensatedGaussianIncrement_exp v)
  · exact hneg.2.symm.trans (compensatedGaussianIncrement_exp_neg v)
  · exact hbound

end RiemannMasullo
