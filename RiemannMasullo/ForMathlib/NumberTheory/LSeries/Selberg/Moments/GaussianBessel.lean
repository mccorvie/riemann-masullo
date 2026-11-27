module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

public section

open MeasureTheory
open scoped ComplexConjugate

namespace RiemannMasullo.Selberg

private noncomputable def gaussianKernel (b x : ℝ) : ℝ :=
  Real.sqrt (Real.pi / b) * Real.exp (-(4 * b)⁻¹ * x ^ 2)

private lemma integral_gaussian_phase {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (∫ t : ℝ, (Real.exp (-b * t ^ 2) : ℂ) * osc (t * x)) = gaussianKernel b x := by
  calc
    _ = ∫ t : ℝ, Complex.exp (Complex.I * x * t) * Complex.exp (-(b : ℂ) * t ^ 2) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [mul_comm, osc, Complex.ofReal_exp]
      push_cast
      ring_nf
    _ = _ := by
      rw [fourierIntegral_gaussian (b := (b : ℂ)) hb, gaussianKernel,
        Complex.ofReal_mul, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity),
        Complex.ofReal_exp]
      push_cast
      congr 2
      ring

private lemma gaussianKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x, gaussianKernel b x = 2 * Real.pi := by
  simp only [gaussianKernel, integral_const_mul, integral_gaussian]
  have h : Real.pi / b * (Real.pi / (4 * b)⁻¹) = (2 * Real.pi) ^ 2 := by
    field_simp
    ring
  rw [← Real.sqrt_mul (by positivity), h, Real.sqrt_sq (by positivity)]

private lemma osc_norm (x : ℝ) : ‖osc x‖ = 1 := by
  rw [osc, mul_comm, Complex.norm_exp_ofReal_mul_I]

private lemma osc_sub (t y z : ℝ) :
    osc (t * (z - y)) = conj (osc (t * y)) * osc (t * z) := by
  simp only [osc, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_sub]
  congr 1
  ring

private lemma ft_sq_as_integral (f : ℝ → ℂ) (t : ℝ) :
    (‖ft f t‖ ^ 2 : ℝ) = (∫ p : ℝ × ℝ,
      (conj (f p.1) * f p.2) * osc (t * (p.2 - p.1)) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm]
  unfold ft
  rw [← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with p
  rw [osc_sub, map_mul]
  ring

/-- Fubini exchanges the frequency with the pair of spatial variables. The absolute
integrand factors as a Gaussian times the product of two copies of the norm of `f`. -/
private lemma gaussian_energy_eq (f : ℝ → ℂ) (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ((∫ t : ℝ, Real.exp (-b * t ^ 2) * ‖ft f t‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, (gaussianKernel b (p.2 - p.1) : ℂ) * (conj (f p.1) * f p.2) := by
  let g (t : ℝ) (p : ℝ × ℝ) : ℂ :=
    ((Real.exp (-b * t ^ 2) : ℂ) * osc (t * (p.2 - p.1))) * (conj (f p.1) * f p.2)
  have hg : Integrable (Function.uncurry g) := by
    apply ((integrable_exp_neg_mul_sq hb).mul_prod (hf.norm.mul_prod hf.norm)).mono'
    · have hcont : Continuous (fun q : ℝ × (ℝ × ℝ) ↦
          (Real.exp (-b * q.1 ^ 2) : ℂ) * osc (q.1 * (q.2.2 - q.2.1))) := by
        unfold osc
        fun_prop
      have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ conj (f p.1) * f p.2) := by
        exact (Complex.continuous_conj.comp_aestronglyMeasurable
          hf.aestronglyMeasurable).comp_fst.mul hf.aestronglyMeasurable.comp_snd
      exact hcont.aestronglyMeasurable.mul hpair.comp_snd
    · filter_upwards with q
      simp only [Function.uncurry, g, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), osc_norm, mul_one, Complex.norm_conj, le_refl]
  calc
    _ = ∫ t : ℝ, ∫ p : ℝ × ℝ, g t p := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with t
      rw [Complex.ofReal_mul, ft_sq_as_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      dsimp [g]
      ring
    _ = ∫ p : ℝ × ℝ, ∫ t : ℝ, g t p := integral_integral_swap hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [g, integral_mul_const, integral_gaussian_phase hb]

private lemma gaussian_pair_bound (f : ℝ → ℂ) (hf₂ : Integrable (fun y ↦ ‖f y‖ ^ 2))
    {b : ℝ} (hb : 0 < b) :
    ‖∫ p : ℝ × ℝ, (gaussianKernel b (p.2 - p.1) : ℂ) * (conj (f p.1) * f p.2)‖ ≤
      2 * Real.pi * ∫ y : ℝ, ‖f y‖ ^ 2 := by
  let row (p : ℝ × ℝ) := ‖f p.1‖ ^ 2 * gaussianKernel b (p.2 - p.1)
  have hK : Integrable (gaussianKernel b) :=
    (integrable_exp_neg_mul_sq (b := (4 * b)⁻¹) (by positivity)).const_mul _
  have hrow : Integrable row :=
    (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable (hf₂.mul_prod hK)
  have hswap : Integrable (fun p : ℝ × ℝ ↦ row p.swap) := hrow.swap
  have hmass : ∫ p, row p = 2 * Real.pi * ∫ y : ℝ, ‖f y‖ ^ 2 := by
    rw [Measure.volume_eq_prod, integral_prod _ hrow]
    simp only [row, integral_const_mul, integral_sub_right_eq_self,
      gaussianKernel_integral hb, integral_mul_const, mul_comm]
  calc
    _ ≤ ∫ p : ℝ × ℝ, (row p + row p.swap) / 2 := by
      apply norm_integral_le_of_norm_le ((hrow.add hswap).div_const 2)
      filter_upwards with p
      have heven : gaussianKernel b (p.1 - p.2) = gaussianKernel b (p.2 - p.1) := by
        simp only [gaussianKernel, sub_sq_comm p.1 p.2]
      have hnonneg : 0 ≤ gaussianKernel b (p.2 - p.1) := by
        unfold gaussianKernel
        positivity
      simp only [Pi.add_apply, row, Prod.fst_swap, Prod.snd_swap, heven, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      nlinarith [mul_nonneg hnonneg (sq_nonneg (‖f p.1‖ - ‖f p.2‖))]
    _ = _ := by
      have hsymm : (∫ p : ℝ × ℝ, row p.swap) = ∫ p, row p := integral_prod_swap row
      rw [integral_div, integral_add hrow hswap, hsymm, hmass]
      ring

/-- Card 37. For an integrable complex function with integrable squared norm, the Fourier energy
with Gaussian weight exp(−(t/U)²) is at most 2π times its squared norm integral for U > 0.
Elementary form of Plancherel used in Titchmarsh (10.10.1), p. 269. -/
theorem gaussian_bessel (f : ℝ → ℂ) (hf : Integrable f) (hf₂ : Integrable (fun y ↦ ‖f y‖^2))
    (U : ℝ) (hU : 0 < U) :
    (∫ t : ℝ, Real.exp (-(t/U)^2)*‖ft f t‖^2) ≤ 2*Real.pi * ∫ y : ℝ, ‖f y‖^2 := by
  let b := (U ^ 2)⁻¹
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hw (t : ℝ) : -(t / U) ^ 2 = -b * t ^ 2 := by
    dsimp [b]
    ring
  simp_rw [hw]
  calc
    _ ≤ ‖((∫ t : ℝ, Real.exp (-b * t ^ 2) * ‖ft f t‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ _ := by
      rw [gaussian_energy_eq f hf hb]
      exact gaussian_pair_bound f hf₂ hb

end RiemannMasullo.Selberg
