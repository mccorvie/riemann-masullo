module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The inverse Laplace kernel of the shifted strip resolvent -/

open MeasureTheory Complex Set

@[expose] public noncomputable section
namespace RiemannMasullo

/-- Exponentially decaying Green kernel, modulated at frequency `b`. -/
def resolventLaplaceKernel (L b x : ℝ) : ℂ :=
  ((Real.exp (-L * |x|) / (2 * L) : ℝ) : ℂ) * cexp (-I * b * x)

/-- Both half-line integrals converge absolutely, and their sum is the strip resolvent. -/
theorem resolventLaplaceKernel_halves_and_transform (L b : ℝ) {z : ℂ} (hz : |z.re| < L) :
    IntegrableOn (fun x : ℝ ↦ resolventLaplaceKernel L b x * cexp (z * x)) (Iic 0) ∧
    IntegrableOn (fun x : ℝ ↦ resolventLaplaceKernel L b x * cexp (z * x)) (Ioi 0) ∧
    bilateralLaplace (resolventLaplaceKernel L b) z = 1 / ((L : ℂ)^2 - (z - b * I)^2) := by
  let w : ℂ := z - b * I
  let A : ℂ := w + L
  let B : ℂ := w - L
  let c : ℂ := (2 * (L : ℂ))⁻¹
  let f (x : ℝ) := resolventLaplaceKernel L b x * cexp (z * x)
  have hw : w.re = z.re := by simp [w, Complex.mul_re]
  have hA : 0 < A.re := by
    simp only [A, Complex.add_re, hw, Complex.ofReal_re]; linarith [(abs_lt.mp hz).1]
  have hB : B.re < 0 := by
    simp only [B, Complex.sub_re, hw, Complex.ofReal_re]; linarith [(abs_lt.mp hz).2]
  have hf (x : ℝ) : f x = c * cexp (↑(-L * |x| : ℝ) + (-I * b * x) + z * x) := by
    simp only [f, resolventLaplaceKernel, c, Complex.ofReal_mul, Complex.exp_add]
    push_cast
    ring
  have hleft (x : ℝ) (hx : x ∈ Iic 0) : f x = c * cexp (A * x) := by
    rw [hf, abs_of_nonpos hx]
    congr 2
    push_cast
    dsimp [A, w]
    ring
  have hright (x : ℝ) (hx : x ∈ Ioi 0) : f x = c * cexp (B * x) := by
    rw [hf, abs_of_nonneg hx.le]
    congr 2
    push_cast
    dsimp [B, w]
    ring
  have hl₀ : IntegrableOn (fun x : ℝ ↦ c * cexp (A * x)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hA 0).const_mul c
  have hr₀ : IntegrableOn (fun x : ℝ ↦ c * cexp (B * x)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hB 0).const_mul c
  have hl := hl₀.congr_fun (fun x hx ↦ (hleft x hx).symm) measurableSet_Iic
  have hr := hr₀.congr_fun (fun x hx ↦ (hright x hx).symm) measurableSet_Ioi
  refine ⟨hl, hr, ?_⟩
  change ∫ x, f x = 1 / ((L : ℂ)^2 - w^2)
  rw [← intervalIntegral.integral_Iic_add_Ioi hl hr, setIntegral_congr_fun measurableSet_Iic hleft,
    setIntegral_congr_fun measurableSet_Ioi hright, integral_const_mul, integral_const_mul,
    integral_exp_mul_complex_Iic hA, integral_exp_mul_complex_Ioi hB]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have ha : A ≠ 0 := fun h ↦ by simp [h] at hA
  have hb : B ≠ 0 := fun h ↦ by simp [h] at hB
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (lt_of_le_of_lt (abs_nonneg _) hz).ne'
  have hfac : (L : ℂ)^2 - w^2 = -(A * B) := by dsimp [A, B]; ring
  rw [hfac]
  dsimp only [c]
  field_simp [ha, hb, hL]
  dsimp [A, B]
  ring

/-- The bilateral transform has no normalization constant in the numerator. -/
theorem bilateralLaplace_resolventLaplaceKernel (L b : ℝ) {z : ℂ} (hz : |z.re| < L) :
    bilateralLaplace (resolventLaplaceKernel L b) z = 1 / ((L : ℂ)^2 - (z - b * I)^2) :=
  (resolventLaplaceKernel_halves_and_transform L b hz).2.2

end RiemannMasullo
