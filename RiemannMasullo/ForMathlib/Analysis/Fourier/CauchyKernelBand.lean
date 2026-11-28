module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Fourier.FourierTransform

/-! # The Cauchy kernel split by frequency

For `p` in the upper half-plane and real `x`, the Cauchy kernel `(x - p)⁻¹` is a superposition of
the oscillations `exp (-i (x - p) τ)` over `τ > 0`. Cutting the frequencies at `T` splits it
into a band-limited part `(1 - exp (-i T (x - p))) / (x - p)` and a remainder
`exp (-i T (x - p)) / (x - p)` carried by the frequencies above `T`. This is the formula for
the Paley–Wiener projection of a simple pole.
-/

open MeasureTheory Complex Set
open scoped FourierTransform Real

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The exponent `-i (x - p)` has negative real part when `p` is in the upper half-plane. -/
theorem re_neg_I_mul_sub_neg {p : ℂ} (hp : 0 < p.im) (x : ℝ) : (-I * ((x : ℂ) - p)).re < 0 := by
  simp
  exact hp

/-- The band-limited part of the Cauchy kernel: frequencies between `0` and `T`. -/
theorem integral_cexp_cauchyKernel_band {p : ℂ} (hp : 0 < p.im) (x T : ℝ) :
    ∫ τ in (0 : ℝ)..T, cexp (-I * ((x : ℂ) - p) * τ) =
      I * (cexp (-I * ((x : ℂ) - p) * T) - 1) / ((x : ℂ) - p) := by
  have hc : -I * ((x : ℂ) - p) ≠ 0 := fun h ↦ by
    have := re_neg_I_mul_sub_neg hp x
    rw [h] at this
    simp at this
  have hxp : (x : ℂ) - p ≠ 0 := fun h ↦ hc (by rw [h, mul_zero])
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The remainder of the Cauchy kernel: frequencies above `T`. -/
theorem integral_cexp_cauchyKernel_tail {p : ℂ} (hp : 0 < p.im) (x T : ℝ) :
    ∫ τ in Ioi T, cexp (-I * ((x : ℂ) - p) * τ) =
      -I * cexp (-I * ((x : ℂ) - p) * T) / ((x : ℂ) - p) := by
  have hre := re_neg_I_mul_sub_neg hp x
  have hc : -I * ((x : ℂ) - p) ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  have hxp : (x : ℂ) - p ≠ 0 := fun h ↦ hc (by rw [h, mul_zero])
  rw [integral_exp_mul_complex_Ioi hre T]
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- The Cauchy kernel is the sum of its band-limited part and its remainder. -/
theorem integral_cexp_cauchyKernel_band_add_tail {p : ℂ} (hp : 0 < p.im) (x T : ℝ) :
    (∫ τ in (0 : ℝ)..T, cexp (-I * ((x : ℂ) - p) * τ)) +
        ∫ τ in Ioi T, cexp (-I * ((x : ℂ) - p) * τ) = -I / ((x : ℂ) - p) := by
  rw [integral_cexp_cauchyKernel_band hp, integral_cexp_cauchyKernel_tail hp]
  ring

/-- The one-sided exponential `τ ↦ exp (2πi p τ)` on `τ > 0`, for `p` in the upper half-plane,
is integrable. -/
theorem integrable_indicator_Ioi_cexp {p : ℂ} (hp : 0 < p.im) :
    Integrable (indicator (Ioi (0 : ℝ)) fun τ : ℝ ↦ cexp (2 * π * I * p * τ)) := by
  have hre : (2 * π * I * p).re < 0 := by
    have : (2 * π * I * p).re = -(2 * π * p.im) := by simp
    rw [this]
    have := Real.pi_pos
    nlinarith
  exact (integrableOn_exp_mul_complex_Ioi hre 0).integrable_indicator measurableSet_Ioi

/-- The Cauchy kernel as a Fourier transform: the transform of the one-sided exponential
`exp (2πi p τ)`, `τ > 0`, is `(2πi (x - p))⁻¹`. -/
theorem fourier_indicator_Ioi_cexp {p : ℂ} (hp : 0 < p.im) (x : ℝ) :
    𝓕 (indicator (Ioi (0 : ℝ)) fun τ : ℝ ↦ cexp (2 * π * I * p * τ)) x =
      (2 * π * I * ((x : ℂ) - p))⁻¹ := by
  have hre : (-(2 * π * I * ((x : ℂ) - p))).re < 0 := by
    have : (-(2 * π * I * ((x : ℂ) - p))).re = -(2 * π * p.im) := by simp
    rw [this]
    have := Real.pi_pos
    nlinarith
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h (τ : ℝ) : cexp (((-2 * π * τ * x : ℝ) : ℂ) * I) •
      indicator (Ioi (0 : ℝ)) (fun τ : ℝ ↦ cexp (2 * π * I * p * τ)) τ =
      indicator (Ioi (0 : ℝ)) (fun τ : ℝ ↦ cexp (-(2 * π * I * ((x : ℂ) - p)) * τ)) τ := by
    by_cases hτ : τ ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hτ, indicator_of_mem hτ, smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem hτ, indicator_of_notMem hτ, smul_zero]
  simp_rw [h]
  rw [integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hre 0]
  simp

/-- The band-limited part of the Cauchy kernel as a Fourier transform: the transform of the
one-sided exponential cut at `τ ≤ T`. -/
theorem fourier_indicator_Ioc_cexp {p : ℂ} (hp : 0 < p.im) (x : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    𝓕 (indicator (Ioc (0 : ℝ) T) fun τ : ℝ ↦ cexp (2 * π * I * p * τ)) x =
      (1 - cexp (-(2 * π * I * ((x : ℂ) - p)) * T)) / (2 * π * I * ((x : ℂ) - p)) := by
  have hre : (-(2 * π * I * ((x : ℂ) - p))).re < 0 := by
    have : (-(2 * π * I * ((x : ℂ) - p))).re = -(2 * π * p.im) := by simp
    rw [this]
    have := Real.pi_pos
    nlinarith
  have hc : -(2 * π * I * ((x : ℂ) - p)) ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h (τ : ℝ) : cexp (((-2 * π * τ * x : ℝ) : ℂ) * I) •
      indicator (Ioc (0 : ℝ) T) (fun τ : ℝ ↦ cexp (2 * π * I * p * τ)) τ =
      indicator (Ioc (0 : ℝ) T) (fun τ : ℝ ↦ cexp (-(2 * π * I * ((x : ℂ) - p)) * τ)) τ := by
    by_cases hτ : τ ∈ Ioc (0 : ℝ) T
    · rw [indicator_of_mem hτ, indicator_of_mem hτ, smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem hτ, indicator_of_notMem hτ, smul_zero]
  simp_rw [h]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hT,
    integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [← neg_div_neg_eq]
  congr 1 <;> ring

/-- Convolution of a function supported in `(-∞, A]` with the one-sided exponential: beyond the
support, it is the exponential times one number, the value at `p` of the transform of `u`.
On the transform side this is `P (q / (x - p)) = (q - q p) / (x - p) + q p * P (1 / (x - p))`:
the part of `q / (x - p)` at frequencies above the band of `q` is `q p` times the Cauchy
kernel. -/
theorem integral_mul_indicator_Ioi_cexp_sub_of_lt {u : ℝ → ℂ} {A : ℝ}
    (hA : ∀ σ, A < σ → u σ = 0) (p : ℂ) {τ : ℝ} (hτ : A < τ) :
    ∫ σ, u σ * indicator (Ioi (0 : ℝ)) (fun t : ℝ ↦ cexp (2 * π * I * p * t)) (τ - σ) =
      cexp (2 * π * I * p * τ) * ∫ σ, u σ * cexp (-(2 * π * I * p * σ)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun σ ↦ ?_)
  by_cases hσ : A < σ
  · simp [hA σ hσ]
  · have hpos : τ - σ ∈ Ioi (0 : ℝ) := by
      simp only [mem_Ioi]
      linarith [not_lt.mp hσ]
    simp only [indicator_of_mem hpos]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Convolution of a function supported in `[A, ∞)` with the one-sided exponential vanishes
below the support. -/
theorem integral_mul_indicator_Ioi_cexp_sub_of_gt {u : ℝ → ℂ} {A : ℝ}
    (hA : ∀ σ, σ < A → u σ = 0) (p : ℂ) {τ : ℝ} (hτ : τ ≤ A) :
    ∫ σ, u σ * indicator (Ioi (0 : ℝ)) (fun t : ℝ ↦ cexp (2 * π * I * p * t)) (τ - σ) = 0 := by
  rw [← integral_zero ℝ ℂ]
  refine integral_congr_ae (.of_forall fun σ ↦ ?_)
  by_cases hσ : σ < A
  · simp [hA σ hσ]
  · have hneg : τ - σ ∉ Ioi (0 : ℝ) := by
      simp only [mem_Ioi, not_lt]
      linarith [not_lt.mp hσ]
    simp [indicator_of_notMem hneg]

end RiemannMasullo
