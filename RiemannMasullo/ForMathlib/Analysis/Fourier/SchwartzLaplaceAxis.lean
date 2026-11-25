module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Imaginary-axis bilateral Laplace transforms in Schwartz space -/

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The imaginary-axis bilateral Laplace transform of a compact smooth test is
Schwartz in angular frequency, in the normalization without the factor `2π`. -/
theorem exists_schwartz_eq_bilateralLaplace_axis {H : ℝ → ℂ}
    (hc : HasCompactSupport H) (hs : ContDiff ℝ ∞ H) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ t : ℝ, g t = bilateralLaplace H ((t : ℂ) * I) := by
  let u := hc.toSchwartzMap hs
  have hπ : 0 < 2 * Real.pi := by positivity
  let a := -(2 * Real.pi)⁻¹
  have ha : a ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hπ.ne')
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (𝓕 u), ?_⟩
  intro t
  change (𝓕 u) (t * a) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, mul_comm _ (u x)]
  change H x * Complex.exp ((↑(-2 * Real.pi * x * (t * a)) : ℂ) * I) =
    H x * Complex.exp ((t : ℂ) * I * x)
  have hf : -2 * Real.pi * x * (t * a) = t*x := by
    dsimp [a]
    field_simp
  rw [hf]
  push_cast
  ring_nf

/-- The real part of the angular-frequency transform is a real Schwartz test. -/
theorem exists_realSchwartz_eq_bilateralLaplace_axis_re {H : ℝ → ℂ}
    (hc : HasCompactSupport H) (hs : ContDiff ℝ ∞ H) :
    ∃ g : 𝓢(ℝ, ℝ), ∀ t : ℝ, g t = (bilateralLaplace H ((t : ℂ) * I)).re := by
  obtain ⟨G, hG⟩ := exists_schwartz_eq_bilateralLaplace_axis hc hs
  exact ⟨SchwartzMap.postcompCLM Complex.reCLM G, fun t ↦ congrArg Complex.re (hG t)⟩

end RiemannMasullo
