module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Change of weight for a rational real-place dilation -/

public noncomputable section

namespace RiemannMasullo

/-- A symmetric strip contributes the exponential factor to the zero-offset
Sobolev density in log norm. -/
theorem intervalSobolevDensity_symmetric_eq_exp_abs_mul
    (β s t : ℝ) (hβ : 0 ≤ β) :
    intervalSobolevDensity (-β) β s t =
      Real.exp (2 * β * |t|) * intervalSobolevDensity 0 0 s t := by
  have hends : 2 * (-β) ≤ 2 * β := by linarith
  simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, max_eq_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hends ht))]
  · have harg : 2 * (-β) * t = 2 * β * (-t) := by ring
    rw [abs_of_nonpos ht, max_eq_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hends ht)), harg]

private theorem exp_sq_mul_symmetricDensity (β s t : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-(β * |t|)) ^ 2 * intervalSobolevDensity (-β) β s t =
      intervalSobolevDensity 0 0 s t := by
  rw [intervalSobolevDensity_symmetric_eq_exp_abs_mul β s t hβ, pow_two,
    ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
  rw [show -(β * |t|) + -(β * |t|) + 2 * β * |t| = 0 by ring, Real.exp_zero, one_mul]

/-- The density-ratio multiplier from the zero-offset space to the
symmetric strip in the same log norm coordinate. -/
def narrowIntervalWeightMultiplier (β s t : ℝ) : ℝ :=
  Real.sqrt (intervalSobolevDensity 0 0 s t / intervalSobolevDensity (-β) β s t)

theorem narrowIntervalWeightMultiplier_eq_exp
    (β s t : ℝ) (hβ : 0 ≤ β) :
    narrowIntervalWeightMultiplier β s t = Real.exp (-(β * |t|)) := by
  have hpos : 0 < intervalSobolevDensity (-β) β s t := by
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hratio : intervalSobolevDensity 0 0 s t / intervalSobolevDensity (-β) β s t =
      Real.exp (-(β * |t|)) ^ 2 :=
    (div_eq_iff hpos.ne').mpr (exp_sq_mul_symmetricDensity β s t hβ).symm
  rw [narrowIntervalWeightMultiplier, hratio, Real.sqrt_sq (Real.exp_nonneg _)]

/-- Squaring the multiplier exactly changes the strip density to the
zero-offset density. -/
theorem narrowIntervalWeightMultiplier_sq_mul_density
    (β s t : ℝ) (hβ : 0 ≤ β) :
    narrowIntervalWeightMultiplier β s t ^ 2 * intervalSobolevDensity (-β) β s t =
      intervalSobolevDensity 0 0 s t := by
  rw [narrowIntervalWeightMultiplier_eq_exp β s t hβ]
  exact exp_sq_mul_symmetricDensity β s t hβ

/-- If both the input and output radii are above one, the density ratio
contributes the dilation radius to the power of the strip half-width. -/
theorem narrowIntervalWeightMultiplier_dilation_ratio
    (s : ℝ) {β g x : ℝ} (hβ : 0 ≤ β) (hg : 1 < g) (hx : g < x) :
    narrowIntervalWeightMultiplier β s (Real.log (x / g)) /
        narrowIntervalWeightMultiplier β s (Real.log x) = g ^ β := by
  have hg₀ : 0 < g := zero_lt_one.trans hg
  have hx₀ : 0 < x := hg₀.trans hx
  have hxg : 1 < x / g := (lt_div_iff₀ hg₀).mpr (by simpa only [one_mul] using hx)
  simp only [narrowIntervalWeightMultiplier_eq_exp β s _ hβ,
    abs_of_nonneg (Real.log_nonneg hxg.le), abs_of_nonneg (Real.log_nonneg (hg.trans hx).le)]
  rw [← Real.exp_sub, Real.log_div hx₀.ne' hg₀.ne', Real.rpow_def_of_pos hg₀]
  congr 1
  ring

/-- Conjugating half-density dilation by the change of weight contributes
the factor g to the power β above the dilation radius. -/
theorem rationalNarrowWeightTransport_dilate
    (s : ℝ) {β g x : ℝ} (hβ : 0 ≤ β) (hg : 1 < g) (hx : g < x)
    (f : ℝ → ℂ) :
    (narrowIntervalWeightMultiplier β s (Real.log x) : ℂ)⁻¹ *
        (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((narrowIntervalWeightMultiplier β s (Real.log (x / g)) : ℂ) * f (x / g))) =
      ((g ^ β : ℝ) : ℂ) * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x / g)) := by
  have hratio :
      (narrowIntervalWeightMultiplier β s (Real.log (x / g)) : ℂ) /
          (narrowIntervalWeightMultiplier β s (Real.log x) : ℂ) = ((g ^ β : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div] using
      congrArg (fun r : ℝ ↦ (r : ℂ)) (narrowIntervalWeightMultiplier_dilation_ratio s hβ hg hx)
  have hratioMul :
      (narrowIntervalWeightMultiplier β s (Real.log (x / g)) : ℂ) *
          (narrowIntervalWeightMultiplier β s (Real.log x) : ℂ)⁻¹ = ((g ^ β : ℝ) : ℂ) :=
    (div_eq_mul_inv _ _).symm.trans hratio
  rw [← hratioMul]
  ring

/-- At positive strip width, the two dilation formulas differ wherever the
input value is nonzero above norm one. -/
theorem rationalNarrowWeightTransport_dilate_ne
    (s : ℝ) {β g x : ℝ} (hβ : 0 < β) (hg : 1 < g) (hx : g < x)
    (f : ℝ → ℂ) (hf : f (x / g) ≠ 0) :
    (narrowIntervalWeightMultiplier β s (Real.log x) : ℂ)⁻¹ *
        (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((narrowIntervalWeightMultiplier β s (Real.log (x / g)) : ℂ) * f (x / g))) ≠
      ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x / g) := by
  rw [rationalNarrowWeightTransport_dilate s hβ.le hg hx f]
  intro heq
  have hdil : ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x / g) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (zero_lt_one.trans hg) _).ne') hf
  have hone : ((g ^ β : ℝ) : ℂ) = 1 :=
    mul_right_cancel₀ hdil (by simpa only [one_mul] using heq)
  have hreal : g ^ β = 1 := by exact_mod_cast hone
  exact (Real.one_lt_rpow hg hβ).ne' hreal

end RiemannMasullo
