module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! The physical log-line weight and its curvature for the width-zero value cardinal. -/

@[expose] public noncomputable section

open Real MeasureTheory

namespace RiemannMasullo.CardinalMoment

/-- Polynomial part of the zero-width density in the physical log coordinate. -/
def symbol (θ x : ℝ) : ℝ := (1+x^2)^θ

def symbolSlope (θ x : ℝ) : ℝ := 2*θ*x*symbol (θ-1) x

def symbolCurvature (θ x : ℝ) : ℝ :=
  2*θ*(1+(2*θ-1)*x^2)*symbol (θ-2) x

theorem symbol_pos (θ x : ℝ) : 0 < symbol θ x := Real.rpow_pos_of_pos (by positivity) _

theorem symbol_step (θ x : ℝ) : symbol (θ-1) x*(1+x^2) = symbol θ x := by
  dsimp [symbol]
  rw [← rpow_add_one (by positivity)]
  ring_nf

theorem hasDerivAt_symbol (θ x : ℝ) : HasDerivAt (symbol θ) (symbolSlope θ x) x := by
  have hd : HasDerivAt (fun y : ℝ ↦ 1+y^2) (2*x) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_add 1
  have hh := hd.rpow_const (p := θ) (Or.inl (by positivity : 1+x^2 ≠ 0))
  exact hh.congr_deriv (by dsimp [symbolSlope,symbol]; ring)

theorem hasDerivAt_symbolSlope (θ x : ℝ) :
    HasDerivAt (symbolSlope θ) (symbolCurvature θ x) x := by
  have hd := (((hasDerivAt_id x).const_mul (2*θ)).mul (hasDerivAt_symbol (θ-1) x))
  convert hd using 1
  · rfl
  · dsimp [symbolSlope,symbolCurvature]
    rw [← symbol_step (θ-1) x]
    have h : θ-1-1 = θ-2 := by ring
    rw [h]
    ring

theorem symbolSlope_abs_le (θ x : ℝ) (hθ : 0 ≤ θ) :
    |symbolSlope θ x| ≤ (2*θ)*symbol θ x := by
  rw [symbolSlope,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*θ),
      abs_of_pos (symbol_pos _ _),← symbol_step θ x]
  have hx : |x| ≤ 1+x^2 := by
    nlinarith [sq_nonneg (|x|-1),sq_abs x]
  nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (symbol_pos (θ-1) x).le)
    (show 0 ≤ 2*θ by positivity)]

theorem symbol_decr_exponent (θ x : ℝ) : symbol (θ-1) x ≤ symbol θ x := by
  rw [← symbol_step θ x]
  nlinarith only [mul_nonneg (symbol_pos (θ-1) x).le (sq_nonneg x)]

/-- The exact sharp bounds are uniform over the entire real log line. -/
theorem half_symbolCurvature_bounds (θ x : ℝ) (hθ : 1 ≤ θ) :
    θ*symbol (θ-1) x ≤ symbolCurvature θ x/2 ∧
    symbolCurvature θ x/2 ≤ θ*(2*θ-1)*symbol (θ-1) x := by
  have h := symbol_step (θ-1) x
  rw [show θ-1-1=θ-2 by ring] at h
  rw [symbolCurvature,← h]
  constructor
  · nlinarith only [mul_nonneg (mul_nonneg (show 0 ≤ θ by linarith) (sub_nonneg.mpr hθ))
      (mul_nonneg (sq_nonneg x) (symbol_pos (θ-2) x).le)]
  · nlinarith only [mul_nonneg (mul_nonneg (show 0 ≤ θ by linarith) (sub_nonneg.mpr hθ))
      (symbol_pos (θ-2) x).le]

theorem symbolCurvature_abs_le (θ x : ℝ) (hθ : 1 ≤ θ) :
    |symbolCurvature θ x| ≤ (2*θ*(2*θ-1))*symbol θ x := by
  obtain ⟨h₀,h₁⟩ := half_symbolCurvature_bounds θ x hθ
  have hθ₀ : 0 ≤ θ := by linarith
  rw [abs_of_nonneg (by nlinarith [mul_nonneg hθ₀ (symbol_pos (θ-1) x).le] : 0 ≤ symbolCurvature θ x)]
  nlinarith only [h₁,mul_le_mul_of_nonneg_left (symbol_decr_exponent θ x)
    (show 0 ≤ θ*(2*θ-1) by apply mul_nonneg hθ₀; linarith)]

theorem integrable_symbol_inv (θ : ℝ) (hθ : 1 ≤ θ) :
    Integrable (fun x : ℝ ↦ (symbol θ x)⁻¹) := by
  have hc : Continuous (fun x : ℝ ↦ (symbol θ x)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_symbol θ x).continuousAt
    · exact fun x ↦ (symbol_pos θ x).ne'
  apply integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (symbol_pos θ x))]
  apply inv_anti₀ (by positivity)
  exact le_trans (show 1+x^2 = (1+x^2)^(1:ℝ) by rw [rpow_one]).le
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) hθ)

end RiemannMasullo.CardinalMoment
