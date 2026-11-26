module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-! # One-sided Parseval identities for a real boundary trace -/

@[expose] public noncomputable section
open MeasureTheory AddCircle Complex Filter
open scoped ComplexConjugate Topology

namespace RiemannMasullo.BoundaryHardy
variable {T : ℝ} [Fact (0 < T)]

/-- The Fourier coefficient of a real function for probability Haar measure. -/
def mode (u : AddCircle T → ℝ) (k : ℤ) : ℂ := fourierCoeff (fun x ↦ (u x : ℂ)) k

/-- The part invariant under reflection in zero. -/
def evenPart (u : AddCircle T → ℝ) (x : AddCircle T) : ℝ := (u x + u (-x)) / 2

theorem fourierCoeff_conj (f : AddCircle T → ℂ) (k : ℤ) :
    fourierCoeff (fun x ↦ conj (f x)) k = conj (fourierCoeff f (-k)) := by
  simp only [fourierCoeff, neg_neg, smul_eq_mul, ← integral_conj, map_mul, ← fourier_neg]

theorem mode_neg (u : AddCircle T → ℝ) (k : ℤ) : mode u (-k) = conj (mode u k) := by
  simpa [mode] using fourierCoeff_conj (fun x ↦ (u x : ℂ)) (-k)

theorem fourierCoeff_reflect (f : AddCircle T → ℂ) (k : ℤ) :
    fourierCoeff (fun x ↦ f (-x)) k = fourierCoeff f (-k) := by
  rw [fourierCoeff, fourierCoeff, neg_neg, ← integral_neg_eq_self
    (fun x : AddCircle T ↦ fourier k x • f x) haarAddCircle]
  simp [fourier_apply, smul_neg, neg_smul]

theorem memLp_evenPart {u : AddCircle T → ℝ} (h : MemLp u 2 haarAddCircle) :
    MemLp (evenPart u) 2 haarAddCircle := by
  have hh := h.comp_measurePreserving (Measure.measurePreserving_neg haarAddCircle)
  change MemLp (fun x ↦ (u x + u (-x)) / 2) 2 haarAddCircle
  simpa [Function.comp_def, div_eq_inv_mul] using (h.add hh).const_mul (2:ℝ)⁻¹

theorem mode_evenPart {u : AddCircle T → ℝ} (h : Integrable u haarAddCircle) (k : ℤ) :
    mode (evenPart u) k = ((mode u k).re : ℂ) := by
  have hc : Integrable (fun x ↦ (u x : ℂ)) haarAddCircle := h.ofReal
  have hr := hc.comp_neg
  have heq : (fun x ↦ (evenPart u x : ℂ)) = fun x ↦ (2 : ℂ)⁻¹ *
      ((fun x ↦ (u x : ℂ)) + (fun x ↦ (u (-x) : ℂ))) x := by
    funext x; simp [evenPart, div_eq_inv_mul]
  rw [mode, heq, fourierCoeff.const_mul, fourierCoeff.add hc hr]
  simp only [Pi.add_apply]
  rw [fourierCoeff_reflect (fun x ↦ (u x : ℂ))]
  change (2:ℂ)⁻¹ * (mode u k + mode u (-k)) = _
  rw [mode_neg, Complex.add_conj]
  push_cast
  ring

theorem mode_zero (u : AddCircle T → ℝ) :
    mode u 0 = ((∫ x, u x ∂haarAddCircle : ℝ) : ℂ) := by
  simpa [mode, fourierCoeff] using (integral_complex_ofReal (μ := haarAddCircle) (f := u))

/-- Parseval over the positive frequencies, with the constant mode removed. -/
theorem hasSum_double_modes {u : AddCircle T → ℝ} (hu : MemLp u 2 haarAddCircle) :
    HasSum (fun n : ℕ ↦ ‖2 * mode u (n+1)‖ ^ 2) (2 * ProbabilityTheory.variance u haarAddCircle) := by
  have hc : MemLp (fun x ↦ (u x : ℂ)) 2 haarAddCircle := hu.ofReal
  have hP := hasSum_sq_fourierCoeff hc.toLp
  rw [fourierCoeff_congr_ae hc.coeFn_toLp] at hP
  have hI : (∫ x, ‖(hc.toLp (f := fun t ↦ (u t : ℂ)) : AddCircle T → ℂ) x‖ ^ 2 ∂haarAddCircle) = ∫ x, u x ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hc.coeFn_toLp] with x hx
    simp [hx, sq_abs]
  rw [hI] at hP
  have hP' : HasSum (fun k : ℤ ↦ ‖mode u k‖^2) (∫ x, u x ^ 2 ∂haarAddCircle) := hP
  have h := (hasSum_nat_add_iff' 1).mpr hP'.nat_add_neg
  have hh := h.mul_left 2
  convert hh using 1
  · funext n
    rw [mode_neg u ((n+1:ℕ):ℤ)]
    simp [mul_pow]
    ring
  · simp [mode_zero, ProbabilityTheory.variance_eq_sub hu, sq_abs]

/-- Parseval over positive frequencies of the reflection-even part. -/
theorem hasSum_double_modes_re {u : AddCircle T → ℝ} (hu : MemLp u 2 haarAddCircle) :
    HasSum (fun n : ℕ ↦ (2 * (mode u (n+1)).re)^2)
      (2 * ProbabilityTheory.variance (evenPart u) haarAddCircle) := by
  refine (hasSum_double_modes (memLp_evenPart hu)).congr_fun (fun n ↦ ?_)
  simp [mode_evenPart (hu.integrable (by norm_num)), mul_pow, sq_abs]

end RiemannMasullo.BoundaryHardy
