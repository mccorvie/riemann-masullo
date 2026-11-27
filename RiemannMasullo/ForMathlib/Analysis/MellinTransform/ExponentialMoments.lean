module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Holomorphic logarithmic moments

An integrable exponential bound in a real logarithmic coordinate gives a holomorphic Mellin
transform. Differentiation in the open strip inserts a power of that coordinate.
-/

@[expose] public noncomputable section
open MeasureTheory Complex Filter Metric Set
open scoped Topology

namespace RiemannMasullo.MellinMoment

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {l : X → ℝ} {f : X → ℂ}

/-- The k-th logarithmic moment of a complex density with logarithmic coordinate l. -/
def moment (μ : Measure X) (l : X → ℝ) (f : X → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  ∫ x, f x * Complex.exp (w * (l x : ℂ)) * (l x : ℂ) ^ k ∂μ

private theorem power_exp_bound (n : ℕ) {A β : ℝ} (hβ : β < A) (x t : ℝ) (ht : |t| ≤ β) :
    |x| ^ n * Real.exp (t * x) ≤ ((n.factorial : ℝ) / (A - β) ^ n) * Real.exp (A * |x|) := by
  let d := A - β
  have hd : 0 < d := sub_pos.mpr hβ
  have hx : t * x ≤ β * |x| := ((le_abs_self _).trans (abs_mul t x).le).trans
    (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
  have hpow : |x| ^ n ≤ ((n.factorial : ℝ) / d ^ n) * Real.exp (d * |x|) := by
    have H := Real.pow_div_factorial_le_exp _ (mul_nonneg hd.le (abs_nonneg x)) n
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial), mul_pow] at H
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hd n)]
    nlinarith only [H]
  calc
    _ ≤ (((n.factorial : ℝ) / d ^ n) * Real.exp (d * |x|)) * Real.exp (β * |x|) :=
      mul_le_mul hpow (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [d]
      ring

private theorem integrand_bound (k : ℕ) {β A : ℝ} (hβ : β < A) (w : ℂ) (hw : |w.re| ≤ β)
    (x : X) :
    ‖f x * Complex.exp (w * (l x : ℂ)) * (l x : ℂ) ^ k‖ ≤
      ((k.factorial : ℝ) / (A - β) ^ k) * (‖f x‖ * Real.exp (A * |l x|)) := by
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h := mul_le_mul_of_nonneg_left (power_exp_bound k hβ (l x) w.re hw) (norm_nonneg (f x))
  nlinarith only [h]

private theorem integrand_measurable (hl : Measurable l) (hf : AEStronglyMeasurable f μ)
    (k : ℕ) (w : ℂ) :
    AEStronglyMeasurable (fun x ↦ f x * Complex.exp (w * (l x : ℂ)) * (l x : ℂ) ^ k) μ := by
  exact (hf.mul (by fun_prop : Measurable (fun x ↦ Complex.exp (w * (l x : ℂ)))).aestronglyMeasurable).mul
    (by fun_prop : Measurable (fun x ↦ (l x : ℂ) ^ k)).aestronglyMeasurable

/-- Inside the strip of exponential absolute integrability each angular Mellin moment
is holomorphic, and its derivative is the next moment. -/
theorem hasDerivAt_moment (hl : Measurable l) (hf : AEStronglyMeasurable f μ)
    {A : ℝ} (hA : Integrable (fun x ↦ ‖f x‖ * Real.exp (A * |l x|)) μ) (k : ℕ)
    {z : ℂ} (hz : |z.re| < A) :
    HasDerivAt (moment μ l f k) (moment μ l f (k + 1) z) z := by
  let β := (A + |z.re|) / 2
  have hb : β < A := by dsimp [β]; linarith
  have hzb : |z.re| < β := by dsimp [β]; linarith
  let U := {w : ℂ | |w.re| < β}
  have hO : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hInt : Integrable (fun x ↦ f x * Complex.exp (z * (l x : ℂ)) * (l x : ℂ) ^ k) μ :=
    (hA.const_mul ((k.factorial : ℝ) / (A - β) ^ k)).mono' (integrand_measurable hl hf k z)
      (.of_forall fun x ↦ integrand_bound k hb z hzb.le x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun w x ↦ f x * Complex.exp (w * (l x : ℂ)) * (l x : ℂ) ^ k)
    (F' := fun w x ↦ f x * Complex.exp (w * (l x : ℂ)) * (l x : ℂ) ^ (k + 1))
    (hO.mem_nhds hzb) (.of_forall (integrand_measurable hl hf k)) hInt
    (integrand_measurable hl hf (k + 1) z)
    (.of_forall fun x w hw ↦ integrand_bound (k + 1) hb w (le_of_lt hw) x)
    (hA.const_mul (((k + 1).factorial : ℝ) / (A - β) ^ (k + 1)))
    (.of_forall fun x w _ ↦ by
      simpa only [pow_succ, id_eq] using
        (((((hasDerivAt_id w).mul_const (l x : ℂ)).cexp).const_mul (f x)).mul_const ((l x : ℂ) ^ k) |>.congr_deriv
          (by simp; ring)))).2

/-- The j-th derivative of the Mellin transform at an interior point equals its
j-th logarithmic moment. -/
theorem iteratedDeriv_moment_zero (hl : Measurable l) (hf : AEStronglyMeasurable f μ)
    {A : ℝ} (hA : Integrable (fun x ↦ ‖f x‖ * Real.exp (A * |l x|)) μ) (k : ℕ)
    {z : ℂ} (hz : |z.re| < A) :
    iteratedDeriv k (moment μ l f 0) z = moment μ l f k z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hO : IsOpen {w : ℂ | |w.re| < A} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
    have he : iteratedDeriv k (moment μ l f 0) =ᶠ[𝓝 z] moment μ l f k := by
      filter_upwards [hO.mem_nhds hz] with w hw using ih hw
    rw [iteratedDeriv_succ, he.deriv_eq, (hasDerivAt_moment hl hf hA k hz).deriv]

/-- Each logarithmic moment is holomorphic throughout the strip of exponential integrability. -/
theorem analyticOnNhd_moment (hl : Measurable l) (hf : AEStronglyMeasurable f μ)
    {A : ℝ} (hA : Integrable (fun x ↦ ‖f x‖ * Real.exp (A * |l x|)) μ) (k : ℕ) :
    AnalyticOnNhd ℂ (moment μ l f k) {w : ℂ | |w.re| < A} := by
  have hO : IsOpen {w : ℂ | |w.re| < A} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  exact DifferentiableOn.analyticOnNhd
    (fun _ hw ↦ (hasDerivAt_moment hl hf hA k hw).differentiableAt.differentiableWithinAt) hO

end RiemannMasullo.MellinMoment
end
