module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelSymmetry
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

namespace RiemannMasullo.Selberg

open Complex MeasureTheory Set Filter
open scoped Topology

private theorem integrable_strip_majorant :
    Integrable (fun x : ℝ ↦ Real.exp (-|x| / 2)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · apply (integrableOn_congr_fun _ measurableSet_Iic).mp
      (integrableOn_exp_mul_Iic (a := 1 / 2) (by norm_num) 0)
    intro x hx
    simp [abs_of_nonpos (mem_Iic.mp hx), div_eq_mul_inv, mul_comm]
  · apply (integrableOn_congr_fun _ measurableSet_Ioi).mp
      (integrableOn_exp_mul_Ioi (a := -(1 / 2)) (by norm_num) 0)
    intro x hx
    simp [abs_of_pos (mem_Ioi.mp hx), div_eq_mul_inv, mul_comm]

/-- Horizontal contour shift for a holomorphic integrand with uniform exponential decay
between heights zero and `a`. -/
private theorem integral_horizontal_shift (F : ℂ → ℂ) (a M : ℝ)
    (hd : ∀ z : ℂ, z.im ∈ uIcc 0 a → DifferentiableAt ℂ F z)
    (hb : ∀ x y : ℝ, y ∈ uIcc 0 a →
      ‖F (x + y * I)‖ ≤ M * Real.exp (-|x| / 2)) :
    (∫ x : ℝ, F (x + (a : ℂ) * I)) = ∫ x : ℝ, F x := by
  have horiz (y : ℝ) (hy : y ∈ uIcc 0 a) :
      Tendsto (fun R : ℝ ↦ ∫ x in -R..R, F (x + (y : ℂ) * I)) atTop
        (𝓝 (∫ x : ℝ, F (x + (y : ℂ) * I))) := by
    apply intervalIntegral_tendsto_integral _ tendsto_neg_atTop_atBot tendsto_id
    refine (integrable_strip_majorant.const_mul M).mono' ?_ (.of_forall (fun x ↦ hb x y hy))
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro x
    exact (hd ((x : ℂ) + y * I) (by simpa using hy)).continuousAt.comp
      (f := fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * I) (by fun_prop)
  have side (s : ℝ → ℝ) (hs : Tendsto (fun R ↦ |s R|) atTop atTop) :
      Tendsto (fun R : ℝ ↦ ∫ y in (0 : ℝ)..a, F (s R + (y : ℂ) * I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm fun R ↦ intervalIntegral.norm_integral_le_of_norm_le_const
      fun y hy ↦ hb (s R) y (uIoc_subset_uIcc hy)
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_neg_atTop_atBot.comp hs).atBot_div_const (show (0 : ℝ) < 2 by norm_num))
    simpa using (h.const_mul M).mul_const |a - 0|
  have rect (R : ℝ) := integral_boundary_rect_eq_zero_of_differentiableOn F
    (⟨-R, 0⟩ : ℂ) (⟨R, a⟩ : ℂ) (fun z hz ↦ (hd z hz.2).differentiableWithinAt)
  have hlim := (((horiz 0 left_mem_uIcc).sub (horiz a right_mem_uIcc)).add
    ((side id tendsto_abs_atTop_atTop).const_smul I)).sub
    ((side (fun R ↦ -R) (by simpa using (tendsto_abs_atTop_atTop (G := ℝ)))).const_smul I)
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds (x := (0 : ℂ)) |>.congr
    (fun R ↦ (rect R).symm))
  simpa using (sub_eq_zero.mp (by simpa using heq)).symm

private theorem strip_height_lt {a y : ℝ} (ha : |a| < Real.pi / 4) (hy : y ∈ uIcc 0 a) :
    |y| < Real.pi / 4 := by
  exact lt_of_le_of_lt (by simpa using abs_sub_left_of_mem_uIcc hy) ha

/-- The height-dependent factor in the kernel estimate, including the Fourier phase,
attains a finite maximum on the closed interval between zero and `a`. -/
private theorem fourier_kernel_bound (t a : ℝ) (ha : |a| < Real.pi / 4) :
    ∃ M : ℝ, ∀ x y : ℝ, y ∈ uIcc 0 a →
      ‖K (x + y * I) * exp (I * ((t : ℂ) * (x + y * I)))‖ ≤ M * Real.exp (-|x| / 2) := by
  obtain ⟨C, _, hC⟩ := kernel_bound
  let B (y : ℝ) := C * (1 + (Real.sqrt (Real.cos (2 * y)))⁻¹) * Real.exp (-(t * y))
  have hc : ∀ y ∈ uIcc 0 a, Real.sqrt (Real.cos (2 * y)) ≠ 0 := by
    intro y hy
    obtain ⟨hl, hu⟩ := abs_lt.mp (strip_height_lt ha hy)
    apply (Real.sqrt_pos.mpr (Real.cos_pos_of_mem_Ioo ?_)).ne'
    constructor <;> linarith
  have hcont : ContinuousOn B (uIcc 0 a) := by
    dsimp [B]
    fun_prop (disch := assumption)
  obtain ⟨b, _, hmax⟩ := isCompact_uIcc.exists_isMaxOn nonempty_uIcc hcont
  refine ⟨B b, fun x y hy ↦ ?_⟩
  have hk := hC ((x : ℂ) + y * I) (by simpa using strip_height_lt ha hy)
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_I_re, mul_I_im, neg_zero, add_zero,
    zero_add] at hk
  rw [norm_mul, Complex.norm_exp, I_mul_re, im_ofReal_mul]
  simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
  calc
    _ ≤ (C * (1 + (Real.sqrt (Real.cos (2 * y)))⁻¹) * Real.exp (-|x| / 2)) *
        Real.exp (-(t * y)) := mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
    _ = B y * Real.exp (-|x| / 2) := by dsimp [B]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hmax y hy) (Real.exp_pos _).le

/-- Card 18. Shifting the kernel from the real axis to height a in the strip multiplies its
Fourier transform at t by exp(at).
Titchmarsh, §10.10, p. 269, rotation of the theta kernel. -/
theorem shift_transform (t a : ℝ) (ha : |a| < Real.pi/4) :
    ft (fun y ↦ K ((y : ℂ)+Complex.I*a)) t =
      (Real.exp (a*t) : ℂ) * ft (fun y ↦ K (y : ℂ)) t := by
  let F (z : ℂ) := K z * exp (I * ((t : ℂ) * z))
  obtain ⟨M, hM⟩ := fourier_kernel_bound t a ha
  have hd (z : ℂ) (hz : z.im ∈ uIcc 0 a) : DifferentiableAt ℂ F z :=
    (kernel_symmetry (strip_height_lt ha hz)).2.2.mul (by fun_prop)
  have hshift := integral_horizontal_shift F a M hd hM
  have hphase (x : ℝ) : (Real.exp (a*t) : ℂ) * F (x + (a : ℂ) * I) =
      K ((x : ℂ) + I*a) * osc (t*x) := by
    dsimp only [F, osc]
    rw [mul_comm I (a : ℂ), mul_left_comm, Complex.ofReal_exp, ← exp_add]
    push_cast
    congr 2
    linear_combination (a : ℂ) * t * I_sq
  unfold ft
  simp_rw [← hphase]
  rw [integral_const_mul, hshift]
  simp [F, osc]

end RiemannMasullo.Selberg
