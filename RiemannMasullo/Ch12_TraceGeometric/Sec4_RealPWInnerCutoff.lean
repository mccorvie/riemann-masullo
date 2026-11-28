module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # The inner spatial cutoff on the even real band of value zero at the origin

In the rational order-zero half-line chart the inverse even Fourier transform has kernel
`2 cos (2π x ξ)`. Vanishing at the origin means that the frequency data have integral zero.
Rescale the spatial interval `[0,r]` and the frequency interval `[0,Y]` to `[0,1]`,
and put `t = rY`. Removing the constant frequency vector centers the cosine row.
For the dilation `f(x) ↦ √d f(dx)` the two rows in the trace have parameters `t` and `dt`.

The real band and its polar-free subspace are the model discussed in #7602 and #7770.
We compute the fifth-order coefficient for both individual dilations and radial tests.
The absolute trace bound is uniform in the rescaled spatial mask. For a fixed mask the
coefficient contains its fourth moment and the variance of squared frequency on the unit interval.
This is the inner contribution in footnote 2 on p. 514. The comparison of the whole weighted
quotient trace with the sharp orbital masses in (12.4.1.24) is a further step.
-/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace RiemannMasullo.Isolated

local notation "μ₀" => Measure.restrict (volume : Measure ℝ) (Icc 0 1)
local notation "H" => Lp ℂ 2 μ₀

private instance realPW_unitInterval_probability : IsProbabilityMeasure μ₀ :=
  ⟨by simp [Measure.restrict_apply, Real.volume_Icc]⟩

/-- The cosine evaluation row on the unit frequency interval, projected orthogonally away
from constants. The scale `t` is the product of the bandwidth and the spatial radius. -/
def realPWInnerCosineRow (t x ξ : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * t * x * ξ) - ∫ η, Real.cos (2 * Real.pi * t * x * η) ∂μ₀

private theorem realPWInnerCosineRow_continuous (t : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ realPWInnerCosineRow t p.1 p.2) := by
  have hav : Continuous (fun x : ℝ ↦ ∫ ξ, Real.cos (2 * Real.pi * t * x * ξ) ∂μ₀) :=
    continuous_of_dominated (bound := fun _ ↦ (1 : ℝ))
      (fun x ↦ (by fun_prop : Continuous (fun ξ : ℝ ↦ Real.cos (2 * Real.pi * t * x * ξ))).aestronglyMeasurable)
      (fun x ↦ ae_of_all _ fun ξ ↦ Real.abs_cos_le_one _) (integrable_const _)
      (ae_of_all _ fun _ ↦ by fun_prop)
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ ↦ Real.cos (2 * Real.pi * t * p.1 * p.2))).sub
    (hav.comp continuous_fst)

private theorem realPWInnerCosineRow_bound (t x ξ : ℝ) : |realPWInnerCosineRow t x ξ| ≤ 2 := by
  have ha : ‖∫ η, Real.cos (2 * Real.pi * t * x * η) ∂μ₀‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ₀) (C := 1)
      (f := fun η ↦ Real.cos (2 * Real.pi * t * x * η))
      (ae_of_all _ fun η : ℝ ↦ Real.abs_cos_le_one (2 * Real.pi * t * x * η))
  unfold realPWInnerCosineRow
  exact (norm_sub_le (Real.cos (2 * Real.pi * t * x * ξ)) _).trans
    ((add_le_add (Real.abs_cos_le_one _) ha).trans_eq (by norm_num))

/-- Centering the cosine leaves its action on every mean-zero frequency vector unchanged. -/
theorem realPWInnerCosineRow_integral_of_mean_zero (t x : ℝ) (f : H)
    (hf : ∫ ξ, f ξ ∂μ₀ = 0) :
    (∫ ξ, (realPWInnerCosineRow t x ξ : ℂ) * f ξ ∂μ₀) =
      ∫ ξ, (Real.cos (2 * Real.pi * t * x * ξ) : ℂ) * f ξ ∂μ₀ := by
  let c (ξ : ℝ) : ℂ := Real.cos (2 * Real.pi * t * x * ξ)
  let a : ℂ := ((∫ η, Real.cos (2 * Real.pi * t * x * η) ∂μ₀ : ℝ) : ℂ)
  have hfi := (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hc : MemLp c ∞ μ₀ := memLp_top_of_bound
    (by dsimp [c]; fun_prop : Continuous c).aestronglyMeasurable 1
    (ae_of_all _ fun ξ ↦ by
      simpa only [c, Complex.norm_real, Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * Real.pi * t * x * ξ))
  have hcf : Integrable (fun ξ ↦ c ξ * f ξ) μ₀ := hfi.mul_of_top_right hc
  simp only [realPWInnerCosineRow, Complex.ofReal_sub, sub_mul]
  rw [integral_sub hcf (hfi.const_mul a), integral_const_mul, hf, mul_zero, sub_zero]

/-- The rescaled quadratic term of a cosine row before its frequency mean is removed. -/
private def innerMoment (u ξ : ℝ) : ℝ := ξ ^ 2 * Real.sinc (Real.pi * u * ξ) ^ 2

private theorem innerMoment_mem (u : ℝ) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    innerMoment u ξ ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · have ha : ξ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hξ.1 (sub_nonneg.mpr hξ.2), hξ.2]
    have hs : Real.sinc (Real.pi * u * ξ) ^ 2 ≤ 1 ^ 2 :=
      sq_le_sq.mpr (by simpa only [abs_one] using Real.abs_sinc_le_one (Real.pi * u * ξ))
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans (by simpa using hs)

private def centeredMoment (u ξ : ℝ) : ℝ := innerMoment u ξ - ∫ η, innerMoment u η ∂μ₀

private theorem centeredMoment_continuous : Continuous (fun p : ℝ × ℝ ↦ centeredMoment p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ ↦ innerMoment p.1 p.2) := by unfold innerMoment; fun_prop
  have hav : Continuous (fun u : ℝ ↦ ∫ η, innerMoment u η ∂μ₀) :=
    continuous_of_dominated (F := fun u η ↦ innerMoment u η) (bound := fun _ ↦ (1 : ℝ))
      (fun u ↦ (h.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (fun u ↦ (ae_restrict_mem measurableSet_Icc).mono fun ξ hξ ↦ by
        simpa only [Real.norm_of_nonneg (innerMoment_mem u hξ).1] using (innerMoment_mem u hξ).2)
      (integrable_const _) (ae_of_all _ fun ξ ↦ h.comp (continuous_id.prodMk continuous_const))
  exact h.sub (hav.comp continuous_fst)

private theorem centeredMoment_bound (u : ℝ) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    |centeredMoment u ξ| ≤ 1 := by
  have hav₀ : 0 ≤ ∫ η, innerMoment u η ∂μ₀ := integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Icc).mono
    fun η hη ↦ (innerMoment_mem u hη).1)
  have hav₁ : ‖∫ η, innerMoment u η ∂μ₀‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ₀) (f := innerMoment u) (C := 1)
      ((ae_restrict_mem measurableSet_Icc).mono fun η hη ↦ by
        simpa only [Real.norm_of_nonneg (innerMoment_mem u hη).1] using (innerMoment_mem u hη).2)
  rw [Real.norm_of_nonneg hav₀] at hav₁
  exact abs_le.mpr ⟨by dsimp [centeredMoment]; linarith [(innerMoment_mem u hξ).1],
    by dsimp [centeredMoment]; linarith [(innerMoment_mem u hξ).2]⟩

private theorem realPWInnerCosineRow_eq (t x ξ : ℝ) :
    realPWInnerCosineRow t x ξ =
      -(2 * Real.pi ^ 2 * (t * x) ^ 2) * centeredMoment (t * x) ξ := by
  let b := 2 * Real.pi ^ 2 * (t * x) ^ 2
  have hc (η : ℝ) : Real.cos (2 * Real.pi * t * x * η) = 1 - b * innerMoment (t * x) η := by
    let v := Real.pi * (t * x) * η
    have hs : Real.sin v = v * Real.sinc v := by
      by_cases hv : v = 0
      · simp [hv]
      · rw [Real.sinc_of_ne_zero hv]; field_simp
    rw [show 2 * Real.pi * t * x * η = 2 * v by dsimp [v]; ring, Real.cos_two_mul_eq_one_sub, hs]
    dsimp [b, innerMoment, v]
    ring
  have hi : Integrable (innerMoment (t * x)) μ₀ :=
    (by unfold innerMoment; fun_prop : Continuous (innerMoment (t * x))).continuousOn.integrableOn_compact
      isCompact_Icc
  simp only [realPWInnerCosineRow, hc, integral_sub (integrable_const _) (hi.const_mul b),
    integral_const, integral_const_mul, probReal_univ, one_smul, centeredMoment]
  dsimp [b]
  ring

private theorem innerCutoff_row_memLp (t : ℝ) :
    MemLp (fun p : ℝ × ℝ ↦ (realPWInnerCosineRow t p.1 p.2 : ℂ)) 2 (Measure.prod μ₀ μ₀) :=
  MemLp.of_bound (Complex.continuous_ofReal.comp (realPWInnerCosineRow_continuous t)).aestronglyMeasurable
    2 (ae_of_all _ fun p ↦ by simpa using realPWInnerCosineRow_bound t p.1 p.2)

private theorem innerCutoff_masked_memLp (t d : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    MemLp (fun p : ℝ × ℝ ↦ ((4 * t * Real.sqrt d : ℝ) : ℂ) *
      (ρ p.1 * (realPWInnerCosineRow (d * t) p.1 p.2 : ℂ))) 2 (Measure.prod μ₀ μ₀) := by
  apply MemLp.const_mul
  refine MemLp.of_bound (((hρ.comp measurable_fst).aestronglyMeasurable).mul
    (innerCutoff_row_memLp (d * t)).aestronglyMeasurable) 2 (ae_of_all _ fun p ↦ ?_)
  rw [norm_mul, Complex.norm_real]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hρ₁ p.1)).trans (realPWInnerCosineRow_bound _ _ _)

private theorem innerCutoff_transpose_memLp (t : ℝ) :
    MemLp (fun p : ℝ × ℝ ↦ (realPWInnerCosineRow t p.2 p.1 : ℂ)) 2 (Measure.prod μ₀ μ₀) :=
  MemLp.of_bound (Complex.continuous_ofReal.comp
    ((realPWInnerCosineRow_continuous t).comp continuous_swap)).aestronglyMeasurable
    2 (ae_of_all _ fun p ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      realPWInnerCosineRow_bound t p.2 p.1)

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2 and (12.4.1.7), p. 516. The nuclear contribution
of an inner spatial window for one dilation on the rational real order-zero even band with
value zero at the origin.
Reconstruction: Write `t = Yr` for bandwidth times inner radius and `d = 1/g` for the
inverse dilation. Rescale the two intervals to the unit interval. In frequency coordinates
the projection off constants centers each cosine row. The product acts on the whole
frequency interval, kills constants and has mean-zero range. -/
def realPWInnerCutoff (t d : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    nuclearEndomorphisms H :=
  let A := integralKernelOperator μ₀ ((innerCutoff_transpose_memLp t).toLp _)
  let B := integralKernelOperator μ₀ ((innerCutoff_masked_memLp t d ρ hρ hρ₁).toLp _)
  ⟨A.val.comp B.val, nuclear_hilbertSchmidt_comp A B⟩

/-- The transpose cosine row has frequency mean zero for every spatial coordinate. -/
theorem realPWInnerCosineRow_integral_eq_zero (t x : ℝ) : ∫ ξ, realPWInnerCosineRow t x ξ ∂μ₀ = 0 := by
  have hi : Integrable (fun ξ : ℝ ↦ Real.cos (2 * Real.pi * t * x * ξ)) μ₀ :=
    (by fun_prop : Continuous (fun ξ : ℝ ↦ Real.cos (2 * Real.pi * t * x * ξ))).continuousOn.integrableOn_compact
      isCompact_Icc
  simp [realPWInnerCosineRow, integral_sub hi (integrable_const _)]

private theorem innerCutoff_transpose_comp_apply (t : ℝ) (b : ℝ × ℝ → ℂ)
    (hb : MemLp b 2 (Measure.prod μ₀ μ₀)) (f : H) :
    let A := integralKernelOperator μ₀ ((innerCutoff_transpose_memLp t).toLp _)
    let B := integralKernelOperator μ₀ (hb.toLp b)
    ∀ᵐ ξ ∂μ₀, A.val (B.val f) ξ =
      ∫ x, (realPWInnerCosineRow t x ξ : ℂ) * ∫ η, b (x, η) * f η ∂μ₀ ∂μ₀ := by
  intro A B
  have hv : ∀ᵐ x ∂μ₀, B.val f x = ∫ η, b (x, η) * f η ∂μ₀ := by
    filter_upwards [integralKernelOperator_apply μ₀ (hb.toLp b) f,
      Measure.ae_ae_of_ae_prod hb.coeFn_toLp] with x hx hrow
    exact hx.2.trans (integral_congr_ae (hrow.mono fun η hη ↦ congrArg (· * f η) hη))
  filter_upwards [integralKernelOperator_apply μ₀ ((innerCutoff_transpose_memLp t).toLp _) (B.val f),
    Measure.ae_ae_of_ae_prod (innerCutoff_transpose_memLp t).coeFn_toLp] with ξ hξ hrow
  refine hξ.2.trans (integral_congr_ae ?_)
  filter_upwards [hrow, hv] with x hx hxv
  exact congrArg₂ (· * ·) hx hxv

/-- Paper: Theorem 12.4.1.1, (12.4.1.7), p. 516. On mean-zero frequency data the inner
window takes the inverse cosine transform at the dilated spatial point, multiplies by the
mask, and returns by the cosine transpose projected off constants.
Reconstruction: Both intervals use the unit-interval coordinates in `realPWInnerCutoff`. -/
theorem realPWInnerCutoff_apply_of_mean_zero (t d : ℝ) (ρ : ℝ → ℂ)
    (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) (f : H) (hf : ∫ ξ, f ξ ∂μ₀ = 0) :
    ∀ᵐ ξ ∂μ₀, (realPWInnerCutoff t d ρ hρ hρ₁).val f ξ =
      ∫ x, (realPWInnerCosineRow t x ξ : ℂ) *
        (((4 * t * Real.sqrt d : ℝ) : ℂ) * ρ x *
          ∫ η, (Real.cos (2 * Real.pi * (d * t) * x * η) : ℂ) * f η ∂μ₀) ∂μ₀ := by
  filter_upwards [innerCutoff_transpose_comp_apply t _ (innerCutoff_masked_memLp t d ρ hρ hρ₁) f]
    with ξ hξ
  refine hξ.trans (integral_congr_ae (ae_of_all _ fun x ↦ ?_))
  dsimp only
  congr 1
  rw [← realPWInnerCosineRow_integral_of_mean_zero (d * t) x f hf, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun η ↦ by ring)

private theorem innerCutoff_transpose_trace (t : ℝ) (b : ℝ × ℝ → ℂ)
    (hb : MemLp b 2 (Measure.prod μ₀ μ₀)) :
    let A := integralKernelOperator μ₀ ((innerCutoff_transpose_memLp t).toLp _)
    let B := integralKernelOperator μ₀ (hb.toLp b)
    hilbertTrace ⟨A.val.comp B.val, nuclear_hilbertSchmidt_comp A B⟩ =
      ∫ p : ℝ × ℝ, (realPWInnerCosineRow t p.1 p.2 : ℂ) * b p ∂(Measure.prod μ₀ μ₀) := by
  let a := (innerCutoff_transpose_memLp t).toLp _
  intro A B
  rw [hilbertTrace_integralKernelOperator_comp_of_hilbertSchmidt,
    ← integral_prod_swap (μ := μ₀) (ν := μ₀) (fun p : ℝ × ℝ ↦ a p * hb.toLp b p.swap)]
  apply integral_congr_ae
  filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (innerCutoff_transpose_memLp t).coeFn_toLp, hb.coeFn_toLp] with p ha hbp
  exact congrArg₂ (· * ·) ha hbp

private theorem realPWInnerCutoff_trace (t d : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    hilbertTrace (realPWInnerCutoff t d ρ hρ hρ₁) =
      ∫ p : ℝ × ℝ, ((4 * t * Real.sqrt d : ℝ) : ℂ) * ρ p.1 *
        (realPWInnerCosineRow t p.1 p.2 : ℂ) * (realPWInnerCosineRow (d * t) p.1 p.2 : ℂ)
        ∂(Measure.prod μ₀ μ₀) := by
  rw [realPWInnerCutoff, innerCutoff_transpose_trace t _ (innerCutoff_masked_memLp t d ρ hρ hρ₁)]
  exact integral_congr_ae (ae_of_all _ fun p ↦ by ring)

private def innerCutoffProfile (d : ℝ) (ρ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, ρ p.1 * ((p.1 ^ 4 *
    centeredMoment (t * p.1) p.2 * centeredMoment (d * t * p.1) p.2 : ℝ) : ℂ) ∂(Measure.prod μ₀ μ₀)

private theorem realPWInnerCutoff_trace_eq_profile (t d : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    hilbertTrace (realPWInnerCutoff t d ρ hρ hρ₁) =
      (((2 * Real.pi) ^ 4 * Real.sqrt d * d ^ 2 * t ^ 5 : ℝ) : ℂ) * innerCutoffProfile d ρ t := by
  rw [realPWInnerCutoff_trace, innerCutoffProfile, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  simp only [realPWInnerCosineRow_eq, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

private theorem innerCutoffProfile_pointwise (t d : ℝ) (ρ : ℝ → ℂ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1)
    (p : ℝ × ℝ) (hx : p.1 ∈ Icc (0 : ℝ) 1) (hξ : p.2 ∈ Icc (0 : ℝ) 1) :
    ‖ρ p.1 * ((p.1 ^ 4 * centeredMoment (t * p.1) p.2 * centeredMoment (d * t * p.1) p.2 : ℝ) : ℂ)‖ ≤
      p.1 ^ 4 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg hx.1]
  calc
    _ ≤ 1 * (p.1 ^ 4 * 1 * 1) := by
      gcongr
      · exact hρ₁ _
      · exact centeredMoment_bound _ hξ
      · exact centeredMoment_bound _ hξ
    _ = _ := by ring

private theorem innerCutoffProfile_continuous (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) : Continuous (fun z : ℝ × ℝ ↦ innerCutoffProfile z.1 ρ z.2) := by
  unfold innerCutoffProfile
  apply continuous_of_dominated (bound := fun _ ↦ (1 : ℝ))
  · intro z
    apply ((hρ.comp measurable_fst).aestronglyMeasurable).mul
    apply Continuous.aestronglyMeasurable
    apply Complex.continuous_ofReal.comp
    exact ((continuous_fst.pow 4).mul (centeredMoment_continuous.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd))).mul
      (centeredMoment_continuous.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))
  · intro z
    have hI : ∀ᵐ x ∂μ₀, x ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ₀) (ν := μ₀)).ae hI,
      (Measure.quasiMeasurePreserving_snd (μ := μ₀) (ν := μ₀)).ae hI]
      with p hx hξ
    change p.1 ∈ Icc (0 : ℝ) 1 at hx
    change p.2 ∈ Icc (0 : ℝ) 1 at hξ
    exact (innerCutoffProfile_pointwise z.2 z.1 ρ hρ₁ p hx hξ).trans (pow_le_one₀ hx.1 hx.2)
  · exact integrable_const _
  · refine ae_of_all _ fun p ↦ continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact (continuous_const.mul (centeredMoment_continuous.comp
      ((continuous_snd.mul continuous_const).prodMk continuous_const))).mul
      (centeredMoment_continuous.comp
        (((continuous_fst.mul continuous_snd).mul continuous_const).prodMk continuous_const))

private theorem innerCutoffProfile_continuous_radius (d : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) : Continuous (innerCutoffProfile d ρ) := by
  simpa only [Function.comp_def, id_eq] using (innerCutoffProfile_continuous ρ hρ hρ₁).comp
    (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (d, t)))

private theorem innerCutoffProfile_continuous_dilation (t : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) : Continuous (fun d ↦ innerCutoffProfile d ρ t) := by
  simpa only [Function.comp_def, id_eq] using (innerCutoffProfile_continuous ρ hρ hρ₁).comp
    (continuous_id.prodMk continuous_const : Continuous (fun d : ℝ ↦ (d, t)))

private theorem innerCutoff_integral_pow (n : ℕ) : ∫ x, x ^ n ∂μ₀ = 1 / (n + 1 : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp

private theorem innerCutoffProfile_zero (d : ℝ) (ρ : ℝ → ℂ) :
    innerCutoffProfile d ρ 0 = (4 / 45 : ℂ) * ∫ x, ρ x * (x : ℂ) ^ 4 ∂μ₀ := by
  have h2 := innerCutoff_integral_pow 2
  have h4 := innerCutoff_integral_pow 4
  norm_num at h2 h4
  have hmoment : (∫ ξ, (ξ ^ 2 - (1 / 3 : ℝ)) ^ 2 ∂μ₀) = 4 / 45 := by
    have hi (n : ℕ) : Integrable (fun x : ℝ ↦ x^n) μ₀ :=
      (continuous_id.pow n).continuousOn.integrableOn_compact isCompact_Icc
    have he (ξ : ℝ) : (ξ ^ 2 - (1 / 3 : ℝ)) ^ 2 = ξ ^ 4 - (2 / 3) * ξ ^ 2 + 1 / 9 := by ring
    simp_rw [he]
    have hi' : Integrable (fun ξ : ℝ ↦ ξ ^ 4 - (2 / 3) * ξ ^ 2) μ₀ := (hi 4).sub ((hi 2).const_mul (2 / 3 : ℝ))
    rw [integral_add hi' (integrable_const (1 / 9 : ℝ)),
      integral_sub (hi 4) ((hi 2).const_mul (2 / 3 : ℝ)), integral_const_mul, h2, h4]
    norm_num
  have hrow (ξ : ℝ) : centeredMoment 0 ξ = ξ ^ 2 - 1 / 3 := by
    simp [centeredMoment, innerMoment, h2]
  unfold innerCutoffProfile
  simp only [mul_zero, zero_mul, hrow]
  have he (p : ℝ × ℝ) :
      ρ p.1 * ((p.1 ^ 4 * (p.2 ^ 2 - 1 / 3) * (p.2 ^ 2 - 1 / 3) : ℝ) : ℂ) =
        (ρ p.1 * (p.1 : ℂ) ^ 4) * (((p.2 ^ 2 - 1 / 3) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  simp_rw [he]
  rw [integral_prod_mul (μ := μ₀) (ν := μ₀) (fun x : ℝ ↦ ρ x * (x : ℂ) ^ 4)
    (fun ξ : ℝ ↦ (((ξ ^ 2 - 1 / 3) ^ 2 : ℝ) : ℂ)), integral_complex_ofReal, hmoment]
  push_cast
  ring

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2 and (12.4.1.7), p. 516. At order zero for the real
place of the rationals, the trace removed by an inner spatial mask has an explicit fifth-order
term in `t = Yr`, the product of bandwidth and inner radius. The coefficient is the fourth
spatial moment of the rescaled mask times the variance of squared frequency and the dilation
factor. In particular the estimate applies while the bandwidth varies.
Reconstruction: The dilation is `f(x) ↦ √d f(dx)` on the half-line. The centered cosine
kernel imposes the zero-value polar condition in frequency coordinates. This is a local
trace calculation for the independent floor in footnote 2. -/
theorem realPWInnerCutoff_trace_div_pow_five_tendsto (d : ℝ) (_hd : 0 < d) (ρ : ℝ → ℂ)
    (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    Tendsto (fun t : ℝ ↦ hilbertTrace (realPWInnerCutoff t d ρ hρ hρ₁) / (t : ℂ) ^ 5)
      (𝓝[>] 0) (𝓝 (((2 * Real.pi) ^ 4 * Real.sqrt d * d ^ 2 * (4 / 45) : ℝ) *
        (∫ x, ρ x * (x : ℂ) ^ 4 ∂μ₀) : ℂ)) := by
  let C : ℂ := ((2 * Real.pi) ^ 4 * Real.sqrt d * d ^ 2 : ℝ)
  have h : Tendsto (fun t ↦ C * innerCutoffProfile d ρ t) (𝓝[>] (0 : ℝ))
      (𝓝 (C * innerCutoffProfile d ρ 0)) :=
    tendsto_const_nhds.mul ((innerCutoffProfile_continuous_radius d ρ hρ hρ₁).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  have hc : C * innerCutoffProfile d ρ 0 = (((2 * Real.pi) ^ 4 * Real.sqrt d * d ^ 2 * (4 / 45) : ℝ) : ℂ) *
      (∫ x, ρ x * (x : ℂ) ^ 4 ∂μ₀) := by
    rw [innerCutoffProfile_zero]
    dsimp [C]
    push_cast
    ring
  rw [← hc]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mem_Ioi.mp ht).ne'
  rw [realPWInnerCutoff_trace_eq_profile]
  dsimp [C]
  push_cast
  field_simp

private theorem innerCutoffProfile_norm_le (t d : ℝ) (ρ : ℝ → ℂ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    ‖innerCutoffProfile d ρ t‖ ≤ 1 / 5 := by
  have hi : Integrable (fun x : ℝ ↦ x ^ 4) μ₀ :=
    (continuous_id.pow 4).continuousOn.integrableOn_compact isCompact_Icc
  unfold innerCutoffProfile
  calc
    _ ≤ ∫ p : ℝ × ℝ, p.1 ^ 4 ∂(Measure.prod μ₀ μ₀) := by
      apply norm_integral_le_of_norm_le (hi.comp_fst μ₀)
      have hI : ∀ᵐ x ∂μ₀, x ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ₀) (ν := μ₀)).ae hI,
        (Measure.quasiMeasurePreserving_snd (μ := μ₀) (ν := μ₀)).ae hI] with p hx hξ
      exact innerCutoffProfile_pointwise t d ρ hρ₁ p hx hξ
    _ = 1 / 5 := by
      rw [integral_fun_fst (μ := μ₀) (ν := μ₀) (fun x : ℝ ↦ x ^ 4), innerCutoff_integral_pow]
      norm_num

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2. The cost of a sharp or smoothed inner window
on the polar-free even real band is bounded uniformly in its measurable mask at fifth
order in bandwidth times radius.
Reconstruction: This bound allows the mask and the bandwidth to vary together. -/
theorem norm_realPWInnerCutoff_trace_le (t d : ℝ) (ht : 0 ≤ t) (ρ : ℝ → ℂ)
    (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    ‖hilbertTrace (realPWInnerCutoff t d ρ hρ hρ₁)‖ ≤
      (2 * Real.pi) ^ 4 * Real.sqrt d * d ^ 2 * t ^ 5 / 5 := by
  have hb := innerCutoffProfile_norm_le t d ρ hρ₁
  rw [realPWInnerCutoff_trace_eq_profile, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2. For the sharp inner interval and the identity
dilation the leading coefficient is strictly positive, so fifth order is attained.
Reconstruction: In this normalization it equals `4 (2π)⁴ / 225`. -/
theorem realPWInnerCutoff_sharp_trace_div_pow_five_tendsto :
    Tendsto (fun t : ℝ ↦ hilbertTrace (realPWInnerCutoff t 1 (fun _ ↦ 1)
      measurable_const (fun _ ↦ (norm_one : ‖(1 : ℂ)‖ = 1).le)) / (t : ℂ) ^ 5)
      (𝓝[>] 0) (𝓝 (((4 * (2 * Real.pi) ^ 4 / 225 : ℝ) : ℂ))) := by
  have h := realPWInnerCutoff_trace_div_pow_five_tendsto 1 zero_lt_one (fun _ ↦ (1 : ℂ))
    measurable_const (fun _ ↦ (norm_one : ‖(1 : ℂ)‖ = 1).le)
  have h4 : (∫ x : ℝ, (x : ℂ) ^ 4 ∂μ₀) = 1 / 5 := by
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, innerCutoff_integral_pow]
    norm_num
  simp only [one_mul, h4, Real.sqrt_one, one_pow, mul_one, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow] at h ⊢
  convert h using 2
  ring

/-- The centered cosine row is continuous as the product of the bandwidth and the
spatial coordinate changes. -/
private theorem innerCutoff_cosine_scale (t x ξ : ℝ) :
    realPWInnerCosineRow t x ξ = realPWInnerCosineRow 1 (t * x) ξ := by
  simp only [realPWInnerCosineRow, mul_one, mul_assoc]

private def innerTestRow (ν : Measure ℝ) (w : ℝ → ℂ) (t : ℝ) (p : ℝ × ℝ) : ℂ :=
  ∫ d, w d * (realPWInnerCosineRow (d * t) p.1 p.2 : ℂ) ∂ν

private theorem innerTestRow_continuous (ν : Measure ℝ) (w : ℝ → ℂ) (hw : Integrable w ν) (t : ℝ) :
    Continuous (innerTestRow ν w t) := by
  unfold innerTestRow
  simp_rw [innerCutoff_cosine_scale (_ * t)]
  apply continuous_of_dominated (bound := fun d ↦ ‖w d‖ * 2)
  · intro p
    exact hw.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
      ((realPWInnerCosineRow_continuous 1).comp
        (((continuous_id.mul continuous_const).mul continuous_const).prodMk
          continuous_const))).aestronglyMeasurable
  · intro p
    refine ae_of_all _ fun d ↦ ?_
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (realPWInnerCosineRow_bound _ _ _) (norm_nonneg _)
  · exact hw.norm.mul_const 2
  · refine ae_of_all _ fun d ↦ continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact (realPWInnerCosineRow_continuous 1).comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)

private theorem innerTest_masked_memLp (ν : Measure ℝ) (w : ℝ → ℂ) (hw : Integrable w ν)
    (t : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) :
    MemLp (fun p : ℝ × ℝ ↦ ((4 * t : ℝ) : ℂ) * (ρ p.1 * innerTestRow ν w t p)) 2 (Measure.prod μ₀ μ₀) := by
  apply MemLp.const_mul
  refine MemLp.of_bound (((hρ.comp measurable_fst).aestronglyMeasurable).mul
    (innerTestRow_continuous ν w hw t).aestronglyMeasurable) (∫ d, ‖w d‖ * 2 ∂ν) (ae_of_all _ fun p ↦ ?_)
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (hρ₁ _)).trans ?_
  apply norm_integral_le_of_norm_le (hw.norm.mul_const 2)
  refine ae_of_all _ fun d ↦ ?_
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (realPWInnerCosineRow_bound _ _ _) (norm_nonneg _)

/-- Paper: Theorem 12.4.1.1, (12.4.1.7), p. 516. The inner-window operator averaged
against a radial dilation test on the real, order-zero polar-free band.
Reconstruction: The weight `w(d) dν(d)` includes the half-density factor for the dilation
`x ↦ dx`. The right Hilbert–Schmidt kernel integrates the test before taking the trace. -/
def realPWInnerTestCutoff (t : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1)
    (ν : Measure ℝ) (w : ℝ → ℂ) (hw : Integrable w ν) : nuclearEndomorphisms H :=
  let A := integralKernelOperator μ₀ ((innerCutoff_transpose_memLp t).toLp _)
  let B := integralKernelOperator μ₀ ((innerTest_masked_memLp ν w hw t ρ hρ hρ₁).toLp _)
  ⟨A.val.comp B.val, nuclear_hilbertSchmidt_comp A B⟩

private theorem innerTestRow_pair (t x : ℝ) (ν : Measure ℝ) [SFinite ν] (w : ℝ → ℂ)
    (hw : Integrable w ν) (f : H) (hf : ∫ ξ, f ξ ∂μ₀ = 0) :
    (∫ η, innerTestRow ν w t (x, η) * f η ∂μ₀) =
      ∫ d, w d * ∫ η, (Real.cos (2 * Real.pi * (d * t) * x * η) : ℂ) * f η ∂μ₀ ∂ν := by
  let J (d η : ℝ) := w d * (realPWInnerCosineRow (d * t) x η : ℂ) * f η
  have hfi := (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hJ : Integrable (Function.uncurry J) (ν.prod μ₀) := by
    apply ((hw.norm.mul_prod hfi.norm).const_mul 2).mono'
    · unfold Function.uncurry J
      refine (hw.aestronglyMeasurable.comp_fst.mul ?_).mul (Lp.aestronglyMeasurable f).comp_snd
      simp_rw [innerCutoff_cosine_scale (_ * t)]
      exact (Complex.continuous_ofReal.comp ((realPWInnerCosineRow_continuous 1).comp
        (((continuous_fst.mul continuous_const).mul continuous_const).prodMk continuous_snd))).aestronglyMeasurable
    · refine ae_of_all _ fun p ↦ ?_
      simp only [Function.uncurry, J, norm_mul, Complex.norm_real]
      calc
        _ ≤ ‖w p.1‖ * 2 * ‖f p.2‖ := by gcongr; exact realPWInnerCosineRow_bound _ _ _
        _ = _ := by ring
  calc
    _ = ∫ η, ∫ d, J d η ∂ν ∂μ₀ := by simp only [innerTestRow, J, integral_mul_const]
    _ = ∫ d, ∫ η, J d η ∂μ₀ ∂ν := (integral_integral_swap hJ).symm
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun d ↦ ?_)
      dsimp only
      rw [← realPWInnerCosineRow_integral_of_mean_zero (d * t) x f hf, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun η ↦ mul_assoc _ _ _)

/-- Paper: Theorem 12.4.1.1, (12.4.1.7)–(12.4.1.9), pp. 516–517. The inner-window
operator on mean-zero frequency data integrates the actual dilated cosine transforms
against the radial test, multiplies by the spatial mask, and projects back to the band.
Reconstruction: The half density and Haar measure are included in the dilation weight. -/
theorem realPWInnerTestCutoff_apply_of_mean_zero (t : ℝ) (ρ : ℝ → ℂ)
    (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) (ν : Measure ℝ) [SFinite ν]
    (w : ℝ → ℂ) (hw : Integrable w ν) (f : H) (hf : ∫ ξ, f ξ ∂μ₀ = 0) :
    ∀ᵐ ξ ∂μ₀, (realPWInnerTestCutoff t ρ hρ hρ₁ ν w hw).val f ξ =
      ∫ x, (realPWInnerCosineRow t x ξ : ℂ) * (((4 * t : ℝ) : ℂ) * ρ x *
        ∫ d, w d * ∫ η, (Real.cos (2 * Real.pi * (d * t) * x * η) : ℂ) * f η ∂μ₀ ∂ν) ∂μ₀ := by
  filter_upwards [innerCutoff_transpose_comp_apply t _ (innerTest_masked_memLp ν w hw t ρ hρ hρ₁) f]
    with ξ hξ
  refine hξ.trans (integral_congr_ae (ae_of_all _ fun x ↦ ?_))
  dsimp only
  congr 1
  rw [← innerTestRow_pair t x ν w hw f hf, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun η ↦ by ring)

private theorem innerTestCutoff_trace_eq (t : ℝ) (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) (ν : Measure ℝ) [SFinite ν] (w : ℝ → ℂ) (hw : Integrable w ν) :
    hilbertTrace (realPWInnerTestCutoff t ρ hρ hρ₁ ν w hw) =
      (((2 * Real.pi) ^ 4 * t ^ 5 : ℝ) : ℂ) *
        ∫ d, (w d * (d : ℂ) ^ 2) * innerCutoffProfile d ρ t ∂ν := by
  let J (p : ℝ × ℝ) (d : ℝ) : ℂ :=
    ρ p.1 * (realPWInnerCosineRow t p.1 p.2 : ℂ) * w d * (realPWInnerCosineRow (d * t) p.1 p.2 : ℂ)
  have hJ : Integrable (Function.uncurry J) ((Measure.prod μ₀ μ₀).prod ν) := by
    have hj (d : ℝ) (p : ℝ × ℝ) : ‖J p d‖ ≤ ‖w d‖ * 4 := by
      simp only [J, norm_mul, Complex.norm_real]
      calc
        _ ≤ 1 * 2 * ‖w d‖ * 2 := by
          gcongr
          · exact hρ₁ _
          · exact realPWInnerCosineRow_bound _ _ _
          · exact realPWInnerCosineRow_bound _ _ _
        _ = _ := by ring
    apply ((hw.norm.mul_const 4).comp_snd (Measure.prod μ₀ μ₀)).mono'
    · unfold J Function.uncurry
      apply AEStronglyMeasurable.mul
      · exact ((hρ.comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp
            ((realPWInnerCosineRow_continuous t).comp continuous_fst)).aestronglyMeasurable).mul
          hw.aestronglyMeasurable.comp_snd
      · simp_rw [innerCutoff_cosine_scale (_ * t)]
        exact (Complex.continuous_ofReal.comp ((realPWInnerCosineRow_continuous 1).comp
          (((continuous_snd.mul continuous_const).mul (continuous_fst.comp continuous_fst)).prodMk
            (continuous_snd.comp continuous_fst)))).aestronglyMeasurable
    · exact ae_of_all _ fun z ↦ hj z.2 z.1
  calc
    _ = ((4 * t : ℝ) : ℂ) * ∫ p : ℝ × ℝ, ∫ d, J p d ∂ν ∂(Measure.prod μ₀ μ₀) := by
      rw [realPWInnerTestCutoff, innerCutoff_transpose_trace t _ (innerTest_masked_memLp ν w hw t ρ hρ hρ₁),
        ← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun p ↦ ?_
      change _ * (_ * (_ * (∫ d, w d * _ ∂ν))) = _
      have he (d : ℝ) : J p d = (ρ p.1 * (realPWInnerCosineRow t p.1 p.2 : ℂ)) *
          (w d * (realPWInnerCosineRow (d * t) p.1 p.2 : ℂ)) := by dsimp [J]; ring
      simp_rw [he]
      rw [integral_const_mul]
      ring
    _ = _ := by
      rw [integral_integral_swap hJ, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun d ↦ ?_
      dsimp only
      simp only [innerCutoffProfile, ← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun p ↦ ?_
      simp only [J, realPWInnerCosineRow_eq, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
        Complex.ofReal_ofNat]
      ring

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2. A product radius tending to zero removes the
inner spatial cutoff in the real order-zero model, uniformly for masks of norm at most one.
Reconstruction: The constant depends only on the absolute second moment of the radial
test in reciprocal dilation coordinates. -/
theorem norm_realPWInnerTestCutoff_trace_le (t : ℝ) (ht : 0 ≤ t) (ρ : ℝ → ℂ)
    (hρ : Measurable ρ) (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) (ν : Measure ℝ) [SFinite ν]
    (w : ℝ → ℂ) (hw : Integrable w ν) (hw₂ : Integrable (fun d ↦ w d * (d : ℂ) ^ 2) ν) :
    ‖hilbertTrace (realPWInnerTestCutoff t ρ hρ hρ₁ ν w hw)‖ ≤
      (2 * Real.pi) ^ 4 * t ^ 5 / 5 * ∫ d, ‖w d * (d : ℂ) ^ 2‖ ∂ν := by
  let W (d : ℝ) := w d * (d : ℂ) ^ 2
  have hb : ‖∫ d, W d * innerCutoffProfile d ρ t ∂ν‖ ≤ (∫ d, ‖W d‖ ∂ν) * (1 / 5) := by
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le (hw₂.norm.mul_const _)
    refine ae_of_all _ fun d ↦ ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (innerCutoffProfile_norm_le t d ρ hρ₁) (norm_nonneg _)
  rw [innerTestCutoff_trace_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by dsimp [W]; ring)

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2. In the real polar-free model the removed
operator trace tends to zero along every family with bandwidth times inner radius
tending to zero, including families with varying mask shapes.
Reconstruction: For the independent lower cutoff take `Y = λ′` and `r = 1/λ″`. -/
theorem realPWInnerTestCutoff_trace_tendsto_zero {ι : Type*} {l : Filter ι}
    (Y r : ι → ℝ) (hpos : ∀ i, 0 ≤ Y i * r i)
    (hYr : Tendsto (fun i ↦ Y i * r i) l (𝓝 0))
    (ρ : ι → ℝ → ℂ) (hρ : ∀ i, Measurable (ρ i)) (hρ₁ : ∀ i x, ‖ρ i x‖ ≤ 1)
    (ν : Measure ℝ) [SFinite ν] (w : ℝ → ℂ) (hw : Integrable w ν)
    (hw₂ : Integrable (fun d ↦ w d * (d : ℂ) ^ 2) ν) :
    Tendsto (fun i ↦ hilbertTrace (realPWInnerTestCutoff (Y i * r i) (ρ i)
      (hρ i) (hρ₁ i) ν w hw)) l (𝓝 0) := by
  apply squeeze_zero_norm (fun i ↦ norm_realPWInnerTestCutoff_trace_le (Y i * r i) (hpos i)
    (ρ i) (hρ i) (hρ₁ i) ν w hw hw₂)
  simpa only [zero_pow (by decide : 5 ≠ 0), mul_zero, zero_div, zero_mul] using
    (((hYr.pow 5).const_mul ((2 * Real.pi) ^ 4)).div_const 5).mul_const
      (∫ d, ‖w d * (d : ℂ) ^ 2‖ ∂ν)

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2 and Steps I–III, pp. 515–517. The fifth-order
coefficient for a radial dilation test factors as its second dilation moment times the
fourth moment of the rescaled spatial mask.
Reconstruction: The weight includes half density. In terms of the multiplier `f(x/g)/√g`,
the second moment is the integral of the test times `g ^ (-5 / 2)` against multiplicative Haar.
The hypotheses hold for a compactly supported radial test on the positive ray. -/
theorem realPWInnerTestCutoff_trace_div_pow_five_tendsto (ρ : ℝ → ℂ) (hρ : Measurable ρ)
    (hρ₁ : ∀ x, ‖ρ x‖ ≤ 1) (ν : Measure ℝ) [SFinite ν] (w : ℝ → ℂ) (hw : Integrable w ν)
    (hw₂ : Integrable (fun d ↦ w d * (d : ℂ) ^ 2) ν) :
    Tendsto (fun t : ℝ ↦ hilbertTrace (realPWInnerTestCutoff t ρ hρ hρ₁ ν w hw) / (t : ℂ) ^ 5)
      (𝓝[>] 0) (𝓝 (((2 * Real.pi) ^ 4 * (4 / 45) : ℝ) *
        (∫ x, ρ x * (x : ℂ) ^ 4 ∂μ₀) * (∫ d, w d * (d : ℂ) ^ 2 ∂ν) : ℂ)) := by
  let W (d : ℝ) := w d * (d : ℂ) ^ 2
  have hc : Continuous (fun t ↦ ∫ d, W d * innerCutoffProfile d ρ t ∂ν) := by
    apply continuous_of_dominated (bound := fun d ↦ ‖W d‖ * (1 / 5))
    · exact fun t ↦ hw₂.aestronglyMeasurable.mul
        (innerCutoffProfile_continuous_dilation t ρ hρ hρ₁).aestronglyMeasurable
    · intro t
      refine ae_of_all _ fun d ↦ ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (innerCutoffProfile_norm_le t d ρ hρ₁) (norm_nonneg _)
    · exact hw₂.norm.mul_const _
    · exact ae_of_all _ fun d ↦ continuous_const.mul (innerCutoffProfile_continuous_radius d ρ hρ hρ₁)
  let C : ℂ := ((2 * Real.pi) ^ 4 : ℝ)
  have hl : Tendsto (fun t ↦ C * ∫ d, W d * innerCutoffProfile d ρ t ∂ν) (𝓝[>] (0 : ℝ))
      (𝓝 (C * ∫ d, W d * innerCutoffProfile d ρ 0 ∂ν)) :=
    tendsto_const_nhds.mul (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have he : C * (∫ d, W d * innerCutoffProfile d ρ 0 ∂ν) = (((2 * Real.pi) ^ 4 * (4 / 45) : ℝ) : ℂ) *
      (∫ x, ρ x * (x : ℂ) ^ 4 ∂μ₀) * ∫ d, w d * (d : ℂ) ^ 2 ∂ν := by
    simp_rw [innerCutoffProfile_zero]
    rw [integral_mul_const]
    dsimp [C, W]
    push_cast
    ring
  rw [← he]
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mem_Ioi.mp ht).ne'
  rw [innerTestCutoff_trace_eq]
  dsimp [C, W]
  push_cast
  field_simp

end RiemannMasullo.Isolated
