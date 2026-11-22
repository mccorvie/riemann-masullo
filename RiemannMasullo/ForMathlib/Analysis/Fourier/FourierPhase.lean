module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Differentiation of Fourier phases under an integral -/

noncomputable section

open MeasureTheory Set

namespace RiemannMasullo

/-- First absolute moments dominate the derivative of a finite sum of real Fourier phases. -/
public theorem hasDerivAt_integral_fourier_phase {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (μ : Measure Y) (a : Y → ℂ) (ha : Integrable a μ) (k : ι → Y → ℂ)
    (hk : ∀ i, AEStronglyMeasurable (k i) μ)
    (hm : ∀ i, Integrable (fun y ↦ ‖a y‖ * ‖k i y‖) μ)
    (z dz : ℝ → ι → ℂ) (hz : ∀ s i, HasDerivAt (fun t ↦ z t i) (dz s i) s)
    (hz0 : ∀ i, z 0 i = 0) (hd : ∀ i, Continuous fun s ↦ dz s i) :
    let P (s : ℝ) (y : Y) := 2 * Real.pi * ∑ i, (z s i * k i y).re
    let D (y : Y) := a y * (((2 * Real.pi * ∑ i, (dz 0 i * k i y).re : ℝ) : ℂ) * Complex.I)
    Integrable D μ ∧ HasDerivAt (fun s ↦ ∫ y, a y * (Circle.exp (P s y) : ℂ) ∂μ)
      (∫ y, D y ∂μ) 0 := by
  classical
  let P (u : ι → ℂ) (y : Y) := 2 * Real.pi * ∑ i, (u i * k i y).re
  let K (s : ℝ) (y : Y) : ℂ := Circle.exp (P (z s) y)
  let D (s : ℝ) (y : Y) := a y * (K s y * ((P (dz s) y : ℂ) * Complex.I))
  have hP (u : ι → ℂ) : AEStronglyMeasurable (P u) μ := by
    apply AEStronglyMeasurable.const_mul
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
      Complex.continuous_re.comp_aestronglyMeasurable ((hk i).const_mul _)
  have hK (s) : AEStronglyMeasurable (K s) μ :=
    (show Continuous (fun x : ℝ ↦ (Circle.exp x : ℂ)) from
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).comp_aestronglyMeasurable
        (hP _)
  have hder (s : ℝ) (y : Y) : HasDerivAt (fun t ↦ a y * K t y) (D s y) s := by
    have h : HasDerivAt (fun t ↦ P (z t) y) (P (dz s) y) s :=
      (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((hz s i).mul_const (k i y))).const_mul _
    exact ((h.ofReal_comp.mul_const Complex.I).cexp).const_mul (a y)
  choose C hC using fun i ↦ isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (hd i).continuousOn
  let bound (y : Y) := (2 * Real.pi) * ∑ i, C i * (‖a y‖ * ‖k i y‖)
  have hbound : Integrable bound μ :=
    (integrable_finsetSum _ fun i _ ↦ (hm i).const_mul (C i)).const_mul _
  have hle (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) (y : Y) : ‖D s y‖ ≤ bound y := by
    have hreal : ‖∑ i, (dz s i * k i y).re‖ ≤ ∑ i, C i * ‖k i y‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun i _ ↦ (Complex.abs_re_le_norm _).trans
        ((norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hC i s hs) (norm_nonneg _)))
    have hnonneg : 0 ≤ 2 * Real.pi := by positivity
    change ‖a y * (K s y * ((P (dz s) y : ℂ) * Complex.I))‖ ≤ _
    simp only [norm_mul, K, Circle.norm_coe, Complex.norm_I, mul_one, one_mul,
      Complex.norm_real, P, norm_mul, Real.norm_of_nonneg hnonneg]
    calc
      _ ≤ ‖a y‖ * ((2 * Real.pi) * ∑ i, C i * ‖k i y‖) := by gcongr
      _ = bound y := by
        simp only [bound, ← mul_assoc, Finset.mul_sum]
        ring_nf
  have hK0 (y : Y) : K 0 y = 1 := by simp [K, P, hz0]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun s y ↦ a y * K s y)
    (F' := D) (s := Icc (-1 : ℝ) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (.of_forall fun s ↦ ha.1.mul (hK s)) (by simpa only [hK0, mul_one] using ha)
    (ha.1.mul ((hK 0).mul ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hP _)).mul_const _)))
    (.of_forall fun y s hs ↦ hle s hs y) hbound (.of_forall fun y s _ ↦ hder s y)
  simpa only [D, hK0, one_mul] using h

end RiemannMasullo
