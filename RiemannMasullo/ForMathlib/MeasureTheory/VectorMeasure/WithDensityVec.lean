module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

open Function Set MeasureTheory Filter Topology
open scoped ENNReal

namespace RiemannMasullo

/-- Integrating a bounded complex test function against a complex density amounts to
multiplying by the density inside the Bochner integral. -/
theorem integral_withDensityᵥ_mul {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {w g : Y → ℂ} (hw : Integrable w ν) (hg : StronglyMeasurable g)
    {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ y, ‖g y‖ ≤ C) :
    (ν.withDensityᵥ w).integral g (ContinuousLinearMap.mul ℝ ℂ) = ∫ y, g y * w y ∂ν := by
  let μ := ν.withDensityᵥ w
  let B := ContinuousLinearMap.mul ℝ ℂ
  have : IsFiniteMeasure μ.variation := ⟨by
    rw [show μ.variation = _ from Measure.variation_withDensityᵥ hw,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hw.2⟩
  have hsint (s : SimpleFunc Y ℂ) : Integrable (fun y ↦ s y * w y) ν := by
    obtain ⟨M, hM⟩ := (s.finite_range.image norm).bddAbove
    exact (hw.norm.const_mul M).mono (s.stronglyMeasurable.aestronglyMeasurable.mul
      hw.aestronglyMeasurable) (ae_of_all _ fun y ↦ by
        rw [norm_mul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (hM ⟨_, mem_range_self y, rfl⟩) (norm_nonneg _)).trans
          (le_abs_self _))
  -- Check indicators first, then extend by additivity to all simple functions.
  have hs (s : SimpleFunc Y ℂ) : μ.integral s B = ∫ y, s y * w y ∂ν := by
    induction s using SimpleFunc.induction with
    | const c ht =>
      rename_i t
      change μ.integral (t.indicator (fun _ ↦ c)) B = ∫ y, t.indicator (fun _ ↦ c) y * w y ∂ν
      rw [VectorMeasure.integral_indicator_const c ht, show μ t = _ from withDensityᵥ_apply hw ht]
      simp_rw [← Set.indicator_mul_left, integral_indicator ht, integral_const_mul]
      rfl
    | add h h₁ h₂ =>
      rename_i s t
      simp only [FunLike.coe_add, Pi.add_apply, add_mul]
      rw [VectorMeasure.integral_add (μ := μ) (B := B) s.integrable_of_isFiniteMeasure
        t.integrable_of_isFiniteMeasure, integral_add (hsint s) (hsint t), h₁, h₂]
  -- Use the same bounded simple approximations for both integrals.
  let s := hg.approxBounded C
  have hb := hg.norm_approxBounded_le hC
  have hl (y : Y) := hg.tendsto_approxBounded_of_norm_le (hgb y)
  apply tendsto_nhds_unique (VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := μ) (B := B) (f := g) (fun _ ↦ C)
    (fun n ↦ (s n).stronglyMeasurable.aestronglyMeasurable) (integrable_const _)
    (fun n ↦ ae_of_all _ (hb n)) (ae_of_all _ hl))
  simp_rw [hs]
  apply tendsto_integral_of_dominated_convergence (fun y ↦ C * ‖w y‖)
    (fun n ↦ (s n).stronglyMeasurable.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (hw.norm.const_mul C)
  · exact fun n ↦ ae_of_all _ fun y ↦ by
      rw [Pi.mul_apply, norm_mul]; exact mul_le_mul_of_nonneg_right (hb n y) (norm_nonneg _)
  · exact ae_of_all _ fun y ↦ (hl y).mul_const _

end RiemannMasullo
