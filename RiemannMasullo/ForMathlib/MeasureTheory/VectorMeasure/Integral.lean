module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory.VectorMeasure

/-- Integrating against a complex density measure multiplies the integrand by the density. -/
theorem integral_withDensityᵥ_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℂ} (hg : Integrable g μ) (hgm : Measurable g)
    (hf : (μ.withDensityᵥ g).Integrable f) :
    (μ.withDensityᵥ g).integral f (ContinuousLinearMap.mul ℝ ℂ) = ∫ x, f x * g x ∂μ := by
  let ν := (μ.withDensityᵥ g).variation
  have hν : ν = μ.withDensity (fun x ↦ (‖g x‖₊ : ℝ≥0∞)) := μ.variation_withDensityᵥ hg
  let u (x : X) : ℂ := ‖g x‖⁻¹ • g x
  have hu : Measurable u := hgm.norm.inv.smul hgm
  have hbound (x : X) : ‖u x‖ ≤ 1 := by
    by_cases hx : g x = 0
    · simp [u, hx]
    · simp [u, norm_ne_zero_iff.mpr hx]
  have hscale (v : X → ℂ) (x : X) : ‖g x‖₊ • (v x * u x) = v x * g x := by
    by_cases hx : g x = 0
    · simp [hx]
    · simp only [u, NNReal.smul_def, coe_nnNorm]
      rw [← mul_smul_comm, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]
  have hconvert (v : X → ℂ) : (∫ x, v x * u x ∂ν) = ∫ x, v x * g x ∂μ := by
    rw [hν, integral_withDensity_eq_integral_smul hgm.nnNorm]
    simp_rw [hscale]
  rw [← hconvert]
  have hmul {v : X → ℂ} (hv : Integrable v ν) : Integrable (fun x ↦ v x * u x) ν :=
    hv.mul_bdd hu.aestronglyMeasurable (ae_of_all _ hbound)
  refine Integrable.induction
    (μ := ν) (P := fun v ↦ (μ.withDensityᵥ g).integral v (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ x, v x * u x ∂ν) ?_ ?_ ?_ ?_ hf
  · intro c s hs hsν
    have : IsFiniteMeasure (ν.restrict s) := ⟨by simpa [Measure.restrict_apply' hs] using hsν⟩
    rw [integral_indicator_const c hs, withDensityᵥ_apply hg hs, hconvert]
    simp_rw [← Set.indicator_mul_left, MeasureTheory.integral_indicator hs]
    exact (integral_const_mul c g).symm
  · intro v w _ hv hw hv' hw'
    simp only [Pi.add_apply, add_mul]
    rw [VectorMeasure.integral_add hv hw, MeasureTheory.integral_add (hmul hv) (hmul hw), hv', hw']
  · refine isClosed_eq VectorMeasure.continuous_integral ?_
    apply (show LipschitzWith 1 (fun v : X →₁[ν] ℂ ↦ ∫ x, v x * u x ∂ν) from ?_).continuous
    intro v w
    rw [ENNReal.coe_one, one_mul, Lp.edist_def,
      eLpNorm_one_eq_lintegral_eNorm ((Lp.aestronglyMeasurable v).sub (Lp.aestronglyMeasurable w))]
    refine (MeasureTheory.edist_integral_le_lintegral_edist
      (hmul (L1.integrable_coeFn v)) (hmul (L1.integrable_coeFn w))).trans ?_
    apply lintegral_mono
    intro x
    simp only [eDist_eq_eNorm_sub, ← sub_mul, eNorm_mul, Pi.sub_apply]
    exact mul_le_of_le_one_right' (by simpa using ENNReal.ofReal_le_ofReal (hbound x))
  · intro v w hvw _ hv
    rw [← VectorMeasure.integral_congr_ae hvw, hv]
    exact MeasureTheory.integral_congr_ae (hvw.mono fun x hx ↦ congrArg (· * u x) hx)

end MeasureTheory.VectorMeasure
