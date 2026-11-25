module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.LpSpace.ComplexInclusion

/-! # The finite weak cardinal in the original quotient norm -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace Matrix ENNReal NNReal

namespace RiemannMasullo.WeakCardinal

/-- Lowering the Sobolev order by two divides the physical squared density by
`1 + (logNorm x)^2`. This gives a norm-one bound on every fixed strip. -/
theorem intervalSobolevMeasure_sub_two_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (l r s : ℝ) :
    intervalSobolevMeasure μ logNorm l r (s-2) ≤ intervalSobolevMeasure μ logNorm l r s := by
  apply withDensity_mono (.of_forall fun x ↦ ?_)
  apply ENNReal.ofReal_le_ofReal
  change max _ _ * (1+(logNorm x)^2)^((s-2)/2) ≤ max _ _ * (1+(logNorm x)^2)^(s/2)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (logNorm x)])
    (by linarith)) ((Real.exp_pos _).le.trans (le_max_left _ _))

/-- Restriction of the original weighted function to the physical space of one lower Bessel order. -/
def intervalSobolevWeakening {A : Type*} [MeasurableSpace A] (μ : Measure A) (logNorm : A → ℝ)
    (l r s : ℝ) : CompactIntervalSobolev μ logNorm l r s →L[ℂ]
      CompactIntervalSobolev μ logNorm l r (s-2) :=
  complexLpInclusionOfMeasureLE (intervalSobolevMeasure_sub_two_le μ logNorm l r s)

theorem intervalSobolevWeakening_coeFn {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (l r s : ℝ) (u : CompactIntervalSobolev μ logNorm l r s) :
    (intervalSobolevWeakening μ logNorm l r s u : A → ℂ) =ᵐ[intervalSobolevMeasure μ logNorm l r (s-2)]
      (u : A → ℂ) :=
  complexLpInclusionOfMeasureLE_coeFn _ u

theorem intervalSobolevWeakening_norm_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (l r s : ℝ) : ‖intervalSobolevWeakening μ logNorm l r s‖ ≤ 1 :=
  complexLpInclusionOfMeasureLE_norm_le _

end RiemannMasullo.WeakCardinal
