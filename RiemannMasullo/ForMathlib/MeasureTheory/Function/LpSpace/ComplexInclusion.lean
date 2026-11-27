module

public import Mathlib.MeasureTheory.Function.L2Space

/-! # Complex-linear inclusion of `L²` spaces for ordered measures -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace RiemannMasullo.WeakCardinal

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

private theorem measure_le_one_smul (h : ν ≤ μ) : ν ≤ (1 : ℝ≥0∞) • μ := by
  simpa only [one_smul] using h

private def realLpInclusion (h : ν ≤ μ) : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 ν :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h)

private theorem realLpInclusion_coeFn (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    (realLpInclusion h f : X → ℂ) =ᵐ[ν] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h) f

/-- The natural complex-linear map obtained by retaining an `L²` representative and passing
to the smaller measure. -/
@[no_expose] def complexLpInclusionOfMeasureLE (h : ν ≤ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν where
  toFun := realLpInclusion h
  map_add' := (realLpInclusion h).map_add
  map_smul' c f := Lp.ext <| (realLpInclusion_coeFn h (c • f)).trans <|
    Filter.EventuallyEq.trans (ae_mono h (Lp.coeFn_smul c f)) <|
      ((realLpInclusion_coeFn h f).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c _).symm
  cont := (realLpInclusion h).continuous

/-- The image has the same representative almost everywhere for the smaller measure. -/
theorem complexLpInclusionOfMeasureLE_coeFn (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    (complexLpInclusionOfMeasureLE h f : X → ℂ) =ᵐ[ν] f := realLpInclusion_coeFn h f

/-- Passing to a smaller measure has operator norm at most one. -/
theorem complexLpInclusionOfMeasureLE_norm_le (h : ν ≤ μ) : ‖complexLpInclusionOfMeasureLE h‖ ≤ 1 := by
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ)]
  change ‖realLpInclusion h‖ ≤ 1
  simpa [realLpInclusion] using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2)
    ENNReal.one_ne_top (measure_le_one_smul h)

/-- Equivalence of the null sets makes the inclusion injective. -/
theorem complexLpInclusionOfMeasureLE_injective (h : ν ≤ μ) (hac : μ ≪ ν) :
    Function.Injective (complexLpInclusionOfMeasureLE h) := by
  intro f g he
  apply Lp.ext
  exact hac.ae_eq ((complexLpInclusionOfMeasureLE_coeFn h f).symm.trans
    (he ▸ complexLpInclusionOfMeasureLE_coeFn h g))

end RiemannMasullo.WeakCardinal
