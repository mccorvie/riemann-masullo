module

public import RiemannMasullo.AppB_AnalyticNT.HeckeLogReference
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_BoundaryHeckeGreen

/-! # The finite ideal logarithmic measurement of the right-hand Green sum

The boundary identity supplies absolute integrability of the ordinary critical-line
logarithm. Its Green sum is therefore the limit of the norm-ordered finite tables.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField
open scoped NNReal Topology

namespace RiemannMasullo.LogQuadrature

open HalfPlaneJensen HeckeBoundaryGreen HeckeHalfPlaneJensen PolynomialIdealSamples

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF

private theorem weightedLog_eq (L : ℂ → ℂ) :
    weightedLog L = fun t ↦ poissonWeight t * Real.log ‖L (point t)‖ := by
  funext t
  have hp : (1/2 : ℂ) + (t : ℂ) * I = point t := by
    apply Complex.ext <;> simp [point, Complex.mul_re, Complex.mul_im]
  simp only [weightedLog, poissonWeight, hp]

/-- The fully finite ideal measurement converges to the genuine, pole-corrected boundary
mean for every normalized character. -/
theorem tendsto_finiteLogDifference_criticalLogDifference (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    Tendsto (finiteLogDifference χ) atTop (𝓝 (criticalLogDifference χ)) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hlog := (integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
  rw [weightedLog_eq] at hlog
  simpa only [criticalLogDifference, weightedLog_eq] using
    tendsto_finiteLogDifference τ hτ χ hχ hlog

/-- All right-hand completed divisor sites, with their multiplicities, sum to the limit
of the finite ideal measurement at two. -/
theorem hasSum_green_limit_finiteLogDifference (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    HasSum (fun z : RightSite χ ↦ (order χ z.val : ℝ) * greenKernel z.val)
      (limUnder atTop (finiteLogDifference χ)) := by
  rw [(tendsto_finiteLogDifference_criticalLogDifference τ hτ χ hχ).limUnder_eq]
  exact hasSum_green_criticalLogDifference τ hτ χ hχ

end RiemannMasullo.LogQuadrature
