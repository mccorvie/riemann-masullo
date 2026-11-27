module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.RadiusSixGramLocalization
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FirstMomentBessel

/-! This finite-window criterion for #7406 uses k-ieren’s first-moment identity.

 # The weak radius-six comparison from the physical Sobolev multiplier

The centered first moment of the literal inverse Gram column exists with the required
Bessel norm bound. Consequently one bounded multiplication operator on the order-`θ`
space suffices to localize the full minimum.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix

namespace RiemannMasullo.WeakCardinal

/-- Compare the true full cardinal to the numerical finite positive form. The sole analytic
input is the physical cutoff multiplier at order `θ`, with its norm and its action on
inverse Fourier evaluations. -/
theorem exists_fullMinimum_radiusSix_of_multiplier {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2) (Z : Set ℝ) (site : ι → ℝ)
    (hinj : Function.Injective site) (j : ι) (hsite : Set.range site = radiusSixSites Z (site j))
    (A : Lp ℂ 2 (sobolevMeasure θ) →L[ℂ] Lp ℂ 2 (sobolevMeasure θ)) (hA : ‖A‖ ≤ 13/48)
    (hmul : ∀ (f : Lp ℂ 2 (sobolevMeasure θ)) x, x ∈ Z →
      (∫ ξ, phase x ξ * A f ξ ∂angularMeasure) =
        (scaledCutoffQuotient (site j) 6 x : ℂ) * (∫ ξ, phase x ξ * f ξ ∂angularMeasure)) :
    let w := site j
    let c (i : ι) := (gramMatrix θ site)⁻¹ i j
    let k := evaluationVector θ (by linarith)
    let hE := ∑ i, c i • k (site i)
    let W := (star c ⬝ᵥ (gramMatrix (θ+1) site) *ᵥ c).re
    ∃ hZ : Lp ℂ 2 (sobolevMeasure θ), IsMinimumCardinal k Z w hZ ∧
      (∀ f, IsMinimumCardinal k Z w f → f = hZ) ∧
      ‖hZ-hE‖ ≤ radiusSixError * Real.sqrt W ∧
      (1-radiusSixError) * Real.sqrt W ≤ ‖besselWeakening θ hZ‖ ∧
      ‖besselWeakening θ hZ‖ ≤ (1+radiusSixError) * Real.sqrt W := by
  intro w c k hE W
  obtain ⟨u, hu, hfirst⟩ := exists_firstMoment_inverseGram hθ site hinj j
  exact exists_fullMinimum_radiusSix_inverseGram hθ hθ' Z site hinj j hsite u (A u)
    (fun x _ ↦ hu x) (fun x hx ↦ hmul u x hx) hfirst
    ((A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u)))

end RiemannMasullo.WeakCardinal
