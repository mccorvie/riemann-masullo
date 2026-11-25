module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.BesselWeightInterpolation
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.RadiusSixCutoffLocalization
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.CutoffAngular

/-! # The unconditional radius-six Bessel comparison for minimum cardinal interpolation -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix

namespace RiemannMasullo.WeakCardinal

private theorem radiusSixEndpoint (w : ℝ) :
    BesselEndpointBound (angularScaledCutoffQuotient w (R := 6) (by norm_num)) (13/48) := by
  intro f j hj
  simpa only [Complex.real_smul] using
    angularScaledCutoffQuotient_full_endpoint_six w f j (by simpa only [Complex.real_smul] using hj)

/-- On the full closed range of orders from zero to two, the radius-six cutoff has
operator norm at most 13/48 and restricts the genuine unweighted Fourier multiplier. -/
theorem exists_radiusSixBesselBound (r : ℝ) (hr₀ : 0 ≤ r) (hr₂ : r ≤ 2) (w : ℝ) :
    ∃ A : Lp ℂ 2 (sobolevMeasure r) →L[ℂ] Lp ℂ 2 (sobolevMeasure r),
      ‖A‖ ≤ 13/48 ∧ ∀ f, besselToAngular r hr₀ (A f) =
        angularScaledCutoffQuotient w (R := 6) (by norm_num) (besselToAngular r hr₀ f) :=
  exists_besselMultiplier_of_endpoints r hr₀ hr₂ _ (by norm_num)
    ((angularScaledCutoffQuotient_norm_le w (R := 6) (by norm_num)).trans (by norm_num))
    (radiusSixEndpoint w)

/-- Above the evaluation threshold, the physical radius-six cutoff acts on the fractional
Bessel space. Its norm is at most 13/48, and its inverse Fourier evaluation
is pointwise multiplication by the explicit scaled quotient. -/
theorem exists_radiusSixBesselMultiplier (r : ℝ) (hr : 1/2 < r) (hr₂ : r ≤ 2) (w : ℝ) :
    ∃ A : Lp ℂ 2 (sobolevMeasure r) →L[ℂ] Lp ℂ 2 (sobolevMeasure r), ‖A‖ ≤ 13/48 ∧
      ∀ (f : Lp ℂ 2 (sobolevMeasure r)) x,
        (∫ ξ, phase x ξ * A f ξ ∂angularMeasure) =
          (scaledCutoffQuotient w 6 x : ℂ) * ∫ ξ, phase x ξ * f ξ ∂angularMeasure := by
  apply exists_besselPhysicalMultiplier_of_endpoints r hr hr₂
    (angularScaledCutoffQuotient w (R := 6) (by norm_num)) _ (by norm_num)
    ((angularScaledCutoffQuotient_norm_le w (R := 6) (by norm_num)).trans (by norm_num))
    (radiusSixEndpoint w)
  intro f hf hout x
  simpa only [Complex.real_smul] using
    angularInverse_scaledCutoffQuotient w (R := 6) (by norm_num) f hf hout x

/-- The full minimum cardinal exists uniquely and its genuine weak Bessel norm is bracketed
by the finite inverse-Gram energy. The finite interpolation sites are all sites at distance
at most six, including both endpoints of the closed radius-six interval. -/
theorem exists_fullMinimum_radiusSix_bessel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2) (Z : Set ℝ) (site : ι → ℝ)
    (hinj : Function.Injective site) (j : ι) (hsite : Set.range site = radiusSixSites Z (site j)) :
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
  obtain ⟨A,hA,hmul⟩ := exists_radiusSixBesselMultiplier θ (by linarith) (by linarith) (site j)
  exact exists_fullMinimum_radiusSix_of_multiplier hθ hθ' Z site hinj j hsite A hA
    (fun f x _ ↦ hmul f x)

end RiemannMasullo.WeakCardinal
