module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.RadiusSixBessel
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.Cutoff

/-! # Radius-six comparison with the computed finite positive quadratic form

For a finite list exhausting all full sites in the closed radius-six interval, the Gram
solution determines the local minimum. A centered moment and the specific radius-six multiplier
at that moment supply the admissible full competitor. The resulting weak comparison involves the
computed finite Gram form itself.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace Matrix

namespace RiemannMasullo.WeakCardinal

/-- A solution of the genuine finite interpolation system determines a unique full minimum.
Its weak norm lies within the radius-six relative error of the computed finite quadratic form.
The two remaining analytic estimates are tested on the finite cardinal and its centered moment. -/
theorem exists_fullMinimum_radiusSix_gram {ι : Type*} [Fintype ι] {θ w : ℝ}
    (hθ : 1 < θ) (hθ' : θ ≤ 3/2) (Z : Set ℝ) (site : ι → ℝ)
    (hsite : Set.range site = radiusSixSites Z w) (c : ι → ℂ)
    (hsolve : (gramMatrix θ site) *ᵥ c = fun i ↦ if site i = w then 1 else 0)
    (u v : Lp ℂ 2 (sobolevMeasure θ)) :
    let k := evaluationVector θ (by linarith)
    let hE := ∑ i, c i • k (site i)
    (∀ x ∈ Z, ⟪k x, u⟫_ℂ = ((x-w : ℝ) : ℂ) * ⟪k x, hE⟫_ℂ) →
    (∀ x ∈ Z, ⟪k x, v⟫_ℂ = (scaledCutoffQuotient w 6 x : ℂ) * ⟪k x, u⟫_ℂ) →
    ‖u‖ ≤ Real.sqrt (θ*(2*θ-1)) * ‖besselWeakening θ hE‖ →
    ‖v‖ ≤ (13/48) * ‖u‖ →
    let W := (star c ⬝ᵥ (gramMatrix (θ+1) site) *ᵥ c).re
    ∃ hZ : Lp ℂ 2 (sobolevMeasure θ), IsMinimumCardinal k Z w hZ ∧
      (∀ f, IsMinimumCardinal k Z w f → f = hZ) ∧
      ‖hZ-hE‖ ≤ radiusSixError * Real.sqrt W ∧
      (1-radiusSixError) * Real.sqrt W ≤ ‖besselWeakening θ hZ‖ ∧
      ‖besselWeakening θ hZ‖ ≤ (1+radiusSixError) * Real.sqrt W := by
  intro k hE hu hv hm hA W
  have hlocal : IsMinimumCardinal k (radiusSixSites Z w) w hE := by
    rw [← hsite]
    exact isMinimumCardinal_of_gram_solution θ (by linarith) site w c hsolve
  have hweak : Real.sqrt W = ‖besselWeakening θ hE‖ := by
    rw [show W = ‖besselWeakening θ hE‖ ^ 2 from
      (besselWeakening_sum_norm_sq θ (by linarith) site c).symm]
    exact Real.sqrt_sq (norm_nonneg _)
  obtain ⟨hZ, hfull, hd, hl, hr⟩ := exists_fullMinimum_radiusSix hθ hθ' (besselWeakening θ)
    ((besselWeakening θ).lipschitzWith_of_opNorm_le (besselWeakening_norm_le θ))
    hlocal (scaledCutoffQuotient w 6) (fun _ hx ↦
      scaledCutoffQuotient_mul_sub_of_le_abs (by norm_num) hx.le) hu hv hm hA
  rw [hweak]
  exact ⟨hZ, hfull, fun _ hf ↦ hf.unique hfull, hd, hl, hr⟩

/-- Direct form for the computed inverse column. The two pointwise hypotheses are written with
the actual inverse angular Fourier integral; all sites in the closed window occur exactly once. -/
theorem exists_fullMinimum_radiusSix_inverseGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2) (Z : Set ℝ) (site : ι → ℝ)
    (hinj : Function.Injective site) (j : ι) (hsite : Set.range site = radiusSixSites Z (site j))
    (u v : Lp ℂ 2 (sobolevMeasure θ)) :
    let w := site j
    let c (i : ι) := (gramMatrix θ site)⁻¹ i j
    let k := evaluationVector θ (by linarith)
    let hE := ∑ i, c i • k (site i)
    let F (f : Lp ℂ 2 (sobolevMeasure θ)) (x : ℝ) := ∫ ξ, phase x ξ * f ξ ∂angularMeasure
    (∀ x ∈ Z, F u x = ((x-w : ℝ) : ℂ) * F hE x) →
    (∀ x ∈ Z, F v x = (scaledCutoffQuotient w 6 x : ℂ) * F u x) →
    ‖u‖ ≤ Real.sqrt (θ*(2*θ-1)) * ‖besselWeakening θ hE‖ →
    ‖v‖ ≤ (13/48) * ‖u‖ →
    let W := (star c ⬝ᵥ (gramMatrix (θ+1) site) *ᵥ c).re
    ∃ hZ : Lp ℂ 2 (sobolevMeasure θ), IsMinimumCardinal k Z w hZ ∧
      (∀ f, IsMinimumCardinal k Z w f → f = hZ) ∧
      ‖hZ-hE‖ ≤ radiusSixError * Real.sqrt W ∧
      (1-radiusSixError) * Real.sqrt W ≤ ‖besselWeakening θ hZ‖ ∧
      ‖besselWeakening θ hZ‖ ≤ (1+radiusSixError) * Real.sqrt W := by
  intro w c k hE F hu hv hm hA W
  have hsolve : (gramMatrix θ site) *ᵥ c = fun i ↦ if site i = w then 1 else 0 := by
    funext i
    exact gramMatrix_mulVec_inverse_column θ (by linarith) hinj i j
  exact exists_fullMinimum_radiusSix_gram hθ hθ' Z site hsite c hsolve u v
    (fun x hx ↦ by simpa only [k, evaluationVector_inner] using hu x hx)
    (fun x hx ↦ by simpa only [k, evaluationVector_inner] using hv x hx) hm hA

end RiemannMasullo.WeakCardinal
