module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.DyadicTailMoments
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePrimeHardy
public import RiemannMasullo.AppB_AnalyticNT.HeckeFiniteLogGreen
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Tactic

/-! # Unconditional second moments and signed-square criteria for ordinary Hecke data -/

@[expose] public noncomputable section
open MeasureTheory Complex Filter Function NumberField AddCircle Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeLaguerre
open LogQuadrature HeckeHalfPlaneJensen BoundaryHardy PolynomialIdealSamples
variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- Every natural absolute moment of the true critical logarithm exists under harmonic measure from two. -/
theorem integrable_criticalLog_abs_pow (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (p : ℕ) :
    Integrable (fun t : ℝ ↦ |Real.log ‖(finiteHeckeL_exists_continuation χ).choose (point t)‖|^p)
      poissonMeasure := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hdiff := (hecke_critical_deriv_polynomial τ hτ χ hχ _ hL he).1
  obtain ⟨A,hA,K,hK,h⟩ := criticalLog_dyadic_tail τ hτ χ hχ
  exact integrable_abs_pow_of_geometric_sq poissonMeasure (Real.measurable_log.comp hdiff.continuous.norm.measurable)
    hA hK.le (by norm_num) (by norm_num) h p

/-- The genuine finite continuation has a square-integrable critical logarithm for Haar probability. -/
theorem criticalTrace_memLp (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) : MemLp (criticalTrace χ) 2 haarAddCircle := by
  apply criticalTrace_memLp_of_weighted_sq τ hτ χ hχ
  have hi := (poisson_integrable_iff _).mp (integrable_criticalLog_abs_pow τ hτ χ hχ 2)
  have hp (t : ℝ) : (1/2:ℂ)+(t:ℂ)*I = point t := by
    apply Complex.ext <;> simp [point,Complex.mul_re,Complex.mul_im]
  simpa only [poissonWeight,sq_abs,hp] using hi

/-- Both genuine Parseval identities for any normalized character whose right-hand site set is empty. -/
theorem hardy_identities_of_empty (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hR : IsEmpty (RightSite χ)) :
    HasSum (fun n ↦ ‖logCoefficient χ n‖^2) (2*ProbabilityTheory.variance (criticalTrace χ) haarAddCircle) ∧
    HasSum (fun n : ℕ ↦ (measuredCoeff χ (n+1)/(n+1:ℝ))^2)
      (2*ProbabilityTheory.variance (evenPart (criticalTrace χ)) haarAddCircle) :=
  ⟨hasSum_logCoefficient_sq τ hτ χ hχ hR (criticalTrace_memLp τ hτ χ hχ),
   hasSum_measuredCoeff_div_sq τ hτ χ hχ hR (criticalTrace_memLp τ hτ χ hχ)⟩

/-- For either fixed sign, bounded partial sums of the true square energies characterize critical confinement. -/
theorem central_iff_bounded_true_energy (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range N, signedSquare (measuredCoeff χ) negative n ≤ C :=
  (central_iff_summable_signedSquare τ hτ χ hχ (criticalTrace_memLp τ hτ χ hχ) negative).trans
    (summable_signedSquare_iff_bounded _ _)

/-- The finite prime-power measurements at norm cutoff `100^n` also characterize critical confinement. -/
theorem central_iff_bounded_raw100_energy (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range N, signedSquare (fun j ↦ finiteMoment χ j (100^j)) negative n ≤ C :=
  central_iff_bounded_raw100_signedSquare τ hτ χ hχ (criticalTrace_memLp τ hτ χ hχ) negative

/-- The measured Cauchy second moment gives an exact arithmetic ceiling for each finite prefix
criterion, with the same ceiling for both orientations. -/
theorem central_iff_prefix_le_cauchy_second_moment (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔ ∀ N : ℕ,
      ∑ n ∈ Finset.range N, signedSquare (measuredCoeff χ) negative n ≤
      2*∫ t : ℝ, ((3/2)/(Real.pi*((3/2)^2+t^2))) *
        (Real.log ‖(finiteHeckeL_exists_continuation χ).choose ((1/2:ℂ)+t*I)‖)^2 :=
  ⟨fun hc ↦ signedSquare_prefix_le_second_moment τ hτ χ hχ ((isEmpty_rightSite_iff_central χ).mpr hc)
    (criticalTrace_memLp τ hτ χ hχ) negative, fun h ↦ (central_iff_bounded_true_energy τ hτ χ hχ negative).mpr ⟨_,h⟩⟩

/-- An explicit ceiling also suffices for the finite raw prime-power version at norm cutoff `100^n`. -/
theorem central_iff_raw100_prefix_le_cauchy_second_moment (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔ ∀ N : ℕ,
      ∑ n ∈ Finset.range N, signedSquare (fun j ↦ finiteMoment χ j (100^j)) negative n ≤
      4*(∫ t : ℝ, ((3/2)/(Real.pi*((3/2)^2+t^2))) *
        (Real.log ‖(finiteHeckeL_exists_continuation χ).choose ((1/2:ℂ)+t*I)‖)^2) +
        (8/3)*(Module.finrank ℚ F:ℝ)^2 :=
  ⟨fun hc ↦ raw100_prefix_le_second_moment τ hτ χ hχ ((isEmpty_rightSite_iff_central χ).mpr hc)
    (criticalTrace_memLp τ hτ χ hχ) negative, fun h ↦ (central_iff_bounded_raw100_energy τ hτ χ hχ negative).mpr ⟨_,h⟩⟩

end RiemannMasullo.HeckeLaguerre
