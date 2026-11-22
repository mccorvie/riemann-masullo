module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a

/-!
# Chapter 12.1.1: statements that are false as printed
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Theorem 12.1.1.2(2), p. 499. For every compactly supported continuous
multiplier in the target variable, smoothening the multiplied kernel gives the
pointwise product of the multiplier with the smoothened kernel. -/
def Printed.dSequenceKernelSmoothening_mul_continuous : Prop :=
  ∀ {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
    (U : ℕ → Set G) (f : G → ℝ≥0),
    IsDPrimeSequence μ U → (∀ n, MeasurableSet (U n)) →
    Continuous f → (∀ x, 0 < f x) → ν = μ.withDensity (fun x ↦ ↑(f x)) →
    ∀ (k : Lp ℂ 2 (ν.prod ν)), IsNuclearOperator (integralKernelOperator ν k).val →
    ∀ (κ : G × G → ℂ), κ =ᵐ[ν.prod ν] k →
    ∀ (ρ : G → ℂ), Continuous ρ → HasCompactSupport ρ →
    dSequenceKernelSmoothening μ U (fun p ↦ ρ p.1 * κ p) =
      fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p

/-- Paper: Theorem 12.1.1.2(2), p. 499. On the additive real line use Lebesgue
measure, density one, and the intervals `[−2⁻ⁿ, 2⁻ⁿ]`. Let `χ(t) = max(0, min(1, 2 − |t|))`,
`g(t) = χ(t) sgn(t) |t|⁻¹⁄⁴` with `g(0) = 0`, and use the rank-one kernel
`k(x,y) = g(x) χ(y)`. The continuous compactly supported multiplier
`ρ(t) = χ(t) sgn(t) |t|¹⁄⁴` gives a weighted kernel equal to one almost
everywhere on the averaging squares at the origin. The unweighted kernel
averages are zero by oddness, so the asserted pointwise identity gives
`1 = 0` at the regular point `(0,0)`. -/
theorem Printed.dSequenceKernelSmoothening_mul_continuous_false :
    ¬ Printed.dSequenceKernelSmoothening_mul_continuous := by sorry

end RiemannMasullo
