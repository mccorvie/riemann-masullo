module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # §12.1.1: the printed Euclidean D′-sequence example -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace RiemannMasullo

/-- Paper: Example after Definition 12.1.1.1, p. 498. As printed: In every Euclidean
dimension, a strictly decreasing real sequence whose first term is positive gives
symmetric Borel D′-sequences of closed balls and cubes with those radii.
`IsDPrimeSequence` supplies the hypothesis used in §12.1.1. See ERRATA F171. -/
def Printed.euclideanBallCube_isDPrimeSequence : Prop :=
  ∀ (N : ℕ) (r : ℕ → ℝ), StrictAnti r → 0 < r 0 →
    let E := EuclideanSpace ℝ (Fin N)
    let μ : Measure (Multiplicative E) := (volume : Measure E)
    let B (n : ℕ) : Set (Multiplicative E) :=
      Multiplicative.toAdd ⁻¹' Metric.closedBall (0 : E) (r n)
    let Q (n : ℕ) : Set (Multiplicative E) :=
      {x | ∀ i : Fin N, Multiplicative.toAdd x i ∈ Icc (-r n) (r n)}
    (IsDPrimeSequence μ B ∧ ∀ n, MeasurableSet (B n) ∧ (B n)⁻¹ = B n) ∧
      (IsDPrimeSequence μ Q ∧ ∀ n, MeasurableSet (Q n) ∧ (Q n)⁻¹ = Q n)

/-- Paper: Example after Definition 12.1.1.1, p. 498. In dimension one take
rₙ = 1 + 2⁻ⁿ. Every ball and cube contains the point with coordinate 1, so
none is contained in the neighborhood (−1, 1) of zero. -/
theorem Printed.euclideanBallCube_isDPrimeSequence_false :
    ¬ Printed.euclideanBallCube_isDPrimeSequence := by
  sorry

end RiemannMasullo
