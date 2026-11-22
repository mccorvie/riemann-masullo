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
  intro h
  have hr : StrictAnti fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1) := by
    intro m n hmn
    have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
    have := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < (m : ℝ) + 1)
      (by linarith : (m : ℝ) + 1 < (n : ℝ) + 1)
    linarith
  have h1 := h 1 (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) hr (by norm_num)
  dsimp only at h1
  obtain ⟨⟨⟨-, hB⟩, -⟩, -⟩ := h1
  -- The open unit ball is a neighborhood of the identity that contains no member.
  let W : Set (Multiplicative (EuclideanSpace ℝ (Fin 1))) :=
    Multiplicative.toAdd ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1
  have hW : W ∈ nhds (1 : Multiplicative (EuclideanSpace ℝ (Fin 1))) :=
    (Metric.isOpen_ball.preimage continuous_toAdd).mem_nhds (by simp)
  obtain ⟨k, hk⟩ := hB W hW
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin 1)) zero_le_one
  have hmem : Multiplicative.ofAdd v ∈ W := hk (by
    show Multiplicative.toAdd (Multiplicative.ofAdd v) ∈ Metric.closedBall 0 _
    rw [toAdd_ofAdd, mem_closedBall_zero_iff, hv]
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith)
  have : ‖v‖ < 1 := by simpa [W] using hmem
  linarith

end RiemannMasullo
