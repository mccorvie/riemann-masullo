module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5b
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Appendix A.5.3–A.5.4: statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Pointwise

/-- Paper: Theorem A.5.3.1, p. 579.
As printed: let `B` be Haar-measurable for a regular Haar measure, with finite enlargement
mass. If each point of `B` centers an allowed translate of a D-sequence, finitely many disjoint
allowed translates centered in `B` have total mass strictly greater than the mass of `B`
divided by the doubling constant.
The enlargement mass uses the outer-measure reading of Remark A.5.3.2. See ERRATA F221 and
`exists_disjoint_dSequence_translates`, which assumes `B` is nonempty. -/
def Printed.exists_disjoint_dSequence_translates : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (U : ℕ → Set G) (C : ℝ),
    IsDSequence μ U → 0 < C →
    (∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k)) →
    ∀ (F : Set (Set G)), F ⊆ {V | ∃ (x : G) (k : ℕ), V = x • U k} →
    ∀ (B : Set G), NullMeasurableSet B μ → μ (B * U 0) < ∞ →
    (∀ x ∈ B, ∃ k, x • U k ∈ F) →
    ∃ (n : ℕ) (x : Fin n → G) (k : Fin n → ℕ),
      (∀ i, x i ∈ B ∧ x i • U (k i) ∈ F) ∧
      Pairwise (fun i j ↦ Disjoint (x i • U (k i)) (x j • U (k j))) ∧
      μ B / ENNReal.ofReal C < ∑ i, μ (U (k i))

/-- Paper: Theorem A.5.3.1, p. 579.
Take the trivial discrete group `Unit` with counting Haar measure, `U k = {1}` for all `k`,
`C = 2`, `F = ∅` and `B = ∅`. The hypotheses hold, and there can be no selected center.
The only possible family is empty, whose mass would have to be strictly above zero. -/
theorem Printed.exists_disjoint_dSequence_translates_false :
    ¬ Printed.exists_disjoint_dSequence_translates := by
  sorry

/-- Paper: Theorem A.5.4.1(1), p. 582.
As printed: on every second-countable Hausdorff locally compact abelian group with Haar
measure, every locally integrable complex function has a uniformly continuous average at
each index of any D′-sequence. The averaging operator is `dSequenceAverage`.
See ERRATA F222. -/
def Printed.uniformContinuous_dSequenceAverage : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (U : ℕ → Set G) (f : G → ℂ), IsDPrimeSequence μ U → LocallyIntegrable f μ →
    letI _printedSec5bUniformSpace : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    ∀ k, UniformContinuous (dSequenceAverage μ (U k) f)

/-- Paper: Theorem A.5.4.1(1), p. 582.
Use the additive real line with Lebesgue measure, `U k = (-2⁻ᵏ, 2⁻ᵏ)` and `f(t) = t²`,
viewed as complex-valued. The average is `x² + 2⁻²ᵏ/3`. For fixed `k`, the points `n` and
`n + 1/n` approach each other while their averages differ by `2 + 1/n²`. -/
theorem Printed.uniformContinuous_dSequenceAverage_false :
    ¬ Printed.uniformContinuous_dSequenceAverage := by
  sorry

/-- Paper: Corollary A.5.4.3, (A.5.4.14)–(A.5.4.15), p. 585.
As printed: for every locally integrable complex function `f`, every compactly supported
continuous function `φ`, and every D′-sequence in a second-countable Hausdorff locally
compact abelian group with Haar measure, at each point where the averages of `f` converge,
the averages of `φ * f` converge to `φ` at that point times the original limit. The averaging
operator is `dSequenceAverage` and the premise describes `dSequenceRegularSet`.
See ERRATA F223. -/
def Printed.tendsto_dSequenceAverage_mul : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (U : ℕ → Set G) (f : G → ℂ), IsDPrimeSequence μ U → LocallyIntegrable f μ →
    ∀ (φ : CompactlySupportedContinuousMap G ℂ) (x : G) (l : ℂ),
      Tendsto (fun k ↦ dSequenceAverage μ (U k) f x) atTop (𝓝 l) →
      Tendsto (fun k ↦ dSequenceAverage μ (U k) (fun y ↦ φ y * f y) x) atTop (𝓝 (φ x * l))

/-- Paper: Corollary A.5.4.3, (A.5.4.14)–(A.5.4.15), p. 585.
Use the additive real line, Lebesgue measure, `U k = (-2⁻ᵏ, 2⁻ᵏ)` and `x = 0`.
For `t ≠ 0` put `f(t) = sgn(t) |t|^(-1/2)` and set `f(0) = 0`. Multiply
`sgn(t) |t|^(1/4)` by the continuous cutoff `max 0 (min 1 (2 - |t|))` to obtain `φ`.
The odd function `f` has zero average for every index. Away from zero on these intervals,
`φ(t) * f(t) = |t|^(-1/4)`, so the averages are `(4/3) * 2^(k/4)` and diverge. -/
theorem Printed.tendsto_dSequenceAverage_mul_false :
    ¬ Printed.tendsto_dSequenceAverage_mul := by
  sorry

end RiemannMasullo
