module

public import RiemannMasullo.Ch12_TraceGeometric.Sec2

/-!
# Section 12.2: statements that are false as printed
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace RiemannMasullo

local instance instQuotientMeasurableSpaceSec2Printed {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: Proposition 12.2.2.2(4), p. 509. The last sentence asserts that at every
pair in the group product, regularity for the indented lift is equivalent to regularity
of the quotient pair for the original kernel. -/
def Printed.diagonalIndentationLift_regular_iff : Prop :=
  ∀ {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [DiscreteTopology H],
    IsClosed (H : Set G) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (G ⧸ H)),
    IsWeilQuotientMeasure H μ Measure.count ν →
    ∀ (D : Set G) (U : ℕ → Set G), IsConnected D → IsDiagonalIndentationSituation H μ D U →
    ∀ (b : G → ℝ), IsIndentation H Measure.count b →
    ∀ (u : (G ⧸ H) × (G ⧸ H) → ℂ), LocallyIntegrable u (ν.prod ν) →
    ∀ p : G × G,
      p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n)
        (diagonalIndentationLift H Measure.count b u) ↔
      (QuotientGroup.mk p.1, QuotientGroup.mk p.2) ∈
        dSequenceRegularSet (ν.prod ν) (fun n ↦
          (QuotientGroup.mk' H '' U n) ×ˢ (QuotientGroup.mk' H '' U n)) u

/-- Paper: Proposition 12.2.2.2(4), p. 509. Use additive `G = ℤ × ℝ`,
`H = ℤ × {0}`, counting times Lebesgue measure, `D = {0} × ℝ`, and
`U n = {0} × (−2⁻ⁿ, 2⁻ⁿ)`. Put `a(t) = 3/4 + sgn(t) min(1, |t|^(1/8))/4`.
The indentation is `a(t)` on the integer slice 0, `1 − a(t)` on slice 1, and
zero on the others. On the quotient use the rank-one kernel
`u(t,s) = g(t) χ(s)`, where `χ(t) = max(0, min(1, 2 − |t|))` and
`g(t) = χ(t) sgn(t) |t|^(−1/4)` for `t ≠ 0`, with `g(0) = 0`.
At the origin the quotient averages are zero by oddness, but the lift averages
over squares of radius `r = 2⁻ⁿ` are `r^(−1/8)/7` and diverge. -/
theorem Printed.diagonalIndentationLift_regular_iff_false :
    ¬ Printed.diagonalIndentationLift_regular_iff := by sorry

end RiemannMasullo
