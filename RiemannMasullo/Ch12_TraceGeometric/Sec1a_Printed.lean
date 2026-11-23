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

/-- Paper: Theorem 12.1.1.2(2), p. 499. The printed pointwise identity is false. In the
additive real line, written multiplicatively, take Lebesgue measure (`dt` under
`Multiplicative.ofAdd`), the averaging intervals of radius `1/(n+1)` about the identity, the
rank-one kernel `k(x, y) = sing x * prof y` with `sing x = tri t * |t|^(-1/4)` and
`prof y = tri u * exp(-u^2)` in the additive coordinates `t`, `u`, and the continuous
compactly supported multiplier `ρ x = tri t * |t|^(1/4)`, where `tri` is the triangle bump.
The kernel is square integrable and its integral operator is rank one, hence nuclear. Since
`ρ` vanishes at the identity, the right-hand side of the asserted identity vanishes there,
while `ρ x * k(x, y)` agrees off the null set `{x = 1}` with `tri t ^ 2 exp(-t^2) tri u`,
whose averages over the shrinking squares tend to one. The identity would give `1 = 0`. -/
private theorem dSequenceKernelSmoothening_mul_continuous_counterexample :
    ∃ (G : Type) (_ : CommGroup G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (_ : T2Space G) (_ : LocallyCompactSpace G) (_ : SecondCountableTopology G)
      (_ : MeasurableSpace G) (_ : BorelSpace G)
      (μ ν : Measure G) (_ : μ.IsHaarMeasure) (_ : IsFiniteMeasureOnCompacts ν)
      (_ : ν.InnerRegular) (U : ℕ → Set G) (f : G → ℝ≥0),
      IsDPrimeSequence μ U ∧ (∀ n, MeasurableSet (U n)) ∧ Continuous f ∧ (∀ x, 0 < f x) ∧
        ν = μ.withDensity (fun x ↦ ↑(f x)) ∧
        (∃ (k : Lp ℂ 2 (ν.prod ν)), IsNuclearOperator (integralKernelOperator ν k).val ∧
          ∃ (κ : G × G → ℂ), κ =ᵐ[ν.prod ν] k ∧
            ∃ (ρ : G → ℂ), Continuous ρ ∧ HasCompactSupport ρ ∧
              dSequenceKernelSmoothening μ U (fun p ↦ ρ p.1 * κ p) ≠
                fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p) := by
  sorry

/-- Paper: Theorem 12.1.1.2(2), p. 499. The pointwise identity is refuted by the
counterexample above: at the identity the two sides are one and zero. -/
theorem Printed.dSequenceKernelSmoothening_mul_continuous_false :
    ¬ Printed.dSequenceKernelSmoothening_mul_continuous := by
  rintro h
  obtain ⟨G, hG₁, hG₂, hG₃, hG₄, hG₅, hG₆, hG₇, hG₈, μ, ν, hμ, hν, hν', U, f,
    hD, hmeas, hcont, hpos, hdens, k, hk, κ, hκ, ρ, hρ, hρc, hne⟩ :=
    dSequenceKernelSmoothening_mul_continuous_counterexample
  exact hne (h (G := G) (μ := μ) (ν := ν) (U := U) (f := f)
    hD hmeas hcont hpos hdens k hk κ hκ ρ hρ hρc)

end RiemannMasullo
