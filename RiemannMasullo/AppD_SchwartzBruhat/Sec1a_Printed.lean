module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a

/-! # Appendix D.1.2: the printed existence claim for Haar fibre integrals -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory

universe u

/-- Paper: Theorem D.1.2.1, p. 747. As printed: for every μ_G-measurable
complex-valued function, the Haar integral over the translate of the closed
subgroup by x exists for μ_G-almost every x. This is the existence assertion in
the second sentence. See `weilQuotientMeasure_existsUnique`,
`weilQuotientIntegral_L1` and ERRATA F230. -/
def Printed.weilQuotientIntegral_measurable : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μG : Measure G) [μG.IsHaarMeasure] [μG.Regular]
      (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
      (f : G → ℂ), AEMeasurable f μG →
        ∀ᵐ x ∂μG, Integrable (fun h : H ↦ f (x * (h : G))) μH

/-- Paper: Theorem D.1.2.1, p. 747. Take G = H = ℝ under addition, with Lebesgue
Haar measures, and f identically one. The integral over each fibre has infinite
mass, so no fibre has a complex Haar integral. For the sign function both the
positive and negative parts have infinite mass on every fibre. -/
theorem Printed.weilQuotientIntegral_measurable_false :
    ¬ Printed.weilQuotientIntegral_measurable := by
  sorry

end RiemannMasullo
