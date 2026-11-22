module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

public section

open MeasureTheory Set

namespace RiemannMasullo

/-- Every Borel Haar measure on a compact Hausdorff group is regular. -/
theorem haar_regular_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] : μ.Regular := by
  let ν : Measure G := Measure.haar
  have heq : μ = μ.haarScalarFactor ν • ν := by
    ext s hs
    exact Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet μ ν hs
      isClosed_closure.isCompact
  rw [heq]
  exact Measure.Regular.smul ENNReal.coe_ne_top

end RiemannMasullo
