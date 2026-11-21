module

public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace RiemannMasullo

/-- A measure dominated by a finite regular measure on a Hausdorff Borel space is regular. -/
theorem regular_of_le_finite_regular {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    [ν.Regular] (h : μ ≤ ν) : μ.Regular := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν h
  have : μ.InnerRegularCompactLTTop := by
    constructor
    intro A hA r hr
    have he : μ A - r ≠ 0 := ne_of_gt (tsub_pos_of_lt hr)
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.1.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν A) he
    refine ⟨K, hKA, hK, ?_⟩
    have hd : μ (A \ K) < μ A - r := lt_of_le_of_lt (h (A \ K)) hsmall
    have hsum : μ A = μ K + μ (A \ K) := by
      simpa [union_eq_right.mpr hKA] using
        (measure_add_sdiff (μ := μ) hK.measurableSet.nullMeasurableSet A).symm
    rw [lt_tsub_iff_right] at hd
    rw [hsum] at hd
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ (A \ K))).mp
      (by simpa [add_comm] using hd)
  infer_instance

end RiemannMasullo
