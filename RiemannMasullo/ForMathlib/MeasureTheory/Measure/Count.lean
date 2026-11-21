module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Group.Measure

/-! # Counting measure on discrete spaces -/

public section

open MeasureTheory Set

namespace RiemannMasullo

/-- Counting measure on a discrete space is regular: every set is open, and an infinite open set
contains finite, hence compact, subsets of every size. -/
theorem count_regular_of_discreteTopology {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [MeasurableSpace X] [MeasurableSingletonClass X] :
    (Measure.count : Measure X).Regular where
  lt_top_of_isCompact _ hK := Measure.count_apply_lt_top.mpr hK.finite_of_discrete
  outerRegular := fun A _ _ hr ↦ ⟨A, subset_rfl, isOpen_discrete A, hr⟩
  innerRegular := by
    intro U _ r hr
    by_cases hU : U.Finite
    · exact ⟨U, subset_rfl, hU.isCompact, hr⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hr.trans_le le_top).ne
      obtain ⟨t, htU, htn⟩ := (Set.not_finite.mp hU).exists_subset_card_eq n
      refine ⟨t, htU, t.finite_toSet.isCompact, ?_⟩
      rw [Measure.count_apply_finset, htn]
      exact hn

/-- Counting measure on a discrete group is a Haar measure. -/
theorem count_isHaarMeasure_of_discreteTopology {G : Type*} [Group G]
    [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableMul G] : (Measure.count : Measure G).IsHaarMeasure :=
  { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
    open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }

end RiemannMasullo
