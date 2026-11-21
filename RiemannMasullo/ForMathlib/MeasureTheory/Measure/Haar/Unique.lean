module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RiemannMasullo

/-- Additive Haar measures on a sigma-compact locally compact Hausdorff group are regular.
The compact exhaustion extends Haar uniqueness on precompact sets to all measurable sets. -/
theorem addHaar_regular_of_sigmaCompactSpace {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] : μ.Regular := by
  let ν : Measure G := Measure.addHaar
  have h : μ = μ.addHaarScalarFactor ν • ν := by
    ext s _hs
    let K (n : ℕ) := s ∩ compactCovering G n
    have hK : Monotone K := monotone_const.inter (fun _ _ h ↦ compactCovering_subset G h)
    have hcover : ⋃ n, K n = s := by
      rw [show (⋃ n, K n) = s ∩ ⋃ n, compactCovering G n from (Set.inter_iUnion _ _).symm,
        iUnion_compactCovering, Set.inter_univ]
    rw [← hcover, hK.measure_iUnion, hK.measure_iUnion]
    congr with n
    exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν
      ((isCompact_compactCovering G n).closure_of_subset Set.inter_subset_right)
  rw [h]
  exact Measure.Regular.smul ENNReal.coe_ne_top

end RiemannMasullo
