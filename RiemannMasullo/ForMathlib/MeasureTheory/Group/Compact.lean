module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Group.Pointwise

public section

open MeasureTheory Set
open scoped Pointwise

namespace RiemannMasullo

/-- A topological group with finite, regular Haar measure is compact. -/
theorem compactSpace_of_isFiniteMeasure_haar {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [IsFiniteMeasure μ] : CompactSpace G := by
  obtain ⟨K, _, hK, hmass⟩ := isOpen_univ.exists_lt_isCompact (μ := μ)
    (ENNReal.half_lt_self (isOpen_univ.measure_ne_zero μ univ_nonempty) (measure_lt_top μ _).ne)
  have hcover : K * K⁻¹ = univ := by
    apply eq_univ_of_forall
    intro x
    have hdisj : ¬ Disjoint K ((x * ·) ⁻¹' K) := by
      intro h
      have hmeas := hK.isClosed.measurableSet.preimage (measurable_const_mul x)
      have hlarge : μ univ < μ (K ∪ (x * ·) ⁻¹' K) := calc
        μ univ = μ univ / 2 + μ univ / 2 := (ENNReal.add_halves _).symm
        _ < μ K + μ K := ENNReal.add_lt_add hmass hmass
        _ = μ (K ∪ (x * ·) ⁻¹' K) := by rw [measure_union h hmeas, measure_preimage_mul]
      exact hlarge.not_ge (measure_mono (subset_univ _))
    obtain ⟨y, hy, hxy⟩ := Set.not_disjoint_iff.mp hdisj
    exact Set.mem_mul.mpr ⟨x * y, hxy, y⁻¹, Set.inv_mem_inv.mpr hy, by simp⟩
  exact ⟨hcover ▸ hK.mul hK.inv⟩

end RiemannMasullo
