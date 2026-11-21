module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Group.Pointwise

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace RiemannMasullo

/-- A group with a regular, σ-finite Haar measure is σ-compact. -/
theorem sigmaCompactSpace_of_sigmaFinite_haar {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ] : SigmaCompactSpace G := by
  let ε (n : ℕ) : ℝ≥0∞ := (↑(n + 1) : ℝ≥0∞)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hex (m n : ℕ) : ∃ K, K ⊆ spanningSets μ m ∧ IsCompact K ∧
      μ (spanningSets μ m \ K) < ε n :=
    (measurableSet_spanningSets μ m).exists_isCompact_sdiff_lt
      (measure_spanningSets_lt_top μ m).ne (by simp [ε])
  choose K _ hK hrem using hex
  let A : Set G := ⋃ p : ℕ × ℕ, K p.1 p.2
  have hA : ∀ᵐ x ∂μ, x ∈ A := by
    have hnull (m : ℕ) : μ (spanningSets μ m \ A) = 0 := by
      refine le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hε fun n ↦ ?_) bot_le
      exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion
        (fun p : ℕ × ℕ ↦ K p.1 p.2) (m, n)))).trans (hrem m n).le
    filter_upwards [ae_all_iff.mpr (fun m ↦ measure_eq_zero_iff_ae_notMem.mp (hnull m))] with x hx
    obtain ⟨m, hm⟩ := iUnion_eq_univ_iff.mp (iUnion_spanningSets μ) x
    by_contra hn
    exact hx m ⟨hm, hn⟩
  let D (p : (ℕ × ℕ) × (ℕ × ℕ)) := K p.1.1 p.1.2 * (K p.2.1 p.2.2)⁻¹
  have hcover : ⋃ p, D p = univ := by
    refine iUnion_eq_univ_iff.mpr fun x ↦ ?_
    obtain ⟨y, hy, hxy⟩ := (hA.and
      ((measurePreserving_mul_left μ x).quasiMeasurePreserving.ae hA)).exists
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact ⟨(i, j), Set.mem_mul.mpr ⟨x * y, hi, y⁻¹, Set.inv_mem_inv.mpr hj, by simp⟩⟩
  exact ⟨hcover ▸ isSigmaCompact_iUnion_of_isCompact D
    (fun p ↦ (hK p.1.1 p.1.2).mul (hK p.2.1 p.2.2).inv)⟩

end RiemannMasullo
