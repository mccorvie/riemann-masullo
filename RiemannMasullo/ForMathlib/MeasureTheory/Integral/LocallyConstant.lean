module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Complex.Basic

/-! # Algebraic integration of locally constant functions with compact support -/

@[expose] public section

namespace RiemannMasullo

open Filter Function MeasureTheory Set
open scoped Topology

/-- The integral of a compactly supported locally constant vector-valued function is
a finite linear combination of its values. Every algebraic functional commutes with it. -/
theorem exists_algebraic_integral_of_locallyConstant {G E : Type*} [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup E] [Module ℂ E]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (h : G → E)
    (hl : IsLocallyConstant h) (hc : HasCompactSupport h) :
    ∃ y : E, ∀ L : E →ₗ[ℂ] ℂ, L y = ∫ g, L (h g) ∂μ := by
  classical
  let C := tsupport h
  let : CompactSpace C := isCompact_iff_compactSpace.mp hc
  let image := (hl.comp_continuous (continuous_subtype_val (p := (· ∈ C)))).range_finite
  let S := image.toFinset.erase 0
  let U (e : E) := h ⁻¹' {e}
  have ho (e : E) : MeasurableSet (U e) := (hl.isOpen_fiber e).measurableSet
  have hcU {e : E} (he : e ∈ S) : IsCompact (U e) := hc.of_isClosed_subset (hl.isClosed_fiber e) (fun x hx ↦ by
    apply subset_tsupport h
    exact (show h x = e from hx).trans_ne (Finset.ne_of_mem_erase he))
  refine ⟨∑ e ∈ S, ((μ (U e)).toReal : ℂ) • e, fun L ↦ ?_⟩
  have hh (g : G) : L (h g) = ∑ e ∈ S, (U e).indicator (fun _ ↦ L e) g := by
    by_cases h0 : h g = 0
    · rw [h0, map_zero]
      symm
      exact Finset.sum_eq_zero fun e he ↦ indicator_of_notMem (fun hs ↦ Finset.ne_of_mem_erase he ((show h g = e from hs).symm.trans h0)) _
    · have hg : g ∈ C := subset_tsupport h h0
      symm
      rw [Finset.sum_eq_single_of_mem (h g) (Finset.mem_erase.mpr ⟨h0, image.mem_toFinset.mpr ⟨⟨g,hg⟩,rfl⟩⟩)]
      · exact indicator_of_mem rfl _
      · intro e _ he
        exact indicator_of_notMem (fun hm ↦ he (show h g = e from hm).symm) _
  simp_rw [hh]
  rw [integral_finsetSum S fun e he ↦ (integrableOn_const (hcU he).measure_ne_top).integrable_indicator (ho e), map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [map_smul, integral_indicator (ho e), setIntegral_const]
  rfl

end RiemannMasullo
