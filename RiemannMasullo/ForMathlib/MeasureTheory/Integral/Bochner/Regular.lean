module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace RiemannMasullo

/-- For an integrable function, a compact subset of a measurable set carries all but an
arbitrarily small part of the integral of its norm, assuming inner regularity on finite sets. -/
theorem exists_isCompact_integral_norm_sdiff_lt
    {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [μ.InnerRegularCompactLTTop] {f : X → E}
    (hf : Integrable f μ) {s : Set X} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ K ⊆ s, IsCompact K ∧ (∫ x in s \ K, ‖f x‖ ∂μ) < ε := by
  obtain ⟨t, ht, htZero, htFin⟩ := hf.aefinStronglyMeasurable.exists_set_sigmaFinite
  let : SigmaFinite (μ.restrict t) := htFin
  let A (n : ℕ) := s ∩ (spanningSets (μ.restrict t) n ∩ t)
  have hA n : MeasurableSet (A n) := hs.inter ((measurableSet_spanningSets _ _).inter ht)
  have hAμ n : μ (A n) < ∞ := by
    apply (measure_mono inter_subset_right).trans_lt
    rw [← Measure.restrict_apply (measurableSet_spanningSets _ _)]
    exact measure_spanningSets_lt_top _ _
  have hUnion : ⋃ n, A n = s ∩ t := by
    simp [A, ← iUnion_inter, ← inter_iUnion]
  have hMono : Monotone A := fun i j hij ↦
    inter_subset_inter_right _ (inter_subset_inter_left _ (monotone_spanningSets _ hij))
  have hLim := tendsto_setIntegral_of_monotone (f := fun x ↦ ‖f x‖) hA hMono hf.norm.integrableOn
  rw [hUnion] at hLim
  have hEq : (∫ x in s ∩ t, ‖f x‖ ∂μ) = ∫ x in s, ‖f x‖ ∂μ := by
    symm
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs.nullMeasurableSet inter_subset_left ?_
    filter_upwards [ae_imp_of_ae_restrict htZero] with x hx hxS
    have hxT : x ∈ tᶜ := fun h ↦ hxS.2 ⟨hxS.1, h⟩
    simp [show f x = 0 from hx hxT]
  rw [hEq] at hLim
  have hNear : ∀ᶠ n in atTop, (∫ x in s, ‖f x‖ ∂μ) - ε / 2 < ∫ x in A n, ‖f x‖ ∂μ :=
    hLim (Ioi_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := hNear.exists
  obtain ⟨δ, hδ, hSmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf.hasFiniteIntegral.ne
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨K, hKA, hK, hm⟩ := (hA n).exists_isCompact_sdiff_lt (hAμ n).ne hδ.ne'
  have hKmeas := hK.isClosed.measurableSet
  have hSmall' : (∫ x in A n \ K, ‖f x‖ ∂μ) < ε / 2 := by
    have h := hSmall (A n \ K) hm
    rw [integral_norm_eq_lintegral_eNorm hf.integrableOn.aestronglyMeasurable]
    exact (ENNReal.toReal_lt_toReal h.ne_top ENNReal.ofReal_ne_top).mpr h |>.trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  have hKs : K ⊆ s := hKA.trans inter_subset_left
  have h₁ := setIntegral_sdiff hKmeas hf.norm.integrableOn hKA
  have h₂ := setIntegral_sdiff hKmeas hf.norm.integrableOn hKs
  exact ⟨K, hKs, hK, by
    change _ < (∫ x in A n, ‖f x‖ ∂μ) at hn
    linarith⟩

end RiemannMasullo
