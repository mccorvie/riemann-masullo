module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UrysohnsLemma

/-! # Approximation by continuous functions of compact support -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace RiemannMasullo

/-- For `p < ∞`, compactly supported continuous functions approximate `Lᵖ` functions on a
locally compact Hausdorff space with a regular measure. This uses local compactness to
obtain cutoffs around compact sets. -/
theorem exists_hasCompactSupport_eLpNorm_sub_le {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} (hp : p ≠ ∞)
    {u : X → E} (hu : MemLp u p ν) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ v : X → E, eLpNorm (u - v) p ν ≤ ε ∧ Continuous v ∧ HasCompactSupport v := by
  classical
  let P (v : X → E) := Continuous v ∧ HasCompactSupport v
  apply hu.induction_dense hp P _ _ hε
  -- A cutoff between a compact subset and an open superset approximates an indicator.
  · intro c s hs hsfin δ hδ
    obtain ⟨η, hη, hb⟩ := exists_eLpNorm_indicator_le (μ := ν) hp
      (‖c‖ + ‖c‖) hδ
    have he := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hη.ne')).ne'
    obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne he
    obtain ⟨V, hsV, hV, -, hsmallV⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne he
    obtain ⟨b, hbK, hbV, hbc, hbr⟩ := exists_continuous_one_zero_of_isCompact hK
      hV.isClosed_compl (disjoint_compl_right_iff_subset.mpr (hKs.trans hsV))
    let v (x : X) := b x • c
    have hv : Continuous v := b.continuous.smul continuous_const
    refine ⟨v, ?_, hv, hbc.smul_right (f' := fun _ ↦ c)⟩
    have hμ : ν (V \ K) ≤ η := calc
      _ ≤ ν ((V \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := (add_le_add hsmallV.le hsmallK.le).trans_eq (ENNReal.add_halves _)
    have hvm : AEStronglyMeasurable v ν :=
      b.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const
    refine (eLpNorm_mono (hvm.sub (aestronglyMeasurable_const.indicator hs))
      (g := (V \ K).indicator fun _ ↦ ‖c‖ + ‖c‖) ?_).trans
        (hb _ hμ (hV.measurableSet.diff hK.isClosed.measurableSet).nullMeasurableSet)
    intro x
    by_cases hx : x ∈ K
    · simp [v, hx, hKs hx, hbK hx]
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hx⟩)]
      refine (norm_sub_le _ _).trans ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact add_le_add (by simpa [v, norm_smul, abs_of_nonneg (hbr x).1] using
        mul_le_mul_of_nonneg_right (hbr x).2 (norm_nonneg c)) (by simp [indicator]; split <;> simp)
    · have hxs : x ∉ s := fun h ↦ hxV (hsV h)
      simp [v, hxV, hxs, hbV hxV]
  · exact fun f g hf hg ↦ ⟨hf.1.add hg.1, hf.2.add hg.2⟩

/-- On a locally compact Hausdorff space with a regular measure, an integrable
function is an almost-everywhere limit of continuous functions of compact support.
No normality or countability condition on the ambient space is needed. -/
theorem exists_tendsto_ae_compactSupport {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : X → E} (hu : Integrable u ν) :
    ∃ U : ℕ → X → E, (∀ n, HasCompactSupport (U n)) ∧ (∀ n, Continuous (U n)) ∧
      ∀ᵐ z ∂ν, Tendsto (fun n ↦ U n z) atTop (𝓝 (u z)) := by
  obtain ⟨ε, -, hε, hlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  choose U hU hP using fun n ↦ exists_hasCompactSupport_eLpNorm_sub_le ENNReal.one_ne_top
    (memLp_one_iff_integrable.2 hu) (hε n).1.ne'
  have ht : Tendsto (fun n ↦ eLpNorm (U n - u) 1 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
      (fun n ↦ (eLpNorm_sub_comm _ _ _ _).le.trans (hU n))
  obtain ⟨s, -, hs⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ht).exists_seq_tendsto_ae
  exact ⟨U ∘ s, fun n ↦ (hP (s n)).2, fun n ↦ (hP (s n)).1, hs⟩

end RiemannMasullo
