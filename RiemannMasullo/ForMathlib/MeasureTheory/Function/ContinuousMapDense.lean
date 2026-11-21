module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UrysohnsLemma

/-! # Approximation by continuous functions of compact support

Compactly supported continuous approximation on locally compact Hausdorff spaces,
including absolutely summable compact-test expansions of integrable functions.
-/

public section

namespace RiemannMasullo

section CompactTestExpansion

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal


variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}

/-- Absolute convergence in integral norm implies integrability of the pointwise sum. -/
theorem integrable_tsum_of_lintegral_eNorm [CompleteSpace E] {g : ℕ → X → E}
    (hm : ∀ n, AEStronglyMeasurable (g n) μ) (hs : ∑' n, ∫⁻ x, ‖g n x‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun x ↦ ∑' n, g n x) μ := by
  refine ⟨.tsum hm, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x ↦ eNorm_tsum_le_tsum_eNorm) ?_
  rwa [lintegral_tsum (fun n ↦ (hm n).eNorm), lt_top_iff_ne_top]

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [μ.Regular] [NormedSpace ℝ E]

/-- Compact-test density for a locally compact Hausdorff domain, without a normality
assumption: regularity sandwiches each finite-measure set between a compact and an open set. -/
private theorem exists_compactTest_eLpNorm_sub_le {f : X → E} (hf : Integrable f μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g, eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ HasCompactSupport g := by
  classical
  apply (memLp_one_iff_integrable.mpr hf).induction_dense (by simp) _ _ _ hε
  · intro c s hsm hsf δ hδ
    obtain ⟨η, hη, hsmall⟩ := exists_eLpNorm_indicator_le (p := 1) (μ := μ) (by simp) c hδ
    have hη' : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hη.ne')).ne'
    obtain ⟨U, hsU, hU, -, hUs⟩ := hsm.exists_isOpen_sdiff_lt hsf.ne hη'
    obtain ⟨K, hKs, hK, hsK⟩ := hsm.exists_isCompact_sdiff_lt hsf.ne hη'
    obtain ⟨b, hbK, hbU, hbs, hb⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hμ : μ (U \ K) ≤ η := calc
      _ ≤ μ ((U \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := (add_le_add hUs.le hsK.le).trans_eq (ENNReal.add_halves _)
    let g (x : X) := b x • c
    have hc : Continuous g := b.continuous.smul continuous_const
    have hs : HasCompactSupport g := hbs.comp_left (g := fun t : ℝ ↦ t • c) (zero_smul _ _)
    refine ⟨g, ?_, hc, hs⟩
    refine (eLpNorm_mono ((hc.integrable_of_hasCompactSupport hs).1.sub (aestronglyMeasurable_const.indicator hsm))
      (g := (U \ K).indicator (fun _ ↦ c)) ?_).trans
      (hsmall _ hμ (hU.measurableSet.diff hK.measurableSet).nullMeasurableSet)
    intro x
    by_cases hxK : x ∈ K
    · simp [g, hxK, hKs hxK, show b x = 1 from hbK hxK]
    by_cases hxs : x ∈ s
    · simp only [Pi.sub_apply, indicator_of_mem hxs, indicator_of_mem
        (show x ∈ U \ K from ⟨hsU hxs, hxK⟩), g]
      rw [show b x • c - c = (b x - 1) • c by rw [sub_smul, one_smul], norm_smul]
      have hle : ‖b x - 1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
      simpa using mul_le_mul_of_nonneg_right hle (norm_nonneg c)
    · by_cases hxU : x ∈ U
      · simpa [g, hxU, hxK, hxs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb x).1] using
          mul_le_mul_of_nonneg_right (hb x).2 (norm_nonneg c)
      · simp [g, hxU, hxs, show b x = 0 from hbU hxU]
  · exact fun _ _ ⟨hc, hs⟩ ⟨hc', hs'⟩ ↦ ⟨hc.add hc', hs.add hs'⟩

/-- Expand an integrable function almost everywhere in compactly supported continuous
functions whose integral norms sum to a finite number. -/
theorem exists_compactTest_tsum {f : X → E} (hf : Integrable f μ) :
    ∃ g : ℕ → X → E, (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
      (∑' n, ∫⁻ x, ‖g n x‖ₑ ∂μ) ≠ ⊤ ∧ (f =ᵐ[μ] fun x ↦ ∑' n, g n x) := by
  obtain ⟨δ, hδ, hδs⟩ := ENNReal.exists_pos_sum_of_countable' (ε := ⊤) (by simp) ℕ
  choose a ha hac has using fun n ↦ exists_compactTest_eLpNorm_sub_le hf (hδ n).ne'
  let g : ℕ → X → E := fun n ↦ Nat.casesOn n (a 0) (fun k ↦ a (k + 1) - a k)
  have hg (n) : Continuous (g n) ∧ HasCompactSupport (g n) := by
    cases n with
    | zero => exact ⟨hac 0, has 0⟩
    | succ n => exact ⟨(hac _).sub (hac n), (has _).sub (has n)⟩
  have htail (n : ℕ) : eLpNorm (g (n + 1)) 1 μ ≤ δ n + δ (n + 1) := by
    have he : g (n+1) = (f - a n) - (f - a (n + 1)) := by dsimp [g]; abel
    exact he ▸ (eLpNorm_sub_le le_rfl).trans (add_le_add (ha n) (ha (n + 1)))
  have hsum : ∑' n, eLpNorm (g n) 1 μ ≠ ⊤ := by
    intro h
    have h0 : eLpNorm (g 0) 1 μ ≠ ⊤ := (memLp_one_iff_integrable.mpr
      ((hac 0).integrable_of_hasCompactSupport (has 0))).eLpNorm_lt_top.ne
    have ht := ENNReal.tsum_add_one_eq_top h h0
    have hh := tsum_le_tsum (f := fun n ↦ eLpNorm (g (n + 1)) 1 μ) (g := fun n ↦ δ n + δ (n + 1)) htail
    rw [ht, tsum_add] at hh
    exact (not_le_of_gt (ENNReal.add_lt_top.mpr ⟨hδs,
      (tsum_comp_le_tsum_of_injective Nat.succ_injective δ).trans_lt hδs⟩)) hh
  refine ⟨g, hg, ?_, ?_⟩
  · have he n := eLpNorm_one_eq_lintegral_eNorm (((hg n).1.integrable_of_hasCompactSupport (μ := μ) (hg n).2).1)
    simpa only [he] using hsum
  · have herr := summable_norm_of_tsum_eLpNorm_ne_top (le_refl (1 : ℝ≥0∞))
        ((tsum_le_tsum (f := fun n ↦ eLpNorm (f - a n) 1 μ) (g := δ) ha).trans_lt hδs).ne
    filter_upwards [herr, summable_norm_of_tsum_eLpNorm_ne_top le_rfl hsum] with x hx hx'
    symm
    apply HasSum.tsum_eq
    apply (hasSum_iff_tendsto_nat_of_summable_norm hx').mpr
    apply (tendsto_add_atTop_iff_nat 1).mp
    have hpart (n : ℕ) : ∑ i ∈ Finset.range (n+1), g i x = a n x := by
      induction n with
      | zero => simp [g]
      | succ n ih => rw [Finset.sum_range_succ, ih]; dsimp [g]; abel
    simp_rw [hpart]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Pi.sub_apply, norm_sub_rev (f x)] using hx.tendsto_atTop_zero

end CompactTestExpansion

section CompactSupportApproximation

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal


/-- Approximate the indicator of a finite-measure set by a continuous cutoff with compact
support. The error is bounded by a constant on a measurable set of arbitrarily small mass. -/
private theorem exists_continuous_indicator_error_bound
    {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) {s : Set X}
    (hs : MeasurableSet s) (hsfin : ν s < ∞) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ (v : X → E) (t : Set X), Continuous v ∧ HasCompactSupport v ∧ AEStronglyMeasurable v ν ∧
      MeasurableSet t ∧ ν t ≤ η ∧ ∀ x, ‖(s.indicator (fun _ ↦ c) - v) x‖ ≤
        ‖t.indicator (fun _ ↦ ‖c‖ + ‖c‖) x‖ := by
  have he := (ENNReal.half_pos hη).ne'
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne he
  obtain ⟨V, hsV, hV, -, hsmallV⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne he
  obtain ⟨b, hbK, hbV, hbc, hbr⟩ := exists_continuous_one_zero_of_isCompact hK
    hV.isClosed_compl (disjoint_compl_right_iff_subset.mpr (hKs.trans hsV))
  let v (x : X) := b x • c
  refine ⟨v, V \ K, b.continuous.smul continuous_const, hbc.smul_right (f' := fun _ ↦ c),
    b.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const,
    hV.measurableSet.diff hK.isClosed.measurableSet, ?_, ?_⟩
  · calc
      _ ≤ ν ((V \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ ν (V \ s) + ν (s \ K) := measure_union_le _ _
      _ ≤ η := (add_le_add hsmallV.le hsmallK.le).trans_eq (ENNReal.add_halves _)
  · intro x
    by_cases hx : x ∈ K
    · simp [v, hx, hKs hx, hbK hx]
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hx⟩)]
      refine (norm_sub_le _ _).trans ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact add_le_add (by simp [indicator]; split <;> simp) (by
        simpa [v, norm_smul, abs_of_nonneg (hbr x).1] using
          mul_le_mul_of_nonneg_right (hbr x).2 (norm_nonneg c))
    · have hxs : x ∉ s := fun h ↦ hxV (hsV h)
      simp [v, hxV, hxs, hbV hxV]

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
  · intro c s hs hsfin δ hδ
    obtain ⟨η, hη, hb⟩ := exists_eLpNorm_indicator_le (μ := ν) hp (‖c‖ + ‖c‖) hδ
    obtain ⟨v, t, hv, hvK, hvm, ht, hνt, hbound⟩ :=
      exists_continuous_indicator_error_bound c hs hsfin (ENNReal.coe_ne_zero.mpr hη.ne')
    refine ⟨v, ?_, hv, hvK⟩
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_mono ((aestronglyMeasurable_const.indicator hs).sub hvm) hbound).trans
      (hb t hνt ht.nullMeasurableSet)
  · exact fun f g hf hg ↦ ⟨hf.1.add hg.1, hf.2.add hg.2⟩

section Approximation

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactly supported continuous functions approximate a function simultaneously in
`Lᵖ` and `Lᑫ` for finite exponents at least one. -/
theorem exists_hasCompactSupport_eLpNorm_sub_le_two
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hp' : p ≠ ∞) (hq' : q ≠ ∞)
    {u : X → E} (hup : MemLp u p ν) (huq : MemLp u q ν) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ v : X → E, Continuous v ∧ HasCompactSupport v ∧
      eLpNorm (u - v) p ν ≤ ε ∧ eLpNorm (u - v) q ν ≤ ε := by
  classical
  borelize E
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have he := (ENNReal.half_pos hε).ne'
  have approxSimple (f : SimpleFunc X E) (hf : MemLp f p ν) :
      ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ v : X → E, Continuous v ∧ HasCompactSupport v ∧
        eLpNorm (⇑f - v) p ν ≤ δ ∧ eLpNorm (⇑f - v) q ν ≤ δ := by
    induction f using SimpleFunc.induction with
    | const c hs =>
      intro δ hδ
      rename_i s
      have hcoe : (⇑(SimpleFunc.piecewise s hs (SimpleFunc.const X c)
          (SimpleFunc.const X 0)) : X → E) = s.indicator (fun _ ↦ c) := by
        rw [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_const]
        rfl
      rw [hcoe]
      by_cases hc : c = 0
      · subst c
        exact ⟨0, continuous_const, HasCompactSupport.zero, by simp, by simp⟩
      have hsfin := SimpleFunc.measure_lt_top_of_memLp_indicator hp0 hp' hc hs hf
      obtain ⟨ηp, hηp, hboundp⟩ := exists_eLpNorm_indicator_le (μ := ν) hp' (‖c‖ + ‖c‖) hδ
      obtain ⟨ηq, hηq, hboundq⟩ := exists_eLpNorm_indicator_le (μ := ν) hq' (‖c‖ + ‖c‖) hδ
      obtain ⟨v, t, hv, hvK, hvm, ht, hνt, hbound⟩ :=
        exists_continuous_indicator_error_bound c hs hsfin
          (ENNReal.coe_ne_zero.mpr (lt_min hηp hηq).ne')
      have hm : AEStronglyMeasurable (s.indicator (fun _ ↦ c) - v) ν :=
        (aestronglyMeasurable_const.indicator hs).sub hvm
      exact ⟨v, hv, hvK,
        (eLpNorm_mono hm hbound).trans (hboundp t (hνt.trans (by exact_mod_cast min_le_left ..))
          ht.nullMeasurableSet),
        (eLpNorm_mono hm hbound).trans (hboundq t (hνt.trans (by exact_mod_cast min_le_right ..))
          ht.nullMeasurableSet)⟩
    | add hdisj ihf ihg =>
      rename_i f g
      intro δ hδ
      rw [FunLike.coe_add, memLp_add_of_disjoint hdisj f.aestronglyMeasurable] at hf
      obtain ⟨v, hv, hvK, hvp, hvq⟩ := ihf hf.1 (δ / 2) (ENNReal.half_pos hδ).ne'
      obtain ⟨w, hw, hwK, hwp, hwq⟩ := ihg hf.2 (δ / 2) (ENNReal.half_pos hδ).ne'
      refine ⟨v + w, hv.add hw, hvK.add hwK, ?_, ?_⟩ <;>
        rw [FunLike.coe_add, add_sub_add_comm]
      · exact (eLpNorm_add_le hp).trans ((add_le_add hvp hwp).trans_eq (ENNReal.add_halves _))
      · exact (eLpNorm_add_le hq).trans ((add_le_add hvq hwq).trans_eq (ENNReal.add_halves _))
  -- The same sequence of simple functions converges in both norms.
  let u' := hup.aestronglyMeasurable.mk u
  have hueq : u =ᵐ[ν] u' := hup.aestronglyMeasurable.ae_eq_mk
  have hum := hup.aestronglyMeasurable.measurable_mk
  let : SeparableSpace (range u' ∪ {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hup.aestronglyMeasurable.stronglyMeasurable_mk
  let a n := SimpleFunc.approxOn u' hum (range u' ∪ {0}) 0 (by simp) n
  have hlim {r : ℝ≥0∞} (hr : r ≠ ∞) (hu : MemLp u r ν) :
      Tendsto (fun n ↦ eLpNorm (⇑(a n) - u') r ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm hr hum (hu.ae_eq hueq).eLpNorm_lt_top
  obtain ⟨n, hpδ, hqδ⟩ := (((hlim hp' hup).eventually (gt_mem_nhds he.bot_lt)).and
    ((hlim hq' huq).eventually (gt_mem_nhds he.bot_lt))).exists
  obtain ⟨v, hv, hvK, hvp, hvq⟩ := approxSimple (a n)
    (SimpleFunc.memLp_approxOn_range hum (hup.ae_eq hueq) n) (ε / 2) he
  have heq : (u - v) =ᵐ[ν] (u' - v) := hueq.sub EventuallyEq.rfl
  refine ⟨v, hv, hvK, ?_, ?_⟩ <;>
    rw [eLpNorm_congr_ae heq, show u' - v = u' - ⇑(a n) + (⇑(a n) - v) by abel]
  · exact (eLpNorm_add_le hp).trans
      ((add_le_add ((eLpNorm_sub_comm _ _ _ _).le.trans hpδ.le) hvp).trans_eq (ENNReal.add_halves _))
  · exact (eLpNorm_add_le hq).trans
      ((add_le_add ((eLpNorm_sub_comm _ _ _ _).le.trans hqδ.le) hvq).trans_eq (ENNReal.add_halves _))

end Approximation

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

end CompactSupportApproximation

end RiemannMasullo
