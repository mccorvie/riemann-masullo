module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Averaging monotone upper cutoffs
Exact radius-layer Fubini and stability of the signed logarithmic main term.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

namespace RiemannMasullo.CutoffAverages

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
  (σ τ : Measure ℝ) [IsFiniteMeasure σ] [IsFiniteMeasure τ]

noncomputable def gate (a r : ℝ) : ℂ := if a ≤ r then 1 else 0

theorem integral_pair (P Q : X → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (H : X → ℂ) (hH : Integrable H μ) :
    (∫ x, (∫ r, gate (P x) r ∂σ) * (∫ s, gate (Q x) s ∂τ) * H x ∂μ) =
      ∫ u, (∫ x, gate (P x) u.1 * gate (Q x) u.2 * H x ∂μ) ∂σ.prod τ := by
  let A : Set (X × (ℝ × ℝ)) := {z | P z.1 ≤ z.2.1 ∧ Q z.1 ≤ z.2.2}
  have hA : MeasurableSet A :=
    (measurableSet_le (hP.comp measurable_fst) (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (hQ.comp measurable_fst) (measurable_snd.comp measurable_snd))
  let F : X × (ℝ × ℝ) → ℂ := fun z => gate (P z.1) z.2.1 * gate (Q z.1) z.2.2 * H z.1
  have hF : Integrable F (μ.prod (σ.prod τ)) := by
    have he : F = A.indicator (fun z => H z.1) := by
      funext z
      by_cases hp : P z.1 ≤ z.2.1 <;> by_cases hq : Q z.1 ≤ z.2.2 <;>
        simp [F, A, gate, Set.indicator, hp, hq]
    rw [he]
    exact (hH.comp_fst (σ.prod τ)).indicator hA
  calc
    _ = ∫ x, (∫ u, F (x,u) ∂σ.prod τ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F, integral_mul_const, integral_prod_mul]
    _ = ∫ z, F z ∂μ.prod (σ.prod τ) := (integral_prod F hF).symm
    _ = _ := integral_prod_symm F hF

private theorem integral_gate_zero {ν : Measure ℝ} {a b : ℝ}
    (hb : ∀ᵐ r ∂ν, r ≤ b) (ha : ¬ a ≤ b) : (∫ r, gate a r ∂ν) = 0 := by
  calc
    _ = ∫ _ : ℝ, (0 : ℂ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hb] with r hr
      exact ite_eq_right (fun h ↦ ha (h.trans hr))
    _ = 0 := by simp

theorem integral_pair_masked (P Q : X → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (H : X → ℂ) (b c : ℝ) (hb : ∀ᵐ r ∂σ, r ≤ b) (hc : ∀ᵐ s ∂τ, s ≤ c)
    (hH : Integrable ({x | P x ≤ b ∧ Q x ≤ c}.indicator H) μ) :
    (∫ x, (∫ r, gate (P x) r ∂σ) * (∫ s, gate (Q x) s ∂τ) * H x ∂μ) =
      ∫ u, (∫ x, gate (P x) u.1 * gate (Q x) u.2 * H x ∂μ) ∂σ.prod τ := by
  let M : Set X := {x | P x ≤ b ∧ Q x ≤ c}
  calc
    _ = ∫ x, (∫ r, gate (P x) r ∂σ) * (∫ s, gate (Q x) s ∂τ) * M.indicator H x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hp : P x ≤ b
      · by_cases hq : Q x ≤ c
        · simp [M, Set.indicator, hp, hq]
        · simp [integral_gate_zero hc hq]
      · simp [integral_gate_zero hb hp]
    _ = _ := (integral_pair μ σ τ P Q hP hQ (M.indicator H) hH).trans (by
      apply integral_congr_ae
      have hb' : ∀ᵐ u : ℝ × ℝ ∂σ.prod τ, u.1 ≤ b := Measure.quasiMeasurePreserving_fst.ae hb
      have hc' : ∀ᵐ u : ℝ × ℝ ∂σ.prod τ, u.2 ≤ c := Measure.quasiMeasurePreserving_snd.ae hc
      filter_upwards [hb', hc'] with u hr hs
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hp : P x ≤ u.1 <;> by_cases hq : Q x ≤ u.2
      · simp [M, Set.indicator, hp.trans hr, hq.trans hs]
      all_goals simp [gate, hp, hq])

end RiemannMasullo.CutoffAverages

open MeasureTheory Set

namespace RiemannMasullo.CutoffAverages

noncomputable def upperRadiusProfile (σ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ r, gate t r ∂σ

theorem upperRadiusProfile_eq_measureReal (σ : Measure ℝ) (t : ℝ) :
    upperRadiusProfile σ t = (σ.real (Ici t) : ℂ) := by
  classical
  calc
    _ = ∫ r, (Ici t).indicator (fun _ : ℝ => (1 : ℂ)) r ∂σ := by
      apply integral_congr_ae
      filter_upwards [] with r
      by_cases h : t ≤ r <;> simp [gate, Set.indicator, h]
    _ = _ := by rw [integral_indicator_const _ measurableSet_Ici, Complex.real_smul, mul_one]

theorem measurable_upperRadiusProfile (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Measurable (upperRadiusProfile σ) := by
  have hm : Antitone (fun t : ℝ => σ.real (Ici t)) :=
    fun _ _ h => measureReal_mono (Ici_subset_Ici.mpr h)
  rw [funext (upperRadiusProfile_eq_measureReal σ)]
  exact Complex.continuous_ofReal.measurable.comp hm.measurable

theorem norm_upperRadiusProfile_le_one (σ : Measure ℝ) [IsProbabilityMeasure σ] (t : ℝ) :
    ‖upperRadiusProfile σ t‖ ≤ 1 := by
  rw [upperRadiusProfile_eq_measureReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem upperRadiusProfile_eq_zero (σ : Measure ℝ) {b t : ℝ}
    (hb : ∀ᵐ r ∂σ, r ≤ b) (ht : b < t) : upperRadiusProfile σ t = 0 := by
  have hz : σ (Ici t) = 0 :=
    measure_mono_null (fun ⦃r⦄ (hr : t ≤ r) => not_le_of_gt (ht.trans_le hr)) (ae_iff.mp hb)
  simp [upperRadiusProfile_eq_measureReal, Measure.real, hz]

theorem upperRadiusProfile_pair_mul_mask {X : Type*} (σ τ : Measure ℝ) (P Q : X → ℝ)
    (H : X → ℂ) {b c : ℝ} (hb : ∀ᵐ r ∂σ, r ≤ b) (hc : ∀ᵐ s ∂τ, s ≤ c) (x : X) :
    upperRadiusProfile σ (P x) * upperRadiusProfile τ (Q x) * H x =
      upperRadiusProfile σ (P x) * upperRadiusProfile τ (Q x) *
        {y | P y ≤ b ∧ Q y ≤ c}.indicator H x := by
  classical
  by_cases hp : P x ≤ b
  · by_cases hq : Q x ≤ c
    · simp [Set.indicator, hp, hq]
    · simp [upperRadiusProfile_eq_zero τ hc (lt_of_not_ge hq)]
  · simp [upperRadiusProfile_eq_zero σ hb (lt_of_not_ge hp)]

/-- Probability profiles inherit integrability from the joint outer sharp box. -/
theorem integrable_upperRadiusProfile_pair {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (P Q : X → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (H : X → ℂ) {b c : ℝ} (hb : ∀ᵐ r ∂σ, r ≤ b) (hc : ∀ᵐ s ∂τ, s ≤ c)
    (hH : Integrable ({x | P x ≤ b ∧ Q x ≤ c}.indicator H) μ) :
    Integrable (fun x ↦ upperRadiusProfile σ (P x) * upperRadiusProfile τ (Q x) * H x) μ := by
  have hp := (measurable_upperRadiusProfile σ).comp hP
  have hq := (measurable_upperRadiusProfile τ).comp hQ
  refine (hH.bdd_mul (hp.mul hq).aestronglyMeasurable (c := 1) (ae_of_all _ fun x ↦ ?_)).congr
    (ae_of_all _ fun x ↦ (upperRadiusProfile_pair_mul_mask σ τ P Q H hb hc x).symm)
  change ‖upperRadiusProfile σ (P x) * upperRadiusProfile τ (Q x)‖ ≤ 1
  rw [norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (norm_upperRadiusProfile_le_one σ _)
      (norm_upperRadiusProfile_le_one τ _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Every sharp pair with smaller radii is cut out of the same integrable box. -/
theorem integrable_gate_pair_of_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (P Q : X → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (H : X → ℂ) {b c r s : ℝ} (hr : r ≤ b) (hs : s ≤ c)
    (hH : Integrable ({x | P x ≤ b ∧ Q x ≤ c}.indicator H) μ) :
    Integrable (fun x ↦ gate (P x) r * gate (Q x) s * H x) μ := by
  let A : Set X := {x | P x ≤ r ∧ Q x ≤ s}
  let B : Set X := {x | P x ≤ b ∧ Q x ≤ c}
  have hA : MeasurableSet A :=
    (measurableSet_le hP measurable_const).inter (measurableSet_le hQ measurable_const)
  refine (hH.indicator hA).congr (ae_of_all _ fun x ↦ ?_)
  change A.indicator (B.indicator H) x = _
  by_cases hp : P x ≤ r <;> by_cases hq : Q x ≤ s
  · simp [A, B, Set.indicator, gate, hp, hq, hp.trans hr, hq.trans hs]
  all_goals simp [A, Set.indicator, gate, hp, hq]

end RiemannMasullo.CutoffAverages

open MeasureTheory Filter

namespace RiemannMasullo.CutoffAverages

/-- A summable uniform majorant permits averaging a countable orbital series termwise.
Only finiteness, not normalization or compact support, is needed of the radius law. -/
theorem integrable_tsum_and_hasSum_integral_of_uniform_bound
    {X ι : Type*} [MeasurableSpace X] [Countable ι] (ν : Measure X) [IsFiniteMeasure ν]
    (M : ι → X → ℂ) (b : ι → ℝ) (hM : ∀ i, Measurable (M i)) (hb : Summable b)
    (hbound : ∀ i, ∀ᵐ r ∂ν, ‖M i r‖ ≤ b i) :
    Integrable (fun r ↦ ∑' i, M i r) ν ∧
      HasSum (fun i ↦ ∫ r, M i r ∂ν) (∫ r, ∑' i, M i r ∂ν) := by
  have hall : ∀ᵐ r ∂ν, ∀ i, ‖M i r‖ ≤ b i := ae_all_iff.mpr hbound
  constructor
  · apply Integrable.of_bound (C := ∑' i, b i)
    · exact (Measurable.tsum hM).aestronglyMeasurable
    · filter_upwards [hall] with r hr
      have hn : Summable (fun i ↦ ‖M i r‖) := hb.of_norm_bounded fun i ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hr i
      exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_mono hb hr)
  · apply hasSum_integral_of_dominated_convergence (fun i _ ↦ b i)
      (fun i ↦ (hM i).aestronglyMeasurable) hbound (ae_of_all _ fun _ ↦ hb)
      (integrable_const _)
    filter_upwards [hall] with r hr
    exact (hb.of_norm_bounded hr).hasSum

end RiemannMasullo.CutoffAverages

open Filter MeasureTheory
open scoped Topology

namespace RiemannMasullo.CutoffAverages

/-- Probability averages preserve a logarithmic asymptotic when their support
escapes to infinity and their logarithmic radius about the center vanishes.
Only the eventual integrability of the original observable is needed. -/
theorem tendsto_average_sub_log_smul {ι X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {l : Filter ι}
    {M : ℝ → E} {A B : E} {lo center err : ι → ℝ}
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (radius : X → ℝ)
    (hM : Tendsto (fun r => M r - Real.log r • A) atTop (𝓝 B))
    (hlo : Tendsto lo l atTop) (herr : Tendsto err l (𝓝 0))
    (hsupp : ∀ᶠ i in l, ∀ᵐ r ∂μ i, lo i ≤ radius r)
    (hlog : ∀ᶠ i in l, ∀ᵐ r ∂μ i, |Real.log (radius r) - Real.log (center i)| ≤ err i)
    (hint : ∀ᶠ i in l, Integrable (M ∘ radius) (μ i)) :
    Tendsto (fun i => (∫ r, M (radius r) ∂μ i) - Real.log (center i) • A) l (𝓝 B) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 (Metric.tendsto_nhds.mp hM (ε / 2) hhalf)
  have hw : Tendsto (fun i => err i * ‖A‖) l (𝓝 0) := by
    simpa using herr.mul (tendsto_const_nhds (x := ‖A‖))
  filter_upwards [(tendsto_atTop.1 hlo R), hsupp, hlog, hint,
    hw.eventually (gt_mem_nhds hhalf)] with i hi hs hl hm he
  let c := Real.log (center i) • A + B
  have hb : ∀ᵐ r ∂μ i, ‖M (radius r) - c‖ ≤ ε / 2 + err i * ‖A‖ := by
    filter_upwards [hs, hl] with r hr hrd
    have ht := hR (radius r) (hi.trans hr)
    rw [dist_eq_norm] at ht
    calc
      ‖M (radius r) - c‖ = ‖(M (radius r) - Real.log (radius r) • A - B) +
          (Real.log (radius r) - Real.log (center i)) • A‖ := by
            congr 1
            dsimp [c]
            rw [sub_smul]
            abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ht.le (by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hrd (norm_nonneg A)))
  have hav := norm_integral_le_of_norm_le_const hb
  change Integrable (fun x ↦ M (radius x)) (μ i) at hm
  rw [integral_sub hm (integrable_const c)] at hav
  simp only [integral_const, probReal_univ, one_smul, mul_one] at hav
  change dist ((∫ r, M (radius r) ∂μ i) - Real.log (center i) • A) B < ε
  rw [dist_eq_norm, sub_sub]
  exact hav.trans_lt (by linarith)

end RiemannMasullo.CutoffAverages
