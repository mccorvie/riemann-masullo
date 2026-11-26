module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWActualCutoffs
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWJetTrials
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The actual Taylor jet system of the rational real weighted band -/

public noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace RiemannMasullo.RealPWBand

/-- Difference quotients converge pointwise on the complete band. Banach–Steinhaus
therefore gives a complex continuous linear functional for each real derivative. -/
private theorem exists_evaluationJet (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) (k : ℕ) :
    ∀ x : ℝ, ∃ L : space Y hμ →L[ℂ] ℂ, ∀ f,
      L f = iteratedDeriv k (fun t ↦ evaluation Y hμ t f) x := by
  induction k with
  | zero => exact fun x ↦ ⟨evaluation Y hμ x, fun f ↦ by simp⟩
  | succ k ih =>
    choose J hJ using ih
    intro x
    let Q (r : ℝ) : space Y hμ →L[ℂ] ℂ := r⁻¹ • (J (x+r) - J x)
    have hQ : Tendsto (fun r f ↦ Q r f) (𝓝[≠] (0 : ℝ))
        (𝓝 (fun f ↦ iteratedDeriv (k+1) (fun t ↦ evaluation Y hμ t f) x)) := by
      apply tendsto_pi_nhds.mpr
      intro f
      have h := (contDiff_nat_iff_iteratedDeriv.mp (contDiff_evaluation Y hμ f (k+1))).2
        k (Nat.lt_succ_self k) x
      simpa only [Q, smul_apply, sub_apply, hJ,
        iteratedDeriv_succ] using h.hasDerivAt.tendsto_slope_zero
    exact ⟨continuousLinearMapOfTendsto Q hQ, fun _ ↦ rfl⟩

/-- Unnormalized derivative, for use with jet systems indexed by derivative order. -/
def evaluationJet (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) (k : ℕ) (x : ℝ) :
    space Y hμ →L[ℂ] ℂ := (exists_evaluationJet Y hμ k x).choose

@[simp] theorem evaluationJet_apply (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (k : ℕ) (x : ℝ) (f : space Y hμ) :
    evaluationJet Y hμ k x f = iteratedDeriv k (fun t ↦ evaluation Y hμ t f) x :=
  (exists_evaluationJet Y hμ k x).choose_spec f

/-- No completeness of a proposed jet expansion is assumed: evenness kills the odd
orders and analyticity turns the resulting infinite order zero into an identically zero trace. -/
theorem eq_zero_of_evaluationJet_tail (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (hac : μ ≪ volume) (n : ℕ) (f : space Y hμ)
    (hlower : ∀ k < n, iteratedDeriv (2*k) (fun t ↦ evaluation Y hμ t f) 0 = 0)
    (htail : ∀ j, evaluationJet Y hμ (2*(n+j)) 0 f = 0) : f = 0 := by
  let F : ℝ → ℂ := fun t ↦ evaluation Y hμ t f
  have hall (k : ℕ) : iteratedDeriv k F 0 = 0 := by
    rcases Nat.even_or_odd k with ⟨i, hi⟩ | ho
    · have hk : k = 2*i := by omega
      by_cases hi' : i < n
      · simpa only [hk, F] using hlower i hi'
      · have he : 2*(n+(i-n)) = k := by omega
        have hz := htail (i-n)
        rw [evaluationJet_apply, he] at hz
        exact hz
    · have href : (fun t ↦ F (-t)) = F := funext (evaluation_even Y hμ f)
      have h := iteratedDeriv_comp_neg k F 0
      simpa only [href, neg_zero, ho.neg_one_pow, neg_one_smul, CharZero.eq_neg_self_iff] using h
  have ha (x : ℝ) : AnalyticAt ℝ F x := analyticOnNhd_evaluation Y hY hμ f x (mem_univ _)
  have hF : F = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 ha).mp
    (ENat.eq_top_iff_forall_ge.mpr fun k ↦
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha 0)).mpr fun i _ ↦ hall i)
  have hre : F =ᵐ[μ] (f.val : ℝ → ℂ) := evaluation_ae Y hμ hac f
  rw [hF] at hre
  apply Subtype.ext
  exact Lp.ext (hre.symm.trans (Lp.coeFn_zero ℂ 2 μ).symm)

end RiemannMasullo.RealPWBand

namespace RiemannMasullo.Isolated

private theorem independentOfTriangular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [LinearOrder ι] (L : ι → E →L[ℂ] ℂ)
    (hw : ∀ j, ∃ u, (∀ i < j, L i u = 0) ∧ L j u ≠ 0) : LinearIndependent ℂ L := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc j hj
  by_contra hn
  let S := s.filter (fun i ↦ c i ≠ 0)
  have hS : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hn⟩⟩
  let m := S.max' hS
  have hm : m ∈ S := S.max'_mem hS
  obtain ⟨hms, hcm⟩ := Finset.mem_filter.mp hm
  obtain ⟨u, hl, hd⟩ := hw m
  have h := congrArg (fun T : E →L[ℂ] ℂ ↦ T u) hc
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, zero_apply] at h
  rw [Finset.sum_eq_single m] at h
  · exact (mul_ne_zero hcm hd) h
  · intro i hi him
    by_cases hz : c i = 0
    · simp [hz]
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨hi, hz⟩
      rw [hl i (lt_of_le_of_ne (S.le_max' i hiS) him), mul_zero]
  · exact fun hnot ↦ (hnot hms).elim

private theorem evaluationJet_coordWitness {Y : ℝ} (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (φ : 𝓢(ℝ, ℂ)) (hφ : φ 0 ≠ 0)
    (hA : AnalyticAt ℝ (φ : ℝ → ℂ) 0) (k : ℕ) (f : RealPWBand.space Y hμ)
    (hf : ∀ t, RealPWBand.evaluation Y hμ t f = t^k • φ t) :
    (∀ i < k, RealPWBand.evaluationJet Y hμ i 0 f = 0) ∧
      RealPWBand.evaluationJet Y hμ k 0 f ≠ 0 := by
  let F : ℝ → ℂ := fun t ↦ RealPWBand.evaluation Y hμ t f
  have ha : AnalyticAt ℝ F 0 := RealPWBand.analyticOnNhd_evaluation Y hY hμ f 0 (mem_univ _)
  have ho : analyticOrderAt F 0 = (k : ℕ) := by
    apply ha.analyticOrderAt_eq_natCast.mpr
    refine ⟨(φ : ℝ → ℂ), hA, hφ, Eventually.of_forall ?_⟩
    intro t
    simpa only [sub_zero] using hf t
  obtain ⟨hl, hd⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mp ho
  exact ⟨fun i hi ↦ (RealPWBand.evaluationJet_apply ..).trans (hl i hi), by
    rw [RealPWBand.evaluationJet_apply]; exact hd⟩

/-- The actual even Taylor derivatives remaining after forced vanishing are
linearly independent. The witnesses are admissible weighted Schwartz monomials. -/
theorem realPWInterval_evaluationJet_tail_linearIndependent {Y α s : ℝ}
    (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) :
    LinearIndependent ℂ (fun j : ℕ ↦ RealPWBand.evaluationJet Y
      (volume_le_realPWIntervalMeasure α s hs) (2 * (realPWOriginJetCount α + j)) 0) := by
  obtain ⟨φ, he, hb, hr⟩ := exists_evenSchwartz_band_trial hY (half_pos hY)
  have hφ₀ : φ 0 ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] at hr
    linarith
  have hφ : ∀ y ∉ Icc (-Y) Y, (𝓕 φ) y = 0 := by
    intro y hy
    rw [SchwartzMap.fourier_coe]
    by_contra h
    exact hy (Ioo_subset_Icc_self (hb h))
  have hA : AnalyticAt ℝ (φ : ℝ → ℂ) 0 := by
    obtain ⟨u, hu⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y φ he hφ
      (le_refl volume) (φ.memLp 2 volume)
    rw [← hu]
    exact RealPWBand.analyticOnNhd_evaluation Y hY.le (le_refl volume) u 0 (mem_univ _)
  let n := realPWOriginJetCount α
  let hμ := volume_le_realPWIntervalMeasure α s hs
  apply independentOfTriangular
  intro j
  have hj : -1 < (↑(4*(n + j)) : ℝ) - 2*α := by
    push_cast
    have hn := realPWOriginJetCount_spec α
    change -1 < 4 * (n : ℝ) - 2*α at hn
    linarith [show 0 ≤ (j : ℝ) from Nat.cast_nonneg j]
  obtain ⟨f, hf⟩ := exists_realPWInterval_coordinateTrial ha hs φ he hφ (n+j) hj
  obtain ⟨hl, he⟩ := evaluationJet_coordWitness hY.le hμ φ hφ₀ hA (2*(n+j)) f hf
  exact ⟨f, fun i hij ↦ hl _ (by omega), he⟩

end RiemannMasullo.Isolated
