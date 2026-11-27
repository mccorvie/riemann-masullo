module
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-! # Nuclear rank-one series and their traces

Absolutely summable rank-one costs give both nuclearity and a trace formula.
The proof uses trace-norm convergence of finite subseries and continuity of the
Hilbert trace; no orthogonality or basis normalization is assumed.
-/

public noncomputable section
open Set Filter
open scoped Topology
namespace RiemannMasullo

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace-norm convergence controls the actual Hilbert trace. -/
private theorem tendsto_hilbertTrace_of_traceNorm_sub {ι : Type*} {l : Filter ι}
    (S : ι → nuclearEndomorphisms H) (T : nuclearEndomorphisms H)
    (h : Tendsto (fun i ↦ traceNorm (T - S i)) l (𝓝 0)) :
    Tendsto (fun i ↦ hilbertTrace (S i)) l (𝓝 (hilbertTrace T)) := by
  obtain ⟨f, hf⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i ↦ norm_nonneg _) ?_ h
  intro i
  calc
    ‖hilbertTrace (S i) - hilbertTrace T‖ = ‖hilbertTrace (T - S i)‖ := by
      simp only [← hf, map_sub, norm_sub_rev]
    _ ≤ traceNorm (T - S i) := norm_hilbertTrace_le _

/-- An absolutely summable family of rank-one maps is nuclear, and its Hilbert
trace is the sum of the evaluations, without an orthogonality hypothesis. -/
theorem nuclear_rankOne_series_trace {ι : Type*}
    (φ : ι → H →L[ℂ] ℂ) (y : ι → H)
    (hc : Summable (fun i ↦ ‖φ i‖ * ‖y i‖)) :
    ∃ h : IsNuclearOperator (∑' i, (φ i).smulRight (y i)),
      traceNorm ⟨_, h⟩ ≤ ∑' i, ‖φ i‖ * ‖y i‖ ∧
      HasSum (fun i ↦ φ i (y i)) (hilbertTrace ⟨_, h⟩) := by
  classical
  let S (i : ι) : nuclearEndomorphisms H :=
    ⟨(φ i).smulRight (y i), smulRight_mem_nuclearEndomorphisms _ _⟩
  let T := ∑' i, (φ i).smulRight (y i)
  have hs : HasSum (fun i ↦ (S i).val) T := by
    apply Summable.hasSum
    apply Summable.of_norm
    simpa only [S, ContinuousLinearMap.norm_smulRight_apply] using hc
  have hb (i : ι) : traceNorm (S i) ≤ ‖φ i‖ * ‖y i‖ := (traceNorm_smulRight _ _).le
  obtain ⟨hT, hbound⟩ := traceNorm_le_of_hasSum S T hs _ hc hb
  obtain ⟨_, hK, _, hlim⟩ := traceNorm_tendsto_of_hasSum_subseries S T hs _ hc hb
    (fun K : Finset ι ↦ (K : Set ι)) atTop (fun i ↦ by
      filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with K hK
      exact hK (by simp))
  have hpart (K : Finset ι) :
      (⟨∑' i : (K : Set ι), (S i.val).val, hK K⟩ : nuclearEndomorphisms H) = ∑ i ∈ K, S i := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, tsum_fintype]
    exact Finset.sum_finset_coe (fun i ↦ (S i).val) K
  simp_rw [hpart] at hlim
  have ht := tendsto_hilbertTrace_of_traceNorm_sub (fun K : Finset ι ↦ ∑ i ∈ K, S i) ⟨T,hT⟩ hlim
  refine ⟨hT, hbound, ?_⟩
  obtain ⟨f, hf⟩ := hilbertTrace_linear (H := H)
  have he (K : Finset ι) : hilbertTrace (∑ i ∈ K, S i) = ∑ i ∈ K, φ i (y i) := by
    simp only [← hf, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hf]
    exact hilbertTrace_smulRight (φ i) (y i)
  change Tendsto (fun K : Finset ι ↦ ∑ i ∈ K, φ i (y i)) atTop (𝓝 (hilbertTrace ⟨T,hT⟩))
  simpa only [he] using ht

/-- Uniformly bounded rank-one projections with unit diagonal admit nuclear
multipliers for every absolutely summable scalar symbol, with the expected trace. -/
theorem nuclear_tsum_smul_rankOne {ι : Type*}
    (P : ι → H →L[ℂ] H) (φ : ι → H →L[ℂ] ℂ) (v : ι → H)
    (hP : ∀ i, (φ i).smulRight (v i) = P i) (hdiag : ∀ i, φ i (v i) = 1)
    (C : ℝ) (hC : ∀ i, ‖P i‖ ≤ C) (c : ι → ℂ) (hc : Summable (fun i ↦ ‖c i‖)) :
    ∃ h : IsNuclearOperator (∑' i, c i • P i),
      traceNorm ⟨_, h⟩ ≤ C * (∑' i, ‖c i‖) ∧ HasSum c (hilbertTrace ⟨_, h⟩) := by
  have hcost (i : ι) : ‖φ i‖ * ‖v i‖ ≤ C := by
    rw [← ContinuousLinearMap.norm_smulRight_apply, hP]
    exact hC i
  have hterm (i : ι) : ‖c i • φ i‖ * ‖v i‖ ≤ C * ‖c i‖ := by
    rw [norm_smul, mul_assoc, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hcost i) (norm_nonneg _)
  have hs : Summable (fun i : ι ↦ ‖c i • φ i‖ * ‖v i‖) :=
    (hc.mul_left C).of_nonneg_of_le (fun i ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) hterm
  obtain ⟨hn, hb, ht⟩ := nuclear_rankOne_series_trace (fun i ↦ c i • φ i) v hs
  have hclm (i : ι) : (c i • φ i).smulRight (v i) = c i • P i := by
    rw [← hP]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_assoc]
  simp_rw [hclm] at hn hb ht
  refine ⟨hn, ?_, ?_⟩
  · exact hb.trans ((hs.tsum_le_tsum hterm (hc.mul_left C)).trans_eq (tsum_mul_left))
  · simpa only [smul_apply, hdiag, smul_eq_mul, mul_one] using ht

end RiemannMasullo
