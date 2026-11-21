module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

public section

open Set Filter Topology

namespace RiemannMasullo

/-- A continuous linear map from a Hilbert space to a Banach space is compact if
the squared norms of the images of its Hilbert basis vectors are summable. -/
private theorem isCompactOperator_of_summable_sq_norm_hilbertBasis
    {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {ι : Type*}
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] X) (hT : Summable fun i ↦ ‖T (b i)‖ ^ 2) :
    IsCompactOperator T := by
  classical
  let A (i : ι) : H →L[ℂ] X := (innerSL ℂ (b i)).smulRight (T (b i))
  let K := compactOperator (RingHom.id ℂ) H X
  have hA (i : ι) : A i ∈ K := by
    let R : ℂ →L[ℂ] X := (ContinuousLinearMap.id ℂ ℂ).smulRight (T (b i))
    exact (isCompactOperator_of_locallyCompactSpace_rng R).comp_clm (innerSL ℂ (b i))
  change T ∈ {f : H →L[ℂ] X | IsCompactOperator f}
  rw [← isClosed_setOfPred_isCompactOperator.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hε₂ : 0 < ε / 2 := half_pos hε
  have hlim : Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, ‖T (b i)‖ ^ 2) atTop
      (𝓝 (∑' i, ‖T (b i)‖ ^ 2)) := hT.hasSum
  obtain ⟨s, hs⟩ := (hlim.eventually (Metric.ball_mem_nhds _ (pow_pos hε₂ 2))).exists
  have hgap : (∑' i, ‖T (b i)‖ ^ 2) - (∑ i ∈ s, ‖T (b i)‖ ^ 2) ≤ (ε / 2) ^ 2 := by
    rw [dist_comm, Real.dist_eq] at hs
    exact (le_abs_self _).trans hs.le
  refine ⟨∑ i ∈ s, A i, K.sum_mem fun i _ ↦ hA i, ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ((T - ∑ i ∈ s, A i).opNorm_le_bound hε₂.le fun x ↦ ?_) (half_lt_self hε)
  have hsum : HasSum (fun i ↦ A i x) (T x) := by
    simpa only [A, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      ← b.repr_apply_apply, map_smul] using T.hasSum (b.hasSum_repr x)
  have hsum' : Tendsto (fun t : Finset ι ↦ ∑ i ∈ t, A i x) atTop (𝓝 (T x)) := hsum
  have ht : Tendsto (fun t : Finset ι ↦ (∑ i ∈ t, A i x) - ∑ i ∈ s, A i x) atTop
      (𝓝 (T x - ∑ i ∈ s, A i x)) := hsum'.sub tendsto_const_nhds
  simp only [sub_apply, sum_apply]
  apply le_of_tendsto ht.norm
  filter_upwards [eventually_ge_atTop s] with t hst
  rw [← Finset.sum_sdiff hst (f := fun i ↦ A i x), add_sub_cancel_right]
  refine (norm_sum_le _ _).trans ?_
  simp only [A, ContinuousLinearMap.smulRight_apply, norm_smul, innerSL_apply_apply]
  apply (sq_le_sq₀ (Finset.sum_nonneg fun i _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg hε₂.le (norm_nonneg x))).mp
  have htail : ∑ i ∈ t \ s, ‖T (b i)‖ ^ 2 ≤ (ε / 2) ^ 2 := by
    have h := hT.sum_le_tsum t fun i _ ↦ sq_nonneg ‖T (b i)‖
    rw [← Finset.sum_sdiff hst (f := fun i ↦ ‖T (b i)‖ ^ 2)] at h
    exact (le_sub_iff_add_le.mpr h).trans hgap
  calc
    _ ≤ (∑ i ∈ t \ s, ‖inner ℂ (b i) x‖ ^ 2) * ∑ i ∈ t \ s, ‖T (b i)‖ ^ 2 :=
      (t \ s).sum_mul_sq_le_sq_mul_sq _ _
    _ ≤ ‖x‖ ^ 2 * (ε / 2) ^ 2 := mul_le_mul (b.orthonormal.sum_inner_products_le x) htail
        (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- An absolutely summing operator from a Hilbert space into a Banach space
is compact. -/
theorem isCompactOperator_of_hilbert_absolutelySumming
    {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : H →L[ℂ] X) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ (n : ℕ) (x : Fin n → H) (M : ℝ), 0 ≤ M →
      (∀ φ : H →L[ℂ] ℂ, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ≤ M) →
      ∑ i, ‖T (x i)‖ ≤ C * M) : IsCompactOperator T := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply isCompactOperator_of_summable_sq_norm_hilbertBasis b T
  refine summable_of_sum_le (c := C ^ 2) (fun i ↦ sq_nonneg _) fun s ↦ ?_
  let e := Fintype.equivFin ↥s
  let a (i : Fin (Fintype.card ↥s)) : H := (‖T (b (e.symm i))‖ : ℂ) • b (e.symm i)
  let L : ℝ := ∑ i ∈ s, ‖T (b i)‖ ^ 2
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have h := hT (Fintype.card ↥s) a (√L) (Real.sqrt_nonneg _) fun φ hφ ↦ ?_
  · have hTa : ∑ i, ‖T (a i)‖ = L := by
      simp only [a, map_smul, norm_smul, Complex.norm_real, norm_norm, ← pow_two]
      rw [e.symm.sum_comp (fun i : s ↦ ‖T (b i)‖ ^ 2)]
      exact (Finset.sum_subtype s (fun _ ↦ Iff.rfl) (fun i ↦ ‖T (b i)‖ ^ 2)).symm
    rw [hTa] at h
    by_cases hzero : L = 0
    · change L ≤ C ^ 2
      exact hzero ▸ sq_nonneg C
    · have hpos := Real.sqrt_pos_of_pos (lt_of_le_of_ne hL (Ne.symm hzero))
      have hroot : √L ≤ C := (mul_le_mul_iff_right₀ hpos).mp (by
        rw [← pow_two, Real.sq_sqrt hL]
        simpa only [mul_comm] using h)
      exact (Real.sq_sqrt hL).symm.trans_le
        ((sq_le_sq₀ hpos.le hC).mpr hroot)
  · let y := (InnerProductSpace.toDual ℂ H).symm φ
    have hy : ‖y‖ ≤ 1 := ((InnerProductSpace.toDual ℂ H).symm.norm_map φ).trans_le hφ
    have hφa (i : Fin (Fintype.card ↥s)) :
        ‖φ (a i)‖ = ‖T (b (e.symm i))‖ * ‖inner ℂ (b (e.symm i)) y‖ := by
      simp only [a, map_smul, norm_smul, Complex.norm_real, norm_norm]
      rw [← InnerProductSpace.toDual_symm_apply, norm_inner_symm y]
    simp only [hφa]
    rw [e.symm.sum_comp (fun i : s ↦ ‖T (b i)‖ * ‖inner ℂ (b i) y‖)]
    rw [← Finset.sum_subtype s (fun _ ↦ Iff.rfl)
      (fun i ↦ ‖T (b i)‖ * ‖inner ℂ (b i) y‖)]
    apply Real.le_sqrt_of_sq_le
    calc
      _ ≤ L * ∑ i ∈ s, ‖inner ℂ (b i) y‖ ^ 2 := s.sum_mul_sq_le_sq_mul_sq _ _
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left
        ((b.orthonormal.sum_inner_products_le y).trans (by
          simpa using (sq_le_sq₀ (norm_nonneg y) zero_le_one).mpr hy)) hL
      _ = L := mul_one _

end RiemannMasullo
