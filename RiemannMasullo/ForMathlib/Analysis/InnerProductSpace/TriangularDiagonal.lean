module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # The diagonal of a triangular map on a Gram–Schmidt family

Let `v` be a family of vectors of a complex inner product space, indexed by a well-order. A map
`R` is *triangular* for the pairings against `v`, with diagonal `r`, when for every `n` and every
`f` orthogonal to all `v i` with `i < n` the pairing of `R f` with `v n` is `r n` times the
pairing of `f` with `v n`. Multiplication by a function is triangular in this sense for the
evaluations of a function space at a sequence of points, with the derivatives at a repeated
point taken in increasing order, and its diagonal is the sequence of its values at the points.

* `inner_map_self_of_triangular`: a vector of the span of `v i`, `i ≤ n`, that is orthogonal to
  `v i` for `i < n` satisfies `⟪κ, R κ⟫ = r n * ⟪κ, κ⟫`.
* `inner_gramSchmidtNormed_map_of_triangular`: so the normalized Gram–Schmidt vectors of `v`
  have `⟪κ n, R (κ n)⟫ = r n`. No independence or separation of the `v n` is assumed.
* `sum_norm_sq_map_gramSchmidtNormed_le`, `summable_norm_sq_map_gramSchmidtNormed`: if moreover
  `‖A f‖ ^ 2 ≤ c * re ⟪f, R f⟫` for all `f`, then `∑ ‖A (κ n)‖ ^ 2 ≤ c * ∑ re (r n)`. When the
  `κ n` span the orthogonal complement of the common kernel of the pairings, the left side is
  the squared Hilbert–Schmidt norm of `A` on that complement. -/

@[expose] public section

open Submodule InnerProductSpace
open scoped InnerProductSpace

namespace RiemannMasullo

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- A triangular map has a prescribed diagonal entry on every vector of the span of the first
vectors that is orthogonal to the earlier ones. -/
theorem inner_map_self_of_triangular (v : ι → E) (R : E → E) (r : ι → ℂ)
    (hR : ∀ n f, (∀ i < n, ⟪v i, f⟫_ℂ = 0) → ⟪v n, R f⟫_ℂ = r n * ⟪v n, f⟫_ℂ)
    (n : ι) (κ : E) (hlow : ∀ i < n, ⟪v i, κ⟫_ℂ = 0) (hmem : κ ∈ span ℂ (v '' Set.Iic n)) :
    ⟪κ, R κ⟫_ℂ = r n * ⟪κ, κ⟫_ℂ := by
  have hperp : ∀ i ≤ n, ⟪v i, R κ - r n • κ⟫_ℂ = 0 := by
    intro i hi
    rw [inner_sub_right, inner_smul_right]
    rcases hi.lt_or_eq with hlt | heq
    · rw [hR i κ (fun l hl ↦ hlow l (hl.trans hlt)), hlow i hlt]
      simp
    · rw [heq, hR n κ hlow, sub_self]
  have hspan : ∀ w ∈ span ℂ (v '' Set.Iic n), ⟪w, R κ - r n • κ⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hperp i hi
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h := hspan κ hmem
  rwa [inner_sub_right, inner_smul_right, sub_eq_zero] at h

/-- The normalized Gram–Schmidt vectors are orthogonal to the earlier vectors of the family. -/
theorem inner_left_gramSchmidtNormed_eq_zero (v : ι → E) {i n : ι} (hin : i < n) :
    ⟪v i, gramSchmidtNormed ℂ v n⟫_ℂ = 0 := by
  have h : ⟪gramSchmidt ℂ v n, v i⟫_ℂ = 0 := gramSchmidt_inv_triangular ℂ v hin
  rw [gramSchmidtNormed, inner_smul_right, ← inner_conj_symm, h]
  simp

/-- The normalized Gram–Schmidt vectors lie in the span of the family up to their index. -/
theorem gramSchmidtNormed_mem_span_Iic (v : ι → E) (n : ι) :
    gramSchmidtNormed ℂ v n ∈ span ℂ (v '' Set.Iic n) :=
  Submodule.smul_mem _ _ (gramSchmidt_mem_span ℂ v le_rfl)

/-- A triangular map has its diagonal on the normalized Gram–Schmidt vectors of the family. -/
theorem inner_gramSchmidtNormed_map_of_triangular (v : ι → E) (R : E → E) (r : ι → ℂ)
    (hR : ∀ n f, (∀ i < n, ⟪v i, f⟫_ℂ = 0) → ⟪v n, R f⟫_ℂ = r n * ⟪v n, f⟫_ℂ)
    {n : ι} (hn : gramSchmidtNormed ℂ v n ≠ 0) :
    ⟪gramSchmidtNormed ℂ v n, R (gramSchmidtNormed ℂ v n)⟫_ℂ = r n := by
  rw [inner_map_self_of_triangular v R r hR n _
      (fun i hi ↦ inner_left_gramSchmidtNormed_eq_zero v hi) (gramSchmidtNormed_mem_span_Iic v n),
    inner_self_eq_norm_sq_to_K, gramSchmidtNormed_unit_length' hn]
  simp

open Classical in
/-- If `A` is dominated by the real part of the form of a triangular map `R`, the squares of
the norms of `A` on the normalized Gram–Schmidt vectors are bounded by the real parts of the
diagonal of `R`. -/
theorem sum_norm_sq_map_gramSchmidtNormed_le (v : ι → E) (A R : E → E) (r : ι → ℂ) {c : ℝ}
    (hR : ∀ n f, (∀ i < n, ⟪v i, f⟫_ℂ = 0) → ⟪v n, R f⟫_ℂ = r n * ⟪v n, f⟫_ℂ)
    (hA : ∀ f, ‖A f‖ ^ 2 ≤ c * (⟪f, R f⟫_ℂ).re) (s : Finset ι) :
    ∑ n ∈ s, ‖A (gramSchmidtNormed ℂ v n)‖ ^ 2 ≤
      c * ∑ n ∈ s with gramSchmidtNormed ℂ v n ≠ 0, (r n).re := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  have h := hA (gramSchmidtNormed ℂ v n)
  by_cases hn : gramSchmidtNormed ℂ v n = 0
  · rw [hn, inner_zero_left, Complex.zero_re, mul_zero] at h
    simpa [hn] using h
  · rw [inner_gramSchmidtNormed_map_of_triangular v R r hR hn] at h
    simpa [hn] using h

/-- If `A` is dominated by the real part of the form of a triangular map whose diagonal has
nonnegative summable real parts, then `A` is square summable on the normalized Gram–Schmidt
vectors, with the sum of the real parts of the diagonal as a bound. -/
theorem summable_norm_sq_map_gramSchmidtNormed (v : ι → E) (A R : E → E) (r : ι → ℂ) {c : ℝ}
    (hc : 0 ≤ c)
    (hR : ∀ n f, (∀ i < n, ⟪v i, f⟫_ℂ = 0) → ⟪v n, R f⟫_ℂ = r n * ⟪v n, f⟫_ℂ)
    (hA : ∀ f, ‖A f‖ ^ 2 ≤ c * (⟪f, R f⟫_ℂ).re)
    (hr₀ : ∀ n, 0 ≤ (r n).re) (hr : Summable fun n ↦ (r n).re) :
    Summable (fun n ↦ ‖A (gramSchmidtNormed ℂ v n)‖ ^ 2) ∧
      ∑' n, ‖A (gramSchmidtNormed ℂ v n)‖ ^ 2 ≤ c * ∑' n, (r n).re := by
  classical
  have hbound : ∀ s : Finset ι,
      ∑ n ∈ s, ‖A (gramSchmidtNormed ℂ v n)‖ ^ 2 ≤ c * ∑' n, (r n).re := by
    intro s
    refine (sum_norm_sq_map_gramSchmidtNormed_le v A R r hR hA s).trans
      (mul_le_mul_of_nonneg_left ?_ hc)
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s)
      (fun n _ _ ↦ hr₀ n)).trans (hr.sum_le_tsum s (fun n _ ↦ hr₀ n))
  have hsum : Summable (fun n ↦ ‖A (gramSchmidtNormed ℂ v n)‖ ^ 2) :=
    summable_of_sum_le (fun n ↦ sq_nonneg _) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end RiemannMasullo
