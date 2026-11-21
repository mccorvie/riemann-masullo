module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.LinearAlgebra.Dimension.LinearMap
import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.Compact.NormAttainment

/-!
# Nuclear convergence and Schatten classes

Masullo, Appendix C, §§C.3.5–C.3.6.
-/

@[expose] public noncomputable section

open Filter Function Set Topology TopologicalSpace UniformSpace
open scoped BigOperators InnerProductSpace NNReal TensorProduct

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section ProjectionConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section OrthogonalSummands

variable {ι : Type*} (V : ι → ClosedSubmodule ℂ H)

local notation "P(" i ")" => Submodule.starProjection (V i : Submodule ℂ H)
local notation "PairwiseOrthogonal" =>
  Pairwise (fun i j ↦ (V i : Submodule ℂ H) ⟂ (V j : Submodule ℂ H))

/-- Paper: Proposition C.3.5.1, p. 699. A pairwise orthogonal family of nonzero
closed subspaces of a separable Hilbert space has a countable index type. -/
theorem countable_orthogonalSummands [SeparableSpace H]
    (hV : PairwiseOrthogonal) (hne : ∀ i, V i ≠ ⊥) : Countable ι := by
  have exists_unit (i : ι) : ∃ x ∈ (V i : Submodule ℂ H), ‖x‖ = 1 := by
    have hi : (V i : Submodule ℂ H) ≠ ⊥ :=
      fun h ↦ hne i (ClosedSubmodule.toSubmodule_injective h)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
    exact ⟨(‖x‖⁻¹ : ℂ) • x, (V i : Submodule ℂ H).smul_mem _ hx, norm_smul_inv_norm hx0⟩
  choose u hu hunit using exists_unit
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (u i) (1 / 2))
    ?_ (fun _ ↦ Metric.isOpen_ball) (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))
  intro i j hij
  apply Metric.ball_disjoint_ball
  have hsq : dist (u i) (u j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq ℂ, (hV hij).inner_eq (hu i) (hu j), hunit i, hunit j]
    norm_num
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  apply (sq_le_sq₀ zero_le_one dist_nonneg).mp
  rw [hsq]
  norm_num

-- TODO(paper-gap): The proof on p. 701 calls each PᵢT finite-rank. A single
-- summand equal to ℓ²(ℕ) and T diagonal with entries 2^(-n-1) gives a counterexample.

omit [CompleteSpace H] in
/-- The canonical operator associated to an algebraic tensor has finite-dimensional range. -/
private theorem finiteDimensional_range_tensorToFiniteRank
    (z : StrongDual ℂ H ⊗[ℂ] H) :
    FiniteDimensional ℂ (tensorToFiniteRank z).toLinearMap.range := by
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
    apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ y)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ x, (tensorToFiniteRank_tmul φ y x).symm⟩
  | add z w hz hw =>
    rw [map_add, ContinuousLinearMap.toLinearMap_add]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)

/-- Paper: Proposition C.3.5.1(1), p. 699. Along any increasing cofinal sequence
of finite subsets, the finite sums of projected nuclear operators converge
in trace norm to the original operator. -/
theorem tendsto_traceNorm_sum_orthogonalProjections_mul [SeparableSpace H]
    (hV : PairwiseOrthogonal) (hne : ∀ i, V i ≠ ⊥)
    (hSOT : ∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x))
    (s : ℕ → Finset ι) (hs : Monotone s) (hcofinal : ∀ t, ∃ k, t ≤ s k)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun k ↦ traceNorm
      ((∑ i ∈ s k, (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ :
        nuclearEndomorphisms H)) - T)) atTop (𝓝 0) := by
  let Q (k : ℕ) : H →L[ℂ] H := (∑ i ∈ s k, P(i)) - 1
  have hQ : ∀ x, Tendsto (fun k ↦ Q k x) atTop (𝓝 0) := by
    intro x
    have hx := (hSOT x).comp (hs.tendsto_atTop_atTop hcofinal)
    simpa [Q, Function.comp_def] using hx.sub tendsto_const_nhds (b := x)
  have hP (i : ι) : IsStarProjection (P(i)) := isStarProjection_starProjection
  have hQ_norm (k : ℕ) : ‖Q k‖ ≤ 1 := by
    have hsum : IsStarProjection (∑ i ∈ s k, P(i)) := by
      refine IsStarProjection.sum (fun i _ ↦ hP i) ?_
      intro i _ j _ hij
      exact ((hP i).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (hP j).isSelfAdjoint).mpr
        (hV hij).starProjection_comp_starProjection
    simpa [Q, norm_sub_rev] using hsum.one_sub.norm_le _
  let product (k : ℕ) (A : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q k * A.val, mul_mem_nuclearEndomorphisms_left (Q k) A⟩
  have hsum (k : ℕ) :
      (∑ i ∈ s k, (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ :
        nuclearEndomorphisms H)) - T = product k T := by
    apply Subtype.ext
    simp [product, Q, sub_mul, Finset.sum_mul]
  simp_rw [hsum]
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := (traceNorm_normedSpaceCore (H := H)).toCore
  have hnonneg (A : nuclearEndomorphisms H) : 0 ≤ traceNorm A :=
    hcore.norm_nonneg A
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (half_pos hε)
  let F : nuclearEndomorphisms H :=
    ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  obtain ⟨_, hF⟩ := tendsto_traceNorm_mul_finiteRank Q hQ F.val
    (finiteDimensional_range_tensorToFiniteRank z)
  have hF' : Tendsto (fun k ↦ traceNorm (product k F)) atTop (𝓝 0) := hF
  filter_upwards [Metric.tendsto_nhds.mp hF' (ε / 2) (half_pos hε)] with k hk
  have hsplit : product k T = product k (T - F) + product k F := by
    apply Subtype.ext
    simp [product, mul_sub]
  have hbound : traceNorm (product k (T - F)) ≤ traceNorm (T - F) :=
    (traceNorm_mul_left_le (Q k) (T - F)).trans
      (by simpa using mul_le_mul_of_nonneg_right (hQ_norm k) (hnonneg (T - F)))
  have htriangle : traceNorm (product k T) ≤
      traceNorm (product k (T - F)) + traceNorm (product k F) := by
    rw [hsplit]
    exact hcore.norm_triangle _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product k F))] at hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product k T))]
  change traceNorm (T - F) < ε / 2 at hz
  linarith

/-- Paper: Proposition C.3.5.1(2), p. 699. The finite sums of the traces of
the projected operators converge to the trace of the original operator. -/
theorem tendsto_sum_hilbertTrace_orthogonalProjections_mul [SeparableSpace H]
    (hV : PairwiseOrthogonal) (hne : ∀ i, V i ≠ ⊥)
    (hSOT : ∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x))
    (s : ℕ → Finset ι) (hs : Monotone s) (hcofinal : ∀ t, ∃ k, t ≤ s k)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun k ↦ ∑ i ∈ s k,
      hilbertTrace ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [← htr, ← map_sum, ← map_sub]
  simp only [htr]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _)
    (tendsto_traceNorm_sum_orthogonalProjections_mul V hV hne hSOT s hs hcofinal T)

/-- Paper: Remark C.3.5.2, p. 699. The finite sums of pairwise orthogonal
projections converge strongly to the identity exactly when the algebraic
sum of the subspaces is dense.
The supremum is taken among submodules and only then viewed as a set: written with the set
ascription outside, Lean coerces each summand first and forms the union, for which the statement
is false (two coordinate axes in the plane). -/
theorem tendsto_sum_orthogonalProjections_iff_dense_iSup (hV : PairwiseOrthogonal) :
    (∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x)) ↔
      Dense (((⨆ i, V i : Submodule ℂ H) : Submodule ℂ H) : Set H) := by
  classical
  let Q (s : Finset ι) : H →L[ℂ] H := ∑ i ∈ s, P(i)
  constructor
  · intro h x
    refine mem_closure_of_tendsto (h x) (Eventually.of_forall fun s ↦ ?_)
    change (∑ i ∈ s, P(i)) x ∈ ⨆ i, (V i : Submodule ℂ H)
    rw [sum_apply]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i
      (Submodule.starProjection_apply_mem _ x)
  · intro hd x
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    -- Approximate x by a vector in the sum of finitely many summands.
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hd x) ε hε
    change y ∈ ⨆ i, (V i : Submodule ℂ H) at hy
    rw [iSup_eq_iSup_finset] at hy
    have hmono : Monotone (fun s : Finset ι ↦ ⨆ i ∈ s, (V i : Submodule ℂ H)) :=
      fun _ _ h ↦ iSup_le fun i ↦ iSup_le fun hi ↦ le_iSup_of_le i (le_iSup_of_le (h hi) le_rfl)
    obtain ⟨t, ht⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hy
    filter_upwards [eventually_ge_atTop t] with s hs
    have hrange : (⨆ i ∈ s, (V i : Submodule ℂ H)) ≤ (Q s).range := by
      refine iSup_le fun i ↦ iSup_le fun hi z hz ↦ ⟨z, ?_⟩
      change (∑ i ∈ s, P(i)) z = z
      rw [sum_apply, Finset.sum_eq_single_of_mem i hi]
      · exact Submodule.starProjection_eq_self_iff.mpr hz
      · intro j _ hji
        exact (Submodule.starProjection_apply_eq_zero_iff _).mpr ((hV hji.symm) hz)
    have hP (i : ι) : IsStarProjection (P(i)) := isStarProjection_starProjection
    have hQs : IsStarProjection (Q s) := by
      refine IsStarProjection.sum (fun i _ ↦ hP i) ?_
      intro i _ j _ hij
      exact ((hP i).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (hP j).isSelfAdjoint).mpr
        (hV hij).starProjection_comp_starProjection
    obtain ⟨hproj, hQ⟩ := isStarProjection_iff_eq_starProjection_range.mp hQs
    -- The projection onto the range of Q s is at least as close to x as y is.
    change dist (Q s x) x < ε
    rw [dist_comm, hQ, Submodule.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (hrange (hmono hs ht))).trans_lt hxy

end OrthogonalSummands

end ProjectionConvergence

section ApproximationNumbers

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Paper: (C.3.6.2), p. 704. The approximation number is the infimum of the
operator-norm errors of approximants of bounded finite rank.
Deviation: Indices start at zero, so index n allows rank at most n. The definition is
placed here for the singular-value statements in §C.3.5. -/
def approximationNumber (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  sInf {r | ∃ S : E →L[ℂ] F, Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}

/-- Paper: (C.3.6.2), p. 704. In finite dimensions the approximation
numbers agree with Mathlib's singular values, including the zero tail.
Deviation: This checks the rank cutoff and the zero-based indexing. -/
theorem approximationNumber_eq_singularValues [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) (n : ℕ) :
    approximationNumber T n = T.toLinearMap.singularValues n := by
  classical
  let errors : Set ℝ := {r | ∃ S : E →L[ℂ] F,
    Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}
  change sInf errors = _
  have hnonneg : (0 : ℝ) ∈ lowerBounds errors := by
    rintro r ⟨S, _, rfl⟩
    exact norm_nonneg _
  have hzero : Module.rank ℂ (0 : E →L[ℂ] F).toLinearMap.range ≤ (n : Cardinal) := by simp
  by_cases hlarge : Module.finrank ℂ T.toLinearMap.range ≤ n
  · have hrank : Module.rank ℂ T.toLinearMap.range ≤ (n : Cardinal) := by
      simpa only [← Module.finrank_eq_rank, Nat.cast_le] using hlarge
    rw [T.toLinearMap.singularValues_eq_zero_iff_le_finrank_range.mpr hlarge]
    apply le_antisymm
    · exact (csInf_le ⟨0, hnonneg⟩ ⟨T, hrank, rfl⟩).trans_eq (by simp)
    · exact le_csInf ⟨_, T, hrank, rfl⟩ hnonneg
  have hn := (Nat.lt_of_not_ge hlarge).trans_le T.toLinearMap.finrank_range_le
  let hSymm := T.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hSymm.eigenvectorBasis rfl
  let σ := T.toLinearMap.singularValues
  have hσ : ∀ i, 0 ≤ σ i := T.toLinearMap.singularValues_nonneg
  have hanti : Antitone σ := T.toLinearMap.singularValues_antitone
  -- In the eigenbasis of T†T, the squared norm of T x is a weighted sum of coordinates.
  have henergy (x : E) : ‖T x‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℂ E), σ i ^ 2 * ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
    rw [show ‖T x‖ ^ 2 = RCLike.re ⟪x, (T.toLinearMap.adjoint ∘ₗ T.toLinearMap) x⟫_ℂ by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, ← norm_sq_eq_re_inner]
      rfl]
    rw [← b.sum_inner_mul_inner, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← b.repr_apply_apply, hSymm.eigenvectorBasis_apply_self_apply rfl,
      ← T.toLinearMap.sq_singularValues_fin rfl i, b.repr_apply_apply]
    rw [mul_left_comm, RCLike.re_ofReal_mul, inner_mul_symm_re_eq_norm, norm_mul,
      ← inner_conj_symm x, RCLike.norm_conj, ← pow_two]
  let V (k : ℕ) := Submodule.span ℂ (b '' {i | (i : ℕ) < k})
  have hdim (k : ℕ) (hk : k ≤ Module.finrank ℂ E) : Module.finrank ℂ (V k) = k := by
    have hind := b.orthonormal.linearIndependent.comp (Fin.castLE hk) (Fin.castLE_injective hk)
    change Module.finrank ℂ (Submodule.span ℂ (b '' {i | (i : ℕ) < k})) = k
    rw [← Fin.range_castLE hk, ← Set.range_comp]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hind
  apply le_antisymm
  · -- Truncate T to the first n eigenvectors.
    let S := T.comp (V n).starProjection
    have hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) := by
      rw [← Module.finrank_eq_rank, Nat.cast_le]
      change Module.finrank ℂ (T.toLinearMap.comp (V n).starProjection.toLinearMap).range ≤ n
      rw [LinearMap.range_comp, Submodule.range_starProjection]
      exact (Submodule.finrank_map_le _ _).trans_eq (hdim n hn.le)
    refine (csInf_le ⟨0, hnonneg⟩ ⟨S, hS, rfl⟩).trans ?_
    rw [norm_sub_rev]
    apply ContinuousLinearMap.opNorm_le_bound _ (hσ n)
    intro x
    let y := (V n)ᗮ.starProjection x
    have hy : y ∈ (V n)ᗮ := ((V n)ᗮ.orthogonalProjectionOnto x).property
    have heq : (T - S) x = T y := by
      simp [S, y, map_sub]
    rw [heq]
    refine (show ‖T y‖ ≤ σ n * ‖y‖ from ?_).trans
      (mul_le_mul_of_nonneg_left ((V n)ᗮ.norm_starProjection_apply_le x) (hσ n))
    apply le_of_sq_le_sq _ (mul_nonneg (hσ n) (norm_nonneg _))
    rw [henergy, mul_pow, ← b.sum_sq_norm_inner_right y, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (i : ℕ) < n
    · have hz := ((V n).mem_orthogonal y).mp hy (b i)
          (Submodule.subset_span (Set.mem_image_of_mem _ hi))
      simp [hz]
    · exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (hσ i) (hσ n)).mpr (hanti (Nat.le_of_not_lt hi))) (sq_nonneg _)
  · refine le_csInf ⟨_, 0, hzero, rfl⟩ ?_
    rintro r ⟨S, hS, rfl⟩
    have hSdim : Module.finrank ℂ S.toLinearMap.range ≤ n := by
      simpa only [← Module.finrank_eq_rank, Nat.cast_le] using hS
    -- Every admissible S kills a nonzero vector in the span of the first n + 1 eigenvectors.
    let R := S.toLinearMap.rangeRestrict.comp (V (n + 1)).subtype
    have hker : R.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [hdim (n + 1) hn]
      exact Nat.lt_succ_of_le hSdim)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (x : E) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hxnorm : 0 < ‖(x : E)‖ := norm_pos_iff.mpr (fun h ↦ hx0 (Subtype.ext h))
    have hlower : σ n * ‖(x : E)‖ ≤ ‖T (x : E)‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      rw [henergy, mul_pow, ← b.sum_sq_norm_inner_right (x : E), Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (i : ℕ) ≤ n
      · exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (hσ n) (hσ i)).mpr (hanti hi)) (sq_nonneg _)
      · have hsupport := (b.toBasis.repr_support_subset_of_mem_span _ x.property)
        have hz : ⟪b i, (x : E)⟫_ℂ = 0 := by
          rw [← b.repr_apply_apply, ← b.coe_toBasis_repr_apply, ← Finsupp.notMem_support_iff]
          exact fun hs ↦ hi (Nat.lt_succ_iff.mp (hsupport hs))
        simp [hz]
    have hbound := (S - T).le_opNorm (x : E)
    rw [sub_apply, hSx, zero_sub, norm_neg] at hbound
    exact le_of_mul_le_mul_right (hlower.trans hbound) hxnorm

end ApproximationNumbers

section SingularValues

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Within any positive operator-norm distance of `A.adjoint` there is a compact operator.
The approximant is `A.adjoint` postcomposed with the orthogonal projection onto a
finite-dimensional subspace, so it factors through a locally compact space. -/
private theorem exists_isCompactOperator_norm_sub_adjoint_le (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : H →L[ℂ] H, IsCompactOperator C ∧ ‖A.adjoint - C‖ ≤ ε := by
  obtain ⟨t, -, ht_fin, ht_cover⟩ :=
    (hA.isCompact_closure_image_closedBall 1).finite_cover_balls hε
  let U : Submodule ℂ H := Submodule.span ℂ t
  have : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ ht_fin
  have : CompleteSpace U := FiniteDimensional.completeSpace ℂ U
  have : U.HasOrthogonalProjection := inferInstance
  have hnorm : ‖A - U.starProjection ∘L A‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : H := (‖x‖⁻¹ : ℂ) • x
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
          inv_mul_cancel₀ hx0.ne']
      have hBu : ‖(A - U.starProjection ∘L A) u‖ < ε := by
        have hu_ball : u ∈ Metric.closedBall (0 : H) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, hu]
        have hAu : A u ∈ closure (A '' Metric.closedBall (0 : H) 1) :=
          subset_closure ⟨u, hu_ball, rfl⟩
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht_cover hAu)
        have hdist : Metric.infDist (A u) (U : Set H) < ε :=
          (Metric.infDist_lt_iff ⟨0, Submodule.zero_mem U⟩).2
            ⟨y, Submodule.subset_span hy, Metric.mem_ball.mp hxy⟩
        rw [sub_apply, ContinuousLinearMap.comp_apply, ← dist_eq_norm,
          U.dist_starProjection_eq_infDist]
        exact hdist
      have hxeq : (‖x‖ : ℂ) • u = x := by
        simp only [u, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx0.ne'), one_smul]
      have hBx : ‖(A - U.starProjection ∘L A) x‖ =
          ‖x‖ * ‖(A - U.starProjection ∘L A) u‖ := by
        conv_lhs => rw [← hxeq]
        rw [(A - U.starProjection ∘L A).map_smul, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hx0.le]
      rw [hBx]
      calc
        ‖x‖ * ‖(A - U.starProjection ∘L A) u‖ ≤ ‖x‖ * ε :=
          mul_le_mul_of_nonneg_left hBu.le hx0.le
        _ = ε * ‖x‖ := mul_comm _ _
  refine ⟨A.adjoint ∘L U.starProjection, ?_, ?_⟩
  · have : LocallyCompactSpace U :=
      LocallyCompactSpace.of_finiteDimensional_of_complete ℂ U
    have hfac : A.adjoint ∘L U.starProjection =
        (A.adjoint ∘L U.subtypeL) ∘L U.orthogonalProjectionOnto := rfl
    rw [hfac]
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (A.adjoint ∘L U.subtypeL)).comp_clm U.orthogonalProjectionOnto
  · rw [← (isSelfAdjoint_starProjection U).adjoint_eq, ← ContinuousLinearMap.adjoint_comp,
      ← (ContinuousLinearMap.adjoint (E := H) (F := H)).map_sub,
      (ContinuousLinearMap.adjoint (E := H) (F := H)).norm_map]
    exact hnorm

/-- Paper: Lemma C.3.5.3(1), p. 700. The adjoint of a compact endomorphism is compact. -/
theorem isCompactOperator_adjoint_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) : IsCompactOperator A.adjoint := by
  have happrox : ∀ n : ℕ, ∃ C : H →L[ℂ] H,
      IsCompactOperator C ∧ ‖A.adjoint - C‖ ≤ 1 / (n + 1 : ℝ) := by
    intro n
    exact exists_isCompactOperator_norm_sub_adjoint_le A hA (by positivity)
  choose C hC hle using happrox
  refine isCompactOperator_of_tendsto (l := atTop) (F := C) ?_ (Eventually.of_forall hC)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  refine (hle n).trans_lt ?_
  have hbig : 1 / ε < (n : ℝ) + 1 :=
    lt_trans (lt_of_lt_of_le hN (Nat.cast_le.mpr hn)) (lt_add_one _)
  have hmul : 1 < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hbig
  rw [show (1 : ℝ) / (n + 1 : ℝ) = 1 / ((n : ℝ) + 1) by simp,
    div_lt_iff₀' (by positivity)]
  exact hmul

/-- Paper: Lemma C.3.5.3(1), p. 700. A compact endomorphism and its adjoint
have the same singular values at every index up to the Hilbert space dimension.
Deviation: The singular values use the approximation-number definition with zero-based indices. -/
theorem approximationNumber_adjoint (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber A n = approximationNumber A.adjoint n := by
  clear hA hn
  have rank_adjoint_le (S : H →L[ℂ] H)
      (hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal)) :
      Module.rank ℂ S.adjoint.toLinearMap.range ≤ (n : Cardinal) := by
    let V := S.toLinearMap.range
    have : FiniteDimensional ℂ V :=
      Module.rank_lt_aleph0_iff.mp (hS.trans_lt Cardinal.natCast_lt_aleph0)
    have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
    -- Factoring S through its range gives a factorization of its adjoint through V.
    have hfac : V.subtypeL.comp S.rangeRestrict = S := rfl
    have hadj : S.adjoint = S.rangeRestrict.adjoint.comp V.subtypeL.adjoint := by
      rw [← ContinuousLinearMap.adjoint_comp, hfac]
    rw [hadj]
    exact (LinearMap.rank_comp_le_left _ _).trans
      (S.rangeRestrict.adjoint.toLinearMap.rank_le_domain.trans hS)
  let errors (T : H →L[ℂ] H) : Set ℝ :=
    {r | ∃ S : H →L[ℂ] H, Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}
  have errors_subset (T : H →L[ℂ] H) : errors T ⊆ errors T.adjoint := by
    rintro _ ⟨S, hS, rfl⟩
    refine ⟨S.adjoint, rank_adjoint_le S hS, ?_⟩
    rw [← ContinuousLinearMap.adjoint.map_sub, LinearIsometryEquiv.norm_map]
  change sInf (errors A) = sInf (errors A.adjoint)
  apply congrArg sInf
  exact Set.Subset.antisymm (errors_subset A)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using errors_subset A.adjoint)

/-- Paper: Lemma C.3.5.3(2), p. 700. The first singular value of a compact
endomorphism equals its operator norm.
Deviation: The first approximation number has index zero. -/
theorem approximationNumber_zero_eq_opNorm (A : H →L[ℂ] H) (hA : IsCompactOperator A) :
    approximationNumber A 0 = ‖A‖ := by
  have hset : {r | ∃ S : H →L[ℂ] H, Module.rank ℂ S.toLinearMap.range ≤ ((0 : ℕ) : Cardinal) ∧
      r = ‖S - A‖} = {‖A‖} := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      have h0 : Module.rank ℂ S.toLinearMap.range = 0 := by
        rw [Nat.cast_zero] at hS
        exact le_zero_iff.mp hS
      rw [Submodule.rank_eq_zero, LinearMap.range_eq_bot] at h0
      have hS0 : S = 0 := ContinuousLinearMap.coe_injective h0
      simp [hS0]
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  unfold approximationNumber
  rw [hset, csInf_singleton]

-- TODO(paper-gap): The proof of (C.3.5.4) uses global weak continuity of the
-- quadratic form of a compact operator and weak compactness of the unit sphere.
-- The quadratic form is weakly continuous on bounded sets, and the closed unit
-- ball is weakly compact. The proof also writes the rank-one spectral
-- projector in (C.3.5.5) as a projection onto a kernel, and the tail span
-- argument can fail for repeated eigenvalues. The min-max identities still hold.
-- The polar isometry used in part (1) has initial space (ker A)ᗮ.

/-- The restriction of `A` to the orthogonal complement of a proper finite-dimensional
subspace has a maximizing unit vector. Its image is orthogonal to the images of all vectors
in the complement that are orthogonal to it. -/
private theorem exists_unit_maximizer_on_orthogonal (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    {n : ℕ} (hn : (n : Cardinal) < Module.rank ℂ H)
    {V : Submodule ℂ H} (hV : Module.rank ℂ V = (n : Cardinal)) :
    ∃ e ∈ Vᗮ, ‖e‖ = 1 ∧ ‖A e‖ = ‖A.comp Vᗮ.subtypeL‖ ∧
      ∀ y ∈ Vᗮ, ⟪e, y⟫_ℂ = 0 → ⟪A e, A y⟫_ℂ = 0 := by
  have : FiniteDimensional ℂ V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  let : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have hproper : V ≠ ⊤ := by
    intro h
    exact hn.ne (by rw [← hV, h, rank_top])
  have : Nontrivial Vᗮ := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h ↦ hproper (V.orthogonal_eq_bot_iff.mp h))
  let T := A.comp Vᗮ.subtypeL
  obtain ⟨e, he, heA, heig⟩ :=
    exists_unit_norm_eq_opNorm_of_isCompactOperator T (hA.comp_clm Vᗮ.subtypeL)
  refine ⟨e, e.property, he, heA, fun y hy hinner ↦ ?_⟩
  let z : Vᗮ := ⟨y, hy⟩
  change ⟪T e, T z⟫_ℂ = 0
  rw [← T.adjoint_inner_left, heig, inner_smul_left]
  change (starRingEnd ℂ _) * ⟪(e : H), y⟫_ℂ = 0
  rw [hinner, mul_zero]

/-- Adjoin a maximizing line to a subspace whose image is orthogonal to the image of its
orthogonal complement. The enlarged subspace retains this property and has a lower
norm bound given by the old restriction norm. -/
private theorem exists_succ_rank_subspace_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) {n : ℕ} (hn : (n : Cardinal) < Module.rank ℂ H)
    {V : Submodule ℂ H} (hV : Module.rank ℂ V = (n : Cardinal))
    (horth : ∀ x ∈ V, ∀ y ∈ Vᗮ, ⟪A x, A y⟫_ℂ = 0)
    (hlower : ∀ x ∈ V, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖) :
    ∃ U : Submodule ℂ H, V ≤ U ∧ Module.rank ℂ U = ((n + 1 : ℕ) : Cardinal) ∧
      (∀ x ∈ U, ∀ y ∈ Uᗮ, ⟪A x, A y⟫_ℂ = 0) ∧
      ∀ x ∈ U, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖ := by
  obtain ⟨e, heV, he, heA, heorth⟩ := exists_unit_maximizer_on_orthogonal A hA hn hV
  let L : Submodule ℂ H := ℂ ∙ e
  have hL : L ≤ Vᗮ := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heV)
  have he0 : e ≠ 0 := by
    intro h
    simp [h] at he
  have hrankL : Module.rank ℂ L = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton he0, Nat.cast_one]
  have hrank : Module.rank ℂ (V ⊔ L : Submodule ℂ H) = ((n + 1 : ℕ) : Cardinal) := by
    have hinf : V ⊓ L = ⊥ := (V.orthogonal_disjoint.mono_right hL).eq_bot
    have h := V.rank_sup_add_rank_inf_eq L
    rw [hinf, rank_bot, add_zero, hV, hrankL] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine ⟨V ⊔ L, le_sup_left, hrank, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hyV : y ∈ Vᗮ := Submodule.orthogonal_le le_sup_left hy
    have hyL : y ∈ Lᗮ := Submodule.orthogonal_le le_sup_right hy
    rw [map_add, map_smul, inner_add_left, inner_smul_left, horth v hv y hyV,
      heorth y hyV (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyL), mul_zero,
      add_zero]
  · intro x hx
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hzV : z ∈ Vᗮ := hL hz
    let c := ‖A.comp Vᗮ.subtypeL‖
    have hz_eq : ‖A z‖ = c * ‖z‖ := by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul, norm_smul, norm_smul, heA, he, mul_one, mul_comm]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    change (c * ‖v + z‖) ^ 2 ≤ ‖A (v + z)‖ ^ 2
    calc
      (c * ‖v + z‖) ^ 2 = (c * ‖v‖) ^ 2 + (c * ‖z‖) ^ 2 := by
        rw [mul_pow, norm_add_sq (𝕜 := ℂ) v z, (V.mem_orthogonal z).mp hzV v hv]
        simp only [RCLike.zero_re, mul_zero, add_zero, mul_add, mul_pow]
      _ ≤ ‖A v‖ ^ 2 + ‖A z‖ ^ 2 := by
        rw [← hz_eq]
        exact add_le_add ((sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hlower v hv)) le_rfl
      _ = ‖A (v + z)‖ ^ 2 := by
        rw [map_add, norm_add_sq (𝕜 := ℂ) (A v) (A z), horth v hv z hzV]
        simp

/-- There are `n` dimensions whose image is orthogonal to the image of the complement, with
norm bounded below by the norm of the operator on the complement. -/
private theorem exists_rank_subspace_of_compact (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) ≤ Module.rank ℂ H) :
    ∃ V : Submodule ℂ H, Module.rank ℂ V = (n : Cardinal) ∧
      (∀ x ∈ V, ∀ y ∈ Vᗮ, ⟪A x, A y⟫_ℂ = 0) ∧
      ∀ x ∈ V, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖ := by
  induction n with
  | zero =>
    refine ⟨⊥, by simp, ?_, ?_⟩ <;> simp
  | succ n ih =>
    have hlt : (n : Cardinal) < Module.rank ℂ H :=
      (Nat.cast_lt.mpr (Nat.lt_succ_self n)).trans_le hn
    obtain ⟨V, hV, horth, hlower⟩ := ih hlt.le
    obtain ⟨U, hVU, hU, hUorth, hUlower⟩ :=
      exists_succ_rank_subspace_of_compact A hA hlt hV horth hlower
    refine ⟨U, hU, hUorth, fun x hx ↦ ?_⟩
    have hmono : ‖A.comp Uᗮ.subtypeL‖ ≤ ‖A.comp Vᗮ.subtypeL‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
      exact (A.comp Vᗮ.subtypeL).le_opNorm ⟨y, Submodule.orthogonal_le hVU y.property⟩
    exact (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)).trans (hUlower x hx)

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the smallest of
the attained maxima of the norm of A on the unit sphere of each orthogonal
complement of an n-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_min_max (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ maxima : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} → ℝ,
      (∀ V, IsGreatest {r | ∃ x ∈ Submodule.orthogonal (Subtype.val V), ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V)) ∧
        IsLeast (Set.range maxima) (approximationNumber A n) := by
  let maxima (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :=
    ‖A.comp (Subtype.val V)ᗮ.subtypeL‖
  have hmax (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :
      IsGreatest {r | ∃ x ∈ (Subtype.val V)ᗮ, ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V) := by
    obtain ⟨e, he, he1, heA, _⟩ := exists_unit_maximizer_on_orthogonal A hA hn V.property
    refine ⟨⟨e, he, he1, heA.symm⟩, ?_⟩
    rintro _ ⟨x, hx, hx1, rfl⟩
    simpa [maxima, hx1] using (A.comp V.valᗮ.subtypeL).le_opNorm ⟨x, hx⟩
  have hle (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :
      approximationNumber A n ≤ maxima V := by
    have : FiniteDimensional ℂ V.val :=
      Module.rank_lt_aleph0_iff.mp (V.property.trans_lt Cardinal.natCast_lt_aleph0)
    let : CompleteSpace V.val := FiniteDimensional.completeSpace ℂ V.val
    -- Projecting onto V gives an admissible rank-n approximation.
    let S := A.comp V.val.starProjection
    have hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) := by
      refine (LinearMap.rank_comp_le_right V.val.starProjection.toLinearMap A.toLinearMap).trans ?_
      change Module.rank ℂ V.val.starProjection.toLinearMap.range ≤ (n : Cardinal)
      rw [Submodule.range_starProjection, V.property]
    have hdiff : A - S = (A.comp V.valᗮ.subtypeL).comp V.valᗮ.orthogonalProjectionOnto := by
      change A - S = A.comp V.valᗮ.starProjection
      ext x
      simp [S, map_sub]
    have happ : approximationNumber A n ≤ ‖S - A‖ :=
      csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S, hS, rfl⟩
    refine happ.trans ?_
    rw [norm_sub_rev, hdiff]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    exact ((A.comp V.valᗮ.subtypeL).le_opNorm (V.valᗮ.orthogonalProjectionOnto x)).trans
      (mul_le_mul_of_nonneg_left (V.valᗮ.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _))
  obtain ⟨V, hV, horth, hlower⟩ := exists_rank_subspace_of_compact A hA n hn.le
  obtain ⟨U, _, hU, _, hUlower⟩ := exists_succ_rank_subspace_of_compact A hA hn hV horth hlower
  let V₀ : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} := ⟨V, hV⟩
  have hge : maxima V₀ ≤ approximationNumber A n := by
    refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    -- Every admissible approximant kills a nonzero vector in U.
    let R := S.toLinearMap.rangeRestrict.comp U.subtype
    have hker : R.ker ≠ ⊥ := by
      intro h
      have hr := (R.rank_le_of_injective (LinearMap.ker_eq_bot.mp h)).trans hS
      rw [hU] at hr
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hr
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (x : H) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr fun h ↦ hx0 (Subtype.ext h)
    have hbound := (S - A).le_opNorm (x : H)
    rw [sub_apply, hSx, zero_sub, norm_neg] at hbound
    exact le_of_mul_le_mul_right ((hUlower x x.property).trans hbound) hnorm
  refine ⟨maxima, hmax, ⟨⟨V₀, le_antisymm hge (hle V₀)⟩, ?_⟩⟩
  rintro _ ⟨W, rfl⟩
  exact hle W

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the largest of
the attained minima of the norm of A on the unit sphere of each
(n + 1)-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_max_min (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ minima : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)} → ℝ,
      (∀ V, IsLeast {r | ∃ x ∈ Subtype.val V, ‖x‖ = 1 ∧ r = ‖A x‖} (minima V)) ∧
        IsGreatest (Set.range minima) (approximationNumber A n) := by sorry

-- Lemma C.3.5.4(1) is Mathlib's IsCompactOperator.comp_clm and IsCompactOperator.clm_comp.

omit [CompleteSpace H] in
/-- An approximation number is bounded by the error of any admissible approximant. -/
private theorem approximationNumber_le_norm_sub (T S : H →L[ℂ] H) {n : ℕ}
    (hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal)) :
    approximationNumber T n ≤ ‖S - T‖ :=
  csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S, hS, rfl⟩

omit [CompleteSpace H] in
/-- If an operation `S ↦ S'` on approximants does not raise the rank and multiplies the
error by at most `‖B‖`, then it bounds the approximation numbers of the new operator `A'`. -/
private theorem approximationNumber_mul_le_of_rank_le (A B : H →L[ℂ] H) {n : ℕ}
    {A' : H →L[ℂ] H} {op : (H →L[ℂ] H) → H →L[ℂ] H}
    (hrank : ∀ S, Module.rank ℂ (op S).toLinearMap.range ≤ Module.rank ℂ S.toLinearMap.range)
    (hnorm : ∀ S, ‖op S - A'‖ ≤ ‖S - A‖ * ‖B‖) :
    approximationNumber A' n ≤ approximationNumber A n * ‖B‖ := by
  rcases (norm_nonneg B).eq_or_lt with hB | hB
  · rw [← hB, mul_zero]
    have h := approximationNumber_le_norm_sub A' (op 0) (n := n)
      ((hrank 0).trans (by simp))
    simpa [← hB] using h.trans (hnorm 0)
  · rw [← div_le_iff₀ hB]
    refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    rw [div_le_iff₀ hB]
    exact (approximationNumber_le_norm_sub A' (op S) ((hrank S).trans hS)).trans (hnorm S)

/-- Paper: Lemma C.3.5.4(2), p. 701. The singular value of a compact
endomorphism composed on the right by a bounded operator is bounded by the
same singular value times the norm of the right factor.
Deviation: The approximation-number index starts at zero. -/
theorem approximationNumber_mul_le_right (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber (A * B) n ≤ approximationNumber A n * ‖B‖ :=
  approximationNumber_mul_le_of_rank_le A B (op := fun S ↦ S * B)
    (fun S ↦ Submodule.rank_mono (LinearMap.range_comp_le_range B.toLinearMap S.toLinearMap))
    (fun S ↦ by rw [← sub_mul]; exact norm_mul_le _ _)

/-- Paper: Lemma C.3.5.4(2), p. 701. The singular value of a compact
endomorphism composed on the left by a bounded operator is bounded by the
same singular value times the norm of the left factor.
Deviation: The approximation-number index starts at zero. -/
theorem approximationNumber_mul_le_left (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber (B * A) n ≤ approximationNumber A n * ‖B‖ :=
  approximationNumber_mul_le_of_rank_le A B (op := fun S ↦ B * S)
    (fun S ↦ by
      change Module.rank ℂ (B.toLinearMap ∘ₗ S.toLinearMap).range ≤ _
      rw [LinearMap.range_comp]
      exact rank_map_le _ _)
    (fun S ↦ by rw [← mul_sub, mul_comm ‖S - A‖]; exact norm_mul_le _ _)

end SingularValues

section FiltrationConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [hsep : SeparableSpace H] (V : ℕ → ClosedSubmodule ℂ H) (hV : Monotone V)
  (hdense : Dense (⋃ i, (V i : Set H)))

local notation "P(" i ")" => Submodule.starProjection (V i : Submodule ℂ H)

include hsep hV hdense

-- TODO(paper-gap): The text says the projections are onto H, though their
-- codomains and the proof specify Hᵢ. The proof also needs to allow zero
-- orthogonal differences when consecutive subspaces coincide.

/-- Paper: Corollary C.3.5.5(1), p. 702. The orthogonal projections of an
increasing sequence of closed subspaces with dense union converge strongly
to the identity.
Deviation: The projections are onto the individual subspaces, as their declared
codomains and the proof specify. The sequence is indexed from zero. -/
theorem tendsto_filtration_orthogonalProjections :
    ∀ x, Tendsto (fun i ↦ (P(i)) x) atTop (𝓝 x) := by sorry

/-- Paper: Corollary C.3.5.5(2), p. 702. Left multiplication by the
projections of a dense filtration converges in trace norm to the original operator. -/
theorem tendsto_traceNorm_filtration_orthogonalProjections_mul (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm
      (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ - T)) atTop (𝓝 0) := by sorry

/-- Paper: Corollary C.3.5.5(2), p. 702. Right multiplication by the
projections of a dense filtration converges in trace norm to the original operator. -/
theorem tendsto_traceNorm_mul_filtration_orthogonalProjections (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * P(i), mul_mem_nuclearEndomorphisms_right (P(i)) T⟩ - T)) atTop (𝓝 0) := by sorry

/-- Paper: Corollary C.3.5.5(3), p. 702. The traces of the left-projected
operators converge to the trace of the original operator. -/
theorem tendsto_hilbertTrace_filtration_orthogonalProjections_mul (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace
      ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by sorry

/-- Paper: Corollary C.3.5.5(3), p. 702. The traces of the right-projected
operators converge to the trace of the original operator. -/
theorem tendsto_hilbertTrace_mul_filtration_orthogonalProjections (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace
      ⟨T.val * P(i), mul_mem_nuclearEndomorphisms_right (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by sorry

end FiltrationConvergence

section SchattenClasses

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

-- TODO(paper-gap): Theorem C.3.6.1(2) requires infinite orthonormal
-- sequences even for finite-rank operators, such as the identity on ℂ.

/-- Paper: Theorem C.3.6.1(2), p. 703. A singular expansion has decreasing
nonnegative coefficients tending to zero and gives a pointwise sum of
rank-one terms from two orthonormal families.
Deviation: The orthonormal families are indexed by the nonzero coefficients.
Mathlib's inner product is linear in its second argument. -/
structure SingularExpansion (T : E →L[ℂ] F) where
  coeff : ℕ → ℝ≥0
  antitone_coeff : Antitone coeff
  tendsto_coeff : Tendsto coeff atTop (𝓝 0)
  source : {n // coeff n ≠ 0} → E
  target : {n // coeff n ≠ 0} → F
  orthonormal_source : Orthonormal ℂ source
  orthonormal_target : Orthonormal ℂ target
  hasSum_apply : ∀ x, HasSum
    (fun n : {n // coeff n ≠ 0} ↦ ((coeff n : ℝ) * ⟪source n, x⟫_ℂ) • target n) (T x)

/-- Paper: Theorem C.3.6.1(2), p. 703. A rank-one map from a pair of unit
vectors has a singular expansion with first coefficient one and all later
coefficients zero.
Deviation: This checks the vectors and coefficient normalization for a rank-one map. -/
theorem singularExpansion_smulRight (e : E) (f : F) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ∃ d : SingularExpansion ((innerSL ℂ e).smulRight f),
      d.coeff 0 = 1 ∧ ∀ n, d.coeff (n + 1) = 0 := by sorry

/-- Paper: Theorem C.3.6.1(1)–(2), p. 703. A bounded operator is compact
exactly when it admits a singular expansion.
Deviation: The expansion uses orthonormal vectors only for nonzero coefficients. -/
theorem isCompactOperator_iff_nonempty_singularExpansion (T : E →L[ℂ] F) :
    IsCompactOperator T ↔ Nonempty (SingularExpansion T) := by sorry

/-- Paper: Theorem C.3.6.1, p. 703. The series of rank-one maps in a
singular expansion converges in operator norm. -/
theorem SingularExpansion.hasSum_opNorm {T : E →L[ℂ] F} (d : SingularExpansion T) :
    HasSum (fun n : {n // d.coeff n ≠ 0} ↦
      ((d.coeff n : ℝ) : ℂ) • (innerSL ℂ (d.source n)).smulRight (d.target n)) T := by sorry

-- TODO(paper-gap): The proof on p. 704 bounds the squared norm using any
-- coefficient. For a leading singular vector, the squared norm is the square
-- of the first coefficient.

/-- Paper: Theorem C.3.6.1, p. 703. The first coefficient of a singular
expansion equals the operator norm, including for the zero operator. -/
theorem SingularExpansion.coeff_zero_eq_opNorm {T : E →L[ℂ] F} (d : SingularExpansion T) :
    (d.coeff 0 : ℝ) = ‖T‖ := by sorry

/-- Paper: §C.3.6, p. 704. The coefficients of a singular expansion are
the approximation numbers and are independent of the orthonormal vectors.
Deviation: The sequences are indexed from zero and include any zero tail. -/
theorem SingularExpansion.coeff_eq_approximationNumber {T : E →L[ℂ] F}
    (d : SingularExpansion T) (n : ℕ) :
    (d.coeff n : ℝ) = approximationNumber T n := by sorry

/-- Paper: Definition C.3.6.2(1), p. 704. The compact operators with summable
p-th powers of the approximation numbers contain zero and are closed under
addition and complex scalar multiplication. -/
theorem schattenClass_submodule_axioms (p : ℝ) (hp : 1 ≤ p) :
    let s : Set (E →L[ℂ] F) :=
      {T | IsCompactOperator T ∧ Summable (fun n ↦ (approximationNumber T n) ^ p)}
    0 ∈ s ∧
      (∀ {A B : E →L[ℂ] F}, A ∈ s → B ∈ s → A + B ∈ s) ∧
      (∀ (c : ℂ) {A : E →L[ℂ] F}, A ∈ s → c • A ∈ s) := by sorry

variable (E F) in
/-- Paper: Definition C.3.6.2(1), p. 704. The Schatten class of index p is
the submodule of compact operators with summable p-th powers of their
approximation numbers. -/
def schattenClass (p : ℝ) (hp : 1 ≤ p) : Submodule ℂ (E →L[ℂ] F) where
  carrier := {T | IsCompactOperator T ∧ Summable (fun n ↦ (approximationNumber T n) ^ p)}
  zero_mem' := (schattenClass_submodule_axioms p hp).1
  add_mem' := (schattenClass_submodule_axioms p hp).2.1
  smul_mem' := (schattenClass_submodule_axioms p hp).2.2

/-- Paper: Definition C.3.6.2(1), p. 704. The Schatten norm is the p-th root
of the sum of the p-th powers of the approximation numbers. -/
def schattenNorm {p : ℝ} {hp : 1 ≤ p} (T : schattenClass E F p hp) : ℝ :=
  (∑' n, (approximationNumber T.val n) ^ p) ^ (1 / p)

omit [CompleteSpace E] [CompleteSpace F] in
/-- An approximation number vanishes once its index bounds the rank of the operator,
since the operator approximates itself. -/
private theorem approximationNumber_eq_zero_of_rank_le (T : E →L[ℂ] F) {n : ℕ}
    (hn : Module.rank ℂ T.toLinearMap.range ≤ (n : Cardinal)) :
    approximationNumber T n = 0 := by
  have hlow : ∀ r ∈ {r | ∃ S : E →L[ℂ] F,
      Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}, 0 ≤ r :=
    fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  apply le_antisymm
  · exact (csInf_le ⟨0, hlow⟩ ⟨T, hn, rfl⟩).trans_eq (by simp)
  · exact le_csInf ⟨_, T, hn, rfl⟩ hlow

omit [CompleteSpace E] [CompleteSpace F] in
/-- The zeroth approximation number is the operator norm, since the only approximant of
rank zero is the zero operator. -/
private theorem approximationNumber_zero_eq_norm (T : E →L[ℂ] F) :
    approximationNumber T 0 = ‖T‖ := by
  have hset : {r | ∃ S : E →L[ℂ] F, Module.rank ℂ S.toLinearMap.range ≤ ((0 : ℕ) : Cardinal) ∧
      r = ‖S - T‖} = {‖T‖} := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      have h0 : Module.rank ℂ S.toLinearMap.range = 0 := by
        rw [Nat.cast_zero] at hS
        exact le_zero_iff.mp hS
      rw [Submodule.rank_eq_zero, LinearMap.range_eq_bot] at h0
      have hS0 : S = 0 := ContinuousLinearMap.coe_injective h0
      simp [hS0]
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  unfold approximationNumber
  rw [hset, csInf_singleton]

/-- An operator with finite-dimensional range is compact and its approximation numbers
vanish from the dimension of the range on, so it lies in every Schatten class. -/
private theorem mem_schattenClass_of_finiteDimensional_range {p : ℝ} (hp : 1 ≤ p)
    (T : E →L[ℂ] F) (hT : FiniteDimensional ℂ T.toLinearMap.range) :
    T ∈ schattenClass E F p hp := by
  have : ProperSpace T.toLinearMap.range := FiniteDimensional.proper_rclike ℂ _
  refine ⟨?_, ?_⟩
  · let T' : E →L[ℂ] T.toLinearMap.range :=
      T.codRestrict _ (fun x ↦ LinearMap.mem_range_self T.toLinearMap x)
    exact (isCompactOperator_of_locallyCompactSpace_dom T').continuous_comp
      continuous_subtype_val
  · apply summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℂ T.toLinearMap.range))
    intro n hn
    have hn : Module.finrank ℂ T.toLinearMap.range ≤ n := by simpa using hn
    rw [approximationNumber_eq_zero_of_rank_le T (by
      rw [← Module.finrank_eq_rank]
      exact_mod_cast hn), Real.zero_rpow (by linarith)]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The range of a rank-one map lies in the span of its vector. -/
private theorem range_smulRight_le (φ : E →L[ℂ] ℂ) (f : F) :
    (φ.smulRight f).toLinearMap.range ≤ ℂ ∙ f := by
  rintro _ ⟨x, rfl⟩
  exact Submodule.mem_span_singleton.mpr ⟨φ x, rfl⟩

/-- Paper: Definition C.3.6.2(1), p. 704. A rank-one map belongs to every
Schatten class.
Deviation: This checks class membership on rank-one maps. -/
theorem smulRight_mem_schattenClass {p : ℝ} (hp : 1 ≤ p) (φ : E →L[ℂ] ℂ) (f : F) :
    φ.smulRight f ∈ schattenClass E F p hp := by
  have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton f)
  exact mem_schattenClass_of_finiteDimensional_range hp _
    (Submodule.finiteDimensional_of_le (range_smulRight_le φ f))

/-- Paper: Definition C.3.6.2(1), p. 704. A rank-one map has Schatten norm
equal to the product of the norms of its functional and its vector.
Deviation: This checks the normalization of the Schatten norm for all indices. -/
theorem schattenNorm_smulRight {p : ℝ} (hp : 1 ≤ p) (φ : E →L[ℂ] ℂ) (f : F) :
    schattenNorm ⟨φ.smulRight f, smulRight_mem_schattenClass hp φ f⟩ = ‖φ‖ * ‖f‖ := by
  have hp0 : p ≠ 0 := by linarith
  have hrank : Module.rank ℂ (φ.smulRight f).toLinearMap.range ≤ 1 :=
    (Submodule.rank_mono (range_smulRight_le φ f)).trans
      ((rank_span_le _).trans_eq (Cardinal.mk_singleton f))
  have hterm (n : ℕ) : approximationNumber (φ.smulRight f) n ^ p =
      if n = 0 then ‖φ.smulRight f‖ ^ p else 0 := by
    rcases n with _ | n
    · simp [approximationNumber_zero_eq_norm]
    · have h1 : (1 : Cardinal) ≤ ((n + 1 : ℕ) : Cardinal) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      rw [approximationNumber_eq_zero_of_rank_le _ (hrank.trans h1), Real.zero_rpow hp0]
      simp
  unfold schattenNorm
  simp only [hterm, tsum_ite_eq]
  rw [one_div, Real.rpow_rpow_inv (norm_nonneg _) hp0,
    ContinuousLinearMap.norm_smulRight_apply]

variable (E F) in
/-- Paper: Definition C.3.6.2(2), p. 704. The Hilbert-Schmidt operators
are the Schatten class of index two. -/
abbrev hilbertSchmidtOperators : Submodule ℂ (E →L[ℂ] F) :=
  schattenClass E F 2 one_le_two

/-- Paper: Definition C.3.6.2(2), p. 704. An operator is Hilbert-Schmidt
exactly when the squared norms of the images of any given Hilbert basis
form a summable family.
Deviation: This checks the index-two class against the basis criterion. -/
theorem mem_hilbertSchmidtOperators_iff_summable_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) :
    T ∈ hilbertSchmidtOperators E F ↔ Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by sorry

variable (E F) in
/-- Paper: Definition C.3.6.2(3), p. 704. The trace-class operators are
the Schatten class of index one. -/
abbrev traceClassOperators : Submodule ℂ (E →L[ℂ] F) :=
  schattenClass E F 1 le_rfl

/-- Paper: Definition C.3.6.2(3), p. 704. For Hilbert endomorphisms, the
index-one Schatten condition is equivalent to nuclearity.
Deviation: This checks that trace class agrees with §C.3.4 on endomorphisms. -/
theorem mem_traceClassOperators_iff_isNuclearOperator (T : E →L[ℂ] E) :
    T ∈ traceClassOperators E E ↔ IsNuclearOperator T := by sorry

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

-- TODO(paper-gap): Lemma C.3.6.3(1) is false. The second approximation numbers
-- of diag(1, 0) and diag(0, 1) on ℂ² vanish, while their sum has second
-- approximation number one.

/-- Paper: Lemma C.3.6.3(2), p. 704. Each approximation number changes
by at most the operator norm of the difference of the two operators.
Deviation: The approximation-number index starts at zero. -/
theorem abs_approximationNumber_sub_le (A B : E →L[ℂ] F) (n : ℕ) :
    |approximationNumber A n - approximationNumber B n| ≤ ‖A - B‖ := by
  have key (A B : E →L[ℂ] F) :
      approximationNumber A n ≤ approximationNumber B n + ‖A - B‖ := by
    have hz : Module.rank ℂ (0 : E →L[ℂ] F).toLinearMap.range ≤ (n : Cardinal) := by simp
    rw [← sub_le_iff_le_add]
    unfold approximationNumber
    refine le_csInf (by exact ⟨_, 0, hz, rfl⟩) ?_
    rintro _ ⟨S, hS, rfl⟩
    rw [sub_le_iff_le_add]
    calc
      approximationNumber A n ≤ ‖S - A‖ :=
        csInf_le ⟨0, fun r ⟨S, _, h⟩ ↦ h ▸ norm_nonneg _⟩ ⟨S, hS, rfl⟩
      _ = ‖(S - B) + (B - A)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖S - B‖ + ‖A - B‖ := (norm_add_le _ _).trans_eq (by rw [norm_sub_rev B A])
  rw [abs_sub_le_iff]
  constructor
  · linarith [key A B]
  · linarith [key B A, norm_sub_rev A B]

/-- Every strict upper bound for an approximation number is realized as a strict error bound
by some approximant of the prescribed rank. -/
private theorem exists_approximation_of_lt {T : E →L[ℂ] F} {n : ℕ} {a : ℝ}
    (h : approximationNumber T n < a) :
    ∃ S : E →L[ℂ] F, S.toLinearMap.rank ≤ (n : Cardinal) ∧ ‖S - T‖ < a := by
  have hz : (0 : E →L[ℂ] F).toLinearMap.rank ≤ (n : Cardinal) := by simp
  unfold approximationNumber at h
  obtain ⟨r, ⟨S, hS, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (by exact ⟨_, 0, hz, rfl⟩) h
  exact ⟨S, hS, hlt⟩

/-- Paper: Lemma C.3.6.3(3), p. 704. The approximation number of a product
at the sum of two one-based indices is bounded by the product of the
approximation numbers of its factors at the corresponding indices.
Deviation: The one-based index sum becomes m + n + 1 in zero-based indexing. -/
theorem approximationNumber_comp_le (A : F →L[ℂ] G) (B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (A.comp B) (m + n + 1) ≤
      approximationNumber A m * approximationNumber B n := by
  apply le_mul_of_forall_lt₀
  intro a ha b hb
  obtain ⟨S, hS, hSa⟩ := exists_approximation_of_lt ha
  obtain ⟨T, hT, hTb⟩ := exists_approximation_of_lt hb
  -- Subtract the product of the errors from the composite to get an approximant.
  let R := S.comp B + (A - S).comp T
  have hleft := (LinearMap.rank_comp_le_left B.toLinearMap S.toLinearMap).trans hS
  have hright : ((A - S).comp T).toLinearMap.rank ≤ (n : Cardinal) := by
    apply Cardinal.lift_le.mp
    exact (LinearMap.lift_rank_comp_le_right T.toLinearMap (A - S).toLinearMap).trans
      (by simpa only [Cardinal.lift_natCast] using Cardinal.lift_le.mpr hT)
  have hR : R.toLinearMap.rank ≤ ((m + n + 1 : ℕ) : Cardinal) := by
    refine (LinearMap.rank_add_le _ _).trans ((add_le_add hleft hright).trans ?_)
    exact_mod_cast Nat.le_succ (m + n)
  have herr : R - A.comp B = (S - A).comp (B - T) := by
    simp only [R, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  calc
    approximationNumber (A.comp B) (m + n + 1) ≤ ‖R - A.comp B‖ := by
      unfold approximationNumber
      refine csInf_le ?_ ⟨R, hR, rfl⟩
      exact ⟨0, fun r ⟨S, _, h⟩ ↦ h ▸ norm_nonneg _⟩
    _ ≤ ‖S - A‖ * ‖T - B‖ := by
      rw [herr, norm_sub_rev T B]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ a * b := mul_le_mul hSa.le hTb.le (norm_nonneg _) ((norm_nonneg _).trans hSa.le)

end SchattenClasses

-- The compact submodule and its closedness are Mathlib's compactOperator and
-- isClosed_setOfPred_isCompactOperator.

section HilbertSchmidtKernels

open MeasureTheory

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Paper: (C.3.6.5)–(C.3.6.6), p. 705. Square-integrable kernels on the product
of two Radon measure spaces correspond to Hilbert-Schmidt operators between their
L² spaces. The operator acts by integrating in the source variable, almost
everywhere in the target variable.
Deviation: The identification is written as a linear norm-preserving equivalence
of equivalence classes. The integral is required to be defined almost everywhere. -/
theorem hilbertSchmidtOperators_equiv_Lp_prod (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]
    [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν] :
    ∃ e : Lp ℂ 2 (μ.prod ν) ≃ₗ[ℂ] hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν),
      (∀ k, schattenNorm (e k) = ‖k‖) ∧
      ∀ (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 μ), ∀ᵐ y ∂ν,
        Integrable (fun x ↦ k (x, y) * f x) μ ∧
          (e k).val f y = ∫ x, k (x, y) * f x ∂μ := by sorry

end HilbertSchmidtKernels

section TensorProducts

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

-- (C.3.6.7) and its injectivity are tensorToFiniteRank and tensorToFiniteRank_injective.

/-- Paper: Proposition C.3.6.4(1), p. 705. The image of every algebraic
tensor under the canonical map belongs to each Schatten class. -/
theorem tensorToFiniteRank_mem_schattenClass {p : ℝ} (hp : 1 ≤ p)
    (z : StrongDual ℂ E ⊗[ℂ] F) :
    tensorToFiniteRank z ∈ schattenClass E F p hp := by
  refine mem_schattenClass_of_finiteDimensional_range hp _ ?_
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
    apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ y)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ x, (tensorToFiniteRank_tmul φ y x).symm⟩
  | add z w hz hw =>
    rw [map_add, ContinuousLinearMap.toLinearMap_add]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)

/-- Paper: (C.3.6.8), p. 705. The norm of the dual of a Hilbert space satisfies
the parallelogram identity.
Deviation: This supplies the compatible inner product on the dual factor. -/
theorem strongDual_parallelogram (φ ψ : StrongDual ℂ E) :
    ‖φ + ψ‖ * ‖φ + ψ‖ + ‖φ - ψ‖ * ‖φ - ψ‖ =
      2 * (‖φ‖ * ‖φ‖ + ‖ψ‖ * ‖ψ‖) := by
  let R := (InnerProductSpace.toDual ℂ E).symm
  have h := parallelogram_law_with_norm_mul ℂ (R φ) (R ψ)
  simpa only [← map_add, ← map_sub, LinearIsometryEquiv.norm_map] using h

/-- Paper: (C.3.6.8), p. 705. The continuous dual of a Hilbert space has the
inner product compatible with its operator norm. -/
@[instance_reducible]
def strongDualInnerProductSpace : InnerProductSpace ℂ (StrongDual ℂ E) :=
  InnerProductSpace.ofNorm ℂ strongDual_parallelogram

attribute [local instance] strongDualInnerProductSpace

/-- Paper: (C.3.6.8), p. 705. The dual inner product reverses the order of
the arguments under the conjugate-linear Riesz identification.
Deviation: This checks the dual inner product convention. -/
theorem strongDual_inner_eq (φ ψ : StrongDual ℂ E) :
    ⟪φ, ψ⟫_ℂ = ⟪(InnerProductSpace.toDual ℂ E).symm ψ,
      (InnerProductSpace.toDual ℂ E).symm φ⟫_ℂ := by
  let R := (InnerProductSpace.toDual ℂ E).symm
  have hI : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
  have h1 : ‖R ψ + R φ‖ = ‖φ + ψ‖ := by
    rw [← map_add, LinearIsometryEquiv.norm_map, add_comm]
  have h2 : ‖R ψ - R φ‖ = ‖φ - ψ‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev]
  have h3 : ‖R ψ - Complex.I • R φ‖ = ‖φ - Complex.I • ψ‖ := by
    have e : R ψ - Complex.I • R φ = R (Complex.I • (φ - Complex.I • ψ)) := by
      simp only [map_smulₛₗ, map_sub, Complex.conj_I, smul_sub, smul_smul]
      simp
      abel
    rw [e, LinearIsometryEquiv.norm_map, norm_smul, hI, one_mul]
  have h4 : ‖R ψ + Complex.I • R φ‖ = ‖φ + Complex.I • ψ‖ := by
    have e : R ψ + Complex.I • R φ = R ((-Complex.I) • (φ + Complex.I • ψ)) := by
      simp only [map_smulₛₗ, map_add, map_neg, Complex.conj_I, neg_neg, smul_add, smul_smul]
      simp [add_comm]
    rw [e, LinearIsometryEquiv.norm_map, norm_smul, norm_neg, hI, one_mul]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) φ ψ, inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (R ψ) (R φ)]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

/-- Paper: Proposition C.3.6.4(2), p. 705. The canonical image of an algebraic
tensor has Hilbert-Schmidt norm equal to the norm from the tensor inner product
of (C.3.6.8). Thus the two norms induce the same topology. -/
theorem schattenNorm_tensorToFiniteRank_eq_hilbertTensorNorm (z : StrongDual ℂ E ⊗[ℂ] F) :
    schattenNorm ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_schattenClass one_le_two z⟩ =
      ‖z‖ := by sorry

/-- Paper: Proposition C.3.6.4(2), p. 705. The canonical map extends from
algebraic tensors to the Hilbert tensor completion as a linear isometry for
the Hilbert-Schmidt norm. -/
theorem exists_hilbertTensorCompletion_schattenIsometry :
    ∃ e : Completion (StrongDual ℂ E ⊗[ℂ] F) →ₗ[ℂ] hilbertSchmidtOperators E F,
      (∀ z : StrongDual ℂ E ⊗[ℂ] F, (e z).val = tensorToFiniteRank z) ∧
      ∀ z, schattenNorm (e z) = ‖z‖ := by sorry

/-- Paper: Proposition C.3.6.4(3), p. 705. The completed projective tensor map
is a linear isometry onto the trace-class operators. On algebraic tensors
the projective norm is the gauge of the absolutely convex hull of elementary
tensors from the two unit balls. These tensors are already closed under
scalars of modulus at most one.
Deviation: The norm on the existing projective completion is expressed as the
continuous extension of this gauge. -/
theorem exists_projectiveTensorCompletion_traceClassIsometry :
    let projectiveNorm : ProjectiveTensor (StrongDual ℂ E) F → ℝ :=
      gauge (convexHull ℝ (Set.image2 (TensorProduct.tmul ℂ)
        (Metric.closedBall (0 : StrongDual ℂ E) 1) (Metric.closedBall (0 : F) 1)))
    UniformContinuous projectiveNorm ∧
      ∃ e : Completion (ProjectiveTensor (StrongDual ℂ E) F) ≃ₗ[ℂ] traceClassOperators E F,
        (∀ z, (e z).val = completedProjectiveTensorToOperators z) ∧
        ∀ z, schattenNorm (e z) = Completion.extension projectiveNorm z := by sorry

/-- Paper: Proposition C.3.6.4(3), p. 705. The canonical map extends to the
injective tensor completion as a linear isometry onto the compact operators
with the operator norm.
Deviation: The norm on the existing injective completion is expressed as the
continuous extension of the unit-ball injective norm. -/
theorem exists_injectiveTensorCompletion_compactOperatorIsometry :
    let injectiveNorm : InjectiveTensor (StrongDual ℂ E) F → ℝ :=
      injectiveTensorNorm (StrongDual ℂ E) F
    UniformContinuous injectiveNorm ∧
      ∃ e : Completion (InjectiveTensor (StrongDual ℂ E) F) →L[ℂ] (E →L[ℂ] F),
        (∀ z : InjectiveTensor (StrongDual ℂ E) F, e z = tensorToFiniteRank z) ∧
        Set.range e = {T : E →L[ℂ] F | IsCompactOperator T} ∧
        ∀ z, ‖e z‖ = Completion.extension injectiveNorm z := by sorry

end TensorProducts

section SchattenConvergence

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ} {hp : 1 ≤ p}

-- TODO(paper-gap): The proof uses the false Lemma C.3.6.3(1) for the triangle
-- inequality and prints repeated factors in (C.3.6.13), (C.3.6.14) and (C.3.6.17).

/-- Paper: Proposition C.3.6.5, p. 705. Left composition by a strongly convergent
sequence of operators converges in the Schatten norm for a fixed right factor in
the class. Each composition and its limit belong to the class.
Deviation: The independent left-composition assertion uses only the left sequence. -/
theorem tendsto_schattenNorm_comp_left (A : schattenClass E F p hp)
    (Cj : ℕ → F →L[ℂ] F) (C : F →L[ℂ] F)
    (hC : ∀ y, Tendsto (fun j ↦ Cj j y) atTop (𝓝 (C y))) :
    ∃ (hj : ∀ j, (Cj j).comp A.val ∈ schattenClass E F p hp)
      (hlim : C.comp A.val ∈ schattenClass E F p hp),
      Tendsto (fun j ↦ schattenNorm
        ((⟨(Cj j).comp A.val, hj j⟩ : schattenClass E F p hp) - ⟨C.comp A.val, hlim⟩))
        atTop (𝓝 0) := by sorry

/-- Paper: Proposition C.3.6.5, p. 705. Right composition by a strongly
convergent sequence of self-adjoint operators converges in the Schatten norm
for a fixed left factor in the class. Each composition and its limit belong to the class.
Deviation: The independent right-composition assertion uses only the right sequence. -/
theorem tendsto_schattenNorm_comp_right (A : schattenClass E F p hp)
    (Bk : ℕ → E →L[ℂ] E) (B : E →L[ℂ] E)
    (hB : ∀ x, Tendsto (fun k ↦ Bk k x) atTop (𝓝 (B x)))
    (hself : ∀ k, IsSelfAdjoint (Bk k)) :
    ∃ (hk : ∀ k, A.val.comp (Bk k) ∈ schattenClass E F p hp)
      (hlim : A.val.comp B ∈ schattenClass E F p hp),
      Tendsto (fun k ↦ schattenNorm
        ((⟨A.val.comp (Bk k), hk k⟩ : schattenClass E F p hp) - ⟨A.val.comp B, hlim⟩))
        atTop (𝓝 0) := by sorry

/-- Paper: Proposition C.3.6.5, p. 705. Simultaneous left and right
composition converges in the Schatten norm as both indices tend to infinity.
The two operator sequences converge strongly and the right factors are self-adjoint. -/
theorem tendsto_schattenNorm_comp_both (A : schattenClass E F p hp)
    (Bk : ℕ → E →L[ℂ] E) (B : E →L[ℂ] E)
    (hB : ∀ x, Tendsto (fun k ↦ Bk k x) atTop (𝓝 (B x)))
    (hself : ∀ k, IsSelfAdjoint (Bk k))
    (Cj : ℕ → F →L[ℂ] F) (C : F →L[ℂ] F)
    (hC : ∀ y, Tendsto (fun j ↦ Cj j y) atTop (𝓝 (C y))) :
    ∃ (hjk : ∀ j k, (Cj j).comp (A.val.comp (Bk k)) ∈ schattenClass E F p hp)
      (hlim : C.comp (A.val.comp B) ∈ schattenClass E F p hp),
      Tendsto (fun jk : ℕ × ℕ ↦ schattenNorm
        ((⟨(Cj jk.1).comp (A.val.comp (Bk jk.2)), hjk jk.1 jk.2⟩ : schattenClass E F p hp) -
          ⟨C.comp (A.val.comp B), hlim⟩)) atTop (𝓝 0) := by sorry

end SchattenConvergence

section TraceClassEndomorphisms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- TODO(paper-gap): Remark C.3.6.6 refers to Proposition C.3.6.5(2) for
-- the cofinal finite subsets. They are introduced in Proposition C.3.5.1.

/-- Paper: Remark C.3.6.6, p. 707. The Schatten norm at index one equals
the earlier trace norm on nuclear endomorphisms. This is the norm identification
used when specializing Proposition C.3.6.5 to the projection results. -/
theorem schattenNorm_one_eq_traceNorm (T : nuclearEndomorphisms H) :
    schattenNorm ⟨T.val, (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property⟩ =
      traceNorm T := by sorry

end TraceClassEndomorphisms

end RiemannMasullo
