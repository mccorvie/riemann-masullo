module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
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
        IsGreatest (Set.range minima) (approximationNumber A n) := by
  classical
  have hmin (U : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)}) :
      ∃ m : ℝ, IsLeast {r | ∃ x ∈ U.val, ‖x‖ = 1 ∧ r = ‖A x‖} m := by
    have : FiniteDimensional ℂ U.val :=
      Module.rank_lt_aleph0_iff.mp (U.property.trans_lt Cardinal.natCast_lt_aleph0)
    have : Nontrivial U.val := Submodule.nontrivial_iff_ne_bot.mpr fun h ↦
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (U.property.symm.trans (Submodule.rank_eq_zero.mpr h))
    let : ProperSpace U.val := FiniteDimensional.proper ℂ U.val
    obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere (0 : U.val) 1).exists_isMinOn
      (Set.nonempty_coe_sort.mp (NormedSpace.sphere_nonempty_rclike ℂ zero_le_one))
      (A.comp U.val.subtypeL).continuous.norm.continuousOn
    refine ⟨‖A x‖, ⟨x, x.property, mem_sphere_zero_iff_norm.mp hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, hy1, rfl⟩
    exact isMinOn_iff.mp hxmin ⟨y, hy⟩ (mem_sphere_zero_iff_norm.mpr hy1)
  choose minima hminima using hmin
  obtain ⟨maxima, hmaxima, hleast⟩ := approximationNumber_min_max A hA n hn
  obtain ⟨W, hW⟩ := hleast.1
  -- Every (n + 1)-dimensional subspace contains a unit vector orthogonal to W.
  have hle (U : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)}) :
      minima U ≤ approximationNumber A n := by
    have : FiniteDimensional ℂ W.val :=
      Module.rank_lt_aleph0_iff.mp (W.property.trans_lt Cardinal.natCast_lt_aleph0)
    let : CompleteSpace W.val := FiniteDimensional.completeSpace ℂ W.val
    let R := W.val.orthogonalProjectionOnto.toLinearMap.comp U.val.subtype
    have hker : R.ker ≠ ⊥ := by
      intro h
      have hrank := R.rank_le_of_injective (LinearMap.ker_eq_bot.mp h)
      rw [U.property, W.property] at hrank
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hrank
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    let y : U.val := (↑‖x‖ : ℂ)⁻¹ • x
    have hy1 : ‖y‖ = 1 := norm_smul_inv_norm hx0
    have hyker : y ∈ R.ker := R.ker.smul_mem _ hx
    have hyW : (y : H) ∈ W.valᗮ := by
      rw [← W.val.ker_orthogonalProjectionOnto]
      exact hyker
    rw [← hW]
    exact (hminima U).2 ⟨y, y.property, hy1, rfl⟩ |>.trans
      ((hmaxima W).2 ⟨y, hyW, hy1, rfl⟩)
  -- Enlarging V by a maximizing line bounds the new minimum from below.
  obtain ⟨V, hV, horth, hlower⟩ := exists_rank_subspace_of_compact A hA n hn.le
  obtain ⟨U, _, hU, _, hUlower⟩ := exists_succ_rank_subspace_of_compact A hA hn hV horth hlower
  let V₀ : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} := ⟨V, hV⟩
  let U₀ : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)} := ⟨U, hU⟩
  have hge : approximationNumber A n ≤ minima U₀ := by
    obtain ⟨v, hv, hv1, hvA⟩ := (hmaxima V₀).1
    obtain ⟨u, hu, hu1, huA⟩ := (hminima U₀).1
    calc
      approximationNumber A n ≤ maxima V₀ := hleast.2 ⟨V₀, rfl⟩
      _ ≤ ‖A.comp Vᗮ.subtypeL‖ := by
        rw [hvA]
        simpa [hv1] using (A.comp Vᗮ.subtypeL).le_opNorm ⟨v, hv⟩
      _ ≤ minima U₀ := by simpa [hu1, huA] using hUlower u hu
  refine ⟨minima, hminima, ⟨⟨U₀, le_antisymm (hle U₀) hge⟩, ?_⟩⟩
  rintro _ ⟨U, rfl⟩
  exact hle U

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
    ∀ x, Tendsto (fun i ↦ (P(i)) x) atTop (𝓝 x) := by
  intro x
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x) ε hε
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  filter_upwards [eventually_ge_atTop j] with i hi
  have hyi : y ∈ (V i : Submodule ℂ H) := hV hi hj
  rw [dist_comm, (V i : Submodule ℂ H).dist_starProjection_eq_infDist]
  exact (Metric.infDist_le_dist_of_mem hyi).trans_lt hxy

-- Keep the separability hypothesis in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Corollary C.3.5.5(2), p. 702. Left multiplication by the
projections of a dense filtration converges in trace norm to the original operator. -/
theorem tendsto_traceNorm_filtration_orthogonalProjections_mul (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm
      (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ - T)) atTop (𝓝 0) := by
  let Q (i : ℕ) : H →L[ℂ] H := 1 - P(i)
  have hQ_tendsto (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x) ε hε
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    filter_upwards [eventually_ge_atTop j] with i hi
    have hyi : y ∈ (V i : Submodule ℂ H) := hV hi hj
    change dist (x - P(i) x) 0 < ε
    rw [dist_zero_right, ← dist_eq_norm, (V i : Submodule ℂ H).dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem hyi).trans_lt hxy
  let A (i : ℕ) : nuclearEndomorphisms H :=
    ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ - T
  have hA (i : ℕ) : (A i).val = -(Q i * T.val) := by
    change P(i) * T.val - T.val = -((1 - P(i)) * T.val)
    rw [sub_mul, one_mul, neg_sub]
  let B (S : H →L[ℂ] H) := CFC.sqrt (star S * S)
  have hB_pos (S : H →L[ℂ] H) : (B S).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hB_norm (S : H →L[ℂ] H) (x : H) : ‖B S x‖ = ‖S x‖ := by
    have hsq : B S * B S = star S * S := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg S)
    rw [(B S).apply_norm_eq_sqrt_inner_adjoint_right, S.apply_norm_eq_sqrt_inner_adjoint_right]
    change Real.sqrt (⟪x, ((B S).adjoint * B S) x⟫_ℂ).re =
      Real.sqrt (⟪x, (star S * S) x⟫_ℂ).re
    rw [(hB_pos S).isSelfAdjoint.adjoint_eq, hsq]
  -- The complementary projections bound the Gram operators, and square root preserves order.
  have hB_le (i : ℕ) : B (A i).val ≤ B T.val := by
    have hP : IsStarProjection (P(i)) := isStarProjection_starProjection
    have hQ : IsStarProjection (Q i) := hP.one_sub
    have hQ_le : Q i ≤ 1 := sub_le_self _ hP.nonneg
    apply CFC.monotone_sqrt
    calc
      star (A i).val * (A i).val = star T.val * Q i * T.val := by
        simp only [hA, star_neg, neg_mul_neg, star_mul, hQ.isSelfAdjoint.star_eq, mul_assoc]
        rw [← mul_assoc (Q i), hQ.isIdempotentElem.eq]
      _ ≤ star T.val * T.val := by
        simpa only [mul_one] using star_left_conjugate_le_conjugate hQ_le T.val
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  let d (S : H →L[ℂ] H) i : ℝ := (⟪b i, B S (b i)⟫_ℂ).re
  have htrace (S : nuclearEndomorphisms H) : HasSum (d S.val) (traceNorm S) :=
    hasSum_traceNorm_diagonal b S
  have hd_nonneg (S : H →L[ℂ] H) i : 0 ≤ d S i :=
    (hB_pos S).re_inner_nonneg_right (b i)
  have hd_bound (i : ℕ) j : ‖d (A i).val j‖ ≤ d T.val j := by
    rw [Real.norm_of_nonneg (hd_nonneg _ _)]
    have h := (ContinuousLinearMap.le_def.mp (hB_le i)).re_inner_nonneg_right (b j)
    change 0 ≤ (⟪b j, (B T.val - B (A i).val) (b j)⟫_ℂ).re at h
    simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using h
  have hd_tendsto (j) : Tendsto (fun i ↦ d (A i).val j) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun i ↦ ‖b j‖ * ‖Q i (T.val (b j))‖)
      (fun i ↦ hd_nonneg _ _) (fun i ↦ ?_) ?_
    · calc
        d (A i).val j ≤ ‖b j‖ * ‖B (A i).val (b j)‖ :=
          (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ = ‖b j‖ * ‖Q i (T.val (b j))‖ := by
          rw [hB_norm, hA, neg_apply, norm_neg]
          rfl
    · simpa only [norm_zero, mul_zero] using
        tendsto_const_nhds.mul (hQ_tendsto (T.val (b j))).norm
  have hsum (i : ℕ) : (∑' j, d (A i).val j) = traceNorm (A i) := (htrace (A i)).tsum_eq
  simpa only [tsum_zero, hsum] using
    tendsto_tsum_of_dominated_convergence (g := fun _ ↦ 0)
      (htrace T).summable hd_tendsto (Eventually.of_forall hd_bound)

omit hsep hV hdense in
open scoped CStarAlgebra in
/-- The trace norm of a nuclear rank-one series is bounded by the sum of its rank-one norms. -/
private theorem traceNorm_le_of_rankOne_series (A : nuclearEndomorphisms H)
    (φ : ℕ → StrongDual ℂ H) (y : ℕ → H)
    (hs : Summable (fun n ↦ ‖φ n‖ * ‖y n‖))
    (hA : ∀ x, HasSum (fun n ↦ φ n x • y n) (A.val x)) :
    traceNorm A ≤ ∑' n, ‖φ n‖ * ‖y n‖ := by
  let R (n : ℕ) : nuclearEndomorphisms H :=
    ⟨(φ n).smulRight (y n), smulRight_mem_nuclearEndomorphisms (φ n) (y n)⟩
  have hR : Summable (fun n ↦ ‖(R n).val‖) := by
    simpa only [R, ContinuousLinearMap.norm_smulRight_apply] using hs
  have hsum : HasSum (fun n ↦ (R n).val) A.val := by
    obtain ⟨B, hB⟩ := hR.of_norm
    have hBA : B = A.val := by
      ext x
      exact ((ContinuousLinearMap.apply ℂ H x).hasSum hB).unique (hA x)
    rwa [hBA] at hB
  have hfin : Tendsto (fun s : Finset ℕ ↦ CFC.abs (∑ n ∈ s, R n).val) atTop
      (𝓝 (CFC.abs A.val)) := by
    simpa only [Submodule.coe_sum, Function.comp_def, SummationFilter.unconditional_filter] using
      (CFC.continuous_abs.tendsto A.val).comp hsum
  -- Pass to the limit in each finite sum of the nonnegative trace diagonal.
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let diag (B : H →L[ℂ] H) (i : ι) : ℝ := (⟪b i, B (b i)⟫_ℂ).re
  have hdiag (X : nuclearEndomorphisms H) :
      HasSum (diag (CFC.abs X.val)) (traceNorm X) := hasSum_traceNorm_diagonal b X
  have hnonneg (B : H →L[ℂ] H) (i : ι) : 0 ≤ diag (CFC.abs B) i :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.abs_nonneg B)).re_inner_nonneg_right _
  refine le_of_tendsto' (hdiag A) fun t ↦ ?_
  have hcont : Continuous (fun B : H →L[ℂ] H ↦ ∑ i ∈ t, diag B i) := by
    unfold diag
    fun_prop
  refine le_of_tendsto' ((hcont.tendsto (CFC.abs A.val)).comp hfin) fun s ↦ ?_
  calc
    ∑ i ∈ t, diag (CFC.abs (∑ n ∈ s, R n).val) i ≤ traceNorm (∑ n ∈ s, R n) :=
      sum_le_hasSum t (fun i _ ↦ hnonneg _ i) (hdiag _)
    _ ≤ ∑ n ∈ s, ‖φ n‖ * ‖y n‖ := by
      let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
      have hcore := traceNorm_normedSpaceCore (H := H)
      have hzero : traceNorm (0 : nuclearEndomorphisms H) = 0 :=
        (hcore.norm_eq_zero_iff 0).mpr rfl
      exact (s.le_sum_of_subadditive traceNorm hzero.le hcore.toCore.norm_triangle R).trans_eq
        (Finset.sum_congr rfl fun n _ ↦ traceNorm_smulRight _ _)
    _ ≤ ∑' n, ‖φ n‖ * ‖y n‖ :=
      hs.sum_le_tsum s (fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))

set_option linter.unusedSectionVars false in
open InnerProductSpace in
/-- Paper: Corollary C.3.5.5(2), p. 702. Right multiplication by the
projections of a dense filtration converges in trace norm to the original operator. -/
theorem tendsto_traceNorm_mul_filtration_orthogonalProjections (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * P(i), mul_mem_nuclearEndomorphisms_right (P(i)) T⟩ - T)) atTop (𝓝 0) := by
  let Q (i : ℕ) : H →L[ℂ] H := P(i) - 1
  have hQ (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    have hd : Dense ((⨆ i, (V i : Submodule ℂ H) : Submodule ℂ H) : Set H) :=
      hdense.mono (iUnion_subset fun i ↦ le_iSup (fun j ↦ (V j : Submodule ℂ H)) i)
    have h := Submodule.starProjection_tendsto_self (fun i ↦ (V i : Submodule ℂ H))
      (fun _ _ hij ↦ ClosedSubmodule.toSubmodule_le_toSubmodule.mpr (hV hij)) x
      (Submodule.dense_iff_topologicalClosure_eq_top.mp hd).ge
    simpa [Q] using h.sub tendsto_const_nhds (b := x)
  have hQa (i : ℕ) : (Q i).adjoint = Q i :=
    ((isSelfAdjoint_starProjection (V i : Submodule ℂ H)).sub
      (IsSelfAdjoint.one (H →L[ℂ] H))).adjoint_eq
  have hQc (i : ℕ) (x : H) : ‖Q i x‖ ≤ ‖x‖ := by
    have hP : IsStarProjection (P(i)) := isStarProjection_starProjection
    have h := hP.one_sub.norm_le _
    rw [norm_sub_rev] at h
    simpa only [one_mul] using (ContinuousLinearMap.opNorm_le_iff zero_le_one).mp h x
  obtain ⟨c, φ, y, hc, hφ, hy, hT⟩ := (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  -- Since Q i is self-adjoint, right composition applies Q i to each Riesz vector.
  let u (n : ℕ) := (toDual ℂ H).symm (φ n)
  have hu (n : ℕ) : ‖u n‖ = ‖φ n‖ := (toDual ℂ H).symm.norm_map _
  let cost (i n : ℕ) := ‖c n‖ * (‖Q i (u n)‖ * ‖y n‖)
  let bound (n : ℕ) := ‖c n‖ * (‖φ n‖ * ‖y n‖)
  have hcost_nonneg (i n : ℕ) : 0 ≤ cost i n := by dsimp [cost]; positivity
  have hbound (i n : ℕ) : ‖cost i n‖ ≤ bound n := by
    rw [Real.norm_of_nonneg (hcost_nonneg i n)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((hQc i (u n)).trans_eq (hu n)) (norm_nonneg _))
      (norm_nonneg _)
  have hs : Summable bound := by
    obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    obtain ⟨D, _, hyD⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
    refine (hc.mul_right (C * D)).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_of_nonneg (by dsimp [bound]; positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hφC _ (mem_range_self n)) (hyD _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  have hlim : Tendsto (fun i ↦ ∑' n, cost i n) atTop (𝓝 0) := by
    have hterm (n : ℕ) : Tendsto (fun i ↦ cost i n) atTop (𝓝 0) := by
      simpa [cost] using ((hQ (u n)).norm.mul_const ‖y n‖).const_mul ‖c n‖
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hs hterm (Eventually.of_forall hbound)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  refine squeeze_zero (fun _ ↦ (traceNorm_normedSpaceCore (H := H)).toCore.norm_nonneg _)
    ?_ hlim
  intro i
  let ψ (n : ℕ) : StrongDual ℂ H := c n • innerSL ℂ (Q i (u n))
  have hψ (n : ℕ) : ‖ψ n‖ * ‖y n‖ = cost i n := by
    simp only [ψ, cost, norm_smul, innerSL_apply_norm, mul_assoc]
  simp_rw [← hψ]
  refine traceNorm_le_of_rankOne_series _ ψ y
    ((hs.of_norm_bounded (hbound i)).congr fun n ↦ (hψ n).symm) fun x ↦ ?_
  have heval (n : ℕ) : ψ n x = c n * φ n (Q i x) := by
    have hinner := (Q i).adjoint_inner_left x (u n)
    rw [hQa] at hinner
    simp only [ψ, smul_apply, smul_eq_mul, innerSL_apply_apply, hinner, u, toDual_symm_apply]
  simpa [heval, Q, map_sub, mul_apply_eq_comp] using hT (Q i x)

/-- Paper: Corollary C.3.5.5(3), p. 702. The traces of the left-projected
operators converge to the trace of the original operator. -/
theorem tendsto_hilbertTrace_filtration_orthogonalProjections_mul (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace
      ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [← htr, ← map_sub]
  simp only [htr]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _)
    (tendsto_traceNorm_filtration_orthogonalProjections_mul V hV hdense T)

/-- Paper: Corollary C.3.5.5(3), p. 702. The traces of the right-projected
operators converge to the trace of the original operator. -/
theorem tendsto_hilbertTrace_mul_filtration_orthogonalProjections (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace
      ⟨T.val * P(i), mul_mem_nuclearEndomorphisms_right (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [← htr, ← map_sub]
  simp only [htr]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _)
    (tendsto_traceNorm_mul_filtration_orthogonalProjections V hV hdense T)

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
      d.coeff 0 = 1 ∧ ∀ n, d.coeff (n + 1) = 0 := by
  let c : ℕ → ℝ≥0 := fun n ↦ if n = 0 then 1 else 0
  have hc (n : {n // c n ≠ 0}) : n.1 = 0 := by
    by_contra h
    exact n.2 (by simp [c, h])
  have : Subsingleton {n // c n ≠ 0} :=
    ⟨fun a b ↦ Subtype.ext ((hc a).trans (hc b).symm)⟩
  refine ⟨{
    coeff := c
    antitone_coeff := ?_
    tendsto_coeff := ?_
    source := fun _ ↦ e
    target := fun _ ↦ f
    orthonormal_source := orthonormal_subsingleton_iff.mpr fun _ ↦ he
    orthonormal_target := orthonormal_subsingleton_iff.mpr fun _ ↦ hf
    hasSum_apply := ?_ }, ?_, fun n ↦ ?_⟩
  · intro m n hmn
    by_cases hn : n = 0
    · subst hn
      obtain rfl : m = 0 := Nat.le_zero.mp hmn
      exact le_rfl
    · simp [c, hn]
  · exact tendsto_const_nhds.congr'
      (eventually_atTop.mpr ⟨1, fun n hn ↦ by simp [c, Nat.pos_iff_ne_zero.mp hn]⟩)
  · intro x
    convert hasSum_single (⟨0, by simp [c]⟩ : {n // c n ≠ 0})
      (fun b hb ↦ absurd (Subsingleton.elim _ _) hb) using 1
    simp [c]
  · simp [c]
  · simp [c]

section

open InnerProductSpace

omit [CompleteSpace E] [CompleteSpace F] in
/-- Bessel's inequality bounds the action of a finite sum of singular terms by
any nonnegative upper bound for its coefficients times the norm of the input. -/
private theorem norm_sum_singularTerms_le (c : ℕ → ℝ≥0)
    {e : {n // c n ≠ 0} → E} {f : {n // c n ≠ 0} → F}
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f)
    (s : Finset {n // c n ≠ 0}) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ i ∈ s, (c i : ℝ) ≤ r) (x : E) :
    ‖∑ i ∈ s, ((c i : ℝ) * ⟪e i, x⟫_ℂ) • f i‖ ≤ r * ‖x‖ := by
  let a (i : {n // c n ≠ 0}) : ℂ := (c i : ℝ) * ⟪e i, x⟫_ℂ
  change ‖∑ i ∈ s, a i • f i‖ ≤ _
  apply le_of_sq_le_sq _ (mul_nonneg hr (norm_nonneg x))
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hf.inner_sum a a, map_sum, mul_pow]
  calc
    ∑ i ∈ s, RCLike.re (starRingEnd ℂ (a i) * a i) ≤ ∑ i ∈ s, r ^ 2 * ‖⟪e i, x⟫_ℂ‖ ^ 2 := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
      have hi0 : 0 ≤ (c i : ℝ) := (c i).2
      simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi0, mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (c i).2 hr).mpr (hs i hi)) (sq_nonneg _)
    _ ≤ r ^ 2 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (he.sum_inner_products_le x) (sq_nonneg _)

omit [CompleteSpace E] in
/-- The rank-one terms from two orthonormal families and coefficients tending to zero
are summable in operator norm. -/
private theorem summable_singularTerms (c : ℕ → ℝ≥0) (hc : Tendsto c atTop (𝓝 0))
    {e : {n // c n ≠ 0} → E} {f : {n // c n ≠ 0} → F}
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    Summable (fun i : {n // c n ≠ 0} ↦ ((c i : ℝ) : ℂ) • rankOne ℂ (f i) (e i)) := by
  classical
  let A (i : {n // c n ≠ 0}) : E →L[ℂ] F := ((c i : ℝ) : ℂ) • rankOne ℂ (f i) (e i)
  have hbound (s : Finset {n // c n ≠ 0}) {r : ℝ} (hr : 0 ≤ r)
      (hs : ∀ i ∈ s, (c i : ℝ) ≤ r) : ‖∑ i ∈ s, A i‖ ≤ r := by
    refine ContinuousLinearMap.opNorm_le_bound _ hr fun x ↦ ?_
    simpa only [A, sum_apply, smul_apply, rankOne_apply, smul_smul] using
      norm_sum_singularTerms_le c he hf s hr hs x
  change Summable A
  rw [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff]
  intro ε hε
  have hc' := NNReal.tendsto_coe.mpr hc
  rw [NNReal.coe_zero, Metric.tendsto_atTop] at hc'
  obtain ⟨N, hN⟩ := hc' (ε / 3) (by positivity)
  let initial := (Finset.range N).subtype (fun n ↦ c n ≠ 0)
  have htail (s : Finset {n // c n ≠ 0}) (hs : Disjoint s initial) :
      ‖∑ i ∈ s, A i‖ ≤ ε / 3 := by
    refine hbound s (by positivity) fun i hi ↦ ?_
    have hiN : N ≤ i.val := by
      by_contra! h
      exact (Finset.disjoint_left.mp hs hi) (Finset.mem_subtype.mpr (Finset.mem_range.mpr h))
    have hi0 : 0 ≤ (c i : ℝ) := (c i).2
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hi0] using (hN i hiN).le
  refine ⟨initial, fun s hs t ht ↦ ?_⟩
  rw [neg_add_eq_sub, ← Finset.sum_sdiff_sub_sum_sdiff]
  have hts := htail (t \ s) (disjoint_sdiff_self_left.mono_right hs)
  have hst := htail (s \ t) (disjoint_sdiff_self_left.mono_right ht)
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- Successive norm-maximizing singular vectors of a compact operator yield a singular
expansion. Each step removes a rank-one term, and compactness forces the residual norms
to tend to zero. -/
private theorem nonempty_singularExpansion_of_isCompactOperator (T : E →L[ℂ] F)
    (hT : IsCompactOperator T) : Nonempty (SingularExpansion T) := by
  classical
  let CompactMap := {R : E →L[ℂ] F // IsCompactOperator R}
  have hexists (S : CompactMap) : ∃ x : E, (S.val ≠ 0 → ‖x‖ = 1) ∧
      (S.val = 0 → x = 0) ∧ ‖S.val x‖ = ‖S.val‖ ∧
      S.val.adjoint (S.val x) = (↑‖S.val‖ ^ 2 : ℂ) • x := by
    by_cases hS : S.val = 0
    · exact ⟨0, fun h ↦ (h hS).elim, fun _ ↦ rfl, by simp [hS], by simp [hS]⟩
    have : Nontrivial E := not_subsingleton_iff_nontrivial.mp fun h ↦
      hS (ContinuousLinearMap.ext fun x ↦ by rw [h.elim x 0]; simp)
    obtain ⟨x, hx, hnorm, heig⟩ :=
      exists_unit_norm_eq_opNorm_of_isCompactOperator S.val S.property
    exact ⟨x, fun _ ↦ hx, fun h ↦ (hS h).elim, hnorm, heig⟩
  choose vector hunit hzero hnorm heig using hexists
  let P (x : E) : E →L[ℂ] E := 1 - rankOne ℂ x x
  let residual : ℕ → CompactMap :=
    Nat.rec ⟨T, hT⟩ (fun _ S ↦ ⟨S.val ∘L P (vector S), S.property.comp_clm _⟩)
  let R (n : ℕ) : E →L[ℂ] F := (residual n).val
  let e (n : ℕ) : E := vector (residual n)
  let y (n : ℕ) : F := R n (e n)
  let A (n : ℕ) : E →L[ℂ] F := rankOne ℂ (y n) (e n)
  have hstep (n : ℕ) : R (n + 1) = R n ∘L P (e n) := rfl
  have hsub (n : ℕ) : R (n + 1) = R n - A n := by
    rw [hstep]
    simp [P, A, y, ContinuousLinearMap.comp_sub, comp_rankOne,
      show (1 : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E from rfl]
  have hproj (n : ℕ) : IsStarProjection (P (e n)) := by
    by_cases hn : R n = 0
    · have hz : e n = 0 := hzero (residual n) hn
      simp [P, hz]
    · exact (isStarProjection_rankOne_self (hunit (residual n) hn)).one_sub
  have hproj_zero (n : ℕ) : P (e n) (e n) = 0 := by
    by_cases hn : R n = 0
    · rw [show e n = 0 from hzero (residual n) hn, map_zero]
    · have hn' : ‖e n‖ = 1 := hunit (residual n) hn
      simp [P, inner_self_eq_norm_sq_to_K, hn']
  have horth_source (n : ℕ) (z : E) (hz : R n z = 0) : ⟪e n, z⟫_ℂ = 0 := by
    by_cases hn : R n = 0
    · simp [show e n = 0 from hzero (residual n) hn]
    have h := (R n).adjoint_inner_left z (y n)
    change ⟪(R n).adjoint (R n (e n)), z⟫_ℂ = _ at h
    rw [heig (residual n), inner_smul_left, hz, inner_zero_right] at h
    have hn' : (↑‖R n‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn)
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr (pow_ne_zero _ hn'))
  -- Each residual and its adjoint annihilate the vectors already selected.
  have hkill (n : ℕ) : ∀ i < n, R n (e i) = 0 ∧ (R n).adjoint (y i) = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hadj : (R (n + 1)).adjoint = P (e n) ∘L (R n).adjoint := by
        rw [hstep, ContinuousLinearMap.adjoint_comp, (hproj n).isSelfAdjoint.adjoint_eq]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hin
      · obtain ⟨hRi, hRai⟩ := ih i hi
        constructor
        · simp [hsub, A, hRi, horth_source n (e i) hRi]
        · simp [hadj, hRai]
      · subst i
        constructor
        · simp [hstep, hproj_zero]
        · rw [hadj, ContinuousLinearMap.comp_apply]
          change P (e n) ((R n).adjoint (R n (e n))) = 0
          rw [heig (residual n), map_smul, hproj_zero, smul_zero]
  have hsource (i j : ℕ) (hij : i < j) : ⟪e i, e j⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (horth_source j (e i) (hkill j i hij).1)
  have htarget (i j : ℕ) (hij : i < j) : ⟪y i, y j⟫_ℂ = 0 := by
    change ⟪y i, R j (e j)⟫_ℂ = 0
    rw [← (R j).adjoint_inner_left, (hkill j i hij).2, inner_zero_left]
  have hpartial (n : ℕ) : ∑ i ∈ Finset.range n, A i = T - R n := by
    induction n with
    | zero => simp [show R 0 = T from rfl]
    | succ n ih => rw [Finset.sum_range_succ, ih, hsub]; abel
  have hTy (n : ℕ) : T (e n) = y n := by
    have hz : (∑ i ∈ Finset.range n, A i) (e n) = 0 := by
      rw [sum_apply]
      exact Finset.sum_eq_zero fun i hi ↦ by simp [A, hsource i n (Finset.mem_range.mp hi)]
    rw [hpartial, sub_apply, sub_eq_zero] at hz
    exact hz
  have hanti : Antitone (fun n ↦ ‖R n‖) := by
    refine antitone_nat_of_succ_le fun n ↦ ?_
    rw [hstep]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) ((hproj n).norm_le _))
  -- Consecutive terms of a convergent subsequence have vanishing distance,
  -- which bounds their norms by orthogonality.
  have hlim : Tendsto (fun n ↦ ‖R n‖) atTop (𝓝 0) := by
    obtain ⟨z, _, φ, hφ, hz⟩ :=
      (hT.isCompact_closure_image_closedBall 1).tendsto_subseq (x := y) fun n ↦ by
        refine subset_closure ⟨e n, ?_, hTy n⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        by_cases hn : R n = 0
        · simp [show e n = 0 from hzero (residual n) hn]
        · exact (hunit (residual n) hn).le
    have hdist : Tendsto (fun n ↦ ‖y (φ n) - y (φ (n + 1))‖) atTop (𝓝 0) := by
      have h := (hz.sub (hz.comp (tendsto_add_atTop_nat 1))).norm
      simpa [Function.comp_def] using h
    apply (tendsto_iff_tendsto_subseq_of_antitone hanti hφ.tendsto_atTop).mpr
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hdist
    change ‖R (φ n)‖ ≤ ‖y (φ n) - y (φ (n + 1))‖
    rw [← hnorm (residual (φ n))]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    change ‖y (φ n)‖ ^ 2 ≤ _
    rw [@norm_sub_sq ℂ, htarget _ _ (hφ (Nat.lt_succ_self n))]
    simp
  let c (n : ℕ) : ℝ≥0 := ‖R n‖₊
  let f (i : {n // c n ≠ 0}) : F := (↑(c i : ℝ) : ℂ)⁻¹ • y i
  have hc : Tendsto c atTop (𝓝 0) := NNReal.tendsto_coe.mp (by simpa [c] using hlim)
  have hcn (i : {n // c n ≠ 0}) : ‖R i‖ ≠ 0 :=
    fun h ↦ i.property (NNReal.eq h)
  have he : Orthonormal ℂ (fun i : {n // c n ≠ 0} ↦ e i) := by
    refine ⟨fun i ↦ hunit (residual i) (norm_ne_zero_iff.mp (hcn i)), ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne (fun h : i.val = j.val ↦ hij (Subtype.ext h)) with h | h
    · exact hsource i j h
    · exact inner_eq_zero_symm.mp (hsource j i h)
  have hf : Orthonormal ℂ f := by
    refine ⟨fun i ↦ ?_, ?_⟩
    · have hy : ‖y i‖ = ‖R i‖ := hnorm (residual i)
      change ‖(↑‖R i‖ : ℂ)⁻¹ • y i‖ = 1
      rw [← hy]
      exact norm_smul_inv_norm (norm_ne_zero_iff.mp (hy.trans_ne (hcn i)))
    · intro i j hij
      have hz : ⟪y i, y j⟫_ℂ = 0 := by
        rcases lt_or_gt_of_ne (fun h : i.val = j.val ↦ hij (Subtype.ext h)) with h | h
        · exact htarget i j h
        · exact inner_eq_zero_symm.mp (htarget j i h)
      simp [f, inner_smul_left, inner_smul_right, hz]
  have hA (i : {n // c n ≠ 0}) : ((c i : ℝ) : ℂ) • rankOne ℂ (f i) (e i) = A i := by
    ext x
    have hci : ((c i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hcn i)
    simp only [smul_apply, rankOne_apply, f, smul_smul, A]
    rw [mul_left_comm, mul_inv_cancel₀ hci, mul_one]
  have hsupp : Function.support A ⊆ {n | c n ≠ 0} := by
    intro n hn h
    have hz : R n = 0 := norm_eq_zero.mp (congrArg NNReal.toReal h)
    exact hn (by simp [A, y, hz])
  have hs : Summable (A ∘ (Subtype.val : {n // c n ≠ 0} → ℕ)) :=
    (summable_singularTerms c hc he hf).congr hA
  have hfull := (hasSum_subtype_iff_of_support_subset hsupp).mp hs.hasSum
  have hnat : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, A i) atTop (𝓝 T) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (hlim.congr fun n ↦ ?_)
    rw [hpartial, sub_right_comm, sub_self, zero_sub, norm_neg]
  have hsum : HasSum (A ∘ (Subtype.val : {n // c n ≠ 0} → ℕ)) T :=
    (tendsto_nhds_unique hfull.tendsto_sum_nat hnat) ▸ hs.hasSum
  refine ⟨⟨c, hanti, hc, (fun i ↦ e i), f, he, hf, fun x ↦ ?_⟩⟩
  have hmapped := hsum.map (ContinuousLinearMap.apply ℂ F x)
    (ContinuousLinearMap.apply ℂ F x).continuous
  refine hmapped.congr_fun fun i ↦ ?_
  change _ = A i x
  rw [← hA i]
  simp only [smul_apply, rankOne_apply, smul_smul]

/-- Paper: Theorem C.3.6.1(1)–(2), p. 703. A bounded operator is compact
exactly when it admits a singular expansion.
Deviation: The expansion uses orthonormal vectors only for nonzero coefficients. -/
theorem isCompactOperator_iff_nonempty_singularExpansion (T : E →L[ℂ] F) :
    IsCompactOperator T ↔ Nonempty (SingularExpansion T) := by
  refine ⟨nonempty_singularExpansion_of_isCompactOperator T, ?_⟩
  rintro ⟨d⟩
  let A (i : {n // d.coeff n ≠ 0}) : E →L[ℂ] F :=
    ((d.coeff i : ℝ) : ℂ) • rankOne ℂ (d.target i) (d.source i)
  have hs : Summable A :=
    summable_singularTerms d.coeff d.tendsto_coeff d.orthonormal_source d.orthonormal_target
  have hT : (∑' i, A i) = T := by
    ext x
    have hmapped := hs.hasSum.map (ContinuousLinearMap.apply ℂ F x)
      (ContinuousLinearMap.apply ℂ F x).continuous
    apply hmapped.unique
    refine (d.hasSum_apply x).congr_fun fun i ↦ ?_
    change A i x = _
    simp only [A, smul_apply, rankOne_apply, smul_smul]
  have hc (i : {n // d.coeff n ≠ 0}) : IsCompactOperator (A i) := by
    change IsCompactOperator (((d.coeff i : ℝ) : ℂ) • rankOne ℂ (d.target i) (d.source i))
    rw [rankOne_def']
    exact ((isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ (d.target i))).comp_clm
        (innerSL ℂ (d.source i))).smul _
  rw [← hT]
  apply isCompactOperator_of_tendsto hs.hasSum
  exact Eventually.of_forall fun s ↦ (compactOperator (RingHom.id ℂ) E F).sum_mem
    (fun i _ ↦ hc i)

end

omit [CompleteSpace E] [CompleteSpace F] in
/-- After including every term with index below `N`, the operator-norm error
of the finite sum is bounded by the coefficient at `N`. -/
private theorem SingularExpansion.norm_sub_sum_le_coeff {T : E →L[ℂ] F}
    (d : SingularExpansion T) (N : ℕ) (s : Finset {n // d.coeff n ≠ 0})
    (hs : ∀ i : {n // d.coeff n ≠ 0}, (i : ℕ) < N → i ∈ s) :
    ‖T - ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
      (innerSL ℂ (d.source i)).smulRight (d.target i)‖ ≤ (d.coeff N : ℝ) := by
  classical
  let ι := {n // d.coeff n ≠ 0}
  let A (i : ι) : E →L[ℂ] F :=
    ((d.coeff i : ℝ) : ℂ) • (innerSL ℂ (d.source i)).smulRight (d.target i)
  let S (s : Finset ι) := ∑ i ∈ s, A i
  have happly (s : Finset ι) (x : E) :
      S s x = ∑ i ∈ s, (((d.coeff i : ℝ) : ℂ) * ⟪d.source i, x⟫_ℂ) • d.target i := by
    simp only [S, A, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  have hpointwise (x : E) : Tendsto (fun s ↦ S s x) atTop (𝓝 (T x)) := by
    simpa only [HasSum, SummationFilter.unconditional_filter, happly] using d.hasSum_apply x
  let c : ℝ := d.coeff N
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  -- Use Pythagoras in the target and Bessel's inequality in the source.
  have htail (u : Finset ι) (hu : ∀ i ∈ u, N ≤ (i : ℕ)) (x : E) :
      ‖S u x‖ ≤ c * ‖x‖ := by
    apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg _))
    rw [happly, mul_pow]
    calc
      _ = ∑ i ∈ u, ‖((d.coeff i : ℝ) : ℂ) * ⟪d.source i, x⟫_ℂ‖ ^ 2 := by
        simpa only [LinearIsometry.toSpanSingleton_apply] using
          d.orthonormal_target.orthogonalFamily.norm_sum
            (fun i ↦ ((d.coeff i : ℝ) : ℂ) * ⟪d.source i, x⟫_ℂ) u
      _ ≤ ∑ i ∈ u, c ^ 2 * ‖⟪d.source i, x⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (NNReal.coe_nonneg _) hc).mpr (NNReal.coe_le_coe.mpr
            (d.antitone_coeff (hu i hi)))) (sq_nonneg _)
      _ ≤ c ^ 2 * ‖x‖ ^ 2 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (d.orthonormal_source.sum_inner_products_le x)
          (sq_nonneg c)
  change ‖T - S s‖ ≤ c
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x ↦ ?_
  -- Pass the finite tail bound to the pointwise limit.
  have hlim : Tendsto (fun t ↦ ‖S t x - S s x‖) atTop (𝓝 ‖(T - S s) x‖) := by
    simpa only [sub_apply] using
      ((hpointwise x).sub tendsto_const_nhds).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop s] with t ht
  have hdiff : S t - S s = S (t \ s) := by
    have hsum : S (t \ s) + S s = S t := Finset.sum_sdiff ht
    exact (eq_sub_of_add_eq hsum).symm
  rw [← sub_apply, hdiff]
  refine htail _ (fun i hi ↦ ?_) x
  exact Nat.le_of_not_gt fun hiN ↦ (Finset.mem_sdiff.mp hi).2 (hs i hiN)

-- Keep the completeness hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem C.3.6.1, p. 703. The series of rank-one maps in a
singular expansion converges in operator norm. -/
theorem SingularExpansion.hasSum_opNorm {T : E →L[ℂ] F} (d : SingularExpansion T) :
    HasSum (fun n : {n // d.coeff n ≠ 0} ↦
      ((d.coeff n : ℝ) : ℂ) • (innerSL ℂ (d.source n)).smulRight (d.target n)) T := by
  classical
  change Tendsto (fun s : Finset {n // d.coeff n ≠ 0} ↦
    ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
      (innerSL ℂ (d.source i)).smulRight (d.target i)) atTop (𝓝 T)
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp d.tendsto_coeff ε hε
  have hcoeff : (d.coeff N : ℝ) < ε := by
    simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      using hN N le_rfl
  refine ⟨(Finset.range N).subtype (fun n ↦ d.coeff n ≠ 0), fun s hs ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (d.norm_sub_sum_le_coeff N s fun i hi ↦
    hs (Finset.mem_subtype.mpr (Finset.mem_range.mpr hi))).trans_lt hcoeff

-- TODO(paper-gap): The proof on p. 704 bounds the squared norm using any
-- coefficient. For a leading singular vector, the squared norm is the square
-- of the first coefficient.

/-- Paper: Theorem C.3.6.1, p. 703. The first coefficient of a singular
expansion equals the operator norm, including for the zero operator. -/
theorem SingularExpansion.coeff_zero_eq_opNorm {T : E →L[ℂ] F} (d : SingularExpansion T) :
    (d.coeff 0 : ℝ) = ‖T‖ := by
  apply le_antisymm
  · by_cases h : d.coeff 0 = 0
    · simpa only [h, NNReal.coe_zero] using norm_nonneg T
    let i : {n // d.coeff n ≠ 0} := ⟨0, h⟩
    have hT : T (d.source i) = ((d.coeff i : ℝ) * ⟪d.source i, d.source i⟫_ℂ) • d.target i :=
      (d.hasSum_apply (d.source i)).unique (hasSum_single i fun j hj ↦ by
        rw [d.orthonormal_source.inner_eq_zero hj, mul_zero, zero_smul])
    have hinner : ⟪d.source i, d.source i⟫_ℂ = 1 := by
      simp [inner_self_eq_norm_sq_to_K, d.orthonormal_source.norm_eq_one i]
    have hi0 : 0 ≤ (d.coeff i : ℝ) := (d.coeff i).2
    simpa only [hT, hinner, mul_one, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hi0, d.orthonormal_target.norm_eq_one i,
      d.orthonormal_source.norm_eq_one i] using T.le_opNorm (d.source i)
  · refine ContinuousLinearMap.opNorm_le_bound T (d.coeff 0).2 fun x ↦ ?_
    refine le_of_tendsto' (d.hasSum_apply x).norm fun s ↦ ?_
    exact norm_sum_singularTerms_le d.coeff d.orthonormal_source d.orthonormal_target
      s (d.coeff 0).2 (fun i _ ↦ d.antitone_coeff (Nat.zero_le i.val)) x

-- Keep the completeness hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: §C.3.6, p. 704. The coefficients of a singular expansion are
the approximation numbers and are independent of the orthonormal vectors.
Deviation: The sequences are indexed from zero and include any zero tail. -/
theorem SingularExpansion.coeff_eq_approximationNumber {T : E →L[ℂ] F}
    (d : SingularExpansion T) (n : ℕ) :
    (d.coeff n : ℝ) = approximationNumber T n := by
  classical
  apply le_antisymm
  · refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    by_cases hn : d.coeff n = 0
    · simp [hn]
    -- Every admissible approximant kills a nonzero combination of the first n + 1 vectors.
    let index (i : Fin (n + 1)) : {k // d.coeff k ≠ 0} :=
      ⟨i, ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le
        (d.antitone_coeff (Nat.lt_succ_iff.mp i.isLt)))⟩
    have hindex : Injective index := fun _ _ h ↦ Fin.val_injective (congrArg Subtype.val h)
    let e := d.source ∘ index
    let f := d.target ∘ index
    have he : Orthonormal ℂ e := d.orthonormal_source.comp index hindex
    have hf : Orthonormal ℂ f := d.orthonormal_target.comp index hindex
    let v := Fintype.linearCombination ℂ e
    let R := S.toLinearMap.rangeRestrict.comp v
    have : FiniteDimensional ℂ S.toLinearMap.range :=
      Module.rank_lt_aleph0_iff.mp (hS.trans_lt Cardinal.natCast_lt_aleph0)
    have hker : R.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_pi, Fintype.card_fin]
      exact Nat.lt_succ_of_le (Module.finrank_le_of_rank_le hS))
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (v a) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    have hxnorm : 0 < ‖v a‖ := norm_pos_iff.mpr fun h ↦ ha0
      (linearIndependent_iff_injective_fintypeLinearCombination.mp he.linearIndependent
        (h.trans (map_zero v).symm))
    have hTe (i : Fin (n + 1)) : T (e i) = ((d.coeff i : ℝ) : ℂ) • f i := by
      let j := index i
      change T (d.source j) = ((d.coeff j : ℝ) : ℂ) • d.target j
      have hsum := d.hasSum_apply (d.source j)
      rw [hsum.unique (hasSum_single j fun k hk ↦ by
        simp [d.orthonormal_source.inner_eq_zero hk])]
      simp [d.orthonormal_source.norm_eq_one j]
    have hTx : T (v a) = ∑ i, (a i * ((d.coeff i : ℝ) : ℂ)) • f i := by
      simp only [v, Fintype.linearCombination_apply, map_sum, map_smul, hTe, smul_smul]
    have hlower : (d.coeff n : ℝ) * ‖v a‖ ≤ ‖T (v a)‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      have he_sq : ‖v a‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
        simpa only [v, Fintype.linearCombination_apply, LinearIsometry.toSpanSingleton_apply]
          using he.orthogonalFamily.norm_sum a Finset.univ
      have hf_sq : ‖T (v a)‖ ^ 2 = ∑ i, ‖a i * ((d.coeff i : ℝ) : ℂ)‖ ^ 2 := by
        rw [hTx]
        simpa only [LinearIsometry.toSpanSingleton_apply] using
          hf.orthogonalFamily.norm_sum (fun i ↦ a i * ((d.coeff i : ℝ) : ℂ)) Finset.univ
      rw [mul_pow, he_sq, Finset.mul_sum, hf_sq]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
        mul_pow, mul_comm (‖a i‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).mpr
          (NNReal.coe_le_coe.mpr (d.antitone_coeff (Nat.lt_succ_iff.mp i.isLt)))) (sq_nonneg _)
    have hbound := (S - T).le_opNorm (v a)
    rw [sub_apply, hSx, zero_sub, norm_neg] at hbound
    exact le_of_mul_le_mul_right (hlower.trans hbound) hxnorm
  · -- Truncating at n gives an admissible approximant with error at most the nth coefficient.
    let s := (Finset.range n).subtype (fun i ↦ d.coeff i ≠ 0)
    let S : E →L[ℂ] F := ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
      (innerSL ℂ (d.source i)).smulRight (d.target i)
    have hrange : S.toLinearMap.range ≤ Submodule.span ℂ (↑(s.image d.target) : Set F) := by
      rintro _ ⟨x, rfl⟩
      change S x ∈ Submodule.span ℂ (↑(s.image d.target) : Set F)
      simp only [S, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
      exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_image_of_mem d.target hi))
    have hcard : (s.image d.target).card ≤ n := by
      refine Finset.card_image_le.trans ?_
      rw [show s.card = ((Finset.range n).filter fun i ↦ d.coeff i ≠ 0).card
        from Finset.card_subtype _ _]
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
    have hS := (Submodule.rank_mono hrange).trans
      ((rank_span_finset_le (s.image d.target)).trans (Nat.cast_le.mpr hcard))
    have happ : approximationNumber T n ≤ ‖S - T‖ :=
      csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S, hS, rfl⟩
    rw [norm_sub_rev] at happ
    exact happ.trans (d.norm_sub_sum_le_coeff n s fun i hi ↦
      Finset.mem_subtype.mpr (Finset.mem_range.mpr hi))

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

omit [CompleteSpace E] in
/-- Square summability on a Hilbert basis gives an operator-norm limit of finite-rank maps. -/
private theorem isCompactOperator_of_summable_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (h : Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ))) :
    IsCompactOperator T := by
  let A (i : ι) : E →L[ℂ] F := InnerProductSpace.rankOne ℂ (T (b i)) (b i)
  have hbound (s : Finset ι) : ‖∑ i ∈ s, A i‖ ≤ √(∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
    rw [sum_apply]
    calc
      ‖∑ i ∈ s, A i x‖ ≤ ∑ i ∈ s, ‖T (b i)‖ * ‖⟪b i, x⟫_ℂ‖ := by
        simpa only [A, InnerProductSpace.rankOne_apply, norm_smul, mul_comm] using
          (norm_sum_le s (fun i ↦ A i x))
      _ ≤ √(∑ i ∈ s, ‖T (b i)‖ ^ 2) * √(∑ i ∈ s, ‖⟪b i, x⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ ≤ √(∑ i ∈ s, ‖T (b i)‖ ^ 2) * ‖x‖ := by
        rw [← Real.sqrt_sq (norm_nonneg x)]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (b.orthonormal.sum_inner_products_le x)) (Real.sqrt_nonneg _)
  have hA : Summable A := by
    refine summable_iff_vanishing_norm.mpr fun ε hε ↦ ?_
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp h (ε ^ 2) (by positivity)
    exact ⟨s, fun t ht ↦ (hbound t).trans_lt
      ((Real.sqrt_lt' hε).mpr ((le_abs_self _).trans_lt (hs t ht)))⟩
  have hsum : (∑' i, A i) = T := by
    ext x
    have hpoint : HasSum (fun i ↦ A i x) (T x) := by
      simpa only [A, InnerProductSpace.rankOne_apply, b.repr_apply_apply, map_smul] using
        T.hasSum (b.hasSum_repr x)
    exact ((ContinuousLinearMap.apply ℂ F x).hasSum hA.hasSum).unique hpoint
  rw [← hsum]
  refine isCompactOperator_of_tendsto hA.hasSum (Eventually.of_forall fun s ↦ ?_)
  refine (compactOperator (RingHom.id ℂ) E F).sum_mem fun i _ ↦ ?_
  change IsCompactOperator (InnerProductSpace.rankOne ℂ (T (b i)) (b i))
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ (T (b i)))).comp_clm (innerSL ℂ (b i))

omit [CompleteSpace E] [CompleteSpace F] in
/-- Parseval in the given basis and orthogonality in the singular expansion identify the
two square-summability criteria by summing the same nonnegative family in either order. -/
private theorem SingularExpansion.summable_sq_iff_summable_basis {ι : Type*}
    (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] F} (d : SingularExpansion T) :
    Summable (fun n ↦ (d.coeff n : ℝ) ^ (2 : ℕ)) ↔
      Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
  let J := {n : ℕ // d.coeff n ≠ 0}
  let a (j : J) (i : ι) : ℝ := (d.coeff j : ℝ) ^ 2 * ‖⟪d.source j, b i⟫_ℂ‖ ^ 2
  have hrow (j : J) : HasSum (a j) ((d.coeff j : ℝ) ^ 2) := by
    have hparseval : HasSum (fun i ↦ ‖⟪d.source j, b i⟫_ℂ‖ ^ (2 : ℕ)) 1 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
        b.repr_apply_apply, norm_inner_symm (b _) (d.source j),
        d.orthonormal_source.norm_eq_one j, one_pow] using
        lp.hasSum_norm (p := 2) (by norm_num) (b.repr (d.source j))
    simpa only [a, mul_one] using hparseval.mul_left ((d.coeff j : ℝ) ^ (2 : ℕ))
  have hcol (i : ι) : HasSum (fun j ↦ a j i) (‖T (b i)‖ ^ 2) := by
    let c (j : J) : ℂ := (d.coeff j : ℝ) * ⟪d.source j, b i⟫_ℂ
    have hnorm (s : Finset J) : ‖∑ j ∈ s, c j • d.target j‖ ^ 2 = ∑ j ∈ s, a j i := by
      simpa only [LinearIsometry.toSpanSingleton_apply, c, a, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (NNReal.coe_nonneg _), mul_pow] using
        d.orthonormal_target.orthogonalFamily.norm_sum c s
    exact ((d.hasSum_apply (b i)).norm.pow 2).congr hnorm
  have hrows : Summable (fun p : J × ι ↦ a p.1 p.2) ↔
      Summable (fun j : J ↦ (d.coeff j : ℝ) ^ (2 : ℕ)) := by
    have hnonneg (p : J × ι) : 0 ≤ a p.1 p.2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have htsum (j : J) : (∑' i, a j i) = (d.coeff j : ℝ) ^ 2 := (hrow j).tsum_eq
    rw [summable_prod_of_nonneg hnonneg, and_iff_right (fun j ↦ (hrow j).summable)]
    simp only [htsum]
  have hcols : Summable (fun p : ι × J ↦ a p.2 p.1) ↔
      Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
    have hnonneg (p : ι × J) : 0 ≤ a p.2 p.1 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have htsum (i : ι) : (∑' j, a j i) = ‖T (b i)‖ ^ 2 := (hcol i).tsum_eq
    rw [summable_prod_of_nonneg hnonneg, and_iff_right (fun i ↦ (hcol i).summable)]
    simp only [htsum]
  have hsupp : Function.support (fun n ↦ (d.coeff n : ℝ) ^ (2 : ℕ)) ⊆
      {n | d.coeff n ≠ 0} := by
    intro n hn hz
    exact hn (by simp [hz])
  have hsub : Summable (fun j : J ↦ (d.coeff j : ℝ) ^ (2 : ℕ)) ↔
      Summable (fun n ↦ (d.coeff n : ℝ) ^ (2 : ℕ)) :=
    exists_congr fun _ ↦ hasSum_subtype_iff_of_support_subset hsupp
  exact hsub.symm.trans (hrows.symm.trans ((Equiv.prodComm ι J).summable_iff.symm.trans hcols))

/-- Paper: Definition C.3.6.2(2), p. 704. An operator is Hilbert-Schmidt
exactly when the squared norms of the images of any given Hilbert basis
form a summable family.
Deviation: This checks the index-two class against the basis criterion. -/
theorem mem_hilbertSchmidtOperators_iff_summable_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) :
    T ∈ hilbertSchmidtOperators E F ↔ Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
  change (IsCompactOperator T ∧ Summable (fun n ↦ approximationNumber T n ^ (2 : ℝ))) ↔ _
  simp only [Real.rpow_two]
  have hcompact (hT : IsCompactOperator T) :
      Summable (fun n ↦ approximationNumber T n ^ (2 : ℕ)) ↔
        Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
    obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hT
    simpa only [d.coeff_eq_approximationNumber] using d.summable_sq_iff_summable_basis b
  refine ⟨fun ⟨hT, hs⟩ ↦ (hcompact hT).mp hs, fun hs ↦ ?_⟩
  have hT := isCompactOperator_of_summable_basis b T hs
  exact ⟨hT, (hcompact hT).mpr hs⟩

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
