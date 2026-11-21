module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular

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
      atTop (𝓝 (hilbertTrace T)) := by sorry

/-- Paper: Remark C.3.5.2, p. 699. The finite sums of pairwise orthogonal
projections converge strongly to the identity exactly when the algebraic
sum of the subspaces is dense. -/
theorem tendsto_sum_orthogonalProjections_iff_dense_iSup (hV : PairwiseOrthogonal) :
    (∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x)) ↔
      Dense ((⨆ i, (V i : Submodule ℂ H)) : Set H) := by sorry

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
    approximationNumber T n = T.toLinearMap.singularValues n := by sorry

end ApproximationNumbers

section SingularValues

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Lemma C.3.5.3(1), p. 700. The adjoint of a compact endomorphism is compact. -/
theorem isCompactOperator_adjoint_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) : IsCompactOperator A.adjoint := by sorry

/-- Paper: Lemma C.3.5.3(1), p. 700. A compact endomorphism and its adjoint
have the same singular values at every index up to the Hilbert space dimension.
Deviation: The singular values use the approximation-number definition with zero-based indices. -/
theorem approximationNumber_adjoint (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber A n = approximationNumber A.adjoint n := by sorry

/-- Paper: Lemma C.3.5.3(2), p. 700. The first singular value of a compact
endomorphism equals its operator norm.
Deviation: The first approximation number has index zero. -/
theorem approximationNumber_zero_eq_opNorm (A : H →L[ℂ] H) (hA : IsCompactOperator A) :
    approximationNumber A 0 = ‖A‖ := by sorry

-- TODO(paper-gap): The proof of (C.3.5.4) uses global weak continuity of the
-- quadratic form of a compact operator and weak compactness of the unit sphere.
-- The quadratic form is weakly continuous on bounded sets, and the closed unit
-- ball is weakly compact. The proof also writes the rank-one spectral
-- projector in (C.3.5.5) as a projection onto a kernel, and the tail span
-- argument can fail for repeated eigenvalues. The min-max identities still hold.
-- The polar isometry used in part (1) has initial space (ker A)ᗮ.

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the smallest of
the attained maxima of the norm of A on the unit sphere of each orthogonal
complement of an n-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_min_max (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ maxima : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} → ℝ,
      (∀ V, IsGreatest {r | ∃ x ∈ Submodule.orthogonal (Subtype.val V), ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V)) ∧
        IsLeast (Set.range maxima) (approximationNumber A n) := by sorry

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

/-- Paper: Lemma C.3.5.4(2), p. 701. The singular value of a compact
endomorphism composed on the right by a bounded operator is bounded by the
same singular value times the norm of the right factor.
Deviation: The approximation-number index starts at zero. -/
theorem approximationNumber_mul_le_right (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber (A * B) n ≤ approximationNumber A n * ‖B‖ := by sorry

/-- Paper: Lemma C.3.5.4(2), p. 701. The singular value of a compact
endomorphism composed on the left by a bounded operator is bounded by the
same singular value times the norm of the left factor.
Deviation: The approximation-number index starts at zero. -/
theorem approximationNumber_mul_le_left (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber (B * A) n ≤ approximationNumber A n * ‖B‖ := by sorry

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

/-- Paper: Definition C.3.6.2(1), p. 704. A rank-one map belongs to every
Schatten class.
Deviation: This checks class membership on rank-one maps. -/
theorem smulRight_mem_schattenClass {p : ℝ} (hp : 1 ≤ p) (φ : E →L[ℂ] ℂ) (f : F) :
    φ.smulRight f ∈ schattenClass E F p hp := by sorry

/-- Paper: Definition C.3.6.2(1), p. 704. A rank-one map has Schatten norm
equal to the product of the norms of its functional and its vector.
Deviation: This checks the normalization of the Schatten norm for all indices. -/
theorem schattenNorm_smulRight {p : ℝ} (hp : 1 ≤ p) (φ : E →L[ℂ] ℂ) (f : F) :
    schattenNorm ⟨φ.smulRight f, smulRight_mem_schattenClass hp φ f⟩ = ‖φ‖ * ‖f‖ := by sorry

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
    |approximationNumber A n - approximationNumber B n| ≤ ‖A - B‖ := by sorry

/-- Paper: Lemma C.3.6.3(3), p. 704. The approximation number of a product
at the sum of two one-based indices is bounded by the product of the
approximation numbers of its factors at the corresponding indices.
Deviation: The one-based index sum becomes m + n + 1 in zero-based indexing. -/
theorem approximationNumber_comp_le (A : F →L[ℂ] G) (B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (A.comp B) (m + n + 1) ≤
      approximationNumber A m * approximationNumber B n := by sorry

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
    tensorToFiniteRank z ∈ schattenClass E F p hp := by sorry

/-- Paper: (C.3.6.8), p. 705. The norm of the dual of a Hilbert space satisfies
the parallelogram identity.
Deviation: This supplies the compatible inner product on the dual factor. -/
theorem strongDual_parallelogram (φ ψ : StrongDual ℂ E) :
    ‖φ + ψ‖ * ‖φ + ψ‖ + ‖φ - ψ‖ * ‖φ - ψ‖ =
      2 * (‖φ‖ * ‖φ‖ + ‖ψ‖ * ‖ψ‖) := by sorry

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
      (InnerProductSpace.toDual ℂ E).symm φ⟫_ℂ := by sorry

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
