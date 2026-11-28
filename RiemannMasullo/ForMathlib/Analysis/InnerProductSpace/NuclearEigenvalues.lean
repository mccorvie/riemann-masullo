module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearFiniteQuotient
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # Absolute eigenvalue lower bounds for the Hilbert nuclear norm

Finite continuous coordinate quotients give lower bounds without a coordinate
conditioning factor. Gram-Schmidt preserves the triangular eigenvalue diagonal;
a diagonal phase contraction then bounds its absolute sum by the nuclear norm.
-/

public noncomputable section
open Set Function Module InnerProductSpace
open scoped InnerProductSpace
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Absolute diagonal sums in an orthonormal basis are bounded by the trace norm. -/
theorem sum_norm_diagonal_le_traceNorm {m : ℕ} (b : OrthonormalBasis (Fin m) ℂ H)
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) :
    (∑ i : Fin m, ‖inner ℂ (b i) (A (b i))‖) ≤ traceNorm ⟨A,hA⟩ := by
  classical
  let : FiniteDimensional ℂ H := b.toBasis.finiteDimensional_of_finite
  choose c hc hcz using fun i : Fin m ↦ Complex.exists_norm_eq_mul_self (inner ℂ (b i) (A (b i)))
  let D : H →L[ℂ] H := (b.toBasis.constr ℂ (fun i ↦ c i • b i)).toContinuousLinearMap
  have hD (x : H) (i : Fin m) : inner ℂ (b i) (D x) = c i * inner ℂ (b i) x := by
    change inner ℂ (b i) ((b.toBasis.constr ℂ (fun i ↦ c i • b i)) x) = _
    rw [Basis.constr_apply_fintype]
    simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    simp [b.repr_apply_apply, mul_comm]
  have hDnorm : ‖D‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← b.sum_sq_norm_inner_right (D x), ← b.sum_sq_norm_inner_right x]
    simp only [hD, norm_mul, hc, one_mul, le_refl]
  have hDA := mul_mem_nuclearEndomorphisms_left D (⟨A,hA⟩ : nuclearEndomorphisms H)
  have hbound := (norm_hilbertTrace_le (⟨D*A,hDA⟩ : nuclearEndomorphisms H)).trans
    (traceNorm_mul_left_le D ⟨A,hA⟩)
  have hbound' : ‖hilbertTrace ⟨D*A,hDA⟩‖ ≤ traceNorm ⟨A,hA⟩ := hbound.trans
    ((mul_le_mul_of_nonneg_right hDnorm
      ((norm_nonneg (hilbertTrace ⟨A,hA⟩)).trans (norm_hilbertTrace_le _))).trans_eq (one_mul _))
  obtain ⟨hn,ht⟩ := nuclear_trace_finiteBasis b.toBasis (D*A)
  have ht' : hilbertTrace ⟨D*A,hDA⟩ = ((∑ i : Fin m, ‖inner ℂ (b i) (A (b i))‖ : ℝ) : ℂ) := by
    rw [ht, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [b.coe_toBasis_repr_apply, b.repr_apply_apply]
    change inner ℂ (b i) (D (A (b i))) = _
    rw [hD]
    exact (hcz i).symm
  rw [ht', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ ↦ norm_nonneg _))] at hbound'
  exact hbound'

/-- Gram-Schmidt preserves the diagonal of an operator presented in an eigenbasis. -/
theorem exists_orthonormalBasis_eigen_diagonal {m : ℕ} (b : Basis (Fin m) ℂ H)
    (A : H →L[ℂ] H) (μ : Fin m → ℂ) (heig : ∀ i, A (b i) = μ i • b i) :
    ∃ w : OrthonormalBasis (Fin m) ℂ H, ∀ i, inner ℂ (w i) (A (w i)) = μ i := by
  classical
  let : FiniteDimensional ℂ H := b.finiteDimensional_of_finite
  have hdim : Module.finrank ℂ H = Fintype.card (Fin m) := Module.finrank_eq_card_basis b
  let w := gramSchmidtOrthonormalBasis hdim (fun i ↦ b i)
  refine ⟨w,fun i ↦ ?_⟩
  let V := Submodule.span ℂ (b '' Set.Iio i)
  have hwi : w i ∈ Submodule.span ℂ (b '' Set.Iic i) := by
    have hne : gramSchmidtNormed ℂ (fun i ↦ b i) i ≠ 0 :=
      (gramSchmidtNormed_linearIndependent b.linearIndependent).ne_zero i
    rw [show w i = gramSchmidtNormed ℂ (fun i ↦ b i) i from
      gramSchmidtOrthonormalBasis_apply hdim hne, gramSchmidtNormed]
    exact (Submodule.span ℂ (b '' Set.Iic i)).smul_mem _ (gramSchmidt_mem_span ℂ b le_rfl)
  have hmap : Submodule.span ℂ (b '' Set.Iic i) ≤
      V.comap (A.toLinearMap - μ i • LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hji,rfl⟩
    change A (b j) - μ i • b j ∈ V
    rw [heig j, ← sub_smul]
    by_cases hji' : j = i
    · subst j
      simp only [sub_self, zero_smul, Submodule.zero_mem]
    · exact V.smul_mem _ (Submodule.subset_span ⟨j,lt_of_le_of_ne hji hji',rfl⟩)
  have horth : V ≤ (innerSL ℂ (w i)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hji,rfl⟩
    change inner ℂ (w i) (b j) = 0
    exact gramSchmidtOrthonormalBasis_inv_triangular hdim (fun i ↦ b i) hji
  have hz := horth (hmap hwi)
  change inner ℂ (w i) (A (w i) - μ i • w i) = 0 at hz
  rw [inner_sub_right, inner_smul_right, orthonormal_iff_ite.mp w.orthonormal, ite_eq_left rfl, mul_one] at hz
  exact sub_eq_zero.mp hz

/-- The absolute eigenvalue sum in any finite eigenbasis is bounded by the trace norm. -/
theorem sum_norm_eigenvalues_le_traceNorm {m : ℕ} (b : Basis (Fin m) ℂ H)
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (μ : Fin m → ℂ)
    (heig : ∀ i, A (b i) = μ i • b i) :
    (∑ i : Fin m, ‖μ i‖) ≤ traceNorm ⟨A,hA⟩ := by
  obtain ⟨w,hw⟩ := exists_orthonormalBasis_eigen_diagonal b A μ heig
  simpa only [hw] using sum_norm_diagonal_le_traceNorm w A hA

/-- Every finite diagonal coordinate quotient gives an absolute eigenvalue lower
bound in the original Hilbert trace norm, without a coordinate norm factor. -/
theorem sum_norm_eigen_coordinates_le_traceNorm (m : ℕ)
    (L : H →L[ℂ] (Fin m → ℂ)) (hL : Surjective L)
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (μ : Fin m → ℂ)
    (hLA : ∀ x i, L (A x) i = μ i * L x i) :
    (∑ i : Fin m, ‖μ i‖) ≤ traceNorm ⟨A,hA⟩ := by
  classical
  let K : ClosedSubmodule ℂ H := ⟨L.ker, L.isClosed_ker⟩
  let : IsClosed (K.toSubmodule : Set H) := K.isClosed
  let Q := H ⧸ K.toSubmodule
  let q : H →L[ℂ] Q := K.toSubmodule.mkQL
  let J : Q →ₗᵢ[ℂ] H := quotientOrthogonalSection K
  let e : Q ≃ₗ[ℂ] (Fin m → ℂ) := L.toLinearMap.quotKerEquivOfSurjective hL
  let b : Basis (Fin m) ℂ Q := Basis.ofEquivFun e
  let AQ := q.comp (A.comp J.toContinuousLinearMap)
  have heq (x : H) : e (q x) = L x :=
    LinearMap.quotKerEquivOfSurjective_apply_mk L.toLinearMap hL x
  have hqJ (x : Q) : q (J x) = x := quotientOrthogonalSection_rightInverse K x
  have hEA (x : Q) (i : Fin m) : e (AQ x) i = μ i * e x i := by
    change e (q (A (J x))) i = _
    rw [heq, hLA, ← heq, hqJ]
  have heb (i : Fin m) : e (b i) = Pi.single i 1 := by
    simp only [b, Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  have heig (i : Fin m) : AQ (b i) = μ i • b i := by
    apply e.injective
    ext j
    rw [hEA, map_smul, Pi.smul_apply, smul_eq_mul, heb]
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  obtain ⟨hn,hb⟩ := traceNorm_sandwich_le A hA J.toContinuousLinearMap q
  have hqnorm : ‖q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    exact (Submodule.Quotient.norm_mk_le K.toSubmodule x).trans_eq (one_mul _).symm
  have hprod : ‖q‖ * ‖J.toContinuousLinearMap‖ ≤ 1 :=
    (mul_le_mul hqnorm J.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (sum_norm_eigenvalues_le_traceNorm b AQ hn μ heig).trans (hb.trans _)
  exact (mul_le_mul_of_nonneg_right hprod
    ((norm_nonneg (hilbertTrace ⟨A,hA⟩)).trans (norm_hilbertTrace_le _))).trans_eq (one_mul _)

/-- A nuclear operator has absolutely summable diagonal eigen-coordinates whenever
its continuous rows admit biorthogonal witnesses. No completeness of that family
and no uniform bound on its coordinate functionals is assumed. -/
theorem nuclear_eigen_coordinates_summable {ι : Type*} [DecidableEq ι]
    (L : ι → H →L[ℂ] ℂ) (v : ι → H)
    (hrow : ∀ i j, L i (v j) = if i = j then 1 else 0)
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (μ : ι → ℂ)
    (hLA : ∀ x i, L i (A x) = μ i * L i x) :
    Summable (fun i ↦ ‖μ i‖) ∧ (∑' i, ‖μ i‖) ≤ traceNorm ⟨A,hA⟩ := by
  classical
  have hfinite (s : Finset ι) : ∑ i ∈ s, ‖μ i‖ ≤ traceNorm ⟨A,hA⟩ := by
    let e := Fintype.equivFin s
    let n : Fin (Fintype.card s) → ι := fun i ↦ (e.symm i).val
    have hn : Injective n := Subtype.val_injective.comp e.symm.injective
    let R := ContinuousLinearMap.pi (fun i : Fin (Fintype.card s) ↦ L (n i))
    have hR : Surjective R := by
      intro y
      refine ⟨∑ i, y i • v (n i),funext fun j ↦ ?_⟩
      simp only [R, ContinuousLinearMap.pi_apply, map_sum, map_smul, smul_eq_mul,
        hrow, hn.eq_iff]
      simp
    have hb := sum_norm_eigen_coordinates_le_traceNorm (Fintype.card s) R hR A hA
      (fun i ↦ μ (n i)) (fun x i ↦ by simpa only [R, ContinuousLinearMap.pi_apply] using hLA x (n i))
    have hsum : (∑ i ∈ s, ‖μ i‖) = ∑ i : Fin (Fintype.card s), ‖μ (n i)‖ := by
      have hs' : (∑ i ∈ s, ‖μ i‖) = ∑ i : s, ‖μ i.val‖ :=
        Finset.sum_subtype s (fun _ ↦ Iff.rfl) (fun i ↦ ‖μ i‖)
      exact hs'.trans (e.symm.sum_comp (fun i : s ↦ ‖μ i.val‖)).symm
    exact hsum.trans_le hb
  have hs : Summable (fun i ↦ ‖μ i‖) := summable_of_sum_le (fun i ↦ norm_nonneg _) hfinite
  exact ⟨hs, le_of_tendsto hs.hasSum (Filter.Eventually.of_forall hfinite)⟩

end RiemannMasullo
