module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.QuotientLayer
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRetraction
public import Mathlib.LinearAlgebra.Trace

/-! # Nuclear trace-norm lower bounds from finite quotients -/

public noncomputable section
open Set Function Module
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a finite-dimensional Hilbert space the nuclear trace is the algebraic
trace in any basis, with no orthogonality assumption on that basis. -/
theorem nuclear_trace_finiteBasis {ι : Type*} [Fintype ι] (b : Basis ι ℂ H) (A : H →L[ℂ] H) :
    ∃ hA : IsNuclearOperator A,
      hilbertTrace ⟨A,hA⟩ = ∑ i, b.repr (A (b i)) i := by
  classical
  let : FiniteDimensional ℂ H := b.finiteDimensional_of_finite
  let φ (i : ι) : H →L[ℂ] ℂ := (b.coord i).toContinuousLinearMap
  let R (i : ι) : H →L[ℂ] H := (φ i).smulRight (A (b i))
  have hR (i : ι) : IsNuclearOperator (R i) := isNuclearOperator_smulRight _ _
  have he : ∑ i, R i = A := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sum_apply, R, ContinuousLinearMap.smulRight_apply]
    have hh := congrArg A (b.sum_repr x)
    simpa only [map_sum, map_smul] using! hh
  have hn : IsNuclearOperator (∑ i, R i) := (nuclearEndomorphisms H).sum_mem (fun i _ ↦ hR i)
  have hA : IsNuclearOperator A := he ▸ hn
  obtain ⟨tr,htr⟩ := hilbertTrace_linear (H := H)
  have hs : (⟨A,hA⟩ : nuclearEndomorphisms H) = ∑ i, ⟨R i,hR i⟩ := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using! he.symm
  refine ⟨hA, ?_⟩
  rw [← htr, hs, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [htr]
  exact hilbertTrace_smulRight (φ i) (A (b i))


/-- The finite-dimensional trace is bounded by dimension times operator norm. -/
theorem norm_hilbertTrace_le_finrank_mul_opNorm [FiniteDimensional ℂ H]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) :
    ‖hilbertTrace ⟨A,hA⟩‖ ≤ (Module.finrank ℂ H : ℝ) * ‖A‖ := by
  classical
  let b := stdOrthonormalBasis ℂ H
  obtain ⟨hn,ht⟩ := nuclear_trace_finiteBasis b.toBasis A
  rw [ht]
  calc
    _ ≤ ∑ i, ‖b.toBasis.repr (A (b i)) i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (Module.finrank ℂ H), ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [b.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      exact (norm_inner_le_norm _ _).trans (by
        rw [b.orthonormal.norm_eq_one i, one_mul]
        exact (A.le_opNorm (b i)).trans_eq (by rw [b.orthonormal.norm_eq_one i, mul_one]))
    _ = _ := by simp

/-- The algebraic trace of a finite quotient constrains every nuclear
approximant in the original operator norm, without a coordinate conditioning factor. -/
theorem finite_quotient_trace_le_nuclear_approximation (m : ℕ)
    (L : H →L[ℂ] (Fin m → ℂ)) (hL : Surjective L)
    (A F : H →L[ℂ] H) (hF : IsNuclearOperator F)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hAB : ∀ x, L (A x) = B (L x)) :
    ‖∑ i : Fin m, B (Pi.single i 1) i‖ ≤ traceNorm ⟨F,hF⟩ + (m : ℝ) * ‖A - F‖ := by
  classical
  let K : ClosedSubmodule ℂ H := ⟨L.ker, L.isClosed_ker⟩
  let : IsClosed (K.toSubmodule : Set H) := K.isClosed
  let Q := H ⧸ K.toSubmodule
  let q : H →L[ℂ] Q := K.toSubmodule.mkQL
  let J : Q →ₗᵢ[ℂ] H := quotientOrthogonalSection K
  let e : Q ≃ₗ[ℂ] (Fin m → ℂ) := L.toLinearMap.quotKerEquivOfSurjective hL
  let b : Basis (Fin m) ℂ Q := Basis.ofEquivFun e
  let AQ : Q →L[ℂ] Q := q.comp (A.comp J.toContinuousLinearMap)
  have heq (x : H) : e (q x) = L x :=
    LinearMap.quotKerEquivOfSurjective_apply_mk L.toLinearMap hL x
  have hqJ (x : Q) : q (J x) = x := quotientOrthogonalSection_rightInverse K x
  have hEA (x : Q) : e (AQ x) = B (e x) := by
    change e (q (A (J x))) = B (e x)
    rw [heq, hAB, ← heq, hqJ]
  obtain ⟨hn,htrace⟩ := nuclear_trace_finiteBasis b AQ
  have htrace' : hilbertTrace ⟨AQ,hn⟩ = ∑ i : Fin m, B (Pi.single i 1) i := by
    rw [htrace]
    apply Finset.sum_congr rfl
    intro i _
    rw [show b = Basis.ofEquivFun e from rfl, Basis.ofEquivFun_repr_apply, hEA]
    simp only [Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  have hqnorm : ‖q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    exact (Submodule.Quotient.norm_mk_le K.toSubmodule x).trans_eq (one_mul _).symm
  have hprod : ‖q‖ * ‖J.toContinuousLinearMap‖ ≤ 1 :=
    (mul_le_mul hqnorm J.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  let : FiniteDimensional ℂ Q := b.finiteDimensional_of_finite
  have hdim : Module.finrank ℂ Q = m := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  let FQ := q.comp (F.comp J.toContinuousLinearMap)
  obtain ⟨hFQ,hb⟩ := traceNorm_sandwich_le F hF J.toContinuousLinearMap q
  have hFQbound : ‖hilbertTrace ⟨FQ,hFQ⟩‖ ≤ traceNorm ⟨F,hF⟩ := by
    apply (norm_hilbertTrace_le _).trans (hb.trans _)
    exact (mul_le_mul_of_nonneg_right hprod
      ((norm_nonneg (hilbertTrace ⟨F,hF⟩)).trans (norm_hilbertTrace_le _))).trans_eq (one_mul _)
  obtain ⟨hE,_⟩ := nuclear_trace_finiteBasis b (AQ - FQ)
  have hEQ : AQ - FQ = q.comp ((A-F).comp J.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [AQ, FQ, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  have hEnorm : ‖AQ - FQ‖ ≤ ‖A-F‖ := by
    rw [hEQ]
    calc
      _ ≤ ‖q‖ * (‖A-F‖ * ‖J.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ = (‖q‖ * ‖J.toContinuousLinearMap‖) * ‖A-F‖ := by ring
      _ ≤ 1 * ‖A-F‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = _ := one_mul _
  have hEbound : ‖hilbertTrace ⟨AQ-FQ,hE⟩‖ ≤ (m : ℝ) * ‖A-F‖ := by
    apply (norm_hilbertTrace_le_finrank_mul_opNorm (AQ-FQ) hE).trans
    rw [hdim]
    exact mul_le_mul_of_nonneg_left hEnorm (Nat.cast_nonneg _)
  obtain ⟨tr,htr⟩ := hilbertTrace_linear (H := Q)
  have he : (⟨AQ,hn⟩ : nuclearEndomorphisms Q) = ⟨FQ,hFQ⟩ + ⟨AQ-FQ,hE⟩ := by
    apply Subtype.ext
    change AQ = FQ + (AQ-FQ)
    abel
  have ht : hilbertTrace ⟨AQ,hn⟩ = hilbertTrace ⟨FQ,hFQ⟩ + hilbertTrace ⟨AQ-FQ,hE⟩ := by
    rw [← htr, he, map_add, htr, htr]
  have hnorm := (norm_add_le (hilbertTrace ⟨FQ,hFQ⟩) (hilbertTrace ⟨AQ-FQ,hE⟩)).trans
    (add_le_add hFQbound hEbound)
  rw [← ht, htrace'] at hnorm
  exact hnorm


/-- A finite quotient with a constant diagonal constrains every nuclear
approximant to the original operator. The error is measured in operator norm;
the quotient coordinates may be nonorthogonal. -/
theorem finite_quotient_diagonal_le_nuclear_approximation (m : ℕ)
    (L : H →L[ℂ] (Fin m → ℂ)) (hL : Surjective L)
    (A F : H →L[ℂ] H) (hF : IsNuclearOperator F)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hAB : ∀ x, L (A x) = B (L x)) (c : ℂ)
    (hdiag : ∀ i : Fin m, B (Pi.single i 1) i = c) :
    (m : ℝ) * ‖c‖ ≤ traceNorm ⟨F,hF⟩ + (m : ℝ) * ‖A - F‖ := by
  simpa only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, norm_mul, Complex.norm_natCast] using
    finite_quotient_trace_le_nuclear_approximation m L hL A F hF B hAB

/-- A finite quotient with a constant diagonal forces the corresponding linear
lower bound on the trace norm of the upstairs nuclear operator. The quotient
coordinates may be nonorthogonal; their norm does not enter the bound. -/
theorem traceNorm_ge_finite_quotient_diagonal (m : ℕ)
    (L : H →L[ℂ] (Fin m → ℂ)) (hL : Surjective L)
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hAB : ∀ x, L (A x) = B (L x)) (c : ℂ)
    (hdiag : ∀ i : Fin m, B (Pi.single i 1) i = c) :
    (m : ℝ) * ‖c‖ ≤ traceNorm ⟨A,hA⟩ := by
  simpa only [sub_self, norm_zero, mul_zero, add_zero] using
    finite_quotient_diagonal_le_nuclear_approximation m L hL A A hA B hAB c hdiag

end RiemannMasullo
