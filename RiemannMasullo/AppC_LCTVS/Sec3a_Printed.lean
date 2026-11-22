module

public import RiemannMasullo.AppC_LCTVS.Sec3a

/-! # Appendix C.3.4: the printed trace-class equalities -/

@[expose] public noncomputable section

namespace RiemannMasullo

open scoped InnerProductSpace

/-- Paper: Lemma C.3.4.1(2), p. 697. As printed: for a trace-class operator on a
complex Hilbert space the sum of the absolute values of its diagonal entries is
independent of the orthonormal basis. `tsum_hilbertDiagonal_eq` gives the independence
of the sum of the entries themselves, as in part (3). See ERRATA F8. -/
def Printed.tsum_norm_hilbertDiagonal_eq : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsNuclearOperator T →
    ∀ (ι κ : Type) (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H),
      (∑' i, ‖⟪b i, T (b i)⟫_ℂ‖) = ∑' j, ‖⟪c j, T (c j)⟫_ℂ‖

/-- Paper: Lemma C.3.4.1(2), p. 697. On ℂ² let `T = diag(1, -1)`. The coordinate
basis has absolute diagonal sum two. In the basis `(e₁ + e₂)/√2`, `(e₁ - e₂)/√2`,
the operator interchanges the basis vectors and the diagonal sum is zero. -/
theorem Printed.tsum_norm_hilbertDiagonal_eq_false : ¬ Printed.tsum_norm_hilbertDiagonal_eq := by sorry

/-- Paper: Lemma C.3.4.4(2), equality in (C.3.4.3), p. 698. As printed: for any
trace-class T and bounded A, the products AT and TA have equal trace norms. The two
upper bounds are `traceNorm_mul_left_le` and `traceNorm_mul_right_le`. See ERRATA F9. -/
def Printed.traceNorm_mul_eq : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (A : H →L[ℂ] H),
    traceNorm ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩ =
      traceNorm ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩

/-- Paper: Lemma C.3.4.4(2), equality in (C.3.4.3), p. 698. On ℂ² let A be the
projection onto e₁ and take `T e₁ = e₂`, `T e₂ = 0`. Then AT is zero, while TA is T,
whose only nonzero singular value is one. -/
theorem Printed.traceNorm_mul_eq_false : ¬ Printed.traceNorm_mul_eq := by sorry

end RiemannMasullo
