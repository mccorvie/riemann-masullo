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
theorem Printed.tsum_norm_hilbertDiagonal_eq_false : ¬ Printed.tsum_norm_hilbertDiagonal_eq := by
  intro h
  let e₀ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1
  let e₁ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1
  let T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    (innerSL ℂ e₀).smulRight e₁
  have hdiag : ∀ x : EuclideanSpace ℂ (Fin 2),
      ‖⟪x, T x⟫_ℂ‖ = ‖x 0‖ * ‖x 1‖ := by
    intro x
    simp only [T, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right, e₀,
      e₁, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
    simp
  let v : Fin 2 → EuclideanSpace ℂ (Fin 2) :=
    ![WithLp.toLp 2 ![3 / 5, 4 / 5], WithLp.toLp 2 ![4 / 5, -3 / 5]]
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [v, PiLp.inner_apply, Fin.sum_univ_two] <;> simp [map_ofNat] <;> ring
  have hcard : Fintype.card (Fin 2) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) := by simp
  let c : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
    ((basisOfOrthonormalOfCardEqFinrank hv hcard).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hv)).toHilbertBasis
  have hc : ∀ j, c j = v j := by
    intro j
    rw [OrthonormalBasis.coe_toHilbertBasis, Module.Basis.coe_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
  let b : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
    (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis
  have hb : ∀ i, b i = EuclideanSpace.single i 1 := by
    intro i
    rw [OrthonormalBasis.coe_toHilbertBasis, EuclideanSpace.basisFun_apply]
  have h1 := h (EuclideanSpace ℂ (Fin 2)) T (smulRight_mem_nuclearEndomorphisms _ _)
    (Fin 2) (Fin 2) b c
  simp only [tsum_fintype, Fin.sum_univ_two, hdiag, hb, hc] at h1
  simp [v] at h1
  norm_num at h1

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
theorem Printed.traceNorm_mul_eq_false : ¬ Printed.traceNorm_mul_eq := by
  intro h
  let H := EuclideanSpace ℂ (Fin 2)
  let e₀ : H := EuclideanSpace.single 0 1
  let e₁ : H := EuclideanSpace.single 1 1
  have ho := orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2))
  have h01 : ⟪e₀, e₁⟫_ℂ = 0 := by simpa using ho 0 1
  have hn0 : ‖e₀‖ = 1 := (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)).1 0
  have hn1 : ‖e₁‖ = 1 := (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)).1 1
  have h00 : ⟪e₀, e₀⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hn0]; simp
  let T : nuclearEndomorphisms H :=
    ⟨(innerSL ℂ e₀).smulRight e₁, smulRight_mem_nuclearEndomorphisms _ _⟩
  let A : H →L[ℂ] H := (innerSL ℂ e₀).smulRight e₀
  have hAT : A * T.val = 0 := by
    ext1 x; simp only [A, T, mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, h01, mul_zero, zero_smul, zero_apply]
  have hTA : T.val * A = T.val := by
    ext1 x; simp only [A, T, mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, h00, mul_one]
  have h1 := h H T A
  have hzero : traceNorm (⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩ :
      nuclearEndomorphisms H) = 0 := by
    have hsub : (⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩ :
        nuclearEndomorphisms H) =
        ⟨(0 : H →L[ℂ] ℂ).smulRight e₁, smulRight_mem_nuclearEndomorphisms _ _⟩ :=
      Subtype.ext (hAT.trans (by ext1 x; simp))
    rw [hsub, traceNorm_smulRight, norm_zero, zero_mul]
  have hone : traceNorm (⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩ :
      nuclearEndomorphisms H) = 1 := by
    have hsub : (⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩ :
        nuclearEndomorphisms H) =
        ⟨(innerSL ℂ e₀).smulRight e₁, smulRight_mem_nuclearEndomorphisms _ _⟩ :=
      Subtype.ext hTA
    rw [hsub, traceNorm_smulRight, innerSL_apply_norm, hn0, hn1, mul_one]
  rw [hzero, hone] at h1
  exact zero_ne_one h1

end RiemannMasullo
