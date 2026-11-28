module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.InnerProductSpace.Trace

/-! # Gram correction for finite theta comparisons -/

public noncomputable section

open Module
open scoped InnerProductSpace

namespace RiemannMasullo

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A right inverse of the Gram operator gives the orthogonal projection onto the range
of the column map. -/
theorem starProjection_range_eq_comp_gramInverse (X : E →L[ℂ] H)
    [X.toLinearMap.range.HasOrthogonalProjection] (Ginv : E →L[ℂ] E)
    (hG : (X.adjoint.comp X).comp Ginv = ContinuousLinearMap.id ℂ E) :
    X.toLinearMap.range.starProjection = X.comp (Ginv.comp X.adjoint) := by
  ext x
  change X.toLinearMap.range.starProjection x = X (Ginv (X.adjoint x))
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨_, rfl⟩ ?_
  rintro _ ⟨y, rfl⟩
  change ⟪x - X (Ginv (X.adjoint x)), X y⟫_ℂ = 0
  rw [← X.adjoint_inner_left, map_sub]
  have hx := DFunLike.congr_fun hG (X.adjoint x)
  change X.adjoint (X (Ginv (X.adjoint x))) = X.adjoint x at hx
  rw [hx, sub_self, inner_zero_left]

/-- Independent columns with a finite-dimensional coefficient space admit a Gram inverse. -/
theorem exists_gramInverse [FiniteDimensional ℂ E] (X : E →L[ℂ] H)
    (hX : Function.Injective X) :
    ∃ Ginv : E →L[ℂ] E, (X.adjoint.comp X).comp Ginv = ContinuousLinearMap.id ℂ E := by
  let G := X.adjoint.comp X
  have hG : Function.Injective G.toLinearMap := X.adjoint_comp_self_injective_iff.mpr hX
  let e := (LinearEquiv.ofInjectiveEndo G.toLinearMap hG).toContinuousLinearEquiv
  exact ⟨e.symm.toContinuousLinearMap, ContinuousLinearMap.ext e.apply_symm_apply⟩

/-- The trace of a finite range projection between two bounded operators is the trace
on the coefficient space with its inverse Gram correction. This applies to the finite
theta projections in a comparison of the cut-off diagonal in §12.3. -/
theorem hilbertTrace_comp_gramProjection_comp {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ E) (X : E →L[ℂ] H) [X.toLinearMap.range.HasOrthogonalProjection]
    (Ginv : E →L[ℂ] E) (hG : (X.adjoint.comp X).comp Ginv = ContinuousLinearMap.id ℂ E)
    (A B : H →L[ℂ] H) :
    ∃ hN : IsNuclearOperator (A.comp (X.toLinearMap.range.starProjection.comp B)),
      hilbertTrace ⟨_, hN⟩ =
        LinearMap.trace ℂ E
          (Ginv.comp (X.adjoint.comp (B.comp (A.comp X)))).toLinearMap := by
  classical
  let : FiniteDimensional ℂ E := b.finiteDimensional_of_finite
  let row (i : ι) : H →L[ℂ] ℂ :=
    (b.coord i).toContinuousLinearMap.comp (Ginv.comp (X.adjoint.comp B))
  let col (i : ι) : H := A (X (b i))
  let term (i : ι) : nuclearEndomorphisms H :=
    ⟨(row i).smulRight (col i), smulRight_mem_nuclearEndomorphisms (row i) (col i)⟩
  have hsum :
      (∑ i, term i).val = A.comp (X.toLinearMap.range.starProjection.comp B) := by
    rw [starProjection_range_eq_comp_gramInverse X Ginv hG]
    ext x
    simp only [Submodule.coe_sum, sum_apply, term,
      ContinuousLinearMap.smulRight_apply, row, col, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
    simp only [← map_smul A, ← map_smul X, ← map_sum A, ← map_sum X, b.sum_repr]
  have hN : IsNuclearOperator (A.comp (X.toLinearMap.range.starProjection.comp B)) :=
    hsum ▸ (∑ i, term i).property
  refine ⟨hN, ?_⟩
  have he : (⟨_, hN⟩ : nuclearEndomorphisms H) = ∑ i, term i := Subtype.ext hsum.symm
  rw [he]
  obtain ⟨trace, htrace⟩ := hilbertTrace_linear (H := H)
  rw [← htrace, map_sum]
  simp_rw [htrace, term, hilbertTrace_smulRight]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp [row, col, LinearMap.toMatrix_apply]

/-- Paper: §12.3, p. 514 and (12.5.1.4), p. 520. In an orthonormal basis of the
finite column space, the trace captured by an observation is the sum of the
squared norms of the observed basis vectors.
Deviation: this finite projection identity supports the comparison of the global diagonal. -/
theorem hilbertTrace_comp_finiteProjection_comp_adjoint {ι : Type*} [Fintype ι]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (b : OrthonormalBasis ι ℂ S)
    (A : H →L[ℂ] H) :
    ∃ hN : IsNuclearOperator (A.comp (S.starProjection.comp A.adjoint)),
      hilbertTrace ⟨_, hN⟩ = ∑ i, ((‖A (b i : H)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  let : FiniteDimensional ℂ S := b.toBasis.finiteDimensional_of_finite
  let : CompleteSpace S := FiniteDimensional.completeSpace ℂ S
  have hRange : S.subtypeL.toLinearMap.range = S := S.range_subtype
  let : S.subtypeL.toLinearMap.range.HasOrthogonalProjection :=
    hRange.symm ▸ inferInstanceAs S.HasOrthogonalProjection
  have hGram : (S.subtypeL.adjoint.comp S.subtypeL).comp (ContinuousLinearMap.id ℂ S) =
      ContinuousLinearMap.id ℂ S := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      S.adjoint_subtypeL, Submodule.subtypeL_apply] using
      S.orthogonalProjectionOnto_mem_subspace_eq_self x
  obtain ⟨hN, hTrace⟩ := hilbertTrace_comp_gramProjection_comp b.toBasis S.subtypeL
    (ContinuousLinearMap.id ℂ S) hGram A A.adjoint
  have hProjection : S.subtypeL.toLinearMap.range.starProjection = S.starProjection := by
    rw [starProjection_range_eq_comp_gramInverse S.subtypeL _ hGram, S.adjoint_subtypeL]
    rfl
  have hMap := congrArg (fun P : H →L[ℂ] H ↦ A.comp (P.comp A.adjoint)) hProjection
  have hN' : IsNuclearOperator (A.comp (S.starProjection.comp A.adjoint)) := hMap ▸ hN
  have hSame : (⟨_, hN'⟩ : nuclearEndomorphisms H) = ⟨_, hN⟩ := Subtype.ext hMap.symm
  refine ⟨hN', ?_⟩
  rw [hSame, hTrace, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪b i, S.subtypeL.adjoint (A.adjoint (A (S.subtypeL (b i))))⟫_ℂ = _
  rw [S.subtypeL.adjoint_inner_right, A.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_pow]
  rfl

/-- Paper: §12.3, p. 514. A single unit vector in a finite column space gives a lower
bound on the captured trace. The observation need only be evaluated on that vector.
Deviation: this is a sufficient test for a finite projection in the comparison. -/
theorem norm_sq_le_hilbertTrace_comp_finiteProjection_comp_adjoint
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] [FiniteDimensional ℂ S]
    (v : S) (hv : ‖v‖ = 1) (A : H →L[ℂ] H) :
    ∃ hN : IsNuclearOperator (A.comp (S.starProjection.comp A.adjoint)),
      ‖A (v : H)‖ ^ 2 ≤ (hilbertTrace ⟨_, hN⟩).re := by
  classical
  have hOrthonormal : Orthonormal ℂ ((↑) : ({v} : Set S) → S) := by
    rw [orthonormal_subsingleton_iff]
    intro x
    have hx : (x : S) = v := x.property
    rw [hx, hv]
  obtain ⟨u, b, hu, hb⟩ := hOrthonormal.exists_orthonormalBasis_extension
  let i : u := ⟨v, hu (Set.mem_singleton v)⟩
  obtain ⟨hN, hTrace⟩ := hilbertTrace_comp_finiteProjection_comp_adjoint S b A
  refine ⟨hN, ?_⟩
  rw [hTrace, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hi : b i = v := congrFun hb i
  rw [← hi]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖A (b j : H)‖) (Finset.mem_univ i)

end RiemannMasullo
