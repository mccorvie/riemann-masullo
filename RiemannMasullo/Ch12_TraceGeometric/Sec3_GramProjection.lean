module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.LinearAlgebra.Trace

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

end RiemannMasullo
