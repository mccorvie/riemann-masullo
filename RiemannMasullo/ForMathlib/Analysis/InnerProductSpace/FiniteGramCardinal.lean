module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Normed.Operator.Basic

/-! Cardinal vectors of finite independent Hilbert families and their images under bounded maps. -/

@[expose] public noncomputable section

open scoped InnerProductSpace Matrix

namespace RiemannMasullo.WeakCardinal

variable {ι H K : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The column of the inverse evaluation Gram gives the finite cardinal in the original space. -/
def finiteGramCardinal (u : ι → H) (w : ι) : H :=
  ∑ i, (Matrix.gram ℂ u)⁻¹ i w • u i

/-- The interpolated values are Kronecker data at every site of the independent family. -/
theorem inner_finiteGramCardinal (u : ι → H) (hu : LinearIndependent ℂ u) (i w : ι) :
    ⟪u i, finiteGramCardinal u w⟫_ℂ = if i = w then 1 else 0 := by
  have hdet := isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hu)
  have h := congrArg (fun M : Matrix ι ι ℂ ↦ M i w) ((Matrix.gram ℂ u).mul_nonsing_inv hdet)
  simpa only [finiteGramCardinal, inner_sum, inner_smul_right, Matrix.mul_apply, Matrix.gram_apply,
    Matrix.one_apply, mul_comm] using h

/-- Applying a bounded map changes the Gram in the quadratic form and retains the
inverse column of the original Gram. -/
theorem norm_sq_map_finiteGramCardinal (A : H →L[ℂ] K) (u : ι → H) (w : ι) :
    let c (i : ι) := (Matrix.gram ℂ u)⁻¹ i w
    ‖A (finiteGramCardinal u w)‖^2 = (star c ⬝ᵥ (Matrix.gram ℂ (A ∘ u)) *ᵥ c).re := by
  let c (i : ι) := (Matrix.gram ℂ u)⁻¹ i w
  change ‖A (∑ i, c i • u i)‖ ^ 2 = _
  rw [map_sum, Matrix.star_dotProduct_gram_mulVec]
  simp only [map_smul, Function.comp_apply]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

end RiemannMasullo.WeakCardinal
