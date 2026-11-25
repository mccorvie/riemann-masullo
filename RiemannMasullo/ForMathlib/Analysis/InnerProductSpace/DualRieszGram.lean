module

public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-! Evaluation rows after a linear isometry from the dual into a Hilbert space. -/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace RiemannMasullo.WeakCardinal

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A conjugate-linear Hilbert isometry preserves the real part of the inner product. -/
private theorem real_inner_semiIso (A : H →ₗᵢ⋆[ℂ] V) (x y : H) :
    (inner ℂ (A x) (A y)).re = (inner ℂ x y).re := by
  calc
    _ = (‖A x + A y‖ * ‖A x + A y‖ - ‖A x‖ * ‖A x‖ - ‖A y‖ * ‖A y‖) / 2 :=
      re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) _ _
    _ = _ := by
      rw [← map_add, A.norm_map, A.norm_map, A.norm_map]
      exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) x y).symm

/-- Under any linear isometric realization of the dual, the Gram of the Riesz
representatives is the transpose of the Gram of the realized functionals. -/
theorem riesz_inner_eq_realization (T : StrongDual ℂ H →ₗᵢ[ℂ] V) (f g : StrongDual ℂ H) :
    f ((InnerProductSpace.toDual ℂ H).symm g) = inner ℂ (T g) (T f) := by
  let R := InnerProductSpace.toDual ℂ H
  let A : H →ₗᵢ⋆[ℂ] V := T.comp R.toLinearIsometry
  have h (x y : H) : inner ℂ (A x) (A y) = star (inner ℂ x y) := by
    apply Complex.ext
    · simpa only [Complex.star_def, Complex.conj_re] using real_inner_semiIso A x y
    · have hi := real_inner_semiIso A x (Complex.I • y)
      have hA : A (Complex.I • y) = (-Complex.I) • A y := by
        rw [map_smulₛₗ, starRingEnd_apply, Complex.star_def, Complex.conj_I]
      rw [hA, inner_smul_right, inner_smul_right, neg_mul, Complex.neg_re,
        Complex.I_mul_re, Complex.I_mul_re, neg_neg] at hi
      simpa only [Complex.star_def, Complex.conj_im] using hi
  have he := h (R.symm g) (R.symm f)
  change inner ℂ (T (R (R.symm g))) (T (R (R.symm f))) = _ at he
  rw [R.apply_symm_apply, R.apply_symm_apply] at he
  rw [he, Complex.star_def, inner_conj_symm]
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (y := f) (x := R.symm g)).symm

end RiemannMasullo.WeakCardinal
