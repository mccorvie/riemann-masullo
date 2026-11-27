module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.AngularGram
import Mathlib.Tactic

/-! Scaling both angular Gram matrices by a common Haar factor scales their inverse-column weak
energy by the reciprocal factor. -/

@[expose] public noncomputable section
open scoped Matrix
open Complex

namespace RiemannMasullo.WeakCardinal

theorem weakForm_haarScale {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℂ) (c : ι → ℂ) (a : ℝ) (ha : 0 < a) :
    (star ((a:ℂ)⁻¹ • c) ⬝ᵥ (((a:ℂ) • B) *ᵥ ((a:ℂ)⁻¹ • c))).re =
      a⁻¹ * (star c ⬝ᵥ B *ᵥ c).re := by
  rw [Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne'),one_smul]
  have hstar : star ((a:ℂ)⁻¹ • c) = (a:ℂ)⁻¹ • star c := by
    funext i
    change star ((a:ℂ)⁻¹*c i) = (a:ℂ)⁻¹*star (c i)
    simp [star_mul']
  rw [hstar,smul_dotProduct,smul_eq_mul,← Complex.ofReal_inv,Complex.re_ofReal_mul]

end RiemannMasullo.WeakCardinal
