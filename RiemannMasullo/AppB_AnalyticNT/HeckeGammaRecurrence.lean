module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic

/-! The two-step gamma quotient for the actual archimedean factor of a unitary Hecke
character. The real and complex local factors use Mathlib's Deligne recurrences. -/

public noncomputable section

open Classical Complex Set Filter Function NumberField Polynomial Topology
open scoped Polynomial
namespace RiemannMasullo.HeckeDivisorRigidity

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)

private def affineShift (b : ℂ) : ℂ[X] :=
  C (1 / 2 / (Real.pi : ℂ)) * (X + C b)

/-- Each real place contributes one affine gamma factor to the two-step
quotient. Each complex place contributes two with consecutive shifts. -/
private def gammaShiftPolynomial (χ : U) : ℂ[X] :=
  ∏ v : InfinitePlace K, if hv : v.IsReal then
    let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    affineShift (a.1 + (a.2.val : ℂ))
  else
    let a := (complexHeckeCharacter_parameters χ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    let b := a.1 + (a.2.natAbs : ℂ)/2
    affineShift b * affineShift (b+1)

private theorem real_gamma_shift (z b : ℂ) (h : 0 < (z+b).re) :
    Complex.Gammaℝ (z+2+b) = Complex.Gammaℝ (z+b) * (affineShift b).eval z := by
  have hn : z+b ≠ 0 := fun he ↦ by simp [he] at h
  rw [show z+2+b = (z+b)+2 by ring, Complex.Gammaℝ_add_two hn]
  simp only [affineShift, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X]
  ring

private theorem complex_gamma_shift (z b : ℂ) (h : 0 < (z+b).re) :
    Complex.Gammaℂ (z+2+b) / 2 = (Complex.Gammaℂ (z+b) / 2) *
      (affineShift b * affineShift (b+1)).eval z := by
  have hn : z+b ≠ 0 := fun he ↦ by simp [he] at h
  have h1 : 0 < (z+b+1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hn1 : z+b+1 ≠ 0 := fun he ↦ by simp [he] at h1
  rw [show z+2+b = ((z+b)+1)+1 by ring, Complex.Gammaℂ_add_one hn1,
    Complex.Gammaℂ_add_one hn]
  simp only [affineShift, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X]
  ring

/-- The true archimedean Hecke factor has this polynomial as its two-step quotient
throughout the positive half-plane, with the project's normalization at complex places. -/
private theorem heckeGammaFactor_add_two (χ : U) {z : ℂ} (hz : 0 < z.re) :
    heckeGammaFactor χ (z+2) = heckeGammaFactor χ z * (gammaShiftPolynomial χ).eval z := by
  classical
  unfold heckeGammaFactor gammaShiftPolynomial
  rw [Polynomial.eval_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v.IsReal
  · simp only [dite_eq_left hv]
    let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    have ha : a.1.re = 0 := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    have h : 0 < (z+(a.1+(a.2.val : ℂ))).re := by
      simp only [Complex.add_re, Complex.natCast_re, ha, zero_add]
      linarith [Nat.cast_nonneg (α := ℝ) a.2.val]
    simpa only [add_assoc, a] using real_gamma_shift z (a.1+(a.2.val : ℂ)) h
  · simp only [dite_eq_right hv]
    let hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let a := (complexHeckeCharacter_parameters χ v hw).exists.choose
    have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ v hw).exists.choose_spec.1
    have h : 0 < (z+(a.1+(a.2.natAbs : ℂ)/2)).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, zero_add]
      positivity
    simpa only [add_assoc, a, hw] using complex_gamma_shift z (a.1+(a.2.natAbs : ℂ)/2) h

/-- The shift quotient has no zero in the positive half-plane. -/
private theorem gammaShiftPolynomial_eval_ne_zero (χ : U) {z : ℂ} (hz : 0 < z.re) :
    (gammaShiftPolynomial χ).eval z ≠ 0 := by
  intro h
  have hshift : 0 < (z+2).re := by simp only [Complex.add_re, Complex.re_ofNat]; linarith
  exact heckeGammaFactor_ne_zero_of_re_pos χ hshift (by rw [heckeGammaFactor_add_two χ hz, h, mul_zero])

private theorem gammaShiftPolynomial_ne_zero (χ : U) : gammaShiftPolynomial χ ≠ 0 := by
  intro h
  exact gammaShiftPolynomial_eval_ne_zero χ (z := 1) (by simp) (by simp [h])

/-- The archimedean Hecke factor of any unitary character has a nonzero polynomial
two-step quotient on the open positive half-plane. This uses the real and complex local
gamma recurrences with the normalization of the project's completed Hecke function. -/
theorem exists_gamma_shift_polynomial (χ : U) :
    ∃ p : ℂ[X], p ≠ 0 ∧ ∀ z : ℂ, 0 < z.re →
      heckeGammaFactor χ (z+2) = heckeGammaFactor χ z * p.eval z :=
  ⟨gammaShiftPolynomial χ, gammaShiftPolynomial_ne_zero χ, fun _ hz ↦ heckeGammaFactor_add_two χ hz⟩

end RiemannMasullo.HeckeDivisorRigidity
