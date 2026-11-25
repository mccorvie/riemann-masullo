module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppB_AnalyticNT.Sec1
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Deligne
import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Multipliers of Hecke L-functions with bounds that are uniform in the character

The cluster route to Theorem 10.3.2.1 (`Sec3_Clusters`) sums over all angular components at
once, so it needs estimates of the classical kind with constants that do not depend on the
character. This file proves them, not for the L-function itself but for an entire multiple of
it, the multiplier `ϑ` below. The size of a unitary character `χ` of the idele
classes is measured by the library's own quantities: `heckeLogDiscriminantConductor χ` for the
finite part, and a bound `X` for the parameters of `realHeckeCharacter_parameters` and
`complexHeckeCharacter_parameters` (the radial exponents and the angular weights) for the
archimedean part.

The estimates are stated for one entire function, the multiplier
`ϑ(s) = Λ(s, χ) Λ(s, χ⁻¹) / (γ(s + 2K, χ) γ(s + 2K, χ⁻¹))`, where `Λ` is the completed Hecke
L-function and `γ` its gamma factor.

* The product over `χ` and `χ⁻¹` satisfies a functional equation with no root number, so no
  bound for the unknown constant of `completedHeckeL_functionalEquation_conductorScale` is
  needed. This is the device of the private lemma
  `idelicExplicitFormula_summable_spectral_characters_discs` of `AppB_AnalyticNT/Sec4b`.
* Dividing by the gamma factors shifted by `2K` makes `ϑ` bounded on the strip
  `-K + 1/2 ≤ Re s ≤ R`, by a constant that depends only on the field, on `K`, on `R` and on a
  bound for the conductor. On the line `Re s = -K + 1/2` the gamma factors cancel exactly in
  norm; no Stirling estimate is used.
* `ϑ` has no zero on the lines `Re s = -k - 1/2`, `k < K`, and to the right of `3/2`, where it
  is bounded below by an inverse power of `‖s‖ + X`. `ϑ` does vanish at the poles of the shifted
  gamma factors, but none of them lies on these lines; so the trivial zeros of the finite
  L-function on half-integer lines (complex places with odd angular weight) do no harm.
* `ϑ` vanishes at each zero of `Λ(·, χ)` to at least its multiplicity.

The uniform statements are for characters that are not trivial on the norm-one idele classes.
In the application they are the values `χ ω`, `ω ≠ 1`, of a basepoint choice that is trivial on
the image of a norm section. The trivial character, whose completed L-function has poles at `0`
and `1`, has a multiplier of the same shape (`exists_trivial_heckeMultiplier`): the poles are
removed by normalizing the meromorphic product with `s (s - 1)`, and two more gamma shifts
absorb its growth.

Main statements: `exists_uniform_heckeMultiplier`, `exists_trivial_heckeMultiplier`, their
versions in the variable `u = s - a` (`…_strip_of_line`), and the zero counts
`continuedCompletedHeckeL_closedBall_zeros_le_log_uniform`,
`continuedCompletedHeckeL_one_closedBall_zeros_le_log`.

`Sec3_TraceClass` uses the versions in the variable `u = s - a` and the zero counts. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology ComplexConjugate

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "halfPlane" => Complex.re ⁻¹' Set.Ioi (1 : ℝ)

section GammaFactors

/-- The local archimedean gamma factor: `Γ_ℝ` at a real place and `Γ_ℂ / 2` at a complex
place. This decomposition of the gamma factor into a local factor and a shift follows the local
`G` and `c` in the proof of the private `archNuclearity_trace_gammaOrder` of
`Ch07_SchauderBasesZeta/Sec4`. -/
private def uniformLocalGamma (v : InfinitePlace F) (z : ℂ) : ℂ :=
  open Classical in if v.IsReal then Complex.Gammaℝ z else Complex.Gammaℂ z / 2

/-- The shift of the local gamma factor of a unitary character: the imaginary radial exponent
plus the sign parity at a real place, or plus half the absolute angular weight at a complex
place. -/
private def uniformGammaShift (χ : PontryaginDual C𝔽) (v : InfinitePlace F) : ℂ :=
  open Classical in
  if hv : v.IsReal then
    (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
      ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
  else
    (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
      ((complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2

/-- The gamma factor is the product of the local factors at the shifted arguments. -/
private theorem heckeGammaFactor_eq_prod_uniformLocalGamma (χ : PontryaginDual C𝔽) (s : ℂ) :
    heckeGammaFactor χ s =
      ∏ v : InfinitePlace F, uniformLocalGamma v (s + uniformGammaShift χ v) := by
  classical
  unfold heckeGammaFactor
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  by_cases hv : v.IsReal
  · simp only [uniformLocalGamma, uniformGammaShift, dite_eq_left hv, ite_eq_left hv, add_assoc]
  · simp only [uniformLocalGamma, uniformGammaShift, dite_eq_right hv, ite_eq_right hv, add_assoc]

/-- Taking the inverse character inverts its restriction to an archimedean completion. This is
the private `infinitePlaceRestriction_inv_twist_zero` of `AppB_AnalyticNT/Sec1` (also the
private `infinitePlaceRestriction_inverse` of `Ch03_IdelicZeta/Sec2`), copied because it is
private. -/
private theorem uniform_infinitePlaceRestriction_inv (χ : PontryaginDual C𝔽)
    (v : InfinitePlace F) (x : v.Completionˣ) :
    infinitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ 0) x =
      (infinitePlaceRestriction F v (ideleClassNormTwist χ 0) x)⁻¹ := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v x
  change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
  simp only [Complex.cpow_zero, mul_one]
  rfl

/-- Inversion negates the radial exponent at a real place and keeps the sign parity. This is
the private `realHeckeCharacter_parameters_inv` of `AppB_AnalyticNT/Sec1` (also the private
`realHecke_inverse_parameters` of `Ch03_IdelicZeta/Sec2`), copied because it is private. -/
private theorem uniform_realParameters_inv (χ : PontryaginDual C𝔽) (v : InfinitePlace F)
    (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(realHeckeCharacter_parameters χ v hv).exists.choose.1,
        (realHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (realHeckeCharacter_parameters χ⁻¹ v hv).unique
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [uniform_infinitePlaceRestriction_inv, ha.2 x, mul_inv, Complex.cpow_neg]
  congr 1
  rw [← inv_pow]
  split <;> simp

/-- Inversion negates the radial exponent and the angular weight at a complex place. This is
the private `complexHeckeCharacter_parameters_inv` of `AppB_AnalyticNT/Sec1` (also the private
`complexHecke_inverse_parameters` of `Ch03_IdelicZeta/Sec2`), copied because it is private. -/
private theorem uniform_complexParameters_inv (χ : PontryaginDual C𝔽) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(complexHeckeCharacter_parameters χ v hv).exists.choose.1,
        -(complexHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (complexHeckeCharacter_parameters χ⁻¹ v hv).unique
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [uniform_infinitePlaceRestriction_inv, ha.2 x, mul_inv, Complex.cpow_neg, zpow_neg]

/-- The gamma shifts of the inverse character are the complex conjugates. -/
private theorem uniformGammaShift_inv (χ : PontryaginDual C𝔽) (v : InfinitePlace F) :
    uniformGammaShift χ⁻¹ v = conj (uniformGammaShift χ v) := by
  classical
  have hconj {a : ℂ} (ha : a.re = 0) : conj a = -a := by
    apply Complex.ext <;> simp [ha]
  by_cases hv : v.IsReal
  · have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    simp only [uniformGammaShift, dite_eq_left hv, uniform_realParameters_inv, map_add,
      hconj ha, Complex.conj_natCast]
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have ha := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
    simp only [uniformGammaShift, dite_eq_right hv, uniform_complexParameters_inv, map_add,
      hconj ha, Int.natAbs_neg, map_div₀, Complex.conj_natCast, map_ofNat]

/-- The gamma shifts have nonnegative real part. -/
private theorem uniformGammaShift_re_nonneg (χ : PontryaginDual C𝔽) (v : InfinitePlace F) :
    0 ≤ (uniformGammaShift χ v).re := by
  classical
  by_cases hv : v.IsReal
  · have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    simp only [uniformGammaShift, dite_eq_left hv, Complex.add_re, ha, Complex.natCast_re,
      zero_add]
    positivity
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have ha := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
    simp only [uniformGammaShift, dite_eq_right hv, Complex.add_re, ha, zero_add,
      Complex.div_ofNat_re, Complex.natCast_re]
    positivity

open Classical in
/-- A bound for the archimedean parameters of a character bounds its gamma shifts. -/
private theorem norm_uniformGammaShift_le (χ : PontryaginDual C𝔽) {X : ℝ} (hX : 1 ≤ X)
    (harch : ∀ w : InfinitePlace F, if hw : w.IsReal then
        ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ X
      else
        let p := (complexHeckeCharacter_parameters χ w
          (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
        ‖p.1‖ ≤ X ∧ (p.2.natAbs : ℝ) ≤ X)
    (v : InfinitePlace F) : ‖uniformGammaShift χ v‖ ≤ 2 * X := by
  classical
  by_cases hv : v.IsReal
  · have h : ‖(realHeckeCharacter_parameters χ v hv).exists.choose.1‖ ≤ X := by
      simpa only [dite_eq_left hv] using harch v
    have hj : ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℝ) ≤ 1 := by
      exact_mod_cast Nat.le_of_lt_succ (realHeckeCharacter_parameters χ v hv).exists.choose.2.isLt
    simp only [uniformGammaShift, dite_eq_left hv]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_natCast]
    linarith
  · have h : ‖(complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1‖ ≤ X ∧
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℝ) ≤ X := by
      simpa only [dite_eq_right hv] using harch v
    simp only [uniformGammaShift, dite_eq_right hv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    linarith [h.1, h.2]

/-- Conjugating the argument conjugates the local gamma factor. -/
private theorem norm_uniformLocalGamma_conj (v : InfinitePlace F) (z : ℂ) :
    ‖uniformLocalGamma v (conj z)‖ = ‖uniformLocalGamma v z‖ := by
  classical
  unfold uniformLocalGamma
  split_ifs
  · rw [Complex.Gammaℝ_conj, Complex.norm_conj]
  · rw [Complex.Gammaℂ_conj, norm_div, norm_div, Complex.norm_conj]

/-- The polynomial that relates a local gamma factor to its shift by `2m`: `m` factors
`(z + 2j) / (2π)` at a real place and `2m` factors `(z + j) / (2π)` at a complex place. -/
private def uniformShiftPoly (v : InfinitePlace F) (m : ℕ) (z : ℂ) : ℂ :=
  open Classical in
  if v.IsReal then ∏ j ∈ Finset.range m, ((z + ((2 : ℝ) : ℂ) * j) / (2 * Real.pi))
  else ∏ j ∈ Finset.range (2 * m), ((z + ((1 : ℝ) : ℂ) * j) / (2 * Real.pi))

/-- The reciprocal of a local gamma factor is the reciprocal of its shift by `2m` times the
shift polynomial, at every point. -/
private theorem inv_uniformLocalGamma_eq (v : InfinitePlace F) (m : ℕ) (z : ℂ) :
    (uniformLocalGamma v z)⁻¹ =
      (uniformLocalGamma v (z + 2 * m))⁻¹ * uniformShiftPoly v m z := by
  classical
  unfold uniformLocalGamma uniformShiftPoly
  split_ifs
  · simpa only [Complex.ofReal_ofNat] using inv_Gammaℝ_eq_inv_Gammaℝ_add_mul_prod z m
  · have h := inv_Gammaℂ_eq_inv_Gammaℂ_add_mul_prod z (2 * m)
    simp only [Complex.ofReal_one, one_mul]
    rw [div_eq_mul_inv, mul_inv, h, div_eq_mul_inv, mul_inv]
    push_cast
    ring

/-- The shift polynomial is bounded by a power of the norm of its argument. -/
private theorem norm_uniformShiftPoly_le (v : InfinitePlace F) (m : ℕ) (z : ℂ) :
    ‖uniformShiftPoly v m z‖ ≤ (‖z‖ + 2 * m) ^ (2 * m) := by
  classical
  unfold uniformShiftPoly
  split_ifs
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have h1 : (1 : ℝ) ≤ ‖z‖ + 2 * m := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith [norm_nonneg z]
      exact (norm_prod_add_mul_div_two_pi_le z (by norm_num : (0 : ℝ) ≤ 2) m).trans
        (pow_le_pow_right₀ h1 (by omega))
  · have h := norm_prod_add_mul_div_two_pi_le z (by norm_num : (0 : ℝ) ≤ 1) (2 * m)
    simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using h

/-- To the right of the line `Re z = 1` the shift polynomial is bounded below by a constant. -/
private theorem le_norm_uniformShiftPoly (v : InfinitePlace F) (m : ℕ) {z : ℂ}
    (hz : 1 ≤ z.re) : (1 / (2 * Real.pi)) ^ (2 * m) ≤ ‖uniformShiftPoly v m z‖ := by
  classical
  have h0 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have h1 : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]
    linarith [Real.two_le_pi]
  unfold uniformShiftPoly
  split_ifs
  · exact (pow_le_pow_of_le_one h0 h1 (by omega)).trans
      (pow_le_norm_prod_add_mul_div_two_pi (by norm_num : (0 : ℝ) ≤ 2) zero_le_one hz m)
  · exact pow_le_norm_prod_add_mul_div_two_pi (by norm_num : (0 : ℝ) ≤ 1) zero_le_one hz (2 * m)

/-- At height at least one the shift polynomial is bounded below by a constant. -/
private theorem le_norm_uniformShiftPoly_of_im (v : InfinitePlace F) (m : ℕ) {z : ℂ}
    (hz : 1 ≤ |z.im|) : (1 / (2 * Real.pi)) ^ (2 * m) ≤ ‖uniformShiftPoly v m z‖ := by
  classical
  have h0 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have h1 : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]
    linarith [Real.two_le_pi]
  unfold uniformShiftPoly
  split_ifs
  · exact (pow_le_pow_of_le_one h0 h1 (by omega)).trans
      (pow_le_norm_prod_add_mul_div_two_pi_of_im (c := 2) zero_le_one hz m)
  · exact pow_le_norm_prod_add_mul_div_two_pi_of_im (c := 1) zero_le_one hz (2 * m)

/-- The product over the archimedean places of the shift polynomials of a character. -/
private def uniformShiftProd (χ : PontryaginDual C𝔽) (m : ℕ) (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace F, uniformShiftPoly v m (s + uniformGammaShift χ v)

/-- The reciprocal of the gamma factor is the reciprocal of its shift by `2m` times the product
of the shift polynomials, at every point. -/
private theorem inv_heckeGammaFactor_eq (χ : PontryaginDual C𝔽) (m : ℕ) (s : ℂ) :
    (heckeGammaFactor χ s)⁻¹ = (heckeGammaFactor χ (s + 2 * m))⁻¹ * uniformShiftProd χ m s := by
  rw [heckeGammaFactor_eq_prod_uniformLocalGamma, heckeGammaFactor_eq_prod_uniformLocalGamma,
    ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, uniformShiftProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [inv_uniformLocalGamma_eq v m, add_right_comm]

/-- On the right half-plane the quotient of the gamma factor by its shift is the reciprocal of
the product of the shift polynomials. -/
private theorem heckeGammaFactor_mul_inv_shift (χ : PontryaginDual C𝔽) (m : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    heckeGammaFactor χ s * (heckeGammaFactor χ (s + 2 * m))⁻¹ = (uniformShiftProd χ m s)⁻¹ := by
  have hγ := heckeGammaFactor_ne_zero_of_re_pos χ hs
  have h := inv_heckeGammaFactor_eq χ m s
  have h1 : heckeGammaFactor χ s * (heckeGammaFactor χ (s + 2 * m))⁻¹ * uniformShiftProd χ m s =
      1 := by
    rw [mul_assoc, ← h, mul_inv_cancel₀ hγ]
  exact eq_inv_of_mul_eq_one_left h1

/-- The product of the shift polynomials is bounded by a power of `‖s‖` plus a bound for the
gamma shifts. -/
private theorem norm_uniformShiftProd_le (χ : PontryaginDual C𝔽) (m : ℕ) (s : ℂ) {Y : ℝ}
    (hY : ∀ v, ‖uniformGammaShift χ v‖ ≤ Y) :
    ‖uniformShiftProd χ m s‖ ≤
      ((‖s‖ + Y + 2 * m) ^ (2 * m)) ^ Fintype.card (InfinitePlace F) := by
  rw [uniformShiftProd, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ ?_
  refine (norm_uniformShiftPoly_le v m _).trans (pow_le_pow_left₀ (by positivity) ?_ _)
  linarith [norm_add_le s (uniformGammaShift χ v), hY v]

/-- To the right of the line `Re s = 1` the product of the shift polynomials is bounded below
by a constant. -/
private theorem le_norm_uniformShiftProd (χ : PontryaginDual C𝔽) (m : ℕ) {s : ℂ}
    (hs : 1 ≤ s.re) :
    ((1 / (2 * Real.pi)) ^ (2 * m)) ^ Fintype.card (InfinitePlace F) ≤
      ‖uniformShiftProd χ m s‖ := by
  rw [uniformShiftProd, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ ?_
  refine le_norm_uniformShiftPoly v m ?_
  rw [Complex.add_re]
  linarith [uniformGammaShift_re_nonneg χ v]

/-- Conjugating the argument and inverting the character preserves the norm of the gamma
factor. This is the statement of the private `norm_heckeGammaFactor_inv_conj` of
`AppB_AnalyticNT/Sec1`, proved again here because that lemma is private. -/
private theorem norm_heckeGammaFactor_inv_conj_uniform (χ : PontryaginDual C𝔽) (s : ℂ) :
    ‖heckeGammaFactor χ⁻¹ (conj s)‖ = ‖heckeGammaFactor χ s‖ := by
  rw [heckeGammaFactor_eq_prod_uniformLocalGamma, heckeGammaFactor_eq_prod_uniformLocalGamma,
    norm_prod, norm_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [uniformGammaShift_inv, ← map_add, norm_uniformLocalGamma_conj]

/-- Reflection of the argument of the gamma factor of the inverse character is, in norm, a real
translation of the argument of the gamma factor of the character. -/
private theorem norm_heckeGammaFactor_inv_one_sub (χ : PontryaginDual C𝔽) (s : ℂ) :
    ‖heckeGammaFactor χ⁻¹ (1 - s)‖ = ‖heckeGammaFactor χ (s + ((1 - 2 * s.re : ℝ) : ℂ))‖ := by
  have h : 1 - s = conj (s + ((1 - 2 * s.re : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
    ring
  rw [h, norm_heckeGammaFactor_inv_conj_uniform]

end GammaFactors

section EulerProduct

/-- An Euler factor of a unitary character at real part at least `r > 1` lies between
`exp (-q ^ (-r))` and `exp (2 q ^ (-r))` in norm, where `q` is the norm of the prime. -/
private theorem uniform_norm_finiteHeckeEulerFactor (χ : PontryaginDual C𝔽)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {r : ℝ} (hr : 1 < r) {s : ℂ}
    (hs : r ≤ s.re) :
    Real.exp (-((v.asIdeal.absNorm : ℝ) ^ (-r))) ≤ ‖finiteHeckeEulerFactor χ v s‖ ∧
      ‖finiteHeckeEulerFactor χ v s‖ ≤ Real.exp (2 * (v.asIdeal.absNorm : ℝ) ^ (-r)) := by
  classical
  have hq2 : (2 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.two_le_absNorm_nnreal v
  have hq1 : (1 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by linarith
  have hx0 : 0 ≤ (v.asIdeal.absNorm : ℝ) ^ (-r) := Real.rpow_nonneg hq0.le _
  have hhalf : (v.asIdeal.absNorm : ℝ) ^ (-r) ≤ 1 / 2 := calc
    (v.asIdeal.absNorm : ℝ) ^ (-r) ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    _ = 1 / (v.asIdeal.absNorm : ℝ) := by rw [Real.rpow_neg hq0.le, Real.rpow_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
  unfold finiteHeckeEulerFactor
  split_ifs
  · let u := (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s)
    change Real.exp (-((v.asIdeal.absNorm : ℝ) ^ (-r))) ≤ ‖(1 - u)⁻¹‖ ∧
      ‖(1 - u)⁻¹‖ ≤ Real.exp (2 * (v.asIdeal.absNorm : ℝ) ^ (-r))
    have hu : ‖u‖ = (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by
      dsimp only [u]
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    have hux : ‖u‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-r) :=
      hu.le.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
    have hlow : 1 - (v.asIdeal.absNorm : ℝ) ^ (-r) ≤ ‖1 - u‖ := by
      have ht := norm_sub_norm_le (1 : ℂ) u
      rw [norm_one] at ht
      linarith
    have hpos : 0 < ‖1 - u‖ := by linarith
    have hup : ‖1 - u‖ ≤ Real.exp ((v.asIdeal.absNorm : ℝ) ^ (-r)) := calc
      ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 1 + (v.asIdeal.absNorm : ℝ) ^ (-r) := by rw [norm_one]; linarith
      _ ≤ Real.exp ((v.asIdeal.absNorm : ℝ) ^ (-r)) := by
        rw [add_comm]; exact Real.add_one_le_exp _
    rw [norm_inv]
    refine ⟨?_, ?_⟩
    · rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hpos).2 hup
    · rw [inv_le_comm₀ hpos (Real.exp_pos _), ← Real.exp_neg]
      refine le_trans ?_ hlow
      have h1 := Real.add_one_le_exp (2 * (v.asIdeal.absNorm : ℝ) ^ (-r))
      have h2 : Real.exp (-(2 * (v.asIdeal.absNorm : ℝ) ^ (-r))) *
          Real.exp (2 * (v.asIdeal.absNorm : ℝ) ^ (-r)) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos (-(2 * (v.asIdeal.absNorm : ℝ) ^ (-r)))]
  · rw [norm_one]
    exact ⟨Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0), Real.one_le_exp (by positivity)⟩

/-- To the right of `r > 1` the finite Hecke L-functions of all unitary characters lie, in norm,
between two positive constants that depend only on the field and on `r`. -/
private theorem uniform_norm_finiteHeckeL (F : Type*) [Field F] [NumberField F] {r : ℝ}
    (hr : 1 < r) :
    ∃ c D : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ D ∧
      ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : halfPlane), r ≤ s.val.re →
        c ≤ ‖finiteHeckeL χ s‖ ∧ ‖finiteHeckeL χ s‖ ≤ D := by
  let u (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := (v.asIdeal.absNorm : ℝ) ^ (-r)
  have hu : Summable u := (summable_absNorm_rpow F hr).comp_injective
    (fun _ _ he ↦ IsDedekindDomain.HeightOneSpectrum.ext he)
  have hpos (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : 0 ≤ u v := by
    dsimp only [u]
    positivity
  have hsum : 0 ≤ ∑' v, u v := tsum_nonneg hpos
  refine ⟨Real.exp (-(∑' v, u v)), Real.exp (2 * ∑' v, u v), Real.exp_pos _,
    Real.exp_le_one_iff.mpr (by linarith), Real.one_le_exp (by linarith), fun χ s hs ↦ ⟨?_, ?_⟩⟩
  · apply ge_of_tendsto' (finiteHeckeL_hasProd χ s).norm
    intro T
    rw [norm_prod]
    calc Real.exp (-(∑' v, u v)) ≤ Real.exp (∑ v ∈ T, -u v) := by
          rw [Finset.sum_neg_distrib]
          exact Real.exp_le_exp.mpr (neg_le_neg (hu.sum_le_tsum T fun v _ ↦ hpos v))
      _ = ∏ v ∈ T, Real.exp (-u v) := Real.exp_sum _ _
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le)
          (fun v _ ↦ (uniform_norm_finiteHeckeEulerFactor χ v hr hs).1)
  · apply le_of_tendsto' (finiteHeckeL_hasProd χ s).norm
    intro T
    rw [norm_prod]
    calc ∏ v ∈ T, ‖finiteHeckeEulerFactor χ v s‖ ≤ ∏ v ∈ T, Real.exp (2 * u v) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
            (fun v _ ↦ (uniform_norm_finiteHeckeEulerFactor χ v hr hs).2)
      _ = Real.exp (∑ v ∈ T, 2 * u v) := (Real.exp_sum _ _).symm
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (hu.sum_le_tsum T fun v _ ↦ hpos v) (by norm_num))

end EulerProduct

section Multiplier

/-- The product of the completed L-functions of a character and of its inverse satisfies a
functional equation with no root number: the unknown constants of the two functional equations
are inverse to each other. -/
private theorem uniform_paired_functionalEquation (χ : PontryaginDual C𝔽) (s : ℂ) :
    continuedCompletedHeckeL χ s * continuedCompletedHeckeL χ⁻¹ s =
      Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (1 - 2 * s)) *
        (continuedCompletedHeckeL χ (1 - s) * continuedCompletedHeckeL χ⁻¹ (1 - s)) := by
  obtain ⟨C, -, hfe⟩ := completedHeckeL_functionalEquation_conductorScale χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  have h1 := hfe s
  have h2 := hfe (1 - s)
  rw [sub_sub_cancel] at h2
  have hE : Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (1 - 2 * s)) *
      Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (s - 1 / 2)) =
      Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * ((1 - s) - 1 / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h2, h1, ← hE]
  ring

/-- The logarithm of the discriminant–conductor product is nonnegative. -/
private theorem heckeLogDiscriminantConductor_nonneg (χ : PontryaginDual C𝔽) :
    0 ≤ heckeLogDiscriminantConductor χ := by
  unfold heckeLogDiscriminantConductor
  refine add_nonneg (Real.log_natCast_nonneg _) (finsum_nonneg fun v ↦ mul_nonneg
    (Real.log_nonneg ?_) (Nat.cast_nonneg _))
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le

/-- The inverse of a character that is not trivial on the norm-one classes is not trivial on
them. -/
private theorem uniform_inv_ne_one {χ : PontryaginDual C𝔽}
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    χ⁻¹.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
  intro h
  apply hχ
  ext1 u
  exact inv_eq_one.mp (DFunLike.congr_fun h u : (χ u.val)⁻¹ = 1)

/-- The multiplier of a character: the product of the completed L-functions of the character and
of its inverse, divided by their gamma factors shifted by `2K`. -/
private def uniformMultiplier (χ : PontryaginDual C𝔽) (K : ℕ) (s : ℂ) : ℂ :=
  continuedCompletedHeckeL χ s * continuedCompletedHeckeL χ⁻¹ s *
    ((heckeGammaFactor χ (s + 2 * K))⁻¹ * (heckeGammaFactor χ⁻¹ (s + 2 * K))⁻¹)

/-- The multiplier of a character that is not trivial on the norm-one classes is entire. -/
private theorem differentiable_uniformMultiplier {χ : PontryaginDual C𝔽}
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) (K : ℕ) :
    Differentiable ℂ (uniformMultiplier χ K) := by
  have h1 := completedHeckeL_continuation_entire χ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 hχ
  have h2 := completedHeckeL_continuation_entire χ⁻¹ _ (continuedCompletedHeckeL_spec χ⁻¹).1
    (continuedCompletedHeckeL_spec χ⁻¹).2 (uniform_inv_ne_one hχ)
  have h3 : Differentiable ℂ (fun s : ℂ ↦ (heckeGammaFactor χ (s + 2 * K))⁻¹) :=
    (differentiable_inv_heckeGammaFactor χ).comp (differentiable_id.add_const _)
  have h4 : Differentiable ℂ (fun s : ℂ ↦ (heckeGammaFactor χ⁻¹ (s + 2 * K))⁻¹) :=
    (differentiable_inv_heckeGammaFactor χ⁻¹).comp (differentiable_id.add_const _)
  exact (h1.mul h2).mul (h3.mul h4)

/-- The multiplier is the completed L-function of the character times an entire function. -/
private theorem uniformMultiplier_eq_mul {χ : PontryaginDual C𝔽}
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) (K : ℕ) :
    Differentiable ℂ (continuedCompletedHeckeL χ) ∧ ∃ r : ℂ → ℂ, Differentiable ℂ r ∧
      uniformMultiplier χ K = continuedCompletedHeckeL χ * r := by
  have h1 := completedHeckeL_continuation_entire χ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 hχ
  have h2 := completedHeckeL_continuation_entire χ⁻¹ _ (continuedCompletedHeckeL_spec χ⁻¹).1
    (continuedCompletedHeckeL_spec χ⁻¹).2 (uniform_inv_ne_one hχ)
  have h3 : Differentiable ℂ (fun s : ℂ ↦ (heckeGammaFactor χ (s + 2 * K))⁻¹) :=
    (differentiable_inv_heckeGammaFactor χ).comp (differentiable_id.add_const _)
  have h4 : Differentiable ℂ (fun s : ℂ ↦ (heckeGammaFactor χ⁻¹ (s + 2 * K))⁻¹) :=
    (differentiable_inv_heckeGammaFactor χ⁻¹).comp (differentiable_id.add_const _)
  refine ⟨h1, fun s ↦ continuedCompletedHeckeL χ⁻¹ s *
    ((heckeGammaFactor χ (s + 2 * K))⁻¹ * (heckeGammaFactor χ⁻¹ (s + 2 * K))⁻¹),
    h2.mul (h3.mul h4), ?_⟩
  funext s
  simp only [uniformMultiplier, Pi.mul_apply]
  ring

/-- The multiplier vanishes at each zero of the completed L-function of the character to at
least its multiplicity. -/
private theorem uniformMultiplier_order {χ : PontryaginDual C𝔽}
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) (K : ℕ) (z : ℂ) :
    (((meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat : ℕ) : ℕ∞) ≤
      analyticOrderAt (uniformMultiplier χ K) z := by
  obtain ⟨h1, r, hr, hfun⟩ := uniformMultiplier_eq_mul hχ K
  rw [hfun, analyticOrderAt_mul (h1.analyticAt z) (hr.analyticAt z),
    (h1.analyticAt z).meromorphicOrderAt_eq]
  refine le_trans ?_ le_self_add
  generalize analyticOrderAt (continuedCompletedHeckeL χ) z = m
  induction m using ENat.recTopCoe with
  | top => exact le_top
  | coe n => simp

/-- The meromorphic orders of the multiplier dominate those of the completed L-function of the
character. -/
private theorem uniformMultiplier_meromorphicOrder {χ : PontryaginDual C𝔽}
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) (K : ℕ) (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤
      meromorphicOrderAt (uniformMultiplier χ K) z := by
  obtain ⟨h1, r, hr, hfun⟩ := uniformMultiplier_eq_mul hχ K
  rw [hfun, meromorphicOrderAt_mul (h1.analyticAt z).meromorphicAt (hr.analyticAt z).meromorphicAt]
  exact le_add_of_nonneg_right (hr.analyticAt z).meromorphicOrderAt_nonneg

/-- To the right of one the multiplier is the product of the two finite L-functions divided by
the products of the shift polynomials. -/
private theorem uniformMultiplier_eq_of_one_lt_re (χ : PontryaginDual C𝔽) (K : ℕ)
    (s : halfPlane) :
    uniformMultiplier χ K s = finiteHeckeL χ s * finiteHeckeL χ⁻¹ s *
      ((uniformShiftProd χ K s)⁻¹ * (uniformShiftProd χ⁻¹ K s)⁻¹) := by
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  unfold uniformMultiplier
  rw [(continuedCompletedHeckeL_spec χ).2 s, (continuedCompletedHeckeL_spec χ⁻¹).2 s,
    ← heckeGammaFactor_mul_inv_shift χ K hs, ← heckeGammaFactor_mul_inv_shift χ⁻¹ K hs]
  simp only [completedHeckeL, finiteHeckeL]
  ring

/-- On the line `Re s = -k - 1/2` the norm of the multiplier with shift `2(k + 1 + m)` is the
conductor factor times the norms of the two finite L-functions at `1 - s`, divided by the norms
of the products of the shift polynomials of degree `m` at `s + 2(k + 1)`. The gamma factors at
`1 - s` and at `s + 2(k + 1)` have the same norm, by conjugation. -/
private theorem norm_uniformMultiplier_of_re_eq (χ : PontryaginDual C𝔽) (k m : ℕ) {s : ℂ}
    (hs : s.re = -(k : ℝ) - 1 / 2) (w : halfPlane) (hw : (w : ℂ) = 1 - s) :
    ‖uniformMultiplier χ (k + 1 + m) s‖ =
      Real.exp (heckeLogDiscriminantConductor χ * (2 * k + 2)) *
        (‖finiteHeckeL χ w‖ * ‖finiteHeckeL χ⁻¹ w‖) *
        (‖uniformShiftProd χ m (s + 2 * ((k + 1 : ℕ) : ℂ))‖⁻¹ *
          ‖uniformShiftProd χ⁻¹ m (s + 2 * ((k + 1 : ℕ) : ℂ))‖⁻¹) := by
  have hpos : 0 < (s + 2 * ((k + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
      Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, hs]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hshift : s + ((1 - 2 * s.re : ℝ) : ℂ) = s + 2 * ((k + 1 : ℕ) : ℂ) := by
    rw [hs]
    push_cast
    ring
  have hK : s + 2 * ((k + 1 + m : ℕ) : ℂ) = s + 2 * ((k + 1 : ℕ) : ℂ) + 2 * (m : ℂ) := by
    push_cast
    ring
  have hγ1 : ‖heckeGammaFactor χ⁻¹ w‖ = ‖heckeGammaFactor χ (s + 2 * ((k + 1 : ℕ) : ℂ))‖ := by
    rw [hw, norm_heckeGammaFactor_inv_one_sub, hshift]
  have hγ2 : ‖heckeGammaFactor χ w‖ = ‖heckeGammaFactor χ⁻¹ (s + 2 * ((k + 1 : ℕ) : ℂ))‖ := by
    have h := norm_heckeGammaFactor_inv_one_sub χ⁻¹ s
    rwa [inv_inv, hshift, ← hw] at h
  have hQ1 : ‖heckeGammaFactor χ (s + 2 * ((k + 1 : ℕ) : ℂ))‖ *
      ‖(heckeGammaFactor χ (s + 2 * ((k + 1 : ℕ) : ℂ) + 2 * (m : ℂ)))⁻¹‖ =
      ‖uniformShiftProd χ m (s + 2 * ((k + 1 : ℕ) : ℂ))‖⁻¹ := by
    rw [← norm_mul, heckeGammaFactor_mul_inv_shift χ m hpos, norm_inv]
  have hQ2 : ‖heckeGammaFactor χ⁻¹ (s + 2 * ((k + 1 : ℕ) : ℂ))‖ *
      ‖(heckeGammaFactor χ⁻¹ (s + 2 * ((k + 1 : ℕ) : ℂ) + 2 * (m : ℂ)))⁻¹‖ =
      ‖uniformShiftProd χ⁻¹ m (s + 2 * ((k + 1 : ℕ) : ℂ))‖⁻¹ := by
    rw [← norm_mul, heckeGammaFactor_mul_inv_shift χ⁻¹ m hpos, norm_inv]
  have hE : ‖Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (1 - 2 * s))‖ =
      Real.exp (heckeLogDiscriminantConductor χ * (2 * k + 2)) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.one_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, hs]
    ring
  unfold uniformMultiplier
  rw [uniform_paired_functionalEquation χ s, hK, ← hw, (continuedCompletedHeckeL_spec χ).2 w,
    (continuedCompletedHeckeL_spec χ⁻¹).2 w]
  simp only [completedHeckeL, finiteHeckeL, norm_mul]
  rw [hE, hγ1, hγ2, ← hQ1, ← hQ2]
  ring

/-- At height above the gamma shifts the product of the shift polynomials is bounded below by a
constant. -/
private theorem le_norm_uniformShiftProd_of_im (χ : PontryaginDual C𝔽) (m : ℕ) {s : ℂ} {Y : ℝ}
    (hY : ∀ v, ‖uniformGammaShift χ v‖ ≤ Y) (hs : Y + 1 ≤ |s.im|) :
    ((1 / (2 * Real.pi)) ^ (2 * m)) ^ Fintype.card (InfinitePlace F) ≤
      ‖uniformShiftProd χ m s‖ := by
  rw [uniformShiftProd, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ ?_
  refine le_norm_uniformShiftPoly_of_im v m ?_
  have h1 : |(uniformGammaShift χ v).im| ≤ Y := (Complex.abs_im_le_norm _).trans (hY v)
  have h2 := abs_sub_abs_le_abs_sub s.im (-(uniformGammaShift χ v).im)
  rw [abs_neg, sub_neg_eq_add] at h2
  rw [Complex.add_im]
  linarith

/-- The multiplier has polynomial growth on each vertical strip. The exponent may depend on the
character; it is only used to apply the Phragmén–Lindelöf principle. -/
private theorem uniformMultiplier_isBigO {χ : PontryaginDual C𝔽}
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) (K : ℕ) (a b : ℝ)
    (hab : a < b) :
    ∃ M : ℝ, uniformMultiplier χ K =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ |z.im| ^ M := by
  let L (ψ : PontryaginDual C𝔽) (s : ℂ) :=
    continuedCompletedHeckeL ψ s * (heckeGammaFactor ψ s)⁻¹
  have hd (ψ : PontryaginDual C𝔽)
      (hψ : ψ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) : Differentiable ℂ (L ψ) :=
    (completedHeckeL_continuation_entire ψ _ (continuedCompletedHeckeL_spec ψ).1
      (continuedCompletedHeckeL_spec ψ).2 hψ).mul (differentiable_inv_heckeGammaFactor ψ)
  have hseries (ψ : PontryaginDual C𝔽) (s : halfPlane) : L ψ s = finiteHeckeL ψ s := by
    simp only [L, (continuedCompletedHeckeL_spec ψ).2 s, completedHeckeL, finiteHeckeL]
    field_simp [heckeGammaFactor_ne_zero_of_re_pos ψ (zero_lt_one.trans s.property)]
  have hpoly (ψ : PontryaginDual C𝔽) (h : Differentiable ℂ (L ψ)) :=
    finiteHeckeL_continuation_isBigO_rpow ψ (L ψ) (fun s _ ↦ (h.analyticAt s).meromorphicNFAt)
      (hseries ψ) a b hab
  obtain ⟨M, hMpos, hM⟩ := hpoly χ (hd χ hχ)
  obtain ⟨M', hMpos', hM'⟩ := hpoly χ⁻¹ (hd χ⁻¹ (uniform_inv_ne_one hχ))
  have hg := (hM.mul hM').congr' (g₂ := fun s : ℂ ↦ |s.im| ^ (M + M'))
    EventuallyEq.rfl (Eventually.of_forall fun s ↦ by
      by_cases hs : s.im = 0
      · simp [hs, hMpos.ne', hMpos'.ne', (add_pos hMpos hMpos').ne']
      · exact (Real.rpow_add (abs_pos.mpr hs) _ _).symm)
  let Y := ∑ v, ‖uniformGammaShift χ v‖
  have hY (v : InfinitePlace F) : ‖uniformGammaShift χ v‖ ≤ Y :=
    Finset.single_le_sum (f := fun v ↦ ‖uniformGammaShift χ v‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ v)
  have hY' (v : InfinitePlace F) : ‖uniformGammaShift χ⁻¹ v‖ ≤ Y := by
    rw [uniformGammaShift_inv, Complex.norm_conj]
    exact hY v
  let ε : ℝ := ((1 / (2 * Real.pi)) ^ (2 * K)) ^ Fintype.card (InfinitePlace F)
  have hε : 0 < ε := by positivity
  refine ⟨M + M', Asymptotics.IsBigO.trans ?_ hg⟩
  have htend : Tendsto (abs ∘ Complex.im)
      (comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)) atTop :=
    tendsto_inf_left tendsto_comap
  refine Asymptotics.IsBigO.of_bound ((ε * ε)⁻¹) ?_
  filter_upwards [htend.eventually_ge_atTop (Y + 1)] with s hs
  have h1 := le_norm_uniformShiftProd_of_im χ K hY hs
  have h2 := le_norm_uniformShiftProd_of_im χ⁻¹ K hY' hs
  have key : uniformMultiplier χ K s * (uniformShiftProd χ K s * uniformShiftProd χ⁻¹ K s) =
      L χ s * L χ⁻¹ s := by
    simp only [uniformMultiplier, L, inv_heckeGammaFactor_eq χ K s,
      inv_heckeGammaFactor_eq χ⁻¹ K s]
    ring
  have hnorm := congrArg norm key
  rw [norm_mul, norm_mul] at hnorm
  rw [inv_mul_eq_div, le_div_iff₀ (mul_pos hε hε)]
  calc ‖uniformMultiplier χ K s‖ * (ε * ε)
      ≤ ‖uniformMultiplier χ K s‖ *
          (‖uniformShiftProd χ K s‖ * ‖uniformShiftProd χ⁻¹ K s‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hε.le (norm_nonneg _)) (norm_nonneg _)
    _ = ‖(L χ * L χ⁻¹) s‖ := hnorm

/-- The Phragmén–Lindelöf principle on a vertical strip for an entire function of polynomial
growth: a bound on the two boundary lines holds on the strip. -/
private theorem uniform_norm_le_of_strip {G : ℂ → ℂ} (hd : Differentiable ℂ G) {a b C M : ℝ}
    (hab : a < b)
    (hg : G =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun z ↦ |z.im| ^ M)
    (ha : ∀ z : ℂ, z.re = a → ‖G z‖ ≤ C) (hb : ∀ z : ℂ, z.re = b → ‖G z‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖G z‖ ≤ C := by
  let l := comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)
  have htend : Tendsto (abs ∘ Complex.im) l atTop := tendsto_inf_left tendsto_comap
  let c := Real.pi / (b - a) / 2
  have hba : 0 < b - a := sub_pos.mpr hab
  have hc : 0 < c := by positivity
  have hO := (hg.mono (inf_le_inf_left _ (principal_mono.mpr
    (preimage_mono Ioo_subset_Icc_self)))).trans
    ((isLittleO_rpow_exp_pos_mul_atTop M hc).isBigO.comp_tendsto htend)
  exact PhragmenLindelof.vertical_strip hd.diffContOnCl
    ⟨c, half_lt_self (by positivity), 1, hO.trans (Asymptotics.IsBigO.of_bound 1
      (Eventually.of_forall fun s ↦ by
        simp only [Function.comp_apply, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (c * |s.im|)])))⟩
    ha hb hza hzb

/-- If the meromorphic order of `f` at a point is at most that of a function `g` analytic there,
then the multiplicity of the zero of `f` is at most the vanishing order of `g`. -/
private theorem toNat_untop₀_le_analyticOrderAt {f g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (h : meromorphicOrderAt f z ≤ meromorphicOrderAt g z) :
    (((meromorphicOrderAt f z).untop₀.toNat : ℕ) : ℕ∞) ≤ analyticOrderAt g z := by
  rw [hg.meromorphicOrderAt_eq] at h
  generalize analyticOrderAt g z = m at h ⊢
  induction m using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    rw [ENat.map_natCast] at h
    have h1 : (meromorphicOrderAt f z).untop₀ ≤ (n : ℤ) := by
      simpa using WithTop.untop₀_le_untop₀ (WithTop.coe_ne_top : ((n : ℤ) : WithTop ℤ) ≠ ⊤) h
    exact_mod_cast Int.toNat_le.mpr h1

end Multiplier

section TrivialCharacter

/-- The gamma shifts of the trivial character vanish. -/
private theorem uniformGammaShift_one (v : InfinitePlace F) :
    uniformGammaShift (1 : PontryaginDual C𝔽) v = 0 := by
  classical
  by_cases hv : v.IsReal
  · have h : (realHeckeCharacter_parameters (1 : PontryaginDual C𝔽) v hv).exists.choose =
        (0, 0) := by
      apply (realHeckeCharacter_parameters (1 : PontryaginDual C𝔽) v hv).unique
        (realHeckeCharacter_parameters (1 : PontryaginDual C𝔽) v hv).exists.choose_spec
      refine ⟨rfl, fun x ↦ ?_⟩
      change (1 : ℂ) * _ ^ (0 : ℂ) = (‖(x : ℝ)‖ : ℂ) ^ (0 : ℂ) * _ ^ (0 : ℕ)
      simp
    simp only [uniformGammaShift, dite_eq_left hv, h]
    simp
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h : (complexHeckeCharacter_parameters (1 : PontryaginDual C𝔽) v hv').exists.choose =
        (0, 0) := by
      apply (complexHeckeCharacter_parameters (1 : PontryaginDual C𝔽) v hv').unique
        (complexHeckeCharacter_parameters (1 : PontryaginDual C𝔽) v hv').exists.choose_spec
      refine ⟨rfl, fun x ↦ ?_⟩
      change (1 : ℂ) * _ ^ (0 : ℂ) = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (0 : ℂ) * _ ^ (0 : ℤ)
      simp
    simp only [uniformGammaShift, dite_eq_right hv, h]
    simp

/-- For the trivial character, the product of the shift polynomials of degree at least two is
bounded below by a constant times `‖z‖ ^ 2`, to the right of the line `Re z = 1`. -/
private theorem le_norm_uniformShiftProd_one {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hz : 1 ≤ z.re) :
    ‖z‖ ^ 2 * ((1 / (2 * Real.pi)) ^ (2 * m)) ^ Fintype.card (InfinitePlace F) ≤
      ‖uniformShiftProd (1 : PontryaginDual C𝔽) m z‖ := by
  classical
  have hz1 : 1 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have h0 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have h1 : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]
    linarith [Real.two_le_pi]
  have hplace (v : InfinitePlace F) :
      ‖z‖ ^ 2 * (1 / (2 * Real.pi)) ^ (2 * m) ≤ ‖uniformShiftPoly v m z‖ := by
    unfold uniformShiftPoly
    split_ifs
    · refine le_trans ?_ (norm_div_pow_le_norm_prod_add_mul_div_two_pi (c := 2) (by norm_num)
        (by linarith) m)
      have hr : (‖z‖ / (2 * Real.pi)) ^ m = ‖z‖ ^ m * (1 / (2 * Real.pi)) ^ m := by
        rw [← mul_pow, mul_one_div]
      rw [hr]
      exact mul_le_mul (pow_le_pow_right₀ hz1 hm) (pow_le_pow_of_le_one h0 h1 (by omega))
        (by positivity) (by positivity)
    · refine le_trans ?_ (norm_div_pow_le_norm_prod_add_mul_div_two_pi (c := 1) zero_le_one
        (by linarith) (2 * m))
      have hr : (‖z‖ / (2 * Real.pi)) ^ (2 * m) =
          ‖z‖ ^ (2 * m) * (1 / (2 * Real.pi)) ^ (2 * m) := by
        rw [← mul_pow, mul_one_div]
      rw [hr]
      exact mul_le_mul (pow_le_pow_right₀ hz1 (by omega)) le_rfl (by positivity) (by positivity)
  have hN : Fintype.card (InfinitePlace F) ≠ 0 := Fintype.card_ne_zero
  rw [uniformShiftProd, norm_prod]
  calc ‖z‖ ^ 2 * ((1 / (2 * Real.pi)) ^ (2 * m)) ^ Fintype.card (InfinitePlace F)
      ≤ (‖z‖ ^ 2) ^ Fintype.card (InfinitePlace F) *
          ((1 / (2 * Real.pi)) ^ (2 * m)) ^ Fintype.card (InfinitePlace F) :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ (one_le_pow₀ hz1) hN) (by positivity)
    _ = ∏ _v : InfinitePlace F, (‖z‖ ^ 2 * (1 / (2 * Real.pi)) ^ (2 * m)) := by
        rw [Finset.prod_const, Finset.card_univ, mul_pow]
    _ ≤ ∏ v : InfinitePlace F, ‖uniformShiftPoly v m (z + uniformGammaShift 1 v)‖ :=
        Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ by
          rw [uniformGammaShift_one, add_zero]
          exact hplace v

/-- The completed L-function of the trivial character is analytic off `0` and `1`, where it has
simple poles. -/
private theorem uniform_trivial_poles (F : Type*) [Field F] [NumberField F] :
    AnalyticOnNhd ℂ (continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)))
        ({0, 1}ᶜ : Set ℂ) ∧
      meromorphicOrderAt
        (continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))) 0 = -1 ∧
      meromorphicOrderAt
        (continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))) 1 = -1 := by
  have hL := (continuedCompletedHeckeL_spec (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))).1
  have h := (continuedCompletedHeckeL_spec (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))).2
  have hA := completedHeckeL_one_analyticOnNhd _ hL h
  obtain ⟨t, ⟨-, h0, h1, -⟩, -⟩ := completedHeckeL_continuation_simplePoles
    (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) _ hL h rfl
  have ht : t = 0 := by
    by_contra hne
    have hmem : Complex.I * (t : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨by simpa using hne, fun h1 ↦ ?_⟩
      have h2 := congrArg Complex.re h1
      simp at h2
    have h3 := (hA _ hmem).meromorphicOrderAt_nonneg
    rw [h0] at h3
    exact absurd (WithTop.coe_le_coe.mp h3) (by norm_num)
  subst ht
  exact ⟨hA, by simpa using h0, by simpa using h1⟩

/-- Normalize the product of a meromorphic function by a polynomial clearing its simple poles. -/
private theorem clear_simple_poles {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ) (Z : Finset ℂ)
    (hAway : ∀ s ∉ Z, AnalyticAt ℂ L s) (hLower : ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt L s) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f univ ∧ ∀ s ∉ Z, f s = (∏ p ∈ Z, (s-p)) * L s := by
  classical
  let P (s : ℂ) := ∏ p ∈ Z, (s-p)
  have hP (s : ℂ) : AnalyticAt ℂ P s :=
    Finset.analyticAt_fun_prod Z (f := fun p s : ℂ ↦ s - p) (fun _ _ ↦ by fun_prop)
  have hPL : MeromorphicOn (P*L) univ :=
    fun s hs ↦ (hP s).meromorphicAt.mul (hL.meromorphicOn s hs)
  refine ⟨toMeromorphicNFOn (P*L) univ, ?_, ?_⟩
  · intro s hs
    apply ((meromorphicNFOn_toMeromorphicNFOn (P*L) univ) hs).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hPL hs]
    by_cases hm : s ∈ Z
    · rw [meromorphicOrderAt_mul (hP s).meromorphicAt (hL.meromorphicOn s hs)]
      have horder : (1 : WithTop ℤ) ≤ meromorphicOrderAt P s := by
        change 1 ≤ meromorphicOrderAt (fun s ↦ ∏ p ∈ Z, (s-p)) s
        rw [meromorphicOrderAt_fun_prod (f := fun p s ↦ s-p) (fun p _ ↦ by fun_prop)]
        rw [← meromorphicOrderAt_id_sub_const (𝕜 := ℂ) (x := s)]
        exact Finset.single_le_sum (fun p _ ↦
          (show AnalyticAt ℂ (fun z : ℂ ↦ z-p) s by fun_prop).meromorphicOrderAt_nonneg) hm
      exact (show (0 : WithTop ℤ) = 1 + (-1) by norm_num) ▸ add_le_add horder (hLower s)
    · exact ((hP s).mul (hAway s hm)).meromorphicOrderAt_nonneg
  · intro s hs
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hPL (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr ((hP s).mul (hAway s hs)).meromorphicNFAt]
    rfl

/-- The completed L-function of the trivial character times `s (s - 1)` extends to an entire
function. -/
private theorem exists_trivial_entire (F : Type*) [Field F] [NumberField F] :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) *
      continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s := by
  obtain ⟨hA, h0, h1⟩ := uniform_trivial_poles F
  have hL := (continuedCompletedHeckeL_spec (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))).1
  obtain ⟨E, hE, hEeq⟩ := clear_simple_poles hL {0, 1}
    (fun s hs ↦ hA s (by simpa using hs)) (fun s ↦ by
      by_cases hs : s = 0 ∨ s = 1
      · rcases hs with rfl | rfl
        · rw [h0]
        · rw [h1]
      · have hneg : (-1 : WithTop ℤ) ≤ 0 :=
          WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)
        exact hneg.trans (hA s (by simpa [not_or] using hs)).meromorphicOrderAt_nonneg)
  refine ⟨E, fun z ↦ (hE z (mem_univ z)).differentiableAt, fun s hs0 hs1 ↦ ?_⟩
  rw [hEeq s (by simp [hs0, hs1]), Finset.prod_pair zero_ne_one, sub_zero]

/-- The multiplier of the trivial character, built from an entire function `E` that equals
`s (s - 1)` times the completed L-function off the two poles: `E ^ 2` divided by the square of
the gamma factor shifted by `2K`. -/
private def trivialMultiplier (F : Type*) [Field F] [NumberField F] (E : ℂ → ℂ) (K : ℕ)
    (s : ℂ) : ℂ :=
  E s * E s * ((heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s + 2 * K))⁻¹ *
    (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s + 2 * K))⁻¹)

/-- The multiplier of the trivial character is entire. -/
private theorem differentiable_trivialMultiplier {E : ℂ → ℂ} (hEd : Differentiable ℂ E)
    (K : ℕ) : Differentiable ℂ (trivialMultiplier F E K) := by
  have hg : Differentiable ℂ (fun s : ℂ ↦
      (heckeGammaFactor (1 : PontryaginDual C𝔽) (s + 2 * K))⁻¹) :=
    (differentiable_inv_heckeGammaFactor 1).comp (differentiable_id.add_const _)
  exact (hEd.mul hEd).mul (hg.mul hg)

/-- Off the two poles, the multiplier of the trivial character is `(s (s - 1)) ^ 2` times the
multiplier of the general construction. -/
private theorem trivialMultiplier_eq {E : ℂ → ℂ}
    (hEeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) *
      continuedCompletedHeckeL (1 : PontryaginDual C𝔽) s) (K : ℕ) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    trivialMultiplier F E K s =
      (s * (s - 1)) ^ 2 * uniformMultiplier (1 : PontryaginDual C𝔽) K s := by
  simp only [trivialMultiplier, uniformMultiplier, inv_one, hEeq s hs0 hs1]
  ring

/-- The meromorphic orders of the multiplier of the trivial character dominate those of the
completed L-function. -/
private theorem trivialMultiplier_meromorphicOrder {E : ℂ → ℂ} (hEd : Differentiable ℂ E)
    (hEeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) *
      continuedCompletedHeckeL (1 : PontryaginDual C𝔽) s) (K : ℕ) (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽)) z ≤
      meromorphicOrderAt (trivialMultiplier F E K) z := by
  obtain ⟨hA, h0, h1⟩ := uniform_trivial_poles F
  have hθ := differentiable_trivialMultiplier (F := F) hEd K
  have hneg : (-1 : WithTop ℤ) ≤ 0 := WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)
  by_cases hz : z = 0 ∨ z = 1
  · have hnn := (hθ.analyticAt z).meromorphicOrderAt_nonneg
    rcases hz with rfl | rfl
    · rw [h0]
      exact hneg.trans hnn
    · rw [h1]
      exact hneg.trans hnn
  · rw [not_or] at hz
    have hg : Differentiable ℂ (fun s : ℂ ↦
        (heckeGammaFactor (1 : PontryaginDual C𝔽) (s + 2 * K))⁻¹) :=
      (differentiable_inv_heckeGammaFactor 1).comp (differentiable_id.add_const _)
    let r (s : ℂ) := s * (s - 1) * E s *
      ((heckeGammaFactor (1 : PontryaginDual C𝔽) (s + 2 * K))⁻¹ *
        (heckeGammaFactor (1 : PontryaginDual C𝔽) (s + 2 * K))⁻¹)
    have hr : Differentiable ℂ r :=
      ((differentiable_id.mul (differentiable_id.sub_const 1)).mul hEd).mul (hg.mul hg)
    have hΛ : AnalyticAt ℂ (continuedCompletedHeckeL (1 : PontryaginDual C𝔽)) z :=
      hA z (by simp [hz.1, hz.2])
    have hopen : ∀ᶠ s in 𝓝 z, s ≠ 0 ∧ s ≠ 1 :=
      (isOpen_ne.inter isOpen_ne).mem_nhds hz
    have heq : trivialMultiplier F E K =ᶠ[𝓝 z]
        continuedCompletedHeckeL (1 : PontryaginDual C𝔽) * r := by
      filter_upwards [hopen] with s hs
      simp only [trivialMultiplier, Pi.mul_apply, r, hEeq s hs.1 hs.2]
      ring
    rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_mul hΛ.meromorphicAt (hr.analyticAt z).meromorphicAt]
    exact le_add_of_nonneg_right (hr.analyticAt z).meromorphicOrderAt_nonneg

/-- The multiplier of the trivial character has polynomial growth on each vertical strip. The
exponent is only used to apply the Phragmén–Lindelöf principle. -/
private theorem trivialMultiplier_isBigO {E : ℂ → ℂ}
    (hEeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) *
      continuedCompletedHeckeL (1 : PontryaginDual C𝔽) s) (K : ℕ) (a b : ℝ) (hab : a < b) :
    ∃ M : ℝ, trivialMultiplier F E K =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ |z.im| ^ M := by
  obtain ⟨hA, -, -⟩ := uniform_trivial_poles F
  have hL := (continuedCompletedHeckeL_spec (1 : PontryaginDual C𝔽)).1
  have hG := differentiable_inv_heckeGammaFactor (1 : PontryaginDual C𝔽)
  let prod : ℂ → ℂ := fun s ↦ (heckeGammaFactor (1 : PontryaginDual C𝔽) s)⁻¹ *
    continuedCompletedHeckeL (1 : PontryaginDual C𝔽) s
  have hm : MeromorphicOn prod univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hL hz).meromorphicAt
  let Lf := toMeromorphicNFOn prod univ
  have hLfeq (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) : Lf z = prod z := by
    have han : AnalyticAt ℂ prod z := (hG.analyticAt z).mul (hA z (by simp [hz0, hz1]))
    change toMeromorphicNFOn prod univ z = prod z
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt]
  have hSeries : ∀ z : halfPlane, Lf z = finiteHeckeL (1 : PontryaginDual C𝔽) z := by
    intro z
    have hz1 : (1 : ℝ) < (z : ℂ).re := z.property
    have hγ := heckeGammaFactor_ne_zero_of_re_pos (1 : PontryaginDual C𝔽)
      (zero_lt_one.trans hz1)
    have h0 : (z : ℂ) ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_re] at hz1
      linarith
    have h1 : (z : ℂ) ≠ 1 := fun h ↦ by
      rw [h, Complex.one_re] at hz1
      exact lt_irrefl _ hz1
    rw [hLfeq z h0 h1]
    simp only [prod, (continuedCompletedHeckeL_spec (1 : PontryaginDual C𝔽)).2 z,
      completedHeckeL, finiteHeckeL]
    field_simp
  obtain ⟨M, -, hM⟩ := finiteHeckeL_continuation_isBigO_rpow (1 : PontryaginDual C𝔽) Lf
    (meromorphicNFOn_toMeromorphicNFOn _ _) hSeries a b hab
  have htend : Tendsto (abs ∘ Complex.im)
      (comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)) atTop :=
    tendsto_inf_left tendsto_comap
  have hmem : ∀ᶠ s : ℂ in comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc a b),
      s ∈ Complex.re ⁻¹' Icc a b := mem_inf_of_right (mem_principal_self _)
  let cab : ℝ := |a| + |b| + 2
  have h4 : (fun s : ℂ ↦ (s * (s - 1)) ^ 2) =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ (4 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (cab ^ 4) ?_
    filter_upwards [hmem, htend.eventually_ge_atTop 1] with s hs him
    change 1 ≤ |s.im| at him
    have hre : |s.re| ≤ |a| + |b| := by
      rw [abs_le]
      constructor
      · linarith [hs.1, neg_abs_le a, abs_nonneg b]
      · linarith [hs.2, le_abs_self b, abs_nonneg a]
    have hnorm := Complex.norm_le_abs_re_add_abs_im s
    have hs_norm : ‖s‖ ≤ cab * |s.im| := by
      dsimp only [cab]
      nlinarith [abs_nonneg a, abs_nonneg b]
    have hs1_norm : ‖s - 1‖ ≤ cab * |s.im| := by
      have h2 := norm_sub_le s 1
      rw [norm_one] at h2
      dsimp only [cab]
      nlinarith [abs_nonneg a, abs_nonneg b]
    have hrpow : |s.im| ^ (4 : ℝ) = |s.im| ^ 4 := by
      exact_mod_cast Real.rpow_natCast |s.im| 4
    rw [norm_pow, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hrpow]
    calc (‖s‖ * ‖s - 1‖) ^ 2 ≤ ((cab * |s.im|) * (cab * |s.im|)) ^ 2 := by gcongr
      _ = cab ^ 4 * |s.im| ^ 4 := by ring
  have hprod := h4.mul (hM.mul hM)
  let ε : ℝ := ((1 / (2 * Real.pi)) ^ (2 * K)) ^ Fintype.card (InfinitePlace F)
  have hε : 0 < ε := by positivity
  have hθ : trivialMultiplier F E K =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Icc a b)] fun s : ℂ ↦ (s * (s - 1)) ^ 2 * (Lf s * Lf s) := by
    refine Asymptotics.IsBigO.of_bound ((ε * ε)⁻¹) ?_
    filter_upwards [htend.eventually_ge_atTop 1] with s him
    change 1 ≤ |s.im| at him
    have hs0 : s ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_im, abs_zero] at him
      linarith
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [h, Complex.one_im, abs_zero] at him
      linarith
    have hQ := le_norm_uniformShiftProd_of_im (1 : PontryaginDual C𝔽) K (Y := 0) (s := s)
      (fun v ↦ by rw [uniformGammaShift_one, norm_zero]) (by linarith)
    have key : trivialMultiplier F E K s *
        (uniformShiftProd (1 : PontryaginDual C𝔽) K s *
          uniformShiftProd (1 : PontryaginDual C𝔽) K s) =
        (s * (s - 1)) ^ 2 * (Lf s * Lf s) := by
      rw [hLfeq s hs0 hs1]
      simp only [trivialMultiplier, prod, hEeq s hs0 hs1,
        inv_heckeGammaFactor_eq (1 : PontryaginDual C𝔽) K s]
      ring
    have hnorm := congrArg norm key
    rw [norm_mul, norm_mul] at hnorm
    rw [inv_mul_eq_div, le_div_iff₀ (mul_pos hε hε)]
    calc ‖trivialMultiplier F E K s‖ * (ε * ε)
        ≤ ‖trivialMultiplier F E K s‖ * (‖uniformShiftProd (1 : PontryaginDual C𝔽) K s‖ *
            ‖uniformShiftProd (1 : PontryaginDual C𝔽) K s‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hQ hQ hε.le (norm_nonneg _)) (norm_nonneg _)
      _ = ‖(s * (s - 1)) ^ 2 * (Lf s * Lf s)‖ := hnorm
  refine ⟨4 + (M + M), (hθ.trans hprod).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [htend.eventually_ge_atTop 1] with s him
  change 1 ≤ |s.im| at him
  have hpos : 0 < |s.im| := by linarith
  rw [Real.rpow_add hpos, Real.rpow_add hpos]

/-- The bounds for the multiplier of the trivial character with shift `2(K + 3)`: it is bounded
on the strip `-K - 1/2 ≤ Re s ≤ R`, and bounded below by an inverse power of `‖s‖ + 1` to the
right of `3/2` and on the lines `Re s = -k - 1/2`, `k ≤ K`. The two extra shifts absorb the
factor `(s (s - 1)) ^ 2` that removes the poles. -/
private theorem trivialMultiplier_bounds (F : Type*) [Field F] [NumberField F] (K : ℕ) {R : ℝ}
    (hR : 3 / 2 ≤ R) {E : ℂ → ℂ} (hEd : Differentiable ℂ E)
    (hEeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) *
      continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s) :
    ∃ (C c : ℝ) (n : ℕ), 0 < C ∧ 0 < c ∧
      (∀ s : ℂ, -(K : ℝ) - 1 / 2 ≤ s.re → s.re ≤ R → ‖trivialMultiplier F E (K + 3) s‖ ≤ C) ∧
      (∀ s : ℂ, 3 / 2 ≤ s.re → c / (‖s‖ + 1) ^ n ≤ ‖trivialMultiplier F E (K + 3) s‖) ∧
      (∀ k : ℕ, k ≤ K → ∀ s : ℂ, s.re = -(k : ℝ) - 1 / 2 →
        c / (‖s‖ + 1) ^ n ≤ ‖trivialMultiplier F E (K + 3) s‖) := by
  obtain ⟨c₀, D, hc₀, -, hD1, hLD⟩ := uniform_norm_finiteHeckeL F (r := 3 / 2) (by norm_num)
  have hD0 : 0 < D := by linarith
  let N := Fintype.card (InfinitePlace F)
  let δR : ℝ := ((1 / (2 * Real.pi)) ^ (2 * (K + 3))) ^ N
  let δL : ℝ := ((1 / (2 * Real.pi)) ^ (2 * 2)) ^ N
  have hδR : 0 < δR := by positivity
  have hδL : 0 < δL := by positivity
  let a₁ : ℝ := heckeLogDiscriminantConductor (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  have ha₁ : 0 ≤ a₁ := heckeLogDiscriminantConductor_nonneg _
  let E₁ : ℝ := Real.exp (a₁ * (2 * K + 2))
  let CR : ℝ := 4 * (D * D) / (δR * δR)
  let CL : ℝ := ((2 * (K : ℝ) + 3) * (2 * (K : ℝ) + 4)) ^ 2 * E₁ * (D * D) / (δL * δL)
  have hCR : 0 < CR := by positivity
  have hCL : 0 < CL := by positivity
  let B : ℝ := 2 * ((K + 3 : ℕ) : ℝ)
  have hB : 0 < B := by positivity
  let n : ℕ := 2 * (K + 3) * (N * 2)
  have hθ := differentiable_trivialMultiplier (F := F) hEd (K + 3)
  have hshift0 (v : InfinitePlace F) :
      ‖uniformGammaShift (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) v‖ ≤ 0 := by
    rw [uniformGammaShift_one, norm_zero]
  -- One bound `W s` for all the products of shift polynomials that occur.
  let W (s : ℂ) : ℝ := ((‖s‖ + 2 * ((K + 3 : ℕ) : ℝ)) ^ (2 * (K + 3))) ^ N
  have hWpos (s : ℂ) : 0 < W s := by positivity
  have hWle (m : ℕ) (hm : m ≤ K + 3) (s z : ℂ)
      (hz : ‖z‖ + 2 * (m : ℝ) ≤ ‖s‖ + 2 * ((K + 3 : ℕ) : ℝ)) :
      ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) m z‖ ≤ W s := by
    refine (norm_uniformShiftProd_le _ m z hshift0).trans (pow_le_pow_left₀ (by positivity) ?_ _)
    have hbase : (1 : ℝ) ≤ ‖s‖ + 2 * ((K + 3 : ℕ) : ℝ) := by
      push_cast
      linarith [norm_nonneg s, Nat.cast_nonneg (α := ℝ) K]
    calc (‖z‖ + 0 + 2 * (m : ℝ)) ^ (2 * m)
        ≤ (‖s‖ + 2 * ((K + 3 : ℕ) : ℝ)) ^ (2 * m) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (‖s‖ + 2 * ((K + 3 : ℕ) : ℝ)) ^ (2 * (K + 3)) :=
          pow_le_pow_right₀ hbase (by omega)
  -- The final comparison of constants for the lower bounds.
  have hfinal (s : ℂ) (h : 1 / 16 * (c₀ * c₀ * ((W s)⁻¹ * (W s)⁻¹)) ≤
      ‖trivialMultiplier F E (K + 3) s‖) :
      c₀ * c₀ / 16 / B ^ n / (‖s‖ + 1) ^ n ≤ ‖trivialMultiplier F E (K + 3) s‖ := by
    have ht : 0 < ‖s‖ + 1 := by linarith [norm_nonneg s]
    have hWB : W s ≤ ((B * (‖s‖ + 1)) ^ (2 * (K + 3))) ^ N := by
      refine pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _) _
      have h1 : (1 : ℝ) ≤ 2 * ((K + 3 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) K]
      have h3 : 0 ≤ ‖s‖ := norm_nonneg s
      change ‖s‖ + 2 * ((K + 3 : ℕ) : ℝ) ≤ 2 * ((K + 3 : ℕ) : ℝ) * (‖s‖ + 1)
      nlinarith
    have hpow : ((B * (‖s‖ + 1)) ^ (2 * (K + 3))) ^ N *
        ((B * (‖s‖ + 1)) ^ (2 * (K + 3))) ^ N =
        B ^ (2 * (K + 3) * (N * 2)) * (‖s‖ + 1) ^ (2 * (K + 3) * (N * 2)) := by
      rw [← sq, ← pow_mul, ← pow_mul, mul_pow]
    have hWW : W s * W s ≤ B ^ n * (‖s‖ + 1) ^ n :=
      (mul_le_mul hWB hWB (hWpos s).le (by positivity)).trans_eq hpow
    have hinv := mul_inv (W s) (W s)
    calc c₀ * c₀ / 16 / B ^ n / (‖s‖ + 1) ^ n
        = 1 / 16 * (c₀ * c₀ * (B ^ n * (‖s‖ + 1) ^ n)⁻¹) := by
          rw [div_div, div_div, div_eq_mul_inv, mul_inv]
          ring
      _ ≤ 1 / 16 * (c₀ * c₀ * (W s * W s)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (inv_anti₀ (mul_pos (hWpos s) (hWpos s)) hWW) (by positivity)) (by norm_num)
      _ = 1 / 16 * (c₀ * c₀ * ((W s)⁻¹ * (W s)⁻¹)) := by rw [hinv]
      _ ≤ ‖trivialMultiplier F E (K + 3) s‖ := h
  -- The norm to the right of `3/2`.
  have hright (s : ℂ) (hs : 3 / 2 ≤ s.re) : ∃ w : halfPlane, (w : ℂ) = s ∧
      ‖trivialMultiplier F E (K + 3) s‖ = (‖s‖ * ‖s - 1‖) ^ 2 *
        (‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖ *
          ‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖ *
          (‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) s‖⁻¹ *
            ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) s‖⁻¹)) := by
    have hw : 1 < s.re := by linarith
    have hs0 : s ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_re] at hs
      linarith
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [h, Complex.one_re] at hs
      linarith
    have h := uniformMultiplier_eq_of_one_lt_re
      (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) ⟨s, hw⟩
    rw [inv_one] at h
    change uniformMultiplier (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) s = _ at h
    refine ⟨⟨s, hw⟩, rfl, ?_⟩
    rw [trivialMultiplier_eq hEeq (K + 3) hs0 hs1, h]
    simp only [norm_mul, norm_pow, norm_inv]
  -- The norm on the line `Re s = -k - 1/2`.
  have hleft (k : ℕ) (hk : k ≤ K) (s : ℂ) (hs : s.re = -(k : ℝ) - 1 / 2) :
      ∃ w : halfPlane, (3 / 2 : ℝ) ≤ (w : ℂ).re ∧
      ‖trivialMultiplier F E (K + 3) s‖ = (‖s‖ * ‖s - 1‖) ^ 2 *
        (Real.exp (a₁ * (2 * k + 2)) *
          (‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖ *
            ‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖) *
          (‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 2 - k)
              (s + 2 * ((k + 1 : ℕ) : ℂ))‖⁻¹ *
            ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 2 - k)
              (s + 2 * ((k + 1 : ℕ) : ℂ))‖⁻¹)) := by
    have hw : 1 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re, hs]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hre : (3 / 2 : ℝ) ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re, hs]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hs0 : s ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_re] at hs
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [h, Complex.one_re] at hs
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hKk : k + 1 + (K + 2 - k) = K + 3 := by omega
    have h := norm_uniformMultiplier_of_re_eq
      (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) k (K + 2 - k) hs ⟨1 - s, hw⟩ rfl
    rw [hKk, inv_one] at h
    refine ⟨⟨1 - s, hw⟩, hre, ?_⟩
    rw [trivialMultiplier_eq hEeq (K + 3) hs0 hs1, norm_mul, norm_pow, norm_mul, h]
  refine ⟨CL + CR, c₀ * c₀ / 16 / B ^ n, n, by positivity, by positivity,
    fun s hs1 hs2 ↦ ?_, fun s hs ↦ hfinal s ?_, fun k hk s hs ↦ hfinal s ?_⟩
  · -- Boundedness on the strip, by the Phragmén–Lindelöf principle.
    have hab : -(K : ℝ) - 1 / 2 < R := by linarith [Nat.cast_nonneg (α := ℝ) K]
    obtain ⟨M, hM⟩ := trivialMultiplier_isBigO (F := F) hEeq (K + 3) (-(K : ℝ) - 1 / 2) R hab
    have hl : ∀ z : ℂ, z.re = -(K : ℝ) - 1 / 2 → ‖trivialMultiplier F E (K + 3) z‖ ≤ CL + CR := by
      intro z hz
      obtain ⟨w, hwre, h⟩ := hleft K le_rfl z hz
      have hL := (hLD (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w hwre).2
      have hz'1 : 1 ≤ (z + 2 * ((K + 1 : ℕ) : ℂ)).re := by
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, hz]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) K]
      have hm2 : K + 2 - K = 2 := by omega
      rw [hm2] at h
      have hQ := le_norm_uniformShiftProd_one (F := F) (m := 2) le_rfl hz'1
      set z' : ℂ := z + 2 * ((K + 1 : ℕ) : ℂ) with hz'def
      have hz'n : 1 ≤ ‖z'‖ := hz'1.trans (Complex.re_le_norm z')
      have hzn : ‖z‖ ≤ (2 * (K : ℝ) + 3) * ‖z'‖ := by
        have h1 : z = z' - 2 * ((K + 1 : ℕ) : ℂ) := by rw [hz'def]; ring
        have h2 : ‖(2 : ℂ) * ((K + 1 : ℕ) : ℂ)‖ = 2 * ((K : ℝ) + 1) := by
          rw [norm_mul, Complex.norm_two, Complex.norm_natCast]
          push_cast
          ring
        have h3 := norm_sub_le z' (2 * ((K + 1 : ℕ) : ℂ))
        rw [← h1, h2] at h3
        nlinarith [Nat.cast_nonneg (α := ℝ) K]
      have hz1n : ‖z - 1‖ ≤ (2 * (K : ℝ) + 4) * ‖z'‖ := by
        have h3 := norm_sub_le z 1
        rw [norm_one] at h3
        nlinarith [Nat.cast_nonneg (α := ℝ) K]
      have hQpos : 0 < ‖z'‖ ^ 2 * δL := by positivity
      have hQinv : ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2 z'‖⁻¹ ≤
          (‖z'‖ ^ 2 * δL)⁻¹ := inv_anti₀ hQpos hQ
      have hE : Real.exp (a₁ * (2 * K + 2)) = E₁ := rfl
      rw [h, hE]
      have hstep : (‖z‖ * ‖z - 1‖) ^ 2 * (E₁ *
          (‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖ *
            ‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖) *
          (‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2 z'‖⁻¹ *
            ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2 z'‖⁻¹)) ≤
          (((2 * (K : ℝ) + 3) * ‖z'‖) * ((2 * (K : ℝ) + 4) * ‖z'‖)) ^ 2 * (E₁ * (D * D) *
            ((‖z'‖ ^ 2 * δL)⁻¹ * (‖z'‖ ^ 2 * δL)⁻¹)) := by
        refine mul_le_mul (pow_le_pow_left₀ (by positivity)
          (mul_le_mul hzn hz1n (norm_nonneg _) (by positivity)) 2)
          (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hL hL (norm_nonneg _) hD0.le)
            (Real.exp_pos _).le) (mul_le_mul hQinv hQinv (by positivity) (by positivity))
            (by positivity) (by positivity)) (by positivity) (by positivity)
      refine hstep.trans ?_
      have hz'0 : ‖z'‖ ≠ 0 := by linarith
      have heq : (((2 * (K : ℝ) + 3) * ‖z'‖) * ((2 * (K : ℝ) + 4) * ‖z'‖)) ^ 2 * (E₁ * (D * D) *
          ((‖z'‖ ^ 2 * δL)⁻¹ * (‖z'‖ ^ 2 * δL)⁻¹)) = CL := by
        dsimp only [CL]
        field_simp
      rw [heq]
      linarith
    have hr : ∀ z : ℂ, z.re = R → ‖trivialMultiplier F E (K + 3) z‖ ≤ CL + CR := by
      intro z hz
      obtain ⟨w, hwz, h⟩ := hright z (by linarith)
      have hL := (hLD (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w (by rw [hwz]; linarith)).2
      have hQ := le_norm_uniformShiftProd_one (F := F) (m := K + 3) (by omega) (z := z)
        (by linarith)
      have hzn : 1 ≤ ‖z‖ := by
        have := Complex.re_le_norm z
        linarith
      have hz1n : ‖z - 1‖ ≤ 2 * ‖z‖ := by
        have h3 := norm_sub_le z 1
        rw [norm_one] at h3
        linarith
      have hQpos : 0 < ‖z‖ ^ 2 * δR := by positivity
      have hQinv : ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) z‖⁻¹ ≤
          (‖z‖ ^ 2 * δR)⁻¹ := inv_anti₀ hQpos hQ
      rw [h]
      have hstep : (‖z‖ * ‖z - 1‖) ^ 2 *
          (‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖ *
            ‖finiteHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w‖ *
          (‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) z‖⁻¹ *
            ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (K + 3) z‖⁻¹)) ≤
          (‖z‖ * (2 * ‖z‖)) ^ 2 * (D * D * ((‖z‖ ^ 2 * δR)⁻¹ * (‖z‖ ^ 2 * δR)⁻¹)) := by
        refine mul_le_mul (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hz1n (norm_nonneg _)) 2)
          (mul_le_mul (mul_le_mul hL hL (norm_nonneg _) hD0.le)
            (mul_le_mul hQinv hQinv (by positivity) (by positivity))
            (by positivity) (by positivity)) (by positivity) (by positivity)
      refine hstep.trans ?_
      have hz0 : ‖z‖ ≠ 0 := by linarith
      have heq : (‖z‖ * (2 * ‖z‖)) ^ 2 * (D * D * ((‖z‖ ^ 2 * δR)⁻¹ * (‖z‖ ^ 2 * δR)⁻¹)) =
          CR := by
        dsimp only [CR]
        field_simp
        ring
      rw [heq]
      linarith
    exact uniform_norm_le_of_strip hθ hab hM hl hr hs1 hs2
  · -- To the right of `3/2`.
    obtain ⟨w, hwz, h⟩ := hright s hs
    have hL := (hLD (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w (by rw [hwz]; exact hs)).1
    have hQ := hWle (K + 3) le_rfl s s le_rfl
    have hQpos : 0 < ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (K + 3) s‖ :=
      lt_of_lt_of_le (by positivity) (le_norm_uniformShiftProd _ (K + 3) (s := s) (by linarith))
    have hsn : 1 ≤ ‖s‖ := by
      have := Complex.re_le_norm s
      linarith
    have hs1n : 1 / 2 ≤ ‖s - 1‖ := by
      have := Complex.re_le_norm (s - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      linarith
    rw [h]
    refine mul_le_mul ?_ (mul_le_mul (mul_le_mul hL hL hc₀.le (norm_nonneg _))
      (mul_le_mul (inv_anti₀ hQpos hQ) (inv_anti₀ hQpos hQ) (by positivity) (by positivity))
      (by positivity) (by positivity)) (by positivity) (by positivity)
    have h1 : (1 : ℝ) / 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
    calc (1 : ℝ) / 16 ≤ (1 / 2) ^ 2 := by norm_num
      _ ≤ (‖s‖ * ‖s - 1‖) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  · -- On the line `Re s = -k - 1/2`.
    obtain ⟨w, hwre, h⟩ := hleft k hk s hs
    have hL := (hLD (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) w hwre).1
    have hz1 : 1 ≤ (s + 2 * ((k + 1 : ℕ) : ℂ)).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, hs]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hKk : ((k + 1 : ℕ) : ℝ) + ((K + 2 - k : ℕ) : ℝ) = ((K + 3 : ℕ) : ℝ) := by
      have : k + 1 + (K + 2 - k) = K + 3 := by omega
      exact_mod_cast this
    have hnorm : ‖s + 2 * ((k + 1 : ℕ) : ℂ)‖ + 2 * ((K + 2 - k : ℕ) : ℝ) ≤
        ‖s‖ + 2 * ((K + 3 : ℕ) : ℝ) := by
      have h1 : ‖(2 : ℂ) * ((k + 1 : ℕ) : ℂ)‖ = 2 * ((k + 1 : ℕ) : ℝ) := by
        rw [norm_mul, Complex.norm_two, Complex.norm_natCast]
      have h2 := norm_add_le s (2 * ((k + 1 : ℕ) : ℂ))
      rw [h1] at h2
      linarith
    have hQ := hWle (K + 2 - k) (by omega) s _ hnorm
    have hQpos : 0 < ‖uniformShiftProd (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (K + 2 - k) (s + 2 * ((k + 1 : ℕ) : ℂ))‖ :=
      lt_of_lt_of_le (by positivity) (le_norm_uniformShiftProd _ (K + 2 - k) hz1)
    have hE : (1 : ℝ) ≤ Real.exp (a₁ * (2 * k + 2)) :=
      Real.one_le_exp (mul_nonneg ha₁ (by positivity))
    have hsn : 1 / 2 ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hs] at this
      have h2 : (k : ℝ) + 1 / 2 ≤ |-(k : ℝ) - 1 / 2| := by
        rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) k])]
        linarith
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hs1n : 1 / 2 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, Complex.one_re, hs] at this
      have h2 : (k : ℝ) + 3 / 2 ≤ |-(k : ℝ) - 1 / 2 - 1| := by
        rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) k])]
        linarith
      linarith [Nat.cast_nonneg (α := ℝ) k]
    rw [h]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · have h1 : (1 : ℝ) / 4 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
      calc (1 : ℝ) / 16 = (1 / 4) ^ 2 := by norm_num
        _ ≤ (‖s‖ * ‖s - 1‖) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    · calc c₀ * c₀ * ((W s)⁻¹ * (W s)⁻¹) = 1 * (c₀ * c₀) * ((W s)⁻¹ * (W s)⁻¹) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul hE (mul_le_mul hL hL hc₀.le (norm_nonneg _))
            (by positivity) (Real.exp_pos _).le)
            (mul_le_mul (inv_anti₀ hQpos hQ) (inv_anti₀ hQpos hQ) (by positivity) (by positivity))
            (by positivity) (by positivity)

end TrivialCharacter

section Uniform

open Classical in
/-- The bounds for the multiplier with shift `2(K + 1)`, with every constant uniform in the
character: it is bounded on the strip `-K - 1/2 ≤ Re s ≤ R`, and bounded below by an inverse
power of `‖s‖ + X` to the right of `3/2` and on the lines `Re s = -k - 1/2`, `k ≤ K`, where `X`
bounds the archimedean parameters. -/
private theorem uniformMultiplier_bounds (F : Type*) [Field F] [NumberField F] (K : ℕ) {R : ℝ}
    (hR : 3 / 2 ≤ R) (A : ℝ) :
    ∃ (C c : ℝ) (n : ℕ), 0 < C ∧ 0 < c ∧ ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      heckeLogDiscriminantConductor χ ≤ A →
        (∀ s : ℂ, -(K : ℝ) - 1 / 2 ≤ s.re → s.re ≤ R → ‖uniformMultiplier χ (K + 1) s‖ ≤ C) ∧
        ∀ X : ℝ, 1 ≤ X →
          (∀ w : InfinitePlace F, if hw : w.IsReal then
              ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ X
            else
              let p := (complexHeckeCharacter_parameters χ w
                (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
              ‖p.1‖ ≤ X ∧ (p.2.natAbs : ℝ) ≤ X) →
          (∀ s : ℂ, 3 / 2 ≤ s.re → c / (‖s‖ + X) ^ n ≤ ‖uniformMultiplier χ (K + 1) s‖) ∧
          (∀ k : ℕ, k ≤ K → ∀ s : ℂ, s.re = -(k : ℝ) - 1 / 2 →
            c / (‖s‖ + X) ^ n ≤ ‖uniformMultiplier χ (K + 1) s‖) := by
  obtain ⟨c₀, D, hc₀, -, hD1, hLD⟩ := uniform_norm_finiteHeckeL F (r := 3 / 2) (by norm_num)
  let N := Fintype.card (InfinitePlace F)
  let ε : ℝ := ((1 / (2 * Real.pi)) ^ (2 * (K + 1))) ^ N
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    have h1 : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
      rw [div_le_one (by positivity)]
      linarith [Real.two_le_pi]
    exact pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) h1)
  let E : ℝ := Real.exp (A * (2 * K + 2))
  let C : ℝ := (E + 1) * (D * D) * (ε * ε)⁻¹
  have hD0 : 0 < D := by linarith
  have hC : 0 < C := by positivity
  let B : ℝ := 2 * ((K + 1 : ℕ) : ℝ) + 2
  have hB : 0 < B := by positivity
  let n : ℕ := 2 * (K + 1) * (N * 2)
  refine ⟨C, c₀ * c₀ / B ^ n, n, hC, by positivity, fun χ hχ hA ↦ ?_⟩
  have ha := heckeLogDiscriminantConductor_nonneg χ
  have hd := differentiable_uniformMultiplier hχ (K + 1)
  refine ⟨fun s hs1 hs2 ↦ ?_, fun X hX harch ↦ ?_⟩
  · -- Boundedness on the strip, by the Phragmén–Lindelöf principle.
    have hab : -(K : ℝ) - 1 / 2 < R := by linarith [Nat.cast_nonneg (α := ℝ) K]
    obtain ⟨M, hM⟩ := uniformMultiplier_isBigO hχ (K + 1) (-(K : ℝ) - 1 / 2) R hab
    have hleft : ∀ z : ℂ, z.re = -(K : ℝ) - 1 / 2 → ‖uniformMultiplier χ (K + 1) z‖ ≤ C := by
      intro z hz
      have hw : 1 < (1 - z).re := by
        rw [Complex.sub_re, Complex.one_re, hz]
        linarith [Nat.cast_nonneg (α := ℝ) K]
      have h := norm_uniformMultiplier_of_re_eq χ K 0 hz ⟨1 - z, hw⟩ rfl
      have hre : (3 / 2 : ℝ) ≤ (1 - z).re := by
        rw [Complex.sub_re, Complex.one_re, hz]
        linarith [Nat.cast_nonneg (α := ℝ) K]
      have hL1 := (hLD χ ⟨1 - z, hw⟩ hre).2
      have hL2 := (hLD χ⁻¹ ⟨1 - z, hw⟩ hre).2
      have hz1 : 1 ≤ (z + 2 * ((K + 1 : ℕ) : ℂ)).re := by
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, hz]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) K]
      have hQ1 := le_norm_uniformShiftProd χ 0 hz1
      have hQ2 := le_norm_uniformShiftProd χ⁻¹ 0 hz1
      simp only [mul_zero, pow_zero, one_pow] at hQ1 hQ2
      have hE : Real.exp (heckeLogDiscriminantConductor χ * (2 * K + 2)) ≤ E :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA (by positivity))
      change ‖uniformMultiplier χ (K + 1) z‖ = _ at h
      rw [h]
      have hi1 := inv_le_one_of_one_le₀ hQ1
      have hi2 := inv_le_one_of_one_le₀ hQ2
      calc Real.exp (heckeLogDiscriminantConductor χ * (2 * K + 2)) *
            (‖finiteHeckeL χ ⟨1 - z, hw⟩‖ * ‖finiteHeckeL χ⁻¹ ⟨1 - z, hw⟩‖) *
            (‖uniformShiftProd χ 0 (z + 2 * ((K + 1 : ℕ) : ℂ))‖⁻¹ *
              ‖uniformShiftProd χ⁻¹ 0 (z + 2 * ((K + 1 : ℕ) : ℂ))‖⁻¹)
          ≤ E * (D * D) * (1 * 1) := by
            refine mul_le_mul (mul_le_mul hE (mul_le_mul hL1 hL2 (norm_nonneg _) hD0.le)
              (by positivity) (Real.exp_pos _).le)
              (mul_le_mul hi1 hi2 (by positivity) zero_le_one) (by positivity) (by positivity)
        _ ≤ C := by
            have h1 : (1 : ℝ) ≤ (ε * ε)⁻¹ :=
              (one_le_inv₀ (mul_pos hε hε)).mpr (by nlinarith)
            have h2 : 0 ≤ E * (D * D) := by positivity
            have h3 : 0 ≤ D * D := by positivity
            calc E * (D * D) * (1 * 1) ≤ (E + 1) * (D * D) * 1 := by nlinarith
              _ ≤ (E + 1) * (D * D) * (ε * ε)⁻¹ :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
    have hright : ∀ z : ℂ, z.re = R → ‖uniformMultiplier χ (K + 1) z‖ ≤ C := by
      intro z hz
      have hw : 1 < z.re := by linarith
      have hre : (3 / 2 : ℝ) ≤ z.re := by linarith
      have h := uniformMultiplier_eq_of_one_lt_re χ (K + 1) ⟨z, hw⟩
      change uniformMultiplier χ (K + 1) z = _ at h
      have hL1 := (hLD χ ⟨z, hw⟩ hre).2
      have hL2 := (hLD χ⁻¹ ⟨z, hw⟩ hre).2
      have hQ1 := le_norm_uniformShiftProd χ (K + 1) (s := z) (by linarith)
      have hQ2 := le_norm_uniformShiftProd χ⁻¹ (K + 1) (s := z) (by linarith)
      rw [h, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
      have hi1 : ‖uniformShiftProd χ (K + 1) z‖⁻¹ ≤ ε⁻¹ := inv_anti₀ hε hQ1
      have hi2 : ‖uniformShiftProd χ⁻¹ (K + 1) z‖⁻¹ ≤ ε⁻¹ := inv_anti₀ hε hQ2
      calc ‖finiteHeckeL χ ⟨z, hw⟩‖ * ‖finiteHeckeL χ⁻¹ ⟨z, hw⟩‖ *
            (‖uniformShiftProd χ (K + 1) z‖⁻¹ * ‖uniformShiftProd χ⁻¹ (K + 1) z‖⁻¹)
          ≤ D * D * (ε⁻¹ * ε⁻¹) :=
            mul_le_mul (mul_le_mul hL1 hL2 (norm_nonneg _) hD0.le)
              (mul_le_mul hi1 hi2 (by positivity) (by positivity)) (by positivity)
              (by positivity)
        _ = 1 * (D * D) * (ε * ε)⁻¹ := by rw [mul_inv]; ring
        _ ≤ C := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
              (by positivity)
            linarith [Real.exp_pos (A * (2 * K + 2))]
    exact uniform_norm_le_of_strip hd hab hM hleft hright hs1 hs2
  · -- Lower bounds, from a bound for the products of the shift polynomials.
    have hY := norm_uniformGammaShift_le χ hX harch
    have hY' (v : InfinitePlace F) : ‖uniformGammaShift χ⁻¹ v‖ ≤ 2 * X := by
      rw [uniformGammaShift_inv, Complex.norm_conj]
      exact hY v
    -- One bound `W s` for all the products of shift polynomials that occur.
    let W (s : ℂ) : ℝ := ((‖s‖ + 2 * X + 2 * ((K + 1 : ℕ) : ℝ)) ^ (2 * (K + 1))) ^ N
    have hWpos (s : ℂ) : 0 < W s := by positivity
    have hWle (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (hψ : ∀ v, ‖uniformGammaShift ψ v‖ ≤ 2 * X) (m : ℕ) (hm : m ≤ K + 1) (s z : ℂ)
        (hz : ‖z‖ + 2 * (m : ℝ) ≤ ‖s‖ + 2 * ((K + 1 : ℕ) : ℝ)) :
        ‖uniformShiftProd ψ m z‖ ≤ W s := by
      refine (norm_uniformShiftProd_le ψ m z hψ).trans (pow_le_pow_left₀ (by positivity) ?_ _)
      have hbase : (1 : ℝ) ≤ ‖s‖ + 2 * X + 2 * ((K + 1 : ℕ) : ℝ) := by
        push_cast
        linarith [norm_nonneg s, Nat.cast_nonneg (α := ℝ) K]
      calc (‖z‖ + 2 * X + 2 * (m : ℝ)) ^ (2 * m)
          ≤ (‖s‖ + 2 * X + 2 * ((K + 1 : ℕ) : ℝ)) ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (‖s‖ + 2 * X + 2 * ((K + 1 : ℕ) : ℝ)) ^ (2 * (K + 1)) :=
            pow_le_pow_right₀ hbase (by omega)
    -- The final comparison of constants.
    have hfinal (s : ℂ) (h : c₀ * c₀ * ((W s)⁻¹ * (W s)⁻¹) ≤ ‖uniformMultiplier χ (K + 1) s‖) :
        c₀ * c₀ / B ^ n / (‖s‖ + X) ^ n ≤ ‖uniformMultiplier χ (K + 1) s‖ := by
      have ht : 0 < ‖s‖ + X := by linarith [norm_nonneg s]
      have hWB : W s ≤ ((B * (‖s‖ + X)) ^ (2 * (K + 1))) ^ N := by
        refine pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _) _
        have h1 : 2 * ((K + 1 : ℕ) : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) * X :=
          le_mul_of_one_le_right (by positivity) hX
        have h2 : 0 ≤ 2 * ((K + 1 : ℕ) : ℝ) * ‖s‖ := by positivity
        have h3 : 0 ≤ ‖s‖ := norm_nonneg s
        change ‖s‖ + 2 * X + 2 * ((K + 1 : ℕ) : ℝ) ≤ (2 * ((K + 1 : ℕ) : ℝ) + 2) * (‖s‖ + X)
        nlinarith
      have hpow : ((B * (‖s‖ + X)) ^ (2 * (K + 1))) ^ N *
          ((B * (‖s‖ + X)) ^ (2 * (K + 1))) ^ N =
          B ^ (2 * (K + 1) * (N * 2)) * (‖s‖ + X) ^ (2 * (K + 1) * (N * 2)) := by
        rw [← sq, ← pow_mul, ← pow_mul, mul_pow]
      have hWW : W s * W s ≤ B ^ n * (‖s‖ + X) ^ n :=
        (mul_le_mul hWB hWB (hWpos s).le (by positivity)).trans_eq hpow
      have hinv := mul_inv (W s) (W s)
      calc c₀ * c₀ / B ^ n / (‖s‖ + X) ^ n
          = c₀ * c₀ * (B ^ n * (‖s‖ + X) ^ n)⁻¹ := by rw [div_div, div_eq_mul_inv]
        _ ≤ c₀ * c₀ * (W s * W s)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (mul_pos (hWpos s) (hWpos s)) hWW)
              (by positivity)
        _ = c₀ * c₀ * ((W s)⁻¹ * (W s)⁻¹) := by rw [hinv]
        _ ≤ ‖uniformMultiplier χ (K + 1) s‖ := h
    refine ⟨fun s hs ↦ hfinal s ?_, fun k hk s hs ↦ hfinal s ?_⟩
    · -- To the right of `3/2`.
      have hw : 1 < s.re := by linarith
      have h := uniformMultiplier_eq_of_one_lt_re χ (K + 1) ⟨s, hw⟩
      change uniformMultiplier χ (K + 1) s = _ at h
      have hL1 := (hLD χ ⟨s, hw⟩ hs).1
      have hL2 := (hLD χ⁻¹ ⟨s, hw⟩ hs).1
      have hQ1 := hWle χ hY (K + 1) le_rfl s s le_rfl
      have hQ2 := hWle χ⁻¹ hY' (K + 1) le_rfl s s le_rfl
      have hn1 : uniformShiftProd χ (K + 1) s ≠ 0 := by
        have := le_norm_uniformShiftProd χ (K + 1) (s := s) (by linarith)
        exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) this)
      have hn2 : uniformShiftProd χ⁻¹ (K + 1) s ≠ 0 := by
        have := le_norm_uniformShiftProd χ⁻¹ (K + 1) (s := s) (by linarith)
        exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) this)
      rw [h, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
      exact mul_le_mul (mul_le_mul hL1 hL2 hc₀.le (norm_nonneg _))
        (mul_le_mul (inv_anti₀ (norm_pos_iff.mpr hn1) hQ1) (inv_anti₀ (norm_pos_iff.mpr hn2) hQ2)
          (by positivity) (by positivity)) (by positivity) (by positivity)
    · -- On the line `Re s = -k - 1/2`.
      have hw : 1 < (1 - s).re := by
        rw [Complex.sub_re, Complex.one_re, hs]
        linarith [Nat.cast_nonneg (α := ℝ) k]
      have hre : (3 / 2 : ℝ) ≤ (1 - s).re := by
        rw [Complex.sub_re, Complex.one_re, hs]
        linarith [Nat.cast_nonneg (α := ℝ) k]
      have hKk : k + 1 + (K - k) = K + 1 := by omega
      have h := norm_uniformMultiplier_of_re_eq χ k (K - k) hs ⟨1 - s, hw⟩ rfl
      rw [hKk] at h
      have hL1 := (hLD χ ⟨1 - s, hw⟩ hre).1
      have hL2 := (hLD χ⁻¹ ⟨1 - s, hw⟩ hre).1
      have hz1 : 1 ≤ (s + 2 * ((k + 1 : ℕ) : ℂ)).re := by
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, hs]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      have hnorm : ‖s + 2 * ((k + 1 : ℕ) : ℂ)‖ + 2 * ((K - k : ℕ) : ℝ) ≤
          ‖s‖ + 2 * ((K + 1 : ℕ) : ℝ) := by
        have h1 : ‖(2 : ℂ) * ((k + 1 : ℕ) : ℂ)‖ = 2 * ((k + 1 : ℕ) : ℝ) := by
          rw [norm_mul, Complex.norm_two, Complex.norm_natCast]
        have h2 := norm_add_le s (2 * ((k + 1 : ℕ) : ℂ))
        rw [h1] at h2
        have h3 : ((k + 1 : ℕ) : ℝ) + ((K - k : ℕ) : ℝ) = ((K + 1 : ℕ) : ℝ) := by
          exact_mod_cast hKk
        linarith
      have hQ1 := hWle χ hY (K - k) (by omega) s _ hnorm
      have hQ2 := hWle χ⁻¹ hY' (K - k) (by omega) s _ hnorm
      have hn1 : 0 < ‖uniformShiftProd χ (K - k) (s + 2 * ((k + 1 : ℕ) : ℂ))‖ :=
        lt_of_lt_of_le (by positivity) (le_norm_uniformShiftProd χ (K - k) hz1)
      have hn2 : 0 < ‖uniformShiftProd χ⁻¹ (K - k) (s + 2 * ((k + 1 : ℕ) : ℂ))‖ :=
        lt_of_lt_of_le (by positivity) (le_norm_uniformShiftProd χ⁻¹ (K - k) hz1)
      have hE : (1 : ℝ) ≤ Real.exp (heckeLogDiscriminantConductor χ * (2 * k + 2)) :=
        Real.one_le_exp (mul_nonneg ha (by positivity))
      rw [h]
      calc c₀ * c₀ * ((W s)⁻¹ * (W s)⁻¹) = 1 * (c₀ * c₀) * ((W s)⁻¹ * (W s)⁻¹) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul hE (mul_le_mul hL1 hL2 hc₀.le (norm_nonneg _))
            (by positivity) (Real.exp_pos _).le)
            (mul_le_mul (inv_anti₀ hn1 hQ1) (inv_anti₀ hn2 hQ2) (by positivity) (by positivity))
            (by positivity) (by positivity)

open Classical in
/-- Paper: Theorem 10.3.2.1(1), pp. 453–455, with Proposition 3.2.1.3, p. 123. A multiplier for
the zeros of a Hecke L-function with every constant uniform in the character.
Fix `K`, a right edge `R ≥ 3/2` and a bound `A` for the logarithm of the discriminant–conductor
product. There are a constant `c > 0` and an exponent `n`, depending only on the field and on
`K`, `R`, `A`, such that every unitary character `χ` of the idele classes that is not trivial on
the norm-one classes and has `heckeLogDiscriminantConductor χ ≤ A` has an entire function `ϑ`
with:
* `ϑ` vanishes at every point to at least the order of the zero of the completed L-function of
  `χ` there;
* `‖ϑ s‖ ≤ 1` on the strip `-K - 1/2 ≤ Re s ≤ R`;
* if `X ≥ 1` bounds the archimedean parameters of `χ`, then `c / (‖s‖ + X) ^ n ≤ ‖ϑ s‖` for
  `Re s ≥ 3/2` and on each line `Re s = -k - 1/2` with `k ≤ K`.
The function is `Λ(s, χ) Λ(s, χ⁻¹) / (γ(s + 2K + 2, χ) γ(s + 2K + 2, χ⁻¹))` divided by a
constant.
Reconstruction: The paper does not state this. It is the uniform form of the growth and lower
bounds that the cluster route to Theorem 10.3.2.1 needs
(`spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData` of `Sec3_Clusters`): the
function `ϑ ω` of that theorem for `ω ≠ 1`, when the basepoint choice is trivial on the image of
a norm section. The bounds are for `ϑ`, not for the L-function. The estimates follow the
private lemmas
`idelicExplicitFormula_summable_spectral_characters_euler`, `…_gamma`, `…_strip`, `…_discs` of
`AppB_AnalyticNT/Sec4b`, which treat the strip `-1/2 ≤ Re s ≤ 5`; see H. Rademacher, *On the
Phragmén–Lindelöf theorem and some applications*, for bounds of this kind with explicit
dependence on the character. -/
theorem exists_uniform_heckeMultiplier (F : Type*) [Field F] [NumberField F] (K : ℕ) {R : ℝ}
    (hR : 3 / 2 ≤ R) (A : ℝ) :
    ∃ (c : ℝ) (n : ℕ), 0 < c ∧ ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      heckeLogDiscriminantConductor χ ≤ A →
      ∃ ϑ : ℂ → ℂ, Differentiable ℂ ϑ ∧
        (∀ z : ℂ, (((meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat : ℕ) : ℕ∞) ≤
          analyticOrderAt ϑ z) ∧
        (∀ s : ℂ, -(K : ℝ) - 1 / 2 ≤ s.re → s.re ≤ R → ‖ϑ s‖ ≤ 1) ∧
        ∀ X : ℝ, 1 ≤ X →
          (∀ w : InfinitePlace F, if hw : w.IsReal then
              ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ X
            else
              let p := (complexHeckeCharacter_parameters χ w
                (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
              ‖p.1‖ ≤ X ∧ (p.2.natAbs : ℝ) ≤ X) →
          (∀ s : ℂ, 3 / 2 ≤ s.re → c / (‖s‖ + X) ^ n ≤ ‖ϑ s‖) ∧
          (∀ k : ℕ, k ≤ K → ∀ s : ℂ, s.re = -(k : ℝ) - 1 / 2 →
            c / (‖s‖ + X) ^ n ≤ ‖ϑ s‖) := by
  obtain ⟨C, c, n, hC, hc, h⟩ := uniformMultiplier_bounds F K hR A
  refine ⟨c / C, n, div_pos hc hC, fun χ hχ hA ↦ ?_⟩
  obtain ⟨hup, hlow⟩ := h χ hχ hA
  have hd := differentiable_uniformMultiplier hχ (K + 1)
  have hnorm (s : ℂ) : ‖((C⁻¹ : ℝ) : ℂ) * uniformMultiplier χ (K + 1) s‖ =
      C⁻¹ * ‖uniformMultiplier χ (K + 1) s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hC.le)]
  have hscale (s : ℂ) (X : ℝ) (hs : c / (‖s‖ + X) ^ n ≤ ‖uniformMultiplier χ (K + 1) s‖) :
      c / C / (‖s‖ + X) ^ n ≤ ‖((C⁻¹ : ℝ) : ℂ) * uniformMultiplier χ (K + 1) s‖ := by
    rw [hnorm, div_right_comm, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hC.le)
  refine ⟨fun s ↦ ((C⁻¹ : ℝ) : ℂ) * uniformMultiplier χ (K + 1) s, hd.const_mul _, fun z ↦ ?_,
    fun s hs1 hs2 ↦ ?_, fun X hX harch ↦ ⟨fun s hs ↦ hscale s X ((hlow X hX harch).1 s hs),
      fun k hk s hs ↦ hscale s X ((hlow X hX harch).2 k hk s hs)⟩⟩
  · -- The order is that of the multiplier.
    have hmul := analyticOrderAt_mul (f := fun _ : ℂ ↦ ((C⁻¹ : ℝ) : ℂ))
      (g := uniformMultiplier χ (K + 1)) (z₀ := z) analyticAt_const (hd.analyticAt z)
    have hconst : analyticOrderAt (fun _ : ℂ ↦ ((C⁻¹ : ℝ) : ℂ)) z = 0 :=
      (analyticAt_const).analyticOrderAt_eq_zero.mpr
        (Complex.ofReal_ne_zero.mpr (inv_ne_zero hC.ne'))
    rw [hconst, zero_add] at hmul
    have hfun : (fun s ↦ ((C⁻¹ : ℝ) : ℂ) * uniformMultiplier χ (K + 1) s) =
        (fun _ : ℂ ↦ ((C⁻¹ : ℝ) : ℂ)) * uniformMultiplier χ (K + 1) := rfl
    rw [hfun, hmul]
    exact uniformMultiplier_order hχ (K + 1) z
  · rw [hnorm, inv_mul_le_iff₀ hC, mul_one]
    exact hup s hs1 hs2

/-- Jensen's inequality for an entire comparison function that is bounded on a vertical strip
and bounded below, to the right of `3/2`, by `c / (‖s‖ + X) ^ n`: any finite set of points in
the closed disc of radius `ρ` around `2 + it` carries at most a constant times
`log (X + |t| + 2)` zeros of a function whose orders the comparison function dominates. -/
private theorem uniform_closedBall_zeros_le_log {Λ θ : ℂ → ℂ} (hΛ : MeromorphicOn Λ univ)
    (hθ : Differentiable ℂ θ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt θ z) {ρ C₀ c X : ℝ} {n : ℕ}
    (hρ : 0 < ρ) (hC₀ : 0 < C₀) (hc : 0 < c) (hX : 1 ≤ X)
    (hup : ∀ s : ℂ, 1 - ρ ≤ s.re → s.re ≤ ρ + 3 → ‖θ s‖ ≤ C₀)
    (hlow : ∀ s : ℂ, 3 / 2 ≤ s.re → c / (‖s‖ + X) ^ n ≤ ‖θ s‖) (t : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ Metric.closedBall (⟨2, t⟩ : ℂ) ρ) :
    ∑ z ∈ S, (((meromorphicOrderAt Λ z).untop₀.toNat : ℕ) : ℝ) ≤
      (|Real.log C₀ - Real.log c| / Real.log 2 + n) / Real.log ((ρ + 1) / ρ) *
        Real.log (X + |t| + 2) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hratio : 1 < (ρ + 1) / ρ := by
    rw [lt_div_iff₀ hρ]
    linarith
  have hlogr : 0 < Real.log ((ρ + 1) / ρ) := Real.log_pos hratio
  -- The lower bound at the centre.
  have hcentre_re : (3 / 2 : ℝ) ≤ (⟨2, t⟩ : ℂ).re := by norm_num
  have hcentre_norm : ‖(⟨2, t⟩ : ℂ)‖ ≤ 2 + |t| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (⟨2, t⟩ : ℂ)
    change ‖(⟨2, t⟩ : ℂ)‖ ≤ |(2 : ℝ)| + |t| at h1
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
  have hbase : 0 < ‖(⟨2, t⟩ : ℂ)‖ + X := by linarith [norm_nonneg (⟨2, t⟩ : ℂ)]
  have hδ : 0 < c / (‖(⟨2, t⟩ : ℂ)‖ + X) ^ n := by positivity
  have hcentre := hlow ⟨2, t⟩ hcentre_re
  have hne : θ ⟨2, t⟩ ≠ 0 := norm_pos_iff.mp (hδ.trans_le hcentre)
  -- The bound for the quotient on the larger disc.
  have hB : ∀ z ∈ Metric.closedBall (⟨2, t⟩ : ℂ) (ρ + 1),
      ‖θ z / θ ⟨2, t⟩‖ ≤ C₀ / (c / (‖(⟨2, t⟩ : ℂ)‖ + X) ^ n) := by
    intro z hz
    have hdist : ‖z - (⟨2, t⟩ : ℂ)‖ ≤ ρ + 1 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzr := (Complex.abs_re_le_norm _).trans hdist
    change |z.re - 2| ≤ ρ + 1 at hzr
    have h1 := (abs_le.mp hzr).1
    have h2 := (abs_le.mp hzr).2
    rw [norm_div]
    exact div_le_div₀ hC₀.le (hup z (by linarith) (by linarith)) hδ hcentre
  -- Jensen's inequality on the points where the function vanishes.
  have hJ := sum_divisor_le_log_of_disk_bound hΛ hcmp hρ (by linarith : ρ < ρ + 1)
    (fun z _ ↦ hθ.analyticAt z) hne hB
    (S.filter fun z ↦ 0 < MeromorphicOn.divisor Λ univ z)
    (fun z hz ↦ hS z (Finset.mem_filter.mp hz).1)
  rw [Finset.sum_filter] at hJ
  have htoNat (z : ℂ) : (((meromorphicOrderAt Λ z).untop₀.toNat : ℕ) : ℝ) =
      if 0 < MeromorphicOn.divisor Λ univ z then (MeromorphicOn.divisor Λ univ z : ℝ) else 0 := by
    rw [MeromorphicOn.divisor_apply hΛ (mem_univ z)]
    split_ifs with h0
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg h0.le]
    · rw [Int.toNat_eq_zero.mpr (not_lt.mp h0), Nat.cast_zero]
  rw [Finset.sum_congr rfl fun z _ ↦ htoNat z]
  refine hJ.trans ?_
  -- The logarithm of the bound is at most a constant times `log (X + |t| + 2)`.
  have hT : 2 ≤ X + |t| + 2 := by linarith [abs_nonneg t]
  have hlogT : Real.log 2 ≤ Real.log (X + |t| + 2) := Real.log_le_log two_pos hT
  have hlogbase : Real.log (‖(⟨2, t⟩ : ℂ)‖ + X) ≤ Real.log (X + |t| + 2) :=
    Real.log_le_log hbase (by linarith)
  have hlogB : Real.log (C₀ / (c / (‖(⟨2, t⟩ : ℂ)‖ + X) ^ n)) =
      Real.log C₀ - Real.log c + n * Real.log (‖(⟨2, t⟩ : ℂ)‖ + X) := by
    rw [Real.log_div hC₀.ne' hδ.ne', Real.log_div hc.ne' (pow_pos hbase n).ne', Real.log_pow]
    ring
  have hconst : Real.log C₀ - Real.log c ≤
      |Real.log C₀ - Real.log c| / Real.log 2 * Real.log (X + |t| + 2) := by
    refine (le_abs_self _).trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
  rw [hlogB, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hlogr.le
  have h3 : (n : ℝ) * Real.log (‖(⟨2, t⟩ : ℂ)‖ + X) ≤ n * Real.log (X + |t| + 2) :=
    mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg n)
  linarith

open Classical in
/-- Paper: Theorem 10.3.2.1, the estimate used after (10.3.2.11), p. 455, with a constant that
is uniform in the character. Fix a radius `ρ` and a bound `A` for the logarithm of the
discriminant–conductor product. There is a constant `C` such that, for every unitary character
`χ` of the idele classes that is not trivial on the norm-one classes and has
`heckeLogDiscriminantConductor χ ≤ A`, for every bound `X ≥ 1` for its archimedean parameters
and for every real `t`, any finite set of points in the closed disc of radius `ρ` around `2 + it`
carries at most `C * log (X + |t| + 2)` zeros of the completed L-function of `χ`, counted with
multiplicity.
Reconstruction: The paper does not state this. It is the classical bound `N(T + 1, χ) - N(T, χ) =
O(log (q(χ) (|T| + 2)))` (see Iwaniec–Kowalski, *Analytic Number Theory*), with
`q(χ)` replaced by the bound `X` and a bounded finite conductor, as the cluster route to
Theorem 10.3.2.1 needs it. It is proved by Jensen's inequality
(`sum_divisor_le_log_of_disk_bound`) for the multiplier of `exists_uniform_heckeMultiplier`. The
private lemma `idelicExplicitFormula_summable_spectral_characters_window` of
`AppB_AnalyticNT/Sec4b` has the same count with `B * X ^ 2` in place of the logarithm. -/
theorem continuedCompletedHeckeL_closedBall_zeros_le_log_uniform (F : Type*) [Field F]
    [NumberField F] {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      heckeLogDiscriminantConductor χ ≤ A →
      ∀ X : ℝ, 1 ≤ X →
        (∀ w : InfinitePlace F, if hw : w.IsReal then
            ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ X
          else
            let p := (complexHeckeCharacter_parameters χ w
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
            ‖p.1‖ ≤ X ∧ (p.2.natAbs : ℝ) ≤ X) →
        ∀ (t : ℝ) (S : Finset ℂ), (∀ z ∈ S, z ∈ Metric.closedBall (⟨2, t⟩ : ℂ) ρ) →
          ∑ z ∈ S, (((meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat : ℕ) : ℝ) ≤
            C * Real.log (X + |t| + 2) := by
  let K := ⌈ρ⌉₊
  have hK : ρ ≤ K := Nat.le_ceil ρ
  obtain ⟨C₀, c, n, hC₀, hc, h⟩ := uniformMultiplier_bounds F K (R := ρ + 3) (by linarith) A
  have hratio : 1 < (ρ + 1) / ρ := by
    rw [lt_div_iff₀ hρ]
    linarith
  have hlogr : 0 < Real.log ((ρ + 1) / ρ) := Real.log_pos hratio
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(|Real.log C₀ - Real.log c| / Real.log 2 + n) / Real.log ((ρ + 1) / ρ),
    by positivity, fun χ hχ hA X hX harch t S hS ↦ ?_⟩
  obtain ⟨hup, hlow⟩ := h χ hχ hA
  exact uniform_closedBall_zeros_le_log (continuedCompletedHeckeL_spec χ).1.meromorphicOn
    (differentiable_uniformMultiplier hχ (K + 1)) (uniformMultiplier_meromorphicOrder hχ (K + 1))
    hρ hC₀ hc hX (fun s h1 h2 ↦ hup s (by linarith) h2) (hlow X hX harch).1 t S hS

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455, with Proposition 3.2.1.3(2), p. 123. The multiplier
of `exists_uniform_heckeMultiplier` for the trivial character, whose completed L-function has
simple poles at `0` and `1`. There are `c > 0`, `n` and an entire function `ϑ` which vanishes at
every point to at least the order of the zero of the completed L-function of the trivial
character there, satisfies `‖ϑ s‖ ≤ 1` on the strip `-K - 1/2 ≤ Re s ≤ R`, and satisfies
`c / (‖s‖ + 1) ^ n ≤ ‖ϑ s‖` for `Re s ≥ 3/2` and on each line `Re s = -k - 1/2` with `k ≤ K`.
The function is `(s (s - 1) Λ(s, 1))² / γ(s + 2K + 6, 1)²` divided by a constant.
Reconstruction: The paper does not state this. It is the function `ϑ ω` of the cluster route to
Theorem 10.3.2.1 for the component `ω = 1`, in the same shape as for the other components. -/
theorem exists_trivial_heckeMultiplier (F : Type*) [Field F] [NumberField F] (K : ℕ) {R : ℝ}
    (hR : 3 / 2 ≤ R) :
    ∃ (c : ℝ) (n : ℕ) (ϑ : ℂ → ℂ), 0 < c ∧ Differentiable ℂ ϑ ∧
      (∀ z : ℂ, (((meromorphicOrderAt (continuedCompletedHeckeL
        (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))) z).untop₀.toNat : ℕ) : ℕ∞) ≤
          analyticOrderAt ϑ z) ∧
      (∀ s : ℂ, -(K : ℝ) - 1 / 2 ≤ s.re → s.re ≤ R → ‖ϑ s‖ ≤ 1) ∧
      (∀ s : ℂ, 3 / 2 ≤ s.re → c / (‖s‖ + 1) ^ n ≤ ‖ϑ s‖) ∧
      (∀ k : ℕ, k ≤ K → ∀ s : ℂ, s.re = -(k : ℝ) - 1 / 2 → c / (‖s‖ + 1) ^ n ≤ ‖ϑ s‖) := by
  obtain ⟨E, hEd, hEeq⟩ := exists_trivial_entire F
  obtain ⟨C, c, n, hC, hc, hup, hr, hl⟩ := trivialMultiplier_bounds F K hR hEd hEeq
  have hd := differentiable_trivialMultiplier (F := F) hEd (K + 3)
  have hnorm (s : ℂ) : ‖((C⁻¹ : ℝ) : ℂ) * trivialMultiplier F E (K + 3) s‖ =
      C⁻¹ * ‖trivialMultiplier F E (K + 3) s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hC.le)]
  have hscale (s : ℂ) (hs : c / (‖s‖ + 1) ^ n ≤ ‖trivialMultiplier F E (K + 3) s‖) :
      c / C / (‖s‖ + 1) ^ n ≤ ‖((C⁻¹ : ℝ) : ℂ) * trivialMultiplier F E (K + 3) s‖ := by
    rw [hnorm, div_right_comm, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hC.le)
  refine ⟨c / C, n, fun s ↦ ((C⁻¹ : ℝ) : ℂ) * trivialMultiplier F E (K + 3) s, div_pos hc hC,
    hd.const_mul _, fun z ↦ ?_, fun s hs1 hs2 ↦ ?_, fun s hs ↦ hscale s (hr s hs),
    fun k hk s hs ↦ hscale s (hl k hk s hs)⟩
  · have hmul := analyticOrderAt_mul (f := fun _ : ℂ ↦ ((C⁻¹ : ℝ) : ℂ))
      (g := trivialMultiplier F E (K + 3)) (z₀ := z) analyticAt_const (hd.analyticAt z)
    have hconst : analyticOrderAt (fun _ : ℂ ↦ ((C⁻¹ : ℝ) : ℂ)) z = 0 :=
      (analyticAt_const).analyticOrderAt_eq_zero.mpr
        (Complex.ofReal_ne_zero.mpr (inv_ne_zero hC.ne'))
    rw [hconst, zero_add] at hmul
    have hfun : (fun s ↦ ((C⁻¹ : ℝ) : ℂ) * trivialMultiplier F E (K + 3) s) =
        (fun _ : ℂ ↦ ((C⁻¹ : ℝ) : ℂ)) * trivialMultiplier F E (K + 3) := rfl
    rw [hfun, hmul]
    exact toNat_untop₀_le_analyticOrderAt (hd.analyticAt z)
      (trivialMultiplier_meromorphicOrder hEd hEeq (K + 3) z)
  · rw [hnorm, inv_mul_le_iff₀ hC, mul_one]
    exact hup s hs1 hs2

/-- Paper: Theorem 10.3.2.1, the estimate used after (10.3.2.11), p. 455, for the trivial
character. For every radius `ρ` there is a constant `C` such that, for every real `t`, any
finite set of points in the closed disc of radius `ρ` around `2 + it` carries at most
`C * log (1 + |t| + 2)` zeros of the completed L-function of the trivial character, counted
with multiplicity. The two poles count zero.
Reconstruction: The paper does not state this. It is the classical bound for the zeros of the
Dedekind zeta function in a window, in the shape of
`continuedCompletedHeckeL_closedBall_zeros_le_log_uniform`. -/
theorem continuedCompletedHeckeL_one_closedBall_zeros_le_log (F : Type*) [Field F]
    [NumberField F] {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (S : Finset ℂ),
      (∀ z ∈ S, z ∈ Metric.closedBall (⟨2, t⟩ : ℂ) ρ) →
      ∑ z ∈ S, (((meromorphicOrderAt (continuedCompletedHeckeL
        (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))) z).untop₀.toNat : ℕ) : ℝ) ≤
        C * Real.log (1 + |t| + 2) := by
  let K := ⌈ρ⌉₊
  have hK : ρ ≤ K := Nat.le_ceil ρ
  obtain ⟨E, hEd, hEeq⟩ := exists_trivial_entire F
  obtain ⟨C₀, c, n, hC₀, hc, hup, hr, -⟩ :=
    trivialMultiplier_bounds F K (R := ρ + 3) (by linarith) hEd hEeq
  have hratio : 1 < (ρ + 1) / ρ := by
    rw [lt_div_iff₀ hρ]
    linarith
  have hlogr : 0 < Real.log ((ρ + 1) / ρ) := Real.log_pos hratio
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(|Real.log C₀ - Real.log c| / Real.log 2 + n) / Real.log ((ρ + 1) / ρ),
    by positivity, fun t S hS ↦ ?_⟩
  exact uniform_closedBall_zeros_le_log
    (continuedCompletedHeckeL_spec (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))).1.meromorphicOn
    (differentiable_trivialMultiplier (F := F) hEd (K + 3))
    (trivialMultiplier_meromorphicOrder hEd hEeq (K + 3)) hρ hC₀ hc le_rfl
    (fun s h1 h2 ↦ hup s (by linarith) h2) hr t S hS

/-- A multiplier in the variable `s`, bounded by one on a strip and bounded below on the lines
`Re s = -k - 1/2` and to the right of `3/2`, gives a multiplier in the variable `u = s - a` with
the same properties on `|Re u| ≤ W`, on `Re u = -(a + k + 1/2)` and for `Re u ≥ a + k + 1/2`. -/
private theorem heckeMultiplier_chart {Λ ϑ : ℂ → ℂ} (P : ℝ → Prop) (a : ℝ) {k K : ℕ}
    {W R c : ℝ} {n : ℕ} (hkK : k ≤ K) (hk : 3 / 2 ≤ 2 * a + k + 1 / 2)
    (hW1 : -(K : ℝ) - 1 / 2 ≤ a - |W|) (hW2 : a + |W| ≤ R) (hc : 0 < c)
    (hd : Differentiable ℂ ϑ)
    (hord : ∀ z : ℂ, (((meromorphicOrderAt Λ z).untop₀.toNat : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ z)
    (hup : ∀ s : ℂ, -(K : ℝ) - 1 / 2 ≤ s.re → s.re ≤ R → ‖ϑ s‖ ≤ 1)
    (hlow : ∀ Y : ℝ, 1 ≤ Y → P Y →
      (∀ s : ℂ, 3 / 2 ≤ s.re → c / (‖s‖ + Y) ^ n ≤ ‖ϑ s‖) ∧
      (∀ k : ℕ, k ≤ K → ∀ s : ℂ, s.re = -(k : ℝ) - 1 / 2 → c / (‖s‖ + Y) ^ n ≤ ‖ϑ s‖)) :
    Differentiable ℂ (fun u : ℂ ↦ ϑ ((a : ℂ) + u)) ∧
      (∀ u : ℂ, (((meromorphicOrderAt Λ ((a : ℂ) + u)).untop₀.toNat : ℕ) : ℕ∞) ≤
        analyticOrderAt (fun u : ℂ ↦ ϑ ((a : ℂ) + u)) u) ∧
      (∀ u : ℂ, |u.re| ≤ W → ‖ϑ ((a : ℂ) + u)‖ ≤ 1) ∧
      ∀ Y : ℝ, 1 ≤ Y → P Y →
        (∀ u : ℂ, a + k + 1 / 2 ≤ u.re →
          c / (1 + |a|) ^ n / (‖u‖ + Y) ^ n ≤ ‖ϑ ((a : ℂ) + u)‖) ∧
        (∀ u : ℂ, u.re = -(a + k + 1 / 2) →
          c / (1 + |a|) ^ n / (‖u‖ + Y) ^ n ≤ ‖ϑ ((a : ℂ) + u)‖) := by
  have hshift : Differentiable ℂ (fun u : ℂ ↦ (a : ℂ) + u) := differentiable_id.const_add _
  have hscale (u : ℂ) (Y : ℝ) (hY : 1 ≤ Y)
      (hu : c / (‖(a : ℂ) + u‖ + Y) ^ n ≤ ‖ϑ ((a : ℂ) + u)‖) :
      c / (1 + |a|) ^ n / (‖u‖ + Y) ^ n ≤ ‖ϑ ((a : ℂ) + u)‖ := by
    refine le_trans ?_ hu
    have h0 : 0 < ‖(a : ℂ) + u‖ + Y := by linarith [norm_nonneg ((a : ℂ) + u)]
    have h1 : ‖(a : ℂ) + u‖ + Y ≤ (1 + |a|) * (‖u‖ + Y) := by
      have h2 := norm_add_le (a : ℂ) u
      rw [Complex.norm_real, Real.norm_eq_abs] at h2
      nlinarith [abs_nonneg a, norm_nonneg u, mul_nonneg (abs_nonneg a) (norm_nonneg u)]
    rw [div_div, ← mul_pow]
    exact div_le_div_of_nonneg_left hc.le (pow_pos h0 n) (pow_le_pow_left₀ h0.le h1 n)
  refine ⟨hd.comp hshift, fun u ↦ ?_, fun u hu ↦ ?_,
    fun Y hY hP ↦ ⟨fun u hu ↦ hscale u Y hY ((hlow Y hY hP).1 _ ?_),
      fun u hu ↦ hscale u Y hY ((hlow Y hY hP).2 k hkK _ ?_)⟩⟩
  · have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := ϑ) (g := fun u : ℂ ↦ (a : ℂ) + u)
      (z₀ := u) (hshift.analyticAt u) (by
        have hderiv : deriv (fun u : ℂ ↦ (a : ℂ) + u) u = 1 := by
          simp
        rw [hderiv]
        exact one_ne_zero)
    change _ ≤ analyticOrderAt (ϑ ∘ fun u : ℂ ↦ (a : ℂ) + u) u
    rw [hcomp]
    exact hord _
  · have h1 := abs_le.mp hu
    refine hup _ ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith [neg_abs_le W, le_abs_self W]
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith [le_abs_self W]
  · simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  · simp only [Complex.add_re, Complex.ofReal_re, hu]
    ring

open Classical in
/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The multiplier of `exists_uniform_heckeMultiplier`
in the variable `u = s - a`, with the left side of the rectangles on a named line: for a natural
number `k` such that `a + (a + k + 1/2) ≥ 3/2`, the half-width is `X = a + k + 1/2`, so that
`Re u = -X` is the line `Re s = -k - 1/2` and `Re u = X` lies to the right of `3/2`. For every
width `W` and every bound `A` for the logarithm of the discriminant–conductor product there are
`c > 0` and `n` such that every unitary character `χ` that is not trivial on the norm-one
classes and has `heckeLogDiscriminantConductor χ ≤ A` has an entire function `ϑ` which vanishes
at `u` to at least the order of the zero of the completed L-function of `χ` at `a + u`,
satisfies `‖ϑ u‖ ≤ 1` for `|Re u| ≤ W`, and, when `Y ≥ 1` bounds the archimedean parameters of
`χ`, satisfies `c / (‖u‖ + Y) ^ n ≤ ‖ϑ u‖` for `Re u ≥ X` and for `Re u = -X`.
Reconstruction: The paper does not state this. -/
theorem exists_uniform_heckeMultiplier_strip_of_line (F : Type*) [Field F] [NumberField F]
    (a : ℝ) (k : ℕ) (hk : 3 / 2 ≤ 2 * a + k + 1 / 2) (W A : ℝ) :
    ∃ (c : ℝ) (n : ℕ), 0 < c ∧
      ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      heckeLogDiscriminantConductor χ ≤ A →
      ∃ ϑ : ℂ → ℂ, Differentiable ℂ ϑ ∧
        (∀ u : ℂ, (((meromorphicOrderAt (continuedCompletedHeckeL χ)
          ((a : ℂ) + u)).untop₀.toNat : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ u) ∧
        (∀ u : ℂ, |u.re| ≤ W → ‖ϑ u‖ ≤ 1) ∧
        ∀ Y : ℝ, 1 ≤ Y →
          (∀ w : InfinitePlace F, if hw : w.IsReal then
              ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ Y
            else
              let p := (complexHeckeCharacter_parameters χ w
                (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
              ‖p.1‖ ≤ Y ∧ (p.2.natAbs : ℝ) ≤ Y) →
          (∀ u : ℂ, a + k + 1 / 2 ≤ u.re → c / (‖u‖ + Y) ^ n ≤ ‖ϑ u‖) ∧
          (∀ u : ℂ, u.re = -(a + k + 1 / 2) → c / (‖u‖ + Y) ^ n ≤ ‖ϑ u‖) := by
  let j : ℕ := ⌈|W| + |a|⌉₊
  have hj : |W| + |a| ≤ j := Nat.le_ceil _
  have hR : (3 / 2 : ℝ) ≤ |a| + |W| + 3 / 2 := by linarith [abs_nonneg a, abs_nonneg W]
  obtain ⟨c, n, hc, h⟩ := exists_uniform_heckeMultiplier F (k + j) hR A
  have ha1 : 0 < 1 + |a| := by linarith [abs_nonneg a]
  refine ⟨c / (1 + |a|) ^ n, n, by positivity, fun χ hχ hA ↦ ?_⟩
  obtain ⟨ϑ, hd, hord, hup, hlow⟩ := h χ hχ hA
  have hW1 : -((k + j : ℕ) : ℝ) - 1 / 2 ≤ a - |W| := by
    push_cast
    linarith [neg_abs_le a, Nat.cast_nonneg (α := ℝ) k]
  have hW2 : a + |W| ≤ |a| + |W| + 3 / 2 := by linarith [le_abs_self a]
  exact ⟨fun u ↦ ϑ ((a : ℂ) + u), heckeMultiplier_chart
    (fun Y ↦ ∀ w : InfinitePlace F, if hw : w.IsReal then
        ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ Y
      else
        let p := (complexHeckeCharacter_parameters χ w
          (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
        ‖p.1‖ ≤ Y ∧ (p.2.natAbs : ℝ) ≤ Y)
    a (Nat.le_add_right k j) hk hW1 hW2 hc hd hord hup hlow⟩

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The multiplier of `exists_trivial_heckeMultiplier`
for the trivial character in the variable `u = s - a`, with the same half-width
`X = a + k + 1/2` as in `exists_uniform_heckeMultiplier_strip_of_line`: an entire function `ϑ`
which vanishes at `u` to at least the order of the zero of the completed L-function of the
trivial character at `a + u`, satisfies `‖ϑ u‖ ≤ 1` for `|Re u| ≤ W`, and satisfies
`c / (‖u‖ + 1) ^ n ≤ ‖ϑ u‖` for `Re u ≥ X` and for `Re u = -X`.
Reconstruction: The paper does not state this. -/
theorem exists_trivial_heckeMultiplier_strip_of_line (F : Type*) [Field F] [NumberField F]
    (a : ℝ) (k : ℕ) (hk : 3 / 2 ≤ 2 * a + k + 1 / 2) (W : ℝ) :
    ∃ (c : ℝ) (n : ℕ) (ϑ : ℂ → ℂ), 0 < c ∧ Differentiable ℂ ϑ ∧
      (∀ u : ℂ, (((meromorphicOrderAt (continuedCompletedHeckeL
        (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))) ((a : ℂ) + u)).untop₀.toNat : ℕ) : ℕ∞) ≤
          analyticOrderAt ϑ u) ∧
      (∀ u : ℂ, |u.re| ≤ W → ‖ϑ u‖ ≤ 1) ∧
      (∀ u : ℂ, a + k + 1 / 2 ≤ u.re → c / (‖u‖ + 1) ^ n ≤ ‖ϑ u‖) ∧
      (∀ u : ℂ, u.re = -(a + k + 1 / 2) → c / (‖u‖ + 1) ^ n ≤ ‖ϑ u‖) := by
  let j : ℕ := ⌈|W| + |a|⌉₊
  have hj : |W| + |a| ≤ j := Nat.le_ceil _
  have hR : (3 / 2 : ℝ) ≤ |a| + |W| + 3 / 2 := by linarith [abs_nonneg a, abs_nonneg W]
  obtain ⟨c, n, ϑ, hc, hd, hord, hup, hr, hl⟩ := exists_trivial_heckeMultiplier F (k + j) hR
  have ha1 : 0 < 1 + |a| := by linarith [abs_nonneg a]
  have hW1 : -((k + j : ℕ) : ℝ) - 1 / 2 ≤ a - |W| := by
    push_cast
    linarith [neg_abs_le a, Nat.cast_nonneg (α := ℝ) k]
  have hW2 : a + |W| ≤ |a| + |W| + 3 / 2 := by linarith [le_abs_self a]
  obtain ⟨h1, h2, h3, h4⟩ := heckeMultiplier_chart (fun Y ↦ Y = 1) a (Nat.le_add_right k j) hk
    hW1 hW2 hc hd hord hup (fun Y _ hY ↦ by
      subst hY
      exact ⟨hr, hl⟩)
  exact ⟨c / (1 + |a|) ^ n, n, fun u ↦ ϑ ((a : ℂ) + u), by positivity, h1, h2, h3,
    (h4 1 le_rfl rfl).1, (h4 1 le_rfl rfl).2⟩

end Uniform

end RiemannMasullo
