module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Injectivity
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHeckeRat

/-! # Rational primitive characters in the complete logarithmic derivative

The finite Hecke lift of a primitive Dirichlet character has coefficient
`χ n * Λ n` at every integer norm. The lift is trivial precisely for the
principal character, so the same identification tracks the pole term.
-/

public section

open Filter NumberField
open scoped NNReal

namespace RiemannMasullo

private theorem rationalIdeal_absNorm_injective :
    Function.Injective (Ideal.absNorm : Ideal (𝓞 ℚ) → ℕ) := by
  intro I J h
  obtain ⟨a, rfl⟩ := RatRingOfIntegers.exists_eq_span_natCast I
  obtain ⟨b, rfl⟩ := RatRingOfIntegers.exists_eq_span_natCast J
  change (Ideal.span {(a : 𝓞 ℚ)}).absNorm = (Ideal.span {(b : 𝓞 ℚ)}).absNorm at h
  rw [RatRingOfIntegers.absNorm_span_natCast, RatRingOfIntegers.absNorm_span_natCast] at h
  rw [h]

open NumberFieldKB.Chebotarev.RatIdele in
/-- Paper: Equations (B.6.1.4), (B.6.1.13)–(B.6.1.14), pp. 636, 638. Over the
rationals, weighting a norm coefficient by the ordinary von Mangoldt function
gives the logarithmic derivative coefficient, including at zero. -/
theorem heckeLogDerivCoefficient_rat_eq_normCoefficient_mul_vonMangoldt
    (η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) (n : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist η 0) n =
      heckeNormCoefficient (ideleClassNormTwist η 0) n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  classical
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let v := placeOf p hp
    have hv : v.asIdeal.absNorm = p := (absNorm_asIdeal v).trans (pr_placeOf p hp)
    have hweight (I : Ideal (𝓞 ℚ)) (hI : I.absNorm = p ^ k) :
        idealVonMangoldt I = ArithmeticFunction.vonMangoldt (p ^ k) := by
      have he : I = v.asIdeal ^ k := rationalIdeal_absNorm_injective (by rw [map_pow, hv, hI])
      rw [he, idealVonMangoldt_prime_pow v hk, hv, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    let e : {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = p ^ k} ≃
        {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = (↑(p ^ k : ℕ) : ℝ)} :=
      Equiv.subtypeEquivRight fun _ ↦ and_congr_right fun _ ↦ Nat.cast_inj.symm
    rw [heckeLogDerivCoefficient, heckeNormCoefficient, finsum_mul, ← finsum_comp_equiv e]
    apply finsum_congr
    intro I
    change heckeIdealVonMangoldt _ I.val = heckeIdealValue _ I.val * _
    rw [heckeIdealVonMangoldt, hweight I.val I.property.2]
  · have hzero := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    have hbound := heckeLogDerivCoefficient_le_vonMangoldt η n
    rw [hzero, mul_zero, norm_le_zero_iff] at hbound
    rw [hbound, hzero, Complex.ofReal_zero, mul_zero]

open NumberFieldKB.Chebotarev.RatIdele in
/-- A primitive Dirichlet character has a finite-order rational Hecke lift trivial
on every positive norm section. Its complete coefficients are the ordinary
Dirichlet values times the von Mangoldt function. The principal characters coincide. -/
theorem exists_rat_heckeLogDerivCoefficient_eq_dirichlet {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ∃ η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ), IsOfFinOrder η ∧
      (∀ (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (t : ℝ≥0ˣ), η (τ t) = 1) ∧
      (η = 1 ↔ χ = 1) ∧ ∀ n : ℕ, heckeLogDerivCoefficient (ideleClassNormTwist η 0) n =
        χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  obtain ⟨η, hη, hval, hL⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ
  have hcoeff (n : ℕ) : heckeLogDerivCoefficient (ideleClassNormTwist η 0) n =
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
    rw [heckeLogDerivCoefficient_rat_eq_normCoefficient_mul_vonMangoldt]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    congr 1
    let a (k : ℕ) := heckeNormCoefficient (ideleClassNormTwist η 0) k
    have ha := (finiteHeckeL_hasSum_normCoefficients η ⟨2, by norm_num⟩).LSeriesSummable
    have hb := (_root_.DirichletCharacter.LSeriesSummable_iff (NeZero.ne q) χ (s := 2)).mpr
      (by norm_num)
    apply LSeries.eq_of_LSeries_eventually_eq (f := a) (g := fun k : ℕ ↦ χ k)
      (ha.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
      (hb.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)) _ hn
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (finiteHeckeL_hasSum_normCoefficients η ⟨x, hx⟩).LSeries_eq.trans (hL x hx)
  refine ⟨η, hη, ?_, ⟨?_, ?_⟩, hcoeff⟩
  · intro τ t
    obtain ⟨k, hk, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hη
    let u : ℝ≥0ˣ := Units.mk0 ((t : ℝ≥0) ^ (k : ℝ)⁻¹) (NNReal.rpow_pos (Units.zero_lt t)).ne'
    have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
    rw [← hu, map_pow, map_pow]
    exact (ContinuousMonoidHom.pow_apply _ k (τ u)).symm.trans
      (congrArg (fun ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) ↦ ψ (τ u)) he)
  · intro he
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (fun h ↦ hne (χ.level_one' h))
    have hpχ : χ (p : ZMod q) = 0 := χ.map_nonunit
      (mt (ZMod.isUnit_iff_coprime p q).mp (fun h ↦ hp.coprime_iff_not_dvd.mp h hpd))
    have h := hcoeff p
    rw [he, heckeLogDerivCoefficient_trivial_rat, hpχ, zero_mul,
      ArithmeticFunction.vonMangoldt_apply_prime hp] at h
    exact (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp.one_lt)).ne') h
  · rintro rfl
    ext1 g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    apply Circle.ext
    rw [hval, coe_ideleChar, MulChar.coe_toUnitHom, MulChar.one_apply_coe, inv_one]
    rfl

end RiemannMasullo
