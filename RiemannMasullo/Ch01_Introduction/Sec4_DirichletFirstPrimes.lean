module

public import RiemannMasullo.Ch01_Introduction.Sec4_TranslatedFirstPrimes
public import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHeckeRat
import Mathlib.NumberTheory.LSeries.Injectivity
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # Dirichlet characters in the rational first-prime sum

The rational Hecke lift of a primitive Dirichlet character recovers its usual prime values
in the translated first-prime sum. Equality of the convergent Dirichlet series identifies
the norm coefficients. At prime norm the logarithmic derivative supplies the factor `log p`.
-/

public section

open Filter NumberField
open scoped BigOperators NNReal

namespace RiemannMasullo

/-- At a rational prime the ideal logarithmic derivative coefficient is the
ordinary norm coefficient times the logarithm of the prime, in any number field. -/
theorem heckeLogDerivCoefficient_prime_eq_normCoefficient {F : Type*} [Field F] [NumberField F]
    (η : HeckeCharacter (𝓞 F) F) {p : ℕ} (hp : p.Prime) :
    heckeLogDerivCoefficient η p = heckeNormCoefficient η p * (Real.log p : ℂ) := by
  classical
  let e : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = p} ≃
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = p} :=
    Equiv.subtypeEquivRight (fun _ ↦ and_congr_right fun _ ↦ Nat.cast_inj.symm)
  rw [heckeLogDerivCoefficient, heckeNormCoefficient, finsum_mul, ← finsum_comp_equiv e]
  apply finsum_congr
  intro I
  have hprime : I.val.absNorm.Prime := I.property.2.symm ▸ hp
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨I.val, Ideal.isPrime_of_irreducible_absNorm (Nat.irreducible_iff_prime.mpr
      (Nat.prime_iff.mp hprime)), I.property.1⟩
  have hv : idealVonMangoldt I.val = Real.log (p : ℝ) := by
    simpa only [pow_one, v, I.property.2] using idealVonMangoldt_prime_pow v (k := 1) (by decide)
  change heckeIdealVonMangoldt η I.val = heckeIdealValue η I.val * _
  rw [heckeIdealVonMangoldt, hv]

/-- Equality with a Dirichlet series on the convergence half-plane identifies all
positive norm coefficients of the rational Hecke lift. -/
theorem heckeNormCoefficient_rat_of_finiteHeckeL_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL η ⟨s, hs⟩ = LSeries (χ ·) s)
    {n : ℕ} (hn : n ≠ 0) :
    heckeNormCoefficient (ideleClassNormTwist η 0) n = χ n := by
  let a (m : ℕ) := heckeNormCoefficient (ideleClassNormTwist η 0) m
  have h₂ := finiteHeckeL_hasSum_normCoefficients η ⟨2, by norm_num⟩
  have ha : LSeries.abscissaOfAbsConv a < ⊤ :=
    h₂.LSeriesSummable.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hb : LSeries.abscissaOfAbsConv (fun m : ℕ ↦ χ m) < ⊤ := by
    rw [_root_.DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne q) χ]
    exact_mod_cast EReal.coe_lt_top (1 : ℝ)
  apply LSeries.eq_of_LSeries_eventually_eq ha hb _ hn
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx' : 1 < (x : ℂ).re := hx
  exact (finiteHeckeL_hasSum_normCoefficients η ⟨x, hx'⟩).LSeries_eq.trans (hL x hx')

/-- A rational Hecke row with the specified convergent Dirichlet series has precisely
the original twisted rational-prime weights at every finite translated cutoff. -/
theorem firstPrimeDegreeOneSum_rat_of_finiteHeckeL_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL η ⟨s, hs⟩ = LSeries (χ ·) s)
    (H : ℝ → ℂ) (y b : ℝ) : firstPrimeDegreeOneSum η H y b =
      ∑ p ∈ Finset.Ioc 0 ⌊Real.exp (y + b)⌋₊ with p.Prime,
        χ p * ((Real.log (p : ℝ) / Real.sqrt (p : ℝ) : ℝ) : ℂ) * H (Real.log (p : ℝ) - y) := by
  classical
  unfold firstPrimeDegreeOneSum
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  rw [← firstPrime_coefficient η hprime, heckeLogDerivCoefficient_prime_eq_normCoefficient _ hprime,
    heckeNormCoefficient_rat_of_finiteHeckeL_eq χ η hL hprime.ne_zero,
    firstPrimeShellWeight, Complex.ofReal_div]
  ring

/-- Each primitive Dirichlet character has a finite-order Chapter 12 parameter trivial
on every positive norm section. Its inverse has the prescribed idelic values and gives
the Dirichlet prime sum at every translated cutoff, including conductor primes. -/
theorem exists_rat_firstPrimeDegreeOneSum_eq_dirichlet {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ∃ ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ), IsOfFinOrder ψ ∧
      (∀ (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (t : ℝ≥0ˣ), ψ (τ t) = 1) ∧
      (∀ x : NumberFieldKB.Chebotarev.RatIdele.IdQ,
        (ψ⁻¹ (QuotientGroup.mk x) : ℂ) =
          ((NumberFieldKB.Chebotarev.RatIdele.ideleChar q χ x : ℂˣ) : ℂ)) ∧
      ∀ (H : ℝ → ℂ) (y b : ℝ), firstPrimeDegreeOneSum ψ⁻¹ H y b =
        ∑ p ∈ Finset.Ioc 0 ⌊Real.exp (y + b)⌋₊ with p.Prime,
          χ p * ((Real.log (p : ℝ) / Real.sqrt (p : ℝ) : ℝ) : ℂ) * H (Real.log (p : ℝ) - y) := by
  classical
  obtain ⟨η, hη, hv, hL⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ
  refine ⟨η⁻¹, hη.inv, ?_, by simpa only [inv_inv] using hv, ?_⟩
  · intro τ t
    obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hη.inv
    let u : ℝ≥0ˣ := Units.mk0 ((t : ℝ≥0) ^ (k : ℝ)⁻¹) (NNReal.rpow_pos (Units.zero_lt t)).ne'
    have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
    rw [← hu, map_pow, map_pow]
    exact (ContinuousMonoidHom.pow_apply _ k (τ u)).symm.trans
      (congrArg (fun θ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) ↦ θ (τ u)) hpow)
  · simpa only [inv_inv] using firstPrimeDegreeOneSum_rat_of_finiteHeckeL_eq χ η hL

end RiemannMasullo
