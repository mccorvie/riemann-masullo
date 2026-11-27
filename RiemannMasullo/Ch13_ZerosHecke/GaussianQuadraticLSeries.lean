module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The quadratic character of discriminant minus four

The character in the Gaussian Dedekind product is Mathlib's integer-valued
character modulo four, with values mapped to the complex numbers. Its zeta
convolution has the explicit split, inert and ramified prime-power coefficients.
-/

open ArithmeticFunction Finset

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The complex Dirichlet character of conductor four attached to the Gaussian field. -/
def gaussianQuadraticCharacter : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The value on a natural number retains the integer-valued character convention. -/
theorem gaussianQuadraticCharacter_apply (n : ℕ) :
    gaussianQuadraticCharacter (n : ZMod 4) = (ZMod.χ₄ (n : ZMod 4) : ℂ) := rfl

/-- The character of discriminant minus four is nonprincipal. -/
theorem gaussianQuadraticCharacter_ne_one : gaussianQuadraticCharacter ≠ 1 := by
  intro he
  have h := congrArg (fun χ : DirichletCharacter ℂ 4 ↦ χ 3) he
  change gaussianQuadraticCharacter (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) 3 at h
  have hc : gaussianQuadraticCharacter (3 : ZMod 4) = -1 := by
    change ((ZMod.χ₄ (3 : ZMod 4) : ℤ) : ℂ) = -1
    norm_num [show ZMod.χ₄ (3 : ZMod 4) = -1 by decide]
  have hu : IsUnit (3 : ZMod 4) := (ZMod.isUnit_iff_coprime 3 4).mpr (by decide)
  rw [hc, MulChar.one_apply hu] at h
  norm_num at h

/-- The character has its full conductor four. -/
theorem gaussianQuadraticCharacter_isPrimitive : gaussianQuadraticCharacter.IsPrimitive := by
  have hm := gaussianQuadraticCharacter.conductor_dvd_level
  have h := Nat.mem_divisors.mpr ⟨hm, (by decide : 4 ≠ 0)⟩
  rw [show (4 : ℕ).divisors = {1, 2, 4} by decide] at h
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h
  · exact (gaussianQuadraticCharacter_ne_one
      (gaussianQuadraticCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
  · have hf := gaussianQuadraticCharacter.factorsThrough_conductor
    rw [h] at hf
    obtain ⟨hd, ψ, he⟩ := hf
    have hψ : ψ = 1 := by
      apply MulChar.ext
      intro u
      rw [Subsingleton.elim u 1]
      simp
    rw [hψ, map_one] at he
    exact (gaussianQuadraticCharacter_ne_one he).elim
  · exact h

/-- The coefficient of the zeta convolution is the sum in Jacobi's two-square formula. -/
theorem gaussianQuadraticCharacter_zetaMul_apply (n : ℕ) :
    gaussianQuadraticCharacter.zetaMul n = ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℂ) := by
  rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply]
  apply sum_congr rfl
  intro d hd
  rw [← gaussianQuadraticCharacter_apply]
  exact (gaussianQuadraticCharacter.apply_eq_toArithmeticFunction_apply
    (Nat.pos_of_mem_divisors hd).ne').symm

/-- The prime-power coefficient is one above two, `k+1` at a split prime, and the
indicator of an even exponent at an inert prime. -/
theorem gaussianQuadraticCharacter_zetaMul_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    gaussianQuadraticCharacter.zetaMul (p^k) =
      if p = 2 then 1 else if p % 4 = 1 then (k : ℂ) + 1 else if Even k then 1 else 0 := by
  have hsum : gaussianQuadraticCharacter.zetaMul (p^k) =
      ∑ i ∈ range (k+1), gaussianQuadraticCharacter (p : ZMod 4)^i := by
    rw [gaussianQuadraticCharacter_zetaMul_apply, Nat.sum_divisors_prime_pow hp]
    simp only [gaussianQuadraticCharacter_apply, Nat.cast_pow, map_pow, Int.cast_pow]
  rw [hsum, gaussianQuadraticCharacter_apply, ZMod.χ₄_nat_eq_if_mod_four]
  by_cases h₂ : p = 2
  · subst p
    norm_num [sum_range_succ', pow_succ']
  have ho : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h₂)
  by_cases h₁ : p % 4 = 1
  · simp [h₂, ho, h₁]
  · simp only [h₂, ho, h₁, one_ne_zero, ↓reduceIte, Int.cast_neg, Int.cast_one, neg_one_geom_sum]
    by_cases hk : Even k <;> simp [Nat.even_add_one, ← Nat.not_even_iff_odd, hk]

/-- On the half-plane of absolute convergence, the actual zeta and Dirichlet
L-functions multiply to the series of the Gaussian divisor coefficients. -/
theorem gaussianQuadraticLSeries_eq_product {s : ℂ} (hs : 1 < s.re) :
    LSeries gaussianQuadraticCharacter.zetaMul s =
      riemannZeta s * gaussianQuadraticCharacter.LFunction s := by
  symm
  rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution']
  · rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr gaussianQuadraticCharacter.apply_eq_toArithmeticFunction_apply s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦
      (gaussianQuadraticCharacter.apply_eq_toArithmeticFunction_apply h).symm).mpr
      (ZMod.LSeriesSummable_of_one_lt_re gaussianQuadraticCharacter hs)

end RiemannMasullo
