module

public import RiemannMasullo.Ch13_ZerosHecke.GaussianDedekindTwoSquares
public import RiemannMasullo.Ch13_ZerosHecke.GaussianJacobiCounts
public import RiemannMasullo.Ch13_ZerosHecke.GaussianNonsplitPrimePowers
public import RiemannMasullo.Ch13_ZerosHecke.GaussianNormMultiplicative

/-!
# The ordinary Dedekind zeta product for the Gaussian field

The split, inert and ramified prime-power counts in the Gaussian integers
determine every ideal coefficient by coprime multiplicativity. This proves
Jacobi's signed two-square identity and the ordinary Dedekind zeta product
for the fourth cyclotomic field.
-/

open NumberField

public noncomputable section

namespace RiemannMasullo

private theorem gaussianIdealNorm_primePower_coefficient {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (Nat.card {I : Ideal GaussianInt // I.absNorm = p^k} : ℂ) =
      gaussianQuadraticCharacter.zetaMul (p^k) := by
  rw [gaussianQuadraticCharacter_zetaMul_prime_pow hp k]
  by_cases h₂ : p = 2
  · subst p
    rw [ite_eq_left rfl]
    have h := gaussianNormFiber_card_prime_pow_two k
    rw [gaussianIdealNorm_count _ (by positivity)] at h
    exact_mod_cast (show Nat.card {I : Ideal GaussianInt // I.absNorm = 2^k} = 1 by omega)
  rw [ite_eq_right h₂]
  by_cases h₁ : p % 4 = 1
  · rw [ite_eq_left h₁]
    have h := gaussianNormFiber_card_prime_pow_of_mod_four_eq_one hp h₁ k
    rw [gaussianIdealNorm_count _ (pow_pos hp.pos k)] at h
    exact_mod_cast (show Nat.card {I : Ideal GaussianInt // I.absNorm = p^k} = k+1 by omega)
  rw [ite_eq_right h₁]
  have ho := Nat.odd_iff.mp (hp.odd_of_ne_two h₂)
  have h₃ : p % 4 = 3 := by omega
  have h := gaussianNormFiber_card_prime_pow_of_mod_four_eq_three hp h₃ k
  rw [gaussianIdealNorm_count _ (pow_pos hp.pos k)] at h
  by_cases he : Even k
  · rw [ite_eq_left he] at h ⊢
    exact_mod_cast (show Nat.card {I : Ideal GaussianInt // I.absNorm = p^k} = 1 by omega)
  · rw [ite_eq_right he] at h ⊢
    exact_mod_cast (show Nat.card {I : Ideal GaussianInt // I.absNorm = p^k} = 0 by omega)

private theorem gaussianIdealNorm_zetaMul {n : ℕ} (hn : n ≠ 0) :
    (Nat.card {I : Ideal GaussianInt // I.absNorm = n} : ℂ) =
      gaussianQuadraticCharacter.zetaMul n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => exact (hn rfl).elim
  | prime_pow p k hp => exact gaussianIdealNorm_primePower_coefficient hp k
  | coprime a b ha hb hab ia ib =>
    rw [gaussianIdealNorm_card_mul_of_coprime hab, Nat.cast_mul,
      gaussianQuadraticCharacter.isMultiplicative_zetaMul.2 hab, ia (by omega), ib (by omega)]

/-- The number of integral ideals of any positive norm in the Gaussian number field
equals the divisor sum of the quadratic character of discriminant minus four. -/
theorem gaussianNumberField_idealNormCoefficient (n : ℕ) (hn : 0 < n) :
    (Nat.card {I : Ideal (𝓞 (CyclotomicField 4 ℚ)) // I.absNorm = n} : ℤ) =
      ∑ d ∈ n.divisors, ZMod.χ₄ (d : ZMod 4) := by
  rw [gaussianNumberField_idealNormFiber_card]
  have h := gaussianIdealNorm_zetaMul hn.ne'
  rw [gaussianQuadraticCharacter_zetaMul_apply] at h
  exact_mod_cast h

/-- Jacobi's two-square identity for the ordered signed integer representations of
every positive natural number. -/
theorem gaussianTwoSquareCount_eq_divisorSum (n : ℕ) (hn : 0 < n) :
    (gaussianTwoSquareCount n : ℤ) = 4 * ∑ d ∈ n.divisors, ZMod.χ₄ (d : ZMod 4) := by
  rw [gaussianTwoSquareCount_eq_four_mul_idealCount n hn, Nat.cast_mul,
    gaussianNumberField_idealNormCoefficient n hn]
  rfl

/-- The ordinary Dedekind zeta function of the Gaussian number field is the product
of the Riemann zeta function and the Dirichlet L-function of its actual primitive
quadratic character modulo four on the half-plane of absolute convergence. -/
theorem gaussianDedekindZeta_eq_product {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (CyclotomicField 4 ℚ) s =
      riemannZeta s * gaussianQuadraticCharacter.LFunction s :=
  gaussianDedekindZeta_eq_of_twoSquareFormula gaussianTwoSquareCount_eq_divisorSum hs

end RiemannMasullo
