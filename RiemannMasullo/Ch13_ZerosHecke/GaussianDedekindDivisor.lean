module

public import RiemannMasullo.Ch13_ZerosHecke.GaussianDedekindProduct
public import RiemannMasullo.Ch13_ZerosHecke.GaussianZetaOrders

/-!
# The completed Gaussian trivial-character divisor

Jacobi's coefficient formula gives the Gaussian Dedekind factorization on the
convergence half-plane. The resulting divisor identity retains both ordinary
multiplicities at a common zero, including in the exterior window of
Theorem 12.5.1.1, pp. 519–520.
-/

public noncomputable section

open NumberField Set

namespace RiemannMasullo

local notation "K" => CyclotomicField 4 ℚ
local notation "G" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "L₄" => continuedCompletedHeckeL (1 : G)
local notation "β₄" => gaussianQuadraticCharacter.LFunction

/-- The genuine Gaussian completed trivial-character divisor is the sum of the
ordinary Riemann and quadratic Dirichlet divisors throughout the positive half-plane. -/
theorem gaussianCompletedDivisor_eq {s : ℂ} (hs : 0 < s.re) :
    MeromorphicOn.divisor L₄ univ s =
      MeromorphicOn.divisor riemannZeta univ s + MeromorphicOn.divisor β₄ univ s :=
  trivialHeckeDivisor_eq_zeta_add_dirichlet_of_dedekindZeta_eq_mul K gaussianQuadraticCharacter
    (fun _ ↦ gaussianDedekindZeta_eq_product) hs

/-- A positive Gaussian completed divisor in the open critical strip is equivalent
to a zero of at least one of its two ordinary factors. -/
theorem gaussianCompletedDivisor_pos_iff {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    0 < MeromorphicOn.divisor L₄ univ s ↔ riemannZeta s = 0 ∨ β₄ s = 0 := by
  apply trivialHeckeDivisor_pos_iff_of_dedekindZeta_eq_mul K gaussianQuadraticCharacter
    (fun _ ↦ gaussianDedekindZeta_eq_product) hs₀
  rintro rfl
  exact (lt_irrefl _ hs₁)

/-- With the inclusive boundary of the paper's exterior sum, the trivial Gaussian
character sees exactly the ordinary zeros of the two factors in that window. -/
theorem gaussianTrivialExteriorZeros_eq (α : ℝ) :
    {s : ℂ | 0 < MeromorphicOn.divisor L₄ univ s ∧ α ≤ |s.re - 1 / 2|} =
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ α ≤ |s.re - 1 / 2| ∧
      (riemannZeta s = 0 ∨ β₄ s = 0)} :=
  trivialHeckeExterior_eq_of_dedekindZeta_eq_mul K gaussianQuadraticCharacter
    (fun _ ↦ gaussianDedekindZeta_eq_product) α

end RiemannMasullo
