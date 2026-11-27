module

public import RiemannMasullo.Ch13_ZerosHecke.GaussianIdealNormFibers
public import RiemannMasullo.Ch13_ZerosHecke.GaussianNumberField
public import RiemannMasullo.Ch13_ZerosHecke.GaussianQuadraticLSeries
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The ordinary Gaussian Dedekind series in signed lattice coordinates

The field is the genuine fourth cyclotomic field. Its norm-`n` ideals for
positive `n` are counted by one quarter of the ordered signed two-square
representations of `n`. This identifies the defining Dedekind series with
the Gaussian lattice series.
-/

open NumberField Finset

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The number of ordered signed representations of a natural integer as two squares. -/
def gaussianTwoSquareCount (n : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ // v.1 ^ 2 + v.2 ^ 2 = (n : ℤ)}

/-- The four Gaussian units account for the multiplicity of every ideal of positive norm. -/
theorem gaussianTwoSquareCount_eq_four_mul_idealCount (n : ℕ) (hn : 0 < n) :
    gaussianTwoSquareCount n =
      4 * Nat.card {I : Ideal (𝓞 (CyclotomicField 4 ℚ)) // I.absNorm = n} := by
  rw [gaussianNumberField_idealNormFiber_card, gaussianTwoSquareCount, gaussianTwoSquare_count,
    gaussianIdealNorm_count n hn]

/-- The ordinary Gaussian Dedekind series has the literal lattice representation numbers
divided by four as its positive Dirichlet coefficients. -/
theorem gaussianDedekindZeta_eq_twoSquareSeries (s : ℂ) :
    dedekindZeta (CyclotomicField 4 ℚ) s =
      LSeries (fun n ↦ (gaussianTwoSquareCount n : ℂ) / 4) s := by
  unfold dedekindZeta
  apply LSeries_congr _ s
  intro n hn
  rw [gaussianTwoSquareCount_eq_four_mul_idealCount n (Nat.pos_of_ne_zero hn)]
  push_cast
  ring

/-- Jacobi's signed integer two-square divisor identity implies the actual ordinary
Dedekind product on its half-plane of absolute convergence. -/
theorem gaussianDedekindZeta_eq_of_twoSquareFormula
    (hJ : ∀ n : ℕ, 0 < n →
      (gaussianTwoSquareCount n : ℤ) = 4 * ∑ d ∈ n.divisors, ZMod.χ₄ (d : ZMod 4))
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (CyclotomicField 4 ℚ) s = riemannZeta s * gaussianQuadraticCharacter.LFunction s := by
  rw [gaussianDedekindZeta_eq_twoSquareSeries, ← gaussianQuadraticLSeries_eq_product hs]
  apply LSeries_congr _ s
  intro n hn
  rw [gaussianQuadraticCharacter_zetaMul_apply]
  have h : (gaussianTwoSquareCount n : ℂ) = 4 * ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℂ) := by
    exact_mod_cast hJ n (Nat.pos_of_ne_zero hn)
  rw [h]
  ring

end RiemannMasullo
