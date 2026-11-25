module

public import RiemannMasullo.ForMathlib.Analysis.Complex.FiniteTaylorControl
public import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-! Explicit finite Dirichlet polynomial extrapolation for a series converging to the right of one. -/

@[expose] public noncomputable section

open Complex Finset Set

namespace RiemannMasullo.FiniteTaylor

/-- The Dirichlet frequency `m^(-s)`, written in exponential coordinates.
The value at zero is harmless because every arithmetic function vanishes there. -/
def frequency (m : ℕ) (s : ℂ) : ℂ := exp (-(Real.log m : ℂ) * s)

theorem frequency_eq_inv_cpow {m : ℕ} (hm : m ≠ 0) (s : ℂ) :
    frequency m s = ((m : ℂ) ^ s)⁻¹ := by
  rw [frequency, cpow_def_of_ne_zero (by exact_mod_cast hm : (m : ℂ) ≠ 0), ← exp_neg]
  rw [Complex.ofReal_log (Nat.cast_nonneg m)]
  push_cast
  rw [neg_mul]

/-- A finite Dirichlet polynomial with the given arithmetic coefficients. -/
def dirichletPolynomial (b : ArithmeticFunction ℂ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ range M, b m * frequency m s

theorem dirichletPolynomial_eq_partial_LSeries (b : ArithmeticFunction ℂ) (M : ℕ) (s : ℂ) :
    dirichletPolynomial b M s = ∑ m ∈ range M, LSeries.term b s m := by
  apply Finset.sum_congr rfl
  intro m hm
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [frequency_eq_inv_cpow hm, LSeries.term_of_ne_zero hm, div_eq_mul_inv]

theorem analytic_dirichletPolynomial (b : ArithmeticFunction ℂ) (M : ℕ) (s : ℂ) :
    AnalyticAt ℂ (dirichletPolynomial b M) s := by
  unfold dirichletPolynomial frequency
  fun_prop

/-- The Taylor extrapolate is itself a finite sum of explicitly weighted single frequencies. -/
def extrapolate (b : ArithmeticFunction ℂ) (K M : ℕ) (c d : ℂ) : ℂ :=
  ∑ m ∈ range M, b m * frequency m c *
    ∑ k ∈ range K, (d * (-(Real.log m : ℂ))) ^ k / (k.factorial : ℂ)

theorem taylorSum_dirichletPolynomial (b : ArithmeticFunction ℂ) (K M : ℕ) (c z : ℂ) :
    taylorSum (dirichletPolynomial b M) c z K = extrapolate b K M c (z - c) := by
  have hi (k : ℕ) : iteratedDeriv k (dirichletPolynomial b M) c =
      ∑ m ∈ range M, b m * ((-(Real.log m : ℂ)) ^ k * frequency m c) := by
    unfold dirichletPolynomial frequency
    rw [iteratedDeriv_fun_sum (by fun_prop)]
    apply Finset.sum_congr rfl
    intro m _
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
  unfold taylorSum extrapolate
  simp only [term, hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow]
  ring

end RiemannMasullo.FiniteTaylor
