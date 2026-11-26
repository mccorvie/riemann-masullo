module

public import RiemannMasullo.Ch13_ZerosHecke.AnnularPrimeTrapezoid
public import RiemannMasullo.Ch13_ZerosHecke.QuarticCharacterFive
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Basic.Complex.BigOperators
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quartic annular statistic on genuine primes

For the primitive character modulo five with value `I` at two, we sum the
annular kernel against the first-prime Riesz coefficients. This gives an
exact comparison between two finite prime statistics in the arithmetic
question associated with Theorem 12.5.1.1, pp. 519–520. Only primes strictly
between `j / 2` and `j` enter the rounding error. Chebyshev's bound makes
the absolute error summable after normalization by `j ^ 7`.
-/

open Finset
open scoped BigOperators

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The first-prime Riesz sum of the primitive quartic character modulo five. -/
def quarticPrimeRieszSum (t : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE ⌊t⌋₊, quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ) *
    (max (t - (p : ℝ)) 0 : ℝ)

/-- The finite quartic prime statistic with the annular kernel at scale `y`. -/
def quarticAnnularPrimeStatistic (y : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE ⌊y⌋₊, quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ) *
    (annularPrimeKernel ((p : ℝ) / y) : ℂ)

/-- The logarithmic prime weight is nonnegative before multiplication by the character. -/
theorem quarticAnnularPrimeWeight_nonneg {p : ℕ} (hp : p.Prime) (y : ℝ) :
    0 ≤ Real.log p * annularPrimeKernel ((p : ℝ) / y) := by
  apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le))
  unfold annularPrimeKernel
  split_ifs with h h'
  · linarith
  · exact div_nonneg (sq_nonneg _) (by linarith)
  · exact le_rfl

/-- The real projection gives each annular prime weight its real character coefficient. -/
theorem quarticAnnularPrimeStatistic_re (y : ℝ) :
    (quarticAnnularPrimeStatistic y).re = ∑ p ∈ Nat.primesLE ⌊y⌋₊,
      (quarticCharacterFive (p : ZMod 5)).re * Real.log p * annularPrimeKernel ((p : ℝ) / y) := by
  simp only [quarticAnnularPrimeStatistic, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The real projection is the difference of the two weighted prime sums
in residue classes one and four. -/
theorem quarticAnnularPrimeStatistic_re_eq_residueSums (y : ℝ) :
    (quarticAnnularPrimeStatistic y).re =
      (∑ p ∈ (Nat.primesLE ⌊y⌋₊).filter (fun p ↦ p % 5 = 1),
        Real.log p * annularPrimeKernel ((p : ℝ) / y)) -
      ∑ p ∈ (Nat.primesLE ⌊y⌋₊).filter (fun p ↦ p % 5 = 4),
        Real.log p * annularPrimeKernel ((p : ℝ) / y) := by
  rw [quarticAnnularPrimeStatistic_re, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [quarticCharacterFive_re_natCast]
  by_cases h₁ : p % 5 = 1
  · simp [h₁]
  · by_cases h₄ : p % 5 = 4 <;> simp [h₁, h₄]

/-- The trapezoidal annular average of the actual Riesz sum at fourth-power scale. -/
def quarticAnnularPrimeDilation (j : ℕ) : ℂ :=
  ∑ n ∈ Icc (j ^ 3) (2 * j ^ 3), (annularTrapWeight (j ^ 3) n : ℂ) * n *
    quarticPrimeRieszSum ((j : ℝ) ^ 4 / n)

/-- The residual from knots strictly inside the annulus, with their exact fractional parts. -/
def quarticAnnularPrimeCorrection (j : ℕ) : ℂ :=
  (1 / 2 : ℂ) * ∑ p ∈ (Nat.primesLE j).filter (fun p ↦ j < 2 * p ∧ p < j),
    quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ) *
      ((p : ℝ) * Int.fract ((j : ℝ) ^ 4 / p) * (1 - Int.fract ((j : ℝ) ^ 4 / p)) : ℝ)

private theorem quarticPrimeRieszSum_extend {t : ℝ} {M : ℕ} (ht : t ≤ M) :
    quarticPrimeRieszSum t = ∑ p ∈ Nat.primesLE M,
      quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ) * (max (t - (p : ℝ)) 0 : ℝ) := by
  apply sum_subset (Nat.primesLE_mono (Nat.floor_le_of_le ht))
  intro p hp hn
  have htp : t ≤ p := by
    by_contra! h
    exact hn (Nat.mem_primesLE.mpr ⟨Nat.le_floor h.le, Nat.prime_of_mem_primesLE hp⟩)
  simp [max_eq_right (sub_nonpos.mpr htp)]

private theorem quarticPrimeRieszSum_dilate {j n : ℕ} (hj : 1 ≤ j) (hn : j ^ 3 ≤ n) :
    (n : ℂ) * quarticPrimeRieszSum ((j : ℝ) ^ 4 / n) = ∑ p ∈ Nat.primesLE j,
      quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ) *
        (max ((j : ℝ) ^ 4 - p * n) 0 : ℝ) := by
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hn' : (j : ℝ) ^ 3 ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (pow_pos hjpos 3) hn'
  have hcut : (j : ℝ) ^ 4 / n ≤ j := by
    rw [div_le_iff₀ hnpos]
    calc (j : ℝ) ^ 4 = j * (j : ℝ) ^ 3 := by ring
         _ ≤ j * (n : ℝ) := mul_le_mul_of_nonneg_left hn' hjpos.le
  rw [quarticPrimeRieszSum_extend hcut, mul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  have hweight : (n : ℝ) * max ((j : ℝ) ^ 4 / n - p) 0 = max ((j : ℝ) ^ 4 - p * n) 0 := by
    rw [mul_max_of_nonneg _ _ hnpos.le, mul_zero]
    congr 1
    field_simp
  rw [← hweight, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

/-- The true trapezoidal fourth-power sample equals `j ^ 7` times the annular
prime statistic plus the fractional-part correction in the open annulus. -/
theorem quarticAnnularPrimeDilation_eq (j : ℕ) (hj : 1 ≤ j) :
    quarticAnnularPrimeDilation j =
      (j : ℂ) ^ 7 * quarticAnnularPrimeStatistic j + quarticAnnularPrimeCorrection j := by
  let b (p : ℕ) : ℂ := quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ)
  let r (p : ℕ) : ℝ := p * Int.fract ((j : ℝ) ^ 4 / p) * (1 - Int.fract ((j : ℝ) ^ 4 / p))
  let s := Icc (j ^ 3) (2 * j ^ 3)
  let w (n p : ℕ) : ℝ := annularTrapWeight (j ^ 3) n * max ((j : ℝ) ^ 4 - p * n) 0
  calc
    quarticAnnularPrimeDilation j = ∑ n ∈ s, ∑ p ∈ Nat.primesLE j, b p * (w n p : ℂ) := by
      unfold quarticAnnularPrimeDilation
      refine sum_congr rfl fun n hn ↦ ?_
      rw [mul_assoc, quarticPrimeRieszSum_dilate hj (mem_Icc.mp hn).1, mul_sum]
      refine sum_congr rfl fun p _ ↦ ?_
      simp only [w, b, Complex.ofReal_mul]
      ring
    _ = ∑ p ∈ Nat.primesLE j, b p * ((∑ n ∈ s, w n p : ℝ) : ℂ) := by
      rw [sum_comm]
      simp only [Complex.ofReal_sum, mul_sum]
    _ = ∑ p ∈ Nat.primesLE j, ((j : ℂ) ^ 7 * (b p * (annularPrimeKernel ((p : ℝ) / j) : ℂ)) +
          (if j < 2 * p ∧ p < j then (1 / 2 : ℂ) * (b p * (r p : ℂ)) else 0)) := by
      refine sum_congr rfl fun p hp ↦ ?_
      have hs := annularPrimeTrapezoid_identity j p hj (Nat.prime_of_mem_primesLE hp).one_le
      change (∑ n ∈ s, w n p) = _ at hs
      rw [hs]
      by_cases h : j < 2 * p ∧ p < j <;> simp [h, r] <;> ring
    _ = _ := by
      simp only [quarticAnnularPrimeStatistic, quarticAnnularPrimeCorrection, Nat.floor_natCast,
        sum_add_distrib, mul_sum, sum_filter, mul_ite, mul_zero, b, r]

/-- The total rounding error is at most `log 4 * j ^ 2 / 8`. -/
theorem norm_quarticAnnularPrimeCorrection_le (j : ℕ) :
    ‖quarticAnnularPrimeCorrection j‖ ≤ Real.log 4 * (j : ℝ) ^ 2 / 8 := by
  let f (p : ℕ) := Int.fract ((j : ℝ) ^ 4 / p)
  let s := (Nat.primesLE j).filter (fun p ↦ j < 2 * p ∧ p < j)
  have hlog (p : ℕ) (hp : p ∈ Nat.primesLE j) : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  have hterm (p : ℕ) (hp : p ∈ Nat.primesLE j) :
      ‖quarticCharacterFive (p : ZMod 5) * (Real.log p : ℂ) *
        ((p : ℝ) * f p * (1 - f p) : ℝ)‖ ≤ Real.log p * (j / 4) := by
    have h₀ : 0 ≤ f p := Int.fract_nonneg _
    have h₁ : 0 ≤ 1 - f p := sub_nonneg.mpr (Int.fract_lt_one _).le
    have hweight : 0 ≤ (p : ℝ) * f p * (1 - f p) := by positivity
    have hjp : (p : ℝ) ≤ j := by exact_mod_cast Nat.le_of_mem_primesLE hp
    have hbound : (p : ℝ) * f p * (1 - f p) ≤ j / 4 := calc
      _ = (p : ℝ) * (f p * (1 - f p)) := by ring
      _ ≤ (p : ℝ) * (1 / 4) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (f p - 1/2)]) p.cast_nonneg
      _ ≤ j / 4 := by linarith
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (p.cast_nonneg : 0 ≤ (p : ℝ)), abs_of_nonneg h₀, abs_of_nonneg h₁,
      abs_of_nonneg (hlog p hp)]
    calc
      _ ≤ 1 * Real.log p * ((p : ℝ) * f p * (1 - f p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (quarticCharacterFive.norm_le_one (p : ZMod 5)) (hlog p hp)) hweight
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_left hbound (hlog p hp)
  rw [quarticAnnularPrimeCorrection, norm_mul, norm_div, norm_one, Complex.norm_two]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ s, Real.log p * (j / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_sum_le _ _).trans (sum_le_sum fun p hp ↦ hterm p (mem_filter.mp hp).1)
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ Nat.primesLE j, Real.log p * (j / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦
        mul_nonneg (hlog p hp) (by positivity)
    _ = (1 / 2 : ℝ) * (Chebyshev.theta j * (j / 4)) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log, sum_mul]
    _ ≤ _ := by
      have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg j : 0 ≤ (j : ℝ))
      nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg j : 0 ≤ (j : ℝ))]

/-- The normalized fourth-power sample approximates the finite annular statistic
with an explicit fifth-power error. -/
theorem quarticAnnularPrimeDilation_normalized_error (j : ℕ) (hj : 1 ≤ j) :
    ‖quarticAnnularPrimeDilation j / (j : ℂ) ^ 7 - quarticAnnularPrimeStatistic j‖ ≤
      (Real.log 4 / 8) / (j : ℝ) ^ 5 := by
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [quarticAnnularPrimeDilation_eq j hj, add_div,
    mul_div_cancel_left₀ _ (pow_ne_zero 7 hjc), add_sub_cancel_left, norm_div, norm_pow,
    Complex.norm_natCast, div_le_iff₀ (pow_pos hjpos 7)]
  calc
    _ ≤ Real.log 4 * (j : ℝ) ^ 2 / 8 := norm_quarticAnnularPrimeCorrection_le j
    _ = _ := by field_simp

/-- The absolute discrepancies of all normalized integer samples form a convergent series. -/
theorem summable_quarticAnnularPrimeDilation_error :
    Summable (fun j : ℕ ↦
      ‖quarticAnnularPrimeDilation j / (j : ℂ) ^ 7 - quarticAnnularPrimeStatistic j‖) := by
  have hs := (Real.summable_nat_pow_inv.mpr (show 1 < 5 by decide)).mul_left (Real.log 4 / 8)
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hs
  intro j
  rcases j with _ | j
  · simp [quarticAnnularPrimeStatistic]
  · simpa only [div_eq_mul_inv] using quarticAnnularPrimeDilation_normalized_error (j + 1) (by omega)

end RiemannMasullo
