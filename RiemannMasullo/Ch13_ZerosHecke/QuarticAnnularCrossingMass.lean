module

public import RiemannMasullo.Ch13_ZerosHecke.CompensatedGaussianMoments
public import RiemannMasullo.Ch13_ZerosHecke.QuarticCharacterFive
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Function.Floor

/-! # Gaussian integrability of the quartic prime crossing mass

The two indicators count primes that an increment of size `|h|` can carry
across either annular endpoint. Chebyshev's bound for the sum of prime
logarithms gives a Gaussian-integrable majorant despite the moving cutoff.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

public noncomputable section

namespace RiemannMasullo

/-- Summation over primes up to a measurable natural cutoff preserves measurability
when each summand is a measurable function of the same variable. -/
theorem measurable_sum_primesLE_of_measurable {g : ℝ → ℕ} {f : ℕ → ℝ → ℝ}
    (hg : Measurable g) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun h ↦ ∑ p ∈ Nat.primesLE (g h), f p h) := by
  have hm : Measurable (fun t : ℝ × ℕ ↦ ∑ p ∈ Nat.primesLE t.2, f p t.1) :=
    measurable_from_prod_countable_left fun N ↦
      (Nat.primesLE N).measurable_fun_sum (fun p _ ↦ hf p)
  exact hm.comp (measurable_id.prodMk hg)

/-- The quartic-character mass of prime crossings at the two logarithmic
annular endpoints, with half the weight at the outer endpoint. -/
@[expose] def quarticAnnularPrimeCrossingMass (y h : ℝ) : ℝ :=
  h^2 * Real.exp |h| * ∑ p ∈ Nat.primesLE ⌊y * Real.exp |h|⌋₊,
    (|(quarticCharacterFive (p : ZMod 5)).re| * Real.log p) *
      ((if |Real.log (2 * (p : ℝ)/y)| ≤ |h| then 1 else 0) +
       (if |Real.log ((p : ℝ)/y)| ≤ |h| then 1/2 else 0))

/-- The crossing mass is nonnegative for every scale and increment. -/
theorem quarticAnnularPrimeCrossingMass_nonneg (y h : ℝ) :
    0 ≤ quarticAnnularPrimeCrossingMass y h := by
  unfold quarticAnnularPrimeCrossingMass
  refine mul_nonneg (by positivity) (sum_nonneg fun p _ ↦ ?_)
  have hp := Real.log_natCast_nonneg p
  split_ifs <;> positivity

/-- For every fixed scale the mass, including its moving prime cutoff, is
measurable in the increment. -/
theorem quarticAnnularPrimeCrossingMass_measurable (y : ℝ) :
    Measurable (quarticAnnularPrimeCrossingMass y) := by
  have hs (b k : ℝ) : Measurable (fun h : ℝ ↦ if b ≤ |h| then k else 0) :=
    Measurable.ite (measurableSet_le measurable_const continuous_abs.measurable)
      measurable_const measurable_const
  unfold quarticAnnularPrimeCrossingMass
  refine Measurable.mul (by fun_prop) (measurable_sum_primesLE_of_measurable (by fun_prop) ?_)
  intro p
  exact measurable_const.mul ((hs _ _).add (hs _ _))

/-- A single exponential majorant controls the mass for every increment.
The prime sum enters through the elementary Chebyshev bound for `θ`. -/
theorem quarticAnnularPrimeCrossingMass_le (y h : ℝ) (hy : 0 ≤ y) :
    quarticAnnularPrimeCrossingMass y h ≤
      (2 * Real.log 4 * y) * (|h|^2 * Real.exp (2 * |h|)) := by
  let b (p : ℕ) : ℝ := (if |Real.log (2 * (p : ℝ)/y)| ≤ |h| then 1 else 0) +
    (if |Real.log ((p : ℝ)/y)| ≤ |h| then 1/2 else 0)
  have hb (p : ℕ) : 0 ≤ b p ∧ b p ≤ 2 := by dsimp [b]; split_ifs <;> norm_num
  have ha (p : ℕ) : |(quarticCharacterFive (p : ZMod 5)).re| ≤ 1 := by
    rw [quarticCharacterFive_re]; split_ifs <;> norm_num
  let Y := y * Real.exp |h|
  have hs : (∑ p ∈ Nat.primesLE ⌊Y⌋₊, (|(quarticCharacterFive (p : ZMod 5)).re| *
      Real.log p) * b p) ≤ 2 * (Real.log 4 * Y) := by
    calc _ ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, 2 * Real.log p := by
           apply sum_le_sum
           intro p _
           have hp := Real.log_natCast_nonneg p
           have hprod := mul_le_mul (mul_le_mul_of_nonneg_right (ha p) hp) (hb p).2
             (hb p).1 (by simpa using hp)
           simpa only [one_mul, mul_comm (Real.log p) 2] using hprod
         _ = 2 * Chebyshev.theta Y := by rw [← mul_sum, Chebyshev.theta_eq_sum_primesLE]
         _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (mul_nonneg hy
           (Real.exp_nonneg _))) (by norm_num)
  calc _ ≤ h^2 * Real.exp |h| * (2 * (Real.log 4 * Y)) :=
         mul_le_mul_of_nonneg_left hs (by positivity)
       _ = _ := by
         rw [sq_abs, show 2 * |h| = |h| + |h| by ring, Real.exp_add]
         dsimp only [Y]
         ring

/-- The annular prime crossing mass is integrable against the centered
Gaussian of every variance at every positive scale. -/
theorem quarticAnnularPrimeCrossingMass_integrable_gaussian (y : ℝ) (hy : 0 < y) (v : ℝ≥0) :
    Integrable (quarticAnnularPrimeCrossingMass y) (gaussianReal 0 v) := by
  apply ((gaussianReal_integrable_abs_pow_mul_exp_abs 0 v 2 2).const_mul
    (2 * Real.log 4 * y)).mono' (quarticAnnularPrimeCrossingMass_measurable y).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun h ↦ by
    rw [Real.norm_of_nonneg (quarticAnnularPrimeCrossingMass_nonneg y h)]
    exact quarticAnnularPrimeCrossingMass_le y h hy.le

end RiemannMasullo
