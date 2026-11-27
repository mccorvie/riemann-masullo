module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Data.Finset.NatDivisors

public section

namespace RiemannMasullo.Selberg

private theorem jordan_mul (p : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    jordan p (a * b) = jordan p a * jordan p b := by
  simp only [jordan, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b),
    hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]
  ring

private theorem sum_jordan_prime_pow (p : ℝ) {q : ℕ} (hq : q.Prime) (k : ℕ) :
    ∑ d ∈ (q ^ k).divisors, jordan p d = ((q ^ k : ℕ) : ℝ) ^ p := by
  rw [Nat.sum_divisors_prime_pow hq]
  induction k with
  | zero => simp [jordan]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq.pos
    have hpow := (Real.rpow_pos_of_pos hqpos p).ne'
    rw [jordan, Nat.primeFactors_pow_succ, hq.primeFactors, Finset.prod_singleton,
      pow_succ, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) hqpos.le, Real.rpow_neg hqpos.le]
    field_simp
    ring

private theorem sum_jordan_mul (p : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    ∑ d ∈ (a * b).divisors, jordan p d =
      (∑ d ∈ a.divisors, jordan p d) * (∑ e ∈ b.divisors, jordan p e) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hab.mul_injOn_divisors, Finset.sum_product]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun e he ↦ ?_
  exact jordan_mul p ((hab.of_dvd_left (Nat.dvd_of_mem_divisors hd)).of_dvd_right
    (Nat.dvd_of_mem_divisors he))

/-- Card 10. For p > 0 the sum of the Jordan totient over the divisors of a positive integer n is
nᵖ, and its value at n lies between zero and nᵖ.
Titchmarsh, §10.11, p. 271, generalized totients. -/
theorem jordan_sum (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : 0 < n) :
    (∑ r ∈ n.divisors, jordan p r) = (n : ℝ)^p ∧
      0 ≤ jordan p n ∧ jordan p n ≤ (n : ℝ)^p := by
  constructor
  · induction n using Nat.recOnPrimeCoprime with
    | zero => omega
    | prime_pow q k hq => exact sum_jordan_prime_pow p hq k
    | coprime a b ha hb hab iha ihb =>
      rw [sum_jordan_mul p hab, iha (by omega), ihb (by omega), Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  · have hfactor (q : ℕ) (hq : q ∈ n.primeFactors) : 0 ≤ 1 - (q : ℝ) ^ (-p) := by
      apply sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos _ (neg_nonpos.mpr hp.le))
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
    unfold jordan
    have hn_nonneg := Real.rpow_nonneg (Nat.cast_nonneg n) p
    refine ⟨mul_nonneg hn_nonneg (Finset.prod_nonneg hfactor), mul_le_of_le_one_right hn_nonneg ?_⟩
    exact Finset.prod_le_one₀ hfactor fun q _ ↦ sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg q) _)

end RiemannMasullo.Selberg
