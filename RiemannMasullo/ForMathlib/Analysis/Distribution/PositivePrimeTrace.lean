module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositiveTests
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Positive-time prime Poisson sums and the von Mangoldt distribution -/

public noncomputable section
open Set Function
open scoped Topology
namespace RiemannMasullo

private theorem positiveTest_eq_zero_of_nonpos (f : PositiveTimeTest) {t : ℝ} (ht : t ≤ 0) :
    f t = 0 := by
  by_contra h
  exact (not_lt_of_ge ht) (f.tsupport_subset (subset_tsupport f h))

/-- A compact positive-time test gives a finitely supported von Mangoldt sum. -/
theorem positiveTest_vonMangoldt_finite (f : PositiveTimeTest) :
    HasFiniteSupport (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * f (Real.log n)) := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.bddAbove
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp R)
  apply (Finset.range B).finite_toSet.subset
  intro n hn
  have hf : f (Real.log n) ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    exact hf (by simpa only [Nat.cast_zero, Real.log_zero] using positiveTest_eq_zero_of_nonpos f le_rfl)
  have hlog := hR (subset_tsupport f hf)
  have hnb : (n : ℝ) < B := by
    calc
      (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn0)).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hlog
      _ < B := hB
  exact Finset.mem_range.mpr (by exact_mod_cast hnb)

private theorem positiveTest_prime_power_term (f : PositiveTimeTest) (p : Nat.Primes) (k : ℕ) :
    (ArithmeticFunction.vonMangoldt (p ^ (k+1)) : ℂ) * f (Real.log (p ^ (k+1) : ℕ)) =
      (Real.log (p : ℝ) : ℂ) * f (Real.log p * (k+1)) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime p.property]
  congr 1
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one, mul_comm]

/-- Integer Poisson sampling of a positive-time test has only positive-power terms. -/
theorem positiveTest_prime_lattice_eq_positive_powers (f : PositiveTimeTest) (p : Nat.Primes) :
    (∑' k : ℤ, f (Real.log p * k)) = ∑' k : ℕ, f (Real.log p * (k+1)) := by
  have hg : Summable (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * f (Real.log n)) :=
    summable_of_hasFiniteSupport (positiveTest_vonMangoldt_finite f)
  have hi : Function.Injective (fun k : ℕ ↦ (p : ℕ) ^ (k+1)) := by
    intro a b h
    exact Nat.succ.inj (Nat.pow_right_injective p.property.one_lt h)
  have hpows := (hg.comp_injective hi).congr (positiveTest_prime_power_term f p)
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hLn : (Real.log (p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hs : Summable (fun k : ℕ ↦ f (Real.log p * (k+1))) :=
    (summable_mul_left_iff hLn).mp hpows
  have hz : f (Real.log (p : ℝ) * (0 : ℤ)) = 0 := by
    exact positiveTest_eq_zero_of_nonpos f (by simp)
  have hneg : ∀ k : ℕ, f (Real.log (p : ℝ) * (-(k+1 : ℤ))) = 0 := by
    intro k
    apply positiveTest_eq_zero_of_nonpos
    apply mul_nonpos_of_nonneg_of_nonpos hL.le
    exact_mod_cast (show -(k+1 : ℤ) ≤ 0 by omega)
  have hn : Summable (fun k : ℕ ↦ f (Real.log (p : ℝ) * (-(k+1 : ℤ)))) := by
    simp only [hneg, summable_zero]
  have h := tsum_of_add_one_of_neg_add_one (f := fun k : ℤ ↦ f (Real.log p * k))
    (by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hs)
    (by simpa only [Int.cast_neg] using hn)
  have hnz : (∑' k : ℕ, f (Real.log (p : ℝ) * (-(k+1 : ℤ)))) = 0 := by
    simp only [hneg, tsum_zero]
  simp only [Int.cast_neg] at h
  rw [hz, hnz, add_zero, add_zero] at h
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using h

/-- The prime Poisson trace distribution equals the von Mangoldt distribution.
All sums are finite on a compact positive-time test. -/
theorem positiveTest_prime_poisson_eq_vonMangoldt (f : PositiveTimeTest) :
    (∑' p : Nat.Primes, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k)) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f (Real.log n) := by
  let g (n : ℕ) := (ArithmeticFunction.vonMangoldt n : ℂ) * f (Real.log n)
  have hg : Summable g := summable_of_hasFiniteSupport (positiveTest_vonMangoldt_finite f)
  have hs : Function.support g ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    exact hn (by simp only [g, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h,
      Complex.ofReal_zero, zero_mul])
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hg hs]
  apply tsum_congr
  intro p
  rw [positiveTest_prime_lattice_eq_positive_powers, ← tsum_mul_left]
  apply tsum_congr
  intro k
  exact (positiveTest_prime_power_term f p k).symm

end RiemannMasullo
