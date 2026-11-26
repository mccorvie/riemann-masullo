module

public import RiemannMasullo.Ch13_ZerosHecke.DirichletJacobiCellEnergy
import RiemannMasullo.Ch12_TraceGeometric.DirichletPrimeProductEnergy

/-!
# Higher conductor moments of prime sums in rational Jacobi cells

Grouping ordered prime products by their integer product bounds the coefficient energy of
the `k`-th power by `k!` times the original energy to the power `k`. The primitive-character
large sieve then sees an interval of length at most `T^k` for primes up to `T`.
-/

open Finset ArithmeticFunction
open scoped Classical

public noncomputable section

namespace RiemannMasullo

/-- The complex rational first-prime Riesz sum in a Jacobi cell, with its factor four.
The sign selected by `true` is positive in each coordinate. -/
@[expose] def dirichletJacobiPrimeCellRow {m : ℕ} (χ : DirichletCharacter ℂ m)
    (T : ℕ) (x : ℝ) (u v : ℕ) (a b : Bool) : ℂ :=
  4 * dirichletThetaRow χ ((Nat.primesLE T).filter (fun n ↦
      (jacobiSym u n : ℝ) = (if a then 1 else -1) ∧
      (jacobiSym v n : ℝ) = (if b then 1 else -1)))
    (fun n ↦ ((vonMangoldt n * max (x - n) 0 : ℝ) : ℂ))

/-- The primitive conductor large sieve for the `2k`-th moment of a prime-supported
Dirichlet polynomial, for arbitrary complex coefficients. -/
theorem dirichletThetaRow_primes_primitive_moment (k C T : ℕ) (hC : 0 < C)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (hbound : ∀ p ∈ P, p ≤ T) (w : ℕ → ℂ) :
    (∑ m ∈ range C, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
        ‖dirichletThetaRow χ P w‖ ^ (2 * k)) ≤
      (k.factorial : ℝ) * ((C : ℝ)^2 + Real.pi * (T : ℝ)^k) * (∑ p ∈ P, ‖w p‖^2)^k := by
  obtain ⟨S, f, hS, hid, he⟩ := dirichletThetaRow_primeProduct_energy P T hprime hbound w k
  have hr {m : ℕ} (χ : DirichletCharacter ℂ m) :
      ‖dirichletThetaRow χ P w‖ ^ (2 * k) = ‖dirichletThetaRow χ S f‖^2 := by
    rw [Nat.mul_comm 2 k, pow_mul, ← norm_pow, hid χ]
  have hl := dirichletThetaRow_primitive_large_sieve C hC S f (Nat.zero_le (T^k))
    (fun n hn ↦ ⟨Nat.zero_le n, hS n hn⟩)
  simp only [Nat.cast_zero, sub_zero, Nat.cast_pow] at hl
  simp_rw [hr]
  apply le_trans _ (hl.trans ?_)
  · apply sum_le_sum
    intro m _
    apply le_mul_of_one_le_left (sum_nonneg (fun χ _ ↦ sq_nonneg _))
    exact (one_le_div (by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos m))).mpr
      (by exact_mod_cast Nat.totient_le (m + 1))
  · calc
      _ ≤ ((C : ℝ)^2 + Real.pi * (T : ℝ)^k) * ((k.factorial : ℝ) * (∑ p ∈ P, ‖w p‖^2)^k) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring

private theorem dirichletJacobiPrime_weight_energy (T : ℕ) (hT : 1 ≤ T) (x : ℝ) (hx : x ≤ T) :
    (∑ p ∈ Nat.primesLE T, ‖((vonMangoldt p * max (x - p) 0 : ℝ) : ℂ)‖ ^ 2) ≤
      3 * ((T : ℝ)^3 * Real.log (2 * T)) := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have htheta : (∑ p ∈ Nat.primesLE T, Real.log p) ≤ 3 * (T : ℝ) := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    apply (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg T)).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg T)
    linarith [Real.log_le_sub_one_of_pos (show 0 < (4 : ℝ) by norm_num)]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE T, Real.log p * (Real.log (2 * T) * (T : ℝ)^2) := by
      apply sum_le_sum
      intro p hp
      have hp' := Nat.prime_of_mem_primesLE hp
      have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp'.one_le
      have hpT : (p : ℝ) ≤ T := by exact_mod_cast Nat.le_of_mem_primesLE hp
      have hw : 0 ≤ max (x - (p : ℝ)) 0 := le_max_right _ _
      have hcut : max (x - (p : ℝ)) 0 ≤ T :=
        max_le ((sub_le_self _ (Nat.cast_nonneg p)).trans hx) (Nat.cast_nonneg T)
      have hilog : Real.log p ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
      rw [vonMangoldt_apply_prime hp', Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Real.log_nonneg hp₁) hw), mul_pow, ← mul_assoc]
      exact mul_le_mul (by simpa only [pow_two] using
        mul_le_mul_of_nonneg_left hilog (Real.log_nonneg hp₁))
        (pow_le_pow_left₀ hw hcut 2) (sq_nonneg _) (mul_nonneg (Real.log_nonneg hp₁) hlog)
    _ = (∑ p ∈ Nat.primesLE T, Real.log p) * (Real.log (2 * T) * (T : ℝ)^2) := (sum_mul ..).symm
    _ ≤ (3 * T) * (Real.log (2 * T) * (T : ℝ)^2) :=
      mul_le_mul_of_nonneg_right htheta (mul_nonneg hlog (sq_nonneg _))
    _ = _ := by ring

/-- Summing the `2k`-th powers of the prime Jacobi cells over all four signs and
all primitive characters of conductor at most `C`. The auxiliary integers are arbitrary. -/
theorem dirichletJacobiPrimeCellRow_primitive_moment (k C T : ℕ) (_hk : 1 ≤ k)
    (hC : 0 < C) (hT : 1 ≤ T) (x : ℝ) (hx : x ≤ T) (u v : ℕ) :
    (∑ m ∈ range C, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
      ∑ s : Bool × Bool, ‖dirichletJacobiPrimeCellRow χ T x u v s.1 s.2‖ ^ (2 * k)) ≤
      (4 * (k.factorial : ℝ) * 48^k) * ((C : ℝ)^2 + Real.pi * (T : ℝ)^k) *
        ((T : ℝ)^3 * Real.log (2 * T))^k := by
  let A := (C : ℝ)^2 + Real.pi * (T : ℝ)^k
  let D := (T : ℝ)^3 * Real.log (2 * T)
  let P (m : ℕ) := (univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive)
  let cell (s : Bool × Bool) := (Nat.primesLE T).filter fun n ↦
    (jacobiSym u n : ℝ) = (if s.1 then 1 else -1) ∧ (jacobiSym v n : ℝ) = (if s.2 then 1 else -1)
  let f (n : ℕ) : ℂ := (vonMangoldt n * max (x - n) 0 : ℝ)
  have hone (s : Bool × Bool) :
      (∑ m ∈ range C, ∑ χ ∈ P m, ‖dirichletJacobiPrimeCellRow χ T x u v s.1 s.2‖ ^ (2 * k)) ≤
        ((k.factorial : ℝ) * 48^k) * A * D^k := by
    have he : ∑ p ∈ cell s, ‖f p‖^2 ≤ 3 * D :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p _ _ ↦ sq_nonneg _)).trans
        (dirichletJacobiPrime_weight_energy T hT x hx)
    have hm := dirichletThetaRow_primes_primitive_moment k C T hC (cell s)
      (fun p hp ↦ Nat.prime_of_mem_primesLE (mem_filter.mp hp).1)
      (fun p hp ↦ Nat.le_of_mem_primesLE (mem_filter.mp hp).1) f
    change (∑ m ∈ range C, ∑ χ ∈ P m, ‖(4 : ℂ) * dirichletThetaRow χ (cell s) f‖ ^ (2 * k)) ≤ _
    simp only [norm_mul, Complex.norm_ofNat, mul_pow, ← mul_sum]
    calc
      _ ≤ 4^(2*k) * ((k.factorial : ℝ) * A * (3 * D)^k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hm.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sum_nonneg (fun p _ ↦ sq_nonneg _)) he k)
          (mul_nonneg (Nat.cast_nonneg _) (by positivity)))
      _ = _ := by
        rw [pow_mul, mul_pow, show (48 : ℝ)^k = (4^2)^k * 3^k by rw [← mul_pow]; norm_num]
        ring
  calc
    _ = ∑ m ∈ range C, ∑ s : Bool × Bool, ∑ χ ∈ P m,
        ‖dirichletJacobiPrimeCellRow χ T x u v s.1 s.2‖ ^ (2*k) :=
      sum_congr rfl (fun m _ ↦ sum_comm)
    _ = ∑ s : Bool × Bool, ∑ m ∈ range C, ∑ χ ∈ P m,
        ‖dirichletJacobiPrimeCellRow χ T x u v s.1 s.2‖ ^ (2*k) := sum_comm
    _ ≤ ∑ _s : Bool × Bool, ((k.factorial : ℝ) * 48^k) * A * D^k :=
      sum_le_sum (fun s _ ↦ hone s)
    _ = _ := by simp [A, D, Fintype.card_prod]; ring

end RiemannMasullo
