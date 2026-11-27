module

public import RiemannMasullo.ForMathlib.NumberTheory.QuadraticLargeSieve
import RiemannMasullo.ForMathlib.NumberTheory.JacobiPower
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Even moments of prime-supported Jacobi sums -/

@[expose] public section

open Finset

namespace RiemannMasullo

private theorem jacobiPrime_restore_two (k : ℕ) (P U : Finset ℕ) (b : ℕ → ℝ) :
    ∑ m ∈ U, (∑ p ∈ P, b p * (jacobiSym m p : ℝ))^(2*k) ≤
      (2:ℝ)^(2*k-1) * ((∑ m ∈ U, (∑ p ∈ P.erase 2, b p * (jacobiSym m p : ℝ))^(2*k)) +
        U.card * (∑ p ∈ P, b p^2)^k) := by
  have heven : Even (2*k) := ⟨k, by omega⟩
  by_cases h2 : 2 ∈ P
  · have hb : b 2 ^ 2 ≤ ∑ p ∈ P, b p ^ 2 := single_le_sum (fun i _ ↦ sq_nonneg (b i)) h2
    have ht (m : ℕ) : (b 2 * (jacobiSym m 2 : ℝ))^(2*k) ≤ (∑ p ∈ P, b p^2)^k := by
      rw [pow_mul]
      apply pow_le_pow_left₀ (sq_nonneg _) _ k
      have hs : (jacobiSym m 2 : ℝ)^2 ≤ 1 := by
        rcases jacobiSym.trichotomy m 2 with he | he | he <;> rw [he] <;> norm_num
      calc _ = b 2 ^ 2 * (jacobiSym m 2 : ℝ)^2 := mul_pow ..
           _ ≤ b 2 ^ 2 * 1 := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
           _ ≤ _ := by simpa only [mul_one] using hb
    calc _ ≤ ∑ m ∈ U, (2:ℝ)^(2*k-1) * ((∑ p ∈ P.erase 2, b p * (jacobiSym m p : ℝ))^(2*k) +
              (∑ p ∈ P, b p^2)^k) := by
              apply sum_le_sum
              intro m _
              rw [← sum_erase_add (s := P) (fun p ↦ b p * (jacobiSym m p : ℝ)) h2]
              exact (Even.add_pow_le heven ..).trans
                (mul_le_mul_of_nonneg_left (add_le_add le_rfl (ht m)) (by positivity))
         _ = _ := by rw [← mul_sum, sum_add_distrib]; simp
  · rw [erase_eq_of_notMem h2]
    have hs : 0 ≤ ∑ m ∈ U, (∑ p ∈ P, b p * (jacobiSym m p : ℝ))^(2*k) :=
      sum_nonneg fun _ _ ↦ heven.pow_nonneg _
    have he : 0 ≤ (U.card:ℝ) * (∑ p ∈ P, b p^2)^k :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sum_nonneg fun p _ ↦ sq_nonneg _) _)
    exact (le_add_of_nonneg_right he).trans
      (le_mul_of_one_le_left (add_nonneg hs he) (one_le_pow₀ (by norm_num)))

/-- The even moment of order `2*k` of a real prime-supported Jacobi sum. The
numerators may range over any subset of the positive odd squarefree integers through
`M` coprime to the prime support. The grouped coefficient length is `T^k`. -/
theorem jacobiPrime_evenMoment (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C > (0 : ℝ), ∀ (T M : ℕ), 0 < T → 0 < M → ∀ (P U : Finset ℕ),
      P ⊆ Nat.primesLE T → U ⊆ oddSquarefreeLE M →
      (∀ m ∈ U, ∀ p ∈ P, m.Coprime p) → ∀ b : ℕ → ℝ,
      ∑ m ∈ U, (∑ p ∈ P, b p * (jacobiSym m p : ℝ)) ^ (2*k) ≤
        C * ((M : ℝ) * (T : ℝ)^k)^η * (M + (T : ℝ)^k) * (∑ p ∈ P, b p^2)^k := by
  obtain ⟨C, hC, hsieve⟩ := heathBrown_quadraticLargeSieve_transpose η hη
  let A := (4:ℝ)^k * k.factorial
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(2:ℝ)^(2*k-1)*(C*A+1), by positivity, ?_⟩
  intro T M hT hM P U hP hU hcop b
  let P' := P.erase 2
  let N := T^k
  let W := oddSquarefreeLE N
  let a := JacobiPower.coefficient k P' b
  let E := (∑ p ∈ P, b p^2)^k
  have hE : 0 ≤ E := pow_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) _
  have hPP : P' ⊆ P := erase_subset _ _
  have hp (p : ℕ) (h : p ∈ P') := Nat.prime_of_mem_primesLE (hP (hPP h))
  have hodd (p : ℕ) (h : p ∈ P') : Odd p :=
    (hp p h).eq_two_or_odd'.resolve_left (mem_erase.mp h).1
  have hsupp (n : ℕ) (h : a n ≠ 0) : n ∈ W := by
    obtain ⟨ho, hs, hpos, hle⟩ := JacobiPower.coefficient_support k P' b T hp hodd
      (fun p h ↦ Nat.le_of_mem_primesLE (hP (hPP h))) h
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpos, hle⟩, ho, hs⟩
  have heq (m : ℕ) (h : m ∈ U) : (∑ p ∈ P', b p * (jacobiSym m p : ℝ)) ^ (2*k) =
      (∑ n ∈ W, a n * (jacobiSym m n : ℝ))^2 := by
    rw [Nat.mul_comm 2 k, pow_mul, JacobiPower.expansion k P' b m hp
      (fun p h' ↦ hcop m h p (hPP h')) W hsupp]
  have hcoeff : ∑ n ∈ W, a n^2 ≤ A*E := by
    apply (JacobiPower.energy k P' b hp W).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ sq_nonneg _)
      (sum_le_sum_of_subset_of_nonneg hPP (fun i _ _ ↦ sq_nonneg (b i))) k) hA.le
  have hsum : ∑ m ∈ U, (∑ p ∈ P', b p * (jacobiSym m p : ℝ))^(2*k) ≤
      C*((M:ℝ)*N)^η*(M+N:ℝ)*(A*E) := by
    calc _ = ∑ m ∈ U, (∑ n ∈ W, a n * (jacobiSym m n : ℝ))^2 := sum_congr rfl heq
         _ ≤ ∑ m ∈ oddSquarefreeLE M, (∑ n ∈ W, a n * (jacobiSym m n : ℝ))^2 :=
           sum_le_sum_of_subset_of_nonneg hU fun _ _ _ ↦ sq_nonneg _
         _ ≤ _ := (hsieve M N hM (pow_pos hT k) a).trans
           (mul_le_mul_of_nonneg_left hcoeff (by positivity))
  have hsize : U.card ≤ M := by
    have hsub : U ⊆ Ioc 0 M := fun m hm ↦ (mem_filter.mp (hU hm)).1
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  have hM1 : 1 ≤ (M:ℝ) := by exact_mod_cast hM
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast (pow_pos hT k)
  have hr := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM1 hN1) hη.le
  have hminor : (U.card:ℝ) * E ≤ ((M:ℝ)*N)^η*(M+N)*E :=
    mul_le_mul_of_nonneg_right
      ((show (U.card:ℝ) ≤ M+N by exact_mod_cast (hsize.trans (Nat.le_add_right M N))).trans
        (le_mul_of_one_le_left (by positivity) hr)) hE
  apply (jacobiPrime_restore_two k P U b).trans
  calc _ ≤ (2:ℝ)^(2*k-1)*(C*((M:ℝ)*N)^η*(M+N)*(A*E) + ((M:ℝ)*N)^η*(M+N)*E) :=
         mul_le_mul_of_nonneg_left (add_le_add hsum hminor) (by positivity)
       _ = _ := by dsimp only [E, N]; push_cast; ring

end RiemannMasullo
