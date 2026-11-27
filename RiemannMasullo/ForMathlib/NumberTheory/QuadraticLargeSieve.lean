module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.PrimeCounting
import RiemannMasullo.ForMathlib.NumberTheory.JacobiCube
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # The quadratic large sieve on positive odd squarefree integers -/

@[expose] public section

open Finset

namespace RiemannMasullo

/-- Positive odd squarefree integers through the inclusive cutoff. -/
def oddSquarefreeLE (N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n ↦ Odd n ∧ Squarefree n

/-- Classical input: D. R. Heath-Brown, *A mean value estimate for real character sums*,
Acta Arithmetica 72 (1995), Theorem 1, p. 237, doi:10.4064/aa-72-3-235-275.
Both indices run over positive odd squarefree integers, the numerator is the coefficient
index, and the implicit constant is uniform in the two positive cutoffs and coefficients. -/
theorem heathBrown_quadraticLargeSieve (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (M N : ℕ), 0 < M → 0 < N → ∀ a : ℕ → ℂ,
      ∑ m ∈ oddSquarefreeLE M, ‖∑ n ∈ oddSquarefreeLE N, a n * (jacobiSym n m : ℂ)‖ ^ 2 ≤
        C * ((M : ℝ) * N) ^ ε * (M + N : ℝ) * ∑ n ∈ oddSquarefreeLE N, ‖a n‖ ^ 2 := by
  sorry

private theorem sum_squares_transpose {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x : κ → ℝ, ∑ i ∈ s, (∑ j ∈ t, x j * K i j) ^ 2 ≤ B * ∑ j ∈ t, x j ^ 2)
    (b : ι → ℝ) :
    ∑ j ∈ t, (∑ i ∈ s, b i * K i j) ^ 2 ≤ B * ∑ i ∈ s, b i ^ 2 := by
  let y (j : κ) := ∑ i ∈ s, b i * K i j
  let z (i : ι) := ∑ j ∈ t, y j * K i j
  let E := ∑ j ∈ t, y j ^ 2
  change E ≤ B * ∑ i ∈ s, b i ^ 2
  have hE : E = ∑ i ∈ s, b i * z i := by
    change (∑ j ∈ t, y j ^ 2) = ∑ i ∈ s, b i * ∑ j ∈ t, y j * K i j
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    conv_lhs => rw [pow_two]; arg 2; change ∑ i ∈ s, b i * K i j
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  have h0 : 0 ≤ E := sum_nonneg fun _ _ ↦ sq_nonneg _
  rcases h0.eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hB (sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hcs : E ^ 2 ≤ (∑ i ∈ s, b i ^ 2) * ∑ i ∈ s, z i ^ 2 := by
    rw [hE]
    exact sum_mul_sq_le_sq_mul_sq s b z
  have hsq := hcs.trans <| mul_le_mul_of_nonneg_left (h y) (sum_nonneg fun _ _ ↦ sq_nonneg _)
  change E ^ 2 ≤ (∑ i ∈ s, b i ^ 2) * (B * E) at hsq
  apply (le_of_mul_le_mul_right · hpos)
  calc E * E = E ^ 2 := (pow_two _).symm
       _ ≤ _ := hsq
       _ = _ := by ring

/-- With real coefficients the numerator may equally be the outer index. Finite matrix
duality after interchanging the cutoffs preserves the large-sieve constant. -/
theorem heathBrown_quadraticLargeSieve_transpose (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (M N : ℕ), 0 < M → 0 < N → ∀ a : ℕ → ℝ,
      ∑ m ∈ oddSquarefreeLE M, (∑ n ∈ oddSquarefreeLE N, a n * (jacobiSym m n : ℝ)) ^ 2 ≤
        C * ((M : ℝ) * N) ^ ε * (M + N : ℝ) * ∑ n ∈ oddSquarefreeLE N, a n ^ 2 := by
  obtain ⟨C, hC, h⟩ := heathBrown_quadraticLargeSieve ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN a
  apply sum_squares_transpose (oddSquarefreeLE N) (oddSquarefreeLE M)
    (fun n m ↦ (jacobiSym m n : ℝ)) (by positivity) _ a
  intro x
  have hd := h N M hN hM fun m ↦ (x m : ℂ)
  have castSum (n : ℕ) :
      ∑ m ∈ oddSquarefreeLE M, (x m : ℂ) * (jacobiSym m n : ℂ) =
        ((∑ m ∈ oddSquarefreeLE M, x m * (jacobiSym m n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  simpa only [castSum, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_comm (N : ℝ) M,
    add_comm (N : ℝ) M] using hd

private theorem sixthMoment_restore_two (P U : Finset ℕ) (b : ℕ → ℝ) :
    ∑ q ∈ U, (∑ p ∈ P, b p * (jacobiSym q p : ℝ))^6 ≤
      32 * ((∑ q ∈ U, (∑ p ∈ P.erase 2, b p * (jacobiSym q p : ℝ))^6) +
        U.card * (∑ p ∈ P, b p^2)^3) := by
  by_cases h2 : 2 ∈ P
  · have hb : b 2 ^ 2 ≤ ∑ p ∈ P, b p ^ 2 := single_le_sum (fun i _ ↦ sq_nonneg (b i)) h2
    have ht (q : ℕ) : (b 2 * (jacobiSym q 2 : ℝ))^6 ≤ (∑ p ∈ P, b p^2)^3 := by
      have hs : (jacobiSym q 2 : ℝ)^6 ≤ 1 := by
        rcases jacobiSym.trichotomy q 2 with he | he | he <;> rw [he] <;> norm_num
      calc _ = b 2 ^ 6 * (jacobiSym q 2 : ℝ)^6 := mul_pow ..
           _ ≤ b 2 ^ 6 * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
           _ = (b 2^2)^3 := by ring
           _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hb 3
    calc _ ≤ ∑ q ∈ U, 32 * ((∑ p ∈ P.erase 2, b p * (jacobiSym q p : ℝ))^6 +
              (∑ p ∈ P, b p^2)^3) := by
              apply sum_le_sum
              intro q _
              rw [← sum_erase_add (s := P) (fun p ↦ b p * (jacobiSym q p : ℝ)) h2]
              apply (Even.add_pow_le (by decide : Even 6)).trans
              norm_num
              linarith [ht q]
         _ = _ := by rw [← mul_sum, sum_add_distrib]; simp
  · rw [erase_eq_of_notMem h2]
    have hs : 0 ≤ ∑ q ∈ U, (∑ p ∈ P, b p * (jacobiSym q p : ℝ))^6 :=
      sum_nonneg fun q _ ↦ by positivity
    have he : 0 ≤ (U.card:ℝ) * (∑ p ∈ P, b p^2)^3 :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sum_nonneg fun p _ ↦ sq_nonneg _) _)
    linarith

/-- A sixth moment of a real prime-supported Jacobi sum. The outer set is any collection
of positive odd squarefree numerators through `M` coprime to the primes in `P`. Cubing
groups the odd-prime weights at squarefree indices through `T^3`. The final term restores
the possible prime 2. -/
theorem jacobiPrime_sixthMoment (η : ℝ) (hη : 0 < η) :
    ∃ C > (0 : ℝ), ∀ (T M : ℕ), 0 < T → 0 < M → ∀ (P U : Finset ℕ),
      P ⊆ Nat.primesLE T → U ⊆ oddSquarefreeLE M →
      (∀ q ∈ U, ∀ p ∈ P, q.Coprime p) → ∀ b : ℕ → ℝ,
      ∑ q ∈ U, (∑ p ∈ P, b p * (jacobiSym q p : ℝ)) ^ 6 ≤
        32 * (C * ((M : ℝ) * T^3) ^ η * (M + (T : ℝ)^3) *
          (15 * (∑ p ∈ P, b p ^ 2)^3) + U.card * (∑ p ∈ P, b p ^ 2)^3) := by
  obtain ⟨C, hC, hsieve⟩ := heathBrown_quadraticLargeSieve_transpose η hη
  refine ⟨C, hC, ?_⟩
  intro T M hT hM P U hP hU hcop b
  let P' := P.erase 2
  let N := T^3
  let W := oddSquarefreeLE N
  let a := JacobiCube.coefficient P' b
  have hPP : P' ⊆ P := erase_subset _ _
  have hp (p : ℕ) (h : p ∈ P') := Nat.prime_of_mem_primesLE (hP (hPP h))
  have hodd (p : ℕ) (h : p ∈ P') : Odd p :=
    (hp p h).eq_two_or_odd'.resolve_left (mem_erase.mp h).1
  have hsupp (n : ℕ) (h : a n ≠ 0) : n ∈ W := by
    obtain ⟨ho, hs, hpos, hle⟩ := JacobiCube.coefficient_support P' b T hp hodd
      (fun p h ↦ Nat.le_of_mem_primesLE (hP (hPP h))) h
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpos, hle⟩, ho, hs⟩
  have hx (q : ℕ) (h : q ∈ U) :
      (∑ p ∈ P', b p * (jacobiSym q p : ℝ)) ^ 6 = (∑ n ∈ W, a n * (jacobiSym q n : ℝ)) ^ 2 := by
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul,
      JacobiCube.expansion P' b q hp (fun p h' ↦ hcop q h p (hPP h')) W hsupp]
  have hcoeff : ∑ n ∈ W, a n^2 ≤ 15 * (∑ p ∈ P, b p^2)^3 := by
    apply (JacobiCube.energy P' b hp W).trans
    have hE : 0 ≤ ∑ p ∈ P', b p^2 := sum_nonneg fun p _ ↦ sq_nonneg (b p)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE
      (sum_le_sum_of_subset_of_nonneg hPP (fun i _ _ ↦ sq_nonneg (b i))) 3) (by norm_num)
  have hoddSum : ∑ q ∈ U, (∑ p ∈ P', b p * (jacobiSym q p : ℝ))^6 ≤
      C * ((M : ℝ) * N)^η * (M + N : ℝ) * (15 * (∑ p ∈ P, b p^2)^3) := by
    calc _ = ∑ q ∈ U, (∑ n ∈ W, a n * (jacobiSym q n : ℝ))^2 := sum_congr rfl hx
         _ ≤ ∑ q ∈ oddSquarefreeLE M, (∑ n ∈ W, a n * (jacobiSym q n : ℝ))^2 :=
           sum_le_sum_of_subset_of_nonneg hU fun _ _ _ ↦ sq_nonneg _
         _ ≤ _ := (hsieve M N hM (pow_pos hT 3) a).trans
           (mul_le_mul_of_nonneg_left hcoeff (by positivity))
  apply (sixthMoment_restore_two P U b).trans
  simp only [N, Nat.cast_pow] at hoddSum
  exact mul_le_mul_of_nonneg_left (add_le_add hoddSum le_rfl) (by norm_num)

end RiemannMasullo
