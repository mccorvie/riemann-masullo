module

public import RiemannMasullo.Ch12_TraceGeometric.ThetaDirichletAverage
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Powers of Dirichlet sums supported on primes

Grouping the multinomial expansion by the integer product of the primes gives
coefficients common to every twisting character. Unique factorization separates
the exponent vectors, and each multinomial coefficient is at most the factorial
of the moment order.
-/

open Finset
open scoped Classical

public section

namespace RiemannMasullo

private theorem primeProduct_factorization (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {e : ℕ → ℕ} {k : ℕ} (he : e ∈ piAntidiag P k) :
    ⇑(∏ p ∈ P, p ^ e p).factorization = e := by
  funext q
  rw [Nat.factorization_prod_apply (fun p hp ↦ pow_ne_zero _ (hprime p hp).ne_zero)]
  calc _ = ∑ p ∈ P, if p = q then e p else 0 := by
            apply sum_congr rfl
            intro p hp
            rw [(hprime p hp).factorization_pow, Finsupp.single_apply]
       _ = _ := by
         rw [sum_ite_eq']
         split_ifs with hq
         · rfl
         · exact (not_imp_comm.mp ((mem_piAntidiag.mp he).2 q) hq).symm

/-- The `k`th power of a prime-supported Dirichlet row is a Dirichlet row on
products at most `T^k`. Its coefficient energy is bounded by `k!` times the
`k`th power of the original energy, uniformly in the character and its modulus. -/
theorem dirichletThetaRow_primeProduct_energy (P : Finset ℕ) (T : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hbound : ∀ p ∈ P, p ≤ T) (w : ℕ → ℂ) (k : ℕ) :
    ∃ S : Finset ℕ, ∃ f : ℕ → ℂ, (∀ n ∈ S, n ≤ T^k) ∧
      (∀ {m : ℕ} (χ : DirichletCharacter ℂ m),
        (dirichletThetaRow χ P w)^k = dirichletThetaRow χ S f) ∧
      (∑ n ∈ S, ‖f n‖^2) ≤ (k.factorial : ℝ) * (∑ p ∈ P, ‖w p‖^2)^k := by
  classical
  let A := piAntidiag P k
  let N (e : ℕ → ℕ) := ∏ p ∈ P, p ^ e p
  let b (e : ℕ → ℕ) : ℂ := (Nat.multinomial P e : ℂ) * ∏ p ∈ P, w p ^ e p
  have recover (e : ℕ → ℕ) (he : e ∈ A) : ⇑(N e).factorization = e :=
    primeProduct_factorization P hprime he
  have hinj : Set.InjOn N (↑A : Set (ℕ → ℕ)) := by
    intro e he g hg h
    rw [← recover e he, h, recover g hg]
  refine ⟨A.image N, fun n ↦ b n.factorization, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨e, he, rfl⟩ := mem_image.mp hn
    calc N e ≤ ∏ p ∈ P, T ^ e p := prod_le_prod (fun p hp ↦ Nat.pow_le_pow_left (hbound p hp) _)
         _ = T^k := by rw [prod_pow_eq_pow_sum, (mem_piAntidiag.mp he).1]
  · intro m χ
    rw [dirichletThetaRow, dirichletThetaRow, sum_pow_eq_sum_piAntidiag, sum_image hinj]
    apply sum_congr rfl
    intro e he
    rw [recover e he]
    dsimp only [N, b]
    push_cast
    simp only [map_prod, map_pow, mul_pow, prod_mul_distrib]
    ring
  · rw [sum_image hinj, sum_pow_eq_sum_piAntidiag, mul_sum]
    apply sum_le_sum
    intro e he
    change ‖b (N e).factorization‖^2 ≤ _
    rw [recover e he]
    have hmulti : (Nat.multinomial P e : ℝ) ≤ k.factorial := by
      exact_mod_cast (show Nat.multinomial P e ≤ k.factorial by
        rw [Nat.multinomial, (mem_piAntidiag.mp he).1]
        exact Nat.div_le_self ..)
    have hnorm : ‖∏ p ∈ P, w p ^ e p‖^2 = ∏ p ∈ P, (‖w p‖^2) ^ e p := by
      rw [norm_prod, ← prod_pow]
      apply prod_congr rfl
      intro p _
      rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    dsimp only [b]
    rw [norm_mul, Complex.norm_natCast, mul_pow, hnorm, pow_two, mul_assoc]
    exact mul_le_mul_of_nonneg_right hmulti (by positivity)

end RiemannMasullo
