module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Counting primitive Dirichlet characters

The conductor decomposition expresses Euler's totient as the sum of the primitive
character counts over the divisors of each positive level. Counting how often a
small conductor can occur gives a uniform lower bound of Q²/1024 for the number
of primitive complex characters of levels 1 through Q. This elementary estimate
supplies the denominator in large-sieve bounds for the proportion of exceptions.
-/

open Finset
open scoped Classical

public noncomputable section
namespace DirichletCharacter

/-- The number of primitive complex Dirichlet characters of level n. -/
@[expose] def primitiveCount (n : ℕ) : ℕ :=
  Nat.card {χ : DirichletCharacter ℂ n // χ.IsPrimitive}

/-- There are at most φ(n) primitive characters of a positive level n. -/
theorem primitiveCount_le_totient (n : ℕ) [NeZero n] : primitiveCount n ≤ n.totient := by
  rw [← card_eq_totient_of_hasEnoughRootsOfUnity ℂ n]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- Each character is induced from a unique primitive character at a divisor of its level. -/
theorem totient_eq_sum_primitiveCount (n : ℕ) [NeZero n] :
    n.totient = ∑ d ∈ n.divisors, primitiveCount d := by
  let B (d : n.divisors) := {χ : DirichletCharacter ℂ d.val // χ.IsPrimitive}
  let (d : n.divisors) : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  have (d : n.divisors) : Finite (B d) := by dsimp [B]; infer_instance
  let lift (p : (d : n.divisors) × B d) : DirichletCharacter ℂ n :=
    p.2.val.changeLevel (Nat.dvd_of_mem_divisors p.1.property)
  have surj : Function.Surjective lift := fun χ ↦
    ⟨⟨⟨χ.conductor, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne n⟩⟩,
      ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩, χ.changeLevel_primitiveCharacter⟩
  have inj : Function.Injective lift := by
    rintro ⟨d, χ⟩ ⟨e, ψ⟩ h
    have he := congrArg DirichletCharacter.conductor h
    change (χ.val.changeLevel _).conductor = (ψ.val.changeLevel _).conductor at he
    rw [conductor_changeLevel, conductor_changeLevel, χ.property, ψ.property] at he
    obtain rfl : d = e := Subtype.ext he
    have hχ : χ = ψ := Subtype.ext (changeLevel_injective (Nat.dvd_of_mem_divisors d.property) h)
    rw [hχ]
  have h := (Nat.card_congr (Equiv.ofBijective lift ⟨inj, surj⟩)).symm
  rw [card_eq_totient_of_hasEnoughRootsOfUnity, Nat.card_sigma] at h
  change n.totient = ∑ d : n.divisors, primitiveCount d.val at h
  simpa only [Finset.sum_coe_sort] using h

private theorem sum_divisors_through (Q : ℕ) (f : ℕ → ℕ) :
    (∑ n ∈ Ioc 0 Q, ∑ d ∈ n.divisors, f d) = ∑ d ∈ Ioc 0 Q, Q / d * f d := by
  classical
  have hdiv (n : ℕ) (hn : n ∈ Ioc 0 Q) : n.divisors = (Ioc 0 Q).filter (· ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    obtain ⟨hn₀, hnQ⟩ := mem_Ioc.mp hn
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn₀, (Nat.le_of_dvd hn₀ hd).trans hnQ⟩, hd⟩
    · exact fun h ↦ ⟨h.2, hn₀.ne'⟩
  calc
    _ = ∑ n ∈ Ioc 0 Q, ∑ d ∈ Ioc 0 Q, if d ∣ n then f d else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [hdiv n hn, sum_filter]
    _ = ∑ d ∈ Ioc 0 Q, ∑ n ∈ Ioc 0 Q, if d ∣ n then f d else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, Nat.cast_id]

private theorem sum_multiples_split (Q K : ℕ) (hK : 0 < K) (f : ℕ → ℕ) (hf : ∀ d ∈ Ioc 0 Q, f d ≤ d) :
    (∑ d ∈ Ioc 0 Q, Q / d * f d) ≤ (Q / K) * Q + K * ∑ d ∈ Ioc 0 Q, f d := by
  have hp (d : ℕ) (hd : d ∈ Ioc 0 Q) :
      Q / d * f d ≤ (if d ≤ Q / K then Q else 0) + K * f d := by
    split_ifs with h
    · exact (Nat.mul_le_mul_left _ (hf d hd)).trans ((Nat.div_mul_le_self Q d).trans (Nat.le_add_right ..))
    · have h' : Q / d ≤ K := by
        have hq : Q < d * K := (Nat.div_lt_iff_lt_mul hK).mp (by omega)
        exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul (mem_Ioc.mp hd).1).mpr (by simpa [Nat.mul_comm] using hq))
      simpa using Nat.mul_le_mul_right (f d) h'
  have hset : (Ioc 0 Q).filter (fun d ↦ d ≤ Q / K) = Ioc 0 (Q / K) := by
    ext d
    simp only [mem_filter, mem_Ioc]
    have := Nat.div_le_self Q K
    omega
  apply (sum_le_sum hp).trans_eq
  rw [sum_add_distrib, ← mul_sum, ← sum_filter, hset, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, Nat.cast_id]

private theorem two_mul_sum_Ioc (Q : ℕ) : 2 * (∑ d ∈ Ioc 0 Q, d) = Q * (Q + 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), Nat.mul_add, ih]
    ring

private theorem quadratic_le_totient_sum (Q : ℕ) :
    Q ^ 2 ≤ 16 * ∑ d ∈ Ioc 0 Q, d.totient := by
  have h := sum_multiples_split Q 4 (by decide) Nat.totient (fun d _ ↦ Nat.totient_le d)
  rw [← sum_divisors_through] at h
  simp_rw [Nat.sum_totient] at h
  have hQ := Nat.div_mul_le_self Q 4
  have ht := two_mul_sum_Ioc Q
  nlinarith only [Nat.mul_le_mul_right Q hQ, h, ht, Nat.zero_le Q]

/-- At least Q²/1024 primitive Dirichlet characters have conductor at most Q. -/
theorem quadratic_le_primitiveCount_sum (Q : ℕ) :
    Q ^ 2 ≤ 1024 * ∑ d ∈ Ioc 0 Q, primitiveCount d := by
  have h := sum_multiples_split Q 32 (by decide) primitiveCount (fun d hd ↦ by
    have : NeZero d := ⟨(mem_Ioc.mp hd).1.ne'⟩
    exact (primitiveCount_le_totient d).trans (Nat.totient_le d))
  rw [← sum_divisors_through] at h
  have hl : (∑ n ∈ Ioc 0 Q, n.totient) = ∑ n ∈ Ioc 0 Q, ∑ d ∈ n.divisors, primitiveCount d := by
    apply sum_congr rfl
    intro n hn
    have : NeZero n := ⟨(mem_Ioc.mp hn).1.ne'⟩
    exact totient_eq_sum_primitiveCount n
  have hQ := Nat.div_mul_le_self Q 32
  nlinarith only [Nat.mul_le_mul_right Q hQ, hl.le.trans h, quadratic_le_totient_sum Q]

/-- The quadratic lower bound in the finite-sum convention used for the primitive large sieve. -/
theorem quadratic_le_sum_card_primitive (Q : ℕ) :
    Q ^ 2 ≤ 1024 * ∑ m ∈ range Q,
      ((univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive)).card := by
  apply (quadratic_le_primitiveCount_sum Q).trans_eq
  congr 1
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), sum_range_succ, ih]
    congr 1
    rw [primitiveCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

end DirichletCharacter
