module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.WeakPNT
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev

/-! # Quadratic twists of the signed degree-one prime Riesz mean

Complete-period orthogonality controls the mean square of quadratic twists of the
rational prime coefficients in Theorem 12.5.1.1 (pp. 519–520). The bounds use
the Euler coefficient majorant of Appendix B.6. In any class with a negative sign,
square norms are absent. The Costa–Pereira inequalities for Chebyshev functions then
control the cost of replacing the prime sum by the full Hecke Riesz sum.
-/

open Finset NumberField

@[expose] public noncomputable section

namespace RiemannMasullo

/-- On one complete period the two distinct odd-prime quadratic signs are orthogonal. -/
private theorem quadraticPrime_complete_cross_sum (p r : ℕ) [Fact p.Prime] [Fact r.Prime] (hp : p ≠ 2)
    (hpr : p.Coprime r) :
    ∑ a : ZMod (p*r), quadraticChar (ZMod p) ((ZMod.chineseRemainder hpr a).1) *
      quadraticChar (ZMod r) ((ZMod.chineseRemainder hpr a).2) = 0 := by
  classical
  let f (z : ZMod p × ZMod r) := quadraticChar (ZMod p) z.1 * quadraticChar (ZMod r) z.2
  change (∑ a : ZMod (p*r), f ((ZMod.chineseRemainder hpr).toEquiv a)) = 0
  rw [(ZMod.chineseRemainder hpr).toEquiv.sum_comp f]
  simp only [Fintype.sum_prod_type, f, ← Finset.mul_sum, ← Finset.sum_mul]
  have hz : (∑ z : ZMod p, quadraticChar (ZMod p) z) = 0 := by
    apply quadraticChar_sum_zero
    rw [ZMod.ringChar_zmod_n]
    exact hp
  rw [hz, zero_mul]

/-- Removing full periods leaves an error bounded by the period length. -/
private theorem quadraticPrime_incomplete_period (L : ℕ) (hL : 0 < L) (g : ℕ → ℤ)
    (hp : ∀ k, g (L + k) = g k) (hz : ∑ k ∈ range L, g k = 0) (hb : ∀ k, |g k| ≤ 1)
    (N : ℕ) : |∑ k ∈ range N, g k| ≤ (L : ℤ) := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hn : N < L
    · calc |∑ k ∈ range N, g k| ≤ ∑ k ∈ range N, |g k| := abs_sum_le_sum_abs g _
           _ ≤ ∑ _ ∈ range N, (1 : ℤ) := sum_le_sum fun i _ ↦ hb i
           _ ≤ L := by simpa using (show (N : ℤ) ≤ L by exact_mod_cast hn.le)
    · have hsplit : N = L + (N - L) := by omega
      have hsmall : N - L < N := by omega
      calc |∑ k ∈ range N, g k| = |∑ k ∈ range (N - L), g k| := by
             conv_lhs => rw [hsplit, sum_range_add, hz, zero_add]
             simp only [hp]
           _ ≤ L := ih _ hsmall

/-- The complete diagonal and the error per pair bound the actual weighted second moment. -/
private theorem quadraticPrime_weighted_second_moment {ι κ : Type*} (m : Finset κ) (s : Finset ι)
    (v : κ → ι → ℝ) (b : ι → ℝ) (B K : ℝ) (hK : 0 ≤ K)
    (diag : ∀ i ∈ s, ∑ a ∈ m, v a i * v a i ≤ B)
    (cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → |∑ a ∈ m, v a i * v a j| ≤ K) :
    ∑ a ∈ m, (∑ i ∈ s, b i * v a i)^2 ≤
      (B + K * s.card) * ∑ i ∈ s, b i ^ 2 := by
  classical
  have one (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      b i * b j * (∑ a ∈ m, v a i * v a j) ≤
      (if i = j then B * b i ^ 2 else 0) + K * (|b i| * |b j|) := by
    by_cases he : i = j
    · subst j
      rw [ite_eq_left rfl]
      calc _ ≤ (b i * b i) * B := mul_le_mul_of_nonneg_left (diag i hi) (mul_self_nonneg _)
           _ ≤ _ := by nlinarith [mul_nonneg hK (mul_self_nonneg |b i|)]
    · rw [ite_eq_right he, zero_add]
      calc _ ≤ |b i * b j * (∑ a ∈ m, v a i * v a j)| := le_abs_self _
           _ ≤ (|b i| * |b j|) * K := by
             rw [abs_mul, abs_mul]
             exact mul_le_mul_of_nonneg_left (cross i hi j hj he) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
           _ = _ := mul_comm ..
  have hgram : ∑ a ∈ m, (∑ i ∈ s, b i * v a i)^2 =
      ∑ i ∈ s, ∑ j ∈ s, b i * b j * (∑ a ∈ m, v a i * v a j) := by
    simp only [pow_two, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro a ha
    ring
  have hcs : (∑ i ∈ s, |b i|)^2 ≤ s.card * ∑ i ∈ s, b i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ |b i|))
  rw [hgram]
  calc _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((if i = j then B * b i ^ 2 else 0) + K * (|b i| * |b j|)) :=
           sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ one i hi j hj
       _ = B * (∑ i ∈ s, b i ^ 2) + K * (∑ i ∈ s, |b i|)^2 := by
           simp only [sum_add_distrib]
           congr 1
           · rw [mul_sum]
             apply sum_congr rfl
             intro i hi
             simp [hi]
           · simp only [pow_two, sum_mul, mul_sum]
             exact sum_comm
       _ ≤ _ := by rw [add_mul, mul_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_left hcs hK) _

private theorem quadraticPrime_sum_range_zmod {L : ℕ} [NeZero L] (g : ZMod L → ℤ) :
    (∑ k ∈ range L, g k) = ∑ a : ZMod L, g a := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro a _
    apply congrArg g
    exact Fin.cast_val_eq_self a

private theorem quadraticPrime_abs_symbol (k p : ℕ) : |jacobiSym k p| ≤ 1 := by
  rcases jacobiSym.trichotomy k p with h | h | h <;> simp [h]

private theorem quadraticPrime_cross_interval {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp2 : p ≠ 2) (hne : p ≠ r) (A M : ℕ) :
    |∑ k ∈ range M, jacobiSym (A+k : ℕ) p * jacobiSym (A+k : ℕ) r| ≤ (p*r : ℕ) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact r.Prime := ⟨hr⟩
  have hpr := (Nat.coprime_primes hp hr).2 hne
  let g (a : ZMod (p*r)) := quadraticChar (ZMod p) ((ZMod.chineseRemainder hpr a).1) *
    quadraticChar (ZMod r) ((ZMod.chineseRemainder hpr a).2)
  have hsum : ∑ a, g a = 0 := quadraticPrime_complete_cross_sum p r hp2 hpr
  have he (k : ℕ) : jacobiSym k p * jacobiSym k r = g k := by
    simp [g, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, map_natCast]
  apply quadraticPrime_incomplete_period (p*r) (Nat.mul_pos hp.pos hr.pos)
  · intro k
    rw [he, he]
    congr 1
    simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
  · simp_rw [he, Nat.cast_add]
    rw [quadraticPrime_sum_range_zmod (L := p*r) (fun z ↦ g ((A : ZMod (p*r)) + z))]
    exact (Equiv.sum_comp (Equiv.addLeft (A : ZMod (p*r))) g).trans hsum
  · intro k
    rw [abs_mul]
    exact (mul_le_mul (quadraticPrime_abs_symbol _ _) (quadraticPrime_abs_symbol _ _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- An elementary quadratic mean-square bound on a consecutive interval of twists. Each
off-diagonal prime pair contributes at most one incomplete period. -/
theorem quadraticPrimeTwist_secondMoment (P : Finset ℕ) (T A M : ℕ)
    (hP : P ⊆ Nat.primesLE T) (b : ℕ → ℝ) :
    ∑ k ∈ range M, (∑ p ∈ P, b p * (jacobiSym (A+k : ℕ) p : ℝ))^2 ≤
      (M + (T : ℝ)^2 * P.card) * ∑ p ∈ P, b p ^ 2 := by
  apply quadraticPrime_weighted_second_moment (range M) P
    (fun k p ↦ (jacobiSym (A+k : ℕ) p : ℝ)) b M ((T : ℝ)^2) (sq_nonneg _)
  · intro i _
    calc (∑ k ∈ range M, _) ≤ ∑ _ ∈ range M, (1 : ℝ) := by
           apply sum_le_sum
           intro k _
           rcases jacobiSym.trichotomy (A+k : ℕ) i with h | h | h <;> rw [h] <;> norm_num
         _ = _ := by simp
  · intro i hi j hj hij
    obtain ⟨hit, hip⟩ := Nat.mem_primesLE.mp (hP hi)
    obtain ⟨hjt, hjp⟩ := Nat.mem_primesLE.mp (hP hj)
    have hcross :
        |∑ k ∈ range M, jacobiSym (A+k : ℕ) i * jacobiSym (A+k : ℕ) j| ≤ (i*j : ℕ) := by
      by_cases h : i = 2
      · simpa only [mul_comm] using quadraticPrime_cross_interval hjp hip (by omega) hij.symm A M
      · exact quadraticPrime_cross_interval hip hjp h hij A M
    have hbound : i*j ≤ T^2 := by simpa [pow_two] using Nat.mul_le_mul hit hjt
    exact_mod_cast hcross.trans (by exact_mod_cast hbound : ((i*j : ℕ) : ℤ) ≤ ((T^2 : ℕ) : ℤ))

private theorem quadraticPrime_prime_card_le (T : ℕ) : (Nat.primesLE T).card ≤ T := by
  calc (Nat.primesLE T).card ≤ (Finset.Ioc 0 T).card := card_le_card fun p hp ↦
         Finset.mem_Ioc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, (Nat.mem_primesLE.mp hp).1⟩
       _ = T := by simp

private theorem quadraticPrime_hecke_energy {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) {x : ℝ} (hx : x ≤ T)
    (u : ℕ → ℝ) (hu : ∀ p ∈ Nat.primesLE T, |u p| ≤ 1) :
    ∑ p ∈ Nat.primesLE T, ((heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re *
      max (x - p) 0 * u p)^2 ≤
      (Module.finrank ℚ F : ℝ)^2 * T^3 * Real.log (2 + T) * Real.log 4 := by
  let D : ℝ := Module.finrank ℚ F
  have hb (p : ℕ) (hp : p ∈ Nat.primesLE T) :
      |(heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re *
        max (x - p) 0 * u p| ≤ D * T * Real.log p := by
    have hcoef := heckeLogDerivCoefficient_le_vonMangoldt χ p
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesLE.mp hp).2] at hcoef
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    have hcoef' := (Complex.abs_re_le_norm _).trans hcoef
    rw [abs_mul, abs_mul, abs_of_nonneg (le_max_right (x - p) (0 : ℝ))]
    calc _ ≤ ((D * Real.log p) * T) * 1 := by
           have hR : max (x-p) 0 ≤ T :=
             max_le ((sub_le_self _ (Nat.cast_nonneg p)).trans hx) (Nat.cast_nonneg _)
           have hD : 0 ≤ D * Real.log p := mul_nonneg (Nat.cast_nonneg _) hlog
           exact mul_le_mul (mul_le_mul hcoef' hR (le_max_right _ _) hD) (hu p hp)
             (abs_nonneg _) (mul_nonneg hD (Nat.cast_nonneg _))
         _ = _ := by ring
  have hsum : ∑ p ∈ Nat.primesLE T, ((heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re *
      max (x - p) 0 * u p)^2 ≤
        ∑ p ∈ Nat.primesLE T, ((D*T)^2 * Real.log (2+T)) * Real.log p := by
    apply sum_le_sum
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    have hlog := Real.log_nonneg (by exact_mod_cast hp'.2.one_le : (1 : ℝ) ≤ p)
    have hlog' : Real.log p ≤ Real.log (2 + T) := Real.log_le_log
      (by exact_mod_cast hp'.2.pos) (by linarith [(by exact_mod_cast hp'.1 : (p : ℝ) ≤ T)])
    calc _ = |(heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re *
             max (x - p) 0 * u p|^2 := (sq_abs _).symm
         _ ≤ (D * T * Real.log p)^2 := by gcongr; exact hb p hp
         _ = (D*T)^2 * Real.log p * Real.log p := by ring
         _ ≤ _ := by gcongr
  rw [← mul_sum, ← Chebyshev.theta_eq_sum_primesLE_log] at hsum
  calc _ ≤ _ := hsum
       _ ≤ ((D*T)^2 * Real.log (2+T)) * (Real.log 4 * T) := by
         have hlog : 0 ≤ Real.log (2+(T : ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) T])
         exact mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg T))
           (mul_nonneg (sq_nonneg _) hlog)
       _ = _ := by dsimp [D]; ring

/-- For the actual signed Hecke coefficients the quadratic twists of every first Riesz
cutoff up to T have total square bounded by a constant times (M+T³)T³ log(2+T).
An extra bounded multiplier permits a second quadratic twist without any loss. -/
theorem quadraticPrimeTwist_hecke_secondMoment {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T A M : ℕ) {x : ℝ} (hx : x ≤ T)
    (u : ℕ → ℝ) (hu : ∀ p ∈ Nat.primesLE T, |u p| ≤ 1) :
    ∑ k ∈ range M, (∑ p ∈ Nat.primesLE T,
      (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re * max (x-p) 0 *
        u p * (jacobiSym (A+k : ℕ) p : ℝ))^2 ≤
      (M + (T : ℝ)^3) * ((Module.finrank ℚ F : ℝ)^2 * T^3 * Real.log (2+T) * Real.log 4) := by
  apply (quadraticPrimeTwist_secondMoment (Nat.primesLE T) T A M (fun _ h ↦ h) _).trans
  apply mul_le_mul _ (quadraticPrime_hecke_energy χ T hx u hu) (sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
  have hc : ((Nat.primesLE T).card : ℝ) ≤ T := by exact_mod_cast quadraticPrime_prime_card_le T
  calc (M : ℝ) + T^2 * (Nat.primesLE T).card ≤ M + (T : ℝ)^2 * T := by gcongr
       _ = _ := by ring

/-- Real first Riesz mean of the degree-one prime coefficients with a bounded choice of
weights on the rational primes. The same cutoff T can be used for all x ≤ T. -/
def degreeOnePrimeRieszSumWith {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE T, (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re *
    max (x-p) 0 * w p

private theorem quadraticPrime_sum_abs_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {K : ℝ}
    (h : ∑ i ∈ s, f i ^ 2 ≤ K) : ∑ i ∈ s, |f i| ≤ Real.sqrt (s.card * K) := by
  apply Real.le_sqrt_of_sq_le
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ |f i|)
  simp only [sq_abs] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

private theorem quadraticPrime_sample_l1 {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T M : ℕ) (s I : Finset ℕ)
    (hs : s ⊆ range M) (x : ℕ → ℝ) (hx : ∀ j ∈ I, x j ≤ T)
    (u : ℕ → ℝ) (hu : ∀ p ∈ Nat.primesLE T, |u p| ≤ 1) :
    ∑ q ∈ s, ∑ j ∈ I, |degreeOnePrimeRieszSumWith χ T (x j)
      (fun p ↦ u p * (jacobiSym q p : ℝ))| ≤ I.card * Real.sqrt (s.card *
      ((M + (T : ℝ)^3) * ((Module.finrank ℚ F : ℝ)^2 * T^3 * Real.log (2+T) * Real.log 4))) := by
  rw [sum_comm]
  calc _ ≤ ∑ _j ∈ I, Real.sqrt (s.card * ((M + (T : ℝ)^3) *
           ((Module.finrank ℚ F : ℝ)^2 * T^3 * Real.log (2+T) * Real.log 4))) := by
         apply sum_le_sum
         intro j hj
         apply quadraticPrime_sum_abs_le
         apply (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ sq_nonneg _)).trans
         simpa only [degreeOnePrimeRieszSumWith, ← mul_assoc, zero_add] using
           quadraticPrimeTwist_hecke_secondMoment χ T 0 M (hx j hj) u hu
       _ = _ := by simp [nsmul_eq_mul]

private theorem quadraticPrime_cell_error {ι : Type*} (s : Finset ι) (b u v : ι → ℝ)
    {e f : ℝ} (he : |e| = 1) (hf : |f| = 1)
    (hu : ∀ i ∈ s, |u i| = 1) (hv : ∀ i ∈ s, |v i| = 1) :
    |4 * (∑ i ∈ s with u i = e ∧ v i = f, b i) - ∑ i ∈ s, b i| ≤
      |∑ i ∈ s, b i * u i| + |∑ i ∈ s, b i * v i| + |∑ i ∈ s, b i * (u i * v i)| := by
  classical
  have signs {z : ℝ} (hz : |z| = 1) : z = 1 ∨ z = -1 := by
    rcases le_or_gt 0 z with h | h
    · exact Or.inl ((abs_of_nonneg h).symm.trans hz)
    · right; rw [abs_of_neg h] at hz; linarith
  have hx : 4 * (∑ i ∈ s with u i = e ∧ v i = f, b i) - ∑ i ∈ s, b i =
      e * (∑ i ∈ s, b i * u i) + f * (∑ i ∈ s, b i * v i) +
      (e*f) * (∑ i ∈ s, b i * (u i * v i)) := by
    rw [sum_filter, mul_sum, ← sum_sub_distrib, mul_sum, mul_sum, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rcases signs he with h₁ | h₁ <;> rcases signs hf with h₂ | h₂ <;>
      rcases signs (hu i hi) with h₃ | h₃ <;> rcases signs (hv i hi) with h₄ | h₄ <;>
      norm_num [h₁, h₂, h₃, h₄] <;> ring
  rw [hx]
  grw [abs_add_le, abs_add_le]
  simp [abs_mul, he, hf]

/-- Four times the contribution of the chosen quadratic sign class. For an odd degree-one
prime norm p, its signs record the two quadratic residue tests in the residue field of p. -/
def quadraticPrimeCellRieszSum {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ)
    (q d : ℕ) (e f : ℝ) : ℝ :=
  4 * ∑ p ∈ Nat.primesLE T with (jacobiSym q p : ℝ) = e ∧ (jacobiSym d p : ℝ) = f,
    (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re * max (x-p) 0

private theorem quadraticPrime_sign_of_coprime {q p : ℕ} (h : Nat.Coprime q p) :
    |(jacobiSym q p : ℝ)| = 1 := by
  have hg : (q : ℤ).gcd p = 1 := by simpa [Int.gcd_eq_natAbs] using h
  rcases jacobiSym.eq_one_or_neg_one hg with hh | hh <;> rw [hh] <;> norm_num

/-- Mean error for a collection of real cutoffs and two sets of auxiliary twists.
The signs of the selected class may depend on each pair and each cutoff. -/
theorem quadraticPrimeTwist_hecke_cell_mean {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T M : ℕ) (U V I : Finset ℕ)
    (hU : U ⊆ range M) (hV : V ⊆ range M)
    (hcU : ∀ q ∈ U, ∀ p ∈ Nat.primesLE T, Nat.Coprime q p)
    (hcV : ∀ d ∈ V, ∀ p ∈ Nat.primesLE T, Nat.Coprime d p)
    (x : ℕ → ℝ) (hx : ∀ j ∈ I, x j ≤ T)
    (e f : ℕ → ℕ → ℕ → ℝ) (he : ∀ q d j, |e q d j| = 1) (hf : ∀ q d j, |f q d j| = 1) :
    let K := (M + (T : ℝ)^3) * ((Module.finrank ℚ F : ℝ)^2 * T^3 * Real.log (2+T) * Real.log 4)
    ∑ q ∈ U, ∑ d ∈ V, ∑ j ∈ I, |quadraticPrimeCellRieszSum χ T (x j) q d (e q d j) (f q d j) -
      degreeOnePrimeRieszSumWith χ T (x j) 1| ≤
      (V.card * (I.card * Real.sqrt (U.card * K)) +
        2 * U.card * (I.card * Real.sqrt (V.card * K))) := by
  intro K
  let R (q j : ℕ) := |degreeOnePrimeRieszSumWith χ T (x j) (fun p ↦ (jacobiSym q p : ℝ))|
  let B (q d j : ℕ) := |degreeOnePrimeRieszSumWith χ T (x j)
    (fun p ↦ (jacobiSym q p : ℝ) * (jacobiSym d p : ℝ))|
  have h1 (s : Finset ℕ) (hs : s ⊆ range M) :
      ∑ q ∈ s, ∑ j ∈ I, R q j ≤ I.card * Real.sqrt (s.card * K) := by
    simpa [R, K] using quadraticPrime_sample_l1 χ T M s I hs x hx (fun _ ↦ 1) (by simp)
  have h2 (q : ℕ) : ∑ d ∈ V, ∑ j ∈ I, B q d j ≤ I.card * Real.sqrt (V.card * K) := by
    exact quadraticPrime_sample_l1 χ T M V I hV x hx (fun p ↦ (jacobiSym q p : ℝ))
      (fun p _ ↦ by exact_mod_cast quadraticPrime_abs_symbol q p)
  have point (q : ℕ) (hq : q ∈ U) (d : ℕ) (hd : d ∈ V) (j : ℕ) :
      |quadraticPrimeCellRieszSum χ T (x j) q d (e q d j) (f q d j) -
        degreeOnePrimeRieszSumWith χ T (x j) 1| ≤ R q j + R d j + B q d j := by
    simpa only [quadraticPrimeCellRieszSum, degreeOnePrimeRieszSumWith, R, B, Pi.one_apply,
      mul_one] using quadraticPrime_cell_error (Nat.primesLE T)
      (fun p ↦ (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re * max (x j-p) 0)
      (fun p ↦ (jacobiSym q p : ℝ)) (fun p ↦ (jacobiSym d p : ℝ))
      (he q d j) (hf q d j)
      (fun p hp ↦ quadraticPrime_sign_of_coprime (hcU q hq p hp))
      (fun p hp ↦ quadraticPrime_sign_of_coprime (hcV d hd p hp))
  calc _ ≤ ∑ q ∈ U, ∑ d ∈ V, ∑ j ∈ I, (R q j + R d j + B q d j) :=
           sum_le_sum fun q hq ↦ sum_le_sum fun d hd ↦ sum_le_sum fun j _ ↦ point q hq d hd j
       _ = V.card * (∑ q ∈ U, ∑ j ∈ I, R q j) +
           U.card * (∑ d ∈ V, ∑ j ∈ I, R d j) + ∑ q ∈ U, ∑ d ∈ V, ∑ j ∈ I, B q d j := by
           simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
       _ ≤ V.card * (I.card * Real.sqrt (U.card * K)) + U.card * (I.card * Real.sqrt (V.card * K)) +
            ∑ _q ∈ U, I.card * Real.sqrt (V.card * K) := by
           exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h1 U hU) (Nat.cast_nonneg _))
             (mul_le_mul_of_nonneg_left (h1 V hV) (Nat.cast_nonneg _))) (sum_le_sum fun q _ ↦ h2 q)
       _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

open Filter Topology in
private theorem quadraticPrime_dyadic_card :
    ∀ᶠ Q : ℕ in atTop, (Q : ℝ) ≤
      2 * ((Nat.primesLE (2*Q) \ Nat.primesLE Q).card : ℝ) * Real.log (2*Q) := by
  have ht := Chebyshev.tendsto_theta_div_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo : ∀ᶠ n : ℕ in atTop, (7/8 : ℝ) < Chebyshev.theta n / n :=
    ht.eventually (lt_mem_nhds (by norm_num))
  have hhi : ∀ᶠ n : ℕ in atTop, Chebyshev.theta n / n < (9/8 : ℝ) :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlo
  filter_upwards [eventually_ge_atTop (max N 1), hhi] with Q hQ hhi
  have hp : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have h := hN (2*Q) (by omega)
  push_cast at h
  have hlow := (lt_div_iff₀ (by positivity)).mp h
  have hhigh := (div_lt_iff₀ hp).mp hhi
  let U := Nat.primesLE (2*Q) \ Nat.primesLE Q
  have heq : ∑ p ∈ U, Real.log p + Chebyshev.theta Q = Chebyshev.theta (2*(Q:ℝ)) := by
    rw [← Nat.cast_ofNat (n := 2) (R := ℝ), ← Nat.cast_mul]
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact sum_sdiff (Nat.primesLE_mono (by omega))
  have hsum : ∑ p ∈ U, Real.log p ≤ U.card * Real.log (2*Q) := by
    calc _ ≤ ∑ _ ∈ U, Real.log (2*Q) := sum_le_sum fun p h ↦ by
           have hm := Nat.mem_primesLE.mp (mem_sdiff.mp h).1
           apply Real.log_le_log (by exact_mod_cast hm.2.pos)
           exact_mod_cast hm.1
         _ = _ := by simp
  change (Q : ℝ) ≤ 2 * (U.card : ℝ) * Real.log (2*Q)
  linarith

private theorem quadraticPrime_fourthPower_error {J n D : ℝ} (hJ : 2 ≤ J) (hn : 0 ≤ n)
    (hD : 0 ≤ D) (hcount : J^12 ≤ 2*n*Real.log (2*J^12)) :
    let T := J^4
    let K := (2*J^12+1+T^3) * (D^2*T^3*Real.log (2+T)*Real.log 4)
    3*n*J*Real.sqrt (n*K) ≤ n^2*(300*D*J^7*Real.log (2+J)) := by
  intro T K
  let L := Real.log (2+J)
  have jpos : 0 < J := by linarith
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfour' : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hlq : Real.log (2*J^12) ≤ 13*L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h1 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have h2 : Real.log J ≤ L := Real.log_le_log jpos (by linarith)
    norm_num
    linarith
  have hcount' : J^12 ≤ 26*n*L := by
    calc _ ≤ _ := hcount
         _ ≤ 2*n*(13*L) := by gcongr
         _ = _ := by ring
  have hlt : Real.log (2+T) ≤ 4*L := by
    calc _ ≤ Real.log ((2+J)^4) := by
           apply Real.log_le_log (by dsimp [T]; positivity)
           dsimp [T]
           nlinarith [sq_nonneg J, (show 0 ≤ J^3 by positivity)]
         _ = _ := by simp [Real.log_pow,L]
  have htq : T^3 = J^12 := by dsimp [T]; ring
  have hjpow : 1 ≤ J^12 := one_le_pow₀ (by linarith)
  have hm : 2*J^12+1+T^3 ≤ 4*J^12 := by rw [htq]; linarith
  have htpos : 0 ≤ T := by dsimp [T]; positivity
  have hlogpos : 0 ≤ Real.log (2+T) := Real.log_nonneg (by linarith)
  have hK : K ≤ n*(100*D*J^6*L)^2 := by
    calc K ≤ (4*J^12)*(D^2*T^3*(4*L)*3) := by
           dsimp only [K]
           apply mul_le_mul hm _ (by positivity) (by positivity)
           exact mul_le_mul (by gcongr) hfour' hfour (by dsimp [T]; positivity)
         _ = (48*D^2*J^12*L)*J^12 := by rw [htq]; ring
         _ ≤ (48*D^2*J^12*L)*(26*n*L) := by gcongr
         _ ≤ n*(100*D*J^6*L)^2 := by
           have factor : 0 ≤ D^2*J^12*L^2*n := by positivity
           nlinarith only [factor]
  have hs : Real.sqrt (n*K) ≤ n*(100*D*J^6*L) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc n*K ≤ n*(n*(100*D*J^6*L)^2) := by gcongr
         _ = _ := by ring
  calc _ ≤ 3*n*J*(n*(100*D*J^6*L)) := by gcongr
       _ = _ := by dsimp [L]; ring

open Filter in
/-- At the fourth powers through `J^4`, the mean total absolute discrepancy over ordered prime
pairs in `(J^12, 2 J^12]` is at most `300 [F:ℚ] J^7 log(2+J)`.
Each of the four quadratic sign classes may be chosen separately at each sample. -/
theorem quadraticPrimeTwist_fourthPower_cell_mean {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∀ᶠ J : ℕ in atTop, let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
      ∀ (e f : ℕ → ℕ → ℕ → ℝ), (∀ q d j, |e q d j| = 1) → (∀ q d j, |f q d j| = 1) →
      ∑ q ∈ U, ∑ d ∈ U, ∑ j ∈ Ioc 0 J,
        |quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) q d (e q d j) (f q d j) -
          degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1| ≤
        (U.card:ℝ)^2 * (300 * (Module.finrank ℚ F : ℝ) * (J:ℝ)^7 * Real.log (2+J)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp quadraticPrime_dyadic_card
  filter_upwards [eventually_ge_atTop (max 2 N)] with J hJ
  intro U e f he hf
  let Q := J^12
  have hJ1 : 1 ≤ J := by omega
  have hJQ : J ≤ Q := le_self_pow₀ hJ1 (by decide)
  have hTQ : J^4 ≤ Q := pow_le_pow_right₀ hJ1 (by decide)
  have sub : U ⊆ range (2*Q+1) := fun q hq ↦ by
    have h := Nat.le_of_mem_primesLE (mem_sdiff.mp hq).1
    exact mem_range.mpr (Nat.lt_succ_of_le h)
  have cop : ∀ q ∈ U, ∀ p ∈ Nat.primesLE (J^4), Nat.Coprime q p := by
    intro q hq p hp
    obtain ⟨hq',hout⟩ := mem_sdiff.mp hq
    have hprime := Nat.prime_of_mem_primesLE hq'
    have hlarge : ¬ q ≤ Q := fun h ↦ hout (Nat.mem_primesLE.mpr ⟨h,hprime⟩)
    exact (Nat.coprime_primes hprime (Nat.prime_of_mem_primesLE hp)).mpr
      (fun h ↦ hlarge (h ▸ (Nat.le_of_mem_primesLE hp).trans hTQ))
  have hx (j : ℕ) (hj : j ∈ Ioc 0 J) : (j:ℝ)^4 ≤ ((J^4 : ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4
  have hm := quadraticPrimeTwist_hecke_cell_mean χ (J^4) (2*Q+1) U U (Ioc 0 J)
    sub sub cop cop (fun j ↦ (j:ℝ)^4) hx e f he hf
  let D : ℝ := Module.finrank ℚ F
  have hcount := hN Q (by omega)
  change (Q:ℝ) ≤ 2*(U.card:ℝ)*Real.log (2*Q) at hcount
  dsimp [Q] at hcount
  push_cast at hcount
  have hs := quadraticPrime_fourthPower_error (J := (J:ℝ)) (n := (U.card:ℝ)) (D := D)
    (by exact_mod_cast (show 2 ≤ J by omega)) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcount
  dsimp only at hm hs
  simp only [Nat.card_Ioc, Nat.sub_zero, Q, Nat.cast_add, Nat.cast_one,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hm
  exact hm.trans (by convert hs using 1; ring)

open Filter in
/-- The same mean bound compares the total deficits below any common sequence of center
values. The center can in particular be the principal character's quadratic main term. -/
theorem quadraticPrimeTwist_fourthPower_deficit_mean {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∀ᶠ J : ℕ in atTop, let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
      ∀ (c : ℕ → ℝ) (e f : ℕ → ℕ → ℕ → ℝ),
      (∀ q d j, |e q d j| = 1) → (∀ q d j, |f q d j| = 1) →
      ∑ q ∈ U, ∑ d ∈ U, |(∑ j ∈ Ioc 0 J, max (c j -
        quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) q d (e q d j) (f q d j)) 0) -
        ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0| ≤
        (U.card:ℝ)^2 * (300 * (Module.finrank ℚ F : ℝ) * (J:ℝ)^7 * Real.log (2+J)) := by
  filter_upwards [quadraticPrimeTwist_fourthPower_cell_mean χ] with J hJ
  intro U c e f he hf
  apply le_trans _ (hJ e f he hf)
  refine sum_le_sum fun q _ ↦ sum_le_sum fun d _ ↦ ?_
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _ ↦ ?_)
  have lip (a b : ℝ) : |max (c j-a) 0 - max (c j-b) 0| ≤ |a-b| := by
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm b a] using
      abs_max_sub_max_le_abs (c j-a) (c j-b) 0
  exact lip _ _


/-- Four times the Riesz sum of the actual Hecke logarithmic-derivative coefficients
over all integer norms with the indicated two quadratic signs. -/
def quadraticPrimePowerCellRieszSum {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ)
    (q d : ℕ) (e f : ℝ) : ℝ :=
  4 * ∑ n ∈ Ioc 0 T with (jacobiSym q n : ℝ) = e ∧ (jacobiSym d n : ℝ) = f,
    (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n).re * max (x-n) 0

open ArithmeticFunction in
private theorem quadraticPrime_square_mass (T : ℕ) :
    let S := (Ioc 0 (Nat.sqrt T)).image (fun n : ℕ ↦ n^2)
    ∑ n ∈ S, vonMangoldt n = Chebyshev.psi ((T:ℝ)^(2:ℝ)⁻¹) := by
  intro S
  rw [← one_div, ← Real.sqrt_eq_rpow, Chebyshev.psi, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  dsimp only [S]
  rw [sum_image (fun a _ b _ h ↦ by simpa using h)]
  exact sum_congr rfl fun a _ ↦ vonMangoldt_apply_pow (by decide)

open ArithmeticFunction in
private theorem quadraticPrime_nonsquare_mass (T : ℕ) (hT : 1 ≤ T) :
    let S := (Ioc 0 (Nat.sqrt T)).image (fun n : ℕ ↦ n^2)
    ∑ n ∈ Ioc 0 T \ (Nat.primesLE T ∪ S), vonMangoldt n ≤
      2*(Real.log 4+4)*(T:ℝ)^(3:ℝ)⁻¹ := by
  intro S
  let P := Nat.primesLE T
  have hsub : P ∪ S ⊆ Ioc 0 T := by
    intro n hn
    rcases mem_union.mp hn with h | h
    · exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE h).pos, Nat.le_of_mem_primesLE h⟩
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp h
      exact mem_Ioc.mpr ⟨pow_pos (mem_Ioc.mp ha).1 _, by
        simpa only [pow_two] using (Nat.le_sqrt.mp (mem_Ioc.mp ha).2)⟩
  have hd : Disjoint P S := by
    refine Finset.disjoint_left.mpr fun n hn hs ↦ ?_
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hs
    exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (Nat.prime_of_mem_primesLE hn)
  have hsum := sum_sdiff (f := fun n ↦ vonMangoldt n) hsub
  rw [sum_union hd] at hsum
  have hp : ∑ n ∈ P, vonMangoldt n = Chebyshev.theta T := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    exact sum_congr rfl fun n hn ↦ vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hn)
  have hs : ∑ n ∈ S, vonMangoldt n = Chebyshev.psi ((T:ℝ)^(2:ℝ)⁻¹) :=
    quadraticPrime_square_mass T
  have hf : ∑ n ∈ Ioc 0 T, vonMangoldt n = Chebyshev.psi T := by simp [Chebyshev.psi]
  rw [hp, hs, hf] at hsum
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi T
  have h3 := Chebyshev.psi_le_const_mul_self (x := (T:ℝ)^(3:ℝ)⁻¹) (by positivity)
  have h5 := Chebyshev.psi_le_const_mul_self (x := (T:ℝ)^(5:ℝ)⁻¹) (by positivity)
  have h53 : (Real.log 4+4)*(T:ℝ)^(5:ℝ)⁻¹ ≤ (Real.log 4+4)*T^(3:ℝ)⁻¹ := by
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT) (by norm_num))
    positivity
  change ∑ n ∈ Ioc 0 T \ (P ∪ S), vonMangoldt n ≤ _
  linarith

open ArithmeticFunction in
/-- Any class with a negative quadratic sign excludes every square norm. The cost of
restricting its complete Riesz sum to prime norms is uniformly of order T^(4/3). -/
theorem quadraticPrimePowerCell_sub_prime_le {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {T : ℕ} (hT : 1 ≤ T)
    {x : ℝ} (hx : x ≤ T) (q d : ℕ) {e f : ℝ} (hneg : e = -1 ∨ f = -1) :
    |quadraticPrimePowerCellRieszSum χ T x q d e f - quadraticPrimeCellRieszSum χ T x q d e f| ≤
      8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*T*(T:ℝ)^(3:ℝ)⁻¹ := by
  classical
  let A := Ioc 0 T
  let P := Nat.primesLE T
  let S := (Ioc 0 (Nat.sqrt T)).image (fun n : ℕ ↦ n^2)
  let R := A \ (P ∪ S)
  let D : ℝ := Module.finrank ℚ F
  let g (n : ℕ) := if (jacobiSym q n : ℝ) = e ∧ (jacobiSym d n : ℝ) = f then
    (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n).re * max (x-n) 0 else 0
  have sqzero {n : ℕ} (hn : n ∈ S) : g n = 0 := by
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hn
    apply ite_eq_right
    rintro ⟨hq,hd⟩
    simp only [jacobiSym.pow_right, Int.cast_pow] at hq hd
    rcases hneg with rfl | rfl <;> nlinarith only [hq,hd,sq_nonneg (jacobiSym q a : ℝ),
      sq_nonneg (jacobiSym d a : ℝ)]
  have hP : P ⊆ A := fun _ hn ↦ mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hn).pos,
    Nat.le_of_mem_primesLE hn⟩
  have hPR : Disjoint P R := Finset.disjoint_left.mpr fun _ hp hr ↦
    (mem_sdiff.mp hr).2 (mem_union_left _ hp)
  have hR : ∑ n ∈ A, g n = (∑ n ∈ P, g n) + ∑ n ∈ R, g n := by
    rw [← sum_union hPR]
    symm
    apply sum_subset (union_subset hP sdiff_subset)
    intro n hn hout
    have hp : n ∉ P := fun hp ↦ hout (mem_union_left _ hp)
    apply sqzero
    by_contra hs
    exact hout (mem_union_right _ (mem_sdiff.mpr ⟨hn, fun h ↦ (mem_union.mp h).elim hp hs⟩))
  have major (n : ℕ) : |g n| ≤ D*T*vonMangoldt n := by
    dsimp only [g]
    split_ifs
    · rw [abs_mul, abs_of_nonneg (le_max_right (x-n) (0:ℝ))]
      calc _ ≤ (D*vonMangoldt n)*T := by
             apply mul_le_mul ((Complex.abs_re_le_norm _).trans
               (heckeLogDerivCoefficient_le_vonMangoldt χ n)) _ (le_max_right _ _)
               (mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg)
             exact max_le ((sub_le_self _ (Nat.cast_nonneg n)).trans hx) (Nat.cast_nonneg _)
           _ = _ := by ring
    · rw [abs_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) vonMangoldt_nonneg
  have hrem : ∑ n ∈ R, |g n| ≤ D*T*(2*(Real.log 4+4)*(T:ℝ)^(3:ℝ)⁻¹) := by
    calc _ ≤ ∑ n ∈ R, D*T*vonMangoldt n := sum_le_sum fun n _ ↦ major n
         _ ≤ _ := by
           rw [← mul_sum]
           exact mul_le_mul_of_nonneg_left (quadraticPrime_nonsquare_mass T hT)
             (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simp only [quadraticPrimePowerCellRieszSum, quadraticPrimeCellRieszSum, sum_filter]
  change |4*(∑ n ∈ A, g n)-4*(∑ n ∈ P, g n)| ≤ _
  rw [hR, mul_add, add_sub_cancel_left, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  calc _ ≤ 4*(D*T*(2*(Real.log 4+4)*(T:ℝ)^(3:ℝ)⁻¹)) :=
           mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans hrem) (by norm_num)
       _ = _ := by dsimp only [D]; ring

/-- The cost of replacing primes by all norms in any of the three nonidentity cells is
O(J^(19/3)) for the cumulative fourth-power deficit, with arbitrary center values.
A new nonidentity cell may be chosen at each sample. -/
theorem quadraticPrimePowerCell_fourthPower_deficit_sub_prime {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {J : ℕ} (hJ : 1 ≤ J)
    (q d : ℕ) (c e f : ℕ → ℝ) (hneg : ∀ j ∈ Ioc 0 J, e j = -1 ∨ f j = -1) :
    |(∑ j ∈ Ioc 0 J, max (c j - quadraticPrimePowerCellRieszSum χ (J^4) ((j:ℝ)^4)
        q d (e j) (f j)) 0) -
      ∑ j ∈ Ioc 0 J, max (c j - quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4)
        q d (e j) (f j)) 0| ≤
      8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3:ℝ) := by
  let B := 8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ _j ∈ Ioc 0 J, B*(J:ℝ)^4*((J:ℝ)^4)^(3:ℝ)⁻¹ := by
           apply sum_le_sum
           intro j hj
           have hx : (j:ℝ)^4 ≤ ((J^4:ℕ):ℝ) := by
             exact_mod_cast Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4
           have hp := quadraticPrimePowerCell_sub_prime_le χ
             (show 1 ≤ J^4 from one_le_pow₀ hJ) hx q d (hneg j hj)
           have hlip (a b : ℝ) : |max (c j-a) 0 - max (c j-b) 0| ≤ |a-b| := by
             simpa only [sub_sub_sub_cancel_left, abs_sub_comm b a] using
               abs_max_sub_max_le_abs (c j-a) (c j-b) 0
           apply (hlip _ _).trans
           simpa only [Nat.cast_pow, B] using hp
       _ = _ := by
         simp only [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
         have hpow : (J:ℝ)^(19/3:ℝ) = (J:ℝ)*((J:ℝ)^4*((J:ℝ)^4)^(3:ℝ)⁻¹) := by
           have hpos : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by omega)
           rw [show (19/3:ℝ) = 1+(4+4*3⁻¹) by norm_num, Real.rpow_add hpos, Real.rpow_one,
             Real.rpow_add hpos, Real.rpow_mul hpos.le]
           norm_cast
         rw [hpow]
         dsimp only [B]
         ring

open Filter in
/-- A bound H for the full prime-power deficits in any nonempty family of selected
nonidentity cells bounds the unrestricted prime deficit. The cardinalities display
the exact cost of the proportion of auxiliary pairs on which the bound is available. -/
theorem quadraticPrimePowerCell_fourthPower_deficit_transfer {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∀ᶠ J : ℕ in atTop, let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
      ∀ (c : ℕ → ℝ) (e f : ℕ → ℕ → ℕ → ℝ),
      (∀ q d j, |e q d j| = 1) → (∀ q d j, |f q d j| = 1) →
      ∀ (G : Finset (ℕ × ℕ)), G ⊆ U ×ˢ U → ∀ H : ℝ,
      (∀ w ∈ G, ∀ j ∈ Ioc 0 J, e w.1 w.2 j = -1 ∨ f w.1 w.2 j = -1) →
      (∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j - quadraticPrimePowerCellRieszSum χ (J^4) ((j:ℝ)^4)
        w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j)) 0 ≤ H) →
      G.card * ((∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0)
        - H - 8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3:ℝ)) ≤
        (U.card:ℝ)^2*(300*(Module.finrank ℚ F : ℝ)*(J:ℝ)^7*Real.log (2+J)) := by
  filter_upwards [quadraticPrimeTwist_fourthPower_deficit_mean χ, eventually_ge_atTop 1] with J hm hJ
  intro U c e f he hf G hG H hneg hH
  let A := ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0
  let P (w : ℕ × ℕ) := ∑ j ∈ Ioc 0 J, max (c j - quadraticPrimeCellRieszSum χ (J^4)
    ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j)) 0
  let B := 8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3:ℝ)
  have hpoint (w : ℕ × ℕ) (hw : w ∈ G) : A-H-B ≤ |P w-A| := by
    have hpow := quadraticPrimePowerCell_fourthPower_deficit_sub_prime χ hJ w.1 w.2 c
      (e w.1 w.2) (f w.1 w.2) (hneg w hw)
    have h := (abs_le.mp hpow).1
    change -B ≤ _ - P w at h
    linarith [hH w hw, neg_le_abs (P w-A)]
  calc G.card*(A-H-B) = ∑ _w ∈ G, (A-H-B) := by simp only [sum_const, nsmul_eq_mul]
       _ ≤ ∑ w ∈ G, |P w-A| := sum_le_sum hpoint
       _ ≤ ∑ w ∈ U ×ˢ U, |P w-A| := sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ ↦ abs_nonneg _)
       _ ≤ _ := by
         rw [sum_product]
         exact hm c e f he hf

end RiemannMasullo
