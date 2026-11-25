module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Prime Riesz sums over a family of Dirichlet characters

For Theorem 12.5.1.1, pp. 519–520, bound the actual first-prime Riesz sums of
characters of prime modulus over all integral cutoffs up to that modulus.
Orthogonality controls each prime prefix. A summable logarithmic weight gives
one exceptional set for every cutoff and every fourth-power prefix. Below the
semiprime collision threshold, the signed deficits of a positive fraction of the
nonprincipal characters have fourth-power prefix size J⁷√(log J).
-/

open Finset
open scoped ComplexConjugate

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Exact second moment of a Dirichlet polynomial supported on distinct units below q. -/
theorem dirichletPrime_character_orthogonality {q : ℕ} [NeZero q] (P : Finset ℕ)
    (hlt : ∀ p ∈ P, p < q) (hu : ∀ p ∈ P, IsUnit (p : ZMod q)) (b : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ p ∈ P, b p * χ (p : ZMod q)‖ ^ 2 =
      q.totient * ∑ p ∈ P, ‖b p‖ ^ 2 := by
  classical
  have ortho (p : ℕ) (hp : p ∈ P) (r : ℕ) (hr : r ∈ P) :
      ∑ χ : DirichletCharacter ℂ q, conj (χ (p : ZMod q)) * χ (r : ZMod q) =
        if p = r then (q.totient : ℂ) else 0 := by
    have he : ((p : ZMod q) = (r : ZMod q)) ↔ p = r := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt p hp), Nat.mod_eq_of_lt (hlt r hr)]
    obtain ⟨u, hu'⟩ := hu p hp
    have hi : Ring.inverse (p : ZMod q) = (p : ZMod q)⁻¹ := by
      rw [← hu', Ring.inverse_unit]
      simp
    simpa only [← RCLike.star_def, MulChar.star_apply', MulChar.inv_apply, hi, he] using
      (DirichletCharacter.sum_char_inv_mul_char_eq ℂ (hu p hp) (r : ZMod q))
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.conj_mul']
  simp only [map_sum, map_mul, sum_mul, mul_sum]
  calc _ = ∑ p ∈ P, ∑ r ∈ P, (conj (b r) * b p) *
             ∑ χ : DirichletCharacter ℂ q, conj (χ (r : ZMod q)) * χ (p : ZMod q) := by
           rw [sum_comm]
           apply sum_congr rfl
           intro p hp
           rw [sum_comm]
           apply sum_congr rfl
           intro r hr
           rw [mul_sum]
           apply sum_congr rfl
           intro χ _
           ring
       _ = _ := by
         apply sum_congr rfl
         intro p hp
         simp_rw [sum_congr rfl (fun r hr ↦ congrArg (fun z : ℂ ↦ (conj (b r)*b p)*z) (ortho r hr p hp))]
         simp [hp, mul_comm]

/-- First Riesz sum of a complex prime coefficient, twisted by a Dirichlet character. -/
def dirichletPrimeRiesz {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℕ → ℂ) (x : ℕ) : ℂ :=
  ∑ p ∈ Nat.primesLE x, ((x:ℂ)-p) * (b p * χ (p : ZMod q))

private theorem dirichletPrime_sum_prefix (b : ℕ → ℂ) (x : ℕ) :
    ∑ n ∈ range x, ∑ p ∈ Nat.primesLE n, b p =
      ∑ p ∈ Nat.primesLE x, ((x:ℂ)-p)*b p := by
  have he (n : ℕ) (hn : n ∈ range x) :
      Nat.primesLE n = (Nat.primesLE x).filter (fun p ↦ p ≤ n) := by
    ext p
    simp only [Nat.mem_primesLE, mem_filter]
    constructor
    · rintro ⟨h,hp⟩; exact ⟨⟨h.trans (mem_range.mp hn).le,hp⟩,h⟩
    · rintro ⟨⟨_,hp⟩,h⟩; exact ⟨h,hp⟩
  calc _ = ∑ n ∈ range x, ∑ p ∈ Nat.primesLE x, if p ≤ n then b p else 0 := by
           apply sum_congr rfl
           intro n hn
           rw [he n hn, sum_filter]
       _ = _ := by
           rw [sum_comm]
           apply sum_congr rfl
           intro p hp
           rw [← sum_filter]
           have hset : (range x).filter (fun n ↦ p ≤ n) = Ico p x := by ext n; simp [and_comm]
           rw [hset, sum_const, Nat.card_Ico, nsmul_eq_mul,
             Nat.cast_sub (Nat.le_of_mem_primesLE hp)]

private theorem dirichletPrime_prefix_moment {q : ℕ} [Fact q.Prime] (b : ℕ → ℂ)
    {D : ℝ} (_hD : 0 ≤ D) (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ D*Real.log p)
    (n : ℕ) (hn : n < q) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ p ∈ Nat.primesLE n, b p * χ (p : ZMod q)‖^2 ≤
      q.totient * (D^2 * Real.log 4 * (n:ℝ) * Real.log ((n:ℝ)+3)) := by
  have hlt (p : ℕ) (hp : p ∈ Nat.primesLE n) : p < q := (Nat.le_of_mem_primesLE hp).trans_lt hn
  have hu (p : ℕ) (hp : p ∈ Nat.primesLE n) : IsUnit (p : ZMod q) :=
    (ZMod.isUnit_iff_coprime _ _).mpr ((Nat.coprime_primes
      (Nat.prime_of_mem_primesLE hp) Fact.out).mpr (hlt p hp).ne)
  rw [dirichletPrime_character_orthogonality (Nat.primesLE n) hlt hu b]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.log ((n:ℝ)+3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  calc _ ≤ ∑ p ∈ Nat.primesLE n, (D^2 * Real.log ((n:ℝ)+3)) * Real.log p := by
           apply sum_le_sum
           intro p hp
           have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
           have hp' : (p:ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primesLE hp
           have hl' : Real.log p ≤ Real.log ((n:ℝ)+3) :=
             Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) (by linarith)
           calc _ ≤ (D*Real.log p)^2 := pow_le_pow_left₀ (norm_nonneg _) (hb p (Nat.prime_of_mem_primesLE hp)) 2
                _ = (D^2*Real.log p)*Real.log p := by ring
                _ ≤ _ := by gcongr
       _ = (D^2*Real.log ((n:ℝ)+3))*Chebyshev.theta n := by
           rw [← mul_sum, Chebyshev.theta_eq_sum_primesLE_log]
       _ ≤ (D^2*Real.log ((n:ℝ)+3))*(Real.log 4*n) :=
           mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)) (by positivity)
       _ = _ := by ring

private theorem dirichletPrime_log_step (n : ℕ) :
    1 / (((n:ℝ)+3) * Real.log ((n:ℝ)+3)^2) ≤
      (Real.log ((n:ℝ)+2))⁻¹ - (Real.log ((n:ℝ)+3))⁻¹ := by
  let a := (n:ℝ)+2
  have ha : 1 < a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have ha' : 0 < a := by linarith
  have ht : 0 < a+1 := by linarith
  have hla := Real.log_pos ha
  have hlt := Real.log_pos (show 1 < a+1 by linarith)
  have hm : Real.log a ≤ Real.log (a+1) := Real.log_le_log ha' (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos ht ha')
  rw [Real.log_div ht.ne' ha'.ne', inv_div] at hl
  have diff : 1/(a+1) ≤ Real.log (a+1)-Real.log a := by
    calc _ = 1-a/(a+1) := by field_simp; ring
         _ ≤ _ := hl
  have hd : (0:ℝ) < Real.log a * Real.log (a+1) := mul_pos hla hlt
  change 1/(((n:ℝ)+3)*Real.log ((n:ℝ)+3)^2) ≤ _
  rw [show (n:ℝ)+3 = a+1 by dsimp [a]; ring]
  change _ ≤ (Real.log a)⁻¹-(Real.log (a+1))⁻¹
  calc _ ≤ (1/(a+1))/(Real.log a*Real.log (a+1)) := by
           rw [div_div]
           apply one_div_le_one_div_of_le (mul_pos ht hd)
           gcongr
           nlinarith only [mul_le_mul_of_nonneg_right hm hlt.le]
       _ ≤ (Real.log (a+1)-Real.log a)/(Real.log a*Real.log (a+1)) := by gcongr
       _ = _ := by field_simp

/-- A logarithmically weighted sum of prime-prefix energies. One bound for this score controls
the Riesz sums of the same character at every integral cutoff up to its modulus. -/
def dirichletPrimePrefixEnergy {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℕ → ℂ) : ℝ :=
  ∑ n ∈ range q, ‖∑ p ∈ Nat.primesLE n, b p * χ (p : ZMod q)‖^2 /
    (((n:ℝ)+3)^2 * Real.log ((n:ℝ)+3)^3)

/-- The mean score over all characters of a prime modulus is at most twice the square
of the coefficient bound, uniformly in the modulus. -/
theorem dirichletPrimePrefixEnergy_sum_le {q : ℕ} [Fact q.Prime]
    (b : ℕ → ℂ) {D : ℝ} (hD : 0 ≤ D) (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ D*Real.log p) :
    ∑ χ : DirichletCharacter ℂ q, dirichletPrimePrefixEnergy χ b ≤ 2*q.totient*D^2 := by
  let A := (q.totient:ℝ)*D^2*Real.log 4
  have hA : 0 ≤ A := by dsimp [A]; positivity
  simp only [dirichletPrimePrefixEnergy]
  rw [sum_comm]
  calc _ ≤ ∑ n ∈ range q, A*((Real.log ((n:ℝ)+2))⁻¹-(Real.log ((n:ℝ)+3))⁻¹) := by
           apply sum_le_sum
           intro n hn
           rw [← sum_div]
           have ht : (0:ℝ) < (n:ℝ)+3 := by positivity
           have hl : 0 < Real.log ((n:ℝ)+3) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
           have h := dirichletPrime_prefix_moment b hD hb n (mem_range.mp hn)
           calc _ ≤ ((q.totient:ℝ)*(D^2*Real.log 4*n*Real.log ((n:ℝ)+3))) /
               (((n:ℝ)+3)^2*Real.log ((n:ℝ)+3)^3) := by gcongr
                _ ≤ A*(1/(((n:ℝ)+3)*Real.log ((n:ℝ)+3)^2)) := by
                  dsimp [A]
                  field_simp
                  nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) q.totient)
                    (sq_nonneg D)) (Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num))]
                _ ≤ _ := mul_le_mul_of_nonneg_left (dirichletPrime_log_step n) hA
       _ = A*((Real.log 2)⁻¹-(Real.log ((q:ℝ)+2))⁻¹) := by
           rw [← mul_sum]
           congr 1
           have h := sum_range_sub (fun n : ℕ ↦ -(Real.log ((n:ℝ)+2))⁻¹) q
           simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add,neg_sub_neg,
             show ∀ n : ℝ, n+1+2=n+3 by intro; ring] using h
       _ ≤ A*(Real.log 2)⁻¹ := by
           gcongr
           apply sub_le_self
           exact inv_nonneg.mpr (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q]))
       _ = _ := by
           have hl : Real.log (4:ℝ) = 2*Real.log 2 := by
             rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
           dsimp [A]
           rw [hl]
           field_simp [ne_of_gt (Real.log_pos (show (1:ℝ)<2 by norm_num))]

/-- The single character score bounds the actual complex prime Riesz sum at every
integer cutoff up to the modulus. -/
theorem dirichletPrimeRiesz_sq_le_prefixEnergy {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℕ → ℂ) {x : ℕ} (hx : x ≤ q) :
    ‖dirichletPrimeRiesz χ b x‖^2 ≤
      x*((x:ℝ)+2)^2 * Real.log ((x:ℝ)+2)^3 * dirichletPrimePrefixEnergy χ b := by
  let F (n : ℕ) := ∑ p ∈ Nat.primesLE n, b p * χ (p : ZMod q)
  let W (n : ℕ) := ((n:ℝ)+3)^2*Real.log ((n:ℝ)+3)^3
  let K := ((x:ℝ)+2)^2*Real.log ((x:ℝ)+2)^3
  have hW (n : ℕ) : 0 < W n := by
    have h : 0 < Real.log ((n:ℝ)+3) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [W]; positivity
  have hK : 0 ≤ K := by
    have h : 0 ≤ Real.log ((x:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) x])
    dsimp [K]; positivity
  have hs : ∑ n ∈ range x, ‖F n‖^2 ≤ K * dirichletPrimePrefixEnergy χ b := by
    calc _ ≤ ∑ n ∈ range x, K*(‖F n‖^2/W n) := by
           apply sum_le_sum
           intro n hn
           have hnx : (n:ℝ)+3 ≤ (x:ℝ)+2 := by
             exact_mod_cast (show n+3 ≤ x+2 by have := mem_range.mp hn; omega)
           have hlog : 0 ≤ Real.log ((n:ℝ)+3) :=
             Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
           have hwk : W n ≤ K := by
             dsimp [W,K]
             gcongr
           calc _ = W n*(‖F n‖^2/W n) := by field_simp [(hW n).ne']
                _ ≤ _ := mul_le_mul_of_nonneg_right hwk (div_nonneg (sq_nonneg _) (hW n).le)
         _ ≤ ∑ n ∈ range q, K*(‖F n‖^2/W n) :=
           sum_le_sum_of_subset_of_nonneg (range_mono hx)
             (fun n _ _ ↦ mul_nonneg hK (div_nonneg (sq_nonneg _) (hW n).le))
         _ = _ := by simp only [dirichletPrimePrefixEnergy,F,W,mul_sum]
  have hR : dirichletPrimeRiesz χ b x = ∑ n ∈ range x, F n :=
    (dirichletPrime_sum_prefix (fun p ↦ b p * χ (p : ZMod q)) x).symm
  rw [hR]
  calc _ ≤ (∑ n ∈ range x, ‖F n‖)^2 :=
           pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2
       _ ≤ (x:ℝ)*∑ n ∈ range x, ‖F n‖^2 := by
           simpa only [card_range] using sq_sum_le_card_mul_sum_sq (s := range x) (f := fun n ↦ ‖F n‖)
       _ ≤ (x:ℝ)*(K*dirichletPrimePrefixEnergy χ b) := by gcongr
       _ = _ := by dsimp [K]; ring

/-- Almost all characters of a prime modulus simultaneously have small complex Riesz
sums at every integer cutoff and small total absolute sums along every quartic prefix.
For a nonprincipal character, the latter majorizes its cumulative one-sided deficit.
The exceptional proportion is at most 2D²/L. -/
theorem dirichletPrimeRiesz_family_prefixes {q : ℕ} [Fact q.Prime]
    (b : ℕ → ℂ) {D L : ℝ} (hD : 0 ≤ D) (hL : 0 < L)
    (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ D*Real.log p) :
    ∃ E : Finset (DirichletCharacter ℂ q), (E.card:ℝ)*L ≤ 2*q.totient*D^2 ∧
      ∀ χ ∉ E, (∀ x : ℕ, x ≤ q → ‖dirichletPrimeRiesz χ b x‖^2 ≤
          x*((x:ℝ)+2)^2*Real.log ((x:ℝ)+2)^3*L) ∧
        ∀ J : ℕ, J^4 ≤ q → (∑ j ∈ Ioc 0 J, ‖dirichletPrimeRiesz χ b (j^4)‖)^2 ≤
          9*L*(J:ℝ)^14*Real.log ((J:ℝ)^4+2)^3 := by
  classical
  let E := univ.filter (fun χ : DirichletCharacter ℂ q ↦ L < dirichletPrimePrefixEnergy χ b)
  have hen (χ : DirichletCharacter ℂ q) : 0 ≤ dirichletPrimePrefixEnergy χ b := by
    apply sum_nonneg
    intro n _
    have hl : 0 ≤ Real.log ((n:ℝ)+3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  refine ⟨E, ?_, ?_⟩
  · calc _ = ∑ _χ ∈ E, L := by simp
         _ ≤ ∑ χ ∈ E, dirichletPrimePrefixEnergy χ b :=
           sum_le_sum fun _ h ↦ (mem_filter.mp h).2.le
         _ ≤ ∑ χ : DirichletCharacter ℂ q, dirichletPrimePrefixEnergy χ b :=
           sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun χ _ _ ↦ hen χ)
         _ ≤ _ := dirichletPrimePrefixEnergy_sum_le b hD hb
  intro χ hχ
  have he : dirichletPrimePrefixEnergy χ b ≤ L :=
    le_of_not_gt fun h ↦ hχ (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hp (x : ℕ) (hx : x ≤ q) : ‖dirichletPrimeRiesz χ b x‖^2 ≤
      x*((x:ℝ)+2)^2*Real.log ((x:ℝ)+2)^3*L := by
    have hl : 0 ≤ Real.log ((x:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) x])
    exact (dirichletPrimeRiesz_sq_le_prefixEnergy χ b hx).trans (mul_le_mul_of_nonneg_left he (by positivity))
  refine ⟨hp, ?_⟩
  intro J hJ
  have hsingle (j : ℕ) (hj : j ∈ Ioc 0 J) : ‖dirichletPrimeRiesz χ b (j^4)‖^2 ≤
      9*L*(J:ℝ)^12*Real.log ((J:ℝ)^4+2)^3 := by
    have hj₁ : 1 ≤ (j:ℝ)^4 := one_le_pow₀ (by exact_mod_cast (mem_Ioc.mp hj).1 : (1:ℝ) ≤ j)
    have hjJ := Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4
    have hcast : (j:ℝ)^4 ≤ (J:ℝ)^4 := by exact_mod_cast hjJ
    have hl : 0 ≤ Real.log ((j:ℝ)^4+2) :=
      Real.log_nonneg (by linarith)
    have h := hp (j^4) (hjJ.trans hJ)
    push_cast at h
    calc _ ≤ _ := h
         _ ≤ (J:ℝ)^4 * (3*(J:ℝ)^4)^2 * Real.log ((J:ℝ)^4+2)^3 * L := by
           gcongr
           linarith
         _ = _ := by ring
  calc _ ≤ (J:ℝ)*∑ j ∈ Ioc 0 J, ‖dirichletPrimeRiesz χ b (j^4)‖^2 := by
           simpa only [Nat.card_Ioc,Nat.sub_zero] using sq_sum_le_card_mul_sum_sq
             (s := Ioc 0 J) (f := fun j ↦ ‖dirichletPrimeRiesz χ b (j^4)‖)
       _ ≤ (J:ℝ)*∑ _j ∈ Ioc 0 J, 9*L*(J:ℝ)^12*Real.log ((J:ℝ)^4+2)^3 :=
           mul_le_mul_of_nonneg_left (sum_le_sum hsingle) (Nat.cast_nonneg _)
       _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero]; ring

open NumberField in
/-- Apply the simultaneous estimate to the genuine degree-one logarithmic-derivative
coefficients of any fixed unitary Hecke character. The raw twisted one-sided prime
deficits use zero center, as appropriate for nonprincipal targets. -/
theorem dirichletPrimeRiesz_hecke_twist_deficits {F : Type*} [Field F] [NumberField F]
    (ξ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {q : ℕ} [Fact q.Prime] {L : ℝ} (hL : 0 < L) :
    let b := heckeLogDerivCoefficient (ideleClassNormTwist ξ 0)
    ∃ E : Finset (DirichletCharacter ℂ q),
      (E.card:ℝ)*L ≤ 2*q.totient*(Module.finrank ℚ F:ℝ)^2 ∧
      ∀ χ ∉ E, ∀ J : ℕ, J^4 ≤ q →
        (∑ j ∈ Ioc 0 J, max (-(dirichletPrimeRiesz χ b (j^4)).re) 0)^2 ≤
          9*L*(J:ℝ)^14*Real.log ((J:ℝ)^4+2)^3 := by
  intro b
  have hb (p : ℕ) (hp : p.Prime) : ‖b p‖ ≤ (Module.finrank ℚ F:ℝ)*Real.log p := by
    simpa only [ArithmeticFunction.vonMangoldt_apply_prime hp] using
      heckeLogDerivCoefficient_le_vonMangoldt ξ p
  obtain ⟨E,hE,hfamily⟩ := dirichletPrimeRiesz_family_prefixes (q := q) b (Nat.cast_nonneg _) hL hb
  refine ⟨E,hE,fun χ hχ J hJ ↦ ?_⟩
  apply le_trans _ ((hfamily χ hχ).2 J hJ)
  apply pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ le_max_right ..) _ 2
  apply sum_le_sum
  intro j _
  exact max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)

/-- Sum of the squared deviations of the prime Riesz masses in the nonzero
residue classes from their common arithmetic mean. -/
def dirichletPrimeProgressionVariance (q : ℕ) (b : ℕ → ℂ) (x : ℕ) : ℝ :=
    let A := (range q).erase 0
    let M (a : ℕ) := ∑ p ∈ (Nat.primesLE x).filter (fun p ↦ p % q = a), ((x:ℂ)-p)*b p
    let μ := (∑ a ∈ A, M a)/(A.card:ℂ)
    ∑ a ∈ A, ‖M a-μ‖^2

private theorem dirichletPrime_sum_range_zmod {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a ∈ range q, f a) = ∑ a : ZMod q, f a := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun a _ ↦ congrArg f (Fin.cast_val_eq_self a)

open Classical in
/-- At every cutoff, even above q, the total squared Riesz norm of the nonprincipal
characters is φ(q) times the variance sum of the reduced progression masses. -/
theorem dirichletPrimeRiesz_nonprincipal_variance {q : ℕ} [Fact q.Prime] (b : ℕ → ℂ) (x : ℕ) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖dirichletPrimeRiesz χ b x‖^2 =
      q.totient * dirichletPrimeProgressionVariance q b x := by
  classical
  let A := (range q).erase 0
  let M (a : ℕ) := ∑ p ∈ (Nat.primesLE x).filter (fun p ↦ p % q = a), ((x:ℂ)-p)*b p
  let μ := (∑ a ∈ A, M a)/(A.card:ℂ)
  have hq : q.Prime := Fact.out
  have h0 : 0 ∈ range q := mem_range.mpr hq.pos
  have hlt (a : ℕ) (ha : a ∈ A) : a < q := mem_range.mp (mem_erase.mp ha).2
  have hu (a : ℕ) (ha : a ∈ A) : IsUnit (a : ZMod q) := by
    apply isUnit_iff_ne_zero.mpr
    rw [Ne, ← Nat.cast_zero (R := ZMod q), ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt a ha),
      Nat.zero_mod]
    exact (mem_erase.mp ha).1
  have hn : (A.card:ℂ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr ⟨1,mem_erase.mpr ⟨by decide,mem_range.mpr hq.one_lt⟩⟩ : 0 < A.card).ne'
  have grouped (χ : DirichletCharacter ℂ q) :
      ∑ a ∈ A, M a * χ (a : ZMod q) = dirichletPrimeRiesz χ b x := by
    calc _ = ∑ a ∈ range q, M a * χ (a : ZMod q) := by
             dsimp only [A]
             rw [sum_erase_eq_sub h0]
             simp [MulChar.map_zero]
         _ = _ := by
           simp only [M, sum_filter, sum_mul, ite_mul, zero_mul]
           rw [sum_comm]
           apply sum_congr rfl
           intro p _
           simp [Nat.mod_lt p hq.pos,mul_assoc]
  let T (χ : DirichletCharacter ℂ q) := ∑ a ∈ A, (M a-μ)*χ (a : ZMod q)
  have hnon (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : T χ = dirichletPrimeRiesz χ b x := by
    have hz : ∑ a ∈ A, χ (a : ZMod q) = 0 := by
      dsimp only [A]
      rw [sum_erase_eq_sub h0, dirichletPrime_sum_range_zmod]
      simp [MulChar.sum_eq_zero_of_ne_one hχ, MulChar.map_zero]
    simp only [T,sub_mul,sum_sub_distrib,← mul_sum,grouped,hz,mul_zero,sub_zero]
  have hone : T 1 = 0 := by
    calc _ = ∑ a ∈ A, (M a-μ) := sum_congr rfl fun a ha ↦ by rw [MulChar.one_apply (hu a ha),mul_one]
         _ = 0 := by
           simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,μ]
           field_simp
           simp
  calc _ = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖T χ‖^2 :=
           sum_congr rfl fun χ hχ ↦ by rw [hnon χ (mem_erase.mp hχ).1]
       _ = ∑ χ : DirichletCharacter ℂ q, ‖T χ‖^2 := by
           rw [sum_erase_eq_sub (mem_univ _), hone]; simp
       _ = _ := dirichletPrime_character_orthogonality A hlt hu (fun a ↦ M a-μ)

/-- Count deep negative values of one fixed nonprincipal character by the variance of the
observed progression masses. This bound has no restriction on sample size relative to q. -/
theorem dirichletPrimeRiesz_negative_samples {q : ℕ} [Fact q.Prime] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (b : ℕ → ℂ) (I : Finset ℕ) (x : ℕ → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((I.filter fun j ↦ (dirichletPrimeRiesz χ b (x j)).re < -t).card : ℝ) * t^2 ≤
      q.totient * ∑ j ∈ I, dirichletPrimeProgressionVariance q b (x j) := by
  classical
  let B := I.filter fun j ↦ (dirichletPrimeRiesz χ b (x j)).re < -t
  have hpt (j : ℕ) (hj : j ∈ B) : t^2 ≤ ‖dirichletPrimeRiesz χ b (x j)‖^2 := by
    apply pow_le_pow_left₀ ht
    have h := (mem_filter.mp hj).2
    exact (show t ≤ -(dirichletPrimeRiesz χ b (x j)).re by linarith).trans
      ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  calc _ = ∑ _j ∈ B, t^2 := by simp [B]
       _ ≤ ∑ j ∈ B, ‖dirichletPrimeRiesz χ b (x j)‖^2 := sum_le_sum hpt
       _ ≤ ∑ j ∈ I, ‖dirichletPrimeRiesz χ b (x j)‖^2 :=
           sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ ↦ sq_nonneg _)
       _ ≤ ∑ j ∈ I, q.totient * dirichletPrimeProgressionVariance q b (x j) := by
           apply sum_le_sum
           intro j _
           rw [← dirichletPrimeRiesz_nonprincipal_variance]
           exact single_le_sum (f := fun ψ ↦ ‖dirichletPrimeRiesz ψ b (x j)‖^2)
             (fun ψ _ ↦ sq_nonneg _) (mem_erase.mpr ⟨hχ,mem_univ χ⟩)
       _ = _ := by rw [mul_sum]

private theorem dirichletPrime_semiprime_fiber {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime) (n : ℕ) :
    ((P ×ˢ P).filter (fun z ↦ z.1*z.2 = n)).card ≤ 2 := by
  classical
  let F := (P ×ˢ P).filter (fun z ↦ z.1*z.2 = n)
  by_cases h : F.Nonempty
  · obtain ⟨⟨a,b⟩,hab⟩ := h
    obtain ⟨hm,hn⟩ := mem_filter.mp hab
    obtain ⟨ha,hb⟩ := mem_product.mp hm
    have sub : F ⊆ {(a,b),(b,a)} := by
      rintro ⟨p,r⟩ hz
      obtain ⟨hz,he⟩ := mem_filter.mp hz
      obtain ⟨hp',hr⟩ := mem_product.mp hz
      have eqn : p*r = a*b := he.trans hn.symm
      have hd : p ∣ a*b := eqn ▸ dvd_mul_right p r
      rcases (hp _ hp').dvd_mul.mp hd with hd | hd
      · have e := (Nat.prime_dvd_prime_iff_eq (hp p hp') (hp a ha)).mp hd
        subst p
        have er : r = b := Nat.eq_of_mul_eq_mul_left (hp _ ha).pos eqn
        simp [er]
      · have e := (Nat.prime_dvd_prime_iff_eq (hp p hp') (hp b hb)).mp hd
        subst p
        rw [mul_comm a b] at eqn
        have er : r = a := Nat.eq_of_mul_eq_mul_left (hp _ hb).pos eqn
        simp [er]
    apply (card_le_card sub).trans
    exact (card_insert_le (a,b) ({(b,a)} : Finset (ℕ × ℕ))).trans_eq (by simp)
  · change F.card ≤ 2
    rw [not_nonempty_iff_eq_empty.mp h]; decide

private theorem dirichletPrime_group_square {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (b : ℕ → ℂ) :
    (∑ p ∈ P, b p * χ (p : ZMod q))^2 =
      ∑ n ∈ (P ×ˢ P).image (fun z ↦ z.1*z.2),
        (∑ z ∈ (P ×ˢ P).filter (fun z ↦ z.1*z.2 = n), b z.1*b z.2) * χ (n : ZMod q) := by
  let f (z : ℕ × ℕ) := z.1*z.2
  calc _ = ∑ z ∈ P ×ˢ P, b z.1*b z.2*χ ((f z : ℕ) : ZMod q) := by
           rw [sum_product, pow_two, sum_mul]
           apply sum_congr rfl
           intro p _
           rw [mul_sum]
           apply sum_congr rfl
           intro r _
           simp [f,map_mul,mul_assoc,mul_comm,mul_left_comm]
       _ = _ := by
           rw [← sum_fiberwise_of_maps_to (t := (P ×ˢ P).image f)
             (fun z (hz : z ∈ P ×ˢ P) ↦ mem_image_of_mem f hz)
             (fun z : ℕ × ℕ ↦ b z.1*b z.2*χ ((f z : ℕ) : ZMod q))]
           apply sum_congr rfl
           intro n _
           rw [sum_mul]
           apply sum_congr rfl
           intro z hz
           rw [(mem_filter.mp hz).2]

/-- Fourth moment below the semiprime collision threshold. An integer product of two
primes contributes at most two ordered representations. -/
theorem dirichletPrime_fourthMoment {q : ℕ} [Fact q.Prime] (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, ∀ r ∈ P, p*r < q) (b : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ p ∈ P, b p*χ (p : ZMod q)‖^4 ≤
      2*q.totient*(∑ p ∈ P, ‖b p‖^2)^2 := by
  let A := P ×ˢ P
  let f (z : ℕ × ℕ) := z.1*z.2
  let M := A.image f
  let C (n : ℕ) := ∑ z ∈ A.filter (fun z ↦ f z = n), b z.1*b z.2
  have hbounds (n : ℕ) (hn : n ∈ M) : 0 < n ∧ n < q := by
    obtain ⟨⟨p,r⟩,hz,rfl⟩ := mem_image.mp hn
    obtain ⟨h₁,h₂⟩ := mem_product.mp hz
    exact ⟨Nat.mul_pos (hp p h₁).pos (hp r h₂).pos,hsize p h₁ r h₂⟩
  have hu (n : ℕ) (hn : n ∈ M) : IsUnit (n : ZMod q) := by
    apply isUnit_iff_ne_zero.mpr
    rw [Ne, ← Nat.cast_zero (R := ZMod q), ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt (hbounds n hn).2,Nat.zero_mod]
    exact (hbounds n hn).1.ne'
  have hc (n : ℕ) : ‖C n‖^2 ≤ 2 * ∑ z ∈ A.filter (fun z ↦ f z = n), ‖b z.1*b z.2‖^2 := by
    calc _ ≤ (∑ z ∈ A.filter (fun z ↦ f z = n), ‖b z.1*b z.2‖)^2 :=
           pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2
         _ ≤ _ := (sq_sum_le_card_mul_sum_sq ..).trans (mul_le_mul_of_nonneg_right
           (by exact_mod_cast dirichletPrime_semiprime_fiber hp n)
           (sum_nonneg fun _ _ ↦ sq_nonneg _))
  have hsem (χ : DirichletCharacter ℂ q) :
      ‖∑ p ∈ P, b p*χ (p : ZMod q)‖^4 = ‖∑ n ∈ M, C n*χ (n : ZMod q)‖^2 := by
    rw [← dirichletPrime_group_square, norm_pow]; ring
  calc _ = ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ M, C n*χ (n : ZMod q)‖^2 :=
           sum_congr rfl (fun χ _ ↦ hsem χ)
       _ = q.totient * ∑ n ∈ M, ‖C n‖^2 := dirichletPrime_character_orthogonality M
           (fun n h ↦ (hbounds n h).2) hu C
       _ ≤ q.totient * ∑ n ∈ M, 2 * ∑ z ∈ A.filter (fun z ↦ f z = n), ‖b z.1*b z.2‖^2 :=
           mul_le_mul_of_nonneg_left (sum_le_sum fun n _ ↦ hc n) (Nat.cast_nonneg _)
       _ = _ := by
           rw [← mul_sum, sum_fiberwise_of_maps_to (fun z (hz : z ∈ A) ↦ mem_image_of_mem f hz)]
           simp only [A,sum_product,norm_mul,mul_pow,← mul_sum,← sum_mul]
           ring

private theorem dirichletPrime_zero_mean {q : ℕ} [Fact q.Prime] (P : Finset ℕ)
    (hP : ∀ n ∈ P, 1 < n ∧ n < q) (b : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ∑ p ∈ P, b p*χ (p : ZMod q) = 0 := by
  rw [sum_comm]
  apply sum_eq_zero
  intro p hp
  rw [← mul_sum, DirichletCharacter.sum_characters_eq_zero]
  · simp
  · rw [Ne, ← Nat.cast_one (R := ZMod q), ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hP p hp).2, Nat.mod_eq_of_lt (Fact.out : q.Prime).one_lt]
    exact (hP p hp).1.ne'

/-- For arbitrary complex prime weights the real part is centered and has exactly
one half of the complex second moment below the semiprime threshold. -/
theorem dirichletPrime_real_moments {q : ℕ} [Fact q.Prime] (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, ∀ r ∈ P, p*r < q) (b : ℕ → ℂ) :
    let Z (χ : DirichletCharacter ℂ q) := ∑ p ∈ P, b p*χ (p : ZMod q)
    (∑ χ, (Z χ).re) = 0 ∧ (2*∑ χ, (Z χ).re^2) = q.totient*∑ p ∈ P, ‖b p‖^2 := by
  intro Z
  have ltq (p : ℕ) (h : p ∈ P) : p < q :=
    (Nat.le_mul_of_pos_right p (hp p h).pos).trans_lt (hsize p h p h)
  have hfirst := dirichletPrime_zero_mean (q := q) P (fun p h ↦ ⟨(hp p h).one_lt,ltq p h⟩) b
  have hsecond : ∑ χ : DirichletCharacter ℂ q, Z χ^2 = 0 := by
    simp only [Z,dirichletPrime_group_square]
    apply dirichletPrime_zero_mean
    intro n hn
    obtain ⟨⟨p,r⟩,hz,rfl⟩ := mem_image.mp hn
    obtain ⟨h₁,h₂⟩ := mem_product.mp hz
    exact ⟨(hp p h₁).one_lt.trans_le (Nat.le_mul_of_pos_right p (hp r h₂).pos),
      hsize p h₁ r h₂⟩
  change ∑ χ, Z χ = 0 at hfirst
  have hfirst' := congrArg Complex.re hfirst
  have hsecond' := congrArg Complex.re hsecond
  simp only [Complex.re_sum,Complex.zero_re] at hfirst' hsecond'
  refine ⟨hfirst', ?_⟩
  have hu (p : ℕ) (h : p ∈ P) : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr
    ((Nat.coprime_primes (hp p h) Fact.out).mpr (ltq p h).ne)
  have id (z : ℂ) : 2*z.re^2 = ‖z‖^2 + (z^2).re := by
    rw [Complex.sq_norm,Complex.normSq_apply,show z^2 = z*z from pow_two z,Complex.mul_re]; ring
  calc _ = ∑ χ, (‖Z χ‖^2 + (Z χ^2).re) := by
           rw [mul_sum]; exact sum_congr rfl fun χ _ ↦ id _
       _ = _ := by rw [sum_add_distrib,hsecond',add_zero]; exact dirichletPrime_character_orthogonality P ltq hu b

private theorem dirichletPrime_negative_mean {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {v H : ℝ} (hv : 0 ≤ v) (hmean : ∑ i ∈ s, f i = 0)
    (hsq : 2*∑ i ∈ s, (f i)^2 = H*v^2) (hfour : ∑ i ∈ s, (f i)^4 ≤ 2*H*v^4) :
    H*v ≤ 8*∑ i ∈ s, max (-f i) 0 := by
  have habs : ∑ i ∈ s, |f i| = 2*∑ i ∈ s, max (-f i) 0 := by
    calc _ = ∑ i ∈ s, (2*max (-f i) 0 + f i) := by
             apply sum_congr rfl
             intro i _
             rcases le_total 0 (f i) with h | h
             · rw [abs_of_nonneg h,max_eq_right (neg_nonpos.mpr h)]; ring
             · rw [abs_of_nonpos h,max_eq_left (neg_nonneg.mpr h)]; ring
         _ = _ := by rw [sum_add_distrib,← mul_sum,hmean,add_zero]
  by_cases zero : v = 0
  · rw [zero,mul_zero]
    exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ ↦ le_max_right ..)
  have key : 12*v^2*(∑ i ∈ s, (f i)^2) ≤
      16*v^3*(∑ i ∈ s, |f i|) + ∑ i ∈ s, (f i)^4 := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro i _
    have h := mul_nonneg (mul_nonneg (abs_nonneg (f i)) (sq_nonneg (|f i|-2*v)))
      (add_nonneg (abs_nonneg (f i)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hv))
    have h₂ := sq_abs (f i)
    have h₄ : |f i|^4 = (f i)^4 := by rw [show (4:ℕ) = 2*2 by decide, pow_mul, pow_mul, h₂]
    nlinarith only [h,h₄,congrArg (fun t : ℝ ↦ t*v^2) h₂]
  rw [habs] at key
  apply (mul_le_mul_iff_left₀ (pow_pos (lt_of_le_of_ne hv (Ne.symm zero)) 3)).mp
  nlinarith only [key,hfour,congrArg (fun t : ℝ ↦ t*v^2) hsq]

private theorem dirichletPrime_deficit_row {q : ℕ} [Fact q.Prime] (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, ∀ r ∈ P, p*r < q) (b : ℕ → ℂ) :
    let Z (χ : DirichletCharacter ℂ q) := ∑ p ∈ P, b p*χ (p : ZMod q)
    let v := Real.sqrt (∑ p ∈ P, ‖b p‖^2)
    q.totient*v ≤ 8*∑ χ, max (-(Z χ).re) 0 ∧
      (∑ χ, (max (-(Z χ).re) 0)^2) ≤ (q.totient:ℝ)/2*v^2 := by
  intro Z v
  obtain ⟨hc,he⟩ := dirichletPrime_real_moments P hp hsize b
  have hv : v^2 = ∑ p ∈ P, ‖b p‖^2 := Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)
  change 2*∑ χ, (Z χ).re^2 = _ at he
  rw [← hv] at he
  constructor
  · apply dirichletPrime_negative_mean univ (fun χ ↦ (Z χ).re) (Real.sqrt_nonneg _) hc he
    calc (∑ χ, (Z χ).re^4) ≤ ∑ χ, ‖Z χ‖^4 := by
           apply sum_le_sum
           intro χ _
           simpa only [show (4:ℕ) = 2*2 by decide,pow_mul,sq_abs] using
             (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (Z χ)) 4)
         _ ≤ _ := by rw [show v^4 = (v^2)^2 by ring,hv]; exact dirichletPrime_fourthMoment P hp hsize b
  · calc _ ≤ ∑ χ, (Z χ).re^2 := by
           apply sum_le_sum
           intro χ _
           rcases le_total ((Z χ).re) 0 with h | h
           · rw [max_eq_left (neg_nonneg.mpr h),neg_sq]
           · rw [max_eq_right (neg_nonpos.mpr h),zero_pow (by decide : (2:ℕ) ≠ 0)]; exact sq_nonneg _
         _ = _ := by linarith

private theorem dirichletPrime_deficit_sum_sq {α ι : Type*} (A : Finset α) (I : Finset ι)
    (f : ι → α → ℝ) (v : ι → ℝ) {K : ℝ} (hK : 0 ≤ K) (hv : ∀ j ∈ I, 0 ≤ v j)
    (hrow : ∀ j ∈ I, ∑ χ ∈ A, (f j χ)^2 ≤ K*(v j)^2) :
    (∑ χ ∈ A, (∑ j ∈ I, f j χ)^2) ≤ K*(∑ j ∈ I, v j)^2 := by
  have pair (j : ι) (hj : j ∈ I) (k : ι) (hk : k ∈ I) :
      (∑ χ ∈ A, f j χ*f k χ) ≤ K*v j*v k := by
    apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg hK (hv j hj)) (hv k hk))
    calc _ ≤ _ := sum_mul_sq_le_sq_mul_sq A (f j) (f k)
         _ ≤ (K*(v j)^2)*(K*(v k)^2) := mul_le_mul (hrow j hj) (hrow k hk)
           (sum_nonneg fun _ _ ↦ sq_nonneg _) (mul_nonneg hK (sq_nonneg _))
         _ = _ := by ring
  simp only [pow_two,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro j hj
  rw [sum_comm]
  apply sum_le_sum
  intro k hk
  simpa only [mul_assoc] using pair k hk j hj

private theorem dirichletPrime_band_card {α : Type*} (A : Finset α) (d : α → ℝ)
    {S : ℝ} (hS : 0 < S) (hl : A.card*S ≤ 8*∑ χ ∈ A, d χ)
    (hu : ∑ χ ∈ A, (d χ)^2 ≤ (A.card:ℝ)/2*S^2) :
    A.card ≤ 128*(A.filter (fun χ ↦ S/16 ≤ d χ ∧ d χ ≤ 16*S)).card := by
  classical
  let G := A.filter fun χ ↦ S/16 ≤ d χ ∧ d χ ≤ 16*S
  have pt (χ : α) (hχ : χ ∈ A) :
      16*S*d χ ≤ S^2 + (d χ)^2 + (if χ ∈ G then 64*S^2 else 0) := by
    by_cases g : χ ∈ G
    · simp only [g, ↓reduceIte]; nlinarith [sq_nonneg (d χ-8*S),sq_nonneg S]
    · simp only [g, ↓reduceIte]
      have h : ¬ (S/16 ≤ d χ ∧ d χ ≤ 16*S) := fun z ↦ g (mem_filter.mpr ⟨hχ,z⟩)
      by_cases l : S/16 ≤ d χ
      · have u : 16*S < d χ := lt_of_not_ge (fun t ↦ h ⟨l,t⟩)
        nlinarith [mul_nonneg (sub_nonneg.mpr u.le) (lt_trans (by positivity : 0 < 16*S) u).le,
          sq_nonneg S]
      · have l' := lt_of_not_ge l
        nlinarith [mul_nonneg hS.le (sub_nonneg.mpr l'.le),sq_nonneg (d χ)]
  have hs := sum_le_sum pt
  have sub : A.filter (fun χ ↦ χ ∈ G) = G := filter_mem_eq_inter.trans
    (inter_eq_right.mpr (filter_subset ..))
  simp only [← mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,← sum_filter,sub] at hs
  suffices h : (A.card:ℝ)*S^2 ≤ (128*(G.card:ℝ))*S^2 by
    exact_mod_cast (le_of_mul_le_mul_right h (sq_pos_of_pos hS))
  nlinarith only [hs,hu,mul_le_mul_of_nonneg_right hl hS.le]

/-- A positive fraction of characters have a signed deficit comparable to the sum of
the row standard deviations for any collection of prime samples below the semiprime
threshold. Rows can overlap arbitrarily. -/
theorem dirichletPrime_signed_deficit_band {q : ℕ} [Fact q.Prime] (I : Finset ℕ)
    (P : ℕ → Finset ℕ) (b : ℕ → ℕ → ℂ) (hp : ∀ j ∈ I, ∀ p ∈ P j, p.Prime)
    (hsize : ∀ j ∈ I, ∀ p ∈ P j, ∀ r ∈ P j, p*r < q) :
    let S := ∑ j ∈ I, Real.sqrt (∑ p ∈ P j, ‖b j p‖^2)
    let D (χ : DirichletCharacter ℂ q) :=
      ∑ j ∈ I, max (-(∑ p ∈ P j, b j p*χ (p : ZMod q)).re) 0
    0 < S → q.totient ≤ 128*(univ.filter fun χ ↦ S/16 ≤ D χ ∧ D χ ≤ 16*S).card := by
  classical
  intro S D hS
  let v (j : ℕ) := Real.sqrt (∑ p ∈ P j, ‖b j p‖^2)
  let f (j : ℕ) (χ : DirichletCharacter ℂ q) :=
    max (-(∑ p ∈ P j, b j p*χ (p : ZMod q)).re) 0
  have hcard : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [card_univ, ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have row (j : ℕ) (hj : j ∈ I) :
      q.totient*v j ≤ 8*∑ χ, f j χ ∧ ∑ χ, (f j χ)^2 ≤ (q.totient:ℝ)/2*(v j)^2 :=
    dirichletPrime_deficit_row (P j) (hp j hj) (hsize j hj) (b j)
  rw [← hcard]
  apply dirichletPrime_band_card univ D hS
  · rw [hcard]
    calc _ = ∑ j ∈ I, q.totient*v j := mul_sum ..
         _ ≤ ∑ j ∈ I, 8*∑ χ, f j χ := sum_le_sum fun j hj ↦ (row j hj).1
         _ = _ := by rw [← mul_sum,sum_comm]
  · rw [hcard]
    exact dirichletPrime_deficit_sum_sq univ I f v (by positivity)
      (fun _ _ ↦ Real.sqrt_nonneg _) fun j hj ↦ (row j hj).2

/-- Sum of the square roots of the prime energies at fourth-power cutoffs. -/
def dirichletPrimeFourthPowerScale (J : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 J, Real.sqrt (∑ p ∈ Nat.primesLE (j^4),
    (((j:ℝ)^4-p)*Real.log p)^2)

/-- The full signed deficit for the ordinary first-prime Riesz sums at fourth powers. -/
def dirichletPrimeFourthPowerDeficit {q : ℕ} (χ : DirichletCharacter ℂ q) (J : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 J, max (-(dirichletPrimeRiesz χ (fun p ↦ Real.log p) (j^4)).re) 0

open Filter Topology in
private theorem dirichletPrime_dyadic_log_mass :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)/2 ≤ ∑ p ∈ Nat.primesLE (2*n) \ Nat.primesLE n, Real.log p := by
  have ht := Chebyshev.tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo : ∀ᶠ n : ℕ in atTop, (7/8:ℝ) < Chebyshev.theta n/n :=
    ht.eventually (lt_mem_nhds (by norm_num))
  have hhi : ∀ᶠ n : ℕ in atTop, Chebyshev.theta n/n < (9/8:ℝ) :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlo
  filter_upwards [eventually_ge_atTop (max N 1),hhi] with n hn hhi
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h := hN (2*n) (by omega)
  push_cast at h
  have hl := (lt_div_iff₀ (by positivity)).mp h
  have hu := (div_lt_iff₀ hn').mp hhi
  have he : (∑ p ∈ Nat.primesLE (2*n) \ Nat.primesLE n, Real.log p) + Chebyshev.theta n =
      Chebyshev.theta (2*(n:ℝ)) := by
    rw [← Nat.cast_ofNat (n := 2) (R := ℝ),← Nat.cast_mul]
    rw [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]
    exact sum_sdiff (Nat.primesLE_mono (by omega))
  linarith

private theorem dirichletPrime_scale_lower_row {L j : ℕ} (hL : 1 ≤ L) (hj : 2*L ≤ j)
    (hmass : ((L^4:ℕ):ℝ)/2 ≤
      ∑ p ∈ Nat.primesLE (2*L^4) \ Nat.primesLE (L^4), Real.log p) :
    (L:ℝ)^6*Real.sqrt (Real.log L)/2 ≤ Real.sqrt
      (∑ p ∈ Nat.primesLE (j^4), (((j:ℝ)^4-p)*Real.log p)^2) := by
  let U := Nat.primesLE (2*L^4) \ Nat.primesLE (L^4)
  have hpow := Nat.pow_le_pow_left hj 4
  rw [mul_pow] at hpow
  norm_num at hpow
  have sub : U ⊆ Nat.primesLE (j^4) :=
    fun p hp ↦ Nat.primesLE_mono (by omega : 2*L^4 ≤ j^4) (mem_sdiff.mp hp).1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have ht (p : ℕ) (hp : p ∈ U) :
      (L:ℝ)^8*Real.log L*Real.log p ≤ (((j:ℝ)^4-p)*Real.log p)^2 := by
    obtain ⟨h₂,hn⟩ := mem_sdiff.mp hp
    obtain ⟨h₂,hp'⟩ := Nat.mem_primesLE.mp h₂
    have h₁ : L^4 < p := lt_of_not_ge fun h ↦ hn (Nat.mem_primesLE.mpr ⟨h,hp'⟩)
    have hLp : L ≤ p := (le_self_pow₀ hL (by decide : (4:ℕ) ≠ 0)).trans h₁.le
    have hpLog : Real.log L ≤ Real.log p := Real.log_le_log (by exact_mod_cast (show 0 < L by omega)) (by exact_mod_cast hLp)
    have hgap : (L:ℝ)^4 ≤ (j:ℝ)^4-p := by
      have hn : L^4+p ≤ j^4 := by omega
      exact le_sub_iff_add_le.mpr (by exact_mod_cast hn)
    have z := mul_le_mul (pow_le_pow_left₀ (by positivity) hgap 2)
      (mul_le_mul_of_nonneg_right hpLog (hlog.trans hpLog)) (mul_nonneg hlog (hlog.trans hpLog))
      (sq_nonneg _)
    convert z using 1 <;> ring
  change ((L^4:ℕ):ℝ)/2 ≤ ∑ p ∈ U, Real.log p at hmass
  push_cast at hmass
  apply Real.le_sqrt_of_sq_le
  calc _ ≤ (L:ℝ)^8*Real.log L*((L:ℝ)^4/2) := by
           rw [div_pow,mul_pow,Real.sq_sqrt hlog]
           nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) L) 12) hlog]
       _ ≤ (L:ℝ)^8*Real.log L*(∑ p ∈ U, Real.log p) :=
           mul_le_mul_of_nonneg_left hmass (mul_nonneg (by positivity) hlog)
       _ = _ := mul_sum ..
       _ ≤ ∑ p ∈ U, (((j:ℝ)^4-p)*Real.log p)^2 := sum_le_sum ht
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ ↦ sq_nonneg _)

private theorem dirichletPrime_scale_upper_row {j J : ℕ} (hJ : 1 ≤ J) (hj : j ≤ J) :
    Real.sqrt (∑ p ∈ Nat.primesLE (j^4), (((j:ℝ)^4-p)*Real.log p)^2) ≤
      4*(J:ℝ)^6*Real.sqrt (Real.log J) := by
  have hlog := Real.log_nonneg (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  have hlog4 : Real.log 4 ≤ 4 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hjJ := Nat.pow_le_pow_left hj 4
  have hjJ' : (j:ℝ)^4 ≤ (J:ℝ)^4 := by exact_mod_cast hjJ
  have hcoef (p : ℕ) (hp : p ∈ Nat.primesLE (j^4)) :
      (((j:ℝ)^4-p)*Real.log p)^2 ≤ ((J:ℝ)^8*(4*Real.log J))*Real.log p := by
    obtain ⟨hpj,hprime⟩ := Nat.mem_primesLE.mp hp
    have h₀ := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le : (1:ℝ) ≤ p)
    have h₁ : Real.log p ≤ 4*Real.log J := by
      simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log
        (by exact_mod_cast hprime.pos : 0 < (p:ℝ))
        (by exact_mod_cast hpj.trans hjJ : (p:ℝ) ≤ (J:ℝ)^4)
    have hgap : 0 ≤ (j:ℝ)^4-p := sub_nonneg.mpr (by exact_mod_cast hpj)
    have hgap' : (j:ℝ)^4-p ≤ (J:ℝ)^4 := by linarith [Nat.cast_nonneg (α := ℝ) p]
    have z := mul_le_mul (pow_le_pow_left₀ hgap hgap' 2)
      (mul_le_mul_of_nonneg_right h₁ h₀) (mul_nonneg h₀ h₀) (sq_nonneg _)
    convert z using 1 <;> ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc _ ≤ ∑ p ∈ Nat.primesLE (j^4), ((J:ℝ)^8*(4*Real.log J))*Real.log p := sum_le_sum hcoef
       _ = ((J:ℝ)^8*(4*Real.log J))*Chebyshev.theta (j^4:ℕ) := by
           rw [← mul_sum,Chebyshev.theta_eq_sum_primesLE_log]
       _ ≤ ((J:ℝ)^8*(4*Real.log J))*(4*(J:ℝ)^4) := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           calc _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
                _ ≤ _ := by push_cast; gcongr
       _ = _ := by rw [mul_pow,Real.sq_sqrt hlog]; ring

open Filter in
/-- The fourth-power prime scale is bounded above and below by absolute multiples
of J⁷√(log J), uniformly for all sufficiently large integer cutoffs. -/
theorem dirichletPrimeFourthPowerScale_bounds :
    ∀ᶠ J : ℕ in atTop,
      (J:ℝ)^7*Real.sqrt (Real.log J)/(2*5^7) ≤ dirichletPrimeFourthPowerScale J ∧
      dirichletPrimeFourthPowerScale J ≤ 4*(J:ℝ)^7*Real.sqrt (Real.log J) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp dirichletPrime_dyadic_log_mass
  filter_upwards [eventually_ge_atTop (4*(max N 5))] with J hJ
  let L := J/4
  have hL : 5 ≤ L := by dsimp [L]; omega
  have hL' : 1 ≤ L := by omega
  have hJL : 4*L ≤ J := by dsimp [L]; omega
  have hJL' : J ≤ 5*L := by dsimp [L] at *; omega
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL')
  have hmass := hN (L^4) (le_trans (by dsimp [L]; omega : N ≤ L)
    (le_self_pow₀ hL' (by decide : (4:ℕ) ≠ 0)))
  have hsmall : (L:ℝ)^7*Real.sqrt (Real.log L) ≤ dirichletPrimeFourthPowerScale J := by
    calc _ = ∑ _j ∈ Ioc (2*L) (4*L), (L:ℝ)^6*Real.sqrt (Real.log L)/2 := by
             simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul]
             rw [show 4*L-2*L = 2*L by omega]; push_cast; ring
         _ ≤ ∑ j ∈ Ioc (2*L) (4*L), Real.sqrt (∑ p ∈ Nat.primesLE (j^4),
               (((j:ℝ)^4-p)*Real.log p)^2) := sum_le_sum fun j hj ↦
             dirichletPrime_scale_lower_row hL' (mem_Ioc.mp hj).1.le hmass
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg
             (fun j hj ↦ mem_Icc.mpr ⟨by have := (mem_Ioc.mp hj).1; omega,
               (mem_Ioc.mp hj).2.trans hJL⟩) (fun _ _ _ ↦ Real.sqrt_nonneg _)
  have hp : (J:ℝ)^7 ≤ 5^7*(L:ℝ)^7 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hJL') _
  have hJLsq : (J:ℝ) ≤ (L:ℝ)^2 := by
    have aux : (5:ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [show (J:ℝ) ≤ 5*L by exact_mod_cast hJL',
      mul_nonneg (sub_nonneg.mpr aux) (Nat.cast_nonneg (α := ℝ) L)]
  have hjlog : Real.log J ≤ 2*Real.log L := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log
      (by exact_mod_cast (show 0 < J by omega)) hJLsq
  have hroot : Real.sqrt (Real.log J) ≤ 2*Real.sqrt (Real.log L) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow,Real.sq_sqrt hlog]
    linarith
  constructor
  · apply le_trans _ hsmall
    apply (div_le_iff₀ (by norm_num)).mpr
    calc _ ≤ (5^7*(L:ℝ)^7)*(2*Real.sqrt (Real.log L)) :=
           mul_le_mul hp hroot (Real.sqrt_nonneg _) (by positivity)
         _ = _ := by ring
  · calc _ ≤ ∑ _j ∈ Icc 1 J, 4*(J:ℝ)^6*Real.sqrt (Real.log J) :=
             sum_le_sum fun j hj ↦ dirichletPrime_scale_upper_row (by omega) (mem_Icc.mp hj).2
         _ = _ := by
             simp only [sum_const,Nat.card_Icc,nsmul_eq_mul]
             rw [show J+1-1 = J by omega]; ring

private theorem dirichletPrime_principal_deficit (q J : ℕ) [Fact q.Prime] :
    dirichletPrimeFourthPowerDeficit (1 : DirichletCharacter ℂ q) J = 0 := by
  apply sum_eq_zero
  intro j _
  apply max_eq_right
  apply neg_nonpos.mpr
  rw [dirichletPrimeRiesz,Complex.re_sum]
  apply sum_nonneg
  intro p hp
  have hp' := Nat.mem_primesLE.mp hp
  have hl := Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le : (1:ℝ) ≤ p)
  by_cases hu : IsUnit (p : ZMod q)
  · rw [MulChar.one_apply hu,mul_one]
    simp only [Complex.sub_re,Complex.natCast_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hp'.1)) hl
  · rw [MulChar.map_nonunit _ hu]; simp

open Filter Classical in
/-- At every sufficiently large cutoff J and every prime modulus above J⁸, at least
one character in 128 is nonprincipal and has its full signed deficit at J between
absolute multiples of J⁷√(log J). -/
theorem dirichletPrimeFourthPowerDeficit_positive_proportion :
    ∀ᶠ J : ℕ in atTop, ∀ (q : ℕ) [Fact q.Prime], J^8 < q →
      q.totient ≤ 128*(univ.filter fun χ : DirichletCharacter ℂ q ↦ χ ≠ 1 ∧
        (J:ℝ)^7*Real.sqrt (Real.log J)/(32*5^7) ≤ dirichletPrimeFourthPowerDeficit χ J ∧
        dirichletPrimeFourthPowerDeficit χ J ≤ 64*(J:ℝ)^7*Real.sqrt (Real.log J)).card := by
  classical
  filter_upwards [dirichletPrimeFourthPowerScale_bounds,eventually_ge_atTop 2] with J hscale hJ
  intro q hq hsize
  let P (j : ℕ) := Nat.primesLE (j^4)
  let b (j p : ℕ) : ℂ := ((((j:ℝ)^4-p)*Real.log p : ℝ) : ℂ)
  have hr (χ : DirichletCharacter ℂ q) (j : ℕ) :
      (∑ p ∈ P j, b j p*χ (p : ZMod q)) = dirichletPrimeRiesz χ (fun p ↦ Real.log p) (j^4) := by
    apply sum_congr rfl
    intro p _
    dsimp [b]
    push_cast
    ring
  have h := dirichletPrime_signed_deficit_band (q := q) (Icc 1 J) P b
    (fun j _ p hp ↦ (Nat.mem_primesLE.mp hp).2) (fun j hj p hp r hr ↦ by
      have he := Nat.pow_le_pow_left (mem_Icc.mp hj).2 4
      have z := Nat.mul_le_mul ((Nat.mem_primesLE.mp hp).1.trans he) ((Nat.mem_primesLE.mp hr).1.trans he)
      exact (z.trans_eq (by ring)).trans_lt hsize)
  simp only [b,Complex.norm_real,Real.norm_eq_abs,sq_abs] at h
  -- Keep the complex sums folded to use the Riesz identity.
  have h' : 0 < dirichletPrimeFourthPowerScale J →
      q.totient ≤ 128*(univ.filter fun χ : DirichletCharacter ℂ q ↦
        dirichletPrimeFourthPowerScale J/16 ≤ dirichletPrimeFourthPowerDeficit χ J ∧
        dirichletPrimeFourthPowerDeficit χ J ≤ 16*dirichletPrimeFourthPowerScale J).card := by
    simpa only [dirichletPrimeFourthPowerScale,dirichletPrimeFourthPowerDeficit,P,← hr,b,
      Complex.norm_real,Real.norm_eq_abs,sq_abs] using h
  have hg : 0 < (J:ℝ)^7*Real.sqrt (Real.log J) := by
    have := Real.log_pos (by exact_mod_cast (show 1 < J by omega) : (1:ℝ)<J)
    positivity
  have hS : 0 < dirichletPrimeFourthPowerScale J :=
    lt_of_lt_of_le (div_pos hg (by norm_num)) hscale.1
  refine (h' hS).trans (Nat.mul_le_mul_left _ (card_le_card ?_))
  intro χ hχ
  obtain ⟨_,hl,hu⟩ := mem_filter.mp hχ
  refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩
  · rintro rfl
    rw [dirichletPrime_principal_deficit] at hl
    linarith
  · linarith [hscale.1]
  · linarith [hscale.2]

end RiemannMasullo
