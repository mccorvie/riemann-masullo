module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Prime Riesz sums over a family of Dirichlet characters

For Theorem 12.5.1.1, pp. 519–520, bound the actual first-prime Riesz sums of
characters of prime modulus over all integral cutoffs up to that modulus.
Orthogonality controls each prime prefix. A summable logarithmic weight gives
one exceptional set for every cutoff and every fourth-power prefix.
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

end RiemannMasullo
