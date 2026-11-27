module

public import RiemannMasullo.Ch13_ZerosHecke.GaussianIdealNormFibers

/-!
# Gaussian norms at the ramified and inert primes

Multiplication by `1 + i` identifies successive norm fibers above two. For a prime
congruent to three modulo four, multiplication by the rational prime increases the
exponent by two, and the fiber at exponent one is empty.
-/

public section

namespace RiemannMasullo

private theorem gaussianNormFiber_card_of_common_divisor {a : GaussianInt} {m n : ℕ}
    (ha : a ≠ 0) (hn : a.norm.natAbs * m = n)
    (hdiv : ∀ z : GaussianInt, z.norm.natAbs = n → a ∣ z) :
    Nat.card {z : GaussianInt // z.norm.natAbs = n} =
      Nat.card {z : GaussianInt // z.norm.natAbs = m} := by
  let f (z : {z : GaussianInt // z.norm.natAbs = m}) : {z : GaussianInt // z.norm.natAbs = n} :=
    ⟨a * z.val, by rw [Zsqrtd.norm_mul, Int.natAbs_mul, z.property, hn]⟩
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · exact fun x y h ↦ Subtype.ext <| mul_left_cancel₀ ha (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := hdiv z hz
    have hpos : 0 < a.norm.natAbs := Int.natAbs_pos.mpr (mt GaussianInt.norm_eq_zero.mp ha)
    refine ⟨⟨w, Nat.eq_of_mul_eq_mul_left hpos ?_⟩, rfl⟩
    rwa [← Int.natAbs_mul, ← Zsqrtd.norm_mul, hn]

private theorem gaussian_dvd_of_norm_dvd {a z : GaussianInt} {n : ℕ}
    (ha : Prime a) (hstar : a ∣ star a) (hn : a ∣ (n : GaussianInt))
    (hz : n ∣ z.norm.natAbs) : a ∣ z := by
  have hprod : (n : GaussianInt) ∣ z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj, ← GaussianInt.natCast_natAbs_norm (α := GaussianInt)]
    exact map_dvd (Nat.castRingHom GaussianInt) hz
  rcases ha.dvd_mul.mp (hn.trans hprod) with h | h
  · exact h
  · apply hstar.trans
    simpa only [starRingEnd_apply, star_star] using map_dvd (starRingEnd GaussianInt) h

/-- Every power of two has four ordered, signed Gaussian representations. -/
theorem gaussianNormFiber_card_prime_pow_two (k : ℕ) :
    Nat.card {z : GaussianInt // z.norm.natAbs = 2 ^ k} = 4 := by
  let a : GaussianInt := ⟨1, 1⟩
  have hnorm : a.norm.natAbs = 2 := rfl
  have ha : Prime a := Ideal.prime_of_irreducible_absNorm_span (by
    rw [GaussianInt.absNorm_span, hnorm]
    exact Nat.prime_two.prime.irreducible)
  have hstar : a ∣ star a := ⟨(⟨0, -1⟩ : GaussianInt), rfl⟩
  have htwo : a ∣ (2 : GaussianInt) := ⟨star a, rfl⟩
  induction k with
  | zero => simpa using gaussianNormFiber_one_card
  | succ k ih =>
    refine (gaussianNormFiber_card_of_common_divisor ha.ne_zero
      (by rw [hnorm, pow_succ, mul_comm]) ?_).trans ih
    intro z hz
    apply gaussian_dvd_of_norm_dvd (n := 2) ha hstar htwo
    rw [hz]
    exact dvd_pow_self _ (Nat.succ_ne_zero k)

/-- For an inert rational prime, the Gaussian norm fiber is a unit orbit at even exponents
and empty at odd exponents. -/
theorem gaussianNormFiber_card_prime_pow_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (hp3 : p % 4 = 3) (k : ℕ) :
    Nat.card {z : GaussianInt // z.norm.natAbs = p ^ k} = if Even k then 4 else 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have ha := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp3
  have hnorm : (p : GaussianInt).norm.natAbs = p ^ 2 := by
    rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, pow_two]
  have hdiv (z : GaussianInt) (h : p ∣ z.norm.natAbs) : (p : GaussianInt) ∣ z :=
    gaussian_dvd_of_norm_dvd ha (by simp) (dvd_refl _) h
  induction k using Nat.twoStepInduction with
  | zero => simpa using gaussianNormFiber_one_card
  | one =>
    have : IsEmpty {z : GaussianInt // z.norm.natAbs = p} := ⟨fun z ↦ by
      obtain ⟨w, hw⟩ := hdiv z.val (by rw [z.property])
      have hsq : p ^ 2 ∣ p := ⟨w.norm.natAbs, by
        calc p = z.val.norm.natAbs := z.property.symm
             _ = p ^ 2 * w.norm.natAbs := by rw [hw, Zsqrtd.norm_mul, Int.natAbs_mul, hnorm]⟩
      exact (not_lt_of_ge (Nat.le_of_dvd hp.pos hsq)) (by nlinarith [hp.one_lt])⟩
    simp
  | more k hk _ =>
    have hcard := gaussianNormFiber_card_of_common_divisor ha.ne_zero
      (m := p ^ k) (n := p ^ (k + 2)) (by rw [hnorm, pow_add, mul_comm]) (fun z hz ↦
        hdiv z (by rw [hz]; exact dvd_pow_self p (by omega)))
    simpa [Nat.even_add] using hcard.trans hk

end RiemannMasullo
