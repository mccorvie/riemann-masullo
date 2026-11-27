module

public import RiemannMasullo.Ch13_ZerosHecke.GaussianIdealNormFibers
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Gaussian integers of prime-power norm

A split prime gives two conjugate divisors of prime norm. Among elements of norm
`p ^ k`, the elements indivisible by one of these divisors form a single orbit
of the four units under multiplication by the other divisor.
-/

public section

namespace RiemannMasullo

private abbrev NormFib (n : ℕ) := {z : GaussianInt // z.norm.natAbs = n}

private theorem gaussianNorm_mul (a b : GaussianInt) :
    (a * b).norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

private theorem gaussianNorm_pos {a : GaussianInt} (ha : a ≠ 0) :
    0 < a.norm.natAbs :=
  Int.natAbs_pos.mpr (mt GaussianInt.norm_eq_zero.mp ha)

private theorem card_mul_part (a : GaussianInt) (ha : a ≠ 0) {m n : ℕ}
    (hmn : a.norm.natAbs * m = n) (P Q : GaussianInt → Prop)
    (hmap : ∀ x, Q (a * x) ↔ P x) (hdiv : ∀ z : NormFib n, Q z.1 → a ∣ z.1) :
    Nat.card {z : NormFib n // Q z.1} = Nat.card {z : NormFib m // P z.1} := by
  let f (x : {z : NormFib m // P z.1}) : {z : NormFib n // Q z.1} :=
    ⟨⟨a * x.1.1, by rw [gaussianNorm_mul, x.1.2, hmn]⟩, (hmap _).2 x.2⟩
  apply (Nat.card_congr (Equiv.ofBijective f ?_)).symm
  constructor
  · intro x y h
    exact Subtype.ext <| Subtype.ext <| mul_left_cancel₀ ha <|
      congrArg (fun t : {z : NormFib n // Q z.1} ↦ t.1.1) h
  · rintro ⟨⟨z, hz⟩, hQ⟩
    obtain ⟨x, rfl⟩ := hdiv ⟨z, hz⟩ hQ
    have hx : x.norm.natAbs = m := Nat.eq_of_mul_eq_mul_left (gaussianNorm_pos ha)
      (by rwa [← gaussianNorm_mul, hmn])
    exact ⟨⟨⟨x, hx⟩, (hmap x).1 hQ⟩, rfl⟩

private theorem gaussianPrime_of_norm_prime {a : GaussianInt} (ha : a.norm.natAbs.Prime) :
    Prime a := by
  apply irreducible_iff_prime.mp
  refine ⟨fun h ↦ ha.ne_one (Zsqrtd.norm_eq_one_iff.mpr h), ?_⟩
  intro b c hbc
  have h := ha.prime.irreducible.isUnit_or_isUnit (a := b.norm.natAbs) (b := c.norm.natAbs)
    (by rw [hbc, gaussianNorm_mul])
  simpa only [← Zsqrtd.norm_eq_one_iff, Nat.isUnit_iff] using h

private theorem cast_norm_dvd {n : ℕ} {z : GaussianInt} (h : n ∣ z.norm.natAbs) :
    (n : GaussianInt) ∣ z * star z := by
  rw [← Zsqrtd.norm_eq_mul_conj, ← GaussianInt.natCast_natAbs_norm (α := GaussianInt)]
  exact map_dvd (Nat.castRingHom GaussianInt) h

private theorem star_dvd_from_dvd_star {a z : GaussianInt} (h : a ∣ star z) :
    star a ∣ z := by
  simpa only [starRingEnd_apply, star_star] using map_dvd (starRingEnd GaussianInt) h

private theorem dvd_or_star_dvd {p : ℕ} {a z : GaussianInt} (ha : Prime a)
    (hn : a.norm.natAbs = p) (h : p ∣ z.norm.natAbs) : a ∣ z ∨ star a ∣ z := by
  have hcast : (p : GaussianInt) = a * star a := by
    rw [← hn, GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
  have hdiv := cast_norm_dvd h
  rw [hcast] at hdiv
  exact (ha.dvd_mul.mp ((dvd_mul_right a _).trans hdiv)).imp_right star_dvd_from_dvd_star


private theorem split_prime_exists {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ a : GaussianInt, a.norm.natAbs = p ∧ ¬ a ∣ star a := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  obtain ⟨x, y, hx, hxy⟩ : ∃ x y : ℕ, 0 < x ∧ x ^ 2 + y ^ 2 = p := by
    by_cases hu : u = 0
    · exact ⟨v, u, by subst u; by_contra! hv; simp [Nat.eq_zero_of_le_zero hv] at huv; omega,
        by rwa [add_comm]⟩
    · exact ⟨u, v, Nat.pos_of_ne_zero hu, huv⟩
  let a : GaussianInt := ⟨x, y⟩
  have hn : a.norm.natAbs = p := by simpa [a, GaussianInt.natAbs_norm_eq, sq] using hxy
  refine ⟨a, hn, ?_⟩
  intro hdiv
  have hsum : a + star a = ((2 * x : ℕ) : GaussianInt) := by
    ext <;> simp [a]
    ring
  have hac : a ∣ ((2 * x : ℕ) : GaussianInt) := hsum ▸ dvd_add (dvd_refl a) hdiv
  obtain ⟨c, hc⟩ := hac
  have hsq : p ∣ (2 * x) ^ 2 := ⟨c.norm.natAbs, by
    have hn' := congrArg (fun z : GaussianInt ↦ z.norm.natAbs) hc
    change (((2 * x : ℕ) : GaussianInt).norm.natAbs) = (a * c).norm.natAbs at hn'
    simpa only [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, gaussianNorm_mul,
      hn, sq] using hn'⟩
  have hnd : ¬p ∣ 2 := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd
    omega
  have hpx := (hp.dvd_mul.mp (hp.dvd_of_dvd_pow hsq)).resolve_left hnd
  have hle := Nat.le_of_dvd hx hpx
  have hp2 := hp.one_lt
  nlinarith [Nat.mul_self_le_mul_self hle]

/-- For a split rational prime, exactly four times `k + 1` Gaussian integers have norm `p ^ k`.
The count distinguishes both coordinate order and sign. -/
theorem gaussianNormFiber_card_prime_pow_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h1 : p % 4 = 1) (k : ℕ) :
    Nat.card {z : GaussianInt // z.norm.natAbs = p ^ k} = 4 * (k + 1) := by
  classical
  obtain ⟨a, hn, has⟩ := split_prime_exists hp h1
  have ha : Prime a := gaussianPrime_of_norm_prime (hn ▸ hp)
  have hs : (star a).norm.natAbs = p := by rw [Zsqrtd.norm_conj, hn]
  have hsn : star a ≠ 0 := by simpa using ha.ne_zero
  let rest (i : ℕ) := Nat.card {z : NormFib (p ^ i) // ¬a ∣ z.1}
  have hn_mul (i : ℕ) : a.norm.natAbs * p ^ i = p ^ (i + 1) := by
    rw [hn, pow_succ, mul_comm]
  have hrest (i : ℕ) : rest i = 4 := by
    induction i with
    | zero =>
      change Nat.card {z : NormFib (p ^ 0) // ¬ a ∣ z.1} = 4
      rw [pow_zero]
      apply Eq.trans _ gaussianNormFiber_one_card
      apply Nat.card_congr (Equiv.subtypeUnivEquiv _)
      intro z hz
      exact ha.not_isUnit (isUnit_of_dvd_unit hz (Zsqrtd.norm_eq_one_iff.mp z.2))
    | succ i ih =>
      apply Eq.trans _ ih
      apply card_mul_part (star a) hsn (m := p ^ i) (n := p ^ (i + 1))
        (by rw [hs, pow_succ, mul_comm]) (fun z ↦ ¬a ∣ z) (fun z ↦ ¬a ∣ z)
      · intro x
        simp [ha.dvd_mul, has]
      · intro z hz
        have hz' : p ∣ z.1.norm.natAbs := by
          rw [z.2]
          exact dvd_pow_self p (by omega)
        exact (dvd_or_star_dvd ha hn hz').resolve_left hz
  induction k with
  | zero => simpa using gaussianNormFiber_one_card
  | succ k ih =>
    have hpart := card_mul_part a ha.ne_zero (hn_mul k) (fun _ ↦ True) (fun z ↦ a ∣ z)
      (fun _ ↦ iff_true_intro (dvd_mul_right ..)) (fun _ h ↦ h)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ : NormFib (p ^ k) ↦ trivial))] at hpart
    let _ := gaussianNormFiber_finite (p ^ (k + 1))
    have hc := Nat.card_congr (Equiv.sumCompl (fun z : NormFib (p ^ (k + 1)) ↦ a ∣ z.1)).symm
    rw [Nat.card_sum, hpart, ih] at hc
    change _ = _ + rest (k + 1) at hc
    rw [hrest] at hc
    omega

end RiemannMasullo
