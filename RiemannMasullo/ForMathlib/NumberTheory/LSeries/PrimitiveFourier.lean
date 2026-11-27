module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-! # Fourier coefficients of primitive Dirichlet Euler factors on one angular residue -/

@[expose] public noncomputable section

open DirichletCharacter
open scoped BigOperators ComplexConjugate

namespace RiemannMasullo.RationalConductor

/-- Finite Fourier coefficient at the unit residue `r`, with the volume of the
one-residue cylinder as its normalization. -/
def cylinderAverage (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) :
    (DirichletCharacter ℂ q → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∑ χ, conj (χ (r : ZMod q)) * f χ) / q.totient
  map_add' f g := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun χ _ ↦ mul_left_comm _ _ _

/-- The norm of a single angular coefficient is bounded by the average of the
absolute row values, including rows at every conductor dividing the modulus. -/
theorem norm_cylinderAverage_le {q : ℕ} [NeZero q] (r : (ZMod q)ˣ)
    (f : DirichletCharacter ℂ q → ℂ) :
    ‖cylinderAverage q r f‖ ≤ (∑ χ, ‖f χ‖) / (q.totient : ℝ) := by
  change ‖(∑ χ, conj (χ (r : ZMod q)) * f χ) / (q.totient : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro χ _
  have hχ : ‖χ (r : ZMod q)‖ = 1 :=
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity r)
  rw [norm_mul, Complex.norm_conj, hχ, one_mul]

/-- The coefficient of an integer in the full primitive Euler prime sum, averaged
over all Dirichlet characters of level `q` with the angular residue `r`. -/
def primeWeight (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (n : ℕ) : ℂ :=
  cylinderAverage q r (fun χ ↦ χ.primitiveCharacter n)

/-- The inverse Dirichlet character in the finite Fourier convention is complex conjugation. -/
theorem conj_apply_unit {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (u : (ZMod m)ˣ) : conj (χ (u : ZMod m)) = χ (u : ZMod m)⁻¹ := by
  change star (χ (u : ZMod m)) = _
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

private theorem sum_conj_apply_mul {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (x : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, conj (χ (r : ZMod q)) * χ x =
      if (r : ZMod q) = x then (q.totient : ℂ) else 0 := by
  simp only [conj_apply_unit, sum_char_inv_mul_char_eq ℂ r.isUnit]

/-- Fourier orthogonality for evaluation at any element of the residue ring. -/
theorem cylinderAverage_eval {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (x : ZMod q) :
    cylinderAverage q r (fun χ ↦ χ x) = if (r : ZMod q) = x then 1 else 0 := by
  change (∑ χ : DirichletCharacter ℂ q, conj (χ (r : ZMod q)) * χ x) / q.totient = _
  rw [sum_conj_apply_mul]
  split_ifs <;> simp [show (q.totient : ℂ) ≠ 0 by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne']

/-- At any integer coprime to the modulus, the cylinder is its exact residue indicator. -/
theorem primeWeight_of_coprime {q n : ℕ} [NeZero q] (hn : n.Coprime q) (r : (ZMod q)ˣ) :
    primeWeight q r n = if (r : ZMod q) = (n : ZMod q) then 1 else 0 := by
  have hprim (χ : DirichletCharacter ℂ q) : χ.primitiveCharacter n = χ n := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr hn)
  simp only [primeWeight, hprim, cylinderAverage_eval]

/-- At the prime power `p^k` only characters lifted from the prime-to-`p` part of
the modulus can contribute. Their orthogonality counts the specified residue and
the full modulus determines the normalizing Haar mass. -/
theorem primeWeight_prime_pow {q p e m k : ℕ} [NeZero q] (hp : p.Prime) (hk : k ≠ 0)
    (hq : q = p ^ e * m) (hpm : ¬ p ∣ m) (r : (ZMod q)ˣ) :
    primeWeight q r (p ^ k) =
      if (ZMod.cast (r : ZMod q) : ZMod m) = (p ^ k : ℕ) then ((p ^ e).totient : ℂ)⁻¹ else 0 := by
  classical
  have hm : 0 < m := by
    by_contra! hm
    have hzero : m = 0 := Nat.eq_zero_of_le_zero hm
    exact (NeZero.ne q) (by simp [hq, hzero])
  let : NeZero m := ⟨hm.ne'⟩
  have hd : m ∣ q := hq ▸ Nat.dvd_mul_left _ _
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hpm
  let E : DirichletCharacter ℂ m ↪ DirichletCharacter ℂ q :=
    ⟨changeLevel hd, changeLevel_injective hd⟩
  let f (χ : DirichletCharacter ℂ q) := conj (χ (r : ZMod q)) * χ.primitiveCharacter (p ^ k : ℕ)
  have hsupport : ∑ χ, f χ = ∑ χ ∈ Finset.univ.map E, f χ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro χ _ hχ
    have hz : χ.primitiveCharacter (p : ℕ) = 0 := by
      by_contra hvalue
      have hpc : p.Coprime χ.conductor := Nat.isCoprime_iff_coprime.mp
        ((χ.primitiveCharacter.apply_ne_zero_iff (p : ℤ)).mp (by simpa using hvalue))
      have hcm : χ.conductor ∣ m := (hpc.symm.pow_right e).dvd_of_dvd_mul_left
        (hq ▸ χ.conductor_dvd_level)
      apply hχ
      refine Finset.mem_map.mpr ⟨changeLevel hcm χ.primitiveCharacter, Finset.mem_univ _, ?_⟩
      change changeLevel hd (changeLevel hcm χ.primitiveCharacter) = χ
      rw [← changeLevel_trans, changeLevel_primitiveCharacter]
    simp [f, Nat.cast_pow, map_pow, hz, zero_pow hk]
  let u := ZMod.unitsMap hd r
  have hχval (ψ : DirichletCharacter ℂ m) : f (E ψ) =
      ψ (u : ZMod m)⁻¹ * ψ (p ^ k : ℕ) := by
    change conj (changeLevel hd ψ (r : ZMod q)) *
      (changeLevel hd ψ).primitiveCharacter (p ^ k : ℕ) = _
    rw [changeLevel_eq_cast_of_dvd]
    change conj (ψ (u : ZMod m)) * _ = _
    rw [conj_apply_unit]
    congr 1
    rw [← Int.cast_natCast, primitiveCharacter_changeLevel_apply,
      primitiveCharacter_apply_of_isCoprime ψ (Nat.isCoprime_iff_coprime.mpr (hcop.pow_left k)),
      Int.cast_natCast]
  have hsum : ∑ χ, f χ =
      if (u : ZMod m) = (p ^ k : ℕ) then (m.totient : ℂ) else 0 := by
    rw [hsupport, Finset.sum_map]
    exact (Finset.sum_congr rfl (fun ψ _ ↦ hχval ψ)).trans
      (sum_char_inv_mul_char_eq ℂ u.isUnit ((p ^ k : ℕ) : ZMod m))
  change (∑ χ, f χ) / (q.totient : ℂ) = _
  rw [hsum]
  have hφ : (q.totient : ℂ) = ((p ^ e).totient : ℂ) * (m.totient : ℂ) := by
    rw [hq, Nat.totient_mul (hcop.pow_left e), Nat.cast_mul]
  have hm' : (m.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
  show (if (u : ZMod m) = (p ^ k : ℕ) then (m.totient : ℂ) else 0) / (q.totient : ℂ) =
    if (u : ZMod m) = (p ^ k : ℕ) then ((p ^ e).totient : ℂ)⁻¹ else 0
  split_ifs <;> simp [hφ, div_eq_mul_inv, hm', mul_comm]

/-- The angular Fourier coefficients of a parity-dependent archimedean term are
supported at `1` and `-1`. Both contributions are retained if the residues coincide. -/
theorem cylinderAverage_parity {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (A B : ℂ) :
    cylinderAverage q r (fun χ ↦ if χ (-1) = 1 then A else B) =
      (if (r : ZMod q) = 1 then (A + B) / 2 else 0) +
      (if (r : ZMod q) = -1 then (A - B) / 2 else 0) := by
  have heq : (fun χ : DirichletCharacter ℂ q ↦ if χ (-1) = 1 then A else B) =
      ((A + B) / 2) • (fun χ ↦ χ 1) + ((A - B) / 2) • (fun χ ↦ χ (-1)) := by
    funext χ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, mul_one]
    rcases χ.even_or_odd with h | h
    · change χ (-1) = 1 at h
      rw [h, ite_eq_left rfl]
      ring
    · change χ (-1) = -1 at h
      rw [h, ite_eq_right (by norm_num : (-1 : ℂ) ≠ 1)]
      ring
  rw [heq, map_add, map_smul, map_smul, cylinderAverage_eval, cylinderAverage_eval]
  split_ifs <;> simp

private theorem prime_pow_le_two_totient {p : ℕ} (hp : p.Prime) (e : ℕ) :
    p ^ e ≤ 2 * (p ^ e).totient := by
  cases e with
  | zero => simp
  | succ e =>
    rw [Nat.totient_prime_pow_succ hp, pow_succ]
    have hh : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left (p ^ e) hh

/-- At a different prime power, the cylinder around `b` has weight at most
`2 |p^k-b| / q`, also when the modulus is divisible by that prime. -/
theorem norm_primeWeight_le_of_ne {q b p k : ℕ} [NeZero q] (hp : p.Prime) (hk : k ≠ 0)
    (hb : b.Coprime q) (hne : p ^ k ≠ b) :
    ‖primeWeight q (ZMod.unitOfCoprime b hb) (p ^ k)‖ ≤
      2 * (((p ^ k : ℕ) : ℤ) - (b : ℤ)).natAbs / (q : ℝ) := by
  let e := q.factorization p
  let m := q / p ^ e
  have hq : q = p ^ e * m := (Nat.ordProj_mul_ordCompl_eq_self q p).symm
  have hpm : ¬ p ∣ m := hp.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hp (NeZero.ne q))
  have hd : m ∣ q := Nat.ordCompl_dvd q p
  rw [primeWeight_prime_pow hp hk hq hpm, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
  split_ifs with h
  · have hmEq := (ZMod.natCast_eq_natCast_iff b (p ^ k) m).mp h
    have hmd : m ∣ (((p ^ k : ℕ) : ℤ) - (b : ℤ)).natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hmEq.dvd)
    have hmle := Nat.le_of_dvd (Int.natAbs_pos.mpr
      (sub_ne_zero.mpr (show ((p ^ k : ℕ) : ℤ) ≠ b by exact_mod_cast hne))) hmd
    have hbound : q ≤ (2 * (((p ^ k : ℕ) : ℤ) - (b : ℤ)).natAbs) * (p ^ e).totient := by
      rw [hq]
      calc
        p ^ e * m ≤ (2 * (p ^ e).totient) * (((p ^ k : ℕ) : ℤ) - (b : ℤ)).natAbs :=
          Nat.mul_le_mul (prime_pow_le_two_totient hp e) hmle
        _ = _ := by ring
    have hφ : (0 : ℝ) < (p ^ e).totient := by
      exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos e)
    rw [norm_inv, Complex.norm_natCast, ← one_div]
    exact (div_le_div_iff₀ hφ (by exact_mod_cast NeZero.pos q)).mpr (by
      rw [one_mul]
      exact_mod_cast hbound)
  · rw [norm_zero]
    positivity

end RiemannMasullo.RationalConductor
