module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.PrimitiveFourier
import Mathlib.Tactic

/-! # Plancherel's identity for one-residue Fourier coefficients -/

@[expose] public noncomputable section

open Classical
open scoped ComplexConjugate

namespace RiemannMasullo.RationalConductor

private theorem sum_character_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ r : (ZMod q)ˣ, χ (r : ZMod q) = if χ = 1 then (q.totient : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card_units_eq_totient]
  · obtain ⟨b,hb⟩ := MulChar.ne_one_iff.mp h
    refine eq_zero_of_mul_eq_self_left hb ?_
    simp only [Finset.mul_sum, ← map_mul]
    exact (Group.mulLeft_bijective b).sum_comp (fun r : (ZMod q)ˣ ↦ χ (r : ZMod q))

private theorem row_orthogonality {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    ∑ r : (ZMod q)ˣ, χ (r : ZMod q) * conj (ψ (r : ZMod q)) =
      if ψ = χ then (q.totient : ℂ) else 0 := by
  have he (r : (ZMod q)ˣ) : χ (r : ZMod q) * conj (ψ (r : ZMod q)) =
      (χ / ψ) (r : ZMod q) := by
    change _ * star _ = _
    rw [MulChar.star_apply', div_eq_mul_inv, MulChar.mul_apply]
  simp_rw [he]
  rw [sum_character_units]
  rw [div_eq_one]
  by_cases h : ψ = χ
  · simp [h]
  · simp [h, Ne.symm h]

/-- Fourier inversion with the actual one-residue cylinder normalization. -/
theorem sum_eval_cylinderAverage {q : ℕ} [NeZero q] (v : DirichletCharacter ℂ q → ℂ)
    (χ : DirichletCharacter ℂ q) :
    ∑ r : (ZMod q)ˣ, χ (r : ZMod q) * cylinderAverage q r v = v χ := by
  have hq : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  change ∑ r : (ZMod q)ˣ, χ (r : ZMod q) * ((∑ ψ, conj (ψ (r : ZMod q)) * v ψ) / _) = _
  simp_rw [← mul_div_assoc, Finset.mul_sum, ← mul_assoc]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, row_orthogonality]
  simp [ite_mul, hq]

/-- The total square error over residues is precisely the mean square of the
character rows. Both sums are unweighted, with the factor 1/φ(q) on the right. -/
theorem sum_norm_sq_cylinderAverage {q : ℕ} [NeZero q] (v : DirichletCharacter ℂ q → ℂ) :
    ∑ r : (ZMod q)ˣ, ‖cylinderAverage q r v‖ ^ 2 = (∑ χ, ‖v χ‖ ^ 2) / q.totient := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_natCast, Complex.sq_norm,
    Complex.normSq_eq_conj_mul_self]
  have he (r : (ZMod q)ˣ) : conj (cylinderAverage q r v) =
      (∑ χ, χ (r : ZMod q) * conj (v χ)) / q.totient := by
    change conj ((∑ χ, conj (χ (r : ZMod q)) * v χ) / _) = _
    simp
  simp_rw [he, div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  simp_rw [mul_right_comm (χ _) (conj (v χ)), ← Finset.sum_mul, sum_eval_cylinderAverage, mul_comm]

end RiemannMasullo.RationalConductor
