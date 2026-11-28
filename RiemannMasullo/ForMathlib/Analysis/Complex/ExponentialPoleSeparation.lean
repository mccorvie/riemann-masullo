module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Spacing of zeros of finitely many exponential denominators -/

public section

open scoped BigOperators

namespace RiemannMasullo

/-- An inverse-polynomial bound on the reciprocal of each exponential denominator at the
poles of a finite family separates its distinct poles by an inverse power of their height.
Reciprocals are totalized, so the bound imposes no condition at an exact coincidence. -/
theorem finitePoleSpacing_of_reciprocalDenominatorBound {ι : Type*} [Fintype ι]
    (pole : ι → ℂ → Prop) (L : ι → ℝ) (u : ι → ℂ) (hL : ∀ v, 0 < L v)
    (hroot : ∀ v a, pole v a → u v * Complex.exp (-(L v : ℂ) * a) = 1)
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hbound : ∀ v w a, pole v a →
      ‖(1 - u w * Complex.exp (-(L w : ℂ) * a))⁻¹‖ ≤ C * (1 + |a.im|) ^ d) :
    ∃ c > (0 : ℝ), ∀ a b : ℂ, (∃ v, pole v a) → (∃ w, pole w b) → a ≠ b →
      c / (1 + |a.im|) ^ d ≤ ‖b - a‖ := by
  let M := 1 + ∑ v, L v
  let K := max 1 (2 * C)
  have hsum : 0 ≤ ∑ v, L v := Finset.sum_nonneg fun v _ ↦ (hL v).le
  have hM : 0 < M := by dsimp [M]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos := zero_lt_one.trans_le hK
  refine ⟨(K * M)⁻¹, inv_pos.mpr (mul_pos hKpos hM), ?_⟩
  rintro a b ⟨v, ha⟩ ⟨w, hb⟩ hab
  let W := (1 + |a.im|) ^ d
  have hW : 1 ≤ W := one_le_pow₀ (by linarith [abs_nonneg a.im])
  have hWpos := zero_lt_one.trans_le hW
  let z := -(L w : ℂ) * (a - b)
  have hz : z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hL w).ne'))
    (sub_ne_zero.mpr hab)
  have hphase : u w * Complex.exp (-(L w : ℂ) * a) = Complex.exp z := by
    calc
      _ = (u w * Complex.exp (-(L w : ℂ) * b)) * Complex.exp z := by
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        dsimp [z]
        ring
      _ = _ := by rw [hroot w b hb, one_mul]
  have hscale : ‖z‖ ≤ M * ‖b - a‖ := by
    have hsingle := Finset.single_le_sum (f := L) (fun i _ ↦ (hL i).le) (Finset.mem_univ w)
    have hwM : L w ≤ M := by dsimp [M]; linarith
    rw [show ‖z‖ = L w * ‖b - a‖ by
      simp only [z, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (hL w).le,
        norm_sub_rev a b]]
    exact mul_le_mul_of_nonneg_right hwM (norm_nonneg _)
  have hseparate : 1 ≤ K * W * ‖z‖ := by
    rcases le_or_gt 1 ‖z‖ with hfar | hnear
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hW) hfar
    · have hsq : ‖z‖ ^ 2 < ‖z‖ := by
        simpa only [pow_two, mul_one] using mul_lt_mul_of_pos_left hnear (norm_pos_iff.mpr hz)
      have hD : 1 - Complex.exp z ≠ 0 := by
        intro h
        have he := (sub_eq_zero.mp h).symm
        have hrem := Complex.norm_exp_sub_one_sub_id_le hnear.le
        rw [he, sub_self, zero_sub, norm_neg] at hrem
        exact hsq.not_ge hrem
      have hbound' := hbound v w a ha
      rw [hphase, norm_inv] at hbound'
      have hrec := (inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hD)).mp hbound'
      have hchord : ‖1 - Complex.exp z‖ ≤ 2 * ‖z‖ := by
        rw [norm_sub_rev]
        exact Complex.norm_exp_sub_one_le hnear.le
      calc
        1 ≤ C * W * ‖1 - Complex.exp z‖ := hrec
        _ ≤ C * W * (2 * ‖z‖) := mul_le_mul_of_nonneg_left hchord (mul_nonneg hC hWpos.le)
        _ = (2 * C) * W * ‖z‖ := by ring
        _ ≤ K * W * ‖z‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hWpos.le) (norm_nonneg _)
  apply (div_le_iff₀ hWpos).mpr
  apply (inv_le_iff_one_le_mul₀' (mul_pos hKpos hM)).mpr
  calc
    1 ≤ K * W * ‖z‖ := hseparate
    _ ≤ K * W * (M * ‖b - a‖) := mul_le_mul_of_nonneg_left hscale (mul_nonneg hKpos.le hWpos.le)
    _ = _ := by ring

end RiemannMasullo
