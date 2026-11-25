module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import RiemannMasullo.ForMathlib.Analysis.Complex.StripJetEnergy
import Mathlib.Data.Nat.Choose.Basic

/-! # Derivative control of the strip resolvent multiplier -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace RiemannMasullo.StripRationalMultiplier

private theorem affineJet (A s : ℂ) (k : ℕ) {z : ℂ} :
    iteratedDeriv k (fun w : ℂ => (A + s*w)⁻¹) z =
      ((k.factorial : ℂ) * (-s)^k) * ((A + s*z)⁻¹)^(k+1) := by
  simp_rw [add_comm A (s * _)]
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  change (-1 : ℂ)^k * (k.factorial : ℂ) * s^k * (s*z+A)^(-1-(k:ℤ)) = _
  rw [show (-1-(k:ℤ)) = -((k+1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, inv_pow, show -s = (-1 : ℂ)*s by ring, mul_pow]
  ring

private theorem polePower {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : b ≤ u.re)
    (k : ℕ) (hk : 1 ≤ k) : ‖u⁻¹‖^(k+1) ≤ (b^k)⁻¹ * u⁻¹.re := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hbu : b ≤ ‖u‖ := hu.trans ((le_abs_self _).trans (Complex.abs_re_le_norm u))
  have hn : 0 < ‖u‖ := hb.trans_le hbu
  rw [norm_inv, inv_pow, Complex.inv_re, Complex.normSq_eq_norm_sq]
  simp only [← one_div, div_mul_div_comm, one_mul]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hh := mul_le_mul (pow_le_pow_left₀ hb.le hbu n) hu hb.le (pow_nonneg hn.le n)
  calc
    _ = (b^n * b) * ‖u‖^2 := by rw [pow_succ, one_mul]
    _ ≤ (‖u‖^n * u.re) * ‖u‖^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by simp only [pow_succ]; ring

private theorem affineBound (A s z : ℂ) (hs : ‖s‖ = 1) (b : ℝ) (hb : 0 < b)
    (hu : b ≤ (A+s*z).re) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedDeriv k (fun w : ℂ => (A+s*w)⁻¹) z‖ ≤
      ((k.factorial : ℝ) * (b^k)⁻¹) * (A+s*z)⁻¹.re := by
  rw [affineJet A s k]
  simp only [norm_mul, norm_pow, norm_neg, hs, one_pow, mul_one, Complex.norm_natCast]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (polePower hb hu k hk) (by positivity)

/-- The derivatives are bounded in terms of the positive real part and the distance to the poles. -/
theorem norm_iteratedDeriv_le {L α : ℝ} (hL : α < L) {z : ℂ} (hz : |z.re| ≤ α)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedDeriv k (fun w : ℂ => 1 / ((L : ℂ)^2 - w^2)) z‖ ≤
      ((k.factorial : ℝ) * ((L-α)^k)⁻¹) * (1 / ((L : ℂ)^2 - z^2)).re := by
  let c : ℝ := (2*L)⁻¹
  have hLp : 0 < L := lt_of_le_of_lt ((abs_nonneg z.re).trans hz) hL
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hm : L-α ≤ ((L : ℂ)-z).re := by simpa using sub_le_sub_left (abs_le.mp hz).2 L
  have hp : L-α ≤ ((L : ℂ)+z).re := by simp; linarith [(abs_le.mp hz).1]
  have hm0 : (L : ℂ)-z ≠ 0 := fun e => by simp [e] at hm; linarith
  have hp0 : (L : ℂ)+z ≠ 0 := fun e => by simp [e] at hp; linarith
  have he : (fun w : ℂ => 1 / ((L : ℂ)^2-w^2)) =ᶠ[𝓝 z]
      fun w => (c : ℂ) * (((L : ℂ)-w)⁻¹ + ((L : ℂ)+w)⁻¹) := by
    filter_upwards [(continuousAt_const.sub continuousAt_id).eventually_ne hm0,
      (continuousAt_const.add continuousAt_id).eventually_ne hp0] with w hw hw'
    change ((L : ℂ) - w) ≠ 0 at hw
    change ((L : ℂ) + w) ≠ 0 at hw'
    have e : (L : ℂ)^2-w^2 = ((L : ℂ)-w)*((L : ℂ)+w) := by ring
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hLp.ne'
    dsimp [c]; push_cast; rw [e]; field_simp [hw, hw', hLc]; ring
  have dm : ContDiffAt ℂ k (fun w : ℂ => ((L : ℂ)-w)⁻¹) z :=
    (contDiffAt_const.sub contDiffAt_id).inv hm0
  have dp : ContDiffAt ℂ k (fun w : ℂ => ((L : ℂ)+w)⁻¹) z :=
    (contDiffAt_const.add contDiffAt_id).inv hp0
  have bm := affineBound L (-1) z (by simp) (L-α) (sub_pos.mpr hL)
    (by simpa [sub_eq_add_neg] using hm) k hk
  have bp := affineBound L 1 z (by simp) (L-α) (sub_pos.mpr hL) (by simpa using hp) k hk
  simp only [neg_one_mul, ← sub_eq_add_neg, one_mul] at bm bp
  have hzrw : 1 / ((L : ℂ)^2 - z^2) = (c : ℂ) * (((L : ℂ)-z)⁻¹ + ((L : ℂ)+z)⁻¹) :=
    he.self_of_nhds
  rw [he.iteratedDeriv_eq k, iteratedDeriv_const_mul_field, iteratedDeriv_fun_add dm dp,
    norm_mul, Complex.norm_of_nonneg hc, hzrw]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re]
  refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add bm bp)) hc).trans_eq ?_
  ring

open Finset

/-- The real part of the rational multiplier is strictly positive on the closed strip. -/
theorem multiplier_re_pos {L α : ℝ} (hL : α < L) {z : ℂ} (hz : |z.re| ≤ α) :
    0 < (1 / ((L : ℂ)^2 - z^2)).re := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp hz
  have h₃ : 0 < (L - z.re) * (L + z.re) := mul_pos (by linarith) (by linarith)
  have h : 0 < ((L : ℂ)^2 - z^2).re := by
    simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq_nonneg z.im]
  have hn : (L : ℂ)^2 - z^2 ≠ 0 := fun e => by simp [e] at h
  rw [one_div, Complex.inv_re]
  exact div_pos h (Complex.normSq_pos.mpr hn)

private theorem thirds_sum (m : ℕ) :
    (∑ r ∈ range m, (1/3 : ℝ)^(r+1)) ≤ 1/2 := by
  have he (n : ℕ) : (∑ r ∈ range n, (1/3 : ℝ)^(r+1)) = (1 - (1/3 : ℝ)^n)/2 := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
  rw [he]
  linarith [show 0 ≤ (1/3 : ℝ)^m by positivity]

/-- A strip-to-pole distance at least three times the jet order makes the off-diagonal
Leibniz coefficient sum at most half of the diagonal coefficient. -/
theorem coefficient_sum_le_half (m : ℕ) {L α : ℝ} (hL : α < L)
    (hgap : 3 * (m : ℝ) ≤ L - α) {z : ℂ} (hz : |z.re| ≤ α) :
    (∑ r ∈ range m, (m.choose (r+1) : ℝ) *
      ‖iteratedDeriv (r+1) (fun w : ℂ => 1 / ((L : ℂ)^2 - w^2)) z‖) ≤
        (1 / ((L : ℂ)^2 - z^2)).re / 2 := by
  let p := (1 / ((L : ℂ)^2 - z^2)).re
  have hp : 0 ≤ p := (multiplier_re_pos hL hz).le
  have hb : 0 < L - α := sub_pos.mpr hL
  have hratio : (m : ℝ) / (L - α) ≤ 1 / 3 := (div_le_iff₀ hb).2 (by linarith)
  have hs (k : ℕ) (hk : 1 ≤ k) :
      (m.choose k : ℝ) * ‖iteratedDeriv k (fun w : ℂ => 1 / ((L : ℂ)^2 - w^2)) z‖ ≤
        (1/3 : ℝ)^k * p := by
    have hn := Nat.descFactorial_le_pow m k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hn
    have hc : (k.factorial : ℝ) * (m.choose k : ℝ) ≤ (m : ℝ)^k := by exact_mod_cast hn
    calc
      _ ≤ (m.choose k : ℝ) * (((k.factorial : ℝ) * ((L-α)^k)⁻¹) * p) :=
        mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le hL hz k hk)
          (by positivity)
      _ = (((k.factorial : ℝ) * (m.choose k : ℝ)) / (L-α)^k) * p := by rw [div_eq_mul_inv]; ring
      _ ≤ ((m : ℝ)^k / (L-α)^k) * p :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc (pow_nonneg hb.le k)) hp
      _ ≤ _ := by
        rw [← div_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio k) hp
  calc
    _ ≤ ∑ r ∈ range m, (1/3 : ℝ)^(r+1) * p := sum_le_sum fun r _ => hs (r+1) (by omega)
    _ = (∑ r ∈ range m, (1/3 : ℝ)^(r+1)) * p := (sum_mul ..).symm
    _ ≤ (1/2 : ℝ) * p := mul_le_mul_of_nonneg_right (thirds_sum m) hp
    _ = _ := by dsimp [p]; ring

/-- The strip resolvent is accretive for every finite strip jet energy once the two
poles are sufficiently far from the strip. -/
theorem jet_re_lower (m : ℕ) {L α : ℝ} (hL : α < L)
    (hgap : 3 * (m : ℝ) ≤ L - α) {z : ℂ} (hz : |z.re| ≤ α)
    {F : ℂ → ℂ} (hF : ContDiffAt ℂ m F z) :
    let Ψ : ℂ → ℂ := fun w ↦ 1 / ((L : ℂ)^2 - w^2)
    (Ψ z).re / 2 * (∑ j ∈ range (m + 1), ‖iteratedDeriv j F z‖ ^ 2) ≤
      ∑ j ∈ range (m + 1), (star (iteratedDeriv j F z) *
        iteratedDeriv j (fun w ↦ Ψ w * F w) z).re := by
  intro Ψ
  have hden : (L : ℂ)^2 - z^2 ≠ 0 := by
    intro he
    have hp := multiplier_re_pos hL hz
    simp [he] at hp
  have hp (j : ℕ) : ContDiffAt ℂ j Ψ z :=
    contDiffAt_const.div (contDiffAt_const.sub (contDiffAt_id.pow 2)) hden
  have hprod (j : ℕ) (hj : j ≤ m) :
      iteratedDeriv j (fun w ↦ Ψ w * F w) z =
        ∑ k ∈ range (j + 1), (j.choose k : ℂ) *
          iteratedDeriv k Ψ z * iteratedDeriv (j - k) F z :=
    iteratedDeriv_fun_mul (hp j) (hF.of_le (by exact_mod_cast hj))
  exact HigherStripEnergy.leibniz_re_lower m (fun j ↦ iteratedDeriv j F z)
    (fun j ↦ iteratedDeriv j Ψ z) (fun j ↦ iteratedDeriv j (fun w ↦ Ψ w * F w) z)
    hprod (coefficient_sum_le_half m hL hgap hz)

end RiemannMasullo.StripRationalMultiplier
