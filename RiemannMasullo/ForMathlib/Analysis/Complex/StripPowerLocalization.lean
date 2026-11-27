module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import RiemannMasullo.ForMathlib.Analysis.Complex.StripJetEnergy

/-! # Positive strip resolvent powers localized at an ordinate -/

@[expose] public noncomputable section

namespace RiemannMasullo

private theorem norm_poleJet {d : ℝ} (hd : 0 < d) {u : ℂ} (hu : d ≤ ‖u‖)
    {K m j : ℕ} (hj : j ≤ m) :
    ‖iteratedDeriv j (fun w : ℂ => w ^ (-(K : ℤ))) u‖ ≤
      (((K : ℝ) + m) / d)^j * ‖u ^ (-(K : ℤ))‖ := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (hd.trans_le hu)
  have hc : (∏ i ∈ Finset.range j, ‖(-(K : ℂ)) - i‖) ≤ ((K : ℝ) + m)^j := by
    calc
      _ ≤ ∏ _i ∈ Finset.range j, ((K : ℝ) + m) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i hi
        have him : i ≤ m := (Finset.mem_range.mp hi).le.trans hj
        calc
          _ ≤ ‖-(K : ℂ)‖ + ‖(i : ℂ)‖ := norm_sub_le _ _
          _ ≤ _ := by simp only [norm_neg, Complex.norm_natCast]; exact_mod_cast Nat.add_le_add_left him K
      _ = _ := by simp
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg u))
    (inv_anti₀ hd hu) j
  rw [iteratedDeriv_eq_iterate, iter_deriv_zpow, sub_eq_add_neg (-(K : ℤ)),
    zpow_add₀ hu0, zpow_neg u (j : ℤ), zpow_natCast]
  simp only [norm_mul, norm_inv, norm_pow, norm_prod, Int.cast_neg, Int.cast_natCast]
  calc
    _ = (∏ i ∈ Finset.range j, ‖(-(K : ℂ)) - i‖) * (‖u‖⁻¹)^j * ‖u ^ (-(K : ℤ))‖ := by rw [inv_pow]; ring
    _ ≤ (((K : ℝ) + m)^j * (d⁻¹)^j) * ‖u ^ (-(K : ℤ))‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hc hp (by positivity) (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]

/-- A relative bound for every jet through order `m`, uniform on the closed strip. -/
private theorem norm_iteratedDeriv_stripResolventPower_le {L α : ℝ} (hL : α < L)
    {z : ℂ} (hz : |z.re| ≤ α) (K m k : ℕ) (hk : k ≤ m) :
    ‖iteratedDeriv k (fun w : ℂ => ((L : ℂ)^2 - w^2) ^ (-(K : ℤ))) z‖ ≤
      (2 * ((K : ℝ) + m) / (L - α))^k * ‖((L : ℂ)^2 - z^2) ^ (-(K : ℤ))‖ := by
  let f := fun w : ℂ => ((L : ℂ) - w) ^ (-(K : ℤ))
  let g := fun w : ℂ => ((L : ℂ) + w) ^ (-(K : ℤ))
  let C := ((K : ℝ) + m) / (L - α)
  have fac : (fun w : ℂ => ((L : ℂ)^2 - w^2) ^ (-(K : ℤ))) = f * g := by
    funext w
    change ((L : ℂ)^2-w^2) ^ (-(K : ℤ)) = _ * _
    rw [show (L : ℂ)^2-w^2 = ((L : ℂ)-w)*((L : ℂ)+w) by ring, mul_zpow]
  have hm : L-α ≤ ((L : ℂ)-z).re := by simpa using sub_le_sub_left (abs_le.mp hz).2 L
  have hp : L-α ≤ ((L : ℂ)+z).re := by simp; linarith [(abs_le.mp hz).1]
  have dm := hm.trans ((le_abs_self _).trans (Complex.abs_re_le_norm ((L : ℂ)-z)))
  have dp := hp.trans ((le_abs_self _).trans (Complex.abs_re_le_norm ((L : ℂ)+z)))
  have hd := sub_pos.mpr hL
  have fm' : ContDiffAt ℂ k (fun w : ℂ ↦ (L : ℂ) - w) z :=
    contDiffAt_const.sub contDiffAt_id
  have gp' : ContDiffAt ℂ k (fun w : ℂ ↦ (L : ℂ) + w) z :=
    contDiffAt_const.add contDiffAt_id
  have fm : ContDiffAt ℂ k f z := by
    simpa only [f, zpow_neg, zpow_natCast] using
      (fm'.pow K).fun_inv (pow_ne_zero K (norm_pos_iff.mp (hd.trans_le dm)))
  have gp : ContDiffAt ℂ k g z := by
    simpa only [g, zpow_neg, zpow_natCast] using
      (gp'.pow K).fun_inv (pow_ne_zero K (norm_pos_iff.mp (hd.trans_le dp)))
  have bf (j : ℕ) (hj : j ≤ m) : ‖iteratedDeriv j f z‖ ≤ C^j * ‖f z‖ := by
    dsimp only [f]
    rw [iteratedDeriv_comp_const_sub j (fun w : ℂ => w ^ (-(K : ℤ))) (L : ℂ)]
    simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
      norm_poleJet (K := K) hd dm hj
  have bg (j : ℕ) (hj : j ≤ m) : ‖iteratedDeriv j g z‖ ≤ C^j * ‖g z‖ := by
    dsimp only [g]
    rw [iteratedDeriv_comp_const_add j (fun w : ℂ => w ^ (-(K : ℤ))) (L : ℂ)]
    exact norm_poleJet hd dp hj
  have hzfac := congrFun fac z
  change ((L : ℂ)^2-z^2) ^ (-(K : ℤ)) = f z * g z at hzfac
  rw [fac, iteratedDeriv_mul fm gp, hzfac, norm_mul]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * (C^k * (‖f z‖ * ‖g z‖)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
      simp only [norm_mul, Complex.norm_natCast]
      calc
        _ ≤ ((k.choose i : ℝ) * (C^i * ‖f z‖)) * (C^(k-i) * ‖g z‖) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (bf i (hik.trans hk)) (by positivity))
            (bg _ ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
          dsimp [C]; positivity
        _ = _ := by
          have he : C^i * C^(k-i) = C^k := by rw [← pow_add, show i + (k-i) = k by omega]
          calc
            _ = (k.choose i : ℝ) * ((C^i * C^(k-i)) * (‖f z‖ * ‖g z‖)) := by ring
            _ = _ := by rw [he]
    _ = _ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [C]; rw [show 2 * ((K : ℝ) + m) / (L-α) = 2 * (((K : ℝ) + m) / (L-α)) by ring, mul_pow]; ring

end RiemannMasullo

namespace RiemannMasullo.StripResolventPowerSector

private theorem power_error (w : ℂ) {e : ℝ} (he : ‖w - (‖w‖ : ℂ)‖ ≤ e * ‖w‖)
    (n : ℕ) : ‖w^n - (‖w‖ : ℂ)^n‖ ≤ (n : ℝ) * e * ‖w‖^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ‖(w^n - (‖w‖ : ℂ)^n) * w + (‖w‖ : ℂ)^n * (w - (‖w‖ : ℂ))‖ := by
        simp only [pow_succ]; congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ = ‖w^n - (‖w‖ : ℂ)^n‖ * ‖w‖ + ‖w‖^n * ‖w - (‖w‖ : ℂ)‖ := by
        simp [norm_pow, Complex.norm_real]
      _ ≤ ((n : ℝ) * e * ‖w‖^n) * ‖w‖ + ‖w‖^n * (e * ‖w‖) :=
        add_le_add (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
          (mul_le_mul_of_nonneg_left he (by positivity))
      _ = _ := by rw [Nat.cast_succ, pow_succ]; ring

private theorem re_power {w : ℂ} (hw : 0 ≤ w.re) (K : ℕ)
    (hs : 4 * (K : ℝ) * |w.im| ≤ w.re) : ‖w‖^K / 2 ≤ (w^K).re := by
  cases K with
  | zero => norm_num
  | succ n =>
    let k : ℝ := ((n+1 : ℕ) : ℝ)
    have hk : 0 < k := by dsimp [k]; positivity
    have hr : w.re ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_re_le_norm w)
    have ht := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_nonneg hw] at ht
    have hc := Complex.norm_le_abs_re_add_abs_im (w - (‖w‖ : ℂ))
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero, abs_of_nonpos (sub_nonpos.mpr hr)] at hc
    have hd : ‖w - (‖w‖ : ℂ)‖ ≤ 2 * |w.im| := by linarith
    change 4 * k * |w.im| ≤ w.re at hs
    have he : ‖w - (‖w‖ : ℂ)‖ ≤ (1 / (2*k)) * ‖w‖ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hd (show 0 ≤ 2*k by positivity)]
    have hp := power_error w he (n+1)
    change _ ≤ k * (1/(2*k)) * ‖w‖^(n+1) at hp
    rw [show k * (1/(2*k)) = 1/2 by field_simp [hk.ne']] at hp
    have hneg := (neg_le_abs (w^(n+1) - (‖w‖ : ℂ)^(n+1)).re).trans
      (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re] at hneg
    rw [← Complex.ofReal_pow] at hp
    linarith

private theorem denom_re {L α : ℝ} {z : ℂ} (hz : |z.re| ≤ α) :
    L^2 - α^2 + z.im^2 ≤ ((L : ℂ)^2 - z^2).re := by
  have hs := pow_le_pow_left₀ (abs_nonneg z.re) hz 2
  rw [sq_abs] at hs
  simp [pow_two, Complex.mul_re]; nlinarith

/-- Powers of the resolvent remain inside a uniform right-hand sector on the strip. -/
private theorem half_norm_pow_le_re {L α : ℝ} (hL : α < L) {z : ℂ} (hz : |z.re| ≤ α)
    (K : ℕ) (hK : 8 * (K : ℝ) * α ≤ L-α) :
    ‖((L : ℂ)^2-z^2)⁻¹‖^K / 2 ≤ ((((L : ℂ)^2-z^2)⁻¹)^K).re := by
  let D := (L : ℂ)^2-z^2
  have ha := (abs_nonneg z.re).trans hz
  have hgap : 0 < L-α := sub_pos.mpr hL
  have hr : L^2-α^2+z.im^2 ≤ D.re := denom_re hz
  have hcross : 2*(L-α)*|z.im| ≤ D.re := by
    nlinarith [sq_nonneg ((L-α)-|z.im|), sq_abs z.im, mul_nonneg ha hgap.le]
  have him : |D.im| = 2 * |z.re| * |z.im| := by
    have h : D.im = -(2*z.re*z.im) := by simp [D, pow_two, Complex.mul_im]; ring
    rw [h, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hsec : 4*(K:ℝ)*|D.im| ≤ D.re := by
    rw [him]
    have hh := mul_le_mul_of_nonneg_left hz (show 0 ≤ 8*(K:ℝ) by positivity)
    nlinarith [mul_le_mul_of_nonneg_right (hh.trans hK) (abs_nonneg z.im),
      mul_nonneg hgap.le (abs_nonneg z.im)]
  have hpos : 0 < D.re := by nlinarith [sq_pos_of_pos hgap, mul_nonneg ha hgap.le, sq_nonneg z.im]
  apply re_power (w := D⁻¹)
  · rw [Complex.inv_re]; exact div_nonneg hpos.le (Complex.normSq_nonneg _)
  · rw [Complex.inv_im, Complex.inv_re, abs_div, abs_neg, abs_of_nonneg (Complex.normSq_nonneg D),
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hsec (Complex.normSq_nonneg _)

/-- Polynomial ordinate decay, including the full pole-distance constant. -/
private theorem norm_power_le {L α : ℝ} (hL : α < L) {z : ℂ} (hz : |z.re| ≤ α) (K : ℕ) :
    ‖(((L : ℂ)^2-z^2)⁻¹)^K‖ ≤ ((L^2-α^2+z.im^2)⁻¹)^K := by
  have ha := (abs_nonneg z.re).trans hz
  have hp : 0 < L^2-α^2+z.im^2 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hL), mul_nonneg ha (sub_nonneg.mpr hL.le), sq_nonneg z.im]
  rw [norm_pow, norm_inv]
  apply pow_le_pow_left₀ (by positivity)
  exact inv_anti₀ hp ((denom_re hz).trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))

end RiemannMasullo.StripResolventPowerSector

open Finset

namespace RiemannMasullo.StripPowerLocalization

/-- The `K`-th resolvent power centered at ordinate `b`. -/
def stripResolventPower (L b : ℝ) (K : ℕ) (z : ℂ) : ℂ :=
  ((L : ℂ)^2 - (z - (b : ℂ) * Complex.I)^2) ^ (-(K : ℤ))

private theorem sector_eq (L b : ℝ) (K : ℕ) (z : ℂ) :
    stripResolventPower L b K z = (((L : ℂ)^2 - (z - (b : ℂ) * Complex.I)^2)⁻¹)^K := by
  rw [stripResolventPower, zpow_neg, zpow_natCast, inv_pow]

private theorem shift_re (b : ℝ) (z : ℂ) : (z - (b : ℂ) * Complex.I).re = z.re := by simp

private theorem shift_im (b : ℝ) (z : ℂ) : (z - (b : ℂ) * Complex.I).im = z.im - b := by simp

private theorem fifths_sum (m : ℕ) :
    (∑ r ∈ range m, (1/5 : ℝ)^(r+1)) ≤ 1/4 := by
  have h (n : ℕ) : (∑ r ∈ range n, (1/5 : ℝ)^(r+1)) = (1 - (1/5 : ℝ)^n)/4 := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
  rw [h]
  linarith [show 0 ≤ (1/5 : ℝ)^m by positivity]

/-- A sufficiently remote positive resolvent power satisfies the finite off-diagonal
coefficient bound uniformly, for every center ordinate. -/
theorem coefficient_sum_le_half (K m : ℕ) {L α : ℝ} (hL : α < L)
    (hsector : 8 * (K : ℝ) * α ≤ L - α)
    (hsize : 10 * (m : ℝ) * ((K : ℝ) + m) ≤ L - α)
    (b : ℝ) {z : ℂ} (hz : |z.re| ≤ α) :
    (∑ r ∈ range m, (m.choose (r+1) : ℝ) *
      ‖iteratedDeriv (r+1) (stripResolventPower L b K) z‖) ≤
        (stripResolventPower L b K z).re / 2 := by
  let w := z - (b : ℂ) * Complex.I
  let u := stripResolventPower L b K z
  let D := 2 * ((K : ℝ) + m) / (L - α)
  have hw : |w.re| ≤ α := by simpa [w, shift_re] using hz
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsmall : (m : ℝ) * D ≤ 1 / 5 := by
    dsimp [D]
    rw [← mul_div_assoc, div_le_iff₀ (sub_pos.mpr hL)]
    linarith
  have h (k : ℕ) (hk : k ≤ m) :
      (m.choose k : ℝ) * ‖iteratedDeriv k (stripResolventPower L b K) z‖ ≤ (1/5 : ℝ)^k * ‖u‖ := by
    have hb : (m.choose k : ℝ) ≤ (m : ℝ)^k := by
      exact_mod_cast Nat.choose_le_pow m k
    have hd : ‖iteratedDeriv k (stripResolventPower L b K) z‖ ≤ D^k * ‖u‖ := by
      let Q (v : ℂ) := ((L : ℂ)^2 - v^2) ^ (-(K : ℤ))
      change ‖iteratedDeriv k (fun v ↦ Q (v - (b : ℂ) * Complex.I)) z‖ ≤ D^k * ‖u‖
      rw [iteratedDeriv_comp_sub_const k Q ((b : ℂ) * Complex.I)]
      exact norm_iteratedDeriv_stripResolventPower_le hL hw K m k hk
    calc
      _ ≤ ((m : ℝ)^k) * (D^k * ‖u‖) :=
        mul_le_mul hb hd (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = ((m : ℝ) * D)^k * ‖u‖ := by rw [mul_pow]; ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsmall k) (norm_nonneg _)
  have hRe : ‖u‖ / 2 ≤ u.re := by
    dsimp only [u]
    rw [sector_eq, norm_pow]
    exact StripResolventPowerSector.half_norm_pow_le_re hL hw K hsector
  calc
    _ ≤ ∑ r ∈ range m, (1/5 : ℝ)^(r+1) * ‖u‖ :=
      sum_le_sum fun r hr ↦ h (r+1) (mem_range.mp hr)
    _ = (∑ r ∈ range m, (1/5 : ℝ)^(r+1)) * ‖u‖ := (sum_mul ..).symm
    _ ≤ (1/4 : ℝ) * ‖u‖ := mul_le_mul_of_nonneg_right (fifths_sum m) (norm_nonneg _)
    _ ≤ _ := by change _ ≤ u.re / 2; linarith

/-- The real part of the translated power has a uniform positive lower bound on
the unit band about its center. -/
theorem re_lower_on_unit_band (K : ℕ) {L α b : ℝ} (hL : α < L)
    (hsector : 8 * (K : ℝ) * α ≤ L - α) {z : ℂ} (hz : |z.re| ≤ α)
    (hu : |z.im - b| ≤ 1) :
    ((L^2 + (α + 1)^2)⁻¹)^K / 2 ≤ (stripResolventPower L b K z).re := by
  let w := z - (b : ℂ) * Complex.I
  let D := (L : ℂ)^2 - w^2
  have hw : |w.re| ≤ α := by simpa [w, shift_re] using hz
  have hi : |w.im| ≤ 1 := by simpa [w, shift_im] using hu
  have hα := (abs_nonneg w.re).trans hw
  have hD : 0 < ‖D‖ := by
    have h := StripResolventPowerSector.denom_re (L := L) hw
    have hp : 0 < L^2 - α^2 + w.im^2 := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr hL), mul_nonneg hα (sub_nonneg.mpr hL.le), sq_nonneg w.im]
    exact (hp.trans_le h).trans_le (Complex.re_le_norm D)
  have hb : ‖D‖ ≤ L^2 + (α + 1)^2 := by
    calc
      _ ≤ ‖(L : ℂ)^2‖ + ‖w^2‖ := norm_sub_le _ _
      _ = L^2 + ‖w‖^2 := by simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _)
        ((Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hw hi)) 2)
  rw [sector_eq]
  refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ K) (by norm_num)).trans
    (StripResolventPowerSector.half_norm_pow_le_re hL hw K hsector)
  rw [norm_inv]
  exact inv_anti₀ hD hb

/-- A translated resolvent power has a uniform polynomial decay bound in the
distance from its center ordinate. -/
theorem norm_le_ordinate_tail (K : ℕ) {L α b : ℝ} (hL : α < L)
    (hp : 1 ≤ L^2 - α^2) {z : ℂ} (hz : |z.re| ≤ α) :
    ‖stripResolventPower L b K z‖ ≤ (2 / (1 + |z.im - b|)^2)^K := by
  let w := z - (b : ℂ) * Complex.I
  have hw : |w.re| ≤ α := by simpa [w, shift_re] using hz
  rw [sector_eq]
  apply (StripResolventPowerSector.norm_power_le hL hw K).trans
  apply pow_le_pow_left₀ (by positivity)
  have hd : 0 < L^2 - α^2 + w.im^2 := by nlinarith [sq_nonneg w.im]
  rw [← shift_im b z, ← one_div, div_le_div_iff₀ hd (by positivity)]
  simp only [one_mul]
  change (1 + |w.im|)^2 ≤ 2 * (L^2 - α^2 + w.im^2)
  nlinarith [sq_nonneg (|w.im| - 1), sq_abs w.im]

end RiemannMasullo.StripPowerLocalization
