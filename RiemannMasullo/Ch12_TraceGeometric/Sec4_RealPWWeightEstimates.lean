module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWSharpCutoff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Weight bounds for the rational real-place cutoff -/

public noncomputable section

open Filter MeasureTheory
open scoped Topology SchwartzMap

namespace RiemannMasullo.Isolated

private theorem weight_at_large {α s x : ℝ} (ha : 0 ≤ α) (hx : 1 ≤ x) :
    realPWIntervalWeight α s x = x ^ (2 * α) * (1 + Real.log x ^ 2) ^ (s / 2) := by
  rw [realPWIntervalWeight_eq _ _ (show x ≠ 0 by linarith), abs_of_nonneg (by linarith : 0 ≤ x),
    max_eq_left (Real.rpow_le_rpow_of_exponent_le hx (show -(2*α) ≤ 2*α by linarith))]

/-- On a dyadic neighborhood at the positive end the weight ratio is uniformly bounded. -/
theorem realPWIntervalWeight_near_ratio {α s x t : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (hx : 4 ≤ x) (ht : |t| ≤ x / 2) :
    Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤
      Real.sqrt ((2 : ℝ) ^ (2*α) * (4 : ℝ) ^ (s/2)) := by
  let y := x+t
  have ht' := (abs_le.mp ht).1
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hxy : x ≤ 2*y := by dsimp [y]; linarith
  have hxy2 : x ≤ y^2 := by nlinarith [mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ y-2 by linarith)]
  have hl := Real.log_le_log (by linarith : 0 < x) hxy2
  rw [Real.log_pow] at hl
  have hlogs : 1 + Real.log x ^ 2 ≤ 4 * (1 + Real.log y ^ 2) := by
    have h := Real.log_nonneg (show 1 ≤ x by linarith)
    norm_num at hl
    nlinarith [sq_nonneg (Real.log y), mul_nonneg (show 0 ≤ 2 * Real.log y - Real.log x by linarith)
      (show 0 ≤ 2 * Real.log y + Real.log x by linarith)]
  apply Real.sqrt_le_sqrt
  apply (div_le_iff₀ (show 0 < realPWIntervalWeight α s y from lt_of_lt_of_le zero_lt_one (one_le_realPWIntervalWeight α s hs y))).2
  change realPWIntervalWeight α s x ≤ _ * realPWIntervalWeight α s y
  rw [weight_at_large ha (show 1 ≤ x by linarith), weight_at_large ha (show 1 ≤ y by linarith)]
  have hp := Real.rpow_le_rpow (by linarith : 0 ≤ x) hxy (show 0 ≤ 2*α by positivity)
  have hq := Real.rpow_le_rpow (by positivity) hlogs (show 0 ≤ s/2 by positivity)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ y)] at hp
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : 0 ≤ 1 + Real.log y ^ 2)] at hq
  calc
    _ ≤ _ := mul_le_mul hp hq (by positivity) (by positivity)
    _ = _ := by ring

/-- A single polynomial in the translation controls the square-root ratio at every x ≥ 4. -/
theorem realPWIntervalWeight_translation_envelope {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ x : ℝ, 4 ≤ x → ∀ t : ℝ,
      Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤ C * (1+|t|)^N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2*α + 2*s)
  let A := Real.sqrt ((2 : ℝ) ^ (2*α) * (4 : ℝ) ^ (s/2))
  refine ⟨max A ((2 : ℝ)^N), N, fun x hx t ↦ ?_⟩
  have ht1 : 1 ≤ 1+|t| := by linarith [abs_nonneg t]
  have hpow := one_le_pow₀ ht1 (n := N)
  by_cases ht : |t| ≤ x/2
  · exact (realPWIntervalWeight_near_ratio ha hs hx ht).trans
      ((le_max_left A _).trans (le_mul_of_one_le_right (le_trans (by dsimp [A]; positivity) (le_max_left A _)) hpow))
  · let b := 2*(1+|t|)
    have hb : 1 ≤ b := by dsimp [b]; linarith
    have hb0 : 0 ≤ b := by linarith
    have hxb : x ≤ b := by dsimp [b]; push Not at ht; linarith
    have hl : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos (show 0 < x by linarith)]
    have hl0 := Real.log_nonneg (show 1 ≤ x by linarith)
    have hb2 : 1 + Real.log x ^ 2 ≤ b ^ (4:ℕ) := by
      have hsq := mul_self_le_mul_self hl0 (hl.trans hxb)
      have hb4 : 0 ≤ (b^2-2)*(b^2+1) := mul_nonneg (by nlinarith [sq_nonneg (b-4)]) (by positivity)
      nlinarith
    have hw : realPWIntervalWeight α s x ≤ b^N := by
      rw [weight_at_large ha (show 1 ≤ x by linarith)]
      have hp := Real.rpow_le_rpow (by linarith : 0 ≤ x) hxb (show 0 ≤ 2*α by positivity)
      have hq := Real.rpow_le_rpow (by positivity) hb2 (show 0 ≤ s/2 by positivity)
      rw [← Real.rpow_natCast b 4, ← Real.rpow_mul (by linarith : 0 ≤ b)] at hq
      calc
        _ ≤ _ := mul_le_mul hp hq (by positivity) (by positivity)
        _ = b ^ (2*α + 2*s) := by
          rw [← Real.rpow_add (by linarith : 0 < b)]
          congr 1
          push_cast
          ring
        _ ≤ b ^ (N:ℝ) := Real.rpow_le_rpow_of_exponent_le hb hN
        _ = _ := Real.rpow_natCast _ _
    have hden := one_le_realPWIntervalWeight α s hs (x + t)
    have hr : realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t) ≤ b^N := by
      apply (div_le_iff₀ (by linarith)).2
      exact hw.trans (le_mul_of_one_le_right (pow_nonneg (by linarith) _) hden)
    have hbN := one_le_pow₀ hb (n := N)
    calc
      _ ≤ Real.sqrt (b^N) := Real.sqrt_le_sqrt hr
      _ ≤ b^N := by nlinarith [Real.sq_sqrt (show 0 ≤ b^N by linarith), sq_nonneg (Real.sqrt (b^N)-1)]
      _ = (2:ℝ)^N * (1+|t|)^N := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- A fixed positive dilation has bounded weight distortion on the positive tail. -/
theorem realPWIntervalWeight_dilation_ratio {α s a : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (h : 0 < a) : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      realPWIntervalWeight α s x / realPWIntervalWeight α s (a*x) ≤ C := by
  let D := 2*(1 + Real.log a ^ 2)
  refine ⟨(a ^ (2*α))⁻¹ * D ^ (s/2), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (1/a))] with x hx
  have hx1 := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ a*x := by
    simpa [mul_comm] using (div_le_iff₀ h).mp ((le_max_right _ _).trans hx)
  have hlog := Real.log_mul h.ne' hx0.ne'
  have hpoly : 1 + Real.log x ^ 2 ≤ D * (1 + Real.log (a*x) ^ 2) := by
    dsimp [D]
    nlinarith [sq_nonneg (Real.log (a*x) + Real.log a),
      sq_nonneg (Real.log a * Real.log (a*x)),
      show Real.log x ^ 2 = (Real.log (a*x) - Real.log a)^2 by rw [hlog]; ring]
  have hb := Real.rpow_le_rpow (by positivity) hpoly (show 0 ≤ s/2 by positivity)
  rw [Real.mul_rpow (by dsimp [D]; positivity) (by positivity)] at hb
  rw [weight_at_large ha hx1, weight_at_large ha hy, Real.mul_rpow h.le hx0.le]
  apply (div_le_iff₀ (by positivity)).2
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le _)
    _ = _ := by field_simp [ne_of_gt (Real.rpow_pos_of_pos h (2*α))]

/-- A Schwartz kernel times the square-root translation distortion has an explicit
square-integrable envelope, independent of the packet center. -/
theorem schwartz_realPWIntervalWeight_L2_envelope {α s : ℝ}
    (h : ∃ C : ℝ, ∃ N : ℕ, ∀ x : ℝ, 4 ≤ x → ∀ t : ℝ,
      Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤ C*(1+|t|)^N)
    (K : 𝓢(ℝ, ℂ)) : ∃ B : ℝ, MemLp (fun t : ℝ ↦ B*(1+|t|)⁻¹) 2 volume ∧
      ∀ x : ℝ, 4 ≤ x → ∀ t : ℝ, ‖K t‖ *
        Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤ B*(1+|t|)⁻¹ := by
  obtain ⟨C,N,hC⟩ := h
  let S := (Finset.Iic ((N + 1, 0) : ℕ × ℕ)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) K
  let B := |C| * (2^(N+1)*S)
  let u (t : ℝ) := (1 + ‖t‖)⁻¹
  have hu : MemLp u 2 volume := by
    apply (integrable_norm_rpow_iff (by dsimp [u]; fun_prop) (by norm_num) (by norm_num)).mp
    have hn (t : ℝ) : ‖u t‖ = (1 + ‖t‖)⁻¹ := Real.norm_of_nonneg (by dsimp [u]; positivity)
    simpa only [hn, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := (2 : ENNReal).toReal) (by simp))
  refine ⟨B, ?_, fun x hx t ↦ ?_⟩
  · change MemLp (B • u) 2 volume
    exact hu.const_smul B
  have hk := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N+1, 0))
    (le_refl (N+1)) (le_refl 0) K t
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hk
  change (1+|t|)^(N+1) * ‖K t‖ ≤ 2^(N+1)*S at hk
  have hc := (hC x hx t).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  apply (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ = |C| * ((1+|t|)^(N+1) * ‖K t‖) := by rw [pow_succ]; ring
    _ ≤ B := mul_le_mul_of_nonneg_left hk (abs_nonneg C)

end RiemannMasullo.Isolated
