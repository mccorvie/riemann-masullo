module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Discrete fourth-power logarithmic sampling -/

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace RiemannMasullo

private theorem logGrid_cell_variation {f : ℝ → ℝ} {p M a t : ℝ} {K : ℝ≥0}
    (hp : 1 ≤ p) (hf : LipschitzWith K f) (hM : ∀ u, |f u| ≤ M)
    (ha : 1 ≤ a) (hat : a ≤ t) (ht : t ≤ a + 1) :
    |t ^ p * f (4 * Real.log t) - a ^ p * f (4 * Real.log a)| ≤
      (M + 4 * (K : ℝ)) * ((a + 1) ^ p - a ^ p) := by
  have ha' : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ht' := ha'.trans_le hat
  have hb : 0 < a + 1 := by linarith
  have hab : a ≤ a + 1 := by linarith
  have hp' : 0 ≤ p := by linarith
  have hpa : a ^ (p - 1) * a = a ^ p := by
    rw [← Real.rpow_add_one ha'.ne', sub_add_cancel]
  have hpb : (a + 1) ^ (p - 1) * (a + 1) = (a + 1) ^ p := by
    rw [← Real.rpow_add_one hb.ne', sub_add_cancel]
  have inc := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow ha'.le hab (sub_nonneg.mpr hp)) hb.le
  rw [hpb] at inc
  have hstep : a ^ (p - 1) ≤ (a + 1) ^ p - a ^ p := by nlinarith only [inc, hpa]
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht' ha')
  rw [Real.log_div ht'.ne' ha'.ne'] at hlog
  have hlog' : a * (Real.log t - Real.log a) ≤ 1 := calc
    _ ≤ a * (t / a - 1) := mul_le_mul_of_nonneg_left hlog ha'.le
    _ = t - a := by field_simp
    _ ≤ 1 := by linarith
  have hosc : a ^ p * (Real.log t - Real.log a) ≤ (a + 1) ^ p - a ^ p := calc
    _ = a ^ (p - 1) * (a * (Real.log t - Real.log a)) := by rw [← hpa]; ring
    _ ≤ a ^ (p - 1) * 1 := mul_le_mul_of_nonneg_left hlog' (Real.rpow_nonneg ha'.le _)
    _ ≤ _ := by simpa using hstep
  have hf' := hf.dist_le_mul (4 * Real.log t) (4 * Real.log a)
  have hla := Real.log_le_log ha' hat
  simp only [Real.dist_eq, abs_of_nonneg (show 0 ≤ 4 * Real.log t - 4 * Real.log a by linarith)]
    at hf'
  have hdiff : 0 ≤ t ^ p - a ^ p := sub_nonneg.mpr (Real.rpow_le_rpow ha'.le hat hp')
  have hM' : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hweight := Real.rpow_le_rpow ht'.le ht hp'
  have hfirst := mul_le_mul_of_nonneg_left hf' (Real.rpow_nonneg ha'.le p)
  have hsecond := mul_le_mul_of_nonneg_left (hM (4 * Real.log t)) hdiff
  have hfirst' := mul_le_mul_of_nonneg_left hosc (show 0 ≤ 4 * (K : ℝ) by positivity)
  have hsecond' := mul_le_mul_of_nonneg_right (sub_le_sub_right hweight (a ^ p)) hM'
  calc
    _ = |a ^ p * (f (4 * Real.log t) - f (4 * Real.log a)) +
        (t ^ p - a ^ p) * f (4 * Real.log t)| := by congr 1; ring
    _ ≤ |a ^ p * (f (4 * Real.log t) - f (4 * Real.log a))| +
        |(t ^ p - a ^ p) * f (4 * Real.log t)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha'.le _), abs_of_nonneg hdiff]
      linarith only [hfirst, hsecond, hfirst', hsecond']

/-- For a bounded Lipschitz profile, the error when the sum at fourth-power logarithms is
replaced by its integral is at most a fixed constant times the last weight. -/
theorem abs_sum_sub_integral_fourthPowerLog {f : ℝ → ℝ} {p M : ℝ} {K : ℝ≥0}
    (hp : 1 ≤ p) (hf : LipschitzWith K f) (hM : ∀ u, |f u| ≤ M)
    (J : ℕ) (hJ : 0 < J) :
    |(∑ j ∈ Finset.range J, ((j : ℝ) + 1) ^ p * f (4 * Real.log ((j : ℝ) + 1))) -
        ∫ t in (1 : ℝ)..(J : ℝ), t ^ p * f (4 * Real.log t)| ≤
      (2 * M + 4 * (K : ℝ)) * (J : ℝ) ^ p := by
  let W (t : ℝ) := t ^ p * f (4 * Real.log t)
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable W volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht' : t ≠ 0 := (lt_of_lt_of_le zero_lt_one (ha.trans ht.1)).ne'
    exact ((Real.continuousAt_rpow_const t p (.inl ht')).mul
      (hf.continuous.continuousAt.comp
        (continuousAt_const.mul (Real.continuousAt_log ht')))).continuousWithinAt
  have hcell (a : ℝ) (ha : 1 ≤ a) :
      |W a - ∫ t in a..a + 1, W t| ≤ (M + 4 * (K : ℝ)) * ((a + 1) ^ p - a ^ p) := by
    have hab : a ≤ a + 1 := by linarith
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + 1)
      (f := fun t ↦ W t - W a) (C := (M + 4 * (K : ℝ)) * ((a + 1) ^ p - a ^ p)) (by
        intro t ht
        rw [Set.uIoc_of_le hab] at ht
        simpa only [Real.norm_eq_abs, W] using logGrid_cell_variation hp hf hM ha ht.1.le ht.2)
    rw [intervalIntegral.integral_sub (hint ha hab) intervalIntegrable_const,
      intervalIntegral.integral_const] at h
    simp only [Real.norm_eq_abs, add_sub_cancel_left, one_smul, abs_one, mul_one] at h
    exact (abs_sub_comm _ _).trans_le h
  have add_error (s i w v : ℝ) : |s + w - (i + v)| ≤ |s - i| + |w - v| := by
    rw [show s + w - (i + v) = (s - i) + (w - v) by ring]
    exact abs_add_le _ _
  have hprefix (n : ℕ) :
      |(∑ j ∈ Finset.range n, W ((j : ℝ) + 1)) - ∫ t in (1 : ℝ)..(n : ℝ) + 1, W t| ≤
        (M + 4 * (K : ℝ)) * (((n : ℝ) + 1) ^ p - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [Finset.sum_range_succ, Nat.cast_succ]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hn) (hint hn (by linarith))]
      exact (add_error _ _ _ _).trans <| (add_le_add ih (hcell _ hn)).trans_eq (by ring)
  cases J with
  | zero => exact (Nat.not_lt_zero _ hJ).elim
  | succ n =>
    change |(∑ j ∈ Finset.range (n + 1), W ((j : ℝ) + 1)) -
      ∫ t in (1 : ℝ)..((n + 1 : ℕ) : ℝ), W t| ≤ _
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have hlast : |W ((n : ℝ) + 1)| ≤ M * ((n : ℝ) + 1) ^ p := by
      dsimp [W]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _) (Real.rpow_nonneg (by positivity) _)
    have hM' := (abs_nonneg _).trans (hM 0)
    have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
    have hcombine := add_error (∑ j ∈ Finset.range n, W ((j : ℝ) + 1))
      (∫ t in (1 : ℝ)..(n : ℝ) + 1, W t) (W ((n : ℝ) + 1)) 0
    simp only [add_zero, sub_zero] at hcombine
    exact hcombine.trans <| (add_le_add (hprefix n) hlast).trans (by linarith)

end RiemannMasullo

