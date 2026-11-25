module

public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The integral-test error for a logarithmically weighted inverse-square series -/

public section

open Filter MeasureTheory Set Topology

namespace RiemannMasullo

private theorem sum_log_div_sq_tail_le (N L : ℕ) (hN : 2 ≤ N) :
    ∑ i ∈ Finset.range L, Real.log ((N : ℝ) + (i + 1 : ℕ)) / ((N : ℝ) + (i + 1 : ℕ)) ^ 2 ≤
      (1 + Real.log N) / N := by
  let f (x : ℝ) := Real.log x / x ^ 2
  let F (x : ℝ) := -(1 + Real.log x) / x
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have he : Real.exp (2 : ℝ)⁻¹ ≤ N := by
    apply le_trans _ hN'
    rw [← Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hab : (N : ℝ) ≤ N + L := le_add_of_nonneg_right (Nat.cast_nonneg L)
  have ha : AntitoneOn f (Icc (N : ℝ) (N + L)) := by
    have h := (Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 2)).mono
      (show Icc (N : ℝ) (N + L) ⊆ Ici (Real.exp (2 : ℝ)⁻¹) from fun _ hx ↦ he.trans hx.1)
    simpa [f, Real.rpow_two] using h
  have hpos {x : ℝ} (hx : x ∈ uIcc (N : ℝ) (N + L)) : 0 < x := by
    rw [uIcc_of_le hab] at hx
    linarith [hx.1]
  have hder {x : ℝ} (hx : 0 < x) : HasDerivAt F (f x) x := by
    conv in f x => dsimp [f]
    dsimp [F]
    convert (((hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_log hx.ne')).neg.div
      (hasDerivAt_id x) hx.ne') using 1 <;> first | rfl | (dsimp; field_simp [hx.ne']; ring)
  have hc : ContinuousOn f (uIcc (N : ℝ) (N + L)) := by
    intro x hx
    exact ((Real.continuousAt_log (hpos hx).ne').div (continuousAt_id.pow 2)
      (pow_ne_zero _ (hpos hx).ne')).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ hder (hpos hx))
    hc.intervalIntegrable
  have hi := ha.sum_le_integral
  change _ ≤ ∫ x in (N : ℝ)..N + L, f x at hi
  rw [hint] at hi
  have hn : 0 ≤ 1 + Real.log ((N : ℝ) + L) := by
    have hx : 1 ≤ (N : ℝ) + L := by linarith
    linarith [Real.log_nonneg hx]
  have hF : F ((N : ℝ) + L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn) (by positivity)
  change _ ≤ _ - F (N : ℝ) at hi
  calc
    _ ≤ F ((N : ℝ) + L) - F (N : ℝ) := hi
    _ ≤ -F (N : ℝ) := by linarith
    _ = _ := by dsimp [F]; ring

/-- Truncating after index `N` costs at most the integral of `D log x / x²` from `N`
to infinity. Only the coefficient bound at indices greater than `N` is required. -/
theorem abs_sub_sum_range_le_log_div_sq_tail {f : ℕ → ℝ} {s D : ℝ} (h : HasSum f s)
    (hD : 0 ≤ D) (N : ℕ) (hN : 2 ≤ N)
    (hf : ∀ m, N < m → |f m| ≤ D * (Real.log m / (m : ℝ)^2)) :
    |s - ∑ m ∈ Finset.range (N + 1), f m| ≤ D * ((1 + Real.log N) / N) := by
  let p := ∑ m ∈ Finset.range (N + 1), f m
  let t (M : ℕ) := ∑ i ∈ Finset.range M, f (N + 1 + i)
  have hn : Tendsto (fun M : ℕ ↦ N + 1 + M) atTop atTop :=
    tendsto_atTop_mono (fun M ↦ Nat.le_add_left M (N + 1)) tendsto_id
  have ht : Tendsto t atTop (𝓝 (s - p)) := by
    simpa [t, p, Function.comp_def, Finset.sum_range_add] using
      (h.tendsto_sum_nat.comp hn).sub_const p
  apply le_of_tendsto ht.abs
  apply Eventually.of_forall
  intro M
  calc
    |t M| ≤ ∑ i ∈ Finset.range M, |f (N + 1 + i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range M, D * (Real.log ((N : ℝ) + (i + 1 : ℕ)) /
        ((N : ℝ) + (i + 1 : ℕ))^2) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [Nat.cast_add, Nat.cast_one, add_right_comm, add_comm, add_left_comm] using
        hf (N + 1 + i) (by omega)
    _ = D * _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_log_div_sq_tail_le N M hN) hD

/-- The explicit tail radius of a fixed field tends to zero along natural cutoffs. -/
theorem tendsto_log_div_sq_tail_radius (D : ℝ) :
    Tendsto (fun N : ℕ ↦ D * ((1 + Real.log N) / N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0))
  have h2 : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simpa [add_div] using ((h1.add h2).comp tendsto_natCast_atTop_atTop).const_mul D

end RiemannMasullo
