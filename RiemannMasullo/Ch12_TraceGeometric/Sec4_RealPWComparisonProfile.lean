module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Real Paley–Wiener comparison profile

For Theorem 12.4.1.1, pp. 514–517, the rational unweighted real model
regularizes the test by subtracting its value at the identity times the
comparison profile `g ^ (-3/2)` supported on `[1/2, 2]`. Multiplying the
profile by the trace density gives an additive finite part of zero. This
fixes the constant in the comparison with Proposition B.4.3.2(1), p. 619.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.Isolated

private theorem integral_realComparison_left {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) :
    (∫ x in a..b, (x * (1 - x ^ 2))⁻¹) =
      (Real.log b - (1 / 2) * Real.log (1 - b ^ 2)) -
        (Real.log a - (1 / 2) * Real.log (1 - a ^ 2)) := by
  have hbounds (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x ∧ 0 < 1 - x ^ 2 := by
    rw [uIcc_of_le hab] at hx
    have hpos : 0 < x := ha.trans_le hx.1
    have hlt : x < 1 := hx.2.trans_lt hb
    refine ⟨hpos, ?_⟩
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_pos (sub_pos.mpr hlt) (by linarith)
  let p : ℝ → ℝ := fun x ↦ Real.log x - (1 / 2) * Real.log (1 - x ^ 2)
  have hp (x : ℝ) (hx : x ∈ uIcc a b) : HasDerivAt p (x * (1 - x ^ 2))⁻¹ x := by
    obtain ⟨hxpos, hsq⟩ := hbounds x hx
    have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub 1
    have h := (Real.hasDerivAt_log hxpos.ne').sub
      ((Real.hasDerivAt_log hsq.ne').comp x hsub |>.const_mul (1 / 2))
    convert h using 1 <;> first
    | rfl
    | field_simp [hxpos.ne', hsq.ne']; ring
  have hc : Continuous (fun x : ℝ ↦ x * (1 - x ^ 2)) := by fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hp
    (hc.continuousOn.inv₀ (fun x hx ↦
      (mul_pos (hbounds x hx).1 (hbounds x hx).2).ne')).intervalIntegrable

private theorem integral_realComparison_right {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, (x ^ 2 - 1)⁻¹) =
      (1 / 2) * (Real.log (b - 1) - Real.log (b + 1)) -
        (1 / 2) * (Real.log (a - 1) - Real.log (a + 1)) := by
  have hbounds (x : ℝ) (hx : x ∈ uIcc a b) :
      0 < x - 1 ∧ 0 < x + 1 ∧ 0 < x ^ 2 - 1 := by
    rw [uIcc_of_le hab] at hx
    have hlt : 1 < x := ha.trans_le hx.1
    have hneg : 0 < x - 1 := sub_pos.mpr hlt
    have hpos : 0 < x + 1 := by linarith
    refine ⟨hneg, hpos, ?_⟩
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact mul_pos hneg hpos
  let p : ℝ → ℝ := fun x ↦ (1 / 2) * (Real.log (x - 1) - Real.log (x + 1))
  have hp (x : ℝ) (hx : x ∈ uIcc a b) : HasDerivAt p (x ^ 2 - 1)⁻¹ x := by
    obtain ⟨hneg, hpos, hsq⟩ := hbounds x hx
    have h₁ := (Real.hasDerivAt_log hneg.ne').comp x ((hasDerivAt_id x).sub_const 1)
    have h₂ := (Real.hasDerivAt_log hpos.ne').comp x ((hasDerivAt_id x).add_const 1)
    convert (h₁.sub h₂).const_mul (1 / 2) using 1 <;> first
    | rfl
    | field_simp [hneg.ne', hpos.ne', hsq.ne']; ring
  have hc : Continuous (fun x : ℝ ↦ x ^ 2 - 1) := by fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hp
    (hc.continuousOn.inv₀ (fun x hx ↦ (hbounds x hx).2.2.ne')).intervalIntegrable

/-- Paper: (12.4.1.1) and (12.4.1.3), pp. 514–515. The comparison profile
multiplied by the trace density has the two rational integrands displayed here.
Their integrals with a symmetric cutoff at one have the stated logarithmic sum. -/
theorem realComparisonProfile_cutoff {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (∫ g in (1 / 2 : ℝ)..(1 - ε), (g * (1 - g ^ 2))⁻¹) +
      (∫ g in (1 + ε)..(2 : ℝ), (g ^ 2 - 1)⁻¹) + Real.log ε =
        Real.log (1 - ε) + (1 / 2) * Real.log ((2 + ε) / (2 - ε)) := by
  have hplus : 2 + ε ≠ 0 := by linarith
  have hminus : 2 - ε ≠ 0 := by linarith
  rw [integral_realComparison_left (by norm_num) (by linarith) (by linarith),
    integral_realComparison_right (by linarith) (by linarith),
    show 1 - (1 - ε) ^ 2 = ε * (2 - ε) by ring,
    Real.log_mul hε.ne' hminus,
    show (1 : ℝ) - (1 / 2) ^ 2 = 3 * (1 / 2) ^ 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
    show 1 + ε - 1 = ε by ring, show 1 + ε + 1 = 2 + ε by ring,
    Real.log_div hplus hminus]
  norm_num
  ring

/-- The comparison profile has zero finite part for the symmetric additive cutoff
of Proposition B.4.3.2(1), p. 619. -/
theorem realComparisonProfile_finitePart :
    Tendsto (fun ε : ℝ ↦
      (∫ g in (1 / 2 : ℝ)..(1 - ε), (g * (1 - g ^ 2))⁻¹) +
        (∫ g in (1 + ε)..(2 : ℝ), (g ^ 2 - 1)⁻¹) + Real.log ε)
      (𝓝[>] 0) (𝓝 0) := by
  let f : ℝ → ℝ := fun ε ↦ Real.log (1 - ε) + (1 / 2) * Real.log ((2 + ε) / (2 - ε))
  have hleft : ContinuousAt (fun ε : ℝ ↦ 1 - ε) 0 := by fun_prop
  have hright : ContinuousAt (fun ε : ℝ ↦ (2 + ε) / (2 - ε)) 0 := by
    have hnum : ContinuousAt (fun ε : ℝ ↦ 2 + ε) 0 := by fun_prop
    have hden : ContinuousAt (fun ε : ℝ ↦ 2 - ε) 0 := by fun_prop
    exact hnum.div hden (by norm_num)
  have h₁ : ContinuousAt (fun ε : ℝ ↦ Real.log (1 - ε)) 0 :=
    (Real.continuousAt_log (show (1 : ℝ) - 0 ≠ 0 by norm_num)).comp hleft
  have h₂ : ContinuousAt (fun ε : ℝ ↦ Real.log ((2 + ε) / (2 - ε))) 0 :=
    (Real.continuousAt_log (show ((2 : ℝ) + 0) / (2 - 0) ≠ 0 by norm_num)).comp
      (f := fun ε : ℝ ↦ (2 + ε) / (2 - ε)) hright
  have hc : ContinuousAt (fun _ : ℝ ↦ (1 / 2 : ℝ)) 0 := continuousAt_const
  have hf : ContinuousAt f 0 := h₁.add (hc.mul h₂)
  have hfzero : f 0 = 0 := by norm_num [f]
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  rw [hfzero] at hlim
  have hsmall : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by norm_num)
  apply hlim.congr'
  filter_upwards [hsmall] with ε hε
  exact (realComparisonProfile_cutoff hε.1 hε.2).symm

end RiemannMasullo.Isolated
