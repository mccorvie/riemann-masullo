module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

namespace RiemannMasullo.Selberg

open Filter

/-- Card 45. For any a, ε > 0 and any prescribed threshold, some integer N above the threshold and
at least two gives 0 < 1/(a log N) ≤ 1/2 and 1/(a log N) < ε.
Titchmarsh, §§10.15, 10.22, pp. 274, 279. -/
theorem choose_window (a ε : ℝ) (ha : 0 < a) (he : 0 < ε) (N₀ : ℕ) :
    ∃ N ≥ max 2 N₀,
      let h := (a*Real.log N)⁻¹
      0 < h ∧ h ≤ 1/2 ∧ h < ε := by
  have hden : Tendsto (fun N : ℕ ↦ a * Real.log N) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have hsmall := hden.inv_tendsto_atTop
  apply Eventually.exists (f := atTop)
  filter_upwards [eventually_ge_atTop (max 2 N₀), hden.eventually_gt_atTop 0,
    hsmall.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num),
    hsmall.eventually_lt_const he] with N hN hpos hhalf hε
  exact ⟨hN, inv_pos.mpr hpos, hhalf, hε⟩

end RiemannMasullo.Selberg
