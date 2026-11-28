module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothMass

/-! # A lower bound on an inversion-symmetric spatial floor -/

public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

/-- A top radius profile supported below L and equal to one at 1/L forces
the upper endpoint of an inversion-symmetric spatial floor to be at least 1/L. -/
theorem inv_topRadius_le_floor_of_symmetric_profiles
    (σTop σFloor : Measure ℝ) [IsProbabilityMeasure σTop]
    {a L b A₀ : ℝ} (hL : 1 ≤ L) (ha : L⁻¹ ≤ a)
    (hTop : σTop (Icc a L)ᶜ = 0) (hFloor : σFloor (Icc b A₀)ᶜ = 0)
    (hInv : ∀ t : ℝ, 0 < t →
      Isolated.avgCutoff σTop t - Isolated.avgCutoff σFloor t =
      Isolated.avgCutoff σTop t⁻¹ - Isolated.avgCutoff σFloor t⁻¹) :
    L⁻¹ ≤ A₀ := by
  by_contra h
  have hA : A₀ < L⁻¹ := lt_of_not_ge h
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨t, htl, htu⟩ := exists_between (max_lt hA (inv_pos.mpr hL₀))
  have ht₀ : 0 < t := (le_max_right A₀ 0).trans_lt htl
  have htA : A₀ < t := (le_max_left A₀ 0).trans_lt htl
  have hLt : L < t⁻¹ := (lt_inv_comm₀ ht₀ hL₀).mp htu
  have hIL : L⁻¹ ≤ L := ((inv_le_one₀ hL₀).mpr hL).trans hL
  have hAt : A₀ < t⁻¹ := (hA.trans_le hIL).trans hLt
  have hs := hInv t ht₀
  rw [Isolated.avgCutoff_eq_one σTop hTop (htu.le.trans ha),
    Isolated.avgCutoff_eq_zero σFloor hFloor htA,
    Isolated.avgCutoff_eq_zero σTop hTop hLt,
    Isolated.avgCutoff_eq_zero σFloor hFloor hAt] at hs
  norm_num at hs

/-- Such a lower bound excludes vanishing floor product on the unrestricted
joint upper-radius filter. -/
theorem not_tendsto_floorProduct_zero_of_eventually_inv_le
    (floor : ℝ × ℝ → ℝ)
    (hFloor : ∀ᶠ p : ℝ × ℝ in atTop ×ˢ atTop, p.1⁻¹ ≤ floor p) :
    ¬ Tendsto (fun p : ℝ × ℝ ↦ floor p * p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  intro h
  have hdiag : Tendsto (fun x : ℝ ↦ (x, x)) atTop (atTop ×ˢ atTop) :=
    tendsto_prod_iff'.2 ⟨tendsto_id, tendsto_id⟩
  have hge : ∀ᶠ x : ℝ in atTop, 1 ≤ floor (x, x) * x := by
    filter_upwards [hdiag.eventually hFloor, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    change x⁻¹ ≤ floor (x, x) at hx
    have hmul := mul_le_mul_of_nonneg_right hx hx0.le
    rwa [inv_mul_cancel₀ hx0.ne'] at hmul
  have hlt : ∀ᶠ x : ℝ in atTop, floor (x, x) * x < 1 :=
    (h.comp hdiag).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨x, hx, hy⟩ := (hge.and hlt).exists
  exact not_lt_of_ge hx hy

end RiemannMasullo
