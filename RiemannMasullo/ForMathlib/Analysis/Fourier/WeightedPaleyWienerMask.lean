module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerBand
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Compact spatial masks for real Paley–Wiener bands -/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace RiemannMasullo.RealPWBand

/-- A compact mask forces the product to vanish on a ray. If the product were
analytic, the identity theorem would make it zero everywhere. On an open set
where the mask is nonzero, this would force the dilated analytic input to vanish. -/
theorem not_analyticOnNhd_compactMask_mul_dilate {m f : ℝ → ℂ} {a : ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) (hm₀ : ∃ x, m x ≠ 0)
    (hf : AnalyticOnNhd ℝ f univ) (hf₀ : ∃ x, f x ≠ 0) (ha : a ≠ 0) :
    ¬ AnalyticOnNhd ℝ (fun x ↦ m x * f (a * x)) univ := by
  intro hp
  obtain ⟨B, hB⟩ := hc.isCompact.bddAbove
  have hz : AnalyticOnNhd ℝ (fun _ : ℝ ↦ (0 : ℂ)) univ := fun _ _ ↦ analyticAt_const
  have hzero := hp.eq_of_eventuallyEq hz (z₀ := B + 1) (by
    filter_upwards [lt_mem_nhds (show B < B + 1 by linarith)] with x hx
    have hout : x ∉ tsupport m := fun h ↦ hx.not_ge (hB h)
    simp [image_eq_zero_of_notMem_tsupport hout])
  obtain ⟨u, hu⟩ := hm₀
  have hd : AnalyticOnNhd ℝ (fun x ↦ f (a * x)) univ := fun x _ ↦
    (hf (a * x) (mem_univ _)).comp (analyticAt_const.mul analyticAt_id)
  have hdzero := hd.eq_of_eventuallyEq hz (z₀ := u) (by
    filter_upwards [hm.continuousAt.eventually_ne hu] with x hx
    exact (mul_eq_zero.mp (congrFun hzero x)).resolve_left hx)
  obtain ⟨v, hv⟩ := hf₀
  exact hv (by simpa only [mul_div_cancel₀ v ha] using congrFun hdzero (v / a))

/-- An unprojected compactly masked dilation of a nonzero band representative
cannot be the representative of another band vector. -/
theorem evaluation_ne_compactMask_mul_dilate {Y Z : ℝ} {μ : Measure ℝ}
    {hμ : volume ≤ μ} (f : space Y hμ) (g : space Z hμ) {m : ℝ → ℂ} {a : ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) (hm₀ : ∃ x, m x ≠ 0)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hf₀ : ∃ x, evaluation Y hμ x f ≠ 0) (ha : a ≠ 0) :
    (fun x ↦ evaluation Z hμ x g) ≠ (fun x ↦ m x * evaluation Y hμ (a * x) f) := by
  intro he
  exact not_analyticOnNhd_compactMask_mul_dilate hm hc hm₀
    (analyticOnNhd_evaluation Y hY hμ f) hf₀ ha (he ▸ analyticOnNhd_evaluation Z hZ hμ g)

end RiemannMasullo.RealPWBand
