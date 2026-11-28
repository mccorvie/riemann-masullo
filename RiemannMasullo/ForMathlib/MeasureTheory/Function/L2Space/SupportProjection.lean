module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder

/-! # Orthogonal projection onto an almost-everywhere support condition -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RiemannMasullo

variable {X : Type*} [MeasurableSpace X]

private theorem memLp_indicator_one_top
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    MemLp (s.indicator (fun _ : X ↦ (1 : ℂ))) ∞ μ := by
  refine memLp_top_of_bound (measurable_const.indicator hs).aestronglyMeasurable 1 ?_
  exact ae_of_all _ fun x ↦ by by_cases hx : x ∈ s <;> simp [hx]

/-- Multiplication by the indicator of a measurable set on complex L². -/
def l2IndicatorMultiplier (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 ((memLp_indicator_one_top μ s hs).toLp _)

/-- The multiplier agrees almost everywhere with pointwise truncation. -/
theorem l2IndicatorMultiplier_ae (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    (l2IndicatorMultiplier μ s hs f : X → ℂ) =ᵐ[μ] s.indicator (f : X → ℂ) := by
  let e : X → ℂ := s.indicator (fun _ ↦ (1 : ℂ))
  let z : Lp ℂ ∞ μ := (memLp_indicator_one_top μ s hs).toLp e
  have hz : (z : X → ℂ) =ᵐ[μ] e := (memLp_indicator_one_top μ s hs).coeFn_toLp
  have hprod : (l2IndicatorMultiplier μ s hs f : X → ℂ) =ᵐ[μ] fun x ↦ z x * f x :=
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) z f
  filter_upwards [hprod, hz] with x hprod' hz'
  rw [hprod', hz']
  by_cases hx : x ∈ s <;> simp [e, hx]

/-- The closed submodule of classes that vanish almost everywhere off `s`. -/
def l2AESupported (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ClosedSubmodule ℂ (Lp ℂ 2 μ) where
  toSubmodule := (l2IndicatorMultiplier μ sᶜ hs.compl).ker
  isClosed' := (l2IndicatorMultiplier μ sᶜ hs.compl).isClosed_ker

/-- Membership is exactly the almost-everywhere vanishing condition. -/
theorem mem_l2AESupported_iff (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    f ∈ l2AESupported μ s hs ↔ ∀ᵐ x ∂μ, x ∉ s → f x = 0 := by
  change l2IndicatorMultiplier μ sᶜ hs.compl f = 0 ↔ _
  have hzero : ((0 : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] 0 := Lp.coeFn_zero ℂ 2 μ
  have hrow := l2IndicatorMultiplier_ae μ sᶜ hs.compl f
  constructor
  · intro hf
    have h := hrow.symm.trans (show (l2IndicatorMultiplier μ sᶜ hs.compl f : X → ℂ)
      =ᵐ[μ] 0 by rw [hf]; exact hzero)
    filter_upwards [h] with x hx hxs
    simpa only [indicator_of_mem (show x ∈ sᶜ from hxs), Pi.zero_apply] using hx
  · intro hf
    apply Lp.ext
    refine (hrow.trans ?_).trans hzero.symm
    filter_upwards [hf] with x hx
    change sᶜ.indicator (f : X → ℂ) x = 0
    by_cases hxs : x ∈ sᶜ
    · rw [indicator_of_mem hxs, hx hxs]
    · rw [indicator_of_notMem hxs]

/-- The support condition can also be read in the restricted measure. -/
theorem mem_l2AESupported_iff_restrict_compl (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    f ∈ l2AESupported μ s hs ↔ (f : X → ℂ) =ᵐ[μ.restrict sᶜ] 0 := by
  rw [mem_l2AESupported_iff]
  exact (ae_restrict_iff' (μ := μ) (p := fun x ↦ f x = 0) hs.compl).symm

/-- Truncation to a measurable set is the orthogonal projection onto the
closed submodule of classes supported there almost everywhere. -/
theorem starProjection_l2AESupported (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    (l2AESupported μ s hs).toSubmodule.starProjection = l2IndicatorMultiplier μ s hs := by
  apply ContinuousLinearMap.ext
  intro f
  let P := l2IndicatorMultiplier μ s hs
  have hrow : (P f : X → ℂ) =ᵐ[μ] s.indicator (f : X → ℂ) :=
    l2IndicatorMultiplier_ae μ s hs f
  apply (l2AESupported μ s hs).toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_l2AESupported_iff μ s hs (P f)).2
    filter_upwards [hrow] with x hx hxs
    rw [hx, indicator_of_notMem hxs]
  · intro w hw
    have hwzero := (mem_l2AESupported_iff μ s hs w).1 hw
    rw [L2.inner_def]
    calc
      _ = ∫ _ : X, (0 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub f (P f), hrow, hwzero] with x hsub hx hwx
        change (f - P f) x = f x - P f x at hsub
        by_cases hxs : x ∈ s
        · rw [hsub, hx, indicator_of_mem hxs, sub_self, inner_zero_left]
        · rw [hwx hxs, inner_zero_right]
      _ = 0 := by simp

theorem range_l2IndicatorMultiplier (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    (l2IndicatorMultiplier μ s hs).range = (l2AESupported μ s hs).toSubmodule := by
  rw [← starProjection_l2AESupported, Submodule.range_starProjection]

end RiemannMasullo
