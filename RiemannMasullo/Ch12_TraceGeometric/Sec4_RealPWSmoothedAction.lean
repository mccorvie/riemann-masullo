module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWWeightEstimates
public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerMask

/-! # The actual smoothed dilation on the weighted real Fourier band -/

public noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace RiemannMasullo.Isolated

/-- A narrow Fourier-smoothed cutoff really acts pointwise on the entire weighted
band after dilation. Neither Fourier projection nor extra decay of the band vector
is needed. -/
theorem exists_realPW_smoothIntervalMask_mul_dilate_evaluation
    {Y α s a c : ℝ} (hY : 0 < Y) (hs : 0 ≤ s) (ha : 0 < a) (hc : 0 ≤ c)
    (hmargin : c ≤ (1 - a) * Y)
    (η : 𝓢(ℝ, ℂ)) (heven : Function.Even (η : ℝ → ℂ))
    (hη : Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c)
    (L : ℝ) (b : ℂ)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    ∃ q : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs), ∀ x : ℝ,
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x q =
        b * smoothIntervalMask η L x *
          RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) (a * x) f := by
  let μ := realPWIntervalMeasure α s
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let v (x : ℝ) := RealPWBand.evaluation Y hμ x f
  let u (x : ℝ) := b * smoothIntervalMask η L x * v (a * x)
  have hv : Continuous v := (RealPWBand.contDiff_evaluation Y hμ f 0).continuous
  have hu : Continuous u := (continuous_const.mul (continuous_smoothIntervalMask η L)).mul
    (hv.comp (continuous_const.mul continuous_id))
  have he : Function.Even u := by
    intro x
    dsimp only [u, v]
    rw [mul_neg, smoothIntervalMask_even η heven L x, RealPWBand.evaluation_even]
  have hvLp : MemLp v 2 μ := (memLp_congr_ae
    (RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) f)).2
      (Lp.memLp f.val)
  have hd : MemLp (fun x ↦ v (a * x)) 2 μ := memLp_realPWIntervalMeasure_dilation hs ha hvLp
  let C : ℝ := ‖b‖ * ∫ t, ‖η t‖
  have hm : MemLp (fun x ↦ C * ‖v (a * x)‖) 2 μ := by
    change MemLp (C • (fun x ↦ ‖v (a * x)‖)) 2 μ
    exact hd.norm.const_smul C
  have huLp : MemLp u 2 μ := hm.mono' hu.aestronglyMeasurable <| ae_of_all _ fun x ↦ by
    change ‖b * smoothIntervalMask η L x * v (a * x)‖ ≤ C * ‖v (a * x)‖
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_smoothIntervalMask_le η.integrable L x) (norm_nonneg b))
      (norm_nonneg _)
  have hF := RealPWBand.fourier_smoothIntervalMask_mul_dilate_evaluation_zero_off
    hY ha.le hc hmargin hμ f η hη L b (huLp.mono_measure hμ)
  obtain ⟨q, hq⟩ := RealPWBand.exists_evaluation_eq_of_band Y hμ hu he huLp hF
  exact ⟨q, congrFun hq⟩

end RiemannMasullo.Isolated
