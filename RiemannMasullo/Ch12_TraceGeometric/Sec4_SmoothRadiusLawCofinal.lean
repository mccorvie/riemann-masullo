module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothMass
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # Smooth radius laws and a cofinal path with vanishing inverse floor -/

public noncomputable section

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace RiemannMasullo

/-- A nondegenerate interval supports an atomless probability measure with
a smooth survival function. -/
theorem exists_smoothRadiusLaw {a L : ℝ} (haL : a < L) :
    ∃ σ : Measure ℝ, IsProbabilityMeasure σ ∧ NullSingletonClass σ ∧
      σ (Icc a L)ᶜ = 0 ∧ ContDiff ℝ (∞ : ℕ∞ω) (Isolated.avgCutoff σ) := by
  let F (x : ℝ) := Real.smoothTransition ((x - a) / (L - a))
  have hw : 0 < L - a := sub_pos.mpr haL
  have hF : ContDiff ℝ (∞ : ℕ∞ω) F :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hMono : Monotone F := by
    intro x y hxy
    exact Real.smoothTransition.monotone
      ((div_le_div_iff_of_pos_right hw).mpr (sub_le_sub_right hxy a))
  have hLow (x : ℝ) (hx : x ≤ a) : F x = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hw.le)
  have hHigh (x : ℝ) (hx : L ≤ x) : F x = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith))
  let G : StieltjesFunction ℝ :=
    ⟨F, hMono, fun _ ↦ hF.continuous.continuousAt.continuousWithinAt⟩
  have hBot : Tendsto G atBot (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot a] with x hx
    exact (hLow x hx).symm
  have hTop : Tendsto G atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop L] with x hx
    exact (hHigh x hx).symm
  have hLeft (x : ℝ) : leftLim G x = G x :=
    (show ContinuousWithinAt (G : ℝ → ℝ) (Iic x) x from
      hF.continuous.continuousAt.continuousWithinAt).leftLim_eq
  have hAtom : NullSingletonClass G.measure := ⟨fun x ↦ by
    rw [G.measure_singleton, hLeft, sub_self, ENNReal.ofReal_zero]⟩
  have hTailLow : G.measure (Iio a) = 0 := by
    rw [G.measure_Iio hBot, hLeft, show G a = 0 from hLow a le_rfl, sub_self,
      ENNReal.ofReal_zero]
  have hTailHigh : G.measure (Ioi L) = 0 := by
    rw [G.measure_Ioi hTop, show G L = 1 from hHigh L le_rfl, sub_self, ENNReal.ofReal_zero]
  have hSupp : G.measure (Icc a L)ᶜ = 0 := by
    rw [show (Icc a L : Set ℝ)ᶜ = Iio a ∪ Ioi L by
      ext x
      simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]]
    exact measure_union_null hTailLow hTailHigh
  have hEq : Isolated.avgCutoff G.measure = fun x ↦ 1 - F x := by
    funext x
    unfold Isolated.avgCutoff Measure.real
    rw [G.measure_Ici hTop, hLeft]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.smoothTransition.le_one _))
  refine ⟨G.measure, G.isProbabilityMeasure hBot hTop, hAtom, hSupp, ?_⟩
  rw [hEq]
  exact contDiff_const.sub hF

/-- A large spatial radius and its square root form a cofinal joint upper path. -/
theorem symmetricRadiusPath_cofinal :
    Tendsto (fun L : ℝ ↦ (L, Real.sqrt L)) atTop (atTop ×ˢ atTop) :=
  tendsto_prod_iff'.mpr ⟨tendsto_id, Real.tendsto_sqrt_atTop⟩

/-- Along the square-root frequency path, the maximum inverse-floor product
vanishes whenever the relative width goes to zero. -/
theorem tendsto_sqrt_mul_inverseRadius {ε : ℝ → ℝ}
    (hε : Tendsto (fun L ↦ ε L / L) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ ↦ (L - ε L)⁻¹ * Real.sqrt L) atTop (𝓝 0) := by
  have hUpper : Tendsto (fun L : ℝ ↦ 2 * (Real.sqrt L)⁻¹) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero] using Real.tendsto_sqrt_atTop.inv_tendsto_atTop.const_mul 2
  have hWidth : ∀ᶠ L : ℝ in atTop, 0 < L ∧ L / 2 ≤ L - ε L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hε.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with L hL hεL
    have hε' := (div_le_iff₀ hL).mp hεL
    exact ⟨hL, by linarith⟩
  refine squeeze_zero' (hWidth.mono fun L hL ↦ ?_) (hWidth.mono fun L hL ↦ ?_) hUpper
  · exact mul_nonneg (inv_nonneg.mpr ((half_pos hL.1).le.trans hL.2)) (Real.sqrt_nonneg _)
  · calc
      _ ≤ (L / 2)⁻¹ * Real.sqrt L :=
        mul_le_mul_of_nonneg_right (inv_anti₀ (half_pos hL.1) hL.2) (Real.sqrt_nonneg _)
      _ = _ := by
        nth_rw 1 [← Real.mul_self_sqrt hL.1.le]
        field_simp [(Real.sqrt_pos.mpr hL.1).ne']

end RiemannMasullo
