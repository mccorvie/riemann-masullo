module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatCosineTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCompactCosineWindow
import RiemannMasullo.ForMathlib.Probability.Distributions.Gaussian.Window

/-!
# Removing the heat, frequency, and spatial cutoffs in the real-even band

The compact test has a positive gap above dilation one. Mrshu's real-even
heat prescription in #7354 permits the heat variance times the logarithm
of the spatial-frequency scale to tend to zero.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal CompactlySupported Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

/-- Along any filter with `B h → 0`, `B L → ∞`, `τ → 0`, and `τ log (BL) → 0`,
the actual heat-sandwiched unpolarized trace converges to the real-even orbital
value of the compact dilation test. -/
theorem tendsto_hilbertTrace_logHeatSandwich_compactCosineTraceOperator
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0))
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto (fun i ↦ (τ i : ℝ)) l (𝓝 0))
    (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0)) :
    Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i)
      (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))) l
      (𝓝 (compactCosineOrbitalValue φ 1)) := by
  let F (i : ι) (z : ℝ) := hilbertTrace (nuclearAfterLogDilation z
    (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))
  let W := ∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar
  simp_rw [hilbertTrace_logHeatSandwich_eq_integral_dilationTrace]
  apply gaussianWindow_average_tendsto (fun i ↦ B i * L i) (fun i ↦ τ i + τ i) hBL
    (by simpa only [NNReal.coe_add, add_zero] using hτ.add hτ)
    (by simpa only [NNReal.coe_add, add_mul, add_zero] using hw.add hw) F _ (4 * W) 0
  · exact .of_forall fun i ↦ (continuous_hilbertTrace_nuclearAfterLogDilation _).aestronglyMeasurable
  · filter_upwards [hbox, hBL.eventually_gt_atTop 0] with i hi hR
    have hL : 0 ≤ L i := by
      by_contra! hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hi.2.le hn.le)) hR
    refine .of_forall fun z ↦ ?_
    dsimp only [F]
    rw [hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator]
    have he := norm_hilbertTrace_compactCosineShift_reducedBand_le φ
      (expRadialUnit z) hi.2.le hi.1 hL
    simp only [expRadialUnit_coe] at he
    simpa only [zero_mul, Real.exp_zero, mul_one,
      show (4 * W) * (B i * L i) = (4 * (B i * L i)) * W by ring] using he
  · intro ε hε
    dsimp only [F]
    simp_rw [hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator]
    exact eventually_hilbertTrace_compactCosineShift_log_reducedBand_near_zero
      φ hη hs hbox hBh hBL hε

end RiemannMasullo.FlatPolar
