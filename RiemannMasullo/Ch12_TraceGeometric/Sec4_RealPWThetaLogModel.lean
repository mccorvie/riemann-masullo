module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWThetaLevel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # The one-prime theta model of the rational real place, in the logarithmic coordinate

Paper: Theorem 12.4.1.1, pp. 514–517, for the real place of `ℚ` beside one finite prime `p`, at
fixed bandwidth and a fixed level.

A band vector `h` is an even function in the weighted space of (9.2.1.30) on the line whose
Fourier transform is supported in `[-Y, Y]`. Its theta sum is `x ↦ ∑ n ≥ 0, h (p ^ n x)` on the
positive half line. This file realises the theta sums of the band vectors that vanish at the
origin as a closed subspace of a weighted `L²` space on which evaluation at a point is
continuous and uniformly bounded. These are the hypotheses of
`sLocalTrace_projectedCutoffKernel` in `Sec4_Isolated`, which is applied there.

* The coordinate is `t = log x`, in which dilation by `p ^ n` is translation by `n log p`. As
  `x → 0` the theta sum oscillates with period `log p` in `log x` and has no limit, so its
  evaluation vectors cannot be continuous on the half line closed at `0`. On the logarithmic
  line that end is at infinity. `realPWLogMeasure α s` is the weighted measure in this
  coordinate.
* `realPWThetaMap` is the theta map from the band to the weighted space. For `α < 1 / 2` it is
  a norm-convergent series of translations (`summable_realPWLogShiftMap`), it is represented
  by the pointwise theta sum (`coeFn_realPWThetaMap`), and it is bounded below
  (`norm_le_norm_realPWThetaMap`).
* `realPWBandLevel` is the level, the band vectors that vanish at the origin, and
  `realPWThetaLevelRange` is its image. The image is complete
  (`completeSpace_realPWThetaLevelRange`) and has continuous, uniformly bounded evaluation
  vectors (`exists_realPWThetaLevelRange_evaluationVector`). Without the vanishing at the
  origin the theta sum grows like `|t|` as `t → -∞`.

Reconstruction: The paper does not state this model. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- The density of the real-place weighted space in the logarithmic coordinate `t = log x` on
the positive half line: the weight at `exp t` times the Jacobian `exp t`. -/
def realPWLogDensity (α s t : ℝ) : ℝ := realPWIntervalWeight α s (Real.exp t) * Real.exp t

theorem realPWLogDensity_eq (α s t : ℝ) :
    realPWLogDensity α s t = max (Real.exp (2 * α * t)) (Real.exp (-(2 * α * t))) *
      Real.exp (s / 2 * Real.log (1 + t ^ 2)) * Real.exp t := by
  simp only [realPWLogDensity, realPWIntervalWeight, abs_of_pos (Real.exp_pos t), Real.log_exp]

theorem continuous_realPWLogDensity (α s : ℝ) : Continuous (realPWLogDensity α s) := by
  have h : realPWLogDensity α s = fun t ↦ max (Real.exp (2 * α * t)) (Real.exp (-(2 * α * t))) *
      Real.exp (s / 2 * Real.log (1 + t ^ 2)) * Real.exp t := funext (realPWLogDensity_eq α s)
  rw [h]
  have hlog : Continuous fun t : ℝ ↦ Real.log (1 + t ^ 2) :=
    (by fun_prop : Continuous fun t : ℝ ↦ 1 + t ^ 2).log fun t ↦ by positivity
  exact (((Real.continuous_exp.comp (by fun_prop)).max (Real.continuous_exp.comp (by fun_prop))).mul
    (Real.continuous_exp.comp (continuous_const.mul hlog))).mul Real.continuous_exp

theorem realPWLogDensity_pos {α s : ℝ} (hs : 0 ≤ s) (t : ℝ) : 0 < realPWLogDensity α s t :=
  mul_pos (zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs _)) (Real.exp_pos t)

/-- The constant by which a shift by `ℓ` changes the logarithmic density. -/
def realPWLogShiftConstant (α s ℓ : ℝ) : ℝ :=
  Real.exp (2 * |α * ℓ|) * (1 + |ℓ| + ℓ ^ 2) ^ (s / 2) * Real.exp (-ℓ)

theorem realPWLogShiftConstant_nonneg (α s ℓ : ℝ) : 0 ≤ realPWLogShiftConstant α s ℓ := by
  unfold realPWLogShiftConstant
  positivity

/-- The logarithmic density at `u - ℓ` is at most the shift constant times the density at `u`. -/
theorem realPWLogDensity_sub_le {α s : ℝ} (hs : 0 ≤ s) (ℓ u : ℝ) :
    realPWLogDensity α s (u - ℓ) ≤ realPWLogShiftConstant α s ℓ * realPWLogDensity α s u := by
  have h := realPWIntervalWeight_le_dilation (α := α) hs (Real.exp_pos ℓ) (Real.exp (u - ℓ))
  rw [Real.log_exp, ← Real.exp_add, add_sub_cancel] at h
  have hexp : Real.exp (u - ℓ) = Real.exp (-ℓ) * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold realPWLogDensity realPWLogShiftConstant
  calc realPWIntervalWeight α s (Real.exp (u - ℓ)) * Real.exp (u - ℓ)
      ≤ (Real.exp (2 * |α * ℓ|) * (1 + |ℓ| + ℓ ^ 2) ^ (s / 2) *
          realPWIntervalWeight α s (Real.exp u)) * Real.exp (u - ℓ) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by rw [hexp]; ring

/-- The real-place weighted measure in the logarithmic coordinate. -/
def realPWLogMeasure (α s : ℝ) : Measure ℝ :=
  volume.withDensity fun t ↦ ENNReal.ofReal (realPWLogDensity α s t)

instance instIsLocallyFiniteMeasureRealPWLogMeasure (α s : ℝ) :
    IsLocallyFiniteMeasure (realPWLogMeasure α s) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (continuous_realPWLogDensity α s)

instance instSigmaFiniteRealPWLogMeasure (α s : ℝ) : SigmaFinite (realPWLogMeasure α s) := by
  unfold realPWLogMeasure
  infer_instance

/-- A shift of the logarithmic coordinate changes the weighted measure by at most the shift
constant. -/
theorem map_add_realPWLogMeasure_le {α s : ℝ} (hs : 0 ≤ s) (ℓ : ℝ) :
    Measure.map (· + ℓ) (realPWLogMeasure α s) ≤
      ENNReal.ofReal (realPWLogShiftConstant α s ℓ) • realPWLogMeasure α s := by
  let W := fun t ↦ ENNReal.ofReal (realPWLogDensity α s t)
  have hW : Measurable W := (continuous_realPWLogDensity α s).measurable.ennreal_ofReal
  have hadd : Measurable (· + ℓ : ℝ → ℝ) := measurable_add_const ℓ
  have hK := realPWLogShiftConstant_nonneg α s ℓ
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply hadd hS, smul_apply, realPWLogMeasure,
    withDensity_apply _ (hadd hS), withDensity_apply _ hS]
  change (∫⁻ t in (· + ℓ) ⁻¹' S, W t) ≤ ENNReal.ofReal (realPWLogShiftConstant α s ℓ) • ∫⁻ t in S, W t
  calc (∫⁻ t in (· + ℓ) ⁻¹' S, W t)
      ≤ ∫⁻ t in (· + ℓ) ⁻¹' S, ENNReal.ofReal (realPWLogShiftConstant α s ℓ) * W (t + ℓ) := by
        apply lintegral_mono
        intro t
        change ENNReal.ofReal (realPWLogDensity α s t) ≤
          ENNReal.ofReal (realPWLogShiftConstant α s ℓ) * ENNReal.ofReal (realPWLogDensity α s (t + ℓ))
        rw [← ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        have h := realPWLogDensity_sub_le (α := α) hs ℓ (t + ℓ)
        rwa [add_sub_cancel_right] at h
    _ = ENNReal.ofReal (realPWLogShiftConstant α s ℓ) *
          ∫⁻ y in S, W y ∂Measure.map (· + ℓ) volume := by
        rw [setLIntegral_map hS hW hadd]
        exact lintegral_const_mul _ (hW.comp hadd)
    _ = _ := by
        rw [map_add_right_eq_self volume ℓ, smul_eq_mul]

/-- The `L²` norm of a continuous function in the logarithmic weighted space grows by at most
the square root of the shift constant under a shift of the coordinate. -/
theorem eLpNorm_comp_add_realPWLogMeasure_le {α s : ℝ} (hs : 0 ≤ s) (ℓ : ℝ) {G : ℝ → ℂ}
    (hG : Continuous G) :
    eLpNorm (fun t ↦ G (t + ℓ)) 2 (realPWLogMeasure α s) ≤
      ENNReal.ofReal (realPWLogShiftConstant α s ℓ) ^ (1 / 2 : ℝ) *
        eLpNorm G 2 (realPWLogMeasure α s) := by
  have hadd : Measurable (· + ℓ : ℝ → ℝ) := measurable_add_const ℓ
  have h1 : eLpNorm (fun t ↦ G (t + ℓ)) 2 (realPWLogMeasure α s) =
      eLpNorm G 2 (Measure.map (· + ℓ) (realPWLogMeasure α s)) :=
    (eLpNorm_map_measure hG.aestronglyMeasurable hadd.aemeasurable).symm
  rw [h1]
  refine (eLpNorm_mono_measure G (map_add_realPWLogMeasure_le hs ℓ)).trans_eq ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] <;>
    first | exact hG.aestronglyMeasurable | simp [smul_eq_mul]

section Conversions

variable {α s : ℝ}

/-- Membership in the logarithmic weighted `L²` space, as an integral against the density. -/
theorem memLp_two_realPWLogMeasure_iff (hs : 0 ≤ s) {F : ℝ → ℂ} (hF : Continuous F) :
    MemLp F 2 (realPWLogMeasure α s) ↔
      Integrable (fun t ↦ ‖F t‖ ^ 2 * realPWLogDensity α s t) := by
  let ρ (t : ℝ) := ENNReal.ofReal (realPWLogDensity α s t)
  have hρ : Measurable ρ := (continuous_realPWLogDensity α s).measurable.ennreal_ofReal
  have hρf : ∀ᵐ t ∂volume, ρ t < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hρw (t : ℝ) : (ρ t).toReal = realPWLogDensity α s t :=
    ENNReal.toReal_ofReal (realPWLogDensity_pos hs t).le
  have hfun : (fun t ↦ (ρ t).toReal • ‖F t‖ ^ 2) =
      fun t ↦ ‖F t‖ ^ 2 * realPWLogDensity α s t := by
    funext t
    rw [hρw, smul_eq_mul, mul_comm]
  rw [memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable]
  change Integrable (fun t ↦ ‖F t‖ ^ 2) (volume.withDensity ρ) ↔ _
  rw [integrable_withDensity_iff_integrable_smul' hρ hρf, hfun]

/-- The squared norm in the logarithmic weighted space, as an integral against the density. -/
theorem integral_sq_realPWLogMeasure (hs : 0 ≤ s) (F : ℝ → ℂ) :
    ∫ t, ‖F t‖ ^ 2 ∂realPWLogMeasure α s = ∫ t, ‖F t‖ ^ 2 * realPWLogDensity α s t := by
  let ρ (t : ℝ) := ENNReal.ofReal (realPWLogDensity α s t)
  have hρ : Measurable ρ := (continuous_realPWLogDensity α s).measurable.ennreal_ofReal
  have hρf : ∀ᵐ t ∂volume, ρ t < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hρw (t : ℝ) : (ρ t).toReal = realPWLogDensity α s t :=
    ENNReal.toReal_ofReal (realPWLogDensity_pos hs t).le
  have hh := integral_withDensity_eq_integral_toReal_smul hρ hρf (fun t ↦ ‖F t‖ ^ 2)
  change ∫ t, ‖F t‖ ^ 2 ∂volume.withDensity ρ = _
  rw [hh]
  exact integral_congr_ae (ae_of_all _ fun t ↦ by
    change (ρ t).toReal • ‖F t‖ ^ 2 = _
    rw [hρw, smul_eq_mul, mul_comm])

/-- A shift of the coordinate keeps a continuous function in the logarithmic weighted space. -/
theorem memLp_comp_add_realPWLogMeasure (hs : 0 ≤ s) (ℓ : ℝ) {G : ℝ → ℂ} (hG : Continuous G)
    (hm : MemLp G 2 (realPWLogMeasure α s)) :
    MemLp (fun t ↦ G (t + ℓ)) 2 (realPWLogMeasure α s) :=
  lt_of_le_of_lt (eLpNorm_comp_add_realPWLogMeasure_le hs ℓ hG)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hm.eLpNorm_lt_top)

/-- The norm of a shifted continuous function is at most the square root of the shift
constant times the norm of the function. -/
theorem norm_toLp_comp_add_realPWLogMeasure_le (hs : 0 ≤ s) (ℓ : ℝ) {G : ℝ → ℂ}
    (hG : Continuous G) (hm : MemLp G 2 (realPWLogMeasure α s)) :
    ‖(memLp_comp_add_realPWLogMeasure hs ℓ hG hm).toLp _‖ ≤
      Real.sqrt (realPWLogShiftConstant α s ℓ) * ‖hm.toLp G‖ := by
  have hK := realPWLogShiftConstant_nonneg α s ℓ
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have hfin : ENNReal.ofReal (realPWLogShiftConstant α s ℓ) ^ (1 / 2 : ℝ) *
      eLpNorm G 2 (realPWLogMeasure α s) ≠ ∞ :=
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hm.eLpNorm_lt_top).ne
  have h := ENNReal.toReal_mono hfin (eLpNorm_comp_add_realPWLogMeasure_le hs ℓ hG)
  rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hK,
    ← Real.sqrt_eq_rpow] at h

end Conversions

section Band

variable {Y α s : ℝ}

/-- In the logarithmic coordinate on the positive half line, a vector of the even weighted band
is square integrable against the logarithmic density, with half its squared norm. -/
theorem realPWBand_integral_log_sq (hs : 0 ≤ s)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    Integrable (fun t ↦ ‖RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
      (Real.exp t) h‖ ^ 2 * realPWLogDensity α s t) ∧
    ∫ t, ‖RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
      (Real.exp t) h‖ ^ 2 * realPWLogDensity α s t = ‖h‖ ^ 2 / 2 := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let μ := realPWIntervalMeasure α s
  let ev := fun x ↦ RealPWBand.evaluation Y hμ x h
  let w := realPWIntervalWeight α s
  let g : ℝ → ℝ := fun x ↦ ‖ev x‖ ^ 2 * w x
  have hEval := RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) h
  have hSq : (fun x ↦ ‖ev x‖ ^ 2) =ᵐ[μ] (fun x ↦ ‖h.val x‖ ^ 2) :=
    hEval.mono fun _ hx ↦ congrArg (fun v : ℂ ↦ ‖v‖ ^ 2) hx
  have hIntμ : Integrable (fun x ↦ ‖ev x‖ ^ 2) μ :=
    ((Lp.memLp h.val).integrable_norm_pow (by norm_num)).congr hSq.symm
  let ρ (x : ℝ) := ENNReal.ofReal (w x)
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight α s)
  have hρf : ∀ᵐ x ∂volume, ρ x < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hw0 (x : ℝ) : 0 ≤ w x := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  have hρw (x : ℝ) : (ρ x).toReal = w x := ENNReal.toReal_ofReal (hw0 x)
  have hgfun : (fun x ↦ (ρ x).toReal • ‖ev x‖ ^ 2) = g := by
    funext x
    change (ρ x).toReal • ‖ev x‖ ^ 2 = ‖ev x‖ ^ 2 * w x
    rw [hρw, smul_eq_mul, mul_comm]
  have hgInt : Integrable g := by
    have h1 := (integrable_withDensity_iff_integrable_smul' hρ hρf).mp hIntμ
    rwa [hgfun] at h1
  have hgTot : ∫ x, g x = ‖h‖ ^ 2 := by
    have hh := integral_withDensity_eq_integral_toReal_smul hρ hρf (fun x ↦ ‖ev x‖ ^ 2)
    rw [hgfun] at hh
    calc ∫ x, g x = ∫ x, ‖ev x‖ ^ 2 ∂μ := hh.symm
      _ = ∫ x, ‖h.val x‖ ^ 2 ∂μ := integral_congr_ae hSq
      _ = ‖h‖ ^ 2 := by rw [L2.integral_sq_norm (𝕜 := ℂ)]; rfl
  have hgeven (x : ℝ) : g (-x) = g x := by
    change ‖RealPWBand.evaluation Y hμ (-x) h‖ ^ 2 * realPWIntervalWeight α s (-x) =
      ‖RealPWBand.evaluation Y hμ x h‖ ^ 2 * realPWIntervalWeight α s x
    rw [RealPWBand.evaluation_even, realPWIntervalWeight_even]
  have hIoi : ∫ x in Ioi (0 : ℝ), g x = ‖h‖ ^ 2 / 2 := by
    have hsplit : ∫ x, g x = (∫ x in Ioi (0 : ℝ), g x) + ∫ x in Iic (0 : ℝ), g x := by
      rw [← integral_add_compl measurableSet_Ioi hgInt, compl_Ioi]
    have hneg : ∫ x in Iic (0 : ℝ), g x = ∫ x in Ioi (0 : ℝ), g x := by
      have h1 := integral_comp_neg_Ioi (0 : ℝ) g
      rw [neg_zero] at h1
      rw [← h1]
      exact setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ hgeven x
    rw [hgTot, hneg] at hsplit
    linarith
  have hfun : (fun t ↦ ‖ev (Real.exp t)‖ ^ 2 * realPWLogDensity α s t) =
      fun t ↦ Real.exp t • g (Real.exp t) := by
    funext t
    change ‖ev (Real.exp t)‖ ^ 2 * (w (Real.exp t) * Real.exp t) =
      Real.exp t • (‖ev (Real.exp t)‖ ^ 2 * w (Real.exp t))
    rw [smul_eq_mul]
    ring
  change Integrable (fun t ↦ ‖ev (Real.exp t)‖ ^ 2 * realPWLogDensity α s t) ∧
    ∫ t, ‖ev (Real.exp t)‖ ^ 2 * realPWLogDensity α s t = ‖h‖ ^ 2 / 2
  rw [hfun]
  refine ⟨?_, ?_⟩
  · have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) MeasurableSet.univ
      (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g).mp
      (by rw [image_univ, Real.range_exp]; exact hgInt.integrableOn)
    rw [integrableOn_univ] at h1
    exact h1.congr (ae_of_all _ fun t ↦ by simp only [abs_of_pos (Real.exp_pos t)])
  · rw [integral_comp_exp g, hIoi]

/-- The restriction of a band vector to the positive half line, in the logarithmic
coordinate. -/
theorem memLp_realPWBand_log (hs : 0 ≤ s)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    MemLp (fun t ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
      (Real.exp t) h) 2 (realPWLogMeasure α s) :=
  (memLp_two_realPWLogMeasure_iff hs
    ((RealPWBand.contDiff_evaluation Y _ h 0).continuous.comp Real.continuous_exp)).mpr
    (realPWBand_integral_log_sq hs h).1

/-- A band vector restricted to the positive half line carries half of its squared norm, since
band vectors are even. -/
theorem norm_sq_toLp_realPWBand_log (hs : 0 ≤ s)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    ‖(memLp_realPWBand_log hs h).toLp _‖ ^ 2 = ‖h‖ ^ 2 / 2 := by
  rw [← L2.integral_sq_norm (𝕜 := ℂ), ← (realPWBand_integral_log_sq hs h).2,
    ← integral_sq_realPWLogMeasure hs]
  exact integral_congr_ae ((memLp_realPWBand_log hs h).coeFn_toLp.mono fun t ht ↦
    congrArg (fun v : ℂ ↦ ‖v‖ ^ 2) ht)

end Band

section ThetaMap

variable {Y α s : ℝ}

/-- A series that converges in `L²` and pointwise almost everywhere has the same sum in both
senses. The same statement is `Lp_hasSum_coeFn_ae_eq` of `Sec3_AdjointBinomial` in #7758; it is
repeated here because this file does not depend on that pull request. -/
private theorem hasSum_Lp_coeFn_ae_eq {X ι : Type*} [MeasurableSpace X] {ν₀ : Measure X}
    [Countable ι] (a : ι → Lp ℂ 2 ν₀) (S : Lp ℂ 2 ν₀) (hS : HasSum a S) (H : X → ℂ)
    (hH : ∀ᵐ x ∂ν₀, HasSum (fun i ↦ (a i : X → ℂ) x) (H x)) : (S : X → ℂ) =ᵐ[ν₀] H := by
  classical
  have h1 : Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, a i) atTop (𝓝 S) := hS
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp h1
  have h3 : TendstoInMeasure ν₀ (fun s : Finset ι ↦ ((∑ i ∈ s, a i : Lp ℂ 2 ν₀) : X → ℂ)) atTop
      (S : X → ℂ) := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) h2
  obtain ⟨ns, hns, hae⟩ := h3.exists_seq_tendsto_ae'
  have hcoe : ∀ᵐ x ∂ν₀, ∀ k : ℕ,
      ((∑ i ∈ ns k, a i : Lp ℂ 2 ν₀) : X → ℂ) x = ∑ i ∈ ns k, (a i : X → ℂ) x :=
    ae_all_iff.mpr fun k ↦ by
      induction ns k using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact Lp.coeFn_zero ℂ 2 ν₀
      | insert b s hb ih =>
        rw [Finset.sum_insert hb]
        filter_upwards [Lp.coeFn_add (a b) (∑ i ∈ s, a i), ih] with x h1 h2
        rw [h1, Pi.add_apply, h2, Finset.sum_insert hb]
  filter_upwards [hae, hH, hcoe] with x hx1 hx2 hx3
  have hx4 : Tendsto (fun k ↦ ∑ i ∈ ns k, (a i : X → ℂ) x) atTop (𝓝 (H x)) := hx2.comp hns
  exact tendsto_nhds_unique hx1 (hx4.congr fun k ↦ (hx3 k).symm)

theorem memLp_realPWBand_log_shift (hs : 0 ≤ s)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) (ℓ : ℝ) :
    MemLp (fun t ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
      (Real.exp (t + ℓ)) h) 2 (realPWLogMeasure α s) :=
  memLp_comp_add_realPWLogMeasure hs ℓ
    (G := fun t ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) (Real.exp t) h)
    ((RealPWBand.contDiff_evaluation Y _ h 0).continuous.comp Real.continuous_exp)
    (memLp_realPWBand_log hs h)

theorem norm_toLp_realPWBand_log_shift_le (hs : 0 ≤ s)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) (ℓ : ℝ) :
    ‖(memLp_realPWBand_log_shift hs h ℓ).toLp _‖ ≤
      Real.sqrt (realPWLogShiftConstant α s ℓ) * ‖h‖ := by
  refine (norm_toLp_comp_add_realPWLogMeasure_le hs ℓ
    ((RealPWBand.contDiff_evaluation Y _ h 0).continuous.comp Real.continuous_exp)
    (memLp_realPWBand_log hs h)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h2 := norm_sq_toLp_realPWBand_log hs h
  have h3 : ‖(memLp_realPWBand_log hs h).toLp _‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [h2]
    linarith [sq_nonneg ‖h‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- The band vector, restricted to the positive half line and shifted by `ℓ` in the logarithmic
coordinate: the function `t ↦ h (exp (t + ℓ))`, as a bounded linear map into the logarithmic
weighted space. -/
def realPWLogShiftMap (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) (ℓ : ℝ) :
    RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) →L[ℂ]
      Lp ℂ 2 (realPWLogMeasure α s) :=
  LinearMap.mkContinuous
    { toFun := fun h ↦ (memLp_realPWBand_log_shift hs h ℓ).toLp _
      map_add' := fun h₁ h₂ ↦ by
        rw [← MemLp.toLp_add (memLp_realPWBand_log_shift hs h₁ ℓ)
          (memLp_realPWBand_log_shift hs h₂ ℓ)]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun t ↦ by simp)
      map_smul' := fun c h ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_realPWBand_log_shift hs h ℓ)]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun t ↦ by simp) }
    (Real.sqrt (realPWLogShiftConstant α s ℓ)) fun h ↦ norm_toLp_realPWBand_log_shift_le hs h ℓ

theorem coeFn_realPWLogShiftMap (hs : 0 ≤ s) (ℓ : ℝ)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    (realPWLogShiftMap Y α hs ℓ h : ℝ → ℂ) =ᵐ[realPWLogMeasure α s]
      fun t ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
        (Real.exp (t + ℓ)) h :=
  MemLp.coeFn_toLp (memLp_realPWBand_log_shift hs h ℓ)

theorem norm_realPWLogShiftMap_le (hs : 0 ≤ s) (ℓ : ℝ) :
    ‖realPWLogShiftMap Y α hs ℓ‖ ≤ Real.sqrt (realPWLogShiftConstant α s ℓ) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-- For `ℓ ≥ 0` the shift constant is at most `exp (s log m) exp ((2 α + s / m - 1) ℓ)`, for
every natural number `m ≥ 1`: the polynomial factor is absorbed into an exponential of small
rate. -/
theorem realPWLogShiftConstant_le_exp (hα : 0 ≤ α) (hs : 0 ≤ s) (m : ℕ) (hm : 1 ≤ m) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    realPWLogShiftConstant α s ℓ ≤
      Real.exp (s * Real.log m) * Real.exp ((2 * α + s / m - 1) * ℓ) := by
  unfold realPWLogShiftConstant
  rw [abs_of_nonneg (mul_nonneg hα hℓ), abs_of_nonneg hℓ]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hme : (m : ℝ) * Real.exp (ℓ / m) = Real.exp (Real.log m + ℓ / m) := by
    rw [Real.exp_add, Real.exp_log hm0]
  have hbase : 1 + ℓ + ℓ ^ 2 ≤ Real.exp (2 * Real.log m + 2 * ℓ / m) := by
    have h1 : ℓ / m + 1 ≤ Real.exp (ℓ / m) := Real.add_one_le_exp _
    have h2 : (m : ℝ) + ℓ ≤ m * Real.exp (ℓ / m) := by
      have h := mul_le_mul_of_nonneg_left h1 hm0.le
      rw [mul_add, mul_one, mul_div_cancel₀ ℓ hm0.ne'] at h
      linarith
    have h3 : Real.exp (2 * Real.log m + 2 * ℓ / m) = ((m : ℝ) * Real.exp (ℓ / m)) ^ 2 := by
      rw [hme, sq, ← Real.exp_add]
      congr 1
      ring
    rw [h3]
    calc 1 + ℓ + ℓ ^ 2 ≤ ((m : ℝ) + ℓ) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_left₀ (by linarith) h2 2
  have hpow : (1 + ℓ + ℓ ^ 2) ^ (s / 2) ≤
      Real.exp ((2 * Real.log m + 2 * ℓ / m) * (s / 2)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  calc Real.exp (2 * (α * ℓ)) * (1 + ℓ + ℓ ^ 2) ^ (s / 2) * Real.exp (-ℓ)
      ≤ Real.exp (2 * (α * ℓ)) * Real.exp ((2 * Real.log m + 2 * ℓ / m) * (s / 2)) *
          Real.exp (-ℓ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = Real.exp (s * Real.log m) * Real.exp ((2 * α + s / m - 1) * ℓ) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring

/-- The square roots of the shift constants along the multiples of `log p` are summable when
the width is below one half. -/
theorem summable_sqrt_realPWLogShiftConstant {p : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hs : 0 ≤ s) (hp : 1 < p) :
    Summable fun n : ℕ ↦ Real.sqrt (realPWLogShiftConstant α s (n * Real.log p)) := by
  have hL : 0 < Real.log p := Real.log_pos hp
  have hgap : 0 < 1 - 2 * α := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (s / (1 - 2 * α))
  let m : ℕ := max m₀ 1
  have hm1 : 1 ≤ m := le_max_right _ _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmbig : s / (1 - 2 * α) < m :=
    hm₀.trans_le (by exact_mod_cast le_max_left m₀ 1)
  have hδ : 0 < 1 - 2 * α - s / m := by
    have h1 : s < (1 - 2 * α) * m := by rwa [div_lt_iff₀ hgap, mul_comm] at hmbig
    have h2 : s / m < 1 - 2 * α := by rwa [div_lt_iff₀ hm0]
    linarith
  let r := Real.exp (-((1 - 2 * α - s / m) * Real.log p) / 2)
  have hr1 : r < 1 := by
    have h0 : -((1 - 2 * α - s / m) * Real.log p) / 2 < 0 := by
      have := mul_pos hδ hL
      linarith
    have := Real.exp_lt_exp.mpr h0
    rwa [Real.exp_zero] at this
  refine Summable.of_nonneg_of_le (fun n ↦ Real.sqrt_nonneg _) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left
      (Real.exp (s * Real.log m / 2)))
  have hK := realPWLogShiftConstant_le_exp hα hs m hm1 (mul_nonneg (Nat.cast_nonneg n) hL.le)
  calc Real.sqrt (realPWLogShiftConstant α s (n * Real.log p))
      ≤ Real.sqrt (Real.exp (s * Real.log m) *
          Real.exp ((2 * α + s / m - 1) * (n * Real.log p))) := Real.sqrt_le_sqrt hK
    _ = Real.exp (s * Real.log m / 2) * r ^ n := by
        rw [← Real.exp_add, ← Real.exp_half, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

/-- The translations by the multiples of `log p` are summable in operator norm when the width
is below one half. -/
theorem summable_realPWLogShiftMap {p : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2) (hs : 0 ≤ s)
    (hp : 1 < p) : Summable fun n : ℕ ↦ realPWLogShiftMap Y α hs (n * Real.log p) :=
  Summable.of_norm_bounded (summable_sqrt_realPWLogShiftConstant hα hα' hs hp)
    fun _ ↦ norm_realPWLogShiftMap_le hs _

/-- The one-prime theta map on the band, in the logarithmic coordinate: the sum over `n ≥ 0`
of the shifts by `n log p`. On a band vector `h` it is the function
`t ↦ ∑ n, h (p ^ n exp t)` (`coeFn_realPWThetaMap`). -/
def realPWThetaMap (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) (p : ℝ) :
    RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) →L[ℂ]
      Lp ℂ 2 (realPWLogMeasure α s) :=
  ∑' n : ℕ, realPWLogShiftMap Y α hs (n * Real.log p)

private theorem exp_add_nat_mul_log {p : ℝ} (hp : 0 < p) (t : ℝ) (n : ℕ) :
    Real.exp (t + n * Real.log p) = p ^ n * Real.exp t := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hp, mul_comm]

/-- The theta map of a band vector is represented by the pointwise theta sum. -/
theorem coeFn_realPWThetaMap {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hα' : α < 1 / 2) (hs : 0 ≤ s)
    (hp : 1 < p) (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    (realPWThetaMap Y α hs p h : ℝ → ℂ) =ᵐ[realPWLogMeasure α s]
      fun t ↦ ∑' n : ℕ, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
        (p ^ n * Real.exp t) h := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsum := (summable_realPWLogShiftMap (Y := Y) hα.le hα' hs hp).hasSum
  have hS : HasSum (fun n : ℕ ↦ realPWLogShiftMap Y α hs (n * Real.log p) h)
      (realPWThetaMap Y α hs p h) :=
    hsum.mapL (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (realPWLogMeasure α s)) h)
  obtain ⟨C, -, hθ⟩ := exists_realPWBand_thetaEvaluation_bound (s := s) hY hα hs hp
  refine hasSum_Lp_coeFn_ae_eq _ _ hS _ ?_
  have hae : ∀ᵐ t ∂realPWLogMeasure α s, ∀ n : ℕ,
      (realPWLogShiftMap Y α hs (n * Real.log p) h : ℝ → ℂ) t =
        RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
          (p ^ n * Real.exp t) h :=
    ae_all_iff.mpr fun n ↦ (coeFn_realPWLogShiftMap hs (n * Real.log p) h).mono fun t ht ↦
      ht.trans (congrArg (fun x ↦ RealPWBand.evaluation Y
        (volume_le_realPWIntervalMeasure α s hs) x h) (exp_add_nat_mul_log hp0 t n))
  filter_upwards [hae] with t ht
  have hsm : Summable fun n : ℕ ↦ RealPWBand.evaluation Y
      (volume_le_realPWIntervalMeasure α s hs) (p ^ n * Real.exp t) h :=
    (hθ h (Real.exp t) (Real.exp_pos t)).1.of_norm
  exact hsm.hasSum.congr_fun fun n ↦ ht n

end ThetaMap

section ThetaVector

variable {Y α s : ℝ}

/-- The theta sum of the evaluation vectors of the band at the point `exp t`: the sum over
`n ≥ 0` of the evaluation vectors at `p ^ n exp t`. Pairing with it is the pointwise theta sum
(`hasSum_evaluation_realPWThetaVector`). -/
def realPWThetaVector (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) (p t : ℝ) :
    RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) :=
  ∑' n : ℕ, RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs)
    (p ^ n * Real.exp t)

/-- Pairing with the theta sum of the evaluation vectors is the pointwise theta sum. -/
theorem hasSum_evaluation_realPWThetaVector {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hs : 0 ≤ s)
    (hp : 1 < p) (t : ℝ) (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    HasSum (fun n : ℕ ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
        (p ^ n * Real.exp t) h) ⟪realPWThetaVector Y α hs p t, h⟫_ℂ := by
  obtain ⟨C, -, hC⟩ := exists_realPWBand_thetaEvaluationVector_bound (s := s) hY hα hs hp
  exact (hC (Real.exp t) (Real.exp_pos t)).2.2 h

/-- The theta sum of the evaluation vectors depends continuously on the logarithmic
coordinate. The series converges uniformly on every half line `t > t₀`. -/
theorem continuous_realPWThetaVector {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hs : 0 ≤ s)
    (hp : 1 < p) : Continuous (realPWThetaVector Y α hs p) := by
  obtain ⟨C₂, hC₂, hκ⟩ := exists_realPWBand_evaluationVector_rpow_bound (s := s) hY hα.le hs
  have hp0 : 0 < p := zero_lt_one.trans hp
  let ρ := p ^ (-α)
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hp0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hpow (n : ℕ) (x : ℝ) (hx : 0 < x) : (p ^ n * x) ^ (-α) = ρ ^ n * x ^ (-α) := by
    rw [Real.mul_rpow (pow_nonneg hp0.le n) hx.le, ← Real.rpow_natCast p n,
      ← Real.rpow_mul hp0.le, mul_comm (n : ℝ) (-α), Real.rpow_mul hp0.le, Real.rpow_natCast]
  refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
  have hon : ContinuousOn (realPWThetaVector Y α hs p) (Ioi (t₀ - 1)) := by
    refine continuousOn_tsum (u := fun n : ℕ ↦ C₂ * Real.exp (t₀ - 1) ^ (-α) * ρ ^ n)
      (fun n ↦ ?_) ?_ fun n t ht ↦ ?_
    · exact ((RealPWBand.continuous_evaluationVector Y _).comp
        (continuous_const.mul Real.continuous_exp)).continuousOn
    · exact (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
    · have hy : 0 < p ^ n * Real.exp t := mul_pos (pow_pos hp0 n) (Real.exp_pos t)
      have hexp : Real.exp t ^ (-α) ≤ Real.exp (t₀ - 1) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (Real.exp_le_exp.mpr (le_of_lt ht))
          (by linarith)
      calc ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs)
            (p ^ n * Real.exp t)‖ ≤ C₂ * (p ^ n * Real.exp t) ^ (-α) := (hκ _ hy).2
        _ = C₂ * Real.exp t ^ (-α) * ρ ^ n := by rw [hpow n _ (Real.exp_pos t)]; ring
        _ ≤ C₂ * Real.exp (t₀ - 1) ^ (-α) * ρ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC₂) (pow_nonneg hρ0.le n)
  exact hon.continuousAt (Ioi_mem_nhds (by linarith))

/-- The theta map of a band vector is represented by the pairing with the theta sums of the
evaluation vectors, a continuous function. -/
theorem coeFn_realPWThetaMap_inner {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hα' : α < 1 / 2)
    (hs : 0 ≤ s) (hp : 1 < p) (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    (realPWThetaMap Y α hs p h : ℝ → ℂ) =ᵐ[realPWLogMeasure α s]
      fun t ↦ ⟪realPWThetaVector Y α hs p t, h⟫_ℂ :=
  (coeFn_realPWThetaMap hY hα hα' hs hp h).trans (ae_of_all _ fun t ↦
    (hasSum_evaluation_realPWThetaVector hY hα hs hp t h).tsum_eq)

/-- The theta sum at `t` is the value of the band vector at `exp t` plus the theta sum at
`t + log p`. -/
theorem inner_realPWThetaVector_eq_add {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hs : 0 ≤ s)
    (hp : 1 < p) (t : ℝ) (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    ⟪realPWThetaVector Y α hs p t, h⟫_ℂ =
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) (Real.exp t) h +
        ⟪realPWThetaVector Y α hs p (t + Real.log p), h⟫_ℂ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have h1 := hasSum_evaluation_realPWThetaVector hY hα hs hp t h
  have h2 := hasSum_evaluation_realPWThetaVector hY hα hs hp (t + Real.log p) h
  rw [← h1.tsum_eq, ← h2.tsum_eq, h1.summable.tsum_eq_zero_add]
  congr 1
  · rw [pow_zero, one_mul]
  · refine tsum_congr fun n ↦ ?_
    have hx : p ^ (n + 1) * Real.exp t = p ^ n * Real.exp (t + Real.log p) := by
      rw [Real.exp_add, Real.exp_log hp0]
      ring
    rw [hx]

/-- The theta map is bounded below on the band: subtracting from the theta sum its translate
by `log p` gives the band vector back. -/
theorem norm_le_norm_realPWThetaMap {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hα' : α < 1 / 2)
    (hs : 0 ≤ s) (hp : 1 < p) (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    ‖h‖ ≤ Real.sqrt 2 * (1 + Real.sqrt (realPWLogShiftConstant α s (Real.log p))) *
      ‖realPWThetaMap Y α hs p h‖ := by
  let G : ℝ → ℂ := fun t ↦ ⟪realPWThetaVector Y α hs p t, h⟫_ℂ
  have hGc : Continuous G := (continuous_realPWThetaVector hY hα hs hp).inner continuous_const
  have hae := coeFn_realPWThetaMap_inner hY hα hα' hs hp h
  have hGm : MemLp G 2 (realPWLogMeasure α s) :=
    (Lp.memLp (realPWThetaMap Y α hs p h)).ae_eq hae
  have hGeq : hGm.toLp G = realPWThetaMap Y α hs p h := by
    rw [← Lp.toLp_coeFn (realPWThetaMap Y α hs p h) (Lp.memLp _)]
    exact MemLp.toLp_congr _ _ hae.symm
  have hGs := memLp_comp_add_realPWLogMeasure hs (Real.log p) hGc hGm
  have hshift := norm_toLp_comp_add_realPWLogMeasure_le hs (Real.log p) hGc hGm
  have hdiff : (memLp_realPWBand_log hs h).toLp _ = hGm.toLp G - hGs.toLp _ := by
    rw [← MemLp.toLp_sub hGm hGs]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun t ↦ ?_)
    change _ = G t - G (t + Real.log p)
    change _ = ⟪realPWThetaVector Y α hs p t, h⟫_ℂ -
      ⟪realPWThetaVector Y α hs p (t + Real.log p), h⟫_ℂ
    rw [inner_realPWThetaVector_eq_add hY hα hs hp t h]
    ring
  have h1 : ‖(memLp_realPWBand_log hs h).toLp _‖ ≤
      (1 + Real.sqrt (realPWLogShiftConstant α s (Real.log p))) *
        ‖realPWThetaMap Y α hs p h‖ := by
    rw [hdiff]
    calc ‖hGm.toLp G - hGs.toLp _‖ ≤ ‖hGm.toLp G‖ + ‖hGs.toLp _‖ := norm_sub_le _ _
      _ ≤ ‖hGm.toLp G‖ +
          Real.sqrt (realPWLogShiftConstant α s (Real.log p)) * ‖hGm.toLp G‖ :=
        add_le_add_right hshift _
      _ = _ := by rw [hGeq]; ring
  have h2 := norm_sq_toLp_realPWBand_log hs h
  have h3 : ‖h‖ = Real.sqrt 2 * ‖(memLp_realPWBand_log hs h).toLp _‖ := by
    have h4 : ‖h‖ ^ 2 = 2 * ‖(memLp_realPWBand_log hs h).toLp _‖ ^ 2 := by linarith
    calc ‖h‖ = Real.sqrt (‖h‖ ^ 2) := (Real.sqrt_sq (norm_nonneg h)).symm
      _ = _ := by rw [h4, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  rw [h3, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)

end ThetaVector

section ThetaLevel

variable {Y α s : ℝ}

/-- The level of the band: the band vectors that vanish at the origin, a closed subspace. -/
def realPWBandLevel (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Submodule ℂ (RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :=
  LinearMap.ker (RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 :
    RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) →ₗ[ℂ] ℂ)

theorem mem_realPWBandLevel_iff (hs : 0 ≤ s)
    (h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    h ∈ realPWBandLevel Y α hs ↔
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 h = 0 := by
  rw [realPWBandLevel, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

instance instCompleteSpaceRealPWBandLevel (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    CompleteSpace (realPWBandLevel Y α hs) :=
  (ContinuousLinearMap.isClosed_ker
    (RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0)).completeSpace_coe

/-- The theta map restricted to the level. -/
def realPWThetaLevelMap (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) (p : ℝ) :
    realPWBandLevel Y α hs →L[ℂ] Lp ℂ 2 (realPWLogMeasure α s) :=
  (realPWThetaMap Y α hs p).comp (realPWBandLevel Y α hs).subtypeL

/-- The image of the level under the theta map, a subspace of the logarithmic weighted space.
It is closed when `0 < α < 1 / 2` (`completeSpace_realPWThetaLevelRange`). -/
def realPWThetaLevelRange (Y α : ℝ) {s : ℝ} (hs : 0 ≤ s) (p : ℝ) :
    Submodule ℂ (Lp ℂ 2 (realPWLogMeasure α s)) :=
  LinearMap.range (realPWThetaLevelMap Y α hs p :
    realPWBandLevel Y α hs →ₗ[ℂ] Lp ℂ 2 (realPWLogMeasure α s))

/-- The image of the level consists of the theta maps of the band vectors that vanish at the
origin. -/
theorem mem_realPWThetaLevelRange_iff (hs : 0 ≤ s) (p : ℝ)
    (F : Lp ℂ 2 (realPWLogMeasure α s)) :
    F ∈ realPWThetaLevelRange Y α hs p ↔
      ∃ h : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs),
        RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 h = 0 ∧
          realPWThetaMap Y α hs p h = F := by
  rw [realPWThetaLevelRange, LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (mem_realPWBandLevel_iff hs _).mp x.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, (mem_realPWBandLevel_iff hs _).mpr hh⟩, rfl⟩

/-- The theta map on the level is bounded below. -/
theorem antilipschitz_realPWThetaLevelMap {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α) (hα' : α < 1 / 2)
    (hs : 0 ≤ s) (hp : 1 < p) :
    AntilipschitzWith
      (Real.toNNReal (Real.sqrt 2 * (1 + Real.sqrt (realPWLogShiftConstant α s (Real.log p)))))
      (realPWThetaLevelMap Y α hs p) :=
  AddMonoidHomClass.antilipschitz_of_bound _ fun x ↦ by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_le_norm_realPWThetaMap hY hα hα' hs hp x.1

/-- The image of the level under the theta map is complete, since the theta map is bounded
below. -/
theorem completeSpace_realPWThetaLevelRange {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α)
    (hα' : α < 1 / 2) (hs : 0 ≤ s) (hp : 1 < p) :
    CompleteSpace (realPWThetaLevelRange Y α hs p) := by
  have hclo : IsClosed (Set.range (realPWThetaLevelMap Y α hs p)) :=
    (antilipschitz_realPWThetaLevelMap hY hα hα' hs hp).isClosed_range
      (realPWThetaLevelMap Y α hs p).uniformContinuous
  have hrange : (realPWThetaLevelRange Y α hs p : Set (Lp ℂ 2 (realPWLogMeasure α s))) =
      Set.range (realPWThetaLevelMap Y α hs p) := by
    ext F
    simp [realPWThetaLevelRange]
  have hclo' : IsClosed (realPWThetaLevelRange Y α hs p : Set (Lp ℂ 2 (realPWLogMeasure α s))) := by
    rw [hrange]
    exact hclo
  exact hclo'.completeSpace_coe

/-- Paper: Theorem 12.4.1.1, pp. 514–517, for one finite prime beside the real place, at a
fixed level. The image of the level under the theta map has continuous, uniformly bounded
evaluation vectors: `⟪e t, f⟫` is the value at `t` of the theta sum that represents `f`.
Reconstruction: The paper does not state this. It is the hypothesis of
`sLocalTrace_projectedCutoffKernel` for the one-prime model in the logarithmic coordinate. -/
theorem exists_realPWThetaLevelRange_evaluationVector {p : ℝ} (hY : 0 ≤ Y) (hα : 0 < α)
    (hα' : α < 1 / 2) (hs : 0 ≤ s) (hp : 1 < p) :
    ∃ (e : ℝ → realPWThetaLevelRange Y α hs p) (C : ℝ), Continuous e ∧ (∀ t, ‖e t‖ ≤ C) ∧
      (∀ (t : ℝ) (h : realPWBandLevel Y α hs) (f : realPWThetaLevelRange Y α hs p),
        (f : Lp ℂ 2 (realPWLogMeasure α s)) = realPWThetaMap Y α hs p h →
          ⟪e t, f⟫_ℂ = ∑' n : ℕ, RealPWBand.evaluation Y
            (volume_le_realPWIntervalMeasure α s hs) (p ^ n * Real.exp t) h) ∧
      ∀ f : realPWThetaLevelRange Y α hs p,
        (fun t ↦ ⟪e t, f⟫_ℂ) =ᵐ[realPWLogMeasure α s]
          ((f : Lp ℂ 2 (realPWLogMeasure α s)) : ℝ → ℂ) := by
  classical
  have := completeSpace_realPWThetaLevelRange hY hα hα' hs hp
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let B := RealPWBand.space Y hμ
  let L₀ := realPWBandLevel Y α hs
  let V := realPWThetaLevelRange Y α hs p
  let Θ₀ := realPWThetaLevelMap Y α hs p
  have hinj : Function.Injective Θ₀ :=
    (antilipschitz_realPWThetaLevelMap hY hα hα' hs hp).injective
  let Θl : L₀ →ₗ[ℂ] Lp ℂ 2 (realPWLogMeasure α s) := Θ₀
  have hinjl : Function.Injective Θl := hinj
  let Jl : L₀ ≃ₗ[ℂ] V := LinearEquiv.ofInjective Θl hinjl
  have hJl (v : V) : Θ₀ (Jl.symm v) = (v : Lp ℂ 2 (realPWLogMeasure α s)) := by
    have h1 : ((Jl (Jl.symm v) : V) : Lp ℂ 2 (realPWLogMeasure α s)) = Θl (Jl.symm v) :=
      LinearEquiv.ofInjective_apply Θl (h := hinjl) (Jl.symm v)
    rw [Jl.apply_symm_apply] at h1
    exact h1.symm
  let K : ℝ := Real.sqrt 2 * (1 + Real.sqrt (realPWLogShiftConstant α s (Real.log p)))
  let J : V →L[ℂ] L₀ := LinearMap.mkContinuous Jl.symm.toLinearMap K fun v ↦ by
    have h1 := norm_le_norm_realPWThetaMap hY hα hα' hs hp (Jl.symm v).1
    have h2 : realPWThetaMap Y α hs p (Jl.symm v).1 = (v : Lp ℂ 2 (realPWLogMeasure α s)) :=
      hJl v
    rw [h2] at h1
    exact h1
  have hJ (v : V) : Θ₀ (J v) = (v : Lp ℂ 2 (realPWLogMeasure α s)) := hJl v
  let A : V →L[ℂ] B := L₀.subtypeL.comp J
  have hA (v : V) : realPWThetaMap Y α hs p (A v) = (v : Lp ℂ 2 (realPWLogMeasure α s)) := hJ v
  have hA0 (v : V) : RealPWBand.evaluation Y hμ 0 (A v) = 0 :=
    (mem_realPWBandLevel_iff hs _).mp (J v).2
  let E := realPWThetaVector Y α hs p
  have hE : Continuous E := continuous_realPWThetaVector hY hα hs hp
  let φ : ℝ → V →L[ℂ] ℂ := fun t ↦ (ContinuousLinearMap.compL ℂ V B ℂ).flip A (innerSL ℂ (E t))
  have hφ (t : ℝ) (v : V) : φ t v = ⟪E t, A v⟫_ℂ := rfl
  let e : ℝ → V := fun t ↦ (InnerProductSpace.toDual ℂ V).symm (φ t)
  have he_inner (t : ℝ) (v : V) : ⟪e t, v⟫_ℂ = ⟪E t, A v⟫_ℂ := by
    rw [← hφ t v]
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨C₁, -, hθ⟩ := exists_realPWBand_thetaEvaluation_bound (s := s) hY hα hs hp
  obtain ⟨C, hC, hlevel⟩ := exists_realPWBand_thetaEvaluation_level_bound (s := s) hY hα hs hp
  refine ⟨e, C * ‖A‖, ?_, fun t ↦ ?_, fun t h f hf ↦ ?_, fun f ↦ ?_⟩
  · exact (InnerProductSpace.toDual ℂ V).symm.continuous.comp
      (((ContinuousLinearMap.compL ℂ V B ℂ).flip A).continuous.comp
        ((innerSL ℂ).continuous.comp hE))
  · have hnorm : ‖e t‖ = ‖φ t‖ := LinearIsometryEquiv.norm_map _ _
    rw [hnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _)) fun v ↦ ?_
    rw [hφ t v, ← (hasSum_evaluation_realPWThetaVector hY hα hs hp t (A v)).tsum_eq]
    calc ‖∑' n : ℕ, RealPWBand.evaluation Y hμ (p ^ n * Real.exp t) (A v)‖
        ≤ ∑' n : ℕ, ‖RealPWBand.evaluation Y hμ (p ^ n * Real.exp t) (A v)‖ :=
          norm_tsum_le_tsum_norm (hθ (A v) (Real.exp t) (Real.exp_pos t)).1
      _ ≤ C * ‖A v‖ := hlevel (A v) (hA0 v) (Real.exp t) (Real.exp_pos t)
      _ ≤ C * (‖A‖ * ‖v‖) := mul_le_mul_of_nonneg_left (A.le_opNorm v) hC
      _ = C * ‖A‖ * ‖v‖ := by ring
  · have hJf : J f = h := hinj ((hJ f).trans hf)
    have hAf : A f = (h : B) := congrArg Subtype.val hJf
    rw [he_inner, hAf, (hasSum_evaluation_realPWThetaVector hY hα hs hp t (h : B)).tsum_eq]
  · have h1 := coeFn_realPWThetaMap_inner hY hα hα' hs hp (A f)
    have h2 : (fun t ↦ ⟪e t, f⟫_ℂ) = fun t ↦ ⟪E t, A f⟫_ℂ := funext fun t ↦ he_inner t f
    rw [h2]
    have h3 : ((f : Lp ℂ 2 (realPWLogMeasure α s)) : ℝ → ℂ) =
        (realPWThetaMap Y α hs p (A f) : ℝ → ℂ) := by rw [hA f]
    rw [h3]
    exact h1.symm

end ThetaLevel

end RiemannMasullo.Isolated
