module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelTrace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The real-place trace for dilations below one, in the unweighted model

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, in the fixed-bandwidth model of the real
place of `ℚ` of #7354, for test functions supported in `0 < g < 1`.

`Sec4_RealPWTestTrace` and `Sec4_RealPWLevelTrace` treat test functions supported in `g > 1`,
where the dilation `f ↦ f (g⁻¹ x)` contracts and so preserves the band. For `g < 1` it does not
preserve the band. The operator is still nuclear and its trace is still the integral of the
diagonal, for every weight (`exists_realPWTestCutoff_nuclear`, which asks only for `0 < a`).
This file computes the limit of the trace when both parameters of the weight are zero, so that
the weight is one and the measure is Lebesgue measure.

* `realPWSharpTrace_zero_zero_eq_star_inv`. Without weight the sharp trace of the dilation by
  `g⁻¹` at cutoff `L` is the conjugate of the sharp trace of the dilation by `g` at cutoff
  `L / g`. This is the change of variable `x = g u` in the diagonal integral, with the
  Hermitian symmetry of the reproducing kernel.
* `exists_realPWTestCutoff_trace_limit_of_lt_one`. On the whole band the traces converge to the
  integral of `ψ` against `(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`
  (`realPWSharpTraceLimit_zero_inv`). This is the integrand of the real term of (12.4.1.1) at
  `g < 1`.
* `integral_star_evaluationVector_zero_mul_dilate_of_lt_one`. For `g < 1` the pairing of the
  evaluation vector at the origin with its own dilate is `g` times its value at the origin.
* `exists_realPWTestCutoff_level_trace_limit_of_lt_one`. On the level of band vectors vanishing
  at the origin the traces converge to the limit on the whole band minus the integral of
  `ψ g g ^ (1/2)`.

Together with `exists_realPWTestCutoff_level_trace_limit`, the term that the level removes in
the unweighted model is the integral of `ψ g min (g ^ (1/2), g ^ (-1/2))`: for `g > 1` it is
`g ^ (-1/2)` and for `g < 1` it is `g ^ (1/2)`.

Reconstruction: The paper does not state this. The operator is the one of
`Sec4_RealPWLevelTrace`.

Not treated here: a weight with `α > 0` or `s > 0` for `g < 1`. There the change of variable
puts the quotient of the weights at `u` and at `g u` into the diagonal integral, and the limit
is not computed. Test functions whose support meets `g = 1`. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- With both parameters zero the weight is one. -/
theorem realPWIntervalWeight_zero_zero (x : ℝ) : realPWIntervalWeight 0 0 x = 1 := by
  simp [realPWIntervalWeight]

/-- With both parameters zero the weighted measure is Lebesgue measure. -/
theorem realPWIntervalMeasure_zero_zero : realPWIntervalMeasure 0 0 = volume := by
  have hw : (fun x ↦ ENNReal.ofReal (realPWIntervalWeight 0 0 x)) = fun _ ↦ 1 := by
    funext x
    rw [realPWIntervalWeight_zero_zero, ENNReal.ofReal_one]
  change volume.withDensity (fun x ↦ ENNReal.ofReal (realPWIntervalWeight 0 0 x)) = volume
  rw [hw, withDensity_const, one_smul]

/-- With both parameters zero an integral for the weighted measure is a Lebesgue integral. -/
theorem integral_realPWIntervalMeasure_zero_zero (F : ℝ → ℂ) :
    ∫ x, F x ∂realPWIntervalMeasure 0 0 = ∫ x, F x := by
  rw [realPWIntervalMeasure_zero_zero]

/-- The sharp mask at a dilated point is the sharp mask of the dilated interval. -/
theorem sharpIntervalMask_mul_left {g : ℝ} (hg : 0 < g) (L u : ℝ) :
    sharpIntervalMask L (g * u) = sharpIntervalMask (L / g) u := by
  have h : g * u ∈ Icc (-L) L ↔ u ∈ Icc (-(L / g)) (L / g) := by
    rw [mem_Icc, mem_Icc, ← neg_div, div_le_iff₀ hg, le_div_iff₀ hg, mul_comm u g]
  by_cases hu : u ∈ Icc (-(L / g)) (L / g)
  · simp [sharpIntervalMask, hu, h.mpr hu]
  · simp [sharpIntervalMask, hu, mt h.mp hu]

/-- For `0 < g < 1` the limit of the sharp trace of the dilation by `g` is
`(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`. This is the integrand of the real term of
(12.4.1.1), p. 514, at `g < 1`, summed over the two signs of the dilation. -/
theorem realPWSharpTraceLimit_zero_inv {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) :
    realPWSharpTraceLimit 0 g⁻¹ =
      ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr hg1
  have hr : g⁻¹ ^ (1 / 2 : ℝ) = (g ^ (1 / 2 : ℝ))⁻¹ := Real.inv_rpow hg0.le _
  have hsq : g ^ (1 / 2 : ℝ) * g ^ (1 / 2 : ℝ) = g := by
    rw [← Real.rpow_add hg0]
    norm_num
  have hp : g ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hg0 _).ne'
  have h3 : g⁻¹ - 1 = (1 - g) / g := by rw [sub_div, div_self hg0.ne', one_div]
  have h4 : g⁻¹ + 1 = (1 + g) / g := by rw [add_div, div_self hg0.ne', one_div]
  have h5 : g * (g ^ (1 / 2 : ℝ))⁻¹ = g ^ (1 / 2 : ℝ) := by
    rw [← div_eq_mul_inv, div_eq_iff hp]
    exact hsq.symm
  have hreal : 1 / 2 * ((g⁻¹ - 1)⁻¹ + (g⁻¹ + 1)⁻¹) * g⁻¹ ^ (1 / 2 : ℝ) =
      1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) := by
    rw [hr, h3, h4, inv_div, inv_div]
    calc 1 / 2 * (g / (1 - g) + g / (1 + g)) * (g ^ (1 / 2 : ℝ))⁻¹
        = 1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * (g * (g ^ (1 / 2 : ℝ))⁻¹) := by ring
      _ = _ := by rw [h5]
  rw [realPWSharpTraceLimit_of_lt_half (by norm_num) hinv]
  exact congrArg Complex.ofReal hreal

section Unweighted

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀
local notation "evv" => RealPWBand.evaluationVector Y hμ₀

/-- Without weight the diagonal of the dilation by `g⁻¹` is the half-density factor times the
reproducing kernel at `(g⁻¹ x, x)`. -/
theorem realPWSharpDensity_zero_zero (g x : ℝ) :
    realPWSharpDensity Y 0 0 hs g x =
      ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x) := by
  change ((realPWIntervalWeight 0 0 x * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ev (g⁻¹ * x) (evv x) = _
  rw [realPWIntervalWeight_zero_zero, one_mul]

/-- The reproducing kernel of the band is Hermitian. -/
private theorem evaluation_evaluationVector_symm (x y : ℝ) :
    (starRingEnd ℂ) (ev y (evv x)) = ev x (evv y) := by
  have h1 : ev x (evv y) = ⟪evv x, evv y⟫_ℂ := by
    rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
  have h2 : ev y (evv x) = ⟪evv y, evv x⟫_ℂ := by
    rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
  rw [h1, h2, inner_conj_symm]

/-- The sharp mask is real. -/
private theorem conj_sharpIntervalMask (L x : ℝ) :
    (starRingEnd ℂ) (sharpIntervalMask L x) = sharpIntervalMask L x := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

/-- Reconstruction: without weight, the sharp trace of the dilation by `g⁻¹` at cutoff `L` is
the conjugate of the sharp trace of the dilation by `g` at cutoff `L / g`. The diagonal
integral is carried over by the change of variable `x = g u`, and the reproducing kernel is
Hermitian. No invariance of the band under the dilation is used. -/
theorem realPWSharpTrace_zero_zero_eq_star_inv {g : ℝ} (hg : 0 < g) (L : ℝ) :
    realPWSharpTrace Y 0 0 hs g L = star (realPWSharpTrace Y 0 0 hs g⁻¹ (L / g)) := by
  have hr1 : g ^ (1 / 2 : ℝ) = g ^ (-(1 / 2 : ℝ)) * g := by
    rw [← Real.rpow_add_one hg.ne']
    norm_num
  have hr2 : g⁻¹ ^ (-(1 / 2 : ℝ)) = g ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow hg.le, ← Real.rpow_neg hg.le, neg_neg]
  have hsub : ∫ u, sharpIntervalMask L (g * u) *
      (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * (g * u)) (evv (g * u))) =
      |g⁻¹| • ∫ x, sharpIntervalMask L x *
        (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x)) :=
    Measure.integral_comp_mul_left (fun x ↦ sharpIntervalMask L x *
      (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x))) g
  have hgg : ((g : ℝ) : ℂ) * ((g⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hg.ne', Complex.ofReal_one]
  calc realPWSharpTrace Y 0 0 hs g L
      = ∫ x, sharpIntervalMask L x *
          (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (evv x)) := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        change sharpIntervalMask L x * realPWSharpDensity Y 0 0 hs g x = _
        rw [realPWSharpDensity_zero_zero Y hs]
    _ = (g : ℂ) * ∫ u, sharpIntervalMask L (g * u) *
          (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * (g * u)) (evv (g * u))) := by
        rw [hsub, abs_of_pos (inv_pos.mpr hg), Complex.real_smul, ← mul_assoc, hgg, one_mul]
    _ = ∫ u, (starRingEnd ℂ)
          (sharpIntervalMask (L / g) u * realPWSharpDensity Y 0 0 hs g⁻¹ u) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        change (g : ℂ) * (sharpIntervalMask L (g * u) *
          (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * (g * u)) (evv (g * u)))) =
          (starRingEnd ℂ) (sharpIntervalMask (L / g) u * realPWSharpDensity Y 0 0 hs g⁻¹ u)
        rw [realPWSharpDensity_zero_zero Y hs, inv_inv, hr2, map_mul, map_mul,
          Complex.conj_ofReal, conj_sharpIntervalMask, evaluation_evaluationVector_symm Y hs,
          sharpIntervalMask_mul_left hg, inv_mul_cancel_left₀ hg.ne', hr1]
        push_cast
        ring
    _ = star (realPWSharpTrace Y 0 0 hs g⁻¹ (L / g)) := by
        rw [integral_conj]
        rfl

/-- Reconstruction: without weight, the sharp trace of the dilation by `g⁻¹`, integrated
against a function of `g` supported in `[a, b]` with `0 < a` and `b < 1`, converges as the
cutoff is removed to the integral against the limits for the reciprocal dilations. -/
theorem tendsto_integral_realPWSharpTrace_of_lt_one (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    Tendsto (fun L ↦ ∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) atTop
      (𝓝 (∫ g, ψ g * realPWSharpTraceLimit 0 g⁻¹)) := by
  by_cases hab : a ≤ b
  swap
  · have hz : ∀ g, ψ g = 0 := fun g ↦ hψ0 g fun hg ↦ hab (hg.1.trans hg.2)
    simp only [hz, zero_mul, integral_zero]
    exact tendsto_const_nhds
  have hb0 : 0 < b := ha0.trans_le hab
  have hb1' : 1 < b⁻¹ := (one_lt_inv₀ hb0).mpr hb1
  obtain ⟨⟨B, hB⟩, hlim⟩ := exists_bound_and_tendsto_realPWSharpTrace (Y := Y) (α := 0)
    (s := 0) hY le_rfl hs hb1' a⁻¹
  have hmem : ∀ g ∈ Icc a b, g⁻¹ ∈ Icc b⁻¹ a⁻¹ := fun g hg ↦
    ⟨inv_anti₀ (ha0.trans_le hg.1) hg.2, inv_anti₀ ha0 hg.1⟩
  have hreal : ∀ g ∈ Icc a b,
      star (realPWSharpTraceLimit 0 g⁻¹) = realPWSharpTraceLimit 0 g⁻¹ := by
    intro g hg
    have h1 : 1 < g⁻¹ := hb1'.trans_le (hmem g hg).1
    rw [realPWSharpTraceLimit_of_lt_half (by norm_num) h1, ← starRingEnd_apply,
      Complex.conj_ofReal]
  refine tendsto_integral_filter_of_dominated_convergence (fun g ↦ ‖ψ g‖ * B)
    (.of_forall fun L ↦ ?_) (.of_forall fun L ↦ ae_of_all _ fun g ↦ ?_)
    (hψ.norm.mul_const _) (ae_of_all _ fun g ↦ ?_)
  · exact hψ.aestronglyMeasurable.mul (measurable_realPWSharpTrace hs L).aestronglyMeasurable
  · by_cases hg : g ∈ Icc a b
    · rw [norm_mul, realPWSharpTrace_zero_zero_eq_star_inv Y hs (ha0.trans_le hg.1), norm_star]
      exact mul_le_mul_of_nonneg_left (hB g⁻¹ (hmem g hg) _) (norm_nonneg _)
    · rw [hψ0 g hg, zero_mul, norm_zero, zero_mul]
  · by_cases hg : g ∈ Icc a b
    · have hg0 : 0 < g := ha0.trans_le hg.1
      have h1 : Tendsto (fun L : ℝ ↦ L / g) atTop atTop := tendsto_id.atTop_div_const hg0
      have h2 := (continuous_star.tendsto _).comp ((hlim g⁻¹ (hmem g hg)).comp h1)
      rw [hreal g hg] at h2
      refine (h2.congr fun L ↦ ?_).const_mul (ψ g)
      exact (realPWSharpTrace_zero_zero_eq_star_inv Y hs hg0 L).symm
    · simp only [hψ0 g hg, zero_mul]
      exact tendsto_const_nhds

/-- Reconstruction: without weight, for a continuous test function `ψ` of the dilation
supported in `[a, b]` with `0 < a` and `b < 1`, the traces of the sharp cutoffs of its action
on the even band converge as the cutoff is removed. By `realPWSharpTraceLimit_zero_inv` the
limit is the integral of `ψ` against `(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`.
Paper: this is the real-place term of Theorem 12.4.1.1, pp. 514–517, in the fixed-bandwidth
model of the real place of `ℚ`, for a test function supported in `0 < g < 1`. -/
theorem exists_realPWTestCutoff_trace_limit_of_lt_one (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L (f : V₀), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) ∧
        (T L).val f = (V₀).orthogonalProjectionOnto r) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g * realPWSharpTraceLimit 0 g⁻¹)) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_nuclear Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) =
      fun L ↦ ∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L := funext hT2
  rw [h]
  exact tendsto_integral_realPWSharpTrace_of_lt_one Y hs hY ha0 hb1 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0

/-- Reconstruction: without weight and for `0 < g < 1`, the pairing of the evaluation vector at
the origin with its own dilate `x ↦ e (g⁻¹ x)` is `g` times its value at the origin. The dilate
is not a band vector. The change of variable `x = g u` turns the pairing into the conjugate of
the pairing with the contraction by `g`, which is known. -/
theorem integral_star_evaluationVector_zero_mul_dilate_of_lt_one (hY : 0 < Y) {g : ℝ}
    (hg0 : 0 < g) (hg1 : g < 1) :
    ∫ x, star (ev x (evv 0)) * ev (g⁻¹ * x) (evv 0) ∂μ₀ = (g : ℂ) * ev 0 (evv 0) := by
  let E : ℝ → ℂ := fun x ↦ ev x (evv 0)
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr hg1
  have hup : ∫ x, star (E x) * E (g * x) = ev 0 (evv 0) := by
    have h := integral_star_evaluationVector_zero_mul_dilate Y 0 0 hs hY hinv (evv 0)
    rw [integral_realPWIntervalMeasure_zero_zero, inv_inv] at h
    exact h
  have hreal : (starRingEnd ℂ) (ev 0 (evv 0)) = ev 0 (evv 0) :=
    evaluation_evaluationVector_symm Y hs 0 0
  have hsub : ∫ u, star (E (g * u)) * E (g⁻¹ * (g * u)) =
      |g⁻¹| • ∫ x, star (E x) * E (g⁻¹ * x) :=
    Measure.integral_comp_mul_left (fun x ↦ star (E x) * E (g⁻¹ * x)) g
  have hG : (fun u ↦ star (E (g * u)) * E (g⁻¹ * (g * u))) =
      fun u ↦ (starRingEnd ℂ) (star (E u) * E (g * u)) := by
    funext u
    rw [inv_mul_cancel_left₀ hg0.ne', map_mul, starRingEnd_apply, starRingEnd_apply,
      star_star, mul_comm]
  rw [hG, integral_conj, hup, hreal, abs_of_pos (inv_pos.mpr hg0), Complex.real_smul] at hsub
  rw [integral_realPWIntervalMeasure_zero_zero]
  change ∫ x, star (E x) * E (g⁻¹ * x) = (g : ℂ) * ev 0 (evv 0)
  rw [hsub, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hg0.ne', Complex.ofReal_one,
    one_mul]

/-- The integral of `ψ g g ^ (-1/2) g N`, divided by `N`, is the integral of
`ψ g g ^ (1/2)`. -/
private theorem inv_mul_integral_halfDensity_mul {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {N : ℂ} (hN : N ≠ 0) :
    N⁻¹ * (∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((g : ℂ) * N))) =
      ∫ g, ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  change N⁻¹ * (ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((g : ℂ) * N))) =
    ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  by_cases hg : g ∈ Icc a b
  · have hg0 : 0 < g := ha0.trans_le hg.1
    have hr : g ^ (1 / 2 : ℝ) = g ^ (-(1 / 2 : ℝ)) * g := by
      rw [← Real.rpow_add_one hg0.ne']
      norm_num
    rw [hr]
    push_cast
    field_simp
  · rw [hψ0 g hg, zero_mul, zero_mul, mul_zero]

/-- Reconstruction: without weight, for a continuous test function `ψ` of the dilation
supported in `[a, b]` with `0 < a` and `b < 1`, the traces of the cutoffs of its action,
compressed to the level of band vectors vanishing at the origin, converge as the cutoff is
removed. The limit is the limit on the whole band minus the integral of `ψ g g ^ (1/2)`. For
`g > 1` the term removed is the integral of `ψ g g ^ (-1/2)`
(`exists_realPWTestCutoff_level_trace_limit`). -/
theorem exists_realPWTestCutoff_level_trace_limit_of_lt_one (hY : 0 < Y) {a b : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L (f : V₀), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((realPWZeroLevel Y 0 0 hs).starProjection f))) ∧
        (T L).val f =
          (realPWZeroLevel Y 0 0 hs).starProjection ((V₀).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 ((∫ g, ψ g * realPWSharpTraceLimit 0 g⁻¹) -
          ∫ g, ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_level_nuclear Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) = fun L ↦
      (∫ g, ψ g * realPWSharpTrace Y 0 0 hs g L) -
        (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWZeroLevelCorrection Y 0 0 hs ψ L := funext hT2
  rw [h]
  have h1 := tendsto_integral_realPWSharpTrace_of_lt_one Y hs hY ha0 hb1 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0
  have hE0 := realPWEvaluationVector_zero_ne_zero Y 0 0 hs hY le_rfl (by norm_num)
  have hN : ev 0 (evv 0) = ((‖evv 0‖ ^ 2 : ℝ) : ℂ) := by
    have h3 : ev 0 (evv 0) = ⟪evv 0, evv 0⟫_ℂ := by
      rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [h3, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hN0 : ((‖evv 0‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hE0))
  have h2 := (tendsto_realPWTestCorrection Y 0 0 hs hY le_rfl ha0 ψ hψc hψ0 (evv 0)
    (fun g ↦ (g : ℂ) * ((‖evv 0‖ ^ 2 : ℝ) : ℂ)) fun g hg ↦ by
      rw [integral_star_evaluationVector_zero_mul_dilate_of_lt_one Y hs hY
        (ha0.trans_le hg.1) (hg.2.trans_lt hb1), hN]).const_mul
    (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹
  rw [inv_mul_integral_halfDensity_mul ha0 hψ0 hN0] at h2
  exact h1.sub h2

end Unweighted

end RiemannMasullo.Isolated
