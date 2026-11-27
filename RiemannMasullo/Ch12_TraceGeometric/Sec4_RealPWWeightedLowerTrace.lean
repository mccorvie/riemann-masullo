module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedLowerTrace
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The real-place trace for dilations below one, with a weight

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, in the fixed-bandwidth model of the real
place of `ℚ` of #7354, for a dilation with `0 < g < 1` and the weight of Definition 10.1.1.1,
(10.1.1.5), p. 434.

`Sec4_RealPWUnweightedLowerTrace` treats `g < 1` without weight. There the change of variable
`x = g u` turns the sharp trace at `g` into the conjugate of the sharp trace at `g⁻¹`. With a
weight the dilation is no longer the adjoint of the reciprocal dilation, and the change of
variable puts the quotient of the weights at `g u` and at `u` into the diagonal integral.

* `realPWSharpTrace_eq_star_integral_weightRatio`. For every weight and every `g > 0`, the
  sharp trace at `g` and cutoff `L` is the conjugate of the integral over `|u| ≤ L / g` of the
  diagonal at `g⁻¹` times the quotient `w (g u) / w u`.
* `realPWIntervalWeight_zero_mul_of_inv_le`. With `s = 0` and `g ≤ 1` the quotient is the
  constant `g ^ (2 α)` on `|u| ≥ g⁻¹`.
* `realPWSharpTrace_zero_eq_of_lt_one`. With `s = 0`, `0 < g < 1` and `L ≥ 1`, the sharp trace
  at `g` is `g ^ (2 α)` times the conjugate of the sharp trace at `g⁻¹` and cutoff `L / g`,
  plus the conjugate of `realPWLowerRemainder`, an integral over `|u| ≤ g⁻¹` that does not
  depend on `L`.
* `tendsto_realPWSharpTrace_zero_of_lt_one`. So for a fixed bandwidth the limit exists. For
  `0 ≤ α < 1 / 2` it is `g ^ (2 α)` times `(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`, the
  integrand of the real term of (12.4.1.1) at `g < 1`, plus the conjugate of the remainder
  (`tendsto_realPWSharpTrace_zero_of_lt_one_of_lt_half`).
* `integral_star_evaluation_mul_dilate_eq_star_weightRatio` and
  `integral_star_evaluationVector_zero_mul_dilate_zero_of_lt_one`. The same change of variable
  for the term that the level of band vectors vanishing at the origin removes from the trace.
  With `s = 0` that term is `g ^ (1/2 + 2 α)` plus a remainder of the same kind,
  `realPWLowerPairingRemainder`.
* `exists_norm_realPWLowerRemainder_le`. For `0 ≤ α < 1 / 2` the remainder of the trace is at
  most a constant times the bandwidth, uniformly for `g` in a compact interval of `(0, 1)`.
* `exists_realPWTestCutoff_trace_limit_zero_of_lt_one`. For a test function supported in
  `0 < g < 1` the traces of the cutoffs of its action on the weighted band converge at every
  fixed bandwidth, to the integral against `realPWLowerTraceLimit`.
* `exists_test_bandwidth_trace_limit_ne_realTerm`. For `0 < α < 1 / 2` there is such a test
  function for which, at every small enough bandwidth, the limit is not the integral against
  the integrand of the real term. The single dilation is
  `exists_bandwidth_not_tendsto_realPWSharpTrace_realTerm`.

So at a fixed bandwidth the powers of `g` in the limit carry the exponent `+ 2 α` of the weight
at infinity. What the weight near the origin contributes is in the two remainders, and the
remainder of the trace is small when the bandwidth is small. For a test function supported in
`g > 1` the limit on the band is the real term for every `0 ≤ α < 1 / 2`
(`Sec4_RealPWTestTrace`). For `g < 1` it is the real term without weight
(`Sec4_RealPWUnweightedLowerTrace`), and with a weight it is not, at least for a small
bandwidth.

Reconstruction: The paper does not state this.

Not treated here: the value of the remainders at a given bandwidth, and their behaviour as the
bandwidth grows, which is the regime of the joint limit of the paper. A weight with `s > 0`,
where the quotient of the weights tends to `g ^ (2 α)` without reaching it. Test functions on
the level. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- With `s = 0` and `α ≥ 0` the weight at a point of absolute value at least one is
`|x| ^ (2 α)`. -/
theorem realPWIntervalWeight_zero_of_one_le {α : ℝ} (ha : 0 ≤ α) {x : ℝ} (hx : 1 ≤ |x|) :
    realPWIntervalWeight α 0 x = |x| ^ (2 * α) := by
  have hx0 : x ≠ 0 := abs_pos.mp (zero_lt_one.trans_le hx)
  rw [realPWIntervalWeight_eq α 0 hx0, zero_div, Real.rpow_zero, mul_one]
  exact max_eq_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith))

/-- With `s = 0`, `α ≥ 0` and `0 < g ≤ 1`, the weight at `g u` is `g ^ (2 α)` times the weight
at `u` as soon as `|u| ≥ g⁻¹`. -/
theorem realPWIntervalWeight_zero_mul_of_inv_le {α g : ℝ} (ha : 0 ≤ α) (hg0 : 0 < g)
    (hg1 : g ≤ 1) {u : ℝ} (hu : g⁻¹ ≤ |u|) :
    realPWIntervalWeight α 0 (g * u) = g ^ (2 * α) * realPWIntervalWeight α 0 u := by
  have h1 : 1 ≤ |g * u| := by
    rw [abs_mul, abs_of_pos hg0]
    calc 1 = g * g⁻¹ := (mul_inv_cancel₀ hg0.ne').symm
      _ ≤ g * |u| := mul_le_mul_of_nonneg_left hu hg0.le
  have h2 : 1 ≤ |u| := ((one_le_inv₀ hg0).mpr hg1).trans hu
  rw [realPWIntervalWeight_zero_of_one_le ha h1, realPWIntervalWeight_zero_of_one_le ha h2,
    abs_mul, abs_of_pos hg0, Real.mul_rpow hg0.le (abs_nonneg u)]

/-- The limit of the sharp trace is real. -/
theorem star_realPWSharpTraceLimit (α g : ℝ) :
    star (realPWSharpTraceLimit α g) = realPWSharpTraceLimit α g := by
  have h : realPWSharpTraceLimit α g =
      ((g ^ (-(1 / 2 : ℝ)) * g⁻¹ ^ (2 * realPWOriginJetCount α) / (1 - g⁻¹ ^ 2) : ℝ) : ℂ) := by
    rw [realPWSharpTraceLimit]
    push_cast
    rfl
  rw [h, ← starRingEnd_apply, Complex.conj_ofReal]

/-- The product of the sharp mask with a function is the indicator of the function. -/
private theorem sharpIntervalMask_mul_eq_indicator (R : ℝ) (F : ℝ → ℂ) :
    (fun u ↦ sharpIntervalMask R u * F u) = (Icc (-R) R).indicator F := by
  funext u
  by_cases h : u ∈ Icc (-R) R <;> simp [sharpIntervalMask, h]

/-- With `s = 0` the quotient of the weights at `g u` and at `u`, minus `g ^ (2 α)`, is
bounded. -/
private theorem exists_norm_weightRatio_sub_le (α : ℝ) (hs : (0 : ℝ) ≤ 0) {g : ℝ}
    (hg0 : 0 < g) :
    ∃ C : ℝ, ∀ u,
      ‖(((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ)) :
        ℂ)‖ ≤ C := by
  refine ⟨Real.exp (2 * |α * Real.log g⁻¹|) *
    (1 + |Real.log g⁻¹| + Real.log g⁻¹ ^ 2) ^ ((0 : ℝ) / 2) + g ^ (2 * α), fun u ↦ ?_⟩
  have hw : 0 < realPWIntervalWeight α 0 u :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α 0 hs u)
  have hwg : 0 < realPWIntervalWeight α 0 (g * u) :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α 0 hs (g * u))
  have h1 := realPWIntervalWeight_le_dilation (α := α) hs (inv_pos.mpr hg0) (g * u)
  rw [inv_mul_cancel_left₀ hg0.ne'] at h1
  have h2 : realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u ≤
      Real.exp (2 * |α * Real.log g⁻¹|) *
        (1 + |Real.log g⁻¹| + Real.log g⁻¹ ^ 2) ^ ((0 : ℝ) / 2) :=
    (div_le_iff₀ hw).mpr h1
  have h3 : 0 ≤ realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u :=
    (div_pos hwg hw).le
  have h4 : 0 ≤ g ^ (2 * α) := (Real.rpow_pos_of_pos hg0 _).le
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg h3, abs_of_nonneg h4]; linarith)

/-- The quotient of the weights at `g u` and at `u`, minus a constant, is measurable. -/
private theorem measurable_weightRatio_sub (α g : ℝ) :
    Measurable (fun u ↦
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ)) :
        ℂ)) :=
  Complex.continuous_ofReal.measurable.comp
    ((((measurable_realPWIntervalWeight α 0).comp (measurable_const_mul g)).div
      (measurable_realPWIntervalWeight α 0)).sub_const _)

/-- With `s = 0`, `α ≥ 0` and `0 < g < 1`, off `[-g⁻¹, g⁻¹]` the quotient of the weights at
`g u` and at `u` is `g ^ (2 α)`. -/
private theorem weightRatio_eq_of_notMem (α : ℝ) (hs : (0 : ℝ) ≤ 0) (ha : 0 ≤ α) {g : ℝ}
    (hg0 : 0 < g) (hg1 : g < 1) {u : ℝ} (hu : u ∉ Icc (-g⁻¹) g⁻¹) :
    realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u = g ^ (2 * α) := by
  have habs : g⁻¹ ≤ |u| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact hu ⟨h.1.le, h.2.le⟩
  have hw : realPWIntervalWeight α 0 u ≠ 0 :=
    (zero_lt_one.trans_le (one_le_realPWIntervalWeight α 0 hs u)).ne'
  rw [realPWIntervalWeight_zero_mul_of_inv_le ha hg0 hg1.le habs, mul_div_assoc,
    div_self hw, mul_one]

section Weighted

variable (Y α s : ℝ) (hs : 0 ≤ s)

local notation "μw" => realPWIntervalMeasure α s
local notation "hμw" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hμw
local notation "ev" => RealPWBand.evaluation Y hμw
local notation "evv" => RealPWBand.evaluationVector Y hμw
local notation "wt" => realPWIntervalWeight α s

/-- The reproducing kernel of the weighted band is Hermitian. -/
private theorem evaluation_evaluationVector_symm' (x y : ℝ) :
    (starRingEnd ℂ) (ev y (evv x)) = ev x (evv y) := by
  have h1 : ev x (evv y) = ⟪evv x, evv y⟫_ℂ := by
    rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
  have h2 : ev y (evv x) = ⟪evv y, evv x⟫_ℂ := by
    rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
  rw [h1, h2, inner_conj_symm]

/-- The sharp mask is real. -/
private theorem conj_sharpIntervalMask' (L x : ℝ) :
    (starRingEnd ℂ) (sharpIntervalMask L x) = sharpIntervalMask L x := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

/-- Reconstruction: for every weight and every `g > 0`, the sharp trace of the dilation by
`g⁻¹` at cutoff `L` is the conjugate of the integral over `|u| ≤ L / g` of the diagonal of the
dilation by `g`, multiplied by the quotient of the weights at `g u` and at `u`. This is the
change of variable `x = g u` in the diagonal integral, with the Hermitian symmetry of the
reproducing kernel. Without weight the quotient is one
(`realPWSharpTrace_zero_zero_eq_star_inv`). -/
theorem realPWSharpTrace_eq_star_integral_weightRatio {g : ℝ} (hg : 0 < g) (L : ℝ) :
    realPWSharpTrace Y α s hs g L =
      star (∫ u, sharpIntervalMask (L / g) u *
        (((wt (g * u) / wt u : ℝ) : ℂ) * realPWSharpDensity Y α s hs g⁻¹ u)) := by
  have hr1 : g ^ (1 / 2 : ℝ) = g ^ (-(1 / 2 : ℝ)) * g := by
    rw [← Real.rpow_add_one hg.ne']
    norm_num
  have hr2 : g⁻¹ ^ (-(1 / 2 : ℝ)) = g ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow hg.le, ← Real.rpow_neg hg.le, neg_neg]
  have hsub : ∫ u, sharpIntervalMask L (g * u) * realPWSharpDensity Y α s hs g (g * u) =
      |g⁻¹| • ∫ x, sharpIntervalMask L x * realPWSharpDensity Y α s hs g x :=
    Measure.integral_comp_mul_left
      (fun x ↦ sharpIntervalMask L x * realPWSharpDensity Y α s hs g x) g
  have hgg : ((g : ℝ) : ℂ) * ((g⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hg.ne', Complex.ofReal_one]
  calc realPWSharpTrace Y α s hs g L
      = (g : ℂ) * ∫ u, sharpIntervalMask L (g * u) *
          realPWSharpDensity Y α s hs g (g * u) := by
        rw [hsub, abs_of_pos (inv_pos.mpr hg), Complex.real_smul, ← mul_assoc, hgg, one_mul]
        rfl
    _ = ∫ u, (starRingEnd ℂ) (sharpIntervalMask (L / g) u *
          (((wt (g * u) / wt u : ℝ) : ℂ) * realPWSharpDensity Y α s hs g⁻¹ u)) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        have hw0 : ((wt u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
          (zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs u)).ne'
        change (g : ℂ) * (sharpIntervalMask L (g * u) *
          (((wt (g * u) * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * (g * u)) (evv (g * u)))) =
          (starRingEnd ℂ) (sharpIntervalMask (L / g) u * (((wt (g * u) / wt u : ℝ) : ℂ) *
            (((wt u * g⁻¹ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹⁻¹ * u) (evv u))))
        rw [inv_inv, hr2, map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
          conj_sharpIntervalMask', evaluation_evaluationVector_symm' Y α s hs,
          sharpIntervalMask_mul_left hg, inv_mul_cancel_left₀ hg.ne', hr1]
        push_cast
        field_simp
    _ = star (∫ u, sharpIntervalMask (L / g) u *
          (((wt (g * u) / wt u : ℝ) : ℂ) * realPWSharpDensity Y α s hs g⁻¹ u)) := by
        rw [integral_conj]
        rfl

/-- The pointwise values of a band vector are square integrable for the weighted measure. -/
private theorem memLp_evaluation' (f : V) : MemLp (fun x ↦ ev x f) 2 μw :=
  (memLp_congr_ae (RealPWBand.evaluation_ae Y hμw
    (realPWIntervalMeasure_absolutelyContinuous α s) f)).2 (Lp.memLp f.val)

/-- The product of the conjugate of one band vector with a dilate of another is integrable for
the weighted measure. -/
private theorem integrable_star_evaluation_mul_dilate' {g : ℝ} (hg : 0 < g) (e f : V) :
    Integrable (fun x ↦ star (ev x e) * ev (g⁻¹ * x) f) μw := by
  let v : ℝ → ℂ := fun x ↦ ev x f
  have hv : MemLp v 2 μw := memLp_evaluation' Y α s hs f
  have hd : MemLp (fun x ↦ v (g⁻¹ * x)) 2 μw :=
    memLp_realPWIntervalMeasure_dilation hs (inv_pos.mpr hg) hv
  have hE := memLp_evaluation' Y α s hs e
  refine (L2.integrable_inner (𝕜 := ℂ) (hE.toLp _) (hd.toLp _)).congr ?_
  filter_upwards [hE.coeFn_toLp, hd.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

/-- An integral for the weighted measure is the Lebesgue integral against the weight. -/
private theorem integral_realPWIntervalMeasure_eq_integral_mul (F : ℝ → ℂ) :
    ∫ x, F x ∂μw = ∫ x, ((wt x : ℝ) : ℂ) * F x := by
  have hWm : Measurable (fun x ↦ ENNReal.ofReal (wt x)) :=
    (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hWlt : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (wt x) < ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  change ∫ x, F x ∂(volume.withDensity fun x ↦ ENNReal.ofReal (wt x)) = _
  rw [integral_withDensity_eq_integral_toReal_smul hWm hWlt]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have hw : 0 ≤ wt x := by
    simp only [realPWIntervalWeight]
    positivity
  change (ENNReal.ofReal (wt x)).toReal • F x = _
  rw [ENNReal.toReal_ofReal hw, Complex.real_smul]

/-- Reconstruction: for every weight and every `g > 0`, the weighted pairing of a band vector
`e` with its dilate `x ↦ e (g⁻¹ x)` is `g` times the conjugate of the weighted pairing of `e`
with its dilate `u ↦ e (g u)`, with the quotient of the weights at `g u` and at `u` inserted.
This is the change of variable `x = g u`. With `e` the evaluation vector at the origin the
left side, times `g ^ (-1/2)` and divided by the square of the norm of `e`, is the term that
the level of band vectors vanishing at the origin removes from the trace. -/
theorem integral_star_evaluation_mul_dilate_eq_star_weightRatio {g : ℝ} (hg : 0 < g) (e : V) :
    ∫ x, star (ev x e) * ev (g⁻¹ * x) e ∂μw =
      (g : ℂ) * star (∫ u, ((wt (g * u) / wt u : ℝ) : ℂ) *
        (star (ev u e) * ev (g * u) e) ∂μw) := by
  have hsub : ∫ u, ((wt (g * u) : ℝ) : ℂ) *
      (star (ev (g * u) e) * ev (g⁻¹ * (g * u)) e) =
      |g⁻¹| • ∫ x, ((wt x : ℝ) : ℂ) * (star (ev x e) * ev (g⁻¹ * x) e) :=
    Measure.integral_comp_mul_left
      (fun x ↦ ((wt x : ℝ) : ℂ) * (star (ev x e) * ev (g⁻¹ * x) e)) g
  have hgg : ((g : ℝ) : ℂ) * ((g⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hg.ne', Complex.ofReal_one]
  have h1 := integral_realPWIntervalMeasure_eq_integral_mul α s
    (fun x ↦ star (ev x e) * ev (g⁻¹ * x) e)
  have h2 := integral_realPWIntervalMeasure_eq_integral_mul α s
    (fun u ↦ ((wt (g * u) / wt u : ℝ) : ℂ) * (star (ev u e) * ev (g * u) e))
  rw [h1, h2]
  calc ∫ x, ((wt x : ℝ) : ℂ) * (star (ev x e) * ev (g⁻¹ * x) e)
      = (g : ℂ) * ∫ u, ((wt (g * u) : ℝ) : ℂ) *
          (star (ev (g * u) e) * ev (g⁻¹ * (g * u)) e) := by
        rw [hsub, abs_of_pos (inv_pos.mpr hg), Complex.real_smul, ← mul_assoc, hgg, one_mul]
    _ = (g : ℂ) * ∫ u, (starRingEnd ℂ) (((wt u : ℝ) : ℂ) *
          (((wt (g * u) / wt u : ℝ) : ℂ) * (star (ev u e) * ev (g * u) e))) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        have hw0 : ((wt u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
          (zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs u)).ne'
        change ((wt (g * u) : ℝ) : ℂ) * (star (ev (g * u) e) * ev (g⁻¹ * (g * u)) e) =
          (starRingEnd ℂ) (((wt u : ℝ) : ℂ) *
            (((wt (g * u) / wt u : ℝ) : ℂ) * (star (ev u e) * ev (g * u) e)))
        rw [inv_mul_cancel_left₀ hg.ne', map_mul, map_mul, map_mul, Complex.conj_ofReal,
          Complex.conj_ofReal, starRingEnd_apply, starRingEnd_apply, star_star]
        push_cast
        field_simp
    _ = (g : ℂ) * star (∫ u, ((wt u : ℝ) : ℂ) *
          (((wt (g * u) / wt u : ℝ) : ℂ) * (star (ev u e) * ev (g * u) e))) := by
        rw [integral_conj]
        rfl

end Weighted

section PowerWeight

variable (Y α : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- With `s = 0`, the part of the weighted sharp trace at `g < 1` that comes from the points
`|u| ≤ g⁻¹`, where the quotient of the weights at `g u` and at `u` differs from its value
`g ^ (2 α)` at infinity. It does not depend on the cutoff. -/
def realPWLowerRemainder (Y α : ℝ) (hs : (0 : ℝ) ≤ 0) (g : ℝ) : ℂ :=
  ∫ u, sharpIntervalMask g⁻¹ u *
    (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) : ℂ) *
      realPWSharpDensity Y α 0 hs g⁻¹ u)

/-- Reconstruction: with `s = 0`, `α ≥ 0`, `0 < g < 1` and cutoff `L ≥ 1`, the sharp trace of
the dilation by `g⁻¹` is `g ^ (2 α)` times the conjugate of the sharp trace of the dilation by
`g` at cutoff `L / g`, plus the conjugate of `realPWLowerRemainder`. The identity is exact: on
`|u| ≥ g⁻¹` the quotient of the weights is `g ^ (2 α)`. -/
theorem realPWSharpTrace_zero_eq_of_lt_one (hY : 0 ≤ Y) (ha : 0 ≤ α) {g : ℝ} (hg0 : 0 < g)
    (hg1 : g < 1) {L : ℝ} (hL : 1 ≤ L) :
    realPWSharpTrace Y α 0 hs g L =
      ((g ^ (2 * α) : ℝ) : ℂ) * star (realPWSharpTrace Y α 0 hs g⁻¹ (L / g)) +
        star (realPWLowerRemainder Y α hs g) := by
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr hg1
  have hc : ((g ^ (2 * α) : ℝ) : ℂ) * star (realPWSharpTrace Y α 0 hs g⁻¹ (L / g)) =
      star (((g ^ (2 * α) : ℝ) : ℂ) * realPWSharpTrace Y α 0 hs g⁻¹ (L / g)) := by
    rw [star_mul', ← starRingEnd_apply ((g ^ (2 * α) : ℝ) : ℂ), Complex.conj_ofReal]
  rw [realPWSharpTrace_eq_star_integral_weightRatio Y α 0 hs hg0 L, hc, ← star_add]
  congr 1
  have hI1 : Integrable (fun u ↦ sharpIntervalMask (L / g) u *
      realPWSharpDensity Y α 0 hs g⁻¹ u) := by
    rw [sharpIntervalMask_mul_eq_indicator, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_realPWSharpDensity hY ha hs hinv (L / g)
  obtain ⟨C, hC⟩ := exists_norm_weightRatio_sub_le α hs hg0
  have hI2 : Integrable (fun u ↦ sharpIntervalMask g⁻¹ u *
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) : ℂ) *
        realPWSharpDensity Y α 0 hs g⁻¹ u)) := by
    rw [sharpIntervalMask_mul_eq_indicator, integrable_indicator_iff measurableSet_Icc]
    refine Integrable.bdd_mul (c := C) (integrableOn_realPWSharpDensity hY ha hs hinv g⁻¹) ?_
      (ae_of_all _ hC)
    exact (measurable_weightRatio_sub α g).aestronglyMeasurable
  change ∫ u, sharpIntervalMask (L / g) u *
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u : ℝ) : ℂ) *
        realPWSharpDensity Y α 0 hs g⁻¹ u) =
    ((g ^ (2 * α) : ℝ) : ℂ) * (∫ u, sharpIntervalMask (L / g) u *
      realPWSharpDensity Y α 0 hs g⁻¹ u) +
    ∫ u, sharpIntervalMask g⁻¹ u *
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) : ℂ) *
        realPWSharpDensity Y α 0 hs g⁻¹ u)
  rw [← integral_const_mul, ← integral_add (hI1.const_mul _) hI2]
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  change sharpIntervalMask (L / g) u *
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u : ℝ) : ℂ) *
        realPWSharpDensity Y α 0 hs g⁻¹ u) =
    ((g ^ (2 * α) : ℝ) : ℂ) * (sharpIntervalMask (L / g) u *
      realPWSharpDensity Y α 0 hs g⁻¹ u) +
    sharpIntervalMask g⁻¹ u *
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) : ℂ) *
        realPWSharpDensity Y α 0 hs g⁻¹ u)
  by_cases hu : u ∈ Icc (-g⁻¹) g⁻¹
  · have hle : g⁻¹ ≤ L / g := by
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left (inv_pos.mpr hg0).le hL
    have hu' : u ∈ Icc (-(L / g)) (L / g) := ⟨(neg_le_neg hle).trans hu.1, hu.2.trans hle⟩
    simp only [sharpIntervalMask, indicator_of_mem hu, indicator_of_mem hu', Pi.one_apply,
      one_mul]
    push_cast
    ring
  · have hr := weightRatio_eq_of_notMem α hs ha hg0 hg1 hu
    rw [hr, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    ring

/-- Reconstruction: with `s = 0`, `α ≥ 0` and `0 < g < 1`, at a fixed bandwidth the sharp
traces of the dilation by `g⁻¹` converge as the cutoff is removed. The limit is `g ^ (2 α)`
times the limit for the reciprocal dilation, plus the conjugate of `realPWLowerRemainder`. -/
theorem tendsto_realPWSharpTrace_zero_of_lt_one (hY : 0 < Y) (ha : 0 ≤ α) {g : ℝ}
    (hg0 : 0 < g) (hg1 : g < 1) :
    Tendsto (fun L ↦ realPWSharpTrace Y α 0 hs g L) atTop
      (𝓝 (((g ^ (2 * α) : ℝ) : ℂ) * realPWSharpTraceLimit α g⁻¹ +
        star (realPWLowerRemainder Y α hs g))) := by
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr hg1
  obtain ⟨-, hlim⟩ := exists_bound_and_tendsto_realPWSharpTrace (Y := Y) (α := α) (s := 0) hY
    ha hs hinv g⁻¹
  have h1 : Tendsto (fun L : ℝ ↦ L / g) atTop atTop := tendsto_id.atTop_div_const hg0
  have h2 := (continuous_star.tendsto _).comp ((hlim g⁻¹ ⟨le_rfl, le_rfl⟩).comp h1)
  rw [star_realPWSharpTraceLimit] at h2
  refine ((h2.const_mul ((g ^ (2 * α) : ℝ) : ℂ)).add_const
    (star (realPWLowerRemainder Y α hs g))).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  exact (realPWSharpTrace_zero_eq_of_lt_one Y α hs hY.le ha hg0 hg1 hL).symm

/-- Reconstruction: with `s = 0`, `0 ≤ α < 1 / 2` and `0 < g < 1`, at a fixed bandwidth the
sharp traces of the dilation by `g⁻¹` converge to `g ^ (2 α)` times
`(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`, plus the conjugate of `realPWLowerRemainder`.
Paper: the second factor is the integrand of the real term of (12.4.1.1), p. 514, at `g < 1`.
Without weight the factor `g ^ (2 α)` is one and the remainder is zero. -/
theorem tendsto_realPWSharpTrace_zero_of_lt_one_of_lt_half (hY : 0 < Y) (ha : 0 ≤ α)
    (hα : α < 1 / 2) {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) :
    Tendsto (fun L ↦ realPWSharpTrace Y α 0 hs g L) atTop
      (𝓝 (((g ^ (2 * α) : ℝ) : ℂ) *
          ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
        star (realPWLowerRemainder Y α hs g))) := by
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr hg1
  have h := tendsto_realPWSharpTrace_zero_of_lt_one Y α hs hY ha hg0 hg1
  rwa [realPWSharpTraceLimit_of_lt_half hα hinv,
    ← realPWSharpTraceLimit_of_lt_half (α := 0) (by norm_num) hinv,
    realPWSharpTraceLimit_zero_inv hg0 hg1] at h

local notation "μp" => realPWIntervalMeasure α 0
local notation "hμp" => volume_le_realPWIntervalMeasure α 0 hs
local notation "evp" => RealPWBand.evaluation Y hμp
local notation "evvp" => RealPWBand.evaluationVector Y hμp

/-- With `s = 0`, the part of the weighted pairing of the evaluation vector at the origin with
its dilate, at `g < 1`, that comes from the points `|u| ≤ g⁻¹`, where the quotient of the
weights at `g u` and at `u` differs from its value `g ^ (2 α)` at infinity. -/
def realPWLowerPairingRemainder (g : ℝ) : ℂ :=
  ∫ u, sharpIntervalMask g⁻¹ u *
    (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) : ℂ) *
      (star (evp u (evvp 0)) * evp (g * u) (evvp 0))) ∂μp

/-- Reconstruction: with `s = 0`, `α ≥ 0` and `0 < g < 1`, the weighted pairing of the
evaluation vector at the origin with its dilate `x ↦ e (g⁻¹ x)` is `g` times the sum of
`g ^ (2 α)` times its value at the origin and the conjugate of
`realPWLowerPairingRemainder`. Without weight this is `g` times the value at the origin
(`integral_star_evaluationVector_zero_mul_dilate_of_lt_one`). Times `g ^ (-1/2)` and divided by
the value at the origin, it is the term that the level of band vectors vanishing at the origin
removes from the trace: `g ^ (1/2 + 2 α)` plus a remainder. -/
theorem integral_star_evaluationVector_zero_mul_dilate_zero_of_lt_one (hY : 0 < Y)
    (ha : 0 ≤ α) {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) :
    ∫ x, star (evp x (evvp 0)) * evp (g⁻¹ * x) (evvp 0) ∂μp =
      (g : ℂ) * (((g ^ (2 * α) : ℝ) : ℂ) * evp 0 (evvp 0) +
        star (realPWLowerPairingRemainder Y α hs g)) := by
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hg0).mpr hg1
  let H : ℝ → ℂ := fun u ↦ star (evp u (evvp 0)) * evp (g * u) (evvp 0)
  have hH : Integrable H μp := by
    have h := integrable_star_evaluation_mul_dilate' Y α 0 hs (inv_pos.mpr hg0) (evvp 0)
      (evvp 0)
    simp only [inv_inv] at h
    exact h
  have hup : ∫ u, H u ∂μp = evp 0 (evvp 0) := by
    have h := integral_star_evaluationVector_zero_mul_dilate Y α 0 hs hY hinv (evvp 0)
    simp only [inv_inv] at h
    exact h
  have hreal : (starRingEnd ℂ) (evp 0 (evvp 0)) = evp 0 (evvp 0) :=
    evaluation_evaluationVector_symm' Y α 0 hs 0 0
  obtain ⟨C, hC⟩ := exists_norm_weightRatio_sub_le α hs hg0
  have hI2 : Integrable (fun u ↦ sharpIntervalMask g⁻¹ u *
      (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) : ℂ) *
        H u)) μp := by
    rw [sharpIntervalMask_mul_eq_indicator, integrable_indicator_iff measurableSet_Icc]
    exact (Integrable.bdd_mul (c := C) hH (measurable_weightRatio_sub α g).aestronglyMeasurable
      (ae_of_all _ hC)).integrableOn
  have hsplit : ∫ u, ((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u : ℝ) : ℂ) *
      H u ∂μp =
      ((g ^ (2 * α) : ℝ) : ℂ) * ∫ u, H u ∂μp + realPWLowerPairingRemainder Y α hs g := by
    rw [← integral_const_mul]
    change _ = (∫ u, ((g ^ (2 * α) : ℝ) : ℂ) * H u ∂μp) +
      ∫ u, sharpIntervalMask g⁻¹ u *
        (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) :
          ℂ) * H u) ∂μp
    rw [← integral_add (hH.const_mul _) hI2]
    refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
    change ((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u : ℝ) : ℂ) * H u =
      ((g ^ (2 * α) : ℝ) : ℂ) * H u + sharpIntervalMask g⁻¹ u *
        (((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ) :
          ℂ) * H u)
    by_cases hu : u ∈ Icc (-g⁻¹) g⁻¹
    · simp only [sharpIntervalMask, indicator_of_mem hu, Pi.one_apply, one_mul]
      push_cast
      ring
    · rw [weightRatio_eq_of_notMem α hs ha hg0 hg1 hu, sub_self, Complex.ofReal_zero, zero_mul,
        mul_zero, add_zero]
  rw [integral_star_evaluation_mul_dilate_eq_star_weightRatio Y α 0 hs hg0 (evvp 0)]
  congr 1
  change star (∫ u, ((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u : ℝ) : ℂ) *
    H u ∂μp) = _
  rw [hsplit, hup, star_add, star_mul', ← starRingEnd_apply ((g ^ (2 * α) : ℝ) : ℂ),
    Complex.conj_ofReal, ← starRingEnd_apply (evp 0 (evvp 0)), hreal]

/-- With `s = 0` and `0 < g ≤ 1`, the diagonal of the dilation by `g` is at most the weight
times twice the bandwidth. -/
theorem norm_realPWSharpDensity_zero_inv_le (hY : 0 ≤ Y) {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (u : ℝ) :
    ‖realPWSharpDensity Y α 0 hs g⁻¹ u‖ ≤ realPWIntervalWeight α 0 u * (2 * Y) := by
  have hw0 : 0 ≤ realPWIntervalWeight α 0 u :=
    zero_le_one.trans (one_le_realPWIntervalWeight α 0 hs u)
  have hr2 : g⁻¹ ^ (-(1 / 2 : ℝ)) = g ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow hg0.le, ← Real.rpow_neg hg0.le, neg_neg]
  have hpow : g⁻¹ ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    rw [hr2]
    exact Real.rpow_le_one hg0.le hg1 (by norm_num)
  have hpow0 : 0 ≤ g⁻¹ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (inv_nonneg.mpr hg0.le) _
  have h2Y : 0 ≤ 2 * Y := mul_nonneg zero_le_two hY
  have hev : ‖evp (g⁻¹⁻¹ * u) (evvp u)‖ ≤ 2 * Y := by
    calc ‖evp (g⁻¹⁻¹ * u) (evvp u)‖ ≤ ‖evp (g⁻¹⁻¹ * u)‖ * ‖evvp u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.sqrt (2 * Y) * Real.sqrt (2 * Y) :=
          mul_le_mul (RealPWBand.norm_evaluation_le Y hY hμp _)
            (RealPWBand.norm_evaluationVector_le Y hY hμp u) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 * Y := Real.mul_self_sqrt h2Y
  change ‖((realPWIntervalWeight α 0 u * g⁻¹ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    evp (g⁻¹⁻¹ * u) (evvp u)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 hpow0)]
  calc realPWIntervalWeight α 0 u * g⁻¹ ^ (-(1 / 2 : ℝ)) * ‖evp (g⁻¹⁻¹ * u) (evvp u)‖
      ≤ realPWIntervalWeight α 0 u * 1 * (2 * Y) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hw0) hev (norm_nonneg _)
          (mul_nonneg hw0 zero_le_one)
    _ = realPWIntervalWeight α 0 u * (2 * Y) := by ring

end PowerWeight

section SmallBandwidth

variable (α : ℝ) (hs : (0 : ℝ) ≤ 0)

include hs in
/-- With `s = 0`, one constant bounds the quotient of the weights at `g u` and at `u`, minus
`g ^ (2 α)`, for all `g` in a compact interval of `(0, 1]`. -/
private theorem exists_norm_weightRatio_sub_le_uniform (ha : 0 ≤ α) {a : ℝ} (ha0 : 0 < a)
    {b : ℝ} (hb1 : b ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ Icc a b, ∀ u : ℝ,
      ‖(((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ)) :
        ℂ)‖ ≤ C := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_realPWIntervalWeight_le_dilation_of_pos (α := α) (s := 0) hs ha0 b
  refine ⟨K + 1, by linarith, fun g hg u ↦ ?_⟩
  have hg0 : 0 < g := ha0.trans_le hg.1
  have hw : 0 < realPWIntervalWeight α 0 u :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α 0 hs u)
  have hwg : 0 < realPWIntervalWeight α 0 (g * u) :=
    zero_lt_one.trans_le (one_le_realPWIntervalWeight α 0 hs (g * u))
  have h1 := hK g hg (g * u)
  rw [inv_mul_cancel_left₀ hg0.ne'] at h1
  have h2 : realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u ≤ K :=
    (div_le_iff₀ hw).mpr h1
  have h3 : 0 ≤ realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u :=
    (div_pos hwg hw).le
  have h4 : 0 ≤ g ^ (2 * α) := (Real.rpow_pos_of_pos hg0 _).le
  have h5 : g ^ (2 * α) ≤ 1 :=
    Real.rpow_le_one hg0.le (hg.2.trans hb1) (mul_nonneg zero_le_two ha)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg h3, abs_of_nonneg h4]; linarith)

/-- Reconstruction: with `s = 0` and `0 ≤ α < 1 / 2`, the remainder of the weighted sharp trace
at `g < 1` is at most a constant times the bandwidth. The constant is the same for all `g` in a
compact interval of `(0, 1)`, and does not depend on the bandwidth. The evaluation vectors of
the band have norm at most the square root of twice the bandwidth, and for these widths the
weight is integrable near the origin. -/
theorem exists_norm_realPWLowerRemainder_le (ha : 0 ≤ α) (hα : α < 1 / 2) {a b : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ Y : ℝ, 0 ≤ Y → ∀ g ∈ Icc a b,
      ‖realPWLowerRemainder Y α hs g‖ ≤ D * Y := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_weightRatio_sub_le_uniform α hs ha ha0 hb1.le
  have hwI : IntegrableOn (realPWIntervalWeight α 0) (Icc (-a⁻¹) a⁻¹) := by
    have h := integrableOn_abs_rpow_mul_realPWIntervalWeight (α := α) (s := 0) (p := 0)
      (R := a⁻¹) ha hs (by linarith)
    simpa only [Real.rpow_zero, one_mul] using h
  have hw0 : ∀ u, 0 ≤ realPWIntervalWeight α 0 u := fun u ↦
    zero_le_one.trans (one_le_realPWIntervalWeight α 0 hs u)
  have hI0 : 0 ≤ ∫ u in Icc (-a⁻¹) a⁻¹, realPWIntervalWeight α 0 u :=
    setIntegral_nonneg measurableSet_Icc fun u _ ↦ hw0 u
  refine ⟨C * 2 * ∫ u in Icc (-a⁻¹) a⁻¹, realPWIntervalWeight α 0 u,
    mul_nonneg (mul_nonneg hC0 zero_le_two) hI0, fun Y hY g hg ↦ ?_⟩
  have hg0 : 0 < g := ha0.trans_le hg.1
  have hg1 : g < 1 := hg.2.trans_lt hb1
  have hpt : ∀ u, ‖sharpIntervalMask g⁻¹ u *
      ((((realPWIntervalWeight α 0 (g * u) / realPWIntervalWeight α 0 u - g ^ (2 * α) : ℝ)) :
        ℂ) * realPWSharpDensity Y α 0 hs g⁻¹ u)‖ ≤
      (Icc (-a⁻¹) a⁻¹).indicator (fun u ↦ C * 2 * Y * realPWIntervalWeight α 0 u) u := by
    intro u
    by_cases hu : u ∈ Icc (-g⁻¹) g⁻¹
    · have hle : g⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hg.1
      have hu' : u ∈ Icc (-a⁻¹) a⁻¹ := ⟨(neg_le_neg hle).trans hu.1, hu.2.trans hle⟩
      have hmask : sharpIntervalMask g⁻¹ u = 1 := by simp [sharpIntervalMask, hu]
      rw [indicator_of_mem hu', hmask, one_mul, norm_mul]
      calc _ ≤ C * (realPWIntervalWeight α 0 u * (2 * Y)) :=
            mul_le_mul (hC g hg u) (norm_realPWSharpDensity_zero_inv_le Y α hs hY hg0 hg1.le u)
              (norm_nonneg _) hC0
        _ = C * 2 * Y * realPWIntervalWeight α 0 u := by ring
    · have hmask : sharpIntervalMask g⁻¹ u = 0 := by simp [sharpIntervalMask, hu]
      rw [hmask, zero_mul, norm_zero]
      exact indicator_nonneg (fun u _ ↦
        mul_nonneg (mul_nonneg (mul_nonneg hC0 zero_le_two) hY) (hw0 u)) u
  calc ‖realPWLowerRemainder Y α hs g‖
      ≤ ∫ u, (Icc (-a⁻¹) a⁻¹).indicator
          (fun u ↦ C * 2 * Y * realPWIntervalWeight α 0 u) u :=
        norm_integral_le_of_norm_le
          ((integrable_indicator_iff measurableSet_Icc).mpr (hwI.const_mul _))
          (ae_of_all _ hpt)
    _ = C * 2 * (∫ u in Icc (-a⁻¹) a⁻¹, realPWIntervalWeight α 0 u) * Y := by
        rw [integral_indicator measurableSet_Icc, integral_const_mul]
        ring

/-- Reconstruction: with `s = 0`, `0 < α < 1 / 2` and `0 < g < 1`, for every small enough
bandwidth the sharp traces of the dilation by `g⁻¹` do not converge to
`(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`. They converge to `g ^ (2 α)` times that number
plus a remainder of size at most a constant times the bandwidth
(`tendsto_realPWSharpTrace_zero_of_lt_one_of_lt_half`, `exists_norm_realPWLowerRemainder_le`),
and `g ^ (2 α) < 1`.
Paper: the number is the integrand of the real term of (12.4.1.1), p. 514, at `g < 1`. -/
theorem exists_bandwidth_not_tendsto_realPWSharpTrace_realTerm (ha : 0 < α) (hα : α < 1 / 2)
    {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) :
    ∃ Y₀ : ℝ, 0 < Y₀ ∧ ∀ Y : ℝ, 0 < Y → Y < Y₀ →
      ¬ Tendsto (fun L ↦ realPWSharpTrace Y α 0 hs g L) atTop
        (𝓝 ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_realPWLowerRemainder_le α hs ha.le hα hg0 hg1
    (a := g) (b := g)
  have hP0 : 0 < 1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) := by
    have h1 : 0 < (1 - g)⁻¹ := inv_pos.mpr (by linarith)
    have h2 : 0 < (1 + g)⁻¹ := inv_pos.mpr (by linarith)
    have h3 : 0 < g ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hg0 _
    positivity
  have hc1 : g ^ (2 * α) < 1 := Real.rpow_lt_one hg0.le hg1 (mul_pos two_pos ha)
  have hδ : 0 < (1 - g ^ (2 * α)) * (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) :=
    mul_pos (sub_pos.mpr hc1) hP0
  have hD1 : 0 < D + 1 := by linarith
  refine ⟨(1 - g ^ (2 * α)) * (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) / (D + 1),
    div_pos hδ hD1, fun Y hY hYlt hlim ↦ ?_⟩
  have h1 := tendsto_realPWSharpTrace_zero_of_lt_one_of_lt_half Y α hs hY ha.le hα hg0 hg1
  have heq := tendsto_nhds_unique hlim h1
  have hR : star (realPWLowerRemainder Y α hs g) =
      (((1 - g ^ (2 * α)) * (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
    push_cast
    push_cast at heq
    linear_combination -heq
  have hnorm : ‖realPWLowerRemainder Y α hs g‖ =
      (1 - g ^ (2 * α)) * (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) := by
    rw [← norm_star, hR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hle := hD Y hY.le g ⟨le_rfl, le_rfl⟩
  rw [hnorm] at hle
  have h2 : D * Y ≤ D * ((1 - g ^ (2 * α)) *
      (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) / (D + 1)) :=
    mul_le_mul_of_nonneg_left hYlt.le hD0
  have h3 : D * ((1 - g ^ (2 * α)) *
      (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) / (D + 1)) <
      (1 - g ^ (2 * α)) * (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) := by
    rw [mul_div_assoc', div_lt_iff₀ hD1]
    nlinarith
  linarith

end SmallBandwidth

section TestFunctions

/-- The limit of the weighted sharp trace of the dilation by `g⁻¹` at `0 < g < 1`, with `s = 0`
and `0 ≤ α < 1 / 2`: `g ^ (2 α)` times the integrand of the real term of (12.4.1.1), p. 514,
plus the conjugate of `realPWLowerRemainder`. -/
def realPWLowerTraceLimit (Y α : ℝ) (hs : (0 : ℝ) ≤ 0) (g : ℝ) : ℂ :=
  ((g ^ (2 * α) : ℝ) : ℂ) * ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
    star (realPWLowerRemainder Y α hs g)

variable (Y α : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μp" => realPWIntervalMeasure α 0
local notation "hμp" => volume_le_realPWIntervalMeasure α 0 hs
local notation "Vp" => RealPWBand.space Y hμp
local notation "evp" => RealPWBand.evaluation Y hμp

/-- With `s = 0` and `0 ≤ α < 1 / 2`, the weighted sharp traces at cutoffs `L ≥ 1` are bounded
uniformly for `g` in a compact interval of `(0, 1)`. -/
private theorem exists_bound_realPWSharpTrace_zero_of_lt_one (hY : 0 < Y) (ha : 0 ≤ α)
    (hα : α < 1 / 2) {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1) :
    ∃ B : ℝ, ∀ g ∈ Icc a b, ∀ L : ℝ, 1 ≤ L → ‖realPWSharpTrace Y α 0 hs g L‖ ≤ B := by
  have hb0 : 0 < b := ha0.trans_le hab
  have hb1' : 1 < b⁻¹ := (one_lt_inv₀ hb0).mpr hb1
  obtain ⟨⟨B₀, hB₀⟩, -⟩ := exists_bound_and_tendsto_realPWSharpTrace (Y := Y) (α := α)
    (s := 0) hY ha hs hb1' a⁻¹
  obtain ⟨D, -, hD⟩ := exists_norm_realPWLowerRemainder_le α hs ha hα ha0 hb1
  refine ⟨B₀ + D * Y, fun g hg L hL ↦ ?_⟩
  have hg0 : 0 < g := ha0.trans_le hg.1
  have hg1 : g < 1 := hg.2.trans_lt hb1
  have hmem : g⁻¹ ∈ Icc b⁻¹ a⁻¹ := ⟨inv_anti₀ hg0 hg.2, inv_anti₀ ha0 hg.1⟩
  have hc0 : 0 ≤ g ^ (2 * α) := (Real.rpow_pos_of_pos hg0 _).le
  have hc1 : g ^ (2 * α) ≤ 1 := Real.rpow_le_one hg0.le hg1.le (mul_nonneg zero_le_two ha)
  rw [realPWSharpTrace_zero_eq_of_lt_one Y α hs hY.le ha hg0 hg1 hL]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc g ^ (2 * α) * ‖realPWSharpTrace Y α 0 hs g⁻¹ (L / g)‖
        ≤ 1 * ‖realPWSharpTrace Y α 0 hs g⁻¹ (L / g)‖ :=
          mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
      _ ≤ B₀ := by
          rw [one_mul]
          exact hB₀ g⁻¹ hmem _
  · rw [norm_star]
    exact hD Y hY.le g hg

/-- Reconstruction: with `s = 0` and `0 ≤ α < 1 / 2`, the weighted sharp trace of the dilation
by `g⁻¹`, integrated against a function of `g` supported in `[a, b]` with `0 < a` and `b < 1`,
converges as the cutoff is removed to the integral against `realPWLowerTraceLimit`. The product
with the limit is integrable. -/
theorem tendsto_integral_realPWSharpTrace_zero_of_lt_one (hY : 0 < Y) (ha : 0 ≤ α)
    (hα : α < 1 / 2) {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    Integrable (fun g ↦ ψ g * realPWLowerTraceLimit Y α hs g) ∧
      Tendsto (fun L ↦ ∫ g, ψ g * realPWSharpTrace Y α 0 hs g L) atTop
        (𝓝 (∫ g, ψ g * realPWLowerTraceLimit Y α hs g)) := by
  by_cases hab : a ≤ b
  swap
  · have hz : ∀ g, ψ g = 0 := fun g ↦ hψ0 g fun hg ↦ hab (hg.1.trans hg.2)
    simp only [hz, zero_mul, integral_zero]
    exact ⟨integrable_zero _ _ _, tendsto_const_nhds⟩
  obtain ⟨B, hB⟩ := exists_bound_realPWSharpTrace_zero_of_lt_one Y α hs hY ha hα ha0 hab hb1
  have hlim : ∀ g, Tendsto (fun L ↦ ψ g * realPWSharpTrace Y α 0 hs g L) atTop
      (𝓝 (ψ g * realPWLowerTraceLimit Y α hs g)) := by
    intro g
    by_cases hg : g ∈ Icc a b
    · exact (tendsto_realPWSharpTrace_zero_of_lt_one_of_lt_half Y α hs hY ha hα
        (ha0.trans_le hg.1) (hg.2.trans_lt hb1)).const_mul (ψ g)
    · simp only [hψ0 g hg, zero_mul]
      exact tendsto_const_nhds
  have hmeas : ∀ L : ℝ, AEStronglyMeasurable
      (fun g ↦ ψ g * realPWSharpTrace Y α 0 hs g L) := fun L ↦
    hψ.aestronglyMeasurable.mul (measurable_realPWSharpTrace hs L).aestronglyMeasurable
  have hbd : ∀ L : ℝ, 1 ≤ L → ∀ g, ‖ψ g * realPWSharpTrace Y α 0 hs g L‖ ≤ ‖ψ g‖ * B := by
    intro L hL g
    by_cases hg : g ∈ Icc a b
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB g hg L hL) (norm_nonneg _)
    · rw [hψ0 g hg, zero_mul, norm_zero, zero_mul]
  refine ⟨?_, tendsto_integral_filter_of_dominated_convergence (fun g ↦ ‖ψ g‖ * B)
    (.of_forall hmeas) ((eventually_ge_atTop 1).mono fun L hL ↦ ae_of_all _ (hbd L hL))
    (hψ.norm.mul_const _) (ae_of_all _ hlim)⟩
  refine (hψ.norm.mul_const B).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop hmeas (ae_of_all _ hlim)) (ae_of_all _ fun g ↦ ?_)
  exact le_of_tendsto (hlim g).norm ((eventually_ge_atTop 1).mono fun L hL ↦ hbd L hL g)

/-- Reconstruction: with `s = 0` and `0 ≤ α < 1 / 2`, for a continuous test function `ψ` of the
dilation supported in `[a, b]` with `0 < a` and `b < 1`, the traces of the sharp cutoffs of its
action on the weighted even band converge as the cutoff is removed, at every fixed bandwidth.
The limit is the integral of `ψ` against `realPWLowerTraceLimit`.
Paper: this is the real-place term of Theorem 12.4.1.1, pp. 514–517, in the fixed-bandwidth
model of the real place of `ℚ`, for a test function supported in `0 < g < 1`. The limit is not
the real term: see `exists_norm_integral_realPWLowerTraceLimit_sub_le`. -/
theorem exists_realPWTestCutoff_trace_limit_zero_of_lt_one (hY : 0 < Y) (ha : 0 ≤ α)
    (hα : α < 1 / 2) {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    ∃ T : ℝ → nuclearEndomorphisms Vp,
      (∀ L (f : Vp), ∃ r : Lp ℂ 2 μp,
        (∀ᵐ x ∂μp, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * evp (g⁻¹ * x) f)) ∧
        (T L).val f = (Vp).orthogonalProjectionOnto r) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g * realPWLowerTraceLimit Y α hs g)) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_nuclear Y α 0 hs hY ha ha0 ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) =
      fun L ↦ ∫ g, ψ g * realPWSharpTrace Y α 0 hs g L := funext hT2
  rw [h]
  exact (tendsto_integral_realPWSharpTrace_zero_of_lt_one Y α hs hY ha hα ha0 hb1 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0).2

end TestFunctions

section TestFunctionBound

variable (α : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- Reconstruction: with `s = 0` and `0 ≤ α < 1 / 2`, the limit of the traces for a test
function `ψ` supported in `[a, b]`, `0 < a`, `b < 1`, differs from the integral of `ψ` against
`g ^ (2 α)` times the integrand of the real term of (12.4.1.1) by at most a constant times the
bandwidth times the integral of `|ψ|`. The constant does not depend on the bandwidth or on the
test function. So for a small bandwidth the limit is close to the real term with the extra
factor `g ^ (2 α)`, and for `α > 0` it is not the real term. -/
theorem exists_norm_integral_realPWLowerTraceLimit_sub_le (ha : 0 ≤ α) (hα : α < 1 / 2)
    {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ Y : ℝ, 0 < Y → ∀ ψ : ℝ → ℂ, Continuous ψ →
      (∀ g ∉ Icc a b, ψ g = 0) →
      ‖(∫ g, ψ g * realPWLowerTraceLimit Y α hs g) -
        ∫ g, ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
          ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))‖ ≤
        D * Y * ∫ g, ‖ψ g‖ := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_realPWLowerRemainder_le α hs ha hα ha0 hb1
  refine ⟨D, hD0, fun Y hY ψ hψc hψ0 ↦ ?_⟩
  have hψ : Integrable ψ :=
    hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)
  have hI1 := (tendsto_integral_realPWSharpTrace_zero_of_lt_one Y α hs hY ha hα ha0 hb1 ψ hψ
    hψ0).1
  have hcont : ContinuousOn (fun g : ℝ ↦ ((g ^ (2 * α) : ℝ) : ℂ) *
      ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) (Icc a b) := by
    have h0 : ContinuousOn (fun g : ℝ ↦ g ^ (2 * α)) (Icc a b) :=
      (Real.continuous_rpow_const (mul_nonneg zero_le_two ha)).continuousOn
    have h1 : ContinuousOn (fun g : ℝ ↦ (1 - g)⁻¹) (Icc a b) :=
      ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.2] : (0 : ℝ) < 1 - g).ne'
    have h2 : ContinuousOn (fun g : ℝ ↦ (1 + g)⁻¹) (Icc a b) :=
      ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.1] : (0 : ℝ) < 1 + g).ne'
    have h3 : ContinuousOn (fun g : ℝ ↦ g ^ (1 / 2 : ℝ)) (Icc a b) :=
      (Real.continuous_rpow_const (by norm_num)).continuousOn
    exact (Complex.continuous_ofReal.comp_continuousOn h0).mul
      (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_const.mul (h1.add h2)).mul h3))
  have hI2 : Integrable (fun g ↦ ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
      ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) := by
    have h1 : IntegrableOn (fun g ↦ ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
        ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) (Icc a b) :=
      (hψc.continuousOn.mul hcont).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset fun g hg ↦ ?_).mp h1
    by_contra hgn
    exact hg (by
      change ψ g * _ = 0
      rw [hψ0 g hgn, zero_mul])
  rw [← integral_sub hI1 hI2]
  calc ‖∫ g, (ψ g * realPWLowerTraceLimit Y α hs g -
        ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
          ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)))‖
      ≤ ∫ g, D * Y * ‖ψ g‖ := by
        refine norm_integral_le_of_norm_le (hψ.norm.const_mul _) (ae_of_all _ fun g ↦ ?_)
        have he : ψ g * realPWLowerTraceLimit Y α hs g -
            ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
              ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
            ψ g * star (realPWLowerRemainder Y α hs g) := by
          rw [realPWLowerTraceLimit]
          ring
        rw [he, norm_mul, norm_star]
        by_cases hg : g ∈ Icc a b
        · calc ‖ψ g‖ * ‖realPWLowerRemainder Y α hs g‖ ≤ ‖ψ g‖ * (D * Y) :=
                mul_le_mul_of_nonneg_left (hD Y hY.le g hg) (norm_nonneg _)
            _ = D * Y * ‖ψ g‖ := by ring
        · rw [hψ0 g hg, norm_zero, zero_mul, mul_zero]
    _ = D * Y * ∫ g, ‖ψ g‖ := integral_const_mul _ _

end TestFunctionBound

section SmallBandwidthTest

variable (α : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- The product of a continuous test supported in `[a, b]` with a function continuous on
`[a, b]` is integrable. -/
private theorem integrable_test_mul_of_continuousOn {ψ : ℝ → ℂ} (hψc : Continuous ψ) {a b : ℝ}
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {h : ℝ → ℂ} (hh : ContinuousOn h (Icc a b)) :
    Integrable (fun g ↦ ψ g * h g) := by
  have h1 : IntegrableOn (fun g ↦ ψ g * h g) (Icc a b) :=
    (hψc.continuousOn.mul hh).integrableOn_Icc
  refine (integrableOn_iff_integrable_of_support_subset fun g hg ↦ ?_).mp h1
  by_contra hgn
  exact hg (by
    change ψ g * h g = 0
    rw [hψ0 g hgn, zero_mul])

/-- The integrand of the real term at `g < 1` is continuous on a compact interval of
`(0, 1)`. -/
private theorem continuousOn_realTermBelow {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) :
    ContinuousOn (fun g : ℝ ↦ 1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) (Icc a b) := by
  have h1 : ContinuousOn (fun g : ℝ ↦ (1 - g)⁻¹) (Icc a b) :=
    ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.2] : (0 : ℝ) < 1 - g).ne'
  have h2 : ContinuousOn (fun g : ℝ ↦ (1 + g)⁻¹) (Icc a b) :=
    ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.1] : (0 : ℝ) < 1 + g).ne'
  have h3 : ContinuousOn (fun g : ℝ ↦ g ^ (1 / 2 : ℝ)) (Icc a b) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  exact (continuousOn_const.mul (h1.add h2)).mul h3

/-- Reconstruction: with `s = 0` and `0 ≤ α < 1 / 2`, let `ψ` be a continuous test function
supported in `[a, b]`, `0 < a`, `b < 1`, whose integral against `1 - g ^ (2 α)` times the
integrand of the real term of (12.4.1.1) is not zero. Then for every small enough bandwidth the
limit of the traces of the cutoffs of its action on the weighted band is not the integral of
`ψ` against the integrand of the real term. -/
theorem exists_bandwidth_integral_realPWLowerTraceLimit_ne (ha : 0 ≤ α) (hα : α < 1 / 2)
    {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0)
    (hne : ∫ g, ψ g * (((1 - g ^ (2 * α)) *
      (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0) :
    ∃ Y₀ : ℝ, 0 < Y₀ ∧ ∀ Y : ℝ, 0 < Y → Y < Y₀ →
      (∫ g, ψ g * realPWLowerTraceLimit Y α hs g) ≠
        ∫ g, ψ g * ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_integral_realPWLowerTraceLimit_sub_le α hs ha hα ha0 hb1
  have hδ : 0 < ‖∫ g, ψ g * (((1 - g ^ (2 * α)) *
      (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ)‖ := norm_pos_iff.mpr hne
  have hm : 0 ≤ ∫ g, ‖ψ g‖ := integral_nonneg fun g ↦ norm_nonneg _
  have hDm : 0 ≤ D * ∫ g, ‖ψ g‖ := mul_nonneg hD0 hm
  have hden : 0 < D * (∫ g, ‖ψ g‖) + 1 := by linarith
  refine ⟨‖∫ g, ψ g * (((1 - g ^ (2 * α)) *
      (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ)‖ /
        (D * (∫ g, ‖ψ g‖) + 1), div_pos hδ hden, fun Y hY hYlt heq ↦ ?_⟩
  have hb := hD Y hY ψ hψc hψ0
  rw [heq] at hb
  have hcP : ContinuousOn (fun g : ℝ ↦
      ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_realTermBelow ha0 hb1)
  have hc0 : ContinuousOn (fun g : ℝ ↦ ((g ^ (2 * α) : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_rpow_const (mul_nonneg zero_le_two ha)).continuousOn
  have hIP := integrable_test_mul_of_continuousOn hψc hψ0 hcP
  have hIcP : Integrable (fun g ↦ ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
      ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) :=
    integrable_test_mul_of_continuousOn hψc hψ0 (hc0.mul hcP)
  have hdiff : (∫ g, ψ g * ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) -
      ∫ g, ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
        ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      ∫ g, ψ g * (((1 - g ^ (2 * α)) *
        (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← integral_sub hIP hIcP]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change ψ g * ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) -
      ψ g * (((g ^ (2 * α) : ℝ) : ℂ) *
        ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      ψ g * (((1 - g ^ (2 * α)) *
        (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ)
    push_cast
    ring
  rw [hdiff] at hb
  have h1 : D * Y * ∫ g, ‖ψ g‖ ≤
      D * (‖∫ g, ψ g * (((1 - g ^ (2 * α)) *
        (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ)‖ /
          (D * (∫ g, ‖ψ g‖) + 1)) * ∫ g, ‖ψ g‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYlt.le hD0) hm
  have h2 : D * (‖∫ g, ψ g * (((1 - g ^ (2 * α)) *
        (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ)‖ /
          (D * (∫ g, ‖ψ g‖) + 1)) * ∫ g, ‖ψ g‖ <
      ‖∫ g, ψ g * (((1 - g ^ (2 * α)) *
        (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) : ℝ) : ℂ)‖ := by
    rw [mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  linarith

/-- A nonnegative continuous test supported in `[c - 2 r, c + 2 r]` whose integral against
every real function that is continuous and positive there is a positive real number. -/
private theorem exists_test_integral_pos_of_pos_at (c r : ℝ) (hr : 0 < r) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ (∀ g ∉ Icc (c - 2 * r) (c + 2 * r), ψ g = 0) ∧
      ∀ h : ℝ → ℝ, ContinuousOn h (Icc (c - 2 * r) (c + 2 * r)) →
        (∀ g ∈ Icc (c - 2 * r) (c + 2 * r), 0 < h g) →
        ∃ k : ℝ, 0 < k ∧ ∫ g, ψ g * ((h g : ℝ) : ℂ) = (k : ℂ) := by
  let B : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  have hB0 : ∀ g ∉ Icc (c - 2 * r) (c + 2 * r), B g = 0 := by
    intro g hg
    apply B.zero_of_le_dist
    rw [Real.dist_eq]
    by_contra h
    have h' : |g - c| < 2 * r := not_le.mp h
    have h'' := abs_lt.mp h'
    exact hg ⟨by linarith [h''.1], by linarith [h''.2]⟩
  refine ⟨fun g ↦ ((B g : ℝ) : ℂ), Complex.continuous_ofReal.comp B.continuous,
    fun g hg ↦ by
      change ((B g : ℝ) : ℂ) = 0
      rw [hB0 g hg, Complex.ofReal_zero], fun h hh hpos ↦ ?_⟩
  let H : ℝ → ℝ := fun g ↦ B g * h g
  have hcast : (fun g : ℝ ↦ ((B g : ℝ) : ℂ) * ((h g : ℝ) : ℂ)) =
      fun g ↦ ((H g : ℝ) : ℂ) := by
    funext g
    change ((B g : ℝ) : ℂ) * ((h g : ℝ) : ℂ) = ((B g * h g : ℝ) : ℂ)
    rw [Complex.ofReal_mul]
  have hnn : 0 ≤ H := by
    intro g
    by_cases hg : g ∈ Icc (c - 2 * r) (c + 2 * r)
    · exact mul_nonneg B.nonneg (hpos g hg).le
    · change 0 ≤ B g * h g
      rw [hB0 g hg, zero_mul]
  have hint : Integrable H := by
    have h1 : IntegrableOn H (Icc (c - 2 * r) (c + 2 * r)) :=
      (B.continuous.continuousOn.mul hh).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset fun g hg ↦ ?_).mp h1
    by_contra hgn
    exact hg (by
      change B g * h g = 0
      rw [hB0 g hgn, zero_mul])
  have hposI : 0 < ∫ g, H g := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    refine lt_of_lt_of_le (Metric.measure_ball_pos volume c hr) (measure_mono fun g hg ↦ ?_)
    have hg' := abs_lt.mp (by simpa [Real.dist_eq] using hg : |g - c| < r)
    have hB1 : B g = 1 := B.one_of_mem_closedBall (Metric.ball_subset_closedBall hg)
    change B g * h g ≠ 0
    rw [hB1, one_mul]
    exact (hpos g ⟨by linarith [hg'.1], by linarith [hg'.2]⟩).ne'
  refine ⟨∫ g, H g, hposI, ?_⟩
  change ∫ g, ((B g : ℝ) : ℂ) * ((h g : ℝ) : ℂ) = _
  rw [hcast, integral_complex_ofReal]

/-- Reconstruction: with `s = 0` and `0 < α < 1 / 2` there is a continuous test function `ψ`
supported in `[1/4, 3/4]` with the following property. At every small enough bandwidth, the
traces of the sharp cutoffs of its action on the weighted even band converge as the cutoff is
removed, and the limit is not the integral of `ψ` against
`(1/2) (1 / (1 - g) + 1 / (1 + g)) g ^ (1/2)`.
Paper: that integrand is the one of the real term of Theorem 12.4.1.1, (12.4.1.1), p. 514, at
`g < 1`. Without weight the limit is that integral
(`exists_realPWTestCutoff_trace_limit_of_lt_one`), and for a test function supported in `g > 1`
it is that integral for every `0 ≤ α < 1 / 2` (`exists_realPWTestCutoff_trace_limit`).
Deviation: the bandwidth is fixed and small. The paper has a joint limit in the two cutoffs,
and nothing is proved here for a large bandwidth. -/
theorem exists_test_bandwidth_trace_limit_ne_realTerm (hα0 : 0 < α) (hα : α < 1 / 2) :
    ∃ (ψ : ℝ → ℂ) (Y₀ : ℝ), Continuous ψ ∧ (∀ g ∉ Icc (1 / 4 : ℝ) (3 / 4), ψ g = 0) ∧
      0 < Y₀ ∧ ∀ Y : ℝ, 0 < Y → Y < Y₀ →
        ∃ T : ℝ → nuclearEndomorphisms
            (RealPWBand.space Y (volume_le_realPWIntervalMeasure α 0 hs)),
          (∀ L (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α 0 hs)),
            ∃ r : Lp ℂ 2 (realPWIntervalMeasure α 0),
              (∀ᵐ x ∂realPWIntervalMeasure α 0, r x = sharpIntervalMask L x *
                ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α 0 hs)
                    (g⁻¹ * x) f)) ∧
              (T L).val f =
                (RealPWBand.space Y
                  (volume_le_realPWIntervalMeasure α 0 hs)).orthogonalProjectionOnto r) ∧
          ∃ ℓ : ℂ, Tendsto (fun L ↦ hilbertTrace (T L)) atTop (𝓝 ℓ) ∧
            ℓ ≠ ∫ g, ψ g * ((1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  obtain ⟨ψ, hψc, hψ0', hpos⟩ :=
    exists_test_integral_pos_of_pos_at (1 / 2) (1 / 8) (by norm_num)
  have hψ0 : ∀ g ∉ Icc (1 / 4 : ℝ) (3 / 4), ψ g = 0 := fun g hg ↦
    hψ0' g fun hg' ↦ hg ⟨by linarith [hg'.1], by linarith [hg'.2]⟩
  have ha0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hb1 : (3 / 4 : ℝ) < 1 := by norm_num
  have hsub : Icc ((1 / 2 : ℝ) - 2 * (1 / 8)) (1 / 2 + 2 * (1 / 8)) ⊆ Icc (1 / 4) (3 / 4) :=
    fun g hg ↦ ⟨by linarith [hg.1], by linarith [hg.2]⟩
  have hcont : ContinuousOn (fun g : ℝ ↦ (1 - g ^ (2 * α)) *
      (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)))
      (Icc ((1 / 2 : ℝ) - 2 * (1 / 8)) (1 / 2 + 2 * (1 / 8))) :=
    ((continuousOn_const.sub
      (Real.continuous_rpow_const (mul_nonneg zero_le_two hα0.le)).continuousOn).mul
      (continuousOn_realTermBelow ha0 hb1)).mono hsub
  have hposh : ∀ g ∈ Icc ((1 / 2 : ℝ) - 2 * (1 / 8)) (1 / 2 + 2 * (1 / 8)),
      0 < (1 - g ^ (2 * α)) * (1 / 2 * ((1 - g)⁻¹ + (1 + g)⁻¹) * g ^ (1 / 2 : ℝ)) := by
    intro g hg
    have hg0 : 0 < g := by linarith [(hsub hg).1]
    have hg1 : g < 1 := by linarith [(hsub hg).2]
    have h1 : 0 < (1 - g)⁻¹ := inv_pos.mpr (by linarith)
    have h2 : 0 < (1 + g)⁻¹ := inv_pos.mpr (by linarith)
    have h3 : 0 < g ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hg0 _
    have h4 : g ^ (2 * α) < 1 := Real.rpow_lt_one hg0.le hg1 (mul_pos two_pos hα0)
    exact mul_pos (sub_pos.mpr h4) (by positivity)
  obtain ⟨k, hk, hke⟩ := hpos _ hcont hposh
  obtain ⟨Y₀, hY₀, hne⟩ := exists_bandwidth_integral_realPWLowerTraceLimit_ne α hs hα0.le hα
    ha0 hb1 ψ hψc hψ0 (by
      rw [hke]
      exact Complex.ofReal_ne_zero.mpr hk.ne')
  refine ⟨ψ, Y₀, hψc, hψ0, hY₀, fun Y hY hYlt ↦ ?_⟩
  obtain ⟨T, hT1, hT2⟩ := exists_realPWTestCutoff_trace_limit_zero_of_lt_one Y α hs hY hα0.le
    hα ha0 hb1 ψ hψc hψ0
  exact ⟨T, hT1, _, hT2, hne Y hY hYlt⟩

end SmallBandwidthTest

end RiemannMasullo.Isolated
