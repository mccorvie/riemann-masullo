module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedLowerTrace
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

So at a fixed bandwidth the powers of `g` in the limit carry the exponent `+ 2 α` of the weight
at infinity. What the weight near the origin contributes is in the two remainders.

Reconstruction: The paper does not state this.

Not treated here: the value of the remainders, and how they depend on the bandwidth. A weight
with `s > 0`, where the quotient of the weights tends to `g ^ (2 α)` without reaching it. Test
functions. -/

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

end PowerWeight

end RiemannMasullo.Isolated
