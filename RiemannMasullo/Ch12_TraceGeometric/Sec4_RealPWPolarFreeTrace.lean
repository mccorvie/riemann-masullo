module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWIntegralLevelTrace

/-! # The real-place trace on the level, for tests whose polar terms vanish

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, and its use in the proof of
Theorem 12.5.1.1, p. 520, in the fixed-bandwidth model of the real place of `ℚ` of #7354, on
the level of Definition 11.2.1.1.

On the level the limit of the cutoff traces of a test function `ψ` supported in `g > 1` is the
integral of `ψ` against the integrand of the real term, minus the integral of `ψ g g ^ (-1/2)`
for the widths `0 ≤ α < 1 / 2` (`Sec4_RealPWLevelTrace`), and minus the integrals of
`ψ g g ^ (-1/2)` and of `ψ g g ^ (1/2)` from width one half and below width three halves
(`Sec4_RealPWIntegralLevelTrace`). With `ψ g = φ g / g` the subtracted integrals have the form
of the polar terms `M(φ)(|·|^(-1/2))` and `M(φ)(|·|^(1/2))` of p. 520.

* `exists_realPWTestCutoff_level_trace_limit_of_polarFree`. For `0 ≤ α < 1 / 2` and a test with
  `∫ ψ g g ^ (-1/2) = 0`, the limit is the integral of `ψ` against the integrand of the real
  term.
* `exists_realPWTestCutoff_integralLevel_trace_limit_of_polarFree`. From width one half and
  below width three halves, for a test with `∫ ψ g g ^ (-1/2) = 0` and `∫ ψ g g ^ (1/2) = 0`,
  the limit is the same integral.

So for tests supported in `g > 1` whose two polar terms vanish, the limit on the level is the
same at every width below three halves that these files treat.

Reconstruction: The paper does not state this.

Not treated here: test functions whose support meets `g = 1` or `g < 1`. At `α = s = 0` the
level subtracts `min (g ^ (1/2)) (g ^ (-1/2))` on both sides of `g = 1`
(`Sec4_RealPWUnweightedTrace`), and its integral against a test is not a combination of the two
polar terms. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- The product of a continuous test supported in `[a, b]` with a function continuous on
`[a, b]` is integrable. -/
private theorem integrable_test_mul' {ψ : ℝ → ℂ} (hψc : Continuous ψ) {a b : ℝ}
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {h : ℝ → ℂ} (hh : ContinuousOn h (Icc a b)) :
    Integrable (fun g ↦ ψ g * h g) := by
  have h1 : IntegrableOn (fun g ↦ ψ g * h g) (Icc a b) :=
    (hψc.continuousOn.mul hh).integrableOn_Icc
  refine (integrableOn_iff_integrable_of_support_subset fun g hg ↦ ?_).mp h1
  by_contra hgn
  exact hg (by
    change ψ g * h g = 0
    rw [hψ0 g hgn, zero_mul])

variable (Y α s : ℝ) (hs : 0 ≤ s)

local notation "μw" => realPWIntervalMeasure α s
local notation "hμw" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hμw
local notation "ev" => RealPWBand.evaluation Y hμw

/-- Paper: Theorem 12.4.1.1, pp. 514–517, the real term, on the level of Definition 11.2.1.1, as
used on p. 520. For `0 ≤ α < 1 / 2` and a test function `ψ` supported in `g > 1` with
`∫ ψ g g ^ (-1/2) = 0`, the traces of the cutoffs of the action of `ψ`, compressed to the level
of band vectors vanishing at the origin, converge to the integral of `ψ` against the integrand
of the real term of (12.4.1.1).
Reconstruction: The paper does not state this. -/
theorem exists_realPWTestCutoff_level_trace_limit_of_polarFree (hY : 0 < Y) (ha : 0 ≤ α)
    (hα : α < 1 / 2) {a b : ℝ} (ha1 : 1 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0)
    (hm : ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 0) :
    ∃ T : ℝ → nuclearEndomorphisms V,
      (∀ L (f : V), ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((realPWZeroLevel Y α s hs).starProjection f))) ∧
        (T L).val f =
          (realPWZeroLevel Y α s hs).starProjection ((V).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g *
          ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) := by
  obtain ⟨T, hT1, hT2⟩ :=
    exists_realPWTestCutoff_level_trace_limit Y α s hs hY ha hα ha1 ψ hψc hψ0
  refine ⟨T, hT1, ?_⟩
  have h : (∫ g, ψ g * realPWSharpTraceLimit α g) -
      ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ∫ g, ψ g * ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hm, sub_zero]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Icc a b
    · change ψ g * realPWSharpTraceLimit α g = _
      rw [realPWSharpTraceLimit_of_lt_half hα (ha1.trans_le hg.1)]
    · change ψ g * _ = ψ g * _
      rw [hψ0 g hg, zero_mul, zero_mul]
  rwa [h] at hT2

/-- Paper: Theorem 12.4.1.1, pp. 514–517, the real term, on the level of Definition 11.2.1.1, as
used on p. 520. From width one half and below width three halves, when the reciprocal of the
weight is integrable, and for a test function `ψ` supported in `g > 1` with
`∫ ψ g g ^ (-1/2) = 0` and `∫ ψ g g ^ (1/2) = 0`, the traces of the cutoffs of the action of
`ψ`, compressed to the closure of the polar-free core, converge to the integral of `ψ` against
the integrand of the real term of (12.4.1.1). This is the limit that
`exists_realPWTestCutoff_level_trace_limit_of_polarFree` gives below width one half.
Reconstruction: The paper does not state this. -/
theorem exists_realPWTestCutoff_integralLevel_trace_limit_of_polarFree (hY : 0 < Y)
    (hα : 1 / 2 ≤ α) (hα' : α < 3 / 2)
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹))
    {a b : ℝ} (ha1 : 1 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0)
    (hm : ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 0)
    (hp : ∫ g, ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 0) :
    ∃ e : V, (((ℂ ∙ e)ᗮ : Submodule ℂ V) : Set V) = closure (realPWBandPolarFreeCore Y α hs) ∧
      ∃ T : ℝ → nuclearEndomorphisms V,
        (∀ L (f : V), ∃ r : Lp ℂ 2 μw,
          (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
            ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ev (g⁻¹ * x) ((ℂ ∙ e)ᗮ.starProjection f))) ∧
          (T L).val f = (ℂ ∙ e)ᗮ.starProjection ((V).orthogonalProjectionOnto r)) ∧
        Tendsto (fun L ↦ hilbertTrace (T L)) atTop
          (𝓝 (∫ g, ψ g *
            ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) := by
  obtain ⟨e, he, T, hT1, hT2⟩ :=
    exists_realPWTestCutoff_integralLevel_trace_limit Y α s hs hY hα hα' hint ha1 ψ hψc hψ0
  refine ⟨e, he, T, hT1, ?_⟩
  have hc1 : ContinuousOn
      (fun g : ℝ ↦ ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ))
      (Icc a b) := by
    have h1 : ContinuousOn (fun g : ℝ ↦ (g - 1)⁻¹) (Icc a b) :=
      ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.1] : (0 : ℝ) < g - 1).ne'
    have h2 : ContinuousOn (fun g : ℝ ↦ (g + 1)⁻¹) (Icc a b) :=
      ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.1] : (0 : ℝ) < g + 1).ne'
    have h3 : ContinuousOn (fun g : ℝ ↦ g ^ (1 / 2 : ℝ)) (Icc a b) :=
      (Real.continuous_rpow_const (by norm_num)).continuousOn
    exact Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.mul (h1.add h2)).mul h3)
  have hc2 : ContinuousOn (fun g : ℝ ↦ ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn fun g hg ↦
      (Real.continuousAt_rpow_const g _
        (Or.inl (zero_lt_one.trans (ha1.trans_le hg.1)).ne')).continuousWithinAt
  have h : (∫ g, ψ g * realPWSharpTraceLimit α g) -
      ∫ g, ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
      ∫ g, ψ g * ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hp, sub_zero]
    have h1 : ∫ g, ψ g * realPWSharpTraceLimit α g =
        (∫ g, ψ g * ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)) -
          ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [← integral_sub (integrable_test_mul' hψc hψ0 hc1) (integrable_test_mul' hψc hψ0 hc2)]
      refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      by_cases hg : g ∈ Icc a b
      · change ψ g * realPWSharpTraceLimit α g = ψ g * _ - ψ g * _
        rw [realPWSharpTraceLimit_of_half_le hα (by linarith) (ha1.trans_le hg.1), mul_sub]
      · change ψ g * _ = ψ g * _ - ψ g * _
        rw [hψ0 g hg, zero_mul, zero_mul, zero_mul, sub_zero]
    rw [h1, hm, sub_zero]
  rwa [h] at hT2

end RiemannMasullo.Isolated
