module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWBandClosure
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The real-place trace of a test function on the level of functions of integral zero

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, and its use in the proof of
Theorem 12.5.1.1, p. 520, in the fixed-bandwidth model of the real place of `ℚ` of #7354, on
the level of Definition 11.2.1.1.

`Sec4_RealPWLevelTrace` treats the widths `0 ≤ α < 1 / 2`, where the level of the model is the
space of band vectors that vanish at the origin. This file treats the weights whose reciprocal
is integrable, for `1 / 2 ≤ α < 3 / 2`. That covers `α = 1 / 2` with `s > 1` and
`1 / 2 < α < 3 / 2`. There every band vector vanishes at the origin, and the level, the closure
of the polar-free core, is the space of band vectors of integral zero (#7771).

* `exists_realPWBand_integralVector`. The integral is the inner product with a band vector `e`.
* `integral_star_integralVector_mul_dilate`. For `g > 1` the contraction `x ↦ f (g⁻¹ x)` of a
  band vector pairs with `e` as a band vector does: the weighted integral of its product with
  the conjugate of `e` is `g` times the integral of `f`.
* `orthogonal_realPWBand_integralVector_eq_closure`. The orthogonal complement of `e` is the
  closure of the polar-free core.
* `exists_realPWTestCutoff_integralLevel_trace_limit`. The traces of the cutoffs of the action
  of a test function `ψ`, compressed to the level, converge. The limit is the limit on the
  whole band minus the integral of `ψ g g ^ (1/2)`.
* `realPWSharpTraceLimit_of_half_le`. For these widths the limit on the whole band has the
  integrand of the real term of (12.4.1.1) minus `g ^ (-1/2)`.

So the limit on the level is the integral of `ψ` against the integrand of the real term minus
`g ^ (-1/2)` minus `g ^ (1/2)`. With `ψ g = φ g / g` the two subtracted integrals have the form
of the terms `M(φ)(|·|^(-1/2))` and `M(φ)(|·|^(1/2))` that the proof of Theorem 12.5.1.1
subtracts on p. 520.

Reconstruction: The paper does not state this. The operator is stated on the whole band, as
`P T P` with `P` the orthogonal projection onto the level, as in `Sec4_RealPWLevelTrace`.

Not treated here: test functions whose support meets `g = 1` or `g < 1`. Widths from three
halves. The comparison with the adelic operator of the paper. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- From width one half and below width five halves the band vectors are forced to vanish to
second order at the origin and no further: the count of forced even jets is one. -/
theorem realPWOriginJetCount_eq_one {α : ℝ} (hα : 1 / 2 ≤ α) (hα' : α < 5 / 2) :
    realPWOriginJetCount α = 1 := by
  have h0 : realPWOriginJetCount α ≠ 0 := by
    intro h
    have h1 := realPWOriginJetCount_spec α
    rw [h] at h1
    norm_num at h1
    linarith
  by_contra h
  have h2 : 1 < realPWOriginJetCount α := by omega
  have h1 := realPWOriginJetCount_min α (j := 1) h2
  norm_num at h1
  linarith

/-- From width one half and below width five halves the limit of the sharp trace of the
dilation by `g⁻¹`, for `g > 1`, is `(1/2) (1 / (g - 1) + 1 / (g + 1)) g ^ (1/2)`, the integrand
of the real term of (12.4.1.1), p. 514, minus `g ^ (-1/2)`. -/
theorem realPWSharpTraceLimit_of_half_le {α g : ℝ} (hα : 1 / 2 ≤ α) (hα' : α < 5 / 2)
    (hg : 1 < g) :
    realPWSharpTraceLimit α g =
      ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ) -
        ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [← realPWSharpTraceLimit_of_lt_half (α := 0) (by norm_num) hg,
    realPWSharpTraceLimit_sub_of_lt_half (α := 0) (by norm_num) hg, realPWSharpTraceLimit,
    realPWOriginJetCount_eq_one hα hα', mul_one]

section IntegralLevel

variable (Y α s : ℝ) (hs : 0 ≤ s)

local notation "μw" => realPWIntervalMeasure α s
local notation "hμw" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hμw
local notation "ev" => RealPWBand.evaluation Y hμw

/-- When the reciprocal of the weight is integrable, the integral of a band vector is its inner
product with a fixed band vector. -/
theorem exists_realPWBand_integralVector
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) :
    ∃ e : V, ∀ f : V, Integrable (fun x ↦ ev x f) ∧ ⟪e, f⟫_ℂ = ∫ x, ev x f := by
  obtain ⟨I, hI, -⟩ := exists_realPWBand_integralFunctional_of_integrable (Y := Y) hs hint
  refine ⟨(InnerProductSpace.toDual ℂ V).symm I, fun f ↦ ⟨(hI f).1, ?_⟩⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact (hI f).2

variable {Y α s hs} in
/-- Reconstruction: for `g > 1` the contraction `x ↦ f (g⁻¹ x)` of a band vector pairs with the
vector `e` that represents the integral as a band vector does: the weighted integral of its
product with the conjugate of `e` is the integral of the contraction, which is `g` times the
integral of `f`. -/
theorem integral_star_integralVector_mul_dilate (hY : 0 < Y) {e : V}
    (he : ∀ f : V, Integrable (fun x ↦ ev x f) ∧ ⟪e, f⟫_ℂ = ∫ x, ev x f) {g : ℝ} (hg : 1 < g)
    (f : V) : ∫ x, star (ev x e) * ev (g⁻¹ * x) f ∂μw = (g : ℂ) * ∫ x, ev x f := by
  have hg0 : 0 < g := zero_lt_one.trans hg
  obtain ⟨m, q, C, hmc, hmb, hm1, hq, hlim⟩ := exists_realPWBand_maskedDilate Y α s hs hY hg f
  have hfi : Integrable (fun x ↦ ev (g⁻¹ * x) f) :=
    (he f).1.comp_mul_left' (inv_ne_zero hg0.ne')
  have h1 (L : ℝ) : ⟪e, q L⟫_ℂ = ∫ x, m L x * ev (g⁻¹ * x) f := by
    rw [(he (q L)).2]
    exact integral_congr_ae (ae_of_all _ fun x ↦ hq L x)
  have h2 : Tendsto (fun L ↦ ∫ x, m L x * ev (g⁻¹ * x) f) atTop
      (𝓝 (∫ x, ev (g⁻¹ * x) f)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖ev (g⁻¹ * x) f‖)
      (.of_forall fun L ↦ ?_) (.of_forall fun L ↦ ae_of_all _ fun x ↦ ?_)
      (hfi.norm.const_mul C) (ae_of_all _ fun x ↦ ?_)
    · exact (hmc L).aestronglyMeasurable.mul hfi.aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hmb L x) (norm_nonneg _)
    · have h := (hm1 x).mul_const (ev (g⁻¹ * x) f)
      rwa [one_mul] at h
  have h3 : ∫ x, ev (g⁻¹ * x) f = (g : ℂ) * ∫ x, ev x f := by
    rw [Measure.integral_comp_mul_left (fun x ↦ ev x f) g⁻¹, inv_inv, abs_of_pos hg0,
      Complex.real_smul]
  rw [← h3]
  exact tendsto_nhds_unique ((hlim e).congr h1) h2

variable {Y α s hs} in
/-- Reconstruction: from width one half and below width five halves, when the reciprocal of the
weight is integrable, the orthogonal complement of the vector that represents the integral is
the closure of the polar-free core. -/
theorem orthogonal_realPWBand_integralVector_eq_closure (hα : 1 / 2 ≤ α) (hα' : α < 5 / 2)
    (hY : 0 < Y) (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) {e : V}
    (he : ∀ f : V, Integrable (fun x ↦ ev x f) ∧ ⟪e, f⟫_ℂ = ∫ x, ev x f) :
    (((ℂ ∙ e)ᗮ : Submodule ℂ V) : Set V) = closure (realPWBandPolarFreeCore Y α hs) := by
  rw [closure_realPWBandPolarFreeCore_eq_of_integrable hα hα' hs hY hint]
  ext f
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, (he f).2]
  rfl

variable {Y α s hs} in
/-- From width one half and below width three halves, when the reciprocal of the weight is
integrable, the vector that represents the integral is not zero. -/
theorem realPWBand_integralVector_ne_zero (hα : 1 / 2 ≤ α) (hα' : α < 3 / 2) (hY : 0 < Y)
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) {e : V}
    (he : ∀ f : V, Integrable (fun x ↦ ev x f) ∧ ⟪e, f⟫_ℂ = ∫ x, ev x f) : e ≠ 0 := by
  obtain ⟨f, -, hf⟩ := exists_realPWBand_notMem_closure_polarFreeCore_of_integrable
    (Y := Y) (by linarith) hα' hs hY hint
  intro h0
  apply hf
  rw [closure_realPWBandPolarFreeCore_eq_of_integrable hα (by linarith) hs hY hint]
  change ∫ x, ev x f = 0
  rw [← (he f).2, h0, inner_zero_left]

/-- Reconstruction: for `1 / 2 ≤ α < 3 / 2`, a weight with integrable reciprocal, and a
continuous test function `ψ` of the dilation supported in `[a, b]` with `1 < a`, the traces of
the cutoffs of its action, compressed to the closure of the polar-free core, converge as the
cutoff is removed. The level is the orthogonal complement of the vector `e` that represents
the integral. The limit is the limit on the whole band minus the integral of
`ψ g g ^ (1/2)`, which is the contribution of the direction removed by the level. By
`realPWSharpTraceLimit_of_half_le` the limit on the whole band is the integral of `ψ` against
the integrand of the real term of (12.4.1.1) minus `g ^ (-1/2)`. -/
theorem exists_realPWTestCutoff_integralLevel_trace_limit (hY : 0 < Y) (hα : 1 / 2 ≤ α)
    (hα' : α < 3 / 2) (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹))
    {a b : ℝ} (ha1 : 1 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    ∃ e : V, (((ℂ ∙ e)ᗮ : Submodule ℂ V) : Set V) = closure (realPWBandPolarFreeCore Y α hs) ∧
      ∃ T : ℝ → nuclearEndomorphisms V,
        (∀ L (f : V), ∃ r : Lp ℂ 2 μw,
          (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
            ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ev (g⁻¹ * x) ((ℂ ∙ e)ᗮ.starProjection f))) ∧
          (T L).val f = (ℂ ∙ e)ᗮ.starProjection ((V).orthogonalProjectionOnto r)) ∧
        Tendsto (fun L ↦ hilbertTrace (T L)) atTop
          (𝓝 ((∫ g, ψ g * realPWSharpTraceLimit α g) -
            ∫ g, ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ))) := by
  have ha : 0 ≤ α := by linarith
  obtain ⟨e, he⟩ := exists_realPWBand_integralVector Y α s hs hint
  refine ⟨e, orthogonal_realPWBand_integralVector_eq_closure (hs := hs) hα (by linarith) hY hint
    he, ?_⟩
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_compl_nuclear Y α s hs hY ha ha1.le ψ hψc hψ0 L e
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) = fun L ↦
      (∫ g, ψ g * realPWSharpTrace Y α s hs g L) -
        (((‖e‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWTestCorrection Y α s hs e ψ L := funext hT2
  rw [h]
  have h1 := tendsto_integral_realPWSharpTrace hY ha hs ha1 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0
  have he0 := realPWBand_integralVector_ne_zero (hs := hs) hα hα' hY hint he
  have hN : ∫ x, ev x e = ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [← (he e).2, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hN0 : ((‖e‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr he0))
  have h2 := (tendsto_realPWTestCorrection Y α s hs hY ha ha1.le ψ hψc hψ0 e
    (fun g ↦ (g : ℂ) * ((‖e‖ ^ 2 : ℝ) : ℂ)) fun g hg ↦ by
      rw [integral_star_integralVector_mul_dilate (hs := hs) hY he (ha1.trans_le hg.1) e,
        hN]).const_mul
    (((‖e‖ ^ 2 : ℝ) : ℂ))⁻¹
  have h3 : (((‖e‖ ^ 2 : ℝ) : ℂ))⁻¹ *
      (∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((g : ℂ) * ((‖e‖ ^ 2 : ℝ) : ℂ)))) =
      ∫ g, ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Icc a b
    · have hg0 : 0 < g := zero_lt_one.trans (ha1.trans_le hg.1)
      have hr : g ^ (1 / 2 : ℝ) = g ^ (-(1 / 2 : ℝ)) * g := by
        rw [← Real.rpow_add_one hg0.ne']
        norm_num
      change (((‖e‖ ^ 2 : ℝ) : ℂ))⁻¹ * (ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((g : ℂ) * ((‖e‖ ^ 2 : ℝ) : ℂ)))) = ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ)
      have hne : ((‖e‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr he0)
      rw [hr]
      push_cast
      field_simp
    · change (((‖e‖ ^ 2 : ℝ) : ℂ))⁻¹ * (ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((g : ℂ) * ((‖e‖ ^ 2 : ℝ) : ℂ)))) = ψ g * ((g ^ (1 / 2 : ℝ) : ℝ) : ℂ)
      rw [hψ0 g hg, zero_mul, zero_mul, mul_zero]
  rw [h3] at h2
  exact h1.sub h2

end IntegralLevel

end RiemannMasullo.Isolated
