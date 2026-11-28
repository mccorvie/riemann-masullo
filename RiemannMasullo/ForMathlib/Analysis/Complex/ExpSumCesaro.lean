module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Endpoint Abel–Laplace residues and Cesàro uniqueness for exponential sums on a half-line

Let the frequencies `w i` be distinct, have no accumulation point in `ℂ`, and satisfy
`Re (w i) ≤ 1/2`, and let the coefficients `b` be summable. For `S y = ∑ i, b i * exp (w i * y)` on
`y ≥ 0`:

1. (`tendsto_mul_laplace_of_hasSum_exp_of_integrable`) If `‖S y‖ ≤ D y` on `y ≥ 0` where
   `D y * exp (-σ * y)` is integrable on `(0, ∞)` for every `σ > c`, then for every frequency
   with `c ≤ Re (w i₀)` (including boundary frequencies `Re (w i₀) = c`), the horizontal
   Abel–Laplace limit `(δ : ℂ) * ∫_{y > 0} S y * exp (-(w i₀ + δ) * y)` as `δ → 0⁺` equals `b i₀`.
2. (`eq_zero_of_hasSum_exp_of_cesaro_majorant`, `eq_zero_of_hasSum_exp_of_cesaro`) If
   `Y⁻¹ * ∫_{y ∈ (0, Y]} ‖S y‖ * exp (-c * y) → 0` as `Y → ∞` (with no exponent saving below `c`),
   then `b i = 0` for **every** frequency in the closed half-plane `c ≤ Re (w i)` (boundary
   `Re (w i) = c` included).
3. (`eq_zero_of_hasSum_exp_of_tendsto_zero`, `eq_zero_of_hasSum_exp_of_endpoint_integrable`,
   `eq_zero_of_hasSum_exp_of_sq_integrable`) In particular, `‖S y‖ * exp (-c * y) → 0`, endpoint
   `L¹` integrability of `‖S y‖ * exp (-c * y)`, or endpoint `L²` integrability of
   `‖S y‖ ^ 2 * exp (-2 * c * y)` on `(0, ∞)` forces `b i = 0` for all `c ≤ Re (w i)`.
-/

public section

open Filter Topology Set MeasureTheory

namespace RiemannMasullo

private theorem expCesaro_range_closed_countable {ι : Type*} (w : ι → ℂ)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ Set.range w) :
    IsClosed (range w) ∧ (range w).Countable := by
  have h : IsClosed (range w) ∧ IsDiscrete (range w) :=
    isClosed_and_discrete_iff.2 fun x => Filter.disjoint_principal_right.2 (hdisc x)
  exact ⟨h.1, h.1.isLindelof.countable_of_isDiscrete h.2⟩

private theorem expCesaro_norm_div_le {a x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x‖) :
    ‖a / x‖ ≤ ‖a‖ * (1 / ρ) := by
  rw [norm_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by rw [one_div]; exact inv_anti₀ hρ hx) (norm_nonneg _)

private theorem expCesaro_aux_dist {x z w : ℂ} {r : ℝ} (h1 : dist x z < r / 2)
    (h2 : r ≤ dist w z) : r / 2 ≤ ‖x - w‖ := by
  rw [← dist_eq_norm]
  have := dist_triangle w x z
  rw [dist_comm w x] at this
  linarith

private theorem expCesaro_resolvent_eq_laplace {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hre : ∀ i, (w i).re ≤ 1 / 2) (hb : Summable b) (z : ℂ) (hz : 1 / 2 < z.re) :
    ∑' i, b i / (z - w i) =
      ∫ y in Ioi (0 : ℝ), (∑' i, b i * Complex.exp (w i * y)) * Complex.exp (-(z * y)) := by
  set F : ι → ℝ → ℂ := fun i y => b i * Complex.exp ((w i - z) * y)
  have hlt : ∀ i, (w i - z).re < 0 := fun i => by simp; linarith [hre i]
  have hint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_complex_Ioi (hlt i) 0).const_mul (b i)
  have hval : ∀ i, ∫ y in Ioi (0 : ℝ), F i y = b i / (z - w i) := by
    intro i
    simp only [F]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hlt i)]
    have h1 : w i - z ≠ 0 := fun h0 => by have := hlt i; rw [h0] at this; simp at this
    have h2 : z - w i ≠ 0 := fun h0 => h1 (by rw [← neg_sub, h0, neg_zero])
    field_simp
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have hnorm : ∀ i, ∫ y in Ioi (0 : ℝ), ‖F i y‖ = ‖b i‖ * (1 / (z.re - (w i).re)) := by
    intro i
    have hpt : ∀ y : ℝ, ‖F i y‖ = ‖b i‖ * Real.exp ((w i - z).re * y) := by
      intro y; simp [F, Complex.norm_exp]
    simp_rw [hpt]
    rw [integral_const_mul, integral_exp_mul_Ioi (hlt i)]
    congr 1
    simp only [mul_zero, Real.exp_zero, Complex.sub_re]
    rw [neg_div, ← div_neg, neg_sub]
  have hsum : Summable fun i => ∫ y in Ioi (0 : ℝ), ‖F i y‖ := by
    simp_rw [hnorm]
    refine (hb.norm.mul_right (1 / (z.re - 1 / 2))).of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    · have := hre i
      exact mul_nonneg (norm_nonneg _) (by rw [one_div]; exact inv_nonneg.2 (by linarith))
    · have := hre i
      gcongr
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hval] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  have hmul : ∀ i, F i y = Complex.exp (-(z * y)) * (b i * Complex.exp (w i * y)) := by
    intro i
    simp only [F, sub_eq_add_neg, add_mul, Complex.exp_add, neg_mul]
    ring
  simp_rw [hmul, tsum_mul_left]
  ring

private theorem expCesaro_resolvent_differentiableOn {ι : Type*} (w b : ι → ℂ) (hb : Summable b)
    (hcl : IsClosed (range w)) :
    DifferentiableOn ℂ (fun z => ∑' i, b i / (z - w i)) (range w)ᶜ := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl z hz
  have hfar : ∀ i, r ≤ dist (w i) z := fun i => by
    by_contra hcon
    exact hball (Metric.mem_ball.2 (not_le.1 hcon)) ⟨i, rfl⟩
  have hd : DifferentiableOn ℂ (fun z => ∑' i, b i / (z - w i)) (Metric.ball z (r / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun i x => b i / (x - w i)) (u := fun i => ‖b i‖ * (1 / (r / 2)))
      (hb.norm.mul_right _) (fun i => ?_) Metric.isOpen_ball (fun i x hx => ?_)
    · have hne : ∀ x ∈ Metric.ball z (r / 2), x - w i ≠ 0 := fun x hx h0 => by
        have := expCesaro_aux_dist (Metric.mem_ball.1 hx) (hfar i)
        rw [h0, norm_zero] at this
        linarith
      exact (differentiableOn_const (b i)).div (differentiableOn_id.sub_const (w i)) hne
    · exact expCesaro_norm_div_le (by linarith) (expCesaro_aux_dist (Metric.mem_ball.1 hx) (hfar i))
  exact (hd.differentiableAt (Metric.ball_mem_nhds z (by linarith))).differentiableWithinAt

private theorem expCesaro_halfPlane_diff_isPreconnected (c : ℝ) {A : Set ℂ} (hA : A.Countable) :
    IsPreconnected ({z : ℂ | c < z.re} \ A) := by
  let f : ℂ → ℂ := fun ζ ↦ ((c + Real.exp ζ.re : ℝ) : ℂ) + (ζ.im : ℂ) * Complex.I
  have hf : Continuous f := by fun_prop
  have hre (ζ : ℂ) : (f ζ).re = c + Real.exp ζ.re := by simp [f, Complex.exp_ofReal_re]
  have him (ζ : ℂ) : (f ζ).im = ζ.im := by simp [f]
  have hinj : Function.Injective f := fun ζ ξ h ↦ by
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    rw [hre, hre, add_right_inj] at h1
    rw [him, him] at h2
    exact Complex.ext (Real.exp_injective h1) h2
  have himg : f '' (f ⁻¹' A)ᶜ = {z : ℂ | c < z.re} \ A := by
    ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact ⟨by rw [mem_ofPred_eq, hre]; linarith [Real.exp_pos ζ.re], hζ⟩
    · rintro ⟨hz, hzA⟩
      have hz' : 0 < z.re - c := sub_pos.mpr hz
      have hfz : f (((Real.log (z.re - c) : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) = z := by
        apply Complex.ext
        · rw [hre]; simp [Real.exp_log hz']
        · rw [him]; simp
      exact ⟨_, by rw [mem_compl_iff, mem_preimage, hfz]; exact hzA, hfz⟩
  rw [← himg]
  exact ((hA.preimage hinj).isConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex])).isPreconnected.image f hf.continuousOn

private theorem expCesaro_continuousOn {ι : Type*} (w b : ι → ℂ) (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) :
    ContinuousOn (fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * y)) (Ici 0) := by
  intro y₀ hy₀
  have hY : ContinuousOn (fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * y)) (Icc 0 (y₀ + 1)) := by
    refine continuousOn_tsum (u := fun i ↦ ‖b i‖ * Real.exp ((y₀ + 1) / 2))
      (fun i ↦ (by fun_prop : Continuous fun y : ℝ ↦ b i * Complex.exp (w i * y)).continuousOn)
      (hb.norm.mul_right _) (fun i y hy ↦ ?_)
    rw [norm_mul, Complex.norm_exp]
    gcongr
    have hwy : (w i * (y : ℂ)).re = (w i).re * y := by simp
    rw [hwy]
    nlinarith [hre i, hy.1, hy.2]
  exact (hY.continuousWithinAt ⟨hy₀, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith : y₀ < y₀ + 1)))
      fun y hy ↦ ⟨hy.1, hy.2.le⟩)

private theorem expCesaro_laplace_integrable (S : ℝ → ℂ) (hS : ContinuousOn S (Ici 0)) (D : ℝ → ℝ)
    (hD : ∀ y, 0 ≤ y → ‖S y‖ ≤ D y) {σ : ℝ}
    (hDi : IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi 0)) {z : ℂ} (hz : σ ≤ z.re) :
    IntegrableOn (fun y : ℝ ↦ S y * Complex.exp (-(z * y))) (Ioi 0) ∧
      ‖∫ y in Ioi (0 : ℝ), S y * Complex.exp (-(z * y))‖ ≤
        ∫ y in Ioi (0 : ℝ), D y * Real.exp (-σ * y) := by
  have hle : ∀ y ∈ Ioi (0 : ℝ),
      ‖S y * Complex.exp (-(z * y))‖ ≤ D y * Real.exp (-σ * y) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hzy : (-(z * (y : ℂ))).re = -(z.re * y) := by simp
    rw [norm_mul, Complex.norm_exp, hzy]
    exact mul_le_mul (hD y hy0.le) (Real.exp_le_exp.mpr (by nlinarith))
      (Real.exp_pos _).le ((norm_nonneg _).trans (hD y hy0.le))
  have hmeas : AEStronglyMeasurable (fun y : ℝ ↦ S y * Complex.exp (-(z * y)))
      (volume.restrict (Ioi 0)) :=
    ((hS.mono Ioi_subset_Ici_self).mul
      (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable measurableSet_Ioi
  have hae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖S y * Complex.exp (-(z * y))‖ ≤ D y * Real.exp (-σ * y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using hle y hy
  exact ⟨hDi.mono' hmeas hae, norm_integral_le_of_norm_le hDi hae⟩

private theorem expCesaro_laplace_differentiableAt (S : ℝ → ℂ) (hS : ContinuousOn S (Ici 0))
    (D : ℝ → ℝ) (hD : ∀ y, 0 ≤ y → ‖S y‖ ≤ D y) {c : ℝ}
    (hDi : ∀ σ, c < σ → IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi 0)) {z₀ : ℂ}
    (hz₀ : c < z₀.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-(z * y))) z₀ := by
  set ε := (z₀.re - c) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hcont (z : ℂ) : ContinuousOn (fun y : ℝ ↦ S y * Complex.exp (-(z * y))) (Ioi 0) :=
    (hS.mono Ioi_subset_Ici_self).mul (Continuous.continuousOn (by fun_prop))
  have hcont' : ContinuousOn (fun y : ℝ ↦ S y * (-(y : ℂ) * Complex.exp (-(z₀ * y)))) (Ioi 0) :=
    (hS.mono Ioi_subset_Ici_self).mul (Continuous.continuousOn (by fun_prop))
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ ε,
      ‖S y * (-(y : ℂ) * Complex.exp (-(z * y)))‖ ≤
        1 / ε * (D y * Real.exp (-(c + ε) * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    have hy0 : (0 : ℝ) < y := hy
    have hzre : z₀.re - ε < z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [← dist_eq_norm, Complex.sub_re] at h1
      have h2 := (abs_lt.mp (h1.trans_lt (Metric.mem_ball.mp hz))).1
      linarith
    have hzy : (-(z * (y : ℂ))).re = -(z.re * y) := by simp
    have hy1 : y ≤ Real.exp (ε * y) / ε := by
      rw [le_div_iff₀ hε0]
      have := Real.add_one_le_exp (ε * y)
      linarith
    have hDy : ‖S y‖ ≤ D y := hD y hy0.le
    have hD0 : 0 ≤ D y := (norm_nonneg _).trans hDy
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
      Complex.norm_exp, hzy]
    calc ‖S y‖ * (y * Real.exp (-(z.re * y)))
        ≤ D y * (Real.exp (ε * y) / ε * Real.exp (-(z.re * y))) :=
          mul_le_mul hDy (mul_le_mul_of_nonneg_right hy1 (Real.exp_pos _).le)
            (mul_nonneg hy0.le (Real.exp_pos _).le) hD0
      _ = 1 / ε * (D y * Real.exp ((ε - z.re) * y)) := by
          rw [show (ε - z.re) * y = ε * y + -(z.re * y) by ring, Real.exp_add]
          ring
      _ ≤ 1 / ε * (D y * Real.exp (-(c + ε) * y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hD0)
            (by positivity)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun z y ↦ S y * Complex.exp (-(z * y)))
    (F' := fun z y ↦ S y * (-(y : ℂ) * Complex.exp (-(z * y))))
    (bound := fun y ↦ 1 / ε * (D y * Real.exp (-(c + ε) * y))) (Metric.ball_mem_nhds z₀ hε0)
    (Eventually.of_forall fun z ↦ (hcont z).aestronglyMeasurable measurableSet_Ioi)
    (expCesaro_laplace_integrable S hS D hD (hDi z₀.re hz₀) le_rfl).1
    (hcont'.aestronglyMeasurable measurableSet_Ioi) hbound
    ((hDi (c + ε) (by linarith)).const_mul _)
    (ae_of_all _ fun y z _ ↦ by
      convert ((hasDerivAt_mul_const (y : ℂ)).neg.cexp).const_mul (S y) using 1
      simp only [Pi.neg_apply]
      ring)
  exact hderiv.2.differentiableAt

/-- Horizontal Abel–Laplace residue extraction on and to the right of the critical abscissa `c`.
Let the frequencies `w i` be distinct, discrete in `ℂ`, and satisfy `Re (w i) ≤ 1/2`, and let `b`
be summable. If `‖S y‖ ≤ D y` on `y ≥ 0` where `D y * exp (-σ * y)` is integrable on `(0, ∞)` for
every `σ > c`, then for every index `i₀` with `c ≤ Re (w i₀)` (including boundary frequencies
`Re (w i₀) = c`), `(δ : ℂ) * ∫_{y > 0} S y * exp (-(w i₀ + δ) * y)` tends to `b i₀` as `δ → 0⁺`. -/
theorem tendsto_mul_laplace_of_hasSum_exp_of_integrable {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (D : ℝ → ℝ) (hS : ∀ y : ℝ, 0 ≤ y → ‖S y‖ ≤ D y)
    (hDi : ∀ σ, c < σ → IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi (0 : ℝ)))
    (i₀ : ι) (hi₀ : c ≤ (w i₀).re) :
    Tendsto (fun δ : ℝ ↦ (δ : ℂ) * ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-((w i₀ + δ) * y)))
      (𝓝[>] 0) (𝓝 (b i₀)) := by
  classical
  obtain ⟨hcl, hcount⟩ := expCesaro_range_closed_countable w hdisc
  have : Countable ι := by
    have := hcount.to_subtype
    exact Function.Injective.countable (f := fun i => (⟨w i, i, rfl⟩ : range w))
      fun a b' hab => hw (congrArg Subtype.val hab)
  set T : ℝ → ℂ := fun y ↦ ∑' i, b i * Complex.exp (w i * y)
  have hTb : ∀ y, 0 ≤ y → ‖T y‖ ≤ D y := fun y hy ↦ by
    rw [show T y = S y from (h y hy).tsum_eq]; exact hS y hy
  have hTc : ContinuousOn T (Ici 0) := expCesaro_continuousOn w b hre hb
  set R : ℂ → ℂ := fun z => ∑' i, b i / (z - w i)
  set L : ℂ → ℂ := fun z => ∫ y in Ioi (0 : ℝ), T y * Complex.exp (-(z * y))
  have hc : c ≤ 1 / 2 := hi₀.trans (hre i₀)
  set V : Set ℂ := {z : ℂ | c < z.re} \ range w
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).sdiff hcl
  have hRa : AnalyticOnNhd ℂ R V :=
    ((expCesaro_resolvent_differentiableOn w b hb hcl).mono fun z (hz : z ∈ V) ↦ hz.2).analyticOnNhd hVo
  have hLa : AnalyticOnNhd ℂ L V :=
    DifferentiableOn.analyticOnNhd (fun z (hz : z ∈ V) ↦
      (expCesaro_laplace_differentiableAt T hTc D hTb hDi hz.1).differentiableWithinAt) hVo
  have h1 : (1 : ℂ) ∈ V := by
    refine ⟨by change c < (1 : ℂ).re; simp; linarith, ?_⟩
    rintro ⟨i, hi⟩
    have := hre i
    rw [hi] at this
    norm_num at this
  have hev : ∀ᶠ z in 𝓝 (1 : ℂ), (R - L) z = 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re})] with z hz
    rw [Pi.sub_apply, sub_eq_zero]
    exact expCesaro_resolvent_eq_laplace w b hre hb z hz
  have hzero := (hRa.sub hLa).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (expCesaro_halfPlane_diff_isPreconnected c hcount) h1
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hdisc (w i₀)))
  have hfar : ∀ i, i ≠ i₀ → ε ≤ dist (w i) (w i₀) := fun i hi => by
    by_contra hcon
    exact hεball (not_le.1 hcon) (fun h0 => hi (hw h0)) ⟨i, rfl⟩
  set C₂ := (∑' i, ‖b i‖) * (1 / (ε / 2)) with hC₂
  have hL_eq : ∀ z : ℂ, L z = ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-(z * y)) := fun z ↦
    setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ by
      rw [show T y = S y from (h y (le_of_lt hy)).tsum_eq]
  have hdist_le : ∀ δ : ℝ, δ ∈ Ioo 0 (ε / 2) →
      dist ((δ : ℂ) * ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-((w i₀ + δ) * y))) (b i₀) ≤ δ * C₂ := by
    rintro δ ⟨hδ0, hδε⟩
    set z : ℂ := w i₀ + δ with hz
    have hzw : z - w i₀ = δ := by rw [hz]; ring
    have hdist : dist z (w i₀) = δ := by
      rw [dist_eq_norm, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    have hzre : z.re = (w i₀).re + δ := by simp [hz]
    have hzU : z ∈ V := by
      refine ⟨by change c < z.re; rw [hzre]; linarith, ?_⟩
      exact hεball (by rw [hdist]; linarith) (fun h0 => by
        rw [h0, dist_self] at hdist; linarith)
    have hRz : R z = L z := sub_eq_zero.mp (hzero hzU)
    have hfar' : ∀ i, i ≠ i₀ → ε / 2 ≤ ‖z - w i‖ := fun i hi =>
      expCesaro_aux_dist (x := z) (z := w i₀) (w := w i) (r := ε) (by rw [hdist]; linarith)
        (hfar i hi)
    have hsumm : Summable fun i => b i / (z - w i) := by
      refine Summable.of_norm_bounded (g := fun i => ‖b i‖ * (1 / δ)) (hb.norm.mul_right _)
        fun i => ?_
      by_cases hi : i = i₀
      · subst hi
        exact expCesaro_norm_div_le hδ0
          (by rw [hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0])
      · exact expCesaro_norm_div_le hδ0 (by linarith [hfar' i hi])
    have hsplit := hsumm.tsum_eq_add_tsum_ite i₀
    have hS' : ‖∑' i, if i = i₀ then 0 else b i / (z - w i)‖ ≤ C₂ := by
      rw [hC₂, ← tsum_mul_right]
      refine tsum_of_norm_bounded (hb.norm.mul_right (1 / (ε / 2))).hasSum fun i => ?_
      by_cases hi : i = i₀
      · simp only [hi, ite_true, norm_zero]
        exact mul_nonneg (norm_nonneg _) (by positivity)
      · simp only [hi, ite_false]
        exact expCesaro_norm_div_le (by linarith) (hfar' i hi)
    have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ0.ne'
    have hdiff : (δ : ℂ) * L z - b i₀ =
        (δ : ℂ) * ∑' i, if i = i₀ then 0 else b i / (z - w i) := by
      have hR_eq : R z = ∑' i, b i / (z - w i) := rfl
      rw [hRz, hsplit, hzw] at hR_eq
      have hmul := congrArg ((δ : ℂ) * ·) hR_eq
      rw [mul_add, mul_div_cancel₀ _ hδc] at hmul
      linear_combination hmul
    rw [← hL_eq z, dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ0]
    exact mul_le_mul_of_nonneg_left hS' hδ0.le
  have hlim : Tendsto (fun δ : ℝ ↦ δ * C₂) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun δ : ℝ ↦ δ * C₂) (𝓝 0) (𝓝 (0 * C₂)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ ↦ dist_nonneg)
    (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hε)) hdist_le) hlim)

private theorem expCesaro_sum_by_parts (r : ℝ) (A : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), r ^ k * (A (k + 1) - A k)) =
      (1 - r) * (∑ k ∈ Finset.range N, r ^ k * A (k + 1)) + r ^ N * A (N + 1) - A 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := fun k ↦ r ^ k * A (k + 1))]
    ring

private theorem expCesaro_geom_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), r ^ k ≤ (1 - r)⁻¹ := by
  have h1 : 0 < 1 - r := sub_pos.mpr hr1
  have hid : (1 - r) * ∑ k ∈ Finset.range (N + 1), r ^ k = 1 - r ^ (N + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  have hle : (1 - r) * ∑ k ∈ Finset.range (N + 1), r ^ k ≤ 1 := by
    rw [hid]
    linarith [pow_nonneg hr0 (N + 1)]
  rwa [← one_div, le_div_iff₀' h1]

private theorem expCesaro_ioc_disjoint (x y z : ℝ) : Disjoint (Ioc x y) (Ioc y z) :=
  Set.disjoint_left.mpr fun _ ht1 ht2 ↦ ht1.2.not_gt ht2.1

private theorem expCesaro_linear_bound_laplace (g : ℝ → ℝ) (hg0 : ∀ y > 0, 0 ≤ g y)
    (hgi : ∀ Y > 0, IntegrableOn g (Ioc 0 Y)) {T M : ℝ} (hT : 0 < T) (hM : 0 < M)
    (hG : ∀ Y ≥ T, (∫ y in Ioc (0 : ℝ) Y, g y) ≤ M * Y) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y ↦ g y * Real.exp (-η * y)) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), g y * Real.exp (-η * y)) ≤ M * T / (1 - Real.exp (-η * T)) := by
  set r := Real.exp (-η * T)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  let G : ℕ → ℝ := fun k ↦ ∫ y in Ioc (0 : ℝ) ((k : ℝ) * T), g y
  have hG0 : G 0 = 0 := by simp [G]
  have hblock (k : ℕ) :
      IntegrableOn (fun y ↦ g y * Real.exp (-η * y)) (Ioc ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T)) ∧
      (∫ y in Ioc ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T), g y * Real.exp (-η * y)) ≤
        r ^ k * (G (k + 1) - G k) := by
    set a := (k : ℝ) * T
    set b := ((k + 1 : ℕ) : ℝ) * T
    have ha0 : 0 ≤ a := by positivity
    have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hg_0b : IntegrableOn g (Ioc 0 b) := hgi b hb0
    have hg_0a : IntegrableOn g (Ioc 0 a) := hg_0b.mono_set (Ioc_subset_Ioc_right hab)
    have hg_ab : IntegrableOn g (Ioc a b) := hg_0b.mono_set (Ioc_subset_Ioc_left ha0)
    have hrk : r ^ k = Real.exp (-η * a) := by
      dsimp [r, a]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hpt : ∀ y ∈ Ioc a b, g y * Real.exp (-η * y) ≤ r ^ k * g y := fun y hy ↦ by
      have hy0 : 0 < y := lt_of_le_of_lt ha0 hy.1
      rw [hrk, mul_comm (Real.exp (-η * a))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hy.1])) (hg0 y hy0)
    have hf_ab : IntegrableOn (fun y ↦ g y * Real.exp (-η * y)) (Ioc a b) := by
      refine (hg_ab.const_mul (r ^ k)).mono'
        (hg_ab.aestronglyMeasurable.mul
          ((Continuous.continuousOn (by fun_prop)).aestronglyMeasurable measurableSet_Ioc)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hy0 : 0 < y := lt_of_le_of_lt ha0 hy.1
      rw [Real.norm_of_nonneg (mul_nonneg (hg0 y hy0) (Real.exp_pos _).le)]
      exact hpt y hy
    have hunion : G (k + 1) = G k + ∫ y in Ioc a b, g y := by
      change (∫ y in Ioc (0 : ℝ) b, g y) = (∫ y in Ioc (0 : ℝ) a, g y) + ∫ y in Ioc a b, g y
      rw [← Ioc_union_Ioc_eq_Ioc ha0 hab,
        setIntegral_union (expCesaro_ioc_disjoint 0 a b) measurableSet_Ioc hg_0a hg_ab]
    refine ⟨hf_ab, ?_⟩
    calc (∫ y in Ioc a b, g y * Real.exp (-η * y))
        ≤ ∫ y in Ioc a b, r ^ k * g y :=
          setIntegral_mono_on hf_ab (hg_ab.const_mul _) measurableSet_Ioc hpt
      _ = r ^ k * ∫ y in Ioc a b, g y := integral_const_mul _ _
      _ = r ^ k * (G (k + 1) - G k) := by rw [hunion]; ring
  have hpref (N : ℕ) :
      IntegrableOn (fun y ↦ g y * Real.exp (-η * y)) (Ioc 0 (((N + 1 : ℕ) : ℝ) * T)) ∧
      (∫ y in Ioc (0 : ℝ) (((N + 1 : ℕ) : ℝ) * T), g y * Real.exp (-η * y)) ≤
        ∑ k ∈ Finset.range (N + 1), r ^ k * (G (k + 1) - G k) := by
    induction N with
    | zero =>
      obtain ⟨hi0, hb0⟩ := hblock 0
      simpa using And.intro hi0 hb0
    | succ N ih =>
      obtain ⟨hiN, hbN⟩ := ih
      obtain ⟨hik, hbk⟩ := hblock (N + 1)
      set a := ((N + 1 : ℕ) : ℝ) * T
      set b := ((N + 2 : ℕ) : ℝ) * T
      have ha0 : 0 ≤ a := by positivity
      have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
      have hunion_set : Ioc (0 : ℝ) b = Ioc 0 a ∪ Ioc a b := (Ioc_union_Ioc_eq_Ioc ha0 hab).symm
      refine ⟨by rw [hunion_set]; exact hiN.union hik, ?_⟩
      rw [hunion_set,
        setIntegral_union (expCesaro_ioc_disjoint 0 a b) measurableSet_Ioc hiN hik,
        Finset.sum_range_succ]
      exact add_le_add hbN hbk
  have hsum_le (N : ℕ) :
      ∑ k ∈ Finset.range (N + 1), r ^ k * (G (k + 1) - G k) ≤ M * T / (1 - r) := by
    rw [expCesaro_sum_by_parts r G N, hG0, sub_zero]
    have hGk (j : ℕ) : G (j + 1) ≤ M * (((j + 1 : ℕ) : ℝ) * T) := by
      refine hG (((j + 1 : ℕ) : ℝ) * T) ?_
      have hj1 : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
      nlinarith
    have h1 : (1 - r) * (∑ k ∈ Finset.range N, r ^ k * G (k + 1)) + r ^ N * G (N + 1) ≤
        M * T * ((1 - r) * (∑ k ∈ Finset.range N, r ^ k * ((k + 1 : ℕ) : ℝ)) +
          r ^ N * ((N + 1 : ℕ) : ℝ)) := by
      have hs : ∑ k ∈ Finset.range N, r ^ k * G (k + 1) ≤
          ∑ k ∈ Finset.range N, r ^ k * (M * (((k + 1 : ℕ) : ℝ) * T)) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hGk k) (pow_nonneg hr0 k)
      have hlast : r ^ N * G (N + 1) ≤ r ^ N * (M * (((N + 1 : ℕ) : ℝ) * T)) :=
        mul_le_mul_of_nonneg_left (hGk N) (pow_nonneg hr0 N)
      calc (1 - r) * (∑ k ∈ Finset.range N, r ^ k * G (k + 1)) + r ^ N * G (N + 1)
          ≤ (1 - r) * (∑ k ∈ Finset.range N, r ^ k * (M * (((k + 1 : ℕ) : ℝ) * T))) +
              r ^ N * (M * (((N + 1 : ℕ) : ℝ) * T)) :=
            add_le_add (mul_le_mul_of_nonneg_left hs h1r.le) hlast
        _ = M * T * ((1 - r) * (∑ k ∈ Finset.range N, r ^ k * ((k + 1 : ℕ) : ℝ)) +
              r ^ N * ((N + 1 : ℕ) : ℝ)) := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            congr 1
            · refine Finset.sum_congr rfl fun k _ ↦ ?_; ring
            · ring
    have hid_nat := expCesaro_sum_by_parts r (fun k : ℕ ↦ (k : ℝ)) N
    simp only [Nat.cast_zero, sub_zero] at hid_nat
    have hid_one : (∑ k ∈ Finset.range (N + 1), r ^ k * (((k + 1 : ℕ) : ℝ) - (k : ℝ))) =
        ∑ k ∈ Finset.range (N + 1), r ^ k := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      ring
    rw [hid_one] at hid_nat
    rw [← hid_nat] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_left (expCesaro_geom_sum_le hr0 hr1 N)
      (by positivity)).trans_eq (div_eq_mul_inv _ _).symm)
  let bseq : ℕ → ℝ := fun N ↦ ((N + 1 : ℕ) : ℝ) * T
  have hb_top : Tendsto bseq atTop atTop := by
    have hnat : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact hnat.atTop_mul_const hT
  have hnorm_eq (N : ℕ) :
      (∫ y in (0 : ℝ)..bseq N, ‖g y * Real.exp (-η * y)‖) =
        ∫ y in Ioc (0 : ℝ) (bseq N), g y * Real.exp (-η * y) := by
    rw [intervalIntegral.integral_of_le (by dsimp [bseq]; positivity)]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy ↦ ?_
    exact Real.norm_of_nonneg (mul_nonneg (hg0 y hy.1) (Real.exp_pos _).le)
  have hi : IntegrableOn (fun y ↦ g y * Real.exp (-η * y)) (Ioi 0) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded (M * T / (1 - r)) 0
      (fun N ↦ (hpref N).1) hb_top
      (Eventually.of_forall fun N ↦ by rw [hnorm_eq N]; exact (hpref N).2.trans (hsum_le N))
  refine ⟨hi, ?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hi hb_top
  refine le_of_tendsto' hlim fun N ↦ ?_
  rw [intervalIntegral.integral_of_le (by dsimp [bseq]; positivity)]
  exact (hpref N).2.trans (hsum_le N)

private theorem expCesaro_laplace_tendsto (g : ℝ → ℝ) (hg0 : ∀ y > 0, 0 ≤ g y)
    (hgi : ∀ Y > 0, IntegrableOn g (Ioc 0 Y))
    (hces : Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, g y) atTop (𝓝 0)) :
    (∀ η > 0, IntegrableOn (fun y ↦ g y * Real.exp (-η * y)) (Ioi 0)) ∧
      Tendsto (fun δ : ℝ ↦ δ * ∫ y in Ioi (0 : ℝ), g y * Real.exp (-δ * y))
        (𝓝[>] 0) (𝓝 0) := by
  have hexists : ∀ M > 0, ∃ T > 0, ∀ Y ≥ T, (∫ y in Ioc (0 : ℝ) Y, g y) ≤ M * Y := by
    intro M hM
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp (hces.eventually (gt_mem_nhds hM))
    refine ⟨max T₀ 1, by positivity, fun Y hY ↦ ?_⟩
    have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_right T₀ 1).trans hY)
    have hlt := hT₀ Y ((le_max_left T₀ 1).trans hY)
    have hmul := mul_lt_mul_of_pos_left hlt hYpos
    rw [← mul_assoc, mul_inv_cancel₀ hYpos.ne', one_mul, mul_comm Y M] at hmul
    exact hmul.le
  constructor
  · intro η hη
    obtain ⟨T, hT, hG⟩ := hexists 1 zero_lt_one
    exact (expCesaro_linear_bound_laplace g hg0 hgi hT zero_lt_one hG hη).1
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨T, hT, hG⟩ := hexists (ε / 4) (by positivity)
    filter_upwards [Ioo_mem_nhdsGT (div_pos zero_lt_one hT)] with δ ⟨hδ0, hδT⟩
    have hδT1 : δ * T < 1 := (lt_div_iff₀ hT).mp hδT
    obtain ⟨_, hbd⟩ := expCesaro_linear_bound_laplace g hg0 hgi hT (by positivity) hG hδ0
    have hnonneg : 0 ≤ δ * ∫ y in Ioi (0 : ℝ), g y * Real.exp (-δ * y) :=
      mul_nonneg hδ0.le (setIntegral_nonneg measurableSet_Ioi fun y hy ↦
        mul_nonneg (hg0 y hy) (Real.exp_pos _).le)
    have hden_lb : δ * T / 2 ≤ 1 - Real.exp (-δ * T) := by
      have hexp1 : 1 + δ * T ≤ Real.exp (δ * T) := by linarith [Real.add_one_le_exp (δ * T)]
      have hexp_inv : Real.exp (-δ * T) ≤ (1 + δ * T)⁻¹ := by
        rw [neg_mul, Real.exp_neg]
        exact inv_anti₀ (by positivity) hexp1
      have hpos1 : 0 < 1 + δ * T := by positivity
      have hfrac : δ * T / 2 ≤ 1 - (1 + δ * T)⁻¹ := by
        refine le_of_mul_le_mul_right ?_ hpos1
        have hrhs : (1 - (1 + δ * T)⁻¹) * (1 + δ * T) = δ * T := by
          field_simp [hpos1.ne']
          ring
        rw [hrhs]
        have hpos_dt : 0 < δ * T := mul_pos hδ0 hT
        nlinarith
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    calc δ * ∫ y in Ioi (0 : ℝ), g y * Real.exp (-δ * y)
        ≤ δ * ((ε / 4) * T / (1 - Real.exp (-δ * T))) :=
          mul_le_mul_of_nonneg_left hbd hδ0.le
      _ ≤ δ * ((ε / 4) * T / (δ * T / 2)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hden_lb) hδ0.le
      _ = ε / 2 := by field_simp [hδ0.ne', hT.ne']; ring
      _ < ε := half_lt_self hε

/-- **Zero-saving Cesàro uniqueness for exponential sums on a half-line (majorant form).**
Let the frequencies `w i` be distinct, have no accumulation point in `ℂ`, and satisfy
`Re (w i) ≤ 1/2`, and let `b` be summable. Suppose `‖S y‖ ≤ D y` on `y ≥ 0`, where
`D y * exp (-c * y)` is locally integrable on `(0, ∞)` and has Cesàro mean zero at the single
exponent `c`:
`Y⁻¹ * ∫_{y ∈ (0, Y]} D y * exp (-c * y) → 0` as `Y → ∞`.
Then `b i = 0` for **every** frequency in the closed half-plane `c ≤ Re (w i)` (boundary
`Re (w i) = c` included, with no exponent saving below `c`). -/
theorem eq_zero_of_hasSum_exp_of_cesaro_majorant {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (D : ℝ → ℝ) (hS : ∀ y : ℝ, 0 ≤ y → ‖S y‖ ≤ D y)
    (hDloc : ∀ Y > 0, IntegrableOn (fun y ↦ D y * Real.exp (-c * y)) (Ioc (0 : ℝ) Y))
    (hces : Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, D y * Real.exp (-c * y))
      atTop (𝓝 0)) :
    ∀ i, c ≤ (w i).re → b i = 0 := by
  let g : ℝ → ℝ := fun y ↦ D y * Real.exp (-c * y)
  have hg0 : ∀ y > 0, 0 ≤ g y := fun y hy ↦
    mul_nonneg ((norm_nonneg _).trans (hS y hy.le)) (Real.exp_pos _).le
  obtain ⟨hgi_all, hlim_zero⟩ := expCesaro_laplace_tendsto g hg0 hDloc hces
  have hDi : ∀ σ, c < σ → IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi (0 : ℝ)) := by
    intro σ hσ
    refine (hgi_all (σ - c) (sub_pos.mpr hσ)).congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
    dsimp [g]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hSc : ContinuousOn S (Ici 0) :=
    (expCesaro_continuousOn w b hre hb).congr fun y hy ↦ (h y hy).tsum_eq.symm
  intro i₀ hi₀
  have hres := tendsto_mul_laplace_of_hasSum_exp_of_integrable w b hw hdisc hre hb S h D hS hDi
    i₀ hi₀
  rcases lt_or_eq_of_le hi₀ with hlt | heq
  · set σ' := (c + (w i₀).re) / 2
    have hσ' : c < σ' := by dsimp [σ']; linarith
    set C₁ := ∫ y in Ioi (0 : ℝ), D y * Real.exp (-σ' * y)
    have hzero : Tendsto (fun δ : ℝ ↦ (δ : ℂ) *
        ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-((w i₀ + δ) * y))) (𝓝[>] 0) (𝓝 0) := by
      have hlimC : Tendsto (fun δ : ℝ ↦ δ * C₁) (𝓝[>] 0) (𝓝 0) := by
        have h0 : Tendsto (fun δ : ℝ ↦ δ * C₁) (𝓝 0) (𝓝 (0 * C₁)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero'
        (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlimC)
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      have hzre : σ' ≤ (w i₀ + (δ : ℂ)).re := by simp [σ']; linarith
      have hbd := (expCesaro_laplace_integrable S hSc D hS (hDi σ' hσ') hzre).2
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_left hbd hδ.le
    exact tendsto_nhds_unique hres hzero
  · have hzero : Tendsto (fun δ : ℝ ↦ (δ : ℂ) *
        ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-((w i₀ + δ) * y))) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero'
        (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim_zero)
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      have hzre : c + δ ≤ (w i₀ + (δ : ℂ)).re := by simp [← heq]
      have hDi_δ : IntegrableOn (fun y ↦ D y * Real.exp (-(c + δ) * y)) (Ioi 0) :=
        hDi (c + δ) (by linarith)
      have hbd := (expCesaro_laplace_integrable S hSc D hS hDi_δ hzre).2
      have hg_eq : (∫ y in Ioi (0 : ℝ), D y * Real.exp (-(c + δ) * y)) =
          ∫ y in Ioi (0 : ℝ), g y * Real.exp (-δ * y) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
        dsimp [g]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, ← hg_eq]
      exact mul_le_mul_of_nonneg_left hbd hδ.le
    exact tendsto_nhds_unique hres hzero

/-- **Zero-saving Cesàro uniqueness for exponential sums on a half-line.**
If `Y⁻¹ * ∫_{y ∈ (0, Y]} ‖S y‖ * exp (-c * y) → 0` as `Y → ∞`, then every frequency in the closed
half-plane `c ≤ Re (w i)` has `b i = 0`. No majorant or strictly smaller exponent is needed. -/
theorem eq_zero_of_hasSum_exp_of_cesaro {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (hces : Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, ‖S y‖ * Real.exp (-c * y))
      atTop (𝓝 0)) :
    ∀ i, c ≤ (w i).re → b i = 0 := by
  have hSc : ContinuousOn S (Ici 0) :=
    (expCesaro_continuousOn w b hre hb).congr fun y hy ↦ (h y hy).tsum_eq.symm
  have hloc : ∀ Y > 0, IntegrableOn (fun y ↦ ‖S y‖ * Real.exp (-c * y)) (Ioc 0 Y) := fun Y _ ↦ by
    have hc_icc : ContinuousOn (fun y ↦ ‖S y‖ * Real.exp (-c * y)) (Icc 0 (max Y 0)) :=
      (hSc.mono Icc_subset_Ici_self).norm.mul (Continuous.continuousOn (by fun_prop))
    exact hc_icc.integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right (le_max_left Y 0)))
  exact eq_zero_of_hasSum_exp_of_cesaro_majorant w b hw hdisc hre hb S h (fun y ↦ ‖S y‖)
    (fun _ _ ↦ le_rfl) hloc hces

/-- **Little-`o` uniqueness at the critical exponent:** if `‖S y‖ * exp (-c * y) → 0` as `y → ∞`,
then `b i = 0` for all `c ≤ Re (w i)` (`eq_zero_of_hasSum_exp_of_cesaro`). -/
theorem eq_zero_of_hasSum_exp_of_tendsto_zero {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (ho : Tendsto (fun y : ℝ ↦ ‖S y‖ * Real.exp (-c * y)) atTop (𝓝 0)) :
    ∀ i, c ≤ (w i).re → b i = 0 := by
  refine eq_zero_of_hasSum_exp_of_cesaro w b hw hdisc hre hb S h ?_
  let g : ℝ → ℝ := fun y ↦ ‖S y‖ * Real.exp (-c * y)
  have hSc : ContinuousOn S (Ici 0) :=
    (expCesaro_continuousOn w b hre hb).congr fun y hy ↦ (h y hy).tsum_eq.symm
  have hloc : ∀ Y ≥ 0, IntegrableOn g (Ioc 0 Y) := fun Y _ ↦ by
    have hc_icc : ContinuousOn g (Icc 0 (max Y 0)) :=
      (hSc.mono Icc_subset_Ici_self).norm.mul (Continuous.continuousOn (by fun_prop))
    exact hc_icc.integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right (le_max_left Y 0)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp (ho.eventually (gt_mem_nhds (half_pos hε)))
  set A := max Y₀ 1
  have hA0 : 0 ≤ A := by positivity
  set M₀ := ∫ y in Ioc (0 : ℝ) A, g y
  have hM₀ : 0 ≤ M₀ := setIntegral_nonneg measurableSet_Ioc fun y _ ↦
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  filter_upwards [eventually_ge_atTop (max A (2 * (M₀ + 1) / ε))] with Y hY
  have hYA : A ≤ Y := (le_max_left _ _).trans hY
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_right Y₀ 1).trans hYA)
  have hnonneg : 0 ≤ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, g y :=
    mul_nonneg (inv_nonneg.mpr hYpos.le) (setIntegral_nonneg measurableSet_Ioc fun y _ ↦
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hunion : (∫ y in Ioc (0 : ℝ) Y, g y) = M₀ + ∫ y in Ioc A Y, g y := by
    rw [← Ioc_union_Ioc_eq_Ioc hA0 hYA,
      setIntegral_union (expCesaro_ioc_disjoint 0 A Y) measurableSet_Ioc (hloc A hA0)
        ((hloc Y hYpos.le).mono_set (Ioc_subset_Ioc_left hA0))]
  have htail : (∫ y in Ioc A Y, g y) ≤ (ε / 2) * Y := by
    have hc_const : IntegrableOn (fun _ : ℝ ↦ ε / 2) (Ioc A Y) := integrableOn_const (by simp)
    calc (∫ y in Ioc A Y, g y)
        ≤ ∫ _ in Ioc A Y, ε / 2 :=
          setIntegral_mono_on ((hloc Y hYpos.le).mono_set (Ioc_subset_Ioc_left hA0))
            hc_const measurableSet_Ioc fun y hy ↦
              (hY₀ y ((le_max_left Y₀ 1).trans hy.1.le)).le
      _ = (Y - A) * (ε / 2) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hYA, smul_eq_mul]
      _ ≤ (ε / 2) * Y := by nlinarith
  have hM_lt : M₀ < (ε / 2) * Y := by
    have hY2 : 2 * (M₀ + 1) / ε ≤ Y := (le_max_right _ _).trans hY
    have hmul := (div_le_iff₀ hε).mp hY2
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, hunion]
  calc Y⁻¹ * (M₀ + ∫ y in Ioc A Y, g y)
      < Y⁻¹ * ((ε / 2) * Y + (ε / 2) * Y) :=
        mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le hM_lt htail) (inv_pos.mpr hYpos)
    _ = ε := by field_simp [hYpos.ne']; ring

/-- **Endpoint `L¹` uniqueness:** if `‖S y‖ * exp (-c * y)` is integrable on `(0, ∞)` at the
single exponent `c`, then `b i = 0` for all `c ≤ Re (w i)`. -/
theorem eq_zero_of_hasSum_exp_of_endpoint_integrable {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (hint : IntegrableOn (fun y : ℝ ↦ ‖S y‖ * Real.exp (-c * y)) (Ioi (0 : ℝ))) :
    ∀ i, c ≤ (w i).re → b i = 0 := by
  refine eq_zero_of_hasSum_exp_of_cesaro w b hw hdisc hre hb S h ?_
  set I := ∫ y in Ioi (0 : ℝ), ‖S y‖ * Real.exp (-c * y)
  have hlim : Tendsto (fun Y : ℝ ↦ Y⁻¹ * I) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const I
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact mul_nonneg (inv_nonneg.mpr hY.le) (setIntegral_nonneg measurableSet_Ioc fun _ _ ↦
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hY.le)
    exact setIntegral_mono_set hint
      (ae_of_all _ fun x : ℝ ↦ mul_nonneg (norm_nonneg (S x)) (Real.exp_pos (-c * x)).le)
      (Eventually.of_forall fun x (hx : x ∈ Ioc (0 : ℝ) Y) ↦ hx.1)

/-- **Endpoint `L²` uniqueness:** if `‖S y‖ ^ 2 * exp (-2 * c * y)` is integrable on `(0, ∞)` at
the single exponent `c`, then `b i = 0` for all `c ≤ Re (w i)`. -/
theorem eq_zero_of_hasSum_exp_of_sq_integrable {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (hsq : IntegrableOn (fun y : ℝ ↦ ‖S y‖ ^ 2 * Real.exp (-2 * c * y)) (Ioi (0 : ℝ))) :
    ∀ i, c ≤ (w i).re → b i = 0 := by
  refine eq_zero_of_hasSum_exp_of_cesaro w b hw hdisc hre hb S h ?_
  let g : ℝ → ℝ := fun y ↦ ‖S y‖ * Real.exp (-c * y)
  have hSc : ContinuousOn S (Ici 0) :=
    (expCesaro_continuousOn w b hre hb).congr fun y hy ↦ (h y hy).tsum_eq.symm
  have hloc : ∀ Y > 0, IntegrableOn g (Ioc 0 Y) := fun Y _ ↦ by
    have hc_icc : ContinuousOn g (Icc 0 (max Y 0)) :=
      (hSc.mono Icc_subset_Ici_self).norm.mul (Continuous.continuousOn (by fun_prop))
    exact hc_icc.integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right (le_max_left Y 0)))
  have hg2 : ∀ y : ℝ, g y ^ 2 = ‖S y‖ ^ 2 * Real.exp (-2 * c * y) := fun y ↦ by
    dsimp [g]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsq' : IntegrableOn (fun y ↦ g y ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [hg2] using hsq
  set I₂ := ∫ y in Ioi (0 : ℝ), g y ^ 2
  have hI₂ : 0 ≤ I₂ := setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ sq_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 1 ((I₂ + 1) / ε ^ 2))] with Y hY
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hY.le)
  have hnonneg : 0 ≤ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, g y :=
    mul_nonneg (inv_nonneg.mpr hYpos.le) (setIntegral_nonneg measurableSet_Ioc fun _ _ ↦
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hdom : IntegrableOn (fun y ↦ ε / 2 + g y ^ 2 / (2 * ε)) (Ioc 0 Y) :=
    (integrableOn_const (by simp)).add ((hsq'.mono_set Ioc_subset_Ioi_self).div_const _)
  have hint_le : (∫ y in Ioc (0 : ℝ) Y, g y) ≤ Y * (ε / 2) + I₂ / (2 * ε) := by
    calc (∫ y in Ioc (0 : ℝ) Y, g y)
        ≤ ∫ y in Ioc (0 : ℝ) Y, (ε / 2 + g y ^ 2 / (2 * ε)) := by
          refine setIntegral_mono_on (hloc Y hYpos) hdom measurableSet_Ioc fun y _ ↦ ?_
          have hsq0 := sq_nonneg (g y - ε)
          have h2ε : 0 < 2 * ε := by positivity
          refine le_of_mul_le_mul_right ?_ h2ε
          have hrhs : (ε / 2 + g y ^ 2 / (2 * ε)) * (2 * ε) = ε ^ 2 + g y ^ 2 := by
            field_simp [hε.ne']
          rw [hrhs]
          nlinarith
      _ = (∫ _ in Ioc (0 : ℝ) Y, ε / 2) + ∫ y in Ioc (0 : ℝ) Y, g y ^ 2 / (2 * ε) :=
          integral_add (integrableOn_const (by simp))
            ((hsq'.mono_set Ioc_subset_Ioi_self).div_const _)
      _ = Y * (ε / 2) + (∫ y in Ioc (0 : ℝ) Y, g y ^ 2) / (2 * ε) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hYpos.le, sub_zero, smul_eq_mul,
            integral_div]
      _ ≤ Y * (ε / 2) + I₂ / (2 * ε) := by
          gcongr
          exact setIntegral_mono_set hsq' (ae_of_all _ fun x : ℝ ↦ sq_nonneg (g x))
            (Eventually.of_forall fun x (hx : x ∈ Ioc (0 : ℝ) Y) ↦ hx.1)
  have htail_lt : I₂ / (2 * ε) < Y * (ε / 2) := by
    have hY2 : (I₂ + 1) / ε ^ 2 < Y := lt_of_le_of_lt (le_max_right _ _) hY
    have hmul := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hY2
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  calc Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, g y
      ≤ Y⁻¹ * (Y * (ε / 2) + I₂ / (2 * ε)) :=
        mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hYpos.le)
    _ < Y⁻¹ * (Y * (ε / 2) + Y * (ε / 2)) :=
        mul_lt_mul_of_pos_left (add_lt_add_right htail_lt _) (inv_pos.mpr hYpos)
    _ = ε := by field_simp [hYpos.ne']; ring

end RiemannMasullo
