module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Abel limits of square-integrable Fourier transforms on the real line

The Poisson kernel is a positive mixture of interval averages. Lebesgue differentiation
therefore gives convergence at almost every frequency. Plancherel identifies this
Poisson integral with exponential damping in the original variable.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Metric
open scoped ENNReal NNReal Topology FourierTransform

namespace RiemannMasullo

private def poissonRadialDerivative (r : ℝ) := 2*r / (1+r^2)^2

private theorem integrable_poissonRadialWeight :
    Integrable (fun r : ℝ ↦ r * poissonRadialDerivative r) := by
  apply (integrable_inv_one_add_sq.const_mul 2).mono' (by unfold poissonRadialDerivative; fun_prop)
  filter_upwards with r
  unfold poissonRadialDerivative
  rw [show r*(2*r/(1+r^2)^2) = 2*r^2/(1+r^2)^2 by ring, Real.norm_of_nonneg (by positivity)]
  have hr : 0 < 1+r^2 := by positivity
  rw [div_le_iff₀ (sq_pos_of_pos hr)]
  field_simp
  nlinarith [sq_nonneg r]

private theorem integral_poissonRadialDerivative {R : ℝ} (hR : 0 ≤ R) :
    ∫ r in Ioi R, poissonRadialDerivative r = (1+R^2)⁻¹ := by
  have hD (r : ℝ) : HasDerivAt (fun t : ℝ ↦ -(1+t^2)⁻¹) (poissonRadialDerivative r) r := by
    have h : HasDerivAt (fun t : ℝ ↦ 1+t^2) (2*r) r := by
      convert! (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2) using 1
      simp
    convert! (h.inv (by dsimp; positivity)).neg using 1
    simp [poissonRadialDerivative]
    ring
  have hlim : Tendsto (fun r : ℝ ↦ -(1+r^2)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ ↦ 1+r^2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by decide : 2 ≠ 0))
    simpa only [neg_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp h).neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun r _ ↦ hD r) (fun r hr ↦
    by unfold poissonRadialDerivative; exact div_nonneg (mul_nonneg two_pos.le (hR.trans hr.le)) (sq_nonneg _)) hlim
  simpa using h

/-- The radial kernel is a positive mixture of indicators of intervals about the center. -/
private theorem poissonRadial_mixture (h : ℝ → ℝ) (hm : Measurable h) (hl : LocallyIntegrable h volume)
    (hpos : ∀ x, 0 ≤ h x) (y δ B : ℝ) (hδ : 0 < δ)
    (hB : ∀ r > 0, (∫ x in closedBall y r, h x) ≤ 2*r*B) :
    (∫ x : ℝ, (1 + (dist x y / δ)^2)⁻¹ * h x) =
      ∫ r in Ioi (0 : ℝ), poissonRadialDerivative r * ∫ x in closedBall y (δ*r), h x := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let G (r x : ℝ) := (closedBall y (δ*r)).indicator (fun t ↦ poissonRadialDerivative r * h t) x
  have hq {r : ℝ} (hr : 0 ≤ r) : 0 ≤ poissonRadialDerivative r := by unfold poissonRadialDerivative; positivity
  have hG : Measurable (uncurry G) := by
    change Measurable (fun p : ℝ × ℝ ↦ if dist p.2 y ≤ δ*p.1 then poissonRadialDerivative p.1 * h p.2 else 0)
    exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by unfold poissonRadialDerivative; fun_prop) measurable_const
  have hleft (r : ℝ) : ∫ x, G r x = poissonRadialDerivative r * ∫ x in closedBall y (δ*r), h x := by
    simp only [G, integral_indicator measurableSet_closedBall, integral_const_mul]
  have hi : Integrable (uncurry G) (μ.prod volume) := by
    apply (integrable_prod_iff hG.aestronglyMeasurable).2
    refine ⟨ae_of_all _ (fun r ↦ ?_), ?_⟩
    · change Integrable ((closedBall y (δ*r)).indicator (fun x ↦ poissonRadialDerivative r * h x)) volume
      exact (integrable_indicator_iff measurableSet_closedBall).2 ((hl.integrableOn_isCompact (isCompact_closedBall y (δ*r))).const_mul _)
    · apply ((integrable_poissonRadialWeight.const_mul (2*δ*B)).integrableOn).mono'
        hG.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
      have hn (x : ℝ) : 0 ≤ G r x := Set.indicator_nonneg (fun x _ ↦ mul_nonneg (hq hr.le) (hpos x)) x
      change ‖∫ x, ‖G r x‖‖ ≤ 2*δ*B*(r*poissonRadialDerivative r)
      simp only [Real.norm_of_nonneg (hn _)]
      rw [Real.norm_of_nonneg (integral_nonneg hn), hleft]
      calc
        _ ≤ poissonRadialDerivative r * (2*(δ*r)*B) := mul_le_mul_of_nonneg_left (hB _ (mul_pos hδ hr)) (hq hr.le)
        _ = _ := by ring
  rw [← show (∫ r in Ioi (0 : ℝ), ∫ x, G r x) = _ from integral_congr_ae (ae_of_all _ hleft),
    integral_integral_swap hi]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  let R := dist x y / δ
  have hR : 0 ≤ R := div_nonneg dist_nonneg hδ.le
  have hright (r : ℝ) : G r x = (Ici R).indicator (fun t ↦ poissonRadialDerivative t * h x) r := by
    simp only [G, Set.indicator, mem_closedBall, mem_Ici, R, div_le_iff₀ hδ, mul_comm δ r]
  change (1+R^2)⁻¹*h x = ∫ r in Ioi 0, G r x
  simp_rw [hright]
  rw [setIntegral_indicator measurableSet_Ici]
  have heq : Ioi (0 : ℝ) ∩ Ici R =ᵐ[volume] Ioi R := by
    filter_upwards [show ∀ᵐ t : ℝ, t ≠ R from by simp [ae_iff]] with t ht
    change (0 < t ∧ R ≤ t) ↔ (R < t)
    exact ⟨fun h ↦ lt_of_le_of_ne h.2 ht.symm, fun h ↦ ⟨hR.trans_lt h, h.le⟩⟩
  rw [setIntegral_congr_set heq, integral_mul_const, integral_poissonRadialDerivative hR]

private theorem poisson_average_bounded (u : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ)
    (hy : Tendsto (fun r : ℝ ↦ ⨍ x in closedBall y r, ‖u x - u y‖) (𝓝[>] 0) (𝓝 0)) :
    ∃ B : ℝ, ∀ r > 0, ∫ x in closedBall y r, ‖u x - u y‖ ≤ 2*r*B := by
  obtain ⟨ε, hε, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hy.eventually (gt_mem_nhds zero_lt_one))
  have hε' : 0 < ε := hε
  let C := ∫ x, ‖u x‖^2
  have hC : 0 ≤ C := integral_nonneg fun x ↦ sq_nonneg _
  have hs := (Lp.memLp u).norm.integrable_sq
  refine ⟨max 1 (1 + ‖u y‖ + C/(2*ε)), fun r hr ↦ ?_⟩
  rcases lt_or_ge r ε with h | h
  · have h₁ := hsmall (show r ∈ Ioo 0 ε from ⟨hr, h⟩)
    change (⨍ x in closedBall y r, ‖u x - u y‖) < 1 at h₁
    rw [setAverage_eq, Real.volume_real_closedBall hr.le, smul_eq_mul, ← div_eq_inv_mul] at h₁
    have h₂ := (div_lt_iff₀ (mul_pos two_pos hr)).mp h₁
    exact h₂.le.trans (by linarith [mul_le_mul_of_nonneg_left (le_max_left 1 (1+‖u y‖+C/(2*ε))) (mul_pos two_pos hr).le])
  · let S := closedBall y r
    have hloc := (Lp.memLp u).locallyIntegrable one_le_two
    have ht : IntegrableOn (fun x ↦ ‖u x - u y‖) S := ((hloc.integrableOn_isCompact (isCompact_closedBall y r)).sub (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall y r))).norm
    have hpt (x : ℝ) : ‖u x - u y‖ ≤ (1+‖u y‖) + ‖u x‖^2 := by
      nlinarith [norm_sub_le (u x) (u y), sq_nonneg (‖u x‖-1/2)]
    have hconst : IntegrableOn (fun _ : ℝ ↦ 1+‖u y‖) S := continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall y r)
    have hi := integral_mono ht (hconst.add hs.integrableOn) hpt
    simp only [Pi.add_apply] at hi
    rw [integral_add hconst hs.integrableOn, setIntegral_const, smul_eq_mul] at hi
    rw [show volume.real S = 2*r from Real.volume_real_closedBall hr.le] at hi
    have hcomp : (∫ x in S, ‖u x‖ ^ 2) ≤ C := setIntegral_le_integral hs (ae_of_all _ fun _ ↦ sq_nonneg _)
    have hscale : C ≤ 2*r*(C/(2*ε)) := by
      calc
        C = 2*ε*(C/(2*ε)) := by field_simp [hε'.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact hi.trans ((by linarith : 2*r*(1+‖u y‖) + ∫ x in S, ‖u x‖^2 ≤ 2*r*(1+‖u y‖+C/(2*ε))).trans
      (mul_le_mul_of_nonneg_left (le_max_right ..) (mul_pos two_pos hr).le))

private def halfPlanePoissonKernel (δ y x : ℝ) : ℝ :=
  (Real.pi * δ)⁻¹ * (1+(dist x y / δ)^2)⁻¹

private theorem halfPlanePoissonKernel_eq {δ : ℝ} (hδ : 0 < δ) (y x : ℝ) :
    halfPlanePoissonKernel δ y x = ProbabilityTheory.cauchyPDFReal y ⟨δ,hδ.le⟩ x := by
  rw [halfPlanePoissonKernel, ProbabilityTheory.cauchyPDFReal_def' y (⟨δ, hδ.le⟩ : ℝ≥0) x, Real.dist_eq]
  change (Real.pi*δ)⁻¹ * (1+(|x-y|/δ)^2)⁻¹ = Real.pi⁻¹ * δ⁻¹ * (1+((x-y)/δ)^2)⁻¹
  simp only [div_pow, sq_abs, mul_inv_rev]
  ring

private theorem halfPlanePoissonKernel_ae_norm (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ y : ℝ, Tendsto (fun δ : ℝ ↦ ∫ x : ℝ, halfPlanePoissonKernel δ y x * ‖u x - u y‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hloc := (Lp.memLp u).locallyIntegrable one_le_two
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1] with y hy
  let h (x : ℝ) := ‖u x - u y‖
  have hm : Measurable h := (Lp.stronglyMeasurable u).measurable.sub measurable_const |>.norm
  have hl : LocallyIntegrable h volume := locallyIntegrable_iff.mpr (fun S hS ↦
    ((hloc.integrableOn_isCompact hS).sub (continuous_const.continuousOn.integrableOn_compact hS)).norm)
  have hpos (x) : 0 ≤ h x := norm_nonneg _
  let A (r : ℝ) := (2*r)⁻¹ * ∫ x in closedBall y r, h x
  have h_avg {r : ℝ} (hr : 0 ≤ r) : (⨍ x in closedBall y r, ‖u x - u y‖) = A r := by
    rw [setAverage_eq, Real.volume_real_closedBall hr]
    rfl
  have hδpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hlim := hy (fun _ : ℝ ↦ y) id (tendsto_id (x := 𝓝[>] (0 : ℝ)))
    (hδpos.mono fun r hr ↦ mem_closedBall_self (by simpa using hr.le))
  obtain ⟨B, hB⟩ := poisson_average_bounded u y hlim
  have hA : Measurable A := by
    have hh : Measurable (fun p : ℝ × ℝ ↦ (closedBall y p.1).indicator h p.2) :=
      Measurable.ite (measurableSet_le (by fun_prop) measurable_fst) (hm.comp measurable_snd) measurable_const
    have hint := hh.stronglyMeasurable.integral_prod_right' (ν := volume)
    have heq (r : ℝ) : ∫ x, (closedBall y r).indicator h x = ∫ x in closedBall y r, h x :=
      integral_indicator measurableSet_closedBall
    simp only [heq] at hint
    exact (by fun_prop : Measurable (fun r : ℝ ↦ (2*r)⁻¹)).mul hint.measurable
  have hAlim : Tendsto A (𝓝[>] 0) (𝓝 0) :=
    hlim.congr' (hδpos.mono fun _ hr ↦ h_avg hr.le)
  let w (r : ℝ) := (2/Real.pi) * (r*poissonRadialDerivative r)
  have hw : Integrable w := integrable_poissonRadialWeight.const_mul _
  have hwpos {r : ℝ} (hr : 0 ≤ r) : 0 ≤ w r := by dsimp [w, poissonRadialDerivative]; positivity
  have hEq (δ : ℝ) (hδ : 0 < δ) : (∫ x, halfPlanePoissonKernel δ y x * h x) =
      ∫ r in Ioi 0, w r * A (δ*r) := by
    simp only [halfPlanePoissonKernel, mul_assoc]
    rw [integral_const_mul, poissonRadial_mixture h hm hl hpos y δ B hδ hB, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [w,A]
    have hr' : 0 < r := hr
    field_simp
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (l := 𝓝[>] (0 : ℝ)) (F := fun δ r ↦ w r * A (δ*r)) (f := fun _ ↦ (0 : ℝ))
    (fun r ↦ w r * B) (Eventually.of_forall (fun δ ↦ (hw.aestronglyMeasurable.mul
      ((hA.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)).mono_measure Measure.restrict_le_self))
    ?_ (hw.mul_const B).integrableOn ?_
  · simpa using ht.congr' (hδpos.mono fun δ hδ ↦ (hEq δ hδ).symm)
  · filter_upwards [hδpos] with δ hδ
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
    have hd : 0 < δ*r := mul_pos hδ hr
    have h₂ : 0 ≤ A (δ*r) := mul_nonneg (by positivity) (integral_nonneg hpos)
    rw [Real.norm_of_nonneg (mul_nonneg (hwpos hr.le) h₂)]
    apply mul_le_mul_of_nonneg_left _ (hwpos hr.le)
    dsimp only [A]
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity : 0 < 2*(δ*r)), mul_comm B]
    exact hB _ hd
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with r hr
    have hd : Tendsto (fun δ : ℝ ↦ δ*r) (𝓝[>] 0) (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.mul continuous_const).continuousAt.tendsto : Tendsto (fun δ : ℝ ↦ δ*r) (𝓝[>] 0) _),
        hδpos.mono fun δ hδ ↦ mul_pos hδ hr⟩
    simpa using (hAlim.comp hd).const_mul (w r)

private def halfPlaneAbelTest (δ y x : ℝ) : ℂ :=
  Complex.exp ((-(2*Real.pi*δ*|x|) : ℝ) + (2*Real.pi*y*x : ℝ) * Complex.I)

private theorem halfPlaneAbelTest_norm (δ y x : ℝ) :
    ‖halfPlaneAbelTest δ y x‖ = Real.exp (-(2*Real.pi*δ*|x|)) := by
  simp [halfPlaneAbelTest, Complex.norm_exp]

private theorem integrable_exp_neg_abs {p : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ ↦ Real.exp (-(p*|x|))) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic hp 0).congr_fun _ measurableSet_Iic
    intro x hx
    simp [abs_of_nonpos hx]
  · apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hp) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_nonneg hx.le]

private theorem halfPlaneAbelTest_mem {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable (halfPlaneAbelTest δ y) ∧ MemLp (halfPlaneAbelTest δ y) 2 := by
  have hm : Continuous (halfPlaneAbelTest δ y) := by unfold halfPlaneAbelTest; fun_prop
  have hi := integrable_exp_neg_abs (show 0 < 2*Real.pi*δ by positivity)
  refine ⟨(integrable_norm_iff hm.aestronglyMeasurable).mp (by simpa only [halfPlaneAbelTest_norm] using hi), ?_⟩
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  apply (integrable_exp_neg_abs (show 0 < 2*(2*Real.pi*δ) by positivity)).congr
  filter_upwards with x
  rw [halfPlaneAbelTest_norm, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem fourier_halfPlaneAbelTest {δ : ℝ} (hδ : 0 < δ) (y t : ℝ) :
    𝓕 (halfPlaneAbelTest δ y) t = (ProbabilityTheory.cauchyPDFReal y (⟨δ,hδ.le⟩ : ℝ≥0) t : ℂ) := by
  let α : ℂ := 2*Real.pi*((δ : ℂ) + (y-t)*Complex.I)
  let β : ℂ := 2*Real.pi*((-δ : ℂ) + (y-t)*Complex.I)
  have hα : 0 < α.re := by dsimp [α]; simp [Complex.mul_re, Complex.mul_im]; positivity
  have hβ : β.re < 0 := by dsimp [β]; simp [Complex.mul_re, Complex.mul_im]; positivity
  let g (x : ℝ) := Complex.exp (↑(-2 * Real.pi * inner ℝ x t) * Complex.I) * halfPlaneAbelTest δ y x
  have hrep (x : ℝ) : g x = Complex.exp (↑(-(2*Real.pi*δ*|x|) : ℝ) + ↑(2*Real.pi*(y-t)*x : ℝ)*Complex.I) := by
    unfold g halfPlaneAbelTest
    rw [← Complex.exp_add, Real.inner_apply]
    congr 1
    push_cast
    ring
  have hleft (x) (hx : x ∈ Iic 0) : g x = Complex.exp (α*x) := by
    rw [hrep, abs_of_nonpos hx]
    unfold α
    congr 1
    push_cast
    ring
  have hright (x) (hx : x ∈ Ioi 0) : g x = Complex.exp (β*x) := by
    rw [hrep, abs_of_nonneg hx.le]
    unfold β
    congr 1
    push_cast
    ring
  have hiL := (integrableOn_exp_mul_complex_Iic hα 0).congr_fun (fun x hx ↦ (hleft x hx).symm) measurableSet_Iic
  have hiR := (integrableOn_exp_mul_complex_Ioi hβ 0).congr_fun (fun x hx ↦ (hright x hx).symm) measurableSet_Ioi
  rw [Real.fourier_eq']
  change ∫ x, g x = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hiL hiR, setIntegral_congr_fun measurableSet_Iic hleft,
    setIntegral_congr_fun measurableSet_Ioi hright, integral_exp_mul_complex_Iic hα,
    integral_exp_mul_complex_Ioi hβ, ProbabilityTheory.cauchyPDFReal_def y (⟨δ,hδ.le⟩ : ℝ≥0) t]
  change Complex.exp (α*(0 : ℝ))/α + -Complex.exp (β*(0 : ℝ))/β =
    ((Real.pi⁻¹ * δ * ((t-y)^2+δ^2)⁻¹ : ℝ) : ℂ)
  have h₁ : α ≠ 0 := fun h ↦ by simp [h] at hα
  have h₂ : β ≠ 0 := fun h ↦ by simp [h] at hβ
  have h₃ : ((t : ℂ)-y)^2+(δ : ℂ)^2 ≠ 0 := by exact_mod_cast (by positivity : 0 < (t-y)^2+δ^2).ne'
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp [h₁, h₂, h₃, Real.pi_ne_zero]
  dsimp [α,β]
  ring_nf
  simp [Complex.I_sq]
  ring

open scoped FourierTransform ComplexConjugate

/-- Abel damping of the Fourier integral of an L² class recovers its Plancherel transform
at almost every frequency. The frequency uses the convention with the factor 2π. -/
theorem fourier_L2_abel_limit (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ y : ℝ, Tendsto (fun δ : ℝ ↦ ∫ x : ℝ, g x *
      Complex.exp (↑(-(2*Real.pi*δ*|x|) : ℝ) - ↑(2*Real.pi*y*x : ℝ)*Complex.I))
      (𝓝[>] 0) (𝓝 ((𝓕 g : Lp ℂ 2 volume) y)) := by
  let u : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 g
  filter_upwards [halfPlanePoissonKernel_ae_norm u] with y hy
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ hy
  filter_upwards [show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin] with δ hδ
  obtain ⟨h₁,h₂⟩ := halfPlaneAbelTest_mem hδ y
  let e := h₂.toLp (halfPlaneAbelTest δ y)
  let K := halfPlanePoissonKernel δ y
  have hfe : ((𝓕 e : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] fun t ↦ (K t : ℂ) := by
    refine (fourier_L2_coeFn_of_integrable e (h₁.congr h₂.coeFn_toLp.symm)).trans (ae_of_all _ fun t ↦ ?_)
    rw [Real.fourier_congr_ae h₂.coeFn_toLp t, fourier_halfPlaneAbelTest hδ, ← halfPlanePoissonKernel_eq hδ]
  have hk (t : ℝ) : 0 ≤ K t := by dsimp [K,halfPlanePoissonKernel]; positivity
  have hmem : Integrable (fun t : ℝ ↦ u t * (K t : ℂ)) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (𝓕 e) u).congr
    filter_upwards [hfe] with x hx
    simp [RCLike.inner_apply, hx]
  have hnorm : Integrable K ∧ ∫ t, K t = 1 := by
    let s : ℝ≥0 := ⟨δ,hδ.le⟩
    have hne : s ≠ 0 := fun h ↦ hδ.ne' (congrArg NNReal.toReal h)
    have heq : K = ProbabilityTheory.cauchyPDFReal y s := funext (halfPlanePoissonKernel_eq hδ y)
    rw [heq]
    exact ⟨ProbabilityTheory.integrable_cauchyPDFReal _, ProbabilityTheory.integral_cauchyPDFReal_eq_one _ hne⟩
  have hp : (∫ x : ℝ, g x *
      Complex.exp (↑(-(2*Real.pi*δ*|x|) : ℝ) - ↑(2*Real.pi*y*x : ℝ)*Complex.I)) = inner ℂ e g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    rw [RCLike.inner_apply, hx, halfPlaneAbelTest, ← Complex.exp_conj]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg]
  have hconv : inner ℂ e g = ∫ t, u t * (K t : ℂ) := by
    rw [← Lp.inner_fourier_eq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfe] with t ht
    simp [RCLike.inner_apply, ht, u]
  have hz : ∫ t : ℝ, u y * (K t : ℂ) = u y := by
    rw [integral_const_mul, integral_complex_ofReal, hnorm.2]
    simp
  rw [hp, hconv, dist_eq_norm]
  change ‖(∫ t, u t * (K t : ℂ)) - u y‖ ≤ _
  have hzint : Integrable (fun t : ℝ ↦ u y * (K t : ℂ)) := hnorm.1.ofReal.const_mul (u y)
  rw [show (∫ t, u t * (K t : ℂ)) - u y = ∫ t, u t * (K t : ℂ) - u y * K t by
    rw [integral_sub hmem hzint, hz]]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk _), mul_comm]

end RiemannMasullo
