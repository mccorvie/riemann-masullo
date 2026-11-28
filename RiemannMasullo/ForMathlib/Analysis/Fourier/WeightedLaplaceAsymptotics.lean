module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Boundary asymptotics of an exponentially damped polynomial weight

For `s ≥ 0`, the weight `x ^ (2 * k) / (1 + x ^ 2) ^ (s / 2)` is asymptotic to
`x ^ (2 * k - s)` on the positive ray. When that exponent is greater than `-1`,
rescaling the Laplace integral by its damping parameter recovers Euler's Gamma integral.
The two-sided transform has the same leading constant when the damping vanishes at either edge.
At exponent `-1` it grows logarithmically, with coefficient one. Below this exponent it
converges to the absolutely convergent endpoint integral.
-/

public noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace RiemannMasullo

private def polynomialWeight (k : ℕ) (s x : ℝ) : ℝ :=
  x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹

private theorem polynomialWeight_posRay {x : ℝ} (hx : 0 < x) (k : ℕ) (s : ℝ) :
    polynomialWeight k s x =
      x ^ ((2 * k : ℕ) - s : ℝ) * (1 + (1 / x) ^ 2) ^ (-(s / 2)) := by
  have hsplit : 1 + x ^ 2 = x ^ 2 * (1 + (1 / x) ^ 2) := by field_simp; ring
  have hpow : (x ^ (2 : ℕ)) ^ (-(s / 2)) = x ^ (-s) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  dsimp only [polynomialWeight]
  rw [← Real.rpow_neg (by positivity), hsplit, Real.mul_rpow (by positivity) (by positivity),
    hpow, Real.rpow_sub hx, Real.rpow_neg hx.le, Real.rpow_natCast]
  ring

private def laplaceRay (k : ℕ) (s t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-(t * x)) * polynomialWeight k s x

private theorem laplaceRay_scaled (k : ℕ) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    t ^ ((2 * k : ℕ) - s + 1 : ℝ) * laplaceRay k s t =
      ∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ ((2 * k : ℕ) - s : ℝ)) *
        (1 + (t / x) ^ 2) ^ (-(s / 2)) := by
  let p : ℝ := (2 * k : ℕ) - s
  let f (x : ℝ) := (Real.exp (-x) * x ^ p) * (1 + (t / x) ^ 2) ^ (-(s / 2))
  change t ^ (p + 1) * laplaceRay k s t = ∫ x in Ioi 0, f x
  have hres := integral_comp_mul_left_Ioi' f 0 ht
  rw [mul_zero, smul_eq_mul] at hres
  rw [← hres, Real.rpow_add ht, Real.rpow_one, mul_right_comm (t ^ p), mul_comm _ t]
  congr 1
  dsimp only [laplaceRay]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : 0 < x := hx
  dsimp only
  rw [polynomialWeight_posRay hx']
  dsimp only [f, p]
  rw [Real.mul_rpow ht.le hx'.le, show t / (t * x) = 1 / x by field_simp]
  ring

/-- The normalized contribution from the ray on which the exponential damping tends to zero
converges to the Gamma integral for every tail exponent greater than `-1`. -/
private theorem laplaceRay_scaled_tendsto (k : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hp : -1 < ((2 * k : ℕ) - s : ℝ)) :
    Tendsto (fun t : ℝ ↦ t ^ ((2 * k : ℕ) - s + 1 : ℝ) * laplaceRay k s t)
      (𝓝[>] 0) (𝓝 (Real.Gamma ((2 * k : ℕ) - s + 1 : ℝ))) := by
  let p : ℝ := (2 * k : ℕ) - s
  let g (x : ℝ) := Real.exp (-x) * x ^ p
  let f (t x : ℝ) := g x * (1 + (t / x) ^ 2) ^ (-(s / 2))
  have hp' : 0 < p + 1 := by dsimp [p]; linarith
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [g, add_sub_cancel_right] using Real.GammaIntegral_convergent hp'
  have hgint : ∫ x in Ioi 0, g x = Real.Gamma (p + 1) := by
    rw [Real.Gamma_eq_integral hp', add_sub_cancel_right]
  have hlim : Tendsto (fun t ↦ ∫ x in Ioi 0, f t x) (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, g x)) := by
    apply tendsto_integral_filter_of_dominated_convergence g
    · exact Eventually.of_forall fun t ↦ by dsimp [f, g]; fun_prop
    · apply Eventually.of_forall
      intro t
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      have hx' : 0 < x := hx
      have hgpos : 0 ≤ g x := by dsimp [g]; positivity
      have hc : (1 + (t / x) ^ 2) ^ (-(s / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (t / x)]) (by linarith)
      dsimp only [f]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgpos (by positivity))]
      exact mul_le_of_le_one_right hgpos hc
    · exact hg
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      have hx' : 0 < x := hx
      have hbase : Continuous (fun t : ℝ ↦ 1 + (t / x) ^ 2) := by fun_prop
      have hc : ContinuousAt (fun t : ℝ ↦ g x * (1 + (t / x) ^ 2) ^ (-(s / 2))) 0 :=
        continuousAt_const.mul (hbase.continuousAt.rpow_const (Or.inl (by simp)))
      have hh : Tendsto (fun t : ℝ ↦ f t x) (𝓝[>] (0 : ℝ)) (𝓝 (f 0 x)) :=
        hc.continuousWithinAt
      simpa [f] using hh
  rw [hgint] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (laplaceRay_scaled k s ht).symm

private theorem polynomialWeight_nonneg (k : ℕ) (s x : ℝ) : 0 ≤ polynomialWeight k s x := by
  unfold polynomialWeight
  rw [pow_mul]
  exact mul_nonneg (pow_nonneg (sq_nonneg x) k) (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))

private theorem polynomialWeight_neg (k : ℕ) (s x : ℝ) : polynomialWeight k s (-x) = polynomialWeight k s x := by
  simp [polynomialWeight, pow_mul]

private theorem laplaceRay_integrable (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    IntegrableOn (fun x ↦ Real.exp (-(t * x)) * polynomialWeight k s x) (Ioi 0) := by
  have hm : IntegrableOn (fun x : ℝ ↦ Real.exp (-(t * x)) * x ^ (2 * k)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((2 * k : ℕ) : ℝ))
      (by push_cast; nlinarith [Nat.cast_nonneg k (α := ℝ)]) (show (0 : ℝ) < 1 by norm_num) ht
    convert h using 1
    funext x
    simp only [Real.rpow_one, Real.rpow_natCast]
    ring_nf
  apply hm.mono' (by dsimp [polynomialWeight]; fun_prop)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  have hx' : 0 < x := hx
  have hden := Real.one_le_rpow (show 1 ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x])
    (show 0 ≤ s / 2 by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (polynomialWeight_nonneg ..))]
  dsimp only [polynomialWeight]
  rw [← mul_assoc]
  apply mul_le_of_le_one_right (by positivity)
  exact inv_le_one_of_one_le₀ hden

private theorem laplaceRay_continuousAt (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ContinuousAt (laplaceRay k s) t := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ Real.exp (-(t / 2 * x)) * polynomialWeight k s x)
  · exact Eventually.of_forall fun u ↦ by dsimp [polynomialWeight]; fun_prop
  · filter_upwards [lt_mem_nhds (show t / 2 < t by linarith)] with u hu
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (polynomialWeight_nonneg ..))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hu.le hx'.le]))
      (polynomialWeight_nonneg ..)
  · exact laplaceRay_integrable k hs (by positivity)
  · refine ae_of_all _ fun x ↦ ?_
    exact (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (-(u * x)) * polynomialWeight k s x)).continuousAt

private theorem laplaceIntegral_eq_two_rays (k : ℕ) {s α b : ℝ} (hs : 0 ≤ s) (hb : |b| < α) :
    (∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) * polynomialWeight k s x) =
      laplaceRay k s (2 * (α - |b|)) + laplaceRay k s (2 * (α + |b|)) := by
  let f (x : ℝ) := Real.exp (2 * b * x - 2 * α * |x|) * polynomialWeight k s x
  have hpos : EqOn f (fun x ↦ Real.exp (-(2 * (α - b) * x)) * polynomialWeight k s x) (Ioi 0) := by
    intro x hx
    dsimp only [f]
    rw [abs_of_pos hx]
    ring_nf
  have hneg : EqOn (fun x ↦ f (-x)) (fun x ↦ Real.exp (-(2 * (α + b) * x)) * polynomialWeight k s x) (Ioi 0) := by
    intro x hx
    dsimp only [f]
    rw [abs_neg, abs_of_pos hx, polynomialWeight_neg]
    ring_nf
  have ip := (laplaceRay_integrable k hs (show 0 < 2 * (α - b) by linarith [(abs_lt.mp hb).2])).congr_fun
    hpos.symm measurableSet_Ioi
  have ineg := (laplaceRay_integrable k hs (show 0 < 2 * (α + b) by linarith [(abs_lt.mp hb).1])).congr_fun
    hneg.symm measurableSet_Ioi
  have hi : IntegrableOn (fun x ↦ f (-x)) (Ici (-(0 : ℝ))) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (by simpa using ineg)
  have il : IntegrableOn f (Iic 0) := by simpa only [neg_neg, Function.comp_def] using hi.comp_neg_Iic
  change (∫ x, f x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi il ip, ← neg_zero (G := ℝ),
    ← integral_comp_neg_Ioi (0 : ℝ) f, neg_zero,
    setIntegral_congr_fun measurableSet_Ioi hpos, setIntegral_congr_fun measurableSet_Ioi hneg]
  change laplaceRay k s (2 * (α + b)) + laplaceRay k s (2 * (α - b)) = _
  rcases le_or_gt 0 b with h | h
  · rw [abs_of_nonneg h, add_comm]
  · rw [abs_of_neg h, sub_neg_eq_add, ← sub_eq_add_neg]

private theorem tendsto_laplace_damping_rates {ι : Type*} {l : Filter ι} {α : ℝ} {b : ι → ℝ}
    (hb : Tendsto (fun i ↦ |b i|) l (𝓝[<] α)) :
    Tendsto (fun i ↦ 2 * (α - |b i|)) l (𝓝[>] 0) ∧
      Tendsto (fun i ↦ 2 * (α + |b i|)) l (𝓝 (2 * (α + α))) := by
  obtain ⟨ht, hi⟩ := tendsto_nhdsWithin_iff.mp hb
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩, (tendsto_const_nhds.add ht).const_mul 2⟩
  · simpa only [sub_self, mul_zero] using ((tendsto_const_nhds (x := α)).sub ht).const_mul (2 : ℝ)
  · exact hi.mono fun i h ↦ mul_pos two_pos (sub_pos.mpr h)

/-- As the damping `2 * (α - |b|)` tends to zero inside the strip, the two-sided Laplace
integral has leading coefficient `Gamma (2k - s + 1)` for `2k - s > -1`. -/
theorem tendsto_scaled_polynomialWeight_laplace_gamma {ι : Type*} {l : Filter ι}
    {α : ℝ} (hα : 0 < α) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) (hp : -1 < ((2 * k : ℕ) - s : ℝ))
    {b : ι → ℝ} (hb : Tendsto (fun i ↦ |b i|) l (𝓝[<] α)) :
    Tendsto (fun i ↦ (2 * (α - |b i|)) ^ ((2 * k : ℕ) - s + 1 : ℝ) *
      ∫ x : ℝ, Real.exp (2 * b i * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) l
      (𝓝 (Real.Gamma ((2 * k : ℕ) - s + 1 : ℝ))) := by
  obtain ⟨hu, hv⟩ := tendsto_laplace_damping_rates hb
  have hpow := (tendsto_nhds_of_tendsto_nhdsWithin hu).rpow_const (p := ((2 * k : ℕ) - s + 1 : ℝ)) (Or.inr (by linarith))
  rw [Real.zero_rpow (by linarith : ((2 * k : ℕ) - s + 1 : ℝ) ≠ 0)] at hpow
  have hfar := hpow.mul ((laplaceRay_continuousAt k hs (show 0 < 2 * (α + α) by positivity)).tendsto.comp hv)
  have hboth := ((laplaceRay_scaled_tendsto k hs hp).comp hu).add hfar
  rw [zero_mul, add_zero] at hboth
  apply hboth.congr'
  filter_upwards [(tendsto_nhdsWithin_iff.mp hb).2] with i h
  dsimp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]
  rw [← mul_add, ← laplaceIntegral_eq_two_rays k hs h]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x ↦ by dsimp [polynomialWeight]; ring)

/-- At critical order and damping `exp (-t)`, the substitution `x = exp (t * y)` turns
the positive-ray integral divided by `t` into the integral of this kernel. -/
private def criticalKernel (s t y : ℝ) : ℝ :=
  Real.exp (-Real.exp (t * (y - 1))) * (1 + Real.exp (t * (-2 * y))) ^ (-(s / 2))

private theorem laplaceRay_critical_rescale (k : ℕ) {t : ℝ} (ht : 0 < t) :
    laplaceRay k ((2 * k : ℕ) + 1 : ℝ) (Real.exp (-t)) / t =
      ∫ y : ℝ, criticalKernel ((2 * k : ℕ) + 1 : ℝ) t y := by
  let s : ℝ := (2 * k : ℕ) + 1
  let g (x : ℝ) := Real.exp (-(Real.exp (-t) * x)) * polynomialWeight k s x
  have hsub := Measure.integral_comp_mul_left (fun u : ℝ ↦ Real.exp u • g (Real.exp u)) t
  rw [abs_of_pos (inv_pos.mpr ht), smul_eq_mul, integral_comp_exp] at hsub
  change (∫ x in Ioi (0 : ℝ), g x) / t = _
  rw [div_eq_inv_mul, ← hsub]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only [g, criticalKernel, smul_eq_mul]
  rw [polynomialWeight_posRay (Real.exp_pos _) k s, show ((2 * k : ℕ) - s : ℝ) = -1 by dsimp [s]; ring,
    Real.rpow_neg_one, ← Real.exp_add]
  have hex : Real.exp ((-t) + t * y) = Real.exp (t * (y - 1)) := by congr 1; ring
  have hinv : (1 / Real.exp (t * y)) ^ 2 = Real.exp (t * (-2 * y)) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hex, hinv]
  field_simp
  rfl

private theorem criticalKernel_bounds (s t y : ℝ) (hs : 0 ≤ s) :
    0 ≤ criticalKernel s t y ∧ criticalKernel s t y ≤ Real.exp (-Real.exp (t * (y - 1))) ∧
      criticalKernel s t y ≤ Real.exp (t * (s * y)) := by
  have hcut := Real.rpow_le_one_of_one_le_of_nonpos
    (show 1 ≤ 1 + Real.exp (t * (-2 * y)) by linarith [Real.exp_pos (t * (-2 * y))])
    (show -(s / 2) ≤ 0 by linarith)
  have hf := Real.exp_le_one_iff.mpr (show -Real.exp (t * (y - 1)) ≤ 0 by linarith [Real.exp_pos (t * (y - 1))])
  have he := Real.rpow_le_rpow_of_nonpos (Real.exp_pos (t * (-2 * y)))
    (le_add_of_nonneg_left (show 0 ≤ (1 : ℝ) by norm_num)) (show -(s / 2) ≤ 0 by linarith)
  rw [← Real.exp_mul] at he
  unfold criticalKernel
  refine ⟨by positivity, mul_le_of_le_one_right (Real.exp_nonneg _) hcut, ?_⟩
  apply (mul_le_of_le_one_left (by positivity) hf).trans
  convert he using 1
  ring_nf

/-- Off the two endpoints, the rescaled kernel converges to the indicator of `(0,1)`.
The common majorant `exp (1 - |y|)` gives the logarithmic coefficient. -/
private theorem laplaceRay_critical_log_tendsto (k : ℕ) :
    Tendsto (fun u : ℝ ↦ laplaceRay k ((2 * k : ℕ) + 1 : ℝ) u / (-Real.log u)) (𝓝[>] 0) (𝓝 1) := by
  let s : ℝ := (2 * k : ℕ) + 1
  have hs : 1 ≤ s := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hs0 : 0 ≤ s := by linarith
  let g := (Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))
  have hi : ∫ y : ℝ, g y = 1 := by
    rw [show g = _ from rfl, integral_indicator measurableSet_Ioo, setIntegral_const,
      Measure.real, Real.volume_Ioo]
    norm_num
  have hdom : Integrable (fun y : ℝ ↦ Real.exp (1 - |y|)) := by
    simpa only [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, one_mul] using
      (integrable_exp_neg_mul_abs (c := 1) zero_lt_one).const_mul (Real.exp 1)
  have hlim : Tendsto (fun t ↦ ∫ y : ℝ, criticalKernel s t y) atTop (𝓝 (∫ y : ℝ, g y)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y ↦ Real.exp (1 - |y|))
    · exact Eventually.of_forall (fun t ↦ (show Measurable (criticalKernel s t) by
        unfold criticalKernel
        fun_prop).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      refine ae_of_all _ fun y ↦ ?_
      obtain ⟨h0, h1, h2⟩ := criticalKernel_bounds s t y hs0
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      rcases le_or_gt y 0 with hy | hy
      · apply h2.trans (Real.exp_le_exp.mpr ?_)
        rw [abs_of_nonpos hy]
        have hprod : 1 ≤ t * s := one_le_mul_of_one_le_of_one_le ht hs
        nlinarith [mul_le_mul_of_nonpos_right hprod hy]
      · apply h1.trans (Real.exp_le_exp.mpr ?_)
        rw [abs_of_pos hy]
        by_cases h : 1 ≤ y
        · have hmul := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr h)
          linarith [Real.add_one_le_exp (t * (y - 1))]
        · linarith [Real.exp_pos (t * (y - 1))]
    · exact hdom
    · filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ)] with y hy0 hy1
      rcases lt_or_gt_of_ne hy0 with hy | hy
      · rw [show g y = 0 by apply indicator_of_notMem; simp [not_lt_of_ge hy.le]]
        apply squeeze_zero (fun t ↦ (criticalKernel_bounds s t y hs0).1) (fun t ↦ (criticalKernel_bounds s t y hs0).2.2)
        exact Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (mul_neg_of_pos_of_neg (by linarith) hy))
      rcases lt_or_gt_of_ne hy1 with hy' | hy'
      · have hf := Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.mpr hy'))
        have hc := Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (show -2 * y < 0 by linarith))
        have hleft := Real.continuous_exp.continuousAt.tendsto.comp hf.neg
        have hright := ((tendsto_const_nhds (x := (1 : ℝ))).add hc).rpow_const (p := -(s / 2)) (.inl (by norm_num))
        rw [show g y = 1 from indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from ⟨hy, hy'⟩) (fun _ ↦ (1 : ℝ))]
        simpa [criticalKernel, Function.comp_def] using hleft.mul hright
      · rw [show g y = 0 by apply indicator_of_notMem; simp [not_lt_of_ge hy'.le]]
        apply squeeze_zero (fun t ↦ (criticalKernel_bounds s t y hs0).1) (fun t ↦ (criticalKernel_bounds s t y hs0).2.1)
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_exp_atTop.comp
          (tendsto_id.atTop_mul_const (sub_pos.mpr hy')))
  rw [hi] at hlim
  have hlog := tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply (hlim.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu hu1
  have hu' : 0 < u := hu
  have hn : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu' hu1.2)
  rw [Function.comp_apply]
  change (∫ y : ℝ, criticalKernel s (-Real.log u) y) = _
  rw [← laplaceRay_critical_rescale k hn, neg_neg, Real.exp_log hu']

/-- At the critical exponent `s = 2k + 1`, the two-sided Laplace integral divided by
the logarithm of the inverse scaled distance to the edge tends to one. -/
theorem tendsto_polynomialWeight_laplace_div_log {ι : Type*} {l : Filter ι}
    {α : ℝ} (hα : 0 < α) (k : ℕ) {b : ι → ℝ}
    (hb : Tendsto (fun i ↦ |b i|) l (𝓝[<] α)) :
    Tendsto (fun i ↦
      (∫ x : ℝ, Real.exp (2 * b i * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (((2 * k : ℕ) + 1 : ℝ) / 2))⁻¹) /
      (-Real.log (2 * (α - |b i|)))) l (𝓝 1) := by
  let s : ℝ := (2 * k : ℕ) + 1
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨hu, hv⟩ := tendsto_laplace_damping_rates hb
  have hfar := ((laplaceRay_continuousAt k hs (show 0 < 2 * (α + α) by positivity)).tendsto.comp hv).mul
    (tendsto_inv_atTop_zero.comp (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hu)))
  have htogether := ((laplaceRay_critical_log_tendsto k).comp hu).add hfar
  rw [mul_zero, add_zero] at htogether
  apply htogether.congr'
  filter_upwards [(tendsto_nhdsWithin_iff.mp hb).2] with i h
  dsimp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]
  change laplaceRay k s (2 * (α - |b i|)) / _ + laplaceRay k s (2 * (α + |b i|)) * (-Real.log _)⁻¹ = _
  rw [← div_eq_mul_inv, ← add_div, ← laplaceIntegral_eq_two_rays k hs h]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x ↦ by dsimp [polynomialWeight, s]; ring)

private theorem integrable_polynomialWeight (k : ℕ) {s : ℝ} (hs : 2 * (k : ℝ) + 1 < s) :
    Integrable (polynomialWeight k s) := by
  have hd : (Module.finrank ℝ ℝ : ℝ) < s - 2 * (k : ℝ) := by simpa using (by linarith : 1 < s - 2 * (k : ℝ))
  have hm : Measurable (polynomialWeight k s) := by unfold polynomialWeight; fun_prop
  apply (integrable_rpow_neg_one_add_norm_sq (μ := volume) hd).mono' hm.aestronglyMeasurable
  refine ae_of_all _ fun x ↦ ?_
  rw [Real.norm_of_nonneg (polynomialWeight_nonneg k s x), Real.norm_eq_abs, sq_abs]
  have hp : 0 < 1 + x ^ 2 := by positivity
  calc
    polynomialWeight k s x ≤ (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
      dsimp only [polynomialWeight]
      rw [pow_mul]
      gcongr
      linarith
    _ = _ := by
      rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hp.le, ← Real.rpow_add hp]
      congr 1
      ring

/-- If `s > 2k + 1`, the exponentially damped polynomial weight is integrable throughout
the closed strip, including both edges. -/
theorem integrable_polynomialWeight_laplace (k : ℕ) {s α b : ℝ}
    (hs : 2 * (k : ℝ) + 1 < s) (hb : |b| ≤ α) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) := by
  have hm : Measurable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) := by fun_prop
  apply (integrable_polynomialWeight k hs).mono' hm.aestronglyMeasurable
  refine ae_of_all _ fun x ↦ ?_
  have hx := (le_abs_self (b * x)).trans ((abs_mul b x).le.trans
    (mul_le_mul_of_nonneg_right hb (abs_nonneg x)))
  have he := Real.exp_le_one_iff.mpr (show 2 * b * x - 2 * α * |x| ≤ 0 by linarith)
  rw [mul_assoc]
  change ‖_ * polynomialWeight k s x‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (polynomialWeight_nonneg ..))]
  exact mul_le_of_le_one_left (polynomialWeight_nonneg ..) he

/-- Above the integrability threshold, approaching either edge yields the finite endpoint value. -/
theorem tendsto_polynomialWeight_laplace_endpoint {ι : Type*} {l : Filter ι}
    {α : ℝ} (k : ℕ) {s : ℝ} (hs : 2 * (k : ℝ) + 1 < s)
    {b : ι → ℝ} (hb : Tendsto (fun i ↦ |b i|) l (𝓝[<] α)) :
    Tendsto (fun i ↦ ∫ x : ℝ, Real.exp (2 * b i * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) l
      (𝓝 (∫ x : ℝ, Real.exp (2 * α * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)) := by
  let w (x : ℝ) := x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  let f (a x : ℝ) := Real.exp (2 * a * x - 2 * α * |x|) * w x
  have heq (a : ℝ) : (∫ x, f |a| x) = ∫ x, f a x := by
    rcases le_or_gt 0 a with ha | ha
    · rw [abs_of_nonneg ha]
    rw [abs_of_neg ha, ← integral_neg_eq_self (fun x ↦ f a x)]
    apply integral_congr_ae
    refine ae_of_all _ fun x ↦ ?_
    simp [f, w, pow_mul]
  have hw (x : ℝ) : 0 ≤ w x := polynomialWeight_nonneg k s x
  have hW : Integrable w := integrable_polynomialWeight k hs
  obtain ⟨ht, hi⟩ := tendsto_nhdsWithin_iff.mp hb
  have habs : Tendsto (fun i ↦ |b i|) l (𝓝[Icc 0 α] α) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, hi.mono (fun i h ↦ ⟨abs_nonneg _, le_of_lt h⟩)⟩
  have hendpoint : Tendsto (fun a ↦ ∫ x, f a x) (𝓝[Icc 0 α] α) (𝓝 (∫ x, f α x)) := by
    apply tendsto_integral_filter_of_dominated_convergence w
    · exact Eventually.of_forall fun a ↦ (show Measurable (f a) by
        dsimp [f, w]
        fun_prop).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with a ha
      change a ∈ Icc 0 α at ha
      refine ae_of_all _ fun x ↦ ?_
      have hle : a * x ≤ α * |x| := (mul_le_mul_of_nonneg_left (le_abs_self x)
        ha.1).trans (mul_le_mul_of_nonneg_right ha.2 (abs_nonneg _))
      have hexp := Real.exp_le_one_iff.mpr (show 2 * a * x - 2 * α * |x| ≤ 0 by linarith)
      dsimp only [f]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hw _))]
      exact mul_le_of_le_one_left (hw _) hexp
    · exact hW
    · refine ae_of_all _ fun x ↦ ?_
      have hc : Continuous (fun a : ℝ ↦ Real.exp (2 * a * x - 2 * α * |x|) * w x) := by fun_prop
      exact hc.continuousAt.continuousWithinAt
  have hlim := hendpoint.comp habs
  simp only [Function.comp_def, heq] at hlim
  simpa only [f, w, mul_assoc] using hlim

end RiemannMasullo
