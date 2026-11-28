module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # The sign of the Riemann zeta function on the real interval `(0, 1)` -/

open Filter MeasureTheory Set
open scoped Asymptotics Topology

public noncomputable section

namespace RiemannMasullo

private def zetaFract (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))

private theorem integrableOn_zetaFract {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h := integrableOn_Ioi_cpow_of_lt
    (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith :
      (-(s + 1)).re < -1) (show (0 : ℝ) < 1 by norm_num)
  refine Integrable.mono h ((measurable_id.fract.complex_ofReal).mul
    (measurable_id.complex_ofReal.pow_const _)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le

private theorem differentiableAt_zetaFract {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaFract s := by
  let A : ℝ → ℂ := (Ioi 1).indicator (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ))
  have hbd (x : ℝ) : ‖A x‖ ≤ 1 := by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simpa [A, hx, abs_of_nonneg (Int.fract_nonneg x)] using (Int.fract_lt_one x).le
    · simp [A, hx]
  have hmeas : Measurable A := (measurable_id.fract.complex_ofReal).indicator measurableSet_Ioi
  have hloc : LocallyIntegrableOn A (Ioi 0) :=
    (locallyIntegrableOn_const (1 : ℝ)).mono hmeas.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (hbd x).trans (Real.le_norm_self _))
  have htop : A =O[atTop] (fun x : ℝ ↦ x ^ (-(0 : ℝ))) :=
    Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun x ↦ by simpa using hbd x⟩
  have hbot (b : ℝ) : A =O[𝓝[>] 0] (fun x : ℝ ↦ x ^ (-b)) := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with x hx
    simp [A, not_lt.mpr hx.le]
  have hM := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) (hbot ((-s).re - 1)) (by linarith)
  have hI (z : ℂ) : mellin A (-z) = zetaFract z := by
    have he (x : ℝ) : (x : ℂ) ^ (-z - 1) • A x =
        (Ioi 1).indicator (fun y : ℝ ↦ ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-(z + 1))) x := by
      by_cases hx : x ∈ Ioi (1 : ℝ)
      · simp only [A, indicator_of_mem hx, smul_eq_mul]
        rw [show -z - 1 = -(z + 1) by ring, mul_comm]
      · simp [A, hx]
    simp only [zetaFract, mellin, he, integral_indicator measurableSet_Ioi]
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  have hM' : DifferentiableAt ℂ (fun z : ℂ ↦ mellin A (-z)) s :=
    hM.comp s differentiableAt_id.neg
  simpa only [hI] using hM'

private theorem riemannZeta_eq_sub_zetaFract_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * zetaFract s := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine (Asymptotics.isBigO_refl _ _).congr_left fun n ↦ ?_
    simp
  have hL := LSeries_eq_mul_integral_of_nonneg (fun _ : ℕ ↦ (1 : ℝ)) zero_le_one hs hO
    (fun _ ↦ zero_le_one)
  have hx (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((1 : ℝ) : ℂ)) * (x : ℂ) ^ (-(s + 1)) =
        (x : ℂ) ^ (-s) - ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
    have hxp : 0 < x := zero_lt_one.trans hx
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
      rw [show -s = 1 + (-(s + 1)) by ring,
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hxp.ne'), Complex.cpow_one]
    simp only [Complex.ofReal_one, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
      Nat.add_sub_cancel]
    have hfloor : (⌊x⌋₊ : ℂ) = (⌊x⌋ : ℂ) := by
      exact_mod_cast Int.natCast_floor_eq_floor hxp.le
    rw [hfloor, hpow]
    simp only [Int.fract]
    push_cast
    ring
  rw [← LSeries_one_eq_riemannZeta hs]
  change LSeries (fun _ : ℕ ↦ ((1 : ℝ) : ℂ)) s = _
  rw [hL, setIntegral_congr_fun measurableSet_Ioi hx,
    integral_sub (integrableOn_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs)) zero_lt_one)
      (integrableOn_zetaFract (zero_lt_one.trans hs)),
    integral_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs)) zero_lt_one]
  simp only [Complex.ofReal_one, Complex.one_cpow, zetaFract, mul_sub]
  congr 1
  rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg, mul_one_div]

private theorem riemannZeta_eq_sub_zetaFract {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    riemannZeta s = s / (s - 1) - s * zetaFract s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}
  let V : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}
  let Z (z : ℂ) := z / (z - 1) - z * zetaFract z
  have hU : IsPreconnected U := ((convex_halfSpace_re_gt 0).inter
    (convex_halfSpace_im_gt 0)).isPreconnected
  have hV : IsPreconnected V := ((convex_halfSpace_re_gt 0).inter
    (convex_halfSpace_re_lt 1)).isPreconnected
  have hUV : IsPreconnected (U ∪ V) :=
    IsPreconnected.union (⟨1 / 2, 1⟩ : ℂ)
      (by norm_num [U]) (by norm_num [V]) hU hV
  have hopen : IsOpen (U ∪ V) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)).union
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const))
  have hpos {z : ℂ} (hz : z ∈ U ∪ V) : 0 < z.re := hz.elim And.left And.left
  have hne {z : ℂ} (hz : z ∈ U ∪ V) : z ≠ 1 := by
    intro he
    subst z
    simp [U, V] at hz
  have hZa : AnalyticOnNhd ℂ Z (U ∪ V) := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have hId : DifferentiableAt ℂ (fun w : ℂ ↦ w) z := differentiableAt_id
    have hSub : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1) z := hId.sub_const 1
    have hDiv : DifferentiableAt ℂ (fun w : ℂ ↦ w / (w - 1)) z :=
      hId.div hSub (sub_ne_zero.mpr (hne hz))
    exact (hDiv.sub
      (hId.fun_mul (differentiableAt_zetaFract (hpos hz)))).differentiableWithinAt
  have hζa : AnalyticOnNhd ℂ riemannZeta (U ∪ V) :=
    fun z hz ↦ analyticOn_riemannZeta z (hne hz)
  have hEq : riemannZeta =ᶠ[𝓝 (⟨2, 1⟩ : ℂ)] Z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (⟨2, 1⟩ : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact riemannZeta_eq_sub_zetaFract_of_one_lt_re hz
  exact (hζa.eqOn_of_preconnected_of_eventuallyEq hZa hUV
    (Or.inl (by norm_num [U])) hEq) (Or.inr ⟨hs, hs'⟩)

/-- The real part of the Riemann zeta function is strictly negative on `(0, 1)`. -/
theorem riemannZeta_re_ofReal_neg {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  have hnonneg : 0 ≤ (zetaFract (x : ℂ)).re := by
    change 0 ≤ RCLike.re (zetaFract (x : ℂ))
    rw [zetaFract, ← integral_re (integrableOn_zetaFract (s := (x : ℂ)) (by simpa using hx))]
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    change 0 ≤ (((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-((x : ℂ) + 1))).re
    rw [show -((x : ℂ) + 1) = ((-(x + 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (zero_lt_one.trans (show 1 < t from ht)).le,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (Int.fract_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  rw [riemannZeta_eq_sub_zetaFract (by simpa using hx) (by simpa using hx'), Complex.sub_re,
    show (x : ℂ) / ((x : ℂ) - 1) = ((x / (x - 1) : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact sub_neg.mpr ((div_neg_of_pos_of_neg hx (sub_neg.mpr hx')).trans_le
    (mul_nonneg hx.le hnonneg))

end RiemannMasullo
