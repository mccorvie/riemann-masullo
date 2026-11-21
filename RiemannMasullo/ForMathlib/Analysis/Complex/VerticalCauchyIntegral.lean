module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Cauchy integrals on vertical lines

The two vertical sides of a strip recover the value of a holomorphic function with uniform
decay at large heights. The elementary pole contributes opposite principal values on the
two lines. Higher Cauchy kernels arise by differentiation in the evaluation point.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped Interval
namespace RiemannMasullo

local notation "verticalPoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)

/-- The symmetric truncations of the elementary Cauchy kernel on a vertical line. -/
private theorem tendsto_symmetric_cauchy_inv {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun T : ℝ ↦ ∫ y in -T..T, (verticalPoint d y)⁻¹) atTop
      (𝓝 ((d⁻¹ * (Real.pi / |d⁻¹|) : ℝ) : ℂ)) := by
  let G (y : ℝ) := (verticalPoint d y)⁻¹
  let H (y : ℝ) := d⁻¹ * (1 + (d⁻¹ * y) ^ 2)⁻¹
  have hG : Continuous G := by
    apply Continuous.inv₀ (by dsimp only; fun_prop)
    intro y h
    exact hd (by simpa using congrArg Complex.re h)
  have hH : Integrable H := (integrable_inv_one_add_mul_sq (inv_ne_zero hd)).const_mul _
  have pair (y : ℝ) : G y + G (-y) = 2 * (H y : ℂ) := by
    have hpos : 0 < d * d + y * y := by nlinarith [sq_pos_of_ne_zero hd, sq_nonneg y]
    rw [← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.inv_re, Complex.normSq_apply, Complex.add_im,
        Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, neg_zero,
        zero_add, add_zero, neg_mul_neg, G]
      dsimp only [H]
      field_simp [hd]
      ring
    · simp [G, Complex.inv_im, Complex.normSq_apply, neg_div]
  have eq (T : ℝ) : (∫ y in -T..T, G y) = ↑(∫ y in -T..T, H y) := by
    have reflected : (∫ y in -T..T, G (-y)) = ∫ y in -T..T, G y := by
      simp only [intervalIntegral.integral_comp_neg, neg_neg]
    have hadd := intervalIntegral.integral_add (μ := volume)
      (hG.intervalIntegrable (-T) T) ((hG.comp continuous_neg).intervalIntegrable (-T) T)
    simp_rw [Function.comp_apply, pair] at hadd
    rw [reflected, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal] at hadd
    linear_combination -hadd / 2
  have lim := intervalIntegral_tendsto_integral hH tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
  have val : (∫ y, H y) = d⁻¹ * (Real.pi / |d⁻¹|) := by
    simp only [H, integral_const_mul, integral_univ_inv_one_add_mul_sq]
  rw [← val]
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp lim).congr fun T ↦ (eq T).symm

/-- Removing the pole subtracts its explicit principal value on each vertical side. -/
private theorem tendsto_dslope_vertical {Φ : ℂ → ℂ} {z : ℂ} {σ : ℝ} (hz : σ ≠ z.re)
    (hi : Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) σ) :
    Tendsto (fun T : ℝ ↦ ∫ y in -T + z.im..T + z.im, dslope Φ z (verticalPoint σ y)) atTop
      (𝓝 ((∫ y : ℝ, Φ (verticalPoint σ y) / (verticalPoint σ y - z)) -
        Φ z * (if z.re < σ then (Real.pi : ℂ) else -(Real.pi : ℂ)))) := by
  let d := σ - z.re
  have hd : d ≠ 0 := sub_ne_zero.mpr hz
  have hne (y : ℝ) : verticalPoint σ y ≠ z := fun h ↦ hz (by simpa using congrArg Complex.re h)
  have hcont : Continuous (fun y : ℝ ↦ (verticalPoint σ y - z)⁻¹) := by
    exact Continuous.inv₀ (by fun_prop) fun y ↦ sub_ne_zero.mpr (hne y)
  have tr (T : ℝ) : (∫ y in -T + z.im..T + z.im, (verticalPoint σ y - z)⁻¹) =
      ∫ y in -T..T, (verticalPoint d y)⁻¹ := by
    rw [← intervalIntegral.integral_comp_add_right (fun y : ℝ ↦ (verticalPoint σ y - z)⁻¹) z.im]
    apply intervalIntegral.integral_congr
    intro y _
    apply congrArg Inv.inv
    apply Complex.ext <;> simp [d]
  have hval : ((d⁻¹ * (Real.pi / |d⁻¹|) : ℝ) : ℂ) =
      (if z.re < σ then (Real.pi : ℂ) else -(Real.pi : ℂ)) := by
    split_ifs with h
    · have hdpos : 0 < d := sub_pos.mpr h
      rw [abs_of_pos (inv_pos.mpr hdpos)]
      apply congrArg Complex.ofReal
      field_simp [hd]
    · have hdneg : d < 0 := sub_neg.mpr (lt_of_le_of_ne (le_of_not_gt h) hz)
      rw [abs_of_neg (inv_lt_zero.mpr hdneg), ← Complex.ofReal_neg]
      apply congrArg Complex.ofReal
      field_simp [hd]
  have lim := tendsto_symmetric_cauchy_inv hd
  rw [hval] at lim
  have ht : Tendsto (fun T : ℝ ↦ T + z.im) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hb : Tendsto (fun T : ℝ ↦ -T + z.im) atTop atBot :=
    tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
  have hK := intervalIntegral_tendsto_integral hi hb ht
  apply (hK.sub (lim.const_mul (Φ z))).congr
  intro T
  rw [← tr, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [dslope_of_ne _ (hne y), slope_def_field, sub_div, div_eq_mul_inv (Φ z)]
  · exact hi.intervalIntegrable
  · exact (continuous_const.mul hcont).intervalIntegrable _ _

/-- Uniform decay on the strip makes the two horizontal sides of the divided difference vanish. -/
private theorem tendsto_horizontal_dslope {Φ : ℂ → ℂ} {z : ℂ} {c d C : ℝ} (hcd : c ≤ d) (hC : 0 ≤ C)
    (hΦ : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y|) :
    Tendsto (fun y : ℝ ↦ ∫ x in c..d, dslope Φ z (verticalPoint x y)) (comap abs atTop) (𝓝 0) := by
  have hy : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
  apply squeeze_zero_norm'
  · filter_upwards [hΦ, hy.eventually (eventually_ge_atTop (2 * |z.im| + 1))] with y hφ hlarge
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hpos : 0 < |y| / 2 := by linarith [abs_nonneg z.im]
    have im := Complex.abs_im_le_norm (verticalPoint x y - z)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add] at im
    have hsep : |y| / 2 ≤ ‖verticalPoint x y - z‖ := by linarith [abs_sub_abs_le_abs_sub y z.im]
    have hne := sub_ne_zero.mp (norm_pos_iff.mp (hpos.trans_le hsep))
    have hnum := (hφ x (Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hx))).trans
      (div_le_self hC (by linarith [abs_nonneg z.im]))
    rw [dslope_of_ne _ hne, slope_def_field, norm_div]
    calc ‖Φ (verticalPoint x y) - Φ z‖ / ‖verticalPoint x y - z‖
      _ ≤ (C + ‖Φ z‖) / (|y| / 2) := div_le_div₀ (by positivity)
        ((norm_sub_le _ _).trans (add_le_add hnum le_rfl)) hpos hsep
      _ = (2 * (C + ‖Φ z‖)) / |y| := by ring
  · simpa using ((tendsto_const_nhds (x := 2 * (C + ‖Φ z‖))).div_atTop hy).mul_const |d - c|

/-- The residue of the simple Cauchy kernel between two vertical sides. -/
theorem verticalCauchyIntegral_sub_eq {Φ : ℂ → ℂ} {z : ℂ} {a b c d C : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (Complex.re ⁻¹' Ioo a b)) (ha : a < c) (hb : d < b)
    (hz : z.re ∈ Ioo c d) (hC : 0 ≤ C)
    (hΦdecay : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y|)
    (hc : Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) c)
    (hd : Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) d) :
    (∫ y : ℝ, Φ (verticalPoint d y) / (verticalPoint d y - z)) - (∫ y : ℝ, Φ (verticalPoint c y) / (verticalPoint c y - z)) =
      2 * (Real.pi : ℂ) * Φ z := by
  have hcd := (hz.1.trans hz.2).le
  have hzmem : Complex.re ⁻¹' Ioo a b ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨ha.trans hz.1, hz.2.trans hb⟩
  have hD := (Complex.differentiableOn_dslope hzmem).mpr hΦ
  let bot (t : ℝ) := -t + z.im
  let top (t : ℝ) := t + z.im
  have hrect (t : ℝ) :
      (∫ x in c..d, dslope Φ z (verticalPoint x (bot t))) - (∫ x in c..d, dslope Φ z (verticalPoint x (top t))) +
      Complex.I • (∫ y in bot t..top t, dslope Φ z (verticalPoint d y)) -
      Complex.I • (∫ y in bot t..top t, dslope Φ z (verticalPoint c y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ (⟨c, bot t⟩ : ℂ) (⟨d, top t⟩ : ℂ)
    apply hD.mono
    intro w hw
    exact Icc_subset_Ioo ha hb ((uIcc_of_le hcd) ▸ hw.1)
  have ht : Tendsto top atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hn : Tendsto bot atTop atBot := tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
  have horiz := tendsto_horizontal_dslope (z := z) hcd hC hΦdecay
  have ht' := horiz.comp (tendsto_comap_iff.mpr (tendsto_abs_atTop_atTop.comp ht))
  have hn' := horiz.comp (tendsto_comap_iff.mpr (tendsto_abs_atBot_atTop.comp hn))
  have vd := tendsto_dslope_vertical hz.2.ne' hd
  have vc := tendsto_dslope_vertical hz.1.ne hc
  rw [ite_eq_left hz.2] at vd
  rw [ite_eq_right (not_lt.mpr hz.1.le)] at vc
  have hlim := (((hn'.sub ht').add (vd.const_smul Complex.I)).sub (vc.const_smul Complex.I))
  have eq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (hrect t).symm)
  simp only [sub_zero, zero_add, smul_eq_mul] at eq
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination eq

/-- Differentiating the Cauchy integral in the pole raises the denominator power by one. -/
theorem hasDerivAt_verticalCauchyIntegral {Φ : ℂ → ℂ} {z : ℂ} {σ : ℝ} (hz : z.re ≠ σ)
    (hΦ : Complex.VerticalIntegrable Φ σ) (n : ℕ)
    (hK : Complex.VerticalIntegrable (fun s ↦ Φ s / (s - z) ^ (n + 1)) σ) :
    HasDerivAt (fun w ↦ ∫ y : ℝ, Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ (n + 1))
      ((n + 1 : ℂ) * ∫ y : ℝ, Φ (verticalPoint σ y) / (verticalPoint σ y - z) ^ (n + 2)) z := by
  let δ := |σ - z.re| / 2
  have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hz.symm))
  let U := {w : ℂ | δ < |σ - w.re|}
  have hU : U ∈ 𝓝 z := (isOpen_lt continuous_const (continuous_const.sub Complex.continuous_re).abs).mem_nhds
    (show δ < |σ - z.re| by dsimp [δ]; linarith [abs_pos.mpr (sub_ne_zero.mpr hz.symm)])
  have hsep {w : ℂ} (hw : w ∈ U) (y : ℝ) : δ ≤ ‖verticalPoint σ y - w‖ :=
    le_trans (le_of_lt (show δ < |σ - w.re| from hw)) (by simpa using Complex.abs_re_le_norm (verticalPoint σ y - w))
  let K (m : ℕ) (w : ℂ) (y : ℝ) := Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ m
  have hmeas : AEStronglyMeasurable (fun y : ℝ ↦ Φ (verticalPoint σ y)) volume := hΦ.aestronglyMeasurable
  have hm (m : ℕ) (w : ℂ) : AEStronglyMeasurable (K m w) volume := by
    have hc : Continuous (fun y : ℝ ↦ (verticalPoint σ y - w) ^ m) := by fun_prop
    change AEStronglyMeasurable (fun y : ℝ ↦ Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ m) volume
    exact (hmeas.aemeasurable.div hc.measurable.aemeasurable).aestronglyMeasurable
  let A := ‖(n + 1 : ℂ)‖ / δ ^ (n + 2)
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := K (n + 1))
    (F' := fun w y ↦ (n + 1 : ℂ) * K (n + 2) w y)
    (bound := fun y ↦ A * ‖Φ (verticalPoint σ y)‖) hU (Eventually.of_forall (hm _)) hK
    ((hm _ _).const_mul _) ?_ (hΦ.norm.const_mul _) ?_).2
  · filter_upwards with y w hw
    change ‖(n + 1 : ℂ) * (Φ (verticalPoint σ y) / (verticalPoint σ y - w) ^ (n + 2))‖ ≤ _
    rw [norm_mul, norm_div, norm_pow]
    calc ‖(n + 1 : ℂ)‖ * (‖Φ (verticalPoint σ y)‖ / ‖verticalPoint σ y - w‖ ^ (n + 2))
      _ ≤ ‖(n + 1 : ℂ)‖ * (‖Φ (verticalPoint σ y)‖ / δ ^ (n + 2)) := by
        gcongr
        exact hsep hw y
      _ = A * ‖Φ (verticalPoint σ y)‖ := by dsimp [A]; ring
  · filter_upwards with y w hw
    have hne := norm_pos_iff.mp (hδ.trans_le (hsep hw y))
    have hder := (hasDerivAt_const w (Φ (verticalPoint σ y))).div
      (((hasDerivAt_id w).const_sub (verticalPoint σ y)).pow (n + 1)) (pow_ne_zero _ hne)
    convert hder using 1
    · funext x
      rfl
    · dsimp [K]
      push_cast
      field_simp [hne]
      ring

end RiemannMasullo
