module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWBandDensity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # The closure of the polar-free core of the weighted real band, for widths below five halves

Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519, for the
real place of `ℚ` with the weight of (9.2.1.30).

The polar-free core consists of the band vectors given by even Schwartz functions with Fourier
transform supported in `[-Y, Y]`, value zero at the origin and integral zero. For `s ≥ 0` and
`0 ≤ α < 5 / 2` its closure in the weighted even band is determined in every case.

* `α < 1 / 2`: the band vectors that vanish at the origin
  (`closure_realPWBandPolarFreeCore_eq`, in `Sec4_RealPWBandDensity`).
* `α = 1 / 2` and `s ≤ 1`: the whole band (`dense_realPWBandPolarFreeCore_half`).
* `α = 1 / 2` and `s > 1`, or `1 / 2 < α < 5 / 2`: the band vectors of integral zero
  (`closure_realPWBandPolarFreeCore_half_eq_integral`,
  `closure_realPWBandPolarFreeCore_eq_integral`).

Beyond what `Sec4_RealPWPolarThreshold` and `Sec4_RealPWBandDensity` prove, two facts are
needed.

For `α ≥ 1 / 2` every band vector vanishes at the origin (`realPWBand_evaluation_zero`), since
the weight is at least `1 / |x|` there and that is not integrable. So from width one half on
the condition at the origin is automatic.

For `1 / 2 ≤ α < 5 / 2` the Schwartz functions of the band are still dense
(`exists_schwartz_realPWBand_norm_sub_lt_of_half_le`). The proof is that of
`Sec4_RealPWBandDensity`. Near the origin the constant bound of that file is replaced by
`C x ^ 2`, which holds because a band vector is even, smooth and zero at the origin, and
`x ^ 4` times the weight is integrable there for `α < 5 / 2`.

Reconstruction: The paper does not state this. The core is that of the order-zero model of the
rational real place.

Not treated here: `α ≥ 5 / 2`, where band vectors vanish to higher order at the origin and
further moments become continuous. -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace RiemannMasullo.Isolated

variable {Y α s : ℝ}

/-- For width at least one half the weight is at least `1 / x` on `(0, 1]`. -/
private theorem inv_le_realPWIntervalWeight (hα : 1 / 2 ≤ α) (hs : 0 ≤ s) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) : x⁻¹ ≤ realPWIntervalWeight α s x := by
  rw [realPWIntervalWeight_eq α s hx0.ne', abs_of_pos hx0]
  have h1 : x⁻¹ ≤ x ^ (-(2 * α)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have h2 : (1 : ℝ) ≤ (1 + Real.log x ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg (Real.log x)]) (div_nonneg hs zero_le_two)
  have h3 : x⁻¹ ≤ max (x ^ (2 * α)) (x ^ (-(2 * α))) := h1.trans (le_max_right _ _)
  calc x⁻¹ = x⁻¹ * 1 := (mul_one _).symm
    _ ≤ max (x ^ (2 * α)) (x ^ (-(2 * α))) * (1 + Real.log x ^ 2) ^ (s / 2) :=
        mul_le_mul h3 h2 zero_le_one ((inv_nonneg.mpr hx0.le).trans h3)

/-- Reconstruction: for width at least one half every vector of the weighted even band vanishes
at the origin. The weight is at least `1 / |x|` near the origin, which is not integrable, so a
continuous function that is square integrable for the weight cannot be nonzero there. -/
theorem realPWBand_evaluation_zero (hα : 1 / 2 ≤ α) (hs : 0 ≤ s)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0 := by
  have hμ := volume_le_realPWIntervalMeasure α s hs
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  let u : ℝ → ℂ := fun x ↦ RealPWBand.evaluation Y hμ x f
  have huc : Continuous u := (RealPWBand.contDiff_evaluation Y hμ f 0).continuous
  have hum : MemLp u 2 (realPWIntervalMeasure α s) :=
    (Lp.memLp (f.val : Lp ℂ 2 (realPWIntervalMeasure α s))).ae_eq
      (RealPWBand.evaluation_ae Y hμ hμac f).symm
  have hUi : Integrable (fun x ↦ ‖u x‖ ^ 2) (realPWIntervalMeasure α s) :=
    (memLp_two_iff_integrable_sq_norm huc.aestronglyMeasurable).mp hum
  by_contra hne
  have hc : 0 < ‖u 0‖ := norm_pos_iff.mpr hne
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousAt_iff.mp huc.continuousAt (‖u 0‖ / 2) (half_pos hc)
  let d : ℝ := min δ 1 / 2
  have hm : 0 < min δ 1 := lt_min hδ one_pos
  have hd0 : 0 < d := half_pos hm
  have hdδ : d < δ := (half_lt_self hm).trans_le (min_le_left _ _)
  have hd1 : d ≤ 1 := (half_lt_self hm).le.trans (min_le_right _ _)
  have hw : IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * realPWIntervalWeight α s x) (Ioc 0 d) :=
    (integrableOn_realPWIntervalMeasure_iff hs _ measurableSet_Ioc).mp hUi.integrableOn
  have hc2 : 0 < (‖u 0‖ / 2) ^ 2 := pow_pos (half_pos hc) 2
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioc 0 d) := by
    refine (hw.const_mul ((‖u 0‖ / 2) ^ 2)⁻¹).mono' measurable_inv.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ ?_
    have hx0 : 0 < x := hx.1
    have hux : ‖u 0‖ / 2 ≤ ‖u x‖ := by
      have h := hδu (x := x) (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
        exact lt_of_le_of_lt hx.2 hdδ)
      rw [dist_eq_norm] at h
      have h2 := norm_sub_norm_le (u 0) (u x)
      rw [norm_sub_rev] at h2
      linarith
    have hwx := inv_le_realPWIntervalWeight hα hs hx0 (hx.2.trans hd1)
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hx0.le), ← div_eq_inv_mul, le_div_iff₀ hc2]
    calc x⁻¹ * (‖u 0‖ / 2) ^ 2 ≤ realPWIntervalWeight α s x * ‖u x‖ ^ 2 :=
          mul_le_mul hwx (pow_le_pow_left₀ (half_pos hc).le hux 2) hc2.le
            (zero_le_one.trans (one_le_realPWIntervalWeight α s hs x))
      _ = ‖u x‖ ^ 2 * realPWIntervalWeight α s x := mul_comm _ _
  have hI : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 0 d :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hd0.le).mpr hinv
  rcases intervalIntegrable_inv_iff.mp hI with h | h
  · exact hd0.ne h
  · exact h left_mem_uIcc

/-- An even twice continuously differentiable function that vanishes at the origin is bounded
on every bounded interval by a multiple of `y ^ 2`. -/
private theorem exists_norm_le_mul_sq_of_even {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u)
    (he : ∀ x, u (-x) = u x) (h0 : u 0 = 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Icc (-R) R, ‖u y‖ ≤ C * |y| ^ (2 : ℝ) := by
  have hd1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu1 : ContDiff ℝ 1 (deriv u) := ContDiff.deriv' (n := 1) (by rwa [one_add_one_eq_two])
  have hd2 : Differentiable ℝ (deriv u) := hu.differentiable_deriv_two
  have hc2 : Continuous (deriv (deriv u)) := hu1.continuous_deriv_one
  have hodd : deriv u 0 = 0 := by
    have h := deriv_comp_neg (f := u) (x := (0 : ℝ))
    rw [show (fun x ↦ u (-x)) = u from funext he, neg_zero] at h
    exact self_eq_neg.mp h
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc2.continuousOn (s := Icc (-R) R))
  refine ⟨max M 0, le_max_right _ _, fun y hy ↦ ?_⟩
  have hM0 : ∀ t ∈ Icc (-R) R, ‖deriv (deriv u) t‖ ≤ max M 0 :=
    fun t ht ↦ (hM t ht).trans (le_max_left _ _)
  have h0R : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
  have h1 : ∀ t ∈ Icc (-R) R, ‖deriv u t‖ ≤ max M 0 * |t| := by
    intro t ht
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv u) (fun x _ ↦ hd2 x) hM0
      (convex_Icc (-R) R) h0R ht
    rwa [hodd, sub_zero, sub_zero, Real.norm_eq_abs] at h
  have hyR : |y| ≤ R := abs_le.mpr hy
  have hsub : Icc (-|y|) |y| ⊆ Icc (-R) R := Icc_subset_Icc (neg_le_neg hyR) hyR
  have h0y : (0 : ℝ) ∈ Icc (-|y|) |y| := ⟨neg_nonpos.mpr (abs_nonneg y), abs_nonneg y⟩
  have hyI : y ∈ Icc (-|y|) |y| := ⟨neg_abs_le y, le_abs_self y⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := u) (C := max M 0 * |y|)
    (fun x _ ↦ hd1 x)
    (fun x hx ↦ (h1 x (hsub hx)).trans
      (mul_le_mul_of_nonneg_left (abs_le.mpr hx) (le_max_right _ _)))
    (convex_Icc (-|y|) |y|) h0y hyI
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at h
  calc ‖u y‖ ≤ max M 0 * |y| * |y| := h
    _ = max M 0 * |y| ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        ring

/-- Reconstruction: for `1/2 ≤ α < 5/2` every vector of the weighted even band is within any
given distance of a band vector whose pointwise representative is an even Schwartz function
with Fourier transform zero outside `[-Y, Y]`. Band vectors vanish at the origin, hence to
second order, and `x ^ 4` times the weight is integrable there for `α < 5/2`. -/
theorem exists_schwartz_realPWBand_norm_sub_lt_of_half_le (hα : 1 / 2 ≤ α) (hα' : α < 5 / 2)
    (hs : 0 ≤ s) (hY : 0 < Y)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) {η : ℝ} (hη : 0 < η) :
    ∃ (g : 𝓢(ℝ, ℂ)) (f' : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)),
      Function.Even (g : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧
      (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f') = g ∧
      ‖f - f'‖ < η := by
  refine exists_schwartz_realPWBand_norm_sub_lt_of_local (by linarith) hs hY f 2 zero_le_two
    (by linarith) (fun R ↦ ?_) hη
  exact exists_norm_le_mul_sq_of_even
    (mod_cast RealPWBand.contDiff_evaluation Y (volume_le_realPWIntervalMeasure α s hs) f 2)
    (RealPWBand.evaluation_even Y (volume_le_realPWIntervalMeasure α s hs) f)
    (realPWBand_evaluation_zero hα hs f) R

/-- Reconstruction: for `0 ≤ α < 5/2` the band vectors given by even Schwartz functions with
Fourier transform zero outside `[-Y, Y]` are dense in the weighted even band. -/
theorem dense_realPWBand_schwartz_of_lt_five_halves (hα : 0 ≤ α) (hα' : α < 5 / 2) (hs : 0 ≤ s)
    (hY : 0 < Y) :
    Dense {f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) |
      ∃ g : 𝓢(ℝ, ℂ), Function.Even (g : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g) ξ = 0) ∧
        (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) = g} := by
  rcases lt_or_ge α (1 / 2) with h | h
  · exact dense_realPWBand_schwartz hα h hs hY
  · intro f
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
      exists_schwartz_realPWBand_norm_sub_lt_of_half_le h hα' hs hY f hη
    exact ⟨f', ⟨g, hge, hgb, hgf⟩, by rwa [dist_eq_norm]⟩

/-- Reconstruction: at width one half with `s ≤ 1` the polar-free core is dense in the weighted
even band. Vanishing at the origin holds for every band vector, and the condition of integral
zero is lost in the closure. -/
theorem dense_realPWBandPolarFreeCore_half (hs : 0 ≤ s) (hs1 : s ≤ 1) (hY : 0 < Y) :
    Dense (realPWBandPolarFreeCore Y (1 / 2) hs) := by
  intro f
  rw [← closure_closure, Metric.mem_closure_iff]
  intro η hη
  obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
    exists_schwartz_realPWBand_norm_sub_lt_of_half_le (α := 1 / 2) le_rfl (by norm_num) hs hY
      f hη
  have hg0 : g 0 = 0 := by
    rw [← congrFun hgf 0]
    exact realPWBand_evaluation_zero le_rfl hs f'
  exact ⟨f', mem_closure_realPWBandPolarFreeCore_of_schwartz_half hs hs1 hY g hge hgb hg0 f'
    hgf, by rwa [dist_eq_norm]⟩

/-- Reconstruction: at width one half with `s ≤ 1` the closure of the polar-free core is the
whole weighted even band. -/
theorem closure_realPWBandPolarFreeCore_half_eq_univ (hs : 0 ≤ s) (hs1 : s ≤ 1) (hY : 0 < Y) :
    closure (realPWBandPolarFreeCore Y (1 / 2) hs) = univ :=
  (dense_realPWBandPolarFreeCore_half hs hs1 hY).closure_eq

/-- Reconstruction: for `1/2 ≤ α < 5/2`, when the reciprocal of the weight is integrable, the
closure of the polar-free core is the set of band vectors of integral zero. Vanishing at the
origin holds for every band vector, and the integral is a continuous linear functional. -/
theorem closure_realPWBandPolarFreeCore_eq_of_integrable (hα : 1 / 2 ≤ α) (hα' : α < 5 / 2)
    (hs : 0 ≤ s) (hY : 0 < Y)
    (hint : Integrable (fun x ↦ (realPWIntervalWeight α s x)⁻¹)) :
    closure (realPWBandPolarFreeCore Y α hs) =
      {f | ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f = 0} := by
  obtain ⟨I, hI, hIc⟩ := exists_realPWBand_integralFunctional_of_integrable (Y := Y) hs hint
  apply Set.Subset.antisymm
  · intro f hf
    change ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f = 0
    rw [← (hI f).2]
    exact hIc f hf
  · intro f hf
    change ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f = 0 at hf
    have hIf : I f = 0 := by
      rw [(hI f).2]
      exact hf
    have hIg : ∀ (g : 𝓢(ℝ, ℂ))
        (f' : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)),
        (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f') = g →
        ∫ x, g x = I f' := by
      intro g f' hgf
      rw [(hI f').2, hgf]
    rw [Metric.mem_closure_iff]
    intro η hη
    by_cases hex : ∃ (g₀ : 𝓢(ℝ, ℂ))
        (e₀ : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)),
        Function.Even (g₀ : ℝ → ℂ) ∧ (∀ ξ ∉ Icc (-Y) Y, (𝓕 g₀) ξ = 0) ∧
        (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x e₀) =
          g₀ ∧ ∫ x, g₀ x ≠ 0
    · obtain ⟨g₀, e₀, he₀, hb₀, hev₀, hne⟩ := hex
      let K : ℝ := 1 + ‖I‖ * (‖∫ x, g₀ x‖⁻¹ * ‖e₀‖)
      have hK : 0 < K := by positivity
      obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
        exists_schwartz_realPWBand_norm_sub_lt_of_half_le hα hα' hs hY f (div_pos hη hK)
      let c : ℂ := (∫ x, g x) / ∫ x, g₀ x
      let g₂ : 𝓢(ℝ, ℂ) := g - c • g₀
      let f₂ := f' - c • e₀
      have hg₂ (x : ℝ) : g₂ x = g x - c * g₀ x := rfl
      have hg₂e : Function.Even (g₂ : ℝ → ℂ) := fun x ↦ by
        rw [hg₂, hg₂, hge x, he₀ x]
      have hg₂b : ∀ ξ ∉ Icc (-Y) Y, (𝓕 g₂) ξ = 0 := fun ξ hξ ↦ by
        change (𝓕 (g - c • g₀)) ξ = 0
        rw [FourierTransform.fourier_sub, FourierTransform.fourier_smul, sub_apply, smul_apply,
          hgb ξ hξ, hb₀ ξ hξ, smul_zero, sub_zero]
      have hf₂ : (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x
          f₂) = g₂ := by
        funext x
        change RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x
          (f' - c • e₀) = g x - c * g₀ x
        rw [map_sub, map_smul, congrFun hgf x, congrFun hev₀ x, smul_eq_mul]
      have hg₂0 : g₂ 0 = 0 := by
        rw [← congrFun hf₂ 0]
        exact realPWBand_evaluation_zero hα hs f₂
      have hg₂i : ∫ x, g₂ x = 0 := by
        have h : (fun x ↦ g₂ x) = fun x ↦ g x - c * g₀ x := funext hg₂
        rw [h, integral_sub g.integrable (g₀.integrable.const_mul c), integral_const_mul,
          div_mul_cancel₀ _ hne, sub_self]
      refine ⟨f₂, ⟨g₂, hg₂e, hg₂b, hg₂0, hg₂i, hf₂⟩, ?_⟩
      have hgi : ‖∫ x, g x‖ ≤ ‖I‖ * ‖f - f'‖ := by
        have h : ∫ x, g x = -I (f - f') := by
          rw [map_sub, hIf, zero_sub, neg_neg]
          exact hIg g f' hgf
        rw [h, norm_neg]
        exact I.le_opNorm _
      have hc : ‖c‖ ≤ ‖I‖ * ‖f - f'‖ * ‖∫ x, g₀ x‖⁻¹ := by
        change ‖(∫ x, g x) / ∫ x, g₀ x‖ ≤ _
        rw [norm_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hgi (inv_nonneg.mpr (norm_nonneg _))
      rw [dist_eq_norm]
      calc ‖f - f₂‖ = ‖(f - f') + c • e₀‖ := by
            congr 1
            change f - (f' - c • e₀) = _
            abel
        _ ≤ ‖f - f'‖ + ‖c‖ * ‖e₀‖ := (norm_add_le _ _).trans (by rw [norm_smul])
        _ ≤ ‖f - f'‖ + (‖I‖ * ‖f - f'‖ * ‖∫ x, g₀ x‖⁻¹) * ‖e₀‖ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
        _ = K * ‖f - f'‖ := by
            change _ = (1 + ‖I‖ * (‖∫ x, g₀ x‖⁻¹ * ‖e₀‖)) * ‖f - f'‖
            ring
        _ < K * (η / K) := mul_lt_mul_of_pos_left hclose hK
        _ = η := mul_div_cancel₀ _ hK.ne'
    · push Not at hex
      obtain ⟨g, f', hge, hgb, hgf, hclose⟩ :=
        exists_schwartz_realPWBand_norm_sub_lt_of_half_le hα hα' hs hY f hη
      have hgi : ∫ x, g x = 0 := hex g f' hge hgb hgf
      have hg0 : g 0 = 0 := by
        rw [← congrFun hgf 0]
        exact realPWBand_evaluation_zero hα hs f'
      exact ⟨f', ⟨g, hge, hgb, hg0, hgi, hgf⟩, by rwa [dist_eq_norm]⟩

/-- Reconstruction: for `1/2 < α < 5/2` the closure of the polar-free core is the set of band
vectors of integral zero. -/
theorem closure_realPWBandPolarFreeCore_eq_integral (hα : 1 / 2 < α) (hα' : α < 5 / 2)
    (hs : 0 ≤ s) (hY : 0 < Y) :
    closure (realPWBandPolarFreeCore Y α hs) =
      {f | ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f = 0} :=
  closure_realPWBandPolarFreeCore_eq_of_integrable hα.le hα' hs hY
    (integrable_inv_realPWIntervalWeight hα hs)

/-- Reconstruction: at width one half with `s > 1` the closure of the polar-free core is the
set of band vectors of integral zero. -/
theorem closure_realPWBandPolarFreeCore_half_eq_integral (hs : 0 ≤ s) (hs1 : 1 < s)
    (hY : 0 < Y) :
    closure (realPWBandPolarFreeCore Y (1 / 2) hs) =
      {f | ∫ x, RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) x f =
        0} :=
  closure_realPWBandPolarFreeCore_eq_of_integrable le_rfl (by norm_num) hs hY
    (integrable_inv_realPWIntervalWeight_half hs1)

end RiemannMasullo.Isolated
