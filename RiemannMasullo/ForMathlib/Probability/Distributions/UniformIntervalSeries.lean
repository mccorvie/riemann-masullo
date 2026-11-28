module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Independent series of centered uniform interval variables

For nonnegative summable radii, the compact law of the coordinate series is even and its
bilateral Laplace transform is the convergent product of its individual interval transforms.
-/

@[expose] public section

open scoped unitInterval Topology BigOperators
open MeasureTheory Set Filter

namespace RiemannMasullo
namespace IntervalBoxLaw

/-- The centered copy of a uniform unit-interval coordinate with prescribed radius. -/
private def step (r : ℝ) (u : I) : ℝ := r * (2 * (u : ℝ) - 1)

private lemma abs_step_le {r : ℝ} (hr : 0 ≤ r) (u : I) : |step r u| ≤ r := by
  have h : |2 * (u : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [u.property.1], by linarith [u.property.2]⟩
  simpa [step, abs_mul, abs_of_nonneg hr] using mul_le_mul_of_nonneg_left h hr

private lemma continuous_step (r : ℝ) : Continuous (step r) := by unfold step; fun_prop

/-- The weighted sum of the centered unit-interval coordinates. -/
private noncomputable def series (a : ℕ → ℝ) (u : ℕ → I) : ℝ := ∑' n, step (a n) (u n)

private lemma summable_step {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (u : ℕ → I) :
    Summable (fun n ↦ step (a n) (u n)) :=
  hs.of_norm_bounded (fun n ↦ by simpa [Real.norm_eq_abs] using abs_step_le (ha n) (u n))

private lemma measurable_series (a : ℕ → ℝ) : Measurable (series a) := by
  apply Measurable.tsum
  intro n
  exact (continuous_step (a n)).measurable.comp (measurable_pi_apply n)

private lemma abs_partial_le {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n) (hs : HasSum a A)
    (s : Finset ℕ) (u : ℕ → I) : |∑ n ∈ s, step (a n) (u n)| ≤ A := by
  calc
    _ ≤ ∑ n ∈ s, |step (a n) (u n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ s, a n := Finset.sum_le_sum fun n _ ↦ abs_step_le (ha n) (u n)
    _ ≤ A := hs.tsum_eq ▸ hs.summable.sum_le_tsum s (fun n _ ↦ ha n)

private lemma series_mem {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n) (hs : HasSum a A)
    (u : ℕ → I) : series a u ∈ Icc (-A) A := by
  apply abs_le.mp
  apply le_of_tendsto' (continuous_abs.tendsto _ |>.comp (summable_step ha hs.summable u).hasSum)
  exact fun s ↦ abs_partial_le ha hs s u

/-- The law of the sum of independent centered uniform variables. -/
noncomputable def law (a : ℕ → ℝ) : Measure ℝ :=
  (Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))).map
    (fun u ↦ ∑' n, a n * (2 * (u n : ℝ) - 1))

instance (a : ℕ → ℝ) : IsProbabilityMeasure (law a) := by
  unfold law
  infer_instance

/-- The support interval is controlled by the full sum of the radii. -/
theorem support_law_subset {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n) (hs : HasSum a A) :
    (law a).support ⊆ Icc (-A) A := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  exact (ae_map_iff (measurable_series a).aemeasurable measurableSet_Icc).mpr
    (ae_of_all _ (series_mem ha hs))

/-- Reflection fixes the physical law because it reflects every uniform coordinate. -/
theorem map_neg_law (a : ℕ → ℝ) : (law a).map Neg.neg = law a := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))
  let reflect (u : ℕ → I) := fun n ↦ unitInterval.symm (u n)
  have hr : Measurable reflect := Measurable.of_eval fun n ↦
    unitInterval.measurable_symm.comp (measurable_pi_apply n)
  have hP : P.map reflect = P := by
    unfold P reflect
    rw [Measure.infinitePi_map_pi _ (fun _ ↦ unitInterval.measurable_symm)]
    simp only [unitInterval.measurePreserving_symm.map_eq]
  have h : Neg.neg ∘ series a = series a ∘ reflect := by
    funext u
    change -(∑' n, step (a n) (u n)) = ∑' n, step (a n) (unitInterval.symm (u n))
    rw [← tsum_neg]
    congr 1
    funext n
    simp only [step, unitInterval.coe_symm_eq]
    ring
  change (P.map (series a)).map Neg.neg = P.map (series a)
  rw [Measure.map_map measurable_neg (measurable_series a), h,
    ← Measure.map_map (measurable_series a) hr, hP]

/-- Each individual coordinate has the normalized interval Laplace transform. -/
private lemma step_laplace (z : ℂ) (r : ℝ) :
    (∫ u : I, Complex.exp (z * (step r u : ℝ))) =
      (∫ x in (-1 : ℝ)..1, Complex.exp (((r : ℂ) * z) * x)) / 2 := by
  let f : ℝ → ℂ := fun x ↦ Complex.exp (((r : ℂ) * z) * x)
  have h : (∫ u : I, Complex.exp (z * (step r u : ℝ))) =
      ∫ u : I, f (2 * (u : ℝ) - 1) := by
    congr 1
    funext u
    unfold f step
    push_cast
    ring_nf
  rw [h, integral_subtype measurableSet_Icc (fun u : ℝ ↦ f (2 * u - 1)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h' := intervalIntegral.integral_comp_mul_sub f (a := (0 : ℝ)) (b := 1) (c := (2 : ℝ)) (by norm_num) 1
  convert h' using 1
  norm_num [f, Complex.real_smul, div_eq_inv_mul, mul_comm]

private lemma partial_transform (a : ℕ → ℝ) (z : ℂ) (s : Finset ℕ) :
    (∫ u, Complex.exp (z * ((∑ n ∈ s, step (a n) (u n) : ℝ) : ℂ))
      ∂Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))) =
      ∏ n ∈ s, (∫ v : I, Complex.exp (z * (step (a n) v : ℝ))) := by
  let F (i : s) (v : I) := Complex.exp (z * (step (a i) v : ℝ))
  have hF (i : s) : Continuous (F i) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_step _)))
  have hInt := MeasureTheory.integral_restrict_infinitePi (fun _ : ℕ ↦ (volume : Measure I))
    (s := s) (f := fun (u : s → I) ↦ ∏ n : s, F n (u n))
    (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [MeasureTheory.integral_fintype_prod_eq_prod F] at hInt
  simpa only [F, ← Finset.prod_attach s, Finset.univ_eq_attach, Finset.restrict,
    Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum] using hInt

/-- The Laplace transform of the physical probability measure equals the convergent product of
the normalized interval transforms, including at the zeros of individual factors. -/
theorem hasProd_laplace {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n) (hs : HasSum a A) (z : ℂ) :
    HasProd (fun n ↦ (∫ x in (-1 : ℝ)..1, Complex.exp (((a n : ℂ) * z) * x)) / 2)
      (∫ x, Complex.exp (z * x) ∂law a) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))
  let F (s : Finset ℕ) (u : ℕ → I) := Complex.exp (z * ((∑ n ∈ s, step (a n) (u n) : ℝ) : ℂ))
  have hF (s : Finset ℕ) : Continuous (F s) := by
    unfold F
    apply Complex.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Complex.continuous_ofReal.comp
    exact continuous_finsetSum _ (fun n _ ↦ (continuous_step _).comp (continuous_apply n))
  have hbound (s : Finset ℕ) (u : ℕ → I) : ‖F s u‖ ≤ Real.exp (|z.re| * A) := by
    unfold F
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans <| (abs_mul _ _).le.trans <|
      mul_le_mul_of_nonneg_left (abs_partial_le ha hs s u) (abs_nonneg _)
  have hlim (u : ℕ → I) : Tendsto (fun s ↦ F s u) atTop
      (𝓝 (Complex.exp (z * (series a u : ℝ)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (summable_step ha hs.summable u).hasSum))
  change HasProd _ (∫ x : ℝ, Complex.exp (z * x) ∂P.map (series a))
  rw [integral_map (measurable_series a).aemeasurable (by fun_prop)]
  change Tendsto _ atTop _
  have hcon := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (fun _ ↦ Real.exp (|z.re| * A))
    (Eventually.of_forall fun s ↦ (hF s).aestronglyMeasurable)
    (Eventually.of_forall fun s ↦ ae_of_all _ (hbound s)) (integrable_const _)
    (ae_of_all _ hlim)
  convert hcon using 1
  funext s
  change _ = ∫ u, F s u ∂P
  rw [show (∫ u, F s u ∂P) = _ from partial_transform a z s]
  exact Finset.prod_congr rfl fun n _ ↦ (step_laplace z (a n)).symm

private lemma charFun_eq_product {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : HasSum a A) (t : ℝ) :
    charFun (law a) t = ∏' n, (∫ x in (-1 : ℝ)..1,
      Complex.exp (((a n : ℂ) * (t * Complex.I)) * x)) / 2 := by
  rw [charFun_apply_real]
  simpa only [Complex.ofReal_mul, mul_right_comm (t : ℂ)] using
    (hasProd_laplace ha hs ((t : ℂ) * Complex.I)).tprod_eq.symm

private lemma law_eq_conv {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n) (hs : HasSum a A) :
    law a = (law (fun n ↦ a (n + 1))).conv (volume.map (step (a 0))) := by
  have htail := ((summable_nat_add_iff (f := a) 1).mpr hs.summable).hasSum
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_eq_product ha hs,
    charFun_eq_product (fun n ↦ ha (n + 1)) htail]
  let F (n : ℕ) := (∫ x in (-1 : ℝ)..1,
    Complex.exp (((a n : ℂ) * (t * Complex.I)) * x)) / 2
  have h0 : charFun (volume.map (step (a 0))) t = F 0 := by
    rw [charFun_apply_real, integral_map (continuous_step _).measurable.aemeasurable (by fun_prop)]
    simpa only [F, Complex.ofReal_mul, mul_right_comm (t : ℂ)] using
      step_laplace ((t : ℂ) * Complex.I) (a 0)
  change (∏' n, F n) = (∏' n, F (n + 1)) * _
  rw [h0, mul_comm]
  exact tprod_eq_zero_mul' (hasProd_laplace (fun n ↦ ha (n + 1)) htail
    ((t : ℂ) * Complex.I)).multipliable

/-- A nondegenerate first interval makes the whole infinite convolution absolutely continuous
with respect to Lebesgue measure. -/
theorem law_absolutelyContinuous {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n) (hs : HasSum a A)
    (h0 : a 0 ≠ 0) : law a ≪ volume := by
  rw [law_eq_conv ha hs]
  apply Measure.conv_absolutelyContinuous
  have hcoe : QuasiMeasurePreserving ((↑) : I → ℝ) volume volume :=
    unitInterval.measurePreserving_coe.quasiMeasurePreserving.mono_right
      Measure.restrict_le_self.absolutelyContinuous
  have hmul : QuasiMeasurePreserving (fun x : ℝ ↦ (2 * a 0) • x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume (mul_ne_zero (by norm_num) h0)
  have hadd := (measurePreserving_add_right (volume : Measure ℝ) (-(a 0))).quasiMeasurePreserving
  apply ((hadd.comp (hmul.comp hcoe)).congr _).absolutelyContinuous
  apply ae_of_all
  intro u
  change 2 * a 0 * (u : ℝ) + -a 0 = a 0 * (2 * (u : ℝ) - 1)
  ring

end IntervalBoxLaw
end RiemannMasullo
