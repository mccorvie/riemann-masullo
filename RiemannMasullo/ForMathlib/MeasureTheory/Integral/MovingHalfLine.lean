module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The scalar kernel at a critical moving half-line

The crossing region of the order-three weighted-translation trace at exponent
`η / 2` and output cutoff `x ≤ 3 * y / 4` is, on writing `u = y - x`,
`0 ≤ x ≤ 3 * u`. Its exponential weight is the kernel below. The two
marginal integrals are the input to the two-leg integral Cauchy--Schwarz
estimate for the lower-window trace correction in §12.3, p. 514.

These statements concern the explicit scalar kernel, not the still-open
global-to-local trace comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RiemannMasullo

/-- The positive crossing-region kernel for the moving cutoff `x ≤ 3 * y / 4`,
with `u = y - x` and exponential normalization `exp (-η * y / 2)`. -/
def criticalWindowKernel (η x u : ℝ) : ℝ :=
  (Icc 0 (3 * u)).indicator (fun t ↦ Real.exp (-(η / 2) * (3 * u - t))) x

/-- The moving-window kernel is nonnegative. -/
theorem criticalWindowKernel_nonneg (η x u : ℝ) : 0 ≤ criticalWindowKernel η x u := by
  classical
  simp only [criticalWindowKernel, Set.indicator_apply]
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- Both scalar coordinates of the moving-window kernel are jointly measurable. -/
theorem measurable_criticalWindowKernel (η : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ criticalWindowKernel η p.1 p.2) := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 3 * p.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_const.mul measurable_snd))
  have hE : Measurable (fun p : ℝ × ℝ ↦ Real.exp (-(η / 2) * (3 * p.2 - p.1))) := by
    fun_prop
  have hfun : (fun p : ℝ × ℝ ↦ criticalWindowKernel η p.1 p.2) =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 3 * p.2}.indicator
        (fun p ↦ Real.exp (-(η / 2) * (3 * p.2 - p.1))) := by
    classical
    funext p
    simp only [criticalWindowKernel, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Icc]
  rw [hfun]
  exact hE.indicator hS

private theorem criticalWindowKernel_row (η : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (fun u ↦ criticalWindowKernel η x u) =
      (Ici (x / 3)).indicator (fun u ↦ Real.exp (-(η / 2) * (3 * u - x))) := by
  classical
  funext u
  by_cases hxu : x ≤ 3 * u
  · have hu : x / 3 ≤ u := by linarith
    simp [criticalWindowKernel, hx, hxu, hu]
  · have hu : ¬x / 3 ≤ u := by linarith
    simp [criticalWindowKernel, hx, hxu, hu]

private theorem criticalWindowKernel_exp_row (η x u : ℝ) :
    Real.exp (-(η / 2) * (3 * u - x)) =
      Real.exp (η * x / 2) * Real.exp (-(3 * η / 2) * u) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Every input-coordinate slice of the positive-width kernel is integrable. -/
theorem integrable_criticalWindowKernel_row {η : ℝ} (hη : 0 < η) (x : ℝ) :
    Integrable (fun u ↦ criticalWindowKernel η x u) := by
  by_cases hx : 0 ≤ x
  · rw [criticalWindowKernel_row η hx]
    apply IntegrableOn.integrable_indicator _ measurableSet_Ici
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simp_rw [criticalWindowKernel_exp_row]
    exact (integrableOn_exp_mul_Ioi (a := -(3 * η / 2)) (by linarith) (x / 3)).const_mul _
  · have heq : (fun u ↦ criticalWindowKernel η x u) = 0 := by
      funext u
      simp [criticalWindowKernel, hx]
    rw [heq]
    exact integrable_zero _ _ _

/-- The input marginal is exactly `2 / (3 * η)` on the nonnegative output half-line. -/
theorem integral_criticalWindowKernel_row {η x : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    (∫ u : ℝ, criticalWindowKernel η x u) = 2 / (3 * η) := by
  rw [criticalWindowKernel_row η hx, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  simp_rw [criticalWindowKernel_exp_row]
  rw [integral_const_mul, integral_exp_mul_Ioi (a := -(3 * η / 2)) (by linarith),
    neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
  rw [show η * x / 2 + -(3 * η / 2) * (x / 3) = 0 by ring, Real.exp_zero]
  field_simp [hη.ne']

/-- The input marginal is bounded by the same constant at every output coordinate. -/
theorem integral_criticalWindowKernel_row_le {η : ℝ} (hη : 0 < η) (x : ℝ) :
    (∫ u : ℝ, criticalWindowKernel η x u) ≤ 2 / (3 * η) := by
  by_cases hx : 0 ≤ x
  · exact (integral_criticalWindowKernel_row hη hx).le
  · have heq : (fun u ↦ criticalWindowKernel η x u) = 0 := by
      funext u
      simp [criticalWindowKernel, hx]
    rw [heq]
    change (∫ _u : ℝ, (0 : ℝ)) ≤ 2 / (3 * η)
    rw [integral_zero]
    positivity

/-- Every output-coordinate slice is integrable, since its support is a compact interval. -/
theorem integrable_criticalWindowKernel_column (η u : ℝ) :
    Integrable (fun x ↦ criticalWindowKernel η x u) := by
  have hc : Continuous (fun x : ℝ ↦ Real.exp (-(η / 2) * (3 * u - x))) := by fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- The output marginal is bounded by `2 / η`, uniformly in the input coordinate. -/
theorem integral_criticalWindowKernel_column_le {η : ℝ} (hη : 0 < η) (u : ℝ) :
    (∫ x : ℝ, criticalWindowKernel η x u) ≤ 2 / η := by
  have heq : (fun x : ℝ ↦ Real.exp (-(η / 2) * (3 * u - x))) =
      fun x ↦ Real.exp (-(3 * η * u / 2)) * Real.exp ((η / 2) * x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ x : ℝ, (Icc 0 (3 * u)).indicator
    (fun t ↦ Real.exp (-(η / 2) * (3 * u - t))) x) ≤ _
  rw [integral_indicator measurableSet_Icc, heq, integral_const_mul]
  have hmono : (∫ x : ℝ in Icc 0 (3 * u), Real.exp ((η / 2) * x)) ≤
      ∫ x : ℝ in Iic (3 * u), Real.exp ((η / 2) * x) := by
    apply setIntegral_mono_set (integrableOn_exp_mul_Iic (a := η / 2) (by linarith) (3 * u))
      (ae_of_all _ fun x ↦ (Real.exp_pos _).le)
    exact Filter.Eventually.of_forall fun x hx ↦ hx.2
  calc
    _ ≤ Real.exp (-(3 * η * u / 2)) *
        ∫ x : ℝ in Iic (3 * u), Real.exp ((η / 2) * x) :=
      mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ = 2 / η := by
      rw [integral_exp_mul_Iic (a := η / 2) (by linarith), ← mul_div_assoc, ← Real.exp_add]
      rw [show -(3 * η * u / 2) + (η / 2) * (3 * u) = 0 by ring, Real.exp_zero]
      field_simp [hη.ne']

/-- The lower Lebesgue input marginal has the same uniform bound. -/
theorem lintegral_criticalWindowKernel_row_le {η : ℝ} (hη : 0 < η) (x : ℝ) :
    (∫⁻ u : ℝ, ENNReal.ofReal (criticalWindowKernel η x u)) ≤
      ENNReal.ofReal (2 / (3 * η)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_criticalWindowKernel_row hη x)
    (ae_of_all _ fun u ↦ criticalWindowKernel_nonneg η x u)]
  exact ENNReal.ofReal_le_ofReal (integral_criticalWindowKernel_row_le hη x)

/-- The lower Lebesgue output marginal has the same uniform bound. -/
theorem lintegral_criticalWindowKernel_column_le {η : ℝ} (hη : 0 < η) (u : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (criticalWindowKernel η x u)) ≤
      ENNReal.ofReal (2 / η) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_criticalWindowKernel_column η u)
    (ae_of_all _ fun x ↦ criticalWindowKernel_nonneg η x u)]
  exact ENNReal.ofReal_le_ofReal (integral_criticalWindowKernel_column_le hη u)

private theorem criticalWindowKernel_half_factor (k a b : ℝ≥0∞) :
    (k * a ^ 2) ^ (1 / 2 : ℝ) * (k * b ^ 2) ^ (1 / 2 : ℝ) = k * a * b := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have ha : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hb : (b ^ 2) ^ (1 / 2 : ℝ) = b := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [ha, hb, mul_mul_mul_comm,
    ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num [mul_assoc]

/-- The two-marginal Cauchy--Schwarz estimate for the critical moving-window
kernel. For finite square integrals its constant is
`sqrt (2 / η) * sqrt (2 / (3 * η)) = 2 / (η * sqrt 3)`.

The statement uses nonnegative integrals, so it remains meaningful before
integrability of the bilinear expression has been established. -/
theorem lintegral_criticalWindowKernel_mul_le {η : ℝ} (hη : 0 < η)
    {a b : ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (criticalWindowKernel η p.1 p.2) * a p.2 * b p.1
        ∂(volume.prod volume)) ≤
      (ENNReal.ofReal (2 / η) * ∫⁻ u : ℝ, a u ^ 2) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (2 / (3 * η)) * ∫⁻ x : ℝ, b x ^ 2) ^ (1 / 2 : ℝ) := by
  let K : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (criticalWindowKernel η p.1 p.2)
  have hK : Measurable K := (measurable_criticalWindowKernel η).ennreal_ofReal
  have hA : Measurable (fun p : ℝ × ℝ ↦ K p * a p.2 ^ 2) :=
    hK.mul ((ha.comp measurable_snd).pow_const 2)
  have hB : Measurable (fun p : ℝ × ℝ ↦ K p * b p.1 ^ 2) :=
    hK.mul ((hb.comp measurable_fst).pow_const 2)
  have hAint : (∫⁻ p : ℝ × ℝ, K p * a p.2 ^ 2 ∂(volume.prod volume)) ≤
      ENNReal.ofReal (2 / η) * ∫⁻ u : ℝ, a u ^ 2 := by
    rw [lintegral_prod_symm _ hA.aemeasurable]
    calc
      _ = ∫⁻ u : ℝ, (∫⁻ x : ℝ, K (x, u)) * a u ^ 2 := by
        apply lintegral_congr
        intro u
        change (∫⁻ x : ℝ, K (x, u) * a u ^ 2) = _
        have hKu : Measurable (fun x : ℝ ↦ K (x, u)) :=
          hK.comp (measurable_id.prodMk measurable_const)
        exact lintegral_mul_const (μ := volume) (f := fun x : ℝ ↦ K (x, u))
          (a u ^ 2) hKu
      _ ≤ ∫⁻ u : ℝ, ENNReal.ofReal (2 / η) * a u ^ 2 := by
        apply lintegral_mono
        intro u
        exact mul_le_mul' (lintegral_criticalWindowKernel_column_le hη u) le_rfl
      _ = _ := lintegral_const_mul _ (ha.pow_const 2)
  have hBint : (∫⁻ p : ℝ × ℝ, K p * b p.1 ^ 2 ∂(volume.prod volume)) ≤
      ENNReal.ofReal (2 / (3 * η)) * ∫⁻ x : ℝ, b x ^ 2 := by
    rw [lintegral_prod _ hB.aemeasurable]
    calc
      _ = ∫⁻ x : ℝ, (∫⁻ u : ℝ, K (x, u)) * b x ^ 2 := by
        apply lintegral_congr
        intro x
        change (∫⁻ u : ℝ, K (x, u) * b x ^ 2) = _
        have hKx : Measurable (fun u : ℝ ↦ K (x, u)) :=
          hK.comp (measurable_const.prodMk measurable_id)
        exact lintegral_mul_const (μ := volume) (f := fun u : ℝ ↦ K (x, u))
          (b x ^ 2) hKx
      _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (2 / (3 * η)) * b x ^ 2 := by
        apply lintegral_mono
        intro x
        exact mul_le_mul' (lintegral_criticalWindowKernel_row_le hη x) le_rfl
      _ = _ := lintegral_const_mul _ (hb.pow_const 2)
  change (∫⁻ p : ℝ × ℝ, K p * a p.2 * b p.1 ∂(volume.prod volume)) ≤ _
  calc
    _ = ∫⁻ p : ℝ × ℝ,
        (K p * a p.2 ^ 2) ^ (1 / 2 : ℝ) * (K p * b p.1 ^ 2) ^ (1 / 2 : ℝ)
          ∂(volume.prod volume) := by
      apply lintegral_congr
      intro p
      exact (criticalWindowKernel_half_factor (K p) (a p.2) (b p.1)).symm
    _ ≤ (∫⁻ p : ℝ × ℝ, K p * a p.2 ^ 2 ∂(volume.prod volume)) ^ (1 / 2 : ℝ) *
        (∫⁻ p : ℝ × ℝ, K p * b p.1 ^ 2 ∂(volume.prod volume)) ^ (1 / 2 : ℝ) :=
      ENNReal.lintegral_mul_norm_pow_le hA.aemeasurable hB.aemeasurable
        (by norm_num) (by norm_num) (by norm_num)
    _ ≤ _ := mul_le_mul'
      (ENNReal.rpow_le_rpow hAint (by norm_num))
      (ENNReal.rpow_le_rpow hBint (by norm_num))

/-- Finite square integrals imply a finite bilinear integral for the critical
moving-window kernel; this is the absolute-integrability part of the Schur bound. -/
theorem lintegral_criticalWindowKernel_mul_lt_top {η : ℝ} (hη : 0 < η)
    {a b : ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (ha2 : (∫⁻ u : ℝ, a u ^ 2) < ⊤) (hb2 : (∫⁻ x : ℝ, b x ^ 2) < ⊤) :
    (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (criticalWindowKernel η p.1 p.2) * a p.2 * b p.1
        ∂(volume.prod volume)) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_criticalWindowKernel_mul_le hη ha hb) ?_
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha2.ne)
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb2.ne)

end RiemannMasullo
