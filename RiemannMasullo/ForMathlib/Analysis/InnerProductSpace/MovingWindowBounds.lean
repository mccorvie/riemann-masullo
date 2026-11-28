module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Quantitative tools for moving-window trace estimates

These are general analytic lemmas supporting the moving-window calculation discussed in
riemann-masullo issue #7353. They certify the exponential resolvent estimate, the orthogonal
output combination, and the stronger quadratic bound when the input and output legs agree.
They do not assert that the actual arithmetic convolution-projection product is positive.
-/

public section

namespace RiemannMasullo.Isolated

open MeasureTheory Set
open scoped ENNReal

/-- An exponentially discounted, strongly measurable family of vectors bounded by `R`
is Bochner integrable on the positive half-line. -/
theorem integrable_exp_discount_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B R : ℝ} (hB : 0 < B) (f : ℝ → E)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖f t‖ ≤ R) :
    Integrable (fun t : ℝ ↦ Real.exp (-B * t) • f t) (volume.restrict (Ioi 0)) := by
  have hmajor : Integrable (fun t : ℝ ↦ Real.exp (-B * t) * R)
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hB) 0).mul_const R
  refine hmajor.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.smul hf) ?_
  filter_upwards [hbound] with t ht
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)

/-- The exact `1 / B` resolvent bound for a uniformly norm-bounded vector family. -/
theorem norm_integral_exp_discount_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B R : ℝ} (hB : 0 < B) (f : ℝ → E)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖f t‖ ≤ R) :
    ‖∫ t : ℝ in Ioi 0, Real.exp (-B * t) • f t‖ ≤ R / B := by
  have hmajor : Integrable (fun t : ℝ ↦ Real.exp (-B * t) * R)
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hB) 0).mul_const R
  calc
    ‖∫ t : ℝ in Ioi 0, Real.exp (-B * t) • f t‖
      ≤ ∫ t : ℝ in Ioi 0, Real.exp (-B * t) * R := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards [hbound] with t ht
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
          mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = R / B := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hB) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
      ring

/-- Additional exponential decay gives the improved resolvent denominator `B + κ`.
This hypothesis is a genuine extra estimate, not a property of translations alone. -/
theorem norm_integral_exp_discount_of_decay_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B κ R : ℝ} (hBκ : 0 < B + κ) (f : ℝ → E)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖f t‖ ≤ Real.exp (-κ * t) * R) :
    ‖∫ t : ℝ in Ioi 0, Real.exp (-B * t) • f t‖ ≤ R / (B + κ) := by
  have hmajor : Integrable (fun t : ℝ ↦ Real.exp (-(B + κ) * t) * R)
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hBκ) 0).mul_const R
  calc
    ‖∫ t : ℝ in Ioi 0, Real.exp (-B * t) • f t‖
      ≤ ∫ t : ℝ in Ioi 0, Real.exp (-(B + κ) * t) * R := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards [hbound] with t ht
        have heq : Real.exp (-B * t) * Real.exp (-κ * t) =
            Real.exp (-(B + κ) * t) := by rw [← Real.exp_add]; congr 1; ring
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          ← mul_assoc, heq] using mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (-B * t))
    _ = R / (B + κ) := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hBκ) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
      ring

/-- The actual translation family in `L²(ℝ; E)` is strongly continuous. The domain
additive action represents `x ↦ f(t + x)` almost everywhere. -/
theorem continuous_l2_translation
    {E : Type*} [NormedAddCommGroup E]
    (f : Lp E 2 (volume : Measure ℝ)) :
    Continuous (fun t : ℝ ↦ DomAddAct.mk t +ᵥ f) := by
  let : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  exact DomAddAct.continuous_mk.vadd continuous_const

/-- The exponentially averaged translation family is a genuine Bochner-integrable
`L²`-valued function, not merely a formal convolution expression. -/
theorem integrable_l2_translation_resolvent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (f : Lp E 2 (volume : Measure ℝ)) :
    Integrable (fun t : ℝ ↦ Real.exp (-B * t) • (DomAddAct.mk t +ᵥ f))
      (volume.restrict (Ioi 0)) := by
  apply integrable_exp_discount_of_norm_le hB (fun t ↦ DomAddAct.mk t +ᵥ f)
    (continuous_l2_translation f).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t ↦ (DomAddAct.norm_vadd_Lp _ _).le)

/-- The exponentially averaged translation operator has `L²` norm at most `1 / B`.
This certifies the resolvent estimate used for the two half-line kernels. -/
theorem norm_l2_translation_resolvent_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (f : Lp E 2 (volume : Measure ℝ)) :
    ‖∫ t : ℝ in Ioi 0, Real.exp (-B * t) • (DomAddAct.mk t +ᵥ f)‖ ≤ ‖f‖ / B := by
  apply norm_integral_exp_discount_le hB
  exact Filter.Eventually.of_forall (fun t ↦ (DomAddAct.norm_vadd_Lp _ _).le)

/-- Restricting the averaged translation to the positive half-line preserves the
resolvent bound. This is the half-line restriction used in the kernel comparison. -/
theorem norm_half_line_translation_resolvent_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (f : Lp E 2 (volume : Measure ℝ)) :
    ‖LpToLpRestrictCLM ℝ E ℝ volume 2 (Ioi 0)
      (∫ t : ℝ in Ioi 0, Real.exp (-B * t) • (DomAddAct.mk t +ᵥ f))‖ ≤ ‖f‖ / B := by
  exact (norm_Lp_toLp_restrict_le (Ioi (0 : ℝ)) _).trans
    (norm_l2_translation_resolvent_le hB f)

/-- A two-dimensional Cauchy--Schwarz estimate, with the exact direct-sum coefficient. -/
theorem moving_window_two_component_bound (t u v : ℝ) :
    u + t * v ≤ Real.sqrt (1 + t ^ 2) * Real.sqrt (u ^ 2 + v ^ 2) := by
  have h1 : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have h2 : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hprod : (Real.sqrt (1 + t ^ 2) * Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 =
      (1 + t ^ 2) * (u ^ 2 + v ^ 2) := by rw [mul_pow, h1, h2]
  have hnonneg : 0 ≤ Real.sqrt (1 + t ^ 2) * Real.sqrt (u ^ 2 + v ^ 2) := by positivity
  nlinarith [sq_nonneg (t * u - v)]

/-- The two-dimensional quadratic estimate that improves the moving-window bound when
its two rank-one legs are the same. The coefficient is the largest eigenvalue of
`[[1, t/2], [t/2, 0]]`. -/
theorem moving_window_quadratic_bound (t u v : ℝ) :
    u ^ 2 + t * u * v ≤
      ((1 + Real.sqrt (1 + t ^ 2)) / 2) * (u ^ 2 + v ^ 2) := by
  let r := Real.sqrt (1 + t ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg t]
  have hprod : (r ^ 2) * (u ^ 2) = (1 + t ^ 2) * (u ^ 2) := by rw [hr2]
  have hs := sq_nonneg (t * u - (1 + r) * v)
  have hfactor : 0 ≤ (1 + r) *
      (((1 + r) / 2) * (u ^ 2 + v ^ 2) - (u ^ 2 + t * u * v)) := by
    nlinarith
  have hpos : 0 < 1 + r := by positivity
  have hnonneg := (mul_nonneg_iff_of_pos_left hpos).mp hfactor
  dsimp [r] at hnonneg
  linarith

/-- The stronger quadratic coefficient is strictly smaller than the unconstrained
orthogonal-output coefficient whenever the crossing component is nonzero. -/
theorem moving_window_positive_constant_lt (t : ℝ) (ht : t ≠ 0) :
    (1 + Real.sqrt (1 + t ^ 2)) / 2 < Real.sqrt (1 + t ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  have hr := Real.sqrt_nonneg (1 + t ^ 2)
  have ht2 := sq_pos_of_ne_zero ht
  nlinarith

/-- A concrete vector attains the scalar quadratic bound. -/
theorem moving_window_quadratic_attained (t : ℝ) :
    (1 + Real.sqrt (1 + t ^ 2)) ^ 2 +
        t * (1 + Real.sqrt (1 + t ^ 2)) * t =
      ((1 + Real.sqrt (1 + t ^ 2)) / 2) *
        ((1 + Real.sqrt (1 + t ^ 2)) ^ 2 + t ^ 2) := by
  have hs : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  linear_combination (-(1 + Real.sqrt (1 + t ^ 2)) / 2) * hs

/-- The quadratic coefficient is optimal over all pairs of real numbers. -/
theorem moving_window_quadratic_best_constant (t K : ℝ) :
    (∀ u v : ℝ, u ^ 2 + t * u * v ≤ K * (u ^ 2 + v ^ 2)) ↔
      (1 + Real.sqrt (1 + t ^ 2)) / 2 ≤ K := by
  constructor
  · intro h
    have htest := h (1 + Real.sqrt (1 + t ^ 2)) t
    rw [moving_window_quadratic_attained] at htest
    have hpos : 0 < (1 + Real.sqrt (1 + t ^ 2)) ^ 2 + t ^ 2 := by
      have hr := Real.sqrt_nonneg (1 + t ^ 2)
      positivity
    exact (mul_le_mul_iff_of_pos_right hpos).mp htest
  · intro h u v
    exact (moving_window_quadratic_bound t u v).trans
      (mul_le_mul_of_nonneg_right h (by positivity))

/-- A same-vector two-output operator estimate. This is the Hilbert-space step behind
the sharper positive trace-class bound; no positivity of an arithmetic operator is assumed. -/
theorem moving_window_same_vector_bound
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (A : E →L[𝕜] E) (D : E →L[𝕜] F) (t B : ℝ) (hB : 0 < B)
    (f : E) (g : F) (hA : ‖A f‖ ≤ ‖f‖ / B)
    (hD : ‖D f‖ ≤ t * ‖f‖ / B) :
    ‖inner 𝕜 (A f) f + inner 𝕜 (D f) g‖ ≤
      ((1 + Real.sqrt (1 + t ^ 2)) / (2 * B)) * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  calc
    ‖inner 𝕜 (A f) f + inner 𝕜 (D f) g‖
      ≤ ‖inner 𝕜 (A f) f‖ + ‖inner 𝕜 (D f) g‖ := norm_add_le _ _
    _ ≤ ‖A f‖ * ‖f‖ + ‖D f‖ * ‖g‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖f‖ / B) * ‖f‖ + (t * ‖f‖ / B) * ‖g‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    _ = (‖f‖ ^ 2 + t * ‖f‖ * ‖g‖) / B := by ring
    _ ≤ (((1 + Real.sqrt (1 + t ^ 2)) / 2) * (‖f‖ ^ 2 + ‖g‖ ^ 2)) / B :=
      div_le_div_of_nonneg_right (moving_window_quadratic_bound t ‖f‖ ‖g‖) hB.le
    _ = _ := by ring

/-- The unconstrained two-leg Hilbert-space estimate combines the two output
components orthogonally. It supplies the sharp coefficient before the kernel/trace assembly. -/
theorem moving_window_two_leg_bound
    {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (A : E →L[𝕜] F) (D : E →L[𝕜] G) (t B : ℝ) (hB : 0 < B)
    (f : E) (g : F) (h : G) (hA : ‖A f‖ ≤ ‖f‖ / B)
    (hD : ‖D f‖ ≤ t * ‖f‖ / B) :
    ‖inner 𝕜 (A f) g + inner 𝕜 (D f) h‖ ≤
      (Real.sqrt (1 + t ^ 2) / B) * ‖f‖ * Real.sqrt (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
  calc
    ‖inner 𝕜 (A f) g + inner 𝕜 (D f) h‖
      ≤ ‖inner 𝕜 (A f) g‖ + ‖inner 𝕜 (D f) h‖ := norm_add_le _ _
    _ ≤ ‖A f‖ * ‖g‖ + ‖D f‖ * ‖h‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖f‖ / B) * ‖g‖ + (t * ‖f‖ / B) * ‖h‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    _ = (‖f‖ / B) * (‖g‖ + t * ‖h‖) := by ring
    _ ≤ (‖f‖ / B) * (Real.sqrt (1 + t ^ 2) * Real.sqrt (‖g‖ ^ 2 + ‖h‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (moving_window_two_component_bound t ‖g‖ ‖h‖)
        (div_nonneg (norm_nonneg _) hB.le)
    _ = _ := by ring

end RiemannMasullo.Isolated
