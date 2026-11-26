module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositiveTests
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Compact test actions of strongly continuous forward semigroups

Vector integrals define bounded operators. Positive-time convolution is composition,
proved by compact-support Fubini and the forward semigroup law.
-/

public noncomputable section
open Set Function MeasureTheory Filter
open scoped Topology Pointwise
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
variable (U : ℝ → H →L[ℂ] H) (hU : ∀ x, Continuous (fun t ↦ U t x))
variable (b : ℝ → ℝ) (hb : Continuous b) (hbound : ∀ t, ‖U t‖ ≤ b t)

include hU in
/-- Compact time support makes every vector orbit integral well defined. -/
theorem forwardTest_integrable (f : PositiveTimeTest) (x : H) :
    Integrable (fun t : ℝ ↦ f t • U t x) volume :=
  (f.continuous.smul (hU x)).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right

include hb hbound in
private theorem forwardTest_norm_integral_le (f : PositiveTimeTest) (x : H) :
    ‖∫ t : ℝ, f t • U t x‖ ≤ (∫ t : ℝ, ‖f t‖ * b t) * ‖x‖ := by
  have hc : HasCompactSupport (fun t ↦ ‖f t‖ * b t) := f.hasCompactSupport.norm.mul_right
  have hi : Integrable (fun t : ℝ ↦ (‖f t‖ * b t) * ‖x‖) volume :=
    ((f.continuous.norm.mul hb).integrable_of_hasCompactSupport hc).mul_const _
  calc
    _ ≤ ∫ t : ℝ, (‖f t‖ * b t) * ‖x‖ := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with t
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (((U t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg x)))
        (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- Integrating a strongly continuous, locally bounded forward action against a
positive-time compact smooth test gives a bounded linear operator. -/
def forwardTestOperator (f : PositiveTimeTest) : H →L[ℂ] H := by
  let A : H →ₗ[ℂ] H := {
    toFun x := ∫ t : ℝ, f t • U t x
    map_add' x y := by
      simp only [map_add, smul_add]
      exact integral_add (forwardTest_integrable U hU f x) (forwardTest_integrable U hU f y)
    map_smul' c x := by
      simp only [map_smul, RingHom.id_apply]
      simp_rw [smul_comm (f _) c]
      exact integral_smul c _ }
  exact A.mkContinuous (∫ t : ℝ, ‖f t‖ * b t) (forwardTest_norm_integral_le U b hb hbound f)

/-- Evaluation is the original vector integral. -/
theorem forwardTestOperator_apply (f : PositiveTimeTest) (x : H) :
    forwardTestOperator U hU b hb hbound f x = ∫ t : ℝ, f t • U t x := by rfl

/-- Addition of tests is addition of their integrated actions. -/
theorem forwardTestOperator_add (f g : PositiveTimeTest) :
    forwardTestOperator U hU b hb hbound (f + g) =
      forwardTestOperator U hU b hb hbound f + forwardTestOperator U hU b hb hbound g := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [forwardTestOperator_apply, add_apply, add_smul]
  exact integral_add (forwardTest_integrable U hU f x) (forwardTest_integrable U hU g x)

include hU in
private theorem forward_convolution_integrable (f g : PositiveTimeTest) (x : H) :
    Integrable (fun z : ℝ × ℝ ↦ (f z.1 * g (z.2 - z.1)) • U z.2 x)
      (volume.prod volume) := by
  let F (z : ℝ × ℝ) := (f z.1 * g (z.2 - z.1)) • U z.2 x
  have hcont : Continuous F :=
    ((f.continuous.comp continuous_fst).mul
      (g.continuous.comp (continuous_snd.sub continuous_fst))).smul
      ((hU x).comp continuous_snd)
  have hK := f.hasCompactSupport.isCompact.prod
    (f.hasCompactSupport.isCompact.add g.hasCompactSupport)
  have hc : HasCompactSupport F := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hf : f z.1 ≠ 0 := fun hf ↦ hz (by simp [F, hf])
    have hg : g (z.2 - z.1) ≠ 0 := fun hg ↦ hz (by simp [F, hg])
    refine ⟨subset_tsupport f hf, z.1, subset_tsupport f hf,
      z.2 - z.1, subset_tsupport g hg, ?_⟩
    ring
  exact hcont.integrable_of_hasCompactSupport hc

/-- Convolution of positive-time tests is composition for a forward semigroup.
Only the semigroup law at nonnegative times is used. -/
theorem forwardTestOperator_convolution
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → U (s + t) = (U s).comp (U t))
    (f g : PositiveTimeTest) :
    forwardTestOperator U hU b hb hbound (positiveTestConvolution f g) =
      (forwardTestOperator U hU b hb hbound f).comp
        (forwardTestOperator U hU b hb hbound g) := by
  apply ContinuousLinearMap.ext
  intro x
  let F (s t : ℝ) := (f s * g (t - s)) • U t x
  have hi := forward_convolution_integrable U hU f g x
  calc
    _ = ∫ t : ℝ, ∫ s : ℝ, F s t := by
      rw [forwardTestOperator_apply]
      simp_rw [positiveTestConvolution_apply, ← integral_smul_const]
      rfl
    _ = ∫ s : ℝ, ∫ t : ℝ, F s t := (integral_integral_swap hi).symm
    _ = ∫ s : ℝ, ∫ r : ℝ, f s • U s (g r • U r x) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_add_left_eq_self (F s) s]
      apply integral_congr_ae
      filter_upwards with r
      dsimp only [F]
      rw [add_sub_cancel_left]
      by_cases hs : f s = 0
      · simp only [hs, zero_mul, zero_smul]
      by_cases hr : g r = 0
      · simp only [hr, mul_zero, zero_smul, map_zero, smul_zero]
      have hs0 := f.tsupport_subset (subset_tsupport f hs)
      have hr0 := g.tsupport_subset (subset_tsupport g hr)
      rw [hadd s r hs0.le hr0.le, ContinuousLinearMap.comp_apply, map_smul, mul_smul]
    _ = ∫ s : ℝ, f s • U s (forwardTestOperator U hU b hb hbound g x) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [integral_smul, (U s).integral_comp_comm (forwardTest_integrable U hU g x),
        ← forwardTestOperator_apply U hU b hb hbound g x]
    _ = _ := (forwardTestOperator_apply U hU b hb hbound f _).symm

end RiemannMasullo
