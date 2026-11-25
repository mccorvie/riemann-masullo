module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.MomentSymbol
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Tactic

/-! Integration by parts in the actual polynomially weighted real log coordinate. -/

@[expose] public noncomputable section
open Real MeasureTheory Filter Set
open scoped InnerProductSpace

namespace RiemannMasullo.CardinalMoment

private theorem weighted_product_integrable {θ A : ℝ} {a : ℝ → ℝ} {V : Type*}
    [NormedAddCommGroup V] {H : ℝ → V} (hH : AEStronglyMeasurable H)
    (hi : Integrable (fun x ↦ symbol θ x*‖H x‖^2)) (ha : AEStronglyMeasurable a)
    (hb : ∀ x, |a x| ≤ A*symbol θ x) :
    Integrable (fun x ↦ a x*‖H x‖^2) := by
  refine (hi.const_mul A).mono' (ha.mul (hH.norm.pow 2)) (.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖H x‖),← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb x) (sq_nonneg _)

/-- The weighted first-moment identity follows from the stationary first derivative.
Both energy hypotheses are ordinary integrability conditions; the exact finite
Fourier cardinal below supplies them and the stationarity condition. -/
theorem firstMoment_of_stationarity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {θ : ℝ} (hθ : 1 ≤ θ) (H D : ℝ → V)
    (hH : ∀ x, HasDerivAt H (D x) x) (hD : AEStronglyMeasurable D)
    (hiH : Integrable (fun x ↦ symbol θ x*‖H x‖^2))
    (hiD : Integrable (fun x ↦ symbol θ x*‖D x‖^2))
    (hstat : (∫ x, ⟪symbolSlope θ x • H x + symbol θ x • D x, D x⟫_ℝ) = 0) :
    (∫ x, symbol θ x*‖D x‖^2) = (∫ x, symbolCurvature θ x*‖H x‖^2)/2 ∧
    θ*(∫ x, symbol (θ-1) x*‖H x‖^2) ≤ ∫ x, symbol θ x*‖D x‖^2 ∧
    (∫ x, symbol θ x*‖D x‖^2) ≤ θ*(2*θ-1)*(∫ x, symbol (θ-1) x*‖H x‖^2) := by
  have hθ₀ : 0 ≤ θ := by linarith
  have hHm : AEStronglyMeasurable H :=
    (continuous_iff_continuousAt.mpr fun x ↦ (hH x).continuousAt).aestronglyMeasurable
  have hmc (t : ℝ) : Continuous (symbol t) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_symbol t x).continuousAt
  have hsc : Continuous (symbolSlope θ) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_symbolSlope θ x).continuousAt
  have hcc : Continuous (symbolCurvature θ) := by unfold symbolCurvature; fun_prop
  have hprim := weighted_product_integrable hHm hiH hsc.aestronglyMeasurable (fun x ↦ symbolSlope_abs_le θ x hθ₀)
  have hcurv := weighted_product_integrable hHm hiH hcc.aestronglyMeasurable (fun x ↦ symbolCurvature_abs_le θ x hθ)
  have hweak := weighted_product_integrable (A := 1) hHm hiH (hmc (θ-1)).aestronglyMeasurable
    (fun x ↦ by simpa only [abs_of_pos (symbol_pos _ _),one_mul] using symbol_decr_exponent θ x)
  have hmix : Integrable (fun x ↦ symbolSlope θ x*⟪H x,D x⟫_ℝ) := by
    refine ((hiH.add hiD).const_mul (2*θ)).mono' (hsc.aestronglyMeasurable.mul (hHm.inner hD))
      (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs,abs_mul]
    have hAB : ‖H x‖*‖D x‖ ≤ ‖H x‖^2+‖D x‖^2 :=
      by nlinarith only [sq_nonneg (‖H x‖-‖D x‖),sq_nonneg ‖H x‖,sq_nonneg ‖D x‖]
    calc
      _ ≤ (2*θ*symbol θ x)*(‖H x‖*‖D x‖) := mul_le_mul (symbolSlope_abs_le _ _ hθ₀)
        (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity [symbol_pos θ x])
      _ ≤ (2*θ*symbol θ x)*(‖H x‖^2+‖D x‖^2) := mul_le_mul_of_nonneg_left hAB
        (by positivity [symbol_pos θ x])
      _ = _ := by simp only [Pi.add_apply]; ring
  have hs : (∫ x, symbolSlope θ x*⟪H x,D x⟫_ℝ) + (∫ x, symbol θ x*‖D x‖^2) = 0 := by
    simpa only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,integral_add hmix hiD]
      using hstat
  have h2mix : Integrable (fun x ↦ symbolSlope θ x*(2*⟪H x,D x⟫_ℝ)) :=
    (hmix.const_mul 2).congr (.of_forall fun x ↦ by ring)
  have hip := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := symbolSlope θ) (v := fun x ↦ ‖H x‖^2)
    (u' := symbolCurvature θ) (v' := fun x ↦ 2*⟪H x,D x⟫_ℝ)
    (fun x _ ↦ hasDerivAt_symbolSlope θ x) (fun x _ ↦ (hH x).norm_sq) h2mix hcurv hprim
  have htwo : (∫ x, symbolSlope θ x*(2*⟪H x,D x⟫_ℝ)) = 2*∫ x, symbolSlope θ x*⟪H x,D x⟫_ℝ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x ↦ by ring)
  rw [htwo] at hip
  have heq : (∫ x, symbol θ x*‖D x‖^2) = (∫ x, symbolCurvature θ x*‖H x‖^2)/2 := by linarith
  refine ⟨heq,?_,?_⟩
  · have hi := integral_mono (hweak.const_mul (2*θ)) hcurv (fun x ↦
        show (2*θ)*(symbol (θ-1) x*‖H x‖^2) ≤ symbolCurvature θ x*‖H x‖^2 by
          have hh := mul_le_mul_of_nonneg_right (half_symbolCurvature_bounds θ x hθ).1 (sq_nonneg ‖H x‖)
          linarith)
    rw [integral_const_mul] at hi
    linarith
  · have hi := integral_mono hcurv (hweak.const_mul (2*(θ*(2*θ-1)))) (fun x ↦
        show symbolCurvature θ x*‖H x‖^2 ≤ (2*(θ*(2*θ-1)))*(symbol (θ-1) x*‖H x‖^2) by
          have hh := mul_le_mul_of_nonneg_right (half_symbolCurvature_bounds θ x hθ).2 (sq_nonneg ‖H x‖)
          linarith)
    rw [integral_const_mul] at hi
    linarith

end RiemannMasullo.CardinalMoment
