module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedPolarVector
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The frequency transition window on the reflected polar vector -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- The difference from the identity is supported in the transition window on
this vector. Its squared norm is at most the exponential mass of the window. -/
theorem normalizedHalflineExponentialL2_sub_multiplier_shell {a c : ℝ} (hac : a ≤ c)
    (M : FlatL2 →L[ℂ] FlatL2) (b : ℝ → ℝ)
    (hM : (M (normalizedHalflineExponentialL2 a) : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (b x : ℂ) * normalizedHalflineExponentialL2 a x)
    (hb : ∀ᵐ x ∂volume, b x ∈ Icc (0 : ℝ) 1)
    (hOne : ∀ᵐ x ∂volume, c ≤ x → b x = 1) :
    let e := normalizedHalflineExponentialL2 a
    (∀ᵐ x ∂volume, x ∉ Ico a c → (M e - e) x = 0) ∧
      ‖M e - e‖ ^ 2 ≤ 1 - Real.exp (a - c) := by
  intro e
  let d := M e - e
  let g : ℝ → ℝ := (Ici a).indicator (fun x ↦ Real.exp ((a - x) / 2))
  have hSub : (d : ℝ → ℂ) =ᵐ[volume] fun x ↦ M e x - e x := Lp.coeFn_sub (M e) e
  have hZero : ∀ᵐ x ∂volume, x ∉ Ico a c → d x = 0 := by
    filter_upwards [hSub, hM, hOne, normalizedHalflineExponentialL2_ae_zero_lt a]
      with x hsub hmul hone he
    intro hx
    by_cases ha : a ≤ x
    · have hc : c ≤ x := le_of_not_gt fun h ↦ hx ⟨ha, h⟩
      rw [hsub, hmul, hone hc, Complex.ofReal_one, one_mul, sub_self]
    · rw [hsub, hmul, he (lt_of_not_ge ha), mul_zero, sub_zero]
  refine ⟨hZero, ?_⟩
  have hSq : ‖d‖ ^ 2 = ∫ x, ‖d x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (norm_sq_eq_re_inner (𝕜 := ℂ) (d x)).symm)
  have hInt : Integrable (fun x ↦ ‖d x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable d)).mp (Lp.memLp d)
  have hIntShell : Integrable ((Iic c).indicator (fun x ↦ g x * g x)) volume :=
    (show Integrable (fun x ↦ g x * g x) volume by
      simpa only [sub_zero] using integrable_normalizedHalflineExponential_mul_shift a 0).indicator
        measurableSet_Iic
  have hBound : (fun x ↦ ‖d x‖ ^ 2) ≤ᵐ[volume] (Iic c).indicator (fun x ↦ g x * g x) := by
    have heRep : (e : ℝ → ℂ) =ᵐ[volume] fun x ↦ (g x : ℂ) :=
      normalizedHalflineExponentialL2_ae_eq a
    filter_upwards [hSub, hM, hb, heRep, hZero] with x hsub hmul hbx he hzero
    by_cases hx : x ≤ c
    · rw [indicator_of_mem (show x ∈ Iic c from hx)]
      have hCoeff : |b x - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hbx.1], by linarith [hbx.2]⟩
      have hNorm : ‖d x‖ ≤ |g x| := by
        calc
          ‖d x‖ = ‖((b x - 1 : ℝ) : ℂ) * (g x : ℂ)‖ := by
            rw [hsub, hmul, he, Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
          _ = |b x - 1| * |g x| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |g x| := mul_le_of_le_one_left (abs_nonneg _) hCoeff
      exact (pow_le_pow_left₀ (norm_nonneg _) hNorm 2).trans_eq (by rw [sq_abs, pow_two])
    · have hx' : x ∉ Ico a c := fun h ↦ hx h.2.le
      rw [indicator_of_notMem (show x ∉ Iic c from hx), hzero hx']
      simp
  change ‖d‖ ^ 2 ≤ _
  rw [hSq]
  calc
    _ ≤ ∫ x, (Iic c).indicator (fun x ↦ g x * g x) x := integral_mono_ae hInt hIntShell hBound
    _ = 1 - Real.exp (a - c) := by
      rw [integral_indicator measurableSet_Iic]
      simpa [g, hac] using integral_normalizedHalflineExponential_mul_shift_Iic a 0 c

/-- A frequency profile equal to one below `B - δ` changes the reflected polar
vector at bandwidth `B` by squared norm at most `δ / B`. -/
theorem normalizedHalflineExponentialL2_sub_frequencyMultiplier_norm_sq_le
    {B δ : ℝ} (hδ : 0 ≤ δ) (hδB : δ < B) (M : FlatL2 →L[ℂ] FlatL2) (b : ℝ → ℝ)
    (hM : ∀ v, (M v : ℝ → ℂ) =ᵐ[volume] fun x ↦ (b (Real.exp (-x)) : ℂ) * v x)
    (hb : ∀ r, 0 ≤ r → b r ∈ Icc (0 : ℝ) 1)
    (hOne : ∀ r, 0 ≤ r → r ≤ B - δ → b r = 1) :
    let e := normalizedHalflineExponentialL2 (-Real.log B)
    ‖M e - e‖ ^ 2 ≤ δ / B := by
  intro e
  have hB := hδ.trans_lt hδB
  have hLow : 0 < B - δ := sub_pos.mpr hδB
  have hEdges : -Real.log B ≤ -Real.log (B - δ) :=
    neg_le_neg ((Real.log_le_log_iff hLow hB).mpr (sub_le_self _ hδ))
  have hPlateau : ∀ᵐ x ∂volume, -Real.log (B - δ) ≤ x → b (Real.exp (-x)) = 1 :=
    ae_of_all _ fun x hx ↦ by
      have hx' : -x ≤ Real.log (B - δ) := by simpa only [neg_neg] using neg_le_neg hx
      exact hOne _ (Real.exp_pos _).le
        ((Real.exp_le_exp.mpr hx').trans_eq (Real.exp_log hLow))
  have hShell := (normalizedHalflineExponentialL2_sub_multiplier_shell hEdges M
    (fun x ↦ b (Real.exp (-x))) (hM e) (ae_of_all _ fun x ↦ hb _ (Real.exp_pos _).le) hPlateau).2
  change ‖M e - e‖ ^ 2 ≤ 1 - Real.exp (-Real.log B - -Real.log (B - δ)) at hShell
  have hExp : Real.exp (-Real.log B - -Real.log (B - δ)) = (B - δ) / B := by
    rw [show -Real.log B - -Real.log (B - δ) = Real.log (B - δ) - Real.log B by ring,
      Real.exp_sub, Real.exp_log hLow, Real.exp_log hB]
  rw [hExp, sub_div, div_self hB.ne', sub_sub_cancel] at hShell
  exact hShell

end RiemannMasullo
