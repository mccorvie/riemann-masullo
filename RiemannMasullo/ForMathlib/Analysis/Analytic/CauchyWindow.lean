module

public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform interval bounds for the regularized square of a function with reciprocal poles. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal

namespace RiemannMasullo

private def regularizedLinear (η x : ℝ) : ℝ := η * x / (1 + η ^ 2 * x)

private theorem regularizedLinear_mono {η x y : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) (hxy : x ≤ y) :
    regularizedLinear η x ≤ regularizedLinear η y := by
  have hy := hx.trans hxy
  unfold regularizedLinear
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hxy hη]

private theorem regularizedLinear_add_le {η x y : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    regularizedLinear η (x + y) ≤ regularizedLinear η x + regularizedLinear η y := by
  unfold regularizedLinear
  rw [mul_add, add_div]
  apply add_le_add
  · apply div_le_div_of_nonneg_left (mul_nonneg hη hx) (by positivity)
    nlinarith only [mul_nonneg (sq_nonneg η) hy]
  · apply div_le_div_of_nonneg_left (mul_nonneg hη hy) (by positivity)
    nlinarith only [mul_nonneg (sq_nonneg η) hx]

private theorem regularizedLinear_sum_le {ι : Type*} (J : Finset ι) {η : ℝ}
    (hη : 0 ≤ η) (u : ι → ℝ) (hu : ∀ j, 0 ≤ u j) :
    regularizedLinear η (∑ j ∈ J, u j) ≤ ∑ j ∈ J, regularizedLinear η (u j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [regularizedLinear]
  | insert j J hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (regularizedLinear_add_le hη (hu j) (Finset.sum_nonneg fun i _ ↦ hu i)).trans
      (add_le_add_right ih _)

private theorem regularizedLinear_sq_div_le_cauchy (η L γ t : ℝ) (hη : 0 < η) (hL : 0 ≤ L) :
    regularizedLinear η ((L / |t - γ|) ^ 2) ≤
      (π * L) * cauchyPDFReal γ (η * L).toNNReal t := by
  rw [cauchyPDFReal_def, Real.coe_toNNReal _ (mul_nonneg hη.le hL)]
  by_cases h : t = γ
  · subst t
    simp only [sub_self, abs_zero, div_zero, regularizedLinear, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, zero_div]
    positivity
  have hd : t - γ ≠ 0 := sub_ne_zero.mpr h
  have he : (t - γ) ^ 2 + (η * L) ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg _)).ne'
  unfold regularizedLinear
  simp only [div_pow, sq_abs]
  have hden : 1 + η ^ 2 * (L ^ 2 / (t - γ) ^ 2) ≠ 0 := by positivity
  apply le_of_eq
  field_simp [Real.pi_ne_zero, hd, he, hden]

/-- If the absolute value of a measurable function on a unit interval is bounded almost
everywhere by a constant plus finitely many reciprocal poles with nonnegative weights,
its regularized square is integrable there. Its mass is at most twice the regularization
parameter times the squared constant plus π times the total pole weight times the square
root of twice the number of poles. The poles may coincide or lie outside the interval. -/
theorem integral_regularizedSquare_Icc_le {ι : Type*} (J : Finset ι) (γ : ι → ℝ) (m : ι → ℝ≥0)
    (a B η : ℝ) (hη : 0 < η) (q : ℝ → ℝ)
    (hq : AEMeasurable q (volume.restrict (Icc a (a + 1))))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a (a + 1)),
      |q t| ≤ B + ∑ j ∈ J, (m j : ℝ) / |t - γ j|) :
    IntegrableOn (fun t ↦ η * (q t) ^ 2 / (1 + η ^ 2 * (q t) ^ 2)) (Icc a (a + 1)) ∧
      ∫ t in Icc a (a + 1), η * (q t) ^ 2 / (1 + η ^ 2 * (q t) ^ 2) ≤
        2 * η * B ^ 2 + π * √(2 * (J.card : ℝ)) * ∑ j ∈ J, (m j : ℝ) := by
  classical
  let S := Icc a (a + 1)
  let r := √(2 * (J.card : ℝ))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * (J.card : ℝ) := Real.sq_sqrt (by positivity)
  let K (j : ι) (t : ℝ) := (π * (r * (m j : ℝ))) *
    cauchyPDFReal (γ j) (η * (r * (m j : ℝ))).toNNReal t
  have hKpos (j : ι) (t : ℝ) : 0 ≤ K j t := by
    dsimp [K]
    rw [cauchyPDFReal_def]
    positivity
  have hKi (j : ι) : Integrable (K j) :=
    (integrable_cauchyPDFReal (γ j)).const_mul _
  have hKsum : Integrable (fun t ↦ ∑ j ∈ J, K j t) := integrable_finsetSum J fun j _ ↦ hKi j
  have hKiBound (j : ι) : ∫ t in S, K j t ≤ π * (r * (m j : ℝ)) := by
    calc
      _ ≤ ∫ t, K j t := setIntegral_le_integral (hKi j) (ae_of_all _ (hKpos j))
      _ = (π * (r * (m j : ℝ))) * ∫ t, cauchyPDFReal (γ j) (η * (r * (m j : ℝ))).toNNReal t :=
        integral_const_mul _ _
      _ ≤ _ := by
        by_cases hz : (η * (r * (m j : ℝ))).toNNReal = 0
        · simp [hz, mul_nonneg Real.pi_pos.le (mul_nonneg hr (m j).coe_nonneg)]
        · rw [integral_cauchyPDFReal_eq_one _ hz, mul_one]
  let f (t : ℝ) := regularizedLinear η ((q t) ^ 2)
  have hf0 (t : ℝ) : 0 ≤ f t := by dsimp [f, regularizedLinear]; positivity
  have hmajor : ∀ᵐ t ∂volume.restrict S, f t ≤ 2 * η * B ^ 2 + ∑ j ∈ J, K j t := by
    filter_upwards [hbound] with t ht
    let u (j : ι) := (m j : ℝ) / |t - γ j|
    have hu (j : ι) : 0 ≤ u j := by dsimp [u]; positivity
    have hcs := sq_sum_le_card_mul_sum_sq (s := J) (f := u)
    have hs : (∑ j ∈ J, (r * (m j : ℝ) / |t - γ j|) ^ 2) =
        (2 * (J.card : ℝ)) * ∑ j ∈ J, (u j) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_div_assoc, mul_pow, hr2]
    have ht2 : (q t) ^ 2 ≤ 2 * B ^ 2 + ∑ j ∈ J, (r * (m j : ℝ) / |t - γ j|) ^ 2 := by
      rw [hs]
      have hp := pow_le_pow_left₀ (abs_nonneg (q t)) ht 2
      change |q t| ^ 2 ≤ (B + ∑ j ∈ J, u j) ^ 2 at hp
      rw [sq_abs] at hp
      nlinarith only [hp, hcs, sq_nonneg (B - ∑ j ∈ J, u j)]
    calc
      f t ≤ _ := regularizedLinear_mono hη.le (sq_nonneg _) ht2
      _ ≤ _ := regularizedLinear_add_le hη.le (by positivity) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ ≤ 2 * η * B ^ 2 + ∑ j ∈ J, regularizedLinear η ((r * (m j : ℝ) / |t - γ j|) ^ 2) := by
        apply add_le_add
        · unfold regularizedLinear
          calc
            _ ≤ η * (2 * B ^ 2) := div_le_self (by positivity) (by nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg B)])
            _ = _ := by ring
        · exact regularizedLinear_sum_le J hη.le _ (fun _ ↦ sq_nonneg _)
      _ ≤ _ := add_le_add_right (Finset.sum_le_sum fun j _ ↦
        regularizedLinear_sq_div_le_cauchy η (r * (m j : ℝ)) (γ j) t hη (mul_nonneg hr (m j).coe_nonneg)) _
  have hC : IntegrableOn (fun _ : ℝ ↦ 2 * η * B ^ 2) S := integrableOn_const (by
    simp [S, Real.volume_Icc])
  have hF : IntegrableOn (fun t ↦ 2 * η * B ^ 2 + ∑ j ∈ J, K j t) S := by
    simpa only [Pi.add_def] using hC.add hKsum.integrableOn
  have hm : AEMeasurable f (volume.restrict S) := by
    change AEMeasurable q (volume.restrict S) at hq
    dsimp [f, regularizedLinear]
    fun_prop
  have hfi : IntegrableOn f S := hF.mono' hm.aestronglyMeasurable
    (hmajor.mono fun t ht ↦ by simpa [Real.norm_of_nonneg (hf0 t)] using ht)
  refine ⟨hfi, ?_⟩
  change (∫ t in S, f t) ≤ _
  calc
    _ ≤ ∫ t in S, (2 * η * B ^ 2 + ∑ j ∈ J, K j t) := integral_mono_ae hfi hF hmajor
    _ = 2 * η * B ^ 2 + ∑ j ∈ J, ∫ t in S, K j t := by
      rw [integral_add hC hKsum.integrableOn, integral_finsetSum J (fun j _ ↦ (hKi j).integrableOn)]
      simp [S, measureReal_def, Real.volume_Icc]
    _ ≤ _ := by
      have hb := Finset.sum_le_sum (s := J) (fun j _ ↦ hKiBound j)
      rw [Finset.mul_sum]
      exact add_le_add_right (hb.trans_eq (Finset.sum_congr rfl fun j _ ↦ by ring)) _

/-- For regularization parameters in `(0,1]`, nonnegative data with natural pole
multiplicities give a bound independent of the parameter on every unit interval. -/
theorem integral_regularizedSquare_Icc_le_uniform {ι : Type*} (J : Finset ι)
    (γ : ι → ℝ) (m : ι → ℕ) (a B η : ℝ) (hη : 0 < η) (hη' : η ≤ 1) (q : ℝ → ℝ)
    (hq : AEMeasurable q (volume.restrict (Icc a (a + 1))))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a (a + 1)),
      0 ≤ q t ∧ q t ≤ B + ∑ j ∈ J, (m j : ℝ) / |t - γ j|) :
    ∫ t in Icc a (a + 1), η * (q t) ^ 2 / (1 + η ^ 2 * (q t) ^ 2) ≤
      4 * B ^ 2 + 2 * π * (∑ j ∈ J, (m j : ℝ)) * J.card := by
  have h := integral_regularizedSquare_Icc_le J γ (fun j ↦ (m j : ℝ≥0)) a B η hη q hq
    (hbound.mono fun t ht ↦ by simpa [abs_of_nonneg ht.1] using ht.2)
  have hs : √(2 * (J.card : ℝ)) ≤ 2 * (J.card : ℝ) := by
    apply Real.sqrt_le_self_iff.mpr
    by_cases hn : J.card = 0
    · exact Or.inl (by simp [hn])
    · have hn' : (1 : ℝ) ≤ J.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      exact Or.inr (by linarith)
  have hB : 2 * η * B ^ 2 ≤ 4 * B ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hη') (sq_nonneg B), sq_nonneg B]
  calc
    _ ≤ 2 * η * B ^ 2 + π * √(2 * (J.card : ℝ)) * ∑ j ∈ J, (m j : ℝ) := by simpa using h.2
    _ ≤ 4 * B ^ 2 + π * (2 * (J.card : ℝ)) * ∑ j ∈ J, (m j : ℝ) := by
      apply add_le_add hB
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs Real.pi_pos.le) (by positivity)
    _ = _ := by ring

end RiemannMasullo
