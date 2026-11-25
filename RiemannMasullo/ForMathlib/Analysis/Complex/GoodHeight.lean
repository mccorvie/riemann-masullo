module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import RiemannMasullo.External.Grh.Lemmas.AnalyticGoodHeightDisk
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure

/-!
# Good heights: a lower bound for an entire function on most horizontal lines of a window

Let `f` be entire, bounded by `M` on the circle of radius `6` around `c = x₀ + i (T + 1/2)` and
at least `δ` in modulus at `c`. Then outside a set of heights of small measure in `[T, T + 1]`,
on the whole horizontal segment `x₀ - 5/2 ≤ σ ≤ x₀ + 5/2` the function does not vanish and
`log ‖f (σ + i t)‖` is bounded below by an explicit multiple of `log (M / δ)`
(`exists_goodHeight_log_norm_lower_bound_off_small_set`). In particular some height in the
window is good. This is the classical device for
moving a contour across a horizontal line between the zeros (see Titchmarsh, *The Theory of the
Riemann Zeta-function*). No constant is hidden, so the bounds are uniform in every
parameter on which `f` depends.

The proof divides `f` by the product of its zeros in the disc of radius `5`
(`External.Grh.exists_goodHeight_disk_factorization`: Jensen for the number of factors,
Borel–Carathéodory for the zero-free quotient) and chooses the height by an average over the
window: Markov's inequality for the sum of the logarithmic losses `max 0 (-log |t - γ|)` over
the ordinates `γ` of the zeros.

The statements and proofs are those of the private lemmas
`finiteHeckeL_outside_horizontal_lower_bound_off_small_set_markov`, `…_disk` and `…_generic` of
`RiemannMasullo/AppB_AnalyticNT/Sec6.lean`, made public, with the real part of the center a
parameter and with a bound for the measure of the exceptional set in place of its exact value.

The later sections put the bound in the form that applications use.

* `exists_goodHeight_norm_lower_bound_off_small_set`: the bound as a product,
  `exp (-(8 + 2 B)) * δ * (δ / M) ^ goodHeightExponent B ≤ ‖f (σ + i t)‖`.
* `exists_goodHeight_norm_lower_bound_scaled`: a horizontal segment of any length `5 ρ`, by the
  change of variable `z = ρ u`, with the bound taken on the circle of radius `6 ρ`.
* `exists_goodHeight_norm_lower_bound_of_growth`: with the bound `C * (2 + |T|) ^ G` on the
  circle, the lower bound is `exp (-(8 + 2 B)) * δ * (δ / C) ^ κ * (2 + |T|) ^ (-(κ * G))`,
  `κ = goodHeightExponent B`.

The last section clears finitely many simple poles of a meromorphic function, so that the
statements above apply to it: `exists_entire_eq_prod_sub_mul_of_finite_simple_poles`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

section LogLoss

/-- The logarithmic loss `max 0 (-log |x|)`. This definition and the three lemmas after it are
copied from `RiemannMasullo/AppB_AnalyticNT/Sec6.lean`, where they are private copies of
`Proofs/Lemmas/LogLossGoodHeight.lean` of Neal Patel's `thatnealpatel/grh` (MIT); see
`External/ATTRIBUTION.md`. -/
private noncomputable def goodHeight_logLoss (x : ℝ) : ℝ := max 0 (-Real.log |x|)

private theorem goodHeight_logLoss_nonneg (x : ℝ) : 0 ≤ goodHeight_logLoss x := le_max_left _ _

private theorem goodHeight_logLoss_integrable_and_integral :
    Integrable goodHeight_logLoss ∧ (∫ x, goodHeight_logLoss x) = 2 := by
  -- `Real.log_abs` holds also at zero, where Lean sets `Real.log 0 = 0`.
  have hcut : goodHeight_logLoss = (Icc (-1 : ℝ) 1).indicator (fun x ↦ -Real.log x) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · have hn := Real.log_nonpos (abs_nonneg x) (abs_le.mpr hx)
      rw [indicator_of_mem hx, goodHeight_logLoss, max_eq_right (neg_nonneg.mpr hn),
        Real.log_abs]
    · have hx' : 1 ≤ |x| := le_of_not_gt fun h ↦ hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
      rw [indicator_of_notMem hx, goodHeight_logLoss,
        max_eq_left (neg_nonpos.mpr (Real.log_nonneg hx'))]
  rw [hcut]
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hlog : IntervalIntegrable (fun x ↦ -Real.log x) volume (-1) 1 :=
    (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).neg
  refine ⟨((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hlog).integrable_indicator
    measurableSet_Icc, ?_⟩
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_neg, integral_log]
  norm_num [Real.log_neg_eq_log]

private theorem goodHeight_logLoss_translate (a : ℝ) :
    Integrable (fun t ↦ goodHeight_logLoss (t - a)) ∧ (∫ t, goodHeight_logLoss (t - a)) = 2 := by
  have hp := measurePreserving_sub_right (volume : Measure ℝ) a
  have he : MeasurableEmbedding (fun t : ℝ ↦ t - a) :=
    (Homeomorph.subRight a).isClosedEmbedding.measurableEmbedding
  exact ⟨(hp.integrable_comp_emb he).2 goodHeight_logLoss_integrable_and_integral.1,
    (hp.integral_comp he goodHeight_logLoss).trans goodHeight_logLoss_integrable_and_integral.2⟩

end LogLoss

/-- Markov's inequality for the multiplicity-weighted logarithmic losses of finitely many
ordinates. The integral bound is adapted from Patel's `exists_goodHeight_sum_posLog`. -/
private theorem exists_goodHeight_log_norm_lower_bound_off_small_set_markov
    (A : Finset ℂ) (n : ℂ → ℕ) (T B : ℝ) (hB : 1 < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E ≤ ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, (∀ ρ ∈ A, t ≠ ρ.im) ∧
        ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|) <
          2 * B * (∑ ρ ∈ A, (n ρ : ℝ) + 1) := by
  classical
  set N : ℝ := ∑ ρ ∈ A, (n ρ : ℝ) with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  let I := Icc T (T + 1)
  let F : ℝ → ℝ := fun t ↦ ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|)
  have hB0 : 0 < B := zero_lt_one.trans hB
  set c : ℝ := 2 * B * (N + 1) with hc
  have hc0 : 0 < c := by positivity
  have hFm : Measurable F := by
    refine Finset.measurable_sum _ fun ρ _ ↦ measurable_const.mul ?_
    exact measurable_const.max (Real.measurable_log.comp
      (continuous_abs.measurable.comp (measurable_id.sub_const _))).neg
  have hterm (ρ : ℂ) : Integrable (fun t ↦ (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|))
      (volume.restrict I) :=
    ((goodHeight_logLoss_translate ρ.im).1.const_mul (n ρ : ℝ)).integrableOn
  have hFi : Integrable F (volume.restrict I) := integrable_finsetSum A fun ρ _ ↦ hterm ρ
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦
    Finset.sum_nonneg fun ρ _ ↦ mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
  have hbound : (∫ t in I, F t) ≤ 2 * N := calc
    (∫ t in I, F t) = ∑ ρ ∈ A, ∫ t in I, (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|) :=
      integral_finsetSum A fun ρ _ ↦ hterm ρ
    _ ≤ ∑ ρ ∈ A, (n ρ : ℝ) * 2 := by
      apply Finset.sum_le_sum
      intro ρ _
      rw [integral_const_mul, ← (goodHeight_logLoss_translate ρ.im).2]
      exact mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun t ↦ goodHeight_logLoss_nonneg (t - ρ.im))
          (goodHeight_logLoss_translate ρ.im).1) (Nat.cast_nonneg _)
    _ = 2 * N := by rw [hN, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict I)
    (Eventually.of_forall hF0) hFi c
  let E₁ := I ∩ {t | c ≤ F t}
  let E₂ : Set ℝ := (fun ρ : ℂ ↦ ρ.im) '' (A : Set ℂ)
  have hE₂ : volume E₂ = 0 := ((A.finite_toSet.image _).measure_zero _)
  have hE₁m : MeasurableSet E₁ := measurableSet_Icc.inter (measurableSet_le measurable_const hFm)
  have hE₁ : volume E₁ ≤ ENNReal.ofReal (1 / B) := by
    have hres : volume E₁ = (volume.restrict I) {t | c ≤ F t} := by
      rw [Measure.restrict_apply (measurableSet_le measurable_const hFm), inter_comm]
    have hlt : (volume.restrict I) {t | c ≤ F t} ≠ ⊤ := by
      rw [← hres]
      exact ne_top_of_le_ne_top (measure_Icc_lt_top (a := T) (b := T + 1)).ne
        (measure_mono inter_subset_left)
    rw [hres, ← ENNReal.ofReal_toReal hlt]
    apply ENNReal.ofReal_le_ofReal
    change ((volume.restrict I).real {t | c ≤ F t}) ≤ 1 / B
    have h2 : c * (volume.restrict I).real {t | c ≤ F t} ≤ 2 * N := hmk.trans hbound
    rw [le_div_iff₀ hB0]
    have : (volume.restrict I).real {t | c ≤ F t} ≤ 2 * N / c := by
      rw [le_div_iff₀ hc0]; linarith
    calc (volume.restrict I).real {t | c ≤ F t} * B ≤ 2 * N / c * B := by
          gcongr
      _ ≤ 1 := by
          rw [hc, div_mul_eq_mul_div, div_le_one hc0]
          nlinarith
  refine ⟨E₁ ∪ (I ∩ E₂),
    hE₁m.union (measurableSet_Icc.inter ((A.finite_toSet.image _).measurableSet)),
    union_subset inter_subset_left inter_subset_left,
    (measure_union_le _ _).trans (by
      rw [measure_mono_null inter_subset_right hE₂, add_zero]; exact hE₁),
    fun t ⟨htI, htE⟩ ↦ ⟨fun ρ hρ hteq ↦ ?_, ?_⟩⟩
  · exact htE (Or.inr ⟨htI, ρ, hρ, hteq.symm⟩)
  · by_contra h
    rw [not_lt] at h
    exact htE (Or.inl ⟨htI, h⟩)

/-- Lower bound for `log ‖f‖` on the radius-3 disk off the zero ordinates. -/
private theorem exists_goodHeight_log_norm_lower_bound_off_small_set_disk
    {f : ℂ → ℂ} {c : ℂ} {M δ : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f c‖) (hM : 1 ≤ M) (hbd : ∀ z ∈ Metric.sphere c 6, ‖f z‖ ≤ M) :
    ∃ (A : Finset ℂ) (n : ℂ → ℕ),
      (∑ ρ ∈ A, (n ρ : ℝ)) ≤ Real.log (M / δ) / Real.log (6 / 5 : ℝ) ∧
      ∀ z ∈ Metric.closedBall c 3, (∀ ρ ∈ A, z.im ≠ ρ.im) →
        f z ≠ 0 ∧ Real.log δ - 8 - (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) *
          Real.log (M / δ) - ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |z.im - ρ.im|) ≤
            Real.log ‖f z‖ := by
  have hfc0 : 0 < ‖f c‖ := hδ.trans_le hfc
  obtain ⟨A, n, g, hfac, hN, hg⟩ :=
    External.Grh.exists_goodHeight_disk_factorization hf (norm_pos_iff.mp hfc0) hM hbd
  have hratio : Real.log (M / ‖f c‖) ≤ Real.log (M / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith) hδ hfc)
  have hk1 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hk2 : 0 ≤ 8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ)) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
    positivity
  refine ⟨A, n, hN.trans (div_le_div_of_nonneg_right hratio hk1.le), fun z hz hne ↦ ?_⟩
  obtain ⟨hgz, hgl⟩ := hg z hz
  have hρ (ρ : ℂ) (hρA : ρ ∈ A) : 0 < |z.im - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hne ρ hρA))
  have hρ' (ρ : ℂ) (hρA : ρ ∈ A) : 0 < ‖z - ρ‖ :=
    (hρ ρ hρA).trans_le (by simpa using Complex.abs_im_le_norm (z - ρ))
  have hnorm : ‖f z‖ = (∏ ρ ∈ A, ‖z - ρ‖ ^ n ρ) * ‖g z‖ := by
    rw [hfac z, norm_mul, norm_prod]
    simp only [norm_pow]
  have hprod : 0 < ∏ ρ ∈ A, ‖z - ρ‖ ^ n ρ :=
    Finset.prod_pos fun ρ hρ ↦ pow_pos (hρ' ρ hρ) _
  have hgz0 : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
  refine ⟨norm_pos_iff.mp (hnorm ▸ mul_pos hprod hgz0), ?_⟩
  rw [hnorm, Real.log_mul hprod.ne' hgz0.ne',
    Real.log_prod (fun ρ hρ ↦ (pow_pos (hρ' ρ hρ) _).ne')]
  have hsum : -∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |z.im - ρ.im|) ≤
      ∑ ρ ∈ A, Real.log (‖z - ρ‖ ^ n ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ρ hρA
    rw [Real.log_pow, ← mul_neg]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : Real.log |z.im - ρ.im| ≤ Real.log ‖z - ρ‖ :=
      Real.log_le_log (hρ ρ hρA) (by simpa using Complex.abs_im_le_norm (z - ρ))
    have h2 : -max 0 (-Real.log |z.im - ρ.im|) ≤ Real.log |z.im - ρ.im| := by
      rw [neg_le]; exact le_max_right _ _
    linarith
  have hlogfc : Real.log δ ≤ Real.log ‖f c‖ := Real.log_le_log hδ hfc
  nlinarith [mul_le_mul_of_nonneg_left hratio hk2]

/-- **Good heights, with a small exceptional set.** Let `f` be entire, with `δ ≤ ‖f c‖` at
`c = x₀ + i (T + 1/2)` and `‖f‖ ≤ M` on the circle of radius `6` around `c`. For every `B > 1`
there is a measurable set `E` of heights in `[T, T + 1]`, of measure at most `1 / B`, such that
for every other height `t` in `[T, T + 1]` and every real `σ` within `5/2` of `x₀`, the value
`f (σ + i t)` is not zero and `log ‖f (σ + i t)‖` is at least
`log δ - 8 - (8 + 9 log 5 / log (6/5)) log (M / δ) - 2 B (log (M / δ) / log (6/5) + 1)`. -/
theorem exists_goodHeight_log_norm_lower_bound_off_small_set
    {f : ℂ → ℂ} {x₀ T M δ B : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f ⟨x₀, T + 1 / 2⟩‖) (hM : 1 ≤ M)
    (hbd : ∀ z ∈ Metric.sphere (⟨x₀, T + 1 / 2⟩ : ℂ) 6, ‖f z‖ ≤ M) (hB : 1 < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E ≤ ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (x₀ - 5 / 2) (x₀ + 5 / 2), f ⟨σ, t⟩ ≠ 0 ∧
        Real.log δ - 8 - (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) * Real.log (M / δ) -
          2 * B * (Real.log (M / δ) / Real.log (6 / 5 : ℝ) + 1) ≤ Real.log ‖f ⟨σ, t⟩‖ := by
  obtain ⟨A, n, hN, hlow⟩ :=
    exists_goodHeight_log_norm_lower_bound_off_small_set_disk hf hδ hfc hM hbd
  obtain ⟨E, hEm, hEI, hEv, hgood⟩ :=
    exists_goodHeight_log_norm_lower_bound_off_small_set_markov A n T B hB
  refine ⟨E, hEm, hEI, hEv, fun t ht σ hσ ↦ ?_⟩
  obtain ⟨hne, hsum⟩ := hgood t ht
  have hz : (⟨σ, t⟩ : ℂ) ∈ Metric.closedBall (⟨x₀, T + 1 / 2⟩ : ℂ) 3 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have h1 : |σ - x₀| ≤ 5 / 2 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have h2 : |t - (T + 1 / 2)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
    linarith
  obtain ⟨hfz, hlog⟩ := hlow _ hz hne
  refine ⟨hfz, le_trans ?_ hlog⟩
  have hB0 : 0 < 2 * B := by linarith
  have := mul_le_mul_of_nonneg_left (add_le_add_right hN 1) hB0.le
  linarith

/-! ## The lower bound as a product, with the constants visible -/

/-- The exponent of `δ / M` in the lower bound at a good height, when the exceptional set of
heights has measure at most `ρ / B`. The summand `8 + 9 log 5 / log (6/5)` comes from the
zero-free quotient (Borel–Carathéodory), the summand `2 B / log (6/5)` from the zeros: Jensen
bounds their number in the disc by `log (M / δ) / log (6/5)`, and each costs at most `2 B`. -/
def goodHeightExponent (B : ℝ) : ℝ :=
  8 + 9 * (Real.log 5 / Real.log (6 / 5)) + 2 * B / Real.log (6 / 5)

theorem goodHeightExponent_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ goodHeightExponent B := by
  have h1 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h2 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  unfold goodHeightExponent
  positivity

/-- **Good heights, in product form.** Let `f` be entire, with `δ ≤ ‖f c‖` at
`c = x₀ + i (T + 1/2)` and `‖f‖ ≤ M` on the circle of radius `6` around `c`. For every `B > 1`
there is a measurable set `E` of heights in `[T, T + 1]`, of measure at most `1 / B`, such that
for every other height `t` in `[T, T + 1]` and every real `σ` within `5/2` of `x₀`,
`exp (-(8 + 2 B)) * δ * (δ / M) ^ goodHeightExponent B ≤ ‖f (σ + i t)‖`. -/
theorem exists_goodHeight_norm_lower_bound_off_small_set
    {f : ℂ → ℂ} {x₀ T M δ B : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f ⟨x₀, T + 1 / 2⟩‖) (hM : 1 ≤ M)
    (hbd : ∀ z ∈ Metric.sphere (⟨x₀, T + 1 / 2⟩ : ℂ) 6, ‖f z‖ ≤ M) (hB : 1 < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E ≤ ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (x₀ - 5 / 2) (x₀ + 5 / 2),
        Real.exp (-(8 + 2 * B)) * δ * (δ / M) ^ goodHeightExponent B ≤ ‖f ⟨σ, t⟩‖ := by
  obtain ⟨E, hEm, hEI, hEv, hgood⟩ :=
    exists_goodHeight_log_norm_lower_bound_off_small_set hf hδ hfc hM hbd hB
  refine ⟨E, hEm, hEI, hEv, fun t ht σ hσ ↦ ?_⟩
  obtain ⟨h0, hlog⟩ := hgood t ht σ hσ
  have hfpos : 0 < ‖f ⟨σ, t⟩‖ := norm_pos_iff.mpr h0
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hq : 0 < δ / M := div_pos hδ hM0
  have hlam : Real.log (6 / 5 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogq : Real.log (M / δ) = -Real.log (δ / M) := by rw [← Real.log_inv, inv_div]
  have hpos : 0 < Real.exp (-(8 + 2 * B)) * δ * (δ / M) ^ goodHeightExponent B :=
    mul_pos (mul_pos (Real.exp_pos _) hδ) (Real.rpow_pos_of_pos hq _)
  have hrhs : Real.log (Real.exp (-(8 + 2 * B)) * δ * (δ / M) ^ goodHeightExponent B) =
      Real.log δ - 8 - (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) * Real.log (M / δ) -
        2 * B * (Real.log (M / δ) / Real.log (6 / 5 : ℝ) + 1) := by
    rw [Real.log_mul (mul_pos (Real.exp_pos _) hδ).ne' (Real.rpow_pos_of_pos hq _).ne',
      Real.log_mul (Real.exp_pos _).ne' hδ.ne', Real.log_exp, Real.log_rpow hq, hlogq]
    unfold goodHeightExponent
    field_simp
    ring
  rw [← hrhs] at hlog
  exact (Real.log_le_log_iff hpos hfpos).mp hlog

/-- **Good heights for a segment of any length.** Let `f` be entire and `ρ ≥ 1`, with
`δ ≤ ‖f c‖` at `c = x₀ + i (T + 1/2)` and `‖f‖ ≤ M` on the circle of radius `6 ρ` around `c`.
For every `B > ρ` there is a measurable set `E` of heights in the unit window `[T, T + 1]`, of
measure at most `ρ / B`, such that for every other height `t` of the window and every real `σ`
within `5 ρ / 2` of `x₀`,
`exp (-(8 + 2 B)) * δ * (δ / M) ^ goodHeightExponent B ≤ ‖f (σ + i t)‖`.
The case `ρ = 1` is `exists_goodHeight_norm_lower_bound_off_small_set`; the general case
follows by the change of variable `z = ρ u`. -/
theorem exists_goodHeight_norm_lower_bound_scaled
    {f : ℂ → ℂ} {x₀ T M δ ρ B : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hρ : 1 ≤ ρ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f ⟨x₀, T + 1 / 2⟩‖) (hM : 1 ≤ M)
    (hbd : ∀ z ∈ Metric.sphere (⟨x₀, T + 1 / 2⟩ : ℂ) (6 * ρ), ‖f z‖ ≤ M) (hB : ρ < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E ≤ ENNReal.ofReal (ρ / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (x₀ - 5 / 2 * ρ) (x₀ + 5 / 2 * ρ),
        Real.exp (-(8 + 2 * B)) * δ * (δ / M) ^ goodHeightExponent B ≤ ‖f ⟨σ, t⟩‖ := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  let g : ℂ → ℂ := fun u ↦ f ((ρ : ℂ) * u)
  have hg : AnalyticOnNhd ℂ g univ := fun u _ ↦
    (hf ((ρ : ℂ) * u) (mem_univ _)).comp (analyticAt_const.mul analyticAt_id)
  have hscale (a b : ℝ) : (ρ : ℂ) * (⟨a / ρ, b / ρ⟩ : ℂ) = ⟨a, b⟩ := by
    apply Complex.ext
    · rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      field_simp
    · rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      field_simp
  let T' : ℝ := (T + 1 / 2) / ρ - 1 / 2
  have hcenter : (⟨x₀ / ρ, T' + 1 / 2⟩ : ℂ) = ⟨x₀ / ρ, (T + 1 / 2) / ρ⟩ := by
    simp only [T', sub_add_cancel]
  have hfc' : δ ≤ ‖g ⟨x₀ / ρ, T' + 1 / 2⟩‖ := by
    rw [hcenter]
    change δ ≤ ‖f ((ρ : ℂ) * ⟨x₀ / ρ, (T + 1 / 2) / ρ⟩)‖
    rw [hscale]
    exact hfc
  have hbd' : ∀ u ∈ Metric.sphere (⟨x₀ / ρ, T' + 1 / 2⟩ : ℂ) 6, ‖g u‖ ≤ M := by
    intro u hu
    apply hbd
    rw [mem_sphere_iff_norm] at hu ⊢
    rw [hcenter] at hu
    rw [← hscale x₀ (T + 1 / 2), ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ0.le, hu]
    ring
  obtain ⟨E, hEm, -, hEv, hgood⟩ :=
    exists_goodHeight_norm_lower_bound_off_small_set hg hδ hfc' hM hbd' (hρ.trans_lt hB)
  refine ⟨Icc T (T + 1) ∩ (fun t : ℝ ↦ t * ρ⁻¹) ⁻¹' E,
    measurableSet_Icc.inter ((measurable_id.mul_const _) hEm), inter_subset_left, ?_,
    fun t ht σ hσ ↦ ?_⟩
  · calc volume (Icc T (T + 1) ∩ (fun t : ℝ ↦ t * ρ⁻¹) ⁻¹' E)
        ≤ volume ((fun t : ℝ ↦ t * ρ⁻¹) ⁻¹' E) := measure_mono inter_subset_right
      _ = ENNReal.ofReal |ρ⁻¹⁻¹| * volume E :=
        Real.volume_preimage_mul_right (inv_ne_zero hρ0.ne') E
      _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal (1 / B) := by
        rw [inv_inv, abs_of_pos hρ0]
        gcongr
      _ = ENNReal.ofReal (ρ / B) := by rw [← ENNReal.ofReal_mul hρ0.le, mul_one_div]
  · have htE : t * ρ⁻¹ ∉ E := fun h ↦ ht.2 ⟨ht.1, h⟩
    have htI : t * ρ⁻¹ ∈ Icc T' (T' + 1) := by
      constructor
      · rw [← div_eq_mul_inv, le_div_iff₀ hρ0]
        simp only [T']
        rw [sub_mul, div_mul_cancel₀ _ hρ0.ne']
        linarith [ht.1.1]
      · rw [← div_eq_mul_inv, div_le_iff₀ hρ0]
        simp only [T']
        rw [add_mul, sub_mul, div_mul_cancel₀ _ hρ0.ne']
        linarith [ht.1.2]
    have hσI : σ * ρ⁻¹ ∈ Icc (x₀ / ρ - 5 / 2) (x₀ / ρ + 5 / 2) := by
      constructor
      · rw [← div_eq_mul_inv, le_div_iff₀ hρ0, sub_mul, div_mul_cancel₀ _ hρ0.ne']
        linarith [hσ.1]
      · rw [← div_eq_mul_inv, div_le_iff₀ hρ0, add_mul, div_mul_cancel₀ _ hρ0.ne']
        linarith [hσ.2]
    have h := hgood (t * ρ⁻¹) ⟨htI, htE⟩ (σ * ρ⁻¹) hσI
    have hval : g ⟨σ * ρ⁻¹, t * ρ⁻¹⟩ = f ⟨σ, t⟩ := by
      change f ((ρ : ℂ) * ⟨σ * ρ⁻¹, t * ρ⁻¹⟩) = f ⟨σ, t⟩
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, hscale]
    rwa [hval] at h

/-- **Good heights under a polynomial bound.** In `exists_goodHeight_norm_lower_bound_scaled`,
let the bound on the circle be `C * (2 + |T|) ^ G` with `C ≥ 1` and `G ≥ 0`. Then at every
height `t` of the window outside the exceptional set, and for every `σ` within `5 ρ / 2` of
`x₀`,
`exp (-(8 + 2 B)) * δ * (δ / C) ^ κ * (2 + |T|) ^ (-(κ * G)) ≤ ‖f (σ + i t)‖`
with `κ = goodHeightExponent B`. So the lower bound is polynomial in the height, with the
exponent `κ * G` given by the growth exponent `G`, and the constant by the bound `δ` at the
center and the constant `C` of the growth. -/
theorem exists_goodHeight_norm_lower_bound_of_growth
    {f : ℂ → ℂ} {x₀ T δ ρ B C G : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hρ : 1 ≤ ρ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f ⟨x₀, T + 1 / 2⟩‖) (hC : 1 ≤ C) (hG : 0 ≤ G)
    (hbd : ∀ z ∈ Metric.sphere (⟨x₀, T + 1 / 2⟩ : ℂ) (6 * ρ), ‖f z‖ ≤ C * (2 + |T|) ^ G)
    (hB : ρ < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E ≤ ENNReal.ofReal (ρ / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (x₀ - 5 / 2 * ρ) (x₀ + 5 / 2 * ρ),
        Real.exp (-(8 + 2 * B)) * δ * (δ / C) ^ goodHeightExponent B *
          (2 + |T|) ^ (-(goodHeightExponent B * G)) ≤ ‖f ⟨σ, t⟩‖ := by
  have hu1 : 1 ≤ 2 + |T| := by linarith [abs_nonneg T]
  have hu0 : 0 < 2 + |T| := by linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hM : 1 ≤ C * (2 + |T|) ^ G :=
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hu1 hG)
  obtain ⟨E, hEm, hEI, hEv, hgood⟩ :=
    exists_goodHeight_norm_lower_bound_scaled hf hρ hδ hfc hM hbd hB
  refine ⟨E, hEm, hEI, hEv, fun t ht σ hσ ↦ ?_⟩
  refine le_of_eq_of_le ?_ (hgood t ht σ hσ)
  have hpow : 0 < (2 + |T|) ^ G := Real.rpow_pos_of_pos hu0 _
  rw [show δ / (C * (2 + |T|) ^ G) = δ / C * ((2 + |T|) ^ G)⁻¹ by field_simp,
    Real.mul_rpow (div_pos hδ hC0).le (inv_pos.mpr hpow).le, Real.inv_rpow hpow.le,
    ← Real.rpow_mul hu0.le, ← Real.rpow_neg hu0.le, mul_comm G]
  ring

/-! ## Clearing finitely many simple poles -/

/-- A function in meromorphic normal form on the plane whose poles lie in a finite set `Z` and
are at most simple becomes entire after multiplication by the product of the factors `s - p`,
`p ∈ Z`. The entire function agrees with the product off `Z`. This is the private lemma
`finiteHeckeL_outside_horizontal_lower_bound_off_small_set_entire` of
`RiemannMasullo/AppB_AnalyticNT/Sec6.lean`, for a general function. -/
theorem exists_entire_eq_prod_sub_mul_of_finite_simple_poles {L : ℂ → ℂ}
    (hL : MeromorphicNFOn L univ) (Z : Finset ℂ) (hAway : ∀ s ∉ Z, AnalyticAt ℂ L s)
    (hLower : ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt L s) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f univ ∧ ∀ s ∉ Z, f s = (∏ p ∈ Z, (s - p)) * L s := by
  classical
  let Q : ℂ → ℂ := fun s ↦ ∏ p ∈ Z, (s - p)
  let G : ℂ → ℂ := Q * L
  have hQ : Differentiable ℂ Q := by
    intro s; exact DifferentiableAt.fun_finsetProd fun p _ ↦ differentiableAt_id.sub_const p
  have hG : MeromorphicOn G univ := fun s _ ↦
    (hQ.analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  have hGan (s : ℂ) (hs : s ∉ Z) : AnalyticAt ℂ G s := (hQ.analyticAt s).mul (hAway s hs)
  refine ⟨toMeromorphicNFOn G univ, fun x _ ↦ ?_, fun s hs ↦ ?_⟩
  · apply ((meromorphicNFOn_toMeromorphicNFOn G univ)
      (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hG (mem_univ x)]
    by_cases hx : x ∈ Z
    · let Q' : ℂ → ℂ := fun s ↦ ∏ p ∈ Z.erase x, (s - p)
      have hQ' : Differentiable ℂ Q' := by
        intro s; exact DifferentiableAt.fun_finsetProd fun p _ ↦ differentiableAt_id.sub_const p
      have hGeq : G = (fun s ↦ s - x) * (Q' * L) := by
        funext s
        simp only [G, Q, Q', Pi.mul_apply, ← mul_assoc]
        rw [Finset.mul_prod_erase Z (fun p ↦ s - p) hx]
      rw [hGeq, meromorphicOrderAt_mul (by fun_prop)
          ((hQ'.analyticAt x).meromorphicAt.mul (hL (mem_univ x)).meromorphicAt),
        meromorphicOrderAt_id_sub_const,
        meromorphicOrderAt_mul (hQ'.analyticAt x).meromorphicAt (hL (mem_univ x)).meromorphicAt]
      have h1 := (hQ'.analyticAt x).meromorphicOrderAt_nonneg
      have h3 := hLower x
      have h4 : (0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt L x := by
        have := add_le_add_right h3 (1 : WithTop ℤ)
        exact le_of_eq_of_le (by rfl) this
      calc (0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt L x := h4
        _ ≤ 1 + (meromorphicOrderAt Q' x + meromorphicOrderAt L x) := by
          gcongr
          exact le_add_of_nonneg_left h1
    · exact (hGan x hx).meromorphicOrderAt_nonneg
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hG (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (hGan s hs).meromorphicNFAt]
    rfl

end RiemannMasullo
