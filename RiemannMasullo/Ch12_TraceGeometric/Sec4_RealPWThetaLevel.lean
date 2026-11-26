module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWThetaEvaluation
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWTaylorJets
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Calculus.MeanValue

/-! # The one-prime theta sum on the level of the real-place band

On the whole even weighted band the theta sum `x ↦ ∑ n ≥ 0, f (p ^ n x)` can grow like
`|log x|` as `x → 0` (`exists_realPWBand_thetaEvaluation_bound`): about `|log x| / log p` of its
terms are near `f 0`. On the level, the vectors with `f 0 = 0`, it is bounded uniformly in `x`
(`exists_realPWBand_thetaEvaluation_level_bound`).

The reason is a second-order bound at the origin. A vector of the band is even, so its first
derivative vanishes at zero; if its value vanishes too, then `‖f t‖ ≤ M t ^ 2 ‖f‖` for
`|t| ≤ 1` (`exists_realPWBand_evaluation_sq_bound`). The constant comes from a bound for the
second derivatives on `[-1, 1]`, uniform over the unit ball of the band
(`exists_realPWBand_secondDeriv_bound`), which is the uniform boundedness principle applied to
the functionals `evaluationJet 2 t`. So the terms of the theta sum with `p ^ n x < 1` are
dominated by a geometric series that increases to at most `p / (p - 1)`. -/

public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.Isolated

/-- On the weighted band the second derivatives at the points of `[-1, 1]` are bounded by a
constant times the norm of the vector. The functionals `evaluationJet 2 t` are pointwise bounded
on the compact interval, since each vector is twice continuously differentiable, and the band is
complete. -/
theorem exists_realPWBand_secondDeriv_bound (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : RealPWBand.space Y hμ) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      ‖iteratedDeriv 2 (fun x ↦ RealPWBand.evaluation Y hμ x f) t‖ ≤ M * ‖f‖ := by
  have hpt : ∀ f : RealPWBand.space Y hμ, ∃ C, ∀ i : Icc (-1 : ℝ) 1,
      ‖RealPWBand.evaluationJet Y hμ 2 i.1 f‖ ≤ C := by
    intro f
    have hcont : Continuous (iteratedDeriv 2 (fun x ↦ RealPWBand.evaluation Y hμ x f)) :=
      (RealPWBand.contDiff_evaluation Y hμ f 2).continuous_iteratedDeriv 2 (by exact_mod_cast le_rfl)
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hcont.continuousOn
    exact ⟨C, fun i ↦ by rw [RealPWBand.evaluationJet_apply]; exact hC i.1 i.2⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  refine ⟨max C 0, le_max_right _ _, fun f t ht ↦ ?_⟩
  rw [← RealPWBand.evaluationJet_apply]
  exact ((RealPWBand.evaluationJet Y hμ 2 t).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right ((hC ⟨t, ht⟩).trans (le_max_left _ _)) (norm_nonneg _))

/-- A vector of the even weighted band that vanishes at zero is at most `M t ^ 2 ‖f‖` at every
`t` with `|t| ≤ 1`: its first derivative vanishes at zero by evenness, and its second derivative
is bounded on `[-1, 1]` by `M ‖f‖`. -/
theorem exists_realPWBand_evaluation_sq_bound (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : RealPWBand.space Y hμ, RealPWBand.evaluation Y hμ 0 f = 0 →
      ∀ t : ℝ, |t| ≤ 1 → ‖RealPWBand.evaluation Y hμ t f‖ ≤ M * t ^ 2 * ‖f‖ := by
  obtain ⟨M, hM, hbound⟩ := exists_realPWBand_secondDeriv_bound Y hμ
  refine ⟨M, hM, fun f h0 t ht ↦ ?_⟩
  let g : ℝ → ℂ := fun x ↦ RealPWBand.evaluation Y hμ x f
  have hg : ContDiff ℝ 3 g := RealPWBand.contDiff_evaluation Y hμ f 3
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgdd : Differentiable ℝ (deriv g) := by
    have h := hg.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  have heven : (fun x ↦ g (-x)) = g := funext fun x ↦ RealPWBand.evaluation_even Y hμ f x
  have hd0 : deriv g 0 = 0 := by
    have h1 : deriv (fun x ↦ g (-x)) 0 = -deriv g (-0) := deriv_comp_neg g 0
    rw [heven, neg_zero] at h1
    exact self_eq_neg.mp h1
  have h2nd : ∀ u ∈ Icc (-1 : ℝ) 1, ‖deriv (deriv g) u‖ ≤ M * ‖f‖ := by
    intro u hu
    have h := hbound f u hu
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hd : ∀ u ∈ Icc (-1 : ℝ) 1, ‖deriv g u‖ ≤ M * ‖f‖ * |u| := by
    intro u hu
    have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (f := deriv g)
      (fun x _ ↦ hgdd x) h2nd h0mem hu
    rwa [hd0, sub_zero, sub_zero, Real.norm_eq_abs] at h
  have h := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_deriv_le (f := g)
    (C := M * ‖f‖ * |t|) (fun x _ ↦ hgd x)
    (fun u hu ↦ (hd u ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans
      (mul_le_mul_of_nonneg_left (abs_le.mpr hu) (mul_nonneg hM (norm_nonneg _))))
    (x := 0) (y := t) ⟨by linarith [abs_nonneg t], abs_nonneg t⟩ ⟨neg_abs_le t, le_abs_self t⟩
  have hg0 : g 0 = 0 := h0
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs] at h
  calc ‖g t‖ ≤ M * ‖f‖ * |t| * |t| := h
    _ = M * t ^ 2 * ‖f‖ := by rw [← sq_abs t]; ring

/-- Paper: Theorem 12.4.1.1, pp. 514–517, for one finite prime beside the real place. On the
level of the even weighted band, the vectors that vanish at zero, the theta sum along the powers
of `p` is bounded uniformly: the sum over `n ≥ 0` of the values of `f` at `p ^ n x` is at most
a constant times `‖f‖`, for every `x > 0`.
Reconstruction: The paper does not state this. On the whole band the bound grows like
`|log x|` (`exists_realPWBand_thetaEvaluation_bound`); the condition at zero removes that
growth. The band is the fixed-bandwidth model of #7354. -/
theorem exists_realPWBand_thetaEvaluation_level_bound {Y α s p : ℝ} (hY : 0 ≤ Y) (ha : 0 < α)
    (hs : 0 ≤ s) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs),
        RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) 0 f = 0 →
        ∀ x : ℝ, 0 < x → ∑' n : ℕ, ‖RealPWBand.evaluation Y
          (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x) f‖ ≤ C * ‖f‖ := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let ev := RealPWBand.evaluation Y hμ
  obtain ⟨C₁, hC₁, hθ⟩ := exists_realPWBand_thetaEvaluation_bound (s := s) hY ha hs hp
  obtain ⟨M, hM, hsq⟩ := exists_realPWBand_evaluation_sq_bound Y hμ
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlarge (f : RealPWBand.space Y hμ) (z : ℝ) (hz : 1 ≤ z) :
      ∑' n : ℕ, ‖ev (p ^ n * z) f‖ ≤ C₁ * ‖f‖ := by
    have hz0 : 0 < z := zero_lt_one.trans_le hz
    refine ((hθ f z hz0).2.1 hz).trans ?_
    have hle : z ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC₁) (norm_nonneg f)
    rwa [mul_one] at h
  refine ⟨C₁ + M * (p / (p - 1)), by positivity, fun f h0 x hx ↦ ?_⟩
  have hK : 0 ≤ M * ‖f‖ := mul_nonneg hM (norm_nonneg _)
  rcases le_total 1 x with hx1 | hx1
  · refine (hlarge f x hx1).trans ?_
    nlinarith [mul_nonneg hK (div_pos hp0 hp1).le]
  · let N := ⌈-Real.log x / Real.log p⌉₊
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    have hNge : -Real.log x / Real.log p ≤ N := Nat.le_ceil _
    have hNlt : (N : ℝ) < -Real.log x / Real.log p + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (by linarith) hlogp.le)
    have hzpos : 0 < p ^ N * x := mul_pos (pow_pos hp0 N) hx
    have hlogz : Real.log (p ^ N * x) = N * Real.log p + Real.log x := by
      rw [Real.log_mul (pow_pos hp0 N).ne' hx.ne', Real.log_pow]
    have hz : 1 ≤ p ^ N * x := by
      rw [← Real.log_nonneg_iff hzpos, hlogz]
      have h := (div_le_iff₀ hlogp).mp hNge
      linarith
    have hzp : p ^ N * x < p := by
      rw [← Real.log_lt_log_iff hzpos hp0, hlogz]
      have h := (lt_div_iff₀ hlogp).mp (sub_lt_iff_lt_add.mpr hNlt)
      linarith
    have hsmall (n : ℕ) (hn : n < N) : p ^ n * x < 1 := by
      have hpos : 0 < p ^ n * x := mul_pos (pow_pos hp0 n) hx
      have hn' : (n : ℝ) < -Real.log x / Real.log p := Nat.lt_ceil.mp hn
      have h := (lt_div_iff₀ hlogp).mp hn'
      rw [← Real.log_neg_iff hpos, Real.log_mul (pow_pos hp0 n).ne' hx.ne', Real.log_pow]
      linarith
    have hhead : ∑ n ∈ Finset.range N, ‖ev (p ^ n * x) f‖ ≤ M * (p / (p - 1)) * ‖f‖ := by
      have hterm : ∀ n ∈ Finset.range N, ‖ev (p ^ n * x) f‖ ≤ M * ‖f‖ * (p ^ n * x) := by
        intro n hn
        have hpos : 0 < p ^ n * x := mul_pos (pow_pos hp0 n) hx
        have hlt := hsmall n (Finset.mem_range.mp hn)
        have h := hsq f h0 (p ^ n * x) (by rw [abs_of_pos hpos]; exact hlt.le)
        have hsqle : (p ^ n * x) ^ 2 ≤ p ^ n * x := by nlinarith
        calc ‖ev (p ^ n * x) f‖ ≤ M * (p ^ n * x) ^ 2 * ‖f‖ := h
          _ ≤ M * (p ^ n * x) * ‖f‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqle hM) (norm_nonneg _)
          _ = M * ‖f‖ * (p ^ n * x) := by ring
      have hgeom : (∑ n ∈ Finset.range N, p ^ n) * (p - 1) = p ^ N - 1 := geom_sum_mul p N
      have hsum : ∑ n ∈ Finset.range N, p ^ n * x ≤ p / (p - 1) := by
        rw [← Finset.sum_mul, le_div_iff₀ hp1]
        calc (∑ n ∈ Finset.range N, p ^ n) * x * (p - 1)
            = (p ^ N - 1) * x := by rw [← hgeom]; ring
          _ ≤ p ^ N * x := by nlinarith
          _ ≤ p := hzp.le
      calc ∑ n ∈ Finset.range N, ‖ev (p ^ n * x) f‖
          ≤ ∑ n ∈ Finset.range N, M * ‖f‖ * (p ^ n * x) := Finset.sum_le_sum hterm
        _ = M * ‖f‖ * ∑ n ∈ Finset.range N, p ^ n * x := by rw [Finset.mul_sum]
        _ ≤ M * ‖f‖ * (p / (p - 1)) := mul_le_mul_of_nonneg_left hsum hK
        _ = M * (p / (p - 1)) * ‖f‖ := by ring
    have htail : ∑' n : ℕ, ‖ev (p ^ (n + N) * x) f‖ ≤ C₁ * ‖f‖ := by
      have hre : (fun n : ℕ ↦ ‖ev (p ^ (n + N) * x) f‖) =
          fun n : ℕ ↦ ‖ev (p ^ n * (p ^ N * x)) f‖ := by
        funext n
        rw [pow_add, mul_assoc]
      rw [hre]
      exact hlarge f _ hz
    rw [← Summable.sum_add_tsum_nat_add N (hθ f x hx).1]
    linarith

end RiemannMasullo.Isolated
