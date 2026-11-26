module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWActualCutoffs

/-! # Evaluation of the one-prime theta sum on the real-place band

For one finite prime `p` beside the real place, a test with the unit indicator at `p` is summed
over the powers of `p`: a function `f` on the real line becomes `x ↦ ∑ n ≥ 0, f (p ^ n x)`.
This file bounds that sum, term by term, for `f` in the even weighted band of
`Sec4_RealPWSharpCutoff` at positive strip width `α`
(`exists_realPWBand_thetaEvaluation_bound`): it converges absolutely at every `x > 0`, it is
`O (x ^ (-α) ‖f‖)` for `x ≥ 1`, and it is `O ((1 + |log x|) ‖f‖)` for `x ≤ 1`.

The proof uses two bounds for the evaluation vectors that the band already has: the uniform
bound of the unweighted band, and the bound of the weight times the squared norm at infinity
(`exists_bound_realPWIntervalWeight_mul_eval_norm_sq`). Together they give
`‖e_y‖ ≤ C y ^ (-α)` for every `y > 0` (`exists_realPWBand_evaluationVector_rpow_bound`), so the
terms are dominated by a geometric series with ratio `p ^ (-α)`. For `x ≤ 1` the terms with
`p ^ n x < 1` are counted, about `|log x| / log p` of them, and the rest is a geometric tail.

The same bound makes the evaluation vectors at the points `p ^ n x` summable in norm. Their sum
`E_x` represents the theta sum as a functional on the band
(`exists_realPWBand_thetaEvaluationVector_bound`), and the inner products of these sums are
bounded by a constant times `x ^ (-α) y ^ (-α)` (`exists_realPWBand_thetaKernel_bound`).

No space of theta sums and no operator is introduced here. The width must be positive: at
`α = 0` the ratio of the geometric series is one. -/

public noncomputable section

open Filter MeasureTheory Set
open scoped Topology InnerProductSpace

namespace RiemannMasullo.Isolated

/-- Paper: Definition 10.1.1.1, (10.1.1.5), p. 434. On the even weighted band of the rational
real place, the norm of the evaluation vector at `y > 0` is bounded, and it is at most a
constant times `y ^ (-α)`. For `y ≥ 4` this is the bound of
`exists_bound_realPWIntervalWeight_mul_eval_norm_sq` with the weight replaced by its power
part; for smaller `y` it is the uniform bound of the unweighted band. -/
theorem exists_realPWBand_evaluationVector_rpow_bound {Y α s : ℝ} (hY : 0 ≤ Y) (ha : 0 ≤ α)
    (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) y‖ ≤ C ∧
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) y‖ ≤
        C * y ^ (-α) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_bound_realPWIntervalWeight_mul_eval_norm_sq Y α s hY ha hs
  let e := RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs)
  let C₁ := Real.sqrt (2 * Y)
  have hC₁ : 0 ≤ C₁ := Real.sqrt_nonneg _
  have hS : 0 ≤ Real.sqrt C₀ := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) < 4 ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have h41 : (1 : ℝ) ≤ 4 ^ α := Real.one_le_rpow (by norm_num) ha
  have hC : 0 ≤ C₁ * 4 ^ α + Real.sqrt C₀ := add_nonneg (mul_nonneg hC₁ h4.le) hS
  refine ⟨C₁ * 4 ^ α + Real.sqrt C₀, hC, fun y hy ↦ ?_⟩
  have he1 : ‖e y‖ ≤ C₁ := RealPWBand.norm_evaluationVector_le Y hY _ y
  have hfirst : ‖e y‖ ≤ C₁ * 4 ^ α + Real.sqrt C₀ := by
    have h : C₁ ≤ C₁ * 4 ^ α := le_mul_of_one_le_right hC₁ h41
    linarith
  refine ⟨hfirst, ?_⟩
  have hyα : 0 < y ^ (-α) := Real.rpow_pos_of_pos hy _
  rcases le_total y 1 with hy1 | hy1
  · have h1 : 1 ≤ y ^ (-α) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
    calc ‖e y‖ ≤ (C₁ * 4 ^ α + Real.sqrt C₀) * 1 := by rw [mul_one]; exact hfirst
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hC
  · rcases lt_or_ge y 4 with hy4 | hy4
    · have h : 1 ≤ 4 ^ α * y ^ (-α) := by
        rw [Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hy _),
          one_mul]
        exact Real.rpow_le_rpow hy.le hy4.le ha
      calc ‖e y‖ ≤ C₁ * 1 := by rw [mul_one]; exact he1
        _ ≤ C₁ * (4 ^ α * y ^ (-α)) := mul_le_mul_of_nonneg_left h hC₁
        _ = C₁ * 4 ^ α * y ^ (-α) := by ring
        _ ≤ (C₁ * 4 ^ α + Real.sqrt C₀) * y ^ (-α) :=
          mul_le_mul_of_nonneg_right (by linarith) hyα.le
    · have hw := hbound y (by rw [abs_of_pos hy]; exact hy4)
      have hq : 1 ≤ 1 + Real.log y ^ 2 := by nlinarith [sq_nonneg (Real.log y)]
      have hwy : y ^ (2 * α) ≤ realPWIntervalWeight α s y := by
        rw [realPWIntervalWeight_eq α s hy.ne', abs_of_pos hy]
        calc y ^ (2 * α) = y ^ (2 * α) * 1 := (mul_one _).symm
          _ ≤ max (y ^ (2 * α)) (y ^ (-(2 * α))) * (1 + Real.log y ^ 2) ^ (s / 2) :=
            mul_le_mul (le_max_left _ _) (Real.one_le_rpow hq (by positivity)) zero_le_one
              ((Real.rpow_nonneg hy.le _).trans (le_max_left _ _))
      have hpow : (y ^ α) ^ 2 = y ^ (2 * α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
        congr 1
        push_cast
        ring
      have hsq : (y ^ α * ‖e y‖) ^ 2 ≤ C₀ := by
        rw [mul_pow, hpow]
        exact (mul_le_mul_of_nonneg_right hwy (sq_nonneg _)).trans hw
      have hroot : y ^ α * ‖e y‖ ≤ Real.sqrt C₀ := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
      calc ‖e y‖ = y ^ (-α) * (y ^ α * ‖e y‖) := by
            rw [← mul_assoc, ← Real.rpow_add hy, neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ y ^ (-α) * Real.sqrt C₀ := mul_le_mul_of_nonneg_left hroot hyα.le
        _ = Real.sqrt C₀ * y ^ (-α) := mul_comm _ _
        _ ≤ (C₁ * 4 ^ α + Real.sqrt C₀) * y ^ (-α) :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hC₁ h4.le]) hyα.le

/-- Paper: Theorem 12.4.1.1, pp. 514–517, for one finite prime beside the real place. For a
vector `f` of the even weighted band at positive strip width `α` and a real `p > 1`, the sum
over `n ≥ 0` of the values of `f` at `p ^ n x`, the theta sum of `f` along the powers of `p`,
converges absolutely at every `x > 0`. It is at most a constant times `x ^ (-α) ‖f‖` for
`x ≥ 1`, and at most a constant times `(1 + |log x|) ‖f‖` for `x ≤ 1`.
Reconstruction: The paper does not state this. The band is the fixed-bandwidth model of
#7354. The theta sum is written here term by term, and no space of such sums is introduced. -/
theorem exists_realPWBand_thetaEvaluation_bound {Y α s p : ℝ} (hY : 0 ≤ Y) (ha : 0 < α)
    (hs : 0 ≤ s) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) (x : ℝ), 0 < x →
        Summable (fun n : ℕ ↦ ‖RealPWBand.evaluation Y
          (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x) f‖) ∧
        (1 ≤ x → ∑' n : ℕ, ‖RealPWBand.evaluation Y
          (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x) f‖ ≤ C * x ^ (-α) * ‖f‖) ∧
        (x ≤ 1 → ∑' n : ℕ, ‖RealPWBand.evaluation Y
          (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x) f‖ ≤
            C * (1 + |Real.log x|) * ‖f‖) := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ
  let ev := RealPWBand.evaluation Y hμ
  obtain ⟨C₂, hC₂, hκ⟩ := exists_realPWBand_evaluationVector_rpow_bound (s := s) hY ha.le hs
  have hp0 : 0 < p := zero_lt_one.trans hp
  let ρ := p ^ (-α)
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hp0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hA : 0 ≤ (1 - ρ)⁻¹ := (inv_pos.mpr h1ρ).le
  have hB : 0 ≤ (Real.log p)⁻¹ := (inv_pos.mpr hlogp).le
  have hev (y : ℝ) (f : RealPWBand.space Y hμ) : ‖ev y f‖ ≤ ‖e y‖ * ‖f‖ := by
    have hn : ‖RealPWBand.evaluation Y hμ y‖ = ‖RealPWBand.evaluationVector Y hμ y‖ := by
      rw [← RealPWBand.toDual_evaluationVector Y hμ y, LinearIsometryEquiv.norm_map]
    exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [hn])
  have hpow (n : ℕ) (x : ℝ) (hx : 0 < x) : (p ^ n * x) ^ (-α) = ρ ^ n * x ^ (-α) := by
    rw [Real.mul_rpow (pow_nonneg hp0.le n) hx.le, ← Real.rpow_natCast p n,
      ← Real.rpow_mul hp0.le, mul_comm (n : ℝ) (-α), Real.rpow_mul hp0.le, Real.rpow_natCast]
  have hterm (f : RealPWBand.space Y hμ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
      ‖ev (p ^ n * x) f‖ ≤ C₂ * x ^ (-α) * ‖f‖ * ρ ^ n := by
    have hy : 0 < p ^ n * x := mul_pos (pow_pos hp0 n) hx
    calc ‖ev (p ^ n * x) f‖ ≤ ‖e (p ^ n * x)‖ * ‖f‖ := hev _ f
      _ ≤ C₂ * (p ^ n * x) ^ (-α) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (hκ _ hy).2 (norm_nonneg _)
      _ = C₂ * x ^ (-α) * ‖f‖ * ρ ^ n := by rw [hpow n x hx]; ring
  have hgeo (c : ℝ) : Summable (fun n : ℕ ↦ c * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left c
  have hsum (f : RealPWBand.space Y hμ) (x : ℝ) (hx : 0 < x) :
      Summable (fun n : ℕ ↦ ‖ev (p ^ n * x) f‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ hterm f n x hx) (hgeo _)
  have htsum (f : RealPWBand.space Y hμ) (x : ℝ) (hx : 0 < x) :
      ∑' n : ℕ, ‖ev (p ^ n * x) f‖ ≤ C₂ * x ^ (-α) * ‖f‖ * (1 - ρ)⁻¹ := by
    have h := Summable.tsum_le_tsum (fun n ↦ hterm f n x hx) (hsum f x hx) (hgeo _)
    rwa [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1] at h
  refine ⟨C₂ * ((1 - ρ)⁻¹ + 1 + (Real.log p)⁻¹), by positivity, fun f x hx ↦
    ⟨hsum f x hx, fun _ ↦ ?_, fun hx1 ↦ ?_⟩⟩
  · refine (htsum f x hx).trans ?_
    have hxα : 0 ≤ x ^ (-α) := (Real.rpow_pos_of_pos hx _).le
    have hre : C₂ * x ^ (-α) * ‖f‖ * (1 - ρ)⁻¹ = C₂ * (1 - ρ)⁻¹ * x ^ (-α) * ‖f‖ := by ring
    rw [hre]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hC₂) hxα) (norm_nonneg _)
  · let N := ⌈-Real.log x / Real.log p⌉₊
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    have hNge : -Real.log x / Real.log p ≤ N := Nat.le_ceil _
    have hNle : (N : ℝ) < -Real.log x / Real.log p + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (by linarith) hlogp.le)
    have hz : 1 ≤ p ^ N * x := by
      have hpos : 0 < p ^ N * x := mul_pos (pow_pos hp0 N) hx
      rw [← Real.log_nonneg_iff hpos, Real.log_mul (pow_pos hp0 N).ne' hx.ne', Real.log_pow]
      have h := (div_le_iff₀ hlogp).mp hNge
      linarith
    have hz0 : 0 < p ^ N * x := lt_of_lt_of_le zero_lt_one hz
    have hhead : ∑ n ∈ Finset.range N, ‖ev (p ^ n * x) f‖ ≤ N * (C₂ * ‖f‖) := by
      calc ∑ n ∈ Finset.range N, ‖ev (p ^ n * x) f‖
          ≤ ∑ _n ∈ Finset.range N, C₂ * ‖f‖ := Finset.sum_le_sum fun n _ ↦
            (hev _ f).trans (mul_le_mul_of_nonneg_right
              (hκ _ (mul_pos (pow_pos hp0 n) hx)).1 (norm_nonneg _))
        _ = N * (C₂ * ‖f‖) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have htail : ∑' n : ℕ, ‖ev (p ^ (n + N) * x) f‖ ≤ C₂ * ‖f‖ * (1 - ρ)⁻¹ := by
      have hre : (fun n : ℕ ↦ ‖ev (p ^ (n + N) * x) f‖) =
          fun n : ℕ ↦ ‖ev (p ^ n * (p ^ N * x)) f‖ := by
        funext n
        rw [pow_add, mul_assoc]
      rw [hre]
      refine (htsum f _ hz0).trans ?_
      have hle : (p ^ N * x) ^ (-α) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle hC₂) (norm_nonneg f)) hA
      rwa [mul_one] at h
    rw [← Summable.sum_add_tsum_nat_add N (hsum f x hx)]
    have hK : 0 ≤ C₂ * ‖f‖ := mul_nonneg hC₂ (norm_nonneg _)
    have hL : 0 ≤ |Real.log x| := abs_nonneg _
    have habs : |Real.log x| = -Real.log x := abs_of_nonpos hlogx
    have hN' : (N : ℝ) ≤ |Real.log x| * (Real.log p)⁻¹ + 1 := by
      rw [habs, ← div_eq_mul_inv]
      exact hNle.le
    have h1 : N * (C₂ * ‖f‖) ≤ (|Real.log x| * (Real.log p)⁻¹ + 1) * (C₂ * ‖f‖) :=
      mul_le_mul_of_nonneg_right hN' hK
    nlinarith [hhead, htail, h1, mul_nonneg hK hA, mul_nonneg (mul_nonneg hK hA) hL,
      mul_nonneg hK hL, mul_nonneg hK hB, mul_nonneg (mul_nonneg hK hL) hB]

/-- Paper: Theorem 12.4.1.1, pp. 514–517, for one finite prime beside the real place. At positive
strip width, the evaluation vectors of the even weighted band at the points `p ^ n x`, `n ≥ 0`,
are summable in norm. Their sum `E_x` has norm at most a constant times `x ^ (-α)`, and it
represents the theta sum: the values of `f` at the points `p ^ n x` sum to the inner product of
`E_x` with `f`.
Reconstruction: The paper does not state this. The band is the fixed-bandwidth model of
#7354. -/
theorem exists_realPWBand_thetaEvaluationVector_bound {Y α s p : ℝ} (hY : 0 ≤ Y) (ha : 0 < α)
    (hs : 0 ≤ s) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      Summable (fun n : ℕ ↦ ‖RealPWBand.evaluationVector Y
        (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x)‖) ∧
      ‖∑' n : ℕ, RealPWBand.evaluationVector Y
        (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x)‖ ≤ C * x ^ (-α) ∧
      ∀ f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs),
        HasSum (fun n : ℕ ↦ RealPWBand.evaluation Y
            (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x) f)
          ⟪∑' n : ℕ, RealPWBand.evaluationVector Y
            (volume_le_realPWIntervalMeasure α s hs) (p ^ n * x), f⟫_ℂ := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ
  obtain ⟨C₂, hC₂, hκ⟩ := exists_realPWBand_evaluationVector_rpow_bound (s := s) hY ha.le hs
  have hp0 : 0 < p := zero_lt_one.trans hp
  let ρ := p ^ (-α)
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hp0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hA : 0 ≤ (1 - ρ)⁻¹ := (inv_pos.mpr (sub_pos.mpr hρ1)).le
  have hpow (n : ℕ) (x : ℝ) (hx : 0 < x) : (p ^ n * x) ^ (-α) = ρ ^ n * x ^ (-α) := by
    rw [Real.mul_rpow (pow_nonneg hp0.le n) hx.le, ← Real.rpow_natCast p n,
      ← Real.rpow_mul hp0.le, mul_comm (n : ℝ) (-α), Real.rpow_mul hp0.le, Real.rpow_natCast]
  have hterm (n : ℕ) (x : ℝ) (hx : 0 < x) : ‖e (p ^ n * x)‖ ≤ C₂ * x ^ (-α) * ρ ^ n := by
    have hy : 0 < p ^ n * x := mul_pos (pow_pos hp0 n) hx
    calc ‖e (p ^ n * x)‖ ≤ C₂ * (p ^ n * x) ^ (-α) := (hκ _ hy).2
      _ = C₂ * x ^ (-α) * ρ ^ n := by rw [hpow n x hx]; ring
  have hgeo (c : ℝ) : Summable (fun n : ℕ ↦ c * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left c
  refine ⟨C₂ * (1 - ρ)⁻¹, mul_nonneg hC₂ hA, fun x hx ↦ ?_⟩
  have hnorm : Summable (fun n : ℕ ↦ ‖e (p ^ n * x)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ hterm n x hx) (hgeo _)
  have hS : Summable (fun n : ℕ ↦ e (p ^ n * x)) := hnorm.of_norm
  refine ⟨hnorm, ?_, fun f ↦ ?_⟩
  · calc ‖∑' n : ℕ, e (p ^ n * x)‖ ≤ ∑' n : ℕ, ‖e (p ^ n * x)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : ℕ, C₂ * x ^ (-α) * ρ ^ n :=
        Summable.tsum_le_tsum (fun n ↦ hterm n x hx) hnorm (hgeo _)
      _ = C₂ * (1 - ρ)⁻¹ * x ^ (-α) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1]
        ring
  · have h1 : HasSum (fun n : ℕ ↦ ⟪f, e (p ^ n * x)⟫_ℂ) ⟪f, ∑' n : ℕ, e (p ^ n * x)⟫_ℂ := by
      simpa using hS.hasSum.mapL (innerSL ℂ f)
    have h2 := h1.star
    have hterm' (n : ℕ) : RealPWBand.evaluation Y hμ (p ^ n * x) f =
        star ⟪f, e (p ^ n * x)⟫_ℂ := by
      rw [← RealPWBand.toDual_evaluationVector Y hμ (p ^ n * x),
        InnerProductSpace.toDual_apply_apply]
      exact (inner_conj_symm _ _).symm
    have hlim : ⟪∑' n : ℕ, e (p ^ n * x), f⟫_ℂ = star ⟪f, ∑' n : ℕ, e (p ^ n * x)⟫_ℂ :=
      (inner_conj_symm _ _).symm
    rw [hlim]
    exact h2.congr_fun fun n ↦ hterm' n

/-- Paper: Theorem 12.4.1.1, pp. 514–517, for one finite prime beside the real place. The kernel
of the theta sums of the evaluation vectors, the inner product of `E_y` with `E_x`, is at most a
constant times `x ^ (-α) y ^ (-α)`. In particular it is bounded on every set of pairs bounded
away from zero.
Reconstruction: The paper does not state this. It is the reproducing kernel of the image of the
band under the theta sum when that image carries the norm of the band; no such space is
introduced here. -/
theorem exists_realPWBand_thetaKernel_bound {Y α s p : ℝ} (hY : 0 ≤ Y) (ha : 0 < α)
    (hs : 0 ≤ s) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 0 < x → 0 < y →
      ‖⟪∑' n : ℕ, RealPWBand.evaluationVector Y
          (volume_le_realPWIntervalMeasure α s hs) (p ^ n * y),
        ∑' m : ℕ, RealPWBand.evaluationVector Y
          (volume_le_realPWIntervalMeasure α s hs) (p ^ m * x)⟫_ℂ‖ ≤
        C * x ^ (-α) * y ^ (-α) := by
  obtain ⟨C, hC, h⟩ := exists_realPWBand_thetaEvaluationVector_bound (s := s) hY ha hs hp
  refine ⟨C * C, mul_nonneg hC hC, fun x y hx hy ↦ ?_⟩
  have hx' := (h x hx).2.1
  have hy' := (h y hy).2.1
  have hxα : 0 ≤ x ^ (-α) := (Real.rpow_pos_of_pos hx _).le
  have hyα : 0 ≤ y ^ (-α) := (Real.rpow_pos_of_pos hy _).le
  refine (norm_inner_le_norm _ _).trans ?_
  calc _ ≤ (C * y ^ (-α)) * (C * x ^ (-α)) :=
        mul_le_mul hy' hx' (norm_nonneg _) (mul_nonneg hC hyα)
    _ = C * C * x ^ (-α) * y ^ (-α) := by ring

end RiemannMasullo.Isolated
