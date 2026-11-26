module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Mellin quadrature on consecutive prime intervals

When the continuous prime density on each interval between primes is moved to its left endpoint,
the Mellin transform changes by a holomorphic correction controlled by the second moment of
the gaps. This isolates the quadrature error from the signed first-prime discrepancy in the
rational case of Theorem 12.5.1.1, pp. 519–520.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace RiemannMasullo

/-- The error from moving Lebesgue measure on a cell to its left endpoint for a Mellin test. -/
def mellinLeftCellError (a b : ℝ) (z : ℂ) : ℂ :=
  (b - a : ℝ) * (a : ℂ) ^ (-z) - ∫ u : ℝ in a..b, (u : ℂ) ^ (-z)

/-- The error of one cell is bounded by its squared length times a derivative bound. -/
theorem norm_mellinLeftCellError_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {z : ℂ} (hz : 0 < z.re) :
    ‖mellinLeftCellError a b z‖ ≤ ‖z‖ * a ^ (-z.re - 1) * (b - a) ^ 2 / 2 := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :=
    hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne'
      (r := -z) (neg_ne_zero.mpr (fun h ↦ by simp [h] at hz))
  have hc : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (-z)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  have hdBound (x : ℝ) (hx : x ∈ Ico a b) :
      ‖-z * (x : ℂ) ^ (-z - 1)‖ ≤ ‖z‖ * a ^ (-z.re - 1) := by
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith))
      (norm_nonneg _)
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx ↦ (hd x hx).hasDerivWithinAt) hdBound
  rw [mellinLeftCellError, ← Complex.real_smul, ← intervalIntegral.integral_const,
    ← intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable)]
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  calc
    _ ≤ ∫ x in a..b, (‖z‖ * a ^ (-z.re - 1)) * (x - a) := by
      apply intervalIntegral.integral_mono_on hab
        ((continuousOn_const.sub hc).norm.intervalIntegrable)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      intro x hx
      simpa only [Pi.sub_apply, norm_sub_rev ((a : ℂ) ^ (-z))] using hseg x hx
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        ((show Continuous (fun x : ℝ ↦ x) from continuous_id).intervalIntegrable _ _) (g := fun _ : ℝ ↦ a) intervalIntegrable_const, integral_id,
        intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- Each individual cell has an entire Mellin correction, including at the density pole. -/
theorem differentiable_mellinLeftCellError {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Differentiable ℂ (mellinLeftCellError a b) := by
  let g (x : ℝ) : ℂ := -(Real.log (max a x) : ℝ)
  have hg : Continuous g := by
    exact (Complex.continuous_ofReal.comp ((continuous_const.max continuous_id).log
      (fun x ↦ (ha.trans_le (le_max_left a x)).ne'))).neg
  have he (z : ℂ) (x : ℝ) (hx : x ∈ uIcc a b) :
      (x : ℂ) ^ (-z) = exp (z * g x) := by
    rw [uIcc_of_le hab] at hx
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ha.trans_le hx.1).ne'),
      ← ofReal_log (ha.trans_le hx.1).le]
    dsimp [g]
    rw [max_eq_right hx.1]
    congr 1
    ring
  have hd (z : ℂ) (x : ℝ) :
      HasDerivAt (fun w : ℂ ↦ exp (w * g x)) (exp (z * g x) * g x) z := by
    simpa using ((hasDerivAt_id z).mul_const (g x)).cexp
  intro z
  apply DifferentiableAt.sub
  · exact (differentiableAt_id.neg.const_cpow (.inl (ofReal_ne_zero.mpr ha.ne'))).const_mul _
  · have heq : (fun w : ℂ ↦ ∫ x : ℝ in a..b, (x : ℂ) ^ (-w)) =
        (fun w : ℂ ↦ ∫ x : ℝ in a..b, exp (w * g x)) :=
      funext fun w ↦ intervalIntegral.integral_congr (he w)
    rw [heq]
    apply HasFDerivAt.differentiableAt
    apply intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv
      (u := univ) (𝕜 := ℂ) (μ := volume) univ_mem
    · change ContinuousOn (fun p : ℂ × ℝ ↦ exp (p.1 * g p.2)) _
      exact (continuous_fst.mul (hg.comp continuous_snd)).cexp.continuousOn
    · exact fun x _ w _ ↦ (hd w x).differentiableAt.differentiableWithinAt
    · simp_rw [(hd _ _).hasFDerivAt.fderiv]
      exact ((ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp
        ((continuous_fst.mul (hg.comp continuous_snd)).cexp.mul (hg.comp continuous_snd))).continuousOn

private theorem norm_mellinLeftCellError_le_majorant {a b σ C : ℝ} (ha : 1 ≤ a)
    (hab : a ≤ b) {z : ℂ} (hz : 0 < z.re) (hσ : σ ≤ z.re) (hC : ‖z‖ ≤ C) :
    ‖mellinLeftCellError a b z‖ ≤ C / 2 * ((b - a) ^ 2 * a ^ (-σ - 1)) := by
  apply (norm_mellinLeftCellError_le (zero_lt_one.trans_le ha) hab hz).trans
  have hp := Real.rpow_le_rpow_of_exponent_le ha (show -z.re - 1 ≤ -σ - 1 by linarith)
  have h := mul_le_mul hC hp (Real.rpow_nonneg (zero_le_one.trans ha) _)
    ((norm_nonneg _).trans hC)
  nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg (b - a))]

/-- A finite weighted second gap moment gives absolute convergence of the Mellin correction. -/
theorem summable_mellinLeftCellError_of_gapMoment {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ i, 1 ≤ a i) (hab : ∀ i, a i ≤ b i) {σ : ℝ}
    (hm : Summable fun i ↦ (b i - a i) ^ 2 * (a i) ^ (-σ - 1))
    {z : ℂ} (hz : 0 < z.re) (hσ : σ ≤ z.re) :
    Summable fun i ↦ mellinLeftCellError (a i) (b i) z :=
  Summable.of_norm_bounded (hm.mul_left (‖z‖ / 2)) fun i ↦
    norm_mellinLeftCellError_le_majorant (ha i) (hab i) hz hσ le_rfl

/-- The correction is holomorphic throughout the open half-plane of the gap moment. -/
theorem differentiableOn_tsum_mellinLeftCellError_of_gapMoment {ι : Type*}
    {a b : ι → ℝ} (ha : ∀ i, 1 ≤ a i) (hab : ∀ i, a i ≤ b i)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hm : Summable fun i ↦ (b i - a i) ^ 2 * (a i) ^ (-σ - 1)) :
    DifferentiableOn ℂ (fun z ↦ ∑' i, mellinLeftCellError (a i) (b i) z)
      {z : ℂ | σ < z.re} := by
  intro z hz
  let U := {w : ℂ | σ < w.re} ∩ {w : ℂ | ‖w‖ < ‖z‖ + 1}
  have ho : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hmem : z ∈ U := ⟨hz, by exact lt_add_of_pos_right _ zero_lt_one⟩
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableOn.differentiableAt _ (ho.mem_nhds hmem)
  refine Complex.differentiableOn_tsum_of_summable_norm (hm.mul_left ((‖z‖ + 1) / 2))
    (fun i ↦ (differentiable_mellinLeftCellError (zero_lt_one.trans_le (ha i))
      (hab i)).differentiableOn) ho ?_
  intro i w hw
  exact norm_mellinLeftCellError_le_majorant (ha i) (hab i) (hσ.trans_lt hw.1) hw.1.le hw.2.le

/-- Real endpoints of the consecutive-prime partition, starting at two. -/
def nthPrimeReal (n : ℕ) : ℝ := Nat.nth Nat.Prime n

private theorem nthPrimeReal_mono : Monotone nthPrimeReal := by
  intro i j hij
  unfold nthPrimeReal
  exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hij

private theorem two_le_nthPrimeReal (n : ℕ) : 2 ≤ nthPrimeReal n := by
  unfold nthPrimeReal
  exact_mod_cast (Nat.prime_nth_prime n).two_le

private theorem nthPrimeReal_succ_le_double (n : ℕ) : nthPrimeReal (n + 1) ≤ 2 * nthPrimeReal n := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ (Nat.prime_nth_prime n).ne_zero
  unfold nthPrimeReal
  exact_mod_cast ((Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hq).2 hlt).trans hle

private theorem hasSum_primeCellIntegrals {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : IntegrableOn f (Ioi 2)) :
    HasSum (fun n ↦ ∫ u in nthPrimeReal n..nthPrimeReal (n + 1), f u) (∫ u in Ioi 2, f u) := by
  have hu : ¬ BddAbove (range nthPrimeReal) := by
    intro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have hg : (n : ℝ) ≤ nthPrimeReal n := by
      unfold nthPrimeReal
      exact_mod_cast (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)
    exact (hn.trans_le hg).not_ge (hB (mem_range_self n))
  have hUnion : (⋃ n, Ioc (nthPrimeReal n) (nthPrimeReal (n + 1))) = Ioi 2 := by
    simpa [nthPrimeReal, Nat.nth_prime_zero_eq_two] using
      iUnion_Ioc_map_succ_eq_Ioi (fun n ↦ nthPrimeReal_mono (Nat.zero_le n)) hu
  have hs := hasSum_integral_iUnion (μ := volume) (f := f)
    (fun n ↦ measurableSet_Ioc (a := nthPrimeReal n) (b := nthPrimeReal (n + 1)))
    nthPrimeReal_mono.pairwise_disjoint_on_Ioc_succ (hUnion ▸ hf)
  simpa only [hUnion, intervalIntegral.integral_of_le (nthPrimeReal_mono (Nat.le_succ _))] using hs

/-- Bertrand's postulate already gives a finite weighted second gap moment to the right of one. -/
theorem summable_primeGapMoment_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n ↦ (nthPrimeReal (n + 1) - nthPrimeReal n) ^ 2 * (nthPrimeReal n) ^ (-σ - 1) := by
  have hI := (hasSum_primeCellIntegrals
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0 : ℝ) < 2))).summable
  apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (by linarith [two_le_nthPrimeReal n]) _)) _ (hI.mul_left ((2 : ℝ) ^ σ))
  intro n
  let p := nthPrimeReal n
  let q := nthPrimeReal (n + 1)
  have hp : 0 < p := (by norm_num : (0 : ℝ) < 2).trans_le (two_le_nthPrimeReal n)
  have hpq : p ≤ q := nthPrimeReal_mono (Nat.le_succ n)
  have hq : q ≤ 2 * p := nthPrimeReal_succ_le_double n
  have hc : IntervalIntegrable (fun u : ℝ ↦ u ^ (-σ)) volume p q := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact fun x hx ↦ (Real.continuousAt_rpow_const x (-σ)
      (Or.inl (hp.trans_le hx.1).ne')).continuousWithinAt
  have hlow : (q - p) * ((2 * p) ^ (-σ)) ≤ ∫ u in p..q, u ^ (-σ) := by
    rw [← smul_eq_mul, ← intervalIntegral.integral_const]
    exact intervalIntegral.integral_mono_on hpq intervalIntegrable_const hc fun x hx ↦
      Real.rpow_le_rpow_of_nonpos (hp.trans_le hx.1) (hx.2.trans hq) (by linarith)
  have hweight : (2 : ℝ) ^ σ * (2 * p) ^ (-σ) = p ^ (-σ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp.le, ← mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero, one_mul]
  have hpower : p * p ^ (-σ - 1) = p ^ (-σ) := by
    nth_rw 1 [← Real.rpow_one p]
    rw [← Real.rpow_add hp]
    congr 1
    ring
  change (q - p) ^ 2 * p ^ (-σ - 1) ≤ (2 : ℝ) ^ σ * ∫ u in p..q, u ^ (-σ)
  calc
    _ ≤ ((q - p) * p) * p ^ (-σ - 1) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hpq)
    _ = (2 : ℝ) ^ σ * ((q - p) * (2 * p) ^ (-σ)) := by
      rw [mul_assoc, hpower, mul_left_comm, hweight]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (by norm_num) _)

/-- To the right of one the prime-gap Dirichlet series is the elementary pole plus the
summable cell correction. -/
theorem hasSum_primeGap_cpow {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun n ↦ ((nthPrimeReal (n + 1) - nthPrimeReal n : ℝ) : ℂ) * (nthPrimeReal n : ℂ) ^ (-z))
      ((2 : ℂ) ^ (1 - z) / (z - 1) + ∑' n, mellinLeftCellError (nthPrimeReal n) (nthPrimeReal (n + 1)) z) := by
  have hleft := summable_mellinLeftCellError_of_gapMoment
    (fun n ↦ (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_nthPrimeReal n))
    (fun n ↦ nthPrimeReal_mono (Nat.le_succ n)) (summable_primeGapMoment_of_one_lt hz)
    (z := z) (by linarith) le_rfl
  have hz' : (-z).re < -1 := by simpa only [neg_re] using neg_lt_neg hz
  have hmain := hasSum_primeCellIntegrals (integrableOn_Ioi_cpow_of_lt hz' (by norm_num : (0 : ℝ) < 2))
  rw [integral_Ioi_cpow_of_lt hz' (by norm_num : (0 : ℝ) < 2)] at hmain
  have hval : -(2 : ℂ) ^ (-z + 1) / (-z + 1) = (2 : ℂ) ^ (1 - z) / (z - 1) := by
    rw [show -z + 1 = 1 - z by ring, show z - 1 = -(1 - z) by ring, div_neg, neg_div]
  convert hmain.add hleft.hasSum using 1
  · ext n
    simp [mellinLeftCellError]
  · simp only [ofReal_ofNat, hval]

/-- A weighted second-moment estimate for the true consecutive prime gaps continues their
Dirichlet series after removal of the density pole. The continuation is regular at one if
the moment is available at any smaller nonnegative exponent. -/
theorem exists_holomorphic_primeGapCorrection {σ : ℝ} (hσ : 0 ≤ σ)
    (hm : Summable fun n ↦ (nthPrimeReal (n + 1) - nthPrimeReal n) ^ 2 * (nthPrimeReal n) ^ (-σ - 1)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z : ℂ | σ < z.re} ∧ ∀ z : ℂ, 1 < z.re →
      HasSum (fun n ↦ ((nthPrimeReal (n + 1) - nthPrimeReal n : ℝ) : ℂ) * (nthPrimeReal n : ℂ) ^ (-z))
        ((2 : ℂ) ^ (1 - z) / (z - 1) + G z) := by
  exact ⟨_, differentiableOn_tsum_mellinLeftCellError_of_gapMoment
    (fun n ↦ (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_nthPrimeReal n))
    (fun n ↦ nthPrimeReal_mono (Nat.le_succ n)) hσ hm, fun _ hz ↦ hasSum_primeGap_cpow hz⟩

/-- A dyadic sum of squared prime gaps of order `X ^ A` gives the weighted moment at every
`σ ≥ 0` with `A < σ + 1`. The dyadic index is the base-two logarithm rounded down. -/
theorem summable_primeGapMoment_of_dyadic_bound {A σ C : ℝ} (hσ : 0 ≤ σ) (hA : A < σ + 1)
    (h : ∀ k : ℕ, (∑' n : {i : ℕ // Nat.log 2 (Nat.nth Nat.Prime i) = k},
      (nthPrimeReal (n.1 + 1) - nthPrimeReal n.1) ^ 2) ≤ C * ((2 : ℝ) ^ k) ^ A) :
    Summable fun n ↦ (nthPrimeReal (n + 1) - nthPrimeReal n) ^ 2 * (nthPrimeReal n) ^ (-σ - 1) := by
  let shell (n : ℕ) := Nat.log 2 (Nat.nth Nat.Prime n)
  have hfinite (k : ℕ) : Finite {i : ℕ // shell i = k} := by
    apply Set.Finite.to_subtype (s := {i : ℕ | shell i = k})
    refine (finite_Iio (2 ^ (k + 1))).subset ?_
    intro n hn
    have hbound := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Nat.nth Nat.Prime n)
    change shell n = k at hn
    change Nat.nth Nat.Prime n < 2 ^ (shell n + 1) at hbound
    rw [hn] at hbound
    exact ((Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)).trans_lt hbound
  have hpos (n : ℕ) : 0 ≤ nthPrimeReal n := (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_nthPrimeReal n)
  rw [← (Equiv.sigmaFiberEquiv shell).summable_iff]
  refine (summable_sigma_of_nonneg (fun i ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hpos _) _))).2
    ⟨fun k ↦ by
      let _ := hfinite k
      exact Summable.of_finite, ?_⟩
  have hgeom := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (A - σ - 1))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  apply Summable.of_nonneg_of_le (fun k ↦ tsum_nonneg fun i ↦
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hpos _) _)) _ (hgeom.mul_left C)
  intro k
  let _ := hfinite k
  let X : ℝ := 2 ^ k
  have hX : 0 < X := pow_pos (by norm_num) _
  let G (n : {i // shell i = k}) : ℝ := (nthPrimeReal (n.1 + 1) - nthPrimeReal n.1) ^ 2
  change (∑' n : {i // shell i = k}, G n * (nthPrimeReal n.1) ^ (-σ - 1)) ≤ _
  calc
    _ ≤ ∑' n : {i // shell i = k}, G n * X ^ (-σ - 1) := by
      apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
      intro n
      have hle := Nat.pow_log_le_self 2 (Nat.prime_nth_prime n.1).ne_zero
      change 2 ^ shell n.1 ≤ Nat.nth Nat.Prime n.1 at hle
      rw [n.2] at hle
      have hle' : (2 : ℝ) ^ k ≤ (Nat.nth Nat.Prime n.1 : ℝ) := by exact_mod_cast hle
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hX hle' (by linarith)) (sq_nonneg _)
    _ = (∑' n, G n) * X ^ (-σ - 1) := tsum_mul_right
    _ ≤ C * X ^ A * X ^ (-σ - 1) := mul_le_mul_of_nonneg_right (h k) (Real.rpow_nonneg hX.le _)
    _ = C * ((2 : ℝ) ^ (A - σ - 1)) ^ k := by
      rw [mul_assoc, ← Real.rpow_add hX]
      dsimp [X]
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring

end RiemannMasullo
