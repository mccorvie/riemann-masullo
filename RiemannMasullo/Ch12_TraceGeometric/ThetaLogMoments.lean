module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Signed log moments of rational theta coefficients

For Theorem 12.5.1.1, pp. 519–520, the rational norm expansion involves
translates of a single log profile with tapered Möbius amplitudes. Group the
indices in short logarithmic intervals. The Taylor polynomial of the sum in
each interval depends only on its signed moments.

For norms through `2 ^ N`, degree `n = (m + 2) * N` suffices for a physical
error bounded pointwise by `A / 2 ^ (m * N)` under the stated order-two
Gevrey derivative bound. With `M = 2 * D * (n + 1)`, the model uses `n + 1`
moments in each of `M * N + 1` intervals. Both the number of intervals and
the required moments are independent of the number of arithmetic terms.
The integral estimates use the original measure `dy / y ^ 2`. On a fixed positive
window, the true norm is within the stated error of the square root of the
finite Gram form of these moments, including its signed cross terms.
-/

open Finset

public noncomputable section

namespace RiemannMasullo.ThetaLogMoments

open Set in
private theorem taylor_at (H : ℝ → ℝ) {n : ℕ} (hH : ContDiff ℝ (n + 1) H)
    (a b : ℝ) :
    taylorWithinEval H n (uIcc a b) a b =
      ∑ k ∈ range (n + 1), (b - a) ^ k * iteratedDeriv k H a / (k.factorial : ℝ) := by
  rcases eq_or_ne a b with rfl | h
  · rw [taylorWithinEval_self, Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [zero_pow hk]
    · simp
  rw [taylor_within_apply]
  refine sum_congr rfl fun k hk ↦ ?_
  have hkn : (k : WithTop ℕ∞) ≤ n + 1 := by
    exact_mod_cast (Nat.le_of_lt (mem_range.mp hk))
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h) (hH.of_le hkn).contDiffAt left_mem_uIcc, smul_eq_mul]
  ring

open Set in
private theorem taylor_error (H : ℝ → ℝ) {n : ℕ} (hH : ContDiff ℝ (n + 1) H)
    {C : ℝ} (hD : ∀ r, |iteratedDeriv (n + 1) H r| ≤ C)
    (a b : ℝ) :
    |H b - ∑ k ∈ range (n + 1), (b - a) ^ k * iteratedDeriv k H a / (k.factorial : ℝ)| ≤
      C * |b - a| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [← taylor_at H hH]
  rcases eq_or_ne a b with rfl | hab
  · simp
  obtain ⟨x, _, hx⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hab hH.contDiffOn
  rw [hx, abs_div, abs_mul, abs_pow, abs_of_nonneg (show 0 ≤ ((n + 1).factorial : ℝ) by positivity)]
  gcongr
  exact hD x

open Set in
private theorem geom_error (H : ℝ → ℝ) {n : ℕ} (hH : ContDiff ℝ (n + 1) H)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hder : ∀ r, |iteratedDeriv (n + 1) H r| ≤ A * D ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2)
    {a b : ℝ} (hw : D * (n + 1) * |b - a| ≤ 1 / 2) :
    |H b - ∑ k ∈ range (n + 1), (b - a) ^ k * iteratedDeriv k H a / (k.factorial : ℝ)| ≤
      A * (1 / 2 : ℝ) ^ (n + 1) := by
  have hfac : ((n + 1).factorial : ℝ) ≤ (n + 1 : ℝ) ^ (n + 1) := by exact_mod_cast Nat.factorial_le_pow (n + 1)
  apply (taylor_error H hH hder a b).trans
  calc
    _ = A * D ^ (n + 1) * |b - a| ^ (n + 1) * ((n + 1).factorial : ℝ) := by
      field_simp
    _ ≤ A * D ^ (n + 1) * |b - a| ^ (n + 1) * (n + 1 : ℝ) ^ (n + 1) := by gcongr
    _ = A * (D * (n + 1) * |b - a|) ^ (n + 1) := by
      simp only [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw _) hA

variable {ι κ E : Type*} [DecidableEq κ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The signed moment of order `k` about the center of a single logarithmic interval. -/
@[expose] def moment (s : Finset ι) (bin : ι → κ) (loc : ι → ℝ) (c : ι → E)
    (center : κ → ℝ) (j : κ) (k : ℕ) : E :=
  ∑ i ∈ s with bin i = j, ((loc i - center j) ^ k) • c i

/-- Evaluate the Taylor expansion of all cells from their signed moments. -/
@[expose] def model (s : Finset ι) (cells : Finset κ) (bin : ι → κ) (loc : ι → ℝ)
    (c : ι → E) (center : κ → ℝ) (H : ℝ → ℝ) (n : ℕ) (x : ℝ) : E :=
  ∑ j ∈ cells, ∑ k ∈ range (n + 1),
    (iteratedDeriv k H (center j - x) / k.factorial) • moment s bin loc c center j k

private theorem model_eq (s : Finset ι) (cells : Finset κ) (bin : ι → κ) (loc : ι → ℝ)
    (c : ι → E) (center : κ → ℝ) (H : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hbin : ∀ i ∈ s, bin i ∈ cells) :
    model s cells bin loc c center H n x =
      ∑ i ∈ s, (∑ k ∈ range (n + 1), (loc i - center (bin i)) ^ k *
        iteratedDeriv k H (center (bin i) - x) / k.factorial) • c i := by
  classical
  unfold model moment
  rw [← sum_fiberwise_of_maps_to hbin (fun i ↦ (∑ k ∈ range (n + 1),
    (loc i - center (bin i)) ^ k * iteratedDeriv k H (center (bin i) - x) / k.factorial) • c i)]
  refine sum_congr rfl fun j hj ↦ ?_
  simp_rw [Finset.smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [(mem_filter.mp hi).2, Finset.sum_smul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul]
  congr 1
  ring

/-- The Taylor error on arbitrary cells of the stated widths is uniform in the evaluation point. -/
theorem model_error (s : Finset ι) (cells : Finset κ) (bin : ι → κ) (loc : ι → ℝ)
    (c : ι → E) (center : κ → ℝ) (hbin : ∀ i ∈ s, bin i ∈ cells)
    (H : ℝ → ℝ) {n : ℕ} (hH : ContDiff ℝ (n + 1) H)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hder : ∀ r, |iteratedDeriv (n + 1) H r| ≤ A * D ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2)
    (hw : ∀ i ∈ s, D * (n + 1) * |loc i - center (bin i)| ≤ 1 / 2) (x : ℝ) :
    ‖(∑ i ∈ s, H (loc i - x) • c i) - model s cells bin loc c center H n x‖ ≤
      A * (1 / 2 : ℝ) ^ (n + 1) * ∑ i ∈ s, ‖c i‖ := by
  rw [model_eq _ _ _ _ _ _ _ _ _ hbin, ← sum_sub_distrib, mul_sum]
  apply norm_sum_le_of_le
  intro i hi
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he : loc i - x - (center (bin i) - x) = loc i - center (bin i) := by ring
  simpa only [he] using geom_error H hH hA hD hder (a := center (bin i) - x) (b := loc i - x)
    (by simpa only [he] using hw i hi)

private theorem grid_bin {x : ℝ} {M N : ℕ} (hx : 0 ≤ x) (hN : x ≤ N) :
    ⌊M * x⌋₊ ∈ range (M * N + 1) := by
  apply Finset.mem_range.mpr
  have h : (⌊M * x⌋₊ : ℝ) ≤ (M * N : ℕ) := by
    push_cast
    exact (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hx)).trans
      (mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg _))
  exact Nat.lt_succ_of_le (by exact_mod_cast h)

private theorem grid_width {x : ℝ} {D n : ℕ} (hx : 0 ≤ x) (hD : 0 < D) :
    (D : ℝ) * (n + 1) * |x - (⌊((2 * D * (n + 1) : ℕ) : ℝ) * x⌋₊ : ℝ) / (2 * D * (n + 1) : ℕ)| ≤ 1 / 2 := by
  let M := 2 * D * (n + 1)
  have hp : 0 < (M : ℝ) := by
    dsimp [M]
    positivity
  change (D : ℝ) * (n + 1) * |x - (⌊(M : ℝ) * x⌋₊ : ℝ) / M| ≤ 1 / 2
  have hl := Nat.floor_le (mul_nonneg hp.le hx)
  have hu := Nat.lt_floor_add_one ((M : ℝ) * x)
  rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hl)))]
  have he : (D : ℝ) * (n + 1) = (M : ℝ) / 2 := by
    dsimp [M]
    push_cast
    ring
  rw [he]
  field_simp
  linarith

/-- The signed moment approximation using an equally spaced logarithmic grid on `[0,N]`. -/
@[expose] def gridModel (s : Finset ι) (loc : ι → ℝ) (c : ι → E)
    (N D n : ℕ) (H : ℝ → ℝ) (x : ℝ) : E :=
  let M := 2 * D * (n + 1)
  model s (range (M * N + 1)) (fun i ↦ ⌊(M : ℝ) * loc i⌋₊) loc c (fun j ↦ (j : ℝ) / M) H n x

private theorem grid_error (s : Finset ι) (loc : ι → ℝ) (c : ι → E) {N D n : ℕ}
    (hloc : ∀ i ∈ s, 0 ≤ loc i ∧ loc i ≤ N) (hD : 0 < D)
    (H : ℝ → ℝ) (hH : ContDiff ℝ (n + 1) H) {A : ℝ} (hA : 0 ≤ A)
    (hder : ∀ r, |iteratedDeriv (n + 1) H r| ≤ A * D ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2)
    (x : ℝ) :
    ‖(∑ i ∈ s, H (loc i - x) • c i) - gridModel s loc c N D n H x‖ ≤
      A * (1 / 2 : ℝ) ^ (n + 1) * ∑ i ∈ s, ‖c i‖ := by
  apply model_error _ _ _ _ _ _ (fun i hi ↦ grid_bin (hloc i hi).1 (hloc i hi).2)
    H hH hA (Nat.cast_nonneg D) hder
  exact fun i hi ↦ grid_width (hloc i hi).1 hD

private theorem coefficient_le (w : ℕ → ℂ) (n : ℕ)
    (hw : ∀ d ∈ n.divisors, ‖w d‖ ≤ 1) :
    ‖(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d) -
      (if n = 1 then 1 else 0)‖ ≤ n + 1 := by
  have hm (d : ℕ) : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hs : ‖∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d‖ ≤
      ∑ _d ∈ n.divisors, (1 : ℝ) := by
    apply norm_sum_le_of_le
    intro d hd
    rw [norm_mul]
    exact (mul_le_mul (hm d) (hw d hd) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hs
  have hu : ‖(if n = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
  exact (norm_sub_le _ _).trans (add_le_add (hs.trans (by exact_mod_cast Nat.card_divisors_le_self n)) hu)

private theorem mass_le (s : Finset ℕ) {X : ℕ} (hs : s ⊆ Icc 1 X)
    (w c : ℕ → ℂ) (hw : ∀ d ≤ X, ‖w d‖ ≤ 1)
    (hc : ∀ n ∈ s, c n = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d) -
      if n = 1 then 1 else 0) :
    ∑ n ∈ s, ‖c n‖ ≤ 2 * (X : ℝ) ^ 2 := by
  have hn (n : ℕ) (h : n ∈ s) : 1 ≤ n ∧ n ≤ X := mem_Icc.mp (hs h)
  have hcard : s.card ≤ X := (card_le_card hs).trans (by simp [Nat.card_Icc])
  calc
    _ ≤ ∑ n ∈ s, (2 * X : ℝ) := by
      refine sum_le_sum fun n h ↦ ?_
      rw [hc n h]
      apply (coefficient_le w n (fun d hd ↦ hw d ((Nat.le_of_dvd (hn n h).1 (Nat.dvd_of_mem_divisors hd)).trans (hn n h).2))).trans
      have hnx : (n : ℝ) ≤ X := by exact_mod_cast (hn n h).2
      have hx : (1 : ℝ) ≤ X := by exact_mod_cast (hn n h).1.trans (hn n h).2
      linarith
    _ ≤ (X : ℝ) * (2 * X) := by
      simp only [sum_const, nsmul_eq_mul]
      gcongr
    _ = _ := by ring

private theorem log_location {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ N) :
    0 ≤ Real.log n ∧ Real.log n ≤ N := by
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.log_nonneg hp, ?_⟩
  have h := Real.log_le_log (by positivity : 0 < (n : ℝ)) (by exact_mod_cast hN : (n : ℝ) ≤ 2 ^ N)
  rw [Real.log_pow] at h
  have h₂ : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact h.trans ((mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _)).trans_eq (mul_one _))

private theorem dyadic_budget (m N : ℕ) :
    (1 / 2 : ℝ) ^ ((m + 2) * N + 1) * (2 * (2 ^ N) ^ 2) = (1 / 2 : ℝ) ^ (m * N) := by
  have h : (1 / 2 : ℝ) ^ (2 * N) * ((2 : ℝ) ^ N) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm N 2, ← mul_pow]
    norm_num
  rw [Nat.add_mul, pow_succ, pow_add]
  calc
    _ = (1 / 2 : ℝ) ^ (m * N) * ((1 / 2 : ℝ) ^ (2 * N) * ((2 : ℝ) ^ N) ^ 2) := by ring
    _ = _ := by rw [h, mul_one]

/-- The moment approximation of tapered Möbius coefficients through `2 ^ N` has arbitrarily prescribed dyadic accuracy. -/
theorem signed_moebius_grid (s : Finset ℕ) {N D : ℕ} (hs : s ⊆ Icc 1 (2 ^ N)) (hD : 0 < D)
    (w c : ℕ → ℂ) (hw : ∀ d ≤ 2 ^ N, ‖w d‖ ≤ 1)
    (hc : ∀ n ∈ s, c n = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d) -
      if n = 1 then 1 else 0) (m : ℕ)
    (H : ℝ → ℝ) (hH : ContDiff ℝ ((m + 2) * N + 1 : ℕ) H) {A : ℝ} (hA : 0 ≤ A)
    (hd : ∀ r, |iteratedDeriv ((m + 2) * N + 1) H r| ≤
      A * D ^ ((m + 2) * N + 1) * (((m + 2) * N + 1).factorial : ℝ) ^ 2) (x : ℝ) :
    ‖(∑ n ∈ s, H (Real.log n - x) • c n) -
      gridModel s (fun n ↦ Real.log n) c N D ((m + 2) * N) H x‖ ≤ A * (1 / 2 : ℝ) ^ (m * N) := by
  apply (grid_error s _ c (fun n h ↦ log_location (mem_Icc.mp (hs h)).1 (mem_Icc.mp (hs h)).2)
    hD H (by simpa only [Nat.cast_add, Nat.cast_one] using hH) hA hd x).trans
  have hmass := mass_le s hs w c hw hc
  push_cast at hmass
  calc
    _ ≤ A * (1 / 2 : ℝ) ^ ((m + 2) * N + 1) * (2 * (2 ^ N) ^ 2) := by gcongr
    _ = _ := by rw [mul_assoc, dyadic_budget]

open Set MeasureTheory in
private theorem halfline {u C : ℝ} (hu : 0 < u) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi u)) (h0 : ∀ y ∈ Ioi u, 0 ≤ f y)
    (hb : ∀ y ∈ Ioi u, f y ≤ C) :
    IntegrableOn (fun y ↦ f y / y ^ 2) (Ioi u) ∧ (∫ y in Ioi u, f y / y ^ 2) ≤ C / u := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hu).const_mul C
  have he (y : ℝ) (hy : y ∈ Ioi u) : y ^ (-2 : ℝ) = 1 / y ^ 2 := by
    rw [Real.rpow_neg (hu.trans hy).le, Real.rpow_two, one_div]
  have hm (y : ℝ) (hy : y ∈ Ioi u) : f y / y ^ 2 ≤ C * y ^ (-2 : ℝ) := by
    rw [he y hy, mul_one_div]
    exact div_le_div_of_nonneg_right (hb y hy) (sq_nonneg _)
  have hf' : IntegrableOn (fun y ↦ f y / y ^ 2) (Ioi u) := by
    apply hi.mono' ((hf.div (continuous_id.pow 2).continuousOn
      (fun y hy ↦ pow_ne_zero _ (hu.trans hy).ne')).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change ‖f y / y ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (h0 y hy) (sq_nonneg _))]
    exact hm y hy
  refine ⟨hf', (setIntegral_mono_on hf' hi measurableSet_Ioi hm).trans_eq ?_⟩
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hu]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

open Set MeasureTheory in
private theorem continuous_model {ι κ E : Type*} [DecidableEq κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (cells : Finset κ) (bin : ι → κ) (loc : ι → ℝ) (c : ι → E)
    (center : κ → ℝ) (H : ℝ → ℝ) (n : ℕ) (hH : ContDiff ℝ (n + 1) H) :
    Continuous (model s cells bin loc c center H n) := by
  unfold model
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro k hk
  have hkn : (k : WithTop ℕ∞) ≤ n + 1 := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hk))
  exact (((hH.continuous_iteratedDeriv k hkn).comp (continuous_const.sub continuous_id)).div_const _).smul continuous_const

open Set MeasureTheory in
private theorem continuous_rows (s : Finset ℕ) (c : ℕ → ℂ) {N D n : ℕ}
    (hs : ∀ i ∈ s, 0 < i) {J : Set ℝ} (hpos : ∀ y ∈ J, 0 < y)
    (H : ℝ → ℝ) (hH : ContDiff ℝ (n + 1) H) :
    ContinuousOn (fun y : ℝ ↦ ∑ i ∈ s, H (Real.log (i / y)) • c i) J ∧
    ContinuousOn (fun y : ℝ ↦ gridModel s (fun i ↦ Real.log i) c N D n H (Real.log y)) J := by
  constructor
  · apply continuousOn_finsetSum
    intro i hi
    have hi' := hs i hi
    have hdiv : ContinuousOn (fun y : ℝ ↦ i / y) J :=
      continuousOn_const.div continuousOn_id (fun y hy ↦ (hpos y hy).ne')
    have hl := hdiv.log (fun y hy ↦ div_ne_zero (by positivity) (hpos y hy).ne')
    exact (hH.continuous.comp_continuousOn hl).smul (continuousOn_const (c := c i))
  · have hmod : Continuous (gridModel s (fun i ↦ Real.log i) c N D n H) := by
      unfold gridModel
      exact continuous_model _ _ _ _ _ _ H n hH
    exact hmod.comp_continuousOn (Real.continuousOn_log.mono (fun y hy ↦ (hpos y hy).ne'))

open Set MeasureTheory in
/-- The physical approximation error is square integrable and has the stated bound above every positive lower cutoff. -/
theorem signed_moebius_physical (s : Finset ℕ) {N D : ℕ} (hs : s ⊆ Finset.Icc 1 (2 ^ N))
    (hD : 0 < D) (w c : ℕ → ℂ) (hw : ∀ d ≤ 2 ^ N, ‖w d‖ ≤ 1)
    (hc : ∀ n ∈ s, c n = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d) -
      if n = 1 then 1 else 0) (m : ℕ)
    (H : ℝ → ℝ) (hH : ContDiff ℝ ((m + 2) * N + 1 : ℕ) H) {A : ℝ} (hA : 0 ≤ A)
    (hd : ∀ r, |iteratedDeriv ((m + 2) * N + 1) H r| ≤
      A * D ^ ((m + 2) * N + 1) * (((m + 2) * N + 1).factorial : ℝ) ^ 2) {u : ℝ} (hu : 0 < u) :
    let F := fun y : ℝ ↦ (∑ n ∈ s, H (Real.log (n / y)) • c n) -
      gridModel s (fun n ↦ Real.log n) c N D ((m + 2) * N) H (Real.log y)
    IntegrableOn (fun y ↦ ‖F y‖ ^ 2 / y ^ 2) (Ioi u) ∧
      (∫ y in Ioi u, ‖F y‖ ^ 2 / y ^ 2) ≤ (A * (1 / 2 : ℝ) ^ (m * N)) ^ 2 / u := by
  dsimp only
  have hlog (n : ℕ) (hn : n ∈ s) (y : ℝ) (hy : y ∈ Ioi u) :
      Real.log (n / y) = Real.log n - Real.log y := by
    have hn' := (Finset.mem_Icc.mp (hs hn)).1
    exact Real.log_div (by positivity) (hu.trans hy).ne'
  apply halfline hu
  · obtain ⟨hF, hG⟩ := continuous_rows s c (N := N) (D := D)
      (fun i hi ↦ (Finset.mem_Icc.mp (hs hi)).1) (fun y (hy : y ∈ Ioi u) ↦ hu.trans hy)
      H (n := (m + 2) * N) (by simpa only [Nat.cast_add, Nat.cast_one] using hH)
    exact (hF.sub hG).norm.pow 2
  · exact fun _ _ ↦ sq_nonneg _
  · intro y hy
    apply pow_le_pow_left₀ (norm_nonneg _)
    have heq : ∑ n ∈ s, H (Real.log (n / y)) • c n = ∑ n ∈ s, H (Real.log n - Real.log y) • c n :=
      sum_congr rfl (fun n hn ↦ by rw [hlog n hn y hy])
    rw [heq]
    exact signed_moebius_grid s hs hD w c hw hc m H hH hA hd _

open Set MeasureTheory in
private theorem integral_gram {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset α) (v : α → E) (b : α → ℝ → ℝ) {u t : ℝ} (hu : 0 < u)
    (hb : ∀ i ∈ s, ContinuousOn (b i) (Set.Icc u t)) :
    (∫ y in Set.Icc u t, ‖∑ i ∈ s, b i y • v i‖ ^ 2 / y ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j) * ∫ y in Set.Icc u t, b i y * b j y / y ^ 2 := by
  let f (i j : α) (y : ℝ) := inner ℝ (v i) (v j) * (b i y * b j y / y ^ 2)
  have hInt (i : α) (hi : i ∈ s) (j : α) (hj : j ∈ s) :
      IntegrableOn (f i j) (Set.Icc u t) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact continuousOn_const.mul (((hb i hi).mul (hb j hj)).div (continuous_id.pow 2).continuousOn
      (fun y hy ↦ pow_ne_zero _ (hu.trans_le hy.1).ne'))
  have hin (y : ℝ) : ‖∑ i ∈ s, b i y • v i‖ ^ 2 / y ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i j y := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_div]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    dsimp only [f]
    rw [real_inner_comm (v j) (v i)]
    ring
  simp_rw [hin]
  rw [integral_finsetSum s (fun i hi ↦ integrable_finsetSum s fun j hj ↦ hInt i hi j hj)]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [integral_finsetSum s (fun j hj ↦ hInt i hi j hj)]
  refine sum_congr rfl fun j _ ↦ ?_
  exact integral_const_mul _ _

open Set MeasureTheory in
/-- The full physical energy of the moment model on a positive compact window is its finite Gram quadratic form. -/
theorem physical_gram {ι κ E : Type*} [DecidableEq κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (cells : Finset κ) (bin : ι → κ) (loc : ι → ℝ) (c : ι → E)
    (center : κ → ℝ) (H : ℝ → ℝ) (n : ℕ) (hH : ContDiff ℝ (n + 1) H)
    {u t : ℝ} (hu : 0 < u) :
    let J := cells ×ˢ Finset.range (n + 1)
    let v := fun p : κ × ℕ ↦ moment s bin loc c center p.1 p.2
    let b := fun (p : κ × ℕ) (y : ℝ) ↦ iteratedDeriv p.2 H (center p.1 - Real.log y) / p.2.factorial
    (∫ y in Set.Icc u t, ‖model s cells bin loc c center H n (Real.log y)‖ ^ 2 / y ^ 2) =
      ∑ p ∈ J, ∑ q ∈ J, inner ℝ (v p) (v q) * ∫ y in Set.Icc u t, b p y * b q y / y ^ 2 := by
  intro J v b
  have hb (p : κ × ℕ) (hp : p ∈ J) : ContinuousOn (b p) (Set.Icc u t) := by
    have hk := Finset.mem_range.mp (Finset.mem_product.mp hp).2
    have hp' : (p.2 : WithTop ℕ∞) ≤ n + 1 := by exact_mod_cast hk.le
    have hlog : ContinuousOn Real.log (Set.Icc u t) :=
      Real.continuousOn_log.mono (fun y hy ↦ (hu.trans_le hy.1).ne')
    exact ((hH.continuous_iteratedDeriv p.2 hp').comp_continuousOn (continuousOn_const.sub hlog)).div_const _
  rw [← integral_gram J v b hu hb]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _
  simp only [J, v, b, model, Finset.sum_product]

open Set MeasureTheory in
private theorem compact_lp_norm {u t : ℝ} (hu : 0 < u) {F : ℝ → E} (hF : ContinuousOn F (Set.Icc u t)) :
    let f := fun y : ℝ ↦ y⁻¹ • F y
    let ν := volume.restrict (Set.Icc u t)
    MemLp f 2 ν ∧ lpNorm f 2 ν = Real.sqrt (∫ y in Set.Icc u t, ‖F y‖ ^ 2 / y ^ 2) := by
  intro f ν
  have hc : ContinuousOn f (Set.Icc u t) :=
    ((continuousOn_id (s := Set.Icc u t)).inv₀ (fun y hy ↦ (hu.trans_le hy.1).ne')).smul hF
  have hf : MemLp f 2 ν := (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable measurableSet_Icc)).mpr
    ((hc.norm.pow 2).integrableOn_compact isCompact_Icc)
  refine ⟨hf, ?_⟩
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  simp [f, norm_smul, mul_pow, sq_abs, Real.norm_eq_abs, div_eq_inv_mul]

open Set MeasureTheory in
private theorem physical_norm_gap {u t C : ℝ} (hu : 0 < u)
    {F G : ℝ → E} (hF : ContinuousOn F (Set.Icc u t)) (hG : ContinuousOn G (Set.Icc u t))
    (henergy : (∫ y in Set.Icc u t, ‖F y - G y‖ ^ 2 / y ^ 2) ≤ C) :
    |Real.sqrt (∫ y in Set.Icc u t, ‖F y‖ ^ 2 / y ^ 2) -
      Real.sqrt (∫ y in Set.Icc u t, ‖G y‖ ^ 2 / y ^ 2)| ≤ Real.sqrt C := by
  obtain ⟨hmF, hnF⟩ := compact_lp_norm hu hF
  obtain ⟨hmG, hnG⟩ := compact_lp_norm hu hG
  obtain ⟨_, hnD⟩ := compact_lp_norm hu (hF.sub hG)
  let ν := volume.restrict (Set.Icc u t)
  let f (y : ℝ) := y⁻¹ • F y
  let g (y : ℝ) := y⁻¹ • G y
  have hd : lpNorm (f - g) 2 ν ≤ Real.sqrt C := by
    apply LE.le.trans _ (Real.sqrt_le_sqrt henergy)
    exact (by simpa only [f, g, Pi.sub_apply, smul_sub, Pi.sub_def] using hnD.le)
  rw [← hnF, ← hnG]
  change |lpNorm f 2 ν - lpNorm g 2 ν| ≤ _
  apply LE.le.trans _ hd
  apply abs_le.mpr
  constructor
  · linarith only [lpNorm_le_lpNorm_add_lpNorm_sub (f := g) hmF (by norm_num : (1 : ENNReal) ≤ 2)]
  · linarith only [lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) hmG (by norm_num : (1 : ENNReal) ≤ 2)]

open Set MeasureTheory in
/-- The square root of the true physical energy of the signed rational coefficients differs from that
of their finite moment model by the prescribed error. The model energy is the quadratic form in `physical_gram`. -/
theorem physical_approximation {u t : ℝ} (hu : 0 < u) (s : Finset ℕ) {N D : ℕ}
    (hs : s ⊆ Finset.Icc 1 (2 ^ N)) (hD : 0 < D) (w c : ℕ → ℂ) (hw : ∀ d ≤ 2 ^ N, ‖w d‖ ≤ 1)
    (hc : ∀ n ∈ s, c n = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d) -
      if n = 1 then 1 else 0) (m : ℕ)
    (H : ℝ → ℝ) (hH : ContDiff ℝ ((m + 2) * N + 1 : ℕ) H) {A : ℝ} (hA : 0 ≤ A)
    (hd : ∀ r, |iteratedDeriv ((m + 2) * N + 1) H r| ≤
      A * D ^ ((m + 2) * N + 1) * (((m + 2) * N + 1).factorial : ℝ) ^ 2) :
    let F := fun y : ℝ ↦ ∑ n ∈ s, H (Real.log (n / y)) • c n
    let G := fun y : ℝ ↦ gridModel s (fun n ↦ Real.log n) c N D ((m + 2) * N) H (Real.log y)
    |Real.sqrt (∫ y in Set.Icc u t, ‖F y‖ ^ 2 / y ^ 2) -
      Real.sqrt (∫ y in Set.Icc u t, ‖G y‖ ^ 2 / y ^ 2)| ≤ A * (1 / 2 : ℝ) ^ (m * N) / Real.sqrt u := by
  intro F G
  obtain ⟨hF, hG⟩ := continuous_rows s c (N := N) (D := D)
    (fun i hi ↦ (Finset.mem_Icc.mp (hs hi)).1) (fun y (hy : y ∈ Set.Icc u t) ↦ hu.trans_le hy.1)
    H (n := (m + 2) * N) (by simpa only [Nat.cast_add, Nat.cast_one] using hH)
  obtain ⟨hint, hbd⟩ := signed_moebius_physical s hs hD w c hw hc m H hH hA hd hu
  have hsmall : (∫ y in Set.Icc u t, ‖F y - G y‖ ^ 2 / y ^ 2) ≤ (A * (1 / 2 : ℝ) ^ (m * N)) ^ 2 / u := by
    rw [integral_Icc_eq_integral_Ioc]
    exact (setIntegral_mono_set hint (ae_of_all _ (fun y ↦ div_nonneg (sq_nonneg _) (sq_nonneg _)))
      (show Set.Ioc u t ⊆ Set.Ioi u from fun _ hy ↦ hy.1).eventuallySubset).trans hbd
  apply (physical_norm_gap hu hF hG hsmall).trans_eq
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]

end RiemannMasullo.ThetaLogMoments
