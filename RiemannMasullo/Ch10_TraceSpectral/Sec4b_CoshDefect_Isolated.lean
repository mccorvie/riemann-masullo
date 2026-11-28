module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshKernel_Isolated
public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Pointwise binomial-hyperbolic defect expansion and operator `HasSum` (`#7406`)

1. `abs_ring_choose_le`, `hasSum_one_add_rpow`: binomial bounds & series on `|w| < 1`.
2. `CoshDefectIndex`, `coshDefectX`, `coshDefectT`: separated factors `(x, t) ↦ X_ι(x) * T_ι(t)`
   for `1 - coshSobolevDensity α s (x - t) / coshSobolevDensity α s x`.
3. `hasSum_coshDefect_pointwise`: pointwise `HasSum` identity for `|t| ≤ 1 / 4`.
4. `coshDefectDerivBound`, `norm_iteratedDeriv_coshDefectT_le`, `summable_coshDefectDerivBound`,
   and `exists_delta_coshDefect_tsum_le_half`.
5. `hasSum_coshTestAction_sub_adjoint`: operator-norm `HasSum` for `A_cosh(ψ) - A_cosh(ψ*)†`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section CoshDefect

/-- Binomial coefficient bound for real parameter `a`: `|Ring.choose a k| ≤ 2 ^ (Nat.ceil |a| + k)`. -/
lemma abs_ring_choose_le (a : ℝ) (k : ℕ) : |Ring.choose a k| ≤ (2 : ℝ) ^ (Nat.ceil |a| + k) := by
  let N : ℕ := Nat.ceil |a|
  have hpoch : ∀ m : ℕ, (descPochhammer ℤ m).smeval a = ∏ i ∈ Finset.range m, (a - (i : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
        Polynomial.smeval_X, Polynomial.smeval_natCast, ih, Finset.prod_range_succ]
      simp only [pow_one, pow_zero, nsmul_eq_mul, mul_one]
  have hdesc : ∀ m : ℕ, (N + m).descFactorial m = ∏ i ∈ Finset.range m, (N + 1 + i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← add_assoc, Nat.succ_descFactorial_succ, ih, Finset.prod_range_succ]
      ring
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hmul : (k.factorial : ℝ) * |Ring.choose a k| ≤ ((N + k).choose k : ℝ) * (k.factorial : ℝ) := by
    have h1 : (k.factorial : ℝ) * Ring.choose a k = ∏ i ∈ Finset.range k, (a - (i : ℝ)) := by
      simpa only [nsmul_eq_mul, hpoch] using (Ring.descPochhammer_eq_factorial_smul_choose a k).symm
    have h2 : (k.factorial : ℝ) * |Ring.choose a k| = ∏ i ∈ Finset.range k, |a - (i : ℝ)| := by
      have := congrArg abs h1
      rw [abs_mul, abs_of_pos hfac, Finset.abs_prod] at this
      exact this
    rw [h2]
    calc ∏ i ∈ Finset.range k, |a - (i : ℝ)|
        ≤ ∏ i ∈ Finset.range k, ((N + 1 + i : ℕ) : ℝ) := by
          refine Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
          have hceil : |a| ≤ (N : ℝ) := Nat.le_ceil |a|
          have hsub : |a - (i : ℝ)| ≤ |a| + (i : ℝ) :=
            (abs_sub a (i : ℝ)).trans_eq (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ))])
          push_cast
          linarith
      _ = ((∏ i ∈ Finset.range k, (N + 1 + i) : ℕ) : ℝ) := by push_cast; rfl
      _ = (((N + k).descFactorial k : ℕ) : ℝ) := by rw [hdesc]
      _ = ((N + k).choose k : ℝ) * (k.factorial : ℝ) := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]; push_cast; rfl
  have hch : |Ring.choose a k| ≤ ((N + k).choose k : ℝ) := by nlinarith
  have hpow : ((N + k).choose k : ℝ) ≤ (2 : ℝ) ^ (N + k) := by
    exact_mod_cast Nat.choose_le_two_pow (N + k) k
  exact hch.trans hpow

/-- Real binomial series identity for `(1 + w) ^ a` when `|w| < 1`. -/
lemma hasSum_one_add_rpow (a w : ℝ) (hw : |w| < 1) :
    HasSum (fun k : ℕ ↦ Ring.choose a k * w ^ k) ((1 + w) ^ a) := by
  have heball : w ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_lt_one.mpr hw
  have h := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a) |>.hasSum heball
  simpa only [zero_add, binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul] using h

/-- Countable defect-expansion index separating `(x)` and `(t)` variables. -/
abbrev CoshDefectIndex : Type := Bool ⊕ (Bool × Σ k : ℕ, Fin (k + 2))

/-- Spatial (`logNorm g`) factor of the separated defect series. -/
def coshDefectX (α : ℝ) : CoshDefectIndex → ℝ → ℂ
  | Sum.inl false => fun _ ↦ 1
  | Sum.inl true => fun x ↦ (Real.tanh (2 * α * x) : ℂ)
  | Sum.inr (false, ⟨k, j⟩) => fun x ↦
      (((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val : ℝ) : ℂ)
  | Sum.inr (true, ⟨k, j⟩) => fun x ↦
      ((Real.tanh (2 * α * x) *
        ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val) : ℝ) : ℂ)

/-- Test (`logNorm y`) factor of the separated defect series. -/
def coshDefectT (α s : ℝ) : CoshDefectIndex → ℝ → ℂ
  | Sum.inl false => fun t ↦ ((1 - Real.cosh (2 * α * t) : ℝ) : ℂ)
  | Sum.inl true => fun t ↦ ((Real.sinh (2 * α * t) : ℝ) : ℂ)
  | Sum.inr (false, ⟨k, j⟩) => fun t ↦
      ((-Ring.choose (s / 2) (k + 1) * ((k + 1).choose j.val : ℝ) *
        Real.cosh (2 * α * t) * t ^ (k + 1 + j.val) : ℝ) : ℂ)
  | Sum.inr (true, ⟨k, j⟩) => fun t ↦
      ((Ring.choose (s / 2) (k + 1) * ((k + 1).choose j.val : ℝ) *
        Real.sinh (2 * α * t) * t ^ (k + 1 + j.val) : ℝ) : ℂ)

private lemma abs_two_mul_div_one_add_sq (x : ℝ) : |-2 * x / (1 + x ^ 2)| ≤ 1 := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden, div_le_one hden, abs_mul, abs_neg, abs_of_pos zero_lt_two]
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

private lemma abs_one_div_one_add_sq (x : ℝ) : |1 / (1 + x ^ 2)| ≤ 1 := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  rw [abs_div, abs_one, abs_of_pos hden, div_le_one hden]
  nlinarith [sq_nonneg x]

lemma norm_coshDefectX_le_one (α : ℝ) (ι : CoshDefectIndex) (x : ℝ) :
    ‖coshDefectX α ι x‖ ≤ 1 := by
  have htanh : |Real.tanh (2 * α * x)| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hlin : |(-2 * x / (1 + x ^ 2))| ≤ 1 := abs_two_mul_div_one_add_sq x
  have hquad : |(1 / (1 + x ^ 2))| ≤ 1 := abs_one_div_one_add_sq x
  rcases ι with b | ⟨b, ⟨k, j⟩⟩
  · cases b
    · simp [coshDefectX]
    · simp only [coshDefectX, Complex.norm_real, Real.norm_eq_abs]
      exact htanh
  · have hprod : |(-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_pow]
      have h1 : |(-2 * x / (1 + x ^ 2))| ^ (k + 1 - j.val) ≤ 1 := pow_le_one₀ (abs_nonneg _) hlin
      have h2 : |(1 / (1 + x ^ 2))| ^ j.val ≤ 1 := pow_le_one₀ (abs_nonneg _) hquad
      exact (mul_le_mul h1 h2 (by positivity) zero_le_one).trans_eq (one_mul 1)
    cases b
    · simp only [coshDefectX, Complex.norm_real, Real.norm_eq_abs]
      exact hprod
    · simp only [coshDefectX, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_mul]
      exact (mul_le_mul htanh hprod (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

lemma continuous_coshDefectX (α : ℝ) (ι : CoshDefectIndex) : Continuous (coshDefectX α ι) := by
  have htanh : Continuous (fun x : ℝ ↦ Real.tanh (2 * α * x)) := by
    have h : Continuous (fun x : ℝ ↦ Real.sinh (2 * α * x) / Real.cosh (2 * α * x)) :=
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
        fun x ↦ (Real.cosh_pos _).ne'
    exact h.congr fun x ↦ (Real.tanh_eq_sinh_div_cosh _).symm
  have hden : ∀ x : ℝ, (1 : ℝ) + x ^ 2 ≠ 0 := fun x ↦ (by positivity : (0 : ℝ) < 1 + x ^ 2).ne'
  have h1 : Continuous (fun x : ℝ ↦ -2 * x / (1 + x ^ 2)) :=
    (continuous_const.mul continuous_id).div (continuous_const.add (continuous_id.pow 2)) hden
  have h2 : Continuous (fun x : ℝ ↦ 1 / (1 + x ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) hden
  rcases ι with b | ⟨b, ⟨k, j⟩⟩
  · cases b
    · exact continuous_const
    · exact Complex.continuous_ofReal.comp htanh
  · have hp : Continuous (fun x : ℝ ↦ (-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val) :=
      (h1.pow _).mul (h2.pow _)
    cases b
    · exact Complex.continuous_ofReal.comp hp
    · exact Complex.continuous_ofReal.comp (htanh.mul hp)

lemma contDiff_coshDefectT (α s : ℝ) (ι : CoshDefectIndex) :
    ContDiff ℝ (⊤ : ℕ∞) (coshDefectT α s ι) := by
  have hcosh : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ Real.cosh (2 * α * t)) :=
    Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  have hsinh : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ Real.sinh (2 * α * t)) :=
    Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)
  rcases ι with b | ⟨b, ⟨k, j⟩⟩
  · cases b
    · exact Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hcosh)
    · exact Complex.ofRealCLM.contDiff.comp hsinh
  · have hpow : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ t ^ (k + 1 + j.val)) := contDiff_id.pow _
    cases b
    · exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul hcosh).mul hpow)
    · exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul hsinh).mul hpow)

@[simp]
lemma coshDefectT_zero (α s : ℝ) (ι : CoshDefectIndex) : coshDefectT α s ι 0 = 0 := by
  rcases ι with b | ⟨b, ⟨k, j⟩⟩
  · cases b <;> simp [coshDefectT]
  · cases b <;> simp [coshDefectT, Nat.add_eq_zero_iff]

/-- Uniform `r`-th derivative bound for `coshDefectT α s ι` on `|t| ≤ δ`. -/
def coshDefectDerivBound (α s δ : ℝ) (r : ℕ) : CoshDefectIndex → ℝ
  | Sum.inl false =>
      if r = 0 then Real.cosh (2 * α * δ) - 1 else (2 * α) ^ r * Real.cosh (2 * α * δ)
  | Sum.inl true =>
      if r = 0 then Real.sinh (2 * α * δ) else (2 * α) ^ r * Real.cosh (2 * α * δ)
  | Sum.inr (_, ⟨k, j⟩) =>
      |Ring.choose (s / 2) (k + 1)| * ((k + 1).choose j.val : ℝ) * Real.cosh (2 * α * δ) *
        ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * (2 * α) ^ q *
          (((k + 1 + j.val).descFactorial (r - q) : ℝ) * δ ^ (k + 1 + j.val - (r - q)))

lemma coshDefectDerivBound_nonneg {α s δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ) (r : ℕ)
    (ι : CoshDefectIndex) : 0 ≤ coshDefectDerivBound α s δ r ι := by
  have h2αδ : 0 ≤ 2 * α * δ := by positivity
  rcases ι with b | ⟨b, ⟨k, j⟩⟩
  · cases b
    · dsimp only [coshDefectDerivBound]
      split_ifs
      · linarith [Real.one_le_cosh (2 * α * δ)]
      · positivity
    · dsimp only [coshDefectDerivBound]
      split_ifs
      · exact Real.sinh_nonneg_iff.mpr h2αδ
      · positivity
  · simp only [coshDefectDerivBound]
    refine mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (Real.cosh_pos _).le) ?_
    refine Finset.sum_nonneg fun q _ ↦ ?_
    positivity

private lemma abs_sinh_le_cosh (y : ℝ) : |Real.sinh y| ≤ Real.cosh y := by
  rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_two]
  refine div_le_div_of_nonneg_right ((abs_sub _ _).trans_eq ?_) zero_le_two
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]

private lemma abs_iteratedDeriv_cosh_le (q : ℕ) (y : ℝ) :
    |iteratedDeriv q Real.cosh y| ≤ Real.cosh y := by
  induction q generalizing y with
  | zero => simp [abs_of_pos (Real.cosh_pos y)]
  | succ q _ =>
    rcases Nat.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [hm, Real.iteratedDeriv_add_one_cosh, show m + m = 2 * m by ring, Real.iteratedDeriv_even_sinh]
      exact abs_sinh_le_cosh y
    · rw [hm, Real.iteratedDeriv_add_one_cosh, Real.iteratedDeriv_odd_sinh]
      exact le_of_eq (abs_of_pos (Real.cosh_pos y))

private lemma abs_iteratedDeriv_sinh_le (q : ℕ) (y : ℝ) :
    |iteratedDeriv q Real.sinh y| ≤ Real.cosh y := by
  induction q generalizing y with
  | zero => simp [abs_sinh_le_cosh y]
  | succ q _ =>
    rw [Real.iteratedDeriv_add_one_sinh]
    exact abs_iteratedDeriv_cosh_le q y

private lemma cosh_le_cosh_of_abs_le {u v : ℝ} (h : |u| ≤ v) : Real.cosh u ≤ Real.cosh v := by
  rw [← abs_of_nonneg ((abs_nonneg u).trans h)] at h
  exact Real.cosh_le_cosh.mpr h

private lemma abs_sinh_le_sinh_of_abs_le {u v : ℝ} (h : |u| ≤ v) : |Real.sinh u| ≤ Real.sinh v := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  rw [abs_le]
  exact ⟨by linarith [Real.sinh_le_sinh.mpr h1, Real.sinh_neg v], Real.sinh_le_sinh.mpr h2⟩

private lemma iteratedDeriv_ofReal_comp {r : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    iteratedDeriv r (fun x ↦ (f x : ℂ)) t = ((iteratedDeriv r f t : ℝ) : ℂ) := by
  induction r generalizing t with
  | zero => simp
  | succ r ih =>
    have hfun : iteratedDeriv r (fun x : ℝ ↦ (f x : ℂ)) =
        fun x : ℝ ↦ Complex.ofRealCLM (iteratedDeriv r f x) :=
      funext ih
    rw [iteratedDeriv_succ, hfun]
    have hdiff : DifferentiableAt ℝ (iteratedDeriv r f) t :=
      hf.differentiable_iteratedDeriv r (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top r)) t
    have hd : HasDerivAt (fun x ↦ Complex.ofRealCLM (iteratedDeriv r f x))
        (Complex.ofRealCLM (deriv (iteratedDeriv r f) t)) t :=
      hdiff.hasDerivAt.ofReal_comp
    rw [hd.deriv, iteratedDeriv_succ]
    rfl

lemma norm_iteratedDeriv_coshDefectT_le {α s δ : ℝ} (hα : 0 ≤ α) (_hδ : 0 ≤ δ) (r : ℕ)
    (ι : CoshDefectIndex) {t : ℝ} (ht : |t| ≤ δ) :
    ‖iteratedDeriv r (coshDefectT α s ι) t‖ ≤ coshDefectDerivBound α s δ r ι := by
  have h2αt : |2 * α * t| ≤ 2 * α * δ := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg zero_le_two hα)]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hcosh_le : Real.cosh (2 * α * t) ≤ Real.cosh (2 * α * δ) := cosh_le_cosh_of_abs_le h2αt
  have hq_cosh (q : ℕ) : ‖iteratedDeriv q (fun x : ℝ ↦ Real.cosh (2 * α * x)) t‖ ≤
      (2 * α) ^ q * Real.cosh (2 * α * δ) := by
    rw [iteratedDeriv_comp_const_mul Real.contDiff_cosh (2 * α), Real.norm_eq_abs, abs_mul,
      abs_pow, abs_of_nonneg (mul_nonneg zero_le_two hα)]
    exact mul_le_mul_of_nonneg_left ((abs_iteratedDeriv_cosh_le q _).trans hcosh_le) (by positivity)
  have hq_sinh (q : ℕ) : ‖iteratedDeriv q (fun x : ℝ ↦ Real.sinh (2 * α * x)) t‖ ≤
      (2 * α) ^ q * Real.cosh (2 * α * δ) := by
    rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh (2 * α), Real.norm_eq_abs, abs_mul,
      abs_pow, abs_of_nonneg (mul_nonneg zero_le_two hα)]
    exact mul_le_mul_of_nonneg_left ((abs_iteratedDeriv_sinh_le q _).trans hcosh_le) (by positivity)
  have hcosh_cd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ Real.cosh (2 * α * x)) :=
    Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  have hsinh_cd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ Real.sinh (2 * α * x)) :=
    Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)
  rcases ι with b | ⟨b, ⟨k, j⟩⟩
  · cases b
    · change ‖iteratedDeriv r (fun x : ℝ ↦ ((1 - Real.cosh (2 * α * x) : ℝ) : ℂ)) t‖ ≤ _
      rw [iteratedDeriv_ofReal_comp (contDiff_const.sub hcosh_cd), Complex.norm_real]
      rcases r with _ | r
      · simp only [iteratedDeriv_zero, coshDefectDerivBound, ↓reduceIte, Real.norm_eq_abs]
        have h1 : 1 ≤ Real.cosh (2 * α * t) := Real.one_le_cosh _
        rw [abs_of_nonpos (by linarith), neg_sub]
        linarith
      · simp only [coshDefectDerivBound, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        rw [iteratedDeriv_const_sub (Nat.succ_pos r)]
        change ‖iteratedDeriv (r + 1) (fun x ↦ -(Real.cosh (2 * α * x))) t‖ ≤ _
        rw [iteratedDeriv_fun_neg, norm_neg]
        exact hq_cosh (r + 1)
    · change ‖iteratedDeriv r (fun x : ℝ ↦ ((Real.sinh (2 * α * x) : ℝ) : ℂ)) t‖ ≤ _
      rw [iteratedDeriv_ofReal_comp hsinh_cd, Complex.norm_real]
      rcases r with _ | r
      · simp only [iteratedDeriv_zero, coshDefectDerivBound, ↓reduceIte, Real.norm_eq_abs]
        exact abs_sinh_le_sinh_of_abs_le h2αt
      · simp only [coshDefectDerivBound, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact hq_sinh (r + 1)
  · have hpow_le (m : ℕ) : ‖iteratedDeriv m (fun x : ℝ ↦ x ^ (k + 1 + j.val)) t‖ ≤
        ((k + 1 + j.val).descFactorial m : ℝ) * δ ^ (k + 1 + j.val - m) := by
      rw [iteratedDeriv_pow, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht _) (Nat.cast_nonneg _)
    have hmul_bound (H : ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
        (hHq : ∀ q, ‖iteratedDeriv q H t‖ ≤ (2 * α) ^ q * Real.cosh (2 * α * δ)) (c : ℝ) :
        ‖iteratedDeriv r (fun x : ℝ ↦ ((c * H x * x ^ (k + 1 + j.val) : ℝ) : ℂ)) t‖ ≤
          |c| * Real.cosh (2 * α * δ) * ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * (2 * α) ^ q *
            (((k + 1 + j.val).descFactorial (r - q) : ℝ) * δ ^ (k + 1 + j.val - (r - q))) := by
      rw [@iteratedDeriv_ofReal_comp r (fun x : ℝ ↦ c * H x * x ^ (k + 1 + j.val))
          ((contDiff_const.mul hH).mul (contDiff_id.pow _)), Complex.norm_real]
      have heq : (fun x : ℝ ↦ c * H x * x ^ (k + 1 + j.val)) =
          fun x ↦ c * ((H * (fun y : ℝ ↦ y ^ (k + 1 + j.val))) x) := funext fun x ↦ by
        dsimp only [Pi.mul_apply]; ring
      have hpow_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ ↦ y ^ (k + 1 + j.val)) := contDiff_id.pow _
      rw [heq, iteratedDeriv_const_mul_field,
        iteratedDeriv_mul (hH.contDiffAt.of_le (by simp)) (hpow_cd.contDiffAt.of_le (by simp))]
      calc ‖c * ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * iteratedDeriv q H t *
              iteratedDeriv (r - q) (fun x : ℝ ↦ x ^ (k + 1 + j.val)) t‖
          = |c| * ‖∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * iteratedDeriv q H t *
              iteratedDeriv (r - q) (fun x : ℝ ↦ x ^ (k + 1 + j.val)) t‖ := by
            rw [norm_mul, Real.norm_eq_abs]
        _ ≤ |c| * ∑ q ∈ Finset.range (r + 1), ‖(r.choose q : ℝ) * iteratedDeriv q H t *
              iteratedDeriv (r - q) (fun x : ℝ ↦ x ^ (k + 1 + j.val)) t‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
        _ ≤ |c| * ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * ((2 * α) ^ q * Real.cosh (2 * α * δ)) *
              (((k + 1 + j.val).descFactorial (r - q) : ℝ) * δ ^ (k + 1 + j.val - (r - q))) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ ↦ ?_) (abs_nonneg _)
            rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hHq q) (Nat.cast_nonneg _))
              (hpow_le (r - q)) (norm_nonneg _) (by positivity)
        _ = _ := by
            rw [mul_assoc |c|]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ ↦ by ring
    cases b
    · have hc : |(-Ring.choose (s / 2) (k + 1) * ((k + 1).choose j.val : ℝ))| =
          |Ring.choose (s / 2) (k + 1)| * ((k + 1).choose j.val : ℝ) := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1).choose j.val : ℝ))]
      have hsub := hmul_bound (fun x ↦ Real.cosh (2 * α * x)) hcosh_cd hq_cosh
        (-Ring.choose (s / 2) (k + 1) * ((k + 1).choose j.val : ℝ))
      refine hsub.trans_eq ?_
      simp only [coshDefectDerivBound, hc, mul_assoc]
    · have hc : |(Ring.choose (s / 2) (k + 1) * ((k + 1).choose j.val : ℝ))| =
          |Ring.choose (s / 2) (k + 1)| * ((k + 1).choose j.val : ℝ) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1).choose j.val : ℝ))]
      have hsub := hmul_bound (fun x ↦ Real.sinh (2 * α * x)) hsinh_cd hq_sinh
        (Ring.choose (s / 2) (k + 1) * ((k + 1).choose j.val : ℝ))
      refine hsub.trans_eq ?_
      simp only [coshDefectDerivBound, hc, mul_assoc]

private lemma coshDefectDerivBound_inr_block_le {α s δ : ℝ} (hα : 0 ≤ α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (r : ℕ) (b : Bool) (k : ℕ) :
    ∑ j : Fin (k + 2), coshDefectDerivBound α s δ r (Sum.inr (b, ⟨k, j⟩)) ≤
      Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) *
        (∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * (2 * α) ^ q) *
        ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r) * (4 : ℝ) ^ k) := by
  let C_α := Real.cosh (2 * α * δ)
  let N_s := Nat.ceil |s / 2|
  let Q_r := ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * (2 * α) ^ q
  have hQ_r : 0 ≤ Q_r := Finset.sum_nonneg fun q _ ↦ by positivity
  have hch_s : |Ring.choose (s / 2) (k + 1)| ≤ (2 : ℝ) ^ (N_s + 1) * (2 : ℝ) ^ k := by
    refine (abs_ring_choose_le (s / 2) (k + 1)).trans_eq ?_
    rw [show N_s + (k + 1) = (N_s + 1) + k by ring, pow_add]
  have hsum_j : ∑ j : Fin (k + 2), ((k + 1).choose j.val : ℝ) = (2 : ℝ) * (2 : ℝ) ^ k := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ((k + 1).choose j : ℝ)) (k + 2)]
    norm_cast
    rw [Nat.sum_range_choose, pow_succ']
  have hq_term (j : Fin (k + 2)) (q : ℕ) (hq : q ∈ Finset.range (r + 1)) :
      ((k + 1 + j.val).descFactorial (r - q) : ℝ) * δ ^ (k + 1 + j.val - (r - q)) ≤
        (2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r) := by
    have _ := Finset.mem_range.mp hq
    have hj : j.val ≤ k + 1 := Nat.lt_succ_iff.mp j.isLt
    have hdf : ((k + 1 + j.val).descFactorial (r - q) : ℝ) ≤ (2 * ((k : ℝ) + 1)) ^ r := by
      have h1 : ((k + 1 + j.val).descFactorial (r - q) : ℝ) ≤ ((k + 1 + j.val : ℕ) : ℝ) ^ (r - q) := by
        exact_mod_cast Nat.descFactorial_le_pow (k + 1 + j.val) (r - q)
      have h2 : ((k + 1 + j.val : ℕ) : ℝ) ^ (r - q) ≤ (2 * ((k : ℝ) + 1)) ^ (r - q) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        have hnat : ((k + 1 + j.val : ℕ) : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : k + 1 + j.val ≤ 2 * (k + 1))
        simpa using hnat
      have h3 : (2 * ((k : ℝ) + 1)) ^ (r - q) ≤ (2 * ((k : ℝ) + 1)) ^ r :=
        pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (Nat.sub_le r q)
      exact h1.trans (h2.trans h3)
    have hpow : δ ^ (k + 1 + j.val - (r - q)) ≤ δ ^ (k + 1 - r) :=
      pow_le_pow_of_le_one hδ0 hδ1 (by omega)
    exact mul_le_mul hdf hpow (by positivity) (by positivity)
  have hterm (j : Fin (k + 2)) :
      coshDefectDerivBound α s δ r (Sum.inr (b, ⟨k, j⟩)) ≤
        |Ring.choose (s / 2) (k + 1)| * ((k + 1).choose j.val : ℝ) * C_α *
          (Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r))) := by
    simp only [coshDefectDerivBound]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * (2 * α) ^ q *
            (((k + 1 + j.val).descFactorial (r - q) : ℝ) * δ ^ (k + 1 + j.val - (r - q)))
        ≤ ∑ q ∈ Finset.range (r + 1), ((r.choose q : ℝ) * (2 * α) ^ q) *
            ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r)) :=
          Finset.sum_le_sum fun q hq ↦ mul_le_mul_of_nonneg_left (hq_term j q hq) (by positivity)
      _ = Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r)) := (Finset.sum_mul _ _ _).symm
  calc ∑ j : Fin (k + 2), coshDefectDerivBound α s δ r (Sum.inr (b, ⟨k, j⟩))
      ≤ ∑ j : Fin (k + 2), |Ring.choose (s / 2) (k + 1)| * ((k + 1).choose j.val : ℝ) * C_α *
          (Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r))) :=
        Finset.sum_le_sum fun j _ ↦ hterm j
    _ = (∑ j : Fin (k + 2), ((k + 1).choose j.val : ℝ)) *
          (|Ring.choose (s / 2) (k + 1)| * C_α * Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r))) := by
        rw [Finset.sum_mul Finset.univ]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        dsimp only [Q_r]; ring
    _ = ((2 : ℝ) * (2 : ℝ) ^ k) *
          (|Ring.choose (s / 2) (k + 1)| * C_α * Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r))) := by
        rw [hsum_j]
    _ ≤ ((2 : ℝ) * (2 : ℝ) ^ k) *
          (((2 : ℝ) ^ (N_s + 1) * (2 : ℝ) ^ k) * C_α * Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hch_s (Real.cosh_pos _).le) hQ_r) (by positivity)
    _ = C_α * (2 : ℝ) ^ (N_s + 2) * Q_r * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r) * (4 : ℝ) ^ k) := by
        have h4 : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
          rw [← mul_pow]; norm_num
        rw [show (2 : ℝ) ^ (N_s + 2) = 2 * (2 : ℝ) ^ (N_s + 1) by rw [pow_succ']]
        calc (2 : ℝ) * (2 : ℝ) ^ k * ((2 : ℝ) ^ (N_s + 1) * (2 : ℝ) ^ k * C_α * Q_r *
              ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r)))
            = C_α * (2 * (2 : ℝ) ^ (N_s + 1)) * Q_r *
                ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r) * ((2 : ℝ) ^ k * (2 : ℝ) ^ k)) := by ring
          _ = _ := by rw [h4]

lemma summable_coshDefectDerivBound {α s δ : ℝ} (hα : 0 ≤ α) (_hs : 0 ≤ s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 32) (r : ℕ) :
    Summable (coshDefectDerivBound α s δ r) := by
  have hδle1 : δ ≤ 1 := hδ1.trans (by norm_num)
  let C_pre : ℝ := Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) *
    (∑ q ∈ Finset.range (r + 1), (r.choose q : ℝ) * (2 * α) ^ q)
  have hC_pre : 0 ≤ C_pre := by positivity
  have h_major : Summable (fun k : ℕ ↦
      C_pre * ((2 * ((k : ℝ) + 1)) ^ r * δ ^ (k + 1 - r) * (4 : ℝ) ^ k)) := by
    rw [← summable_nat_add_iff r]
    have h4δ : ‖4 * δ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
    have hgeom : Summable (fun m : ℕ ↦ ((m : ℝ) ^ r * (4 * δ) ^ m)) :=
      summable_pow_mul_geometric_of_norm_lt_one r h4δ
    have hgeom1 : Summable (fun m : ℕ ↦ ((m + 1 : ℝ) ^ r * (4 * δ) ^ m)) := by
      have hshift : Summable (fun m : ℕ ↦ (((m + 1 : ℕ) : ℝ) ^ r * (4 * δ) ^ (m + 1))) :=
        (summable_nat_add_iff (f := fun m : ℕ ↦ ((m : ℝ) ^ r * (4 * δ) ^ m)) 1).mpr hgeom
      have hdiv : Summable (fun m : ℕ ↦ (4 * δ) * (((m : ℝ) + 1) ^ r * (4 * δ) ^ m)) := by
        refine hshift.congr fun m ↦ ?_
        push_cast; rw [pow_succ']; ring
      by_cases hδz : δ = 0
      · subst hδz
        refine summable_of_ne_finset_zero (s := {0}) fun m hm ↦ ?_
        have hm0 : m ≠ 0 := by simpa using hm
        simp [zero_pow hm0]
      · have hpos : 0 < 4 * δ := by positivity
        exact (hdiv.mul_left (4 * δ)⁻¹).congr fun m ↦ by field_simp
    refine (hgeom1.mul_left (C_pre * (2 * ((r : ℝ) + 1)) ^ r * δ * (4 : ℝ) ^ r)).of_nonneg_of_le
      (fun m ↦ by positivity) fun m ↦ ?_
    have hshift : (m + r : ℕ) + 1 - r = m + 1 := by omega
    have hmr : ((m + r : ℕ) : ℝ) + 1 ≤ ((r : ℝ) + 1) * ((m : ℝ) + 1) := by
      push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) r]
    rw [hshift, pow_add (4 : ℝ) m r, pow_succ' δ m]
    calc C_pre * ((2 * (((m + r : ℕ) : ℝ) + 1)) ^ r * (δ * δ ^ m) * ((4 : ℝ) ^ m * (4 : ℝ) ^ r))
        ≤ C_pre * ((2 * (((r : ℝ) + 1) * ((m : ℝ) + 1))) ^ r * (δ * δ ^ m) * ((4 : ℝ) ^ m * (4 : ℝ) ^ r)) := by
          gcongr
      _ = C_pre * (2 * ((r : ℝ) + 1)) ^ r * δ * (4 : ℝ) ^ r * (((m : ℝ) + 1) ^ r * (4 * δ) ^ m) := by
          rw [show (2 : ℝ) * (((r : ℝ) + 1) * ((m : ℝ) + 1)) = (2 * ((r : ℝ) + 1)) * ((m : ℝ) + 1) by ring,
            mul_pow, mul_pow, mul_pow (4 : ℝ) δ m]
          ring
  have h_sig (b : Bool) : Summable (fun p : (Σ k : ℕ, Fin (k + 2)) ↦
      coshDefectDerivBound α s δ r (Sum.inr (b, p))) := by
    refine (summable_sigma_of_nonneg (fun _ ↦ coshDefectDerivBound_nonneg hα hδ0 r _)).mpr
      ⟨fun _ ↦ Summable.of_finite, ?_⟩
    rw [show (fun k : ℕ ↦ ∑' j : Fin (k + 2), coshDefectDerivBound α s δ r (Sum.inr (b, ⟨k, j⟩))) =
        fun k : ℕ ↦ ∑ j : Fin (k + 2), coshDefectDerivBound α s δ r (Sum.inr (b, ⟨k, j⟩)) from
      funext fun k ↦ tsum_fintype _]
    exact h_major.of_nonneg_of_le
      (fun k ↦ Finset.sum_nonneg fun j _ ↦ coshDefectDerivBound_nonneg hα hδ0 r _)
      (fun k ↦ coshDefectDerivBound_inr_block_le hα hδ0 hδle1 r b k)
  have h_inr : Summable (fun p : Bool × Σ k : ℕ, Fin (k + 2) ↦
      coshDefectDerivBound α s δ r (Sum.inr p)) :=
    (summable_prod_of_nonneg (fun _ ↦ coshDefectDerivBound_nonneg hα hδ0 r _)).mpr
      ⟨fun b ↦ h_sig b, Summable.of_finite⟩
  exact Summable.sum (coshDefectDerivBound α s δ r) Summable.of_finite h_inr

private lemma tsum_coshDefectDerivBound_inl_zero {α s δ : ℝ} :
    ∑' b : Bool, coshDefectDerivBound α s δ 0 (Sum.inl b) =
      (Real.cosh (2 * α * δ) - 1) + Real.sinh (2 * α * δ) := by
  rw [tsum_fintype, Fintype.sum_bool, add_comm]
  simp only [coshDefectDerivBound, ↓reduceIte]

private lemma tsum_coshDefectDerivBound_inr_b_zero {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hδ0 : 0 < δ) (hδ32 : δ ≤ 1 / 32) (b : Bool) :
    ∑' p : Σ k : ℕ, Fin (k + 2), coshDefectDerivBound α s δ 0 (Sum.inr (b, p)) ≤
      2 * (Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) * δ) := by
  have h_sig : Summable (fun p : Σ k : ℕ, Fin (k + 2) ↦
      coshDefectDerivBound α s δ 0 (Sum.inr (b, p))) :=
    (summable_coshDefectDerivBound hα hs hδ0.le hδ32 0).comp_injective
      (fun _ _ h ↦ by cases h; rfl)
  let C₀ : ℝ := Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) * δ
  have hC₀ : 0 ≤ C₀ := by positivity
  have h4δ0 : 0 ≤ 4 * δ := by positivity
  have h4δ1 : 4 * δ < 1 := by linarith
  have h_k : HasSum (fun k : ℕ ↦ ∑ j : Fin (k + 2), coshDefectDerivBound α s δ 0 (Sum.inr (b, ⟨k, j⟩)))
      (∑' p : Σ k : ℕ, Fin (k + 2), coshDefectDerivBound α s δ 0 (Sum.inr (b, p))) :=
    h_sig.hasSum.sigma fun _ ↦ hasSum_fintype _
  have hk_le (k : ℕ) : (∑ j : Fin (k + 2), coshDefectDerivBound α s δ 0 (Sum.inr (b, ⟨k, j⟩))) ≤
      C₀ * (4 * δ) ^ k := by
    have hb := coshDefectDerivBound_inr_block_le (s := s) hα hδ0.le (hδ32.trans (by norm_num)) 0 b k
    refine hb.trans_eq ?_
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.choose_self,
      Nat.cast_one, mul_one, Nat.sub_zero]
    rw [pow_succ' δ k, mul_pow (4 : ℝ) δ k]
    dsimp only [C₀]
    ring
  have hgeom : HasSum (fun k : ℕ ↦ C₀ * (4 * δ) ^ k) (C₀ * (1 - 4 * δ)⁻¹) :=
    (hasSum_geometric_of_lt_one h4δ0 h4δ1).mul_left C₀
  refine (hasSum_le hk_le h_k hgeom).trans ?_
  have hinv : (1 - 4 * δ)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    linarith
  exact (mul_le_mul_of_nonneg_left hinv hC₀).trans_eq (mul_comm C₀ 2)

private def boolProdEquivSum (β : Type*) : β ⊕ β ≃ Bool × β where
  toFun := Sum.elim (fun q ↦ (true, q)) (fun q ↦ (false, q))
  invFun p := if p.1 then Sum.inl p.2 else Sum.inr p.2
  left_inv x := by cases x <;> rfl
  right_inv p := by rcases p with ⟨_ | _, _⟩ <;> rfl

private lemma tsum_bool_prod_eq {β : Type*} (f : Bool × β → ℝ)
    (ht : Summable fun q ↦ f (true, q)) (hf : Summable fun q ↦ f (false, q)) :
    ∑' p : Bool × β, f p = (∑' q, f (true, q)) + ∑' q, f (false, q) := by
  rw [← (boolProdEquivSum β).tsum_eq]
  exact ht.tsum_sum hf

private lemma tsum_coshDefectDerivBound_inr_zero {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hδ0 : 0 < δ) (hδ32 : δ ≤ 1 / 32) :
    ∑' p : Bool × Σ k : ℕ, Fin (k + 2), coshDefectDerivBound α s δ 0 (Sum.inr p) ≤
      4 * Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) * δ := by
  have hsum := summable_coshDefectDerivBound hα hs hδ0.le hδ32 0
  have h_sig (b : Bool) : Summable (fun p : Σ k : ℕ, Fin (k + 2) ↦
      coshDefectDerivBound α s δ 0 (Sum.inr (b, p))) :=
    hsum.comp_injective (Sum.inr_injective.comp (Prod.mk_right_injective b))
  have heq := tsum_bool_prod_eq (fun p : Bool × Σ k : ℕ, Fin (k + 2) ↦
      coshDefectDerivBound α s δ 0 (Sum.inr p)) (h_sig true) (h_sig false)
  rw [heq]
  have h1 := tsum_coshDefectDerivBound_inr_b_zero hα hs hδ0 hδ32 true
  have h2 := tsum_coshDefectDerivBound_inr_b_zero hα hs hδ0 hδ32 false
  linarith

private lemma tsum_coshDefectDerivBound_zero_le {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hδ0 : 0 < δ) (hδ32 : δ ≤ 1 / 32) :
    ∑' ι, coshDefectDerivBound α s δ 0 ι ≤
      (Real.cosh (2 * α * δ) - 1) + Real.sinh (2 * α * δ) +
        4 * Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) * δ := by
  have hsum_all := summable_coshDefectDerivBound hα hs hδ0.le hδ32 0
  have hsum_inl : Summable (fun b : Bool ↦ coshDefectDerivBound α s δ 0 (Sum.inl b)) :=
    hsum_all.comp_injective Sum.inl_injective
  have hsum_inr : Summable (fun p : Bool × Σ k : ℕ, Fin (k + 2) ↦
      coshDefectDerivBound α s δ 0 (Sum.inr p)) :=
    hsum_all.comp_injective Sum.inr_injective
  rw [hsum_inl.tsum_sum hsum_inr, tsum_coshDefectDerivBound_inl_zero (α := α) (s := s) (δ := δ)]
  exact add_le_add le_rfl (tsum_coshDefectDerivBound_inr_zero hα hs hδ0 hδ32)

lemma exists_delta_coshDefect_tsum_le_half {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 32 ∧ (∑' ι, coshDefectDerivBound α s δ₀ 0 ι) ≤ 1 / 2 := by
  let bound (δ : ℝ) : ℝ :=
    (Real.cosh (2 * α * δ) - 1) + Real.sinh (2 * α * δ) +
      4 * Real.cosh (2 * α * δ) * (2 : ℝ) ^ (Nat.ceil |s / 2| + 2) * δ
  have hcont : Continuous bound := by
    have hc : Continuous (fun δ : ℝ ↦ Real.cosh (2 * α * δ)) :=
      Real.continuous_cosh.comp (continuous_const.mul continuous_id)
    have hsi : Continuous (fun δ : ℝ ↦ Real.sinh (2 * α * δ)) :=
      Real.continuous_sinh.comp (continuous_const.mul continuous_id)
    exact ((hc.sub continuous_const).add hsi).add (((continuous_const.mul hc).mul continuous_const).mul continuous_id)
  have hbound0 : bound 0 = 0 := by simp [bound]
  obtain ⟨d, hd0, hd⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (1 / 2 : ℝ) (by norm_num)
  let δ₀ : ℝ := min (1 / 32) (d / 2)
  have hδ0 : 0 < δ₀ := lt_min (by norm_num) (half_pos hd0)
  have hδ32 : δ₀ ≤ 1 / 32 := min_le_left _ _
  have hδd : dist δ₀ 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
    exact (min_le_right _ _).trans_lt (half_lt_self hd0)
  have hbound_le : bound δ₀ ≤ 1 / 2 := by
    have h1 := hd hδd
    rw [Real.dist_eq, hbound0, sub_zero] at h1
    exact (le_abs_self _).trans h1.le
  exact ⟨δ₀, hδ0, hδ32, (tsum_coshDefectDerivBound_zero_le hα hs hδ0 hδ32).trans hbound_le⟩

lemma hasSum_coshDefect_pointwise {α s x t : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (ht : |t| ≤ 1 / 32) :
    HasSum (fun ι ↦ coshDefectX α ι x * coshDefectT α s ι t)
      ((1 - coshSobolevDensity α s (x - t) / coshSobolevDensity α s x : ℝ) : ℂ) := by
  let f : CoshDefectIndex → ℂ := fun ι ↦ coshDefectX α ι x * coshDefectT α s ι t
  have hnorm_le (ι : CoshDefectIndex) : ‖f ι‖ ≤ coshDefectDerivBound α s (1 / 32) 0 ι := by
    dsimp only [f]
    rw [norm_mul]
    have hT := norm_iteratedDeriv_coshDefectT_le (s := s) hα (by norm_num : (0 : ℝ) ≤ 1 / 32) 0 ι ht
    rw [iteratedDeriv_zero] at hT
    exact (mul_le_mul (norm_coshDefectX_le_one α ι x) hT (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hbd_sum : Summable (coshDefectDerivBound α s (1 / 32) 0) :=
    summable_coshDefectDerivBound hα hs (by norm_num) le_rfl 0
  have hf_sum : Summable f :=
    hbd_sum.of_norm_bounded hnorm_le
  refine hf_sum.hasSum_iff.mpr ?_
  have hf_inr : Summable (fun p : Bool × Σ k : ℕ, Fin (k + 2) ↦ f (Sum.inr p)) :=
    hf_sum.comp_injective Sum.inr_injective
  have hf_sig (b : Bool) : Summable (fun p : Σ k : ℕ, Fin (k + 2) ↦ f (Sum.inr (b, p))) :=
    hf_inr.comp_injective fun _ _ h ↦ by cases h; rfl
  let w : ℝ := (-2 * x * t + t ^ 2) / (1 + x ^ 2)
  have hden : 0 < 1 + x ^ 2 := by positivity
  have hw_lt : |w| < 1 := by
    have h1 : |-2 * x / (1 + x ^ 2)| ≤ 1 := abs_two_mul_div_one_add_sq x
    have h2 : |1 / (1 + x ^ 2)| ≤ 1 := abs_one_div_one_add_sq x
    have hw_eq : w = (-2 * x / (1 + x ^ 2)) * t + (1 / (1 + x ^ 2)) * t ^ 2 := by
      dsimp only [w]; field_simp
    calc |w| = |(-2 * x / (1 + x ^ 2)) * t + (1 / (1 + x ^ 2)) * t ^ 2| := by rw [hw_eq]
      _ ≤ |(-2 * x / (1 + x ^ 2)) * t| + |(1 / (1 + x ^ 2)) * t ^ 2| := abs_add_le _ _
      _ = |-2 * x / (1 + x ^ 2)| * |t| + |1 / (1 + x ^ 2)| * t ^ 2 := by
          rw [abs_mul, abs_mul, abs_pow, sq_abs]
      _ ≤ 1 * (1 / 32) + 1 * (1 / 32) ^ 2 := by
          refine add_le_add (mul_le_mul h1 ht (abs_nonneg _) zero_le_one)
            (mul_le_mul h2 (by nlinarith [abs_nonneg t, sq_abs t]) (sq_nonneg _) zero_le_one)
      _ < 1 := by norm_num
  have hbin : HasSum (fun k : ℕ ↦ Ring.choose (s / 2) k * w ^ k) ((1 + w) ^ (s / 2)) :=
    hasSum_one_add_rpow (s / 2) w hw_lt
  have hbin_shift : ∑' k : ℕ, Ring.choose (s / 2) (k + 1) * w ^ (k + 1) = (1 + w) ^ (s / 2) - 1 := by
    have h0 : ∑' k : ℕ, Ring.choose (s / 2) k * w ^ k = (1 + w) ^ (s / 2) := hbin.tsum_eq
    rw [hbin.summable.tsum_eq_zero_add] at h0
    simp only [Ring.choose_zero_right, pow_zero, mul_one] at h0
    linarith
  have hw_add : 1 + w = (1 + (x - t) ^ 2) / (1 + x ^ 2) := by
    dsimp only [w]
    field_simp
    ring
  have hfin_j (k : ℕ) :
      ∑ j : Fin (k + 2), ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val) *
          (((k + 1).choose j.val : ℝ) * t ^ (k + 1 + j.val)) = w ^ (k + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j) * (1 / (1 + x ^ 2)) ^ j) *
      (((k + 1).choose j : ℝ) * t ^ (k + 1 + j))) (k + 2)]
    have hterm (j : ℕ) (_hj : j ≤ k + 1) :
        ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j) * (1 / (1 + x ^ 2)) ^ j) *
            (((k + 1).choose j : ℝ) * t ^ (k + 1 + j)) =
          ((1 / (1 + x ^ 2)) * t ^ 2) ^ j * ((-2 * x / (1 + x ^ 2)) * t) ^ (k + 1 - j) *
            ((k + 1).choose j : ℝ) := by
      have hexp : k + 1 + j = (k + 1 - j) + 2 * j := by omega
      rw [mul_pow, mul_pow, ← pow_mul, hexp, pow_add t (k + 1 - j) (2 * j)]
      ring
    calc ∑ j ∈ Finset.range (k + 2), ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j) * (1 / (1 + x ^ 2)) ^ j) *
            (((k + 1).choose j : ℝ) * t ^ (k + 1 + j))
        = ∑ j ∈ Finset.range (k + 2),
            ((1 / (1 + x ^ 2)) * t ^ 2) ^ j * ((-2 * x / (1 + x ^ 2)) * t) ^ (k + 1 - j) *
              ((k + 1).choose j : ℝ) := by
            refine Finset.sum_congr rfl fun j hj ↦ hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ((1 / (1 + x ^ 2)) * t ^ 2 + (-2 * x / (1 + x ^ 2)) * t) ^ (k + 1) := by
            rw [add_pow]
      _ = w ^ (k + 1) := by
            congr 1; dsimp only [w]; field_simp; ring
  have hsum_inr_false : ∑' p : Σ k : ℕ, Fin (k + 2), f (Sum.inr (false, p)) =
      ((-Real.cosh (2 * α * t) * ((1 + w) ^ (s / 2) - 1) : ℝ) : ℂ) := by
    rw [(hf_sig false).tsum_sigma' (fun _ ↦ Summable.of_finite)]
    have hk_eq (k : ℕ) : (∑' j : Fin (k + 2), f (Sum.inr (false, ⟨k, j⟩))) =
        Complex.ofRealCLM (-Real.cosh (2 * α * t) * (Ring.choose (s / 2) (k + 1) * w ^ (k + 1))) := by
      rw [tsum_fintype]
      have hsub : ∑ j : Fin (k + 2), f (Sum.inr (false, ⟨k, j⟩)) =
          ((-Real.cosh (2 * α * t) * Ring.choose (s / 2) (k + 1) *
            ∑ j : Fin (k + 2), ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val) *
              (((k + 1).choose j.val : ℝ) * t ^ (k + 1 + j.val)) : ℝ) : ℂ) := by
        simp only [f, coshDefectX, coshDefectT, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hsub, hfin_j k, mul_assoc]
      rfl
    simp_rw [hk_eq]
    rw [← Complex.ofRealCLM.map_tsum]
    · change Complex.ofRealCLM (∑' k : ℕ, (-Real.cosh (2 * α * t) * (Ring.choose (s / 2) (k + 1) * w ^ (k + 1)))) = _
      rw [tsum_mul_left, hbin_shift]
      rfl
    · have hsum_w : Summable (fun k : ℕ ↦ Ring.choose (s / 2) (k + 1) * w ^ (k + 1)) :=
        (summable_nat_add_iff 1).mpr hbin.summable
      exact hsum_w.mul_left _
  have hsum_inr_true : ∑' p : Σ k : ℕ, Fin (k + 2), f (Sum.inr (true, p)) =
      ((Real.tanh (2 * α * x) * Real.sinh (2 * α * t) * ((1 + w) ^ (s / 2) - 1) : ℝ) : ℂ) := by
    rw [(hf_sig true).tsum_sigma' (fun _ ↦ Summable.of_finite)]
    have hk_eq (k : ℕ) : (∑' j : Fin (k + 2), f (Sum.inr (true, ⟨k, j⟩))) =
        Complex.ofRealCLM (Real.tanh (2 * α * x) * Real.sinh (2 * α * t) * (Ring.choose (s / 2) (k + 1) * w ^ (k + 1))) := by
      rw [tsum_fintype]
      have hsub : ∑ j : Fin (k + 2), f (Sum.inr (true, ⟨k, j⟩)) =
          ((Real.tanh (2 * α * x) * Real.sinh (2 * α * t) * Ring.choose (s / 2) (k + 1) *
            ∑ j : Fin (k + 2), ((-2 * x / (1 + x ^ 2)) ^ (k + 1 - j.val) * (1 / (1 + x ^ 2)) ^ j.val) *
              (((k + 1).choose j.val : ℝ) * t ^ (k + 1 + j.val)) : ℝ) : ℂ) := by
        simp only [f, coshDefectX, coshDefectT, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hsub, hfin_j k, mul_assoc]
      rfl
    simp_rw [hk_eq]
    rw [← Complex.ofRealCLM.map_tsum]
    · change Complex.ofRealCLM (∑' k : ℕ, (Real.tanh (2 * α * x) * Real.sinh (2 * α * t) *
        (Ring.choose (s / 2) (k + 1) * w ^ (k + 1)))) = _
      rw [tsum_mul_left, hbin_shift]
      rfl
    · have hsum_w : Summable (fun k : ℕ ↦ Ring.choose (s / 2) (k + 1) * w ^ (k + 1)) :=
        (summable_nat_add_iff 1).mpr hbin.summable
      exact hsum_w.mul_left _
  have hsum_inl : ∑' b : Bool, f (Sum.inl b) =
      (((1 - Real.cosh (2 * α * t)) + Real.tanh (2 * α * x) * Real.sinh (2 * α * t) : ℝ) : ℂ) := by
    rw [tsum_fintype, Fintype.sum_bool, add_comm]
    simp [f, coshDefectX, coshDefectT]
  rw [(hf_sum.comp_injective Sum.inl_injective).tsum_sum hf_inr, hsum_inl,
    hf_inr.tsum_prod' (fun b ↦ hf_sig b), tsum_fintype, Fintype.sum_bool,
    add_comm (∑' p, f (Sum.inr (true, p))), hsum_inr_false, hsum_inr_true]
  have hcosh_x : Real.cosh (2 * α * x) ≠ 0 := (Real.cosh_pos _).ne'
  have hsub_cosh : Real.cosh (2 * α * (x - t)) =
      Real.cosh (2 * α * x) * Real.cosh (2 * α * t) - Real.sinh (2 * α * x) * Real.sinh (2 * α * t) := by
    rw [show 2 * α * (x - t) = 2 * α * x - 2 * α * t by ring, Real.cosh_sub]
  have htanh : Real.tanh (2 * α * x) = Real.sinh (2 * α * x) / Real.cosh (2 * α * x) :=
    Real.tanh_eq_sinh_div_cosh _
  have hrpow : (1 + w) ^ (s / 2) = (1 + (x - t) ^ 2) ^ (s / 2) / (1 + x ^ 2) ^ (s / 2) := by
    rw [hw_add, Real.div_rpow (by positivity) hden.le]
  have hrpow_pos : (0 : ℝ) < (1 + x ^ 2) ^ (s / 2) := by positivity
  have hreal_id :
      ((1 - Real.cosh (2 * α * t)) + Real.tanh (2 * α * x) * Real.sinh (2 * α * t)) +
        (-Real.cosh (2 * α * t) * ((1 + w) ^ (s / 2) - 1) +
          Real.tanh (2 * α * x) * Real.sinh (2 * α * t) * ((1 + w) ^ (s / 2) - 1)) =
      1 - coshSobolevDensity α s (x - t) / coshSobolevDensity α s x := by
    simp only [coshSobolevDensity]
    rw [hrpow, hsub_cosh, htanh]
    field_simp [hcosh_x, hrpow_pos.ne']
    ring
  rw [← hreal_id]
  push_cast
  ring

section DefectOperatorHasSum

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

private lemma lintegral_coshSobolevMeasure_defect {F : Type*} [Field F] [NumberField F]
    {α s : ℝ} {f : IdeleClassGroup (𝓞 F) F → ℝ≥0∞}
    (hf : AEMeasurable f (coshSobolevMeasure F α s)) :
    ∫⁻ x : IdeleClassGroup (𝓞 F) F, f x ∂(coshSobolevMeasure F α s) =
      ∫⁻ x : IdeleClassGroup (𝓞 F) F,
        ENNReal.ofReal (coshSobolevDensity α s (logIdeleClassNorm F x)) * f x
          ∂(ideleClassTamagawaMeasure F) := by
  rw [coshSobolevMeasure_eq_withDensity] at hf ⊢
  exact lintegral_withDensity_eq_lintegral_mul₀'
    ((continuous_coshSobolevDensity α s).measurable.comp measurable_logNorm).ennreal_ofReal.aemeasurable
    hf

private lemma ae_integrable_bruhat_mul_u {F : Type*} [Field F] [NumberField F]
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (u_c : CoshIntervalSobolev F α s) :
    ∀ᵐ g ∂(ideleClassTamagawaMeasure F),
      Integrable (fun y : IdeleClassGroup (𝓞 F) F ↦ ψ.val y * u_c (y⁻¹ * g))
        (ideleClassTamagawaMeasure F) := by
  let μ𝔽 := ideleClassTamagawaMeasure F
  let logNorm := logIdeleClassNorm F
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have : SFinite μ𝔽 := inferInstance
  let u := coshIntervalToLp F α s u_c
  have hu_sm := Lp.stronglyMeasurable u
  have hψ_cont : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  obtain ⟨C, hC⟩ := ψ.property.2.exists_bound_of_continuousOn continuous_logNorm.continuousOn
  let δ : ℝ := max 0 C
  have hδ : 0 ≤ δ := le_max_left _ _
  have hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ := fun y hy ↦ by
    have h := hC y (subset_tsupport _ hy)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  let K_adj : ℝ → ℝ → ℂ := fun _ _ ↦ 1
  have hKm : Measurable (uncurry K_adj) := measurable_const
  let Iraw : IdeleClassGroup (𝓞 F) F → ℂ :=
    fun g ↦ ∫ y : IdeleClassGroup (𝓞 F) F, ψ.val y * K_adj (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽
  -- Instead compute the L2(cosh) finiteness directly via `lintegral_prod`:
  let wd : IdeleClassGroup (𝓞 F) F → ℝ≥0∞ := fun g ↦ ENNReal.ofReal (coshSobolevDensity α s (logNorm g))
  have hwd_m : Measurable wd :=
    ((continuous_coshSobolevDensity α s).measurable.comp measurable_logNorm).ennreal_ofReal
  let L₁ : ℝ := ∫ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ ∂μ𝔽
  have hL₁_enn : (∫⁻ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ₑ ∂μ𝔽) = ENNReal.ofReal L₁ :=
    (ofReal_integral_norm_eq_lintegral_eNorm (hψ_cont.integrable_of_hasCompactSupport ψ.property.2)).symm
  let Csh : ℝ := Real.exp (2 * α * δ) * (1 + δ) ^ s
  have hCsh : 0 ≤ Csh := by positivity
  let ν := coshSobolevMeasure F α s
  have hm_joint : AEMeasurable (fun p : IdeleClassGroup (𝓞 F) F × IdeleClassGroup (𝓞 F) F ↦
      wd p.1 * (‖ψ.val p.2‖ₑ * ‖u (p.2⁻¹ * p.1)‖ₑ ^ 2)) ((μ𝔽).prod μ𝔽) :=
    ((hwd_m.comp measurable_fst).mul ((hψ_cont.measurable.eNorm.comp measurable_snd).mul
      (((hu_sm.measurable.comp (measurable_snd.inv.mul measurable_fst)).eNorm).pow_const 2))).aemeasurable
  have hm_inner : Measurable (fun g : IdeleClassGroup (𝓞 F) F ↦
      ∫⁻ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) :=
    ((hψ_cont.measurable.eNorm.comp measurable_snd).mul
      (hu_sm.measurable.comp (measurable_snd.inv.mul measurable_fst)).eNorm).lintegral_prod_right'
  have hfin_tot : ∫⁻ g : IdeleClassGroup (𝓞 F) F, wd g *
      (∫⁻ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) ^ 2 ∂μ𝔽 < ⊤ := by
    let νψ : Measure (IdeleClassGroup (𝓞 F) F) := (μ𝔽).withDensity (fun y ↦ ‖ψ.val y‖ₑ)
    have hpt (g : IdeleClassGroup (𝓞 F) F) :
        (∫⁻ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) ^ 2 ≤
          ENNReal.ofReal L₁ * ∫⁻ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := by
      have h1 : ∫⁻ y, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽 = ∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ∂νψ :=
        (lintegral_withDensity_eq_lintegral_mul _ hψ_cont.measurable.eNorm
          (hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm).symm
      have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq νψ (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2)
        (f := fun _ ↦ (1 : ℝ≥0∞)) (g := fun y ↦ ‖u (y⁻¹ * g)‖ₑ) measurable_const.aemeasurable
        ((hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm.aemeasurable)
      have hholder' : ∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ∂νψ ≤
          νψ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) := by
        calc ∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ∂νψ
            = ∫⁻ y, (1 : ℝ≥0∞) * ‖u (y⁻¹ * g)‖ₑ ∂νψ := by simp_rw [one_mul]
          _ ≤ (∫⁻ y, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) *
                (∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) := by
              simpa only [Pi.mul_apply, one_div] using hholder
          _ = νψ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) := by simp
      have hνψ_univ : νψ Set.univ = ENNReal.ofReal L₁ := by
        rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]; exact hL₁_enn
      have hrhs : (∫⁻ y, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) = ∫⁻ y, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := by
        refine (lintegral_withDensity_eq_lintegral_mul _ hψ_cont.measurable.eNorm
          (((hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm).pow_const (2 : ℝ))).trans ?_
        refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
        change ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) = ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2
        rw [ENNReal.rpow_two]
      rw [← h1, hνψ_univ, hrhs] at hholder'
      have hsq := ENNReal.rpow_le_rpow hholder' (by norm_num : (0 : ℝ) ≤ 2)
      rw [ENNReal.rpow_two, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
        ENNReal.rpow_one, ENNReal.rpow_one] at hsq
      exact hsq
    calc ∫⁻ g, wd g * (∫⁻ y, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) ^ 2 ∂μ𝔽
        ≤ ∫⁻ g, wd g * (ENNReal.ofReal L₁ * ∫⁻ y, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽) ∂μ𝔽 :=
          lintegral_mono fun g ↦ mul_le_mul_of_nonneg_left (hpt g) (by positivity)
      _ = ENNReal.ofReal L₁ * ∫⁻ y, ‖ψ.val y‖ₑ * ∫⁻ g, wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 ∂μ𝔽 := by
          have hswap : (∫⁻ g, wd g * (ENNReal.ofReal L₁ * ∫⁻ y, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽) ∂μ𝔽) =
              ENNReal.ofReal L₁ * ∫⁻ g, ∫⁻ y, wd g * (‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2) ∂μ𝔽 ∂μ𝔽 := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
            refine lintegral_congr_ae (ae_of_all _ fun g ↦ ?_)
            dsimp only
            rw [mul_left_comm (wd g)]
            congr 1
            exact (lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne).symm
          rw [hswap]
          congr 1
          rw [lintegral_lintegral_swap hm_joint]
          refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
          simp_rw [mul_left_comm (wd _)]
          exact lintegral_const_mul' (‖ψ.val y‖ₑ) _ eNorm_lt_top.ne
      _ ≤ ENNReal.ofReal L₁ * ∫⁻ y, ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * eLpNorm (u : _ → ℂ) 2 ν ^ 2) ∂μ𝔽 := by
          refine mul_le_mul_of_nonneg_left (lintegral_mono fun y ↦ ?_) (by positivity)
          by_cases hy : ψ.val y = 0
          · simp [hy]
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hlog_m (a b : IdeleClassGroup (𝓞 F) F) : logNorm (a * b) = logNorm a + logNorm b := by
              change Real.log ((ideleClassNorm F (a * b)).val : ℝ) =
                Real.log ((ideleClassNorm F a).val : ℝ) + Real.log ((ideleClassNorm F b).val : ℝ)
              rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
                (NNReal.coe_ne_zero.2 (ideleClassNorm F a).ne_zero)
                (NNReal.coe_ne_zero.2 (ideleClassNorm F b).ne_zero)]
            calc ∫⁻ g, wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽
                = ∫⁻ x, wd (y * x) * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by
                  rw [← lintegral_mul_left_eq_self (μ := μ𝔽) _ y]
                  refine lintegral_congr_ae (ae_of_all _ fun x ↦ by simp [inv_mul_cancel_left])
              _ ≤ ∫⁻ x, (ENNReal.ofReal Csh * wd x) * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by
                  refine lintegral_mono fun x ↦ ?_; gcongr
                  dsimp only [wd]; rw [← ENNReal.ofReal_mul hCsh]; refine ENNReal.ofReal_le_ofReal ?_
                  rw [hlog_m]
                  refine (coshSobolevDensity_shift_le hα hs (logNorm y) (logNorm x)).trans ?_
                  refine mul_le_mul_of_nonneg_right ?_ (coshSobolevDensity_pos α s _).le
                  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hsupp y hy) (by linarith)))
                    (Real.rpow_le_rpow (by positivity) (by have := hsupp y hy; linarith) hs) (by positivity) (by positivity)
              _ = ENNReal.ofReal Csh * eLpNorm (u : _ → ℂ) 2 ν ^ 2 := by
                  simp_rw [mul_assoc]
                  rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
                  congr 1
                  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
                    (Lp.aestronglyMeasurable u), ENNReal.toReal_ofNat, ← ENNReal.rpow_two,
                    ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
                    lintegral_coshSobolevMeasure_defect
                      ((Lp.aestronglyMeasurable u).aemeasurable.eNorm.pow_const (2 : ℝ))]
                  simp_rw [ENNReal.rpow_two]
                  rfl
      _ < ⊤ := by
          rw [lintegral_mul_const _ hψ_cont.measurable.eNorm, hL₁_enn]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top u))))
  filter_upwards [ae_lt_top (hwd_m.mul (hm_inner.pow_const 2)) hfin_tot.ne] with g hg
  have h_ne_top : (∫⁻ y, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have hwd_pos : wd g ≠ 0 := (ENNReal.ofReal_pos.mpr (coshSobolevDensity_pos α s _)).ne'
    simp [htop, hwd_pos] at hg
  refine ⟨(hψ_cont.measurable.mul (hu_sm.measurable.comp (measurable_inv.mul measurable_const))).aestronglyMeasurable, ?_⟩
  simpa only [HasFiniteIntegral, eNorm_mul] using h_ne_top

private lemma coeFn_sum_coshInterval {F : Type*} [Field F] [NumberField F]
    {α s : ℝ} {ι : Type*} (S : Finset ι) (v : ι → CoshIntervalSobolev F α s) :
    ((coshIntervalToLp F α s (∑ ι ∈ S, v ι) : Lp ℂ 2 (coshSobolevMeasure F α s)) :
        IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[ideleClassTamagawaMeasure F]
      fun g ↦ ∑ ι ∈ S, ((coshIntervalToLp F α s (v ι) : Lp ℂ 2 (coshSobolevMeasure F α s)) :
        IdeleClassGroup (𝓞 F) F → ℂ) g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero]
    filter_upwards [(tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le
      (Lp.coeFn_zero ℂ 2 (coshSobolevMeasure F α s))] with g hg
    exact hg
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, map_add]
    filter_upwards [ih, (tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le
      (Lp.coeFn_add (coshIntervalToLp F α s (v a)) (coshIntervalToLp F α s (∑ ι ∈ S, v ι)))]
      with g hS hadd
    change ((coshIntervalToLp F α s (v a) + coshIntervalToLp F α s (∑ ι ∈ S, v ι) :
      Lp ℂ 2 (coshSobolevMeasure F α s)) : IdeleClassGroup (𝓞 F) F → ℂ) g = ∑ ι ∈ insert a S, _
    rw [hadd, Pi.add_apply, hS, Finset.sum_insert ha]

/-- Operator-norm `HasSum` expansion of the Hilbert-space defect `A_cosh ψ - (A_cosh (ψ*))†` into
separated operators `(coshMulOp X_ι) ∘ A_cosh (radialMul T_ι ψ)` when `ψ` is supported in
`{|logNorm| ≤ δ}` with `0 ≤ δ ≤ 1 / 32`. -/
theorem hasSum_coshTestAction_sub_adjoint {F : Type*} [Field F] [NumberField F]
    {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 32)
    (ψ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (hsupp : ∀ y, ψ.val y ≠ 0 → |logIdeleClassNorm F y| ≤ δ) :
    HasSum (fun ι : CoshDefectIndex ↦
      (coshMulOp (F := F) (α := α) (s := s) (coshDefectX α ι) (continuous_coshDefectX α ι).measurable
        (norm_coshDefectX_le_one α ι)).comp
        (coshTestAction (F := F) hα hs
          (radialMul (coshDefectT α s ι) (contDiff_coshDefectT α s ι) ψ)))
      (coshTestAction (F := F) hα hs ψ - (coshTestAction (F := F) hα hs (bruhatAdjoint ψ)).adjoint) := by
  let μ𝔽 := ideleClassTamagawaMeasure F
  let logNorm := logIdeleClassNorm F
  let T_op : CoshDefectIndex → CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
    fun ι ↦ (coshMulOp (F := F) (α := α) (s := s) (coshDefectX α ι) (continuous_coshDefectX α ι).measurable
        (norm_coshDefectX_le_one α ι)).comp
      (coshTestAction (F := F) hα hs
        (radialMul (coshDefectT α s ι) (contDiff_coshDefectT α s ι) ψ))
  let D : CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
    coshTestAction (F := F) hα hs ψ - (coshTestAction (F := F) hα hs (bruhatAdjoint ψ)).adjoint
  let b : CoshDefectIndex → ℝ := coshDefectDerivBound α s δ 0
  have hb_sum : Summable b := summable_coshDefectDerivBound hα hs hδ0 hδ1 0
  let C_k : ℝ := Real.sqrt (Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : IdeleClassGroup (𝓞 F) F, ‖ψ.val y‖ ∂μ𝔽
  have hC_k : 0 ≤ C_k := by positivity
  have hS_bound (S : Finset CoshDefectIndex) : ‖(∑ ι ∈ S, T_op ι) - D‖ ≤ C_k * ((∑' ι, b ι) - ∑ ι ∈ S, b ι) := by
    let ε_S : ℝ := (∑' ι, b ι) - ∑ ι ∈ S, b ι
    have hε_S : 0 ≤ ε_S := sub_nonneg.mpr (hb_sum.sum_le_tsum S fun ι _ ↦ coshDefectDerivBound_nonneg hα hδ0 0 ι)
    let K_S : ℝ → ℝ → ℂ := fun x t ↦
      (∑ ι ∈ S, coshDefectX α ι x * coshDefectT α s ι t) -
        ((1 - coshSobolevDensity α s (x - t) / coshSobolevDensity α s x : ℝ) : ℂ)
    have hKm : Measurable (uncurry K_S) := by
      refine (Finset.measurable_sum S fun ι _ ↦ ?_).sub ?_
      · exact ((continuous_coshDefectX α ι).comp continuous_fst).measurable.mul
          (((contDiff_coshDefectT α s ι).continuous.comp continuous_snd).measurable)
      · exact (Complex.continuous_ofReal.comp (continuous_const.sub
          (((continuous_coshSobolevDensity α s).comp (continuous_fst.sub continuous_snd)).div
            ((continuous_coshSobolevDensity α s).comp continuous_fst)
            fun p ↦ (coshSobolevDensity_pos α s _).ne'))).measurable
    have hKb (x t : ℝ) (ht : |t| ≤ δ) : ‖K_S x t‖ ≤ ε_S := by
      let g_xt : CoshDefectIndex → ℂ := fun ι ↦ coshDefectX α ι x * coshDefectT α s ι t
      have hg_has : HasSum g_xt ((1 - coshSobolevDensity α s (x - t) / coshSobolevDensity α s x : ℝ) : ℂ) :=
        hasSum_coshDefect_pointwise hα hs (ht.trans hδ1)
      have hnorm_g (ι : CoshDefectIndex) : ‖g_xt ι‖ ≤ b ι := by
        dsimp only [g_xt, b]
        rw [norm_mul]
        have hT := norm_iteratedDeriv_coshDefectT_le (s := s) hα hδ0 0 ι ht
        rw [iteratedDeriv_zero] at hT
        exact (mul_le_mul (norm_coshDefectX_le_one α ι x) hT (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      have hg_sum : Summable g_xt := hg_has.summable
      have hg_tsum := hg_sum.sum_add_tsum_compl (s := S)
      have hb_tsum := hb_sum.sum_add_tsum_compl (s := S)
      have hK_eq : K_S x t = -∑' ι : ↥((S : Set CoshDefectIndex)ᶜ), g_xt ι.val := by
        dsimp only [K_S]
        rw [← hg_has.tsum_eq, ← hg_tsum]
        ring
      have hb_eq : ε_S = ∑' ι : ↥((S : Set CoshDefectIndex)ᶜ), b ι.val := by
        dsimp only [ε_S]
        rw [← hb_tsum]
        ring
      rw [hK_eq, norm_neg, hb_eq]
      exact (norm_tsum_le_tsum_norm (hg_sum.subtype _).norm).trans
        ((hg_sum.subtype _).norm.tsum_le_tsum (fun ι ↦ hnorm_g ι.val) (hb_sum.subtype _))
    have hT_eq (u : CoshIntervalSobolev F α s) :
        (((∑ ι ∈ S, T_op ι) - D) u : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ𝔽]
          fun g ↦ ∫ y : IdeleClassGroup (𝓞 F) F, ψ.val y * K_S (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽 := by
      have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
      have : SFinite μ𝔽 := inferInstance
      have hsub := (tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le
        (Lp.coeFn_sub (coshIntervalToLp F α s ((∑ ι ∈ S, T_op ι) u)) (coshIntervalToLp F α s (D u)))
      have h_each (ι : CoshDefectIndex) :
          ((T_op ι u : CoshIntervalSobolev F α s) : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ𝔽]
            fun g ↦ ∫ y : IdeleClassGroup (𝓞 F) F,
              ψ.val y * (coshDefectX α ι (logNorm g) * coshDefectT α s ι (logNorm y)) * u (y⁻¹ * g) ∂μ𝔽 := by
        have hm := coshMulOp_apply (F := F) (α := α) (s := s) (coshDefectX α ι)
          (continuous_coshDefectX α ι).measurable (norm_coshDefectX_le_one α ι)
          (coshTestAction hα hs (radialMul (coshDefectT α s ι) (contDiff_coshDefectT α s ι) ψ) u)
        change ((T_op ι u : CoshIntervalSobolev F α s) : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ𝔽] _ at hm
        have ha := coshTestAction_apply hα hs
          (radialMul (coshDefectT α s ι) (contDiff_coshDefectT α s ι) ψ) u
        filter_upwards [hm, ha] with g hg_m hg_a
        rw [hg_m, hg_a, lcaConvolution, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        dsimp only
        rw [radialMul_apply]
        ring
      have hsum_ae : (((∑ ι ∈ S, T_op ι) u : CoshIntervalSobolev F α s) : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ𝔽]
          fun g ↦ ∑ ι ∈ S, ∫ y : IdeleClassGroup (𝓞 F) F,
            ψ.val y * (coshDefectX α ι (logNorm g) * coshDefectT α s ι (logNorm y)) * u (y⁻¹ * g) ∂μ𝔽 := by
        rw [sum_apply]
        have hc := coeFn_sum_coshInterval S (fun ι ↦ T_op ι u)
        have hfin : ∀ᵐ g ∂μ𝔽, ∀ ι ∈ S,
            ((T_op ι u : CoshIntervalSobolev F α s) : IdeleClassGroup (𝓞 F) F → ℂ) g =
              ∫ y : IdeleClassGroup (𝓞 F) F,
                ψ.val y * (coshDefectX α ι (logNorm g) * coshDefectT α s ι (logNorm y)) * u (y⁻¹ * g) ∂μ𝔽 :=
          (S.eventually_all).mpr fun ι _ ↦ h_each ι
        filter_upwards [hc, hfin] with g hg_sum hg_fin
        change (coshIntervalToLp F α s (∑ ι ∈ S, T_op ι u) : IdeleClassGroup (𝓞 F) F → ℂ) g = _
        rw [hg_sum]
        exact Finset.sum_congr rfl fun ι hι ↦ hg_fin ι hι
      have hD_ae := coshTestAction_sub_adjoint_eq_integral hα hs ψ u
      have hint_u := ae_integrable_bruhat_mul_u hα hs ψ u
      filter_upwards [hsub, hsum_ae, hD_ae, hint_u] with g hg_sub hg_sum hg_D hg_int
      change (coshIntervalToLp F α s (((∑ ι ∈ S, T_op ι) - D) u) : IdeleClassGroup (𝓞 F) F → ℂ) g = _
      rw [sub_apply, map_sub, hg_sub, Pi.sub_apply, hg_sum, hg_D]
      have hψc : Continuous ψ.val :=
        continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
      have hu_sm : Measurable (fun y : IdeleClassGroup (𝓞 F) F ↦ u (y⁻¹ * g)) :=
        (Lp.stronglyMeasurable (coshIntervalToLp F α s u)).measurable.comp
          (measurable_inv.mul (measurable_const (a := g)))
      have hint_ι (ι : CoshDefectIndex) : Integrable (fun y : IdeleClassGroup (𝓞 F) F ↦
          ψ.val y * (coshDefectX α ι (logNorm g) * coshDefectT α s ι (logNorm y)) * u (y⁻¹ * g)) μ𝔽 := by
        refine Integrable.mono' (hg_int.norm.const_mul (coshDefectDerivBound α s δ 0 ι)) ?_ (ae_of_all _ fun y ↦ ?_)
        · exact ((hψc.mul (continuous_const.mul
            ((contDiff_coshDefectT α s ι).continuous.comp continuous_logNorm))).measurable.mul hu_sm).aestronglyMeasurable
        · by_cases hy : ψ.val y = 0
          · simp [hy]
          · have hnorm_xt : ‖coshDefectX α ι (logNorm g) * coshDefectT α s ι (logNorm y)‖ ≤ coshDefectDerivBound α s δ 0 ι := by
              rw [norm_mul]
              have hT := norm_iteratedDeriv_coshDefectT_le (s := s) hα hδ0 0 ι (hsupp y hy)
              rw [iteratedDeriv_zero] at hT
              exact (mul_le_mul (norm_coshDefectX_le_one α ι _) hT (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
            rw [norm_mul, norm_mul]
            refine (by gcongr : ‖ψ.val y‖ * ‖coshDefectX α ι (logNorm g) * coshDefectT α s ι (logNorm y)‖ * ‖u (y⁻¹ * g)‖ ≤
              ‖ψ.val y‖ * coshDefectDerivBound α s δ 0 ι * ‖u (y⁻¹ * g)‖).trans_eq (by rw [norm_mul]; ring)
      have hint_D : Integrable (fun y : IdeleClassGroup (𝓞 F) F ↦
          ψ.val y * ((1 - coshSobolevDensity α s (logNorm g - logNorm y) /
            coshSobolevDensity α s (logNorm g) : ℝ) : ℂ) * u (y⁻¹ * g)) μ𝔽 := by
        refine Integrable.mono' (hg_int.norm.const_mul (1 + Real.exp (2 * α * δ) * (1 + δ) ^ s))
          ?_ (ae_of_all _ fun y ↦ ?_)
        · have hKc : Continuous (fun y : IdeleClassGroup (𝓞 F) F ↦
              ((1 - coshSobolevDensity α s (logNorm g - logNorm y) /
                coshSobolevDensity α s (logNorm g) : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.comp (continuous_const.sub
              (((continuous_coshSobolevDensity α s).comp (continuous_const.sub continuous_logNorm)).div_const _))
          exact ((hψc.mul hKc).measurable.mul hu_sm).aestronglyMeasurable
        · by_cases hy : ψ.val y = 0
          · simp [hy]
          · have hshift : coshSobolevDensity α s (logNorm g - logNorm y) /
                coshSobolevDensity α s (logNorm g) ≤ Real.exp (2 * α * δ) * (1 + δ) ^ s := by
              rw [div_le_iff₀ (coshSobolevDensity_pos α s _)]
              have hs1 := coshSobolevDensity_shift_le hα hs (-logNorm y) (logNorm g)
              rw [neg_add_eq_sub, abs_neg] at hs1
              refine hs1.trans (mul_le_mul_of_nonneg_right ?_ (coshSobolevDensity_pos α s _).le)
              exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hsupp y hy) (by linarith)))
                (Real.rpow_le_rpow (by positivity) (by linarith [hsupp y hy]) hs) (by positivity) (by positivity)
            have hKbd : ‖((1 - coshSobolevDensity α s (logNorm g - logNorm y) /
                coshSobolevDensity α s (logNorm g) : ℝ) : ℂ)‖ ≤ 1 + Real.exp (2 * α * δ) * (1 + δ) ^ s := by
              rw [Complex.norm_real, Real.norm_eq_abs]
              refine (abs_sub _ _).trans ?_
              rw [abs_one, abs_of_pos (div_pos (coshSobolevDensity_pos α s _) (coshSobolevDensity_pos α s _))]
              linarith [hshift]
            rw [norm_mul, norm_mul]
            refine (by gcongr : ‖ψ.val y‖ * ‖((1 - coshSobolevDensity α s (logNorm g - logNorm y) /
                coshSobolevDensity α s (logNorm g) : ℝ) : ℂ)‖ * ‖u (y⁻¹ * g)‖ ≤
                ‖ψ.val y‖ * (1 + Real.exp (2 * α * δ) * (1 + δ) ^ s) * ‖u (y⁻¹ * g)‖).trans_eq (by rw [norm_mul]; ring)
      rw [← integral_finsetSum S fun ι _ ↦ hint_ι ι,
        ← integral_sub (integrable_finsetSum S fun ι _ ↦ hint_ι ι) hint_D]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      dsimp only [K_S]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    simpa only [ε_S, C_k] using (norm_coshIntegralKernel_le hα hs ψ hδ0 hε_S hsupp K_S hKm hKb ((∑ ι ∈ S, T_op ι) - D) hT_eq).trans_eq (by ring)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hlim : Tendsto (fun S : Finset CoshDefectIndex ↦ C_k * ((∑' ι, b ι) - ∑ ι ∈ S, b ι))
      (SummationFilter.unconditional CoshDefectIndex).filter (𝓝 0) := by
    have hsub := tendsto_const_nhds (x := ∑' ι, b ι) |>.sub hb_sum.hasSum
    rw [sub_self] at hsub
    simpa only [mul_zero] using hsub.const_mul C_k
  exact squeeze_zero (fun _ ↦ norm_nonneg _) hS_bound hlim

end DefectOperatorHasSum

end CoshDefect

end RiemannMasullo.Isolated.CoshPositiveWidth
