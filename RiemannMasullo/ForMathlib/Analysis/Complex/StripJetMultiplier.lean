module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Positive multipliers on finite jets in a strip

The factorial-normalized derivatives of a product are a triangular convolution of the
normalized derivatives of its factors. This makes it possible to control the multiplication
operator on jets of arbitrary finite order, with constants independent of that order.

The multiplier `(L² - z²)⁻¹` has a positive real part on `|re z| < L`. On a strip separated
from its poles by at least three, the sum of the norms of all its nonconstant Taylor
coefficients is at most half its real part. This is the higher-order analogue of the
first-derivative estimate used in the proposed Hilbert–Schmidt argument for #7405.
-/

@[expose] public noncomputable section

open Complex Finset
open scoped InnerProductSpace

namespace RiemannMasullo

/-- Explicit Taylor coefficients of `(L² - z²)⁻¹` at points inside the strip between its poles. -/
def stripMultiplierCoeff (L : ℝ) (z : ℂ) (r : ℕ) : ℂ :=
  (((L : ℂ) - z)⁻¹ ^ (r + 1) + (-1 : ℂ) ^ r * ((L : ℂ) + z)⁻¹ ^ (r + 1)) /
    ((2 * L : ℝ) : ℂ)

private lemma inv_re_eq_re_mul_norm_sq (w : ℂ) :
    (w⁻¹).re = w.re * ‖w⁻¹‖ ^ 2 := by
  rw [Complex.inv_re, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq, div_eq_mul_inv]

private lemma norm_inv_le_of_re {d : ℝ} {w : ℂ} (hd : 0 < d) (hw : d ≤ w.re) :
    ‖w⁻¹‖ ≤ d⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hd (hw.trans (Complex.re_le_norm w))

private lemma norm_inv_pow_le_re {d : ℝ} {w : ℂ} (hd : 0 < d) (hw : d ≤ w.re)
    (r : ℕ) : ‖w⁻¹‖ ^ (r + 2) ≤ d⁻¹ ^ (r + 1) * (w⁻¹).re := by
  have hn := norm_inv_le_of_re hd hw
  have hr : 0 ≤ (w⁻¹).re := by
    rw [inv_re_eq_re_mul_norm_sq]
    exact mul_nonneg (hd.le.trans hw) (sq_nonneg _)
  induction r with
  | zero =>
    simp only [zero_add, pow_one]
    rw [inv_re_eq_re_mul_norm_sq]
    have h : 1 ≤ d⁻¹ * w.re := (one_le_inv_mul₀ hd).2 hw
    nlinarith [sq_nonneg ‖w⁻¹‖]
  | succ r ih =>
    calc
      ‖w⁻¹‖ ^ (r + 1 + 2) = ‖w⁻¹‖ ^ (r + 2) * ‖w⁻¹‖ := by ring
      _ ≤ (d⁻¹ ^ (r + 1) * (w⁻¹).re) * d⁻¹ :=
        mul_le_mul ih hn (norm_nonneg _) (by positivity)
      _ = d⁻¹ ^ (r + 1 + 1) * (w⁻¹).re := by ring

/-- The constant coefficient is the reciprocal quadratic multiplier. -/
theorem stripMultiplierCoeff_zero {L : ℝ} {z : ℂ} (hL : 0 < L)
    (hz : |z.re| < L) : stripMultiplierCoeff L z 0 = ((L : ℂ) ^ 2 - z ^ 2)⁻¹ := by
  have hm : (L : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this
    linarith [le_abs_self z.re]
  have hp : (L : ℂ) + z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at this
    linarith [neg_le_abs z.re]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hq : (L : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hp hm
  simp only [stripMultiplierCoeff, Nat.zero_add, pow_zero, pow_one, one_mul,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [hm, hp, hLc, hq]
  ring

private lemma stripMultiplierCoeff_re_zero (L : ℝ) (z : ℂ) :
    (stripMultiplierCoeff L z 0).re =
      (((L : ℂ) - z)⁻¹.re + ((L : ℂ) + z)⁻¹.re) / (2 * L) := by
  simp only [stripMultiplierCoeff, Nat.zero_add, pow_one, pow_zero, one_mul,
    Complex.div_ofReal_re, Complex.add_re]

/-- A coefficient of positive degree is dominated by a geometric multiple of the real
part of the constant coefficient. The bound depends only on the distance to the poles. -/
theorem norm_stripMultiplierCoeff_succ_le {L α d : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hd : 0 < d) (hL : α + d ≤ L) (hz : |z.re| ≤ α) (r : ℕ) :
    ‖stripMultiplierCoeff L z (r + 1)‖ ≤
      d⁻¹ ^ (r + 1) * (stripMultiplierCoeff L z 0).re := by
  have hLpos : 0 < L := by linarith
  have hm : d ≤ ((L : ℂ) - z).re := by
    simp only [sub_re, ofReal_re]
    linarith [le_abs_self z.re]
  have hp : d ≤ ((L : ℂ) + z).re := by
    simp only [add_re, ofReal_re]
    linarith [neg_le_abs z.re]
  calc
    ‖stripMultiplierCoeff L z (r + 1)‖ ≤
        (‖((L : ℂ) - z)⁻¹‖ ^ (r + 2) + ‖((L : ℂ) + z)⁻¹‖ ^ (r + 2)) /
          (2 * L) := by
      simp only [stripMultiplierCoeff, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < 2 * L by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Nat.add_assoc, Nat.reduceAdd] using
        norm_add_le (((L : ℂ) - z)⁻¹ ^ (r + 2))
          ((-1 : ℂ) ^ (r + 1) * ((L : ℂ) + z)⁻¹ ^ (r + 2))
    _ ≤ (d⁻¹ ^ (r + 1) * ((L : ℂ) - z)⁻¹.re +
        d⁻¹ ^ (r + 1) * ((L : ℂ) + z)⁻¹.re) / (2 * L) := by
      exact div_le_div_of_nonneg_right
        (add_le_add (norm_inv_pow_le_re hd hm r) (norm_inv_pow_le_re hd hp r))
        (by positivity)
    _ = d⁻¹ ^ (r + 1) * (stripMultiplierCoeff L z 0).re := by
      rw [stripMultiplierCoeff_re_zero]
      ring

/-- The constant coefficient has positive real part strictly between the poles. -/
theorem stripMultiplierCoeff_re_pos {L : ℝ} {z : ℂ} (hL : 0 < L)
    (hz : |z.re| < L) : 0 < (stripMultiplierCoeff L z 0).re := by
  have hinv (w : ℂ) (hw : 0 < w.re) : 0 < (w⁻¹).re := by
    rw [Complex.inv_re]
    apply div_pos hw
    apply Complex.normSq_pos.mpr
    rintro rfl
    simp at hw
  rw [stripMultiplierCoeff_re_zero]
  apply div_pos _ (by positivity)
  apply add_pos
  · apply hinv
    simp only [sub_re, ofReal_re]
    linarith [le_abs_self z.re]
  · apply hinv
    simp only [add_re, ofReal_re]
    linarith [neg_le_abs z.re]

/-- Uniformly in the jet order, the nonconstant coefficients contribute at most half of
the positive diagonal whenever the strip is at least three units from the poles. -/
theorem sum_norm_stripMultiplierCoeff_succ_le {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) (n : ℕ) :
    ∑ r ∈ range n, ‖stripMultiplierCoeff L z (r + 1)‖ ≤
      (stripMultiplierCoeff L z 0).re / 2 := by
  have hr : 0 ≤ (stripMultiplierCoeff L z 0).re :=
    (stripMultiplierCoeff_re_pos (by linarith) (by linarith)).le
  have hgeom : ∑ r ∈ range n, (3 : ℝ)⁻¹ ^ (r + 1) ≤ 1 / 2 := by
    have h := geom_sum_mul_neg (3 : ℝ)⁻¹ n
    simp only [pow_succ, ← sum_mul]
    norm_num at h ⊢
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 3 by norm_num) n]
  calc
    ∑ r ∈ range n, ‖stripMultiplierCoeff L z (r + 1)‖ ≤
        ∑ r ∈ range n, (3 : ℝ)⁻¹ ^ (r + 1) * (stripMultiplierCoeff L z 0).re :=
      sum_le_sum fun r _ ↦ norm_stripMultiplierCoeff_succ_le hα (by norm_num) hL hz r
    _ = (∑ r ∈ range n, (3 : ℝ)⁻¹ ^ (r + 1)) * (stripMultiplierCoeff L z 0).re :=
      (sum_mul ..).symm
    _ ≤ (stripMultiplierCoeff L z 0).re / 2 := by nlinarith

/-- The unilateral shift on a finite jet, discarding entries above its order. -/
def finiteJetShift {n : ℕ} (r : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i ↦ if r ≤ i.val then
    v ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ else 0

/-- Truncating a unilateral shift does not increase the Euclidean norm. -/
theorem norm_finiteJetShift_le {n : ℕ} (r : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    ‖finiteJetShift r v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  let g : Fin n → Fin n := fun i ↦ ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  let s := univ.filter fun i : Fin n ↦ r ≤ i.val
  have hginj : Set.InjOn g s := by
    intro i hi j hj hij
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    have heq := congrArg Fin.val hij
    apply Fin.ext
    dsimp [g] at heq
    omega
  calc
    ∑ i, ‖finiteJetShift r v i‖ ^ 2 = ∑ i ∈ s, ‖v (g i)‖ ^ 2 := by
      simp [finiteJetShift, s, g, apply_ite, sum_ite]
    _ = ∑ i ∈ s.image g, ‖v i‖ ^ 2 :=
      (sum_image (f := fun i ↦ ‖v i‖ ^ 2) hginj).symm
    _ ≤ ∑ i, ‖v i‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _

@[simp] theorem finiteJetShift_zero {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    finiteJetShift 0 v = v := by
  ext i
  simp [finiteJetShift]

/-- Multiplication of factorial-normalized jets is truncated convolution. -/
def finiteJetMul {n : ℕ} (c : ℕ → ℂ) (v : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  ∑ r ∈ range (n + 1), c r • finiteJetShift r v

/-- The operator norm of multiplication on jets is bounded by the coefficient `ℓ¹` norm. -/
theorem norm_finiteJetMul_le {n : ℕ} (c : ℕ → ℂ)
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    ‖finiteJetMul c v‖ ≤ (∑ r ∈ range (n + 1), ‖c r‖) * ‖v‖ := by
  calc
    ‖finiteJetMul c v‖ ≤ ∑ r ∈ range (n + 1), ‖c r • finiteJetShift r v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ range (n + 1), ‖c r‖ * ‖v‖ := by
      apply sum_le_sum
      intro r _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_finiteJetShift_le r v) (norm_nonneg _)
    _ = (∑ r ∈ range (n + 1), ‖c r‖) * ‖v‖ := (sum_mul ..).symm

/-- The real part of the jet multiplication form is bounded below by the diagonal minus
the `ℓ¹` norm of the strictly triangular coefficients. No sign assumption is needed. -/
theorem re_inner_finiteJetMul_ge {n : ℕ} (c : ℕ → ℂ)
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    ((c 0).re - ∑ r ∈ range n, ‖c (r + 1)‖) * ‖v‖ ^ 2 ≤
      (⟪v, finiteJetMul c v⟫_ℂ).re := by
  let R := ∑ r ∈ range n, c (r + 1) • finiteJetShift (r + 1) v
  have hR : ‖R‖ ≤ (∑ r ∈ range n, ‖c (r + 1)‖) * ‖v‖ := by
    calc
      ‖R‖ ≤ ∑ r ∈ range n, ‖c (r + 1) • finiteJetShift (r + 1) v‖ :=
        norm_sum_le _ _
      _ ≤ ∑ r ∈ range n, ‖c (r + 1)‖ * ‖v‖ := by
        apply sum_le_sum
        intro r _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_finiteJetShift_le _ v) (norm_nonneg _)
      _ = (∑ r ∈ range n, ‖c (r + 1)‖) * ‖v‖ := (sum_mul ..).symm
  have hinner : |(⟪v, R⟫_ℂ).re| ≤
      (∑ r ∈ range n, ‖c (r + 1)‖) * ‖v‖ ^ 2 := by
    calc
      |(⟪v, R⟫_ℂ).re| ≤ ‖⟪v, R⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖R‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * ((∑ r ∈ range n, ‖c (r + 1)‖) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ = (∑ r ∈ range n, ‖c (r + 1)‖) * ‖v‖ ^ 2 := by ring
  have hdiag : (⟪v, c 0 • v⟫_ℂ).re = (c 0).re * ‖v‖ ^ 2 := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hsplit : finiteJetMul c v = R + c 0 • v := by
    rw [finiteJetMul, sum_range_succ', finiteJetShift_zero]
  rw [hsplit, inner_add_right, Complex.add_re, hdiag]
  linarith [neg_abs_le (⟪v, R⟫_ℂ).re]

/-- The reciprocal quadratic multiplier has a positive multiplication form on every finite
jet. The constant `1/2` is independent of the order. -/
theorem re_inner_stripMultiplierJet_ge {n : ℕ} {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α)
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    (stripMultiplierCoeff L z 0).re / 2 * ‖v‖ ^ 2 ≤
      (⟪v, finiteJetMul (stripMultiplierCoeff L z) v⟫_ℂ).re := by
  have h := re_inner_finiteJetMul_ge (stripMultiplierCoeff L z) v
  have hb := sum_norm_stripMultiplierCoeff_succ_le hα hL hz n
  nlinarith [sq_nonneg ‖v‖]

/-- A scalar coefficient bound controls a second jet multiplier by the positive multiplier's
quadratic form, uniformly in the jet order. -/
theorem norm_finiteJetMul_sq_le_stripMultiplier {n : ℕ} {L α C : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) (hC : 0 ≤ C)
    (b : ℕ → ℂ) (hb : (∑ r ∈ range (n + 1), ‖b r‖) ^ 2 ≤
      C * (stripMultiplierCoeff L z 0).re)
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    ‖finiteJetMul b v‖ ^ 2 ≤
      2 * C * (⟪v, finiteJetMul (stripMultiplierCoeff L z) v⟫_ℂ).re := by
  calc
    ‖finiteJetMul b v‖ ^ 2 ≤ ((∑ r ∈ range (n + 1), ‖b r‖) * ‖v‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 (norm_finiteJetMul_le b v)
    _ = (∑ r ∈ range (n + 1), ‖b r‖) ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
    _ ≤ (C * (stripMultiplierCoeff L z 0).re) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ 2 * C * (⟪v, finiteJetMul (stripMultiplierCoeff L z) v⟫_ℂ).re := by
      have h := mul_le_mul_of_nonneg_left (re_inner_stripMultiplierJet_ge hα hL hz v) hC
      nlinarith

private lemma iteratedDeriv_inv_eq (r : ℕ) (w : ℂ) :
    iteratedDeriv r (fun u : ℂ ↦ u⁻¹) w =
      (-1 : ℂ) ^ r * r.factorial * w⁻¹ ^ (r + 1) := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  have h : (-1 - (r : ℤ)) = -((r + 1 : ℕ) : ℤ) := by omega
  rw [h, zpow_neg, zpow_natCast, inv_pow]

/-- The coefficients used in the jet estimate really are factorial-normalized derivatives
of the positive multiplier, rather than merely a sequence with convenient bounds. -/
theorem stripMultiplierCoeff_eq_iteratedDeriv {L : ℝ} {z : ℂ}
    (hz : |z.re| < L) (r : ℕ) :
    stripMultiplierCoeff L z r =
      iteratedDeriv r (fun w ↦ stripMultiplierCoeff L w 0) z / (r.factorial : ℂ) := by
  have hm : (L : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this
    linarith [le_abs_self z.re]
  have hp : (L : ℂ) + z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at this
    linarith [neg_le_abs z.re]
  have hdm : ContDiffAt ℂ r (fun w : ℂ ↦ ((L : ℂ) - w)⁻¹) z :=
    (contDiffAt_const.sub contDiffAt_id).inv hm
  have hdp : ContDiffAt ℂ r (fun w : ℂ ↦ ((L : ℂ) + w)⁻¹) z :=
    (contDiffAt_const.add contDiffAt_id).inv hp
  have hfac : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  simp only [stripMultiplierCoeff, Nat.zero_add, pow_one, pow_zero, one_mul,
    iteratedDeriv_div_const, iteratedDeriv_fun_add hdm hdp,
    iteratedDeriv_comp_const_sub, iteratedDeriv_comp_const_add, iteratedDeriv_inv_eq,
    smul_eq_mul]
  have hsign : (-1 : ℂ) ^ r * (-1 : ℂ) ^ r = 1 := by
    rw [← mul_pow]
    simp
  simp only [← mul_assoc, hsign, one_mul]
  field_simp [hfac]

/-- The coordinate formula for multiplication of a finite jet. -/
theorem finiteJetMul_apply {n : ℕ} (c : ℕ → ℂ)
    (v : EuclideanSpace ℂ (Fin (n + 1))) (i : Fin (n + 1)) :
    finiteJetMul c v i = ∑ r ∈ range (i.val + 1),
      c r * v ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ := by
  simp only [finiteJetMul, finiteJetShift, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ r ∈ range (n + 1), c r *
    (if r ≤ i.val then v ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ else 0)) = _
  rw [← sum_subset (range_mono (by omega : i.val + 1 ≤ n + 1))]
  · apply sum_congr rfl
    intro r hr
    rw [ite_eq_left (by simpa using mem_range.mp hr)]
  · intro r _ hr
    rw [ite_eq_right (by simpa using hr), mul_zero]

/-- The jet with coordinate `j` equal to the `j`-th derivative divided by `j!`. -/
def finiteNormalizedJet (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun i ↦ iteratedDeriv i.val f z / (i.val.factorial : ℂ)

/-- Leibniz's formula, expressed as multiplication of factorial-normalized jets. -/
theorem finiteNormalizedJet_mul {n : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ n f z) (hg : ContDiffAt ℂ n g z) :
    finiteNormalizedJet n (fun w ↦ f w * g w) z =
      finiteJetMul (fun r ↦ iteratedDeriv r f z / (r.factorial : ℂ))
        (finiteNormalizedJet n g z) := by
  ext i
  rw [finiteJetMul_apply]
  change iteratedDeriv i.val (fun w ↦ f w * g w) z / (i.val.factorial : ℂ) = _
  have hi : (i.val : WithTop ℕ∞) ≤ n := by exact_mod_cast (by omega : i.val ≤ n)
  rw [iteratedDeriv_fun_mul (hf.of_le hi) (hg.of_le hi), sum_div]
  apply sum_congr rfl
  intro r hr
  change (i.val.choose r : ℂ) * iteratedDeriv r f z * iteratedDeriv (i.val - r) g z /
      (i.val.factorial : ℂ) =
    (iteratedDeriv r f z / (r.factorial : ℂ)) *
      (iteratedDeriv (i.val - r) g z / ((i.val - r).factorial : ℂ))
  have hfac (k : ℕ) : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hchoose : (i.val.choose r : ℂ) * r.factorial * (i.val - r).factorial =
      i.val.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by simpa using mem_range.mp hr)
  field_simp [hfac]
  linear_combination iteratedDeriv r f z * iteratedDeriv (i.val - r) g z * hchoose

/-- The reciprocal quadratic multiplier is smooth away from its two poles. -/
theorem contDiffAt_stripMultiplier {n : WithTop ℕ∞} {L : ℝ} {z : ℂ}
    (hz : |z.re| < L) : ContDiffAt ℂ n (fun w ↦ stripMultiplierCoeff L w 0) z := by
  have hm : (L : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this
    linarith [le_abs_self z.re]
  have hp : (L : ℂ) + z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at this
    linarith [neg_le_abs z.re]
  simp only [stripMultiplierCoeff, Nat.zero_add, pow_one, pow_zero, one_mul]
  exact (((contDiffAt_const.sub contDiffAt_id).inv hm).add
    ((contDiffAt_const.add contDiffAt_id).inv hp)).div_const _

/-- The pointwise higher-order strip energy estimate, now for actual derivatives of
products. It includes the mixed derivative terms in the positive multiplier's form. -/
theorem norm_finiteNormalizedJet_mul_sq_le {n : ℕ} {L α C : ℝ} {z : ℂ}
    {Φ f : ℂ → ℂ} (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) (hC : 0 ≤ C)
    (hΦ : ContDiffAt ℂ n Φ z) (hf : ContDiffAt ℂ n f z)
    (hbound : (∑ r ∈ range (n + 1), ‖iteratedDeriv r Φ z / (r.factorial : ℂ)‖) ^ 2 ≤
      C * (stripMultiplierCoeff L z 0).re) :
    ‖finiteNormalizedJet n (fun w ↦ Φ w * f w) z‖ ^ 2 ≤
      2 * C * (⟪finiteNormalizedJet n f z,
        finiteNormalizedJet n (fun w ↦ stripMultiplierCoeff L w 0 * f w) z⟫_ℂ).re := by
  have hz' : |z.re| < L := by linarith
  rw [finiteNormalizedJet_mul hΦ hf,
    finiteNormalizedJet_mul (contDiffAt_stripMultiplier hz') hf]
  simp_rw [← stripMultiplierCoeff_eq_iteratedDeriv hz']
  exact norm_finiteJetMul_sq_le_stripMultiplier hα hL hz hC _ hbound _

section Integral

open MeasureTheory

/-- Integrating the higher-order strip estimate turns an exact diagonal identity into an
energy bound. The measure can be any weighted area measure on the closed strip. -/
theorem integral_finiteNormalizedJet_mul_sq_le {n : ℕ} {L α C : ℝ} {μ : Measure ℂ}
    {Φ f : ℂ → ℂ} (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hC : 0 ≤ C)
    (hstrip : ∀ᵐ z ∂μ, |z.re| ≤ α)
    (hΦ : ∀ᵐ z ∂μ, ContDiffAt ℂ n Φ z) (hf : ∀ᵐ z ∂μ, ContDiffAt ℂ n f z)
    (hbound : ∀ᵐ z ∂μ,
      (∑ r ∈ range (n + 1), ‖iteratedDeriv r Φ z / (r.factorial : ℂ)‖) ^ 2 ≤
        C * (stripMultiplierCoeff L z 0).re)
    (henergy : Integrable (fun z ↦ ‖finiteNormalizedJet n (fun w ↦ Φ w * f w) z‖ ^ 2) μ)
    (hform : Integrable (fun z ↦ (⟪finiteNormalizedJet n f z,
      finiteNormalizedJet n (fun w ↦ stripMultiplierCoeff L w 0 * f w) z⟫_ℂ).re) μ)
    {c : ℝ} (hdiag : ∫ z, (⟪finiteNormalizedJet n f z,
      finiteNormalizedJet n (fun w ↦ stripMultiplierCoeff L w 0 * f w) z⟫_ℂ).re ∂μ = c) :
    ∫ z, ‖finiteNormalizedJet n (fun w ↦ Φ w * f w) z‖ ^ 2 ∂μ ≤ 2 * C * c := by
  calc
    _ ≤ ∫ z, 2 * C * (⟪finiteNormalizedJet n f z,
        finiteNormalizedJet n (fun w ↦ stripMultiplierCoeff L w 0 * f w) z⟫_ℂ).re ∂μ := by
      apply integral_mono_ae henergy (hform.const_mul (2 * C))
      filter_upwards [hstrip, hΦ, hf, hbound] with z hz hΦz hfz hboundz
      exact norm_finiteNormalizedJet_mul_sq_le hα hL hz hC hΦz hfz hboundz
    _ = 2 * C * c := by rw [integral_const_mul, hdiag]

end Integral

private theorem stripQuadratic_re_ge {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) :
    1 + z.im ^ 2 ≤ (((L : ℂ) ^ 2 - z ^ 2)).re := by
  have hsq : z.re ^ 2 ≤ α ^ 2 := (sq_abs z.re) ▸ pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hLs : (α + 3) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
  simp only [sub_re, pow_two, mul_re, ofReal_re, ofReal_im]
  nlinarith

/-- The reciprocal multiplier decays quadratically in height on the closed strip. -/
theorem norm_stripMultiplierCoeff_zero_le {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) :
    ‖stripMultiplierCoeff L z 0‖ ≤ (1 + z.im ^ 2)⁻¹ := by
  rw [stripMultiplierCoeff_zero (by linarith) (by linarith), norm_inv]
  exact inv_anti₀ (by positivity)
    ((stripQuadratic_re_ge hα hL hz).trans (Complex.re_le_norm _))

/-- The reciprocal multiplier's square is controlled by its positive real part. -/
theorem norm_stripMultiplierCoeff_zero_sq_le_re {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) :
    ‖stripMultiplierCoeff L z 0‖ ^ 2 ≤ (stripMultiplierCoeff L z 0).re := by
  have hq := stripQuadratic_re_ge hα hL hz
  rw [stripMultiplierCoeff_zero (by linarith) (by linarith)]
  rw [inv_re_eq_re_mul_norm_sq]
  nlinarith [sq_nonneg z.im, sq_nonneg ‖(((L : ℂ) ^ 2 - z ^ 2))⁻¹‖]

/-- The full Taylor coefficient sum of the reciprocal multiplier is controlled by its
positive real part, uniformly in the number of coefficients. -/
theorem sum_norm_stripMultiplierCoeff_sq_le {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α) (n : ℕ) :
    (∑ r ∈ range (n + 1), ‖stripMultiplierCoeff L z r‖) ^ 2 ≤
      (9 / 4 : ℝ) * (stripMultiplierCoeff L z 0).re := by
  have hs := sum_norm_stripMultiplierCoeff_succ_le hα hL hz n
  have hn := norm_stripMultiplierCoeff_zero_sq_le_re hα hL hz
  have hr := Complex.re_le_norm (stripMultiplierCoeff L z 0)
  have hnon : 0 ≤ ∑ r ∈ range n, ‖stripMultiplierCoeff L z (r + 1)‖ :=
    sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [sum_range_succ']
  nlinarith [norm_nonneg (stripMultiplierCoeff L z 0)]

/-- The positive multiplier controls its own action on all finite jets. -/
theorem norm_finiteJetMul_stripMultiplier_sq_le {n : ℕ} {L α : ℝ} {z : ℂ}
    (hα : 0 ≤ α) (hL : α + 3 ≤ L) (hz : |z.re| ≤ α)
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    ‖finiteJetMul (stripMultiplierCoeff L z) v‖ ^ 2 ≤
      (9 / 2 : ℝ) * (⟪v, finiteJetMul (stripMultiplierCoeff L z) v⟫_ℂ).re := by
  convert norm_finiteJetMul_sq_le_stripMultiplier hα hL hz (by norm_num : (0 : ℝ) ≤ 9 / 4)
    (stripMultiplierCoeff L z) (sum_norm_stripMultiplierCoeff_sq_le hα hL hz n) v using 1
  norm_num

end RiemannMasullo
