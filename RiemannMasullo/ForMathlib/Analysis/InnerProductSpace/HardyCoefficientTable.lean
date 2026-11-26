module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Finite coefficient tables for Hardy polynomials

Multiplication by a polynomial is finite convolution on the Hilbert space of sequences.
A bound for the derivative energy controls the omitted coefficients. A separate estimate
measures the effect of entry errors on the visible Euclidean residual.
-/

@[expose] public noncomputable section

open Filter Finset Set
open scoped Topology BigOperators


namespace HardyTable

abbrev H := lp (fun _ : ℕ ↦ ℂ) 2
abbrev Coeff (d : ℕ) := EuclideanSpace ℂ (Fin (d+1))

private theorem hp : 0 < (2 : ENNReal).toReal := by norm_num

theorem summable_sq (c : H) : Summable (fun j ↦ ‖c j‖ ^ 2) := by
  simpa using (memℓp_gen_iff hp).mp c.prop

theorem norm_sq (c : H) : ‖c‖^2 = ∑' j, ‖c j‖^2 := by
  simpa using lp.norm_rpow_eq_tsum hp c

/-- A column of the lower triangular coefficient matrix, with zero before its diagonal. -/
def shift (c : H) (k : ℕ) : H :=
  ⟨fun j ↦ if k ≤ j then c (j-k) else 0, by
    apply (memℓp_gen_iff hp).2
    apply (summable_nat_add_iff k).mp
    simpa using summable_sq c⟩

/-- Reindex a coefficient tail at zero. -/
def tail (c : H) (L : ℕ) : H :=
  ⟨fun j ↦ c (j+L), by
    apply (memℓp_gen_iff hp).2
    simpa using (summable_nat_add_iff L).mpr (summable_sq c)⟩

/-- Coordinates indexed by 0 through M, inclusive. -/
def head (c : H) (M : ℕ) : Coeff M := WithLp.toLp 2 fun j ↦ c j

def unitVector : H := lp.single 2 0 1

def product {d : ℕ} (c : H) (p : Coeff d) : H :=
  ∑ k : Fin (d+1), (p k) • shift c k

def coeffOneNorm {d : ℕ} (p : Coeff d) : ℝ := ∑ k, ‖p k‖

theorem product_apply {d : ℕ} (c : H) (p : Coeff d) (j : ℕ) :
    product c p j = ∑ k : Fin (d+1), p k * (if (k:ℕ) ≤ j then c (j-k) else 0) := by
  simp only [product, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rfl

theorem unitVector_apply (j : ℕ) : unitVector j = (if j=0 then 1 else 0) := by
  by_cases h : j = 0
  · subst j; simp [unitVector]
  · simp [unitVector, h]

theorem head_tail (c : H) (M : ℕ) :
    ‖head c M‖^2 + ‖tail c (M+1)‖^2 = ‖c‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, norm_sq, norm_sq]
  change (∑ i : Fin (M+1), (fun j : ℕ ↦ ‖c j‖^2) i) + _ = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ ‖c j‖^2) (M+1)]
  exact (summable_sq c).sum_add_tsum_nat_add (M+1)

theorem head_le (c : H) (M : ℕ) : ‖head c M‖ ≤ ‖c‖ := by
  nlinarith [head_tail c M, sq_nonneg ‖tail c (M+1)‖, norm_nonneg c, norm_nonneg (head c M)]

theorem le_head_add_tail (c : H) (M : ℕ) : ‖c‖ ≤ ‖head c M‖ + ‖tail c (M+1)‖ := by
  nlinarith [head_tail c M, mul_nonneg (norm_nonneg (head c M)) (norm_nonneg (tail c (M+1))),
    norm_nonneg c, norm_nonneg (head c M), norm_nonneg (tail c (M+1))]

/-- The weighted square sum must genuinely converge. -/
def DerivativeBound (c : H) (D : ℝ) : Prop :=
  0 ≤ D ∧ Summable (fun j : ℕ ↦ (j:ℝ)^2 * ‖c j‖^2) ∧
    ∑' j : ℕ, (j:ℝ)^2 * ‖c j‖^2 ≤ D^2

/-- Genuine square summability of the weighted coefficients provides the Hilbert vector itself. -/
def ofDerivative (b : ℕ → ℂ) (hs : Summable (fun j : ℕ ↦ (j:ℝ)^2*‖b j‖^2)) : H :=
  ⟨b,by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).2
    suffices ht : Summable (fun j : ℕ ↦ ‖b (j+1)‖^2) by simpa using (summable_nat_add_iff 1).mp ht
    apply Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) _ ((summable_nat_add_iff 1).mpr hs)
    intro j
    have hj : 1 ≤ ((j+1:ℕ):ℝ)^2 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) j, sq_nonneg (j:ℝ)]
    simpa using mul_le_mul_of_nonneg_right hj (sq_nonneg ‖b (j+1)‖)⟩

theorem bound_ofDerivative (b : ℕ → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hs : Summable (fun j : ℕ ↦ (j:ℝ)^2*‖b j‖^2))
    (hle : ∑' j : ℕ, (j:ℝ)^2*‖b j‖^2 ≤ D^2) :
    DerivativeBound (ofDerivative b hs) D := ⟨hD,hs,hle⟩

theorem tail_le_of_derivative {c : H} {D : ℝ} (hD : DerivativeBound c D)
    {L : ℕ} {R : ℝ} (hR : 0 < R) (hL : R ≤ L) : ‖tail c L‖ ≤ D/R := by
  obtain ⟨hD0, hsum, henergy⟩ := hD
  have hweighted : ∑' i : ℕ, ((i+L:ℕ):ℝ)^2 * ‖c (i+L)‖^2 ≤ D^2 := by
    have hj := hsum.sum_add_tsum_nat_add L
    have hn : 0 ≤ ∑ i ∈ range L, (i:ℝ)^2 * ‖c i‖^2 :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hc := (summable_nat_add_iff L).mpr (summable_sq c)
  have hs := (summable_nat_add_iff L).mpr hsum
  have hcomp : R^2 * ‖tail c L‖^2 ≤ D^2 := by
    rw [norm_sq, ← tsum_mul_left]
    apply le_trans _ hweighted
    apply (hc.mul_left (R^2)).tsum_le_tsum _ hs
    intro i
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hi : R ≤ (i+L:ℕ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]
    exact pow_le_pow_left₀ hR.le hi 2
  apply (le_div_iff₀ hR).2
  nlinarith [mul_nonneg (norm_nonneg (tail c L)) hR.le, sq_nonneg (‖tail c L‖ * R - D),
    show (‖tail c L‖ * R)^2 = R^2 * ‖tail c L‖^2 by ring]

/-- Uniform hidden tail, with the exact coefficient one-norm visible. -/
theorem hidden_le {d M : ℕ} {c : H} {D : ℝ} (hD : DerivativeBound c D)
    (p : Coeff d) {R : ℝ} (hR : 0 < R) (hRM : R ≤ (M:ℝ) - d) :
    ‖tail (unitVector - product c p) (M+1)‖ ≤ coeffOneNorm p * (D/R) := by
  have hdM : d ≤ M := by exact_mod_cast (show (d:ℝ) ≤ M by linarith)
  have heq : tail (unitVector - product c p) (M+1) =
      -(∑ k : Fin (d+1), p k • tail c (M+1-k)) := by
    ext i
    have hii : i+(M+1) ≠ 0 := by omega
    change (unitVector - product c p) (i+(M+1)) = _
    simp only [lp.coeFn_sub, Pi.sub_apply, unitVector_apply, ite_eq_right hii, zero_sub,
      product_apply, lp.coeFn_neg, Pi.neg_apply, lp.coeFn_sum, Finset.sum_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, neg_inj]
    apply Finset.sum_congr rfl
    intro k _
    have hk := k.isLt
    simp only [ite_eq_left (show (k:ℕ) ≤ i+(M+1) by omega)]
    change p k * c (i+(M+1)-k) = p k * c (i+(M+1-k))
    rw [show i+(M+1)-(k:ℕ) = i+(M+1-k) by omega]
  rw [heq, norm_neg, coeffOneNorm, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply tail_le_of_derivative hD hR
  have hk := k.isLt
  rw [Nat.cast_sub (by omega : (k:ℕ) ≤ M+1)]
  push_cast
  have hk' : (k.val:ℝ) ≤ d := by exact_mod_cast (show k.val ≤ d by omega)
  linarith

end HardyTable

end

@[expose] public noncomputable section

open Filter Finset Set
open scoped Topology BigOperators

namespace HardyTable

/-- The measured residual vector uses only indices 0 through M of the supplied coefficients. -/
def visible {d : ℕ} (M : ℕ) (a : ℕ → ℂ) (p : Coeff d) : Coeff M :=
  WithLp.toLp 2 fun j ↦ (if j.val = 0 then 1 else 0) -
    ∑ k : Fin (d+1), p k * (if k.val ≤ j.val then a (j.val-k.val) else 0)

theorem visible_eq_head {d : ℕ} (M : ℕ) (c : H) (p : Coeff d) :
    visible M c p = head (unitVector - product c p) M := by
  ext j
  change _ = (unitVector - product c p) j
  simp [visible, unitVector_apply, product_apply]

theorem visible_norm_sq {d : ℕ} (M : ℕ) (a : ℕ → ℂ) (p : Coeff d) :
    ‖visible M a p‖^2 = ∑ j : Fin (M+1), ‖(if j.val = 0 then 1 else 0) -
      ∑ k : Fin (d+1), p k * (if k.val ≤ j.val then a (j.val-k.val) else 0)‖^2 :=
  EuclideanSpace.norm_sq_eq _

/-- A uniform visible error at the coefficient level, independent of the unmeasured coefficients. -/
theorem visible_perturb_le {d M : ℕ} {a b : ℕ → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hab : ∀ j ≤ M, ‖a j - b j‖ ≤ ε) (p : Coeff d) :
    ‖visible M a p - visible M b p‖ ≤ Real.sqrt (M+1) * (coeffOneNorm p * ε) := by
  have hl : 0 ≤ coeffOneNorm p := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hj (j : Fin (M+1)) :
      ‖(visible M a p - visible M b p) j‖ ≤ coeffOneNorm p * ε := by
    change ‖((_ : ℂ) - _) - (_ - _)‖ ≤ _
    simp only [sub_sub_sub_cancel_left]
    rw [← Finset.sum_sub_distrib, coeffOneNorm, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [← mul_sub, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases hkj : k.val ≤ j.val
    · simp only [ite_eq_left hkj]
      rw [norm_sub_rev]
      exact hab _ (by have := j.isLt; omega)
    · simpa [hkj] using hε
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hl hε))).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (by positivity)]
  calc
    _ ≤ ∑ _j : Fin (M+1), (coeffOneNorm p * ε)^2 :=
      sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hj j) 2
    _ = _ := by simp

/-- Absolute error between one measured norm and its genuine Hilbert norm. -/
theorem residual_error {d M : ℕ} {c : H} {D ε R : ℝ} {a : ℕ → ℂ}
    (hD : DerivativeBound c D) (hε : 0 ≤ ε) (ha : ∀ j ≤ M, ‖a j-c j‖ ≤ ε)
    (hR : 0 < R) (hRM : R ≤ (M:ℝ) - d) (p : Coeff d) :
    |‖visible M a p‖ - ‖unitVector - product c p‖| ≤
      Real.sqrt (M+1) * (coeffOneNorm p * ε) + coeffOneNorm p * (D/R) := by
  have hv := visible_perturb_le hε ha p
  have hn := abs_norm_sub_norm_le (visible M a p) (visible M c p)
  rw [visible_eq_head] at hn hv
  have hh := hidden_le hD p hR hRM
  have h₁ := head_le (unitVector - product c p) M
  have h₂ := le_head_add_tail (unitVector - product c p) M
  have hp : 0 ≤ coeffOneNorm p := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have htail := mul_nonneg hp (div_nonneg hD.1 hR.le)
  rw [abs_le] at hn ⊢
  constructor <;> linarith

/-- Ordinary Euclidean coefficient budget. -/
theorem coeffOneNorm_le_sqrt {d : ℕ} (p : Coeff d) :
    coeffOneNorm p ≤ Real.sqrt (d+1) * ‖p‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) univ (fun _ : Fin (d+1) ↦ 1)
    (fun k ↦ ‖p k‖)
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (by positivity)).mp
  simpa [coeffOneNorm, EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (d:ℝ)+1)] using h

/-- The squared coefficient budget with weights (k+1)². -/
def weightedEnergy {d : ℕ} (p : Coeff d) : ℝ :=
  ∑ k : Fin (d+1), (((k.val:ℝ)+1) * ‖p k‖)^2

private theorem reciprocal_sum (d : ℕ) :
    ∑ k : Fin (d+1), (((k.val:ℝ)+1)⁻¹)^2 ≤ 2 := by
  have h (m : ℕ) : (∑ k ∈ range (m+1), (((k:ℝ)+1)⁻¹)^2) ≤ 2 - 1/((m:ℝ)+1) := by
    induction m with
    | zero => norm_num
    | succ m hm =>
      rw [Finset.sum_range_succ]
      push_cast
      have h₁ : 0 < (m:ℝ)+1 := by positivity
      have h₂ : 0 < (m:ℝ)+1+1 := by positivity
      have hstep : (((m:ℝ)+1+1)⁻¹)^2 ≤ 1/((m:ℝ)+1) - 1/((m:ℝ)+1+1) := by
        field_simp
        nlinarith
      linarith
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (((k:ℝ)+1)⁻¹)^2)]
  exact (h _).trans (sub_le_self _ (by positivity))

/-- The weighted ellipsoid controls the coefficient one-norm independently of degree. -/
theorem coeffOneNorm_le_weighted {d : ℕ} (p : Coeff d) :
    coeffOneNorm p ≤ 2 * Real.sqrt (weightedEnergy p) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun k : Fin (d+1) ↦ ((k.val:ℝ)+1)⁻¹)
    (fun k ↦ ((k.val:ℝ)+1)*‖p k‖)
  have he k : ((k.val:ℝ)+1)⁻¹ * (((k.val:ℝ)+1)*‖p k‖) = ‖p k‖ := by
    field_simp
  simp_rw [he] at h
  have hpos : 0 ≤ weightedEnergy p := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hbd := mul_le_mul_of_nonneg_right (reciprocal_sum d) hpos
  change (coeffOneNorm p)^2 ≤ _ * weightedEnergy p at h
  exact (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (by positivity)).mp
    (by change (coeffOneNorm p)^2 ≤ _; nlinarith [Real.sq_sqrt hpos])

end HardyTable

end
