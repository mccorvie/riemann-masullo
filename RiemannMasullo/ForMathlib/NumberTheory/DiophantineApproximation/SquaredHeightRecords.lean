module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A sufficient condition for strict squared-height records

This standalone file concerns the scalar model behind issue #7336. It does not
construct a Hecke character and does not refute the theorem in that issue.

The separation hypothesis is the homogeneous polynomial estimate obtained by
comparing two rotation indices. The conclusion shows that a sufficiently small
inhomogeneous denominator is automatically a strict record against *all* signed
indices in the squared-height window. Thus restricting to records does not
remove hypothetical super-polynomial approximations.
-/

public section

namespace RiemannMasullo.Isolated

/-- A squared-height comparison controls the difference of two signed indices.
The parameter `c` allows the actual height `2 + ‖s_n‖ = 2 + c * |n|`.
-/
theorem scaled_squared_height_window (c : ℝ) (hc : 0 < c) (m n : ℤ)
    (hwindow : 2 + c * |(m : ℝ)| ≤ (2 + c * |(n : ℝ)|) ^ 2) :
    1 + |(m : ℝ) - (n : ℝ)| ≤
      (1 + 2 / c) * (2 + c * |(n : ℝ)|) ^ 2 := by
  let H : ℝ := 2 + c * |(n : ℝ)|
  have hH : 2 ≤ H := by
    dsimp [H]
    nlinarith [mul_nonneg hc.le (abs_nonneg (n : ℝ))]
  have hm : c * |(m : ℝ)| ≤ H ^ 2 - 2 := by
    dsimp only [H]
    linarith
  have hn : c * |(n : ℝ)| = H - 2 := by
    dsimp [H]
    ring
  have hab := mul_le_mul_of_nonneg_left
    (abs_sub (m : ℝ) (n : ℝ)) hc.le
  have hcH : c ≤ c * H ^ 2 := by
    have hsq : 0 ≤ H ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hc.le hsq]
  have hnum : c * (1 + |(m : ℝ) - (n : ℝ)|) ≤ (c + 2) * H ^ 2 := by
    nlinarith
  apply le_of_mul_le_mul_left (a := c) ?_ hc
  calc
    c * (1 + |(m : ℝ) - (n : ℝ)|) ≤ (c + 2) * H ^ 2 := hnum
    _ = c * ((1 + 2 / c) * (2 + c * |(n : ℝ)|) ^ 2) := by
      dsimp only [H]
      field_simp [hc.ne']

/-- Under homogeneous polynomial separation, a sufficiently accurate
inhomogeneous approximation is a strict squared-height record. The conclusion
compares every integer index, including negative indices, and is therefore
stronger than comparison only with the eligible centers of issue #7336.
-/
theorem strong_approximation_is_squared_height_record
    (z : ℤ → ℂ) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (d : ℕ)
    (hseparation : ∀ m n : ℤ, m ≠ n →
      1 ≤ C * (1 + |(m : ℝ) - (n : ℝ)|) ^ d * ‖z m - z n‖)
    (n : ℤ)
    (hsmall : 2 * C * ((1 + 2 / c) * (2 + c * |(n : ℝ)|) ^ 2) ^ d *
      ‖1 - z n‖ < 1) :
    ∀ m : ℤ, m ≠ n →
      2 + c * |(m : ℝ)| ≤ (2 + c * |(n : ℝ)|) ^ 2 →
      ‖1 - z n‖ < ‖1 - z m‖ := by
  intro m hmn hwindow
  by_contra hnot
  have hdelta : ‖1 - z m‖ ≤ ‖1 - z n‖ := le_of_not_gt hnot
  have htriangle : ‖z m - z n‖ ≤ ‖1 - z m‖ + ‖1 - z n‖ := by
    calc
      ‖z m - z n‖ = ‖(z m - 1) + (1 - z n)‖ := by congr 1; ring
      _ ≤ ‖z m - 1‖ + ‖1 - z n‖ := norm_add_le _ _
      _ = ‖1 - z m‖ + ‖1 - z n‖ := by rw [norm_sub_rev (z m) (1 : ℂ)]
  have hnorm : ‖z m - z n‖ ≤ 2 * ‖1 - z n‖ := by linarith
  have hweight : C * (1 + |(m : ℝ) - (n : ℝ)|) ^ d ≤
      C * ((1 + 2 / c) * (2 + c * |(n : ℝ)|) ^ 2) ^ d := by
    gcongr
    exact scaled_squared_height_window c hc m n hwindow
  have hproduct := mul_le_mul hweight hnorm (norm_nonneg (z m - z n))
    (show 0 ≤ C * ((1 + 2 / c) * (2 + c * |(n : ℝ)|) ^ 2) ^ d by positivity)
  have hlower := hseparation m n hmn
  nlinarith

/-- Strict squared-height records are separated by more than squaring, with
strictly decreasing errors. This is a consequence of the definition and requires
no Diophantine hypothesis.
-/
theorem strict_squared_height_records_separated {ι : Type*}
    (H δ : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (_hi : 1 ≤ H i) (hj : 1 ≤ H j) (horder : H i ≤ H j)
    (hrecord_i : ∀ k, k ≠ i → H k ≤ (H i) ^ 2 → δ i < δ k)
    (hrecord_j : ∀ k, k ≠ j → H k ≤ (H j) ^ 2 → δ j < δ k) :
    (H i) ^ 2 < H j ∧ δ j < δ i := by
  have hcompare : H i ≤ (H j) ^ 2 := by nlinarith
  have hdelta := hrecord_j i hij hcompare
  refine ⟨?_, hdelta⟩
  by_contra hnot
  have hreverse := hrecord_i j hij.symm (le_of_not_gt hnot)
  exact (lt_asymm hdelta hreverse)

/-- Under polynomial separation within squared-height windows, a polynomial
lower bound on strict records extends to every index. The scalar separation
assumption follows from the metric triangle inequality and a lower bound on
the distance between distinct orbit points. Its contrapositive says that a
global failure of polynomial bounds cannot disappear on restriction to records.
-/
theorem polynomial_bound_of_squared_record_bound {ι : Type*}
    (H δ : ι → ℝ) (hH : ∀ i, 1 ≤ H i) (hδ : ∀ i, 0 ≤ δ i)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (p d : ℕ)
    (hseparation : ∀ i j, j ≠ i → H j ≤ (H i) ^ 2 →
      1 ≤ K * (H i) ^ p * (δ i + δ j))
    (hrecords : ∀ i,
      (∀ j, j ≠ i → H j ≤ (H i) ^ 2 → δ i < δ j) →
      1 ≤ C * (H i) ^ d * δ i) :
    ∀ i, 1 ≤ (2 * K + C) * (H i) ^ (p + d) * δ i := by
  intro i
  have hH0 : 0 ≤ H i := (by norm_num : (0 : ℝ) ≤ 1).trans (hH i)
  have hp1 : 1 ≤ (H i) ^ p := one_le_pow₀ (hH i)
  have hd1 : 1 ≤ (H i) ^ d := one_le_pow₀ (hH i)
  have hp0 : 0 ≤ (H i) ^ p := pow_nonneg hH0 p
  have hd0 : 0 ≤ (H i) ^ d := pow_nonneg hH0 d
  have hp_le : (H i) ^ p ≤ (H i) ^ (p + d) := by
    rw [pow_add]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hp0
  have hd_le : (H i) ^ d ≤ (H i) ^ (p + d) := by
    rw [pow_add]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hd0
  have htotal : 0 ≤ 2 * K + C := by positivity
  by_cases hsmall : 2 * K * (H i) ^ p * δ i < 1
  · have hrecord : ∀ j, j ≠ i → H j ≤ (H i) ^ 2 → δ i < δ j := by
      intro j hji hwindow
      by_contra hnot
      have hjiδ : δ j ≤ δ i := le_of_not_gt hnot
      have hpair := hseparation i j hji hwindow
      have hupper := mul_le_mul_of_nonneg_left
        (add_le_add_left hjiδ (δ i)) (mul_nonneg hK hp0)
      nlinarith
    have hcoeff : C * (H i) ^ d ≤ (2 * K + C) * (H i) ^ (p + d) :=
      mul_le_mul (by linarith) hd_le hd0 htotal
    exact (hrecords i hrecord).trans (mul_le_mul_of_nonneg_right hcoeff (hδ i))
  · have hcoeff : (2 * K) * (H i) ^ p ≤ (2 * K + C) * (H i) ^ (p + d) :=
      mul_le_mul (by linarith) hp_le hp0 htotal
    exact (le_of_not_gt hsmall).trans (mul_le_mul_of_nonneg_right hcoeff (hδ i))

end RiemannMasullo.Isolated
