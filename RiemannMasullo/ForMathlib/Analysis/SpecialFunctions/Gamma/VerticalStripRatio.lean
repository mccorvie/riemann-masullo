module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Horizontal gamma ratios on vertical strips

Euler's limit formula expresses the logarithmic modulus of gamma as a sum of logarithms.
Their second derivatives along bounded horizontal segments have a summable bound independent
of the height. Interpolation between real parts zero and one, followed by the gamma recurrence,
gives the exact power of the height without a complex Stirling expansion.
-/

public section

open Filter Finset Set
open scoped Topology

namespace RiemannMasullo
/-- On a bounded real interval a summable curvature bound controls the error in
interpolating each logarithm in Euler's product between zero and one. -/
private theorem gammaLogTerm_interpolation {M t : ℝ} (hM : 1 ≤ M) (ht : 1 ≤ |t|)
    (k : ℕ) {x : ℝ} (hx : |x| ≤ M) :
    let f (y : ℝ) := Real.log ((y + k) ^ 2 + t ^ 2) / 2
    |f x - f 0 - x * (f 1 - f 0)| ≤ 4 * M ^ 2 * (M + 1) ^ 2 / (k + 1 : ℝ) ^ 2 := by
  let D (y : ℝ) := (y + k) ^ 2 + t ^ 2
  let f (y : ℝ) := Real.log (D y) / 2
  let g (y : ℝ) := (y + k) / D y
  let B := 2 * (M + 1) ^ 2 / (k + 1 : ℝ) ^ 2
  let S := Icc (-M) M
  have ht₂ : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hD (y : ℝ) : 0 < D y := by dsimp [D]; nlinarith [sq_nonneg (y + k)]
  have hD' (y : ℝ) : HasDerivAt D (2 * (y + k)) y := by
    convert (((hasDerivAt_id y).add_const (k : ℝ)).pow 2).add_const (t ^ 2) using 1 <;> simp [D]
  have hf' (y : ℝ) : HasDerivAt f (g y) y := by
    convert ((hD' y).log (hD y).ne').div_const 2 using 1
    dsimp [g]
    ring
  have hg' (y : ℝ) : HasDerivAt g ((t ^ 2 - (y + k) ^ 2) / D y ^ 2) y := by
    convert ((hasDerivAt_id y).add_const (k : ℝ)).div (hD' y) (hD y).ne' using 1
    · rfl
    · dsimp only [id_eq, D]
      ring
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (y : ℝ) (hy : y ∈ S) : ‖(t ^ 2 - (y + k) ^ 2) / D y ^ 2‖ ≤ B := by
    have h₁ : |t ^ 2 - (y + k) ^ 2| ≤ D y := by
      rw [abs_le]
      constructor <;> dsimp [D] <;> nlinarith [sq_nonneg (y + k), sq_nonneg t]
    have hy' : |1 - y| ≤ M + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h₂ : (1 - y) ^ 2 ≤ (M + 1) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hy' 2
    have h₃ : (k + 1 : ℝ) ^ 2 ≤ 2 * (M + 1) ^ 2 * D y := by
      have hM₂ : 1 ≤ (M + 1) ^ 2 := by nlinarith [sq_nonneg M]
      dsimp only [D]
      nlinarith [sq_nonneg ((y + k) - (1 - y)),
        mul_le_mul_of_nonneg_right hM₂ (sq_nonneg (y + k)),
        mul_le_mul_of_nonneg_left ht₂ (sq_nonneg (M + 1))]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos (hD y))]
    calc
      _ ≤ D y / D y ^ 2 := div_le_div_of_nonneg_right h₁ (sq_nonneg _)
      _ = 1 / D y := by field_simp
      _ ≤ B := (div_le_div_iff₀ (hD y) (by positivity : 0 < (k + 1 : ℝ) ^ 2)).mpr (by simpa using h₃)
  have h₀ : (0 : ℝ) ∈ S := ⟨by linarith, by linarith⟩
  have hg (y : ℝ) (hy : y ∈ S) : ‖g y - g 0‖ ≤ B * M := by
    have h := (convex_Icc (-M) M).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ ↦ (hg' z).hasDerivWithinAt) hbound h₀ hy
    rw [sub_zero, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hy) hB)
  have hr (y : ℝ) (hy : y ∈ S) : |f y - f 0 - y * g 0| ≤ B * M * |y| := by
    have hd (z : ℝ) : HasDerivAt (fun w ↦ f w - w * g 0) (g z - g 0) z := by
      simpa only [one_mul, Pi.sub_def, id_eq] using (hf' z).sub ((hasDerivAt_id z).mul_const (g 0))
    have h := (convex_Icc (-M) M).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ ↦ (hd z).hasDerivWithinAt) hg h₀ hy
    simpa only [zero_mul, sub_zero, Real.norm_eq_abs, sub_right_comm (f y)] using h
  have h₁ : (1 : ℝ) ∈ S := ⟨by linarith, hM⟩
  calc
    |f x - f 0 - x * (f 1 - f 0)| =
        |(f x - f 0 - x * g 0) - x * (f 1 - f 0 - 1 * g 0)| := by congr 1; ring
    _ ≤ |f x - f 0 - x * g 0| + |x| * |f 1 - f 0 - 1 * g 0| := by
      simpa only [abs_mul] using abs_sub (f x - f 0 - x * g 0) (x * (f 1 - f 0 - 1 * g 0))
    _ ≤ B * M * |x| + |x| * (B * M * |(1 : ℝ)|) :=
      add_le_add (hr x (abs_le.mp hx)) (mul_le_mul_of_nonneg_left (hr 1 h₁) (abs_nonneg x))
    _ ≤ B * M * M + M * (B * M) := by
      rw [abs_one, mul_one]
      gcongr
    _ = _ := by dsimp [B]; ring

private theorem gammaLogSeq_formula (x t : ℝ) (ht : t ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    Real.log ‖Complex.GammaSeq ⟨x, t⟩ n‖ = x * Real.log n + Real.log n.factorial -
      ∑ k ∈ range (n + 1), Real.log ((x + k) ^ 2 + t ^ 2) / 2 := by
  let z : ℂ := ⟨x,t⟩
  have hterm (k : ℕ) : z + k ≠ 0 := fun h ↦ ht (by simpa [z] using congrArg Complex.im h)
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hp : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  change Real.log ‖Complex.GammaSeq z n‖ = _
  rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod,
    ← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnp,
    ← Complex.ofReal_natCast n.factorial, Complex.norm_of_nonneg hp.le,
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hnp _).ne' hp.ne')
      (Finset.prod_ne_zero_iff.mpr (fun k _ ↦ norm_ne_zero_iff.mpr (hterm k))),
    Real.log_mul (Real.rpow_pos_of_pos hnp _).ne' hp.ne', Real.log_rpow hnp,
    Real.log_prod (fun k _ ↦ norm_ne_zero_iff.mpr (hterm k))]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
  simp only [z, Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, add_zero, sq]

/-- The logarithmic modulus of gamma on a horizontal segment is within a bounded error of its
affine interpolant at zero and one, uniformly as the absolute imaginary part grows. -/
private theorem gammaLog_interpolation {M : ℝ} (hM : 1 ≤ M) :
    ∃ C : ℝ, ∀ x t : ℝ, |x| ≤ M → 1 ≤ |t| →
      |Real.log ‖Complex.Gamma ⟨x,t⟩‖ - Real.log ‖Complex.Gamma ⟨0,t⟩‖ - x * (Real.log |t|)| ≤ C := by
  let b (k : ℕ) := 4 * M ^ 2 * (M + 1) ^ 2 / (k + 1 : ℝ) ^ 2
  have hb : Summable b := by
    have h := (summable_nat_add_iff (f := fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide))
    simpa only [b, Nat.cast_add, Nat.cast_one, mul_one_div] using h.mul_left (4 * M ^ 2 * (M + 1) ^ 2)
  refine ⟨∑' k, b k, fun x t hx ht ↦ ?_⟩
  have ht₀ : t ≠ 0 := by rintro rfl; norm_num at ht
  let f (k : ℕ) (y : ℝ) := Real.log ((y + k) ^ 2 + t ^ 2) / 2
  let A (y : ℝ) (n : ℕ) := Real.log ‖Complex.GammaSeq ⟨y,t⟩ n‖
  let G (y : ℝ) := Real.log ‖Complex.Gamma ⟨y,t⟩‖
  have hG (y : ℝ) : Complex.Gamma ⟨y,t⟩ ≠ 0 := by
    rw [ne_eq, Complex.Gamma_eq_zero_iff]
    rintro ⟨m, he⟩
    exact ht₀ (by simpa using congrArg Complex.im he)
  have hlim (y : ℝ) : Tendsto (A y) atTop (𝓝 (G y)) :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr (hG y))).tendsto.comp (Complex.GammaSeq_tendsto_Gamma _).norm
  have hbound : |G x - G 0 - x * (G 1 - G 0)| ≤ ∑' k, b k := by
    apply le_of_tendsto (((hlim x).sub (hlim 0)).sub (tendsto_const_nhds.mul ((hlim 1).sub (hlim 0)))).abs
    filter_upwards [eventually_ne_atTop 0] with n hn
    let S := range (n + 1)
    have hsum : A x n - A 0 n - x * (A 1 n - A 0 n) =
        -(∑ k ∈ S, (f k x - f k 0 - x * (f k 1 - f k 0))) := by
      simp only [A, gammaLogSeq_formula _ _ ht₀ n hn, S, sum_sub_distrib, ← mul_sum, f]
      ring
    rw [hsum, abs_neg]
    calc
      _ ≤ ∑ k ∈ S, |f k x - f k 0 - x * (f k 1 - f k 0)| := by
        simpa only [← Real.norm_eq_abs] using norm_sum_le S (fun k ↦ f k x - f k 0 - x * (f k 1 - f k 0))
      _ ≤ ∑ k ∈ S, b k := sum_le_sum fun k _ ↦ gammaLogTerm_interpolation hM ht k hx
      _ ≤ _ := hb.sum_le_tsum S fun k _ ↦ by dsimp [b]; positivity
  have hz : (⟨0,t⟩ : ℂ) ≠ 0 := fun he ↦ ht₀ (congrArg Complex.im he)
  have hn : ‖(⟨0,t⟩ : ℂ)‖ = |t| := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [← sq, Real.sqrt_sq_eq_abs]
  have hrec : G 1 - G 0 = Real.log |t| := by
    dsimp only [G]
    rw [show (⟨1,t⟩ : ℂ) = ⟨0,t⟩ + 1 by apply Complex.ext <;> simp,
      Complex.Gamma_add_one _ hz, norm_mul, hn, Real.log_mul (abs_ne_zero.mpr ht₀) (norm_ne_zero_iff.mpr (hG 0))]
    ring
  rwa [hrec] at hbound

/-- On a bounded range of real parts, a quotient of gamma factors at a common height
is bounded by a constant times the height to the difference of their real parts. -/
theorem norm_Gamma_div_le_rpow_on_strip {M : ℝ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y t : ℝ, |x| ≤ M → |y| ≤ M → 1 ≤ |t| →
      ‖Complex.Gamma ⟨x,t⟩ / Complex.Gamma ⟨y,t⟩‖ ≤ C * |t| ^ (x - y) := by
  obtain ⟨B, hB⟩ := gammaLog_interpolation hM
  refine ⟨Real.exp (2 * B), Real.exp_pos _, fun x y t hx hy ht ↦ ?_⟩
  have hne (z : ℝ) : Complex.Gamma ⟨z,t⟩ ≠ 0 := by
    rw [ne_eq, Complex.Gamma_eq_zero_iff]
    rintro ⟨m, hm⟩
    have h : t = 0 := by simpa using congrArg Complex.im hm
    norm_num [h] at ht
  have ht' := zero_lt_one.trans_le ht
  rw [norm_div, ← Real.log_le_log_iff (div_pos (norm_pos_iff.mpr (hne _)) (norm_pos_iff.mpr (hne _)))
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht' _)),
    Real.log_div (norm_ne_zero_iff.mpr (hne _)) (norm_ne_zero_iff.mpr (hne _)),
    Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos ht' _).ne', Real.log_exp, Real.log_rpow ht']
  linarith [(abs_le.mp (hB x t hx ht)).2, (abs_le.mp (hB y t hy ht)).1]

end RiemannMasullo
