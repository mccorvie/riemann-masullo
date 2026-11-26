module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Gaussian mean squares for finite Riesz zero sums

Gaussian integration changes a pair of shifted zeros into a kernel decaying quadratically
in the distance between their ordinates. The resulting row-sum bound applies to a finite
height shell with multiplicities and arbitrary complex Riesz coefficients.
-/

public noncomputable section

open Finset Complex MeasureTheory
open scoped ComplexConjugate

namespace RiemannMasullo

private theorem rieszGram_integral (z : ℂ) :
    (∫ v : ℝ, Complex.exp (-1 * (v : ℂ) ^ 2 + (2 * z) * v + 0)) =
      (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) := by
  rw [integral_cexp_quadratic (by norm_num : ((-1 : ℂ).re < 0))]
  congr 1
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    norm_num
  · congr 1
    ring

private theorem rieszGram_expand {ι : Type*} (S : Finset ι) (c z : ι → ℂ) (v : ℝ) :
    ((Real.exp (-(v ^ 2)) * ‖∑ i ∈ S, c i * Complex.exp (2 * z i*v)‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
        Complex.exp (-1 * (v : ℂ) ^ 2 + 2 * (z i + conj (z j)) * v + 0) := by
  push_cast
  rw [← Complex.mul_conj']
  simp only [map_sum, map_mul, ← Complex.exp_conj, map_ofNat, Complex.conj_ofReal]
  rw [sum_mul, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [show Complex.exp (-(v : ℂ) ^ 2) *
      (c i * Complex.exp (2 * z i*v) * (conj (c j) * Complex.exp (2 * conj (z j) * v))) =
      (c i * conj (c j)) * (Complex.exp (-(v : ℂ) ^ 2) * Complex.exp (2 * z i*v) *
        Complex.exp (2 * conj (z j) * v)) by ring,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

/-- The exact Gaussian mean square of a finite sum of complex zero terms. The
indices may repeat a zero to encode its multiplicity. -/
theorem rieszZero_gaussian_meanSquare_eq {ι : Type*} (S : Finset ι) (c z : ι → ℂ) :
    ((∫ v : ℝ, Real.exp (-(v ^ 2)) * ‖∑ i ∈ S, c i * Complex.exp (2 * z i*v)‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
        ((Real.sqrt Real.pi : ℂ) * Complex.exp ((z i + conj (z j)) ^ 2)) := by
  have hint (i j : ι) : Integrable (fun v : ℝ ↦ (c i * conj (c j)) *
      Complex.exp (-1 * (v : ℂ) ^ 2 + 2 * (z i + conj (z j)) * v + 0)) :=
    (integrable_cexp_quadratic' (by norm_num : ((-1 : ℂ).re < 0)) _ _).const_mul _
  rw [← integral_complex_ofReal]
  simp_rw [rieszGram_expand]
  rw [integral_finsetSum S (fun i _ ↦ integrable_finsetSum S (fun j _ ↦ hint i j))]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum S (fun j _ ↦ hint i j)]
  simp_rw [integral_const_mul, rieszGram_integral]

private theorem rieszGram_exp_norm {z w : ℂ} (hz : |z.re| ≤ 1 / 2) (hw : |w.re| ≤ 1 / 2) :
    ‖Complex.exp ((z + conj w) ^ 2)‖ ≤ Real.exp 1 * Real.exp (-((z.im - w.im) ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have hsum : |z.re + w.re| ≤ 1 := (abs_add_le ..).trans (by linarith)
  have hsquare := sq_le_sq' (abs_le.mp hsum).1 (abs_le.mp hsum).2
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.conj_re,
    Complex.add_im, Complex.conj_im] at *
  nlinarith

private theorem rieszGram_schur {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (K : ι → ι → ℝ) (R : ℝ) (hn : ∀ i j, 0 ≤ K i j)
    (hs : ∀ i j, K i j = K j i) (hr : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ R) :
    ∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j ≤ R * ∑ i ∈ S, (a i) ^ 2 := by
  have hsym : ∑ i ∈ S, ∑ j ∈ S, (a j) ^ 2 * K i j =
      ∑ i ∈ S, ∑ j ∈ S, (a i) ^ 2 * K i j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by rw [hs j i]
  have hrow : ∑ i ∈ S, ∑ j ∈ S, (a i) ^ 2 * K i j ≤ R * ∑ i ∈ S, (a i) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun i hi ↦ ?_
    rw [← mul_sum, mul_comm R]
    exact mul_le_mul_of_nonneg_left (hr i hi) (sq_nonneg _)
  have hdouble : 2 * (∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j) ≤
      (∑ i ∈ S, ∑ j ∈ S, (a i) ^ 2 * K i j) + ∑ i ∈ S, ∑ j ∈ S, (a j) ^ 2 * K i j := by
    simp_rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
    have h := mul_le_mul_of_nonneg_right (show 2 * (a i * a j) ≤ (a i) ^ 2 + (a j) ^ 2 by
      nlinarith [sq_nonneg (a i - a j)]) (hn i j)
    linarith
  linarith

/-- A Gaussian row sum on ordinate differences controls the mean square, uniformly
over the real parts of zeros in the centered critical strip. -/
theorem rieszZero_gaussian_meanSquare_le {ι : Type*} (S : Finset ι) (c z : ι → ℂ)
    (R : ℝ) (hz : ∀ i ∈ S, |(z i).re| ≤ 1 / 2)
    (hr : ∀ i ∈ S, ∑ j ∈ S, Real.exp (-(((z i).im - (z j).im) ^ 2)) ≤ R) :
    (∫ v : ℝ, Real.exp (-(v ^ 2)) * ‖∑ i ∈ S, c i * Complex.exp (2 * z i*v)‖^2) ≤
      Real.sqrt Real.pi * Real.exp 1 * R * ∑ i ∈ S, ‖c i‖^2 := by
  let K (i j : ι) := Real.exp (-(((z i).im - (z j).im) ^ 2))
  have hschur := rieszGram_schur S (fun i ↦ ‖c i‖) K R
    (fun i j ↦ (Real.exp_pos _).le) (fun i j ↦ by unfold K; congr 2; ring) hr
  have hcast := congrArg norm (rieszZero_gaussian_meanSquare_eq S c z)
  rw [Complex.norm_of_nonneg (integral_nonneg fun _ ↦ by positivity)] at hcast
  rw [hcast, mul_assoc (Real.sqrt Real.pi * Real.exp 1) R]
  refine le_trans (norm_sum_le _ _) ?_
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖(c i * conj (c j)) *
        ((Real.sqrt Real.pi : ℂ) * Complex.exp ((z i + conj (z j)) ^ 2))‖ :=
      sum_le_sum fun i _ ↦ norm_sum_le _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (Real.sqrt Real.pi * Real.exp 1) *
        (‖c i‖ * ‖c j‖ * K i j) := by
      refine sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ ?_
      simp only [norm_mul, Complex.norm_conj, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc
        _ ≤ ‖c i‖ * ‖c j‖ * (Real.sqrt Real.pi * (Real.exp 1 * K i j)) := by
          gcongr
          exact rieszGram_exp_norm (hz i hi) (hz j hj)
        _ = _ := by ring
    _ = (Real.sqrt Real.pi * Real.exp 1) * (∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * K i j) := by
      simp_rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hschur (by positivity)

private theorem rieszGram_coefficient {ρ : ℂ} {J T t : ℝ} (hJ : 1 ≤ J)
    (hβ : ρ.re ≤ 1) (hγ : T ≤ |ρ.im|) (ht : |t| < T) :
    ‖(J : ℂ) ^ (2 * (ρ - 1 / 2 + (t : ℂ) * I)) /
        ((ρ + (t : ℂ) * I) * (ρ + 1 / 2 + (t : ℂ) * I))‖ ≤ J / (T - |t|) ^ 2 := by
  have hδ : 0 < T - |t| := sub_pos.mpr ht
  have him : T - |t| ≤ |ρ.im + t| := by
    have htri := abs_sub (ρ.im + t) t
    simp only [add_sub_cancel_right] at htri
    linarith
  have hl : T - |t| ≤ ‖ρ + (t : ℂ) * I‖ :=
    him.trans (by simpa using Complex.abs_im_le_norm (ρ + (t : ℂ) * I))
  have hr : T - |t| ≤ ‖ρ + 1 / 2 + (t : ℂ) * I‖ :=
    him.trans (by simpa using Complex.abs_im_le_norm (ρ + 1 / 2 + (t : ℂ) * I))
  have hpow : ‖(J : ℂ) ^ (2 * (ρ - 1 / 2 + (t : ℂ) * I))‖ ≤ J := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < J)]
    nth_rw 2 [← Real.rpow_one J]
    apply Real.rpow_le_rpow_of_exponent_le hJ
    simp
    linarith
  rw [norm_div, norm_mul]
  apply div_le_div₀ (by linarith) hpow (sq_pos_of_pos hδ)
  simpa only [sq] using mul_le_mul hl hr hδ.le (norm_nonneg _)

/-- A finite shell of the shifted half-Riesz zero sum. The coefficient contains both
denominators appearing after one integration of the weighted prime explicit formula.
The index set can encode zero multiplicities. -/
theorem rieszZero_gaussian_meanSquare_rieszShell {ι : Type*} (S : Finset ι)
    (ρ : ι → ℂ) (J T t R : ℝ) (hJ : 1 ≤ J) (ht : |t| < T) (hR : 0 ≤ R)
    (hβ : ∀ i ∈ S, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hγ : ∀ i ∈ S, T ≤ |(ρ i).im|)
    (hr : ∀ i ∈ S, ∑ j ∈ S, Real.exp (-(((ρ i).im - (ρ j).im) ^ 2)) ≤ R) :
    (∫ v : ℝ, Real.exp (-(v ^ 2)) *
      ‖∑ i ∈ S, ((J : ℂ) ^ (2 * (ρ i - 1 / 2 + (t : ℂ) * I)) /
        ((ρ i + (t : ℂ) * I) * (ρ i + 1 / 2 + (t : ℂ) * I))) *
        Complex.exp (2 * (ρ i - 1 / 2 + (t : ℂ) * I) * v)‖^2) ≤
      Real.sqrt Real.pi * Real.exp 1 * R * (S.card * (J / (T - |t|) ^ 2) ^ 2) := by
  let z (i : ι) := ρ i - 1 / 2 + (t : ℂ) * I
  let c (i : ι) := (J : ℂ) ^ (2 * z i) / ((ρ i + (t : ℂ) * I) * (ρ i + 1 / 2 + (t : ℂ) * I))
  have hz (i : ι) (hi : i ∈ S) : |(z i).re| ≤ 1 / 2 := by
    obtain ⟨h0, h1⟩ := hβ i hi
    simp [z, abs_le]
    constructor <;> linarith
  have hrow (i : ι) (hi : i ∈ S) :
      ∑ j ∈ S, Real.exp (-(((z i).im - (z j).im) ^ 2)) ≤ R := by
    simpa [z] using hr i hi
  refine (rieszZero_gaussian_meanSquare_le S c z R hz hrow).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc (i : ι) (hi : i ∈ S) : ‖c i‖ ≤ J / (T - |t|) ^ 2 :=
    rieszGram_coefficient hJ (hβ i hi).2 (hγ i hi) ht
  calc
    _ ≤ ∑ _i ∈ S, (J / (T - |t|) ^ 2) ^ 2 :=
      sum_le_sum fun i hi ↦ pow_le_pow_left₀ (norm_nonneg _) (hc i hi) _
    _ = _ := by simp

end RiemannMasullo
