module

public import RiemannMasullo.ForMathlib.Analysis.Complex.HalfPlaneJensen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Green-kernel tails on a bounded interval of reference heights -/

public section

namespace RiemannMasullo.HalfPlaneJensen

/-- Translating the reference point from `2` to `2 + it₀` increases the quadratic
height envelope by at most `(H / (H - T))²` uniformly for `|t₀| ≤ T < H ≤ |Im z|`. -/
theorem greenKernel_sub_imaginary_le {z : ℂ} {t₀ T H : ℝ}
    (hleft : 1 / 2 ≤ z.re) (hright : z.re ≤ 1)
    (ht : |t₀| ≤ T) (hTH : T < H) (hz : H ≤ |z.im|) :
    greenKernel (z - (t₀ : ℂ) * Complex.I) ≤
      3 * (z.re - 1 / 2) * (H / (H - T)) ^ 2 / (1 + z.im ^ 2) := by
  have hT : 0 ≤ T := (abs_nonneg _).trans ht
  have hH : 0 < H := hT.trans_lt hTH
  have hdiff : 0 < H - T := sub_pos.mpr hTH
  have hdist : (H - T) * |z.im| ≤ H * |z.im - t₀| := calc
    _ ≤ H * (|z.im| - |t₀|) := by
      nlinarith only [mul_le_mul_of_nonneg_left hz hT, mul_le_mul_of_nonneg_left ht hH.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_sub_abs_le_abs_sub _ _) hH.le
  have hsq := pow_le_pow_left₀ (mul_nonneg hdiff.le (abs_nonneg _)) hdist 2
  simp only [mul_pow, sq_abs] at hsq
  have hconst := pow_le_pow_left₀ hdiff.le (sub_le_self H hT) 2
  have hrecip : 1 / (1 + (z.im - t₀) ^ 2) ≤ (H / (H - T)) ^ 2 / (1 + z.im ^ 2) := by
    rw [div_pow, div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hsq, hconst]
  have hRe : (z - (t₀ : ℂ) * Complex.I).re = z.re := by simp
  have hIm : (z - (t₀ : ℂ) * Complex.I).im = z.im - t₀ := by simp
  have hgreen := (greenKernel_bounds (s := z - (t₀ : ℂ) * Complex.I)
    (hRe.symm ▸ hleft) (hRe.symm ▸ hright)).2
  rw [hRe, hIm] at hgreen
  calc
    _ ≤ 3 * (z.re - 1 / 2) / (1 + (z.im - t₀) ^ 2) := hgreen
    _ = 3 * (z.re - 1 / 2) * (1 / (1 + (z.im - t₀) ^ 2)) := (mul_one_div _ _).symm
    _ ≤ 3 * (z.re - 1 / 2) * ((H / (H - T)) ^ 2 / (1 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hrecip (by linarith)
    _ = _ := (mul_div_assoc _ _ _).symm

/-- Reciprocal-square tail independent of the real part within the right half of the strip. -/
theorem greenKernel_sub_imaginary_le_inv_sq {z : ℂ} {t₀ T H : ℝ}
    (hleft : 1 / 2 ≤ z.re) (hright : z.re ≤ 1)
    (ht : |t₀| ≤ T) (hTH : T < H) (hz : H ≤ |z.im|) :
    greenKernel (z - (t₀ : ℂ) * Complex.I) ≤
      (3 / 2) * (H / (H - T)) ^ 2 / |z.im| ^ 2 := by
  have hpos : 0 < |z.im| := (abs_nonneg t₀).trans_lt (ht.trans_lt (hTH.trans_le hz))
  have hnum : 3 * (z.re - 1 / 2) ≤ 3 / 2 := by linarith
  refine (greenKernel_sub_imaginary_le hleft hright ht hTH hz).trans ?_
  calc
    _ ≤ (3 / 2) * (H / (H - T)) ^ 2 / (1 + z.im ^ 2) := by
      gcongr
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hpos)
      rw [sq_abs]
      linarith

end RiemannMasullo.HalfPlaneJensen
