module

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Distribution.TemperateGrowth

/-! # Temperate growth on vertical lines -/

public section

open Metric Set
open scoped ContDiff

namespace RiemannMasullo

/-- A polynomial bound on a complex strip gives a temperate multiplier on
its real frequency line. A fixed frequency scale changes the derivative
constants, and all derivative orders retain the same polynomial exponent. -/
theorem hasTemperateGrowth_vertical_of_polynomial_strip
    {f : ℂ → ℂ} {a δ C : ℝ} {k : ℕ} (b : ℝ)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.re - a| ≤ δ})
    (hbound : ∀ z : ℂ, |z.re - a| ≤ δ → ‖f z‖ ≤ C * (1 + ‖z‖) ^ k) :
    Function.HasTemperateGrowth (fun t : ℝ ↦ f ((a : ℂ) + (t : ℂ) * ((b : ℂ) * Complex.I))) := by
  let d : ℂ := (b : ℂ) * Complex.I
  let line (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * d
  let g (t : ℝ) : ℂ := f (line t)
  change Function.HasTemperateGrowth g
  have hre (t : ℝ) : (line t).re = a := by simp [line, d, Complex.mul_re, Complex.mul_im]
  have hLine (t : ℝ) : line t ∈ {z : ℂ | |z.re - a| ≤ δ} := by
    change |(line t).re - a| ≤ δ
    simpa only [hre, sub_self, abs_zero] using hδ.le
  have hstep (n : ℕ) (t : ℝ) :
      HasDerivAt (fun y : ℝ ↦ d ^ n * iteratedDeriv n f (line y))
        (d ^ (n + 1) * iteratedDeriv (n + 1) f (line t)) t := by
    have hd : HasDerivAt (iteratedDeriv n f) (deriv (iteratedDeriv n f) (line t)) (line t) := by
      simpa only [iteratedDeriv_eq_iterate] using
        ((hf (line t) (hLine t)).iterated_deriv n).differentiableAt.hasDerivAt
    have hAffine : HasDerivAt (fun z : ℂ ↦ (a : ℂ) + z * d) d (t : ℂ) := by
      simpa using (((hasDerivAt_id (t : ℂ)).mul_const d).const_add (a : ℂ))
    have h := ((hd.comp (t : ℂ) hAffine).comp_ofReal).const_mul (d ^ n)
    convert h using 1
    · rfl
    · rw [iteratedDeriv_succ, pow_succ]
      ring
  have hiter (n : ℕ) : iteratedDeriv n g = fun t ↦ d ^ n * iteratedDeriv n f (line t) := by
    induction n with
    | zero => simp [g]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext fun t ↦ (hstep n t).deriv
  have hclosed (t : ℝ) : closedBall (line t) δ ⊆ {z : ℂ | |z.re - a| ≤ δ} := by
    intro z hz
    have h := (Complex.abs_re_le_norm (z - line t)).trans (mem_closedBall_iff_norm.mp hz)
    simpa only [mem_ofPred_eq, Complex.sub_re, hre] using h
  let L := 1 + δ + |a| + ‖d‖
  let D : ℝ := C * L ^ k
  have hSphere (t : ℝ) (z : ℂ) (hz : z ∈ sphere (line t) δ) :
      ‖f z‖ ≤ D * (1 + ‖t‖) ^ k := by
    have hline : ‖line t‖ ≤ |a| + ‖t‖ * ‖d‖ := by
      simpa only [line, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        (norm_add_le (a : ℂ) ((t : ℂ) * d))
    have hdist : ‖z - line t‖ = δ := mem_sphere_iff_norm.mp hz
    have hnz : ‖z‖ ≤ δ + (|a| + ‖t‖ * ‖d‖) := by
      simpa only [sub_add_cancel] using
        (norm_add_le (z - line t) (line t)).trans (add_le_add hdist.le hline)
    have hbase : 1 + ‖z‖ ≤ L * (1 + ‖t‖) := by
      dsimp only [L]
      nlinarith [abs_nonneg a, norm_nonneg t, norm_nonneg d,
        mul_nonneg hδ.le (norm_nonneg t), mul_nonneg (abs_nonneg a) (norm_nonneg t)]
    calc
      ‖f z‖ ≤ C * (1 + ‖z‖) ^ k :=
        hbound z (hclosed t (sphere_subset_closedBall hz))
      _ ≤ C * (L * (1 + ‖t‖)) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) hC
      _ = D * (1 + ‖t‖) ^ k := by simp only [D, mul_pow, mul_assoc]
  refine ⟨?_, fun n ↦ ⟨k, ‖d‖ ^ n * (n.factorial * D) / δ ^ n, fun t ↦ ?_⟩⟩
  · apply contDiff_of_differentiable_iteratedDeriv
    intro n _ t
    rw [hiter n]
    exact (hstep n t).differentiableAt
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter n, norm_mul, norm_pow]
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hδ
      (hf.differentiableOn.diffContOnCl_ball (hclosed t)) (hSphere t)
    calc
      _ ≤ ‖d‖ ^ n * ((n.factorial : ℝ) * (D * (1 + ‖t‖) ^ k) / δ ^ n) :=
        mul_le_mul_of_nonneg_left hcauchy (pow_nonneg (norm_nonneg _) _)
      _ = _ := by ring

end RiemannMasullo
