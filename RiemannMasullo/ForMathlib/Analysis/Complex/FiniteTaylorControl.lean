module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Quantitative analytic continuation from a finite Taylor polynomial at a disk center. -/

@[expose] public noncomputable section

open Complex Metric Finset Set

namespace RiemannMasullo.FiniteTaylor

/-- The degree-`n` Taylor term evaluated at `z` about the center `c`. -/
def term (f : ℂ → ℂ) (c z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * (z - c) ^ n * iteratedDeriv n f c

/-- The first `K` Taylor terms, through degree `K - 1`. -/
def taylorSum (f : ℂ → ℂ) (c z : ℂ) (K : ℕ) : ℂ := ∑ n ∈ range K, term f c z n

theorem norm_term_le {f : ℂ → ℂ} {c z : ℂ} {R A : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hA : ∀ w ∈ sphere c R, ‖f w‖ ≤ A) (n : ℕ) :
    ‖term f c z n‖ ≤ A * (‖z - c‖ / R) ^ n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (hf.differentiableOn.diffContOnCl_ball subset_rfl) hA
  simp only [term, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * ‖z - c‖ ^ n * ((n.factorial : ℝ) * A / R ^ n) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by rw [div_pow]; field_simp

/-- The tail of the Taylor series is bounded by the geometric tail with Cauchy majorant `A`. -/
theorem norm_sub_partial_le {f : ℂ → ℂ} {c z : ℂ} {R A : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hA : ∀ w ∈ sphere c R, ‖f w‖ ≤ A)
    (hz : ‖z - c‖ < R) (K : ℕ) :
    ‖f z - taylorSum f c z K‖ ≤ A * (‖z - c‖ / R) ^ K / (1 - ‖z - c‖ / R) := by
  let r := ‖z - c‖ / R
  have hr : 0 ≤ r := div_nonneg (norm_nonneg _) hR.le
  have hr' : r < 1 := (div_lt_one hR).mpr hz
  have hsum : HasSum (term f c z) (f z) := by
    change HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ * (z - c) ^ n * iteratedDeriv n f c) (f z)
    simpa only [smul_eq_mul, mul_assoc] using Complex.hasSum_taylorSeries_on_ball
      (hf.differentiableOn.mono ball_subset_closedBall) (mem_ball_iff_norm.mpr hz)
  have he : f z - taylorSum f c z K = ∑' j : ℕ, term f c z (j + K) := by
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add K]
    simp [taylorSum]
  rw [he]
  have hg := (summable_geometric_of_lt_one hr hr').mul_left (A * r ^ K)
  calc
    _ ≤ ∑' j : ℕ, ‖term f c z (j + K)‖ := norm_tsum_le_tsum_norm
      ((summable_nat_add_iff K).mpr hsum.summable).norm
    _ ≤ ∑' j : ℕ, A * r ^ K * r ^ j :=
      (((summable_nat_add_iff K).mpr hsum.summable).norm).tsum_le_tsum (fun j ↦
        (norm_term_le hR hf hA (j + K)).trans_eq (by change A * r ^ (j + K) = _; rw [pow_add]; ring)) hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr', div_eq_mul_inv]

end RiemannMasullo.FiniteTaylor
