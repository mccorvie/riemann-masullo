module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Weight estimates for a translated moving spatial window

The lemmas below certify the polynomial ratios, exponential comparison, critical-window
geometry, and supercritical growth certificate used in the weighted trace calculation for
issue #7353. They concern the explicit kernels; they assert no global trace-formula identity.
-/

public section

namespace RiemannMasullo.Isolated

/-- The nonpositive-output polynomial weight ratio is a contraction. -/
theorem moving_window_negative_polynomial_ratio
    (u v s : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (hs : 0 ≤ s) :
    ((1 + v ^ 2) / (1 + u ^ 2)) ^ (s / 4) ≤ 1 := by
  have hu : 0 ≤ u := hv.trans hvu
  have hden : 0 < 1 + u ^ 2 := by positivity
  have hratio : (1 + v ^ 2) / (1 + u ^ 2) ≤ 1 := by
    apply (div_le_one hden).2
    nlinarith
  exact Real.rpow_le_one (by positivity) hratio (by positivity)

/-- On the crossing wedge `0 ≤ x ≤ a*u`, the polynomial ratio is bounded by `a^(s/2)`.
This includes the exact dilation power needed by the trace estimate. -/
theorem moving_window_crossing_polynomial_ratio
    (a u x s : ℝ) (ha : 1 ≤ a) (hu : 0 ≤ u) (hx : 0 ≤ x)
    (hxu : x ≤ a * u) (hs : 0 ≤ s) :
    ((1 + x ^ 2) / (1 + u ^ 2)) ^ (s / 4) ≤ a ^ (s / 2) := by
  have ha0 : 0 ≤ a := by linarith
  have hden : 0 < 1 + u ^ 2 := by positivity
  have hsq : x ^ 2 ≤ (a * u) ^ 2 := (sq_le_sq₀ hx (mul_nonneg ha0 hu)).2 hxu
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hratio : (1 + x ^ 2) / (1 + u ^ 2) ≤ a ^ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [hsq]
  calc
    ((1 + x ^ 2) / (1 + u ^ 2)) ^ (s / 4)
      ≤ (a ^ 2) ^ (s / 4) := Real.rpow_le_rpow (by positivity) hratio (by positivity)
    _ = a ^ (s / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul ha0]
      congr 1
      ring

/-- The physical cutoff at the critical slope is exactly the wedge on which the
crossing exponential has nonpositive exponent. -/
theorem moving_window_critical_cutoff_iff
    (A B x u : ℝ) (hAB : 0 < A + B) :
    x ≤ B / (A + B) * (x + u) ↔ A * x ≤ B * u := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hAB]
  constructor <;> intro h <;> nlinarith

/-- The critical physical cutoff is equivalent to the normalized crossing exponential
being at most one. -/
theorem moving_window_critical_exponential_iff
    (A B x u : ℝ) (hAB : 0 < A + B) :
    x ≤ B / (A + B) * (x + u) ↔ Real.exp (A * x - B * u) ≤ 1 := by
  rw [moving_window_critical_cutoff_iff A B x u hAB, Real.exp_le_one_iff]
  exact (sub_nonpos).symm

/-- Pointwise domination of the negative-output kernel by the exponential resolvent kernel. -/
theorem moving_window_negative_kernel_le
    (B u v s : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (hs : 0 ≤ s) :
    Real.exp (-B * (u - v)) * ((1 + v ^ 2) / (1 + u ^ 2)) ^ (s / 4) ≤
      Real.exp (-B * (u - v)) := by
  simpa using mul_le_mul_of_nonneg_left
    (moving_window_negative_polynomial_ratio u v s hv hvu hs) (Real.exp_nonneg _)

/-- Pointwise domination of the crossing kernel by a dilated exponential resolvent kernel. -/
theorem moving_window_crossing_kernel_le
    (B a u x s : ℝ) (ha : 1 ≤ a) (hu : 0 ≤ u) (hx : 0 ≤ x)
    (hxu : x ≤ a * u) (hs : 0 ≤ s) :
    Real.exp ((B / a) * x - B * u) * ((1 + x ^ 2) / (1 + u ^ 2)) ^ (s / 4) ≤
      a ^ (s / 2) * Real.exp (-B * (u - x / a)) := by
  have hexp : (B / a) * x - B * u = -B * (u - x / a) := by ring
  rw [hexp]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (moving_window_crossing_polynomial_ratio a u x s ha hu hx hxu hs) (Real.exp_nonneg _)

/-- A supercritical wedge admits a positive exponential decay parameter whose translated
quadratic density grows along that wedge. These are the exact parameters in the positive
rank-one divergence example. -/
theorem moving_window_supercritical_parameters
    (A B a : ℝ) (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hgap : 0 < A * a - B) :
    let ε := (A * a - B) / (2 * (a + 1))
    0 < ε ∧ ε < A ∧ (A - ε) * a - (B + ε) = (A * a - B) / 2 := by
  dsimp
  have hden : 0 < 2 * (a + 1) := by positivity
  refine ⟨div_pos hgap hden, ?_, ?_⟩
  · apply (div_lt_iff₀ hden).2
    nlinarith
  · field_simp
    ring

/-- The positive growth rate persists on a unit-width strip below a supercritical ray. -/
theorem moving_window_supercritical_strip_growth
    (A B a u x : ℝ) (hA : 0 < A) (hB : 0 < B) (ha : 0 < a)
    (hgap : 0 < A * a - B) (hx : a * u - 1 ≤ x) :
    let ε := (A * a - B) / (2 * (a + 1))
    (A * a - B) / 2 * u - (A - ε) ≤ (A - ε) * x - (B + ε) * u := by
  dsimp
  have hp := moving_window_supercritical_parameters A B a hA hB ha hgap
  dsimp at hp
  have hcoef : 0 ≤ A - (A * a - B) / (2 * (a + 1)) := by linarith [hp.2.1]
  calc
    (A * a - B) / 2 * u - (A - (A * a - B) / (2 * (a + 1)))
      = ((A - (A * a - B) / (2 * (a + 1))) * a -
          (B + (A * a - B) / (2 * (a + 1)))) * u -
          (A - (A * a - B) / (2 * (a + 1))) := by rw [hp.2.2]
    _ = (A - (A * a - B) / (2 * (a + 1))) * (a * u - 1) -
          (B + (A * a - B) / (2 * (a + 1))) * u := by ring
    _ ≤ _ := sub_le_sub_right (mul_le_mul_of_nonneg_left hx hcoef) _

end RiemannMasullo.Isolated
