module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Local symbol bounds from rapidly decreasing derivatives

A derivative with a polynomial decay bound has a local exponential envelope whose
coefficient keeps the same polynomial decay in the center. The mean value theorem
converts this into the two-point bound used by positive jump-energy estimates.
-/

@[expose] public noncomputable section
open Set Real
namespace RiemannMasullo

private theorem polynomial_le_local_exp (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ n ≤ ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8)) * Real.exp (r / 8) := by
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp ((1 + r) / 8) (by positivity) n)
  rw [div_pow] at hp
  have hp' := (div_le_iff₀ (by positivity : 0 < (8 : ℝ) ^ n)).mp hp
  rw [show (1 + r) / 8 = 1 / 8 + r / 8 by ring, Real.exp_add] at hp'
  convert hp' using 1; ring

private theorem polynomial_weight_shift (n : ℕ) (u z : ℝ) :
    (1 + |z|) ^ n ≤ (1 + |u|) ^ n * (1 + |u - z|) ^ n := by
  have ht : |z| ≤ |u| + |u - z| := by
    have h := abs_add_le u (z - u)
    simpa only [add_sub_cancel, abs_sub_comm z u] using h
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg (abs_nonneg u) (abs_nonneg (u - z))]

/-- Polynomial decay of a derivative gives a local exponential derivative envelope,
uniformly in its chosen center. The coefficient retains the full polynomial decay. -/
theorem norm_deriv_le_local_exp_of_decay {b : ℝ → ℂ} {D : ℝ} (hD : 0 ≤ D) (n : ℕ)
    (hb : ∀ u, ‖deriv b u‖ * (1 + |u|) ^ n ≤ D) (u z : ℝ) :
    ‖deriv b u‖ ≤
      (D * ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8)) / (1 + |z|) ^ n) *
        Real.exp (|u - z| / 8) := by
  have hw : 0 < (1 + |z|) ^ n := by positivity
  have hbound : ‖deriv b u‖ * (1 + |z|) ^ n ≤
      D * (((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8)) * Real.exp (|u - z| / 8)) := by
    calc
      _ ≤ ‖deriv b u‖ * ((1 + |u|) ^ n * (1 + |u - z|) ^ n) :=
        mul_le_mul_of_nonneg_left (polynomial_weight_shift n u z) (norm_nonneg _)
      _ = (‖deriv b u‖ * (1 + |u|) ^ n) * (1 + |u - z|) ^ n := by ring
      _ ≤ D * (1 + |u - z|) ^ n := mul_le_mul_of_nonneg_right (hb u) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_le_local_exp n (abs_nonneg _)) hD
  have he := (le_div_iff₀ hw).mpr hbound
  convert he using 1; ring

private theorem abs_sub_le_endpoints {u x y z : ℝ} (hu : u ∈ uIcc x y) :
    |u - z| ≤ |x - z| + |y - z| := by
  rw [abs_le]
  rcases mem_uIcc.mp hu with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;>
    constructor <;> linarith [neg_abs_le (x - z), le_abs_self (x - z),
      neg_abs_le (y - z), le_abs_self (y - z), abs_nonneg (x - z), abs_nonneg (y - z)]

/-- A locally exponential derivative envelope gives the weighted two-point Lipschitz
bound used by the nonlocal residual estimate. -/
theorem norm_sub_le_local_exp_of_deriv {b : ℝ → ℂ} (hb : Differentiable ℝ b)
    {A z : ℝ} (hA : 0 ≤ A)
    (hderiv : ∀ u, ‖deriv b u‖ ≤ A * Real.exp (|u - z| / 8)) (x y : ℝ) :
    ‖b x - b y‖ ≤ A * |x - y| * Real.exp ((|x - z| + |y - z|) / 8) := by
  have hbound : ∀ u ∈ uIcc x y, ‖deriv b u‖ ≤
      A * Real.exp ((|x - z| + |y - z|) / 8) := by
    intro u hu
    apply (hderiv u).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    linarith [abs_sub_le_endpoints (z := z) hu]
  have he := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le
    (fun u _ ↦ hb u) hbound (right_mem_uIcc : y ∈ uIcc x y) (left_mem_uIcc : x ∈ uIcc x y)
  simpa only [Real.norm_eq_abs, mul_right_comm] using he

/-- Rapid polynomial derivative decay implies the spacing-independent local symbol
bound, with an explicit constant and arbitrary polynomial order. -/
theorem norm_sub_le_local_exp_of_deriv_decay {b : ℝ → ℂ} (hb : Differentiable ℝ b)
    {D : ℝ} (hD : 0 ≤ D) (n : ℕ) (hderiv : ∀ u, ‖deriv b u‖ * (1 + |u|) ^ n ≤ D)
    (z x y : ℝ) :
    ‖b x - b y‖ ≤
      (D * ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8)) / (1 + |z|) ^ n) *
        |x - y| * Real.exp ((|x - z| + |y - z|) / 8) :=
  norm_sub_le_local_exp_of_deriv hb (by positivity)
    (fun u ↦ norm_deriv_le_local_exp_of_decay hD n hderiv u z) x y

end RiemannMasullo
