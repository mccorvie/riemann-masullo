module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-! # Centering the reciprocal annulus along the square-root frequency path -/

public section

open Filter Set
open scoped Topology

namespace RiemannMasullo

private theorem reciprocalAnnulus_width_mem_Icc (L : ℝ) :
    (1 + |L|)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  have h : 1 ≤ 1 + |L| := le_add_of_nonneg_right (abs_nonneg L)
  exact ⟨inv_nonneg.mpr (zero_le_one.trans h), (inv_le_one₀ (zero_lt_one.trans_le h)).mpr h⟩

/-- Each fixed logarithmic coordinate, shifted by `-log (sqrt L)`, eventually
lies in the plateau of the reciprocal annulus of spatial radius `L`. -/
theorem eventually_mem_reciprocalAnnulus_centered_sqrt (z : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp z / Real.sqrt L ∈
      Icc (L⁻¹ + (1 + |L|)⁻¹) (L - (1 + |L|)⁻¹) := by
  have hSmall : Tendsto (fun L : ℝ ↦ 2 * (Real.sqrt L)⁻¹) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero] using Real.tendsto_sqrt_atTop.inv_tendsto_atTop.const_mul 2
  have hRootLarge : ∀ᶠ L : ℝ in atTop, Real.exp z ≤ Real.sqrt L :=
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (Real.exp z))
  filter_upwards [eventually_ge_atTop (2 : ℝ), hSmall.eventually_lt_const (Real.exp_pos z),
    hRootLarge] with L hL hLo hHi
  have hLpos : 0 < L := (by norm_num : (0 : ℝ) < 2).trans_le hL
  have hSqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hWidthInv : (1 + |L|)⁻¹ ≤ L⁻¹ :=
    inv_anti₀ hLpos ((le_abs_self L).trans (le_add_of_nonneg_left zero_le_one))
  have hInvMul : L⁻¹ * Real.sqrt L = (Real.sqrt L)⁻¹ := by
    calc
      L⁻¹ * Real.sqrt L = (Real.sqrt L * Real.sqrt L)⁻¹ * Real.sqrt L := by
        rw [Real.mul_self_sqrt hLpos.le]
      _ = (Real.sqrt L)⁻¹ := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hSqrt.ne', mul_one]
  constructor
  · apply (le_div_iff₀ hSqrt).mpr
    calc
      (L⁻¹ + (1 + |L|)⁻¹) * Real.sqrt L ≤ (L⁻¹ + L⁻¹) * Real.sqrt L :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl hWidthInv) hSqrt.le
      _ = 2 * (Real.sqrt L)⁻¹ := by rw [← two_mul, mul_assoc, hInvMul]
      _ ≤ Real.exp z := hLo.le
  · exact ((div_le_one₀ hSqrt).mpr hHi).trans (by
      linarith [(reciprocalAnnulus_width_mem_Icc L).2])

/-- The square root of the relative frequency transition width tends to zero
along the square-root frequency path. -/
theorem tendsto_sqrt_reciprocalAnnulus_width_div_sqrt :
    Tendsto (fun L : ℝ ↦ Real.sqrt ((1 + |L|)⁻¹ / Real.sqrt L)) atTop (𝓝 0) := by
  have hInv : Tendsto (fun L : ℝ ↦ (Real.sqrt L)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_sqrt_atTop.inv_tendsto_atTop
  have hRatio : Tendsto (fun L : ℝ ↦ (1 + |L|)⁻¹ / Real.sqrt L) atTop (𝓝 0) := by
    refine squeeze_zero
      (fun L ↦ div_nonneg (reciprocalAnnulus_width_mem_Icc L).1 (Real.sqrt_nonneg L)) ?_ hInv
    intro L
    rw [← one_div (Real.sqrt L)]
    exact div_le_div_of_nonneg_right (reciprocalAnnulus_width_mem_Icc L).2 (Real.sqrt_nonneg L)
  simpa only [Real.sqrt_zero] using hRatio.sqrt

end RiemannMasullo
