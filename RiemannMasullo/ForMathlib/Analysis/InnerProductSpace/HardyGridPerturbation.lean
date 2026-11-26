module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyPolynomialGrid
import Mathlib.Tactic

/-! # Perturbation bounds for finite Hardy grids

A feasible trial bounds the grid residual after accounting for the entry error and
rounding the polynomial. The canonical dyadic entry error has an inverse-square-root bound. -/

@[expose] public noncomputable section

open Real HardyTable Filter Finset Set
open scoped Topology

namespace HardyTable

/-- Finite quadrature and grid rounding add an explicit error to any feasible
trial in the true Hilbert norm. The estimate is uniform in the trial. -/
theorem gridNorm_le_trial_of_row_error (n : ℕ) (a : ℕ → ℂ) (c : H) {A ε : ℝ}
    (hA : 0 ≤ A) (ha : ∀ j ≤ linearCut n, ‖a j‖ ≤ A) (hε : 0 ≤ ε)
    (herr : ∀ j ≤ linearCut n, ‖a j - c j‖ ≤ ε)
    (p : Coeff n) (hp : p ∈ ellipsoid n) :
    gridNorm n a ≤ ‖unitVector-product c p‖ +
      2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*ε + 4*A/((n:ℝ)+1) := by
  obtain ⟨r,_,hmin,hbest⟩ := exists_leastSquares (M:=linearCut n) a
    (ellipsoid_compact n) (ellipsoid_nonempty n)
  have hbase := (gridNorm_bounds n a hA ha).2
  rw [hmin,Real.sqrt_sq (norm_nonneg _)] at hbase
  have hl : coeffOneNorm p ≤ 2*Real.sqrt ((n:ℝ)+1) :=
    (coeffOneNorm_le_weighted p).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp) (by norm_num))
  have hdiff := visible_perturb_le hε herr p
  have hbound : ‖visible (linearCut n) a p‖ ≤ ‖unitVector-product c p‖ +
      2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*ε := by
    calc
      _ ≤ ‖visible (linearCut n) c p‖ + ‖visible (linearCut n) a p-visible (linearCut n) c p‖ :=
        by linarith [norm_le_norm_sub_add (visible (linearCut n) a p) (visible (linearCut n) c p)]
      _ ≤ ‖unitVector-product c p‖ + Real.sqrt ((linearCut n:ℝ)+1) * (coeffOneNorm p*ε) := by
        gcongr
        · exact (visible_eq_head (linearCut n) c p) ▸ head_le _ _
      _ ≤ _ := by
        rw [Real.sqrt_mul (by positivity : 0≤(n:ℝ)+1)]
        apply add_le_add_right
        calc
          _ ≤ Real.sqrt ((linearCut n:ℝ)+1) * (2*Real.sqrt ((n:ℝ)+1)*ε) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hl hε) (Real.sqrt_nonneg _)
          _ = _ := by ring
  linarith [hbest p hp]

private theorem one_add_le_pow_two (n : ℕ) : (n:ℝ)+1 ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih => push_cast; rw [pow_succ]; nlinarith [one_le_pow₀ (n:=n) (by norm_num : 1≤(2:ℝ))]

/-- The exponentially small error in the canonical row contributes at most
one inverse square root, also at the initial grid index. -/
theorem canonical_row_visible_error_le (n : ℕ) :
    2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*(1/2:ℝ)^(2*linearCut n) ≤
      1 / Real.sqrt ((n:ℝ)+1) := by
  have hpos : 0 < (n:ℝ)+1 := by positivity
  have hx : Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1)) ≤ 2*((n:ℝ)+1) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · unfold linearCut
      push_cast
      nlinarith [sq_nonneg ((n:ℝ)+1)]
  have htwo := one_add_le_pow_two n
  have hpow : ((n:ℝ)+1)^2 ≤ (2:ℝ)^(4*n) := by
    calc
      _ ≤ ((2:ℝ)^n)^2 := pow_le_pow_left₀ hpos.le htwo _
      _ = (2:ℝ)^(n*2) := (pow_mul ..).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : Real.sqrt ((n:ℝ)+1) ≤ (n:ℝ)+1 :=
    (Real.sqrt_le_iff).mpr ⟨hpos.le,by nlinarith [Nat.cast_nonneg (α:=ℝ) n, sq_nonneg (n:ℝ)]⟩
  calc
    _ ≤ 4*((n:ℝ)+1)*(1/2:ℝ)^(2*linearCut n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ 1/((n:ℝ)+1) := by
      rw [show 2*linearCut n = 4*n+2 by unfold linearCut; omega, one_div,inv_pow,pow_add]
      apply (le_div_iff₀ hpos).mpr
      field_simp
      nlinarith
    _ ≤ 1/Real.sqrt ((n:ℝ)+1) := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) hle

end HardyTable
