module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyLeastSquares
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A finite rational grid for a Hardy least-squares residual

At degree `n`, round each real and imaginary part toward zero on a mesh of spacing
`(n + 1)⁻³`. This preserves the weighted coefficient constraint. The finite minimum
of visible norms exceeds the true constrained minimum in norm by at most
`4 * A / (n + 1)` if all visible entries have modulus at most `A`.
-/

@[expose] public noncomputable section

open Finset Filter Set
open scoped BigOperators Topology

namespace HardyTable

/-- Common denominator for the real and imaginary polynomial coefficients. -/
def gridDen (n : ℕ) : ℕ := (n + 1) ^ 3

private theorem den_pos (n : ℕ) : 0 < gridDen n := by unfold gridDen; positivity

/-- A sign and a bounded numerator magnitude. -/
abbrev GridDigit (n : ℕ) := Bool × Fin ((n + 1) * gridDen n + 1)

/-- The two signed numerators for each polynomial coefficient. -/
abbrev GridIndex (n : ℕ) := Fin (n + 1) → GridDigit n × GridDigit n

/-- Signed real coordinate of a rational grid point. -/
def gridCoord {n : ℕ} (v : GridDigit n) : ℝ :=
  (if v.1 then -(v.2.val : ℝ) else (v.2.val : ℝ)) / gridDen n

/-- Polynomial with the indicated signed Gaussian rational coefficients. -/
def rawGrid {n : ℕ} (v : GridIndex n) : Coeff n :=
  WithLp.toLp 2 fun j ↦ ⟨gridCoord (v j).1, gridCoord (v j).2⟩

/-- Integer numerator of the weighted squared norm of a grid polynomial. -/
def gridCost {n : ℕ} (v : GridIndex n) : ℕ :=
  ∑ j, (j.val + 1) ^ 2 * ((v j).1.2.val ^ 2 + (v j).2.2.val ^ 2)

/-- Reject an out-of-budget integer row by replacing it with the zero polynomial. -/
def gridPoint {n : ℕ} (v : GridIndex n) : Coeff n :=
  if gridCost v ≤ (n + 1) * (gridDen n) ^ 2 then rawGrid v else 0

private theorem coord_sq {n : ℕ} (v : GridDigit n) :
    (gridCoord v)^2 = (v.2.val : ℝ)^2 / (gridDen n : ℝ)^2 := by
  rcases v with ⟨b, k⟩
  cases b <;> simp [gridCoord, div_pow]

private theorem raw_cost {n : ℕ} (v : GridIndex n) :
    weightedEnergy (rawGrid v) = (gridCost v : ℝ) / (gridDen n : ℝ)^2 := by
  unfold weightedEnergy gridCost
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hn : ‖rawGrid v j‖^2 = gridCoord (v j).1 ^ 2 + gridCoord (v j).2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [sq, sq]
    rfl
  rw [mul_pow, hn, coord_sq, coord_sq]
  ring

private theorem cost_iff {n : ℕ} (v : GridIndex n) :
    gridCost v ≤ (n + 1) * (gridDen n)^2 ↔ rawGrid v ∈ ellipsoid n := by
  change _ ↔ weightedEnergy (rawGrid v) ≤ _
  rw [raw_cost, div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr (den_pos n)))]
  exact_mod_cast Iff.rfl

theorem gridPoint_mem {n : ℕ} (v : GridIndex n) : gridPoint v ∈ ellipsoid n := by
  unfold gridPoint
  split_ifs with h
  · exact (cost_iff v).mp h
  · simp [ellipsoid, weightedEnergy]
    positivity

private def digit (n : ℕ) (x : ℝ) (hx : |x| ≤ (n : ℝ) + 1) : GridDigit n :=
  (decide (x < 0), ⟨⌊|x| * gridDen n⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    push_cast
    exact mul_le_mul_of_nonneg_right hx (by positivity)))⟩)

private theorem digit_bounds (n : ℕ) (x : ℝ) (hx : |x| ≤ (n : ℝ) + 1) :
    |gridCoord (digit n x hx)| ≤ |x| ∧
      |gridCoord (digit n x hx) - x| ≤ 1 / (gridDen n : ℝ) := by
  let a : ℝ := (⌊|x| * gridDen n⌋₊ : ℕ)
  let d : ℝ := gridDen n
  have hd : 0 < d := Nat.cast_pos.mpr (den_pos n)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hlow : a / d ≤ |x| := (div_le_iff₀ hd).mpr (Nat.floor_le (by positivity))
  have hu : |x| - a / d ≤ 1 / d := by
    have hh : |x| * d < a + 1 := Nat.lt_floor_add_one _
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hd]
    linarith
  by_cases hneg : x < 0
  · have he : gridCoord (digit n x hx) = -(a / d) := by simp [gridCoord, digit, hneg, a, d, neg_div]
    rw [he, abs_neg, abs_of_nonneg (div_nonneg ha hd.le)]
    rw [abs_of_neg hneg] at hlow hu
    refine ⟨by rwa [abs_of_neg hneg], ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have he : gridCoord (digit n x hx) = a / d := by simp [gridCoord, digit, hneg, a, d]
    rw [he, abs_of_nonneg (div_nonneg ha hd.le)]
    refine ⟨hlow, ?_⟩
    rw [abs_of_nonneg (le_of_not_gt hneg)] at hlow hu
    rw [abs_of_nonpos (by linarith)]
    linarith

private theorem index_approx {n : ℕ} (p : Coeff n) (hp : p ∈ ellipsoid n) :
    ∃ v : GridIndex n, ∀ j, ‖gridPoint v j - p j‖ ≤ 2 / (gridDen n : ℝ) := by
  have hnorm (j : Fin (n + 1)) : ‖p j‖ ≤ (n : ℝ) + 1 := by
    have hs : (((j.val : ℝ) + 1) * ‖p j‖)^2 ≤ weightedEnergy p :=
      Finset.single_le_sum (fun i _ ↦ sq_nonneg (((i.val : ℝ) + 1) * ‖p i‖)) (mem_univ j)
    have h0 : ‖p j‖ ≤ ((j.val : ℝ) + 1) * ‖p j‖ := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j.val) (norm_nonneg (p j))]
    have hle : weightedEnergy p ≤ (n:ℝ) + 1 := hp
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h0 2, Nat.cast_nonneg (α := ℝ) n,
      norm_nonneg (p j), sq_nonneg (‖p j‖-1)]
  have hr j := (Complex.abs_re_le_norm (p j)).trans (hnorm j)
  have hi j := (Complex.abs_im_le_norm (p j)).trans (hnorm j)
  let v : GridIndex n := fun j ↦ (digit n (p j).re (hr j), digit n (p j).im (hi j))
  have hsm (j : Fin (n + 1)) : ‖rawGrid v j‖^2 ≤ ‖p j‖^2 := by
    obtain ⟨hr', _⟩ := digit_bounds n (p j).re (hr j)
    obtain ⟨hi', _⟩ := digit_bounds n (p j).im (hi j)
    have h := add_le_add (pow_le_pow_left₀ (abs_nonneg _) hr' 2)
      (pow_le_pow_left₀ (abs_nonneg _) hi' 2)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, ← sq, ← sq, ← sq, ← sq]
    change gridCoord (digit n (p j).re (hr j)) ^ 2 + gridCoord (digit n (p j).im (hi j)) ^ 2 ≤ _
    simpa only [sq_abs] using h
  have hv : rawGrid v ∈ ellipsoid n := by
    apply le_trans _ (show weightedEnergy p ≤ (n:ℝ) + 1 from hp)
    unfold weightedEnergy
    apply Finset.sum_le_sum
    intro j _
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left (hsm j) (sq_nonneg _)
  refine ⟨v, fun j ↦ ?_⟩
  rw [gridPoint, ite_eq_left ((cost_iff v).mpr hv)]
  have ht := add_le_add (digit_bounds n (p j).re (hr j)).2 (digit_bounds n (p j).im (hi j)).2
  calc
    _ ≤ |(rawGrid v j - p j).re| + |(rawGrid v j - p j).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / (gridDen n : ℝ) + 1 / (gridDen n : ℝ) := ht
    _ = _ := by ring

/-- The smallest visible norm on an explicitly finite rational polynomial grid. -/
def gridNorm (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  (Finset.univ : Finset (GridIndex n)).inf' Finset.univ_nonempty
    (fun v ↦ ‖visible (linearCut n) a (gridPoint v)‖)

private theorem perturb_trial {n M : ℕ} {p q : Coeff n} {a : ℕ → ℂ} {A ε : ℝ}
    (hA : 0 ≤ A) (ha : ∀ j ≤ M, ‖a j‖ ≤ A) (hε : 0 ≤ ε) (hp : ∀ k, ‖p k - q k‖ ≤ ε) :
    ‖visible M a p - visible M a q‖ ≤ ((M : ℝ) + 1) * (((n : ℝ) + 1) * ε * A) := by
  let R := ((n : ℝ) + 1) * ε * A
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have he (j : Fin (M + 1)) : ‖(visible M a p - visible M a q) j‖ ≤ R := by
    change ‖((_ : ℂ) - _) - (_ - _)‖ ≤ _
    simp only [sub_sub_sub_cancel_left]
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k : Fin (n + 1), ε * A := Finset.sum_le_sum fun k _ ↦ by
        rw [← sub_mul, norm_mul, norm_sub_rev]
        apply mul_le_mul (hp k) _ (norm_nonneg _) hε
        split_ifs
        · exact ha _ (by have := j.isLt; omega)
        · simpa using hA
      _ = _ := by simp [R, mul_assoc]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hR)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow]
  calc
    _ ≤ ∑ _j : Fin (M + 1), R^2 :=
      Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (he j) 2
    _ = ((M : ℝ) + 1) * R^2 := by simp
    _ ≤ _ := by gcongr; nlinarith [Nat.cast_nonneg (α := ℝ) M, sq_nonneg (M : ℝ)]

/-- Restricting the admissible polynomials to the integer grid gives an upper bound. -/
theorem sqrt_le_gridNorm (n : ℕ) (a : ℕ → ℂ) :
    Real.sqrt (leastSquares (linearCut n) a (ellipsoid n)) ≤ gridNorm n a := by
  obtain ⟨p, _, hm, hmin⟩ := exists_leastSquares (M := linearCut n) a
    (ellipsoid_compact n) (ellipsoid_nonempty n)
  rw [hm, Real.sqrt_sq (norm_nonneg _)]
  exact Finset.le_inf' _ _ (fun v _ ↦ hmin (gridPoint v) (gridPoint_mem v))

/-- The finite grid gives an upper approximation even for a singular Toeplitz matrix. -/
theorem gridNorm_bounds (n : ℕ) (a : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ j ≤ linearCut n, ‖a j‖ ≤ A) :
    Real.sqrt (leastSquares (linearCut n) a (ellipsoid n)) ≤ gridNorm n a ∧
      gridNorm n a ≤ Real.sqrt (leastSquares (linearCut n) a (ellipsoid n)) + 4*A/((n:ℝ)+1) := by
  obtain ⟨p, hp, hm, _⟩ := exists_leastSquares (M := linearCut n) a
    (ellipsoid_compact n) (ellipsoid_nonempty n)
  refine ⟨sqrt_le_gridNorm n a, ?_⟩
  rw [hm, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨v, hv⟩ := index_approx p hp
  apply (Finset.inf'_le _ (Finset.mem_univ v) : gridNorm n a ≤ _).trans
  have hdiff := perturb_trial (M := linearCut n) hA ha (show 0 ≤ 2/(gridDen n : ℝ) by positivity) hv
  have hnorm := (abs_le.mp ((abs_norm_sub_norm_le _ _).trans hdiff)).2
  have hscale : ((linearCut n:ℝ)+1)*(((n:ℝ)+1)*(2/(gridDen n:ℝ))*A) = 4*A/((n:ℝ)+1) := by
    unfold gridDen linearCut
    push_cast
    field_simp
    ring
  linarith

end HardyTable
