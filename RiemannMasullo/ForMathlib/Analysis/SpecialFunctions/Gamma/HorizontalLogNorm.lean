module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Horizontal secant bounds for the digamma function

Euler's product limit for Γ (DLMF 5.8.1) gives horizontal convexity of
`log ‖Γ(x+it)‖` when `|t| < x`. The recurrence (DLMF 5.5.1) evaluates
the two unit secants. This proof uses only Mathlib.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Topology BigOperators

namespace RiemannMasullo.HeckePoisson

/-- The point `x+it` on a horizontal line. -/
def gammaLine (t x : ℝ) : ℂ := (x : ℂ) + (t : ℂ) * I

private theorem gammaLine_add_ne_zero (t x : ℝ) (hx : 0 < x) (j : ℕ) :
    gammaLine t x + j ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp [gammaLine, Complex.add_re] at hh
  linarith [Nat.cast_nonneg (α := ℝ) j]

private theorem quadratic_log_convex (t : ℝ) (j : ℕ) :
    ConvexOn ℝ (Ioi |t|) (fun x : ℝ ↦ -Real.log ((x + j)^2 + t^2) / 2) := by
  let D (x : ℝ) := (x + j)^2 + t^2
  have hpos {x : ℝ} (hx : |t| < x) : 0 < D x := by
    have : 0 < x := (abs_nonneg _).trans_lt hx
    dsimp [D]
    positivity
  have hD (x : ℝ) : HasDerivAt D (2*(x + j)) x := by
    convert ((((hasDerivAt_id x).add_const (j : ℝ)).pow 2).add_const (t^2)) using 1 <;> simp [D]
  have hg (x : ℝ) (hx : |t| < x) :
      HasDerivAt (fun y ↦ -Real.log (D y) / 2) (-(x+j) / D x) x := by
    convert (((hD x).log (hpos hx).ne').neg.div_const 2) using 1
    ring
  have hg' (x : ℝ) (hx : |t| < x) :
      HasDerivAt (fun y : ℝ ↦ -(y+j) / D y) (((x+j)^2-t^2)/(D x)^2) x := by
    convert ((((hasDerivAt_id x).add_const (j : ℝ)).neg).div (hD x) (hpos hx).ne') using 1
    · rfl
    · change ((x+j)^2-t^2)/(D x)^2 = (-1 * D x - (-(x+j)) * (2*(x+j))) / (D x)^2
      dsimp [D]
      ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x ↦ -(x+j) / D x)
    (f'' := fun x ↦ ((x+j)^2-t^2)/(D x)^2) (convex_Ioi _)
    (fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hg x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx ↦ (hg' x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hx' : |t| < x := interior_subset hx
  have hle : |t| ≤ x+j := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hs := (sq_le_sq₀ (abs_nonneg t) ((abs_nonneg t).trans hle)).mpr hle
  exact div_nonneg (sub_nonneg.mpr (by simpa only [sq_abs] using hs)) (sq_nonneg _)

private theorem gammaSeq_log_ordinate (t x : ℝ) (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    Real.log ‖Complex.GammaSeq (gammaLine t x) n‖ =
      Real.log n * x + Real.log (n.factorial : ℝ) +
        ∑ j ∈ Finset.range (n+1), -Real.log ((x+j)^2+t^2) / 2 := by
  have hnorm (j : ℕ) : ‖gammaLine t x + j‖ ^ 2 = (x+j)^2+t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [gammaLine, Complex.add_re, Complex.add_im]
    ring
  have hlog (j : ℕ) : Real.log ‖gammaLine t x + j‖ = Real.log ((x+j)^2+t^2)/2 := by
    rw [← hnorm, Real.log_pow]
    ring
  have hp : (∏ j ∈ Finset.range (n+1), ‖gammaLine t x + j‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ ↦ norm_ne_zero_iff.mpr (gammaLine_add_ne_zero t x hx j))
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod, Complex.norm_natCast_cpow_of_pos hn,
    Complex.norm_natCast, Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hn' _).ne' (by positivity)) hp,
    Real.log_mul (Real.rpow_pos_of_pos hn' _).ne' (by positivity), Real.log_rpow hn',
    Real.log_prod (fun j _ ↦ norm_ne_zero_iff.mpr (gammaLine_add_ne_zero t x hx j)),
    show (gammaLine t x).re = x by simp [gammaLine]]
  simp_rw [hlog]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [neg_div]
  ring

/-- At a fixed height inside the cone `|t| < x`, Euler's finite products
yield horizontal convexity of the log-modulus of the gamma function. -/
theorem gammaLine_log_norm_convex (t : ℝ) :
    ConvexOn ℝ (Ioi |t|) (fun x : ℝ ↦ Real.log ‖Complex.Gamma (gammaLine t x)‖) := by
  let S := Ioi |t|
  have hsum (m : ℕ) : ConvexOn ℝ S
      (fun x : ℝ ↦ ∑ j ∈ Finset.range m, -Real.log ((x+j)^2+t^2)/2) := by
    induction m with
    | zero => simpa using convexOn_const (0 : ℝ) (convex_Ioi |t|)
    | succ m ih =>
      simpa only [Finset.sum_range_succ, Pi.add_def] using ih.add (quadratic_log_convex t m)
  have hfinite {n : ℕ} (hn : 0 < n) :
      ConvexOn ℝ S (fun x : ℝ ↦ Real.log ‖Complex.GammaSeq (gammaLine t x) n‖) := by
    have hmul : ConvexOn ℝ S (fun x : ℝ ↦ Real.log n * x) := by
      refine ⟨convex_Ioi _, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      exact le_of_eq (by ring)
    refine ((hmul.add_const (Real.log (n.factorial : ℝ))).add (hsum (n+1))).congr ?_
    exact fun x hx ↦ (gammaSeq_log_ordinate t x ((abs_nonneg t).trans_lt hx) hn).symm
  have hlim (x : ℝ) (hx : x ∈ S) :
      Tendsto (fun n : ℕ ↦ Real.log ‖Complex.GammaSeq (gammaLine t x) n‖) atTop
        (𝓝 (Real.log ‖Complex.Gamma (gammaLine t x)‖)) := by
    have hre : 0 < (gammaLine t x).re := by simpa [gammaLine] using (abs_nonneg t).trans_lt hx
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hre))).tendsto.comp
      (Complex.GammaSeq_tendsto_Gamma (gammaLine t x)).norm
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hm := (convex_Ioi |t| (𝕜 := ℝ)) hx hy ha hb hab
  refine le_of_tendsto_of_tendsto (hlim _ hm)
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hfinite hn).2 hx hy ha hb hab

private theorem horizontal_gamma_real_deriv (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ Real.log ‖Complex.Gamma (gammaLine t y)‖)
      (Complex.digamma (gammaLine t x)).re x := by
  let G (z : ℂ) := Complex.Gamma (z + (t : ℂ)*I)
  let A := G x
  have hp : 0 < (gammaLine t x).re := by simpa [gammaLine] using hx
  have hA : A ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hp
  have hG : HasDerivAt G (deriv Complex.Gamma (gammaLine t x)) (x : ℂ) := by
    exact HasDerivAt.comp_add_const (x : ℂ) ((t : ℂ)*I)
      (Complex.hasDerivAt_Gamma_of_re_pos hp).differentiableAt.hasDerivAt
  have hslit : G x / A ∈ Complex.slitPlane := by
    change A / A ∈ Complex.slitPlane
    simp [hA]
  have hd := (((hG.div_const A).clog hslit).real_of_complex).add_const (Real.log ‖A‖)
  have hd' : HasDerivAt (fun y : ℝ ↦ (Complex.log (G y / A)).re + Real.log ‖A‖)
      (Complex.digamma (gammaLine t x)).re x := by
    simpa only [show G x / A = 1 from div_self hA, div_one, Complex.digamma_def, logDeriv_apply, G, A,
      gammaLine] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  have hy' : 0 < (gammaLine t y).re := by simpa [gammaLine] using hy
  have hn : G y ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hy'
  rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hn)
    (norm_ne_zero_iff.mpr hA)]
  change Real.log ‖G y‖ = Real.log ‖G y‖ - Real.log ‖A‖ + Real.log ‖A‖
  ring

private theorem log_norm_gamma_increment (t x : ℝ) (hx : 0 < x) :
    Real.log ‖Complex.Gamma (gammaLine t (x+1))‖ =
      Real.log ‖gammaLine t x‖ + Real.log ‖Complex.Gamma (gammaLine t x)‖ := by
  have hp : 0 < (gammaLine t x).re := by simpa [gammaLine] using hx
  have hn : gammaLine t x ≠ 0 := by
    intro he
    rw [he] at hp
    simp at hp
  have heq : gammaLine t (x+1) = gammaLine t x + 1 := by simp [gammaLine]; ring
  rw [heq, Complex.Gamma_add_one _ hn, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hn)
    (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hp))]

/-- The two adjacent horizontal secants bound the real part of the digamma
function wherever `x - 1` lies strictly inside the cone of log-convexity. -/
theorem gammaLine_digamma_secants (t x : ℝ) (hx : |t| + 1 < x) :
    Real.log ‖gammaLine t (x-1)‖ ≤ (Complex.digamma (gammaLine t x)).re ∧
      (Complex.digamma (gammaLine t x)).re ≤ Real.log ‖gammaLine t x‖ := by
  have hm : |t| < x-1 := by linarith
  have hp : |t| < x := by linarith
  have hd := horizontal_gamma_real_deriv t x ((abs_nonneg t).trans_lt hp)
  have hconv := gammaLine_log_norm_convex t
  have hlo := hconv.slope_le_of_hasDerivAt (x := x-1) (y := x) hm hp (by linarith) hd
  have hup := hconv.le_slope_of_hasDerivAt (x := x) (y := x+1) hp
    (show |t| < x+1 by linarith) (by linarith) hd
  have hshift := log_norm_gamma_increment t (x-1) ((abs_nonneg t).trans_lt hm)
  rw [sub_add_cancel] at hshift
  rw [slope_def_field, show x-(x-1) = 1 by ring, div_one] at hlo
  rw [slope_def_field, show x+1-x = 1 by ring, div_one] at hup
  have hnext := log_norm_gamma_increment t x ((abs_nonneg t).trans_lt hp)
  exact ⟨by linarith, by linarith⟩

end RiemannMasullo.HeckePoisson
