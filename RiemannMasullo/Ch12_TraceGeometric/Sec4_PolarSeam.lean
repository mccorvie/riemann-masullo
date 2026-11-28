module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Split polar moment on the rational local Paley–Wiener level

The overlap of the removed real origin vector with its dilation yields the
smaller of the two half powers. This split functional is independent from
the two ordinary half-Mellin moments: a genuine compact smooth test can
annihilate both ordinary moments and have nonzero split moment. On the polar
filter, the split moment is exactly the negative value of the primitive at
logarithmic norm zero. This is the scalar part of the local comparison on
pp. 515–520, not a claim identifying the global trace with the local one.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Real Set
open scoped ContDiff

namespace RiemannMasullo.PolarTwoMoment

/-- The radial polar filter in logarithmic norm. -/
def polarFilter (g : ℝ → ℝ) (x : ℝ) : ℝ := deriv (deriv g) x - g x / 4

private def primitive (t : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  exp (t*x) * (deriv g x - t*g x)

private theorem primitive_contDiff (t : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (primitive t g) :=
  ((contDiff_const.mul contDiff_id).exp).mul (hg.deriv'.sub
    (contDiff_const.mul (hg.of_le (by norm_num))))

private theorem primitive_compact (t : ℝ) {g : ℝ → ℝ} (hk : HasCompactSupport g) :
    HasCompactSupport (primitive t g) := (hk.deriv.sub hk.mul_left).mul_left

private theorem primitive_deriv (t : ℝ) (ht : t^2 = 1/4) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (x : ℝ) :
    deriv (primitive t g) x = exp (t*x) * polarFilter g x := by
  have hd : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hg₁ := (hg.differentiable (by norm_num) x).hasDerivAt
  have hg₂ := (hd.differentiable one_ne_zero x).hasDerivAt
  have hx : HasDerivAt (fun x : ℝ ↦ t*x) t x := by
    simpa using (hasDerivAt_id x).const_mul t
  have h := (hx.exp).mul (hg₂.sub (hg₁.const_mul t))
  have he := h.deriv
  change deriv (primitive t g) x = _ at he
  rw [he]
  simp only [Pi.sub_apply]
  unfold polarFilter
  calc
    _ = exp (t*x) * (deriv (deriv g) x - (t^2)*g x) := by ring
    _ = _ := by rw [ht]; ring

/-- The split half-Mellin functional on the polar filter is the negative seam
value of its compact primitive. The two full half-Mellin moments have no such
boundary term. -/
theorem split_polarFilter_eq_neg_at_origin {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hk : HasCompactSupport g) :
    (∫ x, exp (-|x|/2) * polarFilter g x) = -g 0 := by
  have hp (t : ℝ) : ContDiff ℝ 1 (primitive t g) := primitive_contDiff t hg
  have hK (t : ℝ) : HasCompactSupport (primitive t g) := primitive_compact t hk
  have hm := HasCompactSupport.integral_Iic_deriv_eq (hp (1/2)) (hK (1/2)) 0
  have hplus := HasCompactSupport.integral_Ioi_deriv_eq (hp (-(1/2))) (hK (-(1/2))) 0
  have hderL := primitive_deriv (1/2) (by norm_num) hg
  have hderR := primitive_deriv (-(1/2)) (by norm_num) hg
  simp_rw [hderL] at hm
  simp_rw [hderR] at hplus
  have hi : Integrable fun x ↦ exp (-|x|/2) * polarFilter g x := by
    have hcont : Continuous (polarFilter g) :=
      (hg.deriv'.continuous_deriv_one).sub (hg.continuous.div_const 4)
    have hsupp : HasCompactSupport (polarFilter g) := hk.deriv.deriv.sub (hk.mul_right)
    have hc := (by fun_prop : Continuous (fun x : ℝ ↦ exp (-|x|/2))).mul hcont
    exact hc.integrable_of_hasCompactSupport hsupp.mul_left
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0:ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have hL : (∫ x in Iic (0:ℝ), exp (-|x|/2) * polarFilter g x) = primitive (1/2) g 0 := by
    rw [← hm]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    change exp (-|x|/2) * polarFilter g x = exp ((1/2)*x) * polarFilter g x
    rw [abs_of_nonpos (mem_Iic.mp hx), neg_neg, show x / 2 = (1/2:ℝ)*x by ring]
  have hR : (∫ x in Ioi (0:ℝ), exp (-|x|/2) * polarFilter g x) = -primitive (-(1/2)) g 0 := by
    rw [← hplus]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change exp (-|x|/2) * polarFilter g x = exp (-(1/2)*x) * polarFilter g x
    rw [abs_of_nonneg (mem_Ioi.mp hx).le, show -x/2 = -(1/2:ℝ)*x by ring]
  rw [hL,hR]
  simp only [primitive, mul_zero, exp_zero, one_mul]
  ring

private def bump : ContDiffBump (2 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

private def packet (s x : ℝ) : ℝ := bump (x+s)

private lemma smoothP (s : ℝ) : ContDiff ℝ ∞ (packet s) :=
  bump.contDiff.comp (contDiff_id.add contDiff_const)

private lemma compactP (s : ℝ) : HasCompactSupport (packet s) :=
  bump.hasCompactSupport.comp_homeomorph (Homeomorph.addRight s)

private lemma zeroP {s x : ℝ} (h : x+s ≤ 1 ∨ 3 ≤ x+s) : packet s x = 0 := by
  apply bump.zero_of_le_dist
  change (1 : ℝ) ≤ dist (x+s) 2
  rw [Real.dist_eq, le_abs]
  rcases h with h | h
  · right; linarith
  · left; linarith

private def weighted (t s x : ℝ) := exp (t*x) * packet s x

private lemma integrableW (t s : ℝ) : Integrable (weighted t s) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (smoothP s).continuous).integrable_of_hasCompactSupport (compactP s).mul_left

private lemma translateW (t s : ℝ) : (∫ x, weighted t s x) =
    exp (-(t*s)) * ∫ x, weighted t 0 x := by
  have h (x : ℝ) : weighted t s x = exp (-(t*s)) * weighted t 0 (x+s) := by
    simp only [weighted, packet, add_zero, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_add_right_eq_self]

private def coeff := exp 2 + exp (-2)

/-- Translated copies of the same bump have nonzero sets (-3,-1), (1,3), (5,7). -/
private def test (x : ℝ) := packet 4 x - coeff * packet 0 x + packet (-4) x

private lemma cancel (t : ℝ) (ht : t = 1/2 ∨ t = -(1/2)) :
    (∫ x, exp (t*x) * test x) = 0 := by
  have h (x : ℝ) : exp (t*x) * test x =
      weighted t 4 x - coeff * weighted t 0 x + weighted t (-4) x := by
    unfold weighted test; ring
  simp_rw [h]
  rw [integral_add (f := fun x => weighted t 4 x - coeff * weighted t 0 x)
        (g := weighted t (-4)) ((integrableW t 4).sub ((integrableW t 0).const_mul coeff))
        (integrableW t (-4)),
      integral_sub (f := weighted t 4) (g := fun x => coeff * weighted t 0 x)
        (integrableW t 4) ((integrableW t 0).const_mul coeff),
      integral_const_mul, translateW t 4, translateW t (-4)]
  rcases ht with rfl | rfl <;> norm_num [coeff] <;> ring

private def defect (x : ℝ) := (exp (-x/2) - exp (x/2)) * packet 4 x

private lemma defectPos : 0 < ∫ x, defect x := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := (-2 : ℝ))
  · unfold defect; exact (by fun_prop : Continuous (fun x : ℝ ↦ exp (-x/2) - exp (x/2))).mul
      (smoothP 4).continuous
  · exact (compactP 4).mul_left
  · intro x
    by_cases hx : x ≤ 0
    · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))) bump.nonneg
    · simp [defect, zeroP (s := 4) (x := x) (Or.inr (by linarith))]
  · have hb : 0 < packet 4 (-2) := by
      apply bump.pos_of_mem_ball
      norm_num [Metric.mem_ball, Real.dist_eq, bump]
    exact (mul_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))) hb).ne'

set_option maxHeartbeats 600000 in
/-- In logarithmic radius (so `d a/a = d x` and `a=1` corresponds to `x=0`),
a compact smooth test missing a neighborhood of the identity annihilates both
half Mellin moments but not the integral against the smaller half power. -/
theorem exists_test : ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ x, |x| ≤ 1 → f x = 0) ∧
    (∫ x, exp (x/2) * f x) = 0 ∧ (∫ x, exp (-x/2) * f x) = 0 ∧
    (∫ x, min (exp (x/2)) (exp (-x/2)) * f x) ≠ 0 := by
  have hp : (∫ x, exp (x/2) * test x) = 0 := by
    have he : (fun x : ℝ => exp (x/2) * test x) =
        (fun x : ℝ => exp ((1/2) * x) * test x) := by
      funext x
      rw [show x/2 = (1/2 : ℝ) * x by ring]
    rw [he]
    exact cancel _ (Or.inl rfl)
  have hm : (∫ x, exp (-x/2) * test x) = 0 := by
    have he : (fun x : ℝ => exp (-x/2) * test x) =
        (fun x : ℝ => exp ((-(1/2)) * x) * test x) := by
      funext x
      rw [show -x/2 = -(1/2 : ℝ) * x by ring]
    rw [he]
    exact cancel _ (Or.inr rfl)
  refine ⟨test, ((smoothP 4).sub (contDiff_const.mul (smoothP 0))).add (smoothP (-4)),
    ((compactP 4).sub (compactP 0).mul_left).add (compactP (-4)), ?_, hp, hm, ?_⟩
  · intro x hx
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    simp [test, zeroP (s := 4) (x := x) (Or.inr (by linarith)),
      zeroP (s := 0) (x := x) (Or.inl (by linarith)),
      zeroP (s := -4) (x := x) (Or.inl (by linarith))]
  · have h (x : ℝ) : min (exp (x/2)) (exp (-x/2)) * test x = exp (-x/2) * test x - defect x := by
      by_cases hx : x ≤ 0
      · rw [min_eq_left (Real.exp_le_exp.mpr (by linarith))]
        simp only [test, defect, zeroP (s := 0) (x := x) (Or.inl (by linarith)),
          zeroP (s := -4) (x := x) (Or.inl (by linarith))]; ring
      · rw [min_eq_right (Real.exp_le_exp.mpr (by linarith))]
        simp [defect, zeroP (s := 4) (x := x) (Or.inr (by linarith))]
    have hc : Continuous test := (((smoothP 4).continuous.sub
      (continuous_const.mul (smoothP 0).continuous)).add (smoothP (-4)).continuous)
    have hk : HasCompactSupport test := ((compactP 4).sub (compactP 0).mul_left).add (compactP (-4))
    have hd : Continuous defect := (by fun_prop : Continuous (fun x : ℝ ↦ exp (-x/2) - exp (x/2))).mul (smoothP 4).continuous
    simp_rw [h]
    rw [integral_sub (f := fun x => exp (-x/2) * test x) (g := defect)
      (((by fun_prop : Continuous (fun x : ℝ ↦ exp (-x/2))).mul hc).integrable_of_hasCompactSupport hk.mul_left)
      (hd.integrable_of_hasCompactSupport (compactP 4).mul_left), hm, zero_sub]
    exact neg_ne_zero.mpr defectPos.ne'

/-- In the log coordinate the smaller half power is the two-sided exponential
with a derivative jump at the identity. -/
theorem splitHalfWeight_eq_min (x : ℝ) :
    exp (-|x|/2) = min (exp (x/2)) (exp (-x/2)) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [abs_of_nonpos hx, neg_neg, min_eq_left (Real.exp_le_exp.mpr (by linarith))]
  · rw [abs_of_nonneg hx.le, min_eq_right (Real.exp_le_exp.mpr (by linarith))]

/-- Under the two full polar moment constraints, the split defect of a compact
polar primitive vanishes exactly when that primitive vanishes at the seam. -/
theorem split_polarFilter_eq_zero_iff {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hk : HasCompactSupport g) :
    (∫ x, min (exp (x/2)) (exp (-x/2)) * polarFilter g x) = 0 ↔ g 0 = 0 := by
  simp_rw [← splitHalfWeight_eq_min]
  rw [split_polarFilter_eq_neg_at_origin hg hk, neg_eq_zero]

end RiemannMasullo.PolarTwoMoment
