module

public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace RiemannMasullo

/-- The boundary integral following the bottom and right edges from `z` to `w`,
then the top and left edges from `w` back to `z`. -/
def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f

/-- The four oriented edge integrals, with real parameters increasing from the
coordinates of `z` to the coordinates of `w`. -/
theorem rectangleIntegral_eq (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) := by
  exact Complex.wedgeIntegral_add_wedgeIntegral_eq z w f

private theorem horizontal_mapsTo_boundary {z w : ℂ} {y : ℝ} (hw : z.re ≤ w.re)
    (hy : y = z.im ∨ y = w.im) (ht : z.im ≤ w.im) :
    MapsTo (fun x : ℝ ↦ (x : ℂ) + y * Complex.I) (uIcc z.re w.re)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  intro x hx
  rw [uIcc_of_le hw] at hx
  rcases hy with rfl | rfl <;> simp [Complex.mem_reProdIm, hx, ht]

private theorem vertical_mapsTo_boundary {z w : ℂ} {x : ℝ} (ht : z.im ≤ w.im)
    (hx : x = z.re ∨ x = w.re) (hw : z.re ≤ w.re) :
    MapsTo (fun y : ℝ ↦ (x : ℂ) + y * Complex.I) (uIcc z.im w.im)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  intro y hy
  rw [uIcc_of_le ht] at hy
  rcases hx with rfl | rfl <;> simp [Complex.mem_reProdIm, hy, hw]

private theorem intervalIntegrable_comp_boundary {z w : ℂ} {a b : ℝ} {p : ℝ → ℂ}
    {f : ℂ → ℂ} (hp : Continuous p)
    (hm : MapsTo p (uIcc a b)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)))
    (hf : ContinuousOn f
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    IntervalIntegrable (fun x ↦ f (p x)) volume a b :=
  (hf.comp hp.continuousOn hm).intervalIntegrable

/-- A rectangle integral is unchanged by modifying the integrand at countably
many boundary points. -/
theorem rectangleIntegral_congr_off_countable {f g : ℂ → ℂ} {z w : ℂ} {E : Set ℂ}
    (hw : z.re ≤ w.re) (ht : z.im ≤ w.im) (hE : E.Countable)
    (he : EqOn f g
      (((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) \ E)) :
    rectangleIntegral f z w = rectangleIntegral g z w := by
  have hEdge {a b : ℝ} {p : ℝ → ℂ} (hp : Function.Injective p)
      (hm : MapsTo p (uIcc a b)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
      (∫ x in a..b, f (p x)) = ∫ x in a..b, g (p x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(hE.preimage hp).ae_notMem volume] with x hx hxab
    exact he ⟨hm (uIoc_subset_uIcc hxab), hx⟩
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :=
    hEdge (fun a b hab ↦ by simpa using congrArg Complex.re hab)
      (horizontal_mapsTo_boundary hw hy ht)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :=
    hEdge (fun a b hab ↦ by simpa using congrArg Complex.im hab)
      (vertical_mapsTo_boundary ht hx hw)
  simp only [rectangleIntegral_eq, hH _ (Or.inl rfl), hH _ (Or.inr rfl),
    hV _ (Or.inl rfl), hV _ (Or.inr rfl)]

/-- The rectangle integral is additive on functions continuous on the boundary. -/
theorem rectangleIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hw : z.re ≤ w.re) (ht : z.im ≤ w.im)
    (hf : ContinuousOn f
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)))
    (hg : ContinuousOn g
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectangleIntegral (fun s ↦ f s + g s) z w =
      rectangleIntegral f z w + rectangleIntegral g z w := by
  have hEdge {a b : ℝ} {p : ℝ → ℂ} (hp : Continuous p)
      (hm : MapsTo p (uIcc a b)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :=
    intervalIntegral.integral_add (intervalIntegrable_comp_boundary hp hm hf)
      (intervalIntegrable_comp_boundary hp hm hg)
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :=
    hEdge (by fun_prop) (horizontal_mapsTo_boundary hw hy ht)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :=
    hEdge (by fun_prop) (vertical_mapsTo_boundary ht hx hw)
  simp only [rectangleIntegral_eq, hH _ (Or.inl rfl), hH _ (Or.inr rfl),
    hV _ (Or.inl rfl), hV _ (Or.inr rfl), mul_add]
  abel

/-- The integral of a finite sum of functions continuous on the rectangle
boundary is the sum of their boundary integrals. -/
theorem rectangleIntegral_finsetSum {ι : Type*} {F : ι → ℂ → ℂ} {s : Finset ι} {z w : ℂ}
    (hw : z.re ≤ w.re) (ht : z.im ≤ w.im)
    (hF : ∀ i ∈ s, ContinuousOn (F i)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :
    rectangleIntegral (fun x ↦ ∑ i ∈ s, F i x) z w =
      ∑ i ∈ s, rectangleIntegral (F i) z w := by
  have hEdge {a b : ℝ} {p : ℝ → ℂ} (hp : Continuous p)
      (hm : MapsTo p (uIcc a b)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im))) :=
    intervalIntegral.integral_finsetSum
      (fun i hi ↦ intervalIntegrable_comp_boundary hp hm (hF i hi))
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :=
    hEdge (by fun_prop) (horizontal_mapsTo_boundary hw hy ht)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :=
    hEdge (by fun_prop) (vertical_mapsTo_boundary ht hx hw)
  simp only [rectangleIntegral_eq, hH _ (Or.inl rfl), hH _ (Or.inr rfl),
    hV _ (Or.inl rfl), hV _ (Or.inr rfl), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]

/-- A constant factor can be taken outside the rectangle integral. -/
theorem rectangleIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral (fun x ↦ c * f x) z w = c * rectangleIntegral f z w := by
  simp only [rectangleIntegral_eq, intervalIntegral.integral_const_mul]
  ring

/- The logarithm argument for the simple kernel is adapted from
   DedekindResidue.ExplicitFormula.RectangleContour in AINTLIB.
   Copyright (c) 2026 Chris Birkbeck. Released under Apache 2.0. -/

private theorem integral_log_deriv {p : ℝ → ℂ} {a b : ℝ} {v : ℂ}
    (hp : ∀ x ∈ uIcc a b, HasDerivAt p v x)
    (hslit : ∀ x ∈ uIcc a b, p x ∈ Complex.slitPlane) :
    (∫ x in a..b, v * (p x)⁻¹) = Complex.log (p b) - Complex.log (p a) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    simpa only [div_eq_mul_inv] using (hp x hx).clog_real (hslit x hx)
  · have hc : ContinuousOn p (uIcc a b) := fun x hx ↦
      (hp x hx).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul
      (hc.inv₀ fun x hx ↦ Complex.slitPlane_ne_zero (hslit x hx))).intervalIntegrable

private theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast
  ring

private theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + Real.pi * Complex.I := by
  have h := log_neg_of_im_pos (u := -u) (by simpa using neg_pos.mpr hu)
  rw [neg_neg] at h
  linear_combination -h

private theorem hasDerivAt_horizontal (x y : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * Complex.I - ρ) 1 x := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const
    ((y : ℂ) * Complex.I)).sub_const ρ

private theorem hasDerivAt_vertical (x y : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * Complex.I - ρ) Complex.I y := by
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const
    Complex.I).const_add (x : ℂ)).sub_const ρ

/-- The boundary integral of the simple Cauchy kernel is `2πi` when the
pole is strictly inside the rectangle. -/
theorem rectangleIntegral_sub_inv {z w ρ : ℂ}
    (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun s ↦ (s - ρ)⁻¹) z w = 2 * (Real.pi : ℂ) * Complex.I := by
  let p (x y : ℝ) := (x : ℂ) + y * Complex.I - ρ
  have hB := integral_log_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x z.im) (fun x _ ↦ hasDerivAt_horizontal x z.im ρ)
    (fun x _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inr (by simpa [p] using (sub_neg.mpr hρ.2.1).ne)))
  have hT := integral_log_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x w.im) (fun x _ ↦ hasDerivAt_horizontal x w.im ρ)
    (fun x _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inr (by simpa [p] using (sub_pos.mpr hρ.2.2).ne')))
  have hR := integral_log_deriv (a := z.im) (b := w.im)
    (p := p w.re) (fun y _ ↦ hasDerivAt_vertical w.re y ρ)
    (fun y _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa [p] using sub_pos.mpr hρ.1.2)))
  have hL := integral_log_deriv (a := z.im) (b := w.im)
    (p := fun y ↦ -p z.re y) (fun y _ ↦ (hasDerivAt_vertical z.re y ρ).neg)
    (fun y _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa [p] using neg_pos.mpr (sub_neg.mpr hρ.1.1))))
  have hBL : (p z.re z.im).im < 0 := by simpa [p] using sub_neg.mpr hρ.2.1
  have hTL : 0 < (p z.re w.im).im := by simpa [p] using sub_pos.mpr hρ.2.2
  simp only [one_mul] at hB hT
  simp only [inv_neg, neg_mul_neg] at hL
  rw [intervalIntegral.integral_const_mul] at hL hR
  rw [rectangleIntegral_eq]
  change (∫ x in z.re..w.re, (p x z.im)⁻¹) - (∫ x in z.re..w.re, (p x w.im)⁻¹) +
    Complex.I * (∫ y in z.im..w.im, (p w.re y)⁻¹) -
    Complex.I * (∫ y in z.im..w.im, (p z.re y)⁻¹) = _
  rw [hB, hT, hR, hL, log_neg_of_im_pos hTL, log_neg_of_im_neg hBL]
  ring

private theorem integral_zpow_deriv {p : ℝ → ℂ} {a b : ℝ} {v : ℂ} {n : ℤ}
    (hp : ∀ x ∈ uIcc a b, HasDerivAt p v x)
    (hne : ∀ x ∈ uIcc a b, p x ≠ 0) (hn : n ≠ -1) :
    (∫ x in a..b, v * (p x) ^ n) = (p b ^ (n + 1) - p a ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  have hcast : (↑(n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  rw [sub_div]
  refine integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ ↦ p t ^ (n + 1) / (↑(n + 1) : ℂ)) ?_ ?_
  · intro x hx
    have hd := (((hasDerivAt_zpow (n + 1) (p x) (Or.inl (hne x hx))).comp x
      (hp x hx)).div_const (↑(n + 1) : ℂ))
    have he : v * p x ^ n = ↑(n + 1) * p x ^ (n + 1 - 1) * v / (↑(n + 1) : ℂ) := by
      rw [add_sub_cancel_right]
      field_simp
    exact he ▸ hd
  · have hc : ContinuousOn p (uIcc a b) := fun x hx ↦
      (hp x hx).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul (hc.zpow₀ n fun x hx ↦ Or.inl (hne x hx))).intervalIntegrable

/-- All integer powers of the Cauchy kernel other than exponent `-1` have a
primitive off the pole and integrate to zero on the rectangle boundary. -/
theorem rectangleIntegral_sub_zpow_of_ne {z w ρ : ℂ} {n : ℤ}
    (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) (hn : n ≠ -1) :
    rectangleIntegral (fun s ↦ (s - ρ) ^ n) z w = 0 := by
  let p (x y : ℝ) := (x : ℂ) + y * Complex.I - ρ
  have hH (y : ℝ) (hy : y ≠ ρ.im) := integral_zpow_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x y) (fun x _ ↦ hasDerivAt_horizontal x y ρ)
    (fun x _ he ↦ hy (sub_eq_zero.mp (by simpa [p] using congrArg Complex.im he))) hn
  have hV (x : ℝ) (hx : x ≠ ρ.re) := integral_zpow_deriv (a := z.im) (b := w.im)
    (p := p x) (fun y _ ↦ hasDerivAt_vertical x y ρ)
    (fun y _ he ↦ hx (sub_eq_zero.mp (by simpa [p] using congrArg Complex.re he))) hn
  simp only [one_mul] at hH
  simp only [intervalIntegral.integral_const_mul] at hV
  rw [rectangleIntegral_eq]
  change (∫ x in z.re..w.re, (p x z.im) ^ n) - (∫ x in z.re..w.re, (p x w.im) ^ n) +
    Complex.I * (∫ y in z.im..w.im, (p w.re y) ^ n) -
    Complex.I * (∫ y in z.im..w.im, (p z.re y) ^ n) = _
  rw [hH z.im hρ.2.1.ne, hH w.im hρ.2.2.ne', hV w.re hρ.1.2.ne', hV z.re hρ.1.1.ne]
  ring

end RiemannMasullo
