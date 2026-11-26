module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.ForMathlib.Analysis.Complex.RectangleIntegral
import Mathlib.Tactic

/-! # The two-point resolvent on expanding rectangles

A meromorphic logarithmic derivative determines its own two-point difference
from its signed divisor whenever regular rectangles have sublinear boundary
growth and the divisor samples converge absolutely. The upper and lower
ordinates may be chosen independently in unit intervals.
-/

public noncomputable section
open Set Filter MeasureTheory Complex Topology
namespace RiemannMasullo.ResolventRectangle

/-- The two Cauchy terms in a form that separates either simple pole. -/
def kernel (z b u : ℂ) : ℂ := (z-b) / ((u-z)*(u-b))

theorem kernel_eq_sub {z b u : ℂ} (hz : u ≠ z) (hb : u ≠ b) :
    kernel z b u = 1/(u-z) - 1/(u-b) := by
  unfold kernel
  field_simp [sub_ne_zero.mpr hz, sub_ne_zero.mpr hb]
  ring

private theorem kernel_analytic {z b u : ℂ} (hz : u ≠ z) (hb : u ≠ b) :
    AnalyticAt ℂ (kernel z b) u :=
  analyticAt_const.div ((analyticAt_id.sub analyticAt_const).mul
    (analyticAt_id.sub analyticAt_const)) (mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hb))

private theorem near_left_residue {f : ℂ → ℂ} {z b : ℂ} (hne : z ≠ b) (hf : AnalyticAt ℂ f z) :
    complexResidue (fun u ↦ kernel z b u * f u) z = f z := by
  let G (u : ℂ) := ((z-b)*f u)/(u-b)
  have hG : AnalyticAt ℂ G z := (analyticAt_const.mul hf).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne)
  have he : (fun u ↦ kernel z b u * f u) = fun u ↦ G u/(u-z) := by
    funext u
    simp only [kernel, G, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, complexResidue_div_sub hG]
  dsimp [G]
  field_simp [sub_ne_zero.mpr hne]

private theorem near_right_residue {f : ℂ → ℂ} {z b : ℂ} (hne : z ≠ b) (hf : AnalyticAt ℂ f b) :
    complexResidue (fun u ↦ kernel z b u * f u) b = -f b := by
  let G (u : ℂ) := ((z-b)*f u)/(u-z)
  have hG : AnalyticAt ℂ G b := (analyticAt_const.mul hf).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne.symm)
  have he : (fun u ↦ kernel z b u * f u) = fun u ↦ G u/(u-b) := by
    funext u
    simp only [kernel, G, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, complexResidue_div_sub hG]
  dsimp [G]
  field_simp [sub_ne_zero.mpr hne.symm]
  ring

/-- An unsubtracted rectangle records both evaluation residues and the signed divisor.
The horizontal and vertical coordinates may vary independently. -/
theorem rectangle_resolvent_logDeriv
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ) (hfinite : ∀ u, meromorphicOrderAt L u ≠ ⊤)
    (z b : ℂ) (hzb : z ≠ b) (hz : AnalyticAt ℂ (logDeriv L) z) (hb : AnalyticAt ℂ (logDeriv L) b)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) (hy : y₁ < y₂)
    (hzR : z ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) (hbR : b ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)
    (S : Finset ℂ) (hzS : z ∉ S) (hbS : b ∉ S)
    (hsIn : ∀ ρ ∈ S, ρ ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)
    (hsOut : ∀ u ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂, u ∉ S → meromorphicOrderAt L u = 0) :
    rectangleIntegral (fun u ↦ kernel z b u * logDeriv L u) ⟨x₁,y₁⟩ ⟨x₂,y₂⟩ =
      (2 * (Real.pi : ℂ) * I) * (logDeriv L z - logDeriv L b -
        ∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * (1/(z-ρ) - 1/(b-ρ))) := by
  classical
  let f (u : ℂ) := kernel z b u * logDeriv L u
  have hmer u : MeromorphicAt (kernel z b) u :=
    (MeromorphicAt.const _ _).div (((analyticAt_id.sub analyticAt_const).meromorphicAt).mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt))
  have heq := rectangleIntegral_eq_sum_complexResidue (g := f) hx hy
    (insert z (insert b S)) (fun u _ ↦ (hmer u).mul (hL.logDeriv u (mem_univ u)))
    (by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hzR (And.intro hbR hsIn)) (by
      intro u hu hn
      simp only [Finset.mem_insert, not_or] at hn
      have h0 := meromorphicOrderAt_logDeriv_nonneg (hL u (mem_univ u)) (hsOut u hu hn.2.2)
      change 0 ≤ meromorphicOrderAt (kernel z b * logDeriv L) u
      rw [meromorphicOrderAt_mul (hmer u) (hL.logDeriv u (mem_univ u))]
      exact add_nonneg (kernel_analytic hn.1 hn.2.1).meromorphicOrderAt_nonneg h0)
  rw [rectangleIntegral_eq]
  change _ = _
  refine heq.trans ?_
  congr 1
  rw [Finset.sum_insert (by simp [hzb, hzS]), Finset.sum_insert hbS,
    show complexResidue f z = _ from near_left_residue hzb hz,
    show complexResidue f b = _ from near_right_residue hzb hb]
  have hsum : (∑ ρ ∈ S, complexResidue f ρ) =
      -(∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * (1/(z-ρ) - 1/(b-ρ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hz' : ρ ≠ z := ne_of_mem_of_not_mem hρ hzS
    have hb' : ρ ≠ b := ne_of_mem_of_not_mem hρ hbS
    change complexResidue (fun u ↦ kernel z b u * logDeriv L u) ρ = _
    rw [complexResidue_mul_logDeriv _ _ _ (kernel_analytic hz' hb') (hL ρ (mem_univ ρ)) (hfinite ρ),
      kernel_eq_sub hz' hb', ← neg_sub z ρ, ← neg_sub b ρ]
    simp only [div_neg, sub_neg_eq_add]
    ring
  rw [hsum]
  abel

/-- The reciprocal difference gains two powers of the radius beyond both poles. -/
theorem norm_kernel_le {R : ℝ} {z b u : ℂ} (hR : 0 < R) (hu : R ≤ ‖u‖)
    (hz : ‖z‖ ≤ R/2) (hb : ‖b‖ ≤ R/2) :
    ‖kernel z b u‖ ≤ 4 * ‖z-b‖ / R^2 := by
  have hz' : R/2 ≤ ‖u-z‖ := by linarith [norm_sub_norm_le u z]
  have hb' : R/2 ≤ ‖u-b‖ := by linarith [norm_sub_norm_le u b]
  rw [kernel, norm_div, norm_mul]
  calc
    _ ≤ ‖z-b‖ / ((R/2)*(R/2)) := by
      apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      exact mul_le_mul hz' hb' (by positivity) (norm_nonneg _)
    _ = _ := by ring

/-- An arbitrary uniform bound on each of the four edges controls the rectangle
integral by the bound times its perimeter. -/
theorem norm_rectangle_le_perimeter {f : ℂ → ℂ} {x₁ x₂ y₁ y₂ M : ℝ}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hH : ∀ x ∈ Icc x₁ x₂, ∀ y ∈ ({y₁,y₂} : Set ℝ),
      ‖f ((x : ℂ)+(y : ℂ)*I)‖ ≤ M)
    (hV : ∀ y ∈ Icc y₁ y₂, ∀ x ∈ ({x₁,x₂} : Set ℝ),
      ‖f ((x : ℂ)+(y : ℂ)*I)‖ ≤ M) :
    ‖rectangleIntegral f ⟨x₁,y₁⟩ ⟨x₂,y₂⟩‖ ≤ 2*M*((x₂-x₁)+(y₂-y₁)) := by
  have hH' y (hy' : y ∈ ({y₁,y₂} : Set ℝ)) :
      ‖∫ x in x₁..x₂, f ((x : ℂ)+(y : ℂ)*I)‖ ≤ M*(x₂-x₁) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₁) (b := x₂)
      (C := M) (f := fun x : ℝ ↦ f ((x : ℂ)+(y : ℂ)*I)) fun x h ↦
        hH x (Ioc_subset_Icc_self (uIoc_of_le hx ▸ h)) y hy'
    simpa only [abs_of_nonneg (sub_nonneg.mpr hx)] using h
  have hV' x (hx' : x ∈ ({x₁,x₂} : Set ℝ)) :
      ‖I * ∫ y in y₁..y₂, f ((x : ℂ)+(y : ℂ)*I)‖ ≤ M*(y₂-y₁) := by
    rw [norm_mul, norm_I, one_mul]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := y₁) (b := y₂)
      (C := M) (f := fun y : ℝ ↦ f ((x : ℂ)+(y : ℂ)*I)) fun y h ↦
        hV y (Ioc_subset_Icc_self (uIoc_of_le hy ▸ h)) x hx'
    simpa only [abs_of_nonneg (sub_nonneg.mpr hy)] using h
  rw [rectangleIntegral_eq]
  calc
    _ ≤ (‖∫ x in x₁..x₂, f ((x : ℂ)+(y₁ : ℂ)*I)‖ +
        ‖∫ x in x₁..x₂, f ((x : ℂ)+(y₂ : ℂ)*I)‖) +
        ‖I * ∫ y in y₁..y₂, f ((x₂ : ℂ)+(y : ℂ)*I)‖ +
        ‖I * ∫ y in y₁..y₂, f ((x₁ : ℂ)+(y : ℂ)*I)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ _ := by linarith [hH' y₁ (by simp), hH' y₂ (by simp), hV' x₁ (by simp), hV' x₂ (by simp)]

/-- For square-like boxes reaching beyond radius `R`, the two-point kernel makes
a sublinear boundary bound sufficient. The final factor is independent of the box. -/
theorem norm_rectangle_kernel_le {F : ℂ → ℂ} {z b : ℂ} {R A B M : ℝ}
    (hR : 1 ≤ R) (hA : A ∈ Icc (-R-1) (-R)) (hB : B ∈ Icc R (R+1))
    (hz : ‖z‖ ≤ R/2) (hb : ‖b‖ ≤ R/2) (hM : 0 ≤ M)
    (hH : ∀ x ∈ Icc (-R) R, ∀ y ∈ ({A,B} : Set ℝ), ‖F ((x : ℂ)+(y : ℂ)*I)‖ ≤ M)
    (hV : ∀ y ∈ Icc A B, ∀ x ∈ ({-R,R} : Set ℝ), ‖F ((x : ℂ)+(y : ℂ)*I)‖ ≤ M) :
    ‖rectangleIntegral (fun u ↦ kernel z b u * F u) ⟨-R,A⟩ ⟨R,B⟩‖ ≤ 48*‖z-b‖*(M/R) := by
  have hp : 0 < R := by linarith
  let L := 4*‖z-b‖/R^2*M
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hk {u : ℂ} (hur : R ≤ ‖u‖) (hf : ‖F u‖ ≤ M) : ‖kernel z b u * F u‖ ≤ L := by
    rw [norm_mul]
    exact mul_le_mul (norm_kernel_le hp hur hz hb) hf (norm_nonneg _) (by positivity)
  have hrh (x y : ℝ) (hy : y ∈ ({A,B} : Set ℝ)) : R ≤ ‖(x : ℂ)+(y : ℂ)*I‖ := by
    have hq := Complex.abs_im_le_norm ((x : ℂ)+(y : ℂ)*I)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, zero_mul,
      add_zero, zero_add] at hq
    rcases hy with (hya | hyb)
    · rw [hya] at hq ⊢
      exact (by linarith [hA.2, neg_le_abs A] : R ≤ |A|).trans hq
    · rw [Set.mem_singleton_iff] at hyb
      rw [hyb] at hq ⊢
      exact (hB.1.trans (le_abs_self B)).trans hq
  have hrv (x y : ℝ) (hx : x ∈ ({-R,R} : Set ℝ)) : R ≤ ‖(x : ℂ)+(y : ℂ)*I‖ := by
    have hq := Complex.abs_re_le_norm ((x : ℂ)+(y : ℂ)*I)
    simp [Complex.mul_re] at hq
    rcases hx with (rfl | hx)
    · simpa [abs_neg, abs_of_pos hp] using hq
    · rw [Set.mem_singleton_iff] at hx
      simpa only [hx, abs_of_pos hp] using hq
  have hur := norm_rectangle_le_perimeter (f := fun u ↦ kernel z b u * F u) (M := L) (by linarith : -R ≤ R)
    (by linarith [hA.2,hB.1] : A ≤ B)
    (fun x hx y hy ↦ hk (hrh x y hy) (hH x hx y hy))
    (fun y hy x hx ↦ hk (hrv x y hx) (hV y hy x hx))
  refine hur.trans ?_
  calc
    _ ≤ 2*L*(6*R) := mul_le_mul_of_nonneg_left
      (by linarith [hA.1,hB.2]) (by positivity)
    _ = _ := by dsimp [L]; field_simp; ring

/-- A square-like rectangle whose boundary avoids the divisor and whose logarithmic
derivative has one common norm bound on its four edges. -/
structure RegularLogDerivBox (L : ℂ → ℂ) (R A B M : ℝ) : Prop where
  lower : A ∈ Icc (-R-1) (-R)
  upper : B ∈ Icc R (R+1)
  nonnegative : 0 ≤ M
  boundaryOrder : ∀ u ∈ Icc (-R) R ×ℂ Icc A B,
    u ∉ Ioo (-R) R ×ℂ Ioo A B → meromorphicOrderAt L u = 0
  horizontal : ∀ x ∈ Icc (-R) R, ∀ y ∈ ({A,B} : Set ℝ),
    ‖logDeriv L ((x : ℂ)+(y : ℂ)*I)‖ ≤ M
  vertical : ∀ y ∈ Icc A B, ∀ x ∈ ({-R,R} : Set ℝ),
    ‖logDeriv L ((x : ℂ)+(y : ℂ)*I)‖ ≤ M

private theorem finite_box_divisor (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (hf : ∀ u, meromorphicOrderAt L u ≠ ⊤) (R A B : ℝ) :
    {u : ℂ | u ∈ Ioo (-R) R ×ℂ Ioo A B ∧ meromorphicOrderAt L u ≠ 0}.Finite := by
  let K := Icc (-R) R ×ℂ Icc A B
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply ((MeromorphicOn.divisor L K).finiteSupport hK).subset
  intro u hu
  have huK : u ∈ K := ⟨⟨hu.1.1.1.le,hu.1.1.2.le⟩, ⟨hu.1.2.1.le,hu.1.2.2.le⟩⟩
  change MeromorphicOn.divisor L K u ≠ 0
  rw [MeromorphicOn.divisor_apply (hL.mono_set (subset_univ K)) huK, Ne, WithTop.untop₀_eq_zero]
  exact not_or.mpr ⟨hu.2,hf u⟩

/-- A meromorphic function with an absolutely summable two-point divisor series
and sublinear logarithmic-derivative bounds on exhausting boxes satisfies the
reference-subtracted partial fraction identity at two regular evaluation points. -/
theorem hasSum_divisor_resolvent_of_sublinear_boxes
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ) (hf : ∀ u, meromorphicOrderAt L u ≠ ⊤)
    (z b : ℂ) (hz0 : meromorphicOrderAt L z = 0) (hb0 : meromorphicOrderAt L b = 0)
    (hz : AnalyticAt ℂ (logDeriv L) z) (hb : AnalyticAt ℂ (logDeriv L) b)
    (A B M : ℕ → ℝ)
    (hboxes : ∀ᶠ n : ℕ in atTop, RegularLogDerivBox L n (A n) (B n) (M n))
    (hsmall : Tendsto (fun n : ℕ ↦ M n/n) atTop (𝓝 0))
    (hsum : Summable (fun ρ : {u : ℂ // meromorphicOrderAt L u ≠ 0} ↦
      ((meromorphicOrderAt L ρ.val).untop₀ : ℂ) * (1/(z-ρ.val)-1/(b-ρ.val)))) :
    HasSum (fun ρ : {u : ℂ // meromorphicOrderAt L u ≠ 0} ↦
      ((meromorphicOrderAt L ρ.val).untop₀ : ℂ) * (1/(z-ρ.val)-1/(b-ρ.val)))
      (logDeriv L z-logDeriv L b) := by
  classical
  by_cases hzb : z = b
  · subst b
    simp
  let D := {u : ℂ | meromorphicOrderAt L u ≠ 0}
  let w (u : ℂ) := ((meromorphicOrderAt L u).untop₀ : ℂ) * (1/(z-u)-1/(b-u))
  let S (n : ℕ) := (finite_box_divisor L hL hf n (A n) (B n)).toFinset
  have hS (n : ℕ) (u : ℂ) : u ∈ S n ↔
      u ∈ Ioo (-(n : ℝ)) (n : ℝ) ×ℂ Ioo (A n) (B n) ∧ meromorphicOrderAt L u ≠ 0 :=
    Set.Finite.mem_toFinset _
  have hInside (u : ℂ) : ∀ᶠ n : ℕ in atTop,
      u ∈ Ioo (-(n : ℝ)) (n : ℝ) ×ℂ Ioo (A n) (B n) := by
    filter_upwards [hboxes, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_gt_atTop (max |u.re| |u.im|))] with n hR hmax
    have hr : |u.re| < (n : ℝ) := (le_max_left _ _).trans_lt hmax
    have hi : |u.im| < (n : ℝ) := (le_max_right _ _).trans_lt hmax
    exact ⟨abs_lt.mp hr, ⟨hR.lower.2.trans_lt (abs_lt.mp hi).1,
      (abs_lt.mp hi).2.trans_le hR.upper.1⟩⟩
  let W (n : ℕ) : Finset D := (S n).subtype (· ∈ D)
  have hcof : Tendsto W atTop atTop := by
    simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
    intro u
    filter_upwards [hInside u.val] with n hn
    exact Finset.singleton_subset_iff.mpr (Finset.mem_subtype.mpr ((hS n u.val).mpr ⟨hn,u.property⟩))
  have hpartial : Tendsto (fun n ↦ ∑ u ∈ S n, w u) atTop (𝓝 (∑' u : D, w u.val)) := by
    have hws : HasSum (fun u : D ↦ w u.val) (∑' u : D, w u.val) := hsum.hasSum
    refine (Filter.Tendsto.comp hws hcof).congr fun n ↦ ?_
    exact Finset.sum_subtype_of_mem w fun u hu ↦ ((hS n u).mp hu).2
  let f (u : ℂ) := kernel z b u * logDeriv L u
  let Ibox (n : ℕ) := rectangleIntegral f ⟨-(n : ℝ),A n⟩ ⟨n,B n⟩
  have hbig : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) ∧ ‖z‖ ≤ (n : ℝ)/2 ∧ ‖b‖ ≤ (n : ℝ)/2 := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (max 1 (max (2*‖z‖) (2*‖b‖))))] with n hn
    have hnorm : max (2*‖z‖) (2*‖b‖) ≤ (n : ℝ) := (le_max_right _ _).trans hn
    refine ⟨(le_max_left _ _).trans hn, ?_, ?_⟩
    · linarith [le_max_left (2*‖z‖) (2*‖b‖)]
    · linarith [le_max_right (2*‖z‖) (2*‖b‖)]
  have hzero : Tendsto Ibox atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ ↦ 48*‖z-b‖*(M n/n)) atTop (𝓝 0) := by simpa using hsmall.const_mul (48*‖z-b‖)
    apply squeeze_zero_norm' _ hlim
    · filter_upwards [hboxes,hbig] with n hR hn
      exact norm_rectangle_kernel_le hn.1 hR.lower hR.upper hn.2.1 hn.2.2 hR.nonnegative
        hR.horizontal hR.vertical
  let c := 2 * (Real.pi : ℂ) * I
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero]
  have hid : (fun n ↦ Ibox n) =ᶠ[atTop]
      fun n ↦ c * (logDeriv L z - logDeriv L b - ∑ u ∈ S n, w u) := by
    filter_upwards [hboxes,hbig,hInside z,hInside b] with n hR hn hzin hbin
    apply rectangle_resolvent_logDeriv L hL hf z b hzb hz hb (by linarith [hn.1])
      (by linarith [hR.lower.2,hR.upper.1,hn.1]) hzin hbin (S n)
      (fun h ↦ ((hS n z).mp h).2 hz0) (fun h ↦ ((hS n b).mp h).2 hb0)
      (fun u hu ↦ ((hS n u).mp hu).1)
    intro u hu hnS
    by_contra hne
    by_cases hin : u ∈ Ioo (-(n : ℝ)) (n : ℝ) ×ℂ Ioo (A n) (B n)
    · exact hnS ((hS n u).mpr ⟨hin,hne⟩)
    · exact hne (hR.boundaryOrder u hu hin)
  have eql := tendsto_nhds_unique (hzero.congr' hid)
    ((tendsto_const_nhds.sub hpartial).const_mul c)
  have he : (∑' u : D, w u.val) = logDeriv L z-logDeriv L b := by
    have hsub := (mul_eq_zero.mp eql.symm).resolve_left hc
    exact (sub_eq_zero.mp hsub).symm
  exact he ▸ hsum.hasSum

end RiemannMasullo.ResolventRectangle
