module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Compact Laplace probes with prescribed real zeros -/

@[expose] public noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace RiemannMasullo

/-- Integration by parts for the bilateral Laplace transform of a compact smooth profile. -/
theorem bilateralLaplace_deriv_of_compact (h : ℝ → ℂ) (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (z : ℂ) :
    bilateralLaplace (deriv h) z = -(z * bilateralLaplace h z) := by
  let E (x : ℝ) := Complex.exp (z * x)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hd : Continuous (deriv h) := hs.continuous_deriv (by simp)
  have hE' (x : ℝ) : HasDerivAt E (z * E x) x := by
    change HasDerivAt (fun t : ℝ ↦ Complex.exp (z * t)) (z * Complex.exp (z * x)) x
    convert (((hasDerivAt_id' (x : ℂ)).const_mul z).cexp).comp_ofReal using 1
    ring
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := E) (u' := fun x ↦ z * E x) (v := h) (v' := deriv h) (fun x _ ↦ hE' x)
    (fun x _ ↦ ((hs.differentiable (by simp)) x).hasDerivAt)
    ((hE.mul hd).integrable_of_hasCompactSupport hc.deriv.mul_left)
    (((continuous_const.mul hE).mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hE.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
  change (∫ x : ℝ, deriv h x * E x) = -(z * ∫ x : ℝ, h x * E x)
  calc
    ∫ x : ℝ, deriv h x * E x = ∫ x : ℝ, E x * deriv h x := by congr 1; funext x; ring
    _ = -∫ x : ℝ, z * E x * h x := hparts
    _ = -(z * ∫ x : ℝ, h x * E x) := by
      rw [← integral_const_mul]; congr 2; funext x; ring

private theorem norm_bilateralLaplace_le_weight (h : ℝ → ℂ) (hs : Continuous h)
    (hc : HasCompactSupport h) (β : ℝ) {z : ℂ} (hz : |z.re| ≤ β) :
    ‖bilateralLaplace h z‖ ≤ ∫ x : ℝ, ‖h x‖ * Real.exp (β * |x|) := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (.of_forall fun x ↦ norm_nonneg _)
    ((hs.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hc.norm.mul_right)
  refine .of_forall fun x ↦ ?_
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact ((le_abs_self _).trans (abs_mul _ _).le).trans
    (mul_le_mul_of_nonneg_right hz (abs_nonneg x))

/-- Two integrations by parts give a uniform estimate including the real frequency zero. -/
theorem exists_bilateralLaplace_inverseSquare_bound (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (β : ℝ) :
    ∃ D : ℝ, ∀ z : ℂ, |z.re| ≤ β → ‖bilateralLaplace H z‖ ≤ D / (1 + |z.im|) ^ 2 := by
  let A (h : ℝ → ℂ) := ∫ x : ℝ, ‖h x‖ * Real.exp (β * |x|)
  let H₂ := deriv (deriv H)
  have hs' : ContDiff ℝ ∞ (deriv H) := (contDiff_infty_iff_deriv.mp hs).2
  refine ⟨2 * (A H + A H₂), fun z hz ↦ ?_⟩
  have h₀ := norm_bilateralLaplace_le_weight H hs.continuous hc β hz
  have h₂ := norm_bilateralLaplace_le_weight H₂ (hs'.continuous_deriv (by simp))
    hc.deriv.deriv β hz
  have hid : bilateralLaplace H₂ z = z ^ 2 * bilateralLaplace H z := by
    rw [show bilateralLaplace H₂ z = _ from bilateralLaplace_deriv_of_compact _ hs' hc.deriv z,
      bilateralLaplace_deriv_of_compact H hs hc z]
    ring
  rw [hid, norm_mul, norm_pow] at h₂
  have hsq : |z.im| ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [Complex.abs_im_le_norm z, abs_nonneg z.im, norm_nonneg z,
      mul_nonneg (sub_nonneg.mpr (Complex.abs_im_le_norm z))
        (add_nonneg (norm_nonneg z) (abs_nonneg z.im))]
  have him := mul_le_mul_of_nonneg_right hsq (norm_nonneg (bilateralLaplace H z))
  have hh : (1 + |z.im|) ^ 2 ≤ 2 * (1 + |z.im| ^ 2) := by nlinarith [sq_nonneg (1 - |z.im|)]
  have hh' := mul_le_mul_of_nonneg_left hh (norm_nonneg (bilateralLaplace H z))
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + |z.im|))).mpr
  change ‖bilateralLaplace H z‖ ≤ A H at h₀
  change ‖z‖ ^ 2 * ‖bilateralLaplace H z‖ ≤ A H₂ at h₂
  nlinarith [him, hh']

private theorem bilateralLaplace_real_polar_step (h : ℝ → ℝ) (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (p : ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ ((p * h x + deriv h x : ℝ) : ℂ)) z =
      ((p : ℂ) - z) * bilateralLaplace (fun x ↦ (h x : ℂ)) z := by
  let E := fun x : ℝ ↦ Complex.exp (z * x)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hH : Continuous (fun x ↦ (h x : ℂ)) := Complex.continuous_ofReal.comp hs.continuous
  have hD : Continuous (fun x ↦ ((deriv h x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hs.continuous_deriv (by simp))
  have hcH : HasCompactSupport (fun x ↦ (h x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hcD : HasCompactSupport (fun x ↦ ((deriv h x : ℝ) : ℂ)) := hc.deriv.comp_left Complex.ofReal_zero
  have ih : Integrable (fun x ↦ (h x : ℂ) * E x) :=
    (hH.mul hE).integrable_of_hasCompactSupport hcH.mul_right
  have ider : Integrable (fun x ↦ ((deriv h x : ℝ) : ℂ) * E x) :=
    (hD.mul hE).integrable_of_hasCompactSupport hcD.mul_right
  have hcomp : ContDiff ℝ ∞ (fun x ↦ (h x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hder : deriv (fun x ↦ (h x : ℂ)) = fun x ↦ ((deriv h x : ℝ) : ℂ) :=
    funext fun x ↦ ((hs.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  have hd := bilateralLaplace_deriv_of_compact (fun x ↦ (h x : ℂ)) hcomp hcH z
  rw [hder] at hd
  change (∫ x : ℝ, ((deriv h x : ℝ) : ℂ) * E x) = -(z * ∫ x : ℝ, (h x : ℂ) * E x) at hd
  change (∫ x : ℝ, ((p * h x + deriv h x : ℝ) : ℂ) * E x) =
    ((p : ℂ) - z) * ∫ x : ℝ, (h x : ℂ) * E x
  have hsplit : (fun x : ℝ ↦ ((p * h x + deriv h x : ℝ) : ℂ) * E x) =
      fun x : ℝ ↦ (p : ℂ) * ((h x : ℂ) * E x) + ((deriv h x : ℝ) : ℂ) * E x := by
    funext x; push_cast; ring
  rw [hsplit, integral_add (ih.const_mul (p : ℂ)) ider, integral_const_mul, hd]
  ring

private theorem exists_bilateralLaplace_polar_polynomial (g : ℝ → ℝ) (hs : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (P : Finset ℝ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧ ∀ z : ℂ,
      bilateralLaplace (fun x ↦ (k x : ℂ)) z =
        (∏ p ∈ P, ((p : ℂ) - z)) * bilateralLaplace (fun x ↦ (g x : ℂ)) z := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨g, hs, hc, fun z ↦ by simp⟩
  | @insert p P hp ih =>
    obtain ⟨k, hks, hkc, hk⟩ := ih
    have hpK : HasCompactSupport (fun x ↦ p * k x) := hkc.mul_left
    refine ⟨fun x ↦ p * k x + deriv k x, (contDiff_const.mul hks).add
      (contDiff_infty_iff_deriv.mp hks).2, hpK.add hkc.deriv, ?_⟩
    intro z
    rw [bilateralLaplace_real_polar_step k hks hkc p z, hk, Finset.prod_insert hp, mul_assoc]

private theorem bilateralLaplace_polar_shift (g : ℝ → ℂ) (y : ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ g (x - y)) z = Complex.exp (z * y) * bilateralLaplace g z := by
  unfold bilateralLaplace
  calc ∫ x : ℝ, g (x - y) * Complex.exp (z * x)
      = ∫ x : ℝ, g (x - y) * Complex.exp (z * (((x - y : ℝ) : ℂ) + y)) := by
        congr 1; funext x; push_cast; ring_nf
    _ = ∫ x : ℝ, g x * Complex.exp (z * (x + y)) :=
      integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ g x * Complex.exp (z * (x + y))) y
    _ = _ := by rw [← integral_const_mul]; congr 1; funext x; rw [mul_add, Complex.exp_add]; ring

/-- Apply the differential factors `p + d/dx` to a real smooth compact seed and shift its support
into the open positive half-line. Each further translate has the stated exact Laplace transform. -/
theorem exists_positive_support_bilateralLaplace_polynomial (g : ℝ → ℝ) (hs : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (P : Finset ℝ) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧
      ∃ d : ℝ, ∀ (y : ℝ) (z : ℂ), bilateralLaplace (fun x ↦ (H (x - y) : ℂ)) z =
        Complex.exp (z * ((y + d : ℝ) : ℂ)) *
          ((∏ p ∈ P, ((p : ℂ) - z)) * bilateralLaplace (fun x ↦ (g x : ℂ)) z) := by
  obtain ⟨k, hks, hkc, hk⟩ := exists_bilateralLaplace_polar_polynomial g hs hc P
  have hcompact : IsCompact (tsupport k) := hkc
  obtain ⟨a, ha⟩ := hcompact.bddBelow
  let d := 1 - a
  refine ⟨fun x ↦ k (x - d), hks.comp (contDiff_id.sub contDiff_const),
    hkc.comp_homeomorph (Homeomorph.subRight d), ?_, d, ?_⟩
  · intro x hx
    have hkx : x - d ∈ tsupport k :=
      tsupport_comp_subset_preimage (f := fun t : ℝ ↦ t - d) k (continuous_id.sub continuous_const) hx
    have hx' : a ≤ x - d := ha hkx
    change 0 < x
    dsimp [d] at hx'
    linarith
  · intro y z
    simp only [sub_sub]
    rw [bilateralLaplace_polar_shift (fun x ↦ (k x : ℂ)) (y + d) z, hk]

/-- One real smooth compact profile supported in the open positive half-line annihilates every
prescribed real moment, and its bilateral Laplace transform is nonzero at every other point of
the closed strip. The prescribed moments may lie anywhere on the real axis. -/
theorem exists_compact_positive_support_laplace_polar_filter {B : ℝ} (hB : 0 < B) (P : Finset ℝ) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧
      (∀ p ∈ P, bilateralLaplace (fun x ↦ (H x : ℂ)) (p : ℂ) = 0) ∧
      ∀ z : ℂ, |z.re| ≤ B → (∀ p ∈ P, z ≠ (p : ℂ)) →
        bilateralLaplace (fun x ↦ (H x : ℂ)) z ≠ 0 := by
  classical
  obtain ⟨g, hgs, hgc, _, _, hpositive⟩ := exists_compact_positive_laplace_strip hB
  obtain ⟨H, hs, hc, hsupport, d, hfactor⟩ :=
    exists_positive_support_bilateralLaplace_polynomial g hgs hgc P
  have hL (z : ℂ) := hfactor 0 z
  simp only [sub_zero, zero_add] at hL
  refine ⟨H, hs, hc, hsupport, ?_, ?_⟩
  · intro p hp
    rw [hL, Finset.prod_eq_zero hp (sub_self (p : ℂ)), zero_mul, mul_zero]
  · intro z hz haway
    have hseed : bilateralLaplace (fun x ↦ (g x : ℂ)) z ≠ 0 := by
      intro hzero
      simpa [hzero] using hpositive z hz
    rw [hL]
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun p hp ↦ sub_ne_zero.mpr (haway p hp).symm)) hseed)

end RiemannMasullo
