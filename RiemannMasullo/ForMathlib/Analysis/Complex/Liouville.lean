module

public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public section

open Filter Function Set
open scoped Topology

namespace RiemannMasullo

/-- An entire function without zeros whose modulus is invariant under imaginary translations
is a nonzero constant times an exponential with real exponent coefficient. -/
theorem exists_eq_const_mul_exp_of_norm_add_mul_I {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf₀ : ∀ z, f z ≠ 0)
    (hNorm : ∀ z (t : ℝ), ‖f (z + (t : ℂ) * Complex.I)‖ = ‖f z‖) :
    ∃ r : ℝ, ∀ z, f z = f 0 * Complex.exp ((r : ℂ) * z) := by
  have hShift (t : ℝ) (z : ℂ) :
      f (z + (t : ℂ) * Complex.I) * f 0 = f z * f ((t : ℂ) * Complex.I) := by
    let g (w : ℂ) := f (w + (t : ℂ) * Complex.I) / f w
    have hg : Differentiable ℂ g :=
      (hf.comp (differentiable_id.add_const _)).div hf hf₀
    have hBound : Bornology.IsBounded (range g) := by
      refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
      rintro _ ⟨w, rfl⟩
      change ‖f (w + (t : ℂ) * Complex.I) / f w‖ ≤ 1
      rw [norm_div, hNorm, div_self (norm_ne_zero_iff.mpr (hf₀ w))]
    have h := hg.apply_eq_apply_of_bounded hBound z 0
    simpa only [g, zero_add, div_eq_div_iff (hf₀ z) (hf₀ 0),
      mul_comm (f ((t : ℂ) * Complex.I))] using h
  have hAlong (z : ℂ) :
      (fun w ↦ f (z + w) * f 0) = fun w ↦ f z * f w := by
    apply AnalyticOnNhd.eq_of_frequently_eq (z₀ := 0)
    · exact fun w _ ↦ (hf.analyticAt (z + w)).comp
        (analyticAt_const.add analyticAt_id) |>.mul analyticAt_const
    · exact fun w _ ↦ analyticAt_const.mul (hf.analyticAt w)
    have ht : Tendsto (fun t : ℝ ↦ (t : ℂ) * Complex.I) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ ↦ (t : ℂ) * Complex.I) := by fun_prop
        simpa only [Complex.ofReal_zero, zero_mul] using
          (hc.continuousAt.continuousWithinAt (x := (0 : ℝ)) (s := {0}ᶜ)).tendsto
      · filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ) (a := 0)] with t ht
        simpa using ht
    exact ht.frequently (Frequently.of_forall fun t ↦ hShift t z)
  let a := deriv f 0 / f 0
  have hDeriv (z : ℂ) : deriv f z = a * f z := by
    have hz := (hf.differentiableAt (x := z)).hasDerivAt
    have hLeft : HasDerivAt (fun w ↦ f (z + w) * f 0) (deriv f z * f 0) 0 := by
      have hc : HasDerivAt (fun w : ℂ ↦ z + w) 1 0 := (hasDerivAt_id 0).const_add z
      simpa only [Function.comp_apply, id_eq, add_zero, mul_one] using
        ((show HasDerivAt f (deriv f z) (z + 0) by simpa only [add_zero] using hz).comp 0
          hc).mul_const (f 0)
    rw [hAlong z] at hLeft
    have h := hLeft.unique ((hf.differentiableAt (x := 0)).hasDerivAt.const_mul (f z))
    dsimp only [a]
    rw [div_mul_eq_mul_div, eq_div_iff (hf₀ 0), mul_comm (deriv f 0)]
    exact h
  let g (z : ℂ) := f z * Complex.exp (-a * z)
  have hg (z : ℂ) : HasDerivAt g 0 z := by
    have he := ((hasDerivAt_id z).const_mul (-a)).cexp
    simp only [id_eq, mul_one] at he
    convert (hf.differentiableAt.hasDerivAt.mul he : HasDerivAt g _ z) using 1
    rw [hDeriv]
    ring
  have hExp (z : ℂ) : f z = f 0 * Complex.exp (a * z) := by
    have h := is_const_of_deriv_eq_zero (fun w ↦ (hg w).differentiableAt)
      (fun w ↦ (hg w).deriv) z 0
    have he : Complex.exp (-a * z) * Complex.exp (a * z) = 1 := by
      rw [← Complex.exp_add, show -a * z + a * z = 0 by ring, Complex.exp_zero]
    simpa only [g, mul_zero, Complex.exp_zero, mul_one, mul_assoc, he] using
      congrArg (· * Complex.exp (a * z)) h
  have hI : ‖f Complex.I‖ = ‖f 0‖ := by simpa using hNorm 0 1
  rw [hExp Complex.I, norm_mul, Complex.norm_exp] at hI
  have hIm : a.im = 0 := by
    have h := mul_left_cancel₀ (norm_ne_zero_iff.mpr (hf₀ 0)) (hI.trans (mul_one _).symm)
    have hh : Real.exp ((a * Complex.I).re) = Real.exp 0 := h.trans Real.exp_zero.symm
    simpa [Complex.mul_re] using Real.exp_injective hh
  refine ⟨a.re, ?_⟩
  have hReal : (a.re : ℂ) = a := by
    apply Complex.ext <;> simp [hIm]
  simpa only [hReal] using hExp

end RiemannMasullo
