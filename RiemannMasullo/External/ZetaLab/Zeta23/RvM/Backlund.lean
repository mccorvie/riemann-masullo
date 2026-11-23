module

/- Ported from teal-sea/zeta-lab at a401821c9608526425f3d4cf7ff8e59bc37e1c79.
Upstream file: lean/vendor/zeta23/Zeta23/RvM/Backlund.lean
Apache-2.0, see Zeta23.LICENSE and Zeta23.NOTICE. Local changes for Lean 4.36 are recorded in SOURCE_MAP.json. -/

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

public import RiemannMasullo.External.ZetaLab.Zeta23.RvM.ZetaGrowth
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

open Complex Set MeasureTheory Real intervalIntegral


noncomputable section

namespace Zeta23
namespace RvM

section Variation

variable {T : ℝ}

lemma ofReal_add_mul_I_ne_one (hT : T ≠ 0) (σ : ℝ) : (σ : ℂ) + T * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hT this

/-- `σ ↦ ζ(σ+iT)` has derivative `ζ'(σ+iT)` in the real variable `σ`. -/
lemma hasDerivAt_riemannZeta_horizontal (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => riemannZeta (σ + T * I)) (deriv riemannZeta (σ + T * I)) σ := by
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (σ + T * I)) (σ + T * I) :=
    (differentiableAt_riemannZeta (ofReal_add_mul_I_ne_one hT σ)).hasDerivAt
  have hγ : HasDerivAt (fun σ : ℝ => (σ : ℂ) + T * I) 1 σ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt
    simpa using h1.add_const ((T : ℂ) * I)
  exact (hζ.comp σ hγ).congr_deriv (mul_one _)

lemma continuous_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => riemannZeta (σ + T * I)) :=
  continuous_iff_continuousAt.mpr fun σ => (hasDerivAt_riemannZeta_horizontal hT σ).continuousAt

lemma continuous_deriv_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => deriv riemannZeta (σ + T * I)) := by
  have hγ : Continuous (fun σ : ℝ => (σ : ℂ) + T * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  exact hA.deriv.continuousOn.comp_continuous hγ (fun σ => ofReal_add_mul_I_ne_one hT σ)

/-- `σ ↦ ζ'/ζ(σ+iT)` is continuous on `[1/2,2]` when ζ has no zero on that segment. -/
lemma continuousOn_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    ContinuousOn (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) (Set.Icc (1/2 : ℝ) 2) := by
  have h : ContinuousOn (fun σ : ℝ => deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I))
      (Set.Icc (1/2 : ℝ) 2) :=
    (continuous_deriv_riemannZeta_horizontal hT).continuousOn.div
      (continuous_riemannZeta_horizontal hT).continuousOn hnz
  exact h.congr (fun σ _ => by rw [logDeriv_apply])

lemma intervalIntegrable_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : u ∈ Set.Icc (1/2 : ℝ) 2) (hv : v ∈ Set.Icc (1/2 : ℝ) 2) :
    IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) volume u v :=
  ((continuousOn_logDeriv_horizontal hT hnz).mono
    (Set.uIcc_subset_Icc hu hv)).intervalIntegrable

end Variation

/-! ## The vertical side σ = 2 -/

/-- `Re ζ(2+it) > 0` (indeed `≥ 2 − π²/6`), from `‖ζ(s) − 1‖ ≤ π²/6 − 1 < 1` on `Re s ≥ 2`. -/
lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re := by
  have h := norm_riemannZeta_sub_one_le (s := 2 + t * I) (by simp)
  have h2 : |(riemannZeta (2 + t * I) - 1).re| ≤ ‖riemannZeta (2 + t * I) - 1‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := (abs_le.mp (h2.trans h)).1
  linarith [pi_sq_div_six_sub_one_lt_one]

lemma two_add_mul_I_ne_one (t : ℝ) : (2 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- `t ↦ log ζ(2+it)` is a primitive of `t ↦ ζ'/ζ(2+it)·i`. -/
lemma hasDerivAt_log_riemannZeta_two (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + t * I)))
      (logDeriv riemannZeta (2 + t * I) * I) t := by
  have hs := two_add_mul_I_ne_one t
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (2 + t * I)) (2 + t * I) :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hγ : HasDerivAt (fun t : ℝ => (2 : ℂ) + t * I) I t := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.mul_const I).const_add (2 : ℂ)
  have hcomp : HasDerivAt (fun t : ℝ => riemannZeta (2 + t * I)) (deriv riemannZeta (2 + t * I) * I) t :=
    hζ.comp t hγ
  have hlog : HasDerivAt Complex.log (riemannZeta (2 + t * I))⁻¹ (riemannZeta (2 + t * I)) :=
    Complex.hasDerivAt_log (Or.inl (re_riemannZeta_two_pos t))
  have h := hlog.comp t hcomp
  have e : (riemannZeta (2 + t * I))⁻¹ * (deriv riemannZeta (2 + t * I) * I)
      = logDeriv riemannZeta (2 + t * I) * I := by
    rw [logDeriv_apply]; ring
  rw [e] at h
  exact h

/-- Continuity of `t ↦ ζ'/ζ(2+it)·i`. -/
lemma continuous_logDeriv_riemannZeta_two :
    Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) := by
  have hγ : Continuous (fun t : ℝ => (2 : ℂ) + t * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  have hd : Continuous (fun t : ℝ => deriv riemannZeta (2 + t * I)) :=
    hA.deriv.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hz : Continuous (fun t : ℝ => riemannZeta (2 + t * I)) :=
    hA.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hne : ∀ t : ℝ, riemannZeta (2 + t * I) ≠ 0 := fun t h => by
    have := re_riemannZeta_two_pos t; rw [h] at this; simp at this
  simp only [logDeriv_apply]
  exact ((hd.div hz hne).mul continuous_const)

end RvM
end Zeta23
