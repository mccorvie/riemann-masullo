module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeConjugation
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Conjugation and reflection of completed Hecke logarithmic derivatives -/

public noncomputable section

open Classical Filter Function NumberField Set Complex
open scoped ComplexConjugate Topology

namespace RiemannMasullo.ResolventRectangle
variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

private theorem conjugate_nf {f : ℂ → ℂ} {s : ℂ} (hf : MeromorphicNFAt f (conj s)) :
    MeromorphicNFAt (conj ∘ f ∘ conj) s := by
  have hc := Complex.continuous_conj.tendsto s
  rcases hf with hz | ⟨n,g,hg,hn,hfg⟩
  · left
    filter_upwards [hc.eventually hz] with w hw
    exact (congrArg conj hw).trans (map_zero _)
  · have hga : AnalyticAt ℂ (conj ∘ g ∘ conj) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [hc.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with w hw
      simpa only [Complex.conj_conj] using hw.comp_ringHom conj conj
    refine Or.inr ⟨n, _, hga, (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hn, ?_⟩
    filter_upwards [hc.eventually hfg] with w hw
    simpa only [comp_apply, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, map_mul, map_zpow₀,
      map_sub, Complex.conj_conj] using congrArg conj hw

/-- For a unitary idèle class character, the genuine completed continuation of the
inverse character is the conjugate continuation on the whole plane. -/
theorem completed_inv_eq_conj (χ : U) :
    continuedCompletedHeckeL χ⁻¹ = conj ∘ continuedCompletedHeckeL χ ∘ conj := by
  let G := conj ∘ continuedCompletedHeckeL χ ∘ conj
  have hχ := (continuedCompletedHeckeL_spec χ).1
  have hI := (continuedCompletedHeckeL_spec χ⁻¹).1
  have hG : MeromorphicNFOn G univ := fun w _ ↦ conjugate_nf (hχ (mem_univ (conj w)))
  have h := heckeEulerProductOutside_eq_finite_nf_eq _ G hI.meromorphicOn hG.meromorphicOn (fun w hw ↦ by
    simpa only [G,Function.comp_apply,Complex.conj_conj] using continuedCompletedHeckeL_inv_conj_right χ (conj w) hw)
  rwa [toMeromorphicNFOn_eq_self.mpr hI,toMeromorphicNFOn_eq_self.mpr hG] at h

/-- The logarithmic derivative conjugation holds at all arguments in the canonical
normal-form conventions. -/
theorem completed_logDeriv_inv_conj (χ : U) (s : ℂ) :
    logDeriv (continuedCompletedHeckeL χ⁻¹) (conj s) = conj (logDeriv (continuedCompletedHeckeL χ) s) := by
  simp only [completed_inv_eq_conj χ,logDeriv_apply,deriv_conj_conj,Function.comp_apply,Complex.conj_conj,map_div₀]

/-- Same-character logarithmic differentiation across the critical line at every regular
point. The full discriminant–conductor logarithm is subtracted because it is absent from
the project's completed function. -/
theorem completed_logDeriv_reflection_regular (χ : U) (s : ℂ)
    (hs : meromorphicOrderAt (continuedCompletedHeckeL χ) s = 0) :
    logDeriv (continuedCompletedHeckeL χ) (1-conj s) =
      -conj (logDeriv (continuedCompletedHeckeL χ) s) - (heckeLogDiscriminantConductor χ : ℂ) := by
  have h := completedHeckeL_logDeriv_reflection χ _ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 (continuedCompletedHeckeL_spec χ⁻¹).1
    (continuedCompletedHeckeL_spec χ⁻¹).2 s hs
  have hc := congrArg conj h
  have hdual := completed_logDeriv_inv_conj χ (1-conj s)
  simp only [map_sub,map_one,Complex.conj_conj] at hdual
  rw [hdual] at hc
  simp only [map_sub,map_neg,Complex.conj_conj,Complex.conj_ofReal] at hc
  linear_combination hc

end RiemannMasullo.ResolventRectangle

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

/-- The logarithmic derivative of the two principal pole-clearing factors is
antisymmetric under the unshifted reflection. -/
private theorem principal_pair_reflection (s : ℂ) :
    1/(1-conj s) + 1/(1-conj s-1) = -conj (1/s+1/(s-1)) := by
  rw [show 1-conj s-1 = -(conj s) by ring,show 1-conj s = -(conj s-1) by ring]
  simp only [one_div,map_add,map_inv₀,map_sub,map_one,inv_neg]
  ring

/-- On the Euler half-plane, reflection of the same character's pole-corrected completed
logarithmic derivative is negative conjugation minus the full conductor logarithm.
The variable `s` is the original Hecke coordinate. -/
theorem completedHeckeL_poleCleared_logDeriv_reflection (χ : U𝔽) (s : ℂ) (hs : 1 < s.re) :
    let P (w : ℂ) := logDeriv (continuedCompletedHeckeL χ) w +
      if χ = 1 then 1/w + 1/(w-1) else 0
    P (1-conj s) = -conj (P s) - (heckeLogDiscriminantConductor χ : ℂ) := by
  intro P
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  have horder : meromorphicOrderAt (continuedCompletedHeckeL χ) s = 0 := by
    apply (hL (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
    rw [heq ⟨s, hs⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs))
      (finiteHeckeL_ne_zero_of_one_lt_re χ _)
  have hbare := ResolventRectangle.completed_logDeriv_reflection_regular χ s horder
  by_cases hχ : χ = 1
  · simp only [P, ite_eq_left hχ, hbare, principal_pair_reflection, map_add]
    ring
  · simp only [P, ite_eq_right hχ, hbare, add_zero]

/-- Real-part normalization for the same character, with the discriminant–conductor
logarithm occurring once and with negative sign. -/
theorem re_completedHeckeL_poleCleared_logDeriv_reflection (χ : U𝔽) (s : ℂ) (hs : 1 < s.re) :
    let P (w : ℂ) := logDeriv (continuedCompletedHeckeL χ) w +
      if χ = 1 then 1/w + 1/(w-1) else 0
    (P (1-conj s)).re = -(P s).re - heckeLogDiscriminantConductor χ := by
  intro P
  have h := congrArg Complex.re (completedHeckeL_poleCleared_logDeriv_reflection χ s hs)
  simpa only [Complex.sub_re,Complex.neg_re,Complex.conj_re,Complex.ofReal_re] using h

end RiemannMasullo
