module

public import RiemannMasullo.AppB_AnalyticNT.Sec4a
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Ideal.Int

/-!
# Appendix B.4.1: statements that are false as printed

The printed claim is kept as a proposition with a separate refutation statement.
Nothing imports this file.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped SchwartzMap

namespace RiemannMasullo

/-- Paper: Lemma B.4.1.7, p. 611. As printed: for every number field, continuous
character unramified at a given prime, and Schwartz test function of exponential decay,
the sum of its Mellin transform over the local frequencies equals the negative
normalized logarithmic-derivative integral on any positive vertical line, for every
choice of logarithm. This is the second equality in (B.4.1.20), repeated in
(B.4.1.35). The first equality is `hasSum_localEulerFactor_mellinSamples`.
The one-sided integral formula is `hasSum_localEulerFactor_cauchyIntegral`.
See ERRATA F18. -/
def Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)),
    (ideleClassNormTwist χ 0).IsUnramifiedAt v →
    ∀ (f : 𝓢(ℝ, ℂ)), ExponentialDecay f →
      ∀ a > (0 : ℝ), ∀ ℓ : ℂ,
        let c := (ideleClassNormTwist χ 0).localValue v
        Complex.exp ℓ = c →
          let q : ℂ := v.asIdeal.absNorm
          let logq : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
          let Φ := mellin (fun t : ℝ ↦ f (Real.log t))
          let twoPiI := 2 * (Real.pi : ℂ) * Complex.I
          (∑' m : ℤ, Φ ((ℓ + twoPiI * (m : ℂ)) / logq)) =
            -verticalLineIntegral (fun s ↦ Φ s * (logq / (1 - c⁻¹ * q ^ s))) a / twoPiI

/-- A smooth bump at zero isolates the zeroth sample on a lattice of spacing `L`. -/
private theorem Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_bump
    (L : ℝ) (hL : 0 < L) :
    ∃ f : 𝓢(ℝ, ℂ), ExponentialDecay f ∧ f 0 = 1 ∧
      ∀ m : ℤ, m ≠ 0 → f ((m : ℝ) * L) = 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨L / 4, L / 2, by positivity, by linarith⟩
  have hc : HasCompactSupport (fun x ↦ (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hder (j : ℕ) : HasCompactSupport (iteratedDeriv j (f : ℝ → ℂ)) := by
    induction j with
    | zero =>
      rw [iteratedDeriv_zero]
      exact hc
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hdec : ExponentialDecay f := by
    simp only [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hder
    exact ⟨fun j _ _ ↦ ((hder j).filter_mono atTop_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _), fun j _ _ ↦
      ((hder j).filter_mono atBot_le_cocompact).trans_isBigO (Asymptotics.isBigO_zero _ _)⟩
  refine ⟨f, hdec, ?_, fun m hm ↦ ?_⟩
  · change (b 0 : ℂ) = 1
    rw [b.eventuallyEq_one.self_of_nhds]
    rfl
  · change (b ((m : ℝ) * L) : ℂ) = 0
    apply Complex.ofReal_eq_zero.mpr ∘ b.zero_of_le_dist
    have hm' : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.add_one_le_of_lt (abs_pos.mpr hm)
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hL]
    exact (half_le_self hL.le).trans (le_mul_of_one_le_left hL.le hm')

/-- The logarithmic derivative of the trivial unramified factor in the printed coordinates. -/
private theorem Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_logDeriv
    (q : ℕ) (hq : q ≠ 0) (s : ℂ) :
    logDeriv (fun z : ℂ ↦ (1 - (q : ℂ) ^ (-z))⁻¹) s =
      (Real.log (q : ℝ) : ℂ) / (1 - (q : ℂ) ^ s) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hd := ((hasDerivAt_neg' s).const_cpow (Or.inl hq')).const_sub 1
  have hinv := logDeriv_fun_zpow hd.differentiableAt (-1)
  simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hinv
  rw [hinv, logDeriv_apply, hd.deriv, Complex.cpow_neg, Complex.natCast_log]
  have hp : (q : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq')
  by_cases h : (q : ℂ) ^ s = 1
  · simp [h]
  · field_simp [hp, sub_ne_zero.mpr h, sub_ne_zero.mpr (Ne.symm h)]
    ring

/-- At a prime above two the full lattice contributes its zeroth term, while the
positive lattice contributes nothing. -/
private theorem Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_false_of_numberField.{u}
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral.{u}) : False := by
  obtain ⟨P, hP, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 F) (Ideal.span {((2 : ℕ) : ℤ)})
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, NeZero.ne P⟩
  let χ : PontryaginDual (IdeleClassGroup (𝓞 F) F) := 1
  have hres (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ 0).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunr := HeckeCharacter.isUnramifiedAt_iff.mpr
    (fun u ↦ hres (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u))
  have hval : (ideleClassNormTwist χ 0).localValue v = 1 := by
    obtain ⟨π, hπ⟩ :=
      (Valued.v (R := v.adicCompletion F)).exists_isUniformizer_of_isCyclic_of_nontrivial
    rw [hunr.localValue_eq π hπ]
    exact hres (Units.mk0 π hπ.ne_zero)
  let q := v.asIdeal.absNorm
  let L := Real.log (q : ℝ)
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨f, hf, hf₀, hoff⟩ := Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_bump L hL
  have hℓ : Complex.exp 0 = (ideleClassNormTwist χ 0).localValue v := by
    rw [hval, Complex.exp_zero]
  have hfreq := (hasSum_localEulerFactor_mellinSamples χ v hunr f hf 0 hℓ).tsum_eq
  have hright := (hasSum_localEulerFactor_cauchyIntegral χ v hunr f hf 1 one_pos).tsum_eq
  have hsum : (∑' m : ℤ, (ideleClassNormTwist χ 0).localValue v ^ m * f ((m : ℝ) * L)) = 1 := by
    rw [tsum_eq_single (0 : ℤ) (fun m hm ↦ by rw [hoff m hm, mul_zero])]
    simp [hf₀]
  have hpos (m : ℕ) : f ((m + 1 : ℕ) * Real.log (v.asIdeal.absNorm : ℝ)) = 0 := by
    exact_mod_cast hoff (m + 1 : ℕ) (by positivity)
  have hfactor : finiteHeckeEulerFactor χ v = fun z : ℂ ↦ (1 - (q : ℂ) ^ (-z))⁻¹ := by
    funext z
    simp only [finiteHeckeEulerFactor, ite_eq_left hunr, hval, one_mul, q]
  have heuler := Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_logDeriv q (by omega)
  have heq := h F χ v hunr f hf 1 one_pos 0 hℓ
  dsimp only at heq
  rw [hfreq, hsum, mul_one] at heq
  simp only [hval, inv_one, one_mul] at heq
  simp only [hfactor, heuler, hpos, mul_zero, tsum_zero] at hright
  exact (Complex.ofReal_ne_zero.mpr hL.ne') (heq.trans hright.symm)

/-- Paper: Lemma B.4.1.7, p. 611. Take the rational field, the prime `(2)`,
the trivial character, logarithm zero, and the vertical line at `a = 1`.
Choose a smooth logarithmic profile supported in `(-log 2 / 2, log 2 / 2)` with
value one at zero. The frequency sum equals the two-sided lattice sum times
`log 2`, and only the index zero contributes. The right-line integral samples only
the strictly positive powers of two, so it vanishes. -/
theorem Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_false :
    ¬ Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact Printed.localEulerFactor_mellinSamples_eq_cauchyIntegral_false_of_numberField (ULift ℚ) h

end RiemannMasullo
