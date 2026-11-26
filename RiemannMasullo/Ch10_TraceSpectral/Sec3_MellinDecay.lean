module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! # Decay of the Mellin transform of a test along a flow, uniformly in the character

The cluster route to Theorem 10.3.2.1 sums the Mellin transform of one compactly supported
Bruhat test over all angular components and all heights. This file gives the decay that the
sum needs, with one constant for all characters: the frequency of the quasi-character along a
one-parameter subgroup, to any power, times the Mellin transform of the test, is bounded.

* `bruhatCompactSupport_mellin_frequency_pow_le_of_weight` (any locally compact abelian group):
  for a one-parameter subgroup `b`, a continuous weight, a test `f` and a natural number `N`
  there is `K` such that every quasi-character `c` dominated by the weight satisfies
  `‖bruhatDirectionalDeriv b c 1‖ ^ N * ‖∫ f * c‖ ≤ K`. This is integration by parts along `b`,
  `N` times: the left side is the Mellin coefficient of the `N`-th derivative of `f` along `b`.
* `bruhatCompactSupport_mellin_frequency_pow_le` (idele classes): the same for all unitary
  characters `ψ` twisted by the power `w` of the norm, `|Re w| ≤ W`.
* `bruhatDirectionalDeriv_ideleClassNormTwist_of_mem_ker`: along a one-parameter subgroup of the
  norm-one classes the frequency of the twisted character is the frequency of `ψ` itself, the
  quantity by which `idelicExplicitFormula_normOneFourier_count` (`AppB_AnalyticNT/Sec4b.lean`)
  counts the characters.
* `bruhatDirectionalDeriv_ideleClassNormTwist_normSection`: along a section of the norm, for a
  character that is trivial on the section, the frequency is `w`.

The integration by parts is that of the private lemmas `bruhatMellin_integral_orbitDeriv` and
`bruhatMellin_directionalTest` of `AppB_AnalyticNT/Sec4b.lean`, copied here as private helpers
because they are private there. The public theorem
`idelicExplicitFormula_summable_spectral_characters` of that file uses the same estimate inside
its proof.

`Sec3_TraceClass` uses the last three statements. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "𝒟(" G ")" => BruhatCompactSupport G

section General

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Integrate a derivative along a one-parameter subgroup by first integrating its translates
over a unit time interval. Haar invariance cancels the two endpoints. Copy of the private
`bruhatMellin_integral_orbitDeriv` of `AppB_AnalyticNT/Sec4b.lean`. -/
private theorem bruhatCompactSupport_mellin_frequency_pow_le_of_weight_orbitDeriv
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] (X : LCATopologicalLie G) {w v : G → ℂ}
    (hw : Integrable w μ) (hv : Integrable v μ) (hc : Continuous v)
    (hd : ∀ x, HasDerivAt (fun t : ℝ ↦ w (x * X (Multiplicative.ofAdd t))) (v x) 0) :
    ∫ x, v x ∂μ = 0 := by
  let γ (t : ℝ) := X (Multiplicative.ofAdd t)
  have hγ : Continuous γ := X.continuous.comp continuous_ofAdd
  let V (t : ℝ) (x : G) := v (x * γ t)
  have htime (x : G) (t : ℝ) : HasDerivAt (fun s ↦ w (x * γ s)) (V t x) t := by
    have h : HasDerivAt (fun s ↦ w ((x * γ t) * γ s)) (V t x) (t - t) := sub_self t ▸ hd _
    convert h.comp_sub_const t t using 1
    funext s
    simp only [γ, mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have hFTC (x : G) : (∫ t in (0 : ℝ)..1, V t x) = w (x * γ 1) - w x := by
    simpa only [γ, ofAdd_zero, map_one, mul_one] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ htime x t)
        ((hc.comp (continuous_const.mul hγ)).intervalIntegrable (μ := volume) 0 1)
  have hV : Continuous (uncurry V) := hc.comp (continuous_snd.mul (hγ.comp continuous_fst))
  have hi : Integrable (uncurry V) ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) := by
    let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr (by simp)
    refine (integrable_prod_iff hV.aestronglyMeasurable).mpr ⟨.of_forall fun t ↦
      (measurePreserving_mul_right μ (γ t)).integrable_comp_of_integrable hv, ?_⟩
    have hnorm (t : ℝ) : (∫ x, ‖V t x‖ ∂μ) = ∫ x, ‖v x‖ ∂μ :=
      integral_mul_right_eq_self (fun x ↦ ‖v x‖) (γ t)
    simpa only [uncurry_apply_pair, hnorm] using
      (integrable_const (μ := volume.restrict (uIoc (0 : ℝ) 1)) (∫ x, ‖v x‖ ∂μ))
  have he := intervalIntegral_integral_swap hi
  simp_rw [hFTC] at he
  have hw' : Integrable (fun x ↦ w (x * γ 1)) μ :=
    (measurePreserving_mul_right μ (γ 1)).integrable_comp_of_integrable hw
  rw [integral_sub hw' hw, integral_mul_right_eq_self, sub_self] at he
  simpa [V, integral_mul_right_eq_self] using he

/-- A directional derivative of a test is again a test, and integration by parts expresses its
Mellin coefficient as the original coefficient times the negative multiplier of the
quasi-character. Copy of the private `bruhatMellin_directionalTest` of
`AppB_AnalyticNT/Sec4b.lean`. -/
private theorem bruhatCompactSupport_mellin_frequency_pow_le_of_weight_test (μ : Measure G)
    [μ.IsHaarMeasure] [SFinite μ] (X : LCATopologicalLie G) (f : 𝒟(G))
    (hf : Continuous f.val) :
    ∃ F : 𝒟(G), ∀ (c : QuasiCharacter G) (v : ℂ),
      HasDerivAt (fun t : ℝ ↦ c (X (Multiplicative.ofAdd t))) v 0 →
      (∫ x, F.val x * c x ∂μ) = -(v * ∫ x, f.val x * c x ∂μ) := by
  let D := bruhatDirectionalDeriv X f.val
  have h₁ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 1
  have hD : Continuous D := bruhatDirectionalDeriv_continuous X h₁
  have hK : HasCompactSupport D := by
    apply HasCompactSupport.of_support_subset_isCompact f.property.2
    intro x
    contrapose
    intro hx
    have hγ : Tendsto (fun t : ℝ ↦ x * X (Multiplicative.ofAdd t)) (𝓝 0) (𝓝 x) := by
      have h : Continuous (fun t : ℝ ↦ x * X (Multiplicative.ofAdd t)) :=
        continuous_const.mul (X.continuous.comp continuous_ofAdd)
      simpa using h.tendsto 0
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hγ
    rw [notMem_support]
    simpa [D, bruhatDirectionalDeriv, comp_def] using hz.deriv_eq
  refine ⟨⟨D, bruhatDirectionalDeriv_mem_smooth X ⟨_, f.property.1⟩, hK⟩, ?_⟩
  intro c v hc
  have hi : Integrable (fun x ↦ f.val x * c x) μ :=
    (hf.mul c.continuous).integrable_of_hasCompactSupport f.property.2.mul_right
  have hi' : Integrable (fun x ↦ D x * c x) μ :=
    (hD.mul c.continuous).integrable_of_hasCompactSupport hK.mul_right
  have he := bruhatCompactSupport_mellin_frequency_pow_le_of_weight_orbitDeriv μ X
    (v := fun x ↦ D x * c x + v * (f.val x * c x)) hi (hi'.add (hi.const_mul v))
    ((hD.mul c.continuous).add (continuous_const.mul (hf.mul c.continuous))) (fun x ↦ by
      have h := (hasDerivAt_bruhatDirectionalDeriv X h₁ x).fun_mul (hc.const_mul (c x))
      simp only [ofAdd_zero, map_one, mul_one] at h
      simpa only [map_mul, D, mul_left_comm, mul_comm, mul_assoc] using h)
  rw [integral_add hi' (hi.const_mul v), integral_const_mul] at he
  exact eq_neg_of_add_eq_zero_left he

/-- Paper: Lemma B.4.4.8, p. 624, the analytic half, along one one-parameter subgroup and
uniformly in the quasi-character. Let `b` be a one-parameter subgroup of a locally compact
abelian group and `Wt` a continuous weight. For every test `f` and every natural number `N`
there is a constant `K` such that every quasi-character `c` with `‖c x‖ ≤ Wt x` for all `x`
satisfies `‖bruhatDirectionalDeriv b c 1‖ ^ N * ‖∫ f * c‖ ≤ K`: the frequency of `c` along `b`,
to the power `N`, times the Mellin coefficient of the test.
Deviation: In the paper this decay stands inside the proof of Lemma B.4.4.8, for a modulated
abelian Lie group, with a constant independent of the quasi-character, as a consequence of
Theorem D.3.4.2. Here it is a statement of its own, for any locally compact abelian group and
one one-parameter subgroup, proved by integration by parts. -/
theorem bruhatCompactSupport_mellin_frequency_pow_le_of_weight (μ : Measure G)
    [μ.IsHaarMeasure] [SFinite μ] (b : LCATopologicalLie G) (Wt : G → ℝ)
    (hWt : Continuous Wt) (hcont : ∀ f : 𝒟(G), Continuous f.val) (N : ℕ) (f : 𝒟(G)) :
    ∃ K : ℝ, ∀ c : QuasiCharacter G, (∀ x, ‖c x‖ ≤ Wt x) →
      ‖bruhatDirectionalDeriv b (fun x ↦ c x) 1‖ ^ N * ‖∫ x, f.val x * c x ∂μ‖ ≤ K := by
  induction N generalizing f with
  | zero =>
    refine ⟨∫ x, ‖f.val x‖ * Wt x ∂μ, fun c hc ↦ ?_⟩
    rw [pow_zero, one_mul]
    apply norm_integral_le_of_norm_le (((hcont f).norm.mul hWt).integrable_of_hasCompactSupport
      f.property.2.norm.mul_right)
    exact .of_forall fun x ↦ (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hc x) (norm_nonneg _))
  | succ n ih =>
    obtain ⟨D, hD⟩ :=
      bruhatCompactSupport_mellin_frequency_pow_le_of_weight_test μ b f (hcont f)
    obtain ⟨K, hK⟩ := ih D
    refine ⟨K, fun c hc ↦ ?_⟩
    have hd := hasDerivAt_bruhatDirectionalDeriv b
      ((mem_bruhatSmoothSubmodule_iff _).mp (quasiCharacter_mem_bruhatSmooth c) 1) 1
    simp only [one_mul] at hd
    have h := hD c _ hd
    calc ‖bruhatDirectionalDeriv b (fun x ↦ c x) 1‖ ^ (n + 1) * ‖∫ x, f.val x * c x ∂μ‖
        = ‖bruhatDirectionalDeriv b (fun x ↦ c x) 1‖ ^ n * ‖∫ x, D.val x * c x ∂μ‖ := by
          rw [h, norm_neg, norm_mul, pow_succ, mul_assoc]
      _ ≤ K := hK c hc

end General

section IdeleClasses

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F

/-- Paper: Lemma B.4.4.8, p. 624, along one one-parameter subgroup and uniformly in the
character. For a compactly supported Bruhat test `φ` on the idele classes, a one-parameter
subgroup `b`, a real `W` and a natural number `N` there is a constant `K` such that for every
unitary character `ψ` and every `w` with `|Re w| ≤ W`, the frequency of the quasi-character
`ψ |·| ^ w` along `b`, to the power `N`, times the Mellin transform of the test at that
quasi-character, is at most `K`. For `N = 0` this is the plain uniform bound.
Deviation: In the paper this decay stands inside the proof of Lemma B.4.4.8, with a constant
independent of the quasi-character. The estimate is used inside the proof of
`idelicExplicitFormula_summable_spectral_characters` (`AppB_AnalyticNT/Sec4b.lean`) and is
stated here on its own, for one flow and all unitary characters. -/
theorem bruhatCompactSupport_mellin_frequency_pow_le (φ : BruhatCompactSupport C𝔽)
    (b : Multiplicative ℝ →ₜ* C𝔽) (W : ℝ) (N : ℕ) :
    ∃ K : ℝ, ∀ (ψ : PontryaginDual C𝔽) (w : ℂ), |w.re| ≤ W →
      ‖bruhatDirectionalDeriv b (fun g ↦ (ideleClassNormTwist (F := F) ψ w g : ℂ)) 1‖ ^ N *
        ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ ≤ K := by
  let ρ (x : C𝔽) : ℝ := ((ideleClassNorm F x).val : ℝ)
  have hρ (x : C𝔽) : 0 < ρ x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hρc : Continuous ρ := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  let Wt (x : C𝔽) := ρ x ^ W + ρ x ^ (-W)
  have hWt : Continuous Wt := (hρc.rpow_const fun x ↦ Or.inl (hρ x).ne').add
    (hρc.rpow_const fun x ↦ Or.inl (hρ x).ne')
  obtain ⟨K, hK⟩ := bruhatCompactSupport_mellin_frequency_pow_le_of_weight μ𝔽 b Wt hWt
    (fun f ↦ continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1))
    N φ
  refine ⟨K, fun ψ w hw ↦ hK (ideleClassNormTwist (F := F) ψ w) fun x ↦ ?_⟩
  change ‖((ψ x : Circle) : ℂ) * (ρ x : ℂ) ^ w‖ ≤ _
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hρ x)]
  rcases le_total (ρ x) 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge (hρ x) h (abs_le.mp hw).1).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg (hρ x).le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h (abs_le.mp hw).2).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hρ x).le _))

/-- Along a one-parameter subgroup of the norm-one idele classes the frequency of a unitary
character twisted by a power of the norm is the frequency of the character: the norm is one
along the subgroup. The right side is the quantity by which
`idelicExplicitFormula_normOneFourier_count` counts the characters. -/
theorem bruhatDirectionalDeriv_ideleClassNormTwist_of_mem_ker (b : Multiplicative ℝ →ₜ* C𝔽)
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (ψ : PontryaginDual C𝔽) (w : ℂ) :
    bruhatDirectionalDeriv b (fun g ↦ (ideleClassNormTwist (F := F) ψ w g : ℂ)) 1 =
      bruhatDirectionalDeriv b (fun x : C𝔽 ↦ (ψ x : ℂ)) 1 := by
  have h₁ := hasDerivAt_bruhatDirectionalDeriv b ((mem_bruhatSmoothSubmodule_iff _).mp
    (quasiCharacter_mem_bruhatSmooth (ideleClassNormTwist (F := F) ψ w)) 1) 1
  have h₂ := hasDerivAt_bruhatDirectionalDeriv b
    ((mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth ψ) 1) 1
  simp only [one_mul] at h₁ h₂
  refine h₁.unique (h₂.congr_of_eventuallyEq (.of_forall fun t ↦ ?_))
  have hn : ideleClassNorm F (b (Multiplicative.ofAdd t)) = 1 := MonoidHom.mem_ker.mp (hb _)
  change ((ψ (b (Multiplicative.ofAdd t)) : Circle) : ℂ) *
    (((ideleClassNorm F (b (Multiplicative.ofAdd t))).val : ℝ) : ℂ) ^ w = _
  rw [hn]
  simp

/-- Along a section `τ` of the norm, a unitary character that is trivial on the image of `τ`,
twisted by the power `w` of the norm, has frequency `w`. The private lemma
`idelicExplicitFormula_summable_spectral_characters_radial` of `AppB_AnalyticNT/Sec4b.lean` is
the case of a zero of the completed L-function. -/
theorem bruhatDirectionalDeriv_ideleClassNormTwist_normSection (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽)
    (hψ : ∀ t : ℝ≥0ˣ, ψ (τ t) = 1) (w : ℂ) :
    bruhatDirectionalDeriv (τ.comp (positiveRealLogEquiv.symm : _ →ₜ* _))
      (fun g ↦ (ideleClassNormTwist (F := F) ψ w g : ℂ)) 1 = w := by
  have h₁ := hasDerivAt_bruhatDirectionalDeriv (τ.comp (positiveRealLogEquiv.symm : _ →ₜ* _))
    ((mem_bruhatSmoothSubmodule_iff _).mp
      (quasiCharacter_mem_bruhatSmooth (ideleClassNormTwist (F := F) ψ w)) 1) 1
  simp only [one_mul] at h₁
  have he : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * w)) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp
  refine h₁.unique (he.congr_of_eventuallyEq (.of_forall fun t ↦ ?_))
  let u := positiveRealLogEquiv.symm (Multiplicative.ofAdd t)
  have hu : (u.val : ℝ) = Real.exp t := by
    have h := positiveRealLogEquiv_apply u
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt u))).symm.trans
      (congrArg Real.exp h.symm)
  change ((ψ (τ u) : Circle) : ℂ) * (((ideleClassNorm F (τ u)).val : ℝ) : ℂ) ^ w = _
  rw [hψ, Circle.coe_one, one_mul, hτ, hu, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

end IdeleClasses

end RiemannMasullo
