module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_PositiveLog
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.Ch13_ZerosHecke.Targets
import Mathlib.Data.Nat.Prime.Int
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # The von Mangoldt formula for the positive divisor of completed zeta

The positive-axis contributions in §12.3 use Mathlib's completed Riemann
zeta function. Specializing Theorem B.4.2.2 to the principal rational character
identifies the prime ideal sum with von Mangoldt sampling. The pole at zero
cancels the constant part of the real-place kernel, leaving the pole at one.
-/

public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ArithmeticFunction ContDiff NumberField.AdeleRing Topology

namespace RiemannMasullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "X" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
local notation "L₀" => toMeromorphicNFOn completedRiemannZeta univ
local notation "d₀" => MeromorphicOn.divisor completedRiemannZeta univ
local notation "M(" H ", " z ")" => bilateralLaplace H z
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "tw₀" => ideleClassNormTwist X 0

private theorem rational_norm (v : V) : v.asIdeal.absNorm = (Rat.HeightOneSpectrum.primesEquiv v).val := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hmap : v.asIdeal.map e = (Ideal.span {(p : 𝓞 ℚ)}).map e := by
    simpa [Ideal.map_span, e, p] using (Rat.HeightOneSpectrum.span_natGenerator v).symm
  have he := congrArg (Ideal.comap e) hmap
  simp only [Ideal.comap_map_of_bijective e e.bijective] at he
  rw [he, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl

private theorem prime_power_sum (H : ℝ → ℂ) :
    (∑' j : V × ℕ, (Real.log q(j.1) : ℂ) * H (((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1))) =
      (∑' n : ℕ, (Λ n : ℂ) * H (Real.log n)) := by
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let g (j : V × ℕ) : ℕ := (e j.1).val ^ (j.2 + 1)
  have hi : Injective g := by
    intro i j hij
    obtain ⟨hp, hn⟩ := (e i.1).property.pow_inj (e j.1).property hij
    exact Prod.ext (e.injective (Subtype.ext hp)) hn
  have hs : support (fun n : ℕ ↦ (Λ n : ℂ) * H (Real.log n)) ⊆ range g := by
    intro n hn
    have hΛ : Λ n ≠ 0 := fun h ↦ hn (by simp [h])
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (by_contra fun h ↦
      hΛ (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h))
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact ⟨(e.symm ⟨p, hp⟩, k), congrArg (fun q : Nat.Primes ↦ q.val ^ (k + 1))
      (e.apply_symm_apply ⟨p, hp⟩)⟩
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro j
  simp [g, rational_norm, e, ArithmeticFunction.vonMangoldt_apply_pow,
    ArithmeticFunction.vonMangoldt_apply_prime (e j.1).property, Real.log_pow]

private theorem principal_twist : tw₀ = 1 := by
  ext1 x
  change (1 : ℂ) * (((ideleClassNorm ℚ x).val : ℝ) : ℂ) ^ (0 : ℂ) = 1
  simp

private theorem principal_unit (v : V) (u : (v.adicCompletion ℚ)ˣ) :
    (1 : HeckeCharacter (𝓞 ℚ) ℚ).restrict v u = 1 := by
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  rfl

private theorem principal_unramified (v : V) : (tw₀).IsUnramifiedAt v := by
  rw [principal_twist]
  exact HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
    principal_unit v (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom x)

private theorem principal_value (v : V) : (tw₀).localValue v = 1 := by
  rw [principal_twist]
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  exact principal_unit v (Units.mk0 _ val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)

private theorem principal_parameters (v : InfinitePlace ℚ) (h : v.IsReal) :
    (realHeckeCharacter_parameters X v h).exists.choose = (0, 0) := by
  apply (realHeckeCharacter_parameters X v h).unique
    (realHeckeCharacter_parameters X v h).exists.choose_spec
  refine ⟨rfl, fun x ↦ ?_⟩
  rw [principal_twist]
  simp [infinitePlaceRestriction]

private theorem zeta_meromorphic : MeromorphicOn completedRiemannZeta univ := by
  rw [show completedRiemannZeta = (fun z : ℂ ↦ completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) from
    funext completedRiemannZeta_eq]
  intro z _
  exact ((differentiable_completedZeta₀.analyticAt z).meromorphicAt.sub
    (analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt)).sub
    (analyticAt_const.meromorphicAt.div (analyticAt_const.sub analyticAt_id).meromorphicAt)

private theorem zeta_agrees (s : Complex.re ⁻¹' Ioi (1 : ℝ)) : L₀ s = completedHeckeL X s := by
  have hs : 1 < s.val.re := s.property
  have h0 : s.val ≠ 0 := by rintro h; norm_num [h] at hs
  have h1 : s.val ≠ 1 := by rintro h; simp [h] at hs
  have han : AnalyticAt ℂ completedRiemannZeta s.val := by
    rw [show completedRiemannZeta = (fun z : ℂ ↦ completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) from
      funext completedRiemannZeta_eq]
    exact ((differentiable_completedZeta₀.analyticAt _).sub (analyticAt_const.div analyticAt_id h0)).sub
      (analyticAt_const.div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr h1.symm))
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt zeta_meromorphic (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt,
    completedHeckeL_one_eq_dedekindZeta, InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one
      (Module.finrank_self ℚ), InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one
      (Module.finrank_self ℚ), pow_one, pow_zero, mul_one, dedekindZeta_rat_eq_riemannZeta hs,
    riemannZeta_def_of_ne_zero h0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)]

/-- The actual continued rational principal Hecke function is the meromorphic
normal form of Mathlib's completed zeta on the entire plane. -/
theorem continuedCompletedHeckeL_rat_one_eq_normalizedZeta : continuedCompletedHeckeL X = L₀ := by
  obtain ⟨hL, ha⟩ := continuedCompletedHeckeL_spec X
  have hZ := meromorphicNFOn_toMeromorphicNFOn completedRiemannZeta univ
  have hnear : continuedCompletedHeckeL X =ᶠ[𝓝[≠] (2 : ℂ)] L₀ := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦
      (ha ⟨z, hz⟩).trans (zeta_agrees ⟨z, hz⟩).symm
  have ho := meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp hnear)
  funext z
  have hz := (hL.meromorphicOn.sub hZ.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ z) ho
  exact (((hL (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hZ (mem_univ z))).mp
    (eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp hz))).eq_of_nhds

/-- The positive divisor used to index the rational strip trace agrees with
the divisor in the classical prime formula, including at the two poles. -/
theorem divisor_rat_principal_eq_zeta : MeromorphicOn.divisor (continuedCompletedHeckeL X) univ = d₀ := by
  rw [continuedCompletedHeckeL_rat_one_eq_normalizedZeta, zeta_meromorphic.divisor_of_toMeromorphicNFOn]

private theorem principal_poles : d₀ 0 = -1 ∧ d₀ 1 = -1 ∧ ∀ z, z ≠ 0 → z ≠ 1 → 0 ≤ d₀ z := by
  have hL := meromorphicNFOn_toMeromorphicNFOn completedRiemannZeta univ
  have hAgree := zeta_agrees
  have han := completedHeckeL_one_analyticOnNhd L₀ hL hAgree
  obtain ⟨t, ⟨_, h0, h1, _⟩, _⟩ := completedHeckeL_continuation_simplePoles X L₀ hL hAgree rfl
  have ht : t = 0 := by
    by_contra hn
    have hne : Complex.I * (t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hn)
    have hn1 : Complex.I * (t : ℂ) ≠ 1 := by
      intro he
      have := congrArg Complex.re he
      simp [Complex.mul_re] at this
    have hp := (han (Complex.I * (t : ℂ)) (by simp [hne, hn1])).meromorphicOrderAt_nonneg
    rw [h0] at hp
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hp
    exact (by decide : ¬ ((0 : ℤ) ≤ -1)) (WithTop.coe_le_coe.mp hp)
  subst t
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at h0 h1
  rw [← zeta_meromorphic.divisor_of_toMeromorphicNFOn]
  refine ⟨?_, ?_, fun z hz hz' ↦ ?_⟩
  · rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), h0]; rfl
  · rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), h1]; rfl
  · rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), WithTop.untop₀_nonneg]
    exact (han z (by simp [hz, hz'])).meromorphicOrderAt_nonneg

private theorem add_poles (H : ℝ → ℂ) {A : ℂ}
    (h : HasSum (fun z : ℂ ↦ (d₀ z : ℂ) * M(H, z)) A) :
    HasSum (fun z : {z : ℂ // 0 < d₀ z} ↦ (d₀ z.val : ℂ) * M(H, z.val)) (A + M(H, 0) + M(H, 1)) := by
  classical
  obtain ⟨h0, h1, hnon⟩ := principal_poles
  apply (hasSum_subtype_iff_indicator (s := {z : ℂ | 0 < d₀ z})
    (f := fun z : ℂ ↦ (d₀ z : ℂ) * M(H, z))).mpr
  refine ((h.add (hasSum_ite_eq 0 (M(H, 0)))).add (hasSum_ite_eq 1 (M(H, 1)))).congr_fun fun z ↦ ?_
  by_cases hz0 : z = 0
  · subst z
    simp [h0]
  by_cases hz1 : z = 1
  · subst z
    simp [h1]
  by_cases hp : 0 < d₀ z
  · simp [hp, hz0, hz1]
  · have hz := le_antisymm (le_of_not_gt hp) (hnon z hz0 hz1)
    simp [hz, hz0, hz1]

private theorem zeta_gamma {G : ℝ → ℂ} (hc : HasCompactSupport G) (hG : Continuous G)
    (hs : tsupport G ⊆ Ioi 0) :
    positiveLogGammaIntegral (1 / 2) 0 G = M(G, 0) +
      ∫ x in Ioi (0 : ℝ), G x / ((Real.exp (2 * x) : ℂ) - 1) := by
  let A (x : ℝ) := G x / ((Real.exp (2 * x) : ℂ) - 1)
  have hi : Integrable A := by
    apply (integrableOn_iff_integrable_of_support_subset (s := tsupport G) ?_).mp
    · apply ContinuousOn.integrableOn_compact hc
      apply hG.continuousOn.div (by fun_prop)
      intro x hx
      exact sub_ne_zero.mpr (by exact_mod_cast
        (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) (hs hx))).ne')
    · exact fun x hx ↦ subset_tsupport _ (fun h ↦ hx (by simp [A, h]))
  have h0 : M(G, 0) = ∫ x in Ioi (0 : ℝ), G x := by
    simp only [bilateralLaplace, zero_mul, Complex.exp_zero, mul_one]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_contra hn
      exact hx (hs (subset_tsupport _ hn)))).symm
  rw [h0, positiveLogGammaIntegral, ← integral_add (hG.integrable_of_hasCompactSupport hc).integrableOn
    hi.integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hE : (Real.exp (2 * x) : ℂ) ≠ 1 := by exact_mod_cast
    (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) (show 0 < x from hx))).ne'
  have hne : (Real.exp (2 * x) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, show -x / (1 / 2) = -(2 * x) by ring,
    Real.exp_neg, Complex.ofReal_inv, A]
  field_simp [sub_ne_zero.mpr hE, hne]
  ring

/-- Paper: §12.3, p. 514 and Theorem B.4.2.2, p. 616. The uncentered Laplace
transform, counted with full positive zeta multiplicity, has the pole term at
one, the signed von Mangoldt samples, and the real-place remainder. -/
theorem hasSum_zetaZeros_positiveLog (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ioi 0) :
    HasSum (fun z : {z : ℂ // 0 < d₀ z} ↦ (d₀ z.val : ℂ) * M(G, z.val))
      (M(G, 1) - (∑' n : ℕ, (Λ n : ℂ) * G (Real.log n)) -
        ∫ x in Ioi (0 : ℝ), G x / ((Real.exp (2 * x) : ℂ) - 1)) := by
  have h := hasSum_heckeExplicitFormula_positiveLog X G hG hc hs L₀
    (meromorphicNFOn_toMeromorphicNFOn _ _) zeta_agrees
  rw [zeta_meromorphic.divisor_of_toMeromorphicNFOn] at h
  have hp (j : V × ℕ) : positiveLogPrimeTerm X G j =
      (Real.log q(j.1) : ℂ) * G (((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)) := by
    simp [positiveLogPrimeTerm, principal_unramified, principal_value]
  simp_rw [hp] at h
  rw [prime_power_sum] at h
  have ha (w : InfinitePlace ℚ) : positiveLogArchTerm X G w = positiveLogGammaIntegral (1 / 2) 0 G := by
    rw [positiveLogArchTerm, dite_eq_left (IsTotallyReal.isReal w)]
    simp only [principal_parameters, Fin.val_zero, Nat.cast_zero, add_zero]
  simp_rw [ha] at h
  have hz := add_poles G h
  rw [zeta_gamma hc hG.continuous hs] at hz
  convert hz using 1
  simp
  ring

end RiemannMasullo
