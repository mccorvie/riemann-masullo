module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Comparing the sharp orbital trace and the global geometric diagonal

The support cutoff in the first paragraph of p. 520 removes every finite-place
restriction outside the chosen set. On a strip containing the critical strip,
the full explicit formula then identifies the corrected sharp orbital limit
with the Haar integral of the global geometric diagonal, given its projective kernel.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSpectralQuotientPolynormableSec3 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instSIdeleT2Sec4

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "volS" => (((sLocalNormOneQuotientMeasure F S) univ).toReal : ℂ)
local notation "volF" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "normR(" g ")" => (((ideleClassNorm F g).val : ℝ))
local notation "rootS(" g ")" => (Real.sqrt (((sIdeleNorm F S g).val : ℝ)) : ℂ)
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archPV(" a ")" => (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w))
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finPV(" v "," b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "pole(" φ "," v ")" =>
  modulatedFourierMellin m𝔽 univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist 1 v)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripK(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))
local notation "diag(" hα "," hs "," φ "," hK "," U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x, x))

/-- Paper: Theorem 12.5.1.1, p. 520, first paragraph. If the global test vanishes at norm
one and its support has norm and inverse norm strictly below the residue cardinality of a
finite place, its entire restriction to this place is zero. -/
theorem traceComparison_finiteRestriction_eq_zero
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (v : V) {B : ℝ}
    (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hv : B ≤ (v.asIdeal.absNorm : ℝ)) (u : (v.adicCompletion F)ˣ) :
    φ.val (finiteClass(v) u) = 0 := by
  let c := finiteClass(v) u
  let q : ℝ := v.asIdeal.absNorm
  let k := WithZero.log (Valued.v u.val)
  have hn : normR(c) = ‖u.val‖ := by
    simp only [c, ideleClassNorm_ofAdicCompletion]
    rfl
  have hq : 1 ≤ q := by
    change (1 : ℝ) ≤ (v.asIdeal.absNorm : ℝ)
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le
  have hqpos := lt_of_lt_of_le zero_lt_one hq
  have hz : ‖u.val‖ = q ^ k := norm_adicCompletion_eq_zpow F v u.ne_zero
  change φ.val c = 0
  by_contra hne
  obtain ⟨hlt, hinv⟩ := hB c (subset_tsupport _ hne)
  rw [hn, hz] at hlt hinv
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h := zpow_le_zpow_right₀ hq (show k ≤ -1 by omega)
    rw [zpow_neg_one] at h
    exact (not_lt_of_ge hv) ((le_inv_comm₀ hqpos (zpow_pos hqpos k)).mpr h |>.trans_lt hinv)
  · have heq : ideleClassNorm F c = 1 := by
      apply Units.ext
      apply NNReal.eq
      change normR(c) = 1
      simpa only [hk, zpow_zero] using hn.trans hz
    exact hne (hφ ⟨c, heq⟩)
  · have h := zpow_le_zpow_right₀ hq (show (1 : ℤ) ≤ k by omega)
    rw [zpow_one] at h
    exact (not_lt_of_ge hv) (h.trans_lt hlt)

private theorem traceComparison_volume_ne_zero :
    (volS : ℂ) ≠ 0 := by
  let G := (sIdeleQuotientNorm F S).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  refine Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩)
  · exact isOpen_univ.measure_ne_zero μ univ_nonempty
  · exact measure_ne_top μ univ

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519 and (12.5.1.4), p. 520. For a strip of half-width
at least one half, the normalized sharp orbital masses, corrected by the two *local* dilation
moments, converge to the actual global geometric Haar diagonal. The finite set is chosen
by the radial support bound in the first paragraph of p. 520.
Deviation: This compares the sharp masses. The projective kernel used to define the global
diagonal is an input. -/
theorem sLocalTraceSharpMass_tendsto_globalDiagonal_of_half_le
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let P := (∫ g : Iₛ, f.val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, f.val g / rootS(g) ∂μₛ
    let D := diag((one_half_pos.trans_le hα).le, hs, φ, hK, U)
    Integrable D μ𝔽 ∧
      Tendsto (fun R : ℝ ↦ volF / volS * ((∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) - P))
        atTop (𝓝 (∫ x, D x ∂μ𝔽)) := by
  classical
  intro P D
  obtain ⟨a, b, M, ha, hb, hM, hlim⟩ :=
    sLocalTraceSharpMass_asymptotic φ hPic hRam hOutside f hLift
  let b' : finTest := fun v ↦ if h : v ∈ S then b ⟨v, h⟩ else 0
  have hb' (v : V) (u : (v.adicCompletion F)ˣ) : (b' v).val u = φ.val (finiteClass(v) u) := by
    by_cases h : v ∈ S
    · simpa only [b', dite_eq_left h] using hb ⟨v, h⟩ u
    · rw [traceComparison_finiteRestriction_eq_zero φ hφ v hB (hS v h) u]
      simp only [b', dite_eq_right h]
      rfl
  have hsum : (∑' v : V, finPV(v, b' v)) = ∑ v : S, finPV(v.val, b v) := by
    rw [tsum_eq_sum (s := S) (fun v hv ↦ by simp [b', hv]), ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun v _ ↦ by simp [b', v.property]
  have hφ1 : φ.val 1 = 0 := hφ 1
  have hsharp : Tendsto (fun R : ℝ ↦ ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) atTop
      (𝓝 (volS * (archPV(a) + ∑ v : S, finPV(v.val, b v)))) := by
    simp only [hφ1, mul_zero, zero_mul, sub_zero] at hlim
    exact hlim.congr' (hM.mono fun R h ↦ h.tsum_eq.symm)
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  let hpos := one_half_pos.trans_le hα
  let T := (⟨_, spectralStripConvolution_nuclear_of_projectiveKernel hpos.le hs₁(hs) φ hK⟩ :
    nuclearEndomorphisms (spectralSobolevQuotient F (1 / 2) (hStrip(hpos.le)) hs₀(hs)))
  obtain ⟨hD, _, hGeom⟩ := hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hpos hs
    hK U hU hBorel
  have hSpec := (spectralStripConvolution_trace (F := F) (1 / 2) χ hχ hpos.le hs₁(hs) φ T rfl).2
  have hdiag : -(∫ x, D x ∂μ𝔽) = hilbertTrace T := hGeom.unique hSpec
  have hfull := spectralStripTrace_eq_localTerms_of_half_le φ hα hs₁(hs) a b' ha hb' T rfl
  rw [hsum] at hfull
  have hpole : volF * P = volS * (pole(φ, (1 / 2)) + pole(φ, (-1 / 2))) :=
    sLocalTraceLift_global_polar_sum hPic φ hOutside f hLift
  have hvol : (volS : ℂ) ≠ 0 := traceComparison_volume_ne_zero
  have hconstant : volF / volS * (volS * (archPV(a) + ∑ v : S, finPV(v.val, b v)) - P) =
      ∫ x, D x ∂μ𝔽 := by
    field_simp [hvol]
    linear_combination -hpole + volS * hdiag + volS * hfull
  exact ⟨hD, hconstant ▸ (hsharp.sub_const P).const_mul (volF / volS)⟩

end RiemannMasullo
