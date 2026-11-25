module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels

/-! # Comparing the sharp orbital trace and the global geometric diagonal

At each outside place the radial support bound on p. 520 and outside-unit invariance
identify the test with its identity value times the integer-unit indicator. Its normalized
principal value vanishes away from the different. On a strip containing the critical strip,
the full explicit formula identifies the log-subtracted sharp orbital limit, corrected by
the two local polar moments, with the Haar integral of the centered geometric diagonal.
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

/-- The radial support at a prescribed place can meet only its valuation-zero shell. -/
private theorem traceComparison_valuation_eq_zero
    (φ : BruhatCompactSupport C𝔽) (v : V) {B : ℝ}
    (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hv : B ≤ (v.asIdeal.absNorm : ℝ)) (u : (v.adicCompletion F)ˣ)
    (hne : φ.val (finiteClass(v) u) ≠ 0) : WithZero.log (Valued.v u.val) = 0 := by
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
  obtain ⟨hlt, hinv⟩ := hB c (subset_tsupport _ hne)
  rw [hn, hz] at hlt hinv
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h := zpow_le_zpow_right₀ hq (show k ≤ -1 by omega)
    rw [zpow_neg_one] at h
    exact ((not_lt_of_ge hv) ((le_inv_comm₀ hqpos (zpow_pos hqpos k)).mpr h |>.trans_lt hinv)).elim
  · exact hk
  · have h := zpow_le_zpow_right₀ hq (show (1 : ℤ) ≤ k by omega)
    rw [zpow_one] at h
    exact ((not_lt_of_ge hv) (h.trans_lt hlt)).elim

/-- Paper: Theorem 12.5.1.1, p. 520, first paragraph. If the global test vanishes at norm
one and its support has norm and inverse norm strictly below the residue cardinality of a
finite place, its entire restriction to this place is zero. -/
theorem traceComparison_finiteRestriction_eq_zero
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (v : V) {B : ℝ}
    (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hv : B ≤ (v.asIdeal.absNorm : ℝ)) (u : (v.adicCompletion F)ˣ) :
    φ.val (finiteClass(v) u) = 0 := by
  by_contra hne
  have hk := traceComparison_valuation_eq_zero φ v hB hv u hne
  have hnorm : ‖u.val‖ = 1 := by
    simp only [norm_adicCompletion_eq_zpow F v u.ne_zero, hk, zpow_zero]
  apply hne (hφ ⟨_, ?_⟩)
  apply Units.ext
  apply NNReal.eq
  change normR(finiteClass(v) u) = 1
  have hn : normR(finiteClass(v) u) = ‖u.val‖ := by
    simp only [ideleClassNorm_ofAdicCompletion]
    rfl
  exact hn.trans hnorm

/-- A local integer unit at a place outside S is a complementary integral idele. -/
private theorem traceComparison_ofAdicCompletion_mem_outside
    (v : V) (hv : v ∉ S) (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ (HeightOneSpectrum.adicCompletionIntegers F v).units) :
    IdeleGroup.ofAdicCompletion (𝓞 F) F v u ∈ outsideIntegralIdeleUnits F S := by
  classical
  let O := fun w : V ↦ w.adicCompletionIntegers F
  rw [mem_outsideIntegralIdeleUnits_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro w hw
    change RestrictedProduct.mulSingle O v u.val w = 1
    exact RestrictedProduct.mulSingle_eq_of_ne _ _ (ne_of_mem_of_not_mem hw hv)
  · intro w _
    change RestrictedProduct.mulSingle O v u.val w ∈ O w ∧
      RestrictedProduct.mulSingle O v u⁻¹.val w ∈ O w
    by_cases h : w = v
    · subst w
      rw [RestrictedProduct.mulSingle_eq_same, RestrictedProduct.mulSingle_eq_same]
      exact ⟨hu.1, hu.2⟩
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, RestrictedProduct.mulSingle_eq_of_ne _ _ h]
      exact ⟨(O w).one_mem, (O w).one_mem⟩

/-- Paper: Theorem 12.5.1.1, p. 520 and (B.4.4.22), p. 625. At a prescribed outside place
whose residue cardinality bounds the radial support, the restriction of an outside-unit
invariant test is its value at the identity times the integer-unit indicator. -/
theorem traceComparison_finiteRestriction_eq_unitsIndicator
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (v : V) (hv : v ∉ S) {B : ℝ}
    (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hq : B ≤ (v.asIdeal.absNorm : ℝ)) (u : (v.adicCompletion F)ˣ) :
    φ.val (finiteClass(v) u) = φ.val 1 *
      ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _).indicator (fun _ ↦ (1 : ℂ)) u := by
  classical
  by_cases hu : u ∈ (HeightOneSpectrum.adicCompletionIntegers F v).units
  · rw [indicator_of_mem hu, mul_one]
    let a := IdeleGroup.ofAdicCompletion (𝓞 F) F v u
    exact (congrArg φ.val (mul_one (finiteClass(v) u)).symm).trans
      (hOutside ⟨a, traceComparison_ofAdicCompletion_mem_outside v hv u hu⟩ 1)
  · rw [indicator_of_notMem hu, mul_zero]
    by_contra hne
    have hk := traceComparison_valuation_eq_zero φ v hB hq u hne
    apply hu
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      ← WithZero.exp_log (Valued.v.ne_zero_iff.mpr u.ne_zero), hk, WithZero.exp_zero]

/-- Paper: (B.4.4.22), p. 625 and Theorem 12.5.1.1, p. 520. The normalized finite principal
value of an arbitrary outside-unit invariant test at a prescribed place beyond its radial
support equals its identity value times the local different correction. -/
theorem traceComparison_finitePrincipalValue_eq_different
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (v : V) (hv : v ∉ S) {B : ℝ}
    (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hq : B ≤ (v.asIdeal.absNorm : ℝ)) (b : BruhatCompactSupport (v.adicCompletion F)ˣ)
    (hb : ∀ u, b.val u = φ.val (finiteClass(v) u)) :
    finPV(v, b) = -φ.val 1 *
      (((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) : ℝ) : ℂ) := by
  obtain ⟨d, hd, hPV⟩ := finiteConnesWeilPrincipalValue_unitsIndicator v
  have heq : b = φ.val 1 • d := by
    refine Subtype.ext (funext fun u ↦ ?_)
    change b.val u = φ.val 1 * d.val u
    rw [hb, hd]
    exact traceComparison_finiteRestriction_eq_unitsIndicator φ hOutside v hv hB hq u
  calc
    finPV(v, b) = φ.val 1 * finPV(v, d) := by rw [heq, map_smul, smul_eq_mul, mul_left_comm]
    _ = _ := by rw [hPV]; ring

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

local notation "stripQ(" hα ", " hs ")" =>
  spectralSobolevQuotient F (1 / 2) (hStrip(hα)) (le_of_lt (zero_lt_one.trans hs))
local notation "stripAction(" hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) (1 / 2) (hStrip(hα)) (le_of_lt (zero_lt_one.trans hs)) φ

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519, and (12.5.1.4), p. 520. After subtracting the
identity logarithm and both local dilation moments, the normalized sharp orbital mass converges
to minus the wide-strip quotient trace for an arbitrary compact global test.
Deviation: The strip contains the critical strip. The nuclear operator represents the actual
quotient convolution at Sobolev order greater than one. -/
theorem sLocalTraceSharpMass_logSubtracted_tendsto_neg_spectralTrace_of_half_le
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 1 < s)
    (T : nuclearEndomorphisms stripQ((one_half_pos.trans_le hα).le, hs))
    (hT : T.val = stripAction((one_half_pos.trans_le hα).le, hs, φ)) :
    let P := (∫ g : Iₛ, f.val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, f.val g / rootS(g) ∂μₛ
    Tendsto (fun R : ℝ ↦ volF / volS *
      ((∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) - volS * φ.val 1 * (Real.log R : ℂ) - P))
      atTop (𝓝 (-hilbertTrace T)) := by
  classical
  intro P
  obtain ⟨a, b, M, ha, hb, hM, hlim⟩ :=
    sLocalTraceSharpMass_asymptotic φ hPic hRam hOutside f hLift
  let b' : finTest := fun v ↦ (idelicExplicitFormula_finiteTestMap v).choose φ
  have hb' (v : V) (u : (v.adicCompletion F)ˣ) : (b' v).val u = φ.val (finiteClass(v) u) :=
    (idelicExplicitFormula_finiteTestMap v).choose_spec φ u
  have hvan (v : V) (hv : v ∉ S) : finPV(v, b' v) = 0 := by
    have hdiff : multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0 :=
      multiplicity_eq_zero_of_not_dvd fun h ↦ hv (hRam v (Ideal.dvd_iff_le.mp h))
    rw [traceComparison_finitePrincipalValue_eq_different φ hOutside v hv hB (hS v hv) _ (hb' v), hdiff]
    simp
  have hsum : (∑' v : V, finPV(v, b' v)) = ∑ v : S, finPV(v.val, b v) := by
    rw [tsum_eq_sum (s := S) hvan, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have heq : b' v.val = b v := Subtype.ext (funext fun u ↦ (hb' v.val u).trans (hb v u).symm)
    rw [heq]
  have hsharp : Tendsto (fun R : ℝ ↦ (∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) -
      volS * φ.val 1 * (Real.log R : ℂ)) atTop
      (𝓝 (volS * (archPV(a) + ∑ v : S, finPV(v.val, b v)))) :=
    hlim.congr' (hM.mono fun _ h ↦ congrArg (fun z : ℂ ↦ z - _) h.tsum_eq.symm)
  have hfull := spectralStripTrace_eq_localTerms_of_half_le φ hα hs a b' ha hb' T hT
  rw [hsum] at hfull
  have hpole : volF * P = volS * (pole(φ, (1 / 2)) + pole(φ, (-1 / 2))) :=
    sLocalTraceLift_global_polar_sum hPic φ hOutside f hLift
  have hvol : (volS : ℂ) ≠ 0 := traceComparison_volume_ne_zero
  have hconstant : volF / volS * (volS * (archPV(a) + ∑ v : S, finPV(v.val, b v)) - P) =
      -hilbertTrace T := by
    field_simp [hvol]
    linear_combination -hpole + volS * hfull
  exact hconstant ▸ (hsharp.sub_const P).const_mul (volF / volS)

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519, and (12.5.1.4), p. 520. On a strip containing
the critical strip, the normalized sharp orbital mass, after subtracting its identity logarithm
and the local polar moments, converges to the Haar integral of the centered geometric diagonal.
Deviation: The test may take arbitrary values on norm-one classes. The tensor gives convolution
after spectral projection, and the geometric diagonal is centered at the test value at one. -/
theorem sLocalTraceSharpMass_logSubtracted_tendsto_centeredGlobalDiagonal_of_half_le
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 1 < s)
    (hK : ∃ K, sobolevProjectiveKernelOperator (F := F) (one_half_pos.trans_le hα).le
      (zero_le_one.trans hs.le) K =
        (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip((one_half_pos.trans_le hα).le))
          (zero_le_one.trans hs.le) φ).comp
        (spectralProjection (F := F) (1 / 2) (one_half_pos.trans_le hα).le (zero_le_one.trans hs.le)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let P := (∫ g : Iₛ, f.val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, f.val g / rootS(g) ∂μₛ
    let D := fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) (one_half_pos.trans_le hα).le hs φ hK) (x, x)
    Integrable (fun x ↦ D x - φ.val 1) μ𝔽 ∧
      Tendsto (fun R : ℝ ↦ volF / volS *
        ((∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) - volS * φ.val 1 * (Real.log R : ℂ) - P))
        atTop (𝓝 (∫ x, D x - φ.val 1 ∂μ𝔽)) := by
  intro P D
  obtain ⟨hD, htrace⟩ := integral_centered_smoothenedStripGeometricKernel_diagonal
    (one_half_pos.trans_le hα).le hs φ hK U hU hBorel
  refine ⟨hD, ?_⟩
  rw [show (∫ x, D x - φ.val 1 ∂μ𝔽) = _ from htrace]
  exact sLocalTraceSharpMass_logSubtracted_tendsto_neg_spectralTrace_of_half_le
    φ hPic hRam hOutside hB hS f hLift hα hs _ rfl

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
  have hφ1 : φ.val 1 = 0 := hφ 1
  simpa only [hφ1, mul_zero, zero_mul, sub_zero] using
    sLocalTraceSharpMass_logSubtracted_tendsto_centeredGlobalDiagonal_of_half_le
      φ hPic hRam hOutside hB hS f hLift hα hs₁(hs) hK U hU hBorel

/-- Paper: Theorems 12.4.1.1 and 12.5.1.1, pp. 514 and 520. Choose one S-local lift of an
arbitrary compact global test. For every strip containing the critical strip and every Sobolev
order greater than one, its log-subtracted sharp orbital limit equals both the Haar integral of
the centered geometric diagonal and minus the full quotient trace.
Deviation: The limit concerns sharp orbital masses. The projective kernel on projected inputs
exists by the weighted-adjoint construction, and both polar moments come from the chosen lift. -/
theorem exists_sLocalTraceLift_logSubtracted_sharpMass_eq_centeredWideDiagonal
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ)) :
    ∃ f : BruhatCompactSupport Iₛ,
      (∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) ∧
      ∀ {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 1 < s)
        (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)),
        let hK := stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1 / 2)
          (one_half_pos.trans_le hα).le (zero_le_one.trans hs.le) φ
        let T : nuclearEndomorphisms stripQ((one_half_pos.trans_le hα).le, hs) :=
          ⟨stripAction((one_half_pos.trans_le hα).le, hs, φ),
            spectralStripConvolution_nuclear_of_projectiveKernel (one_half_pos.trans_le hα).le hs φ hK⟩
        let P := (∫ g : Iₛ, f.val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, f.val g / rootS(g) ∂μₛ
        let D := fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
          (globalStripGeometricKernel (F := F) (1 / 2) (one_half_pos.trans_le hα).le hs φ hK) (x, x)
        Integrable (fun x ↦ D x - φ.val 1) μ𝔽 ∧
          (∫ x, D x - φ.val 1 ∂μ𝔽) = -hilbertTrace T ∧
          Tendsto (fun R : ℝ ↦ volF / volS *
            ((∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) - volS * φ.val 1 * (Real.log R : ℂ) - P))
            atTop (𝓝 (∫ x, D x - φ.val 1 ∂μ𝔽)) := by
  let hlift := exists_sLocalTraceLift (F := F) (S := S) hPic φ hOutside
  let f := hlift.choose
  have hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))) :=
    hlift.choose_spec
  refine ⟨f, hLift, ?_⟩
  intro α s hα hs U hU hBorel hK T P D
  have hgeom := integral_centered_smoothenedStripGeometricKernel_diagonal
    (one_half_pos.trans_le hα).le hs φ hK U hU hBorel
  have horbit := sLocalTraceSharpMass_logSubtracted_tendsto_centeredGlobalDiagonal_of_half_le
    φ hPic hRam hOutside hB hS f hLift hα hs hK U hU hBorel
  exact ⟨hgeom.1, hgeom.2, horbit.2⟩

end RiemannMasullo
