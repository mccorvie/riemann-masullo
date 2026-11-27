module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels

/-! # The trace comparison at a fixed set of places

For a fixed finite set and any positive strip width, the difference between the global
geometric diagonal and the pole-subtracted sharp orbital limit has an arithmetic term
from the omitted places and a spectral term from the omitted zero multiplicities.
These two terms determine the joint cutoff limit a local quotient diagonal must satisfy.
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

local notation "localScale(" v ")" => (Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ)
local notation "orbitalIntegrand(" v "," φ ")" => (fun u : ((v : V).adicCompletion F)ˣ ↦
  (φ : BruhatCompactSupport C𝔽).val (finiteClass(v) u) * (Real.sqrt ‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ))
local notation "orbitalTerm(" v "," φ ")" => ((localScale(v) : ℂ) *
  ∫ u, orbitalIntegrand(v, φ) u ∂finiteLocalMultiplicativeTamagawaMeasure F v)

/-- At a test vanishing at one, Appendix B.4 identifies the finite principal values
with ordinary orbital integrals, only finitely many of which are nonzero. -/
private theorem traceComparison_finiteOrbitalTerms
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) :
    ∃ b : finTest, (∀ v u, (b v).val u = φ.val (finiteClass(v) u)) ∧
      (∀ v, finPV(v, b v) = orbitalTerm(v, φ)) ∧ HasFiniteSupport (fun v : V ↦ orbitalTerm(v, φ)) := by
  choose B hB using fun v : V ↦ idelicExplicitFormula_finiteTestMap (F := F) v
  let b : finTest := fun v ↦ B v φ
  have hb (v : V) (u) : (b v).val u = φ.val (finiteClass(v) u) := hB v φ u
  have hterm (v : V) : finPV(v, b v) = orbitalTerm(v, φ) := by
    have hz : (b v).val 1 = 0 := by simpa only [hb, map_one] using hφ
    rw [(finiteConnesWeilPrincipalValue_of_apply_one_zero v (b v) hz).2]
    simp_rw [hb]
  refine ⟨b, hb, hterm, ?_⟩
  refine (idelicExplicitFormula_finite_support φ b hb).subset fun v hv ↦ ?_
  intro hz
  apply hv
  change orbitalTerm(v, φ) = 0
  change finiteConnesWeilPrincipalValue v 1 (b v) = 0 at hz
  rw [← hterm v, hz, mul_zero]

open scoped ComplexOrder

/-- Off the identity the finite-place orbital density is strictly positive. Thus an
integral with a nonnegative test can vanish only if the restriction is identically zero. -/
private theorem traceComparison_nonnegativeOrbitalTerm (φ : BruhatCompactSupport C𝔽)
    (hφ : φ.val 1 = 0) (v : V) (hpos : ∀ u, 0 ≤ φ.val (finiteClass(v) u)) :
    0 ≤ (orbitalTerm(v, φ)).re ∧
      ((orbitalTerm(v, φ)).re = 0 → ∀ u, φ.val (finiteClass(v) u) = 0) := by
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  obtain ⟨B, hB⟩ := idelicExplicitFormula_finiteTestMap (F := F) v
  have h1 : (B φ).val 1 = 0 := by simpa only [hB, map_one] using hφ
  have hi := (finiteConnesWeilPrincipalValue_of_apply_one_zero v (B φ) h1).1
  simp_rw [hB] at hi
  let k (u : (v.adicCompletion F)ˣ) := (orbitalIntegrand(v, φ) u).re
  have hk (u) : k u = (φ.val (finiteClass(v) u)).re * Real.sqrt ‖u.val‖ / ‖1 - u.val‖ :=
    (Complex.div_ofReal_re _ _).trans (by rw [Complex.re_mul_ofReal])
  have hk0 (u) : 0 ≤ k u := by
    rw [hk]
    exact div_nonneg (mul_nonneg (Complex.nonneg_iff.mp (hpos u)).1 (Real.sqrt_nonneg _))
      (norm_nonneg _)
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hscale : 0 < localScale(v) := by
    apply div_pos (Real.log_pos hq)
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos (zero_lt_one.trans hq) _))
  have hre : (orbitalTerm(v, φ)).re = localScale(v) * ∫ u, k u ∂μ :=
    (Complex.re_ofReal_mul _ _).trans (congrArg (localScale(v) * ·) (integral_re hi).symm)
  rw [hre]
  refine ⟨mul_nonneg hscale.le (integral_nonneg hk0), fun hz ↦ ?_⟩
  have hzero := (integral_eq_zero_iff_of_nonneg hk0 hi.re).mp
    ((mul_eq_zero.mp hz).resolve_left hscale.ne')
  have hc : Continuous (fun u ↦ φ.val (finiteClass(v) u)) :=
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)).comp
      (continuous_ideleClass_ofAdicCompletion F v)
  apply congrFun ((hc.ae_eq_iff_eq μ continuous_zero).mp ?_)
  filter_upwards [hzero] with u hu
  by_cases hu1 : u = 1
  · simpa only [hu1, map_one, Pi.zero_apply] using hφ
  have hd : ‖1 - u.val‖ ≠ 0 := norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (fun h ↦ hu1 (Units.ext h.symm)))
  have hn := (div_eq_zero_iff.mp ((hk u).symm.trans hu)).resolve_right hd
  have hr := (mul_eq_zero.mp hn).resolve_right (Real.sqrt_pos.mpr (norm_pos_iff.mpr u.ne_zero)).ne'
  exact norm_eq_zero.mp ((Complex.re_eq_norm.mpr (hpos u)).symm.trans hr)

/-- Paper: §12.3, p. 514 and Theorem 12.5.1.1, p. 520. If the omitted local
restrictions are real and nonnegative, their total correction vanishes exactly when
every omitted restriction vanishes pointwise. Only vanishing at the identity is needed. -/
theorem traceComparison_omittedTerms_eq_zero_iff (φ : BruhatCompactSupport C𝔽)
    (hφ : φ.val 1 = 0) (hpos : ∀ v ∉ S, ∀ u, 0 ≤ φ.val (finiteClass(v) u)) :
    (∑' v : {v : V // v ∉ S}, orbitalTerm(v.val, φ)) = 0 ↔
      ∀ v ∉ S, ∀ u, φ.val (finiteClass(v) u) = 0 := by
  obtain ⟨_, _, _, hfin⟩ := traceComparison_finiteOrbitalTerms φ hφ
  have hs : Summable (fun v : {v : V // v ∉ S} ↦ orbitalTerm(v.val, φ)) :=
    (summable_of_hasFiniteSupport hfin).subtype _
  have hlocal (v : {v : V // v ∉ S}) :=
    traceComparison_nonnegativeOrbitalTerm φ hφ v.val (hpos v.val v.property)
  constructor
  · intro hz v hv
    have hzero := Complex.hasSum_re (hz ▸ hs.hasSum)
    exact (hlocal ⟨v, hv⟩).2 (le_antisymm
      (le_hasSum hzero ⟨v, hv⟩ fun w _ ↦ (hlocal w).1) (hlocal ⟨v, hv⟩).1)
  · intro hz
    have h (v : {v : V // v ∉ S}) : orbitalTerm(v.val, φ) = 0 := by
      simp only [hz v.val v.property, zero_mul, zero_div, integral_zero, mul_zero]
    simp only [h, tsum_zero]

/-- Paper: §12.3, p. 514, and Theorem 12.5.1.1, p. 520. For a fixed finite set,
the global Haar diagonal on a wide strip equals the normalized, pole-subtracted sharp
orbital limit plus the global norm-one volume times the sum of ordinary local integrals
over the omitted places. The sum has finite support.
Deviation: The finite set need not meet the radial support bound on p. 520. -/
theorem sLocalTraceSharpMass_tendsto_globalDiagonal_sub_omitted
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let P := (∫ g : Iₛ, f.val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, f.val g / rootS(g) ∂μₛ
    let D := diag((one_half_pos.trans_le hα).le, hs, φ, hK, U)
    Integrable D μ𝔽 ∧
      Tendsto (fun R : ℝ ↦ volF / volS * ((∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) - P))
        atTop (𝓝 ((∫ x, D x ∂μ𝔽) - volF * ∑' v : {v : V // v ∉ S}, orbitalTerm(v.val, φ))) := by
  classical
  intro P D
  obtain ⟨a, b, M, ha, hb, hM, hlim⟩ :=
    sLocalTraceSharpMass_asymptotic φ hPic hRam hOutside f hLift
  obtain ⟨b', hb', hterm, hsum⟩ := traceComparison_finiteOrbitalTerms φ (hφ 1)
  have heq (v : S) : b' v.val = b v :=
    Subtype.ext (funext fun u ↦ (hb' v.val u).trans (hb v u).symm)
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
  have hinside (v : S) : orbitalTerm(v.val, φ) = finPV(v.val, b v) := by
    rw [← hterm, heq]
  have hsplit := (summable_of_hasFiniteSupport hsum).sum_add_tsum_compl (s := S)
  rw [← Finset.sum_coe_sort] at hsplit
  rw [tsum_congr hterm, ← hsplit, Finset.sum_congr rfl (fun v _ ↦ hinside v)] at hfull
  have hpole : volF * P = volS * (pole(φ, (1 / 2)) + pole(φ, (-1 / 2))) :=
    sLocalTraceLift_global_polar_sum hPic φ hOutside f hLift
  have hvol : (volS : ℂ) ≠ 0 := traceComparison_volume_ne_zero
  have hconstant : volF / volS * (volS * (archPV(a) + ∑ v : S, finPV(v.val, b v)) - P) =
      (∫ x, D x ∂μ𝔽) - volF * ∑' v : {v : V // v ∉ S}, orbitalTerm(v.val, φ) := by
    field_simp [hvol]
    linear_combination -hpole + volS * hdiag + volS * hfull
  exact ⟨hD, hconstant ▸ (hsharp.sub_const P).const_mul (volF / volS)⟩

/-- Paper: §12.3, p. 514, and (12.5.1.4), p. 520. At a positive width, the difference
between the global diagonal and the normalized, pole-subtracted sharp orbital limit is
the sum of the Mellin terms lost from width one half, with the actual edge multiplicities,
and the finite-place integrals outside the chosen set. For integrable local diagonals the
joint cutoff comparison is equivalent to recovering this same correction relative to the
sharp masses.
Reconstruction: Subtract the two closed-strip diagonal formulas on p. 520 and split the
finite-place sum in (12.4.1.27) on p. 519 at the chosen set. -/
theorem sLocalTrace_tendsto_globalDiagonal_iff_sharp_correction
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hK : stripK(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (z : PontryaginDual C₁ × ℝ × ℝ) :=
      meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (shift (1 / 2 + z.2.1) z.2.2)
    let retained (β : ℝ) := {z | z.2.1 ∈ Icc (-β) β ∧ 0 < order z}.indicator (fun z ↦
      (spectralStripMultiplicity β s z.2.1 (order z).untop₀.toNat : ℂ) *
        modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one⟩
          μ𝔽 φ.val (ideleClassNormTwist (χ z.1) (shift z.2.1 z.2.2)))
    let loss := fun z ↦ retained (1 / 2) z - retained α z
    let P := (∫ g : Iₛ, f.val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, f.val g / rootS(g) ∂μₛ
    let M (R : ℝ) := ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R
    let A (m : ℂ) := volF / volS * (m - P)
    let G := ∫ x, diag(hα.le, hs, φ, hK, U) x ∂μ𝔽
    let E := (∑' z, loss z) + volF * ∑' v : {v : V // v ∉ S}, orbitalTerm(v.val, φ)
    Summable (fun z ↦ ‖loss z‖) ∧ Tendsto (fun R ↦ A (M R)) atTop (𝓝 (G - E)) ∧
      ∀ d : ℝ × ℝ → (SIdeleQuotient F S →₁[sLocalQuotientTamagawaMeasure F S] ℂ),
        let I (p : ℝ × ℝ) := ∫ x, d p x ∂sLocalQuotientTamagawaMeasure F S
        Tendsto (fun p ↦ A (I p)) (atTop ×ˢ atTop) (𝓝 G) ↔
          Tendsto (fun p ↦ volF / volS * (I p - M (p.1 * p.2))) (atTop ×ˢ atTop) (𝓝 E) := by
  intro shift order retained loss P M A G E
  have hsum {β : ℝ} (hβ : 0 < β) (K : stripK(hβ.le, hs, φ)) :
      HasSum (retained β) (-(∫ x, diag(hβ.le, hs, φ, K, U) x ∂μ𝔽)) :=
    hasSum_subtype_iff_indicator.mp
      (hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hβ hs K U hU hBorel).2.2
  have hhalf : stripK(one_half_pos.le, hs, φ) :=
    stripTestAction_spectralProjection_has_projectiveKernel (1 / 2) one_half_pos.le hs₀(hs) φ
  have hloss := (hsum one_half_pos hhalf).sub (hsum hα hK)
  have hlim := (sLocalTraceSharpMass_tendsto_globalDiagonal_sub_omitted φ hφ hPic hRam hOutside
    f hLift (le_refl (1 / 2 : ℝ)) hs hhalf U hU hBorel).2
  have heq : G - ∑' z, loss z = ∫ x, diag(one_half_pos.le, hs, φ, hhalf, U) x ∂μ𝔽 := by
    rw [show (∑' z, loss z) = _ from hloss.tsum_eq]
    dsimp only [G]
    ring
  have hsharp : Tendsto (fun R ↦ A (M R)) atTop (𝓝 (G - E)) := by
    dsimp only [E]
    rw [sub_add_eq_sub_sub, heq]
    exact hlim
  refine ⟨hloss.summable.norm, hsharp, fun d ↦ ?_⟩
  intro I
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  have hjoint := hsharp.comp hp
  have hsub (p : ℝ × ℝ) : volF / volS * (I p - M (p.1 * p.2)) =
      A (I p) - A (M (p.1 * p.2)) := by dsimp only [A]; ring
  simp_rw [hsub]
  constructor
  · intro h
    simpa only [Function.comp_def, sub_sub_cancel] using h.sub hjoint
  · intro h
    simpa only [Function.comp_def, sub_add_cancel, show E + (G - E) = G by abel] using h.add hjoint

end RiemannMasullo
