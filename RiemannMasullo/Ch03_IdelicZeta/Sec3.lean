module

public import RiemannMasullo.Ch02_AdelicTheta.Sec4
public import RiemannMasullo.Ch03_IdelicZeta.Sec2

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Units
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Units

/-!
# S-local idelic zeta functions

Masullo, §3.3, pp. 128–141. The finset indexes the finite places, with all
archimedean places included. Holomorphy and meromorphy on quasi-character spaces
are expressed in complex norm-twist coordinates.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "modℂ[" m "," g "]" => (((m g : ℝ≥0) : ℝ) : ℂ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "rightHalf" => (Complex.re ⁻¹' Ioi (0 : ℝ))
local notation "criticalStrip" => (Complex.re ⁻¹' Ioo (0 : ℝ) 1)
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)

section Coordinates

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: §3.1.1, p. 119. A complex power of the positive module is
continuous and multiplicative. -/
theorem normPower_properties (m : G →* ℝ≥0ˣ) (hm : Continuous m) (s : ℂ) :
    (modℂ[m, (1 : G)]) ^ s = 1 ∧
    (∀ g h : G, (modℂ[m, g * h]) ^ s = (modℂ[m, g]) ^ s * (modℂ[m, h]) ^ s) ∧
    Continuous (fun g : G ↦ (modℂ[m, g]) ^ s) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro g h
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s
  · have hr : Continuous (fun g : G ↦ ((m g : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp hm)
    apply (Complex.continuous_ofReal.comp hr).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))

/-- Paper: §3.1.1, p. 119. A norm twist multiplies the quasi-character
by the given complex power of the module. -/
def quasiCharacterNormTwist (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (c : QuasiCharacter G) (s : ℂ) : QuasiCharacter G :=
  let h := normPower_properties m hm s
  c * ⟨{ toFun := fun g ↦ (modℂ[m, g]) ^ s
         map_one' := h.1
         map_mul' := h.2.1 }, h.2.2⟩

/-- Paper: §3.1.1, p. 119. Twisting with exponent one multiplies the
quasi-character by the module. -/
theorem quasiCharacterNormTwist_one (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (c : QuasiCharacter G) (g : G) :
    quasiCharacterNormTwist m hm c 1 g = c g * modℂ[m, g] := by
  change c g * (modℂ[m, g]) ^ (1 : ℂ) = _
  rw [Complex.cpow_one]

end Coordinates

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "chartₛ(" χ ")" => quasiCharacterNormTwist mₛ hmₛ ((circleToComplex).comp χ)
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "positive" => {c : Xₛ | ∃ (χ : PontryaginDual Jₛ) (s : ℂ),
  s ∈ rightHalf ∧ c = chartₛ(χ) s}
local notation "band[" m "," n "]" =>
  {g | (((m g : ℝ≥0) : ℝ)) ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}

local instance : MeasurableSpace Jₛ := borel _
local instance : MeasurableSpace J₁ := borel _
local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
local instance : MeasurableSpace Aₛ :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))

/-- Paper: §3.3.1, p. 128. The Fourier integral formed with the standard
S-adelic character and additive Tamagawa measure preserves the test space. -/
theorem sAdeleSchwartzFourier_mem (f : ℬ(Aₛ)) :
    (fun y : Multiplicative Aₛ ↦ tamagawaFourier (sAdditiveTamagawaMeasure F S)
      (sAdeleStandardCharacter F S) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd) ∈
        schwartzBruhatSubmodule (G := Multiplicative Aₛ) := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let G := Multiplicative Aₛ
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace Aₛ)
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space G := ‹T2Space Aₛ›
  let : SigmaCompactSpace Aₛ := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace G := ‹BorelSpace Aₛ›
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let hμ : (sAdditiveTamagawaMeasure F S).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace (sAdditiveTamagawaMeasure F S)
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  let g : schwartzBruhatSubmodule (PontryaginDual G) := fourier f
  have hEq (y : G) : tamagawaFourier (sAdditiveTamagawaMeasure F S)
      (sAdeleStandardCharacter F S) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd = g.val (e y) := by
    rw [tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
      rw [mul_comm x y.toAdd]
      exact he y.toAdd x)]
    exact ((hfourier f).2 (e y)).symm
  rw [funext hEq]
  exact schwartzBruhat_mem_comp_equiv e g.property

/-- Paper: §3.3.1, p. 128. The S-adelic Fourier transform uses the product
additive Tamagawa measure and the standard S-adelic character. -/
def sAdeleSchwartzFourier (f : ℬ(Aₛ)) : ℬ(Aₛ) :=
  ⟨fun y ↦ tamagawaFourier (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S)
    (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd, sAdeleSchwartzFourier_mem f⟩

/-- Paper: §3.3.1, p. 128. The Fourier transform at zero integrates the
test function against the additive Tamagawa measure. -/
theorem sAdeleSchwartzFourier_apply_zero (f : ℬ(Aₛ)) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) =
      ∫ x : Aₛ, f (Multiplicative.ofAdd x) ∂sAdditiveTamagawaMeasure F S := by
  have hp (p : ℕ) [Fact p.Prime] : padicStandardCharacter p 0 = 1 := by
    have key (n : ℕ) (a : ℤ_[p]) (ha : a = 0) :
        Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n)) = 1 := by
      subst ha
      simp
    unfold padicStandardCharacter
    exact key _ _ (Subtype.ext (mul_zero _))
  have hr : (0 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 0 := rfl
  have hf (v : HeightOneSpectrum (𝓞 ℚ)) : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 0 := rfl
  have h0 : adeleStandardCharacter F 0 = 1 := by
    simp [adeleStandardCharacter, ratAdeleStandardCharacter, hp, hr, hf]
  have hi (w : InfinitePlace F) : (0 : Aₛ).1 w = 0 := rfl
  have hS : sAdeleStandardCharacter F S 0 = 1 := by
    simp only [sAdeleStandardCharacter, finiteLocalStandardCharacter, hi, Pi.single_zero,
      Prod.snd_zero, Pi.zero_apply, RestrictedProduct.single_zero]
    exact (congrArg₂ (· * ·) (Finset.prod_eq_one fun _ _ ↦ h0)
      (Finset.prod_eq_one fun _ _ ↦ h0)).trans (one_mul 1)
  change tamagawaFourier _ _ _ (0 : Aₛ) = _
  simp [tamagawaFourier, hS]

/-- Paper: Equation (3.3.1.1), p. 129. The S-local zeta integral weights
the restriction of the test function to the S-ideles by the quasi-character. -/
def sLocalIdelicZetaIntegral (f : ℬ(Aₛ)) (c : Xₛ) : ℂ :=
  ∫ g : Iₛ, f (Multiplicative.ofAdd g.val) * c (classOf g) ∂μₛ

section AbsoluteConvergence

open scoped Classical ENNReal Pointwise WithZero

private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := ⟨by
  change (borel w.Completion).comap Units.val = _
  rw [← borel_comap, ← (Units.isEmbedding_val₀ (G₀ := w.Completion)).eq_induced]⟩
private local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
private local instance measurableSpace_finiteAdicUnits (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
private local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩

/-- Each infinite coordinate is bounded by the mixed archimedean norm. -/
private theorem infinitePlace_norm_le_mixedNorm (x : InfiniteAdeleRing F) (w : InfinitePlace F) :
    ‖x w‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  apply Finset.le_sup'_of_le _ (Finset.mem_univ w)
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _).symm.le
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _).symm.le

omit [NumberField F] in
/-- A positive norm power at an infinite place becomes integrable against the multiplicative
Tamagawa measure after division by a sufficiently large power at infinity. -/
private theorem infiniteLocalTamagawa_integrable_norm_rpow (w : InfinitePlace F) {σ : ℝ}
    (hσ : 0 < σ) (k : ℕ) (hk : (w.mult : ℝ) * σ < k) :
    SigmaFinite (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
    Integrable (fun u : w.Completionˣ ↦ ‖u.val‖ ^ ((w.mult : ℝ) * σ) / (max 1 ‖u.val‖) ^ k)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  -- Convert the density-weighted integral to radial integration for additive Haar measure.
  let d := w.mult
  let ν := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : w.Completion) := (↑(‖x‖₊ ^ d) : ℝ≥0∞)⁻¹
  let U : Set w.Completion := {0}ᶜ
  have hU : U = range (Units.val : w.Completionˣ → w.Completion) := by
    ext x
    simpa [U] using (Units.exists_iff_ne_zero (p := (· = x))).symm
  have hmU : MeasurableSet U := (measurableSet_singleton (0 : w.Completion)).compl
  have he := (Units.isEmbedding_val₀ (G₀ := w.Completion)).measurableEmbedding (hU ▸ hmU)
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hDf : ∀ᵐ x ∂ν.restrict U, D x < ⊤ := by
    refine (ae_restrict_iff' hmU).mpr (ae_of_all _ fun x hx ↦ ?_)
    have hp : 0 < ‖x‖₊ := NNReal.coe_pos.mp (norm_pos_iff.mpr hx)
    exact ENNReal.inv_lt_top.mpr (by dsimp [D]; positivity)
  have hRad (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
      [μ.IsAddHaarMeasure] (hd : Module.finrank ℝ E = d) :
      Integrable (fun x : E ↦ ‖x‖ ^ ((d : ℝ) * σ - d) / (max 1 ‖x‖) ^ k) μ := by
    refine (integrable_fun_norm_addHaar μ (f := fun r : ℝ ↦
      r ^ ((d : ℝ) * σ - d) / (max 1 r) ^ k)).mpr ?_
    have hd₀ : 0 < d := InfinitePlace.mult_pos (w := w)
    have heq (r : ℝ) (hr : 0 < r) :
        r ^ (Module.finrank ℝ E - 1) • (r ^ ((d : ℝ) * σ - d) / (max 1 r) ^ k) =
          r ^ ((d : ℝ) * σ - 1) / (max 1 r) ^ k := by
      rw [smul_eq_mul, ← mul_div_assoc, hd, ← Real.rpow_natCast, ← Real.rpow_add hr,
        Nat.cast_sub hd₀, Nat.cast_one]
      congr 2
      ring
    refine IntegrableOn.congr_fun ?_ (fun r hr ↦ (heq r hr).symm) measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    apply IntegrableOn.union
    · have hi : IntegrableOn (fun r : ℝ ↦ r ^ ((d : ℝ) * σ - 1)) (Ioc 0 1) :=
        ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by
          have hp := mul_pos (Nat.cast_pos.mpr hd₀) hσ
          linarith)).congr_set_ae Ioo_ae_eq_Ioc.symm
      refine hi.congr_fun (fun r hr ↦ ?_) measurableSet_Ioc
      simp [max_eq_left hr.2]
    · have hi : IntegrableOn (fun r : ℝ ↦ r ^ ((d : ℝ) * σ - 1 - k)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      refine hi.congr_fun (fun r hr ↦ ?_) measurableSet_Ioi
      have hr' : 0 < r := zero_lt_one.trans hr
      rw [max_eq_right hr.le, ← Real.rpow_natCast, ← Real.rpow_sub hr']
  let f (x : w.Completion) := ‖x‖ ^ ((d : ℝ) * σ - d) / (max 1 ‖x‖) ^ k
  have hν : SigmaFinite ν ∧ Integrable f ν := by
    dsimp only [ν]
    by_cases hw : w.IsReal
    · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw]
      let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm
      have hme := e.toHomeomorph.measurableEmbedding
      have hnorm (x : ℝ) : ‖e.toHomeomorph x‖ = ‖x‖ :=
        e.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) x
      exact ⟨hme.sigmaFinite_map, hme.integrable_map_iff.mpr (by
        simpa only [f, Function.comp_def, hnorm] using hRad ℝ volume (by simp [d, hw.mult_eq_one]))⟩
    · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right hw]
      have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').symm
      have hme := e.toHomeomorph.measurableEmbedding
      have hnorm (x : ℂ) : ‖e.toHomeomorph x‖ = ‖x‖ :=
        e.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm) x
      rw [show (2 • (volume : Measure ℂ)) = (2 : ℝ≥0) • volume by
        rw [two_nsmul, ← one_add_one_eq_two, add_smul, one_smul]]
      change SigmaFinite (Measure.map e.toHomeomorph ((2 : ℝ≥0) • volume)) ∧
        Integrable f (Measure.map e.toHomeomorph ((2 : ℝ≥0) • volume))
      have hi : Integrable (f ∘ e.toHomeomorph) volume := by
        simpa only [f, Function.comp_def, hnorm] using
          hRad ℂ volume (by simp [Complex.finrank_real_complex, d, hw'.mult_eq_two])
      exact ⟨hme.sigmaFinite_map, hme.integrable_map_iff.mpr (hi.smul_measure_nnreal (c := 2))⟩
  let : SigmaFinite ν := hν.1
  have hmap : Measure.map Units.val (infiniteLocalMultiplicativeTamagawaMeasure F w) =
      (ν.restrict U).withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, he.map_comap, ← hU,
      restrict_withDensity hmU]
  refine ⟨SigmaFinite.of_map _ he.measurable.aemeasurable (hmap ▸
    (SigmaFinite.withDensity_of_ne_top (hDf.mono fun _ h ↦ h.ne))), ?_⟩
  change Integrable ((fun x : w.Completion ↦
    ‖x‖ ^ ((d : ℝ) * σ) / (max 1 ‖x‖) ^ k) ∘ Units.val) _
  rw [← he.integrable_map_iff, hmap, integrable_withDensity_iff hD hDf]
  refine hν.2.restrict.congr ((ae_restrict_iff' hmU).mpr (ae_of_all _ fun x hx ↦ ?_))
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  dsimp [f, D]
  rw [ENNReal.toReal_inv, ← ENNReal.coe_pow, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnNorm, div_mul_eq_mul_div,
    ← div_eq_mul_inv, Real.rpow_sub hx', Real.rpow_natCast]

/-- A positive norm power at a finite place is integrable against the multiplicative
Tamagawa measure on units with bounded norm. -/
private theorem finiteLocalTamagawa_integrable_norm_rpow (v : HeightOneSpectrum (𝓞 F)) {σ : ℝ}
    (hσ : 0 < σ) (R : ℝ) :
    SigmaFinite (finiteLocalMultiplicativeTamagawaMeasure F v) ∧
    Integrable ({u : (v.adicCompletion F)ˣ | ‖u.val‖ ≤ R}.indicator (fun u ↦ ‖u.val‖ ^ σ))
      (finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let : ProperSpace K := properSpace_adicCompletion v
  let : LocallyCompactSpace Kˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  let : SecondCountableTopology Kˣ :=
    (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let μ := Measure.haar (G := Kˣ)
  let U : Set Kˣ := O.units
  have hUc : IsCompact U := by
    let : CompactSpace O := compactSpace_adicCompletionIntegers v
    let : CompactSpace Oˣ := compactSpace_units_of_compactSpace O
    let ι := Units.map O.subtype.toMonoidHom
    have hι : Continuous ι := continuous_subtype_val.units_map _
    have hrange : range ι = U := by
      ext u
      exact ⟨by rintro ⟨a, rfl⟩; exact ⟨a.val.property, a.inv.property⟩,
        fun hu ↦ ⟨O.toSubmonoid.unitsEquivUnitsType ⟨u, hu⟩, Units.ext rfl⟩⟩
    rw [← hrange]
    exact isCompact_range hι
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hUi : (interior U).Nonempty := by
    rw [hUo.interior_eq]
    exact ⟨1, O.units.one_mem⟩
  have hmass : μ U ≠ 0 := ne_of_gt (μ.measure_pos_of_nonempty_interior hUi)
  have hscale : ∃ a : ℝ≥0, finiteLocalMultiplicativeTamagawaMeasure F v = a • μ := by
    -- The prescribed mass on integer units is finite, and Haar gives them positive mass.
    let a : ℝ≥0∞ := (ENNReal.ofReal (Real.sqrt ((v.asIdeal.absNorm : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ / μ U
    have hn : (0 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
    have hsqrt := Real.sqrt_pos_of_pos (pow_pos hn (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))
    have ha : a ≠ ⊤ := ENNReal.div_ne_top
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))) hmass
    refine ⟨a.toNNReal, ?_⟩
    change finiteLocalMultiplicativeTamagawaMeasure F v = (↑a.toNNReal : ℝ≥0∞) • μ
    rw [ENNReal.coe_toNNReal ha]
    rfl
  obtain ⟨a, ha⟩ := hscale
  rw [ha]
  refine ⟨SMul.sigmaFinite a, ?_⟩
  apply Integrable.smul_measure_nnreal
  -- Every shell is a translate of the compact group of integer units.
  let val : Valuation K ℤᵐ⁰ := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 π.val hπ.ne_zero
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hp : ‖p.val‖ = q⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p hp
  let ι := Units.map O.subtype.toMonoidHom
  have hdecomp (u : Kˣ) : u = p ^ (e u).1.toAdd * ι (e u).2 := by
    apply e.injective
    rw [map_mul, map_zpow, hep, heι]
    refine Prod.ext ?_ (by simp)
    change (e u).1.toAdd = (e u).1.toAdd * 1 + 0
    simp
  have hU (u : Kˣ) (hu : u ∈ U) : ‖u.val‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu)
  have hnorm (k : ℤ) (u : Kˣ) (hu : u ∈ U) : ‖(p ^ k * u).val‖ = q⁻¹ ^ k := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hp, hU u hu, mul_one]
  let r (k : ℤ) := q⁻¹ ^ k
  let shell (k : ℤ) := (fun u : Kˣ ↦ p ^ k * u) '' U
  have hshell (k : ℤ) : IsCompact (shell k) := hUc.image (continuous_const.mul continuous_id)
  have hm (k : ℤ) : μ (shell k) = μ U := measure_smul μ (p ^ k) U
  have hcover : {u : Kˣ | ‖u.val‖ ≤ R} ⊆ ⋃ k : {k : ℤ // r k ≤ R}, shell k.val := by
    intro u hu
    have hz : ι (e u).2 ∈ U := ⟨(e u).2.val.property, (e u).2.inv.property⟩
    have hk : r (e u).1.toAdd ≤ R := by
      change ‖u.val‖ ≤ R at hu
      rwa [hdecomp u, hnorm _ _ hz] at hu
    exact mem_iUnion.mpr ⟨⟨_, hk⟩, ⟨_, hz, (hdecomp u).symm⟩⟩
  have hR : MeasurableSet {u : Kˣ | ‖u.val‖ ≤ R} :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  rw [integrable_indicator_iff hR]
  let f (u : Kˣ) := ‖u.val‖ ^ σ
  have hf : Continuous f := (continuous_norm.comp Units.continuous_val).rpow_const
    (fun _ ↦ Or.inr hσ.le)
  refine (integrableOn_iUnion_of_summable_integral_norm
    (fun (k : {k : ℤ // r k ≤ R}) ↦ hf.continuousOn.integrableOn_compact (hshell k.val)) ?_).mono_set hcover
  have hseq : Summable ({k : ℤ | r k ≤ R}.indicator (fun k ↦ (q⁻¹ ^ k) ^ σ)) := by
    let G := {k : ℤ | r k ≤ R}.indicator (fun k ↦ (q⁻¹ ^ k) ^ σ)
    change Summable G
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine (summable_geometric_of_lt_one (r := q⁻¹ ^ σ) (by positivity)
        (Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hq) hσ)).of_nonneg_of_le ?_ ?_
      · intro n
        exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
      · intro n
        have heq : (q⁻¹ ^ σ) ^ n = (q⁻¹ ^ (n : ℤ)) ^ σ := by
          rw [← zpow_natCast, Real.rpow_zpow_comm (by positivity)]
        rw [heq]
        exact (Set.indicator_le_self' (s := {k : ℤ | r k ≤ R})
          (f := fun k ↦ (q⁻¹ ^ k) ^ σ) (fun _ _ ↦ by positivity)) n
    · obtain ⟨N, hN⟩ := eventually_atTop.mp
        ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop R)
      refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn ↦ ?_)
      have hlt : R < r (-(n : ℤ)) := by
        simpa [r, zpow_neg, inv_zpow] using hN n (by simpa using hn)
      exact Set.indicator_of_notMem (not_le.mpr hlt) _
  have hsub : Summable (fun (k : {k : ℤ // r k ≤ R}) ↦ r k.val ^ σ) := by
    refine (hseq.comp_injective Subtype.val_injective).congr ?_
    intro k
    exact Set.indicator_of_mem k.property _
  refine (hsub.mul_right (μ.real U)).congr fun k ↦ ?_
  have hEq : Set.EqOn (fun u : Kˣ ↦ ‖f u‖) (fun _ ↦ r k.val ^ σ) (shell k.val) := by
    rintro _ ⟨u, hu, rfl⟩
    change ‖‖(p ^ k.val * u).val‖ ^ σ‖ = r k.val ^ σ
    rw [hnorm _ _ hu, Real.norm_of_nonneg (by positivity)]
  rw [setIntegral_congr_fun (hshell _).measurableSet hEq, setIntegral_const]
  change r k.val ^ σ * (μ U).toReal = (μ (shell k.val)).toReal * r k.val ^ σ
  rw [hm, mul_comm]

/-- The modulus of a norm twist of a unitary character is the corresponding real norm power. -/
private theorem norm_sLocalNormTwist (χ : PontryaginDual Jₛ) (s : ℂ) (g : Iₛ) :
    ‖chartₛ(χ) s (classOf g)‖ =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ ((w.mult : ℝ) * s.re)) *
        ∏ v : S, ‖g.val.2 v‖ ^ s.re := by
  change ‖(χ (classOf g) : ℂ) * (modℂ[mₛ, classOf g]) ^ s‖ = _
  rw [norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hnorm : (((sIdeleNorm F S g : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖ := by
    simp [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
      NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_pow]
  rw [hnorm, Real.mul_rpow (by positivity) (by positivity)]
  have hprod {ι : Type _} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
      (∏ i, a i) ^ s.re = ∏ i, a i ^ s.re := by
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert i t hi ht =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (ha i) (Finset.prod_nonneg fun j _ ↦ ha j), ht]
  apply congrArg₂ (· * ·)
  · exact (hprod (fun w : InfinitePlace F ↦ ‖g.val.1 w‖ ^ w.mult)
      (fun w ↦ pow_nonneg (norm_nonneg (g.val.1 w)) w.mult)).trans
      (Finset.prod_congr rfl fun w _ ↦
        (Real.rpow_natCast_mul (norm_nonneg (g.val.1 w)) w.mult s.re).symm)
  · exact hprod (fun v : S ↦ ‖g.val.2 v‖) (fun v ↦ norm_nonneg (g.val.2 v))

/-- Paper: Theorem 3.3.1.1(1), p. 129. The S-idele integrand is absolutely
integrable on the positive half-plane. -/
theorem sLocalIdelicZetaIntegral_integrable (f : ℬ(Aₛ)) (c : Xₛ) (hc : c ∈ positive) :
    Integrable (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val) * c (classOf g)) μₛ := by
  classical
  obtain ⟨χ, s, hs, rfl⟩ := hc
  have hσ : 0 < s.re := hs
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * s.re)
  have hw (w : InfinitePlace F) : (w.mult : ℝ) * s.re < k := by
    have hm : (w.mult : ℝ) ≤ 2 := by
      by_cases h : w.IsReal
      · simp [h.mult_eq_one]
      · simp [(InfinitePlace.not_isReal_iff_isComplex.mp h).mult_eq_two]
    exact (mul_le_mul_of_nonneg_right hm hσ.le).trans_lt hk
  obtain ⟨C, hC, hsupport, hdecay⟩ := sAdeleSchwartz_exists_decay_bound F S f
  have hR (v : S) : ∃ r : ℝ, ∀ x ∈ C, ‖x v‖ ≤ r :=
    hC.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  choose R hR using hR
  obtain ⟨B₀, hB₀, hb₀⟩ := hdecay 0
  obtain ⟨B₁, hB₁, hb₁⟩ := hdecay (∑ _w : InfinitePlace F, k)
  let B := max B₀ B₁
  have hBd (x : Aₛ) :
      ‖f (Multiplicative.ofAdd x)‖ * (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) ≤ B := by
    let r := ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x.1‖
    have hprod : (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) ≤
        (max 1 r) ^ (∑ _w : InfinitePlace F, k) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
        (fun w _ ↦ pow_le_pow_left₀ (by positivity)
          (max_le_max le_rfl (infinitePlace_norm_le_mixedNorm x.1 w)) _)
    refine (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans ?_
    rcases le_total r 1 with hr | hr
    · simpa [max_eq_left hr, B] using (show ‖f (Multiplicative.ofAdd x)‖ ≤ max B₀ B₁ from
        (by simpa using hb₀ x : ‖f (Multiplicative.ofAdd x)‖ ≤ B₀).trans (le_max_left _ _))
    · rw [max_eq_right hr]
      exact (hb₁ x).trans (le_max_right _ _)
  -- The coordinate bounds give an integrable product majorant.
  let a (w : InfinitePlace F) (u : w.Completionˣ) :=
    ‖u.val‖ ^ ((w.mult : ℝ) * s.re) / (max 1 ‖u.val‖) ^ k
  let b (v : S) := {u : (v.val.adicCompletion F)ˣ | ‖u.val‖ ≤ R v}.indicator
    (fun u ↦ ‖u.val‖ ^ s.re)
  let μa := infiniteLocalMultiplicativeTamagawaMeasure F
  let μb := fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val
  have ha (w : InfinitePlace F) := infiniteLocalTamagawa_integrable_norm_rpow w hσ k (hw w)
  have hb (v : S) := finiteLocalTamagawa_integrable_norm_rpow v.val hσ (R v)
  let (w : InfinitePlace F) : SigmaFinite (μa w) := (ha w).1
  let (v : S) : SigmaFinite (μb v) := (hb v).1
  have hmajor := ((Integrable.fintype_prod_dep (fun w ↦ (ha w).2)).mul_prod
    (Integrable.fintype_prod_dep (fun v ↦ (hb v).2))).const_mul B
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let E := e.toHomeomorph.trans (eArch.toHomeomorph.prodCongr eS.toHomeomorph)
  have hE : Measurable E := by
    apply Measurable.prodMk
    · exact Measurable.of_eval fun w ↦ measurable_comap_iff.mpr
        ((measurable_pi_apply w).comp (measurable_fst.comp MeasurableSpace.le_map_comap))
    · apply Measurable.of_eval
      intro v
      have hborel : borel (v.val.adicCompletion F)ˣ =
          (borel (v.val.adicCompletion F)).comap Units.val := by
        rw [(Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)).eq_induced, borel_comap]
      change @Measurable Iₛ _ _ (borel _) _
      rw [hborel]
      exact measurable_comap_iff.mpr
        ((measurable_pi_apply v).comp (measurable_snd.comp MeasurableSpace.le_map_comap))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    (Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)).secondCountableTopology
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  let : BorelSpace Aₛ :=
    inferInstanceAs (BorelSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  have hE' : Measurable E.symm :=
    measurable_comap_iff.mpr
      ((Units.continuous_val : Continuous (Units.val : Iₛ → Aₛ)).comp E.symm.continuous).measurable
  let em : Iₛ ≃ᵐ _ := ⟨E.toEquiv, hE, hE'⟩
  have hmap : μₛ = ((Measure.pi μa).prod (Measure.pi μb)).map em.symm := rfl
  rw [hmap]
  apply em.symm.measurableEmbedding.integrable_map_iff.mpr
  refine hmajor.mono' ?_ (ae_of_all _ fun p ↦ ?_)
  · have hf : Continuous (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val)) :=
      (schwartzBruhat_continuous (G := Multiplicative Aₛ) f).comp
        (Units.continuous_val : Continuous (Units.val : Iₛ → Aₛ))
    have hc' : Continuous (fun g : Iₛ ↦ chartₛ(χ) s (classOf g)) :=
      (chartₛ(χ) s).continuous.comp continuous_quotient_mk'
    exact ((hf.mul hc').comp E.symm.continuous).aestronglyMeasurable
  · let g := em.symm p
    change ‖f (Multiplicative.ofAdd g.val) * chartₛ(χ) s (classOf g)‖ ≤
      B * ((∏ w, a w (p.1 w)) * ∏ v, b v (p.2 v))
    have h₁ (w : InfinitePlace F) : g.val.1 w = (p.1 w).val := rfl
    have h₂ (v : S) : g.val.2 v = (p.2 v).val := rfl
    rw [norm_mul, norm_sLocalNormTwist]
    simp_rw [h₁, h₂]
    by_cases hp : g.val.2 ∈ C
    · have hb' (v : S) : b v (p.2 v) = ‖(p.2 v).val‖ ^ s.re :=
        Set.indicator_of_mem (by simpa [← h₂ v] using hR v g.val.2 hp) _
      simp_rw [hb', a, Finset.prod_div_distrib]
      have hD : 0 < ∏ w : InfinitePlace F, (max 1 ‖(p.1 w).val‖) ^ k := by positivity
      rw [div_mul_eq_mul_div, ← mul_div_assoc, le_div_iff₀ hD]
      have h := hBd g.val
      simp_rw [h₁] at h
      calc
        _ = (‖f (Multiplicative.ofAdd g.val)‖ * ∏ w : InfinitePlace F,
              (max 1 ‖(p.1 w).val‖) ^ k) *
            ((∏ w : InfinitePlace F, ‖(p.1 w).val‖ ^ ((w.mult : ℝ) * s.re)) *
              ∏ v : S, ‖(p.2 v).val‖ ^ s.re) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)
    · rw [hsupport g.val hp, norm_zero, zero_mul]
      exact mul_nonneg (hB₀.trans (le_max_left _ _)) (mul_nonneg
        (Finset.prod_nonneg fun _ _ ↦ by dsimp [a]; positivity)
        (Finset.prod_nonneg fun v _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) _))

end AbsoluteConvergence

/-- Paper: Equation (3.3.1.1), p. 129. At the bare norm character the integrand
is the test function times the S-idelic norm. -/
theorem sLocalIdelicZetaIntegral_norm (f : ℬ(Aₛ)) :
    sLocalIdelicZetaIntegral f (chartₛ((1 : PontryaginDual Jₛ)) 1) =
      ∫ g : Iₛ, f (Multiplicative.ofAdd g.val) * modℂ[sIdeleNorm F S, g] ∂μₛ := by
  unfold sLocalIdelicZetaIntegral
  congr 1
  funext g
  congr 1
  change (((1 : PontryaginDual Jₛ) (classOf g) : Circle) : ℂ) *
    (modℂ[mₛ, classOf g]) ^ (1 : ℂ) = _
  rw [Complex.cpow_one, sIdeleQuotientNorm_mk, PontryaginDual.one_apply, Circle.coe_one, one_mul]

/-- Paper: Theorem 3.3.1.1(1) and Remark 3.3.1.2, p. 129. Closed norm-band
truncations of the zeta integral converge uniformly on compact subsets.
Deviation: The positive band widths are indexed by n + 1. -/
theorem sLocalIdelicZetaIntegral_tendstoUniformlyOn (f : ℬ(Aₛ))
    (K : Set Xₛ) (hK : IsCompact K) (hKpos : K ⊆ positive) :
    TendstoUniformlyOn (fun (n : ℕ) c ↦
      ∫ g in band[sIdeleNorm F S, n], f (Multiplicative.ofAdd g.val) * c (classOf g) ∂μₛ)
      (sLocalIdelicZetaIntegral f) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  have hne : ∃ x, mₛ x ≠ 1 := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨σ t, (hσ t).trans_ne ht⟩
  let abscissa := quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) hne
  have habs : Continuous abscissa :=
    continuous_quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) hne
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne habs.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne habs.continuousOn
  let r (g : Iₛ) : ℝ := (sIdeleNorm F S g : ℝ≥0)
  have hr (g : Iₛ) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnorm {c : Xₛ} (hc : c ∈ K) (g : Iₛ) : ‖c (classOf g)‖ = r g ^ abscissa c := by
    obtain ⟨χ, s, -, rfl⟩ := hKpos hc
    have hs : abscissa (chartₛ(χ) s) = s.re :=
      quasiCharacterAbscissa_of_unitary_twist mₛ (isProperMap_sIdeleQuotientNorm F S) hne
        _ χ s (fun _ ↦ rfl)
    change ‖(χ (classOf g) : ℂ) * (modℂ[mₛ, classOf g]) ^ s‖ = _
    rw [hs, norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (hr g) s
  let integrand (c : Xₛ) (g : Iₛ) := f (Multiplicative.ofAdd g.val) * c (classOf g)
  have hint {c : Xₛ} (hc : c ∈ K) : Integrable (integrand c) μₛ :=
    sLocalIdelicZetaIntegral_integrable f c (hKpos hc)
  -- The two endpoint characters bound the integrands below and above norm one.
  let bound (g : Iₛ) := ‖integrand a g‖ + ‖integrand b g‖
  have hbound : Integrable bound μₛ := (hint ha).norm.add (hint hb).norm
  have hle {c : Xₛ} (hc : c ∈ K) (g : Iₛ) : ‖integrand c g‖ ≤ bound g := by
    have hweighted {d : Xₛ} (h : ‖c (classOf g)‖ ≤ ‖d (classOf g)‖) :
        ‖integrand c g‖ ≤ ‖integrand d g‖ := by
      dsimp only [integrand]
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    by_cases hg : r g ≤ 1
    · refine (hweighted (d := a) ?_).trans (le_add_of_nonneg_right (norm_nonneg (integrand b g)))
      rw [hnorm hc, hnorm ha]
      exact Real.rpow_le_rpow_of_exponent_ge (hr g) hg (hmin hc)
    · refine (hweighted (d := b) ?_).trans (le_add_of_nonneg_left (norm_nonneg (integrand a g)))
      rw [hnorm hc, hnorm hb]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hg) (hmax hc)
  let B (n : ℕ) : Set Iₛ := band[sIdeleNorm F S, n]
  have hB (n : ℕ) : MeasurableSet (B n) := by
    let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
    let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    let : BorelSpace Iₛ := ⟨by
      change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace Aₛ) = _
      rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap,
        BorelSpace.measurable_eq (α := Aₛ)]⟩
    have hnorm_cont : Continuous (fun g : Iₛ ↦ mₛ (classOf g)) :=
      Continuous.comp hmₛ QuotientGroup.continuous_mk
    have hrcont : Continuous r :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp hnorm_cont)
    exact hrcont.measurable measurableSet_Icc
  have hBmono : Monotone B := by
    intro i j hij g hg
    have hij' : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact ⟨((inv_le_inv₀ (by positivity) (by positivity)).mpr hij').trans hg.1,
      hg.2.trans hij'⟩
  have htail : (⋂ n, (B n)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    obtain ⟨n, hn⟩ := exists_nat_gt (max (r g) (r g)⁻¹)
    have hn' : max (r g) (r g)⁻¹ ≤ (n : ℝ) + 1 :=
      hn.le.trans (le_add_of_nonneg_right zero_le_one)
    have hmem : g ∈ B n :=
      ⟨(inv_le_comm₀ (by positivity) (hr g)).2 ((le_max_right _ _).trans hn'),
        (le_max_left _ _).trans hn'⟩
    exact (mem_iInter.mp hg n) hmem
  have hlim : Tendsto (fun n ↦ ∫ g in (B n)ᶜ, bound g ∂μₛ) atTop (𝓝 0) := by
    simpa only [htail, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (μ := μₛ) (f := bound) (fun n ↦ (hB n).compl)
        (fun _ _ hij ↦ compl_subset_compl.mpr (hBmono hij)) ⟨0, hbound.integrableOn⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn c hc
  change dist (∫ g, integrand c g ∂μₛ) (∫ g in B n, integrand c g ∂μₛ) < ε
  rw [dist_eq_norm, ← integral_add_compl (hB n) (hint hc), add_sub_cancel_left]
  calc
    ‖∫ g in (B n)ᶜ, integrand c g ∂μₛ‖ ≤ ∫ g in (B n)ᶜ, ‖integrand c g‖ ∂μₛ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g in (B n)ᶜ, bound g ∂μₛ :=
      setIntegral_mono_on (hint hc).norm.integrableOn hbound.integrableOn (hB n).compl
        (fun g _ ↦ hle hc g)
    _ < ε := hn

/-- A logarithm times a power with exponent in (σ/2, 3σ/2) is bounded by a multiple
of the sum of the σ/4-th and 7σ/4-th powers. -/
private theorem rpow_mul_abs_log_le_of_mem_Ioo {σ x r : ℝ} (hσ : 0 < σ)
    (hx : x ∈ Ioo (σ / 2) (3 * σ / 2)) (hr : 0 < r) :
    r ^ x * |Real.log r| ≤ 4 / σ * (r ^ (σ / 4) + r ^ (7 * σ / 4)) := by
  have hε : 0 < σ / 4 := by positivity
  rcases le_or_gt 1 r with h1 | h1
  · have hlog := Real.log_le_rpow_div hr.le hε
    have hpow : r ^ x ≤ r ^ (3 * σ / 2) := Real.rpow_le_rpow_of_exponent_le h1 hx.2.le
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    calc r ^ x * Real.log r ≤ r ^ (3 * σ / 2) * (r ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul hpow hlog (Real.log_nonneg h1) (by positivity)
      _ = 4 / σ * r ^ (7 * σ / 4) := by
          rw [mul_div_assoc', ← Real.rpow_add hr]
          field_simp
          ring_nf
      _ ≤ _ := by
          have : 0 ≤ r ^ (σ / 4) := by positivity
          nlinarith [show 0 < 4 / σ by positivity]
  · have hlog := Real.log_le_rpow_div (inv_pos.mpr hr).le hε
    have hpow : r ^ x ≤ r ^ (σ / 2) := Real.rpow_le_rpow_of_exponent_ge hr h1.le hx.1.le
    rw [abs_of_neg (Real.log_neg hr h1), ← Real.log_inv]
    calc r ^ x * Real.log r⁻¹ ≤ r ^ (σ / 2) * (r⁻¹ ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul hpow hlog (Real.log_nonneg ((one_le_inv₀ hr).mpr h1.le)) (by positivity)
      _ = 4 / σ * r ^ (σ / 4) := by
          rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, mul_div_assoc', ← Real.rpow_add hr]
          field_simp
          ring_nf
      _ ≤ _ := by
          have : 0 ≤ r ^ (7 * σ / 4) := by positivity
          nlinarith [show 0 < 4 / σ by positivity]

/-- Paper: Theorem 3.3.1.1(1), p. 129. The zeta integral is holomorphic in
every norm-twist coordinate on the right half-plane. -/
theorem sLocalIdelicZetaIntegral_analyticOn (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZetaIntegral f (chartₛ(χ) s)) rightHalf := by
  have hopen : IsOpen (rightHalf : Set ℂ) := isOpen_Ioi.preimage Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) hopen
  refine DifferentiableAt.differentiableWithinAt ?_
  have hσ : 0 < s.re := hs
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace Iₛ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace Aₛ) = _
    rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap,
      BorelSpace.measurable_eq (α := Aₛ)]⟩
  let r (g : Iₛ) : ℝ := ((mₛ (classOf g) : ℝ≥0) : ℝ)
  have hr (g : Iₛ) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrcont : Continuous r :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (Continuous.comp hmₛ QuotientGroup.continuous_mk))
  let W (z : ℂ) (g : Iₛ) : ℂ := f (Multiplicative.ofAdd g.val) * chartₛ(χ) z (classOf g)
  let D (z : ℂ) (g : Iₛ) : ℂ := W z g * Complex.log (r g : ℂ)
  have hnormW (χ' : PontryaginDual Jₛ) (z : ℂ) (g : Iₛ) :
      ‖f (Multiplicative.ofAdd g.val) * chartₛ(χ') z (classOf g)‖ =
        ‖f (Multiplicative.ofAdd g.val)‖ * r g ^ z.re := by
    change ‖f (Multiplicative.ofAdd g.val) * ((χ' (classOf g) : ℂ) * (r g : ℂ) ^ z)‖ = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hr g)]
  let V : Set ℂ := Complex.re ⁻¹' Ioo (s.re / 2) (3 * s.re / 2)
  have hV : V ∈ 𝓝 s := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
    (show s.re ∈ Ioo (s.re / 2) (3 * s.re / 2) from ⟨by linarith, by linarith⟩)
  have hint (χ' : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) :
      Integrable (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val) * chartₛ(χ') z (classOf g)) μₛ :=
    sLocalIdelicZetaIntegral_integrable f _ ⟨χ', z, hz, rfl⟩
  have hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (W z) μₛ :=
    Filter.mem_of_superset hV fun z hz ↦ (hint χ z (by
      have h := hz.1
      linarith)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D s) μₛ :=
    (hint χ s hσ).aestronglyMeasurable.mul (Complex.measurable_log.comp
      (Complex.continuous_ofReal.comp hrcont).measurable).aestronglyMeasurable
  let P (a : ℝ) (g : Iₛ) : ℂ :=
    f (Multiplicative.ofAdd g.val) * chartₛ((1 : PontryaginDual Jₛ)) (a : ℂ) (classOf g)
  have hPint (a : ℝ) (ha : 0 < a) : Integrable (P a) μₛ :=
    hint 1 (a : ℂ) (by simpa using ha)
  let bound (g : Iₛ) : ℝ := 4 / s.re * (‖P (s.re / 4) g‖ + ‖P (7 * s.re / 4) g‖)
  have hbound : Integrable bound μₛ :=
    ((hPint _ (by positivity)).norm.add (hPint _ (by positivity)).norm).const_mul _
  have hDbound : ∀ᵐ g ∂μₛ, ∀ z ∈ V, ‖D z g‖ ≤ bound g := Eventually.of_forall fun g z hz ↦ by
    have hlog : Complex.log (r g : ℂ) = (Real.log (r g) : ℂ) :=
      (Complex.ofReal_log (hr g).le).symm
    change ‖W z g * Complex.log (r g : ℂ)‖ ≤
      4 / s.re * (‖P (s.re / 4) g‖ + ‖P (7 * s.re / 4) g‖)
    rw [norm_mul, hnormW, hlog, Complex.norm_real, Real.norm_eq_abs, hnormW, hnormW,
      Complex.ofReal_re, Complex.ofReal_re, mul_assoc]
    calc ‖f (Multiplicative.ofAdd g.val)‖ * (r g ^ z.re * |Real.log (r g)|)
        ≤ ‖f (Multiplicative.ofAdd g.val)‖ *
          (4 / s.re * (r g ^ (s.re / 4) + r g ^ (7 * s.re / 4))) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le_of_mem_Ioo hσ hz (hr g))
            (norm_nonneg _)
      _ = _ := by ring
  have hdiff : ∀ᵐ g ∂μₛ, ∀ z ∈ V, HasDerivAt (fun w ↦ W w g) (D z g) z :=
    Eventually.of_forall fun g z _ ↦ by
      have hg : (r g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr g).ne'
      change HasDerivAt (fun w : ℂ ↦ f (Multiplicative.ofAdd g.val) *
          ((χ (classOf g) : ℂ) * (r g : ℂ) ^ w))
        ((f (Multiplicative.ofAdd g.val) * ((χ (classOf g) : ℂ) * (r g : ℂ) ^ z)) *
          Complex.log (r g : ℂ)) z
      simpa only [id_eq, mul_assoc, mul_one] using
        (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul
          (χ (classOf g) : ℂ)).const_mul (f (Multiplicative.ofAdd g.val))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmeas (hint χ s hσ) hDmeas
    hDbound hbound hdiff).2.differentiableAt

section LocalFactors

variable {K : Type*} [Field K] [TopologicalSpace K] [MeasurableSpace Kˣ]

/-- Paper: Equation (3.3.1.7), p. 130. The local zeta integral integrates
the test function times the local quasi-character on the unit group. -/
def localIdelicZetaIntegral (μ : Measure Kˣ) (f : K → ℂ) (c : QuasiCharacter Kˣ) : ℂ :=
  ∫ g : Kˣ, f g.val * c g ∂μ

/-- Paper: Equation (3.3.2.1), p. 137. On an indicator of a set of finite
measure on which the character is trivial, the local zeta integral is its mass. -/
theorem localIdelicZetaIntegral_indicator (μ : Measure Kˣ) (c : QuasiCharacter Kˣ)
    (U : Set Kˣ) (hU : MeasurableSet U) (hfin : μ U ≠ ⊤) (hc : ∀ g ∈ U, c g = 1) :
    localIdelicZetaIntegral μ ((Units.val '' U).indicator (fun _ ↦ 1)) c = (μ U).toReal := by
  have h (g : Kˣ) : (Units.val '' U).indicator (fun _ ↦ (1 : ℂ)) g.val * c g =
      U.indicator (fun _ ↦ (1 : ℂ)) g := by
    by_cases hg : g ∈ U
    · rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hg), Set.indicator_of_mem hg, hc g hg,
        one_mul]
    · rw [Set.indicator_of_notMem, Set.indicator_of_notMem hg, zero_mul]
      rintro ⟨x, hx, hxg⟩
      exact hg (Units.ext hxg ▸ hx)
  unfold localIdelicZetaIntegral
  simp_rw [h]
  rw [integral_indicator_const _ hU, measureReal_def, Complex.real_smul, mul_one]

variable [IsTopologicalGroup Kˣ]

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. A local Tate factor is meromorphic
in norm-twist coordinates and gives the local Fourier equation on the strip
of simultaneous absolute convergence. -/
def IsLocalTateFactor (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (μ : Measure Kˣ)
    (fourier : (K → ℂ) → K → ℂ) (ρ : QuasiCharacter Kˣ → ℂ) : Prop :=
  (∀ χ : PontryaginDual Kˣ,
    MeromorphicNFOn (fun s ↦ ρ (quasiCharacterNormTwist m hm ((circleToComplex).comp χ) s)) univ) ∧
  ∀ (f : ℬ(K)) (χ : PontryaginDual Kˣ) (s : ℂ), s ∈ criticalStrip →
    let c := quasiCharacterNormTwist m hm ((circleToComplex).comp χ) s
    let test := fun x ↦ f (Multiplicative.ofAdd x)
    localIdelicZetaIntegral μ test c =
      ρ c * localIdelicZetaIntegral μ (fourier test) (dualQuasiCharacter m hm c)

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. A nonzero transformed zeta integral
on the strip determines the correcting factor by a ratio. -/
theorem IsLocalTateFactor.eq_div {m : Kˣ →* ℝ≥0ˣ} {hm : Continuous m} {μ : Measure Kˣ}
    {fourier : (K → ℂ) → K → ℂ} {ρ : QuasiCharacter Kˣ → ℂ}
    (hρ : IsLocalTateFactor m hm μ fourier ρ) (f : ℬ(K)) (χ : PontryaginDual Kˣ)
    (s : ℂ) (hs : s ∈ criticalStrip) :
    let c := quasiCharacterNormTwist m hm ((circleToComplex).comp χ) s
    let test := fun x ↦ f (Multiplicative.ofAdd x)
    let Zdual := localIdelicZetaIntegral μ (fourier test) (dualQuasiCharacter m hm c)
    Zdual ≠ 0 → ρ c = localIdelicZetaIntegral μ test c / Zdual := by
  intro c test Zdual hZ
  rw [hρ.2 f χ s hs, mul_div_cancel_right₀ _ hZ]

end LocalFactors

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "infiniteNorm(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "finiteNorm(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)

local instance (v : Primes) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

local notation "infiniteFourier(" w ")" => tamagawaFourier (infiniteLocalAdditiveTamagawaMeasure F w)
  (fun x ↦ adeleStandardCharacter F (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "finiteFourier(" v ")" => tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v)
  (finiteLocalStandardCharacter F v)

/-- Paper: Equation (3.3.1.3), p. 129. The normalized archimedean module is continuous. -/
theorem continuous_infiniteLocalModule (w : InfinitePlace F) :
    Continuous (infiniteNorm(w)) := by
  change Continuous (fun x : w.Completionˣ ↦
    Units.map nnNormHom.toMonoidHom x ^ InfinitePlace.mult w)
  exact (continuous_nnNorm.units_map _).pow _

/-- Paper: Equation (3.3.1.3), p. 129. The normalized finite-place module is continuous. -/
theorem continuous_finiteLocalModule (v : Primes) :
    Continuous (finiteNorm(v)) := by
  exact continuous_nnNorm.units_map _

/-- Paper: Equation (3.3.1.3), p. 129. Tate's local equation characterizes
a unique archimedean factor in normal form. -/
theorem infiniteLocalTateFactor_existsUnique (w : InfinitePlace F) :
    ∃! ρ, IsLocalTateFactor (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) (infiniteFourier(w)) ρ := by sorry

/-- Paper: Equation (3.3.1.3), p. 129. Tate's local equation characterizes
a unique finite-place factor in normal form. -/
theorem finiteLocalTateFactor_existsUnique (v : Primes) :
    ∃! ρ, IsLocalTateFactor (finiteNorm(v)) (continuous_finiteLocalModule v)
      (finiteLocalMultiplicativeTamagawaMeasure F v) (finiteFourier(v)) ρ := by sorry

/-- Paper: Equation (3.3.1.3), p. 129. The archimedean Tate factor uses the
standard local Fourier transform.
Deviation: The local functional equation fixes the Fourier sign convention. -/
def infiniteLocalTateFactor (w : InfinitePlace F) : QuasiCharacter w.Completionˣ → ℂ :=
  (infiniteLocalTateFactor_existsUnique w).exists.choose

/-- Paper: Equation (3.3.1.3), p. 129. The finite Tate factor uses the
standard local Fourier transform.
Deviation: The local functional equation fixes the Haar and Fourier conventions. -/
def finiteLocalTateFactor (v : Primes) : QuasiCharacter (v.adicCompletion F)ˣ → ℂ :=
  (finiteLocalTateFactor_existsUnique v).exists.choose

/-- Paper: Equation (3.3.2.11), p. 139. The archimedean factor satisfies
Tate's equation for the specified Fourier transform. -/
theorem infiniteLocalTateFactor_spec (w : InfinitePlace F) :
    IsLocalTateFactor (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) (infiniteFourier(w))
      (infiniteLocalTateFactor w) :=
  (infiniteLocalTateFactor_existsUnique w).exists.choose_spec

/-- Paper: Equation (3.3.2.11), p. 139. The finite-place factor satisfies
Tate's equation for the specified Fourier transform. -/
theorem finiteLocalTateFactor_spec (v : Primes) :
    IsLocalTateFactor (finiteNorm(v)) (continuous_finiteLocalModule v)
      (finiteLocalMultiplicativeTamagawaMeasure F v) (finiteFourier(v))
      (finiteLocalTateFactor v) :=
  (finiteLocalTateFactor_existsUnique v).exists.choose_spec

local notation "eProd" => ContinuousMulEquiv.prodUnits
  (InfiniteAdeleRing F) ((v : S) → HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "eArch" => ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
local notation "eFin" => ContinuousMulEquiv.piUnits (M := fun v : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "archAt(" w ")" => fun x ↦
  classOf ((eProd).symm ((eArch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1))
local notation "finAt(" v ")" => fun x ↦
  classOf ((eProd).symm (1, (eFin).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a unit at an archimedean
place and taking its class is continuous and multiplicative. -/
theorem sLocalInfiniteInsertion_properties (w : InfinitePlace F) :
    let i : w.Completionˣ → Jₛ := archAt(w)
    i 1 = 1 ∧ (∀ x y, i (x * y) = i x * i y) ∧ Continuous i := by
  classical
  let A (v : InfinitePlace F) := v.Completionˣ
  let q : Iₛ →* Jₛ := QuotientGroup.mk' _
  let i := (q.comp (eProd).symm.toMonoidHom).comp
    ((MonoidHom.inl _ _).comp ((eArch).symm.toMonoidHom.comp (MonoidHom.mulSingle A w)))
  refine ⟨i.map_one, i.map_mul, ?_⟩
  exact QuotientGroup.continuous_mk.comp ((eProd).symm.continuous.comp
    (((eArch).symm.continuous.comp (continuous_mulSingle (A := A) w)).prodMk continuous_const))

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a unit at an archimedean
place restricts an S-local quasi-character to that place. -/
def sLocalInfiniteRestriction (w : InfinitePlace F) (c : Xₛ) : QuasiCharacter w.Completionˣ :=
  let h := sLocalInfiniteInsertion_properties (S := S) w
  c.comp ⟨{ toFun := archAt(w), map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a unit at a finite
place and taking its class is continuous and multiplicative. -/
theorem sLocalFiniteInsertion_properties (v : S) :
    let i : (v.val.adicCompletion F)ˣ → Jₛ := finAt(v)
    i 1 = 1 ∧ (∀ x y, i (x * y) = i x * i y) ∧ Continuous i := by
  classical
  let : DecidableEq S := Classical.decEq _
  let B (w : S) := (w.val.adicCompletion F)ˣ
  let q : Iₛ →* Jₛ := QuotientGroup.mk' _
  let i := (q.comp (eProd).symm.toMonoidHom).comp
    ((MonoidHom.inr _ _).comp ((eFin).symm.toMonoidHom.comp (MonoidHom.mulSingle B v)))
  refine ⟨i.map_one, i.map_mul, ?_⟩
  exact QuotientGroup.continuous_mk.comp ((eProd).symm.continuous.comp
    (continuous_const.prodMk ((eFin).symm.continuous.comp (continuous_mulSingle (A := B) v))))

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a local unit at a finite
place restricts an S-local quasi-character to that place. -/
def sLocalFiniteRestriction (v : S) (c : Xₛ) : QuasiCharacter (v.val.adicCompletion F)ˣ :=
  let h := sLocalFiniteInsertion_properties v
  c.comp ⟨{ toFun := finAt(v), map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩

/-- Paper: Equation (3.3.1.3), p. 129. Restriction of a norm twist of the trivial
S-local character to an archimedean place is the same power of the normalized local module. -/
theorem sLocalInfiniteRestriction_normTwist (w : InfinitePlace F) (s : ℂ) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ((1 : PontryaginDual Jₛ)) s) g =
      (modℂ[infiniteNorm(w), g]) ^ s := by
  change (((1 : PontryaginDual Jₛ) (archAt(w) g) : Circle) : ℂ) *
    (modℂ[mₛ, archAt(w) g]) ^ s = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, sIdeleQuotientNorm_mk]
  congr 2
  let x : Iₛ := (eProd).symm ((eArch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w g), 1)
  let ev : (Iₛ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval x))
  change ev (sIdeleNorm F S) = _
  simp only [sIdeleNorm, map_mul, map_prod, map_pow]
  change (∏ w' : InfinitePlace F,
      ‖(((@Pi.mulSingle (InfinitePlace F) (fun u ↦ u.Completionˣ) _ (Classical.decEq _) w g) w' :
        w'.Completionˣ) : w'.Completion)‖ ^
        w'.mult) * ∏ v : S, ‖((1 : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = _
  classical
  rw [Finset.prod_eq_single w (fun w' _ hw' ↦ by rw [Pi.mulSingle_eq_of_ne hw', Units.val_one,
      norm_one, one_pow]) (fun h ↦ absurd (Finset.mem_univ w) h), Pi.mulSingle_eq_same]
  simp

/-- Paper: Equation (3.3.1.3), p. 129. Restriction of the S-idelic norm character
to an archimedean place is the normalized local module. -/
theorem sLocalInfiniteRestriction_norm (w : InfinitePlace F) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ((1 : PontryaginDual Jₛ)) 1) g =
      modℂ[infiniteNorm(w), g] := by
  rw [sLocalInfiniteRestriction_normTwist, Complex.cpow_one]

/-- Paper: Equation (3.3.1.3), p. 129. Restriction of the S-idelic norm character
to a finite place is the normalized local module. -/
theorem sLocalFiniteRestriction_norm (v : S) (g : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (chartₛ((1 : PontryaginDual Jₛ)) 1) g =
      modℂ[finiteNorm(v.val), g] := by
  change (((1 : PontryaginDual Jₛ) (finAt(v) g) : Circle) : ℂ) *
    (modℂ[mₛ, finAt(v) g]) ^ (1 : ℂ) = _
  rw [Complex.cpow_one, PontryaginDual.one_apply, Circle.coe_one, one_mul, sIdeleQuotientNorm_mk]
  congr 1
  let x : Iₛ := (eProd).symm (1, (eFin).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v g))
  let ev : (Iₛ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval x))
  change ev (sIdeleNorm F S) = _
  simp only [sIdeleNorm, map_mul, map_prod, map_pow]
  change (∏ w : InfinitePlace F,
      ‖((1 : w.Completionˣ) : w.Completion)‖ ^ w.mult) * ∏ v' : S,
      ‖(((@Pi.mulSingle S (fun u ↦ (u.val.adicCompletion F)ˣ) _ (Classical.decEq _) v g) v' :
        (v'.val.adicCompletion F)ˣ) :
        v'.val.adicCompletion F)‖ = _
  let : DecidableEq S := Classical.decEq _
  rw [Finset.prod_eq_single v (fun v' _ hv' ↦ by rw [Pi.mulSingle_eq_of_ne hv', Units.val_one,
      norm_one]) (fun h ↦ absurd (Finset.mem_univ v) h), Pi.mulSingle_eq_same]
  simp

/-- Paper: Equation (3.3.1.3), p. 129. The S-local correcting factor multiplies
the local Tate factors on the restricted quasi-characters. -/
def sLocalRhoFactor (c : Xₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalTateFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalTateFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.3), p. 129. With no finite places in S, the correcting
factor is the archimedean product. -/
theorem sLocalRhoFactor_archimedean (c : QuasiCharacter (SIdeleQuotient F ∅)) :
    sLocalRhoFactor c =
      ∏ w : InfinitePlace F, infiniteLocalTateFactor w (sLocalInfiniteRestriction w c) := by
  rw [sLocalRhoFactor, Finset.univ_eq_attach, Finset.attach_empty, Finset.prod_empty, mul_one]

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. The correcting factor is meromorphic
in each norm-twist coordinate. -/
theorem sLocalRhoFactor_meromorphic (χ : PontryaginDual Jₛ) :
    Meromorphic (fun s ↦ sLocalRhoFactor (chartₛ(χ) s)) := by sorry

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. The zeta integral satisfies the
Fourier equation on the strip where both integrals converge. -/
theorem sLocalIdelicZetaIntegral_functionalEquation (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s ∈ criticalStrip) :
    let c := chartₛ(χ) s
    sLocalIdelicZetaIntegral f c =
      sLocalRhoFactor c * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f)
        (dualQuasiCharacter mₛ hmₛ c) := by sorry

/-- The S-idelic module takes a value other than one. -/
private theorem sIdeleQuotientNorm_ne_one' : ∃ x, mₛ x ≠ 1 := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  exact ⟨σ t, (hσ t).trans_ne ht⟩

/-- Paper: Equation (3.1.1.2), p. 119. The abscissa of a norm twist of a unitary
character of J_S is the real part of the exponent. -/
private theorem sLocal_abscissa_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) sIdeleQuotientNorm_ne_one'
      (chartₛ(χ) s) = s.re :=
  quasiCharacterAbscissa_of_unitary_twist mₛ (isProperMap_sIdeleQuotientNorm F S) _ _ χ s
    (fun _ ↦ rfl)

/-- Paper: §3.1.1, p. 119. If two norm-twist charts pass through the same
quasi-character, adding the same increment to both coordinates gives the same
quasi-character again. -/
private theorem sLocal_chart_add_of_eq {χ χ' : PontryaginDual Jₛ} {s s' : ℂ}
    (h : chartₛ(χ) s = chartₛ(χ') s') (z : ℂ) :
    chartₛ(χ) (s + z) = chartₛ(χ') (s' + z) := by
  ext1 g
  have hg := DFunLike.congr_fun h g
  have hn : (modℂ[mₛ, g]) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change (χ g : ℂ) * (modℂ[mₛ, g]) ^ s = (χ' g : ℂ) * (modℂ[mₛ, g]) ^ s' at hg
  change (χ g : ℂ) * (modℂ[mₛ, g]) ^ (s + z) = (χ' g : ℂ) * (modℂ[mₛ, g]) ^ (s' + z)
  rw [Complex.cpow_add _ _ hn, Complex.cpow_add _ _ hn, ← mul_assoc, ← mul_assoc, hg]

/-- Paper: Equation (3.1.1.4), p. 119. Duality in the norm-twist coordinate
takes the inverse unitary character and reflects the exponent. -/
private theorem sLocal_dual_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    dualQuasiCharacter mₛ hmₛ (chartₛ(χ) s) = chartₛ(χ⁻¹) (1 - s) := by
  ext1 g
  let N : ℂ := modℂ[mₛ, g]
  have hN : N ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change N * chartₛ(χ) s g⁻¹ = chartₛ(χ⁻¹) (1 - s) g
  rw [map_inv]
  change N * ((χ g : ℂ) * N ^ s)⁻¹ = ((χ⁻¹ g : Circle) : ℂ) * N ^ (1 - s)
  rw [show ((χ⁻¹ g : Circle) : ℂ) = (χ g : ℂ)⁻¹ from Circle.coe_inv (χ g), mul_inv_rev, Complex.cpow_sub 1 s hN,
    Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem sLocal_eq_of_meromorphicNFOn {G H : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hH : MeromorphicNFOn H univ)
    (h : ∀ z : ℂ, 0 < z.re → G z = H z) (s : ℂ) : G s = H s := by
  have hAt : meromorphicOrderAt (G - H) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  have hOrd := (hG.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s) hAt
  have hNear : G =ᶠ[𝓝[≠] s] H :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  exact (((hG (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))).mp
    hNear).eq_of_nhds

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. Chart continuations of the zeta integral
agree wherever two norm-twist charts pass through the same quasi-character. -/
private theorem sLocalIdelicZetaIntegral_chartContinuation_eq (f : ℬ(Aₛ))
    {χ χ' : PontryaginDual Jₛ} {G G' : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hG' : MeromorphicNFOn G' univ)
    (hGeq : ∀ s : ℂ, 0 < s.re → G s = sLocalIdelicZetaIntegral f (chartₛ(χ) s))
    (hG'eq : ∀ s : ℂ, 0 < s.re → G' s = sLocalIdelicZetaIntegral f (chartₛ(χ') s))
    {s s' : ℂ} (h : chartₛ(χ) s = chartₛ(χ') s') : G s = G' s' := by
  let d := s' - s
  have hRe : s.re = s'.re := by
    rw [← sLocal_abscissa_chart χ s, h, sLocal_abscissa_chart]
  have htw (z : ℂ) : chartₛ(χ') (z + d) = chartₛ(χ) z := by
    have := (sLocal_chart_add_of_eq h (z - s)).symm
    rwa [add_sub_cancel, show s' + (z - s) = z + d by ring] at this
  have hH : MeromorphicNFOn (fun z ↦ G' (z + d)) univ := fun z _ ↦
    (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt (f := G')).mpr (hG' (mem_univ _))
  have hs := sLocal_eq_of_meromorphicNFOn hG hH (fun z hz ↦ by
    have hzd : 0 < (z + d).re := by
      simpa only [d, Complex.add_re, Complex.sub_re, hRe, sub_self, add_zero] using hz
    rw [hGeq z hz, hG'eq _ hzd, htw]) s
  rw [hs]
  change G' (s + (s' - s)) = G' s'
  rw [add_sub_cancel]

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. In each norm-twist coordinate, the zeta integral
on the right half-plane and the correcting factor times the dual zeta integral on the
half-plane left of one glue to a function with a normal-form meromorphic continuation. -/
private theorem sLocalIdelicZetaIntegral_exists_chartContinuation (f : ℬ(Aₛ))
    (χ : PontryaginDual Jₛ) :
    ∃ G : ℂ → ℂ, MeromorphicNFOn G univ ∧
      ∀ s : ℂ, 0 < s.re → G s = sLocalIdelicZetaIntegral f (chartₛ(χ) s) := by
  classical
  let Z (s : ℂ) := sLocalIdelicZetaIntegral f (chartₛ(χ) s)
  let W (s : ℂ) := sLocalRhoFactor (chartₛ(χ) s) *
    sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) (chartₛ(χ⁻¹) (1 - s))
  let M (s : ℂ) := if 0 < s.re then Z s else W s
  have hZ := sLocalIdelicZetaIntegral_analyticOn f χ
  have hZd := sLocalIdelicZetaIntegral_analyticOn (sAdeleSchwartzFourier f) χ⁻¹
  have hρ := sLocalRhoFactor_meromorphic χ
  have hRight : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLeft : IsOpen {s : ℂ | s.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hMZ (s : ℂ) (hs : 0 < s.re) : M =ᶠ[𝓝 s] Z :=
    Filter.mem_of_superset (hRight.mem_nhds hs) fun z hz ↦ if_pos hz
  have hMW (s : ℂ) (hs : s.re < 1) : M =ᶠ[𝓝 s] W := by
    refine Filter.mem_of_superset (hLeft.mem_nhds hs) fun z hz ↦ ?_
    by_cases h0 : 0 < z.re
    · change (if 0 < z.re then Z z else W z) = W z
      rw [if_pos h0]
      have hfe := sLocalIdelicZetaIntegral_functionalEquation f χ z ⟨h0, hz⟩
      simp only at hfe
      rw [sLocal_dual_chart] at hfe
      exact hfe
    · change (if 0 < z.re then Z z else W z) = W z
      rw [if_neg h0]
  have hZan (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ Z s := hZ s hs
  have hWmer (s : ℂ) (hs : s.re < 1) : MeromorphicAt W s := by
    have h1 : (1 - s) ∈ rightHalf := by
      change 0 < (1 - s).re
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hA : AnalyticAt ℂ (fun z : ℂ ↦ sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f)
        (chartₛ(χ⁻¹) (1 - z))) s :=
      (hZd (1 - s) h1).comp (by fun_prop)
    exact (hρ s).mul hA.meromorphicAt
  have hM : MeromorphicOn M univ := by
    intro s _
    by_cases hs : 0 < s.re
    · exact (hZan s hs).meromorphicAt.congr
        ((hMZ s hs).symm.filter_mono nhdsWithin_le_nhds)
    · have hs' : s.re < 1 := by linarith [not_lt.mp hs]
      exact (hWmer s hs').congr ((hMW s hs').symm.filter_mono nhdsWithin_le_nhds)
  refine ⟨toMeromorphicNFOn M univ, meromorphicNFOn_toMeromorphicNFOn M univ, fun s hs ↦ ?_⟩
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr ((hZan s hs).congr (hMZ s hs).symm).meromorphicNFAt]
  exact if_pos hs

/-- Paper: Equation (3.1.1.2), p. 119. Every quasi-character of J_S is a norm twist of a
unitary character, with real exponent its abscissa. -/
private theorem sLocal_exists_chart (c : Xₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), c = chartₛ(χ) s := by
  have : IsClosed ((Subgroup.map (Units.map (RingHom.toMonoidHom (RingHom.comp
      (adeleProjection F S) (Subring.subtype (integralAdelesOutside F S)))))
      (MonoidHom.range (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))) :
        Set Iₛ) := by
    let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
    let d := p.comp (integralAdeleDiagonal F S)
    obtain ⟨hd, hc, _⟩ := sAdele_additive_quotient F S
    rw [MonoidHom.map_range]
    exact isClosed_range_unitsMap d.toMonoidHom hd hc
  have : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have hp := isProperMap_sIdeleQuotientNorm F S
  let a := quasiCharacterAbscissa mₛ hp sIdeleQuotientNorm_ne_one' c
  have hnorm := norm_quasiCharacter_eq_rpow_abscissa mₛ hp sIdeleQuotientNorm_ne_one' c
  let q : Xₛ := c * chartₛ((1 : PontryaginDual Jₛ)) (-(a : ℂ))
  have hmod (g : Jₛ) : 0 < ((mₛ g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hq (g : Jₛ) : ‖q g‖ = 1 := by
    change ‖c g * ((((1 : PontryaginDual Jₛ) g : Circle) : ℂ) * (modℂ[mₛ, g]) ^ (-(a : ℂ)))‖ = 1
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, hnorm,
      Complex.norm_cpow_eq_rpow_re_of_pos (hmod g), Complex.neg_re, Complex.ofReal_re,
      ← Real.rpow_add (hmod g), add_neg_cancel, Real.rpow_zero]
  let χ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨q g, mem_sphere_zero_iff_norm.mpr (hq g)⟩
      map_one' := Circle.ext (map_one q)
      map_mul' := fun g h ↦ Circle.ext (map_mul q g h)
      continuous_toFun := q.continuous.subtype_mk _ }
  refine ⟨χ, a, ?_⟩
  ext1 g
  have hn : (modℂ[mₛ, g]) ≠ 0 := Complex.ofReal_ne_zero.mpr (hmod g).ne'
  change c g = (c g * ((((1 : PontryaginDual Jₛ) g : Circle) : ℂ) *
    (modℂ[mₛ, g]) ^ (-(a : ℂ)))) * (modℂ[mₛ, g]) ^ (a : ℂ)
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, mul_assoc, ← Complex.cpow_add _ _ hn,
    neg_add_cancel, Complex.cpow_zero, mul_one]

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The zeta integral has a unique
meromorphic continuation in normal form on each norm-twist coordinate. -/
theorem sLocalIdelicZetaIntegral_exists_continuation (f : ℬ(Aₛ)) :
    ∃! Z : Xₛ → ℂ, (∀ χ : PontryaginDual Jₛ,
      MeromorphicNFOn (fun s ↦ Z (chartₛ(χ) s)) univ) ∧
      EqOn Z (sLocalIdelicZetaIntegral f) positive := by
  classical
  choose G hGNF hGeq using sLocalIdelicZetaIntegral_exists_chartContinuation f
  choose χc sc hc using sLocal_exists_chart (F := F) (S := S)
  let Z : Xₛ → ℂ := fun c ↦ G (χc c) (sc c)
  have hZ (χ : PontryaginDual Jₛ) (s : ℂ) : Z (chartₛ(χ) s) = G χ s :=
    sLocalIdelicZetaIntegral_chartContinuation_eq f (hGNF _) (hGNF χ) (hGeq _) (hGeq χ)
      (hc (chartₛ(χ) s)).symm
  refine ⟨Z, ⟨fun χ ↦ ?_, fun c hc' ↦ ?_⟩, fun Z' ⟨hZ'NF, hZ'eq⟩ ↦ funext fun c ↦ ?_⟩
  · simpa only [hZ] using hGNF χ
  · obtain ⟨χ, s, hs, rfl⟩ := hc'
    exact (hZ χ s).trans (hGeq χ s hs)
  · rw [hc c, hZ]
    refine sLocal_eq_of_meromorphicNFOn (hZ'NF (χc c)) (hGNF (χc c)) (fun z hz ↦ ?_) (sc c)
    exact (hZ'eq ⟨χc c, z, hz, rfl⟩).trans (hGeq _ z hz).symm

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The S-local Z-function is the
meromorphic continuation of the zeta integral. -/
def sLocalIdelicZFunction (f : ℬ(Aₛ)) : Xₛ → ℂ :=
  (sLocalIdelicZetaIntegral_exists_continuation f).exists.choose

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. On the half-plane of convergence,
the continuation agrees with the defining integral. -/
theorem sLocalIdelicZFunction_eq_integral (f : ℬ(Aₛ)) :
    EqOn (sLocalIdelicZFunction f) (sLocalIdelicZetaIntegral f) positive :=
  (sLocalIdelicZetaIntegral_exists_continuation f).exists.choose_spec.2

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The S-local Z-function is
meromorphic in normal form in each norm-twist coordinate. -/
theorem sLocalIdelicZFunction_meromorphic (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    MeromorphicNFOn (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ :=
  (sLocalIdelicZetaIntegral_exists_continuation f).exists.choose_spec.1 χ

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. Every pole of the Z-function
lies at a pole of the correcting factor and has at most its pole order. -/
theorem sLocalIdelicZFunction_poles (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) :
    min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) s) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) s := by sorry

local notation "diagₛ" =>
  Subgroup.map (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (MonoidHom.range (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

/-- The product σ-algebra on the S-adeles is the Borel σ-algebra. -/
theorem sAdeleRing_borelSpace : BorelSpace Aₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  exact inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))

/-- The σ-algebra on the S-ideles pulled back from the S-adeles is their Borel σ-algebra,
because the S-ideles carry the subspace topology. -/
theorem sIdeleGroup_borelSpace : BorelSpace Iₛ := by
  have := sAdeleRing_borelSpace (F := F) (S := S)
  refine ⟨?_⟩
  rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

/-- Paper: Equation (3.1.2.1), p. 120. The projected diagonal S-units are closed in the
S-ideles. -/
theorem isClosed_sProjectedDiagonal : IsClosed (diagₛ : Set Iₛ) := by
  let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
  let d := p.comp (integralAdeleDiagonal F S)
  obtain ⟨hd, hc, _⟩ := sAdele_additive_quotient F S
  rw [MonoidHom.map_range]
  exact isClosed_range_unitsMap d.toMonoidHom hd hc

/-- Paper: Equation (3.1.2.1), p. 120. The projected diagonal S-units are discrete, since
they lie in the discrete diagonal S-integers. -/
theorem discreteTopology_sProjectedDiagonal : DiscreteTopology (diagₛ : Subgroup Iₛ) := by
  let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
  let d := p.comp (integralAdeleDiagonal F S)
  obtain ⟨hd, -, hdisc, _⟩ := sAdele_additive_quotient F S
  let : DiscreteTopology (Set.range d) := isDiscrete_iff_discreteTopology.mp hdisc
  let f : (diagₛ : Subgroup Iₛ) → Set.range d := fun x ↦ ⟨x.val.val, by
    obtain ⟨_, ⟨u, rfl⟩, hx⟩ := x.prop
    exact ⟨u.val, by rw [← hx]; rfl⟩⟩
  exact .of_continuous_injective (f := f)
    (continuous_induced_rng.2 (Units.continuous_val.comp continuous_subtype_val))
    (fun x y h ↦ Subtype.ext (Units.ext (congrArg Subtype.val h)))

/-- Paper: Definition A.3.2.2(2), p. 560. The finite local multiplicative Tamagawa
measure is a Haar measure on the local unit group. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (v : Primes) :
    (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure := by
  let : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : LocallyCompactSpace (v.adicCompletion F)ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  let U : Set (v.adicCompletion F)ˣ := (v.adicCompletionIntegers F).units
  have hO : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact U := by
    have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    convert isCompact_closedBall (0 : v.adicCompletion F) 1 using 1
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
  have hmass := hO.measure_pos μ ⟨1, (v.adicCompletionIntegers F).units.one_mem⟩
  have hnorm : 0 < (v.asIdeal.absNorm : ℝ) :=
    Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hsqrt := Real.sqrt_pos_of_pos (pow_pos hnorm
    (multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))))
  unfold finiteLocalMultiplicativeTamagawaMeasure
  exact Measure.IsHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      hK.measure_ne_top (μ := μ)⟩)
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne') hmass.ne')

omit [NumberField F] in
/-- Paper: Definition A.3.2.2(1), p. 560. The archimedean local multiplicative Tamagawa
measure `dx / |x|ᵥ` is a Haar measure on the local unit group. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (w : InfinitePlace F) :
    (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let := infiniteLocalAdditiveTamagawaMeasure_haar F w
  unfold infiniteLocalMultiplicativeTamagawaMeasure
  apply isHaarMeasure_comap_units_withDensity
  intro a ha
  by_cases h : w.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    let e := (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm
    have he : Measurable e := (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.continuous.measurable
    rw [map_mul_left_map_ringEquiv e he volume _ real_map_mul_left_volume a ha, h.mult_eq_one]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero (map_zero _) a
    rw [hn]
  · have h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex h').symm
    have he : Measurable e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex h').symm.continuous.measurable
    have hscale (b : ℂ) (hb : b ≠ 0) : ((2 : ℕ) • (volume : Measure ℂ)).map (b * ·) =
        (((‖b‖₊ ^ 2 : ℝ≥0) : ENNReal))⁻¹ • ((2 : ℕ) • (volume : Measure ℂ)) := by
      rw [Measure.map_smul, complex_map_mul_left_volume b hb, ← Nat.cast_smul_eq_nsmul ENNReal,
        ← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, smul_smul, mul_comm]
      exact (measurable_const_mul b).aemeasurable
    rw [map_mul_left_map_ringEquiv e he _ _ hscale a ha, h'.mult_eq_two]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
    rw [hn]

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa measure is a
Haar measure on the S-ideles. -/
theorem sMultiplicativeTamagawaMeasure_isHaarMeasure : (μₛ).IsHaarMeasure := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := by
    refine ⟨?_⟩
    rw [Units.isEmbedding_val₀.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
    rfl
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) w
  let (v : S) := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v.val
  have := sIdeleGroup_borelSpace (F := F) (S := S)
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eInf := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let E := (ContinuousMulEquiv.mk' (eInf.symm.toHomeomorph.prodCongr eS.symm.toHomeomorph)
    (fun x y ↦ Prod.ext (map_mul eInf.symm x.1 y.1) (map_mul eS.symm x.2 y.2))).trans e.symm
  change (Measure.map E _).IsHaarMeasure
  have h1 : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  have h2 : (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  have h3 : ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val))).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure _ _
  exact E.isHaarMeasure_map _

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa measure is
regular. -/
theorem sMultiplicativeTamagawaMeasure_regular : (μₛ).Regular := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hind := (sIdeleGroup_description F S).1
  have hemb : Topology.IsEmbedding (Units.val : Iₛ → Aₛ) := ⟨hind, Units.val_injective⟩
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : TopologicalSpace.MetrizableSpace Aₛ := inferInstanceAs (TopologicalSpace.MetrizableSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := hind.secondCountableTopology
  let : TopologicalSpace.MetrizableSpace Iₛ := hemb.metrizableSpace
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  infer_instance

/-- Paper: Theorem 3.3.1.1(2), p. 129. Weil's formula with counting measure
on the diagonal S-units determines the quotient Tamagawa measure. -/
theorem sLocalQuotientTamagawaMeasure_existsUnique :
    ∃! ν : Measure Jₛ, IsWeilQuotientMeasure _ μₛ Measure.count ν := by
  let : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  let := sMultiplicativeTamagawaMeasure_regular (F := F) (S := S)
  let : DiscreteTopology (diagₛ : Subgroup Iₛ) := discreteTopology_sProjectedDiagonal
  let : (Measure.count : Measure (diagₛ : Subgroup Iₛ)).IsHaarMeasure :=
    count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure (diagₛ : Subgroup Iₛ)).Regular :=
    count_regular_of_discreteTopology
  exact weilQuotientMeasure_existsUnique _ isClosed_sProjectedDiagonal μₛ Measure.count

/-- Paper: Equation (3.3.1.4), p. 129. The measure on the S-idele quotient
is Weil's quotient measure for the product measure and counting measure.
Deviation: The quotient here is J as specified in §3.3.1 and §3.1.2. -/
def sLocalQuotientTamagawaMeasure (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Measure (SIdeleQuotient F S) :=
  (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).exists.choose

local notation "μJ" => sLocalQuotientTamagawaMeasure F S

/-- Paper: Theorem 3.3.1.1(2), p. 129. The quotient measure satisfies the
Weil normalization for integrals against the product measure on the S-ideles. -/
theorem sLocalQuotientTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure _ μₛ Measure.count μJ :=
  (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).exists.choose_spec

/-- Paper: Equation (3.3.1.4), p. 129. The theta Mellin integral weights
the S-local theta function by the quasi-character on the S-idele quotient. -/
def sLocalThetaMellinIntegral (f : ℬ(Aₛ)) (c : Xₛ) : ℂ :=
  ∫ g : Jₛ, sLocalAdelicThetaOnClasses F S f g * c g ∂μJ

/-- Paper: Theorem 3.3.1.1(2)–(3), p. 129. The theta Mellin integral
unfolds to the zeta integral on the positive half-plane. -/
theorem sLocalThetaMellinIntegral_eq_zeta (f : ℬ(Aₛ)) :
    EqOn (sLocalThetaMellinIntegral f) (sLocalIdelicZetaIntegral f) positive := by sorry

/-- Paper: Theorem 3.3.1.1(2), p. 129. The theta Mellin integrand is
absolutely integrable on the positive half-plane. -/
theorem sLocalThetaMellinIntegral_integrable (f : ℬ(Aₛ)) (c : Xₛ) (hc : c ∈ positive) :
    Integrable (fun g : Jₛ ↦ sLocalAdelicThetaOnClasses F S f g * c g) μJ := by sorry

/-- Paper: Theorem 3.3.1.1(2) and Remark 3.3.1.2, p. 129. The theta Mellin
integral converges uniformly on compact subsets under norm-band truncation.
Deviation: The positive band widths are indexed by n + 1. -/
theorem sLocalThetaMellinIntegral_tendstoUniformlyOn (f : ℬ(Aₛ))
    (K : Set Xₛ) (hK : IsCompact K) (hKpos : K ⊆ positive) :
    TendstoUniformlyOn (fun (n : ℕ) c ↦
      ∫ g in band[mₛ, n], sLocalAdelicThetaOnClasses F S f g * c g ∂μJ)
      (sLocalThetaMellinIntegral f) atTop K := by sorry

/-- Paper: Theorem 3.3.1.1(2), p. 129. The theta Mellin integral is
holomorphic on the positive half-plane in each norm-twist coordinate. -/
theorem sLocalThetaMellinIntegral_analyticOn (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalThetaMellinIntegral f (chartₛ(χ) s)) rightHalf := by
  exact AnalyticOnNhd.congr (isOpen_Ioi.preimage Complex.continuous_re)
    (sLocalIdelicZetaIntegral_analyticOn f χ)
    (fun s hs ↦ (sLocalThetaMellinIntegral_eq_zeta f ⟨χ, s, hs, rfl⟩).symm)

local notation "normProduct(" τ ")" =>
  (fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * classOf (τ x.2))

/-- Paper: Theorem 3.3.1.1(3), p. 129. The product of Haar measure on
the norm-one group with dt/t transports to the quotient Tamagawa measure. -/
theorem sLocalNormOneQuotientMeasure_existsUnique :
    ∃! ν : Measure J₁, ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) →
        (ν.prod positiveRealHaar).map (normProduct(τ)) = μJ := by
  -- Topology and measurability of the S-ideles and their quotient.
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hind := (sIdeleGroup_description F S).1
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := hind.secondCountableTopology
  let : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have : IsClosed (diagₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have : BorelSpace Jₛ := ⟨rfl⟩
  have : BorelSpace J₁ := ⟨rfl⟩
  have hmc : Continuous mₛ := hmₛ
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hμJ := sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)
  have : (μJ).IsHaarMeasure := hμJ.1
  -- Probability Haar measure on the compact norm-one group.
  let ν₀ : Measure J₁ := Measure.haarMeasure ⊤
  have hν₀ : ν₀ univ = 1 := Measure.haarMeasure_self
  -- A norm section through one infinite place.
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ₀ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩
  have hτ₀ : RightInverse τ₀ (sIdeleNorm F S) := by
    intro t
    let A := integralAdelesOutside F S
    have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
      simp only [A, integralAdelesOutside, Subring.mem_iInf]
      intro v _
      exact (v.adicCompletionIntegers F).one_mem
    have ht : s t ∈ A.toSubmonoid.units :=
      ⟨hmem t, by
        change ((s t)⁻¹).val ∈ A
        rw [← map_inv]
        exact hmem t⁻¹⟩
    let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
    exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)
  -- For each section, multiplication identifies the product with the quotient.
  have hnorm (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (t : ℝ≥0ˣ) :
      mₛ (classOf (τ t)) = t := (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  let E (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) : (J₁ × ℝ≥0ˣ) ≃ₜ* Jₛ :=
    { toFun := normProduct(τ)
      invFun := fun y ↦ (⟨y * (classOf (τ (mₛ y)))⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnorm τ hτ, mul_inv_cancel]⟩, mₛ y)
      left_inv := fun x ↦ by
        have hk : mₛ (x.1 : Jₛ) = 1 := x.1.property
        have hx : mₛ ((x.1 : Jₛ) * classOf (τ x.2)) = x.2 := by
          rw [map_mul, hk, one_mul, hnorm τ hτ]
        refine Prod.ext (Subtype.ext ?_) hx
        change (x.1 : Jₛ) * classOf (τ x.2) *
          (classOf (τ (mₛ ((x.1 : Jₛ) * classOf (τ x.2)))))⁻¹ = x.1
        rw [hx, mul_inv_cancel_right]
      right_inv := fun y ↦ by simp
      map_mul' := fun x y ↦ by
        change ((x.1 * y.1 : J₁) : Jₛ) * classOf (τ (x.2 * y.2)) =
          ((x.1 : Jₛ) * classOf (τ x.2)) * ((y.1 : Jₛ) * classOf (τ y.2))
        rw [map_mul, QuotientGroup.mk_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _
      continuous_toFun := by
        have : Continuous (classOf) := QuotientGroup.continuous_mk
        fun_prop
      continuous_invFun := by
        have : Continuous (classOf) := QuotientGroup.continuous_mk
        refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hmc
        exact continuous_id.mul ((this.comp (τ.continuous.comp hmc)).inv) }
  let M (τ : ℝ≥0ˣ →ₜ* Iₛ) : Measure Jₛ := (ν₀.prod positiveRealHaar).map (normProduct(τ))
  have hMH (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) : (M τ).IsHaarMeasure :=
    (E τ hτ).isHaarMeasure_map (ν₀.prod positiveRealHaar)
  -- The band of norms between one and e has mass one for each of these measures.
  let T : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hTm : MeasurableSet T :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
  have hPRT : positiveRealHaar T = 1 := by
    let T₀ : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have hT₀ : ((T₀.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval T₀ (by rw [hT₀]; exact Real.one_le_exp zero_le_one)
    rw [hT₀, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  let B : Set Jₛ := mₛ ⁻¹' T
  have hBm : MeasurableSet B := hmc.measurable hTm
  have hMB (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) : M τ B = 1 := by
    have hφ : Continuous (normProduct(τ)) := (E τ hτ).continuous
    rw [Measure.map_apply hφ.measurable hBm]
    have hpre : normProduct(τ) ⁻¹' B = univ ×ˢ T := by
      ext ⟨k, t⟩
      have hk : mₛ (k : Jₛ) = 1 := k.property
      change mₛ ((k : Jₛ) * classOf (τ t)) ∈ T ↔ _
      rw [map_mul, hk, one_mul, hnorm τ hτ]
      simp
    rw [hpre, Measure.prod_prod, hν₀, one_mul, hPRT]
  -- Every such measure is the same multiple of the quotient Tamagawa measure.
  have hscale (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
      μJ = μJ B • M τ := by
    have := hMH τ hτ
    have h := Measure.isMulLeftInvariant_eq_smul μJ (M τ)
    have hB := congrArg (fun ν : Measure Jₛ ↦ ν B) h
    simp only [smul_apply, ENNReal.smul_def, smul_eq_mul, hMB τ hτ, mul_one] at hB
    rw [hB, ← ENNReal.smul_def]
    exact h
  have hTcpt : IsCompact T := by
    let h := Nonneg.unitsHomeomorphPos ℝ
    have hK : IsCompact {y : {x : ℝ // 0 < x} | y.val ∈ Icc 1 (Real.exp 1)} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert isCompact_Icc (a := (1 : ℝ)) (b := Real.exp 1) using 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, by linarith [hx.1]⟩, hx, rfl⟩
    have hTeq : T = h ⁻¹' {y | y.val ∈ Icc 1 (Real.exp 1)} := rfl
    rw [hTeq, ← h.image_symm]
    exact hK.image h.symm.continuous
  have hBtop : μJ B ≠ ⊤ :=
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage hTcpt).measure_lt_top.ne
  have hB0 : μJ B ≠ 0 := by
    intro h
    have h' := hscale τ₀ hτ₀
    rw [h, zero_smul] at h'
    exact NeZero.ne μJ h'
  have hmap (c : ENNReal) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
      ((c • ν₀).prod positiveRealHaar).map (normProduct(τ)) = c • M τ := by
    have hφ : Continuous (normProduct(τ)) := (E τ hτ).continuous
    rw [Measure.prod_smul_left, Measure.map_smul _ hφ.aemeasurable]
  refine ⟨μJ B • ν₀, ⟨Measure.IsHaarMeasure.smul _ hB0 hBtop, Measure.Regular.smul hBtop,
    fun τ hτ ↦ (hmap _ τ hτ).trans (hscale τ hτ).symm⟩, ?_⟩
  rintro ν' ⟨hν'H, hν'R, hν'⟩
  have : SecondCountableTopology J₁ := TopologicalSpace.Subtype.secondCountableTopology _
  have h := Measure.isMulLeftInvariant_eq_smul ν' ν₀
  have hm' := hν' τ₀ hτ₀
  rw [h, ENNReal.smul_def, hmap _ τ₀ hτ₀] at hm'
  have hd := congrArg (fun ν : Measure Jₛ ↦ ν B) hm'
  simp only [smul_apply, hMB τ₀ hτ₀, smul_eq_mul, mul_one] at hd
  rw [h, ENNReal.smul_def, hd]

/-- Paper: Theorem 3.3.1.1(3), p. 129. Normalize Haar measure on the
norm-one S-idele quotient by splitting the quotient measure against dt/t. -/
def sLocalNormOneQuotientMeasure (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Measure (sIdeleQuotientNorm F S).ker :=
  (sLocalNormOneQuotientMeasure_existsUnique (F := F) (S := S)).exists.choose

local notation "μJ₁" => sLocalNormOneQuotientMeasure F S

/-- Paper: Theorem 3.3.1.1(3), p. 129. Multiplication using any norm
section pushes the product with dt/t to the quotient Tamagawa measure. -/
theorem sLocalNormOneQuotientMeasure_normProduct :
    (μJ₁).IsHaarMeasure ∧ ∀ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) →
      ((μJ₁).prod positiveRealHaar).map (normProduct(τ)) = μJ :=
  have h := (sLocalNormOneQuotientMeasure_existsUnique (F := F) (S := S)).exists.choose_spec
  ⟨h.1, h.2.2⟩

section Homogeneous

local instance : Measure.IsHaarMeasure μJ₁ :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

local notation "ωOf(" χ ")" => (χ : PontryaginDual Jₛ).comp
  (⟨Subgroup.subtype (mₛ).ker, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)
local notation "radial[" τ "," f "," χ "," s "]" => (fun t : ℝ≥0ˣ ↦
  sLocalHomogeneousAdelicTheta F S μJ₁ (ωOf(χ)) f (classOf (τ t)) * chartₛ(χ) s (classOf (τ t)))

/-- Paper: Equation (3.3.1.5), p. 129. The radial Mellin integral is the
dt/t integral of the homogeneous theta term times the section's character. -/
def sLocalRadialMellinIntegral (τ : ℝ≥0ˣ →ₜ* Iₛ) (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) : ℂ :=
  ∫ t : ℝ≥0ˣ, radial[τ, f, χ, s] t ∂positiveRealHaar

/-- Paper: Theorem 3.3.1.1(3), p. 129. On the positive half-plane the
radial integral agrees with the quotient theta Mellin integral. -/
theorem sLocalRadialMellinIntegral_eq_theta
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ rightHalf) :
    sLocalRadialMellinIntegral τ f χ s = sLocalThetaMellinIntegral f (chartₛ(χ) s) := by sorry

/-- Paper: Theorem 3.3.1.1(3), p. 129. The radial Mellin integrand is
absolutely integrable for each positive abscissa. -/
theorem sLocalRadialMellinIntegral_integrable
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ rightHalf) :
    Integrable (radial[τ, f, χ, s]) positiveRealHaar := by
  let c := chartₛ(χ) s
  let G (g : Jₛ) := sLocalAdelicThetaOnClasses F S f g * c g
  have hG : Integrable G μJ := sLocalThetaMellinIntegral_integrable f c ⟨χ, s, hs, rfl⟩
  rw [← (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ] at hG
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let e : ℝ ≃ₜ ℝ≥0ˣ :=
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (x : ℝ) : e x = Units.mk0 (Real.exp x).toNNReal (by positivity) := by
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  let : SigmaFinite positiveRealHaar := by
    unfold positiveRealHaar
    rw [← funext he]
    exact e.toMeasurableEquiv.sigmaFinite_map
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : SecondCountableTopology Jₛ := inferInstance
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have hm : Measurable (normProduct(τ)) :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul
      ((QuotientGroup.continuous_mk.comp τ.continuous).measurable.comp measurable_snd)
  have hprod := hG.comp_aemeasurable hm.aemeasurable
  refine hprod.integral_prod_right.congr (.of_forall fun t ↦ ?_)
  change (∫ h : J₁, G (h.val * classOf (τ t)) ∂μJ₁) = radial[τ, f, χ, s] t
  simp only [sLocalHomogeneousAdelicTheta, IsLinearMap.mk'_apply, ContinuousMap.coe_mk]
  rw [← integral_mul_const]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  have hker : c h.val = (χ h.val : ℂ) := by
    change (χ h.val : ℂ) * modℂ[mₛ, h.val] ^ s = (χ h.val : ℂ)
    rw [MonoidHom.mem_ker.mp h.property]
    simp
  change sLocalAdelicThetaOnClasses F S f (h.val * classOf (τ t)) *
      c (h.val * classOf (τ t)) =
    (sLocalAdelicThetaOnClasses F S f (classOf (τ t) * h.val) * (χ h.val : ℂ)) *
      c (classOf (τ t))
  rw [map_mul c, hker, mul_assoc, mul_comm h.val]

/-- Paper: Theorem 3.3.1.1(3) and Remark 3.3.1.2, p. 129. The radial integral
truncated to closed norm bands converges uniformly on compact subsets of each
positive component.
Deviation: The compact sets are taken in a fixed norm-twist component. -/
theorem sLocalRadialMellinIntegral_tendstoUniformlyOn
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (K : Set ℂ) (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) s ↦
      ∫ t in band[MonoidHom.id ℝ≥0ˣ, n], radial[τ, f, χ, s] t ∂positiveRealHaar)
      (sLocalRadialMellinIntegral (F := F) (S := S) τ f χ) atTop K := by sorry

/-- Paper: Theorem 3.3.1.1(3), p. 129. The radial Mellin integral is
holomorphic on each positive norm-twist half-plane. -/
theorem sLocalRadialMellinIntegral_analyticOn
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (sLocalRadialMellinIntegral (F := F) (S := S) τ f χ) rightHalf := by
  exact AnalyticOnNhd.congr (isOpen_Ioi.preimage Complex.continuous_re)
    (sLocalThetaMellinIntegral_analyticOn f χ)
    (fun s hs ↦ (sLocalRadialMellinIntegral_eq_theta τ hτ f χ s hs).symm)

end Homogeneous

/-- Paper: Lemma 3.3.1.3, p. 130. At each quasi-character of positive
abscissa, zeta integration is a continuous linear functional in the test function. -/
theorem sLocalIdelicZetaIntegral_tempered (c : Xₛ) (hc : c ∈ positive) :
    ∃ Z : ℬ(Aₛ) →L[ℂ] ℂ, ∀ f : ℬ(Aₛ), Z f = sLocalIdelicZetaIntegral f c := by sorry


/-- Paper: Remark 3.3.1.4, p. 131. On a pure tensor the S-local zeta
functional is the product of the local zeta functionals.
Deviation: Pointwise factorization specifies the pure tensors. -/
theorem sLocalIdelicZetaIntegral_pureTensor (c : Xₛ) (hc : c ∈ positive)
    (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
    (fFin : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, fFin v (Multiplicative.ofAdd (x.2 v))) :
    sLocalIdelicZetaIntegral f c =
      (∏ w : InfinitePlace F, localIdelicZetaIntegral
        (infiniteLocalMultiplicativeTamagawaMeasure F w) (fun x ↦ fArch w (Multiplicative.ofAdd x))
        (sLocalInfiniteRestriction w c)) *
      ∏ v : S, localIdelicZetaIntegral
        (finiteLocalMultiplicativeTamagawaMeasure F v.val) (fun x ↦ fFin v (Multiplicative.ofAdd x))
        (sLocalFiniteRestriction v c) := by sorry

/-- Paper: Remark 3.3.1.4, p. 131. The zeta functional is determined among
continuous linear functionals by its product formula on pure tensors.
Deviation: The completed tensor functional is characterized by its continuous
extension property on the S-adelic test space itself. -/
theorem sLocalIdelicZetaIntegral_eq_of_pureTensor (c : Xₛ) (hc : c ∈ positive)
    (Z : ℬ(Aₛ) →L[ℂ] ℂ)
    (hZ : ∀ (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
      (fFin : (v : S) → ℬ(v.val.adicCompletion F)),
      (∀ x : Aₛ, f (Multiplicative.ofAdd x) =
        (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
          ∏ v : S, fFin v (Multiplicative.ofAdd (x.2 v))) →
      Z f = sLocalIdelicZetaIntegral f c) (f : ℬ(Aₛ)) :
    Z f = sLocalIdelicZetaIntegral f c := by sorry

/-! ## The correcting factor -/

/-- Paper: Proposition 3.3.1.5(1), p. 132. The product of the factors for
dual quasi-characters is the value of the quasi-character at minus one.
Deviation: Equality is in the codiscrete filter of each norm-twist coordinate. -/
theorem sLocalRhoFactor_mul_dual (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalRhoFactor c * sLocalRhoFactor (dualQuasiCharacter mₛ hmₛ c) =
        c (classOf (-1 : Iₛ)) := by sorry

/-- Paper: Proposition 3.3.1.5(1), p. 132. Conjugating the quasi-character
conjugates its factor and multiplies by the character at minus one.
Deviation: The conjugate character uses the inverse unitary base and the
conjugate exponent. Equality holds off a discrete set of exponents. -/
theorem sLocalRhoFactor_conj (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      sLocalRhoFactor (chartₛ(χ⁻¹) (star s)) =
        chartₛ(χ) s (classOf (-1 : Iₛ)) * star (sLocalRhoFactor (chartₛ(χ) s)) := by sorry

/-- Paper: Proposition 3.3.1.5(2), p. 132. On the critical line the correcting
factor is regular. -/
theorem sLocalRhoFactor_analyticAt_criticalLine (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s.re = 1 / 2) :
    AnalyticAt ℂ (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) s := by sorry

/-- Paper: Proposition 3.3.1.5(2), p. 132. On the critical line the correcting
factor has modulus one. -/
theorem sLocalRhoFactor_norm_criticalLine (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s.re = 1 / 2) :
    ‖sLocalRhoFactor (chartₛ(χ) s)‖ = 1 := by sorry

/-- Paper: Proposition 3.3.1.5(3), p. 132. Every complex derivative of the
correcting factor is holomorphic on the positive half-plane. -/
theorem sLocalRhoFactor_iteratedDeriv_analyticOn (χ : PontryaginDual Jₛ) (k : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv k (fun z ↦ sLocalRhoFactor (chartₛ(χ) z))) rightHalf :=
  by sorry

-- TODO(paper-gap): The bound (3.3.1.11) omits the archimedean degrees when
-- multiplying local factors. For F = ℚ(i), no finite places, and k = 0, the
-- trivial chart at Re(s) = 1 has growth of order |Im(s)|, rather than |Im(s)|^1/2.

-- This pass ends before the definition of the partial Euler product (3.3.1.25), p. 134.

end RiemannMasullo
