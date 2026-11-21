module

public import RiemannMasullo.Ch02_AdelicTheta.Sec4
public import RiemannMasullo.Ch03_IdelicZeta.Sec2

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

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

/-- Paper: Theorem 3.3.1.1(1), p. 129. The S-idele integrand is absolutely
integrable on the positive half-plane. -/
theorem sLocalIdelicZetaIntegral_integrable (f : ℬ(Aₛ)) (c : Xₛ) (hc : c ∈ positive) :
    Integrable (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val) * c (classOf g)) μₛ := by sorry

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
      (sLocalIdelicZetaIntegral f) atTop K := by sorry

/-- Paper: Theorem 3.3.1.1(1), p. 129. The zeta integral is holomorphic in
every norm-twist coordinate on the right half-plane. -/
theorem sLocalIdelicZetaIntegral_analyticOn (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZetaIntegral f (chartₛ(χ) s)) rightHalf := by sorry

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

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The zeta integral has a unique
meromorphic continuation in normal form on each norm-twist coordinate. -/
theorem sLocalIdelicZetaIntegral_exists_continuation (f : ℬ(Aₛ)) :
    ∃! Z : Xₛ → ℂ, (∀ χ : PontryaginDual Jₛ,
      MeromorphicNFOn (fun s ↦ Z (chartₛ(χ) s)) univ) ∧
      EqOn Z (sLocalIdelicZetaIntegral f) positive := by sorry

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


/-- Paper: Theorem 3.3.1.1(2), p. 129. Weil's formula with counting measure
on the diagonal S-units determines the quotient Tamagawa measure. -/
theorem sLocalQuotientTamagawaMeasure_existsUnique :
    ∃! ν : Measure Jₛ, IsWeilQuotientMeasure _ μₛ Measure.count ν := by sorry

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
    AnalyticOnNhd ℂ (fun s ↦ sLocalThetaMellinIntegral f (chartₛ(χ) s)) rightHalf := by sorry

local notation "normProduct(" τ ")" =>
  (fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * classOf (τ x.2))

/-- Paper: Theorem 3.3.1.1(3), p. 129. The product of Haar measure on
the norm-one group with dt/t transports to the quotient Tamagawa measure. -/
theorem sLocalNormOneQuotientMeasure_existsUnique :
    ∃! ν : Measure J₁, ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) →
        (ν.prod positiveRealHaar).map (normProduct(τ)) = μJ := by sorry

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
    Integrable (radial[τ, f, χ, s]) positiveRealHaar := by sorry

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
    AnalyticOnNhd ℂ (sLocalRadialMellinIntegral (F := F) (S := S) τ f χ) rightHalf := by sorry

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
