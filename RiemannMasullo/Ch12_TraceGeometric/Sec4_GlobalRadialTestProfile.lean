module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RadialTestProfile
import RiemannMasullo.Ch12_TraceGeometric.Sec4
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Prod

/-! # The logarithmic profile of a global trace test -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "Hₛ" => sProjectedDiagonal F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "expLog" => fun r : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd r)

attribute [local instance] instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1
  instSIdeleLocallyCompactSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientHaarMeasureSec1 instSIdeleQuotientSecondCountableSec1

local instance instGlobalRadialTestProfileSIdeleT2 : T2Space Iₛ :=
  (sIdeleGroup_description F S).2.1
local instance instGlobalRadialTestProfileNormOneMeasurable : MeasurableSpace J₁ := borel _
local instance instGlobalRadialTestProfileUnitsBorel : BorelSpace ℝ≥0ˣ :=
  borelSpace_units_of_continuousInv₀ _

/-- Paper: (12.4.1.4), p. 515. The compact lift of an outside-unit-invariant
global test periodizes to its compact Bruhat descent on the S-idèle quotient.
Deviation: The quotient descent is bundled together with the lift. -/
theorem exists_sLocalTraceLift_bruhatQuotientTest
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c) :
    ∃ (f : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ),
      (∀ g : Iₛ, Φ.val (QuotientGroup.mk g) =
        φ.val (QuotientGroup.mk (sIdeleInsertion F S g))) ∧
      ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (Φ.val (QuotientGroup.mk g)) := by
  obtain ⟨Φ, hΦ⟩ := exists_sLocalTraceBruhatQuotientTest hPic φ hOutside
  obtain ⟨f, hf⟩ := exists_sLocalTraceLift hPic φ hOutside
  exact ⟨f, Φ, hΦ, fun g ↦ (hΦ g).symm ▸ hf g⟩

/-- Auxiliary result for Theorem 12.4.1.1, p. 514 n. 2. The actual compact
global trace test has an idelic lift and a quotient descent whose norm-one
character coefficient is a compactly supported Schwartz function on the log
line. The coefficient uses the full norm-one Tamagawa measure. -/
theorem exists_sLocalTraceLift_radialTestProfile
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) :
    ∃ (f : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ) (k : 𝓢(ℝ, ℂ)),
      (∀ g : Iₛ, Φ.val (QuotientGroup.mk g) =
        φ.val (QuotientGroup.mk (sIdeleInsertion F S g))) ∧
      (∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (Φ.val (QuotientGroup.mk g))) ∧
      HasCompactSupport (k : ℝ → ℂ) ∧ ∀ x : ℝ,
        k x = ∫ h : J₁,
          Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) * (ω h : ℂ) ∂η := by
  let π : Iₛ →ₜ* Jₛ := ⟨QuotientGroup.mk' Hₛ, continuous_quotient_mk'⟩
  have hσ : RightInverse (π.comp τ) (sIdeleQuotientNorm F S) := fun x ↦ hτ x
  obtain ⟨f, Φ, hΦ, hf⟩ := exists_sLocalTraceLift_bruhatQuotientTest hPic φ hOutside
  obtain ⟨k, hc, hk⟩ := SLocalRadialAction.exists_normOneCharacterLogTest F S
    (π.comp τ) hσ Φ ω
  exact ⟨f, Φ, k, hΦ, hf, hc, hk⟩

/-- In the real logarithmic coordinate the radial measure in the norm product
is Lebesgue measure. -/
private theorem sLocalTrace_logNormProduct_measurePreserving
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
    MeasurePreserving
      (fun p : J₁ × ℝ ↦ p.1.val * (QuotientGroup.mk (τ (expLog p.2)) : Jₛ))
      ((η).prod volume) μJ := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let j (p : J₁ × ℝ≥0ˣ) : Jₛ := p.1.val * QuotientGroup.mk (τ p.2)
  have hτc : Continuous (fun t : ℝ≥0ˣ ↦ (QuotientGroup.mk (τ t) : Jₛ)) :=
    QuotientGroup.continuous_mk.comp τ.continuous
  have hj : Measurable j :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul
      (hτc.measurable.comp measurable_snd)
  have he : Measurable expLog :=
    (positiveRealLogEquiv.symm.continuous.comp continuous_ofAdd).measurable
  have hexp (r : ℝ) : expLog r = Units.mk0 (Real.exp r).toNNReal (by positivity) := by
    apply positiveRealLogEquiv.injective
    apply Multiplicative.toAdd.injective
    rw [show positiveRealLogEquiv (expLog r) = Multiplicative.ofAdd r from
      positiveRealLogEquiv.apply_symm_apply _, positiveRealLogEquiv_apply]
    change r = Real.log ((Real.exp r).toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (Real.exp_pos r).le, Real.log_exp]
  have hExpMap : Measure.map expLog volume = positiveRealHaar := by
    unfold positiveRealHaar
    rw [funext hexp]
  have hprod :
      Measure.map (Prod.map (id : J₁ → J₁) expLog) ((η).prod volume) =
        (η).prod positiveRealHaar := by
    rw [← Measure.map_prod_map η volume measurable_id he, Measure.map_id, hExpMap]
  have hprodτ : ((η).prod positiveRealHaar).map j = μJ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  have heprod : Measurable (Prod.map (id : J₁ → J₁) expLog) :=
    measurable_id.prodMap he
  change MeasurePreserving (j ∘ Prod.map id expLog) ((η).prod volume) μJ
  exact ⟨hj.comp heprod, (Measure.map_map hj heprod).symm.trans
    ((congrArg (Measure.map j) hprod).trans hprodτ)⟩

private theorem lcaConvolution_sLocal_log_eq_of_homogeneous
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (Φ : BruhatCompactSupport Jₛ) (ω : PontryaginDual J₁)
    (u : Jₛ → ℂ) (hu : Continuous u)
    (hω : ∀ (h : J₁) (q : Jₛ), u (h.val⁻¹ * q) = (ω h : ℂ) * u q)
    (k : ℝ → ℂ) :
    let j (r : ℝ) : Jₛ := QuotientGroup.mk (τ (expLog r))
    (∀ r, k r = ∫ h : J₁, Φ.val (h.val * j r) * (ω h : ℂ) ∂η) →
    ∀ x, lcaConvolution μJ Φ.val u (j x) = ∫ r : ℝ, k r * u (j (x - r)) := by
  intro j hk x
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  let P (p : J₁ × ℝ) : Jₛ := p.1.val * j p.2
  have hP : MeasurePreserving P ((η).prod volume) μJ :=
    sLocalTrace_logNormProduct_measurePreserving τ hτ
  let G (y : Jₛ) := Φ.val y * u (y⁻¹ * j x)
  have hΦ : Continuous Φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp Φ.property.1)
  have hG : Integrable G μJ := (hΦ.mul
    (hu.comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      Φ.property.2.mul_right
  have hGmap : Integrable G (((η).prod volume).map P) := by
    rw [hP.map_eq]
    exact hG
  have hGP : Integrable (G ∘ P) ((η).prod volume) := hGmap.comp_measurable hP.measurable
  have hsub (r t : ℝ) : (j r)⁻¹ * j t = j (t - r) := by
    have hexp : expLog (t - r) = expLog t / expLog r := by
      change positiveRealLogEquiv.symm (Multiplicative.ofAdd t / Multiplicative.ofAdd r) =
        positiveRealLogEquiv.symm (Multiplicative.ofAdd t) /
          positiveRealLogEquiv.symm (Multiplicative.ofAdd r)
      exact map_div positiveRealLogEquiv.symm _ _
    let σ : ℝ≥0ˣ →* Jₛ := (QuotientGroup.mk' (sProjectedDiagonal F S)).comp τ.toMonoidHom
    change (σ (expLog r))⁻¹ * σ (expLog t) = σ (expLog (t - r))
    rw [hexp, map_div, div_eq_mul_inv, mul_comm]
  change (∫ y, G y ∂μJ) = _
  calc
    _ = ∫ y, G y ∂Measure.map P ((η).prod volume) :=
      congrArg (fun μ : Measure Jₛ ↦ ∫ y, G y ∂μ) hP.map_eq.symm
    _ = ∫ p, G (P p) ∂((η).prod volume) :=
      integral_map hP.aemeasurable hGmap.aestronglyMeasurable
    _ = ∫ r : ℝ, ∫ h : J₁, G (h.val * j r) ∂η :=
      integral_prod_symm (G ∘ P) hGP
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
      change (∫ h : J₁, G (h.val * j r) ∂η) = k r * u (j (x - r))
      rw [hk r, ← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun h ↦ ?_)
      have harg : (h.val * j r)⁻¹ * j x = h.val⁻¹ * j (x - r) := by
        calc
          _ = h.val⁻¹ * ((j r)⁻¹ * j x) := by
            rw [mul_inv_rev]
            ac_rfl
          _ = _ := by rw [hsub r x]
      change Φ.val (h.val * j r) * u ((h.val * j r)⁻¹ * j x) =
        (Φ.val (h.val * j r) * (ω h : ℂ)) * u (j (x - r))
      rw [harg, hω, mul_assoc]

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517. On a half-density homogeneous
theta representative the quotient convolution restricts on the norm section
to ordinary real convolution by the corresponding character profile. -/
theorem sLocalTrace_homogeneousThetaHalfDensity_logConvolution
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (Φ : BruhatCompactSupport Jₛ) (ω : PontryaginDual J₁) (v : Bₛ) (k : ℝ → ℂ) :
    let j (r : ℝ) : Jₛ := QuotientGroup.mk (τ (expLog r))
    let u (q : Jₛ) := (Real.sqrt ((sIdeleQuotientNorm F S q).val : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap F S ω v q
    (∀ r, k r = ∫ h : J₁, Φ.val (h.val * j r) * (ω h : ℂ) ∂η) →
    ∀ x, lcaConvolution μJ Φ.val u (j x) = ∫ r : ℝ, k r * u (j (x - r)) := by
  intro j u hk
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hN : Continuous (fun q : Jₛ ↦ ((sIdeleQuotientNorm F S q).val : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp
      (continuousSIdeleQuotientNorm F S).continuous)
  have hu : Continuous u := (Complex.continuous_ofReal.comp hN.sqrt).mul
    (sLocalHomogeneousAdelicThetaLinearMap F S ω v).continuous
  have hω (h : J₁) (q : Jₛ) : u (h.val⁻¹ * q) = (ω h : ℂ) * u q := by
    have hn : sIdeleQuotientNorm F S (h.val⁻¹ * q) = sIdeleQuotientNorm F S q := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp h.property, inv_one, one_mul]
    have hθ := sLocalHomogeneousAdelicTheta_homogeneous F S η ω v h q
    dsimp only [u]
    rw [hn]
    change (Real.sqrt ((sIdeleQuotientNorm F S q).val : ℝ) : ℂ) *
      sLocalHomogeneousAdelicTheta F S η ω v (h.val⁻¹ * q) =
      (ω h : ℂ) * ((Real.sqrt ((sIdeleQuotientNorm F S q).val : ℝ) : ℂ) *
        sLocalHomogeneousAdelicTheta F S η ω v q)
    rw [hθ, mul_left_comm]
  exact lcaConvolution_sLocal_log_eq_of_homogeneous τ hτ Φ ω u hu hω k hk

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517. The compact lift and
quotient descent of the global test give a single compact Schwartz kernel
for real logarithmic convolution on every concrete homogeneous theta input.
The character coefficient uses the full norm-one Tamagawa measure. -/
theorem exists_sLocalTraceLift_homogeneousThetaLogConvolution
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) :
    let j (r : ℝ) : Jₛ := QuotientGroup.mk (τ (expLog r))
    ∃ (f : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ) (k : 𝓢(ℝ, ℂ)),
      (∀ g : Iₛ, Φ.val (QuotientGroup.mk g) =
        φ.val (QuotientGroup.mk (sIdeleInsertion F S g))) ∧
      (∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (Φ.val (QuotientGroup.mk g))) ∧
      HasCompactSupport (k : ℝ → ℂ) ∧
      (∀ r, k r = ∫ h : J₁, Φ.val (h.val * j r) * (ω h : ℂ) ∂η) ∧
      ∀ v : Bₛ,
        let u (q : Jₛ) := (Real.sqrt ((sIdeleQuotientNorm F S q).val : ℝ) : ℂ) *
          sLocalHomogeneousAdelicThetaLinearMap F S ω v q
        ∀ x, lcaConvolution μJ Φ.val u (j x) = ∫ r : ℝ, k r * u (j (x - r)) := by
  intro j
  obtain ⟨f, Φ, k, hΦ, hLift, hkc, hk⟩ :=
    exists_sLocalTraceLift_radialTestProfile hPic φ hOutside τ hτ ω
  exact ⟨f, Φ, k, hΦ, hLift, hkc, hk, fun v ↦
    sLocalTrace_homogeneousThetaHalfDensity_logConvolution τ hτ Φ ω v (k : ℝ → ℂ) hk⟩

end RiemannMasullo
