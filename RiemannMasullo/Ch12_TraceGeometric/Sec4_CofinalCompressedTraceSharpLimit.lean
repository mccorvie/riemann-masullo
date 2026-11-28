module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ConcreteCofinalAnnularFamily
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualAmbientAnnulusTrace

/-! # Sharp comparison for an order-zero cofinal family of compressed traces -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "A" => SAdeleRing F S
local notation "I" => (SAdeleRing F S)ˣ
local notation "H" => sProjectedDiagonal F S
local notation "J" => SIdeleQuotient F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "μI" => sMultiplicativeTamagawaMeasure F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "include₁" => (ContinuousMonoidHom.mk
  (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
  continuous_subtype_val : J₁ →ₜ* J)
local notation "orbitOrder" =>
  (2 * (((∑ w : InfinitePlace F, InfinitePlace.mult w) + Fintype.card S) + 1) : ℕ)
local notation "modS(" z ")" => ((∏ w : InfinitePlace F, ‖(z : A).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(z : A).2 v‖)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instSIdeleLocallyCompactSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

local instance instSIdeleT2CofinalCompressedTrace : T2Space I := (sIdeleGroup_description F S).2.1

/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 515–519. Along the square-root
path, the actual order-zero full-band compressed traces of the smooth
annular family agree asymptotically with the sharp orbital sum.
Deviation: The test is a single angular type and the small-radius sharp bound
is an explicit hypothesis. The limit retains the smooth frequency multiplier. -/
theorem exists_sLocalTrace_sqrtPath_compressedTrace_sub_sharpMass_tendsto_zero_orderZero
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (g : C𝔽),
      φ.val (QuotientGroup.mk a.val * g) = φ.val g)
    (Φ : BruhatCompactSupport J) (f : BruhatCompactSupport I)
    (hLift : ∀ x : I, HasSum (fun ξ : H ↦ f.val (ξ.val * x)) (Φ.val (QuotientGroup.mk x)))
    (hShared : ∀ x : I, Φ.val (QuotientGroup.mk x) =
      φ.val (QuotientGroup.mk (sIdeleInsertion F S x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : J) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (D : Set I) (hD : IsFundamentalDomain H D μI)
    (hSharp : ∃ C ≥ 0, ∀ {R : ℝ}, 0 < R → R ≤ 1 →
      Summable (fun ξ : H ↦ ‖sLocalTraceSharpMass f ξ R‖) ∧
      (∑' ξ : H, ‖sLocalTraceSharpMass f ξ R‖) ≤ C * R ^ (1 / 2 : ℝ)) :
    let ε (p : ℝ × ℝ) := (1 + |p.1|)⁻¹
    let path (L : ℝ) := (L, Real.sqrt L)
    let N (q : J) : ℝ := (Q q).val
    let compressedTrace (L : ℝ) (C : nuclearEndomorphisms W₀) : ℂ :=
      let B : Submodule ℂ W₀ := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl
        (show (0 : ℝ) < 1 / 2 by norm_num) angular (Real.sqrt L)
      letI : CompleteSpace B :=
        (show IsClosed (B : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
      hilbertTrace (Isolated.nuclearCompress B.starProjection C)
    ∃ (σ γ : ℝ × ℝ → Measure ℝ) (κ : ℝ × ℝ → J → J → ℂ)
      (C : ℝ → nuclearEndomorphisms W₀),
      (∀ p, IsProbabilityMeasure (σ p) ∧ IsProbabilityMeasure (γ p) ∧
        σ p (Icc (p.1 - ε p) p.1)ᶜ = 0 ∧ γ p (Icc (p.2 - ε p) p.2)ᶜ = 0) ∧
      let ρ (p : ℝ × ℝ) (q : J) := Isolated.avgCutoff (σ p) (N q) -
        Isolated.avgCutoff ((σ p).map (Inv.inv : ℝ → ℝ)) (N q)
      let b (p : ℝ × ℝ) (r : ℝ) : ℂ := Isolated.avgCutoff (γ p) r
      let diag (p : ℝ × ℝ) (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ p q q /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ q) : ℂ))
      let Actual (L : ℝ) (Cn : nuclearEndomorphisms W₀) : Prop :=
        ∃ (hρ : IsModulatedCutoff Q L (ε (path L)) (ρ (path L)))
          (χ : PontryaginDual J) (T : W₀ →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2),
          χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
          sLocalFullReflectedGenAE τ angular χ T ∧
          (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (path L) (Real.exp (-x)) * r x) ∧
          let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ (ρ (path L)) hρ.measurable hρ.abs_le_one
          let CΦ : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ Q 0 0 0 le_rfl le_rfl Φ
          Cn.val = (R.comp CΦ).comp (T.adjoint.comp (M.comp T))
      (∀ p (x y : I), κ p (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun z ↦ (ρ p (QuotientGroup.mk z) : ℂ))
          (fun z ↦ b p (modS(z))) x (ξ.val * y).val) ∧
      (∀ᶠ L : ℝ in atTop, Actual L (C L) ∧ compressedTrace L (C L) =
        ∫ q, diag (path L) q ∂ν₀) ∧
      Tendsto (fun L : ℝ ↦ compressedTrace L (C L) -
        ∑' ξ : H, sLocalTraceSharpMass f ξ (L * Real.sqrt L)) atTop (𝓝 0) := by
  classical
  intro ε path N compressedTrace
  have hLiftGlobal (x : I) : HasSum (fun ξ : H ↦ f.val (ξ.val * x))
      (φ.val (QuotientGroup.mk (sIdeleInsertion F S x))) := by
    rw [← hShared x]
    exact hLift x
  have hFamily :=
    @exists_sLocalTrace_sqrtPath_annularOrbitKernelFamily F _ _ S φ hPic hRam hOutside f
      hLiftGlobal τ hτ D hD 0 le_rfl hSharp
  obtain ⟨σ, γ, κ, hLaw, hData⟩ := hFamily
  obtain ⟨hSmooth, hRep, hCut, hLimit⟩ := hData
  let ρ (p : ℝ × ℝ) (q : J) := Isolated.avgCutoff (σ p) (N q) -
    Isolated.avgCutoff ((σ p).map (Inv.inv : ℝ → ℝ)) (N q)
  let b (p : ℝ × ℝ) (r : ℝ) : ℂ := Isolated.avgCutoff (γ p) r
  let diag (p : ℝ × ℝ) (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ p q q /
    ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ q) : ℂ))
  let Actual (L : ℝ) (Cn : nuclearEndomorphisms W₀) : Prop :=
    ∃ (hρ : IsModulatedCutoff Q L (ε (path L)) (ρ (path L)))
      (χ : PontryaginDual J) (T : W₀ →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      sLocalFullReflectedGenAE τ angular χ T ∧
      (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (path L) (Real.exp (-x)) * r x) ∧
      let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ (ρ (path L)) hρ.measurable hρ.abs_le_one
      let CΦ : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ Q 0 0 0 le_rfl le_rfl Φ
      Cn.val = (R.comp CΦ).comp (T.adjoint.comp (M.comp T))
  let Good (L : ℝ) (Cn : nuclearEndomorphisms W₀) : Prop :=
    Actual L Cn ∧ compressedTrace L Cn = ∫ q, diag (path L) q ∂ν₀
  have hGood : ∀ᶠ L : ℝ in atTop, ∃ Cn : nuclearEndomorphisms W₀, Good L Cn := by
    filter_upwards [hCut] with L hL
    obtain ⟨hρ, hInner, hρContinuous, hPlateauPos, _⟩ := hL
    let p := path L
    let B := Real.sqrt L
    let εb := B - ε p
    let : IsProbabilityMeasure (γ p) := (hLaw p).2.1
    have hSupp : γ p (Icc εb B)ᶜ = 0 := (hLaw p).2.2.2
    have hε : 0 < εb := hPlateauPos
    have hWidth : 0 ≤ ε p := by
      change 0 ≤ (1 + |p.1|)⁻¹
      positivity
    have hB : 0 < B := hε.trans_le (sub_le_self _ hWidth)
    have hCap (r : ℝ) (hr : B < r) : b p r = 0 := by
      change (Isolated.avgCutoff (γ p) r : ℂ) = 0
      rw [Isolated.avgCutoff_eq_zero _ hSupp hr, Complex.ofReal_zero]
    have hBdd (r : ℝ) (_hr : 0 ≤ r) : ‖b p r‖ ≤ 1 := by
      change ‖(Isolated.avgCutoff (γ p) r : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Isolated.avgCutoff_nonneg _ _)]
      exact Isolated.avgCutoff_le_one _ _
    have hPlateau : EqOn (b p) (fun _ ↦ b p 0) (Icc 0 εb) := by
      intro r hr
      change (Isolated.avgCutoff (γ p) r : ℂ) = (Isolated.avgCutoff (γ p) 0 : ℂ)
      rw [Isolated.avgCutoff_eq_one _ hSupp hr.2, Isolated.avgCutoff_eq_one _ hSupp hε.le]
    have hb : ContDiff ℝ (∞ : ℕ∞ω) (b p) := (hSmooth p).2
    have hFinite : ContDiff ℝ orbitOrder (b p) := (contDiff_infty.mp hb) orbitOrder
    obtain ⟨Cb, hDeriv⟩ := sLocalTrace_upperProfile_derivatives_bounded hFinite hCap
    have hρAE : ∀ᵐ q ∂μJ, ContinuousAt (ρ p) q :=
      ae_of_all _ fun _ ↦ hρContinuous.continuousAt
    have hBandTrace :=
      @exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_trace_atBand_orderZero F _ _ S
        τ hτ f Φ hLift angular hΦ (b p) L (ε p) εb Cb (ρ p)
        hρ hInner hρAE hb hBdd hε hPlateau hDeriv B hB
    obtain ⟨χ, T, M, κ', hData⟩ := hBandTrace
    obtain ⟨hχ, hsec, hGen, hM, hRep', hCertificate⟩ := hData
    obtain ⟨hC, _, _, hCompressed⟩ := hCertificate
    have hκ : κ' = κ p := by
      funext q r
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
      exact (hRep' x y).trans (hRep p x y).symm
    subst κ'
    let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ (ρ p) hρ.measurable hρ.abs_le_one
    let CΦ : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ Q 0 0 0 le_rfl le_rfl Φ
    let Cn : nuclearEndomorphisms W₀ := ⟨(R.comp CΦ).comp (T.adjoint.comp (M.comp T)), hC⟩
    exact ⟨Cn, ⟨hρ, χ, T, M, hχ, hsec, hGen, hM, rfl⟩, hCompressed hCap⟩
  let C (L : ℝ) : nuclearEndomorphisms W₀ :=
    if h : ∃ Cn, Good L Cn then Classical.choose h else 0
  have hC : ∀ᶠ L : ℝ in atTop, Good L (C L) := hGood.mono fun L h ↦ by
    rw [show C L = Classical.choose h by simp only [C, dite_eq_left h]]
    exact Classical.choose_spec h
  refine ⟨σ, γ, κ, C, hLaw, hRep, hC, hLimit.congr' ?_⟩
  filter_upwards [hC] with L hL
  have hTrace : compressedTrace L (C L) = ∫ q, diag (path L) q ∂ν₀ := hL.2
  rw [hTrace]

end RiemannMasullo
