module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ConcreteCofinalAnnularFamily
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualAmbientAnnulusTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothPolarTraceLimit
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReciprocalAnnulusCenteredPlateau
import RiemannMasullo.Ch12_TraceGeometric.Sec4_InverseRadiusLaw
import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusTracePrerequisites

/-! # Sharp comparison for an order-zero cofinal family of compressed traces -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

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
local notation "expLog" => fun x : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd x)
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
is an explicit hypothesis. The limit retains the smooth frequency multiplier. In the trivial character
the same operators have the order-zero polar trace correction. -/
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
          L⁻¹ + ε (path L) < L - ε (path L) ∧
          sLocalReflectedPolarLineData (F := F) (S := S) angular (Real.sqrt L) T ∧
          let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ (ρ (path L)) hρ.measurable hρ.abs_le_one
          let CΦ : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ Q 0 0 0 le_rfl le_rfl Φ
          Cn.val = (R.comp CΦ).comp (T.adjoint.comp (M.comp T))
      (∀ p (x y : I), κ p (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun z ↦ (ρ p (QuotientGroup.mk z) : ℂ))
          (fun z ↦ b p (modS(z))) x (ξ.val * y).val) ∧
      (∀ᶠ L : ℝ in atTop, Actual L (C L) ∧ compressedTrace L (C L) =
        ∫ q, diag (path L) q ∂ν₀) ∧
      (Tendsto (fun L : ℝ ↦ compressedTrace L (C L) -
        ∑' ξ : H, sLocalTraceSharpMass f ξ (L * Real.sqrt L)) atTop (𝓝 0)) ∧
      (angular = 1 → ∃ k : 𝓢(ℝ, ℂ),
        (∀ x : ℝ, k x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x)))
          ∂(sLocalNormOneQuotientMeasure F S)) ∧
        Tendsto (fun L : ℝ ↦ sLocalOrderZeroPolarTraceDifference (F := F) (S := S)
          (Real.sqrt L) (C L)) atTop (𝓝 (∫ t, k t * (Real.exp (-|t| / 2) : ℂ)))) := by
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
      L⁻¹ + ε (path L) < L - ε (path L) ∧
      sLocalReflectedPolarLineData (F := F) (S := S) angular (Real.sqrt L) T ∧
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
    obtain ⟨hχ, hsec, hGen, hM, hLine, hRep', hCertificate⟩ := hData
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
    exact ⟨Cn, ⟨hρ, χ, T, M, hχ, hsec, hGen, hM, hInner, hLine, rfl⟩, hCompressed hCap⟩
  let C (L : ℝ) : nuclearEndomorphisms W₀ :=
    if h : ∃ Cn, Good L Cn then Classical.choose h else 0
  have hC : ∀ᶠ L : ℝ in atTop, Good L (C L) := hGood.mono fun L h ↦ by
    rw [show C L = Classical.choose h by simp only [C, dite_eq_left h]]
    exact Classical.choose_spec h
  refine ⟨σ, γ, κ, C, hLaw, hRep, hC, hLimit.congr' ?_, ?_⟩
  · filter_upwards [hC] with L hL
    have hTrace : compressedTrace L (C L) = ∫ q, diag (path L) q ∂ν₀ := hL.2
    rw [hTrace]
  · intro hAngular
    subst angular
    let B (L : ℝ) := Real.sqrt (max 1 L)
    let δ (L : ℝ) := ε (path L)
    let radiusProfile (L t : ℝ) :=
      Isolated.avgCutoff (σ (path L)) t -
        Isolated.avgCutoff ((σ (path L)).map (Inv.inv : ℝ → ℝ)) t
    let logMask (L : ℝ) : ℝ → ℝ :=
      (Iic (Real.log L)).indicator (fun x ↦ radiusProfile L (Real.exp x))
    have hB (L : ℝ) : 0 < B L :=
      Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
    have hBeq : ∀ᶠ L : ℝ in atTop, B L = Real.sqrt L := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      simp only [B, max_eq_right hL]
    have hWidth : Tendsto (fun L : ℝ ↦ Real.sqrt (δ L / B L)) atTop (𝓝 0) :=
      tendsto_sqrt_reciprocalAnnulus_width_div_sqrt.congr'
        (hBeq.mono fun L hL ↦ congrArg (fun d : ℝ ↦ Real.sqrt (δ L / d)) hL.symm)
    have hLogMeas (L : ℝ) : Measurable (logMask L) := by
      let : IsProbabilityMeasure (σ (path L)) := (hLaw (path L)).1
      let : IsProbabilityMeasure ((σ (path L)).map (Inv.inv : ℝ → ℝ)) :=
        inverseRadiusLaw_isProbabilityMeasure (σ (path L))
      refine (Measurable.sub ?_ ?_).indicator measurableSet_Iic
      · exact (Isolated.measurable_avgCutoff (σ (path L))).comp Real.continuous_exp.measurable
      · exact (Isolated.measurable_avgCutoff ((σ (path L)).map (Inv.inv : ℝ → ℝ))).comp
          Real.continuous_exp.measurable
    have hLogBound (L x : ℝ) : |logMask L x| ≤ 1 := by
      change |(Iic (Real.log L)).indicator (fun y ↦ radiusProfile L (Real.exp y)) x| ≤ 1
      by_cases hx : x ∈ Iic (Real.log L)
      · rw [indicator_of_mem hx]
        let : IsProbabilityMeasure (σ (path L)) := (hLaw (path L)).1
        let : IsProbabilityMeasure ((σ (path L)).map (Inv.inv : ℝ → ℝ)) :=
          inverseRadiusLaw_isProbabilityMeasure (σ (path L))
        apply abs_le.mpr
        dsimp only [radiusProfile]
        constructor
        · linarith [Isolated.avgCutoff_nonneg (σ (path L)) (Real.exp x),
            Isolated.avgCutoff_le_one ((σ (path L)).map (Inv.inv : ℝ → ℝ)) (Real.exp x)]
        · linarith [Isolated.avgCutoff_le_one (σ (path L)) (Real.exp x),
            Isolated.avgCutoff_nonneg ((σ (path L)).map (Inv.inv : ℝ → ℝ)) (Real.exp x)]
      · rw [indicator_of_notMem hx, abs_zero]
        exact zero_le_one
    have hLogUpper (L x : ℝ) (hx : Real.log L < x) : logMask L x = 0 :=
      indicator_of_notMem (not_le.mpr hx) _
    have hExpLog (q : J) : Real.exp (ℓ q) = N q :=
      Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt (Q q)))
    have hLogEq (L : ℝ) (hMod : IsModulatedCutoff Q L (δ L) (ρ (path L))) :
        logMask L ∘ ℓ = ρ (path L) := by
      funext q
      change (Iic (Real.log L)).indicator (fun x ↦ radiusProfile L (Real.exp x)) (ℓ q) =
        ρ (path L) q
      by_cases hq : ℓ q ∈ Iic (Real.log L)
      · rw [indicator_of_mem hq, hExpLog]
      · rw [indicator_of_notMem hq]
        by_contra hne
        have hMem : q ∈ tsupport (ρ (path L)) := subset_closure (mem_support.mpr (Ne.symm hne))
        have hUpper : N q ≤ L := (hMod.support_subset hMem).2
        exact hq (Real.log_le_log (NNReal.coe_pos.mpr (Units.zero_lt (Q q))) hUpper)
    have hLogOne (z : ℝ) : ∀ᶠ L : ℝ in atTop, logMask L (z + -Real.log (B L)) = 1 := by
      filter_upwards [hC, hBeq, eventually_mem_reciprocalAnnulus_centered_sqrt z] with L hGood hEq hz
      obtain ⟨hMod, _, _, _, _⟩ := hGood.1
      let x := z + -Real.log (B L)
      let q : J := QuotientGroup.mk (τ (expLog x))
      have hLog : ℓ q = x := by
        have hn := (sIdeleQuotientNorm_mk F S (τ (expLog x))).trans (hτ (expLog x))
        change Real.log ((sIdeleQuotientNorm F S q).val : ℝ) = x
        rw [hn]
        have h := congrArg Multiplicative.toAdd
          (positiveRealLogEquiv.apply_symm_apply (Multiplicative.ofAdd x))
        exact (positiveRealLogEquiv_apply _).symm.trans h
      have hNorm : N q = Real.exp x := hLog ▸ (hExpLog q).symm
      have hRad : Real.exp x = Real.exp z / Real.sqrt L := by
        dsimp only [x]
        rw [Real.exp_add, Real.exp_neg, Real.exp_log (hB L), hEq, div_eq_mul_inv]
      change logMask L x = 1
      rw [← hLog]
      have he : logMask L (ℓ q) = ρ (path L) q := congrFun (hLogEq L hMod) q
      rw [he]
      apply hMod.eq_one
      change N q ∈ Icc (L⁻¹ + δ L) (L - δ L)
      rw [hNorm, hRad]
      exact hz
    have hPolar := @exists_sLocalSmoothPolarTraceDifference_tendsto_orderZero F _ _ S ℝ
      atTop _ τ hτ Φ B (fun L ↦ Real.log L) δ hB logMask hLogMeas hLogBound hLogUpper
      hLogOne hWidth C
    have hActual : ∀ᶠ L : ℝ in atTop, Actual L (C L) := hC.mono fun _ h ↦ h.1
    have hPlateauPos : ∀ᶠ L : ℝ in atTop, 0 < Real.sqrt L - δ L :=
      hCut.mono fun _ h ↦ h.2.2.2.1
    have hLimitPolar := hPolar (by
      filter_upwards [hActual, hBeq, hPlateauPos] with L hAct hEq hδPos
      obtain ⟨hMod, χ, T, M, hData⟩ := hAct
      obtain ⟨_, _, _, hM, hInner, hLine, hOp⟩ := hData
      let : IsProbabilityMeasure (γ (path L)) := (hLaw (path L)).2.1
      have hδ : 0 ≤ δ L := by change 0 ≤ (1 + |L|)⁻¹; positivity
      have hδB : δ L < B L := by
        rw [hEq]
        exact sub_pos.mp hδPos
      have hNuc := isNuclearOperator_sLocalTrace_fixedAnnulus_testAction_comp
        (F := F) (S := S) (s := 0) le_rfl Φ hMod
        ⟨add_pos (inv_pos.mpr hMod.radius_pos) hMod.width_pos, hInner⟩
        (ContinuousLinearMap.id ℂ W₀)
      rw [ContinuousLinearMap.comp_id] at hNuc
      have hR : logMask L ∘ ℓ = ρ (path L) := hLogEq L hMod
      simp only [hR]
      refine ⟨hNuc, hδ, hδB, T, M, Isolated.avgCutoff (γ (path L)), hM, ?_, ?_, ?_, hOp⟩
      · intro r _
        exact ⟨Isolated.avgCutoff_nonneg _ _, Isolated.avgCutoff_le_one _ _⟩
      · intro r _ hr
        rw [hEq] at hr
        exact Isolated.avgCutoff_eq_one _ (hLaw (path L)).2.2.2 hr
      · rw [hEq]
        exact hLine)
    obtain ⟨k, hk, hlim⟩ := hLimitPolar
    exact ⟨k, hk, hlim.congr' (hBeq.mono fun L hL ↦ by rw [hL])⟩

end RiemannMasullo
