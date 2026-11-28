module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualAmbientAnnulusComparison
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedFrequencyCap
import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusOrbit
import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusTracePrerequisites
import RiemannMasullo.AppC_LCTVS.Sec3b
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The trace of the actual order-zero annular orbit operator -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8
set_option quotPrecheck false

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1
  instSIdeleLocallyCompactSec1 instSAdeleMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "include₁" => (ContinuousMonoidHom.mk
  (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
  continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "modS(" u ")" =>
  (∏ w : InfinitePlace F, ‖(u : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
    ∏ v : S, ‖(u : Aₛ).2 v‖
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "orbitOrder" =>
  (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ)

local instance instSIdeleT2AmbientAnnulusTrace : T2Space Iₛ := (sIdeleGroup_description F S).2.1

private theorem annulusTrace_orderZeroMeasure_eq : (ν₀ : Measure Jₛ) = μJ := by
  have hzero (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
  change (μJ).withDensity (fun q ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (ℓ q))) = μJ
  simp only [hzero, ENNReal.ofReal_one]
  exact withDensity_one

local instance instOrderZeroFiniteOnCompactsAmbientAnnulusTrace :
    IsFiniteMeasureOnCompacts (ν₀ : Measure Jₛ) := by
  rw [annulusTrace_orderZeroMeasure_eq]
  infer_instance

local instance instOrderZeroInnerRegularAmbientAnnulusTrace :
    Measure.InnerRegular (ν₀ : Measure Jₛ) := by
  rw [annulusTrace_orderZeroMeasure_eq]
  infer_instance

private theorem ambientAnnulus_trace_eq_of_kernel_representation
    (K : Jₛ × Jₛ → ℂ) (hK : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀))
    (C : W₀ →L[ℂ] W₀) (hC : IsNuclearOperator C)
    (hOp : (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val = C)
    (hCont : ∀ᵐ q ∂ν₀, ContinuousAt K (q, q)) :
    Integrable (fun q ↦ K (q, q)) ν₀ ∧
      hilbertTrace (⟨C, hC⟩ : nuclearEndomorphisms W₀) = ∫ q, K (q, q) ∂ν₀ := by
  let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val
  have hKop : IsNuclearOperator Kop := by
    change IsNuclearOperator (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val
    rw [hOp]
    exact hC
  have hIntegral := hilbertTrace_integralKernelOperator_of_ae_continuous (X := Jₛ) ν₀ hK hKop hCont
  obtain ⟨hInt, hTrace⟩ := hIntegral
  have hBundle : (⟨Kop, hKop⟩ : nuclearEndomorphisms W₀) = ⟨C, hC⟩ := Subtype.ext hOp
  change hilbertTrace (⟨Kop, hKop⟩ : nuclearEndomorphisms W₀) =
    (∫ q, K (q, q) ∂ν₀) at hTrace
  rw [hBundle] at hTrace
  exact ⟨hInt, hTrace⟩

/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 515–518.
At order zero, a frequency profile supported below the band radius gives
the weighted orbital diagonal formula for the trace compressed to the
full invariant band.
Deviation: This uses a fixed strict spatial annulus and retains the smooth
frequency multiplier inside the band compression. -/
theorem exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_trace_atBand_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ) (hInner : Λ⁻¹ + ερ < Λ - ερ)
    (hρcont : ∀ᵐ x ∂μJ, ContinuousAt ρ x)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb)
    (B : ℝ) (hB : 0 < B) :
    let N (q : Jₛ) : ℝ := (m q).val
    ∃ (χ : PontryaginDual Jₛ) (T : W₀ →L[ℂ] FlatL2)
      (M : FlatL2 →L[ℂ] FlatL2) (κ : Jₛ → Jₛ → ℂ),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      sLocalFullReflectedGenAE τ angular χ T ∧
      (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x) ∧
      sLocalReflectedPolarLineData (F := F) (S := S) angular B T ∧
      (∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, sLocalTraceCutoffKernel (F := F) (S := S) fLift
          (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) (fun w ↦ b (modS(w))) x (ξ.val * y).val) ∧
      let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
      let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
      let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
      let C := (R.comp A).comp (T.adjoint.comp (M.comp T))
      ∃ hC : IsNuclearOperator C,
        Integrable (fun q ↦ K (q, q)) ν₀ ∧
        (hilbertTrace ⟨C, hC⟩ = ∫ q, K (q, q) ∂ν₀) ∧
        ((∀ t > B, b t = 0) →
          let V : Submodule ℂ W₀ := fullBand(angular,B)
          letI : CompleteSpace V :=
            (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
          hilbertTrace (Isolated.nuclearCompress V.starProjection ⟨C, hC⟩) =
            ∫ q, K (q, q) ∂ν₀) := by
  intro N
  have hOperatorData :=
    @exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eq_atBand_orderZero F _ _ S
      τ hτ fLift Φ hLift angular hΦ b Λ ερ εb Cb ρ hρ hb hbdd hε hplateau hderiv B hB
  obtain ⟨χ, T, M, κ, hData⟩ := hOperatorData
  obtain ⟨hχ, hsec, hGen, hM, hInter, hPolar, hRep, _, hK, hEq⟩ := hData
  let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
    ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
  let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
  let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
  let D := T.adjoint.comp (M.comp T)
  let C := (R.comp A).comp D
  have hK₂ : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀) := hK
  let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK₂.toLp K)).val
  have hOp : Kop = C := hEq
  have hTwo : (2 : ℕ) ≤ orbitOrder := by omega
  have hFactorData :=
    @exists_sLocalTrace_maskedRadialOrbitSeries_factor F _ _ S fLift b (fun q ↦ (ρ q : ℂ)) κ
      εb Cb ((contDiff_infty.mp hb) 2) hε hplateau
      (fun j hj ↦ hderiv j (hj.trans hTwo)) hRep
  obtain ⟨κ₀, hκ₀, hFactor⟩ := hFactorData
  have hCont : ∀ᵐ q ∂ν₀, ContinuousAt K (q, q) := by
    simpa only [K, hFactor] using
      ae_continuousAt_sLocalTrace_maskedHalfDensity (F := F) (S := S) κ₀ hκ₀ hρcont 0
  have hBand : 0 < Λ⁻¹ + ερ ∧ Λ⁻¹ + ερ < Λ - ερ :=
    ⟨add_pos (inv_pos.mpr hρ.radius_pos) hρ.width_pos, hInner⟩
  have hC : IsNuclearOperator C :=
    isNuclearOperator_sLocalTrace_fixedAnnulus_testAction_comp
      (F := F) (S := S) (s := 0) le_rfl Φ hρ hBand D
  have hTrace := ambientAnnulus_trace_eq_of_kernel_representation (F := F) (S := S)
    K hK₂ C hC hOp hCont
  refine ⟨χ, T, M, κ, hχ, hsec, hGen, hM, hPolar, hRep, hC, hTrace.1, hTrace.2, ?_⟩
  intro hCap V
  let : CompleteSpace V :=
    (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let Cn : nuclearEndomorphisms W₀ := ⟨C, hC⟩
  have hCompressed := @hilbertTrace_nuclearCompress_eq_of_reflectedFrequencyCap W₀ _ _ _
    T M b hM B hB hCap V.starProjection (R.comp A) hInter Cn rfl
  exact hCompressed.trans hTrace.2

/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 515–518.
At a fixed strict annulus the actual order-zero cutoff action for a
homogeneous quotient test is nuclear, and its trace is the integral
of the half-density orbital diagonal.
Deviation: The kernel keeps the smooth cutoffs. The spatial mask's
almost-everywhere continuity is stated explicitly. -/
theorem exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_trace_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ) (hInner : Λ⁻¹ + ερ < Λ - ερ)
    (hρcont : ∀ᵐ x ∂μJ, ContinuousAt ρ x)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : Jₛ) : ℝ := (m q).val
    ∃ (χ : PontryaginDual Jₛ) (T : W₀ →L[ℂ] FlatL2)
      (M : FlatL2 →L[ℂ] FlatL2) (κ : Jₛ → Jₛ → ℂ),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      sLocalFullReflectedGenAE τ angular χ T ∧
      (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x) ∧
      (∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, sLocalTraceCutoffKernel (F := F) (S := S) fLift
          (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) (fun w ↦ b (modS(w))) x (ξ.val * y).val) ∧
      let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
      let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
      let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
      let C := (R.comp A).comp (T.adjoint.comp (M.comp T))
      ∃ hC : IsNuclearOperator C,
        Integrable (fun q ↦ K (q, q)) ν₀ ∧
        hilbertTrace ⟨C, hC⟩ = ∫ q, K (q, q) ∂ν₀ := by
  intro N
  have hAtBand :=
    @exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_trace_atBand_orderZero F _ _ S
      τ hτ fLift Φ hLift angular hΦ b Λ ερ εb Cb ρ hρ hInner hρcont hb hbdd hε hplateau hderiv
      1 one_pos
  obtain ⟨χ, T, M, κ, hData⟩ := hAtBand
  obtain ⟨hχ, hsec, hGen, hM, _, hRep, hCertificate⟩ := hData
  obtain ⟨hC, hInt, hEq, _⟩ := hCertificate
  exact ⟨χ, T, M, κ, hχ, hsec, hGen, hM, hRep, hC, hInt, hEq⟩

end RiemannMasullo
