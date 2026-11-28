module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualReflectedPolarComplement
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualPolarCutoffCoefficient
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualFixedBandTraceClass

/-! # The polar correction to the actual fixed-cutoff trace -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal FourierTransform InnerProductSpace NNReal NumberField.AdeleRing SchwartzMap

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)

local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "circleCoe" =>
  (ContinuousMonoidHom.mk Circle.coeHom continuous_subtype_val : Circle →ₜ* ℂ)
local notation "phase(" χ "," ξ ")" => sLocalRhoFactor
  (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
    (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
    (ContinuousMonoidHom.comp circleCoe χ) (sLocalRadialThetaCriticalParameter ξ))
local notation "expLog" => fun x : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd x)

local instance : MeasurableSpace J₁ := borel _

private theorem exists_nuclearCompressions_trace_sub_of_line
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Vfull Vpolar : Submodule ℂ H) [CompleteSpace Vfull] [CompleteSpace Vpolar]
    (hLe : Vpolar ≤ Vfull) (A : H →L[ℂ] H) (C : Vfull →L[ℂ] H)
    (hC : C ∈ traceClassOperators Vfull H) (hCA : C = A.comp Vfull.subtypeL)
    (u : Vfull) (huNorm : ‖u.val‖ = 1) (huSpan : Vfull ⊓ Vpolarᗮ = ℂ ∙ u.val) :
    ∃ Full Polar : nuclearEndomorphisms H,
      Full.val = Vfull.starProjection * A * Vfull.starProjection ∧
      Polar.val = Vpolar.starProjection * A * Vpolar.starProjection ∧
      hilbertTrace Full - hilbertTrace Polar = ⟪u.val, C u⟫_ℂ := by
  let G : nuclearEndomorphisms H := ⟨C.comp Vfull.orthogonalProjectionOnto,
    (mem_traceClassOperators_iff_isNuclearOperator _).mp
      (comp_right_mem_traceClass C hC Vfull.orthogonalProjectionOnto)⟩
  have hG (v : Vfull) : G.val v.val = C v := by
    change C (Vfull.orthogonalProjectionOnto v.val) = C v
    rw [Vfull.orthogonalProjectionOnto_mem_subspace_eq_self v]
  have hCompress (P : Submodule ℂ H) [P.HasOrthogonalProjection] (hP : P ≤ Vfull) :
      (Isolated.nuclearCompress P.starProjection G).val =
        P.starProjection * A * P.starProjection := by
    ext v
    let w : Vfull := ⟨P.starProjection v, hP (P.starProjection_apply_mem v)⟩
    change P.starProjection (G.val w.val) = P.starProjection (A w.val)
    rw [hG w, hCA]
    rfl
  have hTrace := Isolated.hilbertTrace_nuclearCompress_sub_eq_inner_of_complement_line
    G Vpolar Vfull hLe u.val huNorm huSpan
  rw [hG u] at hTrace
  exact ⟨_, _, hCompress Vfull le_rfl, hCompress Vpolar hLe, hTrace⟩

/-- Paper: Theorem 12.4.1.1, pp. 515–518. At a fixed positive band and Sobolev
order zero, the trivial-character polar correction to the actual upper-cutoff
trace is the pairing of the physical inverse-phase profile with the masked
convolution of the normalized half-line exponential. -/
theorem exists_sLocalFullPW_upperCutoff_trace_sub_polar_eq_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) {B : ℝ} (hB : 0 < B)
    (Φ : BruhatCompactSupport Jₛ) (Tmax : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ x, |ρ x| ≤ 1) (hρT : ∀ x, Tmax < x → ρ x = 0) :
    let Vfull : Submodule ℂ W₀ := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
      le_rfl halfPos (1 : PontryaginDual J₁) B
    let Vpolar : Submodule ℂ W₀ := sLocalInvariantPWSobolev (F := F) (S := S) (s := 0)
      le_rfl halfPos (1 : PontryaginDual J₁) B
    letI : CompleteSpace Vfull :=
      (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    letI : CompleteSpace Vpolar :=
      (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let hρLog : Measurable (ρ ∘ ℓ) := hρm.comp (Real.measurable_log.comp
      (NNReal.continuous_coe.comp
        (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable)
    let A : W₀ →L[ℂ] W₀ :=
      hardySobolevTestAction μJ (continuousSIdeleQuotientNorm F S) 0 0 0 le_rfl le_rfl Φ
    let M : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ (ρ ∘ ℓ) hρLog (fun g ↦ hρ (ℓ g))
    let a := -Real.log B
    ∃ (χ : PontryaginDual Jₛ) (k q : 𝓢(ℝ, ℂ)) (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
      (Full Polar : nuclearEndomorphisms W₀),
      χ.comp include₁ = 1 ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      (∀ x : ℝ, k x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) ∂η) ∧
      (∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
        star (phase(χ,ξ)) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ) ∧
      (∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ = phase(χ,ξ) * 𝓕 (k : ℝ → ℂ) ξ) ∧
      Full.val = Vfull.starProjection * (M.comp A) * Vfull.starProjection ∧
      Polar.val = Vpolar.starProjection * (M.comp A) * Vpolar.starProjection ∧
      let integrand (x : ℝ) := (starRingEnd ℂ) (U.symm (normalizedHalflineExponentialL2 a) x) *
        ((ρ x : ℂ) * ∫ y in Ici a, q (x - y) * (Real.exp ((a - y) / 2) : ℂ))
      hilbertTrace Full - hilbertTrace Polar = (∫ x, integrand x) ∧ Integrable integrand := by
  intro Vfull Vpolar hρLog A M a
  let : CompleteSpace Vfull :=
    (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let : CompleteSpace Vpolar :=
    (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let ω : PontryaginDual J₁ := 1
  obtain ⟨χ, Q, L, U, hχ, hsec, _, _, hL, hRecover, hPhase, hGen, hSupport, hFull, hPolar⟩ :=
    exists_sLocalFullReflectedCoordinates_orderZero (F := F) (S := S) τ hτ ω hB
  let T : W₀ →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp Q
  have hLe : Vpolar ≤ Vfull :=
    (Isolated.sLocalPWSobolev_polarComplement (F := F) (S := S) (s := 0)
      le_rfl halfPos ω B).1
  have hIso (v : W₀) (hv : v ∈ Vfull) : ‖T v‖ = ‖v‖ := by
    change ‖U (Q v)‖ = ‖v‖
    rw [U.norm_map, ← L.norm_map (Q v), hRecover v hv]
  have hPolarRange : Set.range (fun u : Vpolar ↦ T u.val) =
      {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < a → r y = 0) ∧
        (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0} := by
    have hRange : Set.range (fun u : Vpolar ↦ T u.val) =
        {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < a → r y = 0) ∧
          ((1 : PontryaginDual J₁) = 1 → (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0)} :=
      hPolar
    simpa only [true_implies] using hRange
  obtain ⟨u, ⟨huT, huNorm, huSpan⟩, _⟩ :=
    existsUnique_normalizedPolarDirection_of_reflectedRanges Vfull Vpolar hLe T hIso
      a hFull hPolarRange
  let C : Vfull →L[ℂ] W₀ := M.comp (A.comp Vfull.subtypeL)
  have hFactorData :=
    @exists_sLocalFullPW_upperCutoff_factor_orderZero F _ _ S τ hτ ω χ hχ hsec B T L
      hGen hSupport hL Φ Tmax ρ hρm hρ hρT
  rcases hFactorData with ⟨k, q, K, hk, hq, hK, hFactor, hRow⟩
  have hC : C ∈ traceClassOperators Vfull W₀ := by
    change M.comp (A.comp Vfull.subtypeL) ∈ traceClassOperators Vfull W₀
    rw [hFactor]
    exact comp_left_mem_traceClass K hK L.toContinuousLinearMap
  have hCA : C = (M.comp A).comp Vfull.subtypeL := rfl
  have hTraceData :=
    @exists_nuclearCompressions_trace_sub_of_line W₀ _ _ _ Vfull Vpolar _ _
      hLe (M.comp A) C hC hCA u huNorm huSpan
  rcases hTraceData with ⟨Full, Polar, hFullComp, hPolarComp, hTrace⟩
  have hScalarData :=
    @inner_cutoffFactor_eq_integral_of_exponential_preimage W₀ _ _
      Vfull Q T U L K C hFactor u a (hRecover u.val u.property) rfl huT ρ q (hRow u)
  rcases hScalarData with ⟨hScalar, hIntegrable⟩
  have hkTrivial (x : ℝ) :
      k x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) ∂η := by
    simpa only [ω, PontryaginDual.one_apply, Circle.coe_one, mul_one] using hk x
  exact ⟨χ, k, q, U, Full, Polar, hχ, hsec, hkTrivial, hPhase, hq, hFullComp, hPolarComp,
    hTrace.trans hScalar, hIntegrable⟩

end RiemannMasullo
