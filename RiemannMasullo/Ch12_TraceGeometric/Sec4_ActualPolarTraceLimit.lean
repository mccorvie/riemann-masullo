module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualPolarTraceCorrection
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedPolarCutoffLimit
import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import Mathlib.Analysis.Fourier.Inversion

/-! # The limit of the polar correction to the actual trace -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal FourierTransform InnerProductSpace NNReal NumberField.AdeleRing SchwartzMap Topology

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

local instance instNormOneMeasurableActualPolarTraceLimit : MeasurableSpace J₁ := borel _

/-- An L² isometry described by a Fourier multiplier is determined by that
multiplier up to almost-everywhere equality. -/
private theorem reflectedFourierPhase_isometry_eq
    {m m' : ℝ → ℂ} (hm : m =ᵐ[volume] m')
    (U U' : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
    (hU : ∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (m ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ)
    (hU' : ∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U' v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (m' ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ) : U = U' := by
  apply LinearIsometryEquiv.ext
  intro v
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply Lp.ext
  filter_upwards [hU v, hU' v, hm] with ξ hξ hξ' hmul
  exact hξ.trans ((congrArg (fun z : ℂ ↦ star z * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ)
    hmul).trans hξ'.symm)

/-- Equality of the ordinary Fourier integrals identifies Schwartz kernels. -/
private theorem reflectedSchwartz_eq_of_fourier_eq {q q' : 𝓢(ℝ, ℂ)}
    (h : ∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ = 𝓕 (q' : ℝ → ℂ) ξ) : q = q' := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective
  apply SchwartzMap.ext
  intro ξ
  change 𝓕 (q : ℝ → ℂ) ξ = 𝓕 (q' : ℝ → ℂ) ξ
  exact h ξ

/-- Trivial norm-one type and trivial section restriction give the trivial
quotient character. -/
private theorem sLocalCutoffNormSectionCharacter_eq_one
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = 1)
    (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1) : χ = 1 := by
  let σ : ℝ≥0ˣ →ₜ* Jₛ :=
    ⟨(QuotientGroup.mk' (sProjectedDiagonal F S)).comp τ.toMonoidHom,
      QuotientGroup.continuous_mk.comp τ.continuous⟩
  have hσ : RightInverse σ (sIdeleQuotientNorm F S) := fun t ↦
    (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  exact (existsUnique_sLocalNormSectionCharacter σ hσ 1).unique
    ⟨hχ, hsec⟩ ⟨rfl, fun _ ↦ rfl⟩

/-- The Fourier coordinates in the trivial-type cutoff calculation depend
only on the norm section and the test. -/
private theorem sLocalTrivialCutoffFourierWitnesses_eq
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (Φ : BruhatCompactSupport Jₛ)
    (χ χ₀ : PontryaginDual Jₛ)
    (hχ : χ.comp include₁ = 1) (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (hχ₀ : χ₀.comp include₁ = 1) (hsec₀ : ∀ t, χ₀ (QuotientGroup.mk (τ t)) = 1)
    (k q k₀ q₀ : 𝓢(ℝ, ℂ)) (U U₀ : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
    (hk : ∀ x : ℝ, k x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) ∂η)
    (hk₀ : ∀ x : ℝ, k₀ x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) ∂η)
    (hU : ∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (phase(χ,ξ)) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ)
    (hU₀ : ∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U₀ v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (phase(χ₀,ξ)) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ)
    (hq : ∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ = phase(χ,ξ) * 𝓕 (k : ℝ → ℂ) ξ)
    (hq₀ : ∀ ξ : ℝ, 𝓕 (q₀ : ℝ → ℂ) ξ = phase(χ₀,ξ) * 𝓕 (k₀ : ℝ → ℂ) ξ) :
    χ = 1 ∧ χ₀ = 1 ∧ k = k₀ ∧ q = q₀ ∧ U = U₀ := by
  have hχOne := sLocalCutoffNormSectionCharacter_eq_one τ hτ χ hχ hsec
  have hχ₀One := sLocalCutoffNormSectionCharacter_eq_one τ hτ χ₀ hχ₀ hsec₀
  have hχEq := hχOne.trans hχ₀One.symm
  have hkEq : k = k₀ := SchwartzMap.ext fun x ↦ (hk x).trans (hk₀ x).symm
  have hqEq : q = q₀ := reflectedSchwartz_eq_of_fourier_eq fun ξ ↦ by
    rw [hq ξ, hq₀ ξ, hχEq, hkEq]
  have hmEq : (fun ξ : ℝ ↦ phase(χ,ξ)) =ᵐ[volume] (fun ξ : ℝ ↦ phase(χ₀,ξ)) :=
    ae_of_all _ fun ξ ↦ congrArg (fun ψ : PontryaginDual Jₛ ↦ phase(ψ,ξ)) hχEq
  exact ⟨hχOne, hχ₀One, hkEq, hqEq, reflectedFourierPhase_isometry_eq hmEq U U₀ hU hU₀⟩

/-- Paper: Theorem 12.4.1.1, pp. 515–518. At Sobolev order zero in the
trivial norm-one character, the actual full and polar cutoff traces
differ in the limit by the exponential autocorrelation of the radial
test kernel.
Deviation: This computes the difference of the two traces at order zero.
The cutoff plateau is measured relative to the reflected band boundary. -/
theorem exists_sLocalFullPW_upperCutoff_trace_sub_polar_tendsto_orderZero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (Φ : BruhatCompactSupport Jₛ) (B Tmax : ι → ℝ) (hB : ∀ i, 0 < B i)
    (ρ : ι → ℝ → ℝ) (hρm : ∀ i, Measurable (ρ i)) (hρ : ∀ i x, |ρ i x| ≤ 1)
    (hρT : ∀ i x, Tmax i < x → ρ i x = 0)
    (hOne : ∀ z, ∀ᶠ i in l, ρ i (z + -Real.log (B i)) = 1) :
    ∃ k : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, k x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) ∂η) ∧
      ∃ Full Polar : ι → nuclearEndomorphisms W₀,
        (∀ i,
          let Vfull : Submodule ℂ W₀ := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
            le_rfl halfPos (1 : PontryaginDual J₁) (B i)
          let Vpolar : Submodule ℂ W₀ := sLocalInvariantPWSobolev (F := F) (S := S) (s := 0)
            le_rfl halfPos (1 : PontryaginDual J₁) (B i)
          letI : CompleteSpace Vfull :=
            (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
          letI : CompleteSpace Vpolar :=
            (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
          let hρLog : Measurable (ρ i ∘ ℓ) := (hρm i).comp (Real.measurable_log.comp
            (NNReal.continuous_coe.comp
              (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable)
          let A : W₀ →L[ℂ] W₀ :=
            hardySobolevTestAction μJ (continuousSIdeleQuotientNorm F S) 0 0 0 le_rfl le_rfl Φ
          let M : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ (ρ i ∘ ℓ) hρLog (fun g ↦ hρ i (ℓ g))
          (Full i).val = Vfull.starProjection * (M.comp A) * Vfull.starProjection ∧
          (Polar i).val = Vpolar.starProjection * (M.comp A) * Vpolar.starProjection) ∧
        Tendsto (fun i ↦ hilbertTrace (Full i) - hilbertTrace (Polar i)) l
          (𝓝 (∫ t, k t * (Real.exp (-|t| / 2) : ℂ))) := by
  classical
  have hZero := exists_sLocalFullPW_upperCutoff_trace_sub_polar_eq_orderZero
    (F := F) (S := S) τ hτ (B := 1) zero_lt_one Φ 0 (fun _ ↦ 0)
      measurable_const (fun _ ↦ by simp) (fun _ _ ↦ rfl)
  rcases hZero with ⟨χ₀, k₀, q₀, U₀, _, _, hχ₀, hsec₀, hk₀, hU₀, hq₀, _, _, _, _⟩
  have hEach (i : ι) := exists_sLocalFullPW_upperCutoff_trace_sub_polar_eq_orderZero
    (F := F) (S := S) τ hτ (hB i) Φ (Tmax i) (ρ i) (hρm i) (hρ i) (hρT i)
  choose χ k q U Full Polar hSpec using hEach
  refine ⟨k₀, hk₀, Full, Polar, fun i ↦ ?_, ?_⟩
  · let hi := hSpec i
    exact ⟨hi.2.2.2.2.2.1, hi.2.2.2.2.2.2.1⟩
  have hUnit : ∀ᵐ ξ : ℝ ∂volume, ‖phase(χ₀,ξ)‖ = 1 := by
    exact ae_of_all _ fun ξ ↦ sLocalRhoFactor_norm_criticalLine χ₀ _
      (by norm_num [sLocalRadialThetaCriticalParameter, Complex.sub_re, Complex.mul_re])
  have hLim := tendsto_reflectedPolarConvolution_pairing (l := l) U₀
    (fun ξ ↦ phase(χ₀,ξ)) hU₀ hUnit
    (k := (k₀ : ℝ → ℂ)) (q := (q₀ : ℝ → ℂ)) k₀.integrable q₀.integrable (ae_of_all _ hq₀)
    (fun i ↦ -Real.log (B i)) ρ hρm hρ hOne
  refine hLim.congr' (.of_forall fun i ↦ ?_)
  let hi := hSpec i
  obtain ⟨_, _, _, hqEq, hUEq⟩ := sLocalTrivialCutoffFourierWitnesses_eq
    (F := F) (S := S) τ hτ Φ (χ i) χ₀ hi.1 hi.2.1 hχ₀ hsec₀
      (k i) (q i) k₀ q₀ (U i) U₀ hi.2.2.1 hk₀ hi.2.2.2.1 hU₀ hi.2.2.2.2.1 hq₀
  have h := hi.2.2.2.2.2.2.2.1
  rw [hqEq, hUEq] at h
  exact h.symm

end RiemannMasullo
