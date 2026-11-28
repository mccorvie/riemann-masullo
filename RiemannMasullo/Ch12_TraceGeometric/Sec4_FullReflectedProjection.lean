module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualFixedBandTraceClass
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space.SupportProjection
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Contraction

/-! # The full-band projection in the reflected order-zero coordinates -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "W₀" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)

/-- Paper: Theorem 12.4.1.1, pp. 515–518. One order-zero reflected map
intertwines the actual full-band projection at each radius with truncation
to the reflected half-line.
Deviation: This identifies the projection in each norm-one character
at fixed Sobolev order zero. -/
theorem exists_sLocalFullReflectedProjection_uniform_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) :
    ∃ (χ : PontryaginDual Jₛ) (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
      (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
      ‖T‖ ≤ 1 ∧ sLocalFullReflectedGenAE τ ω χ T ∧
      ∀ B : ℝ, 0 < B →
        let V : Submodule ℂ W₀ :=
          Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos ω B
        letI : CompleteSpace V :=
          (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
        let P : FlatL2 →L[ℂ] FlatL2 :=
          l2IndicatorMultiplier volume (Ici (-Real.log B)) measurableSet_Ici
        (∀ v ∈ V, ‖T v‖ = ‖v‖) ∧
        V.starProjection = T.adjoint.comp (P.comp T) ∧
        P.comp T = T.comp V.starProjection ∧
        V.starProjection = L.toContinuousLinearMap.comp
          (U.symm.toLinearIsometry.toContinuousLinearMap.comp (P.comp T)) := by
  obtain ⟨χ, Q, L, U, hχ, hsec, hQnorm, _, _, _, hGen, hBands⟩ :=
    exists_sLocalFullReflectedCoordinates_uniform_orderZero (F := F) (S := S) τ hτ ω
  let T : W₀ →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp Q
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro v
    change ‖U (Q v)‖ ≤ 1 * ‖v‖
    rw [U.norm_map]
    exact (Q.le_opNorm v).trans (mul_le_mul_of_nonneg_right hQnorm (norm_nonneg v))
  refine ⟨χ, Q, L, U, hχ, hsec, hT, hGen, ?_⟩
  intro B hB V P
  let : CompleteSpace V :=
    (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨hRecover, _, hFullRange, _⟩ := hBands B hB
  have hIso (v : W₀) (hv : v ∈ V) : ‖T v‖ = ‖v‖ := by
    change ‖U (Q v)‖ = ‖v‖
    rw [U.norm_map, ← L.norm_map (Q v), hRecover v hv]
  let R := l2AESupported (volume : Measure ℝ) (Ici (-Real.log B)) measurableSet_Ici
  have hSet : Set.range (fun v : V ↦ T v.val) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0} := hFullRange
  have hR : R.toSubmodule = V.map T.toLinearMap := by
    ext r
    change r ∈ R ↔ r ∈ V.map T.toLinearMap
    have hMem : r ∈ R ↔ ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0 := by
      simp only [R, mem_l2AESupported_iff, mem_Ici, not_le]
    rw [hMem]
    change r ∈ {v : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → v y = 0} ↔ _
    rw [← hSet]
    constructor
    · rintro ⟨v, hv⟩
      exact Submodule.mem_map.mpr ⟨v.val, v.property, hv⟩
    · rintro ⟨v, hv, heq⟩
      exact ⟨⟨v, hv⟩, heq⟩
  have hP : R.toSubmodule.starProjection = P :=
    starProjection_l2AESupported volume (Ici (-Real.log B)) measurableSet_Ici
  let J : FlatL2 →L[ℂ] W₀ := L.toContinuousLinearMap.comp
    U.symm.toLinearIsometry.toContinuousLinearMap
  have hJ (v : W₀) (hv : v ∈ V) : J (T v) = v := by
    change L (U.symm (U (Q v))) = v
    rw [U.symm_apply_apply, hRecover v hv]
  have hAdj := starProjection_eq_adjoint_comp_of_isometric_image T hT V R.toSubmodule hIso hR
  have hInter :=
    starProjection_comp_eq_comp_starProjection_of_isometric_image T hT V R.toSubmodule hIso hR
  have hLift :=
    starProjection_eq_recovery_comp_of_isometric_image T J hT V R.toSubmodule hIso hR hJ
  rw [hP] at hAdj hInter hLift
  exact ⟨hIso, hAdj, hInter, hLift⟩

end RiemannMasullo
