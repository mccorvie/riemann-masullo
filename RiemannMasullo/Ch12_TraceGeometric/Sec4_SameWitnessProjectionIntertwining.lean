module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FullReflectedProjection
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Contraction

/-! # Intertwining for a specified reflected map and band -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- The orthogonal projection on a subspace represented isometrically by a
real right half-line is carried to its indicator multiplier. -/
theorem l2IndicatorMultiplier_Ici_comp_eq_comp_starProjection_of_isometric_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (a : ℝ) (T : E →L[ℂ] FlatL2) (hT : ‖T‖ ≤ 1)
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (hIso : ∀ v ∈ V, ‖T v‖ = ‖v‖)
    (hRange : Set.range (fun v : V ↦ T v.val) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < a → r y = 0}) :
    (l2IndicatorMultiplier volume (Ici a) measurableSet_Ici).comp T =
      T.comp V.starProjection := by
  let R := l2AESupported (volume : Measure ℝ) (Ici a) measurableSet_Ici
  have hR : R.toSubmodule = V.map T.toLinearMap := by
    ext r
    change r ∈ R ↔ r ∈ V.map T.toLinearMap
    have hMem : r ∈ R ↔ ∀ᵐ y : ℝ ∂volume, y < a → r y = 0 := by
      simp only [R, mem_l2AESupported_iff, mem_Ici, not_le]
    rw [hMem]
    change r ∈ {v : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < a → v y = 0} ↔ _
    rw [← hRange]
    constructor
    · rintro ⟨v, hv⟩
      exact Submodule.mem_map.mpr ⟨v.val, v.property, hv⟩
    · rintro ⟨v, hv, heq⟩
      exact ⟨⟨v, hv⟩, heq⟩
  have hP : R.toSubmodule.starProjection = l2IndicatorMultiplier volume (Ici a) measurableSet_Ici :=
    starProjection_l2AESupported volume (Ici a) measurableSet_Ici
  have hInter :=
    starProjection_comp_eq_comp_starProjection_of_isometric_image T hT V R.toSubmodule hIso hR
  rw [hP] at hInter
  exact hInter

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "W₀" => CompactIntervalSobolev (sLocalQuotientTamagawaMeasure F S)
  (logSIdeleQuotientNorm F S) 0 0 0
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B

/-- The concrete order-zero projection intertwines the given reflected map
once the exact range and recovery statements for that same map are supplied. -/
theorem sLocalFullReflectedProjection_comp_eq_of_coordinates_orderZero
    (angular : PontryaginDual J₁) (B : ℝ)
    (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
    (hT : ‖U.toLinearIsometry.toContinuousLinearMap.comp Q‖ ≤ 1)
    (hRecover : ∀ v ∈ fullBand(angular,B), L (Q v) = v)
    (hRange : Set.range (fun v : fullBand(angular,B) ↦ U (Q v.val)) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0}) :
    let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
    let V : Submodule ℂ W₀ := fullBand(angular,B)
    letI : CompleteSpace V :=
      (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    (l2IndicatorMultiplier volume (Ici (-Real.log B)) measurableSet_Ici).comp T =
      T.comp V.starProjection := by
  intro T V
  let : CompleteSpace V :=
    (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hIso (v : W₀) (hv : v ∈ V) : ‖T v‖ = ‖v‖ := by
    change ‖U (Q v)‖ = ‖v‖
    rw [U.norm_map, ← L.norm_map (Q v), hRecover v hv]
  exact l2IndicatorMultiplier_Ici_comp_eq_comp_starProjection_of_isometric_image
    (-Real.log B) T hT V hIso hRange

end RiemannMasullo
