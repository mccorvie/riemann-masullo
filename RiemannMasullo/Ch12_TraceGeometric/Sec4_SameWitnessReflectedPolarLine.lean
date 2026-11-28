module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualReflectedPolarComplement
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Contraction

/-! # The polar line for a specified reflected coordinate map -/

public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal InnerProductSpace NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "W₀" => CompactIntervalSobolev (sLocalQuotientTamagawaMeasure F S)
  (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "polarBand(" angular "," B ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B

/-- A reflected map is contractive and in the trivial character carries a unit vector
of the polar line to the normalized half-line exponential, with recovery by the adjoint. -/
@[expose] def sLocalReflectedPolarLineData
    (angular : PontryaginDual J₁) (B : ℝ) (T : W₀ →L[ℂ] FlatL2) : Prop :=
  ‖T‖ ≤ 1 ∧ (angular = 1 →
    ∃ u : fullBand(angular,B), T u.val = normalizedHalflineExponentialL2 (-Real.log B) ∧
      ‖u.val‖ = 1 ∧ fullBand(angular,B) ⊓ polarBand(angular,B)ᗮ = ℂ ∙ u.val ∧
      T.adjoint (normalizedHalflineExponentialL2 (-Real.log B)) = u.val)

/-- The full and polar ranges of the given reflected coordinates determine the polar line
for that same map. -/
theorem sLocalFullReflectedPolarLine_of_coordinates_orderZero
    (angular : PontryaginDual J₁) (B : ℝ)
    (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (hQ : ‖Q‖ ≤ 1)
    (hRecover : ∀ v ∈ fullBand(angular,B), L (Q v) = v)
    (hFullRange : Set.range (fun v : fullBand(angular,B) ↦ U (Q v.val)) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0})
    (hPolarRange : Set.range (fun v : polarBand(angular,B) ↦ U (Q v.val)) =
      {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0) ∧
        (angular = 1 → (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0)}) :
    sLocalReflectedPolarLineData angular B (U.toLinearIsometry.toContinuousLinearMap.comp Q) := by
  let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
  let Vfull : Submodule ℂ W₀ := fullBand(angular,B)
  let Vpolar : Submodule ℂ W₀ := polarBand(angular,B)
  change sLocalReflectedPolarLineData angular B T
  unfold sLocalReflectedPolarLineData
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro v
    change ‖U (Q v)‖ ≤ 1 * ‖v‖
    rw [U.norm_map]
    exact (Q.le_opNorm v).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg v))
  refine ⟨hT, ?_⟩
  intro hAngular
  have hLe : Vpolar ≤ Vfull :=
    (Isolated.sLocalPWSobolev_polarComplement (F := F) (S := S) (s := 0)
      le_rfl halfPos angular B).1
  have hIso (v : W₀) (hv : v ∈ Vfull) : ‖T v‖ = ‖v‖ := by
    change ‖U (Q v)‖ = ‖v‖
    rw [U.norm_map, ← L.norm_map (Q v), hRecover v hv]
  have hRange : Set.range (fun v : Vpolar ↦ T v.val) =
      {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0) ∧
        (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0} := by
    change Set.range (fun v : polarBand(angular,B) ↦ U (Q v.val)) = _
    rw [hPolarRange]
    simp only [hAngular, true_implies]
  obtain ⟨u, ⟨hImage, hNorm, hLine⟩, _⟩ :=
    existsUnique_normalizedPolarDirection_of_reflectedRanges Vfull Vpolar hLe T hIso
      (-Real.log B) hFullRange hRange
  have hAdj : T.adjoint (normalizedHalflineExponentialL2 (-Real.log B)) = u.val := by
    rw [← hImage]
    exact adjoint_apply_apply_eq_of_norm_preserved T hT u.val (hIso u.val u.property)
  exact ⟨u, hImage, hNorm, hLine, hAdj⟩

end RiemannMasullo
