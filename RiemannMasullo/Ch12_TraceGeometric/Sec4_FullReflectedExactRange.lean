module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedCompactProfiles
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedMomentClosure
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedTrivialMoment

/-! # Full and polar order-zero ranges of a common reflected map -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "W₀" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "polarBand(" angular "," B ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "bandTests(" B ")" =>
  sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B)
local notation "fullGen(" angular ")" =>
  Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos angular
local notation "polarGen(" angular ")" =>
  sLocalPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos angular
local notation "reflectedRep(" τ "," χ "," f ")" => fun y : ℝ ↦
  (Real.sqrt (Measure.real η univ) : ℂ) *
    sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-y)

/-- The normalized reflected map on the full order-zero band has exactly
right-half-line-supported range once it is isometric there and has the
Fourier-test representatives. -/
theorem sLocalFullPWSobolev_reflectedRange_orderZero_of_map
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) (χ : PontryaginDual Jₛ) {B : ℝ} (hB : 0 < B)
    (T : W₀ →L[ℂ] FlatL2)
    (hFullGen : ∀ f : Bₛ, f ∈ bandTests(B) →
      (T (fullGen(angular) f) : ℝ → ℂ) =ᵐ[volume] reflectedRep(τ,χ,f))
    (hFullIso : ∀ u ∈ fullBand(angular,B), ‖T u‖ = ‖u‖)
    (hFullSupport : ∀ u ∈ fullBand(angular,B), ∀ᵐ y : ℝ ∂volume, y < -Real.log B → T u y = 0) :
    Set.range (fun u : fullBand(angular,B) ↦ T u.val) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0} := by
  let V : Submodule ℂ W₀ := fullBand(angular,B)
  have hClosed : IsClosed (V : Set W₀) := Submodule.isClosed_topologicalClosure _
  have hRealize : ∀ r : ℝ → ℂ, HasCompactSupport r → ContDiff ℝ (∞ : ℕ∞ω) r →
      tsupport r ⊆ Ioi (-Real.log B) →
      ∃ u ∈ fullBand(angular,B), (T u : ℝ → ℂ) =ᵐ[volume] r := by
    intro r hrc hrd hrs
    obtain ⟨f, hfband, hf⟩ := exists_sLocalPW_reflectedSmoothGenerator τ hτ χ r hrd hrc hB hrs
    refine ⟨fullGen(angular) f, ?_, (hFullGen f hfband).trans (ae_of_all _ hf)⟩
    change fullGen(angular) f ∈ ((bandTests(B)).map (fullGen(angular))).topologicalClosure
    exact Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨f, hfband, rfl⟩)
  have hRange := range_reflectedInput_eq_of_smoothCore V hClosed T
    (-Real.log B) False hFullIso hFullSupport (fun _ _ h ↦ h.elim)
    (fun r hrc hrd hrs _ ↦ hRealize r hrc hrd hrs)
  change Set.range (fun u : V ↦ T u.val) =
    {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0}
  refine hRange.trans (Set.ext fun r ↦ ?_)
  exact ⟨fun hr ↦ hr.1, fun hr ↦ ⟨hr, fun h ↦ h.elim⟩⟩

/-- For one common reflected map, the full order-zero band has the whole
supported range, and the polar level imposes the exponential moment in the
trivial norm-one type. -/
theorem sLocalFullAndPolarPWSobolev_reflectedRanges_orderZero_of_map
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = angular)
    (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1) {B : ℝ} (hB : 0 < B)
    (T : W₀ →L[ℂ] FlatL2)
    (hFullGen : ∀ f : Bₛ, (T (fullGen(angular) f) : ℝ → ℂ) =ᵐ[volume] reflectedRep(τ,χ,f))
    (hFullIso : ∀ u ∈ fullBand(angular,B), ‖T u‖ = ‖u‖)
    (hFullSupport : ∀ u ∈ fullBand(angular,B), ∀ᵐ y : ℝ ∂volume, y < -Real.log B → T u y = 0) :
    (Set.range (fun u : fullBand(angular,B) ↦ T u.val) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0}) ∧
    (Set.range (fun u : polarBand(angular,B) ↦ T u.val) =
      {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0) ∧
        (angular = 1 → (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0)}) := by
  refine ⟨sLocalFullPWSobolev_reflectedRange_orderZero_of_map τ hτ angular χ hB T
    (fun f _ ↦ hFullGen f) hFullIso hFullSupport, ?_⟩
  let P : Submodule ℂ W₀ := polarBand(angular,B)
  have hClosed : IsClosed (P : Set W₀) := Submodule.isClosed_topologicalClosure _
  have hLe : polarBand(angular,B) ≤ fullBand(angular,B) :=
    (Isolated.sLocalPWSobolev_polarComplement (F := F) (S := S) (s := 0) le_rfl halfPos angular B).1
  have hPolarGen (f : Zₛ) :
      (T (polarGen(angular) f) : ℝ → ℂ) =ᵐ[volume] reflectedRep(τ,χ,f.val) := by
    rw [← Isolated.sLocalFullPWThetaSobolevMap_polar (F := F) (S := S) (s := 0) halfPos angular f]
    exact hFullGen f.val
  have hPolarSupport (u : W₀) (hu : u ∈ polarBand(angular,B)) :
      ∀ᵐ y : ℝ ∂volume, y < -Real.log B → T u y = 0 := hFullSupport u (hLe hu)
  have hMoment (u : W₀) (hu : u ∈ polarBand(angular,B)) (hangular : angular = 1) :
      (∫ y, (Real.exp (-y / 2) : ℂ) * T u y) = 0 := by
    subst hangular
    exact (sLocalInvariantPWSobolev_reflectedTrivialMoment_of_representatives
      (s := 0) le_rfl τ hτ B χ T hχ hsec hPolarGen hPolarSupport u hu).2
  refine range_reflectedInput_eq_of_smoothCore P hClosed T
    (-Real.log B) (angular = 1) (fun u hu ↦ hFullIso u (hLe hu)) hPolarSupport hMoment ?_
  intro r hrc hrd hrs hrm
  obtain ⟨f, hfpolar, hfband, hf⟩ := exists_sLocalPolarPW_reflectedSmoothGenerator
    τ hτ χ hsec r hrd hrc hB hrs (fun h ↦ hrm (hχ.symm.trans h))
  let z : Zₛ := ⟨f, hfpolar⟩
  refine ⟨polarGen(angular) z, ?_, (hPolarGen z).trans (ae_of_all _ hf)⟩
  exact sLocalInvariantPWSobolev_mem (F := F) (S := S) (s := 0) le_rfl halfPos angular B z hfband

end RiemannMasullo
