module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3_CompactFourierBand
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualFixedBandTraceClass
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Contraction
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! # Density of compact Fourier tests in the order-zero angular image -/

public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "W₀" => CompactIntervalSobolev (sLocalQuotientTamagawaMeasure F S)
  (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "bandTests(" B ")" =>
  sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B)
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "fullGen(" angular ")" =>
  Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos angular

/-- Uniform exact reflected ranges identify the closed span of compact Fourier
theta generators with the entire order-zero isometric angular image. -/
theorem sLocalFullTheta_compactFourier_closedSpan_eq_lift_range
    (angular : PontryaginDual J₁) (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
    (hRecover : ∀ B : ℝ, 0 < B → ∀ u ∈ fullBand(angular,B), L (Q u) = u)
    (hRange : ∀ B : ℝ, 0 < B →
      Set.range (fun u : fullBand(angular,B) ↦ U (Q u.val)) =
        {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0}) :
    (Submodule.span ℂ {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      fullGen(angular) f = u}).topologicalClosure = LinearMap.range L.toLinearMap := by
  let Gens := {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧
    fullGen(angular) f = u}
  let C := (Submodule.span ℂ Gens).topologicalClosure
  have hC : IsClosed (C : Set W₀) := Submodule.isClosed_topologicalClosure _
  have hBand (B : ℝ) : fullBand(angular,B) ≤ C := by
    change ((bandTests(B)).map (fullGen(angular))).topologicalClosure ≤ C
    refine Submodule.topologicalClosure_minimal _ ?_ hC
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hgc, _⟩ := (mem_sLocalPWTests (F := F) (S := S) (T := S) le_rfl
      (sLocalPWProductRegion S B) f).mp hf
    have hself : sAdeleSchwartzTransition F (le_rfl (a := S)) g = g := by
      classical
      apply Subtype.ext
      funext x
      rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
        ite_eq_left (fun w hw ↦ (hw w.property).elim)]
    rw [hself] at hg
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hg ▸ hgc, rfl⟩)
  apply le_antisymm
  · have hLClosed : IsClosed (LinearMap.range L.toLinearMap : Set W₀) :=
      L.isometry.isClosedEmbedding.isClosed_range
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hLClosed
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨B, hB, hfBand⟩ :=
      exists_sLocalPWTests_sameStage_productRegion_of_hasCompactSupport_fourier f hf
    have hMem : fullGen(angular) f ∈ fullBand(angular,B) :=
      Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨f, hfBand, rfl⟩)
    exact LinearMap.mem_range.mpr ⟨Q (fullGen(angular) f), hRecover B hB _ hMem⟩
  · let J : FlatL2 →L[ℂ] W₀ := L.toContinuousLinearMap.comp
      U.symm.toLinearIsometry.toContinuousLinearMap
    let Core := {v : FlatL2 | ∃ g : ℝ → ℂ, (v : ℝ → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ (∞ : ℕ∞ω) g}
    have hDense : Dense Core := Lp.dense_hasCompactSupport_contDiff
      (μ := (volume : Measure ℝ)) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
    have hCore : Core ⊆ J ⁻¹' (C : Set W₀) := by
      rintro r ⟨g, hg, hgc, _⟩
      have hK : IsCompact (tsupport g) := hgc
      obtain ⟨a, ha⟩ := hK.bddBelow
      let B := Real.exp (-a)
      have hB : 0 < B := Real.exp_pos _
      have hlog : -Real.log B = a := by simp [B]
      have hr : r ∈ Set.range (fun u : fullBand(angular,B) ↦ U (Q u.val)) := by
        rw [hRange B hB]
        change ∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0
        rw [hlog]
        filter_upwards [hg] with y hy hya
        rw [hy]
        exact image_eq_zero_of_notMem_tsupport (fun h ↦ (not_le_of_gt hya) (ha h))
      obtain ⟨u, hu⟩ := hr
      change U (Q u.val) = r at hu
      change J r ∈ C
      rw [← hu]
      change L (U.symm (U (Q u.val))) ∈ C
      rw [U.symm_apply_apply, hRecover B hB u.val u.property]
      exact hBand B u.property
    have hPreimage : IsClosed (J ⁻¹' (C : Set W₀)) := hC.preimage J.continuous
    intro u hu
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hu
    have hMem := (closure_minimal hCore hPreimage) (hDense (U v))
    change L (U.symm (U v)) ∈ C at hMem
    rw [U.symm_apply_apply] at hMem
    change L v = u at hv
    exact hv ▸ hMem

/-- The order-zero angular lift has as its closed image exactly the compact
Fourier theta span. The angular coefficient is its adjoint there and on
the whole ambient Hilbert space. -/
theorem exists_sLocalFullReflectedAngularImage_orderZero
    (τ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ) (hτ : Function.RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) :
    ∃ (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀),
      ‖Q‖ ≤ 1 ∧ Function.LeftInverse Q L ∧ Q.adjoint = L.toContinuousLinearMap ∧
      (Submodule.span ℂ {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧
        fullGen(angular) f = u}).topologicalClosure = LinearMap.range L.toLinearMap := by
  obtain ⟨_, Q, L, U, _, _, hQ, _, _, _, _, hBands⟩ :=
    exists_sLocalFullReflectedCoordinates_uniform_orderZero (F := F) (S := S) τ hτ angular
  let Gens := {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧
    fullGen(angular) f = u}
  let C := (Submodule.span ℂ Gens).topologicalClosure
  have hC : C = LinearMap.range L.toLinearMap :=
    sLocalFullTheta_compactFourier_closedSpan_eq_lift_range angular Q L U
      (fun B hB ↦ (hBands B hB).1) (fun B hB ↦ (hBands B hB).2.2.1)
  let D : W₀ →L[ℂ] W₀ := L.toContinuousLinearMap.comp Q - ContinuousLinearMap.id ℂ W₀
  have hKer : C ≤ D.ker := by
    apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) D.isClosed_ker
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨B, hB, hfBand⟩ :=
      @exists_sLocalPWTests_sameStage_productRegion_of_hasCompactSupport_fourier F _ _ S f hf
    have hMem : fullGen(angular) f ∈ fullBand(angular,B) :=
      Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨f, hfBand, rfl⟩)
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr ((hBands B hB).1 _ hMem))
  have hQL (r : FlatL2) : Q (L r) = r := by
    apply L.injective
    have hMem : L r ∈ C := hC.symm ▸ LinearMap.mem_range_self L.toLinearMap r
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hKer hMem))
  refine ⟨Q, L, hQ, hQL, ?_, hC⟩
  apply ContinuousLinearMap.ext
  intro r
  change Q.adjoint r = L r
  have hIso : ‖Q (L r)‖ = ‖L r‖ := by rw [hQL, L.norm_map]
  have h := adjoint_apply_apply_eq_of_norm_preserved Q hQ (L r) hIso
  simpa only [hQL] using h

end RiemannMasullo
