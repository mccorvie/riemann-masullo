module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_CompactFourierAngularImage
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedProductCutoff
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SameWitnessProjectionIntertwining
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SameWitnessReflectedPolarLine
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3_CompactFourierBand
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Contraction
import Mathlib.MeasureTheory.Function.Holder

/-! # Common angular coordinates for the realized order-zero cutoff -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "N" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker N
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "Bₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" => (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker N))
  continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "prodNorm(" u ")" =>
  (∏ w : InfinitePlace F, ‖(u : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
    ∏ v : S, ‖(u : Aₛ).2 v‖
local notation "fullGen(" angular ")" =>
  Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos angular
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B

/-- The common reflected coordinates realize the frequency cutoff and
intertwine the invariant-band projection at the specified upper radius. -/
theorem exists_sLocalFullReflectedProductCutoff_with_angularLift_atBand_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) (b : ℝ → ℂ)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 δ))
    (B : ℝ) (hB : 0 < B) :
    ∃ (χ : PontryaginDual Jₛ) (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
      (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      (∀ v, (L v : Jₛ → ℂ) =ᵐ[ν₀] fun y ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ y : ℂ)⁻¹ * v (ℓ y)) ∧
      LeftInverse Q L ∧ Q.adjoint = L.toContinuousLinearMap ∧
      (Submodule.span ℂ {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧
        fullGen(angular) f = u}).topologicalClosure = LinearMap.range L.toLinearMap ∧
      (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x) ∧
      let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
      sLocalFullReflectedGenAE τ angular χ T ∧
      (∀ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val →
        ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
          sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f =
            (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
          fullGen(angular) g = T.adjoint (M (T (fullGen(angular) f)))) ∧
      let V : Submodule ℂ W₀ := fullBand(angular,B)
      letI : CompleteSpace V :=
        (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
      (l2IndicatorMultiplier volume (Ici (-Real.log B)) measurableSet_Ici).comp T =
        T.comp V.starProjection ∧
      sLocalReflectedPolarLineData (F := F) (S := S) angular B T := by
  obtain ⟨χ, Q, L, U, hχ, hsec, hQ, _, hL, _, hGen, hBands⟩ :=
    exists_sLocalFullReflectedCoordinates_uniform_orderZero (F := F) (S := S) τ hτ angular
  let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro v
    change ‖U (Q v)‖ ≤ 1 * ‖v‖
    rw [U.norm_map]
    exact (Q.le_opNorm v).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg v))
  let Gens := {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧ fullGen(angular) f = u}
  let C := (Submodule.span ℂ Gens).topologicalClosure
  have hC : C = LinearMap.range L.toLinearMap :=
    sLocalFullTheta_compactFourier_closedSpan_eq_lift_range angular Q L U
      (fun B hB ↦ (hBands B hB).1) (fun B hB ↦ (hBands B hB).2.2.1)
  have hMem (f : Bₛ) (hf : HasCompactSupport (sAdeleSchwartzFourier f).val) :
      ∃ B : ℝ, 0 < B ∧ fullGen(angular) f ∈ fullBand(angular,B) := by
    obtain ⟨B, hB, ht⟩ :=
      @exists_sLocalPWTests_sameStage_productRegion_of_hasCompactSupport_fourier F _ _ S f hf
    exact ⟨B, hB, Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨f, ht, rfl⟩)⟩
  let D : W₀ →L[ℂ] W₀ := L.toContinuousLinearMap.comp Q - ContinuousLinearMap.id ℂ W₀
  have hKer : C ≤ D.ker := by
    apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) D.isClosed_ker
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨B, hB, hv⟩ := hMem f hf
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr ((hBands B hB).1 _ hv))
  have hQL (r : FlatL2) : Q (L r) = r := by
    apply L.injective
    have hmem : L r ∈ C := hC.symm ▸ LinearMap.mem_range_self L.toLinearMap r
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hKer hmem))
  have hQadj : Q.adjoint = L.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro r
    change Q.adjoint r = L r
    have hIso : ‖Q (L r)‖ = ‖L r‖ := by rw [hQL, L.norm_map]
    have h := adjoint_apply_apply_eq_of_norm_preserved Q hQ (L r) hIso
    simpa only [hQL] using h
  let symbol (x : ℝ) := b (Real.exp (-x))
  have hs : MemLp symbol (⊤ : ℝ≥0∞) (volume : Measure ℝ) := memLp_top_of_bound
    (hb.continuous.comp (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ hbdd (Real.exp (-x)) (Real.exp_pos _).le)
  let m := ContinuousLinearMap.mul ℂ ℂ
  let M := m.holderL volume (⊤ : ℝ≥0∞) 2 2 (hs.toLp symbol)
  have hM (r : FlatL2) : (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x :=
    (m.coeFn_holder (r := 2) (hs.toLp symbol) r).trans
      (hs.coeFn_toLp.mono fun x hx ↦ congrArg (· * r x) hx)
  have hRealize (f : Bₛ) (hf : HasCompactSupport (sAdeleSchwartzFourier f).val) :
      ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
        sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f =
          (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
        fullGen(angular) g = T.adjoint (M (T (fullGen(angular) f))) := by
    obtain ⟨g, hg, hCut, hMul⟩ :=
      @exists_sLocalFullReflectedGenAE_productCutoff_transfer F _ _ S
        τ hτ angular χ T hGen b hb δ hδ hplateau M hM f hf
    have hgC : fullGen(angular) g ∈ C :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span (show _ ∈ Gens from ⟨g, hg, rfl⟩))
    have hRecover : L (Q (fullGen(angular) g)) = fullGen(angular) g :=
      sub_eq_zero.mp (LinearMap.mem_ker.mp (hKer hgC))
    have hIso : ‖T (fullGen(angular) g)‖ = ‖fullGen(angular) g‖ := by
      change ‖U (Q (fullGen(angular) g))‖ = ‖fullGen(angular) g‖
      rw [U.norm_map, ← L.norm_map (Q (fullGen(angular) g)), hRecover]
    have hFix := adjoint_apply_apply_eq_of_norm_preserved T hT (fullGen(angular) g) hIso
    exact ⟨g, hg, hCut, hFix.symm.trans (congrArg T.adjoint hMul)⟩
  have hInter :=
    @sLocalFullReflectedProjection_comp_eq_of_coordinates_orderZero F _ _ S
      angular B Q L U hT (hBands B hB).1 (hBands B hB).2.2.1
  have hPolar :=
    @sLocalFullReflectedPolarLine_of_coordinates_orderZero F _ _ S
      angular B Q L U hQ (hBands B hB).1 (hBands B hB).2.2.1 (hBands B hB).2.2.2
  exact ⟨χ, Q, L, U, M, hχ, hsec, hL, hQL, hQadj, hC, hM, hGen, hRealize, hInter, hPolar⟩

/-- The angular lift, the coefficient map, and the reflected cutoff can
be chosen together. In these coordinates the lift of the flat real space
is the closed span of compact Fourier generators of this character. -/
theorem exists_sLocalFullReflectedProductCutoff_with_angularLift_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) (b : ℝ → ℂ)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 δ)) :
    ∃ (χ : PontryaginDual Jₛ) (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
      (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      (∀ v, (L v : Jₛ → ℂ) =ᵐ[ν₀] fun y ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ y : ℂ)⁻¹ * v (ℓ y)) ∧
      LeftInverse Q L ∧ Q.adjoint = L.toContinuousLinearMap ∧
      (Submodule.span ℂ {u : W₀ | ∃ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val ∧
        fullGen(angular) f = u}).topologicalClosure = LinearMap.range L.toLinearMap ∧
      (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x) ∧
      let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
      sLocalFullReflectedGenAE τ angular χ T ∧
      ∀ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val →
        ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
          sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f =
            (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
          fullGen(angular) g = T.adjoint (M (T (fullGen(angular) f))) := by
  have hData :=
    @exists_sLocalFullReflectedProductCutoff_with_angularLift_atBand_orderZero F _ _ S
      τ hτ angular b hb hbdd δ hδ hplateau 1 one_pos
  obtain ⟨χ, Q, L, U, M, hCoordinates⟩ := hData
  obtain ⟨hχ, hsec, hL, hQL, hQadj, hC, hM, hGen, hRealize, _⟩ := hCoordinates
  exact ⟨χ, Q, L, U, M, hχ, hsec, hL, hQL, hQadj, hC, hM, hGen, hRealize⟩

end RiemannMasullo
