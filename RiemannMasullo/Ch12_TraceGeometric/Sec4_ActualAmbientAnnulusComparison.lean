module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedAnnulusOrbitComparison
import RiemannMasullo.Ch12_TraceGeometric.Sec4_RadialOrbitLiftIndependence
import RiemannMasullo.Ch12_TraceGeometric.Sec4_CommonReflectedCutoffWitness
import RiemannMasullo.Ch12_TraceGeometric.Sec4_AngularConjugatedRows
import RiemannMasullo.Ch12_TraceGeometric.Sec4_AmbientReflectedGlue

/-! # The actual annular orbit operator on the order-zero ambient space -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1
  instSIdeleLocallyCompactSec1 instSAdeleMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local instance instSIdeleT2AmbientAnnulusComparison : T2Space Iₛ :=
  (sIdeleGroup_description F S).2.1
set_option quotPrecheck false
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "Bₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" => (ContinuousMonoidHom.mk
  (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
  continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "modS(" u ")" =>
  (∏ w : InfinitePlace F, ‖(u : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
    ∏ v : S, ‖(u : Aₛ).2 v‖
local notation "gen(" angular ")" => Isolated.sLocalFullPWThetaSobolevMap
  (F := F) (S := S) (s := 0) halfPos angular
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "orbitOrder" =>
  (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ)

private theorem ambientAnnulus_orderZeroMeasure_eq : (ν₀ : Measure Jₛ) = μJ := by
  have hzero (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
  change (μJ).withDensity (fun q ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (ℓ q))) = μJ
  simp only [hzero, ENNReal.ofReal_one]
  exact withDensity_one

local instance instOrderZeroFiniteOnCompactsAmbientAnnulusComparison :
    IsFiniteMeasureOnCompacts (ν₀ : Measure Jₛ) := by
  rw [ambientAnnulus_orderZeroMeasure_eq]
  infer_instance

local instance instOrderZeroInnerRegularAmbientAnnulusComparison :
    Measure.InnerRegular (ν₀ : Measure Jₛ) := by
  rw [ambientAnnulus_orderZeroMeasure_eq]
  infer_instance

local notation "OrbitRep(" f "," ρ "," b "," κ ")" =>
  (∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
    ∑' ξ : Hₛ, sLocalTraceCutoffKernel (F := F) (S := S) f
      (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) (fun w ↦ b (modS(w))) x (ξ.val * y).val)

private theorem ambientAnnulus_rawKernel_measurable
    (f : BruhatCompactSupport Iₛ) (b : ℝ → ℂ) (ρ : Jₛ → ℝ) (hρ : Measurable ρ)
    {ε C : ℝ} (hb : ContDiff ℝ (2 : ℕ) b) (hε : 0 < ε)
    (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hderiv : ∀ j ≤ 2, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ C)
    (κ : Jₛ → Jₛ → ℂ) (hRep : OrbitRep(f,ρ,b,κ)) :
    Measurable (Function.uncurry κ) := by
  obtain ⟨κ₀, hCont, hFactor⟩ :=
    exists_sLocalTrace_maskedRadialOrbitSeries_factor f b (fun q ↦ (ρ q : ℂ)) κ
      hb hε hplateau hderiv hRep
  have hFormula : Function.uncurry κ = fun p : Jₛ × Jₛ ↦ (ρ p.1 : ℂ) * κ₀ p.1 p.2 :=
    funext fun p ↦ hFactor p.1 p.2
  rw [hFormula]
  exact (Complex.measurable_ofReal.comp (hρ.comp measurable_fst)).mul hCont.measurable

private theorem ambientAnnulus_rawKernel_inputCovariant
    (f : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * x)) (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ) (hb : ContDiff ℝ orbitOrder b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb)
    (κ : Jₛ → Jₛ → ℂ) (hRep : OrbitRep(f,ρ,b,κ)) :
    ∀ (x y : Jₛ) (h : J₁), κ x (y * h.val) = (angular h : ℂ) * κ x y :=
  ((sLocalTrace_fixedAnnulus_orbitLift_independence_and_angular_covariance
    b hρ hb hε hplateau hderiv).2 f Φ.val hLift κ hRep angular hΦ).2

private theorem ambientAnnulus_kernel_eq_of_inputCovariance
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (hχ : χ.comp include₁ = angular) (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (Q : W₀ →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W₀)
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
    (hL : ∀ v, (L v : Jₛ → ℂ) =ᵐ[ν₀] fun y ↦
      (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ y : ℂ)⁻¹ * v (ℓ y))
    (hQL : LeftInverse Q L) (hQadj : Q.adjoint = L.toContinuousLinearMap)
    (K : Jₛ × Jₛ → ℂ) (hKm : Measurable K)
    (hK : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀))
    (hIn : ∀ (x y : Jₛ) (h : J₁), K (x, y * h.val) = (angular h : ℂ) * K (x, y))
    (M : FlatL2 →L[ℂ] FlatL2) (C : W₀ →L[ℂ] W₀)
    (V : Submodule ℂ W₀)
    (hSpan : V.topologicalClosure = LinearMap.range L.toLinearMap) :
    let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
    let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val
    let Reflected := C.comp (T.adjoint.comp (M.comp T))
    EqOn Kop Reflected (closure (V : Set W₀)) → Kop = Reflected := by
  intro T Kop Reflected hEq
  have hRows : ∀ᵐ x ∂ν₀, ∃ v : FlatL2,
      (L v : Jₛ → ℂ) =ᵐ[ν₀] fun y ↦ star (K (x, y)) :=
    sLocalTrace_ae_conjugatedRows_in_angularLift τ hτ angular χ hχ hsec L hL K hKm hK hIn
  exact integralKernelOperator_eq_reflectedAction_of_eqOn_angularClosure (X := Jₛ) (H := FlatL2)
    ν₀ hK Q L U M C hQL hQadj V hSpan hRows hEq

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517.
The reflected coordinates representing the actual annular operator
intertwine the full invariant-band projection at the given radius.
Deviation: The comparison fixes the annulus and Sobolev order zero. -/
theorem exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eq_atBand_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ)
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
      (let V : Submodule ℂ W₀ := fullBand(angular,B)
       letI : CompleteSpace V :=
         (show IsClosed (V : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
       (l2IndicatorMultiplier volume (Ici (-Real.log B)) measurableSet_Ici).comp T =
         T.comp V.starProjection) ∧
      OrbitRep(fLift,ρ,b,κ) ∧
      let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
      Measurable K ∧ ∃ hK : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀),
        let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val
        let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
        let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
        Kop = (R.comp A).comp (T.adjoint.comp (M.comp T)) := by
  intro N
  have hCoordinates :=
    @exists_sLocalFullReflectedProductCutoff_with_angularLift_atBand_orderZero F _ _ S
      τ hτ angular b hb hbdd εb hε hplateau B hB
  obtain ⟨χ, Q, L, U, M, hData⟩ := hCoordinates
  obtain ⟨hχ, hχsec, hL, hQL, hQadj, hSpan, hM, hGen, hRealize, hInter⟩ := hData
  have hbFin : ContDiff ℝ orbitOrder b := (contDiff_infty.mp hb) orbitOrder
  let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
  have hClosed :=
    @exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eqOn_orderZero F _ _ S
      fLift Φ hLift angular b Λ ερ εb Cb ρ hρ hbFin hε hplateau hderiv T M hRealize
  obtain ⟨κ, hKernelData⟩ := hClosed
  obtain ⟨hRep, hK, hEq⟩ := hKernelData
  let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
    ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
  have hK₂ : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀) := hK
  have hTwo : (2 : ℕ) ≤ orbitOrder := by omega
  have hκm : Measurable (Function.uncurry κ) :=
    ambientAnnulus_rawKernel_measurable (F := F) (S := S) fLift b ρ hρ.measurable
      ((contDiff_infty.mp hb) 2) hε hplateau (fun j hj ↦ hderiv j (hj.trans hTwo)) κ hRep
  have hden (q : Jₛ) : intervalSobolevDensity 0 0 0 (ℓ q) = 1 := by
    simp [intervalSobolevDensity]
  have hKm : Measurable K := by
    have hNm : Measurable N :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)).measurable
    have hSqrt :
        Measurable (fun p : Jₛ × Jₛ ↦ (Real.sqrt (N p.1 * N p.2) : ℂ)) :=
      Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
        ((hNm.comp measurable_fst).mul (hNm.comp measurable_snd)))
    dsimp only [K]
    simp only [hden, Complex.ofReal_one, mul_one]
    exact (hSqrt.mul hκm).div measurable_const
  have hκIn : ∀ (x y : Jₛ) (h : J₁), κ x (y * h.val) = (angular h : ℂ) * κ x y :=
    ambientAnnulus_rawKernel_inputCovariant (F := F) (S := S) fLift Φ hLift angular hΦ b hρ hbFin
      hε hplateau hderiv κ hRep
  have hKIn (x y : Jₛ) (h : J₁) : K (x, y * h.val) = (angular h : ℂ) * K (x, y) := by
    have hNorm : N (y * h.val) = N y := by
      change ((sIdeleQuotientNorm F S (y * h.val)).val : ℝ) =
        ((sIdeleQuotientNorm F S y).val : ℝ)
      rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
    dsimp only [K]
    simp only [hden, Complex.ofReal_one, mul_one, hNorm, hκIn x y h]
    ring
  let V := Submodule.span ℂ {u : W₀ | ∃ f : Bₛ,
    HasCompactSupport (sAdeleSchwartzFourier f).val ∧ gen(angular) f = u}
  let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
  let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
  let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK₂.toLp K)).val
  let C : W₀ →L[ℂ] W₀ := R.comp A
  let Reflected := C.comp (T.adjoint.comp (M.comp T))
  have hEqCore : EqOn Kop Reflected (closure (V : Set W₀)) := hEq
  have hAmb : Kop = Reflected :=
    ambientAnnulus_kernel_eq_of_inputCovariance (F := F) (S := S) τ hτ angular χ hχ hχsec
      Q L U hL hQL hQadj K hKm hK₂ hKIn M C V hSpan hEqCore
  refine ⟨χ, T, M, κ, hχ, hχsec, hGen, hM, hInter, hRep, ?_⟩
  exact ⟨hKm, ⟨hK₂, hAmb⟩⟩

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517.
For a homogeneous quotient test the weighted orbital kernel represents the
annular cutoff action on the whole order-zero quotient Hilbert space.
The same reflected coordinates realize its frequency multiplier.
Deviation: The comparison fixes the annulus and Sobolev order zero. -/
theorem exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eq_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : Jₛ) : ℝ := (m q).val
    ∃ (χ : PontryaginDual Jₛ) (T : W₀ →L[ℂ] FlatL2)
      (M : FlatL2 →L[ℂ] FlatL2) (κ : Jₛ → Jₛ → ℂ),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      sLocalFullReflectedGenAE τ angular χ T ∧
      (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x) ∧
      OrbitRep(fLift,ρ,b,κ) ∧
      let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
      Measurable K ∧ ∃ hK : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀),
        let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val
        let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
        let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
        Kop = (R.comp A).comp (T.adjoint.comp (M.comp T)) := by
  intro N
  have hAtBand :=
    @exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eq_atBand_orderZero F _ _ S
      τ hτ fLift Φ hLift angular hΦ b Λ ερ εb Cb ρ hρ hb hbdd hε hplateau hderiv 1 one_pos
  obtain ⟨χ, T, M, κ, hData⟩ := hAtBand
  obtain ⟨hχ, hχsec, hGen, hM, _, hRep, hKernel⟩ := hData
  exact ⟨χ, T, M, κ, hχ, hχsec, hGen, hM, hRep, hKernel⟩

end RiemannMasullo
