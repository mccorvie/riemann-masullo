module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealizedOrbitRows
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedProductCutoff
import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarTransport
import RiemannMasullo.AppC_LCTVS.Sec3b

/-! # The concrete annular orbit operator on the closed angular space -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1
  instSIdeleLocallyCompactSec1 instSAdeleMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S

local instance instSIdeleT2ReflectedAnnulusOrbitComparison : T2Space Iₛ :=
  (sIdeleGroup_description F S).2.1

local notation "Hₛ" => sProjectedDiagonal F S
set_option quotPrecheck false in
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "modulus" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
set_option quotPrecheck false in
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
set_option quotPrecheck false in
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
set_option quotPrecheck false in
local notation "cut(" b ")" => sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (modS(u)))
set_option quotPrecheck false in
local notation "gen(" angular ")" => Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S)
  (s := 0) (a := 1 / 2) halfPos angular

private theorem orbitOrderZeroMeasure_eq : (ν₀ : Measure Jₛ) = μJ := by
  have hzero (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
  change (μJ).withDensity (fun q ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (ℓ q))) = μJ
  simp only [hzero, ENNReal.ofReal_one]
  change (μJ).withDensity (1 : Jₛ → ℝ≥0∞) = μJ
  exact withDensity_one

local instance orbitOrderZeroFiniteOnCompacts : IsFiniteMeasureOnCompacts (ν₀ : Measure Jₛ) := by
  rw [orbitOrderZeroMeasure_eq]
  infer_instance

local instance orbitOrderZeroInnerRegular : Measure.InnerRegular (ν₀ : Measure Jₛ) := by
  rw [orbitOrderZeroMeasure_eq]
  infer_instance

private theorem integralKernelOperator_apply_representatives
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν]
    {K : X × X → ℂ} (hK : MemLp K 2 (ν.prod ν)) (U : Lp ℂ 2 ν)
    {u : X → ℂ} (hu : (U : X → ℂ) =ᵐ[ν] u) :
    let T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := (integralKernelOperator ν (hK.toLp K)).val
    ∀ᵐ x ∂ν, Integrable (fun y ↦ K (x, y) * u y) ν ∧
      T U x = ∫ y, K (x, y) * u y ∂ν := by
  intro T
  filter_upwards [integralKernelOperator_apply ν (hK.toLp K) U,
    Measure.ae_ae_of_ae_prod hK.coeFn_toLp] with x hx hkx
  have hrow : (fun y ↦ (hK.toLp K) (x, y) * U y) =ᵐ[ν] fun y ↦ K (x, y) * u y := by
    filter_upwards [hkx, hu] with y hky huy
    rw [hky, huy]
  exact ⟨hx.1.congr hrow, hx.2.trans (integral_congr_ae hrow)⟩

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517. The periodized orbit
kernel acts before compression by frequency cutoff, quotient convolution,
and spatial multiplication.
Deviation: This comparison fixes a spatial annulus and Sobolev order zero.
It assumes a cutoff realization on one angular type's compact Fourier
generators and proves the identity on their closed span. -/
theorem exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eqOn_orderZero
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * g))
      (Φ.val (QuotientGroup.mk g)))
    (angular : PontryaginDual J₁) (b : ℝ → ℂ)
    {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ} (hρ : IsModulatedCutoff modulus Λ ερ ρ)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb)
    (T : W₀ →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2)
    (hRealize : ∀ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val →
      ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
        cut(b) f = (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
        gen(angular) g = T.adjoint (M (T (gen(angular) f)))) :
    let N (q : Jₛ) : ℝ := (modulus q).val
    ∃ κ : Jₛ → Jₛ → ℂ,
      (∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, sLocalTraceCutoffKernel (F := F) (S := S) fLift
          (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) (fun v ↦ b (modS(v))) x (ξ.val * y).val) ∧
      let K (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
      ∃ hK : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀),
        let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK.toLp K)).val
        let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ modulus 0 0 0 le_rfl le_rfl Φ
        let R : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
        let D : W₀ →L[ℂ] W₀ := T.adjoint.comp (M.comp T)
        EqOn Kop ((R.comp A).comp D)
          (closure (Submodule.span ℂ {u : W₀ | ∃ f : Bₛ,
            HasCompactSupport (sAdeleSchwartzFourier f).val ∧ gen(angular) f = u} : Set W₀)) := by
  intro N
  let φ : C(Jₛ, ℂ) := ⟨Φ.val,
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 Φ.property.1)⟩
  have hData :=
    @exists_sLocalTrace_fixedAnnulus_realizedCutoff_kernel_rows F _ _ S fLift φ Φ.property.2 hLift b
      Λ ερ εb Cb 0 ρ hρ le_rfl hb hε hplateau hderiv
  obtain ⟨κ, hκ⟩ := hData
  let K (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
    ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
  have hK' : MemLp K 2 ((ν₀ : Measure Jₛ).prod ν₀) := hκ.2.1
  let Kop : W₀ →L[ℂ] W₀ := (integralKernelOperator (X := Jₛ) ν₀ (hK'.toLp K)).val
  let Act : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ modulus 0 0 0 le_rfl le_rfl Φ
  let Sρ : W₀ →L[ℂ] W₀ := lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one
  let C : W₀ →L[ℂ] W₀ := Sρ.comp Act
  refine ⟨κ, hκ.1, hK', ?_⟩
  change EqOn Kop (C.comp (T.adjoint.comp (M.comp T))) _
  refine eqOn_orbit_reflectedProductCutoff_compactGenClosure_orderZero angular b T M Kop C
    hRealize ?_
  intro f g _ _ hcut
  let u (v : Bₛ) (q : Jₛ) := (Real.sqrt (N q) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap F S angular v q
  have hGen (v : Bₛ) : ((gen(angular) v : W₀) : Jₛ → ℂ) =ᵐ[μJ] u v := by
    filter_upwards [Isolated.sLocalFullPWThetaSobolevMap_apply
      (F := F) (S := S) (s := 0) (a := 1 / 2) halfPos angular v] with q hq
    change gen(angular) v q = ((N q ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap F S angular v q at hq
    simpa only [u, Real.sqrt_eq_rpow] using hq
  have hνμ : (ν₀ : Measure Jₛ) ≪ μJ := withDensity_absolutelyContinuous _ _
  have hRowEq (q : Jₛ) :
      (∫ y, K (q, y) * u f y ∂ν₀) = (ρ q : ℂ) * lcaConvolution μJ Φ.val (u g) q :=
    (hκ.2.2 f g hcut angular q).2.1
  have hRaw : (Kop (gen(angular) f) : Jₛ → ℂ) =ᵐ[ν₀] fun q ↦
      (ρ q : ℂ) * lcaConvolution μJ Φ.val (u g) q := by
    have hApply := integralKernelOperator_apply_representatives (X := Jₛ) ν₀ hK'
      (gen(angular) f) (hνμ.ae_eq (hGen f))
    exact hApply.mono fun q hq ↦ hq.2.trans (hRowEq q)
  have hConv (q : Jₛ) : lcaConvolution μJ Φ.val (gen(angular) g) q =
      lcaConvolution μJ Φ.val (u g) q := by
    unfold lcaConvolution
    apply integral_congr_ae
    have hTranslate := (quasiMeasurePreserving_div_left μJ q).ae_eq_comp (hGen g)
    filter_upwards [hTranslate] with v hv
    change gen(angular) g (q / v) = u g (q / v) at hv
    have hqv : q / v = v⁻¹ * q := (div_eq_mul_inv q v).trans (mul_comm _ _)
    rw [hqv] at hv
    exact congrArg (fun z : ℂ ↦ Φ.val v * z) hv
  apply Lp.ext
  filter_upwards [hRaw, lpCutoffMultiplier_apply ν₀ ρ hρ.measurable hρ.abs_le_one (Act (gen(angular) g)),
    hνμ.ae_eq (hardySobolevTestAction_apply μJ modulus 0 0 0 le_rfl le_rfl Φ (gen(angular) g))]
    with q hk hmask hact
  change Kop (gen(angular) f) q = Sρ (Act (gen(angular) g)) q
  change Act (gen(angular) g) q = lcaConvolution μJ Φ.val (gen(angular) g) q at hact
  rw [hk, hmask, hact, hConv q]

end RiemannMasullo
