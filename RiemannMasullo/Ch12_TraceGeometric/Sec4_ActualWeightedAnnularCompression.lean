module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualAmbientAnnulusTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_AnnularWeightTransport
import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusTracePrerequisites
import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealizedOrbitRows
import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarTransport

/-! # The positive-order compression of the smooth annular orbit kernel -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8
set_option quotPrecheck false

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1
  instSIdeleLocallyCompactSec1 instSAdeleMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Bₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ν(" s ")" => intervalSobolevMeasure μJ ℓ 0 0 s
local notation "W(" s ")" => CompactIntervalSobolev μJ ℓ 0 0 s
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "gen(" r "," angular ")" =>
  Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := r) halfPos angular
local notation "modS(" u ")" =>
  (∏ w : InfinitePlace F, ‖(u : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
    ∏ v : S, ‖(u : Aₛ).2 v‖
local notation "cut(" b ")" => sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (modS(u)))
local notation "orbitOrder" =>
  (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ)

private theorem annularDensity_eq (s t : ℝ) :
    intervalSobolevDensity 0 0 s t = (1 + t ^ 2) ^ (s / 2) := by
  simp [intervalSobolevDensity]

private theorem annularDensity_continuous (s : ℝ) :
    Continuous (intervalSobolevDensity 0 0 s ∘ (ℓ : Jₛ → ℝ)) := by
  have hN : Continuous (fun q : Jₛ ↦ ((m q).val : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hlog : Continuous (ℓ : Jₛ → ℝ) :=
    hN.log fun q ↦ (NNReal.coe_pos.mpr (Units.zero_lt (m q))).ne'
  have hw : Continuous (intervalSobolevDensity 0 0 s) := by
    change Continuous (fun t : ℝ ↦ intervalSobolevDensity 0 0 s t)
    simp_rw [annularDensity_eq]
    exact Continuous.rpow_const (by fun_prop) fun _ ↦ Or.inl (by positivity)
  exact hw.comp hlog

private theorem weightedAnnulus_orderZeroMeasure_eq : (ν(0) : Measure Jₛ) = μJ := by
  have hzero (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by
    simp [annularDensity_eq]
  change (μJ).withDensity (fun q ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (ℓ q))) = μJ
  simp only [hzero, ENNReal.ofReal_one]
  exact withDensity_one

local instance instWeightedAnnularFinite (s : ℝ) : IsFiniteMeasureOnCompacts (ν(s) : Measure Jₛ) := by
  let : IsLocallyFiniteMeasure (ν(s) : Measure Jₛ) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (annularDensity_continuous (F := F) (S := S) s)
  infer_instance

local instance instWeightedAnnularInnerRegular (s : ℝ) : Measure.InnerRegular (ν(s) : Measure Jₛ) := by
  let : IsLocallyFiniteMeasure (ν(s) : Measure Jₛ) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (annularDensity_continuous (F := F) (S := S) s)
  infer_instance

local instance instSIdeleT2WeightedAnnularCompression : T2Space Iₛ :=
  (sIdeleGroup_description F S).2.1

/-- A smooth annular orbit kernel gives the actual descended action on
weighted theta generators whenever the additive cutoff is realized. -/
theorem weightedAnnularKernel_action_on_generators
    {s : ℝ} (hs : 0 ≤ s) (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁) (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ) (hb : ContDiff ℝ orbitOrder b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb)
    (κ : Jₛ → Jₛ → ℂ)
    (hRep : ∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
      ∑' ξ : Hₛ, sLocalTraceCutoffKernel fLift (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ))
        (fun v ↦ b (modS(v))) x (ξ.val * y).val) :
    let N (q : Jₛ) : ℝ := (m q).val
    let K (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
      ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ p.2) : ℂ))
    ∀ hKₛ : MemLp K 2 ((ν(s) : Measure Jₛ).prod ν(s)),
    let As := (integralKernelOperator ν(s) (hKₛ.toLp K)).val
    let Rs : W(s) →L[ℂ] W(s) := lpCutoffMultiplier ν(s) ρ hρ.measurable hρ.abs_le_one
    let A_s : W(s) →L[ℂ] W(s) := hardySobolevTestAction μJ m 0 0 s le_rfl hs Φ
    ∀ (f g : Bₛ), cut(b) f = (fun z : Aₛ ↦ g (Multiplicative.ofAdd z)) →
      As (gen(s,angular) f) = Rs (A_s (gen(s,angular) g)) := by
  intro N K hKₛ As Rs A_s f g hCut
  let φ : C(Jₛ, ℂ) := ⟨Φ.val,
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 Φ.property.1)⟩
  obtain ⟨κRows, hRowsRep, _, hRows⟩ :=
    @exists_sLocalTrace_fixedAnnulus_realizedCutoff_kernel_rows F _ _ S
      fLift φ Φ.property.2 hLift b Λ ερ εb Cb s ρ hρ hs hb hε hplateau hderiv
  have hκRows (q y : Jₛ) : κ q y = κRows q y := by
    have h₁ := hRep q.out y.out
    have h₂ := hRowsRep q.out y.out
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h₁ h₂
    exact h₁.trans h₂.symm
  let u (v : Bₛ) (q : Jₛ) := (Real.sqrt (N q) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap F S angular v q
  have hGen (v : Bₛ) : ((gen(s,angular) v : W(s)) : Jₛ → ℂ) =ᵐ[μJ] u v := by
    filter_upwards [Isolated.sLocalFullPWThetaSobolevMap_apply
      (F := F) (S := S) (s := s) (a := 1 / 2) halfPos angular v] with q hq
    change gen(s,angular) v q = ((N q ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap F S angular v q at hq
    simpa only [u, Real.sqrt_eq_rpow] using hq
  have hνsμ : (ν(s) : Measure Jₛ) ≪ μJ := withDensity_absolutelyContinuous _ _
  have hRowEq (q : Jₛ) :
      (∫ y, K (q, y) * u f y ∂ν(s)) = (ρ q : ℂ) * lcaConvolution μJ Φ.val (u g) q := by
    simpa only [K, N, u, φ, ContinuousMap.coe_mk, hκRows] using (hRows f g hCut angular q).2.1
  have hRaw : (As (gen(s,angular) f) : Jₛ → ℂ) =ᵐ[ν(s)] fun q ↦
      (ρ q : ℂ) * lcaConvolution μJ Φ.val (u g) q := by
    have hApply := integralKernelOperator_apply_representatives (X := Jₛ) ν(s) hKₛ
      (gen(s,angular) f) (hνsμ.ae_eq (hGen f))
    exact hApply.mono fun q hq ↦ hq.2.trans (hRowEq q)
  have hConv (q : Jₛ) : lcaConvolution μJ Φ.val (gen(s,angular) g) q =
      lcaConvolution μJ Φ.val (u g) q := by
    unfold lcaConvolution
    apply integral_congr_ae
    have hTranslate := (quasiMeasurePreserving_div_left μJ q).ae_eq_comp (hGen g)
    filter_upwards [hTranslate] with v hv
    change gen(s,angular) g (q / v) = u g (q / v) at hv
    have hqv : q / v = v⁻¹ * q := (div_eq_mul_inv q v).trans (mul_comm _ _)
    rw [hqv] at hv
    exact congrArg (fun z : ℂ ↦ Φ.val v * z) hv
  apply Lp.ext
  filter_upwards [hRaw, lpCutoffMultiplier_apply ν(s) ρ hρ.measurable hρ.abs_le_one
      (A_s (gen(s,angular) g)),
    hνsμ.ae_eq (hardySobolevTestAction_apply μJ m 0 0 s le_rfl hs Φ (gen(s,angular) g))]
    with q hk hmask hact
  change As (gen(s,angular) f) q = Rs (A_s (gen(s,angular) g)) q
  change A_s (gen(s,angular) g) q = lcaConvolution μJ Φ.val (gen(s,angular) g) q at hact
  rw [hk, hmask, hact, hConv q]

private theorem weightedAnnularOrderZeroKernel_trace
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ) (hInner : Λ⁻¹ + ερ < Λ - ερ)
    (hρcont : ∀ᵐ x ∂μJ, ContinuousAt ρ x)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : Jₛ) : ℝ := (m q).val
    ∃ κ : Jₛ → Jₛ → ℂ,
      (∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, sLocalTraceCutoffKernel fLift (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ))
          (fun v ↦ b (modS(v))) x (ξ.val * y).val) ∧
      let K (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
      ∃ (hK : MemLp K 2 ((ν(0) : Measure Jₛ).prod ν(0)))
        (hA : IsNuclearOperator (integralKernelOperator ν(0) (hK.toLp K)).val),
        Integrable (fun q ↦ K (q, q)) ν(0) ∧
        hilbertTrace ⟨(integralKernelOperator ν(0) (hK.toLp K)).val, hA⟩ =
          ∫ q, K (q, q) ∂ν(0) := by
  intro N
  obtain ⟨χ, T, M, κ, hData⟩ :=
    @exists_sLocalTrace_fixedAnnulus_reflectedProductCutoff_eq_orderZero F _ _ S
      τ hτ fLift Φ hLift angular hΦ b Λ ερ εb Cb ρ hρ hb hbdd hε hplateau hderiv
  obtain ⟨_, _, _, _, hRep, _, hK0, hOperator⟩ := hData
  let K (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
    ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 0 (ℓ p.2) : ℂ))
  have hK₀ : MemLp K 2 ((ν(0) : Measure Jₛ).prod ν(0)) := hK0
  let A0 : W(0) →L[ℂ] W(0) := (integralKernelOperator ν(0) (hK₀.toLp K)).val
  let D := T.adjoint.comp (M.comp T)
  let A : W(0) →L[ℂ] W(0) := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
  let R : W(0) →L[ℂ] W(0) := lpCutoffMultiplier ν(0) ρ hρ.measurable hρ.abs_le_one
  have hC : A0 = (R.comp A).comp D := hOperator
  have hBand : 0 < Λ⁻¹ + ερ ∧ Λ⁻¹ + ερ < Λ - ερ :=
    ⟨add_pos (inv_pos.mpr hρ.radius_pos) hρ.width_pos, hInner⟩
  have hA0 : IsNuclearOperator A0 := hC.symm ▸
    isNuclearOperator_sLocalTrace_fixedAnnulus_testAction_comp
      (F := F) (S := S) (s := 0) le_rfl Φ hρ hBand D
  have hTwo : 2 ≤ orbitOrder := by omega
  obtain ⟨κ₀, hκ₀, hMask⟩ :=
    exists_sLocalTrace_maskedRadialOrbitSeries_factor fLift b (fun q ↦ (ρ q : ℂ)) κ
      ((contDiff_infty.mp hb) 2) hε hplateau (fun j hj ↦ hderiv j (hj.trans hTwo)) hRep
  have hCont : ∀ᵐ q ∂ν(0), ContinuousAt K (q,q) := by
    simpa only [K, hMask] using
      ae_continuousAt_sLocalTrace_maskedHalfDensity (F := F) (S := S) κ₀ hκ₀ hρcont 0
  obtain ⟨hInt, hDiag⟩ := hilbertTrace_integralKernelOperator_of_ae_continuous
    (X := Jₛ) ν(0) hK₀ hA0 hCont
  exact ⟨κ, hRep, hK₀, hA0, hInt, hDiag⟩

private theorem weightedAnnularKernel_apply_density
    {s : ℝ} (hs : 0 ≤ s) (P : W(s) →L[ℂ] W(s)) (hP : P * P = P)
    {Z : Set Jₛ} (hZ : IsCompact Z) (κ : Jₛ → Jₛ → ℂ) :
    let N (q : Jₛ) : ℝ := (m q).val
    let K (r : ℝ) (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
      ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 r (ℓ p.2) : ℂ))
    ∀ (hK₀ : MemLp (K 0) 2 ((ν(0) : Measure Jₛ).prod ν(0)))
      (hKₛ : MemLp (K s) 2 ((ν(s) : Measure Jₛ).prod ν(s))),
      (∀ q ∉ Z, ∀ y, K 0 (q, y) = 0) →
      let A0 : W(0) →L[ℂ] W(0) := (integralKernelOperator ν(0) (hK₀.toLp (K 0))).val
      let As : W(s) →L[ℂ] W(s) := (integralKernelOperator ν(s) (hKₛ.toLp (K s))).val
      ∀ hA0 : IsNuclearOperator A0,
        ∃ (J : W(s) →L[ℂ] W(0)) (L : W(0) →L[ℂ] W(s)) (hAs : IsNuclearOperator As),
          (∀ f, (J f : Jₛ → ℂ) =ᵐ[ν(0)] (f : Jₛ → ℂ)) ∧
          (∀ f, (L f : Jₛ → ℂ) =ᵐ[ν(s)] Z.indicator (f : Jₛ → ℂ)) ∧
          let E := (J.comp P - J).comp L
          let A : nuclearEndomorphisms (W(0)) := ⟨A0, hA0⟩
          hilbertTrace (Isolated.nuclearCompress P ⟨As, hAs⟩) =
            hilbertTrace A + hilbertTrace ⟨E * A.val, mul_mem_nuclearEndomorphisms_left E A⟩ := by
  intro N K hK₀ hKₛ hZK A0 As hA0
  let w (q : Jₛ) : ℝ≥0 := (intervalSobolevDensity 0 0 s (ℓ q)).toNNReal
  have hw₁ (q : Jₛ) : 1 ≤ w q := by
    apply NNReal.coe_le_coe.mp
    simp only [w, NNReal.coe_one, annularDensity_eq]
    rw [Real.coe_toNNReal _ (by positivity)]
    exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)
  have hw : Continuous w := continuous_real_toNNReal.comp
    (annularDensity_continuous (F := F) (S := S) s)
  have hwReal (q : Jₛ) : (w q : ℝ) = intervalSobolevDensity 0 0 s (ℓ q) := by
    have hp : 0 ≤ intervalSobolevDensity 0 0 s (ℓ q) := by rw [annularDensity_eq]; positivity
    exact Real.coe_toNNReal _ hp
  have hν : (ν(s) : Measure Jₛ) = (ν(0)).withDensity (fun q ↦ (w q : ℝ≥0∞)) := by
    rw [weightedAnnulus_orderZeroMeasure_eq]
    rfl
  have hKer (p : Jₛ × Jₛ) : K 0 p / ((w p.2 : ℝ) : ℂ) = K s p := by
    simp only [K, annularDensity_eq 0, zero_div, Real.rpow_zero, Complex.ofReal_one, mul_one, hwReal]
    rw [div_div]
  have hKw : MemLp (fun p ↦ K 0 p / ((w p.2 : ℝ) : ℂ)) 2 ((ν(s) : Measure Jₛ).prod ν(s)) := by
    simpa only [hKer] using hKₛ
  have hWeight := hilbertTrace_weightedAnnularKernel_compress_eq
    ν(0) ν(s) w hw hw₁ hν hZ (K 0) hK₀ hZK hA0 hKw
    P hP (ContinuousLinearMap.id ℂ (W(0))) (by
      change A0.comp (ContinuousLinearMap.id ℂ (W(0))) = A0
      exact ContinuousLinearMap.comp_id _)
  simp only [hKer, ContinuousLinearMap.id_comp] at hWeight
  obtain ⟨J, L, hAs, hJ, hL, hTrace⟩ := hWeight
  exact ⟨J, L, hAs, hJ, hL, hTrace⟩

/-- A nuclear operator on quotient `L²` has a factorized diagonal with
absolutely integrable trace density. Applying this to the compressed operator
uses its own Hilbert–Schmidt factors, which include both projections. -/
theorem exists_nuclearL2Endomorphism_integrableFactorDiagonal
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]
    (T : nuclearEndomorphisms (Lp ℂ 2 μ)) :
    ∃ a b : Lp ℂ 2 (μ.prod μ),
      T.val = (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val ∧
      let d (x : X) := ∫ y, a (x, y) * b (y, x) ∂μ
      Integrable d μ ∧ hilbertTrace T = ∫ x, d x ∂μ := by
  obtain ⟨A, B, hcomp⟩ := exists_hilbertSchmidt_factorization T.val T.property
  obtain ⟨a, rfl⟩ := (bijective_integralKernelOperator μ).surjective A
  obtain ⟨b, rfl⟩ := (bijective_integralKernelOperator μ).surjective B
  have hb := (Lp.memLp b).comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  have hmass : Integrable (fun p : X × X ↦ a p * b p.swap) (μ.prod μ) :=
    (Lp.memLp a).integrable_mul hb
  refine ⟨a, b, hcomp, hmass.integral_prod_left, ?_⟩
  have hN : IsNuclearOperator
      ((integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val) := hcomp ▸ T.property
  have hT : T = ⟨_, hN⟩ := Subtype.ext hcomp
  rw [hT, hilbertTrace_integralKernelOperator_comp]
  exact integral_prod _ hmass


/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 515–518.
At a fixed annulus the positive-order compression of the smooth orbit kernel
has its raw diagonal trace and the discrepancy between the actual weighted
projection and the uncompressed ambient action. The actual cutoff row identity
is `weightedAnnularKernel_action_on_generators`. Applying
`exists_nuclearL2Endomorphism_integrableFactorDiagonal` to the same compression
gives its integrable factor-kernel diagonal.
Deviation: The projection discrepancy remains in the trace and is not
estimated as either cutoff varies. -/
theorem exists_sLocalTrace_fixedAnnulus_weightedCompression_eq_add_projectionDefect
    {s : ℝ} (hs : 0 ≤ s)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (fLift : BruhatCompactSupport Iₛ) (Φ : BruhatCompactSupport Jₛ)
    (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ fLift.val (ξ.val * x))
      (Φ.val (QuotientGroup.mk x)))
    (angular : PontryaginDual J₁)
    (hΦ : ∀ (q : Jₛ) (h : J₁), Φ.val (q * h.val) = (angular h : ℂ)⁻¹ * Φ.val q)
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ) (hInner : Λ⁻¹ + ερ < Λ - ερ)
    (hρcont : ∀ᵐ x ∂μJ, ContinuousAt ρ x)
    (hb : ContDiff ℝ (∞ : ℕ∞ω) b) (hbdd : ∀ t, 0 ≤ t → ‖b t‖ ≤ 1)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ orbitOrder, ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb)
    (P : W(s) →L[ℂ] W(s)) (hP : P * P = P) :
    let N (q : Jₛ) : ℝ := (m q).val
    let Z : Set Jₛ := {q | N q ∈ Icc Λ⁻¹ Λ}
    ∃ κ : Jₛ → Jₛ → ℂ,
      (∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, sLocalTraceCutoffKernel fLift (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ))
          (fun v ↦ b (modS(v))) x (ξ.val * y).val) ∧
      let K (r : ℝ) (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 r (ℓ p.2) : ℂ))
      ∃ (hK0 : MemLp (K 0) 2 ((ν(0) : Measure Jₛ).prod ν(0)))
        (hKs : MemLp (K s) 2 ((ν(s) : Measure Jₛ).prod ν(s))),
        let A0 : W(0) →L[ℂ] W(0) := (integralKernelOperator ν(0) (hK0.toLp (K 0))).val
        let As : W(s) →L[ℂ] W(s) := (integralKernelOperator ν(s) (hKs.toLp (K s))).val
        ∃ (J : W(s) →L[ℂ] W(0)) (L : W(0) →L[ℂ] W(s))
          (hA0 : IsNuclearOperator A0) (hAs : IsNuclearOperator As),
          (∀ f, (J f : Jₛ → ℂ) =ᵐ[ν(0)] (f : Jₛ → ℂ)) ∧
          (∀ f, (L f : Jₛ → ℂ) =ᵐ[ν(s)] Z.indicator (f : Jₛ → ℂ)) ∧
          let E := (J.comp P - J).comp L
          let A : nuclearEndomorphisms (W(0)) := ⟨A0, hA0⟩
          Integrable (fun q ↦ K 0 (q, q)) ν(0) ∧
          hilbertTrace (Isolated.nuclearCompress P ⟨As, hAs⟩) =
            (∫ q, K 0 (q, q) ∂ν(0)) +
              hilbertTrace ⟨E * A.val, mul_mem_nuclearEndomorphisms_left E A⟩ := by
  intro N Z
  obtain ⟨κ, hRep, hK0, hA0, hInt, hDiag⟩ := weightedAnnularOrderZeroKernel_trace
    τ hτ fLift Φ hLift angular hΦ b hρ hInner hρcont hb hbdd hε hplateau hderiv
  let K (r : ℝ) (p : Jₛ × Jₛ) : ℂ := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
    ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 r (ℓ p.2) : ℂ))
  have hK₀ : MemLp (K 0) 2 ((ν(0) : Measure Jₛ).prod ν(0)) := hK0
  have hbFin : ContDiff ℝ orbitOrder b := (contDiff_infty.mp hb) orbitOrder
  obtain ⟨hZ, κs, _, _, _, hκsZ, hκsRep, _, _, _, hKs⟩ :=
    exists_sLocalTrace_halfDensityOrbitKernel_fixed_annulus_data fLift b hρ hs hbFin hε hplateau hderiv
  have hκ (q y : Jₛ) : κ q y = κs q y := by
    have h₁ := hRep q.out y.out
    have h₂ := hκsRep q.out y.out
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h₁ h₂
    exact h₁.trans h₂.symm
  have hZK (q : Jₛ) (hq : q ∉ Z) (y : Jₛ) : K 0 (q, y) = 0 := by
    simp only [K, hκ, hκsZ q hq y, mul_zero, zero_div]
  have hLog (q : Jₛ) : ℓ q = Real.log (N q) := rfl
  have hKₛ : MemLp (K s) 2 ((ν(s) : Measure Jₛ).prod ν(s)) := by
    simpa only [K, hLog, N, hκ] using hKs
  obtain ⟨J, L, hAs, hJ, hL, hTrace⟩ := weightedAnnularKernel_apply_density hs P hP hZ
    κ hK₀ hKₛ hZK hA0
  refine ⟨κ, hRep, hK₀, hKₛ, J, L, hA0, hAs, hJ, hL, hInt, ?_⟩
  rw [hTrace, hDiag]

end RiemannMasullo
