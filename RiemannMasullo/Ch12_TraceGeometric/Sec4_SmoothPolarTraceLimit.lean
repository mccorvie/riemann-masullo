module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualPolarTraceLimit
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SameWitnessReflectedPolarLine
import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothPolarTraceEstimate
import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothReflectedPolarShell

/-! # The order-zero polar trace limit with a smooth frequency cutoff -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal InnerProductSpace NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8
set_option quotPrecheck false

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "I" => (SAdeleRing F S)ˣ
local notation "J" => SIdeleQuotient F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "full(" B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos
    (1 : PontryaginDual J₁) B
local notation "polar(" B ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos
    (1 : PontryaginDual J₁) B
local notation "expLog" => fun x : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd x)

/-- The correction for passing from the full to the polar-free band in the trivial
angular character. The input is the same nuclear operator in both compressions. -/
def sLocalOrderZeroPolarTraceDifference (B : ℝ) (C : nuclearEndomorphisms W₀) : ℂ :=
  let Vfull : Submodule ℂ W₀ := full(B)
  let Vpolar : Submodule ℂ W₀ := polar(B)
  letI : CompleteSpace Vfull :=
    (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  letI : CompleteSpace Vpolar :=
    (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  hilbertTrace (Isolated.nuclearCompress Vfull.starProjection C) -
    hilbertTrace (Isolated.nuclearCompress Vpolar.starProjection C)

/-- Paper: Theorem 12.4.1.1, pp. 515–519. A smooth frequency transition with
vanishing relative width preserves the order-zero polar trace correction.
Deviation: This compares the full and polar-free compressions in the trivial
character and assumes a centered spatial plateau along the given filter. -/
theorem exists_sLocalSmoothPolarTraceDifference_tendsto_orderZero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (Φ : BruhatCompactSupport J) (B Tmax δ : ι → ℝ) (hB : ∀ i, 0 < B i)
    (ρ : ι → ℝ → ℝ) (hρm : ∀ i, Measurable (ρ i)) (hρ : ∀ i x, |ρ i x| ≤ 1)
    (hρT : ∀ i x, Tmax i < x → ρ i x = 0)
    (hOne : ∀ z, ∀ᶠ i in l, ρ i (z + -Real.log (B i)) = 1)
    (hWidth : Tendsto (fun i ↦ Real.sqrt (δ i / B i)) l (𝓝 0))
    (C : ι → nuclearEndomorphisms W₀) :
    let hρLog (i : ι) : Measurable (ρ i ∘ ℓ) := (hρm i).comp (Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)).measurable)
    let A : W₀ →L[ℂ] W₀ := hardySobolevTestAction μJ m 0 0 0 le_rfl le_rfl Φ
    let R (i : ι) : W₀ →L[ℂ] W₀ :=
      lpCutoffMultiplier ν₀ (ρ i ∘ ℓ) (hρLog i) (fun g ↦ hρ i (ℓ g))
    (∀ᶠ i in l, IsNuclearOperator ((R i).comp A) ∧ 0 ≤ δ i ∧ δ i < B i ∧
      ∃ (T : W₀ →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2) (b : ℝ → ℝ),
        (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ (b (Real.exp (-x)) : ℂ) * r x) ∧
        (∀ r, 0 ≤ r → b r ∈ Icc (0 : ℝ) 1) ∧
        (∀ r, 0 ≤ r → r ≤ B i - δ i → b r = 1) ∧
        sLocalReflectedPolarLineData (F := F) (S := S) 1 (B i) T ∧
        (C i).val = ((R i).comp A).comp (T.adjoint.comp (M.comp T))) →
    ∃ k : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, k x = ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x)))
        ∂(sLocalNormOneQuotientMeasure F S)) ∧
      Tendsto (fun i ↦ sLocalOrderZeroPolarTraceDifference (F := F) (S := S) (B i) (C i)) l
        (𝓝 (∫ t, k t * (Real.exp (-|t| / 2) : ℂ))) := by
  intro hρLog A R hC
  have hSharp :=
    @exists_sLocalFullPW_upperCutoff_trace_sub_polar_tendsto_orderZero F _ _ S ι l _
      τ hτ Φ B Tmax hB ρ hρm hρ hρT hOne
  obtain ⟨k, hk, Full, Polar, hComp, hLimit⟩ := hSharp
  refine ⟨k, hk, ?_⟩
  let smooth (i : ι) := sLocalOrderZeroPolarTraceDifference (F := F) (S := S) (B i) (C i)
  let sharp (i : ι) := hilbertTrace (Full i) - hilbertTrace (Polar i)
  have hPerturb : ∀ᶠ i in l, ‖smooth i - sharp i‖ ≤ ‖A‖ * Real.sqrt (δ i / B i) := by
    filter_upwards [hC] with i hi
    obtain ⟨hN, hδ, hδB, T, M, b, hM, hb, hPlateau, hLineData, hOp⟩ := hi
    let Vfull : Submodule ℂ W₀ := full(B i)
    let Vpolar : Submodule ℂ W₀ := polar(B i)
    let : CompleteSpace Vfull :=
      (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let : CompleteSpace Vpolar :=
      (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let D : nuclearEndomorphisms W₀ := ⟨(R i).comp A, hN⟩
    have hSub : Vpolar ≤ Vfull :=
      (Isolated.sLocalPWSobolev_polarComplement (F := F) (S := S) (s := 0)
        le_rfl halfPos (1 : PontryaginDual J₁) (B i)).1
    unfold sLocalReflectedPolarLineData at hLineData
    obtain ⟨u, huT, hu, hSpan, hAdj⟩ := hLineData.2 rfl
    have hFull : Isolated.nuclearCompress Vfull.starProjection D = Full i := by
      apply Subtype.ext
      exact (hComp i).1.symm
    have hPolar : Isolated.nuclearCompress Vpolar.starProjection D = Polar i := by
      apply Subtype.ext
      exact (hComp i).2.symm
    have hSharpEq : sharp i = ⟪u.val, (R i).comp A u.val⟫_ℂ := by
      change hilbertTrace (Full i) - hilbertTrace (Polar i) = _
      rw [← hFull, ← hPolar]
      exact Isolated.hilbertTrace_nuclearCompress_sub_eq_inner_of_complement_line
        D Vpolar Vfull hSub u.val hu hSpan
    let e := normalizedHalflineExponentialL2 (-Real.log (B i))
    have hTrace := norm_hilbertTrace_smoothPolarDifference_sub_inner_le
      ((R i).comp A) T M (C i) hOp Vpolar Vfull hSub u.val e hu hSpan huT hAdj hLineData.1
    have hShell : ‖M e - e‖ ≤ Real.sqrt (δ i / B i) :=
      Real.le_sqrt_of_sq_le
        (normalizedHalflineExponentialL2_sub_frequencyMultiplier_norm_sq_le hδ hδB M b hM hb hPlateau)
    have hR : ‖R i‖ ≤ 1 :=
      (exists_lpCutoffMultiplier ν₀ (ρ i ∘ ℓ) (hρLog i) (fun g ↦ hρ i (ℓ g))).choose_spec.1
    have hNorm : ‖(R i).comp A‖ ≤ ‖A‖ :=
      ((R i).opNorm_comp_le A).trans (mul_le_of_le_one_left (norm_nonneg A) hR)
    rw [hSharpEq]
    exact hTrace.trans (mul_le_mul hNorm hShell (norm_nonneg _) (norm_nonneg _))
  have hZero : Tendsto (fun i ↦ ‖smooth i - sharp i‖) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hPerturb
      (by simpa only [mul_zero] using hWidth.const_mul ‖A‖)
  have hDiff : Tendsto (fun i ↦ smooth i - sharp i) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr hZero
  have hSum := hDiff.add (show Tendsto sharp l _ from hLimit)
  simpa only [sub_add_cancel, zero_add] using hSum

end RiemannMasullo
