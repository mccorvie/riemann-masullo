module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualAmbientAnnulusTrace
import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothPolarTraceEstimate
import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothReflectedPolarShell

/-! # The frequency smoothing error for the actual polar trace -/

public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal InnerProductSpace NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1
  instSIdeleLocallyCompactSec1 instSAdeleMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "fullBand(" angular "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B
local notation "polarBand(" angular "," B ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos angular B

/-- The full-minus-polar trace of the actual annular cutoff differs from the
unsmoothed pairing on the unit polar vector by at most the operator norm of
the test action times the square root of the relative frequency width. -/
theorem exists_sLocalTrace_smoothPolarDifference_sub_inner_le_orderZero
    (angular : PontryaginDual J₁) (hAngular : angular = 1)
    {B δ : ℝ} (hδ : 0 ≤ δ) (hδB : δ < B) (b : ℝ → ℝ)
    (hb : ∀ r, 0 ≤ r → b r ∈ Icc (0 : ℝ) 1)
    (hOne : ∀ r, 0 ≤ r → r ≤ B - δ → b r = 1)
    (A : W₀ →L[ℂ] W₀) {Λ ερ : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff m Λ ερ ρ)
    (T : W₀ →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2)
    (hM : ∀ v, (M v : ℝ → ℂ) =ᵐ[volume] fun x ↦ (b (Real.exp (-x)) : ℂ) * v x)
    (hPolar : sLocalReflectedPolarLineData (F := F) (S := S) angular B T)
    (C : nuclearEndomorphisms W₀)
    (hC : C.val = ((lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one).comp A).comp (T.adjoint.comp (M.comp T))) :
    let Vfull : Submodule ℂ W₀ := fullBand(angular,B)
    let Vpolar : Submodule ℂ W₀ := polarBand(angular,B)
    letI : CompleteSpace Vfull :=
      (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    letI : CompleteSpace Vpolar :=
      (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let R : W₀ →L[ℂ] W₀ := (lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one)
    ∃ u : Vfull, ‖u.val‖ = 1 ∧ Vfull ⊓ Vpolarᗮ = ℂ ∙ u.val ∧
      ‖(hilbertTrace (Isolated.nuclearCompress Vfull.starProjection C) -
        hilbertTrace (Isolated.nuclearCompress Vpolar.starProjection C)) -
        ⟪u.val, (R.comp A) u.val⟫_ℂ‖ ≤ ‖A‖ * Real.sqrt (δ / B) := by
  intro Vfull Vpolar R
  let : CompleteSpace Vfull :=
    (show IsClosed (Vfull : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let : CompleteSpace Vpolar :=
    (show IsClosed (Vpolar : Set W₀) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  unfold sLocalReflectedPolarLineData at hPolar
  obtain ⟨hT, hPolarLine⟩ := hPolar
  obtain ⟨u, hTu, hu, hLine, hAdj⟩ := hPolarLine hAngular
  let e := normalizedHalflineExponentialL2 (-Real.log B)
  have hVB : Vpolar ≤ Vfull :=
    (Isolated.sLocalPWSobolev_polarComplement (F := F) (S := S) (s := 0)
      le_rfl halfPos angular B).1
  have hC' : C.val = (R.comp A).comp (T.adjoint.comp (M.comp T)) := hC
  have hEstimate :=
    @norm_hilbertTrace_smoothPolarDifference_sub_inner_le W₀ FlatL2 _ _ _ _ _ _
      (R.comp A) T M C hC' Vpolar Vfull _ _ hVB u.val e hu hLine hTu hAdj hT
  have hRS : ‖R‖ ≤ 1 :=
    (exists_lpCutoffMultiplier ν₀ ρ hρ.measurable hρ.abs_le_one).choose_spec.1
  have hRA : ‖R.comp A‖ ≤ ‖A‖ :=
    (ContinuousLinearMap.opNorm_comp_le R A).trans (mul_le_of_le_one_left (norm_nonneg A) hRS)
  have heSq : ‖M e - e‖ ^ 2 ≤ δ / B :=
    normalizedHalflineExponentialL2_sub_frequencyMultiplier_norm_sq_le hδ hδB M b hM hb hOne
  refine ⟨u, hu, hLine, hEstimate.trans ?_⟩
  calc
    _ ≤ ‖A‖ * ‖M e - e‖ := mul_le_mul_of_nonneg_right hRA (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le heSq) (norm_nonneg A)

end RiemannMasullo
