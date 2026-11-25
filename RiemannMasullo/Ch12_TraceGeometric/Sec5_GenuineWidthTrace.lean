module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_WidthCompatibility
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SignedWidthTrace

/-! # The trace discarded by restriction of genuine theta quotients

Paper: Chapter 10, §10.2.2, pp. 445–446. The representative restriction
intertwines the two actual convolutions. When those convolutions are nuclear,
the signed difference is the trace on the actual kernel. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "W(" δ ", " s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-δ) δ s
local notation "ν(" δ ", " s ")" => intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-δ) δ s
local notation "Θ(" a ", " h ", " hs ")" => globalThetaSobolev F a (neg_le_self h) hs
local notation "Q(" a ", " h ", " hs ")" => spectralSobolevQuotient F a (neg_le_self h) hs

local notation "C(" a ", " h ", " hs ", " φ ")" =>
  spectralConvolution (F := F) a (neg_le_self h) hs φ

/-- The trace of the wide convolution compressed to the closed restriction kernel. -/
def widthKernelTrace {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (J : H →L[ℂ] K) (T : nuclearEndomorphisms H) : ℂ :=
  hilbertTrace (WidthTrace.diagonalBlock J.ker T)

private theorem widthTrace_eq_diagonalBlock {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (J : H →L[ℂ] K) (hd : DenseRange J) (T : nuclearEndomorphisms H)
    (S : nuclearEndomorphisms K) (h : J.comp T.val = S.val.comp J) :
    hilbertTrace T - hilbertTrace S = widthKernelTrace J T :=
  (WidthTrace.hilbertTrace_sub_eq_kernelRestriction J hd T S h).trans
    (congrArg hilbertTrace (Subtype.ext (WidthTrace.kernelBlock_eq_restrict J T S.val h).symm))

/-- The genuine representative-preserving restriction from §10.2.2 discards
exactly the nuclear trace of the wide convolution on its kernel. -/
theorem spectralWidthTrace_sub_eq_kernelTrace (a : ℝ) {α β s : ℝ}
    (hα : 0 ≤ α) (hab : α ≤ β) (hs : 0 ≤ s)
    (I : W(β,s) →L[ℂ] W(α,s)) (hrep : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q)
    (J : Q(a,hα.trans hab,hs) →L[ℂ] Q(a,hα,hs)) (hdJ : DenseRange J)
    (hJ : ∀ q, J ((Θ(a,hα.trans hab,hs)).mkQ q) = (Θ(a,hα,hs)).mkQ (I q))
    (φ : BruhatCompactSupport C𝔽)
    (Tβ : nuclearEndomorphisms Q(a,hα.trans hab,hs)) (Tα : nuclearEndomorphisms Q(a,hα,hs))
    (hβT : Tβ.val = C(a,hα.trans hab,hs,φ)) (hαT : Tα.val = C(a,hα,hs,φ)) :
    hilbertTrace Tβ - hilbertTrace Tα =
      widthKernelTrace (H := Q(a,hα.trans hab,hs)) (K := Q(a,hα,hs)) J Tβ := by
  have h : J.comp Tβ.val = Tα.val.comp J := by
    rw [hβT, hαT]
    exact spectralConvolution_width_intertwines (F := F) a hα hab hs I hrep J hJ φ
  exact widthTrace_eq_diagonalBlock (H := Q(a,hα.trans hab,hs)) (K := Q(a,hα,hs))
    J hdJ Tβ Tα h

end RiemannMasullo
