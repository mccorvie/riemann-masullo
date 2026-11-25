module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch09_HardySobolev.Sec3_Adjoint
import RiemannMasullo.Ch09_HardySobolev.Sec3_AdjointSymbols
import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass

/-! # A projective kernel for convolution on projected strip inputs

Quotient nuclearity implies nuclearity of the adjoint of each compact convolution on the
projected inputs. The finite weighted-adjoint decomposition recovers the original convolution
up to a nuclear error on the full Sobolev space.
-/

@[expose] public noncomputable section

open Function NumberField MeasureTheory
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "I(" h ")" => (neg_nonpos.mpr h).trans h
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "A(" h ", " k ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 _ _ _ I(h) k φ
local notation "P(" a ", " h ", " k ")" => spectralProjection (F := F) a h k

/-- The adjoint of a compact test convolution after spectral projection is nuclear
on the actual symmetric weighted Sobolev space, at every nonnegative width and
Sobolev order. -/
theorem stripTestAction_adjoint_comp_spectralProjection_nuclear
    (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (ψ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((A(hα, hs, ψ)).adjoint.comp P(a, hα, hs)) := by
  have hq := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) a hα hs ψ
  have hp := spectralProjection_convolution_nuclear (F := F) a hα hs ψ hq
  let P := P(a, hα, hs)
  let A : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, ψ)
  have hP : P.adjoint = P := isSelfAdjoint_starProjection _
  have heq : (P.comp A).adjoint = A.adjoint.comp P :=
    (ContinuousLinearMap.adjoint_comp P A).trans (congrArg (fun B ↦ A.adjoint.comp B) hP)
  change IsNuclearOperator (A.adjoint.comp P)
  rw [← heq]
  exact (traceNorm_adjoint_eq (P.comp A) hp).choose

/-- The compact-test convolution on the input spectral projection has a projective
Sobolev kernel for every symmetric strip, nonnegative Sobolev order and real twist. -/
theorem stripTestAction_spectralProjection_has_projectiveKernel (a : ℝ) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα hs K =
      (A(hα, hs, φ)).comp (spectralProjection (F := F) a hα hs) := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m𝔽 := fun t ↦ ⟨QuotientGroup.mk (canonicalIdeleNormSection F t),
    canonicalIdeleNormSection_rightInverse F t⟩
  obtain ⟨J, hJ, c, ψ, M, χ, l, r, hM, hLR, hid⟩ :=
    WeightedConvolution.exists_finite_weighted_adjoint_data μ𝔽 m𝔽 hm hms α s hα φ
  let _ : Fintype J := hJ
  let N (i : Bool × Bool) : W(α, s) →L[ℂ] W(α, s) := M i
  let T : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, φ)
  let B (i : Bool × Bool) : W(α, s) →L[ℂ] W(α, s) := (A(hα, hs, ψ i)).adjoint
  let P := P(a, hα, hs)
  have hR : T - ∑ i, N i * B i ∈ nuclearEndomorphisms (W(α, s)) :=
    WeightedConvolution.isNuclearOperator_sub_finite_masked_adjoints μ𝔽 m𝔽 hm hms
      (-α) α s I(hα) hs φ c ψ N χ l r hM hLR hid
  have hsum : (∑ i, N i * B i) * P ∈ nuclearEndomorphisms (W(α, s)) := by
    rw [Finset.sum_mul]
    apply (nuclearEndomorphisms _).sum_mem
    intro i _
    rw [mul_assoc]
    exact mul_mem_nuclearEndomorphisms_left (N i)
      ⟨B i * P, stripTestAction_adjoint_comp_spectralProjection_nuclear a hα hs (ψ i)⟩
  have herr := mul_mem_nuclearEndomorphisms_right P
    (⟨T - ∑ i, N i * B i, hR⟩ : nuclearEndomorphisms (W(α, s)))
  change (T - ∑ i, N i * B i) * P ∈ nuclearEndomorphisms (W(α, s)) at herr
  have h := (nuclearEndomorphisms _).add_mem herr hsum
  apply ((existsUnique_sobolevProjectiveKernel_iff_nuclear (F := F) hα hs _).mpr ?_).exists
  change T * P ∈ nuclearEndomorphisms (W(α, s))
  simpa only [sub_mul, sub_add_cancel] using h

end RiemannMasullo
