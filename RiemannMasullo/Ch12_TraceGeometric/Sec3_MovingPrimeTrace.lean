module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_MovingPrimeLevel
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ExactPrimeTrace
import RiemannMasullo.ForMathlib.Analysis.Fourier.SparseLaplaceProbe

/-! # Signed comparison of translated narrow traces with the first prime shell -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory Set NumberField
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.RationalWidthLoss

set_option quotPrecheck false

local notation "Ext(" δ ")" => {ρ : zeroSites // (δ : ℝ) ≤ |ρ.val.re - 1/2|}
local notation "freq(" t ")" => (((t : ℝ) : ℂ) * Complex.I)
local notation "shift(" H ", " y ")" => (fun x : ℝ ↦ (H : ℝ → ℂ) (x-y))
local notation "B(" H ", " z ")" => bilateralLaplace H z
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1/2) (band(ha)) (zero_lt_one.trans hs).le
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ))
local notation "lifts(" S ", " f ", " φ ")" => ∀ g : (SAdeleRing ℚ S)ˣ,
  HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ).val (ξ.val * g))
    ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))
local notation "rep(" T ", " φ ", " ha ", " hs ")" =>
  (T : nuclearEndomorphisms Q(ha, hs)).val =
    spectralConvolution (F := ℚ) (1/2) (band(ha)) (zero_lt_one.trans hs).le φ

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

/-- One localized probe kills both poles and every omitted spectral site while
taking prescribed Mellin values at a finite set of critical ordinates. -/
theorem exists_polarFree_critical_probe {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ : Injective γ) (v : ι → ℂ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (c : ℝ) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c-ε) (c+ε) ∧ H c = 1 ∧
      B(H,1/2) = 0 ∧ B(H,-(1/2)) = 0 ∧ (∀ j, B(H,freq(γ j)) = v j) ∧
      ∀ z : Ext(δ), B(H,z.val.val-1/2) = 0 := by
  let w : Ext(δ) ⊕ Bool → ℂ := Sum.elim (fun z ↦ z.val.val-1/2) (fun b ↦ if b then 1/2 else -(1/2))
  have hsum : Summable fun i ↦ 1/(1+|(w i).im|) := by
    apply Summable.sum _
    · simpa [Function.comp_def,w] using summable_exterior_inverse_height_unconditional hδ
    · exact (hasSum_fintype _).summable
  have hr : Injective (fun j ↦ freq(γ j)) := fun _ _ h ↦ hγ (by simpa using congrArg Complex.im h)
  have hdis (i) (j) : w i ≠ freq(γ j) := by
    rcases i with z | b
    · intro he
      have hre := congrArg Complex.re he
      have hz := z.property
      norm_num [w] at hre
      rw [show z.val.val.re-1/2=0 by linarith, abs_zero] at hz
      exact hδ.not_ge hz
    · cases b <;> intro he <;> have hre := congrArg Complex.re he <;> norm_num [w] at hre
  have hw (i) : w i ≠ (2 : ℝ) := by
    rcases i with z | b
    · intro he
      have hre := congrArg Complex.re he
      norm_num [w] at hre
      linarith [(re_mem_Ioo z.val).2]
    · cases b <;> norm_num [w]
  have hr' (j) : freq(γ j) ≠ (2 : ℝ) := by intro he; have := congrArg Complex.re he; norm_num at this
  obtain ⟨H,hH,hb,hc,hz,hv⟩ := SparseLaplace.exists_complex_interpolating_probe
    w hsum _ hr hdis 2 hw hr' v c hε
  exact ⟨H,hH,hb,hc,by simpa [w] using hz (.inr true),by simpa [w] using hz (.inr false),
    hv,fun z ↦ hz (.inl z)⟩

private theorem shift_window {l u y : ℝ} {H : ℝ → ℂ} (hb : tsupport H ⊆ Icc l u) :
    tsupport shift(H,y) ⊆ Icc (l+y) (u+y) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hh := hb (subset_tsupport H (show H (x-y) ≠ 0 from hx))
  exact ⟨by linarith [hh.1],by linarith [hh.2]⟩

set_option maxHeartbeats 850000 in
/-- The same probe and finite list of critical Mellin values work for all large
translations, every width above the prescribed threshold and every Sobolev
order above one. At each translation the sum of the narrow Hilbert trace and
the actual corrected local mass tends to the negative first-prime sum. -/
theorem exists_translated_primeLevel_stripTrace {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ : Injective γ) (v : ι → ℂ) {δ c ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c-ε) (c+ε) ∧ H c = 1 ∧
      (∀ y : ℝ, B(shift(H,y),1/2) = 0 ∧ B(shift(H,y),-(1/2)) = 0 ∧
        ∀ j, B(shift(H,y),freq(γ j)) = v j * Complex.exp (freq(γ j) * y)) ∧
      ∀ᶠ y : ℝ in atTop, let S := rationalPrimeLevel (c+ε+y)
        ∃ (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
          radial(φ,shift(H,y)) ∧ lifts(S,f,φ) ∧
          ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), δ ≤ a → ∀ T : nuclearEndomorphisms Q(ha, hs),
            rep(T,φ,ha,hs) → Tendsto (fun R : ℝ ↦ hilbertTrace T + rationalCorrectedSharpMass f R)
              atTop (𝓝 (-V * rationalFirstPrimeSum shift(H,y))) := by
  obtain ⟨H,hH,hb,hc,hp,hm,hv,hz⟩ := exists_polarFree_critical_probe γ hγ v hδ hε c
  refine ⟨H,hH,hb,hc,fun y ↦ ?_,?_⟩
  · refine ⟨?_, ?_, fun j ↦ ?_⟩ <;> simp only [SparseLaplace.bilateralLaplace_translate,hp,hm,hv,zero_mul]
  filter_upwards [eventually_gt_atTop (3*ε-c)] with y hy
  let G := shift(H,y)
  have hG : ContDiff ℝ (∞) G := hH.comp (contDiff_id.sub contDiff_const)
  have hW := shift_window (y := y) hb
  have hl : 0 < c-ε+y := by linarith
  obtain ⟨φ,f,hφ,hf,hlim⟩ := exists_primeLevel_signed_comparison hl
    (show (c+ε+y)/2 < c-ε+y by linarith) G hG hW
  refine ⟨φ,f,hφ,hf,?_⟩
  intro a s ha hs hδa T hT
  have hk : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hW
  have hpos : tsupport G ⊆ Ioi 0 := fun _ h ↦ hl.trans_le (hW h).1
  have hann (z : Ext(δ)) : B(G,z.val.val-1/2) = 0 := by
    rw [SparseLaplace.bilateralLaplace_translate, hz z, zero_mul]
  rw [hilbertTrace_eq_centered_of_exterior_vanishing hδa ha hs G hG hk hpos hann φ hφ T hT]
  exact hlim

end RiemannMasullo.RationalWidthLoss
