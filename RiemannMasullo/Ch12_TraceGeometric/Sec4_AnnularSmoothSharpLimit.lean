module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_AnnularSmoothMassBridge
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Comparing the raw annular diagonal with the joint sharp orbit sum -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I" => (SAdeleRing F S)ˣ
local notation "H" => sProjectedDiagonal F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μI" => sMultiplicativeTamagawaMeasure F S
set_option quotPrecheck false in
local notation "vol₁" => ((sLocalNormOneQuotientMeasure F S univ).toReal : ℂ)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instSIdeleLocallyCompactSec1 instFiniteCompletionUnitsLocallyCompactSec4b

local instance instSIdeleT2AnnularSmoothSharpLimit : T2Space I := (sIdeleGroup_description F S).2.1

/-- The absolute smoothed mass of a spatial floor satisfies the same
power bound as the sharp masses, evaluated at the maximum radius product. -/
theorem sLocalSmoothMass_floor_norm_sum_le_rpow
    (f : BruhatCompactSupport I) (D : Set I) (hD : IsFundamentalDomain H D μI)
    {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hSharp : ∀ {R : ℝ}, 0 < R → R ≤ 1 →
      Summable (fun ξ : H ↦ ‖sLocalTraceSharpMass f ξ R‖) ∧
      (∑' ξ : H, ‖sLocalTraceSharpMass f ξ R‖) ≤ C * R ^ c)
    (σ γ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure γ]
    {a A₀ b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hσ : σ (Icc a A₀)ᶜ = 0) (hγ : γ (Icc b B)ᶜ = 0)
    (hAB : A₀ * B ≤ 1) :
    Summable (fun ξ : H ↦ ‖Isolated.sLocalSmoothMass f ξ D σ γ A₀‖) ∧
      (∑' ξ : H, ‖Isolated.sLocalSmoothMass f ξ D σ γ A₀‖) ≤ C * (A₀ * B) ^ c := by
  let μ := σ.prod γ
  let m (ξ : H) := Isolated.sLocalSmoothMass f ξ D σ γ A₀
  let k (ξ : H) (p : ℝ × ℝ) := sLocalTraceSharpMass f ξ (p.1 * p.2)
  have hI (ξ : H) : Integrable (k ξ) μ ∧ m ξ = ∫ p, k ξ p ∂μ :=
    Isolated.sLocalSmoothMass_eq_average f ξ D hD σ γ ha hb hσ hγ
  have hmem : ∀ᵐ p ∂μ, p.1 ∈ Icc a A₀ ∧ p.2 ∈ Icc b B := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := σ) (ν := γ)).ae
      (Isolated.ae_mem_of_prob_support hσ),
      (Measure.quasiMeasurePreserving_snd (μ := σ) (ν := γ)).ae
      (Isolated.ae_mem_of_prob_support hγ)] with p h₁ h₂
    exact ⟨h₁, h₂⟩
  have hfin (u : Finset H) : (∑ ξ ∈ u, ‖m ξ‖) ≤ C * (A₀ * B) ^ c := by
    calc
      _ ≤ ∑ ξ ∈ u, ∫ p, ‖k ξ p‖ ∂μ := Finset.sum_le_sum fun ξ _ ↦ by
        rw [(hI ξ).2]
        exact norm_integral_le_integral_norm _
      _ = ∫ p, ∑ ξ ∈ u, ‖k ξ p‖ ∂μ := (integral_finsetSum u fun ξ _ ↦ (hI ξ).1.norm).symm
      _ ≤ ∫ _ : ℝ × ℝ, C * (A₀ * B) ^ c ∂μ := by
        refine integral_mono_ae (integrable_finsetSum u fun ξ _ ↦ (hI ξ).1.norm)
          (integrable_const _) ?_
        filter_upwards [hmem] with p hp
        have hp₁ : 0 < p.1 := ha.trans_le hp.1.1
        have hp₂ : 0 < p.2 := hb.trans_le hp.2.1
        have hle : p.1 * p.2 ≤ A₀ * B :=
          mul_le_mul hp.1.2 hp.2.2 hp₂.le (hp₁.le.trans hp.1.2)
        obtain ⟨hS, hBound⟩ := hSharp (mul_pos hp₁ hp₂) (hle.trans hAB)
        exact ((hS.sum_le_tsum u fun _ _ ↦ norm_nonneg _).trans hBound).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_pos hp₁ hp₂).le hle hc) hC)
      _ = _ := by simp [μ, integral_const]
  have hm := summable_of_sum_le (fun ξ ↦ norm_nonneg (m ξ)) hfin
  exact ⟨hm, hm.tsum_le_of_sum_le hfin⟩

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518. Along the joint upper cutoff limit,
an annular raw diagonal integral
with a small spatial-floor product differs from the summed sharp mass by
a term tending to zero. The exact annular sum and its summability are the
fixed-cutoff inputs. The small-positive-radius estimate is an explicit input.

For the diagonal constructed by
`exists_sLocalTrace_fixedAnnulus_smoothMass_difference`, each spatial mask
must still satisfy `IsModulatedCutoff`, including invariance under inversion.
Deviation: The filter on the radius pair specifies the joint path on which
the floor product vanishes. -/
theorem sLocalAnnularRawDiagonal_sub_sharpMass_tendsto_zero
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (g : C𝔽),
      φ.val (QuotientGroup.mk a.val * g) = φ.val g)
    (f : BruhatCompactSupport I)
    (hLift : ∀ g : I, HasSum (fun ξ : H ↦ f.val (ξ.val * g))
      (φ.val (QuotientGroup.mk (sIdeleInsertion F S g))))
    (D : Set I) (hD : IsFundamentalDomain H D μI)
    (σ γ σFloor : ℝ × ℝ → Measure ℝ)
    [∀ p, IsProbabilityMeasure (σ p)] [∀ p, IsProbabilityMeasure (γ p)]
    [∀ p, IsProbabilityMeasure (σFloor p)]
    (ε aFloor floor : ℝ × ℝ → ℝ) (raw : ℝ × ℝ → ℂ)
    (l : Filter (ℝ × ℝ)) (hl : l ≤ atTop ×ˢ atTop)
    (hσ : ∀ p, σ p (Icc (p.1 - ε p) p.1)ᶜ = 0)
    (hγ : ∀ p, γ p (Icc (p.2 - ε p) p.2)ᶜ = 0)
    (hε₁ : Tendsto (fun p ↦ ε p / p.1) (atTop ×ˢ atTop) (𝓝 0))
    (hε₂ : Tendsto (fun p ↦ ε p / p.2) (atTop ×ˢ atTop) (𝓝 0))
    (hFloor : ∀ᶠ p in l,
      0 < aFloor p ∧ σFloor p (Icc (aFloor p) (floor p))ᶜ = 0)
    (hSharp : ∃ C ≥ 0, ∀ {R : ℝ}, 0 < R → R ≤ 1 →
      Summable (fun ξ : H ↦ ‖sLocalTraceSharpMass f ξ R‖) ∧
      (∑' ξ : H, ‖sLocalTraceSharpMass f ξ R‖) ≤ C * R ^ (1 / 2 : ℝ))
    (hSmall : Tendsto (fun p ↦ floor p * p.2) l (𝓝 0)) :
    let Top (p : ℝ × ℝ) (ξ : H) := Isolated.sLocalSmoothMass f ξ D (σ p) (γ p) p.1
    let Floor (p : ℝ × ℝ) (ξ : H) :=
      Isolated.sLocalSmoothMass f ξ D (σFloor p) (γ p) (floor p)
    (∀ᶠ p in l,
      Summable (fun ξ : H ↦ Top p ξ - Floor p ξ) ∧
      raw p = ∑' ξ : H, (Top p ξ - Floor p ξ)) →
    Tendsto (fun p ↦ raw p - ∑' ξ : H, sLocalTraceSharpMass f ξ (p.1 * p.2))
      l (𝓝 0) := by
  intro Top Floor hRaw
  let R (p : ℝ × ℝ) := p.1 * p.2
  let logTerm (p : ℝ × ℝ) := vol₁ * φ.val 1 * (Real.log (R p) : ℂ)
  let STop (p : ℝ × ℝ) := ∑' ξ : H, Top p ξ
  let SFloor (p : ℝ × ℝ) := ∑' ξ : H, Floor p ξ
  let Sharp (p : ℝ × ℝ) := ∑' ξ : H, sLocalTraceSharpMass f ξ (R p)
  obtain ⟨C, hC, hSharpBound⟩ := hSharp
  have hL : Tendsto (Prod.fst : ℝ × ℝ → ℝ) l atTop := tendsto_fst.mono_left hl
  have hB : Tendsto (Prod.snd : ℝ × ℝ → ℝ) l atTop := tendsto_snd.mono_left hl
  have hγPos : ∀ᶠ p in l, 0 < p.2 - ε p := by
    filter_upwards [hB.eventually (eventually_gt_atTop (0 : ℝ)),
      (hε₂.mono_left hl).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with p hp hεp
    have hεp' := (div_le_iff₀ hp).mp hεp
    linarith
  have hFloorBound : ∀ᶠ p in l,
      Summable (fun ξ : H ↦ ‖Floor p ξ‖) ∧
        (∑' ξ : H, ‖Floor p ξ‖) ≤ C * (floor p * p.2) ^ (1 / 2 : ℝ) := by
    filter_upwards [hγPos, hFloor, hSmall.eventually (ge_mem_nhds zero_lt_one)] with p hg hf hs
    exact sLocalSmoothMass_floor_norm_sum_le_rpow f D hD (c := 1 / 2) (by norm_num) hC hSharpBound
      (σFloor p) (γ p) hf.1 hg hf.2 (hγ p) hs
  have hBound0 : Tendsto (fun p ↦ C * (floor p * p.2) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
    have hr := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
    simpa only [Function.comp_apply, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero] using
      (hr.comp hSmall).const_mul C
  have hFloor0 : Tendsto SFloor l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun p ↦ norm_nonneg (SFloor p)) ?_ hBound0
    filter_upwards [hFloorBound] with p hp
    exact (norm_tsum_le_tsum_norm hp.1).trans hp.2
  have hrawEq : raw =ᶠ[l] fun p ↦ STop p - SFloor p := by
    filter_upwards [hRaw, hFloorBound] with p hp hf
    have hf' : Summable (Floor p) := hf.1.of_norm
    have ht : Summable (Top p) := by
      have h := hp.1.add hf'
      simpa only [sub_add_cancel] using h
    exact hp.2.trans (ht.hasSum.sub hf'.hasSum).tsum_eq
  obtain ⟨a, b, ha, hb, hTopLim⟩ :=
    Isolated.sLocalSmoothMass_asymptotic φ hPic hRam hOutside f hLift D hD
      σ γ ε hσ hγ hε₁ hε₂
  obtain ⟨a', b', M, ha', hb', hSharpSum, hSharpLim⟩ :=
    sLocalTraceSharpMass_asymptotic φ hPic hRam hOutside f hLift
  have haa : a' = a := by
    funext w
    change (show ↥(bruhatCompactSupportSubmodule w.Completionˣ) from a' w) =
      (show ↥(bruhatCompactSupportSubmodule w.Completionˣ) from a w)
    apply Subtype.ext
    exact funext fun u ↦ (ha' w u).trans (ha w u).symm
  have hbb : b' = b := by
    funext v
    change (show ↥(bruhatCompactSupportSubmodule (v.val.adicCompletion F)ˣ) from b' v) =
      (show ↥(bruhatCompactSupportSubmodule (v.val.adicCompletion F)ˣ) from b v)
    apply Subtype.ext
    exact funext fun u ↦ (hb' v u).trans (hb v u).symm
  subst a'
  subst b'
  have hR : Tendsto R l atTop := hL.atTop_mul_atTop₀ hB
  have hSharpEq : (fun p ↦ M (R p) - logTerm p) =ᶠ[l] fun p ↦ Sharp p - logTerm p := by
    filter_upwards [hR.eventually hSharpSum] with p hp
    exact congrArg (fun z : ℂ ↦ z - logTerm p) hp.tsum_eq.symm
  have hBoth := (hTopLim.mono_left hl).sub ((hSharpLim.comp hR).congr' hSharpEq)
  rw [sub_self] at hBoth
  have hTopSharp : Tendsto (fun p ↦ STop p - Sharp p) l (𝓝 0) :=
    hBoth.congr' (Eventually.of_forall fun p ↦ by
      change (STop p - logTerm p) - (Sharp p - logTerm p) = _
      ring)
  have h := hTopSharp.sub hFloor0
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hrawEq] with p hp
  rw [hp]
  change (STop p - Sharp p) - SFloor p = (STop p - SFloor p) - Sharp p
  ring

end RiemannMasullo
