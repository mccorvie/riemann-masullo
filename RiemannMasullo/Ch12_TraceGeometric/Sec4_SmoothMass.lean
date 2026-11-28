module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Smoothed orbital masses as averages of sharp ones

The kernel of Theorem 12.4.1.1 uses smooth cutoffs. In Step II (p. 516) the spatial cutoff
smooths the indicator of `|x| ≤ λ` and the frequency cutoff smooths the indicator of
`|u| ≤ λ'`. Equation (12.4.1.22) then replaces both by sharp indicators. As an equality this
fails (`Printed.sLocalSmoothMass_eq_sharp_real_false`), and `Sec4.lean` proves the asymptotic
for the sharp masses (`sLocalTraceSharpMass_asymptotic`). This file proves it for smoothed
masses, for every number field and every set `S` satisfying the hypotheses of the theorem.

The cutoffs are averages of sharp indicators. For a probability measure `μ` on `[a₀, a₁]` the
cutoff `t ↦ μ([t, ∞))` (`avgCutoff`) equals one up to `a₀` and vanishes beyond `a₁`. On the skew
diagonal the kernel with these cutoffs is a function of the norm (`smoothKernel_diag`).
Integrating it over an S-unit fundamental domain gives the smoothed orbital mass
`sLocalSmoothMass`, the quantity (12.4.1.11). That mass is the average of the sharp masses at the
radii `a b`, for `a` drawn from the spatial measure and `b` from the frequency measure
(`sLocalSmoothMass_eq_average`). The proof is Fubini over the spatial variable and the two
radii. Its domination is the estimate of `sLocalTrace_band_log_fubini` with absolute values
(`integrableOn_bandNorm`).

For each unit, the sharp mass at radius `R` is its logarithmic term, plus a constant, plus a
remainder bounded for `R ≥ 1` by a summable function of the unit
(`sLocalTraceSharpMass_remainder_bound`). The constants cancel between the average and the sharp
mass at `L L'`. The logarithmic terms differ by at most `φ(1)` times
`log (L / (L - ε)) + log (L' / (L' - ε))`, and the remainders tend to zero unit by unit under a
summable bound. So the summed smoothed masses have the asymptotic of Theorem 12.4.1.1
(`sLocalSmoothMass_asymptotic`) as `L` and `L'` tend to infinity with `ε / L` and `ε / L'`
tending to zero. That includes a fixed width `ε` and the regime `ε λ → 0` of p. 519.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

section AverageCutoff

/-- The cutoff `t ↦ μ([t, ∞))`. Against a probability measure `μ` it is the average of the
indicators of `(-∞, a]` over `a`. -/
def avgCutoff (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Ici t)

theorem avgCutoff_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (avgCutoff μ) :=
  fun _ _ h ↦ measureReal_mono (Ici_subset_Ici.2 h)

theorem measurable_avgCutoff (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (avgCutoff μ) :=
  (avgCutoff_antitone μ).measurable

theorem avgCutoff_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ avgCutoff μ t := measureReal_nonneg

theorem avgCutoff_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    avgCutoff μ t ≤ 1 := by
  unfold avgCutoff
  exact (measureReal_mono (subset_univ _)).trans (by simp)

theorem avgCutoff_eq_integral (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (avgCutoff μ t : ℂ) = ∫ a, (Ici t).indicator (fun _ ↦ (1 : ℂ)) a ∂μ := by
  rw [integral_indicator_const _ measurableSet_Ici, Complex.real_smul, mul_one]
  rfl

/-- A probability measure on `[a₀, a₁]` gives a cutoff equal to one up to `a₀`. -/
theorem avgCutoff_eq_one (μ : Measure ℝ) [IsProbabilityMeasure μ] {a₀ a₁ : ℝ}
    (hμ : μ (Icc a₀ a₁)ᶜ = 0) {t : ℝ} (ht : t ≤ a₀) : avgCutoff μ t = 1 := by
  have h : μ (Ici t)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 fun a (ha : a ∈ Icc a₀ a₁) ↦
    show a ∈ Ici t from ht.trans ha.1) hμ
  rw [avgCutoff, Measure.real, prob_compl_eq_zero_iff measurableSet_Ici |>.1 h]
  simp

/-- A probability measure on `[a₀, a₁]` gives a cutoff vanishing beyond `a₁`. -/
theorem avgCutoff_eq_zero (μ : Measure ℝ) {a₀ a₁ : ℝ} (hμ : μ (Icc a₀ a₁)ᶜ = 0) {t : ℝ}
    (ht : a₁ < t) : avgCutoff μ t = 0 := by
  have h : μ (Ici t) = 0 := measure_mono_null (show Ici t ⊆ (Icc a₀ a₁)ᶜ from
    fun a (ha : a ∈ Ici t) (h : a ∈ Icc a₀ a₁) ↦ (not_le.2 (ht.trans_le ha)) h.2) hμ
  rw [avgCutoff, Measure.real, h, ENNReal.toReal_zero]

end AverageCutoff

section Kernel

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
local notation "band(" L ")" => sLocalPWProductRegion (F := F) S L

local instance instSIdeleT2SmoothMass : T2Space Iₛ := (sIdeleGroup_description F S).2.1

theorem continuous_modS : Continuous fun x : Aₛ ↦ modS(x) :=
  (continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
    (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)

theorem modS_neg (u : Aₛ) : modS(-u) = modS(u) := by
  simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, norm_neg]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [show (-u.1) w = -(u.1 w) from rfl, norm_neg]

theorem measurableSet_band (r : ℝ) : MeasurableSet (band(r)) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  exact (isClosed_le continuous_modS continuous_const).measurableSet

/-- An element of the projected diagonal has S-idele norm one. -/
theorem sIdeleNorm_projectedDiagonal (ξ : Hₛ) : sIdeleNorm F S ξ.val = 1 := by
  obtain ⟨γ, hγ, hξ⟩ := Subgroup.mem_map.mp ξ.property
  rw [← hξ]
  exact (sIdeleNorm_spec F S).2 hγ

theorem normS_projectedDiagonal_mul (ξ : Hₛ) (x : Iₛ) : normS(ξ.val * x) = normS(x) := by
  rw [map_mul, sIdeleNorm_projectedDiagonal, one_mul]

/-- The integral of the Fourier transform of the translated test over the band of radius `r`. -/
def bandIntegral (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (r : ℝ) : ℂ :=
  ∫ w in band(r), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ

theorem measurable_bandIntegral (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    Measurable (bandIntegral f ξ) := by
  have h := sLocalTrace_band_integral_measurable f ξ 1
  simp only [one_mul] at h
  exact h

theorem integrable_fourier_dilate (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (x : Iₛ) :
    Integrable (fun u ↦ fourierₛ (sLocalTraceEta f ξ) (x.val * u)) νₛ := by
  have h := (sLocalTraceCutoffKernel_skew f (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ))
    measurable_const ⟨1, fun _ ↦ by simp⟩ (fun _ ↦ rfl) ξ x).1
  simpa using h

/-- Averaging the frequency band over the radius: the frequency integral of the averaged
cutoff is the average of the dilated band integrals. -/
theorem integral_avgCutoff_mul_fourier (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (x : Iₛ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∫ u, (avgCutoff μ modS(u) : ℂ) * fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ =
      ∫ b, ((normS(x))⁻¹ : ℂ) * bandIntegral f ξ (b * normS(x)) ∂μ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  set g := fun u ↦ fourierₛ (sLocalTraceEta f ξ) (x.val * u) with hg_def
  have hg : Integrable g νₛ := integrable_fourier_dilate f ξ x
  have hT : MeasurableSet {p : Aₛ × ℝ | modS(p.1) ≤ p.2} :=
    measurableSet_le (continuous_modS.measurable.comp measurable_fst) measurable_snd
  have hint : Integrable (Function.uncurry fun u b ↦
      (Ici modS(u)).indicator (fun _ ↦ (1 : ℂ)) b * g u) ((νₛ).prod μ) := by
    refine (hg.norm.mul_prod (integrable_const (1 : ℝ))).mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · change AEStronglyMeasurable (fun p : Aₛ × ℝ ↦
        {p : Aₛ × ℝ | modS(p.1) ≤ p.2}.indicator (fun _ ↦ (1 : ℂ)) p * g p.1) _
      exact (measurable_const.indicator hT).aestronglyMeasurable.mul hg.1.comp_fst
    · simp only [Function.uncurry, mul_one]
      by_cases h : p.2 ∈ Ici modS(p.1)
      · rw [indicator_of_mem h, one_mul]
      · rw [indicator_of_notMem h, zero_mul, norm_zero]
        exact norm_nonneg _
  calc ∫ u, (avgCutoff μ modS(u) : ℂ) * g u ∂νₛ
      = ∫ u, ∫ b, (Ici modS(u)).indicator (fun _ ↦ (1 : ℂ)) b * g u ∂μ ∂νₛ := by
        congr 1
        funext u
        rw [avgCutoff_eq_integral, integral_mul_const]
    _ = ∫ b, ∫ u, (Ici modS(u)).indicator (fun _ ↦ (1 : ℂ)) b * g u ∂νₛ ∂μ :=
        integral_integral_swap hint
    _ = ∫ b, ∫ u in band(b), g u ∂νₛ ∂μ := by
        congr 1
        funext b
        rw [← integral_indicator (measurableSet_band b)]
        congr 1
        funext u
        by_cases h : modS(u) ≤ b
        · rw [indicator_of_mem (show b ∈ Ici modS(u) from h), one_mul,
            indicator_of_mem (show u ∈ band(b) from h)]
        · rw [indicator_of_notMem (show b ∉ Ici modS(u) from h), zero_mul,
            indicator_of_notMem (show u ∉ band(b) from h)]
    _ = ∫ b, ((normS(x))⁻¹ : ℂ) * bandIntegral f ξ (b * normS(x)) ∂μ := by
        congr 1
        funext b
        rw [hg_def, sLocalTrace_integral_band_dilate]
        rfl

/-- The kernel with averaged cutoffs on the skew diagonal is a function of the norm. -/
theorem smoothKernel_diag (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (μρ μσ : Measure ℝ)
    [IsProbabilityMeasure μρ] [IsProbabilityMeasure μσ] (x : Iₛ) :
    sLocalTraceCutoffKernel f (fun x ↦ (avgCutoff μρ normS(x) : ℂ))
        (fun u ↦ (avgCutoff μσ modS(u) : ℂ)) (ξ.val * x) x.val =
      (sLocalTraceMeasureFactor S : ℂ) * ((normS(x))⁻¹ : ℂ) *
        ((avgCutoff μρ normS(x) : ℂ) * ∫ b, bandIntegral f ξ (b * normS(x)) ∂μσ) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have hm : Measurable fun u : Aₛ ↦ (avgCutoff μσ modS(u) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_avgCutoff μσ).comp continuous_modS.measurable)
  have hb : ∃ C : ℝ, ∀ u, ‖(avgCutoff μσ modS(u) : ℂ)‖ ≤ C :=
    ⟨1, fun u ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (avgCutoff_nonneg _ _)]
      exact avgCutoff_le_one _ _⟩
  rw [(sLocalTraceCutoffKernel_skew f _ _ hm hb (fun u ↦ by simp only [modS_neg]) ξ x).2]
  simp only [normS_projectedDiagonal_mul]
  rw [integral_avgCutoff_mul_fourier, integral_const_mul]
  ring

/-- The band integral of the norm of the Fourier transform, divided by `t`, is integrable on
`(0, L]`. This is the estimate of `sLocalTrace_band_log_fubini` with absolute values. -/
theorem integrableOn_bandNorm (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) {L L' : ℝ} (hL : 0 < L)
    (hL' : 0 < L') :
    IntegrableOn (fun t ↦ (∫ w in band(L' * t), ‖fourierₛ (sLocalTraceEta f ξ) w‖ ∂νₛ) / t)
      (Ioc 0 L) := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let g := fourierₛ (sLocalTraceEta f ξ)
  have hgi : Integrable g νₛ := sLocalTraceEta_fourier_integrable f ξ
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  have hgc : Continuous g := by
    change Continuous (fourierₛ (sLocalTraceEta f ξ))
    rw [← funext hη]
    exact (schwartzBruhat_continuous (sAdeleSchwartzFourier η)).comp continuous_ofAdd
  have hgl := sLocalTrace_fourier_log_integrable f ξ
  let m : Aₛ → ℝ := fun w ↦ modS(w)
  have hm : Continuous m := continuous_modS
  have hband (r : ℝ) : MeasurableSet (band(r)) := measurableSet_band r
  have hfull : ∀ᵐ u ∂νₛ, u ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  have hmpos : ∀ᵐ w ∂νₛ, 0 < m w := by
    filter_upwards [hfull] with w hw
    obtain ⟨u, rfl⟩ := hw
    have h : m u.val = normS(u) := by simp [m, sIdeleNorm, Units.coe_prod]
    rw [h]
    exact NNReal.coe_pos.mpr (Units.zero_lt _)
  let φ : Aₛ → ℝ := fun w ↦ if m w / L' ≤ L then Real.log L - Real.log (m w / L') else 0
  have hφ (w : Aₛ) (hw : 0 < m w) :
      φ w = (band(L * L')).indicator (fun w ↦ Real.log (L * L') - Real.log (m w)) w := by
    have hiff : m w / L' ≤ L ↔ w ∈ band(L * L') := div_le_iff₀ hL'
    by_cases h : w ∈ band(L * L')
    · rw [indicator_of_mem h]
      simp only [φ, ite_eq_left (hiff.2 h)]
      rw [Real.log_div hw.ne' hL'.ne', Real.log_mul hL.ne' hL'.ne']
      ring
    · rw [indicator_of_notMem h]
      simp only [φ, ite_eq_right (mt hiff.1 h)]
  let μt := (volume : Measure ℝ).restrict (Ioc 0 L)
  let T : Set (ℝ × Aₛ) := {p | m p.2 / L' ≤ p.1}
  have hT : MeasurableSet T :=
    measurableSet_le ((hm.measurable.comp measurable_snd).div_const _) measurable_fst
  let K : ℝ × Aₛ → ℝ := fun p ↦ ‖g p.2‖ * T.indicator (fun p ↦ p.1⁻¹) p
  have hKm : Measurable K := (hgc.norm.measurable.comp measurable_snd).mul
    (measurable_fst.inv.indicator hT)
  have hKt (t : ℝ) (w : Aₛ) : K (t, w) = ‖g w‖ * (Ici (m w / L')).indicator
      (fun t : ℝ ↦ t⁻¹) t := rfl
  have hind_nonneg (w : Aₛ) (hw : 0 < m w) (t : ℝ) :
      0 ≤ (Ici (m w / L')).indicator (fun t : ℝ ↦ t⁻¹) t := by
    by_cases ht : t ∈ Ici (m w / L')
    · rw [indicator_of_mem ht]
      exact inv_nonneg.mpr ((div_pos hw hL').le.trans ht)
    · rw [indicator_of_notMem ht]
  have hinnerN (w : Aₛ) (hw : 0 < m w) : ∫ t, ‖K (t, w)‖ ∂μt = ‖g w‖ * φ w := by
    have h (t : ℝ) : ‖K (t, w)‖ = ‖g w‖ * (Ici (m w / L')).indicator (fun t : ℝ ↦ t⁻¹) t := by
      rw [hKt, norm_mul, norm_norm, Real.norm_eq_abs, abs_of_nonneg (hind_nonneg w hw t)]
    simp_rw [h]
    rw [integral_const_mul, sLocalTrace_integral_inv_Ici _ L (div_pos hw hL')]
  have hgφ : Integrable (fun w ↦ ‖g w‖ * φ w) νₛ := by
    have hlog : Integrable (fun w ↦ ‖g w‖ * Real.log (m w)) νₛ :=
      hgl.norm.mono'
        ((hgc.norm.measurable.mul (Real.measurable_log.comp hm.measurable)).aestronglyMeasurable)
        (ae_of_all _ fun w ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs])
    have hi : Integrable ((band(L * L')).indicator
        (fun w ↦ ‖g w‖ * (Real.log (L * L') - Real.log (m w)))) νₛ := by
      refine Integrable.indicator ?_ (hband _)
      simp_rw [mul_sub]
      exact (hgi.norm.mul_const _).sub hlog
    refine hi.congr ?_
    filter_upwards [hmpos] with w hw
    rw [hφ w hw]
    by_cases h : w ∈ band(L * L')
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  have hKi : Integrable K (μt.prod νₛ) := by
    rw [integrable_prod_iff' hKm.aestronglyMeasurable]
    refine ⟨?_, hgφ.congr ?_⟩
    · filter_upwards [hmpos] with w hw
      have ha : 0 < m w / L' := div_pos hw hL'
      have hb : Integrable (fun t ↦ (Ici (m w / L')).indicator (fun t : ℝ ↦ t⁻¹) t) μt := by
        rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn,
          Measure.restrict_restrict measurableSet_Ici]
        refine (ContinuousOn.integrableOn_compact (isCompact_Icc : IsCompact (Icc (m w / L') L))
          (continuousOn_inv₀.mono fun t ht ↦ (ha.trans_le ht.1).ne')).mono_set ?_
        rintro t ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
      simp_rw [hKt]
      exact hb.const_mul _
    · filter_upwards [hmpos] with w hw
      exact (hinnerN w hw).symm
  have hlhs (t : ℝ) (ht : 0 < t) :
      (∫ w in band(L' * t), ‖g w‖ ∂νₛ) / t = ∫ w, K (t, w) ∂νₛ := by
    rw [← integral_indicator (hband _), ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    change (band(L' * t)).indicator (fun w ↦ ‖g w‖) w / t = K (t, w)
    rw [hKt]
    have hiff : w ∈ band(L' * t) ↔ t ∈ Ici (m w / L') := by
      rw [mem_Ici, div_le_iff₀ hL', mul_comm]
      rfl
    by_cases h : w ∈ band(L' * t)
    · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h), div_eq_mul_inv]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.2 h), zero_div, mul_zero]
  refine hKi.integral_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (hlhs t ht.1).symm

/-- A probability measure supported on `[a₀, L]` with `a₀ ≤ L` forces `a₀ ≤ L`. -/
theorem le_of_prob_support {μ : Measure ℝ} [IsProbabilityMeasure μ] {a₀ L : ℝ}
    (hμ : μ (Icc a₀ L)ᶜ = 0) : a₀ ≤ L := by
  by_contra h
  have hc : (Icc a₀ L)ᶜ = univ := by rw [Icc_eq_empty h, compl_empty]
  rw [hc, measure_univ] at hμ
  exact one_ne_zero hμ

theorem ae_mem_of_prob_support {μ : Measure ℝ} {a₀ L : ℝ} (hμ : μ (Icc a₀ L)ᶜ = 0) :
    ∀ᵐ a ∂μ, a ∈ Icc a₀ L :=
  (measure_eq_zero_iff_ae_notMem.mp hμ).mono fun _ h ↦ not_not.mp h

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518.
Reconstruction: with averaged cutoffs, the radial integral that computes the smoothed orbital
mass is the average of the sharp orbital masses at the radii `a b`, for `a` drawn from the
spatial measure and `b` from the frequency measure. -/
theorem smoothRadial_eq_average (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (μρ μσ : Measure ℝ)
    [IsProbabilityMeasure μρ] [IsProbabilityMeasure μσ] {a₀ L b₀ L' : ℝ} (ha₀ : 0 < a₀)
    (hb₀ : 0 < b₀) (hρ : μρ (Icc a₀ L)ᶜ = 0) (hσ : μσ (Icc b₀ L')ᶜ = 0) :
    IntegrableOn (fun t ↦ (avgCutoff μρ t : ℂ) * (∫ b, bandIntegral f ξ (b * t) ∂μσ) / (t : ℂ))
        (Ioc 0 L) ∧
      Integrable (fun q : ℝ × ℝ ↦ sLocalTraceSharpMass f ξ (q.1 * q.2)) (μρ.prod μσ) ∧
      (volume₁ : ℂ) * ∫ t in Ioc 0 L,
          (avgCutoff μρ t : ℂ) * (∫ b, bandIntegral f ξ (b * t) ∂μσ) / (t : ℂ) =
        ∫ q, sLocalTraceSharpMass f ξ (q.1 * q.2) ∂(μρ.prod μσ) := by
  have hL : 0 < L := ha₀.trans_le (le_of_prob_support hρ)
  have hL' : 0 < L' := hb₀.trans_le (le_of_prob_support hσ)
  let μt := (volume : Measure ℝ).restrict (Ioc 0 L)
  let ν2 := μρ.prod μσ
  let B := bandIntegral f ξ
  have hBm : Measurable B := measurable_bandIntegral f ξ
  let Ψ : ℝ × (ℝ × ℝ) → ℂ := fun p ↦
    (Ici p.1).indicator (fun _ ↦ (1 : ℂ)) p.2.1 * (B (p.2.2 * p.1) / (p.1 : ℂ))
  have hΨm : Measurable Ψ := by
    have hS : MeasurableSet {p : ℝ × (ℝ × ℝ) | p.1 ≤ p.2.1} :=
      measurableSet_le measurable_fst (measurable_fst.comp measurable_snd)
    change Measurable fun p : ℝ × (ℝ × ℝ) ↦
      {p : ℝ × (ℝ × ℝ) | p.1 ≤ p.2.1}.indicator (fun _ ↦ (1 : ℂ)) p *
        (B (p.2.2 * p.1) / (p.1 : ℂ))
    exact (measurable_const.indicator hS).mul
      ((hBm.comp ((measurable_snd.comp measurable_snd).mul measurable_fst)).div
        (Complex.measurable_ofReal.comp measurable_fst))
  have hG := integrableOn_bandNorm f ξ hL hL'
  have hρae := ae_mem_of_prob_support hρ
  have hσae := ae_mem_of_prob_support hσ
  have hq : ∀ᵐ q ∂ν2, q.1 ∈ Icc a₀ L ∧ q.2 ∈ Icc b₀ L' := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μρ) (ν := μσ)).ae hρae,
      (Measure.quasiMeasurePreserving_snd (μ := μρ) (ν := μσ)).ae hσae] with q h1 h2
    exact ⟨h1, h2⟩
  have hΨi : Integrable Ψ (μt.prod ν2) := by
    refine (hG.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ × ℝ ↦ (1 : ℝ)) ν2)).mono'
      hΨm.aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μt) (ν := ν2)).ae
      (ae_restrict_mem measurableSet_Ioc),
      (Measure.quasiMeasurePreserving_snd (μ := μt) (ν := ν2)).ae hq] with p hp1 hp2
    have ht : 0 < p.1 := hp1.1
    have hB : ‖B (p.2.2 * p.1)‖ ≤
        ∫ w in band(L' * p.1), ‖fourierₛ (sLocalTraceEta f ξ) w‖ ∂νₛ := by
      refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_set
        (sLocalTraceEta_fourier_integrable f ξ).norm.integrableOn
        (ae_of_all _ fun _ ↦ norm_nonneg _) (ae_of_all _ fun w (hw : w ∈ band(p.2.2 * p.1)) ↦
          show w ∈ band(L' * p.1) from
            hw.trans (mul_le_mul_of_nonneg_right hp2.2.2 ht.le)))
    simp only [Ψ, mul_one, norm_mul]
    have hind : ‖(Ici p.1).indicator (fun _ ↦ (1 : ℂ)) p.2.1‖ ≤ 1 := by
      by_cases h : p.2.1 ∈ Ici p.1
      · rw [indicator_of_mem h, norm_one]
      · rw [indicator_of_notMem h, norm_zero]
        exact zero_le_one
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    calc ‖(Ici p.1).indicator (fun _ ↦ (1 : ℂ)) p.2.1‖ * (‖B (p.2.2 * p.1)‖ / p.1)
        ≤ 1 * (‖B (p.2.2 * p.1)‖ / p.1) :=
          mul_le_mul_of_nonneg_right hind (div_nonneg (norm_nonneg _) ht.le)
      _ ≤ _ := by
          rw [one_mul]
          exact div_le_div_of_nonneg_right hB ht.le
  -- The inner integral over the measures.
  have hA (t : ℝ) : ∫ q, Ψ (t, q) ∂ν2 =
      (avgCutoff μρ t : ℂ) * (∫ b, B (b * t) ∂μσ) / (t : ℂ) := by
    simp only [Ψ]
    rw [integral_prod_mul (fun a ↦ (Ici t).indicator (fun _ ↦ (1 : ℂ)) a)
      (fun b ↦ B (b * t) / (t : ℂ)), ← avgCutoff_eq_integral, integral_div, mul_div_assoc]
  -- The inner integral over the spatial variable.
  have hB (q : ℝ × ℝ) (hq : q.1 ∈ Icc a₀ L ∧ q.2 ∈ Icc b₀ L') :
      (volume₁ : ℂ) * ∫ t, Ψ (t, q) ∂μt = sLocalTraceSharpMass f ξ (q.1 * q.2) := by
    have ha : 0 < q.1 := ha₀.trans_le hq.1.1
    have hb : 0 < q.2 := hb₀.trans_le hq.2.1
    have hsplit : ∫ t, Ψ (t, q) ∂μt = ∫ t in Ioc 0 q.1, B (q.2 * t) / (t : ℂ) := by
      have h1 : ∫ t, Ψ (t, q) ∂μt =
          ∫ t in Ioc 0 L, (Iic q.1).indicator (fun t ↦ B (q.2 * t) / (t : ℂ)) t := by
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        simp only [Ψ]
        by_cases h : t ≤ q.1
        · rw [indicator_of_mem (show q.1 ∈ Ici t from h), one_mul,
            indicator_of_mem (show t ∈ Iic q.1 from h)]
        · rw [indicator_of_notMem (show q.1 ∉ Ici t from h), zero_mul,
            indicator_of_notMem (show t ∉ Iic q.1 from h)]
      have hset : Ioc 0 L ∩ Iic q.1 = Ioc 0 q.1 := by
        ext t
        simp only [mem_inter_iff, mem_Ioc, mem_Iic]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, h3.trans hq.1.2⟩, h3⟩
      rw [h1, setIntegral_indicator measurableSet_Iic, hset]
    rw [hsplit]
    exact (sLocalTrace_band_log_fubini f ξ q.1 q.2 ha hb).2
  refine ⟨?_, ?_, ?_⟩
  · exact hΨi.integral_prod_left.congr (ae_of_all _ fun t ↦ hA t)
  · refine (hΨi.integral_prod_right.const_mul (volume₁ : ℂ)).congr ?_
    filter_upwards [hq] with q hq'
    exact hB q hq'
  · calc (volume₁ : ℂ) * ∫ t in Ioc 0 L,
          (avgCutoff μρ t : ℂ) * (∫ b, bandIntegral f ξ (b * t) ∂μσ) / (t : ℂ)
        = (volume₁ : ℂ) * ∫ t, ∫ q, Ψ (t, q) ∂ν2 ∂μt := by
          congr 1
          exact integral_congr_ae (ae_of_all _ fun t ↦ (hA t).symm)
      _ = (volume₁ : ℂ) * ∫ q, ∫ t, Ψ (t, q) ∂μt ∂ν2 := by
          rw [integral_integral_swap (f := fun t q ↦ Ψ (t, q)) hΨi]
      _ = ∫ q, (volume₁ : ℂ) * ∫ t, Ψ (t, q) ∂μt ∂ν2 := (integral_const_mul _ _).symm
      _ = ∫ q, sLocalTraceSharpMass f ξ (q.1 * q.2) ∂ν2 := by
          refine integral_congr_ae ?_
          filter_upwards [hq] with q hq'
          exact hB q hq'

/-- Paper: (12.4.1.11)–(12.4.1.12), pp. 517–518.
The orbital mass of the unit `ξ` for the cutoff kernel whose spatial cutoff is
`x ↦ μρ([|x|, ∞))` and whose frequency cutoff is `u ↦ μσ([|u|, ∞))`: the integral of the kernel
on the skew diagonal over the part of norm at most `L` of the S-unit fundamental domain `D`,
against additive measure.
Deviation: The spatial cutoffs are averages of indicators against a measure, and the spatial
integral is restricted to norm at most `L`, where the spatial cutoff vanishes when `μρ` lives on
`(0, L]`. -/
def sLocalSmoothMass (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (D : Set Iₛ) (μρ μσ : Measure ℝ)
    (L : ℝ) : ℂ :=
  ∫ x in D ∩ {x : Iₛ | normS(x) ≤ L},
    sLocalTraceCutoffKernel f (fun x ↦ (avgCutoff μρ normS(x) : ℂ))
      (fun u ↦ (avgCutoff μσ modS(u) : ℂ)) (ξ.val * x) x.val ∂((νₛ).comap Units.val)

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518.
Reconstruction: the smoothed orbital mass is the average of the sharp orbital masses at the
radii `a b`, for `a` drawn from `μρ` and `b` from `μσ`. -/
theorem sLocalSmoothMass_eq_average (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) (μρ μσ : Measure ℝ) [IsProbabilityMeasure μρ]
    [IsProbabilityMeasure μσ] {a₀ L b₀ L' : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hρ : μρ (Icc a₀ L)ᶜ = 0) (hσ : μσ (Icc b₀ L')ᶜ = 0) :
    Integrable (fun q : ℝ × ℝ ↦ sLocalTraceSharpMass f ξ (q.1 * q.2)) (μρ.prod μσ) ∧
      sLocalSmoothMass f ξ D μρ μσ L =
        ∫ q, sLocalTraceSharpMass f ξ (q.1 * q.2) ∂(μρ.prod μσ) := by
  obtain ⟨hI, hS, hE⟩ := smoothRadial_eq_average f ξ μρ μσ ha₀ hb₀ hρ hσ
  refine ⟨hS, ?_⟩
  let h : ℝ → ℂ := fun t ↦ (avgCutoff μρ t : ℂ) * ∫ b, bandIntegral f ξ (b * t) ∂μσ
  have hhm : Measurable h := by
    refine (Complex.measurable_ofReal.comp (measurable_avgCutoff μρ)).mul ?_
    exact (StronglyMeasurable.integral_prod_right' (ν := μσ)
      ((measurable_bandIntegral f ξ).comp (measurable_snd.mul measurable_fst)).stronglyMeasurable
      ).measurable
  obtain ⟨hri, hre⟩ := sLocalTrace_fundamentalDomain_radial D hD L h hhm hI
  obtain ⟨-, hce⟩ := sLocalTrace_setIntegral_comap_density (D ∩ {x : Iₛ | normS(x) ≤ L})
    (fun x ↦ h normS(x)) hri
  rw [sLocalSmoothMass]
  calc ∫ x in D ∩ {x : Iₛ | normS(x) ≤ L},
        sLocalTraceCutoffKernel f (fun x ↦ (avgCutoff μρ normS(x) : ℂ))
          (fun u ↦ (avgCutoff μσ modS(u) : ℂ)) (ξ.val * x) x.val ∂((νₛ).comap Units.val)
      = ∫ x in D ∩ {x : Iₛ | normS(x) ≤ L}, (sLocalTraceMeasureFactor S : ℂ) *
          ((normS(x))⁻¹ : ℂ) * h normS(x) ∂((νₛ).comap Units.val) := by
        congr 1
        funext x
        exact smoothKernel_diag f ξ μρ μσ x
    _ = ∫ x in D ∩ {x : Iₛ | normS(x) ≤ L}, h normS(x) ∂μₛ := hce
    _ = (volume₁ : ℂ) * ∫ t in Ioc 0 L, h t / (t : ℂ) := hre
    _ = _ := hE

end Kernel

section LogWidth

/-- The logarithmic width `log (L / (L - ε)) + log (L' / (L' - ε))` of the radii `a b` with
`a ∈ [L - ε, L]` and `b ∈ [L' - ε, L']`. -/
def logWidth (L L' ε : ℝ) : ℝ := Real.log (L / (L - ε)) + Real.log (L' / (L' - ε))

theorem abs_log_mul_sub_le {L L' ε a b : ℝ} (hL : 0 < L - ε) (hL' : 0 < L' - ε)
    (ha : a ∈ Icc (L - ε) L) (hb : b ∈ Icc (L' - ε) L') :
    |Real.log (a * b) - Real.log (L * L')| ≤ logWidth L L' ε := by
  have ha0 : 0 < a := hL.trans_le ha.1
  have hb0 : 0 < b := hL'.trans_le hb.1
  have hL0 : 0 < L := hL.trans_le (ha.1.trans ha.2)
  have hL0' : 0 < L' := hL'.trans_le (hb.1.trans hb.2)
  rw [Real.log_mul ha0.ne' hb0.ne', Real.log_mul hL0.ne' hL0'.ne', logWidth,
    Real.log_div hL0.ne' hL.ne', Real.log_div hL0'.ne' hL'.ne']
  have h1 := Real.log_le_log ha0 ha.2
  have h2 := Real.log_le_log hL ha.1
  have h3 := Real.log_le_log hb0 hb.2
  have h4 := Real.log_le_log hL' hb.1
  rw [abs_le]
  constructor <;> linarith

theorem tendsto_log_div_sub {ι : Type*} {l : Filter ι} {L ε : ι → ℝ}
    (hL : ∀ᶠ i in l, 0 < L i) (h : Tendsto (fun i ↦ ε i / L i) l (𝓝 0)) :
    Tendsto (fun i ↦ Real.log (L i / (L i - ε i))) l (𝓝 0) := by
  have h1 : Tendsto (fun i ↦ (1 - ε i / L i)⁻¹) l (𝓝 1) := by
    have h' := (h.const_sub 1).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using h'
  have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [hL, h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with i hi hε
  simp only [Function.comp_apply]
  have hlt : ε i < L i := by rwa [div_lt_one hi] at hε
  have hne : L i - ε i ≠ 0 := by linarith
  congr 1
  field_simp

end LogWidth

section Asymptotic

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

local instance instSIdeleT2SmoothMassAsymp : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Paper: Theorem 12.4.1.1, p. 514, with the proof on pp. 516–519.
Reconstruction: take spatial cutoffs `x ↦ μρ([|x|, ∞))` and frequency cutoffs
`u ↦ μσ([|u|, ∞))`, where `μρ` and `μσ` are probability measures on `[L - ε, L]` and
`[L' - ε, L']`. Then the summed smoothed orbital masses, less `volume₁ φ(1) log (L L')`, tend to
`volume₁` times the sum of the local principal values as `L` and `L'` tend to infinity with
`ε / L → 0` and `ε / L' → 0`. Each smoothed mass is the average of the sharp masses at the
radii `a b` (`sLocalSmoothMass_eq_average`). The proof compares that average with the sharp
mass at `L L'` through the estimate per unit `sLocalTraceSharpMass_remainder_bound`.
Deviation: The cutoffs are nonincreasing functions of the absolute value, averages of sharp
indicators; every continuous nonincreasing cutoff with values in `[0, 1]`, equal to one up to
`L - ε` and vanishing beyond `L`, has this form. Definition 9.3.3.1 does not ask for
monotonicity. The masses are integrals over an S-unit fundamental domain, as in (12.4.1.11),
and are not written as diagonal integrals on the quotient. The width `ε` may stay fixed; the
paper takes `ε λ → 0`. -/
theorem sLocalSmoothMass_asymptotic (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μₛ)
    (μρ μσ : ℝ × ℝ → Measure ℝ) [∀ p, IsProbabilityMeasure (μρ p)]
    [∀ p, IsProbabilityMeasure (μσ p)] (ε : ℝ × ℝ → ℝ)
    (hρ : ∀ p, μρ p (Icc (p.1 - ε p) p.1)ᶜ = 0) (hσ : ∀ p, μσ p (Icc (p.2 - ε p) p.2)ᶜ = 0)
    (hε₁ : Tendsto (fun p ↦ ε p / p.1) (atTop ×ˢ atTop) (𝓝 0))
    (hε₂ : Tendsto (fun p ↦ ε p / p.2) (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ (∑' ξ : Hₛ, sLocalSmoothMass f ξ D (μρ p) (μσ p) p.1) -
          (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ))
        (atTop ×ˢ atTop) (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) := by
  obtain ⟨a, b, M, ha, hb, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic (F := F) (S := S) φ
    _hPic _hRamified _hOutside f _hLift
  refine ⟨a, b, ha, hb, ?_⟩
  obtain ⟨bd, hbd, hrem⟩ := sLocalTraceSharpMass_remainder_bound (F := F) (S := S) _hRamified f
  set V₁ : ℂ := (volume₁ : ℂ) with hV₁
  let κ (ξ : Hₛ) : ℂ := -∫ w in range (Units.val : Iₛ → Aₛ),
    fourierₛ (sLocalTraceEta f ξ) w * ((Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ
  let q (ξ : Hₛ) (R : ℝ) : ℂ :=
    sLocalTraceSharpMass f ξ R - V₁ * (f.val ξ.val * (Real.log R : ℂ) + κ ξ)
  have hq_bd (ξ : Hₛ) (R : ℝ) (hR : 1 ≤ R) : ‖q ξ R‖ ≤ bd ξ := (hrem ξ).1 R hR
  have hq_lim (ξ : Hₛ) : Tendsto (q ξ) atTop (𝓝 0) := (hrem ξ).2
  have hy : HasSum (fun ξ : Hₛ ↦ f.val ξ.val) (φ.val 1) := by
    have h := _hLift 1
    simp only [mul_one, map_one, QuotientGroup.mk_one] at h
    exact h
  have hys : Summable fun ξ : Hₛ ↦ ‖f.val ξ.val‖ := summable_norm_iff.mpr hy.summable
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  have hδ : Tendsto (fun p : ℝ × ℝ ↦ logWidth p.1 p.2 (ε p)) (atTop ×ˢ atTop) (𝓝 0) := by
    have h1 := tendsto_log_div_sub (l := atTop ×ˢ atTop) (L := fun p : ℝ × ℝ ↦ p.1)
      (tendsto_fst.eventually (eventually_gt_atTop 0)) hε₁
    have h2 := tendsto_log_div_sub (l := atTop ×ˢ atTop) (L := fun p : ℝ × ℝ ↦ p.2)
      (tendsto_snd.eventually (eventually_gt_atTop 0)) hε₂
    simpa [logWidth] using h1.add h2
  have hgood : ∀ᶠ p in atTop ×ˢ atTop,
      2 ≤ p.1 ∧ 2 ≤ p.2 ∧ ε p / p.1 ≤ 1 / 2 ∧ ε p / p.2 ≤ 1 / 2 := by
    filter_upwards [tendsto_fst.eventually (eventually_ge_atTop (2 : ℝ)),
      tendsto_snd.eventually (eventually_ge_atTop (2 : ℝ)),
      hε₁.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hε₂.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hhalf (p : ℝ × ℝ) (hp : 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ ε p / p.1 ≤ 1 / 2 ∧ ε p / p.2 ≤ 1 / 2) :
      p.1 / 2 ≤ p.1 - ε p ∧ p.2 / 2 ≤ p.2 - ε p := by
    obtain ⟨h1, h2, h3, h4⟩ := hp
    rw [div_le_iff₀ (by linarith)] at h3 h4
    constructor <;> linarith
  let Dξ (p : ℝ × ℝ) (ξ : Hₛ) : ℂ :=
    sLocalSmoothMass f ξ D (μρ p) (μσ p) p.1 - sLocalTraceSharpMass f ξ (p.1 * p.2)
  have hrae (p : ℝ × ℝ) : ∀ᵐ r ∂((μρ p).prod (μσ p)),
      r.1 ∈ Icc (p.1 - ε p) p.1 ∧ r.2 ∈ Icc (p.2 - ε p) p.2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μρ p) (ν := μσ p)).ae
      (ae_mem_of_prob_support (hρ p)),
      (Measure.quasiMeasurePreserving_snd (μ := μρ p) (ν := μσ p)).ae
      (ae_mem_of_prob_support (hσ p))] with r h1 h2
    exact ⟨h1, h2⟩
  -- The difference of a smoothed and a sharp mass is bounded by any bound of the integrand.
  have hDbound (p : ℝ × ℝ) (hp : 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ ε p / p.1 ≤ 1 / 2 ∧ ε p / p.2 ≤ 1 / 2)
      (ξ : Hₛ) (C : ℝ) (hC : ∀ r : ℝ × ℝ, r.1 ∈ Icc (p.1 - ε p) p.1 →
        r.2 ∈ Icc (p.2 - ε p) p.2 →
        ‖sLocalTraceSharpMass f ξ (r.1 * r.2) - sLocalTraceSharpMass f ξ (p.1 * p.2)‖ ≤ C) :
      ‖Dξ p ξ‖ ≤ C := by
    obtain ⟨hA, hB⟩ := hhalf p hp
    have ha₀ : 0 < p.1 - ε p := by linarith [hp.1]
    have hb₀ : 0 < p.2 - ε p := by linarith [hp.2.1]
    obtain ⟨hI, hE⟩ := sLocalSmoothMass_eq_average f ξ D hD (μρ p) (μσ p) ha₀ hb₀ (hρ p) (hσ p)
    have hform : Dξ p ξ = ∫ r, (sLocalTraceSharpMass f ξ (r.1 * r.2) -
        sLocalTraceSharpMass f ξ (p.1 * p.2)) ∂((μρ p).prod (μσ p)) := by
      rw [integral_sub hI (integrable_const _), integral_const, ← hE]
      simp [Dξ]
    rw [hform]
    have h := norm_integral_le_of_norm_le_const ((hrae p).mono fun r hr ↦ hC r hr.1 hr.2)
    simpa using h
  -- The integrand: logarithmic term and two remainders.
  have hpt (p : ℝ × ℝ) (hp : 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ ε p / p.1 ≤ 1 / 2 ∧ ε p / p.2 ≤ 1 / 2)
      (ξ : Hₛ) (r : ℝ × ℝ) (hr1 : r.1 ∈ Icc (p.1 - ε p) p.1) (hr2 : r.2 ∈ Icc (p.2 - ε p) p.2) :
      ‖sLocalTraceSharpMass f ξ (r.1 * r.2) - sLocalTraceSharpMass f ξ (p.1 * p.2)‖ ≤
        ‖V₁‖ * ‖f.val ξ.val‖ * logWidth p.1 p.2 (ε p) +
          (‖q ξ (r.1 * r.2)‖ + ‖q ξ (p.1 * p.2)‖) := by
    obtain ⟨hA, hB⟩ := hhalf p hp
    have ha₀ : 0 < p.1 - ε p := by linarith [hp.1]
    have hb₀ : 0 < p.2 - ε p := by linarith [hp.2.1]
    have hdecomp : sLocalTraceSharpMass f ξ (r.1 * r.2) - sLocalTraceSharpMass f ξ (p.1 * p.2) =
        V₁ * f.val ξ.val * ((Real.log (r.1 * r.2) - Real.log (p.1 * p.2) : ℝ) : ℂ) +
          (q ξ (r.1 * r.2) - q ξ (p.1 * p.2)) := by
      simp only [q]
      push_cast
      ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sub_le _ _))
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_log_mul_sub_le ha₀ hb₀ hr1 hr2
  have hprod (p : ℝ × ℝ) (hp : 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ ε p / p.1 ≤ 1 / 2 ∧ ε p / p.2 ≤ 1 / 2)
      (r : ℝ × ℝ) (hr1 : r.1 ∈ Icc (p.1 - ε p) p.1) (hr2 : r.2 ∈ Icc (p.2 - ε p) p.2) :
      p.1 * p.2 / 4 ≤ r.1 * r.2 := by
    obtain ⟨hA, hB⟩ := hhalf p hp
    have h1 : p.1 / 2 ≤ r.1 := hA.trans hr1.1
    have h2 : p.2 / 2 ≤ r.2 := hB.trans hr2.1
    have h0 : 0 ≤ p.1 / 2 := by linarith [hp.1]
    have h0' : 0 ≤ p.2 / 2 := by linarith [hp.2.1]
    nlinarith [mul_le_mul h1 h2 h0' (h0.trans h1)]
  -- A summable bound for the differences.
  let bound (ξ : Hₛ) : ℝ := ‖V₁‖ * ‖f.val ξ.val‖ + 2 * bd ξ
  have hbound_sum : Summable bound := (hys.mul_left _).add (hbd.mul_left 2)
  have hδ1 : ∀ᶠ p in atTop ×ˢ atTop, logWidth p.1 p.2 (ε p) ≤ 1 :=
    hδ.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbnd : ∀ᶠ p in atTop ×ˢ atTop, ∀ ξ : Hₛ, ‖Dξ p ξ‖ ≤ bound ξ := by
    filter_upwards [hgood, hδ1] with p hp hδp ξ
    refine hDbound p hp ξ _ fun r hr1 hr2 ↦ (hpt p hp ξ r hr1 hr2).trans ?_
    have hr : 1 ≤ r.1 * r.2 := by nlinarith [hprod p hp r hr1 hr2, hp.1, hp.2.1]
    have hpp : 1 ≤ p.1 * p.2 := by nlinarith [hp.1, hp.2.1]
    have h1 := hq_bd ξ _ hr
    have h2 := hq_bd ξ _ hpp
    have h3 : ‖V₁‖ * ‖f.val ξ.val‖ * logWidth p.1 p.2 (ε p) ≤ ‖V₁‖ * ‖f.val ξ.val‖ :=
      mul_le_of_le_one_right (by positivity) hδp
    simp only [bound]
    linarith
  -- Each difference tends to zero.
  have hlimξ (ξ : Hₛ) : Tendsto (fun p ↦ Dξ p ξ) (atTop ×ˢ atTop) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 ((hq_lim ξ).eventually
      (Metric.ball_mem_nhds 0 (by positivity : (0 : ℝ) < η / 3)))
    have hδ' : ∀ᶠ p in atTop ×ˢ atTop,
        ‖V₁‖ * ‖f.val ξ.val‖ * logWidth p.1 p.2 (ε p) < η / 3 := by
      have h := hδ.const_mul (‖V₁‖ * ‖f.val ξ.val‖)
      rw [mul_zero] at h
      exact h.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hgood, hδ', hp.eventually (eventually_ge_atTop (4 * max R₀ 1))]
      with p hp hδp hLL
    rw [dist_zero_right]
    have hqr (R : ℝ) (hR : R₀ ≤ R) : ‖q ξ R‖ < η / 3 := by
      have h := hR₀ R hR
      simpa [dist_zero_right] using h
    refine lt_of_le_of_lt (hDbound p hp ξ (‖V₁‖ * ‖f.val ξ.val‖ * logWidth p.1 p.2 (ε p) +
      (η / 3 + η / 3)) fun r hr1 hr2 ↦ (hpt p hp ξ r hr1 hr2).trans ?_) ?_
    · have hR1 : R₀ ≤ r.1 * r.2 := by
        have := hprod p hp r hr1 hr2
        have := le_max_left R₀ 1
        linarith
      have hR2 : R₀ ≤ p.1 * p.2 := by
        have := le_max_left R₀ 1
        have := le_max_right R₀ 1
        linarith
      have h1 := hqr _ hR1
      have h2 := hqr _ hR2
      linarith
    · linarith
  -- The sum of the differences tends to zero.
  have hsumD : Tendsto (fun p ↦ ∑' ξ, Dξ p ξ) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hbound_sum hlimξ hbnd
  have hfinal : ∀ᶠ p in atTop ×ˢ atTop,
      (M (p.1 * p.2) - V₁ * φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) + ∑' ξ, Dξ p ξ =
        (∑' ξ : Hₛ, sLocalSmoothMass f ξ D (μρ p) (μσ p) p.1) -
          V₁ * φ.val 1 * (Real.log (p.1 * p.2) : ℂ) := by
    filter_upwards [hp.eventually hsum, hbnd] with p hs hb
    have hDs : Summable (Dξ p) := hbound_sum.of_norm_bounded hb
    have hS : HasSum (fun ξ ↦ sLocalSmoothMass f ξ D (μρ p) (μσ p) p.1)
        (M (p.1 * p.2) + ∑' ξ, Dξ p ξ) := by
      have h := hs.add hDs.hasSum
      simpa [Dξ] using h
    rw [hS.tsum_eq]
    ring
  have h := (hlim.comp hp).add hsumD
  rw [add_zero] at h
  exact h.congr' hfinal

end Asymptotic

end RiemannMasullo.Isolated
