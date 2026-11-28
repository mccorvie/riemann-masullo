module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_AffineOrbitDiagonal
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothMass
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The annular quotient diagonal as a difference of smoothed masses -/

public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "A" => SAdeleRing F S
local notation "I" => (SAdeleRing F S)ˣ
local notation "H" => sProjectedDiagonal F S
local notation "J" => SIdeleQuotient F S
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "μI" => sMultiplicativeTamagawaMeasure F S
local notation "νA" => sAdditiveTamagawaMeasure F S
local notation "ψ" => sAdeleStandardCharacter F S
local notation "modS(" z ")" => ((∏ w : InfinitePlace F, ‖(z : A).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(z : A).2 v‖)
set_option quotPrecheck false in
local notation "vol₁" => ((sLocalNormOneQuotientMeasure F S univ).toReal : ℂ)

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1
  instSAdeleMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleLocallyCompactSec1

local instance : T2Space I := (sIdeleGroup_description F S).2.1

private theorem positiveRealHaar_integral_radial_of_vanish_above
    (p : ℝ → ℂ) (hp : Measurable p) {L : ℝ} (hz : ∀ r, L < r → p r = 0)
    (hi : IntegrableOn (fun r ↦ p r / (r : ℂ)) (Ioc 0 L)) :
    Integrable (fun t : ℝ≥0ˣ ↦ p (t.val : ℝ)) positiveRealHaar ∧
      (∫ t : ℝ≥0ˣ, p (t.val : ℝ) ∂positiveRealHaar) =
        ∫ r in Ioc 0 L, p r / (r : ℂ) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let e (x : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hev (x : ℝ) : ((e x).val : ℝ) = Real.exp x :=
    Real.coe_toNNReal _ (Real.exp_pos x).le
  let g := (Iic L).indicator (fun r : ℝ ↦ p r / (r : ℂ))
  have hg : IntegrableOn g (Ioi 0) := by
    change Integrable ((Iic L).indicator fun r : ℝ ↦ p r / (r : ℂ))
      ((volume : Measure ℝ).restrict (Ioi 0))
    rw [integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
    exact hi
  have hexp (x : ℝ) : Real.exp x • g (Real.exp x) = p (Real.exp x) := by
    by_cases hx : Real.exp x ≤ L
    · rw [show g (Real.exp x) = p (Real.exp x) / (Real.exp x : ℂ) from indicator_of_mem hx _,
        Complex.real_smul, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne')]
    · rw [show g (Real.exp x) = 0 from indicator_of_notMem hx _, smul_zero,
        hz _ (lt_of_not_ge hx)]
  have hpm : Measurable (fun t : ℝ≥0ˣ ↦ p (t.val : ℝ)) :=
    hp.comp (NNReal.continuous_coe.comp Units.continuous_val).measurable
  constructor
  · change Integrable (fun t : ℝ≥0ˣ ↦ p (t.val : ℝ)) (Measure.map e volume)
    rw [integrable_map_measure hpm.aestronglyMeasurable he.aemeasurable]
    change Integrable (fun x : ℝ ↦ p ((e x).val : ℝ)) volume
    simp only [hev]
    simpa only [hexp] using (integrable_comp_exp g).mpr hg
  · change (∫ t : ℝ≥0ˣ, p (t.val : ℝ) ∂(Measure.map e volume)) = _
    rw [integral_map_of_stronglyMeasurable he hpm.stronglyMeasurable]
    simp only [hev]
    have h := integral_comp_exp g
    simp_rw [hexp] at h
    rw [h, show g = (Iic L).indicator (fun r : ℝ ↦ p r / (r : ℂ)) from rfl,
      setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

private def annularAffineFrequency (f : BruhatCompactSupport I) (ξ : H)
    (b : ℝ → ℂ) (t : ℝ≥0ˣ) : ℂ :=
  ∫ w : A, b (modS(w) / (t.val : ℝ)) *
    tamagawaFourier νA ψ (sLocalTraceEta f 1) w *
    (ψ (w * (ξ.val.val - 1)) : ℂ) ∂νA

private theorem avgCutoff_mul_annularAffineFrequency
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : BruhatCompactSupport I) (ξ : H) (σ γ : Measure ℝ)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure γ] (t : ℝ≥0ˣ) :
    (Isolated.avgCutoff σ (t.val : ℝ) : ℂ) *
      annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t =
    (Isolated.avgCutoff σ (t.val : ℝ) : ℂ) *
      ∫ u, Isolated.bandIntegral f ξ⁻¹ (u * (t.val : ℝ)) ∂γ := by
  let x := τ t
  have hx : ((sIdeleNorm F S x).val : ℝ) = (t.val : ℝ) :=
    congrArg (fun z : ℝ≥0ˣ ↦ (z.val : ℝ)) (hτ t)
  have hdisp : (x⁻¹).val * (ξ.val * x).val = ξ.val.val := by
    rw [← Units.val_mul, mul_comm ξ.val x, inv_mul_cancel_left]
  have hpair : (ξ⁻¹).val * (ξ.val * x) = x := by
    change ξ.val⁻¹ * (ξ.val * x) = x
    exact inv_mul_cancel_left _ _
  have hscaled := sLocalTraceCutoffKernel_scaled_radial_fourier f
    (fun z ↦ (Isolated.avgCutoff σ ((sIdeleNorm F S z).val : ℝ) : ℂ))
    (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) x (ξ.val * x).val
  rw [hdisp, hx] at hscaled
  have hsmooth := Isolated.smoothKernel_diag f ξ⁻¹ σ γ (ξ.val * x)
  rw [hpair, Isolated.normS_projectedDiagonal_mul, hx] at hsmooth
  let c : ℂ := sLocalTraceMeasureFactor S
  have hc : c ≠ 0 := by
    change (sLocalTraceMeasureFactor S : ℂ) ≠ 0
    apply Complex.ofReal_ne_zero.mpr
    unfold sLocalTraceMeasureFactor
    refine ne_of_gt (Finset.prod_pos fun j _ ↦ ?_)
    have hj : 1 < (j.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm j
    exact div_pos (zero_lt_one.trans hj) (sub_pos.mpr hj)
  have ht : ((t.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (NNReal.coe_pos.mpr (Units.zero_lt t)).ne'
  have h := hscaled.symm.trans hsmooth
  change ((Isolated.avgCutoff σ (t.val : ℝ) : ℂ) * c / ((t.val : ℝ) : ℂ)) *
      annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t =
    c * (((t.val : ℝ) : ℂ)⁻¹) * ((Isolated.avgCutoff σ (t.val : ℝ) : ℂ) *
      ∫ u, Isolated.bandIntegral f ξ⁻¹ (u * (t.val : ℝ)) ∂γ) at h
  apply mul_left_cancel₀ (div_ne_zero hc ht)
  calc
    _ = ((Isolated.avgCutoff σ (t.val : ℝ) : ℂ) * c / ((t.val : ℝ) : ℂ)) *
        annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t := by ring
    _ = _ := h
    _ = _ := by ring

private theorem smoothMass_eq_annularAffineProfile
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : BruhatCompactSupport I) (ξ : H) (D : Set I) (hD : IsFundamentalDomain H D μI)
    (σ γ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure γ]
    {a L c B : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hσ : σ (Icc a L)ᶜ = 0) (hγ : γ (Icc c B)ᶜ = 0) :
    let d (t : ℝ≥0ˣ) := (Isolated.avgCutoff σ (t.val : ℝ) : ℂ) *
      annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t
    Integrable d positiveRealHaar ∧
      vol₁ * (∫ t, d t ∂positiveRealHaar) = Isolated.sLocalSmoothMass f ξ⁻¹ D σ γ L := by
  intro d
  let p (r : ℝ) := (Isolated.avgCutoff σ r : ℂ) *
    ∫ u, Isolated.bandIntegral f ξ⁻¹ (u * r) ∂γ
  have hp : Measurable p := by
    refine (Complex.measurable_ofReal.comp (Isolated.measurable_avgCutoff σ)).mul ?_
    exact (StronglyMeasurable.integral_prod_right' (ν := γ)
      ((Isolated.measurable_bandIntegral f ξ⁻¹).comp
        (measurable_snd.mul measurable_fst)).stronglyMeasurable).measurable
  have hp0 (r : ℝ) (hr : L < r) : p r = 0 := by
    simp only [p, Isolated.avgCutoff_eq_zero σ hσ hr, Complex.ofReal_zero, zero_mul]
  obtain ⟨hi, _, hE⟩ :=
    Isolated.smoothRadial_eq_average f ξ⁻¹ σ γ ha hc hσ hγ
  obtain ⟨hpI, hpHaar⟩ := positiveRealHaar_integral_radial_of_vanish_above p hp hp0 hi
  have heq : d = fun t : ℝ≥0ˣ ↦ p (t.val : ℝ) :=
    funext (avgCutoff_mul_annularAffineFrequency τ hτ f ξ σ γ)
  constructor
  · rw [heq]
    exact hpI
  · rw [heq, hpHaar]
    exact hE.trans (Isolated.sLocalSmoothMass_eq_average f ξ⁻¹ D hD σ γ ha hc hσ hγ).2.symm

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518. The weighted raw diagonal
integrates to the sum of the upper smoothed masses minus the smoothed
spatial floor. Inversion of the S-unit index matches the skew diagonal.
Deviation: The cutoff profiles come from positive radius laws, and the
identity concerns the raw quotient diagonal. -/
theorem exists_sLocalTrace_fixedAnnulus_smoothMass_difference_hasSum
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : BruhatCompactSupport I) (D : Set I) (hD : IsFundamentalDomain H D μI)
    (σTop σFloor γ : Measure ℝ)
    [IsProbabilityMeasure σTop] [IsProbabilityMeasure σFloor] [IsProbabilityMeasure γ]
    {lTop L lFloor A₀ c B : ℝ} (hTop : 0 < lTop) (hFloor : 0 < lFloor) (hc : 0 < c)
    (hσTop : σTop (Icc lTop L)ᶜ = 0) (hσFloor : σFloor (Icc lFloor A₀)ᶜ = 0)
    (hγ : γ (Icc c B)ᶜ = 0)
    (b : ℝ → ℂ) {Λ ερ εb Cb s : ℝ} {ρ : J → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ) (hs : 0 ≤ s)
    (hρLaw : ∀ q : J, ρ q = Isolated.avgCutoff σTop ((Q q).val : ℝ) -
      Isolated.avgCutoff σFloor ((Q q).val : ℝ))
    (hbLaw : ∀ r : ℝ, 0 ≤ r → b r = (Isolated.avgCutoff γ r : ℂ))
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : J) : ℝ := (Q q).val
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    ∃ κ : J → J → ℂ,
      (∀ x y : I, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun x ↦ (ρ (QuotientGroup.mk x) : ℂ))
          (fun z ↦ b (modS(z))) x (ξ.val * y).val) ∧
      let diag (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ q q /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ q) : ℂ))
      Integrable diag ν ∧
      HasSum (fun ξ : H ↦ Isolated.sLocalSmoothMass f ξ D σTop γ L -
        Isolated.sLocalSmoothMass f ξ D σFloor γ A₀) (∫ q, diag q ∂ν) := by
  intro N ℓ ν
  obtain ⟨κ, hRep, _, hDiag, hAffineSum⟩ :=
    exists_sLocalTrace_fixedAnnulus_affineDiagonal_hasSum τ hτ f b hρ hs hb hε hplateau hderiv
  refine ⟨κ, hRep, hDiag, ?_⟩
  let d (ξ : H) (t : ℝ≥0ˣ) :=
    (ρ (QuotientGroup.mk (τ t)) : ℂ) * annularAffineFrequency f ξ b t
  let dTop (ξ : H) (t : ℝ≥0ˣ) :=
    (Isolated.avgCutoff σTop (t.val : ℝ) : ℂ) *
      annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t
  let dFloor (ξ : H) (t : ℝ≥0ˣ) :=
    (Isolated.avgCutoff σFloor (t.val : ℝ) : ℂ) *
      annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t
  let M (ξ : H) := Isolated.sLocalSmoothMass f ξ D σTop γ L -
    Isolated.sLocalSmoothMass f ξ D σFloor γ A₀
  have hterm (ξ : H) : vol₁ * (∫ t, d ξ t ∂positiveRealHaar) = M ξ⁻¹ := by
    obtain ⟨hTopI, hTopE⟩ := smoothMass_eq_annularAffineProfile τ hτ f ξ D hD
      σTop γ hTop hc hσTop hγ
    obtain ⟨hFloorI, hFloorE⟩ := smoothMass_eq_annularAffineProfile τ hτ f ξ D hD
      σFloor γ hFloor hc hσFloor hγ
    have heq : d ξ = fun t ↦ dTop ξ t - dFloor ξ t := by
      funext t
      have hn : Q (QuotientGroup.mk (τ t)) = t :=
        (sIdeleQuotientNorm_mk F S _).trans (hτ t)
      have hbEq : annularAffineFrequency f ξ b t =
          annularAffineFrequency f ξ (fun u ↦ (Isolated.avgCutoff γ u : ℂ)) t := by
        apply integral_congr_ae
        refine ae_of_all _ fun w ↦ ?_
        let phase := tamagawaFourier νA ψ (sLocalTraceEta f 1) w *
          (ψ (w * (ξ.val.val - 1)) : ℂ)
        have hProfile := hbLaw (modS(w) / (t.val : ℝ))
          (div_nonneg (by positivity) (NNReal.coe_nonneg _))
        simpa only [mul_assoc, phase] using congrArg (fun z : ℂ ↦ z * phase) hProfile
      simp only [d, dTop, dFloor, hρLaw, hn, Complex.ofReal_sub, hbEq, sub_mul]
    rw [heq, integral_sub hTopI hFloorI, mul_sub, hTopE, hFloorE]
  change HasSum M _
  apply ((Equiv.inv H).hasSum_iff (f := M)).mp
  exact hAffineSum.congr_fun fun ξ ↦ (hterm ξ).symm

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518. The weighted raw diagonal
integrates to the sum of the upper smoothed masses minus the smoothed
spatial floor. Inversion of the S-unit index matches the skew diagonal.
Deviation: The cutoff profiles come from positive radius laws, and the
identity concerns the raw quotient diagonal. -/
theorem exists_sLocalTrace_fixedAnnulus_smoothMass_difference
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : BruhatCompactSupport I) (D : Set I) (hD : IsFundamentalDomain H D μI)
    (σTop σFloor γ : Measure ℝ)
    [IsProbabilityMeasure σTop] [IsProbabilityMeasure σFloor] [IsProbabilityMeasure γ]
    {lTop L lFloor A₀ c B : ℝ} (hTop : 0 < lTop) (hFloor : 0 < lFloor) (hc : 0 < c)
    (hσTop : σTop (Icc lTop L)ᶜ = 0) (hσFloor : σFloor (Icc lFloor A₀)ᶜ = 0)
    (hγ : γ (Icc c B)ᶜ = 0)
    (b : ℝ → ℂ) {Λ ερ εb Cb s : ℝ} {ρ : J → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ) (hs : 0 ≤ s)
    (hρLaw : ∀ q : J, ρ q = Isolated.avgCutoff σTop ((Q q).val : ℝ) -
      Isolated.avgCutoff σFloor ((Q q).val : ℝ))
    (hbLaw : ∀ r : ℝ, 0 ≤ r → b r = (Isolated.avgCutoff γ r : ℂ))
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : J) : ℝ := (Q q).val
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    ∃ κ : J → J → ℂ,
      (∀ x y : I, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun x ↦ (ρ (QuotientGroup.mk x) : ℂ))
          (fun z ↦ b (modS(z))) x (ξ.val * y).val) ∧
      let diag (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ q q /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ q) : ℂ))
      Integrable diag ν ∧
      (∫ q, diag q ∂ν) = ∑' ξ : H,
        (Isolated.sLocalSmoothMass f ξ D σTop γ L -
          Isolated.sLocalSmoothMass f ξ D σFloor γ A₀) := by
  intro N ℓ ν
  obtain ⟨κ, hRep, hDiag, hSum⟩ :=
    exists_sLocalTrace_fixedAnnulus_smoothMass_difference_hasSum τ hτ f D hD σTop σFloor γ
      hTop hFloor hc hσTop hσFloor hγ b hρ hs hρLaw hbLaw hb hε hplateau hderiv
  exact ⟨κ, hRep, hDiag, hSum.tsum_eq.symm⟩

end RiemannMasullo
