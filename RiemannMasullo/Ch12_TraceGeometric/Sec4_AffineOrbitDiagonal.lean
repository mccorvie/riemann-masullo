module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusOrbit
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Affine orbital integral of the raw annular diagonal -/

public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "A" => SAdeleRing F S
local notation "I" => (SAdeleRing F S)ˣ
local notation "H" => sProjectedDiagonal F S
local notation "J" => SIdeleQuotient F S
local notation "Q" => continuousSIdeleQuotientNorm F S
set_option quotPrecheck false in
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "νA" => sAdditiveTamagawaMeasure F S
local notation "ψ" => sAdeleStandardCharacter F S
local notation "modS(" z ")" => ((∏ w : InfinitePlace F, ‖(z : A).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(z : A).2 v‖)

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSAdeleMeasurableSpaceSec1
  instSIdeleLocallyCompactSec1

local instance instSIdeleT2AffineOrbitDiagonal : T2Space I := (sIdeleGroup_description F S).2.1

/-- Paper: Theorem 12.4.1.1, Step III, pp. 517–518.
The half-density quotient diagonal is integrable for the weighted measure.
Cancelling the Sobolev density gives the absolutely unfolded sum of
smooth affine orbital integrals at a fixed annulus.
Deviation: This computes the raw diagonal and retains the smooth cutoff
profiles in the orbital integrals. -/
theorem exists_sLocalTrace_fixedAnnulus_affineDiagonal_hasSum
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : BruhatCompactSupport I) (b : ℝ → ℂ) {Λ ερ εb Cb s : ℝ} {ρ : J → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ) (hs : 0 ≤ s)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let π (x : I) : J := QuotientGroup.mk x
    let N (q : J) : ℝ := (Q q).val
    let c : ℂ := sLocalTraceMeasureFactor S
    let K : I → A → ℂ := sLocalTraceCutoffKernel f
      (fun x ↦ (ρ (π x) : ℂ)) (fun z ↦ b (modS(z)))
    let d (ξ : H) (t : ℝ≥0ˣ) : ℂ := (ρ (π (τ t)) : ℂ) *
      ∫ w : A, b (modS(w) / (t.val : ℝ)) *
        tamagawaFourier νA ψ (sLocalTraceEta f 1) w *
        (ψ (w * (ξ.val.val - 1)) : ℂ) ∂νA
    ∃ κ : J → J → ℂ,
      (∀ x y : I, κ (π x) (π y) = ∑' ξ : H, K x (ξ.val * y).val) ∧
      let D (q : J) := (N q : ℂ) / c * κ q q
      let ℓ := logSIdeleQuotientNorm F S
      let ν := intervalSobolevMeasure μ ℓ 0 0 s
      let W (q : J) := intervalSobolevDensity 0 0 s (ℓ q)
      let Dν (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ q q / (c * (W q : ℂ))
      Integrable D μ ∧ Integrable Dν ν ∧
      HasSum (fun ξ : H ↦ ((sLocalNormOneQuotientMeasure F S univ).toReal : ℂ) *
        ∫ t, d ξ t ∂positiveRealHaar) (∫ q, Dν q ∂ν) := by
  classical
  intro π N c K d
  let η := sLocalNormOneQuotientMeasure F S
  let Z : Set J := {q | N q ∈ Icc Λ⁻¹ Λ}
  obtain ⟨hZ, κ, C, hC, hκ, _, hRep, _, _, hAll, _⟩ :=
    exists_sLocalTrace_halfDensityOrbitKernel_fixed_annulus_data (s := s) f b hρ
      hs hb hε hplateau hderiv
  have hZ' : IsCompact Z := hZ
  let : (μ : Measure J).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable (((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) :=
    Units.val_injective.countable
  let diag : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ →* I :=
    (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  have hDiag : H = diag.range := MonoidHom.map_range _ _
  let : Countable H := hDiag.symm ▸ diag.rangeRestrict_surjective.countable
  have hQc : Continuous (Q : J → ℝ≥0ˣ) := (Q).continuous
  have hN : Continuous N := NNReal.continuous_coe.comp (Units.continuous_val.comp hQc)
  have hNp (q : J) : 0 < N q := NNReal.coe_pos.mpr (Units.zero_lt (Q q))
  have hNx (x : I) : N (π x) = ((sIdeleNorm F S x).val : ℝ) :=
    congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (sIdeleQuotientNorm_mk F S x)
  have hc : c ≠ 0 := by
    change (sLocalTraceMeasureFactor S : ℂ) ≠ 0
    apply Complex.ofReal_ne_zero.mpr
    unfold sLocalTraceMeasureFactor
    refine ne_of_gt (Finset.prod_pos fun j _ ↦ ?_)
    have hj : 1 < (j.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm j
    exact div_pos (zero_lt_one.trans hj) (sub_pos.mpr hj)
  have hπτ (t : ℝ≥0ˣ) : Q (π (τ t)) = t :=
    (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  have hρrad (x : I) : ρ (π (τ (Q (π x)))) = ρ (π x) := by
    obtain ⟨profile, _, hρprof, _⟩ := hρ.profile
    rw [hρprof (π (τ (Q (π x)))), hρprof (π x)]
    change profile (((Q (π (τ (Q (π x))))).val : ℝ)) = profile ((Q (π x)).val : ℝ)
    rw [hπτ]
  let U (ξ : H) (q : J) := d ξ (Q q)
  have hTerm (ξ : H) (x : I) :
      U ξ (π x) = (N (π x) : ℂ) / c * K x (ξ.val * x).val := by
    have hdisp : (x⁻¹).val * (ξ.val * x).val = ξ.val.val := by
      rw [← Units.val_mul, mul_comm ξ.val x, inv_mul_cancel_left]
    have hscaled := sLocalTraceCutoffKernel_scaled_radial_fourier
      f (fun a ↦ (ρ (π a) : ℂ)) b x (ξ.val * x).val
    change K x (ξ.val * x).val = _ at hscaled
    change (ρ (π (τ (Q (π x)))) : ℂ) *
      (∫ w : A, b (modS(w) / N (π x)) * tamagawaFourier νA ψ (sLocalTraceEta f 1) w *
        (ψ (w * (ξ.val.val - 1)) : ℂ) ∂νA) = _
    rw [hρrad, hscaled, hdisp, hNx]
    have hx : (((sIdeleNorm F S x).val : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    field_simp [hc, hx]
    ring
  have hB (r : ℝ) (hr : 0 ≤ r) : ‖b r‖ ≤ Cb := by
    simpa only [iteratedDeriv_zero] using hderiv 0 (Nat.zero_le _) r hr
  have hKc : Continuous (fun p : I × I ↦
      sLocalTraceCutoffKernel f (fun _ ↦ 1) (fun z ↦ b (modS(z))) p.1 p.2.val) :=
    sLocalTraceCutoffKernel_continuous_radial f _ continuous_const b hb.continuous hB
  have hπc : Continuous π := QuotientGroup.continuous_mk
  have hdm (ξ : H) : Measurable (d ξ) := by
    have hPair : Continuous (fun t : ℝ≥0ˣ ↦ (τ t, ξ.val * τ t)) :=
      τ.continuous.prodMk (continuous_const.mul τ.continuous)
    have hdc : Measurable (fun t : ℝ≥0ˣ ↦ (((t.val : ℝ) : ℂ) / c) *
        (ρ (π (τ t)) : ℂ) *
        sLocalTraceCutoffKernel f (fun _ ↦ 1) (fun z ↦ b (modS(z)))
          (τ t) (ξ.val * τ t).val) :=
      (((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        Units.continuous_val)).measurable.div measurable_const).mul
        (Complex.measurable_ofReal.comp (hρ.measurable.comp (hπc.comp τ.continuous).measurable))).mul
        (hKc.comp hPair).measurable
    have heq : d ξ = fun t : ℝ≥0ˣ ↦ (((t.val : ℝ) : ℂ) / c) *
        (ρ (π (τ t)) : ℂ) *
        sLocalTraceCutoffKernel f (fun _ ↦ 1) (fun z ↦ b (modS(z)))
          (τ t) (ξ.val * τ t).val := by
      funext t
      have hNτ : N (π (τ t)) = (t.val : ℝ) :=
        congrArg (fun z : ℝ≥0ˣ ↦ (z.val : ℝ)) (hπτ t)
      simpa only [U, hπτ, hNτ, K, sLocalTraceCutoffKernel, one_mul, mul_assoc] using
        (hTerm ξ (τ t))
    rw [heq]
    exact hdc
  have hU (ξ : H) : Measurable (U ξ) := (hdm ξ).comp hQc.measurable
  let D (q : J) := (N q : ℂ) / c * κ q q
  have hpoint (q : J) : D q = ∑' ξ : H, U ξ q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change (N (π x) : ℂ) / c * κ (π x) (π x) = ∑' ξ : H, U ξ (π x)
    have hx : κ (π x) (π x) = ∑' ξ : H, K x (ξ.val * x).val := hRep x x
    rw [hx, ← tsum_mul_left]
    exact tsum_congr fun ξ ↦ (hTerm ξ x).symm
  let G (q : J) : ℝ :=
    (N q / ‖c‖) * (C * (N q ^ (-(1 / 4 : ℝ)) + (N q)⁻¹))
  let maj := Z.indicator G
  have hGc : Continuous G :=
    (hN.div_const _).mul (continuous_const.mul
      ((hN.rpow_const (fun q ↦ Or.inl (hNp q).ne')).add (hN.inv₀ (fun q ↦ (hNp q).ne'))))
  have hmaj (q : J) : Summable (fun ξ : H ↦ ‖U ξ q‖) ∧
      (∑' ξ : H, ‖U ξ q‖) ≤ maj q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    let a (ξ : H) := ‖K x (ξ.val * x).val‖
    have hEq (ξ : H) : ‖U ξ (π x)‖ = N (π x) / ‖c‖ * a ξ := by
      rw [hTerm, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (hNp _).le]
    have ha : Summable a := (hAll x x).1
    have hEqFn : (fun ξ : H ↦ ‖U ξ (π x)‖) = fun ξ ↦ N (π x) / ‖c‖ * a ξ :=
      funext hEq
    change Summable (fun ξ : H ↦ ‖U ξ (π x)‖) ∧
      (∑' ξ : H, ‖U ξ (π x)‖) ≤ maj (π x)
    refine ⟨hEqFn.symm ▸ ha.mul_left (N (π x) / ‖c‖), ?_⟩
    by_cases hx : π x ∈ Z
    · have hs (ht : N (π x) ≤ 1) :
          (∑' ξ, a ξ) ≤ C * N (π x) ^ (-(1 / 4 : ℝ)) := by
        rw [hNx x] at ht ⊢
        exact (hAll x x).2.1 ht
      have hl (ht : 1 ≤ N (π x)) : (∑' ξ, a ξ) ≤ C * (N (π x))⁻¹ := by
        rw [hNx x] at ht ⊢
        exact (hAll x x).2.2 ht
      rw [show maj (π x) = G (π x) from indicator_of_mem hx _]
      rw [hEqFn, tsum_mul_left]
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hNp _).le (norm_nonneg _))
      rcases le_total (N (π x)) 1 with ht | ht
      · exact (hs ht).trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (inv_nonneg.mpr (hNp _).le)) hC)
      · exact (hl ht).trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.rpow_nonneg (hNp _).le _)) hC)
    · have hρx : ρ (π x) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h ↦ hx (hρ.support_subset h)
      have hU0 (ξ : H) : U ξ (π x) = 0 := by
        simp only [hTerm, K, sLocalTraceCutoffKernel, hρx, Complex.ofReal_zero, zero_mul, mul_zero]
      have hZero : (fun ξ : H ↦ ‖U ξ (π x)‖) = (fun _ ↦ 0) :=
        funext fun ξ ↦ by rw [hU0, norm_zero]
      rw [hZero, tsum_zero, show maj (π x) = 0 from indicator_of_notMem hx _]
  have hmajI : Integrable maj μ :=
    (integrable_indicator_iff hZ'.measurableSet).mpr (hGc.continuousOn.integrableOn_compact hZ')
  have hmaj₀ : ∀ᵐ q ∂μ, 0 ≤ maj q := ae_of_all _ fun q ↦
    (tsum_nonneg fun ξ : H ↦ norm_nonneg (U ξ q)).trans (hmaj q).2
  have hfin : (∑' ξ, ∫⁻ q, ‖U ξ q‖ₑ ∂μ) < ⊤ := by
    rw [← lintegral_tsum (fun ξ ↦ (hU ξ).eNorm.aemeasurable)]
    calc
      _ ≤ ∫⁻ q, ENNReal.ofReal (maj q) ∂μ := by
        apply lintegral_mono
        intro q
        have he : (∑' ξ : H, ‖U ξ q‖ₑ) = ENNReal.ofReal (∑' ξ : H, ‖U ξ q‖) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun ξ : H ↦ norm_nonneg (U ξ q)) (hmaj q).1]
          exact tsum_congr fun ξ ↦ (ofReal_norm (U ξ q)).symm
        change (∑' ξ : H, ‖U ξ q‖ₑ) ≤ ENNReal.ofReal (maj q)
        rw [he]
        exact ENNReal.ofReal_le_ofReal (hmaj q).2
      _ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hmajI hmaj₀]
        exact ENNReal.ofReal_lt_top
  have hDm : Measurable D := ((Complex.continuous_ofReal.comp hN).measurable.div measurable_const).mul
    (hκ.comp measurable_diag)
  have hDI : Integrable D μ := hmajI.mono' hDm.aestronglyMeasurable <| ae_of_all _ fun q ↦ by
    rw [hpoint]
    exact (norm_tsum_le_tsum_norm (hmaj q).1).trans (hmaj q).2
  let P (p : J₁ × ℝ≥0ˣ) : J := p.1.val * π (τ p.2)
  have hP : Measurable P := ((continuous_subtype_val.comp continuous_fst).mul
    (hπc.comp (τ.continuous.comp continuous_snd))).measurable
  have hNP : (Q : J → ℝ≥0ˣ) ∘ P = Prod.snd := by
    funext p
    change sIdeleQuotientNorm F S (p.1.val * QuotientGroup.mk (τ p.2)) = p.2
    rw [map_mul, MonoidHom.mem_ker.mp p.1.property, one_mul, sIdeleQuotientNorm_mk, hτ]
  have hprod : (η.prod positiveRealHaar).map P = μ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  have hmap : (μ).map (Q : J → ℝ≥0ˣ) = (η univ) • positiveRealHaar := by
    rw [← hprod, Measure.map_map hQc.measurable hP, hNP, Measure.map_snd_prod]
  have hrad (ξ : H) : (∫ q, U ξ q ∂μ) = ((η univ).toReal : ℂ) *
      ∫ t, d ξ t ∂positiveRealHaar := by
    change (∫ q, d ξ (Q q) ∂μ) = _
    rw [← integral_map_of_stronglyMeasurable hQc.measurable (hdm ξ).stronglyMeasurable,
      hmap, integral_smul_measure, Complex.real_smul]
  let ℓ := logSIdeleQuotientNorm F S
  let ν := intervalSobolevMeasure μ ℓ 0 0 s
  let W (q : J) := intervalSobolevDensity 0 0 s (ℓ q)
  let Dν (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ q q / (c * (W q : ℂ))
  let density (q : J) := ENNReal.ofReal (W q)
  have hℓ : Continuous ℓ := hN.log (fun q ↦ (hNp q).ne')
  have hW₀ (q : J) : 0 < W q := by
    dsimp only [W, intervalSobolevDensity]
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hWc : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
    positivity
  have hDensityM : Measurable density := (hWc.comp hℓ).measurable.ennreal_ofReal
  have hDensityFin : ∀ᵐ q ∂μ, density q < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hCancel (q : J) : (density q).toReal • Dν q = D q := by
    rw [show (density q).toReal = W q from ENNReal.toReal_ofReal (hW₀ q).le, Complex.real_smul]
    dsimp only [Dν, D]
    rw [Real.sqrt_mul (hNp q).le, Real.mul_self_sqrt (hNp q).le]
    field_simp [hc, Complex.ofReal_ne_zero.mpr (hW₀ q).ne']
  have hDν : Integrable Dν ν := by
    change Integrable Dν ((μ).withDensity density)
    rw [integrable_withDensity_iff_integrable_smul' hDensityM hDensityFin]
    exact hDI.congr (ae_of_all _ fun q ↦ (hCancel q).symm)
  have hDensityIntegral : (∫ q, Dν q ∂ν) = ∫ q, D q ∂μ := by
    change (∫ q, Dν q ∂((μ).withDensity density)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hDensityM hDensityFin]
    exact integral_congr_ae (ae_of_all _ hCancel)
  have hsumU : Summable (fun ξ : H ↦ ∫ q, U ξ q ∂μ) := by
    apply Summable.of_norm
    apply (ENNReal.tsum_coe_ne_top_iff_summable_coe
      (f := fun ξ : H ↦ ‖∫ q, U ξ q ∂μ‖₊)).mp
    change (∑' ξ : H, ‖∫ q, U ξ q ∂μ‖ₑ) ≠ ⊤
    have hle : (∑' ξ : H, ‖∫ q, U ξ q ∂μ‖ₑ) ≤ ∑' ξ : H, ∫⁻ q, ‖U ξ q‖ₑ ∂μ :=
      tsum_le_tsum fun ξ ↦ eNorm_integral_le_lintegral_eNorm (U ξ)
    exact (hle.trans_lt hfin).ne
  have hHasSum : HasSum (fun ξ : H ↦ ∫ q, U ξ q ∂μ) (∫ q, Dν q ∂ν) := by
    have hEq : (∫ q, Dν q ∂ν) = ∑' ξ : H, ∫ q, U ξ q ∂μ := by
      calc
        (∫ q, Dν q ∂ν) = ∫ q, D q ∂μ := hDensityIntegral
        _ = ∫ q, ∑' ξ : H, U ξ q ∂μ := integral_congr_ae (ae_of_all _ hpoint)
        _ = ∑' ξ : H, ∫ q, U ξ q ∂μ :=
          integral_tsum (fun ξ ↦ (hU ξ).aestronglyMeasurable) hfin.ne
    rw [hEq]
    exact hsumU.hasSum
  exact ⟨κ, hRep, hDI, hDν, hHasSum.congr_fun fun ξ ↦ (hrad ξ).symm⟩

/-- Paper: Theorem 12.4.1.1, Step III, pp. 517–518.
The half-density quotient diagonal is integrable for the weighted measure.
Cancelling the Sobolev density gives the absolutely unfolded sum of
smooth affine orbital integrals at a fixed annulus.
Deviation: This computes the raw diagonal and retains the smooth cutoff
profiles in the orbital integrals. -/
theorem exists_sLocalTrace_fixedAnnulus_affineDiagonal_integral
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : BruhatCompactSupport I) (b : ℝ → ℂ) {Λ ερ εb Cb s : ℝ} {ρ : J → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ) (hs : 0 ≤ s)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let π (x : I) : J := QuotientGroup.mk x
    let N (q : J) : ℝ := (Q q).val
    let c : ℂ := sLocalTraceMeasureFactor S
    let K : I → A → ℂ := sLocalTraceCutoffKernel f
      (fun x ↦ (ρ (π x) : ℂ)) (fun z ↦ b (modS(z)))
    let d (ξ : H) (t : ℝ≥0ˣ) : ℂ := (ρ (π (τ t)) : ℂ) *
      ∫ w : A, b (modS(w) / (t.val : ℝ)) *
        tamagawaFourier νA ψ (sLocalTraceEta f 1) w *
        (ψ (w * (ξ.val.val - 1)) : ℂ) ∂νA
    ∃ κ : J → J → ℂ,
      (∀ x y : I, κ (π x) (π y) = ∑' ξ : H, K x (ξ.val * y).val) ∧
      let D (q : J) := (N q : ℂ) / c * κ q q
      let ℓ := logSIdeleQuotientNorm F S
      let ν := intervalSobolevMeasure μ ℓ 0 0 s
      let W (q : J) := intervalSobolevDensity 0 0 s (ℓ q)
      let Dν (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ q q / (c * (W q : ℂ))
      Integrable D μ ∧ Integrable Dν ν ∧
      (∫ q, Dν q ∂ν) = ((sLocalNormOneQuotientMeasure F S univ).toReal : ℂ) *
        ∑' ξ : H, ∫ t, d ξ t ∂positiveRealHaar := by
  intro π N c K d
  obtain ⟨κ, hRep, hD, hDν, hSum⟩ :=
    exists_sLocalTrace_fixedAnnulus_affineDiagonal_hasSum τ hτ f b hρ hs hb hε hplateau hderiv
  refine ⟨κ, hRep, hD, hDν, ?_⟩
  simpa only [tsum_mul_left] using hSum.tsum_eq.symm

end RiemannMasullo
