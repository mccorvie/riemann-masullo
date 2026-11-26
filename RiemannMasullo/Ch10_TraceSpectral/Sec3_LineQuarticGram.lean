module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_FractionalLineModel
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.ForMathlib.Analysis.Fourier.QuarticKernel
import Mathlib.MeasureTheory.Group.Integral
import RiemannMasullo.Ch11_ShellStructure.Sec2a

/-! # The actual order-four line jets and their local profiles

The Riesz representatives of retained value and first-derivative jets have
exponential-polynomial Mellin observations. Different angular characters are
orthogonal. The spectral projection lies in their closed span by the existing
common-kernel theorem. These identities retain the Tamagawa normalization and
prepare the finite-rank window argument for the ambient operator in #7404.
-/

@[expose] public noncomputable section
open MeasureTheory NumberField Set
open scoped InnerProductSpace NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽


local notation "μs" => intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-0) 0 4 true

local instance quarticLineGramCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

private theorem quarticLineGram_log_preserving : MeasurePreserving (logIdeleClassNorm F) μ𝔽
    (Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
  exact (orbitalJet_logNorm_measurePreserving (F := F)).smul_measure _

private theorem quarticLineGram_density :
    μs = (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal ((1 + (logIdeleClassNorm F g) ^ 2) ^ (-(4 : ℝ) / 2))) := by
  simp only [intervalSobolevMeasure, intervalSobolevDensity, neg_zero, mul_zero, zero_mul,
    Real.exp_zero, max_self, one_mul, ite_true]
  congr 1
  funext g
  rw [neg_div, Real.rpow_neg (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]

private theorem quarticLineGram_density_measurable :
    Measurable fun g : C𝔽 ↦ ENNReal.ofReal ((1 + (logIdeleClassNorm F g) ^ 2) ^ (-(4 : ℝ) / 2)) := by
  have hm := (quarticLineGram_log_preserving (F := F)).measurable
  fun_prop


local notation "W₄" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 4
local notation "R₄" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 4 true
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "hs₀" => (show (0 : ℝ) ≤ 4 by norm_num)
local notation "hs₁" => (show (1 : ℝ) < 4 by norm_num)
local notation "T₄" => (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-0) 0 4 hI hs₀).exists.choose
local notation "J(" χ ", " a ")" => SpectralStripJetIndex χ a 0 4
local notation "raw(" χ ", " j ")" => spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jetU(" χ ", " j ")" => (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀ j).toLp raw(χ, j)
local notation "Riesz(" v ")" => (InnerProductSpace.toDual ℂ W₄).symm ((T₄).symm (v))
local notation "E(" η ", " t ")" => fractionalLineWaveEval hs₁ η t

private theorem quartic_riesz_conj (x y : R₄) :
    ⟪Riesz(x), Riesz(y)⟫_ℂ = star ⟪x, y⟫_ℂ := by
  let U := (T₄).symm.trans (InnerProductSpace.toDual ℂ W₄).symm
  change ⟪U x, U y⟫_ℂ = star ⟪x, y⟫_ℂ
  have hre (v w : R₄) : (⟪U v, U w⟫_ℂ).re = (⟪v, w⟫_ℂ).re := by
    change RCLike.re (⟪U v, U w⟫_ℂ) = RCLike.re (⟪v, w⟫_ℂ)
    rw [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← U.map_add]
    simp only [U.norm_map]
  have hI' (v : R₄) : U (Complex.I • v) = -Complex.I • U v := by
    rw [U.map_smulₛₗ]
    rw [show (starRingEnd ℂ) Complex.I = -Complex.I from Complex.conj_I]
  apply Complex.ext
  · exact hre x y
  · have him := hre x (Complex.I • y)
    simp only [hI', inner_smul_right, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at him
    exact him

/-- Every order-four strip jet at width zero has real offset zero. -/
theorem spectralLineQuarticJet_re_zero
    {a : ℝ} (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (j : J(χ, a)) : j.val.2.1 = 0 := by
  have hj := j.property
  have hn : ¬ (-(0 : ℝ) < j.val.2.1 ∧ j.val.2.1 < 0) := by
    intro h; simp only [neg_zero] at h; linarith [h.1, h.2]
  simp only [spectralStripMultiplicity, ite_eq_right hn] at hj
  split_ifs at hj with hb
  · rcases hb with hb | hb <;> simpa using hb
  · omega

/-- The physical observation of a retained order-four line jet is its reciprocal Gram integral. -/
theorem spectralLineQuarticJet_riesz_observation_integral
    {a : ℝ} (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (j : J(χ, a)) (t : ℝ) :
    E(χ j.val.1, t) (Riesz(jetU(χ, j))) =
      (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) •
        ∫ x : ℝ, Complex.exp (↑((t - j.val.2.2.1) * x) * Complex.I) * (x : ℂ) ^ j.val.2.2.2 *
          ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) := by
  let v := spectralLineFractionalWave hs₁ (χ j.val.1) t
  have he : E(χ j.val.1, t) (Riesz(jetU(χ, j))) =
      star ⟪v, jetU(χ, j)⟫_ℂ := by
    simpa only [InnerProductSpace.toDual_symm_apply, fractionalLineWaveEval, v] using quartic_riesz_conj v jetU(χ, j)
  rw [he, L2.inner_def, Complex.star_def, ← integral_conj]
  have hraw (g : C𝔽) : star ⟪spectralZeroJet (χ j.val.1) 0 t 0 g, raw(χ, j) g⟫_ℂ =
      Complex.exp (↑((t - j.val.2.2.1) * logIdeleClassNorm F g) * Complex.I) *
        (logIdeleClassNorm F g : ℂ) ^ j.val.2.2.2 := by
    have hjet : raw(χ, j) g = spectralZeroJet (χ j.val.1) 0 j.val.2.2.1 0 g *
        (logIdeleClassNorm F g : ℂ) ^ j.val.2.2.2 := by
      simp only [spectralZeroJet, spectralLineQuarticJet_re_zero χ j, pow_zero, mul_one]
    rw [hjet, RCLike.inner_apply, starRingEnd_apply, star_mul, star_mul,
      star_pow, star_star]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [spectralZeroJet_line_phase, spectralZeroJet_line_phase]
    have hc : ((χ j.val.1 g * Circle.exp (t * logIdeleClassNorm F g) : Circle) : ℂ) *
        star ((χ j.val.1 g * Circle.exp (j.val.2.2.1 * logIdeleClassNorm F g) : Circle) : ℂ) =
        Complex.exp (↑((t - j.val.2.2.1) * logIdeleClassNorm F g) * Complex.I) := by
      rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
      have heq : (χ j.val.1 g * Circle.exp (t * logIdeleClassNorm F g)) *
          (χ j.val.1 g * Circle.exp (j.val.2.2.1 * logIdeleClassNorm F g))⁻¹ =
          Circle.exp ((t - j.val.2.2.1) * logIdeleClassNorm F g) := by
        rw [sub_mul, Circle.exp_sub, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
      rw [heq, Circle.coe_exp]
    calc _ = (((χ j.val.1 g * Circle.exp (t * logIdeleClassNorm F g) : Circle) : ℂ) *
        star ((χ j.val.1 g * Circle.exp (j.val.2.2.1 * logIdeleClassNorm F g) : Circle) : ℂ)) *
        (logIdeleClassNorm F g : ℂ) ^ j.val.2.2.2 := by simp only [Complex.star_def]; ring
         _ = _ := by rw [hc]
  calc
    _ = ∫ g, Complex.exp (↑((t - j.val.2.2.1) * logIdeleClassNorm F g) * Complex.I) *
        (logIdeleClassNorm F g : ℂ) ^ j.val.2.2.2 ∂μs := by
      apply integral_congr_ae
      filter_upwards [spectralLineFractionalWave_coeFn hs₁ (χ j.val.1) t,
        (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀ j).coeFn_toLp] with g hg hj
      change v g = _ at hg
      rw [hg, hj]
      exact hraw g
    _ = _ := by
      rw [quarticLineGram_density,
        integral_withDensity_eq_integral_toReal_smul quarticLineGram_density_measurable
          (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      have hweight (x : ℝ) : (1 + x ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + x ^ 2) ^ 2)⁻¹ := by
        norm_num [Real.rpow_neg, Real.rpow_two]
      simp only [hweight, ENNReal.toReal_ofReal (by positivity : 0 ≤ ((1 + (logIdeleClassNorm F _) ^ 2) ^ 2)⁻¹),
        Complex.real_smul]
      let f (x : ℝ) := Complex.exp (↑((t - j.val.2.2.1) * x) * Complex.I) * (x : ℂ) ^ j.val.2.2.2 *
        ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)
      calc
        _ = ∫ g, f (logIdeleClassNorm F g) ∂μ𝔽 := by
          apply integral_congr_ae (.of_forall fun g ↦ ?_)
          dsimp [f]
          ring
        _ = _ := by
          have hw : Continuous (fun x : ℝ ↦ ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.comp
              ((show Continuous (fun x : ℝ ↦ (1 + x ^ 2) ^ 2) by fun_prop).inv₀
                (fun x ↦ by positivity))
          have hf : Continuous f := by
            exact (by fun_prop : Continuous (fun x : ℝ ↦
              Complex.exp (↑((t - j.val.2.2.1) * x) * Complex.I) * (x : ℂ) ^ j.val.2.2.2)).mul hw
          have hlog := quarticLineGram_log_preserving (F := F)
          calc
            _ = ∫ x, f x ∂(Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
              rw [← hlog.map_eq, integral_map hlog.measurable.aemeasurable hf.aestronglyMeasurable]
            _ = _ := by rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]


private theorem quartic_jet_translate (η : PontryaginDual C𝔽) (b t : ℝ) (r : ℕ)
    (k : C₁) (g : C𝔽) :
    spectralZeroJet η b t r (k.val * g) = (η k.val : ℂ) * spectralZeroJet η b t r g := by
  have hN : ideleClassNorm F k.val = 1 := k.property
  have hL : logIdeleClassNorm F (k.val * g) = logIdeleClassNorm F g := by
    simp only [logIdeleClassNorm, map_mul, hN, one_mul]
  have hphase : ideleClassNormTwist η ((b : ℂ) + (t : ℂ) * Complex.I) k.val = (η k.val : ℂ) := by
    change (η k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I) = _
    rw [hN]
    simp
  simp only [spectralZeroJet, map_mul, hL, hphase, mul_assoc]

/-- A retained line jet has zero observation in every other angular character. -/
theorem spectralLineQuarticJet_riesz_observation_zero_of_angular_ne
    {a : ℝ} (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (j : J(χ, a)) (ω : PontryaginDual C₁) (hω : ω ≠ j.val.1) (t : ℝ) :
    E(χ ω, t) (Riesz(jetU(χ, j))) = 0 := by
  have hres (ξ : PontryaginDual C₁) (g : C₁) : χ ξ g.val = ξ g :=
    congrArg (fun η : PontryaginDual C₁ ↦ η g) (hχ ξ)
  obtain ⟨v, hv⟩ : ∃ v : C₁, χ ω v.val ≠ χ j.val.1 v.val := by
    by_contra hn
    push Not at hn
    apply hω
    ext g : 1
    simpa only [hres] using hn g
  let c : ℂ := (χ ω v.val : ℂ) * star (χ j.val.1 v.val : ℂ)
  have hc : c ≠ 1 := by
    intro h
    dsimp only [c] at h
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_one] at h
    have h' : χ ω v.val * (χ j.val.1 v.val)⁻¹ = 1 := Subtype.ext h
    exact hv (mul_inv_eq_one.mp h')
  let f (g : C𝔽) := (((1 + (logIdeleClassNorm F g) ^ 2) ^ (-(4 : ℝ) / 2) : ℝ) : ℂ) *
    star ⟪spectralZeroJet (χ ω) 0 t 0 g, raw(χ, j) g⟫_ℂ
  have he (g : C𝔽) : f (v.val * g) = c * f g := by
    have hL : logIdeleClassNorm F (v.val * g) = logIdeleClassNorm F g := by
      simp only [logIdeleClassNorm, map_mul, show ideleClassNorm F v.val = 1 from v.property, one_mul]
    dsimp only [f, c]
    rw [hL, quartic_jet_translate, quartic_jet_translate]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_mul, star_star]
    ring
  have hi : E(χ ω, t) (Riesz(jetU(χ, j))) = ∫ g, f g ∂μ𝔽 := by
    have h := quartic_riesz_conj (spectralLineFractionalWave hs₁ (χ ω) t) jetU(χ, j)
    rw [InnerProductSpace.toDual_symm_apply] at h
    change E(χ ω, t) (Riesz(jetU(χ, j))) = _ at h
    rw [h, L2.inner_def, Complex.star_def, ← integral_conj]
    calc
      _ = ∫ g, star ⟪spectralZeroJet (χ ω) 0 t 0 g, raw(χ, j) g⟫_ℂ ∂μs := by
        apply integral_congr_ae
        filter_upwards [spectralLineFractionalWave_coeFn hs₁ (χ ω) t,
          (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀ j).coeFn_toLp] with g hg hj
        rw [hg, hj]
        rfl
      _ = _ := by
        rw [quarticLineGram_density,
          integral_withDensity_eq_integral_toReal_smul quarticLineGram_density_measurable
            (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
        apply integral_congr_ae (.of_forall fun g ↦ ?_)
        rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  rw [hi]
  have hIntegral := integral_mul_left_eq_self (μ := μ𝔽) f v.val
  rw [funext he, integral_const_mul] at hIntegral
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
  rw [sub_mul, one_mul, hIntegral, sub_self]

/-- Every retained jet at Sobolev order four has order zero or one. -/
theorem spectralLineQuarticJet_order_le_one
    {a : ℝ} (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (j : J(χ, a)) : j.val.2.2.2 ≤ 1 := by
  have hj := j.property
  rw [spectralStripMultiplicity_boundary (le_refl (0 : ℝ)) (Or.inr (spectralLineQuarticJet_re_zero χ j))] at hj
  have h := ((lt_spectralBoundaryMultiplicity 4 _ _).mp hj).2
  have hh : (j.val.2.2.2 : ℝ) < 2 := by norm_num at h; linarith
  have : j.val.2.2.2 < 2 := by exact_mod_cast hh
  omega

/-- The zeroth retained jet has the quartic Bessel profile with the exact Haar scalar. -/
theorem spectralLineQuarticJet_riesz_observation_zero
    {a : ℝ} (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (j : J(χ, a)) (hj : j.val.2.2.2 = 0) (t : ℝ) :
    E(χ j.val.1, t) (Riesz(jetU(χ, j))) =
      ((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * (Real.pi / 2) : ℂ) *
        (((1 + |t - j.val.2.2.1|) * Real.exp (-|t - j.val.2.2.1|) : ℝ) : ℂ) := by
  rw [spectralLineQuarticJet_riesz_observation_integral, hj]
  simp only [pow_zero, mul_one]
  rw [integral_cexp_mul_inv_one_add_sq_sq, Complex.real_smul]
  push_cast
  ring

/-- Away from its center, the first retained jet has an exponential-linear profile. -/
theorem spectralLineQuarticJet_riesz_observation_one
    {a : ℝ} (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (j : J(χ, a)) (hj : j.val.2.2.2 = 1)
    (t : ℝ) (ht : t ≠ j.val.2.2.1) :
    E(χ j.val.1, t) (Riesz(jetU(χ, j))) =
      ((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * (Real.pi / 2) : ℂ) *
        (Complex.I * (t - j.val.2.2.1) * (Real.exp (-|t - j.val.2.2.1|) : ℂ)) := by
  rw [spectralLineQuarticJet_riesz_observation_integral, hj]
  simp only [pow_one]
  rw [integral_cexp_mul_id_mul_inv_one_add_sq_sq (sub_ne_zero.mpr ht), Complex.real_smul]
  push_cast
  ring

/-- The actual spectral projection takes values in the closed span of the retained Riesz jets. -/
theorem spectralLineQuartic_projection_mem_closedSpan
    (a : ℝ) (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (w : W₄) :
    spectralProjection (F := F) a (le_refl (0 : ℝ)) hs₀ w ∈
      (Submodule.span ℂ (range (fun j : J(χ, a) ↦ Riesz(jetU(χ, j))))).topologicalClosure := by
  let S := Submodule.span ℂ (range (fun j : J(χ, a) ↦ Riesz(jetU(χ, j))))
  let Θ := globalThetaSobolev F a hI hs₀
  have hp (j : J(χ, a)) (v : W₄) : ⟪Riesz(jetU(χ, j)), v⟫_ℂ =
      spectralSobolevPairing v jetU(χ, j) := by
    rw [InnerProductSpace.toDual_symm_apply]
    exact (spectralSobolevPairing_dual hI hs₀ ((T₄).symm jetU(χ, j)) v).2.trans
      (congrArg (spectralSobolevPairing v) ((T₄).apply_symm_apply _))
  have hΘ : Θ = S.orthogonal := by
    ext v
    rw [spectralStripJet_commonKernel χ hχ (le_refl (0 : ℝ)) hs₀ v]
    constructor
    · intro hv
      apply (S.mem_orthogonal' v).mpr
      have hle : S ≤ LinearMap.ker (innerSL ℂ v).toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact inner_eq_zero_symm.mpr ((hp j v).trans (hv j))
      exact fun u hu ↦ hle hu
    · intro hv j
      exact (hp j v).symm.trans ((S.mem_orthogonal v).mp hv _ (Submodule.subset_span (mem_range_self j)))
  have hw := Θ.orthogonal.starProjection_apply_mem w
  have hcl : Θ.orthogonal = S.topologicalClosure := by
    rw [hΘ, S.orthogonal_orthogonal_eq_closure]
  exact hcl ▸ hw

end RiemannMasullo.Isolated
