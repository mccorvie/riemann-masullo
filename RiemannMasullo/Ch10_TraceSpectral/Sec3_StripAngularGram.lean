module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import Mathlib.MeasureTheory.Group.Integral

/-! # Orthogonality of strip jets in distinct angular characters

This extends the norm-one translation argument in `Sec3_LineGram` to arbitrary
strip width and every retained jet order.
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
local notation "l𝔽" => logIdeleClassNorm F
local notation "ν(" α ", " s ")" => intervalSobolevMeasure μ𝔽 l𝔽 (-α) α s true
local notation "raw(" χ ", " j ")" => spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- Multiplication by a norm-one element only changes the angular phase of any jet. -/
private theorem stripAngular_jet_translate (η : PontryaginDual C𝔽) (b t : ℝ) (r : ℕ)
    (k : C₁) (g : C𝔽) :
    spectralZeroJet η b t r (k.val * g) = (η k.val : ℂ) * spectralZeroJet η b t r g := by
  have hN : ideleClassNorm F k.val = 1 := k.property
  have hL : l𝔽 (k.val * g) = l𝔽 g := by
    simp only [logIdeleClassNorm, map_mul, hN, one_mul]
  have hphase : ideleClassNormTwist η ((b : ℂ) + (t : ℂ) * Complex.I) k.val = (η k.val : ℂ) := by
    change (η k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I) = _
    rw [hN]
    simp
  simp only [spectralZeroJet, map_mul, hL, hphase, mul_assoc]

/-- Retained strip jets in different norm-one characters are orthogonal in the
reciprocal-weight Hilbert space, at every width and every nonnegative Sobolev order. -/
theorem spectralStripJet_inner_eq_zero_of_angular_ne
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (j k : SpectralStripJetIndex χ a α s) (hjk : j.val.1 ≠ k.val.1) :
    ⟪(spectralStripJet_memLp χ hα hs j).toLp raw(χ, j),
      (spectralStripJet_memLp χ hα hs k).toLp raw(χ, k)⟫_ℂ = 0 := by
  classical
  have hres (ω : PontryaginDual C₁) (g : C₁) : χ ω g.val = ω g :=
    congrArg (fun η : PontryaginDual C₁ ↦ η g) (hχ ω)
  obtain ⟨v, hv⟩ : ∃ v : C₁, χ j.val.1 v.val ≠ χ k.val.1 v.val := by
    by_contra hn
    push Not at hn
    apply hjk
    ext g : 1
    simpa only [hres] using hn g
  let w (g : C𝔽) := (intervalSobolevDensity (-α) α s (l𝔽 g))⁻¹
  have hw : Measurable w := by
    have hD : Measurable (intervalSobolevDensity (-α) α s) := by
      unfold intervalSobolevDensity
      fun_prop
    have hlog : Continuous l𝔽 :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
        (fun g ↦ NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    exact (hD.comp hlog.measurable).inv
  have hw₀ (g : C𝔽) : 0 ≤ w g := by
    dsimp [w, intervalSobolevDensity]
    positivity
  let c : ℂ := (χ k.val.1 v.val : ℂ) * star (χ j.val.1 v.val : ℂ)
  let f (g : C𝔽) := (w g : ℂ) * ⟪raw(χ, j) g, raw(χ, k) g⟫_ℂ
  have hc : c ≠ 1 := by
    intro h
    dsimp only [c] at h
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_one] at h
    have h' : χ k.val.1 v.val * (χ j.val.1 v.val)⁻¹ = 1 := Subtype.ext h
    exact hv (mul_inv_eq_one.mp h').symm
  have he (g : C𝔽) : f (v.val * g) = c * f g := by
    have hL : l𝔽 (v.val * g) = l𝔽 g := by
      simp only [logIdeleClassNorm, map_mul, show ideleClassNorm F v.val = 1 from v.property, one_mul]
    dsimp only [f, w, c]
    rw [hL, stripAngular_jet_translate, stripAngular_jet_translate]
    simp only [RCLike.inner_apply, map_mul, starRingEnd_apply]
    ring
  have hi : ⟪(spectralStripJet_memLp χ hα hs j).toLp raw(χ, j),
      (spectralStripJet_memLp χ hα hs k).toLp raw(χ, k)⟫_ℂ = ∫ g, f g ∂μ𝔽 := by
    rw [L2.inner_def]
    calc
      _ = ∫ g, ⟪raw(χ, j) g, raw(χ, k) g⟫_ℂ ∂ν(α, s) := by
        apply integral_congr_ae
        filter_upwards [(spectralStripJet_memLp χ hα hs j).coeFn_toLp,
          (spectralStripJet_memLp χ hα hs k).coeFn_toLp] with g hj hk
        rw [hj, hk]
      _ = _ := by
        change (∫ g, ⟪raw(χ, j) g, raw(χ, k) g⟫_ℂ ∂(μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g))) = _
        rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
        apply integral_congr_ae (.of_forall fun g ↦ ?_)
        rw [ENNReal.toReal_ofReal (hw₀ g), Complex.real_smul]
  rw [hi]
  have hI := integral_mul_left_eq_self (μ := μ𝔽) f v.val
  rw [funext he, integral_const_mul] at hI
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
  rw [sub_mul, one_mul, hI, sub_self]

end RiemannMasullo.Isolated
