module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.PhysicalRieszVector
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.HeckeJetGram
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.PhysicalWeakening
import Mathlib.Tactic

/-! Gram matrices and weak cardinal energies of the original quotient Riesz vectors. -/

@[expose] public noncomputable section
open MeasureTheory Filter Set Complex NumberField
open scoped InnerProductSpace ComplexConjugate ENNReal Matrix NumberField.AdeleRing

namespace RiemannMasullo.WeakCardinal

private theorem widthZero_density_mul (s t x : ℝ) :
    intervalSobolevDensity (-0) 0 t x * intervalSobolevDensity (-0) 0 (2*s-t) x =
      intervalSobolevDensity (-0) 0 s x ^ 2 := by
  simp only [intervalSobolevDensity,neg_zero,mul_zero,zero_mul,Real.exp_zero,max_self,one_mul,pow_two]
  have hpos : 0 < 1+x*x := by nlinarith [sq_nonneg x]
  rw [← Real.rpow_add hpos,← Real.rpow_add hpos]
  congr 1
  ring

private theorem conjugate_div_inner (u v : ℂ) {a b d : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hb : b*d=a^2) :
    (b:ℂ)*⟪conj u/(a:ℂ),conj v/(a:ℂ)⟫_ℂ = (↑d⁻¹:ℂ)*⟪v,u⟫_ℂ := by
  simp only [RCLike.inner_apply,map_div₀,starRingEnd_self_apply,Complex.conj_ofReal,Complex.ofReal_inv]
  have e : (b:ℂ)*(d:ℂ)=(a:ℂ)^2 := by exact_mod_cast hb
  field_simp [(Complex.ofReal_ne_zero.mpr ha.ne'),(Complex.ofReal_ne_zero.mpr hd.ne')]
  linear_combination (u*conj v)*e

section Native

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "log𝔽" => logIdeleClassNorm F
local notation "ρ(" s "," g ")" => intervalSobolevDensity (-0) 0 s (log𝔽 g)
local notation "μp(" s ")" => intervalSobolevMeasure μ𝔽 log𝔽 (-0) 0 s
local notation "μd(" s ")" => intervalSobolevMeasure μ𝔽 log𝔽 (-0) 0 s true
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 log𝔽 (-0) 0 s
local notation "hI" => (neg_nonpos.mpr (le_refl (0:ℝ))).trans (le_refl (0:ℝ))

private theorem nativeDensity_meas (s : ℝ) : Measurable (fun g : C𝔽 ↦ ρ(s,g)) := by
  have hlog : Measurable log𝔽 :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hc : Continuous (fun x : ℝ ↦ (1+x^2)^(s/2)) := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦ 1+x^2)).rpow_const (fun x ↦ Or.inl (by dsimp; positivity))
  simpa [intervalSobolevDensity,Function.comp_def] using hc.measurable.comp hlog

private theorem nativeDensity_pos (s : ℝ) (g : C𝔽) : 0 < ρ(s,g) := by
  simp only [intervalSobolevDensity,neg_zero,mul_zero,zero_mul,Real.exp_zero,max_self,one_mul]
  exact Real.rpow_pos_of_pos (by positivity) _

theorem widthZero_base_ac_sobolev (s : ℝ) : μ𝔽 ≪ μp(s) :=
  withDensity_absolutelyContinuous' (nativeDensity_meas s).ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (nativeDensity_pos s g)).ne')

theorem widthZero_base_ac_dual (s : ℝ) : μ𝔽 ≪ μd(s) :=
  withDensity_absolutelyContinuous' (nativeDensity_meas s).inv.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (nativeDensity_pos s g))).ne')

/-- An arbitrary pair of physical value-jet representatives with strong denominator
`ρ_s`, read at order `t`, gives the reciprocal Gram at order `2s−t`.
Conjugation swaps the two indices, and evenness restores their original order. -/
theorem physicalValueRiesz_inner_angularGram (s t : ℝ) (hd : 1 < 2*s-t)
    (η : PontryaginDual C𝔽) (u v : ℝ) (X Y : W(t))
    (hX : (X : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ conj (spectralZeroJet η 0 u 0 g)/(ρ(s,g):ℂ))
    (hY : (Y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ conj (spectralZeroJet η 0 v 0 g)/(ρ(s,g):ℂ)) :
    ⟪X,Y⟫_ℂ = (heckeJetGramScale F:ℂ)*gramMatrix ((2*s-t)/2) (fun x : ℝ ↦ x) u v := by
  let d := 2*s-t
  let J (r : ℝ) := nativeValueWave d hd η r
  have hJ (r : ℝ) : (J r : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet η 0 r 0 :=
    (widthZero_base_ac_dual (F := F) d).ae_eq (memLp_nativeValueWave hd η r).coeFn_toLp
  have heq : ⟪X,Y⟫_ℂ = ⟪J v,J u⟫_ℂ := by
    rw [L2.inner_def,L2.inner_def]
    change (∫ g, ⟪X g,Y g⟫_ℂ ∂(μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (ρ(t,g)))) =
      ∫ g, ⟪J v g,J u g⟫_ℂ ∂(μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (ρ(d,g))⁻¹)
    rw [integral_withDensity_eq_integral_toReal_smul (nativeDensity_meas t).ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul (μ := μ𝔽)
        (show Measurable (fun g : C𝔽 ↦ ENNReal.ofReal ((ρ(d,g))⁻¹)) from
          (nativeDensity_meas (F := F) d).inv.ennreal_ofReal)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hX,hY,hJ u,hJ v] with g hx hy hju hjv
    simp only [hx,hy,hju,hjv,ENNReal.toReal_ofReal (nativeDensity_pos t g).le,
      ENNReal.toReal_ofReal (inv_pos.mpr (nativeDensity_pos d g)).le,Complex.real_smul]
    exact conjugate_div_inner _ _ (nativeDensity_pos s g) (nativeDensity_pos d g)
      (widthZero_density_mul s t _)
  have hG := congrArg (fun G : Matrix ℝ ℝ ℂ ↦ G v u)
    (gram_nativeValueWave d hd η (fun x : ℝ ↦ x))
  change ⟪J v,J u⟫_ℂ = (heckeJetGramScale F:ℂ)*gramMatrix (d/2) (fun x : ℝ ↦ x) v u at hG
  rw [heq,hG,gramMatrix_apply_comm (d/2) (fun x : ℝ ↦ x) u v]

end Native
end RiemannMasullo.WeakCardinal
