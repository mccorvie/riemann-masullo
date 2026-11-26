module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuarticWindows
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineWaveAction
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
@[expose] public noncomputable section
open Set Function Filter
open scoped SchwartzMap Classical
namespace RiemannMasullo.Isolated
open MeasureTheory NumberField
open scoped InnerProductSpace NNReal NumberField.AdeleRing
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Ω" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽


/-- A real Schwartz profile is the unrestricted Mellin symbol of an actual
Schwartz–Bruhat kernel in one norm-one character, and its symbol is zero in
all other characters. Every homogeneous Schwartz kernel is obtained this way. -/
theorem exists_spectralLineWaveProfile
    (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : Ω) :
    ∃ P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽,
      (∀ p ζ t, (∫ g, P p g * spectralZeroJet (χ ζ) 0 t 0 g ∂μ𝔽) =
        if ζ = ω then p t else 0) ∧
      ∀ v : SchwartzBruhat C𝔽,
        (∀ (k : C₁) x, v (k.val⁻¹ * x) = (ω k : ℂ) * v x) → ∃ p, P p = v := by
  classical
  have hres (ζ : Ω) (k : C₁) : χ ζ k.val = ζ k :=
    congrArg (fun η : PontryaginDual C₁ ↦ η k) (hχ ζ)
  obtain ⟨e, he⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let Ψ (ζ : Ω) (t : ℝ) : PontryaginDual C𝔽 := χ ζ * (e (Multiplicative.ofAdd t)).val
  have hΨ (ζ : Ω) (t : ℝ) (g : C𝔽) : (Ψ ζ t g : ℂ) = spectralZeroJet (χ ζ) 0 t 0 g := by
    rw [spectralZeroJet_line_phase]
    change ((χ ζ g * (e (Multiplicative.ofAdd t)).val g : Circle) : ℂ) = _
    rw [he]
    rfl
  have hΨres (ζ : Ω) (t : ℝ) (k : C₁) : Ψ ζ t k.val = ζ k := by
    change χ ζ k.val * (e (Multiplicative.ofAdd t)).val k.val = _
    rw [he, hres, show m𝔽 k.val = 1 from k.property]
    simp
  obtain ⟨P, γ, hγ, hF, hoff, -, honto⟩ := exists_schwartzBruhat_mellinFrequencyChart m𝔽 hm𝔽
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1 μ𝔽 (χ ω)
  have hchart (t : ℝ) : (Ψ ω t)⁻¹ = γ t := by
    ext g : 1
    change (χ ω g * (e (Multiplicative.ofAdd t)).val g)⁻¹ = γ t g
    rw [he, hγ, mul_inv]
    simp only [neg_mul, Circle.exp_neg]
  have hγres (t : ℝ) (k : C₁) : γ t k.val = (ω k)⁻¹ := by
    rw [← hchart]
    exact congrArg Inv.inv (hΨres ω t k)
  have htransform (p : 𝓢(ℝ, ℂ)) (ζ : Ω) (t : ℝ) :
      (∫ g, P p g * spectralZeroJet (χ ζ) 0 t 0 g ∂μ𝔽) = lcaFourier μ𝔽 (P p) (Ψ ζ t)⁻¹ := by
    rw [lcaFourier]
    apply integral_congr_ae (.of_forall fun g ↦ ?_)
    change P p g * spectralZeroJet (χ ζ) 0 t 0 g =
      P p g * star (((Ψ ζ t g)⁻¹ : Circle) : ℂ)
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, hΨ]
  refine ⟨P, ?_, ?_⟩
  · intro p ζ t
    rw [htransform]
    by_cases hζ : ζ = ω
    · simpa only [hζ, ite_true, hchart] using hF p t
    · rw [ite_eq_right hζ]
      apply hoff p _
      rintro ⟨u, hu⟩
      apply hζ
      ext k : 1
      have hh := congrArg (fun η : PontryaginDual C𝔽 ↦ η k.val) hu
      change γ u k.val = (Ψ ζ t k.val)⁻¹ at hh
      rw [hγres, hΨres] at hh
      exact (inv_injective hh).symm
  · intro v hv
    exact honto v (fun k x ↦ by simpa only [hres] using hv k x)

local notation "W₄" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 4
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "hs₀" => (show (0 : ℝ) ≤ 4 by norm_num)
local notation "hs₁" => (show (1 : ℝ) < 4 by norm_num)
local notation "τ" => hardySobolevTranslation μ𝔽 m𝔽 (-0) 0 4 hI hs₀
local notation "Pspec(" a ")" => spectralProjection (F := F) a (le_refl (0 : ℝ)) hs₀

/-- Paper: Theorem 10.4.3.5(3), pp. 472–473, and (12.5.1.4), p. 520.
At zero width and Sobolev order four, convolution by every homogeneous
Schwartz–Bruhat kernel is compact after the ambient spectral projection.
Reconstruction: Compact frequency profiles have finite rank by the four
exterior Bessel modes; density in the Schwartz topology gives compactness. -/
theorem spectralLineQuartic_schwartz_isotype_compact
    (a : ℝ) (A : SchwartzBruhat C𝔽 →L[ℂ] (W₄ →L[ℂ] W₄))
    (hA : ∀ φ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ g • τ g u) (A φ u))
    (ω : Ω) (φ : SchwartzBruhat C𝔽)
    (hφ : ∀ (k : C₁) x, φ (k.val⁻¹ * x) = (ω k : ℂ) * φ x) :
    IsCompactOperator ((A φ).comp Pspec(a)) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨P, hP, honto⟩ := exists_spectralLineWaveProfile χ hχ ω
  obtain ⟨p, rfl⟩ := honto φ hφ
  let B (p : 𝓢(ℝ, ℂ)) : W₄ →L[ℂ] W₄ := (A (P p)).comp Pspec(a)
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hclosed : IsClosed {p : 𝓢(ℝ, ℂ) | IsCompactOperator (B p)} :=
    isClosed_setOfPred_isCompactOperator.preimage hB
  apply (closure_minimal (t := {p : 𝓢(ℝ, ℂ) | IsCompactOperator (B p)}) ?_ hclosed)
    (SchwartzMap.dense_hasCompactSupport p)
  intro q hq
  obtain ⟨l, hl⟩ := hq.bddBelow
  obtain ⟨r, hr⟩ := hq.bddAbove
  have hobs (ζ : Ω) (t : ℝ) (u : W₄) :
      fractionalLineWaveEval hs₁ (χ ζ) t (A (P q) u) =
        (if ζ = ω then q t else 0) * fractionalLineWaveEval hs₁ (χ ζ) t u := by
    rw [spectralLineWaveEval_integratedAction hs₁ (P q) (A (P q)) (hA (P q)), hP]
  have hsupp : ∀ ζ t, (if ζ = ω then q t else 0) ≠ 0 → ζ = ω ∧ t ∈ Ioo (l - 1) (r + 1) := by
    intro ζ t ht
    by_cases hζ : ζ = ω
    · have htq : q t ≠ 0 := by simpa only [hζ, ite_true] using ht
      have hts : t ∈ tsupport (q : ℝ → ℂ) := subset_tsupport _ htq
      exact ⟨hζ, by linarith [hl hts], by linarith [hr hts]⟩
    · simp only [hζ, ite_false, ne_eq, not_true_eq_false] at ht
  have hfin := (spectralLineQuartic_window_finiteRank a χ hχ (A (P q))
    (fun ζ t ↦ if ζ = ω then q t else 0) ω (l - 1) (r + 1) hobs hsupp).1
  let V := (B q).toLinearMap.range
  let : FiniteDimensional ℂ V := hfin
  have : ProperSpace V := FiniteDimensional.proper_rclike ℂ V
  let T : W₄ →L[ℂ] V := (B q).codRestrict V (fun u ↦ LinearMap.mem_range_self _ u)
  exact (isCompactOperator_of_locallyCompactSpace_dom T).continuous_comp continuous_subtype_val

end RiemannMasullo.Isolated
