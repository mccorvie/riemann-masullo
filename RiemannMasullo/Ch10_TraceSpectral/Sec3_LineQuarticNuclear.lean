module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuarticActions
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuarticCount
public import RiemannMasullo.AppC_LCTVS.Sec3a_SchwartzWindows
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
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


local notation "W₄" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 4
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "hs₀" => (show (0 : ℝ) ≤ 4 by norm_num)
local notation "hs₁" => (show (1 : ℝ) < 4 by norm_num)
local notation "τ" => hardySobolevTranslation μ𝔽 m𝔽 (-0) 0 4 hI hs₀
local notation "Pspec(" a ")" => spectralProjection (F := F) a (le_refl (0 : ℝ)) hs₀

/-- At zero width and Sobolev order four, convolution by a homogeneous Schwartz
kernel after the ambient spectral projection is nuclear. Compact frequency windows
have quadratic rank growth, and Schwartz cutoffs give summable nuclear tails. -/
theorem spectralLineQuartic_schwartz_isotype_nuclear
    (a : ℝ) (A : SchwartzBruhat C𝔽 →L[ℂ] (W₄ →L[ℂ] W₄))
    (hA : ∀ φ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ g • τ g u) (A φ u))
    (ω : Ω) (φ : SchwartzBruhat C𝔽)
    (hφ : ∀ (k : C₁) x, φ (k.val⁻¹ * x) = (ω k : ℂ) * φ x) :
    IsNuclearOperator ((A φ).comp Pspec(a)) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨P, hP, honto⟩ := exists_spectralLineWaveProfile χ hχ ω
  obtain ⟨p, rfl⟩ := honto φ hφ
  let L : 𝓢(ℝ, ℂ) →L[ℂ] (W₄ →L[ℂ] W₄) :=
    ((ContinuousLinearMap.compL ℂ W₄ W₄ W₄).flip Pspec(a)).comp (A.comp P)
  let T := L.restrictScalars ℝ
  obtain ⟨C, hC, hrank⟩ := spectralLineQuartic_window_rank_quadratic a χ hχ ω
  apply isNuclearOperator_schwartz_of_quadratic_window_rank T C hC ?_ p
  intro R hR q hq
  apply hrank R hR (A (P q)) (fun ζ t ↦ if ζ = ω then q t else 0)
  · intro ζ t u
    rw [spectralLineWaveEval_integratedAction hs₁ (P q) (A (P q)) (hA (P q)), hP]
  · intro ζ t ht
    by_cases hζ : ζ = ω
    · exact ⟨hζ, hq t (by simpa only [hζ, ite_true] using ht)⟩
    · simp only [hζ, ite_false, ne_eq, not_true_eq_false] at ht

/-- The nuclear homogeneous Schwartz operator has a unique ambient projective
kernel in the reciprocal and positive Sobolev spaces of order four. -/
theorem spectralLineQuartic_schwartz_isotype_projectiveKernel
    (a : ℝ) (A : SchwartzBruhat C𝔽 →L[ℂ] (W₄ →L[ℂ] W₄))
    (hA : ∀ φ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ g • τ g u) (A φ u))
    (ω : Ω) (φ : SchwartzBruhat C𝔽)
    (hφ : ∀ (k : C₁) x, φ (k.val⁻¹ * x) = (ω k : ℂ) * φ x) :
    ∃! K, sobolevProjectiveKernelOperator (F := F) (le_refl (0 : ℝ)) hs₀ K =
      (A φ).comp Pspec(a) :=
  (existsUnique_sobolevProjectiveKernel_iff_nuclear (le_refl (0 : ℝ)) hs₀ _).mpr
    (spectralLineQuartic_schwartz_isotype_nuclear a A hA ω φ hφ)

/-- Paper: Theorem 10.4.3.5(3), pp. 472–473.
Reconstruction: At zero width and order four, the actual compact-test convolution
followed on its input by the spectral projection is nuclear in each angular isotype. -/
theorem spectralLineQuartic_test_isotype_nuclear
    (a : ℝ) (ω : Ω) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) x, φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    IsNuclearOperator ((hardySobolevTestAction μ𝔽 m𝔽 (-0) 0 4 hI hs₀ φ).comp Pspec(a)) := by
  let hms := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let j := bruhatCompactSupportToModulatedExponentialDecay m𝔽 ({0} : Set ℝ) hm𝔽 hms
  obtain ⟨e, he⟩ := modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms 0
  let ψ := e (j φ)
  have hψ : (ψ : C𝔽 → ℂ) = φ.val := by
    exact (he (j φ)).trans ((modulationWeight_zero m𝔽 (j φ).val).trans
      (funext (bruhatCompactSupportToModulatedExponentialDecay_apply m𝔽 {0} hm𝔽 hms φ)))
  obtain ⟨A, hA, -⟩ := exists_spectralLineWaveAction (F := F) hs₁
  have hψhom : ∀ (k : C₁) x, ψ (k.val⁻¹ * x) = (ω k : ℂ) * ψ x := by
    simpa only [hψ] using hφ
  have hident : A ψ = hardySobolevTestAction μ𝔽 m𝔽 (-0) 0 4 hI hs₀ φ := by
    apply ContinuousLinearMap.ext
    intro u
    have hp : HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ.val g • τ g u) (A ψ u) := by
      simpa only [hψ] using hA ψ u
    exact hp.unique (bruhatRegularizedAction_apply μ𝔽 τ _ φ u)
  rw [← hident]
  exact spectralLineQuartic_schwartz_isotype_nuclear a A hA ω ψ hψhom

/-- Paper: Theorem 10.4.3.5(3), p. 473.
Reconstruction: The ambient projective kernel exists uniquely for every homogeneous
compact test at zero width and order four; no geometric rectangle convergence or
zero-spacing assumption is used. -/
theorem spectralLineQuartic_test_isotype_projectiveKernel
    (a : ℝ) (ω : Ω) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) x, φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    ∃! K, sobolevProjectiveKernelOperator (F := F) (le_refl (0 : ℝ)) hs₀ K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-0) 0 4 hI hs₀ φ).comp Pspec(a) :=
  (existsUnique_sobolevProjectiveKernel_iff_nuclear (le_refl (0 : ℝ)) hs₀ _).mpr
    (spectralLineQuartic_test_isotype_nuclear a ω φ hφ)

end RiemannMasullo.Isolated
