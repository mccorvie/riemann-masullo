module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_FractionalLineModel
public import RiemannMasullo.Ch09_HardySobolev.Sec3
@[expose] public noncomputable section
open Set Function Filter
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

variable {s : ℝ}
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "hs₀(" hs ")" => (show 0 ≤ s from by linarith [hs])
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 s
local notation "τ(" hs ")" => hardySobolevTranslation μ𝔽 m𝔽 (-0) 0 s hI hs₀(hs)

/-- The unrestricted Mellin probes are eigenfunctionals of every left translation. -/
theorem spectralLineWaveEval_translation (hs : 1 < s)
    (η : PontryaginDual C𝔽) (t : ℝ) (g : C𝔽) (u : W) :
    fractionalLineWaveEval hs η t (τ(hs) g u) =
      spectralZeroJet η 0 t 0 g * fractionalLineWaveEval hs η t u := by
  let J := spectralZeroJet (F := F) η 0 t 0
  have hJ (x y : C𝔽) : J (x * y) = J x * J y := by
    simp only [J, spectralZeroJet, pow_zero, mul_one, map_mul]
  rw [fractionalLineWaveEval_apply, fractionalLineWaveEval_apply]
  let f (y : C𝔽) := u (g⁻¹ * y) * J y
  calc
    _ = ∫ y, f y ∂μ𝔽 := integral_congr_ae
      ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-0) 0 s hI hs₀(hs) g u).mono
        fun y hy ↦ congrArg (· * J y) hy)
    _ = ∫ y, f (g * y) ∂μ𝔽 := (integral_mul_left_eq_self f g).symm
    _ = ∫ y, J g * (u y * J y) ∂μ𝔽 := integral_congr_ae (.of_forall fun y ↦ by
      simp only [f, inv_mul_cancel_left, hJ]; ring)
    _ = _ := integral_const_mul _ _

/-- A vectorwise integrated convolution multiplies every unrestricted Mellin
probe by its positive-character transform. -/
theorem spectralLineWaveEval_integratedAction (hs : 1 < s)
    (k : C𝔽 → ℂ) (A : W →L[ℂ] W)
    (hA : ∀ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ k g • τ(hs) g u) (A u))
    (η : PontryaginDual C𝔽) (t : ℝ) (u : W) :
    fractionalLineWaveEval hs η t (A u) =
      (∫ g, k g * spectralZeroJet η 0 t 0 g ∂μ𝔽) * fractionalLineWaveEval hs η t u := by
  let δ := fractionalLineWaveEval hs η t
  have hev : δ (A u) = ∫ g, δ (k g • τ(hs) g u) ∂μ𝔽 :=
    congrArg (fun z : PettisWeakCompletion W ↦
      (show Module.Dual ℂ (StrongDual ℂ W) from z) δ) (hA u).2
  rw [hev, ← integral_mul_const]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  rw [map_smul, spectralLineWaveEval_translation, smul_eq_mul, mul_assoc]

/-- The actual Schwartz–Bruhat action on the zero-width Sobolev space, together
with its unrestricted Fourier–Mellin multiplier formula. -/
theorem exists_spectralLineWaveAction (hs : 1 < s) :
    ∃ A : SchwartzBruhat C𝔽 →L[ℂ] (W →L[ℂ] W),
      (∀ φ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ g • τ(hs) g u) (A φ u)) ∧
      ∀ φ η t u, fractionalLineWaveEval hs η t (A φ u) =
        (∫ g, φ g * spectralZeroJet η 0 t 0 g ∂μ𝔽) * fractionalLineWaveEval hs η t u := by
  have hex : ∃ A : SchwartzBruhat C𝔽 →L[ℂ] (W →L[ℂ] W),
      ∀ φ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ g • τ(hs) g u) (A φ u) := by
    have hx (b : ℝ) (hb : b = 0) (hle : b ≤ 0) :
        ∃ A : SchwartzBruhat C𝔽 →L[ℂ]
          (CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) b 0 s →L[ℂ]
            CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) b 0 s),
          ∀ φ u, HasPettisIntegral (.positive μ𝔽)
            (fun g ↦ φ g • hardySobolevTranslation μ𝔽 m𝔽 b 0 s hle hs₀(hs) g u) (A φ u) := by
      subst b
      exact (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs₀(hs)).exists
    exact hx (-0) (neg_zero) hI
  obtain ⟨A, hA⟩ := hex
  exact ⟨A, hA, fun φ η t u ↦ spectralLineWaveEval_integratedAction hs φ (A φ) (hA φ) η t u⟩

end RiemannMasullo.Isolated
