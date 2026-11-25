module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.WeakNormLimit
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FiniteHeckeWindow
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.PhysicalWeakEnergy
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.RadiusSixInterpolation
import Mathlib.Analysis.Matrix.PosDef

/-! # A radius-six estimate for the actual Hecke quotient cardinal

The native reciprocal squared-density and the Haar factor enter through finite Gram identities.
The local ordinate window contains both endpoints and every distinct retained zero of this
character. The full weak norm is measured on the orthogonal representative of the actual
quotient. The finite-window argument and its numerical calibration are recorded in #7406,
issue comment 7163925073, following k-ieren’s first-moment identity in Proposition 3.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped ENNReal Matrix NumberField.AdeleRing

namespace RiemannMasullo.WeakCardinal

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "hI" => (neg_nonpos.mpr (le_refl (0:ℝ))).trans (le_refl (0:ℝ))
local notation "Q(" a "," hs ")" => spectralSobolevQuotient F a hI (zero_le_one.trans (hs).le)
local notation "J(" χ "," a "," s ")" => SpectralStripJetIndex χ a 0 s
local notation "D(" a "," hs ")" => spectralSobolevDualEmbedding F a hI (zero_le_one.trans (hs).le)
local notation "nv(" χ "," hs "," i ")" =>
  (spectralStripJet_memLp χ (le_refl (0:ℝ)) (zero_le_one.trans (hs).le) i).toLp
    (spectralZeroJet (F := F) (χ (i).val.1) (i).val.2.1 (i).val.2.2.1 (i).val.2.2.2)
local notation "weakMap(" a "," s "," hs ")" => spectralWeakRieszReadout F a s hs

/-- The numerical local energy at a genuine zero, computed from one inverse column and a
second positive Gram on the entire closed radius-six same-character window. -/
def spectralWeakCardinalForm (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (hs₃ : s ≤ 3) (j : J(χ,a,s)) : ℝ := by
  classical
  let E := spectralCardinalWindow χ hs₃ j
  exact finiteSiteWeakForm (s/2) (fun i : J(χ,a,s) ↦ i.val.2.2.1) E j
    ((mem_spectralCardinalWindow χ hs₃ j j).2 ⟨rfl,by simp⟩)

/-- Every actual local Gram form is strictly positive, even when other retained ordinates
are arbitrarily close to the chosen one. -/
theorem spectralWeakCardinalForm_pos
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (hs₃ : s ≤ 3)
    (j : J(χ,a,s)) : 0 < spectralWeakCardinalForm χ hs₃ j := by
  classical
  let S := spectralCardinalWindow χ hs₃ j
  have hj := (mem_spectralCardinalWindow χ hs₃ j j).2 ⟨rfl, by simp⟩
  let j₀ : S := ⟨j, hj⟩
  let t (i : S) : ℝ := i.val.val.2.2.1
  have hm (i : S) := ((mem_spectralCardinalWindow χ hs₃ i.val j).1 i.property).1
  have hi : Function.Injective t :=
    spectralStripJet_ordinate_injective hs₃ S (fun i k ↦ (hm i).trans (hm k).symm)
  have hθ : 1/2 < s/2 := by linarith
  let c (i : S) := (gramMatrix (s/2) t)⁻¹ i j₀
  have hc : c ≠ 0 := by
    intro h
    have hval : (gramMatrix (s/2) t *ᵥ c) j₀ = 1 := by
      simpa using gramMatrix_mulVec_inverse_column (s/2) hθ hi j₀ j₀
    simp [h] at hval
  change 0 < finiteSiteWeakForm (s/2) (fun i : J(χ,a,s) ↦ i.val.2.2.1) S j hj
  rw [finiteSiteWeakForm_eq]
  exact (gramMatrix_posDef (s/2+1) (by linarith) hi).re_dotProduct_pos hc

/-- The squared native weak energy of any finite single-character interpolant, with the
chosen equality on the finite site set hidden in the numerical matrix expression. -/
theorem spectralWeakRiesz_finiteSiteWeakForm
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (hs₃ : s ≤ 3)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (S : Finset J(χ,a,s)) (hc : ∀ i k : S, i.val.val.1 = k.val.val.1) (j : J(χ,a,s)) (hj : j ∈ S) :
    finiteRieszGramEnergy (weakMap(a,s,hs)) f j S =
      (heckeJetGramScale F)⁻¹ * finiteSiteWeakForm (s/2) (fun i : J(χ,a,s) ↦ i.val.2.2.1) S j hj := by
  classical
  rw [finiteSiteWeakForm_eq]
  exact spectralStripRiesz_weak_energy_on_character (F := F) χ hs hs₃ f hf S hc j hj

/-- The actual weak finite interpolation energy of the prescribed window has the original
Haar normalization. -/
theorem spectralWeakRiesz_window_energy
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (hs₃ : s ≤ 3)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i)) (j : J(χ,a,s)) :
    finiteRieszGramEnergy (weakMap(a,s,hs)) f j (spectralCardinalWindow χ hs₃ j) =
      (heckeJetGramScale F)⁻¹ * spectralWeakCardinalForm χ hs₃ j := by
  let S := spectralCardinalWindow χ hs₃ j
  have hm (i : S) := ((mem_spectralCardinalWindow χ hs₃ i.val j).1 i.property).1
  have hj := (mem_spectralCardinalWindow χ hs₃ j j).2 ⟨rfl, by simp⟩
  exact spectralWeakRiesz_finiteSiteWeakForm (F := F) χ hs hs₃ f hf S (fun i k ↦ (hm i).trans (hm k).symm) j hj

/-- The radius-six Gram form controls the weaker order of the original lifted basis vector.
The multiplier hypothesis is scalar, independent of the field and of all exterior zeros.
The normalization is the square root of the reciprocal Haar scale. -/
theorem spectralWeakCardinal_radiusSix_of_multiplier
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) {a s : ℝ}
    (hs : 1 < s) (hs₂ : 2 < s) (hs₃ : s ≤ 3)
    (x : J(χ,a,s) → Q(a,hs)) (f : J(χ,a,s) → StrongDual ℂ Q(a,hs))
    (hb : IsSpectralMarkushevichBasis x f) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (j : J(χ,a,s))
    (A : Lp ℂ 2 (sobolevMeasure (s/2)) →L[ℂ] Lp ℂ 2 (sobolevMeasure (s/2)))
    (hA : ‖A‖ ≤ 13/48) (hAeval : ∀ (g : Lp ℂ 2 (sobolevMeasure (s/2))) t,
      (∫ ξ, phase t ξ * A g ξ ∂angularMeasure) =
        (scaledCutoffQuotient j.val.2.2.1 6 t : ℂ) * (∫ ξ, phase t ξ * g ξ ∂angularMeasure)) :
    let localNorm := Real.sqrt (heckeJetGramScale F)⁻¹ * Real.sqrt (spectralWeakCardinalForm χ hs₃ j)
    (1-radiusSixError) * localNorm ≤ ‖weakMap(a,s,hs) (x j)‖ ∧
      ‖weakMap(a,s,hs) (x j)‖ ≤ (1+radiusSixError) * localNorm := by
  classical
  intro localNorm
  refine weakNorm_radiusSix_of_sameCharacter_gram (I := PontryaginDual C₁) (J := J(χ,a,s))
    (H := Q(a,hs)) (V := CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-0) 0 (s-2))
    x f hb (fun k ↦ k.val.1) (fun k ↦ k.val.2.2.1) j
    (spectralCardinalWindow χ hs₃ j) (fun i ↦ mem_spectralCardinalWindow χ hs₃ i j) ?_
    (show 1 < s/2 by linarith) (by linarith) (weakMap(a,s,hs)) (γ := Real.sqrt (heckeJetGramScale F)⁻¹) (Real.sqrt_nonneg _) ?_ A hA ?_
  · intro i k hik
    rw [spectralQuotientRiesz_pair χ (zero_le_one.trans hs.le) f hf i k]
    exact spectralStripJet_inner_zero_of_ne_character χ hχ (zero_le_one.trans hs.le) hs₃ k i (Ne.symm hik)
  · intro S hj hsame
    have hc (i k : S) : i.val.val.1 = k.val.val.1 := (hsame i.val i.property).trans (hsame k.val k.property).symm
    refine ⟨spectralStripJet_ordinate_injective hs₃ S hc, ?_⟩
    have hsq := spectralWeakRiesz_finiteSiteWeakForm (F := F) χ hs hs₃ f hf S hc j hj
    rw [finiteRieszGramEnergy_eq] at hsq
    have hsqrt := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (inv_nonneg.mpr (heckeJetGramScale_pos (F := F)).le)] at hsqrt
    exact hsqrt
  · exact fun g i _ ↦ hAeval g i.val.2.2.1

/-- At every actual one-jet zero, all exterior sites change the weak norm by at most
`13 * sqrt 3 / 48` times the computed local value. Both inequalities include the original
Haar factor. The estimate has no spacing or multiplier assumption. -/
theorem spectralWeakCardinal_radiusSix
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) {a s : ℝ}
    (hs : 1 < s) (hs₂ : 2 < s) (hs₃ : s ≤ 3)
    (x : J(χ,a,s) → Q(a,hs)) (f : J(χ,a,s) → StrongDual ℂ Q(a,hs))
    (hb : IsSpectralMarkushevichBasis x f) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (j : J(χ,a,s)) :
    let localNorm := Real.sqrt (heckeJetGramScale F)⁻¹ * Real.sqrt (spectralWeakCardinalForm χ hs₃ j)
    (1-radiusSixError) * localNorm ≤ ‖weakMap(a,s,hs) (x j)‖ ∧
      ‖weakMap(a,s,hs) (x j)‖ ≤ (1+radiusSixError) * localNorm := by
  obtain ⟨A, hA, heval⟩ := exists_radiusSixBesselMultiplier (s/2) (by linarith) (by linarith) j.val.2.2.1
  exact spectralWeakCardinal_radiusSix_of_multiplier χ hχ hs hs₂ hs₃ x f hb hf j A hA heval

end RiemannMasullo.WeakCardinal
