module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.WeightedGramPairing
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FiniteHeckeWindow
import Mathlib.Tactic

/-! Grams of orthogonal sections of the actual width-zero quotient Riesz functionals. -/

@[expose] public noncomputable section
open MeasureTheory NumberField Complex
open scoped InnerProductSpace ENNReal ComplexConjugate Matrix NumberField.AdeleRing
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
local notation "N(" a "," hs ")" => globalThetaSobolev F a hI (zero_le_one.trans (hs).le)
local notation "J(" χ "," a "," s ")" => SpectralStripJetIndex (F := F) χ a 0 s
local notation "D(" a "," hs ")" => spectralSobolevDualEmbedding F a hI (zero_le_one.trans (hs).le)
local notation "nv(" χ "," hs "," i ")" =>
  (spectralStripJet_memLp (F := F) χ (le_refl (0:ℝ)) (zero_le_one.trans (hs).le) i).toLp
    (spectralZeroJet (F := F) (χ (i).val.1) (i).val.2.1 (i).val.2.2.1 (i).val.2.2.2)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "ρ(" s "," g ")" => intervalSobolevDensity (-0) 0 s (logIdeleClassNorm F g)
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 s
local notation "wave(" χ "," j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "v(" a "," hs "," f ")" => (InnerProductSpace.toDual ℂ Q(a,hs)).symm (f)
local notation "S(" a "," hs "," f ")" => ((N(a,hs)).quotientEquivOrthogonal (v(a,hs,f))).val
local notation "weak(" s ")" => intervalSobolevWeakening μ𝔽 (logIdeleClassNorm F) (-0) 0 s
local notation "site(" j ")" => (j).val.2.2.1

private theorem gram_of_section_profiles {ι : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (h₃ : s ≤ 3) (t : ℝ) (hd : 1 < 2*s-t)
    (j : ι → J(χ,a,s)) (hχ : ∀ i k, (j i).val.1 = (j k).val.1) (V : ι → W(t))
    (hV : ∀ i, (V i : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ conj (wave(χ,j i) g)/(ρ(s,g):ℂ)) :
    Matrix.gram ℂ V = (heckeJetGramScale F:ℂ) • gramMatrix ((2*s-t)/2) (fun i ↦ site(j i)) := by
  apply Matrix.ext
  intro i k
  obtain ⟨j₁,j₂⟩ := retained_offset_order_zero h₃ (j i).property
  obtain ⟨k₁,k₂⟩ := retained_offset_order_zero h₃ (j k).property
  have hi := hV i
  have hk := hV k
  rw [j₁,j₂,hχ i k] at hi
  rw [k₁,k₂] at hk
  exact physicalValueRiesz_inner_angularGram s t hd (χ (j k).val.1) _ _ (V i) (V k) hi hk

/-- The actual retained quotient coordinate, lifted via the orthogonal section, is conjugate
jet divided by the strong density almost everywhere for the original Tamagawa measure. -/
theorem spectralStripRiesz_section_coeFn
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (j : J(χ,a,s)) :
    (S(a,hs,f j) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ conj (wave(χ,j) g)/(ρ(s,g):ℂ) := by
  have hp := spectralSection_riesz_coeFn a (-0) 0 s hI (zero_le_one.trans hs.le) (f j)
  rw [hf j] at hp
  have hj : (nv(χ,hs,j) : C𝔽 → ℂ) =ᵐ[μ𝔽] wave(χ,j) :=
    (widthZero_base_ac_dual (F := F) s).ae_eq
      (spectralStripJet_memLp χ (le_refl (0:ℝ)) (zero_le_one.trans hs.le) j).coeFn_toLp
  exact hp.trans (hj.mono fun g hg ↦ congrArg (fun z : ℂ ↦ conj z/(ρ(s,g):ℂ)) hg)

/-- The physical representative is the same when read in the lower-order positive measure. -/
theorem spectralStripRiesz_weakened_coeFn
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (j : J(χ,a,s)) :
    (weak(s) (S(a,hs,f j)) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ conj (wave(χ,j) g)/(ρ(s,g):ℂ) := by
  have he : (weak(s) (S(a,hs,f j)) : C𝔽 → ℂ) =ᵐ[μ𝔽] S(a,hs,f j) :=
    (widthZero_base_ac_sobolev (F := F) (s-2)).ae_eq
      (intervalSobolevWeakening_coeFn μ𝔽 (logIdeleClassNorm F) (-0) 0 s (S(a,hs,f j)))
  exact he.trans (spectralStripRiesz_section_coeFn χ hs f hf j)

/-- Strong Riesz Gram in the actual quotient, including its positive Haar multiplier. -/
theorem spectralStripRiesz_gramMatrix_line {ι : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (h₃ : s ≤ 3) (j : ι → J(χ,a,s)) (hχ : ∀ i k, (j i).val.1=(j k).val.1) :
    Matrix.gram ℂ (fun i ↦ v(a,hs,f (j i))) =
      (heckeJetGramScale F:ℂ) • gramMatrix (s/2) (fun i ↦ site(j i)) := by
  apply Matrix.ext
  intro i k
  change ⟪v(a,hs,f (j i)),v(a,hs,f (j k))⟫_ℂ =
    (heckeJetGramScale F:ℂ) * gramMatrix (s/2) (fun i ↦ site(j i)) i k
  rw [InnerProductSpace.toDual_symm_apply,spectralQuotientRiesz_pair χ (zero_le_one.trans hs.le) f hf]
  exact (spectralStripJet_inner_angularGram χ (zero_le_one.trans hs.le) h₃ (j k) (j i) (hχ k i)).trans
    (congrArg (fun z : ℂ ↦ (heckeJetGramScale F:ℂ)*z) (gramMatrix_apply_comm (s/2) (fun i ↦ site(j i)) i k))

/-- Weak Gram of the genuine physical section. The exponent is exactly `s/2+1`
and the Haar normalization is the same as in the strong norm. -/
theorem spectralStripRiesz_weak_gramMatrix_line {ι : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (h₃ : s ≤ 3) (j : ι → J(χ,a,s)) (hχ : ∀ i k, (j i).val.1=(j k).val.1) :
    Matrix.gram ℂ (fun i ↦ weak(s) (S(a,hs,f (j i)))) =
      (heckeJetGramScale F:ℂ) • gramMatrix (s/2+1) (fun i ↦ site(j i)) := by
  have h := gram_of_section_profiles χ h₃ (s-2) (by linarith) j hχ
    (fun i ↦ weak(s) (S(a,hs,f (j i)))) (fun i ↦ spectralStripRiesz_weakened_coeFn χ hs f hf (j i))
  simpa only [show (2*s-(s-2))/2 = s/2+1 by ring] using h

end RiemannMasullo.WeakCardinal
