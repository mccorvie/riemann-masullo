module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.PhysicalRieszGram
import Mathlib.Tactic

/-! The original quotient has a continuous weak readout via its canonical orthogonal section. -/

@[expose] public noncomputable section
open MeasureTheory NumberField
open scoped InnerProductSpace ENNReal Matrix NumberField.AdeleRing
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
local notation "sectionMap(" a "," hs ")" => (N(a,hs)).orthogonal.subtypeL.comp
  (N(a,hs)).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
local notation "weakMap(" a "," s "," hs ")" =>
  (intervalSobolevWeakening (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-0) 0 s).comp (sectionMap(a,hs))
local notation "W(" t ")" => CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-0) 0 t
local notation "site(" i ")" => (i).val.val.2.2.1

variable (F) in
/-- The orthogonal section of the original width-zero quotient read at degree `s−2`. -/
def spectralWeakRieszReadout (a s : ℝ) (hs : 1 < s) :
    Q(a,hs) →L[ℂ] W(s-2) := weakMap(a,s,hs)

theorem spectralWeakRieszReadout_apply (a s : ℝ) (hs : 1 < s) (u : Q(a,hs)) :
    spectralWeakRieszReadout F a s hs u =
      intervalSobolevWeakening (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-0) 0 s
        ((N(a,hs)).quotientEquivOrthogonal u).val := rfl

theorem spectralWeakRieszReadout_gram {ι : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (h₃ : s ≤ 3) (j : ι → J(χ,a,s)) (hχ : ∀ i k, (j i).val.1=(j k).val.1) :
    Matrix.gram ℂ (fun i ↦ spectralWeakRieszReadout F a s hs ((InnerProductSpace.toDual ℂ Q(a,hs)).symm (f (j i)))) =
      (heckeJetGramScale F:ℂ) • gramMatrix (s/2+1) (fun i ↦ (j i).val.2.2.1) := by
  simp only [spectralWeakRieszReadout_apply]
  exact spectralStripRiesz_weak_gramMatrix_line (F := F) χ hs f hf h₃ j hχ

end RiemannMasullo.WeakCardinal
