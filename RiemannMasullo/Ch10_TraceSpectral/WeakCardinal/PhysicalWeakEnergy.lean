module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.PhysicalWeakReadout
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.ScaledFiniteEnergy
import Mathlib.Tactic

/-! The finite original-quotient squared weak norms are the normalized angular inverse-Gram energies. -/

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

open Classical in
/-- On each actual finite one-character enlargement the weak energy equals the
selected angular inverse column's weak quadratic form divided by the Haar scale. -/
theorem spectralStripRiesz_weak_energy_on_character
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (h₃ : s ≤ 3)
    (f : J(χ,a,s) → StrongDual ℂ Q(a,hs)) (hf : ∀ i, D(a,hs) (f i) = nv(χ,hs,i))
    (E : Finset J(χ,a,s)) (hχ : ∀ i k : E, i.val.val.1 = k.val.val.1)
    (j : J(χ,a,s)) (hj : j ∈ E) :
    let c (i : E) := (gramMatrix (s/2) (fun k : E ↦ site(k)))⁻¹ i ⟨j,hj⟩
    finiteRieszGramEnergy (spectralWeakRieszReadout F a s hs) f j E =
      (heckeJetGramScale F)⁻¹ * (star c ⬝ᵥ gramMatrix (s/2+1) (fun k : E ↦ site(k)) *ᵥ c).re := by
  classical
  let V := W(s-2)
  let L : Q(a,hs) →L[ℂ] V := spectralWeakRieszReadout F a s hs
  let t (i : E) := site(i)
  let A := gramMatrix (s/2) t
  let B := gramMatrix (s/2+1) t
  have hG : Matrix.gram ℂ (fun i : E ↦ (InnerProductSpace.toDual ℂ Q(a,hs)).symm (f i.val)) =
      (heckeJetGramScale F:ℂ) • A :=
    spectralStripRiesz_gramMatrix_line (F := F) χ hs f hf h₃ (fun i : E ↦ i.val) hχ
  have hW : Matrix.gram ℂ (fun i : E ↦ L ((InnerProductSpace.toDual ℂ Q(a,hs)).symm (f i.val))) =
      (heckeJetGramScale F:ℂ) • B :=
    spectralWeakRieszReadout_gram (F := F) χ hs f hf h₃ (fun i : E ↦ i.val) hχ
  have hi : IsUnit A.det := isUnit_iff_ne_zero.mpr (gramMatrix_det_ne_zero (s/2) (by linarith)
    (spectralStripJet_ordinate_injective (F := F) h₃ E hχ))
  have he := finiteRieszGramEnergy_of_scaledGrams_withDecEq (J := J(χ,a,s)) (H := Q(a,hs)) (V := V) L f j E hj
    (heckeJetGramScale F) (heckeJetGramScale_pos (F := F)) A B hi hG hW
  exact he

end RiemannMasullo.WeakCardinal
