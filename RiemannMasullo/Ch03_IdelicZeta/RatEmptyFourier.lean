module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # The real Fourier normalization for the rational stage with no finite places

The character and measure computations come from the proof of `sec2bP_fourier`,
originally in `Ch11_ShellStructure/Sec2b_Printed.lean`.
-/

noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing

namespace RiemannMasullo

private theorem ratEmpty_single {ι : Type*} [Unique ι] {M : ι → Type*} [∀ i, Zero (M i)]
    {d : DecidableEq ι} (v : M default) : @Pi.single ι M _ d (default : ι) v default = v := by
  let := d
  exact Pi.single_eq_same _ _

open scoped FourierTransform in
private theorem ratEmpty_character (x y : SAdeleRing ℚ ∅) :
    (sAdeleStandardCharacter ℚ ∅ (x * y) : ℂ) =
      Real.fourierChar (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace) *
        InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
          (y.1 Rat.infinitePlace)) := by
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  unfold sAdeleStandardCharacter
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
    adeleStandardCharacter_rat, ratAdeleStandardCharacter_real _ rfl]
  rw [Real.fourierChar_apply']
  congr 3
  dsimp only
  exact (congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
    (ratEmpty_single (M := InfinitePlace.Completion) _)).trans
    (map_mul (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _)

open scoped FourierTransform in
private theorem ratEmpty_integral (G : Rat.infinitePlace.Completion → ℂ) :
    letI : MeasurableSpace Rat.infinitePlace.Completion := borel _
    ∫ x : SAdeleRing ℚ ∅, G (x.1 Rat.infinitePlace) ∂sAdditiveTamagawaMeasure ℚ ∅ =
      ∫ r : ℝ, G ((InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace).symm r) := by
  let (w : InfinitePlace ℚ) : MeasurableSpace w.Completion :=
    instMeasurableSpaceCompletion_riemannMasullo ℚ w
  let : MeasurableSpace (InfiniteAdeleRing ℚ) := instMeasurableSpaceInfiniteAdeleRing_riemannMasullo ℚ
  let (v : (HeightOneSpectrum (𝓞 ℚ))) : MeasurableSpace (v.adicCompletion ℚ) :=
    instMeasurableSpaceAdicCompletionRingOfIntegers_riemannMasullo ℚ v
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
  let e : ℝ ≃ᵐ Rat.infinitePlace.Completion :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm.toHomeomorph.toMeasurableEquiv
  have hν : infiniteLocalAdditiveTamagawaMeasure ℚ Rat.infinitePlace = (volume : Measure ℝ).map e := by
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace]
    rfl
  have hσ : ∀ w : InfinitePlace ℚ, SigmaFinite (infiniteLocalAdditiveTamagawaMeasure ℚ w) := by
    intro w
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    rw [hν]
    exact e.sigmaFinite_map
  have : @SFinite (InfiniteAdeleRing ℚ) (instMeasurableSpaceInfiniteAdeleRing_riemannMasullo ℚ)
      (Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ)) :=
    (inferInstance : SFinite (Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ)))
  unfold sAdditiveTamagawaMeasure
  rw [integral_fun_fst (f := fun a : InfiniteAdeleRing ℚ ↦ G (a Rat.infinitePlace))]
  rw [Measure.pi_of_empty (x := isEmptyElim)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hp := measurePreserving_piUnique (X := fun w : InfinitePlace ℚ ↦ w.Completion)
    (infiniteLocalAdditiveTamagawaMeasure ℚ)
  refine (hp.integral_comp' G).trans ?_
  refine (congrArg (fun μ : Measure Rat.infinitePlace.Completion ↦ ∫ y, G y ∂μ) hν).trans ?_
  rw [integral_map_equiv]
  rfl

open scoped FourierTransform in
/-- With no finite places in S over ℚ, the S-adelic Fourier transform is the real
Fourier transform in the unique archimedean coordinate. -/
public theorem sAdeleSchwartzFourier_ratEmpty_apply (φ : SchwartzMap ℝ ℂ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (y : SAdeleRing ℚ ∅) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd y) =
      𝓕 φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (y.1 Rat.infinitePlace)) := by
  let : MeasurableSpace (SAdeleRing ℚ ∅) := instMeasurableSpaceSAdeleRing ℚ ∅
  change tamagawaFourier (sAdditiveTamagawaMeasure ℚ ∅) (sAdeleStandardCharacter ℚ ∅)
    (fun x ↦ f (Multiplicative.ofAdd x)) y = _
  unfold tamagawaFourier
  simp only [hf, ratEmpty_character]
  rw [ratEmpty_integral (fun z ↦ φ (InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace z) * star ((Real.fourierChar (InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace z * InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace (y.1 Rat.infinitePlace)) : ℂ)))]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  congr 1
  funext r
  rw [RingEquiv.apply_symm_apply, Circle.smul_def, smul_eq_mul, mul_comm]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

end RiemannMasullo
