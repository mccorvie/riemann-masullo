module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # The printed real Haar normalization in §12.4 -/

@[expose] public noncomputable section

open MeasureTheory NumberField
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Theorem 12.4.1.1, prose after (12.4.1.3), p. 514.
As printed: at every real place the multiplicative Tamagawa measure itself is the canonical
Haar measure for the local absolute value. This is the real-place clause of the list.
See `infiniteCanonicalHaar_eq_smul_tamagawa` and ERRATA F245. -/
def Printed.infiniteCanonicalHaar_eq_tamagawa_of_isReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), w.IsReal →
    letI _completionSecondCountable : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    letI _unitsSecondCountable : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    letI _completionMeasurable : MeasurableSpace w.Completion := borel _
    letI _completionBorel : BorelSpace w.Completion := ⟨rfl⟩
    letI _unitsBorel : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let m : w.Completionˣ →ₜ* ℝ≥0ˣ :=
      ⟨(Units.map nnNormHom.toMonoidHom) ^ w.mult, continuous_infiniteLocalModule w⟩
    ∃ hm : IsModulation m,
      canonicalModulatedHaar m hm = infiniteLocalMultiplicativeTamagawaMeasure F w

/-- Paper: Theorem 12.4.1.1, prose after (12.4.1.3), p. 514.
Take the real place of `ℚ`, with completion `ℝ` and local absolute value `|x|`.
The preimage of `[1/2, 2]` consists of the positive and negative copies of that interval.
The Tamagawa measure `dx/|x|` gives it mass `4 log 2`, whereas canonical Haar measure
gives it mass `2 log 2`, since its pushforward under `|x|` is `dt/t`. -/
theorem Printed.infiniteCanonicalHaar_eq_tamagawa_of_isReal_false :
    ¬ Printed.infiniteCanonicalHaar_eq_tamagawa_of_isReal := by sorry

end RiemannMasullo
