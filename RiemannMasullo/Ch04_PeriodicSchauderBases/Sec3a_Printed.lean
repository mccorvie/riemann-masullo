module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a

/-! # Chapter 4.3: printed isotypic transform norm bounds -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function MeasureTheory
open scoped CompactlySupported NNReal

/-- Paper: Equation (4.3.2.5), p. 178. As printed: for every second-countable
modulated group with a section to its module and choices of Haar measures,
each character component satisfies the displayed bound on compactly supported
continuous functions. The Hilbert sum transform in Lemma 4.3.2.2, p. 179, and
the restriction of each component to its isotype on p. 180 are isometries. These are the norm clauses. See
`regularIsotypicTransform_norm_sq` and ERRATA F211. -/
def Printed.regularIsotypicTransform_isometries : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (ν : Measure G) [ν.IsHaarMeasure]
    (ν₁ : Measure m.toMonoidHom.ker) [ν₁.IsHaarMeasure]
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m),
    (∀ (ω : PontryaginDual m.toMonoidHom.ker) (φ : G →C_c ℂ),
      let f := (regularL2_memLp_compactlySupported ν φ).toLp φ
      ‖regularIsotypicComponent m hm ν ν₁ τ hτ ω f‖ ≤ ‖f‖) ∧
    Isometry (regularIsotypicTransform m hm ν ν₁ τ hτ) ∧
    ∀ ω : PontryaginDual m.toMonoidHom.ker,
      Isometry (fun f : {f : RegularL2 ν // ∀ k : m.toMonoidHom.ker,
          regularTranslate ν (k : G) f = (ω k : ℂ) • f} ↦
        regularIsotypicComponent m hm ν ν₁ τ hτ ω f.val)

/-- Paper: Equation (4.3.2.5), p. 178. Take G = ℝ₊ˣ, with identity module and
section, ν = dt/t and ν₁ = 2δ₁ on the trivial kernel. The unique isotype is all
of L², and the continuous test φ(t) = max(0, 1 − |log t|) has compact support and
positive L² norm. Both the component and the Hilbert sum transform double its norm.
Even with product normalization, the idele class group of ℚ(i) gives the norm
factor √(π/4) in the isometry of Lemma 4.3.2.2, p. 179, and in the isotype isometry on p. 180. -/
theorem Printed.regularIsotypicTransform_isometries_false :
    ¬ Printed.regularIsotypicTransform_isometries := by sorry

end RiemannMasullo
