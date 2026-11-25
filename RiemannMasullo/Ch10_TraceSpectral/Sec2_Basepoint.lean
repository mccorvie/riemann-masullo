module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-! # A basepoint choice that is trivial on a norm section

`exists_spectralBasepointChoice` (`Sec2`) extends every character `ω` of the norm-one idele
classes to a unitary character `χ ω` of the idele classes, by composing `ω` with the projection
`g ↦ g / σ |g|` for the canonical section `σ` of the norm. Its statement keeps only the
extension property. The uniform estimates of the cluster route to Theorem 10.3.2.1 are for
characters that are trivial on the image of a norm section, so this file states the
construction with its other properties, for an arbitrary section `τ` of the norm.

* `exists_spectralBasepointChoice_monoidHom_of_normSection`: the choice `χ ω = ω ∘ (g ↦ g / τ |g|)`
  is a group homomorphism in `ω`, it is a basepoint choice, and every `χ ω` is trivial on the
  image of `τ`.
* `exists_spectralBasepointChoice_of_normSection`: the same as a plain function, with
  `χ 1 = 1`.

`Sec3_TraceClass` uses the second statement. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker

/-- Paper: Notation 10.2.1.1, p. 440. Let `τ` be a continuous section of the norm of the idele
classes. Composition with the projection `g ↦ g / τ |g|` onto the norm-one classes is a group
homomorphism `χ` from the characters of the norm-one classes to the unitary characters of the
idele classes; every `χ ω` extends `ω`, and every `χ ω` is trivial on the image of `τ`.
Deviation: The paper chooses the extensions without naming a section. This is the construction
in the proof of `exists_spectralBasepointChoice`, for any section, with its properties
stated. -/
theorem exists_spectralBasepointChoice_monoidHom_of_normSection (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ χ : PontryaginDual C₁ →* PontryaginDual C𝔽,
      IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) ∧
        ∀ (ω : PontryaginDual C₁) (t : ℝ≥0ˣ), χ ω (τ t) = 1 := by
  let n : C𝔽 →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
  let P : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp n
  have hP (x : C𝔽) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  refine ⟨(PontryaginDual.map r).toMonoidHom, fun ω ↦ ?_, fun ω t ↦ ?_⟩
  · ext x : 1
    change ω (r (x : C𝔽)) = ω x
    apply congrArg ω
    apply Subtype.ext
    change (x : C𝔽) / τ (ideleClassNorm F x) = x
    rw [show ideleClassNorm F (x : C𝔽) = 1 from x.property, map_one, div_one]
  · change ω (r (τ t)) = 1
    have hr : r (τ t) = 1 := by
      apply Subtype.ext
      change τ t / τ (ideleClassNorm F (τ t)) = 1
      rw [hτ, div_self']
    rw [hr, map_one]

/-- Paper: Notation 10.2.1.1, p. 440. For every continuous section `τ` of the norm of the idele
classes there is a basepoint choice `χ` such that every `χ ω` is trivial on the image of `τ`
and `χ 1` is the trivial character.
Deviation: As for `exists_spectralBasepointChoice_monoidHom_of_normSection`. -/
theorem exists_spectralBasepointChoice_of_normSection (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ χ : PontryaginDual C₁ → PontryaginDual C𝔽,
      IsSpectralBasepointChoice χ ∧ (∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = 1) ∧ χ 1 = 1 := by
  obtain ⟨χ, hχ, hχτ⟩ := exists_spectralBasepointChoice_monoidHom_of_normSection τ hτ
  exact ⟨fun ω ↦ χ ω, hχ, hχτ, map_one χ⟩

end RiemannMasullo
