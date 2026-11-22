module

public import RiemannMasullo.AppB_AnalyticNT.Sec5
import Mathlib.Algebra.Field.ULift

/-!
# Appendix B.5: statements that are false as printed

The printed claims are kept as propositions with separate refutation statements.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped Topology

namespace RiemannMasullo

/-- Paper: §B.5.1, injectivity sentence, p. 627. As printed: in every positive
dimension, the torus flow of rationally independent frequencies is injective.
This is the injectivity clause of the sentence. The repaired
`torusFlow_injective_of_linearIndependent` requires dimension at least two.
See ERRATA F19. -/
def Printed.torusFlow_injective_of_linearIndependent : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (τ : Fin N → ℝ), LinearIndependent ℚ τ → Injective (torusFlow τ)

/-- Paper: §B.5.1, injectivity sentence, p. 627. In dimension one the
single frequency `1` is rationally independent, and times zero and one have the same
image modulo one. -/
theorem Printed.torusFlow_injective_of_linearIndependent_false :
    ¬ Printed.torusFlow_injective_of_linearIndependent := by
  intro h
  have hli : LinearIndependent ℚ (fun _ : Fin 1 ↦ (1 : ℝ)) :=
    linearIndependent_unique_iff.mpr one_ne_zero
  have h01 :
      torusFlow (fun _ : Fin 1 ↦ (1 : ℝ)) 1 = torusFlow (fun _ : Fin 1 ↦ (1 : ℝ)) 0 := by
    rw [torusFlow_one, map_zero]
    funext i
    exact AddCircle.coe_period (1 : ℝ)
  exact one_ne_zero (h 1 le_rfl _ hli h01)

/-- Paper: Theorem B.5.2.1(2), p. 627. As printed: for every frequency vector
and every Riemann-integrable function on its orbit closure, the forward time average
in (B.5.2.1) exists and tends to the Haar probability integral. The forward equality
requires the time integrals to exist for all sufficiently large endpoints.
The repaired `kroneckerWeyl_riemannIntegrable_forward` assumes a measurable time
trace. See ERRATA F20. -/
def Printed.kroneckerWeyl_riemannIntegrable_forward : Prop :=
  ∀ (N : ℕ) [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ), TorusRiemannIntegrable μ u →
      let trace := fun t ↦ u (torusFlowInClosure τ t)
      (∀ᶠ T : ℝ in atTop, IntervalIntegrable trace volume 0 T) ∧
        Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, trace t) atTop (𝓝 (∫ x, u x ∂μ))

/-- Paper: Theorem B.5.2.1(2), p. 627. Take frequencies `(1, √2)` and a
non-Lebesgue-measurable subset `E` of `(0, 1)`. The indicator of the image of `E`
under the flow is bounded and continuous off the compact Haar-null orbit arc of
`[0, 1]`. Injectivity makes its time trace the indicator of `E`, which is
nonmeasurable on every interval `[0, T]` with `T ≥ 1`. -/
theorem Printed.kroneckerWeyl_riemannIntegrable_forward_false :
    ¬ Printed.kroneckerWeyl_riemannIntegrable_forward := by
  sorry

/-- Paper: Proposition B.5.3.2(1),(3), p. 632. As printed: for every number field,
finite set of places containing the archimedean places, and continuous character
unramified at its finite places, there are heights with both stated signs and a common
finite bound on the product in (B.5.3.3) for every integer index. The bound is written
as a positive lower bound on the norm of the product of the denominators, so it
excludes zeros of every denominator. These two sign conditions and the bound are
the clauses at issue. The repaired
`exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow` allows a positive
height at index zero. See ERRATA F21. -/
def Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
      ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k ≤ 0 → T k ≤ 0) ∧
        ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖

/-- Every number field refutes the printed bound: the trivial character has a zero
factor at time zero. -/
private theorem
    Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false_of_numberField.{u}
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow.{u}) : False := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hone :
      ∀ g, ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 g = 1 := by
    intro g
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres : ∀ x : v.adicCompletion F, x ≠ 0 →
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).restrict v x =
        1 := by
    intro x hx
    rw [show x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
      HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    simp [hone]
  have hunr :
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).IsUnramifiedAt
        v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    intro x
    exact hres _ (by simp)
  obtain ⟨c, T, hc, hpos, hneg, hbound⟩ := h F {v} 1 (by simpa using hunr)
  have hT : T 0 = 0 := le_antisymm (hneg 0 le_rfl) (hpos 0 le_rfl)
  have h0 := hbound 0
  rw [hT, reciprocalPartialHeckeEulerProduct_singleton _ v hunr,
    hunr.localValue_eq _ Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    hres _ (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)] at h0
  simp at h0
  linarith

/-- Paper: Proposition B.5.3.2(1),(3), p. 632. Take the rational field,
the trivial character, and the places consisting of infinity and the prime above two.
Both sign conditions apply at index zero, so `T 0 = 0`. The only finite factor
in the denominator is then `|1 - 2^0| = 0`. -/
theorem Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false :
    ¬ Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact
    Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false_of_numberField
      (ULift ℚ) h

/-- Paper: Lemma B.5.3.4(2), p. 633. As printed: if a holomorphic function on a
bounded nonempty open vertical strip is strongly recurrent on every closed disc it
contains, then the function is strongly recurrent on every compact subset of the strip.
Part (1) is `stronglyRecurrentOn_of_subset`. See ERRATA F22. -/
def Printed.stronglyRecurrentOn_compact_of_closedBall : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (verticalStrip a b) →
    (∀ (z : ℂ) (r : ℝ), 0 ≤ r → Metric.closedBall z r ⊆ verticalStrip a b →
      StronglyRecurrentOn f (Metric.closedBall z r)) →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ verticalStrip a b → StronglyRecurrentOn f K

/-- Paper: Lemma B.5.3.4(2), p. 633. In the strip `|Re z| < 1/2` take the
segment `K = [-2i, 2i]`. Construct an entire function of norm less than one on
`K` and greater than three at every `4ji` for nonzero integer `j`.
Start with polynomial approximations to zero on `K` and four at `±4i`.
Cycle through the rational closed discs strictly inside the strip. At stage
`L = 2^n`, approximate the preceding polynomial on the square of half-side
`4L + 1` and copy its values from the scheduled disc of center `c` to its vertical
translates by `i (4m + 2 - Im c)` for `L ≤ m < 2L`. Their centers have height
`4m + 2` and their radii are less than one half. Schedule each disc infinitely often
after it fits in the old square. Approximate four at `±4ji` for `L < j ≤ 2L`. The union of the
square, new discs, and new marks has connected complement, so Runge approximation
allows summable errors of total less than one. For each disc strictly inside a scheduled
disc, the copy errors tend to zero and continuity gives intervals of good shifts of fixed
positive width.
These intervals give positive upper density along its blocks. Every shift of
`K` by imaginary height of absolute value at least six meets a mark, so its
return times for tolerance two have upper density zero. -/
theorem Printed.stronglyRecurrentOn_compact_of_closedBall_false :
    ¬ Printed.stronglyRecurrentOn_compact_of_closedBall := by
  sorry

end RiemannMasullo
