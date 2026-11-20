module

public import RiemannMasullo.AppC_LCTVS.Sec4
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Pettis averaging, invariants and isotypes -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology
open scoped InnerProductSpace NNReal

section Isotypes

variable {G E : Type*} [Monoid G] [TopologicalSpace G]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Corollary 4.3.3.3(2), p. 183. An isotypic subspace is the common
eigenspace for the given character. For the trivial character it is the
fixed subspace in Lemma 4.3.3.1(2) and for the regular action it is the
isotype of Terminology 4.3.2.1. -/
def actionIsotype (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) : Submodule ℂ E :=
  ⨅ g : G, LinearMap.ker ((ρ g).toLinearMap - (ω g : ℂ) • LinearMap.id)

/-- Paper: Corollary 4.3.3.3(2), p. 183. A vector lies in the isotype exactly
when every group element acts on it by the specified character value. -/
theorem mem_actionIsotype (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) (u : E) :
    u ∈ actionIsotype ρ ω ↔ ∀ g : G, ρ g u = (ω g : ℂ) • u := by sorry

/-- Paper: Lemma 4.3.3.1(2), p. 181 and Corollary 4.3.3.3(2), p. 183.
The isotypic subspace is closed in the original topology. -/
theorem isClosed_actionIsotype [T2Space E] [ContinuousSMul ℂ E] (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) :
    IsClosed (actionIsotype ρ ω : Set E) := by sorry

variable [MeasurableSpace G]

/-- Paper: (4.3.3.1), p. 181 and (4.3.3.8), p. 183. An unnormalized
isotypic averaging operator represents the integrals of the character-twisted
orbits against every continuous linear functional. The trivial character
gives the untwisted average. -/
def IsPettisIsotypicAverageOn (μ : Measure G) (X : Set G)
    (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) (P : E →L[ℂ] E) : Prop :=
  ∀ u : E, HasPettisIntegral (.positive (μ.restrict X))
    (fun g : G ↦ star (ω g : ℂ) • ρ g u) (P u)

/-- Paper: (4.3.3.5), p. 182. The untwisted average of a fixed vector equals
the vector times the mass of the compact group. -/
theorem IsPettisIsotypicAverageOn.apply_fixed [T2Space E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] (μ : Measure G) [IsFiniteMeasure μ]
    (ρ : G →* (E →L[ℂ] E)) (P : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ univ ρ 1 P) (u : E) (hu : ∀ g, ρ g u = u) :
    P u = μ.real univ • u := by sorry

end Isotypes

section Averaging

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [hE : QuasiCompleteSpace ℂ E]
  (μ : Measure G) [hμ : μ.IsHaarMeasure]
  (ρ : G →* (E →L[ℂ] E))
  (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))

include hE hμ hρ

/-- Paper: Lemma 4.3.3.1(1), p. 181. On a compact group the orbit integrals
give a unique continuous linear averaging operator, under equicontinuity
or sequential equicontinuity on a bornological space. -/
theorem existsUnique_compactActionAverage [CompactSpace G]
    (h : EquicontinuousAt (fun g : G ↦ (ρ g : E → E)) 0 ∨
      ((∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
          Continuous p) ∧
        ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
          TendstoUniformly (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop)) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ univ ρ 1 P := by sorry

/-- Paper: Corollary 4.3.3.3(1), p. 183. The character-weighted orbit
integrals determine a unique continuous linear operator for a sequentially
equicontinuous action on a quasi-complete bornological space. -/
theorem existsUnique_compactActionIsotypicAverage [CompactSpace G]
    (hborn : ∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p)
    (hseq : ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
      TendstoUniformly (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop)
    (ω : PontryaginDual G) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ univ ρ ω P := by sorry

/-- Paper: Lemma 4.3.3.7(1), p. 186. On a relatively compact locally
closed subset with nonempty interior, averaging the action gives a unique
continuous linear operator under either of the stated continuity conditions
on compact subsets. -/
theorem existsUnique_relativelyCompactActionAverage
    (X : Set G) (hX : IsCompact (closure X)) (hlc : IsLocallyClosed X)
    (hint : (interior X).Nonempty)
    (h : (∀ K : Set G, IsCompact K →
        EquicontinuousAt (fun g : K ↦ (ρ g : E → E)) 0) ∨
      ((∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
          Continuous p) ∧
        ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
          ∀ K : Set G, IsCompact K →
            TendstoUniformlyOn (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop K)) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ X ρ 1 P := by sorry

-- TODO(paper-gap): Lemma 4.3.3.7(2) and (3) fail for a relatively compact
-- locally closed subset. On the circle take X to be a proper open arc
-- around 1 and take the standard one-dimensional character action.
-- TODO(paper-gap): Corollary 4.3.3.8(1) allows nonmeasurable X.
-- Parts (2) and (3) fail even for an open arc and the trivial weight.

end Averaging

section CompactAverageProperties

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  (μ : Measure G) [hμ : μ.IsHaarMeasure]
  (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
  (ω : PontryaginDual G) (P : E →L[ℂ] E)
  (hP : IsPettisIsotypicAverageOn μ univ ρ ω P)

include hμ hρ hP

/-- Paper: Lemma 4.3.3.1(2), p. 181 and Corollary 4.3.3.3(2), p. 183.
The average surjects onto the isotype, including the fixed subspace
when the character is trivial. -/
theorem compactActionAverage_range : LinearMap.range P.toLinearMap = actionIsotype ρ ω := by sorry

/-- Paper: Lemma 4.3.3.1(2), p. 181 and Corollary 4.3.3.3(2), p. 183.
Dividing the average by the total mass gives an idempotent. -/
theorem compactActionAverage_idempotent :
    let Q : E →L[ℂ] E := (μ.real univ)⁻¹ • P
    Q.comp Q = Q := by sorry

/-- Paper: (4.3.3.2), p. 181 and (4.3.3.9), p. 183. The averaging operator
induces the norm isomorphism from the quotient by its kernel to the
isotypic subspace with its inherited topology. -/
theorem compactActionAverage_quotient_equiv :
    ∃ e : (E ⧸ P.ker) ≃L[ℂ] actionIsotype ρ ω,
      ∀ u : E, (e (P.ker.mkQ u) : E) = P u := by sorry

/-- Paper: Lemma 4.3.3.1(3), p. 181 and Corollary 4.3.3.3(3), p. 183.
The kernel of the averaging operator is the closed span of the differences
for the character-twisted action. -/
theorem compactActionAverage_ker :
    P.ker = (Submodule.span ℂ
      (range fun p : G × E ↦ p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2)).topologicalClosure := by sorry

end CompactAverageProperties

section HilbertProjectors

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (ν : Measure G) [ν.IsHaarMeasure]
  (ν₁ : Measure m.toMonoidHom.ker) [ν₁.IsHaarMeasure]

local notation "K" => m.toMonoidHom.ker
local notation "ρ₁" => MonoidHom.comp (regularL2Action ν) (Subgroup.subtype K)

/-- Paper: Corollary 4.3.3.4, p. 184. The unnormalized Hilbert operator
is also the Pettis operator for the restricted regular action. -/
theorem regularIsotypicIntegral_isPettisAverage (ω : PontryaginDual K) :
    IsPettisIsotypicAverageOn ν₁ univ ρ₁ ω (regularIsotypicIntegral m hm ν ν₁ ω) := by sorry

/-- Paper: Corollary 4.3.3.4, p. 184. The normalized average is the
orthogonal projection onto the isotype. The projected vector lies in
the isotype and the difference is perpendicular to that entire subspace. -/
theorem regularIsotypicIntegral_orthogonalProjection (ω : PontryaginDual K)
    (f : RegularL2 ν) :
    let S := actionIsotype ρ₁ ω
    let p := (ν₁.real univ)⁻¹ • regularIsotypicIntegral m hm ν ν₁ ω f
    p ∈ S ∧ f - p ∈ Sᗮ := by sorry

/-- Paper: Corollary 4.3.3.4, p. 184. Distinct isotypic subspaces of Haar L²
are orthogonal. -/
theorem regularL2_isotypes_orthogonal (ω χ : PontryaginDual K) (h : ω ≠ χ) :
    ∀ f ∈ actionIsotype ρ₁ ω, ∀ g ∈ actionIsotype ρ₁ χ, ⟪f, g⟫_ℂ = 0 := by sorry

end HilbertProjectors

end RiemannMasullo
