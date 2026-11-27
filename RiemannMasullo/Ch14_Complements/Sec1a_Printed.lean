module

public import Mathlib.NumberTheory.LocalField.Basic
public import RiemannMasullo.Ch14_Complements.Sec1a

/-!
# §14.1.1 as printed

The centrality, character decomposition, dimension, holomorphy, and
extension-independence assertions are recorded as propositions for refutation.
-/

@[expose] public noncomputable section

open Function NumberField
open RiemannMasullo.ArtinWeil

namespace RiemannMasullo
namespace Printed

/-- Paper: Proposition 14.1.1.1(1), p. 525. The printed centrality clause says
that the included abelianization of the Weil subgroup is central in the relative
Weil group. We state the local-field case. -/
def relativeWeil_central : Prop :=
  ∀ (F K W : Type) [Field F] [Field K] [Algebra F K] [IsSepClosed K] [IsGalois F K]
    [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
    (φ : W →ₜ* (K ≃ₐ[F] K)) (_ : DenseRange φ)
    (E : IntermediateField F K) [FiniteDimensional F E] [IsGalois F E] [TopologicalSpace E]
    (r : Eˣ ≃ₜ* TopologicalAbelianization (subgroup φ E))
    (art : Eˣ →ₜ* TopologicalAbelianization E.fixingSubgroup)
    (_ : RealizesArtinMap φ E r art),
    ∀ x : Eˣ, relativeInclusion φ E (r x) ∈ Subgroup.center (Relative φ E)

/-- Paper: Proposition 14.1.1.1(1), p. 525. Take `E = ℂ` over `F = ℝ`.
In the real Weil group `W_ℝ = ℂˣ ⊔ jℂˣ`, conjugation by `j` sends the
kernel element `i` to `-i`. This is erratum R18. -/
theorem relativeWeil_central_false : ¬ relativeWeil_central := by sorry

/-- Paper: §14.1.1, p. 526. The printed claim says that if all elements of
a finite-dimensional relative local Weil representation act semisimply, the
representation is a sum of continuous one-dimensional representations of the
relative group. -/
def relativeWeil_characterSum : Prop :=
  ∀ (F K W V : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [IsSepClosed K] [IsGalois F K]
    [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsModuleTopology ℂ V]
    (φ : W →ₜ* (K ≃ₐ[F] K)) (_ : DenseRange φ)
    (E : IntermediateField F K) [FiniteDimensional F E] [IsGalois F E] [TopologicalSpace E]
    (_ : Eˣ ≃ₜ* TopologicalAbelianization (subgroup φ E))
    (ρ : Representation ℂ (Relative φ E) V)
    (_ : ∀ x : V, Continuous (fun g ↦ ρ g x))
    (_ : ∀ g, Module.End.IsSemisimple (ρ g)),
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
      (c : Fin (Module.finrank ℂ V) → QuasiCharacter (Relative φ E)),
      ∀ g j, ρ g (b j) = c j g • b j

/-- Paper: §14.1.1, p. 526. Use the splitting field of `X³ - 2` over
`ℚ₂`. Its Galois group is `S₃`, whose standard irreducible representation
on the complex plane of triples of sum zero inflates to a relative Weil
representation. Every element acts with finite order and there is no invariant
line. This is erratum R19. -/
theorem relativeWeil_characterSum_false : ¬ relativeWeil_characterSum := by sorry

/-- Paper: §14.1.1 before (14.1.1.7), p. 527. The printed pullback of the
inertia invariants to the multiplicative group of the upper local field is a
sum of unramified characters indexed by the dimension of the ambient space.
The local degree is supplied at the relative level. -/
def inertia_characterCount : Prop :=
  ∀ (F K W V : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [IsSepClosed K] [IsGalois F K]
    [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsModuleTopology ℂ V]
    (φ : W →ₜ* (K ≃ₐ[F] K)) (_ : DenseRange φ)
    (E : IntermediateField F K) [FiniteDimensional F E] [IsGalois F E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (r : Eˣ ≃ₜ* TopologicalAbelianization (subgroup φ E))
    (deg : Relative φ E →* Multiplicative ℤ) (_ : Surjective deg)
    (ρ : Representation ℂ (Relative φ E) V)
    (_ : ∀ x : V, Continuous (fun g ↦ ρ g x))
    (_ : ∀ g, Module.End.IsSemisimple (ρ g)),
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ (inertiaInvariants deg ρ))
      (c : Fin (Module.finrank ℂ V) → QuasiCharacter Eˣ),
      (∀ u j, ρ (relativeInclusion φ E (r u)) (b j : V) = c j u • (b j : V)) ∧
        ∀ j (u : Eˣ), ValuativeRel.valuation E (u : E) = 1 → c j u = 1

/-- Paper: Equation (14.1.1.7) and preceding paragraph, p. 527. In the
`S₃` example over `ℚ₂`, inertia has image the three-cycle subgroup.
A three-cycle fixes only zero on the plane of triples of sum zero. The invariant
space has dimension zero while the printed character count is two (R20). -/
theorem inertia_characterCount_false : ¬ inertia_characterCount := by sorry

/-- Paper: Equation (14.1.1.7), p. 527. Even at the trivial relative level
the printed formula asserts that the finite factor of an unramified
one-dimensional representation is holomorphic throughout `Re s > 0`.
The unramified Frobenius value is an arbitrary nonzero complex scalar. -/
def unramifiedEulerFactor_holomorphic : Prop :=
  ∀ (q : ℕ) (_ : 1 < q) (a : ℂˣ),
    AnalyticOnNhd ℂ (fun s : ℂ ↦ (1 - (a : ℂ) * (q : ℂ) ^ (-s))⁻¹)
      {s | 0 < s.re}

/-- Paper: Equation (14.1.1.7), p. 527. Take `ℚ₂` with the unramified
character `|·|⁻¹`. At Frobenius its value is two, and the factor
`(1 - 2^(1-s))⁻¹` has a pole at `s = 1`. -/
theorem unramifiedEulerFactor_holomorphic_false : ¬ unramifiedEulerFactor_holomorphic := by sorry

/-- Paper: §14.1.1, p. 527. At the real place and the trivial relative
level, the printed dichotomy requires the relative group to be `ℂˣ` or a
central extension of the complex square roots of unity by `ℂˣ`.
Its actual group at this level is `ℝˣ`. -/
def trivialRealRelativeGroup : Prop :=
  Nonempty (ℝˣ ≃ₜ* ℂˣ) ∨
    ∃ (i : ℂˣ →ₜ* ℝˣ) (p : ℝˣ →ₜ* rootsOfUnity 2 ℂ),
      Injective i ∧ Surjective p ∧ i.toMonoidHom.range = p.toMonoidHom.ker ∧
        ∀ z, i z ∈ Subgroup.center ℝˣ

/-- Paper: §14.1.1, p. 527. For `E = F = ℝ` neither alternative holds.
The element `i` has order four in `ℂˣ`, while the only real roots of
unity are `1` and `-1`, so there is no injection `ℂˣ → ℝˣ`. -/
theorem trivialRealRelativeGroup_false : ¬ trivialRealRelativeGroup := by sorry

/-- Paper: Equations (14.1.1.8)–(14.1.1.9), p. 527. Specialize the asserted
level-independence to the trivial representation over `ℚ`, using the exact
products over the upper-field places. The Chapter 3 completed trivial Hecke
products express these particular printed products. -/
def upperFieldEulerProduct_invariant_trivialRat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E],
    ∃ A > (1 : ℝ), ∀ (s : {z : ℂ | 1 < z.re}), A < (s : ℂ).re →
      completedHeckeL (F := E) 1 s = completedHeckeL (F := ℚ) 1 s

/-- Paper: Equations (14.1.1.8)–(14.1.1.9), p. 527. Take `E = ℚ(√5)`.
The printed products for the trivial representation are `Γℝ(s) ζ(s)` at
the trivial level and `Γℝ(s)² ζ_E(s)` at the quadratic level. Both zeta
series tend to one on the positive real axis, while `Γℝ(s)` tends to
infinity. The products cannot agree on any right half-plane (R21). -/
theorem upperFieldEulerProduct_invariant_trivialRat_false :
    ¬ upperFieldEulerProduct_invariant_trivialRat := by sorry

end Printed
end RiemannMasullo
