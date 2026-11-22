module

public import RiemannMasullo.Ch02_AdelicTheta.Sec1

/-! # Chapter 2.1: the printed Schwartz–Bruhat decomposition -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter NumberField IsDedekindDomain
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

/-- Paper: Lemma 2.1.3.2(3), p. 68. As printed: every adelic Schwartz–Bruhat function
is a nonempty finite linear combination of products of archimedean Schwartz functions
and finite adelic rectangle indicators whose factors are compact additive subgroups,
equal to the local integer ring at almost every finite place.
`adeleSchwartz_eq_sum_compactOpen_rectangles` uses compact open sets. See ERRATA F11. -/
def Printed.adeleSchwartz_eq_sum_compactSubgroup_rectangles : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ(𝔸[F])),
    ∃ (r : ℕ) (c : Fin r → ℂ) (arch : Fin r → ℬ(InfiniteAdeleRing F))
      (K : Fin r → (v : Places(F)) → AddSubgroup (v.adicCompletion F))
      (φ : Fin r → ℬ(𝔸[F])),
      1 ≤ r ∧
      (∀ i, (∀ v, IsCompact (K i v : Set (v.adicCompletion F))) ∧
        (∀ᶠ v in cofinite,
          (K i v : Set (v.adicCompletion F)) = (v.adicCompletionIntegers F : Set _)) ∧
        ∀ x : 𝔸[F], φ i (Multiplicative.ofAdd x) =
          arch i (Multiplicative.ofAdd x.1) *
            Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K i v} (fun _ ↦ (1 : ℂ)) x.2) ∧
      f = ∑ i, c i • φ i

/-- Paper: Lemma 2.1.3.2(3), p. 68. Over ℚ use the real Gaussian, the indicator of
`1 + 3ℤ₃` at 3 and the indicators of ℤₚ at every other prime. This is Schwartz–Bruhat.
At the adelic point with real coordinate 0, 3-adic coordinate 1 and other finite
coordinates 0 it has value 1. Changing the 3-adic coordinate to −1 gives value 0.
Every product allowed in the printed decomposition is invariant under this change,
because an additive subgroup is invariant under negation. -/
theorem Printed.adeleSchwartz_eq_sum_compactSubgroup_rectangles_false :
    ¬ Printed.adeleSchwartz_eq_sum_compactSubgroup_rectangles := by sorry

end RiemannMasullo
