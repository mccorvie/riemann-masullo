module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Constructions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order

/-!
# Rational S-units do not accumulate after removing the positive real

(12.2.2.1), p. 508, forces a nonidentity scalar weight when nonidentity subgroup
elements can be moved into every neighborhood of the identity by the identity
component. Over a real quadratic field a unit of infinite order does this. Over
`ℚ` the sign and the valuations are discrete coordinates, split from the
positive real. Those coordinates cannot be moved by the identity component, so
the forcing hypothesis fails for rational `S`-units.
-/

@[expose] public section

open Set Topology

namespace RiemannMasullo

/-- The log-absolute value, together with one discrete integer coordinate for
each invariant that remains after it is split off: the valuations at the
primes in a finite set, and the sign. -/
abbrev RatSUnitShape (S : Type*) := ℝ × (S → ℤ)

/-- Over `ℚ`, a nonidentity tuple of sign and valuation data cannot be moved
into every neighborhood of the identity by the positive-real component. -/
theorem not_ratSUnitShape_component_accumulation (S : Type*) [Finite S] :
    ¬ ∀ U : Set (RatSUnitShape S), IsOpen U → (0 : RatSUnitShape S) ∈ U →
      ∃ v : S → ℤ, v ≠ 0 ∧ ∃ c ∈ connectedComponent (0 : RatSUnitShape S),
        c + (0, v) ∈ U := by
  intro hacc
  let U : Set (RatSUnitShape S) := {g | g.2 = 0}
  have hopen : IsOpen U :=
    (isOpen_discrete ({0} : Set (S → ℤ))).preimage continuous_snd
  have hzero : (0 : RatSUnitShape S) ∈ U := by simp [U]
  obtain ⟨v, hv, c, hc, hcu⟩ := hacc U hopen hzero
  have hc2 : c.2 = 0 := by
    have hprod : connectedComponent (0 : RatSUnitShape S) =
        connectedComponent (0 : ℝ) ×ˢ connectedComponent (0 : S → ℤ) :=
      connectedComponent_prod (0 : ℝ) (0 : S → ℤ)
    have hc' : c ∈ connectedComponent (0 : ℝ) ×ˢ connectedComponent (0 : S → ℤ) := by
      simpa [hprod] using hc
    simpa [connectedComponent_eq_singleton (0 : S → ℤ)] using hc'.2
  have hv0 : v = 0 := by
    have : (c + (0, v)).2 = 0 := by simpa [U] using hcu
    simpa [hc2] using this
  exact hv hv0

end RiemannMasullo
