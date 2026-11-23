module

public import RiemannMasullo.Ch14_Complements.Sec2

/-! # §14.2: Infinitely many repetitions at a fixed degree -/

@[expose] public section

namespace RiemannMasullo

open AlgebraicGeometry CategoryTheory

universe u

/-- Paper: §14.2, last paragraph, p. 534. For every smooth projective
geometrically connected curve over a finite field and every fixed degree
`m ≥ 0`, infinitely many closed points contribute the Euler factor for that degree.
Deviation: A smooth proper curve over a field is projective. A residue field of
degree `m` has cardinality `q ^ m`, where `q` is the cardinality of the base field. -/
def Printed.curveZeta_closedPointsOfDegree_infinite : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ),
    {x : X | IsClosed ({x} : Set X) ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Infinite

/-- Paper: §14.2, last paragraph, p. 534. The projective line over `𝔽₂`
has exactly three degree-one closed points, namely `0`, `1` and infinity.
They contribute three copies of the corresponding Euler factor. -/
theorem Printed.curveZeta_closedPointsOfDegree_infinite_false :
    ¬ Printed.curveZeta_closedPointsOfDegree_infinite := by sorry

end RiemannMasullo
