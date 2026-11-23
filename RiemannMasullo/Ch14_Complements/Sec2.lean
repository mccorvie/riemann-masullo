module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# §§14.2–14.3: Global function fields and higher rank

Masullo, pp. 534–536. The Euler product (14.2.0.1) uses every closed point of
the smooth projective curve, including those above infinity for a map to the
projective line.
-/

@[expose] public section

namespace RiemannMasullo

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Paper: (14.2.0.1), p. 534. The zeta Euler product of a smooth projective
geometrically connected curve over a finite field multiplies the reciprocal
factors determined by the sizes of the residue fields of its closed points.
Deviation: The product is defined on `Re(s) > 1`, its half-plane of absolute
convergence. A smooth proper curve over a field is projective. -/
noncomputable def curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' x : {x : X // IsClosed ({x} : Set X)},
    (1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s.val))⁻¹

/-- Paper: (14.2.0.1), p. 534. On `Re(s) > 1` the finite products over closed
points converge to the zeta Euler product.
Deviation: `HasProd` asserts convergence of the product in the display. -/
theorem hasProd_curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun x : {x : X // IsClosed ({x} : Set X)} ↦
      (1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s.val))⁻¹)
      (curveZetaEulerProduct f s) := by sorry

-- TODO(paper-gap): On p. 534 the common poles of the local factors include
-- every 2πin / log(q). The paper gives no function-field Sobolev quotient or
-- trace approximation that shows how these poles constrain its Mellin jets.
-- The comparison in §7.1.3 uses distinct rational residue characteristics.
-- The multiplicity in §11.2.2 counts contributing places above one prime.

/-- Paper: §14.2, last paragraph, p. 534. For each degree there are finitely
many closed points whose residue field has that degree over the base field.
Deviation: Each fixed degree gives finitely many identical factors. Their
counts grow as the degree tends to infinity, as described on p. 535. -/
theorem curveZeta_closedPointsOfDegree_finite (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : X | IsClosed ({x} : Set X) ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Finite := by sorry

-- TODO(paper-gap): On p. 535 the upper bound m Bₘ ≤ Nₘ − N₁ applies for m > 1.
-- The asserted asymptotic also requires a lower estimate. It follows from
-- the Weil estimate for Nₘ together with Nₘ = ∑_{d ∣ m} d B_d.

-- TODO(paper-gap): The comparison on p. 535 refers to the missing Theorem
-- 13.3.1.2. Equation (5.3.1.5) supplies a finite-place principal-value
-- operator. The function-field completion, convergence in the topology of
-- uniform convergence on bounded sets, and trace identity are unspecified.

-- TODO(paper-gap): The gonality equality on p. 535 fails for the Hermitian
-- quartic y³ + y = x⁴ over 𝔽₉. Its genus is three and projection to x has
-- degree three. It is maximal and its sole Frobenius eigenvalue has
-- multiplicity six, which still gives the intended obstruction.

-- TODO(paper-gap): The supersingular example on p. 536 needs a choice of
-- curve with equal Frobenius eigenvalues. Over 𝔽₉, y² = x³ − x has numerator
-- (1 + 3T)². The supersingular curve y² = x³ + (1 + i)x with i² = −1 has
-- numerator 1 + 9T² and gives simple zeros for the quadratic cover's L-function.

-- TODO(paper-gap): §14.3, p. 536 gives n[F : ℚ] as a proposed multiplicity
-- bound for generic zeros. The meaning of generic and the higher-rank
-- argument are left open by the revision note in footnote 2 (ERRATA M43).

end RiemannMasullo
