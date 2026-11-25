module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.Basic

/-!
# A supersingular curve of trace zero over `F₉`

Page 536 gives a supersingular elliptic curve over `F_{p²}` as an example whose
quadratic character has a double zero. The curves with Frobenius trace `±2p` do.
The curve below has trace zero, so its two zeros are distinct. This is the
computation, not a claim that the sentence is false.
-/

@[expose] public section

namespace RiemannMasullo

/-- `F₉` as pairs `(re, im)` over `F₃`, with `i = (0, 1)` and `i² = -1`. -/
abbrev F9Pairs := ZMod 3 × ZMod 3

/-- Addition in the coordinate model of `F₉`. -/
def f9Add (x y : F9Pairs) : F9Pairs := (x.1 + y.1, x.2 + y.2)

/-- Multiplication in the coordinate model of `F₉`. -/
def f9Mul (x y : F9Pairs) : F9Pairs :=
  (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Square in the coordinate model of `F₉`. -/
def f9Sq (x : F9Pairs) : F9Pairs := f9Mul x x

/-- Cube in the coordinate model of `F₉`. -/
def f9Cube (x : F9Pairs) : F9Pairs := f9Mul (f9Sq x) x

/-- The class of `i`. -/
def f9i : F9Pairs := (0, 1)

/-- `i² = -1` in the coordinate model. -/
theorem f9i_sq : f9Mul f9i f9i = (-1, 0) := by decide

/-- The number of affine solutions of `y² = x³ + A x`. -/
def f9AffineCount (A : F9Pairs) : ℕ :=
  (Finset.univ.filter fun t : F9Pairs × F9Pairs =>
    f9Sq t.2 = f9Add (f9Cube t.1) (f9Mul A t.1)).card

/-- The curve `y² = x³ + (1+i) x` has nine affine points over this model of `F₉`. -/
theorem f9_one_add_i_affinePoints : f9AffineCount (1, 1) = 9 := by decide

/-- Paper: §14.2, p. 536. With the point at infinity, `y² = x³ + (1+i) x` has ten
rational points over `F₉`. The trace is `a = 9 + 1 - 10 = 0`, so the L-polynomial
is `1 + 9 T²`. Its discriminant is `-36`, so the two complex roots are simple. -/
theorem f9_one_add_i_tenPoints_LPolynomial_distinctRoots :
    f9AffineCount (1, 1) + 1 = 10 ∧ ((9 + 1 - 10 : ℤ) = 0) ∧
      (0 : ℤ) ^ 2 - 4 * 1 * 9 ≠ 0 := by
  refine ⟨?_, by decide, by decide⟩
  simp [f9_one_add_i_affinePoints]

end RiemannMasullo
