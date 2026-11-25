module

public import RiemannMasullo.Ch14_Complements.Sec2

import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

/-!
# §14.2: a statement that is false as printed

A statement of the paper that turned out to be false is kept here as a proposition, together
with a proof of its negation. Nothing imports this file.
-/

@[expose] public section

namespace RiemannMasullo

/-- The field with nine elements as pairs `(re, im)` of elements of `F_3`, with `i = (0, 1)`
and `i^2 = -1`. -/
abbrev Printed.F9 := ZMod 3 × ZMod 3

/-- Addition in the coordinate model of `F_9`. -/
def Printed.f9Add (x y : Printed.F9) : Printed.F9 := (x.1 + y.1, x.2 + y.2)

/-- Multiplication in the coordinate model of `F_9`. -/
def Printed.f9Mul (x y : Printed.F9) : Printed.F9 :=
  (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Square in the coordinate model of `F_9`. -/
def Printed.f9Sq (x : Printed.F9) : Printed.F9 := Printed.f9Mul x x

/-- Cube in the coordinate model of `F_9`. -/
def Printed.f9Cube (x : Printed.F9) : Printed.F9 := Printed.f9Mul (Printed.f9Sq x) x

/-- The class of `i`. -/
def Printed.f9i : Printed.F9 := (0, 1)

/-- `i^2 = -1` in the coordinate model. -/
lemma Printed.f9i_sq : Printed.f9Mul Printed.f9i Printed.f9i = (-1, 0) := by decide

/-- The number of affine solutions of `y^2 = x^3 + A x`. -/
def Printed.f9AffineCount (A : Printed.F9) : ℕ :=
  (Finset.univ.filter fun t : Printed.F9 × Printed.F9 =>
    Printed.f9Sq t.2 = Printed.f9Add (Printed.f9Cube t.1) (Printed.f9Mul A t.1)).card

/-- `y^2 = x^3 + (1+i) x` has nine affine solutions over this model of `F_9`. -/
lemma Printed.f9AffineCount_one_add_i : Printed.f9AffineCount (1, 1) = 9 := by decide

/-- `y^2 = x^3 - x` has fifteen affine solutions over this model of `F_9`. -/
lemma Printed.f9AffineCount_neg_one : Printed.f9AffineCount (2, 0) = 15 := by decide

/-- Paper: §14.2, p. 536. The curve `y^2 = x^3 - x` over `F_9` has trace `-6`.
Its Weil polynomial is `1 + 6 T + 9 T^2 = (1 + 3 T)^2`, a double zero. This is a
curve for which the printed conclusion holds. The universal claim still fails,
by `Printed.supersingularDoubleCover_doubleZero_false`. -/
theorem Printed.supersingular_x3_sub_x_doubleZero :
    ((9 : ℤ) - Printed.f9AffineCount (2, 0)) ^ 2 = 36 := by
  simp [Printed.f9AffineCount_neg_one]

/-- Paper: §14.2, p. 536. A supersingular elliptic curve over `F_{p^2}`, as a double cover of
the projective line, has an L-function with a double zero.
Deviation: The printed sentence quantifies over every such curve. This proposition is that
assertion for the curves `y^2 = x^3 + A x` with `A ≠ 0` over the model of `F_9` above, which
the printed sentence includes: the `x`-coordinate is a degree-two cover of the line, and
`A ≠ 0` is nonsingularity in characteristic 3 because the derivative of `x^3 + A x` is `A`.
The trace is `a = 9 - N`, where `N` is the number of affine solutions. The projective model
adds one point at infinity, so `a = q + 1 - #E(F_q)`. Supersingularity is `3 ∣ a`. A double
zero of `1 - a T + 9 T^2` is `a^2 = 36`. The printed universal claim implies this
specialization. -/
def Printed.supersingularDoubleCover_doubleZero : Prop :=
  ∀ A : Printed.F9, A ≠ (0, 0) → (3 : ℤ) ∣ ((9 : ℤ) - Printed.f9AffineCount A) →
    ((9 : ℤ) - Printed.f9AffineCount A) ^ 2 = 36

/-- Paper: §14.2, p. 536. The curve `y^2 = x^3 + (1+i) x` over `F_9` has trace zero, so the
divisibility holds, but `0^2 ≠ 36`. Its Weil polynomial `1 + 9 T^2` therefore has distinct
roots. -/
theorem Printed.supersingularDoubleCover_doubleZero_false :
    ¬ Printed.supersingularDoubleCover_doubleZero := by
  intro h
  have hA : ((1, 1) : Printed.F9) ≠ (0, 0) := by decide
  have hdiv : (3 : ℤ) ∣ ((9 : ℤ) - Printed.f9AffineCount (1, 1)) := by
    simp [Printed.f9AffineCount_one_add_i]
  have hsq := h (1, 1) hA hdiv
  simp [Printed.f9AffineCount_one_add_i] at hsq

end RiemannMasullo
