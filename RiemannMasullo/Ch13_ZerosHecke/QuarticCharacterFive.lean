module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum

/-!
# The oriented quartic Dirichlet character modulo five

The two primitive quartic characters modulo five are distinguished by their value at two.
Here that value is `Complex.I`. The real part counts the two real residue classes with
opposite signs.
-/

public noncomputable section

namespace RiemannMasullo

private def quarticFiveValue (a : ZMod 5) : ℂ :=
  match a.val with
  | 1 => 1
  | 2 => Complex.I
  | 3 => -Complex.I
  | 4 => -1
  | _ => 0

private theorem quarticFive_cases (a : ZMod 5) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 :=
  (by decide : ∀ a : ZMod 5, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) a

/-- The Dirichlet character modulo five sending the generator two to `Complex.I`. -/
def quarticCharacterFive : DirichletCharacter ℂ 5 where
  toFun := quarticFiveValue
  map_one' := rfl
  map_mul' := by
    intro a b
    rcases quarticFive_cases a with rfl | rfl | rfl | rfl | rfl <;>
      rcases quarticFive_cases b with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [quarticFiveValue, ZMod.val_mul, ZMod.val_ofNat, ZMod.val_one_eq_one_mod,
        mul_neg, neg_mul, Complex.I_mul_I]
  map_nonunit' := by
    intro a ha
    let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain rfl : a = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using ha
    rfl

/-- The complex values on all five residue classes, including the ramified class zero. -/
theorem quarticCharacterFive_values :
    quarticCharacterFive 0 = 0 ∧ quarticCharacterFive 1 = 1 ∧
      quarticCharacterFive 2 = Complex.I ∧ quarticCharacterFive 3 = -Complex.I ∧
      quarticCharacterFive 4 = -1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every multiple of the conductor, including the prime five itself, has character value zero. -/
theorem quarticCharacterFive_apply_of_five_dvd {n : ℕ} (hn : 5 ∣ n) :
    quarticCharacterFive (n : ZMod 5) = 0 := by
  rw [(ZMod.natCast_eq_zero_iff n 5).mpr hn, quarticCharacterFive_values.1]

/-- The real component is supported on the two real unit classes, with opposite signs. -/
theorem quarticCharacterFive_re (a : ZMod 5) :
    (quarticCharacterFive a).re = if a = 1 then 1 else if a = 4 then -1 else 0 := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := quarticCharacterFive_values
  rcases quarticFive_cases a with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [h₀, h₁, h₂, h₃, h₄] <;> first | rfl | decide

/-- The real part evaluated on a natural integer, in terms of its remainder modulo five. -/
theorem quarticCharacterFive_re_natCast (n : ℕ) :
    (quarticCharacterFive (n : ZMod 5)).re = if n % 5 = 1 then 1 else if n % 5 = 4 then -1 else 0 := by
  rw [quarticCharacterFive_re]
  have h₁ : (n : ZMod 5) = 1 ↔ n % 5 = 1 := ZMod.natCast_eq_natCast_iff' n 1 5
  have h₄ : (n : ZMod 5) = 4 ↔ n % 5 = 4 := ZMod.natCast_eq_natCast_iff' n 4 5
  simp only [h₁, h₄]

/-- The order of the character itself in the group of Dirichlet characters is four. -/
theorem quarticCharacterFive_orderOf : orderOf quarticCharacterFive = 4 := by
  have hu : IsUnit (2 : ZMod 5) := (ZMod.isUnit_iff_coprime 2 5).mpr (by decide)
  have h₂ : quarticCharacterFive^2 ≠ 1 := by
    intro h
    have hh := congrArg (fun χ : DirichletCharacter ℂ 5 ↦ χ 2) h
    change (quarticCharacterFive ^ 2) 2 = (1 : DirichletCharacter ℂ 5) 2 at hh
    rw [MulChar.pow_apply' _ (by decide : 2 ≠ 0), quarticCharacterFive_values.2.2.1,
      Complex.I_sq, MulChar.one_apply hu] at hh
    norm_num at hh
  have h₄ : quarticCharacterFive^4 = 1 := by
    simpa only [ZMod.card_units_eq_totient, show Nat.totient 5 = 4 by decide] using
      quarticCharacterFive.pow_card_eq_one
  exact orderOf_eq_prime_pow (p := 2) (n := 1) h₂ h₄

/-- Its exact conductor is five. -/
theorem quarticCharacterFive_isPrimitive : quarticCharacterFive.IsPrimitive := by
  apply ((Nat.dvd_prime Nat.prime_five).mp quarticCharacterFive.conductor_dvd_level).resolve_left
  intro h
  have ho := quarticCharacterFive_orderOf
  rw [quarticCharacterFive.eq_one_iff_conductor_eq_one.mpr h, orderOf_one] at ho
  contradiction

end RiemannMasullo
