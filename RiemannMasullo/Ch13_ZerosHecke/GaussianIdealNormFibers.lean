module

public import RiemannMasullo.ForMathlib.NumberTheory.GaussianInt.PrimeIdeals
import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Four generators of each Gaussian ideal of positive norm

Multiplication by the four Gaussian units accounts for all the generators of
any nonzero ideal in the Euclidean ring of Gaussian integers. Consequently the
number of ideals of absolute norm `n > 0` is one quarter of the number of
ordered, signed representations `a ^ 2 + b ^ 2 = n`. The ideal subtype is the
one used for the coefficients of the Dedekind zeta function.
-/

public noncomputable section

namespace RiemannMasullo

private theorem gaussianNorm_eq_iff (z : GaussianInt) (n : ℕ) :
    z.norm.natAbs = n ↔ z.re ^ 2 + z.im ^ 2 = (n : ℤ) := by
  rw [← Nat.cast_inj (R := ℤ), GaussianInt.abs_natCast_norm]
  simp [Zsqrtd.norm_def, pow_two]

/-- Every Gaussian norm fiber is finite, including at zero. -/
theorem gaussianNormFiber_finite (n : ℕ) : Finite {z : GaussianInt // z.norm.natAbs = n} := by
  let box := Set.Icc (-(n : ℤ)) (n : ℤ)
  have coord (a : ℤ) (ha : a.natAbs ≤ n) : a ∈ box := by
    apply abs_le.mp
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr ha)
  let f (z : {z : GaussianInt // z.norm.natAbs = n}) : box × box :=
    let h := (GaussianInt.natAbs_norm_eq z.val).symm.trans z.property
    (⟨z.val.re, coord _ ((Nat.le_mul_self _).trans (by omega))⟩,
     ⟨z.val.im, coord _ ((Nat.le_mul_self _).trans (by omega))⟩)
  exact Finite.of_injective f fun z w h ↦ Subtype.ext <| Zsqrtd.ext
    (congrArg (fun v : box × box ↦ (v.1 : ℤ)) h)
    (congrArg (fun v : box × box ↦ (v.2 : ℤ)) h)

/-- Choosing a generator embeds every absolute ideal norm fiber in the finite element fiber. -/
theorem gaussianIdealNormFiber_finite (n : ℕ) :
    Finite {I : Ideal GaussianInt // I.absNorm = n} := by
  let := gaussianNormFiber_finite n
  let gen (I : {I : Ideal GaussianInt // I.absNorm = n}) :
      {z : GaussianInt // z.norm.natAbs = n} :=
    ⟨Submodule.IsPrincipal.generator I.val, by
      rw [← GaussianInt.absNorm_span, Ideal.span_singleton_generator, I.property]⟩
  apply Finite.of_injective gen
  intro I J h
  exact Subtype.ext <| I.val.span_singleton_generator.symm.trans <|
    (congrArg (fun z ↦ Ideal.span {Subtype.val z}) h).trans J.val.span_singleton_generator

/-- The Gaussian integers of norm one are the four lattice points on the unit circle. -/
theorem gaussianNormFiber_one_card : Nat.card {z : GaussianInt // z.norm.natAbs = 1} = 4 := by
  let s : Finset GaussianInt := {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩}
  have hs (z : GaussianInt) : z.norm.natAbs = 1 ↔ z ∈ s := by
    rw [gaussianNorm_eq_iff]
    obtain ⟨a, b⟩ := z
    simp only [s, Finset.mem_insert, Finset.mem_singleton, Zsqrtd.mk.injEq, Nat.cast_one]
    constructor
    · intro h
      by_cases ha : a = 0
      · subst a
        have hb : b = 1 ∨ b = -1 := sq_eq_one_iff.mp (by simpa using h)
        rcases hb with rfl | rfl <;> simp
      · have hb : b = 0 := by
          by_contra hb
          have := sq_pos_of_ne_zero ha
          have := sq_pos_of_ne_zero hb
          omega
        subst b
        have ha' : a = 1 ∨ a = -1 := sq_eq_one_iff.mp (by simpa using h)
        rcases ha' with rfl | rfl <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide
  rw [Nat.card_congr (Equiv.subtypeEquivRight hs), Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

/-- The Gaussian unit group has exactly four elements. -/
theorem gaussianUnits_card : Nat.card GaussianIntˣ = 4 := by
  let e : GaussianIntˣ ≃ {z : GaussianInt // z.norm.natAbs = 1} :=
    { toFun := fun u ↦ ⟨u, Zsqrtd.norm_eq_one_iff.mpr u.isUnit⟩
      invFun := fun z ↦ (Zsqrtd.norm_eq_one_iff.mp z.property).unit
      left_inv := fun u ↦ Units.ext u.isUnit.unit_spec
      right_inv := fun z ↦ Subtype.ext (Zsqrtd.norm_eq_one_iff.mp z.property).unit_spec }
  exact (Nat.card_congr e).trans gaussianNormFiber_one_card

/-- Choosing a generator of each ideal identifies the elements of positive norm
with pairs of an ideal of that norm and a Gaussian unit. -/
def gaussianNormFiberEquiv (n : ℕ) (hn : 0 < n) :
    {z : GaussianInt // z.norm.natAbs = n} ≃
      {I : Ideal GaussianInt // I.absNorm = n} × GaussianIntˣ := by
  let gen (I : {I : Ideal GaussianInt // I.absNorm = n}) := Submodule.IsPrincipal.generator I.val
  have hgen (I) : (gen I).norm.natAbs = n := by
    rw [← GaussianInt.absNorm_span, show Ideal.span {gen I} = I.val from I.val.span_singleton_generator]
    exact I.property
  have hne (I) : gen I ≠ 0 := by
    intro h
    have hh := hgen I
    rw [h, Zsqrtd.norm_zero, Int.natAbs_zero] at hh
    omega
  let f (x : {I : Ideal GaussianInt // I.absNorm = n} × GaussianIntˣ) :
      {z : GaussianInt // z.norm.natAbs = n} :=
    ⟨gen x.1 * (x.2 : GaussianInt), by
      rw [Zsqrtd.norm_mul, Int.natAbs_mul, Zsqrtd.norm_eq_one_iff.mpr x.2.isUnit, mul_one, hgen]⟩
  have hspan (x) : Ideal.span {(f x).val} = x.1.val := calc
    _ = Ideal.span {gen x.1} :=
      Ideal.span_singleton_eq_span_singleton.mpr (associated_mul_unit_left _ _ x.2.isUnit)
    _ = _ := Ideal.span_singleton_generator _
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · rintro ⟨I, u⟩ ⟨J, v⟩ h
    have hIJ : I = J := Subtype.ext <| (hspan (I, u)).symm.trans
      ((congrArg (fun z ↦ Ideal.span {Subtype.val z}) h).trans (hspan (J, v)))
    subst J
    exact Prod.ext rfl <| Units.ext <| mul_left_cancel₀ (hne I) (congrArg Subtype.val h)
  · intro z
    let I : {I : Ideal GaussianInt // I.absNorm = n} :=
      ⟨Ideal.span {z.val}, (GaussianInt.absNorm_span _).trans z.property⟩
    obtain ⟨u, hu⟩ := Submodule.IsPrincipal.associated_generator_span_self z.val
    exact ⟨(I, u), Subtype.ext hu⟩

/-- The ideal coordinate of the norm-fiber equivalence is the principal ideal generated by
the given Gaussian integer. -/
theorem gaussianNormFiberEquiv_ideal (n : ℕ) (hn : 0 < n)
    (z : {z : GaussianInt // z.norm.natAbs = n}) :
    ((gaussianNormFiberEquiv n hn z).1 : Ideal GaussianInt) = Ideal.span {z.val} := by
  obtain ⟨⟨I, u⟩, rfl⟩ := (gaussianNormFiberEquiv n hn).symm.surjective z
  rw [Equiv.apply_symm_apply]
  change I.val = Ideal.span {Submodule.IsPrincipal.generator I.val * (u : GaussianInt)}
  exact ((Ideal.span_singleton_eq_span_singleton.mpr
    (associated_mul_unit_left _ _ u.isUnit)).trans I.val.span_singleton_generator).symm

/-- A positive Gaussian norm occurs four times for each ideal of that absolute norm. -/
theorem gaussianIdealNorm_count (n : ℕ) (hn : 0 < n) :
    Nat.card {z : GaussianInt // z.norm.natAbs = n} =
      4 * Nat.card {I : Ideal GaussianInt // I.absNorm = n} := by
  rw [Nat.card_congr (gaussianNormFiberEquiv n hn), Nat.card_prod, gaussianUnits_card, mul_comm]

/-- The real and imaginary coordinates give all ordered, signed two-square representations. -/
def gaussianTwoSquareEquiv (n : ℕ) : {z : GaussianInt // z.norm.natAbs = n} ≃
    {v : ℤ × ℤ // v.1 ^ 2 + v.2 ^ 2 = (n : ℤ)} := by
  let e : GaussianInt ≃ ℤ × ℤ :=
    ⟨fun z ↦ (z.re, z.im), fun v ↦ ⟨v.1, v.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact e.subtypeEquiv fun z ↦ gaussianNorm_eq_iff z n

/-- Signed pairs and Gaussian integers have the same norm multiplicity at every integer. -/
theorem gaussianTwoSquare_count (n : ℕ) :
    Nat.card {v : ℤ × ℤ // v.1 ^ 2 + v.2 ^ 2 = (n : ℤ)} =
      Nat.card {z : GaussianInt // z.norm.natAbs = n} :=
  (Nat.card_congr (gaussianTwoSquareEquiv n)).symm

/-- The Gaussian ideal-counting coefficient at a positive integer is one quarter
of its number of ordered, signed representations as a sum of two squares. -/
theorem gaussianIdealNorm_count_eq_r2_div (n : ℕ) (hn : 0 < n) :
    Nat.card {I : Ideal GaussianInt // I.absNorm = n} =
      Nat.card {v : ℤ × ℤ // v.1 ^ 2 + v.2 ^ 2 = (n : ℤ)} / 4 := by
  rw [gaussianTwoSquare_count, gaussianIdealNorm_count n hn]
  omega

end RiemannMasullo
