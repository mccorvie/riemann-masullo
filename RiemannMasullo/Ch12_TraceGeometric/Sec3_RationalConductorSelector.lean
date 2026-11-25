module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalCongruence
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-! # The finite conductor selector on rational angular residues

For compatible unit residues, grouping all characters of one level by their
primitive conductor gives the divisor sum. Möbius inversion followed by the
finite Dirichlet hyperbola identity gives the cumulative primitive selector.
-/

@[expose] public noncomputable section

open DirichletCharacter ArithmeticFunction Finset
open scoped BigOperators ComplexConjugate

namespace RiemannMasullo.ConductorSelector

/-- The unnormalized sum over exactly the primitive rows at one conductor. -/
def primitiveSum {q : ℕ} (u : (ZMod q)ˣ) : ℂ := by
  classical
  exact ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, χ (u : ZMod q)

/-- Integer summatory Möbius function, including its value at zero. -/
def mertens (n : ℕ) : ℤ := ∑ m ∈ Finset.Ioc 0 n, ArithmeticFunction.moebius m

/-- Compatible values need only agree after evaluation by the lower-level characters. -/
def EvaluationCompatible (u : (q : ℕ) → (ZMod q)ˣ) : Prop :=
  ∀ {d q : ℕ} (hdq : d ∣ q), q ≠ 0 → ∀ χ : DirichletCharacter ℂ d,
    (χ.changeLevel hdq) (u q : ZMod q) = χ (u d : ZMod d)

/-- The complete character sum at a positive level is the sum of the primitive sums
at its divisors. Coincident values still contribute once per primitive character. -/
theorem sum_divisors_primitiveSum (u : (q : ℕ) → (ZMod q)ˣ) (hu : EvaluationCompatible u)
    {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, primitiveSum (u d) = if u q = 1 then (q.totient : ℂ) else 0 := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have hfiber (d : ℕ) (hd : d ∈ q.divisors) :
      primitiveSum (u d) = ∑ χ : DirichletCharacter ℂ q with χ.conductor = d, χ (u q : ZMod q) := by
    let hdq := Nat.dvd_of_mem_divisors hd
    refine Finset.sum_bij (fun χ _ ↦ χ.changeLevel hdq) ?_ ?_ ?_ ?_
    · intro χ hχ
      have hpr : χ.IsPrimitive := (mem_filter.mp hχ).2
      exact mem_filter.mpr ⟨mem_univ _, (χ.conductor_changeLevel hdq).trans hpr⟩
    · intro χ _ χ' _ heq
      exact DirichletCharacter.changeLevel_injective hdq heq
    · intro χ hχ
      have hd' : χ.conductor = d := (mem_filter.mp hχ).2
      subst d
      exact ⟨χ.primitiveCharacter, mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩,
        χ.changeLevel_primitiveCharacter⟩
    · intro χ _
      exact (hu hdq hq.ne' χ).symm
  calc
    _ = ∑ d ∈ q.divisors, ∑ χ : DirichletCharacter ℂ q with χ.conductor = d,
        χ (u q : ZMod q) := sum_congr rfl hfiber
    _ = ∑ χ : DirichletCharacter ℂ q, χ (u q : ZMod q) :=
      Finset.sum_fiberwise_of_maps_to (fun χ _ ↦ Nat.mem_divisors.mpr
        ⟨χ.conductor_dvd_level, hq.ne'⟩) _
    _ = _ := by
      have hr : (u q : ZMod q) = 1 ↔ u q = 1 := ⟨fun h ↦ Units.ext h, fun h ↦ by rw [h]; rfl⟩
      simpa only [hr] using DirichletCharacter.sum_characters_eq ℂ (u q : ZMod q)

/-- Pointwise Möbius inversion at each positive conductor, before summing in `Q`. -/
theorem primitiveSum_eq_moebius (u : (q : ℕ) → (ZMod q)ˣ) (hu : EvaluationCompatible u)
    {q : ℕ} (hq : 0 < q) :
    primitiveSum (u q) = ∑ v ∈ q.divisorsAntidiagonal,
      (ArithmeticFunction.moebius v.1 : ℂ) * (if u v.2 = 1 then (v.2.totient : ℂ) else 0) := by
  classical
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n hn ↦ sum_divisors_primitiveSum u hu (q := n) hn) q hq).symm

/-- Summing each positive primitive conductor once gives an integer-valued combination
of the identity cylinders at the lower moduli. The formula also holds for `Q = 0`. -/
theorem sum_primitiveSum_eq_mertens (u : (q : ℕ) → (ZMod q)ˣ) (hu : EvaluationCompatible u)
    (Q : ℕ) :
    ∑ q ∈ Finset.Ioc 0 Q, primitiveSum (u q) =
      ∑ d ∈ Finset.Ioc 0 Q, if u d = 1 then (d.totient : ℂ) * (mertens (Q / d) : ℂ) else 0 := by
  classical
  let A : ArithmeticFunction ℂ := ⟨fun d ↦ if u d = 1 then (d.totient : ℂ) else 0, by simp⟩
  let M : ArithmeticFunction ℂ := (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
  have hc (q : ℕ) (hq : 0 < q) : primitiveSum (u q) = (A * M) q := by
    rw [mul_comm, ArithmeticFunction.mul_apply]
    exact primitiveSum_eq_moebius u hu hq
  calc
    _ = ∑ q ∈ Finset.Ioc 0 Q, (A * M) q := sum_congr rfl fun q hq ↦ hc q (mem_Ioc.mp hq).1
    _ = ∑ d ∈ Finset.Ioc 0 Q, A d * ∑ m ∈ Finset.Ioc 0 (Q / d), M m :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum A M Q
    _ = _ := by
      apply sum_congr rfl
      intro d _
      by_cases h : u d = 1 <;> simp [A, M, mertens, h, ArithmeticFunction.intCoe_apply]

/-- An ordinary compatible system of units satisfies the evaluation condition. -/
theorem EvaluationCompatible.of_unitsMap (u : (q : ℕ) → (ZMod q)ˣ)
    (hu : ∀ {d q : ℕ} (hd : d ∣ q), q ≠ 0 → ZMod.unitsMap hd (u q) = u d) :
    EvaluationCompatible u := by
  intro d q hd hq χ
  rw [χ.changeLevel_eq_cast_of_dvd hd (u q), ← ZMod.unitsMap_val hd, hu hd hq]

/-- Each pair in this finite dependent type is one primitive character at its own conductor. -/
abbrev PrimitiveRow (Q : ℕ) :=
  (q : (Finset.Ioc 0 Q)) × {χ : DirichletCharacter ℂ q.val // χ.IsPrimitive}

open scoped Classical in
theorem sum_primitiveRow {M : Type*} [AddCommMonoid M] (Q : ℕ)
    (f : (q : ℕ) → DirichletCharacter ℂ q → M) :
    ∑ r : PrimitiveRow Q, f r.1.val r.2.val =
      ∑ q ∈ Finset.Ioc 0 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, f q χ := by
  classical
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ q : (Finset.Ioc 0 Q), ∑ χ : DirichletCharacter ℂ q.val with χ.IsPrimitive, f q.val χ := by
      refine sum_congr rfl fun q _ ↦ ?_
      exact (Finset.sum_subtype _ (fun χ ↦ by simp) (f q.val)).symm
    _ = _ := Finset.sum_coe_sort (Finset.Ioc 0 Q)
      (fun q : ℕ ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, f q χ)

open NumberFieldKB.Chebotarev.RatIdele NumberField
open scoped NumberField.AdeleRing

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ

/-- The actual rational class residue at every positive level, extended at zero so
the ordinary natural-number divisor sums can use one family. -/
def classUnit (x : Cℚ) (q : ℕ) : (ZMod q)ˣ :=
  if h : q = 0 then 1 else
    have : NeZero q := ⟨h⟩
    ConductorCylinder.classResidue q x

@[simp] theorem classUnit_eq (x : Cℚ) (q : ℕ) [NeZero q] :
    classUnit x q = ConductorCylinder.classResidue q x := by simp [classUnit, NeZero.ne q]

theorem classUnit_evaluationCompatible (x : Cℚ) : EvaluationCompatible (classUnit x) := by
  intro d q hd hq χ
  let : NeZero q := ⟨hq⟩
  let : NeZero d := ⟨fun h ↦ hq (by simpa [h] using hd)⟩
  simp only [classUnit_eq]
  have hchar : ratDirichletChar q (χ.changeLevel hd) x = ratDirichletChar d χ x := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [ratDirichletChar_mk, ratDirichletChar_mk, ideleChar_changeLevel hd χ]
  have hval := congrArg (fun z : ℂˣ ↦ (z : ℂ)) hchar
  change ((ratDirichletChar q (χ.changeLevel hd) x : ℂˣ) : ℂ) =
    ((ratDirichletChar d χ x : ℂˣ) : ℂ) at hval
  rw [ConductorCylinder.ratDirichletChar_eq_conj, ConductorCylinder.ratDirichletChar_eq_conj] at hval
  exact (starRingEnd ℂ).injective hval

/-- Reduction of the native class residue agrees at every pair of positive divisor levels. -/
theorem classResidue_unitsMap {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q) (x : Cℚ) :
    ZMod.unitsMap hd (ConductorCylinder.classResidue q x) = ConductorCylinder.classResidue d x := by
  classical
  let a := ZMod.unitsMap hd (ConductorCylinder.classResidue q x)
  let b := ConductorCylinder.classResidue d x
  change a = b
  have hc (χ : DirichletCharacter ℂ d) : χ (a : ZMod d) = χ (b : ZMod d) := by
    simpa only [a, b, classUnit_eq, ZMod.unitsMap_val, DirichletCharacter.changeLevel_eq_cast_of_dvd]
      using classUnit_evaluationCompatible x hd (NeZero.ne q) χ
  by_contra hab
  have hneq : ((a / b : (ZMod d)ˣ) : ZMod d) ≠ 1 :=
    fun h ↦ hab (div_eq_one.mp (Units.ext h : a / b = 1))
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hneq
  have hunit : χ.toUnitHom a = χ.toUnitHom b := Units.ext (hc χ)
  have hmap : χ.toUnitHom (a / b) = 1 := (map_div _ _ _).trans (div_eq_one.mpr hunit)
  exact hχ (congrArg Units.val hmap)

/-- The physical selector using class residues and ordinary primitive Dirichlet evaluations. -/
theorem sum_primitiveSum_classUnit (x : Cℚ) (Q : ℕ) :
    ∑ q ∈ Finset.Ioc 0 Q, primitiveSum (classUnit x q) =
      ∑ d ∈ Finset.Ioc 0 Q, if classUnit x d = 1 then
        (d.totient : ℂ) * (mertens (Q / d) : ℂ) else 0 :=
  sum_primitiveSum_eq_mertens _ (classUnit_evaluationCompatible x) Q

/-- The sum of the native unit-valued idèle-class lifts at exactly one positive conductor. -/
def primitiveIdelicSum (x : Cℚ) : ℕ → ℂ
  | 0 => 0
  | q + 1 => by
    classical
    exact ∑ χ : DirichletCharacter ℂ (q + 1) with χ.IsPrimitive, ((ratDirichletChar (q + 1) χ x : ℂˣ) : ℂ)

theorem primitiveIdelicSum_eq_conj (x : Cℚ) {q : ℕ} (hq : 0 < q) :
    primitiveIdelicSum x q = conj (primitiveSum (classUnit x q)) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  simp only [primitiveIdelicSum, primitiveSum, map_sum, classUnit_eq, ConductorCylinder.ratDirichletChar_eq_conj]

/-- The inverse convention in the rational idelic character gives the same signed integer
cylinder kernel, since conjugation fixes its coefficients. -/
theorem sum_primitiveIdelicSum_eq_cylinders (x : Cℚ) (Q : ℕ) :
    ∑ q ∈ Finset.Ioc 0 Q, primitiveIdelicSum x q =
      ∑ d ∈ Finset.Ioc 0 Q, if classUnit x d = 1 then
        (d.totient : ℂ) * (mertens (Q / d) : ℂ) else 0 := by
  classical
  calc
    _ = conj (∑ q ∈ Finset.Ioc 0 Q, primitiveSum (classUnit x q)) := by
      rw [map_sum]
      exact sum_congr rfl fun q hq ↦ primitiveIdelicSum_eq_conj x (mem_Ioc.mp hq).1
    _ = _ := by
      rw [sum_primitiveSum_classUnit, map_sum]
      apply sum_congr rfl
      intro d _
      split_ifs <;> simp

@[simp] theorem primitiveSum_one (u : (ZMod 1)ˣ) : primitiveSum u = 1 := by
  classical
  have hχ (χ : DirichletCharacter ℂ 1) : χ.IsPrimitive := by
    rw [DirichletCharacter.level_one χ]
    exact DirichletCharacter.isPrimitive_one_level_one
  simp only [primitiveSum, filter_true_of_mem (fun χ _ ↦ hχ χ)]
  rw [DirichletCharacter.sum_characters_eq]
  simp [Subsingleton.elim u 1]

end RiemannMasullo.ConductorSelector
