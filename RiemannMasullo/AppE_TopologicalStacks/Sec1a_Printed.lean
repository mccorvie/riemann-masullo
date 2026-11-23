module

public import RiemannMasullo.AppE_TopologicalStacks.Sec1a

/-!
# Appendix E.1.1. Claims that are false as printed
-/

@[expose] public section

namespace RiemannMasullo

universe u

/-- Paper: Lemma E.1.1.3, text following (E.1.1.2), p. 831.
As printed, the ordinals whose von Neumann stages meet a nonempty witness class form a set.
The witness class is parametrized by a predicate on `ZFSet`, as in
`exists_least_vonNeumannStages`. -/
def Printed.vonNeumannWitnessStages_form_set : Prop :=
  ∀ (C : ZFSet.{u} → Prop), (∃ z, C z) →
    ∃ S : ZFSet.{u}, ∀ a : Ordinal.{u},
      a.toZFSet ∈ S ↔ ∃ z ∈ ZFSet.vonNeumann a, C z

/-- Paper: Lemma E.1.1.3, text following (E.1.1.2), p. 831.
Take the witness class consisting of the empty set alone. It meets every positive stage,
so any purported set of witnessing ordinals would contain the ordinal `S.rank + 1`,
whose rank exceeds that of the set `S`. -/
theorem Printed.vonNeumannWitnessStages_form_set_false :
    ¬ Printed.vonNeumannWitnessStages_form_set.{u} := by
  sorry

/-- Paper: Lemma E.1.1.3, text following (E.1.1.3), p. 831.
As printed, the union of the witness classes cut off at the common stage is nonempty.
The classes are parametrized by predicates on `ZFSet`, as in `exists_zfSet_meeting_classes`. -/
def Printed.vonNeumannWitnessUnion_nonempty : Prop :=
  ∀ (I : Type u) (C : I → ZFSet.{u} → Prop), (∀ i, ∃ z, C i z) →
    ∃ (b : Ordinal.{u}) (S : ZFSet.{u}),
      (∀ z, z ∈ S ↔ z ∈ ZFSet.vonNeumann b ∧ ∃ i, C i z) ∧ ∃ z, z ∈ S

/-- Paper: Lemma E.1.1.3, text following (E.1.1.3), p. 831.
For the empty space, the index of pairs `(A, x)` is empty. Take `I = Empty` (lifted to
the index universe). The union is empty at every stage. -/
theorem Printed.vonNeumannWitnessUnion_nonempty_false :
    ¬ Printed.vonNeumannWitnessUnion_nonempty.{u} := by
  sorry

end RiemannMasullo
