module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteJetQuotient
import all RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteJetQuotient

/-! # Forward translation on the actual finite-prime jet quotient

The ambient translation descends to the actual quotient, acts by finite
binomial rows, and its difference from the identity raises the jet filtration. -/

public noncomputable section

open MeasureTheory Set
open scoped NNReal
namespace RiemannMasullo.RationalPacket

variable {X : ℝ} (hX : 0 < X) (T K : Finset ℕ)
  (hT : ∀ p ∈ T, p.Prime) (hK : ∀ p ∈ K, p.Prime) (hd : Disjoint T K)
  {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K.card)

local notation "C" => fixedBoxColumnIntersection hX T K hT hK hd hj hjK
local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxColumnDenominator hX T K hT hK hd hj hjK)
local notation "E" => fixedBoxColumnQuotientEquiv hX T K hT hK hd hj hjK
local notation "b" => T.card + j
local notation "J" => halfLineMellinJet (-Real.log X) 0

private theorem column_oldStage (u : C) : (u : LogL2) ∈ closedStageSubmodule X T
    (fun p hp ↦ (hT p hp).one_lt.le) :=
  ((mem_all_card_closedStageSubmodule_union_iff hX T K hT hK hd hj hjK _).mp
    ((mem_fixedBoxColumnIntersection_iff hX T K hT hK hd hj hjK _).mp u.property)).1

/-- All raw rows before the first quotient coordinate vanish, including the old stage rows. -/
theorem fixedBoxColumnIntersection_jet_zero (u : C) {d : ℕ} (hlt : d < b) : J d u = 0 := by
  by_cases h : d < T.card
  · exact halfLineMellinJet_stage_closure_zero hX T hT d h
      ((mem_closedStageSubmodule_iff X T _ _).mp (column_oldStage hX T K hT hK hd hj hjK u))
  · exact ((mem_all_card_closedStageSubmodule_union_iff hX T K hT hK hd hj hjK _).mp
      ((mem_fixedBoxColumnIntersection_iff hX T K hT hK hd hj hjK _).mp u.property)).2.2 d
        (Nat.le_of_not_lt h) hlt

/-- Restriction of physical forward translation to the simultaneous column intersection. -/
def fixedBoxColumnShift (h : ℝ≥0) : C →L[ℂ] C :=
  ((halfShift h).comp (C).toSubmodule.subtypeL).codRestrict (C).toSubmodule (by
    intro u
    apply (mem_fixedBoxColumnIntersection_iff hX T K hT hK hd hj hjK _).mpr
    intro A hA hc
    exact halfShift_mem_closedStage hX (T ∪ A) _ h.property
      (((mem_fixedBoxColumnIntersection_iff hX T K hT hK hd hj hjK _).mp u.property) A hA hc))

local notation "R" => fixedBoxColumnShift hX T K hT hK hd hj hjK

/-- Descent uses invariance of the actual full union stage, the kernel of the finite jet map. -/
def fixedBoxColumnQuotientShift (h : ℝ≥0) : (C ⧸ N) →L[ℂ] (C ⧸ N) :=
  (N).liftQL ((N).mkQL.comp (R h)) (by
    intro u hu
    change Submodule.Quotient.mk (R h u) = (0 : C ⧸ N)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact halfShift_mem_closedStage hX (T ∪ K) _ h.property hu)

local notation "S" => fixedBoxColumnQuotientShift hX T K hT hK hd hj hjK

@[simp] theorem fixedBoxColumnQuotientShift_zero : S 0 = ContinuousLinearMap.id ℂ _ := by
  ext1 x
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  change (N).mkQL (R 0 u) = (N).mkQL u
  exact congrArg (N).mkQL (Subtype.ext (halfShift_zero (u : LogL2)))

theorem fixedBoxColumnQuotientShift_add (h k : ℝ≥0) : S (h+k) = (S h).comp (S k) := by
  ext1 x
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  change (N).mkQL (R (h+k) u) = (N).mkQL (R h (R k u))
  exact congrArg (N).mkQL (Subtype.ext (halfShift_add (h : ℝ) (k : ℝ) (u : LogL2)))

/-- Exact triangular binomial matrix in *raw* quotient coordinates. -/
theorem fixedBoxColumnQuotientShift_row (h : ℝ≥0) (x : C ⧸ N) (r : Fin (K.card-j)) :
    E (S h x) r = ∑ s : Fin (r.val+1),
      ((b + r.val).choose (b + s.val) : ℂ) * ((h : ℝ) : ℂ)^(r.val-s.val) *
        E x ⟨s.val, lt_of_le_of_lt (Nat.le_of_lt_succ s.isLt) r.isLt⟩ := by
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  change J (b + r.val) (halfShift h (u : LogL2)) = ∑ s : Fin (r.val+1),
    ((b + r.val).choose (b + s.val) : ℂ) * ((h : ℝ) : ℂ)^(r.val-s.val) * J (b+s.val) u
  have hf := halfLineMellinJet_halfShift (a := -Real.log X) (h := (h : ℝ)) (F := (u : LogL2))
    h.property (closedStageSubmodule_supported hX T _ (column_oldStage hX T K hT hK hd hj hjK u))
    (b + r.val)
  rw [hf]
  rw [show b + r.val + 1 = b + (r.val+1) by omega, Finset.sum_range_add,
    Finset.sum_eq_zero (fun i hi ↦ by rw [fixedBoxColumnIntersection_jet_zero hX T K hT hK hd hj hjK u
      (Finset.mem_range.mp hi), mul_zero]), zero_add]
  simp only [Nat.add_sub_add_left]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- The translation difference raises the vanishing filtration one step, with the
exact first surviving row; the latter is asserted only when it exists. -/
theorem fixedBoxColumnQuotientShift_sub_filtration (h : ℝ≥0) (x : C ⧸ N) (r : ℕ)
    (hx : ∀ i : Fin (K.card-j), i.val < r → E x i = 0) :
    (∀ i : Fin (K.card-j), i.val ≤ r → E (S h x - x) i = 0) ∧
    (∀ i k : Fin (K.card-j), i.val = r → k.val = r+1 → E (S h x - x) k =
      ((b+r+1 : ℕ) : ℂ) * ((h : ℝ) : ℂ) * E x i) := by
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  have hbound (i : Fin (K.card-j)) : ∀ d < b+i.val, i.val ≤ r → J d u = 0 := by
    intro d hd' hir
    by_cases hlow : d < b
    · exact fixedBoxColumnIntersection_jet_zero hX T K hT hK hd hj hjK u hlow
    · let s : Fin (K.card-j) := ⟨d-b, by have := i.isLt; omega⟩
      have hs := hx s (by dsimp [s]; omega)
      change J (b + (d-b)) u = 0 at hs
      rwa [show b + (d-b) = d by omega] at hs
  have hsupp := closedStageSubmodule_supported hX T _ (column_oldStage hX T K hT hK hd hj hjK u)
  constructor
  · intro i hi
    rw [map_sub]
    change J (b+i.val) (halfShift h (u : LogL2)) - J (b+i.val) u = 0
    rw [← map_sub]
    exact (halfLineMellinJet_halfShift_sub_leading h.property hsupp
      (fun d hd' ↦ hbound i d hd' hi)).1 _ le_rfl
  · intro i k hi hk
    rw [map_sub]
    change J (b+k.val) (halfShift h (u : LogL2)) - J (b+k.val) u = _ * _ * J (b+i.val) u
    rw [← map_sub, show b+k.val = b+i.val+1 by omega, ← hi]
    exact (halfLineMellinJet_halfShift_sub_leading h.property hsupp
      (fun d hd' ↦ hbound i d hd' hi.le)).2

end RiemannMasullo.RationalPacket
