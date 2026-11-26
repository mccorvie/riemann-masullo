module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteJetRange
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Exact finite-prime intersection defect in the actual Hilbert quotient

The full union stage is the kernel of the consecutive central jet map on the
column intersection. Its quotient has exactly one dimension for each missing
jet. -/

public noncomputable section

namespace RiemannMasullo.RationalPacket

/-- The intersection of the actual stages tested by the `j`-column criterion. -/
def fixedBoxColumnIntersection {X : ℝ} (_hX : 0 < X) (T K : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hK : ∀ p ∈ K, p.Prime) (_hd : Disjoint T K)
    {j : ℕ} (_hj : 1 ≤ j) (_hjK : j ≤ K.card) : ClosedSubmodule ℂ LogL2 :=
  ⨅ (A : Finset ℕ) (hA : A ⊆ K) (_ : A.card = j), closedStageSubmodule X (T ∪ A) (by
    intro p hp
    exact (Finset.mem_union.mp hp).elim (fun h ↦ (hT p h).one_lt.le)
      (fun h ↦ (hK p (hA h)).one_lt.le))

variable {X : ℝ} (hX : 0 < X) (T K : Finset ℕ)
  (hT : ∀ p ∈ T, p.Prime) (hK : ∀ p ∈ K, p.Prime) (hd : Disjoint T K)
  {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K.card)

local notation "C" => fixedBoxColumnIntersection hX T K hT hK hd hj hjK

theorem mem_fixedBoxColumnIntersection_iff (u : LogL2) : u ∈ C ↔
    ∀ A : Finset ℕ, ∀ hA : A ⊆ K, A.card = j → u ∈ closedStageSubmodule X (T ∪ A) (by
      intro p hp
      exact (Finset.mem_union.mp hp).elim (fun h ↦ (hT p h).one_lt.le)
        (fun h ↦ (hK p (hA h)).one_lt.le)) := by
  simp only [fixedBoxColumnIntersection, ClosedSubmodule.mem_iInf]

/-- The full union stage pulled back to the actual column intersection. -/
def fixedBoxColumnDenominator : ClosedSubmodule ℂ C :=
  (closedStageSubmodule X (T ∪ K) (by
    intro p hp
    exact (Finset.mem_union.mp hp).elim (fun h ↦ (hT p h).one_lt.le)
      (fun h ↦ (hK p h).one_lt.le))).comap (C).toSubmodule.subtypeL

local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxColumnDenominator hX T K hT hK hd hj hjK)

theorem mem_fixedBoxColumnDenominator_iff (u : C) : u ∈ N ↔
    (u : LogL2) ∈ closedStageSubmodule X (T ∪ K) (by
      intro p hp
      exact (Finset.mem_union.mp hp).elim (fun h ↦ (hT p h).one_lt.le)
        (fun h ↦ (hK p h).one_lt.le)) := by
  unfold fixedBoxColumnDenominator
  rfl

/-- Consecutive raw central jets on the actual intersection. -/
def fixedBoxColumnJets : C →L[ℂ] (Fin (K.card - j) → ℂ) :=
  ContinuousLinearMap.pi fun i ↦
    (halfLineMellinJet (-Real.log X) 0 (T.card + j + i.val)).comp (C).toSubmodule.subtypeL

local notation "L" => fixedBoxColumnJets hX T K hT hK hd hj hjK

theorem fixedBoxColumnJets_surjective : Function.Surjective L := by
  intro y
  obtain ⟨u, hu, hy⟩ := exists_all_card_stage_with_jets_unconditional hX T K hT hK hd hj hjK y
  exact ⟨⟨u, (mem_fixedBoxColumnIntersection_iff hX T K hT hK hd hj hjK u).mpr hu⟩, funext hy⟩

theorem ker_fixedBoxColumnJets : LinearMap.ker (L).toLinearMap = N := by
  ext u
  have hall := (mem_fixedBoxColumnIntersection_iff hX T K hT hK hd hj hjK _).mp u.property
  obtain ⟨hold, hmesh, hlow⟩ :=
    (mem_all_card_closedStageSubmodule_union_iff hX T K hT hK hd hj hjK _).mp hall
  have hfull := mem_closedStageSubmodule_union_iff hX T K hT hK hd (u : LogL2)
  constructor
  · intro hu
    change L u = 0 at hu
    apply hfull.mpr
    refine ⟨hold, hmesh, fun d hle hlt ↦ ?_⟩
    by_cases h : d < T.card + j
    · exact hlow d hle h
    · let i : Fin (K.card - j) := ⟨d - (T.card + j), by omega⟩
      have hi := congrFun hu i
      change halfLineMellinJet (-Real.log X) 0 (T.card + j + i.val) (u : LogL2) = 0 at hi
      have heq : T.card + j + i.val = d := by dsimp [i]; omega
      exact heq ▸ hi
  · intro hu
    have hz := (hfull.mp hu).2.2
    change L u = 0
    funext i
    change halfLineMellinJet (-Real.log X) 0 (T.card + j + i.val) (u : LogL2) = 0
    exact hz _ (by omega) (by have := i.isLt; omega)

/-- The quotient by the full stage has the remaining jet coordinates as a basis model. -/
def fixedBoxColumnQuotientEquiv : (C ⧸ N) ≃ₗ[ℂ] (Fin (K.card - j) → ℂ) :=
  (Submodule.quotEquivOfEq _ _ (ker_fixedBoxColumnJets hX T K hT hK hd hj hjK).symm).trans
    (LinearMap.quotKerEquivOfSurjective (L).toLinearMap
      (fixedBoxColumnJets_surjective hX T K hT hK hd hj hjK))

/-- Raw coordinates of an actual representative in the finite-column quotient. -/
theorem fixedBoxColumnQuotientEquiv_mk (u : C) (i : Fin (K.card - j)) :
    fixedBoxColumnQuotientEquiv hX T K hT hK hd hj hjK ((N).mkQ u) i =
      halfLineMellinJet (-Real.log X) 0 (T.card + j + i.val) (u : LogL2) := by
  unfold fixedBoxColumnQuotientEquiv fixedBoxColumnJets
  rfl

theorem finrank_fixedBoxColumnQuotient : Module.finrank ℂ (C ⧸ N) = K.card - j :=
  (fixedBoxColumnQuotientEquiv hX T K hT hK hd hj hjK).finrank_eq.trans (Module.finrank_fin_fun ℂ)

/-- The jet coordinates identify the topological Hilbert stage quotient as well. -/
def fixedBoxColumnQuotientContinuousEquiv : (C ⧸ N) ≃L[ℂ] (Fin (K.card - j) → ℂ) := by
  haveI : IsClosed (N : Set C) := (fixedBoxColumnDenominator hX T K hT hK hd hj hjK).isClosed
  let e := fixedBoxColumnQuotientEquiv hX T K hT hK hd hj hjK
  letI : FiniteDimensional ℂ (C ⧸ N) := e.symm.finiteDimensional
  exact e.toContinuousLinearEquiv

end RiemannMasullo.RationalPacket
