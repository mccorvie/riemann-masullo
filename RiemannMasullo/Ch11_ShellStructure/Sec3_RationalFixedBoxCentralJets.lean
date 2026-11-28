module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTower
public import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.FiniteJetSurjective
import Mathlib.Data.Nat.Prime.Infinite

/-! # Independent central Mellin jets on the actual rational theta stage -/

public noncomputable section
namespace RiemannMasullo.RationalPacket
open Set
open scoped Topology
variable {X : ℝ}
local notation "E₀" => closedStageSubmodule X ∅ (by simp)

/-- The actual bounded zero-frequency Mellin jets on the original theta stage. -/
def fixedBoxCentralJet (X : ℝ) (j : ℕ) :
    (closedStageSubmodule X ∅ (by simp)) →L[ℂ] ℂ :=
  (halfLineMellinJet (-Real.log X) 0 j).comp
    (closedStageSubmodule X ∅ (by simp)).toSubmodule.subtypeL

theorem fixedBoxCentralJet_apply (X : ℝ) (j : ℕ) (u : closedStageSubmodule X ∅ (by simp)) :
    fixedBoxCentralJet X j u = halfLineMellinJet (-Real.log X) 0 j (u : LogL2) := by rfl

/-- Every finite order has a genuine theta-stage vector with nonzero leading
central jet and all preceding jets zero, in the same total Fourier box. -/
theorem exists_fixedBoxCentralJet_triangular (hX : 0 < X) (j : ℕ) :
    ∃ v : E₀, fixedBoxCentralJet X j v ≠ 0 ∧
      ∀ i < j, fixedBoxCentralJet X i v = 0 := by
  obtain ⟨T, hT, hcard⟩ := Nat.infinite_setOfPred_prime.exists_subset_card_eq j
  have hT' : ∀ q ∈ T, q.Prime := fun q hq ↦ hT hq
  have hT1 : ∀ q ∈ T, 1 ≤ q := fun q hq ↦ (hT' q hq).one_lt.le
  obtain ⟨p,hp,hpT⟩ := Nat.infinite_setOfPred_prime.exists_notMem_finset T
  obtain ⟨v,hv,hrow⟩ := exists_fixedBox_biorthogonal_stage hX T hT' hp hpT
  have hET : v 0 ∈ closedStageSubmodule X T hT1 :=
    (mem_closedStageSubmodule_iff X T hT1 _).mpr (subset_closure (hv 0))
  have hE : v 0 ∈ E₀ := fixedBox_stage_le_empty hX T hT1 hET
  refine ⟨⟨v 0,hE⟩, ?_, fun i hi ↦ ?_⟩
  · intro hz
    have hh := hrow 0 0
    rw [packetRow_apply, ite_eq_left rfl, hcard] at hh
    rw [fixedBoxCentralJet_apply] at hz
    rw [hz, zero_div] at hh
    norm_num at hh
  · rw [fixedBoxCentralJet_apply]
    exact halfLineMellinJet_stage_closure_zero hX T hT' i (hcard ▸ hi) (subset_closure (hv 0))

/-- The first m actual central Mellin jets are independent and jointly onto. -/
theorem fixedBoxCentralJets_surjective (hX : 0 < X) (m : ℕ) :
    Function.Surjective (ContinuousLinearMap.pi (fun i : Fin m ↦ fixedBoxCentralJet X i)) :=
  finiteJetMap_surjective (fixedBoxCentralJet X) (exists_fixedBoxCentralJet_triangular hX) m

end RiemannMasullo.RationalPacket
