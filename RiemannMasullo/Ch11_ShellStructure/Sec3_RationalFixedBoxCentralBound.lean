module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCentralJets
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCentralAction
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearFiniteQuotient
import Mathlib.Data.Nat.Prime.Infinite

/-! # Central-jet obstruction to uniform nuclear bounds along rational prime towers

In the actual unweighted logarithmic model, the finite relative-level action has
a central quotient of dimension equal to the number of primes. Its diagonal is
the test mass, forcing a linear lower bound on the trace norm.
-/

public noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology
namespace RiemannMasullo.RationalPacket
variable {X : ℝ}
local instance (M : ClosedSubmodule ℂ LogL2) : IsClosed (M.toSubmodule : Set LogL2) := M.isClosed
local notation "E₀" => closedStageSubmodule X ∅ (by simp)

/-- The first central Mellin jets of the original-stage component of an ambient vector. -/
def fixedBoxCentralRows (X : ℝ) (m : ℕ) : LogL2 →L[ℂ] (Fin m → ℂ) :=
  (ContinuousLinearMap.pi (fun i : Fin m ↦ halfLineMellinJet (-Real.log X) 0 i)).comp
    (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection

theorem fixedBoxCentralRows_apply (X : ℝ) (m : ℕ) (F : LogL2) (i : Fin m) :
    fixedBoxCentralRows X m F i = halfLineMellinJet (-Real.log X) 0 i
      ((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection F) := by
  simp only [fixedBoxCentralRows, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply]

theorem fixedBoxCentralRows_surjective (hX : 0 < X) (m : ℕ) :
    Surjective (fixedBoxCentralRows X m) := by
  intro y
  obtain ⟨u,hu⟩ := fixedBoxCentralJets_surjective hX m y
  refine ⟨u, funext fun i ↦ ?_⟩
  rw [fixedBoxCentralRows_apply, Submodule.starProjection_eq_self_iff.mpr u.property]
  simpa only [ContinuousLinearMap.pi_apply, fixedBoxCentralJet_apply] using! congrFun hu i

private theorem relative_mem_empty (hX : 0 < X) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (F : LogL2) :
    ((E₀).toSubmodule.starProjection - (closedStageSubmodule X S hS1).toSubmodule.starProjection) F ∈ E₀ := by
  apply (E₀).sub_mem
  · exact ((E₀).toSubmodule.orthogonalProjectionOnto F).property
  · exact fixedBox_stage_le_empty hX S hS1
      ((closedStageSubmodule X S hS1).toSubmodule.orthogonalProjectionOnto F).property

private theorem centralRows_on_empty (m : ℕ) (F : LogL2) (hF : F ∈ E₀) (i : Fin m) :
    fixedBoxCentralRows X m F i = halfLineMellinJet (-Real.log X) 0 i F := by
  rw [fixedBoxCentralRows_apply, Submodule.starProjection_eq_self_iff.mpr hF]

private theorem centralRows_relative (hX : 0 < X) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (hS : ∀ q ∈ S, q.Prime) (F : LogL2) :
    fixedBoxCentralRows X S.card
      (((E₀).toSubmodule.starProjection - (closedStageSubmodule X S hS1).toSubmodule.starProjection) F) =
      fixedBoxCentralRows X S.card F := by
  apply funext
  intro i
  rw [centralRows_on_empty _ _ (relative_mem_empty hX S hS1 F) i, sub_apply, map_sub]
  have hz := halfLineMellinJet_stage_closure_zero hX S hS i i.isLt
    ((mem_closedStageSubmodule_iff X S hS1 _).mp
      ((closedStageSubmodule X S hS1).toSubmodule.orthogonalProjectionOnto F).property)
  have hz' : halfLineMellinJet (-Real.log X) 0 i
      ((closedStageSubmodule X S hS1).toSubmodule.starProjection F) = 0 := hz
  rw [hz', sub_zero, fixedBoxCentralRows_apply]

private theorem centralMoment_sum_extend {m j : ℕ} (hj : j < m)
    (f : PositiveTimeTest) (a : ℕ → ℂ) :
    (∑ i ∈ Finset.range (j+1), ((j.choose i : ℂ) * positiveTestMoment f (j-i)) * a i) =
      ∑ i : Fin m, ((j.choose i.val : ℂ) * positiveTestMoment f (j-i.val)) * a i := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ ((j.choose i : ℂ) * positiveTestMoment f (j-i)) * a i) m]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj))
  intro i _ hi
  have hji : j < i := Nat.lt_of_succ_le (by simpa only [Finset.mem_range, not_lt] using hi)
  simp only [Nat.choose_eq_zero_of_lt hji, Nat.cast_zero, zero_mul]

/-- The central-jet matrix describes the actual ambient action on the original stage. -/
theorem fixedBoxCentralRows_ambientTest (hX : 0 < X) (m : ℕ)
    (f : PositiveTimeTest) (F : LogL2) (hF : F ∈ E₀) :
    fixedBoxCentralRows X m (fixedBoxAmbientTestAction f F) =
      centralJetTestMatrix m f (fixedBoxCentralRows X m F) := by
  have hAF := fixedBoxAmbientTestAction_mem hX ∅ (by simp) f F hF
  apply funext
  intro j
  rw [centralRows_on_empty _ _ hAF j,
    halfLineMellinJet_ambientTest_zero hX ∅ (by simp) j f F hF,
    centralMoment_sum_extend j.isLt, centralJetTestMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [centralRows_on_empty _ _ hF i]

/-- The central jets give an actual finite-dimensional quotient of the full
relative-level test action, with its exact triangular moment matrix. -/
theorem fixedBoxCentralRows_intertwines (hX : 0 < X) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (hS : ∀ q ∈ S, q.Prime)
    (f : PositiveTimeTest) (F : LogL2) :
    fixedBoxCentralRows X S.card (fixedBoxFiniteTestAction (X := X) S hS1 f F) =
      centralJetTestMatrix S.card f (fixedBoxCentralRows X S.card F) := by
  let R := (E₀).toSubmodule.starProjection - (closedStageSubmodule X S hS1).toSubmodule.starProjection
  have hR : R F ∈ E₀ := relative_mem_empty hX S hS1 F
  have hAR : fixedBoxAmbientTestAction f (R F) ∈ E₀ :=
    fixedBoxAmbientTestAction_mem hX ∅ (by simp) f (R F) hR
  rw [fixedBoxFiniteTestAction_def, closedLayerCompression_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, centralRows_relative hX S hS1 hS]
  apply funext
  intro j
  rw [centralRows_on_empty _ _ hAR j, halfLineMellinJet_ambientTest_zero hX ∅ (by simp) j f (R F) hR,
    centralMoment_sum_extend j.isLt, centralJetTestMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← centralRows_on_empty _ _ hR i]
  exact congrFun (centralRows_relative hX S hS1 hS F) i

/-- Each prime supplies a central diagonal entry. Therefore the trace norm of
the full finite-level action grows at least linearly with the number of primes,
even when its scalar Poisson trace has already stabilized. -/
theorem fixedBoxFiniteTestAction_traceNorm_ge_card (hX : 0 < X) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (hS : ∀ q ∈ S, q.Prime) (f : PositiveTimeTest) :
    (S.card : ℝ) * ‖∫ t : ℝ, f t‖ ≤
      traceNorm ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
        fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ :=
  traceNorm_ge_finite_quotient_diagonal S.card (fixedBoxCentralRows X S.card)
    (fixedBoxCentralRows_surjective hX S.card) _
    (fixedBoxFiniteTestAction_nuclear hX S hS1 hS f) (centralJetTestMatrix S.card f)
    (fixedBoxCentralRows_intertwines hX S hS1 hS f) _
    (centralJetTestMatrix_diagonal S.card f)


/-- Nonzero test mass rules out a uniform trace-norm bound over finite prime sets,
even at a single fixed total Fourier box. -/
theorem fixedBoxFiniteTestAction_traceNorm_unbounded (hX : 0 < X)
    (f : PositiveTimeTest) (hf : (∫ t : ℝ, f t) ≠ 0) (C : ℝ) :
    ∃ (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime),
      C < traceNorm ⟨fixedBoxFiniteTestAction (X := X) S (fun p hp ↦ (hS p hp).one_lt.le) f,
        fixedBoxFiniteTestAction_nuclear hX S (fun p hp ↦ (hS p hp).one_lt.le) hS f⟩ := by
  have hc : 0 < ‖∫ t : ℝ, f t‖ := norm_pos_iff.mpr hf
  obtain ⟨n,hn⟩ := exists_nat_gt (C / ‖∫ t : ℝ, f t‖)
  obtain ⟨S,hS,hcard⟩ := Nat.infinite_setOfPred_prime.exists_subset_card_eq n
  have hS' : ∀ p ∈ S, p.Prime := fun p hp ↦ hS hp
  refine ⟨S,hS',?_⟩
  apply lt_of_lt_of_le _ (fixedBoxFiniteTestAction_traceNorm_ge_card hX S
    (fun p hp ↦ (hS' p hp).one_lt.le) hS' f)
  rw [hcard]
  exact (div_lt_iff₀ hc).mp hn

end RiemannMasullo.RationalPacket
