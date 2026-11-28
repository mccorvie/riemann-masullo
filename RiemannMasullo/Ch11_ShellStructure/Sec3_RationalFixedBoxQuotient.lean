module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxRange
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # The forward semigroup on the completed rational fixed-box quotient

Following fpet19's periodization construction (issue #7351, comment 7149080501),
we descend actual forward shifts, without restricting a negative shift to a box.
The equality at the period uses the exact closed-stage range, not a coordinate model.
-/

public noncomputable section

open Set
open scoped NNReal

namespace RiemannMasullo.RationalPacket

variable (X : ℝ) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp : ∀ q ∈ insert p T, 1 ≤ q)

local notation "E" => closedStageSubmodule X T hT

/-- The next closed stage as a closed subspace of the preceding stage. -/
def fixedBoxDenominator : ClosedSubmodule ℂ E :=
  (closedStageSubmodule X (insert p T) hTp).comap (E).toSubmodule.subtypeL

/-- Membership in the actual denominator is membership of the ambient representative
in the next closed stage. -/
theorem mem_fixedBoxDenominator_iff (u : E) :
    u ∈ fixedBoxDenominator X T hT p hTp ↔
      (u : LogL2) ∈ closedStageSubmodule X (insert p T) hTp := by rfl

local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxDenominator X T hT p hTp)

instance fixedBoxDenominator_isClosed : IsClosed (N : Set E) :=
  (fixedBoxDenominator X T hT p hTp).isClosed

scoped notation "FixedBoxQuotient[" x "," t "," ht "," p "," hp "]" =>
  (closedStageSubmodule x t ht) ⧸ (ClosedSubmodule.toSubmodule (fixedBoxDenominator x t ht p hp))

local notation "Q" => FixedBoxQuotient[X,T,hT,p,hTp]

variable {X} (hX : 0 < X)

/-- The forward shifts act on the preceding stage itself. -/
@[expose] def closedStageForwardShift (h : ℝ≥0) : E →L[ℂ] E :=
  ((halfShift h).comp (E).toSubmodule.subtypeL).codRestrict (E).toSubmodule
    (fun u ↦ halfShift_mem_closedStage hX T hT h.property u.property)

local notation "R" => closedStageForwardShift T hT hX

/-- Evaluation of the restricted forward operator in the ambient Hilbert space. -/
theorem closedStageForwardShift_apply (h : ℝ≥0) (u : E) :
    (R h u : LogL2) = halfShift (h : ℝ) (u : LogL2) := rfl

/-- Descend the forward operator through the closed submodule, using invariance
of the next stage independently of invariance of the preceding one. -/
def fixedBoxForwardShift (h : ℝ≥0) : Q →L[ℂ] Q :=
  (N).liftQL ((N).mkQL.comp (R h)) (by
    intro u hu
    change Submodule.Quotient.mk (R h u) = (0 : Q)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact halfShift_mem_closedStage hX (insert p T) hTp h.property hu)

local notation "S" => fixedBoxForwardShift T hT p hTp hX

/-- Representative computation for the quotient action. -/
@[simp] theorem fixedBoxForwardShift_mk (h : ℝ≥0) (u : E) :
    S h ((N).mkQL u) = (N).mkQL (R h u) := by
  simp [fixedBoxForwardShift]

@[simp] theorem fixedBoxForwardShift_zero : S 0 = ContinuousLinearMap.id ℂ Q := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  change (N).mkQL (R 0 u) = (N).mkQL u
  exact congrArg (N).mkQL (Subtype.ext (halfShift_zero (u : LogL2)))

/-- Forward composition needs no backwards stage-invariance hypothesis. -/
theorem fixedBoxForwardShift_add (h k : ℝ≥0) : S (h + k) = (S h).comp (S k) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  change (N).mkQL (R (h + k) u) = (N).mkQL (R h (R k u))
  exact congrArg (N).mkQL (Subtype.ext (halfShift_add (h : ℝ) (k : ℝ) (u : LogL2)))

/-- One logarithmic period is the identity modulo the *actual* next stage. -/
theorem fixedBoxForwardShift_period (hp : 1 < p) (hmem : p ∉ T) :
    S ⟨Real.log (p : ℝ), Real.log_nonneg (by exact_mod_cast hp.le)⟩ =
      ContinuousLinearMap.id ℂ Q := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  apply (Submodule.Quotient.eq N).mpr
  have hd : stagePeriodDifference (p : ℝ) (u : LogL2) ∈
      (closedStageSubmodule X (insert p T) hTp : Set LogL2) := by
    rw [← range_stagePeriodDifference_closedStage hX T hT hp hmem hTp]
    exact ⟨u, rfl⟩
  rw [stagePeriodDifference_apply] at hd
  exact hd

/-- Continuity concerns vector orbits, not the operator norm topology. -/
theorem continuous_fixedBoxForwardShift (x : Q) : Continuous fun h : ℝ≥0 ↦ S h x := by
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective x
  have hc : Continuous fun h : ℝ≥0 ↦ R h u :=
    ((continuous_halfShift (u : LogL2)).comp NNReal.continuous_coe).subtype_mk _
  exact (N).mkQL.continuous.comp hc

/-- The quotient operator norm retains the ambient exponential upper bound. -/
theorem norm_fixedBoxForwardShift_le (h : ℝ≥0) : ‖S h‖ ≤ Real.exp ((h : ℝ) / 2) := by
  let c := Real.exp ((h : ℝ) / 2)
  have hc : 0 < c := Real.exp_pos _
  refine ContinuousLinearMap.opNorm_le_bound (S h) hc.le (fun (x : Q) ↦ ?_)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu, hub⟩ := Submodule.Quotient.norm_mk_lt x (div_pos hε hc)
  calc
    ‖S h x‖ = ‖(N).mkQL (R h u)‖ := by
      rw [← hu]
      exact congrArg norm (fixedBoxForwardShift_mk T hT p hTp hX h u)
    _ ≤ ‖R h u‖ := Submodule.Quotient.norm_mk_le N _
    _ = c * ‖u‖ := norm_halfShift _ _
    _ ≤ c * (‖x‖ + ε / c) := mul_le_mul_of_nonneg_left hub.le hc.le
    _ = c * ‖x‖ + ε := by rw [mul_add, mul_comm c (ε / c), div_mul_cancel₀ ε hc.ne']

end RiemannMasullo.RationalPacket
