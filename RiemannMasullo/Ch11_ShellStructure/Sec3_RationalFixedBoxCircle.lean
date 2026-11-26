module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxRange
public import RiemannMasullo.ForMathlib.Analysis.Fourier.AddCircle
public import RiemannMasullo.ForMathlib.Topology.Algebra.Module.ContinuousLinearMap.AddCircle
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # Circle action on the completed rational fixed-box quotient -/

public noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace RiemannMasullo.RationalPacket

/-- The next rational stage, regarded as a closed submodule of the preceding stage. -/
def nextClosedStage (X : ℝ) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
    (p : ℕ) (hTp : ∀ q ∈ insert p T, 1 ≤ q) :
    ClosedSubmodule ℂ (closedStageSubmodule X T hT) :=
  (closedStageSubmodule X (insert p T) hTp).comap
    (closedStageSubmodule X T hT).toSubmodule.subtypeL

/-- Paper: (11.3.1.3), p. 494.
Deviation: In the trivial rational angular component with zero width and order, the
completed fixed-box quotient carries a strongly continuous circle action of period
`log p` agreeing with all forward half-shifts, and its character eigenspaces have
dense linear span. -/
theorem exists_closedStage_addCircleAction {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 < p) (hmem : p ∉ T)
    (hTp : ∀ q ∈ insert p T, 1 ≤ q) :
    let E := closedStageSubmodule X T hT
    let N := (nextClosedStage X T hT p hTp).toSubmodule
    let L := Real.log (p : ℝ)
    ∃ A : AddCircle L → (E ⧸ N) →L[ℂ] (E ⧸ N),
      (∀ q, A 0 q = q) ∧
      (∀ c d q, A (c + d) q = A c (A d q)) ∧
      (∀ (t : ℝ) (ht : 0 ≤ t) (x : E),
        A (t : AddCircle L) (N.mkQL x) =
          N.mkQL ⟨halfShift t x, halfShift_mem_closedStage hX T hT ht x.property⟩) ∧
      (∀ q, Continuous (fun c ↦ A c q)) ∧
      (Submodule.span ℂ {q : E ⧸ N | ∃ n : ℤ, ∀ c, A c q = fourier n c • q}).topologicalClosure = ⊤ := by
  dsimp only
  let E := closedStageSubmodule X T hT
  let N := (nextClosedStage X T hT p hTp).toSubmodule
  let L := Real.log (p : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp)
  let R (t : ℝ) : E →L[ℂ] E :=
    ((halfShift (max t 0)).comp E.toSubmodule.subtypeL).codRestrict E.toSubmodule
      (fun x ↦ halfShift_mem_closedStage hX T hT (le_max_right t 0) x.property)
  have hR (t : ℝ) (x : E) : (R t x : Lp ℂ 2 (volume : Measure ℝ)) = halfShift (max t 0) x := rfl
  have hzero (x : E) : R 0 x = x := by
    apply Subtype.ext
    rw [hR, max_self, halfShift_zero]
  have hadd (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (x : E) :
      R (t + u) x = R t (R u x) := by
    apply Subtype.ext
    rw [hR, hR, hR, max_eq_left ht, max_eq_left hu, max_eq_left (add_nonneg ht hu),
      halfShift_add]
  have hpreserve (t : ℝ) (_ht : 0 ≤ t) (x : E) (hx : x ∈ N) : R t x ∈ N := by
    change (R t x : Lp ℂ 2 (volume : Measure ℝ)) ∈ closedStageSubmodule X (insert p T) hTp
    rw [hR]
    exact halfShift_mem_closedStage hX (insert p T) hTp (le_max_right t 0) hx
  have hperiod (x : E) : R L x - x ∈ N := by
    change (R L x : Lp ℂ 2 (volume : Measure ℝ)) - x ∈ closedStageSubmodule X (insert p T) hTp
    rw [hR, max_eq_left hL.le]
    have hx : stagePeriodDifference (p : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ)) ∈
        (closedStageSubmodule X (insert p T) hTp : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
      rw [← range_stagePeriodDifference_closedStage hX T hT hp hmem hTp]
      exact ⟨x, rfl⟩
    simpa only [stagePeriodDifference_apply, L, SetLike.mem_coe] using hx
  have hcontinuous (x : E) : Continuous (fun t ↦ R t x) :=
    ((continuous_halfShift (x : Lp ℂ 2 (volume : Measure ℝ))).comp
      (continuous_id.max continuous_const)).subtype_mk _
  obtain ⟨A, hAzero, hAadd, hAagree, hAcontinuous⟩ :=
    exists_addCircleAction_quotient hL N R hzero hadd hpreserve hperiod hcontinuous
  let _ : Fact (0 < L) := ⟨hL⟩
  let _ : IsClosed (N : Set E) := (nextClosedStage X T hT p hTp).isClosed
  refine ⟨A, hAzero, hAadd, ?_, hAcontinuous,
    closure_span_characterEigenvectors_eq_top A hAzero hAadd hAcontinuous⟩
  intro t ht x
  rw [hAagree t ht]
  congr 1
  exact Subtype.ext ((hR t x).trans (by rw [max_eq_left ht]))


/-- A raw Mellin sample on the prime mesh descends to the completed fixed-box quotient. -/
def rawMellinRow {X : ℝ} (hX : 0 < X) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
    {p : ℕ} (hp : 1 < p) (hTp : ∀ q ∈ insert p T, 1 ≤ q) (j : ℤ) :
    let E := closedStageSubmodule X T hT
    let N := (nextClosedStage X T hT p hTp).toSubmodule
    (E ⧸ N) →L[ℂ] ℂ := by
  dsimp only
  let E := closedStageSubmodule X T hT
  let N := (nextClosedStage X T hT p hTp).toSubmodule
  let f := (mellinSample (-Real.log X) ((j : ℝ) / Real.log p)).comp E.toSubmodule.subtypeL
  exact N.liftQL f (by
    intro x hx
    change mellinSample (-Real.log X) ((j : ℝ) / Real.log p) x = 0
    change (x : Lp ℂ 2 (volume : Measure ℝ)) ∈ closedStageSubmodule X (insert p T) hTp at hx
    exact mellinSample_stage_zeros hX _ hTp hp (Finset.mem_insert_self p T) j
      ((mem_closedStageSubmodule_iff X (insert p T) hTp _).mp hx))

/-- Evaluation of the descended raw row on a representative. -/
theorem rawMellinRow_mkQL {X : ℝ} (hX : 0 < X) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
    {p : ℕ} (hp : 1 < p) (hTp : ∀ q ∈ insert p T, 1 ≤ q) (j : ℤ)
    (x : closedStageSubmodule X T hT) :
    rawMellinRow hX T hT hp hTp j ((nextClosedStage X T hT p hTp).toSubmodule.mkQL x) =
      mellinSample (-Real.log X) ((j : ℝ) / Real.log p) x := by
  unfold rawMellinRow
  rfl

/-- For a circle action agreeing with forward half-shifts, the descended raw
Mellin row at mesh point `j` has the character `-j` in the Fourier convention. -/
theorem rawMellinRow_addCircle {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 < p)
    (hTp : ∀ q ∈ insert p T, 1 ≤ q) (j : ℤ) :
    let E := closedStageSubmodule X T hT
    let N := (nextClosedStage X T hT p hTp).toSubmodule
    let L := Real.log (p : ℝ)
    ∀ A : AddCircle L → (E ⧸ N) →L[ℂ] (E ⧸ N),
      (∀ (t : ℝ) (ht : 0 ≤ t) (x : E), A (t : AddCircle L) (N.mkQL x) =
        N.mkQL ⟨halfShift t x, halfShift_mem_closedStage hX T hT ht x.property⟩) →
      ∀ c q, rawMellinRow hX T hT hp hTp j (A c q) =
        fourier (-j) c * rawMellinRow hX T hT hp hTp j q := by
  dsimp only
  intro A hA c q
  let E := closedStageSubmodule X T hT
  let N := (nextClosedStage X T hT p hTp).toSubmodule
  let L := Real.log (p : ℝ)
  let _ : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp)⟩
  let t : ℝ := AddCircle.equivIco L 0 c
  have ht : 0 ≤ t := (AddCircle.equivIco L 0 c).property.1
  have hc : (t : AddCircle L) = c := AddCircle.coe_equivIco (a := 0)
  obtain ⟨x, rfl⟩ := N.mkQ_surjective q
  change rawMellinRow hX T hT hp hTp j (A c (N.mkQL x)) =
    fourier (-j) c * rawMellinRow hX T hT hp hTp j (N.mkQL x)
  rw [← hc, hA t ht, rawMellinRow_mkQL, rawMellinRow_mkQL,
    mellinSample_halfShift hX T hT ht x.property]
  congr 1
  rw [fourier_coe_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

end RiemannMasullo.RationalPacket
