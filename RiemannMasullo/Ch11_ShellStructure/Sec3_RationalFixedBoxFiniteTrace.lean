module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTower
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearCyclicTrace

/-! # Poisson traces on actual finite rational relative levels

The trace is the finite sum of the logarithmic prime-packet traces.
The full finite-level operator is nuclear by positive-time factorization.
-/

public noncomputable section
open Set MeasureTheory
open scoped Topology SchwartzMap NNReal
namespace RiemannMasullo.RationalPacket
variable {X : ℝ} (hX : 0 < X)
local instance (M : ClosedSubmodule ℂ LogL2) : IsClosed (M.toSubmodule : Set LogL2) := M.isClosed

include hX in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The actual finite relative-level trace is the sum of the prime Poisson traces. -/
theorem fixedBoxFiniteTestAction_poisson_trace (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (hS : ∀ q ∈ S, q.Prime) (f : PositiveTimeTest) :
    hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
      fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ =
      ∑ p ∈ S, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k) := by
  induction S using Finset.induction_on with
  | empty =>
    have he : fixedBoxFiniteTestAction (X := X) ∅ hS1 f = 0 := by
      simp only [fixedBoxFiniteTestAction_def, closedLayerCompression_def, sub_self,
        ContinuousLinearMap.zero_comp]
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := LogL2)
    simp only [Finset.sum_empty]
    rw [← htr]
    have hz : (⟨fixedBoxFiniteTestAction (X := X) ∅ hS1 f,
        fixedBoxFiniteTestAction_nuclear hX ∅ hS1 hS f⟩ : nuclearEndomorphisms LogL2) = 0 :=
      Subtype.ext he
    rw [hz, map_zero]
  | @insert p T hpT ih =>
    have hT1 : ∀ q ∈ T, 1 ≤ q := fun q hq ↦ hS1 q (Finset.mem_insert_of_mem hq)
    have hT : ∀ q ∈ T, q.Prime := fun q hq ↦ hS q (Finset.mem_insert_of_mem hq)
    have hp := hS p (Finset.mem_insert_self p T)
    let M := closedStageSubmodule X ∅ (by simp)
    let B := closedStageSubmodule X T hT1
    let D := closedStageSubmodule X (insert p T) hS1
    let A := fixedBoxFiniteTestAction (X := X) (insert p T) hS1 f
    let P := B.toSubmodule.starProjection - D.toSubmodule.starProjection
    let Q := M.toSubmodule.starProjection - B.toSubmodule.starProjection
    let R := M.toSubmodule.starProjection - D.toSubmodule.starProjection
    have hDB : D ≤ B := fixedBox_nextStage_le T hT1 p hS1 hX
    have hBM : B ≤ M := fixedBox_stage_le_empty hX T hT1
    have hPQ : P+Q=R := by dsimp only [P,Q,R]; abel
    have hAR : A.comp R = A := by
      simpa only [A, R, fixedBoxFiniteTestAction_def] using!
        closedLayerCompression_right M D (hDB.trans hBM) (fixedBoxAmbientTestAction f)
    have hdeep : A.comp P =
        fixedBoxLayerTestAction T hT1 p hS1 hX hp hpT (positiveTestToSchwartz f) := by
      dsimp only [A]
      rw [fixedBoxFiniteTestAction_def]
      rw [closedLayerCompression_deep_right M B D hDB hBM _
        (fixedBoxAmbientTestAction_mem hX T hT1 f)
        (fixedBoxAmbientTestAction_mem hX (insert p T) hS1 f)]
      exact (fixedBoxLayerTestAction_eq_compression hX T hT1 p hS1 hp hpT f).symm
    have hshallow : Q.comp A = fixedBoxFiniteTestAction (X := X) T hT1 f := by
      simpa only [Q, A, fixedBoxFiniteTestAction_def] using!
        closedLayerCompression_shallow_left M B D hDB hBM _
          (fixedBoxAmbientTestAction_mem hX T hT1 f)
          (fixedBoxAmbientTestAction_mem hX (insert p T) hS1 f)
    have hn := fixedBoxFiniteTestAction_nuclear hX (insert p T) hS1 hS f
    have htrace := hilbertTrace_two_block A P Q R hn hPQ hAR
    have hpacket := fixedBoxLayerTestAction_poisson_trace T hT1 p hS1 hX hp hpT hT
      (positiveTestToSchwartz f)
    rcases hpacket with ⟨hnp, htp⟩
    have ht : hilbertTrace ⟨A,hn⟩ =
        hilbertTrace ⟨fixedBoxLayerTestAction T hT1 p hS1 hX hp hpT (positiveTestToSchwartz f),hnp⟩ +
        hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) T hT1 f,
          fixedBoxFiniteTestAction_nuclear hX T hT1 hT f⟩ := by
      simpa only [hdeep, hshallow] using! htrace
    rw [htp, ih hT1 hT] at ht
    simpa only [A, Finset.sum_insert hpT, positiveTestToSchwartz_apply] using! ht


private theorem positiveTest_lattice_zero (f : PositiveTimeTest) (R : ℝ)
    (hR : ∀ t ∈ tsupport f, t ≤ R) (p : ℕ) (hp : p.Prime)
    (hRp : R < Real.log p) :
    (∑' k : ℤ, f (Real.log p * k)) = 0 := by
  suffices hf : ∀ k : ℤ, f (Real.log p * k) = 0 by simp only [hf, tsum_zero]
  intro k
  by_contra h
  have hs := f.tsupport_subset (subset_tsupport f h)
  have hb := hR _ (subset_tsupport f h)
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hk : (0 : ℝ) < k := (mul_pos_iff_of_pos_left hL).mp hs
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by exact_mod_cast hk)
  have hlow : Real.log (p : ℝ) ≤ Real.log p * k := le_mul_of_one_le_right hL.le hk1
  linarith

/-- A fixed compact positive-time test has only finitely many nonzero prime
Poisson contributions. The cutoff is independent of the total Fourier box. -/
theorem positiveTest_prime_poisson_finite (f : PositiveTimeTest) :
    ∃ S₀ : Finset ℕ, (∀ p ∈ S₀, p.Prime) ∧
      ∀ p : ℕ, p.Prime → p ∉ S₀ →
        (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k) = 0 := by
  classical
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.bddAbove
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp R)
  let S₀ := (Finset.range B).filter Nat.Prime
  refine ⟨S₀, fun p hp ↦ (Finset.mem_filter.mp hp).2, fun p hp hpS ↦ ?_⟩
  have hBp : B ≤ p := by
    by_contra h
    exact hpS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  have hRp : R < Real.log p := by
    apply (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr
    exact hB.trans_le (by exact_mod_cast hBp)
  rw [positiveTest_lattice_zero f R hR p hp hRp, mul_zero]

/-- The traces of actual finite relative-level actions stabilize exactly once
all primes meeting the compact positive-time support are included. This is a
statement about the finite nuclear compressions, not an infinite-operator limit. -/
theorem fixedBoxFiniteTestAction_trace_stabilizes (f : PositiveTimeTest) :
    ∃ S₀ : Finset ℕ, (∀ p ∈ S₀, p.Prime) ∧
      ∀ (X : ℝ) (hX : 0 < X) (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
        (hS : ∀ q ∈ S, q.Prime), S₀ ⊆ S →
        hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
          fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ =
          ∑ p ∈ S₀, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k) := by
  obtain ⟨S₀, hS₀, hz⟩ := positiveTest_prime_poisson_finite f
  refine ⟨S₀, hS₀, fun X hX S hS1 hS hsub ↦ ?_⟩
  rw [fixedBoxFiniteTestAction_poisson_trace hX S hS1 hS f]
  exact (Finset.sum_subset hsub (fun p hp hp₀ ↦ hz p (hS p hp) hp₀)).symm


end RiemannMasullo.RationalPacket
