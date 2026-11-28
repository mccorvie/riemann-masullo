module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCentralBound
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTrace
public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositiveUnitTest

/-! # Zero finite-level traces with unbounded trace norms

For the actual rational unweighted logarithmic model, the finite traces in
(11.3.1.3)–(11.3.1.4), pp. 494–496, do not imply a trace-norm limit over primes.
A unit-mass test supported before log 2 has zero trace at every finite level
and trace norm at least the number of prime factors. This does not address
the paper's positive-width or higher-Sobolev Hilbert models.
-/

public noncomputable section
open Set Function MeasureTheory
namespace RiemannMasullo.RationalPacket

/-- A test supported strictly before log 2 has no prime Poisson samples. -/
theorem positiveTest_prime_lattice_zero_of_short_support (f : PositiveTimeTest)
    (hf : tsupport f ⊆ Ioo 0 (Real.log 2)) (p : ℕ) (hp : p.Prime) (k : ℤ) :
    f (Real.log p * k) = 0 := by
  by_contra h
  have hs := hf (subset_tsupport f h)
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hk : (0 : ℝ) < k := (mul_pos_iff_of_pos_left hL).mp hs.1
  have hk1 : (1 : ℝ) ≤ k := by
    exact_mod_cast (show (1 : ℤ) ≤ k by exact_mod_cast hk)
  have hlow : Real.log (p : ℝ) ≤ Real.log p * k := le_mul_of_one_le_right hL.le hk1
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  linarith [hs.2]

/-- Every actual finite-level trace vanishes for a test supported before log 2. -/
theorem fixedBoxFiniteTestAction_trace_zero_of_short_support
    (X : ℝ) (hX : 0 < X) (S : Finset ℕ) (hS1 : ∀ p ∈ S, 1 ≤ p)
    (hS : ∀ p ∈ S, p.Prime) (f : PositiveTimeTest)
    (hf : tsupport f ⊆ Ioo 0 (Real.log 2)) :
    hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
      fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ = 0 := by
  rw [fixedBoxFiniteTestAction_poisson_trace hX S hS1 hS f]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [positiveTest_prime_lattice_zero_of_short_support f hf p (hS p hp), tsum_zero, mul_zero]

/-- One fixed test has zero trace at every finite prime level while its trace
norm is at least the number of primes, uniformly over every positive box. -/
theorem exists_fixedBoxFiniteTestAction_zero_trace_large_norm :
    ∃ f : PositiveTimeTest, tsupport f ⊆ Ioo 0 (Real.log 2) ∧ (∫ t : ℝ, f t) = 1 ∧
      ∀ (X : ℝ) (hX : 0 < X) (S : Finset ℕ) (hS1 : ∀ p ∈ S, 1 ≤ p)
        (hS : ∀ p ∈ S, p.Prime),
        hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
          fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ = 0 ∧
        (S.card : ℝ) ≤ traceNorm ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
          fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ := by
  obtain ⟨f, hf, hm⟩ := exists_positiveTest_unit_mass (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨f, hf, hm, fun X hX S hS1 hS ↦ ⟨?_, ?_⟩⟩
  · exact fixedBoxFiniteTestAction_trace_zero_of_short_support X hX S hS1 hS f hf
  · simpa only [hm, norm_one, mul_one] using
      fixedBoxFiniteTestAction_traceNorm_ge_card hX S hS1 hS f

end RiemannMasullo.RationalPacket
