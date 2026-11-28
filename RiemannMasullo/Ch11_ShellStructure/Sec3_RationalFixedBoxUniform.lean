module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxTranslation
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearUnitaryTrace

/-! # Fourier-box-independent nuclear bounds for actual finite theta levels -/

public noncomputable section
namespace RiemannMasullo.RationalPacket

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The trace norm of the actual
finite relative-level test action is independent of the positive total Fourier box.
Deviation: The rational trivial-angular, unweighted logarithmic model is used. -/
theorem fixedBoxFiniteTestAction_traceNorm_eq (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q) (hS : ∀ q ∈ S, q.Prime)
    (f : PositiveTimeTest) :
    traceNorm ⟨fixedBoxFiniteTestAction (X := Y) S hS1 f,
      fixedBoxFiniteTestAction_nuclear hY S hS1 hS f⟩ =
    traceNorm ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
      fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ := by
  let h := Real.log X - Real.log Y
  have hXY : X * Real.exp (-h) = Y := by
    dsimp only [h]
    rw [neg_sub, Real.exp_sub, Real.exp_log hX, Real.exp_log hY]
    field_simp
  have he := fixedBoxFiniteTestAction_unitary_conjugate X S hS1 h f
  rw [hXY] at he
  obtain ⟨hn, hnorm, _⟩ := nuclear_trace_unitary (fixedBoxTranslationEquiv h)
    (fixedBoxFiniteTestAction (X := X) S hS1 f)
    (fixedBoxFiniteTestAction_nuclear hX S hS1 hS f)
  simpa only [← he] using! hnorm

/-- A single finite nuclear bound controls every positive total Fourier box.
No cutoff-dependent norm-equivalence constant is needed. -/
theorem fixedBoxFiniteTestAction_uniform_traceNorm (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (hS : ∀ q ∈ S, q.Prime) (f : PositiveTimeTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ) (hX : 0 < X),
      traceNorm ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
        fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ ≤ C := by
  let C := traceNorm ⟨fixedBoxFiniteTestAction (X := 1) S hS1 f,
    fixedBoxFiniteTestAction_nuclear zero_lt_one S hS1 hS f⟩
  refine ⟨C, ?_, fun X hX ↦ (fixedBoxFiniteTestAction_traceNorm_eq 1 X zero_lt_one hX S hS1 hS f).le⟩
  exact (norm_nonneg (hilbertTrace ⟨fixedBoxFiniteTestAction (X := 1) S hS1 f,
    fixedBoxFiniteTestAction_nuclear zero_lt_one S hS1 hS f⟩)).trans (norm_hilbertTrace_le _)

end RiemannMasullo.RationalPacket
