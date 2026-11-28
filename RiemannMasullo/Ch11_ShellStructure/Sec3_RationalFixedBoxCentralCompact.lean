module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCentralBound
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.CompactFiniteQuotient

/-! # A compactness obstruction for the original rational theta stage

The central jet quotients force the original-stage test action to stay at least
its absolute test mass away from every compact operator. In particular the
finite prime levels cannot approximate it in operator norm when that mass is
nonzero. These are statements in the actual unweighted logarithmic model for
(11.3.1.3)–(11.3.1.4), pp. 494–496; positive-width or higher-Sobolev constructions
are not addressed here.
-/

public noncomputable section
open Set Function MeasureTheory
namespace RiemannMasullo.RationalPacket


private theorem centralRows_originalCompression {X : ℝ} (hX : 0 < X)
    (f : PositiveTimeTest) (m : ℕ) (F : LogL2) :
    fixedBoxCentralRows X m
      (((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection)) F) =
      centralJetTestMatrix m f (fixedBoxCentralRows X m F) := by
  let P := (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection
  have hPF : P F ∈ closedStageSubmodule X ∅ (by simp) :=
    ((closedStageSubmodule X ∅ (by simp)).toSubmodule.orthogonalProjectionOnto F).property
  have hAP := fixedBoxAmbientTestAction_mem hX ∅ (by simp) f (P F) hPF
  have heP : P (fixedBoxAmbientTestAction f (P F)) = fixedBoxAmbientTestAction f (P F) :=
    Submodule.starProjection_eq_self_iff.mpr hAP
  change fixedBoxCentralRows X m (P (fixedBoxAmbientTestAction f (P F))) = _
  rw [heP, fixedBoxCentralRows_ambientTest hX m f (P F) hPF]
  congr 1
  apply funext
  intro i
  rw [fixedBoxCentralRows_apply, fixedBoxCentralRows_apply]
  congr 1
  exact Submodule.starProjection_eq_self_iff.mpr hPF

/-- Every compact operator stays at least the test mass away from the actual
original-stage test action in operator norm. -/
theorem fixedBoxOriginalTestAction_norm_sub_compact_ge {X : ℝ} (hX : 0 < X)
    (f : PositiveTimeTest) (K : LogL2 →L[ℂ] LogL2) (hK : IsCompactOperator K) :
    ‖∫ t : ℝ, f t‖ ≤
      ‖(closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection) - K‖ :=
  norm_sub_compact_ge_of_finite_quotient_diagonal _ _ (fixedBoxCentralRows X)
    (fixedBoxCentralRows_surjective hX) (fun m ↦ centralJetTestMatrix m f)
    (centralRows_originalCompression hX f) (fun m ↦ centralJetTestMatrix_diagonal m f) K hK

/-- Nonzero test mass makes the actual original-stage action noncompact in the
unweighted logarithmic model. -/
theorem fixedBoxOriginalTestAction_not_compact {X : ℝ} (hX : 0 < X)
    (f : PositiveTimeTest) (hf : (∫ t : ℝ, f t) ≠ 0) :
    ¬ IsCompactOperator
      ((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection)) := by
  intro hK
  have hb := fixedBoxOriginalTestAction_norm_sub_compact_ge hX f _ hK
  rw [sub_self, norm_zero] at hb
  exact (norm_pos_iff.mpr hf).not_ge hb

/-- No finite prime level approximates the original stage in operator norm
better than the absolute test mass. -/
theorem fixedBoxOriginalTestAction_norm_sub_finite_ge {X : ℝ} (hX : 0 < X)
    (S : Finset ℕ) (hS1 : ∀ p ∈ S, 1 ≤ p) (hS : ∀ p ∈ S, p.Prime)
    (f : PositiveTimeTest) :
    ‖∫ t : ℝ, f t‖ ≤
      ‖(closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection) -
        fixedBoxFiniteTestAction (X := X) S hS1 f‖ := by
  apply fixedBoxOriginalTestAction_norm_sub_compact_ge hX f
  exact ((mem_traceClassOperators_iff_isNuclearOperator _).mpr
    (fixedBoxFiniteTestAction_nuclear hX S hS1 hS f)).1



end RiemannMasullo.RationalPacket
