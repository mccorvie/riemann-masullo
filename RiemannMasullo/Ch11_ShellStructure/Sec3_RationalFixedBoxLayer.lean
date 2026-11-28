module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxNuclear
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.QuotientLayer
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRetraction

/-! # Nuclear traces of actual closed-stage orthogonal layers

Paper: (11.3.1.3)–(11.3.1.4), p. 494. The completed relative packet is embedded
isometrically in the original logarithmic Hilbert space. Its projection is the
difference of the genuine consecutive closed theta-stage projections. The
transported test action is the two-sided compression of actual forward shifts,
and has the packet Poisson trace. Compact positive-time tests have zero layer
trace uniformly for all sufficiently large primes.

This concerns the rational trivial-angular unweighted logarithmic model.
Identification with the adelic geometric shell and physical cutoffs is separate.
-/

public noncomputable section
open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform NNReal
namespace RiemannMasullo.RationalPacket
variable {X : ℝ} (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q)
local notation "E" => closedStageSubmodule X T hT1
local notation "D" => fixedBoxDenominator X T hT1 p hTp1
local notation "Q" => FixedBoxQuotient[X,T,hT1,p,hTp1]
local notation "N" => closedStageSubmodule X (insert p T) hTp1

/-- Isometric embedding of the actual relative packet in the original logarithmic L². -/
def fixedBoxLayerSection : Q →ₗᵢ[ℂ] LogL2 := nestedQuotientSection E D

/-- Project to the preceding theta stage and then take the actual relative class. -/
def fixedBoxLayerQuotient : LogL2 →L[ℂ] Q := nestedQuotientMap E D

/-- The orthogonal layer projection in the original logarithmic Hilbert space. -/
def fixedBoxLayerProjection : LogL2 →L[ℂ] LogL2 :=
  (fixedBoxLayerSection (X := X) T hT1 p hTp1).toContinuousLinearMap.comp
    (fixedBoxLayerQuotient (X := X) T hT1 p hTp1)

local notation "J" => fixedBoxLayerSection (X := X) T hT1 p hTp1
local notation "q" => fixedBoxLayerQuotient (X := X) T hT1 p hTp1
local notation "P" => fixedBoxLayerProjection (X := X) T hT1 p hTp1

theorem fixedBoxLayerQuotient_subtype (u : E) : q u = (D).toSubmodule.mkQL u :=
  nestedQuotientMap_subtype E D u

theorem fixedBoxLayerQuotient_section :
    (q).comp (J).toContinuousLinearMap = ContinuousLinearMap.id ℂ Q :=
  nestedQuotientMap_section E D

theorem norm_fixedBoxLayerQuotient_le : ‖q‖ ≤ 1 := norm_nestedQuotientMap_le E D

theorem fixedBoxLayerProjection_apply (F : LogL2) : P F = J (q F) := by rfl

/-- Both genuine closed stages are nested in the fixed total box. -/
theorem fixedBox_nextStage_le (hX : 0 < X) : (N).toSubmodule ≤ (E).toSubmodule := by
  intro F hF
  apply (mem_closedStageSubmodule_iff X T hT1 F).mpr
  exact closure_mono (stageGenerators_insert_subset hX T hT1 (hTp1 p (Finset.mem_insert_self p T)))
    ((mem_closedStageSubmodule_iff X (insert p T) hTp1 F).mp hF)

/-- The layer is the difference of the actual consecutive closed-stage projections. -/
theorem fixedBoxLayerProjection_eq_difference (hX : 0 < X) :
    P = (E).toSubmodule.starProjection - (N).toSubmodule.starProjection :=
  nestedQuotientSection_map_eq_difference E D N
    (fixedBox_nextStage_le T hT1 p hTp1 hX)
    (mem_fixedBoxDenominator_iff X T hT1 p hTp1)

variable (hX : 0 < X) (hp : p.Prime) (hpT : p ∉ T)

/-- On the preceding stage, the ambient quotient map intertwines the actual forward shifts. -/
theorem fixedBoxLayerQuotient_halfShift (h : ℝ≥0) (u : E) :
    q (halfShift (h : ℝ) (u : LogL2)) =
      fixedBoxForwardShift T hT1 p hTp1 hX h ((D).toSubmodule.mkQL u) := by
  rw [← closedStageForwardShift_apply T hT1 hX h u, fixedBoxLayerQuotient_subtype,
    fixedBoxForwardShift_mk]

/-- Transporting a quotient shift gives the actual two-sided layer compression. -/
theorem fixedBoxLayerSection_forwardShift (h : ℝ≥0) (F : LogL2) :
    J (fixedBoxForwardShift T hT1 p hTp1 hX h (q F)) = P (halfShift (h : ℝ) (P F)) := by
  let u : E := quotientOrthogonalSection D (q F)
  have hu : (D).toSubmodule.mkQL u = q F := quotientOrthogonalSection_rightInverse D (q F)
  have hJ : (u : LogL2) = J (q F) := by
    exact (nestedQuotientSection_apply E D (q F)).symm
  rw [fixedBoxLayerProjection_apply, fixedBoxLayerProjection_apply]
  rw [← hJ, fixedBoxLayerQuotient_halfShift T hT1 p hTp1 hX h u, hu]

/-- A Schwartz test acts on the actual orthogonal layer, extended by zero on its complement. -/
def fixedBoxLayerTestAction (w : 𝓢(ℝ, ℂ)) : LogL2 →L[ℂ] LogL2 :=
  (J).toContinuousLinearMap.comp
    ((fixedBoxTestAction T hT1 p hTp1 hX hp hpT w).comp q)

/-- For nonnegative support this is the vector integral of the actual compressed forward action. -/
theorem fixedBoxLayerTestAction_apply_forward (w : 𝓢(ℝ, ℂ))
    (hw : Function.support w ⊆ Ici 0) (F : LogL2) :
    fixedBoxLayerTestAction T hT1 p hTp1 hX hp hpT w F =
      ∫ t : ℝ, w t • P (halfShift (t.toNNReal : ℝ) (P F)) := by
  change J (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w (q F)) = _
  rw [fixedBoxTestAction_eq_forward_integral T hT1 p hTp1 hX hp hpT w hw]
  rw [← (J).integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul, fixedBoxLayerSection_forwardShift]

/-- The genuine orthogonal-layer test action is nuclear, with the same Fourier
trace and the same trace-norm estimate as the completed packet. -/
theorem fixedBoxLayerTestAction_nuclear_trace (hT : ∀ r ∈ T, r.Prime)
    (w : 𝓢(ℝ, ℂ)) :
    ∃ h : IsNuclearOperator (fixedBoxLayerTestAction T hT1 p hTp1 hX hp hpT w),
      traceNorm ⟨_, h⟩ ≤ Real.sqrt p *
        (∑' n : ℤ, ‖(𝓕 w) ((n : ℝ) / Real.log p)‖) ∧
      HasSum (fun n : ℤ ↦ (𝓕 w) ((n : ℝ) / Real.log p)) (hilbertTrace ⟨_, h⟩) := by
  have hquot := fixedBoxTestAction_nuclear_trace T hT1 p hTp1 hX hp hpT hT w
  rcases hquot with ⟨hn, hb, ht⟩
  have htrans := nuclear_trace_retraction (J).toContinuousLinearMap q
    (fixedBoxLayerQuotient_section (X := X) T hT1 p hTp1)
    (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w) hn
  rcases htrans with ⟨hn', hb', ht'⟩
  refine ⟨hn', ?_, ?_⟩
  · apply le_trans hb'
    apply le_trans _ hb
    have hprod : ‖(J).toContinuousLinearMap‖ * ‖q‖ ≤ 1 := by
      exact (mul_le_mul (J).norm_toContinuousLinearMap_le
        (norm_fixedBoxLayerQuotient_le (X := X) T hT1 p hTp1) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod ((norm_nonneg (hilbertTrace ⟨fixedBoxTestAction T hT1 p hTp1 hX hp hpT w, hn⟩)).trans (norm_hilbertTrace_le _))
  · simpa only [fixedBoxLayerTestAction, ht'] using! ht

/-- The actual orthogonal difference layer has the logarithmic Poisson trace. -/
theorem fixedBoxLayerTestAction_poisson_trace (hT : ∀ r ∈ T, r.Prime)
    (w : 𝓢(ℝ, ℂ)) :
    ∃ h : IsNuclearOperator (fixedBoxLayerTestAction T hT1 p hTp1 hX hp hpT w),
      hilbertTrace ⟨_, h⟩ = (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, w (Real.log p * k) := by
  have hex := fixedBoxLayerTestAction_nuclear_trace T hT1 p hTp1 hX hp hpT hT w
  rcases hex with ⟨h, _, ht⟩
  exact ⟨h, ht.tsum_eq.symm.trans (fixedBox_test_symbol_poisson p hp w)⟩

/-- Strict first-period support kills the trace of the actual ambient layer compression. -/
theorem fixedBoxLayerTestAction_trace_eq_zero (hT : ∀ r ∈ T, r.Prime)
    (w : 𝓢(ℝ, ℂ)) (hw : Function.support w ⊆ Ioo 0 (Real.log p)) :
    ∃ h : IsNuclearOperator (fixedBoxLayerTestAction T hT1 p hTp1 hX hp hpT w),
      hilbertTrace ⟨_, h⟩ = 0 := by
  have hquot := fixedBoxTestAction_trace_eq_zero T hT1 p hTp1 hX hp hpT hT w hw
  rcases hquot with ⟨hn, ht⟩
  have htrans := nuclear_trace_retraction (J).toContinuousLinearMap q
    (fixedBoxLayerQuotient_section (X := X) T hT1 p hTp1)
    (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w) hn
  rcases htrans with ⟨hn', _, ht'⟩
  exact ⟨hn', ht'.trans ht⟩

/-- A fixed compact positive-time test has zero layer trace for all sufficiently
large primes, uniformly in the total box and all preceding finite factors. -/
theorem eventually_fixedBoxLayerTestAction_trace_eq_zero
    (w : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport w)
    (hw : Function.support w ⊆ Ioi 0) :
    ∃ B : ℕ, ∀ (r : ℕ) (hr : r.Prime), B < r →
      ∀ (Y : ℝ) (hY : 0 < Y) (S : Finset ℕ) (hS1 : ∀ k ∈ S, 1 ≤ k)
        (hSr1 : ∀ k ∈ insert r S, 1 ≤ k) (_hS : ∀ k ∈ S, k.Prime) (hrS : r ∉ S),
        ∃ h : IsNuclearOperator (fixedBoxLayerTestAction S hS1 r hSr1 hY hr hrS w),
          hilbertTrace ⟨_, h⟩ = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp R)
  refine ⟨B, fun r hr hBr Y hY S hS1 hSr1 hS hrS ↦ ?_⟩
  apply fixedBoxLayerTestAction_trace_eq_zero S hS1 r hSr1 hY hr hrS hS w
  intro t ht
  refine ⟨hw ht, ?_⟩
  apply lt_of_le_of_lt (hR (subset_tsupport w ht))
  apply (Real.lt_log_iff_exp_lt (by exact_mod_cast hr.pos)).mpr
  exact hB.trans (by exact_mod_cast hBr)

end RiemannMasullo.RationalPacket
