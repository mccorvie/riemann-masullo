module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCentralBound

/-! # Divergence and non-nuclearity forced by the central jet flag

These results concern the actual unweighted rational logarithmic model for
(11.3.1.3)–(11.3.1.4), pp. 494–496. They do not assert a failure of the
paper's positive-width or higher-order Sobolev constructions.
-/

public noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannMasullo.RationalPacket

/-- Trace norms diverge along every prime-level family whose cardinalities
increase without bound, even when the positive total box varies arbitrarily. -/
theorem fixedBoxFiniteTestAction_traceNorm_tendsto_atTop
    {ι : Type*} {l : Filter ι} (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (S : ι → Finset ℕ) (hS1 : ∀ i p, p ∈ S i → 1 ≤ p)
    (hS : ∀ i p, p ∈ S i → p.Prime)
    (f : PositiveTimeTest) (hf : (∫ t : ℝ, f t) ≠ 0)
    (hcard : Tendsto (fun i ↦ (S i).card) l atTop) :
    Tendsto (fun i ↦ traceNorm ⟨fixedBoxFiniteTestAction (X := X i) (S i) (hS1 i) f,
      fixedBoxFiniteTestAction_nuclear (hX i) (S i) (hS1 i) (hS i) f⟩) l atTop := by
  have hc : Tendsto (fun i ↦ ((S i).card : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hcard
  exact tendsto_atTop_mono
    (fun i ↦ fixedBoxFiniteTestAction_traceNorm_ge_card (hX i) (S i) (hS1 i) (hS i) f)
    (hc.atTop_mul_const (norm_pos_iff.mpr hf))

/-- The distance in trace norm from every fixed nuclear operator also diverges;
in particular these finite-level operators cannot converge in trace norm. -/
theorem fixedBoxFiniteTestAction_traceNorm_sub_tendsto_atTop
    {ι : Type*} {l : Filter ι} (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (S : ι → Finset ℕ) (hS1 : ∀ i p, p ∈ S i → 1 ≤ p)
    (hS : ∀ i p, p ∈ S i → p.Prime)
    (f : PositiveTimeTest) (hf : (∫ t : ℝ, f t) ≠ 0)
    (hcard : Tendsto (fun i ↦ (S i).card) l atTop) (T : nuclearEndomorphisms LogL2) :
    Tendsto (fun i ↦ traceNorm
      ((⟨fixedBoxFiniteTestAction (X := X i) (S i) (hS1 i) f,
        fixedBoxFiniteTestAction_nuclear (hX i) (S i) (hS1 i) (hS i) f⟩ :
          nuclearEndomorphisms LogL2) - T)) l atTop := by
  let A (i : ι) : nuclearEndomorphisms LogL2 :=
    ⟨fixedBoxFiniteTestAction (X := X i) (S i) (hS1 i) f,
      fixedBoxFiniteTestAction_nuclear (hX i) (S i) (hS1 i) (hS i) f⟩
  have hlim := fixedBoxFiniteTestAction_traceNorm_tendsto_atTop X hX S hS1 hS f hf hcard
  apply tendsto_atTop_mono (f := fun i ↦ traceNorm (A i) - traceNorm T) _
    (by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-(traceNorm T)) hlim)
  intro i
  let : Norm (nuclearEndomorphisms LogL2) := ⟨traceNorm⟩
  have htri := (traceNorm_normedSpaceCore (H := LogL2)).norm_triangle (A i - T) T
  change traceNorm (A i - T + T) ≤ traceNorm (A i - T) + traceNorm T at htri
  rw [sub_add_cancel] at htri
  linarith

/-- For nonzero test mass, compression to the original theta stage is not nuclear
in the unweighted logarithmic model: its central quotients have arbitrarily large
finite dimension, each with the same nonzero diagonal. -/
theorem fixedBoxOriginalTestAction_not_nuclear {X : ℝ} (hX : 0 < X)
    (f : PositiveTimeTest) (hf : (∫ t : ℝ, f t) ≠ 0) :
    ¬ IsNuclearOperator
      ((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection)) := by
  intro hA
  let P := (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection
  let A := P.comp ((fixedBoxAmbientTestAction f).comp P)
  have hc : 0 < ‖∫ t : ℝ, f t‖ := norm_pos_iff.mpr hf
  obtain ⟨m,hm⟩ := exists_nat_gt (traceNorm ⟨A,hA⟩ / ‖∫ t : ℝ, f t‖)
  have hAB (F : LogL2) : fixedBoxCentralRows X m (A F) =
      centralJetTestMatrix m f (fixedBoxCentralRows X m F) := by
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
  have hb := traceNorm_ge_finite_quotient_diagonal m (fixedBoxCentralRows X m)
    (fixedBoxCentralRows_surjective hX m) A hA (centralJetTestMatrix m f) hAB _
    (centralJetTestMatrix_diagonal m f)
  exact (not_lt_of_ge hb) ((div_lt_iff₀ hc).mp hm)

end RiemannMasullo.RationalPacket
