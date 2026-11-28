module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTower

/-! # Actual finite Fourier-coordinate quotients of rational theta actions

The common-box cardinal vectors make every selected finite list of distinct
prime-mesh coordinates onto. Their exact diagonal Fourier-test action descends
both from the original stage and from its singleton-prime relative level.
-/

public noncomputable section
open Set Function
namespace RiemannMasullo.RationalPacket
open MeasureTheory
open scoped FourierTransform SchwartzMap Topology
variable {X : ℝ}
local instance (M : ClosedSubmodule ℂ LogL2) : IsClosed (M.toSubmodule : Set LogL2) := M.isClosed
local notation "E₀" => closedStageSubmodule X ∅ (by simp)

/-- Finite prime-mesh coordinates of the original-stage component. -/
def fixedBoxFrequencyRows (X : ℝ) (p m : ℕ) (n : Fin m → ℤ) :
    LogL2 →L[ℂ] (Fin m → ℂ) :=
  (ContinuousLinearMap.pi (fun i ↦ packetRow X ∅ p (n i))).comp
    (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection

theorem fixedBoxFrequencyRows_apply (X : ℝ) (p m : ℕ) (n : Fin m → ℤ)
    (F : LogL2) (i : Fin m) :
    fixedBoxFrequencyRows X p m n F i = packetRow X ∅ p (n i)
      ((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection F) := by rfl

/-- Genuine theta cardinal vectors make every finite list of distinct packet rows onto. -/
theorem fixedBoxFrequencyRows_surjective (hX : 0 < X) (p : ℕ) (hp : p.Prime)
    (m : ℕ) (n : Fin m → ℤ) (hn : Injective n) :
    Surjective (fixedBoxFrequencyRows X p m n) := by
  classical
  obtain ⟨v,hv,hrow⟩ := exists_fixedBox_biorthogonal_stage hX ∅ (by simp) hp (by simp)
  have hvE (k : ℤ) : v k ∈ E₀ :=
    (mem_closedStageSubmodule_iff X ∅ (by simp) _).mpr (subset_closure (hv k))
  intro y
  let F := ∑ i : Fin m, y i • v (n i)
  have hFE : F ∈ E₀ := (E₀).sum_mem (fun i _ ↦ (E₀).smul_mem _ (hvE _))
  refine ⟨F,funext fun j ↦ ?_⟩
  rw [fixedBoxFrequencyRows_apply, Submodule.starProjection_eq_self_iff.mpr hFE]
  dsimp only [F]
  simp only [map_sum, map_smul, smul_eq_mul, hrow, hn.eq_iff]
  simp

private theorem positiveTest_fourier_character (f : PositiveTimeTest) (ξ : ℝ) :
    (∫ t : ℝ, f t * (Real.fourierChar (-t * ξ) : ℂ)) =
      (𝓕 (positiveTestToSchwartz f)) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Circle.smul_def, smul_eq_mul, positiveTestToSchwartz_apply, neg_mul]
  ring

/-- The actual positive test acts diagonally on every empty-stage packet row. -/
theorem packetRow_ambientTest_empty (hX : 0 < X) (p : ℕ) (hp : p.Prime)
    (n : ℤ) (f : PositiveTimeTest) (F : LogL2) (hF : F ∈ E₀) :
    packetRow X ∅ p n (fixedBoxAmbientTestAction f F) =
      (𝓕 (positiveTestToSchwartz f)) ((n : ℝ) / Real.log p) * packetRow X ∅ p n F := by
  have hi : Integrable (fun t : ℝ ↦ f t • halfShift (t.toNNReal : ℝ) F) volume :=
    (f.continuous.smul ((continuous_halfShift F).comp (by fun_prop))).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  rw [fixedBoxAmbientTestAction_apply, ← (packetRow X ∅ p n).integral_comp_comm hi,
    ← positiveTest_fourier_character, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul, smul_eq_mul]
  by_cases ht : f t = 0
  · simp only [ht, zero_mul]
  have ht0 : 0 < t := f.tsupport_subset (subset_tsupport f ht)
  rw [Real.coe_toNNReal t ht0.le, packetRow_halfShift hX ∅ (by simp) hp (by simp) ht0.le
    ((mem_closedStageSubmodule_iff X ∅ (by simp) F).mp hF) n]
  ring

/-- The exact Fourier-symbol matrix of a selected finite packet-coordinate quotient. -/
def fixedBoxFrequencyMatrix (p m : ℕ) (n : Fin m → ℤ) (f : PositiveTimeTest) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  LinearMap.pi (fun i ↦ (𝓕 (positiveTestToSchwartz f)) ((n i : ℝ) / Real.log p) • LinearMap.proj i)

theorem fixedBoxFrequencyMatrix_apply (p m : ℕ) (n : Fin m → ℤ) (f : PositiveTimeTest)
    (y : Fin m → ℂ) (i : Fin m) :
    fixedBoxFrequencyMatrix p m n f y i =
      (𝓕 (positiveTestToSchwartz f)) ((n i : ℝ) / Real.log p) * y i := by rfl

private theorem frequencyRows_on_empty (p m : ℕ) (n : Fin m → ℤ)
    (F : LogL2) (hF : F ∈ E₀) (i : Fin m) :
    fixedBoxFrequencyRows X p m n F i = packetRow X ∅ p (n i) F := by
  rw [fixedBoxFrequencyRows_apply, Submodule.starProjection_eq_self_iff.mpr hF]

/-- The selected frequency rows intertwine the original-stage compression. -/
theorem fixedBoxFrequencyRows_original_intertwines (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (m : ℕ) (n : Fin m → ℤ) (f : PositiveTimeTest) (F : LogL2) :
    fixedBoxFrequencyRows X p m n
      (((E₀).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp (E₀).toSubmodule.starProjection)) F) =
      fixedBoxFrequencyMatrix p m n f (fixedBoxFrequencyRows X p m n F) := by
  have hPF : (E₀).toSubmodule.starProjection F ∈ E₀ :=
    ((E₀).toSubmodule.orthogonalProjectionOnto F).property
  have hAP := fixedBoxAmbientTestAction_mem hX ∅ (by simp) f _ hPF
  simp only [ContinuousLinearMap.comp_apply,
    Submodule.starProjection_eq_self_iff.mpr hAP]
  apply funext
  intro i
  rw [frequencyRows_on_empty _ _ _ _ hAP i,
    packetRow_ambientTest_empty hX p hp _ f _ hPF, fixedBoxFrequencyMatrix_apply,
    fixedBoxFrequencyRows_apply]

private theorem frequency_relative_mem_empty (hX : 0 < X) (p : ℕ)
    (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q) (F : LogL2) :
    ((E₀).toSubmodule.starProjection - (closedStageSubmodule X {p} hS1).toSubmodule.starProjection) F ∈ E₀ := by
  apply (E₀).sub_mem
  · exact ((E₀).toSubmodule.orthogonalProjectionOnto F).property
  · exact fixedBox_stage_le_empty hX {p} hS1
      ((closedStageSubmodule X {p} hS1).toSubmodule.orthogonalProjectionOnto F).property

private theorem frequencyRows_relative (hX : 0 < X) (p : ℕ) (hp : p.Prime)
    (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q) (m : ℕ) (n : Fin m → ℤ) (F : LogL2) :
    fixedBoxFrequencyRows X p m n
      (((E₀).toSubmodule.starProjection - (closedStageSubmodule X {p} hS1).toSubmodule.starProjection) F) =
      fixedBoxFrequencyRows X p m n F := by
  apply funext
  intro i
  rw [frequencyRows_on_empty _ _ _ _ (frequency_relative_mem_empty hX p hS1 F) i, sub_apply, map_sub]
  have hz := packetRow_eq_zero_of_mem_next hX ∅ (by simp) hp (by simp)
    ((mem_closedStageSubmodule_iff X {p} hS1 _).mp
      ((closedStageSubmodule X {p} hS1).toSubmodule.orthogonalProjectionOnto F).property) (n i)
  have hz' : packetRow X ∅ p (n i) ((closedStageSubmodule X {p} hS1).toSubmodule.starProjection F) = 0 := hz
  rw [hz', sub_zero, fixedBoxFrequencyRows_apply]

/-- The same selected rows are an actual finite quotient of the singleton-prime action. -/
theorem fixedBoxFrequencyRows_singleton_intertwines (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
    (m : ℕ) (n : Fin m → ℤ) (f : PositiveTimeTest) (F : LogL2) :
    fixedBoxFrequencyRows X p m n (fixedBoxFiniteTestAction (X := X) {p} hS1 f F) =
      fixedBoxFrequencyMatrix p m n f (fixedBoxFrequencyRows X p m n F) := by
  let R := (E₀).toSubmodule.starProjection - (closedStageSubmodule X {p} hS1).toSubmodule.starProjection
  have hR : R F ∈ E₀ := frequency_relative_mem_empty hX p hS1 F
  have hAR := fixedBoxAmbientTestAction_mem hX ∅ (by simp) f (R F) hR
  rw [fixedBoxFiniteTestAction_def, closedLayerCompression_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, frequencyRows_relative hX p hp hS1]
  apply funext
  intro i
  rw [frequencyRows_on_empty _ _ _ _ hAR i, packetRow_ambientTest_empty hX p hp _ f (R F) hR,
    fixedBoxFrequencyMatrix_apply]
  congr 1
  rw [← frequencyRows_on_empty _ _ _ _ hR i]
  exact congrFun (frequencyRows_relative hX p hp hS1 m n F) i

end RiemannMasullo.RationalPacket
