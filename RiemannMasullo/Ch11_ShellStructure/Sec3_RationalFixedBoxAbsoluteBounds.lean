module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearEigenvalues
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFrequencyQuotients

/-! # Absolute Fourier-symbol bounds in actual rational packets

For the unweighted rational fixed-box model of (11.3.1.3)-(11.3.1.4), pp. 494-496,
the actual nuclear norm dominates the full absolute Fourier-symbol sum and is
at most sqrt(p) times that sum. The bound is uniform in the earlier prime set
and the positive total Fourier box. This proves the absolute-eigenvalue step
in mrshu's #7351 comment 7152400629. It does not identify a physical shell or
extend the result to positive strip width or higher Sobolev order.
-/

public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform NNReal
namespace RiemannMasullo.RationalPacket

/-- The full absolute sum of any finite selection of Fourier eigenvalues is a
lower bound for the actual singleton-prime trace norm. -/
theorem fixedBoxSingleton_traceNorm_ge_abs_samples {X : ℝ} (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
    (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime)
    (m : ℕ) (n : Fin m → ℤ) (hn : Injective n) (f : PositiveTimeTest) :
    (∑ i : Fin m, ‖(𝓕 (positiveTestToSchwartz f)) ((n i : ℝ) / Real.log p)‖) ≤
      traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
        fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ := by
  apply sum_norm_eigen_coordinates_le_traceNorm m (fixedBoxFrequencyRows X p m n)
    (fixedBoxFrequencyRows_surjective hX p hp m n hn)
  intro F i
  have hi := congrFun (fixedBoxFrequencyRows_singleton_intertwines hX p hp hS1 m n f F) i
  simpa only [fixedBoxFrequencyMatrix_apply] using hi

/-- The absolute Fourier-sample series is bounded by the trace norm of the
actual singleton-prime theta compression. -/
theorem fixedBoxSingleton_traceNorm_ge_abs_symbol {X : ℝ} (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
    (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime) (f : PositiveTimeTest) :
    (∑' k : ℤ, ‖(𝓕 (positiveTestToSchwartz f)) ((k : ℝ) / Real.log p)‖) ≤
      traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
        fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ := by
  classical
  have hs := summable_fixedBox_test_symbol p hp (positiveTestToSchwartz f)
  apply le_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  let e := Fintype.equivFin s
  let n : Fin (Fintype.card s) → ℤ := fun i ↦ (e.symm i).val
  have hn : Injective n := Subtype.val_injective.comp e.symm.injective
  have hb := fixedBoxSingleton_traceNorm_ge_abs_samples hX p hp hS1 hS (Fintype.card s) n hn f
  have hsum : (∑ k ∈ s, ‖(𝓕 (positiveTestToSchwartz f)) ((k : ℝ) / Real.log p)‖) =
      ∑ i : Fin (Fintype.card s), ‖(𝓕 (positiveTestToSchwartz f)) ((n i : ℝ) / Real.log p)‖ := by
    have hs' : (∑ k ∈ s, ‖(𝓕 (positiveTestToSchwartz f)) ((k : ℝ) / Real.log p)‖) =
        ∑ k : s, ‖(𝓕 (positiveTestToSchwartz f)) ((k.val : ℝ) / Real.log p)‖ :=
      Finset.sum_subtype s (fun _ ↦ Iff.rfl)
        (fun k : ℤ ↦ ‖(𝓕 (positiveTestToSchwartz f)) ((k : ℝ) / Real.log p)‖)
    exact hs'.trans (e.symm.sum_comp
      (fun k : s ↦ ‖(𝓕 (positiveTestToSchwartz f)) ((k.val : ℝ) / Real.log p)‖)).symm
  exact hsum.trans_le hb

/-- The actual prime-level trace norm lies between the absolute Fourier-symbol
sum and sqrt(p) times that sum, in every positive total Fourier box. -/
theorem fixedBoxSingleton_traceNorm_symbol_bounds {X : ℝ} (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
    (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime) (f : PositiveTimeTest) :
    let M := ∑' k : ℤ, ‖(𝓕 (positiveTestToSchwartz f)) ((k : ℝ) / Real.log p)‖
    M ≤ traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
        fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ ∧
      traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
        fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ ≤ Real.sqrt p * M := by
  dsimp only
  refine ⟨fixedBoxSingleton_traceNorm_ge_abs_symbol hX p hp hS1 hS f,?_⟩
  have he : fixedBoxFiniteTestAction (X := X) {p} hS1 f =
      fixedBoxLayerTestAction ∅ (by simp) p hS1 hX hp (by simp) (positiveTestToSchwartz f) := by
    rw [fixedBoxFiniteTestAction_def]
    simpa only [Finset.insert_empty] using!
      (fixedBoxLayerTestAction_eq_compression hX ∅ (by simp) p hS1 hp (by simp) f).symm
  obtain ⟨hn,hb,_⟩ := fixedBoxLayerTestAction_nuclear_trace ∅ (by simp) p hS1 hX hp
    (by simp) (by simp) (positiveTestToSchwartz f)
  simpa only [he] using! hb

variable {X : ℝ} (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q)
variable (hX : 0 < X) (hp : p.Prime) (hpT : p ∉ T) (hT : ∀ q ∈ T, q.Prime)
local notation "Q" => FixedBoxQuotient[X,T,hT1,p,hTp1]
local instance : NormedSpace ℂ Q := Submodule.Quotient.normedSpace _ ℂ
local instance : NormedSpace ℝ Q := Submodule.Quotient.normedSpace _ ℝ
local notation "ℓ" => fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT

/-- The actual completed packet coordinates diagonalize every Schwartz test action. -/
theorem fixedBoxPacketRow_testAction (w : 𝓢(ℝ, ℂ)) (n : ℤ) (u : Q) :
    ℓ n (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w u) =
      (𝓕 w) ((n : ℝ) / Real.log p) * ℓ n u := by
  obtain ⟨v,hrow,heigen,_,hd,_⟩ := exists_fixedBox_total_eigen_cardinals T hT1 p hTp1 hX hp hpT hT
  have he : (ℓ n).comp (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w) =
      (𝓕 w) ((n : ℝ) / Real.log p) • ℓ n := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr hd)
    rintro _ ⟨k,rfl⟩
    rw [ContinuousLinearMap.comp_apply, fixedBoxTestAction_eigen T hT1 p hTp1 hX hp hpT
      w k (v k) (fun s ↦ heigen s k), map_smul, smul_apply]
    simp only [smul_eq_mul, hrow]
    by_cases hnk : n = k
    · subst n
      simp
    · simp [hnk]
  exact congrArg (fun B : Q →L[ℂ] ℂ ↦ B u) he

/-- In every actual completed packet, including arbitrary earlier prime factors,
the nuclear norm lies between the absolute Fourier-symbol sum and sqrt(p) times
that sum. The estimate holds for every Schwartz test. -/
theorem fixedBoxTestAction_traceNorm_symbol_bounds (hT : ∀ q ∈ T, q.Prime)
    (w : 𝓢(ℝ, ℂ)) :
    ∃ h : IsNuclearOperator (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w),
      (∑' n : ℤ, ‖(𝓕 w) ((n : ℝ) / Real.log p)‖) ≤
        traceNorm (H := Q) ⟨fixedBoxTestAction T hT1 p hTp1 hX hp hpT w,h⟩ ∧
      traceNorm (H := Q) ⟨fixedBoxTestAction T hT1 p hTp1 hX hp hpT w,h⟩ ≤
        Real.sqrt p * (∑' n : ℤ, ‖(𝓕 w) ((n : ℝ) / Real.log p)‖) := by
  have hex := fixedBoxTestAction_nuclear_trace (X := X) T hT1 p hTp1 hX hp hpT hT w
  refine ⟨hex.choose,?_,hex.choose_spec.1⟩
  have hv := exists_fixedBox_rankOne_projections T hT1 p hTp1 hX hp hpT hT
  let v := hv.choose
  have hrow := hv.choose_spec.1
  let L := fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT
  have hLA (u : Q) (n : ℤ) :
      L n (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w u) =
        (𝓕 w) ((n : ℝ) / Real.log p) * L n u :=
    fixedBoxPacketRow_testAction T hT1 p hTp1 hX hp hpT hT w n u
  simpa only using! (nuclear_eigen_coordinates_summable (H := Q) L v hrow
    (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w) hex.choose
    (fun n ↦ (𝓕 w) ((n : ℝ) / Real.log p)) hLA).2

end RiemannMasullo.RationalPacket
