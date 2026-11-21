module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
public import Mathlib.Analysis.LocallyConvex.Montel
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! # Compactness of bounded closed sets in the real-line Schwartz space -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function Metric Set Topology
open scoped SchwartzMap BoundedContinuousFunction OnePoint

private def compactifiedSchwartz (f : 𝓢(ℝ, ℂ)) : OnePoint ℝ →ᵇ ℂ :=
  .mkOfCompact (OnePoint.continuousMapMk ⟨f, f.continuous⟩ 0 (by
    change Tendsto (⇑f) (coclosedCompact ℝ) (𝓝 (0 : ℂ))
    rw [coclosedCompact_eq_cocompact]
    exact f.tendsto_cocompact))

/-- A bounded family of Schwartz functions is equicontinuous on the one-point
compactification, including at infinity where a single weighted bound suffices. -/
private theorem compactifiedSchwartz_equicontinuous {S : Set 𝓢(ℝ, ℂ)} (hS : IsVonNBounded ℂ S) :
    Equicontinuous (fun f : S ↦ ⇑(compactifiedSchwartz f.1)) := by
  have hb := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hS
  obtain ⟨A, hA, hdecay⟩ := hb (1, 0)
  obtain ⟨B, hB, hderiv⟩ := hb (0, 1)
  intro z
  induction z using OnePoint.rec with
  | infty =>
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    apply OnePoint.hasBasis_nhds_infty.eventually_iff.mpr
    refine ⟨closedBall 0 (A / ε), ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
    rintro _ (⟨x, hx, rfl⟩ | hz) f
    · change dist 0 (f.1 x) < ε
      rw [dist_zero_left]
      have hx' : A / ε < ‖x‖ := by
        simpa [mem_closedBall, dist_zero_right] using hx
      have h := f.1.norm_pow_mul_le_seminorm ℂ 1 x
      have hh : ‖x‖ * ‖f.1 x‖ < A := by simpa using h.trans_lt (hdecay _ f.property)
      have hpos : 0 < ‖x‖ := (div_pos hA hε).trans hx'
      exact lt_of_mul_lt_mul_left (hh.trans (by linarith [(div_lt_iff₀ hε).mp hx'])) hpos.le
    · subst hz
      simpa using hε
  | coe x =>
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
    filter_upwards [Metric.ball_mem_nhds x (div_pos hε hB)] with y hy f
    change dist (f.1 x) (f.1 y) < ε
    have hf : LipschitzWith ⟨B, hB.le⟩ (⇑f.1) := by
      apply lipschitzWith_of_nnNorm_deriv_le f.1.differentiable
      intro t
      change ‖deriv f.1 t‖ ≤ B
      have h := f.1.le_seminorm' ℂ 0 1 t
      simpa using h.trans (hderiv _ f.property).le
    apply (hf.dist_le_mul x y).trans_lt
    rw [dist_comm]
    exact (lt_div_iff₀' hB).mp hy

private theorem isCompact_closure_compactifiedSchwartz {S : Set 𝓢(ℝ, ℂ)} (hS : IsVonNBounded ℂ S) :
    IsCompact (closure (compactifiedSchwartz '' S)) := by
  obtain ⟨C, hC, hbound⟩ :=
    ((schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hS) (0, 0)
  apply BoundedContinuousFunction.arzela_ascoli (closedBall 0 C) (isCompact_closedBall _ _)
  · rintro _ x ⟨f, hf, rfl⟩
    induction x using OnePoint.rec with
    | infty => exact mem_closedBall_self hC.le
    | coe x =>
      change dist (f x) 0 ≤ C
      rw [dist_zero_right]
      exact (f.norm_le_seminorm ℂ x).trans (hbound f hf).le
  · let lift (f : compactifiedSchwartz '' S) : S :=
      ⟨f.property.choose, f.property.choose_spec.1⟩
    have h := (compactifiedSchwartz_equicontinuous hS).comp lift
    convert h using 1
    funext f x
    exact congrArg (fun g : OnePoint ℝ →ᵇ ℂ ↦ g x) f.property.choose_spec.2.symm

private def schwartzWeightedDeriv (k n : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ k)).comp (SchwartzMap.derivCLM ℂ ℂ ^ n)

private theorem schwartzWeightedDeriv_apply (k n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzWeightedDeriv k n f x = (x : ℂ) ^ k * iteratedDeriv n f x := by
  have h (n : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ n) f) = iteratedDeriv n f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ n) f)) = _
      rw [ih]
  change (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ k)) _ x = _
  have hpow : (fun x : ℝ ↦ (x : ℂ) ^ k).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.pow k
  rw [SchwartzMap.smulLeftCLM_apply_apply hpow]
  exact congrArg ((x : ℂ) ^ k * ·) (congrFun (h n) x)

private def schwartzCoordinates : 𝓢(ℝ, ℂ) →+ ((ℕ × ℕ) → OnePoint ℝ →ᵇ ℂ) where
  toFun f i := compactifiedSchwartz (schwartzWeightedDeriv i.1 i.2 f)
  map_zero' := by
    ext i x
    induction x using OnePoint.rec <;> simp [compactifiedSchwartz, OnePoint.continuousMapMk]
  map_add' f g := by
    ext i x
    induction x using OnePoint.rec <;> simp [compactifiedSchwartz, OnePoint.continuousMapMk]

private theorem norm_schwartzCoordinates (i : ℕ × ℕ) (f : 𝓢(ℝ, ℂ)) :
    ‖schwartzCoordinates f i‖ = SchwartzMap.seminorm ℂ i.1 i.2 f := by
  have hx (x : ℝ) : ‖schwartzCoordinates f i x‖ = |x| ^ i.1 * ‖iteratedDeriv i.2 f x‖ := by
    change ‖schwartzWeightedDeriv _ _ f x‖ = _
    rw [schwartzWeightedDeriv_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
    intro x
    induction x using OnePoint.rec with
    | infty => exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (apply_nonneg _ _)
    | coe x => exact (hx x).le.trans (f.le_seminorm' ℂ _ _ x)
  · exact f.seminorm_le_bound' ℂ _ _ (norm_nonneg _) fun x ↦
      (hx x).symm.le.trans ((schwartzCoordinates f i).norm_coe_le_norm x)

private theorem isUniformInducing_schwartzCoordinates : IsUniformInducing schwartzCoordinates := by
  apply AddMonoidHom.isUniformInducing_of_isInducing
  have hconv (l : Filter 𝓢(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ)) :
      l ≤ 𝓝 f ↔ Tendsto schwartzCoordinates l (𝓝 (schwartzCoordinates f)) := by
    change Tendsto id l (𝓝 f) ↔ _
    rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds, tendsto_pi_nhds]
    simp only [Metric.tendsto_nhds, dist_eq_norm, schwartzSeminormFamily, id,
      ← norm_schwartzCoordinates, map_sub, Pi.sub_apply]
  apply Topology.isInducing_iff_nhds.mpr
  intro f
  exact le_antisymm ((hconv _ f).mp le_rfl).le_comap ((hconv _ f).mpr tendsto_comap)

/-- Every closed bounded set of complex Schwartz functions on the real line is compact. -/
theorem schwartzMap_real_montel : MontelSpace ℂ 𝓢(ℝ, ℂ) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  constructor
  intro S hclosed hS
  apply TotallyBounded.isCompact_of_isClosed _ hclosed
  apply (totallyBounded_image_iff isUniformInducing_schwartzCoordinates).mp
  let K (i : ℕ × ℕ) := closure (compactifiedSchwartz '' (schwartzWeightedDeriv i.1 i.2 '' S))
  have hK (i : ℕ × ℕ) : IsCompact (K i) :=
    isCompact_closure_compactifiedSchwartz (hS.image (schwartzWeightedDeriv i.1 i.2))
  apply (isCompact_univ_pi hK).totallyBounded.subset
  rintro _ ⟨f, hf, rfl⟩ i _
  exact subset_closure (mem_image_of_mem _ (mem_image_of_mem _ hf))

/-- Extension by zero at infinity sends a bounded Schwartz family into a relatively compact
family for the supremum norm. -/
theorem schwartz_compactified_bounded (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    [ProperSpace D] : ∃ J : 𝓢(D, ℂ) →L[ℂ] (OnePoint D →ᵇ ℂ),
      (∀ f (x : D), J f x = f x) ∧
      ∀ S : Set 𝓢(D, ℂ), IsVonNBounded ℂ S → IsCompact (closure (J '' S)) := by
  let j (f : 𝓢(D, ℂ)) : OnePoint D →ᵇ ℂ := .mkOfCompact
    (OnePoint.continuousMapMk ⟨f, f.continuous⟩ 0 (by
      change Tendsto (⇑f) (coclosedCompact D) (𝓝 (0 : ℂ))
      rw [coclosedCompact_eq_cocompact]
      exact f.tendsto_cocompact))
  let J : 𝓢(D, ℂ) →L[ℂ] (OnePoint D →ᵇ ℂ) := SchwartzMap.mkCLMtoNormedSpace j
    (fun f g ↦ by ext x; induction x using OnePoint.rec <;> simp [j, OnePoint.continuousMapMk])
    (fun a f ↦ by ext x; induction x using OnePoint.rec <;> simp [j, OnePoint.continuousMapMk]) (by
      refine ⟨{(0, 0)}, 1, zero_le_one, fun f ↦ ?_⟩
      rw [one_mul, Finset.sup_singleton]
      apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
      intro x
      induction x using OnePoint.rec with
      | infty => exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (apply_nonneg _ _)
      | coe x => exact f.norm_le_seminorm ℂ x)
  refine ⟨J, fun _ _ ↦ rfl, ?_⟩
  intro S hS
  have hb := (schwartz_withSeminorms ℂ D ℂ).isVonNBounded_iff_seminorm_bounded.mp hS
  obtain ⟨C, hC, hbound⟩ := hb (0, 0)
  obtain ⟨A, hA, hdecay⟩ := hb (1, 0)
  obtain ⟨B, hB, hderiv⟩ := hb (0, 1)
  apply BoundedContinuousFunction.arzela_ascoli (closedBall 0 C) (isCompact_closedBall _ _)
  · rintro _ x ⟨f, hf, rfl⟩
    induction x using OnePoint.rec with
    | infty => exact mem_closedBall_self hC.le
    | coe x =>
      change dist (f x) 0 ≤ C
      rw [dist_zero_right]
      exact (f.norm_le_seminorm ℂ x).trans (hbound f hf).le
  · intro z
    induction z using OnePoint.rec with
    | infty =>
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      apply OnePoint.hasBasis_nhds_infty.eventually_iff.mpr
      refine ⟨closedBall 0 (A / ε), ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
      rintro _ (⟨x, hx, rfl⟩ | hz) ⟨_, f, hf, rfl⟩
      · change dist 0 (f x) < ε
        rw [dist_zero_left]
        have hx' : A / ε < ‖x‖ := by simpa [mem_closedBall, dist_zero_right] using hx
        have hh : ‖x‖ * ‖f x‖ < A := by
          simpa using (f.norm_pow_mul_le_seminorm ℂ 1 x).trans_lt (hdecay _ hf)
        exact lt_of_mul_lt_mul_left (hh.trans (by linarith [(div_lt_iff₀ hε).mp hx']))
          (norm_nonneg x)
      · subst hz
        simpa using hε
    | coe x =>
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
      filter_upwards [Metric.ball_mem_nhds x (div_pos hε hB)] with y hy
      rintro ⟨_, f, hf, rfl⟩
      change dist (f x) (f y) < ε
      have hLip : LipschitzWith ⟨B, hB.le⟩ (⇑f) := by
        apply lipschitzWith_of_nnNorm_fderiv_le f.differentiable
        intro t
        change ‖fderiv ℝ f t‖ ≤ B
        simpa only [← norm_iteratedFDeriv_one] using
          (f.norm_iteratedFDeriv_le_seminorm ℂ 1 t).trans (hderiv _ hf).le
      apply (hLip.dist_le_mul x y).trans_lt
      rw [dist_comm]
      exact (lt_div_iff₀' hB).mp hy

end RiemannMasullo
