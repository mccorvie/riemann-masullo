module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatNuclearHeat
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Hilbert trace of a heat sandwich as a Gaussian average of dilation traces

On positive-ray L², two-sided heat on any nuclear operator has the same trace
as averaging the original operator followed on the right by logarithmic dilation
against the centered Gaussian with twice the heat variance.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal TensorProduct Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "H₊" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "U(" t ")" => ContinuousLinearEquiv.toContinuousLinearMap
  (LinearIsometryEquiv.toContinuousLinearEquiv (logDilation t))
local notation "NucTensor(" z ")" =>
  (Subtype.mk (tensorToFiniteRank z) (tensorToFiniteRank_mem_nuclearEndomorphisms z) : nuclearEndomorphisms H₊)

/-- Precompose a nuclear operator on the ray with the actual logarithmic dilation. -/
def nuclearAfterLogDilation (t : ℝ) : nuclearEndomorphisms H₊ →ₗ[ℂ] nuclearEndomorphisms H₊ where
  toFun A := ⟨A.val.comp U(t), mul_mem_nuclearEndomorphisms_right U(t) A⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The bounded operator represented by the dilated nuclear operator. -/
theorem nuclearAfterLogDilation_val (t : ℝ) (A : nuclearEndomorphisms H₊) :
    (nuclearAfterLogDilation t A).val = A.val.comp U(t) := rfl

/-- The right dilation has operator norm at most one, so its trace coefficient is
bounded uniformly in the real logarithmic shift by the original trace norm. -/
theorem norm_hilbertTrace_nuclearAfterLogDilation_le (t : ℝ) (A : nuclearEndomorphisms H₊) :
    ‖hilbertTrace (nuclearAfterLogDilation t A)‖ ≤ traceNorm A := by
  have hU : ‖U(t)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖logDilation t x‖ ≤ 1 * ‖x‖
    rw [(logDilation t).norm_map, one_mul]
  exact (norm_hilbertTrace_le _).trans ((traceNorm_mul_right_le U(t) A).trans
    (mul_le_of_le_one_left ((norm_nonneg _).trans (norm_hilbertTrace_le A)) hU))

/-- The rank-one right dilation trace is its literal matrix coefficient. -/
theorem hilbertTrace_nuclearAfterLogDilation_smulRight (t : ℝ) (φ : H₊ →L[ℂ] ℂ) (v : H₊) :
    hilbertTrace (nuclearAfterLogDilation t
      ⟨φ.smulRight v, smulRight_mem_nuclearEndomorphisms _ _⟩) = φ (logDilation t v) := by
  have h : nuclearAfterLogDilation t ⟨φ.smulRight v, smulRight_mem_nuclearEndomorphisms _ _⟩ =
      ⟨(φ.comp U(t)).smulRight v, smulRight_mem_nuclearEndomorphisms _ _⟩ := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [h, hilbertTrace_smulRight]
  rfl

private theorem logDilationTrace_add (A B : nuclearEndomorphisms H₊) :
    hilbertTrace (A + B) = hilbertTrace A + hilbertTrace B := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H₊)
  rw [← htr, map_add, htr, htr]

private theorem logDilationTrace_sub (A B : nuclearEndomorphisms H₊) :
    hilbertTrace (A - B) = hilbertTrace A - hilbertTrace B := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H₊)
  rw [← htr, map_sub, htr, htr]

private theorem dist_hilbertTrace_nuclearAfterLogDilation_le (t : ℝ) (A B : nuclearEndomorphisms H₊) :
    dist (hilbertTrace (nuclearAfterLogDilation t A)) (hilbertTrace (nuclearAfterLogDilation t B)) ≤
      traceNorm (A - B) := by
  rw [dist_eq_norm, ← logDilationTrace_sub, ← map_sub]
  exact norm_hilbertTrace_nuclearAfterLogDilation_le t (A - B)

private theorem integrable_dilatedTrace_of_continuous (A : nuclearEndomorphisms H₊)
    (h : Continuous (fun t ↦ hilbertTrace (nuclearAfterLogDilation t A)))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t ↦ hilbertTrace (nuclearAfterLogDilation t A)) μ :=
  Integrable.of_bound h.aestronglyMeasurable (traceNorm A)
    (.of_forall fun t ↦ norm_hilbertTrace_nuclearAfterLogDilation_le t A)

private theorem logHeatSandwich_trace_tensor_integral (z : StrongDual ℂ H₊ ⊗[ℂ] H₊) :
    Continuous (fun t ↦ hilbertTrace (nuclearAfterLogDilation t NucTensor(z))) ∧
    ∀ τ : ℝ≥0, hilbertTrace (logHeatSandwich τ NucTensor(z)) =
      ∫ t, hilbertTrace (nuclearAfterLogDilation t NucTensor(z)) ∂gaussianReal 0 (τ + τ) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ v =>
    have h : NucTensor(φ ⊗ₜ[ℂ] v) =
        ⟨φ.smulRight v, smulRight_mem_nuclearEndomorphisms _ _⟩ := by
      apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      exact tensorToFiniteRank_tmul φ v x
    simp only [h, hilbertTrace_logHeatSandwich_smulRight, hilbertTrace_nuclearAfterLogDilation_smulRight]
    refine ⟨φ.continuous.comp (continuous_logDilation v), fun τ ↦ ?_⟩
    have hi : Integrable (fun t ↦ logDilation t v) (gaussianReal 0 (τ + τ)) :=
      Integrable.of_bound (continuous_logDilation v).aestronglyMeasurable ‖v‖
        (.of_forall fun t ↦ ((logDilation t).norm_map v).le)
    rw [logHeat_apply, φ.integral_comp_comm hi]
  | add z w hz hw =>
    have h : NucTensor(z + w) = NucTensor(z) + NucTensor(w) := Subtype.ext (map_add _ z w)
    rw [h]
    simp only [map_add, logDilationTrace_add]
    refine ⟨hz.1.add hw.1, fun τ ↦ ?_⟩
    rw [hz.2 τ, hw.2 τ, integral_add (integrable_dilatedTrace_of_continuous _ hz.1 _)
      (integrable_dilatedTrace_of_continuous _ hw.1 _)]

/-- For every nuclear operator the scalar trace of its right translates is continuous
on the entire real logarithmic axis. -/
theorem continuous_hilbertTrace_nuclearAfterLogDilation (A : nuclearEndomorphisms H₊) :
    Continuous (fun t ↦ hilbertTrace (nuclearAfterLogDilation t A)) := by
  refine continuous_iff_continuousAt.mpr fun s ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt A (by positivity : 0 < ε / 3)
  let F := NucTensor(z)
  change traceNorm (A - F) < ε / 3 at hz
  have hc := (logHeatSandwich_trace_tensor_integral z).1.tendsto s
  filter_upwards [Metric.tendsto_nhds.mp hc (ε / 3) (by positivity)] with t ht
  have h₁ := (dist_hilbertTrace_nuclearAfterLogDilation_le t A F).trans_lt hz
  have h₂ := (dist_hilbertTrace_nuclearAfterLogDilation_le s A F).trans_lt hz
  have h := dist_triangle4 (hilbertTrace (nuclearAfterLogDilation t A))
    (hilbertTrace (nuclearAfterLogDilation t F)) (hilbertTrace (nuclearAfterLogDilation s F))
    (hilbertTrace (nuclearAfterLogDilation s A))
  rw [dist_comm (hilbertTrace (nuclearAfterLogDilation s F)) (hilbertTrace (nuclearAfterLogDilation s A))] at h
  change dist (hilbertTrace (nuclearAfterLogDilation t F)) (hilbertTrace (nuclearAfterLogDilation s F))
    < ε / 3 at ht
  linarith

/-- The scalar dilation trace is integrable for every finite measure on the real axis. -/
theorem integrable_hilbertTrace_nuclearAfterLogDilation (A : nuclearEndomorphisms H₊)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t ↦ hilbertTrace (nuclearAfterLogDilation t A)) μ :=
  integrable_dilatedTrace_of_continuous _ (continuous_hilbertTrace_nuclearAfterLogDilation A) μ

/-- The trace of actual two-sided heat is the centered Gaussian average of the right
dilation trace. The variance adds, including the degenerate Gaussian at zero. -/
theorem hilbertTrace_logHeatSandwich_eq_integral_dilationTrace (τ : ℝ≥0) (A : nuclearEndomorphisms H₊) :
    hilbertTrace (logHeatSandwich τ A) =
      ∫ t, hilbertTrace (nuclearAfterLogDilation t A) ∂gaussianReal 0 (τ + τ) := by
  let μ := gaussianReal 0 (τ + τ)
  let f (B : nuclearEndomorphisms H₊) (t : ℝ) := hilbertTrace (nuclearAfterLogDilation t B)
  let g (B : nuclearEndomorphisms H₊) := hilbertTrace (logHeatSandwich τ B)
  change g A = ∫ t, f A t ∂μ
  by_contra hne
  have hε := dist_pos.mpr hne
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt A (half_pos hε)
  let F := NucTensor(z)
  change traceNorm (A - F) < dist (g A) (∫ t, f A t ∂μ) / 2 at hz
  have hg : dist (g A) (g F) ≤ traceNorm (A - F) := by
    change dist (hilbertTrace (logHeatSandwich τ A)) (hilbertTrace (logHeatSandwich τ F)) ≤ _
    rw [dist_eq_norm, ← logDilationTrace_sub, ← map_sub]
    exact (norm_hilbertTrace_le _).trans (traceNorm_logHeatSandwich_le ..)
  have hi : dist (∫ t, f A t ∂μ) (∫ t, f F t ∂μ) ≤ traceNorm (A - F) := by
    rw [dist_eq_norm, ← integral_sub (integrable_hilbertTrace_nuclearAfterLogDilation A μ)
      (integrable_hilbertTrace_nuclearAfterLogDilation F μ)]
    have hb (t : ℝ) : ‖f A t - f F t‖ ≤ traceNorm (A - F) := by
      simpa only [f, dist_eq_norm] using dist_hilbertTrace_nuclearAfterLogDilation_le t A F
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := μ) (.of_forall hb))
  have heq : g F = ∫ t, f F t ∂μ := (logHeatSandwich_trace_tensor_integral z).2 τ
  have htri := dist_triangle (g A) (g F) (∫ t, f A t ∂μ)
  rw [heq, dist_comm (∫ t, f F t ∂μ) (∫ t, f A t ∂μ)] at htri
  rw [heq] at hg
  linarith

end RiemannMasullo.FlatPolar
