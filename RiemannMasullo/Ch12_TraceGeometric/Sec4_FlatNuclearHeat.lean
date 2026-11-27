module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatLogHeat

/-!
# Fixed nuclear operators under two-sided logarithmic heat

The actual Gaussian heat on positive-ray L² preserves nuclearity and contracts the trace norm. On rank-one inputs the trace evaluates a single heat at twice the variance.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "H₊" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- The actual two-sided logarithmic heat on nuclear operators on the positive ray. -/
def logHeatSandwich (τ : ℝ≥0) : nuclearEndomorphisms H₊ →ₗ[ℂ] nuclearEndomorphisms H₊ where
  toFun A := ⟨(logHeat τ).comp (A.val.comp (logHeat τ)),
    mul_mem_nuclearEndomorphisms_left (logHeat τ)
      ⟨_, mul_mem_nuclearEndomorphisms_right (logHeat τ) A⟩⟩
  map_add' A B := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    exact (logHeat τ).map_add (A.val (logHeat τ x)) (B.val (logHeat τ x))
  map_smul' c A := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    exact (logHeat τ).map_smul c (A.val (logHeat τ x))

/-- The underlying bounded operator is the indicated genuine composition. -/
theorem logHeatSandwich_val (τ : ℝ≥0) (A : nuclearEndomorphisms H₊) :
    (logHeatSandwich τ A).val = (logHeat τ).comp (A.val.comp (logHeat τ)) := rfl

/-- The heat sandwich is a contraction for the nuclear trace norm. -/
theorem traceNorm_logHeatSandwich_le (τ : ℝ≥0) (A : nuclearEndomorphisms H₊) :
    traceNorm (logHeatSandwich τ A) ≤ traceNorm A := by
  let B : nuclearEndomorphisms H₊ := ⟨A.val * logHeat τ, mul_mem_nuclearEndomorphisms_right _ A⟩
  have hn (T : nuclearEndomorphisms H₊) : 0 ≤ traceNorm T :=
    (norm_nonneg _).trans (norm_hilbertTrace_le T)
  calc
    traceNorm (logHeatSandwich τ A) ≤ ‖logHeat τ‖ * traceNorm B :=
      traceNorm_mul_left_le (logHeat τ) B
    _ ≤ traceNorm B := mul_le_of_le_one_left (hn _) (norm_logHeat_le_one τ)
    _ ≤ ‖logHeat τ‖ * traceNorm A := traceNorm_mul_right_le (logHeat τ) A
    _ ≤ traceNorm A := mul_le_of_le_one_left (hn _) (norm_logHeat_le_one τ)

/-- On a rank-one operator, heat adds its two variances inside the trace coefficient. -/
theorem hilbertTrace_logHeatSandwich_smulRight (τ : ℝ≥0) (φ : H₊ →L[ℂ] ℂ) (v : H₊) :
    hilbertTrace (logHeatSandwich τ ⟨φ.smulRight v, smulRight_mem_nuclearEndomorphisms _ _⟩) =
      φ (logHeat (τ + τ) v) := by
  have h :
      logHeatSandwich τ ⟨φ.smulRight v, smulRight_mem_nuclearEndomorphisms _ _⟩ =
        ⟨(φ.comp (logHeat τ)).smulRight (logHeat τ v), smulRight_mem_nuclearEndomorphisms _ _⟩ := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    exact (logHeat τ).map_smul (φ (logHeat τ x)) v
  rw [h, hilbertTrace_smulRight, logHeat_add]
  rfl

end RiemannMasullo.FlatPolar
