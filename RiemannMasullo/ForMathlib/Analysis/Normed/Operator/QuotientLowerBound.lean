module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Basic

/-! # Quantitative lower bounds after quotienting by an image

For a bounded linear map `B`, the map from `E / N` to `F / B(N)` retains
every nonnegative lower norm bound for `B`. No completeness or closedness is
needed for the seminorm estimate. This supplies the analytic division estimate
in the two-prime compatibility calculation of issue #7351 without importing
the unmerged rational-packet developments.
-/

public noncomputable section

namespace RiemannMasullo

open Metric

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem quotient_norm_eq_infDist (N : Submodule 𝕜 E) (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ N)‖ = infDist x (N : Set E) :=
  QuotientAddGroup.norm_mk (S := N.toAddSubgroup) x

/-- A lower norm bound persists for distances to any submodule and its image.
The source submodule and its image need not be closed. -/
theorem le_infDist_map_of_lowerBound (B : E →L[𝕜] F) (N : Submodule 𝕜 E)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ x, c * ‖x‖ ≤ ‖B x‖) (x : E) :
    c * infDist x (N : Set E) ≤ infDist (B x) (N.map B.toLinearMap : Set F) := by
  apply (le_infDist ⟨0, (N.map B.toLinearMap).zero_mem⟩).mpr
  intro y hy
  obtain ⟨n, hn, rfl⟩ := hy
  calc
    c * infDist x (N : Set E) ≤ c * dist x n :=
      mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem hn) hc
    _ ≤ dist (B x) (B n) := by
      simpa only [dist_eq_norm, map_sub] using hB (x - n)

/-- The quotient seminorm of a mapped vector is bounded above by the operator
norm times its original quotient seminorm. -/
theorem infDist_map_le_opNorm (B : E →L[𝕜] F) (N : Submodule 𝕜 E) (x : E) :
    infDist (B x) (N.map B.toLinearMap : Set F) ≤ ‖B‖ * infDist x (N : Set E) := by
  have h (n : E) (hn : n ∈ N) :
      infDist (B x) (N.map B.toLinearMap : Set F) ≤ ‖B‖ * dist x n := by
    calc
      _ ≤ dist (B x) (B n) := infDist_le_dist_of_mem (show B n ∈ N.map B.toLinearMap from ⟨n, hn, rfl⟩)
      _ ≤ ‖B‖ * dist x n := by
        simpa only [dist_eq_norm, map_sub] using B.le_opNorm (x - n)
  by_cases hzero : ‖B‖ = 0
  · simpa only [hzero, zero_mul] using h 0 N.zero_mem
  · have hpos : 0 < ‖B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    rw [mul_comm ‖B‖]
    apply (div_le_iff₀ hpos).mp
    apply (le_infDist ⟨0, N.zero_mem⟩).mpr
    intro n hn
    exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm ‖B‖] using h n hn)

/-- Quantitative division modulo a submodule: the original quotient seminorm
costs at most the image quotient seminorm divided by the lower bound. -/
theorem infDist_le_map_div_lowerBound (B : E →L[𝕜] F) (N : Submodule 𝕜 E)
    {c : ℝ} (hc : 0 < c) (hB : ∀ x, c * ‖x‖ ≤ ‖B x‖) (x : E) :
    infDist x (N : Set E) ≤ infDist (B x) (N.map B.toLinearMap : Set F) / c := by
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm c] using le_infDist_map_of_lowerBound B N hc.le hB x

/-- The map to the quotient by the image retains the original lower bound,
in the actual quotient seminorms. In particular the estimate does not require
an invariant submodule or any second commuting operator. -/
theorem quotient_map_lowerBound (B : E →L[𝕜] F) (N : Submodule 𝕜 E)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ x, c * ‖x‖ ≤ ‖B x‖) (u : E ⧸ N) :
    c * ‖u‖ ≤ ‖N.mapQ (N.map B.toLinearMap) B.toLinearMap
      (fun x hx ↦ ⟨x, hx, rfl⟩) u‖ := by
  induction u using Submodule.Quotient.induction_on with
  | _ x =>
    change c * ‖(Submodule.Quotient.mk x : E ⧸ N)‖ ≤ ‖(Submodule.Quotient.mk (B x) : F ⧸ N.map B.toLinearMap)‖
    simpa only [quotient_norm_eq_infDist] using le_infDist_map_of_lowerBound B N hc hB x

/-- The same quotient map has upper bound `‖B‖` in the quotient seminorms. -/
theorem quotient_map_norm_le (B : E →L[𝕜] F) (N : Submodule 𝕜 E) (u : E ⧸ N) :
    ‖N.mapQ (N.map B.toLinearMap) B.toLinearMap
      (fun x hx ↦ ⟨x, hx, rfl⟩) u‖ ≤ ‖B‖ * ‖u‖ := by
  induction u using Submodule.Quotient.induction_on with
  | _ x =>
    change ‖(Submodule.Quotient.mk (B x) : F ⧸ N.map B.toLinearMap)‖ ≤ ‖B‖ * ‖(Submodule.Quotient.mk x : E ⧸ N)‖
    simpa only [quotient_norm_eq_infDist] using infDist_map_le_opNorm B N x

end RiemannMasullo
