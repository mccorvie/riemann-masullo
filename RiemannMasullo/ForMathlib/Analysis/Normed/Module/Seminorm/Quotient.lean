module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

public section

open Set
open scoped Pointwise

namespace RiemannMasullo

/-- The infimum of a seminorm over translates by a submodule is a seminorm dominated by the
original seminorm. It vanishes on the submodule and its open balls at zero are the corresponding
balls thickened by the submodule. -/
theorem exists_seminorm_thickening {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] (p : Seminorm 𝕜 E) (S : Submodule 𝕜 E) :
    ∃ q : Seminorm 𝕜 E, q ≤ p ∧ (∀ x ∈ S, q x = 0) ∧
      ∀ r, q.ball 0 r = (S : Set E) + p.ball 0 r := by
  let cost (x : E) (s : S) := p (x - s)
  have hb (x : E) : BddBelow (range (cost x)) :=
    ⟨0, forall_mem_range.mpr fun s ↦ apply_nonneg p (x - s)⟩
  let f (x : E) := ⨅ s, cost x s
  have hf (x : E) (s : S) : f x ≤ cost x s := ciInf_le (hb x) s
  have hfp (x : E) : f x ≤ p x := by simpa [cost] using hf x 0
  let q : Seminorm 𝕜 E := Seminorm.ofSMulLE f
    (le_antisymm ((hfp 0).trans_eq (map_zero p))
      (le_ciInf fun s ↦ apply_nonneg p ((0 : E) - (s : E))))
    (fun x y ↦ le_ciInf_add_ciInf fun s t ↦ (hf (x + y) (s + t)).trans (by
      change p (x + y - (↑s + ↑t)) ≤ p (x - ↑s) + p (y - ↑t)
      rw [add_sub_add_comm]
      exact map_add_le_add p _ _))
    (fun a x ↦ by
      rw [show f x = ⨅ s, cost x s from rfl, Real.mul_iInf_of_nonneg (norm_nonneg a)]
      refine le_ciInf fun s ↦ (hf (a • x) (a • s)).trans_eq ?_
      simp only [cost, Submodule.coe_smul, ← smul_sub, map_smul_eq_mul])
  refine ⟨q, Seminorm.le_def.mpr hfp, ?_, fun r ↦ ?_⟩
  · intro x hx
    apply le_antisymm _ (apply_nonneg q x)
    change f x ≤ 0
    simpa [cost] using hf x ⟨x, hx⟩
  · ext x
    rw [Seminorm.mem_ball_zero]
    constructor
    · intro hx
      obtain ⟨s, hs⟩ : ∃ s : S, p (x - s) < r := by
        by_contra! h
        exact hx.not_ge (le_ciInf h)
      exact ⟨s, s.property, x - s, p.mem_ball_zero.mpr hs, add_sub_cancel _ _⟩
    · rintro ⟨s, hs, y, hy, rfl⟩
      exact (hf (s + y) ⟨s, hs⟩).trans_lt (by
        simpa [cost] using p.mem_ball_zero.mp hy)

end RiemannMasullo
