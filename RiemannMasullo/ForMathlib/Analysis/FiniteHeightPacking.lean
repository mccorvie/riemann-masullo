module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

public section

namespace Finset

/-- In a unit interval one can avoid every height in a finite family by half a grid spacing.
The chosen point is strictly inside the interval, even when the family is empty. -/
theorem exists_mem_Ioo_dist_ge_half_mesh {α : Type*} (S : Finset α) (height : α → ℝ) (j : ℝ) :
    ∃ t ∈ Set.Ioo j (j + 1), ∀ a ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |t - height a| := by
  classical
  let D : ℝ := (S.card : ℝ) + 1
  let p (i : Fin (S.card + 1)) : ℝ := j + ((i.val : ℝ) + 1 / 2) / D
  have hD : 0 < D := by dsimp [D]; positivity
  have hinside (i : Fin (S.card + 1)) : p i ∈ Set.Ioo j (j + 1) := by
    have hi : (i.val : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    constructor
    · exact lt_add_of_pos_right _ (div_pos (by positivity) hD)
    · dsimp [p]
      apply add_lt_add_right
      apply (div_lt_iff₀ hD).2
      dsimp [D]
      linarith
  by_cases h : ∃ i : Fin (S.card + 1), ∀ a ∈ S, 1 / (2 * D) ≤ |p i - height a|
  · obtain ⟨i, hi⟩ := h
    exact ⟨p i, hinside i, hi⟩
  exfalso
  push Not at h
  choose f hf hdist using h
  let g (i : Fin (S.card + 1)) : S := ⟨f i, hf i⟩
  obtain ⟨i, k, hne, hsame⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have heq : f i = f k := congrArg Subtype.val hsame
  have impossible (u v : Fin (S.card + 1)) (huv : u < v) (hfv : f u = f v) : False := by
    have hstep : (u.val : ℝ) + 1 ≤ (v.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt huv : u.val + 1 ≤ v.val)
    have hgap : p u + 1 / D ≤ p v := by
      dsimp [p]
      rw [add_assoc, ← add_div]
      apply add_le_add_right
      apply (div_le_div_iff_of_pos_right hD).2
      linarith
    have hlo := (abs_lt.mp (hdist u)).1
    have hhi := (abs_lt.mp (hdist v)).2
    rw [hfv] at hlo
    have htwice : 1 / (2 * D) + 1 / (2 * D) = 1 / D := by field_simp; norm_num
    linarith
  exact (lt_or_gt_of_ne hne).elim (fun hik ↦ impossible i k hik heq)
    (fun hki ↦ impossible k i hki heq.symm)

end Finset
