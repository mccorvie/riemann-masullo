module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Sampling estimates for real-line Schwartz functions -/

public section

namespace RiemannMasullo

open Set
open scoped SchwartzMap

/-- On a short interval, each vanishing jet gains a power of the mesh width. -/
private theorem norm_iteratedDeriv_le_of_zero_jets (g : 𝓢(ℝ, ℂ)) (y δ : ℝ) (hδ : 0 ≤ δ)
    (m l : ℕ) (hz : ∀ j < m, iteratedDeriv (l + j) g y = 0) (x : ℝ) (hx : x ∈ Icc y (y + δ)) :
    ‖iteratedDeriv l g x‖ ≤ SchwartzMap.seminorm ℂ 0 (l + m) g * δ ^ m := by
  induction m generalizing l x with
  | zero => simpa using g.le_seminorm' ℂ 0 l x
  | succ m ih =>
    have h (t : ℝ) : HasDerivAt (iteratedDeriv l g) (iteratedDeriv (l + 1) g t) t := by
      rw [iteratedDeriv_succ]
      exact ((g.smooth _).differentiable_iteratedDeriv' l t).hasDerivAt
    have ht (t) (ht : t ∈ Ico y (y + δ)) : ‖iteratedDeriv (l + 1) g t‖ ≤
        SchwartzMap.seminorm ℂ 0 (l + (m + 1)) g * δ ^ m := by
      have hh := ih (l + 1) (fun j hj ↦ by
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hz (j + 1) (by omega)) t ⟨ht.1, ht.2.le⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using hh
    have hh := norm_image_sub_le_of_norm_deriv_le_segment' (fun t _ ↦ (h t).hasDerivWithinAt) ht x hx
    rw [show iteratedDeriv l g y = 0 by simpa using hz 0 (Nat.zero_lt_succ _), sub_zero] at hh
    rw [pow_succ, ← mul_assoc]
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hx.2])
      (mul_nonneg (apply_nonneg _ _) (pow_nonneg hδ _)))

/-- Uniform grid observations control each low Schwartz seminorm, with an arbitrary
inverse power of the grid size paid for by two higher Schwartz seminorms. -/
theorem schwartz_grid_estimate (g : 𝓢(ℝ, ℂ)) (N k l r : ℕ) (hN : 0 < N)
    (hm : l + (r + k) ≤ N) (hz : ∀ i : Fin (2 * N ^ 2 + 1), ∀ j < N,
      iteratedDeriv j g ((i.val : ℝ) / N - N) = 0) :
    (N : ℝ) ^ r * SchwartzMap.seminorm ℂ k l g ≤
      SchwartzMap.seminorm ℂ 0 (l + (r + k)) g + SchwartzMap.seminorm ℂ (r + k) l g := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  let C := SchwartzMap.seminorm ℂ 0 (l + (r + k)) g + SchwartzMap.seminorm ℂ (r + k) l g
  rw [mul_comm, ← le_div_iff₀ (pow_pos hp r)]
  apply SchwartzMap.seminorm_le_bound' _ _ _ _ (div_nonneg (add_nonneg (apply_nonneg _ _)
    (apply_nonneg _ _)) (pow_nonneg hp.le _))
  intro x
  rw [le_div_iff₀ (pow_pos hp r)]
  by_cases hsmall : |x| ≤ N
  · let i := ⌊(x + N) * N⌋₊
    obtain ⟨hneg, hpos⟩ := abs_le.mp hsmall
    have hi : i ≤ 2 * N ^ 2 := Nat.floor_le_of_le (by push_cast; nlinarith)
    let y := (i : ℝ) / N - N
    have hx : x ∈ Icc y (y + (N : ℝ)⁻¹) := by
      have ha := Nat.floor_le (a := (x + N) * N) (mul_nonneg (by linarith) hp.le)
      have hb := Nat.lt_floor_add_one ((x + N) * N)
      dsimp only [y]
      constructor
      · rw [sub_le_iff_le_add, div_le_iff₀ hp]; exact ha
      · change x ≤ (i : ℝ) / N - N + (N : ℝ)⁻¹
        rw [show (i : ℝ) / N - N + (N : ℝ)⁻¹ = ((i : ℝ) + 1) / N - N by ring,
          le_sub_iff_add_le, le_div_iff₀ hp]; exact hb.le
    have hh := norm_iteratedDeriv_le_of_zero_jets g y _ (inv_nonneg.mpr hp.le) (r + k) l
      (fun j hj ↦ hz ⟨i, by omega⟩ _ (by omega)) x hx
    calc
      _ ≤ (N : ℝ) ^ k * (SchwartzMap.seminorm ℂ 0 (l + (r + k)) g *
            (N : ℝ)⁻¹ ^ (r + k)) * N ^ r := by gcongr
      _ = SchwartzMap.seminorm ℂ 0 (l + (r + k)) g := by rw [pow_add, inv_pow, inv_pow]; field_simp
      _ ≤ _ := le_add_of_nonneg_right (apply_nonneg _ _)
  · calc
      _ ≤ |x| ^ k * ‖iteratedDeriv l g x‖ * |x| ^ r := by gcongr; exact (not_le.mp hsmall).le
      _ = |x| ^ (r + k) * ‖iteratedDeriv l g x‖ := by rw [pow_add]; ring
      _ ≤ _ := (g.le_seminorm' ℂ (r + k) l x).trans (le_add_of_nonneg_left (apply_nonneg _ _))

end RiemannMasullo
