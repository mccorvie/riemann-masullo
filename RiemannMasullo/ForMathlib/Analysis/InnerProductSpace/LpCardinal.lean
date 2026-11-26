module

public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public noncomputable section
open scoped InnerProductSpace
namespace RiemannMasullo

variable {I T K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A cardinal minimizer in an orthogonal sum has no components on the other fibers. -/
theorem lp_cardinal_support (S : Set (I × T)) (q : T → K)
    (w : lp (fun _ : I ↦ K) 2) (ω : I)
    (hzero : ∀ i t, (i, t) ∈ S → i ≠ ω → ⟪q t, w i⟫_ℂ = 0)
    (horth : ∀ v : lp (fun _ : I ↦ K) 2,
      (∀ i t, (i, t) ∈ S → ⟪q t, v i⟫_ℂ = 0) → ⟪w, v⟫_ℂ = 0)
    (ζ : I) (hζ : ζ ≠ ω) : w ζ = 0 := by
  classical
  have he := horth (lp.single 2 ζ (w ζ)) (by
    intro i t ht
    by_cases hi : i = ζ
    · subst i
      rw [lp.single_apply_self]
      exact hzero ζ t ht hζ
    · rw [lp.single_apply_ne _ _ _ hi, inner_zero_right])
  rw [lp.inner_single_right] at he
  exact inner_self_eq_zero.mp he

/-- Orthogonality to all site-vanishing vectors restricts to the same orthogonality
on each scalar fiber. -/
theorem lp_cardinal_component_orthogonal (S : Set (I × T)) (q : T → K)
    (w : lp (fun _ : I ↦ K) 2) (ω : I)
    (horth : ∀ v : lp (fun _ : I ↦ K) 2,
      (∀ i t, (i, t) ∈ S → ⟪q t, v i⟫_ℂ = 0) → ⟪w, v⟫_ℂ = 0)
    (v : K) (hv : ∀ t, (ω, t) ∈ S → ⟪q t, v⟫_ℂ = 0) : ⟪w ω, v⟫_ℂ = 0 := by
  classical
  have he := horth (lp.single 2 ω v) (by
    intro i t ht
    by_cases hi : i = ω
    · subst i
      rw [lp.single_apply_self]
      exact hv t ht
    · rw [lp.single_apply_ne _ _ _ hi, inner_zero_right])
  simpa only [lp.inner_single_right] using he

end RiemannMasullo
