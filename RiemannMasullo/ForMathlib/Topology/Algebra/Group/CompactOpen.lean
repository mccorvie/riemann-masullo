module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-! # The trivial complex character of a compact monoid -/

@[expose] public section

namespace RiemannMasullo

open Filter

/-- The trivial complex character of a compact monoid is isolated in the compact-open topology. -/
theorem isOpen_singleton_one_complex {G : Type*} [Monoid G] [TopologicalSpace G] [CompactSpace G] :
    IsOpen ({1} : Set (G →ₜ* ℂ)) := by
  let V : Set (G →ₜ* ℂ) := {c | Set.MapsTo c Set.univ (Metric.ball 1 1)}
  have hV : IsOpen V := isOpen_induced
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ Metric.isOpen_ball)
  have hVeq : V = {1} := by
    ext c
    rw [Set.mem_singleton_iff]
    refine ⟨fun hc ↦ ?_, ?_⟩
    · obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := G))
        ((c.continuous.sub continuous_const).norm.continuousOn)
      have hbound (y : G) : ‖c y - 1‖ ≤ ‖c x - 1‖ := isMaxOn_univ_iff.mp hx y
      have hclose : ‖c x - 1‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hc (Set.mem_univ x)
      have hfactor : 1 < ‖c x + 1‖ := by
        have h := norm_add_le (c x + 1) (1 - c x)
        have hsum : c x + 1 + (1 - c x) = 2 := by ring
        rw [hsum, norm_sub_rev, Complex.norm_ofNat] at h
        linarith
      -- Squaring would increase the maximum distance from one if it were positive.
      have hsq := hbound (x ^ 2)
      have hsq_factor : c x ^ 2 - 1 = (c x + 1) * (c x - 1) := by ring
      rw [map_pow, hsq_factor, norm_mul] at hsq
      have hzero : ‖c x - 1‖ = 0 := by
        nlinarith [norm_nonneg (c x - 1)]
      ext1 y
      change c y = 1
      exact sub_eq_zero.mp (norm_eq_zero.mp
        (le_antisymm ((hbound y).trans_eq hzero) (norm_nonneg _)))
    · rintro rfl y _
      simp [Metric.mem_ball]
  simpa [hVeq] using hV

end RiemannMasullo
