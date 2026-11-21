module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

public section

namespace RiemannMasullo

/-- A continuous homomorphism from the real line to the additive circle lifts to
multiplication by a real scalar. -/
theorem exists_addCircle_coe_mul_eq (a : ℝ →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ c : ℝ, ∀ t : ℝ, ((t * c : ℝ) : AddCircle (1 : ℝ)) = a t := by
  let q : ℝ → AddCircle (1 : ℝ) := (↑)
  have hq : IsCoveringMap q := AddCircle.isCoveringMap_coe _
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    (⟨a, ha⟩ : C(ℝ, AddCircle (1 : ℝ))) 0 0 (by simp [q])
  have hLift (t : ℝ) : q (L t) = a t := congrFun hL t
  have hAdd (s t : ℝ) : L (s + t) = L s + L t := by
    have hAgree : q ∘ (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) =
        q ∘ (fun p : ℝ × ℝ ↦ L p.1 + L p.2) := by
      funext p
      change q (L (p.1 + p.2)) = ((L p.1 + L p.2 : ℝ) : AddCircle (1 : ℝ))
      rw [AddCircle.coe_add]
      change q (L (p.1 + p.2)) = q (L p.1) + q (L p.2)
      simp only [hLift, map_add]
    exact congrFun (hq.eq_of_comp_eq (L.continuous.comp (continuous_fst.add continuous_snd))
      ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
      hAgree (0, 0) (by simp [hL0])) (s, t)
  let b : ℝ →+ ℝ := { toFun := L, map_zero' := hL0, map_add' := hAdd }
  refine ⟨L 1, fun t ↦ ?_⟩
  have hLinear : L t = t * L 1 := by
    change b t = t * b 1
    simpa only [smul_eq_mul, mul_one] using map_real_smul b L.continuous t (1 : ℝ)
  exact hLinear ▸ hLift t

end RiemannMasullo
