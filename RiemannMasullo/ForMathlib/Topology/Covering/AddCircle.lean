module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

public section

namespace RiemannMasullo

/-- A continuous homomorphism from a real normed vector space to the additive
circle lifts to a continuous real-linear functional. -/
theorem exists_addCircle_coe_linearMap_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ l : E →L[ℝ] ℝ, ∀ y, (l y : AddCircle (1 : ℝ)) = a y := by
  let p : ℝ → AddCircle (1 : ℝ) := (↑)
  have hp := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨l, ⟨hl0, hl⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    (⟨a, ha⟩ : C(E, AddCircle (1 : ℝ))) 0 0 (by simp)
  have hLiftAt (y : E) : p (l y) = a y := congrFun hl y
  have hAdd (y w : E) : l (y + w) = l y + l w := by
    have hAgree : p ∘ (fun b : E × E ↦ l (b.1 + b.2)) =
        p ∘ (fun b : E × E ↦ l b.1 + l b.2) := by
      funext b
      change p (l (b.1 + b.2)) = ((l b.1 + l b.2 : ℝ) : AddCircle (1 : ℝ))
      rw [AddCircle.coe_add]
      change p (l (b.1 + b.2)) = p (l b.1) + p (l b.2)
      simp only [hLiftAt, map_add]
    exact congrFun (hp.eq_of_comp_eq (l.continuous.comp (continuous_fst.add continuous_snd))
      ((l.continuous.comp continuous_fst).add (l.continuous.comp continuous_snd))
      hAgree (0, 0) (by simp [hl0])) (y, w)
  let addLift : E →+ ℝ := ⟨⟨l, hl0⟩, hAdd⟩
  exact ⟨addLift.toRealLinearMap l.continuous, hLiftAt⟩

/-- A continuous homomorphism from the real line to the additive circle lifts to
multiplication by a real scalar. -/
theorem exists_addCircle_coe_mul_eq (a : ℝ →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ c : ℝ, ∀ t : ℝ, ((t * c : ℝ) : AddCircle (1 : ℝ)) = a t := by
  obtain ⟨l, hl⟩ := exists_addCircle_coe_linearMap_eq a ha
  refine ⟨l 1, fun t ↦ ?_⟩
  have ht : l t = t * l 1 := by
    simpa only [smul_eq_mul, mul_one] using l.map_smul t (1 : ℝ)
  exact ht ▸ hl t

end RiemannMasullo
