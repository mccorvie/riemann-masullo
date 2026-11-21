module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
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

/-- A continuous homomorphism from a simply connected, locally path-connected
topological additive group to the circle lifts to a continuous real-valued homomorphism. -/
theorem exists_addCircle_addMonoidHom_lift {A : Type*} [AddGroup A] [TopologicalSpace A]
    [ContinuousAdd A] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (a : A →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ L : A →+ ℝ, Continuous L ∧ ∀ x, (L x : AddCircle (1 : ℝ)) = a x := by
  let q : ℝ → AddCircle (1 : ℝ) := (↑)
  have hq : IsCoveringMap q := AddCircle.isCoveringMap_coe _
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    (⟨a, ha⟩ : C(A, AddCircle (1 : ℝ))) 0 0 (by simp [q])
  have hLift (t : A) : q (L t) = a t := congrFun hL t
  have hAdd (s t : A) : L (s + t) = L s + L t := by
    have hAgree : q ∘ (fun p : A × A ↦ L (p.1 + p.2)) =
        q ∘ (fun p : A × A ↦ L p.1 + L p.2) := by
      funext p
      change q (L (p.1 + p.2)) = ((L p.1 + L p.2 : ℝ) : AddCircle (1 : ℝ))
      rw [AddCircle.coe_add]
      change q (L (p.1 + p.2)) = q (L p.1) + q (L p.2)
      simp only [hLift, map_add]
    exact congrFun (hq.eq_of_comp_eq (L.continuous.comp (continuous_fst.add continuous_snd))
      ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
      hAgree (0, 0) (by simp [hL0])) (s, t)
  exact ⟨{ toFun := L, map_zero' := hL0, map_add' := hAdd }, L.continuous, hLift⟩

/-- A continuous homomorphism from a real normed vector space to the additive
circle lifts to a continuous real-linear functional. -/
theorem exists_addCircle_coe_linearMap_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ l : E →L[ℝ] ℝ, ∀ y, (l y : AddCircle (1 : ℝ)) = a y := by
  obtain ⟨L, hL, hLift⟩ := exists_addCircle_addMonoidHom_lift a ha
  exact ⟨L.toRealLinearMap hL, hLift⟩

/-- A continuous homomorphism from the real line to the additive circle lifts to
multiplication by a real scalar. -/
theorem exists_addCircle_coe_mul_eq (a : ℝ →+ AddCircle (1 : ℝ)) (ha : Continuous a) :
    ∃ c : ℝ, ∀ t : ℝ, ((t * c : ℝ) : AddCircle (1 : ℝ)) = a t := by
  obtain ⟨L, hL, hLift⟩ := exists_addCircle_addMonoidHom_lift a ha
  refine ⟨L 1, fun t ↦ ?_⟩
  have hLinear : L t = t * L 1 := by
    simpa only [smul_eq_mul, mul_one] using map_real_smul L hL t (1 : ℝ)
  exact hLinear ▸ hLift t

end RiemannMasullo
