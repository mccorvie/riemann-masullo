module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.LocallyConvex.Montel
import Mathlib.Tactic

/-! # Continuous changes of variables in Schwartz space -/

public section

open Bornology Filter Function Set Topology
namespace RiemannMasullo

/-- An orbit in a Montel space is continuous when it is locally bounded and
all its point evaluations are continuous and separate points. -/
private theorem continuous_of_bounded_evaluations {G E A : Type*} [TopologicalSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] [MontelSpace ℂ E] (f : G → E)
    (hb : ∀ g, ∃ S ∈ 𝓝 g, IsVonNBounded ℂ (f '' S)) (ev : A → E → ℂ)
    (hc : ∀ a, Continuous (ev a)) (hi : Injective fun x a ↦ ev a x)
    (hf : ∀ a, Continuous fun g ↦ ev a (f g)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨S, hS, hs⟩ := hb g
  have hK := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure hs.closure
  apply hK.tendsto_nhds_of_unique_mapClusterPt (Filter.mem_of_superset hS fun p hp ↦ subset_closure (mem_image_of_mem f hp))
  intro x _ hx
  apply hi
  funext a
  have hh := hx.continuousAt_comp (hc a).continuousAt
  exact eq_of_nhds_neBot (hh.clusterPt.mono (hf a).continuousAt)

/-- Pullback by a linear change of variables bounds every Schwartz seminorm explicitly. -/
theorem seminorm_comp_changeOfVariables {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : SchwartzMap V ℂ) (A : V ≃L[ℝ] V) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f) ≤
      ‖A.symm.toContinuousLinearMap‖ ^ k * ‖A.toContinuousLinearMap‖ ^ n * SchwartzMap.seminorm ℂ k n f := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  have hx : ‖x‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, A.symm_apply_apply] using A.symm.toContinuousLinearMap.le_opNorm (A x)
  have hd : ‖iteratedFDeriv ℝ n (f ∘ A.toContinuousLinearMap) x‖ ≤
      ‖iteratedFDeriv ℝ n f (A x)‖ * ‖A.toContinuousLinearMap‖ ^ n := by
    rw [A.toContinuousLinearMap.iteratedFDeriv_comp_right (f.smooth n) x (by simp)]
    simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n f (A x)) (fun _ ↦ A.toContinuousLinearMap)
  calc
    _ ≤ (‖A.symm.toContinuousLinearMap‖ * ‖A x‖) ^ k *
        (‖iteratedFDeriv ℝ n f (A x)‖ * ‖A.toContinuousLinearMap‖ ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _) hd (norm_nonneg _) (by positivity)
    _ = _ * (‖A x‖ ^ k * ‖iteratedFDeriv ℝ n f (A x)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (f.le_seminorm ℂ k n (A x)) (by positivity)

/-- Pullback of a fixed Schwartz function varies continuously when the linear maps
and their inverses vary continuously in operator norm. -/
theorem continuous_schwartz_comp_family {G V : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MontelSpace ℂ (SchwartzMap V ℂ)]
    (A : G → V ≃L[ℝ] V) (ha : Continuous fun g ↦ (A g).toContinuousLinearMap)
    (hb : Continuous fun g ↦ (A g).symm.toContinuousLinearMap) (f : SchwartzMap V ℂ) :
    Continuous fun g ↦ SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (A g) f := by
  apply continuous_of_bounded_evaluations _ _ (fun x h ↦ h x) _ _ _
  · intro g
    obtain ⟨K,hK,hKg⟩ := exists_compact_mem_nhds g
    obtain ⟨a, ha'⟩ := hK.exists_bound_of_continuousOn ha.continuousOn
    obtain ⟨b, hb'⟩ := hK.exists_bound_of_continuousOn hb.continuousOn
    refine ⟨K, hKg, (schwartz_withSeminorms ℂ V ℂ).image_isVonNBounded_iff_seminorm_bounded _ |>.mpr ?_⟩
    rintro ⟨k,n⟩
    have ha₀ : 0 ≤ a := (norm_nonneg _).trans (ha' g (mem_of_mem_nhds hKg))
    have hb₀ : 0 ≤ b := (norm_nonneg _).trans (hb' g (mem_of_mem_nhds hKg))
    refine ⟨b ^ k * a ^ n * SchwartzMap.seminorm ℂ k n f + 1, by positivity, fun t ht ↦ ?_⟩
    apply lt_of_le_of_lt (seminorm_comp_changeOfVariables f (A t) k n)
    refine lt_of_le_of_lt ?_ (lt_add_one _)
    gcongr <;> first | exact ha' t ht | exact hb' t ht
  · intro x
    exact ((BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)).continuous
  · intro f g h
    exact SchwartzMap.ext (congrFun h)
  · intro x
    exact f.continuous.comp (ha.clm_apply continuous_const)

end RiemannMasullo
