module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Bounded pullbacks on Schwartz space -/

noncomputable section

open Bornology Set

namespace RiemannMasullo

/-- On classical Schwartz space a family of linear changes of variables with
bounded norms and inverse norms has bounded orbits in every Schwartz seminorm. -/
public theorem schwartz_pullback_bounded {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : I → V ≃L[ℝ] V) (C : ℝ) (hC : 0 ≤ C) (hL : ∀ i, ‖(L i : V →L[ℝ] V)‖ ≤ C)
    (hI : ∀ i, ‖((L i).symm : V →L[ℝ] V)‖ ≤ C) (f : SchwartzMap V ℂ) :
    IsVonNBounded ℂ (range fun i ↦ SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (L i) f) := by
  apply (schwartz_withSeminorms ℂ V ℂ).isVonNBounded_iff_seminorm_bddAbove.mpr
  rintro ⟨k,n⟩
  refine ⟨C ^ k * C ^ n * SchwartzMap.seminorm ℂ k n f, ?_⟩
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  let T : V →L[ℝ] V := L i
  have h1 : ‖x‖ ≤ C * ‖T x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, T] using
      (((L i).symm : V →L[ℝ] V).le_opNorm (T x)).trans
        (mul_le_mul_of_nonneg_right (hI i) (norm_nonneg _))
  have h2 : ‖iteratedFDeriv ℝ n (f ∘ T) x‖ ≤ ‖iteratedFDeriv ℝ n f (T x)‖ * C ^ n := by
    rw [T.iteratedFDeriv_comp_right (f.smooth n) x (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact hL i
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f ∘ T) x‖ ≤ _
  calc
    _ ≤ (C * ‖T x‖) ^ k * (‖iteratedFDeriv ℝ n f (T x)‖ * C ^ n) := by gcongr
    _ = (C ^ k * C ^ n) * (‖T x‖ ^ k * ‖iteratedFDeriv ℝ n f (T x)‖) := by ring
    _ ≤ _ := by gcongr; exact SchwartzMap.le_seminorm ℂ k n f (T x)

/-- A compact family of units acts on classical Schwartz space with bounded orbits. -/
public theorem schwartz_unit_pullbacks {V I : Type*} [NormedCommRing V] [NormedAlgebra ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace I] (u : I → Vˣ) (hu : Continuous u)
    (K : Set I) (hK : IsCompact K) :
    ∃ P : I → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ,
      (∀ i f x, P i f x = f ((u i).val * x)) ∧ ∀ f, IsVonNBounded ℂ ((fun i ↦ P i f) '' K) := by
  let L (i : I) := (Units.mulLeftLinearEquiv ℝ V (u i)).toContinuousLinearEquiv
  refine ⟨fun i ↦ SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (L i), fun _ _ _ ↦ rfl, fun f ↦ ?_⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (Units.continuous_val.comp hu).continuousOn
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (Units.continuous_val.comp hu.inv).continuousOn
  let C := max (max M N) 0
  have hC : 0 ≤ C := le_max_right _ _
  have hnorm (i : K) : ‖(L i.val : V →L[ℝ] V)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      ((hM i.val i.property).trans ((le_max_left M N).trans (le_max_left _ _))) (norm_nonneg x))
  have hinv (i : K) : ‖((L i.val).symm : V →L[ℝ] V)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      ((hN i.val i.property).trans ((le_max_right M N).trans (le_max_left _ _))) (norm_nonneg x))
  apply IsVonNBounded.subset _ (schwartz_pullback_bounded (fun i : K ↦ L i) C hC hnorm hinv f)
  rintro y ⟨i, hi, hy⟩
  exact ⟨⟨i,hi⟩,hy⟩


end RiemannMasullo
