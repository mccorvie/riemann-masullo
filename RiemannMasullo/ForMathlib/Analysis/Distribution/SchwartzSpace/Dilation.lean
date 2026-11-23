module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Seminorms of dilated Schwartz functions

Composing a Schwartz function with multiplication by `T ≥ 1` multiplies its `(k, n)` seminorm
by at most `T ^ n`.
-/

public section

open SchwartzMap

namespace RiemannMasullo

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A Schwartz seminorm of `x ↦ f (T x)` with `T ≥ 1` is at most `T ^ n` times that of `f`. -/
theorem seminorm_comp_smul_le (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (T : ℝ) (hT : 1 ≤ T) (f : 𝓢(V, F)) (k n : ℕ) :
    SchwartzMap.seminorm 𝕜 k n
        (compCLMOfContinuousLinearEquiv 𝕜
          (ContinuousLinearEquiv.smulLeft (Units.mk0 T (by positivity)) : V ≃L[ℝ] V) f) ≤
      T ^ n * SchwartzMap.seminorm 𝕜 k n f := by
  have hT0 : 0 < T := by positivity
  let L : V →L[ℝ] V := T • ContinuousLinearMap.id ℝ V
  refine SchwartzMap.seminorm_le_bound 𝕜 k n _ (by positivity) fun x ↦ ?_
  have hfx : ∀ y, ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f y‖ ≤ SchwartzMap.seminorm 𝕜 k n f :=
    SchwartzMap.le_seminorm 𝕜 k n f
  have hcomp : iteratedFDeriv ℝ n (fun y ↦ f (T • y)) x =
      (iteratedFDeriv ℝ n f (T • x)).compContinuousLinearMap fun _ ↦ L := by
    have := L.iteratedFDeriv_comp_right (f.smooth ⊤) x (i := n) (mod_cast le_top)
    simpa [L, Function.comp_def] using this
  have hnorm : ‖iteratedFDeriv ℝ n (fun y ↦ f (T • y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (T • x)‖ * T ^ n := by
    rw [hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    gcongr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact (ContinuousLinearMap.opNorm_le_bound _ hT0.le fun y ↦ by
      simp [L, norm_smul, abs_of_pos hT0])
  have hx : ‖x‖ ≤ ‖T • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hT0.le]
    exact le_mul_of_one_le_left (norm_nonneg _) hT
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ f (T • y)) x‖ ≤ _
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ f (T • y)) x‖
      ≤ ‖T • x‖ ^ k * (‖iteratedFDeriv ℝ n f (T • x)‖ * T ^ n) := by
        gcongr
    _ = T ^ n * (‖T • x‖ ^ k * ‖iteratedFDeriv ℝ n f (T • x)‖) := by ring
    _ ≤ T ^ n * SchwartzMap.seminorm 𝕜 k n f := by
        gcongr
        exact hfx _

end RiemannMasullo
