module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

namespace RiemannMasullo

open Set
open scoped ComplexOrder

/-- A point outside a closed absolutely convex set containing zero is separated
by the absolute value of a continuous linear functional. -/
theorem exists_dual_norm_le_one_lt_of_notMem {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E] {K : Set E} (hK : IsClosed K)
    (habs : AbsConvex ℂ K) (hzero : 0 ∈ K) {x : E} (hx : x ∉ K) :
    ∃ f : StrongDual ℂ E, (∀ y ∈ K, ‖f y‖ ≤ 1) ∧ 1 < ‖f x‖ := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  obtain ⟨f, r, hfr, hrx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (habs.2.lift ℝ) hK hx
  have hnorm (y : E) (hy : y ∈ K) : ‖f y‖ < r := by
    obtain ⟨c, hc, heq⟩ := RCLike.exists_norm_eq_mul_self (f y)
    have h := hfr (c • y) (balanced_iff_smul_mem.mp habs.1 hc.le hy)
    rw [map_smul, smul_eq_mul, ← heq, RCLike.ofReal_re] at h
    exact h
  have hr : 0 < r := (norm_nonneg _).trans_lt (hnorm 0 hzero)
  refine ⟨(r : ℂ)⁻¹ • f, fun y hy ↦ ?_, ?_⟩
  · change ‖(r : ℂ)⁻¹ * f y‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_of_nonneg hr.le, ← div_eq_inv_mul, div_le_iff₀ hr, one_mul]
    exact (hnorm y hy).le
  · change 1 < ‖(r : ℂ)⁻¹ * f x‖
    rw [norm_mul, norm_inv, Complex.norm_of_nonneg hr.le, ← div_eq_inv_mul, lt_div_iff₀ hr, one_mul]
    exact hrx.trans_le (Complex.re_le_norm _)

/-- Any continuous seminorm on a polynormable space is attained at a given vector
by the absolute value of a continuous linear functional dominated by that seminorm. -/
theorem exists_dual_norm_eq_seminorm {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [PolynormableSpace 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : Continuous p) (z : E) :
    ∃ φ : StrongDual 𝕜 E, (∀ y, ‖φ y‖ ≤ p y) ∧ ‖φ z‖ = p z := by
  by_cases hz : z = 0
  · exact ⟨0, fun _ ↦ by simp, by simp [hz]⟩
  let e := LinearEquiv.toSpanNonzeroSingleton 𝕜 E z hz
  let g := (p z : 𝕜) • e.symm.toLinearMap
  have hb (u : Submodule.span 𝕜 {z}) : ‖g u‖ ≤ p u := by
    obtain ⟨a, rfl⟩ := e.surjective u
    change ‖(p z : 𝕜) * e.symm (e a)‖ ≤ p (a • z)
    rw [e.symm_apply_apply, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p z),
      map_smul_eq_mul, mul_comm]
  obtain ⟨φ, hφ, hbound⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm _ g hp hb
  refine ⟨φ, hbound, ?_⟩
  have h := hφ (e 1)
  change φ ((1 : 𝕜) • z) = (p z : 𝕜) * e.symm (e 1) at h
  simp only [one_smul, e.symm_apply_apply, mul_one] at h
  rw [h, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p z)]

end RiemannMasullo
