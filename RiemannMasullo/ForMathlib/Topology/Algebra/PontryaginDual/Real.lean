module

public import Mathlib.Topology.Algebra.PontryaginDual

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

namespace RiemannMasullo

open Function

/-- The real line is isomorphic to its Pontryagin dual by the pairing
`(x, y) ↦ exp(2πixy)`. -/
theorem exists_realPontryaginDualEquiv :
    ∃ e : Multiplicative ℝ ≃ₜ* PontryaginDual (Multiplicative ℝ),
      ∀ x y : ℝ, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        Circle.exp (2 * Real.pi * (x * y)) := by
  let G := Multiplicative ℝ
  let a : ℝ := 2 * Real.pi
  have ha : a ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  let pairing : G →* PontryaginDual G :=
    { toFun := fun x ↦
        { toFun := fun y ↦ Circle.exp (a * (x.toAdd * y.toAdd))
          map_one' := by change Circle.exp (a * (x.toAdd * 0)) = 1; simp
          map_mul' := fun y z ↦ by
            change Circle.exp (a * (x.toAdd * (y.toAdd + z.toAdd))) =
              Circle.exp (a * (x.toAdd * y.toAdd)) * Circle.exp (a * (x.toAdd * z.toAdd))
            rw [mul_add, mul_add, Circle.exp_add]
          continuous_toFun := Circle.exp.continuous.comp
            (continuous_const.mul (continuous_const.mul continuous_id)) }
      map_one' := PontryaginDual.ext fun y ↦ by
        change Circle.exp (a * (0 * y.toAdd)) = 1
        simp
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change Circle.exp (a * ((x.toAdd + y.toAdd) * z.toAdd)) =
          Circle.exp (a * (x.toAdd * z.toAdd)) * Circle.exp (a * (y.toAdd * z.toAdd))
        rw [add_mul, mul_add, Circle.exp_add] }
  have hcont : Continuous pairing := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
      (show G → (G →ₜ* Circle) from pairing)
    exact Circle.exp.continuous.comp (continuous_const.mul (continuous_fst.mul continuous_snd))
  have hinj : Injective pairing := by
    intro x y hxy
    have hphase : (fun t : ℝ ↦ a * (x.toAdd * t)) = fun t : ℝ ↦ a * (y.toAdd * t) :=
      Circle.isCoveringMap_exp.eq_of_comp_eq (by fun_prop) (by fun_prop)
        (funext fun t ↦ congrArg (fun χ : PontryaginDual G ↦ χ (Multiplicative.ofAdd t)) hxy)
        0 (by simp)
    change x.toAdd = y.toAdd
    exact mul_left_cancel₀ ha (by simpa only [mul_one] using congrFun hphase 1)
  have hsurj : Surjective pairing := by
    intro χ
    let c : C(ℝ, Circle) := ⟨fun t ↦ χ (Multiplicative.ofAdd t), χ.continuous⟩
    obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      c 0 0 (Circle.exp_zero.trans (map_one χ).symm)
    have hl (t : ℝ) : Circle.exp (L t) = χ (Multiplicative.ofAdd t) := congrFun hL t
    have hAgree : Circle.exp ∘ (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) =
        Circle.exp ∘ (fun p : ℝ × ℝ ↦ L p.1 + L p.2) := by
      funext p
      simp only [comp_apply, hl, Circle.exp_add, ← map_mul]
      rfl
    have hadd : (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) = fun p : ℝ × ℝ ↦ L p.1 + L p.2 :=
      Circle.isCoveringMap_exp.eq_of_comp_eq
        (L.continuous.comp (continuous_fst.add continuous_snd))
        ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
        hAgree (0, 0) (by change L (0 + 0) = L 0 + L 0; simp [hL0])
    let Ladd : ℝ →+ ℝ :=
      { toFun := L
        map_zero' := hL0
        map_add' := fun x y ↦ congrFun hadd (x, y) }
    let Llin := Ladd.toRealLinearMap L.continuous
    have hlin (t : ℝ) : L t = t * L 1 := by
      change Llin t = t * Llin 1
      simpa only [smul_eq_mul, mul_one] using Llin.map_smul t (1 : ℝ)
    refine ⟨Multiplicative.ofAdd (L 1 / a), PontryaginDual.ext fun t ↦ ?_⟩
    change Circle.exp (a * ((L 1 / a) * t.toAdd)) = χ t
    calc
      _ = Circle.exp (L t.toAdd) := by
        apply congrArg Circle.exp
        rw [hlin t.toAdd]
        calc
          _ = t.toAdd * (L 1 / a * a) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ ha]
      _ = χ t := hl t.toAdd
  let equiv := MulEquiv.ofBijective pairing ⟨hinj, hsurj⟩
  let e : G ≃ₜ* PontryaginDual G :=
    { equiv with
      continuous_toFun := hcont
      continuous_invFun := (Equiv.continuous_symm_iff equiv.toEquiv).mpr
        (pairing.isOpenMap_of_sigmaCompact hsurj hcont) }
  exact ⟨e, fun _ _ ↦ rfl⟩

end RiemannMasullo
