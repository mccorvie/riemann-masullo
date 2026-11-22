module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Families closed under directional differentiation

For a finite - dimensional real domain, continuous directional derivatives in a basis give
a Fréchet derivative. Iteration gives smoothness and identifies higher derivatives for a
family closed under differentiation along each line.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace RiemannMasullo

/-- Assemble the continuous directional derivatives one coordinate at a time. The derivative
field is indexed by the image point, so the induction also applies to translated slices. -/
private theorem hasFDerivAt_coordinates_of_hasDerivAt_lines {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : E → Y) (d : E → E → Y) (hd : ∀ v, Continuous (d v))
    (h : ∀ v x, HasDerivAt (fun t : ℝ ↦ f (x + t • v)) (d v x) 0) (n : ℕ)
    (L : (Fin n → ℝ) →L[ℝ] E) :
    ∃ A : E → (Fin n → ℝ) →L[ℝ] Y, Continuous A ∧ ∀ x t,
      HasFDerivAt (fun z ↦ f (x + L z)) (A (x + L t)) t := by
  induction n with
  | zero =>
    refine ⟨fun _ ↦ 0, continuous_const, fun x t ↦ ?_⟩
    have he : (fun z ↦ f (x + L z)) = fun _ ↦ f x := funext fun z ↦ by
      simp only [Subsingleton.elim z 0, map_zero, add_zero]
    rw [he]
    exact hasFDerivAt_const _ _
  | succ n ih =>
    let e := Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)
    let v := L (e (1, 0))
    let S := L.comp (e.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)))
    have he (r : ℝ) (z : Fin n → ℝ) : L (e (r, z)) = r • v + S z := by
      change _ = r • L (e (1, 0)) + L (e (0, z))
      rw [← map_smul, ← map_smul, ← map_add, ← map_add]
      congr 2
      simp
    obtain ⟨A, hA, hder⟩ := ih S
    let P (x : E) : ℝ →L[ℝ] Y := ContinuousLinearMap.toSpanSingleton ℝ (d v x)
    let B (x : E) := ((P x).coprod (A x)).comp e.symm.toContinuousLinearMap
    have hP : Continuous P := by
      change Continuous (fun x ↦ (ContinuousLinearMap.toSpanSingletonLIE ℝ Y) (d v x))
      exact (ContinuousLinearMap.toSpanSingletonLIE ℝ Y).continuous.comp (hd v)
    refine ⟨B, ?_, fun x t ↦ ?_⟩
    · dsimp only [B]
      fun_prop
    · let F (r : ℝ) (z : Fin n → ℝ) := f (x + r • v + S z)
      let b (u : ℝ × (Fin n → ℝ)) := x + u.1 • v + S u.2
      have hb : Continuous b := by dsimp [b]; fun_prop
      have h₁ (u : ℝ × (Fin n → ℝ)) : HasFDerivAt (F · u.2) (P (b u)) u.1 := by
        have hh : HasDerivAt (fun t : ℝ ↦ f (b u + t • v)) (d v (b u)) (u.1 - u.1) := by
          simpa only [sub_self] using h v (b u)
        have heq (s : ℝ) : b u + (s - u.1) • v = x + s • v + S u.2 := by
          dsimp [b]; rw [sub_smul]; abel
        have hf := (hh.comp_sub_const u.1 u.1).hasFDerivAt
        simpa only [Function.comp_def, heq] using hf
      have h₂ (u : ℝ × (Fin n → ℝ)) : HasFDerivAt (F u.1) (A (b u)) u.2 := hder _ _
      have hbi := hasStrictFDerivAt_uncurry_coprod (u := e.symm t) (f := F)
        (f₁ := fun r z ↦ P (b (r, z))) (f₂ := fun r z ↦ A (b (r, z)))
        (Eventually.of_forall h₁) (Eventually.of_forall h₂) (hP.comp hb).continuousAt (hA.comp hb).continuousAt
      have hcomp := hbi.hasFDerivAt.comp t e.symm.hasFDerivAt
      have heq (z) : b (e.symm z) = x + L z := by
        simpa only [b, ← add_assoc, e.apply_symm_apply] using congrArg (x + ·) (he (e.symm z).1 (e.symm z).2).symm
      have hf : HasFDerivAt (fun z ↦ f (b (e.symm z))) (B (b (e.symm t))) t := hcomp
      simpa only [heq] using hf

/-- Suppose a continuous family is closed under differentiation along straight lines in a
finite - dimensional real space. Every member is smooth, and each iterated derivative in a
fixed tuple of directions belongs to the family. The resulting index works for all parameters
`b`, which need no topology. -/
theorem contDiff_family_of_hasDerivAt_lines {E Y I B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ E] (f : I → B → E → Y) (D : E → I → I)
    (hc : ∀ i b, Continuous (f i b))
    (h : ∀ i b x v, HasDerivAt (fun t : ℝ ↦ f i b (x + t • v)) (f (D v i) b x) 0) :
    (∀ i b, ContDiff ℝ ∞ (f i b)) ∧
    ∀ (n : ℕ) (w : Fin n → E) i, ∃ j, ∀ b x, iteratedFDeriv ℝ n (f i b) x w = f j b x := by
  have hd (i b) : Differentiable ℝ (f i b) := by
    let L := (Module.finBasis ℝ E).equivFunL.symm
    obtain ⟨A, _, hA⟩ := hasFDerivAt_coordinates_of_hasDerivAt_lines (f i b) (fun v ↦ f (D v i) b)
      (fun v ↦ hc _ _) (fun v x ↦ h i b x v) _ L.toContinuousLinearMap
    intro x
    have hh := (hA 0 (L.symm x)).differentiableAt.comp x L.symm.differentiableAt
    simpa [Function.comp_def] using hh
  have hv (i b x v) : fderiv ℝ (f i b) x v = f (D v i) b x := by
    have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
      have hh := ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
      simpa only [one_smul] using hh
    have hh := (hd i b x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    exact hh.unique (h i b x v)
  have hs (n : ℕ) : ∀ i b, ContDiff ℝ n (f i b) := by
    induction n with
    | zero => exact fun i b ↦ contDiff_zero.mpr (hc i b)
    | succ n ih =>
      intro i b
      rw [Nat.cast_succ]
      apply contDiff_succ_iff_fderiv_apply.mpr
      exact ⟨hd i b, by simp, fun v ↦ by simpa only [hv] using ih (D v i) b⟩
  have hs' : ∀ i b, ContDiff ℝ ∞ (f i b) := fun i b ↦ contDiff_infty.mpr fun n ↦ hs n i b
  refine ⟨hs', fun n ↦ ?_⟩
  induction n with
  | zero => exact fun w i ↦ ⟨i, fun b x ↦ iteratedFDeriv_zero_apply _⟩
  | succ n ih =>
    intro w i
    obtain ⟨j, hj⟩ := ih (Fin.tail w) i
    refine ⟨D (w 0) j, fun b x ↦ ?_⟩
    have ha := ((hs' i b).iteratedFDeriv_right (i := n) (m := 1) (by simp)).differentiable (by simp) x
    rw [ha.iteratedFDeriv_succ_apply_left', show (fun y ↦ iteratedFDeriv ℝ n (f i b) y (Fin.tail w)) = f j b from funext (hj b)]
    exact hv _ _ _ _

end RiemannMasullo
