module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Sums of evaluations on a unit cube -/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace RiemannMasullo

/-- The fundamental theorem of calculus bounds a sum evaluated at different
times by the common initial bound and a uniform sum of derivative norms. -/
private theorem sum_norm_at_different_times {N : ℕ} (g g' : Fin N → ℝ → ℂ)
    (hd : ∀ i t, HasDerivAt (g i) (g' i t) t) (hc : ∀ i, Continuous (g' i))
    (t : Fin N → ℝ) (ht : ∀ i, t i ∈ Icc 0 1) (A B : ℝ)
    (h0 : ∑ i, ‖g i 0‖ ≤ A) (h1 : ∀ u ∈ Icc 0 1, ∑ i, ‖g' i u‖ ≤ B) :
    ∑ i, ‖g i (t i)‖ ≤ A + B := by
  have he (i) : ‖g i (t i)‖ ≤ ‖g i 0‖ + ∫ u in Ioc (0 : ℝ) 1, ‖g' i u‖ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t i)
      (fun u _ ↦ hd i u) ((hc i).intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le (ht i).1] at h
    calc
      ‖g i (t i)‖ ≤ ‖g i 0‖ + ‖g i (t i) - g i 0‖ := by simpa only [sub_add_cancel, add_comm ‖g i 0‖] using norm_add_le (g i (t i) - g i 0) (g i 0)
      _ ≤ _ := by
        rw [← h]
        apply add_le_add le_rfl
        refine (norm_integral_le_integral_norm _).trans ?_
        exact setIntegral_mono_set ((hc i).norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          (.of_forall fun _ ↦ norm_nonneg _) (Filter.Eventually.of_forall (fun _ hu ↦ ⟨hu.1, hu.2.trans (ht i).2⟩))
  refine (Finset.sum_le_sum fun i _ ↦ he i).trans ?_
  rw [Finset.sum_add_distrib, ← integral_finsetSum _ fun i _ ↦ (hc i).norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self]
  apply add_le_add h0
  have h := setIntegral_mono_on (μ := volume) (s := Ioc (0:ℝ) 1)
    ((continuous_finsetSum _ (fun i _ ↦ (hc i).norm)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
    (fun x hx ↦ h1 x ⟨hx.1.le,hx.2⟩)
  simpa using h

/-- Mixed directional derivatives control the sum of evaluations at independently
chosen points in a unit cube. One coordinate costs at most a factor of two. -/
private theorem sum_norm_cube {J : Type*} [DecidableEq J] {N : ℕ} (I : Finset J)
    (D : Fin N → List J → (J → ℝ) → ℂ)
    (hd : ∀ i l x j t, HasDerivAt (fun u ↦ D i l (Function.update x j u))
      (D i (j::l) (Function.update x j t)) t)
    (hc : ∀ i l, Continuous (D i l)) (B : ℝ)
    (hb : ∀ l : List J, l.length ≤ I.card → ∀ x : J → ℝ, (∀ j, x j ∈ Icc 0 1) → ∑ i, ‖D i l x‖ ≤ B)
    (u : Fin N → J → ℝ) (hu : ∀ i j, u i j ∈ Icc 0 1)
    (b : J → ℝ) (hagree : ∀ i j, j ∉ I → u i j = b j) :
    ∑ i, ‖D i [] (u i)‖ ≤ (2:ℝ)^I.card * B := by
  classical
  by_cases hN : IsEmpty (Fin N)
  · have he : ∑ i, ‖D i [] (fun _ ↦ 0)‖ ≤ B := hb [] (by simp) _ fun _ ↦ ⟨le_rfl,zero_le_one⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at he ⊢
    positivity
  let i₀ : Fin N := Classical.choice (not_isEmpty_iff.mp hN)
  induction I using Finset.induction_on generalizing D u b with
  | empty =>
    have h (i) : u i = b := funext fun j ↦ hagree i j (by simp)
    simpa only [h, Finset.card_empty, pow_zero, one_mul] using hb [] (by simp) b (fun j ↦ h i₀ ▸ hu i₀ j)
  | @insert j I hj ih =>
    have step (l : List J) (hl : l.length ≤ 1) (t : ℝ) (ht : t ∈ Icc 0 1) :
        ∑ i, ‖D i l (Function.update (u i) j t)‖ ≤ 2^I.card * B := by
      let D' i (k : List J) := D i (k ++ l)
      refine ih D' (fun i k ↦ hd i (k++l)) (fun i k ↦ hc i (k++l)) ?_ _ ?_ (Function.update b j t) ?_
      · intro k hk
        apply hb (k++l)
        simp only [List.length_append, Finset.card_insert_of_notMem hj]
        omega
      · intro i z
        by_cases hz : z = j
        · simpa [hz] using ht
        · simpa [Function.update_of_ne hz] using hu i z
      · intro i z hz
        by_cases h : z = j
        · simp [h]
        · simpa [Function.update_of_ne h] using hagree i z (by simpa only [Finset.mem_insert, not_or] using And.intro h hz)
    have hc' (i) : Continuous (fun t ↦ D i [j] (Function.update (u i) j t)) :=
      (hc i [j]).comp (continuous_const.update _ continuous_id)
    have h := sum_norm_at_different_times (fun i t ↦ D i [] (Function.update (u i) j t))
      (fun i t ↦ D i [j] (Function.update (u i) j t)) (fun i ↦ hd i [] (u i) j) hc'
      (fun i ↦ u i j) (fun i ↦ hu i j) _ _ (step [] (by simp) 0 ⟨le_rfl,zero_le_one⟩)
      (step [j] (by simp))
    simpa only [Function.update_eq_self, Finset.card_insert_of_notMem hj, pow_succ, mul_assoc,
      two_mul, mul_two, add_mul] using h

/-- A list records the directions used to evaluate one iterated derivative. -/
def listDerivative {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℂ) (v : List X) (x : X) : ℂ := iteratedFDeriv ℝ v.length f x v.get

private theorem listDerivative_continuous {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} (hf : ContDiff ℝ ∞ f) (v : List X) : Continuous (listDerivative f v) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin v.length ↦ X) ℂ v.get).continuous.comp
    (hf.continuous_iteratedFDeriv (by simp))

/-- On a straight line one more directional derivative is obtained by prepending
the direction of the line. -/
private theorem hasDerivAt_listDerivative {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} (hf : ContDiff ℝ ∞ f) (v : List X) {c : ℝ → X} {z : X} {t : ℝ}
    (h : HasDerivAt c z t) : HasDerivAt (fun s ↦ listDerivative f v (c s))
      (listDerivative f (z::v) (c t)) t := by
  have hdiff := ((hf.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (i := v.length) (by simp)).differentiable (by simp)).differentiableAt (x := c t)
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin v.length ↦ X) ℂ v.get
  have hh := L.hasFDerivAt.comp_hasDerivAt t (hdiff.hasFDerivAt.comp_hasDerivAt t h)
  exact hh

private theorem cube_affine_update {J X : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (A : (J → ℝ) →L[ℝ] X) (b : X)
    (u : J → ℝ) (j : J) (t : ℝ) : HasDerivAt (fun s ↦ b + A (Function.update u j s))
      (A (Pi.single j 1)) t := by
  apply HasDerivAt.const_add
  apply A.hasFDerivAt.comp_hasDerivAt
  exact hasDerivAt_update u j t

/-- Bounds on mixed derivatives at common points give a bound at separately
chosen points of an affine image of the unit cube. -/
theorem sum_norm_of_cube_bounds {J X : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {N : ℕ} (A : (J → ℝ) →L[ℝ] X) (b : X)
    (f : Fin N → X → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (v : List X) (B : ℝ)
    (h : ∀ l : List J, l.length ≤ Fintype.card J → ∀ u : J → ℝ, (∀ j, u j ∈ Icc 0 1) →
      ∑ i, ‖listDerivative (f i) ((l.map (fun j ↦ A (Pi.single j 1))) ++ v) (b + A u)‖ ≤ B)
    (u : Fin N → J → ℝ) (hu : ∀ i j, u i j ∈ Icc 0 1) :
    ∑ i, ‖listDerivative (f i) v (b + A (u i))‖ ≤ 2^Fintype.card J * B := by
  let D i (l : List J) (x : J → ℝ) := listDerivative (f i) (l.map (fun j ↦ A (Pi.single j 1)) ++ v) (b + A x)
  exact sum_norm_cube Finset.univ D (fun i l x j t ↦
    hasDerivAt_listDerivative (hf i) _ (cube_affine_update A b x j t)) (fun i l ↦
    (listDerivative_continuous (hf i) _).comp (continuous_const.add A.continuous)) B h u hu
    (fun _ ↦ 0) (by simp)

end RiemannMasullo
