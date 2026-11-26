module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Circle actions on quotients of forward translation semigroups

In a fixed Paley–Wiener box only the forward translations need to preserve the
box. If the period difference takes values in the next stage, forward
translations on the quotient extend to a strongly continuous circle action.
-/

open Set

namespace RiemannMasullo

variable {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

private theorem exists_addCircleAction_of_periodic_forward
    {L : ℝ} (hL : 0 < L) (R : ℝ → E →L[𝕜] E)
    (hzero : ∀ x, R 0 x = x)
    (hadd : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u → ∀ x, R (t + u) x = R t (R u x))
    (hperiod : ∀ x, R L x = R 0 x)
    (hcontinuous : ∀ x, ContinuousOn (fun t ↦ R t x) (Icc 0 L)) :
    ∃ A : AddCircle L → E →L[𝕜] E,
      (∀ x, A 0 x = x) ∧
      (∀ c d x, A (c + d) x = A c (A d x)) ∧
      (∀ t : ℝ, 0 ≤ t → A (t : AddCircle L) = R t) ∧
      ∀ x, Continuous (fun c ↦ A c x) := by
  letI : Fact (0 < L) := ⟨hL⟩
  let A := AddCircle.liftIco L 0 R
  have hmultiple (n : ℕ) (x : E) : R ((n : ℝ) * L) x = x := by
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul,
        hadd _ _ (mul_nonneg (Nat.cast_nonneg n) hL.le) hL.le, hperiod x, hzero x, ih]
  have hagree (t : ℝ) (ht : 0 ≤ t) : A (t : AddCircle L) = R t := by
    let n := ⌊t / L⌋₊
    let r := t - (n : ℝ) * L
    have hn : (n : ℝ) * L ≤ t :=
      (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg ht hL.le))
    have ht' : t < ((n : ℝ) + 1) * L :=
      (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one _)
    have hr : r ∈ Ico 0 L := ⟨sub_nonneg.mpr hn,
      sub_lt_iff_lt_add.mpr (by simpa only [add_mul, one_mul, add_comm] using ht')⟩
    have hcast : (((n : ℝ) * L : ℝ) : AddCircle L) = 0 := by
      rw [← nsmul_eq_mul, AddCircle.coe_nsmul, AddCircle.coe_period, nsmul_zero]
    have hrep : (r : AddCircle L) = (t : AddCircle L) := by
      dsimp only [r]
      rw [AddCircle.coe_sub, hcast, sub_zero]
    have hsplit : (n : ℝ) * L + r = t := by
      dsimp only [r]
      rw [add_comm, sub_add_cancel]
    have hleft : R ((n : ℝ) * L + r) = R r := by
      ext x
      exact (hadd _ _ (mul_nonneg (Nat.cast_nonneg n) hL.le) hr.1 x).trans
        (hmultiple n (R r x))
    exact (congrArg A hrep.symm).trans
      ((AddCircle.liftIco_zero_coe_apply hr).trans (hleft.symm.trans (congrArg R hsplit)))
  refine ⟨A, ?_, ?_, hagree, ?_⟩
  · intro x
    rw [← AddCircle.coe_zero (p := L), hagree 0 le_rfl, hzero]
  · intro c d x
    let t : ℝ := AddCircle.equivIco L 0 c
    let u : ℝ := AddCircle.equivIco L 0 d
    have ht : 0 ≤ t := (AddCircle.equivIco L 0 c).property.1
    have hu : 0 ≤ u := (AddCircle.equivIco L 0 d).property.1
    have htc : (t : AddCircle L) = c := AddCircle.coe_equivIco (a := 0)
    have hud : (u : AddCircle L) = d := AddCircle.coe_equivIco (a := 0)
    rw [← htc, ← hud, ← AddCircle.coe_add, hagree (t + u) (add_nonneg ht hu),
      hagree t ht, hagree u hu]
    exact hadd t u ht hu x
  · intro x
    change Continuous (AddCircle.liftIco L 0 (fun t ↦ R t x))
    exact AddCircle.liftIco_zero_continuous (hperiod x).symm (hcontinuous x)

public section

/-- A strongly continuous forward operator semigroup preserving a submodule acts on
its quotient by the additive circle if every period difference belongs to the
submodule. The circle action agrees with the original forward operators on classes. -/
theorem exists_addCircleAction_quotient {L : ℝ} (hL : 0 < L) (N : Submodule 𝕜 E)
    (R : ℝ → E →L[𝕜] E)
    (hzero : ∀ x, R 0 x = x)
    (hadd : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u → ∀ x, R (t + u) x = R t (R u x))
    (hpreserve : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ N, R t x ∈ N)
    (hperiod : ∀ x, R L x - x ∈ N)
    (hcontinuous : ∀ x, Continuous (fun t ↦ R t x)) :
    ∃ A : AddCircle L → (E ⧸ N) →L[𝕜] (E ⧸ N),
      (∀ q, A 0 q = q) ∧
      (∀ c d q, A (c + d) q = A c (A d q)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x, A (t : AddCircle L) (N.mkQL x) = N.mkQL (R t x)) ∧
      ∀ q, Continuous (fun c ↦ A c q) := by
  let B (t : ℝ) : (E ⧸ N) →L[𝕜] (E ⧸ N) :=
    N.liftQL (N.mkQL.comp (R (max t 0))) (by
      intro x hx
      change (Submodule.Quotient.mk (R (max t 0) x) : E ⧸ N) = 0
      exact (Submodule.Quotient.mk_eq_zero N).mpr (hpreserve _ (le_max_right _ _) x hx))
  have hB (t : ℝ) (ht : 0 ≤ t) (x : E) :
      B t (N.mkQL x) = N.mkQL (R t x) := by
    change N.mkQL (R (max t 0) x) = _
    rw [max_eq_left ht]
  have hBzero (q : E ⧸ N) : B 0 q = q := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    change B 0 (N.mkQL x) = N.mkQL x
    rw [hB 0 le_rfl, hzero]
  have hBadd (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (q : E ⧸ N) :
      B (t + u) q = B t (B u q) := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    change B (t + u) (N.mkQL x) = B t (B u (N.mkQL x))
    rw [hB (t + u) (add_nonneg ht hu), hB u hu, hB t ht, hadd t u ht hu]
  have hBperiod (q : E ⧸ N) : B L q = B 0 q := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    change B L (N.mkQL x) = B 0 (N.mkQL x)
    rw [hB L hL.le, hB 0 le_rfl, hzero]
    exact (Submodule.Quotient.eq N).mpr (hperiod x)
  have hBcontinuous (q : E ⧸ N) : ContinuousOn (fun t ↦ B t q) (Icc 0 L) := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    change ContinuousOn (fun t ↦ N.mkQL (R (max t 0) x)) (Icc 0 L)
    exact (N.mkQL.continuous.comp ((hcontinuous x).comp
      (continuous_id.max continuous_const))).continuousOn
  obtain ⟨A, hAzero, hAadd, hAagree, hAcontinuous⟩ :=
    exists_addCircleAction_of_periodic_forward hL B hBzero hBadd hBperiod hBcontinuous
  exact ⟨A, hAzero, hAadd, fun t ht x ↦ (congrArg (fun S ↦ S (N.mkQL x))
    (hAagree t ht)).trans (hB t ht x), hAcontinuous⟩

end

end RiemannMasullo
