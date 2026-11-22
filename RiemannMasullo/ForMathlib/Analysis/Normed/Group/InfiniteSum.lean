module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Vanishing sums over group cosets and intersections of predicates -/

public section
open Filter Function Set Topology
namespace RiemannMasullo

/-- An absolutely convergent sum over a group vanishes if every coset sum vanishes. -/
theorem tsum_zero_of_cosets {E G H : Type*} [NormedAddCommGroup E] [CompleteSpace E] [CommGroup G] [Group H]
    (d : H →* G) (hd : Injective d) {a : G → E} (ha : Summable a)
    (hc : ∀ g, ∑' h, a (g * d h) = 0) : ∑' g, a g = 0 := by
  let π : G →* G ⧸ d.range := QuotientGroup.mk' _
  rw [← (ha.hasSum.tsum_fiberwise π).tsum_eq]
  refine (tsum_congr (g := fun _ ↦ (0 : E)) ?_).trans (by simp)
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    let e (h : H) : π ⁻¹' {π g} := ⟨g * d h, by
      change π (g * d h) = π g
      rw [map_mul, show π (d h) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨h, rfl⟩, mul_one]⟩
    have he : Bijective e := by
      refine ⟨fun x y h ↦ hd (mul_left_cancel (congrArg Subtype.val h)), ?_⟩
      rintro ⟨x, hx⟩
      have hx' : QuotientGroup.mk g = (QuotientGroup.mk x : G ⧸ d.range) := (show π x = π g from hx).symm
      obtain ⟨y, hy⟩ := QuotientGroup.eq.mp hx'
      exact ⟨y, Subtype.ext (by change g * d y = x; rw [hy, mul_inv_cancel_left])⟩
    exact ((Equiv.ofBijective e he).tsum_eq (fun x ↦ a x.val)).symm.trans (hc g)

/-- Finite inclusion–exclusion works simultaneously for a family of absolutely
convergent sums. If the sums on all intersections belong to an additive subgroup
of the function space, so do the sums avoiding a finite list of predicates. -/
theorem tsum_avoiding_finset_mem {ι α X E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (L : AddSubgroup (X → E)) (a : X → α → E) (ha : ∀ x, Summable (fun t ↦ ‖a x t‖))
    (P : ι → α → Prop) [∀ i t, Decidable (P i t)]
    (h : ∀ B : Finset ι, open Classical in
      (fun x ↦ ∑' t, if ∀ i ∈ B, P i t then a x t else 0) ∈ L) (C : Finset ι) :
    open Classical in (fun x ↦ ∑' t, if ∀ i ∈ C, ¬ P i t then a x t else 0) ∈ L := by
  classical
  let term (C B : Finset ι) (x : X) (t : α) :=
    if (∀ i ∈ B, P i t) ∧ (∀ i ∈ C, ¬ P i t) then a x t else 0
  have hsum C B x : Summable (term C B x) := by
    apply (ha x).of_norm_bounded
    intro t
    change ‖ite _ _ _‖ ≤ _
    split_ifs <;> simp
  have hm (C B : Finset ι) : (fun x ↦ ∑' t, term C B x t) ∈ L := by
    induction C using Finset.induction_on generalizing B with
    | empty => simpa [term] using h B
    | insert i C _ ih =>
      have hd (x t) : term (insert i C) B x t = term C B x t - term C (insert i B) x t := by
        by_cases hp : P i t <;> simp [term, hp]
      have heq : (fun x ↦ ∑' t, term (insert i C) B x t) =
          (fun x ↦ ∑' t, term C B x t) - fun x ↦ ∑' t, term C (insert i B) x t :=
        funext fun x ↦ (tsum_congr (hd x)).trans ((hsum C B x).tsum_sub (hsum C (insert i B) x))
      exact heq ▸ L.sub_mem (ih B) (ih (insert i B))
  simpa [term] using hm C ∅

/-- If an absolutely summable family sums to zero on every finite intersection of predicates,
then it also sums to zero on the set where none of the predicates hold. -/
theorem tsum_avoiding_of_tsum_intersections {ι α E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (a : α → E)
    (P : ι → α → Prop) [∀ i x, Decidable (P i x)] (ha : Summable (fun x ↦ ‖a x‖))
    (hz : ∀ B : Finset ι, open Classical in (∑' x, if ∀ v ∈ B, P v x then a x else 0) = 0) :
    open Classical in (∑' x, if ∀ v, ¬ P v x then a x else 0) = 0 := by
  classical
  let term (B C : Finset ι) (x : α) :=
    if (∀ v ∈ B, P v x) ∧ (∀ v ∈ C, ¬ P v x) then a x else 0
  have bound (B C : Finset ι) (x : α) : ‖term B C x‖ ≤ ‖a x‖ := by
    unfold term
    split_ifs <;> simp
  have hzero (C : Finset ι) : ∑' x, term ∅ C x = 0 := by
    have h := tsum_avoiding_finset_mem (ι := ι) (⊥ : AddSubgroup (Unit → E))
      (fun _ ↦ a) (fun _ ↦ ha) P (fun B ↦ funext (fun _ ↦ hz B)) C
    simpa [term] using congrFun (show _ = (0 : Unit → E) from h) ()

  -- Finite exclusions eventually decide each term.
  have ht (x : α) : Tendsto (fun C ↦ term ∅ C x) atTop
      (𝓝 (if ∀ v, ¬ P v x then a x else 0)) := by
    by_cases h : ∀ v, ¬ P v x
    · simp [term, h]
    · obtain ⟨v, hv⟩ := not_forall.mp h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({v} : Finset ι)] with C hC
      have hc : ¬ ∀ w ∈ C, ¬ P w x := fun hh ↦ hv (hh v (hC (Finset.mem_singleton_self v)))
      simp [term, hc, h]
  have ht' := tendsto_tsum_of_dominated_convergence ha ht
    (Eventually.of_forall (fun C x ↦ bound ∅ C x))
  simpa only [hzero] using (tendsto_nhds_unique ht' (by simpa only [hzero] using
    (tendsto_const_nhds (f := atTop (α := Finset ι)) (x := (0 : E)))))

end RiemannMasullo
