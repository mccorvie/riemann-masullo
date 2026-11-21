module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f g l r : ℝ → E}

/-- The integral of a derivative on a finite interval is the endpoint difference plus
the sum of the left limits minus the right limits at the interior jumps. -/
private theorem intervalIntegral_deriv_eq_sub_add_sum_jumps (S : Finset ℝ)
    (hg : Integrable g)
    (hl : ∀ x ∈ S, Tendsto f (𝓝[<] x) (𝓝 (l x)))
    (hr : ∀ x ∈ S, Tendsto f (𝓝[>] x) (𝓝 (r x)))
    {a b : ℝ} {fa fb : E} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb))
    (hderiv : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = fb - fa + ∑ x ∈ S, if x ∈ Ioo a b then l x - r x else 0 := by
  classical
  induction S using Finset.induction_on generalizing a b fa fb with
  | empty =>
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab
      (fun x hx ↦ hderiv x hx (Finset.notMem_empty x)) hg.intervalIntegrable ha hb
  | @insert c S hc ih =>
    rw [Finset.sum_insert hc]
    have hlS x (hx : x ∈ S) := hl x (Finset.mem_insert_of_mem hx)
    have hrS x (hx : x ∈ S) := hr x (Finset.mem_insert_of_mem hx)
    by_cases hcI : c ∈ Ioo a b
    · rw [ite_eq_left hcI, ← intervalIntegral.integral_add_adjacent_intervals
        (f := g) (b := c) hg.intervalIntegrable hg.intervalIntegrable]
      have habS : ∀ x ∈ Ioo a b, x ∉ S → x ≠ c → HasDerivAt f (g x) x :=
        fun x hx hxS hxc ↦ hderiv x hx (by simpa [hxc] using hxS)
      rw [ih hlS hrS hcI.1 ha (hl c (Finset.mem_insert_self c S))
        (fun x hx hxS ↦ habS x ⟨hx.1, hx.2.trans hcI.2⟩ hxS hx.2.ne),
        ih hlS hrS hcI.2 (hr c (Finset.mem_insert_self c S)) hb
        (fun x hx hxS ↦ habS x ⟨hcI.1.trans hx.1, hx.2⟩ hxS hx.1.ne')]
      have hsum : (∑ x ∈ S, if x ∈ Ioo a c then l x - r x else 0) +
          (∑ x ∈ S, if x ∈ Ioo c b then l x - r x else 0) =
          ∑ x ∈ S, if x ∈ Ioo a b then l x - r x else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx hc) with hxc | hcx
        · have hiff : x ∈ Ioo a c ↔ x ∈ Ioo a b :=
            ⟨fun h ↦ ⟨h.1, hxc.trans hcI.2⟩, fun h ↦ ⟨h.1, hxc⟩⟩
          simp [hiff, hxc.not_gt]
        · have hiff : x ∈ Ioo c b ↔ x ∈ Ioo a b :=
            ⟨fun h ↦ ⟨hcI.1.trans hcx, h.2⟩, fun h ↦ ⟨hcx, h.2⟩⟩
          simp [hiff, hcx.not_gt]
      rw [← hsum]
      abel
    · rw [ite_eq_right hcI, zero_add]
      exact ih hlS hrS hab ha hb fun x hx hxS ↦
        hderiv x hx (by simpa [ne_of_mem_of_not_mem hx hcI] using hxS)

/-- If an integrable function is the derivative of a function off finitely many jump points,
its integral equals the difference of the limits at infinity plus the sum of the left limits
minus the right limits at the jumps. -/
theorem integral_deriv_eq_sub_add_sum_jumps (S : Finset ℝ) (hg : Integrable g)
    (hderiv : ∀ x ∉ S, HasDerivAt f (g x) x)
    (hl : ∀ x ∈ S, Tendsto f (𝓝[<] x) (𝓝 (l x)))
    (hr : ∀ x ∈ S, Tendsto f (𝓝[>] x) (𝓝 (r x)))
    {fa fb : E} (ha : Tendsto f atBot (𝓝 fa)) (hb : Tendsto f atTop (𝓝 fb)) :
    (∫ x, g x) = fb - fa + ∑ x ∈ S, (l x - r x) := by
  classical
  have hlim := intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop)
  refine tendsto_nhds_unique hlim (((hb.sub (ha.comp tendsto_neg_atTop_atBot)).add
    (tendsto_const_nhds (x := ∑ x ∈ S, (l x - r x)))).congr' ?_)
  have hS : ∀ᶠ t : ℝ in atTop, ∀ x ∈ S, x ∈ Ioo (-t) t := by
    apply (Filter.eventually_all_finset S).mpr
    intro x _
    filter_upwards [eventually_gt_atTop (-x), eventually_gt_atTop x] with t h₁ h₂
    exact ⟨neg_lt.mp h₁, h₂⟩
  filter_upwards [hS, eventually_gt_atTop (0 : ℝ)] with t htS ht
  have hleft := (hderiv (-t) (fun h ↦ (htS _ h).1.false)).continuousAt
  have hright := (hderiv t (fun h ↦ (htS _ h).2.false)).continuousAt
  change f t - f (-t) + _ = ∫ x in -t..t, g x
  rw [intervalIntegral_deriv_eq_sub_add_sum_jumps S hg hl hr ((neg_lt_zero.mpr ht).trans ht)
    hleft.continuousWithinAt hright.continuousWithinAt (fun x _ hx ↦ hderiv x hx)]
  congr 1
  exact Finset.sum_congr rfl fun x hx ↦ (ite_eq_left (htS x hx)).symm

end RiemannMasullo
