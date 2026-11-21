module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Rearrangements of series indexed by the naturals -/

public section

open Filter Finset Topology

namespace RiemannMasullo

/-- Every strictly increasing sequence of finite sets that exhausts the naturals
can be realized as initial segments of a single permutation. -/
private theorem exists_perm_finset_range (s : ℕ → Finset ℕ) (hs : StrictMono s)
    (hcover : ∀ i, ∃ n, i ∈ s n) :
    ∃ σ : ℕ ≃ ℕ, ∀ n, (range (s n).card).image σ = s n := by
  let l : ℕ → List ℕ :=
    Nat.rec (s 0).toList fun n acc ↦ acc ++ (s (n + 1) \ s n).toList
  have hstep (n : ℕ) : l (n + 1) = l n ++ (s (n + 1) \ s n).toList := rfl
  have hset (n : ℕ) : (l n).toFinset = s n := by
    induction n with
    | zero => exact toList_toFinset _
    | succ n ih =>
      rw [hstep, List.toFinset_append, ih, toList_toFinset,
        union_sdiff_of_subset (hs.monotone (Nat.le_succ n))]
  have hnodup (n : ℕ) : (l n).Nodup := by
    induction n with
    | zero => exact nodup_toList _
    | succ n ih =>
      rw [hstep]
      refine ih.append (nodup_toList _) ?_
      intro i hi hj
      have hi' : i ∈ s n := by rw [← hset]; exact List.mem_toFinset.mpr hi
      exact (mem_sdiff.mp (mem_toList.mp hj)).2 hi'
  have hprefix {n m : ℕ} (hnm : n ≤ m) : l n <+: l m := by
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨[], by simp⟩
    | succ m _ ih =>
      exact ih.trans ⟨_, (hstep m).symm⟩
  have hcard (n : ℕ) : (l n).length = (s n).card := by
    rw [← hset, List.toFinset_card_of_nodup (hnodup n)]
  have hlen : StrictMono fun n ↦ (l n).length :=
    fun n m hnm ↦ by simpa only [hcard] using card_lt_card (hs hnm)
  have hindex (i : ℕ) : i < (l (i + 1)).length :=
    lt_of_le_of_lt (StrictMono.id_le hlen i) (hlen (Nat.lt_succ_self i))
  -- Prefix compatibility makes the value at position i independent of the stage.
  let σ (i : ℕ) : ℕ := (l (i + 1))[i]'(hindex i)
  have hget (n i : ℕ) (hi : i < (l n).length) : σ i = (l n)[i] := by
    rcases le_total (i + 1) n with h | h
    · exact (List.prefix_iff_getElem.mp (hprefix h)).2 i (hindex i)
    · exact (List.prefix_iff_getElem.mp (hprefix h)).2 i hi |>.symm
  have hinj : Function.Injective σ := by
    intro i j hij
    let n := max (i + 1) (j + 1)
    have hi : i < (l n).length :=
      (hindex i).trans_le (hlen.monotone (le_max_left (i + 1) (j + 1)))
    have hj : j < (l n).length :=
      (hindex j).trans_le (hlen.monotone (le_max_right (i + 1) (j + 1)))
    have h : (⟨i, hi⟩ : Fin (l n).length) = ⟨j, hj⟩ :=
      List.nodup_iff_injective_getElem.mp (hnodup n)
        ((hget n i hi).symm.trans (hij.trans (hget n j hj)))
    exact congrArg Fin.val h
  have himage (n : ℕ) : (range (s n).card).image σ = s n := by
    rw [← hcard, ← hset]
    ext i
    simp only [mem_image, mem_range, List.mem_toFinset]
    constructor
    · rintro ⟨j, hj, e⟩
      exact List.mem_iff_getElem.mpr ⟨j, hj, (hget n j hj).symm.trans e⟩
    · intro hi
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp hi
      exact ⟨j, hj, (hget n j hj).trans e⟩
  have hsurj : Function.Surjective σ := by
    intro i
    obtain ⟨n, hn⟩ := hcover i
    rw [← himage] at hn
    obtain ⟨j, _, hj⟩ := mem_image.mp hn
    exact ⟨j, hj⟩
  exact ⟨Equiv.ofBijective σ ⟨hinj, hsurj⟩, himage⟩

/-- If the ordinary partial sums of a series converge to `u`, and the partial
sums of every rearrangement converge, then the net of finite sums converges to `u`. -/
theorem hasSum_of_summable_conditional_permutations {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] [T2Space E] {a : ℕ → E} {u : E}
    (ha : HasSum a u (SummationFilter.conditional ℕ))
    (hperm : ∀ σ : ℕ ≃ ℕ, Summable (a ∘ σ) (SummationFilter.conditional ℕ)) :
    HasSum a u := by
  classical
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff,
    Function.comp_def] at ha
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_atTop']
  intro U hU
  by_contra h
  push Not at h
  choose bad hsub hout using h
  choose bound hbound using exists_nat_subset_range
  let next (s : Finset ℕ) := range (bound s + 1)
  have hnext (s : Finset ℕ) : s < next s := by
    apply lt_of_le_of_lt (show s ≤ range (bound s) from hbound s)
    refine lt_of_le_of_ne (range_mono (Nat.le_succ _)) ?_
    intro heq
    have hcard := congrArg Finset.card heq
    simp [next] at hcard
  -- Each odd stage is outside U. Each even stage is an ordinary initial segment.
  let s : ℕ → Finset ℕ := Nat.rec ∅ fun n t ↦ if Even n then bad (next t) else next t
  have hstep (n : ℕ) : s (n + 1) = if Even n then bad (next (s n)) else next (s n) := rfl
  have hs : StrictMono s := strictMono_nat_of_lt_succ fun n ↦ by
    rw [hstep]
    split
    · exact (hnext _).trans_le (hsub _)
    · exact hnext _
  have hcard : StrictMono fun n ↦ (s n).card := fun _ _ hnm ↦ card_lt_card (hs hnm)
  have heven (n : ℕ) : s (2 * n) = range (s (2 * n)).card := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, hstep, ite_eq_right (by simp)]
      simp only [next, card_range]
  have hodd (n : ℕ) : (∑ i ∈ s (2 * n + 1), a i) ∉ U := by
    rw [hstep, ite_eq_left (even_two.mul_right n)]
    exact hout _
  obtain ⟨σ, hσ⟩ := exists_perm_finset_range s hs fun i ↦ by
    refine ⟨2 * (i + 1), ?_⟩
    rw [heven, mem_range]
    exact (by omega : i < 2 * (i + 1)).trans_le (StrictMono.id_le hcard (2 * (i + 1)))
  obtain ⟨v, hv⟩ := hperm σ
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff,
    Function.comp_def] at hv
  have hsum (n : ℕ) : (∑ i ∈ range (s n).card, a (σ i)) = ∑ i ∈ s n, a i := by
    rw [← sum_image σ.injective.injOn, hσ n]
  have hseq : Tendsto (fun n ↦ ∑ i ∈ s n, a i) atTop (𝓝 v) :=
    (hv.comp hcard.tendsto_atTop).congr hsum
  have htwice : StrictMono (fun n : ℕ ↦ 2 * n) := fun m n hmn ↦ by
    change 2 * m < 2 * n
    omega
  have hlimit : Tendsto (fun n ↦ ∑ i ∈ s (2 * n), a i) atTop (𝓝 u) :=
    (ha.comp (hcard.comp htwice).tendsto_atTop).congr fun n ↦
      congrArg (fun t : Finset ℕ ↦ ∑ i ∈ t, a i) (heven n).symm
  have hvu : v = u := tendsto_nhds_unique (hseq.comp htwice.tendsto_atTop) hlimit
  subst v
  obtain ⟨N, hN⟩ := tendsto_atTop'.mp hseq U hU
  exact hodd N (hN (2 * N + 1) (by omega))

end RiemannMasullo
