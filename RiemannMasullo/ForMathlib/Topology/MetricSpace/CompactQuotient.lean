module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Sequences

@[expose] public section

open Filter Set Topology

namespace RiemannMasullo

/-- An open quotient map from a complete pseudometric space onto a Hausdorff space lifts
each compact set to a compact set. -/
theorem exists_isCompact_image_eq_of_isOpenQuotientMap
    {X Y : Type*} [PseudoMetricSpace X] [CompleteSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsOpenQuotientMap f) {s : Set Y} (hs : IsCompact s) :
    ∃ t : Set X, IsCompact t ∧ f '' t = s := by
  classical
  let r (n : ℕ) : ℝ := (1 / 2) ^ n
  -- Shrink an open lift while retaining a finite cover by balls of radius r n.
  have step (n : ℕ) (U : Set X) (hU : IsOpen U) (hcover : s ⊆ f '' U) :
      ∃ V : Set X, IsOpen V ∧ s ⊆ f '' V ∧ closure V ⊆ U ∧
        ∃ C : Set X, C.Finite ∧ closure V ⊆ ⋃ x ∈ C, Metric.closedBall x (r n) := by
    have hsmall (x : U) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ r n ∧ Metric.closedBall x.val ε ⊆ U := by
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds x.property)
      refine ⟨min (δ / 2) (r n), lt_min (by positivity) (by dsimp [r]; positivity),
        min_le_right _ _, ?_⟩
      exact (Metric.closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hδ))).trans hball
    choose ε hε hle hsub using hsmall
    obtain ⟨I, hI⟩ := hs.elim_finite_subcover (fun x : U ↦ f '' Metric.ball x.val (ε x))
      (fun x ↦ hf.isOpenMap _ Metric.isOpen_ball) (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hcover hy
        exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_image_of_mem f (Metric.mem_ball_self (hε _))⟩)
    let V := ⋃ x ∈ I, Metric.ball x.val (ε x)
    have hclosure : closure V ⊆ ⋃ x ∈ I, Metric.closedBall x.val (ε x) :=
      closure_minimal (iUnion₂_mono fun x _ ↦ Metric.ball_subset_closedBall)
        (isClosed_biUnion_finset fun _ _ ↦ Metric.isClosed_closedBall)
    refine ⟨V, isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball, ?_,
      hclosure.trans (iUnion₂_subset fun x _ ↦ hsub x), Subtype.val '' (I : Set U),
      I.finite_toSet.image _, ?_⟩
    · simpa only [V, image_iUnion] using hI
    · intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hclosure hx)
      exact mem_iUnion₂.mpr ⟨c.val, mem_image_of_mem _ hc, Metric.closedBall_subset_closedBall (hle c) hxc⟩
  choose next hnextOpen hnextCover hnextSub hnextFinite using step
  let U : ℕ → {U : Set X // IsOpen U ∧ s ⊆ f '' U} :=
    Nat.rec ⟨univ, isOpen_univ, by rw [image_univ, hf.surjective.range_eq]; exact subset_univ _⟩
      (fun n V ↦ ⟨next n V.val V.property.1 V.property.2, hnextOpen n _ _ _, hnextCover n _ _ _⟩)
  let V (n : ℕ) : Set X := (U n).val
  have hnest (n : ℕ) : closure (V (n + 1)) ⊆ V n := hnextSub n _ _ _
  have hanti : Antitone V := antitone_nat_of_succ_le fun n ↦ subset_closure.trans (hnest n)
  have hfinite (n : ℕ) (δ : ℝ) (hδ : r n < δ) :
      ∃ C : Set X, C.Finite ∧ closure (V (n + 1)) ⊆ ⋃ x ∈ C, Metric.ball x δ := by
    obtain ⟨C, hC, hballs⟩ := hnextFinite n (U n).val (U n).property.1 (U n).property.2
    exact ⟨C, hC, hballs.trans (iUnion₂_mono fun _ _ ↦ Metric.closedBall_subset_ball hδ)⟩
  let A := ⋂ n, closure (V (n + 1))
  have hA : IsCompact A := by
    refine (Metric.totallyBounded_iff.mpr fun δ hδ ↦ ?_).isCompact_of_isClosed
      (isClosed_iInter fun _ ↦ isClosed_closure)
    obtain ⟨n, hn⟩ : ∃ n, r n < δ := exists_pow_lt_of_lt_one hδ (by norm_num)
    obtain ⟨C, hC, hballs⟩ := hfinite n δ hn
    exact ⟨C, hC, (iInter_subset _ n).trans hballs⟩
  refine ⟨A ∩ f ⁻¹' s, hA.inter_right (hs.isClosed.preimage hf.continuous), ?_⟩
  apply Subset.antisymm (image_subset_iff.mpr inter_subset_right)
  intro y hy
  choose x hx hfx using fun n : ℕ ↦ (U (n + 1)).property.2 hy
  have htotal : TotallyBounded (range x) := Metric.totallyBounded_iff.mpr fun δ hδ ↦ by
    obtain ⟨n, hn⟩ : ∃ n, r n < δ := exists_pow_lt_of_lt_one hδ (by norm_num)
    obtain ⟨C, hC, hballs⟩ := hfinite n δ hn
    refine ⟨C ∪ x '' Iio n, hC.union ((finite_Iio n).image x), ?_⟩
    rintro _ ⟨m, rfl⟩
    by_cases hm : m < n
    · exact mem_iUnion₂.mpr ⟨x m, Or.inr (mem_image_of_mem x hm), Metric.mem_ball_self hδ⟩
    · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp
        (hballs (subset_closure (hanti (Nat.succ_le_succ (Nat.le_of_not_gt hm)) (hx m))))
      exact mem_iUnion₂.mpr ⟨c, Or.inl hc, hxc⟩
  obtain ⟨z, _, φ, hφ, hlim⟩ :=
    (htotal.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  have hfy : f z = y := by
    apply tendsto_nhds_unique ((hf.continuous.tendsto z).comp hlim)
    have hconst : f ∘ x ∘ φ = fun _ ↦ y := funext fun m ↦ hfx (φ m)
    rw [hconst]
    exact tendsto_const_nhds
  refine ⟨z, ⟨mem_iInter.mpr fun n ↦ ?_, show f z ∈ s from hfy.symm ▸ hy⟩, hfy⟩
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [(hφ.tendsto_atTop.eventually (eventually_ge_atTop n))] with m hm
  exact subset_closure (hanti (Nat.succ_le_succ hm) (hx (φ m)))

end RiemannMasullo
