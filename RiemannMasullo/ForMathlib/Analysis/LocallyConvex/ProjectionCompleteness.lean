module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Order.Lattice

/-! # Completeness from a family of stabilizing projections -/

@[expose] public noncomputable section

open Bornology Filter Set Topology

namespace RiemannMasullo

open scoped Uniformity

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [BarrelledSpace ℂ E]
variable {ι : Type*} [Preorder ι] [Nonempty ι]

omit [PolynormableSpace ℂ E] [BarrelledSpace ℂ E] in
/-- On a Cauchy filter the terms eventually differ from a single reference
point by less than any prescribed continuous seminorm tolerance. -/
private theorem cauchy_exists_seminorm_center {F : Filter E} (hF : Cauchy F)
    (p : Seminorm ℂ E) (hp : Continuous p) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, ∀ᶠ x in F, p (x - y) < ε := by
  let : F.NeBot := hF.1
  have hU : {z : E × E | z.2 - z.1 ∈ p.ball 0 ε} ∈ 𝓤 E := by
    rw [uniformity_eq_comap_nhds_zero]
    exact preimage_mem_comap (p.ball_mem_nhds hp hε)
  obtain ⟨S, hS, hSS⟩ := mem_prod_same_iff.mp (hF.2 hU)
  obtain ⟨y, hy⟩ := Filter.nonempty_of_mem hS
  refine ⟨y, mem_of_superset hS fun x hx ↦ ?_⟩
  exact p.mem_ball_zero.mp (hSS (show (y,x) ∈ S ×ˢ S from ⟨hy,hx⟩))

omit [PolynormableSpace ℂ E] in
/-- If the limits of the projections kept changing, successive differences
along a chain could be rescaled to be unbounded on the Cauchy filter. Their
pointwise supremum is a continuous seminorm by barrelledness. -/
private theorem eventually_equal_projection_limits (P : ι → E →L[ℂ] E) {F : Filter E}
    (hF : Cauchy F) (z : ι → E) (hz : ∀ i, Tendsto (P i) F (𝓝 (z i)))
    (p : Seminorm ℂ E) (hp : Continuous p) (hpos : ∀ x ≠ 0, 0 < p x)
    (hstable : ∀ a : ℕ → ι, Monotone a → ∀ x, ∃ N, ∀ n ≥ N, P (a (n+1)) x = P (a n) x) :
    ∃ i, ∀ j ≥ i, z j = z i := by
  classical
  let : F.NeBot := hF.1
  by_contra! h
  choose next hn hdiff using h
  let a : ℕ → ι := Nat.rec (Classical.choice ‹Nonempty ι›) fun _ i ↦ next i
  have ha : Monotone a := monotone_nat_of_le_succ fun n ↦ hn (a n)
  let D (n : ℕ) := P (a (n+1)) - P (a n)
  let δ (n : ℕ) := z (a (n+1)) - z (a n)
  have hδ (n : ℕ) : 0 < p (δ n) := hpos _ (sub_ne_zero.mpr (hdiff (a n)))
  let w (n : ℕ) := (n : ℝ) / p (δ n)
  let q (n : ℕ) : Seminorm ℂ E := Real.toNNReal (w n) • p.comp (D n).toLinearMap
  have hq (n : ℕ) (x : E) : q n x = w n * p (D n x) := by
    change (Real.toNNReal (w n) : ℝ) * _ = _
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) (hδ n).le)]
    rfl
  have hb : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun x ↦ by
    obtain ⟨N, hN⟩ := hstable a ha x
    refine ⟨(Finset.range N).sup q x, forall_mem_range.mpr fun n ↦ ?_⟩
    by_cases hn : n < N
    · exact Seminorm.le_finset_sup_apply (Finset.mem_range.mpr hn)
    · rw [hq, show D n x = 0 from sub_eq_zero.mpr (hN _ (le_of_not_gt hn)), map_zero, mul_zero]
      exact apply_nonneg _ _
  let Q := ⨆ n, q n
  have hQ : Continuous Q := by
    rw [show (Q : E → ℝ) = _ from Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup q (fun n ↦
      ((hp.comp (D n).continuous).const_mul (w n)).congr fun x ↦ (hq n x).symm) hb
  obtain ⟨y, hy⟩ := cauchy_exists_seminorm_center hF Q hQ zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_gt (1 + Q y)
  have hlim : Tendsto (fun x ↦ q n x) F (𝓝 (w n * p (δ n))) := by
    simp_rw [hq]
    exact (hp.continuousAt.tendsto.comp ((hz _).sub (hz _))).const_mul _
  have hle : w n * p (δ n) ≤ 1 + Q y := le_of_tendsto hlim (hy.mono fun x hx ↦ by
    refine ((le_ciSup hb n : q n ≤ Q) x).trans ?_
    calc
      Q x = Q ((x-y) + y) := by rw [sub_add_cancel]
      _ ≤ Q (x-y) + Q y := map_add_le_add _ _ _
      _ ≤ 1 + Q y := add_le_add hx.le le_rfl)
  rw [show w n * p (δ n) = (n : ℝ) from div_mul_cancel₀ _ (hδ n).ne'] at hle
  exact (not_le_of_gt hn) hle

omit [Nonempty ι] in
/-- A common limit of the stage projections is the limit of the original
Cauchy filter when the projection orbits are bounded and the maps eventually
fix each vector. -/
private theorem tendsto_of_eventually_constant_projections (P : ι → E →L[ℂ] E)
    (hB : ∀ x, IsVonNBounded ℂ (range fun i ↦ P i x))
    (hfix : ∀ x i, ∃ j ≥ i, P j x = x) {F : Filter E} (hF : Cauchy F)
    (i : ι) (z : E) (hz : ∀ j ≥ i, Tendsto (P j) F (𝓝 z)) : F ≤ 𝓝 z := by
  let : F.NeBot := hF.1
  let H := PolynormableSpace.withSeminorms ℂ E
  change Tendsto id F (𝓝 z)
  apply (H.tendsto_nhds id z).mpr
  intro p ε hε
  let q (j : ι) := p.val.comp (P j).toLinearMap
  have hb : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun x ↦ by
    have h := (H.isVonNBounded_iff_seminorm_bddAbove.mp (hB x)) p
    rwa [← range_comp] at h
  let Q := p.val ⊔ ⨆ j, q j
  have hsup : Continuous (⨆ j, q j : Seminorm ℂ E) := by
    rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup q (fun j ↦ p.property.comp (P j).continuous) hb
  have hQ : Continuous Q := p.property.sup hsup
  obtain ⟨y, hy⟩ := cauchy_exists_seminorm_center hF Q hQ (half_pos hε)
  obtain ⟨j, hij, hj⟩ := hfix y i
  have hle : p.val (z - y) ≤ ε / 2 := by
    apply le_of_tendsto (p.property.continuousAt.tendsto.comp ((hz j hij).sub_const y))
    filter_upwards [hy] with x hx
    change p.val (P j x - y) ≤ ε / 2
    rw [← hj, ← map_sub]
    exact ((le_ciSup hb j : q j ≤ _) (x-y)).trans ((le_sup_right : (⨆ j, q j) ≤ Q) _ |>.trans hx.le)
  filter_upwards [hy] with x hx
  have hxy := (show p.val ≤ Q from le_sup_left) (x-y)
  change p.val (x-z) < ε
  rw [← sub_add_sub_cancel x y z]
  exact (map_add_le_add p.val _ _).trans_lt (by
    rw [map_sub_rev p.val y z]
    linarith)
omit [AddCommGroup E] [Module ℂ E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [BarrelledSpace ℂ E] in
/-- A Cauchy filter converges after projection through a complete space. -/
theorem cauchy_projection_limit {V : Type*} [UniformSpace V] [CompleteSpace V]
    (r : E → V) (i : V → E) (hr : UniformContinuous r) (hi : Continuous i)
    {F : Filter E} (hF : Cauchy F) : ∃ t : E, Tendsto (i ∘ r) F (𝓝 t) := by
  obtain ⟨t, ht⟩ := CompleteSpace.complete (hF.map hr)
  exact ⟨i t, hi.continuousAt.tendsto.comp ht⟩

/-- Complete projected filters give completeness when the projections stabilize
pointwise on chains, have bounded orbits, and fix every vector cofinally. -/
theorem complete_of_stabilizing_projections (P : ι → E →L[ℂ] E)
    (hB : ∀ x, IsVonNBounded ℂ (range fun i ↦ P i x))
    (hfix : ∀ x i, ∃ j ≥ i, P j x = x)
    (hstable : ∀ a : ℕ → ι, Monotone a → ∀ x, ∃ N, ∀ n ≥ N, P (a (n+1)) x = P (a n) x)
    (p : Seminorm ℂ E) (hp : Continuous p) (hpos : ∀ x ≠ 0, 0 < p x)
    (hlim : ∀ (F : Filter E), Cauchy F → ∀ a, ∃ t : E, Tendsto (P a) F (𝓝 t)) :
    CompleteSpace E := by
  refine ⟨fun {F} hF ↦ ?_⟩
  choose z hz using hlim F hF
  obtain ⟨a, ha⟩ := eventually_equal_projection_limits P hF z hz p hp hpos hstable
  exact ⟨z a, tendsto_of_eventually_constant_projections P hB hfix hF a (z a) fun b hb ↦ ha b hb ▸ hz b⟩

end RiemannMasullo
