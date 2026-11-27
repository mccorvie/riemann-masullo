module

public import RiemannMasullo.Ch12_TraceGeometric.Sec2
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.GroupTheory.OrderOfElement

/-! # Nonidentity overlaps of normalized indentations

This gives a topological obstruction to dropping all nonidentity scalar weights in
(12.2.2.1), p. 508. It does not identify these weights with arithmetic shells.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] {H : Subgroup G} [MeasurableSingletonClass H] {b : G → ℝ}

/-- If nonidentity subgroup translates of the identity component approach `1`,
a count-normalized continuous indentation has positive overlap with a nonidentity
translate. The subgroup may itself meet the identity component trivially. -/
theorem exists_indentation_translate_overlap (hb : IsIndentation H Measure.count b)
    (hacc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ ξ : H, ξ ≠ 1 ∧ ∃ c ∈ connectedComponent (1 : G), c * (ξ : G) ∈ U) :
    ∃ ξ : H, ξ ≠ 1 ∧ ∃ x : G, 0 < b x ∧ 0 < b ((ξ : G) * x) := by
  classical
  by_contra hn
  have hz (ξ : H) (hξ : ξ ≠ 1) (x : G) (hx : 0 < b x) : b ((ξ : G) * x) = 0 := by
    apply le_antisymm _ (hb.2.1 _)
    exact le_of_not_gt fun hp ↦ hn ⟨ξ, hξ, x, hx, hp⟩
  have hone (x : G) (hx : 0 < b x) : b x = 1 := by
    have he : (fun k : H ↦ b ((k : G)⁻¹ * x)) =
        ({1} : Set H).indicator (fun _ ↦ b x) := by
      funext k
      by_cases hk : k = 1
      · subst k; simp
      · have hz' := hz k⁻¹ (by simpa using hk) x hx
        simpa [hk] using hz'
    have hi := (hb.2.2.2 x).2
    rw [he, integral_indicator_const _ (measurableSet_singleton _), count_real_singleton,
      one_smul] at hi
    exact hi
  obtain ⟨x, hx⟩ : ∃ x : G, 0 < b x := by
    by_contra hall
    have he (x : G) : b x = 0 := le_antisymm (le_of_not_gt fun hp ↦ hall ⟨x, hp⟩) (hb.2.1 _)
    have hi := (hb.2.2.2 (1 : G)).2
    simp [he] at hi
  have h01 (y : G) : b y = 0 ∨ b y = 1 := by
    rcases eq_or_lt_of_le (hb.2.1 y) with he | hp
    · exact Or.inl he.symm
    · exact Or.inr (hone y hp)
  have hhalf (y : G) : b y ≠ 1/2 := by
    rcases h01 y with he | he <;> rw [he] <;> norm_num
  have hfix (c y : G) (hc : c ∈ connectedComponent (1 : G)) : b (c*y) = b y := by
    let f : G → ℝ := fun g ↦ b (g*y)
    have hf : ContinuousOn f (connectedComponent (1 : G)) :=
      (hb.1.comp (continuous_id.mul continuous_const)).continuousOn
    have hone' : f 1 = b y := by simp [f]
    rcases h01 (c*y) with hc0 | hc1
    · rcases h01 y with hy0 | hy1
      · rw [hc0, hy0]
      · have hmid : (1/2 : ℝ) ∈ Icc (f c) (f 1) := by
          change b (c*y) ≤ 1/2 ∧ 1/2 ≤ f 1
          rw [hc0, hone', hy1]
          norm_num
        obtain ⟨g, _, hg⟩ := isPreconnected_connectedComponent.intermediate_value hc
          mem_connectedComponent hf hmid
        exact (hhalf (g*y) hg).elim
    · rcases h01 y with hy0 | hy1
      · have hmid : (1/2 : ℝ) ∈ Icc (f 1) (f c) := by
          change f 1 ≤ 1/2 ∧ 1/2 ≤ b (c*y)
          rw [hc1, hone', hy0]
          norm_num
        obtain ⟨g, _, hg⟩ := isPreconnected_connectedComponent.intermediate_value
          mem_connectedComponent hc hf hmid
        exact (hhalf (g*y) hg).elim
      · rw [hc1, hy1]
  let U : Set G := {g | 0 < b (g*x)}
  have ho : IsOpen U := isOpen_lt continuous_const (hb.1.comp (continuous_id.mul continuous_const))
  have hU : (1 : G) ∈ U := by simpa [U] using hx
  obtain ⟨ξ, hξ, c, hc, hcx⟩ := hacc U ho hU
  change 0 < b ((c*(ξ : G))*x) at hcx
  rw [mul_assoc, hfix c _ hc] at hcx
  exact hn ⟨ξ, hξ, x, hx, hcx⟩

/-- The overlap persists on an open set, where the simultaneous-translate weight of
p. 508 is strictly positive already from the identity term. -/
theorem exists_open_indentation_weight_overlap (hb : IsIndentation H Measure.count b)
    (hacc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ ξ : H, ξ ≠ 1 ∧ ∃ c ∈ connectedComponent (1 : G), c * (ξ : G) ∈ U) :
    ∃ ξ : H, ξ ≠ 1 ∧ ∃ U : Set G, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U,
      0 < b x ∧ 0 < b ((ξ : G) * x) ∧
        0 < diagonalIndentationWeight H Measure.count b (x, (ξ : G) * x) := by
  obtain ⟨ξ, hξ, z, hz, hξz⟩ := exists_indentation_translate_overlap hb hacc
  let U : Set G := {x | 0 < b x} ∩ {x | 0 < b ((ξ : G) * x)}
  refine ⟨ξ, hξ, U, (isOpen_lt continuous_const hb.1).inter
    (isOpen_lt continuous_const (hb.1.comp (continuous_const.mul continuous_id))),
    ⟨z, hz, hξz⟩, ?_⟩
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := hx
  change 0 < b x at hx₁
  change 0 < b ((ξ : G) * x) at hx₂
  refine ⟨hx₁, hx₂, ?_⟩
  let y := (ξ : G) * x
  let F : H → ℝ := fun k ↦ b ((k : G)⁻¹ * x) * b ((k : G)⁻¹ * y)
  change 0 < ∫ k, F k ∂Measure.count
  have hy := (hb.2.2.2 y).1
  have hs := integrable_count_iff.mp hy
  have hi : Integrable F Measure.count := (hb.2.2.2 x).1.mul_bdd hy.aestronglyMeasurable
    (ae_of_all _ fun k ↦ hs.le_tsum k fun j _ ↦ norm_nonneg _)
  apply (integral_pos_iff_support_of_nonneg (fun k ↦ mul_nonneg (hb.2.1 _) (hb.2.1 _)) hi).2
  have hsub : ({1} : Set H) ⊆ Function.support F := by
    intro k hk
    have : k = 1 := hk
    subst k
    change b _ * b _ ≠ 0
    simpa [y] using (mul_pos hx₁ hx₂).ne'
  exact lt_of_lt_of_le (by simp : 0 < Measure.count ({1} : Set H))
    (measure_mono hsub)

/-- A subgroup element of infinite order forces overlap if its first coordinate
is in the identity component and its second coordinate comes from a compact group.
This permits an ambient noncompact second coordinate space. -/
theorem exists_open_indentation_weight_overlap_of_compact_factor
    {A B K : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace (A × B)] {H : Subgroup (A × B)} [MeasurableSingletonClass H] {b : A × B → ℝ}
    (hb : IsIndentation H Measure.count b) (j : K →ₜ* B) {h : H} {k : K}
    (hj : j k = (h : A × B).2) (hinf : ¬ IsOfFinOrder (h : A × B))
    (hA : (h : A × B).1 ∈ connectedComponent (1 : A)) :
    ∃ ξ : H, ξ ≠ 1 ∧ ∃ U : Set (A × B), IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U,
      0 < b x ∧ 0 < b ((ξ : A × B) * x) ∧
        0 < diagonalIndentationWeight H Measure.count b (x, (ξ : A × B) * x) := by
  apply exists_open_indentation_weight_overlap hb
  intro V ho hv
  have hcont : Continuous (fun k : K ↦ ((1 : A), j k)) := continuous_const.prodMk j.continuous
  change ((1 : A), (1 : B)) ∈ V at hv
  have hU : (fun k : K ↦ ((1 : A), j k)) ⁻¹' V ∈ 𝓝 (1 : K) := by
    exact hcont.continuousAt (x := (1 : K)) (by simpa only [map_one] using ho.mem_nhds hv)
  obtain ⟨n, hn, hnV⟩ := frequently_atTop.1
    (mapClusterPt_iff_frequently.1 (mapClusterPt_one_atTop_pow k) _ hU) 1
  refine ⟨h^n, fun he ↦ hinf (isOfFinOrder_iff_pow_eq_one.2
    ⟨n, hn, congrArg Subtype.val he⟩), ((((h : A × B).1 ^ n)⁻¹ : A), (1 : B)), ?_, ?_⟩
  · change _ ∈ connectedComponent ((1 : A), (1 : B))
    rw [connectedComponent_prod]
    exact ⟨(Subgroup.connectedComponentOfOne A).inv_mem
      ((Subgroup.connectedComponentOfOne A).pow_mem hA n), mem_connectedComponent⟩
  · change ((1 : A), j (k^n)) ∈ V at hnV
    rw [map_pow, hj] at hnV
    change ((((h : A × B).1 ^ n)⁻¹) * (h : A × B).1 ^ n, (1 : B) * (h : A × B).2 ^ n) ∈ V
    simpa only [inv_mul_cancel, one_mul] using hnV

end RiemannMasullo
