module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Bases

public section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

/-- A countable `lp` sum of separable spaces is separable for finite exponent. -/
theorem lp.separableSpace {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, SeparableSpace (E i)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    SeparableSpace (lp E p) := by
  classical
  let embed (s : Finset ι) (x : ∀ i : s, E i) : lp E p :=
    ∑ i : s, lp.single p i (x i)
  have hc (s : Finset ι) : Continuous (embed s) := by
    apply continuous_finsetSum
    intro i _
    exact (lp.isometry_single (E := E) (p := p) (i : ι)).continuous.comp (continuous_apply i)
  have hsep : IsSeparable (⋃ s, range (embed s)) :=
    IsSeparable.iUnion fun s ↦ isSeparable_range (hc s)
  have hd : Dense (⋃ s, range (embed s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single hp x)
    apply Eventually.of_forall
    intro s
    refine mem_iUnion.2 ⟨s, ⟨fun i ↦ x i, ?_⟩⟩
    exact Finset.sum_coe_sort s (fun i ↦ lp.single p i (x i))
  have he : closure (⋃ s, range (embed s)) = univ := hd.closure_eq
  rw [← isSeparable_univ_iff, ← he]
  exact hsep.closure
