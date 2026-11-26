module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Strong measurability from measurable inner products

In a separable Hilbert space a function is strongly measurable as soon as its inner products
against all fixed vectors are measurable. The proof expands the function in a Hilbert basis,
which is countable, and passes to the limit of the partial sums.
-/

open Filter MeasureTheory Topology
open scoped InnerProductSpace

public section

namespace RiemannMasullo

/-- In a separable Hilbert space, a function all of whose inner products against fixed vectors
are measurable is strongly measurable. -/
theorem stronglyMeasurable_of_measurable_inner {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] {F : α → E}
    (hF : ∀ h : E, Measurable fun a ↦ ⟪h, F a⟫_ℂ) : StronglyMeasurable F := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  have : Countable w := by
    refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (b i) (1 / 2))
      ?_ (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hd : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), b.orthonormal.norm_eq_one i,
        b.orthonormal.norm_eq_one j, b.orthonormal.inner_eq_zero hij]
      norm_num
    nlinarith [dist_nonneg (x := b i) (y := b j)]
  refine stronglyMeasurable_of_tendsto (atTop : Filter (Finset w))
    (f := fun s a ↦ ∑ i ∈ s, ⟪b i, F a⟫_ℂ • b i) (fun s ↦ ?_) ?_
  · have h := Finset.stronglyMeasurable_sum s (f := fun i a ↦ ⟪b i, F a⟫_ℂ • b i) fun i _ ↦
      (hF (b i)).stronglyMeasurable.smul_const (b i)
    convert h using 1
    ext a
    rw [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro a
    have h := b.hasSum_repr (F a)
    simpa only [HasSum, b.repr_apply_apply, SummationFilter.unconditional_filter] using h

end RiemannMasullo
