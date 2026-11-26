module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public noncomputable section
open Function Set
open scoped InnerProductSpace Topology
namespace RiemannMasullo

variable {ι H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem dense_linearCombination_of_total (p : ι → H)
    (hsep : ∀ w : H, (∀ i, ⟪p i, w⟫_ℂ = 0) → w = 0) :
    DenseRange (Finsupp.linearCombination ℂ p) := by
  let S := Submodule.span ℂ (range p)
  have htop : S.topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr ?_)
    intro u hu
    apply hsep u
    intro i
    exact Submodule.inner_right_of_mem_orthogonal
      (S.le_topologicalClosure (Submodule.subset_span (mem_range_self i))) hu
  have hd : Dense (S : Set H) := Submodule.dense_iff_topologicalClosure_eq_top.mpr htop
  change Dense (Set.range (Finsupp.linearCombination ℂ p))
  rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
  exact hd

private theorem norm_linearCombination_eq_of_gram (p : ι → H) (q : ι → K)
    (hgram : ∀ i j, ⟪p i, p j⟫_ℂ = ⟪q i, q j⟫_ℂ) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ p c‖ = ‖Finsupp.linearCombination ℂ q c‖ := by
  have hi : ⟪Finsupp.linearCombination ℂ p c, Finsupp.linearCombination ℂ p c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ q c, Finsupp.linearCombination ℂ q c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, sum_inner,
      inner_smul_left, inner_smul_right, hgram]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact ((inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans (congrArg Complex.re hi)).trans
    (inner_self_eq_norm_sq (𝕜 := ℂ) _)

/-- Two total Hilbert-space families with identical Gram kernels determine an isometric
linear equivalence carrying every vector of the first family to its counterpart. -/
theorem exists_linearIsometryEquiv_of_total_gram (p : ι → H) (q : ι → K)
    (hp : ∀ w : H, (∀ i, ⟪p i, w⟫_ℂ = 0) → w = 0)
    (hq : ∀ w : K, (∀ i, ⟪q i, w⟫_ℂ = 0) → w = 0)
    (hgram : ∀ i j, ⟪p i, p j⟫_ℂ = ⟪q i, q j⟫_ℂ) :
    ∃ U : H ≃ₗᵢ[ℂ] K, ∀ i, U (p i) = q i := by
  classical
  let e₁ := Finsupp.linearCombination ℂ p
  let e₂ := Finsupp.linearCombination ℂ q
  have hd₁ := dense_linearCombination_of_total p hp
  have hd₂ := dense_linearCombination_of_total q hq
  have hn (c : ι →₀ ℂ) : ‖e₂ ((LinearEquiv.refl ℂ (ι →₀ ℂ)) c)‖ = ‖e₁ c‖ :=
    (norm_linearCombination_eq_of_gram p q hgram c).symm
  let U := (LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry e₁ e₂ hd₁ hd₂ hn
  refine ⟨U, ?_⟩
  intro i
  have he := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ι →₀ ℂ)) e₁ e₂
    hd₁ hd₂ hn (Finsupp.single i 1)
  simpa only [U, e₁, e₂, Finsupp.linearCombination_single, one_smul, LinearEquiv.refl_apply] using he

/-- Matching total observation kernels identify the entire Hilbert spaces and preserve
all observations, rather than only comparing norms of already represented vectors. -/
theorem exists_linearIsometryEquiv_of_total_probe_gram
    (E : ι → StrongDual ℂ H) (q : ι → K)
    (hE : ∀ w : H, (∀ i, E i w = 0) → w = 0)
    (hq : ∀ w : K, (∀ i, ⟪q i, w⟫_ℂ = 0) → w = 0)
    (hgram : ∀ i j, ⟪(InnerProductSpace.toDual ℂ H).symm (E i),
      (InnerProductSpace.toDual ℂ H).symm (E j)⟫_ℂ = ⟪q i, q j⟫_ℂ) :
    ∃ U : H ≃ₗᵢ[ℂ] K, ∀ i w, E i w = ⟪q i, U w⟫_ℂ := by
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_total_gram
    (fun i ↦ (InnerProductSpace.toDual ℂ H).symm (E i)) q
    (fun w hw ↦ hE w (fun i ↦ by simpa only [InnerProductSpace.toDual_symm_apply] using hw i))
    hq hgram
  refine ⟨U, fun i w ↦ ?_⟩
  rw [← hU i, U.inner_map_map, InnerProductSpace.toDual_symm_apply]

end RiemannMasullo
