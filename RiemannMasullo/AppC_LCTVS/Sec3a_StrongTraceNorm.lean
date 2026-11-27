module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import Mathlib.Tactic.NoncommRing

/-! # Strong convergence around a fixed nuclear operator -/

@[expose] public noncomputable section

open Filter Topology
open scoped TensorProduct

namespace RiemannMasullo

section StrongTraceNorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι}

private abbrev nuclearLeftProduct (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    nuclearEndomorphisms H := ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩

private abbrev nuclearRightProduct (T : nuclearEndomorphisms H) (A : H →L[ℂ] H) :
    nuclearEndomorphisms H := ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩

private abbrev nuclearTensor (z : StrongDual ℂ H ⊗[ℂ] H) : nuclearEndomorphisms H :=
  ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩

local notation "left(" A "," T ")" => nuclearLeftProduct A T
local notation "right(" T "," A ")" => nuclearRightProduct T A
local notation "tensor(" z ")" => nuclearTensor z

private theorem tendsto_traceNorm_left_mul_tensor_of_stronglyNull
    (Q : ι → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun i ↦ Q i x) l (𝓝 0))
    (z : StrongDual ℂ H ⊗[ℂ] H) :
    Tendsto (fun i ↦ traceNorm left(Q i,tensor(z))) l (𝓝 0) := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have core := (traceNorm_normedSpaceCore (H := H)).toCore
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    have heq (i : ι) : left(Q i,tensor(φ ⊗ₜ[ℂ] y)) =
        ⟨φ.smulRight (Q i y), smulRight_mem_nuclearEndomorphisms φ (Q i y)⟩ := by
      apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      change Q i (tensorToFiniteRank (φ ⊗ₜ[ℂ] y) x) = φ x • Q i y
      rw [tensorToFiniteRank_tmul, map_smul]
    simpa only [heq, traceNorm_smulRight, norm_zero, mul_zero] using
      (hQ y).norm.const_mul ‖φ‖
  | add z w hz hw =>
    have heq (i : ι) : left(Q i,tensor(z + w)) =
        left(Q i,tensor(z)) + left(Q i,tensor(w)) := by
      apply Subtype.ext
      change Q i * tensorToFiniteRank (z + w) =
        Q i * tensorToFiniteRank z + Q i * tensorToFiniteRank w
      rw [map_add, mul_add]
    simp_rw [heq]
    exact squeeze_zero (fun i ↦ core.norm_nonneg _) (fun i ↦ core.norm_triangle _ _)
      (by simpa only [zero_add] using hz.add hw)

/-- An eventually bounded strongly null family on the left sends a fixed nuclear
operator to zero in trace norm. -/
theorem tendsto_traceNorm_left_mul_of_stronglyNull
    (T : nuclearEndomorphisms H) (Q : ι → H →L[ℂ] H) {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖Q i‖ ≤ C) (hQ : ∀ x, Tendsto (fun i ↦ Q i x) l (𝓝 0)) :
    Tendsto (fun i ↦ traceNorm ⟨Q i * T.val, mul_mem_nuclearEndomorphisms_left (Q i) T⟩)
      l (𝓝 0) := by
  change Tendsto (fun i ↦ traceNorm left(Q i,T)) l (𝓝 0)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have core := (traceNorm_normedSpaceCore (H := H)).toCore
  let C₀ := max C 1
  have hC₀ : 0 < C₀ := zero_lt_one.trans_le (le_max_right _ _)
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (div_pos (half_pos hε) hC₀)
  let F : nuclearEndomorphisms H := tensor(z)
  have hF : Tendsto (fun i ↦ traceNorm left(Q i,F)) l (𝓝 0) :=
    tendsto_traceNorm_left_mul_tensor_of_stronglyNull Q hQ z
  have hsmall : C₀ * traceNorm (T - F) < ε / 2 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hC₀).mp hz
  filter_upwards [hbound, Metric.tendsto_nhds.mp hF (ε / 2) (half_pos hε)] with i hi hFsmall
  have hsplit : left(Q i,T) = left(Q i,T - F) + left(Q i,F) := by
    apply Subtype.ext
    change Q i * T.val = Q i * (T.val - F.val) + Q i * F.val
    rw [mul_sub, sub_add_cancel]
  have ht : traceNorm left(Q i,T - F) ≤ C₀ * traceNorm (T - F) :=
    (traceNorm_mul_left_le (Q i) (T - F)).trans
      (mul_le_mul_of_nonneg_right (hi.trans (le_max_left _ _)) (core.norm_nonneg _))
  have hFnonneg : 0 ≤ traceNorm left(Q i,F) := core.norm_nonneg _
  have hTnonneg : 0 ≤ traceNorm left(Q i,T) := core.norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hFnonneg] at hFsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hTnonneg]
  rw [hsplit]
  have htriangle := core.norm_triangle (left(Q i,T - F)) (left(Q i,F))
  change traceNorm (left(Q i,T - F) + left(Q i,F)) ≤
    traceNorm left(Q i,T - F) + traceNorm left(Q i,F) at htriangle
  linarith

/-- An eventually bounded family on the right sends a fixed nuclear operator
to zero in trace norm if its adjoints are strongly null. -/
theorem tendsto_traceNorm_right_mul_of_adjointStronglyNull
    (T : nuclearEndomorphisms H) (Q : ι → H →L[ℂ] H) {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖Q i‖ ≤ C)
    (hQ : ∀ x, Tendsto (fun i ↦ (Q i).adjoint x) l (𝓝 0)) :
    Tendsto (fun i ↦ traceNorm ⟨T.val * Q i, mul_mem_nuclearEndomorphisms_right (Q i) T⟩)
      l (𝓝 0) := by
  change Tendsto (fun i ↦ traceNorm right(T,Q i)) l (𝓝 0)
  obtain ⟨hT, _⟩ := traceNorm_adjoint_eq T.val T.property
  let Tadj : nuclearEndomorphisms H := ⟨T.val.adjoint, hT⟩
  have heq (i : ι) : traceNorm right(T,Q i) = traceNorm left((Q i).adjoint,Tadj) := by
    obtain ⟨hQadj, htrace⟩ := traceNorm_adjoint_eq (T.val * Q i)
      (mul_mem_nuclearEndomorphisms_right (Q i) T)
    refine htrace.symm.trans (congrArg traceNorm (Subtype.ext ?_))
    exact ContinuousLinearMap.adjoint_comp T.val (Q i)
  have hadj_bound : ∀ᶠ i in l, ‖(Q i).adjoint‖ ≤ C :=
    hbound.mono fun i hi ↦ by simpa only [ContinuousLinearMap.adjoint.norm_map] using hi
  simp_rw [heq]
  exact tendsto_traceNorm_left_mul_of_stronglyNull Tadj (fun i ↦ (Q i).adjoint) hadj_bound hQ

/-- Eventually bounded multipliers converge in trace norm around a fixed nuclear
operator when the left multipliers converge strongly and the right multipliers'
adjoints converge strongly. -/
theorem tendsto_traceNorm_sandwich_of_strong_left_adjoint_right
    (T : nuclearEndomorphisms H) (L R : ι → H →L[ℂ] H) (L₀ R₀ : H →L[ℂ] H)
    {C D : ℝ} (hLbound : ∀ᶠ i in l, ‖L i‖ ≤ C) (hRbound : ∀ᶠ i in l, ‖R i‖ ≤ D)
    (hL : ∀ x, Tendsto (fun i ↦ L i x) l (𝓝 (L₀ x)))
    (hR : ∀ x, Tendsto (fun i ↦ (R i).adjoint x) l (𝓝 (R₀.adjoint x))) :
    let sandwich (A B : H →L[ℂ] H) : nuclearEndomorphisms H :=
      ⟨(A * T.val) * B, mul_mem_nuclearEndomorphisms_right B
        ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩⟩
    Tendsto (fun i ↦ traceNorm (sandwich (L i) (R i) - sandwich L₀ R₀)) l (𝓝 0) := by
  intro sandwich
  change Tendsto (fun i ↦ traceNorm (right(left(L i,T),R i) - right(left(L₀,T),R₀))) l (𝓝 0)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have core := (traceNorm_normedSpaceCore (H := H)).toCore
  let TL (i : ι) := left(L i - L₀,T)
  let TR (i : ι) := right(T,R i - R₀)
  have hL' : Tendsto (fun i ↦ traceNorm (TL i)) l (𝓝 0) := by
    apply tendsto_traceNorm_left_mul_of_stronglyNull T (fun i ↦ L i - L₀)
      (C := C + ‖L₀‖)
    · exact hLbound.mono fun _ hi ↦ (norm_sub_le _ _).trans (add_le_add hi le_rfl)
    · intro x
      simpa only [sub_apply, sub_self] using
        (hL x).sub (tendsto_const_nhds (x := L₀ x))
  have hR' : Tendsto (fun i ↦ traceNorm (TR i)) l (𝓝 0) := by
    apply tendsto_traceNorm_right_mul_of_adjointStronglyNull T (fun i ↦ R i - R₀)
      (C := D + ‖R₀‖)
    · exact hRbound.mono fun _ hi ↦ (norm_sub_le _ _).trans (add_le_add hi le_rfl)
    · intro x
      simpa only [map_sub, sub_apply, sub_self] using
        (hR x).sub (tendsto_const_nhds (x := R₀.adjoint x))
  have hsplit (i : ι) : right(left(L i,T),R i) - right(left(L₀,T),R₀) =
      right(TL i,R i) + left(L₀,TR i) := by
    apply Subtype.ext
    change (L i * T.val) * R i - (L₀ * T.val) * R₀ =
      ((L i - L₀) * T.val) * R i + L₀ * (T.val * (R i - R₀))
    noncomm_ring
  have hlim : Tendsto (fun i ↦ D * traceNorm (TL i) + ‖L₀‖ * traceNorm (TR i)) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hL'.const_mul D).add (hR'.const_mul ‖L₀‖)
  refine squeeze_zero' (.of_forall fun _ ↦ core.norm_nonneg _) (hRbound.mono fun i hi ↦ ?_) hlim
  rw [hsplit i]
  refine (core.norm_triangle _ _).trans (add_le_add ?_ (traceNorm_mul_left_le L₀ (TR i)))
  exact (traceNorm_mul_right_le (R i) (TL i)).trans
    (mul_le_mul_of_nonneg_right hi (core.norm_nonneg _))

end StrongTraceNorm
end RiemannMasullo
