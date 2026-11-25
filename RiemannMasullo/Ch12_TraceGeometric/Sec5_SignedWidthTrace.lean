module

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-! # Signed trace across a dense Hilbert restriction

Paper: Theorem 12.5.1.1, pp. 519–520, and the missing comparison in §12.3.
For a representative-preserving dense restriction of Hilbert quotients, the
signed difference of two compatible nuclear traces is the trace on the actual
closed kernel of the restriction. The proof splits its orthogonal complement
and uses two-sided contractive Tikhonov regularizations, without asserting a
bounded inverse or surjectivity. This theorem does not bound or annihilate the
kernel trace. -/

public noncomputable section

open Filter Function Set Topology ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

namespace RiemannMasullo.WidthTrace

section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem width_resolvent (A : H →L[ℂ] H) (hA : 0 ≤ A) (hd : DenseRange A) :
    ∃ U : ℕ → H →L[ℂ] H,
      (∀ n x, U n (x + (n+1) • A x) = x) ∧
      (∀ n x, U n x + (n+1) • A (U n x) = x) ∧
      (∀ n x, ‖x - U n x‖ ≤ ‖x‖) ∧
      ∀ x, Tendsto (fun n => U n x) atTop (𝓝 0) := by
  classical
  let S (n : ℕ) : H →L[ℂ] H := 1 + (n+1) • A
  have hS (n : ℕ) : 1 ≤ S n := by
    exact le_add_of_nonneg_right (nsmul_nonneg hA _)
  have hu (n : ℕ) : IsUnit (S n) := (isStrictlyPositive_one.of_le (hS n)).isUnit
  let U (n : ℕ) : H →L[ℂ] H := ↑(hu n).unit⁻¹
  have h₀ (n : ℕ) : 0 ≤ U n := by
    apply CFC.inv_nonneg_of_nonneg
    simpa using (zero_le_one.trans (hS n))
  have h₁ (n : ℕ) : U n ≤ 1 := by
    apply CStarAlgebra.inv_le_one
    change (1 : H →L[ℂ] H) ≤ S n
    exact hS n
  have bound (B : H →L[ℂ] H) (hb : 0 ≤ B) (hb' : B ≤ 1) (x : H) : ‖B x‖ ≤ ‖x‖ :=
    (B.le_opNorm x).trans <| by
      simpa using mul_le_mul_of_nonneg_right
        ((CStarAlgebra.norm_le_one_iff_of_nonneg B hb).2 hb') (norm_nonneg x)
  have bU (n : ℕ) := bound (U n) (h₀ n) (h₁ n)
  have bI (n : ℕ) (x : H) : ‖x - U n x‖ ≤ ‖x‖ := by
    exact bound (1 - U n) (sub_nonneg.mpr (h₁ n)) (sub_le_self _ (h₀ n)) x
  have left (n : ℕ) (x : H) : U n (x + (n+1) • A x) = x := by
    change (U n * S n) x = (1 : H →L[ℂ] H) x
    rw [show U n * S n = 1 from (hu n).val_inv_mul]
  have right (n : ℕ) (x : H) : U n x + (n+1) • A (U n x) = x := by
    change (S n * U n) x = (1 : H →L[ℂ] H) x
    rw [show S n * U n = 1 from (hu n).mul_val_inv]
  refine ⟨U, left, right, bI, ?_⟩
  have onRange (z : H) : Tendsto (fun n => U n (A z)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1) * ‖z‖)
    · intro n
      have eq : (n+1) • U n (A z) = z - U n z := by
        have h := left n z
        rw [map_add, map_nsmul] at h
        exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
      have hb := bI n z
      rw [← eq, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul] at hb
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one] at hb
      rw [one_div, inv_mul_eq_div]
      exact (le_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hb)
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖z‖
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨z, hz⟩ := Metric.denseRange_iff.mp hd x (ε/2) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (onRange z) (ε/2) (by positivity)] with n hn
  have hb := bU n (x - A z)
  rw [map_sub] at hb
  have ht := dist_triangle (U n x) (U n (A z)) 0
  simp only [dist_eq_norm, sub_zero] at hz hn ht ⊢
  linarith

/-- Tikhonov inverses with both regularized identities pointwise contractive and
strongly convergent, even when the inverse on the dense range is unbounded. -/
theorem exists_tikhonov_inverse (j : H →L[ℂ] K) (hinj : Function.Injective j)
    (hdense : DenseRange j) : ∃ R : ℕ → K →L[ℂ] H,
    (∀ n x, ‖R n (j x)‖ ≤ ‖x‖) ∧ (∀ n y, ‖j (R n y)‖ ≤ ‖y‖) ∧
    (∀ x, Tendsto (fun n => R n (j x)) atTop (𝓝 x)) ∧
    (∀ y, Tendsto (fun n => j (R n y)) atTop (𝓝 y)) := by
  have had : DenseRange j.adjoint := by
    change Dense (j.adjoint.range : Set H)
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← j.orthogonal_ker,
      LinearMap.ker_eq_bot.mpr hinj, Submodule.bot_orthogonal_eq_top]
  obtain ⟨U, uL, uR, ub, ut⟩ := width_resolvent (j.adjoint.comp j)
    (nonneg_iff_isPositive.mpr j.isPositive_adjoint_comp_self) (had.comp hdense j.adjoint.continuous)
  obtain ⟨V, vL, vR, vb, vt⟩ := width_resolvent (j.comp j.adjoint)
    (nonneg_iff_isPositive.mpr j.isPositive_self_comp_adjoint) (hdense.comp had j.continuous)
  let R (n : ℕ) : K →L[ℂ] H := (n+1) • ((U n).comp j.adjoint)
  have lhs (n : ℕ) (x : H) : R n (j x) = x - U n x := by
    have h := uL n x
    rw [map_add, map_nsmul] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have intertwine (n : ℕ) (w : H) : j (U n w) = V n (j w) := by
    have h := congrArg j (uR n w)
    simp only [map_add, map_nsmul] at h
    conv_rhs => rw [← h]
    exact (vL n (j (U n w))).symm
  have rhs (n : ℕ) (y : K) : j (R n y) = y - V n y := by
    change j ((n+1) • U n (j.adjoint y)) = _
    rw [map_nsmul, intertwine]
    have h := vL n y
    rw [map_add, map_nsmul] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  refine ⟨R, fun n x => by rw [lhs]; exact ub n x, fun n y => by rw [rhs]; exact vb n y, ?_, ?_⟩
  · intro x
    simpa only [lhs, sub_zero] using
      (show Tendsto (fun n => x - U n x) atTop (𝓝 (x - 0)) from tendsto_const_nhds.sub (ut x))
  · intro y
    simpa only [rhs, sub_zero] using
      (show Tendsto (fun n => y - V n y) atTop (𝓝 (y - 0)) from tendsto_const_nhds.sub (vt y))

end

section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private def prePresentation {T : H →L[ℂ] H} (r : NuclearPresentation T) (B : K →L[ℂ] H) :
    NuclearPresentation (T.comp B) where
  coeff := r.coeff
  functional i := (r.functional i).comp B
  disc := r.disc
  isBanachDisc := r.isBanachDisc
  vector := r.vector
  vector_mem := r.vector_mem
  summable_coeff := r.summable_coeff
  equicontinuous U hU := by
    have h := (B.continuous.tendsto' 0 0 (map_zero B)).eventually (r.equicontinuous U hU)
    simpa only [ContinuousLinearMap.comp_apply, map_zero] using h
  hasSum x := r.hasSum (B x)

private theorem preNuclear {T : H →L[ℂ] H} (hT : IsNuclearOperator T) (B : K →L[ℂ] H) :
    IsNuclearOperator (T.comp B) := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation T).mp hT
  exact (isNuclearOperator_iff_nonempty_presentation _).mpr ⟨prePresentation r B⟩

private theorem tendsto_trace_precomp (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    (B : ℕ → H →L[ℂ] H) (hc : ∀ n x, ‖B n x‖ ≤ ‖x‖)
    (hid : ∀ x, Tendsto (fun n ↦ B n x) atTop (𝓝 x)) :
    Tendsto (fun n ↦ nuclearTrace hilbert_approximationProperty (T.comp (B n)) (preNuclear hT _))
      atTop (𝓝 (nuclearTrace hilbert_approximationProperty T hT)) := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation T).mp hT
  obtain ⟨C, hC₀, hC⟩ :=
    ((NormedSpace.equicontinuous_tfae r.functional).out 1 7).mp r.equicontinuous
  obtain ⟨D, hD⟩ :=
    ((NormedSpace.isVonNBounded_iff ℂ).mp r.isBanachDisc.bounded).exists_norm_le
  have hcost : Summable (fun i ↦ ‖r.coeff i‖ * (‖r.functional i‖ * ‖(r.vector i : H)‖)) := by
    refine (r.summable_coeff.mul_right (C * D)).of_nonneg_of_le (fun _ ↦ by positivity) ?_
    intro i
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hC i) (hD _ (r.vector_mem i)) (norm_nonneg _) hC₀) (norm_nonneg _)
  let f := fun (n i : ℕ) ↦ r.coeff i * r.functional i (B n (r.vector i))
  have hlim := tendsto_tsum_of_dominated_convergence (f := f)
    (g := fun i ↦ r.coeff i * r.functional i (r.vector i)) hcost
    (fun i ↦ tendsto_const_nhds.mul ((r.functional i).continuous.continuousAt.tendsto.comp
      (hid (r.vector i))))
    (Eventually.of_forall fun n i ↦ by
      dsimp only [f]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (((r.functional i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hc n _) (norm_nonneg _))) (norm_nonneg _))
  have hsum (n : ℕ) : (∑' i, f n i) = nuclearTrace hilbert_approximationProperty
      (T.comp (B n)) (preNuclear hT _) :=
    ((exists_nuclearTrace_hasSum hilbert_approximationProperty _ (preNuclear hT (B n))).exists.choose_spec
      (prePresentation r (B n))).2.tsum_eq
  have hfinal := ((exists_nuclearTrace_hasSum hilbert_approximationProperty T hT).exists.choose_spec r).2.tsum_eq
  simpa only [hsum, hfinal, nuclearTrace] using hlim

private theorem trace_congr {A B : H →L[ℂ] H} (h : A = B)
    (ha : IsNuclearOperator A) (hb : IsNuclearOperator B) :
    nuclearTrace hilbert_approximationProperty A ha = nuclearTrace hilbert_approximationProperty B hb := by
  subst B
  rfl

/-- Two-sided strongly approximating contractions allow a bounded injective intertwiner
 to preserve the signed Hilbert trace, without requiring a bounded inverse. -/
theorem hilbertTrace_eq_of_intertwiner (j : H →L[ℂ] K) (hj : Injective j)
    (T : H →L[ℂ] H) (S : K →L[ℂ] K) (hT : IsNuclearOperator T) (hS : IsNuclearOperator S)
    (hinter : j.comp T = S.comp j) (R : ℕ → K →L[ℂ] H)
    (hcH : ∀ n x, ‖R n (j x)‖ ≤ ‖x‖) (hcK : ∀ n y, ‖j (R n y)‖ ≤ ‖y‖)
    (hidH : ∀ x, Tendsto (fun n ↦ R n (j x)) atTop (𝓝 x))
    (hidK : ∀ y, Tendsto (fun n ↦ j (R n y)) atTop (𝓝 y)) :
    hilbertTrace ⟨T, hT⟩ = hilbertTrace ⟨S, hS⟩ := by
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  have hleft := tendsto_trace_precomp T hT (fun n ↦ (R n).comp j) hcH hidH
  have hright := tendsto_trace_precomp S hS (fun n ↦ j.comp (R n)) hcK hidK
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  apply Eventually.of_forall
  intro n
  have hcyc := nuclearTrace_factor_comps hilbert_approximationProperty hilbert_approximationProperty
    j hj (T.comp (R n)) (preNuclear hT _)
  exact (trace_congr (congrArg (fun A : H →L[ℂ] K ↦ A.comp (R n)) hinter.symm) _ _).trans hcyc.symm

end

section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem kernel_closed (j : H →L[ℂ] K) : IsClosed (j.ker : Set H) := j.isClosed_ker

theorem kernel_invariant (j : H →L[ℂ] K) (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (h : j.comp T = S.comp j) : ∀ x ∈ j.ker, T x ∈ j.ker := by
  intro x hx
  change j x = 0 at hx
  change j (T x) = 0
  exact (DFunLike.congr_fun h x).trans (by change S (j x) = 0; rw [hx, map_zero])

def kernelEmbedding (j : H →L[ℂ] K) : j.kerᗮ →L[ℂ] K := j.comp j.kerᗮ.subtypeL

theorem kernelEmbedding_project (j : H →L[ℂ] K) (x : H) :
    kernelEmbedding j (j.kerᗮ.orthogonalProjectionOnto x) = j x := by
  change j (j.kerᗮ.starProjection x) = j x
  have hz : j (j.ker.starProjection x) = 0 := (j.ker.orthogonalProjectionOnto x).property
  rw [Submodule.starProjection_orthogonal_val, map_sub, hz, sub_zero]

theorem kernelEmbedding_injective (j : H →L[ℂ] K) : Injective (kernelEmbedding j) := by
  intro x y h
  change j (x : H) = j (y : H) at h
  have hk : (x : H) - y ∈ j.ker := by change j ((x : H) - y) = 0; rw [map_sub, h, sub_self]
  have hb : (x : H) - y ∈ j.ker ⊓ j.kerᗮ := ⟨hk, j.kerᗮ.sub_mem x.property y.property⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hb
  exact Subtype.ext (sub_eq_zero.mp hb)

theorem kernelEmbedding_dense (j : H →L[ℂ] K) (hj : DenseRange j) :
    DenseRange (kernelEmbedding j) := by
  refine Dense.mono ?_ hj
  rintro _ ⟨x, rfl⟩
  exact ⟨_, kernelEmbedding_project j x⟩

def diagonalBlock (M : Submodule ℂ H) [CompleteSpace M] (T : nuclearEndomorphisms H) :
    nuclearEndomorphisms M :=
  ⟨M.orthogonalProjectionOnto.comp (T.val.comp M.subtypeL),
    (traceNorm_sandwich_le T.val T.property M.subtypeL M.orthogonalProjectionOnto).choose⟩

theorem kernelBlock_eq_restrict (j : H →L[ℂ] K) (T : nuclearEndomorphisms H)
    (S : K →L[ℂ] K) (h : j.comp T.val = S.comp j) :
    (diagonalBlock j.ker T).val = T.val.restrict (kernel_invariant j T.val S h) := by
  apply ContinuousLinearMap.ext
  intro x
  exact j.ker.orthogonalProjectionOnto_mem_subspace_eq_self
    (T.val.restrict (kernel_invariant j T.val S h) x)

theorem kernelBlock_restrict_nuclear (j : H →L[ℂ] K) (T : nuclearEndomorphisms H)
    (S : K →L[ℂ] K) (h : j.comp T.val = S.comp j) :
    IsNuclearOperator (T.val.restrict (kernel_invariant j T.val S h)) := by
  rw [← kernelBlock_eq_restrict j T S h]
  exact (diagonalBlock j.ker T).property

theorem kernelEmbedding_intertwines (j : H →L[ℂ] K) (T : nuclearEndomorphisms H)
    (S : K →L[ℂ] K) (h : j.comp T.val = S.comp j) :
    (kernelEmbedding j).comp (diagonalBlock j.kerᗮ T).val = S.comp (kernelEmbedding j) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (kernelEmbedding_project j (T.val (x : H))).trans (DFunLike.congr_fun h (x : H))

private theorem projected_nuclear (M : Submodule ℂ H) [CompleteSpace M]
    (T : nuclearEndomorphisms H) : IsNuclearOperator (M.orthogonalProjectionOnto.comp T.val) := by
  let P := M.orthogonalProjectionOnto
  obtain ⟨c, f, y, hc, hf, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear _).mp T.property
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, f, P ∘ y, hc, hf, (P.continuous.tendsto' 0 0 (map_zero P)).comp hy, ?_⟩
  intro x
  have hn := P.hasSum (hs x)
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul, P] using hn

private theorem diagonalBlock_trace (M : Submodule ℂ H) [CompleteSpace M]
    (T : nuclearEndomorphisms H) : ∃ B : nuclearEndomorphisms H,
    B.val = M.starProjection.comp T.val ∧ hilbertTrace B = hilbertTrace (diagonalBlock M T) := by
  let A := M.orthogonalProjectionOnto.comp T.val
  have hA : IsNuclearOperator A := projected_nuclear M T
  have hi : Injective M.subtypeL := Subtype.val_injective
  have hn := isNuclearOperator_factor_comps M.subtypeL hi A hA
  refine ⟨⟨M.subtypeL.comp A, hn.2⟩, rfl, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  exact (nuclearTrace_factor_comps hilbert_approximationProperty hilbert_approximationProperty
    M.subtypeL hi A hA).symm

theorem hilbertTrace_split_kernel (j : H →L[ℂ] K) (T : nuclearEndomorphisms H) :
    hilbertTrace T = hilbertTrace (diagonalBlock j.ker T) + hilbertTrace (diagonalBlock j.kerᗮ T) := by
  obtain ⟨B, hB, htB⟩ := diagonalBlock_trace j.ker T
  obtain ⟨C, hC, htC⟩ := diagonalBlock_trace j.kerᗮ T
  have he : B + C = T := by
    apply Subtype.ext
    change B.val + C.val = T.val
    rw [hB, hC]
    apply ContinuousLinearMap.ext
    intro x
    exact j.ker.starProjection_add_starProjection_orthogonal (T.val x)
  obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
  rw [← htB, ← htC, ← hL T, ← hL B, ← hL C, ← map_add, he]

end

section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For a dense Hilbert restriction intertwining the nuclear endomorphisms, the
signed wide-minus-narrow trace is the Hilbert trace of the actual restriction
on the discarded closed kernel. No closed-range inverse is assumed. -/
theorem hilbertTrace_sub_eq_kernelRestriction (j : H →L[ℂ] K) (hd : DenseRange j)
    (T : nuclearEndomorphisms H) (S : nuclearEndomorphisms K)
    (h : j.comp T.val = S.val.comp j) :
    hilbertTrace T - hilbertTrace S =
      hilbertTrace ⟨T.val.restrict (kernel_invariant j T.val S.val h),
        kernelBlock_restrict_nuclear j T S.val h⟩ := by
  let J := kernelEmbedding j
  have hj : Injective J := kernelEmbedding_injective j
  have hdJ : DenseRange J := kernelEmbedding_dense j hd
  obtain ⟨R, hc₁, hc₂, hs₁, hs₂⟩ := exists_tikhonov_inverse J hj hdJ
  have he : hilbertTrace (diagonalBlock j.kerᗮ T) = hilbertTrace S :=
    hilbertTrace_eq_of_intertwiner J hj _ S.val (diagonalBlock j.kerᗮ T).property S.property
      (kernelEmbedding_intertwines j T S.val h) R hc₁ hc₂ hs₁ hs₂
  calc
    _ = hilbertTrace (diagonalBlock j.ker T) := by rw [hilbertTrace_split_kernel j T, he, add_sub_cancel_right]
    _ = _ := congrArg hilbertTrace (Subtype.ext (kernelBlock_eq_restrict j T S.val h))

end

end RiemannMasullo.WidthTrace
