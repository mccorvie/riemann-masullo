module
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-! # Unconditional modes of a bounded Hilbert-space circle action

Embedding each vector as its circle orbit in vector-valued Haar L² changes its
norm by at most the uniform action bound in either direction. In that space the
coordinate sums are orthogonal projections. Their norms in the original space
are therefore bounded by the square of the action bound. Density and
equicontinuity give unconditional convergence without changing the original norm.
-/

public noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace RiemannMasullo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {L : ℝ} [Fact (0 < L)]
variable (ρ : AddCircle L → E →L[ℂ] E)
variable (hc : ∀ u, Continuous (fun s ↦ ρ s u))
local notation "μ" => (AddCircle.haarAddCircle : Measure (AddCircle L))

private def circleOrbitContinuous : E →ₗ[ℂ] C(AddCircle L, E) where
  toFun u := ⟨fun s ↦ ρ s u, hc u⟩
  map_add' u v := by ext s; exact map_add (ρ s) u v
  map_smul' c u := by ext s; exact map_smul (ρ s) c u

private def circleOrbitL2Linear : E →ₗ[ℂ] Lp E 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp (circleOrbitContinuous ρ hc)

private theorem circleOrbitL2Linear_ae (u : E) :
    circleOrbitL2Linear ρ hc u =ᵐ[μ] fun s ↦ ρ s u :=
  ContinuousMap.coeFn_toLp μ (circleOrbitContinuous ρ hc u)

private theorem circleOrbitL2Linear_bound (C : ℝ)
    (hb : ∀ s, ‖ρ s‖ ≤ C) (u : E) : ‖circleOrbitL2Linear ρ hc u‖ ≤ C * ‖u‖ := by
  have h : ∀ᵐ s ∂μ, ‖circleOrbitL2Linear ρ hc u s‖ ≤ C * ‖Lp.const 2 μ u s‖ := by
    filter_upwards [circleOrbitL2Linear_ae ρ hc u, Lp.coeFn_const 2 μ u] with s hs hu
    rw [hs, hu]
    exact ((ρ s).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hb s) (norm_nonneg u))
  simpa [Lp.norm_const 2 μ u (by norm_num)] using Lp.norm_le_mul_norm_of_ae_le_mul h

private def circleOrbitL2 (C : ℝ) (hb : ∀ s, ‖ρ s‖ ≤ C) : E →L[ℂ] Lp E 2 μ :=
  (circleOrbitL2Linear ρ hc).mkContinuous C (circleOrbitL2Linear_bound ρ hc C hb)

private theorem circleOrbitL2_ae (C : ℝ) (hb : ∀ s, ‖ρ s‖ ≤ C) (u : E) :
    circleOrbitL2 ρ hc C hb u =ᵐ[μ] fun s ↦ ρ s u := circleOrbitL2Linear_ae ρ hc u

private theorem circleOrbitL2_bound (C : ℝ) (hb : ∀ s, ‖ρ s‖ ≤ C) (u : E) :
    ‖circleOrbitL2 ρ hc C hb u‖ ≤ C * ‖u‖ := circleOrbitL2Linear_bound ρ hc C hb u

private theorem circleOrbitL2_lower (C : ℝ) (hb : ∀ s, ‖ρ s‖ ≤ C)
    (hzero : ρ 0 = ContinuousLinearMap.id ℂ E)
    (hadd : ∀ s t, ρ (s+t) = (ρ s).comp (ρ t)) (u : E) :
    ‖u‖ ≤ C * ‖circleOrbitL2 ρ hc C hb u‖ := by
  have he (s : AddCircle L) : ρ (-s) (ρ s u) = u := by
    rw [← ContinuousLinearMap.comp_apply, ← hadd, neg_add_cancel, hzero]
    rfl
  have h : ∀ᵐ s ∂μ, ‖Lp.const 2 μ u s‖ ≤ C * ‖circleOrbitL2 ρ hc C hb u s‖ := by
    filter_upwards [Lp.coeFn_const 2 μ u, circleOrbitL2_ae ρ hc C hb u] with s hu hs
    rw [hu, hs]
    calc
      ‖u‖ = ‖ρ (-s) (ρ s u)‖ := congrArg norm (he s).symm
      _ ≤ C * ‖ρ s u‖ := ((ρ (-s)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb (-s)) (norm_nonneg _))
  simpa [Lp.norm_const 2 μ u (by norm_num)] using Lp.norm_le_mul_norm_of_ae_le_mul h

private theorem circleOrbitL2_inner_eigen (C : ℝ) (hb : ∀ s, ‖ρ s‖ ≤ C)
    (v : ℤ → E) (heigen : ∀ s n, ρ s (v n) = _root_.fourier (-n) s • v n)
    (ℓ : ℤ → E →L[ℂ] ℂ)
    (hproj : ∀ n u, _root_.fourierCoeff (fun s ↦ ρ s u) (-n) = ℓ n u • v n)
    (n : ℤ) (u : E) :
    ⟪circleOrbitL2 ρ hc C hb (v n), circleOrbitL2 ρ hc C hb u⟫_ℂ =
      ℓ n u * (‖v n‖ : ℂ)^2 := by
  rw [L2.inner_def]
  have hscalar : ∀ s : AddCircle L, starRingEnd ℂ (_root_.fourier (-n) s) =
      _root_.fourier n s := by
    intro s
    rw [← _root_.fourier_neg, neg_neg]
  have he : (fun s : AddCircle L ↦
      ⟪circleOrbitL2 ρ hc C hb (v n) s, circleOrbitL2 ρ hc C hb u s⟫_ℂ) =ᵐ[μ]
      (fun s ↦ ⟪v n, _root_.fourier n s • ρ s u⟫_ℂ) := by
    filter_upwards [circleOrbitL2_ae ρ hc C hb (v n), circleOrbitL2_ae ρ hc C hb u] with s hv hu
    rw [hv, hu, heigen, inner_smul_left, hscalar, inner_smul_right]
  rw [integral_congr_ae he]
  have hi : Integrable (fun s : AddCircle L ↦ _root_.fourier n s • ρ s u) μ :=
    ((map_continuous (_root_.fourier n)).smul (hc u)).integrable_of_hasCompactSupport (.of_compactSpace _)
  rw [integral_inner hi]
  have hp : (∫ s : AddCircle L, _root_.fourier n s • ρ s u ∂μ) = ℓ n u • v n := by
    simpa only [_root_.fourierCoeff, neg_neg] using hproj n u
  rw [hp, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rfl

include hc in
/-- A uniformly bounded strongly continuous circle action with a total
biorthogonal family of one-dimensional Fourier modes has unconditional
coordinate expansions in the original Hilbert norm. -/
theorem hasSum_of_bounded_circle_modes (C : ℝ) (hC : 0 ≤ C) (hb : ∀ s, ‖ρ s‖ ≤ C)
    (hzero : ρ 0 = ContinuousLinearMap.id ℂ E)
    (hadd : ∀ s t, ρ (s+t) = (ρ s).comp (ρ t))
    (v : ℤ → E) (ℓ : ℤ → E →L[ℂ] ℂ)
    (hrow : ∀ j n, ℓ j (v n) = if j = n then 1 else 0)
    (heigen : ∀ s n, ρ s (v n) = _root_.fourier (-n) s • v n)
    (hproj : ∀ n u, _root_.fourierCoeff (fun s ↦ ρ s u) (-n) = ℓ n u • v n)
    (hd : (Submodule.span ℂ (range v)).topologicalClosure = ⊤) :
    (∀ (s : Finset ℤ) (u : E), ‖∑ n ∈ s, ℓ n u • v n‖ ≤ C^2 * ‖u‖) ∧
      ∀ u : E, HasSum (fun n : ℤ ↦ ℓ n u • v n) u := by
  classical
  let O := circleOrbitL2 ρ hc C hb
  let S (s : Finset ℤ) : E →L[ℂ] E := ∑ n ∈ s, (ℓ n).smulRight (v n)
  have hS (s : Finset ℤ) (u : E) : S s u = ∑ n ∈ s, ℓ n u • v n := by
    simp only [S, sum_apply, ContinuousLinearMap.smulRight_apply]
  have hrows (s : Finset ℤ) (u : E) (n : ℤ) (hn : n ∈ s) : ℓ n (u - S s u) = 0 := by
    rw [map_sub, hS, map_sum]
    simp [map_smul, hrow, smul_eq_mul, hn]
  have hbound (s : Finset ℤ) (u : E) : ‖S s u‖ ≤ C^2 * ‖u‖ := by
    have ho : ⟪O (S s u), O (u - S s u)⟫_ℂ = 0 := by
      nth_rw 1 [hS]
      rw [map_sum, sum_inner]
      apply Finset.sum_eq_zero
      intro n hn
      rw [map_smul, inner_smul_left, circleOrbitL2_inner_eigen ρ hc C hb v heigen ℓ hproj,
        hrows s u n hn, zero_mul, mul_zero]
    have honorm : ‖O (S s u)‖ ≤ ‖O u‖ := by
      have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
      rw [← map_add, add_sub_cancel] at he
      nlinarith [sq_nonneg ‖O (u - S s u)‖, norm_nonneg (O (S s u)), norm_nonneg (O u)]
    calc
      ‖S s u‖ ≤ C * ‖O (S s u)‖ := circleOrbitL2_lower ρ hc C hb hzero hadd _
      _ ≤ C * ‖O u‖ := mul_le_mul_of_nonneg_left honorm hC
      _ ≤ C * (C * ‖u‖) := mul_le_mul_of_nonneg_left (circleOrbitL2_bound ρ hc C hb u) hC
      _ = C^2 * ‖u‖ := by ring
  refine ⟨fun s u ↦ (hS s u) ▸ hbound s u, fun u ↦ ?_⟩
  have heq : (∃ D : ℝ, ∀ (s : Finset ℤ) (u : E), ‖S s u‖ ≤ D * ‖u‖) ↔
      Equicontinuous (fun s : Finset ℤ ↦ (S s : E → E)) :=
    (NormedSpace.equicontinuous_tfae S).out 4 2
  have hequi : Equicontinuous (fun s : Finset ℤ ↦ (S s : E → E)) := heq.mp ⟨C^2, hbound⟩
  have hclosed : IsClosed {u : E | Tendsto (fun s : Finset ℤ ↦ S s u) atTop (𝓝 u)} :=
    hequi.isClosed_setOfPred_tendsto continuous_id
  have hspan : ∀ u ∈ Submodule.span ℂ (range v),
      Tendsto (fun s : Finset ℤ ↦ S s u) atTop (𝓝 u) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨n, rfl⟩ := hu
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ({n} : Finset ℤ)] with s hs
        have hn : n ∈ s := hs (by simp)
        rw [hS]
        simp [hrow, hn]
    | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : Finset ℤ ↦ (0 : E)) atTop (𝓝 0))
    | add u v _ _ hu hv => simpa only [map_add] using hu.add hv
    | smul c u _ hu => simpa only [map_smul] using hu.const_smul c
  have hdense : Dense (Submodule.span ℂ (range v) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hd
  have hsub : (Submodule.span ℂ (range v) : Set E) ⊆
      {u : E | Tendsto (fun s : Finset ℤ ↦ S s u) atTop (𝓝 u)} := hspan
  have ht : Tendsto (fun s : Finset ℤ ↦ S s u) atTop (𝓝 u) :=
    closure_minimal hsub hclosed (hdense u)
  change Tendsto (fun s : Finset ℤ ↦ ∑ n ∈ s, ℓ n u • v n) atTop (𝓝 u)
  simpa only [hS] using ht

end RiemannMasullo
