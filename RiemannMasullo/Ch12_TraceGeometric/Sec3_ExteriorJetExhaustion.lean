module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CriticalWindowTrace
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

/-! # Uniform lower-window convergence along an exhaustion of admitted jets

The subspaces may exhaust a proper closed spectral space. The bound is uniform
over the sharp spatial cutoff and all additional jointly measurable lower masks. -/

@[expose] public noncomputable section
open Classical Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RiemannMasullo
set_option quotPrecheck false

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
local notation "RP(" T ", " P ")" => (⟨(T : nuclearEndomorphisms H).val * P,
  mul_mem_nuclearEndomorphisms_right P T⟩ : nuclearEndomorphisms H)

/-- Right compression by increasing orthogonal projections converges in trace
norm on their closed supremum, including when that subspace is proper. -/
theorem tendsto_traceNorm_right_starProjection (T : nuclearEndomorphisms H)
    (U : ι → Submodule ℂ H) [∀ i, (U i).HasOrthogonalProjection] (hU : Monotone U) :
    let P := (⨆ i, U i).topologicalClosure.starProjection
    Tendsto (fun i ↦ traceNorm (RP(T,(U i).starProjection) - RP(T,P))) atTop (𝓝 0) := by
  intro P
  let Q (i : ι) := (U i).starProjection-P
  have hQ (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    simpa only [Q,P,sub_apply,sub_self] using
      (Submodule.starProjection_tendsto_closure_iSup U hU x).sub (tendsto_const_nhds (x := P x))
  have hbound (i : ι) : ‖Q i‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [(U i).starProjection_norm_le,
      (⨆ i,U i).topologicalClosure.starProjection_norm_le])
  have hself (i : ι) : (Q i).adjoint = Q i :=
    ((isSelfAdjoint_starProjection (U i)).sub (isSelfAdjoint_starProjection _)).adjoint_eq
  obtain ⟨hn,-⟩ := traceNorm_adjoint_eq T.val T.property
  let S : nuclearEndomorphisms H := ⟨T.val.adjoint,hn⟩
  apply (spectralTruncatedConvolution_trace_tendsto_null H Q hQ hbound S).congr
  intro i
  let D := RP(T,(U i).starProjection) - RP(T,P)
  obtain ⟨hd,he⟩ := traceNorm_adjoint_eq D.val D.property
  have hD : D.val.adjoint = Q i*S.val := by
    have heq : D.val = T.val * Q i := by change _ - _ = _ * (_ - _); rw [mul_sub]
    rw [heq,ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,hself]; rfl
  refine (congrArg traceNorm (Subtype.ext hD.symm)).trans he

end

section
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
variable (g : ℝ → G) (ℓ : G → ℝ) (α : ℝ)
local notation "ν" => μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 3 (ℓ x)))
local notation "W" => Lp ℂ 2 ν
local notation "tr(" L ", " T ")" => hilbertTrace (⟨(L : W →L[ℂ] W) * (T : nuclearEndomorphisms W).val,
  mul_mem_nuclearEndomorphisms_left L T⟩ : nuclearEndomorphisms W)
local notation "RP(" T ", " P ")" => (⟨(T : nuclearEndomorphisms W).val * P,
  mul_mem_nuclearEndomorphisms_right P T⟩ : nuclearEndomorphisms W)

/-- Quantitative stability of the signed trace density for any two nuclear
inputs with the same moving output mask. -/
theorem integral_masked_trace_sub_le (hg : Measurable g) (hℓ : Measurable ℓ) (hα : 0 < α)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y) (m : ℝ → G → ℂ)
    (hm : Measurable (Function.uncurry m)) (hb : ∀ y x, ‖m y x‖ ≤ 1)
    (hs : ∀ y x, 3*y/4 < ℓ x → m y x = 0) (L : ℝ → W →L[ℂ] W)
    (hL : ∀ y (u : W), (L y u : G → ℂ) =ᵐ[ν] fun x ↦ m y x * u ((g y)⁻¹*x))
    (T S : nuclearEndomorphisms W) :
    (∫ y in Ioi (0:ℝ), Real.exp (-α*y/2)*‖tr(L y,T)-tr(L y,S)‖) ≤ 20/(3*α) * traceNorm (T-S) := by
  have h := (integrable_critical_masked_trace μ g ℓ α hg hℓ hα hshift m hm hb hs L hL (T-S)).2
  have he (y : ℝ) : tr(L y,T)-tr(L y,S) = tr(L y,T-S) := by
    obtain ⟨f,hf⟩ := hilbertTrace_linear (H := W)
    rw [← hf,← hf,← hf,← map_sub]
    congr 1
    apply Subtype.ext
    simp [mul_sub]
  simpa only [he,criticalOrbitBound] using h

set_option maxHeartbeats 900000 in
/-- One stage suffices for all admissible lower masks at once, with the
absolute error integrated in the critical detector norm. -/
theorem eventually_masked_jet_trace_sub_lt {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hg : Measurable g) (hℓ : Measurable ℓ) (hα : 0 < α)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y) (T : nuclearEndomorphisms W)
    (U : ι → Submodule ℂ W) [∀ i, (U i).HasOrthogonalProjection] (hU : Monotone U)
    {ε : ℝ} (hε : 0 < ε) :
    let P := (⨆ i,U i).topologicalClosure.starProjection
    ∀ᶠ i in atTop, ∀ (m : ℝ → G → ℂ), Measurable (Function.uncurry m) → (∀ y x, ‖m y x‖ ≤ 1) →
      (∀ y x, 3*y/4 < ℓ x → m y x = 0) → ∀ (L : ℝ → W →L[ℂ] W),
      (∀ y (u : W), (L y u : G → ℂ) =ᵐ[ν] fun x ↦ m y x * u ((g y)⁻¹*x)) →
      (∫ y in Ioi (0:ℝ), Real.exp (-α*y/2)*
        ‖tr(L y,RP(T,(U i).starProjection))-tr(L y,RP(T,P))‖) < ε := by
  intro P
  have ht : Tendsto (fun i ↦ traceNorm (RP(T,(U i).starProjection) - RP(T,P))) atTop (𝓝 0) :=
    tendsto_traceNorm_right_starProjection T U hU
  have h := ht.const_mul (20/(3*α))
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const hε] with i hi
  intro m hm hb hs L hL
  exact (integral_masked_trace_sub_le μ g ℓ α hg hℓ hα hshift m hm hb hs L hL
    RP(T,(U i).starProjection) RP(T,P)).trans_lt hi

end
end RiemannMasullo

