module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public noncomputable section

open Filter Set Topology

namespace RiemannMasullo

/-- A pointwise holomorphic family of functionals on a barrelled space consists of continuous
linear functionals throughout a connected open set if it does so in a neighborhood of one point. -/
theorem exists_continuousLinearMap_of_analytic_continuation
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    {b : ℂ} (hb : b ∈ U) (hbase : ∀ᶠ z in 𝓝 b, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z)
    {z : ℂ} (hz : z ∈ U) : ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z := by
  classical
  let P := {z : ℂ | ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z}
  let V := interior P ∩ U
  have hV : IsOpen V := isOpen_interior.inter hU
  have analyticDeriv (f : E) {x : ℂ} (hx : x ∈ U) (n : ℕ) : AnalyticAt ℂ (iteratedDeriv n (Φ f)) x := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hΦ f x hx
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  -- Difference quotients recover the Taylor coefficients wherever the evaluations are continuous.
  have hcoeff (n : ℕ) : ∀ y ∈ V, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) y := by
    induction n with
    | zero => exact fun y hy ↦ by simp only [iteratedDeriv_zero]; exact (interior_subset hy.1 : y ∈ P)
    | succ n ih =>
      intro x hx
      let A (y : ℂ) : E →L[ℂ] ℂ := if hy : y ∈ V then (ih y hy).choose else 0
      have hA {y : ℂ} (hy : y ∈ V) (f : E) : A y f = iteratedDeriv n (Φ f) y := by
        simpa only [A, dite_eq_left hy] using (ih y hy).choose_spec f
      let D (y : ℂ) := (y - x)⁻¹ • (A y - A x)
      have hlim : Tendsto (fun y f ↦ D y f) (𝓝[≠] x) (𝓝 fun f ↦ iteratedDeriv (n + 1) (Φ f) x) := by
        refine tendsto_pi_nhds.mpr fun f ↦ ?_
        have hd := analyticDeriv f hx.2 n
        rw [iteratedDeriv_succ]
        refine hd.differentiableAt.hasDerivAt.tendsto_slope.congr' ?_
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy
        simp only [D, smul_apply, sub_apply, hA hy, hA hx, slope, vsub_eq_sub]
      exact ⟨continuousLinearMapOfTendsto D hlim, fun _ ↦ rfl⟩
  -- The Taylor series propagates continuity across every ball contained in the domain.
  have hball (y : ℂ) (hy : y ∈ V) {r : ℝ} (hr : Metric.ball y r ⊆ U) : Metric.ball y r ⊆ P := by
    choose A hA using fun n ↦ hcoeff n y hy
    intro x hx
    let T (s : Finset ℕ) : E →L[ℂ] ℂ := ∑ n ∈ s, (n.factorial : ℂ)⁻¹ • (x - y) ^ n • A n
    have hlim : Tendsto (fun s f ↦ T s f) atTop (𝓝 fun f ↦ Φ f x) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      have h := Complex.hasSum_taylorSeries_on_ball ((hΦ f).differentiableOn.mono hr) hx
      simp only [T, sum_apply, smul_apply, hA]
      exact h
    exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩
  apply interior_subset (s := P)
  suffices h : U ⊆ V from (h hz).1
  refine hconn.subset_of_closure_inter_subset hV ⟨b, hb, mem_interior_iff_mem_nhds.mpr hbase, hb⟩ ?_
  rintro x ⟨hx, hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (r / 2) (half_pos hr)
  have hballU : Metric.ball y (r / 2) ⊆ U := (Metric.ball_subset_ball' (by
    rw [dist_comm y x]; linarith : r / 2 + dist y x ≤ r)).trans hsub
  exact ⟨interior_maximal (hball y hy hballU) Metric.isOpen_ball hxy, hxU⟩

/-- For linear maps from a barrelled space into continuous functions with the compact-open
topology, continuity of all point evaluations implies continuity of the map. -/
theorem continuous_of_continuous_eval_barrelled
    {E X : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] [TopologicalSpace X] (T : E → C(X, ℂ))
    (heval : ∀ x, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = T f x) : Continuous T := by
  choose L hL using heval
  refine continuous_iff_continuousAt.mpr fun f ↦ ?_
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A (x : K) := L x.val
  have hbound (g : E) : Bornology.IsVonNBounded ℂ (range fun x : K ↦ A x g) := by
    have hc : Continuous (fun x : K ↦ T g x.val) := (T g).continuous.comp continuous_subtype_val
    simpa only [A, hL] using (isCompact_range hc).isVonNBounded ℂ
  have he := (PolynormableSpace.banach_steinhaus hbound).equicontinuous f
  intro u hu
  filter_upwards [he u hu] with g hg
  intro x hx
  simpa only [Function.comp_apply, A, hL] using hg (⟨x, hx⟩ : K)

end RiemannMasullo
