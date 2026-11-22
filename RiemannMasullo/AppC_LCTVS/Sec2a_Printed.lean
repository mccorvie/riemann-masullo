module

public import RiemannMasullo.AppC_LCTVS.Sec2a
import all RiemannMasullo.AppC_LCTVS.Sec2a
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach

/-! # Appendix C.2.2: the printed criterion for equality of the dual topologies -/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Paper: §C.2.2.2, p. 674. As printed: on the continuous dual of a Hausdorff
locally convex complex space E, the strong and Mackey topologies agree exactly when
E is barrelled. `strongDualityTopology_le_mackeyTopology` gives the comparison
that holds for every separating duality. See ERRATA F5. -/
def Printed.strongDualityTopology_eq_mackeyTopology_iff_barrelled : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E],
    strongDualityTopology (topDualPairing ℂ E) = mackeyTopology (topDualPairing ℂ E) ↔
      BarrelledSpace ℂ E

open Set Filter Topology Bornology
open scoped UniformConvergence Pointwise ComplexOrder

/-- Builds an element of `C₀(ℕ, ℂ)` from a sequence vanishing beyond `N`. -/
private def c0mk (g : ℕ → ℂ) (N : ℕ) (hg : ∀ i, N ≤ i → g i = 0) :
    ZeroAtInftyContinuousMap ℕ ℂ :=
  ⟨⟨g, continuous_of_discreteTopology⟩, by
    change Tendsto g (cocompact ℕ) (𝓝 0)
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun i hi ↦ (hg i hi).symm⟩)⟩

/-- The unit vectors of `c₀`. -/
private def c0e (n : ℕ) : ZeroAtInftyContinuousMap ℕ ℂ :=
  c0mk (fun i ↦ if i = n then 1 else 0) (n + 1) fun i hi ↦ ite_eq_right (by omega)

/-- The truncated vector with coefficients `c` below `N`. -/
private def c0v (c : ℕ → ℂ) (N : ℕ) : ZeroAtInftyContinuousMap ℕ ℂ :=
  c0mk (fun i ↦ if i < N then c i else 0) N fun i hi ↦ ite_eq_right (by omega)

private theorem c0v_apply_eq (f : ZeroAtInftyContinuousMap ℕ ℂ →L[ℂ] ℂ) (c : ℕ → ℂ) (N : ℕ) :
    f (c0v c N) = ∑ i ∈ Finset.range N, c i * f (c0e i) := by
  induction N with
  | zero =>
    have : c0v c 0 = 0 := by ext j; simp [c0v, c0mk]
    simp [this]
  | succ N ih =>
    have : c0v c (N + 1) = c0v c N + c N • c0e N := by
      ext j
      simp only [add_apply, smul_apply]
      change (if j < N + 1 then c j else 0) = (if j < N then c j else 0) +
        c N • (if j = N then 1 else 0)
      rcases lt_trichotomy j N with h | h | h
      · simp [h, h.ne, show j < N + 1 by omega]
      · subst h; simp
      · simp [show ¬ j < N + 1 by omega, show ¬ j < N by omega, h.ne']
    rw [this, map_add, map_smul, ih, Finset.sum_range_succ, smul_eq_mul]

private theorem c0_sum_norm_le (f : ZeroAtInftyContinuousMap ℕ ℂ →L[ℂ] ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, ‖f (c0e i)‖ ≤ ‖f‖ := by
  let c : ℕ → ℂ := fun i ↦ if f (c0e i) = 0 then 0 else (‖f (c0e i)‖ : ℂ) / f (c0e i)
  have hc (i : ℕ) : c i * f (c0e i) = (‖f (c0e i)‖ : ℂ) := by
    by_cases h : f (c0e i) = 0
    · simp [c, h]
    · simp only [c, ite_eq_right h]
      field_simp
  have hcn (i : ℕ) : ‖c i‖ ≤ 1 := by
    by_cases h : f (c0e i) = 0
    · simp [c, h]
    · simp only [c, ite_eq_right h, norm_div, Complex.norm_real, norm_norm]
      rw [div_self (norm_ne_zero_iff.mpr h)]
  have hv : ‖c0v c N‖ ≤ 1 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le zero_le_one).mpr fun j ↦ ?_
    change ‖(if j < N then c j else 0)‖ ≤ 1
    split_ifs
    · exact hcn j
    · simp
  have h1 : ((∑ i ∈ Finset.range N, ‖f (c0e i)‖ : ℝ) : ℂ) = f (c0v c N) := by
    rw [c0v_apply_eq]; push_cast; simp [hc]
  calc ∑ i ∈ Finset.range N, ‖f (c0e i)‖
      = ‖((∑ i ∈ Finset.range N, ‖f (c0e i)‖ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    _ = ‖f (c0v c N)‖ := by rw [h1]
    _ ≤ ‖f‖ * ‖c0v c N‖ := f.le_opNorm _
    _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg _) hv

private theorem c0_summable_norm (f : ZeroAtInftyContinuousMap ℕ ℂ →L[ℂ] ℂ) :
    Summable fun i ↦ ‖f (c0e i)‖ :=
  summable_of_sum_range_le (fun _ ↦ norm_nonneg _) (c0_sum_norm_le f)

private theorem c0_summable (f : ZeroAtInftyContinuousMap ℕ ℂ →L[ℂ] ℂ) :
    Summable fun i ↦ f (c0e i) :=
  Summable.of_norm (c0_summable_norm f)

/-- The functional `f ↦ ∑ f(eₙ)` on the dual of `c₀`, represented by the constant sequence 1. -/
private def c0Phi : (ZeroAtInftyContinuousMap ℕ ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∑' i, f (c0e i)
      map_add' := fun f g ↦ by
        simp only [add_apply]
        exact (c0_summable f).tsum_add (c0_summable g)
      map_smul' := fun a f ↦ by
        simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
    1 fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      refine (norm_tsum_le_tsum_norm (c0_summable_norm f)).trans ?_
      exact (c0_summable_norm f).tsum_le_of_sum_range_le (c0_sum_norm_le f)

/-- Paper: §C.2.2.2, p. 674. Let E be the Banach space c₀ of complex sequences
tending to zero with the supremum norm. It is barrelled. On its dual ℓ¹ the strong
topology is the norm topology and the sum of all coordinates is a continuous functional.
It is represented by the constant sequence 1, which lies outside c₀. The continuous
dual for the Mackey topology of the pairing is c₀, so the topologies differ. -/
theorem Printed.strongDualityTopology_eq_mackeyTopology_iff_barrelled_false :
    ¬ Printed.strongDualityTopology_eq_mackeyTopology_iff_barrelled := by
  intro H
  let E := ZeroAtInftyContinuousMap ℕ ℂ
  let B := topDualPairing ℂ E
  have hbar : BarrelledSpace ℂ E := inferInstance
  have heq := (H E).mpr hbar
  have hsub : {A : Set E | IsVonNBounded ℂ A} ⊆
      {A | IsVonNBounded (E := WeakBilin B.flip) ℂ A} := by
    intro A hA
    have hcont : @Continuous E E _ (WeakBilin.instTopologicalSpace B.flip) id :=
      WeakBilin.continuous_of_continuous_eval B.flip fun f ↦ f.continuous
    exact IsVonNBounded.of_topologicalSpace_le (continuous_id_iff_le.mp hcont) hA
  have htop : (inferInstance : TopologicalSpace (E →L[ℂ] ℂ)) =
      TopologicalSpace.induced (UniformOnFun.ofFun {S : Set E | IsVonNBounded ℂ S} ∘ DFunLike.coe)
        (UniformOnFun.topologicalSpace E ℂ _) :=
    UniformConvergenceCLM.topologicalSpace_eq (RingHom.id ℂ) ℂ _
  have hle : strongDualityTopology B ≤ (inferInstance : TopologicalSpace (E →L[ℂ] ℂ)) := by
    rw [htop]
    exact induced_mono (UniformSpace.toTopologicalSpace_mono (UniformOnFun.mono le_rfl hsub))
  have hΦ : @Continuous _ _ (mackeyTopology B) _ (c0Phi : (E →L[ℂ] ℂ) → ℂ) := by
    rw [← heq]
    exact @Continuous.comp _ _ _ (strongDualityTopology B) _ _ _ _ c0Phi.continuous
      (continuous_id_iff_le.mpr hle)
  obtain ⟨x, hx⟩ := mem_range_flip_of_mackeyContinuous B (c0Phi : (E →L[ℂ] ℂ) →ₗ[ℂ] ℂ) hΦ
  have hone (n : ℕ) : x n = 1 := by
    let δ : E →L[ℂ] ℂ := LinearMap.mkContinuous
      { toFun := fun f ↦ f n
        map_add' := fun f g ↦ rfl
        map_smul' := fun a f ↦ rfl }
      1 fun f ↦ by
        rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF n
    have h1 : δ x = c0Phi δ := LinearMap.congr_fun hx δ
    have h2 : c0Phi δ = ∑' i, (if i = n then (1 : ℂ) else 0) := by
      change ∑' i, δ (c0e i) = _
      congr 1
      funext i
      change (if n = i then (1 : ℂ) else 0) = _
      by_cases h : i = n
      · simp [h]
      · simp [h, Ne.symm h]
    rw [h2, tsum_ite_eq] at h1
    exact h1
  have hx0 : Tendsto (fun n : ℕ ↦ x n) atTop (𝓝 0) := by
    have := x.zero_at_infty'
    rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at this
  simp only [hone] at hx0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hx0)

end RiemannMasullo
