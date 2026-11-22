module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Montel
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.Ascoli
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual

/-! # Compactness and convergence detected by separating coordinates -/

noncomputable section

open Bornology Filter Function MeasureTheory Set Topology

namespace RiemannMasullo

/-- On a compact subset of a function space a continuous family of separating evaluations
detects convergence, even if the evaluations do not generate the topology globally. -/
private theorem tendsto_of_compact_evaluations {E X I : Type*} [TopologicalSpace E]
    (ev : E → X → ℂ) (hev : Continuous ev) (hinj : Injective ev)
    {K : Set E} (hK : IsCompact K) {l : Filter I} {f : I → E} {a : E}
    (hf : ∀ i, f i ∈ K) (ha : a ∈ K) (h : ∀ x, Tendsto (fun i ↦ ev (f i) x) l (𝓝 (ev a x))) :
    Tendsto f l (𝓝 a) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j (x : K) := ev x.val
  have hj := (hev.comp (continuous_subtype_val (p := (· ∈ K)))).isClosedEmbedding
    (hinj.comp Subtype.val_injective)
  let g (i : I) : K := ⟨f i, hf i⟩
  have hg : Tendsto g l (𝓝 ⟨a,ha⟩) := hj.isEmbedding.isInducing.tendsto_nhds_iff.mpr
    (tendsto_pi_nhds.mpr h)
  exact (continuous_subtype_val.tendsto _).comp hg

/-- Banach–Steinhaus and compactness turn convergence on separating coordinates of
a pointwise bounded operator family into uniform convergence on bounded sets. -/
private theorem uniformOn_montel_of_evaluations {E X I : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [MontelSpace ℂ E] [BarrelledSpace ℂ E] (l : Filter I)
    (ev : E → X → ℂ) (hev : Continuous ev) (hinj : Injective ev)
    (Q : I → E →L[ℂ] E) (D : E → E) (hb : ∀ f, IsVonNBounded ℂ (range fun i ↦ Q i f))
    (h : ∀ f x, Tendsto (fun i ↦ ev (Q i f) x) l (𝓝 (ev (D f) x)))
    (B : Set E) (hB : IsVonNBounded ℂ B) : TendstoUniformlyOn (fun i f ↦ Q i f) D l B := by
  have hpt (f : E) : Tendsto (fun i ↦ Q i f) l (𝓝 (D f)) := by
    let S := closure (insert (D f) (range fun i ↦ Q i f))
    have hS : IsCompact S := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ
      isClosed_closure ((hb f).insert _).closure
    exact tendsto_of_compact_evaluations ev hev hinj hS (fun i ↦ subset_closure
      (mem_insert_of_mem _ (mem_range_self i))) (subset_closure (mem_insert _ _)) (h f)
  let K := closure B
  have hK : IsCompact K := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure hB.closure
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G (i : I) (f : K) := Q i f.val
  have hEq : Equicontinuous (fun i f ↦ Q i f) := (PolynormableSpace.banach_steinhaus (𝓕 := Q) hb).equicontinuous
  have hr : Equicontinuous G := (equicontinuous_restrict_iff _).mpr (hEq.equicontinuousOn K)
  have hu : TendstoUniformly G (fun f ↦ D f.val) l := UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hr.tendsto_uniformFun_iff_pi l _).mpr (tendsto_pi_nhds.mpr fun f ↦ hpt f.val))
  intro V hV
  filter_upwards [hu V hV] with i hi f hf
  exact hi ⟨f, subset_closure hf⟩

/-- Pointwise boundedness and convergence of evaluations may be checked on any
eventual set of parameters. -/
public theorem uniformOn_montel_of_evaluations_near {E X I : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [MontelSpace ℂ E] [BarrelledSpace ℂ E] (l : Filter I)
    (ev : E → X → ℂ) (hev : Continuous ev) (hinj : Injective ev)
    (Q : I → E →L[ℂ] E) (D : E → E) {S : Set I} (hS : S ∈ l)
    (hb : ∀ f, IsVonNBounded ℂ ((fun i ↦ Q i f) '' S))
    (h : ∀ f x, Tendsto (fun i ↦ ev (Q i f) x) l (𝓝 (ev (D f) x)))
    (B : Set E) (hB : IsVonNBounded ℂ B) : TendstoUniformlyOn (fun i f ↦ Q i f) D l B := by
  classical
  let T (i : I) : E →L[ℂ] E := if i ∈ S then Q i else 0
  have hT (f : E) : IsVonNBounded ℂ (range fun i ↦ T i f) := by
    apply IsVonNBounded.subset _ ((hb f).insert 0)
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ S
    · exact mem_insert_of_mem _ ⟨i, hi, by simp [T,hi]⟩
    · simp [T,hi]
  have heq : ∀ᶠ i in l, T i = Q i :=
    (show ∀ᶠ i in l, i ∈ S from hS).mono fun i hi ↦ ite_eq_left hi
  exact (uniformOn_montel_of_evaluations l ev hev hinj T D hT
    (fun f x ↦ (h f x).congr' (heq.mono fun i hi ↦ congrArg (fun L : E →L[ℂ] E ↦ ev (L f) x) hi.symm))
    B hB).congr (heq.mono fun i hi f _ ↦ DFunLike.congr_fun hi f)

/-- A compact convex set containing the coordinatewise velocity on a unit interval
contains the increment. Finite coordinate projections reduce this to vector integration. -/
private theorem sub_mem_of_coordinate_derivatives
    {E X : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (ev : X → E →L[ℝ] ℂ) (hsep : ∀ a b : E, (∀ x, ev x a = ev x b) → a = b)
    {K : Set E} (hK : IsCompact K) (hcv : Convex ℝ K) (a d : ℝ → E)
    (hd : ∀ x, Continuous fun s ↦ ev x (d s))
    (ha : ∀ x s, HasDerivAt (fun t ↦ ev x (a t)) (ev x (d s)) s)
    (hmem : ∀ s ∈ Icc (0 : ℝ) 1, d s ∈ K) : a 1 - a 0 ∈ K := by
  classical
  let S (x : X) := {w : E | ev x w = ev x (a 1 - a 0)}
  have hS (x) : IsClosed (S x) := isClosed_eq (ev x).continuous continuous_const
  have hfin (u : Finset X) : (K ∩ ⋂ x ∈ u, S x).Nonempty := by
    let L : E →L[ℝ] (u → ℂ) := ContinuousLinearMap.pi fun i ↦ ev i.val
    have hh : Continuous (fun s ↦ L (d s)) := continuous_pi fun i ↦ hd i.val
    have hder (s : ℝ) : HasDerivAt (fun t ↦ L (a t)) (L (d s)) s :=
      hasDerivAt_pi.mpr (fun i ↦ ha i.val s)
    let μ := volume.restrict (Ioc (0 : ℝ) 1)
    let : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
    have hint : (∫ s, L (d s) ∂μ) ∈ L '' K := (hcv.linear_image L.toLinearMap).integral_mem
      (hK.image L.continuous).isClosed ((ae_restrict_mem measurableSet_Ioc).mono
        fun s hs ↦ mem_image_of_mem L (hmem s ⟨hs.1.le, hs.2⟩)) (hh.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun s _ ↦ hder s) (hh.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one] at heq
    change (∫ s, L (d s) ∂μ) = _ at heq
    rw [heq, ← map_sub] at hint
    obtain ⟨w, hw, hwe⟩ := hint
    exact ⟨w, hw, mem_iInter₂.mpr fun x hx ↦ congrFun hwe ⟨x,hx⟩⟩
  obtain ⟨w, hw, hwe⟩ := hK.inter_iInter_nonempty S hS hfin
  exact hsep w _ (fun x ↦ mem_iInter.mp hwe x) ▸ hw

open scoped Pointwise ComplexOrder in
/-- Compactness of the translated velocities controls all normalized increments
with bounded step and bounded change of parameter. -/
public theorem exists_compact_slopes_of_velocity {E X : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [MontelSpace ℂ E] (ev : X → E →L[ℂ] ℂ)
    (hsep : ∀ a b, (∀ x, ev x a = ev x b) → a = b) (a d : ℝ → E)
    (hd : ∀ x, Continuous fun r ↦ ev x (d r))
    (ha : ∀ x r, HasDerivAt (fun t ↦ ev x (a t)) (ev x (d r)) r)
    (hb : IsVonNBounded ℂ (d '' Icc (-1 : ℝ) 1)) :
    ∃ C : Set E, IsCompact C ∧ 0 ∈ C ∧
      ∀ s δ : ℝ, |s| ≤ 1 → |s / δ| ≤ 2 → (δ : ℂ)⁻¹ • (a s - a 0) ∈ C := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  obtain ⟨K, hK, _, hSK⟩ := exists_compact_absConvex_superset hb
  let J := Metric.closedBall (0 : ℂ) 2 • K
  have hJ : IsCompact J := (isCompact_closedBall (0 : ℂ) 2).smul_set hK
  obtain ⟨C, hC, hcv, hJC⟩ := exists_compact_absConvex_superset (hJ.isVonNBounded ℂ)
  refine ⟨C, hC, hJC (mem_insert _ _), fun s δ hs hδ ↦ ?_⟩
  let c : ℂ := (δ : ℂ)⁻¹
  let b : ℂ := (s / δ : ℝ)
  let A (r : ℝ) := c • a (r * s)
  let D (r : ℝ) := b • d (r * s)
  let v (x : X) := (ev x).restrictScalars ℝ
  have hd' (x) : Continuous (fun t ↦ v x (D t)) := by
    change Continuous fun t ↦ ev x (b • d (t * s))
    simp only [map_smul, smul_eq_mul]
    exact continuous_const.mul ((hd x).comp (continuous_id.mul continuous_const))
  have ha' (x r) : HasDerivAt (fun t ↦ v x (A t)) (v x (D r)) r := by
    change HasDerivAt (fun t : ℝ ↦ ev x (c • a (t*s))) (ev x (b • d (r*s))) r
    simp only [map_smul, smul_eq_mul]
    have h := ((ha x (r*s)).scomp r ((hasDerivAt_id r).mul_const s)).const_mul c
    simpa only [Function.comp_def, id_eq, one_mul, Complex.real_smul, b, c, Complex.ofReal_div,
      div_eq_mul_inv, mul_left_comm, mul_assoc] using h
  have hmem (r : ℝ) (hr : r ∈ Icc 0 1) : D r ∈ C := by
    have hrs : r * s ∈ Icc (-1 : ℝ) 1 := abs_le.mp (by
      rw [abs_mul, abs_of_nonneg hr.1]
      exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg s)).trans ((one_mul _).le.trans hs))
    have hb : b ∈ Metric.closedBall (0 : ℂ) 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, b, Complex.norm_real, Real.norm_eq_abs] using hδ
    exact hJC (mem_insert_of_mem _ ⟨b, hb, d (r*s), hSK (mem_insert_of_mem _ (mem_image_of_mem _ hrs)), rfl⟩)
  have h := sub_mem_of_coordinate_derivatives v hsep hC (hcv.2.lift ℝ) A D hd' ha' hmem
  simpa only [A, one_mul, zero_mul, smul_sub, c] using h

end RiemannMasullo

public section

open Bornology Filter Function Set Topology

namespace RiemannMasullo

/-- The inverse of a continuous linear bijection from a Montel space is sequentially
continuous when it takes bounded sets to bounded sets. On the compact closure of each
lifted sequence, the comparison is a topological embedding. -/
theorem seqContinuous_symm_of_bounded_comparison {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul 𝕜 X] [T2Space X] [MontelSpace 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul 𝕜 Y] [T2Space Y]
    (C : X ≃ₗ[𝕜] Y) (hc : Continuous C)
    (hb : ∀ B : Set X, IsVonNBounded 𝕜 (C '' B) → IsVonNBounded 𝕜 B) :
    SeqContinuous C.symm := by
  intro u y hu
  let B := closure (insert (C.symm y) (range (fun n ↦ C.symm (u n))))
  have hIm : C '' (insert (C.symm y) (range (fun n ↦ C.symm (u n)))) = insert y (range u) := by
    rw [image_insert_eq, ← range_comp]
    simp [Function.comp_def]
  have hB : IsVonNBounded 𝕜 B := (hb _ (hIm ▸ (hu.isVonNBounded_range 𝕜).insert y)).closure
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure hB)
  let F (z : B) := C z.val
  have he := (hc.comp (continuous_subtype_val (p := (· ∈ B)))).isClosedEmbedding
    (C.injective.comp Subtype.val_injective)
  let v (n : ℕ) : B := ⟨C.symm (u n), subset_closure (mem_insert_of_mem _ (mem_range_self n))⟩
  let z : B := ⟨C.symm y, subset_closure (mem_insert _ _)⟩
  have hF : F ∘ v = u := funext fun n ↦ C.apply_symm_apply (u n)
  have ht : Tendsto v atTop (𝓝 z) := he.isInducing.tendsto_nhds_iff.mpr
    (Eq.mpr (congrArg₂ (fun a b ↦ Tendsto a atTop (𝓝 b)) hF (C.apply_symm_apply y)) hu)
  exact continuous_subtype_val.continuousAt.tendsto.comp ht

end RiemannMasullo
