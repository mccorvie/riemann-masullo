module
public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual

/-! # Bounded convergence on the dual of a space with precompact bounded sets -/

public section

open Bornology Filter Function Set Topology
open scoped Uniformity
namespace RiemannMasullo

/-- Uniform equicontinuity upgrades pointwise continuity of a family to continuous
dependence in the topology of uniform convergence on totally bounded sets. -/
private theorem tendstoUniformlyOn_of_equicontinuous {X Y G : Type*} [UniformSpace X]
    [PseudoMetricSpace Y] [TopologicalSpace G] (f : G → X → Y) (he : UniformEquicontinuous f)
    (hc : ∀ x, Continuous fun i ↦ f i x) (g : G) (B : Set X) (hb : TotallyBounded B) :
    TendstoUniformlyOn f (f g) (𝓝 g) B := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hpos : 0 < ε / 3 := by positivity
  have hU := he {p : Y × Y | dist p.1 p.2 < ε / 3} (Metric.dist_mem_uniformity hpos)
  obtain ⟨D, hD, hcover⟩ := hb _ hU
  have hfinite : ∀ᶠ u in 𝓝 g, ∀ y ∈ D, dist (f g y) (f u y) < ε / 3 :=
    (eventually_all_finite hD).mpr fun y _ ↦ (Metric.tendsto_nhds.mp (hc y).continuousAt _
      hpos).mono fun u h ↦ (dist_comm _ _).trans_lt h
  filter_upwards [hfinite] with u hu x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hg : dist (f g x) (f g y) < ε / 3 := hxy g
  have ht : dist (f u x) (f u y) < ε / 3 := hxy u
  calc
    _ ≤ dist (f g x) (f g y) + dist (f g y) (f u y) + dist (f u y) (f u x) :=
      dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (f u y) (f u x)]; linarith [hu y hy]

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E]

/-- If bounded sets are totally bounded, the polar of a zero-neighborhood is strongly
compact. Finite nets give uniform convergence even when the domain is incomplete. -/
theorem isCompact_strongDual_polar_of_precompact
    (hpre : ∀ B : Set E, IsVonNBounded ℂ B → TotallyBounded B)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) : IsCompact (StrongDual.polar ℂ U) := by
  let A := WeakDual.polar ℂ U
  let f : A → E → ℂ := fun φ ↦ φ.val
  have he : UniformEquicontinuous f := by
    apply uniformEquicontinuous_of_equicontinuousAt_zero
      (fun φ : A ↦ φ.val.toStrongDual.toAddMonoidHom)
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt ℂ hε
    filter_upwards [(set_smul_mem_nhds_zero_iff (norm_pos_iff.mp hc)).2 hU] with x hx φ
    obtain ⟨y, hy, rfl⟩ := hx
    change dist (φ.val 0) (φ.val.toStrongDual (c • y)) < ε
    rw [show φ.val 0 = 0 from map_zero φ.val.toStrongDual, dist_zero_left, map_smul, norm_smul]
    exact (mul_le_of_le_one_right hc.le (φ.property y hy)).trans_lt hcε
  have hcont : Continuous (fun φ : A ↦ φ.val.toStrongDual) := by
    refine continuous_iff_continuousAt.mpr fun φ ↦ ?_
    apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ
      {B : Set E | IsVonNBounded ℂ B}).mpr
    exact fun B hb ↦ tendstoUniformlyOn_of_equicontinuous f he
      (fun x ↦ (WeakBilin.eval_continuous (topDualPairing ℂ E) x).comp continuous_subtype_val)
      φ B (hpre B hb)
  let : CompactSpace A := isCompact_iff_compactSpace.mp (isCompact_weakDual_polar hU)
  have himage : range (fun φ : A ↦ φ.val.toStrongDual) = StrongDual.polar ℂ U := by
    ext φ
    exact ⟨fun ⟨ψ,hψ⟩ ↦ hψ ▸ ψ.property, fun hφ ↦ ⟨⟨φ.toWeakDual,hφ⟩,rfl⟩⟩
  exact himage ▸ isCompact_range hcont

/-- A pointwise bounded subset of the dual of a barrelled space with precompact
bounded sets has strongly compact closure. -/
theorem isCompact_closure_strongDual_of_pointwise_bounded [BarrelledSpace ℂ E]
    (hpre : ∀ B : Set E, IsVonNBounded ℂ B → TotallyBounded B) (S : Set (StrongDual ℂ E))
    (hbounded : ∀ x : E, IsVonNBounded ℂ (range fun φ : S ↦ φ.val x)) :
    IsCompact (closure S) := by
  have hEq := (PolynormableSpace.banach_steinhaus hbounded).equicontinuous (0 : E)
  let U := {x : E | ∀ φ : S, dist (φ.val 0) (φ.val x) < 1}
  have hU : U ∈ 𝓝 (0 : E) := Metric.equicontinuousAt_iff_right.mp hEq 1 zero_lt_one
  have hk := isCompact_strongDual_polar_of_precompact hpre hU
  apply hk.of_isClosed_subset isClosed_closure (closure_minimal ?_ hk.isClosed)
  intro φ hφ x hx
  have h := hx ⟨φ, hφ⟩
  change ‖φ x‖ ≤ 1
  simpa only [map_zero, dist_zero_left] using h.le

/-- The strong dual of a barrelled space in which bounded sets are precompact has
compact closed bounded subsets. -/
theorem montelSpace_strongDual_of_precompact [BarrelledSpace ℂ E]
    (hpre : ∀ B : Set E, IsVonNBounded ℂ B → TotallyBounded B) : MontelSpace ℂ (StrongDual ℂ E) := by
  refine ⟨fun S hclosed hS ↦ ?_⟩
  have hbounded (x : E) : IsVonNBounded ℂ (range fun φ : S ↦ φ.val x) := by
    let ev := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) x
    change IsVonNBounded ℂ (range (ev ∘ (Subtype.val : S → StrongDual ℂ E)))
    rw [range_comp, Subtype.range_coe]
    exact hS.image ev
  exact hclosed.closure_eq ▸ isCompact_closure_strongDual_of_pointwise_bounded hpre S hbounded

/-- A quotient transpose embeds every family whose image is strongly bounded, when
bounded subsets of the barrelled quotient are precompact. -/
theorem isEmbedding_transpose_of_bounded_image {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [BarrelledSpace ℂ E]
    (q : X →L[ℂ] E) (hq : Surjective q)
    (hpre : ∀ B : Set E, IsVonNBounded ℂ B → TotallyBounded B) (S : Set (StrongDual ℂ E))
    (hb : IsVonNBounded ℂ ((fun l : StrongDual ℂ E ↦ l.comp q) '' S)) :
    IsEmbedding (fun l : S ↦ l.val.comp q) := by
  let R : StrongDual ℂ E →L[ℂ] StrongDual ℂ X := ContinuousLinearMap.precomp ℂ q
  have hi : Injective R := fun l m h ↦ ContinuousLinearMap.ext fun y ↦
    (hq y).elim fun x hx ↦ hx ▸ DFunLike.congr_fun h x
  have hbounded (y : E) : IsVonNBounded ℂ (range fun l : S ↦ l.val y) := by
    obtain ⟨x, rfl⟩ := hq y
    let e := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) x
    have h := hb.image e
    have heq : range (fun l : S ↦ l.val (q x)) = e '' (R '' S) :=
      (image_eq_range (fun l : StrongDual ℂ E ↦ l (q x)) S).symm.trans (image_image e R S).symm
    exact heq ▸ h
  let K := closure S
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_closure_strongDual_of_pointwise_bounded hpre S hbounded)
  have he := (R.continuous.comp (continuous_subtype_val (p := (· ∈ K)))).isClosedEmbedding
    (hi.comp Subtype.val_injective)
  exact he.isEmbedding.comp (IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal :
    IsEmbedding (Set.inclusion (subset_closure : S ⊆ K)))

end RiemannMasullo
