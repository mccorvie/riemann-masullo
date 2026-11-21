module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Montel
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.Ascoli
public import RiemannMasullo.ForMathlib.Analysis.Normed.Module.WeakDual

/-! # Compactness in the strong dual of a Montel space -/

public section

namespace RiemannMasullo

open Bornology Filter Function Set Topology
open scoped CompactConvergenceCLM

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [MontelSpace ℂ E]

/-- The polar of a zero-neighborhood in a Montel space is compact in the strong dual. -/
theorem isCompact_strongDual_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (StrongDual.polar ℂ U) := by
  let A := WeakDual.polar ℂ U
  let f : A → E → ℂ := fun φ ↦ φ.val
  have hEq : Equicontinuous f := by
    apply equicontinuous_of_equicontinuousAt_zero
      (fun φ : A ↦ φ.val.toStrongDual.toAddMonoidHom)
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt ℂ hε
    filter_upwards [(set_smul_mem_nhds_zero_iff (norm_pos_iff.mp hc)).2 hU] with x hx φ
    obtain ⟨y, hy, rfl⟩ := hx
    change dist (φ.val 0) (φ.val.toStrongDual (c • y)) < ε
    rw [show φ.val 0 = 0 from map_zero φ.val.toStrongDual, dist_zero_left, map_smul, norm_smul]
    exact (mul_le_of_le_one_right hc.le (φ.property y hy)).trans_lt hcε
  have hweak : IsInducing f :=
    (show IsInducing (fun φ : WeakDual ℂ E ↦ (φ : E → ℂ)) from ⟨rfl⟩).comp
      IsInducing.subtypeVal
  let K : Set (Set E) := {s | IsCompact s}
  have hcompact : IsInducing (UniformOnFun.ofFun K ∘ f) :=
    (EquicontinuousOn.isInducing_uniformOnFun_iff_pi sUnion_isCompact_eq_univ
      (fun _ h ↦ h) (fun s _ ↦ hEq.equicontinuousOn s)).mpr hweak
  let e := ContinuousLinearEquiv.toCompactConvergenceCLM (RingHom.id ℂ) E ℂ
  have hcont : Continuous (fun φ : A ↦ e φ.val.toStrongDual) := by
    apply (UniformConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) ℂ K).isInducing.continuous_iff.mpr
    exact hcompact.continuous
  have himage : (fun φ : A ↦ φ.val.toStrongDual) '' univ = StrongDual.polar ℂ U := by
    ext φ
    constructor
    · rintro ⟨ψ, _, rfl⟩
      exact ψ.property
    · intro hφ
      exact ⟨⟨φ.toWeakDual, hφ⟩, mem_univ _, rfl⟩
  rw [← himage]
  let : CompactSpace A := isCompact_iff_compactSpace.mp (isCompact_weakDual_polar hU)
  exact isCompact_univ.image (e.symm.continuous.comp hcont)

/-- The strong dual of a barrelled Montel space has compact closed bounded subsets. -/
theorem montelSpace_strongDual [BarrelledSpace ℂ E] : MontelSpace ℂ (StrongDual ℂ E) := by
  refine ⟨fun S hclosed hS ↦ ?_⟩
  have hbounded (x : E) : IsVonNBounded ℂ (range fun φ : S ↦ φ.val x) := by
    let ev := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) x
    change IsVonNBounded ℂ (range (ev ∘ (Subtype.val : S → StrongDual ℂ E)))
    rw [range_comp, Subtype.range_coe]
    exact hS.image ev
  have hEq := (PolynormableSpace.banach_steinhaus hbounded).equicontinuous (0 : E)
  let U := {x : E | ∀ φ : S, dist (φ.val 0) (φ.val x) < 1}
  have hU : U ∈ 𝓝 (0 : E) := Metric.equicontinuousAt_iff_right.mp hEq 1 zero_lt_one
  apply (isCompact_strongDual_polar hU).of_isClosed_subset hclosed
  intro φ hφ x hx
  have h := hx ⟨φ, hφ⟩
  change ‖φ x‖ ≤ 1
  simpa only [map_zero, dist_zero_left] using h.le

end RiemannMasullo
