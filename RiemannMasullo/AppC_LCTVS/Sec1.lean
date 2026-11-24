module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Algebra.Module.ULift
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Montel
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WithSeminorms
public import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.Quotient
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.WeakDual
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Pointwise
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import RiemannMasullo.ForMathlib.Topology.Maps.Strict.Module
import RiemannMasullo.ForMathlib.Topology.MetricSpace.CompactQuotient

/-!
# Locally convex topological vector spaces

Masullo, Appendix C, §C.1. The scalars are complex unless the paper specifies real scalars.
We use `PolynormableSpace ℂ E` for the characterization of local convexity by continuous
complex seminorms (§C.1.2.1). Boundedness is von Neumann boundedness.

The elementary notions on pp. 657–658 are Mathlib's `Convex ℝ`, `Balanced ℂ`,
`Absorbent ℂ`, convex and balanced hulls, their closures, and the Minkowski functional `gauge`.
-/

@[expose] public noncomputable section

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum

namespace RiemannMasullo

universe u

/-- Paper: Remark C.1.1.1, p. 657. A circled set is stable under each complex scalar
in the closed unit disc. -/
theorem balanced_iff_closedUnitDisc {E : Type*} [AddCommGroup E] [Module ℂ E] (A : Set E) :
    Balanced ℂ A ↔ ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ x ∈ A, z • x ∈ A :=
  balanced_iff_smul_mem

/-- Paper: Remark C.1.1.2, p. 658. The balanced hull of the closed real hyperbola
has just the origin on the axes, whereas its closure contains both axes. -/
theorem balancedHull_hyperbola :
    let A : Set (ℝ × ℝ) := {p | p.1 * p.2 = 1}
    balancedHull ℝ (closure A) = balancedHull ℝ A ∧
      balancedHull ℝ A = {p | 0 < p.1 * p.2 ∧ p.1 * p.2 ≤ 1} ∪ {0} ∧
      closure (balancedHull ℝ A) = {p | 0 ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ 1} := by
  intro A
  have hmul : Continuous (fun p : ℝ × ℝ ↦ p.1 * p.2) := continuous_fst.mul continuous_snd
  have hA : IsClosed A := isClosed_eq hmul continuous_const
  let B : Set (ℝ × ℝ) := {p | 0 < p.1 * p.2 ∧ p.1 * p.2 ≤ 1} ∪ {0}
  have hHull : balancedHull ℝ A = B := by
    ext p
    rw [mem_balancedHull_iff]
    constructor
    · rintro ⟨r, hr, q, hq, rfl⟩
      obtain rfl | hr₀ := eq_or_ne r 0
      · exact Or.inr (zero_smul ℝ q)
      · change q.1 * q.2 = 1 at hq
        have hprod : (r • q).1 * (r • q).2 = r ^ 2 := by
          change (r * q.1) * (r * q.2) = r ^ 2
          rw [mul_mul_mul_comm, hq, mul_one, pow_two]
        refine Or.inl ⟨hprod ▸ ?_, ?_⟩
        · exact sq_pos_of_ne_zero hr₀
        · rw [hprod, sq_le_one_iff_abs_le_one]
          exact hr
    · rintro (⟨hp, hp'⟩ | hp)
      · -- Rescale the point by the inverse square root of its coordinate product.
        let r := Real.sqrt (p.1 * p.2)
        have hr : 0 < r := Real.sqrt_pos.2 hp
        have hr_sq : r ^ 2 = p.1 * p.2 := Real.sq_sqrt hp.le
        refine ⟨r, ?_, r⁻¹ • p, ?_, smul_inv_smul₀ hr.ne' p⟩
        · rw [Real.norm_eq_abs, abs_of_pos hr]
          exact Real.sqrt_le_one.2 hp'
        · change (r⁻¹ * p.1) * (r⁻¹ * p.2) = 1
          rw [mul_mul_mul_comm, ← pow_two, inv_pow, hr_sq, inv_mul_cancel₀ hp.ne']
      · rw [mem_singleton_iff] at hp
        subst p
        refine ⟨0, by simp, (1, 1), ?_, zero_smul ℝ _⟩
        change (1 : ℝ) * 1 = 1
        exact one_mul 1
  refine ⟨by rw [hA.closure_eq], hHull, ?_⟩
  rw [hHull]
  apply Subset.antisymm
  · apply closure_minimal _ (isClosed_Icc.preimage hmul)
    rintro p (⟨hp, hp'⟩ | hp)
    · exact ⟨hp.le, hp'⟩
    · rw [mem_singleton_iff] at hp
      subst p
      exact ⟨by simp, by simp⟩
  · rintro ⟨x, y⟩ ⟨hxy, hxy'⟩
    obtain hxy | hxy := hxy.eq_or_lt
    · -- Approach each nonzero axis point along a path with coordinate product t.
      have hzero : (0 : ℝ) ∈ closure (Ioc 0 1) := by
        rw [closure_Ioc zero_ne_one]
        exact ⟨le_rfl, zero_le_one⟩
      have approach (f : ℝ → ℝ × ℝ) (hf : Continuous f)
          (hprod : ∀ t, (f t).1 * (f t).2 = t) : f 0 ∈ closure B := by
        have hmaps : MapsTo f (Ioc 0 1) B := fun t ht ↦
          Or.inl ⟨(hprod t).symm ▸ ht.1, (hprod t).symm ▸ ht.2⟩
        exact hmaps.closure hf hzero
      by_cases hx : x = 0
      · subst x
        by_cases hy : y = 0
        · subst y
          exact subset_closure (Or.inr rfl)
        · simpa only [zero_div] using
            approach (fun t ↦ (t / y, y)) ((continuous_id.div_const y).prodMk continuous_const)
              (fun t ↦ div_mul_cancel₀ t hy)
      · have hy : y = 0 := (mul_eq_zero.mp hxy.symm).resolve_left hx
        subst y
        simpa only [zero_div] using
          approach (fun t ↦ (x, t / x)) (continuous_const.prodMk (continuous_id.div_const x))
            (fun t ↦ (mul_div_assoc x t x).symm.trans (mul_div_cancel_left₀ t hx))
    · exact subset_closure (Or.inl ⟨hxy, hxy'⟩)

/-- Paper: Remark C.1.2.1, p. 658. The uniformity of a uniform additive group is the
canonical additive uniformity of its topology. -/
theorem uniformSpace_eq_additiveUniformity (E : Type*) [AddCommGroup E] [uE : UniformSpace E]
    [IsUniformAddGroup E] : uE = IsTopologicalAddGroup.rightUniformSpace E :=
  IsUniformAddGroup.rightUniformSpace_eq.symm

/-- Paper: §C.1.2.1, p. 658. In a topology defined by seminorms, positive integer
rescalings of finite intersections of their closed unit balls give a basis at zero.
The topology is Hausdorff exactly when the common kernel is zero. -/
theorem seminorms_nhds_basis_and_hausdorff {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (p : SeminormFamily ℂ E ι) (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun a : Finset ι × ℕ ↦ 0 < a.2)
      (fun a ↦ {x | ∀ i ∈ a.1, p i x ≤ (a.2 : ℝ)⁻¹}) ∧
      (T2Space E ↔ ∀ x : E, (∀ i, p i x = 0) → x = 0) := by
  constructor
  · refine hp.hasBasis_zero_ball.to_hasBasis ?_ ?_
    · rintro ⟨s, r⟩ hr
      obtain ⟨n, hn, hnr⟩ := Real.exists_nat_pos_inv_lt hr
      refine ⟨(s, n), hn, ?_⟩
      rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
      intro x hx
      simp only [mem_iInter₂, Seminorm.mem_ball_zero]
      exact fun i hi ↦ (hx i hi).trans_lt hnr
    · rintro ⟨s, n⟩ hn
      have hr : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
      refine ⟨(s, (n : ℝ)⁻¹), hr, ?_⟩
      rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
      intro x hx i hi
      simp only [mem_iInter₂, Seminorm.mem_ball_zero] at hx
      exact (hx i hi).le
  · constructor
    · intro h x hx
      by_contra hne
      obtain ⟨i, hi⟩ := hp.separating_of_T1 x hne
      exact hi (hx i)
    · intro h
      have := hp.isTopologicalAddGroup
      have : T1Space E := hp.T1_of_separating (by
        intro x hx
        contrapose! hx
        exact h x hx)
      infer_instance

section Nets

variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J K : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  [Preorder K] [Nonempty K] [IsDirectedOrder K]

/-- Paper: Definition C.1.3.1(1–2), p. 659. A net is a function on a nonempty directed
preorder. It converges to a point exactly when its differences from that point are
eventually in every zero-neighborhood. -/
theorem tendsto_net_iff_sub_mem (f : J → E) (x : E) :
    Tendsto f atTop (𝓝 x) ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, x - f j ∈ U := by
  rw [← tendsto_const_sub_iff x, sub_self, tendsto_iff_forall_eventually_mem]
  simp only [eventually_atTop]

/-- Paper: Definition C.1.3.1(3), p. 659. A net is Cauchy when every zero-neighborhood
contains all pairwise differences on some tail. -/
theorem cauchySeq_iff_sub_mem (f : J → E) :
    CauchySeq f ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, ∀ k ≥ j₀, f j - f k ∈ U := by
  rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto, and_iff_right atTop_neBot,
    prod_atTop_atTop_eq, tendsto_iff_forall_eventually_mem]
  simp only [eventually_atTop_prod_self']

/-- Paper: Definition C.1.3.1(3), p. 659. Two Cauchy nets are equivalent when their
difference on the product directed set converges to zero. -/
def EquivalentCauchyNets (f : J → E) (g : K → E) : Prop :=
  CauchySeq f ∧ CauchySeq g ∧ Tendsto (fun p : J × K ↦ f p.1 - g p.2) atTop (𝓝 0)

/-- Paper: Definition C.1.3.1(3), p. 659. Two convergent nets in a Hausdorff space
are equivalent exactly when their limits coincide. -/
theorem equivalentCauchyNets_iff_of_tendsto [T2Space E] {f : J → E} {g : K → E} {x y : E}
    (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y)) :
    EquivalentCauchyNets f g ↔ x = y := by
  rw [EquivalentCauchyNets, ← prod_atTop_atTop_eq]
  have hsub : Tendsto (fun p : J × K ↦ f p.1 - g p.2) (atTop ×ˢ atTop) (𝓝 (x - y)) :=
    (hf.comp tendsto_fst).sub (hg.comp tendsto_snd)
  constructor
  · rintro ⟨_, _, hzero⟩
    exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)
  · rintro rfl
    exact ⟨hf.cauchy_map, hg.cauchy_map, by simpa only [sub_self] using hsub⟩

-- Retain the additive group instances in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Definition C.1.3.1(4), p. 659. For a Hausdorff subset, uniform completeness
means that every Cauchy net with values in it has a limit in it.
Deviation: Nets indexed in the universe of the ambient space suffice to test completeness. -/
theorem isComplete_iff_cauchyNets (A : Set E) [T2Space A] :
    IsComplete A ↔ ∀ (I : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
      (f : I → A), CauchySeq (fun i ↦ (f i : E)) →
        ∃ x ∈ A, Tendsto (fun i ↦ (f i : E)) atTop (𝓝 x) := by
  constructor
  · intro hA I _ _ _ f hf
    exact hA _ hf (tendsto_principal.mpr (Eventually.of_forall fun i ↦ (f i).property))
  · intro hA F hF hFA
    have : F.NeBot := hF.1
    have hmemA : A ∈ F := le_principal_iff.mp hFA
    -- Order pairs of a filter member and a point in it by reverse inclusion of the sets.
    let I := {p : Set E × A // p.1 ∈ F ∧ (p.2 : E) ∈ p.1}
    let _ : Preorder I := Preorder.lift fun i ↦ OrderDual.toDual i.1.1
    have exists_index (s : Set E) (hs : s ∈ F) : ∃ i : I, i.1.1 = s := by
      obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (inter_mem hs hmemA)
      exact ⟨⟨(s, ⟨x, hx.2⟩), hs, hx.1⟩, rfl⟩
    have : Nonempty I := (exists_index A hmemA).nonempty
    have : IsDirectedOrder I := ⟨fun i j ↦ by
      obtain ⟨k, hk⟩ := exists_index _ (inter_mem i.2.1 j.2.1)
      refine ⟨k, ?_⟩
      change k.1.1 ⊆ i.1.1 ∧ k.1.1 ⊆ j.1.1
      rw [hk]
      exact ⟨inter_subset_left, inter_subset_right⟩⟩
    let f (i : I) : A := i.1.2
    have hmap : map (fun i ↦ (f i : E)) atTop = F := by
      ext s
      change (∀ᶠ i in atTop, (f i : E) ∈ s) ↔ s ∈ F
      rw [eventually_atTop]
      constructor
      · rintro ⟨i, hi⟩
        refine mem_of_superset (inter_mem i.2.1 hmemA) fun x hx ↦ ?_
        exact hi ⟨(i.1.1, ⟨x, hx.2⟩), i.2.1, hx.1⟩ Subset.rfl
      · intro hs
        obtain ⟨i, rfl⟩ := exists_index s hs
        exact ⟨i, fun j hij ↦ (show j.1.1 ⊆ i.1.1 from hij) j.2.2⟩
    have hf : CauchySeq (fun i ↦ (f i : E)) := by
      rwa [CauchySeq, hmap]
    simpa only [Tendsto, hmap] using hA I f hf

end Nets

/-- Paper: Definition C.1.3.1(5), p. 659. A complex Fréchet space is locally convex,
metrizable, and complete for its additive uniformity. Metrizability includes Hausdorffness. -/
def IsFrechetTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  ∃ h : IsTopologicalAddGroup E, letI := h
    PolynormableSpace ℂ E ∧ MetrizableSpace E ∧
      @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)

/-- Paper: Definition C.1.3.1(5), p. 659. Every complex Banach space is Fréchet. -/
theorem isFrechetTVS_of_banach (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] : IsFrechetTVS E := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := E)]
  infer_instance

-- TODO(paper-gap): The reference for construction of the completion by Cauchy nets is “[?]”.

/-- Paper: Remark C.1.3.2, p. 659. Every Cauchy net has an equivalent net indexed by a
family of subsets of the space ordered by reverse inclusion. -/
theorem exists_equivalentCauchyNets_powerset {E J : Type*} [AddCommGroup E] [UniformSpace E]
    [IsUniformAddGroup E] [Preorder J] [Nonempty J] [IsDirectedOrder J] (f : J → E)
    (hf : CauchySeq f) :
    ∃ (S : Set (Set E)) (_ : Nonempty Sᵒᵈ) (_ : IsDirectedOrder Sᵒᵈ) (g : Sᵒᵈ → E),
      EquivalentCauchyNets f g := by
  classical
  let tail (j : J) : Set E := f '' Ici j
  let S := range tail
  let tailIndex (j : J) : Sᵒᵈ := OrderDual.toDual ⟨tail j, mem_range_self j⟩
  let : Nonempty Sᵒᵈ := ⟨tailIndex (Classical.choice ‹Nonempty J›)⟩
  let : IsDirectedOrder Sᵒᵈ := by
    constructor
    intro s t
    obtain ⟨j, hj⟩ := (OrderDual.ofDual s).2
    obtain ⟨k, hk⟩ := (OrderDual.ofDual t).2
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    refine ⟨tailIndex l, ?_, ?_⟩
    · change tail l ⊆ (OrderDual.ofDual s).1
      rw [← hj]
      exact image_mono (Ici_subset_Ici.mpr hjl)
    · change tail l ⊆ (OrderDual.ofDual t).1
      rw [← hk]
      exact image_mono (Ici_subset_Ici.mpr hkl)
  have hnonempty (s : Sᵒᵈ) : ((OrderDual.ofDual s).1 : Set E).Nonempty := by
    obtain ⟨j, hj⟩ := (OrderDual.ofDual s).2
    rw [← hj]
    exact ⟨f j, mem_image_of_mem f le_rfl⟩
  choose g hg using hnonempty
  have hsmallTail (U : Set E) (hU : U ∈ 𝓝 (0 : E)) :
      ∃ j, ∀ x ∈ tail j, ∀ y ∈ tail j, x - y ∈ U := by
    obtain ⟨j, hj⟩ := (cauchySeq_iff_sub_mem f).mp hf U hU
    refine ⟨j, ?_⟩
    rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact hj k hk l hl
  refine ⟨S, inferInstance, inferInstance, g, hf, ?_, ?_⟩
  · rw [cauchySeq_iff_sub_mem]
    intro U hU
    obtain ⟨j, hj⟩ := hsmallTail U hU
    exact ⟨tailIndex j, fun s hs t ht ↦ hj (g s) (hs (hg s)) (g t) (ht (hg t))⟩
  · rw [← prod_atTop_atTop_eq, tendsto_iff_forall_eventually_mem]
    intro U hU
    obtain ⟨j, hj⟩ := hsmallTail U hU
    refine ((eventually_ge_atTop j).prod_mk (eventually_ge_atTop (tailIndex j))).mono fun p hp ↦ ?_
    exact hj (f p.1) (mem_image_of_mem f hp.1) (g p.2) (hp.2 (hg p.2))

-- TODO(paper-gap): The arithmetic Schwartz–Bruhat spaces of Remark C.1.3.3 require Appendix D.

/-- Paper: Remark C.1.3.4, p. 660. The quotient of a Fréchet space by a closed linear
subspace is Fréchet in the quotient topology. -/
theorem isFrechetTVS_quotient {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (M : Submodule ℂ E) (hM : IsClosed (M : Set E)) :
    IsFrechetTVS (E ⧸ M) := by
  obtain ⟨hadd, hpoly, hmetr, hcomplete⟩ := hE
  have hzero : map M.mkQ (𝓝 (0 : E)) = 𝓝 0 := by
    simpa only [map_zero] using M.isOpenQuotientMap_mkQ.map_nhds_eq 0
  refine ⟨inferInstance, ?_, ?_, QuotientAddGroup.completeSpace_right' E M.toAddSubgroup⟩
  · exact polynormableSpace_quotient M
  · let : UniformSpace (E ⧸ M) := IsTopologicalAddGroup.rightUniformSpace (E ⧸ M)
    have : (𝓝 (0 : E ⧸ M)).IsCountablyGenerated :=
      hzero ▸ Filter.map.isCountablyGenerated (𝓝 (0 : E)) M.mkQ
    have : (uniformity (E ⧸ M)).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
    exact UniformSpace.metrizableSpace

section IncompleteQuotient

open scoped ENNReal ZeroAtInfty

-- The source pairs a product of null rows with a closed space of weighted tests.
-- Arbitrarily large weights detect a matrix with infinitely many nonzero rows.

local notation "Row" => ℕ → ℂ
local notation "NullRow" => C₀(ℕ, ℂ)
local notation "RowTests" => ((ℕ → ℂ) × (ℕ → ℕ)) → lp (fun _ : ℕ ↦ ℂ) ∞

/-- Evaluate a weighted row test at one row. -/
private def rowTestEntry (a : (ℕ → ℂ) × (ℕ → ℕ)) (i : ℕ) : RowTests →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) ∞ i).comp (ContinuousLinearMap.proj a)

/-- The compatible families of row tests. Each test reads column `a.2 i` in row `i`
and multiplies it by `a.1 i`. The unweighted constant-column tests recover the matrix. -/
private def compatibleRowTests : Submodule ℂ RowTests :=
  ⨅ a : (ℕ → ℂ) × (ℕ → ℕ), ⨅ i : ℕ,
    (rowTestEntry a i).eqLocus (a.1 i • rowTestEntry (1, fun _ ↦ a.2 i) i)

local notation "MatrixSource" => (ℕ → NullRow) × compatibleRowTests

/-- Compatibility is a closed condition on the tested entries. -/
private theorem isClosed_compatibleRowTests : IsClosed (compatibleRowTests : Set RowTests) := by
  simp only [compatibleRowTests, Submodule.coe_iInf]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun i ↦
    (rowTestEntry a i).isClosed_eqLocus (a.1 i • rowTestEntry (1, fun _ ↦ a.2 i) i)

/-- A compatible test is the corresponding weighted entry of the recovered matrix. -/
private theorem compatibleRowTests_entry (x : compatibleRowTests)
    (a : (ℕ → ℂ) × (ℕ → ℕ)) (i : ℕ) :
    x.val a i = a.1 i * x.val (1, fun _ ↦ a.2 i) i := by
  exact ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp x.property a)) i

/-- Insert one row into the family of weighted tests. -/
private def singleTestRow (i : ℕ) : Row →L[ℂ] compatibleRowTests := by
  let f : Row →L[ℂ] RowTests := ContinuousLinearMap.pi fun a ↦
    (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) ∞ i).comp
      (a.1 i • ContinuousLinearMap.proj (a.2 i))
  refine f.codRestrict _ fun r ↦ (Submodule.mem_iInf _).mpr fun a ↦
    (Submodule.mem_iInf _).mpr fun k ↦ ?_
  change lp.single (E := fun _ : ℕ ↦ ℂ) ∞ i (a.1 i * r (a.2 i)) k =
    a.1 k * lp.single (E := fun _ : ℕ ↦ ℂ) ∞ i (1 * r (a.2 k)) k
  by_cases h : k = i
  · subst k
    simp
  · simp [Pi.single_eq_of_ne h]

/-- Recover a matrix entry from the compatible tests. -/
private def testMatrixEntry (i j : ℕ) : compatibleRowTests →L[ℂ] ℂ :=
  (rowTestEntry (1, fun _ ↦ j) i).comp compatibleRowTests.subtypeL

/-- Insert the same row in every row with index below the cutoff. -/
private def initialTestRows (n : ℕ) : Row →L[ℂ] compatibleRowTests :=
  ∑ i ∈ Finset.range n, singleTestRow i

/-- Recovering an entry after the initial-row insertion gives the supplied row or zero. -/
private theorem testMatrixEntry_initialTestRows (m i j : ℕ) (r : Row) :
    testMatrixEntry i j (initialTestRows m r) = if i < m then r j else 0 := by
  classical
  simp only [initialTestRows, sum_apply, map_sum]
  have h (k : ℕ) : testMatrixEntry i j (singleTestRow k r) = if i = k then r j else 0 := by
    change lp.single (E := fun _ : ℕ ↦ ℂ) ∞ k (1 * r j) i = _
    by_cases h : i = k
    · subst k
      simp
    · simp [h]
  simp only [h]
  rw [Finset.sum_ite_eq]
  simp

/-- Recover the matrix formed by adding the null rows and the rows encoded by tests. -/
private def quotientMatrix :
    MatrixSource →L[ℂ] (ℕ → Row) := by
  let entry (i j : ℕ) : MatrixSource →L[ℂ] ℂ :=
    { toFun := fun x ↦ x.1 i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := (BoundedContinuousFunction.lipschitz_eval_const j).continuous.comp
        (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
          ((continuous_apply i).comp continuous_fst)) }
  exact ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦
    entry i j + (testMatrixEntry i j).comp (ContinuousLinearMap.snd ℂ _ _)

/-- A test family with a nonzero entry in every row would admit an unbounded test.
In particular, the constant-one matrix cannot be recovered from the source. -/
private theorem quotientMatrix_ne_one (x : MatrixSource) :
    quotientMatrix x ≠ (fun _ _ ↦ 1) := by
  intro hx
  have hrow (i : ℕ) : ∃ j, testMatrixEntry i j x.2 ≠ 0 := by
    by_contra! h
    have hconst (j : ℕ) : x.1 i j = 1 := by
      have hxij := congrFun (congrFun hx i) j
      change x.1 i j + testMatrixEntry i j x.2 = 1 at hxij
      simpa only [h j, add_zero] using hxij
    have hz := zero_at_infty (x.1 i)
    rw [show (⇑(x.1 i)) = (fun _ ↦ 1) from funext hconst] at hz
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hz)
  choose c hc using hrow
  let a : (ℕ → ℂ) × (ℕ → ℕ) := (fun i ↦ (i : ℂ) / testMatrixEntry i (c i) x.2, c)
  obtain ⟨i, hi⟩ := exists_nat_gt ‖x.2.val a‖
  have heq : x.2.val a i = (i : ℂ) := by
    rw [compatibleRowTests_entry]
    exact div_mul_cancel₀ _ (hc i)
  apply (not_lt_of_ge ?_) hi
  calc
    (i : ℝ) = ‖(i : ℂ)‖ := (Complex.norm_natCast i).symm
    _ = ‖x.2.val a i‖ := congrArg norm heq.symm
    _ ≤ ‖x.2.val a‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero (x.2.val a) i

/-- The first `n` entries of the constant-one row define a null row. -/
private def truncatedOneRow (n : ℕ) : NullRow where
  toFun j := if j < n then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro j hj
    simp [not_lt.mpr hj]

/-- The quotient of the matrix source by the kernel of matrix recovery is incomplete. -/
private theorem incomplete_matrix_quotient :
    ¬ @CompleteSpace (MatrixSource ⧸ quotientMatrix.ker)
      (IsTopologicalAddGroup.rightUniformSpace (MatrixSource ⧸ quotientMatrix.ker)) := by
  let E := MatrixSource
  let M : Submodule ℂ E := quotientMatrix.ker
  let Q := E ⧸ M
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  let : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  let q : E →L[ℂ] Q := M.mkQL
  let recover : Q →L[ℂ] (ℕ → Row) := M.liftQL quotientMatrix le_rfl
  let parts (n : ℕ) (r : Row) : E := (0, initialTestRows n r)
  let y (n : ℕ) : Q := q (parts n 1)
  have htruncate : Tendsto (fun k ↦ (truncatedOneRow k : Row)) atTop (𝓝 1) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_atTop_of_eventually_const (i₀ := j + 1)
    intro k hk
    change (if j < k then (1 : ℂ) else 0) = 1
    exact ite_eq_left (show j < k from hk)
  -- Finitely truncated rows can be supplied by either factor of the source.
  have hexchange (m k : ℕ) :
      q (parts m (truncatedOneRow k)) =
        q (fun i ↦ if i < m then truncatedOneRow k else 0, 0) := by
    change M.mkQ _ = M.mkQ _
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    change quotientMatrix (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    funext i j
    change 0 + testMatrixEntry i j (initialTestRows m (truncatedOneRow k)) =
      (if i < m then truncatedOneRow k else 0) j + 0
    rw [testMatrixEntry_initialTestRows, zero_add, add_zero]
    split <;> rfl
  have hy : CauchySeq y := by
    rw [cauchySeq_iff_sub_mem]
    intro U hU
    obtain ⟨V, hV, hclosed, hVU⟩ := exists_mem_nhds_isClosed_subset hU
    have hpre : (fun a : ℕ → NullRow ↦ q (a, 0)) ⁻¹' V ∈ 𝓝 0 := by
      have hcont : Continuous (fun a : ℕ → NullRow ↦ q (a, 0)) :=
        q.continuous.comp (continuous_id.prodMk continuous_const)
      apply hcont.tendsto 0
      simpa only [← Prod.zero_eq_mk, map_zero] using hV
    -- The preimage of a zero-neighborhood controls only finitely many null rows.
    rw [nhds_pi, Filter.mem_pi'] at hpre
    obtain ⟨s, W, hW, hsub⟩ := hpre
    refine ⟨s.sup id + 1, fun m hm n hn ↦ hVU ?_⟩
    have hlim (l : ℕ) : Tendsto (fun k ↦ q (parts l (truncatedOneRow k))) atTop (𝓝 (y l)) :=
      (q.continuous.comp (continuous_const.prodMk
        (initialTestRows l).continuous)).tendsto 1 |>.comp htruncate
    apply hclosed.mem_of_tendsto ((hlim m).sub (hlim n))
    filter_upwards with k
    rw [hexchange, hexchange, ← map_sub, Prod.mk_sub_mk, sub_self]
    apply hsub
    intro i hi
    have hi' : i ≤ s.sup id := Finset.le_sup (f := id) hi
    have hm' : i < m := by omega
    have hn' : i < n := by omega
    change ((if i < m then truncatedOneRow k else 0) -
      (if i < n then truncatedOneRow k else 0)) ∈ W i
    rw [ite_eq_left hm', ite_eq_left hn', sub_self]
    exact mem_of_mem_nhds (hW i)
  intro hcomplete
  have : CompleteSpace Q := hcomplete
  -- Every entry of a putative limit must be one.
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hy
  obtain ⟨x, rfl⟩ := M.mkQ_surjective z
  apply quotientMatrix_ne_one x
  funext i j
  have hentry : Tendsto (fun n ↦ recover (y n) i j) atTop
      (𝓝 (quotientMatrix x i j)) :=
    (((continuous_apply j).comp ((continuous_apply i).comp recover.continuous)).tendsto
      (M.mkQ x)).comp hz
  refine tendsto_nhds_unique hentry (tendsto_atTop_of_eventually_const (i₀ := i + 1) ?_)
  intro n hn
  change 0 + testMatrixEntry i j (initialTestRows n 1) = _
  rw [testMatrixEntry_initialTestRows, zero_add, ite_eq_left (show i < n from hn)]
  rfl

/-- Paper: Remark C.1.3.4, p. 660. A complete Hausdorff locally convex space can have
an incomplete quotient by a closed subspace. Both completeness predicates use the
additive uniformity. -/
theorem exists_incomplete_quotient :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E)
      (_ : IsTopologicalAddGroup E) (_ : PolynormableSpace ℂ E) (_ : T2Space E),
      @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) ∧
        ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧
          ¬ @CompleteSpace (E ⧸ M) (IsTopologicalAddGroup.rightUniformSpace (E ⧸ M)) := by
  let E := MatrixSource
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, quotientMatrix.ker, quotientMatrix.isClosed_ker, incomplete_matrix_quotient⟩
  have : IsClosed (compatibleRowTests : Set RowTests) := isClosed_compatibleRowTests
  have : IsUniformAddGroup compatibleRowTests := compatibleRowTests.toAddSubgroup.isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := E)]
  infer_instance

end IncompleteQuotient

/-- Paper: §C.1.4, p. 660. A set is bounded when a nonzero complex multiple of it
fits inside every prescribed zero-neighborhood. -/
theorem isVonNBounded_iff_rescale {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ U ∈ 𝓝 (0 : E), ∃ c : ℂ, c ≠ 0 ∧ c • B ⊆ U := by
  constructor
  · intro hB U hU
    obtain ⟨c, hc, hmaps⟩ :=
      (eventually_mem_nhdsWithin.and (hB hU).eventually_nhdsNE_zero).exists
    exact ⟨c, hc, hmaps.image_subset⟩
  · intro hB
    apply (nhds_basis_balanced ℂ E).isVonNBounded_iff.mpr
    rintro U ⟨hU, hbal⟩
    obtain ⟨c, hc, hsub⟩ := hB U hU
    have hinv : B ⊆ c⁻¹ • U := (smul_set_subset_iff₀ hc).mp hsub
    exact Absorbs.of_norm ⟨‖c⁻¹‖, fun d hd ↦ hinv.trans (hbal.smul_mono hd)⟩

/-- Paper: Proposition C.1.4.1, p. 661. A subset of a Hausdorff locally convex space is
bounded exactly when its image under every continuous linear functional is bounded. -/
theorem isVonNBounded_iff_dual_image {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ l : StrongDual ℂ E, IsBounded (l '' B) := by
  constructor
  · intro h l
    exact (NormedSpace.isVonNBounded_iff ℂ).mp (h.image l)
  · intro h
    refine (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mpr ?_
    rintro ⟨p, hp⟩
    let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
    -- Equip a copy of E with the topology of the single seminorm p.
    let F := ULift.{0} E
    let e : F ≃ₗ[ℂ] E := ULift.moduleEquiv
    let q := p.comp e.toLinearMap
    let : SeminormedAddCommGroup F := q.toAddGroupSeminorm.toSeminormedAddCommGroup
    let : TopologicalSpace F := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let : NormedSpace ℂ F := ⟨fun c x ↦ (map_smul_eq_mul q c x).le⟩
    let j : E →L[ℂ] F :=
      ⟨e.symm.toLinearMap, (norm_withSeminorms ℂ F).continuous_of_continuous_comp
        e.symm.toLinearMap (fun _ ↦ hp)⟩
    -- Evaluation at the points of B is pointwise bounded on the Banach dual of F.
    obtain ⟨C, hC⟩ := banach_steinhaus
        (g := fun x : B ↦ NormedSpace.inclusionInDoubleDual ℂ F (j x)) (fun l ↦ by
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (h (l.comp j))
      exact ⟨M, fun x ↦ hM _ ⟨x, x.property, rfl⟩⟩)
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change ‖j x‖ ≤ C
    rw [← (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := F)).norm_map (j x)]
    exact hC ⟨x, hx⟩

/-- Paper: Definition C.1.4.2, p. 661. A set is relatively compact if its closure in
the ambient space is compact. -/
def IsRelativelyCompact {E : Type*} [TopologicalSpace E] (A : Set E) : Prop :=
  IsCompact (closure A)

/-- Paper: Definition C.1.4.2, p. 661. A set is precompact if its image in the
completion has compact closure. -/
def IsPrecompactInCompletion {E : Type*} [UniformSpace E] (A : Set E) : Prop :=
  IsRelativelyCompact ((fun x : E ↦ (x : UniformSpace.Completion E)) '' A)

/-- Paper: Definition C.1.4.2, p. 661. Relative compactness of a closed subset of a
Hausdorff space agrees with compactness. -/
theorem isRelativelyCompact_iff_of_isClosed {E : Type*} [TopologicalSpace E] [T2Space E]
    {A : Set E} (hA : IsClosed A) : IsRelativelyCompact A ↔ IsCompact A := by
  rw [IsRelativelyCompact, hA.closure_eq]

/-- Paper: Remark C.1.4.3, p. 661. Compactness of the closure in the completion is
equivalent to total boundedness in the original space. -/
theorem isPrecompactInCompletion_iff_totallyBounded {E : Type*} [UniformSpace E] [T2Space E]
    (A : Set E) : IsPrecompactInCompletion A ↔ TotallyBounded A := by
  unfold IsPrecompactInCompletion IsRelativelyCompact
  rw [← totallyBounded_image_iff (UniformSpace.Completion.isUniformInducing_coe E),
    ← totallyBounded_closure]
  exact ⟨IsCompact.totallyBounded, fun h ↦ h.isCompact_of_isClosed isClosed_closure⟩

section Hilbert

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: Example C.1.4.4, p. 661. An infinite-dimensional Hilbert space with its
weak topology is incomplete, although its closed bounded subsets are complete (p. 662). -/
theorem weakHilbert_incomplete (hinf : ¬ FiniteDimensional ℂ H) :
    letI := IsTopologicalAddGroup.rightUniformSpace (WeakSpace ℂ H)
    ¬ CompleteSpace (WeakSpace ℂ H) ∧ QuasiCompleteSpace ℂ (WeakSpace ℂ H) := by
  let := IsTopologicalAddGroup.rightUniformSpace (WeakSpace ℂ H)
  let := isUniformAddGroup_of_addCommGroup (G := WeakSpace ℂ H)
  let := IsTopologicalAddGroup.rightUniformSpace (WeakDual ℂ (StrongDual ℂ H))
  let := isUniformAddGroup_of_addCommGroup (G := WeakDual ℂ (StrongDual ℂ H))
  let j := NormedSpace.inclusionInDoubleDualWeak ℂ H
  have hj : IsEmbedding j := NormedSpace.isEmbedding_inclusionInDoubleDualWeak ℂ H
  let d := InnerProductSpace.toDual ℂ H
  -- Applying Riesz representation to the conjugate of a bidual functional gives its vector.
  have hsurj : Function.Surjective j := by
    intro l
    let g : StrongDual ℂ H := (starL ℂ (A := ℂ)).toContinuousLinearMap.comp
      (l.toStrongDual.comp d.toLinearIsometry.toContinuousLinearMap)
    obtain ⟨x, hx⟩ := d.surjective g
    refine ⟨toWeakSpace ℂ H x, DFunLike.ext _ _ fun f ↦ ?_⟩
    obtain ⟨y, rfl⟩ := d.surjective f
    change inner ℂ y x = l (d y)
    rw [← inner_conj_symm]
    change starRingEnd ℂ (d x y) = l (d y)
    rw [hx]
    change starRingEnd ℂ (starRingEnd ℂ (l (d y))) = l (d y)
    simp
  constructor
  · have hD : ¬ FiniteDimensional ℂ (StrongDual ℂ H) := fun _ ↦
      hinf (Module.Finite.of_surjective d.symm.toLinearEquiv.toLinearMap d.symm.surjective)
    have hu : IsUniformInducing j :=
      AddMonoidHom.isUniformInducing_of_isInducing (f := j.toLinearMap.toAddMonoidHom) hj.isInducing
    exact fun hc ↦ weakDual_not_completeSpace hD ((hu.completeSpace_congr hsurj).mp hc)
  · refine ⟨fun {s} hb hc ↦ ?_⟩
    have hclosed : IsClosed (j '' s) :=
      hj.isInducing.isClosedMap (hsurj.range_eq.symm ▸ isClosed_univ) s hc
    have hcompact := WeakDual.isCompact_of_bounded_of_closed
      (WeakDual.isBounded_iff_isVonNBounded.mpr (hb.image j)) hclosed
    exact (hj.isCompact_iff.mpr hcompact).isComplete

/-- Paper: Example C.1.4.5, p. 661. In the strong operator topology on an infinite-dimensional
Hilbert space there is an unbounded Cauchy net without a limit. Closed bounded sets of
operators are nevertheless complete (p. 662). -/
theorem strongOperator_exists_unbounded_cauchy (hinf : ¬ FiniteDimensional ℂ H) :
    let B := H →Lₚₜ[ℂ] H
    letI := IsTopologicalAddGroup.rightUniformSpace B
    QuasiCompleteSpace ℂ B ∧ ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J)
      (_ : IsDirectedOrder J) (f : J → B), CauchySeq f ∧ ¬ IsVonNBounded ℂ (range f) ∧
        ¬ ∃ T, Tendsto f atTop (𝓝 T) := by
  classical
  let B := H →Lₚₜ[ℂ] H
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  let embed := PointwiseConvergenceCLM.inducingFn (RingHom.id ℂ) H H
  have hembed : IsUniformInducing embed :=
    AddMonoidHom.isUniformInducing_of_isInducing
      (PointwiseConvergenceCLM.isInducing_inducingFn (RingHom.id ℂ) H H)
  let op := UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite}
  have hcomplete : QuasiCompleteSpace ℂ B := by
    refine ⟨fun {s} hb hc ↦ hembed.isComplete_iff.mp (IsClosed.isComplete ?_)⟩
    -- Uniform boundedness gives an operator norm bound that passes to pointwise limits.
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun T : s ↦ op.symm T.1) (fun x ↦ by
      let ev := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H x
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
        ((NormedSpace.isVonNBounded_iff ℂ).mp (hb.image ev))
      exact ⟨M, fun T ↦ hM (ev T.1) ⟨T.1, T.2, rfl⟩⟩)
    apply isClosed_of_closure_subset
    intro g hg
    have hlin : g ∈ closure (range ((↑) : (H →ₗ[ℂ] H) → H → H)) :=
      closure_mono (by rintro _ ⟨T, _, rfl⟩; exact ⟨(op.symm T).toLinearMap, rfl⟩) hg
    have hbound (x : H) : ‖g x‖ ≤ C * ‖x‖ := by
      have hclosed : IsClosed {a : H → H | ‖a x‖ ≤ C * ‖x‖} :=
        isClosed_le (continuous_apply x).norm continuous_const
      refine hclosed.closure_subset_iff.mpr ?_ hg
      rintro _ ⟨T, hT, rfl⟩
      exact (op.symm T).le_of_opNorm_le (hC ⟨T, hT⟩) x
    let T : B := op ((linearMapOfMemClosureRangeCoe g hlin).mkContinuous C hbound)
    have heq : embed T = g := rfl
    refine ⟨T, ?_, heq⟩
    rw [← hc.closure_eq, hembed.isInducing.closure_eq_preimage_closure_image, mem_preimage, heq]
    exact hg
  refine ⟨hcomplete, ?_⟩
  -- Incompleteness of the weak dual provides a discontinuous linear functional.
  let : UniformSpace (WeakDual ℂ H) := IsTopologicalAddGroup.rightUniformSpace (WeakDual ℂ H)
  let : IsUniformAddGroup (WeakDual ℂ H) := isUniformAddGroup_of_addCommGroup
  let eval : WeakDual ℂ H →+ (H → ℂ) := ⟨⟨fun l x ↦ l x, rfl⟩, fun _ _ ↦ rfl⟩
  have heval : IsUniformInducing eval :=
    AddMonoidHom.isUniformInducing_of_isInducing (f := eval) ⟨rfl⟩
  have hnclosed : ¬ IsClosed (range eval) := fun h ↦
    weakDual_not_completeSpace hinf ((completeSpace_iff_isComplete_range heval).mpr h.isComplete)
  have hgap : ¬ closure (range eval) ⊆ range eval := fun h ↦ hnclosed (isClosed_of_closure_subset h)
  obtain ⟨g, hg, hg'⟩ := not_subset.mp hgap
  have hlin : g ∈ closure (range ((↑) : (H →ₗ[ℂ] ℂ) → H → ℂ)) :=
    closure_mono (by rintro _ ⟨l, rfl⟩; exact ⟨(WeakDual.toStrongDual l).toLinearMap, rfl⟩) hg
  let φ := linearMapOfMemClosureRangeCoe g hlin
  have hφ : ¬ Continuous φ := fun h ↦ hg' ⟨StrongDual.toWeakDual ⟨φ, h⟩, rfl⟩
  -- Extend the restriction to each finite-dimensional span by orthogonal projection.
  let l (s : Finset H) : StrongDual ℂ H :=
    let V := Submodule.span ℂ (s : Set H)
    let φV : StrongDual ℂ V := (φ.comp V.subtype).toContinuousLinearMap
    φV.comp V.orthogonalProjectionOnto
  have hl (s : Finset H) (x : H) (hx : x ∈ s) : l s x = φ x := by
    let V := Submodule.span ℂ (s : Set H)
    let y : V := ⟨x, Submodule.subset_span hx⟩
    change φ (V.orthogonalProjectionOnto (y : H) : H) = φ (y : H)
    rw [V.orthogonalProjectionOnto_mem_subspace_eq_self y]
  have : Nontrivial H := not_subsingleton_iff_nontrivial.mp fun _ ↦ hinf inferInstance
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let f (s : Finset H) : B := op ((l s).smulRight v)
  have hpoint (x : H) : Tendsto (fun s ↦ f s x) atTop (𝓝 (φ x • v)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := {x})
    intro s hs
    change l s x • v = φ x • v
    rw [hl s x (Finset.singleton_subset_iff.mp hs)]
  have hlim : Tendsto (fun s ↦ embed (f s)) atTop (𝓝 fun x ↦ φ x • v) :=
    tendsto_pi_nhds.mpr hpoint
  have hf : CauchySeq f := hembed.cauchy_map_iff.mp (by
    rw [Filter.map_map]
    exact hlim.cauchySeq)
  have hnlim : ¬ ∃ T, Tendsto f atTop (𝓝 T) := by
    rintro ⟨T, hT⟩
    have hTv (x : H) : T x = φ x • v :=
      tendsto_nhds_unique (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp hT x) (hpoint x)
    apply hφ ((isClosedEmbedding_smul_left (𝕜 := ℂ) hv).isEmbedding.isInducing.continuous_iff.mpr ?_)
    have hrecover : (fun x ↦ φ x • v) = (op.symm T : H → H) := funext fun x ↦ (hTv x).symm
    change Continuous (fun x ↦ φ x • v)
    rw [hrecover]
    exact (op.symm T).continuous
  refine ⟨Finset H, inferInstance, inferInstance, inferInstance, f, hf, ?_, hnlim⟩
  intro hb
  obtain ⟨T, -, hT⟩ := cauchySeq_tendsto_of_isComplete
    (hcomplete.quasiComplete hb.closure isClosed_closure)
    (fun s ↦ subset_closure (mem_range_self s)) hf
  exact hnlim ⟨T, hT⟩

/-- Paper: Example C.1.4.6(1–2), p. 662. A separable Hilbert space and the operator-norm
space of bounded endomorphisms of any Hilbert space are quasi-complete. -/
theorem hilbert_quasiComplete_examples :
    (SeparableSpace H → IsFrechetTVS H ∧ QuasiCompleteSpace ℂ H) ∧
      CompleteSpace (H →L[ℂ] H) ∧ QuasiCompleteSpace ℂ (H →L[ℂ] H) := by
  exact ⟨fun _ ↦ ⟨isFrechetTVS_of_banach H, inferInstance⟩, inferInstance, inferInstance⟩

end Hilbert

-- TODO(paper-gap): Example C.1.4.6(3) refers to Theorem D.1.5.7 on Schwartz–Bruhat spaces.
-- TODO(paper-gap): Remark C.1.4.7 uses nuclear locally convex spaces from §C.2.4.

section InductiveLimits

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {ι : Type*} {X : ι → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

/-- Paper: §C.1.5, p. 663. The final locally convex topology on a complex vector space
is generated by all seminorms that are continuous on each source. On an algebraic direct
sum or direct limit the maps are the canonical linear maps from its summands or stages. -/
@[instance_reducible]
def locallyConvexFinalTopology (i : ∀ k, X k →ₗ[ℂ] E) : TopologicalSpace E :=
  let p : SeminormFamily ℂ E {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} := Subtype.val
  p.moduleFilterBasis.topology

/-- Paper: §C.1.5, p. 663. For the identity map from a locally convex space the final
locally convex topology recovers the given topology. -/
theorem locallyConvexFinalTopology_id [t : TopologicalSpace E] [PolynormableSpace ℂ E] :
    locallyConvexFinalTopology (X := fun _ : Unit ↦ E) (fun _ ↦ LinearMap.id) = t := by
  change (SeminormFamily.moduleFilterBasis
    (Subtype.val : {p : Seminorm ℂ E // ∀ _ : Unit, Continuous p} → Seminorm ℂ E)).topology = t
  have h : (fun p : Seminorm ℂ E ↦ ∀ _ : Unit, Continuous p) =
      (fun p : Seminorm ℂ E ↦ Continuous p) := by
    simp only [forall_const]
  rw [h]
  exact (PolynormableSpace.withSeminorms ℂ E).withSeminorms_eq.symm

/-- Paper: Proposition C.1.5.1, p. 664. In a countable locally convex direct sum of
normed spaces, the intersection of suitably rescaled zero-neighborhoods is a zero-neighborhood.
Deviation: Both sequences are indexed starting at zero. -/
theorem exists_rescale_directSum_nhds (Y : ℕ → Type*) [∀ k, NormedAddCommGroup (Y k)]
    [∀ k, NormedSpace ℂ (Y k)] :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
    ∀ V : ℕ → Set (⨁ k, Y k), (∀ k, V k ∈ 𝓝 0) →
      ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧ (⋂ k, (ρ k : ℂ) • V k) ∈ 𝓝 0 := by
  classical
  let D := ⨁ k, Y k
  let lof := DirectSum.lof ℂ ℕ Y
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  intro V hV
  let P : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  let : PolynormableSpace ℂ D := hP.toPolynormableSpace
  have hlof (k : ℕ) : Continuous (lof k) :=
    hP.continuous_of_continuous_comp _ fun s ↦ s.property k
  let basis := PolynormableSpace.hasBasis_zero_ball ℂ D
  choose p hp hball using fun i ↦ basis.mem_iff.mp (hV i)
  choose a ha hbound using fun i k ↦
    ((p i).comp (lof k)).bound_of_continuous_normedSpace ((hp i).comp (hlof k))
  -- Each scale bounds its row through the diagonal. Each weight bounds its column above it.
  let ρ (i : ℕ) : ℝ := 1 + ∑ k ∈ Finset.range (i + 1), a i k
  let w (k : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range k, a i k
  have hρ (i : ℕ) : 1 ≤ ρ i := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ ↦ (ha i k).le)
  have hw (k : ℕ) : 1 ≤ w k := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (ha i k).le)
  have hρpos (i : ℕ) : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  have hdom (i k : ℕ) : a i k ≤ ρ i * w k := by
    by_cases h : k ≤ i
    · have hsum : a i k ≤ ∑ j ∈ Finset.range (i + 1), a i j :=
        Finset.single_le_sum (fun j _ ↦ (ha i j).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      calc
        a i k ≤ ρ i := hsum.trans (le_add_of_nonneg_left zero_le_one)
        _ ≤ ρ i * w k := le_mul_of_one_le_right (hρpos i).le (hw k)
    · have hsum : a i k ≤ ∑ j ∈ Finset.range k, a j k :=
        Finset.single_le_sum (fun j _ ↦ (ha j k).le) (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
      calc
        a i k ≤ w k := hsum.trans (le_add_of_nonneg_left zero_le_one)
        _ ≤ ρ i * w k := le_mul_of_one_le_left (zero_le_one.trans (hw k)) (hρ i)
  let s (k : ℕ) : Seminorm ℂ (Y k) :=
    (w k).toNNReal • normSeminorm ℂ (Y k)
  have hs (k : ℕ) (z : Y k) : s k z = w k * ‖z‖ := by
    change ((w k).toNNReal : ℝ) * ‖z‖ = w k * ‖z‖
    rw [Real.coe_toNNReal _ (zero_le_one.trans (hw k))]
  let q := directSumSeminorm s
  have hq : Continuous q := by
    refine hP.continuous_seminorm ⟨q, fun k ↦ ?_⟩
    change Continuous (fun z : Y k ↦ directSumSeminorm s (lof k z))
    simp only [lof, directSumSeminorm_lof, hs]
    exact continuous_norm.const_mul _
  have hpq (i : ℕ) (x : D) : p i x ≤ ρ i * q x := by
    have hsum := Finset.le_sum_of_subadditive (p i) (map_zero (p i)).le
      (map_add_le_add (p i)) x.support (fun k ↦ lof k (x k))
    rw [show (∑ k ∈ x.support, lof k (x k)) = x from DirectSum.sum_support_of x] at hsum
    refine hsum.trans ?_
    rw [show q x = ∑ k ∈ x.support, s k (x k) from directSumSeminorm_apply s x _ Subset.rfl,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [hs, ← mul_assoc]
    exact (hbound i k (x k)).trans (mul_le_mul_of_nonneg_right (hdom i k) (norm_nonneg _))
  refine ⟨ρ, hρpos, mem_of_superset (basis.mem_iff.mpr ⟨q, hq, Subset.rfl⟩) ?_⟩
  intro x hx
  rw [Seminorm.mem_ball_zero] at hx
  refine mem_iInter.mpr fun i ↦ smul_set_mono (hball i) ?_
  have hne : (ρ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρpos i).ne'
  rw [Seminorm.smul_ball_zero hne, Complex.norm_of_nonneg (hρpos i).le, mul_one,
    Seminorm.mem_ball_zero]
  exact (hpq i x).trans_lt (by simpa only [mul_one] using mul_lt_mul_of_pos_left hx (hρpos i))

end InductiveLimits

section CountableLimits

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

/-- Paper: §C.1.5, p. 664. The maps into the limit identify the algebraic stages with a
rising union, and the limit carries their final locally convex topology. The stage
injections need only be continuous. -/
structure IsInjectiveLCLimit (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E) : Prop where
  injective : ∀ k, Function.Injective (i k)
  compatible : ∀ k, (i (k+1)).comp (j k) = i k
  exhaustive : ∀ x : E, ∃ k, x ∈ range (i k)
  topology_eq : tE = locallyConvexFinalTopology (fun k ↦ (i k).toLinearMap)

/-- Paper: §C.1.5, p. 664. A constant sequence with identity transition maps presents
the original locally convex space as its limit. -/
theorem isInjectiveLCLimit_const [PolynormableSpace ℂ E] :
    IsInjectiveLCLimit (X := fun _ ↦ E) (fun _ ↦ ContinuousLinearMap.id ℂ E)
      (fun _ ↦ ContinuousLinearMap.id ℂ E) := by
  refine ⟨fun _ ↦ Function.injective_id, fun _ ↦ rfl, fun x ↦ ⟨0, x, rfl⟩, ?_⟩
  change tE = (SeminormFamily.moduleFilterBasis
    (Subtype.val : {p : Seminorm ℂ E // ∀ _ : ℕ, Continuous p} → Seminorm ℂ E)).topology
  have h : (fun p : Seminorm ℂ E ↦ ∀ _ : ℕ, Continuous p) =
      (fun p : Seminorm ℂ E ↦ Continuous p) := by
    simp only [forall_const]
  rw [h]
  exact (PolynormableSpace.withSeminorms ℂ E).withSeminorms_eq

/-- A continuous seminorm on a stage of a strict system extends to the final locally convex
topology on the limit. -/
private theorem IsInjectiveLCLimit.seminorm_extension
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) (n : ℕ) (p : Seminorm ℂ (X n)) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ q.comp (i n).toLinearMap = p := by
  classical
  have hstep (k : ℕ) (z : X k) : i (k+1) (j k z) = i k z :=
    DFunLike.congr_fun (h.compatible k) z
  have htransition (a b : ℕ) (hab : a ≤ b) :
      ∃ f : X a →L[ℂ] X b, (i b).comp f = i a := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨ContinuousLinearMap.id ℂ _, rfl⟩
    | succ b _ ih =>
      obtain ⟨f, hf⟩ := ih
      exact ⟨(j b).comp f, by rw [← ContinuousLinearMap.comp_assoc, h.compatible, hf]⟩
  choose f hf using fun k hk ↦ htransition k n hk
  let C (k : ℕ) := {s : Seminorm ℂ (X k) // Continuous s}
  let base (k : ℕ) (hk : k ≤ n) : C k :=
    ⟨p.comp (f k hk).toLinearMap, hp.comp (f k hk).continuous⟩
  choose next hnext hnextcomp using fun k (s : C k) ↦
    exists_seminorm_extension (f := (j k).toLinearMap) (hj k).isInducing s.property
  -- Pull back to the earlier stages and extend successively to the later stages.
  let r : ∀ k, C k := Nat.rec (base 0 (Nat.zero_le n)) fun k s ↦
    if hk : k+1 ≤ n then base (k+1) hk else ⟨next k s, hnext k s⟩
  have hrbase (k : ℕ) (hk : k ≤ n) : r k = base k hk := by
    cases k with
    | zero => rfl
    | succ k => exact dite_eq_left hk
  have hr (k : ℕ) (z : X k) : (r (k+1)).val (j k z) = (r k).val z := by
    by_cases hk : k+1 ≤ n
    · rw [hrbase _ hk, hrbase _ (Nat.le_of_succ_le hk)]
      change p (f (k+1) hk (j k z)) = p (f k _ z)
      congr 1
      apply h.injective n
      exact (DFunLike.congr_fun (hf (k+1) hk) (j k z)).trans
        ((hstep k z).trans (DFunLike.congr_fun (hf k _) z).symm)
    · change (if hk : k+1 ≤ n then base (k+1) hk else
        (⟨next k (r k), hnext k (r k)⟩ : C (k+1))).val (j k z) = (r k).val z
      rw [dite_eq_right hk]
      exact DFunLike.congr_fun (hnextcomp k (r k)) z
  have hlift (a : ℕ) (x : X a) (b : ℕ) (hab : a ≤ b) :
      ∃ y : X b, i b y = i a x ∧ (r b).val y = (r a).val x := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨x, rfl, rfl⟩
    | succ b _ ih =>
      obtain ⟨y, hy, hy'⟩ := ih
      exact ⟨j b y, (hstep b y).trans hy, (hr b y).trans hy'⟩
  -- Compare two representatives in a stage that contains both.
  have hagree {a b : ℕ} {x : X a} {y : X b} (he : i a x = i b y) :
      (r a).val x = (r b).val y := by
    obtain ⟨x', hx', hx⟩ := hlift a x (max a b) (le_max_left _ _)
    obtain ⟨y', hy', hy⟩ := hlift b y (max a b) (le_max_right _ _)
    have he' := h.injective (max a b) (hx'.trans (he.trans hy'.symm))
    exact hx.symm.trans ((congrArg (r (max a b)).val he').trans hy)
  choose stage repr hrepr using h.exhaustive
  let s (x : E) : ℝ := (r (stage x)).val (repr x)
  have hs (k : ℕ) (z : X k) : s (i k z) = (r k).val z := hagree (hrepr (i k z))
  let q : Seminorm ℂ E := Seminorm.ofSMulLE s
    (by simpa only [map_zero] using hs 0 0)
    (fun x y ↦ by
      let k := max (stage x) (stage y)
      obtain ⟨u, hu, -⟩ := hlift _ (repr x) k (le_max_left _ _)
      obtain ⟨v, hv, -⟩ := hlift _ (repr y) k (le_max_right _ _)
      rw [← (hu.trans (hrepr x)), ← (hv.trans (hrepr y)), ← map_add, hs, hs, hs]
      exact map_add_le_add (r k).val u v)
    (fun a x ↦ by
      rw [← hrepr x, ← map_smul, hs, hs, map_smul_eq_mul])
  have hseminorms : WithSeminorms
      (Subtype.val : {s : Seminorm ℂ E // ∀ k, Continuous (s ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  refine ⟨q, hseminorms.continuous_seminorm ⟨q, fun k ↦ ?_⟩, ?_⟩
  · simpa only [Function.comp_def, show ∀ z, q (i k z) = (r k).val z from hs k] using
      (r k).property
  · ext z
    change s (i n z) = p z
    rw [hs, hrbase n le_rfl]
    change p (f n le_rfl z) = p z
    congr 1
    exact h.injective n (DFunLike.congr_fun (hf n le_rfl) z)

/-- For a strict system of polynormable stages, the final locally convex topology induces the
original topology on each stage. -/
theorem IsInjectiveLCLimit.isEmbedding_stage
    [IsTopologicalAddGroup E] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) (k : ℕ) : IsEmbedding (i k) := by
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_, h.injective k⟩
  apply le_antisymm
  · simpa only [← map_le_iff_le_comap, Tendsto, map_zero] using (i k).continuous.tendsto 0
  · apply (PolynormableSpace.hasBasis_zero_ball ℂ (X k)).ge_iff.mpr
    intro p hp
    obtain ⟨q, hq, heq⟩ := h.seminorm_extension hj k p hp
    refine Filter.mem_comap.mpr ⟨q.ball 0 1, q.ball_mem_nhds hq zero_lt_one, ?_⟩
    intro z hz
    have heqz : q (i k z) = p z := DFunLike.congr_fun heq z
    rw [p.mem_ball_zero, ← heqz]
    exact q.mem_ball_zero.mp hz

/-- Seminorms that vanish on successively larger stages admit a continuous upper bound
on the limit, since only finitely many contribute on any one stage. -/
private theorem IsInjectiveLCLimit.exists_seminorm_ge_of_vanishing_on_stages
    [∀ k, IsTopologicalAddGroup (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (q : ℕ → Seminorm ℂ E) (hq : ∀ n, Continuous (q n)) (hz : ∀ n z, q n (i n z) = 0) :
    ∃ P : Seminorm ℂ E, Continuous P ∧ ∀ n, q n ≤ P := by
  classical
  let S (k : ℕ) : Submodule ℂ E := (i k).toLinearMap.range
  have hmono : Monotone S := monotone_nat_of_le_succ fun k ↦ by
    rintro _ ⟨y, rfl⟩
    exact ⟨j k y, DFunLike.congr_fun (h.compatible k) y⟩
  let M (k : ℕ) := (Finset.range k).sup (fun n ↦ (q n).comp (i k).toLinearMap)
  have hM (k n : ℕ) (y : X k) : q n (i k y) ≤ M k y := by
    by_cases hn : n < k
    · exact (Finset.le_sup (f := fun n ↦ (q n).comp (i k).toLinearMap)
        (Finset.mem_range.mpr hn) : _ ≤ M k) y
    · obtain ⟨z, hzy⟩ := hmono (Nat.le_of_not_gt hn) (show i k y ∈ S k from ⟨y, rfl⟩)
      change i n z = i k y at hzy
      rw [← hzy, hz]
      exact apply_nonneg _ _
  have hb : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun y ↦ by
    obtain ⟨k, z, rfl⟩ := h.exhaustive y
    exact ⟨M k z, forall_mem_range.mpr fun n ↦ hM k n z⟩
  let P : Seminorm ℂ E := ⨆ n, q n
  have hseminorms : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  refine ⟨P, hseminorms.continuous_seminorm ⟨P, fun k ↦ ?_⟩, fun n ↦ le_ciSup hb n⟩
  have hcont : Continuous (M k) := Seminorm.continuous_finsetSup fun n _ ↦ (hq n).comp (i k).continuous
  refine Seminorm.continuous_of_le (p := P.comp (i k).toLinearMap) hcont
    (Seminorm.le_def.mpr fun y ↦ ?_)
  change P (i k y) ≤ M k y
  rw [Seminorm.iSup_apply hb]
  exact ciSup_le fun n ↦ hM k n y

/-- Paper: Remark C.1.3.3, p. 660. A strict countable limit of complete Hausdorff
locally convex spaces is complete. If the stages are Fréchet and each inclusion
is proper, the limit is nonmetrizable.
Deviation: Stated here after introducing the inductive limit. -/
theorem strictLCLimit_complete_nonmetrizable [IsTopologicalAddGroup E]
    [∀ k, T2Space (X k)] [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (hc : ∀ k, @CompleteSpace (X k) (IsTopologicalAddGroup.rightUniformSpace (X k)))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) ∧
      ((∀ k, IsFrechetTVS (X k)) → (∀ k, ¬ Function.Surjective (j k)) → ¬ MetrizableSpace E) := by
  classical
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : ∀ k, UniformSpace (X k) := fun k ↦ IsTopologicalAddGroup.rightUniformSpace (X k)
  let : ∀ k, IsUniformAddGroup (X k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ k, CompleteSpace (X k) := hc
  let S (k : ℕ) : Submodule ℂ E := (i k).toLinearMap.range
  have hcomplete (k : ℕ) : IsComplete (S k : Set E) := by
    have hi : IsUniformInducing (i k) :=
      AddMonoidHom.isUniformInducing_of_isInducing (h.isEmbedding_stage hj k).isInducing
    exact hi.isComplete_range
  have hseminorms : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : PolynormableSpace ℂ E := hseminorms.toPolynormableSpace
  let : ContinuousSMul ℂ E := hseminorms.continuousSMul
  have hE : CompleteSpace E := by
    let e : E →+ UniformSpace.Completion E := UniformSpace.Completion.toCompl
    have he : IsUniformInducing e := UniformSpace.Completion.isUniformInducing_coe E
    have hd : DenseRange e := UniformSpace.Completion.denseRange_coe
    suffices hs : Function.Surjective e by exact (he.completeSpace_congr hs).mpr inferInstance
    intro x
    by_contra hx
    -- Separate a point outside the completion image from each complete stage.
    have hsep (k : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧
        (∀ y ∈ S k, q y = 0) ∧ x ∉ closure (e '' q.ball 0 1) := by
      have hclosed : IsClosed (e '' (S k : Set E)) :=
        (he.isComplete_iff.mpr (hcomplete k)).isClosed
      have hout : x ∉ e '' (S k : Set E) := fun ⟨y, _, hy⟩ ↦ hx ⟨y, hy⟩
      rw [← hclosed.iInter_closure_add_right_eq (𝓝 (0 : UniformSpace.Completion E)).basis_sets]
        at hout
      simp only [mem_iInter, id_eq, not_forall] at hout
      obtain ⟨U, hU, hxU⟩ := hout
      have hpre : e ⁻¹' U ∈ 𝓝 (0 : E) := by
        apply he.uniformContinuous.continuous.continuousAt.preimage_mem_nhds
        simpa only [map_zero] using hU
      obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hpre
      obtain ⟨q, hqp, hzero, hqball⟩ := exists_seminorm_thickening p (S k)
      refine ⟨q, Seminorm.continuous_of_le hp hqp, hzero, ?_⟩
      intro hxball
      apply hxU (closure_mono ?_ hxball)
      rw [hqball 1]
      rintro _ ⟨_, ⟨y, hy, z, hz, rfl⟩, rfl⟩
      rw [map_add]
      exact add_mem_add (mem_image_of_mem _ hy) (hpU hz)
    choose q hq hzero hout using hsep
    -- Each stage sees only a finite supremum of the weighted seminorms.
    let Q (n : ℕ) : Seminorm ℂ E := ((n : NNReal) + 1) • q n
    obtain ⟨P, hP, hle⟩ := h.exists_seminorm_ge_of_vanishing_on_stages Q
      (fun n ↦ (hq n).const_smul ((n : NNReal) + 1)) (fun n z ↦ by
        have hz : q n (i n z) = 0 := hzero n _ ⟨z, rfl⟩
        simp only [Q, smul_apply, hz, smul_zero])
    have hUC : UniformContinuous P := Seminorm.uniformContinuous_of_continuousAt_zero hP.continuousAt
    let v : UniformSpace.Completion E → ℝ := UniformSpace.Completion.extension P
    have hv : Continuous v := UniformSpace.Completion.continuous_extension
    have hvcoe (y : E) : v (e y) = P y := UniformSpace.Completion.extension_coe hUC y
    obtain ⟨n, hn⟩ := exists_nat_gt (v x)
    have hlarge : v x < (n : ℝ) + 1 := hn.trans (lt_add_one _)
    have hnear : (closure (e '' (q n).ball 0 1))ᶜ ∩ v ⁻¹' Iio ((n : ℝ) + 1) ∈ 𝓝 x :=
      inter_mem (isClosed_closure.isOpen_compl.mem_nhds (hout n))
        ((isOpen_Iio.preimage hv).mem_nhds hlarge)
    obtain ⟨_, hy, y, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hnear
    have hy' : P y < (n : ℝ) + 1 := by
      simpa only [mem_preimage, mem_Iio, hvcoe] using hy.2
    apply hy.1 (subset_closure (mem_image_of_mem _ ((q n).mem_ball_zero.mpr ?_)))
    have hbound := (hle n y).trans_lt hy'
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    apply (mul_lt_mul_iff_right₀ hpos).mp
    simpa only [Q, smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, mul_one]
      using hbound
  refine ⟨hE, fun _ hproper hmetric ↦ ?_⟩
  let : CompleteSpace E := hE
  let : MetrizableSpace E := hmetric
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have hcover : ⋃ k, (S k : Set E) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨k, y, rfl⟩ := h.exhaustive x
    exact ⟨k, y, rfl⟩
  obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed
    (fun k ↦ (hcomplete k).isClosed) hcover
  have hk' := (S k).eq_top_of_nonempty_interior' hk
  apply hproper k
  intro y
  have hy : i (k+1) y ∈ S k := hk' ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, h.injective (k+1) ((DFunLike.congr_fun (h.compatible k) z).trans hz)⟩

/-- Paper: Definition C.1.5.2, p. 664. An LF-space is Hausdorff and is a countable
locally convex inductive limit of Fréchet spaces.
Deviation: We use the equivalent injective presentation justified just after the definition
by quotienting the stages by the kernels of their maps to the limit. -/
def IsLFSpace (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ (X : ℕ → Type u) (_ : ∀ k, AddCommGroup (X k)) (_ : ∀ k, Module ℂ (X k))
    (_ : ∀ k, TopologicalSpace (X k)), (∀ k, IsFrechetTVS (X k)) ∧
      ∃ (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E), IsInjectiveLCLimit j i

/-- Paper: Example C.1.4.6(4), p. 662. A strict LF-space is exhausted by increasing
Fréchet subspaces and has their final locally convex topology.
Deviation: The stages are their images in the limit with the subspace topology, using
the embedding property stated in the example. -/
def IsStrictLFSpace (E : Type*) [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ S : ℕ → Submodule ℂ E, Monotone S ∧ (∀ k, IsFrechetTVS (S k)) ∧
    (∀ x : E, ∃ k, x ∈ S k) ∧ t = locallyConvexFinalTopology (fun k ↦ (S k).subtype)

/-- Paper: Definition C.1.5.2, p. 664. A Fréchet space is an LF-space via its constant
defining sequence. -/
theorem isLFSpace_of_isFrechetTVS (hE : IsFrechetTVS E) : IsLFSpace E := by
  obtain ⟨hadd, hpoly, hmetr, hcomplete⟩ := hE
  refine ⟨inferInstance, fun _ ↦ E, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, fun _ ↦ ⟨hadd, hpoly, hmetr, hcomplete⟩,
    fun _ ↦ ContinuousLinearMap.id ℂ E, fun _ ↦ ContinuousLinearMap.id ℂ E, ?_⟩
  exact isInjectiveLCLimit_const

/-- Paper: Example C.1.4.6(4), p. 662. Strict LF-spaces are LF-spaces and a closed
quotient of an LF-space is LF.
Deviation: Hausdorffness in Definition C.1.5.2 requires the subspace defining the
quotient to be closed. -/
theorem lfSpace_quotient_properties :
    (IsStrictLFSpace E → IsLFSpace E) ∧
      (IsLFSpace E → ∀ M : Submodule ℂ E, IsClosed (M : Set E) → IsLFSpace (E ⧸ M)) := by
  constructor
  · rintro ⟨hT2, S, hmono, hFrechet, hcover, htop⟩
    refine ⟨hT2, fun k ↦ S k, _, _, _, hFrechet, ?_, fun k ↦ (S k).subtypeL, ?_⟩
    · exact fun k ↦ (S k).subtypeL.codRestrict (S (k+1)) fun x ↦ hmono k.le_succ x.property
    · exact ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ by
        obtain ⟨k, hk⟩ := hcover x
        exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩, htop⟩
  · rintro ⟨_, X, _, _, _, hFrechet, j, i, h⟩ M hM
    have hP : WithSeminorms
        (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} →
          Seminorm ℂ E) := ⟨h.topology_eq⟩
    let : IsTopologicalAddGroup E := hP.isTopologicalAddGroup
    let : T2Space (E ⧸ M) := inferInstance
    -- Quotient each stage by the kernel of its map into the quotient of the limit.
    let f (k : ℕ) := M.mkQL.comp (i k)
    let K (k : ℕ) := (f k).ker
    have hf (k : ℕ) (x : X k) : f (k+1) (j k x) = f k x :=
      congrArg M.mkQ (DFunLike.congr_fun (h.compatible k) x)
    let iQ (k : ℕ) : X k ⧸ K k →L[ℂ] E ⧸ M := (K k).liftQL (f k) le_rfl
    let jQ (k : ℕ) : X k ⧸ K k →L[ℂ] X (k+1) ⧸ K (k+1) :=
      (K k).liftQL ((K (k+1)).mkQL.comp (j k)) (by
        intro x hx
        change (K (k+1)).mkQ (j k x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        change f (k+1) (j k x) = 0
        rwa [hf])
    have hiQ (k : ℕ) (x : X k) : iQ k ((K k).mkQ x) = f k x := rfl
    have hjQ (k : ℕ) (x : X k) : jQ k ((K k).mkQ x) = (K (k+1)).mkQ (j k x) := rfl
    refine ⟨inferInstance, fun k ↦ X k ⧸ K k, _, _, _,
      fun k ↦ isFrechetTVS_quotient (hFrechet k) (K k) (f k).isClosed_ker,
      jQ, iQ, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro k
      apply (LinearMap.ker_eq_bot (f := (iQ k).toLinearMap)).mp
      exact (K k).ker_liftQ_eq_bot' (f k).toLinearMap rfl
    · intro k
      ext y
      obtain ⟨x, rfl⟩ := (K k).mkQ_surjective y
      change iQ (k+1) (jQ k ((K k).mkQ x)) = iQ k ((K k).mkQ x)
      rw [hjQ, hiQ, hiQ, hf]
    · intro y
      obtain ⟨x, rfl⟩ := M.mkQ_surjective y
      obtain ⟨k, z, rfl⟩ := h.exhaustive x
      exact ⟨k, (K k).mkQ z, hiQ k z⟩
    · let : PolynormableSpace ℂ E := hP.toPolynormableSpace
      let : PolynormableSpace ℂ (E ⧸ M) := polynormableSpace_quotient M
      -- The continuous seminorms of the quotient are exactly those continuous on all stages.
      have hseminorms : (fun p : Seminorm ℂ (E ⧸ M) ↦
          ∀ k, Continuous (p ∘ (iQ k).toLinearMap)) =
          (fun p : Seminorm ℂ (E ⧸ M) ↦ Continuous p) := by
        funext p
        apply propext
        refine ⟨fun hp ↦ M.isQuotientMap_mkQL.continuous_iff.mpr ?_,
          fun hp k ↦ hp.comp (iQ k).continuous⟩
        apply hP.continuous_seminorm (⟨p.comp M.mkQ, fun k ↦ ?_⟩ : _)
        change Continuous (fun x : X k ↦ p (f k x))
        simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, Submodule.coe_mkQL, hiQ] using
          (hp k).comp (K k).mkQL.continuous
      change (inferInstance : TopologicalSpace (E ⧸ M)) =
        (SeminormFamily.moduleFilterBasis
          (Subtype.val : {p : Seminorm ℂ (E ⧸ M) // ∀ k, Continuous (p ∘ (iQ k).toLinearMap)} →
            Seminorm ℂ (E ⧸ M))).topology
      rw [hseminorms]
      exact (PolynormableSpace.withSeminorms ℂ (E ⧸ M)).withSeminorms_eq

/-- The final locally convex topology of an increasing Fréchet exhaustion is strict
when the stages carry their subspace topologies from a Hausdorff polynormable space. -/
private theorem strictLF_of_frechet_exhaustion [T2Space E] [PolynormableSpace ℂ E]
    (S : ℕ → Submodule ℂ E) (hmono : Monotone S) (hF : ∀ n, IsFrechetTVS (S n))
    (hcover : ∀ x : E, ∃ n, x ∈ S n) :
    @IsStrictLFSpace E _ _ (locallyConvexFinalTopology fun n ↦ (S n).subtype) := by
  let P : SeminormFamily ℂ E
      {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ (S n).subtype)} := Subtype.val
  have hOld := PolynormableSpace.withSeminorms ℂ E
  have hpre (p : Seminorm ℂ E) (hp : Continuous p) (n : ℕ) :
      Continuous (p ∘ (S n).subtype) := hp.comp continuous_subtype_val
  have hadd (n : ℕ) : IsTopologicalAddGroup (S n) := (hF n).choose
  let t := locallyConvexFinalTopology fun n ↦ (S n).subtype
  have hP : WithSeminorms P := ⟨rfl⟩
  have hold : @Continuous E E t tE id := by
    exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E _ _ _ _ _ _ _ _ _ _
      t hP.isTopologicalAddGroup tE hOld LinearMap.id
      (fun p ↦ hP.continuous_seminorm ⟨p.val, hpre p.val p.property⟩)
  have heq (n : ℕ) : TopologicalSpace.induced (fun x : S n ↦ (x : E)) t =
      TopologicalSpace.induced (fun x : S n ↦ (x : E)) tE := by
    have hnew : @Continuous (S n) E (TopologicalSpace.induced (fun x : S n ↦ (x : E)) tE)
        t ((S n).subtype) :=
      @WithSeminorms.continuous_of_continuous_comp ℂ ℂ (S n) E _ _ _ _ _ _ _ _ _ _
        (TopologicalSpace.induced (fun x : S n ↦ (x : E)) tE) (hadd n) t hP
        (S n).subtype (fun p ↦ p.property n)
    apply le_antisymm
    · apply induced_mono
      simpa only [induced_id] using continuous_iff_le_induced.mp hold
    · exact continuous_iff_le_induced.mp hnew
  refine ⟨@T2Space.of_injective_continuous E E t tE _ id Function.injective_id hold,
    S, hmono, ?_, hcover, ?_⟩
  · intro n
    change @IsFrechetTVS (S n) _ _ (TopologicalSpace.induced (fun x : S n ↦ (x : E)) t)
    rw [heq]
    exact hF n
  · have hpred :
        (fun p : Seminorm ℂ E ↦ ∀ n, @Continuous (S n) ℝ
          (TopologicalSpace.induced (fun x : S n ↦ (x : E)) t) _ (p ∘ (S n).subtype)) =
        (fun p : Seminorm ℂ E ↦ ∀ n, @Continuous (S n) ℝ
          (TopologicalSpace.induced (fun x : S n ↦ (x : E)) tE) _ (p ∘ (S n).subtype)) := by
      funext p
      exact propext (forall_congr' fun n ↦ by rw [heq n])
    change t = (SeminormFamily.moduleFilterBasis (Subtype.val :
      {p : Seminorm ℂ E // ∀ n, @Continuous (S n) ℝ
        (TopologicalSpace.induced (fun x : S n ↦ (x : E)) t) _ (p ∘ (S n).subtype)} →
      Seminorm ℂ E)).topology
    rw [hpred]
    rfl

/-- A strict LF-space is complete in its additive uniformity. -/
theorem IsStrictLFSpace.completeSpace [IsTopologicalAddGroup E]
    (h : IsStrictLFSpace E) : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  obtain ⟨_, S, hmono, hF, hcover, htop⟩ := h
  choose hadd hpoly hmetr hcomplete using hF
  let := hadd
  let := hpoly
  let := hmetr
  let : ∀ n, T2Space (S n) := fun _ ↦ inferInstance
  let j (n : ℕ) : S n →L[ℂ] S (n+1) :=
    (S n).subtypeL.codRestrict (S (n+1)) fun x ↦ hmono n.le_succ x.property
  have hlim : IsInjectiveLCLimit j (fun n ↦ (S n).subtypeL) := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, htop⟩
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, ⟨⟨x, hn⟩, rfl⟩⟩
  exact (strictLCLimit_complete_nonmetrizable hcomplete hlim fun n ↦
    IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal).1

section StrictLFQuotient

open scoped ZeroAtInfty

local notation "Matrix" => (ℕ → ℕ → ℂ)
local notation "NullRows" => (ℕ → C₀(ℕ, ℂ))
local notation "MatrixPair" => (NullRows × Matrix)

/-- Allow arbitrary entries in the first `n` correction rows and require the rest to vanish. -/
private def finiteRowStage (n : ℕ) : Submodule ℂ MatrixPair :=
  ⨅ i : {i : ℕ // n ≤ i},
    ((ContinuousLinearMap.proj i.val).comp (ContinuousLinearMap.snd ℂ NullRows Matrix)).ker

/-- The cutoff condition on a pair amounts to vanishing of all later correction rows. -/
private theorem mem_finiteRowStage {n : ℕ} {x : MatrixPair} :
    x ∈ finiteRowStage n ↔ ∀ i, n ≤ i → x.2 i = 0 := by
  rw [finiteRowStage, Submodule.mem_iInf]
  exact ⟨fun h i hi ↦ h ⟨i, hi⟩, fun h i ↦ h i.val i.property⟩

/-- Increasing the cutoff preserves every previously allowed correction. -/
private theorem finiteRowStage_mono : Monotone finiteRowStage := fun _ _ h _ hx ↦
  mem_finiteRowStage.mpr fun i hi ↦ mem_finiteRowStage.mp hx i (h.trans hi)

/-- A cutoff stage is closed in the product of the two row spaces. -/
private theorem isClosed_finiteRowStage (n : ℕ) : IsClosed (finiteRowStage n : Set MatrixPair) := by
  simp only [finiteRowStage, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ ((ContinuousLinearMap.proj i.val).comp
    (ContinuousLinearMap.snd ℂ NullRows Matrix)).isClosed_ker

/-- The source consists of a family of null rows and a correction supported on finitely many rows. -/
private def finiteRowSource : Submodule ℂ MatrixPair := ⨆ n, finiteRowStage n

/-- The cutoff stages regarded as subspaces of the source. -/
private def finiteRowSourceStage (n : ℕ) : Submodule ℂ finiteRowSource :=
  (finiteRowStage n).comap finiteRowSource.subtype

/-- Give the source the final locally convex topology from the cutoff stages. -/
@[instance_reducible]
private def finiteRowTopology : TopologicalSpace finiteRowSource :=
  locallyConvexFinalTopology fun n ↦ (finiteRowSourceStage n).subtype

/-- The final topology is generated by seminorms continuous on the original cutoff stages. -/
private theorem finiteRow_withSeminorms :
    @WithSeminorms ℂ finiteRowSource _ _ _ _
      (Subtype.val : {p : Seminorm ℂ finiteRowSource //
        ∀ k, Continuous (p ∘ (finiteRowSourceStage k).subtype)} → Seminorm ℂ finiteRowSource)
      finiteRowTopology := by
  let : TopologicalSpace finiteRowSource := finiteRowTopology
  exact ⟨rfl⟩

/-- The additive group operations are continuous in the final topology. -/
private theorem finiteRow_isTopologicalAddGroup :
    @IsTopologicalAddGroup finiteRowSource finiteRowTopology _ := by
  let : TopologicalSpace finiteRowSource := finiteRowTopology
  exact finiteRow_withSeminorms.isTopologicalAddGroup

/-- In the final topology every cutoff stage retains its Fréchet topology from the product. -/
private theorem strictLF_finiteRowSource : @IsStrictLFSpace finiteRowSource _ _ finiteRowTopology := by
  apply strictLF_of_frechet_exhaustion finiteRowSourceStage
  · intro m n h x hx
    exact finiteRowStage_mono h hx
  · intro n
    let S := finiteRowSourceStage n
    let e : S → MatrixPair := fun x ↦ x.val.val
    have he : IsUniformInducing e :=
      (show IsUniformInducing (Subtype.val : finiteRowSource → MatrixPair) from ⟨rfl⟩).comp
        (show IsUniformInducing (Subtype.val : S → finiteRowSource) from ⟨rfl⟩)
    have hr : range e = (finiteRowStage n : Set MatrixPair) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨⟨x, le_iSup finiteRowStage n hx⟩, hx⟩, rfl⟩
    let : IsUniformAddGroup finiteRowSource := finiteRowSource.toAddSubgroup.isUniformAddGroup
    let : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
    let : MetrizableSpace (ℕ → ℂ) := UniformSpace.metrizableSpace
    let : MetrizableSpace NullRows := UniformSpace.metrizableSpace
    let : MetrizableSpace Matrix := UniformSpace.metrizableSpace
    let : MetrizableSpace MatrixPair := metrizableSpace_prod
    let : MetrizableSpace finiteRowSource := MetrizableSpace.subtype (finiteRowSource : Set MatrixPair)
    change IsFrechetTVS S
    refine ⟨inferInstance, inferInstance, MetrizableSpace.subtype (S : Set finiteRowSource), ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq (G := S), completeSpace_iff_isComplete_range he, hr]
    exact (isClosed_finiteRowStage n).isComplete
  · intro x
    exact (Submodule.mem_iSup_of_directed _ finiteRowStage_mono.directed_le).mp x.property

/-- The inclusions from the cutoff stages with their original topologies are continuous. -/
private theorem finiteRow_inclusion_continuous (n : ℕ) :
    @Continuous (finiteRowSourceStage n) finiteRowSource _ finiteRowTopology
      (finiteRowSourceStage n).subtype := by
  exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ (finiteRowSourceStage n) finiteRowSource
    _ _ _ _ _ _ _ _ _ _ _ inferInstance finiteRowTopology finiteRow_withSeminorms
    (finiteRowSourceStage n).subtype (fun p ↦ p.property n)

/-- Add the null rows to the finitely supported correction, reading the result entrywise. -/
private def finiteRowRecover :
    @ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ) finiteRowSource finiteRowTopology _ Matrix _ _ _ _ := by
  let recover : MatrixPair →ₗ[ℂ] Matrix :=
    { toFun := fun x i j ↦ x.1 i j + x.2 i j
      map_add' := fun x y ↦ by
        funext i j
        change (x.1 i j + y.1 i j) + (x.2 i j + y.2 i j) = _
        exact add_add_add_comm _ _ _ _
      map_smul' := fun a x ↦ by
        funext i j
        change a * x.1 i j + a * x.2 i j = a * (x.1 i j + x.2 i j)
        exact (mul_add _ _ _).symm }
  have hrecover : Continuous recover := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    apply Continuous.add _ ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
    exact (BoundedContinuousFunction.lipschitz_eval_const j).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
        ((continuous_apply i).comp continuous_fst))
  have hstage (n : ℕ) : Continuous (fun x : finiteRowSourceStage n ↦ recover x.val.val) :=
    hrecover.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hpre (p : Seminorm ℂ Matrix) (hp : Continuous p) (n : ℕ) :
      Continuous (p.comp (recover.comp finiteRowSource.subtype) ∘ (finiteRowSourceStage n).subtype) :=
    hp.comp (hstage n)
  let : TopologicalSpace finiteRowSource := finiteRowTopology
  let : IsTopologicalAddGroup finiteRowSource := finiteRow_isTopologicalAddGroup
  refine ⟨recover.comp finiteRowSource.subtype, ?_⟩
  apply (PolynormableSpace.withSeminorms ℂ Matrix).continuous_of_continuous_comp
  intro p
  exact finiteRow_withSeminorms.continuous_seminorm
    ⟨p.val.comp (recover.comp finiteRowSource.subtype), hpre p.val p.property⟩

/-- The null-row family enters the source with no correction. -/
private def nullRowsInclusion (a : NullRows) : finiteRowSource :=
  ⟨(a, 0), le_iSup finiteRowStage 0 (mem_finiteRowStage.mpr fun _ _ ↦ rfl)⟩

/-- The same row can be used as the correction in all rows below a fixed cutoff. -/
private def firstCorrectionRows (n : ℕ) (r : ℕ → ℂ) : finiteRowSource :=
  ⟨(0, fun i ↦ if i < n then r else 0),
    le_iSup finiteRowStage n (mem_finiteRowStage.mpr fun _ hi ↦ ite_eq_right hi.not_gt)⟩

/-- The quotient by the kernel of row recovery has a Cauchy sequence of partial
constant-one matrices. Its putative limit has no representative with finitely many corrections. -/
private theorem incomplete_finiteRowQuotient :
    letI := finiteRowTopology
    letI := finiteRow_isTopologicalAddGroup
    ¬ @CompleteSpace (finiteRowSource ⧸ finiteRowRecover.ker)
      (IsTopologicalAddGroup.rightUniformSpace (finiteRowSource ⧸ finiteRowRecover.ker)) := by
  -- Establish the continuity of the two ways of supplying the same finite row truncations.
  let stageTopology (n : ℕ) : TopologicalSpace (finiteRowSourceStage n) := inferInstance
  let liftNull (a : NullRows) : finiteRowSourceStage 0 :=
    ⟨nullRowsInclusion a, mem_finiteRowStage.mpr fun _ _ ↦ rfl⟩
  let liftParts (n : ℕ) (r : ℕ → ℂ) : finiteRowSourceStage n :=
    ⟨firstCorrectionRows n r, mem_finiteRowStage.mpr fun _ hi ↦ ite_eq_right hi.not_gt⟩
  have hLiftNull : Continuous liftNull :=
    ((continuous_id.prodMk continuous_const).subtype_mk _).subtype_mk _
  have hLiftParts (n : ℕ) : Continuous (liftParts n) := by
    refine ((continuous_const.prodMk (continuous_pi fun i ↦ ?_)).subtype_mk _).subtype_mk _
    by_cases hi : i < n
    · simpa only [ite_eq_left hi] using (show Continuous (fun r : ℕ → ℂ ↦ r) from continuous_id)
    · simpa only [ite_eq_right hi] using (continuous_const : Continuous (fun _ : ℕ → ℂ ↦ (0 : ℕ → ℂ)))
  let : TopologicalSpace finiteRowSource := finiteRowTopology
  have hnull : Continuous nullRowsInclusion :=
    @Continuous.comp _ _ _ _ (stageTopology 0) finiteRowTopology _ _
      (finiteRow_inclusion_continuous 0) hLiftNull
  have hparts (n : ℕ) : Continuous (firstCorrectionRows n) :=
    @Continuous.comp _ _ _ _ (stageTopology n) finiteRowTopology _ _
      (finiteRow_inclusion_continuous n) (hLiftParts n)
  let : IsTopologicalAddGroup finiteRowSource := finiteRow_isTopologicalAddGroup
  let M : Submodule ℂ finiteRowSource := finiteRowRecover.ker
  let Q := finiteRowSource ⧸ M
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  let : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  let q : finiteRowSource →L[ℂ] Q := M.mkQL
  let recover : Q →L[ℂ] Matrix := M.liftQL finiteRowRecover le_rfl
  let y (n : ℕ) : Q := q (firstCorrectionRows n 1)
  have htruncate : Tendsto (fun k ↦ (truncatedOneRow k : ℕ → ℂ)) atTop (𝓝 1) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_atTop_of_eventually_const (i₀ := j + 1)
    intro k hk
    exact ite_eq_left (show j < k from hk)
  have hexchange (m k : ℕ) :
      q (firstCorrectionRows m (truncatedOneRow k)) =
        q (nullRowsInclusion fun i ↦ if i < m then truncatedOneRow k else 0) := by
    change M.mkQ _ = M.mkQ _
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    change finiteRowRecover (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    funext i j
    change 0 + (if i < m then (truncatedOneRow k : ℕ → ℂ) else 0) j =
      (if i < m then truncatedOneRow k else 0) j + 0
    simp only [zero_add, add_zero]
    split <;> rfl
  have hy : CauchySeq y := by
    rw [cauchySeq_iff_sub_mem]
    intro U hU
    obtain ⟨V, hV, hclosed, hVU⟩ := exists_mem_nhds_isClosed_subset hU
    have hpre : (fun a : NullRows ↦ q (nullRowsInclusion a)) ⁻¹' V ∈ 𝓝 0 :=
      (q.continuous.comp hnull).continuousAt.preimage_mem_nhds
        (show V ∈ 𝓝 (q (nullRowsInclusion 0)) from
          (show q (nullRowsInclusion 0) = 0 from map_zero q) ▸ hV)
    rw [nhds_pi, Filter.mem_pi'] at hpre
    obtain ⟨s, W, hW, hsub⟩ := hpre
    refine ⟨s.sup id + 1, fun m hm n hn ↦ hVU ?_⟩
    have hlim (l : ℕ) : Tendsto (fun k ↦ q (firstCorrectionRows l (truncatedOneRow k)))
        atTop (𝓝 (y l)) := ((q.continuous.comp (hparts l)).tendsto 1).comp htruncate
    apply hclosed.mem_of_tendsto ((hlim m).sub (hlim n))
    filter_upwards with k
    rw [hexchange, hexchange, ← map_sub]
    have hsubtraction (a b : NullRows) :
        nullRowsInclusion a - nullRowsInclusion b = nullRowsInclusion (a - b) :=
      Subtype.ext (Prod.ext rfl (sub_self (0 : Matrix)))
    rw [hsubtraction]
    apply hsub
    intro i hi
    have hi' : i ≤ s.sup id := Finset.le_sup (f := id) hi
    change (if i < m then truncatedOneRow k else 0) -
      (if i < n then truncatedOneRow k else 0) ∈ W i
    rw [ite_eq_left (show i < m by omega), ite_eq_left (show i < n by omega), sub_self]
    exact mem_of_mem_nhds (hW i)
  intro hcomplete
  have : CompleteSpace Q := hcomplete
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hy
  obtain ⟨x, rfl⟩ := M.mkQ_surjective z
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ finiteRowStage_mono.directed_le).mp x.property
  have hzero := mem_finiteRowStage.mp hi i le_rfl
  have hconst (j : ℕ) : x.val.1 i j = 1 := by
    have hentry : Tendsto (fun n ↦ recover (y n) i j) atTop (𝓝 (finiteRowRecover x i j)) :=
      (((continuous_apply j).comp ((continuous_apply i).comp recover.continuous)).tendsto
        (M.mkQ x)).comp hz
    have heq := tendsto_nhds_unique hentry (tendsto_atTop_of_eventually_const (i₀ := i + 1) (by
      intro n hn
      change 0 + (if i < n then (1 : ℕ → ℂ) else 0) j = 1
      rw [ite_eq_left (show i < n from hn), zero_add]
      rfl))
    change x.val.1 i j + x.val.2 i j = 1 at heq
    simpa only [hzero, Pi.zero_apply, add_zero] using heq
  have hlim := zero_at_infty (x.val.1 i)
  rw [show (⇑(x.val.1 i)) = (fun _ ↦ 1) from funext hconst] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- Paper: Example C.1.4.6(4), p. 663. A Hausdorff quotient of a strict LF-space can
fail to be strict. -/
theorem exists_quotient_not_strictLF :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E),
      IsStrictLFSpace E ∧ ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧
        ¬ IsStrictLFSpace (E ⧸ M) := by
  let : TopologicalSpace finiteRowSource := finiteRowTopology
  let : IsTopologicalAddGroup finiteRowSource := finiteRow_isTopologicalAddGroup
  refine ⟨finiteRowSource, inferInstance, inferInstance, finiteRowTopology, strictLF_finiteRowSource,
    finiteRowRecover.ker, finiteRowRecover.isClosed_ker, ?_⟩
  exact fun h ↦ incomplete_finiteRowQuotient h.completeSpace

end StrictLFQuotient

/-- A point outside a stage of a system of closed embeddings is detected by a continuous
seminorm on the limit that vanishes on that stage. -/
private theorem IsInjectiveLCLimit.exists_seminorm_vanishing_on_stage
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsClosedEmbedding (j k)) (n : ℕ) {x : E} (hx : x ∉ range (i n)) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ 0 < q x ∧ ∀ z, q (i n z) = 0 := by
  have transition (a b : ℕ) (hab : a ≤ b) :
      ∃ t : X a →L[ℂ] X b, (i b).comp t = i a ∧ IsClosedEmbedding t := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨ContinuousLinearMap.id ℂ _, rfl, IsClosedEmbedding.id⟩
    | succ b _ ih =>
      obtain ⟨t, ht, htc⟩ := ih
      exact ⟨(j b).comp t, by rw [← ContinuousLinearMap.comp_assoc, h.compatible, ht],
        (hj b).comp htc⟩
  obtain ⟨m, y, hy⟩ := h.exhaustive x
  have hnm : n ≤ m := by
    by_contra! hmn
    obtain ⟨t, ht, _⟩ := transition m n hmn.le
    exact hx ⟨t y, (DFunLike.congr_fun ht y).trans hy⟩
  obtain ⟨t, ht, htc⟩ := transition n m hnm
  have hyout : y ∉ t.toLinearMap.range := by
    rintro ⟨z, rfl⟩
    exact hx ⟨z, (DFunLike.congr_fun ht z).symm.trans hy⟩
  let : Module ℝ (X m) := Module.restrictScalars ℝ ℂ (X m)
  let : IsScalarTower ℝ ℂ (X m) := IsScalarTower.restrictScalars ℝ ℂ (X m)
  let : LocallyConvexSpace ℝ (X m) := (PolynormableSpace.withSeminorms ℂ (X m)).toLocallyConvexSpace
  obtain ⟨φ, hφ, hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem t.toLinearMap.range
    htc.isClosed_range hyout
  let p := (normSeminorm ℂ ℂ).comp φ.toLinearMap
  obtain ⟨q, hq, hqm⟩ := h.seminorm_extension (fun k ↦ (hj k).isEmbedding) m p φ.continuous.norm
  have he (z : X m) : q (i m z) = ‖φ z‖ := DFunLike.congr_fun hqm z
  refine ⟨q, hq, ?_, fun z ↦ ?_⟩
  · rw [← hy, he]
    exact norm_pos_iff.mpr hφ
  · calc
      q (i n z) = q (i m (t z)) := congrArg q (DFunLike.congr_fun ht z).symm
      _ = ‖φ (t z)‖ := he (t z)
      _ = 0 := norm_eq_zero.mpr (hzero (t z) ⟨z, rfl⟩)

/-- Paper: Proposition C.1.5.3, p. 664. In a strict limit with closed stage embeddings
a subset is bounded exactly when it is the image of a bounded subset of a single stage. -/
theorem isVonNBounded_iff_bounded_stage [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsClosedEmbedding (j k)) (B : Set E) :
    IsVonNBounded ℂ B ↔ ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ i k '' A = B := by
  classical
  let : ∀ k, IsTopologicalAddGroup (X k) := fun k ↦ PolynormableSpace.isTopologicalAddGroup ℂ (X k)
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : PolynormableSpace ℂ E := hP.toPolynormableSpace
  constructor
  · intro hB
    have hb := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp hB
    suffices hcontains : ∃ k, B ⊆ range (i k) by
      obtain ⟨k, hk⟩ := hcontains
      refine ⟨k, (i k) ⁻¹' B, ?_, image_preimage_eq_of_subset hk⟩
      apply (PolynormableSpace.withSeminorms ℂ (X k)).isVonNBounded_iff_seminorm_bounded.mpr
      intro p
      obtain ⟨q, hq, he⟩ := h.seminorm_extension (fun n ↦ (hj n).isEmbedding) k p.val p.property
      obtain ⟨R, hR, hRB⟩ := hb ⟨q, hq⟩
      refine ⟨R, hR, fun y hy ↦ ?_⟩
      change p.val y < R
      rw [← DFunLike.congr_fun he y]
      exact hRB _ hy
    by_contra hno
    choose x hxB hx using fun n ↦ Set.not_subset.mp (fun hsub ↦ hno ⟨n, hsub⟩)
    choose q hq hpos hzero using fun n ↦ h.exists_seminorm_vanishing_on_stage hj n (hx n)
    let w (n : ℕ) : NNReal := ⟨(n : ℝ) / q n (x n), div_nonneg (Nat.cast_nonneg n) (hpos n).le⟩
    let Q (n : ℕ) := w n • q n
    obtain ⟨P, hcont, hle⟩ := h.exists_seminorm_ge_of_vanishing_on_stages Q
      (fun n ↦ (hq n).const_smul (w n)) (fun n z ↦ by simp only [Q, smul_apply, hzero, smul_zero])
    obtain ⟨R, _, hRB⟩ := hb ⟨P, hcont⟩
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have he : Q n (x n) = n := div_mul_cancel₀ _ (hpos n).ne'
    have hlt := ((hle n) (x n)).trans_lt (hRB _ (hxB n))
    exact hn.not_gt (he ▸ hlt)
  · rintro ⟨k, A, hA, rfl⟩
    exact hA.image (i k)

/-- Paper: Lemma C.1.5.4, p. 665. If a Hausdorff topological vector space is exhausted
by rising images of Fréchet spaces under continuous linear injections, every continuous
linear map into it from a Fréchet space factors continuously through one stage.
Deviation: The sequence is indexed starting at zero. -/
theorem frechet_factorization [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    (hX : ∀ k, IsFrechetTVS (X k)) (i : ∀ k, X k →L[ℂ] E) (hi : ∀ k, Function.Injective (i k))
    (hr : ∀ k, range (i k) ⊆ range (i (k+1))) (hcov : ∀ x : E, ∃ k, x ∈ range (i k))
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hF : IsFrechetTVS F)
    (u : F →L[ℂ] E) : ∃ k, ∃ v : F →L[ℂ] X k, (i k).comp v = u := by
  obtain ⟨hTF, hPF, hMF, hCF⟩ := hF
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace F := hCF
  have : (uniformity F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  have : BaireSpace F := by
    let := UniformSpace.metricSpace F
    infer_instance
  -- Project the closed graphs of the equations u x = iₖ y onto F.
  let diff (k : ℕ) := u.comp (ContinuousLinearMap.fst ℂ F (X k)) -
    (i k).comp (ContinuousLinearMap.snd ℂ F (X k))
  let G (k : ℕ) := (diff k).ker
  let p (k : ℕ) := (ContinuousLinearMap.fst ℂ F (X k)).comp (G k).subtypeL
  have hg (k : ℕ) (z : G k) : u z.val.1 = i k z.val.2 := sub_eq_zero.mp z.property
  have hcover : ⋃ k, range (p k) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨k, y, hy⟩ := hcov (u x)
    exact mem_iUnion.mpr ⟨k, ⟨(x, y), sub_eq_zero.mpr hy.symm⟩, rfl⟩
  -- Baire gives a nonmeagre range, which is the hypothesis of the open mapping theorem.
  have hex : ∃ k, ¬ IsMeagre (range (p k)) := by
    by_contra! hm
    have hm' := isMeagre_iUnion hm
    rw [hcover] at hm'
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty hm'
  obtain ⟨k, hk⟩ := hex
  obtain ⟨hTk, hPk, hMk, hCk⟩ := hX k
  let : UniformSpace (X k) := IsTopologicalAddGroup.rightUniformSpace (X k)
  have : IsUniformAddGroup (X k) := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace (X k) := hCk
  have : CompleteSpace (G k) := completeSpace_coe_iff_isComplete.mpr (diff k).isClosed_ker.isComplete
  have : IsUniformAddGroup (G k) := (G k).toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology (G k) :=
    inferInstanceAs (FirstCountableTopology ((G k) : Set (F × X k)))
  have hop := isOpenMap_of_not_isMeagre_range (p k) hk
  have hs : Function.Surjective (p k) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_nonempty_interior'
    have ho : IsOpen (range (p k)) := hop.isOpen_range
    rw [show ((p k).range : Set F) = range (p k) from rfl, ho.interior_eq]
    exact range_nonempty _
  have hinj : Function.Injective (p k) := by
    intro z w hzw
    apply Subtype.ext
    exact Prod.ext hzw (hi k ((hg k z).symm.trans ((congrArg u hzw).trans (hg k w))))
  let e := LinearEquiv.ofBijective (p k).toLinearMap ⟨hinj, hs⟩
  let inv : F →L[ℂ] G k := ⟨e.symm, e.toEquiv.continuous_symm_iff.mpr hop⟩
  refine ⟨k, ((ContinuousLinearMap.snd ℂ F (X k)).comp (G k).subtypeL).comp inv, ?_⟩
  ext x
  exact (hg k (inv x)).symm.trans (congrArg u (e.apply_symm_apply x))

-- TODO(paper-gap): On p. 665 the second Baire argument only establishes a dense union.

/-- A linear map out of a countable locally convex limit is continuous if it is
continuous on every stage, even when the target only has a topological additive group
structure. -/
private theorem IsInjectiveLCLimit.continuous_of_stages
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (f : E →ₗ[ℂ] G) (hf : ∀ k, Continuous (f ∘ i k)) : Continuous f := by
  classical
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hP.isTopologicalAddGroup
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  intro U hU
  change f ⁻¹' U ∈ 𝓝 (0 : E)
  -- Use one smaller target neighborhood for each successive stage.
  have shrink (V : {V : Set G // V ∈ 𝓝 (0 : G)}) :
      ∃ W : {W : Set G // W ∈ 𝓝 (0 : G)}, W.val + W.val ⊆ V.val := by
    obtain ⟨W, hW, hW₀, hWV⟩ := exists_open_nhds_zero_add_subset V.property
    exact ⟨⟨W, hW.mem_nhds hW₀⟩, hWV⟩
  let R : ℕ → {V : Set G // V ∈ 𝓝 (0 : G)} :=
    Nat.rec ⟨U, hU⟩ fun _ R ↦ (shrink R).choose
  have hR (n : ℕ) : (R (n+1)).val + (R (n+1)).val ⊆ (R n).val :=
    (shrink (R n)).choose_spec
  have hball (k : ℕ) := (PolynormableSpace.hasBasis_zero_ball ℂ (X k)).mem_iff.mp
    (((hf k).tendsto' 0 0 (by simp)) (R (k+1)).property)
  choose p hp hsub using hball
  let A (k : ℕ) : Set E := i k '' (p k).ball 0 1
  have hA₀ (k : ℕ) : 0 ∈ A k := ⟨0, (p k).mem_ball_self zero_lt_one, map_zero _⟩
  have hA (k : ℕ) : MapsTo f (A k) (R (k+1)).val := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub k hx
  -- The union of the finite sums is balanced and convex and stays inside the preimage of U.
  let S : ℕ → Set E := Nat.rec 0 fun n S ↦ S + A n
  have hstep (n : ℕ) : S (n+1) = S n + A n := rfl
  have hSmono : Monotone S := monotone_nat_of_le_succ fun n x hx ↦ by
    rw [hstep]
    simpa only [add_zero] using add_mem_add hx (hA₀ n)
  have hS₀ (n : ℕ) : 0 ∈ S n := hSmono (Nat.zero_le n) (by simp [S])
  have hAS (n : ℕ) : A n ⊆ S (n+1) := fun x hx ↦ by
    rw [hstep]
    simpa only [zero_add] using add_mem_add (hS₀ n) hx
  have hSsub (n : ℕ) : (f '' S n) + (R n).val ⊆ U := by
    induction n with
    | zero => simp [S, R]
    | succ n ih =>
      rw [hstep, image_add, add_assoc]
      exact (add_subset_add Subset.rfl
        ((add_subset_add (image_subset_iff.mpr (hA n)) Subset.rfl).trans (hR n))).trans ih
  let W : Set E := ⋃ n, S n
  have hWsub : W ⊆ f ⁻¹' U := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hz := mem_of_mem_nhds (R n).property
    change f x ∈ U
    simpa only [add_zero] using hSsub n (add_mem_add (mem_image_of_mem f hn) hz)
  have hWbal : Balanced ℂ W := balanced_iUnion fun n ↦ by
    induction n with
    | zero => exact balanced_zero
    | succ n ih => exact ih.add (((p n).balanced_ball_zero 1).image (i n).toLinearMap)
  have hWconv : Convex ℝ W := hSmono.directed_le.convex_iUnion fun n ↦ by
    induction n with
    | zero => exact convex_singleton 0
    | succ n ih =>
      exact ih.add (((p n).convex_ball 0 1).linear_image ((i n).toLinearMap.restrictScalars ℝ))
  have hpre (k : ℕ) : (i k) ⁻¹' W ∈ 𝓝 (0 : X k) :=
    mem_of_superset (Seminorm.ball_mem_nhds (hp k) zero_lt_one) fun x hx ↦
      mem_iUnion.mpr ⟨k+1, hAS k (mem_image_of_mem _ hx)⟩
  have hWabs : Absorbent ℝ W := by
    apply absorbent_iff_eventually_nhdsNE_zero.mpr
    intro x
    obtain ⟨k, z, rfl⟩ := h.exhaustive x
    let : ContinuousSMul ℝ (X k) := IsScalarTower.continuousSMul ℂ
    filter_upwards [(absorbent_nhds_zero (𝕜 := ℝ) (hpre k)).eventually_nhdsNE_zero z] with a ha
    change i k (a • z) ∈ W at ha
    have hsmul : i k (a • z) = a • i k z := (i k).toLinearMap.map_smul_of_tower a z
    exact hsmul ▸ ha
  let g := gaugeSeminorm hWbal hWconv hWabs
  have hg (k : ℕ) : Continuous (g ∘ i k) := by
    apply Seminorm.continuous' (p := g.comp (i k).toLinearMap) (r := 1)
    refine mem_of_superset (hpre k) fun x hx ↦ ?_
    exact ((g.comp (i k).toLinearMap).mem_closedBall_zero).mpr (gauge_le_one_of_mem hx)
  have hgn := g.ball_mem_nhds (hP.continuous_seminorm ⟨g, hg⟩) zero_lt_one
  exact mem_of_superset hgn fun x hx ↦
    hWsub (setOfPred_gauge_lt_one_subset_self hWconv (mem_iUnion.mpr ⟨0, hS₀ 0⟩)
      hWabs (g.mem_ball_zero.mp hx))

/-- Paper: Theorem C.1.5.5, p. 665. A continuous linear surjection onto an LF-space
is open if its Hausdorff source is exhausted by rising continuous linear images of
Fréchet spaces. -/
theorem isOpenMap_of_surjective_toLF (hE : IsLFSpace E)
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hX : ∀ k, IsFrechetTVS (X k)) (u : ∀ k, X k →L[ℂ] F)
    (hr : ∀ k, range (u k) ⊆ range (u (k+1))) (hcov : ∀ x : F, ∃ k, x ∈ range (u k))
    (q : F →L[ℂ] E) (hq : Function.Surjective q) : IsOpenMap q := by
  obtain ⟨hT2, Y, _, _, _, hY, j, i, h⟩ := hE
  let : ∀ k, IsTopologicalAddGroup (Y k) := fun k ↦ (hY k).choose
  let : ∀ k, PolynormableSpace ℂ (Y k) := fun k ↦ (hY k).choose_spec.1
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hP.isTopologicalAddGroup
  let : ContinuousSMul ℂ E := hP.continuousSMul
  let e := q.toLinearMap.quotKerEquivOfSurjective hq
  let f (k : ℕ) := q.comp (u k)
  let K (k : ℕ) := (f k).ker
  let v (k : ℕ) : X k ⧸ K k →L[ℂ] E := (K k).liftQL (f k) le_rfl
  have hv (k : ℕ) (x : X k) : v k ((K k).mkQ x) = q (u k x) := rfl
  have hvrange (k : ℕ) : range (v k) = q '' range (u k) :=
    ((K k).mkQ_surjective.range_comp (v k)).symm.trans (range_comp q (u k))
  have hc : Continuous e.symm := by
    apply h.continuous_of_stages e.symm.toLinearMap
    intro n
    obtain ⟨k, w, hw⟩ := frechet_factorization
      (fun k ↦ isFrechetTVS_quotient (hX k) (K k) (f k).isClosed_ker) v
      (fun k ↦ LinearMap.ker_eq_bot.mp ((K k).ker_liftQ_eq_bot' (f k).toLinearMap rfl))
      (fun k ↦ by
        rw [hvrange, hvrange]
        exact image_mono (hr k))
      (fun y ↦ by
        obtain ⟨x, rfl⟩ := hq y
        obtain ⟨k, z, rfl⟩ := hcov x
        exact ⟨k, (K k).mkQ z, hv k z⟩)
      (hY n) (i n)
    -- The factor through the quotient stage induces a continuous map into F / ker(q).
    let g : X k ⧸ K k →L[ℂ] F ⧸ q.ker :=
      (K k).liftQL (q.ker.mkQL.comp (u k)) (by
        intro x hx
        change (Submodule.Quotient.mk (u k x) : F ⧸ q.ker) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact hx)
    have hg (z : X k ⧸ K k) : e.symm (v k z) = g z := by
      obtain ⟨x, rfl⟩ := (K k).mkQ_surjective z
      exact q.toLinearMap.quotKerEquivOfSurjective_symm_apply hq (u k x)
    have heq (x : Y n) : e.symm (i n x) = g (w x) :=
      (congrArg e.symm (DFunLike.congr_fun hw x).symm).trans (hg (w x))
    simpa only [Function.comp_def, LinearEquiv.coe_coe, heq] using g.continuous.comp w.continuous
  exact (e.toEquiv.continuous_symm_iff.mp hc).comp q.ker.isOpenQuotientMap_mkQ.isOpenMap

/-- Paper: Definition C.1.5.6, p. 666. Take the final locally convex topology on the
subspace from its intersections with the stages. Each intersection has the topology
induced from its own stage. -/
@[instance_reducible]
def limitSubspaceTopology (i : ∀ k, X k →L[ℂ] E) (F : Submodule ℂ E) : TopologicalSpace F :=
  let inclusion (k : ℕ) : F.comap (i k).toLinearMap →ₗ[ℂ] F :=
    (i k).toLinearMap.restrict (fun _ hx ↦ hx)
  locallyConvexFinalTopology inclusion

/-- Paper: Definition C.1.5.6, p. 666. A closed subspace of an LF-space is a limit
subspace if its inherited topology agrees with the locally convex inductive limit
topology from the chosen defining sequence. -/
def IsLimitSubspace (i : ∀ k, X k →L[ℂ] E) (F : Submodule ℂ E) : Prop :=
  IsClosed (F : Set E) ∧ (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F

set_option linter.unusedVariables false in
/-- Paper: Definition C.1.5.6, p. 666. The whole LF-space is a limit subspace for
every injective defining sequence. -/
theorem isLimitSubspace_top [T2Space E] (hX : ∀ k, IsFrechetTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i) :
    IsLimitSubspace i ⊤ := by
  refine ⟨by simpa only [Submodule.top_coe] using isClosed_univ, ?_⟩
  let F : Submodule ℂ E := ⊤
  let inclusion (k : ℕ) : F.comap (i k).toLinearMap →ₗ[ℂ] F :=
    (i k).toLinearMap.restrict (fun _ hx ↦ hx)
  let p : SeminormFamily ℂ E {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} :=
    Subtype.val
  let q : SeminormFamily ℂ F {q : Seminorm ℂ F // ∀ k, Continuous (q ∘ inclusion k)} :=
    Subtype.val
  have hp : WithSeminorms p := ⟨h.topology_eq⟩
  have hsub : WithSeminorms (p.comp F.subtype) := F.subtype.withSeminorms_induced hp
  -- Each generating seminorm in either family is a member of the other family.
  have hq : WithSeminorms q := by
    apply hsub.congr
    · intro s
      let lift : E →ₗ[ℂ] F := LinearMap.codRestrict F LinearMap.id (fun _ ↦ Submodule.mem_top)
      have hs : ∀ k, Continuous (s.val.comp lift ∘ i k) := by
        intro k
        have hlift : Continuous (fun x : X k ↦
            (⟨x, Submodule.mem_top⟩ : F.comap (i k).toLinearMap)) :=
          continuous_id.subtype_mk _
        exact (s.property k).comp hlift
      refine ⟨{⟨s.val.comp lift, hs⟩}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      exact le_rfl
    · intro a
      have ha : ∀ k, Continuous ((p.comp F.subtype) a ∘ inclusion k) := by
        intro k
        exact (a.property k).comp continuous_subtype_val
      refine ⟨{⟨(p.comp F.subtype) a, ha⟩}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      exact le_rfl
  exact hq.topology_eq_withSeminorms

/-- Lower semicontinuous seminorms on an LF-space are continuous, since their restrictions
to its Fréchet stages are continuous by the Baire category theorem. -/
theorem IsLFSpace.barrelled {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsLFSpace E) : BarrelledSpace ℂ E := by
  obtain ⟨_, X, _, _, _, hX, j, i, h⟩ := hE
  refine ⟨fun p hp ↦ ?_⟩
  have hP : WithSeminorms
      (Subtype.val : {q : Seminorm ℂ E // ∀ k, Continuous (q ∘ (i k).toLinearMap)} →
        Seminorm ℂ E) := ⟨h.topology_eq⟩
  apply hP.continuous_seminorm (i := ⟨p, ?_⟩)
  intro k
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hX k
  let : UniformSpace (X k) := IsTopologicalAddGroup.rightUniformSpace (X k)
  let : IsUniformAddGroup (X k) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (X k) := hcomplete
  let : ContinuousSMul ℂ (X k) := PolynormableSpace.continuousSMul ℂ (X k)
  have : (uniformity (X k)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero (X k)]
    infer_instance
  have : BaireSpace (X k) := by
    let := UniformSpace.metricSpace (X k)
    infer_instance
  exact (p.comp (i k).toLinearMap).continuous_of_lowerSemicontinuous (hp.comp (i k).continuous)

/-- Paper: Example C.1.5.7, p. 666. Some countable locally convex direct sum of Banach
spaces has a closed linear subspace which, in its subspace topology, is not an LF-space. -/
theorem exists_closed_subspace_not_LF :
    ∃ (Y : ℕ → Type) (_ : ∀ k, NormedAddCommGroup (Y k)) (_ : ∀ k, NormedSpace ℂ (Y k))
      (_ : ∀ k, CompleteSpace (Y k)),
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
      ∃ F : Submodule ℂ (⨁ k, Y k), IsClosed (F : Set (⨁ k, Y k)) ∧ ¬ IsLFSpace F := by
  classical
  let B : Type := lp (fun _ : ℕ × ℕ ↦ ℂ) ⊤
  let Y : ℕ → Type := fun _ ↦ B
  refine ⟨Y, fun _ ↦ inferInstanceAs (NormedAddCommGroup B),
    fun _ ↦ inferInstanceAs (NormedSpace ℂ B), fun _ ↦ inferInstanceAs (CompleteSpace B), ?_⟩
  let D := ⨁ k, Y k
  let lof := DirectSum.lof ℂ ℕ Y
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  let P : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  let : PolynormableSpace ℂ D := hP.toPolynormableSpace
  have hlof (k : ℕ) : Continuous (lof k) :=
    hP.continuous_of_continuous_comp _ fun p ↦ p.property k
  let coord (k : ℕ) : D →L[ℂ] B := ⟨DirectSum.component ℂ ℕ Y k, by
    apply (norm_withSeminorms ℂ B).continuous_of_continuous_comp
    intro i
    apply hP.continuous_seminorm (i := ⟨_, ?_⟩)
    intro l
    change Continuous (fun x : Y l ↦ ‖DirectSum.component ℂ ℕ Y k (lof l x)‖)
    by_cases h : l = k
    · subst l
      simpa only [lof, DirectSum.component.of, dite_true]
        using (continuous_norm : Continuous fun x : B ↦ ‖x‖)
    · simpa only [lof, DirectSum.component.of, h, dite_false, norm_zero] using (continuous_const : Continuous fun _ : B ↦ (0 : ℝ))⟩
  let ev (k : ℕ) (j : ℕ × ℕ) : D →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ × ℕ ↦ ℂ) ⊤ j).comp (coord k)
  have hev (k : ℕ) (j : ℕ × ℕ) (x : D) : ev k j x = x k j := rfl
  -- The (n,m) entry of the zeroth summand is (m+1) times that of the (n+1)st summand.
  let eqn (j : ℕ × ℕ) : D →L[ℂ] ℂ := ev 0 j - ((j.2 + 1 : ℕ) : ℂ) • ev (j.1 + 1) j
  let F : Submodule ℂ D := ⨅ j, (eqn j).ker
  have hF (x : D) : x ∈ F ↔ ∀ j : ℕ × ℕ, x 0 j = ((j.2 + 1 : ℕ) : ℂ) * x (j.1 + 1) j := by
    simp [F, eqn, Submodule.mem_iInf, LinearMap.mem_ker, hev, sub_eq_zero]
  refine ⟨F, ?_, ?_⟩
  · change IsClosed (↑(⨅ j, (eqn j).ker) : Set D)
    rw [Submodule.coe_iInf]
    exact isClosed_iInter fun j ↦ (eqn j).isClosed_ker
  intro hLF
  let : BarrelledSpace ℂ F := hLF.barrelled
  let p (j : ℕ × ℕ) : Seminorm ℂ F := (normSeminorm ℂ ℂ).comp
    (((j.1 + 1 : ℕ) : ℂ) • (ev 0 j).toLinearMap.comp F.subtype)
  have hp (j : ℕ × ℕ) (x : F) : p j x = (j.1 + 1 : ℕ) * ‖x.val 0 j‖ := by
    change ‖((j.1 + 1 : ℕ) : ℂ) * ev 0 j x.val‖ = _
    rw [norm_mul, Complex.norm_natCast, hev]
  have hpcont (j : ℕ × ℕ) : Continuous (p j) := by
    exact (((ev 0 j).continuous.comp continuous_subtype_val).const_mul _).norm
  -- Every vector has only finitely many nonzero rows in the zeroth summand.
  have hbdd : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr fun x ↦ by
    refine ⟨((x.val.support.sup (id : ℕ → ℕ) : ℕ) : ℝ) * ‖x.val 0‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    change p j x ≤ _
    rw [hp]
    by_cases hj : j.1 + 1 ∈ x.val.support
    · exact mul_le_mul (Nat.cast_le.mpr (Finset.le_sup (f := id) hj))
        (lp.norm_apply_le_norm ENNReal.top_ne_zero (x.val 0) j) (norm_nonneg _) (by positivity)
    · have hzero := DFinsupp.notMem_support_iff.mp hj
      rw [(hF x.val).mp x.property j, hzero]
      simp
      positivity
  let q : Seminorm ℂ F := ⨆ j, p j
  have hq : Continuous q := by
    simpa only [q, Seminorm.coe_iSup_eq hbdd] using Seminorm.continuous_iSup p hpcont hbdd
  have hball := q.ball_mem_nhds hq (r := 1) zero_lt_one
  rw [show 𝓝 (0 : F) = comap Subtype.val (𝓝 (0 : D)) from nhds_subtype_eq_comap] at hball
  obtain ⟨U, hU, hUsub⟩ := Filter.mem_comap.mp hball
  obtain ⟨s, hs, hsU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ D).mem_iff.mp hU
  choose C hC hsC using fun k ↦
    (s.comp (lof k)).bound_of_continuous_normedSpace (hs.comp (hlof k))
  -- In any ambient zero-neighborhood, put a small entry in a sufficiently high row and
  -- use a sufficiently large column to make its required auxiliary coordinate small too.
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C 0)
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * C (n + 1))
  let j : ℕ × ℕ := (n, m)
  let a : ℂ := ((n + 1 : ℕ) : ℂ)⁻¹
  let b : ℂ := a / ((m + 1 : ℕ) : ℂ)
  let v : B := lp.single ⊤ j a
  let w : B := lp.single ⊤ j b
  let x : D := lof 0 v + lof (n + 1) w
  have hx0 : x 0 = v := by
    simp [x, lof, DirectSum.lof_eq_of, DirectSum.add_apply, DirectSum.of_eq_of_ne]
  have hxk (k : ℕ) : x (k + 1) = if k = n then w else 0 := by
    by_cases hk : k = n
    · subst k
      simp [x, lof, DirectSum.lof_eq_of, DirectSum.add_apply, DirectSum.of_eq_of_ne]
    · simp [x, lof, DirectSum.lof_eq_of, DirectSum.add_apply, DirectSum.of_eq_of_ne, hk]
  have hxF : x ∈ F := by
    rw [hF]
    intro l
    rw [hx0, hxk]
    by_cases hlj : l = j
    · subst l
      have hm0 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      simpa [j, v, w, b] using (mul_div_cancel₀ a hm0).symm
    · rw [show v l = 0 from lp.single_apply_ne _ _ _ hlj]
      split_ifs
      · rw [show w l = 0 from lp.single_apply_ne _ _ _ hlj, mul_zero]
      · simp
  have ha : ‖a‖ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    change ‖((n + 1 : ℕ) : ℂ)⁻¹‖ = _
    rw [norm_inv, Complex.norm_natCast]
  have ha_le : ‖a‖ ≤ 1 := by
    rw [ha, inv_le_one₀ (by positivity)]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hxU : x ∈ U := by
    apply hsU
    rw [Seminorm.mem_ball_zero]
    calc
      s x ≤ s (lof 0 v) + s (lof (n + 1) w) := map_add_le_add _ _ _
      _ ≤ C 0 * ‖v‖ + C (n + 1) * ‖w‖ := add_le_add (hsC 0 v) (hsC (n + 1) w)
      _ < 1 := by
        rw [lp.norm_single (by simp : (0 : ENNReal) < ⊤),
          lp.norm_single (by simp : (0 : ENNReal) < ⊤)]
        have hfirst : C 0 * ‖a‖ < 1 / 2 := by
          rw [ha, ← div_eq_mul_inv, div_lt_iff₀ (by positivity), Nat.cast_succ]
          linarith
        have hsecond : C (n + 1) * ‖b‖ < 1 / 2 := by
          change C (n + 1) * ‖a / ((m + 1 : ℕ) : ℂ)‖ < 1 / 2
          rw [norm_div, Complex.norm_natCast, ← mul_div_assoc,
            div_lt_iff₀ (by positivity), Nat.cast_succ]
          have hbound := mul_le_of_le_one_right (hC (n + 1)).le ha_le
          linarith
        linarith
  have hsmall : q ⟨x, hxF⟩ < 1 := by
    simpa only [Seminorm.mem_ball_zero] using hUsub (a := ⟨x, hxF⟩) hxU
  have hlarge : p j ⟨x, hxF⟩ = 1 := by
    rw [hp]
    change ((n + 1 : ℕ) : ℝ) * ‖x 0 j‖ = 1
    rw [hx0]
    change ((n + 1 : ℕ) : ℝ) * ‖lp.single (E := fun _ : ℕ × ℕ ↦ ℂ) ⊤ j a j‖ = 1
    rw [lp.single_apply_self, ha]
    exact mul_inv_cancel₀ (by positivity)
  exact (not_lt_of_ge ((le_ciSup hbdd j) ⟨x, hxF⟩)) (hlarge ▸ hsmall)

-- TODO(paper-gap): Footnotes 2–4 on p. 667 leave the explicit Köthe space, the two
-- strong topologies, and the justification for the subspace example unspecified.

/-- Paper: Definition C.1.5.8, p. 667. The map σ on the direct sum is the identity
minus the shift that sends the kth summand to the next one by its transition map. -/
def directSumDifference (j : ∀ k, X k →L[ℂ] X (k+1)) : (⨁ k, X k) →ₗ[ℂ] (⨁ k, X k) :=
  LinearMap.id - DirectSum.toModule ℂ ℕ _ (fun k ↦
    (DirectSum.lof ℂ ℕ X (k+1)).comp (j k).toLinearMap)

/-- Paper: Definition C.1.5.8, p. 667. The zeroth coordinate is unchanged and
coordinate k+1 subtracts the image of coordinate k under the kth transition map. -/
theorem directSumDifference_apply (j : ∀ k, X k →L[ℂ] X (k+1)) (x : ⨁ k, X k) :
    directSumDifference j x 0 = x 0 ∧
      ∀ k, directSumDifference j x (k+1) = x (k+1) - j k (x k) := by
  let shift := DirectSum.toModule ℂ ℕ (⨁ k, X k) (fun k ↦
    (DirectSum.lof ℂ ℕ X (k+1)).comp (j k).toLinearMap)
  have hzero : shift x 0 = 0 := by
    suffices (DirectSum.component ℂ ℕ X 0).comp shift = 0 from LinearMap.congr_fun this x
    apply DirectSum.linearMap_ext
    intro i
    ext y : 1
    simp [shift, DirectSum.component.of]
  have hsucc (k : ℕ) : shift x (k+1) = j k (x k) := by
    suffices (DirectSum.component ℂ ℕ X (k+1)).comp shift =
        (j k).toLinearMap.comp (DirectSum.component ℂ ℕ X k) from LinearMap.congr_fun this x
    apply DirectSum.linearMap_ext
    intro i
    ext y : 1
    by_cases h : i = k
    · subst i
      simp [shift]
    · simp [shift, DirectSum.component.of, h]
  change (x - shift x) 0 = x 0 ∧
    ∀ k, (x - shift x) (k+1) = x (k+1) - j k (x k)
  simp [DirectSum.sub_apply, hzero, hsucc]

/-- Paper: Definition C.1.5.8, p. 667. A countable system of Hausdorff locally convex
spaces is acyclic when σ is a closed topological embedding of its locally convex direct sum. -/
def IsAcyclicSystem (j : ∀ k, X k →L[ℂ] X (k+1)) : Prop :=
  letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  IsClosedEmbedding (directSumDifference j)

/-- Extend the sum of the current seminorm and the prescribed seminorm to the next stage. -/
private theorem exists_strictSystem_seminorms
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k))
    (p : ∀ k, Seminorm ℂ (X k)) (hp : ∀ k, Continuous (p k)) :
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ k, (r (k+1)).comp (j k).toLinearMap = r k + p k := by
  choose next hnext hcomp using fun k (s : {s : Seminorm ℂ (X k) // Continuous s}) ↦
    exists_seminorm_extension (f := (j k).toLinearMap) (hj k).isInducing
      (show Continuous (s.val + p k) from s.property.add (hp k))
  let r : ∀ k, {s : Seminorm ℂ (X k) // Continuous s} :=
    Nat.rec ⟨0, continuous_const⟩ (fun k s ↦ ⟨next k s, hnext k s⟩)
  exact ⟨fun k ↦ (r k).val, fun k ↦ (r k).property, fun k ↦ hcomp k (r k)⟩

/-- The difference coordinates after a cutoff bound the input seminorms from the cutoff on.
The restriction identity makes the successive triangle inequalities telescope. -/
private theorem directSumDifference_tail_bound
    (j : ∀ k, X k →L[ℂ] X (k+1)) (p r : ∀ k, Seminorm ℂ (X k))
    (hr : ∀ k, (r (k+1)).comp (j k).toLinearMap = r k + p k)
    (x : ⨁ k, X k) (a : ℕ) [∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)] :
    directSumSeminorm (fun k ↦ if a ≤ k then p k else 0) x + r a (x a) ≤
      directSumSeminorm (fun k ↦ if a < k then r k else 0) (directSumDifference j x) := by
  obtain ⟨b, hb⟩ := Finset.exists_nat_subset_range (insert a x.support)
  have hab : a ≤ b := Nat.le_of_lt (Finset.mem_range.mp (hb (Finset.mem_insert_self _ _)))
  have hs : x.support ⊆ Finset.range b := fun _ hk ↦ hb (Finset.mem_insert_of_mem hk)
  have hxb : x b = 0 := DFinsupp.notMem_support_iff.mp fun h ↦
    (Nat.lt_irrefl b) (Finset.mem_range.mp (hs h))
  let y := directSumDifference j x
  have hstep (k : ℕ) : r k (x k) + p k (x k) ≤ r (k+1) (y (k+1)) + r (k+1) (x (k+1)) := by
    have heq := DFunLike.congr_fun (hr k) (x k)
    change r (k+1) (j k (x k)) = r k (x k) + p k (x k) at heq
    have hdiff : j k (x k) - x (k+1) = -(y (k+1)) := by
      change _ = -(directSumDifference j x (k+1))
      rw [(directSumDifference_apply j x).2 k, neg_sub]
    rw [← heq, add_comm (r (k+1) (y (k+1)))]
    simpa only [hdiff, map_neg_eq_map] using le_map_add_map_sub (r (k+1)) (j k (x k)) (x (k+1))
  have hsum (n : ℕ) (hn : a ≤ n) :
      (∑ k ∈ Finset.Ico a n, p k (x k)) + r a (x a) ≤
        (∑ k ∈ Finset.Ico a n, r (k+1) (y (k+1))) + r n (x n) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn]
      linarith only [ih, hstep n]
  have hinput : directSumSeminorm (fun k ↦ if a ≤ k then p k else 0) x =
      ∑ k ∈ Finset.Ico a b, p k (x k) := by
    rw [directSumSeminorm_apply _ _ _ hs]
    simp only [DFunLike.ite_apply, zero_apply, ← Finset.sum_filter]
    congr 1
    ext k
    simp [and_comm]
  have houtput : (∑ k ∈ Finset.Ico a b, r (k+1) (y (k+1))) ≤
      directSumSeminorm (fun k ↦ if a < k then r k else 0) y := by
    rw [Finset.sum_Ico_add' (fun k ↦ r k (y k)) a b 1]
    refine le_trans ?_ (sum_le_directSumSeminorm _ y (Finset.Ico (a+1) (b+1)))
    apply Finset.sum_le_sum
    intro k hk
    simp only [ite_eq_left (Nat.lt_of_succ_le (Finset.mem_Ico.mp hk).1), le_refl]
  rw [hinput]
  exact (hsum b hab).trans (by simpa only [hxb, map_zero, add_zero] using houtput)

/-- Paper: §C.1.5.1 (after Definition C.1.5.8), p. 667. A strict sequence of Fréchet
spaces is acyclic. -/
theorem isAcyclicSystem_of_strict_frechet (hX : ∀ k, IsFrechetTVS (X k))
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k)) : IsAcyclicSystem j := by
  let _ : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0) := fun _ _ ↦ Classical.propDecidable _
  choose hadd hpoly hmetric _ using hX
  let _ : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let _ : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let _ : ∀ k, MetrizableSpace (X k) := hmetric
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let _ : TopologicalSpace D := locallyConvexFinalTopology lof
  let P : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  let _ : IsTopologicalAddGroup D := hP.isTopologicalAddGroup
  let _ : PolynormableSpace ℂ D := hP.toPolynormableSpace
  have hlof (k : ℕ) : Continuous (lof k) :=
    hP.continuous_of_continuous_comp _ fun p ↦ p.property k
  have hcontinuous {F : Type _} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
      [PolynormableSpace ℂ F] (f : D →ₗ[ℂ] F) (hf : ∀ k, Continuous (f ∘ lof k)) :
      Continuous f := by
    apply (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp
    intro p
    exact hP.continuous_seminorm ⟨p.val.comp f, fun k ↦ p.property.comp (hf k)⟩
  have htailContinuous (a : ℕ) (r : ∀ k, Seminorm ℂ (X k)) (hr : ∀ k, Continuous (r k)) :
      Continuous (directSumSeminorm (fun k ↦ if a < k then r k else 0)) := by
    let s (k : ℕ) : Seminorm ℂ (X k) := if a < k then r k else 0
    refine hP.continuous_seminorm ⟨directSumSeminorm s, fun k ↦ ?_⟩
    have heq : (fun z : X k ↦ directSumSeminorm s (lof k z)) = (s k : X k → ℝ) :=
      funext fun z ↦ directSumSeminorm_lof s k z
    change Continuous (fun z : X k ↦ directSumSeminorm s (lof k z))
    rw [heq]
    dsimp only [s]
    split
    · exact hr k
    · exact continuous_zero
  let σ : D →ₗ[ℂ] D := directSumDifference j
  have hσ : Continuous σ := by
    apply hcontinuous
    intro k
    have heq (z : X k) : σ (lof k z) = lof k z - lof (k+1) (j k z) := by
      change directSumDifference j (DirectSum.lof ℂ ℕ X k z) = _
      rw [directSumDifference, LinearMap.sub_apply, LinearMap.id_apply, DirectSum.toModule_lof]
      rfl
    change Continuous (fun z : X k ↦ σ (lof k z))
    simp_rw [heq]
    exact (hlof k).sub ((hlof (k+1)).comp (j k).continuous)
  let coordinate (k : ℕ) : D →ₗ[ℂ] X k := DirectSum.component ℂ ℕ X k
  have hcoordinate (k : ℕ) : Continuous (coordinate k) := by
    apply hcontinuous
    intro i
    by_cases h : i = k
    · subst i
      have heq : coordinate k ∘ lof k = id :=
        funext fun z ↦ DirectSum.component.lof_self ℂ k z
      rw [heq]
      exact continuous_id
    · have hz : coordinate k ∘ lof i = fun _ ↦ 0 :=
        funext fun z ↦ (DirectSum.component.of ℂ k i z).trans (dite_eq_right h)
      rw [hz]
      exact continuous_const
  let partialSum : ∀ k, D →L[ℂ] X k :=
    Nat.rec ⟨coordinate 0, hcoordinate 0⟩
      (fun k f ↦ (j k).comp f + ⟨coordinate (k+1), hcoordinate (k+1)⟩)
  have hpartialSum (x : D) (k : ℕ) : partialSum k (σ x) = x k := by
    induction k with
    | zero => exact (directSumDifference_apply j x).1
    | succ k ih =>
      change j k (partialSum k (σ x)) + σ x (k+1) = x (k+1)
      rw [ih, (directSumDifference_apply j x).2 k, add_sub_cancel]
  have hinj : Function.Injective σ := fun x y h ↦ DFinsupp.ext fun k ↦ by
    rw [← hpartialSum x k, h, hpartialSum y k]
  change IsClosedEmbedding σ
  constructor
  · let e := LinearEquiv.ofInjective σ hinj
    have he : Continuous e := hσ.subtype_mk _
    have heInv : Continuous e.symm := by
      apply hP.continuous_of_continuous_comp
      intro p
      -- Bound the inverse pullback of each generating seminorm by a continuous seminorm.
      let s (k : ℕ) : Seminorm ℂ (X k) := p.val.comp (lof k)
      obtain ⟨r, hr, hrcomp⟩ := exists_strictSystem_seminorms j hj s p.property
      let q := directSumSeminorm (fun k ↦ if 0 < k then r k else 0)
      have hq : Continuous q := htailContinuous 0 r hr
      have hqsub : Continuous (q.comp σ.range.subtype) := hq.comp continuous_subtype_val
      refine Seminorm.continuous_of_le hqsub fun y ↦ ?_
      let x := e.symm y
      have hx : σ x = (y : D) := congrArg Subtype.val (e.apply_symm_apply y)
      change p.val x ≤ q (y : D)
      rw [← hx]
      have hbound : directSumSeminorm s x ≤ q (σ x) := by
        have hb := directSumDifference_tail_bound j s r hrcomp x 0
        simp only [Nat.zero_le, ite_true] at hb
        exact (le_add_of_nonneg_right (apply_nonneg (r 0) (x 0))).trans hb
      refine le_trans ?_ hbound
      rw [directSumSeminorm_apply _ _ x.support (Finset.Subset.refl _)]
      have hsum := @norm_sum_le ℕ D p.val.toAddGroupSeminorm.toSeminormedAddCommGroup
        x.support (fun k ↦ lof k (x k))
      change p.val (∑ k ∈ x.support, lof k (x k)) ≤ ∑ k ∈ x.support, p.val (lof k (x k)) at hsum
      have hdecomp : (∑ k ∈ x.support, lof k (x k)) = x := DirectSum.sum_support_of x
      rwa [hdecomp] at hsum
    let homeo : D ≃ₜ σ.range := ⟨e.toEquiv, he, heInv⟩
    exact IsEmbedding.subtypeVal.comp homeo.isEmbedding
  · rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range y.support
    -- Every tail seminorm starting after the support vanishes on y.
    have hzero : partialSum n y = 0 := by
      by_contra hne
      obtain ⟨p, hp⟩ := (PolynormableSpace.withSeminorms ℂ (X n)).separating_of_T1 _ hne
      let s (k : ℕ) : Seminorm ℂ (X k) := Pi.single (M := fun k ↦ Seminorm ℂ (X k)) n p.val k
      have hs (k : ℕ) : Continuous (s k) := by
        by_cases h : k = n
        · subst k
          simpa only [s, Pi.single_eq_same] using p.property
        · have hsk : s k = 0 := Pi.single_eq_of_ne h _
          rw [hsk]
          exact continuous_zero
      obtain ⟨r, hr, hrcomp⟩ := exists_strictSystem_seminorms j hj s hs
      let q := directSumSeminorm (fun k ↦ if n < k then r k else 0)
      have hq : Continuous q := htailContinuous n r hr
      have hclosed : IsClosed {z : D | p.val (partialSum n z) ≤ q z} :=
        isClosed_le (p.property.comp (partialSum n).continuous) hq
      have hle : p.val (partialSum n y) ≤ q y := hclosed.closure_subset_iff.mpr (by
        rintro _ ⟨x, rfl⟩
        change p.val (partialSum n (σ x)) ≤ q (σ x)
        rw [hpartialSum]
        have hx := sum_le_directSumSeminorm (fun k ↦ if n ≤ k then s k else 0) x {n}
        simp only [Finset.sum_singleton, le_refl, ite_true, s, Pi.single_eq_same] at hx
        exact hx.trans ((le_add_of_nonneg_right (apply_nonneg (r n) (x n))).trans
          (directSumDifference_tail_bound j s r hrcomp x n))) hy
      have hqy : q y = 0 := by
        rw [directSumSeminorm_apply _ _ _ hn]
        apply Finset.sum_eq_zero
        intro k hk
        simp [not_lt_of_ge (Finset.mem_range.mp hk).le]
      exact hp (le_antisymm (hle.trans_eq hqy) (apply_nonneg p.val _))
    have htail (k : ℕ) (hk : n ≤ k) : partialSum k y = 0 := by
      induction k, hk using Nat.le_induction with
      | base => exact hzero
      | succ k hk ih =>
        have hky : y (k+1) = 0 := DFinsupp.notMem_support_iff.mp fun hm ↦
          (Nat.not_lt_of_ge (Nat.le_succ_of_le hk)) (Finset.mem_range.mp (hn hm))
        change j k (partialSum k y) + y (k+1) = 0
        rw [ih, map_zero, hky, add_zero]
    let x : D := DFinsupp.mk (Finset.range n) (fun k ↦ partialSum k y)
    have hx (k : ℕ) : x k = partialSum k y := by
      change (DFinsupp.mk (Finset.range n) (fun k ↦ partialSum k y)) k = _
      rw [DFinsupp.mk_apply]
      split
      · rfl
      · exact (htail k (Nat.le_of_not_gt fun h ↦ ‹k ∉ Finset.range n›
          (Finset.mem_range.mpr h))).symm
    refine ⟨x, DFinsupp.ext fun k ↦ ?_⟩
    cases k with
    | zero => exact (directSumDifference_apply j x).1.trans (hx 0)
    | succ k =>
      rw [(directSumDifference_apply j x).2 k, hx, hx]
      change j k (partialSum k y) + y (k+1) - j k (partialSum k y) = y (k+1)
      exact add_sub_cancel_left _ _

end CountableLimits

section Lifting

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: Definition C.1.5.9, p. 667. A set in the target can be lifted when it is
contained in the image of a bounded set in the source. Such a set is itself bounded. -/
def HasBoundedLift (f : E →L[ℂ] F) (B : Set F) : Prop :=
  ∃ A : Set E, IsVonNBounded ℂ A ∧ B ⊆ f '' A

/-- Paper: Definition C.1.5.9, p. 667. A continuous linear map lifts bounded sets if
each bounded set in its target has a bounded lift. -/
def LiftsBoundedSets (f : E →L[ℂ] F) : Prop :=
  ∀ B : Set F, IsVonNBounded ℂ B → HasBoundedLift f B

/-- Paper: Definition C.1.5.9, p. 667. A bounded lift can be chosen with image exactly
the specified set. -/
theorem hasBoundedLift_iff_image (f : E →L[ℂ] F) (B : Set F) :
    HasBoundedLift f B ↔ ∃ A : Set E, IsVonNBounded ℂ A ∧ f '' A = B := by
  constructor
  · rintro ⟨A, hA, hB⟩
    refine ⟨A ∩ f ⁻¹' B, hA.subset inter_subset_left, ?_⟩
    rw [image_inter_preimage, inter_eq_right.mpr hB]
  · rintro ⟨A, hA, hB⟩
    exact ⟨A, hA, hB.ge⟩

/-- Paper: Definition C.1.5.9, p. 667. The identity map lifts bounded subsets. -/
theorem liftsBoundedSets_id : LiftsBoundedSets (ContinuousLinearMap.id ℂ E) := by
  intro B hB
  exact ⟨B, hB, fun x hx ↦ ⟨x, hx, rfl⟩⟩

end Lifting

/-- Paper: §C.1.5.1 (Schwartz spaces), p. 667. For each continuous seminorm there is
a zero-neighborhood with precompact image in the corresponding normed quotient.
Deviation: A continuous seminorm is the gauge of its closed unit ball. Total boundedness
for its pseudometric expresses precompactness in the Hausdorff normed quotient. -/
def IsSchwartzTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  PolynormableSpace ℂ E ∧ ∀ p : Seminorm ℂ E, Continuous p → ∃ V ∈ 𝓝 (0 : E),
    @TotallyBounded E p.toSeminormedAddCommGroup.toUniformSpace V

/-- Paper: §C.1.5.1 (Schwartz spaces), p. 667. A normed complex space is Schwartz
exactly when it is finite-dimensional.
Deviation: Sanity check using the norm seminorm in the definition. -/
theorem isSchwartzTVS_iff_finiteDimensional (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsSchwartzTVS E ↔ FiniteDimensional ℂ E := by
  constructor
  · intro h
    obtain ⟨V, hV, htb⟩ := h.2 (normSeminorm ℂ E) continuous_norm
    apply FiniteDimensional.of_totallyBounded_nhds_zero ℂ hV
    have hu : (inferInstance : UniformSpace E) =
        (normSeminorm ℂ E).toSeminormedAddCommGroup.toUniformSpace := by
      simpa using (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf _).mp
        (norm_withSeminorms ℂ E)
    exact (congrArg (fun u : UniformSpace E ↦ @TotallyBounded E u V) hu).mpr htb
  · intro hE
    have : ProperSpace E := FiniteDimensional.proper ℂ E
    refine ⟨inferInstance, fun p hp ↦
      ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one, ?_⟩⟩
    -- The norm-compact unit ball stays compact for each continuous seminorm topology.
    let t (s : {s : Seminorm ℂ E // Continuous s}) :=
      s.val.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
    have hle : (inferInstance : TopologicalSpace E) ≤ t ⟨p, hp⟩ :=
      (PolynormableSpace.withSeminorms ℂ E).topologicalSpace_eq_iInf.le.trans
        (iInf_le t ⟨p, hp⟩)
    have hc : @Continuous E E _ (t ⟨p, hp⟩) id := continuous_id_of_le hle
    apply @IsCompact.totallyBounded E p.toSeminormedAddCommGroup.toUniformSpace
    have himg := @IsCompact.image E E _ (t ⟨p, hp⟩) _ id (isCompact_closedBall (0 : E) 1) hc
    rw [Set.image_id] at himg
    exact himg

-- TODO(paper-gap): Example C.1.5.10 requires nuclear locally convex spaces from §C.2.4.

section QuotientStages

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {X : ℕ → Type*} [∀ k, AddCommGroup (X k)]
  [∀ k, Module ℂ (X k)] [∀ k, TopologicalSpace (X k)]

/-- The kernel of the map from a stage into the quotient of the limit. -/
abbrev limitStageKernel (i : ∀ k, X k →L[ℂ] E) (F : Submodule ℂ E) (k : ℕ) :=
  (F.mkQL.comp (i k)).ker

/-- The map from a quotient stage into the quotient of the limit. -/
def limitQuotientStageMap (i : ∀ k, X k →L[ℂ] E) (F : Submodule ℂ E) (k : ℕ) :
    X k ⧸ limitStageKernel i F k →L[ℂ] E ⧸ F :=
  (limitStageKernel i F k).liftQL (F.mkQL.comp (i k)) le_rfl

/-- The transition map induced by the original transition between consecutive quotient stages. -/
def limitQuotientTransition
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (F : Submodule ℂ E) (k : ℕ) :
    X k ⧸ limitStageKernel i F k →L[ℂ] X (k+1) ⧸ limitStageKernel i F (k+1) :=
  (limitStageKernel i F k).liftQL ((limitStageKernel i F (k+1)).mkQL.comp (j k)) (by
    intro x hx
    change (limitStageKernel i F (k+1)).mkQ (j k x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change F.mkQ (i (k+1) (j k x)) = 0
    rw [show i (k+1) (j k x) = i k x from DFunLike.congr_fun (h.compatible k) x]
    exact hx)

omit [IsTopologicalAddGroup E] in
/-- Passing to a quotient of the limit gives the limit of the corresponding quotient stages.
The final topology identity also holds for a non-Hausdorff quotient. -/
theorem isInjectiveLCLimit_quotientStages [ContinuousSMul ℂ E]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (F : Submodule ℂ E) :
    IsInjectiveLCLimit (limitQuotientTransition h F) (limitQuotientStageMap i F) := by
  let K := limitStageKernel i F
  let q := limitQuotientStageMap i F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact LinearMap.ker_eq_bot.mp ((K k).ker_liftQ_eq_bot' (F.mkQL.comp (i k)).toLinearMap rfl)
  · intro k
    ext z
    obtain ⟨x, rfl⟩ := (K k).mkQ_surjective z
    exact congrArg F.mkQ (DFunLike.congr_fun (h.compatible k) x)
  · intro z
    obtain ⟨x, rfl⟩ := F.mkQ_surjective z
    obtain ⟨k, y, rfl⟩ := h.exhaustive x
    exact ⟨k, (K k).mkQ y, rfl⟩
  · have hP : WithSeminorms
        (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
      ⟨h.topology_eq⟩
    let : PolynormableSpace ℂ E := hP.toPolynormableSpace
    let : PolynormableSpace ℂ (E ⧸ F) := polynormableSpace_quotient F
    have hseminorms : (fun p : Seminorm ℂ (E ⧸ F) ↦ ∀ k, Continuous (p ∘ q k)) =
        (fun p : Seminorm ℂ (E ⧸ F) ↦ Continuous p) := by
      funext p
      apply propext
      refine ⟨fun hp ↦ F.isQuotientMap_mkQL.continuous_iff.mpr ?_,
        fun hp k ↦ hp.comp (q k).continuous⟩
      exact hP.continuous_seminorm ⟨p.comp F.mkQ, fun k ↦ (hp k).comp (K k).mkQL.continuous⟩
    change (inferInstance : TopologicalSpace (E ⧸ F)) = (SeminormFamily.moduleFilterBasis
      (Subtype.val : {p : Seminorm ℂ (E ⧸ F) // ∀ k, Continuous (p ∘ q k)} → _)).topology
    rw [hseminorms]
    exact (PolynormableSpace.withSeminorms ℂ (E ⧸ F)).withSeminorms_eq

end QuotientStages

/-- A quotient retains the Schwartz property. Pull back each continuous seminorm and
send a neighborhood that is totally bounded for the pullback to the quotient. -/
private theorem isSchwartzTVS_quotient
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (hE : IsSchwartzTVS E) (F : Submodule ℂ E) :
    IsSchwartzTVS (E ⧸ F) := by
  let : PolynormableSpace ℂ E := hE.1
  refine ⟨polynormableSpace_quotient F, fun p hp ↦ ?_⟩
  let q := p.comp F.mkQ
  obtain ⟨V, hV, htotal⟩ := hE.2 q (hp.comp F.mkQL.continuous)
  refine ⟨F.mkQ '' V, ?_, ?_⟩
  · rw [← map_zero F.mkQ, ← F.isOpenQuotientMap_mkQ.map_nhds_eq 0]
    exact Filter.image_mem_map hV
  · let := q.toSeminormedAddCommGroup
    let := p.toSeminormedAddCommGroup
    have hisom : Isometry F.mkQ := Isometry.of_dist_eq fun x y ↦ by
      rw [dist_eq_norm_sub, dist_eq_norm_sub]
      change p (F.mkQ x - F.mkQ y) = p (F.mkQ (x - y))
      rw [map_sub F.mkQ]
    exact htotal.image hisom.uniformContinuous

/-- Bounded subsets of a complete Schwartz space have compact closure. Every continuous
seminorm gives finite ball covers, since a bounded set is absorbed by a neighborhood that
is totally bounded for that seminorm. -/
private theorem isCompact_closure_of_schwartz
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] (hS : IsSchwartzTVS E) {B : Set E} (hB : IsVonNBounded ℂ B) :
    IsCompact (closure B) := by
  let : PolynormableSpace ℂ E := hS.1
  suffices htotal : TotallyBounded B from htotal.closure.isCompact_of_isClosed isClosed_closure
  apply (PolynormableSpace.hasBasis_zero_ball ℂ E).uniformity_of_nhds_zero_swapped.totallyBounded_iff.mpr
  intro p hp
  obtain ⟨V, hV, htotal⟩ := hS.2 p hp
  obtain ⟨r, hr, hsub⟩ := (hB hV).exists_pos
  let c : ℂ := r
  have hBV : B ⊆ c • V := hsub c (by simp [c, abs_of_pos hr])
  let := p.toSeminormedAddCommGroup
  let : UniformSpace E := p.toSeminormedAddCommGroup.toUniformSpace
  have hsmul : LipschitzWith ‖c‖₊ (c • · : E → E) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [dist_eq_norm_sub, dist_eq_norm_sub, ← smul_sub]
      exact (map_smul_eq_mul p c (x - y)).le
  have htotalB : TotallyBounded B :=
    (htotal.image hsmul.uniformContinuous).subset hBV
  obtain ⟨A, hA, hcover⟩ := Metric.totallyBounded_iff.mp htotalB 1 zero_lt_one
  refine ⟨A, hA, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcover hx)
  refine mem_iUnion₂.mpr ⟨a, ha, ?_⟩
  change x - a ∈ p.ball 0 1
  rwa [p.sub_mem_ball, add_zero, p.ball_eq_metric]

/-- A Schwartz Fréchet space has the Heine–Borel property used in the Montel regularity
criterion. -/
theorem montelSpace_of_schwartz_frechet
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (hS : IsSchwartzTVS E) : MontelSpace ℂ E := by
  obtain ⟨hadd, _, _, hcomplete⟩ := hE
  let : IsTopologicalAddGroup E := hadd
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  exact ⟨fun B hclosed hB ↦ hclosed.closure_eq ▸ isCompact_closure_of_schwartz hS hB⟩

section MontelLimits

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]
  {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E}

/-- Paper: Equation (C.1.5.2), p. 667. The image of the difference map is the
kernel of the canonical map from the direct sum to the limit. -/
theorem IsInjectiveLCLimit.range_directSumDifference (h : IsInjectiveLCLimit j i) :
    range (directSumDifference j) =
      (DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)).ker := by
  let D := ⨁ k, X k
  let q : D →ₗ[ℂ] E := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  let σ := directSumDifference j
  have hq (k : ℕ) (x : X k) : q (DirectSum.lof ℂ ℕ X k x) = i k x :=
    DirectSum.toModule_lof _ _ _
  refine subset_antisymm ?_ ?_
  · have hcomp : q.comp σ = 0 := by
      apply DirectSum.linearMap_ext
      intro k
      ext x : 1
      change q (σ (DirectSum.lof ℂ ℕ X k x)) = 0
      rw [show σ (DirectSum.lof ℂ ℕ X k x) =
          DirectSum.lof ℂ ℕ X k x - DirectSum.lof ℂ ℕ X (k+1) (j k x) by
        change directSumDifference j (DirectSum.lof ℂ ℕ X k x) = _
        rw [directSumDifference, LinearMap.sub_apply, LinearMap.id_apply,
          DirectSum.toModule_lof]
        rfl]
      rw [map_sub, hq, hq]
      exact sub_eq_zero.mpr (DFunLike.congr_fun (h.compatible k) x).symm
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hcomp x
  · classical
    intro y hy
    let s : ∀ k, X k := Nat.rec (y 0) (fun k z ↦ j k z + y (k+1))
    have hs (k : ℕ) : i k (s k) = ∑ l ∈ Finset.range (k+1), i l (y l) := by
      induction k with
      | zero => simp [s]
      | succ k ih =>
        change i (k+1) (j k (s k) + y (k+1)) = _
        have hcomp : i (k+1) (j k (s k)) = i k (s k) :=
          DFunLike.congr_fun (h.compatible k) (s k)
        rw [map_add, hcomp, ih]
        exact (Finset.sum_range_succ (fun l ↦ i l (y l)) (k+1)).symm
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range y.support
    have hsum (k : ℕ) (hk : n ≤ k) : (∑ l ∈ Finset.range (k+1), i l (y l)) = q y := by
      have hqsum : q y = ∑ l ∈ y.support, i l (y l) := calc
        q y = q (∑ l ∈ y.support, DirectSum.lof ℂ ℕ X l (y l)) :=
          congrArg q (DirectSum.sum_support_of y).symm
        _ = _ := by simp only [map_sum, hq]
      rw [hqsum]
      refine (Finset.sum_subset (hn.trans (Finset.range_mono (Nat.le_succ_of_le hk))) ?_).symm
      intro l _ hl
      rw [DFinsupp.notMem_support_iff.mp hl, map_zero]
    have htail (k : ℕ) (hk : n ≤ k) : s k = 0 := h.injective k <| by
      rw [hs, hsum k hk, map_zero]
      exact hy
    let x : D := DFinsupp.mk (Finset.range n) (fun k ↦ s k)
    have hx (k : ℕ) : x k = s k := by
      change (DFinsupp.mk (Finset.range n) (fun k ↦ s k)) k = _
      rw [DFinsupp.mk_apply]
      split
      · rfl
      · exact (htail k (by simpa using ‹k ∉ Finset.range n›)).symm
    refine ⟨x, DFinsupp.ext fun k ↦ ?_⟩
    cases k with
    | zero => exact (directSumDifference_apply j x).1.trans (hx 0)
    | succ k =>
      rw [(directSumDifference_apply j x).2 k, hx, hx]
      exact add_sub_cancel_left (j k (s k)) (y (k+1))

/-- Paper: Equation (C.1.5.2), p. 667. The canonical map from the locally convex
direct sum to the limit is a quotient map, including for a non-Hausdorff limit. -/
theorem IsInjectiveLCLimit.isQuotientMap_directSum (h : IsInjectiveLCLimit j i)
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)] :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    IsQuotientMap (DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)) := by
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  let q : D →ₗ[ℂ] E := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  have hq (k : ℕ) (x : X k) : q (lof k x) = i k x := DirectSum.toModule_lof _ _ _
  have hsurj : Function.Surjective q := by
    intro x
    obtain ⟨k, y, rfl⟩ := h.exhaustive x
    exact ⟨lof k y, hq k y⟩
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} → Seminorm ℂ D) :=
    ⟨rfl⟩
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  have hE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  have hqc : Continuous q := by
    apply hE.continuous_of_continuous_comp
    intro p
    refine hD.continuous_seminorm (i := ⟨p.val.comp q, fun k ↦ ?_⟩)
    simpa only [Function.comp_def, Seminorm.comp_apply, hq] using p.property k
  let e := q.quotKerEquivOfSurjective hsurj
  have he : Continuous e := q.ker.isQuotientMap_mkQL.continuous_iff.mpr hqc
  have he' : Continuous e.symm := by
    apply h.continuous_of_stages e.symm.toLinearMap
    intro k
    have heq (x : X k) : e.symm (i k x) = q.ker.mkQ (lof k x) := by
      rw [← hq]
      exact q.quotKerEquivOfSurjective_symm_apply hsurj _
    change Continuous (fun x ↦ e.symm (i k x))
    simp_rw [heq]
    exact q.ker.mkQL.continuous.comp
      (hD.continuous_of_continuous_comp (lof k) fun p ↦ p.property k)
  let homeo : (D ⧸ q.ker) ≃ₜ E := ⟨e.toEquiv, he, he'⟩
  change IsQuotientMap q
  exact homeo.isQuotientMap.comp q.ker.isQuotientMap_mkQL

/-- The difference map has closed range exactly when the limit is Hausdorff. -/
theorem IsInjectiveLCLimit.closedRange_directSumDifference_iff (h : IsInjectiveLCLimit j i)
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)] :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    IsClosed (range (directSumDifference j)) ↔ T2Space E := by
  have hE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hE.isTopologicalAddGroup
  let : TopologicalSpace (⨁ k, X k) := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  change IsClosed (range (directSumDifference j)) ↔ T2Space E
  rw [h.range_directSumDifference, IsTopologicalAddGroup.t2Space_iff_zero_closed]
  exact ((isQuotientMap_iff_isClosed.mp h.isQuotientMap_directSum).2 {0}).symm

/-- Bounded lifting from stages forces Hausdorffness. The closure of zero is bounded,
but its preimage in an injective stage cannot contain a nonzero line and be bounded. -/
private theorem IsInjectiveLCLimit.t2Space_of_bounded_stage (h : IsInjectiveLCLimit j i)
    [∀ k, PolynormableSpace ℂ (X k)] [∀ k, T2Space (X k)]
    (hlift : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ i k '' A = B) : T2Space E := by
  have hE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hE.isTopologicalAddGroup
  let : ContinuousSMul ℂ E := hE.continuousSMul
  let N := (⊥ : Submodule ℂ E).topologicalClosure
  have hN : (N : Set E) = closure ({0} : Set E) := by simp [N]
  have hb : IsVonNBounded ℂ (N : Set E) := hE.isVonNBounded_iff_seminorm_bounded.mpr (by
    intro p
    refine ⟨1, zero_lt_one, fun x hx ↦ ?_⟩
    have hzero : p.val x = 0 := by
      rw [hN] at hx
      have hmem := image_closure_subset_closure_image (hE.continuous_seminorm (i := p))
        (mem_image_of_mem p.val hx)
      simpa using hmem
    simp [hzero])
  obtain ⟨k, A, hA, heq⟩ := hlift N hb
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← closure_subset_iff_isClosed, ← hN]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := heq.symm ▸ hx
  suffices hy0 : y = 0 by simp [hy0]
  by_contra hy0
  let P := PolynormableSpace.withSeminorms ℂ (X k)
  obtain ⟨p, hp⟩ := P.separating_of_T1 y hy0
  have hpos : 0 < p.val y := lt_of_le_of_ne (apply_nonneg p.val y) hp.symm
  obtain ⟨R, hRpos, hR⟩ := P.isVonNBounded_iff_seminorm_bounded.mp hA p
  let c : ℂ := (R / p.val y : ℝ)
  have hyN : i k y ∈ N := by
    change i k y ∈ (N : Set E)
    rw [← heq]
    exact mem_image_of_mem (i k) hy
  have hcN : i k (c • y) ∈ N := by
    rw [map_smul]
    exact N.smul_mem c hyN
  have hc : i k (c • y) ∈ i k '' A := by
    rw [heq]
    exact hcN
  obtain ⟨z, hz, hzy⟩ := hc
  have hlt := hR z hz
  rw [h.injective k hzy, map_smul_eq_mul, show ‖c‖ = R / p.val y by
    exact Complex.norm_of_nonneg (div_nonneg hRpos.le hpos.le),
    div_mul_cancel₀ _ hpos.ne'] at hlt
  exact (lt_irrefl R) hlt

/-- If each null sequence has bounded representatives in one stage, then every bounded
set has a bounded lift to one stage. Test each stage with countably many scaled points. -/
private theorem bounded_stage_of_nullSequence (h : IsInjectiveLCLimit j i)
    [ContinuousSMul ℂ E] [∀ k, PolynormableSpace ℂ (X k)]
    (hseq : ∀ u : ℕ → E, Tendsto u atTop (𝓝 0) →
      ∃ k, ∃ v : ℕ → X k, IsVonNBounded ℂ (range v) ∧ ∀ n, i k (v n) = u n)
    (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ i k '' A = B := by
  classical
  by_contra hno
  have hwitness (k : ℕ) :
      ∃ p : {p : Seminorm ℂ (X k) // Continuous p}, ∀ R : ℝ,
        ∃ x ∈ B, x ∉ i k '' p.val.ball 0 R := by
    by_cases hk : B ⊆ range (i k)
    · have hu : ¬ IsVonNBounded ℂ (i k ⁻¹' B) := fun hbounded ↦
        hno ⟨k, _, hbounded, image_preimage_eq_of_subset hk⟩
      rw [(PolynormableSpace.withSeminorms ℂ (X k)).isVonNBounded_iff_seminorm_bounded]
        at hu
      push Not at hu
      obtain ⟨p, hp⟩ := hu
      refine ⟨p, fun R ↦ ?_⟩
      obtain ⟨z, hz, hlarge⟩ := hp (max R 1) (zero_lt_one.trans_le (le_max_right _ _))
      refine ⟨i k z, hz, ?_⟩
      rintro ⟨w, hw, he⟩
      rw [h.injective k he, Seminorm.mem_ball_zero] at hw
      exact (le_max_left _ _).not_gt (hlarge.trans_lt hw)
    · obtain ⟨x, hxB, hx⟩ := Set.not_subset.mp hk
      exact ⟨⟨0, continuous_zero⟩, fun _ ↦
        ⟨x, hxB, fun hmem ↦ hx (image_subset_range _ _ hmem)⟩⟩
  choose p hchoose using hwitness
  let ε (n : ℕ) : ℂ := ((n : ℂ) + 1)⁻¹
  have hε (n : ℕ) : ε n ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  choose x hxB hx using fun n : ℕ ↦
    hchoose (Nat.unpair n).1 ((Nat.unpair n).2 / ‖ε n‖)
  let u (n : ℕ) := ε n • x n
  obtain ⟨k, v, hv, he⟩ := hseq u (hB.smul_tendsto_zero (.of_forall hxB) hlim)
  let P := PolynormableSpace.withSeminorms ℂ (X k)
  obtain ⟨R, _, hR⟩ := P.isVonNBounded_iff_seminorm_bounded.mp hv (p k)
  obtain ⟨m, hm⟩ := exists_nat_gt R
  let n := Nat.pair k m
  let S (km : ℕ × ℕ) := i km.1 '' (p km.1).val.ball 0 ((km.2 : ℝ) / ‖ε n‖)
  have hind : S (Nat.unpair n) = S (k, m) := congrArg S (Nat.unpair_pair k m)
  have hx' : x n ∉ S (k, m) := hind ▸ (show x n ∉ S (Nat.unpair n) from hx n)
  apply hx'
  refine ⟨(ε n)⁻¹ • v n, ?_, ?_⟩
  · rw [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ← div_eq_inv_mul]
    exact div_lt_div_of_pos_right ((hR _ (mem_range_self n)).trans hm)
      (norm_pos_iff.mpr (hε n))
  · rw [map_smul, he n, inv_smul_smul₀ (hε n)]

/-- Paper: Equation (C.1.5.4), p. 667. The inverse difference map bounds a seminorm
at stage `m` in terms of a finite representative through stage `m` and its image
in stage `k > m`. -/
private theorem IsInjectiveLCLimit.directSum_seminorm_control
    [∀ k, IsTopologicalAddGroup (X k)] [∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)]
    (h : IsInjectiveLCLimit j i) (hacyclic : IsAcyclicSystem j)
    (p : ∀ k, Seminorm ℂ (X k)) (hp : ∀ k, Continuous (p k)) :
    let c := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
    ∃ q : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (q k)) ∧
      ∀ (m k : ℕ), m < k → ∀ (z : ⨁ l, X l) (y : X m) (w : X k),
        (∀ l, m < l → z l = 0) → c z = i m y → c z = i k w →
        p m y ≤ directSumSeminorm q z + q k w := by
  dsimp only
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let c := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  let σ := directSumDifference j
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  have hD : WithSeminorms
      (Subtype.val : {s : Seminorm ℂ D // ∀ k, Continuous (s ∘ lof k)} → Seminorm ℂ D) :=
    ⟨rfl⟩
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  have hσ : IsClosedEmbedding σ := hacyclic
  have hpD : Continuous (directSumSeminorm p) := by
    refine hD.continuous_seminorm ⟨_, fun k ↦ ?_⟩
    have he : (directSumSeminorm p : D → ℝ) ∘ lof k = p k :=
      funext (directSumSeminorm_lof p k)
    change Continuous ((directSumSeminorm p : D → ℝ) ∘ lof k)
    rw [he]
    exact hp k
  obtain ⟨Q, hQ, hbound⟩ := Seminorm.exists_le_comp_of_isInducing hpD hσ.isInducing
  let q (k : ℕ) := Q.comp (lof k)
  have hQsum (z : D) : Q z ≤ directSumSeminorm q z := by
    rw [directSumSeminorm_apply q z z.support Subset.rfl]
    have hs := Finset.le_sum_of_subadditive Q (map_zero Q).le
      (map_add_le_add Q) z.support (fun k ↦ lof k (z k))
    rwa [show (∑ k ∈ z.support, lof k (z k)) = z from DirectSum.sum_support_of z] at hs
  have hpartial (u : D) (m : ℕ) :
      i m (u m) = ∑ l ∈ Finset.range (m+1), i l (σ u l) := by
    induction m with
    | zero => simp [(directSumDifference_apply j u).1, σ]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih, (directSumDifference_apply j u).2 m, map_sub,
        show i (m+1) (j m (u m)) = i m (u m) from DFunLike.congr_fun (h.compatible m) (u m)]
      abel
  refine ⟨q, fun k ↦ hQ.comp (hD.continuous_of_continuous_comp _ fun s ↦ s.property k), ?_⟩
  intro m k hmk z y w hz hy hw
  have hc (l : ℕ) (x : X l) : c (lof l x) = i l x := DirectSum.toModule_lof _ _ _
  have hker : z - lof k w ∈ c.ker := by
    rw [LinearMap.mem_ker, map_sub, hc, hw, sub_self]
  have hmem : z - lof k w ∈ range σ := by
    change _ ∈ range (directSumDifference j)
    rw [h.range_directSumDifference]
    exact hker
  obtain ⟨u, hu⟩ := hmem
  have hsum : c z = ∑ l ∈ Finset.range (m+1), i l (z l) := by
    have hsupport : z.support ⊆ Finset.range (m+1) := by
      intro l hl
      exact Finset.mem_range.mpr (by
        by_contra! hml
        exact (DFinsupp.mem_support_iff.mp hl) (hz l (by omega)))
    have hs : z.sum (fun l ↦ lof l) = z := DirectSum.sum_support_of z
    rw [DFinsupp.sum_of_support_subset hsupport (fun l _ ↦ map_zero (lof l))] at hs
    calc
      c z = c (∑ l ∈ Finset.range (m+1), lof l (z l)) := congrArg c hs.symm
      _ = _ := by rw [map_sum]; exact Finset.sum_congr rfl fun l _ ↦ hc l (z l)
  have huy : u m = y := h.injective m (calc
    i m (u m) = ∑ l ∈ Finset.range (m+1), i l (σ u l) := hpartial u m
    _ = ∑ l ∈ Finset.range (m+1), i l (z l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hkl : l ≠ k := by have := Finset.mem_range.mp hl; omega
      rw [show σ u = z - lof k w from hu, DirectSum.sub_apply]
      simp [lof, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hkl]
    _ = c z := hsum.symm
    _ = i m y := hy)
  have hcoord : p m (u m) ≤ directSumSeminorm p u := by
    simpa only [Finset.sum_singleton] using sum_le_directSumSeminorm p u {m}
  calc
    p m y = p m (u m) := congrArg (p m) huy.symm
    _ ≤ directSumSeminorm p u := hcoord
    _ ≤ Q (σ u) := hbound u
    _ ≤ Q z + Q (lof k w) := by rw [show σ u = _ from hu]; exact map_sub_le_add Q _ _
    _ ≤ directSumSeminorm q z + q k w := add_le_add (hQsum z) le_rfl

/-- Paper: Definition C.1.5.8, p. 667. For an acyclic system, one can choose
coordinate seminorms whose unit balls on every finite block admit uniform
comparison estimates from some stage onward. Deviation: this is the finite-block
estimate used to deduce Retakh stabilization from the inverse in (C.1.5.4). -/
private theorem IsInjectiveLCLimit.exists_stabilizing_seminorms
    [∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)]
    (h : IsInjectiveLCLimit j i) (hX : ∀ k, IsFrechetTVS (X k))
    (hacyclic : IsAcyclicSystem j) :
    let c := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ n, ∃ m, n ≤ m ∧ ∀ k, m < k → ∀ p : Seminorm ℂ (X m), Continuous p →
        ∃ q : Seminorm ℂ (X k), Continuous q ∧
          ∀ (z : ⨁ l, X l) (y : X m) (w : X k),
            (∀ l, n < l → z l = 0) → directSumSeminorm r z < 1 →
            c z = i m y → c z = i k w → p y ≤ 1 + q w := by
  classical
  dsimp only
  choose hgroup hpoly hmetric _ using hX
  let : ∀ k, IsTopologicalAddGroup (X k) := hgroup
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetric
  let D := ⨁ k, X k
  let c := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  choose B hB using fun k ↦ (𝓝 (0 : X k)).exists_antitone_basis
  choose b hb hbB using fun k t ↦
    (PolynormableSpace.hasBasis_zero_ball ℂ (X k)).mem_iff.mp ((hB k).mem t)
  -- Enumerate the finite lists of choices of coordinate seminorms.
  let I := Σ n : ℕ, Fin (n+1) → ℕ
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  let code (a : I) := Nat.pair a.1 (e a)
  have hcode : Function.Injective code := by
    intro a a' ha
    apply he
    simpa [code] using congrArg (fun m ↦ (Nat.unpair m).2) ha
  let r₀ (a : I) (l : ℕ) : Seminorm ℂ (X l) :=
    if hl : l < a.1+1 then b l (a.2 ⟨l, hl⟩) else 0
  let Controls (a : I) (m : ℕ) (p : Seminorm ℂ (X m)) :=
    ∀ k : ℕ, m < k → ∃ q : Seminorm ℂ (X k), Continuous q ∧
      ∀ (z : D) (y : X m) (w : X k),
        (∀ l, a.1 < l → z l = 0) → directSumSeminorm (r₀ a) z < 1 →
        c z = i m y → c z = i k w → p y ≤ 1 + q w
  let Good (a : I) (m : ℕ) :=
    ∀ p : Seminorm ℂ (X m), Continuous p → Controls a m p
  -- If a candidate fails at its assigned stage, test the estimate with a witness
  -- to that failure. The inverse difference map must control all tests at once.
  have htest (m : ℕ) : ∃ p : Seminorm ℂ (X m), Continuous p ∧
      ∀ a, code a = m → ¬ Good a m → ¬ Controls a m p := by
    by_cases hm : ∃ a, code a = m ∧ ¬ Good a m
    · obtain ⟨a, ha, hbad⟩ := hm
      obtain ⟨p, hp, hbad⟩ : ∃ p : Seminorm ℂ (X m), ∃ _ : Continuous p, ¬ Controls a m p := by
        simpa only [Good, not_forall] using hbad
      exact ⟨p, hp, fun a' ha' _ ↦ hcode (ha.trans ha'.symm) ▸ hbad⟩
    · exact ⟨0, continuous_zero, fun a ha hbad ↦ (hm ⟨a, ha, hbad⟩).elim⟩
  choose p hp hpTest using htest
  obtain ⟨q, hq, hcontrol⟩ := h.directSum_seminorm_control hacyclic p hp
  have ht (l : ℕ) : ∃ t, q l ≤ b l t := by
    obtain ⟨t, ht⟩ := (hB l).mem_iff.mp (Seminorm.ball_mem_nhds (hq l) zero_lt_one)
    refine ⟨t, fun x ↦ le_of_not_gt fun hx ↦ ?_⟩
    have hpos : 0 < q l x := (apply_nonneg (b l t) x).trans_lt hx
    have hx' := ht (hbB l t (a := ((q l x)⁻¹ : ℝ) • x) (by
      rw [Seminorm.mem_ball_zero, ← Complex.coe_smul, map_smul_eq_mul,
        Complex.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
      simpa [div_eq_inv_mul] using (div_lt_one hpos).mpr hx))
    rw [Seminorm.mem_ball_zero, ← Complex.coe_smul, map_smul_eq_mul,
      Complex.norm_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne'] at hx'
    exact (lt_irrefl _ hx')
  choose t ht using ht
  let r (l : ℕ) := b l (t l)
  refine ⟨r, fun l ↦ hb l _, fun n ↦ ?_⟩
  let a : I := ⟨n, fun l ↦ t l⟩
  let m := code a
  have hnm : n ≤ m := Nat.left_le_pair _ _
  have hsame (z : D) (hz : ∀ l, n < l → z l = 0) :
      directSumSeminorm (r₀ a) z = directSumSeminorm r z := by
    rw [directSumSeminorm_apply _ _ z.support Subset.rfl,
      directSumSeminorm_apply _ _ z.support Subset.rfl]
    apply Finset.sum_congr rfl
    intro l hl
    have hln : l < n+1 := by
      by_contra! hh
      exact (DFinsupp.mem_support_iff.mp hl) (hz l (by omega))
    simp [r₀, a, r, Nat.le_of_lt_succ hln]
  have ha : Good a m := by
    by_contra hbad
    apply hpTest m a rfl hbad
    intro k hmk
    refine ⟨q k, hq k, fun z y w hz hzr hy hw ↦ ?_⟩
    have hzq : directSumSeminorm q z ≤ directSumSeminorm r z := by
      rw [directSumSeminorm_apply _ _ z.support Subset.rfl,
        directSumSeminorm_apply _ _ z.support Subset.rfl]
      exact Finset.sum_le_sum fun l _ ↦ ht l (z l)
    rw [hsame z hz] at hzr
    exact (hcontrol m k hmk z y w (fun l hl ↦ hz l (hnm.trans_lt hl)) hy hw).trans
      (add_le_add (hzq.trans hzr.le) le_rfl)
  refine ⟨m, hnm, fun k hmk p hp ↦ ?_⟩
  obtain ⟨q', hq', hqle⟩ := ha p hp k hmk
  exact ⟨q', hq', fun z y w hz hzr ↦ hqle z y w hz ((hsame z hz).trans_lt hzr)⟩

/-- Retakh's neighborhood stabilization for an acyclic Fréchet system. The disks exhaust
the limit and contain a zero neighborhood from each corresponding stage. A disk closes
in a later stage, and each of its closed subsets there pulls back to a closed set in
every stage. One obtains the nested disks by applying the continuity of the inverse
difference map to seminorms witnessing failure of stabilization on finite boxes. -/
private theorem IsInjectiveLCLimit.exists_stagewise_stable_disks
    (h : IsInjectiveLCLimit j i) (hX : ∀ k, IsFrechetTVS (X k))
    (hacyclic : IsAcyclicSystem j) :
    ∃ S : ℕ → Set E, Monotone S ∧ (∀ x : E, ∃ n, x ∈ S n) ∧
      (∀ n, S n + S n ⊆ S (n+1)) ∧ (∀ n, i n ⁻¹' S n ∈ 𝓝 (0 : X n)) ∧
      ∀ n, ∃ m, n ≤ m ∧ S n ⊆ range (i m) ∧ IsClosed (i m ⁻¹' S n) ∧
        ∀ A : Set E, A ⊆ S n → IsClosed (i m ⁻¹' A) → ∀ k, IsClosed (i k ⁻¹' A) := by
  classical
  let _ : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0) := fun _ _ ↦ Classical.propDecidable _
  have hX' := hX
  choose hgroup hpoly hmetr hcomplete using hX'
  let : ∀ k, IsTopologicalAddGroup (X k) := hgroup
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetr
  let : ∀ k, UniformSpace (X k) := fun _ ↦ IsTopologicalAddGroup.rightUniformSpace _
  let : ∀ k, IsUniformAddGroup (X k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ k, CompleteSpace (X k) := hcomplete
  have htransition (a b : ℕ) (hab : a ≤ b) :
      ∃ f : X a →L[ℂ] X b, (i b).comp f = i a := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨ContinuousLinearMap.id ℂ _, rfl⟩
    | succ b _ ih =>
      obtain ⟨f, hf⟩ := ih
      exact ⟨(j b).comp f, by rw [← ContinuousLinearMap.comp_assoc, h.compatible, hf]⟩
  choose f hf using htransition
  have hfi (a b : ℕ) (hab : a ≤ b) (y : X a) : i b (f a b hab y) = i a y :=
    DFunLike.congr_fun (hf a b hab) y
  obtain ⟨r, hr, hcontrol⟩ := h.exists_stabilizing_seminorms hX hacyclic
  choose m hnm hm using hcontrol
  let D := ⨁ l, X l
  let lof := DirectSum.lof ℂ ℕ X
  let c := DirectSum.toModule ℂ ℕ E (fun l ↦ (i l).toLinearMap)
  let ρ := directSumSeminorm r
  let R (n : ℕ) := (2 : ℝ)^n
  have hR (n : ℕ) : 0 < R n := pow_pos (by norm_num) _
  let T (n : ℕ) := c '' {z : D | (∀ l, n < l → z l = 0) ∧ ρ z < R n}
  let C (n : ℕ) := closure (i (m n) ⁻¹' T n)
  let S (n : ℕ) := i (m n) '' C n
  have hc (k : ℕ) (y : X k) : c (lof k y) = i k y := DirectSum.toModule_lof _ _ _
  have hT_range (n : ℕ) : T n ⊆ range (i (m n)) := by
    rintro _ ⟨z, ⟨hz, _⟩, rfl⟩
    change c z ∈ (i (m n)).toLinearMap.range
    rw [← show (∑ l ∈ z.support, lof l (z l)) = z from DirectSum.sum_support_of z, map_sum]
    apply Submodule.sum_mem
    intro l hl
    have hln : l ≤ n := le_of_not_gt fun hnl ↦ (DFinsupp.mem_support_iff.mp hl) (hz l hnl)
    rw [hc]
    exact ⟨f l (m n) (hln.trans (hnm n)) (z l), hfi _ _ _ _⟩
  have hTS (n : ℕ) : T n ⊆ S n := by
    intro x hx
    obtain ⟨y, hy⟩ := hT_range n hx
    refine ⟨y, subset_closure ?_, hy⟩
    change i (m n) y ∈ T n
    rwa [hy]
  have hC (n : ℕ) : i (m n) ⁻¹' S n = C n :=
    preimage_image_eq _ (h.injective (m n))
  have hball (n a : ℕ) (han : a ≤ n) (y : X a) (hy : r a y < R n) : i a y ∈ T n := by
    refine ⟨lof a y, ⟨fun l hl ↦ ?_, ?_⟩, hc _ _⟩
    · change DirectSum.lof ℂ ℕ X a y l = 0
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
      omega
    · simpa only [ρ, lof, directSumSeminorm_lof] using hy
  have hzero (n : ℕ) : (0 : E) ∈ T n := by
    simpa only [map_zero] using hball n n le_rfl 0 (by simpa only [map_zero] using hR n)
  have hTadd (n : ℕ) : T n + T n ⊆ T (n+1) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨x + y, ⟨fun l hl ↦ ?_, ?_⟩, map_add c _ _⟩
    · rw [DFinsupp.add_apply, hx.1 l (by omega), hy.1 l (by omega), add_zero]
    · calc
        ρ (x + y) ≤ ρ x + ρ y := map_add_le_add ρ _ _
        _ < R n + R n := add_lt_add hx.2 hy.2
        _ = R (n+1) := by simp only [R, pow_succ]; ring
  -- On the closure of a finite ball the later transition induces the same uniformity.
  have hstable (n : ℕ) (A : Set E) (hA : A ⊆ S n) (hclosed : IsClosed (i (m n) ⁻¹' A))
      (k : ℕ) : IsClosed (i k ⁻¹' A) := by
    by_cases hkm : k ≤ m n
    · have he : i k ⁻¹' A = f k (m n) hkm ⁻¹' (i (m n) ⁻¹' A) := by
        ext y
        simp only [mem_preimage, hfi]
      rw [he]
      exact hclosed.preimage (f k (m n) hkm).continuous
    have hmk : m n < k := Nat.lt_of_not_ge hkm
    let F := f (m n) k hmk.le
    let g (y : C n) : X k := F y.val
    have hg : IsUniformInducing g := by
      let hmBasis := (PolynormableSpace.hasBasis_zero_ball ℂ (X (m n))).uniformity_of_nhds_zero_swapped
      let hkBasis := (PolynormableSpace.hasBasis_zero_ball ℂ (X k)).uniformity_of_nhds_zero_swapped
      have hsub : IsUniformInducing (Subtype.val : C n → X (m n)) :=
        isUniformEmbedding_subtype_val.isUniformInducing
      rw [isUniformInducing_iff']
      refine ⟨F.uniformContinuous.comp hsub.uniformContinuous, ?_⟩
      apply ((hkBasis.comap (Prod.map g g)).le_basis_iff (hsub.basis_uniformity hmBasis)).mpr
      intro p hp
      let L := R (n+1)
      have hL : 0 < L := hR _
      let s : ℂ := ((L⁻¹ : ℝ) : ℂ)
      have hs : ‖s‖ = L⁻¹ := Complex.norm_of_nonneg (inv_nonneg.mpr hL.le)
      let P := (2*L).toNNReal • p
      have hP : Continuous P := hp.const_smul _
      obtain ⟨q, hq, hle⟩ := hm n k hmk P hP
      let Q := L⁻¹.toNNReal • q
      have hQ : Continuous Q := hq.const_smul _
      refine ⟨Q, hQ, ?_⟩
      have hbound (y z : X (m n)) (hy : i (m n) y ∈ T n) (hz : i (m n) z ∈ T n) :
          2 * p (y-z) ≤ 1 + Q (F y - F z) := by
        obtain ⟨v, hv, hvy⟩ := hy
        obtain ⟨w, hw, hwz⟩ := hz
        have hdiff : ρ (v-w) < L := by
          have hle := map_sub_le_add ρ v w
          have hL' : L = R n + R n := by simp only [L, R, pow_succ]; ring
          rw [hL']
          exact hle.trans_lt (add_lt_add hv.2 hw.2)
        have hsm : ρ (s • (v-w)) < 1 := by
          rw [map_smul_eq_mul, hs, ← div_eq_inv_mul]
          exact (div_lt_one hL).mpr hdiff
        have heq : c (s • (v-w)) = i (m n) (s • (y-z)) := by
          rw [map_smul, map_smul, map_sub, map_sub, hvy, hwz]
        have heq' : c (s • (v-w)) = i k (s • (F y - F z)) := by
          rw [heq, map_smul, map_smul, map_sub, map_sub]
          change _ = s • (i k (f (m n) k hmk.le y) - i k (f (m n) k hmk.le z))
          rw [hfi, hfi]
        have htest := hle (s • (v-w)) (s • (y-z)) (s • (F y - F z))
          (fun l hl ↦ by rw [DFinsupp.smul_apply, DFinsupp.sub_apply, hv.1 l hl, hw.1 l hl,
            sub_self, smul_zero]) hsm heq heq'
        change ((2*L).toNNReal : ℝ) * p (s • (y-z)) ≤ 1 + q (s • (F y - F z)) at htest
        rw [Real.coe_toNNReal (2*L) (by positivity), map_smul_eq_mul, map_smul_eq_mul, hs,
          ← mul_assoc, mul_assoc 2 L L⁻¹, mul_inv_cancel₀ hL.ne', mul_one] at htest
        change 2 * p (y-z) ≤ 1 + ((L⁻¹ : ℝ).toNNReal : ℝ) * q (F y - F z)
        rwa [Real.coe_toNNReal _ (inv_nonneg.mpr hL.le)]
      have hbound_closed : IsClosed {yz : X (m n) × X (m n) |
          2 * p (yz.1-yz.2) ≤ 1 + Q (F yz.1 - F yz.2)} :=
        isClosed_le ((hp.comp (continuous_fst.sub continuous_snd)).const_mul 2)
          (continuous_const.add (hQ.comp ((F.continuous.comp continuous_fst).sub
            (F.continuous.comp continuous_snd))))
      rintro ⟨y, z⟩ hyz
      change g y - g z ∈ Q.ball 0 1 at hyz
      change y.val - z.val ∈ p.ball 0 1
      rw [Seminorm.mem_ball_zero] at hyz ⊢
      have hmemb : (y.val, z.val) ∈ closure ((i (m n) ⁻¹' T n) ×ˢ (i (m n) ⁻¹' T n)) := by
        rw [closure_prod_eq]
        exact ⟨y.property, z.property⟩
      have hcomp : 2 * p (y.val-z.val) ≤ 1 + Q (g y - g z) := by
        refine hbound_closed.closure_subset_iff.mpr ?_ hmemb
        intro uv huv
        exact hbound uv.1 uv.2 huv.1 huv.2
      linarith
    let A' : Set (C n) := (Subtype.val : C n → X (m n)) ⁻¹' (i (m n) ⁻¹' A)
    let : CompleteSpace (C n) := isClosed_closure.isComplete.completeSpace_coe
    have hAc : IsClosed A' := hclosed.preimage continuous_subtype_val
    have hAc' : IsClosed (g '' A') := ((isComplete_image_iff hg).mpr hAc.isComplete).isClosed
    have hgi (y : C n) : i k (g y) = i (m n) y.val := hfi _ _ _ _
    have hAeq : i k ⁻¹' A = g '' A' := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hyC, hy⟩ := hA hx
        refine ⟨⟨y, hyC⟩, ?_, h.injective k ((hgi ⟨y, hyC⟩).trans hy)⟩
        change i (m n) y ∈ A
        rwa [hy]
      · rintro ⟨y, hy, rfl⟩
        change i k (g y) ∈ A
        rw [hgi]
        exact hy
    rwa [hAeq]
  have hSclosed (n k : ℕ) : IsClosed (i k ⁻¹' S n) :=
    hstable n (S n) Subset.rfl (by rw [hC]; exact isClosed_closure) k
  have hSadd (n : ℕ) : S n + S n ⊆ S (n+1) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    let k := m n
    change i k a + i k b ∈ S (n+1)
    rw [← map_add]
    have hmaps : MapsTo (fun z : X k × X k ↦ z.1 + z.2)
        ((i k ⁻¹' T n) ×ˢ (i k ⁻¹' T n)) (i k ⁻¹' S (n+1)) := by
      intro z hz
      change i k (z.1 + z.2) ∈ S (n+1)
      rw [map_add]
      exact hTS _ (hTadd n (add_mem_add hz.1 hz.2))
    have hab : (a, b) ∈ closure ((i k ⁻¹' T n) ×ˢ (i k ⁻¹' T n)) := by
      rw [closure_prod_eq]
      exact ⟨ha, hb⟩
    have hab' : a + b ∈ closure (i k ⁻¹' S (n+1)) := hmaps.closure continuous_add hab
    rwa [(hSclosed (n+1) k).closure_eq] at hab'
  refine ⟨S, monotone_nat_of_le_succ ?_, ?_, hSadd, ?_, fun n ↦ ?_⟩
  · intro n x hx
    simpa only [add_zero] using hSadd n (add_mem_add hx (hTS n (hzero n)))
  · intro x
    obtain ⟨a, y, rfl⟩ := h.exhaustive x
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r a y) (by norm_num : (1 : ℝ) < 2)
    refine ⟨max a n, hTS _ (hball _ a (le_max_left _ _) y ?_)⟩
    exact hn.trans_le (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))
  · intro n
    refine mem_of_superset ((r n).ball_mem_nhds (hr n) (hR n)) fun y hy ↦ ?_
    exact hTS n (hball n n le_rfl y ((r n).mem_ball_zero.mp hy))
  · exact ⟨m n, hnm n, image_subset_range _ _, hSclosed n _, hstable n⟩

/-- If each coordinate belongs to a prescribed stage neighborhood, the image of
the resulting direct-sum box under the canonical quotient contains a zero neighborhood. -/
private theorem IsInjectiveLCLimit.directSum_box_image_mem_nhds (h : IsInjectiveLCLimit j i)
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (V : ∀ k, Set (X k)) (hV : ∀ k, V k ∈ 𝓝 (0 : X k)) :
    DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap) ''
      {z : ⨁ k, X k | ∀ k, z k ∈ V k} ∈ 𝓝 (0 : E) := by
  classical
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  let q : D →ₗ[ℂ] E := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} → Seminorm ℂ D) :=
    ⟨rfl⟩
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  have hq : IsQuotientMap q := h.isQuotientMap_directSum
  let e := q.quotKerEquivOfSurjective hq.surjective
  have heq : (e : (D ⧸ q.ker) → E) ∘ q.ker.mkQ = q := by
    funext z
    exact q.quotKerEquivOfSurjective_apply_mk hq.surjective z
  have hop : IsOpenMap q := by
    have he : Continuous e := q.ker.isQuotientMap_mkQ.continuous_iff.mpr (heq.symm ▸ hq.continuous)
    have he' : Continuous e.symm := hq.continuous_iff.mpr (by
      have heq' : (e.symm : E → (D ⧸ q.ker)) ∘ q = q.ker.mkQ :=
        funext (q.quotKerEquivOfSurjective_symm_apply hq.surjective)
      rw [heq']
      exact q.ker.continuous_mkQ)
    let homeo : (D ⧸ q.ker) ≃ₜ E := ⟨e.toEquiv, he, he'⟩
    rw [← heq]
    exact homeo.isOpenMap.comp q.ker.isOpenMap_mkQ
  choose p hp hsub using fun k ↦
    (PolynormableSpace.hasBasis_zero_ball ℂ (X k)).mem_iff.mp (hV k)
  let r := directSumSeminorm (fun k ↦ (p k : Seminorm ℂ (X k)))
  have hr : Continuous r := hD.continuous_seminorm (i := ⟨r, fun k ↦ by
    have he : (r : D → ℝ) ∘ lof k = p k := funext (directSumSeminorm_lof _ k)
    rw [he]
    exact hp k⟩)
  have hb : {z : D | ∀ k, z k ∈ V k} ∈ 𝓝 (0 : D) := by
    refine mem_of_superset (r.ball_mem_nhds hr zero_lt_one) fun z hz k ↦ hsub k ?_
    rw [Seminorm.mem_ball_zero] at hz ⊢
    have hcoord : p k (z k) ≤ r z := by
      simpa only [Finset.sum_singleton] using
        sum_le_directSumSeminorm (fun k ↦ (p k : Seminorm ℂ (X k))) z {k}
    exact hcoord.trans_lt hz
  simpa only [map_zero] using hop.image_mem_nhds hb

/-- The canonical direct-sum map is a finite sum of stage images. -/
private theorem exists_eq_sum_stage_coords (z : ⨁ k, X k) :
    ∃ b : ℕ, DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap) z =
      ∑ k ∈ Finset.range b, i k (z k) := by
  let _ : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨b, hb⟩ := Finset.exists_nat_subset_range z.support
  let lof := DirectSum.lof ℂ ℕ X
  let q := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  have he : z.sum (fun k ↦ lof k) = z := DirectSum.sum_support_of z
  have hzsum : (∑ k ∈ Finset.range b, lof k (z k)) = z := by
    rwa [DFinsupp.sum_of_support_subset hb (fun k _ ↦ map_zero (lof k))] at he
  refine ⟨b, ?_⟩
  calc
    q z = q (∑ k ∈ Finset.range b, lof k (z k)) := congrArg q hzsum.symm
    _ = _ := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ DirectSum.toModule_lof _ _ _

/-- A stagewise closed set inside one of a nested family of stable disks is closed in
the locally convex limit. Starting with the set, successively add images of small
stage neighborhoods and close each partial sum in a stage where the larger disk has
stabilized. Each closure remains stagewise closed, so the neighborhoods can be
chosen to keep any fixed exterior point outside every partial sum. -/
private theorem IsInjectiveLCLimit.isClosed_of_stagewise_closed_in_stable_disks
    (h : IsInjectiveLCLimit j i) (hX : ∀ k, IsFrechetTVS (X k))
    (S : ℕ → Set E) (hmono : Monotone S) (hcover : ∀ x : E, ∃ n, x ∈ S n)
    (hadd : ∀ n, S n + S n ⊆ S (n+1)) (hnhds : ∀ n, i n ⁻¹' S n ∈ 𝓝 (0 : X n))
    (hstable : ∀ n, ∃ m, n ≤ m ∧ S n ⊆ range (i m) ∧ IsClosed (i m ⁻¹' S n) ∧
      ∀ A : Set E, A ⊆ S n → IsClosed (i m ⁻¹' A) → ∀ k, IsClosed (i k ⁻¹' A))
    (A : Set E) (n : ℕ) (hA : A ⊆ S n) (hclosed : ∀ k, IsClosed (i k ⁻¹' A)) :
    IsClosed A := by
  classical
  have hX' := hX
  choose hgroup hpoly _ _ using hX'
  let : ∀ k, IsTopologicalAddGroup (X k) := hgroup
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  have hE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hE.isTopologicalAddGroup
  have htransition (a m : ℕ) (ham : a ≤ m) :
      ∃ f : X a →L[ℂ] X m, (i m).comp f = i a := by
    induction m, ham using Nat.le_induction with
    | base => exact ⟨ContinuousLinearMap.id ℂ _, rfl⟩
    | succ m _ ih =>
      obtain ⟨f, hf⟩ := ih
      exact ⟨(j m).comp f, by rw [← ContinuousLinearMap.comp_assoc, h.compatible, hf]⟩
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨a, ha⟩ := hcover x
  let b := max n a
  have hxS : x ∈ S b := hmono (le_max_right _ _) ha
  let P (k : ℕ) := {K : Set E // K ⊆ S (b+k) ∧ (∀ l, IsClosed (i l ⁻¹' K)) ∧ x ∉ K}
  have hstep (k : ℕ) (K : P k) :
      ∃ V : Set (X k), V ∈ 𝓝 (0 : X k) ∧ ∃ L : P (k+1), K.val + i k '' V ⊆ L.val := by
    have hs : b+k ≤ b+(k+1) := by omega
    obtain ⟨m, hm, hSm, hSmclosed, htransfer⟩ := hstable (b+(k+1))
    obtain ⟨y, hy⟩ := hSm (hmono (by omega : b ≤ b+(k+1)) hxS)
    have hyK : y ∉ i m ⁻¹' K.val := fun hyK ↦ K.property.2.2 (hy ▸ hyK)
    obtain ⟨W, hW, havoid⟩ := exists_nhds_zero_closure_add_avoids_finset
      (i m ⁻¹' K.val) (K.property.2.1 m) {y} (by simpa using hyK)
    obtain ⟨f, hf⟩ := htransition k m (by omega)
    have hfi (z : X k) : i m (f z) = i k z := DFunLike.congr_fun hf z
    let V := i k ⁻¹' S k ∩ f ⁻¹' W
    have hV : V ∈ 𝓝 (0 : X k) :=
      inter_mem (hnhds k) ((f.continuous.tendsto' 0 0 (map_zero f)) hW)
    let T := closure (i m ⁻¹' K.val + f '' V)
    let L := i m '' T
    have hT : T ⊆ i m ⁻¹' S (b+(k+1)) := by
      apply hSmclosed.closure_subset_iff.mpr
      rintro _ ⟨s, hsK, _, ⟨t, ht, rfl⟩, rfl⟩
      change i m (s + f t) ∈ S (b+(k+1))
      rw [map_add, hfi]
      exact hadd (b+k) (add_mem_add (K.property.1 hsK) (hmono (by omega : k ≤ b+k) ht.1))
    have hL : L ⊆ S (b+(k+1)) := image_subset_iff.mpr hT
    have hLy : x ∉ L := by
      rintro ⟨y', hy', he⟩
      have he' := h.injective m (he.trans hy.symm)
      apply havoid y (Finset.mem_singleton_self y)
      apply closure_mono (add_subset_add Subset.rfl ?_) (he' ▸ hy')
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    have hLclosed : ∀ l, IsClosed (i l ⁻¹' L) := by
      apply htransfer L hL
      rw [show i m ⁻¹' L = T from preimage_image_eq _ (h.injective m)]
      exact isClosed_closure
    refine ⟨V, hV, ⟨L, hL, hLclosed, hLy⟩, ?_⟩
    rintro _ ⟨s, hsK, _, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨s', hs'⟩ := hSm (hmono hs (K.property.1 hsK))
    have hs'' : s' ∈ i m ⁻¹' K.val := by rw [mem_preimage, hs']; exact hsK
    refine ⟨s' + f t, subset_closure (add_mem_add hs'' (mem_image_of_mem f ht)), ?_⟩
    rw [map_add, hs', hfi]
  let K : ∀ k, P k := Nat.rec
    ⟨A, hA.trans (hmono (show n ≤ b+0 by omega)), hclosed, hx⟩
    fun k K ↦ (hstep k K).choose_spec.2.choose
  let V (k : ℕ) := (hstep k (K k)).choose
  have hV (k : ℕ) : V k ∈ 𝓝 (0 : X k) := (hstep k (K k)).choose_spec.1
  have hKV (k : ℕ) : (K k).val + i k '' V k ⊆ (K (k+1)).val :=
    (hstep k (K k)).choose_spec.2.choose_spec
  let U := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap) ''
    {z : ⨁ k, X k | ∀ k, z k ∈ V k}
  have hU : U ∈ 𝓝 (0 : E) := h.directSum_box_image_mem_nhds V hV
  have havoid : ∀ a ∈ A, ∀ y ∈ U, a + y ≠ x := by
    rintro z hz _ ⟨w, hw, rfl⟩
    have hsum (n : ℕ) : z + (∑ k ∈ Finset.range n, i k (w k)) ∈ (K n).val := by
      induction n with
      | zero => simpa [K] using hz
      | succ n ih =>
        rw [Finset.sum_range_succ]
        simpa only [add_assoc] using hKV n (add_mem_add ih (mem_image_of_mem (i n) (hw n)))
    obtain ⟨N, hN⟩ := exists_eq_sum_stage_coords (i := i) w
    rw [hN]
    exact fun he ↦ (K N).property.2.2 (he ▸ hsum N)
  have hop : IsOpenMap (fun y : E ↦ x - y) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (isOpenMap_add_left x).comp (isOpenMap_neg E)
  refine mem_of_superset (by simpa only [sub_zero] using hop.image_mem_nhds hU) ?_
  rintro _ ⟨y, hy, rfl⟩ ha
  exact havoid _ ha y hy (sub_add_cancel x y)

/-- In a countable locally convex limit, a null sequence lies in one member of any
nested closed exhaustion whose members contain stage neighborhoods and satisfy the
doubling inclusion. If every member misses arbitrarily late terms, thicken successive
partial sums inside the exhaustion while avoiding one more term at each step. -/
private theorem IsInjectiveLCLimit.range_nullSequence_subset_closed_disk
    (h : IsInjectiveLCLimit j i) [T2Space E] [IsTopologicalAddGroup E]
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (S : ℕ → Set E) (hmono : Monotone S) (hcover : ∀ x : E, ∃ n, x ∈ S n)
    (hadd : ∀ n, S n + S n ⊆ S (n+1)) (hnhds : ∀ n, i n ⁻¹' S n ∈ 𝓝 (0 : X n))
    (hclosed : ∀ n, IsClosed (S n)) (u : ℕ → E) (hu : Tendsto u atTop (𝓝 0)) :
    ∃ n, range u ⊆ S n := by
  classical
  by_contra! hno
  have hmiss (k N : ℕ) : ∃ n, N ≤ n ∧ u n ∉ S k := by
    by_contra! htail
    choose f hf using fun n ↦ hcover (u n)
    let m := k ⊔ (Finset.range N).sup f
    obtain ⟨x, ⟨n, rfl⟩, hx⟩ := Set.not_subset.mp (hno m)
    apply hx
    by_cases hn : n < N
    · exact hmono (le_sup_of_le_right (Finset.le_sup (Finset.mem_range.mpr hn))) (hf n)
    · exact hmono le_sup_left (htail n (Nat.le_of_not_gt hn))
  let P (k : ℕ) := {K : Set E // IsClosed K ∧ K ⊆ S k}
  have hzero : (0 : E) ∈ S 0 := by
    simpa only [mem_preimage, map_zero] using mem_of_mem_nhds (hnhds 0)
  let p (k : ℕ) := (hmiss (k+1) k).choose
  have hp (k : ℕ) : k ≤ p k ∧ u (p k) ∉ S (k+1) := (hmiss (k+1) k).choose_spec
  let F (k : ℕ) := (Finset.range k).image (u ∘ p)
  let Q (k : ℕ) := {K : P k // ∀ x ∈ F k, x ∉ K.val}
  have hstep (k : ℕ) (K : Q k) :
      ∃ V : Set (X k), V ∈ 𝓝 (0 : X k) ∧
        ∃ L : Q (k+1), K.val.val + i k '' V ⊆ L.val.val := by
    obtain ⟨W, hW, havoid⟩ :=
      exists_nhds_zero_closure_add_avoids_finset K.val.val K.val.property.1 (F k) K.property
    let V := i k ⁻¹' (S k ∩ W)
    have hV : V ∈ 𝓝 (0 : X k) :=
      inter_mem (hnhds k) (((i k).continuous.tendsto' 0 0 (map_zero _)) hW)
    let L := closure (K.val.val + i k '' V)
    have hL : L ⊆ S (k+1) := (hclosed (k+1)).closure_subset_iff.mpr
      ((add_subset_add K.val.property.2 (image_preimage_subset _ _)).trans
        ((add_subset_add Subset.rfl inter_subset_left).trans (hadd k)))
    have hLF (x : E) (hx : x ∈ F (k+1)) : x ∉ L := by
      change x ∈ (Finset.range (k+1)).image (u ∘ p) at hx
      rw [Finset.range_add_one, Finset.image_insert, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact fun hx ↦ (hp k).2 (hL hx)
      · exact fun hz ↦ havoid x hx
          (closure_mono (add_subset_add Subset.rfl
            ((image_preimage_subset _ _).trans inter_subset_right)) hz)
    exact ⟨V, hV, ⟨⟨L, isClosed_closure, hL⟩, hLF⟩, subset_closure⟩
  let K : ∀ k, Q k := Nat.rec ⟨⟨{0}, isClosed_singleton, singleton_subset_iff.mpr hzero⟩,
    by simp [F]⟩ fun k K ↦ (hstep k K).choose_spec.2.choose
  let V (k : ℕ) := (hstep k (K k)).choose
  have hV (k : ℕ) : V k ∈ 𝓝 (0 : X k) := (hstep k (K k)).choose_spec.1
  have hKV (k : ℕ) : (K k).val.val + i k '' V k ⊆ (K (k+1)).val.val :=
    (hstep k (K k)).choose_spec.2.choose_spec
  have hKmono : Monotone (fun k ↦ (K k).val.val) := monotone_nat_of_le_succ fun k x hx ↦ by
    have hz : (0 : E) ∈ i k '' V k := ⟨0, mem_of_mem_nhds (hV k), map_zero _⟩
    exact hKV k (by simpa only [add_zero] using add_mem_add hx hz)
  let U := ⋃ k, (K k).val.val
  have hU : U ∈ 𝓝 (0 : E) := by
    refine mem_of_superset (h.directSum_box_image_mem_nhds V hV) ?_
    rintro _ ⟨z, hz, rfl⟩
    have hsum (n : ℕ) : (∑ k ∈ Finset.range n, i k (z k)) ∈ (K n).val.val := by
      induction n with
      | zero => simp [K]
      | succ n ih =>
        rw [Finset.sum_range_succ]
        exact hKV n (add_mem_add ih (mem_image_of_mem (i n) (hz n)))
    obtain ⟨b, hb⟩ := exists_eq_sum_stage_coords (i := i) z
    exact mem_iUnion.mpr ⟨b, hb.symm ▸ hsum b⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu hU)
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hN (p N) (hp N).1)
  let b := max k (N+1)
  exact (K b).property (u (p N)) (Finset.mem_image.mpr
    ⟨N, Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _)), rfl⟩)
    (hKmono (le_max_left _ _) hk)

/-- Acyclicity of a Fréchet–Montel system gives bounded stage representatives for each
null sequence in its Hausdorff limit. This is the null-sequence lifting part of
Wengenroth's Theorem 3.3. -/
private theorem IsInjectiveLCLimit.lifts_nullSequence_of_acyclic (h : IsInjectiveLCLimit j i)
    [T2Space E] (hX : ∀ k, IsFrechetTVS (X k)) (hM : ∀ k, MontelSpace ℂ (X k))
    (hacyclic : IsAcyclicSystem j) (u : ℕ → E) (hu : Tendsto u atTop (𝓝 0)) :
    ∃ k, ∃ v : ℕ → X k, IsVonNBounded ℂ (range v) ∧ ∀ n, i k (v n) = u n := by
  have hX' := hX
  choose hgroup hpoly _ _ using hX'
  let : ∀ k, IsTopologicalAddGroup (X k) := hgroup
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, ContinuousSMul ℂ (X k) := fun k ↦ PolynormableSpace.continuousSMul ℂ (X k)
  have hE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hE.isTopologicalAddGroup
  obtain ⟨S, hmono, hcover, hadd, hnhds, hstable⟩ := h.exists_stagewise_stable_disks hX hacyclic
  have hclosed (n : ℕ) : IsClosed (S n) := by
    obtain ⟨k, _, _, hk, htransfer⟩ := hstable n
    exact h.isClosed_of_stagewise_closed_in_stable_disks hX S hmono hcover hadd hnhds hstable
      (S n) n Subset.rfl (htransfer _ Subset.rfl hk)
  obtain ⟨n, hn⟩ := h.range_nullSequence_subset_closed_disk S hmono hcover hadd hnhds hclosed u hu
  obtain ⟨k, _, hsub, hk, htransfer⟩ := hstable n
  let C := i k ⁻¹' S n
  let f (x : C) := i k (x : X k)
  have hf : range f = S n := by
    change range ((i k) ∘ (Subtype.val : C → X k)) = S n
    rw [range_comp, Subtype.range_coe_subtype]
    exact image_preimage_eq_of_subset hsub
  have hfemb : IsClosedEmbedding f := by
    refine IsClosedEmbedding.of_continuous_injective_isClosedMap
      ((i k).continuous.comp continuous_subtype_val)
      (fun _ _ he ↦ Subtype.ext (h.injective k he)) ?_
    intro A hA
    have hpre : i k ⁻¹' (f '' A) = Subtype.val '' A := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, h.injective k he⟩
      · rintro ⟨y, hy, rfl⟩
        exact mem_image_of_mem f hy
    have hA' : f '' A ⊆ S n := hf ▸ image_subset_range _ _
    apply h.isClosed_of_stagewise_closed_in_stable_disks hX S hmono hcover hadd hnhds hstable
      (f '' A) n hA'
    apply htransfer _ hA'
    rw [hpre]
    exact hk.isClosedMap_subtype_val _ hA
  have hK := (hfemb.isCompact_preimage hu.isCompact_insert_range).image
    (continuous_subtype_val : Continuous (Subtype.val : C → X k))
  choose v hv using fun m ↦ hf.symm ▸ hn (mem_range_self m)
  refine ⟨k, fun m ↦ (v m : X k), hK.isVonNBounded ℂ |>.subset ?_, hv⟩
  rintro _ ⟨m, rfl⟩
  refine ⟨v m, ?_, rfl⟩
  change f (v m) ∈ insert 0 (range u)
  rw [hv m]
  exact mem_insert_of_mem _ (mem_range_self m)

/-- The composite of the transition maps from stage `a` to stage `b`. -/
def limitStageTransition (j : ∀ k, X k →L[ℂ] X (k+1))
    {a b : ℕ} (hab : a ≤ b) : X a →L[ℂ] X b :=
  Nat.leRec (ContinuousLinearMap.id ℂ (X a)) (fun {k} _ f ↦ (j k).comp f) hab

/-- Advancing the destination stage by one composes with its transition map. -/
private theorem limitStageTransition_succ {a b : ℕ} (hab : a ≤ b) :
    limitStageTransition j (Nat.le_succ_of_le hab) =
      (j b).comp (limitStageTransition j hab) := by
  unfold limitStageTransition
  rw [Nat.leRec_succ _ _ hab]

/-- Composites of consecutive blocks of transition maps concatenate. -/
private theorem limitStageTransition_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    limitStageTransition j (hab.trans hbc) =
      (limitStageTransition j hbc).comp (limitStageTransition j hab) := by
  induction c, hbc using Nat.le_induction with
  | base => simp [limitStageTransition, Nat.leRec_self]
  | succ c hbc ih =>
    rw [limitStageTransition_succ (hab.trans hbc), limitStageTransition_succ hbc, ih,
      ContinuousLinearMap.comp_assoc]

/-- Passing to a later stage preserves the image in the limit. -/
private theorem IsInjectiveLCLimit.limitStageTransition_apply (h : IsInjectiveLCLimit j i)
    {a b : ℕ} (hab : a ≤ b) (z : X a) :
    i b (limitStageTransition j hab z) = i a z := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp [limitStageTransition, Nat.leRec_self]
  | succ b hab ih =>
    have heq : i (b+1) (j b (limitStageTransition j hab z)) =
        i b (limitStageTransition j hab z) :=
      DFunLike.congr_fun (h.compatible b) _
    unfold limitStageTransition
    rw [Nat.leRec_succ _ _ hab]
    exact heq.trans ih

/-- Compact lifting forces a uniform stage for null sequences drawn from a single
zero-neighborhood of a fixed stage. The neighborhood and the later stage are chosen
before the sequence. -/
private theorem IsInjectiveLCLimit.exists_stage_tendsto_of_compact_lift
    (h : IsInjectiveLCLimit j i) [T2Space E] [∀ k, FirstCountableTopology (X k)]
    (hlift : ∀ K : Set E, IsCompact K → ∃ k, ∃ C : Set (X k), IsCompact C ∧ i k '' C = K)
    (a : ℕ) :
    ∃ (m : ℕ) (ham : a ≤ m) (U : Set (X a)), U ∈ 𝓝 0 ∧
      ∀ v : ℕ → X a, (∀ n, v n ∈ U) → Tendsto (i a ∘ v) atTop (𝓝 0) →
        Tendsto (limitStageTransition j ham ∘ v) atTop (𝓝 0) := by
  classical
  obtain ⟨U, hU⟩ := (𝓝 (0 : X a)).exists_antitone_basis
  by_contra! hno
  have hfail (n : ℕ) := hno (a + n) (Nat.le_add_right a n) (U n)
    (hU.toHasBasis.mem_of_mem trivial)
  choose v hv hlim hbad using hfail
  let K : Set E := ⋃ n, insert 0 (range (i a ∘ v n))
  -- Every open neighborhood of zero contains all but finitely many entire rows.
  have hsmall (V : Set E) (hV : V ∈ 𝓝 0) :
      ∃ N : ℕ, ∀ n ≥ N, range (i a ∘ v n) ⊆ V := by
    have hpre : i a ⁻¹' V ∈ 𝓝 (0 : X a) := (i a).continuous.tendsto' 0 0 (map_zero _) hV
    obtain ⟨N, -, hN⟩ := hU.toHasBasis.mem_iff.mp hpre
    refine ⟨N, fun n hn ↦ ?_⟩
    rintro _ ⟨b, rfl⟩
    exact hN (hU.antitone hn (hv n b))
  have hzero : (0 : E) ∈ K := mem_iUnion.mpr ⟨0, mem_insert _ _⟩
  have hK : IsCompact K := by
    apply isCompact_of_finite_subcover
    intro ι W hW hcover
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hcover hzero)
    obtain ⟨N, hN⟩ := hsmall (W c) ((hW c).mem_nhds hc)
    let row (n : ℕ) := insert (0 : E) (range (i a ∘ v n))
    obtain ⟨t, ht⟩ := ((Finset.range N).isCompact_biUnion
      (f := row) fun n _ ↦ (hlim n).isCompact_insert_range).elim_finite_subcover W hW
        (fun x hx ↦ hcover (by
          obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp hx
          exact mem_iUnion.mpr ⟨n, hn⟩))
    refine ⟨insert c t, ?_⟩
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    by_cases hN' : n < N
    · obtain ⟨b, hb, hxb⟩ :=
        mem_iUnion₂.mp (ht (mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hN', hn⟩))
      exact mem_iUnion₂.mpr ⟨b, Finset.mem_insert_of_mem hb, hxb⟩
    · refine mem_iUnion₂.mpr ⟨c, Finset.mem_insert_self _ _, ?_⟩
      rcases mem_insert_iff.mp hn with rfl | hx'
      · exact hc
      · exact hN n (Nat.le_of_not_gt hN') hx'
  obtain ⟨k, C, hC, himage⟩ := hlift K hK
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C → E := fun z ↦ i k z
  have hf : IsEmbedding f :=
    (((i k).continuous.comp continuous_subtype_val).isClosedEmbedding
      ((h.injective k).comp Subtype.val_injective)).isEmbedding
  have hsurj (z : E) (hz : z ∈ K) : ∃ w : C, f w = z := by
    obtain ⟨w, hw, he⟩ := himage.symm ▸ hz
    exact ⟨⟨w, hw⟩, he⟩
  obtain ⟨w₀, hw₀⟩ := hsurj 0 hzero
  have hw₀' : (w₀ : X k) = 0 := h.injective k (hw₀.trans (map_zero _).symm)
  have hrow (b : ℕ) : i a (v k b) ∈ K :=
    mem_iUnion.mpr ⟨k, mem_insert_of_mem _ (mem_range_self b)⟩
  choose w hw using fun b ↦ hsurj _ (hrow b)
  have hwlim : Tendsto w atTop (𝓝 w₀) := hf.tendsto_nhds_iff.mpr (by
    rw [hw₀, show f ∘ w = i a ∘ v k from funext hw]
    exact hlim k)
  let g := limitStageTransition j (Nat.le_add_left k a)
  have hg : Tendsto (fun b ↦ g (w b)) atTop (𝓝 0) :=
    (g.continuous.tendsto' w₀ 0 (by rw [hw₀', map_zero])).comp
      (continuous_subtype_val.tendsto w₀ |>.comp hwlim)
  apply hbad k
  convert hg using 1
  funext b
  apply h.injective (a + k)
  exact (h.limitStageTransition_apply _ _).trans ((hw b).symm.trans
    (h.limitStageTransition_apply _ _).symm)

/-- A uniform stage for null sequences yields a seminorm estimate. On the original
stage one fixed continuous seminorm can be given an arbitrarily small coefficient,
with the remainder controlled by a continuous seminorm on any further stage. -/
theorem IsInjectiveLCLimit.exists_stage_seminorm_interpolation
    (h : IsInjectiveLCLimit j i) [T2Space E] [∀ k, FirstCountableTopology (X k)]
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (hlift : ∀ K : Set E, IsCompact K → ∃ k, ∃ C : Set (X k), IsCompact C ∧ i k '' C = K)
    (a : ℕ) :
    ∃ (m : ℕ) (ham : a ≤ m) (p : Seminorm ℂ (X a)), Continuous p ∧
      ∀ (l : ℕ) (hal : a ≤ l), m ≤ l →
        ∀ (q : Seminorm ℂ (X m)), Continuous q → ∀ ε : ℝ, 0 < ε →
          ∃ r : Seminorm ℂ (X l), Continuous r ∧
            ∀ z, q (limitStageTransition j ham z) ≤ ε * p z + r (limitStageTransition j hal z) := by
  obtain ⟨m, ham, U, hU, hseq⟩ := h.exists_stage_tendsto_of_compact_lift hlift a
  obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ (X a)).mem_iff.mp hU
  refine ⟨m, ham, p, hp, fun l hal _ q hq ε hε ↦ ?_⟩
  obtain ⟨V, hV⟩ := (𝓝 (0 : X l)).exists_antitone_basis
  have hballs (n : ℕ) := (PolynormableSpace.hasBasis_zero_ball ℂ (X l)).mem_iff.mp
    (hV.toHasBasis.mem_of_mem (i := n) trivial)
  choose r hr hrV using hballs
  by_contra! hno
  have hfail (n : ℕ) := hno (ε.toNNReal • r n)
    (show Continuous (fun z ↦ (ε.toNNReal : ℝ) * r n z) from (hr n).const_mul _)
  choose z hz using hfail
  let A := limitStageTransition j ham
  let B := limitStageTransition j hal
  have hineq (n : ℕ) : ε * p (z n) + ε * r n (B (z n)) < q (A (z n)) := by
    have hn := hz n
    change ε * p (z n) + (ε.toNNReal : ℝ) * r n (B (z n)) < q (A (z n)) at hn
    rwa [Real.coe_toNNReal _ hε.le] at hn
  have hpos (n : ℕ) : 0 < q (A (z n)) :=
    lt_of_le_of_lt (by positivity) (hineq n)
  let v (n : ℕ) : X a := ((ε / q (A (z n)) : ℝ) : ℂ) • z n
  have hvnorm (n : ℕ) : ‖((ε / q (A (z n)) : ℝ) : ℂ)‖ = ε / q (A (z n)) :=
    Complex.norm_of_nonneg (div_nonneg hε.le (hpos n).le)
  have hvU (n : ℕ) : v n ∈ U := by
    apply hpU
    rw [Seminorm.mem_ball_zero]
    dsimp only [v]
    rw [map_smul_eq_mul, hvnorm, div_mul_eq_mul_div,
      div_lt_iff₀ (hpos n), one_mul]
    exact (le_add_of_nonneg_right (by positivity)).trans_lt (hineq n)
  have hvV (n : ℕ) : B (v n) ∈ V n := by
    apply hrV n
    rw [Seminorm.mem_ball_zero]
    dsimp only [v]
    rw [map_smul, map_smul_eq_mul, hvnorm, div_mul_eq_mul_div,
      div_lt_iff₀ (hpos n), one_mul]
    exact (le_add_of_nonneg_left (by positivity)).trans_lt (hineq n)
  have hB : Tendsto (B ∘ v) atTop (𝓝 0) := hV.tendsto hvV
  have hi : Tendsto (i a ∘ v) atTop (𝓝 0) := by
    have heq : i l ∘ (B ∘ v) = i a ∘ v :=
      funext fun n ↦ h.limitStageTransition_apply _ _
    rw [← heq]
    exact ((i l).continuous.tendsto' 0 0 (map_zero _)).comp hB
  have hlim := (hq.tendsto' 0 0 (map_zero _)).comp (hseq v hvU hi)
  have heq : q ∘ (A ∘ v) = fun _ ↦ ε := by
    funext n
    change q (A (((ε / q (A (z n)) : ℝ) : ℂ) • z n)) = ε
    rw [map_smul, map_smul_eq_mul, hvnorm, div_mul_cancel₀ _ (hpos n).ne']
  change Tendsto (q ∘ (A ∘ v)) atTop (𝓝 0) at hlim
  rw [heq] at hlim
  exact hε.ne' (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- A vector in a single summand contributes to that summand and its successor. -/
theorem directSumDifference_lof (j : ∀ k, X k →L[ℂ] X (k+1)) (k : ℕ) (z : X k) :
    directSumDifference j (DirectSum.lof ℂ ℕ X k z) =
      DirectSum.lof ℂ ℕ X k z - DirectSum.lof ℂ ℕ X (k+1) (j k z) := by
  rw [directSumDifference, LinearMap.sub_apply, LinearMap.id_apply, DirectSum.toModule_lof]
  rfl

/-- A stage vector propagated along a finite interval of coordinates of the direct sum. -/
private def propagateStageVector (j : ∀ k, X k →L[ℂ] X (k+1)) (a : ℕ) :
    ℕ → X a →ₗ[ℂ] (⨁ k, X k)
  | 0 => 0
  | d+1 => DirectSum.lof ℂ ℕ X a + (propagateStageVector j (a+1) d).comp (j a).toLinearMap

/-- A seminorm bound for the inverse on a cofinal subsequence gives one on the original
spectrum. Propagate the recovered coordinates at the retained stages and add the
increments between consecutive retained stages. -/
private theorem directSumDifference_seminorm_bound_of_cofinal
    [∀ k, IsTopologicalAddGroup (X k)]
    [dec : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)]
    {a : ℕ → ℕ} (ha : StrictMono a)
    (hbound : letI : ∀ (k : ℕ) (z : X (a k)), Decidable (z ≠ 0) := fun k ↦ dec (a k)
      ∀ s : ∀ k, Seminorm ℂ (X (a k)), (∀ k, Continuous (s k)) →
        ∃ r : ∀ k, Seminorm ℂ (X (a k)), (∀ k, Continuous (r k)) ∧
          ∀ x, directSumSeminorm s x ≤ directSumSeminorm r
            (directSumDifference (fun k ↦ limitStageTransition j (ha (Nat.lt_succ_self k)).le) x))
    (s : ∀ k, Seminorm ℂ (X k)) (hs : ∀ k, Continuous (s k)) :
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ x, directSumSeminorm s x ≤ directSumSeminorm r (directSumDifference j x) := by
  classical
  let Y (k : ℕ) := X (a k)
  let : ∀ (k : ℕ) (z : Y k), Decidable (z ≠ 0) := fun k ↦ dec (a k)
  let : ∀ k, IsTopologicalAddGroup (Y k) := fun _ ↦ inferInstance
  let D := ⨁ k, X k
  let D' := ⨁ k, Y k
  let L := DirectSum.lof ℂ ℕ X
  let L' := DirectSum.lof ℂ ℕ Y
  let : TopologicalSpace D := locallyConvexFinalTopology L
  let : TopologicalSpace D' := locallyConvexFinalTopology L'
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ L k)} → Seminorm ℂ D) := ⟨rfl⟩
  have hD' : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D' // ∀ k, Continuous (p ∘ L' k)} → Seminorm ℂ D') := ⟨rfl⟩
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  have hL (k : ℕ) : Continuous (L k) :=
    hD.continuous_of_continuous_comp _ fun p ↦ p.property k
  have hprop (k d : ℕ) : Continuous (propagateStageVector j k d) := by
    induction d generalizing k with
    | zero => exact continuous_zero
    | succ d ih => exact (hL k).add ((ih (k+1)).comp (j k).continuous)
  have hex (k : ℕ) : ∃ n, k ≤ a n := ⟨k, ha.id_le k⟩
  let next (k : ℕ) := Nat.find (hex k)
  have hnext (k : ℕ) : k ≤ a (next k) := Nat.find_spec (hex k)
  have hleast (k n : ℕ) (hkn : k ≤ a n) : next k ≤ n := Nat.find_min' (hex k) hkn
  have hself (n : ℕ) : next (a n) = n :=
    le_antisymm (hleast _ _ le_rfl) (ha.le_iff_le.mp (hnext _))
  have hsucc (n : ℕ) : next (a n + 1) = n+1 := by
    apply le_antisymm (hleast _ _ (ha (Nat.lt_succ_self _)))
    exact Nat.succ_le_of_lt (ha.lt_iff_lt.mp (hnext _))
  have hskip (k : ℕ) (hk : k ∉ range a) : next (k+1) = next k := by
    have hlt : k < a (next k) := lt_of_le_of_ne (hnext k) fun he ↦ hk ⟨_, he.symm⟩
    exact le_antisymm (hleast _ _ hlt) (hleast _ _ (Nat.le_of_succ_le (hnext (k+1))))
  let Gk (k : ℕ) : X k →ₗ[ℂ] D' := (L' (next k)).comp (limitStageTransition j (hnext k)).toLinearMap
  let Hk (k : ℕ) : X k →ₗ[ℂ] D := propagateStageVector j k (a (next k) - k)
  let Fk (n : ℕ) : Y n →ₗ[ℂ] D := propagateStageVector j (a n) (a (n+1) - a n)
  let G := DirectSum.toModule ℂ ℕ D' Gk
  let H := DirectSum.toModule ℂ ℕ D Hk
  let F := DirectSum.toModule ℂ ℕ D Fk
  let P : D →ₗ[ℂ] D' :=
    { toFun := DFinsupp.comapDomain a ha.injective
      map_add' := DFinsupp.comapDomain_add a ha.injective
      map_smul' := DFinsupp.comapDomain_smul a ha.injective }
  let J (n : ℕ) : Y n →L[ℂ] Y (n+1) := limitStageTransition j (ha (Nat.lt_succ_self n)).le
  let σ := directSumDifference j
  let σ' := directSumDifference J
  have hP (n : ℕ) (z : Y n) : P (L (a n) z) = L' n z :=
    DFinsupp.comapDomain_single a ha.injective n z
  have hPzero (k : ℕ) (hk : k ∉ range a) (z : X k) : P (L k z) = 0 := by
    apply DFinsupp.ext
    intro n
    change L k z (a n) = 0
    change DFinsupp.single k z (a n) = 0
    exact DFinsupp.single_eq_of_ne (fun he ↦ hk ⟨n, he⟩)
  have hσ (k : ℕ) (z : X k) : σ (L k z) = L k z - L (k+1) (j k z) :=
    directSumDifference_lof j k z
  have hσ' (n : ℕ) (z : Y n) : σ' (L' n z) = L' n z - L' (n+1) (J n z) :=
    directSumDifference_lof J n z
  have hGk (k : ℕ) (z : X k) : G (L k z) = Gk k z := DirectSum.toModule_lof _ _ _
  have hHk (k : ℕ) (z : X k) : H (L k z) = Hk k z := DirectSum.toModule_lof _ _ _
  have hFk (n : ℕ) (z : Y n) : F (L' n z) = Fk n z := DirectSum.toModule_lof _ _ _
  have hGk_eq (k n : ℕ) (hn : next k = n) (z : X k) :
      Gk k z = L' n (limitStageTransition j (hn ▸ hnext k) z) := by
    subst n
    rfl
  have hstep (k n : ℕ) (hkn : k+1 ≤ n) (z : X k) :
      limitStageTransition j (Nat.le_of_succ_le hkn) z =
        limitStageTransition j hkn (j k z) := by
    rw [limitStageTransition_trans (Nat.le_succ k) hkn]
    rw [limitStageTransition_succ (le_refl k)]
    simp [limitStageTransition, Nat.leRec_self]
  have hGcomp : G.comp σ = σ'.comp P := by
    apply DirectSum.linearMap_ext
    intro k
    ext z : 1
    change G (σ (L k z)) = σ' (P (L k z))
    rw [hσ, map_sub, hGk, hGk]
    by_cases hk : k ∈ range a
    · obtain ⟨n, rfl⟩ := hk
      rw [hP, hσ']
      have hfirst : Gk (a n) z = L' n z := by
        rw [hGk_eq _ _ (hself n)]
        simp [limitStageTransition, Nat.leRec_self]
      have hsecond : Gk (a n + 1) (j (a n) z) = L' (n+1) (J n z) := by
        rw [hGk_eq _ _ (hsucc n), ← hstep (a n) (a (n+1)) (ha (Nat.lt_succ_self n))]
      rw [hfirst, hsecond]
    · rw [hPzero k hk, map_zero, sub_eq_zero]
      rw [hGk_eq (k+1) (next k) (hskip k hk), hGk_eq k (next k) rfl,
        hstep k (a (next k)) (hskip k hk ▸ hnext (k+1))]
  have hreconstruct : F.comp P + H.comp σ = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro k
    ext z : 1
    change F (P (L k z)) + H (σ (L k z)) = L k z
    rw [hσ, map_sub, hHk, hHk]
    by_cases hk : k ∈ range a
    · obtain ⟨n, rfl⟩ := hk
      rw [hP, hFk]
      have hlen : a (n+1) - a n = a (n+1) - (a n + 1) + 1 := by
        have hlt : a n < a (n+1) := ha (Nat.lt_succ_self n)
        omega
      have hpart : Fk n z = L (a n) z + Hk (a n + 1) (j (a n) z) := by
        simp only [Fk, Hk, hsucc]
        nth_rw 1 [hlen]
        rfl
      rw [show Hk (a n) z = 0 by simp [Hk, hself, propagateStageVector]]
      rw [hpart, zero_sub, ← sub_eq_add_neg, add_sub_cancel_right]
    · rw [hPzero k hk, map_zero, zero_add]
      have hlen : a (next k) - k = a (next k) - (k+1) + 1 := by
        have hlt : k < a (next k) := lt_of_le_of_ne (hnext k) fun he ↦ hk ⟨_, he.symm⟩
        omega
      have hpart : Hk k z = L k z + Hk (k+1) (j k z) := by
        simp only [Hk, hskip k hk]
        nth_rw 1 [hlen]
        rfl
      rw [hpart, add_sub_cancel_right]
  let p := directSumSeminorm s
  have hp : Continuous p := by
    refine hD.continuous_seminorm (i := ⟨p, fun k ↦ ?_⟩)
    change Continuous (fun z : X k ↦ directSumSeminorm s (DirectSum.lof ℂ ℕ X k z))
    simpa only [directSumSeminorm_lof] using hs k
  let s' (n : ℕ) := p.comp (Fk n)
  obtain ⟨r', hr', hbound'⟩ := hbound s' fun n ↦ hp.comp (hprop _ _)
  let p' : Seminorm ℂ D' := directSumSeminorm (X := Y) r'
  have hp' : Continuous p' := by
    refine hD'.continuous_seminorm (i := ⟨p', fun k ↦ ?_⟩)
    have heq (z : Y k) : p' (L' k z) = r' k z :=
      directSumSeminorm_lof (X := Y) r' k z
    change Continuous (fun z : Y k ↦ p' (L' k z))
    simpa only [heq] using hr' k
  have hL' (k : ℕ) : Continuous (L' k) :=
    hD'.continuous_of_continuous_comp _ fun p ↦ p.property k
  let q := p'.comp G + p.comp H
  let r (k : ℕ) := q.comp (L k)
  have hr (k : ℕ) : Continuous (r k) := by
    change Continuous (fun z : X k ↦ p' (G (L k z)) + p (H (L k z)))
    simp_rw [hGk, hHk]
    exact (hp'.comp ((hL' _).comp (limitStageTransition j (hnext k)).continuous)).add
      (hp.comp (hprop _ _))
  have hFp (z : D') : p (F z) ≤ directSumSeminorm s' z := by
    have hsum := Finset.le_sum_of_subadditive (p.comp F) (map_zero (p.comp F)).le
      (map_add_le_add (p.comp F)) z.support (fun k ↦ L' k (z k))
    have hdecomp : (∑ k ∈ z.support, L' k (z k)) = z := DirectSum.sum_support_of z
    rw [hdecomp] at hsum
    rw [directSumSeminorm_apply s' z _ Subset.rfl]
    simpa only [s', Seminorm.comp_apply, hFk] using hsum
  refine ⟨r, hr, fun x ↦ ?_⟩
  have hsplit : F (P x) + H (σ x) = x := LinearMap.congr_fun hreconstruct x
  have hcomm : G (σ x) = σ' (P x) := LinearMap.congr_fun hGcomp x
  have hq : q (σ x) ≤ directSumSeminorm r (σ x) := by
    have hsum := Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q)
      (σ x).support (fun k ↦ L k (σ x k))
    have hdecomp : (∑ k ∈ (σ x).support, L k (σ x k)) = σ x := DirectSum.sum_support_of (σ x)
    rw [hdecomp] at hsum
    rw [directSumSeminorm_apply _ _ _ Subset.rfl]
    exact hsum
  have hcontrol : directSumSeminorm s' (P x) ≤ p' (G (σ x)) := by
    rw [hcomm]
    exact hbound' (P x)
  change p x ≤ directSumSeminorm r (σ x)
  conv => lhs; rw [← hsplit]
  -- The retained coordinates and the skipped increments are controlled separately.
  exact (map_add_le_add p (F (P x)) (H (σ x))).trans
    ((add_le_add ((hFp (P x)).trans hcontrol) (le_refl (p (H (σ x))))).trans hq)

open scoped NNReal in
/-- For a spectrum with seminorm interpolation across consecutive triples of stages,
a weighted estimate for the inverse follows from a forward bound on the partial
sums and a backward bound starting beyond the support. This follows the sufficiency
argument in Vogt, `On the splitting relation for Fréchet-Hilbert spaces`, §2. -/
private theorem directSumDifference_seminorm_bound_adjacent
    [∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)]
    (p : ∀ k, Seminorm ℂ (X k)) (hp : ∀ k, Continuous (p k))
    (hinterp : ∀ (k : ℕ) (q : Seminorm ℂ (X (k+1))), Continuous q →
      ∃ r : Seminorm ℂ (X (k+2)), Continuous r ∧
        ∀ z, q (j k z) ≤ p k z + r (j (k+1) (j k z)))
    (s : ∀ k, Seminorm ℂ (X k)) (hs : ∀ k, Continuous (s k)) :
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ x, directSumSeminorm s x ≤ directSumSeminorm r (directSumDifference j x) := by
  classical
  -- Retain the error term from the previous stage when applying interpolation.
  choose step hstep hstep_bound using fun k (t : {t : Seminorm ℂ (X (k+1)) // Continuous t}) ↦
    hinterp k (p (k+1) + t.val) ((hp (k+1)).add t.property)
  let t : ∀ k, {t : Seminorm ℂ (X (k+1)) // Continuous t} :=
    Nat.rec ⟨0, continuous_zero⟩ fun k t ↦ ⟨step k t, hstep k t⟩
  let b (k : ℕ) := p k + (t k).val.comp (j k).toLinearMap
  have hb (k : ℕ) : Continuous (b k) := (hp k).add ((t k).property.comp (j k).continuous)
  have ht (k : ℕ) (z : X k) :
      p (k+1) (j k z) + (t k).val (j k z) ≤ p k z + (t (k+1)).val (j (k+1) (j k z)) :=
    hstep_bound k (t k) z
  let y := directSumDifference j
  have hforward (x : ⨁ k, X k) (k : ℕ) :
      p k (x k) ≤ (∑ l ∈ Finset.range (k+1), b l (y x l)) + (t k).val (j k (x k)) := by
    induction k with
    | zero => simp [y, b, t, (directSumDifference_apply j x).1]
    | succ k ih =>
      have hcoord : y x (k+1) = x (k+1) - j k (x k) :=
        (directSumDifference_apply j x).2 k
      have hsum : x (k+1) = j k (x k) + y x (k+1) := by rw [hcoord, add_sub_cancel]
      have hp' := map_add_le_add (p (k+1)) (j k (x k)) (y x (k+1))
      rw [← hsum] at hp'
      have ht' := map_sub_le_add (t (k+1)).val (j (k+1) (x (k+1))) (j (k+1) (y x (k+1)))
      conv at ht' => lhs; rw [← map_sub, hcoord, sub_sub_cancel]
      rw [Finset.sum_range_succ]
      change _ ≤ _ + (p (k+1) (y x (k+1)) + (t (k+1)).val (j (k+1) (y x (k+1)))) + _
      linarith [ht k (x k)]
  let weight (k : ℕ) : ℝ≥0 := 4 * 2 ^ k
  choose next hnext hnext_bound using fun k (u : {q : Seminorm ℂ (X (k+1)) // Continuous q}) ↦
    hinterp k (u.val + (t k).val) (u.property.add (t k).property)
  -- Each successive control seminorm absorbs twice the preceding error.
  let R : ∀ k, {r : Seminorm ℂ (X k) // Continuous r} :=
    fun k ↦ match k with
    | 0 => ⟨weight 0 • s 0, (hs 0).const_mul _⟩
    | k+1 => Nat.rec (motive := fun k ↦ {r : Seminorm ℂ (X (k+1)) // Continuous r})
        ⟨weight 1 • s 1, (hs 1).const_mul _⟩
        (fun k r ↦ ⟨weight (k+2) • s (k+2) + (2 : ℝ≥0) • next k r,
          ((hs (k+2)).const_mul _).add ((hnext k r).const_mul _)⟩) k
  let err (k : ℕ) := next k (R (k+1))
  have hErr (k : ℕ) (z : X (k+2)) : 2 * err k z ≤ (R (k+2)).val z := by
    change 2 * err k z ≤ (weight (k+2) : ℝ) * s (k+2) z + 2 * err k z
    exact le_add_of_nonneg_left (by positivity)
  have hR (k : ℕ) (z : X k) : (weight k : ℝ) * s k z ≤ (R k).val z := by
    rcases k with _ | _ | k
    · exact le_rfl
    · exact le_rfl
    · change _ ≤ _ + 2 * err k z
      exact le_add_of_nonneg_right (by positivity)
  let r (k : ℕ) := b k + (R k).val + match k with
    | 0 => 0
    | 1 => (err 0).comp (j 1).toLinearMap
    | k+2 => err k + (err (k+1)).comp (j (k+2)).toLinearMap
  have hr (k : ℕ) : Continuous (r k) := by
    apply ((hb k).add (R k).property).add
    rcases k with _ | _ | k
    · exact continuous_zero
    · exact (hnext 0 (R 1)).comp (j 1).continuous
    · exact (hnext k (R (k+1))).add ((hnext (k+1) (R (k+2))).comp (j (k+2)).continuous)
  have hb_le (k : ℕ) (z : X k) : b k z ≤ r k z := by
    calc
      _ ≤ (b k + (R k).val) z := le_add_of_nonneg_right (apply_nonneg (R k).val z)
      _ ≤ _ := le_add_of_nonneg_right (apply_nonneg _ z)
  have hlocal (x : ⨁ k, X k) (k : ℕ) :
      (R k).val (x k) ≤ directSumSeminorm r (y x) + (R (k+1)).val (x (k+1)) / 2 := by
    cases k with
    | zero =>
      have h0 : (R 0).val (y x 0) ≤ r 0 (y x 0) := by
        change _ ≤ b 0 (y x 0) + (R 0).val (y x 0) + 0
        simp [apply_nonneg (b 0) (y x 0)]
      rw [← (directSumDifference_apply j x).1]
      exact (h0.trans (by simpa only [Finset.sum_singleton] using sum_le_directSumSeminorm r (y x) {0})).trans
        (le_add_of_nonneg_right (by positivity))
    | succ k =>
      have hcoord (l : ℕ) : y x (l+1) = x (l+1) - j l (x l) :=
        (directSumDifference_apply j x).2 l
      have hsum : x (k+1) = j k (x k) + y x (k+1) := by rw [hcoord, add_sub_cancel]
      have hnext_sum : j (k+1) (j k (x k)) =
          (x (k+2) - y x (k+2)) - j (k+1) (y x (k+1)) := by
        rw [hcoord (k+1), sub_sub_cancel, ← map_sub, hcoord k, sub_sub_cancel]
      have h1 := hnext_bound k (R (k+1)) (x k)
      change (R (k+1)).val (j k (x k)) + (t k).val (j k (x k)) ≤
        p k (x k) + err k (j (k+1) (j k (x k))) at h1
      have h2 := map_add_le_add (R (k+1)).val (j k (x k)) (y x (k+1))
      rw [← hsum] at h2
      have h3 := map_sub_le_add (err k) (x (k+2) - y x (k+2)) (j (k+1) (y x (k+1)))
      rw [← hnext_sum] at h3
      have h4 := map_sub_le_add (err k) (x (k+2)) (y x (k+2))
      have h5 : (R (k+1)).val (y x (k+1)) + err k (j (k+1) (y x (k+1))) ≤ r (k+1) (y x (k+1)) := by
        cases k with
        | zero =>
          change _ ≤ b 1 (y x 1) + (R 1).val (y x 1) + err 0 (j 1 (y x 1))
          linarith [apply_nonneg (b 1) (y x 1)]
        | succ k =>
          change _ ≤ b (k+2) (y x (k+2)) + (R (k+2)).val (y x (k+2)) +
            (err k (y x (k+2)) + err (k+1) (j (k+2) (y x (k+2))))
          linarith [apply_nonneg (b (k+2)) (y x (k+2)), apply_nonneg (err k) (y x (k+2))]
      have h6 : err k (y x (k+2)) ≤ r (k+2) (y x (k+2)) := by
        change _ ≤ b (k+2) (y x (k+2)) + (R (k+2)).val (y x (k+2)) +
          (err k (y x (k+2)) + err (k+1) (j (k+2) (y x (k+2))))
        linarith [apply_nonneg (b (k+2)) (y x (k+2)),
          apply_nonneg (R (k+2)).val (y x (k+2)),
          apply_nonneg (err (k+1)) (j (k+2) (y x (k+2)))]
      have h7 := sum_le_directSumSeminorm r (y x) (Finset.range (k+3))
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at h7
      have h8 : (∑ l ∈ Finset.range (k+1), b l (y x l)) ≤
          ∑ l ∈ Finset.range (k+1), r l (y x l) := Finset.sum_le_sum fun l _ ↦ hb_le l _
      linarith [hforward x k, hErr k (x (k+2))]
  refine ⟨r, hr, fun x ↦ ?_⟩
  let Q := directSumSeminorm r (y x)
  have hQ : 0 ≤ Q := apply_nonneg _ _
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range x.support
  have hcontrol (k : ℕ) : (R k).val (x k) ≤ 2 * Q := by
    by_cases hk : k ≤ N
    · induction hk using Nat.decreasingInduction with
      | self =>
        have hzero : x N = 0 := DFinsupp.notMem_support_iff.mp fun hmem ↦
          (Nat.lt_irrefl N) (Finset.mem_range.mp (hN hmem))
        rw [hzero, map_zero]
        positivity
      | of_succ k hk ih => linarith [hlocal x k]
    · have hzero : x k = 0 := DFinsupp.notMem_support_iff.mp fun hmem ↦
        hk (Finset.mem_range.mp (hN hmem)).le
      rw [hzero, map_zero]
      positivity
  rw [directSumSeminorm_apply _ _ _ hN]
  calc
    _ ≤ ∑ k ∈ Finset.range N, (1 / 2 : ℝ)^k * (Q / 2) := by
      apply Finset.sum_le_sum
      intro k _
      have hpos : 0 < (2 : ℝ)^k := by positivity
      rw [one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ hpos]
      have hweight : (weight k : ℝ) = 4 * 2^k := by simp [weight]
      have hle := (hR k (x k)).trans (hcontrol k)
      rw [hweight] at hle
      nlinarith
    _ = (∑ k ∈ Finset.range N, (1 / 2 : ℝ)^k) * (Q / 2) := (Finset.sum_mul ..).symm
    _ ≤ Q := by
      have hsum (n : ℕ) : (∑ k ∈ Finset.range n, (1 / 2 : ℝ)^k) =
          2 - 2 * (1 / 2 : ℝ)^n := by
        induction n with
        | zero => simp
        | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
      have hgeom : (∑ k ∈ Finset.range N, (1 / 2 : ℝ)^k) ≤ 2 := by
        rw [hsum]
        exact sub_le_self _ (by positivity)
      linarith [mul_le_mul_of_nonneg_right hgeom (show 0 ≤ Q / 2 by positivity)]

/-- Choose a cofinal subsequence whose consecutive triples satisfy the interpolation
estimate, then apply the estimate for consecutive stages. -/
theorem directSumDifference_seminorm_bound_of_interpolation
    [∀ k, IsTopologicalAddGroup (X k)] [dec : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)]
    (hinterp : ∀ a : ℕ,
      ∃ (m : ℕ) (ham : a ≤ m) (p : Seminorm ℂ (X a)), Continuous p ∧
        ∀ (l : ℕ) (hal : a ≤ l), m ≤ l →
          ∀ (q : Seminorm ℂ (X m)), Continuous q → ∀ ε : ℝ, 0 < ε →
            ∃ r : Seminorm ℂ (X l), Continuous r ∧
              ∀ z, q (limitStageTransition j ham z) ≤ ε * p z + r (limitStageTransition j hal z))
    (s : ∀ k, Seminorm ℂ (X k)) (hs : ∀ k, Continuous (s k)) :
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ x, directSumSeminorm s x ≤ directSumSeminorm r (directSumDifference j x) := by
  choose m hm p hp h using hinterp
  let a : ℕ → ℕ := Nat.rec 0 fun _ t ↦ m t + 1
  have hma (k : ℕ) : m (a k) ≤ a (k+1) := Nat.le_succ _
  have ha : StrictMono a := strictMono_nat_of_lt_succ fun k ↦ Nat.lt_succ_of_le (hm (a k))
  have hab (k : ℕ) : a k ≤ a (k+1) := (ha (Nat.lt_succ_self k)).le
  let J (k : ℕ) := limitStageTransition j (hab k)
  refine directSumDifference_seminorm_bound_of_cofinal ha ?_ s hs
  let : ∀ (k : ℕ) (z : X (a k)), Decidable (z ≠ 0) := fun k ↦ dec (a k)
  intro s' hs'
  refine directSumDifference_seminorm_bound_adjacent (j := J) (fun k ↦ p (a k))
    (fun k ↦ hp (a k)) ?_ s' hs'
  intro k q hq
  let T := limitStageTransition j (hma k)
  let q₀ := q.comp T.toLinearMap
  obtain ⟨r, hr, hbound⟩ := h (a k) (a (k+2)) ((hab k).trans (hab (k+1)))
    ((hma k).trans (hab (k+1))) q₀ (hq.comp T.continuous) 1 zero_lt_one
  refine ⟨r, hr, fun z ↦ ?_⟩
  have h₁ : T (limitStageTransition j (hm (a k)) z) = J k z :=
    (DFunLike.congr_fun (limitStageTransition_trans (j := j) (hm (a k)) (hma k)) z).symm
  have h₂ : limitStageTransition j ((hab k).trans (hab (k+1))) z = J (k+1) (J k z) :=
    DFunLike.congr_fun (limitStageTransition_trans (j := j) (hab k) (hab (k+1))) z
  specialize hbound z
  change q (T (limitStageTransition j (hm (a k)) z)) ≤
    1 * p (a k) z + r (limitStageTransition j ((hab k).trans (hab (k+1))) z) at hbound
  rwa [h₁, h₂, one_mul] at hbound

/-- In a Fréchet–Montel system, compact lifting from the Hausdorff limit makes the
difference map a topological embedding. This is the embedding step of Wengenroth's
Theorem 3.3. Closedness of its range follows separately from Hausdorffness of the limit. -/
private theorem IsInjectiveLCLimit.isEmbedding_directSumDifference_of_compact_stage
    (h : IsInjectiveLCLimit j i) [T2Space E]
    (hX : ∀ k, IsFrechetTVS (X k)) (hM : ∀ k, MontelSpace ℂ (X k))
    (hlift : ∀ K : Set E, IsCompact K → ∃ k, ∃ C : Set (X k), IsCompact C ∧ i k '' C = K) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    IsEmbedding (directSumDifference j) := by
  classical
  -- The compact lifting hypothesis already supplies the needed compactness.
  clear hM
  let _ : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0) := fun _ _ ↦ Classical.propDecidable _
  choose hadd hpoly hmetric _ using hX
  let : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetric
  have hinterp := h.exists_stage_seminorm_interpolation hlift
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} → Seminorm ℂ D) :=
    ⟨rfl⟩
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  have hlof (k : ℕ) : Continuous (lof k) :=
    hD.continuous_of_continuous_comp _ fun p ↦ p.property k
  let σ : D →ₗ[ℂ] D := directSumDifference j
  have hσ : Continuous σ := by
    apply hD.continuous_of_continuous_comp
    intro p
    refine hD.continuous_seminorm (i := ⟨p.val.comp σ, fun k ↦ ?_⟩)
    change Continuous (fun z : X k ↦ p.val (directSumDifference j (DirectSum.lof ℂ ℕ X k z)))
    simp_rw [directSumDifference_lof]
    exact (hD.continuous_seminorm (i := p)).comp
      ((hlof k).sub ((hlof (k+1)).comp (j k).continuous))
  have hinj : Function.Injective σ := by
    intro x y hxy
    apply DFinsupp.ext
    intro k
    induction k with
    | zero =>
      exact (directSumDifference_apply j x).1.symm.trans
        ((congrArg (fun z : D ↦ z 0) hxy).trans (directSumDifference_apply j y).1)
    | succ k ih =>
      have heq : directSumDifference j x (k+1) = directSumDifference j y (k+1) :=
        congrArg (fun z : D ↦ z (k+1)) hxy
      rwa [(directSumDifference_apply j x).2 k, (directSumDifference_apply j y).2 k, ih,
        sub_left_inj] at heq
  let e := LinearEquiv.ofInjective σ hinj
  have heInv : Continuous e.symm := by
    apply hD.continuous_of_continuous_comp
    intro p
    let s (k : ℕ) := p.val.comp (lof k)
    obtain ⟨r, hr, hbound⟩ := directSumDifference_seminorm_bound_of_interpolation
      hinterp s p.property
    let q := directSumSeminorm r
    have hq : Continuous q := by
      refine hD.continuous_seminorm (i := ⟨q, fun k ↦ ?_⟩)
      change Continuous (fun z : X k ↦ directSumSeminorm r (DirectSum.lof ℂ ℕ X k z))
      simpa only [directSumSeminorm_lof] using hr k
    have hqsub : Continuous (q.comp σ.range.subtype) := hq.comp continuous_subtype_val
    refine Seminorm.continuous_of_le hqsub fun y ↦ ?_
    let x := e.symm y
    have hx : σ x = (y : D) := congrArg Subtype.val (e.apply_symm_apply y)
    change p.val x ≤ q (y : D)
    rw [← hx]
    apply le_trans _ (hbound x)
    rw [directSumSeminorm_apply _ _ x.support Subset.rfl]
    have hsum := Finset.le_sum_of_subadditive p.val (map_zero p.val).le
      (map_add_le_add p.val) x.support (fun k ↦ lof k (x k))
    have hdecomp : (∑ k ∈ x.support, lof k (x k)) = x := DirectSum.sum_support_of x
    rwa [hdecomp] at hsum
  let homeo : D ≃ₜ σ.range := ⟨e.toEquiv, hσ.subtype_mk _, heInv⟩
  exact IsEmbedding.subtypeVal.comp homeo.isEmbedding

end MontelLimits

section QuotientStageAcyclicity

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {X Y : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)] [∀ k, AddCommGroup (Y k)] [∀ k, Module ℂ (Y k)]
  [∀ k, TopologicalSpace (Y k)]

/-- The final locally convex topology on a direct sum makes a linear map into a
polynormable space continuous whenever its restrictions to the summands are continuous. -/
private theorem continuous_directSum [PolynormableSpace ℂ E]
    (f : (⨁ k, X k) →ₗ[ℂ] E)
    (hf : ∀ k, Continuous (f ∘ DirectSum.lof ℂ ℕ X k)) :
    @Continuous (⨁ k, X k) E
      (locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)) _ f := by
  let lof := DirectSum.lof ℂ ℕ X
  let : TopologicalSpace (⨁ k, X k) := locallyConvexFinalTopology lof
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ (⨁ k, X k) // ∀ k, Continuous (p ∘ lof k)} → _) :=
    ⟨rfl⟩
  apply (PolynormableSpace.withSeminorms ℂ E).continuous_of_continuous_comp
  exact fun p ↦ hP.continuous_seminorm ⟨p.val.comp f, fun k ↦ p.property.comp (hf k)⟩

/-- A direct sum of linear quotient maps is a quotient map for the locally convex
direct-sum topologies. -/
private theorem isQuotientMap_directSum_lmap
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, IsTopologicalAddGroup (Y k)]
    (f : ∀ k, X k →ₗ[ℂ] Y k) (hf : ∀ k, IsQuotientMap (f k)) :
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
    IsQuotientMap (DirectSum.lmap f) := by
  let D := ⨁ k, X k
  let T := ⨁ k, Y k
  let lofD := DirectSum.lof ℂ ℕ X
  let lofT := DirectSum.lof ℂ ℕ Y
  let : TopologicalSpace D := locallyConvexFinalTopology lofD
  let : TopologicalSpace T := locallyConvexFinalTopology lofT
  let q : D →ₗ[ℂ] T := DirectSum.lmap f
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lofD k)} → _) := ⟨rfl⟩
  have hT : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ T // ∀ k, Continuous (p ∘ lofT k)} → _) := ⟨rfl⟩
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  let : PolynormableSpace ℂ T := hT.toPolynormableSpace
  let : PolynormableSpace ℂ (D ⧸ q.ker) := polynormableSpace_quotient q.ker
  have hsurj : Function.Surjective q := (DirectSum.lmap_surjective f).mpr fun k ↦ (hf k).surjective
  let e := q.quotKerEquivOfSurjective hsurj
  have hc : Continuous q := continuous_directSum q fun k ↦ by
    change Continuous (fun x ↦ DirectSum.lmap f (DirectSum.lof ℂ ℕ X k x))
    simp only [DirectSum.lmap_lof]
    exact (hT.continuous_of_continuous_comp (lofT k) fun p ↦ p.property k).comp (hf k).continuous
  have he : Continuous e := q.ker.isQuotientMap_mkQL.continuous_iff.mpr hc
  have he' : Continuous e.symm := by
    apply continuous_directSum e.symm.toLinearMap
    intro k
    apply (hf k).continuous_iff.mpr
    have heq (x : X k) : e.symm (lofT k (f k x)) = q.ker.mkQ (lofD k x) := by
      rw [← show q (lofD k x) = lofT k (f k x) from DirectSum.lmap_lof f k x]
      exact q.quotKerEquivOfSurjective_symm_apply hsurj _
    change Continuous (fun x ↦ e.symm (lofT k (f k x)))
    simp only [heq]
    exact q.ker.mkQL.continuous.comp (hD.continuous_of_continuous_comp (lofD k) fun p ↦ p.property k)
  exact (Homeomorph.mk e.toEquiv he he').isQuotientMap.comp q.ker.isQuotientMap_mkQL

/-- The locally convex direct sum of stage embeddings is an embedding. Each seminorm
on the source is bounded by the sum of extensions of its restrictions to the stages. -/
private theorem isEmbedding_directSum_lmap
    [∀ k, IsTopologicalAddGroup (Y k)] [∀ k, PolynormableSpace ℂ (Y k)]
    (f : ∀ k, X k →ₗ[ℂ] Y k) (hf : ∀ k, IsEmbedding (f k)) :
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
    IsEmbedding (DirectSum.lmap f) := by
  classical
  let D := ⨁ k, X k
  let T := ⨁ k, Y k
  let lofD := DirectSum.lof ℂ ℕ X
  let lofT := DirectSum.lof ℂ ℕ Y
  let tD : TopologicalSpace D := locallyConvexFinalTopology lofD
  let : TopologicalSpace T := locallyConvexFinalTopology lofT
  let a : D →ₗ[ℂ] T := DirectSum.lmap f
  let p : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lofD k)} := Subtype.val
  let q : SeminormFamily ℂ T {q : Seminorm ℂ T // ∀ k, Continuous (q ∘ lofT k)} := Subtype.val
  have hT : WithSeminorms q := ⟨rfl⟩
  have hD : @WithSeminorms ℂ D _ _ _ _ p (TopologicalSpace.induced a inferInstance) := by
    let : TopologicalSpace D := TopologicalSpace.induced a inferInstance
    apply (a.withSeminorms_induced hT).congr
    · intro s
      choose r hr hrf using fun k ↦ exists_seminorm_extension (hf k).isInducing
        (show Continuous (s.val.comp (lofD k)) from s.property k)
      let R := directSumSeminorm r
      have hR : ∀ k, Continuous (R ∘ lofT k) := fun k ↦ by
        simpa only [Function.comp_def, R, lofT, directSumSeminorm_lof] using hr k
      refine ⟨{⟨R, hR⟩}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      intro x
      change s.val x ≤ R (a x)
      have hs := Finset.le_sum_of_subadditive s.val (map_zero s.val).le
        (map_add_le_add s.val) x.support (fun k ↦ lofD k (x k))
      rw [show (∑ k ∈ x.support, lofD k (x k)) = x from DirectSum.sum_support_of x] at hs
      refine hs.trans_eq ?_
      rw [show R (a x) = ∑ k ∈ x.support, r k (a x k) from
        directSumSeminorm_apply r _ _ (DFinsupp.support_mapRange (hf := fun k ↦ map_zero (f k)))]
      exact Finset.sum_congr rfl fun k _ ↦ (DFunLike.congr_fun (hrf k) (x k)).symm
    · intro s
      have hs (k : ℕ) : Continuous ((s.val.comp a) ∘ lofD k) := by
        change Continuous (fun x ↦ s.val (DirectSum.lmap f (DirectSum.lof ℂ ℕ X k x)))
        simp only [DirectSum.lmap_lof]
        exact (s.property k).comp (hf k).continuous
      refine ⟨{⟨s.val.comp a, hs⟩}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      exact le_rfl
  refine ⟨⟨?_⟩, (DirectSum.lmap_injective f).mpr fun k ↦ (hf k).injective⟩
  let : TopologicalSpace D := TopologicalSpace.induced a inferInstance
  exact hD.topology_eq_withSeminorms.symm

/-- For a stepwise closed subspace the topology comparison is equivalent to the
quotient-stage difference map being an embedding. Agreement of the topologies also
makes the subspace closed, by completeness of its strict Fréchet limit. -/
private theorem quotientStageDifference_embedding_and_closed_of_topologies
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    (hX : ∀ k, IsFrechetTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) (F : Submodule ℂ E)
    (hF : ∀ k, IsClosed (i k ⁻¹' (F : Set E))) :
    let Q (k : ℕ) := X k ⧸ limitStageKernel i F k
    let tF : TopologicalSpace F := inferInstance
    let := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Q)
    (IsEmbedding (directSumDifference (limitQuotientTransition h F)) ↔
      tF = limitSubspaceTopology i F) ∧
      (tF = limitSubspaceTopology i F → IsClosed (F : Set E)) := by
  let K := limitStageKernel i F
  let S (k : ℕ) := F.comap (i k).toLinearMap
  let Q (k : ℕ) := X k ⧸ K k
  let tF : TopologicalSpace F := inferInstance
  let tF' := limitSubspaceTopology i F
  let : TopologicalSpace (⨁ k, X k) := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  let : TopologicalSpace (⨁ k, S k) := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ (fun k ↦ S k))
  let : TopologicalSpace (⨁ k, Q k) := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Q)
  let σ := directSumDifference j
  let τ := directSumDifference (limitQuotientTransition h F)
  change (IsEmbedding τ ↔ tF = tF') ∧ (tF = tF' → IsClosed (F : Set E))
  have hX' := hX
  choose hadd hpoly hmetr hcomplete using hX'
  let : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetr
  let : ∀ k, IsTopologicalAddGroup (S k) := fun _ ↦ inferInstance
  let : ∀ k, PolynormableSpace ℂ (S k) := fun _ ↦ inferInstance
  let : ∀ k, T2Space (X k) := fun _ ↦ inferInstance
  let : ∀ k, T2Space (S k) := fun _ ↦ inferInstance
  have hSK : S = K := by
    funext k
    ext x
    exact (Submodule.Quotient.mk_eq_zero F).symm
  have hFembed : @IsEmbedding F E tF' _ F.subtype ↔ tF = tF' := by
    refine ⟨fun H ↦ H.eq_induced.symm, fun H ↦ ?_⟩
    rw [← H]
    exact IsEmbedding.subtypeVal
  let l (k : ℕ) : S k →ₗ[ℂ] F := (i k).toLinearMap.restrict (fun _ hx ↦ hx)
  let : TopologicalSpace F := tF'
  have hPF : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ F // ∀ k, Continuous (p ∘ l k)} → _) := ⟨rfl⟩
  let : IsTopologicalAddGroup F := hPF.isTopologicalAddGroup
  let iF (k : ℕ) : S k →L[ℂ] F :=
    ⟨l k, hPF.continuous_of_continuous_comp (l k) fun p ↦ p.property k⟩
  have hcompat (k : ℕ) (x : X k) : i (k+1) (j k x) = i k x :=
    DFunLike.congr_fun (h.compatible k) x
  let jF (k : ℕ) : S k →L[ℂ] S (k+1) :=
    ((j k).comp (S k).subtypeL).codRestrict (S (k+1)) (fun x ↦ by
      change i (k+1) (j k x.val) ∈ F
      rw [hcompat]
      exact x.property)
  have hjF (k : ℕ) : IsEmbedding (jF k) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp ((hj k).comp IsEmbedding.subtypeVal)
  have hlimF : IsInjectiveLCLimit jF iF := by
    refine ⟨fun k x y hxy ↦ Subtype.ext (h.injective k (congrArg Subtype.val hxy)), ?_, ?_, rfl⟩
    · intro k
      ext x : 1
      exact Subtype.ext (hcompat k x.val)
    · intro x
      obtain ⟨k, y, hy⟩ := h.exhaustive x.val
      have hy' : y ∈ S k := by
        change i k y ∈ F
        rw [hy]
        exact x.property
      exact ⟨k, ⟨y, hy'⟩, Subtype.ext hy⟩
  constructor
  · let a := DirectSum.lmap (fun k ↦ (S k).subtype)
    let π := DirectSum.lmap (fun k ↦ (K k).mkQ)
    let p := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
    let pF := DirectSum.toModule ℂ ℕ F (fun k ↦ (iF k).toLinearMap)
    have ha := isEmbedding_directSum_lmap (fun k ↦ (S k).subtype) (fun _ ↦ IsEmbedding.subtypeVal)
    have hp := h.isQuotientMap_directSum
    have hπ := isQuotientMap_directSum_lmap (fun k ↦ (K k).mkQ)
      (fun k ↦ (K k).isOpenQuotientMap_mkQ.isQuotientMap)
    have hpF := hlimF.isQuotientMap_directSum
    have hrσ : range σ = (p.ker : Set (⨁ k, X k)) := h.range_directSumDifference
    have hra : range a = (π.ker : Set (⨁ k, X k)) := by
      change (a.range : Set (⨁ k, X k)) = _
      rw [show a.range = π.ker by
        simp only [a, π, DirectSum.range_lmap, DirectSum.ker_lmap,
          Submodule.range_subtype, Submodule.ker_mkQ, hSK]]
    have hσ : IsEmbedding σ := (isAcyclicSystem_of_strict_frechet hX j hj).isEmbedding
    have haddD : IsTopologicalAddGroup (⨁ k, X k) :=
      (show WithSeminorms (Subtype.val : {p : Seminorm ℂ (⨁ k, X k) //
        ∀ k, Continuous (p ∘ DirectSum.lof ℂ ℕ X k)} → _) from ⟨rfl⟩).isTopologicalAddGroup
    let : IsTopologicalAddGroup (⨁ k, X k) := haddD
    let : IsTopologicalAddGroup (⨁ k, Q k) :=
      (show WithSeminorms (Subtype.val : {p : Seminorm ℂ (⨁ k, Q k) //
        ∀ k, Continuous (p ∘ DirectSum.lof ℂ ℕ Q k)} → _) from ⟨rfl⟩).isTopologicalAddGroup
    have commσ : π.comp σ = τ.comp π := by
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro k
      cases k with
      | zero =>
        exact (congrArg (K 0).mkQ (directSumDifference_apply j x).1).trans
          ((directSumDifference_apply (limitQuotientTransition h F) (π x)).1.symm)
      | succ k =>
        change (K (k+1)).mkQ (σ x (k+1)) = τ (π x) (k+1)
        rw [(directSumDifference_apply j x).2 k,
          (directSumDifference_apply (limitQuotientTransition h F) (π x)).2 k, map_sub]
        rfl
    have comma : p.comp a = F.subtype.comp pF := by
      apply DirectSum.linearMap_ext
      intro k
      ext x : 1
      simp only [LinearMap.comp_apply, a, DirectSum.lmap_lof, p, pF, DirectSum.toModule_lof]
      rfl
    have hτinj : Function.Injective τ := by
      intro x y hxy
      apply DFinsupp.ext
      intro k
      have hcoord (k : ℕ) := congrArg (fun z : ⨁ k, Q k ↦ z k) hxy
      induction k with
      | zero =>
        simpa only [τ, (directSumDifference_apply _ x).1, (directSumDifference_apply _ y).1]
          using hcoord 0
      | succ k ih =>
        simpa only [τ, (directSumDifference_apply _ x).2, (directSumDifference_apply _ y).2,
          ih, sub_left_inj] using hcoord (k+1)
    have hstrict {A B : Type _} [TopologicalSpace A] [TopologicalSpace B]
        {g : A → B} (hg : IsEmbedding g) (R : Set B) (hR : range g = R) :
        ∃ u : A → R, IsQuotientMap u ∧ Subtype.val ∘ u = g := by
      let u (x : A) : R := ⟨g x, hR ▸ mem_range_self x⟩
      have hu : IsEmbedding u := IsEmbedding.subtypeVal.of_comp_iff.mp hg
      exact ⟨u, (hu.isInducing.isOpenQuotientMap_of_surjective fun y ↦ by
        have hy : y.val ∈ range g := (congrArg (fun U : Set B ↦ y.val ∈ U) hR).mpr y.property
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, Subtype.ext hx⟩).isQuotientMap, rfl⟩
    obtain ⟨s, hs, hs_eq⟩ := hstrict hσ _ hrσ
    obtain ⟨b, hb, hb_eq⟩ := hstrict ha _ hra
    have hleft : IsStrictMap (π.comp p.ker.subtype) ↔ IsStrictMap τ := by
      have hcomp : (π.comp p.ker.subtype) ∘ s = τ ∘ π := by
        calc
          _ = π ∘ (Subtype.val ∘ s) := rfl
          _ = π ∘ σ := by rw [hs_eq]
          _ = _ := DFunLike.congr_fun commσ |> fun h ↦ funext h
      exact hs.isStrictMap_iff.trans (hcomp ▸ hπ.isStrictMap_iff.symm)
    have hright : IsStrictMap (p.comp π.ker.subtype) ↔ IsStrictMap F.subtype := by
      have hcomp : (p.comp π.ker.subtype) ∘ b = F.subtype ∘ pF := by
        calc
          _ = p ∘ (Subtype.val ∘ b) := rfl
          _ = p ∘ a := by rw [hb_eq]
          _ = _ := DFunLike.congr_fun comma |> fun h ↦ funext h
      exact hb.isStrictMap_iff.trans (hcomp ▸ hpF.isStrictMap_iff.symm)
    have hmid := isStrictMap_comp_ker_subtype_iff π p
      (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hπ)
      (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hp)
    have hinc : Function.Injective (F.subtype : F → E) := Subtype.val_injective
    rw [isEmbedding_iff_isStrictMap_injective, and_iff_left hτinj, ← hFembed,
      isEmbedding_iff_isStrictMap_injective, and_iff_left hinc]
    exact hleft.symm.trans (hmid.trans hright)
  · intro htop
    let : ∀ k, UniformSpace (X k) := fun _ ↦ IsTopologicalAddGroup.rightUniformSpace _
    let : ∀ k, IsUniformAddGroup (X k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
    let : ∀ k, CompleteSpace (X k) := hcomplete
    have hc (k : ℕ) : @CompleteSpace (S k) (IsTopologicalAddGroup.rightUniformSpace (S k)) := by
      let : IsUniformAddGroup (S k) := (S k).toAddSubgroup.isUniformAddGroup
      rw [IsUniformAddGroup.rightUniformSpace_eq]
      exact completeSpace_coe_iff_isComplete.mpr (hF k).isComplete
    let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    let : CompleteSpace F := (strictLCLimit_complete_nonmetrizable hc hlimF hjF).1
    let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    have he : IsUniformInducing F.subtype :=
      AddMonoidHom.isUniformInducing_of_isInducing (hFembed.mpr htop).isInducing
    have hcF := he.isComplete_range.isClosed
    change IsClosed (range (Subtype.val : F → E)) at hcF
    rwa [Subtype.range_coe] at hcF

/-- In a strict Fréchet system, the limit topology on a stepwise closed subspace agrees
with its inherited topology exactly when the quotient system is acyclic.
This is the exact-sequence criterion for limit subspaces used in Wengenroth's Corollary 3.4.
Apply the direct-sum difference maps to the short exact sequence of the stage subspaces,
original stages, and quotient stages. The first two systems are strict, hence acyclic. -/
private theorem isAcyclicSystem_quotientStages_iff
    [ContinuousSMul ℂ E] [T2Space E] (hX : ∀ k, IsFrechetTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) (F : Submodule ℂ E)
    (hF : ∀ k, IsClosed (i k ⁻¹' (F : Set E))) :
    IsAcyclicSystem (limitQuotientTransition h F) ↔
      (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F := by
  have hPE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → _) := ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hPE.isTopologicalAddGroup
  let K := limitStageKernel i F
  let Q (k : ℕ) := X k ⧸ K k
  let : TopologicalSpace (⨁ k, Q k) := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Q)
  have hK (k : ℕ) : IsClosed (K k : Set (X k)) := by
    convert hF k using 1
    ext x
    exact Submodule.Quotient.mk_eq_zero F
  have hQ (k : ℕ) := isFrechetTVS_quotient (hX k) (K k) (hK k)
  let : ∀ k, IsTopologicalAddGroup (Q k) := fun k ↦ (hQ k).choose
  let : ∀ k, PolynormableSpace ℂ (Q k) := fun k ↦ (hQ k).choose_spec.1
  have hlim := isInjectiveLCLimit_quotientStages h F
  obtain ⟨hembed, hclosed⟩ := quotientStageDifference_embedding_and_closed_of_topologies hX h hj F hF
  change IsClosedEmbedding (directSumDifference (limitQuotientTransition h F)) ↔ _
  refine ⟨fun H ↦ hembed.mp H.isEmbedding, fun H ↦ ⟨hembed.mpr H, ?_⟩⟩
  let : IsClosed (F : Set E) := hclosed H
  exact hlim.closedRange_directSumDifference_iff.mpr inferInstance

end QuotientStageAcyclicity

/-- A countable injective system of Fréchet–Montel spaces is acyclic exactly when each
bounded set of its limit is the image of a bounded set of one stage. This is the
regularity criterion in Wengenroth's Theorem 3.3. In the non-Hausdorff case the
bounded-stage condition fails, since the closure of zero is a bounded subspace and a
Hausdorff locally convex stage has no nonzero bounded subspace. -/
private theorem isAcyclicSystem_iff_bounded_stage_of_montel
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {X : ℕ → Type*}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)] [∀ k, TopologicalSpace (X k)]
    (hX : ∀ k, IsFrechetTVS (X k)) (hM : ∀ k, MontelSpace ℂ (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i) :
    IsAcyclicSystem j ↔
      ∀ B : Set E, IsVonNBounded ℂ B →
        ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ i k '' A = B := by
  have hX' := hX
  choose hadd hpoly hmetric _ using hX'
  let : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetric
  let : ∀ k, T2Space (X k) := fun _ ↦ inferInstance
  let : ∀ k, ContinuousSMul ℂ (X k) := fun k ↦ PolynormableSpace.continuousSMul ℂ (X k)
  have hE : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ E) :=
    ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hE.isTopologicalAddGroup
  let : ContinuousSMul ℂ E := hE.continuousSMul
  let : TopologicalSpace (⨁ k, X k) := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  constructor
  · intro hacyclic
    have hclosed : IsClosedEmbedding (directSumDifference j) := hacyclic
    let : T2Space E := h.closedRange_directSumDifference_iff.mp hclosed.isClosed_range
    exact bounded_stage_of_nullSequence h (h.lifts_nullSequence_of_acyclic hX hM hacyclic)
  · intro hlift
    let : T2Space E := h.t2Space_of_bounded_stage hlift
    refine ⟨h.isEmbedding_directSumDifference_of_compact_stage hX hM ?_,
      h.closedRange_directSumDifference_iff.mpr inferInstance⟩
    intro K hK
    obtain ⟨k, A, hA, heq⟩ := hlift K (hK.isVonNBounded ℂ)
    refine ⟨k, closure A, (hM k).heine_borel _ isClosed_closure hA.closure, ?_⟩
    apply subset_antisymm
    · calc
        i k '' closure A ⊆ closure (i k '' A) :=
          image_closure_subset_closure_image (i k).continuous
        _ = K := by rw [heq, hK.isClosed.closure_eq]
    · rw [← heq]
      exact image_mono subset_closure

/-- Paper: §C.1.5.1 (after Definition C.1.5.9), p. 667. A closed quotient of a Schwartz
Fréchet space lifts bounded sets. Grothendieck's result gives a compact lift, by lifting
the compact closure of the bounded set in the quotient. -/
theorem liftsBoundedSets_mkQL_of_schwartz_frechet
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (hS : IsSchwartzTVS E) (F : Submodule ℂ E)
    (hF : IsClosed (F : Set E)) : LiftsBoundedSets F.mkQL := by
  let hQ := isFrechetTVS_quotient hE F hF
  obtain ⟨hadd, _, hmetr, hcomplete⟩ := hE
  let : IsTopologicalAddGroup E := hadd
  let : MetrizableSpace E := hmetr
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  let : (uniformity E).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  let := UniformSpace.pseudoMetricSpace E
  obtain ⟨haddQ, _, _, hcompleteQ⟩ := hQ
  let : IsTopologicalAddGroup (E ⧸ F) := haddQ
  let : UniformSpace (E ⧸ F) := IsTopologicalAddGroup.rightUniformSpace (E ⧸ F)
  let : IsUniformAddGroup (E ⧸ F) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (E ⧸ F) := hcompleteQ
  intro B hB
  obtain ⟨A, hA, hqA⟩ := exists_isCompact_image_eq_of_isOpenQuotientMap
    F.isOpenQuotientMap_mkQL (isCompact_closure_of_schwartz (isSchwartzTVS_quotient hS F) hB)
  exact ⟨A, hA.isVonNBounded ℂ, hqA.symm ▸ subset_closure⟩

/-- Paper: Theorem C.1.5.11, p. 668. In a strict countable limit of Schwartz Fréchet
spaces, a stepwise closed subspace inherits the limit topology exactly when the quotient
map lifts bounded sets.
Deviation: This is the general form stated immediately after (1)–(2) on the same page.
For a closed subspace, equality of these topologies is the limit subspace condition.
The specialization to nuclear stages uses Example C.1.5.10. -/
theorem limitSubspaceTopology_eq_iff_liftsBoundedSets
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] {X : ℕ → Type*}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)] [∀ k, TopologicalSpace (X k)]
    (hX : ∀ k, IsFrechetTVS (X k)) (hS : ∀ k, IsSchwartzTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    (hj : ∀ k, IsEmbedding (j k)) (F : Submodule ℂ E) (hF : ∀ k, IsClosed (i k ⁻¹' (F : Set E))) :
    (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F ↔
      LiftsBoundedSets F.mkQL := by
  let K := limitStageKernel i F
  have hK (k : ℕ) : IsClosed (K k : Set (X k)) := by
    convert hF k using 1
    ext x
    exact Submodule.Quotient.mk_eq_zero F
  have hX' := hX
  choose hadd hpoly hmetr hcomplete using hX'
  let : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetr
  let : ∀ k, UniformSpace (X k) := fun _ ↦ IsTopologicalAddGroup.rightUniformSpace _
  let : ∀ k, IsUniformAddGroup (X k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ k, CompleteSpace (X k) := hcomplete
  have hjClosed (k : ℕ) : IsClosedEmbedding (j k) :=
    (AddMonoidHom.isUniformEmbedding_of_isEmbedding (hj k)).isClosedEmbedding
  have hFrechetQ (k : ℕ) := isFrechetTVS_quotient (hX k) (K k) (hK k)
  have hregular := isAcyclicSystem_iff_bounded_stage_of_montel hFrechetQ
    (fun k ↦ montelSpace_of_schwartz_frechet (hFrechetQ k) (isSchwartzTVS_quotient (hS k) (K k)))
    (isInjectiveLCLimit_quotientStages h F)
  rw [← isAcyclicSystem_quotientStages_iff hX h hj F hF, hregular]
  constructor
  · intro hB B hbounded
    obtain ⟨k, C, hC, rfl⟩ := hB B hbounded
    obtain ⟨A, hA, hcover⟩ := liftsBoundedSets_mkQL_of_schwartz_frechet
      (hX k) (hS k) (K k) (hK k) C hC
    refine ⟨i k '' A, hA.image (i k), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hcover hz
    exact ⟨i k a, mem_image_of_mem (i k) ha, rfl⟩
  · intro hlift B hB
    obtain ⟨A, hA, rfl⟩ := (hasBoundedLift_iff_image F.mkQL B).mp (hlift B hB)
    obtain ⟨k, C, hC, rfl⟩ := (isVonNBounded_iff_bounded_stage h hjClosed A).mp hA
    refine ⟨k, (K k).mkQL '' C, hC.image (K k).mkQL, ?_⟩
    rw [image_image, image_image]
    rfl

-- TODO(paper-gap): The sentence after C.1.5.11 reverses the implication of Example C.1.5.10.
-- TODO(paper-gap): Remark C.1.5.12 and Corollary C.1.5.13 require nuclearity from §C.2.4.

section Duality

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
  [∀ k, ContinuousSMul ℂ (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
variable {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E}

/-- Paper: Lemma C.1.6.1, p. 669. Restriction identifies the weak dual of a Hausdorff
inductive limit with the projective limit of the stage weak duals. The same holds for
strong duals if every bounded set comes from a bounded set in one stage.
Deviation: The projective limit is expressed as the compatible families in the product.
Unique extension identifies the image and the embeddings give its subspace topology. -/
theorem dual_of_injectiveLCLimit (h : IsInjectiveLCLimit j i) :
    (∀ l : (k : ℕ) → StrongDual ℂ (X k), (∀ k, (l (k+1)).comp (j k) = l k) →
      ∃! L : StrongDual ℂ E, ∀ k, L.comp (i k) = l k) ∧
    IsEmbedding (fun (L : WeakDual ℂ E) k ↦ StrongDual.toWeakDual (L.toStrongDual.comp (i k))) ∧
    ((∀ B : Set E, IsVonNBounded ℂ B →
      ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ B = i k '' A) →
      IsEmbedding (fun (L : StrongDual ℂ E) k ↦ L.comp (i k))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    -- The union of the stage graphs is the graph of a linear functional on E.
    let graph (k : ℕ) := LinearMap.range ((i k).toLinearMap.prod (l k).toLinearMap)
    have hm : Monotone graph := monotone_nat_of_le_succ fun k _ ⟨a, ha⟩ ↦ by
      refine ⟨j k a, ?_⟩
      exact (Prod.ext (DFunLike.congr_fun (h.compatible k) a) (DFunLike.congr_fun (hl k) a)).trans ha
    let G := ⨆ k, graph k
    let proj : G →ₗ[ℂ] E := (LinearMap.fst ℂ E ℂ).comp G.subtype
    have hmem (k : ℕ) (x : X k) : (i k x, l k x) ∈ G := le_iSup graph k ⟨x, rfl⟩
    have hinj : Function.Injective proj := by
      apply (injective_iff_map_eq_zero _).mpr
      rintro ⟨p, hp⟩ hp0
      obtain ⟨k, a, ha⟩ := (Submodule.mem_iSup_of_directed graph hm.directed_le).mp hp
      have ha0 : a = 0 := h.injective k ((congrArg Prod.fst ha).trans (hp0.trans (map_zero _).symm))
      subst a
      exact Subtype.ext (ha.symm.trans (map_zero _))
    have hsurj : Function.Surjective proj := by
      intro x
      obtain ⟨k, y, rfl⟩ := h.exhaustive x
      exact ⟨⟨_, hmem k y⟩, rfl⟩
    let e := LinearEquiv.ofBijective proj ⟨hinj, hsurj⟩
    let L := ((LinearMap.snd ℂ E ℂ).comp G.subtype).comp e.symm.toLinearMap
    have hLi (k : ℕ) (x : X k) : L (i k x) = l k x := by
      have he : e.symm (i k x) = ⟨_, hmem k x⟩ := e.symm_apply_eq.mpr rfl
      change (e.symm (i k x)).val.2 = _
      rw [he]
    -- Its norm is one of the seminorms defining the final locally convex topology.
    let p := (normSeminorm ℂ ℂ).comp L
    have hp (k : ℕ) : Continuous (p ∘ (i k).toLinearMap) := by
      simpa only [p, Function.comp_def, Seminorm.comp_apply, coe_normSeminorm,
        ContinuousLinearMap.coe_coe, hLi] using (l k).continuous.norm
    let P : SeminormFamily ℂ E {s : Seminorm ℂ E // ∀ k, Continuous (s ∘ (i k).toLinearMap)} :=
      Subtype.val
    have hP : WithSeminorms P := ⟨h.topology_eq⟩
    have hL : Continuous L := by
      apply continuous_of_continuousAt_zero L
      have hn := (hP.continuous_seminorm ⟨p, hp⟩).continuousAt (x := 0)
      rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
      change Tendsto (fun x ↦ ‖L x‖) (𝓝 0) (𝓝 ‖L 0‖) at hn
      simpa only [map_zero, norm_zero] using hn
    refine ⟨⟨L, hL⟩, fun k ↦ ContinuousLinearMap.ext (hLi k), ?_⟩
    intro L' hL'
    ext x
    obtain ⟨k, y, rfl⟩ := h.exhaustive x
    exact (DFunLike.congr_fun (hL' k) y).trans (hLi k y).symm
  · -- Every evaluation on E comes from an evaluation on one stage.
    choose k x hx using h.exhaustive
    let eval (l : (k : ℕ) → WeakDual ℂ (X k)) (a : E) := l (k a) (x a)
    have heval : Continuous eval := continuous_pi fun a ↦
      (WeakDual.eval_continuous (x a)).comp (continuous_apply (k a))
    let res (L : WeakDual ℂ E) (n : ℕ) := StrongDual.toWeakDual (L.toStrongDual.comp (i n))
    have hc : Continuous res := continuous_pi fun n ↦
      WeakDual.continuous_of_continuous_eval fun y ↦ WeakDual.eval_continuous (𝕜 := ℂ) (i n y)
    refine IsEmbedding.of_comp hc heval ?_
    have heq : eval ∘ res = fun L a ↦ L a := by
      funext L a
      exact congrArg L (hx a)
    rw [heq]
    exact WeakBilin.isEmbedding ContinuousLinearMap.coe_injective
  · intro hb
    let res : StrongDual ℂ E →L[ℂ] ((k : ℕ) → StrongDual ℂ (X k)) :=
      ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.precomp ℂ (i k)
    change IsEmbedding res
    constructor
    · apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
      refine le_antisymm (map_le_iff_le_comap.mp ?_) ?_
      · simpa only [Tendsto, map_zero] using res.continuous.tendsto 0
      · apply ContinuousLinearMap.hasBasis_nhds_zero.ge_iff.mpr
        rintro ⟨B, V⟩ ⟨hB, hV⟩
        obtain ⟨k, A, hA, rfl⟩ := hb B hB
        have hA' : ∀ᶠ L : StrongDual ℂ (X k) in 𝓝 0, MapsTo L A V :=
          ContinuousLinearMap.eventually_nhds_zero_mapsTo hA hV
        have hpr := (continuous_apply k : Continuous
          (fun l : (k : ℕ) → StrongDual ℂ (X k) ↦ l k)).tendsto 0
        refine Filter.mem_comap.mpr ⟨{l | MapsTo (l k) A V}, hpr hA', ?_⟩
        rintro L hL _ ⟨x, hx, rfl⟩
        exact hL hx
    · intro L M he
      ext a
      obtain ⟨k, x, rfl⟩ := h.exhaustive a
      exact DFunLike.congr_fun (congrFun he k) x

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
  [∀ k, IsTopologicalAddGroup (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)] in
/-- Paper: Remark C.1.6.2, p. 670. If restriction is an embedding, the polar of
a bounded set contains the pullback of the polar of a bounded set at a single stage. -/
private theorem IsInjectiveLCLimit.exists_stage_polar (h : IsInjectiveLCLimit j i)
    (he : IsEmbedding (fun (L : StrongDual ℂ E) k ↦ L.comp (i k)))
    (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ ∀ L : StrongDual ℂ E,
      (∀ a ∈ A, ‖L (i k a)‖ ≤ 1) → ∀ b ∈ B, ‖L b‖ ≤ 1 := by
  let R (k : ℕ) : StrongDual ℂ E →L[ℂ] StrongDual ℂ (X k) := ContinuousLinearMap.precomp ℂ (i k)
  -- Compatibility makes the filters pulled back from the individual stages decreasing.
  let N (k : ℕ) := comap (R k) (𝓝 0)
  have hN : Antitone N := antitone_nat_of_succ_le fun k ↦ by
    let J : StrongDual ℂ (X (k+1)) →L[ℂ] StrongDual ℂ (X k) := ContinuousLinearMap.precomp ℂ (j k)
    have hcomp : ⇑(R k) = J ∘ R (k+1) := by
      funext L
      ext a
      exact (congrArg L (DFunLike.congr_fun (h.compatible k) a)).symm
    change comap (R (k+1)) (𝓝 0) ≤ comap (R k) (𝓝 0)
    rw [hcomp, ← comap_comap]
    apply comap_mono
    apply map_le_iff_le_comap.mp
    simpa only [Tendsto, map_zero] using J.continuous.tendsto 0
  let S := {L : StrongDual ℂ E | ∀ b ∈ B, ‖L b‖ ≤ 1}
  have hS : S ∈ 𝓝 0 := by
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hB
      (Metric.closedBall_mem_nhds (0 : ℂ) (zero_lt_one : (0 : ℝ) < 1))] with L hL
    intro b hb
    simpa only [Metric.mem_closedBall, dist_zero_right] using hL hb
  have heq : 𝓝 (0 : StrongDual ℂ E) = ⨅ k, N k := by
    rw [he.isInducing.nhds_eq_comap, nhds_pi, Filter.pi, comap_iInf]
    simp only [comap_comap]
    rfl
  obtain ⟨k, U, hU, hUS⟩ := (mem_iInf_of_directed hN.directed_ge S).mp (heq ▸ hS)
  obtain ⟨⟨A, ε⟩, ⟨hA, hε⟩, hAU⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall).mem_iff.mp hU
  -- Rescale the stage test set so its polar uses the unit disc.
  let c : ℂ := (ε : ℂ)⁻¹
  let d : X k →L[ℂ] X k := c • ContinuousLinearMap.id ℂ (X k)
  refine ⟨k, d '' A, hA.image d, fun L hL ↦ hUS (hAU ?_)⟩
  intro a ha
  have hv := hL (d a) ⟨a, ha, rfl⟩
  change ‖L ((i k) (c • a))‖ ≤ 1 at hv
  simp only [map_smul, norm_smul, c, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hε, ← div_eq_inv_mul] at hv
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right]
  change ‖L (i k a)‖ ≤ ε
  simpa only [one_mul] using (div_le_iff₀ hε).mp hv

/-- Paper: Remark C.1.6.2, p. 670. The strong dual has the projective limit topology
exactly when every bounded set is in the closure, in the limit, of the image of a
bounded set in one stage. -/
theorem strongDual_isEmbedding_iff_closure_bounded_stage (h : IsInjectiveLCLimit j i) :
    IsEmbedding (fun (L : StrongDual ℂ E) k ↦ L.comp (i k)) ↔
      ∀ B : Set E, IsVonNBounded ℂ B →
        ∃ k, ∃ A : Set (X k), IsVonNBounded ℂ A ∧ B ⊆ closure (i k '' A) := by
  constructor
  · intro he B hB
    obtain ⟨k, A, hA, htest⟩ := h.exists_stage_polar he B hB
    let : Module ℝ E := Module.restrictScalars ℝ ℂ _
    let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ _
    let : Module ℝ (X k) := Module.restrictScalars ℝ ℂ _
    let : IsScalarTower ℝ ℂ (X k) := IsScalarTower.restrictScalars ℝ ℂ _
    let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
    let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
    let Z := {p : Seminorm ℂ (X k) // Continuous p}
    have hP := PolynormableSpace.withSeminorms ℂ (X k)
    choose r hr hbound using hP.isVonNBounded_iff_seminorm_bounded.mp hA
    -- Enlarge A to a bounded, balanced, convex set by intersecting seminorm balls.
    let C := ⋂ p : Z, p.val.ball 0 (r p)
    have hAC : A ⊆ C := fun a ha ↦ mem_iInter.mpr fun p ↦
      (Seminorm.mem_ball_zero _).mpr (hbound p a ha)
    have hC0 : (0 : X k) ∈ C := mem_iInter.mpr fun p ↦ by
      simpa only [Seminorm.mem_ball_zero, map_zero] using hr p
    have hC : IsVonNBounded ℂ C := hP.isVonNBounded_iff_seminorm_bounded.mpr fun p ↦
      ⟨r p, hr p, fun a ha ↦ (Seminorm.mem_ball_zero _).mp (mem_iInter.mp ha p)⟩
    have hbal : Balanced ℂ C := balanced_iInter fun p ↦ p.val.balanced_ball_zero _
    have hconv : Convex ℝ C := convex_iInter fun p ↦ (p.val.restrictScalars ℝ).convex_ball _ _
    let D := closure (i k '' C)
    have hD0 : (0 : E) ∈ D := subset_closure ⟨0, hC0, map_zero _⟩
    have hD : Balanced ℂ D := (hbal.image (i k).toLinearMap).closure
    have hDc : Convex ℝ D := (hconv.linear_image ((i k).restrictScalars ℝ).toLinearMap).closure
    refine ⟨k, C, hC, fun b hb ↦ ?_⟩
    by_contra hn
    obtain ⟨L, s, hLs, hsb⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hDc isClosed_closure hn
    -- Balance turns the separating bound on the real part into a bound on the norm.
    have hnorm (z : E) (hz : z ∈ D) : ‖L z‖ < s := by
      obtain ⟨c, hc, heq⟩ := RCLike.exists_norm_eq_mul_self (L z)
      have hz' := hLs (c • z) (balanced_iff_smul_mem.mp hD hc.le hz)
      rw [map_smul, smul_eq_mul, ← heq, RCLike.ofReal_re] at hz'
      exact hz'
    have hs : 0 < s := (norm_nonneg _).trans_lt (hnorm 0 hD0)
    let M := (s : ℂ)⁻¹ • L
    have hM (z : E) : ‖M z‖ = ‖L z‖ / s := by
      simp only [M, smul_apply, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs, div_eq_inv_mul]
    have hb' := htest M (fun a ha ↦ by
      rw [hM, div_le_iff₀ hs, one_mul]
      exact (hnorm _ (subset_closure ⟨a, hAC ha, rfl⟩)).le) b hb
    rw [hM, div_le_iff₀ hs, one_mul] at hb'
    exact (hsb.trans_le (Complex.re_le_norm _)).not_ge hb'
  · intro hb
    let res : StrongDual ℂ E →L[ℂ] ((k : ℕ) → StrongDual ℂ (X k)) :=
      ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.precomp ℂ (i k)
    change IsEmbedding res
    constructor
    · apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
      refine le_antisymm (map_le_iff_le_comap.mp ?_) ?_
      · simpa only [Tendsto, map_zero] using res.continuous.tendsto 0
      · apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall).ge_iff.mpr
        rintro ⟨B, ε⟩ ⟨hB, hε⟩
        obtain ⟨k, A, hA, hsub⟩ := hb B hB
        let V := Metric.closedBall (0 : ℂ) ε
        have hA' : ∀ᶠ L : StrongDual ℂ (X k) in 𝓝 0, MapsTo L A V :=
          ContinuousLinearMap.eventually_nhds_zero_mapsTo hA (Metric.closedBall_mem_nhds _ hε)
        have hpr := (continuous_apply k : Continuous
          (fun l : (k : ℕ) → StrongDual ℂ (X k) ↦ l k)).tendsto 0
        refine Filter.mem_comap.mpr ⟨{l | MapsTo (l k) A V}, hpr hA', ?_⟩
        rintro L hL b hb'
        apply closure_minimal (t := L ⁻¹' V) ?_ (Metric.isClosed_closedBall.preimage L.continuous) (hsub hb')
        rintro _ ⟨a, ha, rfl⟩
        exact hL ha
    · intro L M he
      ext a
      obtain ⟨k, x, rfl⟩ := h.exhaustive a
      exact DFunLike.congr_fun (congrFun he k) x

end Duality

end RiemannMasullo
