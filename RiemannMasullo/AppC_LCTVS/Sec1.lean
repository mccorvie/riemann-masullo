module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Algebra.Module.ULift
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
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.Quotient
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.WeakDual
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping

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
private theorem IsInjectiveLCLimit.isEmbedding_stage
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

/-- Paper: Example C.1.4.6(4), p. 663. A Hausdorff quotient of a strict LF-space can
fail to be strict. -/
theorem exists_quotient_not_strictLF :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E),
      IsStrictLFSpace E ∧ ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧
        ¬ IsStrictLFSpace (E ⧸ M) := by sorry

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

/-- Paper: Theorem C.1.5.5, p. 665. A continuous linear surjection onto an LF-space
is open if its Hausdorff source is exhausted by rising continuous linear images of
Fréchet spaces. -/
theorem isOpenMap_of_surjective_toLF (hE : IsLFSpace E)
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hX : ∀ k, IsFrechetTVS (X k)) (u : ∀ k, X k →L[ℂ] F)
    (hr : ∀ k, range (u k) ⊆ range (u (k+1))) (hcov : ∀ x : F, ∃ k, x ∈ range (u k))
    (q : F →L[ℂ] E) (hq : Function.Surjective q) : IsOpenMap q := by sorry

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

/-- Paper: Example C.1.5.7, p. 666. Some countable locally convex direct sum of Banach
spaces has a closed linear subspace which, in its subspace topology, is not an LF-space. -/
theorem exists_closed_subspace_not_LF :
    ∃ (Y : ℕ → Type) (_ : ∀ k, NormedAddCommGroup (Y k)) (_ : ∀ k, NormedSpace ℂ (Y k))
      (_ : ∀ k, CompleteSpace (Y k)),
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
      ∃ F : Submodule ℂ (⨁ k, Y k), IsClosed (F : Set (⨁ k, Y k)) ∧ ¬ IsLFSpace F := by sorry

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
      LiftsBoundedSets F.mkQL := by sorry

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
