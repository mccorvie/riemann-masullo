module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import RiemannMasullo.AppC_LCTVS.Sec2b
public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Instances.ZMod
import all RiemannMasullo.AppC_LCTVS.Sec1
import RiemannMasullo.ForMathlib.Algebra.Module.ZLattice.Quotient
import RiemannMasullo.ForMathlib.Topology.Algebra.ContinuousMonoidHom
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Divisible
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.LocalHom
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.LocalSubgroup
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.CircleLocalHom
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Compact
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.WellQuasiOrder
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Structure of locally compact abelian groups and their Schwartz–Bruhat spaces

Masullo, §§D.1.4–D.1.5, pp. 757–765.
-/

@[expose] public noncomputable section

open Bornology Filter MeasureTheory Set Topology TopologicalSpace
open scoped Cardinal ContDiff DirectSum Topology

namespace RiemannMasullo

section TorusHom

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- A neighborhood containing no nontrivial cyclic subgroup gives finitely many characters
whose joint kernel is discrete. -/
theorem exists_torusHom_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) :
    ∃ (t : Finset (PontryaginDual G)) (f : G →ₜ* (t → Circle)),
      (∀ x (χ : t), f x χ = χ.val x) ∧ DiscreteTopology f.toMonoidHom.ker := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pontryaginDual_pairing_separates (G := G)).1
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine ⟨t, f, fun _ _ ↦ rfl, discreteTopology_of_isOpen_singleton_one ?_⟩
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

omit [T2Space G] in
open scoped Pointwise in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel has a
continuous local section over a ball in a linear subspace of the logarithm space. The
section is a local homomorphism, and the images of small balls are identity neighborhoods. -/
theorem exists_localSection_of_discrete_torusKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    ∃ (L : Submodule ℝ (EuclideanSpace ℝ ι)) (ρ : ℝ) (σ : L → G), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ v : L, ‖v‖ < ρ → ∀ i, f (σ v) i = Circle.exp ((v : EuclideanSpace ℝ ι) i)) ∧
      ContinuousOn σ (Metric.ball 0 ρ) ∧
      (∀ v w : L, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → σ (v + w) = σ v * σ w) ∧
      (∀ ε > 0, σ '' Metric.ball 0 ε ∈ 𝓝 1) := by
  classical
  let ex : EuclideanSpace ℝ ι → (ι → Circle) := fun v i ↦ Circle.exp (v i)
  have hex : Continuous ex := continuous_pi fun i ↦ Circle.exp.continuous.comp (by fun_prop)
  have hex0 : ex 0 = 1 := funext fun i ↦ by simp [ex]
  have hexadd : ∀ v w, ex (v + w) = ex v * ex w := fun v w ↦ funext fun i ↦ by
    simp [ex, Circle.exp_add]
  have hexneg : ∀ v, ex (-v) = (ex v)⁻¹ := fun v ↦ funext fun i ↦ by simp [ex]
  -- A neighborhood meeting the kernel only at the identity.
  obtain ⟨O, hO, h1O, hOker⟩ : ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ x ∈ O, f x = 1 → x = 1 := by
    have hopen1 : IsOpen ({1} : Set f.toMonoidHom.ker) := isOpen_discrete _
    obtain ⟨U0, hU0o, hpre⟩ := isOpen_induced_iff.mp hopen1
    refine ⟨U0, hU0o, ?_, ?_⟩
    · have : (1 : f.toMonoidHom.ker) ∈ Subtype.val ⁻¹' U0 := by rw [hpre]; rfl
      simpa using this
    · intro x hx hfx
      have hmem : (⟨x, MonoidHom.mem_ker.mpr hfx⟩ : f.toMonoidHom.ker) ∈
          Subtype.val ⁻¹' U0 := hx
      rw [hpre] at hmem
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  obtain ⟨W, hW, h1W, hWW⟩ := exists_open_nhds_one_mul_subset (hO.mem_nhds h1O)
  have hWW' : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    inter_mem (hW.mem_nhds h1W) (inv_mem_nhds_one G (hW.mem_nhds h1W))
  obtain ⟨V, hV, hVW, hVc⟩ := local_compact_nhds hWW'
  have hinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y := by
    intro x hx y hy hxy
    have hy' : y⁻¹ ∈ W := (hVW hy).2
    have hm : x * y⁻¹ ∈ O := hWW (Set.mul_mem_mul (hVW hx).1 hy')
    have : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hOker _ hm this)
  obtain ⟨C, hC, -, hCinv, hCC⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  have h1C : (1 : G) ∈ C := mem_of_mem_nhds hC
  have hCV : C ⊆ V := fun x hx ↦ by simpa using hCC (Set.mul_mem_mul hx h1C)
  -- Small logarithms of values on `V` come from `C`.
  have hD : IsCompact (f '' (V \ interior C)) :=
    (hVc.diff isOpen_interior).image f.continuous
  have h1D : (1 : ι → Circle) ∉ f '' (V \ interior C) := by
    rintro ⟨x, ⟨hxV, hxC⟩, hfx⟩
    have : x = 1 := hinj x hxV 1 (mem_of_mem_nhds hV) (by rw [hfx, map_one])
    exact hxC (this ▸ mem_interior_iff_mem_nhds.mpr hC)
  obtain ⟨ε, hε, hεD⟩ : ∃ ε > 0, ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε →
      ex v ∉ f '' (V \ interior C) := by
    have hnhds : (f '' (V \ interior C))ᶜ ∈ 𝓝 (ex 0) := by
      rw [hex0]; exact hD.isClosed.isOpen_compl.mem_nhds h1D
    obtain ⟨ε, hε, H⟩ := Metric.mem_nhds_iff.mp (hex.continuousAt hnhds)
    exact ⟨ε, hε, fun v hv ↦ H (by simpa using hv)⟩
  have hlift : ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε → ∀ x ∈ V, f x = ex v → x ∈ C := by
    intro v hv x hx hfx
    by_contra hxC
    exact hεD v hv ⟨x, ⟨hx, fun h ↦ hxC (interior_subset h)⟩, hfx⟩
  -- The logarithms of the image form a closed local subgroup.
  set R := min (ε / 2) 1 with hRdef
  have hR : 0 < R := lt_min (half_pos hε) one_pos
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hR1 : R ≤ 1 := min_le_right _ _
  let A : Set (EuclideanSpace ℝ ι) := {v | ‖v‖ ≤ R ∧ ex v ∈ f '' V}
  have hAc : IsClosed A :=
    (isClosed_le continuous_norm continuous_const).inter
      ((hVc.image f.continuous).isClosed.preimage hex)
  have hA0 : (0 : EuclideanSpace ℝ ι) ∈ A :=
    ⟨by simp [hR.le], ⟨1, mem_of_mem_nhds hV, by rw [map_one, hex0]⟩⟩
  have hAmemC : ∀ v ∈ A, ∃ x ∈ C, f x = ex v := by
    rintro v ⟨hv, x, hx, hfx⟩
    exact ⟨x, hlift v (hv.trans_lt hRε) x hx hfx, hfx⟩
  have hAsym : ∀ v ∈ A, -v ∈ A := by
    intro v hvA
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hvA
    have hxC' : x⁻¹ ∈ C := by rw [← hCinv]; simpa using hxC
    exact ⟨by simpa using hvA.1, x⁻¹, hCV hxC', by rw [map_inv, hfx, hexneg]⟩
  have hAadd : ∀ v ∈ A, ∀ w ∈ A, ‖v + w‖ ≤ R → v + w ∈ A := by
    intro v hv w hw hvw
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hv
    obtain ⟨y, hyC, hfy⟩ := hAmemC w hw
    exact ⟨hvw, x * y, hCC (Set.mul_mem_mul hxC hyC), by rw [map_mul, hfx, hfy, hexadd]⟩
  obtain ⟨L, ε₁, hε₁, hε₁R, hAL⟩ :=
    exists_subspace_ball_eq_of_localSubgroup hR hAc hA0 hAsym hAadd
  have hLA : ∀ v : EuclideanSpace ℝ ι, v ∈ L → ‖v‖ ≤ ε₁ → v ∈ A := by
    intro v hvL hv
    have : v ∈ (L : Set (EuclideanSpace ℝ ι)) ∩ Metric.closedBall 0 ε₁ :=
      ⟨hvL, by simpa using hv⟩
    rw [← hAL] at this
    exact this.1
  have hAL' : ∀ v ∈ A, ‖v‖ ≤ ε₁ → v ∈ L := by
    intro v hvA hv
    have : v ∈ A ∩ Metric.closedBall 0 ε₁ := ⟨hvA, by simpa using hv⟩
    rw [hAL] at this
    exact this.1
  let σ : L → G := fun v ↦ Function.invFunOn f C (ex v)
  have hσ : ∀ v : L, ‖v‖ < ε₁ → σ v ∈ C ∧ f (σ v) = ex v := by
    intro v hv
    exact Function.invFunOn_pos (hAmemC _ (hLA _ v.2 hv.le))
  refine ⟨L, ε₁, σ, hε₁, hε₁R.trans hR1, ?_, ?_, ?_, ?_⟩
  · intro v hv i
    exact congrFun (hσ v hv).2 i
  · rw [continuousOn_iff_continuous_domRestrict]
    let gV : V → (ι → Circle) := fun x ↦ f x
    have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    have hgV : IsClosedEmbedding gV :=
      (f.continuous.comp continuous_subtype_val).isClosedEmbedding
        (fun x y hxy ↦ Subtype.ext (hinj x x.2 y y.2 hxy))
    let σ' : Metric.ball (0 : L) ε₁ → V := fun v ↦
      ⟨σ v, hCV (hσ v (mem_ball_zero_iff.mp v.2)).1⟩
    have hσ' : Continuous σ' := by
      rw [hgV.isInducing.continuous_iff]
      have e : gV ∘ σ' = fun v : Metric.ball (0 : L) ε₁ ↦ ex ((v : L) : EuclideanSpace ℝ ι) :=
        funext fun v ↦ (hσ v (mem_ball_zero_iff.mp v.2)).2
      rw [e]
      exact hex.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact continuous_subtype_val.comp hσ'
  · intro v w hv hw hvw
    have h1 := hσ v hv
    have h2 := hσ w hw
    have h3 := hσ (v + w) hvw
    refine hinj _ (hCV h3.1) _ (hCC (Set.mul_mem_mul h1.1 h2.1)) ?_
    rw [map_mul, h1.2, h2.2, h3.2, ← hexadd]
    rfl
  · intro ε' hε'
    set ε'' := min ε' ε₁ with hε''def
    have hε'' : 0 < ε'' := lt_min hε' hε₁
    have hnear : ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C ∧
        ∃ u : EuclideanSpace ℝ ι, ‖u‖ < ε'' ∧ ∀ i, Circle.exp (u i) = f x i := by
      refine Filter.Eventually.and (show ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C from
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hC)) ?_
      have ht : Tendsto f (𝓝 (1 : G)) (𝓝 1) := by
        have := (map_continuous f).tendsto (1 : G)
        rwa [map_one] at this
      exact ht.eventually (eventually_exists_small_circleLog hε'')
    apply Filter.mem_of_superset hnear
    rintro x ⟨hxC, u, hu, hux⟩
    have hfx : f x = ex u := funext fun i ↦ (hux i).symm
    have hu1 : ‖u‖ < ε₁ := hu.trans_le (min_le_right _ _)
    have huA : u ∈ A := ⟨hu1.le.trans hε₁R, x, hCV (interior_subset hxC), hfx⟩
    have huL : u ∈ L := hAL' u huA hu1.le
    refine ⟨⟨u, huL⟩, by simpa using hu.trans_le (min_le_left _ _), ?_⟩
    have hs := hσ ⟨u, huL⟩ (by simpa using hu1)
    exact hinj _ (hCV hs.1) _ (hCV (interior_subset hxC)) (by rw [hs.2, hfx])

end TorusHom

section Structure

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.4.1, p. 757. A compact neighborhood of the identity
generates the whole group. -/
def IsCompactlyGeneratedGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ IsCompact U ∧ Subgroup.closure U = ⊤

/-- Paper: Definition D.1.4.1, p. 757. A compact group is compactly generated.
Deviation: Sanity check using the whole group as the generating neighborhood. -/
theorem isCompactlyGeneratedGroup_of_compact [CompactSpace G] :
    IsCompactlyGeneratedGroup G :=
  ⟨Set.univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean space admits charts in
some fixed finite real dimension. -/
def IsLocallyEuclidean (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) X)

/-- Paper: Theorem D.1.4.2, p. 757. A discrete space is locally Euclidean in
dimension zero.
Deviation: Sanity check for the locally Euclidean condition. -/
theorem isLocallyEuclidean_of_discrete (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] : IsLocallyEuclidean X :=
  ⟨0, ⟨ChartedSpace.ofDiscreteTopology⟩⟩

/-- Paper: (D.1.4.2), p. 757. A presentation identifies a group topologically
with a product of real, torus, free discrete and finite discrete abelian factors. -/
structure ElementaryLCAPresentation (G : Type*) [CommGroup G] [TopologicalSpace G] where
  realDim : ℕ
  torusDim : ℕ
  latticeRank : ℕ
  finiteFactor : Type
  [finiteGroup : AddCommGroup finiteFactor]
  [finiteFintype : Fintype finiteFactor]
  [finiteTopology : TopologicalSpace finiteFactor]
  [finiteDiscrete : DiscreteTopology finiteFactor]
  equiv : G ≃ₜ* Multiplicative (ElementaryLieGroup realDim torusDim latticeRank finiteFactor)

attribute [instance] ElementaryLCAPresentation.finiteGroup ElementaryLCAPresentation.finiteFintype
  ElementaryLCAPresentation.finiteTopology ElementaryLCAPresentation.finiteDiscrete

/-- The product of two groups of order two is not cyclic, since its exponent is two. -/
private theorem zmodTwoProd_not_isAddCyclic : ¬ IsAddCyclic (ZMod 2 × ZMod 2) := by
  intro h
  have h1 : AddMonoid.exponent (ZMod 2 × ZMod 2) = Nat.card (ZMod 2 × ZMod 2) :=
    IsAddCyclic.exponent_eq_card
  have h2 : AddMonoid.exponent (ZMod 2 × ZMod 2) ∣ 2 :=
    AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero (by decide)
  rw [h1, Nat.card_eq_fintype_card] at h2
  revert h2
  decide

/-- Paper: (D.1.4.2), p. 757. The Klein four group admits an elementary presentation
whose finite factor has order four and is noncyclic.
Deviation: Sanity check for the finite abelian factor. -/
theorem ElementaryLCAPresentation.exists_kleinFour :
    ∃ e : ElementaryLCAPresentation (Multiplicative (ZMod 2 × ZMod 2)),
      Fintype.card e.finiteFactor = 4 ∧ ¬ IsAddCyclic e.finiteFactor := by
  let a : (ZMod 2 × ZMod 2) ≃+ ElementaryLieGroup 0 0 0 (ZMod 2 × ZMod 2) :=
    { toFun := fun x ↦ (0, 0, 0, x)
      invFun := fun p ↦ p.2.2.2
      left_inv := fun _ ↦ rfl
      right_inv := fun p ↦ Prod.ext (by ext i; exact i.elim0)
        (Prod.ext (by ext i; exact i.elim0) (Prod.ext (by ext i; exact i.elim0) rfl))
      map_add' := fun x y ↦ Prod.ext (by ext i; exact i.elim0)
        (Prod.ext (by ext i; exact i.elim0) (Prod.ext (by ext i; exact i.elim0) rfl)) }
  refine ⟨{ realDim := 0, torusDim := 0, latticeRank := 0, finiteFactor := ZMod 2 × ZMod 2
            equiv := { AddEquiv.toMultiplicative a with
              continuous_toFun := continuous_of_discreteTopology
              continuous_invFun := continuous_of_discreteTopology } }, ?_, ?_⟩
  · change Fintype.card (ZMod 2 × ZMod 2) = 4
    decide
  · exact zmodTwoProd_not_isAddCyclic

/-- A continuous homomorphism from a torus to a real vector group vanishes,
since the multiples of a nonzero vector cannot all lie in a compact range. -/
private theorem elementary_torus_to_euclidean_eq_zero {m n : ℕ}
    (f : (Fin n → AddCircle (1 : ℝ)) →+ EuclideanSpace ℝ (Fin m))
    (hf : Continuous f) (x : Fin n → AddCircle (1 : ℝ)) : f x = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (isCompact_range hf).isBounded
  by_contra hx
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hx
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ‖f x‖)
  have hbound := hC (f (k • x)) ⟨k • x, rfl⟩
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_of_nonneg (Nat.cast_nonneg k)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hpos).mp hk)

/-- The subgroup of a finite torus killed by doubling has cardinality two to
the power of the number of circle coordinates. -/
private theorem elementary_torus_two_torsion_card (n : ℕ) :
    Nat.card {x : Fin n → AddCircle (1 : ℝ) // (2 : ℕ) • x = 0} = 2 ^ n := by
  let half : AddCircle (1 : ℝ) := ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
  have horder : addOrderOf half = 2 := by
    simpa [half] using
      (AddCircle.addOrderOf_period_div (p := (1 : ℝ)) (n := 2) (by decide))
  have hhalf : half ≠ 0 := by
    intro h
    simp [h] at horder
  let f (i : Fin 2) : {x : AddCircle (1 : ℝ) // (2 : ℕ) • x = 0} :=
    ⟨if i = 0 then 0 else half, by
      split
      · exact nsmul_zero _
      · exact horder ▸ addOrderOf_nsmul_eq_zero half⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have hval := congrArg Subtype.val h
      fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm hhalf]
    · intro x
      obtain ⟨k, hk, he⟩ := (AddCircle.nsmul_eq_zero_iff (by decide : 0 < 2)).mp x.property
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      interval_cases k <;> simpa [f, half] using he
  let coords : {x : Fin n → AddCircle (1 : ℝ) // (2 : ℕ) • x = 0} ≃
      (Fin n → Fin 2) :=
    (Equiv.subtypeEquiv (Equiv.refl _) (fun _ ↦ funext_iff)).trans
      (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun _ ↦ (Equiv.ofBijective f hf).symm))
  rw [Nat.card_congr coords, Nat.card_fun, Nat.card_fin, Nat.card_fin]

/-- Paper: (D.1.4.2), p. 757. Two elementary presentations have the same real
dimension, torus dimension and free lattice rank, and isomorphic finite factors.
Deviation: The finite factors are compared up to group isomorphism. -/
theorem ElementaryLCAPresentation.invariants (e e' : ElementaryLCAPresentation G) :
    e.realDim = e'.realDim ∧ e.torusDim = e'.torusDim ∧ e.latticeRank = e'.latticeRank ∧
      Nonempty (e.finiteFactor ≃+ e'.finiteFactor) := by
  let model (p : ElementaryLCAPresentation G) :=
    ElementaryLieGroup p.realDim p.torusDim p.latticeRank p.finiteFactor
  let compare := e.equiv.symm.trans e'.equiv
  let φ : model e ≃ₜ+ model e' :=
    { MulEquiv.toAdditive compare.toMulEquiv with
      continuous_toFun := compare.continuous_toFun
      continuous_invFun := compare.continuous_invFun }
  let assoc (p : ElementaryLCAPresentation G) :
      (EuclideanSpace ℝ (Fin p.realDim) × (Fin p.torusDim → AddCircle (1 : ℝ))) ×
        ((Fin p.latticeRank → ℤ) × p.finiteFactor) ≃ₜ+ model p :=
    ContinuousAddEquiv.mk' (Homeomorph.prodAssoc _ _ _) (fun _ _ ↦ rfl)
  let ψ := (assoc e).trans (φ.trans (assoc e').symm)
  have connected_to_discrete {A B A' B' : Type} [AddZeroClass A] [AddZeroClass B]
      [AddZeroClass A'] [AddZeroClass B'] [TopologicalSpace A] [TopologicalSpace B]
      [TopologicalSpace A'] [TopologicalSpace B'] [PreconnectedSpace A] [DiscreteTopology B']
      (g : A × B ≃ₜ+ A' × B') (a : A) : (g (a, 0)).2 = 0 := by
    let f : A → B' := fun x ↦ (g (x, 0)).2
    have hf : Continuous f := (g.continuous_toFun.comp (continuous_id.prodMk continuous_const)).snd
    calc
      (g (a, 0)).2 = (g (0, 0)).2 := TotallyDisconnectedSpace.eq_of_continuous f hf a 0
      _ = 0 := congrArg Prod.snd (map_zero g)
  obtain ⟨⟨connected⟩, ⟨discrete⟩⟩ := continuousAddEquiv_factors_of_snd_eq_zero ψ
    (connected_to_discrete ψ) (connected_to_discrete ψ.symm)
  let swap {A B : Type} [AddZeroClass A] [AddZeroClass B]
      [TopologicalSpace A] [TopologicalSpace B] : B × A ≃ₜ+ A × B :=
    ContinuousAddEquiv.mk' (Homeomorph.prodComm _ _) (fun _ _ ↦ rfl)
  let γ := swap.trans (connected.trans swap.symm)
  have torus_to_real {m n m' n' : ℕ}
      (g : (Fin n → AddCircle (1 : ℝ)) × EuclideanSpace ℝ (Fin m) ≃ₜ+
        (Fin n' → AddCircle (1 : ℝ)) × EuclideanSpace ℝ (Fin m')) (x : Fin n → AddCircle (1 : ℝ)) :
      (g (x, 0)).2 = 0 :=
    elementary_torus_to_euclidean_eq_zero
      ((AddMonoidHom.snd _ _).comp (g.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl _ _)))
      (g.continuous_toFun.comp (continuous_id.prodMk continuous_const)).snd x
  obtain ⟨⟨torus⟩, ⟨real⟩⟩ := continuousAddEquiv_factors_of_snd_eq_zero γ
    (torus_to_real γ) (torus_to_real γ.symm)
  let δ := swap.trans (discrete.trans swap.symm)
  have finite_to_lattice {F F' : Type} [AddCommGroup F] [AddCommGroup F']
      [TopologicalSpace F] [TopologicalSpace F'] [Finite F] {r r' : ℕ}
      (g : F × (Fin r → ℤ) ≃ₜ+ F' × (Fin r' → ℤ)) (x : F) : (g (x, 0)).2 = 0 := by
    let f : F →+ (Fin r' → ℤ) :=
      (AddMonoidHom.snd _ _).comp (g.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl _ _))
    have h := congrArg f (addOrderOf_nsmul_eq_zero x)
    rw [map_nsmul, map_zero] at h
    exact (nsmul_eq_zero_iff_right (addOrderOf_pos x).ne').mp h
  obtain ⟨⟨finite⟩, ⟨lattice⟩⟩ := continuousAddEquiv_factors_of_snd_eq_zero δ
    (finite_to_lattice δ) (finite_to_lattice δ.symm)
  refine ⟨?_, ?_, ?_, ⟨finite.toAddEquiv⟩⟩
  · let linear := real.toAddEquiv.toRealLinearEquiv real.continuous_toFun real.continuous_invFun
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using linear.toLinearEquiv.finrank_eq
  · have h := Nat.card_congr (torus.toEquiv.subtypeEquiv (p := fun x ↦ (2 : ℕ) • x = 0)
      (q := fun y ↦ (2 : ℕ) • y = 0) fun x ↦ by
        change (2 : ℕ) • x = 0 ↔ (2 : ℕ) • torus x = 0
        rw [← map_nsmul, ← map_zero torus, torus.injective.eq_iff])
    rw [elementary_torus_two_torsion_card, elementary_torus_two_torsion_card] at h
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h
  · simpa only [Module.finrank_pi, Fintype.card_fin] using
      lattice.toAddEquiv.toIntLinearEquiv.finrank_eq

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

open scoped Pointwise in
/-- Circle-valued characters lift to real logarithms on a simply connected chart.
These logarithms rule out nontrivial cyclic subgroups in a smaller neighborhood. -/
private theorem exists_nhds_one_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
  obtain ⟨n, ⟨charts⟩⟩ := hG
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E (1 : G)
  have he : (1 : G) ∈ e.source := mem_chart_source E 1
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source he))
  -- Pull back a ball to obtain a simply connected identity neighborhood.
  let B := Metric.ball (e 1) r
  let U := e.symm '' B
  have hU : IsOpen U := (e.symm.isOpen_image_iff_of_subset_source hrb).mpr Metric.isOpen_ball
  have h1U : (1 : G) ∈ U :=
    ⟨e 1, Metric.mem_ball_self hr, e.left_inv he⟩
  let b : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrb rfl
  let : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  let : SimplyConnectedSpace U := b.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace B := Metric.isOpen_ball.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace U := b.locallyPathConnectedSpace
  let : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace E G
  obtain ⟨V₀, hV₀, h1V₀, hprod⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1U)
  obtain ⟨V, ⟨hV, h1V, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (1 : G)).mem_iff.mp (hV₀.mem_nhds h1V₀)
  have hVV : V * V ⊆ U := (Set.mul_subset_mul hVsub hVsub).trans hprod
  have hVU : V ⊆ U := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx h1V)
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds (hV.mem_nhds h1V)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  apply (pontryaginDual_pairing_separates (G := G)).1
  funext χ
  let χU : C(U, Circle) := ⟨fun u ↦ χ u, χ.continuous.comp continuous_subtype_val⟩
  let oneU : U := ⟨1, h1U⟩
  let oneV : V := ⟨1, h1V⟩
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    χU oneU 0 (Circle.exp_zero.trans (map_one χ).symm)
  have hl (u : U) : Circle.exp (L u) = χ u := congrFun hL u
  let incl (v : V) : U := ⟨v, hVU v.property⟩
  let mul (p : V × V) : U := ⟨p.1 * p.2, hVV (Set.mul_mem_mul p.1.property p.2.property)⟩
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  -- Uniqueness of lifts makes the logarithm additive on pairs from the smaller neighborhood.
  have hAdd (a b : V) : L (mul (a, b)) = L (incl a) + L (incl b) := by
    have hMul : Continuous mul :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
    have hIncl : Continuous incl := continuous_subtype_val.subtype_mk _
    have hAgree : Circle.exp ∘ (fun p : V × V ↦ L (mul p)) =
        Circle.exp ∘ (fun p : V × V ↦ L (incl p.1) + L (incl p.2)) := by
      funext p
      simp [Circle.exp_add, hl, mul, incl, map_mul]
    have hStart : L (mul (oneV, oneV)) = L (incl oneV) + L (incl oneV) := by
      have hmul : mul (oneV, oneV) = oneU := Subtype.ext (one_mul 1)
      have hincl : incl oneV = oneU := rfl
      simp [hmul, hincl, hL0]
    exact congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq (L.continuous.comp hMul)
      ((L.continuous.comp (hIncl.comp continuous_fst)).add
        (L.continuous.comp (hIncl.comp continuous_snd))) hAgree (oneV, oneV) hStart) (a, b)
  -- A nonzero logarithm would grow without bound along the powers inside the compact set.
  let z (k : ℕ) : V := ⟨x ^ k, hKV (hx k)⟩
  have hPow (k : ℕ) : L (incl (z k)) = k * L (incl (z 1)) := by
    induction k with
    | zero =>
      have hz : incl (z 0) = oneU := Subtype.ext (pow_zero x)
      simpa [hz] using hL0
    | succ k ih =>
      have hz : incl (z (k + 1)) = mul (z k, z 1) := Subtype.ext (by simp [incl, mul, z, pow_succ])
      rw [hz, hAdd, ih, Nat.cast_succ, add_mul, one_mul]
  have hKb : IsCompact (Subtype.val ⁻¹' K : Set U) := by
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKc
      (Subtype.range_coe.symm ▸ hKV.trans hVU)
  obtain ⟨M, hM⟩ := (hKb.image L.continuous).isBounded.exists_norm_le
  have hZero : L (incl (z 1)) = 0 := by
    by_contra hNe
    obtain ⟨k, hk⟩ := exists_nat_gt (M / ‖L (incl (z 1))‖)
    have hLe := hM _ (mem_image_of_mem L (show incl (z k) ∈ Subtype.val ⁻¹' K from hx k))
    rw [hPow, norm_mul, Real.norm_natCast] at hLe
    exact (not_lt_of_ge hLe) ((div_lt_iff₀ (norm_pos_iff.mpr hNe)).mp hk)
  have hValue := hl (incl (z 1))
  rw [hZero, Circle.exp_zero] at hValue
  simpa [incl, z] using hValue.symm

/-- Paper: Theorem D.1.4.2, p. 757. A connected, locally Euclidean abelian
topological group admits an additive homomorphism from a finite-dimensional real vector
group that is a local homeomorphism.
Deviation: This isolates the local exponential map. After equipping the group with a
compatible Lie group structure, its exponential is a homomorphism by commutativity
and is a local homeomorphism by the inverse function theorem and translation. -/
theorem exists_euclidean_localHomeomorph {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A] [ConnectedSpace A]
    (hA : IsLocallyEuclidean A) :
    ∃ (k : ℕ) (f : EuclideanSpace ℝ (Fin k) →+ A), IsLocalHomeomorph f := by
  let : T2Space (Multiplicative A) := ‹T2Space A›
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean (G := Multiplicative A) hA
  obtain ⟨t, g, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, hρ1, hgσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel g hker
  obtain ⟨f, hf⟩ := exists_addMonoidHom_eqOn_ball_of_local_additive hρ
    (fun v ↦ Multiplicative.toAdd (σ v)) (fun v w hv hw hvw ↦ hσmul v w hv hw hvw)
  have hcont : Continuous f := continuous_of_continuousAt_zero f <|
    ((continuousOn_congr hf).mpr hσc).continuousAt (Metric.ball_mem_nhds 0 hρ)
  have hopen : IsOpenMap f := by
    apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
    rw [Filter.le_map_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    have hδ : 0 < min ε ρ := lt_min hε hρ
    refine mem_of_superset (hσnhds _ hδ) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvε := Metric.ball_subset_ball (min_le_left ε ρ) hv
    have hvρ := Metric.ball_subset_ball (min_le_right ε ρ) hv
    exact ⟨v, hεU hvε, hf hvρ⟩
  have hinj : Set.InjOn f (Metric.ball 0 ρ) := by
    intro v hv w hw hvw
    have hv' := mem_ball_zero_iff.mp hv
    have hw' := mem_ball_zero_iff.mp hw
    have hσ : σ v = σ w := (hf hv).symm.trans (hvw.trans (hf hw))
    apply Subtype.ext
    refine circleExp_coord_injective (hv'.le.trans hρ1) (hw'.le.trans hρ1) fun i ↦ ?_
    rw [← hgσ v hv' i, ← hgσ w hw' i, hσ]
  have hlocal : IsLocalHomeomorph f := by
    refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun x ↦
      ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρ, ?_⟩
    refine IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hcont.comp continuous_subtype_val) ?_
      (hopen.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap)
    intro v w hvw
    have hv : (v : L) - x ∈ Metric.ball 0 ρ := by
      simpa only [mem_ball_zero_iff, ← dist_eq_norm] using Metric.mem_ball.mp v.property
    have hw : (w : L) - x ∈ Metric.ball 0 ρ := by
      simpa only [mem_ball_zero_iff, ← dist_eq_norm] using Metric.mem_ball.mp w.property
    change f (v : L) = f (w : L) at hvw
    apply Subtype.ext
    exact sub_left_inj.mp (hinj hv hw (by rw [map_sub, map_sub, hvw]))
  let e := (stdOrthonormalBasis ℝ L).repr.symm
  exact ⟨Module.finrank ℝ L, f.comp e.toLinearEquiv.toAddMonoidHom,
    hlocal.comp e.toHomeomorph.isLocalHomeomorph⟩

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean LCA group is a product
of real and torus factors and a discrete abelian group. -/
theorem lca_equiv_real_torus_discrete (hG : IsLocallyEuclidean G) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) ×
        (Fin n → AddCircle (1 : ℝ)) × D)) := by
  let A := Additive G
  have : T2Space A := ‹T2Space G›
  have : LocallyCompactSpace A := ‹LocallyCompactSpace G›
  let H := AddSubgroup.connectedComponentOfZero A
  obtain ⟨k, ⟨charts⟩⟩ := hG
  let : ChartedSpace (EuclideanSpace ℝ (Fin k)) A := charts
  have : LocallyConnectedSpace A := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin k)) A
  have hH : IsOpen (H : Set A) := isOpen_connectedComponent
  have : ConnectedSpace H := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : LocallyCompactSpace H := hH.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, f, hf⟩ := exists_euclidean_localHomeomorph (A := H)
    ⟨k, ⟨TopologicalSpace.Opens.instChartedSpace (⟨H, hH⟩ : TopologicalSpace.Opens A)⟩⟩
  have hRange : IsOpen (f.range : Set H) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hf.isOpenMap _ isOpen_univ
  let U : OpenAddSubgroup H := ⟨f.range, hRange⟩
  have hSurj : Function.Surjective f := by
    have hTop := U.isClopen.eq_univ ⟨0, U.zero_mem⟩
    exact Set.range_eq_univ.mp (by
      change (f.range : Set H) = Set.univ at hTop
      simpa only [AddMonoidHom.coe_range] using hTop)
  have hF : IsOpenQuotientMap f := ⟨hSurj, hf.continuous, hf.isOpenMap⟩
  have hKer : DiscreteTopology f.ker := by
    obtain ⟨V, hV, h0, hinj⟩ := hf.isLocallyInjective 0
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hs : (Subtype.val : f.ker → EuclideanSpace ℝ (Fin d)) ⁻¹' V = {0} := by
      ext x
      exact ⟨fun hx ↦ Set.mem_singleton_iff.mpr
        (Subtype.ext (hinj hx h0 (x.property.trans (map_zero f).symm))),
        fun hx ↦ by
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact h0⟩
    exact hs ▸ hV.preimage continuous_subtype_val
  let : DivisibleBy H ℤ := divisibleByOfSMulRightSurj H ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := hSurj y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f ((z : ℝ)⁻¹ • x) = f x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  have : DiscreteTopology f.ker.toIntSubmodule := hKer
  -- Both quotient maps have the same kernel, so they induce a topological isomorphism.
  obtain ⟨m, n, q, hQ, hQker⟩ := exists_euclidean_torus_quotient f.ker.toIntSubmodule
  have hSameKer : f.ker = q.ker := hQker.symm
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective f hF.surjective
  let eQ := QuotientAddGroup.quotientKerEquivOfSurjective q hQ.surjective
  let eKer := QuotientAddGroup.quotientAddEquivOfEq hSameKer
  let e := eF.symm.trans (eKer.trans eQ)
  have he (x : EuclideanSpace ℝ (Fin d)) : e (f x) = q x := by
    have hfmk : eF (QuotientAddGroup.mk x) = f x := rfl
    rw [← hfmk]
    change eQ (eKer (eF.symm (eF _))) = _
    rw [eF.symm_apply_apply]
    rfl
  have eH : H ≃ₜ+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) :=
    { e with
      continuous_toFun := hF.continuous_comp_iff.mp
        (show Continuous (e ∘ f) from (funext he : e ∘ f = q) ▸ hQ.continuous)
      continuous_invFun := hQ.continuous_comp_iff.mp
        (show Continuous (e.symm ∘ q) from
          (funext fun x ↦ e.symm_apply_eq.mpr (he x).symm : e.symm ∘ q = f) ▸ hF.continuous) }
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open H hH
  let D := A ⧸ H
  have : DiscreteTopology D := QuotientAddGroup.discreteTopology hH
  let product := split.toAddEquiv.trans (AddEquiv.prodCongr eH.toAddEquiv (AddEquiv.refl D))
  let assoc := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ)) D
  refine ⟨m, n, D, inferInstance, inferInstance, inferInstance, ⟨{
    AddEquiv.toMultiplicativeRight (product.trans AddEquiv.prodAssoc) with
    continuous_toFun := assoc.continuous.comp
      ((eH.continuous_toFun.prodMap continuous_id).comp split.continuous_toFun)
    continuous_invFun := split.continuous_invFun.comp
      ((eH.continuous_invFun.prodMap continuous_id).comp assoc.symm.continuous) }⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The compact-open neighborhoods of the trivial character test values on compact sets. -/
private theorem pontryaginDual_nhds_one_hasBasis :
    (𝓝 (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × Set Circle ↦ IsCompact p.1 ∧ p.2 ∈ 𝓝 (1 : Circle))
      (fun p ↦ {χ | MapsTo χ p.1 p.2}) := by
  let f : PontryaginDual G → C(G, Circle) := ContinuousMonoidHom.toContinuousMap
  have hf : IsInducing f := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
  rw [hf.nhds_eq_comap]
  exact ((𝓝 (1 : Circle)).basis_sets.nhds_continuousMapConst (X := G)).comap f

/-- Paper: Theorem D.1.4.3(1), p. 757. A locally compact Hausdorff abelian group
with a continuous homomorphism to a finite-dimensional torus and discrete kernel
is locally Euclidean.
Deviation: This isolates the local chart construction. On a sufficiently small
compact identity neighborhood the homomorphism is an embedding. In logarithm
coordinates its image near zero is a relatively closed local additive subgroup
of a finite-dimensional real vector space, hence locally a linear subspace.
Translation gives charts at every point. -/
theorem isLocallyEuclidean_of_discrete_torus_kernel {ι : Type*} [Finite ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  sorry

open scoped Pointwise in
/-- A neighborhood containing no nontrivial cyclic subgroup lets finitely many
characters detect the identity locally. -/
private theorem isLocallyEuclidean_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) : IsLocallyEuclidean G := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pontryaginDual_pairing_separates (G := G)).1
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine isLocallyEuclidean_of_discrete_torus_kernel f
    (discreteTopology_of_isOpen_singleton_one ?_)
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

omit [T2Space G] in
/-- If the dual is locally Euclidean, the subgroup generated by a suitable compact
neighborhood has no nontrivial characters on its quotient, so it equals the whole group. -/
private theorem isCompactlyGeneratedGroup_of_dual_locallyEuclidean
    (h : IsLocallyEuclidean (PontryaginDual G)) : IsCompactlyGeneratedGroup G := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean h
  obtain ⟨⟨K, U⟩, ⟨hK, hU⟩, hSub⟩ := pontryaginDual_nhds_one_hasBasis.mem_iff.mp hW
  obtain ⟨L, hL, hLnhds⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (K ∪ L)
  refine ⟨K ∪ L, mem_of_superset hLnhds subset_union_right, hK.union hL, ?_⟩
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
    (mem_of_superset hLnhds (subset_union_right.trans Subgroup.subset_closure))
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  have hKill (ψ : PontryaginDual (G ⧸ H)) : PontryaginDual.map q ψ = 1 := by
    let φ : G →ₜ* Circle := PontryaginDual.map q ψ
    apply hPow
    intro k
    apply hSub
    intro x hx
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.subset_closure (Or.inl hx))
    change (φ ^ k) x ∈ U
    rw [ContinuousMonoidHom.pow_apply]
    change (PontryaginDual.map q ψ x) ^ k ∈ U
    rw [PontryaginDual.map_apply, hqx, map_one, one_pow]
    exact mem_of_mem_nhds hU
  refine eq_top_iff.mpr fun x _ ↦ (QuotientGroup.eq_one_iff x).mp ?_
  apply (pontryaginDual_pairing_separates (G := G ⧸ H)).1
  funext ψ
  exact DFunLike.congr_fun (hKill ψ) x |>.trans (map_one ψ).symm

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. An LCA group is compactly generated
exactly when its dual is locally Euclidean. -/
theorem isCompactlyGeneratedGroup_iff_dual_locallyEuclidean :
    IsCompactlyGeneratedGroup G ↔ IsLocallyEuclidean (PontryaginDual G) := by
  constructor
  · rintro ⟨K, _, hK, hGen⟩
    have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
      simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
    refine isLocallyEuclidean_of_noSmallCyclicSubgroups
      (pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (K, _)) ⟨hK, hC⟩) ?_
    intro χ hχ
    have hTrivial : K ⊆ (χ : G →ₜ* Circle).toMonoidHom.ker := by
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      let φ : G →ₜ* Circle := χ
      change φ x ^ k ∈ Circle.centeredArc (Real.pi / 2)
      rw [← ContinuousMonoidHom.pow_apply]
      exact hχ k hx
    have hTop : ⊤ ≤ (χ : G →ₜ* Circle).toMonoidHom.ker :=
      hGen ▸ (Subgroup.closure_le _).mpr hTrivial
    exact PontryaginDual.ext fun x ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top x))
  · exact isCompactlyGeneratedGroup_of_dual_locallyEuclidean

open scoped Pointwise in
-- Retain the Hausdorff and local compactness assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. A closed subgroup of a compactly generated
LCA group is compactly generated. -/
theorem isCompactlyGeneratedGroup_closedSubgroup (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup H := by
  classical
  obtain ⟨U, hU, hUc, hGen⟩ := hG
  -- Write every element as a product of finitely many fixed directions and a remainder in U.
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates
    ((hUc.union hUc.inv).mul hUc) ⟨1, mem_interior_iff_mem_nhds.mpr hU⟩
  let a (n : t → ℕ) : G := ∏ i : t, ((i : G)⁻¹) ^ n i
  have ha0 : a 0 = 1 := by simp [a]
  have haAdd (m n : t → ℕ) : a (m + n) = a m * a n := by
    simp only [a, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have haSingle (i : t) : a (Pi.single i 1) = (i : G)⁻¹ := by
    unfold a
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, pow_zero])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same, pow_one]
  have hStep (x : G) (hx : x ∈ U ∪ U⁻¹) (y : G)
      (hy : ∃ n : t → ℕ, ∃ u ∈ U, y = a n * u) :
      ∃ n : t → ℕ, ∃ u ∈ U, x * y = a n * u := by
    obtain ⟨n, u, hu, rfl⟩ := hy
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (ht (Set.mul_mem_mul hx hu))
    change i * (x * u) ∈ U at hiu
    refine ⟨n + Pi.single ⟨i, hi⟩ 1, i * (x * u), hiu, ?_⟩
    rw [haAdd, haSingle]
    simp [mul_assoc, mul_left_comm]
  have hRepresent (x : G) : ∃ n : t → ℕ, ∃ u ∈ U, x = a n * u := by
    have hx : x ∈ Subgroup.closure U := hGen.symm ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction_left (p := fun z _ ↦ ∃ n : t → ℕ, ∃ u ∈ U, z = a n * u)
      ⟨0, 1, mem_of_mem_nhds hU, by simp [ha0]⟩ ?_ ?_ hx
    · exact fun z hz y _ ↦ hStep z (Or.inl hz) y
    · exact fun z hz y _ ↦ hStep z⁻¹ (Or.inr (by simpa using hz)) y
  obtain ⟨V, hV, _, hVinv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hUc
    ⟨1, mem_interior_iff_mem_nhds.mpr hV⟩
  -- For each translate, Dickson's lemma bounds the minimal nonzero exponent vectors.
  let P (i : s) (n : t → ℕ) : Prop :=
    n ≠ 0 ∧ ∃ u ∈ U, (i : G) * u ∈ V ∧ a n * u ∈ H
  let M : Set (t → ℕ) := {0} ∪ ⋃ i : s, {n | Minimal (P i) n}
  have hM : M.Finite := (finite_singleton 0).union (finite_iUnion fun i ↦
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (P i)))
  let K : Set G := (a '' M) * U
  let S : Set H := Subtype.val ⁻¹' K
  let J : Subgroup G := (Subgroup.closure S).map H.subtype
  have hK : IsCompact K := (hM.image a).isCompact.mul hUc
  have hUK : U ⊆ K := by
    intro u hu
    rw [← one_mul u, ← ha0]
    exact Set.mul_mem_mul (mem_image_of_mem a (Or.inl rfl)) hu
  have hMem (x : G) (hx : x ∈ H) (hxK : x ∈ K) : x ∈ J :=
    Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure hxK, rfl⟩
  have hReduce (n : t → ℕ) : ∀ u ∈ U, a n * u ∈ H → a n * u ∈ J := by
    refine wellFounded_lt.induction (C := fun m ↦ ∀ u ∈ U, a m * u ∈ H → a m * u ∈ J) n ?_
    clear n
    intro n ih u hu hnu
    by_cases hn : n = 0
    · exact hMem _ hnu (Set.mul_mem_mul (mem_image_of_mem a (Or.inl hn)) hu)
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (hs hu)
    let j : s := ⟨i, hi⟩
    obtain ⟨m, hmn, hm⟩ := exists_minimal_le_of_wellFoundedLT (P j) n
      ⟨hn, u, hu, hiu, hnu⟩
    obtain ⟨hm0, v, hv, hiv, hmv⟩ := hm.prop
    obtain ⟨d, hd⟩ := exists_add_of_le hmn
    have hdn : d < n := by
      rw [hd]
      exact lt_add_of_pos_left d (lt_of_le_of_ne (fun i ↦ Nat.zero_le (m i)) hm0.symm)
    have huv : u / v ∈ U := by
      have hInv : (i * v)⁻¹ ∈ V := hVinv ▸ Set.mem_inv.mpr (by simpa using hiv)
      have hMul := hVV (Set.mul_mem_mul hiu hInv)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul
    have hFactor : a n * u = (a m * v) * (a d * (u / v)) := by
      rw [hd, haAdd]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hdH : a d * (u / v) ∈ H := by
      simpa only [hFactor, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hmv) hnu
    rw [hFactor]
    exact J.mul_mem (hMem _ hmv (Set.mul_mem_mul (mem_image_of_mem a
      (Or.inr (mem_iUnion.mpr ⟨j, hm⟩))) hv)) (ih d hdn (u / v) huv hdH)
  refine ⟨S, continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hU hUK),
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨n, u, hu, hx⟩ := hRepresent x
  have hxJ : (x : G) ∈ J := hx ▸ hReduce n u hu (hx ▸ x.property)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxJ
  exact (Subtype.ext hyx : y = x) ▸ hy

-- Retain the LCA and closedness assumptions in the existing signature.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Theorem D.1.4.3(1), p. 757. The quotient of a compactly generated LCA
group by a closed subgroup is compactly generated. -/
theorem isCompactlyGeneratedGroup_quotient (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup (G ⧸ H) := by
  obtain ⟨U, hU, hCompact, hGen⟩ := hG
  let q := QuotientGroup.mk' H
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨q '' U, ?_, hCompact.image hq.continuous, ?_⟩
  · simpa only [map_one] using hq.isOpenMap.image_mem_nhds hU
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective q hq.surjective]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The real, torus and discrete factors of an elementary presentation give product charts. -/
private theorem locallyEuclidean_of_elementaryPresentation
    (e : ElementaryLCAPresentation G) : IsLocallyEuclidean G := by
  let R := Fin e.realDim → ℝ
  let T := ModelPi (fun _ : Fin e.torusDim ↦ ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  let : ChartedSpace R (EuclideanSpace ℝ (Fin e.realDim)) :=
    (PiLp.homeomorph 2 (fun _ : Fin e.realDim ↦ ℝ)).symm.chartedSpace
  let : ChartedSpace ℝ (AddCircle (1 : ℝ)) :=
    (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).chartedSpace QuotientAddGroup.mk_surjective
  let : ChartedSpace PUnit.{1} D := ChartedSpace.ofDiscreteTopology
  let M := ModelProd R (ModelProd T PUnit.{1})
  let charts : ChartedSpace M
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    prodChartedSpace _ _ _ _
  let : ChartedSpace M
      (Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) := charts
  let : ChartedSpace M G := e.equiv.toHomeomorph.symm.chartedSpace
  let h : M ≃ₜ EuclideanSpace ℝ (Fin (e.realDim + e.torusDim)) :=
    (Homeomorph.prodCongr (Homeomorph.refl R) (Homeomorph.prodUnique T PUnit)).trans
      ((Fin.appendHomeomorph e.realDim e.torusDim).trans (PiLp.homeomorph 2 _).symm)
  let : ChartedSpace (EuclideanSpace ℝ (Fin (e.realDim + e.torusDim))) M := h.symm.chartedSpace
  exact ⟨e.realDim + e.torusDim, ⟨ChartedSpace.comp _ M G⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- An elementary presentation gives a compact generating neighborhood. -/
private theorem compactlyGenerated_of_elementaryPresentation
    (e : ElementaryLCAPresentation G) : IsCompactlyGeneratedGroup G := by
  let R := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (0 : R)
  have hKgen : AddSubgroup.closure K = ⊤ := by
    let H := AddSubgroup.closure K
    have hH := H.isOpen_of_mem_nhds (mem_of_superset hKnhds AddSubgroup.subset_closure)
    exact SetLike.coe_injective ((OpenAddSubgroup.mk H hH).isClopen.eq_univ ⟨0, H.zero_mem⟩)
  obtain ⟨S, hSgen, hS⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG D)
  let U : Set (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    K ×ˢ ((univ : Set T) ×ˢ insert 0 S)
  have hD : insert 0 S ∈ 𝓝 (0 : D) := (isOpen_discrete _).mem_nhds (mem_insert _ _)
  have hU : U ∈ 𝓝 0 := prod_mem_nhds hKnhds (prod_mem_nhds univ_mem hD)
  have hUc : IsCompact U := hK.prod (isCompact_univ.prod (hS.insert 0).isCompact)
  have hUgen : AddSubgroup.closure U = ⊤ := by
    change AddSubgroup.closure (K ×ˢ ((univ : Set T) ×ˢ insert 0 S)) = ⊤
    rw [AddSubgroup.closure_prod (mem_of_mem_nhds hKnhds) (by simp),
      AddSubgroup.closure_prod (mem_univ (0 : T)) (mem_insert 0 S), hKgen,
      AddSubgroup.closure_univ, AddSubgroup.closure_insert_zero, hSgen,
      AddSubgroup.top_prod_top, AddSubgroup.top_prod_top]
  let f := e.equiv.symm.toMulEquiv.toMonoidHom
  let V : Set (Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) :=
    Multiplicative.toAdd ⁻¹' U
  have hV : V ∈ 𝓝 1 := hU
  refine ⟨f '' V, ?_, hUc.image e.equiv.symm.continuous, ?_⟩
  · have h := e.equiv.symm.toHomeomorph.isOpenMap.image_mem_nhds hV
    change f '' V ∈ 𝓝 (f 1) at h
    rwa [map_one] at h
  · have hVgen : Subgroup.closure V = ⊤ := by
      rw [← AddSubgroup.toSubgroup_closure, hUgen]
      rfl
    rw [← MonoidHom.map_closure, hVgen,
      Subgroup.map_top_of_surjective f e.equiv.symm.surjective]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- In a real–torus–discrete decomposition of a compactly generated group, the discrete
factor is finitely generated and splits as a free abelian group times a finite group. -/
private theorem elementaryPresentation_of_compactlyGenerated
    {m n : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]
    (hG : IsCompactlyGeneratedGroup G)
    (e : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) × D)) :
    Nonempty (ElementaryLCAPresentation G) := by
  classical
  obtain ⟨U, _, hUc, hUgen⟩ := hG
  let R := EuclideanSpace ℝ (Fin m)
  let T := Fin n → AddCircle (1 : ℝ)
  let eA := MulEquiv.toAdditiveLeft e.toMulEquiv
  let p := ((AddMonoidHom.snd T D).comp (AddMonoidHom.snd R (T × D))).comp eA.toAddMonoidHom
  have hp : Function.Surjective p := fun d ↦
    ⟨eA.symm (0, 0, d), congrArg (fun a : R × T × D ↦ a.2.2) (eA.apply_symm_apply _)⟩
  have hpc : Continuous p := (continuous_snd.comp continuous_snd).comp e.continuous
  let V : Set (Additive G) := Additive.toMul ⁻¹' U
  have hVgen : AddSubgroup.closure V = ⊤ := by
    rw [← Subgroup.toAddSubgroup_closure, hUgen]
    rfl
  have : AddGroup.FG D := AddGroup.fg_iff.mpr
    ⟨p '' V, by
      rw [← AddMonoidHom.map_closure, hVgen,
        AddSubgroup.map_top_of_surjective p hp],
      (hUc.image hpc).finite DiscreteTopology.isDiscrete⟩
  obtain ⟨r, ι, _, q, hq, k, ⟨d⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod D
  let F := (i : ι) → ZMod (q i ^ k i)
  let (i : ι) : NeZero (q i ^ k i) := ⟨pow_ne_zero _ (hq i).ne_zero⟩
  let : Fintype F := inferInstanceAs (Fintype ((i : ι) → ZMod (q i ^ k i)))
  let : TopologicalSpace F := ⊥
  let : DiscreteTopology F := ⟨rfl⟩
  let d' : D ≃+ (Fin r → ℤ) × F :=
    d.trans (AddEquiv.prodCongr Finsupp.addEquivFunOnFinite (DirectSum.addEquivProd _))
  let e' := AddEquiv.toMultiplicativeRight
    (eA.trans (AddEquiv.prodCongr (AddEquiv.refl R) (AddEquiv.prodCongr (AddEquiv.refl T) d')))
  refine ⟨{ realDim := m, torusDim := n, latticeRank := r, finiteFactor := F
            equiv := ?_ }⟩
  exact { e' with
    continuous_toFun := (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := d')))).comp e.continuous
    continuous_invFun := e.symm.continuous.comp (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := d'.symm)))) }

/-- Paper: Theorem D.1.4.3(2), p. 757. An LCA group has an elementary presentation
exactly when it is compactly generated and locally Euclidean. -/
theorem lca_elementary_iff :
    (IsCompactlyGeneratedGroup G ∧ IsLocallyEuclidean G) ↔
      Nonempty (ElementaryLCAPresentation G) := by
  constructor
  · rintro ⟨hCompact, hEuclidean⟩
    obtain ⟨m, n, D, _, _, _, ⟨e⟩⟩ := lca_equiv_real_torus_discrete hEuclidean
    exact elementaryPresentation_of_compactlyGenerated hCompact e
  · rintro ⟨e⟩
    exact ⟨compactlyGenerated_of_elementaryPresentation e,
      locallyEuclidean_of_elementaryPresentation e⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: (D.1.4.3), p. 758. The indexing set consists of open compactly
generated subgroups ordered by inclusion. -/
abbrev OpenCompactlyGeneratedSubgroups (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ IsCompactlyGeneratedGroup H}

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (D.1.4.3), p. 758. The open compactly generated subgroups are filtered
and cover the group. The topology is final for their open inclusions. -/
theorem openCompactlyGeneratedSubgroups_colimit :
    IsDirectedOrder (OpenCompactlyGeneratedSubgroups G) ∧
      (∀ x : G, ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val) ∧
      (∀ U : Set G, IsOpen U ↔
        ∀ H : OpenCompactlyGeneratedSubgroups G, IsOpen (Subtype.val ⁻¹' U : Set H.val)) := by
  let ofCompactNeighborhood (K : Set G) (hK : IsCompact K) (hKnhds : K ∈ 𝓝 (1 : G)) :
      OpenCompactlyGeneratedSubgroups G := by
    let H := Subgroup.closure K
    have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
      (mem_of_superset hKnhds Subgroup.subset_closure)
    exact ⟨H, hH, Subtype.val ⁻¹' K,
      continuous_subtype_val.continuousAt.preimage_mem_nhds hKnhds,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage hK,
      Subgroup.closure_preimage_eq_top K⟩
  have hCover (x : G) : ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val := by
    obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
    exact ⟨ofCompactNeighborhood (insert x K) (hK.insert x)
      (mem_of_superset hKnhds (subset_insert x K)), Subgroup.subset_closure (mem_insert x K)⟩
  refine ⟨⟨?_⟩, hCover, ?_⟩
  · intro H J
    obtain ⟨A, hAnhds, hA, hAgen⟩ := H.property.2
    obtain ⟨B, _, hB, hBgen⟩ := J.property.2
    have hAnhds' : H.val.subtype '' A ∈ 𝓝 (1 : G) :=
      H.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hAnhds
    let L := ofCompactNeighborhood (H.val.subtype '' A ∪ J.val.subtype '' B)
      ((hA.image continuous_subtype_val).union (hB.image continuous_subtype_val))
      (mem_of_superset hAnhds' subset_union_left)
    have hL : L.val = H.val ⊔ J.val := by
      change Subgroup.closure (H.val.subtype '' A ∪ J.val.subtype '' B) = _
      rw [Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
        hAgen, hBgen, Subgroup.map_top, Subgroup.map_top, Subgroup.range_subtype,
        Subgroup.range_subtype]
    exact ⟨L, le_sup_left.trans hL.ge, le_sup_right.trans hL.ge⟩
  · intro U
    refine ⟨fun hU H ↦ hU.preimage continuous_subtype_val, ?_⟩
    intro hU
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    obtain ⟨H, hxH⟩ := hCover x
    have hImage := H.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ (hU H)
    exact mem_of_superset (hImage.mem_nhds ⟨⟨x, hxH⟩, hx, rfl⟩)
      (fun _ ⟨_, hy, hEq⟩ ↦ hEq ▸ hy)

omit [T2Space G] in
/-- Every compact set is contained in an open compactly generated subgroup. -/
private theorem exists_openCompactlyGeneratedSubgroup_contains {K : Set G} (hK : IsCompact K) :
    ∃ H : OpenCompactlyGeneratedSubgroups G, K ⊆ (H.val : Set G) := by
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (U ∪ K)
  have hSubset : U ∪ K ⊆ (H : Set G) := Subgroup.subset_closure
  have hOpen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hU₁ (subset_union_left.trans hSubset))
  refine ⟨⟨H, hOpen, ⟨Subtype.val ⁻¹' (U ∪ K), ?_, ?_, ?_⟩⟩,
    subset_union_right.trans hSubset⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hU₁ subset_union_left)
  · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hU.union hK)
      (Subtype.range_coe.symm ▸ hSubset)
  · exact Subgroup.closure_preimage_eq_top _

/-- Paper: Lemma D.1.4.4, p. 758. Evaluation on the open compactly generated
subgroups of the dual identifies the group with their duals' inverse limit.
Deviation: The limit is expressed as the range in the product, with the subspace topology. -/
theorem lca_dualSubgroups_inverseLimit :
    let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
    ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val),
      (∀ x H (χ : H.val), γ x H χ = χ.val x) ∧ IsEmbedding γ ∧
        range γ = {a | ∀ (H J : I) (h : H ≤ J) (χ : H.val),
          a H χ = a J (Subgroup.inclusion h χ)} := by
  classical
  let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
  change ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val), _
  have hCover (χ : PontryaginDual G) : ∃ H : I, χ ∈ H.val := by
    obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains (isCompact_singleton (x := χ))
    exact ⟨H, hH (mem_singleton χ)⟩
  have hDirected (H J : I) : ∃ L : I, H ≤ L ∧ J ≤ L := by
    obtain ⟨U, _, hU, hUgen⟩ := H.property.2
    obtain ⟨V, _, hV, hVgen⟩ := J.property.2
    obtain ⟨L, hL⟩ := exists_openCompactlyGeneratedSubgroup_contains
      ((hU.image continuous_subtype_val).union (hV.image continuous_subtype_val))
    have hLe (M : I) {S : Set M.val} (hGen : Subgroup.closure S = ⊤)
        (hSub : Subtype.val '' S ⊆ (L.val : Set (PontryaginDual G))) : M ≤ L := by
      have hTop : (⊤ : Subgroup M.val) ≤ L.val.comap M.val.subtype :=
        hGen ▸ (Subgroup.closure_le _).mpr (fun x hx ↦ hSub (mem_image_of_mem Subtype.val hx))
      exact fun x hx ↦ hTop (Subgroup.mem_top (⟨x, hx⟩ : M.val))
    exact ⟨L, hLe H hUgen (subset_union_left.trans hL), hLe J hVgen (subset_union_right.trans hL)⟩
  let restrict (H : I) : PontryaginDual (PontryaginDual G) →ₜ* PontryaginDual H.val :=
    PontryaginDual.map ⟨H.val.subtype, continuous_subtype_val⟩
  let γ : G →ₜ* ((H : I) → PontryaginDual H.val) :=
    { toFun := fun x H ↦ restrict H (pontryaginDual_eval x)
      map_one' := funext fun H ↦ (restrict H).comp pontryaginDual_eval |>.map_one
      map_mul' := fun x y ↦ funext fun H ↦ (restrict H).comp pontryaginDual_eval |>.map_mul x y
      continuous_toFun := continuous_pi fun H ↦ (restrict H).continuous.comp
        (pontryaginDual_eval (G := G)).continuous }
  have hEval (x : G) (H : I) (χ : H.val) : γ x H χ = χ.val x := rfl
  refine ⟨γ, hEval, ⟨?_, ?_⟩, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto γ (𝓝 1) (𝓝 (γ 1)) := γ.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      -- A single coordinate contains all the characters needed to test this neighborhood.
      obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
      obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
      have hKH : IsCompact (Subtype.val ⁻¹' K : Set H.val) :=
        IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (Subtype.range_coe.symm ▸ hH)
      let V : Set (PontryaginDual H.val) :=
        {ψ | MapsTo ψ (Subtype.val ⁻¹' K) (Metric.ball 1 (1 / 4))}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo hKH Metric.isOpen_ball).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap H.val Circle).continuous
      refine Filter.mem_comap.mpr ⟨(fun a ↦ a H) ⁻¹' V,
        (hV.preimage (continuous_apply H)).mem_nhds ?_, ?_⟩
      · intro χ _
        simp [Metric.mem_ball]
      · intro x hx
        apply hTest x
        intro χ hχ
        exact hx (show (⟨χ, hH hχ⟩ : H.val) ∈ Subtype.val ⁻¹' K from hχ)
  · intro x y hxy
    apply (pontryaginDual_pairing_separates (G := G)).1
    funext χ
    obtain ⟨H, hH⟩ := hCover χ
    exact congrArg (fun a ↦ a H ⟨χ, hH⟩) hxy
  · ext a
    constructor
    · rintro ⟨x, rfl⟩ H J h χ
      rfl
    · intro ha
      change ∀ (H J : I) (h : H ≤ J) (χ : H.val),
        a H χ = a J (Subgroup.inclusion h χ) at ha
      choose H hH using hCover
      let f (χ : PontryaginDual G) := a (H χ) ⟨χ, hH χ⟩
      -- Compatibility makes the chosen subgroup irrelevant.
      have hf (J : I) (χ : J.val) : f χ.val = a J χ := by
        obtain ⟨L, h₁, h₂⟩ := hDirected (H χ.val) J
        exact (ha _ _ h₁ _).trans (ha _ _ h₂ χ).symm
      let J := H 1
      let ψ : PontryaginDual (PontryaginDual G) :=
        { toFun := f
          map_one' := (hf J 1).trans (map_one (a J))
          map_mul' := fun χ ξ ↦ by
            obtain ⟨L, hχ, hξ⟩ := hDirected (H χ) (H ξ)
            let χL : L.val := ⟨χ, hχ (hH χ)⟩
            let ξL : L.val := ⟨ξ, hξ (hH ξ)⟩
            exact (hf L (χL * ξL)).trans
              ((map_mul (a L) χL ξL).trans (congrArg₂ (· * ·) (hf L χL).symm (hf L ξL).symm))
          continuous_toFun := by
            rw [continuous_iff_continuousAt]
            intro χ
            let J := H χ
            have hComp : f ∘ (Subtype.val : J.val → PontryaginDual G) = a J := funext (hf J)
            exact J.property.1.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
              (hComp.symm ▸ (a J).continuous.continuousAt (x := (⟨χ, hH χ⟩ : J.val))) }
      obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
      refine ⟨e.symm ψ, funext fun J ↦ PontryaginDual.ext fun χ ↦ ?_⟩
      rw [hEval, ← he, e.apply_symm_apply]
      exact hf J χ

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator consists of characters
whose restriction to the subgroup is trivial. -/
def lcaAnnihilator (H : Subgroup G) : Subgroup (PontryaginDual G) :=
  (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)).toMonoidHom.ker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator in the original group is
the intersection of the kernels of the characters in the given subgroup. -/
def lcaDualAnnihilator (J : Subgroup (PontryaginDual G)) : Subgroup G :=
  ⨅ χ : J, (show G →ₜ* Circle from χ.val).toMonoidHom.ker

/-- Paper: Definition D.1.4.5, p. 758. A character is in the annihilator exactly
when its value on every element of the subgroup is one. -/
theorem mem_lcaAnnihilator_iff (H : Subgroup G) (χ : PontryaginDual G) :
    χ ∈ lcaAnnihilator H ↔ ∀ x : H, χ x.val = 1 := by
  rw [lcaAnnihilator, MonoidHom.mem_ker]
  constructor
  · intro h x
    exact congrArg (fun ψ : PontryaginDual H ↦ ψ x) h
  · exact fun h ↦ PontryaginDual.ext h

/-- Paper: Definition D.1.4.5, p. 758. A group element is in the dual annihilator
exactly when every character of the subgroup takes value one there. -/
theorem mem_lcaDualAnnihilator_iff (J : Subgroup (PontryaginDual G)) (x : G) :
    x ∈ lcaDualAnnihilator J ↔ ∀ χ : J, χ.val x = 1 :=
  Subgroup.mem_iInf

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(1), p. 758. Taking the annihilator twice recovers a
closed subgroup under the evaluation pairing. -/
theorem lcaDualAnnihilator_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    lcaDualAnnihilator (lcaAnnihilator H) = H := by
  ext x
  rw [mem_lcaDualAnnihilator_iff]
  constructor
  · intro hx
    let : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
    let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    apply (QuotientGroup.eq_one_iff x).mp
    apply (pontryaginDual_pairing_separates (G := G ⧸ H)).1
    funext ψ
    have hψ : PontryaginDual.map q ψ ∈ lcaAnnihilator H := by
      apply (mem_lcaAnnihilator_iff H _).mpr
      intro y
      have hy : q y.val = 1 := (QuotientGroup.eq_one_iff y.val).mpr y.property
      rw [PontryaginDual.map_apply, hy, map_one]
    exact (hx ⟨PontryaginDual.map q ψ, hψ⟩).trans (map_one ψ).symm
  · intro hx χ
    exact (mem_lcaAnnihilator_iff H χ.val).mp χ.property ⟨x, hx⟩

omit [T2Space G] in
/-- A compact subset of a quotient of a locally compact group lies in the image of a compact set. -/
private theorem exists_isCompact_quotient_preimage (H : Subgroup G) {K : Set (G ⧸ H)}
    (hK : IsCompact K) : ∃ C : Set G, IsCompact C ∧ K ⊆ QuotientGroup.mk '' C := by
  obtain ⟨L, hLcomp, hL⟩ := exists_compact_mem_nhds (1 : G)
  have hU : QuotientGroup.mk '' L ∈ 𝓝 (1 : G ⧸ H) :=
    (QuotientGroup.isOpenMap_coe (N := H)).image_mem_nhds hL
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK
    ⟨(1 : G ⧸ H), mem_interior_iff_mem_nhds.mpr hU⟩
  refine ⟨⋃ g ∈ t, Homeomorph.mulLeft (g.out)⁻¹ '' L,
    t.isCompact_biUnion fun g _ =>
      hLcomp.image (Homeomorph.mulLeft (g.out)⁻¹).continuous, ?_⟩
  intro k hk
  obtain ⟨g, hg, hkU⟩ := mem_iUnion₂.mp (ht hk)
  rw [mem_preimage, mem_image] at hkU
  obtain ⟨y, hy, hgy⟩ := hkU
  refine ⟨(g.out)⁻¹ * y, mem_iUnion₂.mpr ⟨g, hg, mem_image_of_mem _ hy⟩, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hgy,
    inv_mul_cancel_left]

/-- Paper: Lemma D.1.4.6(2), p. 758. Pullback by the quotient map identifies
the dual of a quotient with the annihilator. -/
theorem lcaQuotientDual_equiv_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H,
      ∀ (χ : PontryaginDual (G ⧸ H)) x, (e χ).val x = χ (QuotientGroup.mk x) := by
  -- Closedness of `H` makes the quotient Hausdorff.
  have hpre : QuotientGroup.mk ⁻¹' ({1} : Set (G ⧸ H)) = (H : Set G) := by
    simpa [QuotientGroup.mk_one] using QuotientGroup.preimage_mk_one H
  have : T2Space (G ⧸ H) := IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage, hpre]
    exact hH
  let q : G →ₜ* G ⧸ H :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  have hq (x : G) : q x = QuotientGroup.mk x := by
    change QuotientGroup.mk' H x = QuotientGroup.mk x
    exact QuotientGroup.mk'_apply H x
  have hker (ψ : lcaAnnihilator H) : H ≤ ψ.val.toMonoidHom.ker := by
    intro x hx
    exact (mem_lcaAnnihilator_iff H ψ.val).1 ψ.property ⟨x, hx⟩
  let toAnn : PontryaginDual (G ⧸ H) →* lcaAnnihilator H :=
    { toFun := fun χ => ⟨PontryaginDual.map q χ, by
        rw [mem_lcaAnnihilator_iff]
        intro x
        rw [PontryaginDual.map_apply]
        have : q x.val = 1 := by
          change QuotientGroup.mk x.val = 1
          exact (QuotientGroup.eq_one_iff _).2 x.property
        rw [this, map_one]⟩
      map_one' := Subtype.ext (map_one (PontryaginDual.map q))
      map_mul' := fun χ φ => Subtype.ext (map_mul (PontryaginDual.map q) χ φ) }
  let fromAnnFun (ψ : lcaAnnihilator H) : PontryaginDual (G ⧸ H) :=
    { toMonoidHom := QuotientGroup.lift H ψ.val.toMonoidHom (hker ψ)
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ψ.val.continuous_toFun }
  have happly (ψ : lcaAnnihilator H) (x : G) :
      fromAnnFun ψ (QuotientGroup.mk x) = ψ.val x := by
    dsimp [fromAnnFun]
    exact QuotientGroup.lift_mk' H (hker ψ) x
  let fromAnn : lcaAnnihilator H →* PontryaginDual (G ⧸ H) :=
    { toFun := fromAnnFun
      map_one' := by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly 1 x]
        rfl
      map_mul' := fun ψ φ => by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly (ψ * φ) x]
        have hr :
            (fromAnnFun ψ * fromAnnFun φ) (QuotientGroup.mk x) =
              fromAnnFun ψ (QuotientGroup.mk x) * fromAnnFun φ (QuotientGroup.mk x) :=
          ContinuousMonoidHom.mul_apply _ _ _
        rw [hr, happly ψ x, happly φ x, Subgroup.coe_mul]
        rfl }
  have hinv_left (χ : PontryaginDual (G ⧸ H)) : fromAnn (toAnn χ) = χ := by
    apply PontryaginDual.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    dsimp [fromAnn]
    rw [happly (toAnn χ) x]
    dsimp [toAnn]
    rw [hq]
  have hinv_right (ψ : lcaAnnihilator H) : toAnn (fromAnn ψ) = ψ := by
    apply Subtype.ext
    apply PontryaginDual.ext
    intro x
    dsimp [toAnn, fromAnn]
    rw [hq, happly ψ x]
  have hbij : Function.Bijective toAnn :=
    ⟨fun χ φ h => (hinv_left χ).symm.trans ((congrArg fromAnn h).trans (hinv_left φ)),
      fun ψ => ⟨fromAnn ψ, hinv_right ψ⟩⟩
  have hto_cont : Continuous toAnn := by
    rw [IsInducing.subtypeVal.continuous_iff (f := toAnn)]
    exact (PontryaginDual.map q).continuous
  have hfrom_cont : Continuous fromAnn := by
    refine continuous_of_continuousAt_one fromAnn ?_
    rw [ContinuousAt, map_one fromAnn]
    refine (pontryaginDual_nhds_one_hasBasis (G := G ⧸ H)).tendsto_right_iff.mpr ?_
    rintro ⟨K, V⟩ ⟨hK, hV⟩
    obtain ⟨C, hC, hKC⟩ := exists_isCompact_quotient_preimage H hK
    rw [IsInducing.subtypeVal.nhds_eq_comap (1 : lcaAnnihilator H)]
    refine mem_comap.mpr ⟨{ψ : PontryaginDual G | MapsTo ψ C V},
      pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (C, V)) ⟨hC, hV⟩, ?_⟩
    intro ψ hψ
    replace hψ : MapsTo (ψ.val : G → Circle) C V := by
      simpa [Set.mem_ofPred] using hψ
    show MapsTo (fromAnn ψ) K V
    intro k hk
    obtain ⟨x, hxC, rfl⟩ := hKC hk
    dsimp [fromAnn]
    rw [happly ψ x]
    exact hψ hxC
  let e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H :=
    { toFun := toAnn
      invFun := fromAnn
      left_inv := hinv_left
      right_inv := hinv_right
      map_mul' := toAnn.map_mul
      continuous_toFun := hto_cont
      continuous_invFun := hfrom_cont }
  refine ⟨e, fun χ x => ?_⟩
  dsimp [e, toAnn]
  rw [hq]

open scoped Pointwise in
/-- Some compact subgroup has a σ-compact annihilator. The subgroup is the
intersection of a decreasing sequence of compact identity neighborhoods. -/
private theorem exists_compact_subgroup_sigmaCompact_annihilator :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ SigmaCompactSpace (lcaAnnihilator K) := by
  let N := {U : Set G // U ∈ 𝓝 (1 : G) ∧ IsCompact U}
  have hNext (U : N) : ∃ V : N, (V : Set G)⁻¹ = V.val ∧ V.val * V.val ⊆ U.val := by
    obtain ⟨V, hV, hVc, hVi, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset U.property.1
    have hVU : V ⊆ U.val := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds hV))
    exact ⟨⟨V, hV, U.property.2.of_isClosed_subset hVc hVU⟩, hVi, hVV⟩
  choose next hInv hMul using hNext
  obtain ⟨U₀, hU₀, hU₀nhds⟩ := exists_compact_mem_nhds (1 : G)
  let seq : ℕ → N := Nat.rec ⟨U₀, hU₀nhds, hU₀⟩ fun _ U ↦ next U
  let U (n : ℕ) : Set G := (seq n).val
  have hOne (n : ℕ) : (1 : G) ∈ U n := mem_of_mem_nhds (seq n).property.1
  have hMulU (n : ℕ) : U (n + 1) * U (n + 1) ⊆ U n := hMul (seq n)
  have hAnti : Antitone U := antitone_nat_of_succ_le fun n x hx ↦
    hMulU n (mul_one x ▸ Set.mul_mem_mul hx (hOne (n + 1)))
  let K : Subgroup G :=
    { carrier := ⋂ n, U n
      one_mem' := mem_iInter.mpr hOne
      mul_mem' := fun hx hy ↦ mem_iInter.mpr fun n ↦ hMulU n
        (Set.mul_mem_mul (mem_iInter.mp hx (n + 1)) (mem_iInter.mp hy (n + 1)))
      inv_mem' := fun hx ↦ mem_iInter.mpr fun n ↦ hAnti (Nat.le_succ n) (by
          change _ ∈ (next (seq n)).val
          rw [← hInv (seq n)]
          simpa only [Set.mem_inv, inv_inv] using mem_iInter.mp hx (n + 1)) }
  have hUc (n) : IsCompact (U n) := (seq n).property.2
  have hUK : IsClosed (K : Set G) := isClosed_iInter fun n ↦ (hUc n).isClosed
  have hK : IsCompact (K : Set G) := (hUc 0).of_isClosed_subset hUK (iInter_subset U 0)
  refine ⟨K, hK, ?_⟩
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  let A := lcaAnnihilator K
  have hA : IsClosed (A : Set (PontryaginDual G)) :=
    isClosed_singleton.preimage
      (PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)).continuous
  let P (n : ℕ) : Set A := Subtype.val ⁻¹' {χ | MapsTo χ (U n) (Metric.closedBall 1 r)}
  refine ⟨⟨P, fun n ↦ (?_ : IsCompact (P n)), eq_univ_of_forall fun χ ↦ ?_⟩⟩
  · exact hA.isClosedEmbedding_subtypeVal.isCompact_preimage (hPolar _ (seq n).property.1)
  · let W := (χ.val : PontryaginDual G) ⁻¹' Metric.ball 1 r
    have hW : IsOpen W := Metric.isOpen_ball.preimage χ.val.continuous
    have hKW : (K : Set G) ⊆ W := fun x hx ↦
      show χ.val x ∈ Metric.ball 1 r by
        rw [(mem_lcaAnnihilator_iff K χ.val).mp χ.property ⟨x, hx⟩]
        exact Metric.mem_ball_self hr
    have hDisj : Disjoint (U 0 \ W) (⋂ n, U n) :=
      Set.disjoint_left.mpr fun x hx hxn ↦ hx.2 (hKW hxn)
    obtain ⟨n, hn⟩ := ((hUc 0).diff hW).elim_directed_family_closed U
      (fun n ↦ (hUc n).isClosed) hDisj hAnti.directed_ge
    refine mem_iUnion.mpr ⟨n, fun x hx ↦ Metric.ball_subset_closedBall ?_⟩
    by_contra hxW
    exact Set.disjoint_left.mp hn ⟨hAnti (Nat.zero_le n) hx, hxW⟩ hx

/-- Restriction to a closed subgroup is an open map on the dual groups. -/
private theorem isOpenMap_restrict_dual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsOpenMap (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)) := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨K, hK, hSigma⟩ := exists_compact_subgroup_sigmaCompact_annihilator (G := G)
  -- The restriction between the two open annihilators is surjective.
  let L := K.comap H.subtype
  have hL : IsCompact (L : Set H) := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let A := lcaAnnihilator K
  let B := lcaAnnihilator L
  let : SigmaCompactSpace A := hSigma
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hB : IsOpen (B : Set (PontryaginDual H)) :=
    (isOpen_discrete ({1} : Set (PontryaginDual L))).preimage
      (PontryaginDual.map (⟨L.subtype, continuous_subtype_val⟩ : L →ₜ* H)).continuous
  let : LocallyCompactSpace B := hB.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let g : A →* B := (f.toMonoidHom.comp A.subtype).codRestrict B fun χ ↦
    (mem_lcaAnnihilator_iff L _).mpr fun x ↦
      (mem_lcaAnnihilator_iff K χ.val).mp χ.property ⟨(x.val : G), x.property⟩
  have hg : Continuous g := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hgSurj : Function.Surjective g := by
    intro χ
    obtain ⟨ψ, hψ, hψK⟩ := exists_pontryaginDual_extension_trivial_on_compact H K hH hK χ.val
      (fun x hx ↦ (mem_lcaAnnihilator_iff L χ.val).mp χ.property ⟨x, hx⟩)
    exact ⟨⟨ψ, (mem_lcaAnnihilator_iff K ψ).mpr hψK⟩, Subtype.ext (PontryaginDual.ext hψ)⟩
  have hOpen := g.isOpenMap_of_sigmaCompact hgSurj hg
  have hImg (U : Set (PontryaginDual G)) (hU : U ∈ 𝓝 1) : f '' U ∈ 𝓝 1 := by
    have hU' : (Subtype.val : A → PontryaginDual G) ⁻¹' U ∈ 𝓝 (1 : A) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hV := hOpen.image_mem_nhds hU'
    rw [map_one g] at hV
    apply mem_of_superset (hB.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    exact ⟨χ.val, hχ, rfl⟩
  exact IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr fun U hU ↦
    mem_of_superset (hImg (f ⁻¹' U) hU) (image_preimage_subset f U)

/-- Paper: Lemma D.1.4.6(2), p. 758. Restriction of characters identifies the
dual modulo the annihilator with the dual of the subgroup. -/
theorem lcaDualQuotient_equiv_subgroupDual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ lcaAnnihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H), e (QuotientGroup.mk χ) x = χ x.val := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  have hSurj : Function.Surjective f := by
    intro χ
    obtain ⟨ψ, hψ, _⟩ := exists_pontryaginDual_extension_trivial_on_compact H ⊥ hH
      (by simp) χ (fun x hx ↦ by
        have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
        rw [hx1, map_one])
    exact ⟨ψ, PontryaginDual.ext hψ⟩
  have hOpen := isOpenMap_restrict_dual H hH
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hSurj
  have hq := QuotientGroup.isQuotientMap_mk (lcaAnnihilator H)
  have hf := hOpen.isQuotientMap f.continuous hSurj
  refine ⟨e.toContinuousMulEquiv fun _ ↦ ?_, fun _ _ ↦ rfl⟩
  exact (hq.isCoinducing.isOpen_preimage.symm.trans hf.isCoinducing.isOpen_preimage)

-- Retain the LCA assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(3), p. 758. The annihilator of a compact subgroup is open. -/
theorem isOpen_lcaAnnihilator (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (lcaAnnihilator H : Set (PontryaginDual G)) := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  let restrict := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  change IsOpen (restrict ⁻¹' ({1} : Set (PontryaginDual H)))
  exact (isOpen_discrete _).preimage restrict.continuous

/-- Paper: Lemma D.1.4.6(4), p. 758. The annihilator of an open subgroup is compact. -/
theorem isCompact_lcaAnnihilator (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (lcaAnnihilator H : Set (PontryaginDual G)) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator H (H.isClosed_of_isOpen hH)
  exact isCompact_iff_compactSpace.mpr e.toHomeomorph.compactSpace

/-- Paper: (D.1.4.9), p. 759. Evaluation at points of the original group is dense
in the dual of each open compactly generated subgroup of its Pontryagin dual.
Deviation: This isolates the density consequence of biduality and character extension. -/
theorem lca_dualSubgroup_eval_denseRange
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    DenseRange ((PontryaginDual.map
      (⟨H.val.subtype, continuous_subtype_val⟩ : H.val →ₜ* PontryaginDual G)).comp
        (pontryaginDual_eval (G := G))) := by
  sorry

/-- Paper: (D.1.4.9)–(D.1.4.10), p. 759. The evaluation map onto the dual of
an open compactly generated subgroup of the dual is an open quotient. Its
kernel is the compact annihilator of the subgroup. -/
theorem lca_dualSubgroup_quotient (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    ∃ γ : G →ₜ* PontryaginDual H.val,
      (∀ x (χ : H.val), γ x χ = χ.val x) ∧ IsOpenQuotientMap γ ∧
        γ.toMonoidHom.ker = lcaDualAnnihilator H.val ∧ IsCompact (γ.toMonoidHom.ker : Set G) := by
  let r := PontryaginDual.map (⟨H.val.subtype, continuous_subtype_val⟩ : H.val →ₜ* PontryaginDual G)
  let γ := r.comp (pontryaginDual_eval (G := G))
  have hEval (x : G) (χ : H.val) : γ x χ = χ.val x := rfl
  have hH := H.val.isClosed_of_isOpen H.property.1
  -- The kernel of restriction is dual to the discrete quotient by the open subgroup.
  let : DiscreteTopology (PontryaginDual G ⧸ H.val) := QuotientGroup.discreteTopology H.property.1
  obtain ⟨a, _⟩ := lcaQuotientDual_equiv_annihilator H.val hH
  have hCompact : IsCompact (lcaAnnihilator H.val : Set (PontryaginDual (PontryaginDual G))) :=
    isCompact_iff_compactSpace.mpr a.toHomeomorph.compactSpace
  obtain ⟨e, he⟩ := lcaDualQuotient_equiv_subgroupDual H.val hH
  have hr : (r : PontryaginDual (PontryaginDual G) → PontryaginDual H.val) =
      e ∘ QuotientGroup.mk := funext fun χ ↦ PontryaginDual.ext fun ψ ↦ (he χ ψ).symm
  have hClosedR : IsClosedMap r := hr ▸
    e.toHomeomorph.isClosedMap.comp (QuotientGroup.isClosedMap_coe hCompact)
  have hEmb := isClosedEmbedding_pontryaginDual_eval (G := G)
  have hClosed : IsClosedMap γ := hClosedR.comp hEmb.isClosedMap
  have hRange : IsClosed (range γ) := by
    rw [← image_univ]
    exact hClosed _ isClosed_univ
  have hSurj : Function.Surjective γ := by
    intro ψ
    change ψ ∈ range γ
    rw [← hRange.closure_eq]
    exact lca_dualSubgroup_eval_denseRange H ψ
  have hQ := hClosed.isQuotientMap γ.continuous hSurj
  let iso := (QuotientGroup.quotientKerEquivOfSurjective γ.toMonoidHom hSurj).toContinuousMulEquiv
    fun _ ↦ (QuotientGroup.isQuotientMap_mk γ.toMonoidHom.ker).isCoinducing.isOpen_preimage.symm.trans
      hQ.isCoinducing.isOpen_preimage
  refine ⟨γ, hEval, iso.toHomeomorph.isOpenQuotientMap.comp QuotientGroup.isOpenQuotientMap_mk,
    ?_, hEmb.isCompact_preimage hCompact⟩
  ext x
  rw [MonoidHom.mem_ker, mem_lcaDualAnnihilator_iff]
  exact ⟨fun h χ ↦ congrArg (fun ψ : PontryaginDual H.val ↦ ψ χ) h,
    fun h ↦ PontryaginDual.ext (fun χ ↦ h χ)⟩

-- TODO(paper-gap): p. 759 calls the quotient codomains Uᵢ small subgroups of G.
-- The kernels Kᵢ are the subgroups that become small, as on p. 760.

/-- Paper: After (D.1.4.10), p. 759. Every identity neighborhood contains
one of the compact annihilators.
Deviation: The small subgroups are the kernels Kᵢ, as stated on p. 760. -/
theorem exists_lcaDualAnnihilator_subset_nhds {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenCompactlyGeneratedSubgroups (PontryaginDual G),
      (lcaDualAnnihilator H.val : Set G) ⊆ U := by
  obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
  obtain ⟨H, hKH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
  refine ⟨H, fun x hx ↦ hTest x ?_⟩
  intro χ hχ
  have hχx := (mem_lcaDualAnnihilator_iff H.val x).mp hx ⟨χ, hKH hχ⟩
  change χ x = 1 at hχx
  rw [hχx, dist_self]
  norm_num

-- TODO(paper-gap): The component group of Aᵢⱼ can be infinite, as for G = ℤ with
-- Gⱼ = ℤ and Kᵢ = 1. Its component group is finitely generated by (D.1.4.12).

/-- Paper: (D.1.4.12), p. 759. A quotient in the inverse system of an open
compactly generated subgroup has an elementary presentation. -/
theorem lca_openSubgroup_quotient_elementary (J : OpenCompactlyGeneratedSubgroups G)
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    (_h : lcaDualAnnihilator H.val ≤ J.val) :
    Nonempty (ElementaryLCAPresentation (J.val ⧸ (lcaDualAnnihilator H.val).comap J.val.subtype)) := by
  let N := (lcaDualAnnihilator H.val).comap J.val.subtype
  let : LocallyCompactSpace J.val :=
    J.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyCompactSpace H.val :=
    H.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let ι : H.val →ₜ* PontryaginDual G :=
    ⟨H.val.subtype, continuous_subtype_val⟩
  let f : J.val →ₜ* PontryaginDual H.val :=
    (PontryaginDual.map ι).comp
      (pontryaginDual_eval.comp
        ⟨J.val.subtype, continuous_subtype_val⟩)
  have hker : f.toMonoidHom.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype,
      mem_lcaDualAnnihilator_iff]
    exact
      ⟨fun hx χ ↦ congrArg (fun ψ : PontryaginDual H.val ↦ ψ χ) hx,
        fun hx ↦ PontryaginDual.ext hx⟩
  have hN : IsClosed (N : Set J.val) := by
    rw [← hker]
    exact isClosed_eq f.continuous continuous_const
  let : T1Space (J.val ⧸ N) :=
    QuotientGroup.t1Space_iff.mpr hN
  refine lca_elementary_iff.mp
    ⟨isCompactlyGeneratedGroup_quotient J.property.2 N hN, ?_⟩
  let e : (J.val ⧸ N) →ₜ* PontryaginDual H.val :=
    ⟨QuotientGroup.lift N f.toMonoidHom hker.ge,
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
        f.continuous⟩
  have he : Function.Injective e :=
    (QuotientGroup.injective_lift_iff N f.toMonoidHom hker.ge).mpr
      hker.symm
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean
    (isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp
      H.property.2)
  have hW' : W ∈ 𝓝 (e 1) := by
    rwa [map_one]
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups
    (e.continuous.continuousAt.preimage_mem_nhds hW') ?_
  intro x hx
  apply he
  rw [map_one]
  exact hPow (e x) fun n ↦ map_pow e x n ▸ hx n

/-- Paper: Lemma D.1.4.7, p. 760. Each open compactly generated subgroup is the
inverse limit of its quotients by the annihilators it contains.
Deviation: We express the compatible families as the range in the product. At comparable
indices the coordinates are compatible exactly when they have a common representative.
Together with the open exhaustion (D.1.4.3), this realizes (D.1.4.16). -/
theorem lca_openSubgroup_inverseLimit (J : OpenCompactlyGeneratedSubgroups G) :
    let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
      lcaDualAnnihilator H.val ≤ J.val}
    let K : I → Subgroup J.val := fun H ↦ (lcaDualAnnihilator H.val.val).comap J.val.subtype
    let δ : J.val → ((H : I) → J.val ⧸ K H) := fun x _ ↦ QuotientGroup.mk x
    Nonempty I ∧ IsDirectedOrder I ∧
      IsEmbedding δ ∧ range δ = {a | ∀ (H H' : I), H ≤ H' →
      ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'} := by
  let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
    lcaDualAnnihilator H.val ≤ J.val}
  let K (H : I) : Subgroup J.val := (lcaDualAnnihilator H.val.val).comap J.val.subtype
  let δ : J.val →ₜ* ((H : I) → J.val ⧸ K H) :=
    { toFun := fun x H ↦ QuotientGroup.mk x
      map_one' := funext fun H ↦ QuotientGroup.mk_one (N := K H)
      map_mul' := fun x y ↦ funext fun H ↦ QuotientGroup.mk_mul (K H) x y
      continuous_toFun := continuous_pi fun H ↦ QuotientGroup.continuous_mk }
  change Nonempty I ∧ IsDirectedOrder I ∧ IsEmbedding δ ∧
    range δ = {a | ∀ (H H' : I), H ≤ H' → ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'}
  have hSmall {V : Set J.val} (hV : V ∈ 𝓝 (1 : J.val)) :
      ∃ H : I, (K H : Set J.val) ⊆ V := by
    obtain ⟨H, hH⟩ := exists_lcaDualAnnihilator_subset_nhds
      (J.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    refine ⟨⟨H, fun x hx ↦ ?_⟩, ?_⟩
    · obtain ⟨y, _, rfl⟩ := hH hx
      exact y.property
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hH (Subgroup.mem_comap.mp hx)
      exact (Subtype.ext hyx : y = x) ▸ hy
  let : Nonempty I := ⟨(hSmall Filter.univ_mem).choose⟩
  let : IsDirectedOrder (OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :=
    (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).1
  have hAnti : Antitone (fun H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) ↦
      lcaDualAnnihilator H.val) := by
    intro H H' h x hx
    exact (mem_lcaDualAnnihilator_iff H.val x).mpr fun χ ↦
      (mem_lcaDualAnnihilator_iff H'.val x).mp hx (Subgroup.inclusion h χ)
  let : IsDirectedOrder I := ⟨fun H H' ↦ by
    obtain ⟨L, hHL, hH'L⟩ := exists_ge_ge H.val H'.val
    exact ⟨⟨L, (hAnti hHL).trans H.property⟩, hHL, hH'L⟩⟩
  -- A neighborhood can be tested in a quotient whose kernel lies in a smaller neighborhood.
  have hInducing : IsInducing δ := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto δ (𝓝 1) (𝓝 (δ 1)) := δ.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨V, hV, h1V, hVV⟩ := exists_open_nhds_one_mul_subset hU
      obtain ⟨H, hH⟩ := hSmall (hV.mem_nhds h1V)
      let q : J.val → J.val ⧸ K H := QuotientGroup.mk
      have hqV : q '' V ∈ 𝓝 (1 : J.val ⧸ K H) :=
        (QuotientGroup.isOpenMap_coe (N := K H)).image_mem_nhds (hV.mem_nhds h1V)
      refine Filter.mem_comap.mpr ⟨(fun a ↦ a H) ⁻¹' (q '' V),
        (continuous_apply H).continuousAt.preimage_mem_nhds hqV, ?_⟩
      intro x hx
      obtain ⟨y, hy, hyx⟩ : q x ∈ q '' V := hx
      have hDiff : y⁻¹ * x ∈ K H := QuotientGroup.eq.mp hyx
      exact hVV ⟨y, hy, y⁻¹ * x, hH hDiff, mul_inv_cancel_left y x⟩
  refine ⟨inferInstance, inferInstance, ⟨hInducing, hInducing.injective⟩, ?_⟩
  ext a
  constructor
  · rintro ⟨x, rfl⟩ H H' _
    exact ⟨x, rfl, rfl⟩
  · intro ha
    change ∀ (H H' : I), H ≤ H' → ∃ x : J.val, δ x H = a H ∧ δ x H' = a H' at ha
    let F (H : I) : Set J.val := {x | δ x H = a H}
    have hNonempty (H : I) : (F H).Nonempty := by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (a H)
      exact ⟨x, hx⟩
    have hCompact (H : I) : IsCompact (K H : Set J.val) := by
      have hEval := (isClosedEmbedding_pontryaginDual_eval (G := G)).comp
        (J.val.isClosed_of_isOpen J.property.1).isClosedEmbedding_subtypeVal
      have hPreimage : (K H : Set J.val) =
          (pontryaginDual_eval ∘ (Subtype.val : J.val → G)) ⁻¹'
            (lcaAnnihilator H.val.val : Set (PontryaginDual (PontryaginDual G))) := by
        ext x
        exact (mem_lcaDualAnnihilator_iff H.val.val x.val).trans
          (mem_lcaAnnihilator_iff H.val.val (pontryaginDual_eval x.val)).symm
      rw [hPreimage]
      exact hEval.isCompact_preimage (isCompact_lcaAnnihilator H.val.val H.val.property.1)
    -- The fibers are translates of compact kernels and decrease along the index order.
    have hFiberCompact (H : I) : IsCompact (F H) := by
      obtain ⟨y, hy⟩ := hNonempty H
      have hFiber : F H = (fun z : J.val ↦ y * z) '' (K H : Set J.val) := by
        ext x
        constructor
        · intro hx
          exact ⟨y⁻¹ * x, QuotientGroup.eq.mp (hy.trans hx.symm), mul_inv_cancel_left y x⟩
        · rintro ⟨z, hz, rfl⟩
          change (QuotientGroup.mk (y * z) : J.val ⧸ K H) = a H
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
          exact hy
      rw [hFiber]
      exact (hCompact H).image (continuous_const.mul continuous_id)
    have hFiberAnti : Antitone F := by
      intro H H' h x hx
      obtain ⟨y, hy, hy'⟩ := ha H H' h
      have hDiff : x⁻¹ * y ∈ K H' := QuotientGroup.eq.mp (hx.trans hy'.symm)
      have hK : K H' ≤ K H := Subgroup.comap_mono (hAnti (show H.val ≤ H'.val from h))
      exact (QuotientGroup.eq.mpr (hK hDiff)).trans hy
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      F (directed_of_isDirected_le hFiberAnti) hNonempty hFiberCompact
      (fun H ↦ (hFiberCompact H).isClosed)
    exact ⟨x, funext (mem_iInter.mp hx)⟩

end Structure

section StructuralPairs

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.1(1), p. 760. A good subgroup is closed and has an
open compactly generated annihilator in the dual. -/
def IsBruhatGoodSubgroup (k : Subgroup G) : Prop :=
  IsClosed (k : Set G) ∧ IsOpen (lcaAnnihilator k : Set (PontryaginDual G)) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)

/-- Paper: Definition D.1.5.1(2), p. 760. A structural pair consists of an open
compactly generated subgroup and a good subgroup contained in it.
The order enlarges the first subgroup and shrinks the second. -/
abbrev BruhatStructuralPair (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {p : Subgroup G × (Subgroup G)ᵒᵈ //
    IsOpen (p.1 : Set G) ∧ IsCompactlyGeneratedGroup p.1 ∧
      IsBruhatGoodSubgroup (OrderDual.ofDual p.2) ∧ OrderDual.ofDual p.2 ≤ p.1}

/-- Paper: (D.1.5.2), p. 761. The quotient associated to a pair divides the
open subgroup by the good subgroup inside it. -/
abbrev BruhatStructuralPair.quotient (p : BruhatStructuralPair G) :=
  p.val.1 ⧸ (OrderDual.ofDual p.val.2).comap p.val.1.subtype

/-- Paper: (D.1.5.2), p. 761. The quotient sends a point to the identity if and
only if it belongs to the good subgroup. -/
theorem BruhatStructuralPair.quotient_mk_eq_one (p : BruhatStructuralPair G) (x : p.val.1) :
    (QuotientGroup.mk x : p.quotient) = 1 ↔ (x : G) ∈ OrderDual.ofDual p.val.2 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_comap, Subgroup.coe_subtype]

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] [LocallyCompactSpace G] in
/-- Translating a chart at the identity gives charts everywhere. -/
theorem isLocallyEuclidean_of_chart_at_one {k : ℕ}
    (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin k))) (he : (1 : G) ∈ e.source) :
    IsLocallyEuclidean G := by
  classical
  exact ⟨k, ⟨{
    atlas := Set.range fun g : G ↦
      ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    chartAt := fun g ↦ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    mem_chart_source := fun g ↦ by
      change g ∈ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).source ∩
        (Homeomorph.mulLeft g⁻¹) ⁻¹' e.source
      refine ⟨trivial, ?_⟩
      simpa using he
    chart_mem_atlas := fun g ↦ ⟨g, rfl⟩ }⟩⟩

omit [T2Space G] in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel makes
the group locally Euclidean. -/
theorem isLocallyEuclidean_of_torusHom_discreteKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  classical
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hf
  have hσ0 : σ 0 = 1 := by
    have e := hσmul 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    rw [add_zero] at e
    exact mul_eq_left.mp e.symm
  let B := Metric.ball (0 : L) ρ
  let τ : B → G := fun v ↦ σ v
  have hτc : Continuous τ := continuousOn_iff_continuous_domRestrict.mp hσc
  have hτinj : Function.Injective τ := by
    intro v w hvw
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    have hw : ‖(w : L)‖ < ρ := mem_ball_zero_iff.mp w.2
    apply Subtype.ext
    apply Subtype.ext
    refine circleExp_coord_injective (hv.le.trans hρ1) (hw.le.trans hρ1) fun i ↦ ?_
    rw [← hfσ v hv i, ← hfσ w hw i]
    exact congrArg (fun x ↦ f x i) hvw
  have hτopen : IsOpenMap τ := by
    intro S hS
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨v, hvS, rfl⟩
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS v hvS
    set δ' := min δ (ρ - ‖(v : L)‖) with hδ'def
    have hδ' : 0 < δ' := lt_min hδ (sub_pos.mpr hv)
    have hδ'1 : δ' ≤ δ := min_le_left _ _
    have hδ'2 : δ' ≤ ρ - ‖(v : L)‖ := min_le_right _ _
    have hnhds : (fun x ↦ σ v * x) '' (σ '' Metric.ball (0 : L) δ') ∈ 𝓝 (σ v) := by
      rw [← map_mul_left_nhds_one (σ v)]
      exact image_mem_map (hσnhds δ' hδ')
    apply Filter.mem_of_superset hnhds
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < δ' := mem_ball_zero_iff.mp hw
    have hvw : ‖(v : L) + w‖ < ρ :=
      (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨⟨(v : L) + w, mem_ball_zero_iff.mpr hvw⟩, hδS ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      simpa using hw'.trans_le hδ'1
    · exact (hσmul v w hv (by linarith [norm_nonneg (v : L)]) hvw)
  have hτ : IsOpenEmbedding τ := .of_continuous_injective_isOpenMap hτc hτinj hτopen
  let iso := (stdOrthonormalBasis ℝ L).repr
  let j : B → EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) := fun v ↦ iso v
  have hj : IsOpenEmbedding j :=
    iso.toHomeomorph.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have : Nonempty B := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let e := (hτ.toOpenPartialHomeomorph τ).symm.trans (hj.toOpenPartialHomeomorph j)
  have he : (1 : G) ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact ⟨⟨0, Metric.mem_ball_self hρ⟩, hσ0⟩
  exact isLocallyEuclidean_of_chart_at_one e he

/-- The dual of a locally Euclidean LCA group is compactly generated: the characters
from a torus homomorphism with discrete kernel, together with a compact polar
neighborhood, generate it. -/
theorem isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    IsCompactlyGeneratedGroup (PontryaginDual G) := by
  classical
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hG
  obtain ⟨t, f, hft, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hker
  obtain ⟨r, hr, hpolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  set n : ℕ := Fintype.card t with hn
  set ρ₀ := min (ρ / 4) (r / (n + 1)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by positivity) (by positivity)
  have hρ₀ρ : ρ₀ < ρ / 2 := (min_le_left _ _).trans_lt (by linarith)
  have hnρ₀ : (n : ℝ) * ρ₀ ≤ r := by
    have h1 : ρ₀ ≤ r / (n + 1) := min_le_right _ _
    have h2 : (n : ℝ) * (r / (n + 1)) ≤ r := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    calc (n : ℝ) * ρ₀ ≤ n * (r / (n + 1)) := by gcongr
      _ ≤ r := h2
  set K := σ '' Metric.closedBall (0 : L) ρ₀ with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ρ₀).image_of_continuousOn
      (hσc.mono (Metric.closedBall_subset_ball (hρ₀ρ.trans (half_lt_self hρ))))
  have hK : K ∈ 𝓝 (1 : G) :=
    mem_of_superset (hσnhds ρ₀ hρ₀) (image_mono Metric.ball_subset_closedBall)
  set P := {χ : PontryaginDual G | MapsTo χ K (Metric.closedBall 1 r)} with hPdef
  have hPc : IsCompact P := hpolar K hK
  have hP : P ∈ 𝓝 (1 : PontryaginDual G) := by
    have h1 := pontryaginDual_nhds_one_hasBasis.mem_of_mem
      (i := (K, Metric.ball (1 : Circle) r)) ⟨hKc, Metric.ball_mem_nhds 1 hr⟩
    exact mem_of_superset h1 fun χ hχ ↦ hχ.mono_right Metric.ball_subset_closedBall
  refine ⟨P ∪ (t : Set (PontryaginDual G)), mem_of_superset hP subset_union_left,
    hPc.union t.finite_toSet.isCompact, ?_⟩
  rw [eq_top_iff]
  intro ψ _
  have hψc : ContinuousAt (fun v : L ↦ ψ (σ v)) 0 :=
    ψ.continuous.continuousAt.comp (hσc.continuousAt (Metric.ball_mem_nhds 0 hρ))
  have hψadd : ∀ v w : L, ‖v‖ < ρ / 2 → ‖w‖ < ρ / 2 →
      ψ (σ (v + w)) = ψ (σ v) * ψ (σ w) := by
    intro v w hv hw
    rw [hσmul v w (by linarith) (by linarith) ((norm_add_le v w).trans_lt (by linarith)),
      map_mul]
  obtain ⟨l, hl⟩ := exists_linearMap_circleExp_of_localHom (half_pos hρ) _ hψc hψadd
  obtain ⟨m, hm⟩ := LinearMap.exists_extend l
  let a : t → ℝ := fun i ↦ m (EuclideanSpace.basisFun t ℝ i)
  let k : t → ℤ := fun i ↦ ⌊a i⌋
  set ψ' := ψ * ∏ i : t, (i.val) ^ (-k i) with hψ'def
  have hψ'P : ψ' ∈ P := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ ρ₀ := mem_closedBall_zero_iff.mp hv
    have hvρ : ‖v‖ < ρ / 2 := hv'.trans_lt hρ₀ρ
    let ev : PontryaginDual G →* Circle :=
      { toFun := fun χ ↦ χ (σ v), map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    have hmv : m (v : EuclideanSpace ℝ t) = ∑ i : t, (v : EuclideanSpace ℝ t) i * a i := by
      conv_lhs => rw [← (EuclideanSpace.basisFun t ℝ).sum_repr (v : EuclideanSpace ℝ t)]
      simp [map_sum, map_smul, a]
    have hlv : l v = m (v : EuclideanSpace ℝ t) := (LinearMap.congr_fun hm v).symm
    have hev : ψ' (σ v) = Circle.exp (∑ i : t, (a i - k i) * (v : EuclideanSpace ℝ t) i) := by
      change ev ψ' = _
      rw [hψ'def, map_mul, map_prod]
      change ψ (σ v) * ∏ i : t, ev (i.val ^ (-k i)) = _
      simp only [map_zpow]
      change ψ (σ v) * ∏ i : t, (i.val (σ v)) ^ (-k i) = _
      have hcoord : ∀ i : t, i.val (σ v) = Circle.exp ((v : EuclideanSpace ℝ t) i) := by
        intro i
        rw [← hft, hfσ v (hvρ.trans (half_lt_self hρ)) i]
      simp only [hcoord, ← Circle.exp_intCast_mul]
      rw [hl v hvρ, hlv, hmv, ← circleExp_sum, ← Circle.exp_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
    rw [hev, Metric.mem_closedBall]
    refine (dist_circleExp_one_le _).trans ?_
    calc |∑ i : t, (a i - k i) * (v : EuclideanSpace ℝ t) i|
        ≤ ∑ i : t, |(a i - k i) * (v : EuclideanSpace ℝ t) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : t, ‖v‖ := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          have h0 : 0 ≤ a i - k i := by
            have := Int.fract_nonneg (a i); rwa [Int.fract] at this
          have h1 : a i - k i < 1 := by
            have := Int.fract_lt_one (a i); rwa [Int.fract] at this
          have hvi : |(v : EuclideanSpace ℝ t) i| ≤ ‖v‖ := by
            simpa using PiLp.norm_apply_le (v : EuclideanSpace ℝ t) i
          rw [abs_of_nonneg h0]
          nlinarith [abs_nonneg ((v : EuclideanSpace ℝ t) i)]
      _ = n * ‖v‖ := by simp [hn]
      _ ≤ n * ρ₀ := by gcongr
      _ ≤ r := hnρ₀
  have hψ : ψ = ψ' * ∏ i : t, (i.val) ^ (k i) := by
    rw [hψ'def, mul_assoc, ← Finset.prod_mul_distrib]
    simp
  rw [hψ]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hψ'P))
    (Subgroup.prod_mem _ fun i _ ↦ Subgroup.zpow_mem _ (Subgroup.subset_closure (Or.inr i.2)) _)

/-- If the dual is compactly generated, the group has a neighborhood of the identity
containing no nontrivial cyclic subgroup, hence it is locally Euclidean. -/
theorem isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
    (h : IsCompactlyGeneratedGroup (PontryaginDual G)) : IsLocallyEuclidean G := by
  obtain ⟨K, -, hK, hGen⟩ := h
  have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W : Set G := (pontryaginDual_eval (G := G)) ⁻¹'
    {ψ | MapsTo ψ K (Circle.centeredArc (Real.pi / 2))}
  have hW : W ∈ 𝓝 (1 : G) := by
    have h1 := (pontryaginDual_nhds_one_hasBasis (G := PontryaginDual G)).mem_of_mem
      (i := (K, _)) ⟨hK, hC⟩
    have ht := (map_continuous (pontryaginDual_eval (G := G))).tendsto 1
    rw [map_one] at ht
    exact ht h1
  have hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
    intro x hx
    let evx : PontryaginDual G →* Circle :=
      { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    have hKx : K ⊆ evx.ker := by
      intro χ hχ
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      have := hx k hχ
      change χ (x ^ k) ∈ _ at this
      rwa [map_pow] at this
    have hTop : ⊤ ≤ evx.ker := hGen ▸ (Subgroup.closure_le _).mpr hKx
    apply (pontryaginDual_pairing_separates (G := G)).1
    funext χ
    exact (MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top χ))).trans (map_one χ).symm
  obtain ⟨t, f, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  exact isLocallyEuclidean_of_torusHom_discreteKernel f hker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Compact generation is invariant under topological group isomorphisms. -/
theorem isCompactlyGeneratedGroup_of_continuousMulEquiv {H : Type*} [CommGroup H]
    [TopologicalSpace H] (e : G ≃ₜ* H) (h : IsCompactlyGeneratedGroup G) :
    IsCompactlyGeneratedGroup H := by
  obtain ⟨U, hU, hUc, hGen⟩ := h
  refine ⟨e '' U, ?_, hUc.image e.continuous, ?_⟩
  · have := e.toHomeomorph.isOpenMap.image_mem_nhds hU
    rw [show e.toHomeomorph (1 : G) = 1 from map_one e] at this
    exact this
  · have := MonoidHom.map_closure (e.toMulEquiv.toMonoidHom) U
    rw [hGen, Subgroup.map_top_of_surjective _ e.surjective] at this
    exact this.symm

/-- Paper: Definition D.1.5.1(1), p. 760. The trivial subgroup is good exactly
when the group is locally Euclidean.
Deviation: Sanity check using the fact that its annihilator is the entire dual. -/
theorem isBruhatGoodSubgroup_bot_iff :
    IsBruhatGoodSubgroup (⊥ : Subgroup G) ↔ IsLocallyEuclidean G := by
  have htop : lcaAnnihilator (⊥ : Subgroup G) = ⊤ := by
    ext χ
    simp only [Subgroup.mem_top, iff_true]
    rw [mem_lcaAnnihilator_iff]
    intro x
    rw [Subgroup.mem_bot.mp x.2]
    exact map_one χ
  let eTop : (⊤ : Subgroup (PontryaginDual G)) ≃ₜ* PontryaginDual G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  unfold IsBruhatGoodSubgroup
  rw [htop]
  constructor
  · rintro ⟨-, -, hcg⟩
    exact isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
      (isCompactlyGeneratedGroup_of_continuousMulEquiv eTop hcg)
  · intro h
    refine ⟨by simp, by simp, ?_⟩
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv eTop.symm
      (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean h)

/-- Paper: Lemma D.1.4.6(4), p. 758. An open subgroup of the dual has a
compact annihilator in the original group. -/
private theorem isCompact_lcaDualAnnihilator (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) :
    IsCompact (lcaDualAnnihilator H : Set G) := by
  have hCompact := isCompact_lcaAnnihilator H hH
  convert (isClosedEmbedding_pontryaginDual_eval (G := G)).isCompact_preimage hCompact using 1
  ext x
  exact (mem_lcaDualAnnihilator_iff H x).trans
    (mem_lcaAnnihilator_iff H (pontryaginDual_eval x)).symm

/-- Paper: Definition D.1.5.1, p. 760. The intersection of two good
subgroups is good. Its annihilator is the join of their annihilators. -/
private theorem isBruhatGoodSubgroup_inf {K L : Subgroup G}
    (hK : IsBruhatGoodSubgroup K) (hL : IsBruhatGoodSubgroup L) :
    IsBruhatGoodSubgroup (K ⊓ L) := by
  have hLc := isCompact_lcaDualAnnihilator (lcaAnnihilator L) hL.2.1
  rw [lcaDualAnnihilator_annihilator L hL.1] at hLc
  have hAnti : Antitone (lcaAnnihilator (G := G)) := fun _ _ h χ hχ ↦
    (mem_lcaAnnihilator_iff _ χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff _ χ).mp hχ ⟨x, h x.property⟩
  have hAnn : lcaAnnihilator (K ⊓ L) = lcaAnnihilator K ⊔ lcaAnnihilator L := by
    apply le_antisymm _ (sup_le (hAnti inf_le_left) (hAnti inf_le_right))
    intro χ hχ
    let restrict : PontryaginDual K :=
      PontryaginDual.map ⟨K.subtype, continuous_subtype_val⟩ χ
    obtain ⟨ψ, hψ, hψL⟩ := exists_pontryaginDual_extension_trivial_on_compact K L hK.1 hLc
      restrict (fun x hx ↦ (mem_lcaAnnihilator_iff _ χ).mp hχ ⟨x, x.property, hx⟩)
    refine Subgroup.mem_sup.mpr ⟨χ * ψ⁻¹, ?_, ψ, (mem_lcaAnnihilator_iff L ψ).mpr hψL, ?_⟩
    · refine (mem_lcaAnnihilator_iff K _).mpr fun x ↦ ?_
      change χ x * (ψ x)⁻¹ = 1
      rw [hψ x]
      exact mul_inv_cancel _
    · exact inv_mul_cancel_right χ ψ
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator K, hK.2⟩
  let B : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator L, hL.2⟩
  obtain ⟨C, hAC, hBC⟩ := (openCompactlyGeneratedSubgroups_colimit
    (G := PontryaginDual G)).1.directed A B
  have hOpen : IsOpen (lcaAnnihilator (K ⊓ L) : Set (PontryaginDual G)) :=
    Subgroup.isOpen_mono (hAnti inf_le_left) hK.2.1
  refine ⟨hK.1.inter hL.1, hOpen, ?_⟩
  let J := lcaAnnihilator (K ⊓ L)
  have hJC : J ≤ C.val := by
    change lcaAnnihilator (K ⊓ L) ≤ C.val
    rw [hAnn]
    exact sup_le (show A.val ≤ C.val from hAC) (show B.val ≤ C.val from hBC)
  have hClosed : IsClosed (J.subgroupOf C.val : Set C.val) :=
    (J.isClosed_of_isOpen hOpen).preimage continuous_subtype_val
  let : LocallyCompactSpace C.val := C.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨U, hU, hUc, hGen⟩ := isCompactlyGeneratedGroup_closedSubgroup C.property.2
    (J.subgroupOf C.val) hClosed
  let e := Subgroup.subgroupOfEquivOfLe hJC
  have he : Continuous e := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e.symm := (continuous_subtype_val.subtype_mk _).subtype_mk _
  refine ⟨e '' U, ?_, hUc.image he, ?_⟩
  · have hEq : e '' U = e.symm ⁻¹' U := e.toEquiv.image_eq_preimage_symm U
    rw [hEq]
    exact he'.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
  · change Subgroup.closure (e.toMonoidHom '' U) = ⊤
    rw [← MonoidHom.map_closure e.toMonoidHom, hGen,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- Paper: Lemma D.1.4.6(1), p. 758. An open subgroup of the dual is recovered
from its annihilator in the original group.
Deviation: We isolate the open-subgroup case on the dual side. Once evaluation
is surjective onto the bidual, this follows by separating points in the discrete quotient. -/
theorem lcaAnnihilator_dualAnnihilator_of_open (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) :
    lcaAnnihilator (lcaDualAnnihilator H) = H := by
  sorry

/-- Paper: Lemma D.1.5.2, p. 760. Structural pairs form a nonempty directed order. -/
theorem bruhatStructuralPair_filtered :
    Nonempty (BruhatStructuralPair G) ∧ IsDirectedOrder (BruhatStructuralPair G) := by
  constructor
  · obtain ⟨A, _⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 1
    let K := lcaDualAnnihilator A.val
    have hKc : IsCompact (K : Set G) := isCompact_lcaDualAnnihilator A.val A.property.1
    have hAnn : lcaAnnihilator K = A.val :=
      lcaAnnihilator_dualAnnihilator_of_open A.val A.property.1
    have hK : IsBruhatGoodSubgroup K :=
      ⟨hKc.isClosed, hAnn.symm ▸ A.property⟩
    obtain ⟨H, hKH⟩ := exists_openCompactlyGeneratedSubgroup_contains hKc
    exact ⟨⟨(H.val, OrderDual.toDual K), H.property.1, H.property.2, hK, hKH⟩⟩
  · constructor
    intro p q
    obtain ⟨H, hp, hq⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
      ⟨p.val.1, p.property.1, p.property.2.1⟩ ⟨q.val.1, q.property.1, q.property.2.1⟩
    let K := OrderDual.ofDual p.val.2 ⊓ OrderDual.ofDual q.val.2
    have hK := isBruhatGoodSubgroup_inf p.property.2.2.1 q.property.2.2.1
    have hKH : K ≤ H.val := inf_le_left.trans (p.property.2.2.2.trans hp)
    have hKp : K ≤ OrderDual.ofDual p.val.2 := inf_le_left
    have hKq : K ≤ OrderDual.ofDual q.val.2 := inf_le_right
    exact ⟨⟨(H.val, OrderDual.toDual K), H.property.1, H.property.2, hK, hKH⟩, ⟨hp, hKp⟩, ⟨hq, hKq⟩⟩

/-- Paper: Lemma D.1.5.2(1), p. 761. The quotient attached to a structural pair
has an elementary presentation. -/
theorem BruhatStructuralPair.elementary (p : BruhatStructuralPair G) :
    Nonempty (ElementaryLCAPresentation p.quotient) := by
  let H := p.val.1
  let k := OrderDual.ofDual p.val.2
  let N := k.comap H.subtype
  obtain ⟨hH, hGen, ⟨hk, hkOpen, hkGen⟩, _⟩ := p.property
  let : LocallyCompactSpace H := hH.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let hN : IsClosed (N : Set H) := hk.preimage continuous_subtype_val
  refine lca_elementary_iff.mp ⟨isCompactlyGeneratedGroup_quotient hGen N hN, ?_⟩
  let A := lcaAnnihilator k
  let : LocallyCompactSpace A := hkOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  -- Evaluation on the annihilator has kernel exactly the good subgroup.
  let ι : A →ₜ* PontryaginDual G := ⟨A.subtype, continuous_subtype_val⟩
  let f : H →ₜ* PontryaginDual A :=
    (PontryaginDual.map ι).comp (pontryaginDual_eval.comp ⟨H.subtype, continuous_subtype_val⟩)
  have hker : f.toMonoidHom.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype,
      ← lcaDualAnnihilator_annihilator k hk, mem_lcaDualAnnihilator_iff]
    exact ⟨fun hx χ ↦ congrArg (fun ψ : PontryaginDual A ↦ ψ χ) hx,
      fun hx ↦ PontryaginDual.ext hx⟩
  let e : p.quotient →ₜ* PontryaginDual A :=
    ⟨QuotientGroup.lift N f.toMonoidHom hker.ge,
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr f.continuous⟩
  have he : Function.Injective e :=
    (QuotientGroup.injective_lift_iff N f.toMonoidHom hker.ge).mpr hker.symm
  -- A neighborhood with no nontrivial cyclic subgroups pulls back along this injection.
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean
    (isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp hkGen)
  have hW' : W ∈ 𝓝 (e 1) := by rwa [map_one]
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups
    (e.continuous.continuousAt.preimage_mem_nhds hW') ?_
  intro x hx
  apply he
  rw [map_one]
  exact hPow (e x) fun n ↦ map_pow e x n ▸ hx n

/-- Paper: Lemma D.1.5.2(2), p. 761. The two annihilators form a structural pair
in the dual, with the annihilator of the good subgroup as the open subgroup. -/
theorem BruhatStructuralPair.dual (p : BruhatStructuralPair G) :
    ∃ q : BruhatStructuralPair (PontryaginDual G),
      q.val.1 = lcaAnnihilator (OrderDual.ofDual p.val.2) ∧
      OrderDual.ofDual q.val.2 = lcaAnnihilator p.val.1 := by
  let H := p.val.1
  let k := OrderDual.ofDual p.val.2
  obtain ⟨hH, hGen, ⟨_, hkOpen, hkGen⟩, hkH⟩ := p.property
  have hCompact := isCompact_lcaAnnihilator H hH
  refine ⟨⟨(lcaAnnihilator k, OrderDual.toDual (lcaAnnihilator H)), hkOpen, hkGen,
    ⟨hCompact.isClosed, isOpen_lcaAnnihilator _ hCompact, ?_⟩, ?_⟩, rfl, rfl⟩
  · obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
    let A := lcaAnnihilator (lcaAnnihilator H)
    change IsCompactlyGeneratedGroup A
    have hMem (x : G) : e x ∈ A ↔ x ∈ H := by
      change e x ∈ lcaAnnihilator (lcaAnnihilator H) ↔ x ∈ H
      rw [mem_lcaAnnihilator_iff]
      simp_rw [he]
      rw [← mem_lcaDualAnnihilator_iff, lcaDualAnnihilator_annihilator H
        (H.isClosed_of_isOpen hH)]
    let f : H →* A := (e.toMonoidHom.comp H.subtype).codRestrict A
      fun x ↦ (hMem x).mpr x.property
    have hSurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := e.surjective (y : PontryaginDual (PontryaginDual G))
      exact ⟨⟨x, (hMem x).mp (hx.symm ▸ y.property)⟩, Subtype.ext hx⟩
    have hInducing : IsInducing f := IsInducing.subtypeVal.of_comp_iff.mp
      (e.toHomeomorph.isInducing.comp IsInducing.subtypeVal)
    have hOpen : IsOpenMap f := hInducing.isOpenMap (hSurj.range_eq ▸ isOpen_univ)
    obtain ⟨U, hU, hUc, hUgen⟩ := hGen
    refine ⟨f '' U, ?_, hUc.image hInducing.continuous, ?_⟩
    · simpa only [map_one] using hOpen.image_mem_nhds hU
    · rw [← MonoidHom.map_closure, hUgen, Subgroup.map_top_of_surjective f hSurj]
  · intro χ hχ
    exact (mem_lcaAnnihilator_iff k χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff H χ).mp hχ ⟨x, hkH x.property⟩

section Fourier

variable [MeasurableSpace G] [BorelSpace G]

local instance : MeasurableSpace (PontryaginDual G) := borel _

variable {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
variable {ν : Measure (PontryaginDual G)}

-- TODO(paper-gap): D.1.5.2(3) asserts pointwise converses for arbitrary integrable
-- representatives. On ℝ a function nonzero only at 0 has zero Fourier transform.

-- Retain the integrability hypothesis in the existing signature.
set_option linter.unusedVariables false in
/-- Paper: Lemma D.1.5.2(3), p. 761. Invariance under a subgroup forces the Fourier
transform to vanish off the annihilator.
Deviation: Stated in the forward direction because pointwise invariance can fail
for an integrable representative of an invariant class. -/
theorem lcaFourier_support_subset_annihilator (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (H : Subgroup G) (_hH : IsClosed (H : Set G)) (hinv : ∀ h : H, ∀ x, f (h.val * x) = f x) :
    Function.support (lcaFourier μ f) ⊆ (lcaAnnihilator H : Set (PontryaginDual G)) := by
  intro χ hχ
  refine (mem_lcaAnnihilator_iff H χ).mpr fun h ↦ ?_
  have htranslate : lcaFourier μ f χ = lcaFourier μ f χ * star (χ h.val : ℂ) := by
    unfold lcaFourier
    calc
      (∫ x, f x * star (χ x : ℂ) ∂μ) =
          ∫ x, f (h.val * x) * star (χ (h.val * x) : ℂ) ∂μ :=
        (integral_mul_left_eq_self (μ := μ) (fun x ↦ f x * star (χ x : ℂ)) h.val).symm
      _ = (∫ x, f x * star (χ x : ℂ) ∂μ) * star (χ h.val : ℂ) := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact .of_forall fun x ↦ by
          change f (h.val * x) * star (χ (h.val * x) : ℂ) =
            (f x * star (χ x : ℂ)) * star (χ h.val : ℂ)
          rw [hinv h x, map_mul, Circle.coe_mul, star_mul, mul_assoc]
  have hstar : star (χ h.val : ℂ) = 1 :=
    mul_left_cancel₀ (Function.mem_support.mp hχ) (htranslate.symm.trans (mul_one _).symm)
  exact Circle.coe_eq_one.mp (by simpa only [star_star, star_one] using congrArg star hstar)

-- Keep the existing hypotheses on integrability and regularity in the statement.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Lemma D.1.5.2(3), p. 761. Support in the open subgroup and invariance
under the good subgroup give the corresponding conditions for the dual pair.
Deviation: Stated in the forward direction because pointwise support and invariance
can fail after changing a representative on a null set. -/
theorem lcaFourier_structuralPair_imp (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (a : BruhatStructuralPair G) (hs : Function.support f ⊆ (a.val.1 : Set G))
    (hinv : ∀ h : ↥(OrderDual.ofDual a.val.2 : Subgroup G), ∀ x, f (h.val * x) = f x) :
    (∀ χ : lcaAnnihilator a.val.1, ∀ ψ : PontryaginDual G,
      lcaFourier μ f (χ.val * ψ) = lcaFourier μ f ψ) ∧
      Function.support (lcaFourier μ f) ⊆
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)) := by
  constructor
  · intro χ ψ
    unfold lcaFourier
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ a.val.1
    · have hχ : χ.val x = 1 := (mem_lcaAnnihilator_iff a.val.1 χ.val).mp χ.property ⟨x, hx⟩
      change f x * star ((χ.val x * ψ x : Circle) : ℂ) = f x * star (ψ x : ℂ)
      rw [hχ, one_mul]
    · have hfx : f x = 0 := Function.notMem_support.mp fun hx' ↦ hx (hs hx')
      simp only [hfx, zero_mul]
  · intro ψ hψ
    refine (mem_lcaAnnihilator_iff _ ψ).mpr fun h ↦ ?_
    have hmul : lcaFourier μ f ψ * star (ψ h.val : ℂ) = lcaFourier μ f ψ := by
      unfold lcaFourier
      rw [← integral_mul_const]
      calc
        _ = ∫ x, f (h.val * x) * star (ψ (h.val * x) : ℂ) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only [hinv h x, map_mul, Circle.coe_mul, star_mul, mul_assoc]
        _ = _ := integral_mul_left_eq_self (fun x ↦ f x * star (ψ x : ℂ)) h.val
    have hstar := (mul_eq_left₀ (Function.mem_support.mp hψ)).mp hmul
    apply Circle.coe_injective
    simpa only [Circle.coe_one, star_star, star_one] using congrArg star hstar

end Fourier
end StructuralPairs

section SchwartzBruhat

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.3(1), p. 762. A single good subgroup fixes the
function and its descent to each structural quotient with that subgroup is of class Cᵖ.
The derivatives are tested on the real and torus covers of the discrete fibers. -/
def IsBruhatContDiff (p : ℕ) (f : G → ℂ) : Prop :=
  ∃ k : Subgroup G, IsBruhatGoodSubgroup k ∧ (∀ h : k, ∀ x, f (h.val * x) = f x) ∧
    ∀ a : BruhatStructuralPair G, OrderDual.ofDual a.val.2 = k →
      ∃ f₀ : a.quotient → ℂ, (∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
        ∀ (e : ElementaryLCAPresentation a.quotient)
          (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor),
          ContDiff ℝ (p : ℕ∞) (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd
            (elementaryCover xt z b))))

/-- Paper: Definition D.1.5.3(1), p. 762. A function is smooth if it is of class Cᵖ
for every finite order p. -/
def IsBruhatSmooth (f : G → ℂ) : Prop :=
  ∀ p : ℕ, IsBruhatContDiff p f

/-- A good subgroup of the real line is trivial, since a compact subgroup cannot
contain all integer multiples of a nonzero real number. -/
private theorem isBruhatGoodSubgroup_real_eq_bot {k : Subgroup (Multiplicative ℝ)}
    (hk : IsBruhatGoodSubgroup k) : k = ⊥ := by
  have hc : IsCompact (k : Set (Multiplicative ℝ)) := by
    rw [← lcaDualAnnihilator_annihilator k hk.1]
    exact isCompact_lcaDualAnnihilator _ hk.2.1
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hc.image
    (show Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ) from continuous_id)).isBounded
  refine le_antisymm (fun x hx ↦ Subgroup.mem_bot.mpr ?_) bot_le
  by_contra h
  have hxpos : 0 < |x.toAdd| := abs_pos.mpr (show x.toAdd ≠ 0 from h)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |x.toAdd|)
  have hbound := hC (x ^ n).toAdd ⟨x ^ n, k.pow_mem hx n, rfl⟩
  change ‖n • x.toAdd‖ ≤ C at hbound
  rw [nsmul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hxpos).mp hn)

/-- The interval from `-1` to `1` is a compact generating neighborhood of the real line. -/
private theorem isCompactlyGeneratedGroup_real :
    IsCompactlyGeneratedGroup (Multiplicative ℝ) := by
  let U : Set (Multiplicative ℝ) := Multiplicative.toAdd ⁻¹' Icc (-1 : ℝ) 1
  refine ⟨U, ?_, ?_, eq_top_iff.mpr fun x _ ↦ ?_⟩
  · change Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ)
    exact Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)
  · change IsCompact (Icc (-1 : ℝ) 1)
    exact isCompact_Icc
  · obtain ⟨n, hn⟩ := exists_nat_gt (|x.toAdd|)
    have hnpos : (0 : ℝ) < n := (abs_nonneg _).trans_lt hn
    let y := Multiplicative.ofAdd (x.toAdd / n)
    have hy : y ∈ U := by
      change x.toAdd / n ∈ Icc (-1 : ℝ) 1
      apply abs_le.mp
      rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos, one_mul]
      exact hn.le
    have he : (y ^ n : Multiplicative ℝ) = x := by
      apply Multiplicative.toAdd.injective
      change n • (x.toAdd / n) = x.toAdd
      rw [nsmul_eq_mul]
      change (n : ℝ) * (x.toAdd / n) = x.toAdd
      rw [mul_comm, div_mul_cancel₀ _ hnpos.ne']
    exact he ▸ (Subgroup.closure U).pow_mem (Subgroup.subset_closure hy) n

/-- For a real structural pair with trivial good subgroup, the quotient identifies
with the real line by sending the class of each element to that element. -/
private theorem exists_bruhatQuotientEquiv_real (a : BruhatStructuralPair (Multiplicative ℝ))
    (hk : OrderDual.ofDual a.val.2 = ⊥) :
    ∃ q : a.quotient ≃ₜ* Multiplicative ℝ, ∀ x : a.val.1, q (QuotientGroup.mk x) = x.val := by
  letI : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
  have hTop : (a.val.1 : Set (Multiplicative ℝ)) = univ :=
    (show IsClopen (a.val.1 : Set (Multiplicative ℝ)) from
      ⟨a.val.1.isClosed_of_isOpen a.property.1, a.property.1⟩).eq_univ ⟨1, a.val.1.one_mem⟩
  let incl (x : Multiplicative ℝ) : a.val.1 := ⟨x, by
    change x ∈ (a.val.1 : Set (Multiplicative ℝ))
    rw [hTop]
    exact mem_univ x⟩
  let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  have hN : N = a.val.1.subtype.ker := by
    change (OrderDual.ofDual a.val.2).comap a.val.1.subtype = _
    rw [hk]
    rfl
  let e : a.quotient ≃* Multiplicative ℝ :=
    (QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype incl fun _ ↦ rfl)
  have he (x : a.val.1) : e (QuotientGroup.mk x) = x.val := rfl
  refine ⟨{ e with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (show Continuous (fun x : a.val.1 ↦ e (QuotientGroup.mk x)) by
        simp only [he]
        exact continuous_subtype_val)
    continuous_invFun := ?_ }, he⟩
  have hinv (x : Multiplicative ℝ) :
      e.symm x = QuotientGroup.mk (incl x) :=
    e.symm_apply_eq.mpr (he (incl x)).symm
  change Continuous (fun x ↦ e.symm x)
  simp only [hinv]
  exact QuotientGroup.continuous_mk.comp (continuous_id.subtype_mk _)

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, finite
orders of Bruhat differentiability agree with ordinary differentiability.
Deviation: Sanity check on the real group. -/
theorem isBruhatContDiff_real_iff (p : ℕ) (f : Multiplicative ℝ → ℂ) :
    IsBruhatContDiff p f ↔ ContDiff ℝ (p : ℕ∞) (f ∘ Multiplicative.ofAdd) := by
  let line := (EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  let chart : EuclideanSpace ℝ (Fin 1) ≃ₜ Multiplicative ℝ := line.toHomeomorph
  have hGood : IsBruhatGoodSubgroup (⊥ : Subgroup (Multiplicative ℝ)) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨1, ⟨chart.chartedSpace⟩⟩
  constructor
  · rintro ⟨k, hk, -, h⟩
    have hkbot := isBruhatGoodSubgroup_real_eq_bot hk
    subst k
    let topEquiv : (⊤ : Subgroup (Multiplicative ℝ)) ≃ₜ* Multiplicative ℝ :=
      { Subgroup.topEquiv with
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_id.subtype_mk _ }
    let a : BruhatStructuralPair (Multiplicative ℝ) :=
      ⟨(⊤, OrderDual.toDual ⊥), by simp,
        isCompactlyGeneratedGroup_of_continuousMulEquiv topEquiv.symm isCompactlyGeneratedGroup_real,
        hGood, bot_le⟩
    obtain ⟨q, hq⟩ := exists_bruhatQuotientEquiv_real a rfl
    -- Test differentiability on the presentation with only one real coordinate.
    let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) :=
      uniqueOfSubsingleton 0
    let m : Multiplicative (ElementaryLieGroup 1 0 0 PUnit) ≃ₜ* Multiplicative ℝ :=
      ContinuousMulEquiv.mk' ((Homeomorph.prodUnique _ _).trans line.toHomeomorph)
        (fun x y ↦ line.map_add x.toAdd.1 y.toAdd.1)
    let e : ElementaryLCAPresentation a.quotient := ⟨1, 0, 0, PUnit, q.trans m.symm⟩
    obtain ⟨g, hg, hs⟩ := h a rfl
    have hg' (y : a.quotient) : g y = f (q y) := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact (hg x).trans (congrArg f (hq x).symm)
    have hcomp := (hs e 0 0).comp
      (line.symm.contDiff.prodMk (contDiff_const (c := (0 : EuclideanSpace ℝ (Fin 0)))))
    convert hcomp using 1
    funext t
    simp only [Function.comp_apply, hg']
    change f (Multiplicative.ofAdd t) =
      f (q (q.symm (m (Multiplicative.ofAdd (elementaryCover (line.symm t, 0) 0 0)))))
    rw [q.apply_symm_apply]
    exact congrArg (f ∘ Multiplicative.ofAdd) (line.apply_symm_apply t).symm
  · intro hf
    refine ⟨⊥, hGood, ?_, fun a ha ↦ ?_⟩
    · intro h x
      rw [Subgroup.mem_bot.mp h.property, one_mul]
    obtain ⟨q, hq⟩ := exists_bruhatQuotientEquiv_real a ha
    refine ⟨f ∘ q, fun x ↦ congrArg f (hq x), ?_⟩
    intro e z b
    -- In the cover of each discrete fiber, the map to the real quotient is affine.
    let ψ := AddMonoidHom.toMultiplicative.symm
      ((e.equiv.symm.trans q).toMulEquiv.toMonoidHom)
    let cover : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim) →+
        ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
      { toFun := fun u ↦ elementaryCover u 0 0
        map_zero' := by simp [elementaryCover, Pi.zero_def]
        map_add' := fun u v ↦ by simp [elementaryCover, Pi.add_def] }
    have hcover : Continuous cover :=
      continuous_fst.prodMk ((continuous_pi fun i ↦
        (AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_apply i).comp (EuclideanSpace.equiv _ ℝ).continuous |>.comp
            continuous_snd)).prodMk
        continuous_const)
    have hψ : Continuous ψ := (e.equiv.symm.trans q).continuous
    have hlin := ((ψ.comp cover).toRealLinearMap (hψ.comp hcover)).contDiff
      (n := (p : ℕ∞))
    have hshift (u : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
        elementaryCover u z b = cover u + (0, 0, z, b) := by
      simp [cover, elementaryCover]
    simp_rw [hshift]
    exact hf.comp (show ContDiff ℝ (p : ℕ∞) (fun u ↦ ψ (cover u + (0, 0, z, b))) by
      simp only [map_add]
      exact hlin.add contDiff_const)

/-- The Pontryagin dual of the additive reals is connected. -/
private theorem connectedSpace_pontryaginDual_multiplicative_real :
    ConnectedSpace (PontryaginDual (Multiplicative ℝ)) := by
  obtain ⟨d, _⟩ := exists_realPontryaginDualEquiv
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  exact d.surjective.connectedSpace d.continuous

/-- A compact identity neighborhood generates a connected locally compact group. -/
private theorem realSmooth_compactlyGenerated (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [PreconnectedSpace G] :
    IsCompactlyGeneratedGroup G := by
  obtain ⟨K, hc, hK⟩ := exists_compact_mem_nhds (1 : G)
  have hOpen : IsOpen (Subgroup.closure K : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hK Subgroup.subset_closure)
  exact ⟨K, hK, hc, SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨Subgroup.closure K, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩

/-- The trivial subgroup is the only good subgroup of the additive reals. -/
private theorem isBruhatGoodSubgroup_real_bot :
    IsBruhatGoodSubgroup (⊥ : Subgroup (Multiplicative ℝ)) := by
  have := connectedSpace_pontryaginDual_multiplicative_real
  have hAnn : lcaAnnihilator (⊥ : Subgroup (Multiplicative ℝ)) = ⊤ := by
    refine eq_top_iff.mpr fun χ _ ↦ (mem_lcaAnnihilator_iff _ _).mpr fun x ↦ ?_
    rw [Subgroup.mem_bot.mp x.property, map_one]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Subgroup.coe_bot] using isClosed_singleton
  · rw [hAnn, Subgroup.coe_top]
    exact isOpen_univ
  · rw [hAnn]
    let : ConnectedSpace (⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :=
      (Subgroup.topEquiv.symm.surjective.connectedSpace (continuous_id.subtype_mk _))
    have hOpen : IsOpen ((⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :
        Set (PontryaginDual (Multiplicative ℝ))) := by simp
    let : LocallyCompactSpace (⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :=
      hOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
    exact realSmooth_compactlyGenerated _

private theorem isBruhatGoodSubgroup_real_iff (k : Subgroup (Multiplicative ℝ)) :
    IsBruhatGoodSubgroup k ↔ k = ⊥ := by
  constructor
  · intro hk
    have := connectedSpace_pontryaginDual_multiplicative_real
    let U : OpenSubgroup (PontryaginDual (Multiplicative ℝ)) :=
      ⟨lcaAnnihilator k, hk.2.1⟩
    have hann : lcaAnnihilator k = ⊤ :=
      SetLike.coe_injective (U.isClopen.eq_univ ⟨1, U.one_mem⟩)
    refine le_antisymm (fun x hx ↦ Subgroup.mem_bot.mpr ?_) bot_le
    apply (pontryaginDual_pairing_separates (G := Multiplicative ℝ)).1
    funext χ
    exact ((mem_lcaAnnihilator_iff k χ).mp (hann ▸ Subgroup.mem_top χ) ⟨x, hx⟩).trans
      (map_one χ).symm
  · rintro rfl
    exact isBruhatGoodSubgroup_real_bot

/-- A real structural pair has full open subgroup and trivial kernel, so its quotient
map identifies it with the real group. -/
private theorem realSmooth_pair_quotient (a : BruhatStructuralPair (Multiplicative ℝ)) :
    ∃ (h : ∀ x : Multiplicative ℝ, x ∈ a.val.1) (q : Multiplicative ℝ ≃ₜ* a.quotient),
      ∀ x, q x = QuotientGroup.mk ⟨x, h x⟩ := by
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have ha : a.val.1 = ⊤ := SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨a.val.1, a.property.1⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)
  have hk : OrderDual.ofDual a.val.2 = ⊥ :=
    (isBruhatGoodSubgroup_real_iff _).mp a.property.2.2.1
  have h (x : Multiplicative ℝ) : x ∈ a.val.1 := ha ▸ Subgroup.mem_top x
  let i : Multiplicative ℝ ≃ₜ* a.val.1 :=
    { toMulEquiv :=
        { toFun := fun x ↦ ⟨x, h x⟩
          invFun := Subtype.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_mul' := fun _ _ ↦ rfl }
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let k := OrderDual.ofDual a.val.2
  let p := (QuotientGroup.mk' (k.comap a.val.1.subtype)).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hpInj : Function.Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact hk ▸ (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := MulEquiv.ofBijective p ⟨hpInj, hp.surjective⟩
  exact ⟨h, q.toContinuousMulEquiv (fun _ ↦ hp.isQuotientMap.isOpen_preimage), fun _ ↦ rfl⟩

/-- In any elementary presentation of a real structural quotient, the torus and
discrete factors are trivial and the real coordinate is a linear equivalence. -/
private theorem realSmooth_coordinates (a : BruhatStructuralPair (Multiplicative ℝ))
    (e : ElementaryLCAPresentation a.quotient) :
    e.torusDim = 0 ∧ e.latticeRank = 0 ∧ Subsingleton e.finiteFactor ∧
      ∃ (h : ∀ x : Multiplicative ℝ, x ∈ a.val.1)
        (L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin e.realDim)),
        ∀ x : ℝ, (e.equiv (QuotientGroup.mk ⟨Multiplicative.ofAdd x, h _⟩)).toAdd =
          (L x, 0, 0, 0) := by
  obtain ⟨h, q, hq⟩ := realSmooth_pair_quotient a
  let E := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let Z := Fin e.latticeRank → ℤ
  let F := e.finiteFactor
  let P := ElementaryLieGroup e.realDim e.torusDim e.latticeRank F
  let w := q.trans e.equiv
  let W : ℝ ≃+ P := MulEquiv.toAdditive w.toMulEquiv
  have hW : Continuous W := w.continuous
  have hWi : Continuous W.symm := w.symm.continuous
  let : ConnectedSpace P := W.surjective.connectedSpace hW
  let : ConnectedSpace Z :=
    (show Function.Surjective (fun p : P ↦ p.2.2.1) from fun z ↦ ⟨(0, 0, z, 0), rfl⟩).connectedSpace
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
  let : ConnectedSpace F :=
    (show Function.Surjective (fun p : P ↦ p.2.2.2) from fun b ↦ ⟨(0, 0, 0, b), rfl⟩).connectedSpace
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hZ : Subsingleton Z := subsingleton_of_preconnected_totallyDisconnected
  have hF : Subsingleton F := subsingleton_of_preconnected_totallyDisconnected
  have hz : e.latticeRank = 0 := by
    by_contra hn
    let i : Fin e.latticeRank := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hi := congrFun (hZ.elim (0 : Z) 1) i
    exact zero_ne_one hi
  let tor : T →+ ℝ :=
    { toFun := fun t ↦ W.symm (0, t, 0, 0)
      map_zero' := by
        let p : P := (0, 0, 0, 0)
        have he : p + p = p :=
          Prod.ext (zero_add _) (Prod.ext (zero_add _) (Prod.ext (zero_add _) (hF.elim _ _)))
        have hzero := W.symm.map_add p p
        rw [he] at hzero
        change W.symm p = 0
        linarith
      map_add' := fun t u ↦ by
        rw [← W.symm.map_add]
        apply congrArg W.symm
        exact Prod.ext (zero_add _).symm
          (Prod.ext rfl (Prod.ext (zero_add _).symm (hF.elim _ _))) }
  have htor : Continuous tor :=
    hWi.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  obtain ⟨C, hC⟩ := (isCompact_univ.image htor).isBounded.exists_norm_le
  have htor0 (t : T) : tor t = 0 := by
    by_contra ht
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖tor t‖)
    have hb := hC (tor (n • t)) (mem_image_of_mem tor (mem_univ (n • t)))
    rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hb
    exact (not_lt_of_ge hb) ((div_lt_iff₀ (norm_pos_iff.mpr ht)).mp hn)
  have hT : Subsingleton T := ⟨fun t u ↦ by
    have hu : tor t = tor u := (htor0 t).trans (htor0 u).symm
    exact congrArg (fun p : P ↦ p.2.1) (W.symm.injective hu)⟩
  have ht : e.torusDim = 0 := by
    by_contra hn
    let i : Fin e.torusDim := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hi := congrFun (hT.elim (fun _ ↦ ((1 / 2 : ℝ) : AddCircle (1 : ℝ))) 0) i
    exact (show (1 / 2 : ℝ) ≠ 0 by norm_num)
      ((AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp hi)
  let I : P ≃+ E :=
    { toFun := Prod.fst
      invFun := fun x ↦ (x, 0, 0, 0)
      left_inv := fun p ↦ Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let L := (W.trans I).toRealLinearEquiv (continuous_fst.comp hW)
    (hWi.comp (continuous_id.prodMk continuous_const))
  refine ⟨ht, hz, hF, h, L, fun x ↦ ?_⟩
  rw [← hq]
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- The full real group with trivial kernel has a one-dimensional elementary presentation. -/
private theorem realSmooth_stage :
    ∃ a : BruhatStructuralPair (Multiplicative ℝ), Nonempty (ElementaryLCAPresentation a.quotient) := by
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have hTop : IsOpen ((⊤ : Subgroup (Multiplicative ℝ)) : Set (Multiplicative ℝ)) := by simp
  let : ConnectedSpace (⊤ : Subgroup (Multiplicative ℝ)) :=
    Subgroup.topEquiv.symm.surjective.connectedSpace (continuous_id.subtype_mk _)
  let : LocallyCompactSpace (⊤ : Subgroup (Multiplicative ℝ)) :=
    hTop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let a : BruhatStructuralPair (Multiplicative ℝ) := ⟨(⊤, OrderDual.toDual ⊥),
    hTop, realSmooth_compactlyGenerated _, isBruhatGoodSubgroup_real_bot, bot_le⟩
  obtain ⟨_, q, _⟩ := realSmooth_pair_quotient a
  let E := EuclideanSpace ℝ (Fin 1)
  let L : ℝ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, finrank_euclideanSpace])
  let B := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × Fin 1
  let : Unique B := uniqueOfSubsingleton 0
  let M : ℝ ≃+ ElementaryLieGroup 1 0 0 (Fin 1) :=
    L.toLinearEquiv.toAddEquiv.trans (AddEquiv.prodUnique (M := E) (N := B)).symm
  let M' : Multiplicative ℝ ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 (Fin 1)) :=
    ⟨AddEquiv.toMultiplicative M,
      show Continuous (fun x : ℝ ↦ (L x, (default : B))) from
        L.continuous.prodMk continuous_const,
      show Continuous (fun x : E × B ↦ L.symm x.1) from
        L.symm.continuous.comp continuous_fst⟩
  exact ⟨a, ⟨({ realDim := 1, torusDim := 0, latticeRank := 0, finiteFactor := Fin 1, equiv := q.symm.trans M' } : ElementaryLCAPresentation a.quotient)⟩⟩

/-- Along any elementary chart of a real structural quotient, the descended function
is the original function precomposed with a linear projection. -/
private theorem realSmooth_pullback_eq (f : Multiplicative ℝ → ℂ)
    (a : BruhatStructuralPair (Multiplicative ℝ)) (e : ElementaryLCAPresentation a.quotient)
    (f₀ : a.quotient → ℂ) (hf₀ : ∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val)
    (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
    ∃ L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin e.realDim),
      (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z b)))) =
        fun xt ↦ (f ∘ Multiplicative.ofAdd) (L.symm xt.1) := by
  obtain ⟨ht, hz, hF, hmem, L, hL⟩ := realSmooth_coordinates a e
  have : IsEmpty (Fin e.torusDim) := by rw [ht]; exact Fin.isEmpty
  have : IsEmpty (Fin e.latticeRank) := by rw [hz]; exact Fin.isEmpty
  have : Subsingleton e.finiteFactor := hF
  refine ⟨L, funext fun xt ↦ ?_⟩
  have htail : elementaryCover xt z b = (xt.1, 0, 0, 0) := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  rw [htail]
  have hpoint := hL (L.symm xt.1)
  rw [L.apply_symm_apply] at hpoint
  have hmul := congrArg Multiplicative.ofAdd hpoint
  simp only [ofAdd_toAdd] at hmul
  rw [← hmul, e.equiv.symm_apply_apply, hf₀]
  rfl

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, Bruhat
smoothness agrees with ordinary smoothness.
Deviation: Sanity check on the real group. -/
theorem isBruhatSmooth_real_iff (f : Multiplicative ℝ → ℂ) :
    IsBruhatSmooth f ↔ ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) := by
  constructor
  · intro hf
    rw [contDiff_infty]
    intro n
    rcases hf n with ⟨k, hk, -, hpair⟩
    have hk0 : k = ⊥ := (isBruhatGoodSubgroup_real_iff k).mp hk
    obtain ⟨a, ⟨e⟩⟩ := realSmooth_stage
    have ha : OrderDual.ofDual a.val.2 = k := by
      rw [hk0]
      exact (isBruhatGoodSubgroup_real_iff _).mp a.property.2.2.1
    obtain ⟨f₀, hf₀, hcover⟩ := hpair a ha
    obtain ⟨L, hEq⟩ := realSmooth_pullback_eq f a e f₀ hf₀ 0 0
    have hfun : f ∘ Multiplicative.ofAdd =
        (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt 0 0)))) ∘
          fun x ↦ (L x, (0 : EuclideanSpace ℝ (Fin e.torusDim))) := by
      funext x
      rw [Function.comp_apply, hEq]
      simp [L.symm_apply_apply]
    rw [hfun]
    exact (hcover e 0 0).comp (L.contDiff.prodMk contDiff_const)
  · intro hf n
    refine ⟨⊥, isBruhatGoodSubgroup_real_bot, ?_, ?_⟩
    · intro h x
      rw [Subgroup.mem_bot.mp h.property, one_mul]
    · intro a _ha
      obtain ⟨hmem, q, hquot⟩ := realSmooth_pair_quotient a
      let f₀ : a.quotient → ℂ := fun y ↦ f (q.symm y)
      have hf₀ : ∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val := by
        intro x
        change f (q.symm (QuotientGroup.mk x)) = f x.val
        apply congrArg f
        apply q.injective
        rw [q.apply_symm_apply, hquot x.val]
      refine ⟨f₀, hf₀, fun e z b ↦ ?_⟩
      obtain ⟨L, hEq⟩ := realSmooth_pullback_eq f a e f₀ hf₀ z b
      rw [hEq]
      exact (hf.of_le (by simp)).comp (L.symm.contDiff.comp contDiff_fst)

variable [hTop : IsTopologicalGroup G] [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

/-- An LCA group has a good subgroup. The annihilator of an open compactly generated
subgroup of the dual is compact. Evaluation gives a continuous injection from the quotient
into a group with no small subgroups, so the quotient is locally Euclidean. -/
private theorem exists_bruhatGoodSubgroup : ∃ k : Subgroup G, IsBruhatGoodSubgroup k := by
  obtain ⟨H, _⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 1
  let k := lcaDualAnnihilator H.val
  have hk := isCompact_lcaDualAnnihilator H.val H.property.1
  refine ⟨k, hk.isClosed, isOpen_lcaAnnihilator k hk, ?_⟩
  let : T1Space (G ⧸ k) := QuotientGroup.t1Space_iff.mpr hk.isClosed
  let r := PontryaginDual.map (⟨H.val.subtype, continuous_subtype_val⟩ : H.val →ₜ* PontryaginDual G)
  let γ := r.comp (pontryaginDual_eval (G := G))
  have hker : γ.toMonoidHom.ker = k := by
    ext x
    rw [MonoidHom.mem_ker, mem_lcaDualAnnihilator_iff]
    exact ⟨fun h χ ↦ congrArg (fun ψ : PontryaginDual H.val ↦ ψ χ) h,
      fun h ↦ PontryaginDual.ext h⟩
  let f : G ⧸ k →ₜ* PontryaginDual H.val :=
    ⟨QuotientGroup.lift k γ.toMonoidHom hker.ge,
      (QuotientGroup.isQuotientMap_mk k).continuous_iff.mpr γ.continuous⟩
  have hf : Function.Injective f :=
    (QuotientGroup.injective_lift_iff k γ.toMonoidHom hker.ge).mpr hker.symm
  obtain ⟨C, _, hC, hGen⟩ := H.property.2
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W : Set (PontryaginDual H.val) := {ψ | MapsTo ψ C (Circle.centeredArc (Real.pi / 2))}
  have hW : W ∈ 𝓝 (1 : PontryaginDual H.val) :=
    pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (C, _)) ⟨hC, hArc⟩
  have hW' : W ∈ 𝓝 (f 1) := by rwa [map_one]
  have hPre : f ⁻¹' W ∈ 𝓝 (1 : G ⧸ k) :=
    f.continuous.continuousAt.preimage_mem_nhds hW'
  have hPow (x : G ⧸ k) (hx : ∀ n : ℕ, x ^ n ∈ f ⁻¹' W) : x = 1 := by
    have hCker : C ⊆ (f x).toMonoidHom.ker := by
      intro χ hχ
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro n _
      have hn : f (x ^ n) χ ∈ Circle.centeredArc (Real.pi / 2) := hx n hχ
      rw [map_pow] at hn
      exact (ContinuousMonoidHom.pow_apply (f x) n χ) ▸ hn
    have hTop : ⊤ ≤ (f x).toMonoidHom.ker := hGen ▸ (Subgroup.closure_le _).mpr hCker
    apply hf
    rw [map_one]
    exact PontryaginDual.ext fun χ ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top χ))
  obtain ⟨_, φ, _, hφ⟩ := exists_torusHom_of_noSmallCyclicSubgroups hPre hPow
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator k hk.isClosed
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv e
    (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean
      (isLocallyEuclidean_of_torusHom_discreteKernel φ hφ))

/-- Paper: Definition D.1.5.3(1), p. 762. The zero function is of class Cᵖ. -/
theorem isBruhatContDiff_zero (p : ℕ) : IsBruhatContDiff p (0 : G → ℂ) := by
  obtain ⟨k, hk⟩ := exists_bruhatGoodSubgroup (G := G)
  refine ⟨k, hk, fun _ _ ↦ rfl, fun a _ ↦ ⟨(0 : a.quotient → ℂ), fun _ ↦ rfl, ?_⟩⟩
  intro e z b
  exact contDiff_const

/-- The target of an open continuous map from a real vector group has an elementary
presentation if it is compactly generated. -/
private theorem elementaryPresentation_of_open_vector_map {E B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (f : E →+ Additive B) (hf : Continuous f) (hopen : IsOpenMap f)
    (hB : IsCompactlyGeneratedGroup B) : Nonempty (ElementaryLCAPresentation B) := by
  let : T2Space (Additive B) := ‹T2Space B›
  obtain ⟨m, n, ⟨e⟩⟩ := exists_real_torus_equiv_of_open_vector_range f hf hopen
  have hRange : IsOpen (f.range : Set (Additive B)) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hopen _ isOpen_univ
  let : DivisibleBy f.range ℤ := divisibleByOfSMulRightSurj f.range ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f.rangeRestrict ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f.rangeRestrict ((z : ℝ)⁻¹ • x) = f.rangeRestrict x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open f.range hRange
  let D := Additive B ⧸ f.range
  let : DiscreteTopology D := QuotientAddGroup.discreteTopology hRange
  let product := split.toAddEquiv.trans (AddEquiv.prodCongr e.toAddEquiv (AddEquiv.refl D))
  let assoc := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ)) D
  exact elementaryPresentation_of_compactlyGenerated hB {
    AddEquiv.toMultiplicativeRight (product.trans AddEquiv.prodAssoc) with
    continuous_toFun := assoc.continuous.comp
      ((e.continuous_toFun.prodMap continuous_id).comp split.continuous_toFun)
    continuous_invFun := split.continuous_invFun.comp
      ((e.continuous_invFun.prodMap continuous_id).comp assoc.symm.continuous) }


/-- The cover of the identity component of an elementary group as a homomorphism. -/
private def elementaryCoverZeroHom {m n r : ℕ} {F : Type*} [AddCommGroup F] :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ElementaryLieGroup m n r F where
  toFun := fun xt ↦ elementaryCover xt 0 0
  map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
  map_add' x y := Prod.ext rfl
    (Prod.ext (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm)

/-- The cover of the identity component is continuous and open in the elementary group. -/
private theorem elementaryCoverZeroHom_continuous_isOpenMap {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] :
    let c := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
    Continuous c ∧ IsOpenMap c := by
  refine ⟨continuous_fst.prodMk
    ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const), ?_⟩
  let q : (Fin n → ℝ) → (Fin n → AddCircle (1 : ℝ)) := fun u i ↦ (u i : AddCircle (1 : ℝ))
  have hq : IsOpenMap q := IsOpenMap.piMap
    (fun _ ↦ (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AddSubgroup.zmultiples (1 : ℝ))).isOpenMap)
    (Eventually.of_forall fun _ ↦ QuotientAddGroup.mk_surjective)
  have hzero : IsOpenMap (fun _ : Unit ↦ (0 : (Fin r → ℤ) × F)) := fun _ _ ↦ isOpen_discrete _
  have he : IsOpenMap (fun u : EuclideanSpace ℝ (Fin n) ↦
      ((u, ()) : EuclideanSpace ℝ (Fin n) × Unit)) :=
    (Homeomorph.prodUnique _ _).symm.isOpenMap
  exact IsOpenMap.id.prodMap
    (((hq.comp (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isOpenMap).prodMap hzero).comp he)

/-- On a covered discrete fiber, a continuous homomorphism of elementary groups
is represented in the target cover by a continuous affine map. -/
private theorem contDiff_comp_elementaryHom {m n r m' n' r' : ℕ} {F F' : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    {p : ℕ∞} (a : ElementaryLieGroup m n r F →+ ElementaryLieGroup m' n' r' F')
    (ha : Continuous a) {f : ElementaryLieGroup m' n' r' F' → ℂ}
    (hf : ∀ z b, ContDiff ℝ p (fun u ↦ f (elementaryCover u z b)))
    (z : Fin r → ℤ) (b : F) :
    ContDiff ℝ p (fun u ↦ f (a (elementaryCover u z b))) := by
  let cover := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  let A := a.comp cover
  have hA : Continuous A := ha.comp elementaryCoverZeroHom_continuous_isOpenMap.1
  let R := (AddMonoidHom.fst _ _).comp A
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp A)
  choose l hl using fun i : Fin n' ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hA.snd.fst)
  let L := (R.toRealLinearMap hA.fst).prod
    ((EuclideanSpace.equiv (Fin n') ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi l))
  let c := a (elementaryCover 0 z b)
  obtain ⟨t, ht⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  have hLift (u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
      elementaryCover (L u + (c.1, t)) c.2.2.1 c.2.2.2 = a (elementaryCover u z b) := by
    have hshift : cover u + elementaryCover 0 z b = elementaryCover u z b := by
      simp [cover, elementaryCoverZeroHom, elementaryCover, Pi.zero_def]
    rw [← hshift, map_add]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      have hti := congrArg (fun y : ElementaryLieGroup m' n' r' F' ↦ y.2.1 i) ht
      change ((l i u + t i : ℝ) : AddCircle (1 : ℝ)) = (A u).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hl i u]
      exact congrArg ((A u).2.1 i + ·) hti
    · have h := hA.snd.snd.isConst_of_preconnectedSpace u 0
      rw [map_zero A] at h
      change c.2.2 = (A u).2.2 + c.2.2
      rw [h]
      exact (zero_add _).symm
  simp_rw [← hLift]
  exact (hf c.2.2.1 c.2.2.2).comp (L.contDiff.add (contDiff_const (c := (c.1, t))))

/-- Smooth descents for a good subgroup pull back to structural quotients by
smaller good subgroups. -/
private theorem bruhatContDiff_descend_of_le {p : ℕ} {f : G → ℂ}
    {k : Subgroup G} (hk : IsBruhatGoodSubgroup k)
    (hdesc : ∀ b : BruhatStructuralPair G, OrderDual.ofDual b.val.2 = k →
      ∃ f₀ : b.quotient → ℂ, (∀ x : b.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
        ∀ (e : ElementaryLCAPresentation b.quotient)
          (z : Fin e.latticeRank → ℤ) (d : e.finiteFactor),
          ContDiff ℝ (p : ℕ∞) (fun u ↦ f₀ (e.equiv.symm
            (Multiplicative.ofAdd (elementaryCover u z d)))))
    (a : BruhatStructuralPair G) (hak : OrderDual.ofDual a.val.2 ≤ k) :
    ∃ f₀ : a.quotient → ℂ, (∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
      ∀ (e : ElementaryLCAPresentation a.quotient)
        (z : Fin e.latticeRank → ℤ) (d : e.finiteFactor),
        ContDiff ℝ (p : ℕ∞) (fun u ↦ f₀ (e.equiv.symm
          (Multiplicative.ofAdd (elementaryCover u z d)))) := by
  have hkc := isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  rw [lcaDualAnnihilator_annihilator k hk.1] at hkc
  obtain ⟨J, hkJ⟩ := exists_openCompactlyGeneratedSubgroup_contains hkc
  obtain ⟨H, haH, hJH⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
    ⟨a.val.1, a.property.1, a.property.2.1⟩ J
  let b : BruhatStructuralPair G :=
    ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, hkJ.trans hJH⟩
  let i := Subgroup.inclusion (show a.val.1 ≤ H.val from haH)
  let j : a.quotient →* b.quotient := QuotientGroup.map _ _ i (fun _ hx ↦ hak hx)
  have hi : Continuous i := (continuous_subtype_val : Continuous ((↑) : a.val.1 → G)).subtype_mk _
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hi)
  have hio : IsOpenMap i := a.property.1.isOpenMap_inclusion haH
  have hjo : IsOpenMap j := by
    intro U hU
    let qa : a.val.1 → a.quotient := QuotientGroup.mk
    let qb : b.val.1 → b.quotient := QuotientGroup.mk
    have hEq : j '' U = (qb ∘ i) '' (qa ⁻¹' U) := by
      rw [show qb ∘ i = j ∘ qa from rfl, Set.image_comp,
        Set.image_preimage_eq _ QuotientGroup.mk_surjective]
    rw [hEq]
    exact (QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp hio) _
      (hU.preimage QuotientGroup.continuous_mk)
  obtain ⟨f₀, hf₀, hSmooth⟩ := hdesc b rfl
  refine ⟨f₀ ∘ j, fun x ↦ hf₀ (i x), ?_⟩
  intro e z d
  -- The image of the identity-component cover is open in the larger quotient.
  let c := elementaryCoverZeroHom (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor)
  let j' := MonoidHom.toAdditiveRight (j.comp e.equiv.symm.toMulEquiv.toMonoidHom)
  have hContinuous : Continuous (j'.comp c) :=
    hj.comp (e.equiv.symm.continuous.comp elementaryCoverZeroHom_continuous_isOpenMap.1)
  have hOpen : IsOpenMap (j'.comp c) :=
    hjo.comp (e.equiv.symm.toHomeomorph.isOpenMap.comp
      elementaryCoverZeroHom_continuous_isOpenMap.2)
  have hkClosed : IsClosed ((k.comap b.val.1.subtype : Subgroup b.val.1) : Set b.val.1) :=
    hk.1.preimage continuous_subtype_val
  let : LocallyCompactSpace H.val := H.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : T1Space b.quotient := QuotientGroup.t1Space_iff.mpr hkClosed
  obtain ⟨e'⟩ := elementaryPresentation_of_open_vector_map (j'.comp c) hContinuous hOpen
    (isCompactlyGeneratedGroup_quotient H.property.2 _ hkClosed)
  let L := AddMonoidHom.toMultiplicative.symm
    (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
  have hL : Continuous L := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
  let φ := fun y ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd y))
  have hs := contDiff_comp_elementaryHom L hL (f := φ) (hSmooth e') z d
  convert hs using 1
  funext u
  change f₀ (j (e.equiv.symm _)) = f₀ (e'.equiv.symm (e'.equiv (j (e.equiv.symm _))))
  rw [e'.equiv.symm_apply_apply]

/-- Paper: Definition D.1.5.3(1), p. 762. The sum of two functions of class Cᵖ
is of class Cᵖ. -/
theorem IsBruhatContDiff.add {p : ℕ} {f g : G → ℂ}
    (hf : IsBruhatContDiff p f) (hg : IsBruhatContDiff p g) :
    IsBruhatContDiff p (f + g) := by
  obtain ⟨k, hk, hfk, hfd⟩ := hf
  obtain ⟨l, hl, hgl, hgd⟩ := hg
  refine ⟨k ⊓ l, isBruhatGoodSubgroup_inf hk hl, ?_, ?_⟩
  · intro h x
    exact congrArg₂ (· + ·) (hfk ⟨h, h.property.1⟩ x) (hgl ⟨h, h.property.2⟩ x)
  · intro a ha
    obtain ⟨f₀, hf₀, hfSmooth⟩ := bruhatContDiff_descend_of_le hk hfd a (ha ▸ inf_le_left)
    obtain ⟨g₀, hg₀, hgSmooth⟩ := bruhatContDiff_descend_of_le hl hgd a (ha ▸ inf_le_right)
    exact ⟨f₀ + g₀, fun x ↦ congrArg₂ (· + ·) (hf₀ x) (hg₀ x),
      fun e z d ↦ (hfSmooth e z d).add (hgSmooth e z d)⟩

/-- Paper: Definition D.1.5.3(1), p. 762. A complex scalar multiple of a function
of class Cᵖ is of class Cᵖ. -/
theorem IsBruhatContDiff.smul {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff p f) (z : ℂ) : IsBruhatContDiff p (z • f) := by
  obtain ⟨k, hk, hInv, hDescend⟩ := hf
  refine ⟨k, hk, fun h x ↦ congrArg (z • ·) (hInv h x), ?_⟩
  intro a ha
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend a ha
  exact ⟨z • f₀, fun x ↦ congrArg (z • ·) (hf₀ x),
    fun e l b ↦ (hSmooth e l b).const_smul z⟩

/-- Paper: Definition D.1.5.3(1), p. 762. The Cᵖ functions form a complex vector
subspace of the functions on G. -/
def bruhatContDiffSubmodule (p : ℕ) : Submodule ℂ (G → ℂ) where
  carrier := {f | IsBruhatContDiff p f}
  zero_mem' := isBruhatContDiff_zero p
  add_mem' hf hg := hf.add hg
  smul_mem' z _ hf := hf.smul z

/-- Paper: Definition D.1.5.3(1), p. 762. The smooth functions are the
intersection of the Cᵖ subspaces over all finite orders. -/
def bruhatSmoothSubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ p : ℕ, bruhatContDiffSubmodule p

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the Cᵖ submodule is
equivalent to the stated Bruhat differentiability condition. -/
theorem mem_bruhatContDiffSubmodule_iff (p : ℕ) (f : G → ℂ) :
    f ∈ bruhatContDiffSubmodule p ↔ IsBruhatContDiff p f := Iff.rfl

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the smooth submodule
means Bruhat differentiability at every finite order. -/
theorem mem_bruhatSmoothSubmodule_iff (f : G → ℂ) :
    f ∈ bruhatSmoothSubmodule ↔ IsBruhatSmooth f := by
  simp only [bruhatSmoothSubmodule, Submodule.mem_iInf]
  rfl

omit hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. In an elementary presentation, a stage
is the existing elementary Schwartz space with its seminorm topology. -/
abbrev SchwartzBruhatStage {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : ElementaryLCAPresentation A) :=
  ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. A stage function is pulled back along
the quotient and extended by zero outside the open subgroup.
Deviation: The printed composition is reversed and omits restriction to the open subgroup. -/
def schwartzBruhatStageRealization (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : SchwartzBruhatStage e →ₗ[ℂ] (G → ℂ) :=
  (LinearMap.pi fun x : G ↦
    if hx : x ∈ a.val.1 then
      LinearMap.proj (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
    else 0).comp (elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank
      e.finiteFactor).subtype

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. The realization evaluates a stage
function at the quotient coordinate on the open subgroup and vanishes outside it. -/
theorem schwartzBruhatStageRealization_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    schwartzBruhatStageRealization a e f x =
      if hx : x ∈ a.val.1 then
        f (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
      else 0 := by
  unfold schwartzBruhatStageRealization
  erw [LinearMap.comp_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

include hTop hT2 hLC in
/-- Paper: Lemma D.1.5.4, p. 762. Pullback to the smaller kernel and extension by
zero to the larger open subgroup give a closed embedding of stages.
Deviation: The map is characterized by equality of the realized functions on G,
which determines the pullback and extension on the elementary quotients. -/
theorem schwartzBruhatStage_transition {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (e' : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e',
      (∀ f, schwartzBruhatStageRealization b e' (j f) = schwartzBruhatStageRealization a e f) ∧
        IsClosedEmbedding j := by sorry

/-- Paper: (D.1.5.4), p. 763. The underlying Schwartz–Bruhat submodule is generated
by the realizations in every structural pair and every elementary presentation. -/
def schwartzBruhatSubmodule (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Submodule ℂ (G → ℂ) :=
  ⨆ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
    (schwartzBruhatStageRealization a e).range

/-- Paper: (D.1.5.4), p. 763. The stage realization takes values in the
Schwartz–Bruhat submodule and gives the canonical linear stage map. -/
def schwartzBruhatStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    SchwartzBruhatStage e →ₗ[ℂ] schwartzBruhatSubmodule G :=
  (schwartzBruhatStageRealization a e).codRestrict (schwartzBruhatSubmodule G)
    (fun f ↦ Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem e ⟨f, rfl⟩))

/-- Paper: (D.1.5.4), p. 763. The Schwartz–Bruhat topology is generated by the
seminorms that pull back continuously to each stage.
Deviation: Using all elementary presentations avoids fixing any choice of coordinates. -/
abbrev SchwartzBruhat (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  WithGeneratingSeminorms (schwartzBruhatSubmodule G)
    (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} → _)

instance : CoeFun (SchwartzBruhat G) (fun _ ↦ G → ℂ) where
  coe f := (show schwartzBruhatSubmodule G from f).val

/-- Paper: (D.1.5.4), p. 763. The stage inclusion evaluates to the function
obtained by pullback and extension by zero. -/
theorem schwartzBruhatStageInclusion_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    (show SchwartzBruhat G from schwartzBruhatStageInclusion a e f) x =
      schwartzBruhatStageRealization a e f x := rfl

include hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. A function belongs to the
Schwartz–Bruhat submodule exactly when a single structural pair and a single
elementary Schwartz function realize it. -/
theorem mem_schwartzBruhatSubmodule_iff (f : G → ℂ) :
    f ∈ schwartzBruhatSubmodule G ↔
      ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (s : SchwartzBruhatStage e), schwartzBruhatStageRealization a e s = f := by sorry

/-- Paper: (D.1.5.4), p. 763. The topology has the final locally convex property
for the canonical linear stage maps. -/
theorem schwartzBruhat_topology_eq_final :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      locallyConvexFinalTopology
        (fun i : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient ↦
          (show SchwartzBruhatStage i.2 →ₗ[ℂ] SchwartzBruhat G from
            schwartzBruhatStageInclusion i.1 i.2)) := by sorry

-- TODO(paper-gap): Remark D.1.5.5 identifies global smooth functions with a
-- colimit of the smooth structural quotients. For the same extension-by-zero
-- maps, that colimit contains only functions supported in an open compactly
-- generated subgroup. The constant function 1 on discrete ℚ is smooth but
-- has no such support.

/-- Paper: Remark D.1.5.5, p. 763. Every Schwartz–Bruhat function is smooth in
the sense of Definition D.1.5.3(1). -/
theorem schwartzBruhat_isBruhatSmooth (f : SchwartzBruhat G) : IsBruhatSmooth f := by sorry

/-- Paper: Remark D.1.5.5, p. 763. A character restricts to a smooth function on
each open compactly generated subgroup. -/
theorem pontryaginDual_restriction_isBruhatSmooth (χ : PontryaginDual G)
    (J : OpenCompactlyGeneratedSubgroups G) :
    IsBruhatSmooth (fun x : J.val ↦ (χ x.val : ℂ)) := by sorry

/-- Paper: Lemma D.1.5.6(1), p. 763. The final locally convex topology is Hausdorff
when the group is second countable. -/
theorem schwartzBruhat_t2 [SecondCountableTopology G] : T2Space (SchwartzBruhat G) := by sorry

/-- Paper: Lemma D.1.5.6, p. 763. A compact exhaustion controls the open subgroups,
and shrinking identity neighborhoods control the kernels, since the elementary quotients
have no small subgroups. Together they give an increasing cofinal sequence. -/
private theorem exists_cofinal_bruhatStructuralPairs [SecondCountableTopology G] :
    ∃ b : ℕ → BruhatStructuralPair G, Monotone b ∧ ∀ a, ∃ n, a ≤ b n := by
  classical
  let C := CompactExhaustion.choice G
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose H hH using fun n ↦ exists_openCompactlyGeneratedSubgroup_contains (C.isCompact n)
  choose A hA using fun n ↦ exists_lcaDualAnnihilator_subset_nhds
    (inter_mem (hU.mem n) ((H n).property.1.mem_nhds (H n).val.one_mem))
  let K (n : ℕ) := lcaDualAnnihilator (A n).val
  have hGood (n : ℕ) : IsBruhatGoodSubgroup (K n) := by
    refine ⟨(isCompact_lcaDualAnnihilator _ (A n).property.1).isClosed, ?_⟩
    rw [show lcaAnnihilator (K n) = (A n).val from
      lcaAnnihilator_dualAnnihilator_of_open _ (A n).property.1]
    exact (A n).property
  let b (n : ℕ) : BruhatStructuralPair G :=
    ⟨((H n).val, OrderDual.toDual (K n)), (H n).property.1, (H n).property.2,
      hGood n, fun _ hx ↦ (hA n hx).2⟩
  have hCofinal (a : BruhatStructuralPair G) : ∃ n, a ≤ b n := by
    obtain ⟨D, _, hDc, hDgen⟩ := a.property.2.1
    obtain ⟨m, hm⟩ := C.exists_superset_of_isCompact (hDc.image continuous_subtype_val)
    let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
    let : T1Space a.quotient :=
      QuotientGroup.t1Space_iff.mpr (a.property.2.2.1.1.preimage continuous_subtype_val)
    obtain ⟨e⟩ := a.elementary
    obtain ⟨W, hW, hPow⟩ :=
      exists_nhds_one_of_isLocallyEuclidean (locallyEuclidean_of_elementaryPresentation e)
    let π : a.val.1 →* a.quotient := QuotientGroup.mk' _
    have hPre : π ⁻¹' W ∈ 𝓝 (1 : a.val.1) :=
      (QuotientGroup.continuous_mk (N := _) : Continuous π).continuousAt.preimage_mem_nhds
        (by change W ∈ 𝓝 (π 1); rwa [map_one])
    have hImage : Subtype.val '' (π ⁻¹' W) ∈ 𝓝 (1 : G) :=
      a.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hPre
    obtain ⟨l, _, hl⟩ := hU.1.mem_iff.mp hImage
    let n := max m l
    refine ⟨n, ?_, ?_⟩
    · have hD : D ⊆ ((H n).val.comap a.val.1.subtype : Set a.val.1) :=
        fun x hx ↦ hH n (C.subset (le_max_left m l) (hm ⟨x, hx, rfl⟩))
      have htop : ⊤ ≤ (H n).val.comap a.val.1.subtype :=
        hDgen ▸ (Subgroup.closure_le _).mpr hD
      exact fun x hx ↦ htop (Subgroup.mem_top ⟨x, hx⟩)
    · have hSmall : (K n : Set G) ⊆ Subtype.val '' (π ⁻¹' W) :=
        fun _ hx ↦ hl (hU.2 (le_max_right m l) (hA n hx).1)
      intro x hx
      obtain ⟨y, _, rfl⟩ := hSmall hx
      apply (a.quotient_mk_eq_one y).mp
      change π y = 1
      apply hPow
      intro k
      rw [← map_pow]
      obtain ⟨z, hz, hzy⟩ := hSmall ((K n).pow_mem hx k)
      exact (Subtype.ext hzy : z = y ^ k) ▸ hz
  let := (bruhatStructuralPair_filtered (G := G)).2
  choose upper hleft hright using (exists_ge_ge (α := BruhatStructuralPair G))
  let chain : ℕ → BruhatStructuralPair G :=
    Nat.rec (b 0) fun n prev ↦ upper prev (b (n + 1))
  have hdom (n : ℕ) : b n ≤ chain n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hright (chain n) (b (n + 1))
  exact ⟨chain, monotone_nat_of_le_succ fun n ↦ hleft (chain n) (b (n + 1)), fun a ↦ by
    obtain ⟨n, hn⟩ := hCofinal a
    exact ⟨n, hn.trans (hdom n)⟩⟩

omit hTop hT2 hLC in
/-- A stage function is determined by its realization because every elementary coordinate
is represented by a point in the open subgroup. -/
private theorem schwartzBruhatStageInclusion_injective (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Function.Injective (schwartzBruhatStageInclusion a e) := by
  classical
  intro f g hfg
  apply Subtype.ext
  funext z
  obtain ⟨q, hq⟩ := e.equiv.surjective (Multiplicative.ofAdd z)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have h := congrArg (fun f : schwartzBruhatSubmodule G ↦ f.val x.val) hfg
  change schwartzBruhatStageRealization a e f x.val = schwartzBruhatStageRealization a e g x.val at h
  simpa only [schwartzBruhatStageRealization_apply, dite_eq_left x.property, hq,
    toAdd_ofAdd] using h

omit hTop hT2 hLC in
/-- A cofinal sequence with embedding transitions induces the same final locally convex
topology as the full system. Each stage embeds by factoring through a stage of that sequence. -/
private theorem isEmbedding_of_cofinal_lcStages {ι E : Type*}
    [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, PolynormableSpace ℂ (X a)]
    (inc : ∀ a, X a →ₗ[ℂ] E) (s : ℕ → ι)
    (hinj : ∀ n, Function.Injective (inc (s n)))
    (hex : ∀ x : E, ∃ a, x ∈ (inc a).range)
    (ht : t = locallyConvexFinalTopology inc)
    (hstep : ∀ n, ∃ j : X (s n) →L[ℂ] X (s (n + 1)),
      (∀ x, inc (s (n + 1)) (j x) = inc (s n) x) ∧ IsEmbedding j)
    (hfactor : ∀ a, ∃ n, ∃ j : X a →L[ℂ] X (s n),
      (∀ x, inc (s n) (j x) = inc a x) ∧ IsEmbedding j)
    (a : ι) : IsEmbedding (inc a) := by
  classical
  let stage (n : ℕ) := inc (s n)
  have htests : (fun q : Seminorm ℂ E ↦ ∀ a, Continuous (q ∘ inc a)) =
      (fun q : Seminorm ℂ E ↦ ∀ n, Continuous (q ∘ stage n)) := by
    funext q
    exact propext ⟨fun h n ↦ h (s n), fun h a ↦ by
      obtain ⟨n, j, hj, _⟩ := hfactor a
      exact ((h n).comp j.continuous).congr fun x ↦ congrArg q (hj x)⟩
  have ht' : t = locallyConvexFinalTopology stage :=
    ht.trans (congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology) htests)
  have hseminorms : WithSeminorms
      (Subtype.val : {q : Seminorm ℂ E // ∀ n, Continuous (q ∘ stage n)} → Seminorm ℂ E) := ⟨ht'⟩
  let i (n : ℕ) : X (s n) →L[ℂ] E :=
    ⟨stage n, hseminorms.continuous_of_continuous_comp _ fun q ↦ q.property n⟩
  choose j hj hEmb using hstep
  have hlim : IsInjectiveLCLimit (X := fun n ↦ X (s n)) j i := by
    refine ⟨hinj, fun n ↦ ContinuousLinearMap.ext (hj n), ?_, ht'⟩
    intro x
    obtain ⟨c, y, rfl⟩ := hex x
    obtain ⟨n, k, hk, _⟩ := hfactor c
    exact ⟨n, k y, hk y⟩
  obtain ⟨n, k, hk, hkEmb⟩ := hfactor a
  have hcomp : (i n : X (s n) → E) ∘ k = inc a := funext hk
  exact hcomp ▸ (hlim.isEmbedding_stage hEmb n).comp hkEmb

/-- Paper: Lemma D.1.5.6(1), p. 763. Each structural stage inherits its intrinsic
topology from the final locally convex topology. -/
theorem schwartzBruhatStage_isEmbedding [SecondCountableTopology G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    IsEmbedding (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) := by
  classical
  let ι := (c : BruhatStructuralPair G) × ElementaryLCAPresentation c.quotient
  let X (c : ι) := SchwartzBruhatStage c.2
  let inc (c : ι) : X c →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion c.1 c.2
  have hseq := exists_cofinal_bruhatStructuralPairs (G := G)
  let b := hseq.choose
  let s (n : ℕ) : ι := ⟨b n, Classical.choice (b n).elementary⟩
  have htransition (c c' : ι) (hc : c.1 ≤ c'.1) :
      ∃ j : X c →L[ℂ] X c', (∀ x, inc c' (j x) = inc c x) ∧ IsEmbedding j := by
    have h := schwartzBruhatStage_transition hc c.2 c'.2
    exact ⟨h.choose, fun x ↦ Subtype.ext (h.choose_spec.1 x), h.choose_spec.2.isEmbedding⟩
  refine isEmbedding_of_cofinal_lcStages (X := X) inc s
    (fun n ↦ schwartzBruhatStageInclusion_injective (s n).1 (s n).2)
    ?_ schwartzBruhat_topology_eq_final
    (fun n ↦ htransition (s n) (s (n + 1)) (hseq.choose_spec.1 (Nat.le_succ n))) ?_ ⟨a, e⟩
  · intro f
    have hf := (mem_schwartzBruhatSubmodule_iff _).mp
      (show schwartzBruhatSubmodule G from f).property
    exact hf.elim fun c hc ↦ hc.elim fun p hp ↦ hp.elim fun x hx ↦
      ⟨⟨c, p⟩, x, Subtype.ext hx⟩
  · intro c
    have hc := hseq.choose_spec.2 c.1
    exact ⟨hc.choose, htransition c (s hc.choose) hc.choose_spec⟩

/-- Paper: Lemma D.1.5.6(2), p. 763. Every bounded subset of the limit is
the image of a bounded subset of a single stage. -/
theorem schwartzBruhat_bounded_image_stage [SecondCountableTopology G]
    {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : Set (SchwartzBruhatStage e)), IsVonNBounded ℂ C ∧
        (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
          schwartzBruhatStageInclusion a e) '' C = B := by sorry

end SchwartzBruhat

section MainTheorems

universe v

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.5.7, p. 763. The Schwartz–Bruhat space is barrelled. -/
theorem schwartzBruhat_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is bornological, including beyond the second-countable case.
Deviation: We use the criterion that a seminorm bounded on every bounded set is continuous. -/
theorem schwartzBruhat_bornological :
    ∀ p : Seminorm ℂ (SchwartzBruhat G),
      (∀ B : Set (SchwartzBruhat G), IsVonNBounded ℂ B → BddAbove (p '' B)) →
        Continuous p := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is complete for its additive uniformity, including beyond the second-countable case. -/
theorem schwartzBruhat_complete :
    CompleteSpace (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is complete. -/
theorem schwartzBruhat_strongDual_complete [SecondCountableTopology G] :
    CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The Schwartz–Bruhat space of a second-countable
group is nuclear. -/
theorem schwartzBruhat_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
of a second-countable group is nuclear. -/
theorem schwartzBruhat_strongDual_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Closed bounded subsets
of the Schwartz–Bruhat space are compact, including beyond the second-countable case. -/
theorem schwartzBruhat_montel :
    MontelSpace ℂ (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. Closed bounded subsets of the strong dual
of the Schwartz–Bruhat space are compact. -/
theorem schwartzBruhat_strongDual_montel [SecondCountableTopology G] :
    MontelSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by
  letI : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  letI : BarrelledSpace ℂ (SchwartzBruhat G) := schwartzBruhat_barrelled
  letI : MontelSpace ℂ (SchwartzBruhat G) := schwartzBruhat_montel
  exact montelSpace_strongDual

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Evaluation gives a
linear homeomorphism with the strong bidual, the paper's reflexivity property
of Montel spaces, including beyond the second-countable case. -/
theorem schwartzBruhat_reflexive :
    ∃ e : SchwartzBruhat G ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (SchwartzBruhat G)),
      ∀ f L, e f L = L f := by sorry

-- Checking section-variable usage is expensive for the nested strong duals here.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.5.7, p. 764. Evaluation identifies the strong dual
linearly and topologically with its own strong bidual. -/
theorem schwartzBruhat_strongDual_reflexive [SecondCountableTopology G] :
    let D := StrongDual ℂ (SchwartzBruhat G)
    letI : TopologicalSpace D := inferInstanceAs (TopologicalSpace (StrongDual ℂ (SchwartzBruhat G)))
    let DD := StrongDual ℂ D
    letI : TopologicalSpace DD := ContinuousLinearMap.topologicalSpace
    letI : TopologicalSpace (StrongDual ℂ DD) := ContinuousLinearMap.topologicalSpace
    ∃ e : D ≃L[ℂ] StrongDual ℂ DD, ∀ L M, e L M = M L := by
  refine (schwartzBruhat_reflexive (G := G)).elim ?_
  intro e he
  refine ⟨e.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ), ?_⟩
  intro L M
  change L (e.symm M) = M L
  simpa only [e.apply_symm_apply] using (he (e.symm M) L).symm

open scoped ComplexOrder in
/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is barrelled. -/
theorem schwartzBruhat_strongDual_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by
  suffices h : ∀ (E : Type _) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
      [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
      [MontelSpace ℂ E], BarrelledSpace ℂ (StrongDual ℂ E) by
    let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
    let : MontelSpace ℂ (SchwartzBruhat G) := schwartzBruhat_montel
    exact h (SchwartzBruhat G)
  intro E _ _ _ _ _ _ _ _
  let D := StrongDual ℂ E
  let S : Set (Set E) := {s | IsVonNBounded ℂ s}
  have hS : ⋃₀ S = (univ : Set E) := sUnion_isVonNBounded_eq_univ (𝕜 := ℂ) (E := E)
  have hdense : Dense (Submodule.span ℂ (⋃₀ S) : Set E) := by
    rw [hS, Submodule.span_univ, Submodule.top_coe]
    exact dense_univ
  let : PolynormableSpace ℂ D :=
    uniformConvergenceCLM_polynormable (E := E) (F := ℂ) S (fun _ hs ↦ hs) hdense
  refine ⟨fun p hp ↦ Seminorm.continuous' (r := 1) ?_⟩
  let U := p.closedBall 0 1
  let A := (topDualPairing ℂ E).polar U
  -- The polar of the absorbing unit ball is bounded under every functional on E.
  have hA : IsVonNBounded ℂ A := by
    apply (isVonNBounded_iff_dual_image (E := E) A).mpr
    intro φ
    obtain ⟨c, hc⟩ := (p.absorbent_closedBall_zero one_pos φ).exists
    refine isBounded_iff_forall_norm_le.mpr ⟨‖c‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ψ, hψ, hφ⟩ := hc (mem_singleton φ)
    rw [← hφ]
    change ‖(c • ψ) x‖ ≤ ‖c‖
    rw [smul_apply, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx ψ hψ)
  have hU : IsClosed U := by
    rw [show U = {φ | p φ ≤ 1} from p.closedBall_zero_eq]
    exact hp.isClosed_preimage 1
  let : Module ℝ D := Module.restrictScalars ℝ ℂ D
  let : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  have haU : AbsConvex ℂ U := ⟨p.balanced_closedBall_zero 1,
    convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 1)⟩
  have hzU : 0 ∈ U := p.mem_closedBall_zero.mpr (by simp)
  -- A separating functional is evaluation at a point of A.
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA
    (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with φ hφ
  by_contra hnot
  obtain ⟨l, hl, hlt⟩ := exists_dual_norm_le_one_lt_of_notMem hU haU hzU hnot
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval (E := E) l
  have hx : x ∈ A := fun ψ hψ ↦ hl ψ hψ
  exact (not_lt_of_ge (mem_ball_zero_iff.mp (hφ hx)).le) hlt

/-- Paper: Remark D.1.5.8, p. 764. The Schwartz–Bruhat space of a group that
fails second countability fails nuclearity. -/
theorem schwartzBruhat_not_nuclear (hG : ¬ SecondCountableTopology G) :
    ¬ IsNuclearTVS.{v} (SchwartzBruhat G) := by sorry

/-- Paper: Proposition D.1.5.9, p. 764. Every defining countable sequence
of Fréchet stages for the Schwartz–Bruhat space is acyclic in the sense of §C.1.5.
Deviation: A defining sequence is expressed using the compatible injections and the
locally convex limit topology of `IsInjectiveLCLimit`. -/
theorem schwartzBruhat_acyclic [SecondCountableTopology G]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (hX : ∀ n, IsFrechetTVS (X n))
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] SchwartzBruhat G}
    (h : IsInjectiveLCLimit j i) : IsAcyclicSystem j := by sorry

/-- Paper: Theorem D.1.5.10, p. 765. A cofinal increasing sequence of structural
stages gives a short topologically exact sequence. The difference map embeds
as the closed kernel of the quotient map given by summing the stage inclusions.
Deviation: Each stage is expressed in an elementary presentation and the difference
map uses the induced maps between successive presentations. -/
theorem schwartzBruhat_exists_topologicallyExact [SecondCountableTopology G] :
    ∃ (a : ℕ → BruhatStructuralPair G)
      (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
      (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1))),
      Monotone a ∧ (∀ b, ∃ n, b ≤ a n) ∧
      (∀ n f, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n f) =
        schwartzBruhatStageRealization (a n) (e n) f) ∧
      let X := fun n ↦ SchwartzBruhatStage (e n)
      let q := DirectSum.toModule ℂ ℕ (SchwartzBruhat G)
        (fun n ↦ (show X n →ₗ[ℂ] SchwartzBruhat G from schwartzBruhatStageInclusion (a n) (e n)))
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
      IsClosedEmbedding (directSumDifference j) ∧
        LinearMap.range (directSumDifference j) = LinearMap.ker q ∧ IsQuotientMap q := by sorry

end MainTheorems

/-! ## Deferred from §C.1 -/

section DeferredFromC1

open NumberField

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
adele ring of a number field is nonmetrizable. -/
theorem schwartzBruhat_adele_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a number field's
idele class group is nonmetrizable. -/
theorem schwartzBruhat_ideleClass_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (IdeleClassGroup (𝓞 F) F)) := by sorry

variable (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [LocallyCompactSpace L]

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
group of a nonarchimedean local field is nonmetrizable. -/
theorem schwartzBruhat_localField_not_metrizable :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative L)) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a nonarchimedean
local field has countably infinite complex dimension. -/
theorem schwartzBruhat_localField_rank :
    Module.rank ℂ (SchwartzBruhat (Multiplicative L)) = ℵ₀ := by sorry

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Paper: Example C.1.4.6(3), p. 662. The complete Schwartz–Bruhat space of a
second-countable LCA group is quasi-complete. The example's other properties
are `schwartzBruhat_complete`, `schwartzBruhat_nuclear`, `schwartzBruhat_montel`
and `schwartzBruhat_reflexive` from Theorem D.1.5.7. -/
theorem schwartzBruhat_quasiComplete :
    QuasiCompleteSpace ℂ (SchwartzBruhat G) := by sorry

end DeferredFromC1

end RiemannMasullo
