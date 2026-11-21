module

public import RiemannMasullo.AppC_LCTVS.Sec4
import Mathlib.Analysis.Convex.TotallyBounded
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual

/-! # Pettis averaging, invariants and isotypes -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology
open scoped InnerProductSpace NNReal

section Isotypes

variable {G E : Type*} [Monoid G] [TopologicalSpace G]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Corollary 4.3.3.3(2), p. 183. An isotypic subspace is the common
eigenspace for the given character. For the trivial character it is the
fixed subspace in Lemma 4.3.3.1(2) and for the regular action it is the
isotype of Terminology 4.3.2.1. -/
def actionIsotype (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) : Submodule ℂ E :=
  ⨅ g : G, LinearMap.ker ((ρ g).toLinearMap - (ω g : ℂ) • LinearMap.id)

/-- Paper: Corollary 4.3.3.3(2), p. 183. A vector lies in the isotype exactly
when every group element acts on it by the specified character value. -/
theorem mem_actionIsotype (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) (u : E) :
    u ∈ actionIsotype ρ ω ↔ ∀ g : G, ρ g u = (ω g : ℂ) • u := by
  simp [actionIsotype, Submodule.mem_iInf, sub_eq_zero]

/-- Paper: Lemma 4.3.3.1(2), p. 181 and Corollary 4.3.3.3(2), p. 183.
The isotypic subspace is closed in the original topology. -/
theorem isClosed_actionIsotype [T2Space E] [ContinuousSMul ℂ E] (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) :
    IsClosed (actionIsotype ρ ω : Set E) := by
  rw [actionIsotype, Submodule.coe_iInf]
  refine isClosed_iInter fun g ↦ ?_
  rw [← LinearMap.eqLocus_eq_ker_sub]
  exact isClosed_eq (ρ g).continuous (continuous_const_smul (ω g : ℂ))

variable [MeasurableSpace G]

/-- Paper: (4.3.3.1), p. 181 and (4.3.3.8), p. 183. An unnormalized
isotypic averaging operator represents the integrals of the character-twisted
orbits against every continuous linear functional. The trivial character
gives the untwisted average. -/
def IsPettisIsotypicAverageOn (μ : Measure G) (X : Set G)
    (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) (P : E →L[ℂ] E) : Prop :=
  ∀ u : E, HasPettisIntegral (.positive (μ.restrict X))
    (fun g : G ↦ star (ω g : ℂ) • ρ g u) (P u)

/-- Paper: (4.3.3.5), p. 182. The untwisted average of a fixed vector equals
the vector times the mass of the compact group. -/
theorem IsPettisIsotypicAverageOn.apply_fixed [T2Space E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] (μ : Measure G) [IsFiniteMeasure μ]
    (ρ : G →* (E →L[ℂ] E)) (P : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ univ ρ 1 P) (u : E) (hu : ∀ g, ρ g u = u) :
    P u = μ.real univ • u := by sorry

end Isotypes

open scoped Pointwise in
/-- A weakly integrable map taking values almost everywhere in a compact convex set
containing zero has a Pettis integral in the set scaled by the total measure. -/
theorem exists_hasPettisIntegral_mem_smul_of_isCompact_convex {X E : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → E} (hi : PettisWeaklyIntegrable (.positive μ) f) {C : Set E} (hc : IsCompact C)
    (hconv : Convex ℝ C) (hzero : 0 ∈ C) (hmem : ∀ᵐ x ∂μ, f x ∈ C) :
    ∃ v ∈ μ.real univ • C, HasPettisIntegral (.positive μ) f v := by
  let L := toPettisWeakCompletion E
  let B : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ] (StrongDual ℂ E) →ₗ[ℂ] ℂ := .id
  have : T2Space (PettisWeakCompletion E) :=
    (WeakBilin.isEmbedding (B := B) Function.injective_id).t2Space
  have hL : Continuous L := WeakBilin.continuous_of_continuous_eval B fun φ ↦ φ.continuous
  let w := pettisWeakIntegral (.positive μ) f hi
  let d := μ.real univ
  by_cases hz : μ = 0
  · subst μ
    refine ⟨0, ⟨0, hzero, smul_zero _⟩, hi, ?_⟩
    apply LinearMap.ext
    intro φ
    change φ 0 = ∫ x, φ (f x) ∂(0 : Measure X)
    simp
  have : NeZero μ := ⟨hz⟩
  have hd : 0 < d := measureReal_univ_pos
  have hw : d⁻¹ • w ∈ L '' C := by
    by_contra hn
    obtain ⟨l, r, hl, hr⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (hconv.linear_image (L.restrictScalars ℝ)) (hc.image hL).isClosed hn
    obtain ⟨φ, hφ⟩ := (B.rightDualEquiv LinearMap.SeparatingRight.id).surjective l
    change WeakBilin.eval B φ = l at hφ
    subst l
    have hs : ∀ᵐ x ∂μ, (φ (f x)).re ≤ r := hmem.mono fun x hx ↦
      (hl (L (f x)) ⟨f x, hx, rfl⟩).le
    have hφi : Integrable (fun x ↦ φ (f x)) μ := hi φ
    have hb := integral_mono_ae hφi.re (integrable_const r) hs
    rw [integral_re hφi, integral_const] at hb
    change r < (d⁻¹ • ∫ x, φ (f x) ∂μ).re at hr
    rw [Complex.real_smul, Complex.re_ofReal_mul, lt_inv_mul_iff₀ hd] at hr
    exact hr.not_ge hb
  obtain ⟨u, hu, he⟩ := hw
  refine ⟨d • u, ⟨u, hu, rfl⟩, hi, ?_⟩
  exact ((L.restrictScalars ℝ).map_smul d u).trans (he ▸ smul_inv_smul₀ hd.ne' w)

open scoped Pointwise in
/-- Integration of a jointly continuous family of linear operators against a finite
positive measure concentrated on a compact set gives a continuous linear operator. -/
private theorem existsUnique_pettisIntegral_continuousFamily {X E : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [QuasiCompleteSpace ℂ E] [SeparatingDual ℂ E]
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (A : X → E →L[ℂ] E) (hA : Continuous fun p : X × E ↦ A p.1 p.2) :
    ∃! P : E →L[ℂ] E, ∀ u, HasPettisIntegral (.positive μ) (fun x ↦ A x u) (P u) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let C (u : E) := closure (convexHull ℝ (insert 0 ((fun x ↦ A x u) '' K)))
  have hi (u : E) : PettisWeaklyIntegrable (.positive μ) (fun x ↦ A x u) := by
    intro φ
    have hcont : Continuous (fun x ↦ φ (A x u)) :=
      φ.continuous.comp (hA.comp (continuous_id.prodMk continuous_const))
    obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    exact (integrable_const (μ := μ) r).mono' hcont.aestronglyMeasurable (hμ.mono hr)
  have hP (u : E) : ∃ v ∈ μ.real univ • C u,
      HasPettisIntegral (.positive μ) (fun x ↦ A x u) v := by
    have hc : IsCompact (insert 0 ((fun x ↦ A x u) '' K)) :=
      (hK.image (hA.comp (continuous_id.prodMk continuous_const))).insert 0
    apply exists_hasPettisIntegral_mem_smul_of_isCompact_convex μ (hi u)
      (isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ) hc.totallyBounded.convexHull)
      (convex_convexHull ..).closure (subset_closure (subset_convexHull _ _ (mem_insert _ _)))
    exact hμ.mono fun x hx ↦ subset_closure (subset_convexHull _ _
      (mem_insert_of_mem _ ⟨x, hx, rfl⟩))
  choose P hbound hP using hP
  have hdual {v : E} {f : X → E} (h : HasPettisIntegral (.positive μ) f v) (φ : StrongDual ℂ E) :
      φ v = ∫ x, φ (f x) ∂μ := by
    obtain ⟨_, he⟩ := h
    exact congrArg (fun z : PettisWeakCompletion E ↦
      (show Module.Dual ℂ (StrongDual ℂ E) from z) φ) he
  let L : E →ₗ[ℂ] E :=
    { toFun := P
      map_add' := by
        intro u v
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
        intro φ
        rw [map_add, hdual (hP (u + v)), hdual (hP u), hdual (hP v)]
        simp only [map_add]
        exact integral_add (hi u φ) (hi v φ)
      map_smul' := by
        intro c u
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
        intro φ
        rw [map_smul, hdual (hP (c • u)), hdual (hP u)]
        simp only [map_smul, integral_smul, RingHom.id_apply] }
  have hcont : Continuous L := by
    apply continuous_of_tendsto_nhds_zero L
    apply (nhds_hasBasis_absConvex_closed ℝ E).tendsto_right_iff.2
    intro V hV
    let d := μ.real univ
    have hF : Continuous (fun p : X × E ↦ d • A p.1 p.2) := hA.const_smul d
    obtain ⟨U, W, _, hopen, hU, hW, hprod⟩ :=
      generalized_tube_lemma hK (isCompact_singleton (x := (0 : E)))
      (isOpen_interior.preimage hF) (by
        rintro ⟨x, u⟩ ⟨_, hu⟩
        have hu' : u = 0 := hu
        simpa [hu'] using mem_interior_iff_mem_nhds.mpr hV.1)
    filter_upwards [hopen.mem_nhds (hW (mem_singleton _))] with u hu
    obtain ⟨v, hv, he⟩ := hbound u
    change P u ∈ V
    rw [← he]
    apply (closure_minimal (t := (fun z : E ↦ d • z) ⁻¹' V) _
      (hV.2.1.preimage (continuous_const_smul d))) hv
    apply convexHull_min _ (hV.2.2.2.smul_preimage d)
    rintro _ (rfl | ⟨x, hx, rfl⟩)
    · simpa using mem_of_mem_nhds hV.1
    · exact interior_subset (s := V) (hprod (show (x, u) ∈ U ×ˢ W from ⟨hU hx, hu⟩))
  refine ⟨⟨L, hcont⟩, hP, fun Q hQ ↦ ?_⟩
  ext u
  exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun φ ↦
    (hdual (hQ u) φ).trans (hdual (hP u) φ).symm

section Averaging

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [hE : QuasiCompleteSpace ℂ E]
  (μ : Measure G) [hμ : μ.IsHaarMeasure]
  (ρ : G →* (E →L[ℂ] E))
  (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))

include hE hμ hρ

/-- Paper: Lemma 4.3.3.1(1), p. 181. On a compact group the orbit integrals
give a unique continuous linear averaging operator, under equicontinuity
or sequential equicontinuity on a bornological space. -/
theorem existsUnique_compactActionAverage [CompactSpace G]
    (h : EquicontinuousAt (fun g : G ↦ (ρ g : E → E)) 0 ∨
      ((∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
          Continuous p) ∧
        ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
          TendstoUniformly (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop)) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ univ ρ 1 P := by
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  simpa [IsPettisIsotypicAverageOn] using
    existsUnique_pettisIntegral_continuousFamily μ (K := univ) isCompact_univ
      (ae_of_all _ fun _ ↦ mem_univ _) (fun g ↦ ρ g) hρ

/-- Paper: Corollary 4.3.3.3(1), p. 183. The character-weighted orbit
integrals determine a unique continuous linear operator for a sequentially
equicontinuous action on a quasi-complete bornological space. -/
theorem existsUnique_compactActionIsotypicAverage [CompactSpace G]
    (hborn : ∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p)
    (hseq : ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
      TendstoUniformly (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop)
    (ω : PontryaginDual G) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ univ ρ ω P := by sorry

/-- Paper: Lemma 4.3.3.7(1), p. 186. On a relatively compact locally
closed subset with nonempty interior, averaging the action gives a unique
continuous linear operator under either of the stated continuity conditions
on compact subsets. -/
theorem existsUnique_relativelyCompactActionAverage
    (X : Set G) (hX : IsCompact (closure X)) (hlc : IsLocallyClosed X)
    (hint : (interior X).Nonempty)
    (h : (∀ K : Set G, IsCompact K →
        EquicontinuousAt (fun g : K ↦ (ρ g : E → E)) 0) ∨
      ((∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
          Continuous p) ∧
        ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
          ∀ K : Set G, IsCompact K →
            TendstoUniformlyOn (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop K)) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ X ρ 1 P := by sorry

-- TODO(paper-gap): Lemma 4.3.3.7(2) and (3) fail for a relatively compact
-- locally closed subset. On the circle take X to be a proper open arc
-- around 1 and take the standard one-dimensional character action.

/-- Paper: Corollary 4.3.3.8(1), p. 188. The character-weighted Pettis integrals
over the relatively compact subset determine a unique continuous linear operator.
Deviation: The subset is assumed locally closed so that it is measurable. -/
theorem existsUnique_relativelyCompactActionIsotypicAverage
    (X : Set G) (hX : IsCompact (closure X)) (hlc : IsLocallyClosed X)
    (hint : (interior X).Nonempty)
    (hborn : ∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p)
    (hseq : ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
      ∀ K : Set G, IsCompact K →
        TendstoUniformlyOn (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop K)
    (ω : PontryaginDual G) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ X ρ ω P := by sorry

-- TODO(paper-gap): Corollary 4.3.3.8(1) allows nonmeasurable X.
-- Parts (2) and (3) fail even for an open arc and the trivial weight.

end Averaging

section CompactAverageProperties

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  (μ : Measure G) [hμ : μ.IsHaarMeasure]
  (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
  (ω : PontryaginDual G) (P : E →L[ℂ] E)
  (hP : IsPettisIsotypicAverageOn μ univ ρ ω P)

include hμ hρ hP

omit hμ hρ [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
  [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] in
/-- Testing the average against a continuous functional gives its scalar integral. -/
private theorem compactActionAverage_dual_apply (u : E) (φ : StrongDual ℂ E) :
    φ (P u) = ∫ g, star (ω g : ℂ) * φ (ρ g u) ∂μ := by
  obtain ⟨hi, he⟩ := hP u
  have h := congrArg (fun z : PettisWeakCompletion E ↦
    (show Module.Dual ℂ (StrongDual ℂ E) from z) φ) he
  change φ (P u) = ∫ g, φ (star (ω g : ℂ) • ρ g u) ∂μ.restrict univ at h
  simpa only [Measure.restrict_univ, map_smul, smul_eq_mul] using h

omit hρ [CompactSpace G] [T2Space G] in
/-- Translating a twisted orbit integral multiplies it by the character. -/
private theorem compactActionAverage_mem_isotype (u : E) : P u ∈ actionIsotype ρ ω := by
  apply (mem_actionIsotype ..).2
  intro k
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro φ
  have h := compactActionAverage_dual_apply μ ρ ω P hP u (φ.comp (ρ k))
  rw [map_smul, compactActionAverage_dual_apply μ ρ ω P hP u φ, smul_eq_mul,
    ← integral_const_mul, ← integral_mul_left_eq_self (μ := μ)
      (fun g ↦ (ω k : ℂ) * (star (ω g : ℂ) * φ (ρ g u))) k]
  refine h.trans (integral_congr_ae (ae_of_all _ fun g ↦ ?_))
  simp only [ContinuousLinearMap.comp_apply, map_mul, Circle.coe_mul, star_mul',
    mul_apply_eq_comp]
  rw [mul_assoc (star (ω k : ℂ)), ← mul_assoc (ω k : ℂ)]
  simp [← Circle.coe_inv_eq_conj]

omit hρ hμ [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [BorelSpace G] in
/-- On the isotype the average acts by the total mass of the group. -/
private theorem compactActionAverage_apply_isotype {u : E} (hu : u ∈ actionIsotype ρ ω) :
    P u = (μ.real univ : ℂ) • u := by
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro φ
  rw [compactActionAverage_dual_apply μ ρ ω P hP u φ]
  simp [((mem_actionIsotype ..).1 hu), ← Circle.coe_inv_eq_conj,
    Complex.real_smul]

/-- Paper: Lemma 4.3.3.1(2), p. 181 and Corollary 4.3.3.3(2), p. 183.
The average surjects onto the isotype, including the fixed subspace
when the character is trivial. -/
theorem compactActionAverage_range : LinearMap.range P.toLinearMap = actionIsotype ρ ω := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact compactActionAverage_mem_isotype μ ρ ω P hP u
  · intro u hu
    refine ⟨(μ.real univ : ℂ)⁻¹ • u, ?_⟩
    have hmass : (μ.real univ : ℂ) ≠ 0 := by exact_mod_cast measureReal_univ_pos.ne'
    change P ((μ.real univ : ℂ)⁻¹ • u) = u
    rw [map_smul, compactActionAverage_apply_isotype μ ρ ω P hP hu, smul_smul,
      inv_mul_cancel₀ hmass, one_smul]

/-- Paper: Lemma 4.3.3.1(2), p. 181 and Corollary 4.3.3.3(2), p. 183.
Dividing the average by the total mass gives an idempotent. -/
theorem compactActionAverage_idempotent :
    let Q : E →L[ℂ] E := (μ.real univ)⁻¹ • P
    Q.comp Q = Q := by
  ext u
  let c : ℝ := μ.real univ
  have hc : c ≠ 0 := (measureReal_univ_pos (μ := μ)).ne'
  change (↑c⁻¹ : ℂ) • P ((↑c⁻¹ : ℂ) • P u) = (↑c⁻¹ : ℂ) • P u
  rw [map_smul, compactActionAverage_apply_isotype μ ρ ω P hP
    (compactActionAverage_mem_isotype μ ρ ω P hP u)]
  change (↑c⁻¹ : ℂ) • ((↑c⁻¹ : ℂ) • (c : ℂ) • P u) = _
  rw [smul_smul (↑c⁻¹ : ℂ) (c : ℂ), ← Complex.ofReal_mul, inv_mul_cancel₀ hc,
    Complex.ofReal_one, one_smul]

/-- Paper: (4.3.3.2), p. 181 and (4.3.3.9), p. 183. The averaging operator
induces the norm isomorphism from the quotient by its kernel to the
isotypic subspace with its inherited topology. -/
theorem compactActionAverage_quotient_equiv :
    ∃ e : (E ⧸ P.ker) ≃L[ℂ] actionIsotype ρ ω,
      ∀ u : E, (e (P.ker.mkQ u) : E) = P u := by
  let S := actionIsotype ρ ω
  let c : ℂ := μ.real univ
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (measureReal_univ_pos (μ := μ)).ne'
  have hmem (u : E) : P u ∈ S := compactActionAverage_mem_isotype μ ρ ω P hP u
  let A := P.codRestrict S hmem
  let F := P.ker.liftQL A (by
    intro u hu
    exact Subtype.ext (show P u = 0 from hu))
  let J := P.ker.mkQL.comp (c⁻¹ • S.subtypeL)
  have hfix {u : E} (hu : u ∈ S) : P (c⁻¹ • u) = u := by
    rw [map_smul, compactActionAverage_apply_isotype μ ρ ω P hP hu]
    change c⁻¹ • c • u = u
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hleft : LeftInverse J F := by
    intro q
    obtain ⟨u, rfl⟩ := P.ker.mkQ_surjective q
    apply (Submodule.Quotient.eq P.ker).mpr
    change P (c⁻¹ • P u - u) = 0
    rw [map_sub, hfix (hmem u), sub_self]
  have hright : RightInverse J F := fun y ↦ Subtype.ext (hfix y.property)
  exact ⟨ContinuousLinearEquiv.equivOfInverse F J hleft hright, fun _ ↦ rfl⟩

omit hρ [CompactSpace G] [T2Space G] in
/-- Applying the average after an action multiplies the average by the character. -/
private theorem compactActionAverage_apply_action (g : G) (u : E) :
    P (ρ g u) = (ω g : ℂ) • P u := by
  have : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro φ
  rw [map_smul, compactActionAverage_dual_apply μ ρ ω P hP (ρ g u) φ,
    compactActionAverage_dual_apply μ ρ ω P hP u φ, smul_eq_mul, ← integral_const_mul,
    ← integral_mul_right_eq_self (μ := μ) (fun a ↦ (ω g : ℂ) * (star (ω a : ℂ) * φ (ρ a u))) g]
  apply integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  simp only [map_mul, Circle.coe_mul, star_mul', mul_apply_eq_comp]
  rw [mul_assoc (star (ω a : ℂ)), mul_left_comm (ω g : ℂ) (star (ω a : ℂ)),
    ← mul_assoc (ω g : ℂ)]
  simp [← Circle.coe_inv_eq_conj]

/-- Paper: Lemma 4.3.3.1(3), p. 181 and Corollary 4.3.3.3(3), p. 183.
The kernel of the averaging operator is the closed span of the differences
for the character-twisted action. -/
theorem compactActionAverage_ker :
    P.ker = (Submodule.span ℂ
      (range fun p : G × E ↦ p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2)).topologicalClosure := by
  let D := range fun p : G × E ↦ p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2
  let S := (Submodule.span ℂ D).topologicalClosure
  have hdiff (g : G) (u : E) : u - star (ω g : ℂ) • ρ g u ∈ S :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(g, u), rfl⟩)
  apply le_antisymm
  · intro u hu
    change u ∈ S
    by_contra h
    obtain ⟨φ, hφ, hS⟩ := exists_dual_eq_zero_on_submodule_of_notMem S
      (Submodule.isClosed_topologicalClosure _) h
    have horbit (g : G) : φ u = star (ω g : ℂ) * φ (ρ g u) := by
      simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hS _ (hdiff g u)
    have hv := compactActionAverage_dual_apply μ ρ ω P hP u φ
    change P u = 0 at hu
    simp only [hu, map_zero, ← horbit, integral_const, Complex.real_smul] at hv
    exact hφ ((mul_eq_zero.mp hv.symm).resolve_left
      (by exact_mod_cast (measureReal_univ_pos (μ := μ)).ne'))
  · apply Submodule.topologicalClosure_minimal _ _ P.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, u⟩, rfl⟩
    change P (u - star (ω g : ℂ) • ρ g u) = 0
    rw [map_sub, map_smul, compactActionAverage_apply_action μ ρ ω P hP, smul_smul]
    simp [← Circle.coe_inv_eq_conj]

end CompactAverageProperties

section HilbertProjectors

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (ν : Measure G) [ν.IsHaarMeasure]
  (ν₁ : Measure m.toMonoidHom.ker) [ν₁.IsHaarMeasure]

local notation "K" => m.toMonoidHom.ker
local notation "ρ₁" => MonoidHom.comp (regularL2Action ν) (Subgroup.subtype K)

/-- Paper: Corollary 4.3.3.4, p. 184. The unnormalized Hilbert operator
is also the Pettis operator for the restricted regular action. -/
theorem regularIsotypicIntegral_isPettisAverage (ω : PontryaginDual K) :
    IsPettisIsotypicAverageOn ν₁ univ ρ₁ ω (regularIsotypicIntegral m hm ν ν₁ ω) := by sorry

/-- Paper: Corollary 4.3.3.4, p. 184. The normalized average is the
orthogonal projection onto the isotype. The projected vector lies in
the isotype and the difference is perpendicular to that entire subspace. -/
theorem regularIsotypicIntegral_orthogonalProjection (ω : PontryaginDual K)
    (f : RegularL2 ν) :
    let S := actionIsotype ρ₁ ω
    let p := (ν₁.real univ)⁻¹ • regularIsotypicIntegral m hm ν ν₁ ω f
    p ∈ S ∧ f - p ∈ Sᗮ := by sorry

/-- Paper: Corollary 4.3.3.4, p. 184. Distinct isotypic subspaces of Haar L²
are orthogonal. -/
theorem regularL2_isotypes_orthogonal (ω χ : PontryaginDual K) (h : ω ≠ χ) :
    ∀ f ∈ actionIsotype ρ₁ ω, ∀ g ∈ actionIsotype ρ₁ χ, ⟪f, g⟫_ℂ = 0 := by sorry

end HilbertProjectors

end RiemannMasullo
