module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Compact
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle

/-!
# Differential operators, Poisson summation, supports and translations

Masullo, §§D.1.6–D.1.9, pp. 765–783.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal TensorProduct Topology

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section DifferentialOperators

/-- Paper: Definition D.1.6.1, p. 765. The topological Lie algebra is the
space of continuous one-parameter subgroups with the compact-open topology. -/
abbrev LCATopologicalLie (G : Type*) [Group G] [TopologicalSpace G] :=
  Multiplicative ℝ →ₜ* G

/-- Paper: Definition D.1.6.1, p. 765. Each one-parameter subgroup of the real
line is scalar multiplication by its value at time one.
Deviation: Sanity check on the additive real line. -/
theorem lcaTopologicalLie_real (a : LCATopologicalLie (Multiplicative ℝ)) (t : ℝ) :
    (a (Multiplicative.ofAdd t)).toAdd =
      t * (a (Multiplicative.ofAdd 1)).toAdd := by
  let f : ℝ →+ ℝ := AddMonoidHom.toMultiplicative.symm a.toMonoidHom
  have hf : Continuous f := a.continuous
  change f t = t * f 1
  simpa only [smul_eq_mul, mul_one] using map_real_smul f hf t (1 : ℝ)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

-- TODO(paper-gap): D.1.6.4 claims local compactness of the compact-open hom groups.
-- For the countable product of circles the one-parameter subgroup space is ℝ^ℕ.

omit hT2 in
/-- If evaluation identifies `G` with its Pontryagin bidual, transposing character
evaluation gives the inverse to dualizing one-parameter subgroups. -/
theorem lcaTopologicalLie_dual_of_bidual
    (eG : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (heG : ∀ x χ, eG x χ = χ x) :
    ∃ e : LCATopologicalLie G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  let evalReal := pontryaginDual_eval (G := Multiplicative ℝ)
  let eGinv : PontryaginDual (PontryaginDual G) →ₜ* G := eG.symm
  let dual := PontryaginDual.mapHom (Multiplicative ℝ) G
  let inverse (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)) :
      LCATopologicalLie G :=
    eGinv.comp ((PontryaginDual.map b).comp evalReal)
  have hEval (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ))
      (t : Multiplicative ℝ) (χ : PontryaginDual G) : χ (inverse b t) = b χ t := by
    calc
      χ (inverse b t) = eG (inverse b t) χ := (heG _ _).symm
      _ = evalReal t (b χ) := by
        change eG (eG.symm (PontryaginDual.map b (evalReal t))) χ = _
        rw [eG.apply_symm_apply, PontryaginDual.map_apply]
      _ = b χ t := rfl
  have hLeft : Function.LeftInverse inverse dual := by
    intro a
    apply ContinuousMonoidHom.ext
    intro t
    apply eG.injective
    apply PontryaginDual.ext
    intro χ
    rw [heG, heG, hEval (dual a)]
    rfl
  have hRight : Function.RightInverse inverse dual :=
    fun b ↦ ContinuousMonoidHom.ext fun χ ↦ PontryaginDual.ext fun t ↦ hEval b t χ
  have hCont : Continuous inverse :=
    eGinv.continuous_comp_right.comp
      (evalReal.continuous_comp_left.comp
        (PontryaginDual.mapHom (PontryaginDual G) (PontryaginDual (Multiplicative ℝ))).continuous)
  exact ⟨{ toFun := dual
           invFun := inverse
           left_inv := hLeft
           right_inv := hRight
           map_mul' := map_mul dual
           continuous_toFun := dual.continuous
           continuous_invFun := hCont }, fun _ ↦ rfl⟩

/-- Paper: Lemma D.1.6.4, p. 766. Precomposition of characters with a
one-parameter subgroup gives the canonical compact-open topological group isomorphism.
Deviation: The local compactness assertion fails for an infinite product of circles. -/
theorem lcaTopologicalLie_dual :
    ∃ e : LCATopologicalLie G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  obtain ⟨eG, heG⟩ := pontryaginDual_bidual (G := G)
  exact lcaTopologicalLie_dual_of_bidual eG heG

/-- Paper: Definition D.1.6.5, p. 766. Differentiate the orbit curve of a
function along a one-parameter subgroup at time zero. -/
def bruhatDirectionalDeriv (a : LCATopologicalLie G) (f : G → ℂ) (x : G) : ℂ :=
  deriv (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0

omit hTop hT2 hLC in
/-- Paper: Definition D.1.6.5, p. 766. Differentiation along the identity
one-parameter subgroup of the real line recovers the ordinary derivative.
Deviation: Sanity check on the additive real line. -/
theorem bruhatDirectionalDeriv_real
    (a : LCATopologicalLie (Multiplicative ℝ))
    (ha : ∀ t, a (Multiplicative.ofAdd t) = Multiplicative.ofAdd t)
    (f : Multiplicative ℝ → ℂ) (x : ℝ) :
    bruhatDirectionalDeriv a f (Multiplicative.ofAdd x) =
      deriv (f ∘ Multiplicative.ofAdd) x := by
  simp only [bruhatDirectionalDeriv, ha]
  change deriv (fun t : ℝ ↦ (f ∘ Multiplicative.ofAdd) (x + t)) 0 = _
  rw [deriv_comp_const_add, add_zero]

/-- Every point belongs to the open subgroup of a structural pair with the given good subgroup. -/
private theorem exists_bruhatStructuralPair_mem (k : Subgroup G) (hk : IsBruhatGoodSubgroup k)
    (x : G) : ∃ p : BruhatStructuralPair G, OrderDual.ofDual p.val.2 = k ∧ x ∈ p.val.1 := by
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := PontryaginDual G)
  have hCompact : IsCompact (k : Set G) := by
    refine (isClosedEmbedding_pontryaginDual_eval.isCompact_preimage
      (hPolar _ (hk.2.1.mem_nhds (lcaAnnihilator k).one_mem))).of_isClosed_subset hk.1 ?_
    intro y hy χ hχ
    change χ y ∈ Metric.closedBall 1 r
    rw [(mem_lcaAnnihilator_iff k χ).mp hχ ⟨y, hy⟩]
    exact Metric.mem_closedBall_self hr.le
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hK : IsCompact K := (hUc.union hCompact).insert x
  have hK₁ : K ∈ 𝓝 (1 : G) :=
    mem_of_superset hU (subset_union_left.trans (subset_insert _ _))
  have hH : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hK₁ Subgroup.subset_closure)
  have hGen : IsCompactlyGeneratedGroup H :=
    ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK₁,
      IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
        (Subtype.range_coe.symm ▸ Subgroup.subset_closure),
      Subgroup.closure_preimage_eq_top K⟩
  exact ⟨⟨(H, OrderDual.toDual k), hH, hGen, hk,
    fun y hy ↦ Subgroup.subset_closure (mem_insert_of_mem _ (Or.inr hy))⟩,
    rfl, Subgroup.subset_closure (mem_insert _ _)⟩

omit hT2 hLC in
/-- On an elementary presentation of a structural quotient, a translated one-parameter
subgroup lifts to an affine line in the real and torus cover of a single discrete fiber. -/
private theorem contDiff_bruhatOrbit_of_presentation (a : LCATopologicalLie G) {f : G → ℂ}
    (p : BruhatStructuralPair G) {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (e : p.quotient ≃ₜ* Multiplicative (ElementaryLieGroup m n r F))
    (f₀ : p.quotient → ℂ) (hf₀ : ∀ x : p.val.1, f₀ (QuotientGroup.mk x) = f x.val)
    (hCover : ∀ (z : Fin r → ℤ) (b : F),
      ContDiff ℝ 1 (fun xt ↦ f₀ (e.symm (Multiplicative.ofAdd (elementaryCover xt z b)))))
    (x : p.val.1) :
    ContDiff ℝ 1 (fun t : ℝ ↦ f (x.val * a (Multiplicative.ofAdd t))) := by
  have haMem (t : ℝ) : a (Multiplicative.ofAdd t) ∈ p.val.1 := by
    have haCont : Continuous (fun t : ℝ ↦ a (Multiplicative.ofAdd t)) := a.continuous
    exact isPreconnected_range haCont |>.subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨0, map_one a⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let aH : Multiplicative ℝ →* p.val.1 := a.toMonoidHom.codRestrict p.val.1 haMem
  let q : p.val.1 →* p.quotient := QuotientGroup.mk' _
  let c : ℝ →+ ElementaryLieGroup m n r F :=
    AddMonoidHom.toMultiplicative.symm (e.toMulEquiv.toMonoidHom.comp (q.comp aH))
  have hc : Continuous c :=
    e.continuous.comp (QuotientGroup.continuous_mk.comp (a.continuous.subtype_mk haMem))
  let cR := (AddMonoidHom.fst _ _).comp c
  let cT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c)
  have hR (t : ℝ) : (c t).1 = t • (c 1).1 := by
    change cR t = t • cR 1
    simpa only [smul_eq_mul, mul_one] using
      map_real_smul cR (continuous_fst.comp hc) t (1 : ℝ)
  choose v hv using fun i : Fin n ↦ exists_addCircle_coe_mul_eq
    ((Pi.evalAddMonoidHom _ i).comp cT) ((continuous_apply i).comp hc.snd.fst)
  have hD (t : ℝ) : (c t).2.2 = 0 := by
    have h := hc.snd.snd.isConst_of_preconnectedSpace t 0
    rw [map_zero c] at h
    exact h
  let y := (e (q x)).toAdd
  obtain ⟨u, hu⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  let w := (y.1, u)
  let d := ((c 1).1, WithLp.toLp 2 v)
  have hLine (t : ℝ) : elementaryCover (w + t • d) y.2.2.1 y.2.2.2 = y + c t := by
    refine Prod.ext (congrArg (y.1 + ·) (hR t).symm) (Prod.ext ?_ ?_)
    · funext i
      have hui := congrArg (fun z : ElementaryLieGroup m n r F ↦ z.2.1 i) hu
      change ((u i + t * v i : ℝ) : AddCircle (1 : ℝ)) = y.2.1 i + (c t).2.1 i
      rw [AddCircle.coe_add, show (u i : AddCircle (1 : ℝ)) = y.2.1 i from hui, hv i t]
      rfl
    · change y.2.2 = y.2.2 + (c t).2.2
      rw [hD, add_zero]
  have hOrbit (t : ℝ) :
      f (x.val * a (Multiplicative.ofAdd t)) =
        f₀ (e.symm (Multiplicative.ofAdd
          (elementaryCover (w + t • d) y.2.2.1 y.2.2.2))) := by
    rw [hLine]
    change f ((x * aH (Multiplicative.ofAdd t)).val) =
      f₀ (e.symm (e (q x) * e (q (aH (Multiplicative.ofAdd t)))))
    rw [← map_mul, e.symm_apply_apply, ← map_mul]
    exact (hf₀ _).symm
  simp only [hOrbit]
  exact (hCover y.2.2.1 y.2.2.2).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- A structural pair can be restricted around a point while keeping its good subgroup,
so that the new quotient has an elementary presentation. The original pair itself
has such a presentation by Lemma D.1.5.2(1). -/
theorem BruhatStructuralPair.exists_elementary_subpair_mem
    (p : BruhatStructuralPair G) (x : p.val.1) :
    ∃ q : BruhatStructuralPair G, q.val.1 ≤ p.val.1 ∧
      OrderDual.ofDual q.val.2 = OrderDual.ofDual p.val.2 ∧
      x.val ∈ q.val.1 ∧ Nonempty (ElementaryLCAPresentation q.quotient) :=
  ⟨p, le_rfl, rfl, x.property, p.elementary⟩

/-- Paper: Definition D.1.6.5, p. 766. For a Bruhat C¹ function the orbit
derivative exists at time zero for every starting point. -/
theorem hasDerivAt_bruhatDirectionalDeriv (a : LCATopologicalLie G) {f : G → ℂ}
    (hf : IsBruhatContDiff 1 f) (x : G) :
    HasDerivAt (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t)))
      (bruhatDirectionalDeriv a f x) 0 := by
  obtain ⟨k, hk, _, hDescent⟩ := hf
  obtain ⟨p, hp, hx⟩ := exists_bruhatStructuralPair_mem k hk x
  obtain ⟨q, _, hq, hxq, ⟨e⟩⟩ := p.exists_elementary_subpair_mem ⟨x, hx⟩
  obtain ⟨f₀, hf₀, hCover⟩ := hDescent q (hq.trans hp)
  have h : ContDiff ℝ 1 (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) :=
    contDiff_bruhatOrbit_of_presentation a q
      (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
      e.equiv f₀ hf₀ (hCover e) ⟨x, hxq⟩
  exact (h.differentiable one_ne_zero 0).hasDerivAt

-- TODO(paper-gap): The proofs of D.1.6.6 and D.1.6.7 use support in an open
-- compactly generated subgroup. A global smooth function need not have such support.

omit hTop hT2 hLC in
/-- Paper: Lemma D.1.6.6, p. 767. On an elementary group, differentiability of
class C¹ on each lifted discrete fiber gives continuity of the orbit derivative. -/
private theorem continuous_elementary_orbitDeriv {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (a : ℝ →+ ElementaryLieGroup m n r F) (ha : Continuous a)
    {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ z b, ContDiff ℝ 1 (fun u ↦ f (elementaryCover u z b))) :
    Continuous (fun x ↦ deriv (fun t ↦ f (x + a t)) 0) := by
  let V := EuclideanSpace ℝ (Fin m)
  let W := EuclideanSpace ℝ (Fin n)
  let D := (Fin r → ℤ) × F
  let aV : ℝ →+ V := (AddMonoidHom.fst _ _).comp a
  have haV : Continuous aV := continuous_fst.comp ha
  have hD (t : ℝ) : (a t).2.2 = 0 := by
    have hc : Continuous (fun t ↦ (a t).2.2) := continuous_snd.comp (continuous_snd.comp ha)
    have hconst : (a t).2.2 = (a 0).2.2 :=
      (isPreconnected_range hc).subsingleton (mem_range_self t) (mem_range_self 0)
    exact hconst.trans (by rw [map_zero]; rfl)
  -- The lift through each circle cover is additive by uniqueness of lifts.
  have hLift (i : Fin n) : ∃ v : ℝ, ∀ t : ℝ, ((t * v : ℝ) : AddCircle (1 : ℝ)) = (a t).2.1 i := by
    let q : ℝ → AddCircle (1 : ℝ) := (↑)
    let g : C(ℝ, AddCircle (1 : ℝ)) :=
      ⟨fun t ↦ (a t).2.1 i, (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp ha))⟩
    have hg0 : q 0 = g 0 := by simp [q, g, a.map_zero]
    have hq := AddCircle.isCoveringMap_coe (1 : ℝ)
    obtain ⟨b, ⟨hb0, hb⟩, _⟩ := hq.existsUnique_continuousMap_lifts g 0 0 hg0
    have hb' (t : ℝ) : q (b t) = (a t).2.1 i := congrFun hb t
    have hadd (s t : ℝ) : b (s + t) = b s + b t := by
      have heq : q ∘ (fun p : ℝ × ℝ ↦ b (p.1 + p.2)) =
          q ∘ (fun p : ℝ × ℝ ↦ b p.1 + b p.2) := by
        funext p
        change q (b (p.1 + p.2)) = q (b p.1 + b p.2)
        rw [show q (b p.1 + b p.2) = q (b p.1) + q (b p.2) from QuotientAddGroup.mk_add _ _ _,
          hb', hb', hb', map_add]
        rfl
      exact congrFun (hq.eq_of_comp_eq (b.continuous.comp (continuous_fst.add continuous_snd))
        ((b.continuous.comp continuous_fst).add (b.continuous.comp continuous_snd))
        heq (0, 0) (by simp [hb0])) (s, t)
    let bHom : ℝ →+ ℝ := ⟨⟨b, hb0⟩, hadd⟩
    refine ⟨b 1, fun t ↦ ?_⟩
    have ht : b t = t * b 1 := by
      change bHom t = t * bHom 1
      simpa only [smul_eq_mul, mul_one] using map_real_smul bHom b.continuous t (1 : ℝ)
    rw [← ht]
    exact hb' t
  choose w hw using hLift
  let v : V × W := (aV 1, WithLp.toLp 2 w)
  have hOrbit (u : V × W) (d : D) (t : ℝ) :
      elementaryCover u d.1 d.2 + a t = elementaryCover (u + t • v) d.1 d.2 := by
    have ht : aV t = t • aV 1 := by
      simpa only [smul_eq_mul, mul_one] using map_real_smul aV haV t (1 : ℝ)
    change (u.1 + aV t, (fun i ↦ (u.2 i : AddCircle (1 : ℝ)) + (a t).2.1 i),
      d + (a t).2.2) = (u.1 + t • v.1, (fun i ↦ ((u.2 i + t * w i : ℝ) : AddCircle (1 : ℝ))), d)
    simp only [ht, v, hD, add_zero, QuotientAddGroup.mk_add, hw]
  let q : (V × W) × D → ElementaryLieGroup m n r F :=
    fun p ↦ elementaryCover p.1 p.2.1 p.2.2
  have hqW : IsOpenQuotientMap (fun u : W ↦ fun i ↦ (u i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  have hq : IsOpenQuotientMap q :=
    (Homeomorph.prodAssoc V (Fin n → AddCircle (1 : ℝ)) D).isOpenQuotientMap.comp
      ((IsOpenQuotientMap.id.prodMap hqW).prodMap IsOpenQuotientMap.id)
  apply hq.continuous_comp_iff.mp
  rw [continuous_iff_continuousAt]
  intro p
  let g (d : D) (u : V × W) := f (elementaryCover u d.1 d.2)
  have hg (d : D) : ContDiff ℝ 1 (g d) := hf d.1 d.2
  have hd : ∀ᶠ p' : (V × W) × D in 𝓝 p, p'.2 = p.2 :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_discrete {p.2}).mem_nhds (mem_singleton _))
  have hEq (u : V × W) (d : D) :
      deriv (fun t ↦ f (elementaryCover u d.1 d.2 + a t)) 0 = fderiv ℝ (g d) u v := by
    have hPath : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have hBase : (fun t : ℝ ↦ u + t • v) 0 = u := by simp
    have hFDeriv := ((hg d).differentiable one_ne_zero (u + (0 : ℝ) • v)).hasFDerivAt
    have hDeriv := (hFDeriv.comp_hasDerivAt 0 hPath).deriv
    simp only [hBase] at hDeriv
    simpa only [Function.comp_def, g, hOrbit] using hDeriv
  refine (((hg p.2).continuous_fderiv_apply one_ne_zero).comp
    (continuous_fst.prodMk (continuous_const (y := v)))).continuousAt.congr ?_
  filter_upwards [hd] with p' hp'
  exact hp' ▸ (hEq p'.1 p'.2).symm

/-- A good subgroup is contained, together with any prescribed point, in an
open compactly generated subgroup. -/
private theorem exists_structuralPair_at (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) (x : G) :
    ∃ p : BruhatStructuralPair G, x ∈ p.val.1 ∧ OrderDual.ofDual p.val.2 = k := by
  let J := lcaAnnihilator k
  let : DiscreteTopology (PontryaginDual G ⧸ J) := QuotientGroup.discreteTopology hk.2.1
  let π : PontryaginDual G →ₜ* (PontryaginDual G ⧸ J) :=
    ⟨QuotientGroup.mk' J, QuotientGroup.continuous_mk⟩
  let eval := pontryaginDual_eval (G := G)
  -- The dual of the discrete quotient is compact, and evaluation is a closed embedding.
  have hkCompact : IsCompact (k : Set G) := by
    have hRange : IsCompact (range (PontryaginDual.map π)) :=
      isCompact_range (PontryaginDual.map π).continuous
    have hkPreimage : (k : Set G) = eval ⁻¹' range (PontryaginDual.map π) := by
      ext y
      change y ∈ k ↔ eval y ∈ range (PontryaginDual.map π)
      rw [← lcaDualAnnihilator_annihilator k hk.1, mem_lcaDualAnnihilator_iff]
      constructor
      · intro hy
        let χ : PontryaginDual (PontryaginDual G ⧸ J) :=
          { toMonoidHom := QuotientGroup.lift J (eval y).toMonoidHom (fun z hz ↦ hy ⟨z, hz⟩)
            continuous_toFun := (QuotientGroup.isQuotientMap_mk J).continuous_iff.mpr
              (eval y).continuous }
        exact ⟨χ, PontryaginDual.ext fun _ ↦ rfl⟩
      · rintro ⟨χ, hχ⟩ z
        change eval y z.val = 1
        rw [← hχ, PontryaginDual.map_apply]
        have hz : π z.val = 1 := (QuotientGroup.eq_one_iff z.val).mpr z.property
        rw [hz, map_one]
    rw [hkPreimage]
    exact isClosedEmbedding_pontryaginDual_eval.isCompact_preimage hRange
  obtain ⟨U, hU, hUnhds⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hSub : K ⊆ (H : Set G) := Subgroup.subset_closure
  have hK : K ∈ 𝓝 (1 : G) :=
    mem_of_superset hUnhds (subset_union_left.trans (subset_insert _ _))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hK hSub)
  have hGenerated : IsCompactlyGeneratedGroup H :=
    ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
        ((hU.union hkCompact).insert x), Subgroup.closure_preimage_eq_top K⟩
  exact ⟨⟨(H, OrderDual.toDual k), hH, hGenerated, hk,
    subset_union_right.trans ((subset_insert _ _).trans hSub)⟩, hSub (mem_insert _ _), rfl⟩

/-- Paper: Lemma D.1.6.6, p. 767. An open structural subgroup can be shrunk around
a prescribed point, keeping the same good subgroup, so that the quotient has an
elementary presentation.
Deviation: Local form of the reduction to elementary groups. The original pair itself
has an elementary quotient by Lemma D.1.5.2(1). -/
theorem BruhatStructuralPair.exists_elementary_refinement (p : BruhatStructuralPair G)
    (x : p.val.1) :
    ∃ q : BruhatStructuralPair G, q.val.1 ≤ p.val.1 ∧ x.val ∈ q.val.1 ∧
      OrderDual.ofDual q.val.2 = OrderDual.ofDual p.val.2 ∧
      Nonempty (ElementaryLCAPresentation q.quotient) :=
  ⟨p, le_rfl, x.property, rfl, p.elementary⟩

/-- Paper: Lemma D.1.6.6, p. 767. A first derivative of a Bruhat C¹ function
is continuous. -/
theorem bruhatDirectionalDeriv_continuous (a : LCATopologicalLie G) {f : G → ℂ}
    (hf : IsBruhatContDiff 1 f) :
    Continuous (bruhatDirectionalDeriv a f) := by
  obtain ⟨k, hk, _, hDescend⟩ := hf
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨p₀, hx₀, hp₀⟩ := exists_structuralPair_at k hk x
  obtain ⟨p, _, hx, hp, ⟨e⟩⟩ := p₀.exists_elementary_refinement ⟨x, hx₀⟩
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend p (hp.trans hp₀)
  let H := p.val.1
  have hH : IsOpen (H : Set G) := p.property.1
  have ha (t : Multiplicative ℝ) : a t ∈ H := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    have hRange : IsPreconnected (range a) := isPreconnected_range a.continuous
    exact hRange.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩
      ⟨1, ⟨1, map_one a⟩, H.one_mem⟩ (mem_range_self t)
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let φ := e.equiv
  let aH : Multiplicative ℝ →* H := a.toMonoidHom.codRestrict H ha
  let q : H →* p.quotient := QuotientGroup.mk' _
  let aq : Multiplicative ℝ →* Multiplicative E := φ.toMulEquiv.toMonoidHom.comp (q.comp aH)
  let aE : ℝ →+ E := AddMonoidHom.toMultiplicative.symm aq
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hφ : Continuous φ := φ.continuous
  have haE : Continuous aE := hφ.comp (hq.comp (a.continuous.subtype_mk ha))
  let g : E → ℂ := fun y ↦ f₀ (φ.symm (Multiplicative.ofAdd y))
  have hDeriv := continuous_elementary_orbitDeriv aE haE (f := g) (hSmooth e)
  have hCont : Continuous (fun y : H ↦ deriv (fun t : ℝ ↦ g ((φ (q y)).toAdd + aE t)) 0) :=
    hDeriv.comp (hφ.comp hq)
  have hEq (y : H) :
      deriv (fun t : ℝ ↦ g ((φ (q y)).toAdd + aE t)) 0 = bruhatDirectionalDeriv a f y.val := by
    unfold bruhatDirectionalDeriv
    congr 1
    funext t
    let b := aH (Multiplicative.ofAdd t)
    change f₀ (φ.symm (φ (q y) * φ (q b))) = f (y.val * a (Multiplicative.ofAdd t))
    rw [← show φ (q y * q b) = φ (q y) * φ (q b) from φ.map_mul _ _,
      φ.symm_apply_apply, ← map_mul q]
    exact hf₀ (y * b)
  rw [show (fun y : H ↦ deriv (fun t : ℝ ↦ g ((φ (q y)).toAdd + aE t)) 0) =
      bruhatDirectionalDeriv a f ∘ (Subtype.val : H → G) from funext hEq] at hCont
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hCont.continuousAt (x := (⟨x, hx⟩ : H)))

omit hTop hT2 hLC in
/-- Translation by an elementary one-parameter subgroup lifts on each discrete fiber
to translation by a real multiple of a fixed vector. -/
private theorem exists_elementaryCover_translation {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (c : ℝ →+ ElementaryLieGroup m n r F) (hc : Continuous c) :
    ∃ v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n),
      ∀ u (z : Fin r → ℤ) (b : F) (t : ℝ),
        elementaryCover (u + t • v) z b = elementaryCover u z b + c t := by
  let cR := (AddMonoidHom.fst _ _).comp c
  let cT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c)
  have hR (t : ℝ) : (c t).1 = t • (c 1).1 := by
    change cR t = t • cR 1
    simpa only [smul_eq_mul, mul_one] using map_real_smul cR hc.fst t (1 : ℝ)
  choose w hw using fun i : Fin n ↦ exists_addCircle_coe_mul_eq
    ((Pi.evalAddMonoidHom _ i).comp cT) ((continuous_apply i).comp hc.snd.fst)
  have hD (t : ℝ) : (c t).2.2 = 0 := by
    have h := hc.snd.snd.isConst_of_preconnectedSpace t 0
    rw [map_zero c] at h
    exact h
  refine ⟨((c 1).1, WithLp.toLp 2 w), fun u z b t ↦ ?_⟩
  refine Prod.ext (congrArg (u.1 + ·) (hR t).symm) (Prod.ext ?_ ?_)
  · funext i
    change ((u.2 i + t * w i : ℝ) : AddCircle (1 : ℝ)) =
      (u.2 i : AddCircle (1 : ℝ)) + (c t).2.1 i
    rw [AddCircle.coe_add, hw i t]
    rfl
  · change (z, b) = (z, b) + (c t).2.2
    rw [hD, add_zero]

omit hT2 hLC in
/-- On each structural quotient, differentiation along a one-parameter subgroup
lowers the order of Bruhat differentiability by one and preserves the good subgroup. -/
private theorem IsBruhatContDiff.directionalDeriv {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff (p + 1) f) (a : LCATopologicalLie G) :
    IsBruhatContDiff p (bruhatDirectionalDeriv a f) := by
  obtain ⟨k, hk, hInv, hDescent⟩ := hf
  refine ⟨k, hk, ?_, ?_⟩
  · intro h x
    simp only [bruhatDirectionalDeriv, mul_assoc, hInv]
  · intro q hq
    obtain ⟨f₀, hf₀, hSmooth⟩ := hDescent q hq
    have ha (t : Multiplicative ℝ) : a t ∈ q.val.1 := by
      let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
      exact (isPreconnected_range a.continuous).subset_isClopen
        ⟨q.val.1.isClosed_of_isOpen q.property.1, q.property.1⟩
        ⟨1, ⟨1, map_one a⟩, q.val.1.one_mem⟩ (mem_range_self t)
    let aH := a.toMonoidHom.codRestrict q.val.1 ha
    let π : q.val.1 →* q.quotient := QuotientGroup.mk' _
    let aQ := π.comp aH
    let df₀ (y : q.quotient) := deriv (fun t : ℝ ↦ f₀ (y * aQ (Multiplicative.ofAdd t))) 0
    refine ⟨df₀, ?_, ?_⟩
    · intro x
      unfold df₀ bruhatDirectionalDeriv
      congr 1
      funext t
      change f₀ (π x * π (aH (Multiplicative.ofAdd t))) = _
      rw [← map_mul π]
      exact hf₀ (x * aH (Multiplicative.ofAdd t))
    · intro e z b
      let c := AddMonoidHom.toMultiplicative.symm (e.equiv.toMulEquiv.toMonoidHom.comp aQ)
      have hc : Continuous c :=
        e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (a.continuous.subtype_mk ha))
      obtain ⟨v, hv⟩ := exists_elementaryCover_translation c hc
      let g := fun u ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z b)))
      have hg : ContDiff ℝ ((p : ℕ∞) + 1) g := by
        simpa only [Nat.cast_add, Nat.cast_one, WithTop.coe_add, WithTop.coe_one]
          using hSmooth e z b
      have hd : ContDiff ℝ (p : ℕ∞) (fun u ↦ fderiv ℝ g u v) :=
        (hg.contDiff_fderiv_apply le_rfl).comp (contDiff_id.prodMk contDiff_const)
      convert hd using 1
      funext u
      have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
      have hOrbit (t : ℝ) : g (u + t • v) =
          f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z b)) *
            aQ (Multiplicative.ofAdd t)) := by
        dsimp only [g]
        rw [hv]
        change f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z b) *
          e.equiv (aQ (Multiplicative.ofAdd t)))) = _
        rw [map_mul, e.equiv.symm_apply_apply]
      have h := (hg.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine
        (by simp)
      simpa only [df₀, Function.comp_def, hOrbit] using h.deriv

/-- Paper: Lemma D.1.6.6, p. 767. The first derivative of a Bruhat smooth
function is Bruhat smooth. -/
theorem bruhatDirectionalDeriv_mem_smooth (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) :
    bruhatDirectionalDeriv a f ∈ bruhatSmoothSubmodule := by
  have hf := (mem_bruhatSmoothSubmodule_iff f.val).mp f.property
  exact (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦ (hf (p + 1)).directionalDeriv a

/-- Paper: Lemma D.1.6.6, p. 767. The first derivative satisfies the product
rule on pairs of Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_mul (a : LCATopologicalLie G) {f g : G → ℂ}
    (hf : IsBruhatContDiff 1 f) (hg : IsBruhatContDiff 1 g) :
    bruhatDirectionalDeriv a (f * g) =
      f * bruhatDirectionalDeriv a g + g * bruhatDirectionalDeriv a f := by
  funext x
  have h := ((hasDerivAt_bruhatDirectionalDeriv a hf x).fun_mul
    (hasDerivAt_bruhatDirectionalDeriv a hg x)).deriv
  simpa only [bruhatDirectionalDeriv, Pi.mul_apply, Pi.add_apply,
    ofAdd_zero, map_one, mul_one, mul_comm, add_comm] using h

/-- Paper: Definition D.1.6.5, p. 766. The orbit derivative is additive on
Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_add (a : LCATopologicalLie G)
    (f g : bruhatContDiffSubmodule (G := G) 1) :
    bruhatDirectionalDeriv a (f + g : bruhatContDiffSubmodule 1) =
      bruhatDirectionalDeriv a f + bruhatDirectionalDeriv a g := by
  funext x
  have hf := hasDerivAt_bruhatDirectionalDeriv a f.property x
  have hg := hasDerivAt_bruhatDirectionalDeriv a g.property x
  exact (hf.add hg).deriv

/-- Paper: Definition D.1.6.5, p. 766. The orbit derivative commutes with
complex scalar multiplication on Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_smul (a : LCATopologicalLie G)
    (f : bruhatContDiffSubmodule (G := G) 1) (c : ℂ) :
    bruhatDirectionalDeriv a (c • f : bruhatContDiffSubmodule 1) =
      c • bruhatDirectionalDeriv a f := by
  funext x
  simp only [bruhatDirectionalDeriv, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

/-- Paper: Definition D.1.6.5, p. 766. Orbit differentiation is a complex
linear map from Bruhat C¹ functions to continuous functions. -/
def bruhatDirectionalDerivLinear (a : LCATopologicalLie G) :
    bruhatContDiffSubmodule (G := G) 1 →ₗ[ℂ] C(G, ℂ) where
  toFun f := ⟨bruhatDirectionalDeriv a f,
    bruhatDirectionalDeriv_continuous a ((mem_bruhatContDiffSubmodule_iff 1 f.val).mp f.property)⟩
  map_add' f g := ContinuousMap.ext (congrFun (bruhatDirectionalDeriv_add a f g))
  map_smul' c f := ContinuousMap.ext (congrFun (bruhatDirectionalDeriv_smul a f c))

/-- Paper: Definition D.1.6.5, p. 766. Evaluation of the bundled map agrees
with the derivative of the orbit curve. -/
theorem bruhatDirectionalDerivLinear_apply (a : LCATopologicalLie G)
    (f : bruhatContDiffSubmodule (G := G) 1) (x : G) :
    bruhatDirectionalDerivLinear a f x = bruhatDirectionalDeriv a f x := rfl

/-- Paper: Lemma D.1.6.7(1), p. 767. The first-order operator is the complex
linear directional derivative acting on the smooth submodule. -/
def bruhatFirstOrder (a : LCATopologicalLie G) :
    Module.End ℂ (bruhatSmoothSubmodule (G := G)) where
  toFun f := ⟨bruhatDirectionalDeriv a f, bruhatDirectionalDeriv_mem_smooth a f⟩
  map_add' f g := Subtype.ext
    (bruhatDirectionalDeriv_add a ⟨f, (Submodule.mem_iInf _).mp f.property 1⟩
      ⟨g, (Submodule.mem_iInf _).mp g.property 1⟩)
  map_smul' c f := Subtype.ext
    (bruhatDirectionalDeriv_smul a ⟨f, (Submodule.mem_iInf _).mp f.property 1⟩ c)

/-- Paper: Lemma D.1.6.7(1), p. 767. Evaluation of the first-order operator
gives the orbit derivative. -/
theorem bruhatFirstOrder_apply (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) (x : G) :
    (bruhatFirstOrder a f : G → ℂ) x = bruhatDirectionalDeriv a f x := rfl

omit [CommGroup G] [TopologicalSpace G] hTop hT2 hLC in
/-- An affine map from a real normed space to an elementary group pulls back
functions that are smooth on each covered discrete fiber to smooth functions. -/
private theorem contDiff_comp_affine_elementary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    {p : ℕ∞} (a : E →+ ElementaryLieGroup m n r F) (ha : Continuous a)
    (c : ElementaryLieGroup m n r F) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ z b, ContDiff ℝ p (fun u ↦ f (elementaryCover u z b))) :
    ContDiff ℝ p (fun x ↦ f (a x + c)) := by
  let aR := (AddMonoidHom.fst _ _).comp a
  let aT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp a)
  choose l hl hlift using fun i : Fin n ↦ exists_addCircle_addMonoidHom_lift
    ((Pi.evalAddMonoidHom _ i).comp aT) ((continuous_apply i).comp ha.snd.fst)
  let aLift : E →+ EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
    aR.prod ((EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap.toAddMonoidHom.comp
      (AddMonoidHom.pi l))
  have hLiftCont : Continuous aLift :=
    ha.fst.prodMk ((PiLp.continuous_toLp 2 _).comp (continuous_pi hl))
  have hDiscrete (x : E) : (a x).2.2 = 0 := by
    have h := ha.snd.snd.isConst_of_preconnectedSpace x 0
    rw [map_zero a] at h
    exact h
  obtain ⟨u, hu⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  have hLift (x : E) :
      elementaryCover (aLift x + (c.1, u)) c.2.2.1 c.2.2.2 = a x + c := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      have hui := congrArg (fun y : ElementaryLieGroup m n r F ↦ y.2.1 i) hu
      change ((l i x + u i : ℝ) : AddCircle (1 : ℝ)) = (a x).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hlift i x]
      exact congrArg ((a x).2.1 i + ·) hui
    · change c.2.2 = (a x).2.2 + c.2.2
      rw [hDiscrete, zero_add]
  simp_rw [← hLift]
  exact (hf _ _).comp ((aLift.toRealLinearMap hLiftCont).contDiff.add contDiff_const)

/-- Left translation preserves each finite order of Bruhat differentiability
with the same good subgroup. -/
private theorem IsBruhatContDiff.comp_mul_left {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff p f) (g : G) : IsBruhatContDiff p (fun x ↦ f (g * x)) := by
  obtain ⟨k, hk, hInv, hDescend⟩ := hf
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · simpa only [mul_left_comm] using hInv h (g * x)
  let I := OpenCompactlyGeneratedSubgroups G
  have hColimit := openCompactlyGeneratedSubgroups_colimit (G := G)
  let : IsDirectedOrder I := hColimit.1
  obtain ⟨J, hgJ⟩ := hColimit.2.1 g
  obtain ⟨H, haH, hJH⟩ := exists_ge_ge (⟨a.val.1, a.property.1, a.property.2.1⟩ : I) J
  have hkA : k ≤ a.val.1 := ha ▸ a.property.2.2.2
  let b : BruhatStructuralPair G :=
    ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, hkA.trans haH⟩
  let i := Subgroup.inclusion (show a.val.1 ≤ H.val from haH)
  let j : a.quotient →* b.quotient := QuotientGroup.map _ _ i (by
    intro x hx
    change (x : G) ∈ OrderDual.ofDual a.val.2 at hx
    change (x : G) ∈ k
    rwa [ha] at hx)
  have hi : Continuous i :=
    (continuous_subtype_val : Continuous ((↑) : a.val.1 → G)).subtype_mk _
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hi)
  let gH : b.val.1 := ⟨g, hJH hgJ⟩
  let qg : b.quotient := QuotientGroup.mk gH
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend b rfl
  refine ⟨fun y ↦ f₀ (qg * j y), fun x ↦ hf₀ (gH * i x), ?_⟩
  obtain ⟨e'⟩ := b.elementary
  intro e z d
  let E := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let S := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let T := ElementaryLieGroup e'.realDim e'.torusDim e'.latticeRank e'.finiteFactor
  let cover : E →+ S :=
    { toFun := fun xt ↦ elementaryCover xt 0 0
      map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
      map_add' := fun x y ↦ Prod.ext rfl
        (Prod.ext (funext fun l ↦ AddCircle.coe_add (1 : ℝ) (x.2 l) (y.2 l)) (zero_add _).symm) }
  have hCover : Continuous cover :=
    continuous_fst.prodMk
      ((continuous_pi fun l ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((PiLp.continuous_apply 2 _ l).comp continuous_snd)).prodMk
          (continuous_const.prodMk continuous_const))
  let L : S →+ T := AddMonoidHom.toMultiplicative.symm
    (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
  have hL : Continuous L := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
  let c : T := (e'.equiv qg).toAdd + L (elementaryCover 0 z d)
  let φ : T → ℂ := fun y ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd y))
  have hAffine (xt : E) :
      φ (L (cover xt) + c) =
        f₀ (qg * j (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z d)))) := by
    have hShift : cover xt + elementaryCover 0 z d = elementaryCover xt z d := by
      refine Prod.ext (add_zero _) (Prod.ext ?_ (zero_add _))
      funext l
      change (xt.2 l : AddCircle (1 : ℝ)) + ((0 : ℝ) : AddCircle (1 : ℝ)) =
        (xt.2 l : AddCircle (1 : ℝ))
      rw [AddCircle.coe_zero, add_zero]
    rw [show L (cover xt) + c =
      (e'.equiv qg).toAdd + (L (cover xt) + L (elementaryCover 0 z d)) from
        add_left_comm _ _ _, ← map_add, hShift]
    change f₀ (e'.equiv.symm (e'.equiv qg * e'.equiv (j _))) = _
    rw [← map_mul, e'.equiv.symm_apply_apply]
    rfl
  simpa only [AddMonoidHom.comp_apply, hAffine] using
    contDiff_comp_affine_elementary (L.comp cover) (hL.comp hCover) c (f := φ) (hSmooth e')

/-- Paper: Lemma D.1.6.7(1), p. 767. The directional derivative commutes
with left translations. -/
theorem bruhatFirstOrder_translate (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) (g : G) :
    ∃ f' : bruhatSmoothSubmodule (G := G),
      (∀ x : G, f'.val x = f.val (g⁻¹ * x)) ∧
      ∀ x : G, (bruhatFirstOrder a f').val x = (bruhatFirstOrder a f).val (g⁻¹ * x) := by
  have hf := (mem_bruhatSmoothSubmodule_iff f.val).mp f.property
  refine ⟨⟨fun x ↦ f.val (g⁻¹ * x), (mem_bruhatSmoothSubmodule_iff _).mpr
    (fun p ↦ (hf p).comp_mul_left g⁻¹)⟩, fun _ ↦ rfl, fun x ↦ ?_⟩
  change deriv (fun t : ℝ ↦ f.val (g⁻¹ * (x * a (Multiplicative.ofAdd t)))) 0 =
    deriv (fun t : ℝ ↦ f.val ((g⁻¹ * x) * a (Multiplicative.ofAdd t))) 0
  simp only [mul_assoc]

/-- Paper: Lemma D.1.6.7(1), p. 767. First-order operators add under
pointwise multiplication of one-parameter subgroups. -/
theorem bruhatFirstOrder_mul (a b : LCATopologicalLie G) :
    bruhatFirstOrder (a * b) = bruhatFirstOrder a + bruhatFirstOrder b := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change bruhatDirectionalDeriv (a * b) f x =
    bruhatDirectionalDeriv a f x + bruhatDirectionalDeriv b f x
  -- Use a structural quotient containing the point and both subgroup images.
  have hf : IsBruhatContDiff 1 (f : G → ℂ) := (Submodule.mem_iInf _).mp f.property 1
  obtain ⟨k, hk, _, hDescent⟩ := hf
  obtain ⟨p, hp, hx⟩ := exists_bruhatStructuralPair_mem k hk x
  obtain ⟨e⟩ := p.elementary
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescent p hp
  have hMem (c : LCATopologicalLie G) (t : Multiplicative ℝ) : c t ∈ p.val.1 := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range c.continuous).subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨1, map_one c⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let lift (c : LCATopologicalLie G) := c.toMonoidHom.codRestrict p.val.1 (hMem c)
  let q := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _ : p.val.1 →* p.quotient)
  let cE (c : LCATopologicalLie G) := AddMonoidHom.toMultiplicative.symm (q.comp (lift c))
  have hcE (c : LCATopologicalLie G) : Continuous (cE c) :=
    e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (c.continuous.subtype_mk (hMem c)))
  have hMul (t : ℝ) : cE (a * b) t = cE a t + cE b t := by
    change (q (lift a (Multiplicative.ofAdd t) * lift b (Multiplicative.ofAdd t))).toAdd = _
    rw [map_mul]
    rfl
  -- Evaluate all three derivatives in the same lift of the discrete fiber.
  obtain ⟨va, ha⟩ := exists_elementaryCover_translation (cE a) (hcE a)
  obtain ⟨vb, hb⟩ := exists_elementaryCover_translation (cE b) (hcE b)
  let y := (q ⟨x, hx⟩).toAdd
  obtain ⟨w, hw⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  let u := (y.1, w)
  let g := fun v ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover v y.2.2.1 y.2.2.2)))
  have hg : HasFDerivAt g (fderiv ℝ g u) u :=
    ((hSmooth e y.2.2.1 y.2.2.2).differentiable_one u).hasFDerivAt
  have hDeriv (c : LCATopologicalLie G) (v : EuclideanSpace ℝ (Fin e.realDim) ×
      EuclideanSpace ℝ (Fin e.torusDim))
      (hv : ∀ t : ℝ, elementaryCover (u + t • v) y.2.2.1 y.2.2.2 = y + cE c t) :
      bruhatDirectionalDeriv c f x = fderiv ℝ g u v := by
    have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have hOrbit (t : ℝ) : g (u + t • v) = (f : G → ℂ) (x * c (Multiplicative.ofAdd t)) := by
      dsimp only [g]
      rw [hv]
      change f₀ (e.equiv.symm (q ⟨x, hx⟩ * q (lift c (Multiplicative.ofAdd t)))) = _
      rw [← map_mul q]
      let z := (⟨x, hx⟩ : p.val.1) * lift c (Multiplicative.ofAdd t)
      change f₀ (e.equiv.symm (e.equiv (QuotientGroup.mk z))) = (f : G → ℂ) z.val
      rw [e.equiv.symm_apply_apply]
      exact hf₀ z
    have h := hg.comp_hasDerivAt_of_eq 0 hLine (by simp)
    simpa only [Function.comp_def, hOrbit, bruhatDirectionalDeriv] using h.deriv
  rw [hDeriv a va (fun t ↦ (ha u _ _ t).trans (congrArg (· + cE a t) hw)),
    hDeriv b vb (fun t ↦ (hb u _ _ t).trans (congrArg (· + cE b t) hw)),
    hDeriv (a * b) (va + vb)]
  · exact map_add (fderiv ℝ g u) va vb
  · intro t
    rw [smul_add, ← add_assoc, hb, ha, hw, add_assoc, hMul]

/-- Paper: Lemma D.1.6.7(1), p. 767. Scaling the real parameter scales
the first-order operator by the same factor. -/
theorem bruhatFirstOrder_scale (a : LCATopologicalLie G) (c : ℝ) :
    let scale : LCATopologicalLie (Multiplicative ℝ) :=
      ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative,
        continuous_const_mul c⟩
    bruhatFirstOrder (a.comp scale) = c • bruhatFirstOrder a := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  let orbit : ℝ → ℂ := fun t ↦ f.val (x * a (Multiplicative.ofAdd t))
  change deriv (fun t ↦ orbit (c * t)) 0 = c • deriv orbit 0
  simpa only [mul_zero] using deriv_comp_mul_left c orbit 0

omit [CommGroup G] [TopologicalSpace G] hTop hT2 hLC in
/-- A weighted mixed partial of a fixed-direction derivative on the elementary cover
is controlled by finitely many seminorms of the original function.
The weights are unchanged and one derivative index is raised by one. -/
private theorem elementarySchwartz_directional_bound {m n r : ℕ} {F : Type*}
    (v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (i : ElementarySchwartzIndex m n r) :
    ∃ p : Seminorm ℂ (ElementarySchwartz m n r F), Continuous p ∧
      ∀ (f : ElementarySchwartz m n r F) (g : ElementaryLieGroup m n r F → ℂ),
        (∀ u z b, g (elementaryCover u z b) =
          fderiv ℝ (fun w ↦ f (elementaryCover w z b)) u v) →
        elementarySchwartzBound g i ≤ ENNReal.ofReal (p f) := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let basis : Module.Basis (Fin m ⊕ Fin n) ℝ X :=
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.prod (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let ν : Fin m ⊕ Fin n → ElementarySchwartzIndex m n r
    | .inl j => (i.1, i.2.1 + Pi.single j 1, i.2.2.1, i.2.2.2)
    | .inr j => (i.1, i.2.1, i.2.2.1 + Pi.single j 1, i.2.2.2)
  let q : Seminorm ℂ (ElementarySchwartz m n r F) :=
    Finset.univ.sup (fun j ↦ elementarySchwartzSeminorm (ν j))
  let C : ℝ≥0 := ∑ j, ‖basis.repr v j‖₊
  have hq : Continuous q := Seminorm.continuous_finsetSup fun j _ ↦
    (withGeneratingSeminorms_spec _ _).continuous_seminorm (ν j)
  refine ⟨C • q, ?_, fun f g hg ↦ ?_⟩
  · exact hq.const_smul (C : ℝ)
  -- Adding a coordinate direction increments its multiplicity in the list of partials.
  let dirs {k : ℕ} (d : Fin k → X) (α : Fin k → ℕ) : List X :=
    (List.ofFn fun j ↦ List.replicate (α j) (d j)).flatten
  have hInsert {k : ℕ} (d : Fin k → X) (α : Fin k → ℕ) (j : Fin k) :
      (d j :: dirs d α).Perm (dirs d (α + Pi.single j 1)) := by
    let indices (α : Fin k → ℕ) :=
      (List.finRange k).flatMap fun l ↦ List.replicate (α l) l
    have hMap (α : Fin k → ℕ) : (indices α).map d = dirs d α := by
      simp only [indices, dirs, List.ofFn_eq_map, List.map_flatMap, List.map_replicate,
        List.flatten_eq_flatMap, List.flatMap_map, id_eq]
    have hCount (α : Fin k → ℕ) (l : Fin k) : (indices α).count l = α l := by
      rw [List.count_flatMap, ← Fin.sum_univ_def]
      simp [List.count_replicate]
    have hPerm : (j :: indices α).Perm (indices (α + Pi.single j 1)) := by
      rw [List.perm_iff_count]
      intro l
      simp only [List.count_cons, hCount, beq_iff_eq, Pi.add_apply, Pi.single_apply, eq_comm (a := j)]
    simpa only [List.map_cons, hMap] using hPerm.map d
  let dR (j : Fin m) : X := (EuclideanSpace.single j 1, 0)
  let dT (j : Fin n) : X := (0, EuclideanSpace.single j 1)
  let R := dirs dR i.2.1
  let S := dirs dT i.2.2.1
  let D := R ++ S
  refine iSup_le fun u ↦ iSup_le fun z ↦ iSup_le fun b ↦ ?_
  let l : X → ℂ := fun w ↦ f (elementaryCover w z b)
  have hl : ContDiff ℝ ∞ l := f.property.1 z b
  let weight : ℂ := (∏ k, (u.1 k : ℂ) ^ i.1 k) * (∏ k, (z k : ℂ) ^ i.2.2.2 k)
  let T : X →L[ℝ] ℂ := iteratedFDeriv ℝ D.length (fderiv ℝ l) u D.get
  have hPartial : elementaryPartial g i.2.1 i.2.2.1 u z b = T v := by
    have hFun : (fun w ↦ g (elementaryCover w z b)) =
        (ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ l := funext fun w ↦ hg w z b
    change iteratedFDeriv ℝ D.length (fun w ↦ g (elementaryCover w z b)) u D.get = T v
    rw [hFun, (ContinuousLinearMap.apply ℝ ℂ v).iteratedFDeriv_comp_left
      (hl.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)]
    rfl
  have hLast (d : X) :
      iteratedFDeriv ℝ (D ++ [d]).length l u (D ++ [d]).get = T d := by
    let eval (s : Σ k, Fin k → X) := iteratedFDeriv ℝ s.1 l u s.2
    have hEval := congrArg eval (List.equivSigmaTuple.apply_symm_apply
      ⟨D.length + 1, Fin.snoc D.get d⟩)
    change iteratedFDeriv ℝ (List.ofFn (Fin.snoc D.get d)).length l u
      (List.ofFn (Fin.snoc D.get d)).get = iteratedFDeriv ℝ (D.length + 1) l u
      (Fin.snoc D.get d) at hEval
    have hList : List.ofFn (Fin.snoc D.get d) = D ++ [d] := by
      rw [List.ofFn_succ', Fin.snoc_last, List.concat_eq_append]
      simp only [Fin.snoc_castSucc, List.ofFn_get]
    rw [hList] at hEval
    rw [hEval, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have hCoord (j : Fin m ⊕ Fin n) :
      T (basis j) = elementaryPartial f (ν j).2.1 (ν j).2.2.1 u z b := by
    cases j with
    | inl j =>
      have hBasis : basis (.inl j) = dR j := by
        apply Prod.ext
        · exact (Module.Basis.prod_apply_inl_fst _ _ j).trans
            (EuclideanSpace.basisFun_apply _ _ j)
        · exact Module.Basis.prod_apply_inl_snd _ _ j
      rw [hBasis, ← hLast]
      have hPerm : (D ++ [dR j]).Perm (dirs dR (i.2.1 + Pi.single j 1) ++ S) :=
        (show (D ++ [dR j]).Perm (dR j :: D) by simp).trans
          ((hInsert dR i.2.1 j).append_right S)
      exact iteratedFDeriv_apply_list_perm hl id hPerm u
    | inr j =>
      have hBasis : basis (.inr j) = dT j := by
        apply Prod.ext
        · exact Module.Basis.prod_apply_inr_fst _ _ j
        · exact (Module.Basis.prod_apply_inr_snd _ _ j).trans
            (EuclideanSpace.basisFun_apply _ _ j)
      rw [hBasis, ← hLast]
      have hPerm : (D ++ [dT j]).Perm (R ++ dirs dT (i.2.2.1 + Pi.single j 1)) := by
        rw [show D = R ++ S from rfl, List.append_assoc]
        have hMove : (S ++ [dT j]).Perm (dT j :: S) := by
          simp
        exact (hMove.trans (hInsert dT i.2.2.1 j)).append_left R
      exact iteratedFDeriv_apply_list_perm hl id hPerm u
  have hPoint (j : Fin m ⊕ Fin n) : ‖weight * T (basis j)‖ ≤ q f := by
    rw [hCoord]
    refine le_trans ?_ (Seminorm.le_finset_sup_apply (Finset.mem_univ j))
    have h : (‖weight * elementaryPartial f (ν j).2.1 (ν j).2.2.1 u z b‖₊ : ℝ≥0∞) ≤
        elementarySchwartzBound f (ν j) := by
      cases j <;> exact le_iSup_of_le u (le_iSup_of_le z (le_iSup_of_le b le_rfl))
    exact ENNReal.toReal_mono (f.property.2 (ν j)).ne h
  rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_le_ofReal_iff (apply_nonneg (C • q) f)]
  change ‖weight * elementaryPartial g i.2.1 i.2.2.1 u z b‖ ≤ _
  rw [hPartial]
  -- Expand the direction in the product basis and bound each term by the same seminorm.
  have hSum : weight * T v = ∑ j, basis.repr v j • (weight * T (basis j)) := by
    conv_lhs => rw [← basis.sum_repr v]
    simp only [map_sum, map_smul, Finset.mul_sum, Algebra.mul_smul_comm]
  calc
    ‖weight * T v‖ ≤ ∑ j, ‖basis.repr v j • (weight * T (basis j))‖ := by
      rw [hSum]
      exact norm_sum_le _ _
    _ ≤ ∑ j, ‖basis.repr v j‖ * q f := by
      simp only [norm_smul]
      exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hPoint j) (norm_nonneg _)
    _ = (C • q) f := by simp [C, ← Finset.sum_mul, smul_apply, NNReal.smul_def]

omit [CommGroup G] [TopologicalSpace G] hTop hT2 hLC in
/-- On every elementary stage an orbit derivative is a continuous linear operator,
and every orbit curve of a stage function is differentiable at zero. -/
private theorem elementarySchwartz_orbitDeriv {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (c : ℝ →+ ElementaryLieGroup m n r F) (hc : Continuous c) :
    ∃ B : ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m n r F,
      ∀ f y, HasDerivAt (fun t : ℝ ↦ f (y + c t)) (B f y) 0 := by
  obtain ⟨v, hv⟩ := exists_elementaryCover_translation c hc
  let D (f : ElementarySchwartz m n r F) (y : ElementaryLieGroup m n r F) :=
    deriv (fun t : ℝ ↦ f (y + c t)) 0
  have hDeriv (f : ElementarySchwartz m n r F) (u) (z) (b) :
      HasDerivAt (fun t : ℝ ↦ f (elementaryCover u z b + c t))
        (fderiv ℝ (fun w ↦ f (elementaryCover w z b)) u v) 0 := by
    have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have h := ((f.property.1 z b).differentiable (by simp) u).hasFDerivAt
    simpa only [Function.comp_def, hv] using h.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hLift (f : ElementarySchwartz m n r F) (u) (z) (b) :
      D f (elementaryCover u z b) = fderiv ℝ (fun w ↦ f (elementaryCover w z b)) u v :=
    (hDeriv f u z b).deriv
  have hDiff (f : ElementarySchwartz m n r F) (y : ElementaryLieGroup m n r F) :
      HasDerivAt (fun t : ℝ ↦ f (y + c t)) (D f y) 0 := by
    obtain ⟨w, hw⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
    change elementaryCover (y.1, w) y.2.2.1 y.2.2.2 = y at hw
    rw [← hw, hLift]
    exact hDeriv f _ _ _
  choose p hp hBound using elementarySchwartz_directional_bound (r := r) (F := F) v
  have hMem (f : ElementarySchwartz m n r F) : D f ∈ elementarySchwartzSubmodule m n r F := by
    refine ⟨fun z b ↦ ?_, fun i ↦ (hBound i f (D f) (fun u z b ↦ hLift f u z b)).trans_lt
      ENNReal.ofReal_lt_top⟩
    simp only [hLift]
    exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp
      ((f.property.1 z b).fderiv_right (m := ∞) (by simp))
  let B : ElementarySchwartz m n r F →ₗ[ℂ] ElementarySchwartz m n r F :=
    { toFun := fun f ↦ ⟨D f, hMem f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦
        ((hDiff f y).add (hDiff g y)).deriv)
      map_smul' := fun d f ↦ Subtype.ext (funext fun y ↦
        ((hDiff f y).const_smul d).deriv) }
  refine ⟨⟨B, ?_⟩, hDiff⟩
  apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp B
  intro i
  apply Seminorm.continuous_of_le (hp i)
  intro f
  change (elementarySchwartzBound (D f) i).toReal ≤ p i f
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hBound i f (D f) (fun u z b ↦ hLift f u z b))).trans_eq
      (ENNReal.toReal_ofReal (apply_nonneg (p i) f))

omit hT2 hLC in
/-- Differentiation on a structural stage agrees with differentiation on its
elementary quotient, including the zero extension off the open subgroup. -/
private theorem schwartzBruhatStage_orbitDeriv (a : LCATopologicalLie G)
    (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient) :
    ∃ B : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e,
      ∀ f x, HasDerivAt (fun t : ℝ ↦ schwartzBruhatStageRealization p e f
        (x * a (Multiplicative.ofAdd t))) (schwartzBruhatStageRealization p e (B f) x) 0 := by
  classical
  have hMem (t : Multiplicative ℝ) : a t ∈ p.val.1 := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range a.continuous).subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨1, map_one a⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let aH := a.toMonoidHom.codRestrict p.val.1 hMem
  let q := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _ : p.val.1 →* p.quotient)
  let c := AddMonoidHom.toMultiplicative.symm (q.comp aH)
  have hc : Continuous c :=
    e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (a.continuous.subtype_mk hMem))
  obtain ⟨B, hB⟩ := elementarySchwartz_orbitDeriv c hc
  refine ⟨B, fun f x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ p.val.1
  · rw [dite_eq_left hx]
    let y := (q ⟨x, hx⟩).toAdd
    have hEq (t : ℝ) : schwartzBruhatStageRealization p e f
        (x * a (Multiplicative.ofAdd t)) = f (y + c t) := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_left (p.val.1.mul_mem hx (hMem _))]
      change f (q (⟨x, hx⟩ * aH (Multiplicative.ofAdd t))).toAdd = f (y + c t)
      rw [map_mul q]
      rfl
    simp only [hEq]
    exact hB f y
  · rw [dite_eq_right hx]
    have hEq (t : ℝ) : schwartzBruhatStageRealization p e f
        (x * a (Multiplicative.ofAdd t)) = 0 := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_right]
      exact fun ht ↦ hx ((p.val.1.mul_mem_cancel_right (hMem _)).mp ht)
    simp only [hEq]
    exact hasDerivAt_const 0 (0 : ℂ)

include hT2 hLC in
/-- Paper: Lemma D.1.6.7(1), p. 767. The directional derivative restricts
to a continuous complex linear endomorphism of the Schwartz–Bruhat space. -/
theorem bruhatFirstOrder_schwartz :
    ∀ a : LCATopologicalLie G, ∃ A : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ f x, A f x = bruhatDirectionalDeriv a f x := by
  classical
  intro a
  choose B hB using schwartzBruhatStage_orbitDeriv a
  have hStage (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (f : SchwartzBruhatStage e) :
      bruhatDirectionalDeriv a (schwartzBruhatStageRealization p e f) =
        schwartzBruhatStageRealization p e (B p e f) :=
    funext fun x ↦ (hB p e f x).deriv
  let P (f : G → ℂ) : Prop :=
    (∀ x : G, DifferentiableAt ℝ (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0) ∧
      bruhatDirectionalDeriv a f ∈ schwartzBruhatSubmodule G
  have hMem (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (g : G → ℂ) (hg : g ∈ (schwartzBruhatStageRealization p e).range) : P g := by
    obtain ⟨s, rfl⟩ := hg
    exact ⟨fun x ↦ (hB p e s x).differentiableAt, hStage p e s ▸
      (schwartzBruhatStageInclusion p e (B p e s)).property⟩
  have hZero : P 0 := by
    refine ⟨fun _ ↦ differentiableAt_const _, ?_⟩
    have h : bruhatDirectionalDeriv a (0 : G → ℂ) = 0 := by
      funext x
      exact (hasDerivAt_const 0 (0 : ℂ)).deriv
    rw [h]
    exact (schwartzBruhatSubmodule G).zero_mem
  have hAdd (g h : G → ℂ) (hg : P g) (hh : P h) : P (g + h) := by
    refine ⟨fun x ↦ (hg.1 x).add (hh.1 x), ?_⟩
    have hEq : bruhatDirectionalDeriv a (g + h) =
        bruhatDirectionalDeriv a g + bruhatDirectionalDeriv a h :=
      funext fun x ↦ deriv_add (hg.1 x) (hh.1 x)
    rw [hEq]
    exact (schwartzBruhatSubmodule G).add_mem hg.2 hh.2
  have hAll (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) : P f :=
    Submodule.iSup_induction _ (motive := P) hf
      (fun p g hg ↦ Submodule.iSup_induction _ (motive := P) hg (hMem p) hZero hAdd)
      hZero hAdd
  let A : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G :=
    { toFun := fun f ↦ ⟨bruhatDirectionalDeriv a f, (hAll f.val f.property).2⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦
        deriv_add ((hAll f.val f.property).1 x) ((hAll g.val g.property).1 x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ by
        change deriv (fun t : ℝ ↦ c * f (x * a (Multiplicative.ofAdd t))) 0 =
          c * deriv (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0
        exact congrFun (deriv_const_mul_field' c) 0) }
  refine ⟨⟨A, ?_⟩, fun _ _ ↦ rfl⟩
  apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp A
  intro p
  let q := p.val.comp A
  have hq (s : BruhatStructuralPair G) (e : ElementaryLCAPresentation s.quotient) :
      Continuous (q ∘ schwartzBruhatStageInclusion s e) := by
    have hEq : q ∘ schwartzBruhatStageInclusion s e =
        (p.val ∘ schwartzBruhatStageInclusion s e) ∘ B s e := by
      funext f
      apply congrArg p.val
      exact Subtype.ext (hStage s e f)
    rw [hEq]
    exact (p.property s e).comp (B s e).continuous
  let q' : {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (s : BruhatStructuralPair G) (e : ElementaryLCAPresentation s.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion s e)} := ⟨q, hq⟩
  exact (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G) Subtype.val).continuous_seminorm q'

/-- Paper: Lemma D.1.6.7(2), p. 767. First-order operators commute on the
smooth submodule. -/
theorem bruhatFirstOrder_commute (a b : LCATopologicalLie G) :
    Commute (bruhatFirstOrder a) (bruhatFirstOrder b) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change bruhatDirectionalDeriv a (bruhatDirectionalDeriv b f) x =
    bruhatDirectionalDeriv b (bruhatDirectionalDeriv a f) x
  -- Descend the two-parameter orbit through a structural quotient containing x.
  have hf : IsBruhatContDiff 2 (f : G → ℂ) := (Submodule.mem_iInf _).mp f.property 2
  obtain ⟨k, hk, _, hDescent⟩ := hf
  obtain ⟨p, hp, hx⟩ := exists_bruhatStructuralPair_mem k hk x
  obtain ⟨e⟩ := p.elementary
  obtain ⟨f₀, hf₀, hCover⟩ := hDescent p hp
  have hMem (c : LCATopologicalLie G) (t : Multiplicative ℝ) : c t ∈ p.val.1 := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range c.continuous).subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨1, map_one c⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let lift (c : LCATopologicalLie G) := c.toMonoidHom.codRestrict p.val.1 (hMem c)
  let q := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _ : p.val.1 →* p.quotient)
  let cE (c : LCATopologicalLie G) := AddMonoidHom.toMultiplicative.symm (q.comp (lift c))
  have hcE (c : LCATopologicalLie G) : Continuous (cE c) :=
    e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (c.continuous.subtype_mk (hMem c)))
  let orbit (st : ℝ × ℝ) :=
    (f : G → ℂ) (x * a (Multiplicative.ofAdd st.1) * b (Multiplicative.ofAdd st.2))
  have hOrbit : ContDiff ℝ 2 orbit := by
    let c := (cE a).coprod (cE b)
    have hc : Continuous c := ((hcE a).comp continuous_fst).add ((hcE b).comp continuous_snd)
    let φ := fun y ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd y))
    have hEq (st : ℝ × ℝ) : φ (c st + (q ⟨x, hx⟩).toAdd) = orbit st := by
      let y := (⟨x, hx⟩ : p.val.1) * lift a (Multiplicative.ofAdd st.1) *
        lift b (Multiplicative.ofAdd st.2)
      change f₀ (e.equiv.symm ((q (lift a (Multiplicative.ofAdd st.1)) *
        q (lift b (Multiplicative.ofAdd st.2))) * q ⟨x, hx⟩)) = f.val y.val
      rw [mul_comm _ (q ⟨x, hx⟩), ← mul_assoc, ← map_mul, ← map_mul]
      change f₀ (e.equiv.symm (e.equiv (QuotientGroup.mk y))) = f.val y.val
      rw [e.equiv.symm_apply_apply]
      exact hf₀ y
    simpa [hEq] using
      contDiff_comp_affine_elementary c hc (q ⟨x, hx⟩).toAdd (f := φ) (hCover e)
  have hFirst (u v : ℝ × ℝ) :
      deriv (fun t : ℝ ↦ orbit (u + t • v)) 0 = fderiv ℝ orbit u v := by
    have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    exact ((hOrbit.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hLine (by simp)).deriv
  have hSecond (u v : ℝ × ℝ) :
      deriv (fun t : ℝ ↦ fderiv ℝ orbit (t • u) v) 0 =
        fderiv ℝ (fderiv ℝ orbit) 0 u v := by
    have hd := ((hOrbit.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) 0).hasFDerivAt
    have h := hd.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id (0 : ℝ)).smul_const u) (by simp)
    simpa using (h.clm_apply (hasDerivAt_const 0 v)).deriv
  have ha (t : ℝ) : bruhatDirectionalDeriv a f (x * b (Multiplicative.ofAdd t)) =
      fderiv ℝ orbit (0, t) (1, 0) := by
    simpa [bruhatDirectionalDeriv, orbit, mul_right_comm] using hFirst (0, t) (1, 0)
  have hb (s : ℝ) : bruhatDirectionalDeriv b f (x * a (Multiplicative.ofAdd s)) =
      fderiv ℝ orbit (s, 0) (0, 1) := by
    simpa [bruhatDirectionalDeriv, orbit] using hFirst (s, 0) (0, 1)
  change deriv (fun s : ℝ ↦ bruhatDirectionalDeriv b f (x * a (Multiplicative.ofAdd s))) 0 =
    deriv (fun t : ℝ ↦ bruhatDirectionalDeriv a f (x * b (Multiplicative.ofAdd t))) 0
  simp_rw [ha, hb]
  have hSymm := hOrbit.contDiffAt (x := 0) |>.isSymmSndFDerivAt (by simp)
  have hMixed := (hSecond (1, 0) (0, 1)).trans
    ((hSymm.eq (1, 0) (0, 1)).trans (hSecond (0, 1) (1, 0)).symm)
  simpa only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] using hMixed

/-- Paper: Definition D.1.6.8(1), p. 768. Invariant differential operators
form the unital complex subalgebra generated by the first-order operators. -/
def bruhatDiffAlgebra (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    Subalgebra ℂ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Algebra.adjoin ℂ (range (bruhatFirstOrder (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The invariant differential operator
algebra is commutative. -/
theorem bruhatDiffAlgebra_commute (D E : bruhatDiffAlgebra G) : Commute D E := by
  have hcomm : (range (bruhatFirstOrder (G := G))).Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    exact bruhatFirstOrder_commute a b
  let : IsMulCommutative (bruhatDiffAlgebra G) := Algebra.isMulCommutative_adjoin ℂ hcomm
  exact mul_comm' D E

/-- Paper: Definition D.1.6.8(1), p. 768. The first-order generator belongs to
the differential operator algebra. -/
def bruhatDiffGenerator (a : LCATopologicalLie G) : bruhatDiffAlgebra G :=
  ⟨bruhatFirstOrder a, Algebra.subset_adjoin ⟨a, rfl⟩⟩

/-- Paper: Definition D.1.6.8(1), p. 768. The complex degree-one space is
the complex span of the first-order generators inside the differential operator algebra. -/
def bruhatDiffDegreeOne : Submodule ℂ (bruhatDiffAlgebra G) :=
  Submodule.span ℂ (range (bruhatDiffGenerator (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The real degree-one space is the
real span of first-order operators.
Deviation: This span is taken inside the ambient endomorphism algebra, where every
element of the span belongs to the differential operator algebra. -/
def bruhatDiffDegreeOneReal : Submodule ℝ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Submodule.span ℝ (range (bruhatFirstOrder (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The complex first-order space
contains each generator and excludes the identity operator.
Deviation: Sanity check distinguishing the span from the unital algebra. -/
theorem bruhatDiffDegreeOne_sanity (a : LCATopologicalLie G) :
    bruhatDiffGenerator a ∈ bruhatDiffDegreeOne ∧
      (1 : bruhatDiffAlgebra G) ∉ bruhatDiffDegreeOne := by
  refine ⟨Submodule.subset_span ⟨a, rfl⟩, ?_⟩
  -- The good subgroup witnessing smoothness of zero works for any constant.
  obtain ⟨k, hk, _, _⟩ := isBruhatContDiff_zero (G := G) 0
  have hone : (fun _ : G ↦ (1 : ℂ)) ∈ bruhatSmoothSubmodule := by
    apply (mem_bruhatSmoothSubmodule_iff _).2
    intro p
    refine ⟨k, hk, fun _ _ ↦ rfl, fun q _ ↦ ⟨fun _ ↦ 1, fun _ ↦ rfl, ?_⟩⟩
    intro e z b
    exact contDiff_const
  let f : bruhatSmoothSubmodule (G := G) := ⟨fun _ ↦ 1, hone⟩
  let ev : bruhatDiffAlgebra G →ₗ[ℂ] bruhatSmoothSubmodule (G := G) :=
    (LinearMap.applyₗ f).comp (bruhatDiffAlgebra G).val.toLinearMap
  have hspan : bruhatDiffDegreeOne ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    funext x
    change bruhatDirectionalDeriv b (fun _ ↦ 1) x = 0
    exact deriv_const (0 : ℝ) (1 : ℂ)
  intro h
  have hz : ev 1 = 0 := LinearMap.mem_ker.mp (hspan h)
  exact one_ne_zero (congrArg (fun g : bruhatSmoothSubmodule (G := G) ↦ g.val 1) hz)

/-- Paper: Definition D.1.6.8(1), p. 768. The real degree-one space consists
of individual first-order operators, by real linearity in the direction. -/
theorem mem_bruhatDiffDegreeOneReal_iff
    (D : Module.End ℂ (bruhatSmoothSubmodule (G := G))) :
    D ∈ bruhatDiffDegreeOneReal ↔ ∃ a : LCATopologicalLie G, D = bruhatFirstOrder a := by
  change D ∈ Submodule.span ℝ (Set.range (bruhatFirstOrder (G := G))) ↔ _
  constructor
  · intro hD
    induction hD using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨a, rfl⟩ := hE
      exact ⟨a, rfl⟩
    | zero =>
      exact ⟨_, by simpa only [zero_smul] using
        (bruhatFirstOrder_scale (1 : LCATopologicalLie G) 0).symm⟩
    | add E F _ _ hE hF =>
      obtain ⟨a, rfl⟩ := hE
      obtain ⟨b, rfl⟩ := hF
      exact ⟨a * b, (bruhatFirstOrder_mul a b).symm⟩
    | smul c E _ hE =>
      obtain ⟨a, rfl⟩ := hE
      exact ⟨_, (bruhatFirstOrder_scale a c).symm⟩
  · rintro ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩

/-- Paper: Definition D.1.6.8(2), p. 768. A word acts by applying its first
letter first and its last letter last. -/
def bruhatDiffWord (w : List (LCATopologicalLie G)) : bruhatDiffAlgebra G :=
  (w.reverse.map bruhatDiffGenerator).prod

/-- Paper: Definition D.1.6.8(2), p. 768. A one-letter word evaluates to its
first-order generator. -/
theorem bruhatDiffWord_singleton (a : LCATopologicalLie G) :
    bruhatDiffWord [a] = bruhatDiffGenerator a := by
  simp [bruhatDiffWord]

/-- Paper: Definition D.1.6.8(2), p. 768. Each operator has a presentation
as a finite linear combination of words in the first-order generators. -/
theorem bruhatDiff_exists_presentation (D : bruhatDiffAlgebra G) :
    ∃ c : List (LCATopologicalLie G) →₀ ℂ, c.sum (fun w z ↦ z • bruhatDiffWord w) = D := by
  let incl := (bruhatDiffAlgebra G).val
  have hWords :
      ↑(Submonoid.closure (range (bruhatFirstOrder (G := G)))) ⊆
        range (incl ∘ bruhatDiffWord) := by
    intro A hA
    induction hA using Submonoid.closure_induction with
    | mem A hA =>
        obtain ⟨a, rfl⟩ := hA
        refine ⟨[a], ?_⟩
        rw [Function.comp_apply, bruhatDiffWord_singleton]
        rfl
    | one =>
        exact ⟨[], incl.map_one⟩
    | mul A B _ _ hA hB =>
        obtain ⟨u, rfl⟩ := hA
        obtain ⟨v, rfl⟩ := hB
        refine ⟨v ++ u, ?_⟩
        simp only [Function.comp_apply, bruhatDiffWord, List.reverse_append, List.map_append,
          List.prod_append, map_mul]
  have hD : D.val ∈ Submodule.span ℂ (Submonoid.closure (range (bruhatFirstOrder (G := G))) :
      Set (Module.End ℂ (bruhatSmoothSubmodule (G := G)))) := by
    rw [← Algebra.adjoin_eq_span]
    exact D.property
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (Submodule.span_mono hWords hD)
  refine ⟨c, Subtype.ext ?_⟩
  change incl.toLinearMap (c.sum (fun w z ↦ z • bruhatDiffWord w)) = D.val
  simpa only [Finsupp.sum, map_sum, map_smul, AlgHom.toLinearMap_apply, Function.comp_apply]
    using hc

/-- Paper: Definition D.1.6.8(2), p. 768. The degree is the smallest possible
maximum word length among finite presentations of the operator.
Deviation: Finset supremum sets the empty presentation's length to zero. -/
def bruhatDiffDegree (D : bruhatDiffAlgebra G) : ℕ :=
  sInf {n : ℕ | ∃ c : List (LCATopologicalLie G) →₀ ℂ,
    c.sum (fun w z ↦ z • bruhatDiffWord w) = D ∧ n = c.support.sup List.length}

/-- Paper: Remark D.1.6.11, p. 768. A character gives a Bruhat smooth
function via its circle-valued character map.
Deviation: The global differentiability definition in §D.1.5 allows any
good subgroup in the kernel, so the symbol can use the character itself. -/
theorem pontryaginDual_mem_bruhatSmooth (χ : PontryaginDual G) :
    (fun x : G ↦ (χ x : ℂ)) ∈ bruhatSmoothSubmodule := by
  obtain ⟨H, hχ⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 χ
  let k := lcaDualAnnihilator H.val
  have hkClosed : IsClosed (k : Set G) := by
    have hSet : (k : Set G) = ⋂ ψ : H.val, (ψ.val : G → Circle) ⁻¹' {1} := by
      ext x
      simp only [k, SetLike.mem_coe, mem_lcaDualAnnihilator_iff, mem_iInter, mem_preimage,
        mem_singleton_iff]
    rw [hSet]
    exact isClosed_iInter fun ψ ↦ isClosed_singleton.preimage ψ.val.continuous
  have hk : IsBruhatGoodSubgroup k :=
    ⟨hkClosed, (lcaAnnihilator_dualAnnihilator_of_open H.val H.property.1).symm ▸ H.property⟩
  have hTrivial (x : k) : χ x.val = 1 :=
    (mem_lcaDualAnnihilator_iff H.val x.val).mp x.property ⟨χ, hχ⟩
  apply (mem_bruhatSmoothSubmodule_iff _).2
  intro p
  refine ⟨k, hk, fun x y ↦ ?_, fun a ha ↦ ?_⟩
  · change (χ (x.val * y) : ℂ) = (χ y : ℂ)
    rw [map_mul, hTrivial, one_mul]
  · let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let χH : a.val.1 →* Circle := χ.toMonoidHom.comp a.val.1.subtype
    have hN : N ≤ χH.ker := by
      intro x hx
      have hxk : (x : G) ∈ k := ha ▸ hx
      exact MonoidHom.mem_ker.mpr (hTrivial ⟨x, hxk⟩)
    let χ₀ : a.quotient →* Circle := QuotientGroup.lift N χH hN
    have hχ₀ : Continuous χ₀ := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (χ.continuous.comp continuous_subtype_val)
    refine ⟨fun x ↦ (χ₀ x : ℂ), fun x ↦ rfl, fun e z b ↦ ?_⟩
    -- Lift the character on the vector cover of the identity fiber to a linear phase.
    let E := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
    let S := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
    let cover : E →+ S :=
      { toFun := fun xt ↦ elementaryCover xt 0 0
        map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
        map_add' := fun x y ↦ Prod.ext rfl (Prod.ext
          (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm) }
    have hCover : Continuous cover := continuous_fst.prodMk
      ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const)
    let ψ := χ₀.comp e.equiv.symm.toMulEquiv.toMonoidHom
    let circleEquiv : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
    let phase : E →+ AddCircle (1 : ℝ) :=
      { toFun := fun x ↦ circleEquiv.symm (ψ (Multiplicative.ofAdd (cover x)))
        map_zero' := by
          apply circleEquiv.injective
          simp [circleEquiv, AddCircle.homeomorphCircle_apply]
        map_add' := by
          intro x y
          apply circleEquiv.injective
          have hAdd (u v : AddCircle (1 : ℝ)) :
              circleEquiv (u + v) = circleEquiv u * circleEquiv v := by
            simp only [circleEquiv, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
          change circleEquiv (circleEquiv.symm (ψ (Multiplicative.ofAdd (cover (x + y))))) = _
          simp only [circleEquiv.apply_symm_apply, hAdd, map_add]
          exact map_mul ψ (Multiplicative.ofAdd (cover x)) (Multiplicative.ofAdd (cover y)) }
    have hPhase : Continuous phase :=
      circleEquiv.symm.continuous.comp (hχ₀.comp (e.equiv.symm.continuous.comp hCover))
    obtain ⟨L, hL⟩ := exists_addCircle_coe_linearMap_eq phase hPhase
    have hExp (x : E) : ψ (Multiplicative.ofAdd (cover x)) = Circle.exp (2 * Real.pi * L x) := by
      have h := congrArg circleEquiv (hL x)
      have hApply : circleEquiv (phase x) = ψ (Multiplicative.ofAdd (cover x)) :=
        circleEquiv.apply_symm_apply _
      simpa only [hApply, circleEquiv, AddCircle.homeomorphCircle_apply,
        AddCircle.toCircle_apply_mk, div_one] using h.symm
    -- Moving to the fiber indexed by z and b multiplies the character by a constant.
    have hShift (x : E) : cover x + elementaryCover 0 z b = elementaryCover x z b := by
      refine Prod.ext (add_zero _) (Prod.ext ?_ (zero_add _))
      funext j
      change (x.2 j : AddCircle (1 : ℝ)) + ((0 : ℝ) : AddCircle (1 : ℝ)) =
        (x.2 j : AddCircle (1 : ℝ))
      rw [AddCircle.coe_zero, add_zero]
    have hFormula (x : E) : (ψ (Multiplicative.ofAdd (elementaryCover x z b)) : ℂ) =
        Complex.exp (↑(2 * Real.pi * L x) * Complex.I) *
          (ψ (Multiplicative.ofAdd (elementaryCover 0 z b)) : ℂ) := by
      rw [← hShift x]
      change (ψ (Multiplicative.ofAdd (cover x) *
        Multiplicative.ofAdd (elementaryCover 0 z b)) : ℂ) = _
      rw [map_mul, hExp, Circle.coe_mul, Circle.coe_exp]
    change ContDiff ℝ _ (fun x : E ↦ (ψ (Multiplicative.ofAdd (elementaryCover x z b)) : ℂ))
    rw [funext hFormula]
    exact (((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul L.contDiff)).mul
      contDiff_const).cexp).mul contDiff_const

/-- A scalar directional derivative must vanish on constants and hence on all
characters. Character separation then forces its one-parameter subgroup to be trivial. -/
private theorem bruhatDiffGenerator_ne_smul_one (a : LCATopologicalLie G) (ha : a ≠ 1)
    (z : ℂ) : bruhatDiffGenerator a ≠ z • (1 : bruhatDiffAlgebra G) := by
  intro h
  have hEval (f : bruhatSmoothSubmodule (G := G)) (x : G) :
      bruhatDirectionalDeriv a f x = z * f.val x :=
    congrArg (fun D : bruhatDiffAlgebra G ↦ (D.val f).val x) h
  let f₁ : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth 1⟩
  have hz : z = 0 := by
    simpa [f₁, bruhatDirectionalDeriv] using (hEval f₁ 1).symm
  apply ha
  apply ContinuousMonoidHom.ext
  intro u
  change a u = 1
  apply (pontryaginDual_pairing_separates (G := G)).1
  funext χ
  apply Circle.coe_injective
  let f : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩
  let g : ℝ → ℂ := fun t ↦ f.val (a (Multiplicative.ofAdd t))
  have hf := (mem_bruhatSmoothSubmodule_iff f.val).mp f.property 1
  have hg (t : ℝ) : HasDerivAt (fun s ↦ g (t + s)) 0 0 := by
    have hOrbit :
        (fun s : ℝ ↦ f.val (a (Multiplicative.ofAdd t) * a (Multiplicative.ofAdd s))) =
          (fun s : ℝ ↦ g (t + s)) :=
      funext fun s ↦ congrArg f.val (a.map_mul (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)).symm
    have hDeriv := hasDerivAt_bruhatDirectionalDeriv a hf (a (Multiplicative.ofAdd t))
    rw [hEval f, hz, zero_mul, hOrbit] at hDeriv
    exact hDeriv
  have hDiff : Differentiable ℝ g := fun t ↦
    (differentiableAt_iff_comp_const_add (b := t)).mpr
      (by simpa only [neg_add_cancel] using (hg t).differentiableAt)
  have hZero (t : ℝ) : deriv g t = 0 := by
    simpa only [deriv_comp_const_add, add_zero] using (hg t).deriv
  have hConst := is_const_of_deriv_eq_zero hDiff hZero u.toAdd 0
  change (χ (a u) : ℂ) = (χ (a 1) : ℂ) at hConst
  rwa [map_one a] at hConst

/-- Paper: Remark D.1.6.9, p. 768. A nontrivial one-parameter subgroup
gives a differential operator of degree one. -/
theorem bruhatDiffDegree_generator (a : LCATopologicalLie G) (ha : a ≠ 1) :
    bruhatDiffDegree (bruhatDiffGenerator a) = 1 := by
  classical
  let lengths : Set ℕ := {n | ∃ c : List (LCATopologicalLie G) →₀ ℂ,
    c.sum (fun w z ↦ z • bruhatDiffWord w) = bruhatDiffGenerator a ∧
      n = c.support.sup List.length}
  change sInf lengths = 1
  have hOne : 1 ∈ lengths := by
    refine ⟨Finsupp.single [a] 1, ?_, ?_⟩
    · rw [Finsupp.sum_single_index (h := fun w z ↦ z • bruhatDiffWord w) (zero_smul _ _),
        one_smul, bruhatDiffWord_singleton]
    · rw [Finsupp.support_single _ one_ne_zero, Finset.sup_singleton, List.length_singleton]
  refine le_antisymm (csInf_le' hOne) (le_csInf ⟨1, hOne⟩ ?_)
  rintro n ⟨c, hc, rfl⟩
  by_contra! h
  have hSupport : c.support ⊆ {[]} := by
    intro w hw
    have hLength : w.length ≤ c.support.sup List.length := Finset.le_sup hw
    exact Finset.mem_singleton.mpr (List.length_eq_zero_iff.mp (by omega))
  rw [Finsupp.sum_of_support_subset c hSupport (fun w z ↦ z • bruhatDiffWord w)
    (fun _ _ ↦ zero_smul _ _), Finset.sum_singleton] at hc
  exact bruhatDiffGenerator_ne_smul_one a ha (c []) hc.symm

/-- Paper: Definition D.1.6.10, p. 768. The symbol evaluates the differential
operator applied to a character at the group identity. -/
def bruhatDiffSymbol (D : bruhatDiffAlgebra G) (χ : PontryaginDual G) : ℂ :=
  (D.val ⟨fun x : G ↦ (χ x : ℂ), pontryaginDual_mem_bruhatSmooth χ⟩).val 1

/-- Paper: Definition D.1.6.10, p. 768. The identity operator has constant
symbol one.
Deviation: Sanity check on the normalization of the symbol. -/
theorem bruhatDiffSymbol_one (χ : PontryaginDual G) :
    bruhatDiffSymbol (1 : bruhatDiffAlgebra G) χ = 1 := by
  simp [bruhatDiffSymbol]

omit hTop hT2 hLC in
/-- Paper: Example D.1.6.12, p. 768. On the real line, the symbol of the
ordinary derivative at the character of frequency ξ is 2πiξ. -/
theorem bruhatDiffSymbol_real (ξ : ℝ) (χ : PontryaginDual (Multiplicative ℝ))
    (hχ : ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Real.fourierChar (ξ * x)) :
    bruhatDiffSymbol (bruhatDiffGenerator (ContinuousMonoidHom.id (Multiplicative ℝ))) χ =
      2 * ↑Real.pi * Complex.I * (ξ : ℂ) := by
  change deriv (fun t : ℝ ↦ (χ (1 * Multiplicative.ofAdd t) : ℂ)) 0 = _
  simp only [one_mul, hχ]
  have hZero : deriv (fun t ↦ (Real.fourierChar t : ℂ)) 0 = 2 * ↑Real.pi * Complex.I := by
    simpa only [Real.fourierChar_apply', mul_zero, Circle.exp_zero, Circle.coe_one, mul_one]
      using Real.deriv_fourierChar 0
  simpa only [mul_zero, hZero, Complex.real_smul, mul_comm (ξ : ℂ)] using
    deriv_comp_mul_left ξ (fun t ↦ (Real.fourierChar t : ℂ)) 0

/-- Paper: Lemma D.1.6.13, p. 769. A character is an eigenfunction of a word
of first derivatives, with eigenvalue the product of the individual symbols. -/
theorem bruhatDiffWord_character (w : List (LCATopologicalLie G))
    (χ : PontryaginDual G) (x : G) :
    ((bruhatDiffWord w).val ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩).val x =
      (w.map (fun a ↦ bruhatDiffSymbol (bruhatDiffGenerator a) χ)).prod * (χ x : ℂ) :=
  by
    let f : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩
    have hGenerator (a : LCATopologicalLie G) :
        (bruhatDiffGenerator a).val f = bruhatDiffSymbol (bruhatDiffGenerator a) χ • f := by
      apply Subtype.ext
      funext y
      change bruhatDirectionalDeriv a (fun z ↦ (χ z : ℂ)) y =
        bruhatDirectionalDeriv a (fun z ↦ (χ z : ℂ)) 1 * (χ y : ℂ)
      simp only [bruhatDirectionalDeriv, one_mul, map_mul, Circle.coe_mul, deriv_const_mul_field]
      exact mul_comm _ _
    change ((bruhatDiffWord w).val f).val x = _
    induction w with
    | nil => simp [bruhatDiffWord, f]
    | cons a w ih =>
      have hWord : bruhatDiffWord (a :: w) = bruhatDiffWord w * bruhatDiffGenerator a := by
        simp [bruhatDiffWord, List.reverse_cons, List.prod_append]
      rw [hWord]
      change ((bruhatDiffWord w).val ((bruhatDiffGenerator a).val f)).val x = _
      rw [hGenerator, map_smul]
      change bruhatDiffSymbol (bruhatDiffGenerator a) χ * ((bruhatDiffWord w).val f).val x = _
      rw [ih, List.map_cons, List.prod_cons, mul_assoc]

/-- Paper: Lemma D.1.6.13, p. 769. The symbol of a word is the product
of its first-order symbols. -/
theorem bruhatDiffSymbol_word (w : List (LCATopologicalLie G)) (χ : PontryaginDual G) :
    bruhatDiffSymbol (bruhatDiffWord w) χ =
      (w.map (fun a ↦ bruhatDiffSymbol (bruhatDiffGenerator a) χ)).prod := by sorry

/-- Paper: Lemma D.1.6.13, p. 769. The symbol is invariant under every
compact subgroup of the dual. -/
theorem bruhatDiffSymbol_compact_invariant (D : bruhatDiffAlgebra G)
    (K : Subgroup (PontryaginDual G)) (hK : IsCompact (K : Set (PontryaginDual G)))
    (χ : PontryaginDual G) (k : K) :
    bruhatDiffSymbol D (χ * k.val) = bruhatDiffSymbol D χ := by
  let U := lcaDualAnnihilator K
  have hU : IsOpen (U : Set G) := by
    convert (isOpen_lcaAnnihilator K hK).preimage
      (pontryaginDual_eval (G := G)).continuous using 1
    ext x
    exact (mem_lcaDualAnnihilator_iff K x).trans
      (mem_lcaAnnihilator_iff K (pontryaginDual_eval x)).symm
  -- Every operator in the generated algebra preserves agreement on the open annihilator.
  have hD : ∀ (f g : bruhatSmoothSubmodule (G := G)), EqOn f.val g.val U →
      EqOn (D.val f).val (D.val g).val U := by
    refine Algebra.adjoin_induction (s := range (bruhatFirstOrder (G := G)))
      (p := fun A _ ↦ ∀ (f g : bruhatSmoothSubmodule (G := G)), EqOn f.val g.val U →
        EqOn (A f).val (A g).val U) ?_ ?_ ?_ ?_ D.property
    · rintro _ ⟨a, rfl⟩ f g hfg x hx
      rw [bruhatFirstOrder_apply, bruhatFirstOrder_apply, bruhatDirectionalDeriv]
      have hOrbit : Continuous (fun t : ℝ ↦ x * a (Multiplicative.ofAdd t)) :=
        continuous_const.mul a.continuous
      have hAt : x * a (Multiplicative.ofAdd (0 : ℝ)) = x := by
        change x * a 1 = x
        rw [map_one, mul_one]
      have hNear := hOrbit.tendsto' 0 x hAt (hU.mem_nhds hx)
      exact EventuallyEq.deriv_eq (mem_of_superset hNear fun _ ht ↦ hfg ht)
    · intro c f g hfg x hx
      change (c • f).val x = (c • g).val x
      simp only [Submodule.coe_smul, Pi.smul_apply, hfg hx]
    · intro A B _ _ hA hB f g hfg x hx
      simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, hA f g hfg hx, hB f g hfg hx]
    · intro A B _ _ hA hB f g hfg
      exact hA (B f) (B g) (hB f g hfg)
  refine hD ⟨_, pontryaginDual_mem_bruhatSmooth (χ * k.val)⟩
    ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩ (fun x hx ↦ ?_) U.one_mem
  have hkx : k.val x = 1 := (mem_lcaDualAnnihilator_iff K x).mp hx k
  change (↑(χ x * k.val x) : ℂ) = ↑(χ x)
  rw [hkx, mul_one]

/-- Paper: Lemma D.1.6.14, p. 769. Real first-order operators correspond
bijectively and real-linearly to continuous real-valued homomorphisms on the dual.
The exponential formula is the commutativity of the diagram on characters.
Deviation: Real linearity is expressed by the pointwise laws on the target. -/
theorem bruhatDiffDegreeOne_frequency :
    ∃ σ : bruhatDiffDegreeOneReal (G := G) ≃ (PontryaginDual G →ₜ* Multiplicative ℝ),
      (∀ D E χ, (σ (D + E) χ).toAdd = (σ D χ).toAdd + (σ E χ).toAdd) ∧
      (∀ (c : ℝ) D χ, (σ (c • D) χ).toAdd = c * (σ D χ).toAdd) ∧
      ∀ (a : LCATopologicalLie G) (D : bruhatDiffDegreeOneReal (G := G)),
        D.val = bruhatFirstOrder a → ∀ χ (t : ℝ),
          Real.fourierChar ((σ D χ).toAdd * t) = χ (a (Multiplicative.ofAdd t)) :=
  by
    obtain ⟨dual, hDual⟩ := lcaTopologicalLie_dual (G := G)
    obtain ⟨realDual, hRealDual⟩ := exists_realPontryaginDualEquiv
    have hPair (r : Multiplicative ℝ) (t : ℝ) :
        realDual r (Multiplicative.ofAdd t) = Real.fourierChar (r.toAdd * t) :=
      hRealDual r.toAdd t
    let postcomp : (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)) ≃
        (PontryaginDual G →ₜ* Multiplicative ℝ) :=
      { toFun := fun b ↦ (realDual.symm : _ →ₜ* _).comp b
        invFun := fun b ↦ (realDual : _ →ₜ* _).comp b
        left_inv := fun b ↦ ContinuousMonoidHom.ext fun χ ↦ realDual.apply_symm_apply (b χ)
        right_inv := fun b ↦ ContinuousMonoidHom.ext fun χ ↦ realDual.symm_apply_apply (b χ) }
    let freq := dual.toEquiv.trans postcomp
    have hFreq (a : LCATopologicalLie G) (χ : PontryaginDual G) (t : ℝ) :
        Real.fourierChar ((freq a χ).toAdd * t) = χ (a (Multiplicative.ofAdd t)) := by
      rw [← hPair]
      change realDual (realDual.symm (dual a χ)) (Multiplicative.ofAdd t) = _
      rw [realDual.apply_symm_apply, hDual, PontryaginDual.map_apply]
    -- The derivative of each character at the identity determines its frequency.
    have hDeriv (a : LCATopologicalLie G) (χ : PontryaginDual G) :
        bruhatDirectionalDeriv a (fun x ↦ (χ x : ℂ)) 1 =
          (freq a χ).toAdd • (2 * ↑Real.pi * Complex.I) := by
      simp only [bruhatDirectionalDeriv, one_mul, ← hFreq a χ]
      have hZero : deriv (fun t ↦ (Real.fourierChar t : ℂ)) 0 = 2 * ↑Real.pi * Complex.I := by
        simpa only [Real.fourierChar_apply', mul_zero, Circle.exp_zero, Circle.coe_one, mul_one]
          using Real.deriv_fourierChar 0
      simpa only [mul_zero, hZero] using
        deriv_comp_mul_left (freq a χ).toAdd (fun t ↦ (Real.fourierChar t : ℂ)) 0
    let firstOrder (a : LCATopologicalLie G) : bruhatDiffDegreeOneReal (G := G) :=
      ⟨bruhatFirstOrder a, Submodule.subset_span ⟨a, rfl⟩⟩
    have hInjective : Function.Injective firstOrder := by
      intro a b hab
      apply freq.injective
      apply ContinuousMonoidHom.ext
      intro χ
      let f : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩
      have h := congrArg (fun D : bruhatDiffDegreeOneReal (G := G) ↦ (D.val f).val 1) hab
      change bruhatDirectionalDeriv a (fun x ↦ (χ x : ℂ)) 1 =
        bruhatDirectionalDeriv b (fun x ↦ (χ x : ℂ)) 1 at h
      rw [hDeriv, hDeriv] at h
      exact smul_left_injective ℝ (by simp [Real.pi_ne_zero]) h
    have hSurjective : Function.Surjective firstOrder := by
      intro D
      obtain ⟨a, ha⟩ := (mem_bruhatDiffDegreeOneReal_iff D.val).mp D.property
      exact ⟨a, Subtype.ext ha.symm⟩
    let firstOrderEquiv := Equiv.ofBijective firstOrder ⟨hInjective, hSurjective⟩
    let σ := firstOrderEquiv.symm.trans freq
    have hσ (D : bruhatDiffDegreeOneReal (G := G)) (a : LCATopologicalLie G)
        (ha : D.val = bruhatFirstOrder a) : σ D = freq a := by
      have h : firstOrderEquiv a = D := Subtype.ext ha.symm
      change freq (firstOrderEquiv.symm D) = freq a
      rw [← h, Equiv.symm_apply_apply]
    refine ⟨σ, ?_, ?_, fun a D ha χ t ↦ by rw [hσ D a ha, hFreq]⟩
    · intro D E χ
      obtain ⟨a, rfl⟩ := hSurjective D
      obtain ⟨b, rfl⟩ := hSurjective E
      rw [hσ _ (a * b) (bruhatFirstOrder_mul a b).symm, hσ _ a rfl, hσ _ b rfl]
      change (realDual.symm (dual (a * b) χ)).toAdd =
        (realDual.symm (dual a χ)).toAdd + (realDual.symm (dual b χ)).toAdd
      rw [map_mul, ContinuousMonoidHom.mul_apply, map_mul]
      rfl
    · intro c D χ
      obtain ⟨a, rfl⟩ := hSurjective D
      let scale : LCATopologicalLie (Multiplicative ℝ) :=
        ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative,
          continuous_const_mul c⟩
      rw [hσ _ (a.comp scale) (bruhatFirstOrder_scale a c).symm, hσ _ a rfl]
      change freq (a.comp scale) χ = Multiplicative.ofAdd (c * (freq a χ).toAdd)
      apply realDual.injective
      apply PontryaginDual.ext
      intro t
      change realDual (freq (a.comp scale) χ) (Multiplicative.ofAdd t.toAdd) =
        realDual (Multiplicative.ofAdd (c * (freq a χ).toAdd)) (Multiplicative.ofAdd t.toAdd)
      rw [hPair, hPair, hFreq]
      change χ (a (Multiplicative.ofAdd (c * t.toAdd))) =
        Real.fourierChar ((c * (freq a χ).toAdd) * t.toAdd)
      rw [show (c * (freq a χ).toAdd) * t.toAdd = (freq a χ).toAdd * (c * t.toAdd) by ring,
        hFreq]

/-- Paper: Corollary D.1.6.15, p. 770. The first-order symbol is the real
frequency multiplied by 2πi. The frequency is identified by the character pairing. -/
theorem bruhatDiffSymbol_generator (a : LCATopologicalLie G) (χ : PontryaginDual G)
    (r : ℝ) (hr : ∀ t : ℝ, Real.fourierChar (r * t) = χ (a (Multiplicative.ofAdd t))) :
    bruhatDiffSymbol (bruhatDiffGenerator a) χ = 2 * ↑Real.pi * Complex.I * (r : ℂ) := by
  have h := bruhatDiffSymbol_real r (PontryaginDual.map a χ) (fun t ↦ (hr t).symm)
  change deriv (fun t : ℝ ↦ (PontryaginDual.map a χ (1 * Multiplicative.ofAdd t) : ℂ)) 0 = _ at h
  change deriv (fun t : ℝ ↦ (χ (1 * a (Multiplicative.ofAdd t)) : ℂ)) 0 = _
  simpa only [one_mul, PontryaginDual.map_apply] using h

/-- Paper: Lemma D.1.6.16, p. 770. On an elementary group a smooth function
is Schwartz exactly when each symbol times each differentiated function is
continuous and globally bounded. The dual symbols are evaluated through biduality. -/
theorem mem_schwartzBruhat_iff_bruhatDiff_bounded (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (f : bruhatSmoothSubmodule (G := G)) :
    (f : G → ℂ) ∈ schwartzBruhatSubmodule G ↔
      ∀ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
        Continuous (fun x ↦ bruhatDiffSymbol E (b x) * (D.val f).val x) ∧
        ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * (D.val f).val x‖ ≤ C := by sorry

end DifferentialOperators

section AveragingAndFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

variable (K : Subgroup G)

section CompactAveraging

local instance sec1cCompactSubgroupMeasurableSpace : MeasurableSpace K := borel _

/-- Paper: Lemma D.1.6.18, p. 772. Normalized Haar averaging over a compact
subgroup of an elementary group gives a continuous surjection of Schwartz spaces. -/
theorem elementary_schwartzBruhat_average (e : ElementaryLCAPresentation G)
    (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      (∀ (f : SchwartzBruhat G) (x : G),
        Integrable (fun k : K ↦ f (x * k.val)) μK ∧
        P f (QuotientGroup.mk x) = ∫ k : K, f (x * k.val) ∂μK) ∧
      Function.Surjective P := by sorry

end CompactAveraging

section FibreIntegral

omit hTop hT2 hLC in
/-- Paper: Definition D.1.3.1, p. 750. An elementary Schwartz function is continuous
on the elementary group. Its lifts along the covering map are smooth on each discrete
fibre, and the covering map is open. -/
theorem elementarySchwartz_continuous {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (f : ElementarySchwartz m n r F) :
    Continuous (f : ElementaryLieGroup m n r F → ℂ) := by
  have hf := (show elementarySchwartzSubmodule m n r F from f).property.1
  let π : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) :=
    fun xt ↦ (xt.1, fun i ↦ (xt.2 i : AddCircle (1 : ℝ)))
  have hπ : IsOpenQuotientMap π := by
    have h1 : IsOpenQuotientMap
        (Pi.map fun _ : Fin n ↦ (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))) :=
      IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
    let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
    have h2 : IsOpenQuotientMap e := ⟨e.surjective, e.continuous, e.isOpenMap⟩
    exact IsOpenQuotientMap.id.prodMap (h1.comp h2)
  have hfib : ∀ a b, Continuous
      (fun p : EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) ↦ f (p.1, p.2, a, b)) :=
    fun a b ↦ by
      rw [← hπ.continuous_comp_iff]
      exact (hf a b).continuous
  rw [continuous_iff_continuousAt]
  rintro ⟨x, z, a, b⟩
  have hopen : IsOpen {p : ElementaryLieGroup m n r F | p.2.2 = (a, b)} :=
    (isOpen_discrete {(a, b)}).preimage (continuous_snd.comp continuous_snd)
  have heq : (f : ElementaryLieGroup m n r F → ℂ) =ᶠ[𝓝 (x, z, a, b)]
      fun p ↦ f (p.1, p.2.1, a, b) := by
    filter_upwards [hopen.mem_nhds rfl] with p hp
    obtain ⟨p1, p2, p3, p4⟩ := p
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rfl
  exact ((hfib a b).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousAt.congr heq.symm

omit hTop hT2 hLC in
/-- Paper: Definition D.1.5.1(1), p. 760. A good subgroup is compact. It is the
annihilator of its open annihilator (Lemma D.1.4.6(1)), and by duality the annihilator
of an open subgroup of the dual is compact (Lemma D.1.4.6(4)). -/
theorem IsBruhatGoodSubgroup.isCompact [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] {k : Subgroup G} (hk : IsBruhatGoodSubgroup k) :
    IsCompact (k : Set G) := by
  obtain ⟨hkc, hko, -⟩ := hk
  have hJ := isCompact_lcaAnnihilator (G := PontryaginDual G) (lcaAnnihilator k) hko
  have hpre : (k : Set G) = pontryaginDual_eval ⁻¹'
      (lcaAnnihilator (lcaAnnihilator k) : Set (PontryaginDual (PontryaginDual G))) := by
    conv_lhs => rw [← lcaDualAnnihilator_annihilator k hkc]
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, mem_lcaDualAnnihilator_iff,
      mem_lcaAnnihilator_iff]
    rfl
  rw [hpre]
  exact isClosedEmbedding_pontryaginDual_eval.isCompact_preimage hJ

omit hTop hT2 hLC in
/-- Compact generation passes to the target of a continuous, open and surjective
homomorphism. -/
theorem isCompactlyGeneratedGroup_of_surjective {X : Type*} [CommGroup X] [TopologicalSpace X]
    (f : X →* G) (hf : Continuous f) (hfo : IsOpenMap f) (hs : Function.Surjective f)
    (h : IsCompactlyGeneratedGroup X) : IsCompactlyGeneratedGroup G := by
  obtain ⟨U, hU, hUc, hGen⟩ := h
  refine ⟨f '' U, ?_, hUc.image hf, ?_⟩
  · have := hfo.image_mem_nhds hU
    rwa [map_one] at this
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective f hs]

/-- Paper: Theorem D.1.7.1, p. 776. The images of the two subgroups of a structural
pair in the quotient by a closed subgroup form a structural pair of the quotient.
The image of the good subgroup is compact, and its annihilator is a closed subgroup
of the compactly generated annihilator of the good subgroup. -/
theorem BruhatStructuralPair.exists_quotient (hK : IsClosed (K : Set G))
    (a : BruhatStructuralPair G) :
    ∃ b : BruhatStructuralPair (G ⧸ K),
      b.val.1 = a.val.1.map (QuotientGroup.mk' K) ∧
        OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K) := by
  obtain ⟨hHo, hHcg, hCgood, hCH⟩ := a.property
  have : IsClosed (K : Set G) := hK
  have hCc := hCgood.isCompact
  let q := QuotientGroup.mk' K
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hqc : Continuous q := QuotientGroup.continuous_mk
  refine ⟨⟨(a.val.1.map q, OrderDual.toDual ((OrderDual.ofDual a.val.2).map q)),
    ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · change IsOpen ((a.val.1.map q : Subgroup (G ⧸ K)) : Set (G ⧸ K))
    rw [Subgroup.coe_map]
    exact hqo _ hHo
  · -- The open subgroup of the quotient is compactly generated.
    let f := q.subgroupMap a.val.1
    have hfc : Continuous f := (hqc.comp continuous_subtype_val).subtype_mk _
    have hfo : IsOpenMap f := by
      intro O hO
      have hO' : IsOpen (q '' (Subtype.val '' O)) := hqo _ (hHo.isOpenMap_subtype_val _ hO)
      convert hO'.preimage continuous_subtype_val using 1
      ext y
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨o.val, ⟨o, ho, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, hy⟩
        exact ⟨o, ho, Subtype.ext hy⟩
    exact isCompactlyGeneratedGroup_of_surjective f hfc hfo
      (q.subgroupMap_surjective a.val.1) hHcg
  · -- The image of the good subgroup is good.
    have hCq : IsCompact (((OrderDual.ofDual a.val.2).map q : Subgroup (G ⧸ K)) : Set (G ⧸ K)) := by
      rw [Subgroup.coe_map]
      exact hCc.image hqc
    refine ⟨hCq.isClosed, isOpen_lcaAnnihilator _ hCq, ?_⟩
    obtain ⟨ε, hε⟩ := lcaQuotientDual_equiv_annihilator K hK
    set C := OrderDual.ofDual a.val.2
    obtain ⟨-, hCo, hCcg⟩ := hCgood
    have : LocallyCompactSpace (lcaAnnihilator C) :=
      hCo.isOpenEmbedding_subtypeVal.locallyCompactSpace
    let M : Subgroup (lcaAnnihilator C) := (lcaAnnihilator K).comap (lcaAnnihilator C).subtype
    have hKc : IsClosed (lcaAnnihilator K : Set (PontryaginDual G)) := by
      have : (lcaAnnihilator K : Set (PontryaginDual G)) =
          (PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)) ⁻¹' {1} := rfl
      rw [this]
      exact isClosed_singleton.preimage (PontryaginDual.map _).continuous
    have hMc : IsClosed (M : Set (lcaAnnihilator C)) := hKc.preimage continuous_subtype_val
    have hM := isCompactlyGeneratedGroup_closedSubgroup hCcg M hMc
    refine isCompactlyGeneratedGroup_of_continuousMulEquiv ?_ hM
    have hto : ∀ ψ : M, ε.symm ⟨ψ.val.val, ψ.2⟩ ∈ lcaAnnihilator (C.map q) := by
      intro ψ
      rw [mem_lcaAnnihilator_iff]
      rintro ⟨_, c, hc, rfl⟩
      have h1 := hε (ε.symm ⟨ψ.val.val, ψ.2⟩) c
      rw [ContinuousMulEquiv.apply_symm_apply] at h1
      change (ε.symm ⟨ψ.val.val, ψ.2⟩) (QuotientGroup.mk c) = 1
      rw [← h1]
      exact (mem_lcaAnnihilator_iff C _).mp ψ.val.2 ⟨c, hc⟩
    have hinv₁ : ∀ χ : lcaAnnihilator (C.map q), (ε χ.val).val ∈ lcaAnnihilator C := by
      intro χ
      rw [mem_lcaAnnihilator_iff]
      intro c
      rw [hε]
      exact (mem_lcaAnnihilator_iff _ _).mp χ.2 ⟨q c, c, c.2, rfl⟩
    exact
      { toFun := fun ψ ↦ ⟨ε.symm ⟨ψ.val.val, ψ.2⟩, hto ψ⟩
        invFun := fun χ ↦ ⟨⟨(ε χ.val).val, hinv₁ χ⟩, (ε χ.val).2⟩
        left_inv := fun ψ ↦ by
          apply Subtype.ext; apply Subtype.ext
          simp
        right_inv := fun χ ↦ by
          apply Subtype.ext
          change ε.symm ⟨(ε χ.val).val, (ε χ.val).2⟩ = χ.val
          simp
        map_mul' := fun ψ₁ ψ₂ ↦ by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          rw [← map_mul]
          rfl
        continuous_toFun := (ε.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
        continuous_invFun := ((continuous_subtype_val.comp
          (ε.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _ }
  · exact Subgroup.map_mono hCH

/-- Paper: Theorem D.1.7.1, p. 776. When the structural pair `b` of the quotient by `K`
is the image of the structural pair `a`, the quotient map of `G` induces a continuous,
open and surjective homomorphism from the elementary quotient of `a` to that of `b`.
Its kernel is the image of `K ∩ a.val.1`. -/
theorem BruhatStructuralPair.exists_quotient_hom (a : BruhatStructuralPair G)
    (b : BruhatStructuralPair (G ⧸ K))
    (hb₁ : b.val.1 = a.val.1.map (QuotientGroup.mk' K))
    (hb₂ : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K)) :
    ∃ p : a.quotient →* b.quotient, Continuous p ∧ IsOpenMap p ∧ Function.Surjective p ∧
      p.ker = (K.comap a.val.1.subtype).map
        (QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)) ∧
      ∀ (x : G) (hx : x ∈ a.val.1) (hq : (QuotientGroup.mk x : G ⧸ K) ∈ b.val.1),
        p (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨QuotientGroup.mk x, hq⟩ := by
  obtain ⟨hHo, -, -, hCH⟩ := a.property
  let H := a.val.1
  let C := OrderDual.ofDual a.val.2
  let N := C.comap H.subtype
  let Nb := (OrderDual.ofDual b.val.2).comap b.val.1.subtype
  let q := QuotientGroup.mk' K
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hqc : Continuous q := QuotientGroup.continuous_mk
  let f₀ : H →* b.val.1 := (q.comp H.subtype).codRestrict b.val.1 fun h ↦ by
    rw [hb₁]; exact ⟨h.val, h.2, rfl⟩
  have hf₀ : ∀ h : H, (f₀ h).val = q h.val := fun h ↦ rfl
  have hf₀c : Continuous f₀ := (hqc.comp continuous_subtype_val).subtype_mk _
  have hf₀o : IsOpenMap f₀ := by
    intro O hO
    have hO' : IsOpen (q '' (Subtype.val '' O)) := hqo _ (hHo.isOpenMap_subtype_val _ hO)
    convert hO'.preimage continuous_subtype_val using 1
    ext y
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o.val, ⟨o, ho, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨o, ho, rfl⟩, hy⟩
      exact ⟨o, ho, Subtype.ext hy⟩
  have hf₀s : Function.Surjective f₀ := by
    rintro ⟨y, hy⟩
    rw [hb₁] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let f₁ : H →* b.quotient := (QuotientGroup.mk' Nb).comp f₀
  have hN : N ≤ f₁.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap, Subgroup.coe_subtype, hf₀, hb₂]
    exact ⟨h.val, hh, rfl⟩
  let p : a.quotient →* b.quotient := QuotientGroup.lift N f₁ hN
  have hpmk : ∀ h : H, p (QuotientGroup.mk h) = QuotientGroup.mk (f₀ h) := fun h ↦ rfl
  have hcomp : (p ∘ (QuotientGroup.mk : H → a.quotient)) = (QuotientGroup.mk' Nb) ∘ f₀ :=
    funext hpmk
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr ?_
    rw [hcomp]
    exact QuotientGroup.continuous_mk.comp hf₀c
  · intro U hU
    have hU' : p '' U =
        ((QuotientGroup.mk' Nb) ∘ f₀) '' ((QuotientGroup.mk : H → a.quotient) ⁻¹' U) := by
      rw [← hcomp, Set.image_comp, Set.image_preimage_eq _ (QuotientGroup.mk_surjective)]
    rw [hU', Set.image_comp]
    exact QuotientGroup.isOpenMap_coe _ (hf₀o _ (hU.preimage QuotientGroup.continuous_mk))
  · intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨h, rfl⟩ := hf₀s y
    exact ⟨QuotientGroup.mk h, rfl⟩
  · ext y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, hpmk, QuotientGroup.eq_one_iff, Subgroup.mem_comap,
      Subgroup.coe_subtype, hf₀, hb₂]
    constructor
    · rintro ⟨c, hc, hch⟩
      have hk : c⁻¹ * h.val ∈ K := QuotientGroup.eq.mp hch
      have hkH : c⁻¹ * h.val ∈ H := H.mul_mem (H.inv_mem (hCH hc)) h.2
      refine ⟨⟨c⁻¹ * h.val, hkH⟩, hk, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      change (c⁻¹ * h.val)⁻¹ * h.val ∈ C
      simpa using hc
    · rintro ⟨k, hk, hkh⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hkh
      refine ⟨(k⁻¹ * h).val, hkh, ?_⟩
      change (QuotientGroup.mk ((k⁻¹ * h : H) : G) : G ⧸ K) = QuotientGroup.mk h.val
      rw [QuotientGroup.eq]
      have : ((k⁻¹ * h : H) : G)⁻¹ * h.val = k.val := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        rw [mul_assoc, mul_comm (k : G), inv_mul_cancel_left]
      rw [this]
      exact hk
  · intro x hx hq
    rw [hpmk]
    rfl

-- TODO(paper-gap): The proof of D.1.7.1 cites Lemma D.1.6.18 for the elementary case,
-- but that lemma only averages over compact subgroups. The kernel below can be
-- noncompact, as for ℤ ⊂ ℝ, where the coset integral is a periodization.

omit hTop hT2 hLC in
/-- Paper: Lemma D.1.6.18 and Theorem D.1.7.1, pp. 772 and 776. On an elementary group,
the integral of a Schwartz function along the kernel of a continuous, open and surjective
homomorphism onto another elementary group exists on every coset, and is a Schwartz
function on the target.
Deviation: The kernel is any closed subgroup, not only a compact one. The target
presentation is arbitrary. -/
theorem elementary_fiberIntegral {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A]
    [BorelSpace A] [CommGroup B] [TopologicalSpace B]
    (e : ElementaryLCAPresentation A) (e' : ElementaryLCAPresentation B)
    (p : A →* B) (hp : Continuous p) (hpo : IsOpenMap p) (hps : Function.Surjective p)
    (ν : Measure p.ker) [ν.IsHaarMeasure] (φ : SchwartzBruhatStage e) :
    (∀ y : A, Integrable (fun l : p.ker ↦ φ (Multiplicative.toAdd (e.equiv (y * l)))) ν) ∧
      ∃ ψ : SchwartzBruhatStage e', ∀ y : A,
        ψ (Multiplicative.toAdd (e'.equiv (p y))) =
          ∫ l : p.ker, φ (Multiplicative.toAdd (e.equiv (y * l))) ∂ν := by sorry

end FibreIntegral

variable [MeasurableSpace G] [hBorel : BorelSpace G]

local instance sec1cDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
local instance sec1cQuotientMeasurableSpace : MeasurableSpace (G ⧸ K) := borel _
local instance sec1cQuotientDualMeasurableSpace :
    MeasurableSpace (PontryaginDual (G ⧸ K)) := borel _

variable (μ : Measure G) [hHaar : μ.IsHaarMeasure] [hRegular : μ.Regular]

include hBorel hHaar hRegular

/-- Paper: Lemma D.1.6.19(1), p. 773. An invariant differential operator
preserves Schwartz–Bruhat functions, and on the Fourier side it acts by
multiplication by its symbol. Both integrals are defined on integrable functions. -/
theorem lcaFourier_bruhatDiff (D : bruhatDiffAlgebra G) (f : SchwartzBruhat G) :
    ∃ (hf : (f : G → ℂ) ∈ bruhatSmoothSubmodule)
      (g : SchwartzBruhat G), (g : G → ℂ) = (D.val ⟨f, hf⟩).val ∧
      Integrable (f : G → ℂ) μ ∧ Integrable (g : G → ℂ) μ ∧
      lcaFourier μ g = bruhatDiffSymbol D * lcaFourier μ f := by sorry

/-- Paper: Lemma D.1.6.19(2), p. 773. The Fourier integral gives a continuous
linear isomorphism of the two Schwartz–Bruhat spaces. -/
theorem schwartzBruhat_fourier_equiv :
    ∃ F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ f : SchwartzBruhat G, Integrable (f : G → ℂ) μ ∧
        ∀ χ, F f χ = lcaFourier μ f χ := by sorry

-- TODO(paper-gap): (D.1.6.25) has different domains on its two sides. Its right side
-- is an inverse transform on G, whereas the left side is a Fourier transform on the dual.
-- The direction of the Fourier transform on the right in (D.1.6.26) is also reversed.
-- The footnotes on pp. 771, 773 and 775 leave the measure comparison to be checked.

/-- Paper: Lemma D.1.6.19(3), p. 773. Normalized structural averaging and
extension by zero intertwine with Fourier transform at the dual structural pair.
Deviation: This is the projector identity described after (D.1.6.26), with the
forward transform on both paths and both compact averages taken with mass one.
The ill-typed inverse-transform formula (D.1.6.25) is left open. -/
theorem lcaFourier_structural_projectors (a : BruhatStructuralPair G)
    (μK : Measure ↥(OrderDual.ofDual a.val.2))
    [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (νJ : Measure (lcaAnnihilator a.val.1))
    [νJ.IsHaarMeasure] [IsProbabilityMeasure νJ]
    (f : SchwartzBruhat G) :
    let avg := (a.val.1 : Set G).indicator
      (fun x ↦ ∫ k : ↥(OrderDual.ofDual a.val.2), f (x * k.val) ∂μK)
    Integrable (f : G → ℂ) μ ∧ Integrable avg μ ∧
      (∀ x : G, Integrable (fun k : ↥(OrderDual.ofDual a.val.2) ↦ f (x * k.val)) μK) ∧
      (∀ χ : PontryaginDual G,
        Integrable (fun ψ : lcaAnnihilator a.val.1 ↦ lcaFourier μ f (χ * ψ.val)) νJ) ∧
      lcaFourier μ avg =
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)).indicator
          (fun χ ↦ ∫ ψ : lcaAnnihilator a.val.1, lcaFourier μ f (χ * ψ.val) ∂νJ) := by sorry

omit hHaar hRegular
variable (μK : Measure K) [hHaarK : μK.IsHaarMeasure] [hRegularK : μK.Regular]
variable (hK : IsClosed (K : Set G))

include hK hHaarK hRegularK

-- TODO(paper-gap): The proof of D.1.7.1 uses properness of G → G/k and
-- openness of k. For k = ℤ in G = ℝ both assertions fail.

open Classical in
/-- Paper: Theorem D.1.7.1, p. 776. Let `π` be the quotient of an open subgroup `H` by a
compact subgroup, and `L` the image of `K ∩ H` under it. For a suitable Haar measure on `L`,
integrating a function on `H`, extended by zero, over a coset of `K` through a point of `H`
is the same as integrating its descent over the matching coset of `L`. -/
theorem exists_haar_fiberIntegral_eq {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (H : Subgroup G) (hH : IsOpen (H : Set G)) (π : H →* A) (hπ : Continuous π)
    (hπo : IsOpenMap π) (hπs : Function.Surjective π) (hπk : IsCompact (π.ker : Set H))
    (L : Subgroup A) (hL : L = (K.comap H.subtype).map π) :
    ∃ ν : Measure L, ν.IsHaarMeasure ∧ ∀ g : A → ℂ, Continuous g → ∀ h : H,
      (Integrable (fun k : K ↦ if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0) μK ↔
        Integrable (fun l : L ↦ g (π h * l)) ν) ∧
      ∫ k : K, (if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0) ∂μK =
        ∫ l : L, g (π h * l) ∂ν := by
  subst hL
  -- `π` is proper: it is closed, with compact fibres.
  have hπp : IsProperMap π := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨hπ, fun F hF ↦ ?_, fun y ↦ ?_⟩
    · have hq : IsQuotientMap π := hπo.isQuotientMap hπ hπs
      rw [← hq.isClosed_preimage]
      convert hF.mul_right_of_isCompact hπk using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_mul, SetLike.mem_coe, MonoidHom.mem_ker]
      constructor
      · rintro ⟨f, hf, hfx⟩
        exact ⟨f, hf, f⁻¹ * x, by rw [map_mul, map_inv, hfx, inv_mul_cancel], by simp⟩
      · rintro ⟨f, hf, k, hk, rfl⟩
        exact ⟨f, hf, by rw [map_mul, hk, mul_one]⟩
    · obtain ⟨h₀, rfl⟩ := hπs y
      convert hπk.image (Homeomorph.mulLeft h₀).continuous using 1
      ext x
      constructor
      · intro hx
        have hx' : π x = π h₀ := hx
        refine ⟨h₀⁻¹ * x, ?_, by simp⟩
        change π (h₀⁻¹ * x) = 1
        rw [map_mul, map_inv, hx', inv_mul_cancel]
      · rintro ⟨k, hk, rfl⟩
        have hk' : π k = 1 := hk
        change π (h₀ * k) = π h₀
        rw [map_mul, hk', mul_one]
  -- The open subgroup `K ∩ H` of `K` and the restricted Haar measure.
  have : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let K' : Subgroup K := H.comap K.subtype
  have hK'o : IsOpen (K' : Set K) := hH.preimage continuous_subtype_val
  have hK'c : IsClosed (K' : Set K) := Subgroup.isClosed_of_isOpen K' hK'o
  have : LocallyCompactSpace K' := hK'o.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let μ' : Measure K' := Measure.comap Subtype.val μK
  have hμ' : μ'.IsHaarMeasure := Measure.IsHaarMeasure.comap μK (mH := inferInstance)
    (f := K'.subtype) hK'o.isOpenEmbedding_subtypeVal
  let ι : K' →* H := (K.subtype.comp K'.subtype).codRestrict H fun k ↦ k.2
  have hιc : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hLc : IsClosed (((K.comap H.subtype).map π : Subgroup A) : Set A) := by
    rw [Subgroup.coe_map]
    exact hπp.isClosedMap _ (hK.preimage continuous_subtype_val)
  have : LocallyCompactSpace ((K.comap H.subtype).map π) :=
    hLc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ρ : K' →* (K.comap H.subtype).map π :=
    (π.comp ι).codRestrict _ fun k ↦ ⟨ι k, k.val.2, rfl⟩
  have hρc : Continuous ρ := (hπ.comp hιc).subtype_mk _
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨⟨x.val, hx⟩, x.2⟩, rfl⟩
  have hK'G : IsClosedEmbedding (fun k : K' ↦ k.val.val) :=
    hK.isClosedEmbedding_subtypeVal.comp hK'c.isClosedEmbedding_subtypeVal
  have hρp : Tendsto ρ (cocompact K') (cocompact _) := by
    refine (isProperMap_iff_tendsto_cocompact.mp
      (isProperMap_iff_isCompact_preimage.mpr ⟨hρc, fun S hS ↦ ?_⟩)).2
    have hT := (hπp.isCompact_preimage (hS.image continuous_subtype_val)).image
      continuous_subtype_val
    convert hK'G.isCompact_preimage hT using 1
    ext k
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hk
      exact ⟨ι k, ⟨ρ k, hk, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨s, hs, hsx⟩, hxk⟩
      have : x = ι k := Subtype.ext hxk
      subst this
      have : s = ρ k := Subtype.ext hsx
      rwa [← this]
  let ν : Measure ((K.comap H.subtype).map π) := μ'.map ρ
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_map μ' ρ hρc hρs hρp
  refine ⟨ν, hν, fun g hg h ↦ ?_⟩
  set F : K → ℂ := fun k ↦ if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0 with hFdef
  let Φ : (K.comap H.subtype).map π → ℂ := fun l ↦ g (π h * l)
  have hΦ : Continuous Φ := hg.comp (continuous_const.mul continuous_subtype_val)
  have hF0 : ∀ k, k ∉ (K' : Set K) → F k = 0 := by
    intro k hk
    refine dite_eq_right fun hhk ↦ hk ?_
    have : k.val = h.val⁻¹ * (h.val * k.val) := by group
    change k.val ∈ H
    rw [this]
    exact H.mul_mem (H.inv_mem h.2) hhk
  have hFρ : ∀ k : K', F k.val = Φ (ρ k) := by
    intro k
    have hhk : h.val * k.val.val ∈ H := H.mul_mem h.2 k.2
    simp only [F, dite_eq_left hhk, Φ]
    rw [show (⟨_, hhk⟩ : H) = h * ι k from rfl, map_mul]
    rfl
  have hmeas : MeasurableSet (K' : Set K) := hK'o.measurableSet
  have hsupp : Function.support F ⊆ (K' : Set K) := fun k hk ↦ by
    by_contra h'
    exact hk (hF0 k h')
  have hcomp : F ∘ (Subtype.val : K' → K) = Φ ∘ ρ := funext hFρ
  constructor
  · rw [← integrableOn_iff_integrable_of_support_subset hsupp,
      integrableOn_iff_comap_subtypeVal hmeas]
    change _ ↔ Integrable Φ (μ'.map ρ)
    rw [integrable_map_measure hΦ.aestronglyMeasurable hρc.aemeasurable]
    exact iff_of_eq (congrArg (fun f : K' → ℂ ↦ Integrable f μ') hcomp)
  · calc ∫ k : K, F k ∂μK = ∫ k in (K' : Set K), F k ∂μK :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
      _ = ∫ k : K', F k.val ∂μ' := (integral_subtype_comap hmeas F).symm
      _ = ∫ k : K', Φ (ρ k) ∂μ' := integral_congr_ae (Eventually.of_forall hFρ)
      _ = ∫ l, Φ l ∂ν :=
          (integral_map hρc.aemeasurable hΦ.aestronglyMeasurable).symm

/-- Paper: Theorem D.1.7.1, p. 776. A single stage function, pulled back from the
elementary quotient of a structural pair and extended by zero, is integrable on every
coset, and its coset integral is a Schwartz–Bruhat function on the quotient.
Deviation: This is the case of one stage of the inductive limit; the general case
follows by additivity. -/
theorem lcaCosetIntegral_stageRealization_mem (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (φ : SchwartzBruhatStage e) :
    (∀ x : G, Integrable (fun k : K ↦ schwartzBruhatStageRealization a e φ (x * k.val)) μK) ∧
      lcaCosetIntegral K μK (schwartzBruhatStageRealization a e φ) ∈
        schwartzBruhatSubmodule (G ⧸ K) := by
  classical
  let H := a.val.1
  let C := OrderDual.ofDual a.val.2
  obtain ⟨hHo, -, hCgood, hCH⟩ := a.property
  have hCc : IsCompact (C : Set G) := hCgood.isCompact
  have : IsClosed (K : Set G) := hK
  obtain ⟨b, hb₁, hb₂⟩ := a.exists_quotient K hK
  have : LocallyCompactSpace H := hHo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨e'⟩ := BruhatStructuralPair.elementary b
  let : MeasurableSpace a.quotient := borel _
  have : BorelSpace a.quotient := ⟨rfl⟩
  let N := C.comap H.subtype
  have : IsClosed (N : Set H) := hCc.isClosed.preimage continuous_subtype_val
  let π : H →* a.quotient := QuotientGroup.mk' N
  have hπ : Continuous π := QuotientGroup.continuous_mk
  have hπo : IsOpenMap π := QuotientGroup.isOpenMap_coe
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπk : IsCompact (π.ker : Set H) := by
    rw [QuotientGroup.ker_mk', Subtype.isCompact_iff]
    convert hCc using 1
    ext x
    simp only [Set.mem_image, SetLike.mem_coe]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨⟨x, hCH hx⟩, hx, rfl⟩⟩
  obtain ⟨p, hpc, hpo, hps, hpker, hpmk⟩ := a.exists_quotient_hom K b hb₁ hb₂
  obtain ⟨ν, hν, hfib⟩ := exists_haar_fiberIntegral_eq K μK hK H hHo π hπ hπo hπs hπk p.ker hpker
  obtain ⟨hint, ψ, hψ⟩ :=
    elementary_fiberIntegral (A := a.quotient) (B := b.quotient) e e' p hpc hpo hps ν φ
  let g : a.quotient → ℂ := fun y ↦ φ (Multiplicative.toAdd (e.equiv y))
  have hg : Continuous g :=
    (elementarySchwartz_continuous φ).comp (continuous_toAdd.comp e.equiv.continuous)
  have hR : ∀ x : G, schwartzBruhatStageRealization a e φ x =
      if hx : x ∈ H then g (π ⟨x, hx⟩) else 0 := fun x ↦ by
    rw [schwartzBruhatStageRealization_apply]
    rfl
  -- On a coset through a point of `H`, the integral is computed in the elementary quotient.
  have hkey : ∀ h : H,
      Integrable (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k.val)) μK ∧
        ∫ k : K, schwartzBruhatStageRealization a e φ (h.val * k.val) ∂μK =
          ψ (Multiplicative.toAdd (e'.equiv (p (π h)))) := fun h ↦ by
    have hh := hfib g hg h
    have hfun : (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k.val)) =
        fun k ↦ if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0 := by
      funext k
      rw [schwartzBruhatStageRealization_apply]
      split_ifs with hk
      · exact congrArg (fun y ↦ φ (Multiplicative.toAdd (e.equiv y)))
          (QuotientGroup.mk'_apply N _).symm
      · rfl
    exact ⟨(congrArg (fun F : K → ℂ ↦ Integrable F μK) hfun).mpr (hh.1.mpr (hint (π h))),
      (congrArg (fun F : K → ℂ ↦ ∫ k, F k ∂μK) hfun).trans (hh.2.trans (hψ (π h)).symm)⟩
  -- A point whose coset meets `H` is a point of `H` times a point of `K`.
  have hsplit : ∀ x : G, (QuotientGroup.mk x : G ⧸ K) ∈ b.val.1 →
      ∃ h : H, ∃ k₀ : K, x = h.val * k₀.val := fun x hx ↦ by
    rw [hb₁] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, hy⟩, ⟨y⁻¹ * x, QuotientGroup.eq.mp hyx⟩, ?_⟩
    simp
  -- Off the cosets meeting `H` the function vanishes.
  have hzero : ∀ x : G, (QuotientGroup.mk x : G ⧸ K) ∉ b.val.1 →
      ∀ k : K, schwartzBruhatStageRealization a e φ (x * k.val) = 0 := fun x hx k ↦ by
    rw [hR]
    refine dite_eq_right fun hxk ↦ hx ?_
    rw [hb₁]
    exact ⟨x * k.val, hxk, by simp⟩
  have htrans : ∀ (h : H) (k₀ : K),
      (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k₀.val * k.val)) =
        fun k ↦ schwartzBruhatStageRealization a e φ (h.val * (k₀ * k).val) := fun h k₀ ↦ by
    funext k
    simp [mul_assoc]
  have hintegrable : ∀ x : G,
      Integrable (fun k : K ↦ schwartzBruhatStageRealization a e φ (x * k.val)) μK := by
    intro x
    by_cases hx : (QuotientGroup.mk x : G ⧸ K) ∈ b.val.1
    · obtain ⟨h, k₀, rfl⟩ := hsplit x hx
      rw [htrans h k₀]
      exact (hkey h).1.comp_mul_left k₀
    · simp_rw [hzero x hx]
      exact integrable_zero _ _ _
  refine ⟨hintegrable, ?_⟩
  have hfun : lcaCosetIntegral K μK (schwartzBruhatStageRealization a e φ) =
      schwartzBruhatStageRealization b e' ψ := by
    funext q
    have h1 := schwartzBruhatStageRealization_apply b e' ψ q
    show (∫ k : K, schwartzBruhatStageRealization a e φ ((Quotient.out q) * k.val) ∂μK) = _
    have hq : (QuotientGroup.mk (Quotient.out q) : G ⧸ K) = q := QuotientGroup.out_eq' q
    split_ifs at h1 with hqb
    · have hqb' : (QuotientGroup.mk (Quotient.out q) : G ⧸ K) ∈ b.val.1 := by rw [hq]; exact hqb
      refine Eq.trans ?_ h1.symm
      have hs := hsplit (Quotient.out q) hqb'
      let h : H := Classical.choose hs
      have hs' := Classical.choose_spec hs
      let k₀ : K := Classical.choose hs'
      have hx : Quotient.out q = h.val * k₀.val := Classical.choose_spec hs'
      clear_value h k₀
      have hhq : (QuotientGroup.mk h.val : G ⧸ K) = q := by
        rw [← hq, hx, QuotientGroup.eq]
        simp
      have hhb : (QuotientGroup.mk h.val : G ⧸ K) ∈ b.val.1 := by rw [hhq]; exact hqb
      have hpq : p (π h) = QuotientGroup.mk ⟨q, hqb⟩ :=
        (hpmk h.val h.2 hhb).trans (congrArg _ (Subtype.ext hhq))
      have e1 : (fun k : K ↦ schwartzBruhatStageRealization a e φ (Quotient.out q * k.val)) =
          fun k ↦ schwartzBruhatStageRealization a e φ (h.val * (k₀ * k).val) := by
        funext k
        simp only [hx, mul_assoc, Subgroup.coe_mul]
      calc ∫ k : K, schwartzBruhatStageRealization a e φ (Quotient.out q * k.val) ∂μK
          = ∫ k : K, schwartzBruhatStageRealization a e φ (h.val * (k₀ * k).val) ∂μK :=
            congrArg (fun F : K → ℂ ↦ ∫ k, F k ∂μK) e1
        _ = ∫ k : K, schwartzBruhatStageRealization a e φ (h.val * k.val) ∂μK :=
            integral_mul_left_eq_self
              (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k.val)) k₀
        _ = ψ (Multiplicative.toAdd (e'.equiv (p (π h)))) := (hkey h).2
        _ = _ := congrArg (fun y ↦ ψ (Multiplicative.toAdd (e'.equiv y))) hpq
    · have hqb' : (QuotientGroup.mk (Quotient.out q) : G ⧸ K) ∉ b.val.1 := by rw [hq]; exact hqb
      refine Eq.trans ?_ h1.symm
      simp_rw [hzero (Quotient.out q) hqb']
      exact integral_zero _ _
  rw [hfun]
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem e' ⟨ψ, rfl⟩)

omit [TopologicalSpace G] hTop hT2 hLC hBorel hK hHaarK hRegularK in
/-- The coset integral is additive on functions whose restrictions to all cosets
are integrable. -/
theorem lcaCosetIntegral_add (f g : G → ℂ)
    (hf : ∀ x : G, Integrable (fun k : K ↦ f (x * k.val)) μK)
    (hg : ∀ x : G, Integrable (fun k : K ↦ g (x * k.val)) μK) :
    lcaCosetIntegral K μK (f + g) = lcaCosetIntegral K μK f + lcaCosetIntegral K μK g := by
  funext q
  simp only [lcaCosetIntegral, Pi.add_apply]
  exact integral_add (hf _) (hg _)

/-- Paper: Theorem D.1.7.1, p. 776. The integral of a Schwartz–Bruhat function
over each coset exists and gives a Schwartz–Bruhat function on the quotient. -/
theorem lcaCosetIntegral_mem_schwartzBruhat (f : SchwartzBruhat G) :
    (∀ x : G, Integrable (fun k : K ↦ f (x * k.val)) μK) ∧
      lcaCosetIntegral K μK f ∈ schwartzBruhatSubmodule (G ⧸ K) := by
  have hf := (show schwartzBruhatSubmodule G from f).property
  generalize (show schwartzBruhatSubmodule G from f).val = g at hf ⊢
  let P : (G → ℂ) → Prop := fun g ↦
    (∀ x : G, Integrable (fun k : K ↦ g (x * k.val)) μK) ∧
      lcaCosetIntegral K μK g ∈ schwartzBruhatSubmodule (G ⧸ K)
  have hzero : P 0 := by
    refine ⟨fun x ↦ integrable_zero _ _ _, ?_⟩
    have : lcaCosetIntegral K μK (0 : G → ℂ) = 0 := by
      funext q
      simp [lcaCosetIntegral]
    rw [this]
    exact zero_mem _
  have hadd : ∀ g₁ g₂, P g₁ → P g₂ → P (g₁ + g₂) := fun g₁ g₂ h₁ h₂ ↦ by
    refine ⟨fun x ↦ (h₁.1 x).add (h₂.1 x), ?_⟩
    rw [lcaCosetIntegral_add K μK g₁ g₂ h₁.1 h₂.1]
    exact add_mem h₁.2 h₂.2
  refine Submodule.iSup_induction (motive := P) _ hf (fun a g ha ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ ha (fun e g he ↦ ?_) hzero hadd
  obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp he
  exact lcaCosetIntegral_stageRealization_mem K μK hK a e φ

/-- Paper: (D.1.7.1)–(D.1.7.2), p. 776. Take the existing coset integral with
values in the Schwartz–Bruhat space on the quotient. -/
def schwartzBruhatCosetIntegral (f : SchwartzBruhat G) : SchwartzBruhat (G ⧸ K) :=
  ⟨lcaCosetIntegral K μK f, (lcaCosetIntegral_mem_schwartzBruhat K μK hK f).2⟩

/-- Paper: (D.1.7.2), p. 776. At a quotient point represented by x the
Schwartz–Bruhat coset integral is the integral along the translate by x. -/
theorem schwartzBruhatCosetIntegral_mk (f : SchwartzBruhat G) (x : G) :
    schwartzBruhatCosetIntegral K μK hK f (QuotientGroup.mk x) =
      ∫ k : K, f (x * k.val) ∂μK := by
  show lcaCosetIntegral K μK f (QuotientGroup.mk x) = _
  exact lcaCosetIntegral_mk K μK f x ((lcaCosetIntegral_mem_schwartzBruhat K μK hK f).1 x)

include hHaar hRegular in
/-- Paper: Theorem D.1.7.1(1), p. 776. The coset integral is obtained by integrating
the Fourier transform over the annihilator against the quotient's dual Haar measure.
Deviation: The dual of the quotient is used directly and its characters
are pulled back to G, so the integral uses the specified Plancherel normalization. -/
theorem schwartzBruhat_poisson (μQ : Measure (G ⧸ K)) (hQ : IsWeilQuotientMeasure K μ μK μQ)
    (νQ : Measure (PontryaginDual (G ⧸ K))) (hνQ : IsLCAPlancherelMeasure μQ νQ)
    (f : SchwartzBruhat G) (x : G) :
    let q : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K, continuous_quotient_mk'⟩
    Integrable (f : G → ℂ) μ ∧
      Integrable (fun χ ↦ lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ)) νQ ∧
      schwartzBruhatCosetIntegral K μK hK f (q x) =
        ∫ χ, lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ) ∂νQ := by sorry

/-- Paper: Theorem D.1.7.1(2), p. 776. The coset integral on Schwartz–Bruhat
functions is a continuous linear map. -/
theorem schwartzBruhatCosetIntegral_continuousLinear :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      ∀ f, P f = schwartzBruhatCosetIntegral K μK hK f := by sorry

/-- Paper: Theorem D.1.7.1(2), p. 776. Every Schwartz–Bruhat function on the
quotient is the coset integral of a Schwartz–Bruhat function on the group. -/
theorem schwartzBruhatCosetIntegral_surjective :
    Function.Surjective (schwartzBruhatCosetIntegral K μK hK) := by sorry

/-- Paper: Theorem D.1.7.1(2), p. 776. Under second countability the coset
integral is a topological quotient map. -/
theorem schwartzBruhatCosetIntegral_isQuotientMap [SecondCountableTopology G] :
    IsQuotientMap (schwartzBruhatCosetIntegral K μK hK) := by sorry

end AveragingAndFourier

section Supports

open UniformSpace

local instance sec1cContinuousSMulSeminorms {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H]
  [hTopH : IsTopologicalGroup H] [hT2H : T2Space H] [hLCH : LocallyCompactSpace H]

include hTop hT2 hLC

include hTopH hT2H hLCH in
/-- Paper: Lemma D.1.8.1(1), p. 778. Multiplication of functions on the factors
gives a continuous linear isomorphism from the completed inductive tensor product
onto the Schwartz–Bruhat space of the product. -/
theorem schwartzBruhat_kernel_equiv [SecondCountableTopology G] [SecondCountableTopology H] :
    ∃ e : Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) ≃L[ℂ]
        SchwartzBruhat (G × H),
      ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (x : G) (y : H),
        e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
          (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y := by sorry

/-- Paper: Lemma D.1.8.1(2), p. 778. The completed projective tensor product
of the strong duals is the strong dual on the product. On pure tensors
the identification multiplies the two evaluations. -/
theorem schwartzBruhat_strongDual_kernel_equiv [SecondCountableTopology G]
    [SecondCountableTopology H]
    (e : Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) ≃L[ℂ]
      SchwartzBruhat (G × H))
    (he : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (x : G) (y : H),
      e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
        (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y) :
    ∃ E : Completion (ProjectiveTensor (StrongDual ℂ (SchwartzBruhat G))
          (StrongDual ℂ (SchwartzBruhat H))) ≃L[ℂ] StrongDual ℂ (SchwartzBruhat (G × H)),
      ∀ (S : StrongDual ℂ (SchwartzBruhat G)) (T : StrongDual ℂ (SchwartzBruhat H))
        (f : SchwartzBruhat G) (g : SchwartzBruhat H),
        E (Completion.coe' (α := ProjectiveTensor (StrongDual ℂ (SchwartzBruhat G))
          (StrongDual ℂ (SchwartzBruhat H))) (S ⊗ₜ[ℂ] T))
          (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
            (f ⊗ₜ[ℂ] g))) = S f * T g := by sorry

-- TODO(paper-gap): The proof after (D.1.8.3) cites part (1) for the strong-dual
-- tensor identification at the Fréchet stages. That step uses the nuclear Fréchet result.

/-- Paper: Definition D.1.8.2(1), p. 779. The vanishing locus is the union of
open sets on which the distribution kills all Schwartz–Bruhat tests supported there. -/
def schwartzBruhatVanishingLocus (T : StrongDual ℂ (SchwartzBruhat G)) : Set G :=
  ⋃₀ {U | IsOpen U ∧ ∀ f : SchwartzBruhat G, tsupport (f : G → ℂ) ⊆ U → T f = 0}

/-- Paper: Definition D.1.8.2(2), p. 779. The support is the complement of the
vanishing locus. -/
def schwartzBruhatDistributionSupport (T : StrongDual ℂ (SchwartzBruhat G)) : Set G :=
  (schwartzBruhatVanishingLocus T)ᶜ

/-- Paper: Definition D.1.8.2, p. 779. Point evaluation vanishes precisely off
the evaluation point and has singleton support.
Deviation: Sanity check on both the vanishing locus and the support. -/
theorem schwartzBruhat_dirac_support (x : G) :
    ∃ δ : StrongDual ℂ (SchwartzBruhat G),
      (∀ f, δ f = f x) ∧
      schwartzBruhatVanishingLocus δ = {x}ᶜ ∧ schwartzBruhatDistributionSupport δ = {x} :=
  by sorry

omit hTop hT2 hLC in
/-- Paper: Proposition D.1.8.3, p. 779. The support of a tensor product of four
tempered distributions on the elementary factors is the product of their supports.
Deviation: The tensor distribution is characterized by its pairings with pure tensors. -/
theorem elementary_schwartzBruhat_tensor_support
    (m n r : ℕ) {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    let R := Multiplicative (EuclideanSpace ℝ (Fin m))
    let T := Multiplicative (Fin n → AddCircle (1 : ℝ))
    let Z := Multiplicative (Fin r → ℤ)
    let A := Multiplicative F
    ∀ (d₁ : StrongDual ℂ (SchwartzBruhat R)) (d₂ : StrongDual ℂ (SchwartzBruhat T))
      (d₃ : StrongDual ℂ (SchwartzBruhat Z)) (d₄ : StrongDual ℂ (SchwartzBruhat A))
      (d : StrongDual ℂ (SchwartzBruhat (R × T × Z × A))),
      (∀ (f₁ : SchwartzBruhat R) (f₂ : SchwartzBruhat T) (f₃ : SchwartzBruhat Z)
        (f₄ : SchwartzBruhat A), ∃ f : SchwartzBruhat (R × T × Z × A),
        (∀ x, f x = f₁ x.1 * f₂ x.2.1 * f₃ x.2.2.1 * f₄ x.2.2.2) ∧
        d f = d₁ f₁ * d₂ f₂ * d₃ f₃ * d₄ f₄) →
      schwartzBruhatDistributionSupport d =
        schwartzBruhatDistributionSupport d₁ ×ˢ (schwartzBruhatDistributionSupport d₂ ×ˢ
          (schwartzBruhatDistributionSupport d₃ ×ˢ schwartzBruhatDistributionSupport d₄)) :=
  by sorry

open Classical in
/-- Paper: Lemma D.1.8.4, p. 780. Pullback and extension by zero are continuous
on a structural quotient and induce restriction of a tempered distribution.
The vanishing locus of the original distribution is covered by the lifted
vanishing loci of these restrictions. -/
theorem schwartzBruhatVanishingLocus_subset_stages (T : StrongDual ℂ (SchwartzBruhat G)) :
    ∃ j : ∀ a : BruhatStructuralPair G, SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G,
      (∀ (a : BruhatStructuralPair G) (f : SchwartzBruhat a.quotient) (x : G),
        j a f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x, hx⟩) else 0) ∧
      schwartzBruhatVanishingLocus T ⊆
        ⋃ a : BruhatStructuralPair G,
          Subtype.val '' (QuotientGroup.mk ⁻¹' schwartzBruhatVanishingLocus (T.comp (j a))) :=
  by sorry

end Supports

section Translations

variable {H E : Type*} [Group H] [TopologicalSpace H] [hTopH : IsTopologicalGroup H]

include hTopH in
/-- Paper: Lemma D.1.9.1, p. 780. A linear group action on a strict inductive
limit of barrelled spaces is continuous if it jointly acts at each stage through
the corresponding subsystem of open subgroups.
Deviation: Stages are identified with their images with the subspace topology.
Linearity is explicit, as in the proof's representation by linear operators. -/
theorem continuous_action_strict_inductive_limit [T2Space H] [LocallyCompactSpace H]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E]
    (K : ℕ → OpenSubgroup H) (hK : Monotone K) (hK' : ∀ h : H, ∃ n, h ∈ K n)
    (S : ℕ → Submodule ℂ E) (hS : Monotone S) (hS' : ∀ x : E, ∃ n, x ∈ S n)
    (hFinal : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun n ↦ (S n).subtype))
    (hBarrelled : ∀ n, BarrelledSpace ℂ (S n))
    (ρ : H →* (E ≃ₗ[ℂ] E))
    (hPreserve : ∀ n (k : K n) (x : S n), ρ k.val x.val ∈ S n)
    (hContinuous : ∀ n, Continuous (fun p : K n × S n ↦ ρ p.1.val p.2.val)) :
    Continuous (fun p : H × E ↦ ρ p.1 p.2) := by sorry

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

omit hTop hT2 hLC in
/-- Paper: Proposition D.1.9.2, p. 781. On an elementary group, shifting the argument
by addition preserves the Schwartz space and is jointly continuous for the weighted
derivative seminorm topology. -/
theorem elementarySchwartz_translate_jointly {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    ∃ T : C(ElementaryLieGroup m n r F × ElementarySchwartz m n r F,
        ElementarySchwartz m n r F),
      ∀ g f x, T (g, f) x = f (g + x) := by
  sorry

/-- A stage can be enlarged to contain any prescribed translating element. -/
private theorem exists_bruhatStructuralPair_le_mem (a : BruhatStructuralPair G) (g : G) :
    ∃ b : BruhatStructuralPair G, a ≤ b ∧ g ∈ b.val.1 := by
  let I := OpenCompactlyGeneratedSubgroups G
  have hGroups := openCompactlyGeneratedSubgroups_colimit (G := G)
  let : IsDirectedOrder I := hGroups.1
  obtain ⟨J, hgJ⟩ := hGroups.2.1 g
  let aGroup : I := ⟨a.val.1, a.property.1, a.property.2.1⟩
  obtain ⟨H, haH, hJH⟩ := exists_ge_ge aGroup J
  let b : BruhatStructuralPair G := ⟨(H.val, a.val.2), H.property.1, H.property.2,
    a.property.2.2.1, a.property.2.2.2.trans haH⟩
  exact ⟨b, ⟨haH, le_rfl⟩, hJH hgJ⟩

/-- Paper: Proposition D.1.9.2, p. 781. A left translate of a Schwartz–Bruhat
function is again Schwartz–Bruhat. -/
theorem schwartzBruhat_translate_mem (g : G) (f : SchwartzBruhat G) :
    (fun x ↦ f (g⁻¹ * x)) ∈ schwartzBruhatSubmodule G := by
  classical
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff (fun x ↦ f x)).mp f.property
  obtain ⟨b, hab, hg⟩ := exists_bruhatStructuralPair_le_mem a g
  obtain ⟨e'⟩ := b.elementary
  obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition hab e e'
  obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly
    (m := e'.realDim) (n := e'.torusDim) (r := e'.latticeRank) (F := e'.finiteFactor)
  let h : b.val.1 := ⟨g, hg⟩
  let q (y : b.val.1) := (e'.equiv (QuotientGroup.mk y : b.quotient)).toAdd
  apply (mem_schwartzBruhatSubmodule_iff _).mpr
  refine ⟨b, e', T (q h⁻¹, j s), funext fun x ↦ ?_⟩
  rw [← congrFun hs (g⁻¹ * x), ← congrFun (hj s) (g⁻¹ * x)]
  have hmem := b.val.1.mul_mem_cancel_left (x := g⁻¹) (y := x) (b.val.1.inv_mem hg)
  by_cases hx : x ∈ b.val.1
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_left hx, dite_eq_left (hmem.mpr hx), hT]
    apply congrArg (fun y ↦ j s y)
    change q h⁻¹ + q ⟨x, hx⟩ = q (h⁻¹ * ⟨x, hx⟩)
    unfold q
    rw [QuotientGroup.mk_mul, map_mul]
    rfl
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_right hx, dite_eq_right (hmem.not.mpr hx)]

/-- Paper: Proposition D.1.9.2, p. 781. The left translation by g evaluates
the original function at g⁻¹x. -/
def schwartzBruhatTranslate (g : G) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨fun x ↦ f (g⁻¹ * x), schwartzBruhat_translate_mem g f⟩

/-- Paper: Proposition D.1.9.2, p. 781. Translating a test function by g and
evaluating at gx recovers its original value at x.
Deviation: Sanity check on the direction of left translation. -/
theorem schwartzBruhatTranslate_apply_mul (g x : G) (f : SchwartzBruhat G) :
    schwartzBruhatTranslate g f (g * x) = f x := by
  change f.val (g⁻¹ * (g * x)) = f.val x
  rw [inv_mul_cancel_left]

omit hTop hT2 hLC in
/-- The inclusion of a structural stage is continuous for the generating seminorms. -/
private theorem continuous_schwartzBruhatStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Continuous (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) :=
  (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property a e

/-- The quotient action gives translation by elements of the stage's own open subgroup. -/
private theorem continuous_schwartzBruhatTranslate_on_subgroup (b : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation b.quotient) :
    Continuous (fun p : b.val.1 × SchwartzBruhatStage e ↦
      schwartzBruhatTranslate p.1.val (schwartzBruhatStageInclusion b e p.2)) := by
  classical
  obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly
    (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  let q (h : b.val.1) := (e.equiv (QuotientGroup.mk h : b.quotient)).toAdd
  have hq : Continuous q := continuous_toAdd.comp
    (e.equiv.continuous.comp QuotientGroup.continuous_mk)
  have hCont : Continuous (fun p : b.val.1 × SchwartzBruhatStage e ↦
      (show SchwartzBruhat G from schwartzBruhatStageInclusion b e (T (q p.1⁻¹, p.2)))) :=
    (continuous_schwartzBruhatStageInclusion b e).comp
      (T.continuous.comp ((hq.comp continuous_fst.inv).prodMk continuous_snd))
  refine hCont.congr fun ⟨h, s⟩ ↦ ?_
  refine Subtype.ext (funext fun x ↦ ?_)
  change schwartzBruhatStageRealization b e (T (q h⁻¹, s)) x =
    schwartzBruhatStageRealization b e s ((h : G)⁻¹ * x)
  have hmem := b.val.1.mul_mem_cancel_left (x := (h : G)⁻¹) (y := x)
    (b.val.1.inv_mem h.property)
  by_cases hx : x ∈ b.val.1
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_left hx, dite_eq_left (hmem.mpr hx), hT]
    apply congrArg (fun y ↦ s y)
    change q h⁻¹ + q ⟨x, hx⟩ = q (h⁻¹ * ⟨x, hx⟩)
    unfold q
    rw [QuotientGroup.mk_mul, map_mul]
    rfl
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_right hx, dite_eq_right (hmem.not.mpr hx)]

/-- Translation is jointly continuous when the function varies in a fixed structural stage.
Locally the translating element and the function are handled in one larger stage. -/
private theorem continuous_schwartzBruhatTranslate_stage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Continuous (fun p : G × SchwartzBruhatStage e ↦
      schwartzBruhatTranslate p.1 (schwartzBruhatStageInclusion a e p.2)) := by
  rw [continuous_iff_continuousAt]
  intro ⟨g, f⟩
  obtain ⟨b, hab, hgb⟩ := exists_bruhatStructuralPair_le_mem a g
  obtain ⟨e'⟩ := b.elementary
  obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (a := a) (b := b) hab e e'
  have hOpen : IsOpenEmbedding (Prod.map (Subtype.val : b.val.1 → G)
      (id : SchwartzBruhatStage e → SchwartzBruhatStage e)) :=
    b.property.1.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  apply (hOpen.continuousAt_iff (x := (⟨g, hgb⟩, f))).mp
  have hCont : Continuous (fun p : b.val.1 × SchwartzBruhatStage e ↦
      schwartzBruhatTranslate p.1.val (schwartzBruhatStageInclusion b e' (j p.2))) :=
    (continuous_schwartzBruhatTranslate_on_subgroup b e').comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd))
  refine (hCont.congr fun p ↦ ?_).continuousAt
  exact congrArg (schwartzBruhatTranslate p.1.val) (Subtype.ext (hj p.2))

open scoped ComplexOrder in
/-- Paper: Proposition D.1.9.2, p. 781. For a second-countable group, left
translation is jointly continuous in the group element and Schwartz–Bruhat function. -/
theorem schwartzBruhatTranslate_continuous [SecondCountableTopology G] :
    Continuous (fun p : G × SchwartzBruhat G ↦ schwartzBruhatTranslate p.1 p.2) := by
  let E := SchwartzBruhat G
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : LocallyConvexSpace ℂ E := .ofBasisZero ℂ E _ _ (LocallyConvexSpace.convex_basis_zero ℝ E)
    (fun _ hs ↦ convex_of_nonneg_surjective_algebraMap ℂ
      (fun _ hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) hs.2)
  let : ContinuousSMul ℝ C(G, E) := IsScalarTower.continuousSMul ℂ
  have hOrbit (f : E) : Continuous (fun g ↦ schwartzBruhatTranslate g f) := by
    obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    have hf : (show E from schwartzBruhatStageInclusion a e s) = f := Subtype.ext hs
    rw [← hf]
    exact (continuous_schwartzBruhatTranslate_stage a e).comp (continuous_id.prodMk continuous_const)
  let A : E →ₗ[ℂ] C(G, E) :=
    { toFun := fun f ↦ ⟨fun g ↦ schwartzBruhatTranslate g f, hOrbit f⟩
      map_add' := fun f s ↦ ContinuousMap.ext fun g ↦ Subtype.ext rfl
      map_smul' := fun c f ↦ ContinuousMap.ext fun g ↦ Subtype.ext rfl }
  -- The linear map into the compact-open space is continuous on each stage.
  -- Its seminorm pullbacks are therefore among the defining seminorms of E.
  have hA : Continuous A := by
    let P : SeminormFamily ℂ E {q : Seminorm ℂ E //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine (PolynormableSpace.withSeminorms ℂ C(G, E)).continuous_of_continuous_comp A fun p ↦ ?_
    refine hP.continuous_seminorm ⟨p.val.comp A, ?_⟩
    intro a e
    have hStage : Continuous (fun s : SchwartzBruhatStage e ↦ A (schwartzBruhatStageInclusion a e s)) :=
      ContinuousMap.continuous_of_continuous_uncurry _ <|
        (continuous_schwartzBruhatTranslate_stage a e).comp continuous_swap
    exact p.property.comp hStage
  exact continuous_eval.comp ((hA.comp continuous_snd).prodMk continuous_fst)

/-- Paper: Proposition D.1.9.2, p. 781. Translations by a compact set of group
elements send one common zero-neighborhood into any prescribed zero-neighborhood. -/
theorem schwartzBruhatTranslate_equicontinuous [SecondCountableTopology G]
    (K : Set G) (hK : IsCompact K) {U : Set (SchwartzBruhat G)} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : SchwartzBruhat G),
      ∀ g ∈ K, ∀ f ∈ V, schwartzBruhatTranslate g f ∈ U := by sorry

-- TODO(paper-gap): D.1.9.3 omits additivity of the action. The proof uses
-- distributivity over sums, and the statement fails for actions by arbitrary homeomorphisms.

omit hTop hT2 hLC in
include hTopH in
/-- Paper: Lemma D.1.9.3, p. 781. A complex linear action on the completion
is jointly continuous if each operator is continuous and the invariant original
space has a jointly continuous action.
Deviation: The linear action needed for the addition identities in the proof is explicit. -/
theorem continuous_action_completion [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E]
    (ρ : H →* (UniformSpace.Completion E ≃ₗ[ℂ] UniformSpace.Completion E))
    (hEach : ∀ h : H, Continuous (ρ h))
    (τ : H →* (E ≃ₗ[ℂ] E))
    (hτ : ∀ h (x : E), ρ h (x : UniformSpace.Completion E) = (τ h x : UniformSpace.Completion E))
    (hJoint : Continuous (fun p : H × E ↦ τ p.1 p.2)) :
    Continuous (fun p : H × UniformSpace.Completion E ↦ ρ p.1 p.2) := by sorry

omit hTop hT2 hLC in
include hTopH in
/-- Paper: Lemma D.1.9.4, p. 782. The diagonal action induced by continuous
linear actions on both factors is jointly continuous on their projective tensor product. -/
theorem continuous_action_projectiveTensor
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [T2Space E] [T2Space F] [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (ρ : H →* (E ≃ₗ[ℂ] E)) (τ : H →* (F ≃ₗ[ℂ] F))
    (hρ : Continuous (fun p : H × E ↦ ρ p.1 p.2))
    (hτ : Continuous (fun p : H × F ↦ τ p.1 p.2)) :
    Continuous (fun p : H × ProjectiveTensor E F ↦
      (show ProjectiveTensor E F from
        TensorProduct.map (ρ p.1).toLinearMap (τ p.1).toLinearMap p.2)) := by sorry

end Translations

end RiemannMasullo
