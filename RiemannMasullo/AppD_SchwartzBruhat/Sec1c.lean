module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
public import Mathlib.Analysis.Calculus.Deriv.Basic
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import RiemannMasullo.ForMathlib.MeasureTheory.Function.ContinuousMapDense
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Barrelled
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Compactness.CompactlyCoherentSpace
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

end DifferentialOperators

/-- Smoothness on the covering space descends to continuity on each discrete fiber. -/
private theorem elementarySchwartz_continuousFunction {m n r : ℕ} {F : Type*}
    [TopologicalSpace F] [DiscreteTopology F] (f : ElementarySchwartz m n r F) : Continuous f.val := by
  let q (t : EuclideanSpace ℝ (Fin n)) : Fin n → AddCircle (1 : ℝ) := fun j ↦ (t j : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q := by
    exact (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  let e := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ))
    ((Fin r → ℤ) × F)
  apply e.isQuotientMap.continuous_iff.mpr
  apply continuous_prod_of_discrete_right.mpr
  intro z
  exact (IsOpenQuotientMap.id.prodMap hq).isQuotientMap.continuous_iff.mpr
    (f.property.1 z.1 z.2).continuous

section FourierPairing

open scoped BoundedContinuousFunction ZeroAtInfty

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Every stage realization extends to a bounded continuous function on the group. -/
private theorem schwartzBruhat_boundedContinuous (f : SchwartzBruhat G) :
    ∃ g : G →ᵇ ℂ, ∀ x, g x = f x := by
  classical
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let p := elementarySchwartzSeminorm (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor) (0,0,0,0)
  have hb (y) : ‖s y‖ ≤ p s := by
    change (‖s y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val (0,0,0,0)).toReal
    apply ENNReal.toReal_mono (s.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun w ↦ (‖s w‖₊ : ENNReal)) y
  have hopen := a.property.1
  have hclosed := a.val.1.isClosed_of_isOpen hopen
  let u := schwartzBruhatStageRealization a e s
  have hu : Continuous u := by
    rw [← continuousOn_univ, ← union_compl_self (a.val.1 : Set G),
      continuousOn_union_iff_of_isOpen hopen hclosed.isOpen_compl]
    constructor
    · rw [continuousOn_iff_continuous_domRestrict]
      refine ((elementarySchwartz_continuousFunction s).comp (continuous_toAdd.comp
        (e.equiv.continuous.comp QuotientGroup.continuous_mk))).congr fun y ↦ ?_
      change _ = schwartzBruhatStageRealization a e s (y : G)
      rw [schwartzBruhatStageRealization_apply, dite_eq_left y.property]
      rfl
    · apply continuousOn_const.congr
      intro y hy
      change schwartzBruhatStageRealization a e s y = 0
      rw [schwartzBruhatStageRealization_apply, dite_eq_right (show y ∉ a.val.1 from hy)]
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup u hu (p s) (fun x ↦ ?_), congrFun hs⟩
  dsimp only [u]
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · rw [norm_zero]
    exact apply_nonneg p s

variable [MeasurableSpace G] [BorelSpace G]
private local instance inverseFourierDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (ν : @Measure (PontryaginDual G) (borel _))
omit [μ.IsHaarMeasure] in
/-- The inverse Fourier integral and the forward transform are adjoint on integrable
test functions. Compactly supported approximations provide a product-measurable kernel
even when the product topology and product σ-algebra have different Borel sets. -/
private theorem lcaInverseFourier_integral_pairing
    {u : PontryaginDual G → ℂ} {q : G → ℂ} (hu : Integrable u ν) (hq : Integrable q μ)
    [ν.Regular] :
    (∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ) =
      ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨S, -, hqZero, hSσ⟩ := hq.aefinStronglyMeasurable.exists_set_sigmaFinite
  obtain ⟨T, -, huZero, hTσ⟩ := hu.aefinStronglyMeasurable.exists_set_sigmaFinite
  let := hSσ
  let := hTσ
  have hqZero := ae_imp_of_ae_restrict hqZero
  have huZero := ae_imp_of_ae_restrict huZero
  obtain ⟨Q, hQc, hQ, htQ⟩ := exists_tendsto_ae_compactSupport hq
  obtain ⟨U, hUc, hU, htU⟩ := exists_tendsto_ae_compactSupport hu
  let K (x : G) (χ : PontryaginDual G) := (u χ * (χ x : ℂ)) * star (q x)
  let A (n : ℕ) (p : G × PontryaginDual G) := (U n p.2 * (p.2 p.1 : ℂ)) * star (Q n p.1)
  have hEval : Continuous (fun p : G × PontryaginDual G ↦ (p.2 p.1 : ℂ)) :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk continuous_fst))
  have hA (n : ℕ) : StronglyMeasurable (A n) := by
    apply HasCompactSupport.stronglyMeasurable_of_prod
      ((((hU n).comp continuous_snd).mul hEval).mul ((hQ n).comp continuous_fst).star)
    refine HasCompactSupport.intro ((hQc n).prod (hUc n)) ?_
    intro p hp
    by_cases hq : p.1 ∈ tsupport (Q n)
    · have hu : U n p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun hu ↦ hp ⟨hq, hu⟩)
      simp [hu]
    · simp [image_eq_zero_of_notMem_tsupport hq]
  let k (p : G × PontryaginDual G) := limUnder atTop (fun n ↦ A n p)
  have hk : StronglyMeasurable k := StronglyMeasurable.limUnder hA
  have hLimit : ∀ᵐ x ∂μ, ∀ᵐ χ ∂ν, k (x, χ) = K x χ := by
    filter_upwards [htQ] with x hx
    filter_upwards [htU] with χ hχ
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hLimit' : ∀ᵐ χ ∂ν, ∀ᵐ x ∂μ, k (x, χ) = K x χ := by
    filter_upwards [htU] with χ hχ
    filter_upwards [htQ] with x hx
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hChar (x : G) : AEStronglyMeasurable (fun χ : PontryaginDual G ↦ (χ x : ℂ)) ν :=
    (hEval.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hRow (x : G) : Integrable (K x) ν :=
    (hu.mul_bdd (c := 1) (hChar x) (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le)).mul_const _
  have hInt : Integrable k ((μ.restrict S).prod (ν.restrict T)) := by
    apply (integrable_prod_iff hk.aestronglyMeasurable).2
    have hLim : ∀ᵐ x ∂μ.restrict S, (fun χ ↦ k (x, χ)) =ᵐ[ν.restrict T] K x :=
      ae_restrict_of_ae (hLimit.mono fun _ hx ↦ ae_restrict_of_ae hx)
    refine ⟨hLim.mono fun x hx ↦ (hRow x).restrict.congr hx.symm, ?_⟩
    refine (hq.norm.mul_const (∫ χ in T, ‖u χ‖ ∂ν)).restrict.congr ?_
    filter_upwards [hLim] with x hx
    symm
    calc
      _ = ∫ χ in T, ‖K x χ‖ ∂ν := integral_congr_ae (hx.mono fun χ hχ ↦ congrArg norm hχ)
      _ = _ := by simp [K, integral_mul_const, mul_comm]
  have hrowEq : ∀ᵐ x ∂μ, (∫ χ in T, k (x, χ) ∂ν) = ∫ χ, K x χ ∂ν := by
    filter_upwards [hLimit] with x hx
    rw [integral_congr_ae (ae_restrict_of_ae hx)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem]
  have hcolEq : ∀ᵐ χ ∂ν, (∫ x in S, k (x, χ) ∂μ) = ∫ x, K x χ ∂μ := by
    filter_upwards [hLimit'] with χ hχ
    rw [integral_congr_ae (ae_restrict_of_ae hχ)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem]
  calc
    _ = ∫ x, ∫ χ, K x χ ∂ν ∂μ := by simp_rw [K, integral_mul_const]
    _ = ∫ x in S, ∫ χ, K x χ ∂ν ∂μ := by
      symm
      exact setIntegral_eq_integral_of_ae_compl_eq_zero
        (hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem])
    _ = ∫ x in S, ∫ χ in T, k (x, χ) ∂ν ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hrowEq.mono fun _ hx ↦ hx.symm))
    _ = ∫ χ in T, ∫ x in S, k (x, χ) ∂μ ∂ν := integral_integral_swap hInt
    _ = ∫ χ in T, ∫ x, K x χ ∂μ ∂ν := integral_congr_ae (ae_restrict_of_ae hcolEq)
    _ = ∫ χ, ∫ x, K x χ ∂μ ∂ν := setIntegral_eq_integral_of_ae_compl_eq_zero
      (huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem])
    _ = _ := by
      congr with χ
      simp only [K, mul_assoc, integral_const_mul, lcaFourier, Complex.star_def,
        ← integral_conj, map_mul, starRingEnd_self_apply]
      congr 1
      apply integral_congr_ae
      exact .of_forall fun x ↦ mul_comm _ _

/-- Invert an integrable Plancherel transform by pairing against indicators of finite-measure sets. -/
private theorem lcaInverseFourier_zeroAtInfty (hν : IsLCAPlancherelMeasure μ ν)
    (v : Lp ℂ 2 μ) (u : PontryaginDual G → ℂ) (hu : Integrable u ν)
    (hv : ((lcaFourier_unitary μ ν hν).exists.choose v : PontryaginDual G → ℂ) =ᵐ[ν] u) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] (v : G → ℂ) ∧
      ∀ x, F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨H, hH⟩ := lcaFourier_zeroAtInfty ν hu
  let e : CocompactMap G (PontryaginDual (PontryaginDual G)) :=
    ⟨⟨pontryaginDual_eval, pontryaginDual_eval.continuous⟩,
      isClosedEmbedding_pontryaginDual_eval.tendsto_cocompact⟩
  let F : C₀(G, ℂ) := (H.comp e).comp
    ⟨⟨Inv.inv, continuous_inv⟩, (Homeomorph.inv G).isClosedEmbedding.tendsto_cocompact⟩
  have hF (x : G) : F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
    change H (pontryaginDual_eval x⁻¹) = _
    rw [hH]
    unfold lcaFourier
    apply integral_congr_ae
    exact .of_forall fun χ ↦ by
      change u χ * star (χ x⁻¹ : ℂ) = _
      rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  refine ⟨F, ?_, hF⟩
  -- The nonzero set of a function in C₀ lies in a countable union of compact sets.
  let K (n : ℕ) : Set G := {x | 1 / ((n : ℝ) + 1) ≤ ‖F x‖}
  have hK (n : ℕ) : IsCompact (K n) := by
    have hc : IsClosed (K n) := isClosed_le continuous_const F.continuous.norm
    obtain ⟨L, hL, hsub⟩ := mem_cocompact.mp
      ((Metric.tendsto_nhds.mp F.zero_at_infty') _ (by positivity : 0 < 1 / ((n : ℝ) + 1)))
    exact hL.of_isClosed_subset hc fun x hx ↦ by
      by_contra hxL
      change 1 / ((n : ℝ) + 1) ≤ ‖F x‖ at hx
      have hlt : dist (F x) 0 < 1 / ((n : ℝ) + 1) := hsub hxL
      exact not_lt_of_ge hx (dist_zero_right (F x) ▸ hlt)
  let S := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hFS : ∀ x ∈ Sᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hne)
    exact hx (mem_iUnion.mpr ⟨n, hn.le⟩)
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  have hFin : AEFinStronglyMeasurable (F : G → ℂ) μ :=
    (F.continuous.stronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite
      hS hFS hσ).aefinStronglyMeasurable
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq _ _ _
    hFin ((Lp.memLp v).aefinStronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top)
  · intro A _ hA
    let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA.ne
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F.toBCF‖
      (.of_forall F.toBCF.norm_coe_le_norm)
  · exact fun A _ hA ↦ integrableOn_Lp_of_measure_ne_top v (by norm_num) hA.ne
  · intro A hA hAμ
    let q : G → ℂ := A.indicator fun _ ↦ 1
    have hq : Integrable q μ := memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 hA.nullMeasurableSet 1 (.inr hAμ.ne))
    have hq₂ : MemLp q 2 μ := memLp_indicator_const 2 hA.nullMeasurableSet 1 (.inr hAμ.ne)
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    have hU := (lcaFourier_unitary μ ν hν).exists.choose_spec q hq hq₂
    have hIndic (g : G → ℂ) : (∫ x, g x * star (q x) ∂μ) = ∫ x in A, g x ∂μ := by
      rw [← integral_indicator hA]
      congr with x
      by_cases hx : x ∈ A <;> simp [q, hx]
    calc
      _ = ∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ := by
        simp_rw [← hF]
        exact (hIndic F).symm
      _ = ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν :=
        lcaInverseFourier_integral_pairing μ ν hu hq
      _ = inner ℂ (U (hq₂.toLp q)) (U v) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv, hU] with χ hχ hχ'
        rw [RCLike.inner_apply, starRingEnd_apply, hχ, hχ']
      _ = inner ℂ (hq₂.toLp q) v := U.inner_map_map _ _
      _ = _ := by
        rw [← hIndic v, L2.inner_def]
        exact integral_congr_ae (hq₂.coeFn_toLp.mono fun x hx ↦ by
          change inner ℂ ((hq₂.toLp q) x) (v x) = v x * star (q x)
          rw [RCLike.inner_apply, starRingEnd_apply, hx])

end FourierPairing

section StructuralProjectors

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
private local instance projectorDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Translation invariance makes the average of evaluations the indicator of the double annihilator. -/
private theorem integral_annihilator_eval (J : Subgroup G) (hJ : IsClosed (J : Set G))
    (η : Measure (lcaAnnihilator J)) [η.IsHaarMeasure] [IsProbabilityMeasure η] (x : G) :
    (∫ ψ : lcaAnnihilator J, (ψ.val x : ℂ) ∂η) = (J : Set G).indicator 1 x := by
  classical
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  by_cases hx : x ∈ J
  · rw [indicator_of_mem hx]
    simp only [fun ψ : lcaAnnihilator J ↦ (mem_lcaAnnihilator_iff J ψ.val).mp ψ.property ⟨x,hx⟩,
      Circle.coe_one,integral_const, Measure.real,measure_univ, ENNReal.toReal_one, one_smul, Pi.one_apply]
  · rw [indicator_of_notMem hx]
    have hnx : x ∉ lcaDualAnnihilator (lcaAnnihilator J) := by rwa [lcaDualAnnihilator_annihilator J hJ]
    obtain ⟨ψ,hψ⟩ := not_forall.mp (mt (mem_lcaDualAnnihilator_iff _ x).mpr hnx)
    have ht := integral_mul_left_eq_self (μ := η) (fun z : lcaAnnihilator J ↦ (z.val x : ℂ)) ψ
    change (∫ z : lcaAnnihilator J, (ψ.val x : ℂ) * (z.val x : ℂ) ∂η) = _ at ht
    rw [integral_const_mul] at ht
    by_contra hn
    exact hψ (Circle.ext ((mul_eq_right₀ hn).mp ht))

/-- Pair the twisted function with probability Haar on the annihilator to compute the transform of a cutoff. -/
private theorem lcaFourier_cutoff (J : Subgroup G) (hJ : IsOpen (J : Set G))
    (η : Measure (lcaAnnihilator J)) [η.IsHaarMeasure] [IsProbabilityMeasure η]
    {f : G → ℂ} (hf : Integrable f μ) (χ : PontryaginDual G) :
    lcaFourier μ ((J : Set G).indicator f) χ = ∫ ψ : lcaAnnihilator J, lcaFourier μ f (χ * ψ.val) ∂η := by
  classical
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hJc := J.isClosed_of_isOpen hJ
  have hA := isCompact_lcaAnnihilator J hJ
  let : CompactSpace (lcaAnnihilator J) := isCompact_iff_compactSpace.mp hA
  let ν := η.map (Subtype.val : lcaAnnihilator J → PontryaginDual G)
  let : ν.InnerRegular := Measure.InnerRegular.map_of_continuous continuous_subtype_val
  let : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.map _ η))
  have hmap (u : PontryaginDual G → ℂ) : (∫ ψ, u ψ ∂ν) = ∫ ψ : lcaAnnihilator J, u ψ.val ∂η :=
    hA.isClosed.isClosedEmbedding_subtypeVal.integral_map u
  let t (y : G) := f y * star (χ y : ℂ)
  have ht : Integrable t μ := integrable_fourierIntegrand μ hf χ
  have heq (ψ : PontryaginDual G) : lcaFourier μ t ψ = lcaFourier μ f (χ * ψ) := by
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      change (f y * star (χ y : ℂ)) * star (ψ y : ℂ) = f y * star ((χ y : ℂ) * (ψ y : ℂ))
      rw [star_mul]
      ring
  have h := lcaInverseFourier_integral_pairing μ ν (u := fun _ ↦ 1) (q := t) (integrable_const _) ht
  simp only [one_mul,heq] at h
  rw [hmap] at h
  have heval (x : G) : (∫ ψ : PontryaginDual G, (ψ x : ℂ) ∂ν) = (J : Set G).indicator 1 x :=
    (hmap _).trans (integral_annihilator_eval J hJc η x)
  simp_rw [heval] at h
  have h' := congrArg star h
  simp only [Complex.star_def, ← integral_conj, map_mul, starRingEnd_self_apply] at h'
  refine Eq.trans ?_ h'
  unfold lcaFourier
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ J <;> simp [hx,t]

/-- Apply the Weil formula to a compact average at trivial characters and translation invariance elsewhere. -/
private theorem lcaFourier_compact_average (K : Subgroup G) (hK : IsCompact (K : Set G))
    (η : Measure K) [η.IsHaarMeasure] [IsProbabilityMeasure η]
    {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hav : ∀ x, g x = ∫ k : K, f (x * k.val) ∂η) (χ : PontryaginDual G) :
    lcaFourier μ g χ = (lcaAnnihilator K : Set (PontryaginDual G)).indicator (lcaFourier μ f) χ := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hinv (x : G) (k : K) : g (x * k.val) = g x := by
    rw [hav,hav]
    simpa only [Subgroup.coe_mul,mul_assoc] using
      (integral_mul_left_eq_self (μ := η) (fun h : K ↦ f (x * h.val)) k)
  by_cases hχ : χ ∈ lcaAnnihilator K
  · rw [indicator_of_mem hχ]
    let : MeasurableSpace (G ⧸ K) := borel _
    obtain ⟨μQ,hQ,-⟩ := weilQuotientMeasure_existsUnique K hK.isClosed μ η
    let t (u : G → ℂ) (x : G) := u x * star (χ x : ℂ)
    have hgt := integrable_fourierIntegrand μ hg χ
    have hft := integrable_fourierIntegrand μ hf χ
    change (∫ x, t g x ∂μ) = ∫ x, t f x ∂μ
    refine (weilQuotientIntegral_L1 K hK.isClosed μ η μQ hQ hgt).2.2.trans ?_
    refine Eq.trans ?_ (weilQuotientIntegral_L1 K hK.isClosed μ η μQ hQ hft).2.2.symm
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    have hχk (k : K) : χ (z.out * k.val) = χ z.out := by
      rw [map_mul,(mem_lcaAnnihilator_iff K χ).mp hχ k,mul_one]
    change (∫ k : K, g (z.out * k.val) * star (χ (z.out * k.val) : ℂ) ∂η) =
      ∫ k : K, f (z.out * k.val) * star (χ (z.out * k.val) : ℂ) ∂η
    simp_rw [hχk, hinv, integral_mul_const]
    simp [hav]
  · rw [indicator_of_notMem hχ]
    obtain ⟨k,hk⟩ := not_forall.mp (mt (mem_lcaAnnihilator_iff K χ).mpr hχ)
    have h := lcaFourier_translate μ g k.val χ
    have he : (fun x ↦ g (k.val * x)) = g := funext fun x ↦ by rw [mul_comm,hinv]
    rw [he] at h
    by_contra hn
    exact hk (Circle.ext ((mul_eq_right₀ hn).mp h.symm))

/-- Normalized Haar integration is independent of the chosen Borel measurable-space instance. -/
private theorem integral_eq_normalized_compact_haar {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [CompactSpace H] [m : MeasurableSpace H] [hB : BorelSpace H]
    (η : Measure H) [η.IsHaarMeasure] [IsProbabilityMeasure η] (u : H → ℂ) :
    (letI : MeasurableSpace H := borel _
     let : BorelSpace H := ⟨rfl⟩
     ∫ y, u y ∂Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩, by simp⟩ : TopologicalSpace.PositiveCompacts H)) =
      ∫ y, u y ∂η := by
  obtain rfl := hB.measurable_eq
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let U : TopologicalSpace.PositiveCompacts H := ⟨⟨univ,isCompact_univ⟩,by simp⟩
  let : IsProbabilityMeasure (Measure.haarMeasure U) := ⟨Measure.haarMeasure_self⟩
  change (∫ y, u y ∂Measure.haarMeasure U) = _
  rw [Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.haarMeasure U) η]

/-- Compute the structural stage projection using any normalized Haar measure on its kernel. -/
private theorem schwartzBruhatStageAverage_normalized (a : BruhatStructuralPair G)
    (hK : IsCompact ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G))
    (η : Measure ↥(OrderDual.ofDual a.val.2)) [η.IsHaarMeasure] [IsProbabilityMeasure η]
    (f : G → ℂ) (x : G) : schwartzBruhatStageAverage a f x =
      (a.val.1 : Set G).indicator (fun x ↦ ∫ k : ↥(OrderDual.ofDual a.val.2), f (x * k.val) ∂η) x := by
  classical
  let K := OrderDual.ofDual a.val.2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  by_cases hx : x ∈ a.val.1
  · rw [indicator_of_mem hx]
    unfold schwartzBruhatStageAverage
    rw [ite_eq_left hx]
    refine (integral_eq_normalized_compact_haar η (fun k : K ↦ f (k.val * x))).trans ?_
    simp only [mul_comm _ x]
  · rw [indicator_of_notMem hx]
    unfold schwartzBruhatStageAverage
    rw [ite_eq_right hx]

end StructuralProjectors

section FourierDifferentiation

open scoped Pointwise Interval

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Powers of a symmetric compact generating set cover the group. -/
private theorem sigmaCompact_of_compactlyGenerated (hG : IsCompactlyGeneratedGroup G) : SigmaCompactSpace G := by
  obtain ⟨U,-,hc,hu⟩ := hG
  let C := U ∪ U⁻¹
  have hC : IsCompact C := hc.union hc.inv
  have hi : C⁻¹ = C := by simp [C,union_comm]
  have hall (x : G) (hx : x ∈ Subgroup.closure U) : ∃ n : ℕ, x ∈ C^n := by
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact ⟨1, by simpa using (show x ∈ C from Or.inl hx)⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i,hi⟩ := hx
      obtain ⟨j,hj⟩ := hy
      exact ⟨i+j, pow_add C i j ▸ Set.mul_mem_mul hi hj⟩
    | inv x _ hx =>
      obtain ⟨i,hi'⟩ := hx
      exact ⟨i, by simpa only [← inv_pow,hi] using (Set.inv_mem_inv.mpr hi')⟩
  have he : ⋃ n : ℕ, C^n = univ := iUnion_eq_univ_iff.mpr fun x ↦ hall x (by rw [hu]; trivial)
  have hp (n : ℕ) : IsCompact (C^n) := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [pow_succ] using ih.mul hC
  exact ⟨⟨fun n ↦ C^n,hp,he⟩⟩

/-- A Schwartz function is supported on a σ-compact open subgroup. -/
private theorem schwartzBruhat_supported_open (f : SchwartzBruhat G) :
    ∃ J : Subgroup G, IsOpen (J : Set G) ∧ IsSigmaCompact (J : Set G) ∧ ∀ x ∉ J, f x = 0 := by
  classical
  obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let J := a.val.1
  let : LocallyCompactSpace J := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : SigmaCompactSpace J := sigmaCompact_of_compactlyGenerated a.property.2.1
  refine ⟨J,a.property.1,?_,fun x hx ↦ ?_⟩
  · exact Subtype.range_coe (s := (J : Set G)) ▸ isSigmaCompact_range continuous_subtype_val
  · exact (congrFun hs x).symm.trans ((schwartzBruhatStageRealization_apply a e s x).trans (dite_eq_right hx))

/-- The Haar measure restricted to a σ-compact support is σ-finite. -/
private theorem sigmaFinite_restrict_sigmaCompact [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {S : Set G} (hS : IsSigmaCompact S) : SigmaFinite (μ.restrict S) := by
  obtain ⟨K,hK,hKS⟩ := hS
  have hm : MeasurableSet S := hKS ▸ MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hm.compl),union_inter_distrib_right,
      compl_inter_self,union_empty]
    exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
  · rw [← iUnion_union,hKS,union_compl_self]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Integrate along a unit time interval, then use translation invariance on the σ-compact support. -/
private theorem integral_orbit_derivative_zero (a : LCATopologicalLie G) {w v : G → ℂ}
    (hw : Integrable w μ) (hv : Integrable v μ) (hc : Continuous v)
    (J : Subgroup G) (hJ : IsOpen (J : Set G)) (hσ : IsSigmaCompact (J : Set G))
    (h0 : ∀ x ∉ J, v x = 0)
    (hd : ∀ x : G, HasDerivAt (fun t : ℝ ↦ w (x * a (Multiplicative.ofAdd t))) (v x) 0) :
    ∫ x, v x ∂μ = 0 := by
  let b (t : ℝ) := a (Multiplicative.ofAdd t)
  have hb : Continuous b := a.continuous.comp continuous_ofAdd
  have hmem (t : ℝ) : b t ∈ J := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range a.continuous).subset_isClopen ⟨J.isClosed_of_isOpen hJ,hJ⟩
      ⟨1,⟨1,map_one a⟩,J.one_mem⟩ (mem_range_self _)
  have htime (x : G) (t : ℝ) : HasDerivAt (fun s ↦ w (x * b s)) (v (x * b t)) t := by
    have h : HasDerivAt (fun s : ℝ ↦ w ((x * b t) * b s)) (v (x * b t)) (t - t) := sub_self t ▸ hd (x * b t)
    convert h.comp_sub_const t t using 1
    funext s
    have he : b t * b (s - t) = b s := by
      change a (Multiplicative.ofAdd t) * a (Multiplicative.ofAdd (s-t)) = _
      rw [← map_mul, ← ofAdd_add, add_sub_cancel]
    rw [mul_assoc,he]
  let k (t : ℝ) (x : G) := v (x * b t)
  have hFTC (x : G) : (∫ t in (0:ℝ)..1, k t x) = w (x * b 1) - w x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ htime x t)
      ((hc.comp (continuous_const.mul hb)).intervalIntegrable (μ := volume) 0 1)
    simpa only [k,b,ofAdd_zero,map_one,mul_one] using h
  let S : Set G := J
  let : SigmaFinite (μ.restrict S) := sigmaFinite_restrict_sigmaCompact μ hσ
  have hk0 (t : ℝ) (x : G) (hx : x ∉ S) : k t x = 0 :=
    h0 _ (fun hm ↦ hx ((J.mul_mem_cancel_right (hmem t)).mp hm))
  have hrow (t : ℝ) : (∫ x in S, k t x ∂μ) = ∫ x, v x ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hk0 t)).trans (integral_mul_right_eq_self v (b t))
  have hnorm (t : ℝ) : (∫ x in S, ‖k t x‖ ∂μ) = ∫ x, ‖v x‖ ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hk0 t x hx,norm_zero])).trans ?_
    exact integral_mul_right_eq_self (fun x ↦ ‖v x‖) (b t)
  have hkc : Continuous (Function.uncurry k) := hc.comp (continuous_snd.mul (hb.comp continuous_fst))
  let : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
  have hint : Integrable (Function.uncurry k) ((volume.restrict (uIoc (0:ℝ) 1)).prod (μ.restrict S)) := by
    refine (integrable_prod_iff hkc.aestronglyMeasurable).mpr ⟨.of_forall fun t ↦
      ((measurePreserving_mul_right μ (b t)).integrable_comp_of_integrable hv).restrict, ?_⟩
    simpa only [Function.uncurry_apply_pair,hnorm] using
      (integrable_const (μ := volume.restrict (uIoc (0:ℝ) 1)) (∫ x, ‖v x‖ ∂μ))
  have he := intervalIntegral_integral_swap hint
  simp_rw [hrow,hFTC] at he
  have hzero (x : G) (hx : x ∉ S) : w (x * b 1) - w x = 0 := by
    rw [← hFTC]
    simp only [fun t ↦ hk0 t x hx, intervalIntegral.integral_zero]
  have hw1 : Integrable (fun x ↦ w (x * b 1)) μ :=
    (measurePreserving_mul_right μ (b 1)).integrable_comp_of_integrable hw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_sub hw1 hw,
    integral_mul_right_eq_self,sub_self] at he
  simpa using he

/-- The integrated orbit derivative of a function times a conjugate character vanishes. -/
private theorem lcaFourier_generator (a : LCATopologicalLie G) (f g : SchwartzBruhat G)
    (hg : ∀ x, g x = bruhatDirectionalDeriv a f x)
    (hf₁ : Integrable (f : G → ℂ) μ) (hg₁ : Integrable (g : G → ℂ) μ) (χ : PontryaginDual G) :
    lcaFourier μ g χ = bruhatDiffSymbol (bruhatDiffGenerator a) χ * lcaFourier μ f χ := by
  let c := bruhatDiffSymbol (bruhatDiffGenerator a) χ
  let u : SchwartzBruhat G := g - c • f
  let w (x : G) := f x * star (χ x : ℂ)
  let v (x : G) := u x * star (χ x : ℂ)
  have hμ : Integrable u.val μ := hg₁.sub (hf₁.const_mul c)
  obtain ⟨J,ho,hs,h0⟩ := schwartzBruhat_supported_open u
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous u
  have hc : Continuous v := (b.continuous.congr hb).mul (continuous_subtype_val.comp χ.continuous).star
  have hdχ := hasDerivAt_bruhatDirectionalDeriv a
    ((mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth χ) 1) (1 : G)
  have hchar : HasDerivAt (fun t : ℝ ↦ (χ (a (Multiplicative.ofAdd t)) : ℂ)) c 0 := by
    change HasDerivAt _ (bruhatDirectionalDeriv a (fun x : G ↦ (χ x : ℂ)) 1) 0
    simpa only [one_mul] using hdχ
  have hd (x : G) : HasDerivAt (fun t : ℝ ↦ w (x * a (Multiplicative.ofAdd t))) (v x) 0 := by
    have hχ : HasDerivAt (fun t : ℝ ↦ star (χ (a (Multiplicative.ofAdd t)) : ℂ)) (-c) 0 := by
      have h := HasDerivAt.comp_const_sub (0:ℝ) (0:ℝ) (f := fun t : ℝ ↦ (χ (a (Multiplicative.ofAdd t)) : ℂ))
        (show HasDerivAt _ c (0 - 0) by simpa only [sub_zero] using hchar)
      convert h using 1
      funext t
      simp only [zero_sub,ofAdd_neg,map_inv,Circle.coe_inv_eq_conj,Complex.star_def]
    have hf := hasDerivAt_bruhatDirectionalDeriv a (schwartzBruhat_isBruhatSmooth f 1) x
    have h := hf.fun_mul (hχ.const_mul (star (χ x : ℂ)))
    convert h using 1
    · funext t
      simp only [w,map_mul,Circle.coe_mul,star_mul]
      ring
    · change (g x - c * f x) * star (χ x : ℂ) = _
      simp only [hg,ofAdd_zero,map_one,mul_one,Circle.coe_one,star_one]
      ring
  have hz := integral_orbit_derivative_zero μ a (w := w) (v := v) (integrable_fourierIntegrand μ hf₁ χ)
    (integrable_fourierIntegrand μ hμ χ) hc J ho hs (fun x hx ↦ by simp [v,h0 x hx]) hd
  have hi (x : G) : v x = g x * star (χ x : ℂ) - c * (f x * star (χ x : ℂ)) := by
    change (g x - c * f x) * star (χ x : ℂ) = _
    ring
  simp_rw [hi] at hz
  rw [integral_sub (integrable_fourierIntegrand μ hg₁ χ) ((integrable_fourierIntegrand μ hf₁ χ).const_mul c),
    integral_const_mul] at hz
  exact sub_eq_zero.mp hz

/-- A Fourier multiplier identity on generators extends to the algebra they generate. -/
private theorem symbol_action_adjoin {V E ι : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup E] [Module ℂ E] (i : E →ₗ[ℂ] V) (A : E →ₗ[ℂ] (ι → ℂ)) (ch : ι → V)
    (s : Set (Module.End ℂ V))
    (hgen : ∀ L ∈ s, ∃ c : ι → ℂ, (∀ χ, L (ch χ) = c χ • ch χ) ∧
      ∀ z, ∃ y, i y = L (i z) ∧ ∀ χ, A y χ = c χ * A z χ)
    {L : Module.End ℂ V} (hL : L ∈ Algebra.adjoin ℂ s) :
    ∃ c : ι → ℂ, (∀ χ, L (ch χ) = c χ • ch χ) ∧
      ∀ z, ∃ y, i y = L (i z) ∧ ∀ χ, A y χ = c χ * A z χ := by
  apply Algebra.adjoin_induction (p := fun M _ ↦ ∃ c : ι → ℂ,
    (∀ χ, M (ch χ) = c χ • ch χ) ∧ ∀ z, ∃ y, i y = M (i z) ∧ ∀ χ, A y χ = c χ * A z χ)
    hgen _ _ _ hL
  · intro c
    refine ⟨fun _ ↦ c, fun χ ↦ rfl, fun z ↦ ⟨c • z,i.map_smul c z, fun χ ↦ ?_⟩⟩
    rw [A.map_smul]
    rfl
  · rintro L M _ _ ⟨c,hc,lc⟩ ⟨d,hd,ld⟩
    refine ⟨c+d,fun χ ↦ ?_, fun z ↦ ?_⟩
    · change L (ch χ) + M (ch χ) = (c χ + d χ) • ch χ
      rw [hc,hd,add_smul]
    · obtain ⟨u,hu,fu⟩ := lc z
      obtain ⟨v,hv,fv⟩ := ld z
      refine ⟨u+v, (i.map_add _ _).trans (congrArg₂ (·+·) hu hv), fun χ ↦ ?_⟩
      rw [A.map_add]
      change A u χ + A v χ = (c χ + d χ) * A z χ
      rw [fu,fv,add_mul]
  · rintro L M _ _ ⟨c,hc,lc⟩ ⟨d,hd,ld⟩
    refine ⟨c*d, fun χ ↦ ?_, fun z ↦ ?_⟩
    · change L (M (ch χ)) = (c χ * d χ) • ch χ
      rw [hd,map_smul,hc,smul_smul,mul_comm]
    · obtain ⟨u,hu,fu⟩ := ld z
      obtain ⟨v,hv,fv⟩ := lc u
      refine ⟨v,hv.trans (congrArg L hu), fun χ ↦ ?_⟩
      change A v χ = (c χ * d χ) * A z χ
      rw [fv,fu,mul_assoc]

private def smoothInclusion : SchwartzBruhat G →ₗ[ℂ] bruhatSmoothSubmodule (G := G) :=
    { toFun := fun z ↦ ⟨z.val,(mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth z)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private def smoothCharacter (χ : PontryaginDual G) : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩

private theorem generator_character (a : LCATopologicalLie G) (χ : PontryaginDual G) :
    bruhatFirstOrder a (smoothCharacter χ) = bruhatDiffSymbol (bruhatDiffGenerator a) χ • smoothCharacter χ := by
  apply Subtype.ext
  funext x
  change bruhatDirectionalDeriv a (fun y : G ↦ (χ y : ℂ)) x =
    bruhatDirectionalDeriv a (fun y : G ↦ (χ y : ℂ)) 1 * (χ x : ℂ)
  simp only [bruhatDirectionalDeriv,one_mul,map_mul,Circle.coe_mul,deriv_const_mul_field]
  exact mul_comm _ _

private theorem generator_schwartz_lift (B : SchwartzBruhat G →ₗ[ℂ] (PontryaginDual G → ℂ))
    (hB : ∀ z : SchwartzBruhat G, Integrable z.val μ ∧ ∀ χ, B z χ = lcaFourier μ z χ)
    (a : LCATopologicalLie G) (z : SchwartzBruhat G) :
    ∃ y : SchwartzBruhat G, smoothInclusion (G := G) y = bruhatFirstOrder a (smoothInclusion (G := G) z) ∧
      ∀ χ, B y χ = bruhatDiffSymbol (bruhatDiffGenerator a) χ * B z χ := by
  let L := (bruhatFirstOrder_schwartz (G := G) a).choose
  have hL := (bruhatFirstOrder_schwartz (G := G) a).choose_spec
  refine ⟨L z, ?_, fun χ ↦ ?_⟩
  · apply Subtype.ext
    exact funext (hL z)
  exact ((hB (L z)).2 χ).trans ((lcaFourier_generator μ a z (L z) (hL z)
    (hB z).1 (hB (L z)).1 χ).trans (congrArg (_ * ·) ((hB z).2 χ).symm))

end FourierDifferentiation

section AveragingAndFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

variable (K : Subgroup G)

/-- Use the whole compactly generated group as the open subgroup of the structural pair. -/
private def fullBruhatStage {K : Subgroup G} (hG : IsCompactlyGeneratedGroup G) (hk : IsBruhatGoodSubgroup K) :
    BruhatStructuralPair G :=
  ⟨(⊤, OrderDual.toDual K), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv
      (show G ≃ₜ* (⊤ : Subgroup G) from
        ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩) hG, hk, le_top⟩

omit hTop hT2 hLC in
private theorem fullBruhatStage_quotientEquiv {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    {K : Subgroup G} (hG : IsCompactlyGeneratedGroup G) (hk : IsBruhatGoodSubgroup K)
    (p : G →* Q) (hp : IsOpenQuotientMap p) (hker : p.ker = K) :
    ∃ w : (fullBruhatStage hG hk).quotient ≃ₜ* Q,
      ∀ x : G, w (QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩) = p x := by
  let i : (⊤ : Subgroup G) ≃ₜ* G := ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let t := p.comp (⊤ : Subgroup G).subtype
  have ht : IsOpenQuotientMap t := hp.comp i.toHomeomorph.isOpenQuotientMap
  have hker' : K.comap (⊤ : Subgroup G).subtype = t.ker := by rw [← hker]; rfl
  let w := (QuotientGroup.quotientMulEquivOfEq hker').trans
    (QuotientGroup.quotientKerEquivOfSurjective t ht.surjective)
  let v := w.toContinuousMulEquiv fun s ↦ by
    rw [← (QuotientGroup.isQuotientMap_mk _).isOpen_preimage]
    exact ht.isQuotientMap.isOpen_preimage
  exact ⟨v, fun _ ↦ rfl⟩

private theorem schwartzBruhatStage_surjective_of_maximal (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient)
    (hmax : ∀ b, b ≤ a) : Function.Surjective (schwartzBruhatStageInclusion a d) := by
  intro f
  exact ((mem_schwartzBruhatSubmodule_iff f.val).mp f.property).elim fun b hb ↦ hb.elim fun e' he ↦
    he.elim fun s hs ↦ (schwartzBruhatStage_transition (hmax b) e' d).elim
      fun k hk ↦ ⟨k s, Subtype.ext ((hk.1 s).trans hs)⟩

omit hTop hT2 hLC in
private theorem continuousLinearEquiv_of_surjective_retraction {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (j : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hr : Function.LeftInverse R j) (hs : Function.Surjective j) :
    ∃ I : E ≃L[ℂ] F, ∀ x, I x = j x := by
  let l := LinearEquiv.ofBijective j.toLinearMap ⟨hr.injective,hs⟩
  refine ⟨{l with continuous_toFun := j.continuous, continuous_invFun := ?_}, fun _ ↦ rfl⟩
  exact R.continuous.congr fun f ↦ by
    obtain ⟨s,rfl⟩ := hs f
    exact (hr s).trans (l.symm_apply_apply s).symm

/-- On an elementary group the largest structural stage has zero kernel and realizes the whole space. -/
private theorem elementarySchwartz_equiv_schwartzBruhat (e : ElementaryLCAPresentation G) :
    ∃ I : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhat G,
      ∀ f (x : G), I f x = f (e.equiv x).toAdd := by
  classical
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  have hG := hE.1
  have hEu := hE.2
  let hk := (isBruhatGoodSubgroup_bot_iff (G := G)).mpr hEu
  let a := fullBruhatStage hG hk
  have hW := fullBruhatStage_quotientEquiv hG hk (MonoidHom.id G) IsOpenQuotientMap.id (by simp)
  let w := hW.choose
  have hw := hW.choose_spec
  let d : ElementaryLCAPresentation a.quotient := {e with equiv := w.trans e.equiv}
  let j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G :=
    ⟨schwartzBruhatStageInclusion a d, (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _
      fun q ↦ q.property a d⟩
  have hmax (b : BruhatStructuralPair G) : b ≤ a := ⟨le_top, (bot_le : (⊥ : Subgroup G) ≤ OrderDual.ofDual b.val.2)⟩
  have hret := schwartzBruhatStage_average_retraction a d
  have hI := continuousLinearEquiv_of_surjective_retraction j hret.choose hret.choose_spec.1 (schwartzBruhatStage_surjective_of_maximal a d hmax)
  refine ⟨hI.choose, fun f x ↦ ?_⟩
  rw [hI.choose_spec]
  change schwartzBruhatStageRealization a d f x = _
  have hx : x ∈ a.val.1 := Subgroup.mem_top x
  rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
  change f (e.equiv (w (QuotientGroup.mk _))).toAdd = _
  exact congrArg (fun y : G ↦ f (e.equiv y).toAdd) (hw x)

end AveragingAndFourier

section CoordinateCharacterization

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

omit hT2 in
private theorem exists_dual_weight_direction (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (hb : ∀ x χ, b x χ = χ x) (ρ : G →ₜ* Multiplicative ℝ) :
    ∃ a : LCATopologicalLie (PontryaginDual G), ∀ x,
      bruhatDiffSymbol (bruhatDiffGenerator a) (b x) = 2 * ↑Real.pi * Complex.I * ((ρ x).toAdd : ℂ) := by
  obtain ⟨d,hd⟩ := exists_realPontryaginDualEquiv
  let a := (PontryaginDual.map ρ).comp (d : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))
  refine ⟨a,fun x ↦ bruhatDiffSymbol_generator a (b x) _ fun t ↦ ?_⟩
  rw [hb]
  change Real.fourierChar ((ρ x).toAdd*t) = d (Multiplicative.ofAdd t) (ρ x)
  rw [mul_comm]
  exact (hd t (ρ x).toAdd).symm

/-- Products of real-valued homomorphisms are symbols of suitably normalized words on the dual. -/
private theorem bruhat_realHom_weights (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (hb : ∀ x χ, b x χ = χ x) (L : List (G →ₜ* Multiplicative ℝ)) :
    ∃ E : bruhatDiffAlgebra (PontryaginDual G), ∀ x,
      bruhatDiffSymbol E (b x) = (L.map (fun ρ ↦ ((ρ x).toAdd : ℂ))).prod := by
  choose a ha using exists_dual_weight_direction b hb
  let z : ℂ := 2 * ↑Real.pi * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨(z^L.length)⁻¹ • bruhatDiffWord (L.map a), fun x ↦ ?_⟩
  change (z^L.length)⁻¹ * bruhatDiffSymbol (bruhatDiffWord (L.map a)) (b x) = _
  rw [bruhatDiffSymbol_word]
  have hprod : ((L.map a).map (fun c ↦ bruhatDiffSymbol (bruhatDiffGenerator c) (b x))).prod =
      z^L.length * (L.map (fun ρ ↦ ((ρ x).toAdd : ℂ))).prod := by
    induction L with
    | nil => simp
    | cons ρ l ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ha,ih]
      change z * _ * _ = _
      ring
  rw [hprod,inv_mul_cancel_left₀ (pow_ne_zero _ hz)]

/-- Bruhat smoothness descends to ordinary smoothness on every fiber of the full elementary stage. -/
private theorem smooth_elementary_cover (e : ElementaryLCAPresentation G) (f : bruhatSmoothSubmodule (G := G))
    (z : Fin e.latticeRank → ℤ) (d : e.finiteFactor) :
    ContDiff ℝ ∞ (fun u ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)))) := by
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  let hbot := (isBruhatGoodSubgroup_bot_iff (G := G)).mpr hE.2
  let a := fullBruhatStage hE.1 hbot
  have hW := fullBruhatStage_quotientEquiv hE.1 hbot (MonoidHom.id G) IsOpenQuotientMap.id (by simp)
  let w := hW.choose
  let e' : ElementaryLCAPresentation a.quotient := {e with equiv := w.trans e.equiv}
  apply contDiff_infty.mpr
  intro n
  obtain ⟨k,hk,_,hdesc⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property n
  have H := bruhatContDiff_descend_of_le hk hdesc a (show OrderDual.ofDual a.val.2 ≤ k from bot_le)
  let f₀ := H.choose
  have h (x : G) : f₀ (w.symm x) = f.val x := by
    let t : a.val.1 := ⟨x,Subgroup.mem_top _⟩
    have hw : w (QuotientGroup.mk t) = x := hW.choose_spec x
    exact (congrArg f₀ (w.symm_apply_eq.mpr hw.symm)).trans (H.choose_spec.1 t)
  have hcd := H.choose_spec.2 e' z d
  have heq : (fun u ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)))) =
      fun u ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d))) := funext fun u ↦ h _
  exact heq ▸ hcd

private theorem elementaryCover_add {m n r : ℕ} {F : Type*} [AddCommGroup F]
    (u v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a a' : Fin r → ℤ) (b b' : F) :
    elementaryCover u a b + elementaryCover v a' b' = elementaryCover (u+v) (a+a') (b+b') := by
  exact Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_add _ _ _).symm) rfl)

/-- A vector of the real and torus cover defines a one-parameter subgroup realizing its directional derivative. -/
private theorem exists_direction_cover (e : ElementaryLCAPresentation G)
    (v : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
    ∃ a : LCATopologicalLie G, ∀ (f : bruhatSmoothSubmodule (G := G)) u z d,
      (bruhatFirstOrder a f).val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d))) =
        fderiv ℝ (fun w ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover w z d)))) u v := by
  let V := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let c := (elementaryCoverZeroHom (r := e.latticeRank) (F := e.finiteFactor)).comp L.toLinearMap.toAddMonoidHom
  let a : LCATopologicalLie G := (e.equiv.symm : _ →ₜ* _).comp ⟨AddMonoidHom.toMultiplicative c,
    elementaryCoverZeroHom_continuous_isOpenMap.1.comp L.continuous⟩
  refine ⟨a,fun f u z d ↦ ?_⟩
  let g (w : V) := f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover w z d)))
  have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have h := ((smooth_elementary_cover e f z d).differentiable (by simp) u).hasFDerivAt
  have horb (t : ℝ) : e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)) * a (Multiplicative.ofAdd t) =
      e.equiv.symm (Multiplicative.ofAdd (elementaryCover (u+t • v) z d)) := by
    change e.equiv.symm _ * e.equiv.symm (Multiplicative.ofAdd (elementaryCover (t • v) 0 0)) = _
    rw [← map_mul,← ofAdd_add,elementaryCover_add,add_zero,add_zero]
  change deriv (fun t : ℝ ↦ f.val (_ * a (Multiplicative.ofAdd t))) 0 = _
  simp only [horb]
  exact (h.comp_hasDerivAt_of_eq 0 hLine (by simp)).deriv

/-- Appending a direction differentiates the original function before evaluating the preceding mixed partial. -/
private theorem iteratedFDeriv_append_singleton {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (u v : V) (D : List V) :
    iteratedFDeriv ℝ (D ++ [v]).length f u (D ++ [v]).get =
      iteratedFDeriv ℝ D.length (fun y ↦ fderiv ℝ f y v) u D.get := by
  let eval (s : Σ k, Fin k → V) := iteratedFDeriv ℝ s.1 f u s.2
  have hEval := congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨D.length + 1, Fin.snoc D.get v⟩)
  change iteratedFDeriv ℝ (List.ofFn (Fin.snoc D.get v)).length f u (List.ofFn (Fin.snoc D.get v)).get =
    iteratedFDeriv ℝ (D.length + 1) f u (Fin.snoc D.get v) at hEval
  have hList : List.ofFn (Fin.snoc D.get v) = D ++ [v] := by
    rw [List.ofFn_succ',Fin.snoc_last,List.concat_eq_append]
    simp only [Fin.snoc_castSucc,List.ofFn_get]
  rw [hList] at hEval
  rw [hEval,iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last]
  change _ = iteratedFDeriv ℝ D.length ((ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ f) u D.get
  rw [(ContinuousLinearMap.apply ℝ ℂ v).iteratedFDeriv_comp_left
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)]
  rfl

/-- Products of the directional generators realize all ordered iterated derivatives on the cover. -/
private theorem exists_diff_cover_word (e : ElementaryLCAPresentation G)
    (L : List (EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim))) :
    ∃ D : bruhatDiffAlgebra G, ∀ (f : bruhatSmoothSubmodule (G := G)) u z d,
      (D.val f).val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d))) =
        iteratedFDeriv ℝ L.length (fun v ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover v z d)))) u L.get := by
  induction L using List.reverseRecOn with
  | nil =>
    exact ⟨1,fun _ _ _ _ ↦ rfl⟩
  | append_singleton l v ih =>
    obtain ⟨D,hD⟩ := ih
    obtain ⟨a,ha⟩ := exists_direction_cover e v
    refine ⟨D * bruhatDiffGenerator a,fun f u z d ↦ ?_⟩
    change (D.val (bruhatFirstOrder a f)).val _ = _
    rw [hD,iteratedFDeriv_append_singleton (smooth_elementary_cover e f z d)]
    exact congrArg (fun w ↦ iteratedFDeriv ℝ l.length w u l.get) (funext fun x ↦ ha f x z d)

private def coordinateRealHom (e : ElementaryLCAPresentation G) (i : Fin e.realDim) : G →ₜ* Multiplicative ℝ :=
  let l := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin e.realDim ↦ ℝ) i).toLinearMap.toAddMonoidHom
  let a := l.comp (AddMonoidHom.fst _ _)
  (show Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) →ₜ* Multiplicative ℝ from
    ⟨AddMonoidHom.toMultiplicative a, (PiLp.continuous_apply 2 _ i).comp continuous_fst⟩).comp e.equiv

private def coordinateLatticeHom (e : ElementaryLCAPresentation G) (i : Fin e.latticeRank) : G →ₜ* Multiplicative ℝ :=
  let a := (Int.castAddHom ℝ).comp ((Pi.evalAddMonoidHom _ i).comp ((AddMonoidHom.fst _ _).comp
    ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))))
  (show Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) →ₜ* Multiplicative ℝ from
    ⟨AddMonoidHom.toMultiplicative a, by
      change Continuous (fun y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor ↦ (y.2.2.1 i : ℝ))
      exact (continuous_of_discreteTopology (f := fun z : Fin e.latticeRank → ℤ ↦ (z i : ℝ))).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))⟩).comp e.equiv

/-- Every real and lattice coordinate monomial is the pullback of a symbol along the given biduality map. -/
private theorem exists_elementary_weight (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (α : Fin e.realDim → ℕ) (δ : Fin e.latticeRank → ℕ) :
    ∃ E : bruhatDiffAlgebra (PontryaginDual G), ∀ y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor,
      bruhatDiffSymbol E (b (e.equiv.symm (Multiplicative.ofAdd y))) =
        (∏ i, (y.1 i : ℂ)^α i) * (∏ j, (y.2.2.1 j : ℂ)^δ j) := by
  let powers {n : ℕ} (β : Fin n → ℕ) (ρ : Fin n → G →ₜ* Multiplicative ℝ) :=
    (List.ofFn fun i ↦ List.replicate (β i) (ρ i)).flatten
  have hp {n : ℕ} (β : Fin n → ℕ) (ρ : Fin n → G →ₜ* Multiplicative ℝ) (x : G) :
      ((powers β ρ).map (fun c ↦ ((c x).toAdd : ℂ))).prod = ∏ i, ((ρ i x).toAdd : ℂ)^β i := by
    simp [powers,List.map_flatten,List.prod_flatten,List.map_ofFn,Function.comp_def,List.prod_replicate,List.prod_ofFn]
  obtain ⟨E,hE⟩ := bruhat_realHom_weights b hb (powers α (coordinateRealHom e) ++ powers δ (coordinateLatticeHom e))
  refine ⟨E,fun y ↦ ?_⟩
  rw [hE,List.map_append,List.prod_append,hp,hp]
  have hr (i : Fin e.realDim) : (coordinateRealHom e i (e.equiv.symm (.ofAdd y))).toAdd = y.1 i := by
    change (e.equiv (e.equiv.symm (.ofAdd y))).toAdd.1 i = _
    rw [e.equiv.apply_symm_apply]
    rfl
  have hz (i : Fin e.latticeRank) : (coordinateLatticeHom e i (e.equiv.symm (.ofAdd y))).toAdd = (y.2.2.1 i : ℝ) := by
    change ((e.equiv (e.equiv.symm (.ofAdd y))).toAdd.2.2.1 i : ℝ) = _
    rw [e.equiv.apply_symm_apply]
    rfl
  simp only [hr,hz,Complex.ofReal_intCast]

/-- Bounded symbol-weighted derivatives bound each defining seminorm on the full elementary stage. -/
private theorem elementarySchwartz_of_symbols (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (f : bruhatSmoothSubmodule (G := G))
    (hf : ∀ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
      ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * (D.val f).val x‖ ≤ C) :
    f.val ∈ schwartzBruhatSubmodule G := by
  let g (y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) := f.val (e.equiv.symm (.ofAdd y))
  have hm : g ∈ elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := by
    refine ⟨smooth_elementary_cover e f,fun i ↦ ?_⟩
    let dirs := (List.ofFn fun j ↦ List.replicate (i.2.1 j)
      ((EuclideanSpace.single j (1:ℝ), 0) : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim))).flatten ++
      (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
    obtain ⟨D,hD⟩ := exists_diff_cover_word e dirs
    obtain ⟨E,hE⟩ := exists_elementary_weight e b hb i.1 i.2.2.2
    obtain ⟨C,hC⟩ := hf D E
    refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup_le fun u ↦ iSup_le fun z ↦ iSup_le fun d ↦ ?_) ENNReal.ofReal_lt_top
    let y := elementaryCover u z d
    have hd : (D.val f).val (e.equiv.symm (.ofAdd y)) = elementaryPartial g i.2.1 i.2.2.1 u z d := hD f u z d
    have h := hC (e.equiv.symm (.ofAdd y))
    rw [hE,hd] at h
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal h
  obtain ⟨I,hI⟩ := elementarySchwartz_equiv_schwartzBruhat e
  let s : SchwartzBruhatStage e := ⟨g,hm⟩
  have he : (I s).val = f.val := funext fun x ↦ (hI s x).trans (congrArg f.val (e.equiv.symm_apply_apply x))
  exact he ▸ (I s).property

/-- A continuous real-valued homomorphism kills the compact factors and is linear in the real and lattice coordinates. -/
private theorem elementaryRealHom_polynomial {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (h : ElementaryLieGroup m n r F →+ ℝ) (hh : Continuous h) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ, ∀ y : ElementaryLieGroup m n r F,
      MvPolynomial.eval (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p = (h y : ℂ) := by
  classical
  let V := EuclideanSpace ℝ (Fin m)
  let Z := Fin r → ℤ
  let K := (Fin n → AddCircle (1 : ℝ)) × F
  let G := ElementaryLieGroup m n r F
  let J := Fin m ⊕ Fin r
  let eR : V →+ G :=
    ⟨⟨fun x ↦ (x, 0, 0, 0), rfl⟩, fun _ _ ↦
      Prod.ext rfl (Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (zero_add _).symm))⟩
  let eZ : Z →+ G :=
    ⟨⟨fun a ↦ (0, 0, a, 0), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (Prod.ext rfl (zero_add _).symm))⟩
  let eK : K →+ G :=
    ⟨⟨fun z ↦ (0, z.1, 0, z.2), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl))⟩
  let e (j : J) : G := Sum.elim
    (fun i ↦ eR (EuclideanSpace.single i 1)) (fun i ↦ eZ (Pi.single i 1)) j
  let coord (j : J) : G →+ ℝ := Sum.elim
    (fun i : Fin m ↦
      ⟨⟨fun g : G ↦ g.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r ↦
      (Int.castAddHom ℝ).comp ⟨⟨fun g : G ↦ g.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hlinear (h : G →+ ℝ) (hh : Continuous h) (g : G) :
      h g = ∑ j, coord j g * h (e j) := by
    let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
    let hK := h.comp eK
    have hKcont : Continuous hK :=
      hh.comp (continuous_const.prodMk (continuous_fst.prodMk
        (continuous_const.prodMk continuous_snd)))
    have hvanish (z : K) : hK z = 0 := by
      obtain ⟨M, hM⟩ := (isCompact_range hKcont.norm).bddAbove
      by_contra hz
      obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖hK z‖)
      have hle := hM (Set.mem_range_self (N • z))
      change ‖hK (N • z)‖ ≤ M at hle
      rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hle
      exact (not_lt_of_ge hle) ((div_lt_iff₀ (norm_pos_iff.mpr hz)).mp hN)
    let hR := (h.comp eR).toRealLinearMap (hh.comp (continuous_id.prodMk continuous_const))
    let basisR := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    let basisZ := Pi.basisFun ℤ (Fin r)
    have hr (x : V) : h (eR x) = ∑ i, x i * h (eR (EuclideanSpace.single i 1)) := by
      have he := congrArg hR (basisR.sum_repr x)
      simpa [hR, basisR, smul_eq_mul] using he.symm
    have hz (a : Z) : h (eZ a) = ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1)) := by
      have he := congrArg (h.comp eZ) (basisZ.sum_repr a)
      rw [map_sum] at he
      simp_rw [map_zsmul, zsmul_eq_mul] at he
      simpa [basisZ] using he.symm
    rcases g with ⟨x, z, a, b⟩
    have hdecomp : (x, z, a, b) = eR x + eZ a + eK (z, b) := by
      change (x, z, a, b) = ((x + 0) + 0, (0 + 0) + z, (0 + a) + 0, (0 + 0) + b)
      simp
    have hKzero : h (eK (z, b)) = 0 := hvanish (z, b)
    rw [Fintype.sum_sum_type]
    change h (x, z, a, b) =
      (∑ i, x i * h (eR (EuclideanSpace.single i 1))) +
        ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1))
    rw [hdecomp, map_add, map_add, hKzero, add_zero, hr, hz]
  refine ⟨∑ j, MvPolynomial.X j * MvPolynomial.C (h (e j) : ℂ),fun y ↦ ?_⟩
  rw [hlinear h hh y]
  simp only [map_sum,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C,Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun j _ ↦ by
    cases j with
    | inl i => rfl
    | inr i => simp [coord]

omit hT2 in
private theorem bruhatSymbol_generator_polynomial (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (a : LCATopologicalLie (PontryaginDual G)) :
    ∃ p : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ, ∀ x,
      let y := (e.equiv x).toAdd
      bruhatDiffSymbol (bruhatDiffGenerator a) (b x) =
        MvPolynomial.eval (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p := by
  obtain ⟨σ,_,_,hσ⟩ := bruhatDiffDegreeOne_frequency (G := PontryaginDual G)
  let D : bruhatDiffDegreeOneReal (G := PontryaginDual G) :=
    ⟨bruhatFirstOrder a,Submodule.subset_span ⟨a,rfl⟩⟩
  let L := (σ D).comp ((b : G →ₜ* PontryaginDual (PontryaginDual G)).comp (e.equiv.symm : Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) →ₜ* G))
  let h := AddMonoidHom.toMultiplicative.symm L.toMonoidHom
  obtain ⟨p,hp⟩ := elementaryRealHom_polynomial (F := e.finiteFactor) h L.continuous
  let z : ℂ := 2 * ↑Real.pi * Complex.I
  refine ⟨MvPolynomial.C z * p,fun x ↦ ?_⟩
  dsimp only
  rw [map_mul (MvPolynomial.eval _),MvPolynomial.eval_C,hp]
  have he : h (e.equiv x).toAdd = (σ D (b x)).toAdd := by
    change (σ D (b (e.equiv.symm (e.equiv x)))).toAdd = _
    rw [e.equiv.symm_apply_apply]
  rw [he]
  exact bruhatDiffSymbol_generator a (b x) _ (hσ a D rfl (b x))

/-- The finite word presentation identifies a symbol with a polynomial in the noncompact coordinates. -/
private theorem bruhatSymbol_polynomial (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (E : bruhatDiffAlgebra (PontryaginDual G)) :
    ∃ p : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ, ∀ x,
      let y := (e.equiv x).toAdd
      bruhatDiffSymbol E (b x) = MvPolynomial.eval
        (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p := by
  classical
  choose p hp using bruhatSymbol_generator_polynomial e b
  obtain ⟨c,hc⟩ := bruhatDiff_exists_presentation E
  let word (w : List (LCATopologicalLie (PontryaginDual G))) := (w.map p).prod
  refine ⟨c.sum (fun w z ↦ MvPolynomial.C z * word w),fun x ↦ ?_⟩
  let ev : bruhatDiffAlgebra (PontryaginDual G) →ₗ[ℂ] ℂ :=
    (LinearMap.proj 1).comp ((bruhatSmoothSubmodule (G := PontryaginDual G)).subtype.comp
      ((LinearMap.applyₗ (smoothCharacter (b x))).comp (bruhatDiffAlgebra (PontryaginDual G)).val.toLinearMap))
  change ev E = _
  rw [← hc]
  simp only [Finsupp.sum,map_sum,map_mul,map_smul,MvPolynomial.eval_C,smul_eq_mul]
  refine Finset.sum_congr rfl fun w _ ↦ congrArg (c w * ·) ?_
  change bruhatDiffSymbol (bruhatDiffWord w) (b x) = _
  rw [bruhatDiffSymbol_word]
  simp only [word,map_list_prod,List.map_map,Function.comp_def,hp]

/-- The algebra generated by the one-parameter derivatives preserves the Schwartz submodule. -/
private theorem bruhatDiff_preserves_schwartz (D : bruhatDiffAlgebra G) :
    ∀ f : bruhatSmoothSubmodule (G := G), f.val ∈ schwartzBruhatSubmodule G →
      (D.val f).val ∈ schwartzBruhatSubmodule G := by
  refine Algebra.adjoin_induction (s := range (bruhatFirstOrder (G := G)))
    (p := fun A _ ↦ ∀ f : bruhatSmoothSubmodule (G := G), f.val ∈ schwartzBruhatSubmodule G →
      (A f).val ∈ schwartzBruhatSubmodule G) ?_ ?_ ?_ ?_ D.property
  · rintro _ ⟨a,rfl⟩ f hf
    let s : SchwartzBruhat G := ⟨f.val,hf⟩
    obtain ⟨A,hA⟩ := bruhatFirstOrder_schwartz (G := G) a
    have he : (A s).val = (bruhatFirstOrder a f).val := funext (hA s)
    exact he ▸ (A s).property
  · intro c f hf
    exact (schwartzBruhatSubmodule G).smul_mem c hf
  · intro A B _ _ hA hB f hf
    exact (schwartzBruhatSubmodule G).add_mem (hA f hf) (hB f hf)
  · intro A B _ _ hA hB f hf
    exact hA (B f) (hB f hf)

private theorem polynomial_weight_bounded {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (f : ElementarySchwartz m n r F) :
    ∃ C : ℝ, ∀ y : ElementaryLieGroup m n r F, ‖MvPolynomial.eval
      (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p * f y‖ ≤ C := by
  obtain ⟨q,_,hq⟩ := elementarySchwartz_polynomial_weight_continuous_seminorm (F := F) p 0 0
  refine ⟨q f,fun y ↦ ?_⟩
  obtain ⟨w,hw⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  rw [norm_mul]
  apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg q f)).mp
  rw [hq]
  refine le_iSup_of_le (y.1,w) (le_iSup_of_le y.2.2.1 (le_iSup_of_le y.2.2.2 ?_))
  rw [elementaryPartial_zero, hw]

/-- The polynomial seminorms bound the symbol times a Schwartz function on an elementary group. -/
private theorem bruhatSymbol_weight_bounded (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (E : bruhatDiffAlgebra (PontryaginDual G))
    (g : SchwartzBruhat G) :
    Continuous (fun x ↦ bruhatDiffSymbol E (b x) * g x) ∧
      ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * g x‖ ≤ C := by
  obtain ⟨p,hp⟩ := bruhatSymbol_polynomial e b E
  let ψ (x : G) := (e.equiv x).toAdd
  let coord (y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))
  have hc : Continuous coord := by
    apply continuous_pi
    intro j
    cases j with
    | inl i => exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ i).comp continuous_fst)
    | inr i =>
      exact (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ℂ))).comp
        ((continuous_apply i).comp continuous_snd.snd.fst)
  have hψ : Continuous ψ := continuous_toAdd.comp e.equiv.continuous
  obtain ⟨u,hu⟩ := schwartzBruhat_boundedContinuous (G := G) g
  refine ⟨(((MvPolynomial.continuous_eval p).comp (hc.comp hψ)).mul u.continuous).congr
    (fun x ↦ congrArg₂ (· * ·) (hp x).symm (hu x)),?_⟩
  obtain ⟨I,hI⟩ := elementarySchwartz_equiv_schwartzBruhat e
  let s := I.symm g
  obtain ⟨C,hC⟩ := polynomial_weight_bounded p s
  refine ⟨C,fun x ↦ ?_⟩
  have hs : s (ψ x) = g x := (hI s x).symm.trans (congrArg (fun w : SchwartzBruhat G ↦ w x) (I.apply_symm_apply g))
  exact (congrArg norm (congrArg₂ (· * ·) (hp x) hs.symm)).le.trans (hC (ψ x))

include hTop hT2 hLC in
/-- Paper: Lemma D.1.6.16, p. 770. On an elementary group a smooth function
is Schwartz exactly when each symbol times each differentiated function is
continuous and globally bounded. The dual symbols are evaluated through biduality. -/
theorem mem_schwartzBruhat_iff_bruhatDiff_bounded (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (f : bruhatSmoothSubmodule (G := G)) :
    (f : G → ℂ) ∈ schwartzBruhatSubmodule G ↔
      ∀ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
        Continuous (fun x ↦ bruhatDiffSymbol E (b x) * (D.val f).val x) ∧
        ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * (D.val f).val x‖ ≤ C := by
  constructor
  · intro hf D E
    exact bruhatSymbol_weight_bounded e b E ⟨(D.val f).val, bruhatDiff_preserves_schwartz D f hf⟩
  · intro h
    exact elementarySchwartz_of_symbols e b hb f (fun D E ↦ (h D E).2)

end CoordinateCharacterization

section SchwartzIntegrability

/-- The product measurable structure on an elementary group agrees with its Borel
structure. -/
private theorem elementaryLieGroup_borelSpace {m n r : ℕ} {Fk : Type*}
    [TopologicalSpace Fk] [MeasurableSpace Fk] [BorelSpace Fk] :
    BorelSpace (ElementaryLieGroup m n r Fk) := by
  let : BorelSpace ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := inferInstance
  exact inferInstanceAs (BorelSpace (EuclideanSpace ℝ (Fin m) ×
    (Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk))

/-- Rapid decay in the real and lattice directions makes an elementary Schwartz function
integrable for any Haar measure on its elementary group. -/
private theorem elementarySchwartz_integrable {m n r : ℕ} {Fk : Type*} [AddCommGroup Fk]
    [TopologicalSpace Fk] [DiscreteTopology Fk] [Finite Fk] [MeasurableSpace Fk] [BorelSpace Fk]
    (f : ElementarySchwartz m n r Fk) (μ : Measure (ElementaryLieGroup m n r Fk))
    [μ.IsAddHaarMeasure] : Integrable f μ := by
  let : (Measure.count : Measure ℤ).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : (Measure.count : Measure Fk).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : MeasurableAdd ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := inferInstance
  let : MeasurableAdd ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) :=
    ContinuousAdd.measurableAdd
  let νL : Measure ((Fin r → ℤ) × Fk) :=
    (Measure.pi fun _ : Fin r ↦ (Measure.count : Measure ℤ)).prod Measure.count
  let : νL.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SFinite νL := by dsimp [νL]; infer_instance
  let νT : Measure ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := volume.prod νL
  let : νT.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SFinite νT := by dsimp [νT, νL]; infer_instance
  let ν : Measure (ElementaryLieGroup m n r Fk) := volume.prod νT
  let : BorelSpace (ElementaryLieGroup m n r Fk) := elementaryLieGroup_borelSpace
  let : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  apply Integrable.smul_measure_nnreal
  let A (x : EuclideanSpace ℝ (Fin m)) := (1 + ‖x‖ ^ 2) ^ (m + 1)
  let B (k : ℤ) := 1 + (k : ℝ) ^ 2
  have hA : Integrable (fun x ↦ (A x)⁻¹) volume := by
    have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℝ) < 2 * (m + 1 : ℕ) := by
      simp
      linarith [Nat.cast_nonneg (α := ℝ) m]
    convert integrable_rpow_neg_one_add_norm_sq (μ := volume) hdim using 1
    funext x
    rw [show -(2 * ((m + 1 : ℕ) : ℝ)) / 2 = -((m + 1 : ℕ) : ℝ) by ring,
      Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hB : Integrable (fun k ↦ (B k)⁻¹) Measure.count := by
    rw [integrable_count_iff]
    have hs := Real.summable_one_div_int_pow.mpr (show 1 < 2 by decide)
    apply hs.of_norm_bounded_eventually
    filter_upwards [show ∀ᶠ k : ℤ in cofinite, k ≠ 0 from (finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
    have hpos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)
    simp only [B, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : 0 < 1 + (k : ℝ) ^ 2), one_div]
    exact inv_anti₀ hpos (by linarith)
  let D (w : ElementaryLieGroup m n r Fk) := A w.1 * ∏ k, B (w.2.2.1 k)
  let P : MvPolynomial (Fin m ⊕ Fin r) ℂ :=
    (1 + ∑ i : Fin m, MvPolynomial.X (Sum.inl i) ^ 2) ^ (m + 1) *
      ∏ j : Fin r, (1 + MvPolynomial.X (Sum.inr j) ^ 2)
  obtain ⟨C,hC⟩ := polynomial_weight_bounded P f
  have hP (y : ElementaryLieGroup m n r Fk) : MvPolynomial.eval
      (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) P = (D y : ℂ) := by
    simp [P,D,A,B,EuclideanSpace.real_norm_sq_eq]
  have hdom : Integrable (fun w ↦ C * (D w)⁻¹) ν := by
    have hπ := Integrable.fintype_prod (ι := Fin r) (fun _ ↦ hB)
    have hf : Integrable (fun _ : Fk ↦ (1 : ℝ)) (Measure.count : Measure Fk) := integrable_const _
    have ht : Integrable (fun _ : Fin n → AddCircle (1 : ℝ) ↦ (1 : ℝ)) volume :=
      integrable_const _
    convert (hA.mul_prod (ht.mul_prod (hπ.mul_prod hf))).const_mul C using 1
    funext w
    simp only [D, mul_inv_rev, one_mul, mul_one, Finset.prod_inv_distrib]
    ring
  refine hdom.mono' (elementarySchwartz_continuousFunction f).aestronglyMeasurable
    (Eventually.of_forall fun w ↦ ?_)
  have hD : 0 < D w := by dsimp [D, A, B]; positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hD, mul_comm]
  have h := hC w
  rwa [hP,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD] at h

/-- The compact annihilator of the open dual subgroup recovers the original good subgroup. -/
private theorem isCompact_of_bruhatGoodSubgroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) : IsCompact (k : Set G) := by
  have h := isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  rwa [lcaDualAnnihilator_annihilator k hk.1] at h

open scoped Pointwise in
/-- A Schwartz–Bruhat stage is integrable after pullback along the quotient by its compact
kernel and extension by zero from its open subgroup. -/
private theorem schwartzBruhatStage_integrable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) :
    Integrable (schwartzBruhatStageRealization a e f) μ := by
  let H := a.val.1
  let K := OrderDual.ofDual a.val.2
  let L := K.comap H.subtype
  have hH : IsOpen (H : Set G) := a.property.1
  have hK : IsCompact (L : Set H) :=
    (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_of_bruhatGoodSubgroup K a.property.2.2.1)
  let q := QuotientGroup.mk' L
  have hq : IsProperMap q := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hK, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L y
    change IsCompact (QuotientGroup.mk ⁻¹' {QuotientGroup.mk x})
    rw [← image_singleton, QuotientGroup.preimage_image_mk_eq_mul]
    exact isCompact_singleton.mul hK
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let : MeasurableSpace e.finiteFactor := borel _
  let : BorelSpace e.finiteFactor := ⟨rfl⟩
  let : BorelSpace E := elementaryLieGroup_borelSpace
  let : T2Space (Multiplicative E) := inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin e.realDim) ×
    (Fin e.torusDim → AddCircle (1 : ℝ)) × (Fin e.latticeRank → ℤ) × e.finiteFactor))
  let p : H →* Multiplicative E := e.equiv.toMonoidHom.comp q
  have hp : IsProperMap p := e.equiv.toHomeomorph.isProperMap.comp hq
  let ν := μ.comap H.subtype
  let : ν.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul) μ (f := H.subtype)
      hH.isOpenEmbedding_subtypeVal
  let ρ := ν.map p
  have hρ : ρ.IsHaarMeasure := Measure.isHaarMeasure_map ν p hp.continuous
    (e.equiv.surjective.comp (QuotientGroup.mk'_surjective L))
    (isProperMap_iff_tendsto_cocompact.mp hp).2
  let ρ' : Measure E := ρ
  let : ρ'.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hρ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hρ.toIsOpenPosMeasure
      map_add_left_eq_self := fun x ↦ hρ.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  have hf : Integrable f ρ' := elementarySchwartz_integrable f ρ'
  have hcomp : Integrable (fun x : H ↦ f (Multiplicative.toAdd (p x))) ν :=
    hf.comp_measurable hp.continuous.measurable
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := (H : Set G))
  · rw [integrableOn_iff_comap_subtypeVal hH.measurableSet]
    refine hcomp.congr (Eventually.of_forall fun x ↦ ?_)
    exact ((schwartzBruhatStageRealization_apply a e f x.val).trans
      (dite_eq_left x.property)).symm
  · intro x hx
    exact (schwartzBruhatStageRealization_apply a e f x).trans (dite_eq_right hx)

/-- Rapid decay on the elementary stages gives Haar integrability on the full group. -/
theorem SchwartzBruhat.integrable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : SchwartzBruhat G) : Integrable f.val μ := by
  obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  exact hs ▸ schwartzBruhatStage_integrable μ a e s

/-- The Fourier integral is linear on the space of Schwartz tests. -/
private theorem schwartzBruhat_fourier_linear {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ B : SchwartzBruhat G →ₗ[ℂ] (PontryaginDual G → ℂ), ∀ f χ, B f χ = lcaFourier μ f χ := by
  refine ⟨{ toFun := fun f ↦ lcaFourier μ f
            map_add' := ?_
            map_smul' := ?_ },fun _ _ ↦ rfl⟩
  · intro f g
    funext χ
    change (∫ x, (f x + g x) * star (χ x : ℂ) ∂μ) = _ + _
    simp_rw [add_mul]
    exact integral_add (integrable_fourierIntegrand μ (SchwartzBruhat.integrable μ f) χ)
      (integrable_fourierIntegrand μ (SchwartzBruhat.integrable μ g) χ)
  · intro c f
    funext χ
    change (∫ x, (c * f x) * star (χ x : ℂ) ∂μ) = c * _
    simp_rw [mul_assoc,integral_const_mul]
    rfl

end SchwartzIntegrability

section AveragingAndFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

variable (K : Subgroup G)

section CompactAveraging

local instance sec1cCompactSubgroupMeasurableSpace : MeasurableSpace K := borel _

private theorem fullBruhatStage_average (hG : IsCompactlyGeneratedGroup G) (hk : IsBruhatGoodSubgroup K)
    (μK : Measure K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] (f : G → ℂ) (x : G)
    (hK : IsCompact (K : Set G)) : schwartzBruhatStageAverage (fullBruhatStage hG hk) f x =
      ∫ k : K, f (x * k.val) ∂μK := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : BorelSpace K := ⟨rfl⟩
  let U : TopologicalSpace.PositiveCompacts K := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let : IsProbabilityMeasure (Measure.haarMeasure U) := ⟨Measure.haarMeasure_self⟩
  change (if x ∈ (⊤ : Subgroup G) then ∫ k : K, f (k.val * x) ∂Measure.haarMeasure U else 0) = _
  rw [ite_eq_left (Subgroup.mem_top x), Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.haarMeasure U) μK]
  simp_rw [mul_comm _ x]

/-- Paper: Lemma D.1.6.18, p. 772. Normalized Haar averaging over a compact
subgroup of an elementary group gives a continuous surjection of Schwartz spaces. -/
theorem elementary_schwartzBruhat_average (e : ElementaryLCAPresentation G)
    (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      (∀ (f : SchwartzBruhat G) (x : G),
        Integrable (fun k : K ↦ f (x * k.val)) μK ∧
        P f (QuotientGroup.mk x) = ∫ k : K, f (x * k.val) ∂μK) ∧
      Function.Surjective P := by
  classical
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK.isClosed
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : BorelSpace K := ⟨rfl⟩
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  have hOpen := isOpen_lcaAnnihilator K hK
  have hk : IsBruhatGoodSubgroup K := ⟨hK.isClosed, hOpen,
    isCompactlyGeneratedGroup_closedSubgroup (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean hE.2)
      _ ((lcaAnnihilator K).isClosed_of_isOpen hOpen)⟩
  let a := fullBruhatStage hE.1 hk
  have hW := fullBruhatStage_quotientEquiv hE.1 hk (QuotientGroup.mk' K)
    QuotientGroup.isOpenQuotientMap_mk (QuotientGroup.ker_mk' K)
  let w := hW.choose
  have hw := hW.choose_spec
  let d := Classical.choice a.elementary
  let eQ : ElementaryLCAPresentation (G ⧸ K) := {d with equiv := w.symm.trans d.equiv}
  have hI := elementarySchwartz_equiv_schwartzBruhat eQ
  let I := hI.choose
  have hR := schwartzBruhatStage_average_retraction a d
  let R := hR.choose
  refine ⟨I.toContinuousLinearMap.comp R, fun f x ↦ ⟨?_, ?_⟩,
    I.surjective.comp (show Function.LeftInverse R (schwartzBruhatStageInclusion a d) from hR.choose_spec.1).surjective⟩
  · have hI' := elementarySchwartz_equiv_schwartzBruhat e
    let s := hI'.choose.symm f
    have hs (y : G) : f y = s (e.equiv y).toAdd :=
      (congrArg (fun z : SchwartzBruhat G ↦ z y) (hI'.choose.apply_symm_apply f)).symm.trans
        (hI'.choose_spec s y)
    have hc : Continuous f.val := by
      exact ((elementarySchwartz_continuousFunction s).comp (continuous_toAdd.comp e.equiv.continuous)).congr fun y ↦ (hs y).symm
    exact (hc.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · change I (R f) (QuotientGroup.mk x) = _
    rw [hI.choose_spec]
    change R f (d.equiv (w.symm (QuotientGroup.mk x))).toAdd = _
    have hwx : w.symm (QuotientGroup.mk x) = QuotientGroup.mk (⟨x, Subgroup.mem_top x⟩ : a.val.1) :=
      w.toEquiv.symm_apply_eq.mpr (hw x).symm
    refine (congrArg (fun y : a.quotient ↦ R f (d.equiv y).toAdd) hwx).trans ?_
    have h := hR.choose_spec.2 f x
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx] at h
    refine h.trans ?_
    exact fullBruhatStage_average K hE.1 hk μK f x hK

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
      lcaFourier μ g = bruhatDiffSymbol D * lcaFourier μ f := by
  classical
  obtain ⟨B,hB⟩ := schwartzBruhat_fourier_linear μ
  have hb (z : SchwartzBruhat G) : Integrable z.val μ ∧ ∀ χ, B z χ = lcaFourier μ z χ :=
    ⟨SchwartzBruhat.integrable μ z, hB z⟩
  have hgen (L : Module.End ℂ (bruhatSmoothSubmodule (G := G))) (hL : L ∈ range (bruhatFirstOrder (G := G))) :
      ∃ c : PontryaginDual G → ℂ, (∀ χ, L (smoothCharacter χ) = c χ • smoothCharacter χ) ∧
        ∀ z : SchwartzBruhat G, ∃ y, smoothInclusion (G := G) y = L (smoothInclusion (G := G) z) ∧ ∀ χ, B y χ = c χ * B z χ := by
    obtain ⟨a,rfl⟩ := hL
    exact ⟨bruhatDiffSymbol (bruhatDiffGenerator a), generator_character a, generator_schwartz_lift μ B hb a⟩
  have hP := symbol_action_adjoin (smoothInclusion (G := G)) B smoothCharacter _ hgen (L := D.val) D.property
  obtain ⟨c,hc,hL⟩ := hP
  obtain ⟨g,hg,hF⟩ := hL f
  refine ⟨(smoothInclusion (G := G) f).property,g,congrArg Subtype.val hg,(hb f).1,(hb g).1,funext fun χ ↦ ?_⟩
  have hs : bruhatDiffSymbol D χ = c χ := by
    change (D.val (smoothCharacter χ)).val 1 = _
    rw [hc]
    change c χ * (χ 1 : ℂ) = c χ
    rw [map_one,Circle.coe_one,mul_one]
  change lcaFourier μ g χ = bruhatDiffSymbol D χ * lcaFourier μ f χ
  rw [hs]
  exact (hB g χ).symm.trans ((hF χ).trans (congrArg (c χ * ·) (hB f χ)))

/-- Paper: Lemma D.1.6.19(2), p. 773. The Fourier integral gives a continuous
linear isomorphism of the two Schwartz–Bruhat spaces. -/
theorem schwartzBruhat_fourier_equiv :
    ∃ F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ f : SchwartzBruhat G, Integrable (f : G → ℂ) μ ∧
        ∀ χ, F f χ = lcaFourier μ f χ := by sorry

/-- Both Schwartz functions and their transforms are integrable, so Plancherel inversion holds pointwise. -/
private theorem schwartzBruhat_inverse_integral (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)
    (g : SchwartzBruhat G) (x : G) :
    Integrable (fun χ : PontryaginDual G ↦ lcaFourier μ g χ * (χ x : ℂ)) ν ∧
      g x = ∫ χ : PontryaginDual G, lcaFourier μ g χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨A, hA⟩ := schwartzBruhat_fourier_equiv μ
  have hg := SchwartzBruhat.integrable μ g
  have hu : Integrable (lcaFourier μ g) ν :=
    (SchwartzBruhat.integrable ν (A g)).congr (.of_forall (hA g).2)
  have hm : Continuous (fun χ : PontryaginDual G ↦ (χ x : ℂ)) :=
    continuous_subtype_val.comp (pontryaginDual_eval (G := G) x).continuous
  refine ⟨hu.mul_bdd (c := 1) hm.aestronglyMeasurable (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le), ?_⟩
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous g
  have hg₂ : MemLp (g : G → ℂ) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    simpa only [sq] using hg.norm.mul_bdd (c := ‖b‖) hg.norm.aestronglyMeasurable
      (.of_forall fun y ↦ by simpa only [Real.norm_of_nonneg (norm_nonneg _), ← hb] using b.norm_coe_le_norm y)
  have hv := (lcaFourier_unitary μ ν hν).exists.choose_spec (g : G → ℂ) hg hg₂
  obtain ⟨F,hF,hFx⟩ := lcaInverseFourier_zeroAtInfty μ ν hν _ _ hu hv
  have heq : (F : G → ℂ) = b :=
    Measure.eq_of_ae_eq ((hF.trans hg₂.coeFn_toLp).trans (.of_forall fun y ↦ (hb y).symm)) F.continuous b.continuous
  exact (hb x).symm.trans ((congrFun heq x).symm.trans (hFx x))

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
          (fun χ ↦ ∫ ψ : lcaAnnihilator a.val.1, lcaFourier μ f (χ * ψ.val) ∂νJ) := by
  classical
  intro avg
  let J := a.val.1
  let K := OrderDual.ofDual a.val.2
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hK := isCompact_of_bruhatGoodSubgroup K a.property.2.2.1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (lcaAnnihilator J) := isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator _ a.property.1)
  have hf := SchwartzBruhat.integrable μ f
  let e := Classical.choice a.elementary
  obtain ⟨R,_,hR⟩ := schwartzBruhatStage_average_retraction a e
  let g : SchwartzBruhat G := schwartzBruhatStageInclusion a e (R f)
  have hg : g.val = avg := funext fun x ↦
    (hR f x).trans (schwartzBruhatStageAverage_normalized a hK μK f x)
  have hav : Integrable avg μ := hg ▸ SchwartzBruhat.integrable μ g
  refine ⟨hf,hav,?_,?_,?_⟩
  · intro x
    obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous f
    exact ((b.continuous.comp (continuous_const.mul continuous_subtype_val)).congr
      fun k : K ↦ hb (x * k.val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro χ
    obtain ⟨F,hF⟩ := lcaFourier_zeroAtInfty μ hf
    exact ((F.continuous.comp (continuous_const.mul continuous_subtype_val)).congr
      fun ψ : lcaAnnihilator J ↦ hF (χ * ψ.val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · let c := (J : Set G).indicator f.val
    have hcut (x : G) : avg x = ∫ k : K, c (x * k.val) ∂μK := by
      by_cases hx : x ∈ J
      · have hc (k : K) : c (x * k.val) = f (x * k.val) := indicator_of_mem
          (J.mul_mem hx (a.property.2.2.2 k.property)) _
        simp only [hc]
        exact indicator_of_mem hx _
      · have hc (k : K) : c (x * k.val) = 0 := indicator_of_notMem
          (fun hm ↦ hx ((J.mul_mem_cancel_right (a.property.2.2.2 k.property)).mp hm)) _
        change (J : Set G).indicator _ x = _
        rw [indicator_of_notMem hx]
        simp only [hc]
        exact (integral_const (μ := μK) (0 : ℂ)).trans (smul_zero _) |>.symm
    funext χ
    refine (lcaFourier_compact_average μ K hK μK (hf.indicator a.property.1.measurableSet) hav hcut χ).trans ?_
    exact congrArg (fun u : PontryaginDual G → ℂ ↦ (lcaAnnihilator K : Set (PontryaginDual G)).indicator u χ)
      (funext (lcaFourier_cutoff μ J a.property.1 νJ hf))

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
        ∫ χ, lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ) ∂νQ := by
  intro q
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  let : BorelSpace (G ⧸ K) := ⟨rfl⟩
  let : μQ.IsHaarMeasure := hQ.1
  let : μQ.Regular := hQ.2.1
  let g := schwartzBruhatCosetIntegral K μK hK f
  have hf := SchwartzBruhat.integrable μ f
  have hfour (χ : PontryaginDual (G ⧸ K)) : lcaFourier μ f (PontryaginDual.map q χ) = lcaFourier μQ g χ := by
    let t (y : G) := f y * star (χ (q y) : ℂ)
    have hmeas : Continuous (fun y ↦ star (χ (q y) : ℂ)) :=
      (continuous_subtype_val.comp (χ.continuous.comp q.continuous)).star
    have ht : Integrable t μ := hf.mul_bdd (c := 1) hmeas.aestronglyMeasurable
      (.of_forall fun y ↦ by simp)
    change (∫ y, t y ∂μ) = _
    rw [(weilQuotientIntegral_L1 K hK μ μK μQ hQ ht).2.2]
    unfold lcaFourier
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective z
    have htk (k : K) : t (y * k.val) = f (y * k.val) * star (χ (q y) : ℂ) := by
      have hqk : q k.val = 1 := (QuotientGroup.eq_one_iff k.val).mpr k.property
      simp only [t, map_mul q, hqk, mul_one]
    have hfi := (lcaCosetIntegral_mem_schwartzBruhat K μK hK f).1 y
    have hti : Integrable (fun k : K ↦ t (y * k.val)) μK :=
      (hfi.mul_const _).congr (.of_forall fun k ↦ (htk k).symm)
    rw [lcaCosetIntegral_mk K μK t y hti]
    simp_rw [htk, integral_mul_const]
    exact congrArg (fun z : ℂ ↦ z * _) (schwartzBruhatCosetIntegral_mk K μK hK f y).symm
  refine ⟨hf, ?_⟩
  simp only [hfour]
  exact schwartzBruhat_inverse_integral μQ νQ hνQ g (q x)

section CosetIntegration

omit hK hHaarK hRegularK hBorel hTop hT2 hLC

/-- An annihilator is the intersection of the closed kernels of point evaluations. -/
private theorem closed_lcaAnnihilator {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (K : Subgroup G) :
    IsClosed (lcaAnnihilator K : Set (PontryaginDual G)) := by
  have he : (lcaAnnihilator K : Set (PontryaginDual G)) =
      ⋂ k : K, {χ : PontryaginDual G | χ k.val = 1} := by
    ext χ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_lcaAnnihilator_iff]
  rw [he]
  exact isClosed_iInter fun k ↦ isClosed_eq (pontryaginDual_eval (G := G) k.val).continuous continuous_const

private theorem compactlyGenerated_of_closedEmbedding {H L : Type*} [CommGroup H] [CommGroup L]
    [TopologicalSpace H] [TopologicalSpace L] [IsTopologicalGroup L] [T2Space L] [LocallyCompactSpace L]
    (f : H →* L) (hf : IsClosedEmbedding f) (hL : IsCompactlyGeneratedGroup L) :
    IsCompactlyGeneratedGroup H := by
  have hr : IsCompactlyGeneratedGroup f.range := isCompactlyGeneratedGroup_closedSubgroup hL f.range hf.isClosed_range
  let e := MulEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h ↦ hf.injective (congrArg Subtype.val h),
    fun ⟨_,x,hx⟩ ↦ ⟨x,Subtype.ext hx⟩⟩
  have hd : IsInducing f.rangeRestrict := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let d : H ≃ₜ* f.range := ⟨e,hd.continuous,
    (e.toEquiv.toHomeomorphOfIsInducing hd).symm.continuous⟩
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv d.symm hr

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Pullback embeds the annihilator of the image as a closed subgroup of the original annihilator. -/
private theorem isBruhatGoodSubgroup_quotient_map (K : Subgroup G) (hK : IsClosed (K : Set G))
    (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) :
    IsBruhatGoodSubgroup (k.map (QuotientGroup.mk' K)) := by
  let : IsClosed (K : Set G) := hK
  let q := QuotientGroup.mk' K
  let k' := k.map q
  have hkc := isCompact_of_bruhatGoodSubgroup k hk
  have hk' : IsCompact (k' : Set (G ⧸ K)) := hkc.image QuotientGroup.continuous_mk
  refine ⟨hk'.isClosed,isOpen_lcaAnnihilator k' hk',?_⟩
  obtain ⟨e,he⟩ := lcaQuotientDual_equiv_annihilator K hK
  let i := (lcaAnnihilator K).subtype.comp (e.toMonoidHom.comp (lcaAnnihilator k').subtype)
  let f := i.codRestrict (lcaAnnihilator k) fun χ ↦ (mem_lcaAnnihilator_iff k _).mpr fun u ↦ by
    change (e χ.val).val u.val = 1
    rw [he]
    exact (mem_lcaAnnihilator_iff k' _).mp χ.property ⟨q u.val,⟨u.val,u.property,rfl⟩⟩
  have hi : IsClosedEmbedding i := (closed_lcaAnnihilator K).isClosedEmbedding_subtypeVal.comp
    (e.toHomeomorph.isClosedEmbedding.comp (closed_lcaAnnihilator k').isClosedEmbedding_subtypeVal)
  let : LocallyCompactSpace (lcaAnnihilator k) := hk.2.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  exact compactlyGenerated_of_closedEmbedding f
    (IsClosedEmbedding.of_comp_iff (closed_lcaAnnihilator k).isClosedEmbedding_subtypeVal |>.mp hi) hk.2.2

/-- The images of the open and compact subgroups form a structural pair on the quotient. -/
private theorem bruhatStructuralPair_quotient_map (K : Subgroup G) (hK : IsClosed (K : Set G))
    (a : BruhatStructuralPair G) :
    ∃ b : BruhatStructuralPair (G ⧸ K), b.val.1 = a.val.1.map (QuotientGroup.mk' K) ∧
      OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K) := by
  let q := QuotientGroup.mk' K
  let J := a.val.1
  let M := J.map q
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have ho : IsOpen (M : Set (G ⧸ K)) := hq.isOpenMap _ a.property.1
  let f := (q.comp J.subtype).codRestrict M (fun x ↦ ⟨x.val,x.property,rfl⟩)
  have hf : IsOpenMap f := (hq.isOpenMap.comp a.property.1.isOpenEmbedding_subtypeVal.isOpenMap).subtype_mk _
  have hc : Continuous f := (hq.continuous.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective f := fun ⟨_,x,hx,h⟩ ↦ ⟨⟨x,hx⟩,Subtype.ext h⟩
  obtain ⟨U,hU,hcU,hg⟩ := a.property.2.1
  have hM : IsCompactlyGeneratedGroup M := by
    refine ⟨f '' U,?_,hcU.image hc,?_⟩
    · simpa only [map_one] using hf.image_mem_nhds hU
    · rw [← MonoidHom.map_closure,hg,Subgroup.map_top_of_surjective f hs]
  exact ⟨⟨(M,OrderDual.toDual ((OrderDual.ofDual a.val.2).map q)),ho,hM,
    isBruhatGoodSubgroup_quotient_map K hK _ a.property.2.2.1,Subgroup.map_mono a.property.2.2.2⟩,rfl,rfl⟩

private theorem stageRealization_mul_kernel (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (x u : G) (hu : u ∈ OrderDual.ofDual a.val.2) :
    schwartzBruhatStageRealization a e s (x * u) = schwartzBruhatStageRealization a e s x := by
  have hu' := a.property.2.2.2 hu
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ a.val.1
  · rw [dite_eq_left (a.val.1.mul_mem hx hu'), dite_eq_left hx]
    let v : a.val.1 := ⟨u,hu'⟩
    have hv : v ∈ (OrderDual.ofDual a.val.2).comap a.val.1.subtype := hu
    exact congrArg (fun z : a.quotient ↦ s (e.equiv z).toAdd) (QuotientGroup.mk_mul_of_mem ⟨x,hx⟩ hv)
  · rw [dite_eq_right (fun h ↦ hx ((a.val.1.mul_mem_cancel_right hu').mp h)), dite_eq_right hx]

/-- Normalized averaging fixes a supported, kernel-invariant function. -/
private theorem stageAverage_eq_self_of_invariant (b : BruhatStructuralPair G) (f : G → ℂ)
    (hzero : ∀ x ∉ b.val.1, f x = 0) (hinv : ∀ x k, k ∈ OrderDual.ofDual b.val.2 → f (x*k) = f x)
    (x : G) : schwartzBruhatStageAverage b f x = f x := by
  classical
  let k := OrderDual.ofDual b.val.2
  let : MeasurableSpace k := borel k
  let : BorelSpace k := ⟨rfl⟩
  have hk := isCompact_of_bruhatGoodSubgroup k b.property.2.2.1
  let : CompactSpace k := isCompact_iff_compactSpace.mp hk
  let U : TopologicalSpace.PositiveCompacts k := ⟨⟨univ,isCompact_univ⟩, by simp⟩
  let : IsProbabilityMeasure (Measure.haarMeasure U) := ⟨Measure.haarMeasure_self⟩
  by_cases hx : x ∈ b.val.1
  · unfold schwartzBruhatStageAverage
    rw [ite_eq_left hx]
    change (∫ u : k, f (u.val*x) ∂Measure.haarMeasure U) = f x
    simp only [mul_comm _ x,fun u : k ↦ hinv x u u.property, integral_const]
    simp
  · unfold schwartzBruhatStageAverage
    rw [ite_eq_right hx,hzero x hx]

private theorem continuous_to_stage_of_realization {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) (B : E →ₗ[ℂ] SchwartzBruhatStage d)
    (h : ∀ x : G, ∃ L : E →L[ℂ] ℂ, ∀ s, L s = schwartzBruhatStageRealization b d (B s) x) :
    Continuous B := by
  apply continuous_toElementarySchwartz_of_eval
  intro y
  obtain ⟨q,hq⟩ := d.equiv.surjective (Multiplicative.ofAdd y)
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨L,hL⟩ := h x.val
  refine ⟨L,fun s ↦ ?_⟩
  exact (hL s).trans ((schwartzBruhatStageRealization_apply b d (B s) _).trans
    ((dite_eq_left x.property).trans (congrArg (fun t ↦ B s (Multiplicative.toAdd t)) hq)))

variable [MeasurableSpace G] [BorelSpace G] (K : Subgroup G) (μK : Measure K) [μK.IsHaarMeasure] [μK.Regular]
variable (hK : IsClosed (K : Set G))


private theorem cosetIntegral_add_apply (f g : SchwartzBruhat G) (y : G ⧸ K) :
    schwartzBruhatCosetIntegral K μK hK (f+g) y =
      schwartzBruhatCosetIntegral K μK hK f y + schwartzBruhatCosetIntegral K μK hK g y := by
  induction y using QuotientGroup.induction_on with
  | _ x =>
    simp only [schwartzBruhatCosetIntegral_mk]
    exact integral_add ((lcaCosetIntegral_mem_schwartzBruhat K μK hK f).1 x)
      ((lcaCosetIntegral_mem_schwartzBruhat K μK hK g).1 x)

private theorem cosetIntegral_smul_apply (c : ℂ) (f : SchwartzBruhat G) (y : G ⧸ K) :
    schwartzBruhatCosetIntegral K μK hK (c • f) y = c • schwartzBruhatCosetIntegral K μK hK f y := by
  induction y using QuotientGroup.induction_on with
  | _ x =>
    simp only [schwartzBruhatCosetIntegral_mk]
    exact integral_smul c _

private def cosetIntegralLinear : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat (G ⧸ K) where
  toFun := schwartzBruhatCosetIntegral K μK hK
  map_add' f g := Subtype.ext (funext (cosetIntegral_add_apply K μK hK f g))
  map_smul' c f := Subtype.ext (funext (cosetIntegral_smul_apply K μK hK c f))

/-- Integration sends a stage into the fixed space of its image stage projector. -/
private theorem cosetIntegral_stageAverage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (b : BruhatStructuralPair (G ⧸ K))
    (hJ : b.val.1 = a.val.1.map (QuotientGroup.mk' K))
    (hk : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K))
    (s : SchwartzBruhatStage e) (x : G ⧸ K) :
    let f := schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s)
    schwartzBruhatStageAverage b f x = f x := by
  let : IsClosed (K : Set G) := hK
  let q := QuotientGroup.mk' K
  let f : SchwartzBruhat G := schwartzBruhatStageInclusion a e s
  have hmk := schwartzBruhatCosetIntegral_mk K μK hK f
  dsimp only
  apply stageAverage_eq_self_of_invariant
  · intro y hy
    obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective y
    refine (hmk z).trans ?_
    have hz (u : K) : z*u.val ∉ a.val.1 := by
      intro h
      apply hy
      rw [hJ]
      exact ⟨z*u.val,h,QuotientGroup.mk_mul_of_mem z u.property⟩
    change (∫ u : K, schwartzBruhatStageRealization a e s (z*u.val) ∂μK) = 0
    have h0 (u : K) : schwartzBruhatStageRealization a e s (z * u.val) = 0 :=
      (schwartzBruhatStageRealization_apply a e s _).trans (dite_eq_right (hz u))
    simp only [h0, integral_zero]
  · intro y k hk'
    obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective y
    rw [hk] at hk'
    obtain ⟨v,hv,rfl⟩ := hk'
    refine (hmk (z*v)).trans (Eq.trans ?_ (hmk z).symm)
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    change schwartzBruhatStageRealization a e s (z*v*u.val) = _
    rw [mul_right_comm]
    exact stageRealization_mul_kernel a e s _ v hv


open scoped BoundedContinuousFunction in
/-- The zero-order seminorm controls evaluation uniformly on the elementary group. -/
private theorem elementarySchwartz_continuousEval {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    Continuous (fun p : ElementarySchwartz m n r F × ElementaryLieGroup m n r F ↦ p.1 p.2) := by
  let E := ElementarySchwartz m n r F
  let X := ElementaryLieGroup m n r F
  let q := (elementarySchwartzSeminorm (m := m) (n := n) (r := r) (F := F) (0,0,0,0))
  have hb (f : E) (x : X) : ‖f x‖ ≤ q f := by
    change (‖f x‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0,0,0,0)).toReal
    apply ENNReal.toReal_mono (f.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun y ↦ (‖f y‖₊ : ENNReal)) x
  let L : E →ₗ[ℂ] (X →ᵇ ℂ) :=
    { toFun := fun f ↦ BoundedContinuousFunction.ofNormedAddCommGroup f.val
        (elementarySchwartz_continuousFunction f) (q f) (hb f)
      map_add' := fun _ _ ↦ BoundedContinuousFunction.ext (fun _ ↦ rfl)
      map_smul' := fun _ _ ↦ BoundedContinuousFunction.ext (fun _ ↦ rfl) }
  have hL : Continuous L := by
    refine (norm_withSeminorms ℂ _).continuous_of_continuous_comp L fun _ ↦ ?_
    exact Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0,0,0,0))
      (fun f ↦ BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg q f) (hb f))
  exact continuous_eval.comp ((hL.comp continuous_fst).prodMk continuous_snd)

private theorem stageIntegral_eval_continuous (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (z : G) :
    ∃ L : SchwartzBruhatStage e →L[ℂ] ℂ, ∀ s,
      L s = schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s) (QuotientGroup.mk z) := by
  let X := SchwartzBruhatStage e
  let : TopologicalSpace.MetrizableSpace X := elementarySchwartz_isFrechet.choose_spec.2.1
  let : BarrelledSpace ℂ X := elementarySchwartz_barrelled
  let C : X →ₗ[ℂ] (K → ℂ) := (LinearMap.funLeft ℂ ℂ (fun k : K ↦ z*k.val)).comp (schwartzBruhatStageRealization a e)
  have hc (k : K) : Continuous (fun s : X ↦ C s k) := by
    classical
    change Continuous (fun s : X ↦ schwartzBruhatStageRealization a e s (z*k.val))
    simp only [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · exact elementarySchwartz_continuousEval.comp (continuous_id.prodMk continuous_const)
    · exact continuous_const
  have hi (s : X) : Integrable (C s) μK :=
    (lcaCosetIntegral_mem_schwartzBruhat K μK hK (schwartzBruhatStageInclusion a e s)).1 z
  obtain ⟨L,hL⟩ := exists_integralCLM_of_pointwise_continuous μK C hc hi
  exact ⟨L, fun s ↦ (hL s).trans (schwartzBruhatCosetIntegral_mk K μK hK (schwartzBruhatStageInclusion a e s) z).symm⟩

private theorem stageIntegral_eval_quotient (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (y : G ⧸ K) : ∃ L : SchwartzBruhatStage e →L[ℂ] ℂ, ∀ s,
      L s = schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s) y := by
  exact QuotientGroup.induction_on y (stageIntegral_eval_continuous K μK hK a e)

/-- The coset integral factors continuously through a single elementary quotient stage. -/
private theorem cosetIntegral_continuous_on_stage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Continuous (fun s : SchwartzBruhatStage e ↦ schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s)) := by
  classical
  let : IsClosed (K : Set G) := hK
  let b := (bruhatStructuralPair_quotient_map K hK a).choose
  have hJ := (bruhatStructuralPair_quotient_map K hK a).choose_spec.1
  have hk := (bruhatStructuralPair_quotient_map K hK a).choose_spec.2
  let d := Classical.choice b.elementary
  let j := schwartzBruhatStageInclusion b d
  have hret := schwartzBruhatStage_average_retraction b d
  let R := hret.choose
  let A := (cosetIntegralLinear K μK hK).comp (schwartzBruhatStageInclusion a e)
  let B := R.toLinearMap.comp A
  have hval (s : SchwartzBruhatStage e) (x : G ⧸ K) :
      schwartzBruhatStageRealization b d (B s) x = A s x :=
    (hret.choose_spec.2 (A s) x).trans (cosetIntegral_stageAverage K μK hK a e b hJ hk s x)
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := elementarySchwartz_barrelled
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  have hB : Continuous B := by
    refine continuous_to_stage_of_realization b d B fun x ↦ ?_
    let H := stageIntegral_eval_quotient K μK hK a e x
    exact ⟨H.choose, fun s ↦ (H.choose_spec s).trans (hval s x).symm⟩
  have hj : Continuous (show SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhat (G ⧸ K) from j) :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property b d
  exact (hj.comp hB).congr fun s ↦ Subtype.ext (funext (hval s))

end CosetIntegration

/-- Paper: Theorem D.1.7.1(2), p. 776. The coset integral on Schwartz–Bruhat
functions is a continuous linear map. -/
theorem schwartzBruhatCosetIntegral_continuousLinear :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      ∀ f, P f = schwartzBruhatCosetIntegral K μK hK f := by
  let A := cosetIntegralLinear K μK hK
  have hA : Continuous A := by
    apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp A fun p ↦ ?_
    let P : SeminormFamily ℂ (SchwartzBruhat G) {q : Seminorm ℂ (SchwartzBruhat G) //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine hP.continuous_seminorm ⟨p.val.comp A,?_⟩
    intro a e
    exact ((withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm p).comp
      (cosetIntegral_continuous_on_stage K μK hK a e)
  exact ⟨⟨A,hA⟩,fun _ ↦ rfl⟩

/-- Paper: Theorem D.1.7.1(2), p. 776. Every Schwartz–Bruhat function on the
quotient is the coset integral of a Schwartz–Bruhat function on the group. -/
theorem schwartzBruhatCosetIntegral_surjective :
    Function.Surjective (schwartzBruhatCosetIntegral K μK hK) := by sorry

omit hK hHaarK hRegularK hBorel hTop hT2 hLC in
/-- An embedded Fréchet stage gives its range the same additive uniformity. -/
private theorem frechet_range_of_embedding {X E : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [PolynormableSpace ℂ E] (i : X →L[ℂ] E) (hi : IsEmbedding i)
    (hX : IsFrechetTVS X) : IsFrechetTVS i.range := by
  obtain ⟨_, _, hmetr, hcomp⟩ := hX
  have he : IsEmbedding i.rangeRestrict := IsEmbedding.subtypeVal.of_comp_iff.mp hi
  have hs : Function.Surjective i.rangeRestrict := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
  let m := (Equiv.ofBijective i.rangeRestrict ⟨he.injective, hs⟩).toHomeomorphOfIsInducing he.isInducing
  refine ⟨inferInstance, inferInstance, m.symm.isEmbedding.metrizableSpace, ?_⟩
  let : UniformSpace i.range := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup i.range := isUniformAddGroup_of_addCommGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq] at hcomp
  exact ((AddMonoidHom.isUniformInducing_of_isInducing (f := i.rangeRestrict) he.isInducing).completeSpace_congr hs).mp hcomp

omit hK hHaarK hRegularK hBorel hTop hT2 hLC in
/-- Using the embedded ranges puts the Fréchet stages in the universe of the limit. -/
private theorem isLFSpace_of_embedded_stages {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, UniformSpace (X n)] [∀ n, IsUniformAddGroup (X n)]
    (j : ∀ n, X n →L[ℂ] X (n+1)) (i : ∀ n, X n →L[ℂ] E) (h : IsInjectiveLCLimit j i)
    (he : ∀ n, IsEmbedding (i n)) (hX : ∀ n, IsFrechetTVS (X n)) : IsLFSpace E := by
  apply (lfSpace_quotient_properties (E := E)).1
  refine ⟨inferInstance, fun n ↦ (i n).range, monotone_nat_of_le_succ (fun n x hx ↦ ?_),
    fun n ↦ frechet_range_of_embedding (i n) (he n) (hX n), h.exhaustive, ?_⟩
  · obtain ⟨v, rfl⟩ := hx
    exact ⟨j n v, DFunLike.congr_fun (h.compatible n) v⟩
  · refine h.topology_eq.trans (congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology) ?_)
    funext p
    apply propext
    apply forall_congr'
    intro n
    have hi : IsEmbedding (i n).rangeRestrict := IsEmbedding.subtypeVal.of_comp_iff.mp (he n)
    have hs : Function.Surjective (i n).rangeRestrict := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
    exact (hi.isInducing.isOpenQuotientMap_of_surjective hs).isQuotientMap.continuous_iff
      (g := p ∘ (i n).range.subtype) |>.symm

omit hK hHaarK hRegularK hBorel [MeasurableSpace G] in
/-- A cofinal sequence of structural stages presents the Schwartz–Bruhat space as LF. -/
private theorem schwartzBruhat_isLF [SecondCountableTopology G] : IsLFSpace (SchwartzBruhat G) := by
  classical
  let E := SchwartzBruhat G
  let : T2Space E := schwartzBruhat_t2
  obtain ⟨a, e, j, _, hcof, hj, _⟩ := schwartzBruhat_exists_topologicallyExact (G := G)
  let i (n : ℕ) : SchwartzBruhatStage (e n) →L[ℂ] E :=
    ⟨schwartzBruhatStageInclusion (a n) (e n), (schwartzBruhatStage_isEmbedding _ _).continuous⟩
  have hFac (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) :
      ∃ n, ∃ k : SchwartzBruhatStage d →L[ℂ] SchwartzBruhatStage (e n),
        ∀ x, i n (k x) = schwartzBruhatStageInclusion b d x := by
    let n := (hcof b).choose
    have h := schwartzBruhatStage_transition (hcof b).choose_spec d (e n)
    exact ⟨n, h.choose, fun x ↦ Subtype.ext (h.choose_spec.1 x)⟩
  refine isLFSpace_of_embedded_stages (X := fun n ↦ SchwartzBruhatStage (e n)) j i ?_ (fun n ↦ schwartzBruhatStage_isEmbedding _ _)
    (fun n ↦ elementarySchwartz_isFrechet)
  refine ⟨fun n ↦ (schwartzBruhatStage_isEmbedding (a n) (e n)).injective,
    fun n ↦ ContinuousLinearMap.ext (fun x ↦ Subtype.ext (hj n x)), ?_, ?_⟩
  · intro x
    exact ((mem_schwartzBruhatSubmodule_iff x.val).mp x.property).elim fun b hb ↦
      hb.elim fun d hd ↦ hd.elim fun v hv ↦ (hFac b d).elim fun n hn ↦ hn.elim fun k hk ↦
        ⟨n, k v, (hk v).trans (Subtype.ext hv)⟩
  · apply congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology)
    funext p
    exact propext ⟨fun h n ↦ h (a n) (e n), fun h b d ↦ by
      exact (hFac b d).elim fun n hn ↦ hn.elim fun k hk ↦
        ((h n).comp k.continuous).congr fun x ↦ congrArg p (hk x)⟩

omit hK hHaarK hRegularK hBorel hTop hT2 hLC in
/-- Apply the LF open mapping theorem to a map represented by a continuous linear surjection. -/
private theorem quotientMap_of_LF_surjection {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [AddCommGroup F]
    [Module ℂ F] [TopologicalSpace F] (hE : IsLFSpace E) (hF : IsLFSpace F)
    (f : E → F) (hf : ∃ P : E →L[ℂ] F, ∀ x, P x = f x) (hs : Function.Surjective f) :
    IsQuotientMap f := by
  obtain ⟨P, hP⟩ := hf
  have heq : ⇑P = f := funext hP
  subst f
  obtain ⟨_, X, _, _, _, hX, j, i, h⟩ := hE
  exact (isOpenMap_of_surjective_toLF hF hX i (fun n ↦ by
    rintro _ ⟨v, rfl⟩
    exact ⟨j n v, DFunLike.congr_fun (h.compatible n) v⟩) h.exhaustive P hs).isQuotientMap
      P.continuous hs

/-- Paper: Theorem D.1.7.1(2), p. 776. Under second countability the coset
integral is a topological quotient map. -/
theorem schwartzBruhatCosetIntegral_isQuotientMap [SecondCountableTopology G] :
    IsQuotientMap (schwartzBruhatCosetIntegral K μK hK) := by
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  let : ContinuousSMul ℂ (SchwartzBruhat G) := (withGeneratingSeminorms_spec _ _).continuousSMul
  exact quotientMap_of_LF_surjection (schwartzBruhat_isLF (G := G))
    (schwartzBruhat_isLF (G := G ⧸ K)) _ (schwartzBruhatCosetIntegral_continuousLinear K μK hK)
    (schwartzBruhatCosetIntegral_surjective K μK hK)

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

section ElementaryTests

omit hTop hT2 hLC

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- A compactly supported function smooth on every fiber has finite weighted partials. -/
private theorem elementarySchwartz_of_compactSupport {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) (hc : HasCompactSupport f) :
    f ∈ elementarySchwartzSubmodule m n r F := by
  classical
  refine ⟨hf, fun i ↦ ?_⟩
  let E := EuclideanSpace ℝ (Fin m)
  let N := EuclideanSpace ℝ (Fin n)
  let T := Fin n → AddCircle (1 : ℝ)
  let Z := Fin r → ℤ
  let q (v : N) : T := fun j ↦ (v j : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q := (IsOpenQuotientMap.piMap
    (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  let lift (t : T) := hq.surjective.hasRightInverse.choose t
  have hl (t : T) : q (lift t) = t := hq.surjective.hasRightInverse.choose_spec t
  let d (y : ElementaryLieGroup m n r F) := elementaryPartial f i.2.1 i.2.2.1
    (y.1, lift y.2.1) y.2.2.1 y.2.2.2
  have hd (v : E × N) (z : Z) (b : F) :
      d (elementaryCover v z b) = elementaryPartial f i.2.1 i.2.2.1 v z b := by
    apply (elementaryPartial_descends _ _ _ _ _ (hf z b)).2
    exact Prod.ext rfl (Prod.ext (hl (q v.2)) rfl)
  have hdc : Continuous d := by
    apply (Homeomorph.prodAssoc E T (Z × F)).isQuotientMap.continuous_iff.mpr
    apply continuous_prod_of_discrete_right.mpr
    intro z
    apply (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff.mp
    exact ((elementaryPartial_descends _ _ _ _ _ (hf z.1 z.2)).1.continuous).congr
      (fun w ↦ (hd w z.1 z.2).symm)
  have hdz {y : ElementaryLieGroup m n r F} (hy : y ∉ tsupport f) : d y = 0 := by
    let v : E × N := (y.1, lift y.2.1)
    let p (w : E × N) := elementaryCover w y.2.2.1 y.2.2.2
    have hp : Continuous p := continuous_fst.prodMk ((hq.continuous.comp continuous_snd).prodMk continuous_const)
    have hpv : p v = y := Prod.ext rfl (Prod.ext (hl y.2.1) rfl)
    have hv : v ∉ tsupport (f ∘ p) := fun hv ↦ hy (hpv ▸ tsupport_comp_subset_preimage f hp hv)
    have h0 (j : ℕ) : iteratedFDeriv ℝ j (f ∘ p) v = 0 := by
      by_contra hn
      exact hv (support_iteratedFDeriv_subset j hn)
    dsimp only [d, elementaryPartial]
    change (iteratedFDeriv ℝ _ (f ∘ p) v) _ = 0
    rw [h0]
    rfl
  let w (y : ElementaryLieGroup m n r F) : ℂ :=
    ((∏ j, (y.1 j : ℂ) ^ i.1 j) * (∏ j, (y.2.2.1 j : ℂ) ^ i.2.2.2 j)) * d y
  have hw : Continuous w := by
    apply Continuous.mul _ hdc
    apply Continuous.mul
    · fun_prop
    · exact (continuous_of_discreteTopology (f := fun z : Z ↦ ∏ j, (z j : ℂ) ^ i.2.2.2 j)).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hwK : HasCompactSupport w := HasCompactSupport.intro hc fun y hy ↦ by simp [w, hdz hy]
  obtain ⟨C,hC⟩ := hw.bounded_above_of_compact_support hwK
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun v ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  have h := hC (elementaryCover v a b)
  dsimp only [w] at h
  rw [hd] at h
  exact h

/-- Embed the real and torus factors in a vector space and localize a bump on one discrete fiber. -/
private theorem elementarySchwartz_exists_test {U : Set (ElementaryLieGroup m n r F)}
    (hU : IsOpen U) (x : ElementaryLieGroup m n r F) (hx : x ∈ U) :
    ∃ f : ElementarySchwartz m n r F, tsupport f.val ⊆ U ∧ f x = 1 := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let T := Fin n → AddCircle (1 : ℝ)
  let W := Fin n → ℂ
  let emb (p : E × T) : E × W := (p.1, fun j ↦ (AddCircle.toCircle (p.2 j) : ℂ))
  have ht : IsClosedEmbedding (fun t : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle t : ℂ)) :=
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).isClosedEmbedding
      (Subtype.val_injective.comp (AddCircle.injective_toCircle one_ne_zero)))
  have he : IsClosedEmbedding emb := IsClosedEmbedding.id.prodMap (IsClosedEmbedding.piMap fun _ ↦ ht)
  let inc (p : E × T) : ElementaryLieGroup m n r F := (p.1,p.2,x.2.2.1,x.2.2.2)
  have hi : Continuous inc := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let t : E × T := (x.1,x.2.1)
  have hn : inc ⁻¹' U ∈ 𝓝 t := (hU.preimage hi).mem_nhds hx
  rw [he.isInducing.nhds_eq_comap] at hn
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hn
  obtain ⟨g,hg,hgc,hgs,-,hgx⟩ := exists_contDiff_tsupport_subset (n := ⊤) hV
  let f (y : ElementaryLieGroup m n r F) : ℂ :=
    if y.2.2 = x.2.2 then g (emb (y.1,y.2.1)) else 0
  let K := inc '' (emb ⁻¹' tsupport g)
  have hK : IsCompact K := (he.isCompact_preimage hgc).image hi
  have hS : tsupport f ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases hz : y.2.2 = x.2.2
    · refine ⟨(y.1,y.2.1), subset_tsupport g (fun h ↦ hy (by simp [f,hz,h])), ?_⟩
      exact Prod.ext rfl (Prod.ext rfl hz.symm)
    · exact (hy (by simp [f,hz])).elim
  have hsm (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (fun w ↦ f (elementaryCover w a b)) := by
    by_cases hz : (a,b) = x.2.2
    · change ContDiff ℝ ∞ (fun w ↦ if (a,b) = x.2.2 then _ else _)
      simp only [hz, ite_true]
      apply Complex.ofRealCLM.contDiff.comp
      apply hgs.comp
      apply ContDiff.prodMk contDiff_fst
      apply contDiff_pi.mpr
      intro j
      simp only [elementaryCover, AddCircle.toCircle_apply_mk,Circle.coe_exp]
      apply ContDiff.cexp
      apply ContDiff.mul _ contDiff_const
      apply Complex.ofRealCLM.contDiff.comp
      apply ContDiff.mul contDiff_const
      exact ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin n ↦ ℝ) j).contDiff).comp contDiff_snd
    · simpa only [f,elementaryCover,hz,ite_false] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E × EuclideanSpace ℝ (Fin n) ↦ (0 : ℂ)))
  refine ⟨⟨f, elementarySchwartz_of_compactSupport hsm (hK.of_isClosed_subset isClosed_closure hS)⟩,
    hS.trans ?_, ?_⟩
  · rintro _ ⟨p,hp,rfl⟩
    exact hVU (hg hp)
  · change f x = 1
    simpa [f,t] using congrArg Complex.ofReal hgx

end ElementaryTests

/-- Choose a structural quotient with a neighborhood whose entire lifted fiber lies in the given open set. -/
private theorem exists_stage_open_over {U : Set G} (hU : IsOpen U) {x : G} (hx : x ∈ U) :
    ∃ (a : BruhatStructuralPair G) (y : a.val.1) (V : Set a.quotient), y.val = x ∧
      IsOpen V ∧ QuotientGroup.mk y ∈ V ∧ ∀ t : a.val.1, QuotientGroup.mk t ∈ V → t.val ∈ U := by
  have hN : (fun z : G ↦ x*z) ⁻¹' U ∈ 𝓝 1 :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  obtain ⟨W, hW, h1, hWW⟩ := exists_open_nhds_one_split hN
  obtain ⟨H,hH⟩ := exists_lcaDualAnnihilator_subset_nhds (hW.mem_nhds h1)
  let k := lcaDualAnnihilator H.val
  have hγ := lca_dualSubgroup_quotient H
  have hkc : IsCompact (k : Set G) := by
    change IsCompact (lcaDualAnnihilator H.val : Set G)
    rw [← hγ.choose_spec.2.2.1]
    exact hγ.choose_spec.2.2.2
  have hk : IsBruhatGoodSubgroup k := by
    refine ⟨hkc.isClosed, ?_⟩
    change IsOpen (lcaAnnihilator (lcaDualAnnihilator H.val) : Set (PontryaginDual G)) ∧ _
    rw [lcaAnnihilator_dualAnnihilator_of_open H.val H.property.1]
    exact H.property
  obtain ⟨a, hak, hxa⟩ := exists_bruhatStructuralPair_mem k hk x
  let y : a.val.1 := ⟨x,hxa⟩
  let B : Set a.val.1 := (fun z : a.val.1 ↦ x⁻¹ * z.val) ⁻¹' W
  let V : Set a.quotient := QuotientGroup.mk '' B
  have hB : IsOpen B := hW.preimage (continuous_const.mul continuous_subtype_val)
  refine ⟨a, y, V, rfl, QuotientGroup.isOpenMap_coe B hB, mem_image_of_mem _ (show y ∈ B by simpa [B,y] using h1), ?_⟩
  intro t ht
  obtain ⟨v,hv,he⟩ := ht
  have hker := QuotientGroup.eq.mp he
  have ht' : v.val⁻¹ * t.val ∈ k := by
    rw [← hak]
    exact hker
  simpa only [Set.mem_preimage, inv_mul_cancel_left, mul_inv_cancel_left, ← mul_assoc, mul_inv_cancel, one_mul]
    using hWW (x⁻¹ * v.val) hv _ (hH ht')

/-- Lift an elementary test supported in a small quotient neighborhood and extend it by zero. -/
private theorem schwartzBruhat_exists_test {U : Set G} (hU : IsOpen U) {x : G} (hx : x ∈ U) :
    ∃ f : SchwartzBruhat G, tsupport f.val ⊆ U ∧ f x = 1 := by
  classical
  obtain ⟨a, y, V, hyx, hV, hyV, hVU⟩ := exists_stage_open_over (U := U) (x := x) hU hx
  let e := Classical.choice a.elementary
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let h : a.quotient ≃ₜ E := e.equiv.toHomeomorph.trans ⟨Multiplicative.toAdd, continuous_toAdd, continuous_ofAdd⟩
  let q : a.val.1 → a.quotient := QuotientGroup.mk
  have hV' : IsOpen (h.symm ⁻¹' V) := hV.preimage h.symm.continuous
  have hyV' : h (q y) ∈ h.symm ⁻¹' V := by simpa only [mem_preimage, h.symm_apply_apply] using hyV
  obtain ⟨s, hs, hsy⟩ := elementarySchwartz_exists_test hV' _ hyV'
  let f : SchwartzBruhat G := schwartzBruhatStageInclusion a e s
  let L : Set G := Subtype.val '' ((h ∘ q) ⁻¹' tsupport s.val)
  have hc : IsClosed L := (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_tsupport s.val |>.preimage (h.continuous.comp QuotientGroup.continuous_mk))
  refine ⟨f, (closure_minimal (t := L) ?_ hc).trans ?_, ?_⟩
  · intro z hz
    change schwartzBruhatStageRealization a e s z ≠ 0 at hz
    rw [schwartzBruhatStageRealization_apply] at hz
    split_ifs at hz with hzJ
    · exact ⟨⟨z,hzJ⟩, subset_tsupport s.val hz, rfl⟩
    · exact (hz rfl).elim
  · rintro _ ⟨t,ht,rfl⟩
    have hmem := hs ht
    exact hVU t (by simpa only [mem_preimage,Function.comp_apply,h.symm_apply_apply] using hmem)
  · rw [← hyx]
    change schwartzBruhatStageRealization a e s (y : G) = 1
    rw [schwartzBruhatStageRealization_apply,dite_eq_left y.property]
    exact hsy

/-- Paper: Definition D.1.8.2, p. 779. Point evaluation vanishes precisely off
the evaluation point and has singleton support.
Deviation: Sanity check on both the vanishing locus and the support. -/
theorem schwartzBruhat_dirac_support (x : G) :
    ∃ δ : StrongDual ℂ (SchwartzBruhat G),
      (∀ f, δ f = f x) ∧
      schwartzBruhatVanishingLocus δ = {x}ᶜ ∧ schwartzBruhatDistributionSupport δ = {x} :=
by
  classical
  let ev : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp ev
  let idx : {p : Seminorm ℂ (schwartzBruhatSubmodule G) // ∀ a e, Continuous (p ∘ schwartzBruhatStageInclusion a e)} :=
    ⟨p, fun a e ↦ by
      change Continuous ((normSeminorm ℂ ℂ).comp (ev.comp (schwartzBruhatStageInclusion a e)))
      apply Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0))
      intro f
      change ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f
      rw [schwartzBruhatStageRealization_apply]
      split_ifs
      · change (‖f _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
        apply ENNReal.toReal_mono (f.property.2 _).ne
        rw [elementarySchwartzBound_zero]
        exact le_iSup (fun y ↦ (‖f y‖₊ : ENNReal)) _
      · exact norm_zero.trans_le (apply_nonneg _ _)⟩
  let δ : StrongDual ℂ (SchwartzBruhat G) := ⟨ev,
    (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp ev
      fun _ ↦ (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm idx⟩
  have hδ : schwartzBruhatVanishingLocus δ = {x}ᶜ := by
    ext y
    constructor
    · rintro ⟨U, ⟨hU,hkill⟩,hy⟩ rfl
      obtain ⟨f,hf,hfx⟩ := schwartzBruhat_exists_test hU hy
      exact one_ne_zero (α := ℂ) (hfx.symm.trans (hkill f hf))
    · intro hy
      refine ⟨{x}ᶜ, ⟨isClosed_singleton.isOpen_compl, ?_⟩, hy⟩
      intro f hf
      change f x = 0
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hf h (mem_singleton x))
  exact ⟨δ, fun _ ↦ rfl, hδ, by rw [schwartzBruhatDistributionSupport, hδ, compl_compl]⟩

section TensorSupports

omit hTop hT2 hLC

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Compact support descends from a realization to its elementary test. -/
private theorem stage_compact_of_realization (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (h : HasCompactSupport (schwartzBruhatStageRealization a e s)) :
    HasCompactSupport s.val := by
  let R := schwartzBruhatStageRealization a e s
  let ψ (x : a.val.1) := (e.equiv (QuotientGroup.mk x)).toAdd
  have hψ : Continuous ψ := continuous_toAdd.comp (e.equiv.continuous.comp QuotientGroup.continuous_mk)
  have hc : IsCompact (Subtype.val ⁻¹' tsupport R : Set a.val.1) :=
    (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage h
  apply HasCompactSupport.intro (hc.image hψ)
  intro y hy
  obtain ⟨x,hx⟩ := QuotientGroup.mk_surjective (e.equiv.symm (Multiplicative.ofAdd y))
  have hxy : ψ x = y := congrArg Multiplicative.toAdd ((congrArg e.equiv hx).trans (e.equiv.apply_symm_apply _))
  have hx' : x.val ∉ tsupport R := fun hh ↦ hy ⟨x,hh,hxy⟩
  have he := schwartzBruhatStageRealization_apply a e s x.val
  rw [dite_eq_left x.property] at he
  exact hxy ▸ he.symm.trans (image_eq_zero_of_notMem_tsupport hx')

/-- Multiplication by a compactly supported elementary test is continuous by point evaluation. -/
private theorem elementarySchwartz_compactMultiplier {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (u : ElementarySchwartz m n r F) (hu : HasCompactSupport u.val) :
    ∃ M : ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m n r F, ∀ f x, M f x = u x * f x := by
  let E := ElementarySchwartz m n r F
  let M : E →ₗ[ℂ] E :=
    { toFun := fun f ↦ ⟨fun x ↦ u x * f x, elementarySchwartz_of_compactSupport
        (fun a b ↦ (u.property.1 a b).mul (f.property.1 a b)) (hu.mul_right (f' := f.val))⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ mul_add (u x) (f x) (g x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ mul_left_comm (u x) c (f x)) }
  let : BarrelledSpace ℂ E := elementarySchwartz_barrelled
  let : ContinuousSMul ℂ E := elementarySchwartz_withSeminorms.continuousSMul
  have hM : Continuous M := by
    apply continuous_toElementarySchwartz_of_eval
    intro x
    let ev : E →L[ℂ] ℂ := ⟨(LinearMap.proj x).comp (elementarySchwartzSubmodule m n r F).subtype,
      elementarySchwartz_continuousEval.comp (continuous_id.prodMk continuous_const)⟩
    exact ⟨u x • ev,fun _ ↦ rfl⟩
  exact ⟨⟨M,hM⟩,fun _ _ ↦ rfl⟩

private theorem stageRealization_mul (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (u v w : SchwartzBruhatStage e) (h : ∀ y, w y = u y * v y) (x : G) :
    schwartzBruhatStageRealization a e w x = schwartzBruhatStageRealization a e u x * schwartzBruhatStageRealization a e v x := by
  simp only [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact h _
  · exact (zero_mul _).symm

private theorem schwartzBruhat_compactMultiplier_pair (u : SchwartzBruhat G) (hu : HasCompactSupport u.val)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (c : BruhatStructuralPair G) (t : ElementaryLCAPresentation c.quotient)
    (v : SchwartzBruhatStage t) (hv : schwartzBruhatStageRealization c t v = u.val)
    (i : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage t)
    (hi : ∀ f, schwartzBruhatStageRealization c t (i f) = schwartzBruhatStageRealization a e f) :
    ∃ A : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G, ∀ f x, A f x = u x * schwartzBruhatStageRealization a e f x := by
  have hcomp := stage_compact_of_realization c t v (hv.symm ▸ hu)
  let M := (elementarySchwartz_compactMultiplier v hcomp).choose
  have hM := (elementarySchwartz_compactMultiplier v hcomp).choose_spec
  let k : SchwartzBruhatStage t →L[ℂ] SchwartzBruhat G := ⟨schwartzBruhatStageInclusion c t,
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property c t⟩
  refine ⟨k.comp (M.comp i), fun f x ↦ ?_⟩
  change schwartzBruhatStageRealization c t (M (i f)) x = _
  exact (stageRealization_mul c t v (i f) (M (i f)) (hM (i f)) x).trans
    (congrArg₂ (·*·) (congrFun hv x) (congrFun (hi f) x))

/-- A common structural stage realizes the product with a fixed compactly supported test. -/
private theorem schwartzBruhat_compactMultiplier_stage (u : SchwartzBruhat G) (hu : HasCompactSupport u.val)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∃ A : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G, ∀ f x, A f x = u x * schwartzBruhatStageRealization a e f x := by
  classical
  refine ((mem_schwartzBruhatSubmodule_iff u.val).mp u.property).elim fun b hb ↦ hb.elim fun d hd ↦ hd.elim fun v hv ↦ ?_
  let : IsDirectedOrder (BruhatStructuralPair G) := bruhatStructuralPair_filtered.2
  refine (exists_ge_ge a b).elim fun c hc ↦ ?_
  let t := Classical.choice c.elementary
  refine (schwartzBruhatStage_transition hc.1 e t).elim fun i hi ↦ ?_
  refine (schwartzBruhatStage_transition hc.2 d t).elim fun j hj ↦ ?_
  exact schwartzBruhat_compactMultiplier_pair u hu a e c t (j v) ((hj.1 v).trans hv) i hi.1

/-- Compactly supported Schwartz functions act continuously by multiplication on all stages. -/
private theorem schwartzBruhat_compactMultiplier (u : SchwartzBruhat G) (hu : HasCompactSupport u.val) :
    ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f x, M f x = u x * f x := by
  classical
  choose A hA using schwartzBruhat_compactMultiplier_stage u hu
  have hmem (f : SchwartzBruhat G) : u.val * f.val ∈ schwartzBruhatSubmodule G := by
    obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    have h : (A a e s).val = u.val * f.val := funext fun x ↦ (hA a e s x).trans (congrArg (u x * ·) (congrFun hs x))
    exact h ▸ (A a e s).property
  let M : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G :=
    { toFun := fun f ↦ ⟨u.val * f.val,hmem f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ mul_add (u x) (f x) (g x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ mul_left_comm (u x) c (f x)) }
  have hM : Continuous M := by
    let P : SeminormFamily ℂ (SchwartzBruhat G) {q : Seminorm ℂ (SchwartzBruhat G) //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine hP.continuous_of_continuous_comp M fun p ↦ hP.continuous_seminorm ⟨p.val.comp M,fun a e ↦ ?_⟩
    exact ((hP.continuous_seminorm p).comp (A a e).continuous).congr fun s ↦
      congrArg p.val (Subtype.ext (funext (hA a e s)))
  exact ⟨⟨M,hM⟩,fun _ _ ↦ rfl⟩

private theorem compact_schwartzBruhat_comp {f : SchwartzBruhat G} (hc : HasCompactSupport f.val)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (h0 : φ 0 = 0) :
    ∃ u : SchwartzBruhat G, u.val = φ ∘ f.val := by
  obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  have hsc := stage_compact_of_realization a e s (hs.symm ▸ hc)
  let v : SchwartzBruhatStage e := ⟨φ ∘ s.val, elementarySchwartz_of_compactSupport
    (fun j b ↦ hφ.comp (s.property.1 j b)) (hsc.comp_left h0)⟩
  refine ⟨schwartzBruhatStageInclusion a e v,funext fun x ↦ ?_⟩
  change schwartzBruhatStageRealization a e v x = φ (f x)
  rw [← congrFun hs x,schwartzBruhatStageRealization_apply,schwartzBruhatStageRealization_apply]
  split_ifs
  · rfl
  · exact h0.symm

/-- A compactly supported Schwartz test can be chosen equal to one on a neighborhood. -/
private theorem schwartzBruhat_exists_local_unit {x : G} {U : Set G} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ u : SchwartzBruhat G, HasCompactSupport u.val ∧ tsupport u.val ⊆ U ∧ u.val =ᶠ[𝓝 x] 1 := by
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨f,hf,hfx⟩ := schwartzBruhat_exists_test (hU.inter isOpen_interior) ⟨hx,mem_interior_iff_mem_nhds.mpr hxK⟩
  have hcf : HasCompactSupport f.val := hK.of_isClosed_subset isClosed_closure
    (hf.trans (inter_subset_right.trans interior_subset))
  let g : ContDiffBump (1 : ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have h0 : g 0 = 0 := g.zero_of_le_dist (by norm_num [g])
  let φ (z : ℂ) : ℂ := g z
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp g.contDiff
  have hφ0 : φ 0 = 0 := by simp [φ,h0]
  obtain ⟨u,hu⟩ := compact_schwartzBruhat_comp hcf hφ hφ0
  have hsubset : tsupport u.val ⊆ tsupport f.val := by
    rw [hu]
    exact tsupport_comp_subset hφ0 _
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous f
  have hc : Tendsto f.val (𝓝 x) (𝓝 1) := (b.continuous.congr hb).tendsto' _ _ hfx
  refine ⟨u, hcf.of_isClosed_subset isClosed_closure hsubset, hsubset.trans (hf.trans inter_subset_left), ?_⟩
  filter_upwards [hc.eventually g.eventuallyEq_one] with y hy
  change u.val y = 1
  simp only [hu,Function.comp_apply,φ,show g (f y) = 1 from hy,Complex.ofReal_one]

/-- A continuous functional on a completed inductive tensor is determined by pure tensors. -/
private theorem completedTensor_ext_zero {X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (L : Z →L[ℂ] ℂ)
    (h : ∀ (x : X) (y : Y), L (e (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) = 0) :
    ∀ z, L z = 0 := by
  let j : InductiveTensor X Y →L[ℂ] Completion (InductiveTensor X Y) := Completion.toComplL
  let A : X ⊗[ℂ] Y →ₗ[ℂ] ℂ := L.toLinearMap.comp (e.toLinearEquiv.toLinearMap.comp j.toLinearMap)
  have hz : A = 0 := TensorProduct.ext' h
  intro z
  exact Completion.induction_on (p := fun u ↦ L (e u) = 0) (e.symm z)
    (isClosed_eq (L.continuous.comp e.continuous) continuous_const) (fun u ↦ LinearMap.congr_fun hz u)
    |> fun h ↦ (congrArg L (e.apply_symm_apply z)).symm.trans h

private def completedTensor_right {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (f : X) : Y →L[ℂ] Z :=
  let j : InductiveTensor X Y →L[ℂ] Completion (InductiveTensor X Y) := Completion.toComplL
  let hsp := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) // (∀ x : X, Continuous (fun y : Y ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  e.toContinuousLinearMap.comp (j.comp ⟨TensorProduct.mk ℂ X Y f,
    hsp.continuous_of_continuous_comp (TensorProduct.mk ℂ X Y f) fun p ↦ p.property.1 f⟩)

private theorem completedTensor_right_apply {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (f : X) (g : Y) :
    completedTensor_right (X := X) (Y := Y) e f g = e (Completion.coe' (α := InductiveTensor X Y) (f ⊗ₜ[ℂ] g)) := rfl

variable {G H I J : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I] [T2Space I]
  [LocallyCompactSpace I] [SecondCountableTopology I]
  [CommGroup J] [TopologicalSpace J] [IsTopologicalGroup J] [T2Space J]
  [LocallyCompactSpace J] [SecondCountableTopology J]

private theorem schwartzBruhat_product_tests :
    ∃ b : SchwartzBruhat G → SchwartzBruhat H →L[ℂ] SchwartzBruhat (G × H),
      (∀ f g x y, b f g (x,y) = f x * g y) ∧
      ∀ L : SchwartzBruhat (G × H) →L[ℂ] ℂ, (∀ f g, L (b f g) = 0) → ∀ s, L s = 0 := by
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun e he ↦ ?_
  let b := completedTensor_right (X := SchwartzBruhat G) (Y := SchwartzBruhat H) e
  have hb (f : SchwartzBruhat G) (g : SchwartzBruhat H) := completedTensor_right_apply e f g
  refine ⟨b,fun f g x y ↦ (congrArg (fun w : SchwartzBruhat (G × H) ↦ w (x,y)) (hb f g)).trans (he f g x y),?_⟩
  exact fun L h ↦ completedTensor_ext_zero (X := SchwartzBruhat G) (Y := SchwartzBruhat H) e L
    (fun f g ↦ (congrArg L (hb f g)).symm.trans (h f g))

/-- Iterating the binary kernel isomorphism gives products determining every continuous functional. -/
private theorem schwartzBruhat_fourfold_tests :
    ∃ b : SchwartzBruhat G → SchwartzBruhat H → SchwartzBruhat I → SchwartzBruhat J →
        SchwartzBruhat (G × H × I × J),
      (∀ f g s t x, b f g s t x = f x.1 * g x.2.1 * s x.2.2.1 * t x.2.2.2) ∧
      ∀ L : SchwartzBruhat (G × H × I × J) →L[ℂ] ℂ,
        (∀ f g s t, L (b f g s t) = 0) → ∀ u, L u = 0 := by
  refine (schwartzBruhat_product_tests (G := G) (H := H × I × J)).elim fun A hA ↦ ?_
  refine (schwartzBruhat_product_tests (G := H) (H := I × J)).elim fun B hB ↦ ?_
  refine (schwartzBruhat_product_tests (G := I) (H := J)).elim fun C hC ↦ ?_
  refine ⟨fun f g s t ↦ A f (B g (C s t)),fun f g s t x ↦ ?_,fun L h ↦ ?_⟩
  · rcases x with ⟨x,y,z,w⟩
    refine (hA.1 f (B g (C s t)) x _).trans ?_
    rw [hB.1,hC.1,mul_assoc,mul_assoc]
  · exact hA.2 L fun f ↦ hB.2 (L.comp (A f)) fun g ↦ hC.2 ((L.comp (A f)).comp (B g)) (h f g)

private theorem tsupport_fourfold {X Y Z A : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace A] {f : X → ℂ} {g : Y → ℂ} {h : Z → ℂ} {k : A → ℂ}
    {s : X × Y × Z × A → ℂ} (hs : ∀ x, s x = f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2) :
    tsupport s ⊆ tsupport f ×ˢ (tsupport g ×ˢ (tsupport h ×ˢ tsupport k)) := by
  apply closure_minimal _ ((isClosed_tsupport f).prod ((isClosed_tsupport g).prod ((isClosed_tsupport h).prod (isClosed_tsupport k))))
  intro x hx
  have hn : f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2 ≠ 0 := hs x ▸ hx
  rcases mul_ne_zero_iff.mp hn with ⟨h₃,h₄⟩
  rcases mul_ne_zero_iff.mp h₃ with ⟨h₂,h₃⟩
  rcases mul_ne_zero_iff.mp h₂ with ⟨h₁,h₂⟩
  exact ⟨subset_tsupport _ h₁,subset_tsupport _ h₂,subset_tsupport _ h₃,subset_tsupport _ h₄⟩

private theorem distribution_support_test (T : StrongDual ℂ (SchwartzBruhat G)) {x : G}
    (hx : x ∈ schwartzBruhatDistributionSupport T) {U : Set G} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ f : SchwartzBruhat G, tsupport f.val ⊆ U ∧ T f ≠ 0 := by
  by_contra! h
  exact hx ⟨U,⟨hU,h⟩,hxU⟩

variable (d₁ : StrongDual ℂ (SchwartzBruhat G)) (d₂ : StrongDual ℂ (SchwartzBruhat H))
  (d₃ : StrongDual ℂ (SchwartzBruhat I)) (d₄ : StrongDual ℂ (SchwartzBruhat J))
  (d : StrongDual ℂ (SchwartzBruhat (G × H × I × J)))
variable (b : SchwartzBruhat G → SchwartzBruhat H → SchwartzBruhat I → SchwartzBruhat J →
    SchwartzBruhat (G × H × I × J))
  (hb : ∀ f g s t (x : G × H × I × J), b f g s t x = f x.1 * g x.2.1 * s x.2.2.1 * t x.2.2.2)
  (hd : ∀ f g s t, d (b f g s t) = d₁ f * d₂ g * d₃ s * d₄ t)
  (hext : ∀ L : SchwartzBruhat (G × H × I × J) →L[ℂ] ℂ, (∀ f g s t, L (b f g s t) = 0) → ∀ u, L u = 0)

include hb hd in
/-- A rectangle around four support points contains a product of tests with nonzero pairing. -/
private theorem fourfold_product_subset_support :
    schwartzBruhatDistributionSupport d₁ ×ˢ (schwartzBruhatDistributionSupport d₂ ×ˢ
        (schwartzBruhatDistributionSupport d₃ ×ˢ schwartzBruhatDistributionSupport d₄)) ⊆
      schwartzBruhatDistributionSupport d := by
  rintro ⟨x,y,z,w⟩ ⟨hx,hy,hz,hw⟩ ⟨U,⟨hU,hkill⟩,hmem⟩
  obtain ⟨V₁,W,h₁,hx₁,hW,hW₀,hsub⟩ := mem_nhds_prod_iff'.mp (hU.mem_nhds hmem)
  obtain ⟨V₂,W',h₂,hy₂,hW',hW₀',hsub'⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hW₀)
  obtain ⟨V₃,V₄,h₃,hz₃,h₄,hw₄,hsub''⟩ := mem_nhds_prod_iff'.mp (hW'.mem_nhds hW₀')
  obtain ⟨f,hf,hnf⟩ := distribution_support_test d₁ hx h₁ hx₁
  obtain ⟨g,hg,hng⟩ := distribution_support_test d₂ hy h₂ hy₂
  obtain ⟨s,hs,hns⟩ := distribution_support_test d₃ hz h₃ hz₃
  obtain ⟨t,ht,hnt⟩ := distribution_support_test d₄ hw h₄ hw₄
  have hsup := tsupport_fourfold (hb f g s t)
  have h0 := hkill (b f g s t) (fun v hv ↦ hsub ⟨hf (hsup hv).1,hsub' ⟨hg (hsup hv).2.1,
    hsub'' ⟨hs (hsup hv).2.2.1,ht (hsup hv).2.2.2⟩⟩⟩)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hnf hng) hns) hnt ((hd f g s t).symm.trans h0)

private theorem tsupport_of_mul_left {X : Type*} [TopologicalSpace X] {u v w : X → ℂ}
    (h : ∀ x, w x = u x * v x) : tsupport w ⊆ tsupport u :=
  closure_mono fun x hx hx₀ ↦ hx ((h x).trans (by rw [hx₀,zero_mul]))

private theorem fourfold_mul_reorder (a b c d e f g h : ℂ) :
    (a*b*c*d)*(e*f*g*h) = (a*e)*(b*f)*(c*g)*(d*h) := by ring

include hb hext in
/-- Localizing each factor by a cutoff transfers vanishing from pure products to all nearby tests. -/
private theorem fourfold_vanish_on_rectangle {p : G × H × I × J}
    {U₁ : Set G} {U₂ : Set H} {U₃ : Set I} {U₄ : Set J}
    (h₁ : IsOpen U₁) (h₂ : IsOpen U₂) (h₃ : IsOpen U₃) (h₄ : IsOpen U₄)
    (hp : p ∈ U₁ ×ˢ (U₂ ×ˢ (U₃ ×ˢ U₄)))
    (hkill : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (s : SchwartzBruhat I) (t : SchwartzBruhat J), tsupport (f : G → ℂ) ⊆ U₁ → tsupport (g : H → ℂ) ⊆ U₂ →
        tsupport (s : I → ℂ) ⊆ U₃ → tsupport (t : J → ℂ) ⊆ U₄ → d (b f g s t) = 0) :
    p ∈ schwartzBruhatVanishingLocus d := by
  obtain ⟨v₁,hc₁,hv₁,he₁⟩ := schwartzBruhat_exists_local_unit h₁ hp.1
  obtain ⟨v₂,hc₂,hv₂,he₂⟩ := schwartzBruhat_exists_local_unit h₂ hp.2.1
  obtain ⟨v₃,hc₃,hv₃,he₃⟩ := schwartzBruhat_exists_local_unit h₃ hp.2.2.1
  obtain ⟨v₄,hc₄,hv₄,he₄⟩ := schwartzBruhat_exists_local_unit h₄ hp.2.2.2
  let v := b v₁ v₂ v₃ v₄
  have hvc : HasCompactSupport v.val := (hc₁.prod (hc₂.prod (hc₃.prod hc₄))).of_isClosed_subset
    isClosed_closure (tsupport_fourfold (hb v₁ v₂ v₃ v₄))
  let M := (schwartzBruhat_compactMultiplier v hvc).choose
  have hM := (schwartzBruhat_compactMultiplier v hvc).choose_spec
  have hkill' : ∀ f g s t, d (M (b f g s t)) = 0 := by
    intro f g s t
    let M₁ := schwartzBruhat_compactMultiplier v₁ hc₁
    let M₂ := schwartzBruhat_compactMultiplier v₂ hc₂
    let M₃ := schwartzBruhat_compactMultiplier v₃ hc₃
    let M₄ := schwartzBruhat_compactMultiplier v₄ hc₄
    have hEq : M (b f g s t) = b (M₁.choose f) (M₂.choose g) (M₃.choose s) (M₄.choose t) := by
      apply Subtype.ext
      funext x
      change M (b f g s t) x = _
      refine ((hM _ x).trans (congrArg₂ (·*·) (hb v₁ v₂ v₃ v₄ x) (hb f g s t x))).trans ?_
      refine (fourfold_mul_reorder ..).trans (Eq.trans ?_ (hb _ _ _ _ x).symm)
      exact congrArg₂ (·*·) (congrArg₂ (·*·) (congrArg₂ (·*·)
        (M₁.choose_spec f x.1).symm (M₂.choose_spec g x.2.1).symm)
        (M₃.choose_spec s x.2.2.1).symm) (M₄.choose_spec t x.2.2.2).symm
    apply (congrArg d hEq).trans
    exact hkill (M₁.choose f) (M₂.choose g) (M₃.choose s) (M₄.choose t) ((tsupport_of_mul_left (M₁.choose_spec f)).trans hv₁)
      ((tsupport_of_mul_left (M₂.choose_spec g)).trans hv₂)
      ((tsupport_of_mul_left (M₃.choose_spec s)).trans hv₃)
      ((tsupport_of_mul_left (M₄.choose_spec t)).trans hv₄)
  have hall := hext (d.comp M) hkill'
  have hone : v.val =ᶠ[𝓝 p] 1 := by
    filter_upwards [continuous_fst.continuousAt.eventually he₁,
      (continuous_fst.comp continuous_snd).continuousAt.eventually he₂,
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually he₃,
      (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually he₄] with x h₁ h₂ h₃ h₄
    change b v₁ v₂ v₃ v₄ x = 1
    change v₁ x.1 = 1 at h₁
    change v₂ x.2.1 = 1 at h₂
    change v₃ x.2.2.1 = 1 at h₃
    change v₄ x.2.2.2 = 1 at h₄
    simp only [hb,h₁,h₂,h₃,h₄,one_mul]
  obtain ⟨W,hW,hWo,hpW⟩ := mem_nhds_iff.mp hone
  refine ⟨W,⟨hWo,fun f hf ↦ ?_⟩,hpW⟩
  have he : M f = f := by
    apply Subtype.ext
    funext x
    change M f x = f x
    rw [hM]
    by_cases hx : x ∈ tsupport f.val
    · rw [show v x = 1 from hW (hf hx),one_mul]
    · rw [show f x = 0 from image_eq_zero_of_notMem_tsupport hx,mul_zero]
  exact (congrArg d he).symm.trans (hall f)

private theorem fourfold_mul_zero_d {a b c d : ℂ} (h : d = 0) : a*b*c*d = 0 := by simp [h]

private theorem fourfold_mul_zero_c {a b c d : ℂ} (h : c = 0) : a*b*c*d = 0 := by simp [h]

private theorem fourfold_mul_zero_b {a b c d : ℂ} (h : b = 0) : a*b*c*d = 0 := by simp [h]

private theorem fourfold_mul_zero_a {a b c d : ℂ} (h : a = 0) : a*b*c*d = 0 := by simp [h]


include hb hd hext in
private theorem fourfold_support_subset_product :
    schwartzBruhatDistributionSupport d ⊆ (schwartzBruhatDistributionSupport d₁ ×ˢ
      (schwartzBruhatDistributionSupport d₂ ×ˢ (schwartzBruhatDistributionSupport d₃ ×ˢ
        schwartzBruhatDistributionSupport d₄))) := by
  intro p hp
  have hv {U₁ U₂ U₃ U₄} (h₁ : IsOpen U₁) (h₂ : IsOpen U₂) (h₃ : IsOpen U₃) (h₄ : IsOpen U₄)
      (h : p ∈ U₁ ×ˢ (U₂ ×ˢ (U₃ ×ˢ U₄))) :
      ¬ (∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (s : SchwartzBruhat I) (t : SchwartzBruhat J), tsupport (f : G → ℂ) ⊆ U₁ → tsupport (g : H → ℂ) ⊆ U₂ →
        tsupport (s : I → ℂ) ⊆ U₃ → tsupport (t : J → ℂ) ⊆ U₄ → d (b f g s t) = 0) :=
    fun hkill ↦ hp (fourfold_vanish_on_rectangle d b hb hext h₁ h₂ h₃ h₄ h hkill)
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv hU isOpen_univ isOpen_univ isOpen_univ ⟨hx,trivial,trivial,trivial⟩
      fun f g s t hf _ _ _ ↦ (hd f g s t).trans (fourfold_mul_zero_a (hkill f hf))
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv isOpen_univ hU isOpen_univ isOpen_univ ⟨trivial,hx,trivial,trivial⟩
      fun f g s t _ hg _ _ ↦ (hd f g s t).trans (fourfold_mul_zero_b (hkill g hg))
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv isOpen_univ isOpen_univ hU isOpen_univ ⟨trivial,trivial,hx,trivial⟩
      fun f g s t _ _ hs _ ↦ (hd f g s t).trans (fourfold_mul_zero_c (hkill s hs))
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv isOpen_univ isOpen_univ isOpen_univ hU ⟨trivial,trivial,trivial,hx⟩
      fun f g s t _ _ _ ht ↦ (hd f g s t).trans (fourfold_mul_zero_d (hkill t ht))

private theorem distribution_eval_of_pointwise {X : Type*} [CommGroup X] [TopologicalSpace X]
    (T : StrongDual ℂ (SchwartzBruhat X)) (v : SchwartzBruhat X) {u : X → ℂ} {c : ℂ}
    (hv : ∀ x, v x = u x) (h : ∃ w : SchwartzBruhat X, (∀ x, w x = u x) ∧ T w = c) :
    T v = c :=
  h.elim fun _w hw ↦ (congrArg T (Subtype.ext (funext fun x ↦ (hv x).trans (hw.1 x).symm))).trans hw.2

private theorem fourfold_distribution_support
    (h : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (s : SchwartzBruhat I) (t : SchwartzBruhat J),
      ∃ v : SchwartzBruhat (G × H × I × J),
        (∀ x, v x = f x.1 * g x.2.1 * s x.2.2.1 * t x.2.2.2) ∧
          d v = d₁ f * d₂ g * d₃ s * d₄ t) :
    schwartzBruhatDistributionSupport d = (schwartzBruhatDistributionSupport d₁ ×ˢ
      (schwartzBruhatDistributionSupport d₂ ×ˢ (schwartzBruhatDistributionSupport d₃ ×ˢ
        schwartzBruhatDistributionSupport d₄))) := by
  refine (schwartzBruhat_fourfold_tests (G := G) (H := H) (I := I) (J := J)).elim fun B hB ↦ ?_
  have hpair (f g s t) : d (B f g s t) = d₁ f * d₂ g * d₃ s * d₄ t :=
    distribution_eval_of_pointwise d (B f g s t) (hB.1 f g s t) (h f g s t)
  exact Subset.antisymm (fourfold_support_subset_product d₁ d₂ d₃ d₄ d B hB.1 hpair hB.2)
    (fourfold_product_subset_support d₁ d₂ d₃ d₄ d B hB.1 hpair)

end TensorSupports

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
  by
    intro R T Z A d₁ d₂ d₃ d₄ d h
    exact fourfold_distribution_support (G := R) (H := T) (I := Z) (J := A) d₁ d₂ d₃ d₄ d h

open Classical in
/-- Compose the inverse elementary identification with the canonical stage inclusion. -/
private theorem schwartzBruhatStageLift_of_equiv (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (I : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhat a.quotient)
    (hI : ∀ f (x : a.quotient), I f x = f (e.equiv x).toAdd) :
    ∃ j : SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G, ∀ (f : SchwartzBruhat a.quotient) (x : G),
      j f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x,hx⟩ : a.quotient) else 0 := by
  classical
  let j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G := ⟨schwartzBruhatStageInclusion a e,
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property a e⟩
  refine ⟨j.comp I.symm.toContinuousLinearMap, fun f x ↦ ?_⟩
  change schwartzBruhatStageRealization a e (I.symm f) x = _
  refine (schwartzBruhatStageRealization_apply a e (I.symm f) x).trans ?_
  apply congrArg (fun u : x ∈ a.val.1 → ℂ ↦ dite (x ∈ a.val.1) u (fun _ ↦ 0))
  funext hx
  let y : a.quotient := QuotientGroup.mk (⟨x,hx⟩ : a.val.1)
  have he : I (I.symm f) y = f y :=
    congrArg (fun z : SchwartzBruhat a.quotient ↦ z y) (I.apply_symm_apply f)
  exact (hI (I.symm f) y).symm.trans he

open Classical in
/-- Pull back a Schwartz function on the structural quotient and extend it by zero. -/
private theorem schwartzBruhatStageLift (a : BruhatStructuralPair G) :
    ∃ j : SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G, ∀ (f : SchwartzBruhat a.quotient) (x : G),
      j f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x,hx⟩ : a.quotient) else 0 := by
  classical
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let e := Classical.choice a.elementary
  exact (elementarySchwartz_equiv_schwartzBruhat e).elim fun I hI ↦ schwartzBruhatStageLift_of_equiv a e I hI

open Classical in
/-- The closed subgroup contains the support of the lift over the closed support downstairs. -/
private theorem schwartzBruhatStageLift_tsupport (a : BruhatStructuralPair G) (f : SchwartzBruhat a.quotient)
    (g : SchwartzBruhat G) (hg : ∀ x : G, g x =
      if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x,hx⟩) else 0)
    {V : Set a.quotient} {U : Set G} (hf : tsupport f.val ⊆ V)
    (hU : ∀ t : a.val.1, QuotientGroup.mk t ∈ V → t.val ∈ U) : tsupport g.val ⊆ U := by
  let q : a.val.1 → a.quotient := QuotientGroup.mk
  let L : Set G := Subtype.val '' (q ⁻¹' tsupport f.val)
  have hL : IsClosed L := (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isClosedMap _
    ((isClosed_tsupport f.val).preimage QuotientGroup.continuous_mk)
  refine (closure_minimal (t := L) ?_ hL).trans ?_
  · intro z hz
    change g z ≠ 0 at hz
    rw [hg] at hz
    split_ifs at hz with h
    · exact ⟨⟨z,h⟩, subset_tsupport f.val hz, rfl⟩
    · exact (hz rfl).elim
  · rintro _ ⟨t, ht, rfl⟩
    exact hU t (hf ht)

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
by
  classical
  let j (a : BruhatStructuralPair G) := (schwartzBruhatStageLift a).choose
  have hj (a : BruhatStructuralPair G) := (schwartzBruhatStageLift a).choose_spec
  refine ⟨j, hj, ?_⟩
  rintro x ⟨U, ⟨hU, hT⟩, hx⟩
  refine (exists_stage_open_over (G := G) (U := U) (x := x) hU hx).elim fun a ha ↦
    ha.elim fun y hy ↦ hy.elim fun V h ↦ ?_
  have hkill (f : SchwartzBruhat a.quotient) (hf : tsupport f.val ⊆ V) : T (j a f) = 0 :=
    hT (j a f) (schwartzBruhatStageLift_tsupport a f (j a f) (hj a f) hf h.2.2.2)
  exact mem_iUnion.mpr ⟨a, y, ⟨V, ⟨h.2.1, hkill⟩, h.2.2.1⟩, h.1⟩

end Supports

section ElementaryTranslations

open scoped BoundedContinuousFunction

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

omit [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
private theorem elementaryPartial_translate (g : ElementaryLieGroup m n r F) (v) (hv : elementaryCover v g.2.2.1 g.2.2.2 = g)
    (f : ElementaryLieGroup m n r F → ℂ) (β γ) (u) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (fun x ↦ f (g + x)) β γ u a b =
      elementaryPartial f β γ (u + v) (a + g.2.2.1) (b + g.2.2.2) := by
  have h (w) : g + elementaryCover w a b =
      elementaryCover (w+v) (a+g.2.2.1) (b+g.2.2.2) := by
    rw [add_comm, ← hv]
    exact elementaryCover_add ..
  simp only [elementaryPartial, h]
  rw [iteratedFDeriv_comp_add_right (f := fun w ↦ f (elementaryCover w (a+g.2.2.1) (b+g.2.2.2))) _ v u]

private def elementaryLatticeVector (a : Fin r → ℤ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun k ↦ (a k : ℝ))

private theorem elementaryMonomial_translate_le {k : ℕ} (x t : EuclideanSpace ℝ (Fin k)) (α : Fin k → ℕ) {M : ℝ}
    (hM : ‖t‖ ≤ M) :
    ‖∏ j, (x j : ℂ) ^ α j‖ ≤ (1 + M) ^ (∑ j, α j) * (1 + ‖x + t‖ ^ (∑ j, α j)) := by
  let R := max 1 ‖x+t‖
  have hR : 1 ≤ R := le_max_left ..
  have hM0 := (norm_nonneg t).trans hM
  have h (j : Fin k) : ‖(x j : ℂ)‖ ≤ (1 + M) * R := by
    rw [Complex.norm_real]
    have hx : ‖x‖ ≤ ‖x+t‖ + ‖t‖ := by simpa using norm_sub_le (x+t) t
    calc
      ‖x j‖ ≤ ‖x‖ := PiLp.norm_apply_le x j
      _ ≤ R + M := hx.trans (add_le_add (le_max_right ..) hM)
      _ ≤ (1 + M) * R := by nlinarith [mul_le_mul_of_nonneg_left hR hM0]
  have hpow (d : ℕ) : R ^ d ≤ 1 + ‖x+t‖ ^ d := by
    dsimp [R]
    rcases le_total 1 ‖x+t‖ with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
  rw [norm_prod]
  calc
    _ ≤ ∏ j, ((1 + M) * R) ^ α j := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      (fun j _ ↦ by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (h j) (α j))
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpow _) (by positivity)

/-- On bounded sets of translating parameters, each translated seminorm is dominated
by a single continuous seminorm of the original function. -/
private theorem elementarySchwartzBound_translate_le (i : ElementarySchwartzIndex m n r) (M : ℝ) (hM : 0 ≤ M) :
    ∃ p : Seminorm ℂ (ElementarySchwartz m n r F), Continuous p ∧
      ∀ (g : ElementaryLieGroup m n r F) (f : ElementarySchwartz m n r F),
        ‖g.1‖ ≤ M → ‖elementaryLatticeVector g.2.2.1‖ ≤ M →
        elementarySchwartzBound (fun x ↦ f (g+x)) i ≤ ENNReal.ofReal (p f) := by
  obtain ⟨P, hP, hval⟩ := elementarySchwartz_withSeminorms_P1 (m := m) (n := n) (r := r) (F := F)
  let d := ∑ j, i.1 j
  let l := ∑ j, i.2.2.2 j
  let C : ℝ≥0 := ⟨(1+M)^d * (1+M)^l, by positivity⟩
  let q := P (d, l, i.2.1, i.2.2.1)
  refine ⟨C • q, (hP.continuous_seminorm _).const_smul (C : ℝ), fun g f hx ha ↦ ?_⟩
  obtain ⟨t, ht⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  let v := (g.1,t)
  refine iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have hL : elementaryLatticeVector a + elementaryLatticeVector g.2.2.1 = elementaryLatticeVector (a+g.2.2.1) := by
    ext k
    change (a k : ℝ) + (g.2.2.1 k : ℝ) = ((a k + g.2.2.1 k : ℤ) : ℝ)
    exact (Int.cast_add ..).symm
  let D := ‖elementaryPartial f i.2.1 i.2.2.1 (u+v) (a+g.2.2.1) (b+g.2.2.2)‖
  let X := (1 + ‖u.1+g.1‖^d)
  let Z := (1 + ‖elementaryLatticeVector (a+g.2.2.1)‖^l)
  have hf : X * Z * D ≤ q f := by
    apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg q f)).mp
    rw [show ENNReal.ofReal (q f) = _ from hval _ f]
    exact le_iSup_of_le (u+v) (le_iSup_of_le (a+g.2.2.1) (le_iSup_of_le (b+g.2.2.2) le_rfl))
  have h₁ : ‖∏ k, (u.1 k : ℂ) ^ i.1 k‖ ≤ (1+M)^d * X := elementaryMonomial_translate_le u.1 g.1 i.1 hx
  have h₂ : ‖∏ k, (a k : ℂ) ^ i.2.2.2 k‖ ≤ (1+M)^l * Z := by
    have h := elementaryMonomial_translate_le (elementaryLatticeVector a) (elementaryLatticeVector g.2.2.1) i.2.2.2 ha
    rw [hL] at h
    simpa only [Z, l, elementaryLatticeVector, PiLp.toLp_apply, Complex.ofReal_intCast] using h
  rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _), coe_nnNorm,
    norm_mul, norm_mul, elementaryPartial_translate g v ht]
  calc
    _ ≤ ((1+M)^d * X) * ((1+M)^l * Z) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (by dsimp [X]; positivity)) (norm_nonneg _)
    _ = (C : ℝ) * (X * Z * D) := by change _ = ((1+M)^d * (1+M)^l) * _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf C.property

end ElementaryTranslations

section Translations

variable {H E : Type*} [Group H] [TopologicalSpace H] [hTopH : IsTopologicalGroup H]

open scoped ComplexOrder in
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
    Continuous (fun p : H × E ↦ ρ p.1 p.2) := by
  -- The compact-open argument only needs the stage actions to be continuous into E.
  clear hBarrelled hPreserve
  let : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).isTopologicalAddGroup
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : LocallyConvexSpace ℂ E := .ofBasisZero ℂ E _ _ (LocallyConvexSpace.convex_basis_zero ℝ E)
    (fun _ hs ↦ convex_of_nonneg_surjective_algebraMap ℂ
      (fun _ hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) hs.2)
  let : ContinuousSMul ℝ C(H, E) := IsScalarTower.continuousSMul ℂ
  have hStage (n : ℕ) : Continuous (fun p : H × S n ↦ ρ p.1 p.2.val) := by
    rw [continuous_iff_continuousAt]
    intro ⟨h, x⟩
    obtain ⟨m, hm⟩ := hK' h
    let l := max m n
    have hh : h ∈ K l := hK (le_max_left m n) hm
    let inc : S n →L[ℂ] S l := (S n).subtypeL.codRestrict (S l)
      (fun y ↦ hS (le_max_right m n) y.property)
    have he := (K l).isOpen.isOpenEmbedding_subtypeVal.prodMap
      (IsOpenEmbedding.id (X := S n))
    apply (he.continuousAt_iff (x := (⟨h, hh⟩, x))).mp
    exact ((hContinuous l).comp (continuous_fst.prodMk (inc.continuous.comp continuous_snd))).continuousAt
  have hOrbit (x : E) : Continuous (fun h ↦ ρ h x) := by
    obtain ⟨n, hx⟩ := hS' x
    exact (hStage n).comp (continuous_id.prodMk (continuous_const (y := (⟨x, hx⟩ : S n))))
  let A : E →ₗ[ℂ] C(H, E) :=
    { toFun := fun x ↦ ⟨fun h ↦ ρ h x, hOrbit x⟩
      map_add' := fun x y ↦ ContinuousMap.ext fun h ↦ map_add (ρ h) x y
      map_smul' := fun c x ↦ ContinuousMap.ext fun h ↦ (ρ h).map_smul c x }
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ (S n).subtype)} → _) := ⟨hFinal⟩
  have hA : Continuous A := by
    refine (PolynormableSpace.withSeminorms ℂ C(H, E)).continuous_of_continuous_comp A fun p ↦ ?_
    refine hP.continuous_seminorm ⟨p.val.comp A, fun n ↦ p.property.comp ?_⟩
    exact ContinuousMap.continuous_of_continuous_uncurry _ ((hStage n).comp continuous_swap)
  exact continuous_eval.comp ((hA.comp continuous_snd).prodMk continuous_fst)

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
  let E := ElementarySchwartz m n r F
  let X := ElementaryLieGroup m n r F
  let size (g : X) := max ‖g.1‖ ‖elementaryLatticeVector g.2.2.1‖
  have hsize : Continuous size := continuous_fst.norm.max
    ((continuous_of_discreteTopology (f := fun a ↦ ‖elementaryLatticeVector (r := r) a‖)).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hmem (g : X) (f : E) : (fun x ↦ f (g+x)) ∈ elementarySchwartzSubmodule m n r F := by
    constructor
    · intro a b
      obtain ⟨v, hv⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
      change elementaryCover (g.1,v) g.2.2.1 g.2.2.2 = g at hv
      have heq (u) : g + elementaryCover u a b =
          elementaryCover (u+(g.1,v)) (a+g.2.2.1) (b+g.2.2.2) := by
        exact (add_comm ..).trans ((congrArg (elementaryCover u a b + ·) hv.symm).trans (elementaryCover_add ..))
      simp only [heq]
      exact (f.property.1 (a+g.2.2.1) (b+g.2.2.2)).comp (contDiff_id.add contDiff_const)
    · intro i
      obtain ⟨p, _, hp⟩ := elementarySchwartzBound_translate_le (F := F) i (size g) ((norm_nonneg _).trans (le_max_left ..))
      exact (hp g f (le_max_left ..) (le_max_right ..)).trans_lt ENNReal.ofReal_lt_top
  let T (z : X × E) : E := ⟨_, hmem z.1 z.2⟩
  refine ⟨⟨T, ?_⟩, fun _ _ _ ↦ rfl⟩
  let : TopologicalSpace.MetrizableSpace E := elementarySchwartz_isFrechet.choose_spec.2.1
  change Continuous T
  rw [CompactlyCoherentSpace.isCoherentWith.continuous_iff]
  intro K hK
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hsize.comp continuous_fst).continuousOn
  let M' := max 0 M
  have hbound : Bornology.IsVonNBounded ℂ (T '' K) := by
    apply elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bddAbove.mpr
    intro i
    obtain ⟨p, hp, h⟩ := elementarySchwartzBound_translate_le (F := F) i M' (le_max_left ..)
    obtain ⟨R, hR⟩ := hK.bddAbove_image (hp.comp continuous_snd).continuousOn
    refine ⟨R, ?_⟩
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hg : size z.1 ≤ M' := (hM (mem_image_of_mem _ hz)).trans (le_max_right ..)
    have hb := h z.1 z.2 ((le_max_left ..).trans hg) ((le_max_right ..).trans hg)
    exact (ENNReal.toReal_le_of_le_ofReal (apply_nonneg p _) hb).trans (hR (mem_image_of_mem _ hz))
  -- On the compact closure of these translates, pointwise convergence detects the topology.
  let S := closure (T '' K)
  have hS : IsCompact S := elementarySchwartz_isCompact_of_isClosed_isVonNBounded isClosed_closure hbound.closure
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let ev (f : S) : X → ℂ := f.val.val
  have hEval : Continuous ev := continuous_pi fun x ↦ elementarySchwartz_continuousEval.comp
    (continuous_subtype_val.prodMk (continuous_const (y := x)))
  have he := hEval.isClosedEmbedding (show Function.Injective ev from fun _ _ h ↦ Subtype.ext (Subtype.ext h))
  let lift (z : K) : S := ⟨T z.val, subset_closure (mem_image_of_mem _ z.property)⟩
  have hc : Continuous lift := he.isEmbedding.continuous_iff.mpr (continuous_pi fun x ↦
    elementarySchwartz_continuousEval.comp ((continuous_snd.comp continuous_subtype_val).prodMk
      ((continuous_fst.comp continuous_subtype_val).add continuous_const)))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hc)

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
      ∀ g ∈ K, ∀ f ∈ V, schwartzBruhatTranslate g f ∈ U := by
  have h : ∀ᶠ f in 𝓝 (0 : SchwartzBruhat G), ∀ g ∈ K, schwartzBruhatTranslate g f ∈ U := by
    apply hK.eventually_forall_of_forall_eventually
    intro g _
    have hc := (schwartzBruhatTranslate_continuous (G := G)).comp continuous_swap
    exact (hc.continuousAt (x := (0, g))).preimage_mem_nhds hU
  exact ⟨_, h, fun g hg f hf ↦ hf g hg⟩

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
    Continuous (fun p : H × UniformSpace.Completion E ↦ ρ p.1 p.2) := by
  let C := UniformSpace.Completion E
  let i : E →+ C := UniformSpace.Completion.toCompl
  have hd : IsDenseInducing i := UniformSpace.Completion.isDenseInducing_coe
  -- A closed target neighborhood lets us pass each estimate to the closure in C.
  have hZero (h : H) {U : Set C} (hU : U ∈ 𝓝 0) :
      ∃ N ∈ 𝓝 h, ∃ V ∈ 𝓝 (0 : C), ∀ k ∈ N, MapsTo (ρ k) V U := by
    obtain ⟨W, ⟨hW, hcW⟩, hWU⟩ := (closed_nhds_basis (0 : C)).mem_iff.mp hU
    have hc := hd.continuous.comp hJoint
    have hpre := (hc.continuousAt (x := (h, 0))).preimage_mem_nhds
      (show W ∈ 𝓝 (i (τ h 0)) by simpa using hW)
    obtain ⟨N, hN, B, hB, hNB⟩ := mem_nhds_prod_iff.mp hpre
    refine ⟨N, hN, closure (i '' B), ?_, fun k hk ↦ ?_⟩
    · simpa only [map_zero] using hd.closure_image_mem_nhds hB
    · apply Subset.trans _ (preimage_mono hWU)
      apply closure_minimal _ (hcW.preimage (hEach k))
      rintro _ ⟨y, hy, rfl⟩
      change ρ k (y : C) ∈ W
      rw [hτ]
      exact hNB (a := (k, y)) ⟨hk, hy⟩
  rw [continuous_iff_continuousAt]
  intro ⟨h, x⟩ U hU
  have hsum : Continuous (fun p : C × C × C ↦ p.1 + p.2.1 - p.2.2 + ρ h x) :=
    ((continuous_fst.add (continuous_fst.comp continuous_snd)).sub
      (continuous_snd.comp continuous_snd)).add continuous_const
  have hu : (fun p : C × C × C ↦ p.1 + p.2.1 - p.2.2 + ρ h x) ⁻¹' U ∈
      𝓝 ((0 : C), (0 : C), (0 : C)) := by
    apply hsum.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨A, hA, BC, hBC, hrect⟩ := mem_nhds_prod_iff.mp hu
  obtain ⟨B, hB, D, hD, hrect'⟩ := mem_nhds_prod_iff.mp hBC
  obtain ⟨N, hN, V, hV, hNV⟩ := hZero h (inter_mem hA hD)
  -- Approximate x by an original vector c, retaining a neighborhood around x - c.
  have hnear : {z : C | x - z ∈ interior V} ∈ 𝓝 x := by
    apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
    simpa using interior_mem_nhds.mpr hV
  obtain ⟨_, hz, c, rfl⟩ := mem_closure_iff_nhds.mp (hd.dense x) _ hnear
  have hc : Continuous (fun k ↦ ρ k (i c)) := by
    exact (hd.continuous.comp (hJoint.comp (continuous_id.prodMk continuous_const))).congr
      (fun k ↦ (hτ k c).symm)
  have horbit : ∀ᶠ k in 𝓝 h, ρ k (i c) - ρ h (i c) ∈ B :=
    (hc.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hB)
  have hrem : ∀ᶠ z in 𝓝 x, z - i c ∈ V :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  change ∀ᶠ p : H × C in 𝓝 (h, x), ρ p.1 p.2 ∈ U
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (inter_mem hN horbit),
    continuous_snd.continuousAt.preimage_mem_nhds hrem] with p hp hp'
  have h₁ := (hNV p.1 hp.1 hp').1
  have h₃ := (hNV h (mem_of_mem_nhds hN) (interior_subset hz)).2
  have h := hrect (a := (ρ p.1 (p.2 - i c), ρ p.1 (i c) - ρ h (i c), ρ h (x - i c)))
    ⟨h₁, hrect' ⟨hp.2, h₃⟩⟩
  simpa only [mem_preimage, map_sub, sub_add_sub_cancel, sub_sub_sub_cancel_right, sub_add_cancel]
    using h

open scoped ComplexOrder in
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
        TensorProduct.map (ρ p.1).toLinearMap (τ p.1).toLinearMap p.2)) := by
  let P := ProjectiveTensor E F
  let A (h : H) : P →ₗ[ℂ] P := TensorProduct.map (ρ h).toLinearMap (τ h).toLinearMap
  let tmul : E × F → P := fun z ↦ z.1 ⊗ₜ[ℂ] z.2
  have htZero : tmul (0, 0) = 0 := TensorProduct.zero_tmul E (0 : F)
  have ht : Continuous tmul :=
    (continuous_projectiveTensor_iff (G := P) (LinearMap.id : P →ₗ[ℂ] P)).mp continuous_id
  have horbit (z : P) : Continuous (fun h ↦ A h z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      exact ht.comp ((hρ.comp (continuous_id.prodMk continuous_const)).prodMk
        (hτ.comp (continuous_id.prodMk continuous_const)))
    | add x y hx hy => exact (hx.add hy).congr fun h ↦ ((A h).map_add x y).symm
  have hzero (h : H) : Tendsto (fun p : H × P ↦ A p.1 p.2) (𝓝 (h, 0)) (𝓝 0) := by
    apply (PolynormableSpace.hasBasis_zero_ball ℂ P).tendsto_right_iff.mpr
    intro q hq
    have hball := q.ball_mem_nhds hq one_pos
    have ht0 := ht.continuousAt (x := ((0 : E), (0 : F)))
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (ht0.preimage_mem_nhds
      (by simpa only [htZero] using hball))
    obtain ⟨N, hN, B, hB, hNB⟩ := mem_nhds_prod_iff.mp ((hρ.continuousAt (x := (h, 0))).preimage_mem_nhds
      (show U ∈ 𝓝 (ρ h 0) by simpa using hU))
    obtain ⟨M, hM, D, hD, hMD⟩ := mem_nhds_prod_iff.mp ((hτ.continuousAt (x := (h, 0))).preimage_mem_nhds
      (show V ∈ 𝓝 (τ h 0) by simpa using hV))
    let W := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) B D)
    have hW : W ∈ 𝓝 (0 : P) :=
      (projectiveTensor_zero_basis (𝓝 (0 : E)).basis_sets (𝓝 (0 : F)).basis_sets).mem_of_mem
        (i := (B, D)) ⟨hB, hD⟩
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (inter_mem hN hM),
      continuous_snd.continuousAt.preimage_mem_nhds hW] with p hp hpW
    let s := q.comp (A p.1)
    suffices W ⊆ s.ball 0 1 by
      exact q.mem_ball_zero.mpr (s.mem_ball_zero.mp (this hpW))
    apply absConvexHull_min _ ⟨s.balanced_ball_zero 1,
      convex_RCLike_iff_convex_real.mpr (s.convex_ball 0 1)⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply s.mem_ball_zero.mpr
    exact q.mem_ball_zero.mp (hUV (a := (ρ p.1 x, τ p.1 y))
      ⟨hNB (a := (p.1, x)) ⟨hp.1, hx⟩, hMD (a := (p.1, y)) ⟨hp.2, hy⟩⟩)
  rw [continuous_iff_continuousAt]
  intro ⟨h, z⟩
  have hd : Continuous (fun p : H × P ↦ (p.1, p.2 - z)) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hlim := (hzero h).comp (hd.tendsto' (h, z) (h, 0) (by simp))
  have hc := hlim.add (((horbit z).comp continuous_fst).tendsto (h, z))
  change Tendsto (fun p : H × P ↦ A p.1 p.2) (𝓝 (h, z)) (𝓝 (A h z))
  simpa only [Function.comp_def, map_sub, sub_add_cancel, zero_add] using hc

end Translations

end RiemannMasullo
