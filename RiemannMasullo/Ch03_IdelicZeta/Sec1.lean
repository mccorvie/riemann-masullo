module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import Mathlib.Topology.Algebra.PontryaginDual

import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.CompactOpen
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Units
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual

/-!
# Riemann surfaces of continuous quasi-characters

Section 3.1 of Masullo. We use the compact-open topology on continuous monoid homomorphisms.
On a group, such a map into ℂ takes values in ℂˣ. This convention makes the global space
definitionally Mathlib's space of Hecke characters. The complex coordinates below use the
normalized module, including its exponent two at a complex place.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open scoped NNReal Manifold ContDiff

/-- Paper: §3.1.1, p. 118. The space of quasi-characters has the compact-open topology.
Deviation: We use complex-valued continuous homomorphisms on a group, whose values are units. -/
abbrev QuasiCharacter (G : Type*) [Group G] [TopologicalSpace G] := G →ₜ* ℂ

section Generalities

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)

local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

/-- Paper: Equation (3.1.1.1), p. 119. Restricting a quasi-character to the kernel of the
module gives the projection indexing the components. We view its values as complex numbers. -/
def normOneRestriction : C(QuasiCharacter G, QuasiCharacter m.ker) :=
  let i : m.ker →ₜ* G := ⟨m.ker.subtype, continuous_subtype_val⟩
  ⟨fun c => c.comp i, i.continuous_comp_left⟩

/-- The positive real units have the order topology and compact closed intervals. -/
private theorem nonnegRealUnits_orderTopology_and_compactIccSpace :
    OrderTopology ℝ≥0ˣ ∧ CompactIccSpace ℝ≥0ˣ := by
  let e := Nonneg.unitsHomeomorphPos ℝ
  let f : ℝ≥0ˣ ↪o ℝ := OrderEmbedding.ofStrictMono (Subtype.val ∘ e) (fun _ _ h => h)
  have hi : IsInducing f := (IsInducing.subtypeVal (t := Set.Ioi (0 : ℝ))).comp e.isInducing
  have hr : Set.range f = Set.Ioi 0 := by
    change Set.range ((Subtype.val : Set.Ioi (0 : ℝ) → ℝ) ∘ e) = _
    rw [Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have ho : Set.OrdConnected (Set.range f) := hr.symm ▸ Set.ordConnected_Ioi
  refine ⟨⟨hi.eq_induced.trans (f.strictMono.induced_topology_eq_preorder ho)⟩, ⟨?_⟩⟩
  intro a b
  apply hi.isCompact_iff.mpr
  rw [f.image_Icc ho]
  exact isCompact_Icc

/-- Paper: Equation (3.1.1.1), p. 119. Every quasi-character of a closed nontrivial subgroup
of the positive reals can be joined to the trivial character by a continuous family. -/
private theorem exists_quasiCharacter_deformation (H : Subgroup ℝ≥0ˣ)
    (hH : IsClosed (H : Set ℝ≥0ˣ)) [Nontrivial H] (χ : QuasiCharacter H) :
    ∃ f : ℝ → QuasiCharacter H, Continuous f ∧ f 0 = 1 ∧ f 1 = χ := by
  have := nonnegRealUnits_orderTopology_and_compactIccSpace.1
  rcases H.dense_or_isCyclic with hd | hc
  · have htop : H = ⊤ :=
      Subgroup.coe_eq_univ.mp (hH.closure_eq ▸ hd.closure_eq)
    subst H
    -- Real powers interpolate between the trivial homomorphism and the identity.
    let power (t : ℝ) (u : ↥(⊤ : Subgroup ℝ≥0ˣ)) : ↥(⊤ : Subgroup ℝ≥0ˣ) :=
      ⟨Units.mk0 ((u.val : ℝ≥0) ^ t)
        (ne_of_gt (NNReal.rpow_pos (pos_iff_ne_zero.mpr u.val.ne_zero))), trivial⟩
    have hpower : Continuous (uncurry power) := by
      apply IsInducing.subtypeVal.continuous_iff.mpr
      apply Units.isEmbedding_val₀.continuous_iff.mpr
      apply NNReal.isEmbedding_coe.continuous_iff.mpr
      exact (NNReal.continuous_coe.comp
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd))).rpow
          continuous_fst (fun p => Or.inl (NNReal.coe_ne_zero.mpr p.2.val.ne_zero))
    let f (t : ℝ) : QuasiCharacter ↥(⊤ : Subgroup ℝ≥0ˣ) :=
      χ.comp
        { toFun := power t
          map_one' := by
            apply Subtype.ext
            apply Units.ext
            simp [power]
          map_mul' := by
            intro x y
            apply Subtype.ext
            apply Units.ext
            simp [power, NNReal.mul_rpow]
          continuous_toFun := hpower.comp (continuous_const.prodMk continuous_id) }
    refine ⟨f, ContinuousMonoidHom.continuous_of_continuous_uncurry f
      (χ.continuous.comp hpower), ?_, ?_⟩
    · ext1 x
      change χ (power 0 x) = 1
      have h : power 0 x = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp [power]
      rw [h, map_one]
    · ext1 x
      change χ (power 1 x) = χ x
      congr 1
      apply Subtype.ext
      apply Units.ext
      simp [power]
  · let : DiscreteTopology H := Subgroup.isCyclic_iff_discreteTopology.mp hc
    obtain ⟨orderIso⟩ := LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int.mp hc
    let e := orderIso.toMulEquiv
    -- Exponentiating a multiple of the logarithm interpolates the value on a generator.
    let z := Complex.log (χ (e.symm (Multiplicative.ofAdd 1)))
    let f (t : ℝ) : QuasiCharacter H := {
      toFun x := Complex.exp (((e x).toAdd : ℂ) * ((t : ℂ) * z))
      map_one' := by simp [show (1 : Multiplicative ℤ).toAdd = 0 from rfl]
      map_mul' x y := by
        rw [map_mul]
        change Complex.exp (↑((e x).toAdd + (e y).toAdd) * _) = _
        rw [Int.cast_add, add_mul, Complex.exp_add]
      continuous_toFun := continuous_of_discreteTopology }
    refine ⟨f, ContinuousMonoidHom.continuous_of_continuous_uncurry f ?_, ?_, ?_⟩
    · apply continuous_prod_of_discrete_right.mpr
      intro x
      change Continuous fun t : ℝ => Complex.exp (((e x).toAdd : ℂ) * ((t : ℂ) * z))
      exact Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.mul continuous_const))
    · ext1 x
      change Complex.exp (((e x).toAdd : ℂ) * ((0 : ℝ) * z)) = 1
      simp
    · ext1 x
      change Complex.exp (((e x).toAdd : ℂ) * (Complex.ofReal 1 * z)) = χ x
      have hx : e.symm (Multiplicative.ofAdd 1) ^ (e x).toAdd = x := by
        apply e.injective
        rw [map_zpow, e.apply_symm_apply]
        change Multiplicative.ofAdd ((e x).toAdd • (1 : ℤ)) = e x
        simp
      rw [Complex.ofReal_one, one_mul, Complex.exp_int_mul, Complex.exp_log, ← map_zpow, hx]
      exact ((Group.isUnit _).map χ).ne_zero

/-- Paper: Equation (3.1.1.1), p. 119. Two quasi-characters are in the same connected
component exactly when their restrictions to the norm-one subgroup agree. -/
theorem mem_connectedComponent_iff_normOneRestriction [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c d : QuasiCharacter G) :
    d ∈ connectedComponent c ↔ normOneRestriction m d = normOneRestriction m c := by
  let inv := c.comp (ContinuousMonoidHom.inv G)
  have hc (x : G) : c x ≠ 0 := ((Group.isUnit x).map c).ne_zero
  have hdiv (e : QuasiCharacter G) (x : G) : (e * inv) x = e x / c x := by
    change e x * c x⁻¹ = e x / c x
    rw [map_inv, div_eq_mul_inv]
  have htranslate (q : QuasiCharacter G) : Continuous (fun e : QuasiCharacter G => e * q) := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_eval.comp (continuous_fst.prodMk continuous_snd)).mul
      (q.continuous.comp continuous_snd)
  have hrestrict (e : QuasiCharacter G) :
      normOneRestriction m (e * inv) = 1 ↔ normOneRestriction m e = normOneRestriction m c := by
    rw [DFunLike.ext_iff, DFunLike.ext_iff]
    refine forall_congr' fun x => ?_
    change (e * inv) x = 1 ↔ e x = c x
    rw [hdiv, div_eq_one_iff_eq (hc x)]
  constructor
  · intro hd
    let : CompactSpace m.ker :=
      isCompact_iff_compactSpace.mp (hm.isCompact_preimage (isCompact_singleton (x := 1)))
    have hopen : IsOpen {e | normOneRestriction m e = normOneRestriction m c} := by
      have ho := isOpen_singleton_one_complex.preimage
        ((normOneRestriction m).continuous.comp (htranslate inv))
      convert ho using 1
      ext e
      exact (hrestrict e).symm
    exact IsClopen.connectedComponent_subset
      ⟨isClosed_eq (normOneRestriction m).continuous continuous_const, hopen⟩ rfl hd
  · intro hd
    -- The ratio is trivial on the kernel and descends to the closed norm image.
    let q := d * inv
    have hq (x : m.ker) : q x = 1 := DFunLike.congr_fun ((hrestrict d).mpr hd) x
    let r : G →ₜ* m.range :=
      ⟨m.rangeRestrict, hm.continuous.subtype_mk fun x => ⟨x, rfl⟩⟩
    have hr : IsQuotientMap r :=
      (hm.isClosedMap.codRestrict (s := (m.range : Set ℝ≥0ˣ)) fun x => ⟨x, rfl⟩).isQuotientMap
        r.continuous m.rangeRestrict_surjective
    have hqKer : m.ker ≤ q.toMonoidHom.ker := fun x hx => hq ⟨x, hx⟩
    let qLift := (QuotientGroup.lift m.ker q.toMonoidHom hqKer).comp
      (QuotientGroup.quotientKerEquivRange m).symm.toMonoidHom
    have hqLift (x : G) : qLift (r x) = q x := by
      change
        QuotientGroup.lift m.ker q.toMonoidHom hqKer ((QuotientGroup.quotientKerEquivRange m).symm
          ((QuotientGroup.quotientKerEquivRange m) (QuotientGroup.mk x))) = q.toMonoidHom x
      rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
    have hqCont : Continuous qLift := hr.continuous_iff.mpr (by
      rw [show (qLift : m.range → ℂ) ∘ r = q from funext hqLift]
      exact q.continuous)
    have : Nontrivial m.range := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨r x, 1, fun he => hx (congrArg Subtype.val he)⟩⟩
    obtain ⟨f, hf, hf0, hf1⟩ :=
      exists_quasiCharacter_deformation m.range hm.isClosed_range ⟨qLift, hqCont⟩
    let p (t : ℝ) : QuasiCharacter G := (f t).comp r * c
    have hp : Continuous p := (htranslate c).comp (r.continuous_comp_left.comp hf)
    have hp0 : p 0 = c := by
      ext1 x
      simp [p, hf0, ContinuousMonoidHom.mul_apply]
    have hp1 : p 1 = d := by
      ext1 x
      change f 1 (r x) * c x = d x
      rw [hf1]
      change qLift (r x) * c x = d x
      rw [hqLift, hdiv, div_mul_cancel₀ _ (hc x)]
    exact (isPreconnected_range hp).subset_connectedComponent
      ⟨0, hp0⟩ ⟨1, hp1⟩

/-- Paper: Equation (3.1.1.1), p. 119. The restrictions to the norm-one subgroup are
exactly its unitary characters. In particular every such character lifts. -/
theorem range_normOneRestriction [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Set.range (normOneRestriction m) = Set.range (fun χ : PontryaginDual m.ker =>
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) := by
  let : CompactSpace m.ker :=
    isCompact_iff_compactSpace.mp (hm.isCompact_preimage (isCompact_singleton (x := 1)))
  apply Set.Subset.antisymm
  · rintro _ ⟨c, rfl⟩
    let q := normOneRestriction m c
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := m.ker))
      q.continuous.norm.continuousOn
    have hmax (y : m.ker) : ‖q y‖ ≤ ‖q x‖ := isMaxOn_univ_iff.mp hx y
    have hpos : 0 < ‖q x‖ := zero_lt_one.trans_le (by simpa using hmax 1)
    have hsq := hmax (x * x)
    rw [map_mul, norm_mul] at hsq
    have hle (y : m.ker) : ‖q y‖ ≤ 1 :=
      (hmax y).trans ((mul_le_iff_le_one_right hpos).mp hsq)
    have hnorm (y : m.ker) : ‖q y‖ = 1 := by
      have h := hle y⁻¹
      rw [map_inv, norm_inv] at h
      exact (hle y).antisymm ((inv_le_one₀ (norm_pos_iff.mpr
        ((Group.isUnit y).map q).ne_zero)).mp h)
    let χ : PontryaginDual m.ker :=
      { toFun := fun y => ⟨q y, mem_sphere_zero_iff_norm.mpr (hnorm y)⟩
        map_one' := Circle.ext (map_one q)
        map_mul' := fun y z => Circle.ext (map_mul q y z)
        continuous_toFun := q.continuous.subtype_mk _ }
    exact ⟨χ, ContinuousMonoidHom.ext fun _ => rfl⟩
  · rintro _ ⟨χ, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g, 1 < m g := by
      obtain ⟨g, hg⟩ := hne
      rcases lt_or_gt_of_ne hg with h | h
      · exact ⟨g⁻¹, by simpa only [map_inv, one_lt_inv'] using h⟩
      · exact ⟨g, h⟩
    have := nonnegRealUnits_orderTopology_and_compactIccSpace.1
    have := nonnegRealUnits_orderTopology_and_compactIccSpace.2
    let Z := Subgroup.zpowers g
    -- The module embeds this cyclic subgroup into a discrete subgroup of the positive reals.
    have hmZ : Set.InjOn m (Z : Set G) := by
      intro x hx y hy h
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact congrArg (g ^ ·) ((zpow_right_strictMono hg).injective (by simpa only [map_zpow] using h))
    let : DiscreteTopology (Z.map m) := by
      change DiscreteTopology ((Subgroup.zpowers g).map m)
      rw [MonoidHom.map_zpowers]
      exact Subgroup.isCyclic_iff_discreteTopology.mp inferInstance
    let : DiscreteTopology Z := .of_continuous_injective
      (f := m.subgroupMap Z) ((hm.continuous.comp continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (hmZ x.property y.property (congrArg Subtype.val h)))
    let : IsClosed (Z : Set G) := Subgroup.isClosed_of_discreteTopology
    let p : G →ₜ* G ⧸ Z := ⟨QuotientGroup.mk' Z, QuotientGroup.continuous_mk⟩
    -- Each quotient class has a representative with module between one and `m g`.
    have huniv : p '' (m ⁻¹' Set.Icc 1 (m g)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn, -⟩ := existsUnique_zpow_near_of_one_lt' hg (m y)
      refine ⟨y / g ^ n, ?_, ?_⟩
      · change m (y / g ^ n) ∈ Set.Icc 1 (m g)
        simpa only [map_div, map_zpow, Set.mem_Icc] using ⟨hn.1, hn.2.le⟩
      · have hpow : p (g ^ n) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers g n)
        rw [map_div, hpow, div_one]
        rfl
    let : CompactSpace (G ⧸ Z) := isCompact_univ_iff.mp
      (huniv ▸ (hm.isCompact_preimage isCompact_Icc).image p.continuous)
    let i : m.ker →ₜ* G := ⟨m.ker.subtype, continuous_subtype_val⟩
    have hi : Injective (p.comp i) := by
      apply (MonoidHom.ker_eq_bot_iff (p.comp i).toMonoidHom).mp
      apply le_antisymm ?_ bot_le
      intro x hx
      have hxZ : (x : G) ∈ Z := (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_bot.mpr (Subtype.ext (hmZ hxZ Z.one_mem (x.property.trans (map_one m).symm)))
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_extension_of_compact (p.comp i) hi χ
    let coeCircle : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    exact ⟨(coeCircle.comp ψ).comp p,
      ContinuousMonoidHom.ext fun x => congrArg (fun z : Circle => (z : ℂ)) (hψ x)⟩

/-- Paper: §3.1.1, p. 119. Near each quasi-character the complex exponent is a coordinate
centered at zero. Its inverse sends z to the character twisted by the z-th power of the module. -/
def HasNormTwistCharts : Prop :=
  ∀ c : QuasiCharacter G, ∃ e : OpenPartialHomeomorph (QuasiCharacter G) ℂ,
    c ∈ e.source ∧ e c = 0 ∧
      ∀ z ∈ e.target, ∀ g, e.symm z g = c g * (modℝ g : ℂ) ^ z

/-- A quasi-character trivial at an element of module greater than one is trivial
if its values stay in the open unit ball about one on the corresponding norm interval. -/
private theorem quasiCharacter_eq_one_of_normInterval {g : G}
    (hK : IsCompact (m ⁻¹' Set.Icc 1 (m g)))
    (hg : 1 < m g) (q : QuasiCharacter G) (hqg : q g = 1)
    (hq : Set.MapsTo q (m ⁻¹' Set.Icc 1 (m g)) (Metric.ball 1 1)) : q = 1 := by
  let K := m ⁻¹' Set.Icc 1 (m g)
  -- Multiplying by powers of g moves any element into K without changing its value.
  have himage : Set.range (q : G → ℂ) = q '' K := by
    refine Set.Subset.antisymm (Set.range_subset_iff.mpr fun y => ?_) (Set.image_subset_range _ _)
    obtain ⟨n, hn, -⟩ := existsUnique_zpow_near_of_one_lt' hg (m y)
    refine ⟨y / g ^ n, ?_, by rw [map_div, map_zpow, hqg, one_zpow, div_one]⟩
    simpa only [K, Set.mem_preimage, map_div, map_zpow, Set.mem_Icc] using ⟨hn.1, hn.2.le⟩
  have heq := monoidHom_eq_one_of_compact_range_subset_ball q.toMonoidHom
    (himage ▸ hK.image q.continuous) (himage ▸ hq.image_subset)
  exact ContinuousMonoidHom.ext fun x => DFunLike.congr_fun heq x

/-- Paper: §3.1.1, p. 119. Every modulated group admits local norm-twist coordinates,
including when the complex exponent is defined globally only modulo a period. -/
theorem hasNormTwistCharts_of_proper [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) : HasNormTwistCharts m := by
  intro c
  obtain ⟨g, hg⟩ : ∃ g, 1 < m g := by
    obtain ⟨g, hg⟩ := hne
    rcases lt_or_gt_of_ne hg with h | h
    · exact ⟨g⁻¹, by simpa only [map_inv, one_lt_inv'] using h⟩
    · exact ⟨g, h⟩
  have hpos (x : G) : 0 < modℝ x :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero)
  let L (x : G) : ℂ := Real.log (modℝ x)
  have hLg : L g ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one (hpos g) fun h =>
      hg.ne (Units.val_inj.mp (NNReal.coe_inj.mp h)).symm)
  have hL : Continuous L := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp hm.continuous)).log
      fun x => (hpos x).ne')
  let twist (z : ℂ) : QuasiCharacter G :=
    c * { toFun := fun x => Complex.exp (L x * z)
          map_one' := by simp [L]
          map_mul' := by
            intro x y
            simp only [L, map_mul, Units.val_mul, NNReal.coe_mul,
              Real.log_mul (hpos x).ne' (hpos y).ne', Complex.ofReal_add, add_mul, Complex.exp_add]
          continuous_toFun := (hL.mul continuous_const).cexp }
  have htwist (z : ℂ) (x : G) : twist z x = c x * Complex.exp (L x * z) := rfl
  have htwist_cont : Continuous twist := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (c.continuous.comp continuous_snd).mul
      (((hL.comp continuous_snd).mul continuous_fst).cexp)
  have hneval (d : QuasiCharacter G) (x : G) : d x ≠ 0 := ((Group.isUnit x).map d).ne_zero
  -- Evaluation at g recovers the exponent using the principal logarithm.
  let ratio (d : QuasiCharacter G) : ℂ := d g / c g
  let expChart := Complex.expOpenPartialHomeomorph
  let coord (d : QuasiCharacter G) : ℂ := expChart.symm (ratio d) / L g
  let U := ratio ⁻¹' expChart.target
  let T := (L g * ·) ⁻¹' expChart.source
  have hratio : Continuous ratio := (continuous_eval_const g).div_const (c g)
  have hU : IsOpen U := expChart.open_target.preimage hratio
  have hcoord : ContinuousOn coord U :=
    (expChart.continuousOn_invFun.comp hratio.continuousOn (fun _ h => h)).div_const _
  have hscale (d : QuasiCharacter G) : L g * coord d = expChart.symm (ratio d) := by
    change L g * (expChart.symm (ratio d) / L g) = _
    rw [mul_comm, div_mul_cancel₀ _ hLg]
  let residual (d : QuasiCharacter G) :=
    d * (twist (coord d)).comp (ContinuousMonoidHom.inv G)
  have hresidual (d : QuasiCharacter G) (x : G) : residual d x = d x / twist (coord d) x := by
    change d x * twist (coord d) x⁻¹ = _
    rw [map_inv, div_eq_mul_inv]
  have hresidual_cont : ContinuousOn (fun d => (residual d).toContinuousMap) U := by
    have hforget : Continuous (ContinuousMonoidHom.toContinuousMap : QuasiCharacter G → C(G, ℂ)) :=
      (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
    have hinv := (ContinuousMonoidHom.inv G).continuous_comp_left (C := ℂ)
    exact hforget.continuousOn.mul
      ((hforget.comp hinv).comp_continuousOn' (htwist_cont.comp_continuousOn' hcoord))
  -- On the chart source the residual stays close to one on a compact norm interval.
  let K := m ⁻¹' Set.Icc 1 (m g)
  let V : Set C(G, ℂ) := {f | Set.MapsTo f K (Metric.ball 1 1)}
  let S := U ∩ (fun d => (residual d).toContinuousMap) ⁻¹' V
  have := nonnegRealUnits_orderTopology_and_compactIccSpace.2
  have hK : IsCompact K := hm.isCompact_preimage isCompact_Icc
  have hS : IsOpen S := hresidual_cont.isOpen_inter_preimage hU
    (ContinuousMap.isOpen_setOfPred_mapsTo hK Metric.isOpen_ball)
  have hratio_twist (z : ℂ) : ratio (twist z) = expChart (L g * z) := by
    change twist z g / c g = Complex.exp (L g * z)
    rw [htwist, mul_div_cancel_left₀ _ (hneval c g)]
  have hright (z : ℂ) (hz : z ∈ T) : coord (twist z) = z := by
    change expChart.symm (ratio (twist z)) / L g = z
    rw [hratio_twist, expChart.left_inv hz, mul_div_cancel_left₀ _ hLg]
  have hleft (d : QuasiCharacter G) (hd : d ∈ S) : twist (coord d) = d := by
    have hrg : residual d g = 1 := by
      have hval : twist (coord d) g = d g := by
        rw [htwist, hscale]
        change c g * expChart (expChart.symm (ratio d)) = d g
        rw [expChart.right_inv hd.1, mul_comm]
        exact div_mul_cancel₀ _ (hneval c g)
      rw [hresidual, hval, div_self (hneval d g)]
    have h := quasiCharacter_eq_one_of_normInterval m hK hg (residual d) hrg hd.2
    ext1 x
    have hx : residual d x = 1 := DFunLike.congr_fun h x
    exact ((div_eq_one_iff_eq (hneval _ x)).mp (hresidual d x ▸ hx)).symm
  let e : OpenPartialHomeomorph (QuasiCharacter G) ℂ := {
    toFun := coord
    invFun := twist
    source := S
    target := T
    map_source' d hd := by
      change L g * coord d ∈ expChart.source
      rw [hscale]
      exact expChart.map_target hd.1
    map_target' z hz := by
      refine ⟨?_, ?_⟩
      · change ratio (twist z) ∈ expChart.target
        rw [hratio_twist]
        exact expChart.map_source hz
      · intro x _
        change residual (twist z) x ∈ Metric.ball 1 1
        rw [hresidual, hright z hz, div_self (hneval _ x)]
        exact Metric.mem_ball_self zero_lt_one
    left_inv' := hleft
    right_inv' := hright
    open_source := hS
    open_target := expChart.open_source.preimage (continuous_const.mul continuous_id)
    continuousOn_toFun := hcoord.mono Set.inter_subset_left
    continuousOn_invFun := htwist_cont.continuousOn }
  have hzero : (0 : ℂ) ∈ T := by
    change L g * 0 ∈ expChart.source
    simp [expChart, Complex.expOpenPartialHomeomorph, Real.pi_pos]
  have htwist_zero : twist 0 = c := by
    ext1 x
    simp [htwist]
  refine ⟨e, htwist_zero ▸ e.map_target hzero, ?_, fun z _ x => ?_⟩
  · change coord c = 0
    rw [← htwist_zero, hright 0 hzero]
  · change twist z x = _
    rw [htwist, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos x).ne'),
      ← Complex.ofReal_log (hpos x).le]

/-- Paper: §3.1.1, p. 119. Choose one norm-twist chart around each point. These charts form
an atlas on the existing compact-open space. -/
@[instance_reducible] def quasiCharacterChartedSpace (h : HasNormTwistCharts m) :
    ChartedSpace ℂ (QuasiCharacter G) where
  atlas := Set.range fun c => (h c).choose
  chartAt c := (h c).choose
  mem_chart_source c := (h c).choose_spec.1
  chart_mem_atlas c := ⟨c, rfl⟩

/-- Paper: §3.1.1, p. 119. The atlas of complex norm-twist coordinates is analytic. -/
theorem quasiCharacter_isManifold (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    IsManifold 𝓘(ℂ) ω (QuasiCharacter G) := by
  let := quasiCharacterChartedSpace m h
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range (fun c => (h c).choose) at he
  change e' ∈ Set.range (fun c => (h c).choose) at he'
  obtain ⟨c, rfl⟩ := he
  obtain ⟨d, rfl⟩ := he'
  let e := (h c).choose
  let e' := (h d).choose
  have hc := (h c).choose_spec.2.2
  have hd := (h d).choose_spec.2.2
  change ContDiffOn ℂ ω (e.symm.trans e') ((e.symm.trans e').source ∩ Set.range id)
  rw [Set.range_id, Set.inter_univ]
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ e'.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  let w := e' (e.symm z)
  have hw : w ∈ e'.target := e'.map_source hz'.2
  have hbase (g : G) : c g * (modℝ g : ℂ) ^ z = d g * (modℝ g : ℂ) ^ w := by
    rw [← hc z hz'.1 g, ← hd w hw g]
    exact congrArg (fun q : QuasiCharacter G => q g) (e'.left_inv hz'.2).symm
  -- Adding the same increment to both coordinates twists both characters by the same power.
  let translate (y : ℂ) := w + (y - z)
  have hsmooth : ContDiff ℂ ω translate := contDiff_const.add (contDiff_id.sub contDiff_const)
  have hnear : translate ⁻¹' e'.target ∈ 𝓝 z :=
    (e'.open_target.preimage hsmooth.continuous).mem_nhds (by simpa [translate] using hw)
  refine hsmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnear]
    with y hy htranslate
  have hy' : y ∈ e.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy
    exact hy.1
  have heq : e.symm y = e'.symm (translate y) := by
    ext1 g
    have hmod : (modℝ g : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
    rw [hc y hy' g, hd (translate y) htranslate g]
    change c g * (modℝ g : ℂ) ^ y = d g * (modℝ g : ℂ) ^ (w + (y - z))
    rw [Complex.cpow_add _ _ hmod, ← mul_assoc, ← hbase g, mul_assoc,
      ← Complex.cpow_add _ _ hmod, show z + (y - z) = y by abel]
  change e' (e.symm y) = translate y
  rw [heq, e'.right_inv htranslate]

/-- Paper: Definition 3.1.1.1, p. 119. The abscissa is the real exponent in the modulus of
a quasi-character. We evaluate the ratio of logarithms at a point where the module differs from one.
Deviation: This formula computes (3.1.1.2) without choosing a unitary base-point. -/
def quasiCharacterAbscissa (_hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) : ℝ :=
  Real.log ‖c hne.choose‖ / Real.log (modℝ hne.choose)

/-- Paper: Equation (3.1.1.2), p. 119. Twisting any unitary character by the s-th power
of the module gives a quasi-character of abscissa Re(s). -/
theorem quasiCharacterAbscissa_of_unitary_twist (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (χ : PontryaginDual G) (s : ℂ)
    (hc : ∀ g, c g = (χ g : ℂ) * (modℝ g : ℂ) ^ s) :
    quasiCharacterAbscissa m hm hne c = s.re := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  change Real.log ‖c g‖ / Real.log (modℝ g) = s.re
  rw [hc g, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hmod,
    Real.log_rpow hmod, mul_div_cancel_right₀ _ hlog]

/-- Paper: Equation (3.1.1.2), p. 119. At every element of a modulated group, the modulus
of a quasi-character equals the module raised to its abscissa. -/
theorem norm_quasiCharacter_eq_rpow_abscissa [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (g : G) :
    ‖c g‖ = (modℝ g) ^ quasiCharacterAbscissa m hm hne c := by
  sorry

/-- Paper: Equation (3.1.1.2), p. 119. The abscissa is continuous in the compact-open topology. -/
theorem continuous_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Continuous (quasiCharacterAbscissa m hm hne) := by
  have hev : Continuous (fun c : QuasiCharacter G => c hne.choose) := continuous_eval_const _
  have hneval (c : QuasiCharacter G) : c hne.choose ≠ 0 :=
    ((Group.isUnit hne.choose).map c).ne_zero
  exact (hev.norm.log fun c => norm_ne_zero_iff.mpr (hneval c)).div_const _

/-- Paper: Equation (3.1.1.2), p. 119. Every real number occurs as an abscissa. -/
theorem surjective_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Surjective (quasiCharacterAbscissa m hm hne) := by
  sorry

/-- Paper: Definition 3.1.1.2(1), p. 119. The relative vertical strip over an interval is
the inverse image under the abscissa, with the topology inherited on its subtype.
Deviation: The same inverse image is defined for every real set. -/
def relativeVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    Set (QuasiCharacter G) :=
  quasiCharacterAbscissa m hm hne ⁻¹' I

/-- Paper: Definition 3.1.1.2(2), p. 119. The relative right half-plane has abscissa
strictly larger than its boundary. -/
def relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    TopologicalSpace.Opens (QuasiCharacter G) :=
  ⟨relativeVerticalStrip m hm hne (Set.Ioi a),
    isOpen_Ioi.preimage (continuous_quasiCharacterAbscissa m hm hne)⟩

/-- Paper: Definition 3.1.1.2(3), p. 119. The strip in the component indexed by ω also
requires the restriction of the quasi-character to the norm-one subgroup to equal ω. -/
def componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (χ : PontryaginDual m.ker) (I : Set ℝ) : Set (QuasiCharacter G) :=
  relativeVerticalStrip m hm hne I ∩ {c | ∀ g : m.ker, normOneRestriction m c g = (χ g : ℂ)}

/-- Paper: Definition 3.1.1.2(2), p. 119. The trivial character lies in the relative
right half-plane precisely when its boundary is strictly negative. -/
theorem one_mem_relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    1 ∈ relativeRightHalfPlane m hm hne a ↔ a < 0 := by
  change a < quasiCharacterAbscissa m hm hne 1 ↔ a < 0
  simp [quasiCharacterAbscissa]

/-- Paper: Definition 3.1.1.2, p. 119. The trivial character belongs to the strip in
the trivial component exactly when the interval contains zero. -/
theorem one_mem_componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    1 ∈ componentVerticalStrip m hm hne 1 I ↔ 0 ∈ I := by
  simp [componentVerticalStrip, relativeVerticalStrip, quasiCharacterAbscissa, normOneRestriction]

/-- Paper: Equation (3.1.1.4), p. 119. The dual quasi-character is the module times
the inverse character, evaluated by composing the original character with inversion. -/
def dualQuasiCharacter [IsTopologicalGroup G] (hm : Continuous m) (c : QuasiCharacter G) :
    QuasiCharacter G :=
  let n : QuasiCharacter G :=
    ⟨Complex.ofRealHom.toMonoidHom.comp (NNReal.toRealHom.toMonoidHom.comp
      ((Units.coeHom ℝ≥0).comp m)),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp hm))⟩
  n * c.comp (ContinuousMonoidHom.inv G)

/-- Paper: Equation (3.1.1.4), p. 119. Duality reflects the abscissa in the line σ = 1/2. -/
theorem quasiCharacterAbscissa_dual [IsTopologicalGroup G] (hm : IsProperMap m)
    (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    quasiCharacterAbscissa m hm hne (dualQuasiCharacter m hm.continuous c) =
      1 - quasiCharacterAbscissa m hm hne c := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  have hnorm : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  change Real.log ‖(modℝ g : ℂ) * c (g⁻¹)‖ / Real.log (modℝ g) =
    1 - Real.log ‖c g‖ / Real.log (modℝ g)
  rw [map_inv, ← div_eq_mul_inv, norm_div, Complex.norm_of_nonneg hmod.le,
    Real.log_div hmod.ne' hnorm, sub_div, div_self hlog]

/-- Paper: Equation (3.1.1.4), p. 119. The duality map is an analytic automorphism and
serves as its own inverse. -/
theorem dualQuasiCharacter_analyticEquiv [IsTopologicalGroup G] (hm : Continuous m)
    (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (QuasiCharacter G) (QuasiCharacter G) ω,
      (∀ c, e c = dualQuasiCharacter m hm c) ∧ ∀ c, e.symm c = dualQuasiCharacter m hm c := by
  sorry

end Generalities

section Ideles

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

variable (S : Finset (Primes(F)))

local notation "projectedDiagonal" =>
  Subgroup.map (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (MonoidHom.range (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

/-- Paper: Equation (3.1.2.1), p. 120. The group J_{F,S} is the quotient of the S-ideles
by the projected diagonal S-units. As in §A.1, S specifies the finite places only. -/
abbrev SIdeleQuotient := (SAdeleRing F S)ˣ ⧸ projectedDiagonal

/-- Paper: Equation (3.1.2.1), p. 120. An S-idele represents the identity of J_{F,S}
precisely when it is the projection of a diagonal S-unit. -/
theorem sIdeleQuotient_mk_eq_one (g : (SAdeleRing F S)ˣ) :
    (QuotientGroup.mk g : SIdeleQuotient F S) = 1 ↔
      ∃ u : ((S : Set (Primes(F))).integer F)ˣ, g = Units.map
        ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom
        (Units.map (integralAdeleDiagonal F S).toMonoidHom u) := by
  rw [QuotientGroup.eq_one_iff, MonoidHom.map_range, MonoidHom.mem_range]
  exact exists_congr fun _ ↦ eq_comm

/-- Paper: Equation (3.1.2.1), p. 120. The product of normalized absolute values in S
descends to J_{F,S} by the S-unit product formula. -/
def sIdeleQuotientNorm : SIdeleQuotient F S →* ℝ≥0ˣ :=
  QuotientGroup.lift _ (sIdeleNorm F S)
    (Subgroup.map_le_iff_le_comap.mpr (sIdeleNorm_spec F S).2)

/-- Paper: Equation (3.1.2.1), p. 120. The norm on J_{F,S} takes the S-idelic norm of
any representative. -/
theorem sIdeleQuotientNorm_mk (g : (SAdeleRing F S)ˣ) :
    sIdeleQuotientNorm F S (QuotientGroup.mk g) = sIdeleNorm F S g := by
  rfl

-- TODO(paper-gap): Theorem A.1.5.2 gives compactness for the norm-one part of C_{F,S}.
-- Applying it to J_{F,S} requires projecting away the integer units outside S.

/-- Paper: §3.1.2, p. 120. The norm on J_{F,S} is proper. In particular its fiber over
one is compact. -/
theorem isProperMap_sIdeleQuotientNorm : IsProperMap (sIdeleQuotientNorm F S) := by
  sorry

/-- Paper: §3.1.2.3, p. 121. The S-idelic norm admits a continuous homomorphic section,
as used to parametrize the components in (3.1.2.5). -/
theorem sIdeleQuotientNorm_exists_section :
    ∃ σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S, RightInverse σ (sIdeleQuotientNorm F S) := by
  sorry

/-- Paper: §3.1.2, p. 120. The global idele class norm is a proper module. -/
theorem isProperMap_ideleClassNorm : IsProperMap (ideleClassNorm F) := by
  sorry

/-- Paper: §3.1.2, p. 120. The global idelic module supplies complex exponent charts on
the space of Hecke characters. -/
theorem ideleClass_hasNormTwistCharts : HasNormTwistCharts (ideleClassNorm F) := by
  sorry

/-- Paper: Equation (3.1.2.4), p. 121. Inserting the multiplicative group of a finite completion and
passing to idele classes is continuous. -/
theorem continuous_ideleClass_ofAdicCompletion (v : Primes(F)) :
    Continuous (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) := by
  sorry

/-- Paper: Equation (3.1.2.4), p. 121. Inserting an infinite local multiplicative group
into the idele class group is continuous. -/
theorem continuous_ideleClass_ofCompletion (w : InfinitePlace F) :
    Continuous (IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  sorry

/-- Paper: Equation (3.1.2.4), p. 121. Restriction at a finite place is precomposition
with insertion in that coordinate followed by passage to idele classes. -/
def finitePlaceRestriction (v : Primes(F)) (c : HeckeCharacter (𝓞 F) F) :
    QuasiCharacter (v.adicCompletion F)ˣ :=
  c.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩

/-- Paper: Equation (3.1.2.4), p. 121. Restriction at an infinite place is precomposition
with insertion in that coordinate followed by passage to idele classes. -/
def infinitePlaceRestriction (w : InfinitePlace F) (c : HeckeCharacter (𝓞 F) F) :
    QuasiCharacter w.Completionˣ :=
  c.comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩

/-- Paper: §3.1.2, p. 120. The value of a global character is the product of its local
values on an idele. Only finitely many finite-place factors differ from one. -/
theorem heckeCharacter_eq_prod_restrictions (c : HeckeCharacter (𝓞 F) F)
    (g : IdeleGroup (𝓞 F) F) :
    let a := fun w : InfinitePlace F => infinitePlaceRestriction F w c
      (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom g)
    let b := fun v : Primes(F) => finitePlaceRestriction F v c
      (Units.map ((RestrictedProduct.evalRingHom (fun w : Primes(F) => w.adicCompletion F) v).comp
        (RingHom.snd _ _)).toMonoidHom g)
    b.HasFiniteMulSupport ∧ c (QuotientGroup.mk g) = (∏ w, a w) * ∏ᶠ v, b v := by
  sorry

local notation "finiteNorm" => Units.map nnNormHom.toMonoidHom
local notation "infiniteNorm(" w ")" => (Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w

-- TODO(paper-gap): At a finite place the section in (3.1.2.2) must be taken over the
-- value group q^ℤ. The absolute value has no right inverse on all positive reals.

/-- Paper: Equation (3.1.2.2), p. 120. The finite-place surface is a cylinder for each
character of the local integer units. In exponent coordinates a uniformizer contributes q⁻ˢ.
Deviation: The auxiliary character of the discrete value group is specified by its value b
at the module of the chosen uniformizer. The coordinate equations specify the biholomorphism. -/
theorem finitePlace_quasiCharacterParametrization (v : Primes(F)) (π : (v.adicCompletion F)ˣ)
    (hπ : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹) (b : ℂˣ) :
    let q : ℝ := v.asIdeal.absNorm
    let periods := AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I / (Real.log q : ℂ))
    ∃ e : QuasiCharacter (v.adicCompletion F)ˣ ≃ₜ
        ((ℂ ⧸ periods) × PontryaginDual (v.adicCompletionIntegers F)ˣ),
      ∀ c, (∀ s : ℂ, (e c).1 = QuotientAddGroup.mk s ↔ c π = (b : ℂ) * (q : ℂ) ^ (-s)) ∧
        ∀ u, ((e c).2 u : ℂ) = c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) := by
  sorry

/-- Paper: Equation (3.1.2.2), p. 120. At a finite place the locally defined complex
exponent is a chart for the normalized absolute value. -/
theorem finitePlace_hasNormTwistCharts (v : Primes(F)) :
    HasNormTwistCharts (finiteNorm : (v.adicCompletion F)ˣ →* ℝ≥0ˣ) := by
  sorry

/-- Paper: Equation (3.1.2.3), p. 121. A continuous splitting of the normalized absolute
value identifies the surface with a complex plane for each character of the norm-one group.
Deviation: We use the norm-one kernel specified below (3.1.2.3) for its archimedean unit
group. We state the homeomorphism with the coordinate formulas that determine its analytic maps. -/
theorem infinitePlace_quasiCharacterParametrization (w : InfinitePlace F)
    (σ : ℝ≥0ˣ →ₜ* w.Completionˣ) (hσ : RightInverse σ (infiniteNorm(w))) :
    let n : w.Completionˣ →* ℝ≥0ˣ := infiniteNorm(w)
    ∃ e : QuasiCharacter w.Completionˣ ≃ₜ (ℂ × PontryaginDual n.ker), ∀ c,
      (∀ t : ℝ≥0ˣ, c (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ (e c).1) ∧
        ∀ u : n.ker, ((e c).2 u : ℂ) = c u.val := by
  sorry

/-- Paper: Equation (3.1.2.3), p. 121. At an infinite place the normalized absolute value
gives complex exponent charts. Its multiplicity is one at real places and two at complex places. -/
theorem infinitePlace_hasNormTwistCharts (w : InfinitePlace F) :
    HasNormTwistCharts (infiniteNorm(w) : w.Completionˣ →* ℝ≥0ˣ) := by
  sorry

/-- Paper: §3.1.2, p. 120. Equip the Hecke characters with the norm-twist atlas. -/
scoped instance heckeCharacterChartedSpace : ChartedSpace ℂ (HeckeCharacter (𝓞 F) F) :=
  quasiCharacterChartedSpace _ (ideleClass_hasNormTwistCharts F)

/-- Paper: Lemma 3.1.2.1, p. 121. Restriction to a finite completion is a local
complex analytic isomorphism in the norm-twist atlases. -/
theorem finitePlaceRestriction_isLocalDiffeomorph (v : Primes(F)) :
    letI := quasiCharacterChartedSpace _ (finitePlace_hasNormTwistCharts F v)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (finitePlaceRestriction F v) := by
  sorry

/-- Paper: Lemma 3.1.2.1, p. 121. Restriction to an infinite completion is a local
complex analytic isomorphism in the norm-twist atlases. -/
theorem infinitePlaceRestriction_isLocalDiffeomorph (w : InfinitePlace F) :
    letI := quasiCharacterChartedSpace _ (infinitePlace_hasNormTwistCharts F w)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (infinitePlaceRestriction F w) := by
  sorry

/-- Paper: Equation (3.1.2.5), p. 121. A continuous splitting of the S-idelic norm
identifies the surface with a complex plane for each character of its norm-one subgroup.
Deviation: We give the homeomorphism with its analytic coordinates fixed by evaluation along
the splitting and restriction to the kernel. -/
theorem sIdeleQuotient_quasiCharacterParametrization (σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (hσ : RightInverse σ (sIdeleQuotientNorm F S)) :
    let n := sIdeleQuotientNorm F S
    ∃ e : QuasiCharacter (SIdeleQuotient F S) ≃ₜ (ℂ × PontryaginDual n.ker), ∀ c,
      (∀ t : ℝ≥0ˣ, c (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ (e c).1) ∧
        ∀ u : n.ker, ((e c).2 u : ℂ) = c u.val := by
  sorry

/-- Paper: Equation (3.1.2.5), p. 121. The S-idelic module gives complex exponent
charts on the space of quasi-characters of J_{F,S}. -/
theorem sIdeleQuotient_hasNormTwistCharts : HasNormTwistCharts (sIdeleQuotientNorm F S) := by
  sorry

local notation "LocalIntegers(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "LocalUnits(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v)ˣ

open scoped NumberField.AdeleRing in
/-- Send a family of local integer units to its idele class, with all infinite
coordinates equal to one. -/
private def finiteIntegerUnitInsertion : (∀ v : Primes(F), LocalUnits(v)) →ₜ* IdeleClassGroup (𝓞 F) F :=
  let f : (∀ v : Primes(F), LocalIntegers(v)) →* AdeleRing (𝓞 F) F :=
    (1 : _ →* InfiniteAdeleRing F).prod
      { toFun := RestrictedProduct.structureMap (fun v : Primes(F) => v.adicCompletion F)
          (fun v => (LocalIntegers(v) : Set (v.adicCompletion F))) Filter.cofinite
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  ⟨(QuotientGroup.mk' _).comp ((Units.map f).comp
    (ContinuousMulEquiv.piUnits.symm : (∀ v : Primes(F), LocalUnits(v)) ≃ₜ* _).toMonoidHom),
    QuotientGroup.continuous_mk.comp
      ((continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous).units_map f
        |>.comp (ContinuousMulEquiv.piUnits.symm : (∀ v : Primes(F), LocalUnits(v)) ≃ₜ* _).continuous)⟩

/-- On a family supported at one finite place, the product insertion agrees with
Mathlib's insertion at that place. -/
private theorem finiteIntegerUnitInsertion_mulSingle (v : Primes(F)) (u : LocalUnits(v)) :
    letI := Classical.decEq (Primes(F))
    finiteIntegerUnitInsertion F (Pi.mulSingle v u) =
      IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (Units.map (LocalIntegers(v)).subtype.toMonoidHom u) := by
  let _ := Classical.decEq (Primes(F))
  apply congrArg (QuotientGroup.mk : IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F)
  apply Units.ext
  refine Prod.ext rfl ?_
  apply RestrictedProduct.ext
  intro w
  change (((Pi.mulSingle v u : ∀ w : Primes(F), LocalUnits(w)) w).val : w.adicCompletion F) =
    RestrictedProduct.mulSingle (fun w : Primes(F) => LocalIntegers(w)) v
      (u.val : v.adicCompletion F) w
  rcases eq_or_ne w v with rfl | hw
  · rw [Pi.mulSingle_eq_same]
    exact (RestrictedProduct.mulSingle_eq_same _ _ _).symm
  · rw [Pi.mulSingle_eq_of_ne hw]
    exact (RestrictedProduct.mulSingle_eq_of_ne _ _ hw).symm

/-- Paper: Equation (3.1.2.6), p. 121. The global quasi-characters trivial on the
local integer units at every finite place outside S form an open set. -/
theorem isOpen_unramifiedOutside :
    IsOpen {c : HeckeCharacter (𝓞 F) F | ∀ v ∉ S, c.IsUnramifiedAt v} := by
  classical
  have (v : Primes(F)) : CompactSpace (LocalUnits(v)) := by
    have := compactSpace_adicCompletionIntegers (K := F) v
    exact compactSpace_units_of_compactSpace _
  let cut : (∀ v : Primes(F), LocalUnits(v)) →ₜ* (∀ v : Primes(F), LocalUnits(v)) :=
    ⟨{ toFun := fun u v => if v ∈ S then 1 else u v
       map_one' := by
         funext v
         simp
       map_mul' := fun u w => by
         funext v
         by_cases hv : v ∈ S <;> simp [hv] },
      continuous_pi fun v => by
        by_cases hv : v ∈ S
        · simpa only [hv, ite_true] using continuous_const
        · simpa only [hv, ite_false] using continuous_apply v⟩
  let i := (finiteIntegerUnitInsertion F).comp cut
  have hl (c : HeckeCharacter (𝓞 F) F) (v : Primes(F)) :
      c.IsUnramifiedAt v ↔
        ∀ u : LocalUnits(v), c (finiteIntegerUnitInsertion F (Pi.mulSingle v u)) = 1 := by
    simp only [HeckeCharacter.isUnramifiedAt_iff, finiteIntegerUnitInsertion_mulSingle]
    refine forall_congr' fun u => ?_
    change c.restrict v ↑(Units.map (LocalIntegers(v)).subtype.toMonoidHom u) = 1 ↔ _
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hsingle (v : Primes(F)) (u : LocalUnits(v)) :
      cut (Pi.mulSingle v u) = if v ∈ S then 1 else (Pi.mulSingle v u : ∀ w : Primes(F), LocalUnits(w)) := by
    funext w
    change (if w ∈ S then 1 else (Pi.mulSingle v u : ∀ w : Primes(F), LocalUnits(w)) w) = _
    rcases eq_or_ne w v with rfl | h
    · by_cases hv : w ∈ S <;> simp [hv]
    · by_cases hv : v ∈ S <;> simp [hv, Pi.mulSingle_eq_of_ne h]
  have hset : {c : HeckeCharacter (𝓞 F) F | ∀ v ∉ S, c.IsUnramifiedAt v} =
      (fun c => c.comp i) ⁻¹' {1} := by
    ext c
    change (∀ v ∉ S, c.IsUnramifiedAt v) ↔ c.comp i = 1
    simp only [hl]
    constructor
    · intro hc
      ext1 u
      change c (i u) = 1
      -- Finite products of the single-coordinate families converge to the full family.
      have hp : HasProd (fun v => Pi.mulSingle v (u v)) u := by
        refine Pi.hasProd.mpr fun w => ?_
        convert hasProd_ite_eq w (u w) using 1
        funext v
        rcases eq_or_ne v w with rfl | hv
        · simp
        · simp [hv]
      have hmap := hp.map (c.comp i) (c.comp i).continuous
      refine hmap.unique (hasProd_one.congr_fun fun v => ?_)
      change c (finiteIntegerUnitInsertion F (cut (Pi.mulSingle v (u v)))) = 1
      rw [hsingle]
      by_cases hv : v ∈ S
      · simp [hv]
      · simpa [hv] using hc v hv (u v)
    · intro hc v hv u
      have h := DFunLike.congr_fun hc (Pi.mulSingle v u)
      change c (finiteIntegerUnitInsertion F (cut (Pi.mulSingle v u))) = 1 at h
      simpa [hsingle, hv] using h
  rw [hset]
  exact isOpen_singleton_one_complex.preimage i.continuous_comp_left

/-- Paper: Equation (3.1.2.6), p. 121. The open subspace Ω_S(C_F) consists of the
Hecke characters unramified at every finite place outside S. -/
def unramifiedOutside : TopologicalSpace.Opens (HeckeCharacter (𝓞 F) F) :=
  ⟨{c | ∀ v ∉ S, c.IsUnramifiedAt v}, isOpen_unramifiedOutside F S⟩

/-- Paper: Equation (3.1.2.6), p. 121. Membership in Ω_S is equivalent to triviality
of the continuous local restrictions on all integer units outside S. -/
theorem mem_unramifiedOutside_iff (c : HeckeCharacter (𝓞 F) F) :
    c ∈ unramifiedOutside F S ↔ ∀ v ∉ S, ∀ u : (v.adicCompletionIntegers F)ˣ,
      finitePlaceRestriction F v c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 := by
  change (∀ v ∉ S, c.IsUnramifiedAt v) ↔ _
  simp only [HeckeCharacter.isUnramifiedAt_iff]
  refine forall_congr' fun v => imp_congr_right fun _ => forall_congr' fun u => ?_
  change c.restrict v ↑(Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 ↔ _
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  rfl

/-- Paper: Equations (3.1.2.7)–(3.1.2.8), p. 121. Insert an S-idele into the full idele
group by multiplying its single-coordinate insertions over S, including all infinite places. -/
def sIdeleInsertion : (SAdeleRing F S)ˣ →* IdeleGroup (𝓞 F) F :=
  (∏ w : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F w).comp
    (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom)) *
  ∏ v : S, (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val).comp
    (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom)

/-- Paper: Equation (3.1.2.8), p. 121. The inserted idele has the given components in S
and component one at every finite place outside S. -/
theorem sIdeleInsertion_apply (g : (SAdeleRing F S)ˣ) :
    (sIdeleInsertion F S g).val.1 = g.val.1 ∧
    (∀ v : S, (sIdeleInsertion F S g).val.2 v.val = g.val.2 v) ∧
    ∀ v ∉ S, (sIdeleInsertion F S g).val.2 v = 1 := by
  classical
  have hfinite (v : Primes(F)) :
      (sIdeleInsertion F S g).val.2 v =
        ∏ u : S, (FiniteAdeleRing.ofAdicCompletion F u.val (g.val.2 u)) v := by
    let eval : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      RestrictedProduct.evalRingHom _ v
    change eval (sIdeleInsertion F S g).val.2 =
      ∏ u : S, eval (FiniteAdeleRing.ofAdicCompletion F u.val (g.val.2 u))
    rw [← map_prod]
    apply congrArg eval
    simp [sIdeleInsertion, MonoidHom.finsetProd_apply, AdeleRing, Prod.snd_prod]
  refine ⟨?_, ?_, ?_⟩
  · simp [sIdeleInsertion, MonoidHom.finsetProd_apply, AdeleRing, Prod.fst_prod,
      InfiniteAdeleRing.ofCompletion]
    exact Finset.univ_prod_mulSingle g.val.1
  · intro v
    rw [hfinite, Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
    · exact RestrictedProduct.mulSingle_eq_same _ _ _
    · intro u _ huv
      have h : v.val ≠ u.val := fun h => huv (Subtype.ext h.symm)
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ h
  · intro v hv
    rw [hfinite]
    apply Finset.prod_eq_one
    intro u _
    have h : v ≠ u.val := fun h => hv (h ▸ u.property)
    exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

/-- Paper: Equation (3.1.2.7), p. 121. Extension by one is a closed topological embedding. -/
theorem isClosedEmbedding_sIdeleInsertion : IsClosedEmbedding (sIdeleInsertion F S) := by
  sorry

local notation "pullbackS(" c ")" => MonoidHom.comp (ContinuousMonoidHom.toMonoidHom c)
  (MonoidHom.comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)) (sIdeleInsertion F S))

/-- Paper: Equation (3.1.2.9), p. 121. For a character unramified outside S, pullback
along insertion kills the projected diagonal S-units. -/
theorem sIdeleRestriction_descent (c : unramifiedOutside F S) :
    projectedDiagonal ≤ (pullbackS(c.val)).ker := by
  sorry

/-- Paper: Equation (3.1.2.9), p. 121. The S-local restriction is the quotient lift of
the pullback from idele classes. Its domain carries the open subspace topology. -/
def sIdeleRestriction (c : unramifiedOutside F S) : QuasiCharacter (SIdeleQuotient F S) :=
  ⟨QuotientGroup.lift _ (pullbackS(c.val)) (sIdeleRestriction_descent F S c),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (c.val.continuous.comp (QuotientGroup.continuous_mk.comp
        (isClosedEmbedding_sIdeleInsertion F S).continuous))⟩

/-- Paper: Equation (3.1.2.9), p. 121. On an S-idele representative, the restriction
evaluates the original character on the class of the inserted idele. -/
theorem sIdeleRestriction_mk (c : unramifiedOutside F S) (g : (SAdeleRing F S)ˣ) :
    sIdeleRestriction F S c (QuotientGroup.mk g) = c.val (QuotientGroup.mk (sIdeleInsertion F S g)) := by
  sorry

/-- Paper: Lemma 3.1.2.2, p. 121. Every quasi-character of J_{F,S} extends to an
idele class character unramified outside S. -/
theorem sIdeleRestriction_surjective : Surjective (sIdeleRestriction F S) := by
  sorry

/-- Paper: Lemma 3.1.2.2, p. 121. Restriction from the open unramified locus to the
S-idelic character surface is a local complex analytic isomorphism. -/
theorem sIdeleRestriction_isLocalDiffeomorph :
    letI := quasiCharacterChartedSpace _ (sIdeleQuotient_hasNormTwistCharts F S)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (sIdeleRestriction F S) := by
  sorry

/-- Paper: §3.1.2.3, p. 122. As S varies, the open loci of characters unramified
outside S cover the entire space of Hecke characters. -/
theorem iUnion_unramifiedOutside :
    (⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set (HeckeCharacter (𝓞 F) F))) = Set.univ := by
  sorry

end Ideles

end RiemannMasullo
