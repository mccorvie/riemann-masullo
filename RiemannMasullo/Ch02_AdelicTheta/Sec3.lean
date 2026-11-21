module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1

import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Group.FunctionSeries
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# S-local adelic theta functions

Masullo, §2.3, pp. 98–106. As in §A.1.5, the place set is represented by
its finite part from Notation 2.3.1.1. All archimedean places are included
in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Uₛ" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)
local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "normℝ" => fun (g : Iₛ) ↦ valueℝ (sIdeleNorm F S g)
local notation "thetaTerm" => fun (f : ℬₛ) (ξ : Uₛ) (g : Iₛ) ↦
  f (Multiplicative.ofAdd (Units.val (unitAtS ξ * g)))
local notation "thetaSum" => fun (f : ℬₛ) (g : Iₛ) ↦ ∑' ξ : Uₛ, thetaTerm f ξ g

/-! ## S-local theta operators -/

section Summability

open scoped Classical

local notation "A∞" => mixedEmbedding.mixedSpace F
set_option quotPrecheck false in
local notation "Aᶠₛ" => (∀ v : S, HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "arch" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "sDiagonal" =>
  RingHom.comp (RingHom.comp (adeleProjection F S) (Subring.subtype (integralAdelesOutside F S)))
    (integralAdeleDiagonal F S)

omit [NumberField F] in
/-- The real and complex coordinates give a topological embedding of the infinite adeles. -/
private theorem isEmbedding_thetaArch : IsEmbedding (arch : InfiniteAdeleRing F → A∞) := by
  let e : InfiniteAdeleRing F ≃ₜ A∞ :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans <|
      Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex)))
  exact e.isEmbedding

/-- A compact set of finite S-adeles fits in a compact additive subgroup. -/
private theorem finiteSAdele_exists_compact_addSubgroup (C : Set Aᶠₛ) (hC : IsCompact C) :
    ∃ H : AddSubgroup Aᶠₛ, IsCompact (H : Set Aᶠₛ) ∧ C ⊆ H := by
  classical
  have hBound (v : S) : ∃ r : ℝ, ∀ x ∈ C, ‖x v‖ ≤ r :=
    hC.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  choose r hr using hBound
  let H : AddSubgroup Aᶠₛ :=
    { carrier := {x | ∀ v, ‖x v‖ ≤ max (r v) 0}
      zero_mem' := fun v ↦ by simp
      add_mem' := fun hx hy v ↦
        (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx v) (hy v))
      neg_mem' := fun hx v ↦ by simpa only [Pi.neg_apply, norm_neg] using hx v }
  refine ⟨H, ?_, fun x hx v ↦ (hr v x hx).trans (le_max_left _ _)⟩
  change IsCompact {x : Aᶠₛ | ∀ v, ‖x v‖ ≤ max (r v) 0}
  let balls (v : S) := Metric.closedBall (0 : v.val.adicCompletion F) (max (r v) 0)
  have heq : {x : Aᶠₛ | ∀ v, ‖x v‖ ≤ max (r v) 0} = Set.univ.pi balls := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, balls,
      Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact isCompact_univ_pi fun v ↦ by
    let := properSpace_adicCompletion v.val (K := F)
    exact isCompact_closedBall _ _

/-- Restricting the finite coordinates of diagonal S-integers to a compact additive
subgroup puts their archimedean images in a discrete integral lattice. -/
private theorem sInteger_arch_discrete_lattice (H : AddSubgroup Aᶠₛ)
    (hH : IsCompact (H : Set Aᶠₛ)) :
    ∃ L : Submodule ℤ A∞, DiscreteTopology L ∧
      ∀ x : (S : Set (HeightOneSpectrum (𝓞 F))).integer F,
        (sDiagonal x).2 ∈ H → arch (sDiagonal x).1 ∈ L := by
  let d := sDiagonal
  let D := d.toAddMonoidHom.range
  obtain ⟨_, hClosed, hDiscrete, _⟩ := sAdele_additive_quotient F S
  let l : InfiniteAdeleRing F × H → Aₛ := fun x ↦ (x.1, x.2.val)
  have hl : Continuous l := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hli : Injective l := fun _ _ h ↦
    Prod.ext (congrArg (Prod.fst : Aₛ → _) h) (Subtype.ext (congrArg (Prod.snd : Aₛ → _) h))
  let D' : Set (InfiniteAdeleRing F × H) := l ⁻¹' (D : Set Aₛ)
  have hD' : IsClosed D' := hClosed.preimage hl
  have : DiscreteTopology D' := isDiscrete_iff_discreteTopology.mp
    (hDiscrete.preimage hl.continuousOn hli)
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  -- Projection away from the compact finite factor is closed.
  let p : D' → InfiniteAdeleRing F := fun x ↦ x.val.1
  have hp : IsClosedEmbedding p := .of_continuous_injective_isClosedMap
    (continuous_fst.comp continuous_subtype_val) (by
      intro x y hxy
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have hab : a = b := Subtype.ext ((algebraMap F w.Completion).injective
        (show algebraMap F w.Completion a.val = algebraMap F w.Completion b.val from
          ((congrArg (fun z : Aₛ ↦ z.1 w) ha).trans
            ((congrFun hxy w).trans (congrArg (fun z : Aₛ ↦ z.1 w) hb).symm))))
      exact Subtype.ext (hli (ha.symm.trans (hab ▸ hb))))
    (isClosedMap_fst_of_compactSpace.comp hD'.isClosedMap_subtype_val)
  let L := ((D ⊓ H.comap (AddMonoidHom.snd _ _)).map
    ((arch).toAddMonoidHom.comp (AddMonoidHom.fst _ _))).toIntSubmodule
  refine ⟨L, ?_, fun x hx ↦ ⟨d x, ⟨⟨x, rfl⟩, hx⟩, rfl⟩⟩
  have hRange : Set.range (arch ∘ p) = (L : Set A∞) := by
    ext z
    constructor
    · rintro ⟨⟨⟨a, b⟩, h⟩, rfl⟩
      exact ⟨(a, b.val), ⟨h, b.property⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨h, hb⟩, rfl⟩
      exact ⟨⟨(a, ⟨b, hb⟩), h⟩, rfl⟩
  exact SetLike.isDiscrete_iff_discreteTopology.mp
    (hRange ▸ ((isEmbedding_thetaArch F).comp hp.isEmbedding).isInducing.isDiscrete_range)

/-- Paper: Proposition 2.3.1.2(1), p. 100. An S-adelic Schwartz–Bruhat function
vanishes outside a compact set of finite coordinates. Its absolute value times
any power of the archimedean norm is bounded on the whole S-adele ring. -/
theorem sAdeleSchwartz_exists_decay_bound (f : ℬₛ) :
    ∃ C : Set Aᶠₛ, IsCompact C ∧
      (∀ x : Aₛ, x.2 ∉ C → f (Multiplicative.ofAdd x) = 0) ∧
      ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ x : Aₛ, ‖f (Multiplicative.ofAdd x)‖ * ‖arch x.1‖ ^ N ≤ B := by
  sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. The series of norms of the
S-unit translates is summable uniformly on each compact set of S-ideles. -/
theorem sLocalAdelicTheta_summableUniformlyOn_norm (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    SummableUniformlyOn (fun (ξ : Uₛ) (g : Iₛ) ↦ ‖thetaTerm f ξ g‖) K := by
  classical
  obtain ⟨C, hC, hsupport, hdecay⟩ := sAdeleSchwartz_exists_decay_bound F S f
  -- Undo the idele translates on the finite support simultaneously.
  let T : Aᶠₛ × Iₛ → Aᶠₛ := fun p ↦ p.1 * (p.2⁻¹).val.2
  have hT : Continuous T := continuous_fst.mul
    (continuous_snd.comp (Units.continuous_val.comp (continuous_inv.comp continuous_snd)))
  obtain ⟨H, hH, hTH⟩ :=
    finiteSAdele_exists_compact_addSubgroup F S (T '' (C ×ˢ K)) ((hC.prod hK).image hT)
  obtain ⟨L, hL, hmemL⟩ := sInteger_arch_discrete_lattice F S H hH
  let N := Module.finrank ℤ L + 1
  obtain ⟨B, _, hB⟩ := hdecay N
  let d (ξ : Uₛ) : Aₛ := sDiagonal ξ.val
  let P : Set Uₛ := {ξ | (d ξ).2 ∈ H}
  let toL (ξ : P) : L := ⟨arch (d ξ.val).1, hmemL ξ.val.val ξ.property⟩
  have hToL : Injective toL := by
    intro ξ η h
    have heq := (arch).injective (congrArg Subtype.val h)
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact Subtype.ext (Units.ext (Subtype.ext ((algebraMap F w.Completion).injective
      (congrFun heq w))))
  have hs : Summable (P.indicator (fun ξ ↦ ‖arch (d ξ).1‖⁻¹ ^ N)) := by
    apply summable_subtype_iff_indicator.mp
    change Summable ((fun z : L ↦ ‖z‖⁻¹ ^ N) ∘ toL)
    exact (ZLattice.summable_norm_pow_inv L N (Nat.lt_succ_self _)).comp_injective hToL
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (((isEmbedding_thetaArch F).continuous.comp
      (continuous_fst.comp (Units.continuous_val.comp continuous_inv))).continuousOn :
      ContinuousOn (fun g : Iₛ ↦ arch (g⁻¹).val.1) K)
  let R := max M 1
  have hR : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
  refine HasSumUniformlyOn.summableUniformlyOn
    (hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
      (tendstoUniformlyOn_tsum (hs.mul_left (B * R ^ N)) ?_))
  intro ξ g hg
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  let y : Aₛ := (unitAtS ξ * g).val
  have hy : y = d ξ * g.val := rfl
  have hd : d ξ = y * (g⁻¹).val := by
    rw [hy, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  by_cases hξ : ξ ∈ P
  · rw [Set.indicator_of_mem hξ, inv_pow, ← div_eq_mul_inv]
    have hpos : 0 < ‖arch (d ξ).1‖ := by
      apply norm_pos_iff.mpr
      exact (Units.map ((arch).toMonoidHom.comp (RingHom.fst _ _).toMonoidHom)
        (unitAtS ξ)).ne_zero
    apply (le_div_iff₀ (pow_pos hpos _)).mpr
    have hnorm : ‖arch (d ξ).1‖ ≤ ‖arch y.1‖ * R := by
      rw [hd, Prod.fst_mul, map_mul]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ((hM g hg).trans (le_max_left _ _)) (norm_nonneg _))
    calc
      ‖f (Multiplicative.ofAdd y)‖ * ‖arch (d ξ).1‖ ^ N
          ≤ ‖f (Multiplicative.ofAdd y)‖ * (‖arch y.1‖ * R) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (norm_nonneg _)
      _ = (‖f (Multiplicative.ofAdd y)‖ * ‖arch y.1‖ ^ N) * R ^ N := by
        rw [mul_pow, mul_assoc]
      _ ≤ B * R ^ N := mul_le_mul_of_nonneg_right (hB y) (pow_nonneg hR _)
  · have hyC : y.2 ∉ C := by
      intro h
      apply hξ
      change (d ξ).2 ∈ H
      rw [hd]
      exact hTH ⟨(y.2, g), ⟨h, hg⟩, rfl⟩
    change ‖f (Multiplicative.ofAdd y)‖ ≤
      (B * R ^ N) * P.indicator (fun ξ ↦ ‖arch (d ξ).1‖⁻¹ ^ N) ξ
    rw [hsupport y hyC, norm_zero, Set.indicator_of_notMem hξ, mul_zero]

end Summability

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit series converges
uniformly to its sum on each compact set of S-ideles. -/
theorem sLocalAdelicTheta_hasSumUniformlyOn (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    HasSumUniformlyOn (thetaTerm f) (thetaSum f) K := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit sum is a continuous
function of the S-idele. -/
theorem sLocalAdelicTheta_continuous (f : ℬₛ) : Continuous (thetaSum f) := by sorry

/-- Paper: Definition 2.3.1.1, p. 99. Forming the continuous S-unit sum
is complex linear in the test function. -/
theorem sLocalAdelicTheta_isLinear :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨thetaSum f, sLocalAdelicTheta_continuous F S f⟩ : C(Iₛ, ℂ))) :=
  by sorry

/-- Paper: Definition 2.3.1.1, p. 99. The S-local theta operator sums the
test function over the diagonal S-unit multiples of each S-idele. -/
def sLocalAdelicTheta : ℬₛ →ₗ[ℂ] C(Iₛ, ℂ) :=
  IsLinearMap.mk' _ (sLocalAdelicTheta_isLinear F S)

/-- Paper: Equation (2.3.1.2), p. 99. Evaluating S-local theta at an idele
gives the sum of the evaluations at its S-unit multiples. -/
theorem sLocalAdelicTheta_apply (f : ℬₛ) (g : Iₛ) :
    sLocalAdelicTheta F S f g = thetaSum f g := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. S-local theta is invariant under
left translation by S-units, expressed as constancy on each class fiber. -/
theorem sLocalAdelicTheta_factorsThrough (f : ℬₛ) :
    FactorsThrough (sLocalAdelicTheta F S f) classOf := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit invariant theta
function descends to a continuous function on the S-idele classes. -/
def sLocalAdelicThetaOnClasses (f : ℬₛ) : C(Jₛ, ℂ) :=
  IsQuotientMap.lift (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk _) (sLocalAdelicTheta F S f)
    (sLocalAdelicTheta_factorsThrough F S f)

/-- Paper: Proposition 2.3.1.2(1), p. 100. The descended function at the
class of an S-idele agrees with theta at that S-idele. -/
theorem sLocalAdelicThetaOnClasses_mk (f : ℬₛ) (g : Iₛ) :
    sLocalAdelicThetaOnClasses F S f (classOf g) = sLocalAdelicTheta F S f g := by sorry

-- TODO(paper-gap): The support argument before (2.3.1.5) bounds only the finite
-- coordinates. On p. 104 the argument also switches to test functions on the
-- finite unit groups, where restrictions of additive test functions need not
-- have compact support.
-- TODO(paper-gap): The equality in (2.3.1.9) assumes that a section of the
-- idelic norm scales the Euclidean sup norm by t. Even at a single complex
-- place a positive-real section scales it by √t.

/-- Paper: Proposition 2.3.1.2(2), p. 100. As the S-idelic norm tends
to infinity, S-local theta decays at every positive inverse power. -/
theorem sLocalAdelicTheta_decay_large (f : ℬₛ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : Iₛ, T < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.2(3), p. 100. The large-norm decay constant
and threshold can be chosen uniformly for a bounded set of test functions. -/
theorem sLocalAdelicTheta_decay_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, T < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.2(4), p. 100. The bounded-set decay estimate
holds above S-idelic norm one with a uniform constant. -/
theorem sLocalAdelicTheta_decay_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

local instance normOneSIdeleQuotientMeasurableSpace (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

section HomogeneousTheta

-- TODO(paper-gap): Definition A.3.4.1(3)(3) names C_{F,S}^1 as the quotient
-- of the norm-one local S-ideles. The integral in (2.3.1.13) is over J_{F,S}^1.
-- The Haar measure on the latter is an explicit parameter pending its normalization.

variable (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm F S)))

local notation "classIntegrand" => fun (ω : PontryaginDual J₁) (f : ℬₛ) (g : Jₛ) (h : J₁) ↦
  sLocalAdelicThetaOnClasses F S f (g * Subtype.val h) * (ω h : ℂ)

/-- Paper: Proposition 2.3.1.4(1), p. 105. The character-weighted integral
is absolutely convergent at each S-idele class. -/
theorem sLocalHomogeneousAdelicTheta_integrable [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (g : Jₛ) :
    Integrable (classIntegrand ω f g) μ := by sorry

/-- Paper: Proposition 2.3.1.4(1), p. 105. On a compact set of S-ideles
the integrands have a common constant majorant on the compact norm-one classes.
Deviation: Uniform absolute convergence is expressed by this integrable majorant. -/
theorem sLocalHomogeneousAdelicTheta_integrand_bounded [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun _ : J₁ ↦ C) μ ∧
      ∀ g ∈ K, ∀ h : J₁, ‖classIntegrand ω f (classOf g) h‖ ≤ C := by sorry

/-- Paper: Proposition 2.3.1.4(1), p. 105. Integrating the character-weighted
theta function gives a continuous function on the S-idele classes. -/
theorem sLocalHomogeneousAdelicTheta_continuous [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) :
    Continuous (fun g : Jₛ ↦ ∫ h, classIntegrand ω f g h ∂μ) := by sorry

variable [Measure.IsHaarMeasure μ]

/-- Paper: Definition 2.3.1.3, p. 104. The character-weighted integral
defines a complex-linear map in the test function. -/
theorem sLocalHomogeneousAdelicTheta_isLinear (ω : PontryaginDual J₁) :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨fun g ↦ ∫ h, classIntegrand ω f g h ∂μ,
      sLocalHomogeneousAdelicTheta_continuous F S μ ω f⟩ : C(Jₛ, ℂ))) := by sorry

/-- Paper: Definition 2.3.1.3, p. 104. Homogeneous S-local theta integrates
theta at the class product `g * h` against the character on norm-one classes.
Deviation: The norm-one class Haar measure is an explicit parameter. In (2.3.1.13)
an idele argument is read through its class, as required by (2.3.1.12). -/
def sLocalHomogeneousAdelicTheta (ω : PontryaginDual J₁) : ℬₛ →ₗ[ℂ] C(Jₛ, ℂ) :=
  IsLinearMap.mk' _ (sLocalHomogeneousAdelicTheta_isLinear F S μ ω)

/-- Paper: Equation (2.3.1.13), p. 105. At the identity and for the trivial
character, homogeneous theta integrates unweighted theta on the norm-one classes. -/
theorem sLocalHomogeneousAdelicTheta_trivial_at_one (f : ℬₛ) :
    sLocalHomogeneousAdelicTheta F S μ (1 : PontryaginDual J₁) f 1 =
      ∫ h : J₁, sLocalAdelicThetaOnClasses F S f h.val ∂μ := by sorry

/-- Paper: Proposition 2.3.1.4(1), p. 105. Inverse left translation by a
norm-one class multiplies homogeneous theta by the character at that class.
Its pullback to the S-ideles has the corresponding pulled-back character. -/
theorem sLocalHomogeneousAdelicTheta_homogeneous (ω : PontryaginDual J₁)
    (f : ℬₛ) (h : J₁) (g : Jₛ) :
    sLocalHomogeneousAdelicTheta F S μ ω f (h.val⁻¹ * g) =
      (ω h : ℂ) * sLocalHomogeneousAdelicTheta F S μ ω f g := by sorry

/-- Paper: Proposition 2.3.1.4(2), p. 105. Homogeneous S-local theta decays
at every positive inverse power as the S-idelic norm tends to infinity. -/
theorem sLocalHomogeneousAdelicTheta_decay_large (ω : PontryaginDual J₁)
    (f : ℬₛ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : Iₛ, T < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.4(3), p. 105. The large-norm decay constants
for homogeneous S-local theta are uniform on a bounded set of test functions.
Deviation: Part (3) leaves the range of the exponent implicit. The nonnegative
range is supplied by part (4) and Proposition 2.3.1.2(3). -/
theorem sLocalHomogeneousAdelicTheta_decay_bounded (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, T < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.4(4), p. 105. The uniform decay estimate
for homogeneous theta holds above S-idelic norm one. -/
theorem sLocalHomogeneousAdelicTheta_decay_bounded_threshold_one (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

end HomogeneousTheta

/-! ## Directional derivatives -/

section DirectionalDerivatives

variable (γ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ)

local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)
local notation "orbitDeriv" => fun (f : ℬₛ) (x : Multiplicative Aₛ) ↦
  deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd (Units.val (γ (expUnit s)) * Multiplicative.toAdd x))) 0

/-- Paper: Lemma 2.3.2.1, p. 105. Pointwise differentiation along the
one-parameter subgroup gives a Schwartz–Bruhat function. -/
theorem sAdeleDirectionalDeriv_mem (f : ℬₛ) :
    orbitDeriv f ∈ schwartzBruhatSubmodule (Multiplicative Aₛ) := by sorry

/-- Paper: Lemma 2.3.2.1, p. 106. Taking the directional derivative
is complex linear on the S-local test space. -/
theorem sAdeleDirectionalDeriv_isLinear :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨orbitDeriv f, sAdeleDirectionalDeriv_mem F S γ f⟩ : ℬₛ)) :=
  by sorry

/-- Paper: Equation (2.3.2.1), p. 105. The directional derivative differentiates
the test function along the given one-parameter subgroup at the identity.
Deviation: As in the global definition, the derivative uses `t = exp s` at `s = 0`. -/
def sAdeleDirectionalDeriv : ℬₛ →ₗ[ℂ] ℬₛ :=
  IsLinearMap.mk' (fun f ↦ ⟨orbitDeriv f, sAdeleDirectionalDeriv_mem F S γ f⟩)
    (sAdeleDirectionalDeriv_isLinear F S γ)

/-- Paper: Lemma 2.3.2.1, p. 105. The difference quotient in the positive
real parameter converges to the S-adelic directional derivative. -/
theorem sAdeleDirectionalDeriv_tendsto (f : ℬₛ) (x : Aₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sAdeleDirectionalDeriv F S γ f (Multiplicative.ofAdd x))) := by sorry

/-- Paper: Lemma 2.3.2.1, p. 105. The directional derivative of a fixed
test function is continuous in the S-adele argument. -/
theorem sAdeleDirectionalDeriv_continuous_apply (f : ℬₛ) :
    Continuous (fun x : Aₛ ↦ sAdeleDirectionalDeriv F S γ f (Multiplicative.ofAdd x)) := by sorry

/-- Paper: Lemma 2.3.2.1, p. 106. The directional derivative is continuous
as an endomorphism of the S-local Schwartz–Bruhat space. -/
theorem sAdeleDirectionalDeriv_continuous :
    Continuous (sAdeleDirectionalDeriv F S γ) := by sorry

-- TODO(paper-gap): Equations (2.3.2.2)–(2.3.2.3) print τ(t) in both quotients.
-- For ℚ, S = {∞}, f(x) = exp(-x²), g = 1, and trivial γ, the τ derivative
-- of ordinary theta is -4/e, whereas the right side of (2.3.2.4) is zero.

/-- Paper: Proposition 2.3.2.2, p. 106. The directional difference quotient
of S-local theta converges to theta of the differentiated test function.
The limit is a continuous S-unit invariant function of the idele.
Deviation: Uses γ in (2.3.2.2), as specified by (2.3.2.4) and Lemma 2.3.2.1. -/
theorem sLocalAdelicTheta_directionalDeriv (f : ℬₛ) (g : Iₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (sLocalAdelicTheta F S f (γ t * g) - sLocalAdelicTheta F S f g) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sLocalAdelicTheta F S (sAdeleDirectionalDeriv F S γ f) g)) := by sorry

/-- Paper: Proposition 2.3.2.2, p. 106. The directional difference quotient
of homogeneous theta converges to homogeneous theta of the differentiated test
function. The limit is continuous on the S-idele classes.
Deviation: Uses γ in (2.3.2.3), as specified by (2.3.2.4) and Lemma 2.3.2.1. -/
theorem sLocalHomogeneousAdelicTheta_directionalDeriv
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm F S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (g : Iₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (sLocalHomogeneousAdelicTheta F S μ ω f (classOf (γ t * g)) -
        sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sLocalHomogeneousAdelicTheta F S μ ω (sAdeleDirectionalDeriv F S γ f) (classOf g))) :=
  by sorry

-- Remark 2.3.2.3, p. 106, defers the comparison with global theta to the
-- Mellin-transform constructions in Chapters 3–6.

end DirectionalDerivatives

end RiemannMasullo
