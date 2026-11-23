module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import Mathlib.Algebra.Field.ULift

import Mathlib.Algebra.Field.ULift
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz

import Mathlib.Algebra.Field.ULift
import all RiemannMasullo.AppB_AnalyticNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b

/-! # §7.1.1–7.1.2 Statements that are false as printed -/

@[expose] public noncomputable section

open Asymptotics Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators NNReal

namespace RiemannMasullo

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "Tests(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "normₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) normₛ(F, S) (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "period(" v ")" => (2 * Real.pi / Real.log (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ))

/-- Paper: Before Lemma 7.1.1.1, p. 313.
As printed: Each point of every unshifted lattice is a zero of the product
(7.1.1.1) with real phases tᵥ. The shift in the repaired finite-place pole list is in
`finiteHeckeEulerFactor_poles_iff`. See ERRATA F85. -/
def Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (t : S → ℝ)
    (v : S) (m : ℤ),
    let s : ℂ := ((m : ℝ) * period(v.val) : ℝ) * Complex.I
    ∏ w : S, (1 - (w.val.asIdeal.absNorm : ℂ) ^ (-s - (t w : ℂ) * Complex.I)) = 0

private theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_factor (q : ℕ)
    (hq : 1 < q) :
    1 - (q : ℂ) ^ (-(0 : ℂ) - ((Real.pi / Real.log q : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have hlog : Real.log q ≠ 0 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq
    exact (Real.log_pos this).ne'
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg q)]
  have : ((Real.log q : ℝ) : ℂ) * (-(0 : ℂ) - ((Real.pi / Real.log q : ℝ) : ℂ) * Complex.I) =
      -(Real.pi * Complex.I) := by
    have hlogc : ((Real.log q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    rw [Complex.ofReal_div]
    field_simp
    ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_ulift
    (h : Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros.{u}) : False := by
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) := ⟨⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 (ULift.{u} ℚ))
  let v : HeightOneSpectrum (𝓞 (ULift.{u} ℚ)) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    omega
  have key := h (ULift.{u} ℚ) {v} (fun _ ↦ Real.pi / Real.log (Ideal.absNorm v.asIdeal))
    ⟨v, Finset.mem_singleton_self v⟩ 0
  simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero] at key
  rw [Finset.prod_coe_sort ({v} : Finset _)
    (fun w ↦ 1 - (w.asIdeal.absNorm : ℂ) ^ (-(0 : ℂ) - ((Real.pi / Real.log
      (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) * Complex.I)), Finset.prod_singleton] at key
  exact Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_factor _ hq key

/-- Paper: Before Lemma 7.1.1.1, p. 313.
Take the rational field, the singleton place above 2, and tᵥ = π/(2 log 2).
At m = 0 the factor is 1 − exp(−iπ/2) = 1 + i. -/
theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false :
    ¬ Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros :=
  fun h ↦ Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_ulift h

/-- Paper: Lemma 7.1.2.2(1), p. 317.
As printed: At every complex place of angular weight k, a nonpositive integer in
`|k|/2 - ℕ` gives a pole of the correcting factor after the local imaginary shift.
This is the inclusion from the complex-place part of the pole list. The repaired list is
`sLocalRhoFactor_poles_iff`. See ERRATA F86. -/
def Printed.sLocalRhoFactor_complex_positive_shift : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (w : InfinitePlace F) (hw : w.IsComplex) (m : ℤ),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w (chart 0))).exists.choose
    m ≤ 0 → (∃ n : ℕ, (m : ℝ) = (p.2.natAbs : ℝ) / 2 - n) →
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart z)) ((m : ℂ) - p.1) < 0

/-- Paper: Lemma 7.1.2.2(1), p. 317.
Take ℚ(i) with only its complex place and the character `(z/|z|)^4`, which descends
through the four units. The printed list includes zero, but the numerator Γℂ(s + 2)
and the denominator Γℂ(3 − s) are regular and nonzero there. -/
theorem Printed.sLocalRhoFactor_complex_positive_shift_false :
    ¬ Printed.sLocalRhoFactor_complex_positive_shift := by sorry

section Theta

variable {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}

local instance printedCh07Sec1aNormOneMeasurableSpace :
    MeasurableSpace (normₛ(F, S)).ker := borel _

local instance printedCh07Sec1aNormOneHaar :
    (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

open Classical in
/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
As printed: This is the scalar expansion for every A > 0. The first sum uses
0 < m < A. Its coefficient is evaluated at the printed expression for cᵥ,ₘ,χ,
with exponent m − itᵥ from p. 317, while its norm weight has exponent m + itᵥ.
The pole list on p. 316 only admits m ≤ 0. For positive m the displayed
expression is in the holomorphic half-plane and the inner sum is empty.
At A = 1/2 even the outer integer range is empty, independently of this
index conflict. Each unramified finite place contributes its own copy of
the full Laurent coefficients.
The series converges uniformly on compact sets along horizontal contour cutoffs
(p. 322), and the scalar remainder is of order `O(|g|^A)`.
See `sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt` and ERRATA F87–F89. -/
def Printed.sLocalHomogeneousAdelicTheta_asymptotic : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (A : ℝ), 0 < A →
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    let normℝ (g : Jₛ(F, S)) := ((normₛ(F, S) g : ℝ≥0) : ℝ)
    let ω := χ.comp (⟨(normₛ(F, S)).ker.subtype, continuous_subtype_val⟩ :
      (normₛ(F, S)).ker →ₜ* Jₛ(F, S))
    let term (a weight : ℂ) (g : Jₛ(F, S)) :=
      ∑ j ∈ Finset.range (sLocalPolarMultiplicity f (chart a)),
        (-1 : ℂ) ^ j * sLocalZLaurentCoeff f (chart a) (j : ℤ) / (j.factorial : ℂ) *
          star (χ g : ℂ) * (normℝ g : ℂ) ^ weight * (Real.log (normℝ g) : ℂ) ^ j
    let archPhase (w : InfinitePlace F) :=
      let c := sLocalInfiniteRestriction w (chart 0)
      if hw : w.IsReal then (realLocalEulerParameters w hw c).exists.choose.1
      else
        (complexLocalEulerParameters w (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose.1
    let archSum (g : Jₛ(F, S)) :=
      ∑ w : InfinitePlace F, ∑ m ∈ Finset.Ioo 0 (Nat.ceil A),
        term ((m : ℂ) - archPhase w) ((m : ℂ) + archPhase w) g
    let phase (v : S) (t : ℝ) :=
      t ∈ Ico 0 (period(v.val)) ∧ ∀ x : (v.val.adicCompletion F)ˣ,
        sLocalFiniteRestriction v (chart 0) x =
          (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)
    let finitePlaces := Finset.univ.filter (fun v : S ↦ ∃ t, phase v t)
    let partialSum (height : ℝ) (g : Jₛ(F, S)) :=
      ∑ v : ↥finitePlaces,
        let t := (Finset.mem_filter.mp v.property).2.choose
        let d := period(v.val.val)
        ∑ m ∈ Finset.Ioo ⌊(t - height) / d⌋ ⌈(t + height) / d⌉,
          let a : ℂ := ((m : ℝ) * d - t : ℝ) * Complex.I
          term a (-a) g
    ∃ (T : ℕ → ℝ) (finiteSum : Jₛ(F, S) → ℂ), Tendsto T atTop atTop ∧
      (∀ K : Set Jₛ(F, S), IsCompact K →
        TendstoUniformlyOn (fun n ↦ partialSum (T n)) finiteSum atTop K) ∧
      IsBigO (comap normℝ (𝓝[>] 0))
        (fun g ↦ sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω f g -
          (archSum g + finiteSum g))
        (fun g ↦ Real.rpow (normℝ g) A)

/-- With no finite places and cutoff one half, the printed expansion has only its remainder. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_empty
    (h : Printed.sLocalHomogeneousAdelicTheta_asymptotic.{u})
    (F : Type u) [Field F] [NumberField F] (f : Tests(F, ∅)) :
    let r (g : Jₛ(F, ∅)) : ℝ := (normₛ(F, ∅) g).val
    IsBigO (comap r (𝓝[>] 0))
      (sLocalHomogeneousAdelicTheta F ∅ (sLocalNormOneQuotientMeasure F ∅) 1 f : Jₛ(F, ∅) → ℂ)
      (fun g ↦ r g ^ (1 / 2 : ℝ)) := by
  classical
  have H := h F ∅ 1 f (1 / 2) one_half_pos
  extract_lets chart r ω term archPhase archSum phase places partialSum at H
  obtain ⟨T, L, _, hlim, hO⟩ := H
  have hL (g : Jₛ(F, ∅)) : L g = 0 := by
    refine tendsto_nhds_unique ((hlim {g} isCompact_singleton).tendsto_at (mem_singleton g)) ?_
    refine tendsto_const_nhds.congr fun n ↦ ?_
    dsimp only [partialSum]
    exact (Finset.sum_eq_zero fun v _ ↦ (Finset.notMem_empty _ v.val.property).elim).symm
  have hm : Finset.Ioo 0 ⌈(1 / 2 : ℝ)⌉₊ = ∅ := by
    have hceil : ⌈(1 / 2 : ℝ)⌉₊ ≤ 1 := Nat.ceil_le.mpr (by norm_num)
    ext m
    simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
    omega
  refine hO.congr_left fun g ↦ sub_eq_self.2 ?_
  have ha : archSum g = 0 := by simp only [archSum, hm, Finset.sum_empty, Finset.sum_const_zero]
  rw [ha, hL, add_zero]

/-- At a single real place the pullback of the real Gaussian depends only on the idelic norm. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_gaussian
    (F : Type u) [Field F] [NumberField F] [Unique (InfinitePlace F)]
    (hw : (default : InfinitePlace F).IsReal) :
    ∃ f : Tests(F, ∅), ∀ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      (Real.exp (-(((sIdeleNorm F ∅ g).val : ℝ) ^ 2)) : ℂ) := by
  let w : InfinitePlace F := default
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let e : SAdeleRing F ∅ ≃ₜ ℝ := ((Homeomorph.prodUnique _ _).trans
    (Homeomorph.piUnique fun v : InfinitePlace F ↦ v.Completion)).trans j.toHomeomorph
  let a : SAdeleRing F ∅ ≃+ ℝ :=
    { e.toEquiv with
      map_add' := fun x y ↦ map_add (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (x.1 w) (y.1 w) }
  let E : Multiplicative (SAdeleRing F ∅) ≃ₜ* Multiplicative ℝ :=
    { a.toMultiplicative with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have : T2Space (Multiplicative (SAdeleRing F ∅)) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (SAdeleRing F ∅)) :=
    e.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  obtain ⟨b, hb⟩ := exists_gaussian_schwartz (E := ℝ) 1 zero_lt_one
  obtain ⟨T, hT⟩ := realSchwartzBruhat_equiv
  refine ⟨⟨(T b).val ∘ E, schwartzBruhat_mem_comp_equiv E (T b).property⟩, fun g ↦ ?_⟩
  change T b (Multiplicative.ofAdd (j (g.val.1 w))) = _
  rw [hT, hb, neg_one_mul, j.isometry.norm_map_of_map_zero (map_zero
    (InfinitePlace.Completion.ringEquivRealOfIsReal hw))]
  rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset Places(F))), Finset.prod_empty,
    mul_one, Fintype.prod_subsingleton _ w, hw.mult_eq_one, pow_one]
  rfl

/-- For a copy of ℚ the two unit translates of a radial Gaussian agree, and averaging
over norm-one classes contributes the total Haar mass. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_average
    (F : Type u) [Field F] [NumberField F] (e : F ≃+* ℚ) (f : Tests(F, ∅))
    (hf : ∀ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      (Real.exp (-(((sIdeleNorm F ∅ g).val : ℝ) ^ 2)) : ℂ)) (g : Jₛ(F, ∅)) :
    sLocalHomogeneousAdelicTheta F ∅ (sLocalNormOneQuotientMeasure F ∅) 1 f g =
      ((sLocalNormOneQuotientMeasure F ∅).real univ : ℂ) *
        (2 * (Real.exp (-(((normₛ(F, ∅) g).val : ℝ) ^ 2)) : ℂ)) := by
  let φ (t : ℝ≥0ˣ) : ℂ := Real.exp (-((t.val : ℝ) ^ 2))
  let U := (((∅ : Finset Places(F)) : Set Places(F)).integer F)ˣ
  have hcard : Nat.card U = 2 := by
    dsimp only [U]
    rw [Finset.coe_empty, integer_empty]
    let a := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 F) F)
    let b := (RingOfIntegers.mapRingEquiv e).trans Rat.ringOfIntegersEquiv
    rw [Nat.card_congr (Units.mapEquiv (a.toRingEquiv.trans b).toMulEquiv).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hclass (x : Jₛ(F, ∅)) : sLocalAdelicThetaOnClasses F ∅ f x = 2 * φ (normₛ(F, ∅) x) := by
    refine Quotient.inductionOn x fun y ↦ ?_
    refine (sLocalAdelicThetaOnClasses_mk F ∅ f y).trans ((sLocalAdelicTheta_apply F ∅ f y).trans ?_)
    calc
      _ = ∑' _ : U, φ (sIdeleNorm F ∅ y) := by
        apply tsum_congr
        intro u
        refine (hf (_ * y)).trans (congrArg φ ?_)
        rw [map_mul, MonoidHom.comp_apply,
          show sIdeleNorm F ∅ _ = 1 from (sIdeleNorm_spec F ∅).2 ⟨u, rfl⟩, one_mul]
      _ = _ := by
        rw [tsum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat, sIdeleQuotientNorm_mk]
  change (∫ h : (normₛ(F, ∅)).ker, sLocalAdelicThetaOnClasses F ∅ f (g * h.val) *
    ((1 : PontryaginDual (normₛ(F, ∅)).ker) h : ℂ) ∂_) = _
  have hker (h : (normₛ(F, ∅)).ker) : normₛ(F, ∅) h.val = 1 := h.property
  simp only [hclass, map_mul, hker, mul_one, PontryaginDual.one_apply, Circle.coe_one,
    integral_const, Complex.real_smul, φ]

/-- Every type universe contains a number field isomorphic to ℚ. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_ratCopy :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F), Nonempty (F ≃+* ℚ) := by
  let e : ULift.{u} ℚ ≃+* ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} ℚ) := RingHom.charZero e.toRingHom
  have : FiniteDimensional ℚ (ULift.{u} ℚ) :=
    Module.Finite.equiv e.toRatAlgEquiv.toLinearEquiv.symm
  exact ⟨ULift.{u} ℚ, inferInstance, {}, ⟨e⟩⟩

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
Over ℚ with only the real place, take the trivial character, `A = 1/2`, and a real
Gaussian. Both sums are empty and theta has a positive limit at norm zero.
For the finite-place overlap take ℚ with finite places 2 and 3, the trivial character,
and `A = 1/2`. At the finite places use the integer-ring indicators. At the real place
take a positive log-profile obtained by convolving a nonzero nonnegative smooth bump in
(0,1) with the indicators of [0, log 2] and [0, log 3]. The zeta function is a positive
constant times `6^s H(s)/s^2`, where H is the Mellin transform of the original bump
in the log coordinate. The origin is its only pole. Each finite-place series contributes
the printed logarithmic coefficient `-a₁`, whereas the inverse Mellin transform has
coefficient `-a₋₂`. The ratio 2a₁/a₋₂ is the bump-weighted mean of
(u + log 6)³/3, which exceeds one on (0,1). -/
theorem Printed.sLocalHomogeneousAdelicTheta_asymptotic_false :
    ¬ Printed.sLocalHomogeneousAdelicTheta_asymptotic := by
  classical
  intro h
  obtain ⟨F, _, _, ⟨e⟩⟩ := sLocalHomogeneousAdelicTheta_asymptotic_false_ratCopy
  have hd : Module.finrank ℚ F = 1 :=
    e.toRatAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℚ)
  have hR := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd
  have hC := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  have : Subsingleton (InfinitePlace F) := Fintype.card_le_one_iff_subsingleton.mp
    (by rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC])
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp (show 0 < InfinitePlace.nrRealPlaces F by omega)
  let : Unique (InfinitePlace F) := uniqueOfSubsingleton w
  obtain ⟨f, hf⟩ := sLocalHomogeneousAdelicTheta_asymptotic_false_gaussian F hw
  let r (g : Jₛ(F, ∅)) : ℝ := (normₛ(F, ∅) g).val
  have hr : Ioi 0 ⊆ range r := by
    intro t ht
    obtain ⟨s, hs⟩ := sIdeleQuotientNorm_exists_section F ∅
    let v : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (ne_of_gt (show (0 : ℝ≥0) < ⟨t, ht.le⟩ from ht))
    exact ⟨s v, congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) (hs v)⟩
  have : CompactSpace (normₛ(F, ∅)).ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F ∅).isCompact_preimage (isCompact_singleton (x := 1)))
  have : IsFiniteMeasure (sLocalNormOneQuotientMeasure F ∅) := CompactSpace.isFiniteMeasure
  exact sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_limit r hr _
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := sLocalNormOneQuotientMeasure F ∅)).ne') _
    (sLocalHomogeneousAdelicTheta_asymptotic_false_average F e f hf)
    (sLocalHomogeneousAdelicTheta_asymptotic_false_empty h F f)

end Theta

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
As printed: In the finite-place contribution of a pole to Mellin inversion, the coefficient of
`(-log t)^(k-1)/(k-1)!` is the Laurent coefficient of index k − 1. This states the
residue formula in the centered coordinate, with the common weight at the center removed.
The signed indices are those of `sLocalZLaurentCoeff`. See ERRATA F89. -/
def Printed.sLocalZLaurentCoeff_mellinResidue : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (v : S) (tᵥ : ℝ) (m : ℤ) (f : Tests(F, S)),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    tᵥ ∈ Ico 0 (period(v.val)) →
    (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart 0) x =
      (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((tᵥ : ℂ) * Complex.I)) →
    let c := chart (((m : ℝ) * period(v.val) - tᵥ : ℝ) * Complex.I)
    ∀ t : ℝ, 0 < t →
      complexResidue (fun z ↦ (t : ℂ) ^ (-z) * sLocalIdelicZFunction f (twistₛ(F, S) c z)) 0 =
        ∑ j ∈ Finset.range (sLocalPolarMultiplicity f c),
          sLocalZLaurentCoeff f c (j : ℤ) * (-(Real.log t : ℂ)) ^ j / (j.factorial : ℂ)

/-- Cauchy's differentiation formula, in the normalization used for the Laurent coefficients. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_residue_sq
    {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) :
    complexResidue (fun z ↦ A z / z ^ 2) 0 = deriv A 0 := by
  obtain ⟨R, hR, ha⟩ := hA.exists_ball_analyticOnNhd
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hd := (ha.mono (Metric.closedBall_subset_ball hr.2)).differentiableOn
  have hc := hd.deriv_eq_smul_circleIntegral hr.1
  simpa only [sub_zero, smul_eq_mul, one_div, ← div_eq_inv_mul, mul_div_cancel_left₀ _
    (show 2 * (Real.pi : ℂ) * Complex.I ≠ 0 by simp [Real.pi_ne_zero])] using
      (congrArg (· / (2 * (Real.pi : ℂ) * Complex.I)) hc).symm

/-- At the trivial center and `t = 1`, the printed identity forces the numerator of every
simple pole to agree with its derivative. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_numerator
    {F : Type u} [Field F] [NumberField F]
    {S : Finset Places(F)} (v : S) (h : Printed.sLocalZLaurentCoeff_mellinResidue.{u})
    (f : Tests(F, S)) (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hne : A 0 ≠ 0)
    (he : (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) 1 z)) =ᶠ[𝓝[≠] 0]
      (fun z ↦ A z / z)) : A 0 = deriv A 0 := by
  let chart := twistₛ(F, S) ((circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)))
  have base : (circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)) = 1 := by ext; rfl
  have h0 : chart 0 = 1 := by
    ext x
    change ((1 : Circle) : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hm : MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) 1 z)) 0 := by
    rw [← base]
    exact ((sLocalIdelicZFunction_meromorphic f 1) (mem_univ _)).meromorphicAt
  have hord := (meromorphicOrderAt_eq_int_iff (n := -1) hm).mpr ⟨A, hA, hne, by
    filter_upwards [he] with z hz
    simpa only [sub_zero, zpow_neg_one, smul_eq_mul, ← div_eq_inv_mul] using hz⟩
  have hmult : sLocalPolarMultiplicity f 1 = 1 := by simp [sLocalPolarMultiplicity, hord]
  have hv : 0 < period(v.val) := div_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
  have hres := h F S 1 v 0 0 f ⟨le_rfl, hv⟩ (by
    intro x
    change sLocalFiniteRestriction v (chart 0) x = _
    rw [h0]; simp; rfl) 1 zero_lt_one
  let ξ := chart ((((0 : ℤ) : ℝ) * period(v.val) - 0 : ℝ) * Complex.I)
  have hξ : ξ = 1 := by simpa [ξ] using h0
  change complexResidue (fun z ↦ ((1 : ℝ) : ℂ) ^ (-z) *
      sLocalIdelicZFunction f (twistₛ(F, S) ξ z)) 0 =
    ∑ j ∈ Finset.range (sLocalPolarMultiplicity f ξ),
      sLocalZLaurentCoeff f ξ (j : ℤ) * (-(Real.log 1 : ℂ)) ^ j / (j.factorial : ℂ) at hres
  rw [hξ, hmult] at hres
  simp [sLocalZLaurentCoeff] at hres
  have hl : complexResidue _ 0 = A 0 := (complexResidue_congr he).trans
    (by simpa only [sub_zero] using complexResidue_div_sub hA)
  refine hl.symm.trans (hres.trans ((complexResidue_congr ?_).trans
    (sLocalZLaurentCoeff_mellinResidue_false_residue_sq hA)))
  filter_upwards [he] with z hz
  simp only [hz, div_div, pow_two]

/-- With one infinite place the archimedean test is pulled back by coordinate evaluation. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_tensor
    {F : Type u} [Field F] [NumberField F]
    [Unique (InfinitePlace F)] {S : Finset Places(F)}
    (a : (w : InfinitePlace F) → SchwartzBruhat (Multiplicative w.Completion))
    (b : (v : S) → SchwartzBruhat (Multiplicative (v.val.adicCompletion F))) :
    ∃ f : Tests(F, S), ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
      (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v, b v (Multiplicative.ofAdd (x.2 v)) := by
  let w : InfinitePlace F := default
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* Multiplicative w.Completion :=
    { Homeomorph.piUnique (fun i : InfinitePlace F ↦ i.Completion) with map_mul' := fun _ _ ↦ rfl }
  let : T2Space (Multiplicative w.Completion) := inferInstanceAs (T2Space w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) :=
    inferInstanceAs (LocallyCompactSpace w.Completion)
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let g : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨(a w).val ∘ e, schwartzBruhat_mem_comp_equiv e (a w).property⟩
  obtain ⟨T, hT⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  refine ⟨T (TensorProduct.tmul ℂ g (PiTensorProduct.tprod ℂ b)), fun x ↦ ?_⟩
  rw [hT, Fintype.prod_subsingleton _ w]
  rfl

/-- Pair a real test giving a simple pole with a finite test having nonzero constant transform.
Translating the latter multiplies the numerator by the complex power of the idelic norm. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_contradiction
    {F : Type u} [Field F] [NumberField F]
    [Unique (InfinitePlace F)] (hw : ∀ w : InfinitePlace F, w.IsReal)
    (S : Finset Places(F)) [Unique S] (h : Printed.sLocalZLaurentCoeff_mellinResidue.{u}) : False := by
  classical
  let w : InfinitePlace F := default
  let v : S := default
  let α (i : InfinitePlace F) := quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ i.mult) (continuous_infiniteLocalModule i)
    ((circleToComplex).comp (1 : PontryaginDual i.Completionˣ))
  let β (i : S) := quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom)
    (continuous_finiteLocalModule i.val)
    ((circleToComplex).comp (1 : PontryaginDual (i.val.adicCompletion F)ˣ))
  let chart := twistₛ(F, S) ((circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)))
  have harch (i : InfinitePlace F) (s : ℂ) : sLocalInfiniteRestriction i (chart s) = α i s := by
    ext1 x
    rw [sLocalInfiniteRestriction_normTwist]
    change _ = ((1 : Circle) : ℂ) * _
    rw [Circle.coe_one, one_mul]; rfl
  have hfin (i : S) (s : ℂ) : sLocalFiniteRestriction i (chart s) = β i s := by
    ext1 x
    have hn := sLocalFiniteRestriction_norm i x
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (1 : ℂ) = _ at hn
    simp only [Circle.coe_one, one_mul, Complex.cpow_one] at hn
    change ((1 : Circle) : ℂ) * _ ^ s = ((1 : Circle) : ℂ) * _ ^ s
    rw [hn]
  -- Use the even, trivial-character pole at the real place.
  have hpole (i : InfinitePlace F) := (infiniteLocalIdelicZFunction_real_poles i (hw i) 1 0
    (fun _ ↦ by simp; rfl) 0).2.mpr ⟨0, by simp⟩
  choose a ha using hpole
  let Z (z : ℂ) := infiniteLocalIdelicZFunction w (a w) (α w z)
  have hm : Meromorphic Z := fun z ↦
    (((infiniteLocalIdelicZFunction_existsUnique w (a w)).exists.choose_spec 1).1
      (mem_univ z)).meromorphicAt
  obtain ⟨H, hH, hnH, hZ⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) (hm 0)).mp (ha w)
  choose b C hnC hb using fun i : S ↦ exists_finite_constant_zeta_test i.val 1
  let B (z : ℂ) := H z * C v
  have hB : AnalyticAt ℂ B 0 := hH.mul analyticAt_const
  have hnB : B 0 ≠ 0 := mul_ne_zero hnH (hnC v)
  have allD (p : (i : S) → (i.val.adicCompletion F)ˣ) :
      B 0 = deriv (fun z : ℂ ↦ B z * (‖(p v).val‖ : ℂ) ^ z) 0 := by
    let r : ℂ := ‖(p v).val‖
    have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (p v).ne_zero)
    have hrA := (differentiable_id.const_cpow (c := r) (Or.inl hr)).analyticAt
    let d := fun i ↦ schwartzBruhatUnitTranslate (p i) (b i)
    obtain ⟨f, hf⟩ := sLocalZLaurentCoeff_mellinResidue_false_tensor a d
    let G (z : ℂ) := sLocalIdelicZFunction f (chart z)
    have heq (z : ℂ) (hz : 0 < z.re) : G z = Z z * (r ^ z * C v) := by
      have eq := sLocalIdelicZetaIntegral_pureTensor (chart z) ⟨1, z, hz, rfl⟩ f a d hf
      rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ v, harch, hfin] at eq
      refine (sLocalIdelicZFunction_eq_integral f ⟨1, z, hz, rfl⟩).trans (eq.trans ?_)
      congr 1
      · exact (infiniteLocalIdelicZFunction_eq_integral w (a w) 1 hz).symm
      · exact (finiteZeta_dilate v.val _ (β v z) (p v)).trans
          (congrArg₂ (· * ·) (finite_norm_chart_apply v.val z (p v)) (hb v z))
    -- Continue the product identity from the right half-plane to the punctured germ.
    have hM : Meromorphic G := fun z ↦
      ((sLocalIdelicZFunction_meromorphic f 1) (mem_univ z)).meromorphicAt
    have he := meromorphic_eq_of_germ hM
      (fun z ↦ (hm z).mul (((hrA z).mul analyticAt_const).meromorphicAt))
      (z := 1) (by
        have hh : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) :=
          (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
        filter_upwards [nhdsWithin_le_nhds hh] with z hz using heq z hz)
    have base : (circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)) = 1 := by ext; rfl
    have hG : (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) 1 z)) =ᶠ[𝓝[≠] 0]
        fun z ↦ (B z * r ^ z) / z := by
      rw [← base]
      filter_upwards [he.filter_mono (nhdsNE_le_codiscrete 0), hZ] with z hz hzz
      change G z = _
      change G z = Z z * (r ^ z * C v) at hz
      rw [hz, hzz]
      simp only [B, sub_zero, zpow_neg_one, smul_eq_mul, div_eq_mul_inv]
      ring
    simpa only [Complex.cpow_zero, mul_one] using
      sLocalZLaurentCoeff_mellinResidue_false_numerator v h f
        (fun z ↦ B z * r ^ z) (hB.mul (hrA 0)) (by simpa using hnB) hG
  -- Compare the unit translate with the uniformizer translate.
  have hd : B 0 = deriv B 0 := by simpa using allD (fun _ ↦ 1)
  choose p hp using fun i : S ↦ exists_finite_norm_uniformizer i.val
  have hd' := allD p
  let r : ℂ := ‖(p v).val‖
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (p v).ne_zero)
  change B 0 = deriv (fun z ↦ B z * r ^ z) 0 at hd'
  have hdiff : DifferentiableAt ℂ (fun z : ℂ ↦ r ^ z) 0 :=
    (differentiable_id.const_cpow (c := r) (Or.inl hr)).differentiableAt
  rw [deriv_fun_mul hB.differentiableAt hdiff, Complex.deriv_const_cpow_id] at hd'
  simp only [Complex.cpow_zero, mul_one] at hd'
  have hdiff₀ : B 0 * Complex.log r = 0 := by linear_combination hd - hd'
  have hlog : Complex.log r = 0 := (mul_eq_zero.mp hdiff₀).resolve_left hnB
  have hone : r = 1 := by rw [← Complex.exp_log hr, hlog, Complex.exp_zero]
  have hlt : ‖(p v).val‖ < 1 := by
    rw [hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)
  exact hlt.ne (Complex.ofReal_injective (hone.trans Complex.ofReal_one.symm))

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
Over ℚ take the place above 2, χ = 1, tᵥ = m = 0 and t = 1. Use a smooth
nonzero nonnegative real bump supported in (exp 1, exp 2) times the indicator of ℤ₂.
Its transform is B(s)/(1 − 2⁻ˢ), where B′(0) > B(0) > 0 since log x > 1
on the bump. The residue is B(0)/log 2. The printed coefficient is
a₀ = B′(0)/log 2 + B(0)/2, strictly larger. -/
theorem Printed.sLocalZLaurentCoeff_mellinResidue_false :
    ¬ Printed.sLocalZLaurentCoeff_mellinResidue := by
  classical
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  let F := ULift ℚ
  have hd : Module.finrank ℚ F = 1 := by
    change Module.finrank ℚ (ULift ℚ) = 1
    rw [finrank_ulift, Module.finrank_self]
  have hreal := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd
  have hcomplex := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hcomplex, add_zero]
  let := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard).some
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : Places(F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  apply sLocalZLaurentCoeff_mellinResidue_false_contradiction (F := F) (S := {v}) _ h
  intro w
  have hr : Nonempty {i : InfinitePlace F // i.IsReal} :=
    Fintype.card_pos_iff.mp (by rw [← InfinitePlace.nrRealPlaces, hreal]; decide)
  obtain ⟨i, hi⟩ := hr
  simpa only [Subsingleton.elim i w] using hi

/-- Paper: Proof of Theorem 7.1.2.3, p. 322.
As printed: The continued S-local zeta transform has a finite L¹ norm on the vertical
line of real part −A for every positive A, as required for the stated remainder
bound. The obstruction is recorded in `Sec1a`. See ERRATA F90. -/
def Printed.sLocalIdelicZFunction_verticalIntegrable_neg : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (A : ℝ), 0 < A →
      Complex.VerticalIntegrable
        (fun s ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) s)) (-A)

/-- Paper: Proof of Theorem 7.1.2.3, p. 322.
Take ℚ(√2), only its two real places, the trivial character, and at each place
`x² exp(-πx²)`. The zeta transform is a nonzero constant times Γℝ(s + 2)².
At A = 2 its norm on the vertical line is of order `|Im s|⁻²` near −2. -/
theorem Printed.sLocalIdelicZFunction_verticalIntegrable_neg_false :
    ¬ Printed.sLocalIdelicZFunction_verticalIntegrable_neg := by sorry

/-- Paper: Discussion of Theorem 7.1.2.3, p. 320.
As printed: Each nonnegative Laurent coefficient at c is an S-local eigendistribution
of weight c. This states the eigencharacter law using the scalar coefficient
`sLocalZLaurentCoeff` and the translation action of §5.5. See ERRATA F91. -/
def Printed.sLocalZLaurentCoeff_eigendistribution : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (c : QuasiCharacter Jₛ(F, S)) (m : ℕ) (g : (SAdeleRing F S)ˣ) (f : Tests(F, S)),
    sLocalZLaurentCoeff (schwartzBruhatUnitTranslate g f) c (m : ℤ) =
      c (QuotientGroup.mk g) * sLocalZLaurentCoeff f c (m : ℤ)

/-- Paper: Discussion of Theorem 7.1.2.3, p. 320.
Over ℚ with only the real place and the trivial center, use m = 0 and the
Gaussian `exp(-πx²)`. Replacing it by `exp(-π(x/2)²)` multiplies its zeta
transform by `2^s`. The residue is 2, so the constant coefficient changes
by `2 log 2`, contrary to the trivial weight law. -/
theorem Printed.sLocalZLaurentCoeff_eigendistribution_false :
    ¬ Printed.sLocalZLaurentCoeff_eigendistribution := by sorry

/-- Paper: Discussion of Theorem 7.1.2.3, p. 321.
As printed: The coefficient whose Laurent index equals the finite-place lattice
index is supported on the corresponding periodic locus. In particular it vanishes on
tests whose support misses the inverse image of that locus, where the indicated
finite coordinate is zero. The scalar coefficient is `sLocalZLaurentCoeff`.
See ERRATA F92. -/
def Printed.sLocalZLaurentCoeff_finitePlace_support : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (v : S) (t : ℝ) (m : ℤ) (f : Tests(F, S)),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    t ∈ Ico 0 (period(v.val)) →
      (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart 0) x =
        (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)) →
      Disjoint (tsupport (fun x ↦ f x))
        {x : Multiplicative (SAdeleRing F S) | x.toAdd.2 v = 0} →
      sLocalZLaurentCoeff f (chart ((((m : ℝ) * period(v.val) - t : ℝ) : ℂ) * Complex.I)) m = 0

/-- Paper: Discussion of Theorem 7.1.2.3, p. 321.
Take ℚ with the real place and the place above 2, the trivial character and m = 0.
Use a nonzero nonnegative smooth bump supported in (1,2) times the indicator of
ℤ₂ˣ. The support avoids the zero at the finite coordinate, but the zeta integral
is holomorphic at zero and its constant term is strictly positive. -/
theorem Printed.sLocalZLaurentCoeff_finitePlace_support_false :
    ¬ Printed.sLocalZLaurentCoeff_finitePlace_support := by sorry

/-- Paper: Proof of Theorem 7.1.2.3, p. 321.
As printed: For every test the trivial-character zeta function has pole order equal
to the number of infinite places at the origin. The test-dependent order is
`sLocalPolarMultiplicity`. See ERRATA F93. -/
def Printed.sLocalPolarMultiplicity_trivial_origin : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (f : Tests(F, S)),
    sLocalPolarMultiplicity f 1 = Fintype.card (InfinitePlace F)

/-- Paper: Proof of Theorem 7.1.2.3, p. 321.
The zero test over ℚ with only the real place has no pole. Over ℚ with the real
place and the place above 2, the Gaussian times the indicator of ℤ₂ instead
has a double pole from Γℝ(s) and the Euler factor at 2. -/
theorem Printed.sLocalPolarMultiplicity_trivial_origin_false :
    ¬ Printed.sLocalPolarMultiplicity_trivial_origin := by
  intro h
  let F := ULift ℚ
  let : NumberField F := NumberField.of_ringEquiv ℚ F ULift.ringEquiv.symm
  let f : Tests(F, ∅) := ⟨0, (schwartzBruhatSubmodule _).zero_mem⟩
  have hZ : sLocalIdelicZFunction f = fun _ ↦ 0 := by
    have hcont := sLocalIdelicZetaIntegral_exists_continuation f
    exact hcont.unique hcont.exists.choose_spec
      ⟨fun _ _ _ ↦ analyticAt_const.meromorphicNFAt, fun c _ ↦ by
        simp [sLocalIdelicZetaIntegral, f]⟩
  have hmult : sLocalPolarMultiplicity f 1 = 0 := by
    simp [sLocalPolarMultiplicity, hZ, meromorphicOrderAt_const]
  exact Fintype.card_ne_zero ((h F ∅ f).symm.trans hmult)

/-- Paper: Coefficient formula after Theorem 7.1.2.3, p. 323.
As printed: The Laurent coefficient of index k − 1 is given by the contour integral
around any continuously differentiable simple contour enclosing the center.
The local coefficient is `sLocalZLaurentCoeff`. See ERRATA F94. -/
def Printed.sLocalZLaurentCoeff_any_contour : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (a : ℂ) (k : ℕ), 1 ≤ k →
    ∀ γ : ComplexContour, ContDiffOn ℝ 1 γ.toContinuousMap (Icc 0 1) →
      InjOn γ.toContinuousMap (Ico 0 1) → a ∉ γ.trace → γ.index a ≠ 0 →
        let chart := twistₛ(F, S) ((circleToComplex).comp χ)
        let integrand := fun s ↦ sLocalIdelicZFunction f (chart s) / (s - a) ^ k
        HasPettisIntegral (PettisMeasure.complex γ.measure) integrand
          (2 * (Real.pi : ℂ) * Complex.I * sLocalZLaurentCoeff f (chart a) ((k : ℤ) - 1))

/-- Paper: Coefficient formula after Theorem 7.1.2.3, p. 323.
For ℚ with only its real place take the Gaussian, the trivial character,
a = 0 and k = 1. The counterclockwise circle of radius 3 centered at zero also
encloses −2. The residue of Γℝ(s)/s at −2 adds π to the local coefficient. -/
theorem Printed.sLocalZLaurentCoeff_any_contour_false :
    ¬ Printed.sLocalZLaurentCoeff_any_contour := by sorry

end RiemannMasullo
