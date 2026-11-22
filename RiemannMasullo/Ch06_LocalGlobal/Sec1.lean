module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Pi

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Structure Theorem IV: local within global

Masullo, §6.1, pp. 287–295. The finite sets index finite places. The
archimedean places are included in every S-adelic ring.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped CompactlySupported MonoidAlgebra NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "L(" w ")" => (HeightOneSpectrum.adicCompletion (R := 𝓞 F) F w)
local notation "ℬᵥ(" w ")" => (SchwartzBruhat (Multiplicative (L(w))))
local notation "O(" w ")" => (HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F w)
local notation "U(" w ")" =>
  (Submonoid.units (Subsemiring.toSubmonoid (Subring.toSubsemiring (ValuationSubring.toSubring (O(w))))))

-- TODO(paper-gap): Proposition 6.1.1.1, (6.1.1.1)–(6.1.1.2), multiplies
-- inverses of test-space endomorphisms to obtain transitions between distinct
-- quotients. On the target coinvariants every basis lift acts as the identity,
-- so the differences have no inverse. Already over ℚ, with S = {∞} and
-- S' = {∞, p}, the proposed geometric series does not converge in the target
-- quotient on a nonzero transition class. The global series has the same defect.

section Ranges

private theorem mem_ker_adeleProjection_units_iff (T : Finset (HeightOneSpectrum (𝓞 F)))
    (g : IdeleGroup (𝓞 F) F) :
    g ∈ (Units.map (adeleProjection F T).toMonoidHom).ker ↔
      g.val.1 = 1 ∧ ∀ w : T, g.val.2 w.val = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp only [Units.coe_map, Units.val_one]
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w ↦ congrFun h2 w⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun w ↦ h2 w⟩

variable (F S) in
/-- Paper: (6.1.2.2), p. 288.
The complementary integral ideles are the ideles integral and invertible outside S
whose S-adelic projection is the identity.
Deviation: In (6.1.2.2) the ambient outside multiplicative factors form a restricted
product. The full product of integer units embeds in the ideles. -/
def outsideIntegralIdeleUnits : Subgroup (IdeleGroup (𝓞 F) F) :=
  (integralIdeleInsertion F S).range ⊓ (Units.map (adeleProjection F S).toMonoidHom).ker

/-- Paper: (6.1.2.2), p. 288.
An idele belongs to the complementary group exactly when its archimedean and S coordinates
are one and its other coordinates are local integer units. -/
theorem mem_outsideIntegralIdeleUnits_iff (g : IdeleGroup (𝓞 F) F) :
    g ∈ outsideIntegralIdeleUnits F S ↔
      g.val.1 = 1 ∧ (∀ w ∈ S, g.val.2 w = 1) ∧
        ∀ w ∉ S, g.val.2 w ∈ O(w) ∧ (g⁻¹).val.2 w ∈ O(w) := by
  unfold outsideIntegralIdeleUnits
  rw [Subgroup.mem_inf, mem_ker_adeleProjection_units_iff,
    show g ∈ (integralIdeleInsertion F S).range ↔ g ∈ Set.range (integralIdeleInsertion F S) from
      Iff.rfl,
    mem_range_integralIdeleInsertion]
  constructor
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, fun w hw ↦ h3 ⟨w, hw⟩, h2⟩
  · rintro ⟨h1, h3, h2⟩
    exact ⟨h2, h1, fun w ↦ h3 w.1 w.2⟩

variable (F S T) in
/-- Paper: (6.1.2.1), p. 288.
Projecting the complementary integral ideles to T inserts the integer units at T minus S.
Deviation: The insertion lands in the T-ideles, as required by Theorem 6.1.2.1(1). -/
def relativeIntegralIdeleUnits : Subgroup (SAdeleRing F T)ˣ :=
  (outsideIntegralIdeleUnits F S).map (Units.map (adeleProjection F T).toMonoidHom)

/-- Paper: (6.1.2.1), p. 288.
The relative group has identity coordinates on the archimedean factor and S, and
arbitrary integer-unit coordinates on T minus S. -/
theorem mem_relativeIntegralIdeleUnits_iff (g : (SAdeleRing F T)ˣ) :
    g ∈ relativeIntegralIdeleUnits F S T ↔
      g.val.1 = 1 ∧ (∀ w : T, w.val ∈ S → g.val.2 w = 1) ∧
        ∀ w : T, w.val ∉ S → g.val.2 w ∈ O(w.val) ∧ (g⁻¹).val.2 w ∈ O(w.val) := by
  classical
  unfold relativeIntegralIdeleUnits
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (mem_outsideIntegralIdeleUnits_iff h).1 hh
    refine ⟨h1, fun w hw ↦ h2 w.val hw, fun w hw ↦ h3 w.val hw⟩
  · rintro ⟨h1, h2, h3⟩
    let e (x : (w : T) → HeightOneSpectrum.adicCompletion F w.val) :
        RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) ↦ HeightOneSpectrum.adicCompletion F w)
          (fun w ↦ HeightOneSpectrum.adicCompletionIntegers F w) Filter.cofinite :=
      RestrictedProduct.mk
        (fun w : HeightOneSpectrum (𝓞 F) ↦ if hw : w ∈ T then x ⟨w, hw⟩ else 1)
        (by
          filter_upwards [T.eventually_cofinite_notMem] with w hw
          simp only [hw, dite_false]
          exact one_mem _)
    have he (x) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∈ T) : e x w = x ⟨w, hw⟩ := by
      exact dif_pos hw
    have he' (x) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) : e x w = 1 := by
      exact dif_neg hw
    have hmul : ∀ w : T, g.val.2 w * (g⁻¹).val.2 w = 1 := fun w ↦
      congrFun (congrArg Prod.snd g.val_inv) w
    have hmul' : ∀ w : T, (g⁻¹).val.2 w * g.val.2 w = 1 := fun w ↦
      congrFun (congrArg Prod.snd g.inv_val) w
    have hm1 : e g.val.2 * e (g⁻¹).val.2 = 1 := Subtype.ext (funext fun w ↦ by
      by_cases hw : w ∈ T
      · change e _ w * e _ w = 1
        rw [he _ _ hw, he _ _ hw]; exact hmul ⟨w, hw⟩
      · change e _ w * e _ w = 1
        rw [he' _ _ hw, he' _ _ hw]; exact mul_one _)
    have hm2 : e (g⁻¹).val.2 * e g.val.2 = 1 := Subtype.ext (funext fun w ↦ by
      by_cases hw : w ∈ T
      · change e _ w * e _ w = 1
        rw [he _ _ hw, he _ _ hw]; exact hmul' ⟨w, hw⟩
      · change e _ w * e _ w = 1
        rw [he' _ _ hw, he' _ _ hw]; exact mul_one _)
    let h : IdeleGroup (𝓞 F) F :=
      ⟨(1, e g.val.2), (1, e (g⁻¹).val.2), Prod.ext (mul_one 1) hm1, Prod.ext (mul_one 1) hm2⟩
    refine ⟨h, ?_, ?_⟩
    · rw [mem_outsideIntegralIdeleUnits_iff]
      refine ⟨rfl, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hT : w ∈ T
        · exact (he _ _ hT).trans (h2 ⟨w, hT⟩ hw)
        · exact he' _ _ hT
      · by_cases hT : w ∈ T
        · exact ⟨(he _ _ hT).symm ▸ (h3 ⟨w, hT⟩ hw).1, (he _ _ hT).symm ▸ (h3 ⟨w, hT⟩ hw).2⟩
        · exact ⟨(he' _ _ hT).symm ▸ one_mem _, (he' _ _ hT).symm ▸ one_mem _⟩
    · refine Units.ext (Prod.ext h1.symm (funext fun w ↦ ?_))
      exact he _ _ w.2

/-- Paper: (6.1.2.2), p. 288.
The group of integral idelic units outside S is compact in the global ideles. -/
theorem outsideIntegralIdeleUnits_isCompact :
    IsCompact (outsideIntegralIdeleUnits F S : Set (IdeleGroup (𝓞 F) F)) := by sorry

/-- Paper: (6.1.2.1), p. 288.
The group of integer units inserted at the additional finite places is compact in the T-ideles. -/
theorem relativeIntegralIdeleUnits_isCompact :
    IsCompact (relativeIntegralIdeleUnits F S T : Set (SAdeleRing F T)ˣ) := by sorry

-- TODO(paper-gap): The proof of Theorem 6.1.2.1 applies its invariant-space
-- tensor identification to the full test space and has mismatched indices
-- in (6.1.2.21). The argument on pp. 294–295 assumes convergent Cauchy nets
-- have bounded tails in the strict LF topology. Equation (5.1.1.3) defines the
-- two theta spaces as quotients by the theta kernels. Remark 5.2.3.4 concerns
-- the separate comparison with closures of principal translation differences.

/-- Paper: Theorem 6.1.2.1(1), p. 288.
When the S-integers have trivial Picard group, the range of the transition is the fixed
subspace for the relative integral units in the T-local theta quotient of (5.1.1.3). -/
theorem sLocalThetaTransition_range_eq_invariants (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    Set.range (sLocalThetaTransition (F := F) hST.le) =
      {x : Θₛ(T) | ∀ g : relativeIntegralIdeleUnits F S T,
        ρ (QuotientGroup.mk g.val) x = x} := by sorry

/-- Paper: Theorem 6.1.2.1(2), p. 288.
When the S-integers have trivial Picard group, the range of the global insertion is the fixed
subspace for the complementary integral units in the global theta quotient of (5.1.1.3). -/
theorem sLocalThetaToGlobal_range_eq_invariants
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    Set.range (sLocalThetaToGlobal F S) =
      {x : Θ𝔽 | ∀ g : outsideIntegralIdeleUnits F S, ρ (QuotientGroup.mk g.val) x = x} := by sorry

end Ranges

section UnitRepresentation

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "translate" => fun (g : Rˣ) ↦
  ((LinearMap.funLeft ℂ ℂ (fun x : Multiplicative R ↦
    Multiplicative.ofAdd ((g⁻¹ : Rˣ).val * x.toAdd))).comp
    (schwartzBruhatSubmodule (Multiplicative R)).subtype).codRestrict
      (schwartzBruhatSubmodule (Multiplicative R)) (schwartzBruhat_unitTranslate_mem g)

/-- Paper: Remark 6.1.2.3, p. 289.
The identity unit acts by the identity on the additive Schwartz–Bruhat space. -/
theorem schwartzBruhatUnitRepresentation_map_one :
    translate (1 : Rˣ) = (1 : Module.End ℂ ℬ(R)) := by sorry

/-- Paper: Remark 6.1.2.3, p. 289.
Pullback by the inverse of a product agrees with the composition of the two translations. -/
theorem schwartzBruhatUnitRepresentation_map_mul (g h : Rˣ) :
    translate (g * h) = (translate g : Module.End ℂ ℬ(R)) * translate h := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change f.val (Multiplicative.ofAdd (((g * h)⁻¹ : Rˣ).val * x.toAdd)) =
    f.val (Multiplicative.ofAdd ((h⁻¹ : Rˣ).val * ((g⁻¹ : Rˣ).val * x.toAdd)))
  rw [mul_inv_rev, Units.val_mul, mul_assoc]

/-- Paper: Remark 6.1.2.3, p. 289.
The inverse-multiplication pullback action on additive Schwartz–Bruhat functions,
bundled as a complex linear representation of the unit group. -/
def schwartzBruhatUnitRepresentation : Representation ℂ Rˣ ℬ(R) where
  toFun := translate
  map_one' := schwartzBruhatUnitRepresentation_map_one
  map_mul' := schwartzBruhatUnitRepresentation_map_mul

/-- Paper: Remark 6.1.2.3, p. 289.
The bundled representation acts by the existing left-translation operator. -/
theorem schwartzBruhatUnitRepresentation_apply (g : Rˣ) (f : ℬ(R)) :
    schwartzBruhatUnitRepresentation (R := R) g f = schwartzBruhatUnitTranslate g f := by sorry

end UnitRepresentation

local notation "ρ(" w ")" =>
  (schwartzBruhatUnitRepresentation (R := L(w))).comp
    (Subgroup.subtype (U(w)))

section Laurent

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_eval_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ℝ≥0∞).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ℝ≥0∞)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

private theorem unitInvariants_isClosed {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (H : Subgroup Rˣ) :
    IsClosed (SetLike.coe (Representation.invariants
      ((schwartzBruhatUnitRepresentation (R := R)).comp H.subtype)) : Set ℬ(R)) := by
  have : (SetLike.coe (Representation.invariants
      ((schwartzBruhatUnitRepresentation (R := R)).comp H.subtype)) : Set ℬ(R)) =
      ⋂ g : H, ⋂ x : R, {f | f (Multiplicative.ofAdd (((g⁻¹ : H) : Rˣ).val * x)) =
        f (Multiplicative.ofAdd x)} := by
    ext f
    simp only [SetLike.mem_coe, Representation.mem_invariants, Set.mem_iInter, Set.mem_setOf_eq]
    refine forall_congr' fun g ↦ ?_
    constructor
    · intro h x
      exact congrArg (fun φ : ℬ(R) ↦ φ.val (Multiplicative.ofAdd x)) h
    · intro h
      exact Subtype.ext (funext fun x ↦ h x.toAdd)
  rw [this]
  exact isClosed_iInter fun g ↦ isClosed_iInter fun x ↦
    isClosed_eq (schwartzBruhat_eval_continuous (Multiplicative.ofAdd _))
      (schwartzBruhat_eval_continuous (Multiplicative.ofAdd _))

open Classical in
/-- Paper: Lemma 6.1.2.2(1), p. 288.
The monomial of exponent n corresponds to the indicator of the integral ball
scaled by the n-th power of the uniformizer. -/
def finitePlaceBallIndicator (w : Places) (π : (L(w))ˣ) (n : ℤ)
    (x : L(w)) : ℂ :=
  (O(w) : Set L(w)).indicator (fun _ ↦ (1 : ℂ)) ((π ^ (-n)).val * x)

/-- Paper: Lemma 6.1.2.2(1), p. 288.
The translated ball contains the m-th uniformizer power exactly when m is at least its
defining exponent n. -/
theorem finitePlaceBallIndicator_at_power (w : Places) (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    (m n : ℤ) :
    finitePlaceBallIndicator w π n (π ^ m).val = (if n ≤ m then 1 else 0) := by
  have hv : Valued.v (π.val) = (WithZero.exp (-1 : ℤ)) := _hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (w.valuedAdicCompletion_surjective F)))
  have h1 : (π ^ (-n)).val * (π ^ m).val = ((π ^ (m - n)).val) := by
    rw [← Units.val_mul, ← zpow_add]; congr 2; ring
  have h2 : Valued.v ((π ^ (m - n)).val) = WithZero.exp (-(m - n)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, ← WithZero.exp_zsmul]; simp
  unfold finitePlaceBallIndicator
  rw [h1]
  by_cases h : n ≤ m
  · rw [if_pos h, Set.indicator_of_mem]
    show _ ∈ O(w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · rw [if_neg h, Set.indicator_of_notMem]
    show _ ∉ O(w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    rw [not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega


/-- Paper: Lemma 6.1.2.2(1)(1), p. 288.
The integer-unit invariants form a free Laurent module on the integer-ball indicator.
Deviation: A complex linear equivalence spells out the Laurent action by the generator
and the image of the free generator, without installing an extra module instance. -/
theorem finitePlaceSchwartz_invariants_laurent_free (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : LaurentPolynomial ℂ ≃ₗ[ℂ] (Representation.invariants (ρ(w))),
      (∀ x, (e 1).val (Multiplicative.ofAdd x) = finitePlaceBallIndicator w π 0 x) ∧
      ∀ P, (e (LaurentPolynomial.T 1 * P)).val =
        schwartzBruhatUnitTranslate π (e P).val := by sorry

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
The integer-unit invariants are closed in the local Schwartz–Bruhat space. -/
theorem finitePlaceSchwartz_invariants_isClosed (w : Places) :
    IsClosed (SetLike.coe (Representation.invariants (V := ℬᵥ(w)) (ρ(w))) : Set ℬᵥ(w)) :=
  unitInvariants_isClosed _

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
With the finest locally convex topology on Laurent polynomials, the monomial-to-ball
correspondence is a linear homeomorphism onto the unit invariants. -/
theorem finitePlaceSchwartz_invariants_laurent_equiv (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : FinestLocallyConvex (LaurentPolynomial ℂ) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ n x, (e (LaurentPolynomial.T n)).val (Multiplicative.ofAdd x) =
        finitePlaceBallIndicator w π n x := by sorry

end Laurent

section RelativeLaurent

-- TODO(paper-gap): Lemma 6.1.2.2(2), (6.1.2.5), specifies the projective
-- topology, but §2.1.4.2 uses the inductive topology on this algebraic tensor.
-- For ℚ with one new prime the invariant space is a locally convex direct sum
-- of copies of the real Schwartz space. The canonical tensor pairing into
-- this sum is separately continuous and is not jointly continuous.
-- TODO(paper-gap): After (6.1.2.9) the kernel is the image of the outside unit
-- group itself. Its intersection with the principal ideles is trivial by the
-- archimedean coordinate. The extra quotient by the S-units is unjustified.
-- TODO(paper-gap): The restriction used on p. 291 need not be compactly
-- supported on the multiplicative group, as the restriction of 1_{ℤₚ} shows.

open Classical in
/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5)–(6.1.2.6), p. 289.
The larger-stage relative unit invariants have a unique linear topological identification
with the S-local test space tensored with the multivariate Laurent polynomials.
Each pure tensor with a monomial multiplies the old test function by the indicated local balls.
Deviation: The tensor topology is inductive, following Corollary 2.1.4.2 as formalized. -/
theorem sLocalSchwartz_invariants_laurent_equiv (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (_hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val) :
    ∃! e : InductiveTensor ℬ(SAdeleRing F S)
        (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
        (Representation.invariants <| (schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
          (relativeIntegralIdeleUnits F S T).subtype),
      ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
        (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST.le w.property⟩)) *
            ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
              (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) := by sorry

end RelativeLaurent

section Averaging

-- These Borel structures agree with the local instances in Appendix A.3.
local instance instLocalUnitMeasurableSpaceCh06Sec1 (w : Places) :
    MeasurableSpace (L(w))ˣ := borel _

local notation "μ(" w ")" => finiteLocalMultiplicativeTamagawaMeasure F w

private theorem unitsMass_ne_top (w : Places) :
    μ(w) (U(w) : Set (L(w))ˣ) ≠ ⊤ := by
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits F w, ne_eq, ENNReal.inv_eq_top,
    ENNReal.ofReal_eq_zero, not_le]
  exact Real.sqrt_pos.2
    (pow_pos (Nat.cast_pos.2 (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm w))) _)

private theorem units_isCompact (w : Places) : IsCompact (U(w) : Set (L(w))ˣ) :=
  Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w))

private theorem units_isOpen (w : Places) : IsOpen (U(w) : Set (L(w))ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

private instance unitsRestrict_isFinite (w : Places) :
    IsFiniteMeasure ((μ(w)).restrict (U(w) : Set (L(w))ˣ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (unitsMass_ne_top w).lt_top⟩

private local instance instProperSpaceCh06Sec1 (w : Places) : ProperSpace (L(w)) :=
  properSpace_adicCompletion w
private local instance instSecondCountableUnitsCh06Sec1 (w : Places) :
    SecondCountableTopology (L(w))ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance instBorelUnitsCh06Sec1 (w : Places) : BorelSpace (L(w))ˣ := ⟨rfl⟩

/-- Paper: Lemma 6.1.2.4(1), p. 291.
The span of integer-unit translation differences is closed.
Consequently the algebraic and continuous coinvariant quotients use the same relations.
Deviation: The closure equality states both conclusions on the relation submodule. -/
theorem finitePlaceSchwartz_unitRelations_closure_eq (w : Places) :
    (Representation.Coinvariants.ker (ρ(w))).topologicalClosure =
      Representation.Coinvariants.ker (ρ(w)) := by sorry

/-- Paper: (6.1.2.14), p. 292.
Averaging a local test function evaluates it along the multiplicative orbit and integrates
over the integer units against the local multiplicative Tamagawa measure. -/
def finitePlaceUnitAverage (w : Places) (f : ℬᵥ(w)) (x : L(w)) : ℂ :=
  ∫ u : (L(w))ˣ, f (Multiplicative.ofAdd (x * u.val)) ∂((μ(w)).restrict (U(w)))

/-- Paper: (6.1.2.14), p. 292.
The orbit integral at zero is the value at zero times the Tamagawa mass of the integer units. -/
theorem finitePlaceUnitAverage_zero (w : Places) (f : ℬᵥ(w)) :
    finitePlaceUnitAverage w f 0 =
      ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ) *
        f (Multiplicative.ofAdd 0) := by sorry

/-- Paper: (6.1.2.14), p. 292.
Each integrand of the local averaging formula is integrable on the integer units. -/
theorem finitePlaceUnitAverage_integrable (w : Places) (f : ℬᵥ(w)) (x : L(w)) :
    IntegrableOn (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val)))
      (U(w) : Set (L(w))ˣ) (μ(w)) := by
  have hc : Continuous (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val))) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (continuous_const.mul Units.continuous_val))
  obtain ⟨C, hC⟩ := (units_isCompact w).exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound hc.aestronglyMeasurable C
    ((ae_restrict_iff' (units_isOpen w).measurableSet).2 (Filter.Eventually.of_forall hC))


/-- Paper: Lemma 6.1.2.4(2), (6.1.2.13)–(6.1.2.14), p. 292.
Local unit averaging defines a linear map to compactly supported continuous functions
which is continuous for their uniform norm. -/
theorem finitePlaceUnitAverage_continuous_uniform (w : Places) :
    ∃ A : ℬᵥ(w) →ₗ[ℂ] C_c(L(w), ℂ),
      (∀ f x, A f x = finitePlaceUnitAverage w f x) ∧
        Continuous (fun f ↦ (A f).toBoundedContinuousFunction) := by sorry

/-- Paper: Lemma 6.1.2.4(2), p. 292.
Local unit averaging also defines a continuous linear map in the intrinsic
Schwartz–Bruhat topology. -/
theorem finitePlaceUnitAverage_continuous_schwartzBruhat (w : Places) :
    ∃ A : ℬᵥ(w) →L[ℂ] ℬᵥ(w),
      ∀ f x, A f (Multiplicative.ofAdd x) = finitePlaceUnitAverage w f x := by sorry

/-- Paper: Lemma 6.1.2.4(2), p. 292.
A test function averages to zero exactly when it belongs to the span of unit
translation differences. -/
theorem finitePlaceUnitAverage_eq_zero_iff (w : Places) (f : ℬᵥ(w)) :
    (∀ x, finitePlaceUnitAverage w f x = 0) ↔
      f ∈ Representation.Coinvariants.ker (ρ(w)) := by sorry

-- TODO(paper-gap): The proof on p. 292 identifies multiplicative unit averaging
-- with additive convolution and deduces vanishing of the function from unramified
-- Mellin values. For the indicator of the integer ring at the trivial character,
-- the shell integrals in (6.1.2.17) all have the same positive mass. A nonzero
-- eigendistribution annihilates every unit difference only for unramified weight.
-- The kernel assertion follows by averaging the finite unit orbit of each test function.

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.15), p. 292.
Multiplicative unit averaging induces a linear homeomorphism from the algebraic
coinvariants with their quotient topology to the integer-unit invariants. -/
theorem finitePlaceUnitAverage_coinvariants_equiv (w : Places) :
    ∃ N : (ℬᵥ(w) ⧸ Representation.Coinvariants.ker (ρ(w))) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ (f : ℬᵥ(w)) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finitePlaceUnitAverage w f x := by sorry

local notation "K(" D ")" => FinitePlaceProduct F D
local notation "KUnits(" D ")" =>
  (Subgroup.pi Set.univ (fun w : D ↦ U(w.val))).comap
    (MulEquiv.piUnits (M := fun w : D ↦ L(w.val))).toMonoidHom
local notation "ρΠ(" D ")" =>
  (schwartzBruhatUnitRepresentation (R := K(D))).comp (KUnits(D)).subtype

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product of the local averages integrates the test function along its orbit
against the product of the restricted local multiplicative Tamagawa measures. -/
def finiteProductUnitAverage (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) : ℂ :=
  ∫ u : ∀ v : D, (L(v.val))ˣ,
    f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))
    ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val)))

/-- Paper: Lemma 6.1.2.4(3), p. 292.
At the zero tuple, product averaging multiplies the value there by the product
of the local integer-unit masses. -/
theorem finiteProductUnitAverage_zero (D : Finset Places) (f : ℬ(K(D))) :
    finiteProductUnitAverage D f 0 =
      (∏ w : D, ((μ(w.val) (U(w.val) : Set (L(w.val))ˣ)).toReal : ℂ)) *
        f (Multiplicative.ofAdd 0) := by
  unfold finiteProductUnitAverage
  simp only [Pi.zero_apply, zero_mul, integral_const]
  rw [Measure.real, Measure.pi_univ, ENNReal.toReal_prod, Complex.real_smul, Complex.ofReal_prod]
  simp only [Measure.restrict_apply_univ]
  rfl

private local instance (w : HeightOneSpectrum (𝓞 F)) : ProperSpace (L(w)) := properSpace_adicCompletion w
private local instance (w : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (L(w))ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product orbit integral is integrable against the finite product of the restricted measures. -/
theorem finiteProductUnitAverage_integrable (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) :
    Integrable
      (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val)))
      (Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))) := by
  have hc : Continuous (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (continuous_pi fun v ↦
        continuous_const.mul (Units.continuous_val.comp (continuous_apply v))))
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun v : D ↦ units_isCompact v.val).exists_bound_of_continuousOn
    hc.continuousOn
  refine Integrable.of_bound hc.aestronglyMeasurable C ?_
  have hae : ∀ᵐ u ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))),
      ∀ v : D, u v ∈ (U(v.val) : Set (L(v.val))ˣ) := by
    rw [ae_all_iff]
    intro v
    exact (Measure.tendsto_eval_ae_ae (μ := fun v : D ↦ (μ(v.val)).restrict (U(v.val))) (i := v)).eventually
      (ae_restrict_mem (units_isOpen v.val).measurableSet)
  filter_upwards [hae] with u hu
  exact hC u (Set.mem_univ_pi.2 hu)


/-- Paper: Lemma 6.1.2.4(3), p. 292.
The integer-unit invariants are closed in the Schwartz–Bruhat space on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductSchwartz_unitInvariants_isClosed (D : Finset Places) (_hD : D.Nonempty) :
    IsClosed ((Representation.invariants (ρΠ(D))) : Set ℬ(K(D))) :=
  unitInvariants_isClosed _

/-- Paper: Lemma 6.1.2.4(3), (6.1.2.16), p. 292.
The product of the local unit averages induces a linear homeomorphism from
coinvariants with their quotient topology to invariants on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductUnitAverage_coinvariants_equiv (D : Finset Places) (_hD : D.Nonempty) :
    ∃ N : (ℬ(K(D)) ⧸ Representation.Coinvariants.ker (ρΠ(D))) ≃L[ℂ] (Representation.invariants (ρΠ(D))),
      ∀ (f : ℬ(K(D))) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finiteProductUnitAverage D f x := by sorry

end Averaging

end RiemannMasullo
