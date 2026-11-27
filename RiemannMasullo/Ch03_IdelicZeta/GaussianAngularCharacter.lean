module

public import RiemannMasullo.Ch03_IdelicZeta.PrincipalAngularCharacter
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.GaussianPlaces
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# The fourth angular Hecke character of the Gaussian field

At the places (3), (2+i), (2−i), the local character values on the displayed prime
generators are 1, (−7−24i)/25 and (−7+24i)/25. These are the unramified local factors
in mccorvie’s Gaussian example for #7279, under the orientation fixed by the complex
completion. See also aadrianvv’s independent calculation on the issue.
-/

public section

noncomputable section

namespace RiemannMasullo.Gaussian

open IsDedekindDomain NumberField NumberField.Gaussian
open scoped ComplexConjugate

set_option quotPrecheck false

local notation "K" => CyclotomicField 4 ℚ
local notation "J" => SIdeleQuotient K finitePlaces
local notation "χ₀(" χ ")" => quasiCharacterNormTwist (sIdeleQuotientNorm K finitePlaces)
  (isProperMap_sIdeleQuotientNorm K finitePlaces).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) 0

private theorem gaussian_global_unit_four (t : (𝓞 (CyclotomicField 4 ℚ))ˣ) : t ^ 4 = 1 := by
  let e := Units.mapEquiv integersEquiv.toMulEquiv
  obtain ⟨u, rfl⟩ := e.surjective t
  rw [← map_pow, GaussianInt.unit_pow_four, map_one]

private theorem unitPhase_plus :
    (((2 + Complex.I : ℂ) / (‖2 + Complex.I‖ : ℂ)) ^ 4)⁻¹ = (-7 - 24 * Complex.I) / 25 := by
  have h : ‖(2 + Complex.I : ℂ)‖ ^ 2 = 5 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  have h4 : (‖(2 + Complex.I : ℂ)‖ : ℂ) ^ 4 = 25 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ← Complex.ofReal_pow, h]
    norm_num
  rw [div_pow, inv_div, h4]
  norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply,
    pow_succ, Complex.mul_re, Complex.mul_im]

private theorem unitPhase_minus :
    (((2 - Complex.I : ℂ) / (‖2 - Complex.I‖ : ℂ)) ^ 4)⁻¹ = (-7 + 24 * Complex.I) / 25 := by
  have h := congrArg (star : ℂ → ℂ) unitPhase_plus
  have hn : ‖(2 - Complex.I : ℂ)‖ = ‖(2 + Complex.I : ℂ)‖ := by
    calc
      _ = ‖star (2 + Complex.I : ℂ)‖ := by simp [sub_eq_add_neg]
      _ = _ := norm_star _
  rw [hn]
  simpa [sub_eq_add_neg] using h

/-- Paper: Theorem 7.1.2.3, p. 318. The fourth angular character on the actual three-place
Gaussian idèle quotient. The finite components compensate the angular value on every
diagonal S-unit.
Deviation: The concrete field and angular character are from the Gaussian example in #7279. -/
def angularCharacter : PontryaginDual J :=
  (exists_sLocal_fourthAngularCharacter place gen asIdeal_eq_span_gen gaussian_global_unit_four).choose

/-- The archimedean restriction has fourth angular weight in the complex orientation
of the completion used throughout the library. -/
theorem angularCharacter_infinite (z : place.Completionˣ) :
    sLocalInfiniteRestriction place (χ₀(angularCharacter)) z =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex isComplex_place z.val /
        (‖InfinitePlace.Completion.ringEquivComplexOfIsComplex isComplex_place z.val‖ : ℂ)) ^ 4 :=
  (exists_sLocal_fourthAngularCharacter place gen asIdeal_eq_span_gen gaussian_global_unit_four).choose_spec.1 z

/-- All three finite restrictions are unramified. -/
theorem angularCharacter_integerUnits (v : finitePlaces) :
    ∀ t ∈ (v.val.adicCompletionIntegers K).units, sLocalFiniteRestriction v (χ₀(angularCharacter)) t = 1 :=
  ((exists_sLocal_fourthAngularCharacter place gen asIdeal_eq_span_gen gaussian_global_unit_four).choose_spec.2 v).1

/-- The chosen Gaussian prime itself as a unit in the fraction field of the corresponding
completed local ring. -/
def primeUniformizer (v : finitePlaces) : (v.val.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom
    (Units.mk0 (gen v : K) ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2
      (primeGenerator_ne_zero v.val _ (asIdeal_eq_span_gen v))))

private theorem uniformizer_spec (v : finitePlaces) :
    ‖(primeUniformizer v).val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ ∧
      sLocalFiniteRestriction v (χ₀(angularCharacter)) (primeUniformizer v) =
        ((place.embedding (gen v : K) / (‖place.embedding (gen v : K)‖ : ℂ)) ^ 4)⁻¹ := by
  obtain ⟨p, hp, hn, hc⟩ :=
    ((exists_sLocal_fourthAngularCharacter place gen asIdeal_eq_span_gen gaussian_global_unit_four).choose_spec.2 v).2
  have e : p = primeUniformizer v := Units.ext hp
  exact e ▸ And.intro hn hc

/-- The chosen uniformizers have the project’s normalized reciprocal residue norm. -/
theorem norm_primeUniformizer (v : finitePlaces) :
    ‖(primeUniformizer v).val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ := (uniformizer_spec v).1

/-- The angular character takes value one on the inert uniformizer three. -/
theorem angularCharacter_three :
    sLocalFiniteRestriction threeMember (χ₀(angularCharacter)) (primeUniformizer threeMember) = 1 := by
  rw [(uniformizer_spec threeMember).2, gen_threeMember, embedding_integersEquiv]
  norm_num [GaussianInt.toComplex_def]

/-- At the norm-five place generated by 2+i the inverse fourth angular power has
negative imaginary part. -/
theorem angularCharacter_two_add_i :
    sLocalFiniteRestriction plusMember (χ₀(angularCharacter)) (primeUniformizer plusMember) =
      (-7 - 24 * Complex.I) / 25 := by
  rw [(uniformizer_spec plusMember).2, gen_plusMember, embedding_integersEquiv]
  simpa [GaussianInt.toComplex_def'] using unitPhase_plus

/-- The other norm-five place has the conjugate character value. -/
theorem angularCharacter_two_sub_i :
    sLocalFiniteRestriction minusMember (χ₀(angularCharacter)) (primeUniformizer minusMember) =
      (-7 + 24 * Complex.I) / 25 := by
  rw [(uniformizer_spec minusMember).2, gen_minusMember, embedding_integersEquiv]
  simpa [GaussianInt.toComplex_def', sub_eq_add_neg] using unitPhase_minus

private theorem splitPhase_not_isOfFinOrder : ¬ IsOfFinOrder ((-7 - 24 * Complex.I) / 25) := by
  let z : ℂ := (-7 - 24 * Complex.I) / 25
  intro h
  have hfin : IsOfFinOrder z := h
  have hfin' : IsOfFinOrder (star z) := by
    obtain ⟨n, hn, he⟩ := hfin.exists_pow_eq_one
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
    change (starRingEnd ℂ z) ^ n = 1
    rw [← map_pow, he, map_one]
  have hz : IsIntegral ℤ z := (IsPrimitiveRoot.orderOf z).isIntegral hfin.orderOf_pos
  have hz' : IsIntegral ℤ (star z) := (IsPrimitiveRoot.orderOf (star z)).isIntegral hfin'.orderOf_pos
  have htrace : z + star z = (((-14 / 25) : ℚ) : ℂ) := by
    norm_num [z, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hi := hz.add hz'
  rw [htrace] at hi
  have hiq : IsIntegral ℤ (-14 / 25 : ℚ) := isIntegral_ratCast_iff.mp hi
  obtain ⟨k, hk⟩ : ∃ k : ℤ, algebraMap ℤ ℚ k = (-14 / 25 : ℚ) := IsIntegrallyClosed.isIntegral_iff.mp hiq
  have ha : (k : ℚ) * 25 = -14 := (eq_div_iff (by norm_num)).mp hk
  have hb : k * 25 = -14 := by exact_mod_cast ha
  omega

private def finiteClass (v : finitePlaces) (g : (v.val.adicCompletion K)ˣ) : J :=
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing K) ((v : finitePlaces) → v.val.adicCompletion K)
  let f := ContinuousMulEquiv.piUnits (M := fun v : finitePlaces ↦ v.val.adicCompletion K)
  QuotientGroup.mk (e.symm (1, f.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v g)))

private theorem finiteClass_norm (v : finitePlaces) (g : (v.val.adicCompletion K)ˣ) :
    ((sIdeleQuotientNorm K finitePlaces (finiteClass v g) : NNReal) : ℝ) = ‖g.val‖ := by
  have h := sLocalFiniteRestriction_norm v g
  change (((1 : PontryaginDual J) (finiteClass v g) : Circle) : ℂ) *
    (((sIdeleQuotientNorm K finitePlaces (finiteClass v g) : NNReal) : ℝ) : ℂ) ^ (1 : ℂ) = (‖g.val‖ : ℂ) at h
  simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one,
    Complex.ofReal_inj] using h

private theorem finiteClass_character (v : finitePlaces) (g : (v.val.adicCompletion K)ˣ) :
    (angularCharacter (finiteClass v g) : ℂ) = sLocalFiniteRestriction v (χ₀(angularCharacter)) g := by
  change (angularCharacter (finiteClass v g) : ℂ) =
    (angularCharacter (finiteClass v g) : ℂ) * _ ^ (0 : ℂ)
  rw [Complex.cpow_zero, mul_one]

/-- The quotient of the two split uniformizers has idèle norm one and nontorsion
character value. In particular the angular character retains infinite order after
restriction to the norm-one idèle classes. -/
theorem exists_normOne_angularCharacter_nontorsion :
    ∃ x : (sIdeleQuotientNorm K finitePlaces).ker, ¬ IsOfFinOrder (angularCharacter x.val : ℂ) := by
  let a := finiteClass plusMember (primeUniformizer plusMember)
  let b := finiteClass minusMember (primeUniformizer minusMember)
  have hab : sIdeleQuotientNorm K finitePlaces a = sIdeleQuotientNorm K finitePlaces b := by
    apply Units.ext
    apply NNReal.coe_injective
    change ((sIdeleQuotientNorm K finitePlaces (finiteClass _ _) : NNReal) : ℝ) = _
    rw [finiteClass_norm]
    change _ = ((sIdeleQuotientNorm K finitePlaces (finiteClass _ _) : NNReal) : ℝ)
    rw [finiteClass_norm, norm_primeUniformizer, norm_primeUniformizer]
    simp
  refine ⟨⟨a / b, by change sIdeleQuotientNorm K finitePlaces (a / b) = 1; rw [map_div, hab, div_self']⟩, ?_⟩
  have hφ : (angularCharacter (a / b) : ℂ) = ((-7 - 24 * Complex.I) / 25) ^ 2 := by
    rw [map_div, Circle.coe_div]
    change (angularCharacter (finiteClass _ _) : ℂ) / (angularCharacter (finiteClass _ _) : ℂ) = _
    rw [finiteClass_character, finiteClass_character, angularCharacter_two_add_i, angularCharacter_two_sub_i]
    norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      pow_succ, Complex.mul_re, Complex.mul_im]
  change ¬ IsOfFinOrder (angularCharacter (a / b) : ℂ)
  rw [hφ]
  intro h
  obtain ⟨n, hn, he⟩ := h.exists_pow_eq_one
  apply splitPhase_not_isOfFinOrder
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2*n, by omega, (pow_mul _ _ _).trans he⟩


/-- The fourth angular character is the restriction of a genuine global unitary Hecke
character unramified outside these three Gaussian places. -/
theorem exists_global_angularCharacter :
    ∃ ψ : PontryaginDual (IdeleClassGroup (𝓞 K) K),
      ∃ hψ : (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ ∈ unramifiedOutside K finitePlaces,
        sIdeleRestriction K finitePlaces ⟨_, hψ⟩ =
          (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp angularCharacter :=
  exists_unitary_unramifiedOutside_extension angularCharacter

end RiemannMasullo.Gaussian
