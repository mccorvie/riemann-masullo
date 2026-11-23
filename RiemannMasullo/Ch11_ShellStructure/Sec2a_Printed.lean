module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch11_ShellStructure.Sec2a

/-! # §11.2.0 assertions that are false as printed -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "restriction(" F ")" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "logNorm(" F ")" =>
  (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "μ'(" F ", " s ")" => (μ(F)).withDensity (fun g ↦
  ENNReal.ofReal (intervalSobolevDensity 0 0 (s) (logNorm(F) g))⁻¹)
local notation "W(" F ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) 0 0 s
local notation "W'(" F ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) 0 0 s true
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "H(" F ", " hs ")" => globalThetaSobolev F 0 hI hs
local notation "ρ(" F ", " hs ")" =>
  hardySobolevTranslation (μ(F))
    (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ) 0 0 _ hI hs
local notation "Wω(" F ", " hs ", " ω ")" =>
  actionIsotype ((ρ(F, hs)).comp (ideleClassNorm F).ker.subtype) ω
local notation "frequency(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "jet(" χ ", " t ", " m ")" => spectralZeroJet χ 0 t m

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. The range of the extended
principal-value map is asserted to be closed for degree at least twice the set size. -/
def Printed.globalThetaSobolevPrincipalValue_closedRange : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)) (s : ℝ) (hs : 0 ≤ s),
    2 * (S.card : ℝ) ≤ s →
    IsClosed (range (globalThetaSobolevPrincipalValue F S 0 hs))

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. Take ℚ, S₀ = {2}, degree 2
and the trivial isotype, identified with the log-line space by zero-line density.
The prime difference is injective there since a nonzero
periodic function cannot be in weighted L². For any nonzero smooth ψ supported
in (1,2), the ratio of the norms of the difference of ψ(x/R) and of ψ(x/R)
tends to zero. The isotype projection commutes with the operator, so its
nonclosed range on this isotype also rules out closed range on the full space. -/
theorem Printed.globalThetaSobolevPrincipalValue_closedRange_false :
    ¬ Printed.globalThetaSobolevPrincipalValue_closedRange := by sorry

/-- Paper: Lead-in to (11.2.0.3), p. 484. At every twist and nonnegative
degree the completed PV map is a closed embedding whose image equals the
completion of its test image. -/
def Printed.globalThetaSobolevPrincipalValue_isClosedEmbedding : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let P := globalThetaSobolevPrincipalValue F S a hs
    let j := globalThetaSobolevInclusion F a hI hs
    Topology.IsClosedEmbedding P ∧ range P =
      closure (range fun f : ↥(adelePolarSubspace F) ↦ P (j (Submodule.Quotient.mk f)))

/-- Paper: Lead-in to (11.2.0.3), p. 484. The case a = 0, s = 2,
F = ℚ and S = {2} already has nonclosed image. -/
theorem Printed.globalThetaSobolevPrincipalValue_isClosedEmbedding_false :
    ¬ Printed.globalThetaSobolevPrincipalValue_isClosedEmbedding := by
  intro h
  apply Printed.globalThetaSobolevPrincipalValue_closedRange_false
  intro F _ _ S s hs _
  exact (h F S 0 s hs).1.isClosed_range

/-- Paper: Theorem 11.2.0.2(1), p. 485. For each represented rational prime p,
the reciprocal product over S equals the product of the local denominators
over the places of S above p. Use the reciprocal factors of §6.3.1. -/
def Printed.orbitalEulerProduct_eq_primary : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ p : HeightOneSpectrum (𝓞 ℚ), (sLocalPrimaryPlaces S p).Nonempty → ∀ z : ℂ,
      reciprocalPartialHeckeEulerProduct χ S z =
        reciprocalPartialHeckeEulerProduct χ (sLocalPrimaryPlaces S p) z

private theorem Printed.orbitalEulerProduct_eq_primary_false_twoPlaces :
    ∃ v w : HeightOneSpectrum (𝓞 ℚ), v ≠ w := by
  have hP (p : ℤ) (hp : Prime p) :
      (Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {p})).IsPrime :=
    Ideal.IsPrime.comap _ (hK := (Ideal.span_singleton_prime hp.ne_zero).mpr hp)
  have hB (p : ℤ) (hp : Prime p) :
      Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {p}) ≠ ⊥ := by
    intro h
    have := Ideal.map_comap_of_surjective _ Rat.ringOfIntegersEquiv.surjective (Ideal.span {p})
    rw [h, Ideal.map_bot] at this
    exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp this.symm)
  have h2 : Prime (2 : ℤ) := Int.prime_two
  have h3 : Prime (3 : ℤ) := Int.prime_three
  refine ⟨⟨_, hP 2 h2, hB 2 h2⟩, ⟨_, hP 3 h3, hB 3 h3⟩, fun h ↦ ?_⟩
  have h' := congrArg HeightOneSpectrum.asIdeal h
  have := Ideal.comap_injective_of_surjective _ Rat.ringOfIntegersEquiv.surjective h'
  have hmem : (2 : ℤ) ∈ Ideal.span {(3 : ℤ)} := this ▸ Ideal.mem_span_singleton_self 2
  rw [Ideal.mem_span_singleton] at hmem
  omega

private theorem Printed.orbitalEulerProduct_eq_primary_false_trivial
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).IsUnramifiedAt v ∧
      (finiteHeckeEulerFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) v 1)⁻¹ =
        1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ := by
  have hr (u : (v.adicCompletion ℚ)ˣ) :
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).restrict v
        (u : v.adicCompletion ℚ) = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (1 : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨u, hu⟩ :=
    (Valued.v : Valuation (v.adicCompletion ℚ) _).exists_isUniformizer_of_isCyclic_of_nontrivial
  have hχ : (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).IsUnramifiedAt
      v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hr (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom x)
  have hl := (hχ.localValue_eq _ hu).trans (hr (Units.mk0 (u : v.adicCompletion ℚ) hu.ne_zero))
  refine ⟨hχ, ?_⟩
  rw [finiteHeckeEulerFactor, ite_eq_left hχ, inv_inv, hl, one_mul, Complex.cpow_neg_one]

/-- Paper: Theorem 11.2.0.2(1), p. 485. Over ℚ with trivial character,
S = {2,3}, p = 2, and z = 1, the two sides are 1/3 and 1/2. -/
theorem Printed.orbitalEulerProduct_eq_primary_false :
    ¬ Printed.orbitalEulerProduct_eq_primary := by
  intro h
  classical
  obtain ⟨v, w, hvw⟩ := Printed.orbitalEulerProduct_eq_primary_false_twoPlaces
  obtain ⟨hv, hav⟩ := Printed.orbitalEulerProduct_eq_primary_false_trivial v
  obtain ⟨hw, haw⟩ := Printed.orbitalEulerProduct_eq_primary_false_trivial w
  have hunder (u : HeightOneSpectrum (𝓞 ℚ)) : u.under (𝓞 ℚ) = u :=
    HeightOneSpectrum.ext (Ideal.comap_id u.asIdeal)
  have hprim : sLocalPrimaryPlaces ({v, w} : Finset _) v = {v} := by
    ext u
    rw [mem_sLocalPrimaryPlaces, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
    erw [hunder]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨Or.inl h, h⟩
  have key := h ℚ 1 {v, w} (by simp [hv, hw]) v (by rw [hprim]; simp) 1
  rw [hprim, reciprocalPartialHeckeEulerProduct, reciprocalPartialHeckeEulerProduct,
    Finset.prod_pair hvw, Finset.prod_singleton, hav, haw] at key
  have hv1 : (1 : ℂ) - (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, inv_ne_one]
    have : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    exact_mod_cast this
  have hw0 : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 := by
    have : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast this
  have := mul_left_cancel₀ hv1 (key.trans (mul_one _).symm)
  rw [sub_eq_self, inv_eq_zero] at this
  exact hw0 this

/-- Paper: Theorem 11.2.0.2 and (11.2.0.6), p. 485. Every jet admitted by
the printed floor cutoff is asserted to lie in the conjugate reciprocal-weight isotype. -/
def Printed.orbitalJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ), 0 ≤ s → ∀ (t : ℝ) (m : ℕ),
      reciprocalPartialHeckeEulerProduct χ S (frequency(t)) = 0 →
      m < min (orbitalEulerMultiplicity χ S (frequency(t))) (Nat.floor ((s - 1) / 2 + 1)) →
      ∃ h : MemLp (jet(χ, t, m)) 2 (μ'(F, s)),
        let u := h.toLp (jet(χ, t, m))
        ∀ k : C₁(F), (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ(F)] fun g ↦ (χ⁻¹ k.val : ℂ) * u g

/-- The reciprocal of the square root of `1 + x²` is not integrable on the line: on `(1, ∞)` it
dominates `x⁻¹ / 2`. -/
private theorem Printed.orbitalJet_memLp_false_line :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ ((1 : ℝ) / 2))⁻¹ = ⊤ := by
  by_contra hfin
  have hmeas : Measurable fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ 2) ^ ((1 : ℝ) / 2))⁻¹ := by
    fun_prop
  have hint := integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin
  have hint' : IntegrableOn (fun x : ℝ ↦ 2 * ((1 + x ^ 2) ^ ((1 : ℝ) / 2))⁻¹) (Ioi 1) := by
    refine IntegrableOn.congr_fun ((hint.const_mul 2).integrableOn (s := Ioi 1))
      (fun x _ ↦ ?_) measurableSet_Ioi
    change 2 * (ENNReal.ofReal _).toReal = _
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))]
  apply not_integrableOn_Ioi_inv (a := 1)
  refine hint'.mono' (by fun_prop) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hx0.le)]
  have hsq : (1 + x ^ 2) ^ ((1 : ℝ) / 2) ≤ 2 * x := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by linarith)]
    nlinarith
  have hpos : 0 < (1 + x ^ 2) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [le_mul_inv_iff₀ hpos, inv_mul_eq_div, div_le_iff₀ hx0]
  linarith

/-- The reciprocal Euler factor of the trivial character over ℚ vanishes at zero at every
finite place. -/
private theorem Printed.orbitalJet_memLp_false_factor (v : V(ℚ)) :
    (finiteHeckeEulerFactor (1 : PontryaginDual C𝔽(ℚ)) v 0)⁻¹ = 0 := by
  obtain ⟨hv, -⟩ := Printed.orbitalEulerProduct_eq_primary_false_trivial v
  have hπ := (Valued.v : Valuation (v.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
  rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
  have h1 : ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0 = 1 := by
    ext g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  rw [h1]
  simp [HeckeCharacter.localValue, hπ.ne_zero]

/-- A function of the log-norm whose integral over the line is infinite has infinite integral
over the idele classes of ℚ: Haar measure is a positive multiple of the canonical one, which the
log-norm pushes forward to Lebesgue measure. -/
private theorem Printed.orbitalJet_memLp_false_push (ψ : ℝ → ENNReal) (hψ : Measurable ψ)
    (htop : ∫⁻ x : ℝ, ψ x = ⊤) : ∫⁻ g, ψ (logNorm(ℚ) g) ∂(μ(ℚ)) = ⊤ := by
  have hm : IsModulation (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ :
      C𝔽(ℚ) →ₜ* ℝ≥0ˣ) := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  let ν : Measure C𝔽(ℚ) := canonicalModulatedHaar _ hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar _ hm).exists.choose_spec.1
  rw [Measure.isMulLeftInvariant_eq_smul (μ(ℚ)) ν, lintegral_smul_measure,
    (orbitalJet_logNorm_measurePreserving (F := ℚ)).lintegral_comp hψ, htop]
  exact ENNReal.mul_top (by exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne')

/-- Over ℚ the reciprocal Sobolev measure of degree one has infinite total mass. -/
private theorem Printed.orbitalJet_memLp_false_mass : (μ'(ℚ, 1)) univ = ⊤ := by
  let φ : ℝ → ENNReal := fun x ↦ ENNReal.ofReal ((1 + x ^ 2) ^ ((1 : ℝ) / 2))⁻¹
  have hdens (g : C𝔽(ℚ)) : ENNReal.ofReal (intervalSobolevDensity 0 0 1 (logNorm(ℚ) g))⁻¹ =
      φ (logNorm(ℚ) g) := by
    simp only [φ, intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_congr hdens]
  exact Printed.orbitalJet_memLp_false_push φ (by fun_prop) Printed.orbitalJet_memLp_false_line

/-- Paper: Theorem 11.2.0.2 and (11.2.0.6), p. 485. Over ℚ with the trivial
character and S₀ = {2}, the factor 1 − 2⁻ᶻ has a simple zero at 0. At degree
1 the printed floor admits the constant jet. Its squared norm diverges
because the reciprocal weight is asymptotic to 1/|x|. -/
theorem Printed.orbitalJet_memLp_false : ¬ Printed.orbitalJet_memLp := by
  intro h
  classical
  obtain ⟨v, -, -⟩ := Printed.orbitalEulerProduct_eq_primary_false_twoPlaces
  obtain ⟨hv, -⟩ := Printed.orbitalEulerProduct_eq_primary_false_trivial v
  have hf0 : frequency((0 : ℝ)) = 0 := by simp
  have hfac := Printed.orbitalJet_memLp_false_factor v
  have hz : reciprocalPartialHeckeEulerProduct (1 : PontryaginDual C𝔽(ℚ)) {v}
      (frequency((0 : ℝ))) = 0 := by
    rw [hf0, reciprocalPartialHeckeEulerProduct, Finset.prod_singleton, hfac]
  have hmult : orbitalEulerMultiplicity (1 : PontryaginDual C𝔽(ℚ)) {v} (frequency((0 : ℝ))) = 1 := by
    rw [orbitalEulerMultiplicity_eq_card, hf0, Finset.filter_singleton, if_pos hfac,
      Finset.card_singleton]
  obtain ⟨hmem, -⟩ := h ℚ 1 {v} (by simpa using hv) 1 zero_le_one 0 0 hz (by
    rw [hmult]; norm_num)
  have hjet : (jet((1 : PontryaginDual C𝔽(ℚ)), 0, 0) : C𝔽(ℚ) → ℂ) = fun _ ↦ 1 := by
    funext g
    rw [spectralZeroJet_zero]
    rfl
  rw [hjet] at hmem
  have hne := hmem.eLpNorm_lt_top
  rw [eLpNorm_const' _ two_ne_zero ENNReal.ofNat_ne_top, Printed.orbitalJet_memLp_false_mass]
    at hne
  simp at hne

/-- Paper: Theorem 11.2.0.2, p. 485. The jet vectors form a Markushevich
basis of the PV annihilator taken in the full negative space with its subspace topology. -/
def Printed.orbitalJets_basis_fullAnnihilator : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ) (hs : 0 ≤ s), 2 * (S.card : ℝ) ≤ s →
      let ω := χ.comp (restriction(F))
      let J := {j : ℝ × ℕ //
        j.2 < min (orbitalEulerMultiplicity χ S (frequency(j.1)))
          (Nat.floor ((s - 1) / 2 + 1))}
      ∃ A : Submodule ℂ W'(F, s),
        (A : Set W'(F, s)) = {ψ | ∀ f : H(F, hs), (f : W(F, s)) ∈ Wω(F, hs, ω) →
          spectralSobolevPairing ((globalThetaSobolevPrincipalValue F S 0 hs f).val) ψ = 0} ∧
        ∃ (u : J → A) (Λ : J → StrongDual ℂ A),
          (∀ j, ((u j).val : C𝔽(F) → ℂ) =ᵐ[μ(F)] jet(χ, j.val.1, j.val.2)) ∧
          IsSpectralMarkushevichBasis u Λ

/-- Paper: Theorem 11.2.0.2, p. 485. Over ℚ take the trivial character,
S₀ = {2}, and degree 2. Every jet is constant on the compact norm-one factor
Ẑ×. The nontrivial quadratic character modulo 3 on that factor defines a
nonzero negative-space vector annihilating the whole trivial isotype. It lies
outside its closed trivial isotype and hence outside the closed jet span. -/
theorem Printed.orbitalJets_basis_fullAnnihilator_false :
    ¬ Printed.orbitalJets_basis_fullAnnihilator := by sorry

/-- Paper: Remark 11.2.0.3, p. 485. The dual of the quotient by the entire
isotypic theta space is identified by the pairing with the PV annihilator
in the ambient negative space, with its subspace topology. -/
def Printed.orbitalQuotientDual_missingPV : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) → ∀ (s : ℝ) (hs : 0 ≤ s),
      let ω := χ.comp (restriction(F))
      let Q := spectralSobolevIsotypeQuotient F 0 hI hs ω
      let N := (globalThetaSobolev F 0 hI hs).comap (Wω(F, hs, ω)).subtype
      ∃ D : StrongDual ℂ Q →L[ℂ] W'(F, s), Topology.IsEmbedding D ∧
        range D = {ψ | ∀ f : H(F, hs), (f : W(F, s)) ∈ Wω(F, hs, ω) →
          spectralSobolevPairing (globalThetaSobolevPrincipalValue F S 0 hs f).val ψ = 0} ∧
        ∀ (Λ : StrongDual ℂ Q) (f : Wω(F, hs, ω)), spectralSobolevPairing f.val (D Λ) =
          Λ (N.mkQ f)

/-- The trivial unitary character of the idele class group of ℚ, untwisted, is the
trivial quasi-character. -/
private theorem trivialTwist_eq_one :
    ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0 = 1 := by
  ext g
  change (1 : ℂ) * _ ^ (0 : ℂ) = 1
  simp

/-- The trivial character is unramified at every finite place of ℚ. -/
private theorem trivialTwist_isUnramifiedAt (v : V(ℚ)) :
    (ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0).IsUnramifiedAt v := by
  rw [trivialTwist_eq_one, HeckeCharacter.isUnramifiedAt_iff]
  intro x
  simp

/-- The reciprocal Euler factor of the trivial character vanishes at zero at every
finite place of ℚ. -/
private theorem trivialTwist_factor (v : V(ℚ)) :
    (finiteHeckeEulerFactor (1 : PontryaginDual C𝔽(ℚ)) v 0)⁻¹ = 0 := by
  rw [finiteHeckeEulerFactor, ite_eq_left (trivialTwist_isUnramifiedAt v), inv_inv,
    trivialTwist_eq_one]
  have hπ := (Valued.v : Valuation (v.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
  simp [HeckeCharacter.localValue, hπ.ne_zero]

/-- A functional on a quotient that takes the value one somewhere cannot vanish on
every class. -/
private theorem functional_ne_of_pairing_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N : Submodule ℂ E) [TopologicalSpace (E ⧸ N)] (Λ : (E ⧸ N) →L[ℂ] ℂ) (q : E ⧸ N)
    (hq : Λ q = 1) (p : E → ℂ) (hp : ∀ f, Λ (N.mkQ f) = p f) (h0 : ∀ f, p f = 0) : False := by
  obtain ⟨f, rfl⟩ := N.mkQ_surjective q
  rw [hp, h0] at hq
  exact zero_ne_one hq

/-- A continuous linear map commuting with a group action that restricts an ambient
action preserves every ambient isotype. -/
private theorem mem_actionIsotype_of_commute {K E : Type*} [Monoid K] [TopologicalSpace K]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (ρ : K →* (E →L[ℂ] E))
    (ω : PontryaginDual K) (H : Submodule ℂ E) (R : K → H →L[ℂ] H)
    (hR : ∀ k u, (R k u : E) = ρ k u) (P : H →L[ℂ] H) (hP : ∀ k u, P (R k u) = R k (P u))
    (u : H) (hu : (u : E) ∈ actionIsotype ρ ω) : (P u : E) ∈ actionIsotype ρ ω := by
  rw [mem_actionIsotype] at hu ⊢
  intro k
  have hRk : R k u = (ω k : ℂ) • u := Subtype.ext ((hR k u).trans (hu k))
  rw [← hR, ← hP, hRk, map_smul]
  rfl

/-- The image of a vector under a map of a submodule lies in the closure of the range. -/
private theorem mem_comap_closure_range {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] (H K : Submodule ℂ E)
    (P : H →L[ℂ] H) (f : H) (hf : (P f : E) ∈ K) :
    (⟨_, hf⟩ : K) ∈ ((H.subtype.comp P.toLinearMap).range.topologicalClosure).comap
      K.subtype :=
  Submodule.le_topologicalClosure _ ⟨f, rfl⟩

/-- A functional on a quotient vanishes on the class of a vector of the submodule. -/
private theorem functional_mkQ_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N : Submodule ℂ E) [TopologicalSpace (E ⧸ N)] (Λ : (E ⧸ N) →L[ℂ] ℂ) {x : E}
    (hx : x ∈ N) : Λ (N.mkQ x) = 0 := by
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hx, map_zero]

/-- The pullback of the whole space to a submodule is the whole submodule. -/
private theorem comap_subtype_eq_top_of_eq_top {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H K : Submodule ℂ E) (hH : H = ⊤) : H.comap K.subtype = ⊤ := by
  rw [hH, Submodule.comap_top]

/-- A continuous linear functional on the quotient by the whole space is zero. -/
private theorem strongDual_quotient_top_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N : Submodule ℂ E) (hN : N = ⊤) [TopologicalSpace (E ⧸ N)] (Λ : (E ⧸ N) →L[ℂ] ℂ) :
    Λ = 0 := by
  have : Subsingleton (E ⧸ N) := Submodule.Quotient.subsingleton_iff.2 hN
  ext q
  rw [Subsingleton.elim q 0, map_zero, map_zero]

/-- Paper: Remark 11.2.0.3, p. 485. Take ℚ, S₀ = {2}, degree 2, and the
trivial isotype. Integration is nonzero and continuous on that positive
isotype and kills the prime difference. The quotient by the full theta
completion is zero by 0-line density. -/
theorem Printed.orbitalQuotientDual_missingPV_false :
    ¬ Printed.orbitalQuotientDual_missingPV := by
  intro h
  let v : V(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hunr : ∀ w ∈ ({v} : Finset V(ℚ)),
      (ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0).IsUnramifiedAt w :=
    fun w _ ↦ trivialTwist_isUnramifiedAt w
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  obtain ⟨D, -, hrange, hcomp⟩ := h ℚ 1 {v} hunr 2 hs
  have htop : globalThetaSobolev ℚ 0 hI hs = ⊤ := by
    apply (Submodule.dense_iff_topologicalClosure_eq_top).1
    refine (denseRange_globalTheta_zeroLine (F := ℚ) hs).mono ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hN : (globalThetaSobolev ℚ 0 hI hs).comap
      (Wω(ℚ, hs, (1 : PontryaginDual C𝔽(ℚ)).comp (restriction(ℚ)))).subtype = ⊤ :=
    comap_subtype_eq_top_of_eq_top _ _ htop
  obtain ⟨-, x, Λ, hbasis, hpair⟩ :=
    orbitalMarkushevichBasis (F := ℚ) 1 {v} hs (by norm_num) hunr
  let j0 : OrbitalJetIndex (1 : PontryaginDual C𝔽(ℚ)) {v} 2 := ⟨((0 : ℝ), 0), by
    rw [lt_spectralBoundaryMultiplicity, orbitalEulerMultiplicity_eq_card]
    refine ⟨?_, by norm_num⟩
    simp [trivialTwist_factor]⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ∀ f, Λ j0 ((orbitalSobolevSubmodule ℚ {v} hs
      ((1 : PontryaginDual C𝔽(ℚ)).comp (restriction(ℚ)))).mkQ f) =
        spectralSobolevPairing f.val ψ := ⟨_, hpair j0⟩
  let R := (exists_globalThetaSobolevAction (F := ℚ) 0 hI hs).choose
  have hR := (exists_globalThetaSobolevAction (F := ℚ) 0 hI hs).choose_spec.1
  have hann : ψ ∈ range D := by
    rw [hrange]
    intro f hf
    have hPf : ((globalThetaSobolevPrincipalValue ℚ {v} 0 hs f : H(ℚ, hs)) : W(ℚ, 2)) ∈
        Wω(ℚ, hs, (1 : PontryaginDual C𝔽(ℚ)).comp (restriction(ℚ))) := by
      have heq := fun k : C₁(ℚ) ↦
        globalThetaSobolevPrincipalValue_equivariant (F := ℚ) {v} 0 hs k
      exact mem_actionIsotype_of_commute _ _ _ (fun k ↦ R k.val) (fun k ↦ hR k.val)
        (globalThetaSobolevPrincipalValue ℚ {v} 0 hs) heq f hf
    have hmem : (⟨_, hPf⟩ : Wω(ℚ, hs, (1 : PontryaginDual C𝔽(ℚ)).comp (restriction(ℚ)))) ∈
        orbitalSobolevSubmodule ℚ {v} hs ((1 : PontryaginDual C𝔽(ℚ)).comp (restriction(ℚ))) := by
      unfold orbitalSobolevSubmodule
      exact mem_comap_closure_range _ _ _ f hPf
    exact (hψ ⟨_, hPf⟩).symm.trans (functional_mkQ_eq_zero _ _ hmem)
  obtain ⟨Λ', rfl⟩ := hann
  exact functional_ne_of_pairing_zero _ (Λ j0) (x j0) (hbasis.1 j0) _ hψ
    (fun f ↦ by rw [hcomp Λ' f, strongDual_quotient_top_eq_zero _ hN Λ']; rfl)


/-- Paper: (11.2.0.8), p. 486. Every full-order jet must have a representative
in the specified subset of the printed negative Sobolev isotype. -/
def Printed.orbitalJetsIn {F : Type} [Field F] [NumberField F]
    (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)) (s : ℝ) (B : Set W'(F, s)) : Prop :=
  ∀ (t : ℝ) (m : ℕ), reciprocalPartialHeckeEulerProduct χ S (frequency(t)) = 0 →
    m < orbitalEulerMultiplicity χ S (frequency(t)) →
    ∃ h : MemLp (jet(χ, t, m)) 2 (μ'(F, s)),
      let u := h.toLp (jet(χ, t, m))
      (∀ k : C₁(F), (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ(F)] fun g ↦ (χ k.val : ℂ) * u g) ∧
      u ∈ B

/-- Paper: Proposition 11.2.0.4 and (11.2.0.9), p. 486. The full-multiplicity
family belongs to the annulus in the printed positive-character isotype. -/
def Printed.orbitalJet_norm_annulus : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
      Printed.orbitalJetsIn χ S s {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C}

/-- The function `x² / (1 + x²)^{3/2}` is not integrable on the line: on `(1, ∞)` it dominates
`x⁻¹ / 8`. -/
private theorem Printed.orbitalJet_norm_annulus_false_line :
    ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2 * ((1 + x ^ 2) ^ ((3 : ℝ) / 2))⁻¹) = ⊤ := by
  by_contra hfin
  have hmeas : Measurable fun x : ℝ ↦ ENNReal.ofReal (x ^ 2 * ((1 + x ^ 2) ^ ((3 : ℝ) / 2))⁻¹) := by
    fun_prop
  have hint := integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin
  have hint' : IntegrableOn (fun x : ℝ ↦ 8 * (x ^ 2 * ((1 + x ^ 2) ^ ((3 : ℝ) / 2))⁻¹)) (Ioi 1) := by
    refine IntegrableOn.congr_fun ((hint.const_mul 8).integrableOn (s := Ioi 1))
      (fun x _ ↦ ?_) measurableSet_Ioi
    change 8 * (ENNReal.ofReal _).toReal = _
    rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
      (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)))]
  apply not_integrableOn_Ioi_inv (a := 1)
  refine hint'.mono' (by fun_prop) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hx0.le)]
  have hsq : (1 + x ^ 2) ^ ((1 : ℝ) / 2) ≤ 2 * x := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by linarith)]
    nlinarith
  have hcube : (1 + x ^ 2) ^ ((3 : ℝ) / 2) ≤ 8 * x ^ 3 := by
    have h3 : (1 + x ^ 2) ^ ((3 : ℝ) / 2) = ((1 + x ^ 2) ^ ((1 : ℝ) / 2)) ^ 3 := by
      rw [← Real.rpow_natCast ((1 + x ^ 2) ^ ((1 : ℝ) / 2)) 3, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h3]
    calc ((1 + x ^ 2) ^ ((1 : ℝ) / 2)) ^ 3 ≤ (2 * x) ^ 3 :=
          pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hsq 3
      _ = 8 * x ^ 3 := by ring
  have hpos : 0 < (1 + x ^ 2) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hpos]
  calc x⁻¹ * (1 + x ^ 2) ^ ((3 : ℝ) / 2) ≤ x⁻¹ * (8 * x ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (inv_nonneg.mpr hx0.le)
    _ = 8 * x ^ 2 := by field_simp

/-- Paper: Proposition 11.2.0.4, p. 486. In ℚ(i), take the two places over 5
and the trivial character. The product (1 − 5⁻ᶻ)² has a double zero at 0.
For degree 3 the permitted jet of order 1 has squared integrand asymptotic
to 1/|x| in the log-norm coordinate, so it has no finite norm. -/
theorem Printed.orbitalJet_norm_annulus_false : ¬ Printed.orbitalJet_norm_annulus := by
  intro h
  classical
  obtain ⟨v, w, hvw⟩ := Printed.orbitalEulerProduct_eq_primary_false_twoPlaces
  obtain ⟨hv, -⟩ := Printed.orbitalEulerProduct_eq_primary_false_trivial v
  obtain ⟨hw, -⟩ := Printed.orbitalEulerProduct_eq_primary_false_trivial w
  have hf0 : frequency((0 : ℝ)) = 0 := by simp
  have hz : reciprocalPartialHeckeEulerProduct (1 : PontryaginDual C𝔽(ℚ)) {v, w}
      (frequency((0 : ℝ))) = 0 := by
    rw [hf0, reciprocalPartialHeckeEulerProduct, Finset.prod_pair hvw,
      Printed.orbitalJet_memLp_false_factor v, zero_mul]
  have hmult : orbitalEulerMultiplicity (1 : PontryaginDual C𝔽(ℚ)) {v, w}
      (frequency((0 : ℝ))) = 2 := by
    rw [orbitalEulerMultiplicity_eq_card, hf0, Finset.filter_true_of_mem fun u _ ↦
      Printed.orbitalJet_memLp_false_factor u, Finset.card_pair hvw]
  obtain ⟨C, -, hC⟩ := h ℚ 1 {v, w} (by simp [hv, hw]) 3 (by norm_num)
  obtain ⟨hmem, -⟩ := hC 0 1 hz (by rw [hmult]; norm_num)
  have hjet : (jet((1 : PontryaginDual C𝔽(ℚ)), 0, 1) : C𝔽(ℚ) → ℂ) =
      fun g ↦ (logNorm(ℚ) g : ℂ) := by
    funext g
    unfold spectralZeroJet
    simp only [pow_one, Complex.ofReal_zero, zero_mul, add_zero]
    change (1 : ℂ) * _ ^ (0 : ℂ) * _ = _
    rw [Complex.cpow_zero, one_mul, one_mul]
  rw [hjet] at hmem
  have hne := hmem.eLpNorm_lt_top
  have hcont : Continuous fun g : C𝔽(ℚ) ↦ (logNorm(ℚ) g : ℂ) :=
    Complex.continuous_ofReal.comp orbitalJet_logNorm_continuous
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hcont.aestronglyMeasurable] at hne
  have hdens : Measurable fun g : C𝔽(ℚ) ↦
      ENNReal.ofReal (intervalSobolevDensity 0 0 3 (logNorm(ℚ) g))⁻¹ :=
    (orbitalJet_density_continuous 3).measurable.ennreal_ofReal
  have htop : ∫⁻ g, ‖(logNorm(ℚ) g : ℂ)‖ₑ ^ ((2 : ENNReal).toReal) ∂(μ'(ℚ, 3)) = ⊤ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hdens
      ((hcont.measurable.eNorm).pow_const _)]
    refine (lintegral_congr fun g ↦ ?_).trans (Printed.orbitalJet_memLp_false_push
      (fun x ↦ ENNReal.ofReal (x ^ 2 * ((1 + x ^ 2) ^ ((3 : ℝ) / 2))⁻¹)) (by fun_prop)
      Printed.orbitalJet_norm_annulus_false_line)
    simp only [Pi.mul_apply, ENNReal.toReal_ofNat, intervalSobolevDensity, mul_zero, zero_mul,
      Real.exp_zero, max_self, one_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)), mul_comm]
  rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hne
  exact lt_irrefl _ hne

/-- Paper: Proposition 11.2.0.4, p. 486. The printed family lies in the annulus
and has an element outside the open ball in the same isotype, with the same C. -/
def Printed.orbitalJets_not_subset_ball : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
      Printed.orbitalJetsIn χ S s {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} ∧
      ¬ Printed.orbitalJetsIn χ S s {u | ‖u‖ < C⁻¹}

/-- Paper: Proposition 11.2.0.4, p. 486. Take ℚ, the trivial character,
S₀ empty, and degree 2. The Euler product is one so the jet set is empty
and is contained in every open ball. -/
theorem Printed.orbitalJets_not_subset_ball_false :
    ¬ Printed.orbitalJets_not_subset_ball := by
  intro h
  obtain ⟨C, _, _, hball⟩ := h ℚ 1 ∅ (by simp) 2 (by norm_num)
  apply hball
  intro t m hz
  simp [reciprocalPartialHeckeEulerProduct] at hz

end RiemannMasullo
