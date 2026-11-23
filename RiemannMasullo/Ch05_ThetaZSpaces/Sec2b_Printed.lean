module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ProdPi
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Chapter 5.2.3–5.2.4: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding theta-space results are in `Sec2b.lean`, and `ERRATA.md` records the errors.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Test(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "GlobalTest(" F ")" => SchwartzBruhat (Multiplicative 𝔸[F])

open Classical in
/-- Paper: Theorem 5.2.3.1, (5.2.3.4), p. 233.
The displayed formula gives one geometric Euler factor per place added to S on insertion into T.
Deviation: We read the two-argument `L_T` as the test-function transform `Z_T` of §5.1 and
record (5.2.3.4) as an identity of transforms for arbitrary tests. The proof invokes it
under source-kernel vanishing on p. 233 and target-kernel vanishing on p. 234. The missing
mass affects the identity but cancels in both kernel arguments. Global extensions
parametrize the indicated local components, and equality is tested at common regular values.
See ERRATA F26 and I96. The mass correction appears in
`weilIdentity_unramifiedOutside_meromorphic`, and
`sLocalHomogeneousThetaTransition_preserves_kernel` gives the kernel implication.
-/
def Printed.sLocalIdelicMellin_transition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (Places(F))) (hST : S ⊆ T)
    (f : Test(F, S)) (c : unramifiedOutside F S)
    (π : (v : Places(F)) → (v.adicCompletion F)ˣ),
    (∀ v ∈ T \ S, (Valued.v :
      Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π v).val) →
    let cS := sIdeleRestriction F S c
    let cT := sIdeleRestriction F T ⟨c.val, fun v hv ↦ c.property v (fun h ↦ hv (hST h))⟩
    0 ≤ sLocalIdelicOrderBound (F := F) (S := S) cS →
    0 ≤ sLocalIdelicOrderBound (F := F) (S := T) cT →
    (∀ v ∈ T \ S, finitePlaceRestriction F v c.val (π v) ≠ 1) →
    sLocalIdelicZFunction (F := F) (S := T) (sAdeleSchwartzTransition F hST f) cT =
      sLocalIdelicZFunction (F := F) (S := S) f cS *
        ∏ v ∈ T \ S, (1 - finitePlaceRestriction F v c.val (π v))⁻¹

/-- A place dividing the different has integer and integer-unit Tamagawa masses
strictly smaller than one. -/
private theorem sLocalIdelicMellin_transition_false_mass_lt_one
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    finiteLocalAdditiveTamagawaMeasure F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < 1 ∧
      finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units < 1 := by
  rw [finiteLocalAdditiveTamagawaMeasure_integers,
    finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
  have hpow : 1 < (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) := by
    apply one_lt_pow₀
    · exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    · exact (multiplicity_pos_of_dvd hv (Ideal.finiteMultiplicity
        (Ideal.IsPrime.ne_top v.isPrime) differentIdeal_ne_bot)).ne'
  have hs : 1 < ENNReal.ofReal (Real.sqrt ((v.asIdeal.absNorm : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) := by
    rw [ENNReal.one_lt_ofReal, Real.lt_sqrt zero_le_one, one_pow]
    exact hpow
  have hi := ENNReal.inv_lt_one.mpr hs
  exact ⟨hi, hi⟩

/-- The third cyclotomic field has degree two, so some finite place divides its
different. This supplies a ramified place without choosing a uniformizer explicitly. -/
private theorem sLocalIdelicMellin_transition_false_ramified_place :
    ∃ v : HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ)),
      v.asIdeal ∣ differentIdeal ℤ (𝓞 (CyclotomicField 3 ℚ)) := by
  let F := CyclotomicField 3 ℚ
  have : IsCyclotomicExtension {3} ℚ F := CyclotomicField.isCyclotomicExtension 3 ℚ
  have hF : 1 < Module.finrank ℚ F := by
    rw [IsCyclotomicExtension.Rat.finrank 3 F]
    decide
  have hdisc := NumberField.abs_discr_gt_two hF
  have hnorm := NumberField.absNorm_differentIdeal F (𝓞 F)
  have htop : differentIdeal ℤ (𝓞 F) ≠ ⊤ := by
    intro ht
    rw [ht, Ideal.absNorm_top] at hnorm
    have : |NumberField.discr F| = 1 := by
      rw [Int.abs_eq_natAbs, ← hnorm]
      rfl
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ htop
  have hbot : M ≠ ⊥ := fun hb ↦ differentIdeal_ne_bot (hb ▸ hle |> le_bot_iff.mp)
  exact ⟨⟨M, hM.isPrime, hbot⟩, Ideal.dvd_iff_le.mpr hle⟩

open Filter Set MeasureTheory in
/-- Norm powers are unramified at every finite place. -/
private theorem sLocalIdelicMellin_transition_false_unramified
    (F : Type) [Field F] [NumberField F] (s : ℂ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s).IsUnramifiedAt v := by
  apply HeckeCharacter.isUnramifiedAt_iff.mpr
  intro u
  let g := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
  have hn : ‖(g : v.adicCompletion F)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show g ∈ (v.adicCompletionIntegers F).units from ⟨u.val.property, u.inv.property⟩))
  change (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s).restrict v
    (g : v.adicCompletion F) = 1
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change (1 : ℂ) * (((ideleClassNorm F
    (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : NNReal) : ℝ) : ℂ) ^ s = 1
  rw [ideleClassNorm_ofAdicCompletion]
  change (1 : ℂ) * (‖(g : v.adicCompletion F)‖ : ℂ) ^ s = 1
  rw [hn, Complex.ofReal_one, Complex.one_cpow, one_mul]

open Filter Set MeasureTheory in
/-- Restricting a global norm power gives the corresponding local norm chart. -/
private theorem sLocalIdelicMellin_transition_false_chart
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ)
    (hc : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s ∈
      unramifiedOutside F S) :
    sIdeleRestriction F S ⟨ideleClassNormTwist 1 s, hc⟩ =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual (SIdeleQuotient F S))) s := by
  ext1 x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [sIdeleRestriction_mk]
  change (1 : ℂ) * _ ^ s = (1 : ℂ) * _ ^ s
  rw [sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
  rfl

open Filter Set MeasureTheory in
/-- A positive norm chart is a regular value of the local Mellin transform. -/
private theorem sLocalIdelicMellin_transition_false_regular
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (s : ℂ) (hs : 0 < s.re) :
    0 ≤ sLocalIdelicOrderBound (F := F) (S := S)
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) s) := by
  let m := sIdeleQuotientNorm F S
  let hm := (isProperMap_sIdeleQuotientNorm F S).continuous
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  let ρ := fun z ↦ sLocalRhoFactor (quasiCharacterNormTwist m hm c z)
  have he (z : ℂ) : quasiCharacterNormTwist m hm
      (quasiCharacterNormTwist m hm c s) z = quasiCharacterNormTwist m hm c (z + s) := by
    ext1 g
    let N : ℂ := (((m g : NNReal) : ℝ) : ℂ)
    change c g * N ^ s * N ^ z = c g * N ^ (z + s)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m g).ne_zero)), mul_assoc]
  change 0 ≤ min 0 (meromorphicOrderAt (fun z ↦
    sLocalRhoFactor (quasiCharacterNormTwist m hm (quasiCharacterNormTwist m hm c s) z)) 0)
  simp only [he]
  change 0 ≤ min 0 (meromorphicOrderAt (fun z ↦ ρ (z + s)) 0)
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add, le_min_iff]
  have ha := sLocalRhoFactor_iteratedDeriv_analyticOn (F := F) (S := S) χ 0 s hs
  rw [iteratedDeriv_zero] at ha
  exact ⟨le_rfl, ha.meromorphicOrderAt_nonneg⟩

open Filter Set MeasureTheory in
/-- Each local Euler factor is nonzero in the half-plane of convergence. -/
private theorem sLocalIdelicMellin_transition_false_euler_ne_zero
    (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (z : ℂ) (hz : 1 < z.re) :
    finiteHeckeEulerFactor χ v z ≠ 0 := by
  classical
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlt : ‖(ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-z)‖ < 1 := by
    rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simp only [Complex.neg_re]; linarith)
  unfold finiteHeckeEulerFactor
  split_ifs
  · exact inv_ne_zero (sub_ne_zero.mpr fun h ↦ (ne_of_lt hlt) (h ▸ norm_one))
  · exact one_ne_zero

open Filter Set MeasureTheory in
/-- Absolute summability of the Euler deviations makes their product nonzero. -/
private theorem sLocalIdelicMellin_transition_false_L_ne_zero
    (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : ℂ) (hs : 1 < s.re) :
    finiteHeckeL χ ⟨s, hs⟩ ≠ 0 := by
  rw [← (finiteHeckeL_hasProd χ ⟨s, hs⟩).tprod_eq]
  have hsum : Summable (fun v ↦ ‖finiteHeckeEulerFactor χ v s - 1‖) :=
    (finiteHeckeEulerFactor_summableUniformlyOn χ {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr hs)).summable (mem_singleton s)
  simpa only [add_sub_cancel] using
    (tprod_one_add_ne_zero_of_summable
      (f := fun v ↦ finiteHeckeEulerFactor χ v s - 1)
      (fun v ↦ by simpa only [add_sub_cancel] using
        sLocalIdelicMellin_transition_false_euler_ne_zero F χ v s hs) hsum)

open Filter Set MeasureTheory in
/-- Removing finitely many Euler factors divides the convergent Hecke Euler product. -/
private theorem sLocalIdelicMellin_transition_false_outside_euler
    (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : ℂ) (hz : 1 < z.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, finiteHeckeEulerFactor χ v.val z) =
      (∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹) * finiteHeckeL χ ⟨z, hz⟩ := by
  classical
  let E (v : HeightOneSpectrum (𝓞 F)) := finiteHeckeEulerFactor χ v z
  let C : Set (HeightOneSpectrum (𝓞 F)) := {v | v ∉ S}
  have hprod := (finiteHeckeL_hasProd χ ⟨z, hz⟩).congr_cofinite₀ (s := S) (g := C.mulIndicator E)
    (fun v _ ↦ sLocalIdelicMellin_transition_false_euler_ne_zero F χ v z hz)
    (fun v hv ↦ (mulIndicator_of_mem hv E).symm)
  have ht : (∏' v : C, E v.val) = _ := (hasProd_subtype_iff_mulIndicator.mpr hprod).tprod_eq
  have hS : ∏ v ∈ S, C.mulIndicator E v = 1 :=
    Finset.prod_eq_one fun v hv ↦ mulIndicator_of_notMem (show v ∉ C from not_not_intro hv) _
  change (∏' v : C, E v.val) = (∏ v ∈ S, (E v)⁻¹) * _
  rw [ht, hS, one_div, Finset.prod_inv_distrib, mul_comm]

open Filter Set MeasureTheory in
/-- A finite-support product separates one factor from its complementary product. -/
private theorem sLocalIdelicMellin_transition_false_finprod_remove
    (ι : Type) (f : ι → ℂ) (hf : Function.HasFiniteMulSupport f) (a : ι) :
    f a * (∏ᶠ x : {x : ι // x ≠ a}, f x.val) = ∏ᶠ x, f x := by
  have h := finprod_mem_inter_mul_sdiff' (f := f) (s := Set.univ) ({a} : Set ι)
    (by simpa only [Set.univ_inter, Function.HasFiniteMulSupport] using hf)
  rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff, finprod_mem_singleton,
    finprod_mem_univ] at h
  simpa only [finprod_subtype_eq_finprod_cond, Set.mem_compl_iff, Set.mem_singleton_iff] using h

open Filter Set MeasureTheory in
/-- Each local integer-unit mass is a nonzero finite real number. -/
private theorem sLocalIdelicMellin_transition_false_mass_ne_zero
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (((finiteLocalMultiplicativeTamagawaMeasure F v)
      (v.adicCompletionIntegers F).units).toReal : ℂ) ≠ 0 := by
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hs : 0 < Real.sqrt ((v.asIdeal.absNorm : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) := Real.sqrt_pos.mpr (pow_pos hq _)
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le]
  exact_mod_cast inv_ne_zero hs.ne'

open Filter Set MeasureTheory in
/-- The two global Weil identities expose the missing local integer-unit mass. -/
private theorem sLocalIdelicMellin_transition_false_contra
    (F : Type) [Field F] [NumberField F] (v₀ : HeightOneSpectrum (𝓞 F))
    (hv₀ : (finiteLocalMultiplicativeTamagawaMeasure F v₀)
      (v₀.adicCompletionIntegers F).units < 1)
    (h : Printed.sLocalIdelicMellin_transition) : False := by
  classical
  let V := HeightOneSpectrum (𝓞 F)
  let χ : PontryaginDual (IdeleClassGroup (𝓞 F) F) := 1
  let c := ideleClassNormTwist χ 2
  let S : Finset V := ∅
  let T : Finset V := {v₀}
  have hST : S ⊆ T := Finset.empty_subset _
  have hu (R : Finset V) : c ∈ unramifiedOutside F R := fun v _ ↦
    sLocalIdelicMellin_transition_false_unramified F 2 v
  let cR (R : Finset V) := sIdeleRestriction F R ⟨c, hu R⟩
  have hcR (R : Finset V) : cR R =
      quasiCharacterNormTwist (sIdeleQuotientNorm F R)
        (isProperMap_sIdeleQuotientNorm F R).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual (SIdeleQuotient F R))) 2 :=
    sLocalIdelicMellin_transition_false_chart F R 2 (hu R)
  have hpos (R : Finset V) : ∃ (η : PontryaginDual (SIdeleQuotient F R)) (s : ℂ),
      0 < s.re ∧ cR R =
        quasiCharacterNormTwist (sIdeleQuotientNorm F R)
          (isProperMap_sIdeleQuotientNorm F R).continuous
          ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) s :=
    ⟨1, 2, by norm_num, hcR R⟩
  have hreg (R : Finset V) : 0 ≤ sLocalIdelicOrderBound (F := F) (S := R) (cR R) := by
    rw [hcR]
    exact sLocalIdelicMellin_transition_false_regular F R 1 2 (by norm_num)
  obtain ⟨f, -, hf⟩ := sLocal_exists_real_test (F := F) (S := S) (cR S) (hpos S)
  let fT := sAdeleSchwartzTransition F hST f
  let ZS := sLocalIdelicZetaIntegral f (cR S)
  let ZT := sLocalIdelicZetaIntegral fT (cR T)
  let E (v : V) := finiteHeckeEulerFactor χ v 2
  let L := finiteHeckeL χ ⟨2, by norm_num⟩
  have hE (v : V) : E v ≠ 0 :=
    sLocalIdelicMellin_transition_false_euler_ne_zero F χ v 2 (by norm_num)
  have hL : L ≠ 0 := sLocalIdelicMellin_transition_false_L_ne_zero F χ 2 (by norm_num)
  let π (v : V) : (v.adicCompletion F)ˣ :=
    let q : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    Units.mk0 (q.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
      q.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hπ (v : V) : (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).IsUniformizer (π v).val :=
    Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
  have hEuler (v : V) : (E v)⁻¹ = 1 - finitePlaceRestriction F v c (π v) :=
    finiteHeckeEulerFactor_inv_uniformizer χ v (π v) (hπ v)
      (sLocalIdelicMellin_transition_false_unramified F 0 v) (by norm_num)
  have hchar (v : V) : finitePlaceRestriction F v c (π v) ≠ 1 := by
    intro he
    have := hEuler v
    rw [he, sub_self, inv_eq_zero] at this
    exact hE v this
  have hp := h F S T hST f ⟨c, hu S⟩ π (fun v _ ↦ hπ v)
    (hreg S) (hreg T) (fun v _ ↦ hchar v)
  change sLocalIdelicZFunction fT (cR T) = sLocalIdelicZFunction f (cR S) * _ at hp
  rw [sLocalIdelicZFunction_eq_integral fT (hpos T),
    sLocalIdelicZFunction_eq_integral f (hpos S)] at hp
  have hp' : ZT = ZS * E v₀ := by
    simpa only [S, T, Finset.sdiff_empty, Finset.prod_singleton, ← hEuler, inv_inv] using hp
  let M (v : V) : ℂ := (((finiteLocalMultiplicativeTamagawaMeasure F v)
    (v.adicCompletionIntegers F).units).toReal : ℂ)
  let A (R : Finset V) : ℂ := ∏ᶠ v : {v : V // v ∉ R}, M v.val
  have hWeilS := weilIdentity_unramifiedOutside (F := F) S f χ 2 (by norm_num) (hu S)
  have hWeilT := weilIdentity_unramifiedOutside (F := F) T fT χ 2 (by norm_num) (hu T)
  have hglobal : sAdeleSchwartzToGlobal F T fT = sAdeleSchwartzToGlobal F S f :=
    LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hST) f
  rw [hglobal] at hWeilT
  rw [sLocalIdelicMellin_transition_false_outside_euler F χ S 2 (by norm_num)] at hWeilS
  rw [sLocalIdelicMellin_transition_false_outside_euler F χ T 2 (by norm_num)] at hWeilT
  have hWeil : A S * ZS * L = A T * ZT * ((E v₀)⁻¹ * L) := by
    simpa only [S, T, Finset.prod_empty, one_mul, Finset.prod_singleton]
      using hWeilS.symm.trans hWeilT
  rw [hp'] at hWeil
  have hA : A S = A T := by
    apply mul_right_cancel₀ (mul_ne_zero hf hL)
    calc
      A S * (ZS * L) = A T * (ZS * E v₀) * ((E v₀)⁻¹ * L) := by
        simpa only [mul_assoc] using hWeil
      _ = A T * (ZS * L) := by field_simp [hE v₀]
  have hm : ∀ᶠ v : V in cofinite,
      (finiteLocalMultiplicativeTamagawaMeasure F v) (v.adicCompletionIntegers F).units = 1 := by
    simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite]
      using finiteLocalTamagawaMass_finite F
  have hfin : Function.HasFiniteMulSupport M :=
    eventually_cofinite.mp (hm.mono fun v hv ↦ by simp only [M, hv, ENNReal.toReal_one, Complex.ofReal_one])
  have hsplit : M v₀ * A T = A S := by
    simpa only [A, S, T, finprod_subtype_eq_finprod_cond, Finset.mem_singleton,
      Finset.notMem_empty, not_false_eq_true, finprod_true]
      using sLocalIdelicMellin_transition_false_finprod_remove V M hfin v₀
  have hAT : A T ≠ 0 := finprod_ne_zero fun v ↦
    sLocalIdelicMellin_transition_false_mass_ne_zero F v.val
  have hMv : M v₀ = 1 := mul_right_cancel₀ hAT (by rw [hsplit, hA, one_mul])
  have hreal : ((finiteLocalMultiplicativeTamagawaMeasure F v₀)
      (v₀.adicCompletionIntegers F).units).toReal = 1 := by
    simpa only [M, Complex.ofReal_re, Complex.one_re] using congrArg Complex.re hMv
  have hmass := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_toReal (hv₀.trans ENNReal.one_lt_top).ne, ENNReal.ofReal_one] at hmass
  exact hv₀.ne hmass

/-- Paper: Theorem 5.2.3.1, (5.2.3.4), p. 233.
For F = ℚ(ζ₃), take the archimedean stage and add a finite place dividing the different.
At the square of the idelic norm, choose an archimedean test with nonzero zeta integral.
Comparing the two Weil identities for its common global insertion shows that the printed
transition formula would force the added place's integer-unit Tamagawa mass to be one.
That mass is strictly smaller than one at a place dividing the different.
-/
theorem Printed.sLocalIdelicMellin_transition_false :
    ¬ Printed.sLocalIdelicMellin_transition := by
  intro h
  obtain ⟨v, hv⟩ := sLocalIdelicMellin_transition_false_ramified_place
  exact sLocalIdelicMellin_transition_false_contra (CyclotomicField 3 ℚ) v
    (sLocalIdelicMellin_transition_false_mass_lt_one (CyclotomicField 3 ℚ) v hv).2 h

/-- Paper: Introduction to Proposition 5.2.3.2, (5.2.3.9), pp. 235–236.
As printed: for every number field, every finite stage containing the archimedean places,
and every character of the respective norm-one group, the global and S-local Pettis averages
are projectors. This records the idempotence asserted by the word “projectors.”
The averages and their quotient identifications are given by
`existsUnique_globalThetaIsotypicAverage`, `existsUnique_sLocalThetaIsotypicAverage`,
`globalThetaIsotypicAverage_equiv` and `sLocalThetaIsotypicAverage_equiv`.
`compactActionAverage_idempotent` gives idempotence after normalization. See ERRATA F27.
-/
def Printed.thetaIsotypicAverage_idempotent : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    (∀ ω : PontryaginDual (ideleClassNorm F).ker,
      let P := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
      P.comp P = P) ∧
    (∀ χ : PontryaginDual (sIdeleQuotientNorm F S).ker,
      let P := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose
      P.comp P = P)

open Filter Set MeasureTheory in
/-- The norm-one idele classes of ℚ(ζ₃) have Tamagawa mass π/(3√3) < 1. -/
private theorem thetaIsotypicAverage_idempotent_false_volume_lt_one :
    normOneIdeleClassTamagawaMeasure (CyclotomicField 3 ℚ) Set.univ < 1 := by
  rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.ofReal_lt_one]
  have : IsCyclotomicExtension {(3:ℕ)} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hh : NumberField.classNumber (CyclotomicField 3 ℚ) = 1 :=
    classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid _)
  have ht : Units.torsionOrder (CyclotomicField 3 ℚ) = 6 := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3)]; decide
  have hd : NumberField.discr (CyclotomicField 3 ℚ) = -3 := by
    rw [IsCyclotomicExtension.Rat.discr_prime 3 (CyclotomicField 3 ℚ)]
    norm_num
  have h1 : InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) _ (by norm_num)
  have h2 : InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3]; decide
  have hR : Units.regulator (CyclotomicField 3 ℚ) = 1 := by
    have hc : Fintype.card (InfinitePlace (CyclotomicField 3 ℚ)) = 1 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h1, h2]
    have hall : ∀ a b : InfinitePlace (CyclotomicField 3 ℚ), a = b :=
      Fintype.card_le_one_iff.mp hc.le
    classical
    rw [Units.regulator_eq_det', Matrix.det_eq_one_of_card_eq_zero
      (Fintype.card_eq_zero_iff.mpr ⟨fun w ↦ w.2 (hall _ _)⟩), abs_one]
  rw [hh, ht, hd, h1, h2, hR]
  have hs : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  rw [div_lt_one (by positivity)]
  norm_num
  nlinarith

open Filter Set MeasureTheory in
/-- The squared-norm Mellin evaluation is nonzero on a normalized Hecke test. -/
private theorem thetaIsotypicAverage_idempotent_false_nonzero
    (F : Type) [Field F] [NumberField F]
    (hc : 0 ≤ globalIdelicOrderBound
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2)) :
    ∃ x : GlobalAdelicThetaSpace F,
      (globalThetaMellin (F := F) x).val
        ⟨ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2, hc⟩ ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL
    (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  let s : Complex.re ⁻¹' Set.Ioi (1 : ℝ) := ⟨2, by norm_num⟩
  refine ⟨Submodule.Quotient.mk f, ?_⟩
  rw [globalThetaMellin_mk, globalIdelicMellin_apply,
    globalIdelicZFunction_eq_integral f
      (globalTwist_mem_rightHalf (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (by norm_num))]
  rw [show globalIdelicZetaIntegral f
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2) =
      completedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s from hf s]
  exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos _ (by norm_num [s]))
    (sLocalIdelicMellin_transition_false_L_ne_zero F _ s s.property)

open Filter Set MeasureTheory in
/-- A nonzero eigenfunctional forbids idempotence when its eigenvalue is neither zero nor one. -/
private theorem thetaIsotypicAverage_idempotent_false_scalar
    (E : Type) (P : E → E) (φ : E → ℂ) (M : ℂ)
    (hM0 : M ≠ 0) (hM1 : M ≠ 1) (hφ : ∀ x, φ (P x) = M * φ x)
    (x : E) (hx : φ x ≠ 0) (hP : ∀ y, P (P y) = P y) : False := by
  have he := congrArg φ (hP x)
  simp only [hφ] at he
  have hMM : M * M = M := mul_right_cancel₀ hx (by simpa only [mul_assoc] using he)
  exact hM1 (mul_right_cancel₀ hM0 (hMM.trans (one_mul M).symm))

open Filter Set MeasureTheory in
/-- A field whose norm-one Tamagawa mass is strictly less than one disproves raw idempotence. -/
private theorem thetaIsotypicAverage_idempotent_false_of_volume_lt_one
    (F : Type) [Field F] [NumberField F]
    (hvol : normOneIdeleClassTamagawaMeasure F Set.univ < 1)
    (hprinted : Printed.thetaIsotypicAverage_idempotent) : False := by
  classical
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let μ := normOneIdeleClassTamagawaMeasure F
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : MeasureTheory.IsFiniteMeasure μ := ⟨hvol.trans (by simp)⟩
  let P := (existsUnique_globalThetaIsotypicAverage (F := F)
    (1 : PontryaginDual (ideleClassNorm F).ker)).exists.choose
  have hc : 0 ≤ globalIdelicOrderBound
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2) := by
    rw [globalIdelicOrderBound_one_and_normSquared.2]
  let c := (⟨ideleClassNormTwist
    (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2, hc⟩ :
      {c : QuasiCharacter (IdeleClassGroup (𝓞 F) F) // 0 ≤ globalIdelicOrderBound c})
  let φ : GlobalAdelicThetaSpace F → ℂ := fun x ↦ (globalThetaMellin (F := F) x).val c
  have hφ (x : GlobalAdelicThetaSpace F) :
      φ (P x) = (μ.real Set.univ : ℂ) * φ x := by
    apply globalThetaMellin_isotypicAverage (F := F) 1 x c
    intro g
    change (1 : ℂ) * (((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ (2 : ℂ) = 1
    rw [MonoidHom.mem_ker.mp g.property, Units.val_one, NNReal.coe_one,
      Complex.ofReal_one, Complex.one_cpow, one_mul]
  obtain ⟨x, hx⟩ := thetaIsotypicAverage_idempotent_false_nonzero F hc
  have hM0 : (μ.real Set.univ : ℂ) ≠ 0 := by
    exact_mod_cast (MeasureTheory.measureReal_univ_pos (μ := μ)).ne'
  have hMlt : μ.real Set.univ < 1 := by
    change (μ Set.univ).toReal < 1
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ne_of_lt (hvol.trans (by simp))) ENNReal.one_ne_top).mpr hvol
  have hM1 : (μ.real Set.univ : ℂ) ≠ 1 := by exact_mod_cast hMlt.ne
  apply thetaIsotypicAverage_idempotent_false_scalar _ P φ _ hM0 hM1 hφ x hx
  intro y
  exact congrArg (fun A : GlobalAdelicThetaSpace F →L[ℂ] GlobalAdelicThetaSpace F ↦ A y)
    ((hprinted F ∅).1 (1 : PontryaginDual (ideleClassNorm F).ker))

/-- Paper: Introduction to Proposition 5.2.3.2, (5.2.3.9), pp. 235–236.
For F = ℚ(ζ₃), the norm-one idele classes have Tamagawa mass M = π/(3√3), with 0 < M < 1.
Mellin evaluation at the squared norm is nonzero on a normalized Hecke test and is
multiplied by M under the global trivial-character average. Idempotence of that average
would therefore imply M² = M, a contradiction.
-/
theorem Printed.thetaIsotypicAverage_idempotent_false :
    ¬ Printed.thetaIsotypicAverage_idempotent := by
  intro hprinted
  exact thetaIsotypicAverage_idempotent_false_of_volume_lt_one (CyclotomicField 3 ℚ)
    thetaIsotypicAverage_idempotent_false_volume_lt_one hprinted

/-- Paper: Remark 5.2.3.4(1)–(2), p. 237.
As printed: for every number field and finite stage containing the archimedean places,
the topologies on global and S-local test functions induced by the theta maps are Hausdorff.
This records the Hausdorff assertions in the two closure statements.
`globalThetaKernel_eq_induced_closure` and `sLocalThetaKernel_eq_induced_closure`
give the closure identities with the indicated pullback topologies. See ERRATA F28.
-/
def Printed.thetaInducedTopology_t2 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let q := (LinearMap.ker (adelicThetaLinearMap F)).mkQ
    let qS := (LinearMap.ker (sLocalAdelicTheta F S)).mkQ
    @T2Space (GlobalTest(F)) (TopologicalSpace.induced q inferInstance) ∧
    @T2Space (Test(F, S)) (TopologicalSpace.induced qS inferInstance)

/-- In the topology induced by a map, a Hausdorff space identifies points with equal images. -/
private theorem thetaInducedTopology_t2_false_eq {X Y : Type*} [t : TopologicalSpace Y]
    (q : X → Y) (h : @T2Space X (TopologicalSpace.induced q t)) {a b : X} (hab : q a = q b) :
    a = b := by
  let : TopologicalSpace X := TopologicalSpace.induced q t
  exact Inseparable.eq (show nhds a = nhds b by rw [nhds_induced, nhds_induced, hab])

open scoped RestrictedProduct in
/-- The rational adeles are a nontrivial Hausdorff locally compact group. -/
private theorem thetaInducedTopology_t2_false_adeles :
    Nontrivial 𝔸[ℚ] ∧ T2Space (Multiplicative 𝔸[ℚ]) ∧
      LocallyCompactSpace (Multiplicative 𝔸[ℚ]) := by
  let (v : Places(ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Places(ℚ), IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  refine ⟨?_, ?_, ?_⟩
  · change Nontrivial (InfiniteAdeleRing ℚ ×
      (Πʳ v : Places(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  · change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : Places(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  · change LocallyCompactSpace (InfiniteAdeleRing ℚ ×
      (Πʳ v : Places(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance

/-- The global theta function of a test does not change under pullback by negation:
the principal multiples are reindexed by `ξ ↦ -ξ`. -/
private theorem thetaInducedTopology_t2_false_neg (f : GlobalTest(ℚ)) :
    adelicTheta (schwartzBruhatUnitTranslate (-1) f) = adelicTheta f := by
  ext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [adelicTheta_mk, adelicTheta_mk]
  refine (tsum_congr fun ξ ↦ ?_).trans ((Equiv.neg ℚˣ).tsum_eq
    (fun ξ : ℚˣ ↦ f (Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (ξ : ℚ) * g.val))))
  rw [schwartzBruhatUnitTranslate_apply]
  simp [Units.val_neg, map_neg]

/-- Paper: Remark 5.2.3.4(1)–(2), p. 237.
For F = ℚ use the odd real test x ↦ x exp(−πx²), at S consisting of the real place
and globally tensored with the indicator of the finite integer adeles. Each test is nonzero,
and the terms at opposite nonzero rational elements cancel at every global idele.
The real-stage sum pairs the terms at the two units ±1. Each theta map sends its test
and zero to the same point, so the pullback topology cannot separate them.
-/
theorem Printed.thetaInducedTopology_t2_false : ¬ Printed.thetaInducedTopology_t2 := by
  classical
  intro h
  have hG := (h ℚ ∅).1
  obtain ⟨_, _, _⟩ := thetaInducedTopology_t2_false_adeles
  let x : Multiplicative 𝔸[ℚ] := Multiplicative.ofAdd 1
  let y : Multiplicative 𝔸[ℚ] := Multiplicative.ofAdd (-1)
  have hxy : x ≠ y := by
    intro hxy
    have h1 : (1 : 𝔸[ℚ]) = -1 := congrArg Multiplicative.toAdd hxy
    have h2 : algebraMap ℚ 𝔸[ℚ] 1 = algebraMap ℚ 𝔸[ℚ] (-1) := by simpa using h1
    have := (algebraMap ℚ 𝔸[ℚ]).injective h2
    norm_num at this
  obtain ⟨δ, hδ, hvan, -⟩ := schwartzBruhat_dirac_support x
  have hex : ∃ f : GlobalTest(ℚ), tsupport (f : Multiplicative 𝔸[ℚ] → ℂ) ⊆ {y}ᶜ ∧ f x ≠ 0 := by
    by_contra! hc
    have hmem : x ∈ schwartzBruhatVanishingLocus δ :=
      ⟨{y}ᶜ, ⟨isOpen_compl_singleton, fun f hf ↦ (hδ f).trans (hc f hf)⟩, hxy⟩
    rw [hvan] at hmem
    exact hmem rfl
  obtain ⟨f, hfs, hfx⟩ := hex
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun hy ↦ hfs hy rfl)
  let d : GlobalTest(ℚ) := f - schwartzBruhatUnitTranslate (-1) f
  have hdx : d x = f x := by
    have e : schwartzBruhatUnitTranslate (-1) f x = f y := by
      change schwartzBruhatUnitTranslate (-1) f (Multiplicative.ofAdd 1) = _
      rw [schwartzBruhatUnitTranslate_apply]
      simp [y]
    change f x - schwartzBruhatUnitTranslate (-1) f x = f x
    rw [e, hfy, sub_zero]
  have hd0 : d ≠ 0 := by
    intro hd
    apply hfx
    rw [← hdx, hd]
    rfl
  have hker : d ∈ LinearMap.ker (adelicThetaLinearMap ℚ) := by
    rw [LinearMap.mem_ker, map_sub, adelicThetaLinearMap_apply, adelicThetaLinearMap_apply,
      thetaInducedTopology_t2_false_neg, sub_self]
  have hq : (LinearMap.ker (adelicThetaLinearMap ℚ)).mkQ d =
      (LinearMap.ker (adelicThetaLinearMap ℚ)).mkQ 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).2 hker
  exact hd0 (thetaInducedTopology_t2_false_eq _ hG hq)

/-- Paper: §5.2.4, introduction to Theorem 5.2.4.1, p. 238.
The introduction says that the local Fourier maps tend to “the inversion automorphism”
on the global theta space. We record the existence of the named target automorphism.
Deviation: We read inversion as pullback of theta functions by `g ↦ g⁻¹` on idele classes.
`existsUnique_globalThetaFourier` gives the Fourier automorphism, whose action on theta values
is governed by `adelicTheta_riemannRoch`. See ERRATA F29.
-/
def Printed.globalTheta_inversionAutomorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    let K := LinearMap.ker (adelicThetaLinearMap F)
    let theta := K.liftQ (adelicThetaLinearMap F) le_rfl
    ∃ J : GlobalAdelicThetaSpace F ≃L[ℂ] GlobalAdelicThetaSpace F,
      ∀ (f : GlobalTest(F)) (g : IdeleClassGroup (𝓞 F) F),
        theta (J (K.mkQ f)) g = adelicTheta f g⁻¹

/-- Paper: §5.2.4, introduction to Theorem 5.2.4.1, p. 238.
Take F = ℚ and the self-dual test exp(−πx²) times the indicator of the finite integer adeles.
On the idele with real component t > 0 and finite components 1, its inverted theta value
is asymptotic to t as t tends to infinity. Every global theta function decays there by
`adelicTheta_decay_large`, so the inverted function cannot represent a global theta class.
-/
theorem Printed.globalTheta_inversionAutomorphism_false :
    ¬ Printed.globalTheta_inversionAutomorphism := by
  classical
  intro h
  obtain ⟨f, hf⟩ := (adelePolarValues_surjective (F := ℚ)) (0, 1)
  have hf0 : f (Multiplicative.ofAdd (0 : 𝔸[ℚ])) = 0 := congrArg Prod.fst hf
  have hf1 : adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[ℚ])) = 1 := congrArg Prod.snd hf
  obtain ⟨J, hJ⟩ := h ℚ
  let K := LinearMap.ker (adelicThetaLinearMap ℚ)
  obtain ⟨d, hd⟩ := Submodule.mkQ_surjective K (J (K.mkQ f))
  have heq (g : IdeleClassGroup (𝓞 ℚ) ℚ) : adelicTheta d g = adelicTheta f g⁻¹ := by
    have hh := hJ f g
    change (K.liftQ (adelicThetaLinearMap ℚ) le_rfl) (J (K.mkQ f)) g = _ at hh
    have hd' := congrArg (fun x => (K.liftQ (adelicThetaLinearMap ℚ) le_rfl) x g) hd
    exact hd'.trans hh
  obtain ⟨C, T, hC, hT, hsmall⟩ := adelicTheta_decay_small f 0
  obtain ⟨D, U, hD, hU, hlarge⟩ := adelicTheta_decay_large d 0
  let r : ℝ := max (max (C + D + 1) U) (T⁻¹) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrU : U < r := by
    dsimp [r]
    linarith [le_max_right (C + D + 1) U, le_max_left (max (C + D + 1) U) T⁻¹]
  have hrT : T⁻¹ < r := by
    dsimp [r]
    linarith [le_max_right (max (C + D + 1) U) T⁻¹]
  have hrCD : C + D < r := by
    dsimp [r]
    linarith [le_max_left (C + D + 1) U, le_max_left (max (C + D + 1) U) T⁻¹]
  let t : Units NNReal := Units.mk0 (⟨r, hr.le⟩ : NNReal)
    (by intro h; exact hr.ne' (congrArg NNReal.toReal h))
  let g : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hn : ((ideleClassNorm ℚ g : NNReal) : ℝ) = r := by
    change ((ideleNorm ℚ (canonicalIdeleNormSection ℚ t) : NNReal) : ℝ) = r
    rw [canonicalIdeleNormSection_rightInverse]
    rfl
  have hni : ((ideleClassNorm ℚ g⁻¹ : NNReal) : ℝ) = r⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, hn]
  have hsm : ((ideleClassNorm ℚ g⁻¹ : NNReal) : ℝ) < T := by
    rw [hni]
    exact (inv_lt_comm₀ hr hT).2 hrT
  have hs := hsmall g⁻¹ hsm
  have hl := hlarge g (by change U < ((ideleClassNorm ℚ g : NNReal) : ℝ); rw [hn]; exact hrU)
  dsimp only at hs
  rw [hni, inv_inv, hf0, hf1] at hs
  simp only [Complex.real_smul, mul_one, add_zero, pow_zero] at hs
  simp only [pow_zero, inv_one, mul_one] at hl
  rw [heq] at hl
  have hb : r ≤ ‖adelicTheta f g⁻¹‖ + C := by
    have hh := norm_le_norm_add_norm_sub (adelicTheta f g⁻¹) (r : ℂ)
    simp only [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  linarith

/-- Paper: Theorem 5.2.4.1(1)–(2), (5.2.4.2) and (5.2.4.4), p. 239.
As printed: for every number field and every pair of nested finite stages containing the
archimedean places, Fourier on the theta quotients commutes with stage enlargement and
with insertion into the global theta quotient. This records the two insertion assertions.
See ERRATA F30. The repaired statements are `sLocalThetaFourier_transition` and
`sLocalThetaFourier_toGlobal`, with restrictions at places dividing the different.
-/
def Printed.thetaFourier_insertion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    (∀ (T : Finset (Places(F))) (hST : S ⊆ T) (x : SLocalAdelicThetaSpace F S),
      let fourierT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
      let transition := sLocalThetaTransition (F := F) hST
      fourierT (transition x) = transition (fourierS x)) ∧
    (∀ x : SLocalAdelicThetaSpace F S,
      fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x))

open Filter Set MeasureTheory Classical in
/-- Equal global theta classes have the same value at the additive origin, as read
from the residue at the trivial quasi-character. -/
private theorem thetaFourier_insertion_false_global_zero
    (F : Type) [Field F] [NumberField F]
    (f g : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hfg : (Submodule.Quotient.mk f : GlobalAdelicThetaSpace F) =
      Submodule.Quotient.mk g) :
    f (Multiplicative.ofAdd (0 : 𝔸[F])) = g (Multiplicative.ofAdd (0 : 𝔸[F])) := by
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  have hθ := (globalAdelicThetaSpace_mk_eq_iff f g).mp hfg
  have hZ (s : ℂ) :
      globalIdelicZFunction f (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s) =
        globalIdelicZFunction g (ideleClassNormTwist 1 s) := by
    refine congrFun (eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic f 1)
      (globalIdelicZFunction_meromorphic g 1) 1 fun z hz ↦ ?_) s
    have hr := globalTwist_mem_rightHalf (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) hz
    rw [globalIdelicZFunction_eq_integral f hr, globalIdelicZFunction_eq_integral g hr,
      ← globalThetaMellinIntegral_eq_idelic f hr, ← globalThetaMellinIntegral_eq_idelic g hr]
    simp only [globalThetaMellinIntegral, hθ]
  have hf := globalIdelicZFunction_residue_zero f
  have hg := globalIdelicZFunction_residue_zero g
  have hlim := tendsto_nhds_unique hf (hg.congr' (Filter.Eventually.of_forall
    (fun s : ℂ ↦ congrArg (s * ·) (hZ s).symm)))
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : (normOneIdeleClassTamagawaMeasure F univ).toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨isOpen_univ.measure_ne_zero _ univ_nonempty, measure_ne_top _ _⟩
  exact mul_left_cancel₀ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hm)) hlim

open Filter Set MeasureTheory Classical in
/-- Global integer-ring insertion preserves evaluation at zero. -/
private theorem thetaFourier_insertion_false_toGlobal_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (0 : 𝔸[F])) =
      f (Multiplicative.ofAdd (0 : SAdeleRing F S)) := by
  rw [sAdeleSchwartzToGlobal_apply]
  have hmem : ∀ w ∉ S, (0 : 𝔸[F]).2 w ∈ w.adicCompletionIntegers F := by
    intro w _
    change (0 : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    exact (w.adicCompletionIntegers F).zero_mem
  rw [ite_eq_left hmem, map_zero]

open Filter Set MeasureTheory Classical in
/-- Equal local theta classes have the same value at the additive origin. -/
private theorem thetaFourier_insertion_false_local_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f g : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hfg : (Submodule.Quotient.mk f : SLocalAdelicThetaSpace F S) =
      Submodule.Quotient.mk g) :
    f (Multiplicative.ofAdd (0 : SAdeleRing F S)) =
      g (Multiplicative.ofAdd (0 : SAdeleRing F S)) := by
  have hh := congrArg (sLocalThetaToGlobal F S) hfg
  rw [sLocalThetaToGlobal_mk, sLocalThetaToGlobal_mk] at hh
  have hz := thetaFourier_insertion_false_global_zero F _ _ hh
  simpa only [thetaFourier_insertion_false_toGlobal_zero] using hz

open Filter Set MeasureTheory Classical in
/-- At every finite stage one can prescribe Fourier evaluation at zero to be one. -/
private theorem thetaFourier_insertion_false_test
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      sAdeleSchwartzFourier f (Multiplicative.ofAdd (0 : SAdeleRing F S)) = 1 := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let G := Multiplicative (SAdeleRing F S)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (SAdeleRing F S))
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  obtain ⟨u, -, -, hu⟩ := schwartzBruhat_exists_local_unit
    (G := G) isOpen_univ (mem_univ (Multiplicative.ofAdd (0 : SAdeleRing F S)))
  refine ⟨sAdeleSchwartzFourier u, ?_⟩
  rw [sLocal_fourier_inversion]
  simpa only [neg_zero, Pi.one_apply] using hu.eq_of_nhds

open Filter Set MeasureTheory Classical in
/-- Integer-ring insertion scales Fourier evaluation at zero by the product of
additive Tamagawa masses of the inserted integer rings. -/
private theorem thetaFourier_insertion_false_transition
    (F : Type) [Field F] [NumberField F]
    (S D : Finset (HeightOneSpectrum (𝓞 F))) (hSD : Disjoint S D)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sAdeleSchwartzFourier
        (sAdeleSchwartzTransition F (Finset.subset_union_left (s₁ := S) (s₂ := D)) f)
        (Multiplicative.ofAdd (0 : SAdeleRing F (S ∪ D))) =
      (∏ v : D, (((finiteLocalAdditiveTamagawaMeasure F v.val)
        (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))).toReal : ℂ)) *
        sAdeleSchwartzFourier f (Multiplicative.ofAdd (0 : SAdeleRing F S)) := by
  classical
  let hST : S ⊆ S ∪ D := Finset.subset_union_left
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let μ := finiteLocalAdditiveTamagawaMeasure F
  let (v : HeightOneSpectrum (𝓞 F)) : (μ v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let b (v : D) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))
  have hbi (v : D) : (∫ x, b v x ∂μ v) =
      (((μ v) (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))).toReal : ℂ) := by
    have ho : IsOpen (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)) :=
      Valued.isOpen_valuationSubring _
    rw [show b v = (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
      (fun _ ↦ (1 : ℂ)) from rfl, integral_indicator_const _ ho.measurableSet,
      Complex.real_smul, mul_one]
    rfl
  have hprod := Finset.prod_congr (rfl : (Finset.univ : Finset D) = Finset.univ)
    (fun v _ ↦ hbi v)
  rw [sAdeleSchwartzFourier_apply_zero, sAdeleSchwartzFourier_apply_zero, ← hprod, mul_comm]
  let (w : InfinitePlace F) : SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) := by
    rw [infiniteLocalAdditiveTamagawaMeasure]
    split_ifs with hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
    · rw [two_nsmul]
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
  apply integral_prod_piFinsetUnion (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)) μ hSD
    (fun z ↦ f (Multiplicative.ofAdd z)) b
  intro a x y
  rw [sAdeleSchwartzTransition_apply]
  let X (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
  let t := MeasurableEquiv.piFinsetUnion X hSD (x, y)
  have hmem : (∀ w : ↥(S ∪ D), w.val ∉ S → t w ∈ w.val.adicCompletionIntegers F) ↔
      ∀ v : D, y v ∈ v.val.adicCompletionIntegers F := by
    constructor
    · intro h v
      have hv := h ⟨v.val, Finset.mem_union_right S v.property⟩
        (fun hs ↦ Finset.disjoint_left.mp hSD hs v.property)
      simpa only [t, MeasurableEquiv.piFinsetUnion_right X hSD v.property] using hv
    · intro h w hw
      have hv := (Finset.mem_union.mp w.property).resolve_left hw
      simpa only [t, MeasurableEquiv.piFinsetUnion_right X hSD hv] using! h ⟨w.val, hv⟩
  change (if _ then f (Multiplicative.ofAdd (a, fun v : S ↦ t ⟨v.val, hST v.property⟩)) else 0) = _
  have hx : (fun v : S ↦ t ⟨v.val, hST v.property⟩) = x :=
    funext fun v ↦ MeasurableEquiv.piFinsetUnion_left X hSD v.property _
  simp only [b, indicator_apply, Fintype.prod_boole, mul_ite, mul_one, mul_zero]
  exact if_congr hmem (congrArg (fun u ↦ f (Multiplicative.ofAdd (a, u))) hx) rfl

open Filter Set MeasureTheory Classical in
/-- Integer-ring insertion also preserves the original test value at zero. -/
private theorem thetaFourier_insertion_false_transition_zero
    (F : Type) [Field F] [NumberField F]
    (S T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sAdeleSchwartzTransition F hST f (Multiplicative.ofAdd (0 : SAdeleRing F T)) =
      f (Multiplicative.ofAdd (0 : SAdeleRing F S)) := by
  rw [sAdeleSchwartzTransition_apply]
  have hmem : ∀ w : T, w.val ∉ S →
      (0 : SAdeleRing F T).2 w ∈ w.val.adicCompletionIntegers F := by
    intro w _
    change (0 : w.val.adicCompletion F) ∈ w.val.adicCompletionIntegers F
    exact (w.val.adicCompletionIntegers F).zero_mem
  rw [ite_eq_left hmem]
  rfl

/-- Paper: Theorem 5.2.4.1(1)–(2), (5.2.4.2) and (5.2.4.4), p. 239.
For F = ℚ(ζ₃), take the archimedean stage and add a finite place dividing the different.
Choose a test whose Fourier value at zero is one. Fourier after integer-ring insertion
has value at zero equal to the added integer ring's Tamagawa mass, which is less than one;
insertion after Fourier has value one. Equal theta classes have equal values at zero,
as follows from the global zeta residue at the trivial character. Thus the two classes differ.
-/
theorem Printed.thetaFourier_insertion_false : ¬ Printed.thetaFourier_insertion := by
  classical
  intro h
  let F := CyclotomicField 3 ℚ
  obtain ⟨v, hv⟩ := sLocalIdelicMellin_transition_false_ramified_place
  have hm := (sLocalIdelicMellin_transition_false_mass_lt_one F v hv).1
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ {v}
  have hST : S ⊆ T := Finset.subset_union_left
  obtain ⟨f, hf⟩ := thetaFourier_insertion_false_test F S
  let Kₛ := LinearMap.ker (sLocalAdelicTheta F S)
  let Kₜ := LinearMap.ker (sLocalAdelicTheta F T)
  let eS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  let eT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
  have heS (a : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
      eS (Kₛ.mkQ a) = Kₛ.mkQ (sAdeleSchwartzFourier a) :=
    (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 a
  have heT (a : SchwartzBruhat (Multiplicative (SAdeleRing F T))) :
      eT (Kₜ.mkQ a) = Kₜ.mkQ (sAdeleSchwartzFourier a) :=
    (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose_spec.2 a
  have hc := (h F S).1 T hST (Kₛ.mkQ f)
  change eT (Kₜ.mkQ (sAdeleSchwartzTransition F hST f)) =
    sLocalThetaTransition (F := F) hST (eS (Kₛ.mkQ f)) at hc
  rw [heT, heS] at hc
  change (Submodule.Quotient.mk (sAdeleSchwartzFourier (sAdeleSchwartzTransition F hST f)) :
      SLocalAdelicThetaSpace F T) =
    Submodule.Quotient.mk (sAdeleSchwartzTransition F hST (sAdeleSchwartzFourier f)) at hc
  have hz := thetaFourier_insertion_false_local_zero F T _ _ hc
  rw [thetaFourier_insertion_false_transition_zero] at hz
  have hscale := thetaFourier_insertion_false_transition F S {v} (by simp [S]) f
  have hs : sAdeleSchwartzFourier (sAdeleSchwartzTransition F hST f)
      (Multiplicative.ofAdd (0 : SAdeleRing F T)) =
        (((finiteLocalAdditiveTamagawaMeasure F v)
          (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal : ℂ) := by
    rw [hf, mul_one] at hscale
    simpa (config := { congrConsts := false }) using hscale
  rw [hs, hf] at hz
  have hmone : (finiteLocalAdditiveTamagawaMeasure F v)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    exact_mod_cast hz
  exact hm.ne hmone

/-- Paper: Theorem 5.2.4.1(1)–(2), p. 239.
As printed: for every number field, every finite stage containing the archimedean places,
and every continuous global norm-one character, the descended local character used in the
isotype assertions exists. This records the existence required by the printed scope.
The descent criterion is `normOneCharacterUnramifiedOutside_iff`, and
`sLocalThetaFourier_mem_isotype` states exchange for local characters. See ERRATA F31.
-/
def Printed.exists_sLocalNormOneCharacter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F)))
    (ω : PontryaginDual (ideleClassNorm F).ker),
    ∃ χ : PontryaginDual (sIdeleQuotientNorm F S).ker,
      ∀ (u : (integralAdelesOutside F S)ˣ) (x : (ideleClassNorm F).ker)
        (y : (sIdeleQuotientNorm F S).ker),
        let g := integralIdeleInsertion F S u
        x.val = QuotientGroup.mk g →
        y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom g) →
        χ y = ω x

/-- Paper: Theorem 5.2.4.1(1)–(2), p. 239.
Take F = ℚ, S consisting of the real place, and the quadratic character modulo 3.
The idele with component −1 at 3 and 1 everywhere else is a unit outside S and has norm
one. Its S-projection is the identity, while the global character takes value −1 there.
-/
theorem Printed.exists_sLocalNormOneCharacter_false :
    ¬ Printed.exists_sLocalNormOneCharacter := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅
  -- The single nontrivial finite component can be placed at any finite place.
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨m, hm.isPrime, NeZero.ne m⟩
  let g := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  have hself : g.val.2 v = -1 := RestrictedProduct.mulSingle_eq_same _ _ _
  have hoff (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) : g.val.2 w = 1 :=
    RestrictedProduct.mulSingle_eq_of_ne _ _ hw
  have hinv : g⁻¹ = g := by simp [g, ← map_inv]
  have hmem : g ∈ (integralIdeleInsertion ℚ S).range := by
    apply (mem_range_integralIdeleInsertion ℚ S g).2
    intro w _
    have hw : g.val.2 w ∈ w.adicCompletionIntegers ℚ := by
      rcases eq_or_ne w v with rfl | h
      · rw [hself]
        exact neg_mem (one_mem _)
      · rw [hoff _ h]
        exact one_mem _
    exact ⟨hw, by change (g⁻¹).val.2 w ∈ _; rwa [hinv]⟩
  obtain ⟨u, hu⟩ := hmem
  have hproj : Units.map (adeleProjection ℚ S).toMonoidHom g = 1 := by
    apply Units.ext
    exact Prod.ext rfl (funext fun w ↦ (Finset.notMem_empty w.val w.property).elim)
  let c := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  have hc : c ∈ (ideleClassNorm ℚ).ker := by
    change ideleClassNorm ℚ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)) = 1
    rw [ideleClassNorm_ofAdicCompletion]
    apply Units.ext
    change ‖(-1 : v.adicCompletion ℚ)‖₊ = 1
    simp
  let x : (ideleClassNorm ℚ).ker := ⟨c, hc⟩
  have hne : x ≠ 1 := by
    intro hx
    have he : QuotientGroup.mk g = (1 : IdeleClassGroup (𝓞 ℚ) ℚ) := congrArg Subtype.val hx
    obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff g).mp he
    -- A principal representative with infinite component 1 must come from 1.
    have hreal : algebraMap ℚ (InfiniteAdeleRing ℚ) q.val = 1 :=
      congrArg (fun a : 𝔸[ℚ]ˣ ↦ a.val.1) hq
    have hq1 : q = 1 := Units.ext ((algebraMap ℚ (InfiniteAdeleRing ℚ)).injective
      (hreal.trans (map_one _).symm))
    rw [hq1, map_one] at hq
    have hcontra : (1 : v.adicCompletion ℚ) = -1 :=
      (congrArg (fun a : 𝔸[ℚ]ˣ ↦ a.val.2 v) hq).trans hself
    have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
      (by simpa only [map_one, map_neg] using hcontra)
    norm_num at this
  -- Separate the global class from 1; no local character can do so after projection.
  let : T2Space (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.2.1
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  obtain ⟨ω, hω⟩ := exists_pontryaginDual_apply_ne_one (G := (ideleClassNorm ℚ).ker) hne
  intro h
  obtain ⟨χ, hχ⟩ := h ℚ S ω
  apply hω
  have h := hχ u x 1 (by rw [hu]; rfl) (by rw [hu, hproj]; rfl)
  simpa using h.symm

end RiemannMasullo
