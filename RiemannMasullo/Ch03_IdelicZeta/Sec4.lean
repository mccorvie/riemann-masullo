module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
public import RiemannMasullo.AppC_LCTVS.Sec5b
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Eigendistributions and Weil's identity

Masullo, §3.4, pp. 141–153. Page 154 is blank. The zeta integrals use the
Tamagawa measures from Appendix A. The local factorization recalled in
Notation 3.4.1.1 is `heckeCharacter_eq_prod_restrictions` from §3.1.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology UniformConvergenceCLM

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "C_F" => IdeleClassGroup (𝓞 F) F
local notation "X" => HeckeCharacter (𝓞 F) F
local notation "I_F" => IdeleGroup (𝓞 F) F
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "normℝ" => fun (g : C_F) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "finiteNorm(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "infiniteNorm(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)

section UnramifiedIdentity

local notation "AArch" => SAdeleRing F (∅ : Finset V)
local notation "μArch" => sMultiplicativeTamagawaMeasure F (∅ : Finset V)
local notation "μv" => finiteLocalMultiplicativeTamagawaMeasure F
local notation "valuation(" v ")" =>
  (Valued.v : Valuation (HeightOneSpectrum.adicCompletion F v) (WithZero (Multiplicative ℤ)))
local notation "positive" => (relativeRightHalfPlane (G := C_F) (ideleClassNorm F)
  (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 0 : Set X)

-- Named, because an anonymous instance gets the same generated name in every file that declares
-- it, and two such files can then not be imported together.
local instance instMeasurableSpaceUnitsAdicCompletionSec4 (v : V) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

/-- Paper: Equation (3.4.1.2), p. 143. The archimedean integral uses the
restriction of the quasi-character along insertion of the archimedean ideles. -/
def weilArchimedeanIntegral (fArch : ℬ(AArch)) (c : X) : ℂ :=
  ∫ g : AArchˣ, fArch (Multiplicative.ofAdd g.val) *
    c (classOf (sIdeleInsertion F ∅ g)) ∂μArch

/-- Paper: Equation (3.4.1.2), p. 143. The integral at the bare norm is the
integral of the test function weighted by the archimedean module. -/
theorem weilArchimedeanIntegral_norm (fArch : ℬ(AArch)) :
    weilArchimedeanIntegral fArch (ideleClassNormTwist 1 1) =
      ∫ g : AArchˣ, fArch (Multiplicative.ofAdd g.val) *
        (((sIdeleNorm F ∅ g : ℝ≥0) : ℝ) : ℂ) ∂μArch := by
  unfold weilArchimedeanIntegral
  congr with g
  rw [ideleClassNormTwist_one_one]
  change _ * (((ideleNorm F (sIdeleInsertion F ∅ g) : ℝ≥0) : ℝ) : ℂ) = _
  rw [ideleNorm_sIdeleInsertion]

/-- Paper: Theorem 3.4.1.1, p. 143. The archimedean integrand is absolutely
integrable at each quasi-character of positive abscissa. -/
theorem weilArchimedeanIntegral_integrable (fArch : ℬ(AArch)) (c : X) (hc : c ∈ positive) :
    Integrable (fun g : AArchˣ ↦ fArch (Multiplicative.ofAdd g.val) *
      c (classOf (sIdeleInsertion F ∅ g))) μArch := by
  obtain ⟨-, -, -, -, -, hC₂, hClc, -⟩ := ideleGroup_quotient.{_, 0} F
  let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  have hσ : 0 < σ := hc
  -- Compare with the S-local integrand for the norm twist of exponent σ and S = ∅.
  let c₀ : QuasiCharacter (SIdeleQuotient F ∅) :=
    quasiCharacterNormTwist (sIdeleQuotientNorm F ∅)
      (isProperMap_sIdeleQuotientNorm F ∅).continuous ((circleToComplex).comp 1) σ
  have hc₀ := sLocalIdelicZetaIntegral_integrable fArch c₀ ⟨1, σ, by simpa using hσ, rfl⟩
  have hnorm (g : AArchˣ) : ‖c (classOf (sIdeleInsertion F ∅ g))‖ =
      ‖c₀ (QuotientGroup.mk g)‖ := by
    rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c]
    change (((ideleNorm F (sIdeleInsertion F ∅ g) : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ σ =
      ‖((1 : Circle) : ℂ) * ((((sIdeleQuotientNorm F ∅ (QuotientGroup.mk g) : ℝ≥0ˣ) :
        ℝ≥0) : ℝ) : ℂ) ^ (σ : ℂ)‖
    rw [ideleNorm_sIdeleInsertion, sIdeleQuotientNorm_mk, Circle.coe_one, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Complex.ofReal_re]
  -- The σ-algebras of §3.3.1 on the archimedean ideles.
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace AArch := inferInstanceAs (MeasurableSpace
    (InfiniteAdeleRing F × ((v : (∅ : Finset V)) → v.val.adicCompletion F)))
  let : BorelSpace AArchˣ := sIdeleGroup_borelSpace
  have hf : Continuous fun g : AArchˣ ↦ fArch (Multiplicative.ofAdd g.val) :=
    (schwartzBruhat_continuous (G := Multiplicative AArch) fArch).comp
      (continuous_ofAdd.comp Units.continuous_val)
  have hcc : Continuous fun g : AArchˣ ↦ c (classOf (sIdeleInsertion F ∅ g)) :=
    c.continuous.comp (QuotientGroup.continuous_mk.comp
      (isClosedEmbedding_sIdeleInsertion F ∅).continuous)
  refine hc₀.norm.mono' (hf.mul hcc).aestronglyMeasurable (ae_of_all _ fun g ↦ ?_)
  rw [norm_mul, norm_mul, hnorm]

open Classical in
/-- Paper: Equations (3.4.1.3)–(3.4.1.4), p. 143. At an unramified place,
subtract the test function pulled back by inverse uniformizer multiplication
before integrating. At a ramified place, integrate the original test function. -/
def weilModifiedFiniteIntegral (v : V) (π : (v.adicCompletion F)ˣ)
    (f : v.adicCompletion F → ℂ) (c : X) : ℂ :=
  localIdelicZetaIntegral (μv v)
    (if c.IsUnramifiedAt v then fun x ↦ f x - f ((↑π⁻¹ : v.adicCompletion F) * x) else f)
    (finitePlaceRestriction F v c)

open Classical in
/-- Paper: Theorem 3.4.1.1, pp. 143–144. The finite-place integrals of the
modified compact-open indicators are absolutely convergent at positive abscissa. -/
theorem weilModifiedFiniteIntegral_integrable (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (K : Set (v.adicCompletion F))
    (hK : IsCompact K) (hKo : IsOpen K) (c : X) (hc : c ∈ positive) :
    let f := K.indicator (fun _ ↦ (1 : ℂ))
    let test := if c.IsUnramifiedAt v then fun x ↦ f x - f ((↑π⁻¹ : v.adicCompletion F) * x)
      else f
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ test g.val * finitePlaceRestriction F v c g)
      (μv v) := by
  intro f test
  let L := v.adicCompletion F
  have : BorelSpace Lˣ := ⟨rfl⟩
  -- The character has modulus a positive power of the local norm.
  obtain ⟨-, -, -, -, -, hC₂, hClc, -⟩ := ideleGroup_quotient.{_, 0} F
  let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  have hσ : 0 < σ := hc
  have hnorm (g : Lˣ) : ‖finitePlaceRestriction F v c g‖ = ‖(g : L)‖ ^ σ := by
    change ‖c (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g)‖ = _
    rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c]
    change (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^
      σ = _
    rw [ideleClassNorm_ofAdicCompletion]
    rfl
  -- The test function is bounded by two and vanishes outside a ball.
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let R := max R₀ (‖(π : L)‖ * R₀)
  have hsupp (x : L) (hx : test x ≠ 0) : ‖x‖ ≤ R := by
    have hcases : x ∈ K ∨ (↑π⁻¹ : L) * x ∈ K := by
      by_contra h
      push Not at h
      apply hx
      by_cases hu : c.IsUnramifiedAt v
      · simp only [test, f, hu, ite_true]
        rw [indicator_of_notMem h.1, indicator_of_notMem h.2, sub_self]
      · simp only [test, f, hu, ite_false]
        rw [indicator_of_notMem h.1]
    rcases hcases with h | h
    · exact (by simpa using hR₀ x h : ‖x‖ ≤ R₀).trans (le_max_left _ _)
    · have h' : ‖(↑π⁻¹ : L) * x‖ ≤ R₀ := by simpa using hR₀ _ h
      have hx : x = (π : L) * ((↑π⁻¹ : L) * x) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      refine le_trans ?_ (le_max_right _ _)
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_left h' (norm_nonneg _)
  have hbound (x : L) : ‖test x‖ ≤ 2 := by
    have h1 (y : L) : ‖f y‖ ≤ 1 := by
      by_cases hy : y ∈ K <;> simp [f, hy]
    by_cases hu : c.IsUnramifiedAt v
    · simp only [test, hu, ite_true]
      exact (norm_sub_le _ _).trans (by linarith [h1 x, h1 ((↑π⁻¹ : L) * x)])
    · simp only [test, hu, ite_false]
      linarith [h1 x]
  -- Measurability: the test function is a difference of indicators of open sets of units.
  have hmeasf (a : L) : Measurable fun g : Lˣ ↦ f (a * g.val) := by
    have hopen : IsOpen {g : Lˣ | a * g.val ∈ K} :=
      hKo.preimage ((continuous_const.mul Units.continuous_val))
    have heq : (fun g : Lˣ ↦ f (a * g.val)) = {g : Lˣ | a * g.val ∈ K}.indicator 1 := by
      funext g
      by_cases hg : a * g.val ∈ K <;> simp [f, hg]
    rw [heq]
    exact measurable_one.indicator hopen.measurableSet
  have hmeas : Measurable fun g : Lˣ ↦ test g.val := by
    by_cases hu : c.IsUnramifiedAt v
    · simp only [test, hu, ite_true]
      have h1 := hmeasf 1
      simp only [one_mul] at h1
      exact h1.sub (hmeasf _)
    · simp only [test, hu, ite_false]
      have h1 := hmeasf 1
      simpa only [one_mul] using h1
  -- Dominate by the truncated norm power.
  have hb := finiteLocalTamagawa_integrable_norm_rpow v hσ R
  refine (hb.2.const_mul 2).mono'
    (hmeas.aestronglyMeasurable.mul (finitePlaceRestriction F v c).continuous.aestronglyMeasurable)
    (ae_of_all _ fun g ↦ ?_)
  rw [norm_mul, hnorm]
  by_cases hg : test (g : L) = 0
  · rw [hg, norm_zero, zero_mul]
    exact mul_nonneg zero_le_two (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)
  · rw [indicator_of_mem (show g ∈ {u : Lˣ | ‖(u : L)‖ ≤ R} from hsupp _ hg)]
    exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)

/-- Paper: Theorem 3.4.1.1, p. 144. At an unramified place the modified
integer-ring indicator integrates to the Tamagawa mass of the integer units. -/
theorem weilModifiedFiniteIntegral_integerRing (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (c : X)
    (hc : c.IsUnramifiedAt v) :
    weilModifiedFiniteIntegral v π
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ 1)) c =
      ((μv v) (v.adicCompletionIntegers F).units).toReal := by
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let U : Set Kˣ := (v.adicCompletionIntegers F).units
  let val := (valuation(v))
  -- The uniformizer has valuation `exp (-1)`, the largest value below one.
  have hval : val (π : K) = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hlt (y : WithZero (Multiplicative ℤ)) (hy : y < 1) : y ≤ WithZero.exp (-1) := by
    rcases eq_or_ne y 0 with rfl | h0
    · exact zero_le
    rw [← WithZero.exp_log h0] at hy ⊢
    rw [WithZero.exp_lt_one_iff] at hy
    rw [WithZero.exp_le_exp]
    omega
  have hmemO (x : K) : x ∈ O ↔ val x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  have hmemU (x : K) : x ∈ Units.val '' U ↔ val x = 1 := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      have h1 : val (g : K) ≤ 1 := (hmemO _).mp hg.1
      have h2 : val ((g⁻¹ : Kˣ) : K) ≤ 1 := (hmemO _).mp hg.2
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
      have hg0 : val (g : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr g.ne_zero
      exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hg0)).mp h2)
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, map_zero] at hx
        exact zero_ne_one hx
      refine ⟨Units.mk0 x hx0, ⟨(hmemO _).mpr hx.le, (hmemO _).mpr ?_⟩, rfl⟩
      simp only [Units.coeHom_apply, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hx,
        inv_one, le_refl]
  have hπinv (x : K) : val ((↑π⁻¹ : K) * x) = WithZero.exp 1 * val x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval, ← WithZero.exp_neg, neg_neg]
  -- The modified integer-ring indicator is the indicator of the integer units.
  have htest : (fun x : K ↦ O.indicator (fun _ ↦ (1 : ℂ)) x -
      O.indicator (fun _ ↦ (1 : ℂ)) ((↑π⁻¹ : K) * x)) =
        (Units.val '' U).indicator (fun _ ↦ 1) := by
    funext x
    have he1 : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp 1 := by simp
    rcases lt_trichotomy (val x) 1 with h | h | h
    · have hx : x ∈ O := (hmemO x).mpr h.le
      have hx' : (↑π⁻¹ : K) * x ∈ O := by
        rw [hmemO, hπinv]
        calc WithZero.exp 1 * val x ≤ WithZero.exp 1 * WithZero.exp (-1) := by
              gcongr
              exact hlt _ h
          _ = 1 := by rw [← WithZero.exp_add]; simp
      have hU : x ∉ Units.val '' U := fun hU ↦ h.ne ((hmemU x).mp hU)
      rw [indicator_of_mem hx, indicator_of_mem hx', indicator_of_notMem hU, sub_self]
    · have hx : x ∈ O := (hmemO x).mpr h.le
      have hx' : (↑π⁻¹ : K) * x ∉ O := by
        rw [hmemO, hπinv, h, mul_one, not_le]
        exact he1
      have hU : x ∈ Units.val '' U := (hmemU x).mpr h
      rw [indicator_of_mem hx, indicator_of_notMem hx', indicator_of_mem hU, sub_zero]
    · have hx : x ∉ O := by rw [hmemO, not_le]; exact h
      have hx' : (↑π⁻¹ : K) * x ∉ O := by
        rw [hmemO, hπinv, not_le]
        calc (1 : WithZero (Multiplicative ℤ)) = 1 * 1 := (mul_one 1).symm
          _ < WithZero.exp 1 * val x := mul_lt_mul'' he1 h zero_le zero_le
      have hU : x ∉ Units.val '' U := fun hU ↦ h.ne' ((hmemU x).mp hU)
      rw [indicator_of_notMem hx, indicator_of_notMem hx', indicator_of_notMem hU, sub_zero]
  -- The integer units are a compact open set on which the character is trivial.
  have : BorelSpace Kˣ := ⟨rfl⟩
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := by
    have : ProperSpace K := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set K)
    convert isCompact_closedBall (0 : K) 1 using 1
    ext x
    simp only [SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right,
      Valued.toNormedField.norm_le_one_iff]
    exact hmemO x
  have : (μv v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  have hcU (g : Kˣ) (hg : g ∈ U) : finitePlaceRestriction F v c g = 1 := by
    let x := (v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType ⟨g, hg⟩
    have h := HeckeCharacter.isUnramifiedAt_iff.mp hc x
    simp only [HeckeCharacter.restrict, x] at h
    have hxg : (((v.adicCompletionIntegers F).unitsEquivUnitsType ⟨g, hg⟩ :
        v.adicCompletionIntegers F) : K) = (g : K) := rfl
    rw [hxg, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits] at h
    exact h
  unfold weilModifiedFiniteIntegral
  simp only [hc, ↓reduceIte]
  rw [htest]
  exact localIdelicZetaIntegral_indicator (μv v) _ U hUo.measurableSet hUc.measure_ne_top hcU

/-- Paper: Equation (3.4.1.1), p. 143. The modified zeta function is the
archimedean integral times the product of the modified finite integrals. -/
def weilModifiedZeta (fArch : ℬ(AArch)) (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ) (c : X) : ℂ :=
  weilArchimedeanIntegral fArch c *
    (∏' v : V, weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c)

/-- Paper: Theorem 3.4.1.1, pp. 143–144. When the character is unramified
at every finite place and every local test is the integer-ring indicator,
the finite product contributes the product of integer-unit masses. -/
theorem weilModifiedZeta_integerRings (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hK : ∀ v : V, K v = v.adicCompletionIntegers F) (c : X)
    (hc : ∀ v, c.IsUnramifiedAt v) :
    weilModifiedZeta fArch K uniformizer c = weilArchimedeanIntegral fArch c *
      ∏ᶠ v : V, (((μv v) (v.adicCompletionIntegers F).units).toReal : ℂ) := by
  have hfactor (v : V) :
      weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c =
        (((μv v) (v.adicCompletionIntegers F).units).toReal : ℂ) := by
    rw [hK v]
    exact weilModifiedFiniteIntegral_integerRing v _ (hπ v) c (hc v)
  unfold weilModifiedZeta
  rw [tprod_congr hfactor]
  congr 1
  refine tprod_eq_finprod ((finiteLocalTamagawaMass_finite (F := F)).subset fun v hv h ↦ hv ?_)
  change ((((μv v) (v.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) = 1
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, h, ENNReal.toReal_one,
    Complex.ofReal_one]

/-- Paper: Theorem 3.4.1.1, p. 143. The finite-place factors of the modified
zeta product differ from one by an absolutely summable family. -/
theorem weilModifiedZeta_summable
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F) (c : X) (hc : c ∈ positive) :
    Summable (fun v : V ↦
      ‖weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c - 1‖) := by sorry

/-- Paper: Theorem 3.4.1.1, p. 143. The net of partial modified products
converges uniformly on compact sets of quasi-characters of positive abscissa. -/
theorem weilModifiedZeta_tendstoUniformlyOn (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (L : Set X) (hL : IsCompact L) (hLpos : L ⊆ positive) :
    TendstoUniformlyOn (fun S : Finset V ↦ fun c ↦
      weilArchimedeanIntegral fArch c *
        ∏ v ∈ S, weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c)
      (weilModifiedZeta fArch K uniformizer) atTop L := by sorry

/-- Paper: Theorem 3.4.1.1, p. 143. The modified zeta product is holomorphic
on the positive half-plane in each unitary norm-twist coordinate. -/
theorem weilModifiedZeta_analyticOn (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F) (χ : PontryaginDual C_F) :
    AnalyticOnNhd ℂ (fun s ↦ weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s))
      (Complex.re ⁻¹' Ioi 0) := by sorry

/-- Paper: Proof of Theorem 3.4.1.1, p. 144. For a character of positive abscissa
unramified at every finite place, the archimedean integral equals the continued
S-idelic Z-function with no finite places. -/
theorem weilArchimedeanIntegral_eq_sLocal (fArch : ℬ(AArch)) (c : X)
    (hc : c ∈ unramifiedOutside F ∅) (hpos : c ∈ positive) :
    weilArchimedeanIntegral fArch c =
      sLocalIdelicZFunction fArch (sIdeleRestriction F ∅ ⟨c, hc⟩) := by sorry

-- TODO(paper-gap): Equations (3.4.1.5)–(3.4.1.6) omit the outside integer-unit masses.
-- In (3.4.1.6) the ramified finite Euler factors are one, and the continuation
-- on the positive half-plane can have a pole. Footnote 3 asks for the product comparison.

open Classical in
/-- Paper: Equation (3.4.1.5), p. 143. The modified product factors through the
S₀-idelic integral over the archimedean and ramified places, with modified factors at
the remaining exceptional places in S.
Deviation: The Tamagawa masses of the integer units outside S are included. The finite
sets S₀ and S index only finite places, since all archimedean places are implicit. -/
theorem weilModifiedZeta_eq_sLocal (S₀ S : Finset V) (hS : S₀ ⊆ S)
    (fArch : ℬ(AArch)) (fS₀ : ℬ(SAdeleRing F S₀))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ v ∉ S, K v = v.adicCompletionIntegers F)
    (hfS₀ : ∀ x : SAdeleRing F S₀, fS₀ (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (x.1, 0)) *
        ∏ v : S₀, (K v.val).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (c : X) (hc : c ∈ positive) (hc₀ : c ∈ unramifiedOutside F S₀)
    (hram : ∀ v ∈ S₀, ¬ c.IsUnramifiedAt v) :
    weilModifiedZeta fArch K uniformizer c =
      (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
        sLocalIdelicZetaIntegral fS₀ (sIdeleRestriction F S₀ ⟨c, hc₀⟩) *
        ∏ v ∈ S \ S₀,
          weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c := by sorry

/-- Paper: Equation (3.4.1.6), p. 143, in the form used on p. 231. The zeta integral
of a test extended from S is its S-idelic zeta integral times the outside Euler product.
Deviation: The Tamagawa masses of the integer units outside S are included. This is the
absolute-convergence form of the identity, with an arbitrary S-adelic test function. -/
theorem weilIdentity_unramifiedOutside (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re)
    (hc : ideleClassNormTwist χ s ∈ unramifiedOutside F S) :
    globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ s) =
      (∏ᶠ v : {v : V // v ∉ S},
          (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
        sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨ideleClassNormTwist χ s, hc⟩) *
        ∏' v : {v : V // v ∉ S}, finiteHeckeEulerFactor χ v.val s := by sorry

/-- Paper: Equation (3.4.1.6), pp. 143–144, as applied on p. 231. For a test extended
from S, the global Z-function is the S-local Z-function times the continued outside
Euler product and the outside integer-unit masses.
Deviation: The continuation is expressed away from a discrete set of exponents. -/
theorem weilIdentity_unramifiedOutside_meromorphic (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (χ : PontryaginDual C_F) (hc : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hLf : ∀ (s : ℂ) (hs : 1 < s.re), L s = finiteHeckeL χ ⟨s, hs⟩) :
    let cS := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hc⟩
    let twistS := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous cS
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦
        (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
          sLocalIdelicZFunction fS (twistS s) * (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s) := by
  sorry

/-- Paper: Equation (3.4.1.6), p. 143. For a pure tensor the zeta integral is the
modified zeta product times the finite Hecke L-function on the absolute-convergence half-plane.
Deviation: The modified product already contains the outside Tamagawa masses. The
finite Hecke L-function has Euler factor one at every ramified place, as in §3.2. -/
theorem weilIdentity_modifiedZeta (f : ℬ(𝔸[F])) (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (adeleProjection F ∅ x)) *
        ∏ᶠ v : V, (K v).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re) :
    globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s) *
        finiteHeckeL χ ⟨s, hs⟩ := by sorry

/-- Paper: Equation (3.4.1.6), pp. 143–144. The pure-tensor identity extends to the
positive half-plane for the continued zeta function and finite Hecke L-function.
Deviation: The same normalization as in `weilIdentity_modifiedZeta` is used. The
continuation is meromorphic, with equality expressed off a discrete set. -/
theorem weilIdentity_modifiedZeta_meromorphic (f : ℬ(𝔸[F])) (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (adeleProjection F ∅ x)) *
        ∏ᶠ v : V, (K v).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (χ : PontryaginDual C_F) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hLf : ∀ (s : ℂ) (hs : 1 < s.re), L s = finiteHeckeL χ ⟨s, hs⟩) :
    (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) =ᶠ[
        codiscreteWithin (Complex.re ⁻¹' Ioi 0)]
      (fun s ↦ weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s) * L s) := by sorry

end UnramifiedIdentity

section Applications

-- TODO(paper-gap): Proposition 3.4.2.1 asserts Lebesgue integrability on the
-- relative one-line. The standard test function over ℚ gives absolute divergence.

open Classical in
/-- Paper: Equation (3.4.2.6), p. 146. For the trivial norm-one character
the cutoff is the indicator of norm at most one. For other characters it vanishes. -/
def thetaPolarCutoff (ω : PontryaginDual C₁) (g : C_F) : ℂ :=
  if ω = 1 ∧ normℝ g ≤ 1 then 1 else 0

/-- Paper: Equation (3.4.2.6), p. 146. The trivial-character cutoff equals
one at the identity class. -/
theorem thetaPolarCutoff_one : thetaPolarCutoff (1 : PontryaginDual C₁) 1 = 1 := by
  simp [thetaPolarCutoff]

/-- Paper: Theorem 3.4.2.2(1), p. 146. At large norm homogeneous theta
decays to every inverse power, uniformly over a bounded set of test functions.
This restates the large-norm bound in `homogeneousAdelicTheta_decay_bounded`. -/
theorem weilTheta_decay_large (ω : PontryaginDual C₁)
    (B : Set ℬ(𝔸[F])) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C_F, T < normℝ g →
      ‖homogeneousAdelicTheta ω f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  obtain ⟨C, T, hC, -, h⟩ := homogeneousAdelicTheta_decay_bounded ω B hB N
  refine ⟨C, Real.exp T, hC, Real.exp_pos T, fun f hf g hg ↦ (h f hf g).1 ?_⟩
  have hpos : (0 : ℝ) < normℝ g := (Real.exp_pos T).trans hg
  exact (Real.lt_log_iff_exp_lt hpos).2 hg

-- TODO(paper-gap): Equation (3.4.2.4) drops the norm-one class volume
-- included in Theorem 2.2.5.4 and in Equations (3.4.2.9)–(3.4.2.10).

/-- Paper: Theorem 3.4.2.2(2), p. 146. At small norm homogeneous theta
minus the cutoff polar term decays to every power, uniformly over bounded sets.
Deviation: The polar coefficient includes the norm-one Tamagawa volume as in
Equation (3.4.2.10) and `homogeneousAdelicTheta_decay_bounded`. -/
theorem weilTheta_decay_small (ω : PontryaginDual C₁)
    (B : Set ℬ(𝔸[F])) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C_F, normℝ g < T →
      let zeroAdele := Multiplicative.ofAdd (0 : 𝔸[F])
      let polar := (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele
      ‖homogeneousAdelicTheta ω f g -
        (normOneIdeleClassTamagawaMeasure F univ).toReal • (thetaPolarCutoff ω g * polar)‖ ≤
        C * (normℝ g) ^ N := by sorry

/-- Paper: Theorem 3.4.2.2(2), p. 146. For norm at most one, the volume-scaled
cutoff polar term equals the polar term of Theorem 2.2.5.4. -/
theorem thetaPolarCutoff_polarTerm (ω : PontryaginDual C₁) (f : ℬ(𝔸[F])) (g : C_F)
    (hg : normℝ g ≤ 1) :
    (normOneIdeleClassTamagawaMeasure F univ).toReal •
        (thetaPolarCutoff ω g *
          ((normℝ g)⁻¹ • adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F])) -
            f (Multiplicative.ofAdd (0 : 𝔸[F])))) =
      homogeneousAdelicTheta_polarTerm ω f g := by
  unfold thetaPolarCutoff homogeneousAdelicTheta_polarTerm
  by_cases hω : ω = 1
  · rw [ite_eq_left ⟨hω, hg⟩, ite_eq_left hω, one_mul]
  · rw [ite_eq_right fun h ↦ hω h.1, ite_eq_right hω, zero_mul, smul_zero]

-- TODO(paper-gap): Equation (3.4.2.7) counts each modified finite factor
-- twice. The line below it also divides by the local Euler denominator,
-- while the definition (3.4.1.3) multiplies by that denominator.
-- TODO(paper-gap): Remarks 3.4.2.3–3.4.2.4 assert attainment of maxima on
-- arbitrary bounded sets. The compact closure gives a bound. The small-norm
-- estimate (3.4.2.17) also omits the polar subtraction for the full theta sum.

end Applications

section Eigendistributions

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "isEigen(" c "," T ")" =>
  (∀ g : Rˣ, ∀ f : ℬ(R), (T) (schwartzBruhatUnitTranslate g f) = (c) g * (T) f)

/-- Paper: Definition 3.4.3.1, p. 151. The weight condition is preserved
by zero, addition and complex scalar multiplication. -/
theorem schwartzBruhatEigen_submodule (c : QuasiCharacter Rˣ) :
    isEigen(c, (0 : StrongDual ℂ ℬ(R))) ∧
      (∀ T U : StrongDual ℂ ℬ(R), isEigen(c, T) → isEigen(c, U) → isEigen(c, T + U)) ∧
      (∀ (a : ℂ) (T : StrongDual ℂ ℬ(R)), isEigen(c, T) → isEigen(c, a • T)) := by
  refine ⟨fun g f ↦ by simp, fun T U hT hU g f ↦ ?_, fun a T hT g f ↦ ?_⟩
  · simp only [ContinuousLinearMap.add_apply, hT g f, hU g f, mul_add]
  · simp only [ContinuousLinearMap.smul_apply, hT g f, smul_eq_mul]
    ring

-- TODO(paper-gap): The right-translation gloss in Definition 3.4.3.1 reverses
-- the action of (2.1.2.2) and the weight condition recalled in Definition 5.5.1.1.

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. The eigendistributions are the
continuous functionals that take translation by a unit to multiplication by its weight.
Deviation: The action on test functions is `ρ(g, f)(x) = f(g⁻¹x)`, as in
Equation (2.1.2.2) and Definition 5.5.1.1. -/
def schwartzBruhatEigendistributions (c : QuasiCharacter Rˣ) : Submodule ℂ (StrongDual ℂ ℬ(R)) where
  carrier := {T | isEigen(c, T)}
  zero_mem' := (schwartzBruhatEigen_submodule c).1
  add_mem' := (schwartzBruhatEigen_submodule c).2.1 _ _
  smul_mem' a := (schwartzBruhatEigen_submodule c).2.2 a _

/-- Point evaluation on the Schwartz–Bruhat space is continuous because its
absolute value pulls back to a continuous seminorm on every elementary stage.
Copied from the private `continuous_schwartzBruhat_eval` in
`AppD_SchwartzBruhat/Sec2b.lean`, which this file does not import. -/
private theorem continuous_schwartzBruhat_eval' {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hp : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    intro a e
    let q := (normSeminorm ℂ ℂ).comp (L.comp (schwartzBruhatStageInclusion a e))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    apply Seminorm.continuous_of_le hp₀
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ p₀ f
    let := e.finiteGroup
    have he := schwartzBruhatStageRealization_apply a e f x
    by_cases hx : x ∈ a.val.1
    · rw [dite_eq_left hx] at he
      rw [he]
      let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
        (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
          (elementarySchwartzBound_zero f.val).symm
      exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
    · rw [dite_eq_right hx] at he
      exact ((congrArg norm he).trans (norm_zero (E := ℂ))).le.trans (apply_nonneg p₀ f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion a e)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. Evaluation at zero belongs
to the weight-one subspace, since unit multiplication fixes zero. -/
theorem schwartzBruhatEigendistributions_zeroEval :
    ∃ T : StrongDual ℂ ℬ(R), T ∈ schwartzBruhatEigendistributions (1 : QuasiCharacter Rˣ) ∧
      ∀ f : ℬ(R), T f = f (Multiplicative.ofAdd 0) := by
  let L : ℬ(R) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd 0)).comp (schwartzBruhatSubmodule _).subtype
  refine ⟨⟨L, continuous_schwartzBruhat_eval' _⟩, fun g f ↦ ?_, fun f ↦ rfl⟩
  change schwartzBruhatUnitTranslate g f (Multiplicative.ofAdd 0) = _ * f (Multiplicative.ofAdd 0)
  rw [schwartzBruhatUnitTranslate_apply, mul_zero]
  exact (one_mul _).symm

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. The weight subspace is
closed in the strong topology of the continuous dual. -/
theorem schwartzBruhatEigendistributions_isClosed (c : QuasiCharacter Rˣ) :
    IsClosed (schwartzBruhatEigendistributions c : Set (StrongDual ℂ ℬ(R))) := by
  have h : (schwartzBruhatEigendistributions c : Set (StrongDual ℂ ℬ(R))) =
      ⋂ (g : Rˣ) (f : ℬ(R)), {T | T (schwartzBruhatUnitTranslate g f) = c g * T f} := by
    ext T
    simp only [Set.mem_iInter]
    rfl
  -- Rewriting with `h` takes minutes, so transport closedness along it instead.
  exact (congrArg (fun s : Set (StrongDual ℂ ℬ(R)) ↦ IsClosed s) h).mpr
    (isClosed_iInter fun g ↦ isClosed_iInter fun f ↦
      isClosed_eq (continuous_eval_const _) ((continuous_eval_const f).const_mul _))

end Eigendistributions

/-- Paper: Definition 3.4.3.1(2), p. 151. The global weight subspace uses the
pullback of the quasi-character from the idele classes to the ideles. -/
def adelicEigendistributions (c : X) : Submodule ℂ (StrongDual ℂ ℬ(𝔸[F])) :=
  schwartzBruhatEigendistributions
    (c.comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : QuasiCharacter I_F)

/-- Paper: Definition 3.4.3.1(2), p. 151. At global weight one,
evaluation at the zero adele is an eigendistribution. -/
theorem adelicEigendistributions_zeroEval :
    ∃ T : StrongDual ℂ ℬ(𝔸[F]), T ∈ adelicEigendistributions (1 : X) ∧
      ∀ f : ℬ(𝔸[F]), T f = f (Multiplicative.ofAdd 0) := by
  have h1 : ((1 : X).comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
      QuasiCharacter I_F) = 1 := ContinuousMonoidHom.ext fun _ ↦ rfl
  have h2 : adelicEigendistributions (1 : X) =
      schwartzBruhatEigendistributions (1 : QuasiCharacter 𝔸[F]ˣ) :=
    congrArg schwartzBruhatEigendistributions h1
  -- Destructuring the existential with `obtain` unfolds the membership and takes minutes.
  exact (show ∃ T : StrongDual ℂ ℬ(𝔸[F]),
      T ∈ schwartzBruhatEigendistributions (1 : QuasiCharacter 𝔸[F]ˣ) ∧
        ∀ f : ℬ(𝔸[F]), T f = f (Multiplicative.ofAdd 0) from
    schwartzBruhatEigendistributions_zeroEval).imp
    fun T hT ↦ ⟨(congrArg (T ∈ ·) h2).mpr hT.1, hT.2⟩

section Gaussians

local notation "realCoord(" h ")" => InfinitePlace.Completion.ringEquivRealOfIsReal h
local notation "complexCoord(" h ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex h

-- TODO(paper-gap): The complex monomials in (3.4.3.5)–(3.4.3.6) have the same
-- angular weight as the character, so their local zeta integrals vanish at nonzero weight.

open Classical in
/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The local real Gaussian is
even or odd according to the character on signs. The complex Gaussian
has angular exponent opposite to the character.
Deviation: The monomials in (3.4.3.5)–(3.4.3.6) are conjugated so that the
angular factors cancel in the local zeta integral. -/
def infiniteStandardGaussianValue (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (x : w.Completion) : ℂ :=
  if h : w.IsReal then
    let y := realCoord(h) x
    let parity := if χ (-1) = 1 then (1 : ℝ) else y
    (parity * Real.exp (-Real.pi * y ^ 2) : ℝ)
  else
    let e := complexCoord(InfinitePlace.not_isReal_iff_isComplex.mp h)
    let c : ℂˣ →ₜ* ℂ :=
      (circleToComplex).comp (χ.comp ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.continuous.units_map _⟩)
    let m := (existsUnique_complexUnits_character_parameters c
      (fun _ ↦ Circle.norm_coe _)).exists.choose.2
    let z := e x
    let monomial := if 0 ≤ m then (star z) ^ m.natAbs else z ^ m.natAbs
    monomial * Complex.exp (-2 * (Real.pi : ℂ) * z * star z) / (2 * (Real.pi : ℂ))

/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The real and complex
Gaussian formulas give Schwartz–Bruhat test functions on the completion. -/
theorem infiniteStandardGaussian_mem (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    (fun x : Multiplicative w.Completion ↦ infiniteStandardGaussianValue w χ x.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative w.Completion) := by sorry

/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The standard infinite-place
test function is the Gaussian of the sign or angular weight.
Deviation: The complex Gaussian uses the conjugated monomials of `infiniteStandardGaussianValue`. -/
def infiniteStandardGaussian (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    ℬ(w.Completion) :=
  ⟨fun x ↦ infiniteStandardGaussianValue w χ x.toAdd, infiniteStandardGaussian_mem w χ⟩

/-- The angular exponent of the trivial unitary character of the complex units is zero. -/
theorem complexUnits_character_parameter_snd_trivial (c : ℂˣ →ₜ* ℂ) (hc : ∀ x, ‖c x‖ = 1)
    (h1 : ∀ x, c x = 1) :
    (existsUnique_complexUnits_character_parameters c hc).exists.choose.2 = 0 := by
  have h := (existsUnique_complexUnits_character_parameters c hc).unique
    (existsUnique_complexUnits_character_parameters c hc).exists.choose_spec
    (show ((0 : ℂ), (0 : ℤ)).1.re = 0 ∧ _ from ⟨by simp, fun x ↦ by simp [h1]⟩)
  exact congrArg Prod.snd h

open Classical in
/-- Paper: Equations (3.4.3.3) and (3.4.3.5), p. 152. At zero and weight
one, the real Gaussian equals one and the complex Gaussian equals one over two pi. -/
theorem infiniteStandardGaussian_trivial_zero (w : InfinitePlace F) :
    infiniteStandardGaussian w 1 (Multiplicative.ofAdd 0) =
      if w.IsReal then 1 else (2 * (Real.pi : ℂ))⁻¹ := by
  by_cases h : w.IsReal
  · simp [infiniteStandardGaussian, infiniteStandardGaussianValue, h]
  · simp only [infiniteStandardGaussian, infiniteStandardGaussianValue, h, dite_false,
      ite_false]
    rw [complexUnits_character_parameter_snd_trivial]
    · simp
    · intro x
      refine (congrArg norm (?_ : _ = (1 : ℂ))).trans (norm_one (α := ℂ))
      rfl
    · intro x
      rfl

local notation "integerUnits(" v ")" => ((HeightOneSpectrum.adicCompletionIntegers F v).units)
local notation "unramified(" v "," c ")" => (∀ u ∈ integerUnits(v), c u = (1 : ℂ))

open Classical in
/-- Paper: Definition 3.4.3.2(3), p. 152. The finite Gaussian is the
integer-ring indicator for unramified weights. For ramified weights it
is the inverse quasi-character on the integer units, extended by zero. -/
def finiteStandardGaussianValue (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (x : v.adicCompletion F) : ℂ :=
  if unramified(v, c) then
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ 1) x
  else
    (Units.val '' integerUnits(v)).indicator
      (fun y ↦ if hy : y ≠ 0 then (c (Units.mk0 y hy))⁻¹ else 0) x

/-- A complex number all of whose powers lie within `r < 1` of one is one. Otherwise the real
parts of the geometric sums `∑ n < N, z ^ n` would grow linearly in `N`, while the sums
themselves, equal to `(z ^ N - 1) / (z - 1)`, stay bounded. -/
private theorem eq_one_of_forall_norm_pow_sub_one_le {z : ℂ} {r : ℝ} (hr : r < 1)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ r) : z = 1 := by
  by_contra hz
  have hz1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hpos : 0 < (1 - r) * ‖z - 1‖ := mul_pos (sub_pos.mpr hr) hz1
  obtain ⟨N, hN⟩ := exists_nat_gt (r / ((1 - r) * ‖z - 1‖))
  rw [div_lt_iff₀ hpos] at hN
  have hre : (N : ℝ) * (1 - r) ≤ (∑ n ∈ Finset.range N, z ^ n).re := by
    rw [Complex.re_sum]
    have hle : ∀ n ∈ Finset.range N, 1 - r ≤ (z ^ n).re := fun n _ ↦ by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (z ^ n - 1)).trans (h n))).1
      rw [Complex.sub_re, Complex.one_re] at h1
      linarith
    simpa using Finset.card_nsmul_le_sum _ _ _ hle
  have hbound : (∑ n ∈ Finset.range N, z ^ n).re * ‖z - 1‖ ≤ r :=
    calc _ ≤ ‖∑ n ∈ Finset.range N, z ^ n‖ * ‖z - 1‖ :=
          mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hz1.le
      _ = ‖z ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ r := h N
  nlinarith [mul_le_mul_of_nonneg_right hre hz1.le]

/-- A continuous character of the units of a nonarchimedean normed field is trivial near one.
If `‖t - 1‖ < δ ≤ 1`, every power of `t` also lies within `δ` of one, so all powers of the
character value stay near one in `ℂ`, which forces the value to be one. -/
private theorem exists_forall_norm_sub_one_lt_map_eq_one {K : Type*} [NormedField K]
    [IsUltrametricDist K] (c : Kˣ →ₜ* ℂ) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ t : Kˣ, ‖(t : K) - 1‖ < δ → c t = 1 := by
  have hc : Tendsto c (nhds 1) (nhds 1) := by
    simpa only [map_one] using (map_continuous c).tendsto 1
  have hU := hc (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_map, mem_comap] at hU
  obtain ⟨s, hs, hsU⟩ := hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun t ht ↦ ?_⟩
  have ht1' : ‖(t : K) - 1‖ < 1 := ht.trans_le (min_le_right _ _)
  have ht1 : ‖(t : K)‖ = 1 := by
    have hne : ‖(1 : K)‖ ≠ ‖(t : K) - 1‖ := by rw [norm_one]; exact ht1'.ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    rwa [add_sub_cancel, norm_one, max_eq_left ht1'.le] at this
  have hpow (n : ℕ) : ‖((t ^ n : Kˣ) : K) - 1‖ < min ε 1 := by
    induction n with
    | zero => simpa using lt_min hε one_pos
    | succ n ih =>
      rw [Units.val_pow_eq_pow_val] at ih ⊢
      have he : (t : K) ^ (n + 1) - 1 = (t : K) ^ n * ((t : K) - 1) + ((t : K) ^ n - 1) := by
        ring
      rw [he]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rwa [norm_mul, norm_pow, ht1, one_pow, one_mul]
  refine eq_one_of_forall_norm_pow_sub_one_le (r := 1 / 2) (by norm_num) fun n ↦ ?_
  have hmem : ((t ^ n : Kˣ) : K) ∈ s := hball (by
    rw [Metric.mem_ball, dist_eq_norm, Units.val_one]
    exact (hpow n).trans_le (min_le_left _ _))
  have hlt := Metric.mem_ball.mp (hsU hmem)
  rw [dist_eq_norm, map_pow] at hlt
  exact hlt.le

/-- An element of a finite completion is the image of an integral unit exactly when its norm
is one. -/
private theorem mem_integerUnits_iff_norm_eq_one (v : V) (x : v.adicCompletion F) :
    x ∈ Units.val '' integerUnits(v) ↔ ‖x‖ = 1 := by
  have he1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 1 :=
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'
  rw [NumberField.FinitePlace.norm_def, NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff _ _ he1]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha
  · intro hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    exact ⟨Units.mk0 x hx0,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hx, rfl⟩

/-- Paper: Definition 3.4.3.2(3), p. 152. Both finite Gaussian formulas
give Schwartz–Bruhat test functions on the completion. -/
theorem finiteStandardGaussian_mem (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    (fun x : Multiplicative (v.adicCompletion F) ↦ finiteStandardGaussianValue v c x.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F)) := by
  -- At a finite place, Schwartz–Bruhat means locally constant with compact support.
  classical
  set O : Set (v.adicCompletion F) := ↑(v.adicCompletionIntegers F) with hO
  have hOc : IsCompact O :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := F) v)
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  have hOcl : IsClosed O := Valued.isClosed_valuationSubring _
  have hlc : IsLocallyConstant (finiteStandardGaussianValue v c) ∧
      HasCompactSupport (finiteStandardGaussianValue v c) := by
    by_cases hu : unramified(v, c)
    · -- Unramified: the indicator of the compact open integer ring.
      have hf : finiteStandardGaussianValue v c = O.indicator (fun _ ↦ 1) := by
        funext x
        unfold finiteStandardGaussianValue
        rw [ite_eq_left hu]
      rw [hf]
      refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_,
        HasCompactSupport.intro hOc fun x hx ↦ indicator_of_notMem hx _⟩
      by_cases hx : x ∈ O
      · exact ⟨O, hOo, hx, fun y hy ↦ by rw [indicator_of_mem hy, indicator_of_mem hx]⟩
      · exact ⟨Oᶜ, hOcl.isOpen_compl, hx, fun y hy ↦ by
          rw [indicator_of_notMem hy, indicator_of_notMem hx]⟩
    · -- Ramified: the inverse character on the integral units, which form the unit sphere.
      set U₀ : Set (v.adicCompletion F) := Units.val '' integerUnits(v) with hU₀
      have hU₀O : U₀ ⊆ O := by
        rintro _ ⟨a, ha, rfl⟩
        exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha).le
      have hf : finiteStandardGaussianValue v c = U₀.indicator
          (fun y ↦ if hy : y ≠ 0 then (c (Units.mk0 y hy))⁻¹ else 0) := by
        funext x
        unfold finiteStandardGaussianValue
        rw [ite_eq_right hu]
      rw [hf]
      refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_,
        HasCompactSupport.intro hOc fun x hx ↦ indicator_of_notMem (fun h ↦ hx (hU₀O h)) _⟩
      by_cases hx : x ∈ U₀
      · obtain ⟨δ, hδ, hδ1, hδc⟩ := exists_forall_norm_sub_one_lt_map_eq_one c
        have hx1 : ‖x‖ = 1 := (mem_integerUnits_iff_norm_eq_one v x).mp hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          simp at hx1
        refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun y hy ↦ ?_⟩
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have hy1 : ‖y‖ = 1 := by
          have hne : ‖x‖ ≠ ‖y - x‖ := by rw [hx1]; exact (hy.trans_le hδ1).ne'
          have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
          rwa [add_sub_cancel, hx1, max_eq_left (hy.trans_le hδ1).le] at this
        have hy0 : y ≠ 0 := by
          rintro rfl
          simp at hy1
        have hyU : y ∈ U₀ := (mem_integerUnits_iff_norm_eq_one v y).mpr hy1
        rw [indicator_of_mem hyU, indicator_of_mem hx, dite_eq_left hy0, dite_eq_left hx0]
        have ht : Units.mk0 y hy0 = Units.mk0 x hx0 * Units.mk0 (y / x) (div_ne_zero hy0 hx0) :=
          Units.ext (by simp [mul_div_cancel₀ _ hx0])
        have hsmall : ‖((Units.mk0 (y / x) (div_ne_zero hy0 hx0) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) - 1‖ < δ := by
          rw [Units.val_mk0, show y / x - 1 = (y - x) / x by field_simp, norm_div, hx1, div_one]
          exact hy
        rw [ht, map_mul, hδc _ hsmall, mul_one]
      · refine ⟨U₀ᶜ, ?_, hx, fun y hy ↦ by rw [indicator_of_notMem hy, indicator_of_notMem hx]⟩
        have hsphere : U₀ = Metric.sphere 0 1 := by
          ext y
          rw [mem_sphere_zero_iff_norm]
          exact mem_integerUnits_iff_norm_eq_one v y
        rw [hsphere]
        exact Metric.isClosed_sphere.isOpen_compl
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (finiteStandardGaussianValue v c)).mpr hlc
  have heq : (fun x : Multiplicative (v.adicCompletion F) ↦
      finiteStandardGaussianValue v c x.toAdd) = (g : Multiplicative (v.adicCompletion F) → ℂ) :=
    funext fun x ↦ (hg x.toAdd).symm
  rw [heq]
  exact g.property

/-- Paper: Definition 3.4.3.2(3), p. 152. The finite-place standard
Gaussian is the bundled test function given by the local indicator formula. -/
def finiteStandardGaussian (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    ℬ(v.adicCompletion F) :=
  ⟨fun x ↦ finiteStandardGaussianValue v c x.toAdd, finiteStandardGaussian_mem v c⟩

/-- Paper: Equations (3.4.3.7)–(3.4.3.8), p. 152. On an integer unit,
the local Gaussian takes the reciprocal of the character value. -/
theorem finiteStandardGaussian_integerUnit (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (u : (v.adicCompletion F)ˣ) (hu : u ∈ integerUnits(v)) :
    finiteStandardGaussian v c (Multiplicative.ofAdd u.val) = (c u)⁻¹ := by
  classical
  change finiteStandardGaussianValue v c u.val = (c u)⁻¹
  unfold finiteStandardGaussianValue
  split_ifs with hc
  · rw [indicator_of_mem (show u.val ∈ (v.adicCompletionIntegers F : Set _) from hu.1),
      hc u hu, inv_one]
  · rw [indicator_of_mem (mem_image_of_mem _ hu)]
    simp [u.ne_zero]

local notation "infiniteUnitaryRestriction(" χ "," w ")" =>
  ((χ).comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩)

local notation "globalGaussianTest(" χ ")" => fun x : Multiplicative 𝔸[F] ↦
  (∏ w : InfinitePlace F,
    infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))
      (Multiplicative.ofAdd (x.toAdd.1 w))) *
    ∏ᶠ v : V, finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist (χ) 0))
      (Multiplicative.ofAdd (x.toAdd.2 v))

/-- Paper: Equation (3.4.3.9), p. 152. The restricted product of local
Gaussians is Schwartz–Bruhat on the adeles. -/
theorem adelicStandardGaussian_mem (χ : PontryaginDual C_F) :
    globalGaussianTest(χ) ∈ schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by sorry

/-- Paper: Equation (3.4.3.9), p. 152. The adelic Gaussian is the pointwise
restricted product of the indicated local Gaussians.
Deviation: The component is specified by a unitary representative, and the complex
factors use the conjugated monomials of `infiniteStandardGaussianValue`. -/
def adelicStandardGaussian (χ : PontryaginDual C_F) : ℬ(𝔸[F]) :=
  ⟨globalGaussianTest(χ), adelicStandardGaussian_mem χ⟩

/-- Paper: Equation (3.4.3.9), p. 152. The trivial-character Gaussian
at the zero adele has one factor of one over two pi per complex place. -/
theorem adelicStandardGaussian_trivial_zero :
    adelicStandardGaussian (1 : PontryaginDual C_F) (Multiplicative.ofAdd 0) =
      (2 * (Real.pi : ℂ))⁻¹ ^ InfinitePlace.nrComplexPlaces F := by
  classical
  have hInf (w : InfinitePlace F) :
      ((1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)).comp
        ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩) = 1 :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have hFin (v : HeightOneSpectrum (𝓞 F)) :
      finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist 1 0))
        (Multiplicative.ofAdd 0) = 1 := by
    have hc : ∀ u, finitePlaceRestriction F v (ideleClassNormTwist 1 0) u = 1 := fun u ↦ by
      change (((1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : Circle) : ℂ) *
        (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : NNReal) : ℝ) : ℂ) ^
          (0 : ℂ) = 1
      simp
    change finiteStandardGaussianValue v _ 0 = 1
    simp [finiteStandardGaussianValue, hc]
  change (∏ w : InfinitePlace F,
      infiniteStandardGaussian w _ (Multiplicative.ofAdd ((0 : 𝔸[F]).1 w))) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      finiteStandardGaussian v _ (Multiplicative.ofAdd ((0 : 𝔸[F]).2 v)) = _
  simp only [hInf]
  have h2 (v : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸[F]).2 v = 0 := rfl
  have hI (w : InfinitePlace F) :
      infiniteStandardGaussian w 1 (Multiplicative.ofAdd ((0 : 𝔸[F]).1 w)) =
        if w.IsReal then (1 : ℂ) else (2 * (Real.pi : ℂ))⁻¹ :=
    infiniteStandardGaussian_trivial_zero w
  simp only [h2, hFin, finprod_one, mul_one]
  refine (Finset.prod_congr rfl fun w _ ↦ hI w).trans ?_
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      (if w.1.IsReal then (1 : ℂ) else (2 * (Real.pi : ℂ))⁻¹) = 1 :=
    fun w ↦ ite_eq_left_iff.mpr fun h ↦ absurd w.2 h
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (if w.1.IsReal then (1 : ℂ) else (2 * (Real.pi : ℂ))⁻¹) = (2 * (Real.pi : ℂ))⁻¹ :=
    fun w ↦ ite_eq_right_iff.mpr fun h ↦ absurd h (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)
  simp only [hR, hC, Finset.prod_const_one, Finset.prod_const, Finset.card_univ, one_mul]

/-- Unitary characters of the complex units that agree on the unit circle have the same
angular exponent. -/
private theorem complexUnits_character_parameter_snd_congr (c d : ℂˣ →ₜ* ℂ)
    (hc : ∀ x, ‖c x‖ = 1) (hd : ∀ x, ‖d x‖ = 1)
    (h : ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → c x = d x) :
    (existsUnique_complexUnits_character_parameters c hc).exists.choose.2 =
      (existsUnique_complexUnits_character_parameters d hd).exists.choose.2 := by
  have hP := (existsUnique_complexUnits_character_parameters c hc).exists
  have hQ := (existsUnique_complexUnits_character_parameters d hd).exists
  change hP.choose.2 = hQ.choose.2
  have key (x : ℂˣ) : ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ hP.choose.2 =
      ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ hQ.choose.2 := by
    have hr : ‖(x : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr x.ne_zero
    let u : ℂˣ := Units.mk0 ((x : ℂ) / (‖(x : ℂ)‖ : ℂ))
      (div_ne_zero x.ne_zero (Complex.ofReal_ne_zero.mpr hr))
    have hu : ‖(u : ℂ)‖ = 1 := by
      change ‖(x : ℂ) / (‖(x : ℂ)‖ : ℂ)‖ = 1
      rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self hr]
    have h1 := hP.choose_spec.2 u
    have h2 := hQ.choose_spec.2 u
    rw [hu, one_pow, Complex.ofReal_one, Complex.one_cpow, one_mul, div_one] at h1 h2
    exact h1.symm.trans ((h u hu).trans h2)
  have hpair := (existsUnique_complexUnits_character_parameters c hc).unique hP.choose_spec
    (show (hP.choose.1, hQ.choose.2).1.re = 0 ∧ _ from
      ⟨hP.choose_spec.1, fun x ↦ by rw [hP.choose_spec.2 x, key x]⟩)
  exact (congrArg Prod.snd hpair :)

/-- Paper: Definition 3.4.3.2, p. 152. The adelic Gaussian depends only on
the restriction of the unitary representative to the norm-one classes. -/
theorem adelicStandardGaussian_eq_of_restriction (χ ψ : PontryaginDual C_F)
    (h : normOneRestriction (G := C_F) (ideleClassNorm F) (ideleClassNormTwist χ 0) =
      normOneRestriction (G := C_F) (ideleClassNorm F) (ideleClassNormTwist ψ 0)) :
    adelicStandardGaussian χ = adelicStandardGaussian ψ := by
  classical
  have hk : ∀ g : C_F, ideleClassNorm F g = 1 → χ g = ψ g := fun g hg ↦ by
    have hg' := DFunLike.congr_fun h ⟨g, hg⟩
    change (χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
      (ψ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) at hg'
    rw [Complex.cpow_zero, mul_one, mul_one] at hg'
    exact Circle.coe_injective hg'
  have hN (w : InfinitePlace F) (y : w.Completionˣ) (hy : ‖(y : w.Completion)‖ = 1) :
      χ (IdeleClassGroup.ofCompletion (𝓞 F) F w y) =
        ψ (IdeleClassGroup.ofCompletion (𝓞 F) F w y) :=
    hk _ (by
      rw [ideleClassNorm_ofCompletion, show Units.map nnNormHom.toMonoidHom y = 1 from
        Units.ext (NNReal.coe_injective hy), one_pow])
  have hInf (w : InfinitePlace F) (x : w.Completion) :
      infiniteStandardGaussianValue w (infiniteUnitaryRestriction(χ,w)) x =
        infiniteStandardGaussianValue w (infiniteUnitaryRestriction(ψ,w)) x := by
    unfold infiniteStandardGaussianValue
    by_cases hw : w.IsReal
    · simp only [dite_eq_left hw]
      congr 4
      exact hN w (-1) (by rw [Units.val_neg, Units.val_one, norm_neg, norm_one])
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hm := complexUnits_character_parameter_snd_congr
        ((circleToComplex).comp ((infiniteUnitaryRestriction(χ,w)).comp
          ⟨Units.map complexCoord(hc).symm.toMonoidHom,
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hc).symm.continuous.units_map _⟩))
        ((circleToComplex).comp ((infiniteUnitaryRestriction(ψ,w)).comp
          ⟨Units.map complexCoord(hc).symm.toMonoidHom,
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hc).symm.continuous.units_map _⟩))
        (fun _ ↦ Circle.norm_coe _) (fun _ ↦ Circle.norm_coe _)
        (fun x hx ↦ congrArg (fun z : Circle ↦ (z : ℂ))
          (hN w (Units.map complexCoord(hc).symm.toMonoidHom x)
            (((InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hc).symm.isometry.norm_map_of_map_zero
                (map_zero complexCoord(hc).symm) (x : ℂ)).trans hx)))
      simp only [dite_eq_right hw, hm]
  have hFin (v : V) (x : v.adicCompletion F) :
      finiteStandardGaussianValue v (finitePlaceRestriction F v (ideleClassNormTwist χ 0)) x =
        finiteStandardGaussianValue v
          (finitePlaceRestriction F v (ideleClassNormTwist ψ 0)) x := by
    have hu : ∀ u ∈ integerUnits(v), finitePlaceRestriction F v (ideleClassNormTwist χ 0) u =
        finitePlaceRestriction F v (ideleClassNormTwist ψ 0) u := fun u hu ↦
      DFunLike.congr_fun h ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u, by
        change ideleClassNorm F _ = 1
        rw [ideleClassNorm_ofAdicCompletion]
        exact Units.ext (NNReal.coe_injective (Valued.toNormedField.norm_eq_one_iff.mpr
          (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu)))⟩
    have h1 : unramified(v, finitePlaceRestriction F v (ideleClassNormTwist χ 0)) ↔
        unramified(v, finitePlaceRestriction F v (ideleClassNormTwist ψ 0)) :=
      forall₂_congr fun u hu' ↦ by rw [hu u hu']
    rw [finiteStandardGaussianValue, finiteStandardGaussianValue]
    by_cases h0 : unramified(v, finitePlaceRestriction F v (ideleClassNormTwist χ 0))
    · rw [ite_eq_left h0, ite_eq_left (h1.mp h0)]
    · rw [ite_eq_right h0, ite_eq_right (mt h1.mpr h0)]
      by_cases hx : x ∈ Units.val '' (integerUnits(v) : Set (v.adicCompletion F)ˣ)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        obtain ⟨u, hu', rfl⟩ := hx
        rw [dite_eq_left u.ne_zero, dite_eq_left u.ne_zero, Units.mk0_val, hu u hu']
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  apply Subtype.ext
  funext x
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ hInf w _)
    (finprod_congr fun v ↦ hFin v _)

-- TODO(paper-gap): Even with the corrected complex Gaussians, the Tamagawa
-- zeta integral has an extra factor of |d_F|^(-1/2) relative to the Euler product of §3.2.

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152.
The completed function with the Gaussian normalization is the continued
global zeta function of the standard Gaussian on the chosen component.
Deviation: This uses the corrected complex Gaussian and the Tamagawa measures.
The comparison with the completed Euler product of §3.2 includes the factor `|d_F|^(-1/2)`. -/
def gaussianCompletedHeckeL (χ : PontryaginDual C_F) (s : ℂ) : ℂ :=
  globalIdelicZFunction (adelicStandardGaussian χ) (ideleClassNormTwist χ s)

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152.
In the half-plane of absolute convergence, the Gaussian normalization
is the global zeta integral of the Gaussian. -/
theorem gaussianCompletedHeckeL_eq_integral (χ : PontryaginDual C_F) (s : ℂ)
    (hs : 1 < s.re) :
    gaussianCompletedHeckeL χ s =
      globalIdelicZetaIntegral (adelicStandardGaussian χ) (ideleClassNormTwist χ s) := by
  refine globalIdelicZFunction_eq_integral (adelicStandardGaussian χ) ?_
  change 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s)
  rwa [quasiCharacterAbscissa_ideleClassNormTwist]

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152. In the half-plane of
absolute convergence the Gaussian zeta function gives the completed Euler product of §3.2
scaled by the product of the finite integer-unit Tamagawa masses.
Deviation: The scale is the inverse square root of the absolute discriminant. -/
theorem gaussianCompletedHeckeL_eq_completedHeckeL (χ : PontryaginDual C_F) (s : ℂ)
    (hs : 1 < s.re) :
    gaussianCompletedHeckeL χ s =
      ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ) * completedHeckeL χ ⟨s, hs⟩ := by sorry

/-- Paper: Theorem 3.4.3.3(1), pp. 152–153. At a finite place each
quasi-character has a one-dimensional eigendistribution space. -/
theorem finiteEigendistributions_rank (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    Module.rank ℂ (schwartzBruhatEigendistributions c) = 1 := by sorry

/-- Paper: Theorem 3.4.3.3(1), pp. 152–153. At an infinite place each
quasi-character has a one-dimensional eigendistribution space. -/
theorem infiniteEigendistributions_rank (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) :
    Module.rank ℂ (schwartzBruhatEigendistributions c) = 1 := by sorry

-- TODO(paper-gap): At a finite place (3.4.3.13) needs the Tamagawa mass of the
-- integer units with the normalized tests in (3.4.3.10)–(3.4.3.11).

/-- Paper: Theorem 3.4.3.3(1), p. 153. The holomorphic family at a finite place
is normalized on the integer-ring indicator in the unramified case and on the inverse
character supported on the integer units in the ramified case. Scaling by the Euler
factor and the unit mass gives the zeta function away from the trivial quasi-character.
Deviation: Equation (3.4.3.13) includes the integer-unit Tamagawa mass. -/
theorem finiteEigendistribution_normalized (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let twist := quasiCharacterNormTwist (finiteNorm(v)) (continuous_finiteLocalModule v)
      ((circleToComplex).comp χ)
    ∃ D : ℂ → StrongDual ℂ ℬ(v.adicCompletion F), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(v.adicCompletion F),
        T = D s ↔ T ∈ schwartzBruhatEigendistributions (twist s) ∧
          T (finiteStandardGaussian v (twist s)) = 1) ∧
      ∀ s : ℂ, twist s ≠ 1 → ∀ f : ℬ(v.adicCompletion F),
        finiteLocalIdelicZFunction v f (twist s) =
          ((finiteLocalMultiplicativeTamagawaMeasure F v) integerUnits(v)).toReal *
            finiteLocalEulerFactor v (twist s) * D s f := by sorry

/-- Paper: Theorem 3.4.3.3(1), p. 153. At an infinite place the normalized
eigendistribution evaluates to one on the Gaussian and varies holomorphically.
Multiplication by the Euler factor recovers the local zeta function.
Deviation: The complex Gaussian uses the corrected angular weight, and the meromorphic
identity (3.4.3.13) is expressed off a discrete set of exponents. -/
theorem infiniteEigendistribution_normalized (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    ∃ D : ℂ → StrongDual ℂ ℬ(w.Completion), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(w.Completion),
        T = D s ↔ T ∈ schwartzBruhatEigendistributions (twist s) ∧
          T (infiniteStandardGaussian w χ) = 1) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
        infiniteLocalIdelicZFunction w f (twist s) =
          infiniteLocalEulerFactor w (twist s) * D s f := by sorry

/-- Paper: Theorem 3.4.3.3(2), p. 153. The global eigendistributions of
each idelic weight form a one-dimensional space. -/
theorem adelicEigendistributions_rank (c : X) :
    Module.rank ℂ (adelicEigendistributions c) = 1 := by sorry

/-- Paper: Theorem 3.4.3.3(2), p. 153. The unique global eigendistribution normalized
on the adelic Gaussian varies holomorphically. Multiplication by the Gaussian zeta
function recovers the global zeta function away from its possible poles.
Deviation: The scalar factor uses the Gaussian normalization of p. 152, including
its Tamagawa scale relative to the completed Euler product in §3.2. -/
theorem adelicEigendistribution_normalized (χ : PontryaginDual C_F) :
    ∃ D : ℂ → StrongDual ℂ ℬ(𝔸[F]), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(𝔸[F]),
        T = D s ↔ T ∈ adelicEigendistributions (ideleClassNormTwist χ s) ∧
          T (adelicStandardGaussian χ) = 1) ∧
      ∀ s : ℂ, ideleClassNormTwist χ s ≠ 1 →
        ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : PontryaginDual C_F) 1 →
        ∀ f : ℬ(𝔸[F]), globalIdelicZFunction f (ideleClassNormTwist χ s) =
          gaussianCompletedHeckeL χ s * D s f := by sorry

/-- Paper: Equation (3.4.3.14), p. 153. The normalized global eigendistribution
evaluates on a restricted pure tensor as the product of normalized local evaluations.
Deviation: Pointwise factorization specifies the test tensor. The product of finite-place
evaluations has finite support because the local factors are normalized on the standard Gaussians. -/
theorem adelicEigendistribution_apply_pureTensor (χ : PontryaginDual C_F) (s : ℂ) :
    let c := ideleClassNormTwist χ s
    ∀ (T : StrongDual ℂ ℬ(𝔸[F]))
      (TArch : (w : InfinitePlace F) → StrongDual ℂ ℬ(w.Completion))
      (TFin : (v : V) → StrongDual ℂ ℬ(v.adicCompletion F)),
      T ∈ adelicEigendistributions c → T (adelicStandardGaussian χ) = 1 →
      (∀ w, TArch w ∈ schwartzBruhatEigendistributions (infinitePlaceRestriction F w c) ∧
        TArch w (infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))) = 1) →
      (∀ v, TFin v ∈ schwartzBruhatEigendistributions (finitePlaceRestriction F v c) ∧
        TFin v (finiteStandardGaussian v (finitePlaceRestriction F v c)) = 1) →
      ∀ (f : ℬ(𝔸[F])) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
        (fFin : (v : V) → ℬ(v.adicCompletion F)),
        (∀ᶠ v in cofinite, fFin v = finiteStandardGaussian v (finitePlaceRestriction F v c)) →
        (∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
          (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
            ∏ᶠ v : V, fFin v (Multiplicative.ofAdd (x.2 v))) →
        T f = (∏ w : InfinitePlace F, TArch w (fArch w)) * ∏ᶠ v : V, TFin v (fFin v) := by sorry

-- Remark 3.4.3.4, p. 153. The tensor acts on the full test space by continuity.
-- The completed archimedean product uses `schwartzBruhat_kernel_equiv`; the finite
-- stages and their passage to the adeles use `sAdeleSchwartz_inductiveTensor_equiv`
-- and `sAdeleSchwartzToGlobal_finalTopology`.

end Gaussians

end RiemannMasullo
