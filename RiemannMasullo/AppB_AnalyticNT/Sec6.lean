module

public import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.ForMathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.EulerProduct.Basic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction

/-!
# Classical zero-free regions for Hecke L-functions

Masullo, §B.6, pp. 636–643. The finite Hecke L-function is represented by a
meromorphic continuation in normal form, as in §B.1.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "𝒳[" F "]" => HeckeCharacter (𝓞 F) F
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "atHeight" => comap (abs ∘ Complex.im) atTop
local notation "atAbsTop" => comap (abs : ℝ → ℝ) atTop

/-- Paper: Proposition B.6.1.1, p. 636. An absolute constant gives a
zero-free region for each finite Hecke L-function, with a scale depending on
the field and character. Meromorphic order distinguishes poles from zeros.
Deviation: The scale is chosen greater than `1/3` so the logarithm in the
denominator is positive at every height. It is an existential scale and may be
enlarged to exclude an exceptional zero. The separate real-zero clause is false. -/
theorem finiteHeckeL_zeroFreeRegion :
    ∃ A : ℝ, 0 < A ∧
      ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
        ∃ B : ℝ, 1 / 3 < B ∧
          ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
            (∀ s : halfPlane, L s = finiteHeckeL χ s) →
            ∀ s : ℂ, 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 *
              Real.log (B * (|s.im| + 3))) ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  sorry

-- TODO(paper-gap): The paragraph after (B.6.1.1) identifies two different conductors.
-- A pure imaginary norm twist preserves the finite conductor but changes the
-- archimedean parameter. No conductor-uniform exceptional-zero assertion is made here.
-- TODO(paper-gap): The real-zero clause of Proposition B.6.1.1 is false on [1/2, 1].
-- If ζ(1/2 + iγ) = 0 with γ ≠ 0, the nonquadratic norm character |·|^(iγ)
-- over ℚ has finite L-function ζ(s + iγ), which vanishes at the real point 1/2.
-- The square of this character has finite L-function ζ(s + 2iγ), with a pole.

/-- Paper: §B.6.1.2, p. 636. The value at a nonzero integral ideal is the
product of local uniformizer values with the ideal's prime exponents. At a
ramified prime the local value used in this product is zero.
Deviation: The value at the zero ideal is set to zero. -/
def heckeIdealValue (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  open Classical in
  if I = ⊥ then 0 else
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (if χ.IsUnramifiedAt v then χ.localValue v else 0) ^ multiplicity v.asIdeal I

open Classical in
/-- Paper: §B.6.1.2, p. 636. The value on a positive power of a prime ideal
is the corresponding power of the local value, or zero at a ramified prime. -/
theorem heckeIdealValue_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    {k : ℕ} (hk : 0 < k) :
    heckeIdealValue χ (v.asIdeal ^ k) =
      if χ.IsUnramifiedAt v then χ.localValue v ^ k else 0 := by
  have hne : v.asIdeal ^ k ≠ ⊥ := pow_ne_zero _ v.ne_bot
  unfold heckeIdealValue
  rw [ite_eq_right hne, finprod_eq_single _ v, multiplicity_pow_self_of_prime v.prime]
  · split_ifs <;> simp [hk.ne']
  · intro w hw
    rw [multiplicity_eq_zero_of_not_dvd fun hd ↦ hw (HeightOneSpectrum.eq_of_dvd_pow hd), pow_zero]

/-- Paper: Equation (B.6.1.2), p. 636. To the right of one, the series indexed
by nonzero integral ideals converges absolutely to the finite Hecke L-function. -/
theorem finiteHeckeL_hasSum_ideals (χ : U[F]) (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealValue (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ))
      (finiteHeckeL χ s) := by
  classical
  let a (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
    if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v else 0
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :=
    a v ^ multiplicity v.asIdeal I
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hzero : value 0 = 0 := by simp [value, heckeIdealValue]
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ 0) : value I = ∏ᶠ v, factor I v := by
    have hI' : I ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hI
    simp only [value, heckeIdealValue, ite_eq_right hI', factor, a]
  have hsupport (I : Ideal (𝓞 F)) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible
  let c : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := value
      map_zero' := hzero
      map_one' := by
        rw [hvalue one_ne_zero]
        exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp only [factor, multiplicity_one_right, pow_zero]
      map_mul' := by
        intro I J
        by_cases hI : I = 0
        · simp only [hI, zero_mul, hzero]
        by_cases hJ : J = 0
        · simp only [hJ, mul_zero, hzero]
        rw [hvalue (mul_ne_zero hI hJ), hvalue hI, hvalue hJ,
          ← finprod_mul_distrib (hsupport I) (hsupport J)]
        apply finprod_congr
        intro v
        simp only [factor, multiplicity_mul v.prime
          (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hcPrime (v : HeightOneSpectrum (𝓞 F)) : c v.asIdeal = a v := by
    change value v.asIdeal = _
    rw [hvalue v.prime.ne_zero, finprod_eq_single _ v]
    · simp only [factor, multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.prime.ne_zero),
        pow_one]
    · intro w hw
      simp only [factor, multiplicity_eq_zero_of_not_dvd (fun h ↦ hw (hd w v h)), pow_zero]
  have ha (v : HeightOneSpectrum (𝓞 F)) : ‖a v‖ ≤ 1 := by
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;>
      simp [a, h, norm_ideleClassNormTwist_zero_localValue]
  have hc (I : Ideal (𝓞 F)) : ‖c I‖ ≤ 1 := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      exact zero_le_one
    change ‖value I‖ ≤ 1
    rw [hvalue hI, finprod_eq_prod _ (hsupport I), norm_prod]
    exact Finset.prod_le_one₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ by
      simp only [factor, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (ha v)
  let term : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := fun I ↦ c I * ((I.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))
      map_zero' := by rw [map_zero c, zero_mul]
      map_one' := by rw [map_one c, map_one, Nat.cast_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
      map_mul' := by
        intro I J
        rw [map_mul c, map_mul, Nat.cast_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg I.absNorm) (Nat.cast_nonneg J.absNorm)]
        ring }
  have hr : 1 < (s : ℂ).re := s.property
  have hbound (I : Ideal (𝓞 F)) : ‖term I‖ ≤ (I.absNorm : ℝ) ^ (-(s : ℂ).re) := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      positivity
    have hN : (0 : ℝ) < I.absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (by simpa only [Ideal.zero_eq_bot] using hI))
    change ‖c I * ((I.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))‖ ≤ _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hN.le _) (hc I)
  have hsum : Summable (fun I ↦ ‖term I‖) :=
    (summable_absNorm_rpow F hr).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hprod := hasProd_eulerFactors_of_summable
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal) (fun v ↦ v.prime) hd
    (fun I hI h1 ↦ by
      obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using h1)
      exact ⟨⟨J, hJ.isPrime, fun h ↦ hI (le_bot_iff.mp (h ▸ hIJ))⟩, Ideal.dvd_iff_le.mpr hIJ⟩)
    term hsum (fun v ↦ by
      have hv : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hlt := (hbound v.asIdeal).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hv (by linarith : -(s : ℂ).re < 0))
      exact fun h ↦ (ne_of_lt hlt) (by rw [h, norm_one]))
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      finiteHeckeEulerFactor χ v s = (1 - term v.asIdeal)⁻¹ := by
    change _ = (1 - c v.asIdeal * ((v.asIdeal.absNorm : ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹
    rw [hcPrime, Complex.ofReal_natCast]
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, a, h]
  have hEq : (∑' I, term I) = finiteHeckeL χ s :=
    (hprod.congr_fun hlocal).unique (finiteHeckeL_hasProd χ s)
  have hsupport' : Function.support (term : Ideal (𝓞 F) → ℂ) ⊆ {I | I ≠ ⊥} := by
    intro I hI hBot
    exact hI ((show I = 0 by simpa only [Ideal.zero_eq_bot] using hBot) ▸ term.map_zero)
  refine ((hasSum_subtype_iff_of_support_subset hsupport').mpr
    (hEq ▸ hsum.of_norm.hasSum)).congr_fun fun I ↦ ?_
  change value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ) =
    value I.val * ((I.val.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))
  rw [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

/-- Paper: Equation (B.6.1.3), p. 636. The summatory function adds the values
at nonzero integral ideals of norm at most `x`. -/
def heckeIdealSummatory (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.3), p. 636. At `x = 1` only the unit ideal contributes. -/
theorem heckeIdealSummatory_one (χ : 𝒳[F]) : heckeIdealSummatory χ 1 = 1 := by
  have hmem : ∀ I : Ideal (𝓞 F), I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 1 ↔ I = ⊤ := fun I ↦ by
    constructor
    · rintro ⟨h0, h1⟩
      have h1' : Ideal.absNorm I ≤ 1 := by exact_mod_cast h1
      have h0' : Ideal.absNorm I ≠ 0 := fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)
      exact Ideal.absNorm_eq_one_iff.mp (by omega)
    · rintro rfl
      exact ⟨top_ne_bot, by simp⟩
  let : Unique {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 1} :=
    { default := ⟨⊤, (hmem ⊤).mpr rfl⟩
      uniq := fun I ↦ Subtype.ext ((hmem I.val).mp I.2) }
  unfold heckeIdealSummatory
  rw [finsum_unique]
  show heckeIdealValue χ ⊤ = 1
  unfold heckeIdealValue
  rw [ite_eq_right top_ne_bot]
  refine finprod_eq_one_of_forall_eq_one fun w ↦ ?_
  rw [← Ideal.one_eq_top, multiplicity_one_right, pow_zero]

/-- Paper: Equation (B.6.1.4), p. 636. The coefficient at `x` sums the
values at nonzero integral ideals of norm exactly `x`. The sum is zero if
there are no such ideals. -/
def heckeNormCoefficient (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.4), p. 636. At natural numbers the coefficients
agree with the coefficients of Mathlib's formal Euler product. -/
theorem heckeNormCoefficient_natCast (χ : 𝒳[F]) (m : ℕ) :
    heckeNormCoefficient χ (m : ℝ) = χ.LFunction m := by
  classical
  let a (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
    if χ.IsUnramifiedAt v then χ.localValue v else 0
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :=
    a v ^ multiplicity v.asIdeal I
  let value := heckeIdealValue χ
  have hzero : value 0 = 0 := by simp [value, heckeIdealValue]
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ 0) : value I = ∏ᶠ v, factor I v := by
    have hI' : I ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hI
    simp only [value, heckeIdealValue, ite_eq_right hI', factor, a]
  have hsupport (I : Ideal (𝓞 F)) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible
  let c : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := value
      map_zero' := hzero
      map_one' := by
        rw [hvalue one_ne_zero]
        exact finprod_eq_one_of_forall_eq_one fun v ↦ by
          simp only [factor, multiplicity_one_right, pow_zero]
      map_mul' := by
        intro I J
        by_cases hI : I = 0
        · simp only [hI, zero_mul, hzero]
        by_cases hJ : J = 0
        · simp only [hJ, mul_zero, hzero]
        rw [hvalue (mul_ne_zero hI hJ), hvalue hI, hvalue hJ,
          ← finprod_mul_distrib (hsupport I) (hsupport J)]
        apply finprod_congr
        intro v
        simp only [factor, multiplicity_mul v.prime
          (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hcPrime (v : HeightOneSpectrum (𝓞 F)) : c v.asIdeal = a v := by
    change value v.asIdeal = _
    rw [hvalue v.prime.ne_zero, finprod_eq_single _ v]
    · simp only [factor,
        multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.prime.ne_zero), pow_one]
    · intro w hw
      simp only [factor, multiplicity_eq_zero_of_not_dvd (fun h ↦ hw (hd w v h)), pow_zero]
  have hN (v : HeightOneSpectrum (𝓞 F)) : 1 < v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hE (v : HeightOneSpectrum (𝓞 F)) : χ.localEulerFactor v =
      ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm (PowerSeries.mk fun k ↦ a v ^ k) := by
    rw [HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
      hecke_localPowerSeries_eq_mk]
  have hEpow (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
      χ.localEulerFactor v (v.asIdeal.absNorm ^ k) = a v ^ k := by
    rw [hE, ArithmeticFunction.ofPowerSeries_apply_pow (hN v), PowerSeries.coeff_mk]
  have hEne (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (h : χ.localEulerFactor v d ≠ 0) :
      v.asIdeal.absNorm ^ Nat.log v.asIdeal.absNorm d = d := by
    by_contra hk
    apply h
    rw [hE, ArithmeticFunction.ofPowerSeries_apply (hN v), Function.extend_apply']
    · rfl
    rintro ⟨k, rfl⟩
    exact hk (by rw [Nat.log_pow (hN v)])
  let U (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) : Finset (Ideal (𝓞 F)) :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).toFinset.filter fun I ↦ ∀ v, v.asIdeal ∣ I → v ∈ S
  have hmemU {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} {I : Ideal (𝓞 F)} :
      I ∈ U S n ↔ I.absNorm = n ∧ ∀ v, v.asIdeal ∣ I → v ∈ S := by
    simp [U]
  have key (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
      (∏ v ∈ S, χ.localEulerFactor v) n = ∑ I ∈ U S n, c I := by
    induction S using Finset.induction_on generalizing n with
    | empty =>
      have hU (I : Ideal (𝓞 F)) (hI : I ∈ U ∅ n) : I = ⊥ ∨ I = ⊤ := by
        by_contra! h
        obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal h.2
        have hv := (hmemU.mp hI).2 ⟨J, hJ.isPrime, fun hJ0 ↦ h.1 (le_bot_iff.mp (hJ0 ▸ hIJ))⟩
          (Ideal.dvd_iff_le.mpr hIJ)
        simp at hv
      rw [Finset.prod_empty]
      by_cases hn : n = 1
      · subst hn
        rw [ArithmeticFunction.one_one,
          Finset.sum_eq_single_of_mem ⊤ (hmemU.mpr ⟨Ideal.absNorm_top, by
          intro v hv
          exact absurd (Ideal.dvd_iff_le.mp hv) (fun h ↦ v.isPrime.ne_top (top_le_iff.mp h))⟩)]
        · rw [← Ideal.one_eq_top, map_one]
        · intro I hI hIt
          rcases hU I hI with rfl | rfl
          · rw [← Ideal.zero_eq_bot, _root_.map_zero]
          · exact absurd rfl hIt
      · rw [ArithmeticFunction.one_apply_ne hn]
        refine (Finset.sum_eq_zero fun I hI ↦ ?_).symm
        rcases hU I hI with rfl | rfl
        · rw [← Ideal.zero_eq_bot, _root_.map_zero]
        · exact absurd ((hmemU.mp hI).1.symm.trans Ideal.absNorm_top) hn
    | insert w S hw ih =>
      have hw0 : w.asIdeal ≠ 0 := w.prime.ne_zero
      rw [Finset.prod_insert hw, ArithmeticFunction.mul_apply]
      simp_rw [ih, Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij_ne_zero
        (fun p _ _ ↦ w.asIdeal ^ Nat.log w.asIdeal.absNorm p.1.1 * p.2) ?_ ?_ ?_ ?_
      · rintro ⟨⟨d, e⟩, J⟩ hp hne
        rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU] at hp
        have hk := hEne w d (left_ne_zero_of_mul hne)
        refine hmemU.mpr ⟨?_, fun v hv ↦ ?_⟩
        · rw [map_mul, map_pow, hk, hp.2.1, hp.1.1]
        · rcases v.prime.dvd_or_dvd hv with h | h
          · exact Finset.mem_insert.mpr (Or.inl (hd v w (v.prime.dvd_of_dvd_pow h)))
          · exact Finset.mem_insert_of_mem (hp.2.2 v h)
      · have hmult (k : ℕ) (J : Ideal (𝓞 F)) (hJ : J ≠ 0) (hwJ : ¬ w.asIdeal ∣ J) :
            multiplicity w.asIdeal (w.asIdeal ^ k * J) = k := by
          rw [multiplicity_mul w.prime (FiniteMultiplicity.of_prime_left w.prime
            (mul_ne_zero (pow_ne_zero _ hw0) hJ)), multiplicity_pow_self_of_prime w.prime,
            multiplicity_eq_zero_of_not_dvd hwJ, add_zero]
        rintro ⟨⟨d, e⟩, J⟩ hp hne ⟨⟨d', e'⟩, J'⟩ hp' hne' heq
        rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU] at hp hp'
        have hJ : J ≠ 0 := fun h ↦ hne (by rw [h, _root_.map_zero, mul_zero])
        have hJ' : J' ≠ 0 := fun h ↦ hne' (by rw [h, _root_.map_zero, mul_zero])
        have hwJ : ¬ w.asIdeal ∣ J := fun h ↦ hw (hp.2.2 w h)
        have hwJ' : ¬ w.asIdeal ∣ J' := fun h ↦ hw (hp'.2.2 w h)
        dsimp only at heq
        have hkk := (hmult _ J hJ hwJ).symm.trans ((congrArg _ heq).trans (hmult _ J' hJ' hwJ'))
        have hJJ : J = J' := mul_left_cancel₀ (pow_ne_zero _ hw0) (hkk ▸ heq)
        have hdd : d = d' := by
          rw [← hEne w d (left_ne_zero_of_mul hne), ← hEne w d' (left_ne_zero_of_mul hne'), hkk]
        have hee : e = e' := hp.2.1.symm.trans (hJJ ▸ hp'.2.1)
        subst hJJ hdd hee
        rfl
      · intro I hI hcI
        rw [hmemU] at hI
        have hI0 : I ≠ 0 := fun h ↦ hcI (by rw [h, _root_.map_zero])
        obtain ⟨k, J, hwJ, rfl⟩ := WfDvdMonoid.max_power_factor hI0 w.irreducible
        refine ⟨⟨(w.asIdeal.absNorm ^ k, J.absNorm), J⟩, ?_, ?_, ?_⟩
        · rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU]
          refine ⟨⟨by rw [← hI.1, map_mul, map_pow], ?_⟩, rfl, fun v hv ↦ ?_⟩
          · rw [← hI.1, Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
            exact hI0
          · rcases Finset.mem_insert.mp (hI.2 v (dvd_mul_of_dvd_right hv _)) with rfl | h
            · exact absurd hv hwJ
            · exact h
        · rw [map_mul, map_pow, hcPrime] at hcI
          rwa [hEpow]
        · dsimp only
          rw [Nat.log_pow (hN w)]
      · rintro ⟨⟨d, e⟩, J⟩ hp hne
        dsimp only
        rw [map_mul, map_pow, hcPrime, ← hEpow, hEne w d (left_ne_zero_of_mul hne)]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [ArithmeticFunction.map_zero, heckeNormCoefficient]
    have : IsEmpty {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = ((0 : ℕ) : ℝ)} :=
      ⟨fun I ↦ I.2.1 (Ideal.absNorm_eq_zero_iff.mp (by exact_mod_cast I.2.2))⟩
    exact finsum_of_isEmpty _
  obtain ⟨S, hS, hSm⟩ := ((heckeLocalEulerFactor_eventually_prod_eq χ m).and
    (eventually_ge_atTop ((Ring.HasFiniteQuotients.finite_absNorm_le m).preimage
      HeightOneSpectrum.asIdeal_injective.injOn).toFinset)).exists
  rw [← hS, key S m]
  have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m} = ↑(U S m) := by
    ext I
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, hmemU]
    constructor
    · rintro ⟨-, hIm⟩
      have hIm' : I.absNorm = m := by exact_mod_cast hIm
      refine ⟨hIm', fun v hv ↦ hSm ?_⟩
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq, ← hIm']
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (hIm' ▸ hm)) (map_dvd Ideal.absNorm hv)
    · rintro ⟨hIm, -⟩
      exact ⟨fun h ↦ hm (by rw [← hIm, h, Ideal.absNorm_bot]), by exact_mod_cast hIm⟩
  change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m}, value I = _
  rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset]
  rfl

/-- Paper: Equation (B.6.1.5), p. 637. Grouping the terms by their integral
norm gives the absolutely convergent Dirichlet series with coefficients `aₘ`. -/
theorem finiteHeckeL_hasSum_normCoefficients (χ : U[F]) (s : halfPlane) :
    LSeriesHasSum (fun m : ℕ ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) (m : ℝ))
      (s : ℂ) (finiteHeckeL χ s) := by
  let normIndex (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℕ := I.val.absNorm
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hs : (s : ℂ) ≠ 0 := by
    intro h
    have hr : 1 < (s : ℂ).re := s.property
    norm_num [h] at hr
  refine ((finiteHeckeL_hasSum_ideals χ s).tsum_fiberwise normIndex).congr_fun ?_
  intro n
  symm
  rw [LSeries.term_of_ne_zero' hs]
  let normFiber : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ (I.absNorm : ℝ) = (n : ℝ)}
  let e : (normIndex ⁻¹' ({n} : Set ℕ) : Set {I : Ideal (𝓞 F) // I ≠ ⊥}) ≃ normFiber :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property,
        by exact_mod_cast (show I.val.val.absNorm = n from I.property)⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, by
        change I.val.absNorm = n
        exact_mod_cast I.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hnorm (I : normFiber) : I.val.absNorm = n := by exact_mod_cast I.property.2
  rw [← e.symm.tsum_eq]
  change (∑' I : normFiber, value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) =
    heckeNormCoefficient (ideleClassNormTwist χ 0) (n : ℝ) / (n : ℂ) ^ (s : ℂ)
  let : Finite normFiber :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
      (show normFiber ⊆ {I | I.absNorm = n} from fun I hI ↦ hnorm ⟨I, hI⟩)).to_subtype
  simp_rw [hnorm, tsum_div_const, tsum_eq_finsum (Set.toFinite _)]
  rfl

/-- Paper: Equation (B.6.1.6), p. 637. For each positive `ε`, the summatory
function is bounded by a constant times `x^(1 + ε)`, uniformly in unitary characters. -/
theorem heckeIdealSummatory_bound (F : Type*) [Field F] [NumberField F] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ χ : U[F],
      ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ C * x ^ (1 + ε) := by
  classical
  have hvalue (χ : U[F]) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    rw [heckeIdealValue, ite_eq_right hI]
    refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp) (fun _ w hz hw ↦ ?_) (fun v ↦ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg w) hz).trans hw
    · rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      split_ifs <;> simp [norm_ideleClassNormTwist_zero_localValue]
  obtain ⟨B, hB⟩ := (NumberField.Ideal.tendsto_norm_le_div_atTop F).isBoundedUnder_le.eventually_le
  have hC : 0 < max 1 B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨max 1 B, hC, ?_⟩
  filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with x hcount hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let ideals := {I : Ideal (𝓞 F) | (I.absNorm : ℝ) ≤ x}
  let nonzeroIdeals := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}
  have hfinite : ideals.Finite := by
    simp only [ideals, ← Nat.le_floor_iff hxpos.le]
    exact Ring.HasFiniteQuotients.finite_absNorm_le _
  have hsub : nonzeroIdeals ⊆ ideals := fun _ hI ↦ hI.2
  let : Fintype nonzeroIdeals := (hfinite.subset hsub).fintype
  intro χ
  calc
    ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ ∑ _ : nonzeroIdeals, (1 : ℝ) := by
      change ‖∑ᶠ I : nonzeroIdeals, heckeIdealValue (ideleClassNormTwist χ 0) I.1‖ ≤ _
      rw [finsum_eq_sum_of_fintype]
      exact norm_sum_le_of_le _ fun I _ ↦ hvalue χ I.2.1
    _ = (nonzeroIdeals.ncard : ℝ) := by simp
    _ ≤ (ideals.ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hfinite
    _ ≤ max 1 B * x := (div_le_iff₀ hxpos).mp (hcount.trans (le_max_right 1 B))
    _ ≤ max 1 B * x ^ (1 + ε) := mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_one_le hx (le_add_of_nonneg_right hε.le)) hC.le

-- TODO(paper-gap): Equation (B.6.1.7) multiplies the norm-one class volume by an
-- extra inverse square root of the discriminant under the normalization in §A.3.

/-- A unitary character trivial on the norm-one subgroup is a unique imaginary power of
the norm. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_existsUnique (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let c : NNRealˣ →ₜ* ℂ := (ideleClassNormTwist χ 0).comp ⟨σ, hσ⟩
  have hunit (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist χ 0 g = (χ g : ℂ) := by
    change (χ g : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ :=
    existsUnique_unitaryComplexPower c (fun u ↦ by
      change ‖ideleClassNormTwist χ 0 (σ u)‖ = 1
      rw [hunit, Circle.norm_coe])
  have hparam : -Complex.I * ((-z.im : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzre]
  refine ⟨-z.im, ?_, ?_⟩
  · change ideleClassNormTwist χ 0 =
      ideleClassNormTwist (1 : U[F]) (-Complex.I * ((-z.im : ℝ) : ℂ))
    rw [hparam]
    ext1 g
    let u := ideleClassNorm F g
    have hk : g / σ u ∈ (ideleClassNorm F).ker := MonoidHom.mem_ker.mpr (by
      rw [map_div, hnorm u, div_self'])
    have hkχ : χ (g / σ u) = 1 :=
      DFunLike.congr_fun hχ (⟨g / σ u, hk⟩ : (ideleClassNorm F).ker)
    have he : ideleClassNormTwist χ 0 (g / σ u) = 1 := by rw [hunit, hkχ, Circle.coe_one]
    calc
      ideleClassNormTwist χ 0 g = ideleClassNormTwist χ 0 (g / σ u) * c u := by
        change ideleClassNormTwist χ 0 g =
          ideleClassNormTwist χ 0 (g / σ u) * ideleClassNormTwist χ 0 (σ u)
        rw [← map_mul, div_mul_cancel]
      _ = ideleClassNormTwist (1 : U[F]) z g := by
        change ideleClassNormTwist χ 0 (g / σ u) * c u =
          1 * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ z
        rw [he, hz u]
  · intro t ht
    have he : -Complex.I * (t : ℂ) = z := huniq _ ⟨by simp [Complex.mul_re], fun u ↦ by
      change ideleClassNormTwist χ 0 (σ u) = _
      rw [ht]
      change (1 : ℂ) * (((ideleClassNorm F (σ u) : NNReal) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) = _
      rw [one_mul, hnorm u]⟩
    apply neg_eq_iff_eq_neg.mp
    simpa [Complex.mul_im] using congrArg Complex.im he

/-- Undoing the imaginary norm twist of such a character gives the trivial character. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_eq_one (χ : U[F]) (t₀ : ℝ)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist χ (Complex.I * t₀) g = 1 := by
  have h := DFunLike.congr_fun ht g
  change (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (0 : ℂ) =
    1 * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (-Complex.I * t₀) at h
  change (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (Complex.I * t₀) = 1
  have hne : (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ideleClassNorm F g).ne_zero
  rw [Complex.cpow_zero, mul_one, one_mul] at h
  rw [h, ← Complex.cpow_add _ _ hne, neg_mul, neg_add_cancel, Complex.cpow_zero]

/-- A character that is identically one has value one at every nonzero ideal. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_value (χ : 𝒳[F])
    (hχ : ∀ g, χ g = 1) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : heckeIdealValue χ I = 1 := by
  classical
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      χ.restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hχ, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F), χ.IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), χ.localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- Paper: Lemma B.6.1.2(1), p. 637. For a unitary character trivial on
norm-one classes, undoing its imaginary norm twist gives the ideal-counting
limit at the residue of Dedekind zeta.
Deviation: Uses Mathlib's `dedekindZeta_residue`, the class volume in §A.3,
with the extra printed inverse square root of the discriminant removed. -/
theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    (∃! t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) ∧
      ∀ t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
        Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
          atTop (𝓝 (dedekindZeta_residue F : ℂ)) := by
  refine ⟨heckeIdealSummatory_tendsto_of_trivial_on_normOne_existsUnique χ hχ, fun t₀ ht ↦ ?_⟩
  have hval {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      heckeIdealValue (ideleClassNormTwist χ (Complex.I * t₀)) I = 1 :=
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_value _
      (heckeIdealSummatory_tendsto_of_trivial_on_normOne_eq_one χ t₀ ht) hI
  have hlim := (Complex.continuous_ofReal.tendsto _).comp (Ideal.tendsto_norm_le_div_atTop₀ F)
  rw [← dedekindZeta_residue_def] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  let e : {I : nonZeroDivisors (Ideal (𝓞 F)) // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x} ≃
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} :=
    { toFun := fun I ↦ ⟨I.1.1, by simpa using mem_nonZeroDivisors_iff_ne_zero.mp I.1.2, I.2⟩
      invFun := fun I ↦ ⟨⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using I.2.1)⟩, I.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} := Fintype.ofFinite _
  unfold heckeIdealSummatory
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun I _ ↦ hval I.2.1, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Paper: Lemma B.6.1.2(2), p. 637. If the character is nontrivial on norm-one
classes, its summatory function divided by `x` tends to zero. -/
theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ 0) x / x) atTop (𝓝 0) := by
  sorry

/-- Paper: Theorem B.6.1.3, p. 637. The logarithmic derivative is bounded by
a squared logarithm for large absolute heights, uniformly over the narrower
region defined by `α * η`. The Dedekind zeta continuation is the one for the
trivial character. For fixed field, character and `α`, the implied constant
works for every admissible width. Its height threshold may depend on the width.
Deviation: The width is represented by a real function restricted to `t ≥ 0`.
Decreasing is expressed as nonincreasing, and the logarithm uses absolute height.
Eventual analyticity and nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree (χ : U[F]) (L Z : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hZ : MeromorphicNFOn Z univ) (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hα : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ → ℝ,
      MapsTo η (Ici 0) (Ioc 0 (1 / 2)) →
      DifferentiableOn ℝ η (Ici 0) → AntitoneOn η (Ici 0) →
      Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0) →
      ((fun t ↦ (η t)⁻¹) =O[atTop] Real.log) →
      (∀ s : ℂ, 1 - η |s.im| < s.re → meromorphicOrderAt L s ≤ 0) →
      let l := atHeight ⊓ 𝓟 {s : ℂ | 1 - α * η |s.im| ≤ s.re}
      (∀ᶠ s in l, AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
        Asymptotics.IsBigOWith C l (logDeriv L) (fun s ↦ (Real.log |s.im|) ^ 2) := by
  sorry

/-- Paper: Equation (B.6.1.13), p. 638. The ideal von Mangoldt function is
`log (N p)` on positive powers of a nonzero prime ideal `p` and zero elsewhere. -/
def idealVonMangoldt (I : Ideal (𝓞 F)) : ℝ :=
  open Classical in
  if h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k then
    Real.log (h.choose.asIdeal.absNorm : ℝ)
  else 0

/-- Paper: Equation (B.6.1.13), p. 638. The value at a positive prime-ideal
power is the logarithm of the prime's norm, independently of the exponent. -/
theorem idealVonMangoldt_prime_pow (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (hk : 0 < k) :
    idealVonMangoldt (v.asIdeal ^ k) = Real.log (v.asIdeal.absNorm : ℝ) := by
  have h : ∃ w : HeightOneSpectrum (𝓞 F), ∃ j : ℕ, 0 < j ∧ v.asIdeal ^ k = w.asIdeal ^ j :=
    ⟨v, k, hk, rfl⟩
  unfold idealVonMangoldt
  split_ifs with h'
  · obtain ⟨hj, hw⟩ := h'.choose_spec.choose_spec
    rw [HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ hj.ne').trans hw.symm.dvd)]
  · exact absurd h h'

/-- Paper: §B.6.1.2, p. 638. The twisted von Mangoldt value is the product
of the ideal character value and the ideal von Mangoldt weight. -/
def heckeIdealVonMangoldt (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  heckeIdealValue χ I * (idealVonMangoldt I : ℂ)

/-- Paper: §B.6.1.2, p. 638. At a positive power of an unramified prime, the
twisted weight is the character power times the logarithm of the prime norm. -/
theorem heckeIdealVonMangoldt_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    (hv : χ.IsUnramifiedAt v) {k : ℕ} (hk : 0 < k) :
    heckeIdealVonMangoldt χ (v.asIdeal ^ k) =
      χ.localValue v ^ k * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
  classical
  rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow χ v hk, ite_eq_left hv,
    idealVonMangoldt_prime_pow v hk]

/-- A positive prime power has twisted weight of norm at most the logarithm of its norm.
The weight vanishes on all other ideals. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_weight (χ : U[F])
    (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ Real.log I.absNorm := by
  classical
  by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    have hq : (1 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
    rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hq), map_pow, Nat.cast_pow]
    split_ifs <;> simp only [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul,
      norm_zero, zero_mul]
    · exact Real.log_le_log (zero_lt_one.trans_le hq) (le_self_pow₀ hq hk.ne')
    · exact Real.log_nonneg (one_le_pow₀ hq)
  · simp [heckeIdealVonMangoldt, idealVonMangoldt, h, Real.log_natCast_nonneg]

/-- The logarithmic weight is absorbed by the difference between two exponents greater than one. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_summable (χ : U[F]) (s : halfPlane) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) := by
  obtain ⟨r, hr, hrs⟩ := exists_between (show 1 < (s : ℂ).re from s.property)
  let ε := (s : ℂ).re - r
  have hε : 0 < ε := sub_pos.mpr hrs
  have hs := ((summable_absNorm_rpow F hr).subtype (fun I ↦ I ≠ ⊥)).div_const ε
  apply hs.of_norm_bounded
  intro I
  let q : ℝ := I.val.absNorm
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  change ‖-heckeIdealVonMangoldt _ I.val / (q : ℂ) ^ (s : ℂ)‖ ≤ q ^ (-r) / ε
  rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  calc
    _ ≤ (q ^ ε / ε) / q ^ (s : ℂ).re := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hq.le _)
      exact (finiteHeckeL_logDeriv_hasSum_ideals_weight χ I.val).trans
        (Real.log_le_rpow_div hq.le hε)
    _ = q ^ (-r) / ε := by
      rw [div_right_comm, ← Real.rpow_sub hq]
      congr 2
      dsimp [ε]
      ring

/-- At one finite place, the logarithmic derivative sums the weights of its positive powers. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_local (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) (s : halfPlane) :
    DifferentiableAt ℂ (finiteHeckeEulerFactor χ v) s ∧ finiteHeckeEulerFactor χ v s ≠ 0 ∧
      HasSum (fun k : ℕ ↦ -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
        ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ (s : ℂ)) (logDeriv (finiteHeckeEulerFactor χ v) s) := by
  classical
  let ψ := ideleClassNormTwist χ 0
  let a := if ψ.IsUnramifiedAt v then ψ.localValue v else 0
  let q := v.asIdeal.absNorm
  let z (w : ℂ) := a * (q : ℂ) ^ (-w)
  have hq : (1 : ℝ) < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have ha : ‖a‖ ≤ 1 := by
    by_cases h : ψ.IsUnramifiedAt v <;> simp [a, h, ψ, norm_ideleClassNormTwist_zero_localValue]
  have hz : ‖z s‖ < 1 := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-(s : ℂ))‖ < 1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr (zero_lt_one.trans s.property)))
  have hden : 1 - z s ≠ 0 := fun h ↦ hz.ne (by rw [← sub_eq_zero.mp h, norm_one])
  have hfactor : finiteHeckeEulerFactor χ v = fun w ↦ (1 - z w)⁻¹ := by
    funext w
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;>
      simp [finiteHeckeEulerFactor, z, a, q, ψ, h]
  rw [hfactor]
  have dz := ((hasDerivAt_id (s : ℂ)).neg.const_cpow (Or.inl hq₀)).const_mul a
  change HasDerivAt z _ (s : ℂ) at dz
  have df := (dz.const_sub 1).inv hden
  change HasDerivAt (fun w ↦ (1 - z w)⁻¹) _ (s : ℂ) at df
  refine ⟨df.differentiableAt, inv_ne_zero hden, ?_⟩
  have hlog : logDeriv (fun w ↦ (1 - z w)⁻¹) s =
      (-Complex.log q * z s) * (1 - z s)⁻¹ := by
    rw [logDeriv_apply, df.deriv]
    change _ / (1 - z s)⁻¹ = _
    field_simp [hden]
    dsimp [z]
    ring
  rw [hlog]
  apply ((hasSum_geometric_of_norm_lt_one hz).mul_left (-Complex.log q * z s)).congr_fun
  intro k
  have hv : heckeIdealValue ψ (v.asIdeal ^ (k + 1)) = a ^ (k + 1) := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k)]
    by_cases h : ψ.IsUnramifiedAt v <;> simp [a, h]
  rw [heckeIdealVonMangoldt, hv, idealVonMangoldt_prime_pow v (Nat.succ_pos k),
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
    Complex.natCast_log]
  change -(a ^ (k + 1) * Complex.log q) / ((q : ℂ) ^ (s : ℂ)) ^ (k + 1) =
    (-Complex.log q * z s) * z s ^ k
  rw [mul_assoc (-Complex.log q), ← pow_succ',
    show z s = a * ((q : ℂ) ^ (s : ℂ))⁻¹ by simp [z, Complex.cpow_neg],
    mul_pow, inv_pow, div_eq_mul_inv]
  ring

/-- On the right half-plane, the logarithmic derivatives of the local Euler factors sum
to the logarithmic derivative of the continuation. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_places (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (s : halfPlane) :
    L s ≠ 0 ∧ HasSum (fun v ↦ logDeriv (finiteHeckeEulerFactor χ v) s) (logDeriv L s) := by
  have hlocal := finiteHeckeL_logDeriv_hasSum_ideals_local χ
  have hn : L s ≠ 0 := by
    rw [hSeries s]
    exact finiteHeckeL_ne_zero_of_one_lt_re χ s
  refine ⟨hn, ?_⟩
  obtain ⟨r, hr, hrs⟩ := exists_between (show 1 < (s : ℂ).re from s.property)
  let D := Complex.re ⁻¹' Ioi r
  have hD : IsOpen D := isOpen_Ioi.preimage Complex.continuous_re
  have hconv := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ hr).mono
    (show D ⊆ {w : ℂ | r ≤ w.re} from fun w (hw : r < w.re) ↦ show r ≤ w.re from hw.le)
  have hconvL := hconv.congr_right
    (show EqOn _ L D from fun w hw ↦ (hSeries ⟨w, hr.trans hw⟩).symm)
  have hd (v : HeightOneSpectrum (𝓞 F)) : DifferentiableOn ℂ (finiteHeckeEulerFactor χ v) D :=
    fun w hw ↦ (hlocal v ⟨w, hr.trans hw⟩).1.differentiableWithinAt
  apply (Complex.logDeriv_tendsto hD hrs hconvL.tendstoLocallyUniformlyOn
    (.of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun v _ ↦ hd v) hn).congr
  intro S
  exact logDeriv_fun_prod (fun v _ ↦ (hlocal v s).2.1) (fun v _ ↦ (hlocal v s).1)

/-- Paper: Equation (B.6.1.12), p. 638. To the right of one, the negative of
the Dirichlet series weighted by the ideal von Mangoldt function converges
absolutely to the logarithmic derivative of the finite Hecke L-function. -/
theorem finiteHeckeL_logDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    AnalyticAt ℂ L (s : ℂ) ∧ L s ≠ 0 ∧
      HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
        -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
          (I.val.absNorm : ℂ) ^ (s : ℂ)) (logDeriv L s) := by
  obtain ⟨hne, hplaces⟩ := finiteHeckeL_logDeriv_hasSum_ideals_places χ L hSeries s
  have hNF := hL (mem_univ (s : ℂ))
  refine ⟨hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hNF.meromorphicOrderAt_eq_zero_iff.mpr hne).ge, hne, ?_⟩
  let P (p : HeightOneSpectrum (𝓞 F) × ℕ) : {I : Ideal (𝓞 F) // I ≠ ⊥} :=
    ⟨p.1.asIdeal ^ (p.2 + 1), pow_ne_zero _ p.1.ne_bot⟩
  have hP : Injective P := by
    rintro ⟨v, k⟩ ⟨w, j⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq))
  let f (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :=
    -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)
  have hout (I) (hI : I ∉ range P) : f I = 0 := by
    have h : ¬ ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, he⟩
      · exact hk.false
      · exact hI ⟨(v, k), Subtype.ext he.symm⟩
    simp [f, heckeIdealVonMangoldt, idealVonMangoldt, h]
  have hsum : Summable (f ∘ P) :=
    (finiteHeckeL_logDeriv_hasSum_ideals_summable χ s).comp_injective hP
  have hvalue := hsum.hasSum.prod_fiberwise fun v ↦
    (finiteHeckeL_logDeriv_hasSum_ideals_local χ v s).2.2
  exact (hP.hasSum_iff hout).mp (hvalue.unique hplaces ▸ hsum.hasSum)

/-- Paper: Equation (B.6.1.14), p. 638. The coefficient `Aₘ` sums the
character-weighted von Mangoldt values over nonzero ideals of norm `m`.
Deviation: The empty sum at `m = 0` is also defined. -/
def heckeLogDerivCoefficient (χ : 𝒳[F]) (m : ℕ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, heckeIdealVonMangoldt χ I.val

/-- Over `ℚ`, the ideal von Mangoldt function at the ideal generated by `n` is `Λ n`. -/
private theorem idealVonMangoldt_ratSpan (n : ℕ) :
    idealVonMangoldt (Ideal.span {(n : 𝓞 ℚ)}) = ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      { asIdeal := Ideal.span {(p : 𝓞 ℚ)}
        isPrime := (Ideal.span_singleton_prime (RatRingOfIntegers.natCast_ne_zero hp.ne_zero)).mpr
          (RatRingOfIntegers.prime_natCast_iff.mpr hp)
        ne_bot := by
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact RatRingOfIntegers.natCast_ne_zero hp.ne_zero }
    have hv : Ideal.span {((p ^ k : ℕ) : 𝓞 ℚ)} = v.asIdeal ^ k := by
      simp [v, Ideal.span_singleton_pow]
    rw [hv, idealVonMangoldt_prime_pow v hk, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    show Real.log ((Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) : ℕ) : ℝ) = _
    rw [RatRingOfIntegers.absNorm_span_natCast]
  · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right hn, idealVonMangoldt, dite_eq_right]
    rintro ⟨v, k, hk, hvk⟩
    apply hn
    obtain ⟨p, hp⟩ := RatRingOfIntegers.exists_eq_span_natCast v.asIdeal
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact v.ne_bot (by simpa using hp)
    have hprime : Nat.Prime p := RatRingOfIntegers.prime_natCast_iff.mp
      ((Ideal.span_singleton_prime (RatRingOfIntegers.natCast_ne_zero hp0)).mp (hp ▸ v.isPrime))
    have hpow : Ideal.span {(n : 𝓞 ℚ)} = Ideal.span {((p ^ k : ℕ) : 𝓞 ℚ)} := by
      rw [hvk, hp, Ideal.span_singleton_pow]
      simp
    have := congrArg Ideal.absNorm hpow
    rw [RatRingOfIntegers.absNorm_span_natCast, RatRingOfIntegers.absNorm_span_natCast] at this
    exact this ▸ (isPrimePow_nat_iff _).mpr ⟨p, k, hprime, hk, rfl⟩

/-- A character that is identically one has value one at every nonzero ideal. -/
private theorem heckeIdealValue_of_forall_eq_one (χ : 𝒳[F]) (hχ : ∀ g, χ g = 1)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : heckeIdealValue χ I = 1 := by
  classical
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      χ.restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hχ, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F), χ.IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), χ.localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- Paper: Equation (B.6.1.14), p. 638. Over the rationals with trivial
character these coefficients recover the classical von Mangoldt function. -/
theorem heckeLogDerivCoefficient_trivial_rat (m : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[ℚ]) 0) m =
      (ArithmeticFunction.vonMangoldt m : ℂ) := by
  have hχ : ∀ g, ideleClassNormTwist (1 : U[ℚ]) 0 g = 1 := fun g ↦ by
    simp only [ideleClassNormTwist, Complex.cpow_zero]
    change ((1 : U[ℚ]) g : ℂ) * 1 = 1
    simp
  unfold heckeLogDerivCoefficient
  rcases eq_or_ne m 0 with rfl | hm
  · have : IsEmpty {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = 0} :=
      ⟨fun I ↦ I.2.1 (Ideal.absNorm_eq_zero_iff.mp I.2.2)⟩
    rw [finsum_of_isEmpty]
    simp
  · have hmem : ∀ I : Ideal (𝓞 ℚ), I ≠ ⊥ ∧ I.absNorm = m ↔ I = Ideal.span {(m : 𝓞 ℚ)} :=
      fun I ↦ by
        constructor
        · rintro ⟨-, h⟩
          obtain ⟨n, rfl⟩ := RatRingOfIntegers.exists_eq_span_natCast I
          rw [RatRingOfIntegers.absNorm_span_natCast] at h
          rw [h]
        · rintro rfl
          refine ⟨?_, RatRingOfIntegers.absNorm_span_natCast m⟩
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact RatRingOfIntegers.natCast_ne_zero hm
    let : Unique {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = m} :=
      { default := ⟨_, (hmem _).mpr rfl⟩
        uniq := fun I ↦ Subtype.ext ((hmem I.val).mp I.2) }
    rw [finsum_unique]
    show heckeIdealVonMangoldt _ (Ideal.span {(m : 𝓞 ℚ)}) = _
    rw [heckeIdealVonMangoldt, heckeIdealValue_of_forall_eq_one _ hχ ((hmem _).mpr rfl).1,
      idealVonMangoldt_ratSpan, one_mul]

/-- A unitary character twisted by the trivial norm power has values of norm at most one,
so the twisted von Mangoldt weight is bounded by the ideal von Mangoldt weight. -/
private theorem heckeLogDerivCoefficient_bound_norm_le (χ : U[F]) (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ idealVonMangoldt I := by
  classical
  have hΛ : 0 ≤ idealVonMangoldt I := by
    unfold idealVonMangoldt
    split_ifs
    exacts [Real.log_natCast_nonneg _, le_rfl]
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    unfold heckeIdealValue
    split_ifs
    · simp
    · refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp)
        (fun x y hx hy ↦ (norm_mul_le x y).trans (by nlinarith [norm_nonneg x, norm_nonneg y]))
        fun v ↦ ?_
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      split_ifs
      · exact (norm_ideleClassNormTwist_zero_localValue χ v).le
      · simp
  rw [heckeIdealVonMangoldt, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ]
  exact mul_le_of_le_one_left hΛ hval

/-- A nonzero prime ideal lies over a rational prime `q`, and its norm is a positive
power of `q`. -/
private theorem heckeLogDerivCoefficient_bound_liesOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ q f : ℕ, q.Prime ∧ 0 < f ∧ v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      v.asIdeal.absNorm = q ^ f := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set q := Ideal.absNorm (v.asIdeal.under ℤ)
  have hl : v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := Int.liesOver_span_absNorm _
  refine ⟨q, v.asIdeal.inertiaDeg ℤ, Nat.absNorm_under_prime v.asIdeal,
    Ideal.inertiaDeg_pos _ _, hl, ?_⟩
  rw [← Ideal.natAbs_pow_inertiaDeg (q : ℤ) v.asIdeal, Int.natAbs_natCast]

/-- At most `[F : ℚ]` positive prime-ideal powers have a given norm `m ≥ 2`, and each
has von Mangoldt weight at most `log m`. -/
private theorem heckeLogDerivCoefficient_bound_finsum_le {m : ℕ} (hm : 2 ≤ m) :
    ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, idealVonMangoldt I.val ≤
      Module.finrank ℚ F * Real.log m := by
  classical
  set p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := Fintype.ofFinite _
  have : Fintype (P.primesOver (𝓞 F)) := (primesOver_finite P (𝓞 F)).fintype
  -- The ideals with nonzero weight are positive powers of primes over `p`.
  have hpow : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, idealVonMangoldt I.val ≠ 0 →
      ∃ v : HeightOneSpectrum (𝓞 F), ∃ k, 0 < k ∧ I.val = v.asIdeal ^ k := by
    intro I hI
    by_contra h
    exact hI (by rw [idealVonMangoldt, dite_eq_right_iff.mpr fun h' ↦ absurd h' h])
  have hover : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), 0 < k →
      (v.asIdeal ^ k).absNorm = m → v.asIdeal ∈ P.primesOver (𝓞 F) := by
    intro v k hk hvk
    obtain ⟨q, f, hq, hf, hlies, hnorm⟩ := heckeLogDerivCoefficient_bound_liesOver v
    rw [map_pow, hnorm, ← pow_mul] at hvk
    have hqp : q = p := by
      have h : m.minFac = q := by rw [← hvk, hq.pow_minFac (Nat.mul_ne_zero hf.ne' hk.ne')]
      exact h.symm
    subst hqp
    exact ⟨v.isPrime, hlies⟩
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), 0 < k →
      (v.asIdeal ^ k).absNorm = m → Real.log (v.asIdeal.absNorm : ℝ) ≤ Real.log m := by
    intro v k hk hvk
    have h0 : 0 < v.asIdeal.absNorm :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    refine Real.log_le_log (by exact_mod_cast h0) ?_
    rw [← hvk, map_pow]
    exact_mod_cast Nat.le_self_pow hk.ne' _
  -- Weighted ideals inject into the primes over `p` through their radicals.
  set s := Finset.univ.filter fun I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} ↦
    idealVonMangoldt I.val ≠ 0
  have hrad : ∀ I ∈ s, ∃ v : HeightOneSpectrum (𝓞 F), ∃ k, 0 < k ∧ I.val = v.asIdeal ^ k ∧
      I.val.radical = v.asIdeal := by
    intro I hI
    obtain ⟨v, k, hk, hI'⟩ := hpow I (Finset.mem_filter.mp hI).2
    exact ⟨v, k, hk, hI', by rw [hI', Ideal.radical_pow v.asIdeal hk.ne', v.isPrime.radical]⟩
  have hcard : s.card ≤ Fintype.card (P.primesOver (𝓞 F)) := by
    rw [← Fintype.card_coe s]
    refine Fintype.card_le_of_injective (fun I ↦ ⟨I.1.1.radical, ?_⟩) ?_
    · obtain ⟨v, k, hk, hI, hr⟩ := hrad I.1 I.2
      rw [hr]
      exact hover v k hk (hI ▸ I.1.2.2)
    · rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ
      obtain ⟨v, k, hk, hI', hrI⟩ := hrad I hI
      obtain ⟨w, j, hj, hJ', hrJ⟩ := hrad J hJ
      have hvw : v.asIdeal = w.asIdeal := by
        have := congrArg Subtype.val hIJ
        simp only at this
        rw [← hrI, ← hrJ, this]
      have h2 : 2 ≤ v.asIdeal.absNorm := by
        have h0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
        have h1 : v.asIdeal.absNorm ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]
          exact v.isPrime.ne_top
        omega
      have hkj : k = j := by
        have hI2 := I.2.2
        have hJ2 := J.2.2
        rw [hI', map_pow] at hI2
        rw [hJ', ← hvw, map_pow] at hJ2
        exact Nat.pow_right_injective h2 (hI2.trans hJ2.symm)
      have : I = J := Subtype.ext (by rw [hI', hJ', hvw, hkj])
      subst this
      rfl
  have hprimes : Fintype.card (P.primesOver (𝓞 F)) ≤ Module.finrank ℚ F := by
    rw [← RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank P (𝓞 F),
      Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver P := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter_ne_zero]
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  calc ∑ I ∈ s, idealVonMangoldt I.val ≤ ∑ _I ∈ s, Real.log m := by
        refine Finset.sum_le_sum fun I hI ↦ ?_
        obtain ⟨v, k, hk, hI', -⟩ := hrad I hI
        rw [hI', idealVonMangoldt_prime_pow v hk]
        exact hle v k hk (hI' ▸ I.2.2)
    _ = s.card * Real.log m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Module.finrank ℚ F * Real.log m := by
        gcongr
        exact_mod_cast hcard.trans hprimes

/-- Paper: Lemma B.6.1.4, p. 638. The logarithmic-derivative coefficients are
bounded by a constant times `log m`, with the constant depending only on the field degree. -/
theorem heckeLogDerivCoefficient_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [NumberField F], Module.finrank ℚ F = d →
        ∀ᶠ m : ℕ in atTop, ∀ χ : U[F],
          ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖ ≤ C * Real.log (m : ℝ) := by
  refine ⟨d + 1, by positivity, fun F _ _ hd ↦ ?_⟩
  subst hd
  filter_upwards [eventually_ge_atTop 2] with m hm χ
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := Fintype.ofFinite _
  have hsum := heckeLogDerivCoefficient_bound_finsum_le (F := F) hm
  rw [finsum_eq_sum_of_fintype] at hsum
  unfold heckeLogDerivCoefficient
  rw [finsum_eq_sum_of_fintype]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun I _ ↦
    heckeLogDerivCoefficient_bound_norm_le χ I.val).trans (hsum.trans ?_))
  gcongr
  linarith

-- TODO(paper-gap): In (B.6.1.16) a pure norm twist can have a pole in Ω.
-- Restrict the logarithm to heights above the pole. After (B.6.1.19) the
-- summand must retain the power m in N(p)^(m * (1 + αη(T))).
-- TODO(paper-gap): Substituting the radii from (B.6.1.18) into the first
-- coefficient in (B.6.1.20) gives 4(1 + 3α) / ((1 - α)^2 η(T)).

/-- Paper: Corollary B.6.1.5, p. 639. On the line `Re(s) = 1`, the logarithmic
derivative is bounded by a squared logarithm as the absolute height grows.
Deviation: The logarithm uses absolute height. Eventual analyticity and
nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      (fun t : ℝ ↦ logDeriv L ⟨1, t⟩) =O[atAbsTop] (fun t ↦ (Real.log |t|) ^ 2) := by
  sorry

open Complex in
/-- The inequality for the three Euler factors with a common radius and a unit phase. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_one_le_norm_eulerFactor_product {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - (r : ℂ) * z)⁻¹ ^ 4 *
      (1 - (r : ℂ) * z ^ 2)⁻¹‖ := by
  have h₀ : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hr]; exact hr₁
  have h₁ : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hz] using h₀
  have h₂ : ‖(r : ℂ) * z ^ 2‖ < 1 := by simpa [norm_mul, norm_pow, hz] using h₀
  have hinv {w : ℂ} (hw : ‖w‖ < 1) : (1 - w)⁻¹ = exp (-log (1 - w)) := by
    rw [exp_neg, exp_log (fun h ↦ hw.ne (by rw [← sub_eq_zero.mp h, norm_one]))]
  rw [hinv h₀, hinv h₁, hinv h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add,
    norm_exp, Real.one_le_exp_iff]
  simp only [add_re, mul_re, re_ofNat, im_ofNat, Nat.cast_ofNat, zero_mul, sub_zero]
  rw [← ((hasSum_re (hasSum_taylorSeries_neg_log h₀)).mul_left 3 |>.add
    ((hasSum_re (hasSum_taylorSeries_neg_log h₁)).mul_left 4) |>.add
    (hasSum_re (hasSum_taylorSeries_neg_log h₂))).tsum_eq]
  apply tsum_nonneg
  intro n
  simp only [mul_pow, ← ofReal_pow, div_natCast_re, ofReal_re, mul_re, ofReal_im, zero_mul,
    sub_zero, ← mul_div_assoc, ← add_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hnorm : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have him := sq_norm_sub_sq_re (z ^ n)
  rw [hnorm, one_pow] at him
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, pow_two (z ^ n), mul_re]
  have hident :
      3 * r ^ n + 4 * (r ^ n * (z ^ n).re) + r ^ n *
        ((z ^ n).re * (z ^ n).re - (z ^ n).im * (z ^ n).im) =
      2 * r ^ n * ((z ^ n).re + 1) ^ 2 := by
    rw [← sq ((z ^ n).im), ← him]
    ring
  rw [hident]
  positivity

/-- The de la Vallée Poussin Euler-product inequality for the trivial character, a unitary
character, and its square at ordinates in the ratio zero, one, and two. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_norm_finiteHeckeL_product_ge_one (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (a : ℂ) (ha : a.re = 0) :
    1 ≤ ‖(ideleClassNormTwist (1 : U[F]) 0).LSeries (x : ℂ) ^ 3 * (ideleClassNormTwist χ 0).LSeries ((x : ℂ) + a) ^ 4 *
      (ideleClassNormTwist (χ ^ 2) 0).LSeries ((x : ℂ) + 2 * a)‖ := by
  classical
  have h₂a : (2 * a).re = 0 := by simp [Complex.mul_re, ha]
  let s₀ : halfPlane := ⟨(x : ℂ), hx⟩
  let s₁ : halfPlane := ⟨(x : ℂ) + a, by simpa [mem_preimage, Complex.add_re, ha]⟩
  let s₂ : halfPlane := ⟨(x : ℂ) + 2 * a, by simpa [mem_preimage, Complex.add_re, h₂a]⟩
  have hp := (((finiteHeckeL_hasProd (1 : U[F]) s₀).pow 3).mul
    ((finiteHeckeL_hasProd χ s₁).pow 4)).mul (finiteHeckeL_hasProd (χ ^ 2) s₂)
  apply ge_of_tendsto' hp.norm
  intro T
  simp only [norm_prod]
  refine Finset.one_le_prod₀ fun v _ ↦ ?_
  change 1 ≤ ‖finiteHeckeEulerFactor (1 : U[F]) v x ^ 3 *
    finiteHeckeEulerFactor χ v ((x : ℂ) + a) ^ 4 *
    finiteHeckeEulerFactor (χ ^ 2) v ((x : ℂ) + 2 * a)‖
  have hres (ψ : U[F]) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v (u : v.adicCompletion F) =
        (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hres_one (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) 0).restrict v (u : v.adicCompletion F) = 1 := by
    rw [hres, PontryaginDual.one_apply, Circle.coe_one]
  have hres_sq (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (χ ^ 2) 0).restrict v (u : v.adicCompletion F) =
        ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F)) ^ 2 := by
    rw [hres, hres]
    rfl
  have hu₀ : (ideleClassNormTwist (1 : U[F]) 0).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr
    fun u ↦ hres_one (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
  have hu₂ (hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v) : (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦ by
      rw [show (ideleClassNormTwist (χ ^ 2) 0).restrict v u = ((ideleClassNormTwist χ 0).restrict v u) ^ 2 from
        hres_sq (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u),
        hu.restrict_apply_unit_eq_one, one_pow]
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv₀ : (ideleClassNormTwist (1 : U[F]) 0).localValue v = 1 := hres_one u
  have hv₂ : (ideleClassNormTwist (χ ^ 2) 0).localValue v = ((ideleClassNormTwist χ 0).localValue v) ^ 2 := hres_sq u
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  let r := q ^ (-x)
  have hr : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let z (ψ : U[F]) (b : ℂ) := (ideleClassNormTwist ψ 0).localValue v * (q : ℂ) ^ (-b)
  have hz (ψ : U[F]) (b : ℂ) (hb : b.re = 0) : ‖z ψ b‖ = 1 := by
    simp [z, norm_ideleClassNormTwist_zero_localValue,
      Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re, hb]
  have hphase (ψ : U[F]) (b : ℂ) :
      (ideleClassNormTwist ψ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-((x : ℂ) + b)) =
        (r : ℂ) * z ψ b := by
    change (ideleClassNormTwist ψ 0).localValue v * (q : ℂ) ^ (-((x : ℂ) + b)) = _
    rw [neg_add, Complex.cpow_add _ _ hqC, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow hq₀.le]
    exact mul_left_comm ..
  have hsq : z (χ ^ 2) (2 * a) = z χ a ^ 2 := by
    simp only [z, hv₂, mul_pow, neg_mul_eq_mul_neg]
    rw [show (2 : ℂ) = (↑(2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_mul]
  rw [finiteHeckeEulerFactor, ite_eq_left hu₀, hv₀, one_mul]
  change 1 ≤ ‖(1 - (q : ℂ) ^ (-(x : ℂ)))⁻¹ ^ 3 * _ * _‖
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · rw [finiteHeckeEulerFactor, ite_eq_left hu, finiteHeckeEulerFactor, ite_eq_left (hu₂ hu),
      hphase χ a, hphase (χ ^ 2) (2 * a), hsq]
    exact finiteHeckeL_inv_isBigO_oneLine_one_le_norm_eulerFactor_product hr hr₁ (hz χ a ha)
  · rw [finiteHeckeEulerFactor, ite_eq_right hu, one_pow, mul_one, finiteHeckeEulerFactor]
    have hrnorm : ‖(1 : ℂ) - (r : ℂ)‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr hr₁.le)]
    split_ifs
    · rw [hphase (χ ^ 2) (2 * a)]
      let w := (r : ℂ) * z (χ ^ 2) (2 * a)
      change 1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - w)⁻¹‖
      have hw : ‖w‖ = r := by
        rw [show ‖w‖ = ‖(r : ℂ)‖ * ‖z (χ ^ 2) (2 * a)‖ from norm_mul _ _,
          hz _ _ h₂a, Complex.norm_of_nonneg hr, mul_one]
      have hpos : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr fun h ↦
        hr₁.ne (by rw [← hw, ← sub_eq_zero.mp h, norm_one])
      rw [norm_mul, norm_pow, norm_inv, norm_inv, hrnorm, inv_pow, ← mul_inv,
        one_le_inv₀ (mul_pos (pow_pos (sub_pos.mpr hr₁) 3) hpos)]
      have hle : ‖(1 : ℂ) - w‖ ≤ 1 + r := by
        simpa only [hw, norm_one] using norm_sub_le (1 : ℂ) w
      calc
        (1 - r) ^ 3 * ‖(1 : ℂ) - w‖ ≤ (1 - r) ^ 3 * (1 + r) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg (sub_nonneg.mpr hr₁.le) _)
        _ = (1 - r) ^ 2 * (1 - r ^ 2) := by ring
        _ ≤ (1 - r) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) (sq_nonneg _)
        _ ≤ 1 := by
          rw [mul_one]
          exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)
    · rw [mul_one, norm_pow, norm_inv, hrnorm, inv_pow,
        one_le_inv₀ (pow_pos (sub_pos.mpr hr₁) 3)]
      exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)

/-- Euler product inequality in the exact variables used in the bound. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_euler (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {x : ℝ} (hx : 1 < x) (t : ℝ) :
    1 ≤ ‖dedekindZeta F x‖ ^ 3 * ‖L ⟨x,t⟩‖ ^ 4 *
      ‖finiteHeckeL (χ ^ 2) ⟨⟨x,2*t⟩,hx⟩‖ := by
  let a : ℂ := ⟨0,t⟩
  have h := finiteHeckeL_inv_isBigO_oneLine_norm_finiteHeckeL_product_ge_one χ hx a rfl
  have h1 : (x : ℂ) + a = ⟨x,t⟩ := by apply Complex.ext <;> simp [a]
  have h2 : (x : ℂ) + 2 * a = ⟨x,2*t⟩ := by apply Complex.ext <;> simp [a, Complex.mul_re, Complex.mul_im]
  have hζ := completedHeckeL_one_eq_dedekindZeta (F := F) (⟨x,hx⟩ : halfPlane)
  change heckeGammaFactor (1 : U[F]) x * _ = _ at hζ
  rw [← heckeGammaFactor_one] at hζ
  have hz := mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (zero_lt_one.trans hx)) hζ
  rw [h1, h2, norm_mul, norm_mul, norm_pow, norm_pow] at h
  rw [hSeries ⟨⟨x,t⟩,hx⟩]
  simpa only [finiteHeckeL, hz] using h

private theorem finiteHeckeL_inv_isBigO_oneLine_scalar {V B X L Q : ℝ} (hV : 3 ≤ V) (hB : 0 ≤ B) (hX : 0 ≤ X) (hQ : 0 ≤ Q)
    (hzeta : B ≤ V ^ 13) (hsq : Q ≤ V) (hdiff : X ≤ L + (V ^ 11)⁻¹)
    (hprod : 1 ≤ B ^ 3 * X ^ 4 * Q) : (V ^ 11)⁻¹ ≤ L := by
  by_contra! hbad
  have hpos : 0 < V := by linarith
  have ht : X ≤ 2 / V ^ 11 := by rw [div_eq_mul_inv]; linarith
  have h := calc
    1 ≤ B ^ 3 * X ^ 4 * Q := hprod
    _ ≤ (V ^ 13) ^ 3 * (2 / V ^ 11) ^ 4 * V := by gcongr
    _ = 16 / V ^ 4 := by field_simp; ring
  have hh : 3 ^ 4 ≤ V ^ 4 := by gcongr
  have := (le_div_iff₀ (pow_pos hpos 4)).mp h
  norm_num at hh
  linarith

/-- A local version of the strip bounds sufficient for the reciprocal estimate. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_bounds (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (m : ℕ) (hm : m ≠ 0)
    (ha : ∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩)
    (h₁ : ∀ᶠ t : ℝ in atAbsTop, ∀ d ∈ Ioc (0:ℝ) 1,
      ‖L ⟨1 + d,t⟩ - L ⟨1,t⟩‖ ≤ |t| ^ m * d)
    (h₂ : ∀ᶠ t : ℝ in atAbsTop, ∀ d ∈ Ioc (0:ℝ) 1, ∀ hd : 1 < 1+d,
      ‖finiteHeckeL (χ ^ 2) ⟨⟨1+d,2*t⟩,hd⟩‖ ≤ |t| ^ m) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩ ∧ L ⟨1,t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1,t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  let V (t : ℝ) := |t| ^ m
  let d (t : ℝ) := (V t ^ 12)⁻¹
  have hV : Tendsto V atAbsTop atTop :=
    (tendsto_pow_atTop (α := ℝ) hm).comp tendsto_comap
  have hd : Tendsto d atAbsTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α := ℝ) (by decide : 12 ≠ 0)).comp hV)
  have hx : Tendsto (fun t ↦ 1+d t) atAbsTop (𝓝[>] (1:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hd.const_add 1, ?_⟩
    filter_upwards [hV.eventually_gt_atTop 0] with t ht
    change 1 < 1 + (V t ^ 12)⁻¹
    exact lt_add_of_pos_right _ (inv_pos.mpr (pow_pos ht 12))
  obtain ⟨C,hC⟩ := ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm.comp hx).isBoundedUnder_le.eventually_le
  have hbound : ∀ᶠ t : ℝ in atAbsTop, (V t ^ 11)⁻¹ ≤ ‖L ⟨1,t⟩‖ := by
    filter_upwards [hC, hV.eventually_ge_atTop C, hV.eventually_ge_atTop 3,
      hd.eventually_le_const zero_lt_one, h₁, h₂] with t hζ hCV hv hdle hdiff hsq
    have hv' : 0 < V t := by linarith
    have hdt : 0 < d t := inv_pos.mpr (pow_pos hv' 12)
    have hxt : 1 < 1 + d t := lt_add_of_pos_right _ hdt
    have hz : d t * ‖dedekindZeta F (1 + d t : ℝ)‖ ≤ C := by
      simpa [Function.comp_def, norm_mul, Real.norm_of_nonneg hdt.le] using hζ
    apply finiteHeckeL_inv_isBigO_oneLine_scalar hv (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) _ (hsq (d t) ⟨hdt,hdle⟩ hxt) _
      (finiteHeckeL_inv_isBigO_oneLine_euler χ L hSeries hxt t)
    · have hvBound : ‖dedekindZeta F (1 + d t : ℝ)‖ ≤ V t / d t :=
        (le_div_iff₀ hdt).mpr (by simpa only [mul_comm (d t)] using hz.trans hCV)
      exact hvBound.trans_eq (show V t / d t = V t ^ 13 by dsimp only [d]; rw [div_inv_eq_mul, pow_succ (V t) 12, mul_comm])
    · calc
        _ ≤ ‖L ⟨1,t⟩‖ + ‖L ⟨1+d t,t⟩ - L ⟨1,t⟩‖ := by
          linarith [norm_sub_norm_le (L ⟨1+d t,t⟩) (L ⟨1,t⟩)]
        _ ≤ ‖L ⟨1,t⟩‖ + V t * d t := add_le_add_right (hdiff _ ⟨hdt,hdle⟩) _
        _ = _ := by dsimp [d]; field_simp
  refine ⟨?_, m*11, Nat.mul_pos (Nat.pos_of_ne_zero hm) (by decide), Asymptotics.IsBigO.of_bound 1 ?_⟩
  · filter_upwards [ha, hbound, hV.eventually_gt_atTop 0] with t ht hb hv
    exact ⟨ht, norm_pos_iff.mp ((inv_pos.mpr (pow_pos hv 11)).trans_le hb)⟩
  · filter_upwards [hbound, hV.eventually_gt_atTop 0] with t ht hv
    rw [norm_inv, Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _), one_mul, pow_mul]
    exact (inv_le_comm₀ ((inv_pos.mpr (pow_pos hv 11)).trans_le ht) (pow_pos hv 11)).mpr ht


private theorem finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat (G : ℂ → ℂ) (a b M : ℝ)
    (hO : G =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M) :
    ∃ n : ℕ, ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖G z‖ ≤ |z.im| ^ n := by
  obtain ⟨n,hn⟩ := exists_nat_gt M
  obtain ⟨c,hc⟩ := Asymptotics.isBigO_iff.mp hO
  simp only [eventually_inf_principal, eventually_comap, eventually_atTop] at hc
  obtain ⟨T,hT⟩ := hc
  refine ⟨n+1, max T (max 1 c), fun z hz htz ↦ ?_⟩
  have hz₁ : 1 ≤ |z.im| := (le_max_left 1 c).trans ((le_max_right ..).trans htz)
  have hzc : c ≤ |z.im| := (le_max_right 1 c).trans ((le_max_right ..).trans htz)
  have h := hT |z.im| ((le_max_left ..).trans htz) z rfl hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  calc
    ‖G z‖ ≤ c * |z.im| ^ M := h
    _ ≤ |z.im| * |z.im| ^ M := by gcongr
    _ ≤ |z.im| * |z.im| ^ (n:ℝ) := by gcongr
    _ = _ := by rw [Real.rpow_natCast, pow_succ, mul_comm]

private theorem finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    {n : ℕ} {T : ℝ} (hT : ∀ z : ℂ, z.re ∈ Icc (-1:ℝ) 4 → T ≤ |z.im| → ‖L z‖ ≤ |z.im| ^ n)
    (t : ℝ) (ht : max 2 (T + 2) ≤ |t|) {σ : ℝ} (hσ : σ ∈ Icc (1:ℝ) 2) :
    AnalyticAt ℂ L ⟨σ,t⟩ ∧ ‖deriv L ⟨σ,t⟩‖ ≤ (2*|t|)^n := by
  let s : ℂ := ⟨σ,t⟩
  have him := (le_max_left 2 (T+2)).trans ht
  have hlarge := (le_max_right 2 (T+2)).trans ht
  have hDisk {w : ℂ} (hw : w ∈ Metric.closedBall s 1) :
      w.re ∈ Ioo (-1:ℝ) 4 ∧ T < |w.im| ∧ |w.im| ≤ 2 * |t| := by
    have dist := mem_closedBall_iff_norm.mp hw
    have hre := (Complex.abs_re_le_norm (w - s)).trans dist
    have him' := (Complex.abs_im_le_norm (w - s)).trans dist
    change |w.re - σ| ≤ 1 at hre
    change |w.im - t| ≤ 1 at him'
    rw [abs_le] at hre
    refine ⟨⟨by linarith [hre.1,hσ.1], by linarith [hre.2,hσ.2]⟩, ?_, ?_⟩
    · linarith [(abs_sub_abs_le_abs_sub t w.im).trans (by simpa [abs_sub_comm] using him')]
    · linarith [(abs_sub_abs_le_abs_sub w.im t).trans him']
  have han {w : ℂ} (hw : w ∈ Metric.closedBall s 1) : AnalyticAt ℂ L w := by
    obtain ⟨hRe,hLo,hHi⟩ := hDisk hw
    apply (hL (mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hp
    have hre := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hRe
    have him := (isOpen_Ioo.preimage Complex.continuous_im.abs).mem_nhds
      (show w ∈ (fun z : ℂ ↦ |z.im|) ⁻¹' Ioo T (|w.im|+1) from ⟨hLo, by linarith⟩)
    have hb : ∀ᶠ z in 𝓝 w, ‖L z‖ ≤ (|w.im|+1)^n := by
      filter_upwards [hre,him] with z hz h'z
      exact (hT z (Ioo_subset_Icc_self hz) h'z.1.le).trans (pow_le_pow_left₀ (abs_nonneg _) h'z.2.le _)
    have hp' := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop ((|w.im|+1)^n)
    obtain ⟨_,h,h'⟩ := ((hb.filter_mono nhdsWithin_le_nhds).and hp').exists
    exact h'.not_ge h
  refine ⟨han (Metric.mem_closedBall_self zero_le_one), ?_⟩
  have hDiff : DiffContOnCl ℂ L (Metric.ball s 1) :=
    (show DifferentiableOn ℂ L (Metric.closedBall s 1) from fun w hw ↦
      (han hw).differentiableAt.differentiableWithinAt).diffContOnCl_ball subset_rfl
  have hCircle : ∀ w ∈ Metric.sphere s 1, ‖L w‖ ≤ (2 * |t|)^n := by
    intro w hw
    obtain ⟨hRe,hLo,hHi⟩ := hDisk (Metric.sphere_subset_closedBall hw)
    exact (hT w (Ioo_subset_Icc_self hRe) hLo.le).trans (pow_le_pow_left₀ (abs_nonneg _) hHi _)
  simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hDiff hCircle

/-- Reduction to polynomial *upper* bounds. No log derivative or zero-free region is needed. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_strip_growth (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hG : ∃ M : ℝ, L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (-1:ℝ) 4)] fun s ↦ |s.im| ^ M)
    (hG₂ : ∃ n : ℕ, ∃ T : ℝ, ∀ z : halfPlane, (z:ℂ).re ≤ 2 → T ≤ |(z:ℂ).im| →
      ‖finiteHeckeL (χ^2) z‖ ≤ |(z:ℂ).im| ^ n) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩ ∧ L ⟨1,t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1,t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  obtain ⟨M,hM⟩ := hG
  obtain ⟨n,T,hT⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat L _ _ _ hM
  obtain ⟨k,T₂,hT₂⟩ := hG₂
  let m := 2 * (n+k) + 1
  have hb {x : ℝ} (hx : 2 ≤ x) {j : ℕ} (hj : j ≤ n + k) : (2 * x) ^ j ≤ x ^ m := by
    have hx₁ : 1 ≤ x := by linarith
    calc
      (2*x) ^ j ≤ (x*x) ^ j := by gcongr
      _ = x ^ (2*j) := by rw [← sq, pow_mul]
      _ ≤ x ^ m := pow_le_pow_right₀ hx₁ (by dsimp [m]; omega)
  have hlim : Tendsto abs atAbsTop atTop := tendsto_comap
  have hev := hlim.eventually_ge_atTop (max 2 (T+2))
  apply finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_bounds χ L hSeries m (Nat.succ_ne_zero _)
  · filter_upwards [hev] with t ht
    exact (finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip L hL hT t ht ⟨le_rfl,one_le_two⟩).1
  · filter_upwards [hev] with t ht
    have hs (σ : ℝ) (hσ : σ ∈ Icc (1:ℝ) 2) := finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip L hL hT t ht hσ
    have hd (σ : ℝ) (hσ : σ ∈ Icc (1:ℝ) 2) : HasDerivAt (fun u : ℝ ↦ L ⟨u,t⟩) (deriv L ⟨σ,t⟩) σ := by
      have he (u : ℝ) : (u:ℂ) + ⟨0,t⟩ = ⟨u,t⟩ := by apply Complex.ext <;> simp
      have hd := ((hs σ hσ).1.differentiableAt.hasDerivAt.comp_of_eq (x := (σ:ℂ))
        ((hasDerivAt_id (σ:ℂ)).add_const (⟨0,t⟩:ℂ)) (he σ).symm).comp_ofReal
      simpa only [he,mul_one,id_eq,Function.comp_def] using hd
    intro d hd'
    have hu : 1+d ∈ Icc (1:ℝ) 2 := ⟨by linarith [hd'.1], by linarith [hd'.2]⟩
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 1) (b := 2)
      (fun σ hσ ↦ (hd σ hσ).hasDerivWithinAt)
      (fun σ hσ ↦ (hs σ (Ico_subset_Icc_self hσ)).2.trans (hb ((le_max_left ..).trans ht) (by omega))) _ hu
    simpa using h
  · filter_upwards [hev, hlim.eventually_ge_atTop T₂] with t ht ht₂
    intro d hd hd'
    have h := hT₂ (⟨⟨1+d,2*t⟩,hd'⟩ : halfPlane) (by change 1+d ≤ 2; linarith [hd.2])
      (by change T₂ ≤ |2*t|; rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith [abs_nonneg t])
    change _ ≤ |2*t| ^ k at h
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h.trans (hb ((le_max_left ..).trans ht) (by omega))


/-- Paper: Theorem B.6.1.6, p. 640. The reciprocal of the finite Hecke
L-function grows at most polynomially on `Re(s) = 1` at large absolute heights.
Deviation: Eventual analyticity and nonvanishing make the reciprocal well-defined. -/
theorem finiteHeckeL_inv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  apply finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_strip_growth χ L hL hSeries
  · obtain ⟨M,_,hM⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (-1) 4 (by norm_num)
    exact ⟨M,hM⟩
  · obtain ⟨G,hG,hAgree⟩ := finiteHeckeL_exists_continuation (χ^2)
    obtain ⟨M,_,hM⟩ := finiteHeckeL_continuation_isBigO_rpow (χ^2) G hG hAgree 1 2 one_lt_two
    obtain ⟨n,T,hT⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat G _ _ _ hM
    exact ⟨n,T,fun z hz ht ↦ hAgree z ▸ hT z ⟨z.2.le,hz⟩ ht⟩

-- TODO(paper-gap): Equation (B.6.1.23) uses the finite L-factors. Its χ²
-- argument has height 2t, which (B.6.1.28) must retain.
-- TODO(paper-gap): The upper bound in (B.6.1.28) uses the critical-strip exponent
-- for σ > 1, where that exponent can be negative and the Euler factors need not decay.

section OutsideEulerProduct

variable (χ : U[F]) (L : ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)

-- TODO(later): needs §6.3 to compare with the S-local quotient in (6.3.1.6).
-- Compare as meromorphic germs, or after normalizing the quotient at removable
-- singularities. The factors agree via sLocalHeckeL_eq_partialEulerProduct on
-- descended characters. The finite-factor expression already occurs in §3.4.
local notation "Loutside" => (fun s : ℂ ↦ (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s)

include hL hSeries

/-- Paper: Theorem B.6.1.7, p. 641. Each sufficiently high open unit interval
contains a height at which the Euler product outside `S` has a polynomial
lower bound on the whole horizontal segment from real part `-1` to `2`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_exists_horizontal_lower_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∃ t ∈ Ioo T (T + 1),
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A) < ‖Loutside ⟨σ, t⟩‖ := by
  sorry

/-- Paper: Theorem B.6.1.7, p. 641. The polynomial lower bound holds on a
closed unit interval outside a measurable set of length `1 / B`, with the
large-height threshold independent of `B > 1`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∀ B : ℝ, 1 < B →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧
        volume E = ENNReal.ofReal (1 / B) ∧
        ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (-1 : ℝ) 2,
          T ^ (-(A * B)) < ‖Loutside ⟨σ, t⟩‖ := by
  sorry

-- TODO(paper-gap): The exponent in (B.6.1.38) must account for the left edge
-- of the strip. The basepoint for the integration in (B.6.1.43) is log Loutside(2 + it).

-- TODO(paper-gap): Footnote 29 asks for details in the proof of Corollary B.6.1.8
-- that pass from horizontal lower bounds to bounds for reciprocal derivatives.
-- At the selected heights use Cauchy's estimates on a wider fixed strip for
-- derivatives of Loutside, then differentiate Loutside * (1 / Loutside) = 1.

/-- Paper: Corollary B.6.1.8, p. 643. For each derivative order there is a
nondecreasing sequence of heights tending to infinity in absolute value and
growing at most linearly in the index. The derivative of the reciprocal Euler
product is bounded by a fixed power of the height on every selected segment.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. The supremum is expressed pointwise, and
analyticity ensures the iterated derivatives are defined on the segments. The
unit intervals of Theorem B.6.1.7, reflected for the conjugate character on the
negative tail, give heights within one of the index for the application of §B.3. -/
theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound (m : ℕ) :
    let l := comap (abs : ℤ → ℤ) atTop
    ∃ (A β : ℝ) (T : ℤ → ℝ), 0 < A ∧ 0 < β ∧ Monotone T ∧
      Tendsto (abs ∘ T) l atTop ∧ (T =O[l] fun k ↦ |(k : ℝ)|) ∧
      (∀ᶠ k : ℤ in l, |T k - (k : ℝ)| ≤ 1) ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩ ∧
          ‖iteratedDeriv m (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩‖ ≤ A * |T k| ^ β := by
  sorry

end OutsideEulerProduct

end RiemannMasullo
