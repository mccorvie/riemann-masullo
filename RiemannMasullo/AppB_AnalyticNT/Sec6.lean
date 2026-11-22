module

public import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.ForMathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
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
  sorry

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
  sorry

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

/-- Paper: Lemma B.6.1.4, p. 638. The logarithmic-derivative coefficients are
bounded by a constant times `log m`, with the constant depending only on the field degree. -/
theorem heckeLogDerivCoefficient_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [NumberField F], Module.finrank ℚ F = d →
        ∀ᶠ m : ℕ in atTop, ∀ χ : U[F],
          ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖ ≤ C * Real.log (m : ℝ) := by
  sorry

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

/-- Paper: Theorem B.6.1.6, p. 640. The reciprocal of the finite Hecke
L-function grows at most polynomially on `Re(s) = 1` at large absolute heights.
Deviation: Eventual analyticity and nonvanishing make the reciprocal well-defined. -/
theorem finiteHeckeL_inv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  sorry

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
