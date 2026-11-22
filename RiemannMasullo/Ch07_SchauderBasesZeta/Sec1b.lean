module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import Mathlib.Analysis.Complex.LocallyUniformLimit
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# §7.1.3–7.1.4 Polar multiplicities and spectral biorthogonal sequences

A finite set of finite places is used to specify an S-local space. Every infinite place is
included in the S-local space regardless of this set.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped DirectSum NNReal Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "RatPrimes" => HeightOneSpectrum (𝓞 ℚ)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "degree" => Module.finrank ℚ F
local notation "archCount" => Fintype.card (InfinitePlace F)

section Polar

/-- Paper: §7.1.3, p. 323.
A quasi-character of Galois type is a complex norm twist of a finite-order unitary character. -/
def IsGaloisType (c : HeckeCharacter (𝓞 F) F) : Prop :=
  ∃ (χ₀ : U𝔽) (s : ℂ), IsOfFinOrder χ₀ ∧ c = ideleClassNormTwist χ₀ s

/-- Paper: §7.1.3, p. 323.
A pure norm power is of Galois type.
Deviation: States a sanity check using the trivial finite-order character. -/
theorem isGaloisType_normPower (s : ℂ) :
    IsGaloisType (ideleClassNormTwist (1 : U𝔽) s) :=
  ⟨1, s, IsOfFinOrder.one, rfl⟩

/-- Paper: Remark 7.1.3.1, p. 323.
A rational prime splits completely when every prime over it has ramification index one
and residue degree one. -/
def rationalPrimeSplitsCompletely (F : Type*) [Field F] [NumberField F] (p : RatPrimes) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v.under (𝓞 ℚ) = p →
    v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1

/-- Paper: Remark 7.1.3.1, p. 323.
Every rational prime splits completely in the base field.
Deviation: States a sanity check for the definition of complete splitting. -/
theorem rationalPrimeSplitsCompletely_rat (p : RatPrimes) :
    rationalPrimeSplitsCompletely ℚ p := by
  intro v _
  let q := v.asIdeal
  let : q.IsPrime := v.isPrime
  let : q.IsMaximal := v.isMaximal
  let : q.LiesOver q := ⟨(Ideal.comap_id q).symm⟩
  refine ⟨Ideal.ramificationIdx_eq_one q (𝓞 ℚ), ?_⟩
  exact (Ideal.inertiaDeg_eq_of_isMaximal q q).trans (Module.finrank_self (𝓞 ℚ ⧸ q))

local notation "overₚ(" T "," p ")" =>
  @Finset.filter Primes (fun v : Primes ↦ HeightOneSpectrum.under (𝓞 ℚ) v = p)
    (Classical.decPred _) T

/-- The local value of a unitary character at an unramified place has norm one. -/
private theorem reciprocalEulerProduct_over_prime_zero_norm (χ : U𝔽) (v : Primes)
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ‖(ideleClassNormTwist χ 0).localValue v‖ = 1 := by
  obtain ⟨π, hπ⟩ :=
    (Valued.v : Valuation (v.adicCompletion F) _).exists_isUniformizer_of_isCyclic_of_nontrivial
  have hπ0 : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    have h' := hπ
    rw [Valuation.IsUniformizer, h, map_zero] at h'
    exact (Units.ne_zero _) h'.symm
  rw [hv.localValue_eq π hπ, show (π : v.adicCompletion F) =
    ((Units.mk0 _ hπ0 : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
    HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change ‖(χ _ : ℂ) * (((ideleClassNorm F _ : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)‖ = 1
  rw [Complex.cpow_zero, mul_one, Circle.norm_coe]

/-- Paper: Remark 7.1.3.1, p. 323.
A zero of the reciprocal Euler product over a rational prime belongs to the phase lattice
of some unramified place over that prime. -/
theorem reciprocalEulerProduct_over_prime_zero (χ : U𝔽) (S₀ : Finset Primes)
    (p : RatPrimes) {s : ℂ}
    (hs : reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s = 0) :
    ∃ v ∈ overₚ(S₀, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧
      ∃ (k : ℤ) (t : ℝ),
        let q := v.asIdeal.absNorm
        let period := 2 * Real.pi / Real.log (q : ℝ)
        t ∈ Ico 0 period ∧
        (ideleClassNormTwist χ 0).localValue v = (q : ℂ) ^ (-(t : ℂ) * Complex.I) ∧
        s = (((k : ℝ) * period - t : ℝ) : ℂ) * Complex.I := by
  obtain ⟨v, hvS, hv0⟩ := Finset.prod_eq_zero_iff.mp hs
  by_cases hun : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  swap
  · rw [finiteHeckeEulerFactor, ite_eq_right hun, inv_one] at hv0
    exact absurd hv0 one_ne_zero
  refine ⟨v, hvS, hun, ?_⟩
  rw [finiteHeckeEulerFactor, ite_eq_left hun, inv_inv] at hv0
  set q : ℕ := v.asIdeal.absNorm with hqdef
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  set ℓ := Real.log (q : ℝ) with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos hq1
  have hP : 0 < 2 * Real.pi / ℓ := div_pos Real.two_pi_pos hℓ
  set a := (ideleClassNormTwist χ 0).localValue v with hadef
  have ha1 : ‖a‖ = 1 := reciprocalEulerProduct_over_prime_zero_norm χ v hun
  have hlog : Complex.log (q : ℂ) = (ℓ : ℂ) := by rw [hℓdef, Complex.natCast_log]
  have hcpow (t : ℝ) : (q : ℂ) ^ (-(t : ℂ) * Complex.I) =
      Complex.exp (((-t * ℓ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hq0, hlog]
    congr 1
    push_cast
    ring
  set t₀ : ℝ := -Complex.arg a / ℓ
  set t : ℝ := toIcoMod hP 0 t₀
  have ht : t ∈ Ico 0 (2 * Real.pi / ℓ) := by simpa using toIcoMod_mem_Ico hP 0 t₀
  have hta : a = (q : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    rw [hcpow]
    have hm := toIcoMod_add_toIcoDiv_zsmul hP 0 t₀
    set m := toIcoDiv hP 0 t₀
    have : -t * ℓ = Complex.arg a + (m : ℝ) * (2 * Real.pi) := by
      have h1 : t = t₀ - m * (2 * Real.pi / ℓ) := by rw [zsmul_eq_mul] at hm; linarith
      rw [h1]
      simp only [t₀]
      field_simp
      ring
    rw [this]
    push_cast
    rw [add_mul, Complex.exp_add, show (m : ℂ) * (2 * Real.pi) * Complex.I =
      m * (2 * Real.pi * Complex.I) by ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a, ha1]
    simp
  rw [hta, sub_eq_zero, ← Complex.cpow_add _ _ hq0, eq_comm,
    Complex.cpow_def_of_ne_zero hq0, hlog, Complex.exp_eq_one_iff] at hv0
  obtain ⟨n, hn⟩ := hv0
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  refine ⟨-n, t, ht, hta, ?_⟩
  push_cast
  rw [hlog]
  field_simp
  linear_combination -hn


/-- The places over a rational prime in a finite set inject into the primes over it, and
bijectively when the set contains all of them. -/
private theorem reciprocalEulerProduct_over_prime_order_le_map (p : RatPrimes) (T : Finset Primes) :
    ∃ e : overₚ(T, p) → p.asIdeal.primesOver (𝓞 F), (∀ v, (e v).1 = v.1.asIdeal) ∧ Injective e ∧
      ((∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ T) → Surjective e) := by
  classical
  refine ⟨fun v ↦ ⟨v.1.asIdeal, v.1.isPrime,
    ⟨(congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.mp v.2).2).symm⟩⟩, fun _ ↦ rfl, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · intro hT q
    have hq0 : q.1 ≠ ⊥ := by
      intro h
      have := q.2.2.over
      rw [h, Ideal.under_bot] at this
      exact p.ne_bot this
    let w : Primes := ⟨q.1, q.2.1, hq0⟩
    have hw : w.under (𝓞 ℚ) = p := HeightOneSpectrum.ext q.2.2.over.symm
    exact ⟨⟨w, Finset.mem_filter.mpr ⟨hT w hw, hw⟩⟩, rfl⟩

/-- The fundamental identity for the places of `F` over a rational prime. -/
private theorem reciprocalEulerProduct_over_prime_order_le_sum (p : RatPrimes) :
    ∑ q : p.asIdeal.primesOver (𝓞 F), q.1.ramificationIdx (𝓞 ℚ) * q.1.inertiaDeg (𝓞 ℚ) =
      degree := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 ℚ) ℚ (𝓞 F) F]

/-- A rational prime has at most `[F : ℚ]` primes of `F` above it. -/
private theorem reciprocalEulerProduct_over_prime_order_le_card_le (p : RatPrimes) :
    Fintype.card (p.asIdeal.primesOver (𝓞 F)) ≤ degree := by
  rw [← reciprocalEulerProduct_over_prime_order_le_sum p, Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have := q.2.1
  have := q.2.2
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
    (Ideal.ramificationIdx_pos (𝓞 ℚ) q.1).ne' (Ideal.inertiaDeg_pos q.1 (𝓞 ℚ)).ne')

/-- Each reciprocal finite Euler factor is entire with zeros of order at most one. -/
private theorem reciprocalEulerProduct_over_prime_order_le_factor (χ : U𝔽) (v : Primes) (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) s ∧
      analyticOrderAt (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) s ≤ 1 := by
  classical
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · have hq1 : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    set L := Complex.log (v.asIdeal.absNorm : ℂ)
    have hL : L ≠ 0 := by
      simp only [L, ← Complex.natCast_log]
      exact_mod_cast (Real.log_pos hq1).ne'
    set a := (ideleClassNormTwist χ 0).localValue v
    have hfun : (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) =
        fun z ↦ 1 - a * Complex.exp (-(L * z)) := by
      funext z
      rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv, Complex.cpow_def_of_ne_zero hN0]
      congr 3
      ring
    rw [hfun]
    refine ⟨by fun_prop, ?_⟩
    by_cases h0 : 1 - a * Complex.exp (-(L * s)) = 0
    · have hd : HasDerivAt (fun z ↦ 1 - a * Complex.exp (-(L * z)))
          (-(a * (Complex.exp (-(L * s)) * -(L * 1)))) s :=
        ((((hasDerivAt_id s).const_mul L).neg.cexp).const_mul a).const_sub 1
      have ha : a ≠ 0 := by intro ha; rw [ha] at h0; simp at h0
      exact (AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        (f := fun z ↦ 1 - a * Complex.exp (-(L * z))) (by fun_prop) h0
        (by rw [hd.deriv]; simp [ha, hL, Complex.exp_ne_zero])).le
    · rw [(analyticOrderAt_eq_zero (f := fun z ↦ 1 - a * Complex.exp (-(L * z))) (z₀ := s)).mpr
        (Or.inr h0)]
      exact zero_le_one
  · have hfun : (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) = fun _ ↦ 1 := by
      funext z
      rw [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
    rw [hfun]
    refine ⟨analyticAt_const, ?_⟩
    rw [(analyticOrderAt_eq_zero (f := fun _ : ℂ ↦ (1 : ℂ)) (z₀ := s)).mpr (Or.inr one_ne_zero)]
    exact zero_le_one

/-- A reciprocal partial Euler product is analytic with zero order at most the number of
places in it. -/
private theorem reciprocalEulerProduct_over_prime_order_le_prod
    (χ : U𝔽) (T : Finset Primes) (s : ℂ) :
    AnalyticAt ℂ (reciprocalPartialHeckeEulerProduct χ T) s ∧
      analyticOrderAt (reciprocalPartialHeckeEulerProduct χ T) s ≤ T.card := by
  classical
  induction T using Finset.induction with
  | empty =>
    have : reciprocalPartialHeckeEulerProduct χ ∅ = fun _ ↦ 1 := by
      funext z; simp [reciprocalPartialHeckeEulerProduct]
    rw [this, (analyticOrderAt_eq_zero (f := fun _ : ℂ ↦ (1 : ℂ)) (z₀ := s)).mpr
      (Or.inr one_ne_zero)]
    exact ⟨analyticAt_const, by simp⟩
  | insert v T hvT ih =>
    have hsplit : reciprocalPartialHeckeEulerProduct χ (insert v T) =
        (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) * reciprocalPartialHeckeEulerProduct χ T := by
      funext z
      simp [reciprocalPartialHeckeEulerProduct, Finset.prod_insert hvT]
    obtain ⟨hfa, hfo⟩ := reciprocalEulerProduct_over_prime_order_le_factor χ v s
    rw [hsplit, analyticOrderAt_mul hfa ih.1, Finset.card_insert_of_notMem hvT]
    refine ⟨hfa.mul ih.1, ?_⟩
    push_cast
    rw [add_comm]
    exact add_le_add ih.2 hfo

/-- Paper: Remark 7.1.3.1, p. 323.
The zero multiplicity of a reciprocal Euler product over a single rational prime is
bounded by the degree of the number field. -/
theorem reciprocalEulerProduct_over_prime_order_le (χ : U𝔽) (S₀ : Finset Primes)
    (p : RatPrimes) (s : ℂ) :
    analyticOrderAt (reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p)) s ≤
      (degree : ℕ∞) := by
  obtain ⟨e, -, he, -⟩ := reciprocalEulerProduct_over_prime_order_le_map p S₀
  refine (reciprocalEulerProduct_over_prime_order_le_prod χ _ s).2.trans ?_
  have h1 := Fintype.card_le_of_injective e he
  rw [Fintype.card_coe] at h1
  exact_mod_cast h1.trans (reciprocalEulerProduct_over_prime_order_le_card_le p)

/-- Paper: Remark 7.1.3.1, p. 323.
At a completely split rational prime, the product of the reciprocal unramified factors
is a power of the rational Euler polynomial when all uniformizer values are one. -/
theorem reciprocalEulerProduct_over_split_prime (χ : U𝔽) (S₀ : Finset Primes)
    (p : RatPrimes) (hp : rationalPrimeSplitsCompletely F p)
    (hS₀ : ∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S₀)
    (hχ : ∀ v : Primes, v.under (𝓞 ℚ) = p →
      (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧ (ideleClassNormTwist χ 0).localValue v = 1)
    (s : ℂ) :
    reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
      (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ degree := by
  classical
  have hfac : ∀ v ∈ overₚ(S₀, p),
      (finiteHeckeEulerFactor χ v s)⁻¹ = 1 - (p.asIdeal.absNorm : ℂ) ^ (-s) := by
    intro v hv
    have hvp := (Finset.mem_filter.mp hv).2
    obtain ⟨hun, h1⟩ := hχ v hvp
    have hN : v.asIdeal.absNorm = p.asIdeal.absNorm := by
      have : v.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hvp).symm⟩
      rw [← Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal, (hp v hvp).2, pow_one]
    rw [finiteHeckeEulerFactor, ite_eq_left hun, inv_inv, h1, one_mul, hN]
  rw [reciprocalPartialHeckeEulerProduct, Finset.prod_congr rfl hfac, Finset.prod_const]
  congr 1
  obtain ⟨e, hev, he, hsurj⟩ := reciprocalEulerProduct_over_prime_order_le_map p S₀
  rw [← Fintype.card_coe, Fintype.card_of_bijective ⟨he, hsurj hS₀⟩,
    ← reciprocalEulerProduct_over_prime_order_le_sum p,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  obtain ⟨⟨w, hw⟩, rfl⟩ := hsurj hS₀ q
  obtain ⟨he1, hf1⟩ := hp w (Finset.mem_filter.mp hw).2
  rw [hev, he1, hf1]

/-- Paper: Remark 7.1.3.1, p. 323.
There are infinitely many completely split rational primes at which the character
is unramified at every place above the prime. -/
theorem infinite_split_primes_unramified (χ : U𝔽) :
    {p : RatPrimes | rationalPrimeSplitsCompletely F p ∧
      ∀ v : Primes, v.under (𝓞 ℚ) = p → (ideleClassNormTwist χ 0).IsUnramifiedAt v}.Infinite :=
  by sorry

/-- Paper: Remark 7.1.3.1, p. 324.
The completely split rational primes have positive density among the rational primes.
Deviation: Uses Mathlib's Dirichlet density. -/
theorem split_rationalPrimes_pos_dirichletDensity (F : Type*) [Field F] [NumberField F] :
    ∃ δ > (0 : ℝ),
      NumberField.Set.HasDirichletDensity {p : RatPrimes | rationalPrimeSplitsCompletely F p} δ :=
  by sorry

-- TODO(paper-gap): The claim on p. 324 extending (7.1.3.1) to Galois type needs to
-- translate the exponent by ix. For ℚ and χ = |·|^i the identity fails at s = 0.

/-- Paper: Remark 7.1.3.1, p. 324.
For a Galois-type unitary character there are infinitely many completely split primes
where the full reciprocal Euler polynomial is a degree power in the translated coordinate.
Deviation: The right side uses exponent s + ix for the character χ₀ |·|^(ix). -/
theorem infinite_split_primes_reciprocalEulerProduct_normTwist
    (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I)) :
    {p : RatPrimes | rationalPrimeSplitsCompletely F p ∧
      ∀ S₀ : Finset Primes, (∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S₀) →
        ∀ s : ℂ, reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
          (1 - (p.asIdeal.absNorm : ℂ) ^ (-(s + (x : ℂ) * Complex.I))) ^ degree}.Infinite :=
  by sorry

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
local notation "chartₛ(" χ "," h ")" => twistₛ (sIdeleRestriction F S (Subtype.mk (ideleClassNormTwist χ 0) h))
local notation "rhoChart(" χ "," h ")" => fun z ↦ sLocalRhoFactor (chartₛ(χ, h) z)

/-- Paper: Lemma 7.1.2.2, p. 317 and Theorem 7.1.3.2, p. 324.
The multiplicity of the correcting factor is the order of its pole in the norm-twist
coordinate at the chosen quasi-character. It is zero at a point without a pole. -/
def sLocalRhoPoleOrder (c : QuasiCharacter (SIdeleQuotient F S)) : ℕ :=
  (-(sLocalIdelicOrderBound c).untop₀).toNat

/-- Paper: Lemma 7.1.2.2, p. 317. The pole order is the negative of the
order bound used in the target space of the S-local Mellin transform of §5.1. -/
theorem sLocalIdelicOrderBound_eq_neg_poleOrder (c : QuasiCharacter (SIdeleQuotient F S)) :
    sLocalIdelicOrderBound c = ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) := by
  have hle : sLocalIdelicOrderBound c ≤ 0 := min_le_left _ _
  unfold sLocalRhoPoleOrder
  generalize sLocalIdelicOrderBound c = b at hle ⊢
  induction b using WithTop.recTopCoe with
  | top => exact absurd hle (by simp)
  | coe n =>
    have hn : n ≤ 0 := by exact_mod_cast hle
    simp only [WithTop.untop₀_coe]
    norm_cast
    omega

/-- Paper: Theorem 7.1.3.2, p. 324.
A simple pole of the correcting factor has multiplicity one in a unitary chart.
Deviation: States a sanity check comparing the centered and uncentered coordinates. -/
theorem sLocalRhoPoleOrder_eq_one_iff (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S) (s : ℂ) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) = 1 ↔
      meromorphicOrderAt rhoChart(χ, hχ) s = -1 := by
  have hcomp : (fun z ↦ sLocalRhoFactor (F := F) (S := S)
        (quasiCharacterNormTwist (G := Jₛ) mₛ
          (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S)) (chartₛ(χ, hχ) s) z)) =
      (fun z ↦ sLocalRhoFactor (chartₛ(χ, hχ) z)) ∘ (· + s) := by
    funext z
    simp only [Function.comp]
    congr 1
    ext1 g
    simp only [quasiCharacterNormTwist]
    have hn : (((mₛ g : ℝ≥0ˣ) : ℝ≥0) : ℂ) ≠ 0 := by simp
    change ((_ : ℂ) * _) * _ = (_ : ℂ) * _
    rw [mul_assoc]
    congr 1
    change (((mₛ g : ℝ≥0ˣ) : ℝ≥0) : ℂ) ^ s * (((mₛ g : ℝ≥0ˣ) : ℝ≥0) : ℂ) ^ z = _
    rw [← Complex.cpow_add _ _ hn, add_comm]
    rfl
  have key : meromorphicOrderAt (fun z ↦ sLocalRhoFactor (F := F) (S := S)
        (quasiCharacterNormTwist (G := Jₛ) mₛ
          (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S)) (chartₛ(χ, hχ) s) z)) 0
      = meromorphicOrderAt rhoChart(χ, hχ) s := by
    rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  unfold sLocalRhoPoleOrder sLocalIdelicOrderBound
  rw [key]
  generalize meromorphicOrderAt rhoChart(χ, hχ) s = o
  induction o using WithTop.recTopCoe with
  | top =>
    have h0 : (-WithTop.untop₀ (0 : WithTop ℤ)).toNat = 0 := by
      rw [← WithTop.coe_zero, WithTop.untop₀_coe]; rfl
    simp only [min_eq_left le_top, h0]
    have : (⊤ : WithTop ℤ) ≠ -1 := by
      first
        | exact WithTop.top_ne_coe
        | simp
        | decide
    simp [this]
  | coe n =>
    rw [← WithTop.coe_zero, ← WithTop.coe_min]
    simp only [WithTop.untop₀_coe]
    constructor
    · intro h
      have : (-(min 0 n)).toNat = 1 := h
      have : n = -1 := by omega
      subst this
      rfl
    · intro h
      have : n = -1 := by
        first
          | exact_mod_cast h
          | exact WithTop.coe_injective h
          | simpa using h
      subst this
      rfl

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)

-- TODO(paper-gap): The common-pole observation preceding Theorem 7.1.3.2 needs
-- distinct residue characteristics. For the trivial character of ℚ(i), both
-- Euler factors over 5 have a pole at 2πi/log 5.

/-- The absolute norm of a finite place is a positive power of the rational prime below it. -/
private theorem finiteHeckeEulerFactors_common_pole_subsingleton_norm (v : Primes) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.under ℤ = Ideal.span {(ℓ : ℤ)} ∧
      ∃ f : ℕ, 0 < f ∧ v.asIdeal.absNorm = ℓ ^ f := by
  set P := v.asIdeal.under ℤ with hPdef
  have hP : P.IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot v.ne_bot
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
  have hg' : P = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by rintro rfl; exact hP0 (by rw [hg']; simp)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hP)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, by rw [hg', Int.span_natAbs], ?_⟩
  have : v.asIdeal.LiesOver P := ⟨rfl⟩
  refine ⟨v.asIdeal.inertiaDeg ℤ, Ideal.inertiaDeg_pos v.asIdeal ℤ, ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg P v.asIdeal, hg', Ideal.absNorm_span_singleton]
  simp

/-- The rationals have a single prime above each nonzero prime of the integers. -/
private theorem finiteHeckeEulerFactors_common_pole_subsingleton_unique
    (P : Ideal ℤ) [P.IsMaximal] (a b : HeightOneSpectrum (𝓞 ℚ))
    (ha : a.asIdeal.under ℤ = P) (hb : b.asIdeal.under ℤ = P) : a = b := by
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 ℚ)
  rw [RingOfIntegers.rank, Module.finrank_self] at hsum
  have hcard : Fintype.card (P.primesOver (𝓞 ℚ)) ≤ 1 := by
    rw [← hsum, Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have := q.2.1
    have := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  let ea : P.primesOver (𝓞 ℚ) := ⟨a.asIdeal, a.isPrime, ⟨ha.symm⟩⟩
  let eb : P.primesOver (𝓞 ℚ) := ⟨b.asIdeal, b.isPrime, ⟨hb.symm⟩⟩
  have := Fintype.card_le_one_iff.mp hcard ea eb
  exact HeightOneSpectrum.ext (congrArg Subtype.val this)

/-- Places with multiplicatively dependent absolute norms lie over the same rational prime. -/
private theorem finiteHeckeEulerFactors_common_pole_subsingleton_eq
    (v w : Primes) {m n : ℕ} (hm : 0 < m) (_hn : 0 < n)
    (h : v.asIdeal.absNorm ^ m = w.asIdeal.absNorm ^ n) : v.under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
  obtain ⟨ℓ, hℓ, hvP, f, hf, hvN⟩ := finiteHeckeEulerFactors_common_pole_subsingleton_norm v
  obtain ⟨ℓ', hℓ', hwP, g, hg, hwN⟩ := finiteHeckeEulerFactors_common_pole_subsingleton_norm w
  rw [hvN, hwN, ← pow_mul, ← pow_mul] at h
  have hdvd : ℓ ∣ ℓ' := hℓ.dvd_of_dvd_pow (h ▸ dvd_pow_self ℓ (by positivity))
  have hll : ℓ = ℓ' := (Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp hdvd
  subst hll
  have hpr : (Ideal.span {(ℓ : ℤ)}).IsPrime := hvP ▸ Ideal.IsPrime.under ℤ v.asIdeal
  have : (Ideal.span {(ℓ : ℤ)}).IsMaximal := hpr.isMaximal (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hℓ.ne_zero)
  apply finiteHeckeEulerFactors_common_pole_subsingleton_unique (Ideal.span {(ℓ : ℤ)})
  · change (v.asIdeal.under (𝓞 ℚ)).under ℤ = _
    rw [Ideal.under_under, hvP]
  · change (w.asIdeal.under (𝓞 ℚ)).under ℤ = _
    rw [Ideal.under_under, hwP]

/-- Any two poles of an unramified Euler factor differ by a multiple of `2πi / log q`. -/
private theorem finiteHeckeEulerFactors_common_pole_subsingleton_pole
    (χ : U𝔽) (v : Primes) (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {s : ℂ} (hs : meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0) :
    ∀ s' : ℂ, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s' < 0 →
      ∃ k : ℤ, (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * (s' - s) =
        k * (2 * Real.pi * Complex.I) := by
  classical
  have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  set L := Complex.log (v.asIdeal.absNorm : ℂ) with hLdef
  have hL : (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) = L := by rw [hLdef, Complex.natCast_log]
  set a := (ideleClassNormTwist χ 0).localValue v
  have hfun : finiteHeckeEulerFactor χ v = fun z ↦ (1 - a * Complex.exp (-(L * z)))⁻¹ := by
    funext z
    rw [finiteHeckeEulerFactor, ite_eq_left hv, Complex.cpow_def_of_ne_zero hN0]
    congr 4
    ring
  have hzero (z : ℂ) (hz : meromorphicOrderAt (finiteHeckeEulerFactor χ v) z < 0) :
      a * Complex.exp (-(L * z)) = 1 := by
    by_contra h
    have h0 : 1 - a * Complex.exp (-(L * z)) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have han : AnalyticAt ℂ (finiteHeckeEulerFactor χ v) z := by
      rw [hfun]
      exact (by fun_prop : AnalyticAt ℂ (fun z ↦ 1 - a * Complex.exp (-(L * z))) z).inv h0
    exact absurd hz (not_lt.mpr han.meromorphicOrderAt_nonneg)
  intro s' hs'
  have e1 := hzero s hs
  have e2 := hzero s' hs'
  have ha : a ≠ 0 := by intro ha; rw [ha, zero_mul] at e1; exact zero_ne_one e1
  have : Complex.exp (-(L * s')) = Complex.exp (-(L * s)) :=
    mul_left_cancel₀ ha (e2.trans e1.symm)
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp this
  exact ⟨-k, by rw [hL]; push_cast; linear_combination -hk⟩

/-- Paper: Theorem 7.1.3.2(1), p. 324.
Two unramified finite places above different rational primes have at most one shared
pole of their local Euler factors. -/
theorem finiteHeckeEulerFactors_common_pole_subsingleton
    (_hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (v w : ↥S) (hv : (ideleClassNormTwist (F := F) χ 0).IsUnramifiedAt v.val)
    (hw : (ideleClassNormTwist (F := F) χ 0).IsUnramifiedAt w.val)
    (hp : (v.val : Primes).under (𝓞 ℚ) ≠ w.val.under (𝓞 ℚ)) :
    {s : ℂ | meromorphicOrderAt (finiteHeckeEulerFactor (F := F) χ v.val) s < 0 ∧
      meromorphicOrderAt (finiteHeckeEulerFactor (F := F) χ w.val) s < 0}.Subsingleton := by
  intro s₁ hs₁ s₂ hs₂
  by_contra hne
  have hkv := finiteHeckeEulerFactors_common_pole_subsingleton_pole χ v.val hv hs₁.1
  have hkw := finiteHeckeEulerFactors_common_pole_subsingleton_pole χ w.val hw hs₁.2
  obtain ⟨m, hm⟩ := hkv s₂ hs₂.1
  obtain ⟨n, hn⟩ := hkw s₂ hs₂.2
  set lv := Real.log (v.val.asIdeal.absNorm : ℝ)
  set lw := Real.log (w.val.asIdeal.absNorm : ℝ)
  have hqv : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hqw : 1 < (w.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm w.val
  have hlv : 0 < lv := Real.log_pos hqv
  have hlw : 0 < lw := Real.log_pos hqw
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hreal : lw * m = lv * n := by
    have : ((lw * m - lv * n : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
      push_cast
      linear_combination -(lw : ℂ) * hm + (lv : ℂ) * hn
    have := (mul_eq_zero.mp this).resolve_right h2pi
    exact_mod_cast sub_eq_zero.mp (by exact_mod_cast this)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    have : (lv : ℂ) * (s₂ - s₁) = 0 := by simpa using hm
    have hlv0 : (lv : ℂ) ≠ 0 := by exact_mod_cast hlv.ne'
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hlv0)).symm
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero, mul_eq_zero, hlw.ne', false_or] at hreal
    exact hm0 (by exact_mod_cast hreal)
  have habs : (m.natAbs : ℝ) * lw = (n.natAbs : ℝ) * lv := by
    have := congrArg abs hreal
    rw [abs_mul, abs_mul, abs_of_pos hlw, abs_of_pos hlv] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    linarith
  have hpow : ((v.val.asIdeal.absNorm ^ n.natAbs : ℕ) : ℝ) =
      ((w.val.asIdeal.absNorm ^ m.natAbs : ℕ) : ℝ) := by
    push_cast
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_pow, Real.log_pow]
    linarith
  exact hp (finiteHeckeEulerFactors_common_pole_subsingleton_eq v.val w.val
    (Int.natAbs_pos.mpr hn0) (Int.natAbs_pos.mpr hm0)
    (by exact_mod_cast hpow))

/-- Paper: Theorem 7.1.3.2(2)–(3), p. 324.
The pole order is bounded by the number of places in S, including all infinite places.
Deviation: Uses the proof's bound at every point of the component, which includes the
archimedean points of abscissa zero and all the indicated finite-place poles. -/
theorem sLocalRhoPoleOrder_le_card (s : ℂ) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤ archCount + S.card := by
  classical
  let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
  have hc (x : Jₛ) : ‖c x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [show c (QuotientGroup.mk g) = ideleClassNormTwist χ 0
      (QuotientGroup.mk (sIdeleInsertion F S g)) from sIdeleRestriction_mk F S _ g]
    change ‖(χ _ : ℂ) * _ ^ (0 : ℂ)‖ = 1
    simp
  let ψ : PontryaginDual Jₛ :=
    { toFun := fun x ↦ ⟨c x, mem_sphere_zero_iff_norm.mpr (hc x)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hψ : (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ = c := by
    ext x
    rfl
  have hcomp : (fun z ↦ sLocalRhoFactor (F := F) (S := S)
        (twistₛ (chartₛ(χ, hχ) s) z)) = rhoChart(χ, hχ) ∘ (· + s) := by
    funext z
    simp only [Function.comp]
    congr 1
    ext1 g
    simp only [quasiCharacterNormTwist]
    have hn : (((mₛ g : ℝ≥0ˣ) : ℝ≥0) : ℂ) ≠ 0 := by simp
    change ((_ : ℂ) * _) * _ = (_ : ℂ) * _
    rw [mul_assoc]
    congr 1
    change (((mₛ g : ℝ≥0ˣ) : ℝ≥0) : ℂ) ^ s * (((mₛ g : ℝ≥0ˣ) : ℝ≥0) : ℂ) ^ z = _
    rw [← Complex.cpow_add _ _ hn, add_comm]
    rfl
  have key : sLocalIdelicOrderBound (chartₛ(χ, hχ) s) =
      min 0 (meromorphicOrderAt rhoChart(χ, hχ) s) := by
    unfold sLocalIdelicOrderBound
    rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  have hord := sLocalRhoFactor_orderAt_pole (F := F) (S := S) ψ s
  dsimp only at hord
  rw [hψ] at hord
  change meromorphicOrderAt rhoChart(χ, hχ) s < 0 → _ at hord
  have hbound : (-( (archCount + S.card : ℕ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt rhoChart(χ, hχ) s := by
    by_cases h : meromorphicOrderAt rhoChart(χ, hχ) s < 0
    · rw [hord h]
      have ha := Finset.card_filter_le (s := (Finset.univ : Finset (InfinitePlace F)))
        (p := fun w ↦ meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w
          (sLocalInfiniteRestriction w (twistₛ c z))) s < 0)
      have hf := Finset.card_filter_le (s := (Finset.univ : Finset S))
        (p := fun v ↦ meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val
          (sLocalFiniteRestriction v (twistₛ c z))) s < 0)
      simp only [Finset.card_univ, Fintype.card_coe] at ha hf
      exact_mod_cast (show -((archCount + S.card : ℕ) : ℤ) ≤
        -(((_ + _ : ℕ)) : ℤ) by omega)
    · exact le_trans (by exact_mod_cast (show -((archCount + S.card : ℕ) : ℤ) ≤ 0 by omega))
        (le_of_not_gt h)
  have hb : (-( (archCount + S.card : ℕ) : ℤ) : WithTop ℤ) ≤
      sLocalIdelicOrderBound (chartₛ(χ, hχ) s) := by
    rw [key]
    exact le_min (by exact_mod_cast (show -((archCount + S.card : ℕ) : ℤ) ≤ 0 by omega)) hbound
  rw [sLocalIdelicOrderBound_eq_neg_poleOrder] at hb
  have : -((archCount + S.card : ℕ) : ℤ) ≤ -(sLocalRhoPoleOrder (chartₛ(χ, hχ) s) : ℤ) := by
    exact_mod_cast hb
  omega

/-- Paper: Theorem 7.1.3.2(2), p. 324.
In the open left half-plane the pole order is bounded by the number of infinite places.
Deviation: Includes all negative abscissae, as in the local-factor argument, and implies
the stated bounds for negative even abscissae and by the degree. -/
theorem sLocalRhoPoleOrder_le_archimedean_of_re_neg {s : ℂ} (hs : s.re < 0) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤ archCount := by sorry

-- TODO(paper-gap): The bound by r₂ at negative odd abscissae in Theorem 7.1.3.2(2)
-- omits real sign factors. The odd Dirichlet character modulo 4 gives a pole at -1
-- over ℚ, where r₂ = 0.

open Classical in
/-- Paper: Theorem 7.1.3.2(2), p. 324. At a negative odd abscissa the order
is bounded by the number of complex places plus the number of odd real places.
Deviation: Counts the real sign characters whose gamma factors have poles at this parity. -/
theorem sLocalRhoPoleOrder_le_of_re_neg_odd (n : ℕ) {s : ℂ}
    (hs : s.re = -((2 * n + 1 : ℕ) : ℝ)) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤
      (Finset.univ.filter (fun w : InfinitePlace F ↦ w.IsComplex ∨
        w.IsReal ∧ sLocalInfiniteRestriction w (chartₛ(χ, hχ) 0) (-1) = -1)).card := by sorry

open Classical in
/-- Paper: Theorem 7.1.3.2(3), p. 324.
Excess pole orders at finite-place poles can occur at at most the number of infinite
places plus the number of unordered pairs of unramified finite places. -/
theorem sLocalRhoPoleOrder_exceptions_encard_le :
    let S₀ := S.filter (fun v ↦ (ideleClassNormTwist (F := F) χ 0).IsUnramifiedAt v)
    {s : ℂ | degree < sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ∧
      ∃ v ∈ S₀, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0}.encard ≤
        (archCount + S₀.card.choose 2 : ℕ) := by sorry

-- On a radial subgroup, taking a power kills the finite-order part of the character.

private theorem excess_gamma_radial_inj {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (h : ∀ r : ℝ, 0 < r → ((r : ℂ) ^ a) ^ n = ((r : ℂ) ^ b) ^ n) : a = b := by
  have he : (n : ℂ) * a - n * b = 0 := by
    apply (existsUnique_complexPower (1 : ℝ≥0ˣ →ₜ* ℂ)).unique
    · intro t
      let r : ℝ := (t : ℝ≥0)
      have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt t)
      change (1 : ℂ) = (r : ℂ) ^ _
      have hr' := Complex.ofReal_ne_zero.mpr hr.ne'
      rw [Complex.cpow_sub _ _ hr', Complex.cpow_nat_mul, Complex.cpow_nat_mul, h r hr,
        div_self (pow_ne_zero _ (Complex.cpow_ne_zero_iff.mpr (.inl hr')))]
    · simp
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn.ne') (sub_eq_zero.mp he)

private theorem excess_gamma_twist_power (χ χ₀ : U𝔽) {a : ℂ}
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ a) {n : ℕ}
    (hn : χ₀ ^ n = 1) (g : C𝔽) :
    (ideleClassNormTwist χ 0 g) ^ n =
      ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ a) ^ n := by
  have hv : (χ₀ g : ℂ) ^ n = 1 := by
    rw [← Circle.coe_pow]
    have hp : (χ₀ g) ^ n = (χ₀ ^ n) g := (ContinuousMonoidHom.pow_apply χ₀ n g).symm
    rw [hp, hn, PontryaginDual.one_apply, Circle.coe_one]
  rw [hx]
  change ((χ₀ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ a) ^ n = _
  rw [mul_pow, hv, one_mul]

private theorem excess_gamma_real_parameter (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) {a : ℂ}
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ a)
    (v : InfinitePlace F) (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ v hv).exists.choose.1 = a := by
  obtain ⟨n, hn, hp⟩ := hχ₀.exists_pow_eq_one
  apply excess_gamma_radial_inj hn
  intro r hr
  let t := Units.mk0 r hr.ne'
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  let u := Units.map e.toMonoidHom t
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v u
  have hloc := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.2 t
  change ideleClassNormTwist χ 0 g = (‖r‖ : ℂ) ^ _ * (if 0 < r then 1 else (-1 : ℂ)) ^ _ at hloc
  rw [ite_eq_left hr, one_pow, mul_one, Real.norm_eq_abs, abs_of_pos hr] at hloc
  rw [← hloc, excess_gamma_twist_power χ χ₀ hx hp]
  have hnorm : (((ideleClassNorm F g : ℝ≥0) : ℝ)) = r := by
    dsimp only [g]
    rw [ideleClassNorm_ofCompletion, hv.mult_eq_one, pow_one]
    change ‖e r‖ = r
    exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
      (map_zero e) r).trans (abs_of_pos hr)
  rw [hnorm]

private theorem excess_gamma_complex_parameter (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) {a : ℂ}
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ a)
    (v : InfinitePlace F) (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters χ v hv).exists.choose.1 = a := by
  obtain ⟨n, hn, hp⟩ := hχ₀.exists_pow_eq_one
  apply excess_gamma_radial_inj hn
  intro r hr
  let y := Real.sqrt r
  have hy : 0 < y := Real.sqrt_pos.2 hr
  have hy' := Complex.ofReal_ne_zero.mpr hy.ne'
  have hsq : y ^ 2 = r := Real.sq_sqrt hr.le
  let t := Units.mk0 (y : ℂ) hy'
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  let u := Units.map e.toMonoidHom t
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v u
  have hloc := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec.2 t
  change ideleClassNormTwist χ 0 g = ((‖(y : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ _ *
    ((y : ℂ) / (‖(y : ℂ)‖ : ℂ)) ^ _ at hloc
  rw [Complex.norm_of_nonneg hy.le, div_self hy', one_zpow, mul_one, hsq] at hloc
  rw [← hloc, excess_gamma_twist_power χ χ₀ hx hp]
  have hnorm : (((ideleClassNorm F g : ℝ≥0) : ℝ)) = r := by
    dsimp only [g]
    rw [ideleClassNorm_ofCompletion, hv.mult_eq_two, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    change ‖e (y : ℂ)‖ ^ 2 = r
    have hi := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.isometry.norm_map_of_map_zero
      (map_zero e) (y : ℂ)
    change ‖e (y : ℂ)‖ = ‖(y : ℂ)‖ at hi
    rw [hi, Complex.norm_of_nonneg hy.le, hsq]
  rw [hnorm]

private theorem excess_gamma_real_ne_zero (z : ℂ) (hz : 0 ≤ z.re) (hne : z ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) : Complex.Gammaℝ (z + (r : ℂ)) ≠ 0 := by
  intro h
  obtain ⟨n, h⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re] at hre
  have hn : n = 0 := by exact_mod_cast (show (n : ℝ) = 0 by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : r = 0 := by subst n; simp at hre; linarith
  exact hne (by simpa [hr0, hn] using h)

private theorem excess_gamma_analytic (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I))
    (s : ℂ) (hs : 0 ≤ s.re) (hne : s ≠ -((x : ℂ) * Complex.I)) :
    AnalyticAt ℂ (heckeGammaFactor χ) s := by
  classical
  let z := s + (x : ℂ) * Complex.I
  have hz : 0 ≤ z.re := by simpa [z] using hs
  have hnz : z ≠ 0 := fun h ↦ hne (eq_neg_of_add_eq_zero_left h)
  have hΓ : heckeGammaFactor χ s ≠ 0 := by
    unfold heckeGammaFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    split_ifs with hv
    · dsimp only
      rw [excess_gamma_real_parameter χ χ₀ hχ₀ hx v hv]
      exact_mod_cast excess_gamma_real_ne_zero z hz hnz _ (Nat.cast_nonneg _)
    · dsimp only
      have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      rw [excess_gamma_complex_parameter χ χ₀ hχ₀ hx v hv']
      let k := (complexHeckeCharacter_parameters χ v hv').exists.choose.2.natAbs
      change Complex.Gammaℂ (z + (k : ℂ) / 2) / 2 ≠ 0
      apply (div_ne_zero · two_ne_zero)
      rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
      refine mul_ne_zero ?_ (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
      · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast] using
          excess_gamma_real_ne_zero z hz hnz ((k : ℝ) / 2) (by positivity)
      · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.one_re]
        positivity
  simpa only [inv_inv] using (((differentiable_inv_heckeGammaFactor χ).analyticAt s).fun_inv
    (inv_ne_zero hΓ))

-- A common pole translates, after taking a power, to a common pole of trivial-character
-- Euler factors. Those factors already have a common pole at zero.

private theorem excess_geometric_pole (q : ℕ) (hq : 1 < q) (a s : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ (1 - a * (q : ℂ) ^ (-z))⁻¹) s < 0 ↔
      a * (q : ℂ) ^ (-s) = 1 := by
  let D (z : ℂ) := 1 - a * (q : ℂ) ^ (-z)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (zero_lt_one.trans hq).ne'
  have hd (z : ℂ) : HasDerivAt D (a * (q : ℂ) ^ (-z) * Complex.log q) z := by
    have hpow := (hasDerivAt_neg' z).const_cpow (Or.inl hq0)
    convert (hpow.const_mul a).const_sub 1 using 1
    ring
  have ha : AnalyticAt ℂ D s := (show Differentiable ℂ D from fun z ↦ (hd z).differentiableAt).analyticAt s
  change meromorphicOrderAt D⁻¹ s < 0 ↔ _
  constructor
  · intro h
    by_contra hne
    exact (not_lt_of_ge (ha.inv (sub_ne_zero.mpr (Ne.symm hne))).meromorphicOrderAt_nonneg) h
  · intro h
    have hlog : Complex.log (q : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q)]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hq)).ne'
    have hzero : D s = 0 := sub_eq_zero.mpr h.symm
    have hderiv : deriv D s ≠ 0 := by rwa [(hd s).deriv, h, one_mul]
    rw [meromorphicOrderAt_inv, ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv]
    exact WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)

private theorem excess_finite_pole (χ : U𝔽) (v : Primes) (s : ℂ) :
    meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 ↔
      (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧
      (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) = 1 := by
  classical
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · have he : finiteHeckeEulerFactor χ v = fun z : ℂ ↦
        (1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-z))⁻¹ := by
      funext z; rw [finiteHeckeEulerFactor, ite_eq_left hu]
    rw [he, excess_geometric_pole _ (HeightOneSpectrum.one_lt_absNorm v)]
    simp [hu]
  · have he : finiteHeckeEulerFactor χ v = fun _ : ℂ ↦ 1 := by
      funext z; rw [finiteHeckeEulerFactor, ite_eq_right hu]
    simp [he, hu, meromorphicOrderAt_const]

private theorem excess_trivial_local (v : Primes) :
    (ideleClassNormTwist (1 : U𝔽) 0).IsUnramifiedAt v ∧
      (ideleClassNormTwist (1 : U𝔽) 0).localValue v = 1 := by
  have hval (u : (v.adicCompletion F)ˣ) : (ideleClassNormTwist (1 : U𝔽) 0).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hu := HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
    hval (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
  refine ⟨hu, ?_⟩
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  rw [hu.localValue_eq π hπ]
  exact hval (Units.mk0 π hπ.ne_zero)

private theorem excess_kill_phase (χ χ₀ : U𝔽) (N : ℕ) (hN : χ₀ ^ N = 1) (b s : ℂ)
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ b) (v : Primes)
    (hv : meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0) :
    (v.asIdeal.absNorm : ℂ) ^ (-((s + b) * (N : ℂ))) = 1 := by
  obtain ⟨hu, hp⟩ := (excess_finite_pole χ v s).mp hv
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u
  have hnorm : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) = ((v.asIdeal.absNorm : ℝ)⁻¹ : ℝ) := by
    apply congrArg Complex.ofReal
    dsimp only [g]
    rw [ideleClassNorm_ofAdicCompletion]
    have hval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπ.trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective F)))
    change ‖(π : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  have he : (ideleClassNormTwist χ 0).localValue v =
      (χ₀ g : ℂ) * (v.asIdeal.absNorm : ℂ) ^ (-b) := by
    rw [hu.localValue_eq u hπ, hx, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (χ₀ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ b = _
    rw [hnorm, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) b,
      ← Complex.cpow_neg, Complex.ofReal_natCast]
  have hq0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [he, mul_assoc, ← Complex.cpow_add _ _ hq0, ← neg_add, add_comm b s] at hp
  have hroot : (χ₀ g : ℂ) ^ N = 1 := by
    have hunit : (χ₀ g) ^ N = 1 := by
      exact (ContinuousMonoidHom.pow_apply (χ₀ : C𝔽 →ₜ* Circle) N g).symm.trans
        (DFunLike.congr_fun hN g)
    exact (map_pow Circle.coeHom (χ₀ g) N).symm.trans (by rw [hunit, map_one])
  have hpN := congrArg (fun z : ℂ ↦ z ^ N) hp
  rw [← neg_mul, Complex.cpow_mul_nat]
  simpa only [mul_pow, hroot, one_mul, one_pow] using hpN

private theorem excess_same_prime (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I))
    (S : Finset Primes) (s : ℂ) (hne : s ≠ -((x : ℂ) * Complex.I)) (v w : S)
    (hv : meromorphicOrderAt (finiteHeckeEulerFactor χ v.val) s < 0)
    (hw : meromorphicOrderAt (finiteHeckeEulerFactor χ w.val) s < 0) :
    (v.val : Primes).under (𝓞 ℚ) = w.val.under (𝓞 ℚ) := by
  by_contra hp
  obtain ⟨N, hpos, hN⟩ := hχ₀.exists_pow_eq_one
  have hS : ideleClassNormTwist (1 : U𝔽) 0 ∈ unramifiedOutside F S :=
    fun t _ ↦ (excess_trivial_local t).1
  have hsub := finiteHeckeEulerFactors_common_pole_subsingleton (1 : U𝔽) hS v w
    (excess_trivial_local v.val).1 (excess_trivial_local w.val).1 hp
  have htriv (t : Primes) (z : ℂ) (hz : (t.asIdeal.absNorm : ℂ) ^ (-z) = 1) :
      meromorphicOrderAt (finiteHeckeEulerFactor (1 : U𝔽) t) z < 0 := by
    obtain ⟨hu, hval⟩ := excess_trivial_local t
    exact (excess_finite_pole _ _ _).mpr ⟨hu, by rw [hval, one_mul, hz]⟩
  have hzero : (s + (x : ℂ) * Complex.I) * N = 0 := hsub
    ⟨htriv v.val _ (excess_kill_phase χ χ₀ N hN _ s hx v.val hv),
     htriv w.val _ (excess_kill_phase χ χ₀ N hN _ s hx w.val hw)⟩
    ⟨htriv v.val 0 (by simp), htriv w.val 0 (by simp)⟩
  exact hne (eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hzero).resolve_right
    (Nat.cast_ne_zero.mpr hpos.ne')))

private theorem excess_finite_inv_analyticAt (χ : U𝔽) (v : Primes) (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) s := by
  apply Differentiable.analyticAt
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp only [inv_inv]
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    fun_prop (disch := simp [hq])
  · exact differentiable_const _

private theorem excess_finite_meromorphicAt (χ : U𝔽) (v : Primes) (s : ℂ) :
    MeromorphicAt (finiteHeckeEulerFactor χ v) s := by
  simpa only [Pi.inv_def, inv_inv] using (excess_finite_inv_analyticAt χ v s).meromorphicAt.inv

private theorem excess_finite_product_meromorphicAt (χ : U𝔽) (S : Finset Primes) (s : ℂ) :
    MeromorphicAt (fun z ↦ ∏ v : S, finiteHeckeEulerFactor χ v.val z) s :=
  MeromorphicAt.fun_prod fun v _ ↦ excess_finite_meromorphicAt χ v.val s

private theorem excess_finite_order_over_prime (χ : U𝔽) (S : Finset Primes) (p : RatPrimes)
    (s : ℂ) : -(degree : WithTop ℤ) ≤
      ∑ v ∈ overₚ(S, p), meromorphicOrderAt (finiteHeckeEulerFactor χ v) s := by
  let T := overₚ(S, p)
  let R := reciprocalPartialHeckeEulerProduct χ T
  have hR : AnalyticAt ℂ R s :=
    T.analyticAt_fun_prod fun v _ ↦ excess_finite_inv_analyticAt χ v s
  have hprod : (fun z ↦ ∏ v ∈ T, finiteHeckeEulerFactor χ v z) = R⁻¹ := by
    funext z
    simp [R, reciprocalPartialHeckeEulerProduct, Finset.prod_inv_distrib]
  have hbound : analyticOrderAt R s ≤ (degree : ℕ∞) :=
    reciprocalEulerProduct_over_prime_order_le χ S p s
  change _ ≤ ∑ v ∈ T, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s
  rw [← meromorphicOrderAt_fun_prod (fun v (_ : v ∈ T) ↦ excess_finite_meromorphicAt χ v s),
    hprod, meromorphicOrderAt_inv, hR.meromorphicOrderAt_eq]
  lift analyticOrderAt R s to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound with n
  have hn : n ≤ degree := by exact_mod_cast hbound
  change ((-((degree : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ ((-(n : ℤ) : ℤ) : WithTop ℤ)
  exact WithTop.coe_le_coe.mpr (neg_le_neg (by exact_mod_cast hn))

private theorem excess_finite_order (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I))
    (S : Finset Primes) (s : ℂ) (hne : s ≠ -((x : ℂ) * Complex.I)) :
    -(degree : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ ∏ v : S, finiteHeckeEulerFactor χ v.val z) s := by
  classical
  have hprod : (fun z ↦ ∏ v : S, finiteHeckeEulerFactor χ v.val z) =
      (fun z ↦ ∏ v ∈ S, finiteHeckeEulerFactor χ v z) :=
    funext fun z ↦ Finset.prod_coe_sort S (fun v ↦ finiteHeckeEulerFactor χ v z)
  rw [hprod, meromorphicOrderAt_fun_prod (fun v (_ : v ∈ S) ↦ excess_finite_meromorphicAt χ v s)]
  by_cases h : ∃ v : S, meromorphicOrderAt (finiteHeckeEulerFactor χ v.val) s < 0
  · obtain ⟨v, hv⟩ := h
    refine (excess_finite_order_over_prime χ S (v.val.under (𝓞 ℚ)) s).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro w hw houtside
    exact le_of_not_gt fun hwneg ↦ houtside (Finset.mem_filter.mpr
      ⟨hw, excess_same_prime χ χ₀ hχ₀ x hx S s hne ⟨w, hw⟩ v hwneg hv⟩)
  · have hdeg : -(degree : WithTop ℤ) ≤ 0 := by
      change ((-((degree : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr (neg_nonpos.mpr (Int.natCast_nonneg _))
    exact hdeg.trans (Finset.sum_nonneg fun w hw ↦ le_of_not_gt fun hn ↦ h ⟨⟨w, hw⟩, hn⟩)

-- The epsilon factor and the reciprocal dual Euler product are holomorphic, so passing
-- from the Euler product to the correcting factor cannot increase a pole order.

private theorem excess_center (c : QuasiCharacter Jₛ) (s z : ℂ) :
    twistₛ (twistₛ c s) z = twistₛ c (z + s) := by
  ext1 g
  let N : ℂ := (((mₛ g : ℝ≥0) : ℝ) : ℂ)
  change c g * N ^ s * N ^ z = c g * N ^ (z + s)
  have hn : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
  rw [add_comm z s, Complex.cpow_add _ _ hn, mul_assoc]

private theorem excess_orderBound_eq (c : QuasiCharacter Jₛ) (s : ℂ) :
    sLocalIdelicOrderBound (twistₛ c s) =
      min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (twistₛ c z)) s) := by
  unfold sLocalIdelicOrderBound
  simp only [excess_center]
  rw [← zero_add s, ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ))
    (f := fun z ↦ sLocalRhoFactor (twistₛ c z))]
  simp only [zero_add]
  rfl

private theorem excess_differentiable_inv (η : PontryaginDual Jₛ) :
    let j := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
    Differentiable ℂ (fun z ↦ (sLocalHeckeL (F := F) (S := S) (twistₛ (j.comp η) z))⁻¹) := by
  classical
  obtain ⟨ψ, h, hη, -⟩ := sLocal_character_extension (F := F) (S := S) η
  dsimp only
  simp_rw [sLocalHeckeL_eq_partialEulerProduct η ψ h hη, mul_inv, ← Finset.prod_inv_distrib]
  refine (differentiable_inv_heckeGammaFactor ψ).mul (Differentiable.fun_finsetProd fun v _ ↦ ?_)
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp_rw [inv_inv]
    have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr v.val.ne_bot)
    exact (differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_neg.const_cpow (Or.inl hq)))
  · simp_rw [inv_one]
    exact differentiable_const _

private theorem excess_unitary_restriction :
    ∃ η : PontryaginDual Jₛ, sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η := by
  let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
  have hn (g : Jₛ) : ‖c g‖ = 1 := by
    induction g using QuotientGroup.induction_on with
    | H a =>
      change ‖(χ (QuotientGroup.mk (sIdeleInsertion F S a)) : ℂ) * _ ^ (0 : ℂ)‖ = 1
      rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  let η : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Circle.ext (map_one c)
      map_mul' := fun u v ↦ Circle.ext (map_mul c u v)
      continuous_toFun := c.continuous.subtype_mk _ }
  exact ⟨η, ContinuousMonoidHom.ext fun _ ↦ rfl⟩

private theorem excess_dual (η : PontryaginDual Jₛ) (z : ℂ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    dualQuasiCharacter mₛ (isProperMap_sIdeleQuotientNorm F S).continuous (twistₛ (j.comp η) z) =
      twistₛ (j.comp η⁻¹) (1 - z) := by
  dsimp only
  ext1 u
  let N : ℂ := (((mₛ u : ℝ≥0) : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ u).ne_zero)
  change N * twistₛ _ z u⁻¹ = (η⁻¹ u : ℂ) * N ^ (1 - z)
  rw [map_inv]
  change N * ((η u : ℂ) * N ^ z)⁻¹ = (η u : ℂ)⁻¹ * N ^ (1 - z)
  rw [mul_inv_rev, Complex.cpow_sub 1 z hN, Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

private theorem excess_euler_ratio (η : PontryaginDual Jₛ) (s : ℂ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let C := twistₛ (j.comp η)
    let D (z : ℂ) := twistₛ (j.comp η⁻¹) (1 - z)
    (fun z ↦ sLocalRhoFactor (C z)) =ᶠ[𝓝[≠] s]
      fun z ↦ (sLocalEpsilonFactor (C z) * (sLocalHeckeL (D z))⁻¹) * sLocalHeckeL (C z) := by
  intro j C D
  filter_upwards [(sLocalRhoFactor_eq_epsilon_mul η).filter_mono (nhdsNE_le_codiscrete s)] with z hz
  change sLocalRhoFactor (C z) = sLocalEpsilonFactor (C z) * (_ / _) at hz
  rw [hz, excess_dual η z]
  rw [div_eq_mul_inv, mul_assoc, mul_comm (sLocalHeckeL (C z))]

private theorem excess_correction_analytic (η : PontryaginDual Jₛ) (s : ℂ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let C := twistₛ (j.comp η)
    let D (z : ℂ) := twistₛ (j.comp η⁻¹) (1 - z)
    AnalyticAt ℂ (fun z ↦ sLocalEpsilonFactor (C z) * (sLocalHeckeL (D z))⁻¹) s := by
  intro j C D
  let I (z : ℂ) := (sLocalHeckeL (twistₛ (j.comp η⁻¹) z))⁻¹
  have hI : AnalyticAt ℂ I (1 - s) := (excess_differentiable_inv (η⁻¹)).analyticAt (1 - s)
  have hR : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s := by fun_prop
  have hIR : AnalyticAt ℂ (I ∘ (fun z : ℂ ↦ 1 - z)) s := hI.comp hR
  have hE : AnalyticAt ℂ (fun z ↦ sLocalEpsilonFactor (C z)) s := (sLocalEpsilonFactor_entire η) s trivial
  exact hE.mul hIR

private theorem excess_L_meromorphic (η : PontryaginDual Jₛ) (s : ℂ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let C := twistₛ (j.comp η)
    MeromorphicAt (fun z ↦ sLocalHeckeL (C z)) s := by
  intro j C
  let L (z : ℂ) := sLocalHeckeL (C z)
  have hm : MeromorphicAt L⁻¹ s := ((excess_differentiable_inv η).analyticAt s).meromorphicAt
  simpa only [inv_inv] using hm.inv

private theorem excess_order_ge_L (η : PontryaginDual Jₛ) (s : ℂ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let C := twistₛ (j.comp η)
    meromorphicOrderAt (fun z ↦ sLocalHeckeL (C z)) s ≤
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (C z)) s := by
  intro j C
  let D (z : ℂ) := twistₛ (j.comp η⁻¹) (1 - z)
  let A (z : ℂ) := sLocalEpsilonFactor (C z) * (sLocalHeckeL (D z))⁻¹
  let L (z : ℂ) := sLocalHeckeL (C z)
  have hA : AnalyticAt ℂ A s := excess_correction_analytic η s
  have hm : MeromorphicAt L s := excess_L_meromorphic η s
  have heq : (fun z ↦ sLocalRhoFactor (C z)) =ᶠ[𝓝[≠] s] A * L := excess_euler_ratio η s
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul hA.meromorphicAt hm]
  exact le_add_of_nonneg_left hA.meromorphicOrderAt_nonneg

private theorem excess_order_le_of_factors (s : ℂ)
    (hΓ : AnalyticAt ℂ (heckeGammaFactor (F := F) χ) s)
    (hmer : MeromorphicAt (fun z ↦ ∏ v : S, finiteHeckeEulerFactor χ v.val z) s)
    (hb : -(degree : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ ∏ v : S, finiteHeckeEulerFactor χ v.val z) s) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤ degree := by
  obtain ⟨η, hη⟩ := excess_unitary_restriction χ hχ
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let C := twistₛ (j.comp η)
  have hc : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩ = C 0 := by
    rw [hη]
    ext1 g
    change (η g : ℂ) = (η g : ℂ) * _ ^ (0 : ℂ)
    rw [Complex.cpow_zero, mul_one]
  have he : (fun z ↦ sLocalHeckeL (C z)) = (heckeGammaFactor χ) *
      (fun z ↦ ∏ v : S, finiteHeckeEulerFactor χ v.val z) :=
    funext (sLocalHeckeL_eq_partialEulerProduct η χ hχ hc)
  have hle := excess_order_ge_L η s
  change meromorphicOrderAt (fun z ↦ sLocalHeckeL (C z)) s ≤ _ at hle
  rw [he, meromorphicOrderAt_mul hΓ.meromorphicAt hmer] at hle
  have h := (add_le_add hΓ.meromorphicOrderAt_nonneg hb).trans hle
  rw [zero_add] at h
  have hdeg : -(degree : WithTop ℤ) ≤ 0 :=
    WithTop.coe_le_coe.mpr (neg_nonpos.mpr (Int.natCast_nonneg degree))
  have hmin := le_min hdeg h
  rw [← excess_orderBound_eq, sLocalIdelicOrderBound_eq_neg_poleOrder] at hmin
  rw [hη]
  exact_mod_cast neg_le_neg_iff.mp (WithTop.coe_le_coe.mp hmin)

/-- Paper: Theorem 7.1.3.2(3)(a), p. 324.
For a finite-order character twisted by an imaginary norm power, an excess pole order
can occur only at the negative of that twist parameter. -/
theorem sLocalRhoPoleOrder_excess_eq_neg_normTwist (χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I))
    {s : ℂ} (hs : degree < sLocalRhoPoleOrder (chartₛ(χ, hχ) s)) :
    s = -((x : ℂ) * Complex.I) := by
  by_contra hne
  apply (not_le.mpr hs)
  by_cases hneg : s.re < 0
  · refine (sLocalRhoPoleOrder_le_archimedean_of_re_neg χ hχ hneg).trans ?_
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank]
    omega
  · exact excess_order_le_of_factors χ hχ s
      (excess_gamma_analytic χ χ₀ hχ₀ x hx s (le_of_not_gt hneg) hne)
      (excess_finite_product_meromorphicAt χ S s)
      (excess_finite_order χ χ₀ hχ₀ x hx S s hne)

-- TODO(prerequisite): Theorem 7.1.3.2(3)(b) needs the algebraic Hecke-character
-- predicate used also in §1.7 and the statement of Schanuel's Conjecture.

local instance instMeasurableSLocalNormOneSec1b :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

local instance instHaarSLocalNormOneSec1b :
    (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

/-- Paper: Corollary 7.1.3.3, p. 325.
With a unique infinite place, the homogeneous theta function has the stated logarithmic
upper bound near norm zero. The remainder exponent comes from the largest smaller order.
Deviation: Uses zero when there is no smaller positive order, as in the least-bound
description on p. 326. This includes test functions whose zeta function has no poles. -/
theorem sLocalHomogeneousAdelicTheta_log_bound (harch : archCount = 1) (ψ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    let ω := ψ.comp
      (⟨Subgroup.subtype (MonoidHom.ker mₛ), continuous_subtype_val⟩ :
        MonoidHom.ker mₛ →ₜ* Jₛ)
    let normℝ (g : Jₛ) := ((mₛ g : ℝ≥0) : ℝ)
    let poleOrder (s : ℂ) := sLocalPolarMultiplicity f
      (twistₛ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) s)
    ∃ (M m : ℕ) (C D : ℝ), IsGreatest (range poleOrder) M ∧
      IsLeast {k : ℕ | ∀ s, poleOrder s < M → poleOrder s ≤ k} m ∧
      m < archCount + S.card ∧ 0 < C ∧ 0 ≤ D ∧
      ∀ᶠ g in comap normℝ (𝓝[>] 0),
        ‖sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω f g‖ ≤
          C * |Real.log (normℝ g)| ^ (archCount + S.card - 1) +
            D * |Real.log (normℝ g)| ^ ((m : ℤ) - 1) := by sorry

end Polar

section Spectral

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "Aℂ" => SchwartzBergman (univ : Set ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Situation 7.1.4.1, p. 326.
The restriction of a unitary character along the chosen idelic norm section is a
purely imaginary power with a unique real frequency. -/
theorem existsUnique_ideleNormSection_character_phase (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) :
    ∃! x : ℝ, ∀ t : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ t)) : ℂ) =
      (((t : ℝ≥0) : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I) := by
  let q : I𝔽 →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let incl : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let c := (incl.comp χ).comp (q.comp τ)
  obtain ⟨z, ⟨hz, hval⟩, huniq⟩ := existsUnique_unitaryComplexPower c
    (fun t ↦ Circle.norm_coe (χ (q (τ t))))
  have him : (z.im : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp [hz]
  refine ⟨z.im, fun t ↦ (hval t).trans (by rw [him]), fun x hx ↦ ?_⟩
  have he := huniq ((x : ℂ) * Complex.I) ⟨by simp, hx⟩
  simpa using congrArg Complex.im he

/-- Paper: Situation 7.1.4.1, p. 326. The Mellin transform on the polar
subspace descends through homogeneous theta to the entire Schwartz–Bergman space.
On a test function it is the section integral with the weight of the chosen character. -/
theorem exists_globalPolarThetaMellin (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* C𝔽)
    let P := adelePolarSubspace F
    let T := (homogeneousAdelicThetaLinearMap F ω).domRestrict P
    ∃ Z : (↥P ⧸ LinearMap.ker T) →L[ℂ] Aℂ, ∀ (f : P) (s : ℂ),
      (Z (Submodule.Quotient.mk f)).val s =
        homogeneousThetaMellinIntegral τ ω f.val (ideleClassNormTwist χ s) ∧
      (Z (Submodule.Quotient.mk f)).val s =
        globalIdelicZFunction f.val (ideleClassNormTwist χ s) := by
  intro ω P T
  -- The polar section integral is entire, so it is already its own continuation.
  have hM (f : P) : (fun s ↦ homogeneousThetaMellinIntegral τ ω f.val (ideleClassNormTwist χ s)) =
      (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) := by
    have h := homogeneousThetaMellinIntegral_entire_on_component τ ω f.val _hτ
      (Or.inl f.property) χ (fun _ ↦ rfl)
    exact (homogeneousThetaMellinIntegral_meromorphicContinuation τ ω f.val _hτ χ
      (fun _ ↦ rfl) _).mp ⟨fun s _ ↦ (h.analyticAt s).meromorphicNFAt, fun _ _ ↦ rfl⟩
  -- On the trivial component use the pole-free converse theorem. On every other
  -- component restrict the transform on the full homogeneous quotient to polar tests.
  have hex : ∃ M : P →L[ℂ] Aℂ, T.ker ≤ M.ker ∧
      ∀ (f : P) (s : ℂ), (M f).val s = globalIdelicZFunction f.val (ideleClassNormTwist χ s) := by
    by_cases hω : ω = 1
    · have ht := (globalConverse_existsUnique_normTwist χ hω).exists
      refine (globalConverse_normTwist χ ht.choose ht.choose_spec).elim fun M h ↦ ?_
      refine ⟨M, ?_, h.2.2.1⟩
      exact (congrArg (fun ψ ↦ (homogeneousAdelicThetaLinearMap F ψ).ker.comap P.subtype)
        hω).le.trans h.2.2.2.2.ge
    · refine (globalConverse_nontrivial χ hω).elim fun B h ↦ ?_
      let K := (homogeneousAdelicThetaLinearMap F ω).ker
      refine ⟨B.comp (K.mkQL.comp P.subtypeL), ?_, fun f s ↦ h.2.1 f.val s⟩
      intro f hf
      change B (K.mkQ f.val) = 0
      exact (congrArg B ((Submodule.Quotient.mk_eq_zero K).mpr hf)).trans B.map_zero
  refine hex.elim fun M h ↦ ?_
  refine ⟨T.ker.liftQL M h.1, fun f s ↦ ?_⟩
  change (M f).val s = _ ∧ (M f).val s = _
  exact ⟨(h.2 f s).trans (congrFun (hM f) s).symm, h.2 f s⟩

/-- Paper: §7.1.4, p. 326.
The entire functions in the compact-open continuous function algebra are closed under
addition and multiplication and contain every constant function. -/
theorem entireContinuousMap_subalgebra_properties :
    (∀ c : ℂ, Differentiable ℂ (algebraMap ℂ C(ℂ, ℂ) c : ℂ → ℂ)) ∧
    (∀ f g : C(ℂ, ℂ), Differentiable ℂ f → Differentiable ℂ g →
      Differentiable ℂ (f + g : C(ℂ, ℂ))) ∧
    (∀ f g : C(ℂ, ℂ), Differentiable ℂ f → Differentiable ℂ g →
      Differentiable ℂ (f * g : C(ℂ, ℂ))) := by
  exact ⟨fun c ↦ differentiable_const c, fun _ _ hf hg ↦ hf.add hg,
    fun _ _ hf hg ↦ hf.mul hg⟩

/-- Paper: §7.1.4, p. 326.
The ring of entire functions carries the compact-open topology of uniform convergence
on compact sets inherited from the ambient space of continuous functions. -/
def entireContinuousMapSubalgebra : Subalgebra ℂ C(ℂ, ℂ) where
  carrier := {f | Differentiable ℂ f}
  algebraMap_mem' := entireContinuousMap_subalgebra_properties.1
  zero_mem' := entireContinuousMap_subalgebra_properties.1 0
  one_mem' := entireContinuousMap_subalgebra_properties.1 1
  add_mem' := fun hf hg ↦ entireContinuousMap_subalgebra_properties.2.1 _ _ hf hg
  mul_mem' := fun hf hg ↦ entireContinuousMap_subalgebra_properties.2.2 _ _ hf hg

/-- Paper: §7.1.4, p. 326.
Complex conjugation is excluded from the algebra of entire functions.
Deviation: States a sanity check distinguishing the entire subalgebra from the ambient space. -/
theorem conj_not_mem_entireContinuousMapSubalgebra :
    (⟨starRingEnd ℂ, Complex.continuous_conj⟩ : C(ℂ, ℂ)) ∉ entireContinuousMapSubalgebra :=
  by
  intro h
  change Differentiable ℂ (starRingEnd ℂ : ℂ → ℂ) at h
  let D := fderiv ℂ (starRingEnd ℂ : ℂ → ℂ) 0
  have hD : D.restrictScalars ℝ = Complex.conjCLE.toContinuousLinearMap :=
    ((h 0).hasFDerivAt.restrictScalars ℝ).unique Complex.conjCLE.hasFDerivAt
  have hval (z : ℂ) : D z = (starRingEnd ℂ) z := DFunLike.congr_fun hD z
  have he : D Complex.I = Complex.I * D 1 := by
    simpa only [smul_eq_mul, mul_one] using D.map_smul Complex.I (1 : ℂ)
  rw [hval, hval] at he
  have hIm := congrArg Complex.im he
  norm_num at hIm

local notation "Entire" => Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra)

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The pole-removing multiple of the completed Hecke continuation is entire, with values
at the canceled poles supplied by meromorphic normalization. -/
theorem regularizedCompletedHeckeL_differentiable (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let b := (x₀ : ℂ) * Complex.I
    let δ : ℕ := open Classical in
      if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    Differentiable ℂ (toMeromorphicNFOn (fun s ↦ (s + b) ^ δ * (1 - s - b) ^ δ * L s) univ) :=
  by
    classical
    have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
    let x := hphase.exists.choose
    let b := (x : ℂ) * Complex.I
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · simp only [ite_eq_left hχ, pow_one]
      let P (s : ℂ) := (s + b) * (1 - s - b)
      change Differentiable ℂ (toMeromorphicNFOn (P * L) univ)
      obtain ⟨t, ⟨hchar, hzero, hone, haway⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ L _hL _hEq hχ
      have hx : -t = x := by
        refine hphase.unique ?_ hphase.exists.choose_spec
        intro u
        have he := DFunLike.congr_fun hchar (QuotientGroup.mk (τ u))
        change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
          1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
        rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
        rw [Complex.ofReal_neg, show -(t : ℂ) * Complex.I = -Complex.I * (t : ℂ) by ring]
        exact he
      have hb : b = -(Complex.I * (t : ℂ)) := by
        dsimp only [b]
        rw [← hx, Complex.ofReal_neg]
        ring
      have hP (s : ℂ) : AnalyticAt ℂ P s := by
        dsimp only [P]
        fun_prop
      have hmer : MeromorphicOn (P * L) univ :=
        fun s hs ↦ (hP s).meromorphicAt.mul (_hL hs).meromorphicAt
      have hcancel (s : ℂ) (hz : P s = 0) (hp : meromorphicOrderAt L s = -1) :
          0 ≤ meromorphicOrderAt (P * L) s := by
        rw [meromorphicOrderAt_mul (hP s).meromorphicAt (_hL (mem_univ s)).meromorphicAt, hp]
        have hpos : 0 < meromorphicOrderAt P s := by
          apply (tendsto_zero_iff_meromorphicOrderAt_pos (hP s).meromorphicAt).mp
          rw [← hz]
          exact (hP s).continuousAt.continuousWithinAt
        generalize meromorphicOrderAt P s = w at hpos ⊢
        cases w with
        | top => simp
        | coe k =>
          have hk : (0 : ℤ) < k := WithTop.coe_lt_coe.mp hpos
          exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ k + (-1) by omega)
      intro s
      apply AnalyticAt.differentiableAt
      have hNF := meromorphicNFOn_toMeromorphicNFOn (P * L) univ (mem_univ s)
      apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ s)]
      by_cases hs₀ : s = Complex.I * (t : ℂ)
      · subst s
        exact hcancel _ (by dsimp only [P]; rw [hb]; ring) hzero
      by_cases hs₁ : s = 1 + Complex.I * (t : ℂ)
      · subst s
        exact hcancel _ (by dsimp only [P]; rw [hb]; ring) hone
      exact ((hP s).mul (haway s (by simp [hs₀, hs₁]))).meromorphicOrderAt_nonneg
    · simpa only [ite_eq_right hχ, pow_zero, one_mul, toMeromorphicNFOn_eq_self.mpr _hL] using
        completedHeckeL_continuation_entire χ L _hL _hEq hχ

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The generator of the spectral ideal is the completed Hecke continuation multiplied by
the indicated pole-removing polynomial.
Deviation: Takes the holomorphic values at the canceled poles by meromorphic normalization. -/
def regularizedCompletedHeckeL (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s) : Entire :=
  open Classical in
  let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (x₀ : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let h := regularizedCompletedHeckeL_differentiable χ τ hτ L hL hEq
  ⟨⟨toMeromorphicNFOn (fun s ↦ (s + b) ^ δ * (1 - s - b) ^ δ * L s) univ, h.continuous⟩, h⟩

/-- Paper: Theorem 7.1.4.2(1), pp. 326–327.
At the two poles of a pure imaginary norm twist, the regularized generator is nonzero.
Deviation: States a sanity check safeguarding the removable values at the two poles. -/
theorem regularizedCompletedHeckeL_ne_zero_at_canceled_poles
    (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let b := (x₀ : ℂ) * Complex.I
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    Λ.val (-b) ≠ 0 ∧ Λ.val (1 - b) ≠ 0 := by
  classical
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  let x := hphase.exists.choose
  let b := (x : ℂ) * Complex.I
  obtain ⟨t, ⟨hchar, hzero, hone, _⟩, _⟩ :=
    completedHeckeL_continuation_simplePoles χ L hL hEq hχ
  have hx : -t = x := by
    refine hphase.unique ?_ hphase.exists.choose_spec
    intro u
    have he := DFunLike.congr_fun hchar (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    rw [Complex.ofReal_neg, show -(t : ℂ) * Complex.I = -Complex.I * (t : ℂ) by ring]
    exact he
  have hb : b = -(Complex.I * (t : ℂ)) := by
    dsimp only [b]
    rw [← hx, Complex.ofReal_neg]
    ring
  let P (z : ℂ) := (z + b) * (1 - z - b)
  have hP (s : ℂ) : AnalyticAt ℂ P s := by
    dsimp only [P]
    fun_prop
  have hD (s : ℂ) : HasDerivAt P ((1 - s - b) - (s + b)) s := by
    simpa [P, sub_eq_add_neg] using ((hasDerivAt_id s).add_const b).fun_mul
      (((hasDerivAt_const s (1 : ℂ)).fun_sub (hasDerivAt_id s)).sub_const b)
  have hmer : MeromorphicOn (P * L) univ :=
    fun s hs ↦ (hP s).meromorphicAt.mul (hL hs).meromorphicAt
  have cancel (s : ℂ) (hz : P s = 0) (hd : (1 - s - b) - (s + b) ≠ 0)
      (hord : meromorphicOrderAt L s = -1) : toMeromorphicNFOn (P * L) univ s ≠ 0 := by
    have h1 := (hP s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz (by rwa [(hD s).deriv])
    apply (meromorphicNFOn_toMeromorphicNFOn (P * L) univ (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ s),
      meromorphicOrderAt_mul (hP s).meromorphicAt (hL (mem_univ s)).meromorphicAt,
      (hP s).meromorphicOrderAt_eq, h1, hord]
    norm_num
  change toMeromorphicNFOn _ univ (-b) ≠ 0 ∧ toMeromorphicNFOn _ univ (1 - b) ≠ 0
  simp only [ite_eq_left hχ, pow_one]
  refine ⟨cancel _ (by dsimp only [P]; ring) (by ring_nf <;> norm_num) ?_,
    cancel _ (by dsimp only [P]; ring) (by ring_nf <;> norm_num) ?_⟩
  · simpa [hb] using hzero
  · simpa [hb] using hone

/-- Paper: Equation (7.1.4.4), p. 326.
Evaluation of the m-th complex derivative at a point defines a continuous linear
functional in the compact-open topology. -/
theorem entireJet_properties (ρ : ℂ) (m : ℕ) :
    let jet (f : Entire) := iteratedDeriv m (f.val : ℂ → ℂ) ρ
    (∀ f g : Entire, jet (f + g) = jet f + jet g) ∧
      (∀ (a : ℂ) (f : Entire), jet (a • f) = a • jet f) ∧ Continuous jet := by
  dsimp only
  have hd (f : Entire) : Differentiable ℂ (f.val : ℂ → ℂ) := f.property
  refine ⟨fun f g ↦ iteratedDeriv_add (hd f).contDiff.contDiffAt (hd g).contDiff.contDiffAt,
    fun a f ↦ iteratedDeriv_const_smul_field a (f.val : ℂ → ℂ), ?_⟩
  apply continuous_iff_continuousAt.mpr
  intro f
  have hlim (n : ℕ) : TendstoLocallyUniformlyOn
      (fun g : Entire ↦ iteratedDeriv n (g.val : ℂ → ℂ))
      (iteratedDeriv n (f.val : ℂ → ℂ)) (𝓝 f) univ := by
    induction n with
    | zero =>
      exact tendstoLocallyUniformlyOn_univ.mpr
        (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
          (show Tendsto (fun g : Entire ↦ g.val) (𝓝 f) (𝓝 f.val) from
            continuous_subtype_val.continuousAt))
    | succ n ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Filter.Eventually.of_forall fun g ↦
          ((hd g).contDiff.differentiable_iteratedDeriv' n).differentiableOn) isOpen_univ
  exact (hlim m).tendsto_at (mem_univ ρ)

/-- Paper: Equation (7.1.4.4), p. 326.
The jet functional takes the m-th derivative of an entire function at the indicated point. -/
def entireJet (ρ : ℂ) (m : ℕ) : StrongDual ℂ Entire where
  toFun f := iteratedDeriv m (f.val : ℂ → ℂ) ρ
  map_add' := (entireJet_properties ρ m).1
  map_smul' := (entireJet_properties ρ m).2.1
  cont := (entireJet_properties ρ m).2.2

/-- Paper: Equation (7.1.4.4), p. 326.
The functional evaluates the prescribed complex derivative.
Deviation: Its evaluation law is the sanity check for the bundled functional. -/
theorem entireJet_apply (ρ : ℂ) (m : ℕ) (f : Entire) :
    entireJet ρ m f = iteratedDeriv m (f.val : ℂ → ℂ) ρ := rfl

/-- Paper: Equation (7.1.4.3), p. 326.
The jet space at a zero of multiplicity n is spanned by evaluations of the first n
derivatives, beginning with the value. It inherits the topology of the strong dual. -/
def entireJetSpace (ρ : ℂ) (n : ℕ) : Submodule ℂ (StrongDual ℂ Entire) :=
  Submodule.span ℂ (range fun m : Fin n ↦ entireJet ρ m.val)

/-- Paper: Equation (7.1.4.3), p. 326.
There are exactly n independent jet coordinates at a point for order n.
Deviation: States the dimension check for the span used in the definition. -/
theorem entireJetSpace_finrank (ρ : ℂ) (n : ℕ) :
    Module.finrank ℂ (entireJetSpace ρ n) = n := by
  classical
  let J (i : Fin n) := entireJet ρ i.val
  have hJ : LinearIndependent ℂ J := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    let p : Entire := ⟨⟨fun z ↦ (z - ρ) ^ i.val, by fun_prop⟩,
      (differentiable_id.sub (differentiable_const ρ)).pow _⟩
    have hp (j : Fin n) : J j p = if j = i then (i.val.factorial : ℂ) else 0 := by
      change iteratedDeriv j.val (fun z : ℂ ↦ (z - ρ) ^ i.val) ρ = _
      simp only [iteratedDeriv_comp_sub_const (f := fun z : ℂ ↦ z ^ i.val), sub_self,
        iteratedDeriv_fun_pow_zero, Fin.val_inj, apply_ite Nat.cast, Nat.cast_zero]
    have h := congrArg (fun ℓ : StrongDual ℂ Entire ↦ ℓ p) hc
    simp only [sum_apply, smul_apply,
      hp, zero_apply, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast Nat.factorial_ne_zero i.val)
  change Module.finrank ℂ (Submodule.span ℂ (range J)) = n
  exact (finrank_span_eq_card hJ).trans (Fintype.card_fin n)

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The annihilator of a principal ideal consists of the continuous linear functionals
that vanish on that ideal. Its topology is inherited from the strong dual. -/
def entireIdealAnnihilator (g : Entire) : Submodule ℂ (StrongDual ℂ Entire) :=
  ((Ideal.span ({g} : Set Entire)).restrictScalars ℂ).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ)

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The annihilator for the constant unit generator is zero.
Deviation: States a sanity check for the annihilator. -/
theorem entireIdealAnnihilator_one : entireIdealAnnihilator 1 = ⊥ := by
  ext φ
  simp only [entireIdealAnnihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator, Submodule.mem_bot]
  have hmem : ∀ w : Entire, w ∈ Submodule.restrictScalars ℂ (Ideal.span ({1} : Set Entire)) := by
    intro w
    simp [Ideal.span_singleton_one]
  constructor
  · intro h
    ext w
    simpa using h w (hmem w)
  · intro h w _
    simp [h]

-- TODO(paper-gap): In (7.1.4.2) the product is the quotient's model, while the
-- continuous dual consists of finite-support jets as computed on p. 328.
-- The proof's second pole-removing factor also has the wrong sign of ix₀.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
  (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)

open Classical in
/-- Paper: Theorem 7.1.4.2(1), pp. 326–328.
The strong annihilator of the regularized Hecke ideal is the locally convex direct
sum of the jet spaces of the completed Hecke zeros.
Deviation: Uses the direct sum computed in the proof. A zero is detected by positive
meromorphic order, since a pole can have value zero in meromorphic normal form. -/
theorem spectralAnnihilator_directSum :
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    let Zeros := {ρ : ℂ // 0 < meromorphicOrderAt L ρ}
    let J (ρ : Zeros) := entireJetSpace ρ.val (meromorphicOrderAt L ρ.val).untop₀.toNat
    letI instJetAddSec1b : ∀ ρ : Zeros, AddCommGroup ↥(J ρ) :=
      fun ρ ↦ Submodule.addCommGroup (J ρ)
    letI instJetModuleSec1b : ∀ ρ : Zeros, Module ℂ ↥(J ρ) :=
      fun ρ ↦ Submodule.module (J ρ)
    let inclusion := DirectSum.lof ℂ Zeros (fun ρ ↦ ↥(J ρ))
    letI instJetSumTopologySec1b : TopologicalSpace (⨁ ρ : Zeros, ↥(J ρ)) :=
      locallyConvexFinalTopology inclusion
    ∃ e : (⨁ ρ : Zeros, ↥(J ρ)) ≃L[ℂ] entireIdealAnnihilator Λ,
      ∀ (ρ : Zeros) (a : ↥(J ρ)), (e (inclusion ρ a)).val = a.val := by sorry

/-- Paper: Theorem 7.1.4.2(2), p. 326.
An entire Schwartz–Bergman function includes continuously into the compact-open space
by keeping its value at each point. -/
theorem exists_schwartzBergman_entireInclusion :
    ∃ i : Aℂ →L[ℂ] Entire, ∀ (f : Aℂ) (z : ℂ), (i f).val z = f.val z := by sorry

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327. The canonical map includes entire
Schwartz–Bergman functions into the compact-open space of entire functions. -/
def schwartzBergmanEntireInclusion : Aℂ →L[ℂ] Entire :=
  exists_schwartzBergman_entireInclusion.choose

/-- Paper: Theorem 7.1.4.2(2), p. 326. Inclusion preserves the value at every point. -/
theorem schwartzBergmanEntireInclusion_apply (f : Aℂ) (s : ℂ) :
    (schwartzBergmanEntireInclusion f).val s = f.val s :=
  exists_schwartzBergman_entireInclusion.choose_spec f s

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327. The preimage of the entire principal
ideal consists of the Schwartz–Bergman functions divisible by its generator. -/
def schwartzBergmanDivisible (g : Entire) : Submodule ℂ Aℂ :=
  ((Ideal.span ({g} : Set Entire)).restrictScalars ℂ).comap
    schwartzBergmanEntireInclusion.toLinearMap

/-- An entire function is divisible by `g` exactly when it vanishes to at least the order of
`g` at every point. In that case the normalized quotient gives an entire factor. -/
private theorem schwartzBergmanDivisible_isClosed_dvd (g f : Entire) :
    g ∣ f ↔ ∀ z, analyticOrderAt (g.val : ℂ → ℂ) z ≤ analyticOrderAt (f.val : ℂ → ℂ) z := by
  have ha (a : Entire) (z : ℂ) : AnalyticAt ℂ (a.val : ℂ → ℂ) z :=
    (show Differentiable ℂ a.val from a.property).analyticAt z
  constructor
  · rintro ⟨k, rfl⟩ z
    change _ ≤ analyticOrderAt ((g.val : ℂ → ℂ) * (k.val : ℂ → ℂ)) z
    rw [analyticOrderAt_mul (ha g z) (ha k z)]
    exact self_le_add_right _ _
  · intro hord
    let q := (f.val : ℂ → ℂ) / (g.val : ℂ → ℂ)
    have hq : MeromorphicOn q univ := fun z _ ↦ (ha f z).meromorphicAt.div (ha g z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (ha f z).meromorphicAt (ha g z).meromorphicAt,
        (ha f z).meromorphicOrderAt_eq, (ha g z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt (f.val : ℂ → ℂ) z = m at hle ⊢
      generalize analyticOrderAt (g.val : ℂ → ℂ) z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨⟨⟨_, hdiff.continuous⟩, hdiff⟩, Subtype.ext (ContinuousMap.ext fun z ↦ ?_)⟩
    change f.val z = g.val z * toMeromorphicNFOn q univ z
    by_cases hz : g.val z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((ha g z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (ha f z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((ha f z).div (ha g z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- A principal ideal of entire functions is the intersection of its vanishing jet kernels. -/
private theorem schwartzBergmanDivisible_isClosed_span (g : Entire) :
    IsClosed (Ideal.span ({g} : Set Entire) : Set Entire) := by
  have heq : (Ideal.span ({g} : Set Entire) : Set Entire) =
      ⋂ (z : ℂ) (n : ℕ) (_ : (n : ℕ∞) ≤ analyticOrderAt (g.val : ℂ → ℂ) z)
        (i : ℕ) (_ : i < n), ((entireJet z i).ker : Set Entire) := by
    ext f
    simp only [SetLike.mem_coe, Ideal.mem_span_singleton,
      schwartzBergmanDivisible_isClosed_dvd, mem_iInter, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, entireJet_apply]
    apply forall_congr'
    intro z
    rw [← ENat.forall_natCast_le_iff_le]
    simp_rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((show Differentiable ℂ f.val from f.property).analyticAt z)]
  rw [heq]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ (entireJet z i).isClosed_ker

/-- Paper: Theorem 7.1.4.2(2), pp. 326–328. Divisibility defines a closed subspace,
so its quotient with the Schwartz–Bergman quotient topology is Hausdorff. -/
theorem schwartzBergmanDivisible_isClosed (g : Entire) :
    IsClosed (schwartzBergmanDivisible g : Set Aℂ) :=
  (schwartzBergmanDivisible_isClosed_span g).preimage schwartzBergmanEntireInclusion.continuous

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327 and Theorem 7.1.4.3(2), p. 331.
Restriction to Schwartz–Bergman functions induces an injective map with dense image
in the strong dual of the quotient by the corresponding divisibility conditions.
Deviation: States the analytic restriction map for every entire generator. -/
theorem exists_schwartzBergman_jetRestriction (g : Entire) :
    ∃ U : ↥(entireIdealAnnihilator g) →L[ℂ] StrongDual ℂ (Aℂ ⧸ schwartzBergmanDivisible g),
      Injective U ∧ DenseRange U ∧ ∀ (ℓ : entireIdealAnnihilator g) (f : Aℂ),
        U ℓ (Submodule.Quotient.mk f) = ℓ.val (schwartzBergmanEntireInclusion f) := by sorry

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327. The range identification from
the global converse transports restriction to the dual of the theta Mellin quotient.
Deviation: The range equality from §6.3.2 is an explicit hypothesis. -/
theorem spectralTheta_jetRestriction_of_range_eq :
    let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
    let g := regularizedCompletedHeckeL χ τ hτ L hL hEq
    LinearMap.range Z.toLinearMap = schwartzBergmanDivisible g →
      ∃ U : ↥(entireIdealAnnihilator g) →L[ℂ] StrongDual ℂ (Aℂ ⧸ LinearMap.range Z.toLinearMap),
        Injective U ∧ DenseRange U ∧ ∀ (ℓ : entireIdealAnnihilator g) (f : Aℂ),
          U ℓ (Submodule.Quotient.mk f) = ℓ.val (schwartzBergmanEntireInclusion f) := by
  intro Z g h
  rw [h]
  exact exists_schwartzBergman_jetRestriction g

-- TODO(paper-gap): In (7.1.4.6), with φ already in the Mellin coordinate, the
-- factor t^(ix₀) shifts the derivative to ρ + ix₀. The proof on p. 329 uses t^ρ.

/-- Paper: Equations (7.1.4.6) and (7.1.4.27), pp. 327, 329 and 331.
On the Schwartz–Bergman space, jet evaluation is a logarithmic moment of the inverse
Mellin transform. Both the inverse integral at positive t and the moment converge.
Deviation: Uses the exponent ρ from the derivation on p. 329 and the orbital formula. -/
theorem schwartzBergman_jet_eq_mellinInv_moment (f : Aℂ) (ρ : ℂ) (m : ℕ) :
    let φ : ℂ → ℂ := f.val
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ m * mellinInv 0 φ t
    Complex.VerticalIntegrable φ 0 ∧ MellinConvergent moment ρ.re ∧
      iteratedDeriv m φ ρ = mellin moment ρ := by sorry

-- TODO(paper-gap): Theorem 7.1.4.2(4) names the ordinary Schwartz quotient, whereas
-- the setup and argument use the exponentially decaying quotient. Theorem
-- 7.1.4.3(3) makes the same switch before (7.1.4.28).

/-- Paper: Theorem 7.1.4.2(4), pp. 327, 330–331. On the entire Schwartz–Bergman
space the factorial-normalized derivatives across the closed critical strip are
equicontinuous and bounded in the strong dual.
Deviation: States the estimate on the Mellin side for all derivative orders. -/
theorem schwartzBergman_normalizedJets :
    let jets := fun i : {z : ℂ // z.re ∈ Icc 0 1} × ℕ ↦
      (i.2.factorial : ℂ)⁻¹ • (entireJet i.1.val i.2).comp schwartzBergmanEntireInclusion
    Equicontinuous (fun i (f : Aℂ) ↦ jets i f) ∧
      Bornology.IsVonNBounded ℂ (range jets) := by sorry

-- TODO(paper-gap): Theorem 7.1.4.3(1) misses collisions across rational primes.
-- At s = 0 for the trivial character of ℚ with 2 and 3 removed, the orbital
-- generator has a double zero. The separate p-blocks supply only evaluation at 0.
-- Part (3) also omits the pole-removing polynomial when indexing its jets:
-- with just 2 removed, (1 - 2⁻ˢ)L(s,1) has order zero at the origin.

/-- Paper: Theorem 7.1.4.3(1), pp. 331–332.
The finite Euler correction multiplies the regularized completed L-function by the
reciprocal factors of the selected places, with factor one at ramified places. -/
theorem orbitalHeckeGenerator_differentiable (S₀ : Finset Primes) :
    Differentiable ℂ (fun s ↦
      reciprocalPartialHeckeEulerProduct χ S₀ s *
        (regularizedCompletedHeckeL χ τ hτ L hL hEq).val s) := by
  classical
  refine Differentiable.mul ?_ (regularizedCompletedHeckeL χ τ hτ L hL hEq).property
  unfold reciprocalPartialHeckeEulerProduct
  apply Differentiable.fun_finsetProd
  intro v _
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · simp only [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    exact (differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_id.neg.const_cpow (.inl hq)))
  · simp only [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
    exact differentiable_const _

/-- Paper: Theorem 7.1.4.3(1), p. 331.
The entire generator of the orbital ideal is the finite Euler correction of the regularized
completed Hecke L-function. -/
def orbitalHeckeGenerator (S₀ : Finset Primes) : Entire :=
  let g := fun s ↦ reciprocalPartialHeckeEulerProduct χ S₀ s *
    (regularizedCompletedHeckeL χ τ hτ L hL hEq).val s
  let hg := orbitalHeckeGenerator_differentiable χ τ hτ L hL hEq S₀
  ⟨⟨g, hg.continuous⟩, hg⟩

/-- Paper: Theorem 7.1.4.3(1), p. 331.
Removing an empty set of Euler factors recovers the spectral generator.
Deviation: States a sanity check for the orbital ideal generator. -/
theorem orbitalHeckeGenerator_empty :
    orbitalHeckeGenerator χ τ hτ L hL hEq ∅ = regularizedCompletedHeckeL χ τ hτ L hL hEq :=
  by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  simp [orbitalHeckeGenerator, reciprocalPartialHeckeEulerProduct]

private theorem orbitalHeckeGenerator_order_at_canceled_pole_factor (χ : U𝔽) (b : ℂ)
    (hχ : ∀ g : C𝔽, (χ g : ℂ) = (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ b)
    (v : Primes) (s : ℂ) :
    (finiteHeckeEulerFactor χ v s)⁻¹ = 1 - (v.asIdeal.absNorm : ℂ) ^ (-(s + b)) := by
  classical
  have hval (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ 0).restrict v u = (‖(u : v.adicCompletion F)‖ : ℂ) ^ b := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u
    change (χ g : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one, hχ,
      show ideleClassNorm F g = _ from ideleClassNorm_ofAdicCompletion F v u]
    rfl
  have hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist χ 0).restrict v u = 1
    rw [hval, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hn : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [finiteHeckeEulerFactor, ite_eq_left hu, inv_inv, hu.localValue_eq u hπ, hval, hn,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) b, ← Complex.cpow_neg,
    Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq, neg_add, add_comm (-b)]

/-- Paper: Theorem 7.1.4.3(1), pp. 331–332. At the canceled pole on the
imaginary axis of a pure norm power, every removed finite place adds one jet.
Deviation: Records the total order at a point where indexing by the raw product loses a jet. -/
theorem orbitalHeckeGenerator_order_at_canceled_pole (S₀ : Finset Primes)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    analyticOrderAt (g.val : ℂ → ℂ) (-((x : ℂ) * Complex.I)) = (S₀.card : ℕ∞) := by
  classical
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (x : ℂ) * Complex.I
  have hpower (g : C𝔽) : (χ g : ℂ) = (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ b := by
    let t := ideleClassNorm F g
    let k : C𝔽 := QuotientGroup.mk (τ t)
    have hk : ideleClassNorm F k = t := hτ t
    have hg : g / k ∈ (ideleClassNorm F).ker := by simp [MonoidHom.mem_ker, hk, t]
    have h1 : χ (g / k) = 1 := DFunLike.congr_fun hχ (⟨_, hg⟩ : (ideleClassNorm F).ker)
    have he : χ g = χ k := div_eq_one.mp ((map_div χ g k).symm.trans h1)
    rw [he]
    exact (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose_spec t
  let G (T : Finset Primes) : ℂ → ℂ := (orbitalHeckeGenerator χ τ hτ L hL hEq T).val
  change analyticOrderAt (G S₀) (-b) = _
  induction S₀ using Finset.induction_on with
  | empty =>
    change analyticOrderAt ((orbitalHeckeGenerator χ τ hτ L hL hEq ∅).val : ℂ → ℂ) (-b) = 0
    rw [orbitalHeckeGenerator_empty]
    exact analyticOrderAt_eq_zero.mpr (.inr
      (regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L hL hEq hχ).1)
  | @insert v T hv ih =>
    let q : ℂ := v.asIdeal.absNorm
    let f (s : ℂ) := 1 - q ^ (-(s + b))
    have hq : q ≠ 0 := by
      dsimp only [q]
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    have hlog : Complex.log q ≠ 0 := by
      dsimp only [q]
      rw [← Complex.natCast_log]
      exact_mod_cast (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).ne'
    have hdiff : Differentiable ℂ f :=
      (differentiable_const _).sub (((differentiable_id.add_const b).neg).const_cpow (.inl hq))
    have hder : HasDerivAt f (Complex.log q) (-b) := by
      simpa [f] using (hasDerivAt_const (-b) (1 : ℂ)).fun_sub
        ((((hasDerivAt_id (-b)).add_const b).neg).const_cpow (.inl hq))
    have ho := (hdiff.analyticAt (-b)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp [f]) (hder.deriv ▸ hlog)
    have hmul : G (insert v T) = f * G T := by
      funext s
      change (∏ w ∈ insert v T, (finiteHeckeEulerFactor χ w s)⁻¹) * _ = f s * ((∏ w ∈ T, _) * _)
      rw [Finset.prod_insert hv, mul_assoc,
        orbitalHeckeGenerator_order_at_canceled_pole_factor χ b hpower]
    have hG : Differentiable ℂ (G T) := (orbitalHeckeGenerator χ τ hτ L hL hEq T).property
    rw [hmul, analyticOrderAt_mul (hdiff.analyticAt _) (hG.analyticAt _), ho, ih,
      Finset.card_insert_of_notMem hv, Nat.cast_add_one, add_comm]

open Classical in
/-- Paper: Theorem 7.1.4.3(1), p. 331.
The strong annihilator of the orbital ideal is a locally convex direct sum of jets.
Deviation: Counts zeros of the regularized generator of the ideal in part (1),
adding all coincident local orders even at a canceled pole of the completed L-function.
Uses the locally convex direct sum from p. 328. -/
theorem orbitalAnnihilator_directSum (S₀ : Finset Primes) :
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let Zeros := {ρ : ℂ // 0 < analyticOrderAt (g.val : ℂ → ℂ) ρ}
    let J (ρ : Zeros) := entireJetSpace ρ.val (analyticOrderAt (g.val : ℂ → ℂ) ρ.val).toNat
    letI instJetAddSec1b : ∀ ρ : Zeros, AddCommGroup ↥(J ρ) :=
      fun ρ ↦ Submodule.addCommGroup (J ρ)
    letI instJetModuleSec1b : ∀ ρ : Zeros, Module ℂ ↥(J ρ) :=
      fun ρ ↦ Submodule.module (J ρ)
    let inclusion := DirectSum.lof ℂ Zeros (fun ρ ↦ ↥(J ρ))
    letI instJetSumTopologySec1b : TopologicalSpace (⨁ ρ : Zeros, ↥(J ρ)) :=
      locallyConvexFinalTopology inclusion
    ∃ e : (⨁ ρ : Zeros, ↥(J ρ)) ≃L[ℂ] entireIdealAnnihilator g,
      ∀ (ρ : Zeros) (a : ↥(J ρ)), (e (inclusion ρ a)).val = a.val := by sorry

open Classical in
/-- Paper: Theorem 7.1.4.2(3), p. 327 and Theorem 7.1.4.3(3), pp. 331–332.
The derivative functionals of the regularized generator have biorthogonal
Schwartz–Bergman representatives. Their classes work in the divisibility quotient.
Deviation: The empty set gives the spectral family. The indices use the total
order of the regularized generator, including at canceled poles. -/
theorem orbitalSchwartzBergman_biorthogonal (S₀ : Finset Primes) :
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let indices := {p : ℂ × ℕ // (p.2 : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) p.1}
    ∃ b : indices → Aℂ, ∀ i j : indices,
      iteratedDeriv i.val.2 (b j).val i.val.1 = if i = j then 1 else 0 := by sorry

-- TODO(prerequisite): Transport the analytic quotient and its jet families to
-- (7.1.4.7) by §6.3.2. The orbital identification (7.1.4.26)–(7.1.4.28)
-- also uses the global principal-value operator of §5.3.1.

end Spectral

end RiemannMasullo
