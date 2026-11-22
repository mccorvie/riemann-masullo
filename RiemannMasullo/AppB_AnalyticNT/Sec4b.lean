module

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec4a
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Topology.Algebra.IsOpenUnits
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a

/-!
# Explicit formulas for Hecke L-functions

Masullo, §§B.4.2–B.4.4, pp. 614–626. The Schwartz test on the positive
real line is written in its logarithmic coordinate.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "halfPlane" => (Complex.re ⁻¹' Ioi (1 : ℝ))
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0
local notation "logMellin" => (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

section MellinExplicitFormula

-- TODO(paper-gap): The unnumbered residue identity on p. 614 reverses the
-- signs in (B.4.2.2). Poles are present only for norm characters and may be shifted.

/-- Paper: §B.4.2.1, p. 614. The logarithmic derivative of the completed
function has slow growth near its poles on the strip used for the residue formula.
Deviation: Uses the repaired height bounds of Definition B.3.1.1. -/
theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv (χ : U[F]) (L : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (_ha : 1 < a) (_haMax : a ≤ 2) :
    HasSlowGrowthNearPoles (logDeriv L) (1 - a) a := by sorry

/-- Paper: Equation (B.4.2.2), p. 614. The right vertical integral minus the
left vertical integral is the signed divisor sum of Mellin values.
Deviation: The meromorphic order includes the actual poles and zero multiplicities.
The unordered sum strengthens the rectangular limit and uses zero counting for fixed χ. -/
theorem hasSum_heckeAsymptoticResidue (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (_ha : 1 < a) (_haMax : a ≤ 2) :
    let H := fun s ↦ logMellin f s * logDeriv L s
    Complex.VerticalIntegrable H a ∧ Complex.VerticalIntegrable H (1 - a) ∧
      HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f ρ)
        ((verticalLineIntegral H a - verticalLineIntegral H (1 - a)) / twoPiI) := by sorry

-- TODO(paper-gap): (B.4.2.3) misses the chain-rule sign. The page specifies
-- Aχ, but the identification ε'/ε = log Aχ needs the conductor calculation.
-- The normalized integral of Φ in (B.4.2.4) gives the test value at one.

local notation "conductorExponents(" χ ", " v ")" =>
  ({n : ℕ | ∀ u : (HeightOneSpectrum.adicCompletion F v)ˣ, ‖u.val‖ = 1 →
    ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ)) →
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1} : Set ℕ)

/-- Paper: Equation (B.4.2.3), p. 614. Each finite local character has
a least conductor exponent, and only finitely many exponents are nonzero.
Deviation: The exponent is given by the local unit filtration of §3.3.1. -/
theorem exists_heckeConductorExponents (χ : U[F]) :
    ∃ n : Primes(F) → ℕ, (Function.support n).Finite ∧
      ∀ v, IsLeast (conductorExponents(χ, v)) (n v) := by
  classical
  have hlocal (v : Primes(F)) : (conductorExponents(χ, v)).Nonempty := by
    let η : (v.adicCompletion F)ˣ →ₜ* Circle := χ.comp
      ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩
    have harc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
      simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
    have hpre : η ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : (v.adicCompletion F)ˣ) :=
      η.continuous.continuousAt.preimage_mem_nhds (by
        change Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (η 1)
        rwa [map_one])
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hpre
    obtain ⟨W, hW, hsub⟩ := mem_comap.mp hpre
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
    have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hq)
    refine ⟨n, fun u hu hclose ↦ ?_⟩
    -- Every power stays close to one, so its character lies in the same half circle.
    change η u = 1
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro k _
    rw [← map_pow]
    apply hsub
    apply hball
    change dist (u.val ^ k) 1 < r
    rw [dist_eq_norm]
    apply (local_unit_pow_bound u.val hu.le k).trans_lt
    exact hclose.trans_lt (by simpa only [zpow_neg, zpow_natCast, inv_pow] using hn)
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have hcover : c ∈ ⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set _) := by
    rw [iUnion_unramifiedOutside]
    exact mem_univ _
  obtain ⟨T, hT⟩ := mem_iUnion.mp hcover
  refine ⟨fun v ↦ sInf (conductorExponents(χ, v)), T.finite_toSet.subset ?_,
    fun v ↦ ⟨Nat.sInf_mem (hlocal v), fun _ hn ↦ Nat.sInf_le hn⟩⟩
  intro v hv
  by_contra hvT
  have hzero : 0 ∈ conductorExponents(χ, v) := by
    intro u hu _
    have hunit : u ∈ (v.adicCompletionIntegers F).units :=
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
        (Valued.toNormedField.norm_eq_one_iff.mp hu)
    let u' := (v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType ⟨u, hunit⟩
    have h := (mem_unramifiedOutside_iff F T c).mp hT v hvT u'
    exact Subtype.ext h
  exact hv (Nat.eq_zero_of_le_zero (Nat.sInf_le hzero))

/-- Paper: Equation (B.4.2.3), p. 614. The logarithm of the
discriminant–conductor product adds the finite conductor exponents weighted by log prime norm.
Deviation: The conductor exponent is given by the local unit filtration of §3.3.1. -/
def heckeLogDiscriminantConductor (χ : U[F]) : ℝ :=
  Real.log (Int.natAbs (NumberField.discr F)) +
    ∑ᶠ v : Primes(F), Real.log q(v) * (sInf (conductorExponents(χ, v)) : ℕ)

/-- Paper: Equation (B.4.2.3), p. 614. The trivial character has only the
discriminant contribution. -/
theorem heckeLogDiscriminantConductor_one :
    heckeLogDiscriminantConductor (1 : U[F]) =
      Real.log (Int.natAbs (NumberField.discr F)) := by
  simp [heckeLogDiscriminantConductor]

/-- Paper: Equation (B.4.2.3), p. 614. The reflected logarithmic derivative
and the discriminant–conductor term give the logarithmic derivative of the continuation.
Deviation: Both terms acquire the minus signs dictated by the functional equation
in Proposition 3.2.1.3(3). The order hypothesis excludes zeros and poles. -/
theorem completedHeckeL_logDeriv_reflection (χ : U[F]) (L Ldual : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (_hLdual : MeromorphicNFOn Ldual univ)
    (_hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s)
    (s : ℂ) (_hs : meromorphicOrderAt L s = 0) :
    logDeriv L s = -logDeriv Ldual (1 - s) - (heckeLogDiscriminantConductor χ : ℂ) := by sorry

-- TODO(paper-gap): In (B.4.2.15) a compactly supported logarithmic profile
-- with f(0) = 1 leaves Nᵥ/x at infinity. The gamma arguments also omit
-- the sign parity or angular weight. With the printed negative αᵥ on p. 616,
-- the constant in (B.4.2.12) should be +αᵥ. The digamma integral below includes
-- the parity or angular weight and the gamma prefactor.

/-- Paper: Proposition B.4.2.1, p. 616. The combined digamma integrand uses
the gamma arguments of the two local characters and the positive and negative
samples of the logarithmic test.
Deviation: The subtraction uses Euler's convergent digamma kernel. -/
def heckeArchimedeanDigammaKernel (k : ℝ) (zPlus zMinus : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (k : ℂ) * (2 * (Real.exp (-t) : ℂ) * f 0 / (t : ℂ) -
    (f (k * t) * Complex.exp (-zPlus * (t : ℂ)) +
      f (-(k * t)) * Complex.exp (-zMinus * (t : ℂ))) / (1 - (Real.exp (-t) : ℂ)))

section GaussDigamma

open Real

/-- The factor `1 / t - 1 / (1 - e^{-t})` lies in `[-1, 0]` for positive `t`. -/
private lemma digamma_remainder_bounds {t : ℝ} (ht : 0 < t) :
    -1 ≤ 1 / t - 1 / (1 - exp (-t)) ∧ 1 / t - 1 / (1 - exp (-t)) ≤ 0 := by
  have hq : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - exp (-t) := by linarith
  have h1 : 1 - exp (-t) ≤ t := by linarith [add_one_le_exp (-t)]
  have h2 : t * exp (-t) ≤ 1 - exp (-t) := by
    have h := add_one_le_exp t
    have he : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos (-t)]
  constructor
  · rw [div_sub_div _ _ ht.ne' hd.ne', le_div_iff₀ (mul_pos ht hd)]
    nlinarith
  · rw [sub_nonpos]
    exact one_div_le_one_div_of_le hd h1

/-- The real Gauss kernel `e^{-t}/t - e^{-t}/(1 - e^{-t})` of `ψ(1)`. -/
private noncomputable def gaussDigammaKernel (t : ℝ) : ℝ :=
  exp (-t) / t - exp (-t) / (1 - exp (-t))

private lemma exp_neg_natCast_mul (m : ℕ) (t : ℝ) : exp (-((m : ℝ) * t)) = exp (-t) ^ m := by
  rw [← exp_nat_mul]
  ring_nf

/-- Splitting off the first `n` terms of the geometric series. -/
private lemma gaussDigammaKernel_eq (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussDigammaKernel t =
      t⁻¹ * (exp (-(1 * t)) - exp (-(((n + 1 : ℕ) : ℝ) * t))) -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t))) := by
  have hq : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 1 - exp (-t) ≠ 0 := by linarith
  simp only [exp_neg_natCast_mul, one_mul, gaussDigammaKernel]
  set q := exp (-t)
  have hgeom : (∑ i ∈ Finset.range n, q ^ (i + 1)) * (1 - q) = q - q ^ (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have hsum : ∑ i ∈ Finset.range n, q ^ (i + 1) = (q - q ^ (n + 1)) / (1 - q) := by
    rw [← hgeom, mul_div_cancel_right₀ _ hd]
  rw [hsum]
  field_simp
  ring

private lemma integrableOn_exp_neg_natCast_mul (m : ℕ) (hm : 0 < m) :
    IntegrableOn (fun t : ℝ ↦ exp (-((m : ℝ) * t))) (Ioi 0) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -(m : ℝ)) (by simp [hm]) 0

private lemma integral_exp_neg_natCast_mul (m : ℕ) (hm : 0 < m) :
    ∫ t in Ioi (0 : ℝ), exp (-((m : ℝ) * t)) = 1 / m := by
  have := integral_exp_mul_Ioi (a := -(m : ℝ)) (by simp [hm]) 0
  simp only [neg_mul, mul_zero, exp_zero] at this
  rw [this]
  field_simp

private lemma integrableOn_gaussDigammaKernel : IntegrableOn gaussDigammaKernel (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_Ioi 0) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have hd : 1 - exp (-t) ≠ 0 := by
      have : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
      linarith
    have ht' : t ≠ 0 := ht.ne'
    unfold gaussDigammaKernel
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_)
    have ht : (0 : ℝ) < t := ht
    obtain ⟨h1, h2⟩ := digamma_remainder_bounds ht
    have : gaussDigammaKernel t = exp (-t) * (1 / t - 1 / (1 - exp (-t))) := by
      unfold gaussDigammaKernel; ring
    rw [this, norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
    have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
    nlinarith [exp_pos (-t)]

private lemma integral_gaussDigammaKernel :
    ∫ t in Ioi (0 : ℝ), gaussDigammaKernel t = -eulerMascheroniConstant := by
  set I := ∫ t in Ioi (0 : ℝ), gaussDigammaKernel t
  -- The remainder after `n` geometric terms.
  let R : ℕ → ℝ := fun n ↦
    ∫ t in Ioi (0 : ℝ), exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))
  have hRint : ∀ n : ℕ, IntegrableOn
      (fun t ↦ exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) (Ioi 0) := by
    intro n
    refine Integrable.mono' (integrableOn_exp_neg_natCast_mul (n + 1) n.succ_pos) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht : (0 : ℝ) < t := ht
      have hd : 1 - exp (-t) ≠ 0 := by
        have : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
        linarith
      have ht' : t ≠ 0 := ht.ne'
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_)
      obtain ⟨h1, h2⟩ := digamma_remainder_bounds (show (0 : ℝ) < t from ht)
      rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
      have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
      nlinarith [exp_pos (-(((n + 1 : ℕ) : ℝ) * t))]
  have hRle : ∀ n : ℕ, ‖R n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    calc ‖R n‖ ≤ ∫ t in Ioi (0 : ℝ), exp (-(((n + 1 : ℕ) : ℝ) * t)) := by
          refine norm_integral_le_of_norm_le (integrableOn_exp_neg_natCast_mul (n + 1) n.succ_pos)
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_))
          obtain ⟨h1, h2⟩ := digamma_remainder_bounds (show (0 : ℝ) < t from ht)
          rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
          have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
          nlinarith [exp_pos (-(((n + 1 : ℕ) : ℝ) * t))]
      _ = 1 / ((n : ℝ) + 1) := by
          rw [integral_exp_neg_natCast_mul (n + 1) n.succ_pos]; push_cast; rfl
  -- The finite expansion of the integral.
  have hexp : ∀ n : ℕ, I = -(harmonic n - log ((n : ℝ) + 1)) + R n := by
    intro n
    have hsumint : ∀ i ∈ Finset.range n,
        IntegrableOn (fun t : ℝ ↦ exp (-(((i + 1 : ℕ) : ℝ) * t))) (Ioi 0) :=
      fun i _ ↦ integrableOn_exp_neg_natCast_mul (i + 1) i.succ_pos
    have hsumint' : IntegrableOn
        (fun t : ℝ ↦ ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) (Ioi 0) :=
      integrable_finsetSum _ hsumint
    let Fr : ℝ → ℝ := fun t ↦ t⁻¹ * (exp (-(1 * t)) - exp (-(((n + 1 : ℕ) : ℝ) * t)))
    have hFr : EqOn Fr (fun t ↦ gaussDigammaKernel t +
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) -
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) (Ioi 0) := by
      intro t ht
      simp only [Fr, gaussDigammaKernel_eq n (show (0 : ℝ) < t from ht)]
      ring
    have hFrint : IntegrableOn Fr (Ioi 0) :=
      ((integrableOn_gaussDigammaKernel.add hsumint').sub (hRint n)).congr_fun hFr.symm
        measurableSet_Ioi
    have hFrval : ∫ t in Ioi (0 : ℝ), Fr t = log ((n : ℝ) + 1) := by
      have hc : Continuous fun x : ℝ ↦ exp (-x) := by fun_prop
      have hL : Tendsto (fun x : ℝ ↦ exp (-x)) (𝓝[>] 0) (𝓝 1) := by
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      have := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ exp (-x)) (a := 1)
        (b := ((n + 1 : ℕ) : ℝ)) (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
        one_pos (by positivity) hL tendsto_exp_neg_atTop_nhds_zero hFrint
      simpa [Fr] using this
    have hsumval : ∫ t in Ioi (0 : ℝ), ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)) =
        harmonic n := by
      rw [integral_finsetSum _ hsumint, harmonic, Rat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_exp_neg_natCast_mul (i + 1) i.succ_pos]
      push_cast
      ring
    have hI : I = ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ gaussDigammaKernel_eq n ht
    have e1 : ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) =
        (∫ t in Ioi (0 : ℝ), (Fr t -
          (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))))) + R n :=
      integral_add (hFrint.sub hsumint') (hRint n)
    have e2 : ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)))) =
        (∫ t in Ioi (0 : ℝ), Fr t) -
          ∫ t in Ioi (0 : ℝ), ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)) :=
      integral_sub hFrint hsumint'
    rw [hI, e1, e2, hFrval, hsumval]
    ring
  -- Let `n → ∞`.
  have hR0 : Tendsto R atTop (𝓝 0) :=
    squeeze_zero_norm hRle tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ ↦ -(harmonic n - log ((n : ℝ) + 1)) + R n) atTop
      (𝓝 (-eulerMascheroniConstant + 0)) :=
    tendsto_harmonic_sub_log_add_one.neg.add hR0
  rw [add_zero] at hlim
  refine tendsto_nhds_unique ?_ hlim
  simp_rw [← hexp]
  exact tendsto_const_nhds

end GaussDigamma

/-- Paper: Proposition B.4.2.1, p. 616. At unit scale and unit gamma
arguments the integrable kernel for the constant test gives twice the digamma value at one.
Deviation: This is a sanity check for the corrected kernel. -/
theorem heckeArchimedeanDigammaKernel_one :
    let K := heckeArchimedeanDigammaKernel 1 1 1 (fun _ ↦ 1)
    IntegrableOn K (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), K t) = -2 * (Real.eulerMascheroniConstant : ℂ) := by
  intro K
  have hK : K = fun t ↦ ((2 * gaussDigammaKernel t : ℝ) : ℂ) := by
    funext t
    simp only [K, heckeArchimedeanDigammaKernel, gaussDigammaKernel]
    push_cast
    simp only [neg_mul, one_mul]
    ring
  rw [hK]
  simp only []
  refine ⟨(integrableOn_gaussDigammaKernel.const_mul 2).ofReal, ?_⟩
  rw [integral_complex_ofReal, integral_const_mul, integral_gaussDigammaKernel]
  push_cast
  ring

local notation "circleToComplex" =>
  (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

local notation "localChart(" w ", " χ ")" =>
  quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ (InfinitePlace.mult w) :
      (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w) (ContinuousMonoidHom.comp circleToComplex χ)

/-- Paper: Proposition B.4.2.1, p. 616. The two real local contour terms equal
the integral of the digamma kernel and the real gamma prefactor contribution.
Deviation: The integral converges at both endpoints and includes sign parity. -/
theorem realHeckeArchimedean_mellinLogDeriv (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (a : ℝ) (_ha : 1 < a) :
    let p := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    let K := heckeArchimedeanDigammaKernel (1 / 2)
      ((p.1 + p.2.val) / 2) ((1 - p.1 + p.2.val) / 2) f
    let H := fun s ↦ logMellin f s * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ)) s +
      logMellin f (1 - s) * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)) s
    Complex.VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      verticalLineIntegral H a / twoPiI =
        (∫ t in Ioi (0 : ℝ), K t) - (Real.log Real.pi : ℂ) * f 0 := by sorry

/-- Paper: Proposition B.4.2.1, p. 616. The two complex local contour terms
equal the digamma integral and the complex gamma prefactor contribution.
Deviation: The integral converges at both endpoints and includes absolute angular weight. -/
theorem complexHeckeArchimedean_mellinLogDeriv (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (a : ℝ) (_ha : 1 < a) :
    let p := (complexLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    let K := heckeArchimedeanDigammaKernel 1
      (p.1 + (p.2.natAbs : ℂ) / 2) (1 - p.1 + (p.2.natAbs : ℂ) / 2) f
    let H := fun s ↦ logMellin f s * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ)) s +
      logMellin f (1 - s) * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)) s
    Complex.VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      verticalLineIntegral H a / twoPiI =
        (∫ t in Ioi (0 : ℝ), K t) - 2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by sorry

-- TODO(paper-gap): (B.4.2.10) needs dt/(2π). With upward ds/(2πi),
-- (B.4.2.11) gives +log(q) χ̄(π)^m q^(-m) φ(q^(-m)).
-- Theorem B.4.2.2 also subtracts two pole terms for every χ and uses the
-- divergent archimedean integral from (B.4.2.15).

local notation "primeTerm(" χ ", " f ")" =>
  (fun j : Primes(F) × ℕ ↦
    if χ₀(χ).IsUnramifiedAt j.1 then
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      (Real.log q(j.1) * Real.exp (-x / 2) : ℝ) *
        ((χ₀(χ).localValue j.1) ^ (j.2 + 1) * f x +
          (χ₀(χ⁻¹).localValue j.1) ^ (j.2 + 1) * f (-x))
    else (0 : ℂ))

/-- Paper: Theorem B.4.2.2, p. 616. The centered prime-power contributions
are absolutely summable over the finite places and positive exponents.
Deviation: Ramified Euler factors contribute zero. -/
theorem summable_heckeExplicitPrimeTerms (χ : U[F]) (f : 𝓢(ℝ, ℂ))
    (_hf : ExponentialDecay f) :
    Summable (fun j ↦ ‖primeTerm(χ, f) j‖) := by
  obtain ⟨g, hg⟩ := exponentialDecay_weighted_schwartz f _hf 3
  obtain ⟨h, hh⟩ := exponentialDecay_weighted_schwartz f _hf (-3)
  let C := SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ 0 0 h
  have hdecay (x : ℝ) : ‖f x‖ + ‖f (-x)‖ ≤ C * Real.exp (-(3 * x)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), add_mul]
    have hg' := g.norm_le_seminorm ℂ x
    have hh' := h.norm_le_seminorm ℂ (-x)
    rw [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hg'
    simp only [hh, neg_mul_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)] at hh'
    simpa only [mul_comm] using add_le_add hg' hh'
  -- Index the majorant by the corresponding prime-power ideals.
  let I (j : Primes(F) × ℕ) := j.1.asIdeal ^ (j.2 + 1)
  have hI : Injective I := by
    rintro ⟨v, n⟩ ⟨w, k⟩ he
    change v.asIdeal ^ (n + 1) = w.asIdeal ^ (k + 1) at he
    have hd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow
      (he ▸ dvd_pow_self _ (Nat.succ_ne_zero n))
    have hvw : v = w := HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hd)).symm
    subst w
    have hN := congrArg (Ideal.absNorm : Ideal (𝓞 F) → ℕ) he
    simp only [map_pow] at hN
    have hn := Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) hN
    exact Prod.ext rfl (Nat.succ.inj hn)
  have hsum := (summable_absNorm_rpow F (r := 2) (by norm_num)).comp_injective hI
  refine (hsum.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
  rintro ⟨v, k⟩
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlog := (Real.log_pos hq).le
  let x := ((k + 1 : ℕ) : ℝ) * Real.log q(v)
  have hx : Real.log q(v) ≤ x := by
    dsimp [x]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hlog]
  have hfactor : Real.log q(v) * Real.exp (-x / 2) ≤ Real.exp x :=
    (mul_le_of_le_one_right hlog (Real.exp_le_one_iff.mpr (by linarith))).trans
      (hx.trans (by linarith [Real.add_one_le_exp x]))
  change ‖(if _ then _ else (0 : ℂ))‖ ≤ C * ((I (v, k)).absNorm : ℝ) ^ (-(2 : ℝ))
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hlog (Real.exp_nonneg _))]
    calc
      _ ≤ (Real.log q(v) * Real.exp (-x / 2)) * (‖f x‖ + ‖f (-x)‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog (Real.exp_nonneg _))
        simpa only [norm_mul, norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul]
          using norm_add_le ((χ₀(χ).localValue v) ^ (k + 1) * f x)
            ((χ₀(χ⁻¹).localValue v) ^ (k + 1) * f (-x))
      _ ≤ Real.exp x * (C * Real.exp (-(3 * x))) :=
        mul_le_mul hfactor (hdecay x) (by positivity) (Real.exp_nonneg _)
      _ = C * Real.exp (x + -(3 * x)) := by rw [Real.exp_add]; ring
      _ = _ := by
        change _ = C * (((v.asIdeal ^ (k + 1)).absNorm : ℕ) : ℝ) ^ (-(2 : ℝ))
        rw [map_pow, Nat.cast_pow, Real.rpow_def_of_pos (pow_pos (zero_lt_one.trans hq) _),
          Real.log_pow]
        dsimp [x]
        ring_nf
  · rw [norm_zero]
    exact mul_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Paper: Theorem B.4.2.2, p. 616. The centered divisor sum equals the
discriminant–conductor term, minus the prime-power series, plus the gamma terms.
Deviation: Signed meromorphic orders count zeros and the actual poles of the
norm twist. The archimedean terms use the convergent digamma kernel with the
local sign parity or angular weight from §3.2. -/
theorem hasSum_heckeExplicitFormula (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f (ρ - 1 / 2))
      ((heckeLogDiscriminantConductor χ : ℂ) * f 0 - (∑' j, primeTerm(χ, f) j) +
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0) := by sorry

end MellinExplicitFormula

local notation "𝒮ₐ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "𝒟(" G ")" => BruhatCompactSupport G
local notation "addTest(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure F v
local notation "ν∞(" w ")" => infiniteLocalAdditiveTamagawaMeasure F w
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter F v
local notation "ψ∞(" w ")" => (fun x ↦ adeleStandardCharacter F
  (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "V𝔭(" v ")" => ((μ𝔭(v) (O(v)).units).toReal)
local notation "finiteWeilScale(" v ")" => ((Real.log q(v) / V𝔭(v) : ℝ) : ℂ)

-- Use the local-field topology and Borel measures of Appendix A.
local instance instFiniteCompletionUnitsLocallyCompactSec4b (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F)ˣ :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance

local instance instFiniteCompletionMeasurableSec4b (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance instFiniteCompletionUnitsMeasurableSec4b (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance instInfiniteCompletionMeasurableSec4b (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _
local instance instIdeleClassT2Sec4b : T2Space C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSec4b : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassMeasurableSec4b : MeasurableSpace C[F] := borel _
local instance instNormOneIdeleClassMeasurableSec4b :
    MeasurableSpace (MonoidHom.ker (ideleClassNorm F)) := borel _

local notation "J𝔭(" v ")" =>
  (fun y : HeightOneSpectrum.adicCompletion F v ↦ (Real.log ‖y‖ / Real.log q(v) : ℝ))
local notation "J∞(" w ")" =>
  (fun y : InfinitePlace.Completion w ↦ Real.log (‖y‖ ^ InfinitePlace.mult w))
local notation "logFourierIntegrand(" ν ", " ψ ", " J ", " f ")" =>
  (fun y ↦ ((J y : ℝ) : ℂ) * tamagawaFourier ν ψ f y)

section LocalFourier

/-- Paper: Proposition B.4.3.1(1), p. 617. Dilation of the additive test
changes the Fourier transform of the normalized logarithm by a multiple of evaluation at zero. -/
theorem finiteLogFourier_dilate (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ) :
    let K : (v.adicCompletion F → ℂ) → v.adicCompletion F → ℂ :=
      fun g ↦ logFourierIntegrand(ν𝔭(v), ψ𝔭(v), J𝔭(v), g)
    Integrable (K (addTest(f) ∘ (fun x ↦ a.inv * x))) ν𝔭(v) ∧
      Integrable (K addTest(f)) ν𝔭(v) ∧
      (∫ y, K (addTest(f) ∘ (fun x ↦ a.inv * x)) y ∂ν𝔭(v)) =
        (∫ y, K addTest(f) y ∂ν𝔭(v)) -
          (Real.log ‖a.val‖ / Real.log q(v) : ℝ) * addTest(f) 0 := by sorry

/-- Paper: Proposition B.4.3.1(2), p. 617. On additive tests vanishing at
zero, the Fourier transform is minus multiplicative Haar measure divided by
the mass of the integer units. -/
theorem finiteLogFourier_eq_neg_haar (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (_hf : addTest(f) 0 = 0) :
    let K : v.adicCompletion F → ℂ := logFourierIntegrand(ν𝔭(v), ψ𝔭(v), J𝔭(v), addTest(f))
    Integrable K ν𝔭(v) ∧ Integrable (fun u : (v.adicCompletion F)ˣ ↦ addTest(f) u.val) μ𝔭(v) ∧
      (∫ y, K y ∂ν𝔭(v)) =
        -(∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v)) / (V𝔭(v) : ℂ) := by sorry

-- TODO(paper-gap): Jᵥ is unbounded near zero and is not an additive
-- Schwartz–Bruhat test. The normalization at one is on its punctured-field representative.

/-- Paper: Proposition B.4.3.1, p. 618. The restriction away from zero of the
Fourier transform determines the normalized logarithm among continuous representatives off zero.
Deviation: The representative acts by integration on Fourier-transformed tests. -/
theorem finiteLogFourier_unique (v : Primes(F)) (J : v.adicCompletion F → ℂ)
    (_hcont : ContinuousOn J ({0}ᶜ)) (_hOne : J 1 = 0)
    (_hInt : ∀ f : 𝒮ₐ(v.adicCompletion F),
      Integrable (fun y ↦ J y * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v))
    (_hAway : ∀ f : 𝒮ₐ(v.adicCompletion F), addTest(f) 0 = 0 →
      (∫ y, J y * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) =
        -(∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v)) / (V𝔭(v) : ℂ)) :
    ∀ x ≠ 0, J x = (J𝔭(v) x : ℝ) := by sorry

-- TODO(paper-gap): (B.4.3.13)–(B.4.3.14) multiply the Fourier distributions by
-- the local norm-one volumes 2 and 2π. Dilation gives the wrong delta term
-- with those factors (already visible on the real self-dual Gaussian).

local notation "eulerLogConstant" => (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)

/-- Paper: Proposition B.4.3.2(1), p. 619. The real Fourier pairing equals
minus half the finite part and minus the logarithmic constant times evaluation at zero.
Deviation: Divides the printed distribution by two. -/
theorem realLogFourier_finitePart (w : InfinitePlace F) (_hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) :
    let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
    Integrable K ν∞(w) ∧
      (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ addTest(f) x / ((‖x‖ : ℝ) : ℂ))
        {x : w.Completion | ε ≤ ‖x‖} ν∞(w)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖},
        addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w)) + 2 * addTest(f) 0 * (Real.log ε : ℂ))
        (𝓝[>] 0) (𝓝 (-2 * ((∫ y, K y ∂ν∞(w)) + (eulerLogConstant : ℂ) * addTest(f) 0))) :=
  by sorry

/-- Paper: Proposition B.4.3.2(2), p. 619. The complex Fourier pairing
equals minus the finite part divided by 2π, with the squared module in the cutoff.
Deviation: Divides the printed distribution by 2π. -/
theorem complexLogFourier_finitePart (w : InfinitePlace F) (_hw : w.IsComplex)
    (f : 𝒮ₐ(w.Completion)) :
    let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
    Integrable K ν∞(w) ∧
      (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ))
        {x : w.Completion | ε ≤ ‖x‖ ^ 2} ν∞(w)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
        addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂ν∞(w)) +
        (2 * Real.pi : ℝ) * addTest(f) 0 * (Real.log ε : ℂ))
        (𝓝[>] 0) (𝓝 (-(2 * Real.pi : ℝ) *
          ((∫ y, K y ∂ν∞(w)) + (2 * eulerLogConstant : ℝ) * addTest(f) 0))) := by sorry

end LocalFourier

section PrincipalValues

local notation "scaledMeasure(" v ", " a ")" =>
  (ENNReal.ofReal (Real.sqrt ‖(a : (HeightOneSpectrum.adicCompletion F v)ˣ).val‖) • ν𝔭(v))
local notation "scaledChar(" v ", " a ")" => (fun x ↦ ψ𝔭(v) (Units.val a * x))
local notation "zeroExtend(" f ")" => (Function.extend Units.val (f : _ → ℂ) (fun _ ↦ 0))
local notation "weightedTranslate(" abs ", " f ")" =>
  (fun x ↦ zeroExtend(f) (1 + x) / (Real.sqrt (abs (1 + x)) : ℂ))

/-- Paper: Definition B.4.4.1(1), p. 619. The scaled finite Fourier
pairing defines a continuous linear functional on additive tests.
Deviation: The additive character is allowed to be any translate of the standard character
by a nonzero field multiplier, with the corresponding self-dual measure. -/
theorem exists_finiteConnesPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    ∃ T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)),
      ∀ f : 𝒮ₐ(v.adicCompletion F),
        let ν := scaledMeasure(v, a)
        let K : v.adicCompletion F → ℂ := logFourierIntegrand(ν, scaledChar(v, a), J𝔭(v), addTest(f))
        Integrable K ν ∧ T f = -(V𝔭(v) : ℂ) * ∫ y, K y ∂ν := by sorry

/-- Paper: Definition B.4.4.1(1), p. 619. Connes's finite additive
principal value pairs the Fourier-transformed test with the normalized logarithm.
Deviation: The nonzero multiplier specifies the character as in (B.4.4.12). -/
def finiteConnesPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    StrongDual ℂ (𝒮ₐ(v.adicCompletion F)) := (exists_finiteConnesPrincipalValue v a).choose

/-- Paper: Definition B.4.4.1(1), p. 619. Outside the singularity, the finite
additive principal value for the standard character is ordinary multiplicative integration. -/
theorem finiteConnesPrincipalValue_one_of_apply_zero (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) (_hf : addTest(f) 0 = 0) :
    finiteConnesPrincipalValue v 1 f =
      ∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v) := by
  have hT := ((exists_finiteConnesPrincipalValue v 1).choose_spec f).2
  have hK := (finiteLogFourier_eq_neg_haar v f _hf).2.2
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  change finiteConnesPrincipalValue v 1 f = _ at hT
  simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    one_mul] at hT
  rw [hT, hK, mul_div, neg_mul_neg]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hV)

/-- Paper: Definition B.4.4.1(1), p. 619. The archimedean Fourier pairing
defines a continuous linear functional on additive tests. -/
theorem exists_infiniteConnesPrincipalValue (w : InfinitePlace F) :
    ∃ T : StrongDual ℂ (𝒮ₐ(w.Completion)), ∀ f : 𝒮ₐ(w.Completion),
      let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
      Integrable K ν∞(w) ∧ T f = -(∫ y, K y ∂ν∞(w)) := by sorry

/-- Paper: Definition B.4.4.1(1), p. 619. Connes's archimedean additive
principal value is minus the Fourier transform of the logarithm distribution. -/
def infiniteConnesPrincipalValue (w : InfinitePlace F) :
    StrongDual ℂ (𝒮ₐ(w.Completion)) := (exists_infiniteConnesPrincipalValue w).choose

/-- Paper: Definition B.4.4.1(1), p. 619. On real tests vanishing at
zero, the additive principal value is integration against half of the weighted additive measure.
Deviation: The factor one half is the real case of the correction to Proposition B.4.3.2. -/
theorem realConnesPrincipalValue_of_apply_zero (w : InfinitePlace F) (_hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) (_hf : addTest(f) 0 = 0) :
    infiniteConnesPrincipalValue w f =
      (1 / 2 : ℂ) * ∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) := by
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec f).2
  change infiniteConnesPrincipalValue w f = _ at hT
  have hL := (realLogFourier_finitePart w _hw f).2.2
  simp only [_hf, mul_zero, zero_mul, add_zero] at hL
  let : BorelSpace w.Completion := ⟨rfl⟩
  -- Real coordinates turn the test into a classical Schwartz function vanishing at zero.
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { toMulEquiv := (InfinitePlace.Completion.ringEquivRealOfIsReal _hw).toAddEquiv.toMultiplicative
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have hc := schwartzBruhat_realCoordinate_equiv c
  have hE := hc.choose_spec
  let s := hc.choose.symm f
  have hs (t : ℝ) : s t = addTest(f) (e.symm t) := by
    have := hE s (Multiplicative.ofAdd (e.symm t))
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    refine Eq.trans ?_ this.symm
    exact congrArg s (e.apply_symm_apply t).symm
  have h0 : e.symm 0 = 0 := map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal _hw).symm
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ := by
    rw [← dist_zero_right, ← dist_zero_right t, ← e.symm.dist_eq t 0, h0]
  have hs0 : s 0 = 0 := by rw [hs, h0]; exact _hf
  -- The weighted test is integrable on the real line: Lipschitz near zero, decaying at infinity.
  let C := SchwartzMap.seminorm ℝ 0 1 s
  have hlip (t : ℝ) : ‖s t‖ ≤ C * ‖t‖ := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := s) (s := univ) (C := C)
      (fun x _ ↦ s.differentiableAt) (fun x _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ t)
    · simpa [hs0] using this
    · rw [← norm_iteratedFDeriv_one]
      exact s.norm_iteratedFDeriv_le_seminorm ℝ 1 x
  have hR : Integrable (fun t : ℝ ↦ s t / ((‖t‖ : ℝ) : ℂ)) := by
    refine Integrable.mono' (g := fun t ↦ (Icc (-1 : ℝ) 1).indicator (fun _ ↦ C) t + ‖s t‖)
      ((continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).add
        s.integrable.norm)
      (s.continuous.measurable.div
        (Complex.measurable_ofReal.comp measurable_norm)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [norm_div, Complex.norm_real, norm_norm]
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem ht]
      rcases eq_or_ne t 0 with rfl | ht0
      · simp [hs0, C]
      · have : ‖s t‖ / ‖t‖ ≤ C := (div_le_iff₀ (norm_pos_iff.mpr ht0)).mpr (hlip t)
        linarith [norm_nonneg (s t)]
    · rw [indicator_of_notMem ht, zero_add]
      have h1 : 1 ≤ ‖t‖ := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rw [Real.norm_eq_abs]
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact div_le_self (norm_nonneg _) h1
  have hG : Integrable (fun x : w.Completion ↦ addTest(f) x / ((‖x‖ : ℝ) : ℂ)) ν∞(w) := by
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left _hw]
    let m := e.symm.toHomeomorph.toMeasurableEquiv
    rw [show ((InfinitePlace.Completion.ringEquivRealOfIsReal _hw).symm : ℝ → w.Completion) = m
      from rfl, integrable_map_equiv]
    refine hR.congr (Eventually.of_forall fun t ↦ ?_)
    change s t / ((‖t‖ : ℝ) : ℂ) = addTest(f) (e.symm t) / ((‖e.symm t‖ : ℝ) : ℂ)
    rw [hs, hnorm]
  -- Dominated convergence removes the cutoff.
  have hmeas (ε : ℝ) : MeasurableSet {x : w.Completion | ε ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in {x : w.Completion | ε ≤ ‖x‖},
      addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w)) (𝓝[>] 0)
      (𝓝 (∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w))) := by
    simp_rw [← integral_indicator (hmeas _)]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖addTest(f) x / ((‖x‖ : ℝ) : ℂ)‖)
      (Eventually.of_forall fun ε ↦ hG.aestronglyMeasurable.indicator (hmeas ε))
      (Eventually.of_forall fun ε ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)
      hG.norm (Eventually.of_forall fun x ↦ ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Set.indicator_apply]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (norm_pos_iff.mpr hx))] with ε hε
      rw [indicator_of_mem (show ε ≤ ‖x‖ from hε.le)]
  rw [hT, tendsto_nhds_unique hlim hL]
  ring

/-- Paper: Definition B.4.4.1(2), p. 620. Translation of the zero-extended
test after inverse square-root weighting gives a continuous linear map to additive tests. -/
theorem exists_finiteWeilTestMap (v : Primes(F)) :
    ∃ A : 𝒟((v.adicCompletion F)ˣ) →L[ℂ] 𝒮ₐ(v.adicCompletion F),
      ∀ (f : 𝒟((v.adicCompletion F)ˣ)) (x : v.adicCompletion F),
        addTest(A f) x = weightedTranslate(norm, f.val) x := by sorry

/-- Paper: Definition B.4.4.1(2), p. 620. The weighted translate of a
multiplicative test at an infinite place is an additive test, continuously in the original test. -/
theorem exists_infiniteWeilTestMap (w : InfinitePlace F) :
    ∃ A : 𝒟(w.Completionˣ) →L[ℂ] 𝒮ₐ(w.Completion),
      ∀ (f : 𝒟(w.Completionˣ)) (x : w.Completion),
        addTest(A f) x = weightedTranslate((fun y : w.Completion ↦ ‖y‖ ^ w.mult), f.val) x :=
  by sorry

/-- Paper: Definition B.4.4.1(2), p. 620. The finite multiplicative
principal value applies Connes's functional to the weighted translated test.
Deviation: The multiplier parametrizes the additive character used by Lemma B.4.4.4. -/
def finiteConnesWeilPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    StrongDual ℂ (𝒟((v.adicCompletion F)ˣ)) :=
  (finiteConnesPrincipalValue v a).comp (exists_finiteWeilTestMap v).choose

/-- Paper: Definition B.4.4.1(2), p. 620. The infinite multiplicative
principal value applies Connes's functional to the weighted translated test. -/
def infiniteConnesWeilPrincipalValue (w : InfinitePlace F) :
    StrongDual ℂ (𝒟(w.Completionˣ)) :=
  (infiniteConnesPrincipalValue w).comp (exists_infiniteWeilTestMap w).choose

/-- Paper: Definition B.4.4.1(2), p. 620. At a real place a test vanishing
at one has its principal value given by the canonical ordinary integral. -/
theorem realConnesWeilPrincipalValue_of_apply_one_zero (w : InfinitePlace F)
    (_hw : w.IsReal) (f : 𝒟(w.Completionˣ)) (_hf : f.val 1 = 0) :
    let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
    (infiniteConnesWeilPrincipalValue w) f =
      (1 / 2 : ℂ) * ∫ u : w.Completionˣ,
        f.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ := by
  intro μ
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let r := InfinitePlace.Completion.ringEquivRealOfIsReal _hw
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hA := (exists_infiniteWeilTestMap w).choose_spec f
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, _hw]
  let Fz : w.Completion → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hFu (u : w.Completionˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have hFz (y : w.Completion) (hy : y ∉ range (Units.val : w.Completionˣ → w.Completion)) :
      Fz y = 0 := by
    simp only [Fz, Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hy ⟨u, hu⟩)]
  have h0 : addTest((exists_infiniteWeilTestMap w).choose f) 0 = 0 := by
    rw [hA]
    change Fz (1 + 0) / _ = 0
    rw [add_zero, ← Units.val_one, hFu, _hf, zero_div]
  change infiniteConnesPrincipalValue w ((exists_infiniteWeilTestMap w).choose f) = _
  rw [realConnesPrincipalValue_of_apply_zero w _hw _ h0]
  congr 1
  let G : w.Completion → ℂ := fun y ↦ Fz y / (Real.sqrt ‖y‖ : ℂ) / ((‖y - 1‖ : ℝ) : ℂ)
  -- Translation invariance moves the singularity from zero to one.
  have htr : ∫ x, addTest((exists_infiniteWeilTestMap w).choose f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) =
      ∫ y, G y ∂ν∞(w) := by
    have hG : (fun x ↦ addTest((exists_infiniteWeilTestMap w).choose f) x / ((‖x‖ : ℝ) : ℂ)) =
        fun x ↦ G (1 + x) := by
      funext x
      rw [hA]
      change Fz (1 + x) / ((Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ)) / _ =
        Fz (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ) / ((‖1 + x - 1‖ : ℝ) : ℂ)
      rw [hmult, pow_one, add_sub_cancel_left]
    rw [hG, infiniteLocalAdditiveTamagawaMeasure, dite_eq_left _hw]
    let m := e.symm.toHomeomorph.toMeasurableEquiv
    rw [show (r.symm : ℝ → w.Completion) = m from rfl, integral_map_equiv, integral_map_equiv]
    have hm (t : ℝ) : 1 + m t = m (1 + t) := by
      change 1 + r.symm t = r.symm (1 + t)
      rw [map_add, map_one]
    simp_rw [hm]
    exact integral_add_left_eq_self (fun t ↦ G (m t)) 1
  rw [htr]
  -- The multiplicative measure is the additive one with density `1 / ‖y‖` on units.
  let d : w.Completion → ENNReal := fun x ↦ (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  simp only [← hFu]
  change _ = ∫ u, _ ∂(ν∞(w).withDensity d).comap Units.val
  rw [← hval.integral_map (g := fun y ↦ Fz y * (Real.sqrt ‖y‖ : ℂ) / ((‖1 - y‖ : ℝ) : ℂ)),
    hval.map_comap, setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _
      hval.measurableSet_range,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
      (fun y hy ↦ by simp only [G, hFz y hy, zero_div])]
  · refine setIntegral_congr_fun hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr (hu ▸ u.ne_zero)
    simp only [G, d, hmult, pow_one]
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm, Complex.real_smul, norm_sub_rev]
    have hs : (Real.sqrt ‖y‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
    have hsq : (‖y‖ : ℂ) = (Real.sqrt ‖y‖ : ℂ) * (Real.sqrt ‖y‖ : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt hn.le).symm
    push_cast
    rw [hsq]
    field_simp
  · refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp only [d, hmult, pow_one]
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])

local notation "finiteWeilIntegrand(" v ", " f ")" =>
  (fun u : (HeightOneSpectrum.adicCompletion F v)ˣ ↦
    f u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ))

/-- Paper: Remark B.4.4.2, p. 620. For the finite local norm the canonical
multiplicative Haar measure gives an integer-unit shell mass equal to the log prime norm. -/
theorem finiteCanonicalHaar_eq_smul_tamagawa (v : Primes(F)) :
    letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    letI : SecondCountableTopology (v.adicCompletion F)ˣ :=
      (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).secondCountableTopology
    letI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
    let m : (v.adicCompletion F)ˣ →ₜ* ℝ≥0ˣ :=
      ⟨Units.map nnNormHom.toMonoidHom, continuous_finiteLocalModule v⟩
    ∃ hm : IsModulation m, canonicalModulatedHaar m hm =
      ENNReal.ofReal (Real.log q(v) / V𝔭(v)) • μ𝔭(v) := by
  classical
  intro m
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let : BorelSpace Kˣ := ⟨rfl⟩
  let q : ℝ≥0ˣ := Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (by exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne')
  have hq : 1 < (q.val : ℝ) := by
    change 1 < (v.asIdeal.absNorm : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  have hgen : m p⁻¹ = q := by
    apply Units.ext
    apply NNReal.eq
    change ‖(p⁻¹).val‖ = q(v)
    rw [Units.val_inv_eq_inv_val, norm_inv, hp, inv_inv]
  have hm : IsModulation m := by
    constructor
    · change IsProperMap (Units.map nnNormHom.toMonoidHom : Kˣ →* ℝ≥0ˣ)
      have h := isProperMap_units_nnNorm_pow (K := K) 1 one_ne_zero
      simpa only [MonoidHom.pow_apply, pow_one] using h
    · refine ⟨p⁻¹, fun he ↦ hq.ne' ?_⟩
      exact congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (hgen.symm.trans he)
  -- The inverse uniformizer generates the range of the normalized absolute value.
  have hrange : m.toMonoidHom.range = Subgroup.zpowers q := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨WithZero.log (Valued.v u.val), ?_⟩
      apply Units.ext
      apply NNReal.eq
      change (((q ^ _).val : ℝ≥0) : ℝ) = ‖u.val‖
      rw [Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, FinitePlace.norm_def,
        WithZeroMulInt.toNNReal_neg_apply _ (Valued.v.ne_zero_iff.mpr u.ne_zero)]
      simp [q]
    · exact Subgroup.zpowers_le.mpr ⟨p⁻¹, hgen⟩
  have hker : (m.toMonoidHom.ker : Set Kˣ) = (O(v)).units := by
    ext u
    change m u = 1 ↔ u ∈ (O(v)).units
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      ← Valued.toNormedField.norm_eq_one_iff, ← Units.val_inj, ← NNReal.coe_inj]
    rfl
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  refine ⟨hm, (existsUnique_canonicalModulatedHaar m hm).unique
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists) ?_⟩
  have hqval : (q.val : ℝ) = q(v) := by simp [q]
  simpa only [hker, hqval] using haar_logGrowth_of_cyclic_range m hm hq hrange μ𝔭(v)

/-- Paper: Remark B.4.4.2, p. 620. For the infinite local module, dividing
Tamagawa measure by two at a real place or by two pi at a complex place gives canonical Haar measure. -/
theorem infiniteCanonicalHaar_eq_smul_tamagawa (w : InfinitePlace F) :
    letI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    letI : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    letI : BorelSpace w.Completion := ⟨rfl⟩
    letI : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let m : w.Completionˣ →ₜ* ℝ≥0ˣ :=
      ⟨(Units.map nnNormHom.toMonoidHom) ^ w.mult, continuous_infiniteLocalModule w⟩
    ∃ hm : IsModulation m, canonicalModulatedHaar m hm =
      ENNReal.ofReal ((if w.IsReal then 2 else 2 * Real.pi)⁻¹) •
        infiniteLocalMultiplicativeTamagawaMeasure F w := by sorry

/-- Paper: Lemma B.4.4.3, p. 620. If the locally constant test vanishes
at one, the finite principal value is the ordinary integrable local term. -/
theorem finiteConnesWeilPrincipalValue_of_apply_one_zero (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) (_hf : f.val 1 = 0) :
    Integrable (finiteWeilIntegrand(v, f.val)) μ𝔭(v) ∧
      finiteConnesWeilPrincipalValue v 1 f =
        ∫ u, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v) := by sorry

-- TODO(paper-gap): Equation (B.4.4.6) gives the wrong sign and scale for
-- the restriction of T, and Fourier transformation requires an additive test space.

/-- Paper: Lemma B.4.4.3, pp. 620–621. The translated Fourier
distribution is normalized on the Fourier transform of the integer-unit indicator.
It evaluates the finite multiplicative principal value on inverse square-root weighted tests.
Deviation: The distribution is on the full additive test space. Its restriction away
from one is minus the specified density divided by the mass of the integer units.
The evaluation identity extends to all multiplicative tests by the weighted translation. -/
theorem existsUnique_finiteWeilFourierDistribution (v : Primes(F)) :
    let normalized := fun T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)) ↦
      (∀ f : 𝒮ₐ(v.adicCompletion F), addTest(f) 1 = 0 →
        T f = -((q(v) / (q(v) - 1) / V𝔭(v) : ℝ) : ℂ) *
          ∫ x, addTest(f) x / ((‖1 - x‖ : ℝ) : ℂ) ∂ν𝔭(v)) ∧
      (∃ g : 𝒮ₐ(v.adicCompletion F),
        addTest(g) = tamagawaFourier ν𝔭(v) ψ𝔭(v)
          (indicator {x : v.adicCompletion F | ‖x‖ = 1} (fun _ ↦ 1)) ∧ T g = 0)
    ∃ T, normalized T ∧ (∀ S, normalized S → S = T) ∧
      (∀ f : 𝒟((v.adicCompletion F)ˣ), ∃ g : 𝒮ₐ(v.adicCompletion F),
        (∀ x, addTest(g) x = zeroExtend(f.val) x / (Real.sqrt ‖x‖ : ℂ)) ∧
        finiteConnesWeilPrincipalValue v 1 f = -(V𝔭(v) : ℂ) * T g) := by sorry

/-- Paper: Lemma B.4.4.4(1), p. 622. Changing the finite additive
character by a multiplier adds a multiple of evaluation at zero to Connes's principal value. -/
theorem finiteConnesPrincipalValue_changeCharacter (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    finiteConnesPrincipalValue v a f = finiteConnesPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * addTest(f) 0 := by sorry

/-- Paper: Lemma B.4.4.4(2), p. 622. The same change of character
adds a multiple of evaluation at one to the multiplicative principal value. -/
theorem finiteConnesWeilPrincipalValue_changeCharacter (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒟((v.adicCompletion F)ˣ)) :
    finiteConnesWeilPrincipalValue v a f = finiteConnesWeilPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * f.val 1 := by
  let A := (exists_finiteWeilTestMap v).choose
  have hunit := Units.val_injective.extend_apply f.val (fun _ ↦ 0)
    (1 : (v.adicCompletion F)ˣ)
  have hzero : addTest(A f) 0 = f.val 1 := by
    have h := (exists_finiteWeilTestMap v).choose_spec f 0
    simp only [add_zero, norm_one, Real.sqrt_one, Complex.ofReal_one, div_one] at h
    exact h.trans hunit
  exact (finiteConnesPrincipalValue_changeCharacter v a (A f)).trans
    (congrArg (fun z : ℂ ↦ finiteConnesWeilPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * z) hzero)

-- TODO(paper-gap): In the proof on p. 623 (footnote 24), the annihilator of
-- the maximal ideal is the inverse maximal ideal times the inverse different.
-- The second indicator in the printed display uses the different itself.

local notation "differentExp(" v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))


/-- Paper: Lemma B.4.4.5, p. 622. The rescaled finite principal value is
the unit-subtracted finite part with the different correction. -/
theorem finiteConnesWeilPrincipalValue_eq_finitePart (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) :
    let units : Set (v.adicCompletion F)ˣ := (O(v)).units
    let outside := finiteWeilIntegrand(v, f.val)
    let inside := finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1))
    IntegrableOn outside unitsᶜ μ𝔭(v) ∧ IntegrableOn inside units μ𝔭(v) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        finiteWeilScale(v) * ((∫ u in unitsᶜ, outside u ∂μ𝔭(v)) +
          (∫ u in units, inside u ∂μ𝔭(v))) -
        ((differentExp(v) : ℝ) * Real.log q(v) : ℝ) * f.val 1 :=
  by sorry

/-- Evaluating the finite part on a compact open subgroup indicator gives the correction term. -/
private theorem finiteConnesWeilPrincipalValue_integerUnits_test
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G))
    (μ : Measure G) (num den : G → ℂ) (eval : 𝒟(G) → ℂ) (scale correction : ℂ)
    (heval : ∀ f : 𝒟(G), eval f =
      scale * ((∫ u in (U : Set G)ᶜ, f.val u * num u / den u ∂μ) +
        (∫ u in (U : Set G), (f.val u - f.val 1) * num u / den u ∂μ)) -
      correction * f.val 1) :
    ∃ f : 𝒟(G), f.val = (U : Set G).indicator (fun _ ↦ 1) ∧ eval f = -correction := by
  classical
  let g : G → ℂ := (U : Set G).indicator (fun _ ↦ 1)
  let : CompactSpace (lcaAnnihilator U) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U hU)
  have hClosed : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have hSmooth : IsBruhatSmooth g := by
    intro p
    refine ⟨U, ⟨hClosed, isOpen_lcaAnnihilator U hUc, isCompactlyGeneratedGroup_of_compact⟩,
      ?_, ?_⟩
    · intro h x
      have hmem : h.val * x ∈ (U : Set G) ↔ x ∈ (U : Set G) := by
        refine ⟨fun hx ↦ ?_, U.mul_mem h.property⟩
        change x ∈ U
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem h.property) hx
      simp only [g, indicator_apply, hmem]
    · intro a ha
      let f₀ : a.quotient → ℂ := ({1} : Set a.quotient).indicator (fun _ ↦ 1)
      refine ⟨f₀, fun x ↦ ?_, ?_⟩
      · simp only [f₀, g, indicator_apply, mem_singleton_iff, a.quotient_mk_eq_one, ha]
        rfl
      · intro e z b
        let : DiscreteTopology a.quotient := QuotientGroup.discreteTopology (by
          rw [ha]
          exact hU.preimage continuous_subtype_val)
        let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
        let q : X → a.quotient := fun x ↦ e.equiv.symm (Multiplicative.ofAdd (elementaryCover x z b))
        have hq : Continuous q := e.equiv.symm.continuous.comp
          (continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
            ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const))
        change ContDiff ℝ (p : ℕ∞) (fun x ↦ f₀ (q x))
        have heq : (fun x ↦ f₀ (q x)) = fun _ : X ↦ f₀ (q 0) :=
          funext fun x ↦ congrArg f₀ (TotallyDisconnectedSpace.eq_of_continuous q hq x 0)
        rw [heq]
        exact contDiff_const
  have hSub : Function.support g ⊆ (U : Set G) := support_indicator_subset
  have hSupport : HasCompactSupport g :=
    hUc.of_isClosed_subset isClosed_closure (closure_minimal hSub hClosed)
  let f : 𝒟(G) := ⟨g, (mem_bruhatSmoothSubmodule_iff _).mpr hSmooth, hSupport⟩
  have hOne : g 1 = 1 := indicator_of_mem U.one_mem (fun _ : G ↦ (1 : ℂ))
  have hOut : (∫ u in (U : Set G)ᶜ, f.val u * num u / den u ∂μ) = 0 := by
    change (∫ u in (U : Set G)ᶜ, g u * num u / den u ∂μ) = 0
    calc
      _ = ∫ _u in (U : Set G)ᶜ, (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU.measurableSet.compl
        intro u hu
        have hgu : g u = 0 := indicator_of_notMem hu _
        simp only [hgu, zero_mul, zero_div]
      _ = 0 := by simp
  have hIn : (∫ u in (U : Set G), (f.val u - f.val 1) * num u / den u ∂μ) = 0 := by
    change (∫ u in (U : Set G), (g u - g 1) * num u / den u ∂μ) = 0
    calc
      _ = ∫ _u in (U : Set G), (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU.measurableSet
        intro u hu
        have hgu : g u = 1 := indicator_of_mem hu (fun _ : G ↦ (1 : ℂ))
        simp only [hgu, hOne, sub_self, zero_mul, zero_div]
      _ = 0 := by simp
  refine ⟨f, rfl, ?_⟩
  have hValue := heval f
  have hfOne : f.val 1 = 1 := hOne
  rw [hOut, hIn, hfOne, add_zero, mul_zero, zero_sub, mul_one] at hValue
  exact hValue

/-- Paper: Lemma B.4.4.5, p. 622. The integer-unit indicator detects
the different contribution to the Fourier-defined principal value. The
unit-subtracted finite part is zero on this test. -/
theorem finiteConnesWeilPrincipalValue_integerUnits (v : Primes(F)) :
    ∃ f : 𝒟((v.adicCompletion F)ˣ),
      f.val = indicator ((O(v)).units : Set (v.adicCompletion F)ˣ) (fun _ ↦ 1) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        -(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ) := by
  let U : Subgroup (v.adicCompletion F)ˣ := (O(v)).units
  have hU : IsOpen (U : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (U : Set (v.adicCompletion F)ˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  exact finiteConnesWeilPrincipalValue_integerUnits_test U hU hUc (μ𝔭(v))
    (fun u : (v.adicCompletion F)ˣ ↦ (Real.sqrt ‖u.val‖ : ℂ))
    (fun u : (v.adicCompletion F)ˣ ↦ ((‖1 - u.val‖ : ℝ) : ℂ))
    (fun f ↦ finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f)
    finiteWeilScale(v) (((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ)
    (fun f ↦ (finiteConnesWeilPrincipalValue_eq_finitePart v f).2.2)

/-- Paper: Remark B.4.4.6, p. 623. A finite local test agrees with its value at
one on a neighborhood of one, so the unit-subtracted integrand vanishes there. -/
theorem finiteWeilTest_eventually_eq_at_one (v : Primes(F)) (f : 𝒟((v.adicCompletion F)ˣ)) :
    ∀ᶠ u in 𝓝 (1 : (v.adicCompletion F)ˣ), f.val u = f.val 1 := by
  let G := (v.adicCompletion F)ˣ
  have hf : IsBruhatSmooth f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1
  obtain ⟨k, hk, hInv, _⟩ := hf 0
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
  obtain ⟨γ, _, hγ, hker, _⟩ := lca_dualSubgroup_quotient A
  let Q := PontryaginDual A.val
  let : LocallyCompactSpace A.val := A.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨n, ⟨charts⟩⟩ := isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp A.property.2
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q := charts
  let : LocallyConnectedSpace Q := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) Q
  let B : OpenSubgroup G :=
    ⟨(v.adicCompletionIntegers F).units, Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)⟩
  let : CompactSpace B.toSubgroup := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j : B.toSubgroup → v.adicCompletion F := Units.val ∘ Subtype.val
  have hj : Topology.IsEmbedding j :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).comp Topology.IsEmbedding.subtypeVal
  let η : B.toSubgroup →ₜ* Q := γ.comp ⟨B.toSubgroup.subtype, continuous_subtype_val⟩
  have hη : Continuous η := η.continuous
  have hηOpen : IsOpenMap η := hγ.isOpenMap.comp B.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hSmall (U : Set Q) (hU : U ∈ 𝓝 (1 : Q)) : ∃ V : OpenSubgroup Q, (V : Set Q) ⊆ U := by
    have hpre : η ⁻¹' U ∈ 𝓝 (1 : B.toSubgroup) :=
      hη.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
    rw [hj.isInducing.nhds_eq_comap] at hpre
    obtain ⟨S, hS, hSsub⟩ := mem_comap.mp hpre
    let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨r, hr⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hS
    let W := (fun x : B.toSubgroup ↦ j x - j 1) ⁻¹' {y | ν.restrict y < r.val}
    have hW : IsClopen W :=
      (Valued.isClopen_ball (v.adicCompletion F) r.val).preimage
        (hj.continuous.sub continuous_const)
    have h1W : (1 : B.toSubgroup) ∈ W := by
      change ν.restrict (j 1 - j 1) < r.val
      rw [sub_self, map_zero]
      exact pos_iff_ne_zero.mpr r.ne_zero
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
    refine ⟨⟨V.toSubgroup.map η.toMonoidHom, hηOpen _ V.isOpen⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hSsub (hr (hV hx))
  have hComponent : connectedComponent (1 : Q) = {1} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr mem_connectedComponent)
    intro y hy
    by_contra hne
    have h1y : (1 : Q) ∈ ({y} : Set Q)ᶜ :=
      fun h ↦ hne (mem_singleton_iff.mpr (mem_singleton_iff.mp h).symm)
    obtain ⟨V, hV⟩ := hSmall _ (isOpen_compl_singleton.mem_nhds h1y)
    have hyV := isPreconnected_connectedComponent.subset_isClopen V.isClopen
      ⟨1, mem_connectedComponent, V.one_mem⟩ hy
    exact (hV hyV) (mem_singleton y)
  have hOne : IsOpen ({1} : Set Q) := hComponent ▸ isOpen_connectedComponent
  have hkOpen : IsOpen (k : Set G) := by
    rw [← lcaDualAnnihilator_annihilator k hk.1, ← hker]
    exact hOne.preimage γ.continuous
  filter_upwards [hkOpen.mem_nhds k.one_mem] with u hu
  simpa only [mul_one] using hInv ⟨u, hu⟩ 1

end PrincipalValues

section IdelicExplicitFormula

/-- Paper: Theorem B.4.4.7, p. 623. Use the meromorphic continuation
from §3.2 to read off each zero's multiplicity in its norm-twist coordinate. -/
def explicitFormulaCompletedHeckeL (χ : U[F]) : ℂ → ℂ :=
  (completedHeckeL_exists_continuation χ).choose

/-- Paper: Theorem B.4.4.7, p. 623. The continued function is in
meromorphic normal form and agrees with the completed Euler product on the right half-plane. -/
theorem explicitFormulaCompletedHeckeL_spec (χ : U[F]) :
    MeromorphicNFOn (explicitFormulaCompletedHeckeL χ) univ ∧
      ∀ s : halfPlane, explicitFormulaCompletedHeckeL χ s = completedHeckeL χ s :=
  (completedHeckeL_exists_continuation χ).choose_spec

local notation "chartZeros(" τ ")" =>
  {z : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL z.1.val) univ z.2}
local notation "zeroMultiplicity(" z ")" =>
  (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (z).val.1.val) univ (z).val.2 : ℂ)
local notation "zeroCharacter(" z ")" => ideleClassNormTwist (z).val.1.val (z).val.2
local notation "classVolume" => (normOneIdeleClassTamagawaMeasure F univ).toReal
local notation "classMeasure" => ideleClassTamagawaMeasure F
local notation "classWeight(" g ", " a ")" =>
  ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (a : ℂ))
local notation "classMellinIntegrand(" f ", " c ", " a ")" =>
  (fun g : C[F] ↦ (f).val g * c g * classWeight(g, a))
local notation "finiteClassMap(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "infiniteClassMap(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w

-- TODO(paper-gap): The printed sum omits zero multiplicity. In (B.4.4.16)
-- the corrected archimedean Fourier pairing is already canonically normalized.
-- The proof on p. 625 also needs the norm-one volume divisor in D(φ) and
-- a comparison of the Mellin local terms with the principal values (footnote 27).
-- For (B.4.4.22), compact norm support handles nonunit shells at large primes.
-- Invariance under the local units at almost every prime makes the unit-shell test constant.

/-- Paper: Theorem B.4.4.7, pp. 623–626. The sum over completed Hecke zeros
equals the pole distributions minus the local principal value distributions.
The zero and finite-place series converge in the strong dual of the test space.
Deviation: A norm section indexes each quasi-character once, the signed formula
counts zero multiplicity, and the archimedean pairing already uses canonical
Haar normalization. -/
theorem idelicExplicitFormula (τ : ℝ≥0ˣ →ₜ* C[F]) (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ (spectral : chartZeros(τ) → StrongDual ℂ (𝒟(C[F])))
      (poles : StrongDual ℂ (𝒟(C[F])))
      (arch : InfinitePlace F → StrongDual ℂ (𝒟(C[F])))
      (finite : Primes(F) → StrongDual ℂ (𝒟(C[F]))),
      (∀ z f, spectral z f = zeroMultiplicity(z) / (classVolume : ℂ) *
        ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure) ∧
      (∀ f, poles f =
        ((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ)) ∧
      (∀ w f, ∃ test : 𝒟(w.Completionˣ),
        (∀ u, test.val u = f.val (infiniteClassMap(w) u)) ∧
        arch w f = infiniteConnesWeilPrincipalValue w test) ∧
      (∀ v f, ∃ test : 𝒟((v.adicCompletion F)ˣ),
        (∀ u, test.val u = f.val (finiteClassMap(v) u)) ∧
        finite v f = finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 test) ∧
      (∀ f, Summable (fun z ↦ ‖spectral z f‖)) ∧
      (∀ f, (Function.support (fun v ↦ finite v f)).Finite) ∧
      Summable finite ∧
      HasSum spectral (poles - (∑ w, arch w) - (∑' v, finite v)) := by sorry

-- TODO(paper-gap): Discreteness in each component imposes no bound on
-- the number of points in consecutive height intervals, even for G = ℝ₊ˣ.
-- In (B.4.4.18), c(τ(t)) already equals t^s. Use this radial character once.

/-- Paper: Lemma B.4.4.8, p. 624. Compactly supported Bruhat tests have
absolutely summable Mellin evaluations on polynomially counted samples in
a bounded strip of the quasi-character space of a real-modulated abelian Lie group.
Deviation: The joint counting bound includes both vertical height and torus
frequency, and uses a common strip. A product coordinate displays the compact
kernel as a torus times a finite abelian group. -/
theorem summable_bruhatMellin_of_polynomialCount
    {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {d : ℕ} (e : G ≃ₜ* (ℝ≥0ˣ × (Fin d → Circle) × A))
    (μ : Measure G) [μ.IsHaarMeasure]
    (Z : Set (ℂ × (Fin d → ℤ) × PontryaginDual A))
    (a b : ℝ) (_hStrip : ∀ z ∈ Z, z.1.re ∈ Icc a b)
    (_hCount : ∃ C k : ℕ, ∀ T : ℕ,
      {z ∈ Z | |z.1.im| ≤ T ∧ ∀ j, (z.2.1 j).natAbs ≤ T}.encard ≤
        ((C * (T + 1) ^ k : ℕ) : ℕ∞))
    (f : 𝒟(G)) :
    Summable (fun z : Z ↦ ‖∫ g, f.val g *
      (((e g).1.val : ℝ) : ℂ) ^ z.val.1 *
      (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.val.2.1 j) *
      (z.val.2.2 (e g).2.2 : ℂ) ∂μ‖) := by sorry

-- TODO(paper-gap): On p. 625, passing to a Lie quotient eliminates other kernel
-- characters. A uniform zero count with multiplicity for the remaining characters
-- is still needed to apply the corrected Lemma B.4.4.8.

/-- Paper: Lemma B.4.4.9, pp. 624–625. Mellin evaluations on any subset
of the completed Hecke zeros are absolutely summable after a real norm twist.
Deviation: Norm-section coordinates list the zeros once, and the weight also
counts their multiplicities as needed in the explicit formula. -/
theorem summable_ideleClassMellin_completedHeckeZeros (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (Z : Set (chartZeros(τ)))
    (f : 𝒟(C[F])) (a : ℝ) :
    Summable (fun z : Z ↦ ‖zeroMultiplicity(z.val) *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z.val), (a : ℂ)) g ∂classMeasure‖) :=
  by sorry

end IdelicExplicitFormula

end RiemannMasullo
