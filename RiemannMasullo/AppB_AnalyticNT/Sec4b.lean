module

public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec4a
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

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
      ∀ v, IsLeast (conductorExponents(χ, v)) (n v) := by sorry

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
    Summable (fun j ↦ ‖primeTerm(χ, f) j‖) := by sorry

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
      ∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v) := by sorry

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
      (1 / 2 : ℂ) * ∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) := by sorry

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
        f.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ := by sorry

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
      ENNReal.ofReal (Real.log q(v) / V𝔭(v)) • μ𝔭(v) := by sorry

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
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * f.val 1 := by sorry

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

/-- Paper: Lemma B.4.4.5, p. 622. The integer-unit indicator detects
the different contribution to the Fourier-defined principal value. The
unit-subtracted finite part is zero on this test. -/
theorem finiteConnesWeilPrincipalValue_integerUnits (v : Primes(F)) :
    ∃ f : 𝒟((v.adicCompletion F)ˣ),
      f.val = indicator ((O(v)).units : Set (v.adicCompletion F)ˣ) (fun _ ↦ 1) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        -(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ) := by sorry

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
