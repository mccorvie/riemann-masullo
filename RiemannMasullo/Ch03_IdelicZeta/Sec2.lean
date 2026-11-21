module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta

import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Convergence

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Global idelic zeta functions

Masullo, §3.2, pp. 122–128. This section uses the global adelic theta and Fourier
operators of §2.2 and the Tamagawa measures of §A.3.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "𝒳[" F "]" => HeckeCharacter (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])
local notation "classNormℝ" => fun (g : C[F]) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Set.Ioi (1 : ℝ)

section Hecke

/-- Paper: §3.2.1, p. 122. Raising the positive idele class norm to a fixed
complex power gives a continuous multiplicative function. -/
theorem ideleClassNorm_cpow_properties (s : ℂ) :
    (classNormℝ (1 : C[F]) : ℂ) ^ s = 1 ∧
    (∀ g h : C[F], (classNormℝ (g * h) : ℂ) ^ s =
      (classNormℝ g : ℂ) ^ s * (classNormℝ h : ℂ) ^ s) ∧
    Continuous (fun g : C[F] ↦ (classNormℝ g : ℂ) ^ s) := by
  have hcont : Continuous (ideleClassNorm F) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (ideleGroup_topology F).2.2.2.2.1
  refine ⟨by simp, ?_, ?_⟩
  · intro g h
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s
  · have hr : Continuous classNormℝ := NNReal.continuous_coe.comp (Units.continuous_val.comp hcont)
    apply (Complex.continuous_ofReal.comp hr).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))

/-- Paper: §3.2.1, p. 122. The coordinate at a unitary character `χ`
sends `s` to the quasi-character `χ |·|^s`. -/
def ideleClassNormTwist (χ : U[F]) (s : ℂ) : 𝒳[F] :=
  let unitary : 𝒳[F] :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  let power : 𝒳[F] :=
    ⟨{ toFun := fun g ↦ (classNormℝ g : ℂ) ^ s
       map_one' := (ideleClassNorm_cpow_properties (F := F) s).1
       map_mul' := (ideleClassNorm_cpow_properties (F := F) s).2.1 },
     (ideleClassNorm_cpow_properties (F := F) s).2.2⟩
  unitary * power

/-- Paper: §3.2.1, p. 122. At exponent one the twist of the trivial character
takes the value of the idele class norm. -/
theorem ideleClassNormTwist_one_one (g : C[F]) :
    ideleClassNormTwist (1 : U[F]) 1 g = (classNormℝ g : ℂ) := by
  change (1 : ℂ) * (classNormℝ g : ℂ) ^ (1 : ℂ) = _
  rw [one_mul, Complex.cpow_one]

local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0

/-- Paper: Equation (3.2.1.2), p. 123. At an unramified finite prime the Euler
factor is the reciprocal of `1 - χ(πᵥ) (N v)^(-s)`. A ramified place contributes one. -/
def finiteHeckeEulerFactor (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  open Classical in
  if χ₀(χ).IsUnramifiedAt v then
    (1 - χ₀(χ).localValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

/-- Paper: Equation (3.2.1.1), p. 122. At an unramified finite place and in the
half-plane of absolute convergence, the reciprocal Euler factor can be evaluated
on any uniformizer using the twisted quasi-character. -/
theorem finiteHeckeEulerFactor_inv_uniformizer (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) (hχ : χ₀(χ).IsUnramifiedAt v)
    {s : ℂ} (hs : s ∈ halfPlane) :
    (finiteHeckeEulerFactor χ v s)⁻¹ =
      1 - finitePlaceRestriction F v (ideleClassNormTwist χ s) π := by
  classical
  rw [finiteHeckeEulerFactor, ite_eq_left hχ, inv_inv, hχ.localValue_eq _ hπ,
    HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
  change 1 - ((χ g : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ)) * _ =
    1 - (χ g : ℂ) * (classNormℝ g : ℂ) ^ s
  have hn : classNormℝ g = (v.asIdeal.absNorm : ℝ)⁻¹ := by
    change ((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) : ℝ≥0) : ℝ) = _
    rw [ideleClassNorm_ofAdicCompletion]
    exact norm_uniformizer_adicCompletion v _ hπ
  rw [Complex.cpow_zero, mul_one, hn, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg
    (Nat.cast_nonneg _) s, Complex.cpow_neg, Complex.ofReal_natCast]

/-- Paper: Equation (3.2.1.4), p. 123. A real local unitary character has a
unique imaginary radial exponent and a unique sign parity. -/
theorem realHeckeCharacter_parameters (χ : U[F]) (v : InfinitePlace F) (hv : v.IsReal) :
    ∃! a : ℂ × Fin 2, a.1.re = 0 ∧ ∀ x : ℝˣ,
      infinitePlaceRestriction F v χ₀(χ)
          (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x) =
        (‖(x : ℝ)‖ : ℂ) ^ a.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.2.val := by
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  let i : ℝˣ →ₜ* v.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.units_map _⟩
  let c := (infinitePlaceRestriction F v χ₀(χ)).comp i
  apply existsUnique_realUnits_character_parameters c
  intro x
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v (i x)
  change ‖(χ g : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ)‖ = 1
  simp

/-- Paper: Equation (3.2.1.5), p. 123. A complex local unitary character has a
unique imaginary radial exponent and integer angular weight.
Deviation: We take the radius in the paper to be the normalized absolute value `‖x‖²`. -/
theorem complexHeckeCharacter_parameters (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    ∃! a : ℂ × ℤ, a.1.re = 0 ∧ ∀ x : ℂˣ,
      infinitePlaceRestriction F v χ₀(χ)
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom x) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a.1 * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ a.2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  let i : ℂˣ →ₜ* v.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous.units_map _⟩
  let c := (infinitePlaceRestriction F v χ₀(χ)).comp i
  apply existsUnique_complexUnits_character_parameters c
  intro x
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v (i x)
  change ‖(χ g : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ)‖ = 1
  simp

/-- Paper: Equations (3.2.1.3)–(3.2.1.5), p. 123. The global gamma factor
multiplies the real and complex local gamma factors, using the local radial
exponent after twisting and the real sign parity or complex angular weight.
Deviation: The local argument explicitly includes any imaginary radial exponent of the fixed
unitary character. Mathlib's complex gamma factor includes a factor of two, which is divided out. -/
def heckeGammaFactor (χ : U[F]) (s : ℂ) : ℂ :=
  open Classical in
  ∏ v : InfinitePlace F, if hv : v.IsReal then
    let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
  else
    let a := (complexHeckeCharacter_parameters χ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2

/-- Paper: Equations (3.2.1.3)–(3.2.1.5), p. 123. The trivial character contributes
one unshifted real or complex gamma factor at each infinite place. -/
theorem heckeGammaFactor_one (s : ℂ) :
    heckeGammaFactor (1 : U[F]) s =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F := by
  classical
  have hR (v : InfinitePlace F) (hv : v.IsReal) :
      (realHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose = (0, 0) := by
    apply (realHeckeCharacter_parameters (1 : U[F]) v hv).unique
      (realHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose_spec
    refine ⟨rfl, fun x ↦ ?_⟩
    change (1 : ℂ) * _ ^ (0 : ℂ) = (‖(x : ℝ)‖ : ℂ) ^ (0 : ℂ) * _ ^ (0 : ℕ)
    simp
  have hC (v : InfinitePlace F) (hv : v.IsComplex) :
      (complexHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose = (0, 0) := by
    apply (complexHeckeCharacter_parameters (1 : U[F]) v hv).unique
      (complexHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose_spec
    refine ⟨rfl, fun x ↦ ?_⟩
    change (1 : ℂ) * _ ^ (0 : ℂ) = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (0 : ℂ) * _ ^ (0 : ℤ)
    simp
  unfold heckeGammaFactor
  simp_rw [hR, hC]
  simp only [Fin.val_zero, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, dite_eq_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, ← Fintype.card_subtype, InfinitePlace.not_isReal_iff_isComplex]

/-- The value of a unitary Hecke character on a local uniformizer has norm one. -/
theorem norm_ideleClassNormTwist_zero_localValue (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) :
    ‖χ₀(χ).localValue v‖ = 1 := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let π := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose
  let u := Units.mk0 (π : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  change ‖χ₀(χ).restrict v (u : v.adicCompletion F)‖ = 1
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change ‖(χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) * _ ^ (0 : ℂ)‖ = 1
  simp

private theorem norm_finiteHeckeEulerFactor_sub_one_le (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) {r : ℝ} (hr : 1 < r) {s : ℂ} (hs : r ≤ s.re) :
    ‖finiteHeckeEulerFactor χ v s - 1‖ ≤ 2 * (v.asIdeal.absNorm : ℝ) ^ (-r) := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  have hq : 2 ≤ q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.two_le_absNorm_nnreal v
  have hq' : 1 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  rw [finiteHeckeEulerFactor]
  split_ifs with hχ
  · let z := χ₀(χ).localValue v * (q : ℂ) ^ (-s)
    change ‖(1 - z)⁻¹ - 1‖ ≤ 2 * q ^ (-r)
    have hz : ‖z‖ = q ^ (-s.re) := by
      simp [z, norm_ideleClassNormTwist_zero_localValue,
        Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hcomp : ‖z‖ ≤ q ^ (-r) :=
      hz.le.trans (Real.rpow_le_rpow_of_exponent_le hq' (by linarith))
    have hhalf : q ^ (-r) ≤ 1 / 2 := calc
      q ^ (-r) ≤ q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq' (by linarith)
      _ = 1 / q := by rw [Real.rpow_neg hqpos.le, Real.rpow_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
    have hd : 1 / 2 ≤ ‖1 - z‖ := by
      have ht := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at ht
      linarith
    have hn : 1 - z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    rw [show (1 - z)⁻¹ - 1 = z / (1 - z) by field_simp; ring, norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖1 - z‖)).mpr
    calc
      ‖z‖ ≤ q ^ (-r) := hcomp
      _ = (2 * q ^ (-r)) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  · simp only [sub_self, norm_zero]
    positivity

/-- Paper: Lemma 3.2.1.1, p. 123. On each compact subset of `Re(s) > 1`,
the deviations of the Euler factors from one are absolutely and uniformly summable. -/
theorem finiteHeckeEulerFactor_summableUniformlyOn (χ : U[F])
    (K : Set ℂ) (hK : IsCompact K) (h : K ⊆ halfPlane) :
    SummableUniformlyOn (fun v s ↦ ‖finiteHeckeEulerFactor χ v s - 1‖) K := by
  obtain ⟨r, hr, hmin⟩ : ∃ r : ℝ, 1 < r ∧ ∀ s ∈ K, r ≤ s.re := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨2, by norm_num, by simp⟩
    · obtain ⟨s, hs, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
      exact ⟨s.re, h hs, fun x hx ↦ hmin hx⟩
  have hu : Summable fun v : HeightOneSpectrum (𝓞 F) ↦ (v.asIdeal.absNorm : ℝ) ^ (-r) :=
    (summable_absNorm_rpow F hr).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  apply (HasSumUniformlyOn.of_norm_le_summable (hu.mul_left 2) _).summableUniformlyOn
  intro v s hs
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_finiteHeckeEulerFactor_sub_one_le χ v hr (hmin s hs)

/-- Paper: Definition 3.2.1.2, p. 123. The Hecke L-function on the half-plane
is the archimedean gamma factor times Mathlib's finite Hecke L-series. -/
def completedHeckeL (χ : U[F]) (s : halfPlane) : ℂ :=
  heckeGammaFactor χ s * χ₀(χ).LSeries s


/-- Paper: Proposition 3.2.1.3(4), p. 123. A zero of the continuation in
the positive half-plane lies strictly to the left of `Re(s) = 1`. -/
theorem completedHeckeL_continuation_zeros (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    {s : ℂ} (hs : 0 < s.re) (hzero : 0 < meromorphicOrderAt L s) :
    s.re < 1 := by sorry

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Hecke L-function
uses Mathlib's Hecke L-series on the half-plane of absolute convergence. -/
def finiteHeckeL (χ : U[F]) (s : halfPlane) : ℂ :=
  χ₀(χ).LSeries s

/-- Paper: Definition 3.2.1.4, pp. 123–124. In the half-plane where the Euler
product is defined, Mathlib's finite Hecke Dirichlet series is absolutely summable. -/
theorem finiteHeckeL_seriesSummable (χ : U[F]) (s : halfPlane) :
    LSeriesSummable χ₀(χ).LFunction s := by
  exact LSeriesSummable_heckeLFunction _ s.property fun v _ ↦
    (norm_ideleClassNormTwist_zero_localValue χ v).le

/-- Each formal local Euler factor has a geometric Dirichlet series with the stated analytic
value in the half-plane of absolute convergence. -/
private theorem LSeriesHasSum_finiteHeckeEulerFactor (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (χ₀(χ).localEulerFactor v) s (finiteHeckeEulerFactor χ v s) := by
  classical
  let a := if χ₀(χ).IsUnramifiedAt v then χ₀(χ).localValue v else 0
  let q := v.asIdeal.absNorm
  let z := a * (q : ℂ) ^ (-s)
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have ha : ‖a‖ ≤ 1 := by
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [a, h, norm_ideleClassNormTwist_zero_localValue]
  have hz : ‖z‖ < 1 := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < (q : ℝ)) _,
      Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hq' (by linarith))
  have hval : finiteHeckeEulerFactor χ v s = (1 - z)⁻¹ := by
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, z, a, q, h]
  rw [hval, HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
    hecke_localPowerSeries_eq_mk]
  obtain ⟨hpow, hout⟩ := LSeries_term_geometric_ofPowerSeries hq a s
  apply (Nat.pow_right_injective hq).hasSum_iff hout |>.mp
  exact (hasSum_geometric_of_norm_lt_one hz).congr_fun hpow

/-- Paper: Definition 3.2.1.4, pp. 123–124. The partial Hecke Euler products converge
uniformly to the Hecke Dirichlet series on every closed half-plane to the right of one. -/
theorem finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane (χ : U[F]) {a : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦ fun s ↦ ∏ v ∈ S, finiteHeckeEulerFactor χ v s)
      χ₀(χ).LSeries atTop {s : ℂ | a ≤ s.re} := by
  obtain ⟨r, hr, hra⟩ := exists_between ha
  let Places := HeightOneSpectrum (𝓞 F)
  let ψ := χ₀(χ)
  let f := ψ.localEulerFactor
  let u (v : Places) := 2 * (v.asIdeal.absNorm : ℝ) ^ (-r)
  have hu : Summable u := ((summable_absNorm_rpow F hr).comp_injective
    (fun v w (h : (v : Places).asIdeal = w.asIdeal) ↦ HeightOneSpectrum.ext h)).mul_left 2
  have hlocal (v : Places) := LSeries_heckeLocalEulerFactor_bound ψ v (s := (r : ℂ)) hr
    (fun _ ↦ (norm_ideleClassNormTwist_zero_localValue χ v).le)
  have hp := LSeries_finset_prod_bound f (r : ℂ) (u := u)
    (fun v ↦ (hlocal v).1) (fun v ↦ (hlocal v).2)
  have hu₀ (v : Places) : 0 ≤ u v :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC (S : Finset Places) :
      (∑' n, ‖LSeries.term ⇑(∏ v ∈ S, f v) (r : ℂ) n‖) ≤ Real.exp (∑' v, u v) :=
    (hp S).2.trans (Real.exp_le_exp.mpr (hu.sum_le_tsum S (fun v _ ↦ hu₀ v)))
  have h := tendstoUniformlyOn_LSeries_of_eventuallyEq
    (fun S : Finset Places ↦ ⇑(∏ v ∈ S, f v)) ψ.LFunction hra (Real.exp_pos _).le
    (fun S ↦ (hp S).1) (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), hr⟩) hC
    (heckeLocalEulerFactor_eventually_prod_eq ψ)
  apply h.congr
  exact Filter.Eventually.of_forall fun S s hs ↦
    (LSeriesHasSum_finset_prod f _ s (fun v ↦ LSeriesHasSum_finiteHeckeEulerFactor χ v
      (ha.trans_le hs)) S).LSeries_eq

/-- The reciprocal archimedean factor is entire, including at the poles of the gamma factors. -/
theorem differentiable_inv_heckeGammaFactor (χ : U[F]) :
    Differentiable ℂ (fun s ↦ (heckeGammaFactor χ s)⁻¹) := by
  classical
  unfold heckeGammaFactor
  simp_rw [← Finset.prod_inv_distrib]
  apply Differentiable.fun_finsetProd
  intro v _
  by_cases hv : v.IsReal
  · simp only [dite_eq_left hv]
    apply Complex.differentiable_Gammaℝ_inv.comp
    fun_prop
  · simp only [dite_eq_right hv, div_eq_mul_inv, mul_inv_rev, inv_inv]
    apply Differentiable.const_mul
    apply Complex.differentiable_Gammaℂ_inv.comp
    fun_prop

/-- No archimedean gamma factor vanishes on the positive half-plane. -/
theorem heckeGammaFactor_ne_zero_of_re_pos (χ : U[F]) {s : ℂ} (hs : 0 < s.re) :
    heckeGammaFactor χ s ≠ 0 := by
  classical
  unfold heckeGammaFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  by_cases hv : v.IsReal
  · simp only [dite_eq_left hv]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    simp only [Complex.add_re, Complex.natCast_re, ha, add_zero]
    positivity
  · simp only [dite_eq_right hv]
    apply (div_ne_zero · two_ne_zero)
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let a := (complexHeckeCharacter_parameters χ v hv').exists.choose
    have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
    have ht : 0 < (s + a.1 + (a.2.natAbs : ℂ) / 2).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, add_zero]
      positivity
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ht)
      (Complex.Gammaℝ_ne_zero_of_re_pos (by
        simpa only [Complex.add_re, Complex.one_re] using
          (add_pos ht zero_lt_one)))

/-- The archimedean factor is holomorphic on the positive half-plane. -/
theorem differentiableAt_heckeGammaFactor_of_re_pos (χ : U[F]) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (heckeGammaFactor χ) s := by
  have h := (differentiable_inv_heckeGammaFactor χ).differentiableAt (x := s)
  have hd : DifferentiableAt ℂ (fun t ↦ ((heckeGammaFactor χ t)⁻¹)⁻¹) s :=
    h.inv (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs))
  simpa only [inv_inv] using hd

/-- Paper: Lemma 3.2.1.1, p. 123. The Euler product multiplied by the archimedean
gamma factor converges uniformly on compact subsets of the open half-plane. -/
theorem completedHeckeEulerProduct_hasProdUniformlyOn (χ : U[F])
    (K : Set ℂ) (hK : IsCompact K) (h : K ⊆ halfPlane) :
    TendstoUniformlyOn
      (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦
        fun s ↦ heckeGammaFactor χ s * ∏ v ∈ S, finiteHeckeEulerFactor χ v s)
      (fun s ↦ heckeGammaFactor χ s * χ₀(χ).LSeries s) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  have hu := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ (a := s₀.re) (h hs₀)).mono
    (fun s hs ↦ hmin hs : K ⊆ {s : ℂ | s₀.re ≤ s.re})
  have hc : ContinuousOn (fun s ↦ ‖heckeGammaFactor χ s‖) K := fun s hs ↦
    (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans (h hs))).continuousAt.norm.continuousWithinAt
  obtain ⟨b, _, hb⟩ := hK.exists_isMaxOn hne hc
  let B := ‖heckeGammaFactor χ b‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / B) (div_pos hε hB)] with T hT
  intro s hs
  have hbound : ‖heckeGammaFactor χ s‖ ≤ B := (hb hs).trans (by dsimp [B]; linarith)
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have hsmall := hT s hs
  rw [dist_eq_norm] at hsmall
  exact (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_left hsmall hB).trans_eq (mul_div_cancel₀ _ hB.ne'))

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Hecke L-function
is the value of the convergent Euler product with the ramified factors omitted. -/
theorem finiteHeckeL_hasProd (χ : U[F]) (s : halfPlane) :
    HasProd (fun v ↦ finiteHeckeEulerFactor χ v s) (finiteHeckeL χ s) := by
  have h := finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ (a := s.val.re) s.property
  exact h.tendsto_at (x := s.val) (Set.mem_ofPred.mpr (le_refl s.val.re))

/-- Paper: Definition 3.2.1.2, p. 123. For the trivial character the completed
L-function on the half-plane is the corresponding gamma product times Dedekind zeta. -/
theorem completedHeckeL_one_eq_dedekindZeta (s : halfPlane) :
    completedHeckeL (1 : U[F]) s =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F * dedekindZeta F s := by
  classical
  have hχ : χ₀((1 : U[F])) = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      finiteHeckeEulerFactor (1 : U[F]) v s =
        (1 - (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    have hunit (u : (v.adicCompletion F)ˣ) : (1 : 𝒳[F]).restrict v u = 1 := by
      rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
      rfl
    have hu : (1 : 𝒳[F]).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
      val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
    have hval : (1 : 𝒳[F]).localValue v = 1 := hunit u
    rw [finiteHeckeEulerFactor, hχ, ite_eq_left hu, hval, one_mul]
  have h := (finiteHeckeL_hasProd (1 : U[F]) s).unique
    ((dedekindZeta_hasProd F s.property).congr_fun hlocal)
  exact congrArg₂ (· * ·) (heckeGammaFactor_one s) h

/-- A unitary character trivial on the norm-one subgroup is a unique imaginary power of the norm. -/
private theorem existsUnique_ideleClassNormTwist (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, χ₀(χ) = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let c : ℝ≥0ˣ →ₜ* ℂ := χ₀(χ).comp ⟨σ, hσ⟩
  have hunit (g : C[F]) : χ₀(χ) g = (χ g : ℂ) := by
    change (χ g : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ :=
    existsUnique_unitaryComplexPower c (fun u ↦ by
      change ‖χ₀(χ) (σ u)‖ = 1
      rw [hunit, Circle.norm_coe])
  have hparam : -Complex.I * ((-z.im : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzre]
  refine ⟨-z.im, ?_, ?_⟩
  · change χ₀(χ) = ideleClassNormTwist (1 : U[F]) (-Complex.I * ((-z.im : ℝ) : ℂ))
    rw [hparam]
    ext1 g
    let u := ideleClassNorm F g
    have hk : g / σ u ∈ (ideleClassNorm F).ker := MonoidHom.mem_ker.mpr (by
      rw [map_div, hnorm u, div_self'])
    have hkχ : χ (g / σ u) = 1 :=
      DFunLike.congr_fun hχ (⟨g / σ u, hk⟩ : (ideleClassNorm F).ker)
    have he : χ₀(χ) (g / σ u) = 1 := by rw [hunit, hkχ, Circle.coe_one]
    calc
      χ₀(χ) g = χ₀(χ) (g / σ u) * c u := by
        change χ₀(χ) g = χ₀(χ) (g / σ u) * χ₀(χ) (σ u)
        rw [← map_mul, div_mul_cancel]
      _ = ideleClassNormTwist (1 : U[F]) z g := by
        change χ₀(χ) (g / σ u) * c u = 1 * (classNormℝ g : ℂ) ^ z
        rw [he, hz u]
  · intro t ht
    have he : -Complex.I * (t : ℂ) = z := huniq _ ⟨by simp [Complex.mul_re], fun u ↦ by
      change χ₀(χ) (σ u) = _
      rw [ht]
      change (1 : ℂ) * (classNormℝ (σ u) : ℂ) ^ (-Complex.I * (t : ℂ)) = _
      dsimp only
      rw [one_mul, hnorm u]⟩
    apply neg_eq_iff_eq_neg.mp
    simpa [Complex.mul_im] using congrArg Complex.im he

/-- An imaginary norm twist translates the argument of the archimedean product. -/
private theorem heckeGammaFactor_of_normTwist (χ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hχ : χ₀(χ) = ideleClassNormTwist (1 : U[F]) a) (s : ℂ) :
    heckeGammaFactor χ s = heckeGammaFactor (1 : U[F]) (s + a) := by
  classical
  have hre (v : InfinitePlace F) (hv : v.IsReal) :
      (realHeckeCharacter_parameters χ v hv).exists.choose = (a, 0) := by
    apply (realHeckeCharacter_parameters χ v hv).unique
      (realHeckeCharacter_parameters χ v hv).exists.choose_spec
    refine ⟨ha, fun x ↦ ?_⟩
    rw [hχ]
    let u := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x
    change 1 * (classNormℝ (IdeleClassGroup.ofCompletion (𝓞 F) F v u) : ℂ) ^ a =
      (‖(x : ℝ)‖ : ℂ) ^ a * _ ^ (0 : ℕ)
    dsimp only
    rw [ideleClassNorm_ofCompletion, hv.mult_eq_one, pow_one]
    have hn : ((↑(Units.map nnNormHom.toMonoidHom u) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
      let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      change ‖e (x : ℝ)‖ = ‖(x : ℝ)‖
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℝ)
    rw [hn, one_mul, pow_zero, mul_one]
  have hco (v : InfinitePlace F) (hv : v.IsComplex) :
      (complexHeckeCharacter_parameters χ v hv).exists.choose = (a, 0) := by
    apply (complexHeckeCharacter_parameters χ v hv).unique
      (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
    refine ⟨ha, fun x ↦ ?_⟩
    rw [hχ]
    let u := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom x
    change 1 * (classNormℝ (IdeleClassGroup.ofCompletion (𝓞 F) F v u) : ℂ) ^ a =
      ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a * _ ^ (0 : ℤ)
    dsimp only
    rw [ideleClassNorm_ofCompletion, hv.mult_eq_two, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    have hn : ((↑(Units.map nnNormHom.toMonoidHom u) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ := by
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
      change ‖e (x : ℂ)‖ = ‖(x : ℂ)‖
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℂ)
    rw [hn, one_mul, zpow_zero, mul_one]
  rw [heckeGammaFactor_one, heckeGammaFactor]
  simp_rw [hre, hco]
  simp only [Fin.val_zero, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, dite_eq_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, ← Fintype.card_subtype, InfinitePlace.not_isReal_iff_isComplex]

/-- The finite Euler factor of a norm twist depends on the sum of the two exponents. -/
private theorem finiteHeckeEulerFactor_of_normTwist (χ : U[F]) (a : ℂ)
    (hχ : χ₀(χ) = ideleClassNormTwist (1 : U[F]) a)
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    finiteHeckeEulerFactor χ v s = finiteHeckeEulerFactor (1 : U[F]) v (s + a) := by
  classical
  have hval (z : ℂ) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) z).restrict v u =
        (‖(u : v.adicCompletion F)‖ : ℂ) ^ z := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change 1 * (classNormℝ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) ^ z = _
    dsimp only
    rw [one_mul, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu (z : ℂ) : (ideleClassNormTwist (1 : U[F]) z).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist (1 : U[F]) z).restrict v u = 1
    rw [hval z u, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  rw [finiteHeckeEulerFactor, finiteHeckeEulerFactor, hχ, ite_eq_left (hu a), ite_eq_left (hu 0),
    (hu a).localValue_eq u hπ, (hu 0).localValue_eq u hπ, hval, hval, hnorm, Complex.cpow_zero,
    one_mul, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
    ← Complex.cpow_neg, Complex.ofReal_natCast,
    ← Complex.cpow_add _ _ (by exact_mod_cast ((zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))).ne'),
    neg_add, add_comm (-a)]

/-- On the half-plane of convergence, twisting the trivial character shifts the
completed L-function by the norm exponent. -/
private theorem completedHeckeL_of_normTwist (χ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hχ : χ₀(χ) = ideleClassNormTwist (1 : U[F]) a) (s : halfPlane) :
    completedHeckeL χ s =
      completedHeckeL (1 : U[F]) ⟨(s : ℂ) + a, by
        change 1 < (s : ℂ).re + a.re
        rw [ha, add_zero]
        exact s.property⟩ := by
  let w : halfPlane := ⟨(s : ℂ) + a, by
    change 1 < (s : ℂ).re + a.re
    rw [ha, add_zero]
    exact s.property⟩
  have h := (finiteHeckeL_hasProd χ s).unique <|
    (finiteHeckeL_hasProd (1 : U[F]) w).congr_fun
      (fun v ↦ finiteHeckeEulerFactor_of_normTwist χ a hχ v s)
  exact congrArg₂ (· * ·) (heckeGammaFactor_of_normTwist χ a ha hχ s) h

/-- The class number formula gives a simple pole at one for a continuation
of the completed L-function of the trivial character. -/
private theorem completedHeckeL_one_order_one (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (h : ∀ s : halfPlane, L s = completedHeckeL (1 : U[F]) s) :
    meromorphicOrderAt L 1 = -1 := by
  let P (s : ℂ) := (s - 1) * L s
  let γ := heckeGammaFactor (1 : U[F])
  let c : ℂ := γ 1 * dedekindZeta_residue F
  have hγ : DifferentiableAt ℂ γ 1 :=
    differentiableAt_heckeGammaFactor_of_re_pos _ (by simp)
  have hc : c ≠ 0 := mul_ne_zero
    (heckeGammaFactor_ne_zero_of_re_pos _ (by simp))
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using (show 1 < r from hr).ne'
  have hlim : Tendsto (fun r : ℝ ↦ P r) (𝓝[>] (1 : ℝ)) (𝓝 c) := by
    apply ((hγ.continuousAt.tendsto.comp (hreal.mono_right nhdsWithin_le_nhds)).mul
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (r : ℂ) ∈ halfPlane := by simpa using hr
    have he := h ⟨r, hr'⟩
    rw [completedHeckeL_one_eq_dedekindZeta, ← heckeGammaFactor_one] at he
    dsimp [P, γ]
    rw [show L r = heckeGammaFactor (1 : U[F]) r * dedekindZeta F r from he]
    ring
  have hsub : AnalyticAt ℂ (fun s : ℂ ↦ s - 1) 1 := by fun_prop
  have horder : meromorphicOrderAt P 1 = 0 := by
    rcases lt_trichotomy (meromorphicOrderAt P 1) 0 with hneg | he | hpos
    · have hinf := (tendsto_norm_atTop_iff_cobounded.mpr
        (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).comp hreal
      exact (not_tendsto_atTop_of_tendsto_nhds hlim.norm hinf).elim
    · exact he
    · exact (hc (tendsto_nhds_unique hlim
        ((tendsto_zero_of_meromorphicOrderAt_pos hpos).comp hreal))).elim
  have hsubOrder : meromorphicOrderAt (fun s : ℂ ↦ s - 1) 1 = 1 := by
    exact (meromorphicOrderAt_eq_int_iff hsub.meromorphicAt (n := 1)).mpr
      ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, by simp⟩
  change meromorphicOrderAt ((fun s : ℂ ↦ s - 1) * L) 1 = 0 at horder
  rw [meromorphicOrderAt_mul hsub.meromorphicAt (hL (mem_univ _)).meromorphicAt, hsubOrder]
    at horder
  have he : (-(1 : ℤ) : WithTop ℤ) + (1 : WithTop ℤ) = 0 := by norm_num
  simpa [← add_assoc, he] using congrArg (fun x : WithTop ℤ ↦ (-1) + x) horder

/-- Paper: Proposition 3.2.1.3(2), p. 123. A continuation of the completed
Dedekind zeta function in the trivial Hecke character normalization is
holomorphic away from zero and one. -/
theorem completedHeckeL_one_analyticOnNhd (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (h : ∀ s : halfPlane, L s = completedHeckeL (1 : U[F]) s) :
    AnalyticOnNhd ℂ L ({0, 1}ᶜ : Set ℂ) := by sorry

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Euler product
converges uniformly on each compact subset of the half-plane. -/
theorem finiteHeckeL_hasProdUniformlyOn (χ : U[F]) (K : Set halfPlane) (hK : IsCompact K) :
    HasProdUniformlyOn (fun v (s : halfPlane) ↦ finiteHeckeEulerFactor χ v s) (finiteHeckeL χ) K := by
  apply hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨s₀, _, hmin⟩ := hK.exists_isMinOn hne
      (Complex.continuous_re.comp continuous_subtype_val).continuousOn
    have h := finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ (a := s₀.val.re) s₀.property
    exact (h.comp (fun s : halfPlane ↦ s.val)).mono fun s hs ↦ hmin hs

/-- Paper: Definition 3.2.1.4, p. 124. The finite Hecke L-function admits
a meromorphic continuation to the complex plane. -/
theorem finiteHeckeL_exists_continuation (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = finiteHeckeL χ s := by sorry

/-- Paper: Equation (3.2.1.9), p. 124. The reflection multiplier is the ratio
of the reflected and original gamma factors divided by the entire epsilon factor.
Deviation: Values at singularities use the meromorphic normal form. -/
def finiteHeckeReflectionFactor (χ : U[F]) (ε : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ (ε s)⁻¹ * (heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s)) univ

/-- The archimedean gamma factor is meromorphic on the plane. -/
theorem meromorphic_heckeGammaFactor (χ : U[F]) : Meromorphic (heckeGammaFactor χ) := by
  intro s
  have h : MeromorphicAt (fun t ↦ ((heckeGammaFactor χ t)⁻¹)⁻¹) s :=
    ((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicAt.inv
  simpa only [inv_inv] using h

/-- Paper: Equation (3.2.1.9), p. 124. At the midpoint for the trivial character
the gamma factors cancel, leaving the reciprocal epsilon factor. -/
theorem finiteHeckeReflectionFactor_one_half (ε : ℂ → ℂ) (hε : Differentiable ℂ ε)
    (hn : ∀ s, ε s ≠ 0) :
    finiteHeckeReflectionFactor (1 : U[F]) ε (1 / 2) = (ε (1 / 2))⁻¹ := by
  let G := heckeGammaFactor (1 : U[F])
  let p : ℂ := 1 / 2
  let f (s : ℂ) := (ε s)⁻¹ * (G (1 - s) / G s)
  have hG := meromorphic_heckeGammaFactor (1 : U[F])
  have hf : Meromorphic f := fun z ↦ (hε.analyticAt z).meromorphicAt.inv.mul
    (((hG (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)).div (hG z))
  have hp : 0 < p.re := by norm_num [p]
  have hsym : 1 - p = p := by dsimp [p]; ring
  have hG₀ : G p ≠ 0 := heckeGammaFactor_ne_zero_of_re_pos _ hp
  have haG : AnalyticAt ℂ G p := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos (1 : U[F]) hz).differentiableWithinAt)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
  have hfa : AnalyticAt ℂ f p := (hε.analyticAt p).inv (hn p) |>.mul
    (((hsym.symm ▸ haG : AnalyticAt ℂ G (1 - p)).comp (analyticAt_const.sub analyticAt_id)).div haG hG₀)
  change toMeromorphicNFOn _ univ p = _
  simp only [inv_one]
  change toMeromorphicNFOn f univ p = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf.meromorphicOn (Set.mem_univ p),
    toMeromorphicNFAt_eq_self.mpr hfa.meromorphicNFAt]
  change f p = (ε p)⁻¹
  simp [f, hsym, hG₀]

/-- Paper: Equation (3.2.1.8), p. 124. The finite continuations satisfy the
reflection equation with the displayed gamma ratio and a nowhere-vanishing entire
epsilon factor. Equality is taken off a discrete set, as an identity of meromorphic functions. -/
theorem finiteHeckeL_continuation_functionalEquation (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      L =ᶠ[codiscreteWithin univ] (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)) := by
  sorry

/-- Paper: Equation (3.2.1.10), p. 124. On a fixed closed vertical strip with
nonnegative real part, the reflection multiplier satisfies the stated power bound
as the absolute imaginary part tends to infinity. -/
theorem finiteHeckeReflectionFactor_bound (χ : U[F]) (L Ldual ε : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ) (hdual : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hn : ∀ s, ε s ≠ 0)
    (hEq : L =ᶠ[codiscreteWithin univ] (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)))
    (α β : ℝ) (hα : 0 ≤ α) (hβ : α ≤ β) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ s : ℂ, α ≤ s.re → s.re ≤ β → T ≤ |s.im| →
      ‖finiteHeckeReflectionFactor χ ε s‖ ≤ C * |s.im| ^
        ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by sorry

end Hecke

section Zeta

local instance globalZetaIdeleMeasurableSpace : MeasurableSpace 𝕀[F] := borel _
local instance globalZetaIdeleClassMeasurableSpace : MeasurableSpace C[F] := borel _

/-- Paper: §3.2.2, p. 124. An idele belongs to the closed norm band if its norm
lies between the two endpoints. -/
def ideleNormBand (F : Type*) [Field F] [NumberField F] (a b : ℝ) : Set 𝕀[F] :=
  {g | ((ideleNorm F g : ℝ≥0) : ℝ) ∈ Icc a b}

/-- Paper: §3.2.2, p. 124. The identity lies in a closed norm band precisely
when the band contains one. -/
theorem one_mem_ideleNormBand (a b : ℝ) :
    (1 : 𝕀[F]) ∈ ideleNormBand F a b ↔ a ≤ 1 ∧ 1 ≤ b := by
  simp [ideleNormBand]

/-- Paper: §3.2.2, p. 124. The surjective idele class norm takes values
other than one, so its abscissa is defined. -/
theorem ideleClassNorm_ne_one : ∃ g : C[F], ideleClassNorm F g ≠ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
  obtain ⟨g, hg⟩ := hsurj t
  refine ⟨g, fun h ↦ ?_⟩
  have ht := congrArg Units.val (hg.symm.trans h)
  norm_num [t] at ht

local notation "rightHalf" =>
  (relativeRightHalfPlane (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) 1 : Set 𝒳[F])

/-- Paper: Equation (3.2.2.1), p. 124. The global zeta integral is the
multiplicative Tamagawa integral of the test function against the quasi-character
pulled back to the ideles. The convergence statements give its domain of use. -/
def globalIdelicZetaIntegral (f : ℬ[F]) (c : 𝒳[F]) : ℂ :=
  ∫ g : 𝕀[F], f (Multiplicative.ofAdd g.val) * c (classOf g) ∂multiplicativeTamagawaMeasure F

/-- Paper: Equation (3.2.2.1), p. 124. At the squared norm character, the
zeta integral weights the test function by the square of the idelic norm. -/
theorem globalIdelicZetaIntegral_normSquared (f : ℬ[F]) :
    globalIdelicZetaIntegral f (ideleClassNormTwist (1 : U[F]) 2) =
      ∫ g : 𝕀[F], f (Multiplicative.ofAdd g.val) * ((ideleNorm F g : ℝ≥0) : ℂ) ^ (2 : ℕ)
        ∂multiplicativeTamagawaMeasure F := by
  unfold globalIdelicZetaIntegral
  congr 1
  funext g
  congr 1
  change (((1 : U[F]) (classOf g) : Circle) : ℂ) * (classNormℝ (classOf g) : ℂ) ^ (2 : ℂ) = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_ofNat]
  rfl

/-- Paper: Theorem 3.2.2.1(1), p. 124. The global zeta integral converges
absolutely for every quasi-character with abscissa greater than one. -/
theorem globalIdelicZetaIntegral_integrable (f : ℬ[F]) (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Integrable (fun g : 𝕀[F] ↦ f (Multiplicative.ofAdd g.val) * c (classOf g))
      (multiplicativeTamagawaMeasure F) := by sorry

/-- Paper: Theorem 3.2.2.1(1) and Remark 3.2.2.2, pp. 124–125.
Norm-band truncations of the zeta integral converge uniformly on compact subsets
of the half-plane as the outer bound tends to infinity. -/
theorem globalIdelicZetaIntegral_tendstoUniformlyOn (f : ℬ[F]) (K : Set 𝒳[F])
    (hK : IsCompact K) (h : K ⊆ rightHalf) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ g in ideleNormBand F (a n)⁻¹ (a n), f (Multiplicative.ofAdd g.val) * c (classOf g)
        ∂multiplicativeTamagawaMeasure F)
      (globalIdelicZetaIntegral f) atTop K := by sorry

-- TODO(paper-gap): In Remark 3.2.2.2 the truncated idele domain is not compact.
-- It contains the closed infinite discrete subgroup of principal ideles.

/-- Paper: Remark 3.2.2.2, p. 125. Each fixed norm-band truncation of the zeta
integral is holomorphic in the complex norm-twist coordinate.
Deviation: The norm bound controls the variation in the exponent on the band. -/
theorem globalIdelicZetaIntegral_normBand_entire (f : ℬ[F]) (χ : U[F])
    (a : ℝ) (ha : 1 ≤ a) :
    Differentiable ℂ (fun s ↦
      ∫ g in ideleNormBand F a⁻¹ a, f (Multiplicative.ofAdd g.val) *
        ideleClassNormTwist χ s (classOf g) ∂multiplicativeTamagawaMeasure F) := by sorry

/-- Paper: Theorem 3.2.2.1(1), p. 124. The zeta integral is holomorphic on the
right half-plane, expressed in the complex norm-twist coordinates of §3.1. -/
theorem globalIdelicZetaIntegral_analyticOn (f : ℬ[F]) (χ : U[F]) :
    AnalyticOnNhd ℂ (fun s ↦ globalIdelicZetaIntegral f (ideleClassNormTwist χ s)) halfPlane := by
  sorry

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The zeta integral admits a
meromorphic continuation, in normal form on every complex norm-twist chart. -/
theorem globalIdelicZetaIntegral_exists_continuation (f : ℬ[F]) :
    ∃ Z : 𝒳[F] → ℂ, (∀ χ : U[F],
      MeromorphicNFOn (fun s ↦ Z (ideleClassNormTwist χ s)) univ) ∧
      EqOn Z (globalIdelicZetaIntegral f) rightHalf := by sorry

/-- Paper: Definition 3.2.2.5, p. 128. The global idelic Z-function is the
meromorphic continuation of the zeta integral.
Deviation: This definition is placed next to its existence theorem so that the
remaining statements can use it. At poles we use Mathlib's meromorphic normal form. -/
def globalIdelicZFunction (f : ℬ[F]) : 𝒳[F] → ℂ :=
  (globalIdelicZetaIntegral_exists_continuation f).choose

/-- Paper: Definition 3.2.2.5, p. 128. On the half-plane of convergence the
global idelic Z-function agrees with its defining integral. -/
theorem globalIdelicZFunction_eq_integral (f : ℬ[F]) :
    EqOn (globalIdelicZFunction f) (globalIdelicZetaIntegral f) rightHalf :=
  (globalIdelicZetaIntegral_exists_continuation f).choose_spec.2

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. In every norm-twist coordinate
the global Z-function is in meromorphic normal form. -/
theorem globalIdelicZFunction_meromorphic (f : ℬ[F]) (χ : U[F]) :
    MeromorphicNFOn (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) univ :=
  (globalIdelicZetaIntegral_exists_continuation f).choose_spec.1 χ

local notation "archimedeanZeta" =>
  fun (f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (c : 𝒳[F]) ↦
    ∫ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd (Units.val g)) *
      c (classOf (sIdeleInsertion F ∅ g)) ∂sMultiplicativeTamagawaMeasure F ∅

/-- Paper: Equations (3.4.3.3)–(3.4.3.6), p. 152. The archimedean test function
given by the product of the local Gaussians has zeta integral equal to the gamma
factor of the unitary character in the half-plane of absolute convergence.
Deviation: The complex monomial is chosen with angular weight opposite to the character. -/
theorem exists_archimedeanHeckeTest (χ : U[F]) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅)), ∀ s : halfPlane,
      archimedeanZeta f (ideleClassNormTwist χ s) = heckeGammaFactor χ s := by
  sorry

/-- Paper: Equations (3.4.3.7)–(3.4.3.9), p. 152. Tensoring an archimedean test
with integer-ring indicators at unramified places and inverse character weights
on integer units at ramified places contributes the finite Hecke Euler product.
Deviation: The finite integer-unit Tamagawa masses give a nonzero scalar independent of `s`. -/
theorem exists_globalHeckeTest (χ : U[F])
    (fArch : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) :
    ∃ (f : ℬ[F]) (a : ℂ), a ≠ 0 ∧ ∀ s : halfPlane,
      globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
        a * (archimedeanZeta fArch (ideleClassNormTwist χ s) * finiteHeckeL χ s) := by
  sorry

/-- Paper: Proposition 3.2.1.3, p. 123. The completed Hecke L-function extends
meromorphically to the complex plane. We use Mathlib's normal form at poles. -/
theorem completedHeckeL_exists_continuation (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = completedHeckeL χ s := by
  obtain ⟨fArch, hArch⟩ := exists_archimedeanHeckeTest χ
  obtain ⟨f, a, ha, hf⟩ := exists_globalHeckeTest χ fArch
  refine ⟨fun s ↦ a⁻¹ * globalIdelicZFunction f (ideleClassNormTwist χ s), ?_, ?_⟩
  · exact (meromorphicNFOn_fun_const_smul_iff_meromorphicNFOn (inv_ne_zero ha)).2
      (globalIdelicZFunction_meromorphic f χ)
  · intro s
    have hσ := quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F)
      (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
      (ideleClassNormTwist χ s) χ s (fun _ ↦ rfl)
    have hs : ideleClassNormTwist χ s ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa (ideleClassNorm F) _ _ _
      rw [hσ]
      exact s.property
    change a⁻¹ * globalIdelicZFunction f (ideleClassNormTwist χ s) = completedHeckeL χ s
    rw [globalIdelicZFunction_eq_integral f hs, hf s, hArch s, ← mul_assoc,
      inv_mul_cancel₀ ha, one_mul]
    rfl

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The global Z-function is analytic
away from the trivial character and the norm, where it has at most simple poles. -/
theorem globalIdelicZFunction_poles (f : ℬ[F]) (χ : U[F]) :
    let Z := fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)
    AnalyticOnNhd ℂ Z {s | ideleClassNormTwist χ s ≠ 1 ∧
      ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : U[F]) 1} ∧
    ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt Z s := by sorry

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The residue at the trivial character
is minus the norm-one class volume times the test function evaluated at zero. -/
theorem globalIdelicZFunction_residue_zero (f : ℬ[F]) :
    Tendsto (fun s : ℂ ↦ s * globalIdelicZFunction f (ideleClassNormTwist (1 : U[F]) s))
      (𝓝[≠] 0)
      (𝓝 (-((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) * f zeroAdele)) := by sorry

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The residue at the norm character
is the norm-one class volume times the Fourier transform evaluated at zero. -/
theorem globalIdelicZFunction_residue_one (f : ℬ[F]) :
    Tendsto (fun s : ℂ ↦ (s - 1) * globalIdelicZFunction f (ideleClassNormTwist (1 : U[F]) s))
      (𝓝[≠] 1)
      (𝓝 (((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) *
        adeleSchwartzFourier f zeroAdele)) := by sorry

/-- Paper: Theorem 3.2.2.1(1)(b), p. 124. Fourier transforming the test function
and taking the norm times the inverse character preserves its global Z-function value. -/
theorem globalIdelicZFunction_functionalEquation (f : ℬ[F]) (c : 𝒳[F]) :
    globalIdelicZFunction f c = globalIdelicZFunction (adeleSchwartzFourier f)
      (dualQuasiCharacter (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous c) := by sorry

local notation "archimedeanFourier" =>
  fun (f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (y : SAdeleRing F ∅) ↦
    @tamagawaFourier _ _ (instMeasurableSpaceSAdeleRing (F := F) (S := ∅))
      (sAdditiveTamagawaMeasure F ∅) (sAdeleStandardCharacter F ∅)
      (fun x ↦ f (Multiplicative.ofAdd x)) y

/-- Paper: Equations (3.4.3.3)–(3.4.3.6), p. 152. Choose archimedean Gaussians
for a unitary character and its inverse whose zeta integrals equal their gamma factors.
The trace-pairing Fourier transform exchanges the two Gaussians up to a nonzero scalar.
Deviation: The complex monomials have angular weight opposite to the character. -/
theorem exists_archimedeanHeckeTest_fourier (χ : U[F]) :
    ∃ (f fdual : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (c : ℂ), c ≠ 0 ∧
      (∀ y, archimedeanFourier f y = c * fdual (Multiplicative.ofAdd y)) ∧
      (∀ s : halfPlane, archimedeanZeta f (ideleClassNormTwist χ s) = heckeGammaFactor χ s) ∧
      (∀ s : halfPlane,
        archimedeanZeta fdual (ideleClassNormTwist χ⁻¹ s) = heckeGammaFactor χ⁻¹ s) := by
  sorry

/-- Paper: Proposition 3.2.1.3(3), p. 123 and Equations (3.4.3.7)–(3.4.3.9),
p. 152. Extend the archimedean test by integer-ring indicators at unramified finite places
and inverse character weights on integer units at ramified places. In the right half-plane,
the finite factors of the two zeta integrals are the Euler products for the character and
its inverse. The Fourier-transformed finite test gives a nonzero scalar and a positive
real scale raised to the exponent, from the different and the character conductor. -/
theorem exists_globalHeckeTest_fourier (χ : U[F])
    (fArch fArchDual : SchwartzBruhat (Multiplicative (SAdeleRing F ∅)))
    (c : ℂ) (hc : c ≠ 0)
    (hFourier : ∀ y, archimedeanFourier fArch y = c * fArchDual (Multiplicative.ofAdd y)) :
    ∃ (f : ℬ[F]) (a b : ℂ) (q : ℝ), a ≠ 0 ∧ b ≠ 0 ∧ 0 < q ∧
      (∀ s : halfPlane, globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
        a * (archimedeanZeta fArch (ideleClassNormTwist χ s) * finiteHeckeL χ s)) ∧
      (∀ s : halfPlane,
        globalIdelicZetaIntegral (adeleSchwartzFourier f) (ideleClassNormTwist χ⁻¹ s) =
          (b * (q : ℂ) ^ (s : ℂ)) *
            (archimedeanZeta fArchDual (ideleClassNormTwist χ⁻¹ s) * finiteHeckeL χ⁻¹ s)) := by
  sorry

/-- An entire nonzero multiple of the completed series determines the corresponding
global idelic Z-function whenever it agrees with the zeta integral on the right half-plane. -/
private theorem globalIdelicZFunction_eq_mul_completedHeckeL_of_integral
    (f : ℬ[F]) (χ : U[F]) (L A : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hA : Differentiable ℂ A) (hA₀ : ∀ s, A s ≠ 0)
    (hIntegral : ∀ s : halfPlane, globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      A s * completedHeckeL χ s) (s : ℂ) :
    globalIdelicZFunction f (ideleClassNormTwist χ s) = A s * L s := by
  let Z (z : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ z)
  have hZ : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hAL : MeromorphicNFOn (A * L) univ := fun z hz ↦
    (meromorphicNFAt_mul_iff_right (hA.analyticAt z) (hA₀ z)).2 (hL hz)
  have hAgree (z : halfPlane) : Z z = (A * L) z := by
    have hz : ideleClassNormTwist χ z ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa (ideleClassNorm F) _ _ _
      rw [quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F)
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
        (ideleClassNormTwist χ z) χ z (fun _ ↦ rfl)]
      exact z.property
    change globalIdelicZFunction f (ideleClassNormTwist χ z) = A z * L z
    rw [globalIdelicZFunction_eq_integral f hz, hIntegral z, h z]
  have hAtTwo : meromorphicOrderAt (Z - A * L) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hNear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hNear.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr (hAgree ⟨z, hz⟩)
  have hOrder := (hZ.meromorphicOn.sub hAL.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
  have hPunctured : Z =ᶠ[𝓝[≠] s] A * L :=
    (meromorphicOrderAt_eq_top_iff.mp hOrder).mono fun _ hz ↦ sub_eq_zero.mp hz
  exact (((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hAL (mem_univ s))).mp hPunctured).eq_of_nhds

/-- Paper: Equation (3.1.1.4), p. 119. Duality in the norm-twist coordinate
takes the inverse unitary character and reflects the exponent. -/
private theorem dualQuasiCharacter_ideleClassNormTwist (χ : U[F]) (s : ℂ) :
    dualQuasiCharacter (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
      (ideleClassNormTwist χ s) = ideleClassNormTwist χ⁻¹ (1 - s) := by
  ext1 g
  let N : ℂ := (classNormℝ g : ℂ)
  have hN : N ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
  change N * ideleClassNormTwist χ s g⁻¹ = ideleClassNormTwist χ⁻¹ (1 - s) g
  rw [map_inv]
  change N * ((χ g : ℂ) * N ^ s)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1 - s)
  rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

/-- Paper: Proposition 3.2.1.3(3), p. 123. Reflecting the continuation of the
inverse unitary character gives the original continuation times a nowhere-vanishing
entire function. Inversion agrees with complex conjugation for a unitary character. -/
theorem completedHeckeL_continuation_functionalEquation (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      ∀ s, Ldual (1 - s) = ε s * L s := by
  obtain ⟨fArch, fArchDual, c, hc, hFourier, hArch, hArchDual⟩ :=
    exists_archimedeanHeckeTest_fourier χ
  obtain ⟨f, a, b, q, ha, hb, hq, hf, hFourierIntegral⟩ :=
    exists_globalHeckeTest_fourier χ fArch fArchDual c hc hFourier
  let B (s : ℂ) := b * (q : ℂ) ^ s
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hB : Differentiable ℂ B :=
    (differentiable_id.const_cpow (Or.inl hq₀)).const_mul b
  have hB₀ (s : ℂ) : B s ≠ 0 :=
    mul_ne_zero hb (fun hz ↦ hq₀ ((Complex.cpow_eq_zero_iff _ _).mp hz).1)
  have hZ := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral f χ L (fun _ ↦ a)
    hL h (differentiable_const a) (fun _ ↦ ha) (fun s ↦ by
      rw [hf s, hArch s]
      rfl)
  have hZdual := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral
    (adeleSchwartzFourier f) χ⁻¹ Ldual B hLdual hdual hB hB₀ (fun s ↦ by
      rw [hFourierIntegral s, hArchDual s]
      rfl)
  have hReflect : Differentiable ℂ (fun s : ℂ ↦ 1 - s) :=
    (differentiable_const (1 : ℂ)).sub differentiable_id
  refine ⟨fun s ↦ (B (1 - s))⁻¹ * a,
    ((hB.comp hReflect).inv (fun s ↦ hB₀ (1 - s))).mul_const a,
    fun s ↦ mul_ne_zero (inv_ne_zero (hB₀ (1 - s))) ha, fun s ↦ ?_⟩
  have hEq := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist χ s)
  rw [dualQuasiCharacter_ideleClassNormTwist, hZ s, hZdual (1 - s)] at hEq
  rw [mul_assoc, hEq, ← mul_assoc, inv_mul_cancel₀ (hB₀ (1 - s)), one_mul]

/-- At the trivial character, reflection in the functional equation transfers the
simple pole at one to a simple pole at zero. -/
private theorem completedHeckeL_one_order_zero (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (h : ∀ s : halfPlane, L s = completedHeckeL (1 : U[F]) s) :
    meromorphicOrderAt L 0 = -1 := by
  obtain ⟨ε, hε, hεne, hfun⟩ := completedHeckeL_continuation_functionalEquation
    (1 : U[F]) L L hL h hL (by simpa using h)
  have hcomp : meromorphicOrderAt (fun s ↦ L (1 - s)) 0 = meromorphicOrderAt L 1 := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) 0 := by fun_prop
    have hd : deriv (fun s : ℂ ↦ 1 - s) 0 ≠ 0 := by simp
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero (f := L) ha hd
  have hεan := hε.analyticAt (z := 0)
  have hεord : meromorphicOrderAt ε 0 = 0 :=
    (hεan.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr (hεne 0)
  rw [show (fun s ↦ L (1 - s)) = ε * L from funext hfun,
    meromorphicOrderAt_mul hεan.meromorphicAt (hL (mem_univ _)).meromorphicAt,
    hεord, zero_add, completedHeckeL_one_order_one L hL h] at hcomp
  exact hcomp

/-- Paper: Proposition 3.2.1.3(2), p. 123. If the character is trivial on norm-one
classes, there is a unique real norm-twist parameter and the two indicated poles
are simple. The continuation is analytic elsewhere.
Deviation: The printed residue formulas have a normalization conflict described below. -/
theorem completedHeckeL_continuation_simplePoles (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) ∧
      meromorphicOrderAt L (Complex.I * (t : ℂ)) = -1 ∧
      meromorphicOrderAt L (1 + Complex.I * (t : ℂ)) = -1 ∧
      AnalyticOnNhd ℂ L ({Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}ᶜ) := by
  obtain ⟨t, ht, huniq⟩ := existsUnique_ideleClassNormTwist χ hχ
  let b : ℂ := Complex.I * (t : ℂ)
  have hbre : b.re = 0 := by simp [b, Complex.mul_re]
  have hχ' : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-b) := by simpa [b] using ht
  let L₀ (s : ℂ) := L (s + b)
  have hL₀ : MeromorphicNFOn L₀ univ :=
    fun _ _ ↦ meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (hL (mem_univ _))
  have h₀ (s : halfPlane) : L₀ s = completedHeckeL (1 : U[F]) s := by
    let w : halfPlane := ⟨(s : ℂ) + b, by
      change 1 < (s : ℂ).re + b.re
      rw [hbre, add_zero]
      exact s.property⟩
    change L w = _
    rw [h w, completedHeckeL_of_normTwist χ (-b) (by simp [hbre]) hχ' w]
    congr 1
    apply Subtype.ext
    change (s : ℂ) + b + -b = s
    simp
  refine ⟨t, ⟨ht, ?_, ?_, ?_⟩, fun u hu ↦ huniq u hu.1⟩
  · have ho := completedHeckeL_one_order_zero L₀ hL₀ h₀
    simpa [L₀, b, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt] using ho
  · have ho := completedHeckeL_one_order_one L₀ hL₀ h₀
    simpa [L₀, b, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt] using ho
  · intro s hs
    have hs₀ : s - b ∈ ({0, 1}ᶜ : Set ℂ) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs ⊢
      exact ⟨fun he ↦ hs.1 (sub_eq_zero.mp he), fun he ↦ hs.2 (sub_eq_iff_eq_add.mp he)⟩
    have ha := completedHeckeL_one_analyticOnNhd L₀ hL₀ h₀ (s - b) hs₀
    have hb := ha.comp (f := fun z : ℂ ↦ z - b) (show AnalyticAt ℂ (fun z : ℂ ↦ z - b) s by fun_prop)
    simpa [L₀, Function.comp_def] using hb

-- TODO(paper-gap): The residues printed in Proposition 3.2.1.3(2) disagree with the
-- Euler product normalization. For the trivial character of ℚ(√5), the residue at 1
-- is already the Appendix A.3.2.1 class volume, since both real gamma factors equal 1.

/-- Paper: Equation (3.2.2.3), p. 124. The theta Mellin integral is the idele-class
Tamagawa integral of the global theta function against the quasi-character. -/
def globalThetaMellinIntegral (f : ℬ[F]) (c : 𝒳[F]) : ℂ :=
  ∫ g : C[F], adelicTheta f g * c g ∂ideleClassTamagawaMeasure F

/-- Paper: Theorem 3.2.2.1(2), p. 124. The theta Mellin integral is absolutely
convergent on the right half-plane. -/
theorem globalThetaMellinIntegral_integrable (f : ℬ[F]) (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Integrable (fun g : C[F] ↦ adelicTheta f g * c g) (ideleClassTamagawaMeasure F) := by sorry

/-- Paper: Theorem 3.2.2.1(2), p. 124. Truncating the theta Mellin integral to
norm bands converges uniformly on every compact subset of the right half-plane. -/
theorem globalThetaMellinIntegral_tendstoUniformlyOn (f : ℬ[F]) (K : Set 𝒳[F])
    (hK : IsCompact K) (h : K ⊆ rightHalf) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ g in {g : C[F] | classNormℝ g ∈ Icc (a n)⁻¹ (a n)}, adelicTheta f g * c g
        ∂ideleClassTamagawaMeasure F)
      (globalThetaMellinIntegral f) atTop K := by sorry

/-- Paper: Equation (3.2.2.11), p. 127. Unfolding theta on the right half-plane
identifies its Mellin integral with the zeta integral on the ideles. -/
theorem globalThetaMellinIntegral_eq_idelic (f : ℬ[F]) :
    EqOn (globalThetaMellinIntegral f) (globalIdelicZetaIntegral f) rightHalf := by sorry

/-- Paper: Theorem 3.2.2.1(2)(a), p. 124. If the test function and its Fourier
transform vanish at zero, the theta Mellin integral converges absolutely everywhere. -/
theorem globalThetaMellinIntegral_integrable_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0) (c : 𝒳[F]) :
    Integrable (fun g : C[F] ↦ adelicTheta f g * c g) (ideleClassTamagawaMeasure F) := by sorry

/-- Paper: Theorem 3.2.2.1(2)(a), p. 124. If both zero terms vanish, norm-band
truncations of the theta Mellin integral converge uniformly on every compact set. -/
theorem globalThetaMellinIntegral_tendstoUniformlyOn_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0)
    (K : Set 𝒳[F]) (hK : IsCompact K) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ g in {g : C[F] | classNormℝ g ∈ Icc (a n)⁻¹ (a n)}, adelicTheta f g * c g
        ∂ideleClassTamagawaMeasure F)
      (globalThetaMellinIntegral f) atTop K := by sorry

/-- Paper: Theorem 3.2.2.1(2)(a), p. 124. With both zero terms vanishing, the
theta Mellin integral is entire in every complex norm-twist coordinate. -/
theorem globalThetaMellinIntegral_entire_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0) (χ : U[F]) :
    Differentiable ℂ (fun s ↦ globalThetaMellinIntegral f (ideleClassNormTwist χ s)) := by sorry

/-- Paper: Theorem 3.2.2.1(2)(a) and (3), pp. 124–125. When both zero terms
vanish, the entire theta Mellin transform agrees everywhere with the global Z-function. -/
theorem globalThetaMellinIntegral_eq_continuation_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0) :
    globalThetaMellinIntegral f = globalIdelicZFunction f := by sorry

-- TODO(paper-gap): The absolute convergence asserted in Theorem 3.2.2.1(2)(b)
-- fails for nontrivial norm-one characters. The modulus of the quasi-character is
-- the same on every component at fixed abscissa, and the small-norm polar term persists.

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. The continuation of the theta Mellin
integral is the global Z-function and is entire on every nontrivial norm-one component.
Deviation: Entireness concerns the continuation of the integral from its region of convergence. -/
theorem globalIdelicZFunction_entire_of_nontrivial (f : ℬ[F]) (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Differentiable ℂ (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) := by sorry

set_option maxHeartbeats 1000000 in
/-- Paper: §3.4.3.1, p. 152. On the half-plane of absolute convergence, the idelic
zeta integral of a normalized adelic Gaussian gives the completed Euler product.
Deviation: The finite Tamagawa unit masses are absorbed by scaling the test function.
The complex Gaussian uses the opposite angular weight to the character. -/
theorem exists_globalIdelicZetaIntegral_eq_completedHeckeL (χ : U[F]) :
    ∃ f : ℬ[F], ∀ s : halfPlane,
      globalIdelicZetaIntegral f (ideleClassNormTwist χ s) = completedHeckeL χ s := by
  obtain ⟨fArch, hArch⟩ := exists_archimedeanHeckeTest χ
  obtain ⟨f, a, ha, hf⟩ := exists_globalHeckeTest χ fArch
  refine ⟨a⁻¹ • f, fun s ↦ ?_⟩
  have hscale : globalIdelicZetaIntegral (a⁻¹ • f) (ideleClassNormTwist χ s) =
      a⁻¹ * globalIdelicZetaIntegral f (ideleClassNormTwist χ s) := by
    let integrand (g : 𝕀[F]) := f (Multiplicative.ofAdd g.val) * (ideleClassNormTwist χ s) (classOf g)
    calc
      _ = ∫ g, a⁻¹ * integrand g ∂multiplicativeTamagawaMeasure F := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
        change (a⁻¹ * f (Multiplicative.ofAdd g.val)) * (ideleClassNormTwist χ s) (classOf g) =
          a⁻¹ * (f (Multiplicative.ofAdd g.val) * (ideleClassNormTwist χ s) (classOf g))
        exact mul_assoc _ _ _
      _ = _ := integral_const_mul (μ := multiplicativeTamagawaMeasure F) a⁻¹ integrand
  rw [hscale, hf s, hArch s, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rfl

/-- Paper: Proposition 3.2.1.3(1), p. 123. When the restriction to norm-one
classes is nontrivial, the continuation is entire. -/
theorem completedHeckeL_continuation_entire (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Differentiable ℂ L := by
  obtain ⟨f, hf⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ
  let Z (s : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ s)
  have hZ : Differentiable ℂ Z := globalIdelicZFunction_entire_of_nontrivial f χ hχ
  have hZNF : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hEq : EqOn L Z halfPlane := by
    intro s hs
    have habs : quasiCharacterAbscissa (ideleClassNorm F)
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
        (ideleClassNormTwist χ s) = s.re :=
      quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F) _ _ _ χ s (fun _ ↦ rfl)
    have hmem : ideleClassNormTwist χ s ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa _ _ _ _
      rwa [habs]
    exact (h ⟨s, hs⟩).trans
      ((globalIdelicZFunction_eq_integral f hmem).trans (hf ⟨s, hs⟩)).symm
  have h₂ : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ halfPlane :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
  have hnear : L =ᶠ[𝓝[≠] (2 : ℂ)] Z :=
    (h₂.mono hEq).filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (L - Z) (2 : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp hnear)
  have hsub := hL.meromorphicOn.sub hZNF.meromorphicOn
  -- The difference vanishes as a meromorphic germ everywhere by connectedness.
  have hident : L = Z := by
    funext s
    have horder := hsub.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2 : ℂ)) (mem_univ s) htop
    have hlocal : L =ᶠ[𝓝[≠] s] Z :=
      eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp horder)
    exact (((hL (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hZNF (mem_univ s))).mp hlocal).eq_of_nhds
  rwa [hident]

section HomogeneousMellin

local notation "χ₁[" F "]" => PontryaginDual (MonoidHom.ker (ideleClassNorm F))
local notation "componentStrip" =>
  componentVerticalStrip (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F))
local notation "mellinIntegrand" =>
  fun (τ : ℝ≥0ˣ →ₜ* 𝕀[F]) (ω : χ₁[F]) (f : ℬ[F]) (c : 𝒳[F]) (t : ℝ≥0ˣ) ↦
    homogeneousAdelicTheta ω f (classOf (τ t)) * c (classOf (τ t))

/-- Paper: Equation (3.2.2.4), p. 125. The homogeneous theta Mellin integral
uses a continuous homomorphic section of the idelic norm and the measure `dt/t`. -/
def homogeneousThetaMellinIntegral (τ : ℝ≥0ˣ →ₜ* 𝕀[F]) (ω : χ₁[F])
    (f : ℬ[F]) (c : 𝒳[F]) : ℂ :=
  ∫ t, mellinIntegrand τ ω f c t ∂positiveRealHaar

variable (τ : ℝ≥0ˣ →ₜ* 𝕀[F])
variable (ω : χ₁[F]) (f : ℬ[F])

/-- Paper: Equation (3.2.2.4), p. 125. For the squared norm character, the
Mellin weight on the section is the square of the positive real parameter. -/
theorem homogeneousThetaMellinIntegral_normSquared (hτ : RightInverse τ (ideleNorm F)) :
    homogeneousThetaMellinIntegral τ (1 : χ₁[F]) f (ideleClassNormTwist (1 : U[F]) 2) =
      ∫ t : ℝ≥0ˣ, homogeneousAdelicTheta (1 : χ₁[F]) f (classOf (τ t)) *
        (t.val : ℂ) ^ (2 : ℕ) ∂positiveRealHaar := by
  unfold homogeneousThetaMellinIntegral
  congr 1
  funext t
  beta_reduce
  congr 1
  change (((1 : U[F]) (classOf (τ t)) : Circle) : ℂ) *
    (classNormℝ (classOf (τ t)) : ℂ) ^ (2 : ℂ) = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_ofNat]
  change (((ideleNorm F (τ t) : ℝ≥0) : ℝ) : ℂ) ^ 2 = _
  rw [hτ t]

/-- Paper: Theorem 3.2.2.1(3), p. 125. The homogeneous theta Mellin integral
converges absolutely on the right half-plane of the component indexed by ω. -/
theorem homogeneousThetaMellinIntegral_integrable (hτ : RightInverse τ (ideleNorm F)) (c : 𝒳[F])
    (hc : c ∈ componentStrip ω (Ioi 1)) :
    Integrable (mellinIntegrand τ ω f c) positiveRealHaar := by sorry

/-- Paper: Theorem 3.2.2.1(3), p. 125. Norm-band truncations of the homogeneous
theta Mellin integral converge uniformly on compact subsets of that right half-plane. -/
theorem homogeneousThetaMellinIntegral_tendstoUniformlyOn
    (hτ : RightInverse τ (ideleNorm F))
    (K : Set 𝒳[F]) (hK : IsCompact K) (h : K ⊆ componentStrip ω (Ioi 1))
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ t in {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc (a n)⁻¹ (a n)},
        mellinIntegrand τ ω f c t ∂positiveRealHaar)
      (homogeneousThetaMellinIntegral τ ω f) atTop K := by sorry

/-- Paper: Theorem 3.2.2.1(3)(a) and (b), p. 125. The homogeneous theta Mellin
integral converges absolutely throughout the component when both zero terms
vanish or when the norm-one character is nontrivial. -/
theorem homogeneousThetaMellinIntegral_integrable_on_component
    (hτ : RightInverse τ (ideleNorm F))
    (h : f ∈ adelePolarSubspace F ∨ ω ≠ 1) (c : 𝒳[F]) (hc : c ∈ componentStrip ω univ) :
    Integrable (mellinIntegrand τ ω f c) positiveRealHaar := by sorry

/-- Paper: Theorem 3.2.2.1(3)(a) and (b), p. 125. When both zero terms vanish
or the norm-one character is nontrivial, norm-band truncations converge
uniformly on every compact subset of the component. -/
theorem homogeneousThetaMellinIntegral_tendstoUniformlyOn_component
    (hτ : RightInverse τ (ideleNorm F))
    (h : f ∈ adelePolarSubspace F ∨ ω ≠ 1)
    (K : Set 𝒳[F]) (hK : IsCompact K) (hcomponent : K ⊆ componentStrip ω univ)
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ t in {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc (a n)⁻¹ (a n)},
        mellinIntegrand τ ω f c t ∂positiveRealHaar)
      (homogeneousThetaMellinIntegral τ ω f) atTop K := by sorry

/-- Paper: Theorem 3.2.2.1(3)(a) and (b), p. 125. In either case of
convergence throughout the component, the integral is entire in its
complex norm-twist coordinate. -/
theorem homogeneousThetaMellinIntegral_entire_on_component
    (hτ : RightInverse τ (ideleNorm F))
    (h : f ∈ adelePolarSubspace F ∨ ω ≠ 1) (χ : U[F])
    (hχ : ∀ g : (ideleClassNorm F).ker, χ g.val = ω g) :
    Differentiable ℂ (fun s ↦
      homogeneousThetaMellinIntegral τ ω f (ideleClassNormTwist χ s)) := by sorry

-- The fiber integral in the proof on p. 127 needs the character weight ω(h).
-- Definition 2.2.5.1 includes this weight in homogeneousAdelicTheta.

/-- Paper: Equation (3.2.2.5), p. 125. On the right half-plane of a component,
Weil integration identifies the theta Mellin integral with the homogeneous integral. -/
theorem globalThetaMellinIntegral_eq_homogeneous (hτ : RightInverse τ (ideleNorm F)) :
    EqOn (globalThetaMellinIntegral f) (homogeneousThetaMellinIntegral τ ω f)
      (componentStrip ω (Ioi 1)) := by sorry

/-- Paper: Equation (3.2.2.5), p. 125. The global Z-function in the component's
norm-twist coordinate is the unique meromorphic continuation of the homogeneous
theta Mellin integral. The theta Mellin integral has the same continuation by
its equality with the homogeneous integral on the right half-plane.
Deviation: Meromorphic continuation is expressed in Mathlib's normal form. -/
theorem homogeneousThetaMellinIntegral_meromorphicContinuation
    (hτ : RightInverse τ (ideleNorm F)) (χ : U[F])
    (hχ : ∀ g : (ideleClassNorm F).ker, χ g.val = ω g) (M : ℂ → ℂ) :
    (MeromorphicNFOn M univ ∧ EqOn M (fun s ↦
      homogeneousThetaMellinIntegral τ ω f (ideleClassNormTwist χ s)) halfPlane) ↔
    M = fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s) := by sorry

/-- Paper: Theorem 3.2.2.1(3), p. 125. If both zero terms vanish, the global
Z-function is entire in the norm-twist coordinate of every component. -/
theorem globalIdelicZFunction_entire_of_vanishing
    (h : f ∈ adelePolarSubspace F) (χ : U[F]) :
    Differentiable ℂ (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) := by sorry

end HomogeneousMellin

/-- Paper: Lemma 3.2.2.3, p. 125. For fixed quasi-character of abscissa
greater than one, the zeta integral is continuous in the Schwartz–Bruhat topology. -/
theorem continuous_globalIdelicZetaIntegral (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Continuous (fun f : ℬ[F] ↦ globalIdelicZetaIntegral f c) := by sorry

-- TODO(paper-gap): In Example 3.2.2.4 the displayed Euler multiplier has the
-- exponent reversed. The Fourier transform of 1_{ℤ₂ˣ} gives the factor 1 - 2^(s-1),
-- which cancels the pole at s = 1 but leaves the pole at s = 0.

end Zeta

end RiemannMasullo
