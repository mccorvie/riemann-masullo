module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec5b

/-!
# Partial Euler products and local zeta residues

Masullo, §3.3 from (3.3.1.25) through §3.3.2, pp. 134–141.
The exponent variables use the normalized local absolute values.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "test(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "m∞(" w ")" => ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
  (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "m𝔭(" v ")" => (Units.map nnNormHom.toMonoidHom :
  (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "h∞(" w ")" => continuous_infiniteLocalModule w
local notation "h𝔭(" v ")" => continuous_finiteLocalModule v
local notation "chartₛ(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ ((circleToComplex).comp χ)
local notation "emptyChart" => quasiCharacterNormTwist (G := SIdeleQuotient F ∅)
  (sIdeleQuotientNorm F ∅) (isProperMap_sIdeleQuotientNorm F ∅).continuous 1
local notation "chart∞[" w "," χ "]" =>
  quasiCharacterNormTwist m∞(w) h∞(w) ((circleToComplex).comp χ)
local notation "chart𝔭[" v "," χ "]" =>
  quasiCharacterNormTwist m𝔭(v) h𝔭(v) ((circleToComplex).comp χ)
local notation "rightHalf" => (Complex.re ⁻¹' Ioi (0 : ℝ))
local notation "vert(" σ "," t ")" => ((σ : ℂ) + (t : ℂ) * Complex.I)
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))
local notation "diffExp(" v ")" => multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "μ∞(" w ")" => infiniteLocalMultiplicativeTamagawaMeasure F w
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ψ∞(" w ")" => (fun x ↦ adeleStandardCharacter F
  (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "F∞(" w ")" => tamagawaFourier (infiniteLocalAdditiveTamagawaMeasure F w) ψ∞(w)
local notation "F𝔭(" v ")" => tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v)
  (finiteLocalStandardCharacter F v)

local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : Primes) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

local notation "realModel(" hw ")" => InfinitePlace.Completion.ringEquivRealOfIsReal hw
local notation "complexModel(" hw ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
local notation "realShape[" hw "," c "," z "," a "]" => (∀ x : ℝˣ,
  c (Units.map (realModel(hw)).symm.toMonoidHom x) =
    (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (a : Fin 2).val)
local notation "complexShape[" hw "," c "," z "," r "]" => (∀ x : ℂˣ,
  c (Units.map (complexModel(hw)).symm.toMonoidHom x) =
    ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z : ℂ) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (r : ℤ))
local notation "unramified[" v "," c "]" => (∀ u : (HeightOneSpectrum.adicCompletionIntegers F v)ˣ,
  c (Units.map (HeightOneSpectrum.adicCompletionIntegers F v).subtype.toMonoidHom u) = 1)

/-- Paper: Equation (3.3.1.25), p. 134. A real local quasi-character has a
unique complex radial exponent and sign parity for its Euler factor. -/
theorem realLocalEulerParameters (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) :
    ∃! p : ℂ × Fin 2, realShape[hw, c, p.1, p.2] := by sorry

/-- Paper: Equation (3.3.1.25), p. 134. A complex local quasi-character has a
unique exponent for the squared absolute value and a unique angular weight. -/
theorem complexLocalEulerParameters (w : InfinitePlace F) (hw : w.IsComplex)
    (c : QuasiCharacter w.Completionˣ) :
    ∃! p : ℂ × ℤ, complexShape[hw, c, p.1, p.2] := by sorry

/-- Paper: Equation (3.3.1.25), p. 134. The infinite local Euler factor is the
real or complex gamma factor shifted by the sign parity or angular weight.
Deviation: As in §3.2.1, the complex factor uses half of Mathlib's Gammaℂ. -/
def infiniteLocalEulerFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) : ℂ :=
  open Classical in
  if hw : w.IsReal then
    let p := (realLocalEulerParameters w hw c).exists.choose
    Complex.Gammaℝ (p.1 + (p.2.val : ℂ))
  else
    let p := (complexLocalEulerParameters w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose
    Complex.Gammaℂ (p.1 + (p.2.natAbs : ℂ) / 2) / 2

/-- Paper: Equation (3.3.1.25), p. 134. The Euler factor of a bare norm power
at a real place is the unshifted real gamma factor. -/
theorem infiniteLocalEulerFactor_real_norm (w : InfinitePlace F) (_hw : w.IsReal) (s : ℂ) :
    infiniteLocalEulerFactor w (chart∞[w, (1 : PontryaginDual w.Completionˣ)] s) =
      Complex.Gammaℝ s := by sorry

/-- Paper: Equation (3.3.1.25), p. 134. The finite local Euler factor of an
unramified character is the reciprocal of one minus its value at a uniformizer.
A ramified character contributes one. -/
def finiteLocalEulerFactor (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  open Classical in
  if unramified[v, c] then
    let h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    (1 - c (Units.mk0 h.choose h.choose_spec.ne_zero))⁻¹
  else 1

/-- Paper: Equation (3.3.1.25), p. 134. A bare norm power over a finite local
field gives the geometric Euler factor in the right half-plane. -/
theorem finiteLocalEulerFactor_norm (v : Primes) {s : ℂ} (hs : s ∈ rightHalf) :
    finiteLocalEulerFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      (1 - (q(v) : ℂ) ^ (-s))⁻¹ := by sorry

/-- Paper: Equation (3.3.1.25), p. 134. The S-local Hecke L-function is the
product of the Euler factors of the restricted quasi-characters. -/
def sLocalHeckeL (c : QuasiCharacter Jₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalEulerFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.25), p. 134. For a bare norm power and no finite
places, the partial Euler product consists of the unshifted gamma factors. -/
theorem sLocalHeckeL_archimedean (s : ℂ) :
    sLocalHeckeL (emptyChart s) =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F := by sorry

-- TODO(paper-gap): The description after (3.3.1.25) calls local insertion
-- injective. For ℚ with only its real place, insertion kills the diagonal unit −1.

/-- Paper: Remark 3.3.1.6, p. 135. The chosen unitary base lifts to a unitary
idele class character, and the finite set of places can be enlarged to kill
the Picard group.
Deviation: Agreement is expressed through the restriction in §3.1.2. The lift
is unramified outside S because its prescribed value on the outside unit
factors is trivial. -/
theorem sLocal_character_extension (χ : PontryaginDual Jₛ) :
    ∃ (χ' : PontryaginDual C𝔽) (h : ideleClassNormTwist χ' 0 ∈ unramifiedOutside F S),
      sIdeleRestriction F S ⟨ideleClassNormTwist χ' 0, h⟩ = chartₛ(χ) 0 ∧
      ∃ T : Finset Primes, S ⊆ T ∧ Subsingleton (CommRing.Pic ((T : Set Primes).integer F)) :=
  by sorry

/-- Paper: Remark 3.3.1.6, p. 135. Along the component of any such lift,
the S-local product matches the selected Euler factors of the global L-function. -/
theorem sLocalHeckeL_eq_partialEulerProduct (χ : PontryaginDual Jₛ) (χ' : PontryaginDual C𝔽)
    (h : ideleClassNormTwist χ' 0 ∈ unramifiedOutside F S)
    (hχ : sIdeleRestriction F S ⟨ideleClassNormTwist χ' 0, h⟩ = chartₛ(χ) 0) (s : ℂ) :
    sLocalHeckeL (chartₛ(χ) s) =
      heckeGammaFactor χ' s * ∏ v : S, finiteHeckeEulerFactor χ' v.val s := by sorry

/-- Paper: Lemma 3.3.1.7(1), p. 135. On every bounded strip in the positive
half-plane the zeta function is uniformly Schwartz in height. -/
theorem sLocalIdelicZFunction_schwartzOnStrip (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ k : ℕ, UniformlySchwartzOnStrip
      (iteratedDeriv k (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s))) a b := by sorry

/-- Paper: Equation (3.3.1.26), p. 135. The normalized S-local zeta function
is the meromorphic quotient by the local Euler product.
Deviation: The quotient is put in normal form before evaluation, so that a
removable singularity takes its limiting value. -/
def sLocalNormalizedZFunction (f : ℬ(SAdeleRing F S)) (c : QuasiCharacter Jₛ) : ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦
    let c' := quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ c s
    sLocalIdelicZFunction f c' / sLocalHeckeL c') univ 0

/-- Paper: Equation (3.3.1.26), p. 135. In the positive half-plane the
normalized function is the convergent zeta integral divided by the Euler product. -/
theorem sLocalNormalizedZFunction_eq_div (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    {s : ℂ} (hs : s ∈ rightHalf) :
    sLocalNormalizedZFunction f (chartₛ(χ) s) =
      sLocalIdelicZetaIntegral f (chartₛ(χ) s) / sLocalHeckeL (chartₛ(χ) s) := by sorry

/-- Paper: Lemma 3.3.1.7(2), p. 135. Dividing by the Euler product removes
all poles of the S-local zeta function. -/
theorem sLocalNormalizedZFunction_entire (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalNormalizedZFunction f (chartₛ(χ) s)) univ := by sorry

/-- Paper: Equation (3.3.1.27), p. 135. The normalized zeta function has the
given Stirling growth bound uniformly on each closed positive strip.
Deviation: The real exponential uses absolute height in both directions. -/
theorem sLocalNormalizedZFunction_heightBound (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (N : ℕ) (hN : 1 ≤ N) :
    let d : ℝ := (InfinitePlace.nrRealPlaces F : ℝ) / 2 + InfinitePlace.nrComplexPlaces F
    ∃ C > (0 : ℝ), ∀ᶠ t : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖sLocalNormalizedZFunction f (chartₛ(χ) (vert(σ, t)))‖ ≤
        C * |t| ^ (-((N : ℝ) + (σ - 1 / 2) * d)) * Real.exp (Real.pi * |t| / 2 * d) :=
  by sorry

-- TODO(paper-gap): The proof's (3.3.1.34) inserts an extra ε_S in the
-- decomposition of Z_S/L_S. The estimate above uses the quotient in (3.3.1.26).
-- Footnote 2 asks for a reference for the uniform rapid decay of the finite-place quotient.

/-- Paper: Lemma 3.3.1.7(3)(a)(i)–(ii), p. 135. The infinite epsilon factor
depends on the real sign parity or the absolute complex angular weight.
Deviation: The phase is i to that power for the conjugate Fourier kernel
of App. A and D and the direction of Tate's equation used in §3.3.1. -/
def infiniteLocalEpsilonFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) : ℂ :=
  open Classical in
  if hw : w.IsReal then
    Complex.I ^ (realLocalEulerParameters w hw c).exists.choose.2.val
  else
    Complex.I ^ (complexLocalEulerParameters w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose.2.natAbs

/-- Paper: Lemma 3.3.1.7(3)(a)(i), p. 135. The odd real component contributes
the constant epsilon factor i with the existing Fourier transform.
Deviation: The printed phase is conjugated. -/
theorem infiniteLocalEpsilonFactor_real_odd (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) (s : ℂ) (hc : realShape[hw, c, s, 1]) :
    infiniteLocalEpsilonFactor w c = Complex.I := by sorry

/-- Paper: Lemma 3.3.1.7(3)(a)(iii), pp. 135–136. The finite epsilon factor
is the local Tate factor with the two local Euler factors removed.
Deviation: Normal form retains removable values. The Tate factor uses the
standard local character, with the finite-place sign fixed in App. A. -/
def finiteLocalEpsilonFactor (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦
    let c' := quasiCharacterNormTwist m𝔭(v) h𝔭(v) c s
    finiteLocalTateFactor v c' / finiteLocalEulerFactor v c' *
      finiteLocalEulerFactor v (dualQuasiCharacter m𝔭(v) h𝔭(v) c')) univ 0

/-- Paper: Equation (3.3.1.29), p. 135. On a bare norm power the finite
epsilon factor is the different norm to the exponent s minus one half. -/
theorem finiteLocalEpsilonFactor_norm (v : Primes) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      ((q(v) : ℂ) ^ diffExp(v)) ^ (s - 1 / 2) := by sorry

/-- Paper: Equation (3.3.1.30), p. 136. For a ramified unitary base trivial
on the chosen uniformizer, the epsilon factor is the normalized Gauss sum
over unit representatives modulo the conductor times the indicated norm power.
Deviation: The norm power uses the product of the different and conductor.
The sum uses the existing finite standard character, including the sign in F13. -/
theorem finiteLocalEpsilonFactor_ramified (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) (π : (v.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π : v.adicCompletion F)) (hχπ : χ π = 1)
    (n : ℕ) (hn : 0 < n)
    (hcond : IsLeast {j : ℕ | ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
      ‖u.val - 1‖ ≤ (q(v) : ℝ) ^ (-(j : ℤ)) → χ u = 1} n)
    (U : Finset ((v.adicCompletion F)ˣ)) (hU : ∀ u ∈ U, ‖u.val‖ = 1)
    (hreps : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
      ∃! a : U, ‖a.val.val - u.val‖ ≤ (q(v) : ℝ) ^ (-(n : ℤ))) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v, χ] s) =
      ((q(v) : ℂ) ^ (diffExp(v) + n)) ^ (s - 1 / 2) *
        ((q(v) : ℂ) ^ n) ^ (-(1 / 2 : ℂ)) *
        ∑ u ∈ U, (χ u : ℂ) *
          (finiteLocalStandardCharacter F v (u.val / π.val ^ (diffExp(v) + n)) : ℂ) :=
  by sorry

/-- Paper: Lemma 3.3.1.7(3)(a), p. 135. The infinite local epsilon factor
is entire in each norm-twist chart. -/
theorem infiniteLocalEpsilonFactor_entire (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    AnalyticOnNhd ℂ (infiniteLocalEpsilonFactor w ∘ chart∞[w, χ]) univ := by sorry

/-- Paper: Lemma 3.3.1.7(3)(a), p. 135. The finite local epsilon factor
is entire in each norm-twist chart. -/
theorem finiteLocalEpsilonFactor_entire (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    AnalyticOnNhd ℂ (finiteLocalEpsilonFactor v ∘ chart𝔭[v, χ]) univ := by sorry

/-- Paper: Equation (3.3.1.28), p. 135. The S-local epsilon factor is the
product of the epsilon factors of the restricted quasi-characters. -/
def sLocalEpsilonFactor (c : QuasiCharacter Jₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.28), p. 135. With only archimedean places, the
trivial component has epsilon factor one. -/
theorem sLocalEpsilonFactor_archimedean_trivial (s : ℂ) :
    sLocalEpsilonFactor (emptyChart s) = 1 := by sorry

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor is entire. -/
theorem sLocalEpsilonFactor_entire (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalEpsilonFactor (chartₛ(χ) s)) univ := by sorry

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor is nowhere zero. -/
theorem sLocalEpsilonFactor_ne_zero (c : QuasiCharacter Jₛ) :
    sLocalEpsilonFactor c ≠ 0 := by sorry

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor has
modulus one on the critical line. -/
theorem sLocalEpsilonFactor_norm_criticalLine (χ : PontryaginDual Jₛ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖sLocalEpsilonFactor (chartₛ(χ) s)‖ = 1 := by sorry

/-- Paper: Equations (3.3.1.31) and (3.3.1.33), pp. 136–137. The entire
normalized zeta functions satisfy the S-local Fourier functional equation.
Deviation: The numerator on the right is the Z-function in (3.3.1.33). -/
theorem sLocalNormalizedZFunction_functionalEquation (f : ℬ(SAdeleRing F S))
    (c : QuasiCharacter Jₛ) :
    sLocalNormalizedZFunction f c =
      sLocalEpsilonFactor c * sLocalNormalizedZFunction (sAdeleSchwartzFourier f)
        (dualQuasiCharacter (G := Jₛ) mₛ hmₛ c) := by sorry

/-- Paper: Equation (3.3.1.32), p. 136. As meromorphic functions, the
correcting factor is epsilon times the Euler factor divided by its dual.
Deviation: The equality is expressed off a discrete set of exponents. -/
theorem sLocalRhoFactor_eq_epsilon_mul (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalRhoFactor c = sLocalEpsilonFactor c *
        (sLocalHeckeL c / sLocalHeckeL (dualQuasiCharacter (G := Jₛ) mₛ hmₛ c)) := by sorry

/-- Paper: Remark 3.3.1.8, p. 136. At each infinite place the additive
Tamagawa measure is self-dual for the restricted standard character. The finite
case is already stated as finiteLocalAdditiveTamagawaMeasure_selfDual. -/
theorem infiniteLocalAdditiveTamagawaMeasure_selfDual (w : InfinitePlace F) :
    IsTamagawaSelfDual (infiniteLocalAdditiveTamagawaMeasure F w) ψ∞(w) := by sorry


/-! ## Local zeta functions and their poles -/

/-- Paper: Equation (3.3.2.1), p. 137. The archimedean zeta integral is
absolutely convergent on the positive half-plane. -/
theorem infiniteLocalIdelicZetaIntegral_integrable (w : InfinitePlace F) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    Integrable (fun g : w.Completionˣ ↦ test(f) g.val * chart∞[w, χ] s g) μ∞(w) := by sorry

/-- Paper: Equation (3.3.2.1), p. 137. The finite local zeta integral is
absolutely convergent on the positive half-plane. -/
theorem finiteLocalIdelicZetaIntegral_integrable (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ test(f) g.val * chart𝔭[v, χ] s g) μ𝔭(v) :=
  by sorry

local notation "normBand[" m "," n "]" =>
  {g | (((m g : ℝ≥0) : ℝ)) ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}

/-- Paper: Equation (3.3.2.1), p. 137. Norm-band truncations of the
archimedean zeta integral converge uniformly on compact positive exponent sets.
Deviation: Uniformity is stated on compact subsets of the convergence domain. -/
theorem infiniteLocalIdelicZetaIntegral_tendstoUniformlyOn (w : InfinitePlace F)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (K : Set ℂ)
    (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) ↦
      ∫ g in normBand[m∞(w), n], test(f) g.val * chart∞[w, χ] s g ∂μ∞(w))
      (fun s ↦ localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s)) atTop K := by sorry

/-- Paper: Equation (3.3.2.1), p. 137. Norm-band truncations of the
finite local zeta integral converge uniformly on compact positive exponent sets.
Deviation: Uniformity is stated on compact subsets of the convergence domain. -/
theorem finiteLocalIdelicZetaIntegral_tendstoUniformlyOn (v : Primes)
    (f : ℬ(v.adicCompletion F)) (χ : PontryaginDual (v.adicCompletion F)ˣ) (K : Set ℂ)
    (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) ↦
      ∫ g in normBand[m𝔭(v), n], test(f) g.val * chart𝔭[v, χ] s g ∂μ𝔭(v))
      (fun s ↦ localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s)) atTop K := by sorry

/-- Paper: §3.3.2, p. 137. The archimedean integral (3.3.2.1) has a unique
meromorphic continuation, in normal form in every norm-twist chart. -/
theorem infiniteLocalIdelicZFunction_existsUnique (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    ∃! Z : QuasiCharacter w.Completionˣ → ℂ, ∀ χ : PontryaginDual w.Completionˣ,
      MeromorphicNFOn (Z ∘ chart∞[w, χ]) univ ∧
        EqOn (Z ∘ chart∞[w, χ]) (fun s ↦ localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s))
          rightHalf := by sorry

/-- Paper: §3.3.2, p. 137. The archimedean Z-function is the meromorphic
continuation of the local integral. -/
def infiniteLocalIdelicZFunction (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    QuasiCharacter w.Completionˣ → ℂ :=
  (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose

/-- Paper: Equation (3.3.2.1), p. 137. In the half-plane of convergence the
archimedean Z-function gives the integral using the multiplicative Tamagawa measure. -/
theorem infiniteLocalIdelicZFunction_eq_integral (w : InfinitePlace F) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    infiniteLocalIdelicZFunction w f (chart∞[w, χ] s) =
      localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s) := by sorry

/-- Paper: §3.3.2, p. 137. The finite local integral (3.3.2.1) has a unique
meromorphic continuation, in normal form in every norm-twist chart. -/
theorem finiteLocalIdelicZFunction_existsUnique (v : Primes) (f : ℬ(v.adicCompletion F)) :
    ∃! Z : QuasiCharacter (v.adicCompletion F)ˣ → ℂ, ∀ χ : PontryaginDual (v.adicCompletion F)ˣ,
      MeromorphicNFOn (Z ∘ chart𝔭[v, χ]) univ ∧
        EqOn (Z ∘ chart𝔭[v, χ]) (fun s ↦ localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s))
          rightHalf := by sorry

/-- Paper: §3.3.2, p. 137. The finite local Z-function is the meromorphic
continuation of the local integral. -/
def finiteLocalIdelicZFunction (v : Primes) (f : ℬ(v.adicCompletion F)) :
    QuasiCharacter (v.adicCompletion F)ˣ → ℂ :=
  (finiteLocalIdelicZFunction_existsUnique v f).exists.choose

/-- Paper: Equation (3.3.2.1), p. 137. In the half-plane of convergence the
finite local Z-function gives the integral using the multiplicative Tamagawa measure. -/
theorem finiteLocalIdelicZFunction_eq_integral (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) =
      localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s) := by sorry

/-- Paper: §3.3.2, p. 137. In each archimedean chart the local zeta function
is meromorphic with values in the strong dual of the test space.
Deviation: Agreement with scalar normal form is required off the
distributional poles, where evaluation on a test function is regular. -/
theorem infiniteLocalIdelicZFunction_distribution (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let poles := {s : ℂ | ∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s < 0}
    ∃ Z : ℂ → StrongDual ℂ (ℬ(w.Completion)), IsVectorMeromorphicOn Z univ poles ∧
      ∀ s ∉ poles, ∀ f, Z s f = infiniteLocalIdelicZFunction w f (chart∞[w, χ] s) := by sorry

/-- Paper: §3.3.2, p. 137. In each finite-place chart the local zeta function
is meromorphic with values in the strong dual of the test space.
Deviation: Agreement with scalar normal form is required off the
distributional poles. -/
theorem finiteLocalIdelicZFunction_distribution (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let poles := {s : ℂ | chart𝔭[v, χ] s = 1}
    ∃ Z : ℂ → StrongDual ℂ (ℬ(v.adicCompletion F)), IsVectorMeromorphicOn Z univ poles ∧
      ∀ s ∉ poles, ∀ f, Z s f = finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) := by sorry

/-- Paper: Lemma 3.3.2.1(1)(1), p. 138. In the pure sign-parity chart, each
scalar zeta function has at most simple poles. The exponents at which some
test function gives a pole are the nonpositive integers of that parity.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem infiniteLocalIdelicZFunction_real_poles (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (s : ℂ) :
    (∀ f : ℬ(w.Completion),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s) ∧
    ((∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s = -1) ↔
      ∃ k : ℕ, s = -((2 * k + a.val : ℕ) : ℂ)) := by sorry

/-- Paper: Lemma 3.3.2.1(1)(2), p. 138. In the pure angular-weight chart,
each scalar zeta function has at most simple poles. The exponents at which
some test function gives a pole are minus half the absolute weight minus a natural number.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem infiniteLocalIdelicZFunction_complex_poles (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r]) (s : ℂ) :
    (∀ f : ℬ(w.Completion),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s) ∧
    ((∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s = -1) ↔
      ∃ m : ℕ, s = -(r.natAbs : ℂ) / 2 - m) := by sorry

-- TODO(paper-gap): The right side of (3.3.2.13) has the opposite sign from
-- its gamma quotient. The residue of that quotient in (3.3.2.16) needs +i.
-- In (3.3.2.14) and (3.3.2.17) the conjugate Fourier kernel gives +i to
-- the absolute angular weight. In (3.3.2.21) the proof needs m ≥ 0.
-- The residue formulas below use ordinary Taylor coefficients.

/-- Paper: Lemma 3.3.2.1(2)(1), p. 138. At a real pole, the residue applied
to a test function is twice the Taylor coefficient of the corresponding degree.
Deviation: This evaluates the residue directly on the test function. In the
paper's scaled differential notation the odd coefficient has phase +i. -/
theorem infiniteLocalIdelicZFunction_real_residue (w : InfinitePlace F) (hw : w.IsReal)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (k : ℕ) :
    let n := 2 * k + a.val
    let s₀ : ℂ := -(n : ℂ)
    Tendsto (fun s : ℂ ↦ (s - s₀) * infiniteLocalIdelicZFunction w f (chart∞[w, χ] s))
      (𝓝[≠] s₀) (𝓝 (2 * iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0 /
        (n.factorial : ℂ))) := by sorry

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The z-Wirtinger derivative differentiates
in the two real coordinate directions with coefficients 1/2 and −i/2.
Deviation: The scaling by 1/(2πi) is absorbed into the residue formula. -/
def wirtingerDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The conjugate-Wirtinger derivative
uses coefficients 1/2 and i/2 in the real coordinate directions.
Deviation: The scaling by 1/(2πi) is absorbed into the residue formula. -/
def wirtingerConjDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The Wirtinger derivatives distinguish
the coordinate function from its conjugate. -/
theorem wirtingerDeriv_id_conj (z : ℂ) :
    wirtingerDeriv id z = 1 ∧ wirtingerDeriv star z = 0 ∧
      wirtingerConjDeriv id z = 0 ∧ wirtingerConjDeriv star z = 1 := by sorry

/-- Paper: Lemma 3.3.2.1(2)(2), pp. 138–139. At a complex pole the residue
is 2π times the Taylor coefficient of angular weight opposite to the character.
Deviation: This uses unscaled Wirtinger derivatives on the test function,
absorbing the phase and normalization into the Taylor coefficient. -/
theorem infiniteLocalIdelicZFunction_complex_residue (w : InfinitePlace F) (hw : w.IsComplex)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r]) (m : ℕ) :
    let s₀ : ℂ := -(r.natAbs : ℂ) / 2 - m
    let a := m + (-r).toNat
    let b := m + r.toNat
    let g : ℂ → ℂ := fun z ↦ test(f) ((complexModel(hw)).symm z)
    Tendsto (fun s : ℂ ↦ (s - s₀) * infiniteLocalIdelicZFunction w f (chart∞[w, χ] s))
      (𝓝[≠] s₀) (𝓝 (2 * (Real.pi : ℂ) *
        ((wirtingerConjDeriv^[b]) ((wirtingerDeriv^[a]) g)) 0 /
        ((a.factorial : ℂ) * (b.factorial : ℂ)))) := by sorry

/-- Paper: Equation (3.3.2.11), p. 139. The archimedean local functional
equation holds between meromorphic continuations with the standard Fourier transform.
Deviation: Equality is expressed off a discrete set of exponents. -/
theorem infiniteLocalIdelicZFunction_functionalEquation (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    ∃ fHat : ℬ(w.Completion), test(fHat) = F∞(w) test(f) ∧
      ∀ χ : PontryaginDual w.Completionˣ, ∀ᶠ s : ℂ in codiscrete ℂ,
        let c := chart∞[w, χ] s
        infiniteLocalIdelicZFunction w f c = infiniteLocalTateFactor w c *
          infiniteLocalIdelicZFunction w fHat (dualQuasiCharacter m∞(w) h∞(w) c) := by sorry

/-- Paper: Equation (3.3.2.11), p. 139. The finite-place local functional
equation holds between meromorphic continuations with the standard Fourier transform.
Deviation: Equality is expressed off a discrete set of exponents. -/
theorem finiteLocalIdelicZFunction_functionalEquation (v : Primes) (f : ℬ(v.adicCompletion F)) :
    ∃ fHat : ℬ(v.adicCompletion F), test(fHat) = F𝔭(v) test(f) ∧
      ∀ χ : PontryaginDual (v.adicCompletion F)ˣ, ∀ᶠ s : ℂ in codiscrete ℂ,
        let c := chart𝔭[v, χ] s
        finiteLocalIdelicZFunction v f c = finiteLocalTateFactor v c *
          finiteLocalIdelicZFunction v fHat (dualQuasiCharacter m𝔭(v) h𝔭(v) c) := by sorry

/-- Paper: Lemma 3.3.2.2, p. 141. Each scalar finite local zeta function
has at most simple poles. A pole occurs for some test function exactly over
the trivial quasi-character, including its periodic lifts in the exponent plane.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem finiteLocalIdelicZFunction_poles (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) (s : ℂ) :
    (∀ f : ℬ(v.adicCompletion F),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s) ∧
    ((∃ f : ℬ(v.adicCompletion F),
      meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s = -1) ↔
      chart𝔭[v, χ] s = 1) := by sorry

-- TODO(paper-gap): In (3.3.2.23) the indicator of ℤₚˣ would have nonzero
-- residue, but its trivial-component zeta integral is identically 1.
-- The measure relation used under (3.3.2.25) omits the finite-place factor
-- q/(q−1) of Lemma A.3.2.3.

/-- Paper: Equation (3.3.2.23), p. 141. The residue at the trivial character
is evaluation at zero times the multiplicative mass of the integer units
divided by log of the residue field size.
Deviation: Fourier inversion yields f(0). The factor 1−q⁻¹ cancels against
the weighted measure factor in Lemma A.3.2.3. -/
theorem finiteLocalIdelicZFunction_residue (v : Primes) (f : ℬ(v.adicCompletion F)) :
    Tendsto (fun s : ℂ ↦ s * finiteLocalIdelicZFunction v f
      (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s)) (𝓝[≠] 0)
      (𝓝 (((μ𝔭(v) (v.adicCompletionIntegers F).units).toReal : ℂ) /
        (Real.log (q(v) : ℝ) : ℂ) * test(f) 0)) := by sorry

end RiemannMasullo
