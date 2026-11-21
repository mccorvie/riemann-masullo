module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.DedekindZeta

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
    ideleClassNormTwist (1 : U[F]) 1 g = (classNormℝ g : ℂ) := by sorry

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
      1 - finitePlaceRestriction F v (ideleClassNormTwist χ s) π := by sorry

/-- Paper: Equation (3.2.1.4), p. 123. A real local unitary character has a
unique imaginary radial exponent and a unique sign parity. -/
theorem realHeckeCharacter_parameters (χ : U[F]) (v : InfinitePlace F) (hv : v.IsReal) :
    ∃! a : ℂ × Fin 2, a.1.re = 0 ∧ ∀ x : ℝˣ,
      infinitePlaceRestriction F v χ₀(χ)
          (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x) =
        (‖(x : ℝ)‖ : ℂ) ^ a.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.2.val := by sorry

/-- Paper: Equation (3.2.1.5), p. 123. A complex local unitary character has a
unique imaginary radial exponent and integer angular weight.
Deviation: We take the radius in the paper to be the normalized absolute value `‖x‖²`. -/
theorem complexHeckeCharacter_parameters (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    ∃! a : ℂ × ℤ, a.1.re = 0 ∧ ∀ x : ℂˣ,
      infinitePlaceRestriction F v χ₀(χ)
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom x) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a.1 * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ a.2 := by sorry

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
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F := by sorry

/-- Paper: Lemma 3.2.1.1, p. 123. On each compact subset of `Re(s) > 1`,
the deviations of the Euler factors from one are absolutely and uniformly summable. -/
theorem finiteHeckeEulerFactor_summableUniformlyOn (χ : U[F])
    (K : Set ℂ) (hK : IsCompact K) (h : K ⊆ halfPlane) :
    SummableUniformlyOn (fun v s ↦ ‖finiteHeckeEulerFactor χ v s - 1‖) K := by sorry

/-- Paper: Lemma 3.2.1.1, p. 123. The Euler product multiplied by the archimedean
gamma factor converges uniformly on compact subsets of the open half-plane. -/
theorem completedHeckeEulerProduct_hasProdUniformlyOn (χ : U[F])
    (K : Set ℂ) (hK : IsCompact K) (h : K ⊆ halfPlane) :
    TendstoUniformlyOn
      (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦
        fun s ↦ heckeGammaFactor χ s * ∏ v ∈ S, finiteHeckeEulerFactor χ v s)
      (fun s ↦ heckeGammaFactor χ s * χ₀(χ).LSeries s) atTop K := by sorry

/-- Paper: Definition 3.2.1.2, p. 123. The Hecke L-function on the half-plane
is the archimedean gamma factor times Mathlib's finite Hecke L-series. -/
def completedHeckeL (χ : U[F]) (s : halfPlane) : ℂ :=
  heckeGammaFactor χ s * χ₀(χ).LSeries s

/-- Paper: Definition 3.2.1.2, p. 123. For the trivial character the completed
L-function on the half-plane is the corresponding gamma product times Dedekind zeta. -/
theorem completedHeckeL_one_eq_dedekindZeta (s : halfPlane) :
    completedHeckeL (1 : U[F]) s =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F * dedekindZeta F s := by sorry

/-- Paper: Proposition 3.2.1.3, p. 123. The completed Hecke L-function extends
meromorphically to the complex plane. We use Mathlib's normal form at poles. -/
theorem completedHeckeL_exists_continuation (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = completedHeckeL χ s := by sorry

/-- Paper: Proposition 3.2.1.3(1), p. 123. When the restriction to norm-one
classes is nontrivial, the continuation is entire. -/
theorem completedHeckeL_continuation_entire (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Differentiable ℂ L := by sorry

/-- Paper: Proposition 3.2.1.3(2), p. 123. If the character is trivial on norm-one
classes, there is a unique real norm-twist parameter and the two indicated poles
are simple. The continuation is analytic elsewhere.
Deviation: The printed residue formulas have a normalization conflict described below. -/
theorem completedHeckeL_continuation_simplePoles (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, χ₀(χ) = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) ∧
      meromorphicOrderAt L (Complex.I * (t : ℂ)) = -1 ∧
      meromorphicOrderAt L (1 + Complex.I * (t : ℂ)) = -1 ∧
      AnalyticOnNhd ℂ L ({Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}ᶜ) := by sorry

-- TODO(paper-gap): The residues printed in Proposition 3.2.1.3(2) disagree with the
-- Euler product normalization. For the trivial character of ℚ(√5), the residue at 1
-- is already the Appendix A.3.2.1 class volume, since both real gamma factors equal 1.

/-- Paper: Proposition 3.2.1.3(3), p. 123. Reflecting the continuation of the
inverse unitary character gives the original continuation times a nowhere-vanishing
entire function. Inversion agrees with complex conjugation for a unitary character. -/
theorem completedHeckeL_continuation_functionalEquation (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      ∀ s, Ldual (1 - s) = ε s * L s := by sorry

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
    LSeriesSummable χ₀(χ).LFunction s := by sorry

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Hecke L-function
is the value of the convergent Euler product with the ramified factors omitted. -/
theorem finiteHeckeL_hasProd (χ : U[F]) (s : halfPlane) :
    HasProd (fun v ↦ finiteHeckeEulerFactor χ v s) (finiteHeckeL χ s) := by sorry

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Euler product
converges uniformly on each compact subset of the half-plane. -/
theorem finiteHeckeL_hasProdUniformlyOn (χ : U[F]) (K : Set halfPlane) (hK : IsCompact K) :
    HasProdUniformlyOn (fun v (s : halfPlane) ↦ finiteHeckeEulerFactor χ v s) (finiteHeckeL χ) K :=
  by sorry

/-- Paper: Definition 3.2.1.4, p. 124. The finite Hecke L-function admits
a meromorphic continuation to the complex plane. -/
theorem finiteHeckeL_exists_continuation (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = finiteHeckeL χ s := by sorry

/-- Paper: Equation (3.2.1.9), p. 124. The reflection multiplier is the ratio
of the reflected and original gamma factors divided by the entire epsilon factor.
Deviation: Values at singularities use the meromorphic normal form. -/
def finiteHeckeReflectionFactor (χ : U[F]) (ε : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ (ε s)⁻¹ * (heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s)) univ

/-- Paper: Equation (3.2.1.9), p. 124. At the midpoint for the trivial character
the gamma factors cancel, leaving the reciprocal epsilon factor. -/
theorem finiteHeckeReflectionFactor_one_half (ε : ℂ → ℂ) (hε : Differentiable ℂ ε)
    (hn : ∀ s, ε s ≠ 0) :
    finiteHeckeReflectionFactor (1 : U[F]) ε (1 / 2) = (ε (1 / 2))⁻¹ := by sorry

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
    (1 : 𝕀[F]) ∈ ideleNormBand F a b ↔ a ≤ 1 ∧ 1 ≤ b := by sorry

/-- Paper: §3.2.2, p. 124. The surjective idele class norm takes values
other than one, so its abscissa is defined. -/
theorem ideleClassNorm_ne_one : ∃ g : C[F], ideleClassNorm F g ≠ 1 := by sorry

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
        ∂multiplicativeTamagawaMeasure F := by sorry

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
    EqOn (globalIdelicZFunction f) (globalIdelicZetaIntegral f) rightHalf := by sorry

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. In every norm-twist coordinate
the global Z-function is in meromorphic normal form. -/
theorem globalIdelicZFunction_meromorphic (f : ℬ[F]) (χ : U[F]) :
    MeromorphicNFOn (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) univ := by sorry

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
  sorry

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
