module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4

/-! # Third Structure Theorem: strong duals and eigendistributions

Masullo, §5.5, pp. 277–285. The finite set in the S-local notation lists only
the finite places. The archimedean places are included in every S-local space.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Aₛ" => SAdeleRing F S
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "m𝔽" => ideleClassNorm F
local notation "Kₛ" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)
local notation "Kₛω(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "D(" V ")" => StrongDual ℂ V
local notation "pull(" K ")" =>
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ (Submodule.mkQL K)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartₛ(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((circleToComplex).comp χ)
local notation "restricts(" c ", " m ", " ω ")" =>
  (normOneRestriction m c = (circleToComplex).comp ω)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

section Eigendistributions

/-- Paper: Definition 5.5.1.1(1), p. 277.
The S-local weight space pulls the weight on S-idele classes back to the S-ideles
acting on Schwartz–Bruhat tests. The submodule carries its strong-dual subspace topology. -/
def sLocalEigendistributions (c : QuasiCharacter Jₛ) : Submodule ℂ D(ℬ(Aₛ)) :=
  schwartzBruhatEigendistributions
    (c.comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : QuasiCharacter Aₛˣ)

/-- Paper: Definition 5.5.1.1(1), p. 277.
Membership is the weight equation after translating a test by an S-idele. -/
theorem mem_sLocalEigendistributions (c : QuasiCharacter Jₛ) (T : D(ℬ(Aₛ))) :
    T ∈ sLocalEigendistributions c ↔ ∀ (u : Aₛˣ) (f : ℬ(Aₛ)),
      T (schwartzBruhatUnitTranslate u f) = c (QuotientGroup.mk u) * T f := by sorry

/-- Paper: Definition 5.5.1.1(1), p. 277.
The S-local weight subspace is closed for the strong topology. -/
theorem sLocalEigendistributions_isClosed (c : QuasiCharacter Jₛ) :
    IsClosed (sLocalEigendistributions c : Set D(ℬ(Aₛ))) := by sorry

/-- Paper: Definition 5.5.1.1(2), p. 278.
The global weight subspace of §3.4 is closed for the strong topology. -/
theorem adelicEigendistributions_isClosed (c : QuasiCharacter C𝔽) :
    IsClosed (adelicEigendistributions c : Set D(ℬ(𝔸[F]))) := by sorry

end Eigendistributions

section SLocal

local notation "unitMass(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F v) (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The continued normalized S-local zeta values give the tensor generator as a
continuous linear functional.
Deviation: The product of the finite integer-unit masses accounts for the
Tamagawa normalization of the local factors, as in §3.4. -/
theorem existsUnique_sLocalNormalizedEigendistribution (c : QuasiCharacter Jₛ) :
    ∃! T : D(ℬ(Aₛ)), ∀ f : ℬ(Aₛ),
      (↑(∏ v : S, unitMass(v.val)) : ℂ) * T f = sLocalNormalizedZFunction f c := by sorry

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The S-local generator is the functional given by the continued normalized zeta values.
Deviation: The normalization incorporates the finite integer-unit masses. -/
def sLocalNormalizedEigendistribution (c : QuasiCharacter Jₛ) : D(ℬ(Aₛ)) :=
  (existsUnique_sLocalNormalizedEigendistribution c).exists.choose

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The normalized S-local generator takes the value one on the pure tensor of the
local standard Gaussians of §3.4. -/
theorem sLocalNormalizedEigendistribution_gaussian (χ : PontryaginDual Jₛ) (s : ℂ)
    (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (f : ℬ(Aₛ))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w, infiniteStandardGaussian w (χArch w) (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, finiteStandardGaussian v.val (sLocalFiniteRestriction v (chartₛ(χ) s))
          (Multiplicative.ofAdd (x.2 v))) :
    sLocalNormalizedEigendistribution (chartₛ(χ) s) f = 1 := by sorry

/-- Paper: Theorem 5.5.1.2(1), p. 278.
On a pure tensor the S-local generator is the product of the local Gaussian-normalized
eigendistributions. The restrictions of the weight specify the local eigen equations. -/
theorem sLocalNormalizedEigendistribution_apply_pureTensor (χ : PontryaginDual Jₛ) (s : ℂ)
    (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (TArch : (w : InfinitePlace F) → D(ℬ(w.Completion)))
    (TFin : (v : S) → D(ℬ(v.val.adicCompletion F)))
    (hArch : ∀ w, TArch w ∈
      schwartzBruhatEigendistributions (sLocalInfiniteRestriction w (chartₛ(χ) s)) ∧
      TArch w (infiniteStandardGaussian w (χArch w)) = 1)
    (hFin : ∀ v, TFin v ∈
      schwartzBruhatEigendistributions (sLocalFiniteRestriction v (chartₛ(χ) s)) ∧
      TFin v (finiteStandardGaussian v.val (sLocalFiniteRestriction v (chartₛ(χ) s))) = 1)
    (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
    (fFin : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w, fArch w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, fFin v (Multiplicative.ofAdd (x.2 v))) :
    sLocalNormalizedEigendistribution (chartₛ(χ) s) f =
      (∏ w, TArch w (fArch w)) * ∏ v : S, TFin v (fFin v) := by sorry

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The normalized S-local distribution spans the eigenspace of its weight. -/
theorem sLocalEigendistributions_eq_span (c : QuasiCharacter Jₛ) :
    sLocalEigendistributions c =
      Submodule.span ℂ {sLocalNormalizedEigendistribution c} := by sorry

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The normalized S-local distributions form a holomorphic family on each norm chart. -/
theorem sLocalNormalizedEigendistribution_holomorphic (χ : PontryaginDual Jₛ) :
    VectorHolomorphicOn (fun s ↦ sLocalNormalizedEigendistribution (chartₛ(χ) s)) univ := by sorry

/-- Paper: Theorem 5.5.1.2(2), pp. 278–279.
Each S-local eigendistribution has a unique continuous descent to the theta space.
On quotient representatives, its descended weight equation follows the same convention
as Definition 5.5.1.1. -/
theorem sLocalEigendistribution_descends (c : QuasiCharacter Jₛ) (T : D(ℬ(Aₛ)))
    (hT : T ∈ sLocalEigendistributions c) :
    ∃! U : D(SLocalAdelicThetaSpace F S), pull(Kₛ) U = T := by sorry

/-- Paper: Equation (5.5.1.12), p. 279.
The normalized S-local eigendistribution annihilates the theta kernel. -/
theorem sLocalThetaKernel_le_eigendistribution (c : QuasiCharacter Jₛ) :
    Kₛ ≤ (sLocalNormalizedEigendistribution c).ker := by sorry

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The generator on the S-local theta quotient is the continuous descent of the
normalized eigendistribution. -/
def sLocalThetaEigendistribution (c : QuasiCharacter Jₛ) : D(SLocalAdelicThetaSpace F S) :=
  (Kₛ).liftQL (sLocalNormalizedEigendistribution c) (sLocalThetaKernel_le_eigendistribution c)

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The descended generator evaluates on a theta class by acting on its Schwartz–Bruhat
representative. -/
theorem sLocalThetaEigendistribution_mk (c : QuasiCharacter Jₛ) (f : ℬ(Aₛ)) :
    sLocalThetaEigendistribution c ((Kₛ).mkQL f) = sLocalNormalizedEigendistribution c f := by sorry

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The eigenspace in the S-local theta dual is the line through the descended generator.
The weight condition is tested after pullback to Schwartz–Bruhat functions. -/
theorem sLocalThetaEigendistributions_eq_span (c : QuasiCharacter Jₛ) :
    (sLocalEigendistributions c).comap (pull(Kₛ)).toLinearMap =
      Submodule.span ℂ {sLocalThetaEigendistribution c} := by sorry

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The normalized S-local family in the strong dual of the theta quotient is holomorphic. -/
theorem sLocalThetaEigendistribution_holomorphic (χ : PontryaginDual Jₛ) :
    VectorHolomorphicOn (fun s ↦ sLocalThetaEigendistribution (chartₛ(χ) s)) univ := by sorry

end SLocal

section Global

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The global normalized generator from §3.4 is uniquely specified by its
weight and by its value on the standard Gaussian in any chart. -/
theorem existsUnique_adelicNormalizedEigendistribution (c : QuasiCharacter C𝔽) :
    ∃! T : D(ℬ(𝔸[F])), T ∈ adelicEigendistributions c ∧
      ∀ (χ : PontryaginDual C𝔽) (s : ℂ), ideleClassNormTwist χ s = c →
        T (adelicStandardGaussian χ) = 1 := by sorry

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The global generator is the Gaussian-normalized eigendistribution.
Its restricted tensor evaluations are given by `adelicEigendistribution_apply_pureTensor`. -/
def adelicNormalizedEigendistribution (c : QuasiCharacter C𝔽) : D(ℬ(𝔸[F])) :=
  (existsUnique_adelicNormalizedEigendistribution c).exists.choose

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The global normalized generator takes the value one on the Gaussian for its weight. -/
theorem adelicNormalizedEigendistribution_gaussian (χ : PontryaginDual C𝔽) (s : ℂ) :
    adelicNormalizedEigendistribution (ideleClassNormTwist χ s) (adelicStandardGaussian χ) =
      1 := by sorry

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The normalized global distribution spans the eigenspace of its weight. -/
theorem adelicEigendistributions_eq_span (c : QuasiCharacter C𝔽) :
    adelicEigendistributions c = Submodule.span ℂ {adelicNormalizedEigendistribution c} := by sorry

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The normalized global distributions form a holomorphic family on each norm chart. -/
theorem adelicNormalizedEigendistribution_holomorphic (χ : PontryaginDual C𝔽) :
    VectorHolomorphicOn (fun s ↦ adelicNormalizedEigendistribution (ideleClassNormTwist χ s))
      univ := by sorry

/-- Paper: Theorem 5.5.1.3(2), p. 279.
Each global eigendistribution descends uniquely to the theta quotient. The pullback
equation identifies the descended distribution and encodes its weight on representatives. -/
theorem adelicEigendistribution_descends (c : QuasiCharacter C𝔽) (T : D(ℬ(𝔸[F])))
    (hT : T ∈ adelicEigendistributions c) :
    ∃! U : D(GlobalAdelicThetaSpace F), pull(K𝔽) U = T := by sorry

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The normalized adelic eigendistribution annihilates the global theta kernel,
so its descent is a continuous linear quotient lift. -/
theorem globalThetaKernel_le_eigendistribution (c : QuasiCharacter C𝔽) :
    K𝔽 ≤ (adelicNormalizedEigendistribution c).ker := by sorry

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The generator on the global theta quotient is the continuous descent of the
normalized adelic eigendistribution. -/
def globalThetaEigendistribution (c : QuasiCharacter C𝔽) : D(GlobalAdelicThetaSpace F) :=
  Submodule.liftQL (σ := RingHom.id ℂ) (M := ℬ(𝔸[F])) (M₂ := ℂ) (K𝔽)
    (adelicNormalizedEigendistribution (F := F) c) (globalThetaKernel_le_eigendistribution (F := F) c)

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The descended global generator evaluates on a theta class by acting on its representative. -/
theorem globalThetaEigendistribution_mk (c : QuasiCharacter C𝔽) (f : ℬ(𝔸[F])) :
    globalThetaEigendistribution c ((K𝔽).mkQL f) = adelicNormalizedEigendistribution c f := by sorry

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The eigenspace in the global theta dual is the line through the descended generator,
with the weight condition tested on the pullback. -/
theorem globalThetaEigendistributions_eq_span (c : QuasiCharacter C𝔽) :
    (adelicEigendistributions c).comap (pull(K𝔽)).toLinearMap =
      Submodule.span ℂ {globalThetaEigendistribution c} := by sorry

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The normalized global family in the strong dual of the theta quotient is holomorphic. -/
theorem globalThetaEigendistribution_holomorphic (χ : PontryaginDual C𝔽) :
    VectorHolomorphicOn (fun s ↦ globalThetaEigendistribution (ideleClassNormTwist χ s))
      univ := by sorry

/-- Paper: Remark 5.5.1.4, p. 280.
The descended S-local eigendistributions span a strongly dense subspace of the theta dual. -/
theorem sLocalThetaEigendistributions_dense_span :
    Dense (Submodule.span ℂ (Set.range (sLocalThetaEigendistribution (F := F) (S := S))) :
      Set D(SLocalAdelicThetaSpace F S)) := by sorry

end Global

section PolarValues

local notation "Θ" => GlobalAdelicThetaSpace F
local notation "unitaryOne" => (1 : PontryaginDual C𝔽)
local notation "normWeight" => ideleClassNormTwist unitaryOne 1
local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose
local notation "normℂ(" g ")" => (((m𝔽 g : ℝ≥0) : ℝ) : ℂ)

/-- Paper: Lemma 5.5.2.1, p. 280.
The theta kernel is contained in the common polar kernel from §2.2.4, so both
continuous polar functionals vanish on it. -/
theorem globalThetaKernel_le_adelePolarSubspace :
    K𝔽 ≤ LinearMap.ker (adelePolarValues (F := F)) := by sorry

/-- Paper: Lemma 5.5.2.1, p. 280.
Evaluation at zero and Fourier evaluation at zero descend as a pair of
continuous linear functionals on the global theta quotient. -/
def globalThetaPolarValues : Θ →L[ℂ] ℂ × ℂ :=
  ⟨Submodule.liftQ (τ₁₂ := RingHom.id ℂ) (K𝔽) (adelePolarValues (F := F))
      (globalThetaKernel_le_adelePolarSubspace (F := F)),
    continuous_quot_lift _ (adelePolarValues_continuous (F := F))⟩

/-- Paper: Lemma 5.5.2.1, p. 280.
The two descended values on a theta class are the evaluations at zero of its
representative and of the Fourier transform of that representative. -/
theorem globalThetaPolarValues_mk (f : ℬ(𝔸[F])) :
    globalThetaPolarValues (F := F) ((K𝔽).mkQL f) =
      (f zeroAdele, adeleSchwartzFourier f zeroAdele) := by sorry

/-- Paper: Lemma 5.5.2.1, p. 280.
The evaluations on test representatives uniquely determine the descended pair. -/
theorem globalThetaPolarValues_unique (P : Θ →L[ℂ] ℂ × ℂ)
    (hP : ∀ f : ℬ(𝔸[F]), P ((K𝔽).mkQL f) = (f zeroAdele, adeleSchwartzFourier f zeroAdele)) :
    P = globalThetaPolarValues (F := F) := by sorry

/-- Paper: Lemma 5.5.2.1, p. 280.
Evaluation at zero on the global theta quotient has weight one. -/
theorem globalThetaPolarValues_fst_translate (g : C𝔽) (x : Θ) :
    (globalThetaPolarValues (F := F) (ρ𝔽 g x)).1 = (globalThetaPolarValues (F := F) x).1 := by sorry

/-- Paper: Lemma 5.5.2.1, p. 280.
Fourier evaluation at zero on the global theta quotient has weight equal to the idelic norm. -/
theorem globalThetaPolarValues_snd_translate (g : C𝔽) (x : Θ) :
    (globalThetaPolarValues (F := F) (ρ𝔽 g x)).2 = normℂ(g) * (globalThetaPolarValues (F := F) x).2 := by sorry

/-- Paper: Lemma 5.5.2.1, p. 280.
On the trivial norm-one isotype the two polar values can be prescribed independently.
Deviation: This records the range needed in (6.3.2.5)–(6.3.2.6) on p. 304. -/
theorem globalThetaPolarValues_surjective_on_trivial_isotype :
    Surjective (fun x : actionIsotype ((ρ𝔽).comp (m𝔽).ker.subtype) 1 ↦
      globalThetaPolarValues (F := F) x.val) := by sorry

/-- Paper: Lemma 5.5.2.1, p. 280.
Both polar functionals vanish on the norm-one isotype precisely when its character
is nontrivial. The isotype is viewed inside the ordinary theta quotient. -/
theorem globalThetaPolarValues_vanish_on_isotype_iff (ω : PontryaginDual (m𝔽).ker) :
    (∀ x : Θ, (∀ g : (m𝔽).ker, ρ𝔽 g.val x = (ω g : ℂ) • x) →
      globalThetaPolarValues (F := F) x = 0) ↔ ω ≠ 1 := by sorry

-- TODO(paper-gap): In (5.5.2.3) each equality loses the value of the polar
-- functional on the normalized Gaussian. For ℚ(i) the first value is 1/(2π).

/-- Paper: Equation (5.5.2.3), p. 280.
The two polar functionals are multiples of the descended normalized generators.
Deviation: The multipliers are the values of the polar functionals on the standard
Gaussian, which need not equal one. -/
theorem globalThetaPolarValues_eq_eigendistributions (x : Θ) :
    let f := adelicStandardGaussian unitaryOne
    globalThetaPolarValues (F := F) x =
      (f zeroAdele * globalThetaEigendistribution (F := F) (1 : QuasiCharacter C𝔽) x,
        adeleSchwartzFourier f zeroAdele * globalThetaEigendistribution (F := F) normWeight x) := by sorry

/-- Paper: Remark 5.5.2.2, p. 281.
The putative orbit sum for evaluation at zero is summable exactly when the test
vanishes at zero, since each translated summand is the same value.
Deviation: The printed divergence claim requires a nonzero value at zero. -/
theorem summable_globalZeroEval_orbit_iff (f : ℬ(𝔸[F])) :
    Summable (fun a : Fˣ ↦ f (Multiplicative.ofAdd
      ((algebraMap F 𝔸[F]) ((a⁻¹ : Fˣ) : F) * 0))) ↔ f zeroAdele = 0 := by sorry

end PolarValues

section LocalGeneration

local notation "finiteModule(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "infiniteModule(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)

-- TODO(paper-gap): The proof of Proposition 5.5.3.1 identifies the weak and
-- strong dual topologies. The needed claim is equality of closures of linear subspaces.

/-- Paper: Proposition 5.5.3.1, p. 281.
At a finite place the eigendistributions span a strongly dense subspace of the dual.
The set of all eigenvectors gives the same span as the normalized generators of §3.4. -/
theorem finiteEigendistributions_dense_span (v : HeightOneSpectrum (𝓞 F)) :
    Dense (Submodule.span ℂ {T : D(ℬ(v.adicCompletion F)) |
      ∃ c : QuasiCharacter (v.adicCompletion F)ˣ, T ∈ schwartzBruhatEigendistributions c} :
      Set D(ℬ(v.adicCompletion F))) := by sorry

/-- Paper: Proposition 5.5.3.1, p. 281.
At an infinite place the eigendistributions span a strongly dense subspace of the dual.
The set of all eigenvectors gives the same span as the normalized generators of §3.4. -/
theorem infiniteEigendistributions_dense_span (w : InfinitePlace F) :
    Dense (Submodule.span ℂ {T : D(ℬ(w.Completion)) |
      ∃ c : QuasiCharacter w.Completionˣ, T ∈ schwartzBruhatEigendistributions c} :
      Set D(ℬ(w.Completion))) := by sorry

/-- Paper: Proposition 5.5.3.1, p. 281.
At a finite place the closed span of eigendistributions with prescribed norm-one
restriction is the corresponding homogeneous subspace of the strong dual.
Only the restriction of the unitary character to the local norm-one units matters. -/
theorem finiteEigendistributions_component_closedSpan (v : HeightOneSpectrum (𝓞 F))
    (ω : PontryaginDual (v.adicCompletion F)ˣ) :
    closure (Submodule.span ℂ {T : D(ℬ(v.adicCompletion F)) |
      ∃ c : QuasiCharacter (v.adicCompletion F)ˣ,
        (∀ u : (finiteModule(v)).ker, c u.val = (ω u.val : ℂ)) ∧
          T ∈ schwartzBruhatEigendistributions c} : Set D(ℬ(v.adicCompletion F))) =
      {T | ∀ (u : (finiteModule(v)).ker) (f : ℬ(v.adicCompletion F)),
        T (schwartzBruhatUnitTranslate u.val f) = (ω u.val : ℂ) * T f} := by sorry

/-- Paper: Proposition 5.5.3.1, p. 281.
At an infinite place the closed span of eigendistributions with prescribed norm-one
restriction is the corresponding homogeneous subspace of the strong dual.
Only the restriction of the unitary character to the local norm-one units matters. -/
theorem infiniteEigendistributions_component_closedSpan (w : InfinitePlace F)
    (ω : PontryaginDual w.Completionˣ) :
    closure (Submodule.span ℂ {T : D(ℬ(w.Completion)) |
      ∃ c : QuasiCharacter w.Completionˣ,
        (∀ u : (infiniteModule(w)).ker, c u.val = (ω u.val : ℂ)) ∧
          T ∈ schwartzBruhatEigendistributions c} : Set D(ℬ(w.Completion))) =
      {T | ∀ (u : (infiniteModule(w)).ker) (f : ℬ(w.Completion)),
        T (schwartzBruhatUnitTranslate u.val f) = (ω u.val : ℂ) * T f} := by sorry

end LocalGeneration

section StructureTheorem

-- TODO(paper-gap): In the proof of Theorem 5.5.3.2 on pp. 283–284,
-- vectors in a spectral interval need not be eigenvectors at a point of that interval.
-- On L²(ℝ, dx), multiplication by x ↦ exp(itx) has no nonzero common eigenvectors.

/-- Paper: Theorem 5.5.3.2(1), p. 282.
Pullback along the homogeneous S-local theta quotient is injective on strong duals. -/
theorem sLocalHomogeneousThetaTranspose_injective (ω : PontryaginDual (mₛ).ker) :
    Injective (pull(Kₛω(ω))) := by sorry

/-- Paper: Theorem 5.5.3.2(1), p. 282.
Distributions pulled back from the homogeneous S-local theta quotient have weight
`ω` on the norm-one classes.
Deviation: The weight uses the transpose convention of (5.5.1.1) and the
homogeneous theta transform of §5.2. The proof on p. 284 also uses a contragredient. -/
theorem sLocalHomogeneousThetaTranspose_homogeneous (ω : PontryaginDual (mₛ).ker)
    (T : D(SLocalHomogeneousThetaSpace F S ω)) (g : (mₛ).ker) (u : Aₛˣ)
    (hu : QuotientGroup.mk u = g.val) (f : ℬ(Aₛ)) :
    pull(Kₛω(ω)) T (schwartzBruhatUnitTranslate u f) =
      (ω g : ℂ) * pull(Kₛω(ω)) T f := by sorry

/-- Paper: Theorem 5.5.3.2(1), p. 282.
The strong closure of the homogeneous S-local theta transpose range is the closed
span of the normalized eigendistributions whose weights restrict to the given character.
The generators are expressed by their pullbacks to the test space. -/
theorem sLocalHomogeneousThetaTranspose_closure_range (ω : PontryaginDual (mₛ).ker) :
    closure (Set.range (pull(Kₛω(ω)))) =
      closure (Submodule.span ℂ
        (sLocalNormalizedEigendistribution '' {c : QuasiCharacter Jₛ | restricts(c, mₛ, ω)}) :
          Set D(ℬ(Aₛ))) := by sorry

/-- Paper: Theorem 5.5.3.2(2), p. 282.
Pullback along the ordinary S-local theta quotient is injective on strong duals. -/
theorem sLocalThetaTranspose_injective :
    Injective (pull(Kₛ)) := by sorry

/-- Paper: Theorem 5.5.3.2(2), p. 282.
Distributions pulled back from the S-local theta quotient are invariant under the
projected diagonal S-units, the kernel of the map to S-idele classes. -/
theorem sLocalThetaTranspose_invariant (T : D(SLocalAdelicThetaSpace F S)) (u : Aₛˣ)
    (hu : (QuotientGroup.mk u : Jₛ) = 1) (f : ℬ(Aₛ)) :
    pull(Kₛ) T (schwartzBruhatUnitTranslate u f) = pull(Kₛ) T f := by sorry

/-- Paper: Theorem 5.5.3.2(2), p. 282.
The strong closure of the ordinary S-local theta transpose range is the closed span
of all normalized S-local eigendistributions pulled back from the theta quotient. -/
theorem sLocalThetaTranspose_closure_range :
    closure (Set.range (pull(Kₛ))) =
      closure (Submodule.span ℂ (Set.range (sLocalNormalizedEigendistribution (F := F) (S := S))) :
        Set D(ℬ(Aₛ))) := by sorry

-- TODO(paper-gap): Remark 5.5.3.3, p. 285, claims that one connected subset of weights
-- with an interval in it detects the whole theta space. A subset of a single component
-- cannot see the other norm-one isotypes.

/-- Paper: Remark 5.5.3.3, p. 285.
The S-local eigendistributions over all weights separate points of the S-local theta space.
Deviation: Weights range over all components of the character space. -/
theorem sLocalThetaEigendistributions_separate (x : SLocalAdelicThetaSpace F S)
    (hx : ∀ c : QuasiCharacter Jₛ, sLocalThetaEigendistribution c x = 0) : x = 0 := by sorry

/-- Paper: Remark 5.5.3.3, p. 285.
The eigendistributions with weights in a set that has an accumulation point in every
norm chart separate points of ordinary theta space.
Deviation: The identity theorem applies on each connected component separately. -/
theorem sLocalThetaEigendistributions_separate_of_accumulation
    (W : Set (QuasiCharacter Jₛ))
    (hW : ∀ χ : PontryaginDual Jₛ, ∃ z : ℂ,
      z ∈ closure ((chartₛ(χ) ⁻¹' W) \ {z}))
    (x : SLocalAdelicThetaSpace F S)
    (hx : ∀ c ∈ W, sLocalThetaEigendistribution c x = 0) : x = 0 := by sorry

/-- Paper: Theorem 5.5.3.4(1), p. 285.
Pullback from the homogeneous global theta quotient is a topological embedding
for the strong dual topologies. -/
theorem globalHomogeneousThetaTranspose_isEmbedding (ω : PontryaginDual (m𝔽).ker) :
    IsEmbedding (pull(K𝔽ω(ω))) := by sorry

/-- Paper: Theorem 5.5.3.4(1), p. 285.
The global homogeneous theta transpose takes values in the distributions that
transform by the specified character on the norm-one classes. -/
theorem globalHomogeneousThetaTranspose_homogeneous (ω : PontryaginDual (m𝔽).ker)
    (T : D(GlobalHomogeneousThetaSpace F ω)) (g : (m𝔽).ker)
    (u : IdeleGroup (𝓞 F) F) (hu : QuotientGroup.mk u = g.val) (f : ℬ(𝔸[F])) :
    pull(K𝔽ω(ω)) T (schwartzBruhatUnitTranslate u f) =
      (ω g : ℂ) * pull(K𝔽ω(ω)) T f := by sorry

/-- Paper: Theorem 5.5.3.4(1), p. 285.
The range of the global homogeneous theta transpose is strongly generated by
the normalized eigendistributions whose weights restrict to the given character.
The generators are expressed by their pullbacks to the test space. -/
theorem globalHomogeneousThetaTranspose_range (ω : PontryaginDual (m𝔽).ker) :
    Set.range (pull(K𝔽ω(ω))) =
      closure (Submodule.span ℂ
        (adelicNormalizedEigendistribution (F := F) '' {c : QuasiCharacter C𝔽 | restricts(c, m𝔽, ω)}) :
          Set D(ℬ(𝔸[F]))) := by sorry

-- The global embedding in Theorem 5.5.3.4(2) is already stated as
-- `globalThetaQuotient_transpose_isEmbedding` in §5.2.

/-- Paper: Theorem 5.5.3.4(2), p. 285.
Distributions pulled back from the ordinary global theta quotient are invariant under
principal ideles, the kernel of the map to idele classes. -/
theorem globalThetaTranspose_invariant (T : D(GlobalAdelicThetaSpace F))
    (u : IdeleGroup (𝓞 F) F) (hu : (QuotientGroup.mk u : C𝔽) = 1) (f : ℬ(𝔸[F])) :
    pull(K𝔽) T (schwartzBruhatUnitTranslate u f) = pull(K𝔽) T f := by sorry

/-- Paper: Theorem 5.5.3.4(2), p. 285.
The range of the ordinary global theta transpose is the strongly closed span of
all normalized adelic eigendistributions pulled back from the theta quotient. -/
theorem globalThetaTranspose_range :
    Set.range (pull(K𝔽)) =
      closure (Submodule.span ℂ (Set.range (adelicNormalizedEigendistribution (F := F))) :
        Set D(ℬ(𝔸[F]))) := by sorry

end StructureTheorem

end RiemannMasullo
