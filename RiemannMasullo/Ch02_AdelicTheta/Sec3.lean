module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1

/-!
# S-local adelic theta functions

Masullo, §2.3, pp. 98–106. As in §A.1.5, the place set is represented by
its finite part from Notation 2.3.1.1. All archimedean places are included
in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Uₛ" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)
local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "normℝ" => fun (g : Iₛ) ↦ valueℝ (sIdeleNorm F S g)
local notation "thetaTerm" => fun (f : ℬₛ) (ξ : Uₛ) (g : Iₛ) ↦
  f (Multiplicative.ofAdd (Units.val (unitAtS ξ * g)))
local notation "thetaSum" => fun (f : ℬₛ) (g : Iₛ) ↦ ∑' ξ : Uₛ, thetaTerm f ξ g

/-! ## S-local theta operators -/

/-- Paper: Proposition 2.3.1.2(1), p. 100. The series of norms of the
S-unit translates is summable uniformly on each compact set of S-ideles. -/
theorem sLocalAdelicTheta_summableUniformlyOn_norm (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    SummableUniformlyOn (fun (ξ : Uₛ) (g : Iₛ) ↦ ‖thetaTerm f ξ g‖) K := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit series converges
uniformly to its sum on each compact set of S-ideles. -/
theorem sLocalAdelicTheta_hasSumUniformlyOn (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    HasSumUniformlyOn (thetaTerm f) (thetaSum f) K := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit sum is a continuous
function of the S-idele. -/
theorem sLocalAdelicTheta_continuous (f : ℬₛ) : Continuous (thetaSum f) := by sorry

/-- Paper: Definition 2.3.1.1, p. 99. Forming the continuous S-unit sum
is complex linear in the test function. -/
theorem sLocalAdelicTheta_isLinear :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨thetaSum f, sLocalAdelicTheta_continuous F S f⟩ : C(Iₛ, ℂ))) :=
  by sorry

/-- Paper: Definition 2.3.1.1, p. 99. The S-local theta operator sums the
test function over the diagonal S-unit multiples of each S-idele. -/
def sLocalAdelicTheta : ℬₛ →ₗ[ℂ] C(Iₛ, ℂ) :=
  IsLinearMap.mk' _ (sLocalAdelicTheta_isLinear F S)

/-- Paper: Equation (2.3.1.2), p. 99. Evaluating S-local theta at an idele
gives the sum of the evaluations at its S-unit multiples. -/
theorem sLocalAdelicTheta_apply (f : ℬₛ) (g : Iₛ) :
    sLocalAdelicTheta F S f g = thetaSum f g := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. S-local theta is invariant under
left translation by S-units, expressed as constancy on each class fiber. -/
theorem sLocalAdelicTheta_factorsThrough (f : ℬₛ) :
    FactorsThrough (sLocalAdelicTheta F S f) classOf := by sorry

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit invariant theta
function descends to a continuous function on the S-idele classes. -/
def sLocalAdelicThetaOnClasses (f : ℬₛ) : C(Jₛ, ℂ) :=
  IsQuotientMap.lift (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk _) (sLocalAdelicTheta F S f)
    (sLocalAdelicTheta_factorsThrough F S f)

/-- Paper: Proposition 2.3.1.2(1), p. 100. The descended function at the
class of an S-idele agrees with theta at that S-idele. -/
theorem sLocalAdelicThetaOnClasses_mk (f : ℬₛ) (g : Iₛ) :
    sLocalAdelicThetaOnClasses F S f (classOf g) = sLocalAdelicTheta F S f g := by sorry

-- TODO(paper-gap): The support argument before (2.3.1.5) bounds only the finite
-- coordinates. On p. 104 the argument also switches to test functions on the
-- finite unit groups, where restrictions of additive test functions need not
-- have compact support.
-- TODO(paper-gap): The equality in (2.3.1.9) assumes that a section of the
-- idelic norm scales the Euclidean sup norm by t. Even at a single complex
-- place a positive-real section scales it by √t.

/-- Paper: Proposition 2.3.1.2(2), p. 100. As the S-idelic norm tends
to infinity, S-local theta decays at every positive inverse power. -/
theorem sLocalAdelicTheta_decay_large (f : ℬₛ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : Iₛ, T < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.2(3), p. 100. The large-norm decay constant
and threshold can be chosen uniformly for a bounded set of test functions. -/
theorem sLocalAdelicTheta_decay_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, T < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.2(4), p. 100. The bounded-set decay estimate
holds above S-idelic norm one with a uniform constant. -/
theorem sLocalAdelicTheta_decay_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

local instance normOneSIdeleQuotientMeasurableSpace (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

section HomogeneousTheta

-- TODO(paper-gap): Definition A.3.4.1(3)(3) names C_{F,S}^1 as the quotient
-- of the norm-one local S-ideles. The integral in (2.3.1.13) is over J_{F,S}^1.
-- The Haar measure on the latter is an explicit parameter pending its normalization.

variable (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm F S)))

local notation "classIntegrand" => fun (ω : PontryaginDual J₁) (f : ℬₛ) (g : Jₛ) (h : J₁) ↦
  sLocalAdelicThetaOnClasses F S f (g * Subtype.val h) * (ω h : ℂ)

/-- Paper: Proposition 2.3.1.4(1), p. 105. The character-weighted integral
is absolutely convergent at each S-idele class. -/
theorem sLocalHomogeneousAdelicTheta_integrable [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (g : Jₛ) :
    Integrable (classIntegrand ω f g) μ := by sorry

/-- Paper: Proposition 2.3.1.4(1), p. 105. On a compact set of S-ideles
the integrands have a common constant majorant on the compact norm-one classes.
Deviation: Uniform absolute convergence is expressed by this integrable majorant. -/
theorem sLocalHomogeneousAdelicTheta_integrand_bounded [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun _ : J₁ ↦ C) μ ∧
      ∀ g ∈ K, ∀ h : J₁, ‖classIntegrand ω f (classOf g) h‖ ≤ C := by sorry

/-- Paper: Proposition 2.3.1.4(1), p. 105. Integrating the character-weighted
theta function gives a continuous function on the S-idele classes. -/
theorem sLocalHomogeneousAdelicTheta_continuous [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) :
    Continuous (fun g : Jₛ ↦ ∫ h, classIntegrand ω f g h ∂μ) := by sorry

variable [Measure.IsHaarMeasure μ]

/-- Paper: Definition 2.3.1.3, p. 104. The character-weighted integral
defines a complex-linear map in the test function. -/
theorem sLocalHomogeneousAdelicTheta_isLinear (ω : PontryaginDual J₁) :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨fun g ↦ ∫ h, classIntegrand ω f g h ∂μ,
      sLocalHomogeneousAdelicTheta_continuous F S μ ω f⟩ : C(Jₛ, ℂ))) := by sorry

/-- Paper: Definition 2.3.1.3, p. 104. Homogeneous S-local theta integrates
theta at the class product `g * h` against the character on norm-one classes.
Deviation: The norm-one class Haar measure is an explicit parameter. In (2.3.1.13)
an idele argument is read through its class, as required by (2.3.1.12). -/
def sLocalHomogeneousAdelicTheta (ω : PontryaginDual J₁) : ℬₛ →ₗ[ℂ] C(Jₛ, ℂ) :=
  IsLinearMap.mk' _ (sLocalHomogeneousAdelicTheta_isLinear F S μ ω)

/-- Paper: Equation (2.3.1.13), p. 105. At the identity and for the trivial
character, homogeneous theta integrates unweighted theta on the norm-one classes. -/
theorem sLocalHomogeneousAdelicTheta_trivial_at_one (f : ℬₛ) :
    sLocalHomogeneousAdelicTheta F S μ (1 : PontryaginDual J₁) f 1 =
      ∫ h : J₁, sLocalAdelicThetaOnClasses F S f h.val ∂μ := by sorry

/-- Paper: Proposition 2.3.1.4(1), p. 105. Inverse left translation by a
norm-one class multiplies homogeneous theta by the character at that class.
Its pullback to the S-ideles has the corresponding pulled-back character. -/
theorem sLocalHomogeneousAdelicTheta_homogeneous (ω : PontryaginDual J₁)
    (f : ℬₛ) (h : J₁) (g : Jₛ) :
    sLocalHomogeneousAdelicTheta F S μ ω f (h.val⁻¹ * g) =
      (ω h : ℂ) * sLocalHomogeneousAdelicTheta F S μ ω f g := by sorry

/-- Paper: Proposition 2.3.1.4(2), p. 105. Homogeneous S-local theta decays
at every positive inverse power as the S-idelic norm tends to infinity. -/
theorem sLocalHomogeneousAdelicTheta_decay_large (ω : PontryaginDual J₁)
    (f : ℬₛ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : Iₛ, T < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.4(3), p. 105. The large-norm decay constants
for homogeneous S-local theta are uniform on a bounded set of test functions.
Deviation: Part (3) leaves the range of the exponent implicit. The nonnegative
range is supplied by part (4) and Proposition 2.3.1.2(3). -/
theorem sLocalHomogeneousAdelicTheta_decay_bounded (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, T < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Proposition 2.3.1.4(4), p. 105. The uniform decay estimate
for homogeneous theta holds above S-idelic norm one. -/
theorem sLocalHomogeneousAdelicTheta_decay_bounded_threshold_one (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

end HomogeneousTheta

/-! ## Directional derivatives -/

section DirectionalDerivatives

variable (γ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ)

local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)
local notation "orbitDeriv" => fun (f : ℬₛ) (x : Multiplicative Aₛ) ↦
  deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd (Units.val (γ (expUnit s)) * Multiplicative.toAdd x))) 0

/-- Paper: Lemma 2.3.2.1, p. 105. Pointwise differentiation along the
one-parameter subgroup gives a Schwartz–Bruhat function. -/
theorem sAdeleDirectionalDeriv_mem (f : ℬₛ) :
    orbitDeriv f ∈ schwartzBruhatSubmodule (Multiplicative Aₛ) := by sorry

/-- Paper: Lemma 2.3.2.1, p. 106. Taking the directional derivative
is complex linear on the S-local test space. -/
theorem sAdeleDirectionalDeriv_isLinear :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨orbitDeriv f, sAdeleDirectionalDeriv_mem F S γ f⟩ : ℬₛ)) :=
  by sorry

/-- Paper: Equation (2.3.2.1), p. 105. The directional derivative differentiates
the test function along the given one-parameter subgroup at the identity.
Deviation: As in the global definition, the derivative uses `t = exp s` at `s = 0`. -/
def sAdeleDirectionalDeriv : ℬₛ →ₗ[ℂ] ℬₛ :=
  IsLinearMap.mk' (fun f ↦ ⟨orbitDeriv f, sAdeleDirectionalDeriv_mem F S γ f⟩)
    (sAdeleDirectionalDeriv_isLinear F S γ)

/-- Paper: Lemma 2.3.2.1, p. 105. The difference quotient in the positive
real parameter converges to the S-adelic directional derivative. -/
theorem sAdeleDirectionalDeriv_tendsto (f : ℬₛ) (x : Aₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sAdeleDirectionalDeriv F S γ f (Multiplicative.ofAdd x))) := by sorry

/-- Paper: Lemma 2.3.2.1, p. 105. The directional derivative of a fixed
test function is continuous in the S-adele argument. -/
theorem sAdeleDirectionalDeriv_continuous_apply (f : ℬₛ) :
    Continuous (fun x : Aₛ ↦ sAdeleDirectionalDeriv F S γ f (Multiplicative.ofAdd x)) := by sorry

/-- Paper: Lemma 2.3.2.1, p. 106. The directional derivative is continuous
as an endomorphism of the S-local Schwartz–Bruhat space. -/
theorem sAdeleDirectionalDeriv_continuous :
    Continuous (sAdeleDirectionalDeriv F S γ) := by sorry

-- TODO(paper-gap): Equations (2.3.2.2)–(2.3.2.3) print τ(t) in both quotients.
-- For ℚ, S = {∞}, f(x) = exp(-x²), g = 1, and trivial γ, the τ derivative
-- of ordinary theta is -4/e, whereas the right side of (2.3.2.4) is zero.

/-- Paper: Proposition 2.3.2.2, p. 106. The directional difference quotient
of S-local theta converges to theta of the differentiated test function.
The limit is a continuous S-unit invariant function of the idele.
Deviation: Uses γ in (2.3.2.2), as specified by (2.3.2.4) and Lemma 2.3.2.1. -/
theorem sLocalAdelicTheta_directionalDeriv (f : ℬₛ) (g : Iₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (sLocalAdelicTheta F S f (γ t * g) - sLocalAdelicTheta F S f g) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sLocalAdelicTheta F S (sAdeleDirectionalDeriv F S γ f) g)) := by sorry

/-- Paper: Proposition 2.3.2.2, p. 106. The directional difference quotient
of homogeneous theta converges to homogeneous theta of the differentiated test
function. The limit is continuous on the S-idele classes.
Deviation: Uses γ in (2.3.2.3), as specified by (2.3.2.4) and Lemma 2.3.2.1. -/
theorem sLocalHomogeneousAdelicTheta_directionalDeriv
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm F S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (g : Iₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (sLocalHomogeneousAdelicTheta F S μ ω f (classOf (γ t * g)) -
        sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sLocalHomogeneousAdelicTheta F S μ ω (sAdeleDirectionalDeriv F S γ f) (classOf g))) :=
  by sorry

-- Remark 2.3.2.3, p. 106, defers the comparison with global theta to the
-- Mellin-transform constructions in Chapters 3–6.

end DirectionalDerivatives

end RiemannMasullo
