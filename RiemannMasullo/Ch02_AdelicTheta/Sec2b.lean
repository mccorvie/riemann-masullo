module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Directional derivatives and homogeneous adelic theta functions

Masullo, §§2.2.4–2.2.5, pp. 86–98.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped ContDiff Manifold NNReal NumberField.AdeleRing

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N₁[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "normℝ" => fun (g : C[F]) ↦ valueℝ (ideleClassNorm F g)
local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

section DirectionalDerivatives

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.1, p. 87. Every idele in a continuous one-parameter
subgroup has finite component one. -/
theorem adeleOneParameter_finite_eq_one (t : ℝ≥0ˣ) : (γ t).val.2 = 1 := by
  have : ConnectedSpace ℝ≥0ˣ :=
    (Nonneg.unitsHomeomorphPos ℝ).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp (isConnected_Ioi (a := (0 : ℝ))))
  have hVal : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val) :=
    Units.continuous_val.comp γ.continuous
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  have hCoord : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val.2 v) :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp hVal)
  calc
    (γ t).val.2 v = (γ 1).val.2 v :=
      TotallyDisconnectedSpace.eq_of_continuous _ hCoord t 1
    _ = (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v := by rw [map_one]; rfl

/-- Paper: Lemma 2.2.4.1, p. 87. The norm of a continuous one-parameter
subgroup is a power of its positive real parameter, with unique real exponent.
The norm-one case has exponent zero. -/
theorem adeleOneParameter_norm_rpow :
    ∃! α : ℝ, ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α := by sorry

/-- Paper: Lemma 2.2.4.1(1)–(2), p. 87. The norm of the subgroup is either
an automorphism smooth in both directions or identically one. Smoothness is
expressed in the logarithmic coordinate on the positive reals. -/
theorem adeleOneParameter_norm_cases :
    Xor
      (∃ e : ℝ≥0ˣ ≃ₜ* ℝ≥0ˣ, (∀ t, e t = ideleNorm F (γ t)) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ Real.log (valueℝ (e (expUnit s)))) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ Real.log (valueℝ (e.symm (expUnit s)))))
      (∀ t : ℝ≥0ˣ, ideleNorm F (γ t) = 1) := by sorry

local notation "orbitDeriv" => fun (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (f : ℬ[F]) (x : Multiplicative 𝔸[F]) ↦
  deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd (Units.val (γ (expUnit s)) * Multiplicative.toAdd x))) 0

/-- Paper: Lemma 2.2.4.2, p. 87. Differentiating the orbit curve pointwise in
the logarithmic parameter gives a Schwartz–Bruhat function. -/
theorem adeleDirectionalDeriv_mem (f : ℬ[F]) :
    orbitDeriv γ f ∈ schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by sorry

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative is
complex linear on the adelic Schwartz–Bruhat space. -/
theorem adeleDirectionalDeriv_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦
      (⟨orbitDeriv γ f, adeleDirectionalDeriv_mem γ f⟩ : ℬ[F])) := by sorry

/-- Paper: Equation (2.2.4.2), p. 87. The directional derivative differentiates
`f (γ(t) x)` at `t = 1` and is a complex-linear endomorphism.
Deviation: The definition uses the equivalent parameter `t = exp s` at `s = 0`,
as in (2.2.4.4). -/
def adeleDirectionalDeriv : ℬ[F] →ₗ[ℂ] ℬ[F] :=
  IsLinearMap.mk' _ (adeleDirectionalDeriv_isLinear γ)

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative
is continuous in the Schwartz–Bruhat topology. -/
theorem adeleDirectionalDeriv_continuous : Continuous (adeleDirectionalDeriv γ) := by sorry

/-- Paper: Lemma 2.2.4.2, p. 87. The difference quotient in the positive real
parameter converges to the directional derivative at every adele. -/
theorem adeleDirectionalDeriv_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (adeleDirectionalDeriv γ f (Multiplicative.ofAdd x))) :=
  by sorry

-- TODO(paper-gap): The last sentence of the proof of Lemma 2.2.4.2 uses
-- injectivity of γ∞. Lemma 2.2.4.1 only gives factorization through the infinite ideles.
-- TODO(paper-gap): The proof of Lemma 2.2.4.3 cites “Lemma ??” for closedness
-- of the section image and invokes the unrestricted bound from Lemma 2.2.2.1(3).

/-- Paper: Lemma 2.2.4.3, p. 88. The difference quotient of theta along the
projected one-parameter subgroup converges to theta of the directional derivative.
The limit is continuous since it is a global theta function. -/
theorem adelicTheta_directionalDeriv (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (adelicTheta f (classOf (γ t) * g) - adelicTheta f g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adelicTheta (adeleDirectionalDeriv γ f) g)) := by sorry

end DirectionalDerivatives

section PolarHyperplanes

/-- Paper: Definition 2.2.4.4, p. 91. The evaluations of a test function and
its Fourier transform at zero are complex linear. -/
theorem adelePolarValues_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦ (f zeroAdele, adeleSchwartzFourier f zeroAdele)) := by sorry

/-- Paper: Definition 2.2.4.4, p. 91. The two polar functionals are the
coordinates of the map that evaluates a test function and its transform at zero. -/
def adelePolarValues : ℬ[F] →ₗ[ℂ] ℂ × ℂ :=
  IsLinearMap.mk' _ (adelePolarValues_isLinear (F := F))

/-- Paper: Definition 2.2.4.4, p. 91. The polar functionals give the test
function and Fourier transform values at zero. -/
theorem adelePolarValues_apply (f : ℬ[F]) :
    adelePolarValues (F := F) f = (f zeroAdele, adeleSchwartzFourier f zeroAdele) := by sorry

/-- Paper: Definition 2.2.4.4, p. 91. The intersection of the global polar
hyperplanes is the common kernel of the two polar functionals. -/
def adelePolarSubspace (F : Type*) [Field F] [NumberField F] : Submodule ℂ ℬ[F] :=
  LinearMap.ker (adelePolarValues (F := F))

/-- Paper: Definition 2.2.4.4, p. 91. A function belongs to the polar
subspace exactly when both it and its Fourier transform vanish at zero. -/
theorem mem_adelePolarSubspace (f : ℬ[F]) :
    f ∈ adelePolarSubspace F ↔ f zeroAdele = 0 ∧ adeleSchwartzFourier f zeroAdele = 0 := by sorry

/-- Paper: Definition 2.2.4.4, p. 91. Both polar functionals are continuous,
expressed as continuity of the pair of evaluations. -/
theorem adelePolarValues_continuous : Continuous (adelePolarValues (F := F)) := by sorry

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.5(1), p. 91. The common polar kernel is closed in
the Schwartz–Bruhat topology. -/
theorem adelePolarSubspace_closed : IsClosed (adelePolarSubspace F : Set ℬ[F]) := by sorry

/-- Paper: Lemma 2.2.4.5(1), p. 91. Directional differentiation preserves the
common polar kernel, so it induces a linear map on the polar quotient. -/
theorem adeleDirectionalDeriv_preserves_polarSubspace :
    adelePolarSubspace F ≤ (adelePolarSubspace F).comap (adeleDirectionalDeriv γ) := by sorry

/-- Paper: Equation (2.2.4.25), p. 91. The two polar evaluations are jointly
surjective, so they identify the quotient by their common kernel with `ℂ × ℂ`. -/
theorem adelePolarValues_surjective : Surjective (adelePolarValues (F := F)) := by sorry

/-- Paper: Lemma 2.2.4.5(2), p. 91. In the two evaluation coordinates on
the quotient, the induced derivative has diagonal entries `0` and `-α`,
where `α` is the norm exponent of the subgroup. -/
theorem adeleDirectionalDeriv_polarQuotient_diagonal (α : ℝ)
    (hα : ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α) (z : ℂ × ℂ) :
    let T : (ℬ[F] ⧸ adelePolarSubspace F) ≃ₗ[ℂ] ℂ × ℂ :=
      (adelePolarValues (F := F)).quotKerEquivOfSurjective (adelePolarValues_surjective (F := F))
    let D : (ℬ[F] ⧸ adelePolarSubspace F) →ₗ[ℂ] ℬ[F] ⧸ adelePolarSubspace F :=
      (adelePolarSubspace F).mapQ (τ₁₂ := RingHom.id ℂ) (adelePolarSubspace F)
        (adeleDirectionalDeriv (F := F) γ) (adeleDirectionalDeriv_preserves_polarSubspace (F := F) γ)
    T.toFun (D.toFun (T.symm.toFun z)) = (0, (-α) • z.2) := by sorry

local instance adelicThetaAdeleMeasurableSpace : MeasurableSpace 𝔸[F] := borel _

/-- Paper: Lemma 2.2.4.5(3), p. 92. The difference quotient of the Fourier
transform under inverse dilation, weighted by the reciprocal norm, converges
pointwise to the Fourier transform of the directional derivative. -/
theorem adeleDirectionalDeriv_fourier_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      ((valueℝ (ideleNorm F (γ t)))⁻¹ •
          adeleSchwartzFourier f (Multiplicative.ofAdd (((γ t)⁻¹).val * x)) -
        adeleSchwartzFourier f (Multiplicative.ofAdd x)) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x))) :=
  by sorry

/-- Paper: Equation (2.2.4.30), p. 92. The Fourier transform of the derivative
uses the conjugate standard character and the real trace of the archimedean
velocity times the frequency and integration variable. The integrand is integrable.
Deviation: The velocity is expressed using the complex embeddings of the local
completions in the logarithmic parameter. The real trace counts complex places twice. -/
theorem adeleDirectionalDeriv_fourier_integral (f : ℬ[F]) (α : ℝ)
    (hα : ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α) :
    ∃ velocity : InfinitePlace F → ℂ,
      (∀ v, HasDerivAt (fun s : ℝ ↦
        InfinitePlace.Completion.extensionEmbedding v ((γ (expUnit s)).val.1 v))
        (velocity v) 0) ∧
      ∀ x : 𝔸[F],
        let integrand := fun y : 𝔸[F] ↦
          f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F (x * y) : ℂ) *
            (-(α : ℂ) + 2 * Real.pi * Complex.I *
              (∑ v : InfinitePlace F, (v.mult : ℝ) *
                (velocity v * InfinitePlace.Completion.extensionEmbedding v (x.1 v * y.1 v)).re : ℝ))
        Integrable integrand (additiveTamagawaMeasure F) ∧
          adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x) =
            ∫ y, integrand y ∂additiveTamagawaMeasure F := by sorry

-- TODO(paper-gap): On p. 92 the proof of Lemma 2.2.4.5 incorrectly drops
-- the norm factor at x = 0. The limit is -α * f̂(0), as in part (2).
-- The finite local factors of (2.2.4.32) also evaluate f_v at x_v under dν_v(y_v).

/-- Paper: Remark 2.2.4.6, p. 92. The norm-weighted inverse-dilation
quotients of the Fourier transforms converge in the Schwartz–Bruhat topology,
uniformly over every bounded set of inputs. -/
theorem adeleDirectionalDeriv_fourier_tendstoUniformlyOn (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun (t : ℝ≥0ˣ) (f : ℬ[F]) ↦
      (((valueℝ t : ℂ) - 1)⁻¹) •
        (((valueℝ (ideleNorm F (γ t)) : ℂ)⁻¹) •
          schwartzBruhatUnitTranslate (γ t) (adeleSchwartzFourier f) - adeleSchwartzFourier f))
      (fun f ↦ adeleSchwartzFourier (adeleDirectionalDeriv γ f)) (𝓝[≠] 1) B := by sorry

end PolarHyperplanes

section HomogeneousTheta

local instance adelicThetaIdeleMeasurableSpace : MeasurableSpace 𝕀[F] := borel _
local instance adelicThetaClassMeasurableSpace : MeasurableSpace C[F] := borel _

local notation "χ[" F "]" => PontryaginDual C₁[F]
local notation "μ₁" => normOneIdeleTamagawaMeasure F
local notation "μ̄₁" => normOneIdeleClassTamagawaMeasure F
local notation "classIntegrand" => fun (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) (h : C₁[F]) ↦
  adelicTheta f (Subtype.val h * g) * (ω₁ h : ℂ)

/-- Paper: Definition 2.2.5.1, p. 95. The character-weighted theta integrand
is integrable over the compact group of norm-one idele classes. -/
theorem homogeneousAdelicTheta_integrable (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) :
    Integrable (classIntegrand ω₁ f g) μ̄₁ := by sorry

/-- Paper: Lemma 2.2.5.2(2), p. 95. Averaging theta against the character on
the norm-one idele classes gives a continuous function of the ambient class. -/
theorem homogeneousAdelicTheta_continuous (ω₁ : χ[F]) (f : ℬ[F]) :
    Continuous (fun g ↦ ∫ h, classIntegrand ω₁ f g h ∂μ̄₁) := by sorry

/-- Paper: Definition 2.2.5.1, p. 95. Homogeneous theta is the integral of
theta at `h * g`, weighted by `ω₁ h` against norm-one class Haar measure. -/
def homogeneousAdelicTheta (ω₁ : χ[F]) (f : ℬ[F]) : C(C[F], ℂ) :=
  ⟨fun g ↦ ∫ h, classIntegrand ω₁ f g h ∂μ̄₁, homogeneousAdelicTheta_continuous ω₁ f⟩

/-- Paper: Definition 2.2.5.1, p. 95. For the trivial character and at the
identity class, homogeneous theta integrates theta over the norm-one classes. -/
theorem homogeneousAdelicTheta_trivial_at_one (f : ℬ[F]) :
    homogeneousAdelicTheta (1 : χ[F]) f 1 = ∫ h : C₁[F], adelicTheta f h.val ∂μ̄₁ := by sorry

/-- Paper: Definition 2.2.5.1, p. 95. Formation of homogeneous theta is
complex linear in the test function. -/
theorem homogeneousAdelicTheta_isLinear (ω₁ : χ[F]) :
    IsLinearMap ℂ (homogeneousAdelicTheta ω₁) := by sorry

local notation "classOfNormOne" => fun h : N₁[F] ↦
  (Subtype.mk (classOf (Subtype.val h)) (Subtype.property h) : C₁[F])
local notation "ideleIntegrand" => fun (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) (h : N₁[F]) ↦
  f (Multiplicative.ofAdd (Units.val (Subtype.val h * g))) * (ω₁ (classOfNormOne h) : ℂ)

/-- Paper: Lemma 2.2.5.2(1), p. 95. The integral of the adelic test function
against the character pulled back from the norm-one classes converges absolutely
on norm-one ideles. -/
theorem homogeneousAdelicTheta_idele_integrable (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    Integrable (ideleIntegrand ω₁ f g) μ₁ := by sorry

/-- Paper: Lemma 2.2.5.2(1), p. 95. The norm-one idele integral against the
pulled-back character is continuous in the ambient idele. -/
theorem homogeneousAdelicTheta_idele_continuous (ω₁ : χ[F]) (f : ℬ[F]) :
    Continuous (fun g ↦ ∫ h, ideleIntegrand ω₁ f g h ∂μ₁) := by sorry

/-- Paper: Lemma 2.2.5.2(1), p. 95. Inverse translation of the ambient
idele by a norm-one idele multiplies the integral by the pulled-back character. -/
theorem homogeneousAdelicTheta_idele_homogeneous (ω₁ : χ[F]) (f : ℬ[F])
    (h₀ : N₁[F]) (g : 𝕀[F]) :
    (∫ h, ideleIntegrand ω₁ f (h₀.val⁻¹ * g) h ∂μ₁) =
      (ω₁ (classOfNormOne h₀) : ℂ) * ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ := by sorry

/-- Paper: Lemma 2.2.5.2(2), p. 95. At an idele representative, homogeneous
theta equals the test-function integral over the norm-one ideles. -/
theorem homogeneousAdelicTheta_eq_idele_integral (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    homogeneousAdelicTheta ω₁ f (classOf g) = ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ := by sorry

-- TODO(paper-gap): The paragraph on p. 96 describes h⁻¹ * g inside (2.2.5.2),
-- while the displayed integral and the equivariance computation on p. 97 use h * g.
-- Bound (2.2.5.5) reuses the unrestricted estimate flagged in §2.2.2.1(3).
-- TODO(later): needs §4.3.3 for the general construction cited by Remark 2.2.5.3.

/-- Paper: Theorem 2.2.5.4(1), p. 97. Inverse translation of a class by a
norm-one class acts on homogeneous theta by the prescribed character. -/
theorem homogeneousAdelicTheta_homogeneous (ω₁ : χ[F]) (f : ℬ[F]) (h : C₁[F]) (g : C[F]) :
    homogeneousAdelicTheta ω₁ f (h.val⁻¹ * g) = (ω₁ h : ℂ) * homogeneousAdelicTheta ω₁ f g :=
  by sorry

/-- Paper: Theorem 2.2.5.4(2), p. 97. At large norm, homogeneous theta decays
faster than every inverse power of the norm. -/
theorem homogeneousAdelicTheta_decay_large (ω₁ : χ[F]) (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < normℝ g →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

open scoped Classical in
/-- Paper: Equation (2.2.5.10), p. 97. The polar term is the norm-one class
volume times the difference of the two polar evaluations with reciprocal norm
on the Fourier value. It contributes only for the trivial character. -/
def homogeneousAdelicTheta_polarTerm (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) : ℂ :=
  if ω₁ = 1 then (μ̄₁ univ).toReal •
    ((normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele) else 0

/-- Paper: Equation (2.2.5.10), p. 97. At norm one and for the trivial
character the polar term is the class volume times the difference of the evaluations. -/
theorem homogeneousAdelicTheta_polarTerm_trivial_at_one (f : ℬ[F]) :
    homogeneousAdelicTheta_polarTerm (1 : χ[F]) f 1 =
      (μ̄₁ univ).toReal • (adeleSchwartzFourier f zeroAdele - f zeroAdele) := by sorry

/-- Paper: Theorem 2.2.5.4(2), p. 97. After subtracting the polar term,
homogeneous theta decays faster than every power of the norm at small norm. -/
theorem homogeneousAdelicTheta_decay_small (ω₁ : χ[F]) (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], normℝ g < T →
      ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
        C * (normℝ g) ^ N := by sorry

/-- Paper: Theorem 2.2.5.4(3), p. 97. Homogeneous theta commutes with
directional differentiation. The difference quotient tends to homogeneous theta
of the differentiated test function. -/
theorem homogeneousAdelicTheta_directionalDeriv (γ : ℝ≥0ˣ →ₜ* 𝕀[F])
    (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (homogeneousAdelicTheta ω₁ f (classOf (γ t) * g) - homogeneousAdelicTheta ω₁ f g) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (homogeneousAdelicTheta ω₁ (adeleDirectionalDeriv γ f) g)) :=
  by sorry

open scoped Classical in
set_option maxSynthPendingDepth 8 in
/-- Paper: Theorem 2.2.5.4(3), p. 98. With the finite component fixed,
homogeneous theta on ideles is smooth in the archimedean units. The charts
are the units charts in the real and complex completion coordinates. -/
theorem homogeneousAdelicTheta_archimedean_smooth (ω₁ : χ[F]) (f : ℬ[F])
    (g : 𝔸ᶠ[F]ˣ) :
    let e := Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
    ContMDiff 𝓘(ℝ, mixedEmbedding.mixedSpace F) 𝓘(ℝ, ℂ) (∞ : ℕ∞ω)
      (fun a : (mixedEmbedding.mixedSpace F)ˣ ↦
        homogeneousAdelicTheta ω₁ f (classOf
          ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) 𝔸ᶠ[F]).symm
            (e.symm a, g)))) := by sorry

-- TODO(paper-gap): The proof of Theorem 2.2.5.4(3) repeats the same term in
-- (2.2.5.13), then uses γ(t⁻¹) with the sign for γ(t) in (2.2.5.15).

/-- Paper: Theorem 2.2.5.4(4), p. 98. For a test function in the polar
subspace or a nontrivial character, homogeneous theta decays at both ends
at every exponential rate in the absolute logarithmic norm. -/
theorem homogeneousAdelicTheta_decay_both (ω₁ : χ[F]) (f : ℬ[F])
    (h : f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < |Real.log (normℝ g)| →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by sorry

-- TODO(paper-gap): The last sentence of Theorem 2.2.5.4(4) uses the
-- conjugate of ω to descend to the logarithmic norm. Even after choosing a
-- character extension, this transforms by ω(h)⁻² under translation by h.

-- TODO(paper-gap): Theorem 2.2.5.4(5) cites (2.2.5.11) among the estimates
-- with a constant and a threshold, although it is an identity valid everywhere.

/-- Paper: Theorem 2.2.5.4(5), p. 98. The large-norm, small-norm and two-sided
estimates have a common constant and logarithmic threshold uniform over a
bounded set of test functions. The two-sided bound retains the condition in (4). -/
theorem homogeneousAdelicTheta_decay_bounded (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C[F],
      (T < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (T < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → T < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) :=
  by sorry

/-- Paper: Theorem 2.2.5.4(6), p. 98. The three uniform estimates hold with
logarithmic threshold one and a common constant. -/
theorem homogeneousAdelicTheta_decay_bounded_threshold_one (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (1 < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → 1 < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) :=
  by sorry

end HomogeneousTheta

end RiemannMasullo
