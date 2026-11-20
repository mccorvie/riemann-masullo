module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Strong continuity and the Hilbert-space isotypic transform -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function MeasureTheory Set TopologicalSpace
open scoped CompactlySupported ENNReal InnerProductSpace NNReal

section Regular

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Paper: Definition 4.3.1.1, p. 175. The space of the regular representation
is complex Haar L².
Deviation: Mathlib's inner product is conjugate-linear in the first slot.
The paper uses the swapped order, as made explicit in `regularL2_inner`. -/
abbrev RegularL2 (ν : Measure G) := Lp ℂ 2 ν

/-- Paper: Definition 4.3.1.1, p. 175. Swapping the arguments of Mathlib's inner
product gives the integral of the first function times the conjugate of the second. -/
theorem regularL2_inner (ν : Measure G) (f h : RegularL2 ν) :
    ⟪h, f⟫_ℂ = ∫ x, f x * star (h x) ∂ν := by sorry

variable (ν : Measure G) [hν : ν.IsHaarMeasure]

include hν

/-- Paper: Lemma 4.3.1.3, p. 175. Haar measure is regular. -/
theorem regularL2_haar_regular : ν.Regular := by sorry

/-- Paper: Lemma 4.3.1.3, p. 175. Haar measure is Radon, expressed by inner
regularity by compact sets together with finiteness on compact sets. -/
theorem regularL2_haar_radon : ν.InnerRegular ∧ IsFiniteMeasureOnCompacts ν := by sorry

/-- Paper: Lemma 4.3.1.3, p. 175. Haar measure on the second-countable group is
sigma-finite. -/
theorem regularL2_haar_sigmaFinite : SigmaFinite ν := by sorry

/-- Paper: Remark 4.3.1.4, p. 175. A continuous compactly supported function
is square-integrable. -/
theorem regularL2_memLp_compactlySupported (f : G →C_c ℂ) :
    MemLp (f : G → ℂ) 2 ν := by sorry

/-- Paper: Remark 4.3.1.4, p. 175. Classes of continuous compactly
supported functions are dense in Haar L². -/
theorem regularL2_compactlySupported_dense :
    DenseRange (fun f : G →C_c ℂ ↦ (regularL2_memLp_compactlySupported ν f).toLp f) := by sorry

/-- Paper: Lemma 4.3.1.5(1), p. 176. The Haar L² space is separable. -/
theorem regularL2_separable : SeparableSpace (RegularL2 ν) := by sorry

/-- Paper: (4.3.1.4), p. 175. Left translation on Haar L² precomposes with
multiplication by the inverse group element. -/
def regularTranslate (g : G) (f : RegularL2 ν) : RegularL2 ν :=
  DomMulAct.mk g⁻¹ • f

/-- Paper: (4.3.1.4), p. 175. Left translation has the stated representative
almost everywhere. -/
theorem regularTranslate_ae_eq (g : G) (f : RegularL2 ν) :
    (regularTranslate ν g f : G → ℂ) =ᵐ[ν] fun x ↦ f (g⁻¹ * x) := by sorry

/-- Paper: Lemma 4.3.1.5(2), p. 176. Translation extends to a unique strongly
continuous linear action on Haar L². Its values on compactly supported
continuous functions agree almost everywhere with the original formula. -/
theorem existsUnique_regularL2_action :
    ∃! ρ : G →* (RegularL2 ν →L[ℂ] RegularL2 ν),
      (∀ f : RegularL2 ν, Continuous fun g ↦ ρ g f) ∧
      ∀ (g : G) (f : G →C_c ℂ),
        (ρ g ((regularL2_memLp_compactlySupported ν f).toLp f) : G → ℂ)
          =ᵐ[ν] fun x ↦ f (g⁻¹ * x) := by sorry

/-- Paper: Lemma 4.3.1.5(2), p. 176. The regular representation uses the unique
strongly continuous extension of translation from compactly supported functions. -/
def regularL2Action : G →* (RegularL2 ν →L[ℂ] RegularL2 ν) :=
  Classical.choose (existsUnique_regularL2_action ν).exists

/-- Paper: Lemma 4.3.1.5(2), p. 176. The extended action agrees with
measure-preserving precomposition on every L² class. -/
theorem regularL2Action_apply (g : G) (f : RegularL2 ν) :
    regularL2Action ν g f = regularTranslate ν g f := by sorry

/-- Paper: Lemma 4.3.1.5(2), p. 176. Left translations preserve the
Hermitian inner product and their inverses are the opposite translations. -/
theorem regularL2Action_inner (g : G) (f h : RegularL2 ν) :
    ⟪regularL2Action ν g f, regularL2Action ν g h⟫_ℂ = ⟪f, h⟫_ℂ := by sorry

/-- Paper: Lemma 4.3.1.5(3), p. 176. Composing the regular representation
with a continuous section of the module gives a strongly continuous
one-parameter group of unitary operators. -/
theorem regularL2Action_section (m : G →ₜ* ℝ≥0ˣ) (_hm : IsModulation m)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m) :
    (∀ f : RegularL2 ν, Continuous fun t ↦ ((regularL2Action ν).comp τ.toMonoidHom) t f) ∧
    ∀ (t : ℝ≥0ˣ) (f h : RegularL2 ν),
      ⟪regularL2Action ν (τ t) f, regularL2Action ν (τ t) h⟫_ℂ = ⟪f, h⟫_ℂ := by sorry

end Regular

section Transform

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (ν : Measure G) [hν : ν.IsHaarMeasure]
  (ν₁ : Measure m.toMonoidHom.ker) [hν₁ : ν₁.IsHaarMeasure]

include hm hν hν₁

local notation "K" => m.toMonoidHom.ker

-- TODO(paper-gap): The Tamagawa measure reference after (4.3.2.1) is printed
-- as “Definition ??”. The statements use specified Haar measures instead.

/-- Paper: (4.3.2.1), p. 178. The character-weighted translate of an L²
representative is integrable on almost every norm-one fiber. -/
theorem regularIsotypic_ae_integrable (ω : PontryaginDual K) (f : RegularL2 ν) :
    ∀ᵐ x ∂ν, Integrable (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * x)) ν₁ := by sorry

/-- Paper: (4.3.2.1), p. 178. Fiber averaging defines a continuous linear
operator on Haar L² with its stated almost-everywhere formula. -/
theorem existsUnique_regularIsotypicIntegral (ω : PontryaginDual K) :
    ∃! P : RegularL2 ν →L[ℂ] RegularL2 ν, ∀ f : RegularL2 ν,
      (P f : G → ℂ) =ᵐ[ν] fun x ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * x) ∂ν₁ := by sorry

/-- Paper: (4.3.2.1), p. 178. The unnormalized L² isotypic operator is
the continuous linear map given almost everywhere by integration over the kernel. -/
def regularIsotypicIntegral (ω : PontryaginDual K) : RegularL2 ν →L[ℂ] RegularL2 ν :=
  Classical.choose (existsUnique_regularIsotypicIntegral m hm ν ν₁ ω).exists

/-- Paper: (4.3.2.1), p. 178. The L² average agrees almost everywhere with
the integral using positive translation and the unconjugated character. -/
theorem regularIsotypicIntegral_ae_eq (ω : PontryaginDual K) (f : RegularL2 ν) :
    (regularIsotypicIntegral m hm ν ν₁ ω f : G → ℂ) =ᵐ[ν]
      fun x ↦ ∫ k : K, (ω k : ℂ) * f ((k : G) * x) ∂ν₁ := by sorry

variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

include hτ

/-- Paper: (4.3.2.4), p. 178. Integration on the fibers parametrized by a
section is defined almost everywhere and gives an L² function for `dt/t`.
Deviation: We use fiber integration of a representative to define the
operator, since the restriction of an arbitrary L² class to the section
is undefined. -/
theorem regularIsotypicComponent_memLp (ω : PontryaginDual K) (f : RegularL2 ν) :
    (∀ᵐ t ∂positiveRealHaar,
      Integrable (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * τ t)) ν₁) ∧
    MemLp (fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁)
      2 positiveRealHaar := by sorry

/-- Paper: (4.3.2.4), p. 178. The section gives the `dt/t` L² coordinate
of the unnormalized character average.
Deviation: The fiber integral is formed before passing to the L² class. -/
def regularIsotypicComponent (ω : PontryaginDual K) (f : RegularL2 ν) :
    RegularL2 positiveRealHaar :=
  (regularIsotypicComponent_memLp m hm ν ν₁ τ hτ ω f).2.toLp
    (fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁)

/-- Paper: (4.3.2.4), p. 178. Translation by a norm-one element acts on the
corresponding transformed coordinate by the character. -/
theorem regularIsotypicComponent_equivariant (ω : PontryaginDual K) (k : K) (f : RegularL2 ν) :
    regularIsotypicComponent m hm ν ν₁ τ hτ ω (regularTranslate ν (k : G) f) =
      (ω k : ℂ) • regularIsotypicComponent m hm ν ν₁ τ hτ ω f := by sorry

-- TODO(paper-gap): (4.3.2.3) evaluates ω on G before choosing its extension
-- from G¹. The section gives an extension trivial on its image.
-- TODO(paper-gap): (4.3.2.5) needs measure normalization. For G = ℝ>0,
-- ν = dt/t and ν₁ = 2 δ₁, the only component is multiplication by 2.

/-- Paper: (4.3.2.7), p. 178. The family of all coordinates belongs to the
Hilbert direct sum. -/
theorem regularIsotypicTransform_memℓp (f : RegularL2 ν) :
    Memℓp (fun ω : PontryaginDual K ↦ regularIsotypicComponent m hm ν ν₁ τ hτ ω f) 2 := by sorry

/-- Paper: (4.3.2.7), p. 178. The transform takes all the character
coordinates together in the Hilbert direct sum. -/
def regularIsotypicTransform (f : RegularL2 ν) :
    lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2 :=
  ⟨fun ω ↦ regularIsotypicComponent m hm ν ν₁ τ hτ ω f,
    regularIsotypicTransform_memℓp m hm ν ν₁ τ hτ f⟩

/-- Paper: (4.3.2.7), p. 178. The coordinate indexed by a character is the
almost-everywhere integral with that character's conjugate. -/
theorem regularIsotypicTransform_ae_eq (ω : PontryaginDual K) (f : RegularL2 ν) :
    (regularIsotypicTransform m hm ν ν₁ τ hτ f ω : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar]
      fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁ := by sorry

/-- Paper: (4.3.2.7), p. 178. The transform is linear and continuous
for the Hilbert direct sum topology. -/
theorem regularIsotypicTransform_continuousLinear :
    ∃ T : RegularL2 ν →L[ℂ] lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2,
      ∀ f : RegularL2 ν, T f = regularIsotypicTransform m hm ν ν₁ τ hτ f := by sorry

/-- Paper: Lemma 4.3.2.2, p. 179. Every square-summable family of L²
coordinates is in the range of the transform. -/
theorem regularIsotypicTransform_surjective :
    Surjective (regularIsotypicTransform m hm ν ν₁ τ hτ) := by sorry

-- TODO(paper-gap): Lemma 4.3.2.2's isometry and the isometry asserted on
-- p. 180 fail for the same measure rescaling as (4.3.2.5).

end Transform

end RiemannMasullo
