module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation

/-!
# Fourier analysis and Schwartz spaces of elementary abelian Lie groups

Masullo, §§D.1.1–D.1.3, pp. 745–757.
-/

@[expose] public noncomputable section

open Bornology Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal TensorProduct Topology ZeroAtInfty

namespace RiemannMasullo

section Pontryagin

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.1.1(1), p. 746. The Pontryagin dual is Hausdorff and locally compact.
Mathlib supplies its abelian topological group structure and precomposition functor
`PontryaginDual.map`, with `PontryaginDual.map_one` and `PontryaginDual.map_comp`. -/
theorem pontryaginDual_basic : T2Space (PontryaginDual G) ∧
    LocallyCompactSpace (PontryaginDual G) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Paper: Theorem D.1.1.1(2), p. 746. Characters separate points of the group, and
evaluation separates characters. -/
theorem pontryaginDual_pairing_separates :
    Function.Injective (fun (x : G) (χ : PontryaginDual G) ↦ χ x) ∧
    Function.Injective (fun (χ : PontryaginDual G) (x : G) ↦ χ x) := by
  constructor
  · intro x y h
    by_contra hxy
    obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr hxy)
    exact hχ (by simp [map_div, congrFun h χ])
  · intro χ ψ h
    exact PontryaginDual.ext (congrFun h)

/-- Paper: Theorem D.1.1.1(2), p. 746. Evaluation gives the canonical topological
group isomorphism with the double dual. -/
theorem pontryaginDual_bidual :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),
      ∀ x χ, e x χ = χ x := by sorry

/-- Paper: Theorem D.1.1.1(3), p. 746. A locally compact abelian group is compact
exactly when its dual is discrete. -/
theorem compactSpace_iff_discretePontryaginDual :
    CompactSpace G ↔ DiscreteTopology (PontryaginDual G) := by sorry

end Pontryagin

section Fourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

local instance : MeasurableSpace (PontryaginDual G) := borel _

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Paper: (D.1.1.4), p. 746. Evaluate the Fourier transform by integrating against
the complex conjugate of a character. -/
def lcaFourier (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ x, f x * star (χ x : ℂ) ∂μ

/-- Paper: (D.1.1.4), p. 746. At the trivial character the transform is the integral
of the original function. -/
theorem lcaFourier_one (f : G → ℂ) (hf : Integrable f μ) :
    lcaFourier μ f 1 = ∫ x, f x ∂μ := by sorry

/-- Paper: (D.1.1.5), p. 746. Multiplicative convolution integrates the product with
the left translate of the second function. -/
def lcaConvolution (μ : Measure G) (f g : G → ℂ) (x : G) : ℂ :=
  ∫ y, f y * g (y⁻¹ * x) ∂μ

/-- Paper: (D.1.1.5), p. 746. Convolution on a one-point group is multiplication
scaled by its total Haar mass. -/
theorem lcaConvolution_subsingleton [Subsingleton G] (f g : G → ℂ) (x : G) :
    lcaConvolution μ f g x = (μ univ).toReal * f x * g x := by sorry

/-- Paper: (D.1.1.5)–(D.1.1.6), p. 746. The fibre integrals of two L¹ functions
exist almost everywhere and their convolution is L¹ with the product norm bound. -/
theorem lcaConvolution_integrable {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      Integrable (lcaConvolution μ f g) μ ∧
      eLpNorm (lcaConvolution μ f g) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := by sorry

/-- Paper: Lemma D.1.1.2(1), p. 746. The Fourier transform of an L¹ function
is continuous and vanishes at infinity on the dual group. -/
theorem lcaFourier_zeroAtInfty {f : G → ℂ} (hf : Integrable f μ) :
    ∃ F : C₀(PontryaginDual G, ℂ), ∀ χ, F χ = lcaFourier μ f χ := by sorry

/-- Paper: Lemma D.1.1.2(2), p. 746. The integral formula gives an injective
complex-linear map on L¹ equivalence classes with operator norm at most one. -/
theorem lcaFourier_L1 :
    ∃ F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ),
      (∀ f χ, F f χ = lcaFourier μ (f : G → ℂ) χ) ∧
      Function.Injective F ∧ ∀ f, ‖F f‖ ≤ ‖f‖ := by sorry

/-- Paper: Lemma D.1.1.2(3), p. 747. The fibre integrals of two L² functions
exist everywhere and give a continuous function vanishing at infinity with the product norm bound. -/
theorem lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      ∃ F : C₀(G, ℂ), (∀ x, F x = lcaConvolution μ f g x) ∧
        ‖F‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by sorry

/-- Paper: Lemma D.1.1.2(4), p. 747. A Plancherel measure is a regular Haar measure
on the dual for which the Fourier transform preserves the finite L² norm on L¹ ∩ L². -/
def IsLCAPlancherelMeasure (μ : Measure G) (ν : Measure (PontryaginDual G)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ (f : G → ℂ), Integrable f μ → MemLp f 2 μ →
      MemLp (lcaFourier μ f) 2 ν ∧ eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ

/-- Paper: Lemma D.1.1.2(4), p. 747. On the one-point group the two
total masses must be reciprocals. -/
theorem isLCAPlancherelMeasure_subsingleton [Subsingleton G]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular] :
    IsLCAPlancherelMeasure μ ν ↔ ν univ = (μ univ)⁻¹ := by sorry

/-- Paper: Lemma D.1.1.2(4), p. 747. There is exactly one Plancherel measure. -/
theorem lcaPlancherelMeasure_existsUnique :
    ∃! ν : Measure (PontryaginDual G), IsLCAPlancherelMeasure μ ν := by sorry

/-- Paper: Lemma D.1.1.2(4), p. 747. The Fourier transform on L¹ ∩ L²
extends uniquely to a unitary isomorphism on L². -/
theorem lcaFourier_unitary (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) :
    ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
      ∀ (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ),
        (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by sorry

-- TODO(paper-gap): Lemma D.1.1.2(5) asserts continuity and pointwise inversion for an
-- arbitrary measurable representative. A nonzero function supported at one point of
-- the real line has zero transform, and its double transform is everywhere zero.

/-- Paper: Lemma D.1.1.2(6), p. 747. The Fourier transform takes L¹ convolution
to pointwise multiplication on the dual. -/
theorem lcaFourier_convolution {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    lcaFourier μ (lcaConvolution μ f g) = lcaFourier μ f * lcaFourier μ g := by sorry

end Fourier

section Weil

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

local instance : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: (D.1.2.1), p. 747. Integrate over the translate of the subgroup represented
by a quotient point. The representative is chosen by `Quotient.out`. -/
def lcaCosetIntegral (μH : Measure H) (f : G → ℂ) (q : G ⧸ H) : ℂ :=
  ∫ h : H, f (q.out * (h : G)) ∂μH

/-- Paper: (D.1.2.1), p. 747. If the fibre is integrable at a representative,
the quotient integral agrees with integration using that representative. -/
theorem lcaCosetIntegral_mk (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G)
    (hf : Integrable (fun h : H ↦ f (x * (h : G))) μH) :
    lcaCosetIntegral H μH f (QuotientGroup.mk x) =
      ∫ h : H, f (x * (h : G)) ∂μH := by sorry

/-- Paper: Theorem D.1.2.1, p. 747. A regular Haar measure on the quotient
is normalized by Weil's formula on continuous compactly supported test functions. -/
def IsWeilQuotientMeasure (μ : Measure G) (μH : Measure H) (ν : Measure (G ⧸ H)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν

/-- Paper: Theorem D.1.2.1, p. 747. Taking the quotient by the trivial
subgroup, normalized to mass one, recovers the pushforward of the group measure. -/
theorem isWeilQuotientMeasure_bot (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    IsWeilQuotientMeasure (⊥ : Subgroup G) μ Measure.count
      (μ.map (QuotientGroup.mk : G → G ⧸ (⊥ : Subgroup G))) := by sorry

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]

include hH in
/-- Paper: Theorem D.1.2.1, p. 747. There is a unique quotient Haar measure
satisfying Weil's formula for compactly supported continuous functions. -/
theorem weilQuotientMeasure_existsUnique :
    ∃! ν : Measure (G ⧸ H), IsWeilQuotientMeasure H μ μH ν := by sorry

-- TODO(paper-gap): Theorem D.1.2.1 also asserts a.e. existence of the fibre integral
-- for every measurable function. For H = G = ℝ and f = 1, the sole fibre has infinite integral.

include hH in
/-- Paper: Theorem D.1.2.1, p. 747. For an L¹ function the fibre
integrals exist quotient-almost everywhere, define an L¹ function and satisfy Weil's formula. -/
theorem weilQuotientIntegral_L1 (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ μH ν)
    {f : G → ℂ} (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H ↦ f (q.out * (h : G))) μH) ∧
      Integrable (lcaCosetIntegral H μH f) ν ∧
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by sorry

include hH in
/-- Paper: Lemma D.1.2.3, p. 747. For a σ-finite group, finiteness of
the iterated integral of the norm implies integrability and Weil's formula. -/
theorem integrable_of_weilNormIntegral [SigmaFinite μ] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {f : G → ℂ} (hf : Measurable f)
    (hfin : (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖₊ ∂μH ∂ν) < (⊤ : ℝ≥0∞)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by sorry

section FundamentalDomain

variable [DiscreteTopology H] [SecondCountableTopology G]
variable {Δ Δ' : Set G} (hΔ : MeasurableSet Δ)
variable (hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)))

include hH hΔ hbij in
/-- Paper: Proposition D.1.2.4, p. 748. The integrals over the translates
of a Borel fundamental domain sum absolutely to the group integral. -/
theorem weilFundamentalDomain_hasSum {f : G → ℂ} (hf : Integrable f μ) :
    HasSum (fun h : H ↦ ∫ x in (fun y : G ↦ y * (h : G)) '' Δ, f x ∂μ)
      (∫ x, f x ∂μ) := by sorry

variable (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ Measure.count ν)

include hH hΔ hbij hν in
/-- Paper: Proposition D.1.2.4, p. 748. Borel measurability on the quotient
can be tested on the pullback restricted to a Borel fundamental domain. -/
theorem weilFundamentalDomain_measurable_iff (f : G ⧸ H → ℂ) :
    Measurable f ↔ Measurable (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) := by sorry

include hH hΔ hbij hν in
/-- Paper: Proposition D.1.2.4, p. 748. Integrability on the quotient
can be tested on the pullback restricted to a Borel fundamental domain. -/
theorem weilFundamentalDomain_integrable_iff (f : G ⧸ H → ℂ) :
    Integrable f ν ↔ Integrable (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) μ := by sorry

include hH hΔ hbij hν in
/-- Paper: Proposition D.1.2.4, p. 748. The integral on the quotient
equals the integral of its pullback over a Borel fundamental domain. -/
theorem weilFundamentalDomain_integral {f : G ⧸ H → ℂ} (hf : Integrable f ν) :
    (∫ q, f q ∂ν) = ∫ x in Δ, f (QuotientGroup.mk x) ∂μ := by sorry

include hH hΔ hbij in
/-- Paper: Corollary D.1.2.5, p. 748. The integral of a subgroup-invariant function
over one Borel fundamental domain agrees with its integral over any other such domain. -/
theorem weilFundamentalDomain_integral_eq (hΔ' : MeasurableSet Δ')
    (hbij' : Function.Bijective (fun x : Δ' ↦ (QuotientGroup.mk x.val : G ⧸ H)))
    {f : G → ℂ} (hf : Measurable f) (hinv : ∀ (x : G) (h : H), f (x * (h : G)) = f x)
    (hint : IntegrableOn f Δ μ) :
    IntegrableOn f Δ' μ ∧ (∫ x in Δ, f x ∂μ) = ∫ x in Δ', f x ∂μ := by sorry

end FundamentalDomain

-- TODO(later): needs §D.1.4 (Definition D.1.4.5 and Lemma D.1.4.6) for the
-- annihilator and its canonical identification with the quotient dual in
-- Situation D.1.2.6, Theorem D.1.2.7 and Remark D.1.2.8.

end Weil

section Elementary

/-- Paper: (D.1.3.1), p. 749. The elementary group has real, torus, integer
and finite factors.
Deviation: The whole group is written additively, with `AddCircle 1` for ℝ/ℤ. -/
abbrev ElementaryLieGroup (m n r : ℕ) (F : Type*) :=
  EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × F

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

/-- Paper: (D.1.3.2), p. 749. The covering map reduces each real torus coordinate
modulo the integer lattice and leaves the other coordinates fixed. -/
def elementaryCover (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a : Fin r → ℤ) (b : F) : ElementaryLieGroup m n r F :=
  (xt.1, fun i ↦ (xt.2 i : AddCircle (1 : ℝ)), a, b)

/-- Paper: (D.1.3.1)–(D.1.3.2), p. 749. Every group element has a lift
for its real and torus coordinates. -/
theorem elementaryCover_surjective (a : Fin r → ℤ) (b : F)
    (x : EuclideanSpace ℝ (Fin m)) (z : Fin n → AddCircle (1 : ℝ)) :
    ∃ t : EuclideanSpace ℝ (Fin n), elementaryCover (x, t) a b = (x, z, a, b) := by sorry

/-- Paper: (D.1.3.3), p. 749. The mixed partial is evaluated on the cover by
repeating differentiation along each coordinate vector according to its exponent. -/
def elementaryPartial (f : ElementaryLieGroup m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) : ℂ :=
  let realDirections : List (List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    List.ofFn (fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))
  let torusDirections : List (List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    List.ofFn (fun i : Fin n ↦ List.replicate (γ i) (0, EuclideanSpace.single i 1))
  let directions : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    realDirections.flatten ++ torusDirections.flatten
  iteratedFDeriv ℝ directions.length (fun v ↦ f (elementaryCover v a b)) xt directions.get

/-- Paper: (D.1.3.3), p. 749. With both multi-indices zero, the partial is just the
pullback of the function to the cover. -/
theorem elementaryPartial_zero (f : ElementaryLieGroup m n r F → ℂ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial f 0 0 xt a b = f (elementaryCover xt a b) := by sorry

/-- Paper: (D.1.3.4), p. 750. The lifted partials of a smooth fibre are smooth
and have the same value at any two lifts of a given group point. -/
theorem elementaryPartial_descends (f : ElementaryLieGroup m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) :
    ContDiff ℝ ∞ (fun xt ↦ elementaryPartial f β γ xt a b) ∧
      ∀ u v, elementaryCover u a b = elementaryCover v a b →
        elementaryPartial f β γ u a b = elementaryPartial f β γ v a b := by sorry

/-- Paper: (D.1.3.7), p. 750. These are the two monomial multi-indices and the
two derivative multi-indices in the paper's order. -/
abbrev ElementarySchwartzIndex (m n r : ℕ) :=
  (Fin m → ℕ) × (Fin m → ℕ) × (Fin n → ℕ) × (Fin r → ℕ)

/-- Paper: (D.1.3.6)–(D.1.3.7), p. 750. Take the supremum of the absolute value
of a mixed partial multiplied by the real and integer monomials.
Deviation: The supremum ranges over all lifts of the torus coordinates. -/
def elementarySchwartzBound (f : ElementaryLieGroup m n r F → ℂ)
    (i : ElementarySchwartzIndex m n r) : ℝ≥0∞ :=
  ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
    ((‖((∏ k, (xt.1 k : ℂ) ^ i.1 k) * (∏ k, (a k : ℂ) ^ i.2.2.2 k)) *
      elementaryPartial f i.2.1 i.2.2.1 xt a b‖₊ : ℝ≥0∞))

/-- Paper: (D.1.3.7), p. 750. With every index zero the bound is the supremum
of the absolute value of the original function. -/
theorem elementarySchwartzBound_zero (f : ElementaryLieGroup m n r F → ℂ) :
    elementarySchwartzBound f (0, 0, 0, 0) =
      ⨆ g, (‖f g‖₊ : ℝ≥0∞) := by sorry

section

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Paper: Definition D.1.3.1, p. 750. The zero function is smooth on each
discrete fibre and has finite weighted bounds. -/
theorem elementarySchwartzSubmodule_zero_mem :
    (0 : ElementaryLieGroup m n r F → ℂ) ∈
      {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
        ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)} := by sorry

/-- Paper: Definition D.1.3.1, p. 750. The Schwartz condition is closed under addition. -/
theorem elementarySchwartzSubmodule_add_mem {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞))
    (hg : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) :
    f + g ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by sorry

/-- Paper: Definition D.1.3.1, p. 750. The Schwartz condition is closed under
complex scalar multiplication. -/
theorem elementarySchwartzSubmodule_smul_mem (c : ℂ) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)) :
    c • f ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by sorry

/-- Paper: Definition D.1.3.1, p. 750. A Schwartz function is smooth in the real
and torus variables on each discrete fibre and has finite bounds for all four multi-indices. -/
def elementarySchwartzSubmodule (m n r : ℕ) (F : Type*) :
    Submodule ℂ (ElementaryLieGroup m n r F → ℂ) where
  carrier := {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
    ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)}
  zero_mem' := elementarySchwartzSubmodule_zero_mem
  add_mem' := elementarySchwartzSubmodule_add_mem
  smul_mem' := elementarySchwartzSubmodule_smul_mem

end

/-- Paper: Definition D.1.3.1, p. 750. On the purely real factor the paper's
membership condition agrees with Mathlib's Schwartz class. -/
theorem elementarySchwartzSubmodule_real_iff
    (f : EuclideanSpace ℝ (Fin m) → ℂ) :
    (fun g : ElementaryLieGroup m 0 0 PUnit ↦ f g.1) ∈
        elementarySchwartzSubmodule m 0 0 PUnit ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ, (s : _ → ℂ) = f := by sorry

section

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Paper: Definition D.1.3.1, p. 750. Every weighted bound vanishes on the zero function. -/
theorem elementarySchwartzSeminorm_map_zero (i : ElementarySchwartzIndex m n r) :
    (elementarySchwartzBound (0 : elementarySchwartzSubmodule m n r F).val i).toReal = 0 :=
  by sorry

/-- Paper: Definition D.1.3.1, p. 750. Each real-valued weighted bound is subadditive
on the Schwartz submodule. -/
theorem elementarySchwartzSeminorm_add_le (i : ElementarySchwartzIndex m n r)
    (f g : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (f + g).val i).toReal ≤
      (elementarySchwartzBound f.val i).toReal + (elementarySchwartzBound g.val i).toReal :=
  by sorry

/-- Paper: Definition D.1.3.1, p. 750. Scaling a Schwartz function multiplies its
real-valued weighted bound by the norm of the scalar. -/
theorem elementarySchwartzSeminorm_smul (i : ElementarySchwartzIndex m n r)
    (c : ℂ) (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (c • f).val i).toReal =
      ‖c‖ * (elementarySchwartzBound f.val i).toReal := by sorry

/-- Paper: Definition D.1.3.1, p. 750. Each real-valued weighted bound is invariant
under negation on the Schwartz submodule. -/
theorem elementarySchwartzSeminorm_neg (i : ElementarySchwartzIndex m n r)
    (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (-f).val i).toReal =
      (elementarySchwartzBound f.val i).toReal := by sorry

/-- Paper: Definition D.1.3.1, p. 750. On the Schwartz submodule each finite
weighted bound gives a real-valued seminorm. -/
def elementarySchwartzSeminorm (i : ElementarySchwartzIndex m n r) :
    Seminorm ℂ (elementarySchwartzSubmodule m n r F) where
  toFun f := (elementarySchwartzBound f.val i).toReal
  map_zero' := elementarySchwartzSeminorm_map_zero i
  add_le' := elementarySchwartzSeminorm_add_le i
  smul' := elementarySchwartzSeminorm_smul i
  neg' := elementarySchwartzSeminorm_neg i

end

/-- Paper: Definition D.1.3.1, p. 750. The locally convex topology on
the Schwartz space is generated by the weighted derivative seminorms. -/
abbrev ElementarySchwartz (m n r : ℕ) (F : Type*) :=
  WithGeneratingSeminorms (elementarySchwartzSubmodule m n r F) elementarySchwartzSeminorm

instance : CoeFun (ElementarySchwartz m n r F) (fun _ ↦ ElementaryLieGroup m n r F → ℂ) where
  coe f := (show elementarySchwartzSubmodule m n r F from f).val

/-- Paper: Definition D.1.3.1, p. 750. At zero multi-indices the seminorm is the
uniform norm of the underlying function. -/
theorem elementarySchwartzSeminorm_zero (f : ElementarySchwartz m n r F) :
    elementarySchwartzSeminorm (0, 0, 0, 0) f = ⨆ g, ‖f g‖ := by sorry

/-- Paper: Definition D.1.3.1, p. 750. The canonical seminorm family generates
the topology of the space. -/
theorem elementarySchwartz_withSeminorms :
    WithSeminorms (E := ElementarySchwartz m n r F) elementarySchwartzSeminorm := by sorry

/-- Paper: Remark D.1.3.2, p. 750. The Schwartz topology is Hausdorff. -/
theorem elementarySchwartz_t2 : T2Space (ElementarySchwartz m n r F) := by sorry

/-- Paper: Lemma D.1.3.3, p. 750. Pullback by a topological group automorphism
gives a linear topological automorphism of the elementary Schwartz space. -/
theorem elementarySchwartz_pullback (φ : ElementaryLieGroup m n r F ≃ₜ+ ElementaryLieGroup m n r F) :
    ∃ e : ElementarySchwartz m n r F ≃L[ℂ] ElementarySchwartz m n r F,
      ∀ f g, e f g = f (φ g) := by sorry

/-- Paper: Lemma D.1.3.4, p. 751. Polynomial weights in the two Euclidean lengths,
with a fixed mixed partial for each seminorm, generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P1 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖) := by sorry

/-- Paper: Lemma D.1.3.4, p. 751. Complex polynomial weights in the real and integer
coordinates, with a fixed mixed partial for each seminorm, generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P2 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        ((Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal
            (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.2.2‖ *
              ‖elementaryPartial f i.1 i.2.1 xt a b‖) := by sorry

/-- Paper: Lemma D.1.3.4, p. 751. Polynomial weights applied to
constant-coefficient polynomial differential operators generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P3 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.1 *
            i.2.coeff.sum (fun d c ↦ c * elementaryPartial f
              (fun k ↦ d (.inl k)) (fun k ↦ d (.inr k)) xt a b)‖₊ : ℝ≥0∞) := by sorry

/-- Paper: Lemma D.1.3.5(1), p. 752. Summing the monomial seminorms with each
multi-index of total degree at most N gives a family of norms generating the topology. -/
theorem elementarySchwartz_withSeminorms_sum :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F) ℕ,
      WithSeminorms p ∧ (∀ N f, p N f = 0 ↔ f = 0) ∧
        ∀ N f, p N f =
          ∑ i : (Fin m → Fin (N + 1)) × (Fin m → Fin (N + 1)) ×
                (Fin n → Fin (N + 1)) × (Fin r → Fin (N + 1)),
            if (∑ k, (i.1 k).val) ≤ N ∧ (∑ k, (i.2.1 k).val) ≤ N ∧
                (∑ k, (i.2.2.1 k).val) ≤ N ∧ (∑ k, (i.2.2.2 k).val) ≤ N then
              elementarySchwartzSeminorm
                (fun k ↦ (i.1 k).val, fun k ↦ (i.2.1 k).val,
                  fun k ↦ (i.2.2.1 k).val, fun k ↦ (i.2.2.2 k).val) f
            else 0 := by sorry

/-- Paper: Lemma D.1.3.5(2), p. 752. The elementary Schwartz space is Fréchet. -/
theorem elementarySchwartz_isFrechet : IsFrechetTVS (ElementarySchwartz m n r F) := by sorry

end Elementary

section ElementaryTensor

variable {m n r : ℕ} {F : Type*}

/-- Paper: (D.1.3.17), p. 752. The j-th bound on a sequence is its absolute sum
with weight `(1 + |a|)^j`, where the integer lattice inherits the Euclidean length. -/
def rapidDecaySequenceBound (j : ℕ) (s : (Fin r → ℤ) → ℂ) : ℝ≥0∞ :=
  ∑' a : Fin r → ℤ,
    (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j *
      (‖s a‖₊ : ℝ≥0∞)

/-- Paper: (D.1.3.17), p. 752. On a point mass at the origin the weighted sum
is the norm of the mass, for every weight. -/
theorem rapidDecaySequenceBound_singleton_zero (j : ℕ) (c : ℂ) :
    rapidDecaySequenceBound (r := r) j (({0} : Set (Fin r → ℤ)).indicator (fun _ ↦ c)) =
      (‖c‖₊ : ℝ≥0∞) := by sorry

/-- Paper: Remark D.1.3.6, p. 752. The zero lattice sequence has finite weighted
absolute sums of all orders. -/
theorem rapidDecaySequenceSubmodule_zero_mem :
    ∀ j, rapidDecaySequenceBound j (0 : (Fin r → ℤ) → ℂ) < ⊤ := by sorry

/-- Paper: Remark D.1.3.6, p. 752. Rapidly decreasing lattice sequences are closed
under addition. -/
theorem rapidDecaySequenceSubmodule_add_mem {s t : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤)
    (ht : ∀ j, rapidDecaySequenceBound j t < ⊤) :
    ∀ j, rapidDecaySequenceBound j (s + t) < ⊤ := by sorry

/-- Paper: Remark D.1.3.6, p. 752. Rapidly decreasing lattice sequences are closed
under complex scalar multiplication. -/
theorem rapidDecaySequenceSubmodule_smul_mem (c : ℂ) {s : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤) :
    ∀ j, rapidDecaySequenceBound j (c • s) < ⊤ := by sorry

/-- Paper: Remark D.1.3.6, p. 752. A rapidly decreasing lattice sequence
has finite weighted absolute sums of all orders. -/
def rapidDecaySequenceSubmodule (r : ℕ) : Submodule ℂ ((Fin r → ℤ) → ℂ) where
  carrier := {s | ∀ j, rapidDecaySequenceBound j s < ⊤}
  zero_mem' := rapidDecaySequenceSubmodule_zero_mem
  add_mem' := rapidDecaySequenceSubmodule_add_mem
  smul_mem' := rapidDecaySequenceSubmodule_smul_mem

/-- Paper: Remark D.1.3.6, p. 752. Every finitely supported lattice sequence
belongs to the rapidly decreasing sequence space. -/
theorem mem_rapidDecaySequenceSubmodule_of_finiteSupport (s : (Fin r → ℤ) → ℂ)
    (hs : (Function.support s).Finite) :
    s ∈ rapidDecaySequenceSubmodule r := by sorry

/-- Paper: (D.1.3.17), p. 752. Each weighted absolute sum vanishes on the zero sequence. -/
theorem rapidDecaySequenceSeminorm_map_zero (j : ℕ) :
    (rapidDecaySequenceBound j (0 : rapidDecaySequenceSubmodule r).val).toReal = 0 := by sorry

/-- Paper: (D.1.3.17), p. 752. Each real-valued weighted absolute sum is subadditive
on rapidly decreasing lattice sequences. -/
theorem rapidDecaySequenceSeminorm_add_le (j : ℕ) (s t : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (s + t).val).toReal ≤
      (rapidDecaySequenceBound j s.val).toReal + (rapidDecaySequenceBound j t.val).toReal :=
  by sorry

/-- Paper: (D.1.3.17), p. 752. Scaling a rapidly decreasing lattice sequence
multiplies its real-valued weighted absolute sum by the norm of the scalar. -/
theorem rapidDecaySequenceSeminorm_smul (j : ℕ) (c : ℂ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (c • s).val).toReal =
      ‖c‖ * (rapidDecaySequenceBound j s.val).toReal := by sorry

/-- Paper: (D.1.3.17), p. 752. Each real-valued weighted absolute sum is invariant
under negation on rapidly decreasing lattice sequences. -/
theorem rapidDecaySequenceSeminorm_neg (j : ℕ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (-s).val).toReal = (rapidDecaySequenceBound j s.val).toReal :=
  by sorry

/-- Paper: (D.1.3.17), p. 752. The finite weighted sums are seminorms on the
space of rapidly decreasing sequences. -/
def rapidDecaySequenceSeminorm (j : ℕ) : Seminorm ℂ (rapidDecaySequenceSubmodule r) where
  toFun s := (rapidDecaySequenceBound j s.val).toReal
  map_zero' := rapidDecaySequenceSeminorm_map_zero j
  add_le' := rapidDecaySequenceSeminorm_add_le j
  smul' := rapidDecaySequenceSeminorm_smul j
  neg' := rapidDecaySequenceSeminorm_neg j

/-- Paper: Remark D.1.3.6, p. 753. The weighted absolute-sum seminorms generate
the locally convex topology on the rapidly decreasing lattice sequences. -/
abbrev RapidDecaySequence (r : ℕ) :=
  WithGeneratingSeminorms (rapidDecaySequenceSubmodule r) rapidDecaySequenceSeminorm

instance : CoeFun (RapidDecaySequence r) (fun _ ↦ (Fin r → ℤ) → ℂ) where
  coe s := (show rapidDecaySequenceSubmodule r from s).val

/-- Paper: (D.1.3.17), p. 752. On a rapidly decreasing sequence the seminorm
of order zero is the unweighted absolute sum. -/
theorem rapidDecaySequenceSeminorm_zero (s : RapidDecaySequence r) :
    rapidDecaySequenceSeminorm 0 s = ∑' a, ‖s a‖ := by sorry

/-- Paper: Remark D.1.3.6, p. 753. The weighted sums generate the topology
and give a Fréchet space. -/
theorem rapidDecaySequence_withSeminorms :
    WithSeminorms (E := RapidDecaySequence r) rapidDecaySequenceSeminorm := by sorry

/-- Paper: Remark D.1.3.6, p. 753. The rapidly decreasing sequence space is Fréchet. -/
theorem rapidDecaySequence_isFrechet : IsFrechetTVS (RapidDecaySequence r) := by sorry

/-- Paper: Remark D.1.3.6, p. 752. Reading a sequence as a function on the
integer lattice identifies it with the elementary Schwartz space of that lattice. -/
theorem rapidDecaySequence_equiv_elementarySchwartz :
    ∃ e : RapidDecaySequence r ≃L[ℂ] ElementarySchwartz 0 0 r PUnit,
      ∀ s (g : ElementaryLieGroup 0 0 r PUnit), e s g = s g.2.2.1 := by sorry

-- TODO(later): needs §C.2.4 for the nuclearity assertion in Remark D.1.3.6.

/-- Paper: (D.1.3.18), p. 753. Bracket the projective tensor product into two pairs. -/
abbrev elementaryProjectiveTensor (m n r : ℕ) (F : Type*) :=
  ProjectiveTensor
    (ProjectiveTensor (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
      (ElementarySchwartz 0 n 0 PUnit))
    (ProjectiveTensor (RapidDecaySequence r) (F → ℂ))

/-- Paper: (D.1.3.18), p. 753. The four factors carry the projective tensor topology.
The real factor uses Mathlib's Schwartz space, and the torus factor is the
elementary Schwartz space with its other factors trivial. -/
def ElementarySchwartzTensor (m n r : ℕ) (F : Type*) : Type _ :=
  elementaryProjectiveTensor m n r F

section TensorInstances

set_option synthInstance.maxHeartbeats 100000

instance : AddCommGroup (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (AddCommGroup (elementaryProjectiveTensor m n r F))

instance : Module ℂ (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (Module ℂ (elementaryProjectiveTensor m n r F))

instance : UniformSpace (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (UniformSpace (elementaryProjectiveTensor m n r F))

instance : IsUniformAddGroup (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (IsUniformAddGroup (elementaryProjectiveTensor m n r F))

instance : ContinuousSMul ℂ (ElementarySchwartzTensor m n r F) :=
  WithSeminorms.continuousSMul (E := ElementarySchwartzTensor m n r F)
    (withGeneratingSeminorms_spec _ _)

instance : UniformContinuousConstSMul ℂ (ElementarySchwartzTensor m n r F) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℂ _

end TensorInstances

/-- Paper: (D.1.3.19), p. 753. Form the pure tensor in the projective product
of the four Schwartz factors. -/
def elementarySchwartzTmul (u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
    (v : ElementarySchwartz 0 n 0 PUnit) (s : RapidDecaySequence r) (c : F → ℂ) :
    ElementarySchwartzTensor m n r F :=
  (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] c)

variable [hF : Finite F]

include hF in
/-- Paper: Lemma D.1.3.7(1), p. 753. Multiplying the four factors pointwise on
pure tensors gives a linear embedding that induces the projective tensor product topology. -/
theorem elementarySchwartzTensor_isEmbedding :
    ∃ φ : ElementarySchwartzTensor m n r F →ₗ[ℂ] ElementarySchwartz m n r F,
      IsEmbedding φ ∧
        ∀ (u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (v : ElementarySchwartz 0 n 0 PUnit)
          (s : RapidDecaySequence r) (c : F → ℂ) (g : ElementaryLieGroup m n r F),
          φ (elementarySchwartzTmul u v s c) g =
            u g.1 * v (0, g.2.1, 0, PUnit.unit) * s g.2.2.1 * c g.2.2.2 := by sorry

include hF in
/-- Paper: Lemma D.1.3.7(2), p. 753. Multiplication of the factors on pure tensors
extends uniquely to a linear topological isomorphism from the projective completion.
Deviation: We complete the iterated algebraic projective tensor product once. -/
theorem elementarySchwartzTensor_completion_equiv :
    ∃! e : UniformSpace.Completion (ElementarySchwartzTensor m n r F) ≃L[ℂ]
        ElementarySchwartz m n r F,
      ∀ (u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (v : ElementarySchwartz 0 n 0 PUnit)
        (s : RapidDecaySequence r) (c : F → ℂ) (g : ElementaryLieGroup m n r F),
        e (UniformSpace.Completion.coe' (α := ElementarySchwartzTensor m n r F)
          (elementarySchwartzTmul u v s c)) g =
          u g.1 * v (0, g.2.1, 0, PUnit.unit) * s g.2.2.1 * c g.2.2.2 := by sorry

-- TODO(paper-gap): In the proof of Lemma D.1.3.7(2), (D.1.3.33) bounds a global
-- seminorm by a quantity tending to zero as the real or lattice coordinate goes to infinity.

/-- Paper: Lemma D.1.3.7(3), p. 753. The strong dual of the elementary Schwartz
space is complete. Completeness of the Schwartz space is part of Lemma D.1.3.5(2). -/
theorem elementarySchwartz_strongDual_complete :
    CompleteSpace (StrongDual ℂ (ElementarySchwartz m n r F)) := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Evaluation gives a linear topological
isomorphism from the elementary Schwartz space to its strong double dual. -/
theorem elementarySchwartz_reflexive :
    ∃ e : ElementarySchwartz m n r F ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (ElementarySchwartz m n r F)),
      ∀ f L, e f L = L f := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Evaluation gives a linear topological
isomorphism from the strong dual to its own strong double dual. -/
theorem elementarySchwartz_strongDual_reflexive :
    let D := StrongDual ℂ (ElementarySchwartz m n r F)
    ∃ e : D ≃L[ℂ] StrongDual ℂ (StrongDual ℂ D), ∀ L M, e L M = M L := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Closed bounded subsets of the elementary
Schwartz space are compact. -/
theorem elementarySchwartz_isCompact_of_isClosed_isVonNBounded
    {A : Set (ElementarySchwartz m n r F)} (hA : IsClosed A) (hb : IsVonNBounded ℂ A) :
    IsCompact A := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Closed bounded subsets of the strong dual
of the elementary Schwartz space are compact. -/
theorem elementarySchwartz_strongDual_isCompact_of_isClosed_isVonNBounded
    {A : Set (StrongDual ℂ (ElementarySchwartz m n r F))}
    (hA : IsClosed A) (hb : IsVonNBounded ℂ A) :
    IsCompact A := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. The elementary Schwartz space is barrelled. -/
theorem elementarySchwartz_barrelled : BarrelledSpace ℂ (ElementarySchwartz m n r F) := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. The strong dual of the elementary Schwartz
space is barrelled. -/
theorem elementarySchwartz_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (ElementarySchwartz m n r F)) := by sorry

-- TODO(later): needs §C.2.4 for the nuclearity of the Schwartz space and its
-- strong dual in Lemma D.1.3.7(3).
-- TODO(later): needs §C.5.1 (Theorem C.5.1.30(4)) for the vector-valued Schwartz
-- identifications used to define distribution tensor products in Remark D.1.3.8.

end ElementaryTensor

end RiemannMasullo
