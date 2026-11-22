module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.Extension
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Lebesgue differentiation along the diagonal

Masullo, §12.2, pp. 504–513. Completed-measure measurability is expressed as
`AEMeasurable` on the Borel measure space. Kernel smoothenings use the extension
by zero from §12.1, with regularity hypotheses where the paper uses their values.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped CompactlySupported ENNReal Pointwise

namespace RiemannMasullo

local instance instQuotientMeasurableSpaceSec2 {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

section Indentations

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  (H : Subgroup G)

local notation "Q" => G ⧸ H
local notation "π" => QuotientGroup.mk' H

/-- Paper: Definition 12.2.1.3, p. 506. An indentation is a continuous nonnegative real
function whose support meets the saturation of every compact set in a compact set, and
whose integral over each subgroup fibre converges and equals one. -/
def IsIndentation (μH : Measure H) (b : G → ℝ) : Prop :=
  Continuous b ∧ (∀ x, 0 ≤ b x) ∧
    (∀ K : Set G, IsCompact K → IsCompact (tsupport b ∩ π ⁻¹' (π '' K))) ∧
    ∀ x : G, Integrable (fun h : H ↦ b ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, b ((h : G)⁻¹ * x) ∂μH) = 1

/-- Paper: Definition 12.2.1.3, p. 506. For the trivial subgroup with unit counting
measure, the indentations are exactly the constant one function. -/
theorem isIndentation_bot_iff (b : G → ℝ) :
    IsIndentation (⊥ : Subgroup G) Measure.count b ↔ b = fun _ ↦ 1 := by sorry

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G]
  (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]

include hH in
/-- Paper: Lemma 12.2.1.1(1)–(3), p. 504. Every closed subgroup with a choice of
Haar measure has an indentation. The fibre integral is identically one on the group,
which entails continuity and invariance. -/
theorem exists_indentation : ∃ b : G → ℝ, IsIndentation H μH b := by sorry

/-- Paper: (12.2.1.8), p. 506. Lift a quotient function by pulling it back and
multiplying by the indentation. -/
def indentationLift (b : G → ℝ) (u : Q → ℂ) (x : G) : ℂ :=
  (b x : ℂ) * u (π x)

include hH in
/-- Paper: Lemma 12.2.1.1, p. 505. The lift of a continuous quotient function is
integrable on every subgroup fibre and its fibre integral recovers the quotient value. -/
theorem integral_indentationLift {b : G → ℝ} (hb : IsIndentation H μH b)
    (u : C(Q, ℂ)) (x : G) :
    Integrable (fun h : H ↦ indentationLift H b u ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, indentationLift H b u ((h : G)⁻¹ * x) ∂μH) = u (π x) := by sorry

/-- Paper: (12.2.1.5), p. 505. Fibre integration of a compactly supported test
commutes with complex scalar multiplication. -/
theorem indentationAverage_smul (c : ℂ) (f : C_c(G, ℂ)) :
    (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH (c • f) =
      c • (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH f := by sorry

/-- Paper: (12.2.1.5), p. 505. The quotient average of a compactly supported
continuous function integrates over the subgroup fibres and is a complex-linear
map into compactly supported continuous functions. -/
def indentationAverage : C_c(G, ℂ) →ₗ[ℂ] C_c(Q, ℂ) where
  toFun := (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH
  map_add' := ((TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH).map_add
  map_smul' := indentationAverage_smul H hH μH

/-- Paper: (12.2.1.5), p. 506. Evaluate the quotient average at the coset of any
representative by integrating its inverse subgroup translates. -/
theorem indentationAverage_apply (f : C_c(G, ℂ)) (x : G) :
    Integrable (fun h : H ↦ f ((h : G)⁻¹ * x)) μH ∧
      indentationAverage H hH μH f (π x) = ∫ h : H, f ((h : G)⁻¹ * x) ∂μH := by sorry

/-- Paper: (12.2.1.6), p. 506. A regular positive measure upstairs lifts a quotient
measure if its integrals on compactly supported continuous tests agree with the
quotient integrals of the fibre averages. -/
def IsIndentationMeasureLift (ν₀ : Measure Q) (μ₀ : Measure G) : Prop :=
  μ₀.Regular ∧
    ∀ f : C_c(G, ℂ), (∫ q, indentationAverage H hH μH f q ∂ν₀) = ∫ x, f x ∂μ₀

/-- Paper: (12.2.1.6), p. 506. Weil-normalized Haar measures give an instance of the
measure lift from the quotient. -/
theorem isIndentationMeasureLift_of_weil {μ : Measure G} [μ.IsHaarMeasure]
    {ν : Measure Q} (hν : IsWeilQuotientMeasure H μ μH ν) :
    IsIndentationMeasureLift H hH μH ν μ := by sorry

/-- Paper: Corollary 12.2.1.2(1), p. 506. Each positive Radon measure on the quotient
has a unique positive Radon lift satisfying the normalization on compact tests.
Deviation: Regularity of the lift is explicit, as in the proof. -/
theorem existsUnique_indentationMeasureLift (ν₀ : Measure Q) [ν₀.Regular] :
    ∃! μ₀ : Measure G, IsIndentationMeasureLift H hH μH ν₀ μ₀ := by sorry

/-- Paper: Corollary 12.2.1.2(1), p. 506. The lifted measure is invariant under
left translation by every subgroup element. -/
theorem map_mul_indentationMeasureLift {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) (h : H) :
    μ₀.map (fun x : G ↦ (h : G) * x) = μ₀ := by sorry

/-- Paper: Corollary 12.2.1.2(2), p. 506. Fibre integration extends to a surjective
continuous complex-linear map of L¹ spaces, agreeing with the original map on compact tests. -/
theorem exists_indentationAverageL1 {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) :
    ∃ A : Lp ℂ 1 μ₀ →L[ℂ] Lp ℂ 1 ν₀,
      Function.Surjective A ∧
        ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
          (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f := by sorry

/-- Paper: Corollary 12.2.1.2(2), p. 506. Multiplying the pulled-back L¹ representative
by any indentation defines an isometric continuous linear right inverse to the L¹ extension. -/
theorem exists_indentationLiftL1 {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀)
    (A : Lp ℂ 1 μ₀ →L[ℂ] Lp ℂ 1 ν₀)
    (hA : ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
      (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f)
    {b : G → ℝ} (hb : IsIndentation H μH b) :
    ∃ L : Lp ℂ 1 ν₀ →L[ℂ] Lp ℂ 1 μ₀,
      Isometry L ∧ Function.RightInverse L A ∧
        ∀ u : Lp ℂ 1 ν₀, (L u : G → ℂ) =ᵐ[μ₀] indentationLift H b u := by sorry

end Indentations

section ProperActions

variable {A X : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T2Space A] [LocallyCompactSpace A] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MulAction A X] [ContinuousSMul A X] [ProperSMul A X]
  [IsCancelSMul A X] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace X] [BorelSpace X]

local notation "Ω" => MulAction.orbitRel.Quotient A X
local instance instOrbitQuotientMeasurableSpaceSec2 : MeasurableSpace Ω := borel _

-- Mathlib supplies the Hausdorff orbit quotient of a proper action, the open quotient map,
-- and second countability of the quotient of a second countable space.
/-- Paper: Remark 12.2.1.4, p. 507. For a free proper action, an invariant Radon measure
and a choice of Haar measure determine a unique Radon measure on the orbit space.
Deviation: The normalization formula is tested on compactly supported continuous functions. -/
theorem existsUnique_properActionQuotientMeasure (μA : Measure A) [μA.IsHaarMeasure]
    (μX : Measure X) [μX.Regular] [SMulInvariantMeasure A X μX] :
    ∃! ν : Measure Ω, ν.Regular ∧
      ∀ f : C_c(X, ℂ),
        Integrable (fun q : Ω ↦ ∫ a : A, f (a • q.out) ∂μA) ν ∧
          (∫ x, f x ∂μX) = ∫ q : Ω, ∫ a : A, f (a • q.out) ∂μA ∂ν := by sorry

end ProperActions

section FundamentalDomains

variable {A X : Type*} [Group A] [MulAction A X] [TopologicalSpace X] [MeasurableSpace X]

-- TODO(paper-gap): (12.2.1.13) lies in X but is assigned a measure on X/G.
-- For the discrete subgroup cases below, a null overlap upstairs is equivalent
-- to its image being null for the corresponding normalized quotient measure.
/-- Paper: Remark 12.2.1.4, p. 507. The domain has nonempty interior, each point has
a unique translate in it, and the closure has null overlap with each of its
nonidentity translates.
Deviation: The overlap is measured upstairs. We drop connectedness for §12.2.2:
already for the rational ideles a connected set has singleton projection to ℚₚˣ
at every finite place, and hence has empty interior. -/
def IsIndentationFundamentalDomain (A : Type*) [Group A] [MulAction A X]
    (μ : Measure X) (D : Set X) : Prop :=
  (interior D).Nonempty ∧
    (∀ x : X, ∃! a : A, a • x ∈ D) ∧
    ∀ a : A, a ≠ 1 → μ (closure D ∩ a • closure D) = 0

/-- Paper: Remark 12.2.1.4, p. 507. With the trivial group acting, the whole space is
a fundamental domain exactly when it is nonempty under the relaxed definition. -/
theorem isIndentationFundamentalDomain_univ_punit (μ : Measure X) :
    IsIndentationFundamentalDomain PUnit μ (univ : Set X) ↔
      (univ : Set X).Nonempty := by sorry

/-- Paper: Remark 12.2.1.4, p. 507. With countably many translates and a Borel
measure, the paper's exact tiling gives a measure-theoretic fundamental domain. -/
theorem IsIndentationFundamentalDomain.isFundamentalDomain [Countable A] [BorelSpace X]
    {μ : Measure X} {D : Set X} (hD : IsIndentationFundamentalDomain A μ D) :
    IsFundamentalDomain A D μ := by sorry

end FundamentalDomains

section Diagonal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

local notation "Q" => G ⧸ H
local notation "π" => QuotientGroup.mk' H
local notation "q₂" => (Prod.map (QuotientGroup.mk' H) (QuotientGroup.mk' H))
local notation "countH" => (Measure.count : Measure H)

/-- Paper: Situation 12.2.2.1, p. 508. The domain for the translation action contains a
D′-sequence of relatively compact open symmetric neighborhoods of the identity. The discrete
closed subgroup and the compatible Haar measures are the standing hypotheses of the results. -/
def IsDiagonalIndentationSituation (μ : Measure G) (D : Set G) (U : ℕ → Set G) : Prop :=
  IsIndentationFundamentalDomain H μ D ∧ IsDPrimeSequence μ U ∧
    ∀ n, U n ⊆ D ∧ IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n

/-- Paper: Situation 12.2.2.1, p. 508. On the one-element group, the whole space
is a fundamental domain and also supplies the constant neighborhood sequence. -/
theorem isDiagonalIndentationSituation_subsingleton [Subsingleton G] :
    IsDiagonalIndentationSituation (⊥ : Subgroup G) Measure.count univ (fun _ ↦ univ) := by sorry

variable [DiscreteTopology H] (hH : IsClosed (H : Set G))
  {μ : Measure G} [μ.IsHaarMeasure] {ν : Measure (G ⧸ H)}
  (hν : IsWeilQuotientMeasure H μ Measure.count ν)
  {D : Set G} {U : ℕ → Set G} (hS : IsDiagonalIndentationSituation H μ D U)

local notation "Ū" => (fun n ↦ (QuotientGroup.mk' H) '' U n)

include hH hν hS in
/-- Paper: Situation 12.2.2.1, p. 508. The quotient images of the neighborhoods in
the fundamental domain form a D′-sequence for the normalized quotient Haar measure. -/
theorem IsDiagonalIndentationSituation.quotient :
    IsDPrimeSequence ν Ū := by sorry

/-- Paper: (12.2.2.1), p. 508. Multiply the two indentation factors and integrate
their simultaneous subgroup translates. -/
def diagonalIndentationWeight (μH : Measure H) (b : G → ℝ) (p : G × G) : ℝ :=
  ∫ h : H, b ((h : G)⁻¹ * p.1) * b ((h : G)⁻¹ * p.2) ∂μH

/-- Paper: (12.2.2.1), p. 508. Averaging over the trivial subgroup with unit counting
measure returns the product of the two indentation factors. -/
theorem diagonalIndentationWeight_bot (b : G → ℝ) (p : G × G) :
    diagonalIndentationWeight (⊥ : Subgroup G) Measure.count b p = b p.1 * b p.2 := by sorry

variable {b : G → ℝ} (hb : IsIndentation H Measure.count b)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The product of simultaneous translates is
integrable in the subgroup variable at every pair. -/
theorem integrable_diagonalIndentationWeight (p : G × G) :
    Integrable (fun h : H ↦ b ((h : G)⁻¹ * p.1) * b ((h : G)⁻¹ * p.2)) countH := by sorry

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The averaged indentation weight is continuous. -/
theorem continuous_diagonalIndentationWeight :
    Continuous (diagonalIndentationWeight H countH b) := by sorry

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The averaged indentation weight is nonnegative. -/
theorem diagonalIndentationWeight_nonneg (p : G × G) :
    0 ≤ diagonalIndentationWeight H countH b p := by sorry

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. Translating both coordinates by the same
subgroup element leaves the averaged weight invariant. -/
theorem diagonalIndentationWeight_mul (h : H) (p : G × G) :
    diagonalIndentationWeight H countH b ((h : G) * p.1, (h : G) * p.2) =
      diagonalIndentationWeight H countH b p := by sorry

/-- Paper: (12.2.2.2), p. 508. Lift a quotient kernel by pulling it back in both
coordinates and multiplying by the subgroup-averaged indentation weight. -/
def diagonalIndentationLift (μH : Measure H) (b : G → ℝ) (u : Q × Q → ℂ)
    (p : G × G) : ℂ :=
  (diagonalIndentationWeight H μH b p : ℂ) * u (q₂ p)

/-- Paper: (12.2.2.2), p. 508. For the trivial subgroup with unit counting measure,
the kernel lift is a product of the two indentation factors and the pulled-back value. -/
theorem diagonalIndentationLift_bot (b : G → ℝ)
    (u : (G ⧸ (⊥ : Subgroup G)) × (G ⧸ (⊥ : Subgroup G)) → ℂ) (x y : G) :
    diagonalIndentationLift (⊥ : Subgroup G) Measure.count b u (x, y) =
      (b x : ℂ) * (b y : ℂ) * u (QuotientGroup.mk x, QuotientGroup.mk y) := by sorry

variable {u : (G ⧸ H) × (G ⧸ H) → ℂ} (hu : LocallyIntegrable u (ν.prod ν))

local notation "uSmooth" => (dSequenceKernelSmoothening ν Ū u)
local notation "Ψ" => (diagonalIndentationLift H (Measure.count : Measure H) b)

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The lifted kernel is measurable for
completed product Haar measure.
Deviation: The local integrability hypothesis uses the product measure as in the proof. -/
theorem aemeasurable_diagonalIndentationLift :
    AEMeasurable (Ψ u) (μ.prod μ) := by sorry

variable (hdiag : ∀ᵐ q ∂ν, (q, q) ∈
    dSequenceRegularSet (ν.prod ν)
      (fun n ↦ (QuotientGroup.mk' H '' U n) ×ˢ (QuotientGroup.mk' H '' U n)) u)

include hH hν hS hu hdiag in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The smoothened quotient diagonal is
measurable for the completed quotient Haar measure. -/
theorem aemeasurable_dSequenceKernelSmoothening_diagonal :
    AEMeasurable (fun q ↦ uSmooth (q, q)) ν := by sorry

include hH hν hS hu hdiag in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The quotient points used on both skew
diagonals of the lift are regular for almost every group coordinate. -/
theorem ae_quotient_diagonal_mem_dSequenceRegularSet :
    ∀ᵐ x ∂μ, (π x, π x) ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := by sorry

variable (hi : Integrable (fun q ↦
  dSequenceKernelSmoothening ν (fun n ↦ QuotientGroup.mk' H '' U n) u (q, q)) ν)

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. Translating the first diagonal coordinate
gives a function measurable for the completed product measure.
Deviation: The product measure follows the coordinate order `(x, h)`. -/
theorem aemeasurable_diagonalIndentationLift_left :
    AEMeasurable (fun p : G × H ↦ Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1)) (μ.prod countH) :=
  by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. Translating the second diagonal coordinate
gives a function measurable for the completed product measure.
Deviation: The product measure follows the coordinate order `(x, h)`. -/
theorem aemeasurable_diagonalIndentationLift_right :
    AEMeasurable (fun p : G × H ↦ Ψ uSmooth (p.1, (p.2 : G)⁻¹ * p.1)) (μ.prod countH) :=
  by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.3), p. 508. The first skew-diagonal evaluation is absolutely
integrable on the fundamental domain times the subgroup. -/
theorem integrable_diagonalIndentationLift_left :
    Integrable (fun p : G × H ↦ Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1))
      ((μ.restrict D).prod countH) := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The second skew-diagonal evaluation is
absolutely integrable on the fundamental domain times the subgroup. -/
theorem integrable_diagonalIndentationLift_right :
    Integrable (fun p : G × H ↦ Ψ uSmooth (p.1, (p.2 : G)⁻¹ * p.1))
      ((μ.restrict D).prod countH) := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The integral of the smoothened quotient diagonal
equals the integral of the first skew diagonal, integrating subgroup translates first. -/
theorem integral_diagonalIndentationLift_left :
    (∫ q, uSmooth (q, q) ∂ν) =
      ∫ x in D, ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH ∂μ := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.5), p. 508. The first skew-diagonal integral is unchanged by
exchanging the order of integration. -/
theorem integral_diagonalIndentationLift_left_swap :
    (∫ x in D, ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH ∂μ) =
      ∫ h : H, ∫ x in D, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂μ ∂countH := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.6), p. 508. Translating the second coordinate gives the same
integral as translating the first. -/
theorem integral_diagonalIndentationLift_swap_coordinates :
    (∫ h : H, ∫ x in D, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂μ ∂countH) =
      ∫ h : H, ∫ x in D, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂μ ∂countH := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.7), p. 508. The second skew-diagonal integral is unchanged by
exchanging the order of integration. -/
theorem integral_diagonalIndentationLift_right_swap :
    (∫ h : H, ∫ x in D, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂μ ∂countH) =
      ∫ x in D, ∫ h : H, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂countH ∂μ := by sorry

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(3), p. 508. Multiplication by a compactly supported
continuous quotient function commutes almost everywhere with the kernel lift after
pullback of the multiplier. -/
theorem diagonalIndentationLift_mul (ρ : C_c(Q × Q, ℂ)) :
    Ψ (fun p ↦ ρ p * u p) =ᵐ[μ.prod μ] fun p ↦ ρ (q₂ p) * Ψ u p := by sorry

-- TODO(paper-gap): The continuous multiplier step on p. 511 applies Corollary
-- A.5.4.3 at every regular point. The printed equivalence fails (ERRATA R8).
include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(4), p. 509. On product-Haar-almost every pair,
the averages of the lifted kernel converge to the lift of the quotient smoothening. -/
theorem ae_tendsto_diagonalIndentationLift_average :
    ∀ᵐ p ∂μ.prod μ, Tendsto (fun n ↦
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (Ψ u) p) atTop (𝓝 (Ψ uSmooth p)) := by sorry

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(4), p. 509. Regularity of a pair for the lifted kernel
agrees with regularity of its quotient pair for product-Haar-almost every pair.
Deviation: Product-almost-everywhere equivalence replaces the printed every-pair claim. -/
theorem ae_diagonalIndentationLift_regular_iff :
    ∀ᵐ p ∂μ.prod μ,
      p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) (Ψ u) ↔
        q₂ p ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := by sorry

-- Remark 12.2.2.3, p. 509. Mathlib's AEMeasurable.nullMeasurable and
-- NullMeasurable.aemeasurable identify measurability on the completed source
-- with almost-everywhere measurability on the Borel source for complex functions.

/-- Paper: (12.2.2.26), p. 512. The tail kernel restricts the lifted smoothened
kernel to second coordinates outside the indicated subgroup. -/
def diagonalIndentationTail (μH : Measure H) (b : G → ℝ) (v : Q × Q → ℂ)
    (K : Subgroup G) (p : G × G) : ℂ :=
  ((K : Set G)ᶜ).indicator (fun y ↦ diagonalIndentationLift H μH b v (p.1, y)) p.2

/-- Paper: (12.2.2.26), p. 512. Outside the indicated subgroup in the second
coordinate, the tail kernel equals the lifted kernel. -/
theorem diagonalIndentationTail_of_notMem (μH : Measure H) (b : G → ℝ) (v : Q × Q → ℂ)
    {K : Subgroup G} {x y : G} (hy : y ∉ K) :
    diagonalIndentationTail H μH b v K (x, y) =
      diagonalIndentationLift H μH b v (x, y) := by sorry

-- TODO(paper-gap): The closing citation on p. 513 refers to the tail definition
-- (12.2.2.26); the convergence claim is (12.2.2.27).
-- TODO(paper-gap): In (12.2.2.31), u₁ is only defined on G₀, but the inner integral
-- evaluates u₁(h⁻¹ x) for arbitrary x in G. It needs a fibre representative in G₀.
include hH hν hS hu hdiag hi in
/-- Paper: Proposition 12.2.2.4, p. 512. For an exhaustive filtration by open
subgroups with cyclic infinite successive quotients and a common fundamental domain in
the first stage, there is a compatible indentation whose integrated skew-diagonal tails
tend to zero. On each stage the indicator times the indentation is its restriction.
Deviation: The absolute integrability of each tail is explicit, as in the proof. -/
theorem exists_indentation_tendsto_tail (K : ℕ → Subgroup G)
    (hKopen : ∀ n, IsOpen (K n : Set G)) (hKmono : Monotone K)
    (hKexhaust : (⋃ n, (K n : Set G)) = univ) (hD₀ : D ⊆ (K 0 : Set G))
    (hDk : ∀ n, IsIndentationFundamentalDomain (H.comap (K n).subtype)
      (μ.comap (Subtype.val : K n → G)) ((Subtype.val : K n → G) ⁻¹' D))
    (hKrank : ∀ n, Nonempty
      ((K (n + 1) ⧸ (K n).comap (K (n + 1)).subtype) ≃* Multiplicative ℤ)) :
    ∃ c : G → ℝ, IsIndentation H countH c ∧
      (∀ n, IsIndentation (H.comap (K n).subtype) Measure.count (fun x : K n ↦ c x)) ∧
      (∀ n, Integrable (fun p : G × H ↦
        diagonalIndentationTail H countH c uSmooth (K n) (p.1, (p.2 : G)⁻¹ * p.1))
          ((μ.restrict D).prod countH)) ∧
      Tendsto (fun n ↦ ∫ x in D, ∫ h : H,
        diagonalIndentationTail H countH c uSmooth (K n) (x, (h : G)⁻¹ * x) ∂countH ∂μ)
          atTop (𝓝 0) := by sorry

end Diagonal

end RiemannMasullo
