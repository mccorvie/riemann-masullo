module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Periodic Schauder bases in the absence of multiplicity

Masullo, §4.5, pp. 197–209. We use the left translation and Haar measure
conventions of §4.4.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [hSC : SecondCountableTopology G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G)
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)

local notation "K" => m.toMonoidHom.ker
local notation "Γ" => Subgroup.zpowers γ
local notation "Q" => G ⧸ Γ
local notation "S" => SchwartzBruhat Q
local notation "E" => ModulatedExponentialDecay m (Set.univ : Set ℝ)
local notation "L" => Real.log ((m γ).val : ℝ)

local notation "zeroUniv" => (⟨(0 : ℝ), Set.mem_univ _⟩ : (Set.univ : Set ℝ))
local notation "twist₀" => modulatedExponentialDecayTwist m Set.univ zeroUniv
local notation "ρG" => schwartzBruhatTranslationAction (G := G)
local notation "ρQ" =>
  (letI : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
   schwartzBruhatTranslationAction (G := Q))
local notation "q" => QuotientGroup.mk' Γ

local instance instMeasurableSpaceCyclicQuotientSec5 : MeasurableSpace Q := borel _
local notation "H[" ω "]" =>
  (show Submodule ℂ E from (actionIsotype ((ρG).comp (K).subtype) ω).comap twist₀)

/-! ## 4.5.1 Periodization and its isotypic quotients -/

section Periodization

local notation "per" => modulatedPeriodization m γ hm hms hγ

include hSC in
/-- Paper: Proposition 4.5.1.1(1), pp. 197–198. The orbit sum of §4.4 is linear
and continuous for the two Schwartz–Bruhat topologies. -/
theorem modulatedPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ per ∧ Continuous per := by sorry

/-- Paper: Equation (4.5.1.1), p. 197. Ordinary periodization is the bundled
continuous linear map given by the orbit sum of §4.4. -/
def modulatedPeriodizationCLM : E →L[ℂ] S :=
  let h := modulatedPeriodization_isLinearMap_continuous m γ hm hms hγ
  ⟨IsLinearMap.mk' per h.1, h.2⟩

local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

-- Equation (4.5.1.2) at each lift is modulatedPeriodization_hasSum in §4.4.

/-- Paper: Proposition 4.5.1.1(1), pp. 197–199. The ordinary orbit sums converge
uniformly on compact sets of representatives in the original group.
Deviation: Finite partial sums need representatives because they are generally
functions on G only. -/
theorem modulatedPeriodization_tendstoUniformlyOn (f : E) (C : Set G) (hC : IsCompact C) :
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, f.val (γ ^ n * x))
      (fun x ↦ P f (q x)) atTop C := by sorry

/-- Paper: Proposition 4.5.1.1(1), pp. 197–199. On compact sets of lifts,
each iterated directional derivative of the orbit sum is the locally uniform
sum of the corresponding derivatives of the translates. -/
theorem modulatedPeriodization_deriv_tendstoUniformlyOn (f : E)
    (α : LCATopologicalLie G) (r : ℕ) (C : Set G) (hC : IsCompact C) :
    let d := (bruhatDirectionalDeriv α)^[r]
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, d f.val (γ ^ n * x))
      (d (fun x ↦ P f (q x))) atTop C := by sorry

/-- Paper: Proposition 4.5.1.1(1), pp. 197–198. Every Schwartz–Bruhat function
on the compact cyclic quotient is a periodization. -/
theorem modulatedPeriodization_surjective : Surjective P := by sorry

-- TODO(paper-gap): Remarks 4.5.1.2 and 4.5.1.4 use arbitrary I for
-- periodization. For I = (1,2), a smooth log-profile equal to one near
-- minus infinity and zero near plus infinity has divergent orbit sums.

/-- Paper: Remark 4.5.1.2, p. 198. Ordinary periodization on the two-sided
exponentially decaying space is open. -/
theorem modulatedPeriodization_isOpenMap : IsOpenMap P := by sorry

-- TODO(paper-gap): The continuity proof on pp. 199–200 assumes that a
-- convergent net in a locally convex space has a bounded tail.
-- The majorant on p. 199 also needs the supremum of the absolute values.
-- Remark 4.5.1.3 uses the tensor comparison of §D.3.3. For the valid
-- sequential assertion in Remarks 4.5.1.2 and 4.5.1.4 see the interval section.

/-- Paper: Proposition 4.5.1.1(1), p. 198. Periodization takes the corresponding
norm-one isotype on the decay space to a closed subspace of the quotient test space. -/
theorem modulatedPeriodization_isClosed_isotype_image (ω : PontryaginDual K) :
    IsClosed (P '' (H[ω] : Set E)) := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "perχ" => modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ

-- Proposition 4.5.1.1(2) is modulatedIsotypicPeriodization_mem in §4.4.

/-- Paper: Proposition 4.5.1.1(3), p. 198. The homogeneous orbit sum of §4.4
is linear and continuous. -/
theorem modulatedIsotypicPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ perχ ∧ Continuous perχ := by sorry

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization is the
bundled continuous linear map given by the character-weighted orbit sum. -/
def modulatedIsotypicPeriodizationCLM : E →L[ℂ] S :=
  let h := modulatedIsotypicPeriodization_isLinearMap_continuous m γ hm hms hγ μ₁ χ
  ⟨IsLinearMap.mk' perχ h.1, h.2⟩

local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

-- The pointwise sum in (2–3) is modulatedIsotypicPeriodization_hasSum in §4.4.

/-- Paper: §4.5 introduction and Proposition 4.5.1.1(2), pp. 197–198.
The homogeneous orbit sums converge uniformly on compact sets of representatives.
Deviation: The finite sums are evaluated on G, where their summands are defined. -/
theorem modulatedIsotypicPeriodization_tendstoUniformlyOn
    (f : E) (C : Set G) (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun s : Finset ℤ ↦ fun x : G ↦
        ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (fun x ↦ Pχ f (q x)) atTop C := by sorry

/-- Paper: §4.5 introduction and Proposition 4.5.1.1(2), pp. 197–199.
On compact sets of lifts each directional derivative of homogeneous periodization
is the locally uniform sum of the averaged derivatives. -/
theorem modulatedIsotypicPeriodization_deriv_tendstoUniformlyOn (f : E)
    (α : LCATopologicalLie G) (r : ℕ) (C : Set G) (hC : IsCompact C) :
    let d := (bruhatDirectionalDeriv α)^[r]
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x : G ↦
      ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * d f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (d (fun x ↦ Pχ f (q x))) atTop C := by sorry

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization is open
as a map to its image with the subspace topology. -/
theorem modulatedIsotypicPeriodization_isOpenMap_range :
    IsOpenMap ((Pχ).rangeRestrict) := by sorry

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization has closed range. -/
theorem modulatedIsotypicPeriodization_isClosed_range : IsClosed (range Pχ) := by sorry

end Periodization

section Difference

variable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)

local notation "D" => ModulatedExponentialDecay m I
local notation "diff" => (fun f : D ↦
  let g : modulatedExponentialDecaySubmodule m I := ⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
    modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩
  Sub.sub (α := D) f g)

include hSC hInt hne in
/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. Subtracting the
translate by the inverse generator is linear and continuous on the decay space. -/
theorem modulatedCyclicDifference_isLinearMap_continuous :
    IsLinearMap ℂ diff ∧ Continuous diff := by sorry

/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. The cyclic
difference sends a function to itself minus its translate by the inverse generator. -/
def modulatedCyclicDifference : D →L[ℂ] D :=
  let h := modulatedCyclicDifference_isLinearMap_continuous m γ hm hms I hInt hne
  let T : D →ₗ[ℂ] D := IsLinearMap.mk' diff h.1
  ⟨T, h.2⟩
set_option linter.unusedSectionVars false in -- Avoid expensive unused-section-variable linting.
/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. The difference
at x subtracts the function's value at γx. -/
theorem modulatedCyclicDifference_apply (f : D) (x : G) :
    (modulatedCyclicDifference m γ hm hms I hInt hne f).val x =
      f.val x - f.val (γ * x) := congrArg (fun y : G ↦ f.val x - f.val (y * x)) (inv_inv γ)

end Difference

local notation "Δ" => modulatedCyclicDifference m γ hm hms Set.univ
  (ordConnected_univ) (Set.univ_nonempty)
local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

section DifferenceKernels

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "ωχ" => PontryaginDual.map
  (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

-- TODO(paper-gap): On p. 202 the multiplier needs χ(γ)⁻¹. With the Mellin
-- weight χ(x)m(x)^s its zero lattice is 2πin/log(m γ) − it₀. The print has
-- the i in the numerator and writes log γ for the logarithm of the module.

/-- Paper: Proposition 4.5.1.1(4), p. 198. Inside the isotype, the kernel of
homogeneous periodization is the closure of the differences of isotypic functions.
Deviation: Closure is taken in the ambient decay space and then restricted to
the closed isotype. The linear image already contains the span of the differences. -/
theorem modulatedIsotypicPeriodization_ker_eq_closure :
    (Pχ).ker.comap (H[ωχ]).subtype =
      ((H[ωχ]).map (Δ).toLinearMap).topologicalClosure.comap (H[ωχ]).subtype := by sorry

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(5), p. 198. The ordinary periodization kernel
is the closure of the image of the cyclic difference. -/
theorem modulatedPeriodization_ker_eq_closure :
    (P).ker = (Δ).range.topologicalClosure := by sorry

-- TODO(paper-gap): The opening of the proof of (6) on p. 203 uses equality
-- with the actual difference range. Part (5) only identifies its closure.

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(6), p. 198. The cyclic difference has closed range. -/
theorem modulatedCyclicDifference_isClosed_range : IsClosed (range Δ) := by sorry

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(6), pp. 198, 203. Taking the range of the cyclic
difference commutes with passage to any norm-one isotype. -/
theorem modulatedCyclicDifference_range_isotype (ω : PontryaginDual K) :
    (Δ).range ⊓ H[ω] = (H[ω]).map (Δ).toLinearMap := by sorry

end DifferenceKernels

section QuotientIsotype

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

local notation "qK" => (q).comp (K).subtype
local notation "Sχ[" ω "]" => actionIsotype ((ρQ).comp qK) ω

-- TODO(paper-gap): In the proof on p. 201 the square of the unnormalized
-- quotient average is its Haar mass times the average itself.

include hm hγ in
/-- Paper: Notation 4.5.1.1, p. 204. The stated normalized compact average,
evaluated on the cyclic quotient, lands in the quotient Schwartz–Bruhat space. -/
theorem modulatedQuotientIsotypicProjector_mem (ω : PontryaginDual K) (f : S) :
    (fun z : Q ↦ (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁) ∈ schwartzBruhatSubmodule Q ∧
      ∀ z : Q, Integrable (fun u : K ↦ (ω u : ℂ) * f (qK u * z)) μ₁ := by sorry

local notation "avg[" ω "," f "]" => (⟨fun z : Q ↦ (μ₁.real univ : ℂ)⁻¹ *
  ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁,
  (modulatedQuotientIsotypicProjector_mem m γ hm hγ μ₁ ω f).1⟩ : S)

include hm hγ hSC in
/-- Paper: Notation 4.5.1.1, p. 204. The normalized compact average is linear
and continuous in the quotient test-function topology. -/
theorem modulatedQuotientIsotypicProjector_isLinearMap_continuous (ω : PontryaginDual K) :
    let A : S → S := fun f ↦ avg[ω, f]
    IsLinearMap ℂ A ∧ Continuous A := by sorry

/-- Paper: Notation 4.5.1.1, p. 204. The quotient projector is the
character-weighted compact average divided by the mass of the norm-one group. -/
def modulatedQuotientIsotypicProjector (ω : PontryaginDual K) : S →L[ℂ] S :=
  let h := modulatedQuotientIsotypicProjector_isLinearMap_continuous m γ hm hγ μ₁ ω
  let T : S →ₗ[ℂ] S := IsLinearMap.mk' (fun f : S ↦ avg[ω, f]) h.1
  ⟨T, h.2⟩

local notation "Ψ[" ω "]" => modulatedQuotientIsotypicProjector m γ hm hγ μ₁ ω

/-- Paper: Notation 4.5.1.1, p. 204. The normalized average fixes every
function in the norm-one isotype. -/
theorem modulatedQuotientIsotypicProjector_fix (ω : PontryaginDual K) (f : Sχ[ω]) :
    Ψ[ω] f.val = f.val := by sorry

/-- Paper: Notation 4.5.1.1 and Equation (4.5.1.9), p. 204. The projector
has range exactly the norm-one isotype on the quotient. -/
theorem modulatedQuotientIsotypicProjector_range (ω : PontryaginDual K) :
    (Ψ[ω]).range = Sχ[ω] := by sorry

/-- Paper: Notation 4.5.1.1, p. 204. The normalized quotient projector is idempotent. -/
theorem modulatedQuotientIsotypicProjector_idempotent (ω : PontryaginDual K) :
    (Ψ[ω]).comp Ψ[ω] = Ψ[ω] := ContinuousLinearMap.ext fun f ↦ modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω ⟨Ψ[ω] f, Eq.mp (congrArg (fun T ↦ Ψ[ω] f ∈ T) (modulatedQuotientIsotypicProjector_range m γ hm hγ μ₁ ω)) (LinearMap.mem_range_self _ f)⟩

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν
local notation "e" => modulatedCyclicExponential m γ hm hγ χ t₀ ht₀

include hSC hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. For a fixed norm-one character the
integer family of Fourier coefficient functionals is bounded in the strong dual. -/
theorem modulatedCyclicFourierCoeff_isVonNBounded (ω : PontryaginDual K) :
    IsVonNBounded ℂ (range fun n : ℤ ↦ a (ω, n)) := by sorry

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. The Fourier coefficients restricted
to the quotient isotype form a bounded set in its strong dual. -/
theorem modulatedCyclicFourierCoeff_isotype_isVonNBounded (ω : PontryaginDual K) :
    IsVonNBounded ℂ (range fun n : ℤ ↦ (a (ω, n)).comp (Sχ[ω]).subtypeL) := by sorry

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. The Fourier coefficients restricted
to the quotient isotype form an equicontinuous family. -/
theorem modulatedCyclicFourierCoeff_isotype_equicontinuous (ω : PontryaginDual K) :
    Equicontinuous (fun (n : ℤ) (f : Sχ[ω]) ↦ a (ω, n) f.val) := by sorry

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "volQ" => (L * μ₁.real univ : ℂ)

/-- Paper: Equation (4.5.1.12), p. 204. The quotient by the homogeneous
kernel maps to the test-function space by normalized homogeneous periodization.
Deviation: Normalizing recovers ordinary periodization on the isotypic representatives. -/
def modulatedIsotypicPeriodizationQuotient (ω : PontryaginDual K) : V[ω] →L[ℂ] S :=
  (μ₁.real univ : ℂ)⁻¹ • (Pχ[ω]).ker.liftQL (Pχ[ω]) le_rfl

local notation "T[" ω "]" => modulatedIsotypicPeriodizationQuotient m γ hm hms hγ μ₁ χ ω

include hχ in
/-- Paper: Corollary 4.5.1.6 and Equation (4.5.1.12), p. 204. The normalized
quotient map agrees with ordinary periodization on the matching isotype. -/
theorem modulatedIsotypicPeriodizationQuotient_mkQ (ω : PontryaginDual K)
    (f : E) (hf : f ∈ H[ω]) :
    T[ω] ((Pχ[ω]).ker.mkQ f) = P f := by sorry

include hχ in
/-- Paper: Equations (4.5.1.7)–(4.5.1.9) and (4.5.1.12), pp. 201, 204.
On every lift the normalized quotient map applies the quotient projector after
ordinary periodization. The unnormalized map of §4.4 multiplies this by the kernel mass. -/
theorem modulatedIsotypicPeriodizationQuotient_projector (ω : PontryaginDual K) (f : E) :
    T[ω] ((Pχ[ω]).ker.mkQ f) = Ψ[ω] (P f) ∧
      Pχ[ω] f = (μ₁.real univ : ℂ) • Ψ[ω] (P f) := by sorry

include hχ in
/-- Paper: Equation (4.5.1.12), p. 204. The induced periodization identifies
the kernel quotient topologically with the quotient isotype. -/
theorem modulatedIsotypicPeriodizationQuotient_equiv (ω : PontryaginDual K) :
    ∃ F : V[ω] ≃L[ℂ] Sχ[ω], ∀ v, (F v).val = T[ω] v := by sorry

include hχ in
/-- Paper: Proposition 4.5.1.1(4,6) and Corollary 4.5.1.6, pp. 198, 202–204.
Inclusion identifies the isotype modulo its cyclic differences with the full
decay space modulo homogeneous periodization. -/
theorem modulatedIsotypicPeriodizationQuotient_fromIsotype (ω : PontryaginDual K) :
    let H₀ := H[ω]
    let N := (H₀.map (Δ).toLinearMap).comap H₀.subtype
    ∃ F : (H₀ ⧸ N) ≃L[ℂ] V[ω], ∀ f : H₀, F (N.mkQ f) = (Pχ[ω]).ker.mkQ f.val := by sorry

/-- Paper: Equation (4.5.1.10), p. 204. The quotient functional multiplies the
Fourier coefficient of normalized periodization by the logarithmic period times
the kernel mass. For the compatible Weil measure this is the quotient volume. -/
def modulatedCyclicPairing (ω : PontryaginDual K) (n : ℤ) : StrongDual ℂ (V[ω]) :=
  volQ • (a (ω, n)).comp (T[ω])

local notation "b[" ω "]" => modulatedCyclicPairing m γ hm hms hγ μ₁ χ t₀ ht₀ ν ω
local notation "pairing[" ω "," n "," f "]" =>
  fun x : G ↦ (f).val x * star (e (ω, n) (q x))

include hχ hτ hμ hν in
/-- Paper: Equation (4.5.1.10), pp. 204–205. On a lift, the quotient functional
integrates the function against the corresponding annihilator character of G. -/
theorem modulatedCyclicPairing_mkQ (ω : PontryaginDual K) (n : ℤ) (f : E) :
    Integrable (pairing[ω, n, f]) μ ∧
      b[ω] n ((Pχ[ω]).ker.mkQ f) = ∫ x, pairing[ω, n, f] x ∂μ := by sorry

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.6, p. 204. For every enumeration of the integer
frequencies the integral functionals form an unconditional Schauder basis
of the strong dual of the kernel quotient. This dual represents the kernel annihilator. -/
theorem modulatedCyclicPairing_unconditionalBasis (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (V[ω])),
      IsSchauderBasis (b[ω] ∘ σ) c ∧
        SchauderBasis.IsUnconditional (b[ω] ∘ σ) c := by sorry

-- TODO(paper-gap): In Corollary 4.5.1.6 the full periodization depends on the
-- representative of the homogeneous kernel class. The unnormalized integral pairs to the
-- quotient volume against the matching unscaled exponential.

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.6 and Equation (4.5.1.11), p. 204. The
biorthogonal vectors form an absolute basis of the kernel quotient.
Deviation: Periodization uses isotypic representatives, and the displayed
exponentials are divided by the quotient Haar volume to match (4.5.1.10). -/
theorem modulatedIsotypicPeriodizationQuotient_absoluteBasis
    (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ v : ℕ → V[ω], IsSchauderBasis v (b[ω] ∘ σ) ∧
      SchauderBasis.IsAbsolute v (b[ω] ∘ σ) ∧
      ∀ n, T[ω] (v n) = volQ⁻¹ • e (ω, σ n) := by sorry

end QuotientIsotype

/-! ## 4.5.2 Support conditions -/

section Support

variable (B : Set ℝ≥0ˣ) (k : Subgroup G)

-- TODO(paper-gap): The opening of §4.5.2 uses a global completed projective
-- tensor isomorphism despite the compact-generation restriction in Remark 4.5.1.3.

/-- Paper: §4.5.2, p. 205. The fixed-support space consists of compactly supported
two-sided decay functions that vanish off the module window. For the paper's
compact windows their topological support also lies in the window.
Deviation: The support cylinder is written as the preimage of the window under
the module. For a section τ this is τ(B) times the norm-one group. -/
def modulatedCompactSupportSubmodule : Submodule ℂ E :=
  (bruhatCompactSupportSubmodule G).comap (modulatedExponentialDecaySubmodule m Set.univ).subtype ⊓
    ⨅ x : {x : G // m x ∉ B}, LinearMap.ker
      ((LinearMap.proj x.val).comp (modulatedExponentialDecaySubmodule m Set.univ).subtype)

/-- Paper: §4.5.2, p. 205. For a closed module window, membership in the
fixed-support space is equivalent to the stated condition on topological support. -/
theorem mem_modulatedCompactSupportSubmodule_iff (hB : IsClosed B) (f : E) :
    f ∈ modulatedCompactSupportSubmodule m B ↔
      HasCompactSupport f.val ∧ tsupport f.val ⊆ m ⁻¹' B := by sorry

/-- Paper: §4.5.2, p. 205. The fixed-support k-stage imposes k-invariance
on the supported decay space, with the topology inherited from the decay space. -/
def modulatedCompactSupportStage : Submodule ℂ E :=
  modulatedCompactSupportSubmodule m B ⊓ (schwartzBruhatInvariantSubmodule k).comap twist₀

/-- Paper: §4.5.2, p. 205. The stage consists of the supported functions
whose values are unchanged by translation by elements of k. -/
theorem mem_modulatedCompactSupportStage_iff (f : E) :
    f ∈ modulatedCompactSupportStage m B k ↔
      f ∈ modulatedCompactSupportSubmodule m B ∧
        ∀ (x : G) (u : k), f.val (u.val * x) = f.val x := by sorry

variable (hk : IsCompact (k : Set G))
variable (hperp : IsCompactlyGeneratedGroup (lcaAnnihilator (k.comap m.toMonoidHom.ker.subtype)))
variable (hB : IsCompact B) (hBi : (interior B).Nonempty)

include hSC hm hms hk hperp hB hBi in
/-- Paper: Proposition 4.5.2.1(1), p. 205. The fixed-support k-stage is
a closed subspace of the two-sided decay space. -/
theorem modulatedCompactSupportStage_isClosed :
    IsClosed (modulatedCompactSupportStage m B k : Set E) := by sorry

include hSC hm hms hk hperp hB hBi in
/-- Paper: Proposition 4.5.2.1(1), p. 205. The inherited topology on the
supported k-stage agrees with the fixed-support test-function topology on G/k.
Deviation: The test space is represented by the elementary structural pair
with open subgroup G and compact subgroup k, using the fixed-support stage of §D.3.6. -/
theorem modulatedCompactSupportStage_testFunction_equiv :
    ∃ (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (C : TopologicalSpace.Compacts G)
      (F : bruhatCompactSupportStage p e C ≃L[ℂ] modulatedCompactSupportStage m B k),
      p.val.1 = ⊤ ∧ OrderDual.ofDual p.val.2 = k ∧ (C : Set G) = m ⁻¹' B ∧
      ∀ f, (F f).val.val = schwartzBruhatStageRealization p e f.val := by sorry

-- Remark 4.5.2.2, p. 207, uses the Fréchet topology of this elementary
-- stage. See also modulatedExponentialDecayStage_frechet and
-- modulatedExponentialDecay_stageLimit in §D.3.3.

variable (a b : ℝ≥0ˣ)
variable (ha : 1 < a.val) (hwidth : Real.log ((m γ).val : ℝ) < 2 * Real.log (a.val : ℝ))

local notation "window" => Icc (b / a) (b * a)
local notation "W" => modulatedCompactSupportStage m window k

include hSC hm hms hγ ha hwidth in
/-- Paper: Proposition 4.5.2.1(2), p. 205. A module window wider than one
logarithmic period maps onto the cyclic quotient. -/
theorem modulatedCompactSupport_quotient_image :
    q '' (m ⁻¹' window) = (univ : Set Q) := by sorry

include hγ hwidth in
/-- Paper: Proposition 4.5.2.1(2), pp. 205–206. The interior of a strict-width
window already meets every orbit. -/
theorem modulatedCompactSupport_quotient_image_interior :
    q '' (m ⁻¹' interior window) = (univ : Set Q) := by sorry

include hk hperp ha hwidth in
/-- Paper: Proposition 4.5.2.1(2) and Equation (4.5.2.1), p. 205. On a window
wider than one period, the supported k-stage modulo the periodization kernel
is identified by periodization with the quotient test space on G/(γ^ℤ k). -/
theorem modulatedCompactSupportStage_periodization_equiv :
    let N := (P).ker.comap (W).subtype
    ∃ F : ((W) ⧸ N) ≃L[ℂ] SchwartzBruhat (G ⧸ (Γ ⊔ k)),
      ∀ (f : W) (x : G), F (N.mkQ f) (QuotientGroup.mk x) = P f.val (q x) := by sorry

-- TODO(paper-gap): Proposition 4.5.2.1(3) has a false support bound. For
-- G = ℝ_{>0}, γ = a > 1 and b = 1, its A is zero. A nonzero bump ψ in
-- (1, γ) gives φ(x) = ψ(x) - ψ(γx) in the kernel with the required support,
-- but a continuous ψ supported in {1} is zero.

/-- Paper: Proposition 4.5.2.1(3), pp. 205–207. A supported kernel element
has a k-invariant primitive supported over the window with its lower endpoint
multiplied by the generator's module.
Deviation: Forward and backward telescoping give this asymmetric interval
in place of the false symmetric bound. -/
theorem modulatedCompactSupportStage_exists_difference
    (f : W) (hf : P f.val = 0) :
    ∃ g : modulatedCompactSupportStage m (Icc (m γ * (b / a)) (b * a)) k,
      Δ g.val = f.val := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "D[" B "]" => modulatedCompactSupportSubmodule m B

-- TODO(paper-gap): Equation (4.5.2.2) is false for arbitrary compact windows
-- with interior. Already G = ℝ_{>0}, χ = 1, B = [1, γ] misses the constant
-- periodization, since a smooth function supported there vanishes at both endpoints.

variable (hcover : q '' (m ⁻¹' interior B) = (univ : Set Q))

include hB hcover in
/-- Paper: Theorem 4.5.2.3 and Equation (4.5.2.2), p. 207. The supported
homogeneous quotient is identified with the full quotient by inclusion.
Deviation: The interior of the compact module window must cover the quotient.
Every strict-width interval in part (2) satisfies this condition. -/
theorem modulatedCompactSupport_isotypicQuotient_equiv (ω : PontryaginDual K) :
    let N := (Pχ[ω]).ker.comap (D[B]).subtype
    ∃ F : ((D[B]) ⧸ N) ≃L[ℂ] V[ω],
      ∀ f : D[B], F (N.mkQ f) = (Pχ[ω]).ker.mkQ f.val := by sorry

include hk hperp hB hcover in
/-- Paper: Theorem 4.5.2.3 and Equation (4.5.2.2), p. 207. On a compact window
whose interior covers the quotient, inclusion identifies the two quotients of
k-invariant functions with their quotient topologies.
Deviation: Uses the interior coverage condition on the window. -/
theorem modulatedCompactSupportStage_isotypicQuotient_image (ω : PontryaginDual K) :
    let J : Submodule ℂ E := (schwartzBruhatInvariantSubmodule k).comap twist₀
    let W₀ := modulatedCompactSupportStage m B k
    let i : W₀ →ₗ[ℂ] J := Submodule.inclusion (inf_le_right : W₀ ≤ J)
    let N := (Pχ[ω]).ker.comap W₀.subtype
    let N' := (Pχ[ω]).ker.comap J.subtype
    ∃ F : (W₀ ⧸ N) ≃L[ℂ] (J ⧸ N'), ∀ f : W₀, F (N.mkQ f) = N'.mkQ (i f) := by sorry

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "bχ[" ω "]" => modulatedCyclicPairing m γ hm hms hγ μ₁ χ t₀ ht₀ ν ω

include hχ hτ hμ hν in
/-- Paper: Theorem 4.5.2.3(1), p. 207. The lattice integrals indexed by
the integer frequencies give an unconditional basis of the strong dual of
the homogeneous kernel quotient. -/
theorem modulatedCyclicPairing_int_unconditionalBasis (ω : PontryaginDual K) :
    ∃ c : ℤ → StrongDual ℂ (StrongDual ℂ (V[ω])),
      (∀ m n, c m (bχ[ω] n) = if m = n then 1 else 0) ∧
      ∀ u, HasSum (fun n ↦ c n u • bχ[ω] n) u := by sorry

include hχ hτ hμ hν hwidth in
/-- Paper: Theorem 4.5.2.3(2), pp. 207–208. Biorthogonal representatives can
be chosen with support in the wide module window. Their classes give an
absolute basis, and the induced integral functionals give an unconditional
basis of the strong dual of the supported quotient.
Deviation: The paper's integer family is expressed in an arbitrary enumeration,
as in Corollary 4.5.1.6. -/
theorem modulatedCompactSupport_isotypicQuotient_bases (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    let N := (Pχ[ω]).ker.comap (D[window]).subtype
    let U := (D[window]) ⧸ N
    ∃ (f : ℕ → D[window]) (c : ℕ → StrongDual ℂ U),
      (∀ n (g : D[window]), c n (N.mkQ g) = bχ[ω] (σ n) ((Pχ[ω]).ker.mkQ g.val)) ∧
      IsSchauderBasis (N.mkQ ∘ f) c ∧
      SchauderBasis.IsAbsolute (N.mkQ ∘ f) c ∧
      let d : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
        fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (N.mkQ (f n))
      IsSchauderBasis c d ∧ SchauderBasis.IsUnconditional c d := by sorry

end Support

/-! ## 4.5.3 Periodization for an open interval containing zero -/

section Interval

variable [MeasurableSpace G] [BorelSpace G]

local notation "S₀" => SchwartzBruhat G

include hγ in
/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208. Counting
measure on the discrete cyclic subgroup is regular Haar measure. -/
theorem modulatedCyclic_countingMeasure :
    (Measure.count : Measure Γ).IsHaarMeasure ∧ (Measure.count : Measure Γ).Regular := by sorry

local notation "cosetPeriodization" => (fun f : S₀ ↦
  letI := (modulatedCyclic_countingMeasure m γ hγ).1
  letI := (modulatedCyclic_countingMeasure m γ hγ).2
  schwartzBruhatCosetIntegral Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ) f)

include hSC in
/-- Paper: Equation (4.5.3.2), p. 208. The coset integral of §D.1.7
with counting measure is linear and continuous on ordinary Schwartz–Bruhat functions. -/
theorem schwartzBruhatCyclicPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ cosetPeriodization ∧ Continuous cosetPeriodization := by sorry

/-- Paper: Equation (4.5.3.2), p. 208. Ordinary Schwartz–Bruhat periodization
is the coset integral with respect to counting measure on the cyclic subgroup. -/
def schwartzBruhatCyclicPeriodization : S₀ →L[ℂ] S :=
  let h := schwartzBruhatCyclicPeriodization_isLinearMap_continuous m γ hγ
  ⟨IsLinearMap.mk' cosetPeriodization h.1, h.2⟩

local notation "P₀" => schwartzBruhatCyclicPeriodization m γ hγ

/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208. At any lift of
a quotient point the cyclic sum converges to the coset integral. -/
theorem schwartzBruhatCyclicPeriodization_hasSum (f : S₀) (x : G) :
    HasSum (fun n : ℤ ↦ f (γ ^ n * x)) (P₀ f (q x)) := by sorry

/-- Paper: Corollary 4.5.3.1, p. 208. The ordinary Schwartz–Bruhat
periodization is surjective. -/
theorem schwartzBruhatCyclicPeriodization_surjective : Surjective P₀ := by sorry

/-- Paper: Corollary 4.5.3.1, p. 208. The ordinary Schwartz–Bruhat
periodization is open. -/
theorem schwartzBruhatCyclicPeriodization_isOpenMap : IsOpenMap P₀ := by sorry

variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (h0 : 0 ∈ I)

local notation "D" => ModulatedExponentialDecay m I
local notation "zeroI" => (⟨0, h0⟩ : I)
local notation "j₀" => modulatedExponentialDecayTwist m I zeroI
local notation "ΔI" => modulatedCyclicDifference m γ hm hms I hInt (⟨0, h0⟩ : I.Nonempty)

include hSC hm hms hInt in
/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208.
At exponent zero the canonical inclusion into ordinary Schwartz–Bruhat
functions is continuous. -/
theorem modulatedExponentialDecay_zeroTwist_continuous :
    Continuous (fun f : D ↦ (j₀ f : S₀)) := by sorry

/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208.
The zero twist preserves pointwise values and is the injective inclusion
of the interval decay space into ordinary Schwartz–Bruhat functions. -/
theorem modulatedExponentialDecay_zeroTwist_injective :
    Injective j₀ ∧ ∀ (f : D) (x : G), j₀ f x = f.val x := by sorry

/-- Paper: Equation (4.5.3.1), p. 208. Periodization at an interval containing
zero composes the zero twist with ordinary Schwartz–Bruhat periodization. -/
def modulatedIntervalPeriodization : D →L[ℂ] S :=
  let j : D →L[ℂ] S₀ :=
    ⟨j₀, modulatedExponentialDecay_zeroTwist_continuous m hm hms I hInt h0⟩
  (P₀).comp j

local notation "PI" => modulatedIntervalPeriodization m γ hm hms hγ I hInt h0

/-- Paper: Equation (4.5.3.1), p. 208. At a lift of a quotient point the
orbit series for an interval-decaying function converges to its periodization. -/
theorem modulatedIntervalPeriodization_hasSum (f : D) (x : G) :
    HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) (PI f (q x)) := by sorry

include hOpen in
/-- Paper: Corollary 4.5.3.1 and Equations (4.5.3.1)–(4.5.3.2), p. 208.
The periodization is surjective, uniquely characterized by the diagram,
and extends two-sided exponential periodization along the canonical inclusion. -/
theorem modulatedIntervalPeriodization_factorization :
    ∃ i : E →L[ℂ] D,
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f, PI (i f) = P f) ∧
      Surjective PI ∧
      ∀ T : D →L[ℂ] S, T.comp i = P → T = PI := by sorry

section ProjectivePeriodization

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

open UniformSpace in
open scoped TensorProduct in
/-- Paper: Remarks 4.5.1.2 and 4.5.1.4, pp. 198, 203. Periodization on the
projective tensor completion is sequentially continuous and surjective. The
induced bijection has a sequentially continuous inverse.
Deviation: The interval contains zero. The tensor factors are ordered as in
modulatedExponentialDecay_tensor_equiv. General forward continuity fails. -/
theorem modulatedIntervalPeriodization_projective
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (e : Completion (InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)) ≃L[ℂ] D)
    (he : ∀ (h : SchwartzBruhat K) (p : PositiveRealExponentialDecay I) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I))
        (h ⊗ₜ[ℂ] p))).val (u.val * τ t) = h u * p.val (Real.log (t.val : ℝ))) :
    let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
    let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
    ∃ A : Completion TP →ₗ[ℂ] S, SeqContinuous A ∧ Surjective A ∧
      (∀ z : Completion TI, A (@Completion.map TI _ TP _ id z) = PI (e z)) ∧
      ∃ B : S ≃ₗ[ℂ] ((Completion TP) ⧸ A.ker),
        SeqContinuous B ∧ ∀ z, B (A z) = A.ker.mkQ z := by sorry

end ProjectivePeriodization

-- TODO(paper-gap): Remark 4.5.1.4, p. 203, calls the forward quotient
-- bijection continuous. For an infinite product of copies of ℤ/2, the
-- quotient Schwartz space admits a continuous seminorm testing derivative
-- order j at the jth coordinate character. On a fixed compact set no single
-- continuous radial seminorm controls all those derivative orders.

-- TODO(paper-gap): In (4.5.3.6) the ordinary Schwartz–Bruhat quotient map
-- has the interval decay space printed in its codomain. On p. 208 the
-- proof uses the equality of the difference image with the pulled-back
-- closed range before justifying it.

include hOpen in
/-- Paper: Corollary 4.5.3.1(1), p. 208. On the interval decay space the
periodization kernel is exactly the range of the cyclic difference. -/
theorem modulatedIntervalPeriodization_ker_eq_range :
    (PI).ker = (ΔI).range := by sorry

include hOpen in
/-- Paper: Corollary 4.5.3.1(1), pp. 208–209. The difference range in the
interval decay space is closed and restricts to the difference range on each isotype. -/
theorem modulatedIntervalDifference_range_isotype (ω : PontryaginDual K) :
    let H := (actionIsotype ((ρG).comp (K).subtype) ω).comap j₀
    (PI).ker ⊓ H = H.map (ΔI).toLinearMap := by sorry

/-- Paper: Equation (4.5.3.3), p. 208. The cyclic difference on the ordinary
Schwartz–Bruhat space subtracts left translation by the inverse generator. -/
def schwartzBruhatCyclicDifference : S₀ →L[ℂ] S₀ :=
  ContinuousLinearMap.id ℂ S₀ - ρG γ⁻¹

local notation "Δ₀" => schwartzBruhatCyclicDifference γ

/-- Paper: Equation (4.5.3.3), p. 208. The ordinary cyclic difference at x
subtracts the function's value at γx. -/
theorem schwartzBruhatCyclicDifference_apply (f : S₀) (x : G) :
    Δ₀ f x = f x - f (γ * x) := by sorry

include hm hms in
/-- Paper: Corollary 4.5.3.1(2), pp. 208–209. On ordinary Schwartz–Bruhat
functions the periodization kernel is exactly the range of the cyclic difference. -/
theorem schwartzBruhatCyclicPeriodization_ker_eq_range :
    (P₀).ker = (Δ₀).range := by sorry

include hm hms in
/-- Paper: Corollary 4.5.3.1(2), pp. 208–209. On each ordinary
Schwartz–Bruhat isotype the kernel consists of differences of functions of that isotype. -/
theorem schwartzBruhatCyclicDifference_range_isotype (ω : PontryaginDual K) :
    let H := actionIsotype ((ρG).comp (K).subtype) ω
    (P₀).ker ⊓ H = H.map (Δ₀).toLinearMap := by sorry

include hOpen hγ in
/-- Paper: Corollary 4.5.3.1, (4.5.3.4)–(4.5.3.6), pp. 208–209. The two
inclusions identify the quotients by the three difference ranges, as used
in Corollary 4.6.3.1. Both maps send each function to its own class. -/
theorem modulatedIntervalDifference_quotient_equivs :
    ∃ (i : E →L[ℂ] D)
      (F : (E ⧸ (Δ).range) ≃L[ℂ] (D ⧸ (ΔI).range))
      (J : (D ⧸ (ΔI).range) ≃L[ℂ] (S₀ ⧸ (Δ₀).range)),
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f : E, F ((Δ).range.mkQ f) = (ΔI).range.mkQ (i f)) ∧
      ∀ g : D, J ((ΔI).range.mkQ g) = (Δ₀).range.mkQ (j₀ g) := by sorry

end Interval

end RiemannMasullo
