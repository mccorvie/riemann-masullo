module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Comparisons for the exponential system on monogenic quotients

Masullo, §4.4.2, pp. 191–194. The two descriptions of the annihilator use
inverse characters. In the positive-real case, normalized logarithmic
coordinates identify the quotient with the unit circle used in §4.2.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G) (hm : IsModulation m) (hms : Surjective m)
  (hγ : 1 < (m γ).val)

local notation "K" => m.toMonoidHom.ker

/-- Paper: Equation (4.4.2.4), p. 193, and Remark D.3.5.2, pp. 818–819.
With the same lifts, phases and integer indices, the §4.4 quotient character
pulled back to the original group is the pointwise inverse of the appendix character.
Deviation: This makes the comparison of the two parametrizations explicit. -/
theorem modulatedCyclicCharacter_eq_inv_zpowers_annihilator
    (χ : PontryaginDual K → PontryaginDual G)
    (hχ : ∀ (ω : PontryaginDual K) (k : K), χ ω k.val = ω k)
    (t₀ : PontryaginDual K → ℝ)
    (ht₀ : let L := Real.log ((m γ).val : ℝ)
      ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ ω * L) = χ ω γ)
    (j : PontryaginDual K × ℤ) (x : G) :
    let a := (modulatedCharacter_zpowers_annihilator m hm hms γ hγ χ hχ t₀ ht₀).choose
    modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk x) = ((a j).val x)⁻¹ := by
  sorry

/-- Paper: Definition 4.4.2.1, pp. 191–192, and Proposition 4.5.1.1(1), p. 197.
The ordinary orbit sum is complex-linear on the two-sided decay space. -/
theorem modulatedPeriodization_isLinearMap :
    IsLinearMap ℂ (modulatedPeriodization m γ hm hms hγ) := by sorry

variable [MeasurableSpace G] [BorelSpace G]

/-- Paper: Definition 4.4.2.1, pp. 191–192, and Proposition 4.5.1.1(3), p. 198.
The character-weighted orbit sum is complex-linear on the two-sided decay space. -/
theorem modulatedIsotypicPeriodization_isLinearMap (μ₁ : Measure K) [μ₁.IsHaarMeasure]
    (χ : PontryaginDual G) :
    IsLinearMap ℂ (modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ) := by sorry

end Modulated

section PositiveReal

local notation "m" => ContinuousMonoidHom.id ℝ≥0ˣ
local notation "K" => MonoidHom.ker (ContinuousMonoidHom.toMonoidHom m)
local notation "χ₀" => (fun _ : PontryaginDual K ↦ (1 : PontryaginDual ℝ≥0ˣ))
local notation "t₀" => (fun _ : PontryaginDual K ↦ (0 : ℝ))
local notation "T" => AddCircle (1 : ℝ)
local notation "S" => ElementarySchwartz 0 1 0 (PUnit : Type)
local notation "point" z => ((0, fun _ : Fin 1 ↦ z, 0, PUnit.unit) :
  ElementaryLieGroup 0 1 0 (PUnit : Type))

/-- Paper: Example D.3.3.4, p. 805. The positive reals with the identity module
are a modulated group. -/
theorem identityModulation_isModulation : IsModulation m :=
  ⟨isProperMap_id, exists_ne 1⟩

variable (γ : ℝ≥0ˣ) (hγ : 1 < γ.val)

local notation "Q[" g "]" => ℝ≥0ˣ ⧸ Subgroup.zpowers g
local notation "L[" g "]" => Real.log ((Units.val g : ℝ≥0) : ℝ)

include hγ in
/-- Paper: Situation 4.4.2.3(5), p. 192, and Remark 4.4.2.8, p. 194.
For the trivial lift, the prescribed phase is zero. -/
theorem positiveRealCyclic_trivialPhase :
    ∀ ω : PontryaginDual K, t₀ ω ∈ Ico 0 (2 * Real.pi / L[γ]) ∧
      Circle.exp (t₀ ω * L[γ]) = χ₀ ω γ := by
  intro ω
  have hL : 0 < L[γ] := Real.log_pos (by exact_mod_cast hγ)
  refine ⟨⟨le_rfl, div_pos (by positivity) hL⟩, ?_⟩
  simp

include hγ in
/-- Paper: Definition 4.2.1.1, p. 162, and Remark 4.4.2.8, p. 194.
The two Schwartz topologies on the positive-real cyclic quotient agree under
the coordinate log(t) / log(γ) modulo one.
Deviation: The paper uses the same space for both models. Lean states their
continuous linear equivalence and specifies it by evaluation on representatives. -/
theorem positiveRealCyclicSchwartz_equiv :
    ∃ A : SchwartzBruhat Q[γ] ≃L[ℂ] S, ∀ (f : SchwartzBruhat Q[γ]) (t : ℝ≥0ˣ),
      A f (point ((L[t] / L[γ] : ℝ) : T)) = f (QuotientGroup.mk t) := by sorry

variable (A : SchwartzBruhat Q[γ] ≃L[ℂ] S)
  (hA : ∀ (f : SchwartzBruhat Q[γ]) (t : ℝ≥0ˣ),
    A f (point ((L[t] / L[γ] : ℝ) : T)) = f (QuotientGroup.mk t))

include hA

/-- Paper: Equations (4.2.1.3), p. 162, and (4.4.2.5), p. 193.
In normalized logarithmic coordinates the trivial-lift exponential of §4.4
at index n is the §4.2 exponential at index −n.
Deviation: This makes the change of index between the two conventions explicit. -/
theorem modulatedCyclicExponential_positiveReal (n : ℤ) :
    A (modulatedCyclicExponential m γ identityModulation_isModulation hγ χ₀ t₀
      (positiveRealCyclic_trivialPhase γ hγ) (1, n)) = cyclicExponential (-n) := by sorry

local instance instBorelSpacePositiveRealsSec4b : BorelSpace ℝ≥0ˣ :=
  borelSpace_units_of_continuousInv₀ ℝ≥0
local instance instMeasurableSpaceCyclicQuotientSec4b : MeasurableSpace Q[γ] := borel _

variable (μ₁ : Measure K) [μ₁.IsHaarMeasure]

/-- Paper: Equations (4.2.1.4), p. 162, and (4.4.2.6), p. 193, and Remark 4.4.2.7, p. 194.
With the stated quotient Haar mass, the trivial-lift coefficient at index n
is the pullback of the probability Haar Fourier coefficient at index −n.
Deviation: The quotient measure is specified by its Haar mass, and the index
change and transport between the two models are explicit. -/
theorem modulatedCyclicFourierCoeff_positiveReal (ν : Measure Q[γ]) [ν.IsHaarMeasure]
    (hν : ν univ = ENNReal.ofReal L[γ] * μ₁ univ) (n : ℤ) :
    modulatedCyclicFourierCoeff m γ identityModulation_isModulation hγ χ₀ t₀
      (positiveRealCyclic_trivialPhase γ hγ) μ₁ ν (1, n) =
        (cyclicFourierCoeff (-n)).comp A.toContinuousLinearMap := by sorry

local notation "logProfiles" =>
  Exists.choose (identityModulationExponentialDecay_equiv univ ordConnected_univ univ_nonempty)

/-- Paper: Definitions 4.2.1.1, p. 162, and 4.4.2.1, pp. 191–192.
The ordinary periodizations agree under the logarithmic identification of
the sources and the normalized logarithmic identification of the targets.
Deviation: The comparison makes the coordinate transports explicit. -/
theorem modulatedPeriodization_positiveReal (f : PositiveRealExponentialDecay univ) :
    A (modulatedPeriodization m γ identityModulation_isModulation surjective_id hγ
      (logProfiles f)) = cyclicPeriodization γ.val (NNReal.coe_lt_coe.mpr hγ) f := by sorry

/-- Paper: Definitions 4.2.1.1, p. 162, and 4.4.2.1, pp. 191–192.
After the same coordinate transports, trivial-character periodization is the
§4.2 periodization multiplied by the Haar mass of the trivial norm-one group.
Deviation: The comparison makes the coordinate transports and mass factor explicit. -/
theorem modulatedIsotypicPeriodization_positiveReal (f : PositiveRealExponentialDecay univ) :
    A (modulatedIsotypicPeriodization m γ identityModulation_isModulation surjective_id hγ
      μ₁ 1 (logProfiles f)) =
        (μ₁.real univ : ℂ) • cyclicPeriodization γ.val (NNReal.coe_lt_coe.mpr hγ) f := by sorry

end PositiveReal

end RiemannMasullo
