module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoisson
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.Ch12_TraceGeometric.Sec5
/-! # Finite certificates from translated Poisson mass

Hiary, Ireland and Kyi, *A method for verifying the generalized Riemann hypothesis*
(2024), §5, Theorem 11 and Lemma 3, use a translated logarithmic derivative and
lower bounds from intervals containing verified zeros. Here the sites and
multiplicities are those of a single completed Hecke function of a number field.
-/

@[expose] public noncomputable section

open Classical Function MeasureTheory NumberField Set
open scoped ComplexConjugate NNReal

namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z

set_option maxHeartbeats 1000000 in
/-- The finite multiset of certified central copies. A point can occur up to its
actual multiplicity. Only copies in the support need verified ordinate bounds. -/
structure CentralBrackets (χ : U𝔽) where
  copies : Site χ →₀ ℕ
  left : Site χ → ℝ
  right : Site χ → ℝ
  copies_le : ∀ z : Site χ, copies z ≤ multiplicity (χ := χ) z
  verified : ∀ z : Site χ, z ∈ copies.support →
    z.val.re = 1 / 2 ∧ z.val.im ∈ Icc (left z) (right z)

namespace CentralBrackets


/-- Certified contribution of the brackets at center `t`, with multiplicity. -/
def lowerMass {χ : U𝔽} (B : CentralBrackets χ) (t : ℝ) : ℝ :=
  ∑ z ∈ B.copies.support, (B.copies z : ℝ) * bracketLowerBound t (B.left z) (B.right z)

private def credit {χ : U𝔽} (B : CentralBrackets χ) (t : ℝ) (z : Site χ) : ℝ :=
  (B.copies z : ℝ) * bracketLowerBound t (B.left z) (B.right z)

private theorem hasSum_credit {χ : U𝔽} (B : CentralBrackets χ) (t : ℝ) : HasSum (B.credit t) (B.lowerMass t) :=
  hasSum_sum_of_ne_finset_zero (s := B.copies.support) (fun z hz ↦ by
    simp [credit, Finsupp.notMem_support_iff.mp hz])

private theorem credit_le_weight {χ : U𝔽} (B : CentralBrackets χ) (t : ℝ) (z : Site χ) :
    B.credit t z ≤ (B.copies z : ℝ) * weight t z.val := by
  by_cases hz : z ∈ B.copies.support
  · exact mul_le_mul_of_nonneg_left
      (weight_central_bracket t (B.left z) (B.right z) z.val (B.verified z hz).1
        (B.verified z hz).2) (Nat.cast_nonneg _)
  · simp [credit, Finsupp.notMem_support_iff.mp hz]

private theorem credit_le {χ : U𝔽} (B : CentralBrackets χ) (t : ℝ) (z : Site χ) : B.credit t z ≤ siteWeight t z :=
  (B.credit_le_weight t z).trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast B.copies_le z) (weight_nonneg t z.val (siteStrip z)))

private theorem credit_off_line {χ : U𝔽} (B : CentralBrackets χ) (t : ℝ) (z : Site χ) (hz : z.val.re ≠ 1 / 2) :
    B.credit t z = 0 := by
  have h : z ∉ B.copies.support := fun h ↦ hz (B.verified z h).1
  simp [credit, Finsupp.notMem_support_iff.mp h]

end CentralBrackets

private theorem pair_le_residual {χ : U𝔽} {t m c : ℝ} {credit : Site χ → ℝ}
    (hm : HasSum (siteWeight (χ := χ) t) m) (hc : HasSum credit c)
    (hle : ∀ z, credit z ≤ siteWeight t z) (hoff : ∀ z, z.val.re ≠ 1 / 2 → credit z = 0)
    (z : Site χ) (hz : z.val.re ≠ 1 / 2) :
    weight t z.val + weight t (1 - conj z.val) ≤ m - c := by
  let r : Site χ := positiveSiteReflection χ z
  have hre : r.val.re = 1 - z.val.re := by
    change (1 - conj z.val).re = _
    simp
  have hr : r.val.re ≠ 1 / 2 := fun he ↦ hz (by linarith)
  have hne : z ≠ r := fun e ↦ hz (by
    have he := congrArg (fun q : Site χ ↦ q.val.re) e
    linarith)
  have hs := hm.sub hc
  have hpair := hs.summable.sum_le_tsum ({z, r} : Finset (Site χ))
    (fun i _ ↦ sub_nonneg.mpr (hle i))
  simp only [Finset.mem_singleton, hne, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, hoff z hz, hoff r hr, sub_zero, hs.tsum_eq] at hpair
  exact (add_le_add (weight_le_siteWeight t z) (weight_le_siteWeight t r)).trans hpair

/-- If the residual after the verified brackets is at most `6/5`, every zero in
the closed unit cell lies on the central line. Each off-line site and its
distinct reflection for the same character would cost strictly more. -/
theorem cell_central_of_brackets {χ : U𝔽} (B : CentralBrackets χ) {t m : ℝ}
    (hm : HasSum (siteWeight (χ := χ) t) m) (hbudget : m - B.lowerMass t ≤ 6 / 5)
    (z : Site χ) (hcell : |z.val.im - t| ≤ 1 / 2) : z.val.re = 1 / 2 := by
  by_contra hz
  exact (not_le_of_gt (weight_reflected_cell_lt t z.val (siteStrip z) hcell hz))
    ((pair_le_residual hm (B.hasSum_credit t) (B.credit_le t) (B.credit_off_line t) z hz).trans
      hbudget)

/-- Below the cost of one central copy the bracket multiplicities exhaust the
divisor at every site in the closed cell, including sites already witnessed. -/
theorem cell_multiplicity_of_brackets {χ : U𝔽} (B : CentralBrackets χ) {t m : ℝ}
    (hm : HasSum (siteWeight (χ := χ) t) m) (hbudget : m - B.lowerMass t < 3 / 5)
    (z : Site χ) (hcell : |z.val.im - t| ≤ 1 / 2) : multiplicity z = B.copies z := by
  have hz := cell_central_of_brackets B hm (by linarith) z hcell
  by_contra he
  have hl : B.copies z + 1 ≤ multiplicity z := by
    have := B.copies_le z
    omega
  have hr : (B.copies z : ℝ) + 1 ≤ (multiplicity z : ℝ) := by exact_mod_cast hl
  have hslack := mul_le_mul_of_nonneg_right hr (weight_nonneg t z.val (siteStrip z))
  have hs := hm.sub (B.hasSum_credit t)
  have hb := hs.summable.le_tsum z (fun i _ ↦ sub_nonneg.mpr (B.credit_le t i))
  rw [hs.tsum_eq] at hb
  change siteWeight t z - B.credit t z ≤ _ at hb
  unfold siteWeight at hb
  rw [add_mul, one_mul] at hslack
  linarith [weight_central_cell t z.val hz hcell, B.credit_le_weight t z]

/-- Pole-cleared arithmetic logarithmic derivative at `2 + t i` for a character
trivial on the chosen norm section. The completed continuation omits the
conductor power; the principal character has poles at zero and one. -/
def normalizedLogDerivative (χ : U𝔽) (t : ℝ) : ℝ :=
  let s : ℂ := 2 + (t : ℂ) * Complex.I
  heckeLogDiscriminantConductor χ / 2 + (logDeriv (continuedCompletedHeckeL χ) s).re +
    if χ = 1 then (1 / s + 1 / (s - 1)).re else 0

/-- Finite-height exclusion from the translated explicit formula and a
certified upper bound at each center in a finite cover of `[a,b]`. -/
theorem interval_central_of_arithmetic_brackets {χ : U𝔽} (a b : ℝ) (T : Finset ℝ)
    (hcover : ∀ y ∈ Icc a b, ∃ t ∈ T, |y - t| ≤ 1 / 2)
    (B : ℝ → CentralBrackets χ) (U : ℝ → ℝ)
    (hformula : ∀ t ∈ T, HasSum (siteWeight (χ := χ) t) (normalizedLogDerivative χ t))
    (hupper : ∀ t ∈ T, normalizedLogDerivative χ t ≤ U t)
    (hbudget : ∀ t ∈ T, U t - (B t).lowerMass t ≤ 6 / 5)
    (z : Site χ) (hz : z.val.im ∈ Icc a b) : z.val.re = 1 / 2 := by
  obtain ⟨t, ht, hcell⟩ := hcover _ hz
  exact cell_central_of_brackets (B t) (hformula t ht)
    ((sub_le_sub_right (hupper t ht) _).trans (hbudget t ht)) z hcell

/-- Central contribution of a site, set to zero off the line. -/
def centralTerm {χ : U𝔽} (t : ℝ) : Site χ → ℝ :=
  {z : Site χ | z.val.re = 1 / 2}.indicator (siteWeight t)

/-- Mass of all actual central sites at the translated point, with their full
divisor multiplicities, whether or not individual sites have been located. -/
def centralMass (χ : U𝔽) (t : ℝ) : ℝ := ∑' z : Site χ, centralTerm t z

/-- The whole critical-line assertion for a fixed character is equivalent to
the absolute threshold `6/5` at the integer centers. Equality is allowed:
a distinct reflected pair costs strictly more even on a shared cell edge. -/
theorem criticalLine_iff_integer_deficit (χ : U𝔽) (m : ℤ → ℝ)
    (hm : ∀ k : ℤ, HasSum (siteWeight (χ := χ) k) (m k)) :
    (∀ z : Site χ, z.val.re = 1 / 2) ↔ ∀ k : ℤ, m k - centralMass χ k ≤ 6 / 5 := by
  constructor
  · intro h k
    have he : centralTerm (χ := χ) k = siteWeight k := by
      funext z
      exact Set.indicator_of_mem (h z : z ∈ {q : Site χ | q.val.re = 1 / 2}) _
    simp only [centralMass, he, (hm k).tsum_eq, sub_self]
    norm_num
  · intro hb z
    by_contra hz
    obtain ⟨k, hcell⟩ := exists_int_cell z.val.im
    have hs : HasSum (centralTerm (χ := χ) k) (centralMass χ k) :=
      ((hm k).summable.indicator {q : Site χ | q.val.re = 1 / 2}).hasSum
    have hle (q : Site χ) : centralTerm k q ≤ siteWeight k q := by
      by_cases h : q.val.re = 1 / 2
      · exact (Set.indicator_of_mem (h : q ∈ {j : Site χ | j.val.re = 1 / 2}) _).le
      · rw [centralTerm, Set.indicator_of_notMem (h : q ∉ {j : Site χ | j.val.re = 1 / 2})]
        exact siteWeight_nonneg _ q
    have hoff (q : Site χ) (h : q.val.re ≠ 1 / 2) : centralTerm k q = 0 := by
      exact Set.indicator_of_notMem (h : q ∉ {j : Site χ | j.val.re = 1 / 2}) _
    exact (not_le_of_gt (weight_reflected_cell_lt k z.val (siteStrip z) hcell hz))
      ((pair_le_residual (hm k) hs hle hoff z hz).trans (hb k))

/-- The complete Poisson sum at the point `2 + t i`, including every positive
divisor site with its multiplicity. -/
def fullMass (χ : U𝔽) (t : ℝ) : ℝ := ∑' z : Site χ, siteWeight t z

/-- The integer test for one character requires no analytic formula: both
real Poisson series converge unconditionally. -/
theorem criticalLine_iff_integer_mass (χ : U𝔽) :
    (∀ z : Site χ, z.val.re = 1 / 2) ↔
      ∀ k : ℤ, fullMass χ k - centralMass χ k ≤ 6 / 5 :=
  criticalLine_iff_integer_deficit χ _ (fun k ↦ (summable_siteWeight χ k).hasSum)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
set_option quotPrecheck false in
local notation "ext(" σ ", " a ")" =>
  {p : {η : U𝔽 // ∀ u : ℝ≥0ˣ, η (σ u) = 1} × ℂ //
    0 < ord(p.1.val, p.2) ∧ (a : ℝ) ≤ |p.2.re - 1 / 2|}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

/-- The omitted-zero cancellation in Theorem 12.5.1.1, at one half-width. -/
def exteriorCancellation (σ : ℝ≥0ˣ →ₜ* C𝔽) (a : ℝ) : Prop :=
  ∀ φ : BruhatCompactSupport C𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    HasSum (fun z : ext(σ, a) ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
      ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g
        ∂ideleClassTamagawaMeasure F) 0

private theorem exteriorCancellation_iff_empty (σ : ℝ≥0ˣ →ₜ* C𝔽)
    (hσ : RightInverse σ (ideleClassNorm F)) (a : ℝ) :
    exteriorCancellation σ a ↔ IsEmpty ext(σ, a) := by
  simpa only [exteriorCancellation, modulatedFourierMellin, relativeVerticalStrip,
    Set.preimage_univ, Set.indicator_univ] using hasSum_exteriorZeros_iff_isEmpty σ hσ a

/-- The all-width omitted-zero cancellation of Theorem 12.5.1.1 is equivalent
to one numerical threshold at the integer ordinates for each normalized
character. Both sides use the actual divisor of the same completed function. -/
theorem all_widths_iff_integer_mass (σ : ℝ≥0ˣ →ₜ* C𝔽)
    (hσ : RightInverse σ (ideleClassNorm F)) :
    (∀ a > 0, exteriorCancellation σ a) ↔
      ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (σ u) = 1) →
        ∀ k : ℤ, fullMass χ k - centralMass χ k ≤ 6 / 5 := by
  constructor
  · intro h χ hχ
    apply (criticalLine_iff_integer_mass χ).mp
    intro z
    by_contra hz
    have he := (exteriorCancellation_iff_empty σ hσ _).mp
      (h |z.val.re - 1 / 2| (abs_pos.mpr (sub_ne_zero.mpr hz)))
    exact he.false ⟨(⟨χ, hχ⟩, z.val), z.property, le_rfl⟩
  · intro h a ha
    apply (exteriorCancellation_iff_empty σ hσ a).mpr
    refine ⟨fun z ↦ ?_⟩
    have he := (criticalLine_iff_integer_mass z.val.1.val).mpr
      (h z.val.1.val z.val.1.property) ⟨z.val.2, z.property.1⟩
    change z.val.2.re = 1 / 2 at he
    have := z.property.2
    rw [he, sub_self, abs_zero] at this
    exact (not_le_of_gt ha) this

/-- With the translated explicit formula supplied, the same all-width
criterion compares the pole-cleared arithmetic logarithmic derivative with
the complete central-line contribution at integer centers. -/
theorem all_widths_iff_integer_logDerivative (σ : ℝ≥0ˣ →ₜ* C𝔽)
    (hσ : RightInverse σ (ideleClassNorm F))
    (hformula : ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (σ u) = 1) →
      ∀ k : ℤ, HasSum (siteWeight (χ := χ) k) (normalizedLogDerivative χ k)) :
    (∀ a > 0, exteriorCancellation σ a) ↔
      ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (σ u) = 1) →
        ∀ k : ℤ, normalizedLogDerivative χ k - centralMass χ k ≤ 6 / 5 := by
  rw [all_widths_iff_integer_mass σ hσ]
  constructor <;> intro h χ hχ k <;>
    simpa only [fullMass, (hformula χ hχ k).tsum_eq] using h χ hχ k

end RiemannMasullo.HeckePoisson
