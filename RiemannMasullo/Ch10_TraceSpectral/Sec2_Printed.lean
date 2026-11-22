module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # §10.2 assertions that are false as printed -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1

set_option quotPrecheck false

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "order(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "weight(" F ", " α ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)

local notation "lineWeight(" F ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)
local notation "floorCut(" s ", " N ")" => min N (Nat.floor ((s - 1) / 2 + 1))
local notation "stripFloor(" α ", " s ", " b ", " N ")" =>
  (if b = -α ∨ b = α then floorCut(s, N) else if b ∈ Ioo (-α) α then N else 0)

/-- Paper: Theorem 10.2.1.1, p. 440. For the printed index set the jets
belong to the negative line space and, in any enumeration, are the
functional half of a Markushevich basis of the theta quotient. -/
def Printed.spectralLineMarkushevichBasis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        ∀ j, D (Λ j) = (h j).toLp (η j)

/-- Paper: Theorem 10.2.1.1, p. 440. The squared Artin factor of the
splitting field of X³−2 supplies a double zero. At s = 3 its first
derivative is among the printed jets and fails square integrability. -/
theorem Printed.spectralLineMarkushevichBasis_false :
    ¬ Printed.spectralLineMarkushevichBasis := by sorry

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. The printed floor cutoff
makes each selected jet belong to the negative Sobolev space on the line. -/
def Printed.spectralLineJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
    k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
    MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s))

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. Take the splitting
field of X³−2, the trivial character, s = 3, and a+it a nontrivial zero of the
two-dimensional Artin factor. That factor occurs squared in the Dedekind
zeta function. The cutoff includes k = 1, whose squared norm has a 1/|x|
tail in the log norm coordinate x. -/
theorem Printed.spectralLineJet_memLp_false : ¬ Printed.spectralLineJet_memLp := by sorry

/-- Paper: Proposition 10.2.1.3, p. 443. The printed annulus statement uses
all derivative orders below the full zero multiplicity. -/
def Printed.spectralLineJet_annulus : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      let η := spectralZeroJet (χ ω) 0 t k
      ∃ h : MemLp η 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp η‖ ∧ ‖h.toLp η‖ ≤ C

/-- Paper: Proposition 10.2.1.3, p. 443. In the splitting field of X³−2
use the trivial character and a nontrivial zero of its squared two-dimensional
Artin factor. For s = 3 the printed full multiplicity includes k = 1 and the
squared norm diverges logarithmically. -/
theorem Printed.spectralLineJet_annulus_false : ¬ Printed.spectralLineJet_annulus := by sorry

/-- Paper: Proposition 10.2.1.3, p. 443. As printed, the a-line family
fails to be contained in an open ball of some positive radius. -/
def Printed.spectralLineJet_not_subset_ball : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. Take F = ℚ, a = 2 and s = 2.
All the completed Hecke L-functions are zero-free on this line by the
absolutely convergent Euler products and the nonvanishing gamma factors.
The resulting empty family is contained in every open ball. -/
theorem Printed.spectralLineJet_not_subset_ball_false :
    ¬ Printed.spectralLineJet_not_subset_ball := by sorry

/-- Paper: Proposition 10.2.1.3, p. 443. One constant gives (10.2.1.12)
and the asserted noncontainment for the family with full multiplicities. -/
def Printed.spectralLineJet_annulus_and_noncontainment : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s →
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ // j.2.2 < order(χ j.1, shift(a, j.2.1))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      ∃ C : ℝ, 0 < C ∧
        (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp (η j)‖ ∧ ‖h.toLp (η j)‖ ≤ C) ∧
        ¬ (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), ‖h.toLp (η j)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. For ℚ at a = 2 the zero
family is empty and hence lies in the open ball for every C > 0. -/
theorem Printed.spectralLineJet_annulus_and_noncontainment_false :
    ¬ Printed.spectralLineJet_annulus_and_noncontainment := by sorry

/-- Paper: Terminology 10.2.1.2(2), p. 444. The printed implication says
that the functionals paired with a regular Markushevich family are bounded. -/
def Printed.spectralRegular_dual_bounded : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (x : ℕ → E) (Λ : ℕ → StrongDual ℂ E),
    (∀ i, Λ i (x i) = 1) → (∀ i j, i ≠ j → Λ j (x i) = 0) →
    Dense (Submodule.span ℂ (range x) : Set E) →
    (∀ v : E, (∀ i, Λ i v = 0) → v = 0) → IsRegularSpectralFamily x →
    ∃ C : ℝ, ∀ n, ‖Λ n‖ ≤ C

/-- Paper: Terminology 10.2.1.2(2), p. 444. In complex ℓ² take
x₂ₙ = e₂ₙ and x₂ₙ₊₁ = e₂ₙ + (n+1)⁻¹ e₂ₙ₊₁. If eⱼ* is coordinate evaluation,
the dual pair is e₂ₙ* − (n+1)e₂ₙ₊₁* and (n+1)e₂ₙ₊₁*. Both spans contain
the finite-support families, every x has norm at least one, and the dual
norms are unbounded. -/
theorem Printed.spectralRegular_dual_bounded_false :
    ¬ Printed.spectralRegular_dual_bounded := by sorry

/-- Paper: Corollary 10.2.1.4, p. 444. The printed floor-indexed
line jets form a normalized basis in the image of the quotient dual. -/
def Printed.spectralLineMarkushevichBasis_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily (fun j ↦ D (Λ j))

/-- Paper: Corollary 10.2.1.4, p. 444. The splitting-field example at
s = 3 includes a positive-order jet of infinite squared integral. -/
theorem Printed.spectralLineMarkushevichBasis_normalized_false :
    ¬ Printed.spectralLineMarkushevichBasis_normalized := by sorry

/-- Paper: Theorem 10.2.1.1 and Remark 10.2.1.5, pp. 440, 444. The
asserted basis and its claimed primal normalization together give a bounded
regular family biorthogonal to the prescribed jets. -/
def Printed.spectralLineMarkushevichBasis_primal_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily x

/-- Paper: Remark 10.2.1.5, p. 444. Use the rational trivial component
at a = 1/2 and s = 2. For close simple zeta zeros the two evaluation
vectors approach one another in the dual norm. A vector pairing to one
with the first and zero with the second has norm at least the reciprocal
of their distance. The required primal bound fails. -/
theorem Printed.spectralLineMarkushevichBasis_primal_normalized_false :
    ¬ Printed.spectralLineMarkushevichBasis_primal_normalized := by sorry

/-- Paper: Theorem 10.2.2.1, p. 446. The jets indexed by the printed
interior and boundary multiplicities belong to the reciprocal strip space
and are the functionals of a Markushevich basis in any enumeration. -/
def Printed.spectralStripMarkushevichBasis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      let hI := (neg_nonpos.mpr hα).trans hα
      let Q := spectralSobolevQuotient F a hI hs
      let D := spectralSobolevDualEmbedding F a hI hs
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (weight(F, α, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        ∀ j, D (Λ j) = (h j).toLp (η j)

/-- Paper: Theorem 10.2.2.1, p. 446. On the singleton strip with s = 1
a Riemann zeta zero supplies a zeroth jet with divergent squared norm. -/
theorem Printed.spectralStripMarkushevichBasis_false :
    ¬ Printed.spectralStripMarkushevichBasis := by sorry

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5)–(10.2.2.6), p. 446.
The printed floor cutoff on the boundary and the full cutoff in the interior
are asserted to produce elements of the reciprocal strip space. -/
def Printed.spectralStripJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 0 ≤ s → ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ) (k : ℕ),
    let N := order(χ ω, shift(a + b, t))
    ((b = -α ∨ b = α) ∧ k < min N (Nat.floor ((s - 1) / 2 + 1)) ∨
      b ∈ Ioo (-α) α ∧ k < N) →
    MemLp (spectralZeroJet (χ ω) b t k) 2 (weight(F, α, s))

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5), p. 446. Take F = ℚ,
the trivial character, s = 1, α = b = 0 and a+it the first nontrivial
Riemann zeta zero with positive ordinate. The printed cutoff includes k = 0.
Its squared norm has a 1/|x| tail in log coordinates. -/
theorem Printed.spectralStripJet_memLp_false : ¬ Printed.spectralStripJet_memLp := by sorry

/-- Paper: Proposition 10.2.2.2, pp. 446–447. The annulus uses the
reciprocal strip norm and the final open ball uses the negative line norm.
The ordinate is required to occur on the a-line as printed in (2). The
displacement in the displayed family is constrained by the multiplicity
at a+b+it, using the two cases of the definition on the same page. -/
def Printed.spectralStripJet_annulus_and_noncontainment : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s →
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        0 < order(χ j.1, shift(a, j.2.2.1)) ∧
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      ∃ C : ℝ, 0 < C ∧
        (∀ j, ∃ h : MemLp (η j) 2 (weight(F, α, s)), C⁻¹ ≤ ‖h.toLp (η j)‖ ∧ ‖h.toLp (η j)‖ ≤ C) ∧
        ¬ (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), ‖h.toLp (η j)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. In ℚ take a = 2, s = 2
and α = 0. The family is empty, so it is contained in every open ball. -/
theorem Printed.spectralStripJet_annulus_and_noncontainment_false :
    ¬ Printed.spectralStripJet_annulus_and_noncontainment := by sorry

/-- Paper: Proposition 10.2.2.2, p. 447. The asserted noncontainment in an
open ball is specialized to the allowed singleton interval, where the
repeated boundary reference and the stated ambient line norm both apply. -/
def Printed.spectralStripJet_not_subset_ball_singleton : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, p. 447. Take F = ℚ, a = 2, s = 2 and
I = {0}. On that strip every Hecke L-function is zero-free, so the empty
family is contained in every open ball. -/
theorem Printed.spectralStripJet_not_subset_ball_singleton_false :
    ¬ Printed.spectralStripJet_not_subset_ball_singleton := by sorry

/-- Paper: Corollary 10.2.2.3, p. 447. The printed index requires an
ordinate from the a-line. The conclusion identifies the normalized family
in the reciprocal strip space and also locates the annihilator in the negative line space. -/
def Printed.spectralStripMarkushevichBasis_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        0 < order(χ j.1, shift(a, j.2.2.1)) ∧
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      let hI := (neg_nonpos.mpr hα).trans hα
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (weight(F, α, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) ∧
        (∀ L : StrongDual ℂ Q, ∃ v : Lp ℂ 2 (lineWeight(F, s)),
          (v : C𝔽(F) → ℂ) =ᵐ[ideleClassTamagawaMeasure F] (D L : C𝔽(F) → ℂ))

/-- Paper: Corollary 10.2.2.3, p. 447. For ℚ at a = α = s = 2 the
a-line has no zeros. A nontrivial critical-line Riemann zero with ordinate γ
supplies a nonzero quotient functional: the jet with b = -3/2 and t = γ
is strip-integrable in squared norm and vanishes on polar-free weighted theta
tests by the forward zeta integral factorization. An empty family cannot span
this dual. -/
theorem Printed.spectralStripMarkushevichBasis_normalized_false :
    ¬ Printed.spectralStripMarkushevichBasis_normalized := by sorry

end RiemannMasullo
