module

public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Slow growth near poles and the asymptotic residue theorem

Masullo, §B.3, pp. 604–606. The residue limit uses rectangles whose horizontal
edges lie at selected heights above and below the real axis.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Asymptotics BigOperators Topology

namespace RiemannMasullo

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "verticalTrace" =>
  (fun (f : ℂ → ℂ) (σ : ℝ) (y : ℝ) ↦ f (verticalPoint σ y))
local notation "openStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Ioo a b)
local notation "atAbsInfty" => (comap abs atTop)
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

-- TODO(paper-gap): (B.3.1.1) includes k = 0, forcing f to vanish along the
-- entire horizontal line at T 0 and hence to have zero meromorphic germ on the strip.
-- TODO(paper-gap): If both signs in (1)(a) range over all integer step indices,
-- the absolute heights are constant, contradicting (1)(b).

/-- Paper: Definition B.3.1.1, p. 604. A witness is a sequence of heights with
nondecreasing absolute heights on each tail, divergence in absolute value, and
polynomial upper and lower bounds. The function is holomorphic near every selected
line, is polynomially bounded in the nonzero index there, and has continuous,
polynomially bounded traces on two interior vertical lines.
Deviation: The index in (1)(a) counts steps outward on each tail. Part (1)(c)
includes the eventual polynomial lower bound used in Lemma B.3.1.2. The holomorphic
neighborhoods lie in the domain strip, and (B.3.1.1) applies only when `k ≠ 0`. -/
def WitnessesSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) (T : ℤ → ℝ) : Prop :=
  a < b ∧ MeromorphicOn f (openStrip a b) ∧
    Monotone (fun k : ℕ ↦ |T (k : ℤ)|) ∧ Monotone (fun k : ℕ ↦ |T (-(k : ℤ))|) ∧
    Tendsto (fun k : ℤ ↦ |T k|) atAbsInfty atTop ∧
    (∃ α : ℝ, 0 < α ∧ T =O[atAbsInfty] (fun k : ℤ ↦ |(k : ℝ)| ^ α)) ∧
    (∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧
      ∀ᶠ k : ℤ in atAbsInfty, c * |(k : ℝ)| ^ γ ≤ |T k|) ∧
    (∀ k : ℤ, ∃ δ > (0 : ℝ), DifferentiableOn ℂ f
      (openStrip a b ∩ Complex.im ⁻¹' Ioo (T k - δ) (T k + δ))) ∧
    (∃ β A : ℝ, 0 < β ∧ 0 < A ∧
      ∀ (k : ℤ), k ≠ 0 → ∀ σ ∈ Ioo a b,
        ‖f (verticalPoint σ (T k))‖ ≤ A * |(k : ℝ)| ^ β) ∧
    ∃ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ ε₁ < ε₂ ∧ ε₂ < (b - a) / 2 ∧
      ∀ σ ∈ ({a + ε₁, b - ε₂} : Set ℝ),
        Continuous (verticalTrace f σ) ∧
          ∃ γ > (0 : ℝ), verticalTrace f σ =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ)

/-- Paper: Definition B.3.1.1, p. 604. A function has slow growth near its poles
on the strip if there exists a sequence witnessing that condition.
Deviation: Uses the repaired witness condition above. -/
def HasSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ T : ℤ → ℝ, WitnessesSlowGrowthNearPoles f a b T

/-- Paper: Definition B.3.1.1, p. 604. The integer heights witness slow growth
for the zero function on every nonempty strip.
Deviation: Sanity check for the witness predicate. -/
theorem witnessesSlowGrowthNearPoles_zero {a b : ℝ} (hab : a < b) :
    WitnessesSlowGrowthNearPoles (fun _ ↦ 0) a b (fun k : ℤ ↦ (k : ℝ)) := by sorry

/-- Paper: Definition B.3.1.1, p. 604. The reciprocal function has slow growth on
the strip with real parts between −1 and 1, and has a simple pole at zero.
Deviation: Sanity check for the repaired definition, with heights `T k = k + 1/2`. -/
theorem hasSlowGrowthNearPoles_one_div :
    HasSlowGrowthNearPoles (fun z : ℂ ↦ 1 / z) (-1) 1 ∧
      meromorphicOrderAt (fun z : ℂ ↦ 1 / z) 0 = -1 := by sorry

-- TODO(paper-gap): The proof of (B.3.1.2) needs a polynomial lower bound on
-- |T k|, whereas Definition B.3.1.1 gives an upper bound. The bounds at T k
-- also need not apply at -T k.

/-- Paper: Lemma B.3.1.2, p. 605. At the selected heights the horizontal absolute
integral exists for |k| ≥ 2 and tends to zero as |k| goes to infinity.
Deviation: The limit uses the repaired witness condition and is taken at `T k`
on both index tails. The two strip endpoints have zero measure. -/
theorem tendsto_horizontalIntegral_of_slowGrowthNearPoles
    {f Φ : ℂ → ℂ} {a b : ℝ} {T : ℤ → ℝ}
    (hT : WitnessesSlowGrowthNearPoles f a b T)
    (ε : ℝ) (hε : 0 < ε) (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε)) :
    let F (k : ℤ) (σ : ℝ) := ‖Φ (verticalPoint σ (T k)) * f (verticalPoint σ (T k))‖
    (∀ k : ℤ, 2 ≤ |k| → IntervalIntegrable (F k) volume a b) ∧
      Tendsto (fun k : ℤ ↦ ∫ σ in a..b, F k σ) atAbsInfty (𝓝 0) := by sorry

-- TODO(paper-gap): Theorem B.3.2.1(1) uses rectangles defined for T > 0,
-- but the nonnegative-indexed witness heights need not be positive.
-- TODO(paper-gap): Theorem B.3.2.1(2) uses Φ(ρ) Res f at arbitrary poles,
-- whereas the contour integral gives Res (Φ * f).
-- TODO(paper-gap): Theorem B.3.2.1(2) uses arbitrary pole-free vertical sides,
-- but the growth condition supplies polynomial bounds only on two existentially chosen lines.
-- TODO(paper-gap): The horizontal terms in (B.3.2.4) have signs opposite to
-- the counterclockwise orientation in Figure 3.

/-- Paper: Theorem B.3.2.1(2), p. 606. The trace of the product is absolutely
integrable on an interior vertical line where the trace of `f` is continuous
and polynomially bounded.
Deviation: The trace assumptions are explicit for each line. -/
theorem verticalIntegrable_mul_of_polynomialGrowth {f Φ : ℂ → ℂ} {a b σ : ℝ}
    (hΦ : UniformlySchwartzOnStrip Φ a b) (hσ : σ ∈ Ioo a b)
    (hContinuous : Continuous (verticalTrace f σ))
    (hGrowth : ∃ γ > (0 : ℝ), verticalTrace f σ =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ)) :
    Complex.VerticalIntegrable (fun z ↦ Φ z * f z) σ := by sorry

/-- Paper: Theorem B.3.2.1, p. 606. For a meromorphic germ, the residue is the
normalized counterclockwise circle integral in the limit of small positive radii.
Deviation: Makes the residue operation in the paper explicit. -/
def complexResidue (f : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r ↦ circleIntegral f ρ r / twoPiI)

/-- Paper: Theorem B.3.2.1, p. 606. Dividing a function holomorphic near `ρ` by
`z - ρ` gives residue equal to the numerator at `ρ`.
Deviation: Sanity check for the residue normalization at a simple pole. -/
theorem complexResidue_div_sub {g : ℂ → ℂ} {ρ : ℂ} (hg : AnalyticAt ℂ g ρ) :
    complexResidue (fun z ↦ g z / (z - ρ)) ρ = g ρ := by sorry

set_option quotPrecheck false in
local notation "rectanglePoles" =>
  (fun (f : ℂ → ℂ) (σ₁ σ₂ t₁ t₂ : ℝ) ↦
    {ρ : ℂ | ρ.re ∈ Ioo σ₁ σ₂ ∧ ρ.im ∈ Ioo t₁ t₂ ∧ meromorphicOrderAt f ρ < 0})

/-- Paper: Theorem B.3.2.1(1), p. 606. An open rectangle whose vertical sides
are interior to the strip contains only finitely many poles.
Deviation: Makes the finiteness implicit in the rectangle sum explicit. -/
theorem finite_rectanglePoles {f : ℂ → ℂ} {a b σ₁ σ₂ t₁ t₂ : ℝ}
    (hf : MeromorphicOn f (openStrip a b)) (hσ₁ : a < σ₁) (hσ₂ : σ₂ < b) :
    (rectanglePoles f σ₁ σ₂ t₁ t₂).Finite := by sorry

section AsymptoticResidue

variable {f Φ : ℂ → ℂ} {a b a' b' σ₁ σ₂ : ℝ} {T : ℤ → ℝ}
  (hT : WitnessesSlowGrowthNearPoles f a b T)
  (ha : a' < a) (hb : b < b') (hΦ : UniformlySchwartzOnStrip Φ a' b')
  (hσ₁ : a < σ₁) (hσ : σ₁ < σ₂) (hσ₂ : σ₂ < b)
  (hSides : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ), Continuous (verticalTrace f σ) ∧
    ∃ γ > (0 : ℝ), verticalTrace f σ =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ))
  (hHeights : ∀ k : ℕ, 0 < k → T (-(k : ℤ)) < 0 ∧ 0 < T (k : ℤ))

include ha hb hΦ hσ hSides hHeights

/-- Paper: Theorem B.3.2.1(1)–(2), p. 606. The finite sums of the residues of
`Φ * f` at poles of `f` converge to the upward integral on the right minus
the upward integral on the left, divided by `2πi`.
Deviation: The vertical sides have continuous, polynomially bounded traces.
The lower and upper edges use the selected heights `T (-k)` and `T k`, assumed
to have opposite signs for positive `k`. The residue is that of the product. -/
theorem tendsto_rectangleResidueSum :
    Tendsto
      (fun k : ℕ ↦
        ∑ ρ ∈ (finite_rectanglePoles (t₁ := T (-(k : ℤ))) (t₂ := T (k : ℤ))
          hT.2.1 hσ₁ hσ₂).toFinset, complexResidue (fun z ↦ Φ z * f z) ρ)
      atTop
      (𝓝 ((verticalLineIntegral (fun z ↦ Φ z * f z) σ₂ -
        verticalLineIntegral (fun z ↦ Φ z * f z) σ₁) / twoPiI)) := by sorry

/-- Paper: Theorem B.3.2.1(1)–(2), p. 606. If the poles between the chosen
lines are simple, the finite sums with weights `Φ ρ * complexResidue f ρ`
converge to the normalized difference of vertical integrals.
Deviation: Uses the same trace and signed height hypotheses as the residue
theorem. The simple-pole assumption justifies the printed weight. -/
theorem tendsto_rectangleResidueSum_of_simplePoles
    (hSimple : ∀ ρ : ℂ, ρ.re ∈ Ioo σ₁ σ₂ →
      meromorphicOrderAt f ρ < 0 → meromorphicOrderAt f ρ = -1) :
    Tendsto
      (fun k : ℕ ↦
        ∑ ρ ∈ (finite_rectanglePoles (t₁ := T (-(k : ℤ))) (t₂ := T (k : ℤ))
          hT.2.1 hσ₁ hσ₂).toFinset, Φ ρ * complexResidue f ρ)
      atTop
      (𝓝 ((verticalLineIntegral (fun z ↦ Φ z * f z) σ₂ -
        verticalLineIntegral (fun z ↦ Φ z * f z) σ₁) / twoPiI)) := by sorry

end AsymptoticResidue

end RiemannMasullo
