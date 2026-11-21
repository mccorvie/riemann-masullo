module

public import RiemannMasullo.AppB_AnalyticNT.Sec2

/-!
# Slow growth near poles and the asymptotic residue theorem

Masullo, §B.3, pp. 604–606. The growth bound is stated with its printed
quantifier over all integer indices.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Asymptotics Topology

namespace RiemannMasullo

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "openStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Ioo a b)
local notation "atAbsInfty" => (comap abs atTop)

-- TODO(paper-gap): (B.3.1.1) includes k = 0, forcing f to vanish along the
-- entire horizontal line at T 0 and hence to have zero meromorphic germ on the strip.

/-- Paper: Definition B.3.1.1, p. 604. A witness is a sequence of heights with
nondecreasing absolute heights on each tail, divergence in absolute value, and
a polynomial upper bound. The function is holomorphic near each selected line,
satisfies the indexed growth bound there, and has continuous, polynomially
bounded traces on two interior vertical lines.
Deviation: The index in (1)(a) counts steps outward on each tail. The horizontal
neighborhoods are intersected with the domain strip. -/
def WitnessesSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) (T : ℤ → ℝ) : Prop :=
  a < b ∧ MeromorphicOn f (openStrip a b) ∧
    Monotone (fun k : ℕ ↦ |T (k : ℤ)|) ∧ Monotone (fun k : ℕ ↦ |T (-(k : ℤ))|) ∧
    Tendsto (fun k : ℤ ↦ |T k|) atAbsInfty atTop ∧
    (∃ α : ℝ, 0 < α ∧ T =O[atAbsInfty] (fun k : ℤ ↦ |(k : ℝ)| ^ α)) ∧
    (∀ k : ℤ, ∃ δ > (0 : ℝ), DifferentiableOn ℂ f
      (openStrip a b ∩ Complex.im ⁻¹' Ioo (T k - δ) (T k + δ))) ∧
    (∃ β A : ℝ, 0 < β ∧ 0 < A ∧
      ∀ (k : ℤ) (σ : ℝ), σ ∈ Ioo a b → ‖f (verticalPoint σ (T k))‖ ≤ A * |(k : ℝ)| ^ β) ∧
    ∃ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ ε₁ < ε₂ ∧ ε₂ < (b - a) / 2 ∧
      ∀ σ ∈ ({a + ε₁, b - ε₂} : Set ℝ),
        Continuous (fun y : ℝ ↦ f (verticalPoint σ y)) ∧
          ∃ γ : ℝ, 0 < γ ∧
            (fun y : ℝ ↦ f (verticalPoint σ y)) =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ)

/-- Paper: Definition B.3.1.1, p. 604. A function has slow growth near its poles
on the strip if there exists a sequence witnessing that condition. -/
def HasSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ T : ℤ → ℝ, WitnessesSlowGrowthNearPoles f a b T

/-- Paper: Definition B.3.1.1, p. 604. The integer heights witness slow growth
for the zero function on every nonempty strip.
Deviation: Sanity check for the witness predicate. -/
theorem witnessesSlowGrowthNearPoles_zero {a b : ℝ} (hab : a < b) :
    WitnessesSlowGrowthNearPoles (fun _ ↦ 0) a b (fun k : ℤ ↦ (k : ℝ)) := by sorry

/-- Paper: Definition B.3.1.1, p. 604. The bound at index zero forces the
meromorphic germ to vanish everywhere in the strip.
Deviation: Sanity check recording the consequence of the printed quantifier. -/
theorem HasSlowGrowthNearPoles.meromorphicOrderAt_eq_top {f : ℂ → ℂ} {a b : ℝ}
    (hf : HasSlowGrowthNearPoles f a b) {z : ℂ} (hz : z ∈ openStrip a b) :
    meromorphicOrderAt f z = ⊤ := by sorry

-- TODO(paper-gap): The proof of (B.3.1.2) needs a polynomial lower bound on
-- |T k|, whereas Definition B.3.1.1 gives an upper bound. The bounds at T k
-- also need not apply at -T k. The literal hypotheses force zero germs.

/-- Paper: Lemma B.3.1.2, p. 605. At each of the two signed witness heights,
the horizontal absolute integral exists for |k| ≥ 2 and tends to zero as |k|
goes to infinity. The limit uses the literal slow-growth condition.
Deviation: Endpoints on the strip boundary are ignored by interval integration. -/
theorem tendsto_horizontalIntegral_of_slowGrowthNearPoles
    {f Φ : ℂ → ℂ} {a b : ℝ} {T : ℤ → ℝ}
    (hT : WitnessesSlowGrowthNearPoles f a b T)
    (ε : ℝ) (hε : 0 < ε) (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε))
    (sign : ℝ) (hsign : sign = -1 ∨ sign = 1) :
    let F (k : ℤ) (σ : ℝ) := ‖f (verticalPoint σ (sign * T k)) * Φ (verticalPoint σ (sign * T k))‖
    (∀ k : ℤ, 2 ≤ |k| → IntervalIntegrable (F k) volume a b) ∧
      Tendsto (fun k : ℤ ↦ ∫ σ in a..b, F k σ) atAbsInfty (𝓝 0) := by sorry

-- TODO(paper-gap): Theorem B.3.2.1(1) uses rectangles defined for T > 0,
-- but the nonnegative-indexed witness heights need not be positive.
-- TODO(paper-gap): Theorem B.3.2.1(2) uses Φ(ρ) Res f at arbitrary poles,
-- whereas the contour integral gives Res (Φ * f). The printed growth
-- condition also supplies polynomial bounds only on two existentially chosen lines.
-- TODO(paper-gap): The horizontal terms in (B.3.2.4) have signs opposite to
-- the counterclockwise orientation in Figure 3.

/-- Paper: Theorem B.3.2.1(2), p. 606. The absolute-convergence claim for the
vertical integrals holds on an interior pole-free line under the literal
slow-growth condition.
Deviation: A line parameter states the absolute-convergence claim for either
side of the rectangle. The residue-limit identity is deferred. -/
theorem verticalIntegrable_mul_of_slowGrowthNearPoles {f Φ : ℂ → ℂ} {a b a' b' : ℝ}
    (hf : HasSlowGrowthNearPoles f a b) (ha : a' < a) (hb : b < b')
    (hΦ : UniformlySchwartzOnStrip Φ a' b') {σ : ℝ} (hσ : σ ∈ Ioo a b)
    (hNoPole : ∀ y : ℝ, 0 ≤ meromorphicOrderAt f (verticalPoint σ y)) :
    Complex.VerticalIntegrable (fun z ↦ Φ z * f z) σ := by sorry

end RiemannMasullo
