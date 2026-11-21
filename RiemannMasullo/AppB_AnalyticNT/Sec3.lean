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
      meromorphicOrderAt (fun z : ℂ ↦ 1 / z) 0 = -1 := by
  have hOrder : meromorphicOrderAt (fun z : ℂ ↦ 1 / z) 0 = -1 := by
    have h : meromorphicOrderAt (fun z : ℂ ↦ (z - 0) ^ (-1 : ℤ)) 0 =
        ((-1 : ℤ) : WithTop ℤ) := meromorphicOrderAt_zpow_id_sub_const
    simpa only [sub_zero, zpow_neg_one, one_div, WithTop.LinearOrderedAddCommGroup.coe_neg,
      WithTop.coe_one] using h
  refine ⟨?_, hOrder⟩
  let T (k : ℤ) : ℝ := (k : ℝ) + 1 / 2
  have hHeight (k : ℤ) : (1 / 2 : ℝ) ≤ |T k| := by
    change (1 / 2 : ℝ) ≤ |(k : ℝ) + 1 / 2|
    rcases le_or_gt 0 k with hk | hk
    · have hk' : 0 ≤ (k : ℝ) := by exact_mod_cast hk
      linarith [le_abs_self ((k : ℝ) + 1 / 2)]
    · have hk' : (k : ℝ) ≤ -1 := Int.cast_le_neg_one_of_neg hk
      linarith [neg_le_abs ((k : ℝ) + 1 / 2)]
  have hIndex : Tendsto (fun k : ℤ ↦ |(k : ℝ)|) atAbsInfty atTop := by
    simpa only [Function.comp_def, Int.cast_abs] using
      (tendsto_intCast_atTop_atTop (R := ℝ)).comp
        (tendsto_comap : Tendsto (abs : ℤ → ℤ) atAbsInfty atTop)
  have hLower : ∀ᶠ k : ℤ in atAbsInfty, (1 / 2 : ℝ) * |(k : ℝ)| ≤ |T k| := by
    filter_upwards [hIndex.eventually_ge_atTop 1] with k hk
    have h := abs_sub_abs_le_abs_sub (k : ℝ) (-(1 / 2 : ℝ))
    rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), sub_neg_eq_add] at h
    change (1 / 2 : ℝ) * |(k : ℝ)| ≤ |(k : ℝ) + 1 / 2|
    linarith
  have hReciprocal (σ y : ℝ) {c : ℝ} (hc : 0 < c) (hy : c ≤ |y|) :
      ‖(1 : ℂ) / verticalPoint σ y‖ ≤ c⁻¹ := by
    have hNorm : |y| ≤ ‖verticalPoint σ y‖ := by
      simpa [Complex.add_im, Complex.mul_I_im] using
        Complex.abs_im_le_norm (verticalPoint σ y)
    rw [one_div, norm_inv]
    exact (inv_le_inv₀ (hc.trans_le (hy.trans hNorm)) hc).2 (hy.trans hNorm)
  refine ⟨T, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Meromorphic.const (1 : ℂ)).div Meromorphic.id).meromorphicOn
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    simp only [T, Int.cast_natCast, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1 / 2)]
    exact (add_le_add_left hmn' _).trans (le_abs_self _)
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    simp only [T, Int.cast_neg, Int.cast_natCast]
    apply abs_le'.2
    refine ⟨?_, ?_⟩
    · have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hn : (1 / 2 : ℝ) ≤ |-(n : ℝ) + 1 / 2| := by
        simpa only [T, Int.cast_neg, Int.cast_natCast] using hHeight (-(n : ℤ))
      exact (by linarith : -(m : ℝ) + 1 / 2 ≤ 1 / 2).trans hn
    · exact (by linarith : -(-(m : ℝ) + 1 / 2) ≤ -(-(n : ℝ) + 1 / 2)).trans (neg_le_abs _)
  · refine tendsto_atTop.2 fun r ↦ ?_
    filter_upwards [hIndex.eventually_ge_atTop (2 * r), hLower] with k hk hbound
    linarith
  · refine ⟨1, zero_lt_one, Asymptotics.isBigO_iff.2 ⟨2, ?_⟩⟩
    filter_upwards [hIndex.eventually_ge_atTop 1] with k hk
    simp only [T, Real.rpow_one, Real.norm_eq_abs, abs_abs]
    have h := abs_add_le (k : ℝ) (1 / 2)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    linarith
  · exact ⟨1 / 2, 1, by norm_num, zero_lt_one, by simpa only [Real.rpow_one] using hLower⟩
  · intro k
    refine ⟨1 / 2, by norm_num, fun z hz ↦ ?_⟩
    have hz₀ : z ≠ 0 := by
      rintro rfl
      have him := hz.2
      change T k - 1 / 2 < (0 : ℂ).im ∧ (0 : ℂ).im < T k + 1 / 2 at him
      rw [Complex.zero_im] at him
      exact (not_lt_of_ge (hHeight k))
        (abs_lt.2 ⟨by linarith [him.2], by linarith [him.1]⟩)
    exact ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hz₀).differentiableWithinAt
  · refine ⟨1, 2, zero_lt_one, by norm_num, ?_⟩
    intro k hk σ _
    have hk' : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    rw [Real.rpow_one]
    calc
      ‖(1 : ℂ) / verticalPoint σ (T k)‖ ≤ 2 := by
        simpa only [one_div, inv_inv] using hReciprocal σ (T k) (by norm_num) (hHeight k)
      _ ≤ 2 * |(k : ℝ)| := by linarith
  · refine ⟨1 / 4, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro σ hσ
    have hσ₀ : σ ≠ 0 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl <;> norm_num
    refine ⟨?_, 1, zero_lt_one, Asymptotics.isBigO_iff.2 ⟨1, ?_⟩⟩
    · refine continuous_const.div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y hz ↦ ?_
      apply hσ₀
      simpa [Complex.add_re, Complex.mul_I_re] using congrArg Complex.re hz
    · have hY : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| :=
        tendsto_comap.eventually (eventually_ge_atTop 1)
      filter_upwards [hY] with y hy
      simp only [Real.rpow_one, Real.norm_eq_abs, abs_abs, one_mul]
      calc
        ‖(1 : ℂ) / verticalPoint σ y‖ ≤ 1 := by
          simpa only [inv_one] using hReciprocal σ y zero_lt_one hy
        _ ≤ |y| := hy

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
