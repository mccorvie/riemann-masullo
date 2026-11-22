module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-! # Printed cutoff claims in §12.4 -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Padic SchwartzMap

namespace RiemannMasullo

/-- Paper: Step II, p. 516. In the model F = ℚ with only the real place, the
printed spatial multiplier sends all Schwartz functions to the flat subspace.
Deviation: State this specialization with a smooth even profile, a unit plateau,
and support in the closed outer ball. -/
def Printed.sLocalSpatialCutoff_realFlatRange : Prop :=
  ∀ (L ε : ℝ), 0 < ε → ε < L →
    ∀ (ρ : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → (∀ x, ρ (-x) = ρ x) →
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1) → tsupport ρ ⊆ Icc (-L) L →
      EqOn ρ 1 (Icc (-(L - ε)) (L - ε)) →
      ∀ f : 𝓢(ℝ, ℂ), ∃ h : 𝓢(ℝ, ℂ), h ∈ realSchwartzFlatAtOrigin ∧
        ∀ x : ℝ, h x = (ρ x : ℂ) * f x

/-- Paper: Step II, p. 516. Take outer radius two, transition width one,
a smooth even cutoff equal to one on [−1,1], and the Gaussian exp(−x²).
The product has value one at zero, so it fails even the zeroth flatness condition. -/
theorem Printed.sLocalSpatialCutoff_realFlatRange_false :
    ¬ Printed.sLocalSpatialCutoff_realFlatRange := by sorry

local notation "adelicModel" => Multiplicative (ℝ × ℚ_[2])

/-- Paper: Step II, pp. 516–517. In the model F = ℚ, S = {∞, 2}, the
product-norm cutoff is used to multiply the additive Schwartz–Bruhat space into itself.
Deviation: State the multiplication claim for this model and for smooth real
profiles with a unit plateau and a finite outer radius. -/
def Printed.sLocalProductCutoff_preservesSchwartzBruhat : Prop :=
  ∀ (L ε : ℝ), 0 < ε → ε < L →
    ∀ (ρ : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) →
      (∀ t ≥ L, ρ t = 0) → EqOn ρ 1 (Icc 0 (L - ε)) →
      ∀ f : SchwartzBruhat adelicModel,
        (fun x : adelicModel ↦ (ρ (‖x.toAdd.1‖ * ‖x.toAdd.2‖) : ℂ) * f x) ∈
          schwartzBruhatSubmodule (G := adelicModel)

/-- Paper: Step II, pp. 516–517. Take the product of exp(−x²) and the indicator
of ℤ₂, with a smooth profile equal to one up to radius one and zero from radius two.
For every n choose h = 2ⁿ and x = 2ⁿ⁺². The product is nonzero at (x,0) and
zero at (x,h). No common open subgroup of translations in ℚ₂ fixes the product. -/
theorem Printed.sLocalProductCutoff_preservesSchwartzBruhat_false :
    ¬ Printed.sLocalProductCutoff_preservesSchwartzBruhat := by sorry

/-- Paper: (12.4.1.22), p. 518. The smoothed identity orbital mass is set
equal to the integral over the two sharp intervals.
Deviation: State the real part in the rational real model for lifts supported
on the positive reals. The positive half-line is the S-unit fundamental domain. -/
def Printed.sLocalSmoothMass_eq_sharp_real : Prop :=
  ∀ (L L' ε : ℝ), 0 < ε → ε < L → ε < L' →
    ∀ (ρ σ f : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → ContDiff ℝ (∞ : ℕ∞ω) σ →
      (∀ x, ρ (-x) = ρ x ∧ σ (-x) = σ x) →
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1 ∧ 0 ≤ σ x ∧ σ x ≤ 1) →
      tsupport ρ ⊆ Icc (-L) L → tsupport σ ⊆ Icc (-L') L' →
      EqOn ρ 1 (Icc (-(L - ε)) (L - ε)) → EqOn σ 1 (Icc (-(L' - ε)) (L' - ε)) →
      ContDiff ℝ (∞ : ℕ∞ω) f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
      let m := fun x u : ℝ ↦ ∫ g in Ioi (0 : ℝ),
        f g / (g * Real.sqrt g) * Real.cos (2 * Real.pi * (g⁻¹ - 1) * x * u)
      (∫ x in Ioi (0 : ℝ), ρ x * ∫ u : ℝ, σ u * m x u) =
        ∫ x in Ioc (0 : ℝ) L, ∫ u in Icc (-L') L', m x u

/-- Paper: (12.4.1.22), p. 518. Set both radii to one and the width to one half.
Use smooth even cutoffs that taper from one to zero on (1/2,1) and a nonzero
nonnegative smooth lift supported in (15/16,17/16). The cosine is strictly
positive on the sharp integration region, so tapering strictly decreases the mass. -/
theorem Printed.sLocalSmoothMass_eq_sharp_real_false :
    ¬ Printed.sLocalSmoothMass_eq_sharp_real := by sorry

end RiemannMasullo
