module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a

/-!
# Appendix B.7.1: statements that are false as printed
-/

@[expose] public noncomputable section

open Filter NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "oneLine" => Complex.re ⁻¹' ({1} : Set ℝ)

/-- Paper: Lemma B.7.1.1, Equations (B.7.1.4)–(B.7.1.5), p. 644.
The two printed simplified bounds are uniform in the unrestricted range
`σ > 1 - c`. A common constant majorizes the three big-O constants.
The bound in (B.7.1.3) is supplied as one law of the exponent and the
coefficient bound in (1), fixed for all the sequences under consideration.
The natural floor extends the integer majorant to positive real arguments. -/
def Printed.truncatedPerron_error_of_isBigO : Prop :=
  ∀ (α A : ℝ), 0 < α → 0 < A →
    ∃ C : ℝ, 0 < C ∧ ∀ (absBound : ℝ → ℝ → ℝ),
      (∀ α' A', 0 < α' → 0 < A' → 0 < absBound α' A') →
      ∀ (a : ℕ → ℂ) (ψ : ℕ → ℝ),
      (∀ n, 0 < ψ n) → Monotone ψ →
      (∀ s : ℂ, 1 < s.re → LSeriesSummable a s) →
      (∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ A * ψ n) →
      Asymptotics.IsBigOWith (absBound α A) (𝓝[>] (1 : ℝ))
        (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖)
        (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹) →
      ∀ (c σ T : ℝ), 0 < c → 1 - c < σ → 1 ≤ T →
        let s : ℂ := ⟨σ, T⟩
        (∀ (x : ℝ), 0 < x → x ∉ Set.range (Int.cast : ℤ → ℝ) →
          ∀ N : ℤ, |x - (N : ℝ)| ≤ 1 / 2 →
            ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
              C * (x ^ c / (T * (σ + c - 1) ^ α) +
                |ψ ⌊2 * x⌋₊ * x ^ (1 - σ) * Real.log x / T| +
                ψ N.toNat * x ^ (1 - σ) / (T * |x - (N : ℝ)|))) ∧
        (∀ m : ℕ, 0 < m →
          ‖perronHalfWeightedSum a s m - truncatedPerronIntegral (LSeries a) s m c T‖ ≤
            C * ((m : ℝ) ^ c / (T * (σ + c - 1) ^ α) +
              ψ (2 * m) * (m : ℝ) ^ (1 - σ) * Real.log m / T +
              ψ m * c * (m : ℝ) ^ (-σ) / T))

/-- Paper: Lemma B.7.1.1, pp. 644–645. Take `a₁ = 1`, all other
coefficients zero, `ψ ≡ 1`, and `α = c = T = 1`. At `x = 5/4` and
`x = 2` the cutoff sum is 1, while the integral has norm at most `x / π < 1`.
Each proposed error bound tends to zero as `σ → +∞`. -/
theorem Printed.truncatedPerron_error_of_isBigO_false :
    ¬ Printed.truncatedPerron_error_of_isBigO := by
  sorry

/-- Paper: Equation (B.7.1.11), p. 646. The printed bound uses a full weight at
integer cutoffs with the error terms for the half-weight Perron formula. -/
def Printed.heckeLogDerivPolynomial_perron_error : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℂ → ℂ), MeromorphicNFOn Z univ →
      (∀ s : halfPlane, Z s = dedekindZeta F s) →
      ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → s ≠ 1 + Complex.I * t₀ → 1 < x → 0 < c → 1 ≤ T →
        ‖heckeLogDerivPolynomial χ x s -
          truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T‖ ≤
          C * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
            (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
             else Real.log x / (T * |x - (round x : ℝ)|)))

/-- Paper: Equation (B.7.1.11), p. 646. Over the rationals take the trivial
character, `t₀ = 0`, `s = 1 + i`, `x = 2` and `c = 1`. The integral
tends to the half-weight sum as `T → +∞`. The full sum differs by
`log(2) / (2 · 2^s) ≠ 0`, whereas the printed error tends to zero. -/
theorem Printed.heckeLogDerivPolynomial_perron_error_false :
    ¬ Printed.heckeLogDerivPolynomial_perron_error := by
  sorry

/-- Paper: Contour preceding Equation (B.7.1.12), p. 647. The printed choice
`δ = α η(|T - t₀|)` is claimed to place the entire contour inside the
region specified by the width `η`. -/
def Printed.dedekindZeta_perron_contour_in_zeroFreeRegion : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∀ (Z : ℂ → ℂ), MeromorphicNFOn Z univ → (∀ s : halfPlane, Z s = dedekindZeta F s) →
    ∀ (A B : ℝ), 0 < A → 1 / 3 < B →
    let η := fun v : ℝ ↦ A / Real.log (B * (|v| + 3))
    MapsTo η (Ici 0) (Ioc 0 (1 / 2)) →
    (∀ z : ℂ, 1 - η |z.im| < z.re → meromorphicOrderAt Z z ≤ 0) →
    ∀ (α t T c : ℝ), α ∈ Ioo 0 1 → t ≠ t₀ → 2 + |t₀| + |t| ≤ T → 0 < c →
      let δ := α * η |T - t₀|
      ∀ u ∈ Icc (-δ) c, ∀ y ∈ Icc (-T) T,
        (u = -δ ∨ u = c ∨ y = -T ∨ y = T) →
        1 - η |t + y - t₀| < 1 + u

/-- Paper: Contour preceding Equation (B.7.1.12), p. 647. Take `t₀ = 0`,
`t = 2`, `T = 4`, and `c = 1`. At the top left corner the shifted
height is 6. Take the trivial character over the rationals and any genuine
logarithmic zero-free width from Proposition B.6.1.1, shrinking its numerator
to ensure the range condition. For every such width, `η(6) / η(4) < 1`.
Choose `α` strictly between that ratio and one. -/
theorem Printed.dedekindZeta_perron_contour_in_zeroFreeRegion_false :
    ¬ Printed.dedekindZeta_perron_contour_in_zeroFreeRegion := by
  sorry

end RiemannMasullo
