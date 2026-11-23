module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Logarithmic derivatives and Perron's formula on the 1-line

Masullo, §B.7.1, pp. 643–648. The finite Hecke L-function on the boundary is
represented by a meromorphic continuation in normal form, as in §B.6.
-/

@[expose] public noncomputable section

open Filter NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "oneLine" => Complex.re ⁻¹' ({1} : Set ℝ)

/-- Paper: Equation (B.7.1.1), p. 643. The twisted ideal von Mangoldt series
converges absolutely to the negative logarithmic derivative to the right of one. -/
theorem finiteHeckeL_negLogDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
        (I.val.absNorm : ℂ) ^ (s : ℂ)) (-logDeriv L s) := by
  sorry

/-- Paper: Equations (B.7.1.4)–(B.7.1.5), p. 644. This is the normalized integral
of `f(s+w) x^w / w` up the segment from `c - iT` to `c + iT`. The factor
`i` in the path derivative cancels the `i` in the normalization. -/
def truncatedPerronIntegral (f : ℂ → ℂ) (s : ℂ) (x c T : ℝ) : ℂ :=
  (∫ t in -T..T, f (s + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
    (2 * (Real.pi : ℂ))

/-- Paper: Equation (B.7.1.7), p. 645. At the endpoint, the integral of the
constant series at cutoff one gives the arctangent factor. -/
theorem truncatedPerronIntegral_one (s : ℂ) {c T : ℝ} (hc : 0 < c) :
    truncatedPerronIntegral (fun _ ↦ 1) s 1 c T = (Real.arctan (T / c) / Real.pi : ℝ) := by
  sorry

/-- Paper: Lemma B.7.1.1, pp. 644–645. This sums the Dirichlet terms for positive
integers up to the real cutoff, with half weight when the cutoff is an integer. -/
def perronHalfWeightedSum (a : ℕ → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    if (n : ℝ) = x then LSeries.term a s n / 2 else LSeries.term a s n

/-- Paper: Equation (B.7.1.5), p. 644. At a positive integer cutoff, the terms
strictly below the cutoff have full weight and the last term has half weight. -/
theorem perronHalfWeightedSum_nat (a : ℕ → ℂ) (s : ℂ) {m : ℕ} (hm : 0 < m) :
    perronHalfWeightedSum a s m =
      (∑ n ∈ Finset.Ico 1 m, LSeries.term a s n) + LSeries.term a s m / 2 := by
  sorry

/-- Paper: Equations (B.7.1.6)–(B.7.1.7), pp. 644–645. The truncated Perron
error is bounded by a sum weighted by the inverse logarithmic distance from
the cutoff. An exact endpoint contributes the separate arctangent error.
Deviation: This includes both endpoint cases and assumes absolute convergence
at the specific line of integration, which suffices for this bound. -/
theorem truncatedPerron_error (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 1 ≤ T) (ha : LSeriesSummable a (s + (c : ℂ))) :
    ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
      x ^ c / (Real.pi * T) *
        (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = x then 0
          else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) +
      (if (⌊x⌋₊ : ℝ) = x then
        c * ‖LSeries.term a s ⌊x⌋₊‖ / (Real.pi * T) else 0) := by
  sorry

/-- Paper: Lemma B.7.1.1, Equation (B.7.1.4), p. 644.
The truncated Perron error at a noninteger cutoff has a far contribution,
a near contribution and a contribution from a nearest integer.
Deviation: The simplified estimate is uniform for `1 < s.re + c ≤ 2`.
Its constant may depend on the coefficient sequence and majorant.
The imaginary part of `s` is independent of the integration height.
The expression `ψ(2x)` is evaluated at the natural floor of `2x`. -/
theorem truncatedPerron_error_noninteger (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hcoeff : a =O[atTop] ψ)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ) (N : ℕ),
      0 < x → 0 < c → 1 ≤ T → s.re + c ∈ Ioc 1 2 →
      x ∉ Set.range (Int.cast : ℤ → ℝ) → |x - (N : ℝ)| ≤ 1 / 2 →
      ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
        C * (x ^ c / (T * (s.re + c - 1) ^ α) +
          ψ ⌊2 * x⌋₊ * x ^ (1 - s.re) * |Real.log x| / T +
          ψ N * x ^ (1 - s.re) / (T * |x - (N : ℝ)|)) := by
  sorry

/-- Paper: Lemma B.7.1.1, Equation (B.7.1.5), p. 644. The truncated
Perron error at an integer cutoff includes the half-weight endpoint error.
Deviation: The simplified estimate is uniform for `1 < s.re + c ≤ 2`.
Its constant may depend on the coefficient
sequence and majorant. The imaginary part of `s` is independent of the
integration height. -/
theorem truncatedPerron_error_integer (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hcoeff : a =O[atTop] ψ)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (m : ℕ) (c T : ℝ),
      0 < m → 0 < c → 1 ≤ T → s.re + c ∈ Ioc 1 2 →
      ‖perronHalfWeightedSum a s m - truncatedPerronIntegral (LSeries a) s m c T‖ ≤
        C * ((m : ℝ) ^ c / (T * (s.re + c - 1) ^ α) +
          ψ (2 * m) * (m : ℝ) ^ (1 - s.re) * Real.log m / T +
          ψ m * c * (m : ℝ) ^ (-s.re) / T) := by
  sorry

/-- Paper: Equation (B.7.1.8), p. 645, and the coefficient choice on p. 646.
The cutoff polynomial sums the twisted von Mangoldt coefficients, grouped by
the norm of the ideal, through the last integer norm at most `x`. -/
def heckeLogDerivPolynomial (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n

/-- Paper: Equation (B.7.1.8), p. 645. The polynomial grouped by norm equals
the sum over all nonzero integral ideals whose norms are at most the cutoff. -/
theorem heckeLogDerivPolynomial_eq_sum_ideals (χ : U[F]) (x : ℝ) (s : ℂ) :
    heckeLogDerivPolynomial χ x s =
      ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x},
        heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ s := by
  sorry

/-- Paper: Theorem B.7.1.2(1), p. 645. The set `J_b` consists of the integer
cuts and the real cuts at distance at least `b` from the integers. -/
def perronCutoffSet (b : ℝ) : Set ℝ :=
  Set.range (Int.cast : ℤ → ℝ) ∪ {x : ℝ | b ≤ |x - (round x : ℝ)|}

/-- Paper: Theorem B.7.1.2(1), p. 645. For positive `b`, integer cuts are always
allowed and half-integer cuts are allowed precisely when `b ≤ 1/2`. -/
theorem perronCutoffSet_integer_half_integer {b : ℝ} (hb : 0 < b) (n : ℤ) :
    (n : ℝ) ∈ perronCutoffSet b ∧
      ((n : ℝ) + 1 / 2 ∈ perronCutoffSet b ↔ b ≤ 1 / 2) := by
  sorry

/-- Paper: Theorem B.7.1.2(1), Equation (B.7.1.8), p. 645. For the character
`|·|^(-it₀)`, the cutoff polynomial on the 1-line is the negative shifted
Dedekind zeta logarithmic derivative plus the oscillatory pole term and an
analytic remainder. The remainder tends uniformly to zero on compact subsets
away from the pole along `J_b`. -/
theorem heckeLogDerivPolynomial_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (K : Set ℂ) (hK : IsCompact K) (hKline : K ⊆ oneLine)
    (hpole : (1 + Complex.I * t₀ : ℂ) ∉ K) {b : ℝ} (hb : 0 < b) :
    ∃ error : ℝ → ℂ → ℂ,
      (∀ x > 1, AnalyticOnNhd ℂ (error x) oneLine ∧
        ∀ s ∈ oneLine, s ≠ 1 + Complex.I * t₀ →
          heckeLogDerivPolynomial χ x s = -logDeriv Z (s - Complex.I * t₀) +
            (x : ℂ) ^ (1 + Complex.I * t₀ - s) / (1 + Complex.I * t₀ - s) + error x s) ∧
      TendstoUniformlyOn error (fun _ ↦ 0) (atTop ⊓ 𝓟 (perronCutoffSet b)) K := by
  sorry

/-- Paper: Theorem B.7.1.2(1), Equation (B.7.1.9), p. 645. At the pole
ordinate, the cutoff polynomial differs from the logarithm of the cutoff by
a bounded quantity as the real cutoff tends to infinity.
Deviation: The implied constant is for the fixed number field. The double-pole
residue on p. 648 involves the field's Euler–Kronecker constant. -/
theorem heckeLogDerivPolynomial_at_pole (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    (fun x : ℝ ↦ heckeLogDerivPolynomial χ x (1 + Complex.I * t₀) - (Real.log x : ℂ))
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry

/-- Paper: Theorem B.7.1.2(2), Equation (B.7.1.10), p. 646. For a character
nontrivial on the norm-one subgroup, the cutoff polynomial on the 1-line is the
negative logarithmic derivative plus an analytic remainder that tends uniformly
to zero on compact subsets along `J_b`.
Deviation: The positive parameter `b` occurring in part (1) is made explicit. -/
theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℂ) (hK : IsCompact K) (hKline : K ⊆ oneLine) {b : ℝ} (hb : 0 < b) :
    ∃ error : ℝ → ℂ → ℂ,
      (∀ x > 1, AnalyticOnNhd ℂ (error x) oneLine ∧
        ∀ s ∈ oneLine, heckeLogDerivPolynomial χ x s = -logDeriv L s + error x s) ∧
      TendstoUniformlyOn error (fun _ ↦ 0) (atTop ⊓ 𝓟 (perronCutoffSet b)) K := by
  sorry

/-- Paper: Equation (B.7.1.11), p. 646. Perron's estimate for the full Hecke
cutoff includes a correction for the remaining half of the last coefficient
at an integer cutoff.
Deviation: Adds the half-endpoint correction. For `c ≥ 1` the absence of
a norm-one coefficient gives exponential decay to the right. The initial contour lies
strictly to the right of the pole, so the estimate also holds at the pole ordinate. -/
theorem heckeLogDerivPolynomial_perron_error (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → 1 ≤ T →
      ‖heckeLogDerivPolynomial χ x s -
        truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T -
        (if (⌊x⌋₊ : ℝ) = x then
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2
         else 0)‖ ≤
        C * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
          (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
           else Real.log x / (T * |x - (round x : ℝ)|))) := by
  sorry

-- TODO(paper-gap): The proof of (B.7.1.12) bounds the raw logarithmic derivative
-- on a region containing its pole. Subtract the principal part before using
-- compactness, and use the maximum absolute shifted height on the rectangle.

/-- Paper: Equation (B.7.1.12), p. 647. The integral along the left edge is
bounded by the cutoff to the power `-δ` times a cubed logarithm.
Deviation: The width `δ` uses the maximum absolute shifted height. The
estimate allows the unregularized logarithmic derivative to contribute a
term of order `1 / δ` near its pole. The punctured disc is the hypothesis
on `α` in Theorem B.6.1.3. Both constants may depend on the chosen width. -/
theorem dedekindZeta_perron_left_bound (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x T : ℝ),
      s ∈ oneLine → 1 ≤ x → T₀ + |s.im - t₀| ≤ T →
      let height := T + |s.im - t₀| + 3
      let δ := α * A / Real.log (B * height)
      ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
        (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖ ≤
        C * x ^ (-δ) * (Real.log height) ^ 3 := by
  sorry

/-- Paper: Equations (B.7.1.13)–(B.7.1.14), p. 647. On either horizontal
edge the squared logarithm of its shifted height controls the integral.
Deviation: Each edge uses its own absolute shifted height. The contour
width uses the maximum of both heights, and the estimate starts at a
sufficiently large height for the logarithmic-derivative estimate of §B.6.
The punctured disc is its hypothesis on `α`. Both constants may depend on the width. -/
theorem dedekindZeta_perron_horizontal_bound (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x c T y : ℝ),
      s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - t₀| ≤ T → (y = -T ∨ y = T) →
      let δ := α * A / Real.log (B * (T + |s.im - t₀| + 3))
      ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) *
        (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
        C * x ^ c * (Real.log (|s.im - t₀ + y| + 3)) ^ 2 / (T * Real.log x) := by
  sorry

-- TODO(paper-gap): The uniform limit away from the pole does not justify taking
-- the limit at the pole in (B.7.1.9). The contour there has a double pole.

end RiemannMasullo
