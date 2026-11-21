module

public import RiemannMasullo.Ch02_AdelicTheta.Sec3

/-!
# Small-norm estimates for S-local adelic theta

Masullo, §2.4, pp. 106–116. As in §2.3, the Lean place set records the
finite places only. All archimedean places are included in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Asymptotics Bornology Filter IsDedekindDomain MeasureTheory NumberField Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "classOf" => (QuotientGroup.mk : Iₛ → SIdeleQuotient F S)
local notation "normℝ[" K "," V "]" =>
  fun (g : (SAdeleRing K V)ˣ) ↦ ((Units.val (sIdeleNorm K V g) : ℝ≥0) : ℝ)
local notation "smallNorm[" K "," V "]" => comap normℝ[K, V] (𝓝[>] (0 : ℝ))

-- As in §2.3, the homogeneous operator takes its Haar measure as a parameter.
local instance : MeasurableSpace J₁ := borel _

/-! ## The rational number field -/

section Rat

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- Paper: Proposition 2.4.1.1, p. 107. Over the rationals the theta
function grows at most as the absolute log norm to the number of finite
places in S, uniformly as the S-idelic norm tends to zero from above. -/
theorem sLocalAdelicTheta_rat_log_growth (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalAdelicTheta ℚ S f g) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by sorry

/-- Paper: Proposition 2.4.1.1, pp. 107, 110. Over the rationals the same
logarithmic growth bound holds for homogeneous theta for each continuous
character of the norm-one S-idele classes.
Deviation: As in §2.3, the Haar measure on those classes is explicit. -/
theorem sLocalHomogeneousAdelicTheta_rat_log_growth
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S)))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalHomogeneousAdelicTheta ℚ S μ ω f (QuotientGroup.mk g)) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by sorry

end Rat

-- TODO(paper-gap): Lemma 2.4.1.2 prints C in (2.4.1.3) after quantifying Cφ.
-- A coefficient depending only on T, M, N and the bases fails for
-- M = 1, N = 2, a₁ = 2, T = 1 and φ(t) = K on (0, 1), zero for t ≥ 1.
-- At t = 2⁻ⁿ the sum is K n, so the coefficient must be at least K / log 2.

/-- Paper: Lemma 2.4.1.2, p. 107. For a bounded function with power decay
at infinity, the sum of the norms over the multiplicative grid with M bases
greater than one converges and is bounded by a constant times the Mth power
of the absolute log near zero.
Deviation: Equation (2.4.1.3) uses the existentially quantified constant
`Cφ`. The real-domain function is used only at positive arguments, and
summability is explicit. -/
theorem summable_geometric_grid_log_bound (M N : ℕ) (hM : 1 ≤ M) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ)
    (hbounded : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ C)
    (hdecay : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖φ t‖ ≤ A * (t ^ N)⁻¹) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t : ℝ, 0 < t → t < T₀ →
      let term : (Fin M → ℕ) → ℝ := fun k ↦ ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ Cφ * |Real.log t| ^ M := by sorry

-- TODO(paper-gap): The geometric series in (2.4.1.5) has an unrounded
-- lower endpoint, and (2.4.1.8) loses a factor in the power of T. The
-- reduction in (2.4.1.14) changes the local support condition. The
-- application on p. 109 omits S = {∞}, where the S-units are {±1}.
-- TODO(paper-gap): The p. 110 ergodicity assertion fails for S = {∞, p} over ℚ.
-- On Hₚ with nonzero real coordinate, log |x| modulo log p is invariant.
-- Theta can be bounded at zero, for instance when S = {∞} over ℚ. Its
-- Mellin integral there fails to converge uniformly on the entire open
-- right half-plane, even for the real Gaussian with trivial character.

/-! ## The general case -/

local notation "normℝ" => normℝ[F, S]
local notation "smallNorm" => smallNorm[F, S]

-- TODO(paper-gap): In the proof of Theorem 2.4.2.1, (2.4.2.2) leaves x∞
-- free on the right after taking the supremum on the left. Equation
-- (2.4.2.3) fails for the real Gaussian times the local integer indicators
-- at 2 and 3. The count of S-unit multiples in a fixed real annulus
-- outside the ball can grow without bound. The averaged estimate
-- (2.4.2.4) alone does not give a pointwise bound.

/-- Paper: Theorem 2.4.2.1, p. 111. Below S-idelic norm one, the theta
function is bounded by a constant times the absolute log norm to the
power `|S| - 1`, plus an additive constant. Both constants are uniform
on a bounded set of Schwartz–Bruhat functions. -/
theorem sLocalAdelicTheta_log_growth_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖sLocalAdelicTheta F S f g‖ ≤
        C₁ * |Real.log (normℝ g)| ^ (Fintype.card (InfinitePlace F) + S.card - 1) + C₂ := by sorry

/-! ## Order of growth -/

variable (ε : ℝ) (hε : 0 < ε)

include hε

-- TODO(paper-gap): The derivative of φ(t, g) on p. 113 drops g and ω(g).
-- In (2.4.3.3) the supremum is unweighted since |g′| = 1. It can be
-- infinite, as for the Gaussian example at (2.4.2.3).

/-- Paper: Proposition 2.4.3.1(1), p. 113. Multiplying S-local theta by
any positive real power of the S-idelic norm gives a bounded function
as the norm tends to zero from above. -/
theorem sLocalAdelicTheta_norm_pow_isBigO (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by sorry

/-- Paper: Proposition 2.4.3.1(1), p. 113. The same small-norm bound
holds for homogeneous theta multiplied by a positive norm power.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_isBigO
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by sorry

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the bound for theta times a positive norm power is uniform on a bounded
set of test functions. -/
theorem sLocalAdelicTheta_norm_pow_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the corresponding homogeneous bound is uniform on a bounded set of test functions.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(3), p. 113. The uniform bound for theta
times a positive norm power holds below S-idelic norm one. -/
theorem sLocalAdelicTheta_norm_pow_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(3), p. 113. The corresponding uniform
homogeneous bound holds below S-idelic norm one.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded_threshold_one
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by sorry

/-- Paper: Corollary 2.4.3.2, p. 115. Theta multiplied by any positive
real power of the S-idelic norm tends to zero as that norm tends to zero. -/
theorem sLocalAdelicTheta_norm_pow_tendsto_zero (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) smallNorm (𝓝 0) := by sorry

/-- Paper: Corollary 2.4.3.2, p. 115. The same vanishing holds for
homogeneous theta for every continuous character of the norm-one classes.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_tendsto_zero
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g))
      smallNorm (𝓝 0) := by sorry

end RiemannMasullo
