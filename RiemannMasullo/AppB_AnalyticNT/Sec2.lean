module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Mellin transforms and asymptotic Cauchy integrals

Masullo, §B.2, pp. 591–604. A Schwartz–Bruhat function on the positive reals is
represented by its real-line Schwartz map in the coordinate `x = log t`.
Other functions on the positive reals are represented by functions on ℝ whose
values outside the positive reals are immaterial.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Asymptotics ContDiff ENNReal NNReal SchwartzMap Topology

namespace RiemannMasullo

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "verticalTrace" =>
  (fun (Φ : ℂ → ℂ) (σ : ℝ) (y : ℝ) ↦ Φ (verticalPoint σ y))
local notation "atAbsInfty" => (comap abs atTop)
local notation "openStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Ioo a b)
local notation "closedStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Icc a b)
set_option quotPrecheck false in
local notation "stripWithTop" =>
  (fun (a : ℝ) (b : WithTop ℝ) ↦ {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
set_option quotPrecheck false in
local notation "heightBound" =>
  (fun (Φ : ℂ → ℂ) (J : Set ℝ) (N : ℕ) (C : ℝ) ↦
    ∀ σ ∈ J, ∀ y : ℝ, y ≠ 0 → ‖Φ (verticalPoint σ y)‖ ≤ C / |y| ^ N)
set_option quotPrecheck false in
local notation "eventualHeightBound" =>
  (fun (Φ : ℂ → ℂ) (J : Set ℝ) (N : ℕ) ↦
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in atAbsInfty, ∀ σ ∈ J,
      ‖Φ (verticalPoint σ y)‖ ≤ C / |y| ^ N)
set_option quotPrecheck false in
local notation "lpTail" =>
  (fun (p : ℝ) (N : ℕ) ↦ ∫ y : ℝ in {y | 1 / 2 ≤ |y|}, 1 / |y| ^ (p * (N : ℝ)))
local notation "logWeight" =>
  (fun (σ x : ℝ) ↦ (Real.exp (σ * x) : ℂ))
local notation "fromLog" => (fun (f : ℝ → ℂ) (t : ℝ) ↦ f (Real.log t))

/-- Paper: §B.2.1, p. 592. The half-plane Hardy condition is holomorphy
and a finite uniform bound on the vertical Lᵖ norms. -/
def MemLeftHardy (Φ : ℂ → ℂ) (b p : ℝ) : Prop :=
  0 < p ∧ DifferentiableOn ℂ Φ (Complex.re ⁻¹' Iio b) ∧
    ∃ C : ℝ≥0, ∀ σ < b, eLpNorm (verticalTrace Φ σ) (ENNReal.ofReal p) volume ≤ C

/-- Paper: §B.2.1, p. 592. At exponent one, the half-plane Hardy bound is
equivalent to a common finite bound on the integrals of the vertical absolute values.
Deviation: Sanity check for the extended-norm formulation. -/
theorem memLeftHardy_one_iff (Φ : ℂ → ℂ) (b : ℝ) :
    MemLeftHardy Φ b 1 ↔ DifferentiableOn ℂ Φ (Complex.re ⁻¹' Iio b) ∧
      ∃ C : ℝ, ∀ σ < b, Complex.VerticalIntegrable Φ σ ∧
        (∫ y : ℝ, ‖Φ (verticalPoint σ y)‖) ≤ C := by sorry

-- TODO(paper-gap): Footnotes 5 and 6 ask how the cited Hardy-space results
-- apply on the left half-plane. Footnote 7 asks how far the decay is uniform.

/-- Paper: Definition B.2.1.1(1), p. 593. Every derivative of the logarithmic
profile decays faster than every exponential as the log coordinate tends to positive infinity.
Deviation: Uses logarithmic differentiation as allowed in Remark B.2.1.2. -/
def ForwardSemiExponentialDecay (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ (j : ℕ) (A : ℝ), 0 < A →
    (iteratedDeriv j (f : ℝ → ℂ)) =O[atTop] fun x ↦ Real.exp (-A * x)

/-- Paper: Definition B.2.1.1(1), p. 593. Every derivative of the logarithmic
profile decays faster than every exponential as the log coordinate tends to negative infinity.
Deviation: Uses logarithmic differentiation as allowed in Remark B.2.1.2. -/
def BackwardSemiExponentialDecay (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ (j : ℕ) (A : ℝ), 0 < A →
    (iteratedDeriv j (f : ℝ → ℂ)) =O[atBot] fun x ↦ Real.exp (A * x)

/-- Paper: Definition B.2.1.1(2), p. 593. Exponential decay requires
the two semi-exponential decay conditions on the logarithmic profile. -/
def ExponentialDecay (f : 𝓢(ℝ, ℂ)) : Prop :=
  ForwardSemiExponentialDecay f ∧ BackwardSemiExponentialDecay f

/-- Paper: Definition B.2.1.1, p. 593. The ordinary real Gaussian
satisfies all three decay conditions as a logarithmic profile.
Deviation: Sanity check for the three definitions. -/
theorem exists_gaussian_logProfile_exponentialDecay :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x : ℝ, f x = Real.exp (-(x ^ 2))) ∧
      ForwardSemiExponentialDecay f ∧ BackwardSemiExponentialDecay f ∧
      ExponentialDecay f := by sorry

/-- Paper: Remark B.2.1.2, p. 593. Forward decay is equivalent to the
Schwartz condition on every nonnegatively weighted logarithmic profile. -/
theorem forwardSemiExponentialDecay_iff_weighted_schwartz (f : 𝓢(ℝ, ℂ)) :
    ForwardSemiExponentialDecay f ↔ ∀ A : ℝ, 0 ≤ A →
      ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight A x * f x := by sorry

-- TODO(paper-gap): The single rate O(e⁻ˣ) in the last assertion of Remark B.2.1.2
-- does not imply the family of bounds required by Definition B.2.1.1(1).
-- TODO(paper-gap): Remark B.2.1.3 quantifies over every exponent and over all t.
-- The exponent zero forces boundedness and the bound at t = 1 forces vanishing there.
-- TODO(paper-gap): Lemma B.2.1.4(1) claims that the zero extension is Schwartz.
-- A smooth function supported away from zero and equal to 1/t for large t
-- has backward semi-exponential decay but fails the ordinary Schwartz bounds.

/-- Paper: Lemma B.2.1.4(1), p. 593. Backward semi-exponential decay makes the
zero extension smooth across the origin.
Deviation: The ordinary Schwartz assertion is false without forward decay. -/
theorem contDiff_zeroExtension_of_backwardSemiExponentialDecay (f : 𝓢(ℝ, ℂ))
    (hf : BackwardSemiExponentialDecay f) :
    ContDiff ℝ ∞ ((Ioi (0 : ℝ)).indicator (fromLog f)) := by sorry

/-- Paper: Lemma B.2.1.4(2), p. 593. Inversion on the positive reals is
the continuous linear involution given by reflection of the logarithmic profile. -/
theorem exists_schwartzLogReflection :
    ∃ R : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ), (∀ (f : 𝓢(ℝ, ℂ)) (x : ℝ), R f x = f (-x)) ∧
      Involutive R := by sorry

/-- Paper: Lemma B.2.1.4(2), p. 593. Exponential decay is invariant under
reflection of the logarithmic profile. -/
theorem exponentialDecay_iff_reflected (f g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g x = f (-x)) :
    ExponentialDecay g ↔ ExponentialDecay f := by sorry

/-- Paper: Lemma B.2.1.4(2), p. 593. Reflection interchanges forward
and backward semi-exponential decay. -/
theorem backwardSemiExponentialDecay_iff_forward_reflected
    (f g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g x = f (-x)) :
    BackwardSemiExponentialDecay g ↔ ForwardSemiExponentialDecay f := by sorry

/-- Paper: Lemma B.2.1.4(3), p. 593. The zero extension of a function with
exponential decay is an ordinary Schwartz function on the real line. -/
theorem exists_schwartz_zeroExtension_of_exponentialDecay (f : 𝓢(ℝ, ℂ))
    (hf : ExponentialDecay f) :
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = (Ioi (0 : ℝ)).indicator (fromLog f) := by sorry

/-- Paper: Lemma B.2.1.4(4), p. 593. Logarithmic differentiation preserves
forward semi-exponential decay. -/
theorem ForwardSemiExponentialDecay.deriv (f : 𝓢(ℝ, ℂ)) (hf : ForwardSemiExponentialDecay f) :
    ForwardSemiExponentialDecay (SchwartzMap.derivCLM ℂ ℂ f) := by sorry

/-- Paper: Lemma B.2.1.4(4), p. 593. Logarithmic differentiation preserves
backward semi-exponential decay. -/
theorem BackwardSemiExponentialDecay.deriv (f : 𝓢(ℝ, ℂ)) (hf : BackwardSemiExponentialDecay f) :
    BackwardSemiExponentialDecay (SchwartzMap.derivCLM ℂ ℂ f) := by sorry

/-- Paper: Lemma B.2.1.4(4), p. 593. Logarithmic differentiation preserves
exponential decay. -/
theorem ExponentialDecay.deriv (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) :
    ExponentialDecay (SchwartzMap.derivCLM ℂ ℂ f) := by sorry

-- Equation (B.2.1.2) is Mathlib's `mellin`, with `MellinConvergent`
-- for absolute convergence and `HasMellin` for a convergent integral with a specified value.

section ForwardMellin

variable (f : 𝓢(ℝ, ℂ)) (hf : ForwardSemiExponentialDecay f)

include hf

/-- Paper: Proposition B.2.1.5, p. 594. The Mellin integral converges
absolutely in the open right half-plane. -/
theorem mellinConvergent_of_forwardSemiExponentialDecay (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fromLog f) s := by sorry

/-- Paper: Proposition B.2.1.5(1), p. 594. The Mellin transform is
holomorphic in the open right half-plane. -/
theorem differentiableOn_mellin_of_forwardSemiExponentialDecay :
    DifferentiableOn ℂ (mellin (fromLog f)) (Complex.re ⁻¹' Ioi 0) := by sorry

/-- Paper: Proposition B.2.1.5(2), p. 594. For each positive integer
power, one constant gives the vertical decay bound throughout the prescribed closed strip. -/
theorem mellin_heightBound_of_forwardSemiExponentialDecay
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), heightBound (mellin (fromLog f)) (Icc a b) N C := by sorry

/-- Paper: Proposition B.2.1.5(3), p. 594. The Lᵖ norms on the vertical
lines admit the displayed central and tail bound, uniformly in the abscissa.
Deviation: The constant from part (2) is supplied with its bound. -/
theorem mellin_verticalLp_of_forwardSemiExponentialDecay
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (p : ℝ) (hp : 1 ≤ p)
    (N : ℕ) (hN : 1 < N) (C : ℝ) (hC : heightBound (mellin (fromLog f)) (Icc a b) N C) :
    ∃ B > (0 : ℝ), ∀ σ ∈ Icc a b,
      eLpNorm (verticalTrace (mellin (fromLog f)) σ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((B ^ p + C ^ p * lpTail p N) ^ (1 / p)) := by sorry

end ForwardMellin

/-- Paper: Lemma B.2.1.6, p. 594. Iterating the Euler derivative
before the exponential change of variables gives the ordinary iterated derivative afterwards. -/
theorem iterate_eulerDeriv_comp_exp (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    ((fun g : ℝ → ℂ ↦ fun t ↦ (t : ℂ) * deriv g t)^[N]) φ (Real.exp x) =
      iteratedDeriv N (fun u : ℝ ↦ φ (Real.exp u)) x := by sorry

-- TODO(paper-gap): Theorem B.2.1.7(1)(c) places a uniform bound on a strip
-- containing the prescribed poles. Even on the punctured strip it rules out
-- every nonzero pole. The statement needs a specified exclusion or height restriction.

/-- Paper: Theorem B.2.1.7(2), p. 596. A finite power-log expansion at zero
gives a meromorphic continuation, with poles of the prescribed orders.
Deviation: Meromorphic continuation is in normal form. The coefficients are
indexed by their logarithm degree, starting at zero. -/
theorem exists_meromorphic_mellin_of_asymptoticExpansion
    (a A : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hA : A < 0) (hab : (a : WithTop ℝ) < b)
    (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (hWeighted : ∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
      ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight σ x * φ (Real.exp x))
    (poles : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ α ∈ poles, 1 ≤ m α)
    (hpoles : ∀ α ∈ poles, (-α).re ∈ Ioc A a) (c : ℂ → ℕ → ℂ)
    (hc : ∀ α ∈ poles, c α (m α - 1) ≠ 0)
    (hAsymptotic : (fun t : ℝ ↦ φ t -
      ∑ α ∈ poles, ∑ j ∈ Finset.range (m α), c α j * (t : ℂ) ^ α * (Real.log t : ℂ) ^ j)
      =O[𝓝[>] (0 : ℝ)] fun t ↦ t ^ (-A)) :
    ∃ F : ℂ → ℂ, MeromorphicNFOn F (stripWithTop A b) ∧
      (∀ s ∈ stripWithTop a b, HasMellin φ s (F s)) ∧
      (∀ α ∈ poles, meromorphicOrderAt F (-α) = -((m α : ℕ) : ℤ)) ∧
      ∀ s ∈ stripWithTop A b, -s ∉ poles → 0 ≤ meromorphicOrderAt F s := by sorry

/-- Paper: Equation (B.2.1.19), p. 597. The logarithmic profile is
m-times continuously differentiable and its derivatives through order m vanish at infinity. -/
def MemLogContDiffZero (m : ℕ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ (m : ℕ∞) f ∧
    ∀ j ≤ m, Tendsto (iteratedDeriv j f) (cocompact ℝ) (𝓝 0)

/-- Paper: Equation (B.2.1.19), p. 597. At order zero the condition
means that the logarithmic profile is a continuous map vanishing at infinity.
Deviation: Sanity check using Mathlib's bundled space. -/
theorem memLogContDiffZero_zero_iff (f : ℝ → ℂ) :
    MemLogContDiffZero 0 f ↔
      ∃ g : ZeroAtInftyContinuousMap ℝ ℂ, (g : ℝ → ℂ) = f := by sorry

/-- Paper: Equation (B.2.1.19), p. 597. The norm is the sum of the
supremum norms of the logarithmic derivatives through order m. -/
def logContDiffZeroNorm (m : ℕ) (f : {f : ℝ → ℂ // MemLogContDiffZero m f}) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), sSup (range fun x : ℝ ↦ ‖iteratedDeriv j f.val x‖)

/-- Paper: Equation (B.2.1.19), p. 597. At order zero the norm is the
supremum of the absolute value on the positive reals.
Deviation: Sanity check for the logarithmic norm. -/
theorem logContDiffZeroNorm_zero (f : {f : ℝ → ℂ // MemLogContDiffZero 0 f}) :
    logContDiffZeroNorm 0 f = sSup (range fun x : ℝ ↦ ‖f.val x‖) := by sorry

-- TODO(paper-gap): In the proof of Proposition B.2.1.8, the integrals in dτ
-- need the factor 1/(2π). The boundary term of (B.2.1.22) uses f, since it
-- comes from integrating the derivative of f(s)t⁻ˢ.

/-- Paper: Proposition B.2.1.8, p. 597. Polynomial decay of a holomorphic
function on closed interior strips gives a Mellin inverse with the stated differentiability,
vanishing and square-integrability properties.
Deviation: Square integrability for dt/t is written in logarithmic coordinates. -/
theorem exists_mellin_of_holomorphicOn_isPolynomialDecay
    (a : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hab : (a : WithTop ℝ) < b)
    (N : ℝ) (hN : 2 < N) (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (stripWithTop a b))
    (hBound : ∀ c d : ℝ, a < c → c ≤ d → (d : WithTop ℝ) < b →
      BddAbove ((fun s : ℂ ↦ ‖s‖ ^ N * ‖F s‖) '' closedStrip c d))
    (m : ℕ) (hm : (m : ℝ) < N - 1) :
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ (m : ℕ∞) φ (Ioi 0) ∧
      (∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
        MemLogContDiffZero m (fun x : ℝ ↦ logWeight σ x * φ (Real.exp x)) ∧
        MemLp (fun x : ℝ ↦ logWeight σ x * φ (Real.exp x)) 2 volume) ∧
      ∀ s ∈ stripWithTop a b, HasMellin φ s (F s) := by sorry

section ExponentialMellin

variable (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)

include hf

/-- Paper: Equation (B.2.1.26), p. 598. The Mellin integral of an
exponentially decaying function converges absolutely at every complex exponent. -/
theorem mellinConvergent_of_exponentialDecay (s : ℂ) :
    MellinConvergent (fromLog f) s := by sorry

/-- Paper: Proposition B.2.1.9(1), p. 598. The Mellin transform of an
exponentially decaying function is entire. -/
theorem differentiable_mellin_of_exponentialDecay :
    Differentiable ℂ (mellin (fromLog f)) := by sorry

/-- Paper: Proposition B.2.1.9(2), p. 598. The Mellin transform satisfies
every inverse-power height bound uniformly on each bounded closed strip. -/
theorem mellin_heightBound_of_exponentialDecay (a b : ℝ) (hab : a < b) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), heightBound (mellin (fromLog f)) (Icc a b) N C := by sorry

/-- Paper: Proposition B.2.1.9(3), p. 599. On a closed strip, the vertical
Lᵖ norms satisfy the bound with the exponentially weighted L¹ term.
Deviation: The L¹ term uses the logarithmic coordinate, and the constant from
part (2) is supplied with its bound. -/
theorem mellin_verticalLp_of_exponentialDecay
    (a b : ℝ) (hab : a < b) (p : ℝ) (hp : 1 ≤ p)
    (N : ℕ) (hN : 1 < N) (C : ℝ) (hC : heightBound (mellin (fromLog f)) (Icc a b) N C) :
    ∀ σ ∈ Icc a b,
      eLpNorm (verticalTrace (mellin (fromLog f)) σ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal
          (((∫ x : ℝ, Real.exp ((max |a| |b| + (N : ℝ)) * |x|) * ‖f x‖) ^ p +
            C ^ p * lpTail p N) ^ (1 / p)) := by sorry

/-- Paper: Proposition B.2.1.9(4), p. 599. Support in t > 1 permits the
choice of one height-decay constant for the whole left half-plane.
Deviation: The cited estimate is (B.2.1.27). The support is tested in x = log t. -/
theorem mellin_heightBound_left_of_exponentialDecay
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Ioi 0) (b : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), heightBound (mellin (fromLog f)) (Iic b) N C := by sorry

/-- Paper: Proposition B.2.1.9(4), p. 599. If the function is supported in
t > 1, its Mellin transform belongs to each left half-plane Hardy class with p ≥ 1. -/
theorem memLeftHardy_mellin_of_exponentialDecay
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Ioi 0) (b p : ℝ) (hp : 1 ≤ p) :
    MemLeftHardy (mellin (fromLog f)) b p := by sorry

local notation "shiftedMellin" =>
  (fun (n : ℕ) (δ : ℝ) (s : ℂ) ↦ mellin (fromLog f) ((n : ℂ) + (δ : ℂ) * s))

variable (n : ℕ) (δ : ℝ) (hδ : δ = 1 ∨ δ = -1)

include hδ

/-- Paper: Corollary B.2.1.10(1), p. 600. The two shifts of the Mellin
variable, with and without reflection, give entire functions. -/
theorem differentiable_shiftedMellin_of_exponentialDecay :
    Differentiable ℂ (shiftedMellin n δ) := by sorry

/-- Paper: Corollary B.2.1.10(1), p. 600. Both shifted transforms are
bounded on each vertical strip of bounded width. -/
theorem bddAbove_norm_shiftedMellin_of_exponentialDecay (a b : ℝ) (hab : a < b) :
    BddAbove ((fun s : ℂ ↦ ‖shiftedMellin n δ s‖) '' closedStrip a b) := by sorry

/-- Paper: Corollary B.2.1.10(1), p. 600. The inequality (B.2.1.28)
applies to both shifts with the weighted, possibly reflected input.
Deviation: The sign encodes both shifts. The L¹ term uses the logarithmic
profile exp(nδx) f(δx) of the shifted transform. -/
theorem shiftedMellin_verticalLp_of_exponentialDecay
    (a b : ℝ) (hab : a < b) (N : ℕ) (hN : 1 < N) :
    ∃ C > (0 : ℝ), heightBound (shiftedMellin n δ) (Icc a b) N C ∧
      ∀ p : ℝ, 1 ≤ p → ∀ σ ∈ Icc a b,
        eLpNorm (verticalTrace (shiftedMellin n δ) σ) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal
            (((∫ x : ℝ, Real.exp (((n : ℝ) * δ) * x + (max |a| |b| + (N : ℝ)) * |x|) *
                  ‖f (δ * x)‖) ^ p + C ^ p * lpTail p N) ^ (1 / p)) := by sorry

/-- Paper: Corollary B.2.1.10(2), p. 600. Multiplying either shifted Mellin
transform by a meromorphic function of polynomial growth gives rapid vertical decay.
Deviation: The proof identifies the intended estimate as (B.2.1.27). -/
theorem mul_shiftedMellin_eventualHeightBound (hn : 1 ≤ n)
    (a b : ℝ) (hab : a < b) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (openStrip a b))
    (hPoles : {s : ℂ | s ∈ openStrip a b ∧ meromorphicOrderAt F s < 0}.Finite)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hGrowth : ∀ᶠ y : ℝ in atAbsInfty, ∀ σ ∈ Ioo a b, ‖F (verticalPoint σ y)‖ ≤ A * |y| ^ B)
    (N : ℕ) (hN : 1 ≤ N) :
    eventualHeightBound (fun s ↦ F s * shiftedMellin n δ s) (Ioo a b) N := by sorry

end ExponentialMellin

/-- Paper: Definition B.2.2.1, p. 600. A holomorphic function on an open
strip has uniform rapid decay in height on every closed interior strip. -/
def UniformlySchwartzOnStrip (Φ : ℂ → ℂ) (a b : ℝ) : Prop :=
  a < b ∧ DifferentiableOn ℂ Φ (openStrip a b) ∧
    ∀ ε > (0 : ℝ), a + ε < b - ε → ∀ N : ℕ, 1 ≤ N →
      eventualHeightBound Φ (Icc (a + ε) (b - ε)) N

/-- Paper: Definition B.2.2.1, p. 600. An entire function is Schwartz on
vertical strips if it has uniform rapid decay on every bounded open strip. -/
def SchwartzOnVerticalStrips (Φ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Φ ∧ ∀ a b : ℝ, a < b → UniformlySchwartzOnStrip Φ a b

/-- Paper: Definition B.2.2.1, p. 600. A holomorphic function on a left
half-plane has uniform rapid decay in height on every smaller closed left half-plane. -/
def SchwartzOnLeftHalfPlane (Φ : ℂ → ℂ) (b : ℝ) : Prop :=
  DifferentiableOn ℂ Φ (Complex.re ⁻¹' Iio b) ∧
    ∀ ε > (0 : ℝ), ∀ N : ℕ, 1 ≤ N → eventualHeightBound Φ (Iic (b - ε)) N

/-- Paper: Example B.2.2.2, p. 600. Exponentially decaying functions give
Mellin transforms that are Schwartz on vertical strips. -/
theorem schwartzOnVerticalStrips_mellin_of_exponentialDecay
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) :
    SchwartzOnVerticalStrips (mellin (fromLog f)) := by sorry

/-- Paper: Example B.2.2.2, p. 600. Exponentially decaying functions give
Mellin transforms that are uniformly Schwartz on each prescribed vertical strip. -/
theorem uniformlySchwartzOnStrip_mellin_of_exponentialDecay
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a b : ℝ) (hab : a < b) :
    UniformlySchwartzOnStrip (mellin (fromLog f)) a b := by sorry

/-- Paper: Definition B.2.2.1, p. 600. An exponentially decaying function
supported in t > 1 gives a Mellin transform that is Schwartz on each left half-plane.
Deviation: Sanity check using Proposition B.2.1.9(4). -/
theorem schwartzOnLeftHalfPlane_mellin_of_exponentialDecay
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Ioi 0) (b : ℝ) :
    SchwartzOnLeftHalfPlane (mellin (fromLog f)) b := by sorry

section UniformRiemannLebesgue

variable (f : 𝓢(ℝ, ℂ)) (a b : ℝ) (hab : a < b)
  (hWeighted : ∀ σ ∈ Icc a b, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight σ x * f x)

include hab hWeighted

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin integral converges
absolutely throughout the closed strip of Schwartz weights. -/
theorem mellinConvergent_on_strip_of_weighted_schwartz (s : ℂ) (hs : s ∈ closedStrip a b) :
    MellinConvergent (fromLog f) s := by sorry

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform is continuous
on the closed strip of Schwartz weights. -/
theorem continuousOn_mellin_of_weighted_schwartz :
    ContinuousOn (mellin (fromLog f)) (closedStrip a b) := by sorry

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform restricts
to a Schwartz function on each vertical line of the closed strip. -/
theorem exists_schwartz_verticalTrace_mellin_of_weighted_schwartz (σ : ℝ) (hσ : σ ∈ Icc a b) :
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = verticalTrace (mellin (fromLog f)) σ := by sorry

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform is holomorphic
in the interior of the strip of Schwartz weights. -/
theorem differentiableOn_mellin_of_weighted_schwartz :
    DifferentiableOn ℂ (mellin (fromLog f)) (openStrip a b) := by sorry

/-- Paper: Proposition B.2.2.3(2), p. 601. The rapid decay bound holds
uniformly across the full closed strip, including the two boundary lines. -/
theorem mellin_eventualHeightBound_of_weighted_schwartz (N : ℕ) (hN : 1 ≤ N) :
    eventualHeightBound (mellin (fromLog f)) (Icc a b) N := by sorry

end UniformRiemannLebesgue

/-- Paper: Equation (B.2.2.4), p. 601. An upward vertical line integral uses
the parameter y ↦ σ + iy and its differential i dy. -/
def verticalLineIntegral (Φ : ℂ → ℂ) (σ : ℝ) : ℂ :=
  Complex.I * ∫ y : ℝ, Φ (verticalPoint σ y)

/-- Paper: Equation (B.2.2.4), p. 601. The normalized line integral is
the inverse Mellin integral evaluated at one.
Deviation: Sanity check for orientation and normalization. -/
theorem verticalLineIntegral_div_eq_mellinInv_one (Φ : ℂ → ℂ) (σ : ℝ)
    (hΦ : Complex.VerticalIntegrable Φ σ) :
    verticalLineIntegral Φ σ / (2 * (Real.pi : ℂ) * Complex.I) = mellinInv σ Φ 1 := by sorry

local notation "cauchyKernel" =>
  (fun (Φ : ℂ → ℂ) (N : ℕ) (z s : ℂ) ↦ Φ s / (s - z) ^ (N + 1))
local notation "normalizedCauchyIntegral" =>
  (fun (Φ : ℂ → ℂ) (N : ℕ) (σ : ℝ) (z : ℂ) ↦
    (Nat.factorial N : ℂ) / (2 * (Real.pi : ℂ) * Complex.I) *
      verticalLineIntegral (cauchyKernel Φ N z) σ)

section CauchyStrip

variable {Φ : ℂ → ℂ} {a b : ℝ} (hΦ : UniformlySchwartzOnStrip Φ a b)

include hΦ

/-- Paper: Theorem B.2.2.4(1), p. 602. The Cauchy kernel is absolutely
integrable on each interior line off the real part of the evaluation point. -/
theorem cauchyKernel_verticalIntegrable_on_strip (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) σ := by sorry

variable (ε : ℝ) (hε : 0 < ε) (hWidth : a + ε < b - ε) (N : ℕ) (z : ℂ)

include hε hWidth

/-- Paper: Theorem B.2.2.4(1), p. 601. The normalized right-line integral
minus the normalized left-line integral gives the derivative at a point between the lines. -/
theorem asymptoticCauchy_eq_iteratedDeriv (hz : z.re ∈ Ioo (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      iteratedDeriv N Φ z := by sorry

/-- Paper: Theorem B.2.2.4(1), p. 602. The two normalized line integrals
agree when the evaluation point is outside the closed strip they bound. -/
theorem asymptoticCauchy_eq_zero (hz : z.re ∉ Icc (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      0 := by sorry

end CauchyStrip

-- TODO(paper-gap): The finite rectangle preceding (B.2.2.10) needs
-- |T| > |Im(z)| for z to lie between the horizontal sides.
-- TODO(paper-gap): Theorem B.2.2.4(2), equations (B.2.2.6) and (B.2.2.7),
-- fail under the large-height condition of Definition B.2.2.1 alone.
-- The hypothesis does not bound the Hardy norm used in (B.2.2.12).

/-- Paper: Theorem B.2.2.4(2), p. 602. The vertical Cauchy integral on the
shifted half-plane boundary converges absolutely off the line.
Deviation: The two identities fail with the printed half-plane hypothesis. -/
theorem cauchyKernel_verticalIntegrable_on_leftHalfPlane
    {Φ : ℂ → ℂ} {b : ℝ} (hΦ : SchwartzOnLeftHalfPlane Φ b)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) (z : ℂ) (hz : z.re ≠ b - ε) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) (b - ε) := by sorry

-- TODO(paper-gap): Remark B.2.2.5 drops the inverse Mellin normalization
-- and does not justify extension by zero from the real-axis Fourier argument.
-- Its final global bound would force the entire function to vanish.

/-- Paper: Remark B.2.2.5, p. 603. The inverse Mellin integrand
on the imaginary axis is absolutely integrable for every positive input. -/
theorem verticalIntegrable_mellinInv_of_schwartzOnVerticalStrips {Φ : ℂ → ℂ}
    (hΦ : SchwartzOnVerticalStrips Φ) (t : ℝ) (ht : 0 < t) :
    Complex.VerticalIntegrable (fun s ↦ Φ s * (t : ℂ) ^ (-s)) 0 := by sorry

/-- Paper: Remark B.2.2.5, p. 603. The zero extension of the imaginary-axis
contour integral is smooth on the real line. -/
theorem contDiff_zeroExtension_mellinInv_of_schwartzOnVerticalStrips {Φ : ℂ → ℂ}
    (hΦ : SchwartzOnVerticalStrips Φ) :
    ContDiff ℝ ∞ ((Ioi (0 : ℝ)).indicator fun t ↦
      verticalLineIntegral (fun s ↦ Φ s * (t : ℂ) ^ (-s)) 0) := by sorry

section CauchySelectedHeights

variable {Φ : ℂ → ℂ} {a a' a'' b'' b' b : ℝ}
  (ha₁ : a < a'') (ha₂ : a'' < a') (hab : a' < b') (hb₁ : b' < b'') (hb₂ : b'' < b)
  (hΦ : DifferentiableOn ℂ Φ (openStrip a b))
  (hLeft : UniformlySchwartzOnStrip Φ a a') (hRight : UniformlySchwartzOnStrip Φ b' b)
  (T : ℤ → ℝ) (hMono : StrictMono T)
  (hInf : Tendsto (fun k : ℤ ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop)
  (hHeight : ∀ M : ℕ, 1 ≤ M → ∃ C > (0 : ℝ),
    ∀ᶠ k : ℤ in atAbsInfty, ∀ σ ∈ Icc a'' b'',
      ‖Φ (verticalPoint σ (T k))‖ ≤ C / |T k| ^ M)

include ha₁ ha₂ hab hb₁ hb₂ hΦ hLeft hRight hMono hInf hHeight

/-- Paper: Corollary B.2.2.6, p. 603. With the two edge bounds and the
selected horizontal heights, the vertical Cauchy kernel is absolutely integrable
on each interior line off the real part of the evaluation point. -/
theorem cauchyKernel_verticalIntegrable_of_selectedHeights (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) σ := by sorry

variable (ε : ℝ) (hε : 0 < ε) (hWidth : a + ε < b - ε) (N : ℕ) (z : ℂ)

include hε hWidth

/-- Paper: Corollary B.2.2.6, p. 603. Rapid decay near both edges and
along the selected horizontal lines gives the Cauchy derivative formula inside. -/
theorem asymptoticCauchy_eq_iteratedDeriv_of_selectedHeights (hz : z.re ∈ Ioo (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      iteratedDeriv N Φ z := by sorry

/-- Paper: Corollary B.2.2.6, p. 603. Under the same edge and height
conditions, the difference of the normalized integrals vanishes outside. -/
theorem asymptoticCauchy_eq_zero_of_selectedHeights (hz : z.re ∉ Icc (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      0 := by sorry

end CauchySelectedHeights

end RiemannMasullo
