module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannMasullo.ForMathlib.Analysis.MellinTransform
import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalCauchyIntegral

/-!
# Mellin transforms and asymptotic Cauchy integrals

Masullo, §B.2, pp. 591–604. A Schwartz–Bruhat function on the positive reals is
represented by its real-line Schwartz map in the coordinate `x = log t`.
Other functions on the positive reals are represented by functions on ℝ whose
values outside the positive reals are immaterial.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Asymptotics ContDiff ENNReal FourierTransform NNReal SchwartzMap Topology

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
        (∫ y : ℝ, ‖Φ (verticalPoint σ y)‖) ≤ C := by
  simp only [MemLeftHardy, zero_lt_one, true_and, ENNReal.ofReal_one,
    Complex.VerticalIntegrable]
  constructor
  · rintro ⟨hΦ, C, hC⟩
    refine ⟨hΦ, C, fun σ hσ ↦ ?_⟩
    have hLp := hC σ hσ
    have hInt : Integrable (verticalTrace Φ σ) :=
      memLp_one_iff_integrable.mp (memLp_iff.mpr (hLp.trans_lt ENNReal.coe_lt_top))
    refine ⟨hInt, ?_⟩
    rw [integral_norm_eq_lintegral_eNorm hInt.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_eNorm hInt.aestronglyMeasurable]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top hLp
  · rintro ⟨hΦ, C, hC⟩
    refine ⟨hΦ, C.toNNReal, fun σ hσ ↦ ?_⟩
    obtain ⟨hInt, hBound⟩ := hC σ hσ
    rw [eLpNorm_one_eq_lintegral_eNorm hInt.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm hInt, ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal hBound

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
      Involutive R := by
  let T := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (ContinuousLinearEquiv.neg ℝ (M := ℝ))
  have hT (f : 𝓢(ℝ, ℂ)) (x : ℝ) : T f x = f (-x) := rfl
  have hinv (f : 𝓢(ℝ, ℂ)) : T (T f) = f := by ext x; simp only [hT, neg_neg]
  exact ⟨ContinuousLinearEquiv.equivOfInverse T T hinv hinv, hT, hinv⟩

/-- Paper: Lemma B.2.1.4(2), p. 593. Exponential decay is invariant under
reflection of the logarithmic profile. -/
theorem exponentialDecay_iff_reflected (f g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g x = f (-x)) :
    ExponentialDecay g ↔ ExponentialDecay f := by sorry

/-- Paper: Lemma B.2.1.4(2), p. 593. Reflection interchanges forward
and backward semi-exponential decay. -/
theorem backwardSemiExponentialDecay_iff_forward_reflected
    (f g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g x = f (-x)) :
    BackwardSemiExponentialDecay g ↔ ForwardSemiExponentialDecay f := by
  have normEq (n : ℕ) (x : ℝ) : ‖iteratedDeriv n (g : ℝ → ℂ) x‖ = ‖iteratedDeriv n (f : ℝ → ℂ) (-x)‖ := by
    rw [show (g : ℝ → ℂ) = fun y ↦ f (-y) from funext hg, iteratedDeriv_comp_neg]
    simp [norm_pow]
  constructor
  · intro h j A hA
    obtain ⟨C, hC⟩ := (h j A hA).bound
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [tendsto_neg_atTop_atBot.eventually hC] with x hx
    simpa only [normEq, neg_neg, mul_neg, neg_mul] using hx
  · intro h j A hA
    obtain ⟨C, hC⟩ := (h j A hA).bound
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [tendsto_neg_atBot_atTop.eventually hC] with x hx
    rw [normEq]
    simpa only [neg_mul_neg] using hx

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

/-- The Mellin integral of a logarithmic profile after the substitution `t = exp x`. -/
private theorem mellin_logProfile_eq (g : ℝ → ℂ) (s : ℂ) :
    mellin (fromLog g) s = ∫ x : ℝ, Complex.exp (s * x) * g x := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

section UniformRiemannLebesgue

variable (f : 𝓢(ℝ, ℂ)) (a b : ℝ) (hab : a < b)
  (hWeighted : ∀ σ ∈ Icc a b, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight σ x * f x)

include hab hWeighted

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin integral converges
absolutely throughout the closed strip of Schwartz weights. -/
theorem mellinConvergent_on_strip_of_weighted_schwartz (s : ℂ) (hs : s ∈ closedStrip a b) :
    MellinConvergent (fromLog f) s := by
  obtain ⟨g, hg⟩ := hWeighted s.re hs
  apply mellinConvergent_of_integrable_logWeight
  exact (g.integrable (μ := volume)).congr (Eventually.of_forall hg)

/-- Paper: Proposition B.2.2.3(1), p. 601. The two endpoint weights give one
integrable majorant for every Mellin integrand in the closed strip. -/
private theorem mellin_logProfile_dominated :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ s ∈ closedStrip a b, ∀ x : ℝ,
      ‖Complex.exp (s * x) * f x‖ ≤ B x := by
  obtain ⟨g, hg⟩ := hWeighted a (left_mem_Icc.mpr hab.le)
  obtain ⟨h, hh⟩ := hWeighted b (right_mem_Icc.mpr hab.le)
  refine ⟨fun x ↦ ‖g x‖ + ‖h x‖, (g.integrable (μ := volume)).norm.add
    (h.integrable (μ := volume)).norm, ?_⟩
  intro s hs x
  have hnorm (r : ℝ) : ‖(Real.exp (r * x) : ℂ) * f x‖ = Real.exp (r * x) * ‖f x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖Complex.exp (s * x) * f x‖ ≤ _
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rcases le_total x 0 with hx | hx
  · apply le_add_of_le_of_nonneg _ (norm_nonneg _)
    rw [hg, hnorm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hs.1 hx))
      (norm_nonneg _)
  · apply le_add_of_nonneg_of_le (norm_nonneg _) _
    rw [hh, hnorm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.2 hx))
      (norm_nonneg _)


/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform is continuous
on the closed strip of Schwartz weights. -/
theorem continuousOn_mellin_of_weighted_schwartz :
    ContinuousOn (mellin (fromLog f)) (closedStrip a b) := by
  obtain ⟨B, hB, hbound⟩ := mellin_logProfile_dominated f a b hab hWeighted
  change ContinuousOn (fun s ↦ mellin (fromLog f) s) (closedStrip a b)
  simp_rw [mellin_logProfile_eq]
  apply continuousOn_of_dominated (bound := B)
  · intro s _
    exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      f.continuous).aestronglyMeasurable
  · exact fun s hs ↦ Eventually.of_forall (hbound s hs)
  · exact hB
  · filter_upwards with x
    exact ((Complex.continuous_exp.comp (continuous_id.mul_const (x : ℂ))).mul_const
      (f x)).continuousOn

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform restricts
to a Schwartz function on each vertical line of the closed strip. -/
theorem exists_schwartz_verticalTrace_mellin_of_weighted_schwartz (σ : ℝ) (hσ : σ ∈ Icc a b) :
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = verticalTrace (mellin (fromLog f)) σ := by
  obtain ⟨g, hg⟩ := hWeighted σ hσ
  let r := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv g
  let e := (LinearEquiv.smulOfNeZero ℝ ℝ (2 * Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (𝓕 r), ?_⟩
  funext y
  change (𝓕 r) ((2 * Real.pi)⁻¹ * y) = mellin (fun t ↦ f (Real.log t)) (σ + y * Complex.I)
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add, Real.log_exp,
    div_eq_inv_mul]
  apply congrArg (fun v : ℝ → ℂ ↦ 𝓕 v ((2 * Real.pi)⁻¹ * y))
  funext x
  change g (-x) = _
  simp only [hg, Complex.real_smul, mul_neg, neg_mul]

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform is holomorphic
in the interior of the strip of Schwartz weights. -/
theorem differentiableOn_mellin_of_weighted_schwartz :
    DifferentiableOn ℂ (mellin (fromLog f)) (openStrip a b) := by
  have hloc : LocallyIntegrableOn (fun t ↦ f (Real.log t)) (Ioi 0) volume :=
    (f.continuous.comp_continuousOn (Real.continuousOn_log.mono
      (fun x hx ↦ ne_of_gt hx))).locallyIntegrableOn measurableSet_Ioi
  have bound {c : ℝ} (hc : c ∈ Icc a b) {l : Filter ℝ} (hl : ∀ᶠ t in l, 0 < t) :
      (fun t ↦ f (Real.log t)) =O[l] (fun t : ℝ ↦ t ^ (-c)) := by
    obtain ⟨g, hg⟩ := hWeighted c hc
    apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g)
    filter_upwards [hl] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos ht _), Real.rpow_def_of_pos ht, mul_comm (Real.log t)]
    simpa only [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      using g.norm_le_seminorm ℂ (Real.log t)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  exact mellin_differentiableAt_of_isBigO_rpow hloc
    (bound (right_mem_Icc.mpr hab.le) (eventually_gt_atTop 0)) hs.2
    (bound (left_mem_Icc.mpr hab.le) self_mem_nhdsWithin) hs.1

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

/-- A continuous trace with inverse-square decay at both ends is integrable. -/
private theorem integrable_of_eventual_sq_decay {u : ℝ → ℂ} (hu : Continuous u) {C : ℝ} (hC : 0 < C)
    (h : ∀ᶠ y : ℝ in comap abs atTop, ‖u y‖ ≤ C / |y| ^ 2) : Integrable u := by
  apply hu.locallyIntegrable.integrable_of_isBigO_cocompact _
    (integrable_inv_one_add_sq.integrableAtFilter _)
  apply Asymptotics.IsBigO.of_bound (2 * C)
  have hf : comap (abs : ℝ → ℝ) atTop = cocompact ℝ := by
    rw [show (abs : ℝ → ℝ) = norm from funext fun x ↦ (Real.norm_eq_abs x).symm,
      comap_norm_atTop, Metric.cobounded_eq_cocompact]
  rw [← hf]
  have hlarge : ∀ᶠ y : ℝ in comap abs atTop, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [h, hlarge] with y hy hy'
  apply hy.trans
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, sq_abs]
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hy2)]

/-- Staying away from the real part of the pole gives a bounded Cauchy multiplier. -/
private theorem kernel_integrable_from_trace {Φ : ℂ → ℂ} {σ : ℝ} (h : Complex.VerticalIntegrable Φ σ)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (fun s ↦ Φ s / (s - z) ^ (N + 1)) σ := by
  let w (y : ℝ) := (σ : ℂ) + y * Complex.I
  have hw (y : ℝ) : w y - z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re (sub_eq_zero.mp h)
    exact hz (by simpa [w] using hr.symm)
  let K (y : ℝ) := ((w y - z) ^ (N + 1))⁻¹
  have hc : Continuous K := by
    apply Continuous.inv₀ _ fun y ↦ pow_ne_zero _ (hw y)
    dsimp [w]
    fun_prop
  have hbound (y : ℝ) : ‖K y‖ ≤ (|σ - z.re| ^ (N + 1))⁻¹ := by
    have hsep : |σ - z.re| ≤ ‖w y - z‖ := by simpa [w] using Complex.abs_re_le_norm (w y - z)
    rw [show ‖K y‖ = (‖w y - z‖ ^ (N + 1))⁻¹ by simp [K]]
    exact inv_anti₀ (pow_pos (abs_pos.mpr (sub_ne_zero.mpr hz.symm)) _)
      (pow_le_pow_left₀ (abs_nonneg _) hsep _)
  exact (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hbound)).congr
    (Eventually.of_forall fun y ↦ by simp [K, w, div_eq_inv_mul])

/-- Paper: Theorem B.2.2.4(1), p. 602. Every interior vertical trace is
absolutely integrable because it has inverse-square decay at large heights. -/
theorem UniformlySchwartzOnStrip.verticalIntegrable {Φ : ℂ → ℂ} {a b : ℝ} (hΦ : UniformlySchwartzOnStrip Φ a b)
    (σ : ℝ) (hσ : σ ∈ Ioo a b) : Complex.VerticalIntegrable Φ σ := by
  let δ := min (σ - a) (b - σ) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min (sub_pos.mpr hσ.1) (sub_pos.mpr hσ.2))
  have hleft : a + δ < σ := by dsimp [δ]; linarith [min_le_left (σ - a) (b - σ), hσ.1]
  have hright : σ < b - δ := by dsimp [δ]; linarith [min_le_right (σ - a) (b - σ), hσ.2]
  obtain ⟨C, hC, h⟩ := hΦ.2.2 δ hδ (hleft.trans hright) 2 (by norm_num)
  refine integrable_of_eventual_sq_decay ?_ hC ?_
  · apply hΦ.2.1.continuousOn.comp_continuous
    · fun_prop
    · intro y
      simpa using hσ
  · exact h.mono fun y hy ↦ hy σ ⟨hleft.le, hright.le⟩

section ContourShift

open scoped Interval

/-- The horizontal Cauchy integrals vanish when the numerator decays uniformly in height. -/
private theorem horizontalKernel_tendsto_zero {Φ : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d) {C : ℝ}
    (hd : ∀ᶠ y : ℝ in atAbsInfty, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y|) (N : ℕ) (z : ℂ) :
    Tendsto (fun y : ℝ ↦ ∫ x in c..d, Φ (verticalPoint x y) / (verticalPoint x y - z) ^ (N + 1))
      atAbsInfty (𝓝 0) := by
  have hy : Tendsto (abs : ℝ → ℝ) atAbsInfty atTop := tendsto_comap
  apply squeeze_zero_norm'
  · filter_upwards [hd, hy.eventually (eventually_ge_atTop (|z.im| + 1))] with y hφ hlarge
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have im := Complex.abs_im_le_norm (verticalPoint x y - z)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add] at im
    have hsep : 1 ≤ ‖verticalPoint x y - z‖ := by linarith [abs_sub_abs_le_abs_sub y z.im]
    rw [norm_div, norm_pow]
    exact (div_le_self (norm_nonneg _) (one_le_pow₀ hsep)).trans
      (hφ x (Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hx)))
  · simpa using ((tendsto_const_nhds (x := C)).div_atTop hy).mul_const |d - c|

/-- Cauchy–Goursat on expanding rectangles allows a vertical contour to be shifted
across a strip of holomorphy when its horizontal boundary integrals tend to zero. -/
private theorem verticalIntegral_eq_of_contour_shift {K : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable K c) (hd : Complex.VerticalIntegrable K d)
    (hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0)) :
    verticalLineIntegral K d = verticalLineIntegral K c := by
  have hrect (t : ℝ) :
      (∫ x in c..d, K (verticalPoint x (-t))) - (∫ x in c..d, K (verticalPoint x t)) +
      Complex.I • (∫ y in -t..t, K (verticalPoint d y)) -
      Complex.I • (∫ y in -t..t, K (verticalPoint c y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn K (⟨c, -t⟩ : ℂ) (⟨d, t⟩ : ℂ)
    apply hK.mono
    intro w hw
    simpa only [uIcc_of_le hcd] using hw.1
  have ht : Tendsto (fun t : ℝ ↦ t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    exact tendsto_abs_atTop_atTop
  have hn : Tendsto (fun t : ℝ ↦ -t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def] using tendsto_abs_atTop_atTop
  have hv (x : ℝ) (hi : Complex.VerticalIntegrable K x) :=
    intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
  have hlim := (((hh.comp hn).sub (hh.comp ht)).add ((hv d hd).const_smul Complex.I)).sub
    ((hv c hc).const_smul Complex.I)
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (hrect t).symm)
  simpa [verticalLineIntegral, sub_eq_zero] using heq

end ContourShift

section CauchyStrip

variable {Φ : ℂ → ℂ} {a b : ℝ} (hΦ : UniformlySchwartzOnStrip Φ a b)

include hΦ

/-- Paper: Theorem B.2.2.4(1), p. 602. The Cauchy kernel is absolutely
integrable on each interior line off the real part of the evaluation point. -/
theorem cauchyKernel_verticalIntegrable_on_strip (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) σ := by
  exact kernel_integrable_from_trace (hΦ.verticalIntegrable σ hσ) N z hz

variable (ε : ℝ) (hε : 0 < ε) (hWidth : a + ε < b - ε) (N : ℕ) (z : ℂ)

include hε hWidth

/-- Paper: Theorem B.2.2.4(1), p. 601. The normalized right-line integral
minus the normalized left-line integral gives the derivative at a point between the lines. -/
theorem asymptoticCauchy_eq_iteratedDeriv (hz : z.re ∈ Ioo (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      iteratedDeriv N Φ z := by
  let c := a + ε
  let d := b - ε
  have ha : a < c := by dsimp [c]; linarith
  have hb : d < b := by dsimp [d]; linarith
  have hc : c ∈ Ioo a b := ⟨ha, hWidth.trans hb⟩
  have hd : d ∈ Ioo a b := ⟨ha.trans hWidth, hb⟩
  let J (n : ℕ) (σ : ℝ) (w : ℂ) := normalizedCauchyIntegral Φ n σ w
  change J N d z - J N c z = iteratedDeriv N Φ z
  induction N generalizing z with
  | zero =>
    obtain ⟨C, hC, hdecay⟩ := hΦ.2.2 ε hε hWidth 1 le_rfl
    have hk (σ : ℝ) (hσ : σ ∈ Ioo a b) (hne : z.re ≠ σ) :
        Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) σ := by
      simpa using cauchyKernel_verticalIntegrable_on_strip hΦ σ hσ 0 z hne
    have h := verticalCauchyIntegral_sub_eq hΦ.2.1 ha hb hz hC.le
      (by simpa only [pow_one] using hdecay) (hk c hc hz.1.ne') (hk d hd hz.2.ne)
    simp only [J, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, iteratedDeriv_zero,
      verticalLineIntegral]
    rw [← mul_sub, ← mul_sub, h]
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  | succ n ih =>
    have hJ (σ : ℝ) (hσ : σ ∈ Ioo a b) (hne : z.re ≠ σ) :
        HasDerivAt (J n σ) (J (n + 1) σ z) z := by
      have h := hasDerivAt_verticalCauchyIntegral hne (hΦ.verticalIntegrable σ hσ) n
        (cauchyKernel_verticalIntegrable_on_strip hΦ σ hσ n z hne)
      convert (h.const_mul Complex.I).const_mul ((n.factorial : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) using 1
      · rfl
      · simp only [J, verticalLineIntegral, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
    have heq : (fun w ↦ J n d w - J n c w) =ᶠ[𝓝 z] iteratedDeriv n Φ :=
      ((isOpen_Ioo.preimage Complex.continuous_re).eventually_mem hz).mono fun w hw ↦ ih w hw
    rw [iteratedDeriv_succ, ← heq.deriv_eq]
    exact ((hJ d hd hz.2.ne).sub (hJ c hc hz.1.ne')).deriv.symm

/-- Paper: Theorem B.2.2.4(1), p. 602. The two normalized line integrals
agree when the evaluation point is outside the closed strip they bound. -/
theorem asymptoticCauchy_eq_zero (hz : z.re ∉ Icc (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      0 := by
  let c := a + ε
  let d := b - ε
  have ha : a < c := by dsimp [c]; linarith
  have hb : d < b := by dsimp [d]; linarith
  have hcd : c < d := hWidth
  have hzc : z.re ≠ c := fun h ↦ hz (h ▸ left_mem_Icc.mpr hcd.le)
  have hzd : z.re ≠ d := fun h ↦ hz (h ▸ right_mem_Icc.mpr hcd.le)
  let K := cauchyKernel Φ N z
  have hdiff : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d) := by
    apply (hΦ.2.1.mono (preimage_mono (Icc_subset_Ioo ha hb))).div
      ((differentiable_id.sub_const z).pow _).differentiableOn
    intro w hw
    exact pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ hz (h ▸ hw))
  obtain ⟨C, _, hC⟩ := hΦ.2.2 ε hε hWidth 1 le_rfl
  have hh := horizontalKernel_tendsto_zero (Φ := Φ) hcd.le (C := C)
    (by simpa only [pow_one] using hC) N z
  have hv := verticalIntegral_eq_of_contour_shift hcd.le hdiff
    (cauchyKernel_verticalIntegrable_on_strip hΦ c ⟨ha, hcd.trans hb⟩ N z hzc)
    (cauchyKernel_verticalIntegrable_on_strip hΦ d ⟨ha.trans hcd, hb⟩ N z hzd) hh
  change _ * verticalLineIntegral K d - _ * verticalLineIntegral K c = 0
  rw [hv, sub_self]

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
    Complex.VerticalIntegrable (cauchyKernel Φ N z) (b - ε) := by
  apply kernel_integrable_from_trace _ N z hz
  obtain ⟨C, hC, h⟩ := hΦ.2 ε hε 2 (by norm_num)
  apply integrable_of_eventual_sq_decay _ hC
  · exact h.mono fun y hy ↦ hy (b - ε) le_rfl
  · apply hΦ.1.continuousOn.comp_continuous
    · fun_prop
    · intro y
      simpa using (sub_lt_self b hε)

-- TODO(paper-gap): Remark B.2.2.5 drops the inverse Mellin normalization
-- and does not justify extension by zero from the real-axis Fourier argument.
-- Its final global bound would force the entire function to vanish.

/-- Paper: Remark B.2.2.5, p. 603. The inverse Mellin integrand
on the imaginary axis is absolutely integrable for every positive input. -/
theorem verticalIntegrable_mellinInv_of_schwartzOnVerticalStrips {Φ : ℂ → ℂ}
    (hΦ : SchwartzOnVerticalStrips Φ) (t : ℝ) (ht : 0 < t) :
    Complex.VerticalIntegrable (fun s ↦ Φ s * (t : ℂ) ^ (-s)) 0 := by
  have h := (hΦ.2 (-1) 1 (by norm_num)).verticalIntegrable 0 (by constructor <;> norm_num)
  have hphase : Continuous (fun y : ℝ ↦ (t : ℂ) ^ (-(verticalPoint 0 y))) := by
    apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast ht.ne')
  have bound (y : ℝ) : ‖(t : ℂ) ^ (-(verticalPoint 0 y))‖ ≤ 1 := by
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  exact (h.bdd_mul hphase.aestronglyMeasurable (Eventually.of_forall bound)).congr
    (Eventually.of_forall fun y ↦ mul_comm _ _)

/-- Paper: Remark B.2.2.5, p. 603. The zero extension of the imaginary-axis
contour integral is smooth on the real line. -/
theorem contDiff_zeroExtension_mellinInv_of_schwartzOnVerticalStrips {Φ : ℂ → ℂ}
    (hΦ : SchwartzOnVerticalStrips Φ) :
    ContDiff ℝ ∞ ((Ioi (0 : ℝ)).indicator fun t ↦
      verticalLineIntegral (fun s ↦ Φ s * (t : ℂ) ^ (-s)) 0) := by sorry

/-- Apply the strip estimate to a compact interval of arbitrary placement. -/
private theorem closedSubstrip_decay {Φ : ℂ → ℂ} {a b c d : ℝ} (h : UniformlySchwartzOnStrip Φ a b)
    (ha : a < c) (hcd : c ≤ d) (hb : d < b) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in atAbsInfty, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y| ^ n := by
  let ε := min (c - a) (b - d) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))
  have hl : a + ε < c := by dsimp [ε]; linarith [min_le_left (c - a) (b - d)]
  have hr : d < b - ε := by dsimp [ε]; linarith [min_le_right (c - a) (b - d)]
  obtain ⟨C, hC, h'⟩ := h.2.2 ε hε (hl.trans (hcd.trans_lt hr)) n hn
  exact ⟨C, hC, h'.mono fun y hy x hx ↦ hy x ⟨hl.le.trans hx.1, hx.2.trans hr.le⟩⟩

/-- A polynomial weight absorbs the inverse powers of the imaginary part at large heights. -/
private theorem pow_mul_bound_of_heightBound {Φ : ℂ → ℂ} {c d C x y : ℝ} {n : ℕ}
    (hx : x ∈ Icc c d) (hy : 1 ≤ |y|) (h : ‖Φ (verticalPoint x y)‖ ≤ C / |y| ^ n) :
    ‖(verticalPoint x y) ^ n * Φ (verticalPoint x y)‖ ≤ (max |c| |d| + 1) ^ n * C := by
  let M := max |c| |d|
  have hM : 0 ≤ M := (abs_nonneg c).trans (le_max_left _ _)
  have hxM : |x| ≤ M := abs_le.mpr ⟨by linarith [hx.1, neg_abs_le c, le_max_left |c| |d|],
    by linarith [hx.2, le_abs_self d, le_max_right |c| |d|]⟩
  have hb : ‖verticalPoint x y‖ ≤ (M + 1) * |y| := by
    calc ‖verticalPoint x y‖ ≤ |x| + |y| := by simpa using norm_add_le (x : ℂ) ((y : ℂ) * Complex.I)
      _ ≤ (M + 1) * |y| := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hy)]
  rw [norm_mul, norm_pow]
  calc ‖verticalPoint x y‖ ^ n * ‖Φ (verticalPoint x y)‖ ≤ ((M + 1) * |y|) ^ n * (C / |y| ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb _) h (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; dsimp only [M]; field_simp [ne_of_gt (zero_lt_one.trans_le hy)]

/-- A continuous function bounded outside a bounded interval is bounded everywhere. -/
private theorem globally_bounded_of_height_bound {G : ℝ → ℂ} (hG : Continuous G) {C : ℝ}
    (h : ∀ᶠ y : ℝ in atAbsInfty, ‖G y‖ ≤ C) : ∃ D, ∀ y, ‖G y‖ ≤ D := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp h)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).bddAbove_image hG.norm.continuousOn
  refine ⟨max B C, fun y ↦ ?_⟩
  by_cases hy : R ≤ |y|
  · exact (hR |y| hy y rfl).trans (le_max_right _ _)
  · exact (hB (mem_image_of_mem _ (abs_le.mp (le_of_not_ge hy)))).trans (le_max_left _ _)

/-- Bounds along selected horizontal lines above and below each point propagate through the strip. -/
private theorem norm_le_of_selected_rectangles {F : ℂ → ℂ} {c d B : ℝ} (hcd : c < d)
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c d))
    (hedge : ∀ w : ℂ, w.re = c ∨ w.re = d → ‖F w‖ ≤ B)
    (T : ℤ → ℝ) (hMono : Monotone T)
    (hInf : Tendsto (fun k : ℤ ↦ |T k|) (comap abs atTop) atTop)
    (hT : ∀ᶠ k : ℤ in comap abs atTop, ∀ x ∈ Icc c d, ‖F (verticalPoint x (T k))‖ ≤ B)
    (z : ℂ) (hz : z.re ∈ Icc c d) : ‖F z‖ ≤ B := by
  have top : Tendsto (fun k : ℤ ↦ k) atTop (comap abs atTop) :=
    tendsto_comap_iff.mpr tendsto_abs_atTop_atTop
  have bot : Tendsto (fun k : ℤ ↦ k) atBot (comap abs atTop) :=
    tendsto_comap_iff.mpr tendsto_abs_atBot_atTop
  obtain ⟨u, hu, hTu⟩ : ∃ k, z.im < T k ∧ ∀ x ∈ Icc c d, ‖F (verticalPoint x (T k))‖ ≤ B := by
    have eventually := (hInf.comp top).eventually (eventually_gt_atTop (max z.im (-(T 0))))
    obtain ⟨k, hpos, hlarge, hhorizontal⟩ :=
      ((eventually_ge_atTop 0).and (eventually.and (top.eventually hT))).exists
    have h0 := hMono hpos
    refine ⟨k, ?_, hhorizontal⟩
    change max z.im (-(T 0)) < |T k| at hlarge
    rcases lt_abs.mp hlarge with h | h
    · exact (le_max_left _ _).trans_lt h
    · linarith [le_max_right z.im (-(T 0))]
  obtain ⟨l, hl, hTl⟩ : ∃ k, T k < z.im ∧ ∀ x ∈ Icc c d, ‖F (verticalPoint x (T k))‖ ≤ B := by
    have eventually := (hInf.comp bot).eventually (eventually_gt_atTop (max (-z.im) (T 0)))
    obtain ⟨k, hneg, hlarge, hhorizontal⟩ :=
      ((eventually_le_atBot 0).and (eventually.and (bot.eventually hT))).exists
    have h0 := hMono hneg
    refine ⟨k, ?_, hhorizontal⟩
    change max (-z.im) (T 0) < |T k| at hlarge
    rcases lt_abs.mp hlarge with h | h
    · linarith [le_max_right (-z.im) (T 0)]
    · linarith [le_max_left (-z.im) (T 0)]
  have hlu := hl.trans hu
  have cl := Complex.closure_reProdIm (Ioo c d) (Ioo (T l) (T u))
  rw [closure_Ioo hcd.ne, closure_Ioo hlu.ne] at cl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le ((Metric.isBounded_Ioo c d).reProdIm (Metric.isBounded_Ioo (T l) (T u)))
  · apply DifferentiableOn.diffContOnCl
    rw [cl]
    exact hF.mono fun w hw ↦ hw.1
  · intro w hw
    rw [Complex.frontier_reProdIm, frontier_Ioo hcd, frontier_Ioo hlu, closure_Ioo hcd.ne,
      closure_Ioo hlu.ne] at hw
    rcases hw with hw | hw
    · have him : w.im = T l ∨ w.im = T u := hw.2
      have hxy : verticalPoint w.re w.im = w := Complex.re_add_im w
      rcases him with him | him
      · rw [← hxy, him]
        exact hTl _ hw.1
      · rw [← hxy, him]
        exact hTu _ hw.1
    · exact hedge w hw.1
  · rw [cl]
    exact ⟨hz, hl.le, hu.le⟩

/-- Multiplication by a polynomial gives a globally bounded vertical trace. -/
private theorem weighted_trace_bound {Φ : ℂ → ℂ} {x C : ℝ} {n : ℕ}
    (hc : Continuous (fun y : ℝ ↦ Φ (verticalPoint x y)))
    (h : ∀ᶠ y : ℝ in atAbsInfty, ‖Φ (verticalPoint x y)‖ ≤ C / |y| ^ n) :
    ∃ B, ∀ y : ℝ, ‖(verticalPoint x y) ^ n * Φ (verticalPoint x y)‖ ≤ B := by
  apply globally_bounded_of_height_bound (Continuous.mul (by fun_prop) hc)
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [h, hy] with y hyφ hy'
  exact pow_mul_bound_of_heightBound (show x ∈ Icc x x from ⟨le_rfl, le_rfl⟩) hy' hyφ

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

/-- Paper: Corollary B.2.2.6, p. 603. Rapid decay along the chosen horizontal
lines and near both vertical edges implies uniform rapid decay on every closed substrip. -/
theorem uniformlySchwartzOnStrip_of_selectedHeights : UniformlySchwartzOnStrip Φ a b := by
  have hmid := ha₂.trans (hab.trans hb₁)
  refine ⟨ha₁.trans (hmid.trans hb₂), hΦ, ?_⟩
  intro ε hε _ n hn
  let l := min (a + ε) a''
  let r := max (b - ε) b''
  obtain ⟨L, hL, left⟩ := closedSubstrip_decay hLeft
    (show a < l from lt_min (by linarith) ha₁) (min_le_right _ _) ha₂ n hn
  obtain ⟨R, hR, right⟩ := closedSubstrip_decay hRight hb₁ (le_max_right _ _)
    (show r < b from max_lt (by linarith) hb₂) n hn
  let F (z : ℂ) := z ^ n * Φ z
  have hcont (x : ℝ) (hx : x ∈ Ioo a b) : Continuous (fun y : ℝ ↦ Φ (verticalPoint x y)) :=
    hΦ.continuousOn.comp_continuous (by fun_prop) fun y ↦ by simpa using hx
  obtain ⟨A, hA⟩ := weighted_trace_bound (hcont a'' ⟨ha₁, hmid.trans hb₂⟩)
    (left.mono fun y hy ↦ hy a'' ⟨min_le_right _ _, le_rfl⟩)
  obtain ⟨B, hB⟩ := weighted_trace_bound (hcont b'' ⟨ha₁.trans hmid, hb₂⟩)
    (right.mono fun y hy ↦ hy b'' ⟨le_rfl, le_max_right _ _⟩)
  obtain ⟨C, _, hC⟩ := hHeight n hn
  let H := (max |a''| |b''| + 1) ^ n * C
  let D := max (max A B) H
  have hbound (z : ℂ) (hz : z.re ∈ Icc a'' b'') : ‖F z‖ ≤ D := by
    apply norm_le_of_selected_rectangles hmid (F := F) _ _ T hMono.monotone hInf _ z hz
    · exact ((differentiable_id.pow n).differentiableOn.mul hΦ).mono (preimage_mono (Icc_subset_Ioo ha₁ hb₂))
    · intro w hw
      rw [← Complex.re_add_im w]
      rcases hw with hw | hw
      · rw [hw]
        exact (hA w.im).trans ((le_max_left A B).trans (le_max_left _ _))
      · rw [hw]
        exact (hB w.im).trans ((le_max_right A B).trans (le_max_left _ _))
    · filter_upwards [hC, hInf.eventually (eventually_ge_atTop 1)] with k hk hy x hx
      exact (pow_mul_bound_of_heightBound hx hy (hk x hx)).trans (le_max_right _ _)
  let M := max (max L R) D
  refine ⟨M, hL.trans_le ((le_max_left L R).trans (le_max_left _ _)), ?_⟩
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [left, right, hy] with y hly hry hy x hx
  by_cases hl : x ≤ a''
  · exact (hly x ⟨(min_le_left _ _).trans hx.1, hl⟩).trans
      (div_le_div_of_nonneg_right ((le_max_left L R).trans (le_max_left _ _)) (by positivity))
  by_cases hr : b'' ≤ x
  · exact (hry x ⟨hr, hx.2.trans (le_max_left _ _)⟩).trans
      (div_le_div_of_nonneg_right ((le_max_right L R).trans (le_max_left _ _)) (by positivity))
  have hz : (verticalPoint x y).re ∈ Icc a'' b'' := by simpa using And.intro (le_of_not_ge hl) (le_of_not_ge hr)
  have him : |y| ≤ ‖verticalPoint x y‖ := by simpa using Complex.abs_im_le_norm (verticalPoint x y)
  rw [le_div_iff₀ (pow_pos hy _), mul_comm]
  calc |y| ^ n * ‖Φ (verticalPoint x y)‖ ≤ ‖verticalPoint x y‖ ^ n * ‖Φ (verticalPoint x y)‖ := by gcongr
    _ = ‖F (verticalPoint x y)‖ := by simp only [F, norm_mul, norm_pow]
    _ ≤ M := (hbound _ hz).trans (le_max_right _ _)

/-- Paper: Corollary B.2.2.6, p. 603. With the two edge bounds and the
selected horizontal heights, the vertical Cauchy kernel is absolutely integrable
on each interior line off the real part of the evaluation point. -/
theorem cauchyKernel_verticalIntegrable_of_selectedHeights (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) σ := by
  exact cauchyKernel_verticalIntegrable_on_strip
    (uniformlySchwartzOnStrip_of_selectedHeights ha₁ ha₂ hab hb₁ hb₂ hΦ hLeft hRight T hMono hInf hHeight)
    σ hσ N z hz

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
