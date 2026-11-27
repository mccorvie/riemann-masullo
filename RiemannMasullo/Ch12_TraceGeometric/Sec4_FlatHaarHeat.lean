module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatKernel
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatNuclearHeat
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Gaussian kernel in multiplicative Haar coordinates

The half-density factors transport the positive-ray integral kernel to logarithmic
Lebesgue measure, equivalently multiplicative Haar measure. Its integrated diagonal
is the genuine Hilbert trace at each positive heat variance.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- The continuous two-sided heat kernel after the unitary change of variables
`x = exp(s)`, including the half-density on both kernel variables. -/
def haarHeatKernel (τ : ℝ≥0) (T : H →L[ℂ] H) (s t : ℝ) : ℂ :=
  ((Real.sqrt (Real.exp s) : ℝ) : ℂ) * ((Real.sqrt (Real.exp t) : ℝ) : ℂ) *
    heatSandwichKernel τ T (Real.exp s, Real.exp t)

/-- The log-coordinate kernel acts on each half-density representative of a
positive-ray L² vector by an absolutely convergent integral at every point. -/
theorem haarHeatKernel_integral {τ : ℝ≥0} (hτ : 0 < τ) (T : H →L[ℂ] H)
    (f : H) (s : ℝ) :
    let u (t : ℝ) := (Real.sqrt (Real.exp t) : ℂ) * f (Real.exp t)
    Integrable (fun t ↦ haarHeatKernel τ T s t * u t) ∧
      (∫ t, haarHeatKernel τ T s t * u t) =
        (Real.sqrt (Real.exp s) : ℂ) * heatRepresentative τ (T (logHeat τ f)) (Real.exp s) := by
  let g (x : ℝ) := heatSandwichKernel τ T (Real.exp s, x) * f x
  obtain ⟨hg, hrep⟩ := heatSandwichKernel_integral hτ T f (Real.exp_pos s)
  have hsub := (integrable_comp_exp g).mpr hg
  have he (t : ℝ) :
      haarHeatKernel τ T s t * ((Real.sqrt (Real.exp t) : ℂ) * f (Real.exp t)) =
        (Real.sqrt (Real.exp s) : ℂ) * (Real.exp t • g (Real.exp t)) := by
    have hs : (Real.sqrt (Real.exp t) : ℂ) * (Real.sqrt (Real.exp t) : ℂ) = (Real.exp t : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.exp_pos t).le]
    simp only [haarHeatKernel, g, Complex.real_smul]
    rw [← hs]
    ring
  dsimp only
  simp_rw [he]
  refine ⟨hsub.const_mul _, ?_⟩
  rw [integral_const_mul, integral_comp_exp g, hrep]

/-- For a nuclear input the canonical log-Haar diagonal is integrable and equals
the trace of the actual heat-sandwiched operator. -/
theorem haarHeatKernel_diagonal_trace {τ : ℝ≥0} (hτ : 0 < τ) (T : nuclearEndomorphisms H) :
    Integrable (fun s ↦ haarHeatKernel τ T.val s s) ∧
      (∫ s, haarHeatKernel τ T.val s s) = hilbertTrace (logHeatSandwich τ T) := by
  obtain ⟨_, _, _, hi, he⟩ := heatSandwichKernel_nuclearTrace hτ T
  let g (x : ℝ) := heatSandwichKernel τ T.val (x, x)
  have hd (s : ℝ) : haarHeatKernel τ T.val s s = Real.exp s • g (Real.exp s) := by
    simp only [haarHeatKernel, g, Complex.real_smul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Real.exp_pos s).le]
  simp_rw [hd]
  exact ⟨(integrable_comp_exp g).mpr hi, (integral_comp_exp g).trans he⟩

end RiemannMasullo.FlatPolar
