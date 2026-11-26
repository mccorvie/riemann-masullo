module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Comparison and product identities for positive jump energies

The positive-part comparison and exact multiplier identity hold for an arbitrary positive
jump measure. For fractional Sobolev energies they give the two cancellations needed in
the cardinal-interpolant argument, without a lower bound on the distance between sites.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace RiemannMasullo

variable {X : Type*} [MeasurableSpace X]

/-- The local `L²` energy plus the squared differences against a positive jump measure. -/
def nonlocalEnergy (μ : Measure X) (ν : Measure (X × X)) (f : X → ℂ) : ℝ :=
  (∫ x, ‖f x‖ ^ 2 ∂μ) + (1 / 2 : ℝ) * ∫ p, ‖f p.1 - f p.2‖ ^ 2 ∂ν

/-- The real bilinear form associated with a positive jump energy. -/
def realNonlocalPairing (μ : Measure X) (ν : Measure (X × X)) (f g : X → ℝ) : ℝ :=
  (∫ x, f x * g x ∂μ) + (1 / 2 : ℝ) * ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂ν

private theorem posPart_difference_sq_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (a - b) * (max a 0 - max b 0) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_right ha, max_eq_right hb]
  · rw [max_eq_right ha, max_eq_left hb]
    nlinarith
  · rw [max_eq_left ha, max_eq_right hb]
    nlinarith
  · rw [max_eq_left ha, max_eq_left hb]
    ring_nf
    exact le_rfl

/-- Orthogonality to the positive part forces a finite-energy function to be nonpositive.
This is the comparison argument for cardinal interpolants in a fractional Sobolev space. -/
theorem ae_nonpos_of_realNonlocalPairing_posPart_eq_zero
    (μ : Measure X) (ν : Measure (X × X)) {u : X → ℝ} (hm : Measurable u)
    (hu : MemLp u 2 μ) (hdu : MemLp (fun p : X × X ↦ u p.1 - u p.2) 2 ν)
    (horth : realNonlocalPairing μ ν u (fun x ↦ max (u x) 0) = 0) :
    ∀ᵐ x ∂μ, u x ≤ 0 := by
  let v (x : X) := max (u x) 0
  have hv : MemLp v 2 μ := by
    apply hu.norm.mono' (hm.max measurable_const).aestronglyMeasurable
    exact .of_forall fun x ↦ by
      dsimp [v]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hdv : MemLp (fun p : X × X ↦ v p.1 - v p.2) 2 ν := by
    apply hdu.norm.mono' (by dsimp [v]; fun_prop)
    exact .of_forall fun p ↦ by
      simpa only [v, Real.norm_eq_abs] using abs_max_sub_max_le_abs (u p.1) (u p.2) 0
  have hv2 : Integrable (fun x ↦ v x ^ 2) μ := by
    simpa only [pow_two, Pi.mul_def] using hv.integrable_mul hv
  have hdv2 : Integrable (fun p : X × X ↦ (v p.1 - v p.2) ^ 2) ν := by
    simpa only [pow_two, Pi.mul_def] using hdv.integrable_mul hdv
  have hc : Integrable (fun p : X × X ↦ (u p.1 - u p.2) * (v p.1 - v p.2)) ν :=
    hdu.integrable_mul hdv
  have hp : (∫ x, u x * v x ∂μ) = ∫ x, v x ^ 2 ∂μ := by
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    rcases le_total (u x) 0 with hx | hx <;> simp [v, max_eq_right hx, max_eq_left hx, pow_two]
  have hle : (∫ p, (v p.1 - v p.2) ^ 2 ∂ν) ≤
      ∫ p, (u p.1 - u p.2) * (v p.1 - v p.2) ∂ν :=
    integral_mono hdv2 hc (fun p ↦ posPart_difference_sq_le (u p.1) (u p.2))
  have hn : 0 ≤ ∫ p, (v p.1 - v p.2) ^ 2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  have he : (∫ x, v x ^ 2 ∂μ) = 0 := by
    change (∫ x, u x * v x ∂μ) + 1 / 2 *
      (∫ p, (u p.1 - u p.2) * (v p.1 - v p.2) ∂ν) = 0 at horth
    rw [hp] at horth
    have hn' : 0 ≤ ∫ x, v x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
    linarith
  have hae : ∀ᵐ x ∂μ, v x ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (.of_forall fun _ ↦ sq_nonneg _) hv2).mp he
  filter_upwards [hae] with x hx
  have hvx : v x = 0 := (sq_eq_zero_iff).mp hx
  exact (le_max_left (u x) 0).trans_eq hvx

private theorem nonlocal_product_difference (a c : ℝ) (b d : ℂ) :
    ‖(a : ℂ) * b - (c : ℂ) * d‖ ^ 2 =
      (a - c) * (‖b‖ ^ 2 * a - ‖d‖ ^ 2 * c) + a * c * ‖b - d‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

/-- The exact nonlocal product identity. When the pairing term vanishes by interpolation,
only the squared difference of the multiplier remains; no derivative of the interpolant
or separation between interpolation sites enters the formula. -/
theorem nonlocalEnergy_mul_eq (μ : Measure X) (ν : Measure (X × X))
    (h : X → ℝ) (b : X → ℂ)
    (hjump : Integrable (fun p : X × X ↦ ‖(h p.1 : ℂ) * b p.1 - (h p.2 : ℂ) * b p.2‖ ^ 2) ν)
    (hpair : Integrable (fun p : X × X ↦ (h p.1 - h p.2) *
      (‖b p.1‖ ^ 2 * h p.1 - ‖b p.2‖ ^ 2 * h p.2)) ν) :
    nonlocalEnergy μ ν (fun x ↦ (h x : ℂ) * b x) =
      realNonlocalPairing μ ν h (fun x ↦ ‖b x‖ ^ 2 * h x) +
        (1 / 2 : ℝ) * ∫ p, h p.1 * h p.2 * ‖b p.1 - b p.2‖ ^ 2 ∂ν := by
  have hi : Integrable (fun p : X × X ↦ h p.1 * h p.2 * ‖b p.1 - b p.2‖ ^ 2) ν := by
    apply (hjump.sub hpair).congr
    exact .of_forall fun p ↦ by
      dsimp
      rw [nonlocal_product_difference]
      ring
  have he : (∫ x, ‖(h x : ℂ) * b x‖ ^ 2 ∂μ) =
      ∫ x, h x * (‖b x‖ ^ 2 * h x) ∂μ := by
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  unfold nonlocalEnergy realNonlocalPairing
  simp_rw [nonlocal_product_difference]
  rw [he, integral_add hpair hi]
  ring


/-- The comparison inequality holds pointwise for a continuous representative. -/
theorem nonpos_of_realNonlocalPairing_posPart_eq_zero
    [TopologicalSpace X] [BorelSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (ν : Measure (X × X)) {u : X → ℝ} (hc : Continuous u)
    (hu : MemLp u 2 μ) (hdu : MemLp (fun p : X × X ↦ u p.1 - u p.2) 2 ν)
    (horth : realNonlocalPairing μ ν u (fun x ↦ max (u x) 0) = 0) (x : X) :
    u x ≤ 0 := by
  have hd := Measure.dense_of_ae (μ := μ)
    (ae_nonpos_of_realNonlocalPairing_posPart_eq_zero μ ν hc.measurable hu hdu horth)
  have hclosed : IsClosed {x : X | u x ≤ 0} := isClosed_le hc continuous_const
  have hall : {x : X | u x ≤ 0} = Set.univ := hclosed.closure_eq.symm.trans hd.closure_eq
  have hx : x ∈ {x : X | u x ≤ 0} := by rw [hall]; trivial
  exact hx

/-- Bilinearity in the first variable, with the finite-energy hypotheses that justify
subtracting the two local and jump integrals. -/
theorem realNonlocalPairing_sub_left (μ : Measure X) (ν : Measure (X × X))
    {f g v : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hv : MemLp v 2 μ)
    (hdf : MemLp (fun p : X × X ↦ f p.1 - f p.2) 2 ν)
    (hdg : MemLp (fun p : X × X ↦ g p.1 - g p.2) 2 ν)
    (hdv : MemLp (fun p : X × X ↦ v p.1 - v p.2) 2 ν) :
    realNonlocalPairing μ ν (fun x ↦ f x - g x) v =
      realNonlocalPairing μ ν f v - realNonlocalPairing μ ν g v := by
  have he (p : X × X) : ((f p.1 - g p.1) - (f p.2 - g p.2)) * (v p.1 - v p.2) =
      (f p.1 - f p.2) * (v p.1 - v p.2) - (g p.1 - g p.2) * (v p.1 - v p.2) := by ring
  have hl (x : X) : (f x - g x) * v x = f x * v x - g x * v x := sub_mul _ _ _
  have hfv : Integrable (fun x ↦ f x * v x) μ := by simpa only [Pi.mul_def] using hf.integrable_mul hv
  have hgv : Integrable (fun x ↦ g x * v x) μ := by simpa only [Pi.mul_def] using hg.integrable_mul hv
  have hdfv : Integrable (fun p : X × X ↦ (f p.1 - f p.2) * (v p.1 - v p.2)) ν :=
    hdf.integrable_mul hdv
  have hdgv : Integrable (fun p : X × X ↦ (g p.1 - g p.2) * (v p.1 - v p.2)) ν :=
    hdg.integrable_mul hdv
  unfold realNonlocalPairing
  simp_rw [he, hl]
  rw [integral_sub hfv hgv, integral_sub hdfv hdgv]
  ring

end RiemannMasullo
