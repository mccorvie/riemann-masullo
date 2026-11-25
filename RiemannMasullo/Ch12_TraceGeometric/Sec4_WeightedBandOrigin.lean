module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandLevel
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! # The weighted band: the condition at the origin is automatic

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

`weightedBand Y` is defined as the space of the functions of the level `realPWLevel Y` with
finite weighted norm, for the weight `w x = x ^ 2 + x ^ (-2)`. The level asks for three things:
the Fourier transform vanishes outside `[-Y, Y]`, the function is even, and it vanishes at the
origin. This file proves that for a function of finite weighted norm the third condition
follows from the first two, so the weighted band is the space of the even band-limited
functions of finite weighted norm.

* `not_memLp_inv_mul_of_norm_eq_one`: `1 / x` times a function of modulus one is not
  square-integrable.
* `mem_weightedBand_iff_even_bandLimited`: a vector of the weighted space is in the weighted
  band exactly when it is band-limited and even.

The reason is the division formula `bandLaplace_bandPrimitive` at the origin: for a function
`F` of the band, `F (x) / x` differs from a function of the band by
`F (0) e ^ (-2 π i x Y) / x`. The weight makes `F (x) / x` square-integrable, and `1 / x` is
not, so `F (0) = 0`.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "Hw" => Lp ℂ 2 weightedBandMeasure

/-- `1 / x` times a function of modulus one is not square-integrable on the line. -/
theorem not_memLp_inv_mul_of_norm_eq_one {u : ℝ → ℂ} (hu : ∀ x, ‖u x‖ = 1) :
    ¬ MemLp (fun x : ℝ ↦ (x : ℂ)⁻¹ * u x) 2 volume := by
  intro h
  have h2 := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  have h3 : Integrable fun x : ℝ ↦ (x ^ 2)⁻¹ := by
    refine h2.congr (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [norm_mul, hu, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs]
  have h4 : IntervalIntegrable (fun x : ℝ ↦ (x ^ 2)⁻¹) volume 0 1 := h3.intervalIntegrable
  refine not_intervalIntegrable_of_sub_inv_isBigO_punctured (c := 0) ?_ zero_ne_one
    left_mem_uIcc h4
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with x hx0 hx1
  have hx : x ≠ 0 := hx0
  have hlt : |x| < 1 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx1
    exact hx1
  have hpos : 0 < |x| := abs_pos.mpr hx
  rw [sub_zero, one_mul, norm_inv, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  refine inv_anti₀ (by positivity) ?_
  nlinarith

/-- **The weighted band is the space of the even band-limited functions of finite weighted
norm.** A vector of the weighted space is in `weightedBand Y` exactly when its Fourier transform
vanishes outside `[-Y, Y]` and it is even. Vanishing at the origin is automatic. -/
theorem mem_weightedBand_iff_even_bandLimited {Y : ℝ} {f : Hw} :
    f ∈ weightedBand Y ↔ weightedBandInclusion f ∈ realBandLimited Y ∧
      ∀ᵐ x, (f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) x := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hι := coeFn_weightedBandInclusion f
  have hιn := (Measure.measurePreserving_neg (volume : Measure ℝ)
    ).quasiMeasurePreserving.ae_eq_comp hι
  rw [mem_weightedBand_iff]
  constructor
  · intro hF
    obtain ⟨hout, heven, -⟩ := mem_realPWLevelFourier_iff.mp (mem_realPWLevel_iff.mp hF)
    refine ⟨mem_realBandLimited_iff.mpr hout, ?_⟩
    have heven' : ∀ᵐ ξ, ((𝓕 (weightedBandInclusion f) : H) : ℝ → ℂ) (-ξ) =
        1 * ((𝓕 (weightedBandInclusion f) : H) : ℝ → ℂ) ξ :=
      heven.mono fun ξ e ↦ by rw [e, one_mul]
    filter_upwards [fourier_parity_iff.mp heven', hι, hιn] with x e1 e2 e3
    have e3' : (weightedBandInclusion f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) (-x) := e3
    rw [← e3', e1, one_mul, e2]
  · rintro ⟨hband, hfeven⟩
    have hFeven : ∀ᵐ x, (weightedBandInclusion f : ℝ → ℂ) (-x) =
        1 * (weightedBandInclusion f : ℝ → ℂ) x := by
      filter_upwards [hfeven, hι, hιn] with x e1 e2 e3
      have e3' : (weightedBandInclusion f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) (-x) := e3
      rw [e3', e1, e2, one_mul]
    obtain ⟨b, hb1, hb2, hsupp, hbeven, hFb⟩ :=
      exists_band_data_of_parity (σ := 1) (by norm_num) (mem_realBandLimited_iff.mp hband)
        (fourier_parity_iff.mpr hFeven)
    have hFa : (weightedBandInclusion f : ℝ → ℂ) =ᵐ[volume] 𝓕 b := by
      have := fourier_ae_eq_fourier_toLp hb1 hb2
      rw [← hFb] at this
      exact this.symm
    have hB0 : bandLaplace b 0 = 0 := by
      by_contra hB
      -- `F (x) / x` is square-integrable because of the weight
      have hdiv : MemLp (fun x : ℝ ↦ 𝓕 b x / (x : ℂ)) 2 volume := by
        have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ 𝓕 b x / (x : ℂ)) volume := by
          simp_rw [div_eq_mul_inv]
          exact (aestronglyMeasurable_fourier_real hb1).mul
            Complex.measurable_ofReal.inv.aestronglyMeasurable
        refine (Lp.memLp (weightedBandUnitary f)).mono hmeas ?_
        filter_upwards [coeFn_weightedBandUnitary f, hι, hFa, ae_ne_zero_real] with x e1 e2 e3 hx
        have hw : (x ^ 2)⁻¹ ≤ ‖weightedBandFactor x‖ ^ 2 := by
          rw [norm_sq_weightedBandFactor hx, weightedBandWeight]
          have : 0 ≤ x ^ 2 := sq_nonneg x
          linarith
        have hle : |x|⁻¹ ≤ ‖weightedBandFactor x‖ := by
          refine le_of_sq_le_sq ?_ (norm_nonneg _)
          rw [inv_pow, sq_abs]
          exact hw
        rw [e1, ← e2, e3, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      -- the primitive at rate zero
      have hP1 := integrable_bandPrimitive hb1 hsupp 0
      have hP2 := memLp_bandPrimitive hb1 hsupp 0
      have hFP : MemLp (𝓕 (bandPrimitive Y b 0)) 2 volume :=
        (memLp_two_fourier_and_eLpNorm_eq hP1 hP2).1
      have hsub := hdiv.sub (hFP.const_mul (2 * π * Complex.I))
      have hbad : MemLp (fun x : ℝ ↦ (x : ℂ)⁻¹ *
          Complex.exp (2 * π * (-(Complex.I * (x : ℂ)) - 0) * Y)) 2 volume := by
        have h1 := hsub.const_mul (bandLaplace b 0)⁻¹
        refine (memLp_congr_ae ?_).mp h1
        filter_upwards [ae_ne_zero_real] with x hx
        have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
        have hs : -(Complex.I * (x : ℂ)) ≠ 0 :=
          neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero hxc)
        have e := bandLaplace_bandPrimitive hb1 hsupp (v := 0) (s := -(Complex.I * (x : ℂ))) hs
        rw [← fourier_eq_bandLaplace b x, ← fourier_eq_bandLaplace (bandPrimitive Y b 0) x] at e
        simp only [Pi.sub_apply]
        generalize Complex.exp (2 * π * (-(Complex.I * (x : ℂ)) - 0) * Y) = E at e ⊢
        have hI := Complex.I_ne_zero
        field_simp
        linear_combination e
      refine not_memLp_inv_mul_of_norm_eq_one (fun x ↦ ?_) hbad
      have : (2 * π * (-(Complex.I * (x : ℂ)) - 0) * Y : ℂ) =
          ((-(2 * π * x * Y) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [hFb]
    exact fourier_toLp_mem_realPWLevel hb2 hsupp (fun ξ ↦ by rw [hbeven, one_mul]) hB0

end RiemannMasullo
