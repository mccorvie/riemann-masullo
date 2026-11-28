module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandSpace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandDivision

/-! # The weighted band of the rational real-place model and the limit of its traces

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

The weight is `w x = x ^ 2 + x ^ (-2)`. The weighted band `weightedBand Y`
(`Sec4_WeightedBandSpace`) is the space of the functions of the level `realPWLevel Y` of the
project that have finite weighted norm, inside `L²(ℝ, w dx)`. This file proves that
multiplication by `μ x = (x ^ 2 - i) / x` carries it onto the space `weightedPWBand Y` of the
odd functions of the band that vanish at `ζ = e ^ (i π / 4)`, and deduces the limit of the
traces on the weighted space from `Sec4_WeightedBandTrace`.

* `mem_realPWLevel_of_div_weightedBandFactor`: if `h` is an odd function of the band that
  vanishes at `ζ`, then `h / μ` is a function of the level. Since `h` also vanishes at `-ζ` and
  `1 / μ = (1 / (x - ζ) + 1 / (x + ζ)) / 2`, this is the division formula
  `bandLaplace_bandPrimitive` at the two points.
* `mem_weightedPWBand_of_weightedBandFactor_mul`: if `F` is a function of the level and `μ F`
  is square-integrable, then `μ F` is an odd function of the band that vanishes at `ζ`. Here
  `μ F = x F - i F / x`: the division formula at the origin handles `F / x`, and
  `mul_fourier_mem_realBandLimited` handles `x F`.
* `weightedBand_map_weightedBandUnitary`: hence the unitary carries the weighted band onto
  `weightedPWBand Y`.
* `tendsto_hilbertTrace_weightedBand_compression`: **on the weighted space, the Hilbert trace
  of `P ∘ M_L ∘ D_g ∘ P` tends to `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2)` as `L → ∞`, at every
  fixed `Y > 0` and `g > 1`.** Here `P` is the projection onto the weighted band, `M_L` the
  multiplication by `1_[-L, L]` and `D_g f (x) = g^(-1/2) f (x / g)`.

**Not formalized.** One weight, `x ^ 2 + x ^ (-2)`, which is not the logarithmic weight of the
paper. One dilation `g > 1` at a time, with no average against a test function. The sharp
cutoff. The rational field with no finite place.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "Hw" => Lp ℂ 2 weightedBandMeasure

/-! ### Preliminaries -/

/-- The two-sided Laplace transform commutes with multiplication by a constant. -/
theorem bandLaplace_const_mul (a : ℂ) (p : ℝ → ℂ) (s : ℂ) :
    bandLaplace (fun ξ ↦ a * p ξ) s = a * bandLaplace p s := by
  unfold bandLaplace
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  ring

/-- The two-sided Laplace transform is additive. -/
theorem bandLaplace_add {p q : ℝ → ℂ} {s : ℂ}
    (hp : Integrable fun ξ : ℝ ↦ p ξ * Complex.exp (2 * π * s * ξ))
    (hq : Integrable fun ξ : ℝ ↦ q ξ * Complex.exp (2 * π * s * ξ)) :
    bandLaplace (fun ξ ↦ p ξ + q ξ) s = bandLaplace p s + bandLaplace q s := by
  unfold bandLaplace
  rw [← integral_add hp hq]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  ring

/-- The two-sided Laplace transform at the origin is the integral. -/
theorem bandLaplace_zero (p : ℝ → ℂ) : bandLaplace p 0 = ∫ ξ, p ξ := by
  unfold bandLaplace
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp

/-- The factor `μ` is odd. -/
theorem weightedBandFactor_neg (x : ℝ) : weightedBandFactor (-x) = -weightedBandFactor x := by
  rw [weightedBandFactor, weightedBandFactor]
  push_cast
  rw [neg_sq, div_neg]

/-- A real number minus `ζ` is not zero. -/
theorem ofReal_sub_weightedZero_ne_zero (x : ℝ) : (x : ℂ) - weightedZero ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
  linarith [weightedZero_im_pos]

/-- A real number plus `ζ` is not zero. -/
theorem ofReal_add_weightedZero_ne_zero (x : ℝ) : (x : ℂ) + weightedZero ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im] at this
  linarith [weightedZero_im_pos]

/-- `(x - ζ) (x + ζ) = x ^ 2 - i`. -/
theorem ofReal_sub_mul_add_weightedZero (x : ℝ) :
    ((x : ℂ) - weightedZero) * ((x : ℂ) + weightedZero) = (x : ℂ) ^ 2 - Complex.I := by
  rw [← weightedZero_sq]
  ring

/-! ### From the Paley–Wiener picture to the level -/

/-- **Division by `μ`.** If `h` is an odd function of the band that vanishes at `ζ`, then
`h / μ` is a function of the level of the project: it is in the band, even, and vanishes at the
origin. -/
theorem mem_realPWLevel_of_div_weightedBandFactor {Y : ℝ} {h F : H} (hh : h ∈ weightedPWBand Y)
    (hF : ∀ᵐ x, (F : ℝ → ℂ) x = (h : ℝ → ℂ) x / weightedBandFactor x) : F ∈ realPWLevel Y := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨hodd, hk⟩ := mem_weightedPWBand_iff.mp hh
  obtain ⟨hout, hpar⟩ := mem_realOddBandFourier_iff.mp (mem_realOddBand_iff.mp hodd)
  have hpar' : ∀ᵐ ξ, ((𝓕 h : H) : ℝ → ℂ) (-ξ) = -1 * ((𝓕 h : H) : ℝ → ℂ) ξ :=
    hpar.mono fun ξ e ↦ by rw [e, neg_one_mul]
  obtain ⟨b, hb1, hb2, hsupp, hbodd, hhb⟩ :=
    exists_band_data_of_parity (σ := -1) (by norm_num) hout hpar'
  have hbodd' : ∀ ξ, b (-ξ) = -b ξ := fun ξ ↦ by rw [hbodd, neg_one_mul]
  have hha : (h : ℝ → ℂ) =ᵐ[volume] 𝓕 b := by
    have := fourier_ae_eq_fourier_toLp hb1 hb2
    rw [← hhb] at this
    exact this.symm
  have hhodd : ∀ᵐ x, (h : ℝ → ℂ) (-x) = -(h : ℝ → ℂ) x :=
    (fourier_parity_iff.mp hpar').mono fun x e ↦ by rw [e, neg_one_mul]
  have hB0 : bandLaplace b weightedRate = 0 := by
    have h1 := inner_weightedKernelVector_of_odd Y hhodd
    rw [hk, weightedEvalVector] at h1
    have h2 := inner_complexBandVector_fourier (Y := Y) (conj weightedRate) hb2 hsupp
    rw [← hhb, Complex.conj_conj] at h2
    rw [← h2]
    exact h1.symm
  have hBm : bandLaplace b (-weightedRate) = 0 := by
    rw [bandLaplace_neg_of_odd hbodd', hB0, neg_zero]
  have hBz : bandLaplace b 0 = 0 := by
    have h1 := bandLaplace_neg_of_odd hbodd' 0
    rw [neg_zero] at h1
    linear_combination (1 / 2 : ℂ) * h1
  have hu0 := weightedRate_ne_zero
  -- the frequency data of `h / μ`
  have hp1 := integrable_bandPrimitive hb1 hsupp weightedRate
  have hp2 := integrable_bandPrimitive hb1 hsupp (-weightedRate)
  have hs1 : ∀ ξ, ξ ∉ Icc (-Y) Y → bandPrimitive Y b weightedRate ξ = 0 :=
    fun ξ hξ ↦ bandPrimitive_of_notMem hξ
  have hs2 : ∀ ξ, ξ ∉ Icc (-Y) Y → bandPrimitive Y b (-weightedRate) ξ = 0 :=
    fun ξ hξ ↦ bandPrimitive_of_notMem hξ
  set c : ℝ → ℂ := fun ξ ↦ π * Complex.I *
    (bandPrimitive Y b weightedRate ξ + bandPrimitive Y b (-weightedRate) ξ) with hc
  have hc1 : Integrable c := (hp1.add hp2).const_mul _
  have hc2 : MemLp c 2 :=
    ((memLp_bandPrimitive hb1 hsupp weightedRate).add
      (memLp_bandPrimitive hb1 hsupp (-weightedRate))).const_mul _
  have hcsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0 := fun ξ hξ ↦ by
    rw [hc]
    dsimp only
    rw [hs1 ξ hξ, hs2 ξ hξ, add_zero, mul_zero]
  have hcL : ∀ s : ℂ, bandLaplace c s = π * Complex.I *
      (bandLaplace (bandPrimitive Y b weightedRate) s +
        bandLaplace (bandPrimitive Y b (-weightedRate)) s) := fun s ↦ by
    rw [hc, bandLaplace_const_mul, bandLaplace_add (integrable_mul_cexp_of_band hp1 hs1 s)
      (integrable_mul_cexp_of_band hp2 hs2 s)]
  have hpt : ∀ x : ℝ, x ≠ 0 → 𝓕 c x = 𝓕 b x / weightedBandFactor x := fun x hx ↦ by
    have hxm := ofReal_sub_weightedZero_ne_zero x
    have hxp := ofReal_add_weightedZero_ne_zero x
    have hne1 : -(Complex.I * (x : ℂ)) ≠ weightedRate := fun e ↦ by
      have := congrArg Complex.re e
      simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im] at this
      linarith [weightedRate_re_pos]
    have hne2 : -(Complex.I * (x : ℂ)) ≠ -weightedRate := fun e ↦ by
      have := congrArg Complex.re e
      simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im] at this
      linarith [weightedRate_re_pos]
    have e1 := bandLaplace_bandPrimitive hb1 hsupp hne1
    have e2 := bandLaplace_bandPrimitive hb1 hsupp hne2
    have hBs : bandLaplace b (-(Complex.I * (x : ℂ))) = 𝓕 b x := (fourier_eq_bandLaplace b x).symm
    have hwr : weightedRate = -Complex.I * weightedZero := rfl
    rw [hB0, mul_zero, zero_sub, hBs] at e1
    rw [hBm, mul_zero, zero_sub, hBs] at e2
    have e1' : bandLaplace (bandPrimitive Y b weightedRate) (-(Complex.I * (x : ℂ))) =
        𝓕 b x / (2 * π * Complex.I * ((x : ℂ) - weightedZero)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)
        hxm)]
      linear_combination (-1 : ℂ) * e1 - 2 * π *
        bandLaplace (bandPrimitive Y b weightedRate) (-(Complex.I * (x : ℂ))) * hwr
    have e2' : bandLaplace (bandPrimitive Y b (-weightedRate)) (-(Complex.I * (x : ℂ))) =
        𝓕 b x / (2 * π * Complex.I * ((x : ℂ) + weightedZero)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)
        hxp)]
      linear_combination (-1 : ℂ) * e2 + 2 * π *
        bandLaplace (bandPrimitive Y b (-weightedRate)) (-(Complex.I * (x : ℂ))) * hwr
    have hsum : π * Complex.I * (𝓕 b x / (2 * π * Complex.I * ((x : ℂ) - weightedZero)) +
        𝓕 b x / (2 * π * Complex.I * ((x : ℂ) + weightedZero))) =
        𝓕 b x * (x : ℂ) / (((x : ℂ) - weightedZero) * ((x : ℂ) + weightedZero)) := by
      have hI := Complex.I_ne_zero
      field_simp
      ring
    rw [fourier_eq_bandLaplace, hcL, e1', e2', hsum, ofReal_sub_mul_add_weightedZero,
      weightedBandFactor, div_div_eq_mul_div]
  have hFc : F = (𝓕 (hc2.toLp c) : H) := by
    refine Lp.ext ?_
    filter_upwards [hF, hha, fourier_ae_eq_fourier_toLp hc1 hc2, ae_ne_zero_real]
      with x e1 e2 e3 hx
    rw [e1, e2, ← e3, hpt x hx]
  have hco : ((𝓕 F : H) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ c (-ξ) := by
    rw [hFc]
    exact coeFn_fourier_fourier_toLp hc2
  have hmem : ∀ ξ : ℝ, -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := fun ξ ↦ by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [mem_realPWLevel_iff, mem_realPWLevelFourier_iff]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hco] with ξ e hξ
    rw [e, hcsupp _ (mt (hmem ξ).mp hξ)]
  · have hFeven : ∀ᵐ x, (F : ℝ → ℂ) (-x) = 1 * (F : ℝ → ℂ) x := by
      have hFn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hF
      filter_upwards [hF, hFn, hhodd] with x e1 e2 e3
      rw [e2, e3, weightedBandFactor_neg, neg_div_neg_eq, e1, one_mul]
    exact (fourier_parity_iff.mpr hFeven).mono fun ξ e ↦ by rw [e, one_mul]
  · rw [setIntegral_congr_ae measurableSet_Icc (hco.mono fun ξ e _ ↦ e),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun ξ hξ ↦ hcsupp _ (mt (hmem ξ).mp hξ)),
      integral_neg_eq_self c volume, ← bandLaplace_zero, hcL]
    have z1 := bandLaplace_bandPrimitive hb1 hsupp (v := weightedRate) (s := 0) (Ne.symm hu0)
    have z2 := bandLaplace_bandPrimitive hb1 hsupp (v := -weightedRate) (s := 0)
      (Ne.symm (neg_ne_zero.mpr hu0))
    rw [hB0, hBz, mul_zero, sub_zero] at z1
    rw [hBm, hBz, mul_zero, sub_zero] at z2
    have n1 : (2 : ℂ) * π * (0 - weightedRate) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hπ) (sub_ne_zero.mpr (Ne.symm hu0))
    have n2 : (2 : ℂ) * π * (0 - -weightedRate) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hπ)
        (sub_ne_zero.mpr (Ne.symm (neg_ne_zero.mpr hu0)))
    rw [(mul_eq_zero.mp z1).resolve_left n1, (mul_eq_zero.mp z2).resolve_left n2, add_zero,
      mul_zero]

/-! ### From the level to the Paley–Wiener picture -/

/-- **Multiplication by `μ`.** If `F` is a function of the level of the project and `μ F` is
square-integrable, with class `h`, then `h` is an odd function of the band that vanishes at
`ζ`. -/
theorem mem_weightedPWBand_of_weightedBandFactor_mul {Y : ℝ} {F h : H} (hF : F ∈ realPWLevel Y)
    (hh : ∀ᵐ x, (h : ℝ → ℂ) x = weightedBandFactor x * (F : ℝ → ℂ) x) :
    h ∈ weightedPWBand Y := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨hout, heven, hint⟩ := mem_realPWLevelFourier_iff.mp (mem_realPWLevel_iff.mp hF)
  have heven' : ∀ᵐ ξ, ((𝓕 F : H) : ℝ → ℂ) (-ξ) = 1 * ((𝓕 F : H) : ℝ → ℂ) ξ :=
    heven.mono fun ξ e ↦ by rw [e, one_mul]
  obtain ⟨b, hb1, hb2, hsupp, -, hFb⟩ :=
    exists_band_data_of_parity (σ := 1) (by norm_num) hout heven'
  have hFa : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 b := by
    have := fourier_ae_eq_fourier_toLp hb1 hb2
    rw [← hFb] at this
    exact this.symm
  have hFeven : ∀ᵐ x, (F : ℝ → ℂ) (-x) = (F : ℝ → ℂ) x :=
    (fourier_parity_iff.mp heven').mono fun x e ↦ by rw [e, one_mul]
  have hmem : ∀ ξ : ℝ, -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := fun ξ ↦ by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hBz : bandLaplace b 0 = 0 := by
    have hco : ((𝓕 F : H) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ b (-ξ) := by
      rw [hFb]
      exact coeFn_fourier_fourier_toLp hb2
    rw [bandLaplace_zero, ← integral_neg_eq_self b volume, ← hint,
      setIntegral_congr_ae measurableSet_Icc (hco.mono fun ξ e _ ↦ e),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun ξ hξ ↦ hsupp _ (mt (hmem ξ).mp hξ))]
  -- the frequency data of `F / x`
  have hs0 : ∀ ξ, ξ ∉ Icc (-Y) Y → bandPrimitive Y b 0 ξ = 0 :=
    fun ξ hξ ↦ bandPrimitive_of_notMem hξ
  obtain ⟨cu, hcu⟩ : ∃ cu : ℝ → ℂ, cu = fun ξ ↦ 2 * π * Complex.I * bandPrimitive Y b 0 ξ :=
    ⟨_, rfl⟩
  have hcu1 : Integrable cu := by
    rw [hcu]
    exact (integrable_bandPrimitive hb1 hsupp 0).const_mul _
  have hcu2 : MemLp cu 2 := by
    rw [hcu]
    exact (memLp_bandPrimitive hb1 hsupp 0).const_mul _
  have hcusupp : ∀ ξ, ξ ∉ Icc (-Y) Y → cu ξ = 0 := fun ξ hξ ↦ by
    rw [hcu]
    dsimp only
    rw [hs0 ξ hξ, mul_zero]
  have hcuL : ∀ s : ℂ, s ≠ 0 →
      s * bandLaplace cu s = -(Complex.I * bandLaplace b s) := fun s hs ↦ by
    have e := bandLaplace_bandPrimitive hb1 hsupp (v := 0) (s := s) hs
    rw [hBz, mul_zero, zero_sub, sub_zero] at e
    rw [hcu, bandLaplace_const_mul]
    linear_combination Complex.I * e
  have hupt : ∀ x : ℝ, x ≠ 0 → 𝓕 cu x = 𝓕 b x / (x : ℂ) := fun x hx ↦ by
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have e := hcuL (-(Complex.I * (x : ℂ)))
      (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero hxc))
    rw [← fourier_eq_bandLaplace cu x, ← fourier_eq_bandLaplace b x] at e
    rw [eq_div_iff hxc]
    refine mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    linear_combination e
  -- the class of `x F (x)`
  obtain ⟨G, hGdef⟩ : ∃ G : H, G = h + Complex.I • (𝓕 (hcu2.toLp cu) : H) := ⟨_, rfl⟩
  have hGa : (G : ℝ → ℂ) =ᵐ[volume] fun x ↦ (x : ℂ) * 𝓕 b x := by
    rw [hGdef]
    filter_upwards [Lp.coeFn_add h (Complex.I • (𝓕 (hcu2.toLp cu) : H)),
      Lp.coeFn_smul Complex.I (𝓕 (hcu2.toLp cu) : H), hh, hFa,
      fourier_ae_eq_fourier_toLp hcu1 hcu2, ae_ne_zero_real] with x e1 e2 e3 e4 e5 hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, e4, ← e5, hupt x hx, weightedBandFactor,
      smul_eq_mul]
    field_simp
    ring
  have hGmem := mul_fourier_mem_realBandLimited hb1 hb2 hsupp hGa
  have hGev := inner_complexBandVector_mul_fourier hb1 hb2 hsupp hGa
  have hhG : h = G - Complex.I • (𝓕 (hcu2.toLp cu) : H) := by
    rw [hGdef, add_sub_cancel_right]
  have hhband : h ∈ realBandLimited Y := by
    rw [hhG]
    exact Submodule.sub_mem _ hGmem
      (Submodule.smul_mem _ _ (fourier_toLp_mem_realBandLimited hcu2 hcusupp))
  have hhodd : ∀ᵐ x, (h : ℝ → ℂ) (-x) = -(h : ℝ → ℂ) x := by
    have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hh
    filter_upwards [hh, hn, hFeven] with x e1 e2 e3
    rw [e2, e3, weightedBandFactor_neg, neg_mul, e1]
  rw [mem_weightedPWBand_iff, mem_realOddBand_iff, mem_realOddBandFourier_iff]
  refine ⟨⟨mem_realBandLimited_iff.mp hhband, ?_⟩, ?_⟩
  · have hpar : ∀ᵐ x, (h : ℝ → ℂ) (-x) = -1 * (h : ℝ → ℂ) x :=
      hhodd.mono fun x e ↦ by rw [e, neg_one_mul]
    exact (fourier_parity_iff.mpr hpar).mono fun ξ e ↦ by rw [e, neg_one_mul]
  · rw [inner_weightedKernelVector_of_odd Y hhodd]
    obtain ⟨bh, hbh1, hbh2, hbhsupp, hhbh⟩ :=
      exists_band_data (mem_realBandLimited_iff.mp hhband)
    have hbig : ∀ ξ : ℝ, ξ ∉ Icc (-(Y + 1)) (Y + 1) → ξ ∉ Icc (-Y) Y :=
      fun ξ hξ h' ↦ hξ ⟨by linarith [h'.1], by linarith [h'.2]⟩
    have e1 : ⟪weightedEvalVector Y, h⟫_ℂ = bandLaplace bh weightedRate := by
      have h1 := inner_complexBandVector_fourier (Y := Y) (conj weightedRate) hbh2 hbhsupp
      rw [← hhbh, Complex.conj_conj] at h1
      exact h1
    have e2 : ⟪complexBandVector (Y + 1) (conj weightedRate), h⟫_ℂ =
        bandLaplace bh weightedRate := by
      have h1 := inner_complexBandVector_fourier (Y := Y + 1) (conj weightedRate) hbh2
        (fun ξ hξ ↦ hbhsupp ξ (hbig ξ hξ))
      rw [← hhbh, Complex.conj_conj] at h1
      exact h1
    have e3 : ⟪complexBandVector (Y + 1) (conj weightedRate), (𝓕 (hcu2.toLp cu) : H)⟫_ℂ =
        bandLaplace cu weightedRate := by
      have h1 := inner_complexBandVector_fourier (Y := Y + 1) (conj weightedRate) hcu2
        (fun ξ hξ ↦ hcusupp ξ (hbig ξ hξ))
      rw [Complex.conj_conj] at h1
      exact h1
    have e4 := hGev weightedRate
    have hu0 := weightedRate_ne_zero
    have e5 : bandLaplace cu weightedRate =
        -(Complex.I * bandLaplace b weightedRate) / weightedRate := by
      rw [eq_div_iff hu0, mul_comm]
      exact hcuL weightedRate hu0
    rw [e1, ← e2]
    conv_lhs => rw [hhG]
    rw [inner_sub_right, inner_smul_right, e4, e3, e5]
    have hfin : Complex.I * weightedRate * bandLaplace b weightedRate -
        Complex.I * (-(Complex.I * bandLaplace b weightedRate) / weightedRate) =
        bandLaplace b weightedRate / weightedRate *
          (Complex.I * weightedRate ^ 2 + Complex.I * Complex.I) := by
      field_simp
      ring
    rw [hfin, weightedRate_sq, mul_neg, Complex.I_mul_I, neg_neg, add_neg_cancel, mul_zero]

/-! ### The weighted band and the limit of the traces -/

/-- **The unitary carries the weighted band onto its Paley–Wiener picture.** Multiplication by
`μ` maps the functions of the level with finite weighted norm onto the odd functions of the
band that vanish at `ζ`. -/
theorem weightedBand_map_weightedBandUnitary (Y : ℝ) :
    (weightedBand Y).map weightedBandUnitary.toLinearIsometry.toLinearMap = weightedPWBand Y :=
  weightedBand_map_eq_of
    (fun _ _ hF hh ↦ mem_weightedPWBand_of_weightedBandFactor_mul hF hh)
    (fun _ _ hh hF ↦ mem_realPWLevel_of_div_weightedBandFactor hh hF)

/-- The compression of the cutoff dilation to the weighted band is nuclear. -/
theorem isNuclearOperator_weightedBand_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (L : ℝ) :
    IsNuclearOperator ((weightedBand Y).starProjection ∘L
      (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedBand Y).starProjection) :=
  (hilbertTrace_weightedBand_compression_of_map hY hg
    (weightedBand_map_weightedBandUnitary Y) L).choose

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520. **On the weighted
space the traces tend to `V_∞ - L₋` at every bandwidth.** Let `w x = x ^ 2 + x ^ (-2)`, let `P`
be the orthogonal projection of `L²(ℝ, w dx)` onto the functions of the level `realPWLevel Y`
with finite weighted norm, `M_L` the multiplication by `1_[-L, L]`, and `D_g` the dilation
`f ↦ g^(-1/2) f (x / g)`. Then `P ∘ M_L ∘ D_g ∘ P` is nuclear and its Hilbert trace tends to
`g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2)` as `L → ∞`, for every fixed `Y > 0` and every `g > 1`.
Reconstruction: the rational real-place model at order zero, with this weight in place of the
logarithmic weight of the paper, the sharp spatial cutoff, and a single dilation. In the
unweighted model the same limit requires `Y L → ∞`
(`tendsto_hilbertTrace_realPWLevel_compression_eq`). -/
theorem tendsto_hilbertTrace_weightedBand_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g) :
    Tendsto (fun L : ℝ ↦
        hilbertTrace ⟨_, isNuclearOperator_weightedBand_compression hY hg L⟩) atTop
      (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ))) := by
  obtain ⟨hn, h⟩ := tendsto_hilbertTrace_weightedBand_compression_of_map hY hg
    (weightedBand_map_weightedBandUnitary Y)
  exact h

end RiemannMasullo
