module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandRankOne
public import RiemannMasullo.AppC_LCTVS.Sec3a_RankOneCompression

/-! # The trace over the weighted band tends to `V_∞ - L₋` for every bandwidth

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

This file works in the Paley–Wiener picture of the weighted band described in
`Sec4_WeightedBandKernel`: the weight is `x ^ 2 + x ^ (-2)`, the weighted band is the space
`weightedPWBand Y` of the odd functions of the band `[-Y, Y]` that vanish at
`ζ = e ^ (i π / 4)`, and the dilation is `weightedPWDilation g`, the unitary dilation `D_g`
followed by the multiplication by `r_g x = g (x ^ 2 - i) / (x ^ 2 - i g ^ 2)`.

* `isNuclearOperator_weightedPWBand_compression`: with `P` the orthogonal projection onto the
  weighted band and `M_L` the sharp spatial cutoff, `P ∘ M_L ∘ R_g ∘ P` is nuclear.
* `hilbertTrace_weightedPWBand_compression_eq`: its Hilbert trace is the diagonal integral over
  the odd band minus `⟪k, M_L R_g k⟫ / ‖k‖ ^ 2`, with `k` the reproducing vector of the odd band
  at `ζ`.
* `tendsto_hilbertTrace_weightedPWBand_compression`: **the traces tend to
  `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2)` as `L → ∞`, at every fixed `Y > 0` and `g > 1`.** The
  two parts have limits `V_∞ - L₋ + E (Y)` and `E (Y)` with the same `E (Y)`
  (`Sec4_WeightedBandDiagonal`, `Sec4_WeightedBandRankOne`), so the limit has no remainder in
  the bandwidth. For the unweighted level the same limit needs `Y L → ∞`
  (`tendsto_hilbertTrace_realPWLevel_compression_eq`).

**Not formalized here.** The identification of this picture with the weighted space is in
`Sec4_WeightedBandBridge`. A single dilation `g > 1` is treated: no average against a test
function.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- The weighted band in its Paley–Wiener picture: the odd functions of the band `[-Y, Y]` that
vanish at `ζ = e ^ (i π / 4)`, that is, the odd band less the line of its reproducing vector at
`ζ`. -/
def weightedPWBand (Y : ℝ) : Submodule ℂ H :=
  realOddBand Y ⊓ (ℂ ∙ weightedKernelVector Y)ᗮ

/-- Membership in the weighted band: an odd function of the band whose pairing with the
reproducing vector at `ζ` vanishes. -/
theorem mem_weightedPWBand_iff {Y : ℝ} {F : H} :
    F ∈ weightedPWBand Y ↔ F ∈ realOddBand Y ∧ ⟪weightedKernelVector Y, F⟫_ℂ = 0 := by
  rw [weightedPWBand, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- The weighted band is closed. -/
theorem isClosed_weightedPWBand (Y : ℝ) : IsClosed (weightedPWBand Y : Set H) :=
  (isClosed_realOddBand Y).inter (Submodule.isClosed_orthogonal _)

/-- The weighted band is complete. -/
instance instCompleteSpaceWeightedPWBand (Y : ℝ) : CompleteSpace (weightedPWBand Y) :=
  (isClosed_weightedPWBand Y).completeSpace_coe

/-- The dilation of the weighted band in its Paley–Wiener picture: the unitary dilation `D_g`
followed by the multiplication by `r_g`. -/
def weightedPWDilation (g : ℝ) : H →L[ℂ] H :=
  realMultiplier (weightedDilationMultiplier g) ∘L realDilation g

/-- The dilation of the weighted band, applied to a vector. -/
theorem coeFn_weightedPWDilation {g : ℝ} (hg : 1 ≤ g) (f : H) :
    (weightedPWDilation g f : ℝ → ℂ) =ᵐ[volume] fun x ↦
      weightedDilationMultiplier g x * (realDilation g f : H) x :=
  coeFn_realMultiplier (continuous_weightedDilationMultiplier (by linarith)).measurable
    (norm_weightedDilationMultiplier_le hg) (realDilation g f)

/-- The compression of the cutoff dilation to the weighted band is nuclear, and its trace is
the trace of the compression to the odd band minus the rank-one term. -/
private theorem hilbertTrace_weightedPWBand_compression_aux {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (L : ℝ) :
    ∃ hn : IsNuclearOperator ((weightedPWBand Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection),
      hilbertTrace ⟨_, hn⟩ =
        hilbertTrace ⟨(realOddBand Y).starProjection ∘L realCutoff L ∘L
          realMultiplier (weightedDilationMultiplier g) ∘L realDilation g ∘L
          (realOddBand Y).starProjection,
          isNuclearOperator_realOddBand_compression hY (by linarith) L
            (continuous_weightedDilationMultiplier (by linarith)).measurable
            (norm_weightedDilationMultiplier_le hg.le)⟩ -
        ⟪weightedKernelVector Y, realCutoff L (weightedPWDilation g (weightedKernelVector Y))⟫_ℂ /
          (‖weightedKernelVector Y‖ : ℂ) ^ 2 := by
  have hg0 : 0 < g := by linarith
  have hr := (continuous_weightedDilationMultiplier hg0.ne').measurable
  have hC := norm_weightedDilationMultiplier_le hg.le
  have hodd := isNuclearOperator_realOddBand_compression hY hg0 L hr hC
  have hk := weightedKernelVector_mem Y
  have hk0 := weightedKernelVector_ne_zero hY
  have hcomp : (realOddBand Y).starProjection ∘L
      (realCutoff L ∘L weightedPWDilation g) ∘L (realOddBand Y).starProjection =
      (realOddBand Y).starProjection ∘L realCutoff L ∘L
        realMultiplier (weightedDilationMultiplier g) ∘L realDilation g ∘L
        (realOddBand Y).starProjection := rfl
  have hodd' : IsNuclearOperator ((realOddBand Y).starProjection ∘L
      (realCutoff L ∘L weightedPWDilation g) ∘L (realOddBand Y).starProjection) := hcomp ▸ hodd
  have hinst : (realOddBand Y ⊓ (ℂ ∙ weightedKernelVector Y)ᗮ).HasOrthogonalProjection :=
    inferInstanceAs (weightedPWBand Y).HasOrthogonalProjection
  have hmain := hilbertTrace_compression_inf_orthogonal_span_singleton hk hk0
    (realCutoff L ∘L weightedPWDilation g) hodd'
  obtain ⟨hn', htr'⟩ := hmain
  exact ⟨hn', htr'⟩

/-- The compression of the cutoff dilation to the weighted band, in its Paley–Wiener picture,
is nuclear. -/
theorem isNuclearOperator_weightedPWBand_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (L : ℝ) :
    IsNuclearOperator ((weightedPWBand Y).starProjection ∘L
      (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection) :=
  (hilbertTrace_weightedPWBand_compression_aux hY hg L).choose

/-- **The trace of the compression to the weighted band.** It is the diagonal integral over the
odd band minus the rank-one term of the reproducing vector at `ζ`. -/
theorem hilbertTrace_weightedPWBand_compression_eq {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g) {L : ℝ}
    (hL : 0 ≤ L) :
    hilbertTrace ⟨_, isNuclearOperator_weightedPWBand_compression hY hg L⟩ =
      (((√g)⁻¹ : ℝ) : ℂ) * (∫ z in (-L)..L,
        weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)) -
      ⟪weightedKernelVector Y, realCutoff L (weightedPWDilation g (weightedKernelVector Y))⟫_ℂ /
        (‖weightedKernelVector Y‖ : ℂ) ^ 2 := by
  refine (hilbertTrace_weightedPWBand_compression_aux hY hg L).choose_spec.trans ?_
  rw [hilbertTrace_realOddBand_compression_eq hY (by linarith) hL
    (continuous_weightedDilationMultiplier (by linarith)).measurable
    (norm_weightedDilationMultiplier_le hg.le)]

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520. **The trace over the
weighted band tends to `V_∞ - L₋`, for every bandwidth.** In the Paley–Wiener picture of the
weight `x ^ 2 + x ^ (-2)`, with `P` the orthogonal projection onto the weighted band, `M_L` the
sharp spatial cutoff and `R_g` the dilation, the Hilbert trace of `P ∘ M_L ∘ R_g ∘ P` tends to
`g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2)` as `L → ∞`, at every `Y > 0` and `g > 1`. The bandwidth
`Y` stays fixed: there is no remainder in `Y`.
Reconstruction: the rational real-place model at order zero with this weight. The trace over
the odd band has limit `V_∞ - L₋ + E (Y)` and the rank-one term has limit `E (Y)`, with the
same `E (Y) = weightedBandDefect Y g`. -/
theorem tendsto_hilbertTrace_weightedPWBand_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g) :
    Tendsto (fun L : ℝ ↦
        hilbertTrace ⟨_, isNuclearOperator_weightedPWBand_compression hY hg L⟩) atTop
      (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ))) := by
  have h1 := tendsto_integral_weightedDilationMultiplier_mul_realOddBandKernel hY hg
  have h2 := tendsto_inner_realCutoff (weightedKernelVector Y)
    (weightedPWDilation g (weightedKernelVector Y))
  have hk0 : (‖weightedKernelVector Y‖ : ℂ) ^ 2 ≠ 0 := by
    have : (‖weightedKernelVector Y‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr (weightedKernelVector_ne_zero hY)).ne'
    exact pow_ne_zero 2 this
  have hkk : ⟪weightedKernelVector Y, weightedKernelVector Y⟫_ℂ =
      (‖weightedKernelVector Y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  rw [inner_weightedKernelVector_multiplier_dilation hY.le hg
    (coeFn_weightedPWDilation hg.le _), hkk] at h2
  have h3 := h1.sub (h2.div_const ((‖weightedKernelVector Y‖ : ℂ) ^ 2))
  have h4 : Tendsto (fun L : ℝ ↦ (((√g)⁻¹ : ℝ) : ℂ) * (∫ z in (-L)..L,
        weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)) -
      ⟪weightedKernelVector Y, realCutoff L (weightedPWDilation g (weightedKernelVector Y))⟫_ℂ /
        (‖weightedKernelVector Y‖ : ℂ) ^ 2) atTop
      (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ))) := by
    convert h3 using 2
    rw [mul_div_assoc, div_self, mul_one, add_sub_cancel_right]
    exact hk0
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  exact (hilbertTrace_weightedPWBand_compression_eq hY hg hL).symm

end RiemannMasullo
