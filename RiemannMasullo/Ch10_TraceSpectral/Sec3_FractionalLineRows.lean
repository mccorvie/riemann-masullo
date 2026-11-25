module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_FractionalLineModel
public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalModelRows
public import RiemannMasullo.ForMathlib.Analysis.Calculus.MeanValueEnvelope
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Fractional residual estimates for the actual orthogonal quotient lift

The compact multiplier regularity calculation adapts PR #7537
(commit `ed4192ba9dee0d5e35f3942a4d71ec9c774f3edb`). The fractional cardinal estimate
and its unitary transport extend the geometric row bound to `1 < s < 2`.
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped InnerProductSpace NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.Isolated
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Ω" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "l𝔽" => logIdeleClassNorm F
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 l𝔽 (-0) 0 s

/-- The real-frequency Mellin multiplier of a compact test, with the paper's positive phase. -/
def fractionalLineMultiplier (η : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽) (t : ℝ) : ℂ :=
  ∫ g, φ.val g * spectralZeroJet η 0 t 0 g ∂μ𝔽

/-- The multiplier in the geometric criterion uses the project's positive unitary
norm twist, precisely at `it`. -/
theorem fractionalLineMultiplier_eq_twist (η : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽) (t : ℝ) :
    fractionalLineMultiplier η φ t = ∫ g, φ.val g * ideleClassNormTwist η ((t : ℂ) * Complex.I) g ∂μ𝔽 := by
  simp only [fractionalLineMultiplier, spectralZeroJet, Complex.ofReal_zero, zero_add, pow_zero, mul_one]

/-- The compact-test first log moment gives a uniform bound for the derivative, and
the zeroth moment bounds the function itself. The same two constants work for every
base character. -/
theorem fractionalLineMultiplier_regular (η : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽) :
    ContDiff ℝ 1 (fractionalLineMultiplier η φ) ∧
      (∀ t, ‖fractionalLineMultiplier η φ t‖ ≤ ∫ g, ‖φ.val g‖ ∂μ𝔽) ∧
      (∀ t, ‖deriv (fractionalLineMultiplier η φ) t‖ ≤ ∫ g, ‖φ.val g‖ * ‖l𝔽 g‖ ∂μ𝔽) := by
  let A (t : ℝ) (g : C𝔽) := (φ.val g * (η g : ℂ)) * Complex.exp (((t * l𝔽 g : ℝ) : ℂ) * Complex.I)
  let B (t : ℝ) (g : C𝔽) := A t g * ((l𝔽 g : ℂ) * Complex.I)
  let C (g : C𝔽) := ‖φ.val g‖ * ‖l𝔽 g‖
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hL : Continuous l𝔽 :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
      (fun g ↦ NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
  have hη : Continuous (fun g : C𝔽 ↦ (η g : ℂ)) := continuous_subtype_val.comp η.continuous
  have hA (t : ℝ) : Continuous (A t) := by dsimp [A]; fun_prop
  have hB (t : ℝ) : Continuous (B t) := by dsimp [B]; fun_prop
  have hC : Integrable C μ𝔽 :=
    (hφ.norm.mul hL.norm).integrable_of_hasCompactSupport
      ((show HasCompactSupport φ.val from φ.property.2).norm.mul_right)
  have hAabs (t : ℝ) (g : C𝔽) : ‖A t g‖ = ‖φ.val g‖ := by
    simp only [A, norm_mul, Circle.norm_coe, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hBabs (t : ℝ) (g : C𝔽) : ‖B t g‖ = C g := by
    simp only [B, C, norm_mul, hAabs, Complex.norm_real, Complex.norm_I, mul_one]
  have hAe (t : ℝ) : Integrable (A t) μ𝔽 :=
    (hA t).integrable_of_hasCompactSupport ((show HasCompactSupport φ.val from φ.property.2).mul_right.mul_right)
  have htransform : fractionalLineMultiplier η φ = fun t ↦ ∫ g, A t g ∂μ𝔽 := by
    funext t
    exact integral_congr_ae (.of_forall fun g ↦
      (congrArg (φ.val g * ·) (show spectralZeroJet η 0 t 0 g = _ by
        rw [spectralZeroJet_line_phase, Circle.coe_mul, Circle.coe_exp])).trans (mul_assoc _ _ _).symm)
  have hd (t : ℝ) : HasDerivAt (fractionalLineMultiplier η φ) (∫ g, B t g ∂μ𝔽) t := by
    rw [htransform]
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) univ_mem
      (.of_forall fun t ↦ (hA t).aestronglyMeasurable) (hAe t) (hB t).aestronglyMeasurable
      (.of_forall fun g t _ ↦ (hBabs t g).le) hC ?_).2
    refine .of_forall fun g u _ ↦ ?_
    have hd := (((hasDerivAt_id u).mul_const (l𝔽 g)).ofReal_comp.mul_const Complex.I).cexp
    convert hd.const_mul (φ.val g * (η g : ℂ)) using 1
    · simp [A]
    · simp [A, B]
      ring
  have hd' : deriv (fractionalLineMultiplier η φ) = fun t ↦ ∫ g, B t g ∂μ𝔽 := funext fun t ↦ (hd t).deriv
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun t ↦ (hd t).differentiableAt, ?_⟩, ?_, ?_⟩
  · rw [hd']
    exact continuous_of_dominated (fun t ↦ (hB t).aestronglyMeasurable)
      (fun t ↦ .of_forall fun g ↦ (hBabs t g).le) hC (.of_forall fun g ↦ by dsimp [B, A]; fun_prop)
  · intro t
    rw [htransform]
    exact (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall (hAabs t)))
  · intro t
    rw [hd']
    exact (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall (hBabs t)))


variable {s : ℝ} (hs : 1 < s) (hs₂ : s < 2) (a : ℝ)
local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "N" => globalThetaSobolev F a hI hs₀
local notation "Q" => spectralSobolevQuotient F a hI hs₀
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a 0 s
local notation "lift(" x ")" => ((N).quotientEquivOrthogonal (x)).val
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-0) 0 s hI hs₀ φ

include hs₂

/-- The actual orthogonal lift and its convolution residual satisfy the fractional
cardinal row estimate. The bound is independent of zero spacing and of the Tamagawa
normalization; the hypotheses on the symbol concern only its centered Mellin multiplier. -/
theorem fractionalLine_residual_row_sq_le
    (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (x : J(χ) → Q) (f : J(χ) → StrongDual ℂ Q)
    (hbasis : IsSpectralMarkushevichBasis x f)
    (hjets : ∀ j, spectralSobolevDualEmbedding F a hI hs₀ (f j) =
      (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀ j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (j : J(χ)) {A : ℝ} (hA : 0 ≤ A)
    {B L : NNReal}
    (hB : ∀ t, ‖fractionalLineMultiplier (χ j.val.1) φ t -
      fractionalLineMultiplier (χ j.val.1) φ j.val.2.2.1‖ ≤ B)
    (hL : LipschitzWith L (fun t ↦ fractionalLineMultiplier (χ j.val.1) φ t -
      fractionalLineMultiplier (χ j.val.1) φ j.val.2.2.1))
    (hlocal : ∀ u v, ‖fractionalLineMultiplier (χ j.val.1) φ u -
      fractionalLineMultiplier (χ j.val.1) φ v‖ ≤
        A * |u - v| * Real.exp ((|u - j.val.2.2.1| + |v - j.val.2.2.1|) / 8)) :
    (‖(f j).comp (N).mkQL‖ *
      ‖A(φ) (lift(x j)) - fractionalLineMultiplier (χ j.val.1) φ j.val.2.2.1 • lift(x j)‖) ^ 2 ≤
      ‖fractionalProbe (s / 2) (by linarith : 1 / 2 < s / 2) 0‖ ^ 2 *
        (8 * (s / 2) * ((2 : ℝ) ^ (s / 2 - 1 / 2)) ^ 2 * A ^ 2) := by
  obtain ⟨U, hU⟩ := exists_fractionalLineFourierEquiv hs χ hχ
  let w : W(s) := lift(x j)
  let lam := fractionalLineMultiplier (χ j.val.1) φ j.val.2.2.1
  let r : W(s) := A(φ) w - lam • w
  let E (ω : Ω) (t : ℝ) := fractionalLineWaveEval hs (χ ω) t
  let site (k : J(χ)) : Ω × ℝ := (k.val.1, k.val.2.2.1)
  have hcoords (k : J(χ)) : (f k).comp (N).mkQL = E (site k).1 (site k).2 :=
    fractionalLine_pulledCoordinate_eq_waveEval hs (by linarith) a χ k (f k) (hjets k)
  have hquot : (N).mkQL w = x j :=
    ((N).quotientEquivOrthogonal_symm_eq_mk w ((N).quotientEquivOrthogonal (x j)).property).symm.trans
      ((N).quotientEquivOrthogonal.symm_apply_apply (x j))
  have hobs (k : J(χ)) : E (site k).1 (site k).2 w = f k (x j) := by
    rw [← hcoords, ContinuousLinearMap.comp_apply, hquot]
  have horth : ∀ v : W(s), (∀ k, E (site k).1 (site k).2 v = 0) → ⟪w, v⟫_ℂ = 0 := by
    intro v hv
    have hq : (N).mkQL v = 0 := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
      have hall : ContinuousLinearMap.apply ℂ ℂ ((N).mkQL v) = ContinuousLinearMap.apply ℂ ℂ (0 : Q) := by
        apply ContinuousLinearMap.ext_on hbasis.2.2.2
        rintro _ ⟨k, rfl⟩
        change f k ((N).mkQL v) = f k 0
        rw [map_zero]
        exact (DFunLike.congr_fun (hcoords k) v).trans (hv k)
      exact fun ℓ ↦ DFunLike.congr_fun hall ℓ
    have hvN : v ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hq
    exact Submodule.inner_left_of_mem_orthogonal hvN ((N).quotientEquivOrthogonal (x j)).property
  have he := fractional_model_cardinal_row_sq_le
    (show 1 / 2 < s / 2 by linarith) (show s / 2 < 1 by linarith)
    (fractionalLineFourierScale_pos (F := F)) U E hU site j w r
    ((hobs j).trans (hbasis.1 j))
    (fun k hk ↦ (hobs k).trans (hbasis.2.1 j k hk.symm)) horth
    (fun ω t ↦ fractionalLineMultiplier (χ ω) φ t - lam)
    (fun ω t ↦ fractionalLineWaveEval_residual hs (χ ω) t φ lam w)
    hA hB hL (sub_self _)
    (fun u v ↦ by simpa only [sub_sub_sub_cancel_right] using hlocal u v)
  rw [hcoords j]
  exact he

/-- A polynomial envelope for the actual Mellin derivative gives a uniform residual
row bound at its center. The constant depends only on the Sobolev and polynomial orders. -/
theorem fractionalLine_residual_row_sq_le_of_deriv_envelope
    (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (x : J(χ) → Q) (f : J(χ) → StrongDual ℂ Q)
    (hbasis : IsSpectralMarkushevichBasis x f)
    (hjets : ∀ j, spectralSobolevDualEmbedding F a hI hs₀ (f j) =
      (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀ j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (j : J(χ)) {D : ℝ} (hD : 0 ≤ D) (n : ℕ)
    (hderiv : ∀ t, ‖deriv (fractionalLineMultiplier (χ j.val.1) φ) t‖ ≤
      D * (1 + |t - j.val.2.2.1|) ^ n) :
    (‖(f j).comp (N).mkQL‖ *
      ‖A(φ) (lift(x j)) - fractionalLineMultiplier (χ j.val.1) φ j.val.2.2.1 • lift(x j)‖) ^ 2 ≤
      ‖fractionalProbe (s / 2) (by linarith : 1 / 2 < s / 2) 0‖ ^ 2 *
        (8 * (s / 2) * ((2 : ℝ) ^ (s / 2 - 1 / 2)) ^ 2 * (D * ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8))) ^ 2) := by
  obtain ⟨hm, hbound, hderivBound⟩ := fractionalLineMultiplier_regular (χ j.val.1) φ
  let B : NNReal := ⟨2 * ∫ g, ‖φ.val g‖ ∂μ𝔽, by positivity⟩
  let L : NNReal := ⟨∫ g, ‖φ.val g‖ * ‖l𝔽 g‖ ∂μ𝔽, integral_nonneg fun _ ↦ by positivity⟩
  have hLip : LipschitzWith L (fractionalLineMultiplier (χ j.val.1) φ) :=
    lipschitzWith_of_nnNorm_deriv_le hm.differentiable_one
      (fun t ↦ by exact_mod_cast hderivBound t)
  have hcenter : LipschitzWith L (fun t ↦ fractionalLineMultiplier (χ j.val.1) φ t -
      fractionalLineMultiplier (χ j.val.1) φ j.val.2.2.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hLip.norm_sub_le u v
  refine fractionalLine_residual_row_sq_le hs hs₂ a χ hχ x f hbasis hjets φ j
    (by positivity) (B := B) (L := L) ?_ hcenter ?_
  · intro t
    exact (norm_sub_le _ _).trans
      ((add_le_add (hbound t) (hbound j.val.2.2.1)).trans_eq (two_mul _).symm)
  · exact norm_sub_le_local_exp_of_deriv_polynomial_envelope hm.differentiable_one hD n hderiv

end RiemannMasullo.Isolated
