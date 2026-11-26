module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineGaps
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.GramMatrix
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic
import RiemannMasullo.Ch11_ShellStructure.Sec2a
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ModulatedBound
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5

/-! # The block series of Theorem 10.3.2.1(1): a sufficient majorant and a necessary separation

The recorded gap `spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241)
says that, after inserting any fixed compact operator, the traces of the zero blocks of the
spectral convolution are summable. This file proves it from one smaller statement, a summable
majorant built from the scalar Mellin transform of the test and the norms of the coordinate
functionals and their biorthogonal vectors, and shows what the gap forces: one constant must
bound the Mellin value at every zero times its zeroth jet, relative to the distance of that jet
from the zeroth jet at any other zero. The second statement is where the spacing of the zeros of
the Hecke `L`-functions enters. The majorant is equivalent to a uniform bound for finite
principal Gram matrices of the explicit jets. The remaining estimate is
`spectralStripConvolution_finiteGram_bound`. At width zero, that estimate for every test forces
the zeros of each component to be separated polynomially in the height
(`spectralStripConvolution_finiteGram_bound_forces_polynomial_gaps`). -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology SchwartzMap

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ z)

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

section Majorant

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. If the scalar Mellin bounds on the circles around
the zeros, multiplied by the sums of the products of the norms of the coordinate functionals and
their biorthogonal vectors at each zero, are summable, then the block traces are summable after
inserting any bounded operator, compact or not. -/
theorem spectralStripConvolution_block_series_of_summable_jetNorms
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (M : Z(χ, α) → ℝ) (hM : ∀ z, 0 ≤ M z)
    (hMellin : ∀ z : Z(χ, α), ∀ w ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2))
      (2 * Real.exp ((4 * α + s) / 2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M z)
    (hcoordinates : Summable (fun z : Z(χ, α) ↦ M z *
      ∑ m : Fin (N(χ, α, s, z)), ‖Λ (jet(z, m))‖ * ‖x (jet(z, m))‖))
    (U : Q(a, hStrip(hα), hs₀(hs)) →L[ℂ] Q(a, hStrip(hα), hs₀(hs))) :
    Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
      (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ (U (x (jet(z, m)))))) := by
  let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
  refine Summable.of_norm_bounded (hcoordinates.mul_left (4 * ‖U‖)) fun z ↦ ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ ↦ ?_
  have hjet := spectralStripConvolution_jet_norm_le_mellin_circle a hα hs χ Λ hj φ z m _ (hM z)
    (hMellin z)
  calc ‖Λ (jet(z, m)) (A (U (x (jet(z, m)))))‖
      = ‖((Λ (jet(z, m))).comp A) (U (x (jet(z, m))))‖ := rfl
    _ ≤ ‖(Λ (jet(z, m))).comp A‖ * (‖U‖ * ‖x (jet(z, m))‖) :=
      ((Λ (jet(z, m))).comp A).le_opNorm_of_le (U.le_opNorm _)
    _ ≤ (4 * M z * ‖Λ (jet(z, m))‖) * (‖U‖ * ‖x (jet(z, m))‖) :=
      mul_le_mul_of_nonneg_right hjet (by positivity)
    _ = 4 * ‖U‖ * (M z * (‖Λ (jet(z, m))‖ * ‖x (jet(z, m))‖)) := by ring

/-- Evaluation on a biorthogonal vector reads its coefficient on the dense span of the jets. -/
private theorem biorthogonal_norm_le_iff_coefficients {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : ι → E} {Λ : ι → StrongDual ℂ E}
    (hb : IsSpectralMarkushevichBasis x Λ) (i : ι) {K : ℝ} (hK : 0 ≤ K) :
    ‖x i‖ ≤ K ↔ ∀ c : ι →₀ ℂ, ‖c i‖ ≤ K * ‖Finsupp.linearCombination ℂ Λ c‖ := by
  classical
  let ev := NormedSpace.inclusionInDoubleDual ℂ E (x i)
  have hsingle : ev.toLinearMap ∘ Λ = Pi.single i (1 : ℂ) := by
    funext j
    change Λ j (x i) = _
    rcases eq_or_ne j i with rfl | hji
    · simp [hb.1]
    · rw [hb.2.1 i j hji.symm, Pi.single_eq_of_ne hji]
  have heval (c : ι →₀ ℂ) : (Finsupp.linearCombination ℂ Λ c) (x i) = c i := by
    change ev.toLinearMap (Finsupp.linearCombination ℂ Λ c) = _
    rw [Finsupp.apply_linearCombination, hsingle]
    simp
  constructor
  · intro h c
    rw [← heval c]
    exact ((Finsupp.linearCombination ℂ Λ c).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (mul_comm _ _))
  · intro h
    apply NormedSpace.norm_le_dual_bound ℂ (x i) hK
    intro f
    apply le_on_closure (s := (Submodule.span ℂ (Set.range Λ) : Set (StrongDual ℂ E)))
      (f := fun g : StrongDual ℂ E ↦ ‖g (x i)‖) (g := fun g ↦ K * ‖g‖) ?_
      ev.continuous.norm.continuousOn (continuous_const.mul continuous_norm).continuousOn
      (hb.2.2.2 f)
    intro g hg
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
    change ‖(Finsupp.linearCombination ℂ Λ c) (x i)‖ ≤ K * ‖Finsupp.linearCombination ℂ Λ c‖
    rw [heval]
    exact h c

private theorem biorthogonal_norm_isLUB_coefficients {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : ι → E} {Λ : ι → StrongDual ℂ E}
    (hb : IsSpectralMarkushevichBasis x Λ) (i : ι) :
    IsLUB (Set.range fun c : ι →₀ ℂ ↦ ‖c i‖ / ‖Finsupp.linearCombination ℂ Λ c‖) ‖x i‖ := by
  let L := Finsupp.linearCombination ℂ Λ
  have hcoeff := (biorthogonal_norm_le_iff_coefficients hb i (norm_nonneg (x i))).mp le_rfl
  constructor
  · rintro _ ⟨c, rfl⟩
    rcases eq_or_lt_of_le (norm_nonneg (L c)) with h | h
    · change ‖c i‖ / ‖L c‖ ≤ ‖x i‖
      simp [← h]
    · exact (div_le_iff₀ h).mpr (hcoeff c)
  · intro b hbnd
    have hratio (c : ι →₀ ℂ) : ‖c i‖ / ‖L c‖ ≤ b := hbnd (Set.mem_range_self c)
    apply (biorthogonal_norm_le_iff_coefficients hb i
      ((div_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hratio 0))).mpr
    intro c
    rcases eq_or_lt_of_le (norm_nonneg (L c)) with h | h
    · change ‖c i‖ ≤ b * ‖L c‖
      simpa only [← h, mul_zero] using (show ‖c i‖ ≤ ‖x i‖ * ‖L c‖ from hcoeff c)
    · exact (div_le_iff₀ h).mp (hratio c)

private theorem exists_half_sample {C : Type*} [Nonempty C] {v : C → ℝ} {k : ℝ}
    (hs : IsLUB (Set.range v) k) (hv : ∀ c, 0 ≤ v c) : ∃ c, k ≤ 2 * v c := by
  by_contra! h
  have half : k ≤ k / 2 := hs.2 (by rintro _ ⟨c, rfl⟩; linarith [h c])
  obtain ⟨c⟩ := ‹Nonempty C›
  linarith [h c, hv c]

/-- For nonnegative blocks, simultaneous finite samples detect summability. Choose each circle
maximum and a coefficient test within a factor of two of each individual norm. -/
private theorem summable_blocks_iff_finite_samples {Z J W C : Type*}
    (n : Z → ℕ) (jet : (z : Z) → Fin (n z) → J)
    (s : Z → Set W) (v : Z → W → ℝ) (k : J → ℝ) (r : J → C → ℝ)
    (hv : ∀ z w, 0 ≤ v z w) (hk : ∀ j, 0 ≤ k j) (hr : ∀ j c, 0 ≤ r j c)
    (hmax : ∀ z, ∃ w ∈ s z, ∀ t ∈ s z, v z t ≤ v z w)
    (hle : ∀ j c, r j c ≤ k j) (hhalf : ∀ j, ∃ c, k j ≤ 2 * r j c) :
    (∃ M : Z → ℝ, (∀ z, 0 ≤ M z) ∧ (∀ z w, w ∈ s z → v z w ≤ M z) ∧
      Summable (fun z ↦ M z * ∑ m, k (jet z m))) ↔
    ∃ B : ℝ, ∀ (T : Finset Z) (w : Z → W) (c : J → C), (∀ z ∈ T, w z ∈ s z) →
      ∑ z ∈ T, v z (w z) * ∑ m, r (jet z m) (c (jet z m)) ≤ B := by
  constructor
  · rintro ⟨M, hM, hval, hsum⟩
    refine ⟨∑' z, M z * ∑ m, k (jet z m), fun T w c hw ↦ ?_⟩
    refine (Finset.sum_le_sum fun z hz ↦ ?_).trans
      (hsum.sum_le_tsum T fun z _ ↦ mul_nonneg (hM z) (Finset.sum_nonneg fun _ _ ↦ hk _))
    exact mul_le_mul (hval z _ (hw z hz))
      (Finset.sum_le_sum fun m _ ↦ hle (jet z m) _) (Finset.sum_nonneg fun m _ ↦ hr _ _) (hM z)
  · rintro ⟨B, hB⟩
    choose w hw hgreatest using hmax
    choose c hc using hhalf
    refine ⟨fun z ↦ v z (w z), fun z ↦ hv _ _, hgreatest, summable_of_sum_le
      (fun z ↦ mul_nonneg (hv _ _) (Finset.sum_nonneg fun _ _ ↦ hk _)) (c := 2 * B) ?_⟩
    intro T
    calc
      (∑ z ∈ T, v z (w z) * ∑ m, k (jet z m)) ≤
          ∑ z ∈ T, v z (w z) * ∑ m, 2 * r (jet z m) (c (jet z m)) :=
        Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun m _ ↦ hc (jet z m)) (hv _ _)
      _ = 2 * ∑ z ∈ T, v z (w z) * ∑ m, r (jet z m) (c (jet z m)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        rw [← Finset.mul_sum, mul_left_comm]
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left (hB T w c fun z _ ↦ hw z) (by norm_num)

private theorem stripTest_mellinNorm_continuous (χ : PontryaginDual C𝔽)
    (φ : BruhatCompactSupport C𝔽) :
    Continuous (fun w : ℂ ↦ ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist χ w g ∂μ𝔽‖) := by
  let n (g : C𝔽) : ℝ := (ideleClassNorm F g).val
  let f (g : C𝔽) := φ.val g * (χ g : ℂ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have he (w : ℂ) (g : C𝔽) : f g * (n g : ℂ) ^ w = φ.val g * ideleClassNormTwist χ w g :=
    mul_assoc _ _ _
  have hφ : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have h := analyticOnNhd_integral_mul_cpow_of_integrable μ𝔽 f n hn.measurable
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _)) isOpen_univ (fun w _ ↦ by
      simp only [he]
      exact (hφ.mul (ideleClassNormTwist χ w).continuous).integrable_of_hasCompactSupport
        (show HasCompactSupport φ.val from φ.property.2).mul_right)
  simp only [he] at h
  exact (show Differentiable ℂ _ from fun w ↦ (h w (mem_univ _)).differentiableAt).continuous.norm

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The norm of each biorthogonal vector is the
least upper bound of finite coefficient ratios in the actual weighted jet space. This includes
all the other derivative orders at the same zero as well as the jets at different zeros.
Reconstruction: this expresses the biorthogonal norm needed in (10.3.2.7). -/
theorem spectralStripJet_norm_isLUB_finiteCoefficients
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (i : J(χ)) :
    let u (j : J(χ)) := (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))
    IsLUB (range fun c : J(χ) →₀ ℂ ↦ ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖) ‖x i‖ := by
  intro u
  have hd := (spectralSobolevDualEmbedding_isometry_range (F := F) a hStrip(hα) hs₀(hs)).1
  have he : D ∘ Λ = u := funext hj
  have hn (c : J(χ) →₀ ℂ) :
      ‖Finsupp.linearCombination ℂ u c‖ = ‖Finsupp.linearCombination ℂ Λ c‖ := by
    rw [← he, ← Finsupp.apply_linearCombination, hd.norm_map_of_map_zero (map_zero D)]
  simpa only [hn] using biorthogonal_norm_isLUB_coefficients hb i

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The circle majorant of (10.3.2.7) exists
exactly when one constant bounds the displayed finite tests. Pick a point on the Mellin circle
at each of finitely many zeros and, independently for each retained jet there, a finite linear
combination of the explicit weighted jets. The numerator reads one coefficient of that
combination.
Reconstruction: the finite tests express the missing estimate using the scalar Mellin transform
and the explicit jets. A uniform bound for these tests at the genuine zeros remains open. -/
theorem spectralStripConvolution_summable_jetNorms_iff_finite_samples
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) :
    let u (j : J(χ)) := (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))
    let j (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) : J(χ) := jet(z, m)
    let v (z : Z(χ, α)) (w : ℂ) := ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖
    let circle (z : Z(χ, α)) := Metric.sphere (shift(z.val.2.1, z.val.2.2))
      (2 * Real.exp ((4 * α + s) / 2))
    let ratio (i : J(χ)) (c : J(χ) →₀ ℂ) := ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖
    (∃ M : Z(χ, α) → ℝ, (∀ z, 0 ≤ M z) ∧ (∀ z w, w ∈ circle z → v z w ≤ M z) ∧
      Summable (fun z ↦ M z * ∑ m, ‖Λ (j z m)‖ * ‖x (j z m)‖)) ↔
    ∃ B : ℝ, ∀ (T : Finset (Z(χ, α))) (w : Z(χ, α) → ℂ) (c : J(χ) → J(χ) →₀ ℂ),
      (∀ z ∈ T, w z ∈ circle z) →
      ∑ z ∈ T, v z (w z) * ∑ m, ‖u (j z m)‖ * ratio (j z m) (c (j z m)) ≤ B := by
  intro u j v circle ratio
  have hiso := (spectralSobolevDualEmbedding_isometry_range (F := F) a hStrip(hα) hs₀(hs)).1
  have hn (i : J(χ)) : ‖u i‖ = ‖Λ i‖ := by
    change ‖(spectralStripJet_memLp χ hα hs₀(hs) i).toLp (raw(χ, i))‖ = _
    rw [← hj i, hiso.norm_map_of_map_zero (map_zero D)]
  have hlub (i : J(χ)) : IsLUB (range (ratio i)) ‖x i‖ :=
    spectralStripJet_norm_isLUB_finiteCoefficients a hα hs χ x Λ hb hj i
  have hp (i : J(χ)) (c : J(χ) →₀ ℂ) : 0 ≤ ratio i c := div_nonneg (norm_nonneg _) (norm_nonneg _)
  apply summable_blocks_iff_finite_samples (fun z ↦ N(χ, α, s, z)) j circle v
    (fun i ↦ ‖Λ i‖ * ‖x i‖) (fun i c ↦ ‖u i‖ * ratio i c)
    (fun _ _ ↦ norm_nonneg _) (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (hp _ _))
  · intro z
    obtain ⟨w, hw, hmax⟩ := (isCompact_sphere (shift(z.val.2.1, z.val.2.2))
      (2 * Real.exp ((4 * α + s) / 2))).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr (by positivity))
      (stripTest_mellinNorm_continuous (χ z.val.1) φ).continuousOn
    exact ⟨w, hw, fun t ht ↦ hmax ht⟩
  · intro i c
    rw [hn]
    exact mul_le_mul_of_nonneg_left ((hlub i).1 (mem_range_self c)) (norm_nonneg _)
  · intro i
    obtain ⟨c, hc⟩ := exists_half_sample (hlub i) (hp i)
    refine ⟨c, ?_⟩
    rw [hn, mul_left_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)

private theorem spectralStripJet_linearIndependent_of_biorthogonal
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) :
    LinearIndependent ℂ (fun j : J(χ) ↦ (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) := by
  have hΛ : LinearIndependent ℂ Λ := LinearIndependent.of_pairwise_dual_eq_zero_one Λ
    (fun j ↦ (NormedSpace.inclusionInDoubleDual ℂ _ (x j)).toLinearMap)
    (fun i j hij ↦ hb.2.1 i j hij) hb.1
  have he : D ∘ Λ = fun j ↦ (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)) := funext hj
  rw [← he]
  exact hΛ.map' D (LinearMap.ker_eq_bot.mpr
    (spectralSobolevDualEmbedding_isometry_range (F := F) a hStrip(hα) hs₀(hs)).1.injective)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The norm of the biorthogonal vector
at each retained jet is the supremum of the square roots of its diagonal entries
in the inverses of the finite Gram matrices of the weighted jets.
Reconstruction: this formula computes the coordinate norm needed in (10.3.2.7). -/
theorem spectralStripJet_norm_isLUB_finiteGram
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (i : J(χ)) :
    let u (j : J(χ)) := (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))
    IsLUB (range (finiteGramCoordinate u i)) ‖x i‖ := by
  intro u
  exact (finiteGram_coefficient_isLUB_iff
    (spectralStripJet_linearIndependent_of_biorthogonal a hα hs χ x Λ hb hj) i _).mp
    (spectralStripJet_norm_isLUB_finiteCoefficients a hα hs χ x Λ hb hj i)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The circle majorant exists exactly when
one constant bounds the finite sums below. Every term uses a diagonal entry of the
inverse of the same principal Gram matrix on `S`. Jets outside `S` contribute zero.
Reconstruction: this is a finite matrix criterion for the missing bound in (10.3.2.7). -/
theorem spectralStripConvolution_summable_jetNorms_iff_finiteGram
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) :
    let u (j : J(χ)) := (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))
    let j (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) : J(χ) := jet(z, m)
    let v (z : Z(χ, α)) (w : ℂ) := ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖
    let circle (z : Z(χ, α)) := Metric.sphere (shift(z.val.2.1, z.val.2.2))
      (2 * Real.exp ((4 * α + s) / 2))
    (∃ M : Z(χ, α) → ℝ, (∀ z, 0 ≤ M z) ∧ (∀ z w, w ∈ circle z → v z w ≤ M z) ∧
      Summable (fun z ↦ M z * ∑ m, ‖Λ (j z m)‖ * ‖x (j z m)‖)) ↔
    ∃ B : ℝ, ∀ (T : Finset (Z(χ, α))) (w : Z(χ, α) → ℂ) (S : Finset (J(χ))),
      (∀ z ∈ T, w z ∈ circle z) →
      ∑ z ∈ T, v z (w z) * ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B := by
  classical
  intro u j v circle
  have hu : LinearIndependent ℂ u := spectralStripJet_linearIndependent_of_biorthogonal a hα hs χ x Λ hb hj
  let ratio (i : J(χ)) (c : J(χ) →₀ ℂ) := ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖
  refine (spectralStripConvolution_summable_jetNorms_iff_finite_samples a hα hs χ φ x Λ hb hj).trans ?_
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun T w S hw ↦ ?_⟩
    choose c _ hc using fun i : J(χ) ↦ (finiteGramCoordinate_isGreatest hu i S).1
    have he (i : J(χ)) : ratio i (c i) = finiteGramCoordinate u i S := hc i
    simp_rw [← he]
    exact hB T w c hw
  · rintro ⟨B, hB⟩
    refine ⟨B, fun T w c hw ↦ ?_⟩
    let S := T.biUnion (fun z ↦ Finset.univ.biUnion (fun m : Fin (N(χ, α, s, z)) ↦ (c (j z m)).support))
    have hle (z : Z(χ, α)) (hz : z ∈ T) (m : Fin (N(χ, α, s, z))) :
        ratio (j z m) (c (j z m)) ≤ finiteGramCoordinate u (j z m) S := by
      apply (finiteGramCoordinate_isGreatest hu (j z m) S).2
      refine ⟨c (j z m), ?_, rfl⟩
      exact fun _ hk ↦ Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hk⟩⟩
    refine (Finset.sum_le_sum fun z hz ↦ ?_).trans (hB T w S hw)
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ ↦
      mul_le_mul_of_nonneg_left (hle z hz m) (norm_nonneg _)) (norm_nonneg _)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455.
Reconstruction: the fixed Mellin circles in (10.3.2.7) and the weighted jets determine
each finite sum below. All coordinate factors come from one principal Gram matrix.
Gap: a uniform bound for these finite sums at the genuine Hecke zeros is unknown.
The issue is the growth of the inverse Gram diagonal when zeros cluster. -/
theorem spectralStripConvolution_finiteGram_bound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) (φ : BruhatCompactSupport C𝔽) :
    let u (j : J(χ)) := (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))
    let j (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) : J(χ) := jet(z, m)
    let v (z : Z(χ, α)) (w : ℂ) := ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖
    let circle (z : Z(χ, α)) := Metric.sphere (shift(z.val.2.1, z.val.2.2))
      (2 * Real.exp ((4 * α + s) / 2))
    ∃ B : ℝ, ∀ (T : Finset (Z(χ, α))) (w : Z(χ, α) → ℂ) (S : Finset (J(χ))),
      (∀ z ∈ T, w z ∈ circle z) →
      ∑ z ∈ T, v z (w z) * ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B := by
  sorry

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455.
At width zero and exponent two the finite Gram bound is equivalent to a single
nonnegative series. The summand uses the actual maximum on the Mellin circle and
the nearest actual zeros on the same character. Convergence for general compact
Bruhat tests remains open. -/
theorem spectralStripConvolution_finiteGram_bound_iff_trueGaps
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (φ : BruhatCompactSupport C𝔽) :
    let u (j : SpectralStripJetIndex χ a 0 2) :=
      (spectralStripJet_memLp χ (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) j).toLp (raw(χ, j))
    let j (z : Z(χ, 0)) (m : Fin (N(χ, 0, 2, z))) : SpectralStripJetIndex χ a 0 2 := jet(z, m)
    let v (z : Z(χ, 0)) (w : ℂ) := ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖
    let circle (z : Z(χ, 0)) := Metric.sphere (shift(z.val.2.1, z.val.2.2)) (2 * Real.exp ((4 * 0 + 2) / 2))
    (∃ B : ℝ, ∀ (T : Finset (Z(χ, 0))) (w : Z(χ, 0) → ℂ)
      (S : Finset (SpectralStripJetIndex χ a 0 2)), (∀ z ∈ T, w z ∈ circle z) →
      ∑ z ∈ T, v z (w z) * ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B) ↔
      Summable (fun z : Z(χ, 0) ↦ sSup ((v z) '' circle z) *
        Real.sqrt (spectralLineTrueGramDiagonal χ (spectralLineZeroJet χ z))) := by
  intro u j v circle
  let k (z : Z(χ, 0)) (S : Finset (SpectralStripJetIndex χ a 0 2)) :=
    ‖u (spectralLineZeroJet χ z)‖ * finiteGramCoordinate u (spectralLineZeroJet χ z) S
  have hsum (z : Z(χ, 0)) (S : Finset (SpectralStripJetIndex χ a 0 2)) :
      (∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S) = k z S :=
    spectralLine_sum_retainedJets_two χ z (fun i ↦ ‖u i‖ * finiteGramCoordinate u i S)
  simp_rw [hsum]
  apply (summable_maxima_iff_common_finite_bound v circle k _ _ (fun _ _ ↦ norm_nonneg _)
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (finiteGramCoordinate_nonneg _ _ _)) _ _
    (fun z ↦ spectralLine_finiteGram_isGreatest χ hχ (spectralLineZeroJet χ z))).symm
  · intro z S U hSU
    exact mul_le_mul_of_nonneg_left ((monotone_finiteGramCoordinate
      (spectralStripJet_toLp_linearIndependent χ hχ a (le_refl 0) (by norm_num : (0 : ℝ) ≤ 2)) _) hSU) (norm_nonneg _)
  · intro z
    obtain ⟨w, hw, hmax⟩ := (isCompact_sphere (shift(z.val.2.1, z.val.2.2)) _).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.exp ((4 * 0 + 2) / 2)))
      (stripTest_mellinNorm_continuous (χ z.val.1) φ).continuousOn
    have hg : IsGreatest ((v z) '' circle z) (v z w) :=
      ⟨⟨w, hw, rfl⟩, fun _ ⟨q, hq, he⟩ ↦ he ▸ hmax hq⟩
    rw [hg.csSup_eq]
    exact hg

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455, the estimate of (10.3.2.7) on p. 455 in the
actual norms. For a Markushevich basis realizing the strip jets, some bounds for the scalar
Mellin transform of the test on the circles of the fixed radius around the zeros, multiplied
by the products `‖Λ_{z,m}‖ ‖x_{z,m}‖` of the norms of the coordinate functionals and of their
biorthogonal vectors summed over the jets at each zero, form a summable series.
Reconstruction: The paper does not state this. It is the project's formulation of a majorant
that suffices for `spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3`
(proved below, `spectralStripConvolution_traceCauchy_compact_block_series_of_summable_jetNorms`)
and for `spectralStripConvolution_traceCauchy_of_summable_jetNorms`. It is stronger than that
gap: it controls each biorthogonal vector, where the gap only needs the whole block at a zero.
The scalar Mellin bounds decay rapidly and the zeros are counted classically; what is not known
is a polynomial bound for `‖Λ_{z,m}‖ ‖x_{z,m}‖`. At a site with one surviving jet, `‖x_{z,0}‖` is
the reciprocal of the distance of `Λ_{z,0}` from the span of all the other jets, and by
`spectralStripConvolution_compact_block_series_forces_jet_separation` the gap itself already
forces a lower bound for the distance of `Λ_{z,0}` from each single `Λ_{w,0}`, `w ≠ z`.
It is not known how this statement connects with the rest of the proof in Lean; the pages that
use it are those of `spectralStripConvolution_traceCauchy`, pp. 452–455 and 458–473.
Proved here (#7468) from the open statement `spectralStripConvolution_finiteGram_bound`, a
bound for finite Gram matrices of the weighted jets, to which it is proved equivalent in this
file. No bound for the biorthogonal vectors of the zero jets is known when zeros cluster. At
width zero it needs at least a lower bound, polynomial in the height, for the distance between
distinct zeros of a Hecke `L`-function on the line (see #7241). No such bound is known to us
even for the Riemann zeta function, unconditionally or on the Riemann hypothesis. -/
theorem spectralStripConvolution_summable_jetNorms (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) (φ : BruhatCompactSupport C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) :
    ∃ M : Z(χ, α) → ℝ, (∀ z, 0 ≤ M z) ∧
      (∀ z : Z(χ, α), ∀ w ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2))
        (2 * Real.exp ((4 * α + s) / 2)),
        ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M z) ∧
      Summable (fun z : Z(χ, α) ↦ M z *
        ∑ m : Fin (N(χ, α, s, z)), ‖Λ (jet(z, m))‖ * ‖x (jet(z, m))‖) := by
  exact (spectralStripConvolution_summable_jetNorms_iff_finiteGram a hα hs χ φ x Λ _hb _hj).2
    (spectralStripConvolution_finiteGram_bound a hα hs χ _hχ φ)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. What the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` forces. If the block
traces are summable after every compact insertion, one constant bounds, at every zero `z`, the
Mellin value of the test times the norm of the zeroth jet `Λ_{z,0}`, relative to the distance
from `Λ_{z,0}` to the zeroth jet `Λ_{w,0}` at any other zero `w`. Two zeros whose jets come close
therefore force the Mellin value or the jet norm down. -/
theorem spectralStripConvolution_compact_block_series_forces_jet_separation
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽)
    (h : ∀ U : compactOperator (RingHom.id ℂ) Q(a, hStrip(hα), hs₀(hs)) Q(a, hStrip(hα), hs₀(hs)),
      Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
        (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ (U.val (x (jet(z, m))))))) :
    ∃ C > (0 : ℝ), ∀ (z w : Z(χ, α)), w ≠ z → ∀ (hz : 0 < N(χ, α, s, z))
      (hw : 0 < N(χ, α, s, w)),
      ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ *
          ‖Λ (jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z)))))‖ ≤
        C * ‖Λ (jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z))))) -
          Λ (jet(w, (⟨0, hw⟩ : Fin (N(χ, α, s, w)))))‖ := by
  have hrank (v : Q(a, hStrip(hα), hs₀(hs))) (f : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))) :
      IsCompactOperator (f.smulRight v) := by
    have he : f.smulRight v = (ContinuousLinearMap.toSpanSingleton ℂ v).comp f := by
      ext u
      simp
    rw [he]
    exact (isCompactOperator_of_locallyCompactSpace_dom f).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ v)
  obtain ⟨C, hC, hbound⟩ := spectralStripConvolution_mellin_norm_le_of_summable_rankOne_blocks
    a hα hs χ x Λ hb hj φ (fun v f ↦ h ⟨f.smulRight v, hrank v f⟩)
  refine ⟨C, hC, fun z w hwz hz hw ↦ ?_⟩
  refine (hbound z hz).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  rw [← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem (Submodule.subset_span ⟨w, hwz, ⟨0, hw⟩, rfl⟩)

/-- In a Markushevich system every combination of the other functionals vanishes at the
`i`th vector. -/
private theorem spectralSobolevQuotient_markushevich_span_apply {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x Λ) (i : ι)
    {ℓ : StrongDual ℂ E} (hℓ : ℓ ∈ Submodule.span ℂ (Λ '' {j | j ≠ i})) : ℓ (x i) = 0 := by
  induction hℓ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    exact hb.2.1 i j (Ne.symm hj)
  | zero => rfl
  | add f g _ _ hf hg => simp [hf, hg]
  | smul c f _ hf => simp [hf]

/-- In any normed space, the `i`th vector of a Markushevich system has norm at least the
reciprocal of the distance of the `i`th functional from the span of the others. -/
private theorem spectralSobolevQuotient_markushevich_le_norm_mul_infDist {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x Λ) (i : ι) :
    1 ≤ ‖x i‖ * Metric.infDist (Λ i) (Submodule.span ℂ (Λ '' {j | j ≠ i}) : Set _) := by
  have hx : 0 < ‖x i‖ := by
    refine norm_pos_iff.2 fun h ↦ ?_
    have := hb.1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  rw [← div_le_iff₀' hx]
  refine (Metric.le_infDist ⟨0, Submodule.zero_mem _⟩).2 fun ℓ hℓ ↦ ?_
  rw [div_le_iff₀' hx, dist_eq_norm]
  calc (1 : ℝ) = ‖(Λ i - ℓ) (x i)‖ := by
        simp [hb.1 i, spectralSobolevQuotient_markushevich_span_apply x Λ hb i hℓ]
    _ ≤ ‖Λ i - ℓ‖ * ‖x i‖ := (Λ i - ℓ).le_opNorm _
    _ = ‖x i‖ * ‖Λ i - ℓ‖ := mul_comm _ _

/-- In a space isometric to a Hilbert space the bound of
`spectralSobolevQuotient_markushevich_le_norm_mul_infDist` is an equality: the orthogonal part of
the Riesz vector of the `i`th functional, relative to the others, is a multiple of the `i`th
vector. -/
private theorem spectralSobolevQuotient_markushevich_norm_mul_infDist_le {ι E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (e : E ≃ₗᵢ[ℂ] H)
    (x : ι → E) (Λ : ι → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x Λ) (i : ι) :
    ‖x i‖ * Metric.infDist (Λ i) (Submodule.span ℂ (Λ '' {j | j ≠ i}) : Set _) ≤ 1 := by
  let ψ : H → StrongDual ℂ E := fun w ↦ (InnerProductSpace.toDual ℂ H w).comp
    (e : E →L[ℂ] H)
  have hψ (w v) : ψ w v = inner ℂ w (e v) := InnerProductSpace.toDual_apply_apply
  have hψnorm (w : H) : ‖ψ w‖ = ‖w‖ := by
    simp only [ψ]
    rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, LinearIsometryEquiv.norm_map]
  have hψsub (a b : H) : ψ a - ψ b = ψ (a - b) := by
    ext v; simp [hψ, inner_sub_left]
  have hψcont : Continuous ψ := by
    refine (LipschitzWith.of_dist_le_mul fun a b ↦ ?_).continuous (K := 1)
    rw [dist_eq_norm, hψsub, hψnorm, dist_eq_norm]; simp
  let y : ι → H := fun j ↦ (InnerProductSpace.toDual ℂ H).symm
    ((Λ j).comp (e.symm : H →L[ℂ] E))
  have hy (j) : ψ (y j) = Λ j := by
    ext v
    rw [hψ]
    change (InnerProductSpace.toDual ℂ H (y j)) (e v) = _
    simp [y]
  let S : Submodule ℂ H := Submodule.span ℂ (y '' {j | j ≠ i})
  let SΛ : Submodule ℂ (StrongDual ℂ E) := Submodule.span ℂ (Λ '' {j | j ≠ i})
  have hmap (w : H) (hw : w ∈ S) : ψ w ∈ SΛ := by
    induction hw using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨j, hj, rfl⟩ := hf
      rw [hy]; exact Submodule.subset_span ⟨j, hj, rfl⟩
    | zero =>
      have : ψ 0 = 0 := by ext v; simp [hψ]
      rw [this]; exact Submodule.zero_mem _
    | add f g _ _ hf hg =>
      have : ψ (f + g) = ψ f + ψ g := by ext v; simp [hψ, inner_add_left]
      rw [this]; exact Submodule.add_mem _ hf hg
    | smul c f _ hf =>
      have : ψ (c • f) = (starRingEnd ℂ c) • ψ f := by ext v; simp [hψ, inner_smul_left]
      rw [this]; exact Submodule.smul_mem _ _ hf
  let K : Submodule ℂ H := S.topologicalClosure
  let p : H := K.starProjection (y i)
  let q : H := y i - p
  have hq : q ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (y i)
  have hpK : p ∈ K := K.starProjection_apply_mem (y i)
  have hpcl : ψ p ∈ closure (SΛ : Set (StrongDual ℂ E)) := by
    have : p ∈ closure (S : Set H) := by
      rw [← Submodule.topologicalClosure_coe]; exact hpK
    exact map_mem_closure hψcont this fun w hw ↦ hmap w hw
  have hdist : Metric.infDist (Λ i) (SΛ : Set _) ≤ ‖q‖ := by
    rw [← Metric.infDist_closure]
    refine (Metric.infDist_le_dist_of_mem hpcl).trans_eq ?_
    rw [← hy, dist_eq_norm, hψsub, hψnorm]
  -- the vector representing `q`
  let v : E := e.symm q
  have hΛv (j) : Λ j v = inner ℂ (y j) q := by
    rw [← hy, hψ]; simp [v]
  have hothers (j) (hj : j ≠ i) : Λ j v = 0 := by
    rw [hΛv]
    exact Submodule.inner_right_of_mem_orthogonal
      (S.le_topologicalClosure (Submodule.subset_span (Set.mem_image_of_mem y hj))) hq
  have hself : Λ i v = (‖q‖ : ℂ) ^ 2 := by
    rw [hΛv]
    have : y i = p + q := by simp [q]
    rw [this, inner_add_left, Submodule.inner_right_of_mem_orthogonal hpK hq, zero_add,
      inner_self_eq_norm_sq_to_K]
    rfl
  have hv : v = ((‖q‖ : ℂ) ^ 2) • x i := by
    have hsep : ∀ j, Λ j (v - ((‖q‖ : ℂ) ^ 2) • x i) = 0 := by
      intro j
      by_cases hij : j = i
      · subst hij; simp [hself, hb.1 j]
      · simp [hothers j hij, hb.2.1 i j (Ne.symm hij)]
    have hz : v - ((‖q‖ : ℂ) ^ 2) • x i = 0 := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
      have he : ContinuousLinearMap.apply ℂ ℂ (v - ((‖q‖ : ℂ) ^ 2) • x i) =
          ContinuousLinearMap.apply ℂ ℂ (0 : E) := by
        apply ContinuousLinearMap.ext_on hb.2.2.2
        rintro _ ⟨j, rfl⟩
        change Λ j _ = Λ j 0
        rw [hsep j, map_zero]
      exact fun ℓ ↦ DFunLike.congr_fun he ℓ
    exact sub_eq_zero.mp hz
  have hnv : ‖q‖ = ‖q‖ ^ 2 * ‖x i‖ := by
    have h1 : ‖v‖ = ‖q‖ := by simp [v]
    calc ‖q‖ = ‖v‖ := h1.symm
      _ = _ := by rw [hv, norm_smul, norm_pow, Complex.norm_real, norm_norm]
  have hqx : ‖x i‖ * ‖q‖ ≤ 1 := by
    rcases eq_or_ne ‖q‖ 0 with h0 | h0
    · rw [h0, mul_zero]; exact zero_le_one
    · have : ‖q‖ * ‖x i‖ = 1 := by
        have := hnv
        field_simp at this
        nlinarith [this]
      linarith [mul_comm ‖q‖ ‖x i‖]
  exact (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)).trans hqx

/-- Paper: Remark 10.2.1.2, pp. 440–441, with Theorem 10.3.2.1(1), pp. 453–455. In a Markushevich
basis of the strip quotient, the norm of each biorthogonal vector is the reciprocal of the distance
of its coordinate functional from the linear span of all the other coordinate functionals. -/
theorem spectralSobolevQuotient_markushevich_norm_mul_infDist {ι : Type*}
    (x : ι → Q(a, hStrip(hα), hs₀(hs))) (Λ : ι → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ) (i : ι) :
    ‖x i‖ * Metric.infDist (Λ i) (Submodule.span ℂ (Λ '' {j | j ≠ i}) : Set _) = 1 :=
  le_antisymm
    (spectralSobolevQuotient_markushevich_norm_mul_infDist_le
      (globalThetaSobolev F a hStrip(hα) hs₀(hs)).quotientEquivOrthogonal x Λ hb i)
    (spectralSobolevQuotient_markushevich_le_norm_mul_infDist x Λ hb i)

local notation "u(" χ ", " j ")" => ((spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)) :
  CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455, the products `‖Λ_{z,m}‖ ‖x_{z,m}‖` of (10.3.2.7)
without the basis. For a Markushevich basis realizing the strip jets, the product of the norms
of a coordinate functional and of its biorthogonal vector is the norm of the jet in the
reciprocal-weight space divided by its distance there from the linear span of all the other
jets. -/
theorem spectralStripJet_norm_mul_norm_eq_div_infDist (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = u(χ, j)) (j : J(χ)) :
    ‖Λ j‖ * ‖x j‖ = ‖u(χ, j)‖ /
      Metric.infDist (u(χ, j)) (Submodule.span ℂ ((fun k ↦ u(χ, k)) '' {k | k ≠ j}) : Set _) := by
  have hD : Isometry D := (spectralSobolevDualEmbedding_isometry_range (F := F) a
    hStrip(hα) hs₀(hs)).1
  have hnorm : ‖Λ j‖ = ‖u(χ, j)‖ := by
    rw [← hj j, hD.norm_map_of_map_zero (map_zero D)]
  have himage : D '' (Submodule.span ℂ (Λ '' {k | k ≠ j}) : Set _) =
      (Submodule.span ℂ ((fun k ↦ u(χ, k)) '' {k | k ≠ j}) : Set _) := by
    rw [← Submodule.map_coe, Submodule.map_span, Set.image_image]
    congr 2
    exact Set.image_congr fun k _ ↦ hj k
  have hdist : Metric.infDist (u(χ, j))
      (Submodule.span ℂ ((fun k ↦ u(χ, k)) '' {k | k ≠ j}) : Set _) =
      Metric.infDist (Λ j) (Submodule.span ℂ (Λ '' {k | k ≠ j}) : Set _) := by
    rw [← himage, ← hj j, Metric.infDist_image hD]
  have hone := spectralSobolevQuotient_markushevich_norm_mul_infDist a hα hs x Λ hb j
  have hne : Metric.infDist (Λ j) (Submodule.span ℂ (Λ '' {k | k ≠ j}) : Set _) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hone; exact zero_ne_one hone
  rw [hdist, hnorm, eq_div_iff hne, mul_assoc, hone, mul_one]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The series of the majorant
`spectralStripConvolution_summable_jetNorms` does not depend on the basis: for any weights `M`, it
converges exactly when the series with `‖Λ_{z,m}‖ ‖x_{z,m}‖` replaced by the norm of the jet
divided by its distance from the span of all the other jets converges. That second series is a
statement about the jets alone, in the reciprocal-weight `L²` space. -/
theorem spectralStripConvolution_summable_jetNorms_iff_jetDistances
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = u(χ, j)) (M : Z(χ, α) → ℝ) :
    Summable (fun z : Z(χ, α) ↦ M z *
        ∑ m : Fin (N(χ, α, s, z)), ‖Λ (jet(z, m))‖ * ‖x (jet(z, m))‖) ↔
      Summable (fun z : Z(χ, α) ↦ M z * ∑ m : Fin (N(χ, α, s, z)),
        ‖u(χ, (jet(z, m) : J(χ)))‖ / Metric.infDist (u(χ, (jet(z, m) : J(χ))))
          (Submodule.span ℂ ((fun k : J(χ) ↦ u(χ, k)) '' {k : J(χ) | k ≠ (jet(z, m) : J(χ))}) : Set _)) := by
  refine Iff.of_eq (congrArg Summable (funext fun z ↦ congrArg (M z * ·)
    (Finset.sum_congr rfl fun m _ ↦ ?_)))
  exact spectralStripJet_norm_mul_norm_eq_div_infDist a hα hs χ x Λ hb hj _

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. A basis-free sufficient condition for the block
series of the recorded gap `spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3`
(#7241), after inserting any bounded operator: Mellin bounds on the circles around the zeros,
times the sums over the jets at each zero of the norm of the jet divided by its distance from
the span of all the other jets in the reciprocal-weight `L²` space, form a summable series. By
`spectralStripConvolution_summable_jetNorms_iff_jetDistances` this is the majorant
`spectralStripConvolution_summable_jetNorms` with the basis removed. -/
theorem spectralStripConvolution_block_series_of_summable_jetDistances
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = u(χ, j))
    (φ : BruhatCompactSupport C𝔽) (M : Z(χ, α) → ℝ) (hM : ∀ z, 0 ≤ M z)
    (hMellin : ∀ z : Z(χ, α), ∀ w ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2))
      (2 * Real.exp ((4 * α + s) / 2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M z)
    (hdistances : Summable (fun z : Z(χ, α) ↦ M z * ∑ m : Fin (N(χ, α, s, z)),
        ‖u(χ, (jet(z, m) : J(χ)))‖ / Metric.infDist (u(χ, (jet(z, m) : J(χ))))
          (Submodule.span ℂ ((fun k : J(χ) ↦ u(χ, k)) '' {k : J(χ) | k ≠ (jet(z, m) : J(χ))}) : Set _)))
    (U : Q(a, hStrip(hα), hs₀(hs)) →L[ℂ] Q(a, hStrip(hα), hs₀(hs))) :
    Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
      (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ (U (x (jet(z, m)))))) :=
  spectralStripConvolution_block_series_of_summable_jetNorms a hα hs χ x Λ hj φ M hM hMellin
    ((spectralStripConvolution_summable_jetNorms_iff_jetDistances a hα hs χ x Λ hb hj M).2
      hdistances) U

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. What the majorant
`spectralStripConvolution_summable_jetNorms` forces on the spacing of the jets. Choose for every
jet `j` some other jet `c j`. If the series of the majorant converges for nonnegative weights `M`,
so does the series with `‖Λ_{z,m}‖ ‖x_{z,m}‖` replaced by the norm of the jet divided by its
distance from the chosen other jet, in the reciprocal-weight `L²` space. -/
theorem spectralStripConvolution_summable_jetNorms_forces_summable_separation
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = u(χ, j)) (M : Z(χ, α) → ℝ) (hM : ∀ z, 0 ≤ M z)
    (c : J(χ) → J(χ)) (hc : ∀ j, c j ≠ j)
    (hsum : Summable (fun z : Z(χ, α) ↦ M z *
        ∑ m : Fin (N(χ, α, s, z)), ‖Λ (jet(z, m))‖ * ‖x (jet(z, m))‖)) :
    Summable (fun z : Z(χ, α) ↦ M z * ∑ m : Fin (N(χ, α, s, z)),
        ‖u(χ, (jet(z, m) : J(χ)))‖ / ‖u(χ, (jet(z, m) : J(χ))) - u(χ, c (jet(z, m) : J(χ)))‖) := by
  have hle (j : J(χ)) : ‖u(χ, j)‖ / ‖u(χ, j) - u(χ, c j)‖ ≤ ‖Λ j‖ * ‖x j‖ := by
    rw [spectralStripJet_norm_mul_norm_eq_div_infDist a hα hs χ x Λ hb hj j]
    have hpos : 0 < Metric.infDist (u(χ, j))
        (Submodule.span ℂ ((fun k ↦ u(χ, k)) '' {k | k ≠ j}) : Set _) := by
      have h1 : 1 ≤ ‖Λ j‖ * ‖x j‖ := by
        have := (Λ j).le_opNorm (x j)
        rwa [hb.1 j, norm_one] at this
      refine Metric.infDist_nonneg.lt_of_ne fun h ↦ ?_
      have := spectralStripJet_norm_mul_norm_eq_div_infDist a hα hs χ x Λ hb hj j
      rw [← h, div_zero] at this
      linarith
    have hdle : Metric.infDist (u(χ, j))
        (Submodule.span ℂ ((fun k ↦ u(χ, k)) '' {k | k ≠ j}) : Set _) ≤
        ‖u(χ, j) - u(χ, c j)‖ := by
      rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem (Submodule.subset_span ⟨c j, hc j, rfl⟩)
    exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hdle
  refine Summable.of_nonneg_of_le (fun z ↦ mul_nonneg (hM z) (Finset.sum_nonneg fun m _ ↦
    div_nonneg (norm_nonneg _) (norm_nonneg _))) (fun z ↦ mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun m _ ↦ hle _) (hM z)) hsum

section LineHolder

local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽

local instance lineHolderCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- The logarithm of the idele class norm carries the Tamagawa measure to a multiple of
Lebesgue measure. -/
private theorem lineHolder_log_preserving : MeasurePreserving (logIdeleClassNorm F) μ𝔽
    (Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
  exact (orbitalJet_logNorm_measurePreserving (F := F)).smul_measure _

/-- A zeroth jet at real offset zero is the character times a unimodular wave in the
logarithm of the norm. -/
private theorem lineHolder_jet_phase (η : PontryaginDual C𝔽) (t : ℝ) (g : C𝔽) :
    spectralZeroJet η 0 t 0 g =
      (η g : ℂ) * Complex.exp (Complex.I * ((t * logIdeleClassNorm F g : ℝ) : ℂ)) := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^
    ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ ^ 0 = _
  rw [zero_add, pow_zero, mul_one, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le]
  congr 2
  change (logIdeleClassNorm F g : ℂ) * (t * Complex.I) = _
  push_cast
  ring

/-- An elementary interpolation: a quantity bounded by `2` and by `y ≥ 0` is bounded by
`2 y ^ β` for `0 ≤ β ≤ 1`. -/
private theorem lineHolder_le_two_mul_rpow {q y β : ℝ} (hy : 0 ≤ y) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h2 : q ≤ 2) (hq : q ≤ y) : q ≤ 2 * y ^ β := by
  rcases le_or_gt 1 y with h1 | h1
  · have : 1 ≤ y ^ β := Real.one_le_rpow h1 hβ0
    linarith
  · have hyβ : y ≤ y ^ β := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' hy h1.le hβ0 hβ1
    have : 0 ≤ y ^ β := Real.rpow_nonneg hy β
    linarith

/-- Pointwise Hölder bound for the difference of two zeroth jets at real offset zero on one
character. -/
private theorem lineHolder_jet_sub_le (η : PontryaginDual C𝔽) (u v : ℝ) (g : C𝔽)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ‖spectralZeroJet η 0 u 0 g - spectralZeroJet η 0 v 0 g‖ ≤
      2 * |u - v| ^ β * (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2) := by
  set L := logIdeleClassNorm F g
  have hsplit : Complex.exp (Complex.I * ((u * L : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((v * L : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((u - v) * L : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hphase : ‖spectralZeroJet η 0 u 0 g - spectralZeroJet η 0 v 0 g‖ =
      ‖Complex.exp (Complex.I * (((u - v) * L : ℝ) : ℂ)) - 1‖ := by
    rw [lineHolder_jet_phase, lineHolder_jet_phase, ← mul_sub, norm_mul, Circle.norm_coe, one_mul,
      hsplit, ← mul_sub_one, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have h2 : ‖Complex.exp (Complex.I * (((u - v) * L : ℝ) : ℂ)) - 1‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (Complex.I * (((u - v) * L : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
  have hy : ‖Complex.exp (Complex.I * (((u - v) * L : ℝ) : ℂ)) - 1‖ ≤ |u - v| * |L| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (u - v) * L)
    rwa [Real.norm_eq_abs, abs_mul] at this
  have hmain := lineHolder_le_two_mul_rpow (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hβ0 hβ1 h2 hy
  rw [hphase]
  refine hmain.trans ?_
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_assoc]
  gcongr
  have hL : |L| ≤ (1 + L ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  calc |L| ^ β ≤ ((1 + L ^ 2) ^ (1 / 2 : ℝ)) ^ β := Real.rpow_le_rpow (abs_nonneg _) hL hβ0
    _ = (1 + L ^ 2) ^ (β / 2) := by
      rw [← Real.rpow_mul (by positivity)]; ring_nf

/-- At width zero the reciprocal Sobolev measure is the Tamagawa measure with density
`(1 + L²)^(-s/2)` in the logarithm `L` of the norm. -/
private theorem lineHolder_measure_eq (s : ℝ) {α : ℝ} (hα0 : α = 0) :
    intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true =
      Measure.withDensity μ𝔽 fun g ↦
        ENNReal.ofReal ((1 + logIdeleClassNorm F g ^ 2) ^ (s / 2))⁻¹ := by
  subst hα0
  simp [intervalSobolevMeasure, intervalSobolevDensity]

/-- At width zero the weight `(1 + L²)^(β/2)` is square integrable for the reciprocal Sobolev
measure once `2β < s - 1`. -/
private theorem lineHolder_weight_memLp {α s β : ℝ} (hα0 : α = 0) (hβs : 2 * β < s - 1) :
    MemLp (fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) 2
      (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true) := by
  have hLc : Continuous (logIdeleClassNorm F) := orbitalJet_logNorm_continuous (F := F)
  have hbase : Continuous fun g : C𝔽 ↦ 1 + logIdeleClassNorm F g ^ 2 :=
    continuous_const.add (hLc.pow 2)
  have hcont : Continuous fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2) :=
    hbase.rpow_const fun _ ↦ Or.inl (by positivity)
  have hdens : Measurable fun g : C𝔽 ↦
      ENNReal.ofReal ((1 + logIdeleClassNorm F g ^ 2) ^ (s / 2))⁻¹ :=
    (hbase.rpow_const fun _ ↦ Or.inl (by positivity)).measurable.inv.ennreal_ofReal
  rw [lineHolder_measure_eq s hα0]
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
  rw [integrable_withDensity_iff hdens (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * β := by
    rw [Module.finrank_self]; push_cast; linarith
  have hi := (lineHolder_log_preserving (F := F)).integrable_comp_of_integrable
    ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) hr).smul_measure_nnreal
      (c := Measure.haarScalarFactor μ𝔽 ν𝔽))
  apply hi.congr (ae_of_all _ fun g ↦ ?_)
  set L := logIdeleClassNorm F g
  have h1 : (0 : ℝ) < 1 + L ^ 2 := by positivity
  simp only [Function.comp_apply, Real.norm_eq_abs, sq_abs]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_nonneg h1.le _))]
  change (1 + L ^ 2) ^ (-(s - 2 * β) / 2) = ((1 + L ^ 2) ^ (β / 2)) ^ 2 * ((1 + L ^ 2) ^ (s / 2))⁻¹
  rw [← Real.rpow_natCast ((1 + L ^ 2) ^ (β / 2)) 2, ← Real.rpow_mul h1.le, ← Real.rpow_neg h1.le,
    ← Real.rpow_add h1]
  congr 1
  push_cast
  ring

/-- At width zero, the distance between the zeroth jets at two zeros of one character, in the
reciprocal-weight space, is at most a constant times the `β`-th power of the distance between
their ordinates. -/
private theorem lineHolder_jet_dist_le (hα0 : α = 0) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβs : 2 * β < s - 1) (j k : J(χ))
    (hχk : k.val.1 = j.val.1) (hj0 : j.val.2.1 = 0) (hk0 : k.val.2.1 = 0)
    (hjm : j.val.2.2.2 = 0) (hkm : k.val.2.2.2 = 0) :
    ‖u(χ, j) - u(χ, k)‖ ≤ 2 * |j.val.2.2.1 - k.val.2.2.1| ^ β *
      (eLpNorm (fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) 2
        (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true)).toReal := by
  have hmj := spectralStripJet_memLp χ hα hs₀(hs) j
  have hmk := spectralStripJet_memLp χ hα hs₀(hs) k
  rw [← MemLp.toLp_sub, Lp.norm_toLp]
  have hbound : ∀ g : C𝔽, ‖(raw(χ, j) - raw(χ, k)) g‖ ≤
      ‖(2 * |j.val.2.2.1 - k.val.2.2.1| ^ β) * (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)‖ := by
    intro g
    have hj' : raw(χ, j) g = spectralZeroJet (χ j.val.1) 0 j.val.2.2.1 0 g := by
      simp only [hj0, hjm]
    have hk' : raw(χ, k) g = spectralZeroJet (χ j.val.1) 0 k.val.2.2.1 0 g := by
      simp only [hk0, hkm, hχk]
    rw [Pi.sub_apply, hj', hk', Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (lineHolder_jet_sub_le (χ j.val.1) _ _ g hβ0 hβ1).trans_eq (by ring)
  calc (eLpNorm (raw(χ, j) - raw(χ, k)) 2 _).toReal
      ≤ (eLpNorm (fun g : C𝔽 ↦ (2 * |j.val.2.2.1 - k.val.2.2.1| ^ β) *
          (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) 2
          (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true)).toReal := by
        refine ENNReal.toReal_mono ?_
          (eLpNorm_mono (hmj.sub hmk).aestronglyMeasurable fun g ↦ hbound g)
        exact ((lineHolder_weight_memLp (F := F) hα0 hβs).const_mul _).eLpNorm_ne_top
    _ = _ := by
        rw [show (fun g : C𝔽 ↦ (2 * |j.val.2.2.1 - k.val.2.2.1| ^ β) *
            (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) =
            (2 * |j.val.2.2.1 - k.val.2.2.1| ^ β) •
              (fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) from rfl,
          eLpNorm_const_smul, ENNReal.toReal_mul, toReal_eNorm, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. What the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241) forces at width
zero, in terms of the ordinates. If the block traces are summable after every compact insertion,
then for every exponent `0 ≤ β ≤ 1` with `2β < s - 1` one constant bounds, at any two distinct
zeros `z, w` of one character, the Mellin value of the test at `z` by that constant times
`|Im z - Im w| ^ β`. So two zeros on the line that come close force the Mellin transform of
every test down at both; with tests modulated to a prescribed height this becomes a lower bound,
polynomial in the height, for the gaps between zeros on the line. -/
theorem spectralStripConvolution_compact_block_series_forces_line_holder (hα0 : α = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽)
    (h : ∀ U : compactOperator (RingHom.id ℂ) Q(a, hStrip(hα), hs₀(hs)) Q(a, hStrip(hα), hs₀(hs)),
      Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
        (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ (U.val (x (jet(z, m)))))))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβs : 2 * β < s - 1) :
    ∃ C > (0 : ℝ), ∀ (z w : Z(χ, α)), w ≠ z → w.val.1 = z.val.1 →
      ∀ (_hz : 0 < N(χ, α, s, z)) (_hw : 0 < N(χ, α, s, w)),
      ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ ≤ C * |z.val.2.2 - w.val.2.2| ^ β := by
  obtain ⟨C, hC, hsep⟩ :=
    spectralStripConvolution_compact_block_series_forces_jet_separation a hα hs χ x Λ hb hj φ h
  obtain ⟨c, hc, hlow⟩ := spectralStripJet_lowerBound χ hχ (a := a) hα hs
  have hD : Isometry D := (spectralSobolevDualEmbedding_isometry_range (F := F) a
    hStrip(hα) hs₀(hs)).1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (eLpNorm (fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) 2
    (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true)).toReal := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ ENNReal.toReal_nonneg
  have hKfin := (lineHolder_weight_memLp (F := F) hα0 hβs).eLpNorm_ne_top
  refine ⟨C * (2 * K + 1) / c, div_pos (mul_pos hC (by linarith)) hc, fun z w hwz hχzw hz hw ↦ ?_⟩
  let jz : J(χ) := jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z))))
  let jw : J(χ) := jet(w, (⟨0, hw⟩ : Fin (N(χ, α, s, w))))
  have hz0 : z.val.2.1 = 0 := by
    have := z.property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hw0 : w.val.2.1 = 0 := by
    have := w.property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hdiff : ‖Λ jz - Λ jw‖ ≤ 2 * |z.val.2.2 - w.val.2.2| ^ β * K := by
    rw [← hD.norm_map_of_map_zero (map_zero D), map_sub, hj, hj, hK]
    exact lineHolder_jet_dist_le a hα hs hα0 χ hβ0 hβ1 hβs jz jw hχzw hz0 hw0 rfl rfl
  have hnorm : c ≤ ‖Λ jz‖ := by
    rw [← hD.norm_map_of_map_zero (map_zero D), hj]
    exact hlow jz
  have hsepzw := hsep z w hwz hz hw
  have hM0 : 0 ≤ ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ := norm_nonneg _
  have hd0 : 0 ≤ |z.val.2.2 - w.val.2.2| ^ β := Real.rpow_nonneg (abs_nonneg _) _
  rw [mul_comm (C * (2 * K + 1) / c), ← mul_div_assoc, le_div_iff₀ hc]
  calc ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ * c
      ≤ ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ * ‖Λ jz‖ :=
        mul_le_mul_of_nonneg_left hnorm hM0
    _ ≤ C * ‖Λ jz - Λ jw‖ := hsepzw
    _ ≤ C * (2 * |z.val.2.2 - w.val.2.2| ^ β * K) := mul_le_mul_of_nonneg_left hdiff hC.le
    _ ≤ |z.val.2.2 - w.val.2.2| ^ β * (C * (2 * K + 1)) := by
      nlinarith [mul_nonneg hC.le hd0]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. What the majorant
`spectralStripConvolution_summable_jetNorms` (equivalently the open bound
`spectralStripConvolution_finiteGram_bound`, #7455) forces at width zero, in terms of the
ordinates. Assign to each zero `z` another zero `w z` of the same character. If the series of
the majorant converges for nonnegative weights `M`, then so does `Σ M z / |Im z - Im (w z)| ^ β`
for every exponent `0 ≤ β ≤ 1` with `2β < s - 1`. With `M` the Mellin maxima of the test and
`w z` a nearest zero, this is a quantitative lower bound for the gaps between zeros on the line. -/
theorem spectralStripConvolution_summable_jetNorms_forces_line_gaps (hα0 : α = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ) (hj : ∀ j, D (Λ j) = u(χ, j))
    (M : Z(χ, α) → ℝ) (hM : ∀ z, 0 ≤ M z)
    (hsum : Summable (fun z : Z(χ, α) ↦ M z *
        ∑ m : Fin (N(χ, α, s, z)), ‖Λ (jet(z, m))‖ * ‖x (jet(z, m))‖))
    (w : Z(χ, α) → Z(χ, α)) (hw : ∀ z, w z ≠ z) (hwχ : ∀ z, (w z).val.1 = z.val.1)
    (hN : ∀ z : Z(χ, α), 0 < N(χ, α, s, z)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβs : 2 * β < s - 1) :
    Summable (fun z : Z(χ, α) ↦ M z * (|z.val.2.2 - (w z).val.2.2| ^ β)⁻¹) := by
  let zero (j : J(χ)) : Z(χ, α) :=
    ⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩
  let c (j : J(χ)) : J(χ) := jet(w (zero j), (⟨0, hN _⟩ : Fin (N(χ, α, s, w (zero j)))))
  have hc : ∀ j, c j ≠ j := by
    intro j hcj
    apply hw (zero j)
    apply Subtype.ext
    have h1 := congrArg (fun i : J(χ) ↦ i.val.1) hcj
    have h2 := congrArg (fun i : J(χ) ↦ i.val.2.1) hcj
    have h3 := congrArg (fun i : J(χ) ↦ i.val.2.2.1) hcj
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hsep := spectralStripConvolution_summable_jetNorms_forces_summable_separation a hα hs χ x Λ
    hb hj M hM c hc hsum
  obtain ⟨c₀, hc₀, hlow⟩ := spectralStripJet_lowerBound χ hχ (a := a) hα hs
  have hind := spectralStripJet_linearIndependent_of_biorthogonal a hα hs χ x Λ hb hj
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (eLpNorm (fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2))
    2 (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true)).toReal := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ ENNReal.toReal_nonneg
  refine Summable.of_nonneg_of_le (fun z ↦ mul_nonneg (hM z) (inv_nonneg.mpr
    (Real.rpow_nonneg (abs_nonneg _) _))) (fun z ↦ ?_) (hsep.mul_left ((2 * K + 1) / c₀))
  let j0 : J(χ) := jet(z, (⟨0, hN z⟩ : Fin (N(χ, α, s, z))))
  have hz0 : z.val.2.1 = 0 := by
    have := z.property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hw0 : (w z).val.2.1 = 0 := by
    have := (w z).property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hdist : ‖u(χ, j0) - u(χ, c j0)‖ ≤ 2 * |z.val.2.2 - (w z).val.2.2| ^ β * K := by
    rw [hK]
    exact lineHolder_jet_dist_le a hα hs hα0 χ hβ0 hβ1 hβs j0 (c j0) (hwχ z) hz0 hw0 rfl rfl
  have hpos : 0 < ‖u(χ, j0) - u(χ, c j0)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hc j0 (hind.injective h).symm)
  have hterm : (|z.val.2.2 - (w z).val.2.2| ^ β)⁻¹ ≤
      (2 * K + 1) / c₀ * (‖u(χ, j0)‖ / ‖u(χ, j0) - u(χ, c j0)‖) := by
    rcases (Real.rpow_nonneg (abs_nonneg (z.val.2.2 - (w z).val.2.2)) β).eq_or_lt with h0 | hd
    · rw [← h0, inv_zero]
      exact mul_nonneg (div_nonneg (by linarith) hc₀.le) (div_nonneg (norm_nonneg _) hpos.le)
    · have hu : c₀ ≤ ‖u(χ, j0)‖ := hlow j0
      rw [div_mul_div_comm, le_div_iff₀ (mul_pos hc₀ hpos), inv_mul_eq_div, div_le_iff₀ hd]
      calc c₀ * ‖u(χ, j0) - u(χ, c j0)‖ ≤ c₀ * (2 * |z.val.2.2 - (w z).val.2.2| ^ β * K) :=
            mul_le_mul_of_nonneg_left hdist hc₀.le
        _ ≤ (2 * K + 1) * ‖u(χ, j0)‖ * |z.val.2.2 - (w z).val.2.2| ^ β := by
            nlinarith [mul_nonneg hc₀.le hd.le, mul_le_mul_of_nonneg_right hu hd.le]
  have hsingle : ‖u(χ, j0)‖ / ‖u(χ, j0) - u(χ, c j0)‖ ≤ ∑ m : Fin (N(χ, α, s, z)),
      ‖u(χ, (jet(z, m) : J(χ)))‖ / ‖u(χ, (jet(z, m) : J(χ))) - u(χ, c (jet(z, m) : J(χ)))‖ :=
    Finset.single_le_sum (f := fun m : Fin (N(χ, α, s, z)) ↦
      ‖u(χ, (jet(z, m) : J(χ)))‖ / ‖u(χ, (jet(z, m) : J(χ))) - u(χ, c (jet(z, m) : J(χ)))‖)
      (fun m _ ↦ div_nonneg (norm_nonneg _) (norm_nonneg _))
      (Finset.mem_univ (⟨0, hN z⟩ : Fin (N(χ, α, s, z))))
  calc M z * (|z.val.2.2 - (w z).val.2.2| ^ β)⁻¹
      ≤ M z * ((2 * K + 1) / c₀ * (‖u(χ, j0)‖ / ‖u(χ, j0) - u(χ, c j0)‖)) :=
        mul_le_mul_of_nonneg_left hterm (hM z)
    _ ≤ M z * ((2 * K + 1) / c₀ * ∑ m : Fin (N(χ, α, s, z)),
          ‖u(χ, (jet(z, m) : J(χ)))‖ / ‖u(χ, (jet(z, m) : J(χ))) - u(χ, c (jet(z, m) : J(χ)))‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsingle
          (div_nonneg (by linarith) hc₀.le)) (hM z)
    _ = (2 * K + 1) / c₀ * (M z * ∑ m : Fin (N(χ, α, s, z)),
          ‖u(χ, (jet(z, m) : J(χ)))‖ /
            ‖u(χ, (jet(z, m) : J(χ))) - u(χ, c (jet(z, m) : J(χ)))‖) := by
        ring

end LineHolder

section GramSpacing

/-- The completed `L`-function of a unitary character has finite order at every point.
This repeats the private `spectralStripComponent_finite_window_order_ne_top` of
`Sec3_Clusters`. -/
private theorem gramSpacing_order_ne_top (ψ : PontryaginDual C𝔽) (z : ℂ) : order(ψ, z) ≠ ⊤ := by
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec ψ
  have h2 : order(ψ, (2 : ℂ)) ≠ ⊤ := fun htop ↦ by
    have hbad := completedHeckeL_continuation_zeros ψ _ hΛ hval (by norm_num : 0 < (2 : ℂ).re)
      (by rw [htop]; exact WithTop.coe_lt_top 0)
    norm_num at hbad
  exact hΛ.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ z) h2

include hs in
/-- At width zero every zero keeps its jet of order zero. -/
private theorem gramSpacing_N_pos (hα0 : α = 0) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (z : Z(χ, α)) : 0 < N(χ, α, s, z) := by
  have hz0 : z.val.2.1 = 0 := by
    have := z.property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hord := z.property.2
  have hne := gramSpacing_order_ne_top (χ z.val.1) (shift(a + z.val.2.1, z.val.2.2))
  have hmult : 0 < mult(χ z.val.1, shift(a + z.val.2.1, z.val.2.2)) := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hn] at hord ⊢
    simp only [WithTop.untop₀_coe]
    exact Int.lt_toNat.mpr (by exact_mod_cast hord)
  rw [spectralStripMultiplicity_boundary (le_of_eq hα0.symm) (Or.inr (hz0.trans hα0.symm)) s]
  unfold spectralBoundaryMultiplicity
  refine lt_min hmult (Nat.ceil_pos.mpr (by linarith))

/-- One test and two zeros: the finite Gram bound of `spectralStripConvolution_finiteGram_bound`
for one test, applied to the block of the two zeroth jets, bounds the Mellin transform of the
test on the circle around the first zero by a constant times the `β`-th power of the distance
between the ordinates. -/
private theorem gramSpacing_pair (hα0 : α = 0) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (φ : BruhatCompactSupport C𝔽)
    (hgap : ∃ B : ℝ, ∀ (T : Finset (Z(χ, α))) (w : Z(χ, α) → ℂ) (S : Finset (J(χ))),
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2))
        (2 * Real.exp ((4 * α + s) / 2))) →
      ∑ z ∈ T, ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (w z) g ∂μ𝔽‖ *
        ∑ m : Fin (N(χ, α, s, z)), ‖u(χ, (jet(z, m) : J(χ)))‖ *
          finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) (jet(z, m) : J(χ)) S ≤ B)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβs : 2 * β < s - 1) :
    ∃ C ≥ (0 : ℝ), ∀ z w : Z(χ, α), w ≠ z → w.val.1 = z.val.1 →
      ∀ w' ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2)) (2 * Real.exp ((4 * α + s) / 2)),
        ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w' g ∂μ𝔽‖ ≤
          C * |z.val.2.2 - w.val.2.2| ^ β := by
  classical
  obtain ⟨B, hB⟩ := hgap
  obtain ⟨c₀, hc₀, hlow⟩ := spectralStripJet_lowerBound χ hχ (a := a) hα hs
  have hind := spectralStripJet_toLp_linearIndependent χ hχ a hα hs₀(hs)
  let K := (eLpNorm (fun g : C𝔽 ↦ (1 + logIdeleClassNorm F g ^ 2) ^ (β / 2)) 2
    (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true)).toReal
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := by simpa using hB ∅ (fun _ ↦ 0) ∅ (by simp)
  refine ⟨2 * K * B / c₀, by positivity, fun z w hwz hχzw w' hw' ↦ ?_⟩
  let jz : J(χ) := jet(z, (⟨0, gramSpacing_N_pos a hs hα0 χ z⟩ : Fin (N(χ, α, s, z))))
  let jw : J(χ) := jet(w, (⟨0, gramSpacing_N_pos a hs hα0 χ w⟩ : Fin (N(χ, α, s, w))))
  have hz0 : z.val.2.1 = 0 := by
    have := z.property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hw0 : w.val.2.1 = 0 := by
    have := w.property.1; simp only [mem_Icc] at this; subst hα0; linarith
  have hjne : jw ≠ jz := by
    intro h
    apply hwz
    apply Subtype.ext
    have h1 := congrArg (fun i : J(χ) ↦ i.val.1) h
    have h2 := congrArg (fun i : J(χ) ↦ i.val.2.1) h
    have h3 := congrArg (fun i : J(χ) ↦ i.val.2.2.1) h
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hdist : ‖u(χ, jz) - u(χ, jw)‖ ≤ 2 * |z.val.2.2 - w.val.2.2| ^ β * K :=
    lineHolder_jet_dist_le a hα hs hα0 χ hβ0 hβ1 hβs jz jw hχzw hz0 hw0 rfl rfl
  have hpos : 0 < ‖u(χ, jz) - u(χ, jw)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hjne (hind.injective h).symm)
  -- The Gram coordinate of the zeroth jet at `z` in the block `{jz, jw}`.
  have hcoord : 1 / ‖u(χ, jz) - u(χ, jw)‖ ≤
      finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) jz {jz, jw} := by
    have hg := (finiteGramCoordinate_isGreatest hind jz {jz, jw}).2
    refine hg ⟨Finsupp.single jz 1 - Finsupp.single jw 1, ?_, ?_⟩
    · intro k hk
      have := Finsupp.support_sub hk
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h)))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (Finset.mem_singleton.mp (Finsupp.support_single_subset h))))
    · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hjne.symm, sub_zero, norm_one, map_sub,
        Finsupp.linearCombination_single, one_smul]
  have hsum := hB {z} (fun _ ↦ w') {jz, jw} (by simpa using hw')
  rw [Finset.sum_singleton] at hsum
  have hterm : ‖u(χ, jz)‖ * finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) jz {jz, jw} ≤
      ∑ m : Fin (N(χ, α, s, z)), ‖u(χ, (jet(z, m) : J(χ)))‖ *
        finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) (jet(z, m) : J(χ)) {jz, jw} :=
    Finset.single_le_sum (f := fun m : Fin (N(χ, α, s, z)) ↦ ‖u(χ, (jet(z, m) : J(χ)))‖ *
        finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) (jet(z, m) : J(χ)) {jz, jw})
      (fun m _ ↦ mul_nonneg (norm_nonneg _) (finiteGramCoordinate_nonneg _ _ _))
      (Finset.mem_univ _)
  have hlowz : c₀ ≤ ‖u(χ, jz)‖ := hlow jz
  have hv0 : 0 ≤ ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w' g ∂μ𝔽‖ := norm_nonneg _
  have hquot : c₀ / ‖u(χ, jz) - u(χ, jw)‖ ≤ ∑ m : Fin (N(χ, α, s, z)), ‖u(χ, (jet(z, m) : J(χ)))‖ *
        finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) (jet(z, m) : J(χ)) {jz, jw} := by
    calc c₀ / ‖u(χ, jz) - u(χ, jw)‖ = c₀ * (1 / ‖u(χ, jz) - u(χ, jw)‖) := by ring
      _ ≤ ‖u(χ, jz)‖ * finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) jz {jz, jw} :=
          mul_le_mul hlowz hcoord (by positivity) (norm_nonneg _)
      _ ≤ _ := hterm
  have h1 := (mul_le_mul_of_nonneg_left hquot hv0).trans hsum
  rw [← mul_div_assoc, div_le_iff₀ hpos] at h1
  have h3 := h1.trans (mul_le_mul_of_nonneg_left hdist hB0)
  rw [show 2 * K * B / c₀ * |z.val.2.2 - w.val.2.2| ^ β =
    B * (2 * |z.val.2.2 - w.val.2.2| ^ β * K) / c₀ by ring]
  exact (le_div_iff₀ hc₀).mpr h3

local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽

local instance gramSpacingCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- The logarithm of the idele class norm is a proper map. -/
private theorem gramSpacing_logNorm_proper : IsProperMap (logIdeleClassNorm F) := by
  have hpos (x : C𝔽) : 0 < ((m𝔽 x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m𝔽 x))
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he : (e ∘ m𝔽) = logIdeleClassNorm F :=
    funext fun g ↦ (Real.log_of_pos (hpos g)).symm
  exact he ▸ e.isProperMap.comp (hm𝔽).1

/-- A smooth compactly supported profile of the logarithm of the norm, times the conjugate of a
unitary character, is a compactly supported Bruhat test. -/
private theorem gramSpacing_exists_test (η : PontryaginDual C𝔽) (r : ℝ → ℂ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) (hc : HasCompactSupport r) :
    ∃ φ : BruhatCompactSupport C𝔽, ∀ g, φ.val g = r (logIdeleClassNorm F g) * star (η g : ℂ) := by
  let c : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η⁻¹
  have hcg (g : C𝔽) : c g = star (η g : ℂ) := by
    change ((η⁻¹ g : Circle) : ℂ) = _
    rw [show η⁻¹ g = (η g)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    rfl
  let f : C𝔽 → ℂ := fun g ↦ r (logIdeleClassNorm F g) * star (η g : ℂ)
  have hlog : IsBruhatSmooth (fun x : C𝔽 ↦ (r (Real.log ((m𝔽 x).val : ℝ)) : ℂ)) :=
    isBruhatSmooth_logProfile m𝔽 hr
  have hchar : IsBruhatSmooth (fun x : C𝔽 ↦ c x) :=
    (mem_bruhatSmoothSubmodule_iff _).mp (quasiCharacter_mem_bruhatSmooth c)
  have hsmooth : IsBruhatSmooth f := by
    intro p
    have := isBruhatContDiff_mul (hlog p) (hchar p)
    convert this using 1
    funext g
    simp only [Pi.mul_apply, f, hcg]
    rfl
  have hsupp : HasCompactSupport f := by
    refine HasCompactSupport.intro ((gramSpacing_logNorm_proper (F := F)).isCompact_preimage hc) ?_
    intro g hg
    simp only [f, mem_preimage] at hg ⊢
    rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]
  exact ⟨⟨f, (mem_bruhatSmoothSubmodule_iff f).mpr hsmooth, hsupp⟩, fun _ ↦ rfl⟩

/-- The Mellin integral of the test of `gramSpacing_exists_test` against the twist of the same
character is a Laplace integral of the profile. -/
private theorem gramSpacing_mellin (η : PontryaginDual C𝔽) (r : ℝ → ℂ) (hr : Continuous r)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g, φ.val g = r (logIdeleClassNorm F g) * star (η g : ℂ)) (w : ℂ) :
    ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) η w g ∂μ𝔽 =
      (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℂ) * ∫ x : ℝ, r x * Complex.exp (w * x) := by
  let G : ℝ → ℂ := fun x ↦ r x * Complex.exp (w * x)
  have hpt (g : C𝔽) : φ.val g * ideleClassNormTwist (F := F) η w g = G (logIdeleClassNorm F g) := by
    have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have htw : (ideleClassNormTwist (F := F) η w g : ℂ) =
        (η g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ w := rfl
    have hη : star (η g : ℂ) * (η g : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]; norm_num
    rw [hφ, htw, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ← Complex.ofReal_log hp.le]
    change r _ * star (η g : ℂ) * ((η g : ℂ) * Complex.exp (_ * w)) = r _ * Complex.exp (w * _)
    rw [show r (logIdeleClassNorm F g) * star (η g : ℂ) * ((η g : ℂ) *
        Complex.exp (((Real.log ((ideleClassNorm F g).val : ℝ) : ℝ) : ℂ) * w)) =
        r (logIdeleClassNorm F g) * (star (η g : ℂ) * (η g : ℂ)) *
        Complex.exp (((Real.log ((ideleClassNorm F g).val : ℝ) : ℝ) : ℂ) * w) by ring, hη,
      mul_one, mul_comm _ w]
  have hG : Continuous G := hr.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))
  simp_rw [hpt]
  have hL := lineHolder_log_preserving (F := F)
  rw [← integral_map hL.measurable.aemeasurable hG.aestronglyMeasurable, hL.map_eq,
    integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- The common end of the two spacing theorems below. Suppose that, for every test, one constant
bounds the Mellin transform at the point `shift(0, Im z) + r` attached to a zero `z` by that
constant times `|Im z - Im w| ^ β`, for every other zero `w` of the same component. Then the
zeros of each component are separated polynomially in the height. The proof uses the tests
`θ(log |g|) ψ(log |g|) · conj (χ ω g)` for `ψ` in the Schwartz space of the line, whose Mellin
transforms are Laplace integrals of `θ ψ`, the Banach–Steinhaus theorem on that Schwartz space,
and the modulated tests `θ(x) e^{-itx}`, whose Schwartz seminorms grow polynomially in `t`. -/
private theorem gramSpacing_of_holder (hα0 : α = 0) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (ω : PontryaginDual C₁) {β : ℝ} (hβpos : 0 < β) (R : ℝ)
    (H : ∀ φ : BruhatCompactSupport C𝔽, ∃ C : ℝ, ∀ z w : Z(χ, α), w ≠ z → w.val.1 = z.val.1 →
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2) + R) g
        ∂μ𝔽‖ ≤ C * |z.val.2.2 - w.val.2.2| ^ β) :
    ∃ c > (0 : ℝ), ∃ A : ℝ, ∀ z w : Z(χ, α), z.val.1 = ω → w ≠ z → w.val.1 = z.val.1 →
      c * (1 + |z.val.2.2|) ^ (-A) ≤ |z.val.2.2 - w.val.2.2| := by
  classical
  -- The cut-off and the profile.
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let θ : ℝ → ℂ := fun x ↦ ((b x : ℝ) : ℂ)
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hθc : HasCompactSupport θ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hθcont : Continuous θ := hθs.continuous
  let η := χ ω
  let cH : ℝ := Measure.haarScalarFactor μ𝔽 ν𝔽
  have hcH : 0 < cH := NNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _)
  -- For every Schwartz profile, the test and its bound.
  have htest (ψ : 𝓢(ℝ, ℂ)) := gramSpacing_exists_test η (fun x ↦ θ x * ψ x)
    (hθs.mul (ψ.smooth ⊤)) (hθc.mul_right)
  choose φ hφ using htest
  choose Cψ hCψ using fun ψ ↦ H (φ ψ)
  -- The family of functionals.
  let I := {p : Z(χ, α) × Z(χ, α) // p.1.val.1 = ω ∧ p.2 ≠ p.1 ∧ p.2.val.1 = p.1.val.1}
  let pt (i : I) : ℂ := shift(i.val.1.val.2.1, i.val.1.val.2.2) + R
  let g (i : I) : ℝ → ℂ := fun x ↦ θ x * Complex.exp (pt i * x)
  have hg (i : I) : Integrable (g i) :=
    (hθcont.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
      ).integrable_of_hasCompactSupport hθc.mul_right
  let Δ (i : I) : ℝ := |i.val.1.val.2.2 - i.val.2.val.2.2| ^ β
  have hΔ (i : I) : 0 < Δ i := by
    refine Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr fun h ↦ i.property.2.1 ?_)) _
    have hz0 : i.val.1.val.2.1 = 0 := by
      have := i.val.1.property.1; simp only [mem_Icc] at this; subst hα0; linarith
    have hw0 : i.val.2.val.2.1 = 0 := by
      have := i.val.2.property.1; simp only [mem_Icc] at this; subst hα0; linarith
    exact Subtype.ext (Prod.ext i.property.2.2 (Prod.ext (hw0.trans hz0.symm) h.symm))
  let L (i : I) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := ((cH / Δ i : ℝ) : ℂ) • schwartzPairing (g i) (hg i)
  have hLapp (i : I) (ψ : 𝓢(ℝ, ℂ)) : L i ψ = ((cH / Δ i : ℝ) : ℂ) *
      ∫ x, θ x * ψ x * Complex.exp (pt i * x) := by
    change ((cH / Δ i : ℝ) : ℂ) • schwartzPairing (g i) (hg i) ψ = _
    rw [schwartzPairing_apply, smul_eq_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [g]
    ring
  have hbound (i : I) (ψ : 𝓢(ℝ, ℂ)) : ‖L i ψ‖ ≤ Cψ ψ := by
    have hm := gramSpacing_mellin η (fun x ↦ θ x * ψ x) (hθcont.mul ψ.continuous) (φ ψ) (hφ ψ)
      (pt i)
    have hc := hCψ ψ i.val.1 i.val.2 i.property.2.1 i.property.2.2
    rw [show χ i.val.1.val.1 = η from congrArg χ i.property.1, hm] at hc
    rw [hLapp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hcH.le (hΔ i).le)]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcH.le] at hc
    rw [div_mul_eq_mul_div, div_le_iff₀ (hΔ i)]
    exact hc
  obtain ⟨C, n, hC0, hCL⟩ := schwartz_uniform_bound_modulated L Cψ hbound θ hθs hθc
  -- The value at the matching frequency.
  let I₀ : ℝ := ∫ x, b x * b x * Real.exp (R * x)
  have hI₀ : 0 < I₀ := by
    have hcont : Continuous fun x : ℝ ↦ b x * b x * Real.exp (R * x) :=
      (b.continuous.mul b.continuous).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    refine hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (b.hasCompactSupport.mul_right.mul_right)
      (fun x ↦ mul_nonneg (mul_nonneg b.nonneg b.nonneg) (Real.exp_pos _).le) (x := 0) ?_
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    simp
  refine ⟨(cH * I₀ / (C + 1)) ^ β⁻¹, by positivity, n / β, fun z w hzω hwz hχzw ↦ ?_⟩
  let i : I := ⟨(z, w), hzω, hwz, hχzw⟩
  have hval : L i (modulatedSchwartz θ hθs hθc z.val.2.2) = ((cH / Δ i : ℝ) : ℂ) * (I₀ : ℂ) := by
    rw [hLapp]
    congr 1
    rw [show (I₀ : ℂ) = ∫ x : ℝ, ((b x * b x * Real.exp (R * x) : ℝ) : ℂ) from integral_ofReal.symm]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [modulatedSchwartz_apply, θ, pt, i]
    have hz0 : z.val.2.1 = 0 := by
      have := z.property.1; simp only [mem_Icc] at this; subst hα0; linarith
    rw [hz0]
    push_cast
    rw [mul_assoc, mul_assoc, ← Complex.exp_add]
    have : -(z.val.2.2 : ℂ) * Complex.I * x + ((0 : ℂ) + z.val.2.2 * Complex.I + R) * x =
        ((R * x : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    push_cast
    ring
  have hle := hCL i z.val.2.2
  rw [hval, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg hcH.le (hΔ i).le), Real.norm_of_nonneg hI₀.le] at hle
  have h1t : 0 < 1 + |z.val.2.2| := by positivity
  -- `cH I₀ / (C + 1) · (1 + |t|) ^ (-n) ≤ |Δ| ^ β`.
  have hkey : cH * I₀ / (C + 1) * (1 + |z.val.2.2|) ^ (-(n : ℝ)) ≤ Δ i := by
    rw [Real.rpow_neg h1t.le, Real.rpow_natCast, ← div_eq_mul_inv, div_div,
      div_le_iff₀ (by positivity)]
    have : cH / Δ i * I₀ ≤ (C + 1) * (1 + |z.val.2.2|) ^ n :=
      hle.trans (by gcongr; linarith)
    rw [div_mul_eq_mul_div, div_le_iff₀ (hΔ i)] at this
    linarith
  have hd : |z.val.2.2 - w.val.2.2| = (Δ i) ^ β⁻¹ :=
    (Real.rpow_rpow_inv (abs_nonneg _) hβpos.ne').symm
  rw [hd, show -(n / β) = -(n : ℝ) * β⁻¹ by ring, Real.rpow_mul h1t.le, ← Real.mul_rpow
    (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) hkey (by positivity)


/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. What the recorded gap
`spectralStripConvolution_finiteGram_bound` (#7455), assumed for every test, forces at width
zero: the zeros of each component are separated polynomially in the height. For each norm-one
character `ω` there are `c > 0` and `A` such that any two distinct zeros `z, w` of `χ ω` on the
line satisfy `|Im z - Im w| ≥ c (1 + |Im z|) ^ (-A)`.
The hypothesis is the statement of `spectralStripConvolution_finiteGram_bound` for every test,
with its `let`s unfolded. The proof applies the finite Gram bound to the block of two zeroth jets
(`gramSpacing_pair`), tests of the form `ψ(log |g|) · conj (χ ω g)` whose Mellin transforms are
Laplace integrals of `ψ`, the Banach–Steinhaus theorem on the Schwartz space of the line, and the
modulated tests `ρ(x) e^{-itx}`, whose Schwartz seminorms grow polynomially in `t`. Over `ℚ`,
at `a = 1/2` and on the component of the trivial character, the conclusion is a lower bound,
polynomial in the height, for the gaps between the ordinates of zeros of the Riemann zeta
function on the critical line. No such bound is known to us, unconditionally or on the Riemann
hypothesis. The bound is for one component at a time, with no uniformity in `ω`. -/
theorem spectralStripConvolution_finiteGram_bound_forces_polynomial_gaps (hα0 : α = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hgap : ∀ φ : BruhatCompactSupport C𝔽, ∃ B : ℝ, ∀ (T : Finset (Z(χ, α))) (w : Z(χ, α) → ℂ)
      (S : Finset (J(χ))),
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.2.1, z.val.2.2))
        (2 * Real.exp ((4 * α + s) / 2))) →
      ∑ z ∈ T, ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (w z) g ∂μ𝔽‖ *
        ∑ m : Fin (N(χ, α, s, z)), ‖u(χ, (jet(z, m) : J(χ)))‖ *
          finiteGramCoordinate (fun j : J(χ) ↦ u(χ, j)) (jet(z, m) : J(χ)) S ≤ B)
    (ω : PontryaginDual C₁) :
    ∃ c > (0 : ℝ), ∃ A : ℝ, ∀ z w : Z(χ, α), z.val.1 = ω → w ≠ z → w.val.1 = z.val.1 →
      c * (1 + |z.val.2.2|) ^ (-A) ≤ |z.val.2.2 - w.val.2.2| := by
  let β : ℝ := min 1 ((s - 1) / 4)
  have hβpos : 0 < β := lt_min one_pos (by linarith)
  have hβs : 2 * β < s - 1 := by
    have : β ≤ (s - 1) / 4 := min_le_right _ _
    linarith
  let R : ℝ := 2 * Real.exp ((4 * α + s) / 2)
  have hR : 0 < R := by positivity
  refine gramSpacing_of_holder a hα0 χ ω hβpos R fun φ ↦ ?_
  obtain ⟨C, -, hC⟩ := gramSpacing_pair a hα hs hα0 χ hχ φ (hgap φ) hβpos.le (min_le_left _ _) hβs
  refine ⟨C, fun z w hwz hχzw ↦ hC z w hwz hχzw _ ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
    Real.norm_of_nonneg hR.le]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. What the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241), assumed for every
test, forces at width zero: the zeros of each component are separated polynomially in the
height. For each norm-one character `ω` there are `c > 0` and `A` such that any two distinct
zeros `z, w` of `χ ω` on the line satisfy `|Im z - Im w| ≥ c (1 + |Im z|) ^ (-A)`.
The hypothesis `h` is the conclusion of that gap for every test, for the given basis, as in
`spectralStripConvolution_compact_block_series_forces_line_holder`, which gives the bound at one
test. The rest is as for `spectralStripConvolution_finiteGram_bound_forces_polynomial_gaps`, with
the Mellin transform taken at the centres of the circles instead of on them. Over `ℚ`, at
`a = 1/2` and on the component of the trivial character, the conclusion is a lower bound,
polynomial in the height, for the gaps between the ordinates of zeros of the Riemann zeta
function on the critical line. No such bound is known to us, unconditionally or on the Riemann
hypothesis. The bound is for one component at a time, with no uniformity in `ω`. -/
theorem spectralStripConvolution_compact_block_series_forces_polynomial_gaps (hα0 : α = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (h : ∀ φ : BruhatCompactSupport C𝔽,
      ∀ U : compactOperator (RingHom.id ℂ) Q(a, hStrip(hα), hs₀(hs)) Q(a, hStrip(hα), hs₀(hs)),
      Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
        (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ (U.val (x (jet(z, m)))))))
    (ω : PontryaginDual C₁) :
    ∃ c > (0 : ℝ), ∃ A : ℝ, ∀ z w : Z(χ, α), z.val.1 = ω → w ≠ z → w.val.1 = z.val.1 →
      c * (1 + |z.val.2.2|) ^ (-A) ≤ |z.val.2.2 - w.val.2.2| := by
  let β : ℝ := min 1 ((s - 1) / 4)
  have hβpos : 0 < β := lt_min one_pos (by linarith)
  have hβs : 2 * β < s - 1 := by
    have : β ≤ (s - 1) / 4 := min_le_right _ _
    linarith
  refine gramSpacing_of_holder a hα0 χ ω hβpos 0 fun φ ↦ ?_
  obtain ⟨C, -, hC⟩ := spectralStripConvolution_compact_block_series_forces_line_holder a hα hs
    hα0 χ hχ x Λ hb hj φ (h φ) hβpos.le (min_le_left _ _) hβs
  refine ⟨C, fun z w hwz hχzw ↦ ?_⟩
  have hM := hC z w hwz hχzw (gramSpacing_N_pos a hs hα0 χ z) (gramSpacing_N_pos a hs hα0 χ w)
  simpa only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ,
    Complex.ofReal_zero, add_zero] using hM

end GramSpacing

end Majorant

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The statement of the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241), word for word,
proved from the majorant `spectralStripConvolution_summable_jetNorms`. -/
theorem spectralStripConvolution_traceCauchy_compact_block_series_of_summable_jetNorms
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let jet (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) :
        SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
      ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
    ∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z : Z(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m))))) := by
  intro H A jet U
  obtain ⟨M, hM, hMellin, hsum⟩ :=
    spectralStripConvolution_summable_jetNorms a hα hs χ _hχ φ x Λ _hb _hj
  exact spectralStripConvolution_block_series_of_summable_jetNorms a hα hs χ x Λ _hj φ M hM hMellin
    hsum U.val

/-- A real family whose finite partial sums are bounded in absolute value is summable. -/
private theorem spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_real
    {Z : Type*} (h : Z → ℝ) (C : ℝ) (hb : ∀ K : Finset Z, |∑ z ∈ K, h z| ≤ C) :
    Summable h := by
  classical
  refine Summable.of_abs (summable_of_sum_le (c := C + C) (fun z ↦ abs_nonneg (h z)) fun K ↦ ?_)
  have hsplit : ∑ z ∈ K, |h z| =
      ∑ z ∈ K.filter (fun z ↦ 0 ≤ h z), h z - ∑ z ∈ K.filter (fun z ↦ ¬ 0 ≤ h z), h z := by
    rw [← Finset.sum_filter_add_sum_filter_not K (fun z ↦ 0 ≤ h z) (fun z ↦ |h z|)]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun z hz ↦ abs_of_nonneg (Finset.mem_filter.mp hz).2
    · exact Finset.sum_congr rfl fun z hz ↦ abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hz).2)
  rw [hsplit]
  have h1 := (abs_le.mp (hb (K.filter (fun z ↦ 0 ≤ h z)))).2
  have h2 := (abs_le.mp (hb (K.filter (fun z ↦ ¬ 0 ≤ h z)))).1
  linarith

/-- A complex family whose finite partial sums are bounded in norm is summable. -/
private theorem spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_complex
    {Z : Type*} (g : Z → ℂ) (C : ℝ) (hb : ∀ K : Finset Z, ‖∑ z ∈ K, g z‖ ≤ C) :
    Summable g := by
  have hre := spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_real
    (fun z ↦ (g z).re) C fun K ↦ by
      rw [← Complex.re_sum]
      exact (Complex.abs_re_le_norm _).trans (hb K)
  have him := spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_real
    (fun z ↦ (g z).im) C fun K ↦ by
      rw [← Complex.im_sum]
      exact (Complex.abs_im_le_norm _).trans (hb K)
  exact ((Complex.hasSum_iff g ⟨∑' z, (g z).re, ∑' z, (g z).im⟩).mpr
    ⟨hre.hasSum, him.hasSum⟩).summable

/-- Bounded trace norms of the finite block sums give summable block traces after inserting
any bounded operator: the trace of the inserted finite sum is at most the norm of the operator
times the trace norm. -/
private theorem spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_abstract
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) (R : Z → nuclearEndomorphisms H)
    (hR : ∀ K : Finset Z, (∑ z ∈ K, R z).val = spectralConvolutionFiniteSum A x Λ K N jet)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z)))
    (U : H →L[ℂ] H) :
    Summable (fun z ↦ ∑ m : Fin (N z), Λ (jet z m) (A (U (x (jet z m))))) := by
  classical
  obtain ⟨c, hc⟩ := hbound
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  let term (j : J) (y : H) : nuclearEndomorphisms H :=
    ⟨((Λ j).comp A).smulRight y, smulRight_mem_nuclearEndomorphisms _ _⟩
  refine spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_complex _ (‖U‖ * c)
    fun K ↦ ?_
  let T := ∑ z ∈ K, R z
  let D : nuclearEndomorphisms H := ⟨U * T.val, mul_mem_nuclearEndomorphisms_left U T⟩
  have heq : D = ∑ z ∈ K, ∑ m, term (jet z m) (U (x (jet z m))) := by
    apply Subtype.ext
    ext v
    change U (T.val v) = _
    rw [show T.val = spectralConvolutionFiniteSum A x Λ K N jet from hR K]
    simp only [spectralConvolutionFiniteSum, term, Submodule.coe_sum,
      sum_apply, ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  have htrace : hilbertTrace D = ∑ z ∈ K, ∑ m : Fin (N z), Λ (jet z m) (A (U (x (jet z m)))) := by
    rw [← htr, heq, map_sum]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [htr]
    exact hilbertTrace_smulRight _ _
  rw [← htrace]
  refine (norm_hilbertTrace_le D).trans ((traceNorm_mul_left_le U T).trans ?_)
  exact mul_le_mul_of_nonneg_left (hc ⟨K, rfl⟩) (norm_nonneg U)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The statement of the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241), for every bounded
insertion, follows from a bound for the trace norms of the finite sums of the zero blocks. That
bound is all that `spectralStripConvolution_traceCauchy` uses: in `Sec3` the gap is consumed only
through the private `spectralStripConvolution_traceCauchy_scalar_bound`, which derives this bound
from the gap. With this theorem the two are equivalent, so the gap cannot be weakened by testing
fewer insertions without changing what the rectangles of (10.3.2.1) are asked to do. -/
theorem spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (R : Z(χ, α) → nuclearEndomorphisms Q(a, hStrip(hα), hs₀(hs)))
    (hR : ∀ K : Finset Z(χ, α), (∑ z ∈ K, R z).val =
      spectralConvolutionFiniteSum (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) x Λ K
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩))
    (hbound : BddAbove (range fun K : Finset Z(χ, α) ↦ traceNorm (∑ z ∈ K, R z)))
    (U : Q(a, hStrip(hα), hs₀(hs)) →L[ℂ] Q(a, hStrip(hα), hs₀(hs))) :
    Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)),
      Λ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
        (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
          (U (x ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)))) :=
  spectralStripConvolution_compact_block_series_of_traceNorm_bddAbove_abstract _ x Λ _ _ R hR
    hbound U

end RiemannMasullo.Isolated
