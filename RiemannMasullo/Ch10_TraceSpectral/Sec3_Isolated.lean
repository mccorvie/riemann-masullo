module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The block series of Theorem 10.3.2.1(1): a sufficient majorant and a necessary separation

The recorded gap `spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241)
says that, after inserting any fixed compact operator, the traces of the zero blocks of the
spectral convolution are summable. This file proves it from one smaller statement, a summable
majorant built from the scalar Mellin transform of the test and the norms of the coordinate
functionals and their biorthogonal vectors, and shows what the gap forces: one constant must
bound the Mellin value at every zero times its zeroth jet, relative to the distance of that jet
from the zeroth jet at any other zero. The second statement is where the spacing of the zeros of
the Hecke `L`-functions enters. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

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
Gap: No bound for the biorthogonal vectors of the zero jets is known when zeros cluster. At
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
  sorry

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
