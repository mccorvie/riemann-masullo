module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Isolated statements of §12.5

Statements of the section that are neither proved nor refuted and that nothing else in Lean
uses, with what follows from them (`AGENTS.md`, "False statements and gaps"). Nothing imports
this file.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.

## The one-sided width comparison for Theorem 12.5.1.1

For one test per character and candidate edge, the signed closed-strip sum detects
boundary zeros by a downward jump when the real Mellin moments on the edge are positive.
The two hypotheses of `traceFormula_exteriorZeros_of_signedWidthComparison` specify
this positivity and the one-sided comparison that excludes the jump.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo.Isolated

section WidthJump

open Filter
open scoped Topology

private theorem widthJump_le (a s x : ℝ) (n : ℕ) :
    spectralStripMultiplicity a s x n ≤ n := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

private theorem widthJump_outside {a x : ℝ} (ha : 0 ≤ a) (h : a < |x|) (s : ℝ) (n : ℕ) :
    spectralStripMultiplicity a s x n = 0 := by
  rw [spectralStripMultiplicity, ite_eq_right (by simpa only [← abs_lt] using h.not_gt)]
  rw [ite_eq_right]
  rintro (hx | hx) <;> simp [hx, abs_of_nonneg ha] at h

private theorem widthJump_interior_summable {ι : Type*} (x v : ι → ℝ) (m : ι → ℕ)
    (h : Summable (fun i ↦ (m i : ℝ) * |v i|)) (b : ℝ) :
    Summable (fun i ↦ if |x i| < b then (m i : ℝ) * v i else 0) := by
  apply h.of_norm_bounded
  intro i
  split_ifs
  · simp
  · simpa using mul_nonneg (Nat.cast_nonneg (m i)) (abs_nonneg (v i))

private theorem widthJump_boundary_summable {ι : Type*} (x v : ι → ℝ) (m : ι → ℕ)
    (h : Summable (fun i ↦ (m i : ℝ) * |v i|)) (b s : ℝ) :
    Summable (fun i ↦ if |x i| = b then (spectralBoundaryMultiplicity s (m i) : ℝ) * v i else 0) := by
  apply h.of_norm_bounded
  intro i
  split_ifs
  · simp only [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact_mod_cast (min_le_left _ _ : spectralBoundaryMultiplicity s (m i) ≤ m i)
  · simpa using mul_nonneg (Nat.cast_nonneg (m i)) (abs_nonneg (v i))

/-- As the strip width increases to a positive value from below, its real trace tends to
the full-order open-strip sum. The real moments can have either sign. The bound is on
the sum of the absolute values with the full multiplicities. -/
theorem tendsto_signedStripTrace_left {ι : Type*} (x v : ι → ℝ) (m : ι → ℕ)
    (h : Summable (fun i ↦ (m i : ℝ) * |v i|)) {b : ℝ} (hb : 0 < b) (s : ℝ) :
    Tendsto (fun a : ℝ ↦ -(∑' i, (spectralStripMultiplicity a s (x i) (m i) : ℝ) * v i))
      (𝓝[<] b) (𝓝 (-(∑' i, if |x i| < b then (m i : ℝ) * v i else 0))) := by
  apply Tendsto.neg
  apply tendsto_tsum_of_dominated_convergence h
  · intro i
    by_cases hi : |x i| < b
    · rw [ite_eq_left hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hi)] with a ha
      rw [spectralStripMultiplicity_interior (abs_lt.mp ha)]
    · rw [ite_eq_right hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [show ∀ᶠ a in 𝓝[<] b, a < b from self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_gt_nhds hb)] with a hab ha
      rw [widthJump_outside ha.le (hab.trans_le (le_of_not_gt hi)), Nat.cast_zero, zero_mul]
  · exact Eventually.of_forall fun a i ↦ by
      simp only [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast widthJump_le a s (x i) (m i))
        (abs_nonneg _)

/-- The real part of the signed closed-strip trace has a strictly downward jump from the
left exactly when the boundary contains an index, assuming its real moments there are positive.
Both endpoints use the actual Sobolev cap of (10.2.2.5). -/
theorem signedStripTrace_left_jump_iff {ι : Type*} (x v : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (h : Summable (fun i ↦ (m i : ℝ) * |v i|))
    {b s : ℝ} (hb : 0 < b) (hs : 1 < s) (hv : ∀ i, |x i| = b → 0 < v i) :
    (-(∑' i, (spectralStripMultiplicity b s (x i) (m i) : ℝ) * v i)) <
      -(∑' i, if |x i| < b then (m i : ℝ) * v i else 0) ↔ ∃ i, |x i| = b := by
  let I (i : ι) : ℝ := if |x i| < b then (m i : ℝ) * v i else 0
  let E (i : ι) : ℝ := if |x i| = b then (spectralBoundaryMultiplicity s (m i) : ℝ) * v i else 0
  have hI : Summable I := widthJump_interior_summable x v m h b
  have hE : Summable E := widthJump_boundary_summable x v m h b s
  have hsplit (i : ι) : (spectralStripMultiplicity b s (x i) (m i) : ℝ) * v i = I i + E i := by
    rcases lt_trichotomy |x i| b with hi | hi | hi
    · simp only [I, E, ite_eq_left hi, ite_eq_right hi.ne, add_zero,
        spectralStripMultiplicity_interior (abs_lt.mp hi)]
    · have hside : x i = -b ∨ x i = b := by
        rcases le_total 0 (x i) with hxi | hxi
        · exact Or.inr (by simpa [abs_of_nonneg hxi] using hi)
        · exact Or.inl (by rw [abs_of_nonpos hxi] at hi; linarith)
      simp only [I, E, ite_eq_right hi.not_lt, ite_eq_left hi, zero_add,
        spectralStripMultiplicity_boundary hb.le hside]
    · simp only [I, E, ite_eq_right hi.not_gt, ite_eq_right hi.ne', add_zero, widthJump_outside hb.le hi,
        Nat.cast_zero, zero_mul]
  have he_pos (i : ι) (he : |x i| = b) : 0 < E i := by
    have hcap : 0 < spectralBoundaryMultiplicity s (m i) :=
      (lt_spectralBoundaryMultiplicity s (m i) 0).mpr ⟨hm i, by norm_num; linarith⟩
    simpa only [E, ite_eq_left he] using mul_pos (show (0 : ℝ) < (spectralBoundaryMultiplicity s (m i) : ℝ) by
      exact_mod_cast hcap) (hv i he)
  change _ < -(∑' i, I i) ↔ _
  simp_rw [hsplit]
  rw [hI.tsum_add hE, neg_lt_neg_iff, lt_add_iff_pos_right]
  constructor
  · contrapose!
    intro hnone
    have hz (i : ι) : E i = 0 := ite_eq_right (hnone i)
    simp [hz]
  · rintro ⟨i, hi⟩
    apply hE.tsum_pos _ i (he_pos i hi)
    intro j
    by_cases hj : |x j| = b
    · exact (he_pos j hj).le
    · simp [E, hj]

end WidthJump

section HeckeWidthJump

open Function
open scoped NNReal NumberField.AdeleRing
set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "Chars(" τ ")" => {χ : PontryaginDual C // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ, z)}
local notation "Ext(" τ ", " α ")" => {p : Chars(τ) × ℂ //
  0 < ord(p.1.val, p.2) ∧ α ≤ |p.2.re - 1/2|}
local notation "Off(" z ")" => ((z : ℂ).re - 1/2)
local notation "m(" χ ", " z ")" => (ord(χ, (z : ℂ))).toNat
local notation "M(" f ", " χ ", " z ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    (ideleClassTamagawaMeasure F) (f : BruhatCompactSupport C).val
    (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))

private theorem widthJump_strict_critical (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (z : Sites(χ.val)) :
    |Off(z)| < 1/2 := by
  have no := (hasSum_exteriorZeros_iff_isEmpty τ hτ (1/2)).mp
    (fun φ _ ↦ traceFormula_exteriorZeros_of_half_le τ φ le_rfl)
  exact lt_of_not_ge fun h ↦ no.false ⟨(χ,z.val),z.property,h⟩

/-- The wide-strip explicit formula already supplies the absolute bound used by
left convergence, separately for any normalized character and any compact Bruhat test. -/
theorem summable_heckeRealMoments_fullOrder (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (f : BruhatCompactSupport C) :
    Summable (fun z : Sites(χ.val) ↦ (m(χ.val,z) : ℝ) * |(M(f,χ.val,z)).re|) := by
  obtain ⟨_, _, _, _, _, hsum⟩ := traceFormula_of_half_le τ hτ f (le_refl (1/2))
  let w (z : Sites(χ.val)) : {p : Chars(τ) × ℂ //
      0 < ord(p.1.val, p.2) ∧ |p.2.re - 1/2| < 1/2} :=
    ⟨(χ,z.val), z.property, widthJump_strict_critical τ hτ χ z⟩
  have hw : Injective w := fun i j e ↦ Subtype.ext (congrArg (fun p ↦ p.val.2) e)
  have habs := (hsum.summable.comp_injective hw).norm
  apply habs.of_norm_bounded
  intro z
  change ‖(m(χ.val,z) : ℝ) * |(M(f,χ.val,z)).re|‖ ≤
    ‖((ord(χ.val,z.val) : ℤ) : ℂ) * M(f,χ.val,z)‖
  have hcast : ((m(χ.val,z) : ℕ) : ℂ) = ((ord(χ.val,z.val) : ℤ) : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg z.property.le
  have hbound (n : ℕ) (v : ℂ) : ‖(n : ℝ)*|v.re|‖ ≤ ‖(n : ℂ)*v‖ := by
    simp only [norm_mul, Complex.norm_natCast, Real.norm_eq_abs, Nat.abs_cast, abs_abs]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Nat.cast_nonneg _)
  rw [← hcast]
  exact hbound _ _

/-- Paper: Theorem 12.5.1.1, pp. 519–520. A one-sided comparison at each possible boundary
radius at or beyond the requested width gives the original exterior cancellation.
Reconstruction: the probes below are actual compact Bruhat tests. Their real Mellin moments
must be positive at both edges in the selected character. The comparison is required for
one probe per character and radius; its open-side sum is the left limit of the signed trace
by `tendsto_signedStripTrace_left`. The comparison remains open. -/
theorem traceFormula_exteriorZeros_of_signedWidthComparison (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) {α s : ℝ} (hα : 0 < α) (hs : 1 < s)
    (probe : Chars(τ) → ℝ → BruhatCompactSupport C)
    (hpositive : ∀ (χ : Chars(τ)) (b : ℝ), α ≤ b → b < 1/2 →
      ∀ z : Sites(χ.val), |Off(z)| = b → 0 < (M(probe χ b,χ.val,z)).re)
    (hcomparison : ∀ (χ : Chars(τ)) (b : ℝ), α ≤ b → b < 1/2 →
      -(∑' z : Sites(χ.val), if |Off(z)| < b then
        (m(χ.val,z) : ℝ) * (M(probe χ b,χ.val,z)).re else 0) ≤
      -(∑' z : Sites(χ.val), (spectralStripMultiplicity b s Off(z) m(χ.val,z) : ℝ) *
        (M(probe χ b,χ.val,z)).re))
    (φ : BruhatCompactSupport C) :
    HasSum (fun p : Ext(τ, α) ↦ ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(φ,p.val.1.val,p.val.2)) 0 := by
  let : IsEmpty Ext(τ, α) := ⟨fun p ↦ by
    let χ : Chars(τ) := p.val.1
    let z : Sites(χ.val) := ⟨p.val.2, p.property.1⟩
    let b := |Off(z)|
    have hb : α ≤ b := p.property.2
    have hb' : b < 1/2 := widthJump_strict_critical τ hτ χ z
    have hdown := (signedStripTrace_left_jump_iff
      (fun z : Sites(χ.val) ↦ Off(z)) (fun z ↦ (M(probe χ b,χ.val,z)).re)
      (fun z ↦ m(χ.val,z)) (fun z ↦ by have hz := z.property; omega)
      (summable_heckeRealMoments_fullOrder τ hτ χ (probe χ b)) (hα.trans_le hb) hs
      (hpositive χ b hb hb')).mpr ⟨z,rfl⟩
    exact (not_lt_of_ge (hcomparison χ b hb hb')) hdown⟩
  exact hasSum_empty

end HeckeWidthJump

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (zero_lt_one.trans hs₁(hs)).le

/-- Paper: (12.5.1.4), p. 520. For a test vanishing on the norm-one classes, a projective
Sobolev tensor represents convolution by the test after spectral projection at twist 1/2.
Reconstruction: Definition 10.4.3.7(2), p. 473, subtracts the spectral kernel. Using this
subtraction on p. 520 presupposes a tensor for the operator in (10.4.3.45).
Deviation: We ask for any representing tensor, restricted to the positive half-widths and
tests of Theorem 12.5.1.1. We impose no finite-rank expansion on the tensor.
Gap: The projective norm estimate for the geometric component of the output is missing.
Nothing in the Lean uses this statement, and it is not known how it connects with the rest of
the proof in Lean; in the paper it is used on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  sorry

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
It is proved from the kernel existence statement above, which is open, so it is no more
established than that statement. Nothing in the Lean uses it. -/
theorem hasSum_stripZeros_neg_integral_smoothenedDiagonal_of_vanishing
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let hK := exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs
    let diagonal (x : C𝔽) := dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK) (x, x)
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (η : PontryaginDual C𝔽) := meromorphicOrderAt (continuedCompletedHeckeL η)
    let Z := {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < order (χ z.1) (shift (1 / 2 + z.2.1) z.2.2)}
    let term (z : Z) := ((spectralStripMultiplicity α s z.val.2.1
      (order (χ z.val.1) (shift (1 / 2 + z.val.2.1) z.val.2.2)).untop₀.toNat : ℕ) : ℂ) *
      modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μ𝔽 φ.val (ideleClassNormTwist (χ z.val.1) (shift z.val.2.1 z.val.2.2))
    Integrable diagonal μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧
      HasSum term (-(∫ x, diagonal x ∂μ𝔽)) :=
  hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hα hs
    (exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs) U hU hBorel

end RiemannMasullo.Isolated
