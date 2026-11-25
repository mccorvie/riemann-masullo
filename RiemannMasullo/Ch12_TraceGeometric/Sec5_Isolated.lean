module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.ForMathlib.Analysis.Fourier.DiscreteStripProbe
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Isolated statements of §12.5

The projective strip kernel and its consequences for the smoothened geometric diagonal.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.

## The one-sided width comparison for Theorem 12.5.1.1

For one test per character and candidate edge, the signed closed-strip sum detects
boundary zeros by a downward jump when the real Mellin moments on the edge are positive.
The two hypotheses of `traceFormula_exteriorZeros_of_signedWidthComparison` specify
this positivity and the one-sided comparison that excludes the jump.

One compact smooth test per normalized character also detects every noncentral
zero simultaneously. It vanishes on norm-one classes and at the polar moments.
As positive widths tend to zero, the difference of the genuine geometric
diagonal integrals tends to the full-order noncentral mass. An upper bound
by the half-width diagonal for one sequence per character would give
the exterior cancellation at every positive width.
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

open Filter
open scoped Topology

/-- For positive widths tending to zero, the signed strip trace minus the width-one-half trace
converges to the sum of the real Mellin moments at all noncentral sites, counted at full order. -/
theorem tendsto_hecke_signedWidth_difference_zero_right (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (f : BruhatCompactSupport C)
    (s : ℝ) : Tendsto (fun a : ℝ ↦
      -(∑' z : Sites(χ.val), (spectralStripMultiplicity a s Off(z) m(χ.val,z) : ℝ) *
        (M(f,χ.val,z)).re) -
      (-(∑' z : Sites(χ.val), (spectralStripMultiplicity (1/2) s Off(z) m(χ.val,z) : ℝ) *
        (M(f,χ.val,z)).re))) (𝓝[>] 0)
      (𝓝 (∑' z : Sites(χ.val), if Off(z) ≠ 0 then
        (m(χ.val,z) : ℝ) * (M(f,χ.val,z)).re else 0)) := by
  let x (z : Sites(χ.val)) := Off(z)
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let v (z : Sites(χ.val)) := (M(f,χ.val,z)).re
  let w (z : Sites(χ.val)) := (n z : ℝ) * v z
  let term (a : ℝ) (z : Sites(χ.val)) := (spectralStripMultiplicity a s (x z) (n z) : ℝ) * v z
  have hs : Summable (fun z ↦ (n z : ℝ) * |v z|) := summable_heckeRealMoments_fullOrder τ hτ χ f
  have hw : Summable w := hs.of_norm_bounded fun z ↦ by simp [w, Real.norm_eq_abs]
  have hsplit : (∑' z, w z) = (∑' z, if x z = 0 then w z else 0) +
      (∑' z, if x z ≠ 0 then w z else 0) := by
    simpa only [tsum_subtype, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_compl_iff] using
      (hw.tsum_subtype_add_tsum_subtype_compl {z | x z = 0}).symm
  have hfull (z : Sites(χ.val)) : term (1/2) z = w z := by
    exact congrArg (fun k : ℕ ↦ (k : ℝ) * v z)
      (spectralStripMultiplicity_interior (abs_lt.mp (widthJump_strict_critical τ hτ χ z)) s (n z))
  have hlim : Tendsto (fun a : ℝ ↦ ∑' z, term a z) (𝓝[>] 0)
      (𝓝 (∑' z, if x z = 0 then w z else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro z
      by_cases hx : x z = 0
      · rw [ite_eq_left hx]
        apply tendsto_const_nhds.congr'
        filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin] with a ha
        simp only [term, w, spectralStripMultiplicity_interior (show x z ∈ Ioo (-a) a by
          rw [hx]; exact ⟨neg_lt_zero.mpr ha, ha⟩)]
      · rw [ite_eq_right hx]
        apply tendsto_const_nhds.congr'
        filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin,
          nhdsWithin_le_nhds (eventually_lt_nhds (abs_pos.mpr hx))] with a ha hax
        simp only [term, widthJump_outside ha.le hax, Nat.cast_zero, zero_mul]
    · exact Eventually.of_forall fun a z ↦ by
        simp only [term, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast widthJump_le a s (x z) (n z))
          (abs_nonneg _)
  change Tendsto (fun a : ℝ ↦ -(∑' z, term a z) - (-(∑' z, term (1/2) z))) _ _
  simp_rw [hfull]
  have hdiff : -(∑' z, if x z = 0 then w z else 0) - (-(∑' z, w z)) =
      ∑' z, if x z ≠ 0 then w z else 0 := by rw [hsplit]; ring
  simpa only [hdiff] using hlim.neg.sub_const (-(∑' z, w z))

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

section AllSiteHeckeProbe

open Function MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z

/-- Paper: Theorem 12.5.1.1, pp. 519–520. A single smooth compact radial shape for one
normalized character vanishes at log norm zero and at the two polar Mellin arguments.
Its real Mellin value is strictly positive at every positive-order zero of the character. -/
theorem exists_heckeAllSitePositiveRadialProfile (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : PontryaginDual C) (hχ : ∀ t, χ (τ t) = 1) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ H 0 = 0 ∧
      bilateralLaplace H (1/2) = 0 ∧ bilateralLaplace H (-1/2) = 0 ∧
      ∀ z : ℂ, 0 < ord(χ,z) → 0 < (bilateralLaplace H (z-1/2)).re := by
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
  let S : Set ℂ := {w | 0 < D (w+1/2)}
  have hstrip (w : ℂ) (hw : w ∈ S) : |w.re| < 1/2 := by
    simpa using widthJump_strict_critical τ hτ ⟨χ,hχ⟩ ⟨w+1/2,hw⟩
  have hloc : LocallyFiniteSupport (fun z ↦ D z) :=
    fun z ↦ D.supportLocallyFiniteWithinDomain z (mem_univ z)
  have hfin (T : ℝ) : {w ∈ S | |w.im| ≤ T}.Finite := by
    have hf := (hloc.finite_inter_support_of_isCompact (isCompact_closedBall (0:ℂ) (1+T))).image
      (fun z : ℂ ↦ z-1/2)
    apply hf.subset
    rintro w ⟨hw, ht⟩
    have hbox := abs_lt.mp (hstrip w hw)
    refine ⟨w+1/2, ⟨?_, hw.out.ne'⟩, by ring⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hpos : 0 ≤ w.re + 1/2 := by linarith [hbox.1]
    simp only [Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.one_re,
      Complex.div_ofNat_im, Complex.one_im, zero_div, add_zero, abs_of_nonneg hpos]
    linarith [hbox.2, ht]
  obtain ⟨H, hs, hc, h₀, hp, hm, hpos⟩ :=
    RiemannMasullo.exists_compact_polarFree_positive_on_discreteStrip
      (show (0:ℝ) < 1/2 by norm_num) S hstrip hfin
  have hn : (-1/2 : ℂ) = -(((1/2:ℝ) : ℂ)) := by
    push_cast
    ring
  refine ⟨H, hs, hc, h₀, by simpa using hp, by rw [hn]; exact hm, fun z hz ↦ hpos (z-1/2) ?_⟩
  show 0 < D (z-1/2+1/2)
  simpa only [sub_add_cancel] using hz

end AllSiteHeckeProbe

section WidthIntersection

namespace StripWidth

open Filter Function
open scoped Topology NumberField.AdeleRing

local notation "μ" => ideleClassTamagawaMeasure F
local notation "logN" => logIdeleClassNorm F
local notation "H(" α ", " s ")" => CompactIntervalSobolev μ logN (-α) α s
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (neg_le_self hα) hs
local notation "jets(" χ ", " a ", " α ", " s ")" => SpectralStripJetIndex χ a α s
local notation "jet(" χ ", " j ")" =>
  spectralZeroJet (χ j.1.1) j.1.2.1 j.1.2.2.1 j.1.2.2.2

private theorem symm_density {α : ℝ} (ha : 0 ≤ α) (s t : ℝ) :
    intervalSobolevDensity (-α) α s t = Real.exp (2 * α * |t|) * (1 + t ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos ht, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem logN_cont : Continuous (logIdeleClassNorm F) := by
  let m : C𝔽 →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
  change Continuous (fun g : C𝔽 ↦ Real.log ((m g).val : ℝ))
  exact (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    (fun g ↦ NNReal.coe_ne_zero.mpr (m g).ne_zero)

private theorem haar_ac_strip (α s : ℝ) (dual : Bool) :
    μ ≪ intervalSobolevMeasure μ logN (-α) α s dual := by
  have hlog : Measurable logN := (logN_cont (F := F)).measurable
  have hd : Measurable (fun x : C𝔽 ↦ intervalSobolevDensity (-α) α s (logN x)) := by
    unfold intervalSobolevDensity
    fun_prop
  have hp (x : C𝔽) : 0 < intervalSobolevDensity (-α) α s (logN x) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  cases dual with
  | false =>
    exact withDensity_absolutelyContinuous' hd.ennreal_ofReal.aemeasurable
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  | true =>
    exact withDensity_absolutelyContinuous' hd.inv.ennreal_ofReal.aemeasurable
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hp x))).ne')

/-- The ambient strip measure increases with the half-width at fixed Sobolev order. -/
theorem measure_le_of_halfWidth_le {α b : ℝ} (ha : 0 ≤ α) (hab : α ≤ b) (s : ℝ) :
    intervalSobolevMeasure μ logN (-α) α s ≤ intervalSobolevMeasure μ logN (-b) b s := by
  apply withDensity_mono
  refine .of_forall fun g ↦ ENNReal.ofReal_le_ofReal ?_
  change intervalSobolevDensity (-α) α s (logN g) ≤ intervalSobolevDensity (-b) b s (logN g)
  rw [symm_density ha, symm_density (ha.trans hab)]
  gcongr

/-- Regard a vector in a wider symmetric strip as the same Haar class in a narrower strip. -/
def restrictWidth {α b : ℝ} (ha : 0 ≤ α) (hab : α ≤ b) (s : ℝ) (f : H(b,s)) : H(α,s) :=
  ((Lp.memLp f).mono_measure (measure_le_of_halfWidth_le ha hab s)).toLp f

private theorem restrictWidth_ae {α b : ℝ} (ha : 0 ≤ α) (hab : α ≤ b) (s : ℝ) (f : H(b,s)) :
    (restrictWidth ha hab s f : C𝔽 → ℂ) =ᵐ[μ] (f : C𝔽 → ℂ) :=
  (haar_ac_strip (F := F) α s false).ae_eq (MemLp.coeFn_toLp _)

private theorem jetClass_ae (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (j : jets(χ,a,α,s)) :
    ((spectralStripJet_memLp χ ha hs j).toLp _ : C𝔽 → ℂ) =ᵐ[μ]
    jet(χ, j) :=
  (haar_ac_strip (F := F) α s true).ae_eq (MemLp.coeFn_toLp _)

private theorem rawKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (f : H(α,s)) :
    f ∈ Θ(a,ha,hs) ↔ ∀ j : jets(χ,a,α,s),
      (∫ g, f g * jet(χ, j) g ∂μ) = 0 := by
  rw [spectralStripJet_commonKernel χ hχ ha hs f]
  apply forall_congr'
  intro j
  have he := integral_congr_ae ((EventuallyEq.rfl (f := (f : C𝔽 → ℂ))).mul (jetClass_ae χ ha hs j))
  exact ⟨fun h ↦ he.symm.trans h, fun h ↦ he.trans h⟩

/-- For the varying half-width in (12.5.1.4), p. 520, a vector in the target strip belongs
physically to every strictly narrower global theta space exactly when all the target's
strict-interior zero moments vanish. Zero abscissae may accumulate at the target width. -/
theorem all_narrower_iff_interior_moments (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) (f : H(b,s)) :
    (∀ (α : ℝ) (ha : 0 < α) (hab : α < b),
      restrictWidth ha.le hab.le s f ∈ Θ(a,ha.le,hs)) ↔
    ∀ j : jets(χ,a,b,s), |j.1.2.1| < b →
      (∫ g, f g * jet(χ, j) g ∂μ) = 0 := by
  constructor
  · intro H j hj
    let α := (|j.1.2.1| + b) / 2
    have ha : 0 < α := by dsimp [α]; linarith [abs_nonneg j.1.2.1]
    have hab : α < b := by dsimp [α]; linarith
    have hjα : |j.1.2.1| < α := by dsimp [α]; linarith
    let k : jets(χ,a,α,s) := ⟨j.1, by
      rw [spectralStripMultiplicity_interior (abs_lt.mp hjα)]
      exact j.2.trans_le (widthJump_le ..)⟩
    have he := (rawKernel χ hχ ha.le hs _).mp (H α ha hab) k
    exact (integral_congr_ae ((restrictWidth_ae ha.le hab.le s f).mul
      (EventuallyEq.rfl (f := jet(χ, j))))).symm.trans he
  · intro H α ha hab
    apply (rawKernel χ hχ ha.le hs _).mpr
    intro j
    have hjα := (j.mem_strip_order_pos ha.le).1
    have hjb : |j.1.2.1| < b := abs_lt.mpr ⟨by linarith [hjα.1], by linarith [hjα.2]⟩
    let k : jets(χ,a,b,s) := ⟨j.1, by
      rw [spectralStripMultiplicity_interior (abs_lt.mp hjb)]
      exact j.2.trans_le (widthJump_le ..)⟩
    exact (integral_congr_ae ((restrictWidth_ae ha.le hab.le s f).mul
      (EventuallyEq.rfl (f := jet(χ, j))))).trans (H k hjb)

/-- For the global theta projection in (12.5.1.4), p. 520, the pullbacks from every strictly
narrower strip recover the target theta space exactly when every admitted jet lies in the
strict interior. The reverse obstruction is witnessed by an individual jet interpolant. -/
theorem closed_strip_recovered_iff_no_edge_jet (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    (∀ f : H(b,s), (∀ (α : ℝ) (ha : 0 < α) (hab : α < b),
      restrictWidth ha.le hab.le s f ∈ Θ(a,ha.le,hs)) → f ∈ Θ(a,hb.le,hs)) ↔
    (∀ j : jets(χ,a,b,s), |j.1.2.1| < b) := by
  classical
  constructor
  · intro h j
    by_contra hcrit
    obtain ⟨f, hf⟩ := spectralStripJet_singleInterpolant χ hχ hb.le hs j
    have hr (i : jets(χ,a,b,s)) :
        (∫ g, f g * jet(χ, i) g ∂μ) =
          if i = j then 1 else 0 := by
      exact (integral_congr_ae ((EventuallyEq.rfl (f := (f : C𝔽 → ℂ))).mul
        (jetClass_ae χ hb.le hs i))).symm.trans (hf i)
    have hinside := (all_narrower_iff_interior_moments χ hχ hb hs f).mpr
      (fun i hi ↦ by
        have hij : i ≠ j := fun he ↦ hcrit (he ▸ hi)
        simpa [hij] using hr i)
    have hzero := (rawKernel χ hχ hb.le hs f).mp (h f hinside) j
    simp [hr] at hzero
  · intro hall f hn
    exact (rawKernel χ hχ hb.le hs f).mpr fun j ↦
      (all_narrower_iff_interior_moments χ hχ hb hs f).mp hn j (hall j)

end StripWidth

end WidthIntersection

namespace CenterGeometry

local notation "centerHs₁(" hs ")" =>
  (lt_of_lt_of_le (show (1 : ℝ) < 3 from Nat.one_lt_cast.mpr (Nat.one_lt_succ_succ 1)) hs)
local notation "centerHs₀(" hs ")" => (zero_lt_one.trans centerHs₁(hs)).le

open Complex Filter Function MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "Chars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))
local notation "tensor(" a ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) a centerHs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr a).trans a) centerHs₀(hs) φ).comp
      (spectralProjection (F := F) (1/2) a centerHs₀(hs)))
local notation "diag(" a ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1/2) a centerHs₁(hs) φ hK) (x,x))

local notation "Rdiag(" a ", " hs ", " φ ", " hK ", " U ")" =>
  (∫ x, diag(a,hs,φ,hK,U) x ∂μ𝔽).re
local notation "hhalf" => (show 0 ≤ (1/2:ℝ) by norm_num)
local notation "ExtC(" τ ", " α ")" => {p : Chars(τ) × ℂ //
  0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re-1/2|}
local notation "mass(" χ ", " φ ")" =>
  (∑' z : Sites(χ), if z.val.re ≠ 1/2 then
    ((ord(χ,z.val)).toNat : ℝ) * (M(φ,χ,z.val)).re else 0)

namespace Fiber

private def point (σ t : ℝ) : ℂ := ((1/2+σ : ℝ) : ℂ) + (t:ℂ)*I

private theorem point_re_sub (σ t : ℝ) : (point σ t).re - 1/2 = σ := by simp [point]
private theorem point_im (σ t : ℝ) : (point σ t).im = t := by simp [point]
private theorem point_reconstruct (z : ℂ) : point (z.re-1/2) z.im = z := by
  apply Complex.ext <;> simp [point]

private theorem exterior_multiplicity {a σ : ℝ} (ha : 0 ≤ a)
    (h : σ ∉ Icc (-a) a) (s : ℝ) (n : ℕ) : spectralStripMultiplicity a s σ n = 0 := by
  have hi : ¬(-a<σ ∧ σ<a) := fun t ↦ h ⟨t.1.le,t.2.le⟩
  have he : ¬(σ = -a ∨ σ = a) := by
    rintro (rfl | rfl) <;> apply h <;> constructor <;> linarith
  simp [spectralStripMultiplicity, hi, he]

/-- Removing the other character fibers and extending the selected row from the
closed strip to all its sites preserves the sum. The multiplicity remains truncated
on the two edges and is zero strictly outside. -/
private theorem hasSum_single_character {K : Type*} (k : K) (P : K → ℂ → Prop)
    (n : K → ℂ → ℕ) (W : K → ℂ → ℂ) (a s : ℝ) (ha : 0 ≤ a)
    (hoff : ∀ j : K, j ≠ k → ∀ z : ℂ, W j z = 0) {T : ℂ}
    (hsum : HasSum (fun q : {q : K × ℝ × ℝ //
        q.2.1 ∈ Icc (-a) a ∧ P q.1 (point q.2.1 q.2.2)} ↦
      (spectralStripMultiplicity a s q.val.2.1 (n q.val.1 (point q.val.2.1 q.val.2.2)) : ℂ) *
        W q.val.1 (point q.val.2.1 q.val.2.2)) T) :
    HasSum (fun z : {z : ℂ // P k z} ↦
      (spectralStripMultiplicity a s (z.val.re-1/2) (n k z.val) : ℂ) * W k z.val) T := by
  let S := {z : ℂ // P k z}
  let B := {z : S // z.val.re-1/2 ∈ Icc (-a) a}
  let Q := {q : K × ℝ × ℝ // q.2.1 ∈ Icc (-a) a ∧ P q.1 (point q.2.1 q.2.2)}
  let R (q : Q) := (spectralStripMultiplicity a s q.val.2.1
    (n q.val.1 (point q.val.2.1 q.val.2.2)) : ℂ) * W q.val.1 (point q.val.2.1 q.val.2.2)
  let V (z : S) := (spectralStripMultiplicity a s (z.val.re-1/2) (n k z.val) : ℂ) * W k z.val
  let j : B → Q := fun z ↦ ⟨(k,z.val.val.re-1/2,z.val.val.im),z.property,
    by rw [point_reconstruct]; exact z.val.property⟩
  have hj : Injective j := by
    intro x y e
    have hr := congrArg (fun q : Q ↦ q.val.2.1) e
    have hi := congrArg (fun q : Q ↦ q.val.2.2) e
    apply Subtype.ext
    apply Subtype.ext
    apply Complex.ext
    · change x.val.val.re-1/2 = y.val.val.re-1/2 at hr
      change x.val.val.re = y.val.val.re
      linarith
    · exact hi
  have hother (q : Q) (hq : q ∉ range j) : R q = 0 := by
    by_cases h : q.val.1 = k
    · exfalso
      apply hq
      let ρ := point q.val.2.1 q.val.2.2
      have hz : P k ρ := h ▸ q.property.2
      have has : ρ.re-1/2 ∈ Icc (-a) a := by rw [point_re_sub]; exact q.property.1
      refine ⟨⟨⟨ρ,hz⟩,has⟩,Subtype.ext (Prod.ext h.symm (Prod.ext ?_ ?_))⟩
      · exact point_re_sub _ _
      · exact point_im _ _
    · change _ * W q.val.1 _ = 0
      rw [hoff _ h, mul_zero]
  have hcomp : HasSum (R ∘ j) T := (hj.hasSum_iff hother).mpr hsum
  have hB : HasSum (fun z : B ↦ V z.val) T := by
    apply hcomp.congr_fun
    intro z
    simp only [V, R, Function.comp_apply, j, point_reconstruct]
  have hext (z : S) (hz : z ∉ range (fun x : B ↦ x.val)) : V z = 0 := by
    have hout : z.val.re-1/2 ∉ Icc (-a) a := fun hi ↦ hz ⟨⟨z,hi⟩,rfl⟩
    dsimp only [V]
    rw [exterior_multiplicity ha hout s _, Nat.cast_zero, zero_mul]
  exact (Subtype.val_injective.hasSum_iff hext).mp hB

end Fiber

private theorem normalized_basepoints (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ lift : PontryaginDual C₁ → PontryaginDual C𝔽, IsSpectralBasepointChoice lift ∧
      (∀ ξ t, lift ξ (τ t) = 1) ∧
      ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) → lift (ψ.comp restriction) = ψ := by
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let P : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp n
  have hP (x : C𝔽) : P x ∈ C₁ := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div,hτ,div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict _ hP,P.continuous.subtype_mk _⟩
  have hr (x : C𝔽) : (r x : C𝔽) = x / τ (ideleClassNorm F x) := rfl
  refine ⟨fun ξ ↦ ξ.comp r, fun ξ ↦ ?_, fun ξ t ↦ ?_,fun ψ hψ ↦ ?_⟩
  · ext x : 1
    change ξ (r (x : C𝔽)) = ξ x
    apply congrArg ξ
    apply Subtype.ext
    rw [hr,show ideleClassNorm F (x : C𝔽) = 1 from x.property,map_one,div_one]
  · change ξ (r (τ t)) = 1
    have ht : r (τ t) = 1 := Subtype.ext (by rw [hr,hτ,div_self']; rfl)
    rw [ht,map_one]
  · ext x : 1
    change ψ (r x : C𝔽) = ψ x
    rw [hr,map_div,hψ,div_one]

private theorem divisor_eq_order (χ : PontryaginDual C𝔽) (z : ℂ) :
    ord(χ,z) = (order(χ,z)).untop₀ :=
  MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ z)

private theorem divisor_pos_iff_order_pos (χ : PontryaginDual C𝔽) (z : ℂ) :
    0 < ord(χ,z) ↔ 0 < order(χ,z) := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  have hfinite : order(χ,(2:ℂ)) ≠ ⊤ := by
    intro h
    have hp : 0 < order(χ,(2:ℂ)) := by rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
    have hbad := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2:ℂ).re) hp
    norm_num at hbad
  have hn := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ z) hfinite
  rw [divisor_eq_order]
  obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [← hk, WithTop.untop₀_coe]
  exact_mod_cast Iff.rfl

/-- At a fixed positive width the global diagonal is integrable and the selected
character's full list of divisor sites, with closed-strip jet multiplicities,
sums to its negative complex integral. -/
private theorem hasSum_oneCharacter_neg_integral_diagonal (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hoff : ∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ,η,z) = 0)
    {a s : ℝ} (ha : 0 < a) (hs : 3 ≤ s) (hK : tensor(ha.le,hs,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable diag(ha.le,hs,φ,hK,U) μ𝔽 ∧
      HasSum (fun z : Sites(χ.val) ↦
        (spectralStripMultiplicity a s (z.val.re-1/2) (ord(χ.val,z.val)).toNat : ℂ) *
        M(φ,χ.val,z.val)) (-(∫ x, diag(ha.le,hs,φ,hK,U) x ∂μ𝔽)) := by
  obtain ⟨lift,hbase,hnorm,hinv⟩ := normalized_basepoints τ hτ
  let k := χ.val.comp restriction
  have hk : lift k = χ.val := hinv χ.val χ.property
  have hdiff (j : PontryaginDual C₁) (hj : j ≠ k) : lift j ≠ χ.val := by
    intro h
    apply hj
    rw [← hbase j,h]
  let P (j : PontryaginDual C₁) (w : ℂ) := 0 < order(lift j,w)
  let n (j : PontryaginDual C₁) (w : ℂ) := (order(lift j,w)).untop₀.toNat
  let W (j : PontryaginDual C₁) (w : ℂ) := M(φ,lift j,w)
  obtain ⟨hint,-,hglobal⟩ := hasSum_stripZeros_neg_integral_smoothenedDiagonal
    φ hφ lift hbase ha hs hK U hU hBorel
  refine ⟨hint,?_⟩
  have hmoment (σ t : ℝ) : Fiber.point σ t - 1/2 = (σ:ℂ)+(t:ℂ)*I := by
    dsimp [Fiber.point]; push_cast; ring
  have hsum := Fiber.hasSum_single_character k P n W a s ha.le
    (fun j hj w ↦ hoff (lift j) (hnorm j) (hdiff j hj) w)
    (T := -(∫ x, diag(ha.le,hs,φ,hK,U) x ∂μ𝔽)) (by
      apply hglobal.congr_fun
      intro q
      dsimp only [n,W]
      rw [hmoment]
      rfl)
  have hraw : HasSum (fun z : {z : ℂ // 0 < order(χ.val,z)} ↦
      (spectralStripMultiplicity a s (z.val.re-1/2) (order(χ.val,z.val)).untop₀.toNat : ℂ) *
        M(φ,χ.val,z.val)) (-(∫ x, diag(ha.le,hs,φ,hK,U) x ∂μ𝔽)) := by
    rw [← hk]
    exact hsum
  let e : Sites(χ.val) ≃ {z : ℂ // 0 < order(χ.val,z)} :=
    Equiv.subtypeEquivRight (divisor_pos_iff_order_pos χ.val)
  apply (e.hasSum_iff.mpr hraw).congr_fun
  intro z
  change _ = (spectralStripMultiplicity a s (z.val.re-1/2) (order(χ.val,z.val)).untop₀.toNat : ℂ) *
    M(φ,χ.val,z.val)
  rw [divisor_eq_order]

/-- The signed real trace of the selected normalized character is the real part
of the integral of the actual smoothened global geometric diagonal. -/
private theorem integral_diagonal_re_eq_signedTrace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hoff : ∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ,η,z) = 0)
    {a s : ℝ} (ha : 0 < a) (hs : 3 ≤ s) (hK : tensor(ha.le,hs,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    (∫ x, diag(ha.le,hs,φ,hK,U) x ∂μ𝔽).re =
      -(∑' z : Sites(χ.val), (spectralStripMultiplicity a s (z.val.re-1/2) (ord(χ.val,z.val)).toNat : ℝ) *
        (M(φ,χ.val,z.val)).re) := by
  have hh := (hasSum_oneCharacter_neg_integral_diagonal τ hτ χ φ hφ hoff ha hs hK U hU hBorel).2
  have hre := Complex.reCLM.hasSum hh
  have hreal : HasSum (fun z : Sites(χ.val) ↦
      (spectralStripMultiplicity a s (z.val.re-1/2) (ord(χ.val,z.val)).toNat : ℝ) * (M(φ,χ.val,z.val)).re)
      (-(∫ x, diag(ha.le,hs,φ,hK,U) x ∂μ𝔽).re) := by
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.neg_re,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using hre
  rw [hreal.tsum_eq, neg_neg]

private theorem normOneVolume_pos : 0 < ((normOneIdeleClassTamagawaMeasure F) univ).toReal := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  exact ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

private theorem logNormMellin (H : ℝ → ℂ) (s : ℂ) :
    introTraceMellin (fun r ↦ H (Real.log r)) s = bilateralLaplace H s := by
  rw [introTraceMellin,mellin,← integral_comp_exp,bilateralLaplace]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp,Complex.real_smul,smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add,mul_comm]
  congr 1
  ring_nf

private theorem normalized_otherMoment_eq_zero (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ η : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (τ t) = 1) (hη : ∀ t, η (τ t) = 1) (hne : η ≠ χ)
    (f : ℝ → ℂ) (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g, φ.val g = introTraceTest χ f g)
    (z : ℂ) : M(φ,η,z) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, η y ≠ χ y := not_forall.mp (fun h ↦ hne (DFunLike.ext _ _ h))
  let u : (ideleClassNorm F).ker := ⟨y * (τ (ideleClassNorm F y))⁻¹, by
    change ideleClassNorm F _ = 1
    rw [map_mul, map_inv, hτ, mul_inv_cancel]⟩
  have huχ : χ u.val = χ y := by simp [u, hχ]
  have huη : η u.val = η y := by simp [u, hη]
  let d : ℂ := star (χ u.val : ℂ) * (η u.val : ℂ)
  have hd : d ≠ 1 := by
    intro hd
    have hunit : (χ u.val : ℂ) * star (χ u.val : ℂ) = 1 := by
      simp [← Circle.coe_inv_eq_conj]
    have he : (η u.val : ℂ) = (χ u.val : ℂ) := by
      dsimp only [d] at hd
      linear_combination (χ u.val : ℂ) * hd - (η u.val : ℂ) * hunit
    exact hy (Subtype.ext (by simpa only [huχ, huη] using he))
  let W (g : C𝔽) := φ.val g * ideleClassNormTwist η (z-1/2) g
  have hW (x : C𝔽) : W (u.val * x) = d * W x := by
    rw [mul_comm u.val x]
    have ht : ideleClassNormTwist η (z-1/2) u.val = (η u.val : ℂ) := by
      change (η u.val : ℂ) * (((ideleClassNorm F u.val).val : ℝ) : ℂ) ^ (z-1/2) = _
      simp [show ideleClassNorm F u.val = 1 from u.property]
    simp only [W, d, map_mul, ht, hφ, introTraceTest_mul_normOne]
    ring
  let m := ideleClassTamagawaMeasure F
  have hi : (∫ g, W g ∂m) = d * ∫ g, W g ∂m := by
    calc
      _ = ∫ g, W (u.val * g) ∂m := (integral_mul_left_eq_self (μ := m) W u.val).symm
      _ = _ := by rw [← integral_const_mul]; exact integral_congr_ae (.of_forall hW)
  have hzero : (∫ g, W g ∂m) = 0 :=
    (mul_eq_zero.mp (show (1-d) * (∫ g, W g ∂m) = 0 by linear_combination hi)).resolve_left
      (fun he ↦ hd (sub_eq_zero.mp he).symm)
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ]
    using hzero

private theorem exists_polarTest (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) :
    ∃ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) ∧
      M(φ,(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧ M(φ,(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 ∧
      (∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ,η,z) = 0) ∧
      ∀ z : Sites(χ.val), 0 < (M(φ,χ.val,z.val)).re := by
  obtain ⟨H,hs,hc,h₀,hp,hm,hpos⟩ :=
    exists_heckeAllSitePositiveRadialProfile (F := F) τ hτ χ.val χ.property
  have hneg : bilateralLaplace H (-(1/2)) = 0 := by simpa only [neg_div] using hm
  obtain ⟨φ,hφ⟩ := exists_characterNormTest (F := F) χ.val⁻¹ H hs hc
  let f (r : ℝ) := H (Real.log r)
  have htest (g : C𝔽) : φ.val g = introTraceTest χ.val f g := by
    rw [hφ g,introTraceTest]
    rw [show χ.val⁻¹ g = (χ.val g)⁻¹ from rfl,Circle.coe_inv_eq_conj]
    rfl
  have hM (z : ℂ) : M(φ,χ.val,z) = (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
      bilateralLaplace H (z-1/2) := by
    have hval := (introTraceTest_mellin χ.val f φ htest (z-1/2)).2
    simpa only [modulatedFourierMellin,relativeVerticalStrip,Set.preimage_univ,
      Set.indicator_univ,f,logNormMellin] using hval
  have hoff (η : PontryaginDual C𝔽) (hη : ∀ t, η (τ t) = 1) (hne : η ≠ χ.val) (z : ℂ) :
      M(φ,η,z) = 0 := normalized_otherMoment_eq_zero τ hτ χ.val η χ.property hη hne f φ htest z
  have hprin : M(φ,(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧ M(φ,(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 := by
    by_cases h : (1 : PontryaginDual C𝔽) = χ.val
    · rw [h,hM,hM,zero_sub,show (1:ℂ)-1/2 = 1/2 by ring,hp,hneg,mul_zero]
      exact ⟨rfl,rfl⟩
    · exact ⟨hoff 1 (by simp) h 0,hoff 1 (by simp) h 1⟩
  refine ⟨φ,?_,hprin.1,hprin.2,hoff,?_⟩
  · intro g
    simp only [hφ,show ideleClassNorm F g.val = 1 from g.property,
      Units.val_one,NNReal.coe_one,Real.log_one,h₀,mul_zero]
  · intro z
    rw [hM,Complex.re_ofReal_mul]
    exact mul_pos (normOneVolume_pos (F := F)) (hpos z.val z.property)

private theorem central_of_mass_nonpos (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hp : ∀ z : Sites(χ.val), 0 < (M(φ,χ.val,z.val)).re)
    (hle : mass(χ.val,φ) ≤ 0) (z : Sites(χ.val)) : z.val.re = 1/2 := by
  let w (z : Sites(χ.val)) : ℝ := ((ord(χ.val,z.val)).toNat : ℝ) * (M(φ,χ.val,z.val)).re
  let E (z : Sites(χ.val)) : ℝ := if z.val.re ≠ 1/2 then w z else 0
  have habs : Summable fun z ↦ |w z| := by
    simpa only [w,abs_mul,Nat.abs_cast] using summable_heckeRealMoments_fullOrder τ hτ χ φ
  have hE : Summable E := by
    apply habs.of_norm_bounded
    intro u
    by_cases h : u.val.re ≠ 1/2
    · simpa only [E,ite_eq_left h,Real.norm_eq_abs] using (le_refl |w u|)
    · simpa only [E,ite_eq_right h,norm_zero] using (abs_nonneg (w u))
  have hpos (u : Sites(χ.val)) (h : u.val.re ≠ 1/2) : 0 < E u := by
    have hu : 0 < ord(χ.val,u.val) := u.property
    have hn : 0 < (ord(χ.val,u.val)).toNat := by omega
    simpa only [E,ite_eq_left h,w] using mul_pos
      (by exact_mod_cast hn : (0:ℝ) < ((ord(χ.val,u.val)).toNat : ℝ)) (hp u)
  have hnn (u : Sites(χ.val)) : 0 ≤ E u := by
    by_cases h : u.val.re ≠ 1/2
    · exact (hpos u h).le
    · simp only [E,ite_eq_right h,le_refl]
  change (∑' u, E u) ≤ 0 at hle
  by_contra h
  exact hle.not_gt (hE.tsum_pos hnn z (hpos z h))

private theorem tendsto_centerDiagonal (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hoff : ∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ,η,z) = 0)
    {s : ℝ} (hs : 3 ≤ s) (β : ℕ → ℝ) (hβ : ∀ n, 0 < β n) (ht : Tendsto β atTop (𝓝 0))
    (hK : ∀ n, tensor((hβ n).le,hs,φ)) (hfull : tensor(hhalf,hs,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun n ↦ Rdiag((hβ n).le,hs,φ,hK n,U) - Rdiag(hhalf,hs,φ,hfull,U))
      atTop (𝓝 mass(χ.val,φ)) := by
  have hr : Tendsto β atTop (𝓝[>] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨ht,.of_forall hβ⟩
  have h := (tendsto_hecke_signedWidth_difference_zero_right τ hτ χ φ s).comp hr
  simp only [sub_ne_zero] at h
  apply h.congr
  intro n
  rw [integral_diagonal_re_eq_signedTrace τ hτ χ φ hφ hoff (hβ n) hs (hK n) U hU hBorel,
    integral_diagonal_re_eq_signedTrace τ hτ χ φ hφ hoff (by norm_num : 0 < (1/2:ℝ)) hs hfull U hU hBorel]
  rfl

private theorem central_of_diagonal_le (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hp : ∀ z : Sites(χ.val), 0 < (M(φ,χ.val,z.val)).re)
    (D : ℕ → ℝ) (d : ℝ) (h : Tendsto (fun n ↦ D n-d) atTop (𝓝 mass(χ.val,φ)))
    (hle : limUnder atTop D ≤ d) : ∀ z : Sites(χ.val), z.val.re = 1/2 := by
  have hD : Tendsto D atTop (𝓝 (mass(χ.val,φ)+d)) := by
    simpa only [sub_add_cancel] using h.add_const d
  rw [hD.limUnder_eq] at hle
  exact central_of_mass_nonpos τ hτ χ φ hp (by linarith only [hle])

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For each section-normalized character, a single
compact test has positive real Mellin moments at every positive-order zero. As positive
widths tend to zero, its real smoothened geometric diagonal minus the half-width diagonal
converges to the full-order noncentral moment sum. A weak upper comparison with the
half-width diagonal for these tests gives the original exterior-zero sum at every
positive width. The representing tensors and the upper comparison are hypotheses. -/
theorem exists_centerGeometricProbes_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ probe : Chars(τ) → BruhatCompactSupport C𝔽,
      (∀ χ : Chars(τ), (∀ g : C₁, (probe χ).val g = 0) ∧
        M(probe χ,(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧ M(probe χ,(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 ∧
        (∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(probe χ,η,z) = 0) ∧
        (∀ z : Sites(χ.val), 0 < (M(probe χ,χ.val,z.val)).re) ∧
        ∀ {s : ℝ} (hs : 3 ≤ s) (β : ℕ → ℝ) (hβ : ∀ n, 0 < β n), Tendsto β atTop (𝓝 0) →
          ∀ (hK : ∀ n, tensor((hβ n).le,hs,probe χ)) (hfull : tensor(hhalf,hs,probe χ))
            (U : ℕ → Set C𝔽), IsDPrimeSequence μ𝔽 U → (∀ n, MeasurableSet (U n)) →
            Tendsto (fun n ↦ Rdiag((hβ n).le,hs,probe χ,hK n,U)-Rdiag(hhalf,hs,probe χ,hfull,U))
              atTop (𝓝 mass(χ.val,probe χ))) ∧
      ((∀ χ : Chars(τ), ∃ (s : ℝ) (hs : 3 ≤ s) (β : ℕ → ℝ) (hβ : ∀ n, 0 < β n),
        Tendsto β atTop (𝓝 0) ∧ ∃ (hK : ∀ n, tensor((hβ n).le,hs,probe χ))
          (hfull : tensor(hhalf,hs,probe χ)) (U : ℕ → Set C𝔽), IsDPrimeSequence μ𝔽 U ∧
          (∀ n, MeasurableSet (U n)) ∧
          limUnder atTop (fun n ↦ Rdiag((hβ n).le,hs,probe χ,hK n,U)) ≤
            Rdiag(hhalf,hs,probe χ,hfull,U)) →
        ∀ (α : ℝ), 0 < α → ∀ f : BruhatCompactSupport C𝔽, (∀ g : C₁, f.val g = 0) →
          HasSum (fun p : ExtC(τ,α) ↦ ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) *
            M(f,p.val.1.val,p.val.2)) 0) := by
  let probe (χ : Chars(τ)) := (exists_polarTest τ hτ χ).choose
  have spec (χ : Chars(τ)) := (exists_polarTest τ hτ χ).choose_spec
  refine ⟨probe,?_,?_⟩
  · intro χ
    refine ⟨(spec χ).1,(spec χ).2.1,(spec χ).2.2.1,(spec χ).2.2.2.1,(spec χ).2.2.2.2,?_⟩
    intro s hs β hβ ht hK hfull U hU hBorel
    exact tendsto_centerDiagonal τ hτ χ (probe χ) (spec χ).1 (spec χ).2.2.2.1
      hs β hβ ht hK hfull U hU hBorel
  · intro hcomparison α hα f _hf
    have hcenter (χ : Chars(τ)) : ∀ z : Sites(χ.val), z.val.re = 1/2 := by
      obtain ⟨s,hs,β,hβ,ht,hK,hfull,U,hU,hBorel,hcmp⟩ := hcomparison χ
      exact central_of_diagonal_le τ hτ χ (probe χ) (spec χ).2.2.2.2 _ _
        (tendsto_centerDiagonal τ hτ χ (probe χ) (spec χ).1 (spec χ).2.2.2.1
          hs β hβ ht hK hfull U hU hBorel) hcmp
    let : IsEmpty ExtC(τ,α) := ⟨fun p ↦ by
      let z : Sites(p.val.1.val) := ⟨p.val.2,p.property.1⟩
      have hge : α ≤ |z.val.re-1/2| := p.property.2
      rw [hcenter p.val.1 z,sub_self,abs_zero] at hge
      exact hα.not_ge hge⟩
    exact hasSum_empty

local notation "centerKernel(" h ", " hs ", " φ ")" =>
  ((sobolevProjectiveKernelOperator_injective (F := F) h centerHs₀(hs)).existsUnique_iff_exists.mpr
    (stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1/2) h centerHs₀(hs) φ)).exists
local notation "centerDiagonal(" h ", " hs ", " φ ", " U ")" =>
  Rdiag(h,hs,φ,centerKernel(h,hs,φ),U)

/-- For any compact test vanishing on the norm-one classes and supported in a single
normalized character on the Mellin side, the change in the genuine geometric diagonal
from half-width one half to a shrinking positive width converges to the full-order
off-line real moment sum. The weighted-adjoint theorem of #7590 supplies the representing
tensors using Szymon Mikler's clustered quotient nuclearity from #7535. Injectivity of the
projective kernel operator gives uniqueness. -/
theorem tendsto_geometricDiagonal_sub_halfWidth_offLineMass (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hoff : ∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ,η,z) = 0)
    {s : ℝ} (hs : 3 ≤ s) (β : ℕ → ℝ) (hβ : ∀ n, 0 < β n) (ht : Tendsto β atTop (𝓝 0))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun n ↦ centerDiagonal((hβ n).le,hs,φ,U) - centerDiagonal(hhalf,hs,φ,U))
      atTop (𝓝 mass(χ.val,φ)) :=
  tendsto_centerDiagonal τ hτ χ φ hφ hoff hs β hβ ht
    (fun n ↦ centerKernel((hβ n).le,hs,φ)) centerKernel(hhalf,hs,φ) U hU hBorel

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The compact positive probes of #7556 use one
test per normalized character. An upper comparison of its genuine smoothened diagonal with its
half-width diagonal on one admissible shrinking family per character implies the exterior
cancellation for every positive width and every compact test vanishing on the norm-one classes. -/
theorem exists_centerGeometricProbes_exteriorZeros_of_upperComparison (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ probe : Chars(τ) → BruhatCompactSupport C𝔽,
      (∀ χ : Chars(τ), (∀ g : C₁, (probe χ).val g = 0) ∧
        M(probe χ,(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧ M(probe χ,(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 ∧
        (∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(probe χ,η,z) = 0) ∧
        ∀ z : Sites(χ.val), 0 < (M(probe χ,χ.val,z.val)).re) ∧
      ((∀ χ : Chars(τ), ∃ (s : ℝ) (hs : 3 ≤ s) (β : ℕ → ℝ) (hβ : ∀ n, 0 < β n),
        Tendsto β atTop (𝓝 0) ∧ ∃ U : ℕ → Set C𝔽, IsDPrimeSequence μ𝔽 U ∧
          (∀ n, MeasurableSet (U n)) ∧
          limUnder atTop (fun n ↦ centerDiagonal((hβ n).le,hs,probe χ,U)) ≤ centerDiagonal(hhalf,hs,probe χ,U)) →
        ∀ α : ℝ, 0 < α → ∀ f : BruhatCompactSupport C𝔽, (∀ g : C₁, f.val g = 0) →
          HasSum (fun p : ExtC(τ,α) ↦ ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(f,p.val.1.val,p.val.2)) 0) := by
  refine (exists_centerGeometricProbes_exteriorZeros τ hτ).elim fun probe hp ↦ ?_
  refine ⟨probe, ?_, ?_⟩
  · intro χ
    have h := hp.1 χ
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  · intro hcompare
    apply hp.2
    intro χ
    refine (hcompare χ).elim fun s h ↦ h.elim fun hs h ↦ ?_
    refine h.elim fun β h ↦ h.elim fun hβ h ↦ ?_
    exact h.2.elim fun U hU ↦ ⟨s, hs, β, hβ, h.1, fun n ↦ centerKernel((hβ n).le,hs,probe χ),
      centerKernel(hhalf,hs,probe χ), U, hU.1, hU.2.1, hU.2.2⟩

end CenterGeometry

/-- Paper: (12.5.1.4), p. 520. For a test vanishing on the norm-one classes, a projective
Sobolev tensor represents convolution by the test after spectral projection at twist 1/2.
Reconstruction: Definition 10.4.3.7(2), p. 473, subtracts the spectral kernel. Using this
subtraction on p. 520 presupposes a tensor for the operator in (10.4.3.45).
Deviation: We ask for any representing tensor, restricted to the positive half-widths and
tests of Theorem 12.5.1.1. We impose no finite-rank expansion on the tensor.
Quotient nuclearity and a finite decomposition into weighted adjoints give the representing
tensor. The paper uses it on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  exact stripTestAction_spectralProjection_has_projectiveKernel (1 / 2) hα.le hs₀(hs) φ

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
The projective kernel above supplies the witness in the smoothened diagonal formula. -/
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

/-! ## Localizing the kernel condition

Tests supported in any prescribed nonempty open set of log norms suffice to check the kernel condition.
-/

section KernelLocalization

open scoped ContDiff

local notation "ℓ" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 ℓ (-α) α s
local notation "A(" ha ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs φ
local notation "T(" ha ", " hs ", " g ")" =>
  hardySobolevTranslation μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs g
local notation "kerExists(" ha ", " hs ", " P ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = (A(ha, hs, φ)).comp P)

private theorem kernelLocalization_exists_translate (g : C𝔽) (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ x, ψ.val x = φ.val (g⁻¹ * x) := by
  have hφ := modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩
    ⟨φ.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (fun t ↦ ⟨QuotientGroup.mk (canonicalIdeleNormSection F t),
        canonicalIdeleNormSection_rightInverse F t⟩) φ.property⟩
  rw [modulationWeight_zero] at hφ
  let f : SchwartzBruhat C𝔽 := ⟨φ.val, hφ⟩
  have hsm := schwartzBruhat_isBruhatSmooth (schwartzBruhatTranslate g f)
  have hc := (show HasCompactSupport φ.val from φ.property.2).comp_homeomorph
    (Homeomorph.mulLeft g⁻¹)
  exact ⟨⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hsm, hc⟩, fun _ ↦ rfl⟩

/-- Left translating a test postcomposes its weighted strip convolution with the same
translation. -/
theorem stripTestAction_translate {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽) (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    A(ha, hs, ψ) = (T(ha, hs, g)).comp (A(ha, hs, φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have hφ := hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs φ u
  have htr := (measurePreserving_mul_left μ𝔽 g⁻¹).quasiMeasurePreserving.ae_eq_comp hφ
  have ht := hardySobolevTranslation_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs g
    (A(ha, hs, φ) u)
  filter_upwards [hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs ψ u,
    htr, ht] with x hx hy hz
  refine hx.trans ((?_ : lcaConvolution μ𝔽 ψ.val u x =
    lcaConvolution μ𝔽 φ.val u (g⁻¹ * x)).trans (hy.symm.trans hz.symm))
  unfold lcaConvolution
  rw [← integral_mul_left_eq_self (fun y ↦ ψ.val y * u (y⁻¹ * x)) g]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  rw [hψ, inv_mul_cancel_left, mul_inv_rev, mul_assoc]

private theorem kernelLocalization_nuclear_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (B : W(α, s) →L[ℂ] W(α, s)) :
    (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = B) ↔ IsNuclearOperator B := by
  refine ⟨fun ⟨K, hK⟩ ↦ (existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs B).mp
    ⟨K, hK, fun L hL ↦ sobolevProjectiveKernelOperator_injective ha hs (hL.trans hK.symm)⟩,
    fun h ↦ ((existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs B).mpr h).exists⟩

/-- Translating a test preserves projective kernel existence after any fixed input
operator on the strip. The inverse translation gives the converse. -/
theorem stripTestAction_projectiveKernel_translate_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    kerExists(ha, hs, P, ψ) ↔ kerExists(ha, hs, P, φ) := by
  have h (g : C𝔽) (f k : BruhatCompactSupport C𝔽) (hk : ∀ x, k.val x = f.val (g⁻¹ * x))
      (hK : kerExists(ha, hs, P, f)) : kerExists(ha, hs, P, k) := by
    apply (kernelLocalization_nuclear_iff ha hs _).mpr
    rw [stripTestAction_translate ha hs g f k hk]
    exact mul_mem_nuclearEndomorphisms_left _ ⟨_, (kernelLocalization_nuclear_iff ha hs _).mp hK⟩
  exact ⟨h g⁻¹ ψ φ (fun x ↦ by simp only [inv_inv, hψ, inv_mul_cancel_left]), h g φ ψ hψ⟩

/-- For a translated test the trace norm on the strip is bounded by the endpoint
exponential times the Sobolev polynomial. This applies to any fixed input operator. -/
theorem stripTestAction_translate_traceNorm_le {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) (N : nuclearEndomorphisms (W(α, s)))
    (hN : N.val = (A(ha, hs, φ)).comp P) :
    ∃ M : nuclearEndomorphisms (W(α, s)), M.val = (A(ha, hs, ψ)).comp P ∧
      traceNorm M ≤ Real.exp (α * |ℓ g|) * (1 + |ℓ g|) ^ (s / 2) * traceNorm N := by
  let T := T(ha, hs, g)
  refine ⟨⟨T * N.val, mul_mem_nuclearEndomorphisms_left T N⟩, ?_, ?_⟩
  · change T * N.val = _
    rw [hN, stripTestAction_translate ha hs g φ ψ hψ]
    rfl
  · have hn : 0 ≤ traceNorm N := by
      let : Norm (nuclearEndomorphisms (W(α, s))) := ⟨traceNorm⟩
      exact (traceNorm_normedSpaceCore (H := W(α, s))).norm_nonneg N
    refine (traceNorm_mul_left_le T N).trans (mul_le_mul_of_nonneg_right ?_ hn)
    apply (norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s _ hs g).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    apply max_le <;> apply Real.exp_le_exp.mpr
    · calc -α * ℓ g = α * (-ℓ g) := by ring
           _ ≤ α * |ℓ g| := mul_le_mul_of_nonneg_left (neg_le_abs _) ha
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) ha

private theorem kernelLocalization_continuous_log : Continuous (ℓ : C𝔽 → ℝ) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
    fun g ↦ NNReal.coe_ne_zero.mpr (m𝔽 g).ne_zero

private theorem kernelLocalization_log_mul (g x : C𝔽) : ℓ (g * x) = ℓ g + ℓ x := by
  change Real.log ((ideleClassNorm F (g * x)).val : ℝ) = _
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
    (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)]

private theorem kernelLocalization_log_surjective : Function.Surjective (ℓ : C𝔽 → ℝ) := by
  intro t
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e t))
  refine ⟨g, ?_⟩
  change Real.log ((ideleClassNorm F g).val : ℝ) = _
  rw [show ideleClassNorm F g = e t from canonicalIdeleNormSection_rightInverse F (e t)]
  exact Real.log_exp _


open scoped Manifold in
private theorem kernelLocalization_real_partition {K U : Set ℝ} (hc : IsCompact K)
    (ho : IsOpen U) {u : ℝ} (hu : u ∈ U) :
    ∃ (S : Finset ℝ) (ρ : S → ℝ → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i)) ∧
      (∀ i t, t ∈ tsupport (ρ i) → (u - i.val) + t ∈ U) ∧
      ∀ t ∈ K, ∑ i, ρ i t = 1 := by
  classical
  let V (t : ℝ) := (fun x : ℝ ↦ (u - t) + x) ⁻¹' U
  have hV (t : ℝ) : IsOpen (V t) := ho.preimage (continuous_const.add continuous_id)
  obtain ⟨S, hS⟩ := hc.elim_finite_subcover V hV fun t _ ↦
    mem_iUnion.mpr ⟨t, by simpa only [V, mem_preimage, sub_add_cancel] using hu⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℝ) hc.isClosed
    (fun i : S ↦ V i.val) (fun i ↦ hV i.val) (by simpa only [iUnion_subtype] using hS)
  refine ⟨S, fun i t ↦ ρ i t, fun i ↦ contMDiff_iff_contDiff.mp (ρ i).contMDiff,
    fun i _ ht ↦ hρ i ht, fun t ht ↦ ?_⟩
  rw [← finsum_eq_sum_of_fintype]
  exact ρ.sum_eq_one ht

private def kernelLocalization_profile (φ : BruhatCompactSupport C𝔽) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) : BruhatCompactSupport C𝔽 :=
  ⟨fun x ↦ (r (ℓ x) : ℂ) * φ.val x, (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
    isBruhatContDiff_mul (isBruhatSmooth_logProfile m𝔽 (Complex.ofRealCLM.contDiff.comp hr) p)
      ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (show HasCompactSupport φ.val from φ.property.2).mul_left⟩

private theorem kernelLocalization_profile_support (φ : BruhatCompactSupport C𝔽)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    tsupport (kernelLocalization_profile φ r hr).val ⊆ ℓ ⁻¹' tsupport r :=
  tsupport_mul_subset_left.trans ((tsupport_comp_subset_preimage
    (fun t : ℝ ↦ (r t : ℂ)) kernelLocalization_continuous_log).trans
    (preimage_mono (tsupport_comp_subset Complex.ofReal_zero r)))

private theorem kernelLocalization_profile_sum {ι : Type*} [Fintype ι] (φ : BruhatCompactSupport C𝔽)
    (r : ι → ℝ → ℝ) (hr : ∀ i, ContDiff ℝ ∞ (r i))
    (h1 : ∀ t ∈ ℓ '' tsupport φ.val, ∑ i, r i t = 1) :
    φ = ∑ i, kernelLocalization_profile φ (r i) (hr i) := by
  classical
  apply Subtype.ext
  funext x
  let ev : BruhatCompactSupport C𝔽 →+ ℂ :=
    { toFun k := k.val x, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  change φ.val x = ev (∑ i, kernelLocalization_profile φ (r i) (hr i))
  rw [map_sum]
  change φ.val x = ∑ i, (r i (ℓ x) : ℂ) * φ.val x
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hx : x ∈ tsupport φ.val
  · rw [h1 _ (mem_image_of_mem ℓ hx), Complex.ofReal_one, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

private theorem kernelLocalization_shift_support {U : Set ℝ} (d : ℝ) (f : BruhatCompactSupport C𝔽)
    (hf : ∀ x ∈ tsupport f.val, d + ℓ x ∈ U) :
    ∃ (g : C𝔽) (ψ : BruhatCompactSupport C𝔽), tsupport ψ.val ⊆ ℓ ⁻¹' U ∧
      ∀ x, f.val x = ψ.val (g⁻¹ * x) := by
  obtain ⟨g, hg⟩ := kernelLocalization_log_surjective (F := F) d
  obtain ⟨ψ, hψ⟩ := kernelLocalization_exists_translate g f
  refine ⟨g⁻¹, ψ, ?_, fun x ↦ by simp only [inv_inv, hψ, inv_mul_cancel_left]⟩
  intro x hx
  have he : ψ.val = f.val ∘ (fun y ↦ g⁻¹ * y) := funext hψ
  have hy := hf (g⁻¹ * x) (tsupport_comp_subset_preimage f.val
    (continuous_const.mul continuous_id) (he ▸ hx))
  rwa [← hg, ← kernelLocalization_log_mul, mul_inv_cancel_left] at hy

/-- A compact Bruhat test is a finite sum of translates of tests supported in any
prescribed nonempty open log-norm set. The summands and translations depend only on
the test and the set, so the same decomposition works at every strip width. -/
theorem bruhatCompactSupport_finite_sum_translates_of_logNorm {U : Set ℝ} (ho : IsOpen U)
    (hne : U.Nonempty) (φ : BruhatCompactSupport C𝔽) :
    ∃ (S : Finset ℝ) (f ψ : S → BruhatCompactSupport C𝔽) (g : S → C𝔽),
      φ = ∑ i, f i ∧ (∀ i, tsupport (ψ i).val ⊆ ℓ ⁻¹' U) ∧
      ∀ i x, (f i).val x = (ψ i).val ((g i)⁻¹ * x) := by
  classical
  obtain ⟨u, hu⟩ := hne
  have hc : IsCompact (ℓ '' tsupport φ.val) :=
    (show HasCompactSupport φ.val from φ.property.2).image kernelLocalization_continuous_log
  obtain ⟨S, ρ, hr, hsup, hsum⟩ := kernelLocalization_real_partition hc ho hu
  let f (i : S) := kernelLocalization_profile φ (ρ i) (hr i)
  have piece (i : S) := kernelLocalization_shift_support (u - i.val) (f i)
    (fun x hx ↦ hsup i (ℓ x) (kernelLocalization_profile_support φ (ρ i) (hr i) hx))
  choose g ψ hψ he using piece
  exact ⟨S, f, ψ, g, kernelLocalization_profile_sum φ ρ hr hsum, hψ, he⟩

private theorem kernelLocalization_sum {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) {ι : Type*} [Fintype ι] (f : ι → BruhatCompactSupport C𝔽)
    (h : ∀ i, kerExists(ha, hs, P, f i)) : kerExists(ha, hs, P, ∑ i, f i) := by
  classical
  choose kernels hk using h
  refine ⟨∑ i, kernels i, ?_⟩
  rw [map_sum, map_sum]
  change ∑ i, sobolevProjectiveKernelOperator (F := F) ha hs (kernels i) =
    (∑ i, (A(ha, hs, f i) : W(α, s) →L[ℂ] W(α, s))).comp P
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, hk]
  change ∑ i, A(ha, hs, f i) (P v) =
    (∑ i, (A(ha, hs, f i) : W(α, s) →L[ℂ] W(α, s))) (P v)
  rw [sum_apply]

/-- At fixed strip and input operator, it suffices to test a single prescribed nonempty
open set of log norms. -/
theorem stripTestAction_projectiveKernel_iff_support_in_open {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) {U : Set ℝ} (ho : IsOpen U) (hne : U.Nonempty) :
    (∀ φ : BruhatCompactSupport C𝔽, kerExists(ha, hs, P, φ)) ↔
      ∀ φ : BruhatCompactSupport C𝔽, tsupport φ.val ⊆ ℓ ⁻¹' U → kerExists(ha, hs, P, φ) := by
  refine ⟨fun h φ _ ↦ h φ, ?_⟩
  intro h φ
  obtain ⟨S, f, ψ, g, hsum, hsup, htr⟩ := bruhatCompactSupport_finite_sum_translates_of_logNorm ho hne φ
  rw [hsum]
  exact kernelLocalization_sum ha hs P f fun i ↦
    (stripTestAction_projectiveKernel_translate_iff ha hs P (g i) (ψ i) (f i) (htr i)).mpr (h _ (hsup i))

/-- Paper: (12.5.1.4), p. 520. The kernel assertion for all tests vanishing on the
norm-one classes is equivalent to testing any nonempty open set of log norms. In
particular a fixed short interval, or an arbitrary far half-line, suffices. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection_iff_support_in_open
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) {U : Set ℝ} (ho : IsOpen U) (hne : U.Nonempty) :
    let hs' : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 3).trans hs
    let P := spectralProjection (F := F) (1 / 2) hα.le hs'
    (∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) → kerExists(hα.le, hs', P, φ)) ↔
      ∀ φ : BruhatCompactSupport C𝔽, tsupport φ.val ⊆ ℓ ⁻¹' U → kerExists(hα.le, hs', P, φ) := by
  intro hs' P
  apply Iff.trans _ (stripTestAction_projectiveKernel_iff_support_in_open hα.le hs' P ho hne)
  refine ⟨fun h ↦ ?_, fun h φ _ ↦ h φ⟩
  apply (stripTestAction_projectiveKernel_iff_support_in_open hα.le hs' P isOpen_Ioi
    (nonempty_Ioi : (Ioi (0 : ℝ)).Nonempty)).mpr
  intro φ hφ
  apply h φ
  intro g
  apply image_eq_zero_of_notMem_tsupport
  intro hg
  have hx : 0 < ℓ g.val := hφ hg
  change 0 < Real.log ((ideleClassNorm F g.val).val : ℝ) at hx
  rw [g.property] at hx
  simp at hx

end KernelLocalization

end RiemannMasullo.Isolated
