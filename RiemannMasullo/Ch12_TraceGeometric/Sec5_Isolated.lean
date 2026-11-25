module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroDensity
public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeSchwartz
public import RiemannMasullo.ForMathlib.Analysis.Fourier.SchwartzLaplaceAxis
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PolynomialWindow
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.ForMathlib.Analysis.Analytic.CauchyWindow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
public import RiemannMasullo.AppA_AlgebraicNT.Sec5a_IdeleClassDPrime
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_UpperFrequencyGate
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLocalPolar
import RiemannMasullo.ForMathlib.Analysis.Fourier.DiscreteStripProbe
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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

One compact smooth test per normalized character also detects every noncentral
zero simultaneously. It vanishes on norm-one classes and at the polar moments.
As positive widths tend to zero, the difference of the genuine geometric
diagonal integrals tends to the full-order noncentral mass. An upper bound
by the half-width diagonal for one sequence per character would give
the exterior cancellation at every positive width.

At width zero, projecting after convolution gives a second comparison. Increasing
the Sobolev degree recovers all central multiplicities for the same test. The
upper comparison for its Haar integrals with the local principal values is
equivalent to exterior cancellation, with quotient nuclearity supplied by §10.3.
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

end CenterGeometry

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

namespace OutputOrderGeometry

open Complex Filter Function IsDedekindDomain

open scoped NNReal NumberField.AdeleRing Topology

set_option quotPrecheck false

attribute [local instance] instSpectralQuotientPolynormableSec3 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "Chars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))
local notation "outside(" τ ", " χ ", " φ ")" => (∀ η : PontryaginDual C𝔽,
  (∀ t, η (τ t) = 1) → η ≠ (χ).val → ∀ z : ℂ, M(φ,η,z) = 0)
local notation "hline" => (le_refl (0 : ℝ))
local notation "hbase" => ((neg_nonpos.mpr hline).trans hline)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "Aq(" hs ", " φ ")" => spectralConvolution (F := F) (1/2) hbase hs φ
local notation "w(" s ")" => (fun g : C𝔽 ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logIdeleClassNorm F g))
local notation "ν(" s ")" => ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (w(s) g))
local notation "ν'(" s ")" => ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (w(s) g)⁻¹)
local notation "L²(" s ")" => Lp ℂ 2 ((ν(s)).prod (ν'(s)))

/-- The unique mixed-weight Haar class for the actual output-projected operator. -/
private def haarClass {s : ℝ} (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (hQ : IsNuclearOperator (Aq(hs,φ))) : L²(s) :=
  (OutputProjectedLine.existsUnique_haarKernel (F := F) (1/2) hs φ hQ).exists.choose

/-- Smoothened geometric diagonal after selecting the output-projected Haar kernel. -/
private def diagonal {s : ℝ} (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (hQ : IsNuclearOperator (Aq(hs,φ))) (U : ℕ → Set C𝔽) (x : C𝔽) : ℂ :=
  dSequenceKernelSmoothening μ𝔽 U
    (fun p ↦ φ.val (p.1 * p.2⁻¹) - haarClass hs φ hQ p) (x,x)

local notation "point(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "Mshift(" φ ", " χ ", " w ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ w)

private theorem hasSum_global (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {s : ℝ} (hs : 1 < s) (hQ : IsNuclearOperator (Aq(hs₀(hs),φ)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable (diagonal hs₀(hs) φ hQ U) μ𝔽 ∧
    HasSum (fun z : {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < order(χ z.1,point(1/2+z.2.1,z.2.2))} ↦
      (spectralStripMultiplicity 0 s z.val.2.1
        (order(χ z.val.1,point(1/2+z.val.2.1,z.val.2.2))).untop₀.toNat : ℂ) *
      Mshift(φ,χ z.val.1,point(z.val.2.1,z.val.2.2)))
      (-(∫ x, diagonal hs₀(hs) φ hQ U x ∂μ𝔽)) := by
  let k := haarClass hs₀(hs) φ hQ
  have hk := (OutputProjectedLine.existsUnique_haarKernel (F := F) (1/2) hs₀(hs) φ hQ).exists.choose_spec
  obtain ⟨hi, he⟩ := OutputProjectedLine.geometricDiagonal_eq_neg_quotient (F := F) (1/2)
    hs₀(hs) φ hφ hQ k hk U hU hBorel
  change (∫ x, diagonal hs₀(hs) φ hQ U x ∂μ𝔽) = -hilbertTrace ⟨Aq(hs₀(hs),φ),hQ⟩ at he
  refine ⟨hi, ?_⟩
  rw [he, neg_neg]
  exact (spectralStripConvolution_trace (F := F) (1/2) χ hχ hline hs φ ⟨_,hQ⟩ rfl).2

/-- The geometric integral has the selected character's genuine closed-strip zero expansion at width zero. -/
private theorem hasSum_oneCharacter (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    {s : ℝ} (hs : 1 < s) (hQ : IsNuclearOperator (Aq(hs₀(hs),φ)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable (diagonal hs₀(hs) φ hQ U) μ𝔽 ∧
      HasSum (fun z : Sites(χ.val) ↦
        (spectralStripMultiplicity 0 s (z.val.re-1/2) (ord(χ.val,z.val)).toNat : ℂ) *
          M(φ,χ.val,z.val)) (-(∫ x, diagonal hs₀(hs) φ hQ U x ∂μ𝔽)) := by
  obtain ⟨lift,hlift,hnorm,hinv⟩ := CenterGeometry.normalized_basepoints τ hτ
  let k := χ.val.comp restriction
  have hk : lift k = χ.val := hinv χ.val χ.property
  have hdiff (j : PontryaginDual C₁) (hj : j ≠ k) : lift j ≠ χ.val := by
    intro h
    apply hj
    rw [← hlift j,h]
  let P (j : PontryaginDual C₁) (w : ℂ) := 0 < order(lift j,w)
  let n (j : PontryaginDual C₁) (w : ℂ) := (order(lift j,w)).untop₀.toNat
  let W (j : PontryaginDual C₁) (w : ℂ) := M(φ,lift j,w)
  obtain ⟨hint,hglobal⟩ := hasSum_global φ hφ lift hlift hs hQ U hU hBorel
  refine ⟨hint,?_⟩
  have hmoment (σ t : ℝ) : CenterGeometry.Fiber.point σ t - 1/2 = (σ:ℂ)+(t:ℂ)*I := by
    dsimp [CenterGeometry.Fiber.point]; push_cast; ring
  have hsum := CenterGeometry.Fiber.hasSum_single_character k P n W 0 s hline
    (fun j hj w ↦ hoff (lift j) (hnorm j) (hdiff j hj) w)
    (T := -(∫ x, diagonal hs₀(hs) φ hQ U x ∂μ𝔽)) (by
      apply hglobal.congr_fun
      intro q
      dsimp only [n,W]
      rw [hmoment]
      rfl)
  have hraw : HasSum (fun z : {z : ℂ // 0 < order(χ.val,z)} ↦
      (spectralStripMultiplicity 0 s (z.val.re-1/2) (order(χ.val,z.val)).untop₀.toNat : ℂ) *
        M(φ,χ.val,z.val)) (-(∫ x, diagonal hs₀(hs) φ hQ U x ∂μ𝔽)) := by
    rw [← hk]
    exact hsum
  let e : Sites(χ.val) ≃ {z : ℂ // 0 < order(χ.val,z)} :=
    Equiv.subtypeEquivRight (CenterGeometry.divisor_pos_iff_order_pos χ.val)
  apply (e.hasSum_iff.mpr hraw).congr_fun
  intro z
  change _ = (spectralStripMultiplicity 0 s (z.val.re-1/2) (order(χ.val,z.val)).untop₀.toNat : ℂ) *
    M(φ,χ.val,z.val)
  rw [CenterGeometry.divisor_eq_order]


/-- An odd Sobolev degree with exactly `k+1` available boundary jets. -/
private def degree (k : ℕ) : ℝ := 2 * ((k : ℝ) + 1) + 1

private theorem one_lt_degree (k : ℕ) : 1 < degree k := by
  have h : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  unfold degree
  linarith

local notation "hk₀(" k ")" => (le_of_lt (zero_lt_one.trans (one_lt_degree k)))

private theorem multiplicity_at_degree (k n : ℕ) (x : ℝ) :
    spectralStripMultiplicity 0 (degree k) x n = if x = 0 then min n (k+1) else 0 := by
  by_cases hx : x = 0
  · subst x
    rw [spectralStripMultiplicity_boundary hline (Or.inr rfl)]
    have hreal : (degree k - 1) / 2 = ((k+1 : ℕ) : ℝ) := by push_cast; unfold degree; ring
    simp only [spectralBoundaryMultiplicity, hreal, Nat.ceil_natCast, ite_true]
  · have hno : ¬ (0 < x ∧ x < 0) := fun h ↦ lt_asymm h.1 h.2
    simp [spectralStripMultiplicity, hx, hno]

local notation "m(" χ ", " z ")" => (ord(χ,(z : ℂ))).toNat
local notation "v(" φ ", " χ ", " z ")" => (M(φ,χ,z)).re
local notation "central(" z ")" => ((z : ℂ).re = 1/2)

/-- At degree `2(k+1)+1`, the complex trace counts each central site with
weight `min(order,k+1)`. All noncentral sites contribute zero. -/
private theorem hasSum_diagonal_degree (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (k : ℕ) (hQ : IsNuclearOperator (Aq(hk₀(k),φ)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable (diagonal hk₀(k) φ hQ U) μ𝔽 ∧
      HasSum (fun z : Sites(χ.val) ↦ if central(z) then
        ((min (m(χ.val,z)) (k+1) : ℕ) : ℂ) * M(φ,χ.val,z) else 0)
        (-(∫ x, diagonal hk₀(k) φ hQ U x ∂μ𝔽)) := by
  obtain ⟨hi, ht⟩ := hasSum_oneCharacter τ hτ χ φ hφ hoff (one_lt_degree k) hQ U hU hBorel
  refine ⟨hi, ht.congr_fun (fun z ↦ ?_)⟩
  rw [multiplicity_at_degree]
  by_cases hz : central(z)
  · simp only [hz, sub_self, ite_true]
  · simp only [hz, mt sub_eq_zero.mp hz, ite_false, Nat.cast_zero, zero_mul]

/-- Real part of the measured integral at one degree. -/
private theorem integral_re_degree (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (k : ℕ) (hQ : IsNuclearOperator (Aq(hk₀(k),φ)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    (∫ x, diagonal hk₀(k) φ hQ U x ∂μ𝔽).re =
      -(∑' z : Sites(χ.val), if central(z) then
        ((min (m(χ.val,z)) (k+1) : ℕ) : ℝ) * v(φ,χ.val,z) else 0) := by
  have hs := (hasSum_diagonal_degree τ hτ χ φ hφ hoff k hQ U hU hBorel).2
  have hr : HasSum (fun z : Sites(χ.val) ↦ if central(z) then
      ((min (m(χ.val,z)) (k+1) : ℕ) : ℝ) * v(φ,χ.val,z) else 0)
      (-(∫ x, diagonal hk₀(k) φ hQ U x ∂μ𝔽).re) := by
    apply (Complex.reCLM.hasSum hs).congr_fun
    intro z
    by_cases hz : central(z) <;> simp only [Complex.reCLM_apply,
      hz, ite_true, ite_false, Complex.zero_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
  rw [hr.tsum_eq, neg_neg]

private theorem norm_capped_le {ι : Type*} (center : ι → Prop) [DecidablePred center]
    (n : ι → ℕ) (v : ι → ℝ) (k : ℕ) (i : ι) :
    ‖if center i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0‖ ≤ (n i : ℝ) * |v i| := by
  by_cases h : center i
  · simp only [h, ite_true, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left (n i) (k+1)) (abs_nonneg _)
  · simp only [h, ite_false, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg (n i)) (abs_nonneg (v i))

private theorem tendsto_capped_sum {ι : Type*} (center : ι → Prop) [DecidablePred center]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|)) :
    Tendsto (fun k : ℕ ↦ -(∑' i, if center i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0))
      atTop (𝓝 (-(∑' i, if center i then (n i : ℝ) * v i else 0))) := by
  apply Tendsto.neg
  apply tendsto_tsum_of_dominated_convergence h
  · intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n i)] with k hk
    rw [min_eq_left (by omega : n i ≤ k+1)]
  · exact Eventually.of_forall fun k i ↦ norm_capped_le center n v k i

/-- The real geometric diagonal tends to minus the full central mass for the
same test, with the intrinsic full-order Hecke estimate supplying domination. -/
private theorem tendsto_integral_re (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (hQ : ∀ k : ℕ, IsNuclearOperator (Aq(hk₀(k),φ)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun k : ℕ ↦ (∫ x, diagonal hk₀(k) φ (hQ k) U x ∂μ𝔽).re) atTop
      (𝓝 (-(∑' z : Sites(χ.val), if central(z) then (m(χ.val,z) : ℝ) * v(φ,χ.val,z) else 0))) := by
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let V (z : Sites(χ.val)) := v(φ,χ.val,z)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z : ℝ) * |V z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have h := tendsto_capped_sum (fun z : Sites(χ.val) ↦ central(z)) n V hs
  exact h.congr' (.of_forall fun k ↦
    (integral_re_degree τ hτ χ φ hφ hoff k (hQ k) U hU hBorel).symm)


private theorem capped_sum_successive_difference {ι : Type*} (center : ι → Prop) [DecidablePred center]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|)) (k : ℕ) :
    (-(∑' i, if center i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0)) -
      (-(∑' i, if center i then ((min (n i) ((k+1)+1) : ℕ) : ℝ) * v i else 0)) =
       ∑' i, if center i ∧ k+2 ≤ n i then v i else 0 := by
  let f (j : ℕ) (i : ι) := if center i then ((min (n i) (j+1) : ℕ) : ℝ) * v i else 0
  have hsum (j : ℕ) : Summable (f j) := h.of_norm_bounded (norm_capped_le center n v j)
  change (-(∑' i, f k i)) - (-(∑' i, f (k+1) i)) = _
  rw [neg_sub_neg, ← (hsum (k+1)).tsum_sub (hsum k)]
  apply tsum_congr
  intro i
  by_cases hc : center i
  · by_cases hn : k+2 ≤ n i
    · have h1 : k+1 ≤ n i := by omega
      have h2 : (k+1)+1 ≤ n i := by omega
      simp only [f, hc, hn, true_and, ite_true, min_eq_right h1, min_eq_right h2,
        Nat.cast_add, Nat.cast_one]
      ring
    · have h1 : n i ≤ k+1 := by omega
      have h2 : n i ≤ (k+1)+1 := by omega
      simp only [f, hc, hn, true_and, ite_true, ite_false, min_eq_left h1, min_eq_left h2, sub_self]
  · simp only [f, hc, false_and, ite_false, sub_self]

/-- Subtracting the next measured integral from the current one counts each
central site of order at least `k+2` once, with its signed real Mellin value. -/
private theorem integral_degree_successive_difference (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽)
    (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ)) (k : ℕ)
    (h0 : IsNuclearOperator (Aq(hk₀(k),φ))) (h1 : IsNuclearOperator (Aq(hk₀(k+1),φ)))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    (∫ x, diagonal hk₀(k) φ h0 U x ∂μ𝔽).re - (∫ x, diagonal hk₀(k+1) φ h1 U x ∂μ𝔽).re =
      ∑' z : Sites(χ.val), if central(z) ∧ k+2 ≤ m(χ.val,z) then v(φ,χ.val,z) else 0 := by
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let V (z : Sites(χ.val)) := v(φ,χ.val,z)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z : ℝ) * |V z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have hdiff := capped_sum_successive_difference (fun z : Sites(χ.val) ↦ central(z)) n V hs k
  rw [integral_re_degree τ hτ χ φ hφ hoff k h0 U hU hBorel,
    integral_re_degree τ hτ χ φ hφ hoff (k+1) h1 U hU hBorel]
  exact hdiff

/-- At Sobolev order 2(k+1)+1, smooth the convolution kernel minus the unique
Haar kernel of projection after convolution. The cluster theorem supplies trace class. -/
def lineOrderDiagonal (k : ℕ) (φ : BruhatCompactSupport C𝔽) (U : ℕ → Set C𝔽) (x : C𝔽) : ℂ :=
  let s : ℝ := 2 * ((k : ℝ) + 1) + 1
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let hQ := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) (1/2) hline hs φ
  let K := (OutputProjectedLine.existsUnique_haarKernel (F := F) (1/2) hs φ hQ).exists.choose
  dSequenceKernelSmoothening μ𝔽 U (fun p ↦ φ.val (p.1*p.2⁻¹) - K p) (x,x)

/-- Exact complex expansion at each degree, including integrability of the actual diagonal. -/
theorem hasSum_lineOrderDiagonal (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (k : ℕ) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable (lineOrderDiagonal k φ U) μ𝔽 ∧
      HasSum (fun z : Sites(χ.val) ↦ if central(z) then
        ((min (m(χ.val,z)) (k+1) : ℕ) : ℂ) * M(φ,χ.val,z) else 0)
        (-(∫ x, lineOrderDiagonal k φ U x ∂μ𝔽)) :=
  hasSum_diagonal_degree τ hτ χ φ hφ hoff k
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) (1/2) hline hk₀(k) φ)
    U hU hBorel

/-- With the quotient trace class at every degree, the same compact test and the
same sequence give the full-order real central mass in the high Sobolev limit. -/
theorem tendsto_lineOrderDiagonal_re (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun k : ℕ ↦ (∫ x, lineOrderDiagonal k φ U x ∂μ𝔽).re) atTop
      (𝓝 (-(∑' z : Sites(χ.val), if central(z) then (m(χ.val,z) : ℝ) * v(φ,χ.val,z) else 0))) :=
  tendsto_integral_re τ hτ χ φ hφ hoff (fun k ↦
    spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) (1/2) hline hk₀(k) φ)
    U hU hBorel

/-- The difference of successive measured integrals counts the surviving central
sites with order at least `k+2`, each with one real Mellin value. -/
theorem lineOrderDiagonal_successive_difference (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽)
    (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ)) (k : ℕ)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    (∫ x, lineOrderDiagonal k φ U x ∂μ𝔽).re - (∫ x, lineOrderDiagonal (k+1) φ U x ∂μ𝔽).re =
      ∑' z : Sites(χ.val), if central(z) ∧ k+2 ≤ m(χ.val,z) then v(φ,χ.val,z) else 0 :=
  integral_degree_successive_difference τ hτ χ φ hφ hoff k
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) (1/2) hline hk₀(k) φ)
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) (1/2) hline hk₀(k+1) φ)
    U hU hBorel

private theorem summable_masked_weight {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n q : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|))
    (hq : ∀ i, q i ≤ n i) :
    Summable (fun i ↦ if P i then (q i : ℝ) * v i else 0) := by
  apply h.of_norm_bounded
  intro i
  by_cases hp : P i
  · simp only [hp, ite_true, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq i) (abs_nonneg (v i))
  · simp only [hp, ite_false, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg (n i)) (abs_nonneg (v i))

private theorem full_split {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|)) :
    (∑' i, (n i : ℝ) * v i) = (∑' i, if P i then (n i : ℝ) * v i else 0) +
      ∑' i, if ¬ P i then (n i : ℝ) * v i else 0 := by
  have hc := summable_masked_weight P n n v h (fun _ ↦ le_rfl)
  have he := summable_masked_weight (fun i ↦ ¬ P i) n n v h (fun _ ↦ le_rfl)
  rw [← hc.tsum_add he]
  apply tsum_congr
  intro i
  by_cases hp : P i <;> simp only [hp, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, add_zero, zero_add]

private theorem split_at_order {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|)) (k : ℕ) :
    (∑' i, (n i : ℝ) * v i) -
      (∑' i, if P i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0) =
      (∑' i, if ¬ P i then (n i : ℝ) * v i else 0) +
      ∑' i, if P i then (((n i)-(k+1) : ℕ) : ℝ) * v i else 0 := by
  let cap (i : ι) := if P i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0
  let rem (i : ι) := if P i then (((n i)-(k+1) : ℕ) : ℝ) * v i else 0
  have hc : Summable cap := summable_masked_weight P n _ v h (fun i ↦ min_le_left _ _)
  have hr : Summable rem := summable_masked_weight P n _ v h (fun i ↦ Nat.sub_le _ _)
  have hcentral : (∑' i, if P i then (n i : ℝ) * v i else 0) = (∑' i, cap i) + ∑' i, rem i := by
    rw [← hc.tsum_add hr]
    apply tsum_congr
    intro i
    by_cases hp : P i
    · have hnat : n i = min (n i) (k+1) + (n i - (k+1)) := by omega
      have hreal : (n i : ℝ) = ((min (n i) (k+1) : ℕ) : ℝ) + ((n i - (k+1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simp only [cap, rem, hp, ite_true]
      exact (congrArg (· * v i) hreal).trans (add_mul _ _ _)
    · simp only [cap, rem, hp, ite_false, add_zero]
  change _ - (∑' i, cap i) = _ + ∑' i, rem i
  rw [full_split P n v h, hcentral]
  ring

private theorem exterior_zero_iff {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|))
    (hn : ∀ i, 0 < n i) (hv : ∀ i, 0 < v i) :
    (∑' i, if ¬ P i then (n i : ℝ) * v i else 0) = 0 ↔ ∀ i, P i := by
  have he := summable_masked_weight (fun i ↦ ¬ P i) n n v h (fun _ ↦ le_rfl)
  have hnon (i : ι) : 0 ≤ (if ¬ P i then (n i : ℝ) * v i else 0) :=
    ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hv i).le) le_rfl
  constructor
  · intro hz i
    by_contra hi
    have hpos : 0 < (if ¬ P i then (n i : ℝ) * v i else 0) := by
      rw [ite_eq_left hi]
      exact mul_pos (by exact_mod_cast hn i) (hv i)
    exact (he.tsum_pos hnon i hpos).ne' hz
  · intro hp
    simp only [hp, not_true_eq_false, ite_false, tsum_zero]

private theorem approximates_iff_limUnder_le (I : ℕ → ℝ) (L V : ℝ)
    (ht : Tendsto I atTop (𝓝 L)) (hb : ∀ k, L ≤ I k) :
    (∀ δ : ℝ, 0 < δ → ∃ k, I k ≤ -V + δ) ↔ limUnder atTop I ≤ -V := by
  rw [ht.limUnder_eq]
  constructor
  · intro h
    by_contra! hlarge
    obtain ⟨k,hk⟩ := h ((L+V)/2) (by linarith)
    linarith [hb k]
  · intro h δ hδ
    have he : ∀ᶠ k in atTop, I k < -V + δ :=
      ht.eventually (eventually_lt_nhds (by linarith : L < -V + δ))
    exact he.exists.imp fun k hk ↦ hk.le

local notation "I(" k ", " φ ", " U ")" => (∫ x, lineOrderDiagonal k φ U x ∂μ𝔽).re
local notation "full(" χ ", " φ ")" =>
  (∑' z : Sites(χ), (m(χ,z) : ℝ) * v(φ,χ,z))
local notation "E(" χ ", " φ ")" =>
  (∑' z : Sites(χ), if ¬ central(z) then (m(χ,z) : ℝ) * v(φ,χ,z) else 0)
local notation "rem(" χ ", " φ ", " k ")" =>
  (∑' z : Sites(χ), if central(z) then ((m(χ,z) - (k+1) : ℕ) : ℝ) * v(φ,χ,z) else 0)

/-- The full mass plus the signed geometric integral is exactly the off-line mass
and the central multiplicities above the Sobolev cutoff. The identity is signed. -/
theorem lineOrderDiagonal_defect_eq_exterior_add_remainder
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (V : ℝ) (hV : V = full(χ.val,φ)) (k : ℕ)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    V + I(k,φ,U) = E(χ.val,φ) + rem(χ.val,φ,k) := by
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let W (z : Sites(χ.val)) := v(φ,χ.val,z)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z : ℝ) * |W z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have hQ := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms
    (F := F) (1/2) (le_refl (0:ℝ)) (le_of_lt (zero_lt_one.trans (one_lt_degree k))) φ
  have hi : I(k,φ,U) = -(∑' z : Sites(χ.val), if central(z) then
      ((min (n z) (k+1) : ℕ) : ℝ) * W z else 0) :=
    integral_re_degree τ hτ χ φ hφ hoff k hQ U hU hBorel
  rw [hV, hi, ← sub_eq_add_neg]
  exact split_at_order (fun z : Sites(χ.val) ↦ central(z)) n W hs k

/-- Adding the full mass to the high-order geometric diagonal converges to the
full off-line mass for this one character and one fixed smoothing sequence. -/
private theorem tendsto_lineOrderDiagonal_defect
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (V : ℝ) (hV : V = full(χ.val,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun k : ℕ ↦ V + I(k,φ,U)) atTop (𝓝 E(χ.val,φ)) := by
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let W (z : Sites(χ.val)) := v(φ,χ.val,z)
  let P (z : Sites(χ.val)) := central(z)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z : ℝ) * |W z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have hpart := full_split P n W hs
  have hsum : V + (-(∑' z : Sites(χ.val), if P z then (n z : ℝ) * W z else 0)) = E(χ.val,φ) := by
    rw [hV]
    change (∑' z, (n z : ℝ) * W z) + _ = _
    rw [hpart]
    ring
  have h := (tendsto_lineOrderDiagonal_re τ hτ χ φ hφ hoff U hU hBorel).const_add V
  rw [← hsum]
  exact h

/-- For a strictly positive test and a fixed measurable D-prime sequence, arbitrarily
close finite-order upper bounds, and the bound on the actual limit, are each equivalent
to centrality of every positive-order site of the chosen character. -/
private theorem lineOrderDiagonal_terminal_equivalences
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) (hoff : outside(τ,χ,φ))
    (hpositive : ∀ z : Sites(χ.val), 0 < v(φ,χ.val,z))
    (V : ℝ) (hV : V = full(χ.val,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    ((∀ δ : ℝ, 0 < δ → ∃ k : ℕ, I(k,φ,U) ≤ -V + δ) ↔
        ∀ z : Sites(χ.val), central(z)) ∧
      ((limUnder atTop (fun k : ℕ ↦ I(k,φ,U)) ≤ -V) ↔
        ∀ z : Sites(χ.val), central(z)) := by
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let W (z : Sites(χ.val)) := v(φ,χ.val,z)
  let P (z : Sites(χ.val)) := central(z)
  let A (k : ℕ) := I(k,φ,U)
  let E₀ := E(χ.val,φ)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z : ℝ) * |W z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have hn (z : Sites(χ.val)) : 0 < n z := by
    have hz := z.property
    change 0 < (ord(χ.val,z.val)).toNat
    omega
  have hE : E₀ = 0 ↔ ∀ z, P z := exterior_zero_iff P n W hs hn hpositive
  have hnon : 0 ≤ E₀ := tsum_nonneg (fun z : Sites(χ.val) ↦
    ite_nonneg (mul_nonneg (Nat.cast_nonneg (n z)) (hpositive z).le) le_rfl)
  have hlim : Tendsto (fun k : ℕ ↦ V + A k) atTop (𝓝 E₀) :=
    tendsto_lineOrderDiagonal_defect τ hτ χ φ hφ hoff V hV U hU hBorel
  have hA : Tendsto A atTop (𝓝 (E₀ - V)) := by
    have h := hlim.sub_const V
    simpa only [add_sub_cancel_left] using h
  have hlo (k : ℕ) : E₀ - V ≤ A k := by
    have hr : 0 ≤ rem(χ.val,φ,k) := tsum_nonneg (fun z : Sites(χ.val) ↦
      ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpositive z).le) le_rfl)
    have heq : V + A k = E₀ + rem(χ.val,φ,k) :=
      lineOrderDiagonal_defect_eq_exterior_add_remainder τ hτ χ φ hφ hoff V hV k U hU hBorel
    linarith
  have hcrit : limUnder atTop A ≤ -V ↔ ∀ z, P z := by
    rw [hA.limUnder_eq, ← hE]
    constructor <;> intro h <;> linarith
  exact ⟨(approximates_iff_limUnder_le A (E₀ - V) V hA hlo).trans hcrit, hcrit⟩

local notation "Vf" => HeightOneSpectrum (𝓞 F)
local notation "volC" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "Arch" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "FinV" => ((v : Vf) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteV(" v ")" => (finiteLocalMultiplicativeTamagawaMeasure F v
  ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finTerm(" v ", " b ")" => ((Real.log ((v : Vf).asIdeal.absNorm : ℝ) / finiteV(v) : ℝ) : ℂ) *
  finiteConnesWeilPrincipalValue v 1 b
local notation "rawM(" φ ", " χ ", " w ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ w)
local notation "localSum(" φ ", " A ", " B ")" =>
  rawM(φ,(1 : PontryaginDual C𝔽),(1/2)) + rawM(φ,(1 : PontryaginDual C𝔽),(-1/2)) -
    volC * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)) +
      ∑' v : Vf, finTerm(v,B v))

/-- The unconditional wide explicit formula identifies the full signed moment of a
single isotype with its actual polar terms and all finite and infinite principal values. -/
theorem exists_localTerms_eq_fullMoments (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽)
    (hoff : ∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ,η,z) = 0) :
    ∃ (A : Arch) (B : FinV),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (A w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : Vf) (u : (v.adicCompletion F)ˣ), (B v).val u = φ.val (finiteClass(v) u)) ∧
      Summable (fun v : Vf ↦ finTerm(v,B v)) ∧
      (localSum(φ,A,B)).re =
        ∑' z : Sites(χ.val), ((ord(χ.val,z.val)).toNat : ℝ)*(M(φ,χ.val,z.val)).re := by
  obtain ⟨A,B,hA,hB,hf,hall⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1/2:ℝ))
  refine ⟨A,B,hA,hB,hf,?_⟩
  let J := {p : Chars(τ) × ℂ // 0 < ord(p.1.val,p.2) ∧ |p.2.re-1/2| < 1/2}
  let f (p : J) := ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(φ,p.val.1.val,p.val.2)
  have hfull : HasSum f localSum(φ,A,B) := hall
  have hw (z : Sites(χ.val)) : |z.val.re-1/2| < 1/2 :=
    widthJump_strict_critical τ hτ χ z
  let j : Sites(χ.val) → J := fun z ↦ ⟨(χ,z.val),z.property,hw z⟩
  have hinj : Injective j := fun u v he ↦ Subtype.ext (congrArg (fun p : J ↦ p.val.2) he)
  have hother (p : J) (hp : p ∉ range j) : f p = 0 := by
    by_cases he : p.val.1 = χ
    · exfalso
      apply hp
      let z : Sites(χ.val) := ⟨p.val.2, by rw [← he]; exact p.property.1⟩
      exact ⟨z,Subtype.ext (Prod.ext he.symm rfl)⟩
    · have hneq : p.val.1.val ≠ χ.val := fun e ↦ he (Subtype.ext e)
      dsimp only [f]
      rw [hoff p.val.1.val p.val.1.property hneq p.val.2, mul_zero]
  have hv := Complex.reCLM.hasSum ((hinj.hasSum_iff hother).mpr hfull)
  have hr : HasSum (fun z : Sites(χ.val) ↦ ((ord(χ.val,z.val)).toNat : ℝ)*(M(φ,χ.val,z.val)).re)
      (localSum(φ,A,B)).re := by
    apply hv.congr_fun
    intro z
    have hm : ((ord(χ.val,z.val)).toNat : ℝ) = ((ord(χ.val,z.val) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg z.property.le
    simp only [Function.comp_apply, j, f, Complex.reCLM_apply, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,hm]
  exact hr.tsum_eq.symm

local notation "ext(" τ ", " α ")" => {p : Chars(τ) × ℂ //
  0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re-1/2|}
local notation "target(" τ ")" => (∀ (α : ℝ), 0 < α → ∀ f : BruhatCompactSupport C𝔽,
  (∀ g : C₁, f.val g = 0) → HasSum (fun p : ext(τ,α) ↦
    ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ)*M(f,p.val.1.val,p.val.2)) 0)

local notation "PV(" A ", " B ")" => (volC * ((∑ w : InfinitePlace F,
  infiniteConnesWeilPrincipalValue w (A w)) + ∑' v : Vf, finTerm(v,B v))).re

local notation "weight(" φ ", " χ ", " z ")" => ((ord(χ,(z : ℂ))).toNat : ℝ) * (M(φ,χ,z)).re

private theorem allCentral_iff_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    (∀ (χ : Chars(τ)) (z : Sites(χ.val)), z.val.re = 1/2) ↔ target(τ) := by
  constructor
  · intro hc α hα
    apply (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mpr
    refine ⟨fun p ↦ ?_⟩
    have hz := hc p.val.1 ⟨p.val.2,p.property.1⟩
    have he := p.property.2
    change p.val.2.re = 1/2 at hz
    rw [hz,sub_self,abs_zero] at he
    exact hα.not_ge he
  · intro h χ z
    by_contra hne
    have ha : 0 < |z.val.re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have h₀ := (hasSum_exteriorZeros_iff_isEmpty τ hτ _).mp (h _ ha)
    exact h₀.false ⟨(χ,z.val),z.property,le_refl _⟩

local notation "probeComparison(" τ ", " U ")" => (
  ∃ (φ : Chars(τ) → BruhatCompactSupport C𝔽) (A : Chars(τ) → Arch) (B : Chars(τ) → FinV),
      (∀ χ : Chars(τ),
        (∀ g : C₁, (φ χ).val g = 0) ∧
        M(φ χ,(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧ M(φ χ,(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 ∧
        (∀ η : PontryaginDual C𝔽, (∀ t, η (τ t) = 1) → η ≠ χ.val → ∀ z : ℂ, M(φ χ,η,z) = 0) ∧
        (∀ z : Sites(χ.val), 0 < (M(φ χ,χ.val,z.val)).re) ∧
        (∀ (w : InfinitePlace F) (u : w.Completionˣ),
          (A χ w).val u = (φ χ).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ (v : Vf) (u : (v.adicCompletion F)ˣ),
          (B χ v).val u = (φ χ).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        Summable (fun v : Vf ↦ finTerm(v,B χ v)) ∧
        -PV(A χ,B χ) = ∑' z : Sites(χ.val), weight(φ χ,χ.val,z) ∧
        Tendsto (fun k : ℕ ↦ -PV(A χ,B χ) + I(k,φ χ,U)) atTop
          (𝓝 (∑' z : Sites(χ.val), if z.val.re ≠ 1/2 then weight(φ χ,χ.val,z) else 0))) ∧
      ((∀ (χ : Chars(τ)) (δ : ℝ), 0 < δ → ∃ k : ℕ, I(k,φ χ,U) ≤ PV(A χ,B χ)+δ) ↔ target(τ)) ∧
      ((∀ χ : Chars(τ), limUnder atTop (fun k : ℕ ↦ I(k,φ χ,U)) ≤ PV(A χ,B χ)) ↔ target(τ)))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. A single compact test in each normalized
character simultaneously detects its entire positive divisor. A fixed measurable
D′-sequence determines its actual output-projected line Haar integrals at all odd
Sobolev degrees at least three. The positive-width exterior sum holds for every
test precisely when these real integrals admit the displayed signed upper bound
by the finite and infinite principal values. -/
theorem exists_probes_localPV_linePA_iff_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    probeComparison(τ,U) := by
  obtain ⟨φ,hspec,_⟩ := CenterGeometry.exists_centerGeometricProbes_exteriorZeros τ hτ
  have hoff (χ : Chars(τ)) := (hspec χ).2.2.2.1
  have hp (χ : Chars(τ)) := (hspec χ).2.2.2.2.1
  have hφ (χ : Chars(τ)) : (φ χ).val 1 = 0 := (hspec χ).1 (1 : C₁)
  choose A B hA hB hfin hv using fun χ : Chars(τ) ↦ exists_localTerms_eq_fullMoments τ hτ χ (φ χ) (hoff χ)
  have hV (χ : Chars(τ)) : -PV(A χ,B χ) = ∑' z : Sites(χ.val), weight(φ χ,χ.val,z) := by
    have h₀ : rawM(φ χ,(1 : PontryaginDual C𝔽),(-1/2)) = 0 := by
      simpa only [zero_sub, neg_div] using (hspec χ).2.1
    have h₁ : rawM(φ χ,(1 : PontryaginDual C𝔽),(1/2)) = 0 := by
      simpa only [show (1 : ℂ) - 1/2 = 1/2 by ring] using (hspec χ).2.2.1
    simpa only [h₁,h₀,zero_add,zero_sub,Complex.neg_re] using hv χ
  have hc (χ : Chars(τ)) := lineOrderDiagonal_terminal_equivalences
    τ hτ χ (φ χ) (hφ χ) (hoff χ) (hp χ) (-PV(A χ,B χ)) (hV χ) U hU hBorel
  simp only [neg_neg] at hc
  refine ⟨φ,A,B,?_,?_,?_⟩
  · intro χ
    refine ⟨(hspec χ).1,(hspec χ).2.1,(hspec χ).2.2.1,hoff χ,hp χ,hA χ,hB χ,hfin χ,hV χ,?_⟩
    exact tendsto_lineOrderDiagonal_defect τ hτ χ (φ χ) (hφ χ) (hoff χ)
      (-PV(A χ,B χ)) (hV χ) U hU hBorel
  · exact (forall_congr' fun χ ↦ (hc χ).1).trans (allCentral_iff_exteriorZeros τ hτ)
  · exact (forall_congr' fun χ ↦ (hc χ).2).trans (allCentral_iff_exteriorZeros τ hτ)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Every number field admits a single
Borel smoothing sequence for the preceding comparison across all normalized characters. -/
theorem exists_measurableSequence_localPV_linePA_iff_exteriorZeros :
    ∃ U : ℕ → Set C𝔽, IsDPrimeSequence μ𝔽 U ∧ (∀ n, MeasurableSet (U n)) ∧
      ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) → probeComparison(τ,U) := by
  obtain ⟨U,hU,hBorel⟩ := exists_measurable_ideleClassDPrimeSequence F
  exact ⟨U,hU,hBorel,fun τ hτ ↦ exists_probes_localPV_linePA_iff_exteriorZeros τ hτ U hU hBorel⟩

section PrimeFreeCentered

open scoped ContDiff

local notation "J(" k ", " φ ", " U ")" =>
  (∫ x, lineOrderDiagonal k (φ : BruhatCompactSupport C𝔽) U x -
    (φ : BruhatCompactSupport C𝔽).val 1 ∂μ𝔽).re

private theorem quotient_hasSum_oneCharacter (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hoff : outside(τ,χ,φ))
    {s : ℝ} (hs : 1 < s) (hQ : IsNuclearOperator (Aq(hs₀(hs),φ))) :
    HasSum (fun z : Sites(χ.val) ↦
      (spectralStripMultiplicity 0 s (z.val.re-1/2) (ord(χ.val,z.val)).toNat : ℂ) *
        M(φ,χ.val,z.val)) (hilbertTrace ⟨Aq(hs₀(hs),φ),hQ⟩) := by
  obtain ⟨lift,hlift,hnorm,hinv⟩ := CenterGeometry.normalized_basepoints τ hτ
  let k := χ.val.comp restriction
  have hk : lift k = χ.val := hinv χ.val χ.property
  have hdiff (j : PontryaginDual C₁) (hj : j ≠ k) : lift j ≠ χ.val := by
    intro h
    apply hj
    rw [← hlift j,h]
  let P (j : PontryaginDual C₁) (w : ℂ) := 0 < order(lift j,w)
  let n (j : PontryaginDual C₁) (w : ℂ) := (order(lift j,w)).untop₀.toNat
  let W (j : PontryaginDual C₁) (w : ℂ) := M(φ,lift j,w)
  let T := hilbertTrace ⟨Aq(hs₀(hs),φ),hQ⟩
  have hglobal := (spectralStripConvolution_trace (F := F) (1/2) lift hlift hline hs φ
    (⟨_,hQ⟩ : nuclearEndomorphisms (spectralSobolevQuotient F (1/2) hbase hs₀(hs))) rfl).2
  have hmoment (σ t : ℝ) : CenterGeometry.Fiber.point σ t - 1/2 = (σ:ℂ)+(t:ℂ)*I := by
    dsimp [CenterGeometry.Fiber.point]; push_cast; ring
  have hsum := CenterGeometry.Fiber.hasSum_single_character k P n W 0 s hline
    (fun j hj w ↦ hoff (lift j) (hnorm j) (hdiff j hj) w) (T := T) (by
      apply hglobal.congr_fun
      intro q
      dsimp only [n,W]
      rw [hmoment]
      rfl)
  let SumAt (ψ : PontryaginDual C𝔽) := HasSum (fun z : {z : ℂ // 0 < order(ψ,z)} ↦
    (spectralStripMultiplicity 0 s (z.val.re-1/2) (order(ψ,z.val)).untop₀.toNat : ℂ) *
      M(φ,ψ,z.val)) T
  have hraw : SumAt χ.val := (congrArg SumAt hk).mp (show SumAt (lift k) from hsum)
  let e : Sites(χ.val) ≃ {z : ℂ // 0 < order(χ.val,z)} :=
    Equiv.subtypeEquivRight (CenterGeometry.divisor_pos_iff_order_pos χ.val)
  apply (e.hasSum_iff.mpr hraw).congr_fun
  intro z
  change _ = (spectralStripMultiplicity 0 s (z.val.re-1/2) (order(χ.val,z.val)).untop₀.toNat : ℂ) *
    M(φ,χ.val,z.val)
  rw [CenterGeometry.divisor_eq_order]

/-- For an arbitrary value at the identity, centering the actual geometric diagonal inside
the Haar integral recovers the central multiplicities capped at the Sobolev order. -/
theorem hasSum_centeredLineOrderDiagonal (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hoff : outside(τ,χ,φ))
    (k : ℕ) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable (fun x ↦ lineOrderDiagonal k φ U x - φ.val 1) μ𝔽 ∧
      HasSum (fun z : Sites(χ.val) ↦ if central(z) then
        ((min (m(χ.val,z)) (k+1) : ℕ) : ℂ) * M(φ,χ.val,z) else 0)
        (-(∫ x, lineOrderDiagonal k φ U x - φ.val 1 ∂μ𝔽)) := by
  let hQ := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (F := F) (1/2) hline hk₀(k) φ
  let hK := (OutputProjectedLine.existsUnique_haarKernel (F := F) (1/2) hk₀(k) φ hQ).exists
  obtain ⟨hi,he⟩ := OutputProjectedLine.geometricDiagonal_sub_atOne_eq_neg_quotient (F := F)
    (1/2) hk₀(k) φ hQ hK.choose hK.choose_spec U hU hBorel
  refine ⟨hi,?_⟩
  change (∫ x, lineOrderDiagonal k φ U x - φ.val 1 ∂μ𝔽) = -hilbertTrace ⟨Aq(hk₀(k),φ),hQ⟩ at he
  rw [he,neg_neg]
  apply (quotient_hasSum_oneCharacter τ hτ χ φ hoff (one_lt_degree k) hQ).congr_fun
  intro z
  rw [multiplicity_at_degree]
  by_cases hz : central(z)
  · simp only [hz,sub_self,ite_true]
  · simp only [hz,mt sub_eq_zero.mp hz,ite_false,Nat.cast_zero,zero_mul]

private theorem centeredIntegral_re_eq (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hoff : outside(τ,χ,φ))
    (k : ℕ) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    J(k,φ,U) = -(∑' z : Sites(χ.val), if central(z) then
      ((min (m(χ.val,z)) (k+1) : ℕ) : ℝ) * v(φ,χ.val,z) else 0) := by
  have hsum := (hasSum_centeredLineOrderDiagonal τ hτ χ φ hoff k U hU hBorel).2
  have hr : HasSum (fun z : Sites(χ.val) ↦ if central(z) then
      ((min (m(χ.val,z)) (k+1) : ℕ) : ℝ) * v(φ,χ.val,z) else 0) (-J(k,φ,U)) := by
    apply (Complex.reCLM.hasSum hsum).congr_fun
    intro z
    by_cases hz : central(z) <;> simp only [Complex.reCLM_apply,hz,ite_true,ite_false,
      Complex.zero_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  rw [hr.tsum_eq,neg_neg]

private theorem centeredIntegral_sign (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Chars(τ)) (φ : BruhatCompactSupport C𝔽) (hoff : outside(τ,χ,φ))
    (hp : ∀ z : Sites(χ.val), 0 < v(φ,χ.val,z)) (V : ℝ) (hV : V = full(χ.val,φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    (∀ k : ℕ, V + J(k,φ,U) = E(χ.val,φ) + rem(χ.val,φ,k)) ∧
    Tendsto (fun k : ℕ ↦ V + J(k,φ,U)) atTop (𝓝 E(χ.val,φ)) ∧
    ((∀ δ : ℝ, 0 < δ → ∃ k : ℕ, J(k,φ,U) ≤ -V + δ) ↔ ∀ z : Sites(χ.val), central(z)) ∧
    ((limUnder atTop (fun k : ℕ ↦ J(k,φ,U)) ≤ -V) ↔ ∀ z : Sites(χ.val), central(z)) := by
  let P (z : Sites(χ.val)) := central(z)
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let W (z : Sites(χ.val)) := v(φ,χ.val,z)
  let A (k : ℕ) := J(k,φ,U)
  let L := -(∑' z, if P z then (n z : ℝ) * W z else 0)
  let E₀ := E(χ.val,φ)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z : ℝ) * |W z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have hA : Tendsto A atTop (𝓝 L) :=
    (tendsto_capped_sum P n W hs).congr' (.of_forall fun k ↦
      (centeredIntegral_re_eq τ hτ χ φ hoff k U hU hBorel).symm)
  have hsplit : V + L = E₀ := by
    dsimp only [L]
    rw [hV,full_split P n W hs]
    ring
  have hstep (k : ℕ) : V + A k = E₀ + rem(χ.val,φ,k) := by
    dsimp only [A]
    rw [hV,centeredIntegral_re_eq τ hτ χ φ hoff k U hU hBorel,← sub_eq_add_neg]
    exact split_at_order P n W hs k
  have hE : E₀ = 0 ↔ ∀ z, P z := exterior_zero_iff P n W hs (fun z ↦ by
    have hz := z.property
    change 0 < (ord(χ.val,z.val)).toNat
    omega) hp
  have hnon : 0 ≤ E₀ := tsum_nonneg fun z : Sites(χ.val) ↦
    ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp z).le) le_rfl
  have hlo (k : ℕ) : L ≤ A k := by
    have hr : 0 ≤ rem(χ.val,φ,k) := tsum_nonneg fun z : Sites(χ.val) ↦
      ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp z).le) le_rfl
    linarith [hstep k]
  have hcrit : limUnder atTop A ≤ -V ↔ ∀ z, P z := by
    rw [hA.limUnder_eq,← hE]
    constructor <;> intro h <;> linarith
  refine ⟨hstep,?_,(approximates_iff_limUnder_le A L V hA hlo).trans hcrit,hcrit⟩
  change Tendsto (fun k ↦ V+A k) atTop (𝓝 E₀)
  rw [← hsplit]
  exact hA.const_add V

/-- A smooth even profile inside the first prime shell, chosen before the number field. -/
def primeFreeProfile : ℝ → ℝ :=
  (exists_smallSupport_polarFree_positiveLaplace (B := 1/2) (R := Real.log 2)
    (by norm_num) (Real.log_pos (by norm_num))).choose

theorem primeFreeProfile_properties :
    ContDiff ℝ (∞) primeFreeProfile ∧ HasCompactSupport primeFreeProfile ∧
    tsupport primeFreeProfile ⊆ Ioo (-Real.log 2) (Real.log 2) ∧
    (∀ x, primeFreeProfile (-x) = primeFreeProfile x) ∧ 0 < primeFreeProfile 0 ∧
    bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) (1/2) = 0 ∧
    bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) (-(1/2)) = 0 ∧
    ∀ w : ℂ, |w.re| < 1/2 → 0 < (bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) w).re := by
  simpa only [primeFreeProfile,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    (exists_smallSupport_polarFree_positiveLaplace (B := 1/2) (R := Real.log 2)
      (by norm_num) (Real.log_pos (by norm_num))).choose_spec

/-- The rational local min-power correction of the chosen short profile is strictly positive. -/
theorem primeFreeProfile_minPower_pos :
    0 < ∫ x : ℝ, Real.exp (-(1/2 : ℝ) * |x|) * primeFreeProfile x := by
  obtain ⟨hs,hc,_,_,_,_,_,hstrip⟩ := primeFreeProfile_properties
  apply integral_exp_neg_abs_mul_pos_of_bilateralLaplace primeFreeProfile hc hs _ (by norm_num)
  intro t
  apply hstrip
  simp

section UpperFrequencyGates

open RationalUpperGate

/-- The centered test of §12.5 gives a positive lower bound for the compensated
rank-one defect of every normalized rational upper frequency gate at fixed spatial scale. -/
theorem primeFreeProfile_upperGate {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ∈ Icc 0 1)
    (hplateau : ∃ δ > 0, ∀ u ∈ Ioc 0 δ, Q u = 1) :
    0 < rankOneDefect primeFreeProfile (fun _ ↦ 1) ∧
    rankOneDefect primeFreeProfile (fun _ ↦ 1) +
      (1 - 1 / Real.sqrt 2) * primeFreeProfile 0 * logLoss Q ≤
      rankOneDefect primeFreeProfile Q + primeFreeProfile 0 * logLoss Q ∧
    0 < rankOneDefect primeFreeProfile Q + primeFreeProfile 0 * logLoss Q := by
  obtain ⟨hs, _, hS, heven, _, _, _, hstrip⟩ := primeFreeProfile_properties
  apply compensated_defect_of_positive_spectrum hs hS heven _ hQ hbound hplateau
  intro t
  apply hstrip
  simp

private theorem primeFreeProfile_negHalfMoment :
    (∫ x : ℝ, primeFreeProfile x * Real.exp (-x / 2)) = 0 := by
  obtain ⟨_, _, _, _, _, _, hpolar, _⟩ := primeFreeProfile_properties
  rw [halfMoment_eq_re_bilateralLaplace]
  simpa only [neg_div, Complex.zero_re] using congrArg Complex.re hpolar

/-- A forward translate by at least `log 2` kills the actual short test's rank-one
gate term for every gate and its physical value at norm one. -/
theorem primeFreeProfile_translated_upperGate (Q : ℝ → ℝ) {y : ℝ} (hy : Real.log 2 ≤ y) :
    rankOneDefect (fun x ↦ primeFreeProfile (x - y)) Q = 0 ∧ primeFreeProfile (-y) = 0 := by
  obtain ⟨_, _, hS, _⟩ := primeFreeProfile_properties
  simpa only [primeFreeProfile_negHalfMoment, mul_zero] using
    rankOneDefect_translate_of_le Q hS hy

/-- At the half-width frequency gate and reciprocal spatial scale two, the chosen
test has zero rank-one term and its total local scale correction is zero. -/
theorem primeFreeProfile_balancedHalfGate :
    rankOneDefect primeFreeProfile (upperStep (1/2)) = 0 ∧
    logLoss (upperStep (1/2)) = Real.log 2 ∧
    ∀ P : ℂ, P + ((primeFreeProfile 0 * (Real.log 2 - logLoss (upperStep (1/2))) -
      rankOneDefect primeFreeProfile (upperStep (1/2)) : ℝ) : ℂ) = P := by
  obtain ⟨_, _, hS, _, _, _, hpolar, _⟩ := primeFreeProfile_properties
  obtain ⟨hD, hL⟩ := upperStep_half_of_polar (fun x hx ↦ (hS hx).1.le) hpolar
  refine ⟨hD, hL, fun P ↦ ?_⟩
  rw [hD, hL, sub_self, mul_zero, sub_zero, Complex.ofReal_zero, add_zero]

end UpperFrequencyGates

local notation "T(" χ ", " A ")" => ((normOneIdeleClassTamagawaMeasure F) univ).toReal *
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)).re -
    primeFreeProfile 0 * heckeLogDiscriminantConductor (F := F) χ)
local notation "shortSpec(" τ ", " χ ", " φ ", " A ", " B ", " U ")" => (
  (∀ g, (φ : BruhatCompactSupport C𝔽).val g =
    ((χ : Chars(τ)).val⁻¹ g : ℂ) * (primeFreeProfile (logIdeleClassNorm F g) : ℂ)) ∧
  (φ : BruhatCompactSupport C𝔽).val 1 = (primeFreeProfile 0 : ℂ) ∧
  rawM(φ,(1 : PontryaginDual C𝔽),(-1/2)) = 0 ∧ rawM(φ,(1 : PontryaginDual C𝔽),(1/2)) = 0 ∧
  (∀ z : ℂ, M(φ,(χ).val,z) = volC * bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) (z-1/2)) ∧
  (∀ z : Sites((χ).val), 0 < v(φ,(χ).val,z)) ∧
  (∀ (w : InfinitePlace F) (u : w.Completionˣ), (A w).val u = (φ : BruhatCompactSupport C𝔽).val (archClass(w) u)) ∧
  (∀ (v : Vf) (u : (v.adicCompletion F)ˣ), (B v).val u = (φ : BruhatCompactSupport C𝔽).val (finiteClass(v) u)) ∧
  (Function.support (fun v : Vf ↦ finTerm(v,B v))).Finite ∧
  HasSum (fun v : Vf ↦ finTerm(v,B v)) (-(primeFreeProfile 0 : ℂ) * (heckeLogDiscriminantConductor (χ).val : ℂ)) ∧
  -T((χ).val,A) = full((χ).val,φ) ∧
  (∀ k : ℕ, J(k,φ,U)-T((χ).val,A) = E((χ).val,φ)+rem((χ).val,φ,k)) ∧
  Tendsto (fun k : ℕ ↦ J(k,φ,U)-T((χ).val,A)) atTop (𝓝 E((χ).val,φ)))

/-- Theorem 12.5.1.1, pp. 519–520. At a normalized character the finite-place terms
of the fixed short profile sum to minus its value at zero times the log discriminant-conductor.
Their sum with the archimedean values gives the scalar in the centered line comparison. -/
theorem exists_centeredProbe_archConductor_iff_central
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    ∃ (φ : BruhatCompactSupport C𝔽) (A : Arch) (B : FinV), shortSpec(τ,χ,φ,A,B,U) ∧
      ((∀ δ : ℝ, 0 < δ → ∃ k : ℕ, J(k,φ,U) ≤ T(χ.val,A)+δ) ↔ ∀ z : Sites(χ.val), central(z)) ∧
      ((limUnder atTop (fun k : ℕ ↦ J(k,φ,U)) ≤ T(χ.val,A)) ↔ ∀ z : Sites(χ.val), central(z)) := by
  obtain ⟨hs,hc,hS,_,_,hp,hm,hstrip⟩ := primeFreeProfile_properties
  let H (x : ℝ) : ℂ := primeFreeProfile x
  have hsC : tsupport H ⊆ Ioo (-Real.log 2) (Real.log 2) :=
    (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero primeFreeProfile).trans hS
  obtain ⟨φ,hφ⟩ := exists_characterNormTest (F := F) χ.val⁻¹ H
    (Complex.ofRealCLM.contDiff.comp hs) (hc.comp_left Complex.ofReal_zero)
  have hone : φ.val 1 = (primeFreeProfile 0 : ℂ) := by simpa [H] using hφ 1
  let f (r : ℝ) := H (Real.log r)
  have htest (g : C𝔽) : φ.val g = introTraceTest χ.val f g := by
    rw [hφ g,introTraceTest,show χ.val⁻¹ g = (χ.val g)⁻¹ from rfl,Circle.coe_inv_eq_conj]
    rfl
  have hM (z : ℂ) : M(φ,χ.val,z) = volC * bilateralLaplace H (z-1/2) := by
    have hval := (introTraceTest_mellin χ.val f φ htest (z-1/2)).2
    simpa only [modulatedFourierMellin,relativeVerticalStrip,Set.preimage_univ,
      Set.indicator_univ,f,CenterGeometry.logNormMellin] using hval
  have hoff : outside(τ,χ,φ) := fun η hη hne z ↦
    CenterGeometry.normalized_otherMoment_eq_zero τ hτ χ.val η χ.property hη hne f φ htest z
  have hpos (z : Sites(χ.val)) : 0 < v(φ,χ.val,z) := by
    rw [hM,Complex.re_ofReal_mul]
    exact mul_pos (CenterGeometry.normOneVolume_pos (F := F))
      (hstrip _ (by simpa using widthJump_strict_critical τ hτ χ z))
  have hpol : M(φ,(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧ M(φ,(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 := by
    by_cases h : (1 : PontryaginDual C𝔽) = χ.val
    · rw [h,hM,hM,zero_sub,show (1:ℂ)-1/2 = 1/2 by ring]
      simp only [H,hp,hm,mul_zero,and_self]
    · exact ⟨hoff 1 (by simp) h 0,hoff 1 (by simp) h 1⟩
  have h₀ : rawM(φ,(1 : PontryaginDual C𝔽),(-1/2)) = 0 := by
    simpa only [zero_sub,neg_div] using hpol.1
  have h₁ : rawM(φ,(1 : PontryaginDual C𝔽),(1/2)) = 0 := by
    simpa only [show (1:ℂ)-1/2 = 1/2 by ring] using hpol.2
  obtain ⟨A,B,hA,hB,_,hfull⟩ := exists_localTerms_eq_fullMoments τ hτ χ φ hoff
  obtain ⟨hsupp,hfinite⟩ := hasSum_finitePrincipalValues_characterLogProfile χ.val H hsC φ hφ B hB
  have hT : PV(A,B) = T(χ.val,A) := by
    rw [hfinite.tsum_eq,Complex.re_ofReal_mul,Complex.add_re]
    simp only [H,neg_mul,Complex.neg_re,← Complex.ofReal_mul,Complex.ofReal_re,sub_eq_add_neg]
  have hmass : -T(χ.val,A) = full(χ.val,φ) := by
    rw [← hT]
    simpa only [h₀,h₁,zero_add,zero_sub,Complex.neg_re] using hfull
  obtain ⟨hstep,ht,happrox,hlim⟩ :=
    centeredIntegral_sign τ hτ χ φ hoff hpos (-T(χ.val,A)) hmass U hU hBorel
  simp only [neg_neg] at happrox hlim
  refine ⟨φ,A,B,⟨hφ,hone,h₀,h₁,hM,hpos,hA,hB,hsupp,hfinite,hmass,?_,?_⟩,happrox,hlim⟩
  · simpa only [sub_eq_neg_add] using hstep
  · simpa only [sub_eq_neg_add] using ht

/-- Theorem 12.5.1.1, pp. 519–520. One Borel smoothing sequence for each number
field suffices at every normalized character. The upper comparison against the
archimedean and conductor scalar is equivalent to the original exterior-zero sum. -/
theorem exists_measurableSequence_archConductor_linePA_iff_exteriorZeros :
    ∃ U : ℕ → Set C𝔽, IsDPrimeSequence μ𝔽 U ∧ (∀ n, MeasurableSet (U n)) ∧
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) →
      ∃ (φ : Chars(τ) → BruhatCompactSupport C𝔽) (A : Chars(τ) → Arch) (B : Chars(τ) → FinV),
        (∀ χ : Chars(τ), shortSpec(τ,χ,φ χ,A χ,B χ,U)) ∧
        ((∀ (χ : Chars(τ)) (δ : ℝ), 0 < δ → ∃ k : ℕ, J(k,φ χ,U) ≤ T(χ.val,A χ)+δ) ↔ target(τ)) ∧
        ((∀ χ : Chars(τ), limUnder atTop (fun k : ℕ ↦ J(k,φ χ,U)) ≤ T(χ.val,A χ)) ↔ target(τ)) := by
  obtain ⟨U,hU,hBorel⟩ := exists_measurable_ideleClassDPrimeSequence F
  refine ⟨U,hU,hBorel,?_⟩
  intro τ hτ
  choose φ A B hspec happrox hlim using fun χ : Chars(τ) ↦
    exists_centeredProbe_archConductor_iff_central τ hτ χ U hU hBorel
  exact ⟨φ,A,B,hspec,(forall_congr' happrox).trans (allCentral_iff_exteriorZeros τ hτ),
    (forall_congr' hlim).trans (allCentral_iff_exteriorZeros τ hτ)⟩

end PrimeFreeCentered

end OutputOrderGeometry

section CriticalFiniteHeckeDensity

open Complex Filter Function Topology

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "completed(" χ ")" => (continuedCompletedHeckeL (F := F) χ)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor completed(χ) univ z

private theorem criticalLine_re (t : ℝ) : cl(t).re = 1 / 2 := by norm_num [Complex.mul_re]
private theorem criticalLine_im (t : ℝ) : cl(t).im = t := by norm_num [Complex.mul_im]
private theorem criticalLine_rebuild (z : ℂ) (hz : z.re = 1 / 2) : cl(z.im) = z :=
  Complex.ext ((criticalLine_re _).trans hz.symm) (criticalLine_im _)

private theorem analyticAt_criticalLine (t : ℝ) : AnalyticAt ℝ (fun x : ℝ ↦ cl(x)) t :=
  analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)

/-- Restricting a holomorphic germ to the parametrized vertical line preserves its order.
The complex unit in the real factorization is multiplied by `I ^ n`. -/
private theorem analyticOrderAt_criticalLine {A : ℂ → ℂ} {t : ℝ} (hA : AnalyticAt ℂ A cl(t)) :
    AnalyticAt ℝ (fun x : ℝ ↦ A cl(x)) t ∧
    analyticOrderAt (fun x : ℝ ↦ A cl(x)) t = analyticOrderAt A cl(t) := by
  have hline := analyticAt_criticalLine t
  have hres : AnalyticAt ℝ (fun x : ℝ ↦ A cl(x)) t :=
    (hA.restrictScalars (𝕜 := ℝ)).comp (f := fun x : ℝ ↦ cl(x)) hline
  refine ⟨hres, ?_⟩
  by_cases htop : analyticOrderAt A cl(t) = ⊤
  · rw [htop, analyticOrderAt_eq_top]
    exact hline.continuousAt.tendsto.eventually (analyticOrderAt_eq_top.mp htop)
  let n := analyticOrderNatAt A cl(t)
  have hn : analyticOrderAt A cl(t) = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨u, hu, hu0, hfac⟩ := hA.analyticOrderAt_eq_natCast.mp hn
  rw [hn, hres.analyticOrderAt_eq_natCast]
  refine ⟨fun x : ℝ ↦ I ^ n * u cl(x),
    analyticAt_const.mul ((hu.restrictScalars (𝕜 := ℝ)).comp (f := fun x : ℝ ↦ cl(x)) hline),
    mul_ne_zero (pow_ne_zero _ I_ne_zero) hu0, ?_⟩
  filter_upwards [hline.continuousAt.tendsto.eventually hfac] with x hx
  have he : cl(x) - cl(t) = ((x - t : ℝ) : ℂ) * I := by push_cast; ring
  rw [hx, he, smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, mul_pow, mul_assoc]

private theorem analyticAt_completedHecke_of_openStrip (χ : PontryaginDual C𝔽) {z : ℂ}
    (ha : 0 < z.re) (hb : z.re < 1) : AnalyticAt ℂ completed(χ) z := by
  obtain ⟨hm, he⟩ := continuedCompletedHeckeL_spec χ
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨r, ⟨-, -, -, hhol⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _ hm he hχ
    apply hhol z
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff]
    rintro (h | h)
    · have hr := congrArg Complex.re h
      simp [Complex.mul_re] at hr
      linarith
    · have hr := congrArg Complex.re h
      simp [Complex.mul_re] at hr
      linarith
  · exact (completedHeckeL_continuation_entire χ _ hm he hχ).analyticAt z

private theorem completedHecke_order_ne_top (χ : PontryaginDual C𝔽) (z : ℂ) :
    meromorphicOrderAt completed(χ) z ≠ ⊤ := by
  obtain ⟨hm, he⟩ := continuedCompletedHeckeL_spec χ
  have h₂ : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hval : completed(χ) 2 ≠ 0 := by
    rw [he ⟨2, h₂⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans h₂))
      (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨2, h₂⟩)
  apply hm.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z)
  rw [(hm (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hval]
  exact WithTop.coe_ne_top

/-- The finite Hecke function on the critical line, formed by removing the archimedean
gamma factor from the specified meromorphic continuation of the completed function. -/
def criticalFiniteHeckeL (χ : PontryaginDual C𝔽) (t : ℝ) : ℂ :=
  completed(χ) cl(t) * (heckeGammaFactor χ cl(t))⁻¹

/-- Every normal-form continuation of the finite Euler product agrees with
`criticalFiniteHeckeL` at every point of the critical line. -/
theorem criticalFiniteHeckeL_eq_continuation (χ : PontryaginDual C𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (he : ∀ z : {z : ℂ // 1 < z.re}, L z = finiteHeckeL χ z) :
    criticalFiniteHeckeL χ = fun t : ℝ ↦ L cl(t) := by
  let M (z : ℂ) := completed(χ) z * (heckeGammaFactor χ z)⁻¹
  obtain ⟨hΛ, hΛe⟩ := continuedCompletedHeckeL_spec χ
  have hM : MeromorphicOn M univ := fun z hz ↦ (hΛ hz).meromorphicAt.mul
    ((differentiable_inv_heckeGammaFactor χ).analyticAt z).meromorphicAt
  have hEq := heckeEulerProductOutside_eq_finite_nf_eq L M hL.meromorphicOn hM (fun z hz ↦ by
    rw [he ⟨z, hz⟩]
    dsimp only [M]
    rw [hΛe ⟨z, hz⟩]
    change finiteHeckeL χ ⟨z, hz⟩ = heckeGammaFactor χ z * finiteHeckeL χ ⟨z, hz⟩ * _
    rw [mul_right_comm, mul_inv_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)),
      one_mul])
  rw [toMeromorphicNFOn_eq_self.mpr hL] at hEq
  funext t
  have hpos : 0 < cl(t).re := by rw [criticalLine_re]; norm_num
  have hlt : cl(t).re < 1 := by rw [criticalLine_re]; norm_num
  have hreg : AnalyticAt ℂ M cl(t) := (analyticAt_completedHecke_of_openStrip χ hpos hlt).mul
    ((differentiable_inv_heckeGammaFactor χ).analyticAt _)
  rw [hEq, toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr hreg.meromorphicNFAt]
  rfl

/-- The finite critical-line function is real analytic with a nonzero germ. Its real
analytic order, including at multiple zeros, equals the integer divisor of the completed
Hecke function at the corresponding complex point. -/
theorem criticalFiniteHeckeL_order (χ : PontryaginDual C𝔽) (t : ℝ) :
    AnalyticAt ℝ (criticalFiniteHeckeL χ) t ∧
    ¬ (∀ᶠ u in 𝓝 t, criticalFiniteHeckeL χ u = 0) ∧
    (analyticOrderNatAt (criticalFiniteHeckeL χ) t : ℤ) = ord(χ, cl(t)) := by
  let M := completed(χ) * (fun z ↦ (heckeGammaFactor χ z)⁻¹)
  have hpos : 0 < cl(t).re := by rw [criticalLine_re]; norm_num
  have hlt : cl(t).re < 1 := by rw [criticalLine_re]; norm_num
  have hΛ := analyticAt_completedHecke_of_openStrip χ hpos hlt
  have hΓ := (differentiable_inv_heckeGammaFactor χ).analyticAt cl(t)
  have hunit : (heckeGammaFactor χ cl(t))⁻¹ ≠ 0 :=
    inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hpos)
  have hM : AnalyticAt ℂ M cl(t) := hΛ.mul hΓ
  obtain ⟨hreal, hv⟩ := analyticOrderAt_criticalLine hM
  have hA : analyticOrderAt (criticalFiniteHeckeL χ) t = analyticOrderAt completed(χ) cl(t) := by
    change analyticOrderAt (fun u : ℝ ↦ M cl(u)) t = _
    rw [hv, show analyticOrderAt M cl(t) = _ + _ from analyticOrderAt_mul hΛ hΓ,
      hΓ.analyticOrderAt_eq_zero.mpr hunit, add_zero]
  have hfinite : analyticOrderAt (criticalFiniteHeckeL χ) t ≠ ⊤ := by
    intro ht
    apply completedHecke_order_ne_top χ cl(t)
    rw [hΛ.meromorphicOrderAt_eq, ← hA, ht, ENat.map_top]
  refine ⟨hreal, fun h ↦ hfinite (analyticOrderAt_eq_top.mpr h), ?_⟩
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _),
    hΛ.meromorphicOrderAt_eq, ← hA, ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_natCast,
    WithTop.untop₀_coe]

private theorem critical_zero_moments_eq (χ : PontryaginDual C𝔽) (g : ℝ → ℝ) :
    (∑' t : {t : ℝ // criticalFiniteHeckeL χ t = 0},
      (analyticOrderNatAt (criticalFiniteHeckeL χ) t.val : ℝ) * g t.val) =
      ∑' z : {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}, ((ord(χ,z.val)).toNat : ℝ) * g z.val.im := by
  classical
  let f := criticalFiniteHeckeL χ
  let Z := {t : ℝ // f t = 0}
  let C := {z : ℂ // 0 < ord(χ, z) ∧ z.re = 1 / 2}
  have hlocal (t : ℝ) := criticalFiniteHeckeL_order χ t
  have hfin (t : ℝ) : analyticOrderAt f t ≠ ⊤ := fun ht ↦ (hlocal t).2.1 (analyticOrderAt_eq_top.mp ht)
  have hpos (t : ℝ) : f t = 0 ↔ 0 < ord(χ, cl(t)) := by
    rw [← (hlocal t).2.2]
    rw [← (hlocal t).1.analyticOrderAt_ne_zero, ← Nat.cast_analyticOrderNatAt (hfin t)]
    simp [f, Nat.pos_iff_ne_zero]
  let e : Z ≃ C :=
    { toFun := fun t ↦ ⟨cl(t.val), (hpos t).mp t.2, criticalLine_re _⟩
      invFun := fun z ↦ ⟨z.val.im, (hpos _).mpr (by rw [criticalLine_rebuild _ z.2.2]; exact z.2.1)⟩
      left_inv := fun t ↦ Subtype.ext (criticalLine_im _)
      right_inv := fun z ↦ Subtype.ext (criticalLine_rebuild _ z.2.2) }
  have hsum : (∑' t : Z, (analyticOrderNatAt f t.val : ℝ) * g t.val) =
      ∑' z : C, ((ord(χ, z.val)).toNat : ℝ) * g z.val.im := by
    calc
      _ = ∑' t : Z, ((ord(χ, (e t).val)).toNat : ℝ) * g (e t).val.im := by
        apply tsum_congr
        intro t
        change _ = ((ord(χ, cl(t.val))).toNat : ℝ) * g cl(t.val).im
        rw [criticalLine_im, ← (hlocal t).2.2, Int.toNat_natCast]
      _ = _ := e.tsum_eq (fun z : C ↦ ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)
  exact hsum

/-- Integrating the finite Hecke function's regularized logarithmic-derivative density
against a signed compact continuous test recovers the completed divisor on exactly its
occupied central sites, with full multiplicities. -/
theorem tendsto_integral_criticalFiniteHeckeL (χ : PontryaginDual C𝔽) {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun η : ℝ ↦ ∫ t, g t * analyticZeroDensity (criticalFiniteHeckeL χ) η t) (𝓝[>] 0)
      (𝓝 (∑' z : {z : ℂ // 0 < ord(χ, z) ∧ z.re = 1 / 2},
        ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)) := by
  classical
  let f := criticalFiniteHeckeL χ
  let C := {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}
  have hlocal (t : ℝ) := criticalFiniteHeckeL_order χ t
  have hfin (t : ℝ) : analyticOrderAt f t ≠ ⊤ := fun ht ↦ (hlocal t).2.1 (analyticOrderAt_eq_top.mp ht)
  have hlim := tendsto_integral_analyticZeroDensity (f := f) hg hgc
    (fun t _ ↦ (hlocal t).1) (fun t _ ↦ hfin t)
  have hsum := critical_zero_moments_eq χ g
  change Tendsto (fun η : ℝ ↦ ∫ t, g t * analyticZeroDensity f η t) (𝓝[>] 0)
    (𝓝 (∑' z : C, ((ord(χ, z.val)).toNat : ℝ) * g z.val.im))
  rw [← hsum]
  exact hlim

end CriticalFiniteHeckeDensity

section CriticalSchwartzDensity

open Complex Filter Function Topology
open scoped _root_.SchwartzMap ContDiff ENNReal FourierTransform NNReal

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "central(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ z.re = 1 / 2}
local notation "mult(" χ ", " z ")" => (ord(χ, (z : ℂ))).toNat
local notation "density(" χ ", " η ")" => analyticZeroDensity (criticalFiniteHeckeL χ) η

/-- The positive atomic measure on the ordinates of the central zeros of the completed
Hecke function. Each point has mass equal to its full analytic multiplicity. -/
def criticalHeckeZeroMeasure (χ : PontryaginDual C𝔽) : Measure ℝ :=
  Measure.sum fun z : central(χ) ↦ (mult(χ, z) : ℝ≥0∞) • Measure.dirac z.val.im

private theorem criticalHeckeZeroMeasure_finite_sites (χ : PontryaginDual C𝔽)
    {K : Set ℝ} (hK : IsCompact K) : {z : central(χ) | z.val.im ∈ K}.Finite := by
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
  have hloc : LocallyFiniteSupport (fun z ↦ D z) :=
    fun z ↦ D.supportLocallyFiniteWithinDomain z (mem_univ z)
  have hline : Continuous (fun t : ℝ ↦ cl(t)) := by fun_prop
  have hf := hloc.finite_inter_support_of_isCompact (hK.image hline)
  refine (hf.preimage (f := fun z : central(χ) ↦ z.val) Subtype.val_injective.injOn).subset ?_
  intro z hz
  exact ⟨⟨z.val.im, hz, criticalLine_rebuild _ z.property.2⟩, z.property.1.ne'⟩

/-- Local finiteness of the completed divisor makes the central atomic measure finite on
every compact set of ordinates. -/
instance criticalHeckeZeroMeasure_finiteOnCompacts (χ : PontryaginDual C𝔽) :
    IsFiniteMeasureOnCompacts (criticalHeckeZeroMeasure χ) where
  lt_top_of_isCompact {K} hK := by
    classical
    let hfin := criticalHeckeZeroMeasure_finite_sites χ hK
    have hv (z : central(χ)) : ((mult(χ, z) : ℝ≥0∞) • Measure.dirac z.val.im : Measure ℝ) K =
        if z.val.im ∈ K then (mult(χ, z) : ℝ≥0∞) else 0 := by
      by_cases h : z.val.im ∈ K <;> simp [Measure.dirac_apply' _ hK.measurableSet, h]
    rw [criticalHeckeZeroMeasure, Measure.sum_apply _ hK.measurableSet, tsum_congr hv]
    rw [tsum_eq_sum (s := hfin.toFinset) (f := fun z : central(χ) ↦
      if z.val.im ∈ K then (mult(χ, z) : ℝ≥0∞) else 0) (fun z hz ↦ by
        simp [show z.val.im ∉ K from fun hm ↦ hz (hfin.mem_toFinset.mpr hm)])]
    apply ENNReal.sum_lt_top.mpr
    intro z _
    split <;> finiteness

/-- Integrating against the central zero measure is an unconditionally convergent sum over
the exact complex central-site subtype, with full multiplicities and ordinate evaluation. -/
theorem hasSum_criticalHeckeZeroMeasure (χ : PontryaginDual C𝔽) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E)
    (hg : Integrable g (criticalHeckeZeroMeasure χ)) :
    HasSum (fun z : central(χ) ↦ (mult(χ, z) : ℝ) • g z.val.im)
      (∫ t, g t ∂criticalHeckeZeroMeasure χ) := by
  unfold criticalHeckeZeroMeasure at hg ⊢
  simpa only [integral_smul_measure, integral_dirac, ENNReal.toReal_natCast] using
    hasSum_integral_measure hg

/-- The critical finite Hecke density is Borel measurable for every parameter. -/
theorem criticalFiniteHeckeL_density_measurable (χ : PontryaginDual C𝔽) (η : ℝ) :
    Measurable (density(χ, η)) := by
  have hc : Continuous (criticalFiniteHeckeL χ) :=
    continuous_iff_continuousAt.mpr fun t ↦ (criticalFiniteHeckeL_order χ t).1.continuousAt
  have hd : Continuous (deriv (criticalFiniteHeckeL χ)) :=
    continuous_iff_continuousAt.mpr fun t ↦ (criticalFiniteHeckeL_order χ t).1.deriv.continuousAt
  unfold analyticZeroDensity
  fun_prop

private theorem criticalHeckeDensity_norm_le (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ‖density(χ, η) t‖ ≤ 1 / (Real.pi * η) := by
  rw [Real.norm_of_nonneg (by unfold analyticZeroDensity; positivity)]
  unfold analyticZeroDensity
  by_cases hd : deriv (criticalFiniteHeckeL χ) t = 0
  · simp only [hd, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
    positivity
  have hs : 0 < η ^ 2 * ‖deriv (criticalFiniteHeckeL χ) t‖ ^ 2 := by positivity
  calc
    _ ≤ (η / Real.pi) * ‖deriv (criticalFiniteHeckeL χ) t‖ ^ 2 /
        (η ^ 2 * ‖deriv (criticalFiniteHeckeL χ) t‖ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hs (le_add_of_nonneg_left (sq_nonneg _))
    _ = _ := by field_simp [Real.pi_ne_zero, hη.ne', norm_ne_zero_iff.mpr hd]

private theorem criticalHeckeDensity_integrableOn_compact (χ : PontryaginDual C𝔽)
    {η : ℝ} (hη : 0 < η) {K : Set ℝ} (hK : IsCompact K) : IntegrableOn (density(χ, η)) K := by
  have hc : IntegrableOn (fun _ : ℝ ↦ 1 / (Real.pi * η)) K := integrableOn_const hK.measure_ne_top
  exact hc.mono' (criticalFiniteHeckeL_density_measurable χ η).aestronglyMeasurable
    (ae_of_all _ (criticalHeckeDensity_norm_le χ hη))

/-- At every positive scale the signed Schwartz pairing is an absolutely convergent
Lebesgue integral. -/
theorem integrable_schwartz_mul_criticalFiniteHeckeL_density (χ : PontryaginDual C𝔽)
    {η : ℝ} (hη : 0 < η) (g : 𝓢(ℝ, ℝ)) : Integrable (fun t ↦ g t * density(χ, η) t) := by
  have hmajor : Integrable (fun t ↦ ‖g t‖ * (1 / (Real.pi * η))) := g.integrable.norm.mul_const _
  apply hmajor.mono' (g.continuous.measurable.mul (criticalFiniteHeckeL_density_measurable χ η)).aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by
    change ‖g t * density(χ, η) t‖ ≤ _
    rw [_root_.norm_mul]
    exact mul_le_mul_of_nonneg_left (criticalHeckeDensity_norm_le χ hη t) (norm_nonneg _)

private def criticalHeckeDensityMeasure (χ : PontryaginDual C𝔽) (η : ℝ) : Measure ℝ :=
  volume.withDensity (fun t ↦ ENNReal.ofReal (density(χ, η) t))

private theorem criticalHeckeDensityMeasure_pairing (χ : PontryaginDual C𝔽)
    {η : ℝ} (hη : 0 < η) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ t, g t ∂criticalHeckeDensityMeasure χ η) = ∫ t, density(χ, η) t • g t := by
  unfold criticalHeckeDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (criticalFiniteHeckeL_density_measurable χ η).aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun t ↦ by
    change (ENNReal.ofReal (density(χ, η) t)).toReal • g t = density(χ, η) t • g t
    rw [ENNReal.toReal_ofReal (by unfold analyticZeroDensity; positivity)])

private theorem criticalHeckeDensityMeasure_compact (χ : PontryaginDual C𝔽) (g : ℝ → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun η : ℝ ↦ ∫ t, g t ∂criticalHeckeDensityMeasure χ η) (𝓝[>] 0)
      (𝓝 (∫ t, g t ∂criticalHeckeZeroMeasure χ)) := by
  have hsum := (hasSum_criticalHeckeZeroMeasure χ g (hg.integrable_of_hasCompactSupport hgc)).tsum_eq
  simp only [smul_eq_mul] at hsum
  have h := tendsto_integral_criticalFiniteHeckeL χ hg hgc
  rw [hsum] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hη
  rw [criticalHeckeDensityMeasure_pairing χ hη]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ mul_comm _ _

private theorem criticalHeckeDensityMeasure_window (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 < η) (k : ℤ) :
    criticalHeckeDensityMeasure χ η (Icc (k : ℝ) (k + 1)) =
      ENNReal.ofReal (∫ t in Icc (k : ℝ) (k + 1), density(χ, η) t) := by
  rw [criticalHeckeDensityMeasure, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (criticalHeckeDensity_integrableOn_compact χ hη isCompact_Icc)]
  exact ae_of_all _ fun t ↦ by unfold analyticZeroDensity; positivity

private theorem integrable_schwartz_of_criticalWindow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : Measure ℝ) (C : ℝ≥0) (d : ℕ)
    (hν : ∀ k : ℤ, ν (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d))
    (g : 𝓢(ℝ, E)) : Integrable g ν := by
  let p : Seminorm ℝ 𝓢(ℝ, E) := (Finset.Iic (d + 2, 0)).sup
    (fun m ↦ _root_.SchwartzMap.seminorm ℝ m.1 m.2)
  have hb (x : ℝ) : (1 + |x|) ^ (d + 2) * ‖g x‖ ≤ 2 ^ (d + 2) * p g := by
    simpa [p, Real.norm_eq_abs] using
      _root_.SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 2, 0)) (n := 0)
        le_rfl le_rfl g x
  exact (integral_norm_le_of_polynomial_window_mass ν C d hν _ g.continuous.aestronglyMeasurable _
    (mul_nonneg (by positivity) (apply_nonneg _ _)) hb).1

/-- The regularized finite-Hecke critical-line density converges on every real Schwartz
test to the sum of all central test moments with full analytic orders. A single eventual
polynomial bound on its unit-window masses suffices. -/
theorem tendsto_integral_criticalFiniteHeckeL_schwartz_of_window_bound (χ : PontryaginDual C𝔽)
    (C : ℝ≥0) (d : ℕ)
    (hwin : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ k : ℤ, (∫ t in Icc (k : ℝ) (k + 1), density(χ, η) t) ≤
      (C : ℝ) * (1 + |(k : ℝ)|) ^ d) (g : 𝓢(ℝ, ℝ)) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |g z.val.im|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t, g t * density(χ, η) t) (𝓝[>] 0)
      (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * g z.val.im)) := by
  let ν := criticalHeckeZeroMeasure χ
  let μ := criticalHeckeDensityMeasure χ
  let D : ℝ≥0 := 3 * 2 ^ d * C
  have hD : (D : ℝ) = 3 * 2 ^ d * (C : ℝ) := by simp [D]
  have hC : (C : ℝ) ≤ D := by
    rw [hD]
    have hd : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    calc
      _ = 1 * (C : ℝ) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) C.coe_nonneg
  have hm : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ k : ℤ, μ η (Icc (k : ℝ) (k + 1)) ≤
      ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d) := by
    filter_upwards [hwin, self_mem_nhdsWithin] with η h hη k
    exact (criticalHeckeDensityMeasure_window χ hη k).trans_le (ENNReal.ofReal_le_ofReal (h k))
  have hcomp (f : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport (f : ℝ → ℝ)) :=
    criticalHeckeDensityMeasure_compact χ f f.continuous hc
  have hn (k : ℤ) : ν (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((D : ℝ) * (1 + |(k : ℝ)|) ^ d) := by
    rw [hD]
    exact polynomial_window_mass_of_tendsto_compact _ μ ν C d hm hcomp k
  have hi := integrable_schwartz_of_criticalWindow ν D d hn g
  have hs := hasSum_criticalHeckeZeroMeasure χ g hi
  simp only [smul_eq_mul] at hs
  have habs := (show Integrable g (Measure.sum (fun z : central(χ) ↦
    (mult(χ, z) : ℝ≥0∞) • Measure.dirac z.val.im)) from hi).summable_of_dirac
  refine ⟨by simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs] using habs, ?_⟩
  rw [hs.tsum_eq]
  have hlim := tendsto_integral_schwartz_of_polynomial_window_mass _ μ ν D d
    (hm.mono fun η hh k ↦ (hh k).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC (by positivity)))) hn hcomp g
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hη
  change (∫ t, g t ∂criticalHeckeDensityMeasure χ η) = _
  rw [criticalHeckeDensityMeasure_pairing χ hη]
  exact integral_congr_ae (ae_of_all _ fun t ↦ mul_comm _ _)

/-- A smooth compactly supported log-profile gives precisely the centered Laplace moments
of the complex central sites. The regularized integral uses only the real vertical trace. -/
theorem tendsto_integral_criticalFiniteHeckeL_centeredLaplace_of_window_bound (χ : PontryaginDual C𝔽)
    (C : ℝ≥0) (d : ℕ)
    (hwin : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ k : ℤ, (∫ t in Icc (k : ℝ) (k + 1), density(χ, η) t) ≤
      (C : ℝ) * (1 + |(k : ℝ)|) ^ d)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |(bilateralLaplace H (z.val - 1 / 2)).re|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t : ℝ, (bilateralLaplace H ((t : ℂ) * I)).re * density(χ, η) t)
      (𝓝[>] 0) (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * (bilateralLaplace H (z.val - 1 / 2)).re)) := by
  obtain ⟨g, hg⟩ := exists_realSchwartz_eq_bilateralLaplace_axis_re hHc hH
  have hz (z : central(χ)) : (z.val.im : ℂ) * I = z.val - 1 / 2 := by
    linear_combination criticalLine_rebuild z.val z.property.2
  simpa only [hg, hz] using tendsto_integral_criticalFiniteHeckeL_schwartz_of_window_bound χ C d hwin g

end CriticalSchwartzDensity

section ActualHeckeWindows

open Complex Filter MeasureTheory NumberField Set Topology
open scoped NNReal

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "W(" j ")" => Icc ((j : ℤ) : ℝ) ((j : ℝ) + 1)
local notation "D(" χ ", " η ")" => analyticZeroDensity (criticalFiniteHeckeL χ) η

/-- The density is nonnegative for all nonnegative regularization parameters. -/
theorem criticalFiniteHeckeL_density_nonneg (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 ≤ η) (t : ℝ) :
    0 ≤ D(χ, η) t := by unfold analyticZeroDensity; positivity

private theorem density_le_inverse_parameter (f : ℝ → ℂ) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    analyticZeroDensity f η t ≤ 1 / (Real.pi * η) := by
  unfold analyticZeroDensity
  apply div_le_of_le_mul₀ (by positivity) (by positivity)
  calc
    _ = 1 / (Real.pi * η) * (η ^ 2 * ‖deriv f t‖ ^ 2) := by
      field_simp [Real.pi_ne_zero, hη.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (by positivity)

private theorem criticalDensity_integrableOn (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 < η) (j : ℤ) :
    IntegrableOn D(χ, η) W(j) := by
  have hc : IntegrableOn (fun _ : ℝ ↦ 1 / (Real.pi * η)) W(j) := integrableOn_const (by simp)
  apply hc.mono' (criticalFiniteHeckeL_density_measurable χ η).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (criticalFiniteHeckeL_density_nonneg χ hη.le t)]
  exact density_le_inverse_parameter _ hη t

private theorem density_eq_regularizedSquare {f : ℝ → ℂ} {η t : ℝ} (ht : f t ≠ 0) :
    analyticZeroDensity f η t = Real.pi⁻¹ *
      (η * (‖deriv f t‖ / ‖f t‖) ^ 2 / (1 + η ^ 2 * (‖deriv f t‖ / ‖f t‖) ^ 2)) := by
  have ha : 0 < ‖f t‖ := norm_pos_iff.mpr ht
  have hb : 0 < ‖f t‖ ^ 2 + η ^ 2 * ‖deriv f t‖ ^ 2 := by positivity
  have hc : 0 < 1 + η ^ 2 * (‖deriv f t‖ / ‖f t‖) ^ 2 := by positivity
  unfold analyticZeroDensity
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']

private theorem criticalRelativeDerivative (χ : PontryaginDual C𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (he : ∀ z : {z : ℂ // 1 < z.re}, L z = finiteHeckeL χ z)
    (t : ℝ) (hn : L ⟨1 / 2, t⟩ ≠ 0) :
    criticalFiniteHeckeL χ t ≠ 0 ∧
      ‖deriv (criticalFiniteHeckeL χ) t‖ / ‖criticalFiniteHeckeL χ t‖ = ‖logDeriv L ⟨1 / 2, t⟩‖ := by
  have hcl : cl(t) = (⟨1 / 2, t⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  rw [← hcl] at hn ⊢
  have hnf := hL (mem_univ cl(t))
  have ha := hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hnf.meromorphicOrderAt_eq_zero_iff.mpr hn).ge
  have hp : HasDerivAt (fun u : ℝ ↦ cl(u)) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (1 / 2 : ℂ)
  have hd := ha.differentiableAt.hasDerivAt.scomp (h := fun u : ℝ ↦ cl(u)) t hp
  rw [criticalFiniteHeckeL_eq_continuation χ L hL he]
  refine ⟨hn, ?_⟩
  change ‖deriv (L ∘ (fun u : ℝ ↦ cl(u))) t‖ / ‖L cl(t)‖ = _
  rw [hd.deriv, logDeriv_apply, norm_div]
  simp [smul_eq_mul]

private theorem criticalDensity_high_windows (χ : PontryaginDual C𝔽) :
    ∃ A > (0 : ℝ), ∃ J > (0 : ℝ), ∀ j : ℤ, J ≤ |(j : ℝ)| →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∫ t in W(j), D(χ, η) t ≤ A * (1 + |(j : ℝ)|) ^ 2 := by
  classical
  obtain ⟨L, hL, he⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨C, hC, J, hJ, hwindow⟩ := finiteHeckeL_continuation_highHeight_unitWindow_logDeriv χ L hL he
  let A := Real.pi⁻¹ * (4 + 2 * Real.pi) * C ^ 2
  refine ⟨A, by dsimp [A]; positivity, J, hJ, ?_⟩
  intro j hj η hη hη'
  obtain ⟨_, _, S, _, horder, hmass, _, hrect⟩ := hwindow (j : ℝ) hj
  let f := criticalFiniteHeckeL χ
  let q (t : ℝ) := ‖deriv f t‖ / ‖f t‖
  let m := analyticOrderNatAt L
  let B := C * Real.log (2 + |(j : ℝ)|)
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t ↦
    (criticalFiniteHeckeL_order χ t).1.continuousAt
  have hd : Continuous (deriv f) := continuous_iff_continuousAt.mpr fun t ↦
    (criticalFiniteHeckeL_order χ t).1.deriv.continuousAt
  have hq : Measurable q := hd.measurable.norm.div hf.measurable.norm
  have hgood : ∀ᵐ t ∂volume.restrict W(j), f t ≠ 0 ∧ 0 ≤ q t ∧
      q t ≤ B + ∑ ρ ∈ S, (m ρ : ℝ) / |t - ρ.im| := by
    have hne : ∀ᵐ t ∂volume.restrict W(j), ∀ ρ ∈ S, t ≠ ρ.im :=
      S.eventually_all.mpr (fun ρ _ ↦ ae_restrict_of_ae (volume.ae_ne ρ.im))
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc, hne] with t ht ha
    have hz := (hrect (1 / 2) ⟨le_rfl, by norm_num⟩ t ht ha).2
    have hder := criticalRelativeDerivative χ L hL he t hz.1
    exact ⟨hder.1, div_nonneg (norm_nonneg _) (norm_nonneg _), hder.2.le.trans hz.2⟩
  have hraw := integral_regularizedSquare_Icc_le_uniform S Complex.im m (j : ℝ) B η hη hη' q
    hq.aemeasurable (hgood.mono fun _ ht ↦ ht.2)
  have heq : (∫ t in W(j), D(χ, η) t) =
      Real.pi⁻¹ * ∫ t in W(j), η * (q t) ^ 2 / (1 + η ^ 2 * (q t) ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (hgood.mono fun _ ht ↦ density_eq_regularizedSquare ht.1)
  have hcard : (S.card : ℝ) ≤ ∑ ρ ∈ S, (m ρ : ℝ) := by
    calc
      _ = ∑ _ρ ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun ρ hρ ↦ by exact_mod_cast (horder ρ hρ).1
  have hB₀ : 0 ≤ B := (Finset.sum_nonneg fun ρ (_ : ρ ∈ S) ↦ (Nat.cast_nonneg (m ρ) : (0 : ℝ) ≤ _)).trans hmass
  have hprod := mul_le_mul hmass (hcard.trans hmass) (Nat.cast_nonneg S.card) hB₀
  have hrhs : 4 * B ^ 2 + 2 * Real.pi * (∑ ρ ∈ S, (m ρ : ℝ)) * S.card ≤
      (4 + 2 * Real.pi) * B ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hlog : Real.log (2 + |(j : ℝ)|) ≤ 1 + |(j : ℝ)| := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |(j : ℝ)|)]
  have hbig := pow_le_pow_left₀ hB₀ (mul_le_mul_of_nonneg_left hlog hC.le) 2
  calc
    _ = _ := heq
    _ ≤ Real.pi⁻¹ * ((4 + 2 * Real.pi) * B ^ 2) :=
      mul_le_mul_of_nonneg_left (hraw.trans hrhs) (by positivity)
    _ ≤ Real.pi⁻¹ * ((4 + 2 * Real.pi) * (C * (1 + |(j : ℝ)|)) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbig (by positivity)) (by positivity)
    _ = _ := by dsimp [A]; ring

private theorem criticalDensity_bounded_windows (χ : PontryaginDual C𝔽) {J : ℝ} (hJ : 0 < J) :
    ∃ M > (0 : ℝ), ∀ j : ℤ, |(j : ℝ)| < J → ∀ η : ℝ, 0 < η → ∫ t in W(j), D(χ, η) t ≤ M := by
  let b : ContDiffBump (0 : ℝ) := ⟨J + 1, J + 2, by linarith, by linarith⟩
  have hone (j : ℤ) (hj : |(j : ℝ)| < J) (t : ℝ) (ht : t ∈ W(j)) : b t = 1 := by
    apply b.one_of_mem_closedBall
    change |t - 0| ≤ J + 1
    rw [sub_zero]
    obtain ⟨hleft, hright⟩ := abs_lt.mp hj
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbi (η : ℝ) (hη : 0 < η) : Integrable (fun t ↦ b t * D(χ, η) t) := by
    apply ((b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport).mul_const
      (1 / (Real.pi * η))).mono' (b.continuous.measurable.mul
        (criticalFiniteHeckeL_density_measurable χ η)).aestronglyMeasurable
    filter_upwards with t
    change ‖b t * D(χ, η) t‖ ≤ b t * (1 / (Real.pi * η))
    rw [Real.norm_of_nonneg (mul_nonneg (b.nonneg' t) (criticalFiniteHeckeL_density_nonneg χ hη.le t))]
    exact mul_le_mul_of_nonneg_left (density_le_inverse_parameter _ hη t) (b.nonneg' t)
  have htest (j : ℤ) (hj : |(j : ℝ)| < J) (η : ℝ) (hη : 0 < η) :
      ∫ t in W(j), D(χ, η) t ≤ ∫ t, b t * D(χ, η) t := by
    calc
      _ = ∫ t in W(j), b t * D(χ, η) t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        change D(χ, η) t = b t * D(χ, η) t
        rw [hone j hj t ht, one_mul]
      _ ≤ _ := setIntegral_le_integral (hbi η hη) (ae_of_all _ fun t ↦
        mul_nonneg (b.nonneg' t) (criticalFiniteHeckeL_density_nonneg χ hη.le t))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ᶠ η : ℝ in 𝓝[>] 0, (∫ t, b t * D(χ, η) t) ≤ M := by
    have hlim := tendsto_integral_criticalFiniteHeckeL χ b.continuous b.hasCompactSupport
    exact ⟨_, hlim.eventually_le_const (lt_add_one _)⟩
  obtain ⟨δ, hδ, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hM
  refine ⟨max M (1 / (Real.pi * δ)), (by positivity : 0 < 1 / (Real.pi * δ)).trans_le
    (le_max_right _ _), ?_⟩
  intro j hj η hη
  by_cases hs : η < δ
  · exact (htest j hj η hη).trans ((hsmall ⟨hη, hs⟩).trans (le_max_left _ _))
  · apply le_trans _ (le_max_right _ _)
    have hc : IntegrableOn (fun _ : ℝ ↦ 1 / (Real.pi * η)) W(j) := integrableOn_const (by simp)
    calc
      _ ≤ ∫ _t in W(j), 1 / (Real.pi * η) := integral_mono (criticalDensity_integrableOn χ hη j) hc
        (density_le_inverse_parameter _ hη)
      _ = 1 / (Real.pi * η) := by simp [measureReal_def, Real.volume_Icc]
      _ ≤ _ := one_div_le_one_div_of_le (mul_pos Real.pi_pos hδ)
        (mul_le_mul_of_nonneg_left (le_of_not_gt hs) Real.pi_pos.le)

/-- One quadratic bound controls the regularized finite Hecke density on every
integer unit window simultaneously for every parameter in `(0, 1]`. -/
theorem criticalFiniteHeckeL_polynomial_window_mass (χ : PontryaginDual C𝔽) :
    ∃ C : ℝ≥0, ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ j : ℤ,
      IntegrableOn D(χ, η) W(j) ∧
        ∫ t in W(j), D(χ, η) t ≤ (C : ℝ) * (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨A, hA, J, hJ, hhigh⟩ := criticalDensity_high_windows χ
  obtain ⟨M, hM, hlow⟩ := criticalDensity_bounded_windows χ hJ
  refine ⟨⟨max A M, hA.le.trans (le_max_left _ _)⟩, fun η hη hη' j ↦
    ⟨criticalDensity_integrableOn χ hη j, ?_⟩⟩
  change _ ≤ max A M * (1 + |(j : ℝ)|) ^ 2
  by_cases hj : J ≤ |(j : ℝ)|
  · exact (hhigh j hj η hη hη').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · apply (hlow j (lt_of_not_ge hj) η hη).trans
    have hOne := one_le_pow₀ (show 1 ≤ 1 + |(j : ℝ)| by linarith [abs_nonneg (j : ℝ)]) (n := 2)
    exact (le_max_right A M).trans (le_mul_of_one_le_right (hM.le.trans (le_max_right _ _)) hOne)

/-- The simultaneous window bound in the form used to extend compact-test
convergence to Schwartz tests by polynomial mass control. -/
theorem criticalFiniteHeckeL_eventually_polynomial_window_mass (χ : PontryaginDual C𝔽) :
    ∃ C : ℝ≥0, ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ j : ℤ, IntegrableOn D(χ, η) W(j) ∧
      ∫ t in W(j), D(χ, η) t ≤ (C : ℝ) * (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨C, hC⟩ := criticalFiniteHeckeL_polynomial_window_mass χ
  refine ⟨C, ?_⟩
  have hnear : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  filter_upwards [hpos, hnear.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with η hη hη'
  exact hC η hη hη'

end ActualHeckeWindows

section CriticalSchwartzLimits

open Complex Filter MeasureTheory NumberField Set Topology
open scoped _root_.SchwartzMap ContDiff

local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "central(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ Complex.re z = 1 / 2}
local notation "mult(" χ ", " z ")" => Int.toNat (ord(χ, (z : ℂ)))
local notation "density(" χ ", " η ")" => analyticZeroDensity (criticalFiniteHeckeL χ) η

/-- For every Hecke character, the whole-line regularized integral recovers the
absolutely summable central moments of every real Schwartz test. -/
theorem tendsto_integral_criticalFiniteHeckeL_schwartz (χ : PontryaginDual C𝔽) (g : 𝓢(ℝ, ℝ)) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |g z.val.im|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t, g t * density(χ, η) t) (𝓝[>] 0)
      (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * g z.val.im)) := by
  obtain ⟨C, hC⟩ := criticalFiniteHeckeL_eventually_polynomial_window_mass χ
  exact tendsto_integral_criticalFiniteHeckeL_schwartz_of_window_bound χ C 2
    (hC.mono fun _ hk k ↦ (hk k).2) g

/-- On a smooth compactly supported log-profile the regularized finite-Hecke density
recovers the full central real moments of its centered bilateral Laplace transform. -/
theorem tendsto_integral_criticalFiniteHeckeL_centeredLaplace (χ : PontryaginDual C𝔽)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |(bilateralLaplace H (z.val - 1 / 2)).re|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t : ℝ, (bilateralLaplace H ((t : ℂ) * I)).re * density(χ, η) t)
      (𝓝[>] 0) (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * (bilateralLaplace H (z.val - 1 / 2)).re)) := by
  obtain ⟨C, hC⟩ := criticalFiniteHeckeL_eventually_polynomial_window_mass χ
  exact tendsto_integral_criticalFiniteHeckeL_centeredLaplace_of_window_bound χ C 2
    (hC.mono fun _ hk k ↦ (hk k).2) H hH hHc

end CriticalSchwartzLimits

section CriticalHeckeLattice

open Complex Filter Metric Topology
open RiemannMasullo.AnalyticLattice
open scoped _root_.SchwartzMap

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "central(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ Complex.re z = 1 / 2}

/-- The logarithmic window estimate for the finite Hecke continuation bounds the actual
normalized count of strict consecutive-value comparisons in each high integer bin. -/
theorem criticalFiniteHeckeL_high_bin_count (χ : PontryaginDual C𝔽) :
    ∃ C > (0 : ℝ), ∃ J > (0 : ℝ), ∀ j : ℤ, J ≤ |(j : ℝ)| → ∀ n : ℕ, 0 < n →
      ((binIndices (criticalFiniteHeckeL χ) j n).card : ℝ) / n ≤
        13 * (C * Real.log (2 + |(j : ℝ)|) + 1) ^ 2 := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hfinite := criticalFiniteHeckeL_eq_continuation χ L hL he
  obtain ⟨C, hC, J, hJ, hrect⟩ := finiteHeckeL_continuation_highHeight_unitWindow_logDeriv χ L hL he
  refine ⟨C, hC, J, hJ, ?_⟩
  intro j hj n hn
  obtain ⟨hA, _, S, _, horders, hmass, _, hw⟩ := hrect j hj
  apply bin_count_le_of_logDeriv S (analyticOrderNatAt L) Complex.im
    (mul_nonneg hC.le (Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])))
    (fun z hz ↦ (horders z hz).1) hmass j _ n hn
  intro t ht hne
  obtain ⟨_, hval, hder⟩ := hw (1 / 2 : ℝ) ⟨le_rfl, by norm_num⟩ t ht hne
  have hm : cl(t) = (⟨1 / 2, t⟩ : ℂ) := by apply Complex.ext <;> simp
  have hzin : cl(t) ∈ closedBall (⟨2, (j : ℝ) + 1 / 2⟩ : ℂ) 4 := by
    rw [mem_closedBall, dist_eq_norm, hm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |1 / 2 - 2| + |t - ((j : ℝ) + 1 / 2)| ≤ 4
    have hbound : |t - ((j : ℝ) + 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    norm_num
    linarith
  have hp : HasDerivAt (fun u : ℝ ↦ cl(u)) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (1 / 2 : ℂ)
  have hd := (hA _ hzin).differentiableAt.hasDerivAt.scomp (h := fun u : ℝ ↦ cl(u)) t hp
  rw [hfinite]
  refine ⟨by change L cl(t) ≠ 0; rw [hm]; exact hval, hd.differentiableAt, ?_⟩
  change ‖deriv (L ∘ fun u : ℝ ↦ cl(u)) t‖ / ‖L cl(t)‖ ≤ _
  rw [hd.deriv, hm]
  simpa [logDeriv, smul_eq_mul, norm_div] using hder

/-- The compact strict lattice probe of the finite Hecke function recovers the occupied
critical-line divisor with its full orders. -/
theorem tendsto_sampleSum_criticalFiniteHeckeL_compact (χ : PontryaginDual C𝔽) {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (sampleSum (criticalFiniteHeckeL χ) g) atTop
      (𝓝 (∑' z : central(χ), ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)) := by
  classical
  let f := criticalFiniteHeckeL χ
  let C := {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}
  have hlocal (t : ℝ) := criticalFiniteHeckeL_order χ t
  have hfin (t : ℝ) : analyticOrderAt f t ≠ ⊤ := fun ht ↦ (hlocal t).2.1 (analyticOrderAt_eq_top.mp ht)
  have hlim := tendsto_sampleSum (f := f) hg hgc (fun t _ ↦ (hlocal t).1) (fun t _ ↦ hfin t)
  have hsum := critical_zero_moments_eq χ g
  change Tendsto (sampleSum f g) atTop (𝓝 (∑' z : C, ((ord(χ, z.val)).toNat : ℝ) * g z.val.im))
  rw [← hsum]
  exact hlim

/-- The finite Hecke continuation's strict lattice probe converges against every real
Schwartz function to the genuine completed central divisor, including all multiplicities. -/
theorem tendsto_sampleSum_criticalFiniteHeckeL (χ : PontryaginDual C𝔽) (g : 𝓢(ℝ, ℝ)) :
    Tendsto (sampleSum (criticalFiniteHeckeL χ) g) atTop
      (𝓝 (∑' z : central(χ), ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)) := by
  classical
  let Z := {z : ℂ // 0 < ord(χ, z)}
  let e (z : central(χ)) : Z := ⟨z.val, z.2.1⟩
  have he : Function.Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun z : Z ↦ z.val) h)
  have hZ : Summable (fun z : Z ↦ (ord(χ, z.val) : ℝ) / (1 + |z.val.im|) ^ 2) := by
    simpa only [explicitFormulaCompletedHeckeL, continuedCompletedHeckeL] using
      explicitFormulaCompletedHeckeL_summable_divisor_div_sq χ
  have hc : Summable (fun z : central(χ) ↦ ((ord(χ, z.val)).toNat : ℝ) / (1 + |z.val.im|)^2) := by
    apply (hZ.comp_injective he).congr
    intro z
    change (ord(χ, z.val) : ℝ) / _ = _
    have hcast : ((ord(χ, z.val)).toNat : ℝ) = (ord(χ, z.val) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg z.2.1.le
    rw [hcast]
  obtain ⟨C, hC, J, hJ, hhigh⟩ := criticalFiniteHeckeL_high_bin_count χ
  apply tendsto_sampleSum_schwartz (criticalFiniteHeckeL χ) (fun z : central(χ) ↦ z.val.im)
    (fun z ↦ ((ord(χ, z.val)).toNat : ℝ)) (fun _ ↦ Nat.cast_nonneg _) hc
    (fun _ ↦ tendsto_sampleSum_criticalFiniteHeckeL_compact χ)
    (C := 13 * (C + 1)^2) (J := J) (by positivity) _ g
  intro j hj n hn
  have hl : Real.log (2 + |(j : ℝ)|) ≤ 1 + |(j : ℝ)| := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 2 + |(j : ℝ)| by positivity)]
  have hlog : 0 ≤ Real.log (2 + |(j : ℝ)|) := Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])
  have hsize : C * Real.log (2 + |(j : ℝ)|) + 1 ≤ (C+1) * (1+|(j : ℝ)|) := by
    nlinarith [mul_le_mul_of_nonneg_left hl hC.le, abs_nonneg (j : ℝ)]
  calc
    _ ≤ _ := hhigh j hj n hn
    _ ≤ 13 * ((C+1) * (1+|(j : ℝ)|))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize 2) (by norm_num)
    _ = _ := by ring

/-- The normalized character's chosen continuation is sampled directly at the prescribed
critical-line points on every mesh. -/
theorem tendsto_sampleSum_chosenFiniteHeckeL
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (χ : {χ : PontryaginDual C𝔽 // ∀ a : ℝ≥0ˣ, χ (τ a) = 1})
    (g : 𝓢(ℝ, ℝ)) :
    let L := (finiteHeckeL_exists_continuation χ.val).choose
    Tendsto (sampleSum (fun t : ℝ ↦ L cl(t)) g) atTop
      (𝓝 (∑' z : central(χ.val), ((ord(χ.val, z.val)).toNat : ℝ) * g z.val.im)) := by
  let L := (finiteHeckeL_exists_continuation χ.val).choose
  have hL := (finiteHeckeL_exists_continuation χ.val).choose_spec
  change Tendsto (sampleSum (fun t : ℝ ↦ L cl(t)) g) atTop _
  rw [← criticalFiniteHeckeL_eq_continuation χ.val L hL.1 hL.2]
  exact tendsto_sampleSum_criticalFiniteHeckeL χ.val g

end CriticalHeckeLattice

namespace OutputOrderGeometry

open Complex Filter Function IsDedekindDomain
open scoped ContDiff NNReal NumberField.AdeleRing Topology

set_option quotPrecheck false

attribute [local instance] instSpectralQuotientPolynormableSec3 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Chars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))
local notation "m(" χ ", " z ")" => (ord(χ,(z : ℂ))).toNat
local notation "v(" φ ", " χ ", " z ")" => (M(φ,χ,z)).re
local notation "central(" z ")" => ((z : ℂ).re = 1/2)
local notation "E(" χ ", " φ ")" =>
  (∑' z : Sites(χ), if ¬ central(z) then (m(χ,z) : ℝ) * v(φ,χ,z) else 0)
local notation "volC" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "Arch" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "ext(" τ ", " α ")" => {p : Chars(τ) × ℂ //
  0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re-1/2|}
local notation "target(" τ ")" => (∀ (α : ℝ), 0 < α → ∀ f : BruhatCompactSupport C𝔽,
  (∀ g : C₁, f.val g = 0) → HasSum (fun p : ext(τ,α) ↦
    ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ)*M(f,p.val.1.val,p.val.2)) 0)
local notation "T(" χ ", " A ")" => ((normOneIdeleClassTamagawaMeasure F) univ).toReal *
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)).re -
    primeFreeProfile 0 * heckeLogDiscriminantConductor (F := F) χ)

local notation "centralMass(" χ ", " g ")" =>
  (∑' z : {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2},
    ((ord(χ,z.val)).toNat : ℝ) * (g : ℝ → ℝ) z.val.im)
local notation "archTarget(" χ ", " A ")" =>
  (primeFreeProfile 0 * heckeLogDiscriminantConductor (F := F) χ -
    (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w ((A : Arch) w)).re)
local notation "axisWeight" => (fun t : ℝ ↦
  (bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) ((t : ℂ)*I)).re)

/-- Reindex the real Mellin mass on the central line to its actual complex divisor
sites. At the selected profile its common volume factor is the norm-one volume. -/
private theorem central_sum_eq_volume_mul (χ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (hM : ∀ z : ℂ, M(φ,χ,z) = volC * bilateralLaplace
      (fun x ↦ (primeFreeProfile x : ℂ)) (z-1/2)) :
    (∑' z : Sites(χ), if central(z) then (m(χ,z):ℝ)*v(φ,χ,z) else 0) =
      ((normOneIdeleClassTamagawaMeasure F) univ).toReal * centralMass(χ,axisWeight) := by
  classical
  let W (z : Sites(χ)) := (m(χ,z):ℝ)*v(φ,χ,z)
  let s : Set (Sites(χ)) := {z | central(z)}
  let C := {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}
  let e : s ≃ C :=
    { toFun := fun z ↦ ⟨z.val.val,z.val.property,z.property⟩
      invFun := fun z ↦ ⟨⟨z.val,z.property.1⟩,z.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let vF := ((normOneIdeleClassTamagawaMeasure F) univ).toReal
  let G (z : C) := vF * (((ord(χ,z.val)).toNat : ℝ) * axisWeight z.val.im)
  have hsub : (∑' z : Sites(χ), if central(z) then W z else 0) = ∑' z : s, W z.val := by
    rw [tsum_subtype]
    apply tsum_congr
    intro z
    by_cases h : central(z) <;> simp [Set.indicator_apply,s,h]
  calc
    _ = ∑' z : s, W z.val := hsub
    _ = ∑' z : s, G (e z) := by
      apply tsum_congr
      intro z
      have hz : z.val.val - 1/2 = ((z.val.val.im : ℝ):ℂ)*I := by
        apply Complex.ext
        · change z.val.val.re - (1/2 : ℂ).re = _
          simp [show z.val.val.re = 1/2 from z.property,Complex.mul_re]
        · simp [Complex.mul_im]
      change (m(χ,z.val):ℝ) * v(φ,χ,z.val) =
        vF * ((m(χ,z.val):ℝ) * axisWeight z.val.val.im)
      rw [hM,hz,Complex.re_ofReal_mul]
      ring
    _ = ∑' z : C, G z := e.tsum_eq G
    _ = _ := tsum_mul_left

/-- For the short radial test the full archimedean and conductor scalar dominates
the total mass of the positive central divisor. Equality detects all omitted sites. -/
theorem exists_shortArch_centralMass_iff (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) :
    ∃ A : Arch, (∀ (w : InfinitePlace F) (u : w.Completionˣ), (A w).val u =
      (χ.val⁻¹ (archClass(w) u) : ℂ) * (primeFreeProfile (logIdeleClassNorm F (archClass(w) u)) : ℂ)) ∧
      centralMass(χ.val,axisWeight) ≤ archTarget(χ.val,A) ∧
      (archTarget(χ.val,A) ≤ centralMass(χ.val,axisWeight) ↔
        ∀ z : Sites(χ.val), central(z)) := by
  classical
  obtain ⟨U,hU,hB⟩ := exists_measurable_ideleClassDPrimeSequence F
  obtain ⟨φ,A,B,h,hterminal,htlim⟩ := exists_centeredProbe_archConductor_iff_central τ hτ χ U hU hB
  obtain ⟨hφ,_,_,_,hM,hpos,hA,_,_,_,hmass,_,_⟩ := h
  refine ⟨A,fun w u ↦ (hA w u).trans (hφ _),?_⟩
  let vF := ((normOneIdeleClassTamagawaMeasure F) univ).toReal
  have hv : 0 < vF := CenterGeometry.normOneVolume_pos (F := F)
  let n (z : Sites(χ.val)) := m(χ.val,z)
  let W (z : Sites(χ.val)) := v(φ,χ.val,z)
  let P (z : Sites(χ.val)) := central(z)
  have hs : Summable (fun z : Sites(χ.val) ↦ (n z:ℝ)*|W z|) :=
    summable_heckeRealMoments_fullOrder (F := F) τ hτ χ φ
  have hn (z : Sites(χ.val)) : 0 < n z := by
    have hz := z.property
    change 0 < (ord(χ.val,z.val)).toNat
    omega
  have hE : E(χ.val,φ) = 0 ↔ ∀ z : Sites(χ.val), central(z) :=
    exterior_zero_iff P n W hs hn hpos
  have hnon : 0 ≤ E(χ.val,φ) := tsum_nonneg (fun z : Sites(χ.val) ↦
    ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos z).le) le_rfl)
  have hsplit := full_split P n W hs
  have heq := central_sum_eq_volume_mul χ.val φ hM
  have htotal : vF * archTarget(χ.val,A) =
      vF * centralMass(χ.val,axisWeight) + E(χ.val,φ) := by
    calc
      _ = -T(χ.val,A) := by dsimp only [vF]; ring
      _ = _ := hmass
      _ = _ := by simpa only [P,n,W,heq] using hsplit
  refine ⟨(mul_le_mul_iff_right₀ hv).mp (by linarith), ?_⟩
  rw [← hE]
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h hv.le
    linarith
  · intro h
    exact (mul_le_mul_iff_right₀ hv).mp (by linarith)


local notation "densityIntegrand(" χ ", " η ")" => (fun t : ℝ ↦ axisWeight t *
  analyticZeroDensity (criticalFiniteHeckeL (F := F) χ) η t)
local notation "measurement(" χ ")" =>
  (limUnder (𝓝[>] (0 : ℝ)) (fun η : ℝ ↦ ∫ t, densityIntegrand(χ,η) t))

private theorem shortCriticalDensity_limits (χ : PontryaginDual C𝔽) :
    (∀ η : ℝ, 0 < η → Integrable densityIntegrand(χ,η)) ∧
    Tendsto (fun η : ℝ ↦ ∫ t, densityIntegrand(χ,η) t) (𝓝[>] 0)
      (𝓝 centralMass(χ,axisWeight)) := by
  obtain ⟨hH,hHc,_,_,_,_,_,_⟩ := primeFreeProfile_properties
  let G (x : ℝ) : ℂ := primeFreeProfile x
  have hs : ContDiff ℝ (∞) G := Complex.ofRealCLM.contDiff.comp hH
  have hc : HasCompactSupport G := hHc.comp_left Complex.ofReal_zero
  have hlim := (tendsto_integral_criticalFiniteHeckeL_centeredLaplace χ G hs hc).2
  have hpoint (z : {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}) :
      z.val - 1/2 = (z.val.im : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.mul_re, z.property.2]
    · simp [Complex.mul_im]
  refine ⟨?_,by simpa only [hpoint,G] using hlim⟩
  intro η hη
  have hg : Integrable (fun t : ℝ ↦ (bilateralLaplace G ((t : ℂ)*I)).re) :=
    (bilateralLaplace_inversion_zero hs hc).1.re
  exact hg.mul_bdd (criticalFiniteHeckeL_density_measurable χ η).aestronglyMeasurable
    (ae_of_all _ (criticalHeckeDensity_norm_le χ hη))

/-- Theorem 12.5.1.1, pp. 519–520. For the fixed short profile the full local arithmetic
scalar is a lower bound on one critical-line measurement for each normalized character
exactly when the exterior terms vanish at all positive widths. The reverse inequalities
and the absolute convergence of all the measured integrals hold unconditionally. -/
theorem exists_archConductor_criticalDensity_iff_exteriorZeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ A : Chars(τ) → Arch,
      (∀ (χ : Chars(τ)) (w : InfinitePlace F) (u : w.Completionˣ), ((A χ) w).val u =
        (χ.val⁻¹ (archClass(w) u) : ℂ) * (primeFreeProfile (logIdeleClassNorm F (archClass(w) u)) : ℂ)) ∧
      (∀ χ : Chars(τ), (∀ η : ℝ, 0 < η → Integrable densityIntegrand(χ.val,η)) ∧
        Tendsto (fun η : ℝ ↦ ∫ t, densityIntegrand(χ.val,η) t) (𝓝[>] 0)
          (𝓝 centralMass(χ.val,axisWeight)) ∧ measurement(χ.val) ≤ archTarget(χ.val,A χ)) ∧
      ((∀ χ : Chars(τ), archTarget(χ.val,A χ) ≤ measurement(χ.val)) ↔ target(τ)) := by
  choose A hA hle hiff using fun χ : Chars(τ) ↦ exists_shortArch_centralMass_iff τ hτ χ
  refine ⟨A,hA,fun χ ↦ ?_, ?_⟩
  · obtain ⟨hi,ht⟩ := shortCriticalDensity_limits χ.val
    exact ⟨hi,ht,ht.limUnder_eq ▸ hle χ⟩
  · apply Iff.trans _ (allCentral_iff_exteriorZeros τ hτ)
    apply forall_congr'
    intro χ
    rw [(shortCriticalDensity_limits χ.val).2.limUnder_eq]
    exact hiff χ



local notation "criticalGrid(" χ ")" => (fun t : ℝ ↦
  (finiteHeckeL_exists_continuation (F := F) χ).choose ((1/2 : ℂ)+(t : ℂ)*I))
local notation "gridSum(" χ ")" => AnalyticLattice.sampleSum criticalGrid(χ) axisWeight

private theorem tendsto_shortCriticalGrid (τ : ℝ≥0ˣ →ₜ* C𝔽) (χ : Chars(τ)) :
    Tendsto gridSum(χ.val) atTop (𝓝 centralMass(χ.val,axisWeight)) := by
  obtain ⟨hs,hc,_,_,_,_,_,_⟩ := primeFreeProfile_properties
  let H (x : ℝ) : ℂ := primeFreeProfile x
  have hs' : ContDiff ℝ (∞) H := Complex.ofRealCLM.contDiff.comp hs
  have hc' : HasCompactSupport H := hc.comp_left Complex.ofReal_zero
  obtain ⟨g,hg⟩ := exists_realSchwartz_eq_bilateralLaplace_axis_re hc' hs'
  have he : (g : ℝ → ℝ) = axisWeight := funext hg
  simpa only [he] using tendsto_sampleSum_chosenFiniteHeckeL τ χ g

private theorem lowerBound_iff_cofinal_samples {v : ℕ → ℝ} {L S : ℝ}
    (hv : Tendsto v atTop (𝓝 L)) :
    (∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ S-δ ≤ v n) ↔ S ≤ L := by
  constructor
  · intro h
    by_contra! hgap
    let d := (S-L)/3
    have hd : 0 < d := by dsimp [d]; linarith
    obtain ⟨N,hN⟩ := eventually_atTop.1 (hv.eventually (gt_mem_nhds (show L < L+d by linarith)))
    obtain ⟨n,hn,hl⟩ := h d hd N
    have hh := hN n hn
    change v n < L+d at hh
    dsimp [d] at hh hl
    linarith
  · intro h δ hδ N
    obtain ⟨M,hM⟩ := eventually_atTop.1 (hv.eventually (lt_mem_nhds (show S-δ < L by linarith)))
    exact ⟨max N M,le_max_left _ _,(hM _ (le_max_right N M)).le⟩

/-- Theorem 12.5.1.1, pp. 519–520. On the predetermined critical-line grid,
consecutive absolute values of the finite Hecke continuation recover the entire weighted
central divisor. The remaining one-sided comparison asks for arbitrarily late finite
samples approaching the fixed archimedean and conductor scalar from below. -/
theorem exists_archConductor_finiteCriticalSamples_iff_exteriorZeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ A : Chars(τ) → Arch,
      (∀ (χ : Chars(τ)) (w : InfinitePlace F) (u : w.Completionˣ), ((A χ) w).val u =
        (χ.val⁻¹ (archClass(w) u) : ℂ) * (primeFreeProfile (logIdeleClassNorm F (archClass(w) u)) : ℂ)) ∧
      (∀ χ : Chars(τ), Tendsto gridSum(χ.val) atTop (𝓝 centralMass(χ.val,axisWeight)) ∧
        limUnder atTop gridSum(χ.val) ≤ archTarget(χ.val,A χ)) ∧
      ((∀ (χ : Chars(τ)) (δ : ℝ), 0 < δ → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        archTarget(χ.val,A χ)-δ ≤ gridSum(χ.val) n) ↔ target(τ)) := by
  choose A hA hle hiff using fun χ : Chars(τ) ↦ exists_shortArch_centralMass_iff τ hτ χ
  refine ⟨A,hA,fun χ ↦ ?_, ?_⟩
  · have ht := tendsto_shortCriticalGrid τ χ
    exact ⟨ht,ht.limUnder_eq ▸ hle χ⟩
  · apply Iff.trans _ (allCentral_iff_exteriorZeros τ hτ)
    apply forall_congr'
    intro χ
    exact (lowerBound_iff_cofinal_samples (tendsto_shortCriticalGrid τ χ)).trans (hiff χ)

end OutputOrderGeometry

end RiemannMasullo.Isolated
