module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
public import RiemannMasullo.AppA_AlgebraicNT.Sec5a_IdeleClassDPrime
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges
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
