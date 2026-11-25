module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Order
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges

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

/-! ### Positive edge probes vanishing on norm-one classes

The compact positive cosine transform supplies a numerator with a scaled
second-derivative correction. Its radial lift gives the sign hypothesis
of the preceding comparison, including for the principal character. -/

section PositiveEdgeProbes

open Complex Filter Function
open scoped ContDiff NNReal NumberField.AdeleRing Topology

private theorem cosine_deriv (f : ℝ → ℝ) (hs : ContDiff ℝ (∞) f)
    (hc : HasCompactSupport f) (t : ℝ) :
    ∫ x, deriv f x * Real.cos (t*x) = t * ∫ x, f x * Real.sin (t*x) := by
  have hI : Integrable (fun x ↦ f x * Real.cos (t*x)) :=
    (hs.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hD : Integrable (fun x ↦ deriv f x * Real.cos (t*x)) :=
    ((hs.continuous_deriv (by simp)).mul (by fun_prop)).integrable_of_hasCompactSupport hc.deriv.mul_right
  have hS : Integrable (fun x ↦ f x * Real.sin (t*x)) :=
    (hs.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hprod (x : ℝ) : HasDerivAt (fun y ↦ f y * Real.cos (t*y))
      (deriv f x * Real.cos (t*x) - t*(f x * Real.sin (t*x))) x := by
    convert ((hs.differentiable (by simp) x).hasDerivAt.mul
      ((Real.hasDerivAt_cos (t*x)).comp x ((hasDerivAt_id x).const_mul t))) using 1
    · rfl
    · dsimp
      ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hprod (hD.sub (hS.const_mul t)) hI
  rw [integral_sub hD (hS.const_mul t), integral_const_mul] at hz
  exact sub_eq_zero.mp hz

private theorem sine_deriv (f : ℝ → ℝ) (hs : ContDiff ℝ (∞) f)
    (hc : HasCompactSupport f) (t : ℝ) :
    ∫ x, deriv f x * Real.sin (t*x) = -(t * ∫ x, f x * Real.cos (t*x)) := by
  have hI : Integrable (fun x ↦ f x * Real.sin (t*x)) :=
    (hs.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hD : Integrable (fun x ↦ deriv f x * Real.sin (t*x)) :=
    ((hs.continuous_deriv (by simp)).mul (by fun_prop)).integrable_of_hasCompactSupport hc.deriv.mul_right
  have hC : Integrable (fun x ↦ f x * Real.cos (t*x)) :=
    (hs.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hprod (x : ℝ) : HasDerivAt (fun y ↦ f y * Real.sin (t*y))
      (deriv f x * Real.sin (t*x) + t*(f x * Real.cos (t*x))) x := by
    convert ((hs.differentiable (by simp) x).hasDerivAt.mul
      ((Real.hasDerivAt_sin (t*x)).comp x ((hasDerivAt_id x).const_mul t))) using 1
    · rfl
    · dsimp
      ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hprod (hD.add (hC.const_mul t)) hI
  rw [integral_add hD (hC.const_mul t), integral_const_mul] at hz
  exact eq_neg_of_add_eq_zero_left hz

private theorem secondDeriv_even (K : ℝ → ℝ) (hs : ContDiff ℝ (∞) K) (he : ∀ x, K (-x) = K x)
    (x : ℝ) : deriv (deriv K) (-x) = deriv (deriv K) x := by
  have hD (x : ℝ) := (hs.differentiable (by simp) x).hasDerivAt
  have hD' (x : ℝ) := ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) x).hasDerivAt
  have hodd (x : ℝ) : deriv K (-x) = -deriv K x := by
    have h := (hD (-x)).comp x (hasDerivAt_neg x)
    change HasDerivAt (fun y ↦ K (-y)) _ x at h
    simp_rw [he] at h
    simpa using (congrArg Neg.neg (hD x |>.unique h)).symm
  have h := (hD' (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun y ↦ deriv K (-y)) _ x at h
  simp_rw [hodd] at h
  simpa using ((hD' x).neg.unique h).symm

/-- From a compact, smooth, even kernel having positive value at the origin and strictly
positive cosine transform, produce a compact smooth even numerator vanishing at the origin
whose cosine transform is positive outside any prescribed interval about zero. -/
private theorem exists_stripEdgeNumerator_of_kernel (K : ℝ → ℝ) (hs : ContDiff ℝ (∞) K)
    (hc : HasCompactSupport K) (he : ∀ x, K (-x) = K x) (h0 : 0 < K 0)
    (hF : ∀ t : ℝ, 0 < ∫ x, K x * Real.cos (t*x)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ (∞) u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      u 0 = 0 ∧ ∀ t : ℝ, δ ≤ |t| → 0 < ∫ x, u x * Real.cos (t*x) := by
  let c := -(deriv (deriv K) 0)/K 0
  let U (x : ℝ) := -(deriv (deriv K) x) - c*K x
  have hsd : ContDiff ℝ (∞) (deriv K) := (contDiff_infty_iff_deriv.mp hs).2
  have hsdd : ContDiff ℝ (∞) (deriv (deriv K)) := (contDiff_infty_iff_deriv.mp hsd).2
  have hsU : ContDiff ℝ (∞) U := hsdd.neg.sub (contDiff_const.mul hs)
  have hcU : HasCompactSupport U := hc.deriv.deriv.neg.sub hc.mul_left
  have heU (x : ℝ) : U (-x) = U x := by simp [U, he, secondDeriv_even K hs he]
  have hU0 : U 0 = 0 := by dsimp [U, c]; field_simp; ring
  have hU (t : ℝ) : ∫ x, U x * Real.cos (t*x) = (t^2-c) * ∫ x, K x * Real.cos (t*x) := by
    have hI (g : ℝ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) :
        Integrable (fun x ↦ g x * Real.cos (t*x)) :=
      (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
    simp only [U, sub_mul, neg_mul, mul_assoc]
    rw [integral_sub (f := fun x ↦ -(deriv (deriv K) x * Real.cos (t*x)))
      (g := fun x ↦ c*(K x * Real.cos (t*x)))
      (hI _ hsdd.continuous hc.deriv.deriv).neg ((hI _ hs.continuous hc).const_mul c),
      integral_neg, integral_const_mul]
    rw [cosine_deriv _ hsd hc.deriv, sine_deriv K hs hc]
    ring
  let R := (|c|+1)/δ
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨fun x ↦ U (x/R), hsU.comp (by fun_prop), ?_, ?_, by simpa using hU0, ?_⟩
  · simpa only [Function.comp_def, Homeomorph.coe_mulRight₀, div_eq_mul_inv] using
      hcU.comp_homeomorph (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero hR.ne'))
  · intro x
    simpa only [neg_div] using heU (x/R)
  · intro t ht
    have hscale : (∫ x, U (x/R) * Real.cos (t*x)) = R * ∫ x, U x * Real.cos ((R*t)*x) := by
      convert Measure.integral_comp_div (fun x : ℝ ↦ U x * Real.cos ((R*t)*x)) R using 1
      · apply integral_congr_ae
        filter_upwards with x
        congr 2
        field_simp
      · simp [abs_of_pos hR, smul_eq_mul]
    rw [hscale, hU]
    apply mul_pos hR (mul_pos _ (hF _))
    have hRT : |c| + 1 ≤ |R*t| := by
      rw [abs_mul, abs_of_pos hR]
      calc
        _ = R*δ := by dsimp [R]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left ht hR.le
    nlinarith [sq_abs (R*t), sq_nonneg (|R*t| - 1), le_abs_self c]

/-- A radial test which removes the hyperbolic cosine in the real moment on either edge. -/
private def stripEdgeProfile (u : ℝ → ℝ) (b t₀ x : ℝ) : ℂ :=
  (u x / Real.cosh (b*x) : ℝ) * Complex.exp (-(t₀ : ℂ) * Complex.I * x)

private theorem stripEdgeProfile_support {u : ℝ → ℝ} (hc : HasCompactSupport u) (b t₀ : ℝ) :
    HasCompactSupport (stripEdgeProfile u b t₀) := by
  apply hc.mono
  intro x hx hz
  exact hx (by simp [stripEdgeProfile, hz])

/-- The test attached to a compact smooth numerator is a compact smooth radial test, and
vanishes at zero when the numerator does. -/
private theorem stripEdgeProfile_admissible {u : ℝ → ℝ} (hu : ContDiff ℝ (∞) u)
    (hc : HasCompactSupport u) (hz : u 0 = 0) (b t₀ : ℝ) :
    ContDiff ℝ (∞) (stripEdgeProfile u b t₀) ∧ HasCompactSupport (stripEdgeProfile u b t₀) ∧
      stripEdgeProfile u b t₀ 0 = 0 := by
  refine ⟨?_, stripEdgeProfile_support hc b t₀, by simp [stripEdgeProfile, hz]⟩
  unfold stripEdgeProfile
  have hcosh (x : ℝ) : Real.cosh (b*x) ≠ 0 := (Real.cosh_pos _).ne'
  have hquot : ContDiff ℝ (∞) (fun x ↦ u x / Real.cosh (b*x)) :=
    hu.div (by simp_rw [Real.cosh_eq]; fun_prop) hcosh
  exact (Complex.ofRealCLM.contDiff.comp hquot).mul
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))

private theorem stripEdgeProfile_integrand (u : ℝ → ℝ) (b r t₀ γ x : ℝ) :
    (stripEdgeProfile u b t₀ x * Complex.exp (((r : ℂ) + (γ : ℂ)*Complex.I) * x)).re =
      u x / Real.cosh (b*x) * Real.exp (r*x) * Real.cos ((γ-t₀)*x) := by
  rw [stripEdgeProfile, mul_assoc, ← Complex.exp_add]
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf

private theorem stripEdgeProfile_symm (u : ℝ → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
    (he : ∀ x, u (-x) = u x) (b t : ℝ) :
    ∫ x, u x / Real.cosh (b*x) * Real.exp (b*x) * Real.cos (t*x) =
      ∫ x, u x * Real.cos (t*x) := by
  let f (r x : ℝ) := u x / Real.cosh (b*x) * Real.exp (r*x) * Real.cos (t*x)
  have hint (r : ℝ) : Integrable (f r) := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [f]
      have hcosh (x : ℝ) : Real.cosh (b*x) ≠ 0 := (Real.cosh_pos _).ne'
      fun_prop (disch := first | exact hcosh | exact hcosh _)
    · apply hc.mono
      intro x hx hz
      exact hx (by simp [f, hz])
  have heq : (∫ x, f (-b) x) = ∫ x, f b x := by
    conv_rhs => rw [← integral_neg_eq_self (f b) volume]
    apply integral_congr_ae
    filter_upwards with x
    simp [f, he, neg_mul, mul_neg]
  have hsum : (∫ x, f b x) + (∫ x, f (-b) x) = 2 * ∫ x, u x * Real.cos (t*x) := by
    rw [← integral_add (hint _) (hint _), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [f]
    have h0 := (Real.cosh_pos (b*x)).ne'
    rw [neg_mul]
    have hsumexp : Real.exp (b*x) + Real.exp (-(b*x)) = 2 * Real.cosh (b*x) := by
      rw [Real.cosh_eq]
      ring
    calc
      _ = u x / Real.cosh (b*x) * Real.cos (t*x) *
          (Real.exp (b*x) + Real.exp (-(b*x))) := by ring
      _ = _ := by rw [hsumexp]; field_simp
  rw [heq] at hsum
  change (∫ x, f b x) = _
  linarith

/-- At either edge the real Mellin value is the same cosine transform. No symmetry of
the zero ordinates, or of the character defining the angular component, is required. -/
private theorem stripEdgeProfile_moment_re (u : ℝ → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
    (he : ∀ x, u (-x) = u x) (b r t₀ γ : ℝ) (hr : r = b ∨ r = -b) :
    (∫ x, stripEdgeProfile u b t₀ x * Complex.exp (((r : ℂ) + (γ : ℂ)*Complex.I) * x)).re =
      ∫ x, u x * Real.cos ((γ-t₀)*x) := by
  have h0 (x : ℝ) : Real.cosh (b*x) ≠ 0 := (Real.cosh_pos _).ne'
  have hI : Integrable (fun x ↦ stripEdgeProfile u b t₀ x *
      Complex.exp (((r : ℂ) + (γ : ℂ)*Complex.I) * x)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold stripEdgeProfile
      fun_prop (disch := first | exact h0 | exact h0 _)
    · exact (stripEdgeProfile_support hc b t₀).mul_right
  change RCLike.re (∫ x, stripEdgeProfile u b t₀ x * _) = _
  rw [← integral_re hI]
  change (∫ x, (stripEdgeProfile u b t₀ x * _).re) = _
  simp_rw [stripEdgeProfile_integrand]
  rcases hr with h | h
  · rw [h]
    exact stripEdgeProfile_symm u hu hc he b (γ-t₀)
  · rw [h]
    simpa only [neg_mul, Real.cosh_neg] using stripEdgeProfile_symm u hu hc he (-b) (γ-t₀)

/-- Given any gap around a chosen ordinate, the same smooth compact radial probe
vanishes at zero and has strictly positive real transform at every remaining
ordinate on either vertical edge. -/
private theorem exists_positiveStripEdgeProfile {δ : ℝ} (hδ : 0 < δ) (b t₀ : ℝ) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ H 0 = 0 ∧
      ∀ r γ : ℝ, (r = b ∨ r = -b) → δ ≤ |γ-t₀| →
        0 < (bilateralLaplace H ((r : ℂ) + (γ : ℂ)*Complex.I)).re := by
  obtain ⟨K, hs, hc, he, h0, hF⟩ := exists_compact_pos_cosineTransform
  obtain ⟨u, hus, huc, hue, hu0, huF⟩ :=
    exists_stripEdgeNumerator_of_kernel K hs hc he h0 hF hδ
  obtain ⟨hhs, hhc, hh0⟩ := stripEdgeProfile_admissible hus huc hu0 b t₀
  refine ⟨stripEdgeProfile u b t₀, hhs, hhc, hh0, fun r γ hedge hgap ↦ ?_⟩
  rw [bilateralLaplace, stripEdgeProfile_moment_re u hus.continuous huc hue b r t₀ γ hedge]
  exact huF _ hgap

private theorem logTest_mellin (H : ℝ → ℂ) (s : ℂ) :
    introTraceMellin (fun r ↦ H (Real.log r)) s = bilateralLaplace H s := by
  rw [introTraceMellin, mellin, ← integral_comp_exp, bilateralLaplace]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 1
  ring_nf


set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "vol₁" => ((normOneIdeleClassTamagawaMeasure F) univ).toReal
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin
  (continuousIdeleClassNorm F) univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))

private theorem exists_ordinate_gap (χ : PontryaginDual C𝔽) (R : ℝ) :
    ∃ t δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 0 < ord(χ,z) → |z.re| ≤ R → δ ≤ |z.im - t| := by
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
  let K := Metric.closedBall (0 : ℂ) (R + 2) ∩ (fun z ↦ D z).support
  have hloc : LocallyFiniteSupport (fun z ↦ D z) :=
    fun z ↦ D.supportLocallyFiniteWithinDomain z (mem_univ z)
  have hfin : (Complex.im '' K).Finite :=
    (hloc.finite_inter_support_of_isCompact (isCompact_closedBall _ _)).image _
  obtain ⟨t, ht, hnot⟩ := (Ioo_infinite (zero_lt_one : (0:ℝ) < 1)).exists_notMem_finite hfin
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl t hnot
  refine ⟨t, min 1 η, lt_min zero_lt_one hη, fun z hz hR ↦ ?_⟩
  by_contra! hsmall
  have hsmall₁ := abs_lt.mp (hsmall.trans_le (min_le_left 1 η))
  have him : |z.im| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1, hsmall₁.1],
    by linarith [ht.2, hsmall₁.2]⟩
  have hnear : z.im ∈ Metric.ball t η := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hsmall.trans_le (min_le_right 1 η)
  apply hball hnear
  refine ⟨z, ⟨?_, hz.ne'⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hR him)

private theorem normOneVolume_pos : 0 < vol₁ := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  exact (ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top)

/-- A real-positive transform at every actual zero of either specified edge in one
character is attained by a genuine compact Bruhat test vanishing on norm-one classes. -/
theorem exists_heckePositiveStripEdgeTest (χ : PontryaginDual C𝔽) (b : ℝ) :
    ∃ φ : BruhatCompactSupport C𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) ∧
      ∀ z : ℂ, 0 < ord(χ,z) → |z.re - 1/2| = b → 0 < (M(φ,χ,z)).re := by
  obtain ⟨t, δ, hδ, hg⟩ := exists_ordinate_gap χ (|b| + 1)
  obtain ⟨H, hs, hc, h₀, hedge⟩ := exists_positiveStripEdgeProfile hδ b t
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) χ⁻¹ H hs hc
  let f (r : ℝ) := H (Real.log r)
  have htest (g : C𝔽) : φ.val g = introTraceTest χ f g := by
    rw [hφ g, introTraceTest]
    rw [show χ⁻¹ g = (χ g)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    rfl
  refine ⟨φ, ?_, fun z hz hb ↦ ?_⟩
  · intro g
    simp only [hφ, show ideleClassNorm F g.val = 1 from g.property,
      Units.val_one, NNReal.coe_one, Real.log_one, h₀, mul_zero]
  have hside : z.re-1/2 = b ∨ z.re-1/2 = -b := by
    rcases le_total 0 (z.re-1/2) with h | h
    · rw [abs_of_nonneg h] at hb
      exact Or.inl hb
    · exact Or.inr (by rw [abs_of_nonpos h] at hb; linarith)
  have hR : |z.re| ≤ |b| + 1 := calc
    |z.re| = |(z.re - 1/2) + 1/2| := by ring_nf
    _ ≤ |z.re - 1/2| + |(1/2:ℝ)| := abs_add_le _ _
    _ ≤ |b| + 1 := by rw [hb]; norm_num; linarith [le_abs_self b]
  have hh := hedge (z.re-1/2) z.im hside (hg z hz hR)
  have hw : (((z.re-1/2 : ℝ) : ℂ) + (z.im : ℂ)*Complex.I) = z - 1/2 := by
    apply Complex.ext <;> simp
  rw [hw] at hh
  have hm : introTraceMellin f (z-1/2) = bilateralLaplace H (z-1/2) := by
    exact logTest_mellin H (z-1/2)
  have hf := (introTraceTest_mellin χ f φ htest (z-1/2)).2
  simp only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ]
  rw [hf, hm, Complex.re_ofReal_mul]
  exact mul_pos (normOneVolume_pos (F := F)) hh

/-- One compact, norm-one-vanishing probe of the chosen character and edge radius
for the signed-width comparison in Theorem 12.5.1.1, pp. 519–520. -/
def heckePositiveStripEdgeProbe (χ : PontryaginDual C𝔽) (b : ℝ) : BruhatCompactSupport C𝔽 :=
  (exists_heckePositiveStripEdgeTest χ b).choose

/-- The chosen probe is admissible at the identity and has strictly positive real
Mellin value at every occupied site of the two prescribed strip edges. -/
theorem heckePositiveStripEdgeProbe_spec (χ : PontryaginDual C𝔽) (b : ℝ) :
    (∀ g : (ideleClassNorm F).ker, (heckePositiveStripEdgeProbe χ b).val g = 0) ∧
    ∀ z : ℂ, 0 < ord(χ,z) → |z.re - 1/2| = b →
      0 < (M(heckePositiveStripEdgeProbe χ b,χ,z)).re :=
  (exists_heckePositiveStripEdgeTest χ b).choose_spec

local notation "edgeChars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "edgeSites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "edgeExterior(" τ ", " α ")" => {p : edgeChars(τ) × ℂ //
  0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re - 1/2|}
local notation "edgeOff(" z ")" => ((z : ℂ).re - 1/2)
local notation "edgeOrder(" χ ", " z ")" => (ord(χ, (z : ℂ))).toNat
local notation "edgeReal(" χ ", " b ", " z ")" =>
  (M(heckePositiveStripEdgeProbe χ b,χ,z)).re

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The indicated one-sided comparison on
a concrete norm-one-vanishing probe for each character and candidate radius gives
the exterior-zero formula. The comparison is the remaining hypothesis. -/
theorem traceFormula_exteriorZeros_of_positiveEdgeProbeComparison
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    {α s : ℝ} (hα : 0 < α) (hs : 1 < s)
    (hcomparison : ∀ (χ : edgeChars(τ)) (b : ℝ), α ≤ b → b < 1/2 →
      -(∑' z : edgeSites(χ.val), if |edgeOff(z)| < b then
        (edgeOrder(χ.val,z) : ℝ) * edgeReal(χ.val,b,z) else 0) ≤
      -(∑' z : edgeSites(χ.val),
        (spectralStripMultiplicity b s edgeOff(z) edgeOrder(χ.val,z) : ℝ) * edgeReal(χ.val,b,z)))
    (φ : BruhatCompactSupport C𝔽) :
    HasSum (fun p : edgeExterior(τ,α) ↦ ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) *
      M(φ,p.val.1.val,p.val.2)) 0 :=
  traceFormula_exteriorZeros_of_signedWidthComparison τ hτ hα hs
    (fun χ b ↦ heckePositiveStripEdgeProbe χ.val b)
    (fun χ b _ _ z hz ↦ (heckePositiveStripEdgeProbe_spec χ.val b).2 z.val z.property hz)
    hcomparison φ

end PositiveEdgeProbes

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

end RiemannMasullo.Isolated
