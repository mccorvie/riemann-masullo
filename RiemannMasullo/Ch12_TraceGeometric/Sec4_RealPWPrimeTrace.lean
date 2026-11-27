module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedLogTerm
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedLowerTrace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The real place together with one prime: the term `log p`

Paper: Theorem 12.4.1.1, pp. 514–517, the terms of the finite places, for `F = ℚ` and
`S = {∞, p}`, in the unweighted model of #7354. This is A. Connes, *Trace formula in
noncommutative geometry and the zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31,
for `k = ℚ` and `S = {∞, p}`, on the functions invariant under the units of `ℚ_p`.

On that sector the space `L²(X_S)` is the space of even functions on the line, and the Fourier
transform of `X_S` is the Fourier transform of the line followed by
`U = (1 - r T⁻¹) (1 - r T)⁻¹`, where `T f (x) = p ^ (1/2) f (p x)` and `r = p ^ (-1/2)`. So the
frequency cutoff is `U Q U⁻¹` with `Q` the projection onto the band, and the trace of the
cutoff action of a test function `ψ` is the trace of `Q (U⁻¹ M_L U) A_ψ Q` on the band. With
`U = ∑ n, d n T ^ (n - 1)` this operator is the sum over pairs `(i, j)` of `d i d j` times
`Q M_{L p ^ (i - 1)} A_{ψ_{j - i}} Q`, where `ψ_k (u) = p ^ k ψ (p ^ k u)`. Each of these is an
operator of `Sec4_RealPWTestTrace`, with trace the integral of `ψ_k` against the sharp trace
at cutoff `L p ^ (i - 1)`. That reduction is on paper and is not formalized here.

This file treats the resulting series of traces.

* `primeTwistCoeff`. The coefficients `d n` of `U`.
* `hasSum_primeTwistCoeff_mul`. Their autocorrelation is one at shift zero and zero at every
  other shift. This is the unitarity of `U`.
* `hasSum_primeTwistCoeff_moment` and `hasSum_primeTwistCoeff_moment_lower`. The first moment
  `∑ (i - 1) d i d j` over the pairs with `j - i = k` is `r ^ |k|` for `k ≠ 0` and zero for
  `k = 0`.
* `exists_primeBlock_nuclear`. Each block is a nuclear operator on the band, and `primeBlock`
  is its trace.
* `tendsto_primeBlockRemainder` and `exists_eventually_norm_primeBlockRemainder_le`. Each
  block has the logarithmic growth of `Sec4_RealPWUnweightedLogTerm`, and the remainders are
  bounded uniformly over the scales `p ^ k` for large cutoffs.
* `tendsto_primeTraceSeries_sub_log`. The series of traces less `ψ 1 log (2πYL)` converges.
  The limit is the limit for the real place alone plus
  `log p ∑ n ≥ 1, r ^ n (φ (p ^ n) + φ (p ^ (-n)))` with `φ g = g ψ g`. For `r = p ^ (-1/2)`
  this is the term of the prime `p` in the explicit formula.

The real-place limits of the blocks at the shifts `k ≠ 0` cancel, by the autocorrelation
identity. The term `log p` comes from the logarithms `log (2πY L p ^ (i - 1))` of the cutoffs
of the blocks, through the first moments.

Reconstruction: The paper does not state this.

Not treated here: the reduction of the sector of `L²(X_S)` to this series, which is on paper,
and the convergence of the series of operators in trace norm, so that the series is the trace
of `Q (U⁻¹ M_L U) A_ψ Q`. Test functions that are not Lipschitz. A weight. The level. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

/-- The coefficients of `U = (1 - r T⁻¹) (1 - r T)⁻¹ = ∑ n, d n T ^ (n - 1)`: `d 0 = -r` and
`d (n + 1) = (1 - r²) r ^ n`. -/
def primeTwistCoeff (r : ℝ) : ℕ → ℝ
  | 0 => -r
  | n + 1 => (1 - r ^ 2) * r ^ n

theorem primeTwistCoeff_zero (r : ℝ) : primeTwistCoeff r 0 = -r := rfl

theorem primeTwistCoeff_succ (r : ℝ) (n : ℕ) :
    primeTwistCoeff r (n + 1) = (1 - r ^ 2) * r ^ n := rfl

/-- The coefficients decay geometrically. -/
theorem abs_primeTwistCoeff_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (i : ℕ) :
    |primeTwistCoeff r i| ≤ r⁻¹ * r ^ i := by
  cases i with
  | zero =>
    rw [primeTwistCoeff_zero, abs_neg, abs_of_pos hr0, pow_zero, mul_one]
    exact hr1.le.trans ((one_le_inv₀ hr0).mpr hr1.le)
  | succ n =>
    have h1 : r⁻¹ * r ^ (n + 1) = r ^ n := by
      rw [pow_succ]
      field_simp
    have h2 : 0 ≤ 1 - r ^ 2 := by nlinarith
    rw [primeTwistCoeff_succ, h1, abs_of_nonneg (mul_nonneg h2 (pow_nonneg hr0.le n))]
    calc (1 - r ^ 2) * r ^ n ≤ 1 * r ^ n :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg r]) (pow_nonneg hr0.le n)
      _ = r ^ n := one_mul _

/-- The autocorrelation of the coefficients is one at shift zero and zero at every other
shift. This is the unitarity of `U`. -/
theorem hasSum_primeTwistCoeff_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    HasSum (fun i ↦ primeTwistCoeff r i * primeTwistCoeff r (i + n))
      (if n = 0 then 1 else 0) := by
  have hx0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hx1 : r ^ 2 < 1 := by nlinarith
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  have hg := (hasSum_geometric_of_lt_one hx0 hx1).mul_left ((1 - r ^ 2) ^ 2 * r ^ n)
  have htail : HasSum (fun l ↦ primeTwistCoeff r (l + 1) * primeTwistCoeff r (l + 1 + n))
      ((1 - r ^ 2) * r ^ n) := by
    have he : (fun l ↦ primeTwistCoeff r (l + 1) * primeTwistCoeff r (l + 1 + n)) =
        fun l ↦ (1 - r ^ 2) ^ 2 * r ^ n * (r ^ 2) ^ l := by
      funext l
      rw [show l + 1 + n = (l + n) + 1 by omega, primeTwistCoeff_succ, primeTwistCoeff_succ]
      ring
    have hv : (1 - r ^ 2) * r ^ n = (1 - r ^ 2) ^ 2 * r ^ n * (1 - r ^ 2)⁻¹ := by
      field_simp
    rw [he, hv]
    exact hg
  have h := (hasSum_nat_add_iff
    (f := fun i ↦ primeTwistCoeff r i * primeTwistCoeff r (i + n)) 1).mp htail
  rw [Finset.sum_range_one] at h
  have hval : (1 - r ^ 2) * r ^ n + primeTwistCoeff r 0 * primeTwistCoeff r (0 + n) =
      if n = 0 then 1 else 0 := by
    cases n with
    | zero =>
      rw [if_pos rfl, primeTwistCoeff_zero]
      ring
    | succ m =>
      rw [if_neg (Nat.succ_ne_zero m), zero_add, primeTwistCoeff_zero, primeTwistCoeff_succ]
      ring
  rwa [hval] at h

/-- The first moment of the autocorrelation at a shift `n ≥ 0`: the sum of `(i - 1) d i d (i + n)`
is `r ^ n` for `n ≠ 0` and zero for `n = 0`. -/
theorem hasSum_primeTwistCoeff_moment {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    HasSum (fun i : ℕ ↦ ((i : ℝ) - 1) * (primeTwistCoeff r i * primeTwistCoeff r (i + n)))
      (if n = 0 then 0 else r ^ n) := by
  have hx0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hx1 : r ^ 2 < 1 := by nlinarith
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  have hnorm : ‖r ^ 2‖ < 1 := by rwa [Real.norm_of_nonneg hx0]
  have hg := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left ((1 - r ^ 2) ^ 2 * r ^ n)
  have htail : HasSum (fun l : ℕ ↦ (((l + 1 : ℕ) : ℝ) - 1) *
      (primeTwistCoeff r (l + 1) * primeTwistCoeff r (l + 1 + n))) (r ^ (n + 2)) := by
    have he : (fun l : ℕ ↦ (((l + 1 : ℕ) : ℝ) - 1) *
        (primeTwistCoeff r (l + 1) * primeTwistCoeff r (l + 1 + n))) =
        fun l : ℕ ↦ (1 - r ^ 2) ^ 2 * r ^ n * ((l : ℝ) * (r ^ 2) ^ l) := by
      funext l
      rw [show l + 1 + n = (l + n) + 1 by omega, primeTwistCoeff_succ, primeTwistCoeff_succ]
      push_cast
      ring
    have hv : r ^ (n + 2) = (1 - r ^ 2) ^ 2 * r ^ n * (r ^ 2 / (1 - r ^ 2) ^ 2) := by
      field_simp
      ring
    rw [he, hv]
    exact hg
  have h := (hasSum_nat_add_iff (f := fun i : ℕ ↦ ((i : ℝ) - 1) *
    (primeTwistCoeff r i * primeTwistCoeff r (i + n))) 1).mp htail
  rw [Finset.sum_range_one] at h
  have hval : r ^ (n + 2) + (((0 : ℕ) : ℝ) - 1) *
      (primeTwistCoeff r 0 * primeTwistCoeff r (0 + n)) = if n = 0 then 0 else r ^ n := by
    cases n with
    | zero =>
      rw [if_pos rfl, primeTwistCoeff_zero]
      push_cast
      ring
    | succ m =>
      rw [if_neg (Nat.succ_ne_zero m), zero_add, primeTwistCoeff_zero, primeTwistCoeff_succ]
      push_cast
      ring
  rwa [hval] at h

/-- The first moment of the autocorrelation at a shift `-(n + 1)`: the sum of
`(j + n) d (j + n + 1) d j` is `r ^ (n + 1)`. -/
theorem hasSum_primeTwistCoeff_moment_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    HasSum (fun j : ℕ ↦ ((j : ℝ) + n) *
      (primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j)) (r ^ (n + 1)) := by
  have hx0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hx1 : r ^ 2 < 1 := by nlinarith
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  have hnorm : ‖r ^ 2‖ < 1 := by rwa [Real.norm_of_nonneg hx0]
  have hg1 := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left
    ((1 - r ^ 2) ^ 2 * r ^ (n + 1))
  have hg2 := (hasSum_geometric_of_lt_one hx0 hx1).mul_left
    ((1 - r ^ 2) ^ 2 * r ^ (n + 1) * (1 + n))
  have htail : HasSum (fun l : ℕ ↦ (((l + 1 : ℕ) : ℝ) + n) *
      (primeTwistCoeff r (l + 1 + n + 1) * primeTwistCoeff r (l + 1)))
      (r ^ (n + 1) * (r ^ 2 + (1 + n) * (1 - r ^ 2))) := by
    have he : (fun l : ℕ ↦ (((l + 1 : ℕ) : ℝ) + n) *
        (primeTwistCoeff r (l + 1 + n + 1) * primeTwistCoeff r (l + 1))) =
        fun l : ℕ ↦ (1 - r ^ 2) ^ 2 * r ^ (n + 1) * ((l : ℝ) * (r ^ 2) ^ l) +
          (1 - r ^ 2) ^ 2 * r ^ (n + 1) * (1 + n) * (r ^ 2) ^ l := by
      funext l
      rw [primeTwistCoeff_succ, primeTwistCoeff_succ]
      push_cast
      ring
    have hv : r ^ (n + 1) * (r ^ 2 + (1 + n) * (1 - r ^ 2)) =
        (1 - r ^ 2) ^ 2 * r ^ (n + 1) * (r ^ 2 / (1 - r ^ 2) ^ 2) +
          (1 - r ^ 2) ^ 2 * r ^ (n + 1) * (1 + n) * (1 - r ^ 2)⁻¹ := by
      field_simp
    rw [he, hv]
    exact hg1.add hg2
  have h := (hasSum_nat_add_iff (f := fun j : ℕ ↦ ((j : ℝ) + n) *
    (primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j)) 1).mp htail
  rw [Finset.sum_range_one] at h
  have hval : r ^ (n + 1) * (r ^ 2 + (1 + n) * (1 - r ^ 2)) + (((0 : ℕ) : ℝ) + n) *
      (primeTwistCoeff r (0 + n + 1) * primeTwistCoeff r 0) = r ^ (n + 1) := by
    rw [zero_add, primeTwistCoeff_zero, primeTwistCoeff_succ]
    push_cast
    ring
  rwa [hval] at h

/-- The test function of `T ^ k A_ψ` for `c = p ^ k`: `u ↦ c ψ (c u)`. -/
def scaleTest (ψ : ℝ → ℂ) (c : ℝ) (u : ℝ) : ℂ := (c : ℂ) * ψ (c * u)

theorem scaleTest_one_left (ψ : ℝ → ℂ) : scaleTest ψ 1 = ψ := by
  funext u
  simp [scaleTest]

/-- The scaled test function is supported in the scaled interval. -/
theorem scaleTest_eq_zero {ψ : ℝ → ℂ} {a b : ℝ} (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {c : ℝ}
    (hc : 0 < c) {u : ℝ} (hu : u ∉ Icc (a / c) (b / c)) : scaleTest ψ c u = 0 := by
  rw [scaleTest, hψ0 (c * u) fun h ↦
    hu ⟨(div_le_iff₀' hc).mpr h.1, (le_div_iff₀' hc).mpr h.2⟩, mul_zero]

theorem continuous_scaleTest {ψ : ℝ → ℂ} (hψ : Continuous ψ) (c : ℝ) :
    Continuous (scaleTest ψ c) :=
  continuous_const.mul (hψ.comp (continuous_const.mul continuous_id))

theorem integrable_scaleTest {ψ : ℝ → ℂ} (hψ : Integrable ψ) {c : ℝ} (hc : 0 < c) :
    Integrable (scaleTest ψ c) :=
  (hψ.comp_mul_left' hc.ne').const_mul _

/-- Scaling keeps the integral of the absolute value. -/
theorem integral_norm_scaleTest (ψ : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ u, ‖scaleTest ψ c u‖ = ∫ g, ‖ψ g‖ := by
  have h := Measure.integral_comp_mul_left (fun g ↦ ‖ψ g‖) c
  have he : (fun u ↦ ‖scaleTest ψ c u‖) = fun u ↦ c * ‖ψ (c * u)‖ := by
    funext u
    rw [scaleTest, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [he, integral_const_mul, h, abs_of_pos (inv_pos.mpr hc), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul]

/-- A Lipschitz test function stays Lipschitz at `1` after scaling. -/
theorem norm_scaleTest_sub_le {ψ : ℝ → ℂ} {K : ℝ}
    (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) {c : ℝ} (hc : 0 < c) (g : ℝ) :
    ‖scaleTest ψ c g - scaleTest ψ c 1‖ ≤ c ^ 2 * K * |g - 1| := by
  have h := hK (c * g) (c * 1)
  rw [← mul_sub, abs_mul, abs_of_pos hc] at h
  rw [scaleTest, scaleTest, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc]
  calc c * ‖ψ (c * g) - ψ (c * 1)‖ ≤ c * (K * (c * |g - 1|)) :=
        mul_le_mul_of_nonneg_left h hc.le
    _ = c ^ 2 * K * |g - 1| := by ring

section Blocks

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- The trace of the block `Q M_X A_{ψ_c} Q`: the integral of the scaled test function against
the sharp trace at cutoff `X`. -/
def primeBlock (ψ : ℝ → ℂ) (c X : ℝ) : ℂ :=
  ∫ u, scaleTest ψ c u * realPWSharpTrace Y 0 0 hs u X

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀

/-- Reconstruction: `primeBlock` is the trace of an operator. For a continuous test function
supported in `[a, b]`, `0 < a`, and a scale `c > 0`, the compression to the band of the cutoff
to `[-X, X]` of the action of the scaled test function is nuclear, and its trace is
`primeBlock`. This is `exists_realPWTestCutoff_nuclear` for the scaled test function. -/
theorem exists_primeBlock_nuclear (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {c : ℝ} (hc : 0 < c) (X : ℝ) :
    ∃ T : nuclearEndomorphisms V₀,
      (∀ f : V₀, ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask X x *
          ∫ g, scaleTest ψ c g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) ∧
        T.val f = (V₀).orthogonalProjectionOnto r) ∧
      hilbertTrace T = primeBlock Y hs ψ c X :=
  exists_realPWTestCutoff_nuclear Y 0 0 hs hY le_rfl (div_pos ha0 hc) (scaleTest ψ c)
    (continuous_scaleTest hψc c) (fun _ hg ↦ scaleTest_eq_zero hψ0 hc hg) X

/-- The trace of a block less its logarithmic term. -/
def primeBlockRemainder (ψ : ℝ → ℂ) (c X : ℝ) : ℂ :=
  primeBlock Y hs ψ c X - scaleTest ψ c 1 * ((Real.log (2 * π * Y * X) : ℝ) : ℂ)

/-- The limit of `primeBlockRemainder` as the cutoff is removed. -/
def primeBlockLimit (ψ : ℝ → ℂ) (c : ℝ) : ℂ :=
  scaleTest ψ c 1 * ((sincLogConstant / π : ℝ) : ℂ) +
    ∫ g, (scaleTest ψ c g - scaleTest ψ c 1 * ((logTermProfile g : ℝ) : ℂ)) *
      ((realTermDensity g : ℝ) : ℂ)

/-- Reconstruction: each block has the logarithmic growth of
`tendsto_integral_realPWSharpTrace_sub_log`. -/
theorem tendsto_primeBlockRemainder (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X ↦ primeBlockRemainder Y hs ψ c X) atTop (𝓝 (primeBlockLimit ψ c)) :=
  tendsto_integral_realPWSharpTrace_sub_log Y hs hY (div_pos ha0 hc) (scaleTest ψ c)
    (integrable_scaleTest
      (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hc)
    (fun _ hg ↦ scaleTest_eq_zero hψ0 hc hg)
    (norm_sub_mul_logTermProfile_le (norm_scaleTest_sub_le hK hc))

/-- Without weight the sharp trace of a dilation by a factor at most one half or at least two
is at most `6`, for every bandwidth and every cutoff. -/
theorem norm_realPWSharpTrace_zero_zero_le_six (hY : 0 < Y) {u : ℝ} (hu0 : 0 < u)
    (hu : u ≤ 1 / 2 ∨ 2 ≤ u) {X : ℝ} (hX : 0 ≤ X) :
    ‖realPWSharpTrace Y 0 0 hs u X‖ ≤ 6 := by
  have key : ∀ {v X' : ℝ}, 0 < v → v ≤ 1 / 2 → 0 ≤ X' →
      ‖realPWSharpTrace Y 0 0 hs v X'‖ ≤ 6 := by
    intro v X' hv0 hv hX'
    have h := norm_realPWSharpTrace_zero_zero_le Y hs hY hv0 (by linarith) hX'
    have h1 : v ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hv0.le (by linarith) (by norm_num)
    have h0 : 0 ≤ v ^ (1 / 2 : ℝ) := Real.rpow_nonneg hv0.le _
    have h2 : |v - 1|⁻¹ ≤ 2 := by
      rw [abs_of_neg (by linarith), neg_sub, inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have h3 : 0 ≤ |v - 1|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
    calc ‖realPWSharpTrace Y 0 0 hs v X'‖ ≤ 2 * v ^ (1 / 2 : ℝ) * (|v - 1|⁻¹ + 1) := h
      _ ≤ 2 * 1 * (2 + 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) (by linarith) (by linarith)
            (by norm_num)
      _ = 6 := by norm_num
  rcases hu with h | h
  · exact key hu0 h hX
  · rw [realPWSharpTrace_zero_zero_eq_star_inv Y hs hu0 X, norm_star]
    refine key (inv_pos.mpr hu0) ?_ (div_nonneg hX hu0.le)
    rw [inv_le_comm₀ hu0 (by norm_num)]
    linarith

/-- Reconstruction: when the scaled test function is supported below one half or above two,
its value at `1` is zero and the trace of its block is at most six times the integral of
`|ψ|`, for every cutoff. -/
theorem norm_primeBlock_le_of_far (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {c : ℝ} (hc : 0 < c)
    (hfar : 2 * b ≤ c ∨ c ≤ a / 2) {X : ℝ} (hX : 0 ≤ X) :
    scaleTest ψ c 1 = 0 ∧ ‖primeBlock Y hs ψ c X‖ ≤ 6 * ∫ g, ‖ψ g‖ := by
  have hψ : Integrable ψ :=
    hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)
  have hsupp : ∀ u, scaleTest ψ c u ≠ 0 → 0 < u ∧ (u ≤ 1 / 2 ∨ 2 ≤ u) := by
    intro u hu
    have hmem : u ∈ Icc (a / c) (b / c) := by
      by_contra h
      exact hu (scaleTest_eq_zero hψ0 hc h)
    refine ⟨(div_pos ha0 hc).trans_le hmem.1, ?_⟩
    rcases hfar with h | h
    · exact Or.inl (hmem.2.trans ((div_le_iff₀ hc).mpr (by linarith)))
    · exact Or.inr (((le_div_iff₀ hc).mpr (by linarith)).trans hmem.1)
  refine ⟨?_, ?_⟩
  · by_contra h
    obtain ⟨-, h1 | h1⟩ := hsupp 1 h <;> norm_num at h1
  · calc ‖primeBlock Y hs ψ c X‖ ≤ ∫ u, ‖scaleTest ψ c u‖ * 6 := by
          refine norm_integral_le_of_norm_le ((integrable_scaleTest hψ hc).norm.mul_const 6)
            (ae_of_all _ fun u ↦ ?_)
          rw [norm_mul]
          by_cases hu : scaleTest ψ c u = 0
          · rw [hu, norm_zero, zero_mul, zero_mul]
          · obtain ⟨hu0, hu'⟩ := hsupp u hu
            exact mul_le_mul_of_nonneg_left
              (norm_realPWSharpTrace_zero_zero_le_six Y hs hY hu0 hu' hX) (norm_nonneg _)
      _ = 6 * ∫ g, ‖ψ g‖ := by
          rw [integral_mul_const, integral_norm_scaleTest ψ hc, mul_comm]

/-- Reconstruction: one constant bounds the remainders of all the blocks at the scales
`p ^ n` and `p ^ (-(n + 1))`, for every large enough cutoff. Only finitely many of the scaled
test functions have support meeting `[1/2, 2]`. For those the remainder converges, and for
the others the block is bounded by `norm_primeBlock_le_of_far`. -/
theorem exists_eventually_norm_primeBlockRemainder_le (hY : 0 < Y) {p : ℝ} (hp : 1 < p)
    {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0)
    {K : ℝ} (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) :
    ∃ B : ℝ, ∀ᶠ X in atTop, ∀ n : ℕ,
      ‖primeBlockRemainder Y hs ψ (p ^ n) X‖ ≤ B ∧
        ‖primeBlockRemainder Y hs ψ ((p ^ (n + 1))⁻¹) X‖ ≤ B := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨N₁, hN₁⟩ := pow_unbounded_of_one_lt (2 * b) hp
  obtain ⟨N₂, hN₂⟩ := pow_unbounded_of_one_lt (2 / a) hp
  let N := max N₁ N₂
  have hfarU : ∀ n, N ≤ n → 2 * b ≤ p ^ n := fun n hn ↦
    hN₁.le.trans (pow_le_pow_right₀ hp.le ((le_max_left _ _).trans hn))
  have hfarL : ∀ n, N ≤ n → (p ^ (n + 1))⁻¹ ≤ a / 2 := by
    intro n hn
    have h1 : 2 / a ≤ p ^ (n + 1) :=
      hN₂.le.trans (pow_le_pow_right₀ hp.le (((le_max_right _ _).trans hn).trans n.le_succ))
    rw [inv_le_comm₀ (pow_pos hp0 _) (half_pos ha0)]
    calc (a / 2)⁻¹ = 2 / a := by rw [inv_div]
      _ ≤ p ^ (n + 1) := h1
  let SU := ∑ n ∈ Finset.range N, (‖primeBlockLimit ψ (p ^ n)‖ + 1)
  let SL := ∑ n ∈ Finset.range N, (‖primeBlockLimit ψ ((p ^ (n + 1))⁻¹)‖ + 1)
  have hSU0 : ∀ n ∈ Finset.range N, 0 ≤ ‖primeBlockLimit ψ (p ^ n)‖ + 1 := fun n _ ↦ by
    positivity
  have hSL0 : ∀ n ∈ Finset.range N, 0 ≤ ‖primeBlockLimit ψ ((p ^ (n + 1))⁻¹)‖ + 1 :=
    fun n _ ↦ by positivity
  have hI0 : 0 ≤ 6 * ∫ g, ‖ψ g‖ :=
    mul_nonneg (by norm_num) (integral_nonneg fun g ↦ norm_nonneg _)
  refine ⟨6 * (∫ g, ‖ψ g‖) + SU + SL, ?_⟩
  have hU : ∀ n ∈ Finset.range N, ∀ᶠ X in atTop,
      ‖primeBlockRemainder Y hs ψ (p ^ n) X‖ ≤ ‖primeBlockLimit ψ (p ^ n)‖ + 1 := fun n _ ↦
    ((tendsto_primeBlockRemainder Y hs hY ha0 hψc hψ0 hK (pow_pos hp0 n)).norm.eventually
      (gt_mem_nhds (lt_add_one _))).mono fun X h ↦ h.le
  have hL : ∀ n ∈ Finset.range N, ∀ᶠ X in atTop,
      ‖primeBlockRemainder Y hs ψ ((p ^ (n + 1))⁻¹) X‖ ≤
        ‖primeBlockLimit ψ ((p ^ (n + 1))⁻¹)‖ + 1 := fun n _ ↦
    ((tendsto_primeBlockRemainder Y hs hY ha0 hψc hψ0 hK
      (inv_pos.mpr (pow_pos hp0 (n + 1)))).norm.eventually
      (gt_mem_nhds (lt_add_one _))).mono fun X h ↦ h.le
  filter_upwards [(Filter.eventually_all_finset _).mpr hU,
    (Filter.eventually_all_finset _).mpr hL, eventually_ge_atTop (0 : ℝ)] with X hXU hXL hX0 n
  by_cases hn : n < N
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
    have h1 := Finset.single_le_sum hSU0 hmem
    have h2 := Finset.single_le_sum hSL0 hmem
    have h3 : 0 ≤ SU := Finset.sum_nonneg hSU0
    have h4 : 0 ≤ SL := Finset.sum_nonneg hSL0
    exact ⟨(hXU n hmem).trans (by linarith), (hXL n hmem).trans (by linarith)⟩
  · have hn' : N ≤ n := not_lt.mp hn
    have h3 : 0 ≤ SU := Finset.sum_nonneg hSU0
    have h4 : 0 ≤ SL := Finset.sum_nonneg hSL0
    obtain ⟨hz1, hb1⟩ := norm_primeBlock_le_of_far Y hs hY ha0 hψc hψ0 (pow_pos hp0 n)
      (Or.inl (hfarU n hn')) hX0
    obtain ⟨hz2, hb2⟩ := norm_primeBlock_le_of_far Y hs hY ha0 hψc hψ0
      (inv_pos.mpr (pow_pos hp0 (n + 1))) (Or.inr (hfarL n hn')) hX0
    constructor
    · rw [primeBlockRemainder, hz1, zero_mul, sub_zero]
      exact hb1.trans (by linarith)
    · rw [primeBlockRemainder, hz2, zero_mul, sub_zero]
      exact hb2.trans (by linarith)

end Blocks

/-- The autocorrelation at a shift `-(n + 1)` is zero. -/
theorem hasSum_primeTwistCoeff_mul_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    HasSum (fun j ↦ primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j) 0 := by
  have h := hasSum_primeTwistCoeff_mul hr0 hr1 (n + 1)
  rw [if_neg (Nat.succ_ne_zero n)] at h
  have he : (fun j ↦ primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j) =
      fun i ↦ primeTwistCoeff r i * primeTwistCoeff r (i + (n + 1)) :=
    funext fun j ↦ mul_comm _ _
  rw [he]
  exact h

/-- A summable bound for the products of two coefficients, indexed by the shift and the
position. -/
def primeTwistBound (r : ℝ) (x : ℕ × ℕ) : ℝ := r⁻¹ ^ 2 * (r ^ x.1 * (r ^ 2) ^ x.2)

theorem primeTwistBound_nonneg {r : ℝ} (hr0 : 0 < r) (x : ℕ × ℕ) : 0 ≤ primeTwistBound r x := by
  unfold primeTwistBound
  positivity

theorem summable_primeTwistBound {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (primeTwistBound r) :=
  ((summable_geometric_of_lt_one hr0.le hr1).mul_of_nonneg
    (summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith))
    (fun n ↦ pow_nonneg hr0.le n) (fun i ↦ pow_nonneg (sq_nonneg r) i)).mul_left _

theorem summable_primeTwistBound_linear {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun x : ℕ × ℕ ↦ ((x.1 : ℝ) + 1) * ((x.2 : ℝ) + 1) * primeTwistBound r x) := by
  have hlin : ∀ {x : ℝ}, 0 ≤ x → x < 1 → Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * x ^ n) := by
    intro x hx0 hx1
    have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rwa [Real.norm_of_nonneg hx0] : ‖x‖ < 1)).summable
    have h2 := summable_geometric_of_lt_one hx0 hx1
    exact (h1.add h2).congr fun n ↦ by ring
  have h := ((hlin hr0.le hr1).mul_of_nonneg (hlin (sq_nonneg r) (by nlinarith))
    (fun n ↦ by positivity) (fun i ↦ by positivity)).mul_left (r⁻¹ ^ 2)
  refine h.congr fun x ↦ ?_
  unfold primeTwistBound
  ring

theorem abs_primeTwistCoeff_mul_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n i : ℕ) :
    |primeTwistCoeff r i * primeTwistCoeff r (i + n)| ≤ primeTwistBound r (n, i) := by
  rw [abs_mul]
  calc |primeTwistCoeff r i| * |primeTwistCoeff r (i + n)|
      ≤ (r⁻¹ * r ^ i) * (r⁻¹ * r ^ (i + n)) :=
        mul_le_mul (abs_primeTwistCoeff_le hr0 hr1 i) (abs_primeTwistCoeff_le hr0 hr1 (i + n))
          (abs_nonneg _) (by positivity)
    _ = primeTwistBound r (n, i) := by
        unfold primeTwistBound
        ring

theorem abs_primeTwistCoeff_mul_lower_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n j : ℕ) :
    |primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j| ≤ primeTwistBound r (n, j) := by
  rw [abs_mul]
  have h1 : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1.le n.le_succ
  calc |primeTwistCoeff r (j + n + 1)| * |primeTwistCoeff r j|
      ≤ (r⁻¹ * r ^ (j + n + 1)) * (r⁻¹ * r ^ j) :=
        mul_le_mul (abs_primeTwistCoeff_le hr0 hr1 (j + n + 1))
          (abs_primeTwistCoeff_le hr0 hr1 j) (abs_nonneg _) (by positivity)
    _ = r⁻¹ ^ 2 * (r ^ (n + 1) * (r ^ 2) ^ j) := by ring
    _ ≤ r⁻¹ ^ 2 * (r ^ n * (r ^ 2) ^ j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity))
          (by positivity)

/-- The product of the coefficients of the pair `(i, i + n)`, indexed by `(n, i)`. -/
def primeUpperCoeff (r : ℝ) (x : ℕ × ℕ) : ℝ :=
  primeTwistCoeff r x.2 * primeTwistCoeff r (x.2 + x.1)

/-- The product of the coefficients of the pair `(j + n + 1, j)`, indexed by `(n, j)`. -/
def primeLowerCoeff (r : ℝ) (x : ℕ × ℕ) : ℝ :=
  primeTwistCoeff r (x.2 + x.1 + 1) * primeTwistCoeff r x.2

theorem abs_primeUpperCoeff_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : ℕ × ℕ) :
    |primeUpperCoeff r x| ≤ primeTwistBound r x :=
  abs_primeTwistCoeff_mul_le hr0 hr1 x.1 x.2

theorem abs_primeLowerCoeff_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (x : ℕ × ℕ) :
    |primeLowerCoeff r x| ≤ primeTwistBound r x :=
  abs_primeTwistCoeff_mul_lower_le hr0 hr1 x.1 x.2

/-- The values at `1` of the scaled test functions are bounded. -/
theorem exists_norm_scaleTest_one_le {ψ : ℝ → ℂ} {a b : ℝ} (hψ0 : ∀ g ∉ Icc a b, ψ g = 0)
    {K : ℝ} (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c : ℝ, 0 < c → ‖scaleTest ψ c 1‖ ≤ A := by
  refine ⟨|b| * (|K| * (|b| + 1 + |a|)), by positivity, fun c hc ↦ ?_⟩
  rw [scaleTest, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  by_cases hmem : c ∈ Icc a b
  · have h0 : ψ (b + 1) = 0 := hψ0 _ fun h ↦ by linarith [h.2]
    have h1 := hK c (b + 1)
    rw [h0, sub_zero] at h1
    have h2 : |c - (b + 1)| ≤ |b| + 1 + |a| := by
      rw [abs_le]
      constructor <;>
        linarith [hmem.1, hmem.2, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self a]
    have h3 : ‖ψ c‖ ≤ |K| * (|b| + 1 + |a|) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg K)))
    exact mul_le_mul (hmem.2.trans (le_abs_self b)) h3 (norm_nonneg _) (abs_nonneg b)
  · rw [hψ0 c hmem, norm_zero, mul_zero]
    positivity

/-- A sum over pairs, of a real coefficient times a function of the first index, is the sum
over the first index of the fiber sums of the coefficient times the function. -/
theorem hasSum_fiber_mul {coef : ℕ × ℕ → ℝ} {v : ℕ → ℂ} {σ : ℕ → ℝ}
    (hsum : Summable fun x : ℕ × ℕ ↦ ((coef x : ℝ) : ℂ) * v x.1)
    (hf : ∀ n, HasSum (fun i ↦ coef (n, i)) (σ n)) :
    HasSum (fun n ↦ ((σ n : ℝ) : ℂ) * v n) (∑' x : ℕ × ℕ, ((coef x : ℝ) : ℂ) * v x.1) :=
  hsum.hasSum.prod_fiberwise fun n ↦ by
    have h := (Complex.ofRealCLM.hasSum (hf n)).mul_right (v n)
    simpa using h

section Series

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- Reconstruction: the sum over pairs of a coefficient times the remainder of a block
converges, as the cutoff is removed, to the sum of the coefficient times the limit of the
block. The coefficients are dominated by `primeTwistBound` and the remainders are bounded
uniformly for large cutoffs, so this is dominated convergence for series. -/
theorem tendsto_tsum_primeBlockRemainder {p : ℝ} (hp : 1 < p) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (ψ : ℝ → ℂ) (coef : ℕ × ℕ → ℝ)
    (hcoef : ∀ x, |coef x| ≤ primeTwistBound r x) (c : ℕ → ℝ) (e : ℕ × ℕ → ℕ) {B : ℝ}
    (hB : ∀ᶠ X in atTop, ∀ n, ‖primeBlockRemainder Y hs ψ (c n) X‖ ≤ B)
    (hlim : ∀ n, Tendsto (fun X ↦ primeBlockRemainder Y hs ψ (c n) X) atTop
      (𝓝 (primeBlockLimit ψ (c n)))) :
    (∀ᶠ L in atTop, Summable fun x : ℕ × ℕ ↦ ((coef x : ℝ) : ℂ) *
      primeBlockRemainder Y hs ψ (c x.1) (L * p ^ e x / p)) ∧
    Summable (fun x : ℕ × ℕ ↦ ((coef x : ℝ) : ℂ) * primeBlockLimit ψ (c x.1)) ∧
    Tendsto (fun L ↦ ∑' x : ℕ × ℕ, ((coef x : ℝ) : ℂ) *
      primeBlockRemainder Y hs ψ (c x.1) (L * p ^ e x / p)) atTop
      (𝓝 (∑' x : ℕ × ℕ, ((coef x : ℝ) : ℂ) * primeBlockLimit ψ (c x.1))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hB
  have hsum : Summable (fun x ↦ primeTwistBound r x * B) :=
    (summable_primeTwistBound hr0 hr1).mul_right B
  have hX : ∀ L, max (p * X₁) 0 ≤ L → ∀ x : ℕ × ℕ, X₁ ≤ L * p ^ e x / p := by
    intro L hL x
    have hL0 : 0 ≤ L := (le_max_right _ _).trans hL
    have h1 : p * X₁ ≤ L := (le_max_left _ _).trans hL
    have h2 : (1 : ℝ) ≤ p ^ e x := one_le_pow₀ hp.le
    rw [le_div_iff₀ hp0]
    calc X₁ * p = p * X₁ := mul_comm _ _
      _ ≤ L := h1
      _ = L * 1 := (mul_one L).symm
      _ ≤ L * p ^ e x := mul_le_mul_of_nonneg_left h2 hL0
  have hbound : ∀ L, max (p * X₁) 0 ≤ L → ∀ x : ℕ × ℕ, ‖((coef x : ℝ) : ℂ) *
      primeBlockRemainder Y hs ψ (c x.1) (L * p ^ e x / p)‖ ≤ primeTwistBound r x * B := by
    intro L hL x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hcoef x) (hX₁ _ (hX L hL x) x.1) (norm_nonneg _)
      ((abs_nonneg _).trans (hcoef x))
  have hlimB : ∀ n, ‖primeBlockLimit ψ (c n)‖ ≤ B := fun n ↦
    le_of_tendsto (hlim n).norm (eventually_atTop.mpr ⟨X₁, fun X hX' ↦ hX₁ X hX' n⟩)
  refine ⟨eventually_atTop.mpr ⟨max (p * X₁) 0, fun L hL ↦
    Summable.of_norm_bounded hsum (hbound L hL)⟩,
    Summable.of_norm_bounded hsum fun x ↦ ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hcoef x) (hlimB x.1) (norm_nonneg _) ((abs_nonneg _).trans (hcoef x))
  · refine tendsto_tsum_of_dominated_convergence hsum (fun x ↦ ?_)
      (eventually_atTop.mpr ⟨max (p * X₁) 0, hbound⟩)
    have hscale : Tendsto (fun L : ℝ ↦ L * p ^ e x / p) atTop atTop :=
      (tendsto_id.atTop_mul_const (pow_pos hp0 _)).atTop_div_const hp0
    exact ((hlim x.1).comp hscale).const_mul _

/-- Reconstruction: the logarithmic terms of the blocks sum to the logarithm of the cutoff
times the autocorrelation sums, plus `log p` times the first-moment sums. The cutoff of the
block at `x` is `L p ^ (e x) / p`, whose logarithm is `log (2πYL) + (e x - 1) log p`. -/
theorem tsum_primeLogTerm {p : ℝ} (hp : 1 < p) (hY : 0 < Y) (coef : ℕ × ℕ → ℝ)
    (e : ℕ × ℕ → ℕ) (a : ℕ → ℂ) (σ μ : ℕ → ℝ)
    (hs1 : Summable fun x : ℕ × ℕ ↦ ((coef x : ℝ) : ℂ) * a x.1)
    (hs2 : Summable fun x : ℕ × ℕ ↦ ((((e x : ℝ) - 1) * coef x : ℝ) : ℂ) * a x.1)
    (hσ : ∀ n, HasSum (fun i ↦ coef (n, i)) (σ n))
    (hμ : ∀ n, HasSum (fun i ↦ ((e (n, i) : ℝ) - 1) * coef (n, i)) (μ n)) {L : ℝ}
    (hL : 0 < L) :
    Summable (fun x : ℕ × ℕ ↦ ((coef x : ℝ) : ℂ) *
      (a x.1 * ((Real.log (2 * π * Y * (L * p ^ e x / p)) : ℝ) : ℂ))) ∧
    ∑' x : ℕ × ℕ, ((coef x : ℝ) : ℂ) *
        (a x.1 * ((Real.log (2 * π * Y * (L * p ^ e x / p)) : ℝ) : ℂ)) =
      ((Real.log (2 * π * Y * L) : ℝ) : ℂ) * ∑' n, ((σ n : ℝ) : ℂ) * a n +
        ((Real.log p : ℝ) : ℂ) * ∑' n, ((μ n : ℝ) : ℂ) * a n := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hπ : 0 < π := Real.pi_pos
  have hlog : ∀ x : ℕ × ℕ, Real.log (2 * π * Y * (L * p ^ e x / p)) =
      Real.log (2 * π * Y * L) + ((e x : ℝ) - 1) * Real.log p := by
    intro x
    have h1 : 2 * π * Y * (L * p ^ e x / p) = 2 * π * Y * L * p ^ e x / p := by ring
    have h2 : 2 * π * Y * L ≠ 0 := by positivity
    rw [h1, Real.log_div (mul_ne_zero h2 (pow_pos hp0 _).ne') hp0.ne',
      Real.log_mul h2 (pow_pos hp0 _).ne', Real.log_pow]
    ring
  have he : (fun x : ℕ × ℕ ↦ ((coef x : ℝ) : ℂ) *
      (a x.1 * ((Real.log (2 * π * Y * (L * p ^ e x / p)) : ℝ) : ℂ))) =
      fun x : ℕ × ℕ ↦ ((Real.log (2 * π * Y * L) : ℝ) : ℂ) * (((coef x : ℝ) : ℂ) * a x.1) +
        ((Real.log p : ℝ) : ℂ) * (((((e x : ℝ) - 1) * coef x : ℝ) : ℂ) * a x.1) := by
    funext x
    rw [hlog x]
    push_cast
    ring
  rw [he]
  refine ⟨(hs1.mul_left _).add (hs2.mul_left _), ?_⟩
  rw [(hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    (hasSum_fiber_mul hs1 hσ).tsum_eq, (hasSum_fiber_mul hs2 hμ).tsum_eq]

/-- A term of the series of the pairs `(i, i + n)`: the product of the two coefficients times
the trace of the block at scale `p ^ n` and cutoff `L p ^ (i - 1)`. The index is `(n, i)`. -/
def primeUpperTerm (r p : ℝ) (ψ : ℝ → ℂ) (L : ℝ) (x : ℕ × ℕ) : ℂ :=
  ((primeUpperCoeff r x : ℝ) : ℂ) * primeBlock Y hs ψ (p ^ x.1) (L * p ^ x.2 / p)

/-- A term of the series of the pairs `(j + n + 1, j)`: the product of the two coefficients
times the trace of the block at scale `p ^ (-(n + 1))` and cutoff `L p ^ (j + n)`. The index is
`(n, j)`. -/
def primeLowerTerm (r p : ℝ) (ψ : ℝ → ℂ) (L : ℝ) (x : ℕ × ℕ) : ℂ :=
  ((primeLowerCoeff r x : ℝ) : ℂ) *
    primeBlock Y hs ψ ((p ^ (x.1 + 1))⁻¹) (L * p ^ (x.2 + x.1 + 1) / p)

/-- The series of traces of `Q (U⁻¹ M_L U) A_ψ Q`: the sum over all pairs `(i, j)` of
`d i d j` times the trace of `Q M_{L p ^ (i - 1)} A_{ψ_{j - i}} Q`. The pairs with `i ≤ j` and
those with `i > j` are summed separately. -/
def primeTraceSeries (r p : ℝ) (ψ : ℝ → ℂ) (L : ℝ) : ℂ :=
  (∑' x, primeUpperTerm Y hs r p ψ L x) + ∑' x, primeLowerTerm Y hs r p ψ L x

end Series

section FiberSums

/-- Summed over all pairs `(i, i + n)`, the coefficients times a function of the shift give
the value of the function at shift zero. -/
theorem tsum_primeUpperCoeff_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {v : ℕ → ℂ}
    (hsum : Summable fun x : ℕ × ℕ ↦ ((primeUpperCoeff r x : ℝ) : ℂ) * v x.1) :
    ∑' x : ℕ × ℕ, ((primeUpperCoeff r x : ℝ) : ℂ) * v x.1 = v 0 := by
  have h := hasSum_fiber_mul (coef := primeUpperCoeff r) (v := v)
    (σ := fun n ↦ if n = 0 then 1 else 0) hsum
    (fun n ↦ hasSum_primeTwistCoeff_mul hr0 hr1 n)
  have he : (fun n : ℕ ↦ if n = 0 then v 0 else 0) =
      fun n : ℕ ↦ (((if n = 0 then 1 else 0 : ℝ)) : ℂ) * v n := by
    funext n
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [hn]
  have h2 : HasSum (fun n : ℕ ↦ if n = 0 then v 0 else 0)
      (∑' x : ℕ × ℕ, ((primeUpperCoeff r x : ℝ) : ℂ) * v x.1) := by
    rw [he]
    exact h
  exact h2.unique (hasSum_ite_eq 0 _)

/-- Summed over all pairs `(j + n + 1, j)`, the coefficients times a function of the shift
give zero. -/
theorem tsum_primeLowerCoeff_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {v : ℕ → ℂ}
    (hsum : Summable fun x : ℕ × ℕ ↦ ((primeLowerCoeff r x : ℝ) : ℂ) * v x.1) :
    ∑' x : ℕ × ℕ, ((primeLowerCoeff r x : ℝ) : ℂ) * v x.1 = 0 := by
  have h := hasSum_fiber_mul (coef := primeLowerCoeff r) (v := v) (σ := fun _ ↦ 0) hsum
    (fun n ↦ hasSum_primeTwistCoeff_mul_lower hr0 hr1 n)
  have he : (fun _ : ℕ ↦ (0 : ℂ)) = fun n : ℕ ↦ ((0 : ℝ) : ℂ) * v n := by
    funext n
    simp
  have h2 : HasSum (fun _ : ℕ ↦ (0 : ℂ))
      (∑' x : ℕ × ℕ, ((primeLowerCoeff r x : ℝ) : ℂ) * v x.1) := by
    rw [he]
    exact h
  exact h2.unique hasSum_zero

variable (Y : ℝ)

/-- Reconstruction: the logarithmic terms of the blocks of the pairs `(i, i + n)` sum to the
logarithm of the cutoff times the value at shift zero, plus `log p` times the sum of
`r ^ (n + 1) a (n + 1)`. -/
theorem tsum_primeUpperLog (hY : 0 < Y) {p r : ℝ} (hp : 1 < p) (hr0 : 0 < r) (hr1 : r < 1)
    {a : ℕ → ℂ} {A : ℝ} (hA : ∀ n, ‖a n‖ ≤ A) {L : ℝ} (hL : 0 < L) :
    Summable (fun x : ℕ × ℕ ↦ ((primeUpperCoeff r x : ℝ) : ℂ) *
      (a x.1 * ((Real.log (2 * π * Y * (L * p ^ x.2 / p)) : ℝ) : ℂ))) ∧
    ∑' x : ℕ × ℕ, ((primeUpperCoeff r x : ℝ) : ℂ) *
        (a x.1 * ((Real.log (2 * π * Y * (L * p ^ x.2 / p)) : ℝ) : ℂ)) =
      ((Real.log (2 * π * Y * L) : ℝ) : ℂ) * a 0 +
        ((Real.log p : ℝ) : ℂ) * ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * a (n + 1) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hs1 : Summable fun x : ℕ × ℕ ↦ ((primeUpperCoeff r x : ℝ) : ℂ) * a x.1 :=
    Summable.of_norm_bounded ((summable_primeTwistBound hr0 hr1).mul_right A) fun x ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (abs_primeUpperCoeff_le hr0 hr1 x) (hA x.1) (norm_nonneg _)
        (primeTwistBound_nonneg hr0 x)
  have hs2 : Summable fun x : ℕ × ℕ ↦
      (((((x.2 : ℕ) : ℝ) - 1) * primeUpperCoeff r x : ℝ) : ℂ) * a x.1 :=
    Summable.of_norm_bounded ((summable_primeTwistBound_linear hr0 hr1).mul_right A)
      fun x ↦ by
        have hx1 : (0 : ℝ) ≤ x.1 := Nat.cast_nonneg _
        have hx2 : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _
        have h1 : |((x.2 : ℕ) : ℝ) - 1| ≤ ((x.1 : ℝ) + 1) * ((x.2 : ℝ) + 1) := by
          rw [abs_le]
          constructor <;> nlinarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (mul_le_mul h1 (abs_primeUpperCoeff_le hr0 hr1 x) (abs_nonneg _)
          (by positivity)) (hA x.1) (norm_nonneg _)
          (mul_nonneg (by positivity) (primeTwistBound_nonneg hr0 x))
  obtain ⟨h1, h2⟩ := tsum_primeLogTerm Y hp hY (primeUpperCoeff r) (fun x ↦ x.2) a
    (fun n ↦ if n = 0 then 1 else 0) (fun n ↦ if n = 0 then 0 else r ^ n) hs1 hs2
    (fun n ↦ hasSum_primeTwistCoeff_mul hr0.le hr1 n)
    (fun n ↦ hasSum_primeTwistCoeff_moment hr0.le hr1 n) hL
  refine ⟨h1, ?_⟩
  have hσ : ∑' n : ℕ, (((if n = 0 then 1 else 0 : ℝ)) : ℂ) * a n = a 0 := by
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn]]
    simp
  have hμ0 : Summable (fun n : ℕ ↦ (((if n = 0 then 0 else r ^ n : ℝ)) : ℂ) * a n) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0.le hr1).mul_right A)
      fun n ↦ by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul ?_ (hA n) (norm_nonneg _) (pow_nonneg hr0.le n)
        by_cases hn : n = 0
        · rw [if_pos hn, abs_zero]
          exact pow_nonneg hr0.le n
        · rw [if_neg hn, abs_of_nonneg (pow_nonneg hr0.le n)]
  have hμ : ∑' n : ℕ, (((if n = 0 then 0 else r ^ n : ℝ)) : ℂ) * a n =
      ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * a (n + 1) := by
    rw [hμ0.tsum_eq_zero_add]
    simp
  rw [h2, hσ, hμ]

/-- Reconstruction: the logarithmic terms of the blocks of the pairs `(j + n + 1, j)` sum to
`log p` times the sum of `r ^ (n + 1) a n`. The logarithm of the cutoff does not appear. -/
theorem tsum_primeLowerLog (hY : 0 < Y) {p r : ℝ} (hp : 1 < p) (hr0 : 0 < r) (hr1 : r < 1)
    {a : ℕ → ℂ} {A : ℝ} (hA : ∀ n, ‖a n‖ ≤ A) {L : ℝ} (hL : 0 < L) :
    Summable (fun x : ℕ × ℕ ↦ ((primeLowerCoeff r x : ℝ) : ℂ) *
      (a x.1 * ((Real.log (2 * π * Y * (L * p ^ (x.2 + x.1 + 1) / p)) : ℝ) : ℂ))) ∧
    ∑' x : ℕ × ℕ, ((primeLowerCoeff r x : ℝ) : ℂ) *
        (a x.1 * ((Real.log (2 * π * Y * (L * p ^ (x.2 + x.1 + 1) / p)) : ℝ) : ℂ)) =
      ((Real.log p : ℝ) : ℂ) * ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * a n := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hs1 : Summable fun x : ℕ × ℕ ↦ ((primeLowerCoeff r x : ℝ) : ℂ) * a x.1 :=
    Summable.of_norm_bounded ((summable_primeTwistBound hr0 hr1).mul_right A) fun x ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (abs_primeLowerCoeff_le hr0 hr1 x) (hA x.1) (norm_nonneg _)
        (primeTwistBound_nonneg hr0 x)
  have hs2 : Summable fun x : ℕ × ℕ ↦
      (((((x.2 + x.1 + 1 : ℕ) : ℝ) - 1) * primeLowerCoeff r x : ℝ) : ℂ) * a x.1 :=
    Summable.of_norm_bounded ((summable_primeTwistBound_linear hr0 hr1).mul_right A)
      fun x ↦ by
        have hx1 : (0 : ℝ) ≤ x.1 := Nat.cast_nonneg _
        have hx2 : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _
        have h1 : |((x.2 + x.1 + 1 : ℕ) : ℝ) - 1| ≤ ((x.1 : ℝ) + 1) * ((x.2 : ℝ) + 1) := by
          push_cast
          rw [abs_le]
          constructor <;> nlinarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (mul_le_mul h1 (abs_primeLowerCoeff_le hr0 hr1 x) (abs_nonneg _)
          (by positivity)) (hA x.1) (norm_nonneg _)
          (mul_nonneg (by positivity) (primeTwistBound_nonneg hr0 x))
  have hμf : ∀ n, HasSum (fun j : ℕ ↦ (((j + n + 1 : ℕ) : ℝ) - 1) *
      primeLowerCoeff r (n, j)) (r ^ (n + 1)) := by
    intro n
    have h := hasSum_primeTwistCoeff_moment_lower hr0.le hr1 n
    have he : (fun j : ℕ ↦ (((j + n + 1 : ℕ) : ℝ) - 1) * primeLowerCoeff r (n, j)) =
        fun j : ℕ ↦ ((j : ℝ) + n) *
          (primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j) := by
      funext j
      change (((j + n + 1 : ℕ) : ℝ) - 1) *
        (primeTwistCoeff r (j + n + 1) * primeTwistCoeff r j) = _
      push_cast
      ring
    rw [he]
    exact h
  obtain ⟨h1, h2⟩ := tsum_primeLogTerm Y hp hY (primeLowerCoeff r) (fun x ↦ x.2 + x.1 + 1) a
    (fun _ ↦ 0) (fun n ↦ r ^ (n + 1)) hs1 hs2
    (fun n ↦ hasSum_primeTwistCoeff_mul_lower hr0.le hr1 n) hμf hL
  refine ⟨h1, ?_⟩
  rw [h2]
  simp

end FiberSums

section Main

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

/-- Reconstruction: the series of traces for the real place together with a scale `p > 1`,
less `ψ 1 log (2πYL)`, converges as the cutoff is removed. The limit is the limit for the real
place alone (`tendsto_integral_realPWSharpTrace_sub_log`) plus `log p` times the sum over
`n ≥ 1` of `r ^ n (φ (p ^ n) + φ (p ^ (-n)))`, where `φ g = g ψ g`. The real-place limits of
the blocks cancel except at shift zero, because the autocorrelation of the coefficients
vanishes off zero. The new term comes from the logarithms `log (2πY L p ^ (i - 1))` of the
cutoffs of the blocks, through the first moments of the autocorrelation.
Paper: for `r = p ^ (-1/2)` the new term is the term of the place `p` in Theorem 12.4.1.1,
(12.4.1.1), p. 514, for `F = ℚ`, and the statement is the case `k = ℚ`, `S = {∞, p}` of
A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
function*, §VII, Theorem 4, p. 31, on the functions invariant under the units of `ℚ_p`.
Deviation: the statement is about the series of traces of the blocks. That this series is the
trace of the cutoff operator on the sector of `L²(X_S)` is not formalized. The test function
is assumed Lipschitz. -/
theorem tendsto_primeTraceSeries_sub_log (hY : 0 < Y) {p r : ℝ} (hp : 1 < p) (hr0 : 0 < r)
    (hr1 : r < 1) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ} (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) :
    Tendsto (fun L ↦ primeTraceSeries Y hs r p ψ L -
        ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop
      (𝓝 (ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
        (∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ)) +
        ((Real.log p : ℝ) : ℂ) * ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) *
          (((p ^ (n + 1) : ℝ) : ℂ) * ψ (p ^ (n + 1)) +
            (((p ^ (n + 1))⁻¹ : ℝ) : ℂ) * ψ ((p ^ (n + 1))⁻¹)))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨B, hB⟩ := exists_eventually_norm_primeBlockRemainder_le Y hs hY hp ha0 hψc hψ0 hK
  obtain ⟨hRU1, hRU2, hRU3⟩ := tendsto_tsum_primeBlockRemainder Y hs hp hr0 hr1 ψ
    (primeUpperCoeff r) (abs_primeUpperCoeff_le hr0 hr1) (fun n ↦ p ^ n) (fun x ↦ x.2)
    (hB.mono fun X h n ↦ (h n).1)
    (fun n ↦ tendsto_primeBlockRemainder Y hs hY ha0 hψc hψ0 hK (pow_pos hp0 n))
  obtain ⟨hRL1, hRL2, hRL3⟩ := tendsto_tsum_primeBlockRemainder Y hs hp hr0 hr1 ψ
    (primeLowerCoeff r) (abs_primeLowerCoeff_le hr0 hr1) (fun n ↦ (p ^ (n + 1))⁻¹)
    (fun x ↦ x.2 + x.1 + 1) (hB.mono fun X h n ↦ (h n).2)
    (fun n ↦ tendsto_primeBlockRemainder Y hs hY ha0 hψc hψ0 hK
      (inv_pos.mpr (pow_pos hp0 (n + 1))))
  have hGU := tsum_primeUpperCoeff_mul hr0.le hr1
    (v := fun n ↦ primeBlockLimit ψ (p ^ n)) hRU2
  have hGL := tsum_primeLowerCoeff_mul hr0.le hr1
    (v := fun n ↦ primeBlockLimit ψ ((p ^ (n + 1))⁻¹)) hRL2
  obtain ⟨A, hA0, hA⟩ := exists_norm_scaleTest_one_le hψ0 hK
  have hAU : ∀ n : ℕ, ‖scaleTest ψ (p ^ n) 1‖ ≤ A := fun n ↦ hA _ (pow_pos hp0 n)
  have hAL : ∀ n : ℕ, ‖scaleTest ψ ((p ^ (n + 1))⁻¹) 1‖ ≤ A := fun n ↦
    hA _ (inv_pos.mpr (pow_pos hp0 (n + 1)))
  have hgeo : Summable (fun n : ℕ ↦ r ^ n * A) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_right A
  have hsa : Summable (fun n : ℕ ↦ ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ (p ^ (n + 1)) 1) :=
    Summable.of_norm_bounded hgeo fun n ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0.le _)]
      exact mul_le_mul (pow_le_pow_of_le_one hr0.le hr1.le n.le_succ) (hAU (n + 1))
        (norm_nonneg _) (pow_nonneg hr0.le n)
  have hsb : Summable (fun n : ℕ ↦ ((r ^ (n + 1) : ℝ) : ℂ) *
      scaleTest ψ ((p ^ (n + 1))⁻¹) 1) :=
    Summable.of_norm_bounded hgeo fun n ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0.le _)]
      exact mul_le_mul (pow_le_pow_of_le_one hr0.le hr1.le n.le_succ) (hAL n)
        (norm_nonneg _) (pow_nonneg hr0.le n)
  -- For large cutoffs the series is the sum of the remainders plus a constant.
  have hmain : ∀ᶠ L in atTop, primeTraceSeries Y hs r p ψ L -
      ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ) =
      (∑' x : ℕ × ℕ, ((primeUpperCoeff r x : ℝ) : ℂ) *
        primeBlockRemainder Y hs ψ (p ^ x.1) (L * p ^ x.2 / p)) +
      (∑' x : ℕ × ℕ, ((primeLowerCoeff r x : ℝ) : ℂ) *
        primeBlockRemainder Y hs ψ ((p ^ (x.1 + 1))⁻¹) (L * p ^ (x.2 + x.1 + 1) / p)) +
      ((Real.log p : ℝ) : ℂ) *
        ((∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ (p ^ (n + 1)) 1) +
          ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ ((p ^ (n + 1))⁻¹) 1) := by
    filter_upwards [hRU1, hRL1, eventually_gt_atTop (0 : ℝ)] with L hSU hSL hL
    obtain ⟨hHU, hHUv⟩ := tsum_primeUpperLog Y hY hp hr0 hr1
      (a := fun n ↦ scaleTest ψ (p ^ n) 1) hAU hL
    obtain ⟨hHL, hHLv⟩ := tsum_primeLowerLog Y hY hp hr0 hr1
      (a := fun n ↦ scaleTest ψ ((p ^ (n + 1))⁻¹) 1) hAL hL
    have hU : ∑' x, primeUpperTerm Y hs r p ψ L x =
        (∑' x : ℕ × ℕ, ((primeUpperCoeff r x : ℝ) : ℂ) *
          primeBlockRemainder Y hs ψ (p ^ x.1) (L * p ^ x.2 / p)) +
        ∑' x : ℕ × ℕ, ((primeUpperCoeff r x : ℝ) : ℂ) *
          (scaleTest ψ (p ^ x.1) 1 *
            ((Real.log (2 * π * Y * (L * p ^ x.2 / p)) : ℝ) : ℂ)) := by
      rw [← hSU.tsum_add hHU]
      refine tsum_congr fun x ↦ ?_
      rw [primeUpperTerm, primeBlockRemainder]
      ring
    have hLw : ∑' x, primeLowerTerm Y hs r p ψ L x =
        (∑' x : ℕ × ℕ, ((primeLowerCoeff r x : ℝ) : ℂ) *
          primeBlockRemainder Y hs ψ ((p ^ (x.1 + 1))⁻¹) (L * p ^ (x.2 + x.1 + 1) / p)) +
        ∑' x : ℕ × ℕ, ((primeLowerCoeff r x : ℝ) : ℂ) *
          (scaleTest ψ ((p ^ (x.1 + 1))⁻¹) 1 *
            ((Real.log (2 * π * Y * (L * p ^ (x.2 + x.1 + 1) / p)) : ℝ) : ℂ)) := by
      rw [← hSL.tsum_add hHL]
      refine tsum_congr fun x ↦ ?_
      rw [primeLowerTerm, primeBlockRemainder]
      ring
    have h1 : scaleTest ψ (p ^ 0) 1 = ψ 1 := by rw [pow_zero, scaleTest_one_left]
    rw [primeTraceSeries, hU, hLw, hHUv, hHLv, h1]
    ring
  have hlimit := ((hRU3.add hRL3).add_const (((Real.log p : ℝ) : ℂ) *
    ((∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ (p ^ (n + 1)) 1) +
      ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ ((p ^ (n + 1))⁻¹) 1))).congr'
    (hmain.mono fun L h ↦ h.symm)
  rw [hGU, hGL, add_zero] at hlimit
  have hval : ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
      (∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ)) +
      ((Real.log p : ℝ) : ℂ) * ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) *
        (((p ^ (n + 1) : ℝ) : ℂ) * ψ (p ^ (n + 1)) +
          (((p ^ (n + 1))⁻¹ : ℝ) : ℂ) * ψ ((p ^ (n + 1))⁻¹)) =
      primeBlockLimit ψ (p ^ 0) + ((Real.log p : ℝ) : ℂ) *
        ((∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ (p ^ (n + 1)) 1) +
          ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) * scaleTest ψ ((p ^ (n + 1))⁻¹) 1) := by
    rw [← hsa.tsum_add hsb]
    have h1 : primeBlockLimit ψ (p ^ 0) = ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
        ∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ) := by
      simp only [pow_zero, primeBlockLimit, scaleTest_one_left]
    rw [h1]
    congr 2
    refine tsum_congr fun n ↦ ?_
    simp only [scaleTest, mul_one]
    ring
  rw [hval]
  exact hlimit

end Main

end RiemannMasullo.Isolated
