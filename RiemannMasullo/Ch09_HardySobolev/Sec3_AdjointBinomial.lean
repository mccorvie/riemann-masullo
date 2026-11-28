module

public import RiemannMasullo.Ch09_HardySobolev.Sec3_TestSeries
public import Mathlib.Analysis.Analytic.Binomial

/-! # The adjoint of a weighted convolution for the density `(1 + t ^ 2) ^ σ`

`Sec3_AdjointPolynomial` writes the Hilbert adjoint of a convolution on the weighted space of
§9.2 as a finite sum when the density is the polynomial `(1 + t ^ 2) ^ n` of the logarithm of
the modulation. On the base interval `{0}` the density is `(1 + t ^ 2) ^ (s / 2)` for every
Sobolev order `s`, a polynomial only when `s` is an even integer.

This file treats every real exponent `σ`. The translate of the density is the density times
`(1 + p r + q r ^ 2) ^ σ`, with `p` and `q` bounded by one, and for a small shift `r` this is a
binomial series in powers of `r` (`hasSum_binomWeightCoeff`). For a test supported where the
logarithm of the modulation is small, the adjoint of convolution by its reflected conjugate is
then the sum of a norm convergent series of the same terms as in the polynomial case
(`hasSum_hardySobolevTestAction_adjoint_binomWeight`).

`Ch10_TraceSpectral/Sec4b_BinomialRecursion` uses this for the geometric part of
Theorem 10.4.3.5 on the line at every order. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace Pointwise ComplexConjugate ContDiff

namespace RiemannMasullo.WeightedConvolution

section BinomialWeight

/-- The coefficient of the term `(k, l)`, with `l ≤ k`, of the binomial series of
`(1 + p r + q r ^ 2) ^ σ` in powers of `r`: the generalized binomial coefficient of `σ` and `k`
times the binomial coefficient of `k` and `l`. -/
def binomWeightCoeff (σ : ℝ) (i : Σ k : ℕ, Fin (k + 1)) : ℝ :=
  Ring.choose σ i.1 * (i.1.choose i.2 : ℝ)

/-- The binomial series of `(1 + u) ^ σ` for `|u| < 1`. -/
theorem hasSum_choose_mul_pow (σ u : ℝ) (hu : |u| < 1) :
    HasSum (fun k : ℕ ↦ Ring.choose σ k * u ^ k) ((1 + u) ^ σ) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := σ)).hasSum (y := u) (by
    rw [mem_eball_zero_iff, ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_lt_one]
    exact hu)
  rw [zero_add] at h
  refine h.congr_fun fun k ↦ ?_
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- The binomial series converges absolutely inside the unit disc. -/
theorem summable_abs_choose_mul_pow (σ ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Summable fun k : ℕ ↦ |Ring.choose σ k| * ρ ^ k := by
  have hr := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := σ)).r_le
  have h := (binomialSeries ℝ σ).summable_norm_apply (x := ρ) (by
    rw [mem_eball_zero_iff]
    refine lt_of_lt_of_le ?_ hr
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_lt_one, abs_of_nonneg hρ0]
    exact hρ)
  refine h.congr fun k ↦ ?_
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, norm_mul,
    Real.norm_eq_abs, abs_pow, abs_of_nonneg hρ0]

/-- The terms of one power `k` of `p r + q r ^ 2`, sorted by the power of `r`. -/
theorem sum_choose_mul_pow_mul_pow (k : ℕ) (P Q r : ℝ) :
    ∑ l : Fin (k + 1), (k.choose l : ℝ) * (P ^ (k - l) * Q ^ (l : ℕ)) * r ^ (k + l) =
      (P * r + Q * r ^ 2) ^ k := by
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ (k.choose l : ℝ) * (P ^ (k - l) * Q ^ l) * r ^ (k + l))
    (k + 1), add_comm (P * r), add_pow]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hr : (r ^ 2) ^ l * r ^ (k - l) = r ^ (k + l) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← hr]
  ring

/-- The series of the absolute values of the coefficients against powers of `x`. -/
theorem hasSum_abs_binomWeightCoeff_mul_pow (σ x : ℝ) (hx0 : 0 ≤ x) (hx : x + x ^ 2 < 1) :
    Summable (fun i : Σ k : ℕ, Fin (k + 1) ↦ |binomWeightCoeff σ i| * x ^ (i.1 + i.2)) ∧
      ∀ k : ℕ, ∑ l : Fin (k + 1), |binomWeightCoeff σ ⟨k, l⟩| * x ^ (k + l) =
        |Ring.choose σ k| * (x + x ^ 2) ^ k := by
  have hfib (k : ℕ) : ∑ l : Fin (k + 1), |binomWeightCoeff σ ⟨k, l⟩| * x ^ (k + l) =
      |Ring.choose σ k| * (x + x ^ 2) ^ k := by
    have h := sum_choose_mul_pow_mul_pow k 1 1 x
    simp only [one_pow, mul_one, one_mul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    change |Ring.choose σ k * (k.choose l : ℝ)| * x ^ (k + l) = _
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k.choose l : ℝ) from Nat.cast_nonneg _)]
    ring
  refine ⟨?_, hfib⟩
  rw [summable_sigma_of_nonneg fun i ↦ by positivity]
  refine ⟨fun k ↦ (hasSum_fintype _).summable, ?_⟩
  refine (summable_abs_choose_mul_pow σ (x + x ^ 2) (by positivity) hx).congr fun k ↦ ?_
  rw [tsum_fintype]
  exact (hfib k).symm

/-- The binomial series of `(1 + p r + q r ^ 2) ^ σ`, sorted by the power of `r`, for
coefficients `p`, `q` bounded by one and `|r| ≤ δ` with `δ + δ ^ 2 < 1`. -/
theorem hasSum_binomWeightCoeff (σ P Q r δ : ℝ) (hP : |P| ≤ 1) (hQ : |Q| ≤ 1) (hr : |r| ≤ δ)
    (hδ : δ + δ ^ 2 < 1) :
    HasSum (fun i : Σ k : ℕ, Fin (k + 1) ↦
        binomWeightCoeff σ i * (P ^ (i.1 - i.2) * Q ^ (i.2 : ℕ)) * r ^ (i.1 + i.2))
      ((1 + P * r + Q * r ^ 2) ^ σ) := by
  have hδ0 : 0 ≤ δ := (abs_nonneg r).trans hr
  have hu : |P * r + Q * r ^ 2| < 1 := by
    refine lt_of_le_of_lt ((abs_add_le _ _).trans ?_) hδ
    rw [abs_mul, abs_mul, abs_pow]
    have h1 : |P| * |r| ≤ δ := (mul_le_mul hP hr (abs_nonneg _) zero_le_one).trans (one_mul δ).le
    have h2 : |Q| * |r| ^ 2 ≤ δ ^ 2 :=
      (mul_le_mul hQ (pow_le_pow_left₀ (abs_nonneg _) hr 2) (by positivity) zero_le_one).trans
        (one_mul _).le
    exact add_le_add h1 h2
  have h0 := hasSum_choose_mul_pow σ (P * r + Q * r ^ 2) hu
  rw [← add_assoc] at h0
  refine HasSum.sigma_of_hasSum h0 (fun k ↦ ?_) ?_
  · have h := hasSum_fintype (fun l : Fin (k + 1) ↦
      binomWeightCoeff σ ⟨k, l⟩ * (P ^ (k - l) * Q ^ (l : ℕ)) * r ^ (k + l))
    have hval : ∑ l : Fin (k + 1),
        binomWeightCoeff σ ⟨k, l⟩ * (P ^ (k - l) * Q ^ (l : ℕ)) * r ^ (k + l) =
        Ring.choose σ k * (P * r + Q * r ^ 2) ^ k := by
      rw [← sum_choose_mul_pow_mul_pow k P Q r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      change Ring.choose σ k * (k.choose l : ℝ) * _ * _ = _
      ring
    exact hval ▸ h
  · refine Summable.of_norm_bounded (hasSum_abs_binomWeightCoeff_mul_pow σ δ hδ0 hδ).1 fun i ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
    have h1 : |P| ^ (i.1 - i.2) * |Q| ^ (i.2 : ℕ) ≤ 1 :=
      (mul_le_mul (pow_le_one₀ (abs_nonneg _) hP) (pow_le_one₀ (abs_nonneg _) hQ)
        (by positivity) zero_le_one).trans (one_mul 1).le
    calc |binomWeightCoeff σ i| * (|P| ^ (i.1 - i.2) * |Q| ^ (i.2 : ℕ)) * |r| ^ (i.1 + i.2)
        ≤ |binomWeightCoeff σ i| * 1 * δ ^ (i.1 + i.2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (pow_le_pow_left₀ (abs_nonneg _) hr _) (by positivity) (by positivity)
      _ = |binomWeightCoeff σ i| * δ ^ (i.1 + i.2) := by ring

/-- The terms other than `(0, 0)` of the series of absolute values of the coefficients against
powers of `x` sum to at most `x + x ^ 2` times a constant that depends only on `σ`, when
`x + x ^ 2 ≤ 1 / 2`. So the series without its first term is small when `x` is small. -/
theorem tsum_abs_binomWeightCoeff_tail_le (σ x : ℝ) (hx0 : 0 ≤ x) (hx : x + x ^ 2 ≤ 1 / 2) :
    Summable (fun i : Σ k : ℕ, Fin (k + 1) ↦
      |if i.1 = 0 then 0 else binomWeightCoeff σ i| * x ^ (i.1 + i.2)) ∧
    ∑' i : Σ k : ℕ, Fin (k + 1),
      |if i.1 = 0 then 0 else binomWeightCoeff σ i| * x ^ (i.1 + i.2) ≤
      (x + x ^ 2) * ∑' k : ℕ, |Ring.choose σ (k + 1)| * (1 / 2 : ℝ) ^ k := by
  have hx1 : x + x ^ 2 < 1 := by linarith
  have hu0 : 0 ≤ x + x ^ 2 := by positivity
  obtain ⟨hfull, hfib⟩ := hasSum_abs_binomWeightCoeff_mul_pow σ x hx0 hx1
  let f (i : Σ k : ℕ, Fin (k + 1)) : ℝ :=
    |if i.1 = 0 then 0 else binomWeightCoeff σ i| * x ^ (i.1 + i.2)
  have hf0 (i : Σ k : ℕ, Fin (k + 1)) : 0 ≤ f i := by positivity
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun i ↦ ?_) hfull
    change |if i.1 = 0 then 0 else binomWeightCoeff σ i| * x ^ (i.1 + i.2) ≤ _
    split_ifs
    · rw [abs_zero, zero_mul]
      positivity
    · exact le_rfl
  let g (k : ℕ) : ℝ := if k = 0 then 0 else |Ring.choose σ k| * (x + x ^ 2) ^ k
  have hfibf (k : ℕ) : ∑' l : Fin (k + 1), f ⟨k, l⟩ = g k := by
    rw [tsum_fintype]
    change ∑ l : Fin (k + 1),
      |if k = 0 then 0 else binomWeightCoeff σ ⟨k, l⟩| * x ^ (k + l) = g k
    by_cases hk : k = 0
    · simp [g, hk]
    · simp only [g, ite_eq_right hk]
      exact hfib k
  have hsig : ∑' i, f i = ∑' k, g k := by
    rw [hfs.tsum_sigma' fun k ↦ (hasSum_fintype _).summable]
    exact tsum_congr hfibf
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_)
      (summable_abs_choose_mul_pow σ (x + x ^ 2) hu0 hx1)
    · change 0 ≤ if k = 0 then 0 else |Ring.choose σ k| * (x + x ^ 2) ^ k
      split_ifs <;> positivity
    · change (if k = 0 then 0 else |Ring.choose σ k| * (x + x ^ 2) ^ k) ≤ _
      split_ifs
      · positivity
      · exact le_rfl
  have hhalf : Summable fun k : ℕ ↦ |Ring.choose σ (k + 1)| * (1 / 2 : ℝ) ^ k := by
    have h := (summable_nat_add_iff 1).mpr
      (summable_abs_choose_mul_pow σ (1 / 2) (by norm_num) (by norm_num))
    refine (h.mul_left 2).congr fun k ↦ ?_
    rw [pow_succ]
    ring
  refine ⟨hfs, ?_⟩
  change ∑' i, f i ≤ _
  rw [hsig, hgs.tsum_eq_zero_add, show g 0 = 0 from ite_eq_left rfl, zero_add, ← tsum_mul_left]
  refine ((summable_nat_add_iff 1).mpr hgs).tsum_le_tsum (fun k ↦ ?_) (hhalf.mul_left _)
  change (if k + 1 = 0 then 0 else |Ring.choose σ (k + 1)| * (x + x ^ 2) ^ (k + 1)) ≤ _
  rw [ite_eq_right (Nat.succ_ne_zero k), pow_succ]
  have hpow : (x + x ^ 2) ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hu0 hx k
  calc |Ring.choose σ (k + 1)| * ((x + x ^ 2) ^ k * (x + x ^ 2))
      ≤ |Ring.choose σ (k + 1)| * ((1 / 2 : ℝ) ^ k * (x + x ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hu0) (abs_nonneg _)
    _ = (x + x ^ 2) * (|Ring.choose σ (k + 1)| * (1 / 2 : ℝ) ^ k) := by ring

end BinomialWeight

section SeriesInLp

/-- A series that converges in `L²` and pointwise almost everywhere has the same sum in both
senses: the sum in `L²` is almost everywhere the pointwise sum. Convergence in `L²` gives
convergence in measure, so a sequence of partial sums converges almost everywhere. -/
theorem Lp_hasSum_coeFn_ae_eq {X ι : Type*} [MeasurableSpace X] {ν₀ : Measure X} [Countable ι]
    (a : ι → Lp ℂ 2 ν₀) (S : Lp ℂ 2 ν₀) (hS : HasSum a S) (H : X → ℂ)
    (hH : ∀ᵐ x ∂ν₀, HasSum (fun i ↦ (a i : X → ℂ) x) (H x)) : (S : X → ℂ) =ᵐ[ν₀] H := by
  classical
  have h1 : Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, a i) atTop (𝓝 S) := hS
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp h1
  have h3 : TendstoInMeasure ν₀ (fun s : Finset ι ↦ ((∑ i ∈ s, a i : Lp ℂ 2 ν₀) : X → ℂ)) atTop
      (S : X → ℂ) := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) h2
  obtain ⟨ns, hns, hae⟩ := h3.exists_seq_tendsto_ae'
  have hcoe : ∀ᵐ x ∂ν₀, ∀ k : ℕ,
      ((∑ i ∈ ns k, a i : Lp ℂ 2 ν₀) : X → ℂ) x = ∑ i ∈ ns k, (a i : X → ℂ) x :=
    ae_all_iff.mpr fun k ↦ by
      induction ns k using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact Lp.coeFn_zero ℂ 2 ν₀
      | insert b s hb ih =>
        rw [Finset.sum_insert hb]
        filter_upwards [Lp.coeFn_add (a b) (∑ i ∈ s, a i), ih] with x h1 h2
        rw [h1, Pi.add_apply, h2, Finset.sum_insert hb]
  filter_upwards [hae, hH, hcoe] with x hx1 hx2 hx3
  have hx4 : Tendsto (fun k ↦ ∑ i ∈ ns k, (a i : X → ℂ) x) atTop (𝓝 (H x)) := hx2.comp hns
  exact tendsto_nhds_unique hx1 (hx4.congr fun k ↦ (hx3 k).symm)

/-- A convergent series of bounded operators converges at each vector. -/
private theorem hasSum_clm_apply₂ {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : ι → E →L[ℂ] E) (S : E →L[ℂ] E) (hS : HasSum B S) (u : E) :
    HasSum (fun n ↦ (B n) u) (S u) :=
  (ContinuousLinearMap.apply ℂ E u).hasSum hS

end SeriesInLp

section AdjointSeries

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "L" => (fun x ↦ Real.log ((m x).val : ℝ))
local notation "ν" => (fun a b s ↦ intervalSobolevMeasure μ L a b s)

set_option maxHeartbeats 800000 in
/-- For the density `(1 + t ^ 2) ^ σ`, with any real exponent `σ`, the Hilbert adjoint of
convolution by the reflected conjugate of a test `φ` supported where the logarithm of the
modulation is at most `δ`, with `δ + δ ^ 2 < 1`, is the sum of a norm convergent series:
convolutions by `φ` times powers of minus the logarithm of the modulation, each followed by
multiplication by a bounded function of that logarithm, with the coefficients of the binomial
series of `(1 + p r + q r ^ 2) ^ σ`. The term of the pair `(0, 0)` is convolution by `φ`.
For a natural number `σ` the series is the finite sum of
`hardySobolevTestAction_adjoint_eq_sum_polyWeight`. The identity is checked on continuous
compactly supported inputs, where both sides have kernels
(`hardySobolevTestAction_compact_kernels`): the series converges in the weighted `L²` space and
pointwise, by the binomial series of the translated density inside the kernel of the adjoint,
and the two sums agree almost everywhere (`Lp_hasSum_coeFn_ae_eq`). -/
theorem hasSum_hardySobolevTestAction_adjoint_binomWeight (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (σ : ℝ) (hw : ∀ t, intervalSobolevDensity a b s t = (1 + t ^ 2) ^ σ)
    (φ φ' : BruhatCompactSupport G) (hφ' : ∀ g, φ'.val g = star (φ.val g⁻¹))
    (Φ : ℕ → BruhatCompactSupport G)
    (hΦ : ∀ e g, (Φ e).val g = (((-Real.log ((m g).val : ℝ)) ^ e : ℝ) : ℂ) * φ.val g)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ + δ ^ 2 < 1)
    (hsupp : ∀ g, φ.val g ≠ 0 → |Real.log ((m g).val : ℝ)| ≤ δ)
    (T : (Σ _ : ℕ, ℕ) →
      (CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s))
    (hTn : ∀ i, ‖T i‖ ≤ 1)
    (hT : ∀ i u, (T i u : G → ℂ) =ᵐ[ν a b s] fun x ↦ ((polyWeightMask i (L x) : ℝ) : ℂ) * u x) :
    HasSum (fun i : Σ k : ℕ, Fin (k + 1) ↦ ((binomWeightCoeff σ i : ℝ) : ℂ) •
        (T ⟨i.1, i.2⟩).comp (hardySobolevTestAction μ m a b s hab hs (Φ (i.1 + i.2)) :
          CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s))
      (ContinuousLinearMap.adjoint (hardySobolevTestAction μ m a b s hab hs φ' :
        CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s)) := by
  let A' : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs φ'
  let B (e : ℕ) : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs (Φ e)
  let w (x : G) : ℝ := intervalSobolevDensity a b s (L x)
  have hL : Continuous L := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    m.continuous)).log fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hD : Continuous (intervalSobolevDensity a b s) := by
    rw [show intervalSobolevDensity a b s = fun t ↦ (1 + t ^ 2) ^ σ from funext hw]
    exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun t ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + t ^ 2).ne'
  have hwc : Continuous w := hD.comp hL
  have hwx (x : G) : w x = (1 + L x ^ 2) ^ σ := hw (L x)
  have hwpos (x : G) : 0 < w x := by
    rw [hwx]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hν : ν a b s = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := rfl
  let : IsLocallyFiniteMeasure (ν a b s) := hν ▸ IsLocallyFiniteMeasure.withDensity_ofReal hwc
  have hLmul (g h : G) : L (g * h) = L g + L h := by
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m g).ne_zero) (NNReal.coe_ne_zero.2 (m h).ne_zero)]
  have hLinv (g : G) : L g⁻¹ = -L g := by
    dsimp only
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  let c (i : Σ k : ℕ, Fin (k + 1)) : ℝ := binomWeightCoeff σ i
  let F (i : Σ k : ℕ, Fin (k + 1)) :
      CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    ((c i : ℝ) : ℂ) • (T ⟨i.1, i.2⟩).comp (B (i.1 + i.2))
  obtain ⟨M₀, hM₀⟩ :=
    exists_hardySobolevTestAction_logPow_norm_le μ m a b s hab hs φ Φ hΦ δ hδ0 hsupp
  have hM₀0 : 0 ≤ M₀ := by
    have h := (norm_nonneg _).trans (hM₀ 0)
    simpa using h
  have hsumc := (hasSum_abs_binomWeightCoeff_mul_pow σ δ hδ0 hδ).1
  have hΦn (e : ℕ) (z : G) : ‖(Φ e).val z‖ ≤ δ ^ e * ‖φ.val z‖ := by
    rw [hΦ e z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg]
    by_cases hz : φ.val z = 0
    · rw [hz, norm_zero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hsupp z hz) e)
        (norm_nonneg _)
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (hsumc.mul_left M₀) fun i ↦ ?_
    change ‖((c i : ℝ) : ℂ) • (T ⟨i.1, i.2⟩).comp (B (i.1 + i.2))‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖(T ⟨i.1, i.2⟩).comp (B (i.1 + i.2))‖ ≤ M₀ * δ ^ (i.1 + i.2) :=
      ((T ⟨i.1, i.2⟩).opNorm_comp_le _).trans
        ((mul_le_mul (hTn _) (hM₀ (i.1 + i.2)) (norm_nonneg _) zero_le_one).trans (one_mul _).le)
    calc |c i| * ‖(T ⟨i.1, i.2⟩).comp (B (i.1 + i.2))‖ ≤ |c i| * (M₀ * δ ^ (i.1 + i.2)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = M₀ * (|c i| * δ ^ (i.1 + i.2)) := by ring
  have hlimit : ∑' i, F i = A'.adjoint := by
    symm
    apply DFunLike.coe_injective
    apply Continuous.ext_on (dense_compactCore' (ν a b s)) A'.adjoint.continuous
      (ContinuousLinearMap.continuous _)
    rintro u ⟨f, hf, hfc, hu⟩
    apply Lp.ext
    have h1 := (hardySobolevTestAction_compact_kernels μ m a b s hab hs φ' u f hf hfc hu).2
    have h2 (e : ℕ) :=
      (hardySobolevTestAction_compact_kernels μ m a b s hab hs (Φ e) u f hf hfc hu).1
    have hFi (i : Σ k : ℕ, Fin (k + 1)) :
        ((F i u : CompactIntervalSobolev μ L a b s) : G → ℂ) =ᵐ[ν a b s]
        fun x ↦ ((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
          ∫ y, (Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y ∂(ν a b s)) := by
      change ((((c i : ℝ) : ℂ) • (T ⟨i.1, i.2⟩ (B (i.1 + i.2) u)) :
        CompactIntervalSobolev μ L a b s) : G → ℂ) =ᵐ[ν a b s] _
      filter_upwards [Lp.coeFn_smul ((c i : ℝ) : ℂ) (T ⟨i.1, i.2⟩ (B (i.1 + i.2) u)),
        hT ⟨i.1, i.2⟩ (B (i.1 + i.2) u), h2 (i.1 + i.2)] with x hx1 hx2 hx3
      rw [hx1, Pi.smul_apply, smul_eq_mul, hx2, hx3]
    -- For every `x` the kernel integrals sum to the kernel integral of the adjoint.
    have hpoint (x : G) : HasSum (fun i : Σ k : ℕ, Fin (k + 1) ↦
        ((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
          ∫ y, (Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y ∂(ν a b s)))
        (∫ y, star (φ'.val (y * x⁻¹)) / (w x : ℂ) * f y ∂(ν a b s)) := by
      have hφc : Continuous φ.val :=
        continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
      have hint (e : ℕ) :
          Integrable (fun y ↦ (Φ e).val (x * y⁻¹) / (w y : ℂ) * f y) (ν a b s) := by
        have hΦc : Continuous (Φ e).val :=
          continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp (Φ e).property.1)
        have hcont : Continuous (fun y ↦ (Φ e).val (x * y⁻¹) / (w y : ℂ) * f y) :=
          ((hΦc.comp (continuous_const.mul continuous_inv)).div
            (Complex.continuous_ofReal.comp hwc)
            fun y ↦ Complex.ofReal_ne_zero.mpr (hwpos y).ne').mul hf
        exact hcont.integrable_of_hasCompactSupport hfc.mul_left
      have hint0 : Integrable (fun y ↦ ‖φ.val (x * y⁻¹) / (w y : ℂ) * f y‖) (ν a b s) := by
        have hcont : Continuous (fun y ↦ φ.val (x * y⁻¹) / (w y : ℂ) * f y) :=
          ((hφc.comp (continuous_const.mul continuous_inv)).div
            (Complex.continuous_ofReal.comp hwc)
            fun y ↦ Complex.ofReal_ne_zero.mpr (hwpos y).ne').mul hf
        exact (hcont.integrable_of_hasCompactSupport hfc.mul_left).norm
      let Hn (i : Σ k : ℕ, Fin (k + 1)) (y : G) : ℂ := ((c i : ℝ) : ℂ) *
        (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
          ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y))
      have hHint (i : Σ k : ℕ, Fin (k + 1)) : Integrable (Hn i) (ν a b s) :=
        ((hint (i.1 + i.2)).const_mul _).const_mul _
      have hHn (i : Σ k : ℕ, Fin (k + 1)) (y : G) : ‖Hn i y‖ ≤
          |c i| * δ ^ (i.1 + i.2) * ‖φ.val (x * y⁻¹) / (w y : ℂ) * f y‖ := by
        change ‖((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
          ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y))‖ ≤ _
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, norm_mul, norm_div, norm_mul, norm_div]
        have hm := abs_polyWeightMask_le_one ⟨i.1, i.2⟩ (L x)
        have hΦ' := hΦn (i.1 + i.2) (x * y⁻¹)
        have hw0 : 0 ≤ ‖(w y : ℂ)‖ := norm_nonneg _
        calc |c i| * (|polyWeightMask ⟨i.1, i.2⟩ (L x)| *
              (‖(Φ (i.1 + i.2)).val (x * y⁻¹)‖ / ‖(w y : ℂ)‖ * ‖f y‖))
            ≤ |c i| * (1 * (δ ^ (i.1 + i.2) * ‖φ.val (x * y⁻¹)‖ / ‖(w y : ℂ)‖ * ‖f y‖)) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul hm ?_ (by positivity) zero_le_one)
                (abs_nonneg _)
              exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hΦ' hw0)
                (norm_nonneg _)
          _ = |c i| * δ ^ (i.1 + i.2) * (‖φ.val (x * y⁻¹)‖ / ‖(w y : ℂ)‖ * ‖f y‖) := by ring
      have hHsum : Summable fun i ↦ ∫ y, ‖Hn i y‖ ∂(ν a b s) := by
        refine Summable.of_nonneg_of_le (fun i ↦ integral_nonneg fun _ ↦ norm_nonneg _)
          (fun i ↦ ?_) (hsumc.mul_right (∫ y, ‖φ.val (x * y⁻¹) / (w y : ℂ) * f y‖ ∂(ν a b s)))
        rw [← integral_const_mul]
        exact integral_mono (hHint i).norm (hint0.const_mul _) (hHn i)
      have h3 := hasSum_integral_of_summable_integral_norm hHint hHsum
      have h4 : (fun i ↦ ∫ y, Hn i y ∂(ν a b s)) = fun i : Σ k : ℕ, Fin (k + 1) ↦
          ((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
            ∫ y, (Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y ∂(ν a b s)) := by
        funext i
        change ∫ y, ((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
          ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y)) ∂(ν a b s) = _
        rw [integral_const_mul, integral_const_mul]
      have h5 : ∫ y, ∑' i, Hn i y ∂(ν a b s) =
          ∫ y, star (φ'.val (y * x⁻¹)) / (w x : ℂ) * f y ∂(ν a b s) := by
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        have hstar : star (φ'.val (y * x⁻¹)) = φ.val (x * y⁻¹) := by
          rw [hφ', star_star, mul_inv_rev, inv_inv]
        have hwxne : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos x).ne'
        have hwyne : (w y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos y).ne'
        have hsumy : HasSum (fun i ↦ Hn i y) (star (φ'.val (y * x⁻¹)) / (w x : ℂ) * f y) := by
          rw [hstar]
          by_cases hz : φ.val (x * y⁻¹) = 0
          · rw [hz, zero_div, zero_mul]
            refine hasSum_zero.congr_fun fun i ↦ ?_
            change ((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
              ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y)) = 0
            rw [hΦ, hz]
            simp
          · have hLy : L x + -L (x * y⁻¹) = L y := by
              rw [hLmul, hLinv]
              ring
            have hpos : (0 : ℝ) < 1 + L x ^ 2 := by positivity
            have hP : |2 * L x / (1 + L x ^ 2)| ≤ 1 := by
              rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_mul, abs_two]
              nlinarith [sq_abs (L x), sq_nonneg (|L x| - 1)]
            have hQ : |1 / (1 + L x ^ 2)| ≤ 1 := by
              rw [abs_div, abs_one, abs_of_pos hpos, div_le_one hpos]
              nlinarith [sq_nonneg (L x)]
            have hr : |(-L (x * y⁻¹))| ≤ δ := by
              rw [abs_neg]
              exact hsupp _ hz
            have hser := hasSum_binomWeightCoeff σ (2 * L x / (1 + L x ^ 2))
              (1 / (1 + L x ^ 2)) (-L (x * y⁻¹)) δ hP hQ hr hδ
            have hbase : 1 + 2 * L x / (1 + L x ^ 2) * -L (x * y⁻¹) +
                1 / (1 + L x ^ 2) * (-L (x * y⁻¹)) ^ 2 = (1 + L y ^ 2) / (1 + L x ^ 2) := by
              rw [← hLy]
              field_simp
              ring
            have hratio : (1 + 2 * L x / (1 + L x ^ 2) * -L (x * y⁻¹) +
                1 / (1 + L x ^ 2) * (-L (x * y⁻¹)) ^ 2) ^ σ = w y / w x := by
              rw [hbase, hwx y, hwx x, Real.div_rpow (by positivity) (by positivity)]
            rw [hratio] at hser
            have hserC := (Complex.ofRealCLM.hasSum hser).mul_left
              (φ.val (x * y⁻¹) / (w y : ℂ) * f y)
            have hval : φ.val (x * y⁻¹) / (w y : ℂ) * f y * ((w y / w x : ℝ) : ℂ) =
                φ.val (x * y⁻¹) / (w x : ℂ) * f y := by
              rw [Complex.ofReal_div]
              field_simp
            have hserC' : HasSum (fun i : Σ k : ℕ, Fin (k + 1) ↦
                φ.val (x * y⁻¹) / (w y : ℂ) * f y *
                  ((binomWeightCoeff σ i * ((2 * L x / (1 + L x ^ 2)) ^ (i.1 - i.2) *
                    (1 / (1 + L x ^ 2)) ^ (i.2 : ℕ)) * (-L (x * y⁻¹)) ^ (i.1 + i.2) : ℝ) : ℂ))
                (φ.val (x * y⁻¹) / (w x : ℂ) * f y) := hval ▸ hserC
            refine hserC'.congr_fun fun i ↦ ?_
            change ((c i : ℝ) : ℂ) * (((polyWeightMask ⟨i.1, i.2⟩ (L x) : ℝ) : ℂ) *
              ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y)) = _
            rw [hΦ]
            change _ = φ.val (x * y⁻¹) / (w y : ℂ) * f y *
              ((c i * polyWeightMask ⟨i.1, i.2⟩ (L x) * (-L (x * y⁻¹)) ^ (i.1 + i.2) : ℝ) : ℂ)
            push_cast
            ring
        exact hsumy.tsum_eq
      rw [h4, h5] at h3
      exact h3
    have hae : ∀ᵐ x ∂(ν a b s), HasSum (fun i ↦
        ((F i u : CompactIntervalSobolev μ L a b s) : G → ℂ) x)
        (∫ y, star (φ'.val (y * x⁻¹)) / (w x : ℂ) * f y ∂(ν a b s)) := by
      filter_upwards [ae_all_iff.mpr hFi] with x hx
      exact (hpoint x).congr_fun fun i ↦ hx i
    have hSu := hasSum_clm_apply₂ F _ hFs.hasSum u
    have hfin := Lp_hasSum_coeFn_ae_eq (fun i ↦ F i u) _ hSu _ hae
    exact h1.trans hfin.symm
  exact hlimit ▸ hFs.hasSum

end AdjointSeries

end RiemannMasullo.WeightedConvolution
