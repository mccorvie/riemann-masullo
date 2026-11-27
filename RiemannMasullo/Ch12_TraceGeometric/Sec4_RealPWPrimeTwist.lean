module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWBlockTraceNorm
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The cutoff twisted at a prime as a product of operators

Paper: Theorem 12.4.1.1, pp. 514–517, the terms of the finite places, for `F = ℚ` and
`S = {∞, p}`, in the unweighted model of #7354, as in `Sec4_RealPWPrimeTrace`.

`Sec4_RealPWBlockTraceNorm` adds up the blocks `Q M_X A_{ψ_c} Q` to one nuclear operator on
the band. This file shows that this operator is the compression to the band of
`U⁻¹ M_L U A_ψ`, where `T f (x) = √p f (p x)`, `U = (1 - r T⁻¹) (1 - r T)⁻¹`, `M_L` is the
cutoff to `[-L, L]` and `A_ψ` is the action of the test function.

* `twistOperator` and `IsContractiveIntRep.hasSum_twistOperator`. In a Banach algebra, for the
  powers `S n` of an invertible isometry, the twist is `∑ i, d i S (i - 1)` with the
  coefficients `primeTwistCoeff`. The twist of the inverse powers is its inverse
  (`twistOperator_mul_neg`, `twistOperator_neg_mul`).
* `IsContractiveIntRep.hasSum_twist_conj`. If `S k M e = M (e - k) S k`, then `U⁻¹ M 0 U` is
  the double series of `d i d j M (i - 1) S (j - i)`, convergent in norm.
* `lpCutoff` and `lpDilation`. The cutoff and the half-density dilation on `L²` of the line,
  with the commutation `lpDilation_mul_lpCutoff`.
* `memLp_testActionFun`. The action of a test function maps a bounded continuous
  square-integrable function to a square-integrable function.
* `lpDilation_bandTestAction`. `T ^ k A_ψ = A_{ψ_c}` on band vectors, for `c = p ^ k`.
* `IsPrimeTwistedCutoff.apply_eq`. The sum of the blocks sends `f` to the projection onto the
  band of `U⁻¹ M_L U A_ψ f`.
* `exists_primeTwistedCutoff_compression_trace_limit`. The trace of the compression of
  `U⁻¹ M_L U A_ψ`, less its logarithmic term, converges to the real-place limit plus the term
  of the prime.

Reconstruction: The paper does not state this.

Deviation: That `Q U⁻¹ M_L U A_ψ Q` is the cutoff operator of Connes on the functions on `X_S`
invariant under the units of `ℚ_p` is on paper and is not formalized. No `p`-adic object
appears here. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

section TwistSeries

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- A family `S n`, `n ∈ ℤ`, of elements of norm at most one of a Banach algebra with
`S 0 = 1` and `S (m + n) = S m * S n`: the powers of an invertible isometry. -/
structure IsContractiveIntRep (S : ℤ → R) : Prop where
  zero : S 0 = 1
  add : ∀ m n, S (m + n) = S m * S n
  norm_le : ∀ n, ‖S n‖ ≤ 1

/-- The twist `U = (1 - r T⁻¹) (1 - r T)⁻¹` for `T = S 1`, with the inverse of `1 - r T` given
by its Neumann series. -/
def twistOperator (S : ℤ → R) (r : ℝ) : R :=
  (1 - (r : ℂ) • S (-1)) * ∑' n : ℕ, ((r : ℂ) • S 1) ^ n

/-- The reversed family `n ↦ S (-n)`: the powers of `T⁻¹`. -/
theorem IsContractiveIntRep.neg {S : ℤ → R} (hS : IsContractiveIntRep S) :
    IsContractiveIntRep fun n ↦ S (-n) where
  zero := by rw [neg_zero, hS.zero]
  add m n := by rw [neg_add, hS.add]
  norm_le n := hS.norm_le _

theorem IsContractiveIntRep.smul_pow {S : ℤ → R} (hS : IsContractiveIntRep S) (r : ℝ) (n : ℕ) :
    ((r : ℂ) • S 1) ^ n = ((r ^ n : ℝ) : ℂ) • S n := by
  induction n with
  | zero => simp [hS.zero]
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_smul_comm, ← hS.add, pow_succ]
    push_cast
    rfl

theorem IsContractiveIntRep.norm_smul_lt {S : ℤ → R} (hS : IsContractiveIntRep S) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℤ) : ‖(r : ℂ) • S k‖ < 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0]
  exact (mul_le_of_le_one_right hr0 (hS.norm_le k)).trans_lt hr1

/-- The twist and the twist of the reversed family are inverse to each other. -/
theorem IsContractiveIntRep.twistOperator_mul_neg {S : ℤ → R} (hS : IsContractiveIntRep S)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    twistOperator S r * twistOperator (fun n ↦ S (-n)) r = 1 := by
  have hx := hS.norm_smul_lt hr0 hr1 1
  have hy := hS.norm_smul_lt hr0 hr1 (-1)
  change (1 - (r : ℂ) • S (-1)) * (∑' n : ℕ, ((r : ℂ) • S 1) ^ n) *
    ((1 - (r : ℂ) • S (-(-1))) * ∑' n : ℕ, ((r : ℂ) • S (-1)) ^ n) = 1
  rw [neg_neg, mul_assoc, ← mul_assoc (∑' n : ℕ, ((r : ℂ) • S 1) ^ n), geom_series_mul_neg _ hx,
    one_mul, mul_neg_geom_series _ hy]

/-- The twist of the reversed family is also a left inverse of the twist. -/
theorem IsContractiveIntRep.twistOperator_neg_mul {S : ℤ → R} (hS : IsContractiveIntRep S)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    twistOperator (fun n ↦ S (-n)) r * twistOperator S r = 1 := by
  have h := hS.neg.twistOperator_mul_neg hr0 hr1
  simpa only [neg_neg] using h

/-- The coefficients of the twist are those of `primeTwistCoeff`: `U = ∑ i, d i T ^ (i - 1)`,
with convergence in norm. -/
theorem IsContractiveIntRep.hasSum_twistOperator {S : ℤ → R} (hS : IsContractiveIntRep S)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun i : ℕ ↦ ((primeTwistCoeff r i : ℝ) : ℂ) • S ((i : ℤ) - 1))
      (twistOperator S r) := by
  have hx := hS.norm_smul_lt hr0 hr1 1
  set G : R := ∑' n : ℕ, ((r : ℂ) • S 1) ^ n with hGdef
  have hG : HasSum (fun n : ℕ ↦ ((r : ℂ) • S 1) ^ n) G :=
    (summable_geometric_of_norm_lt_one hx).hasSum
  have h1 : (1 - (r : ℂ) • S 1) * G = 1 := mul_neg_geom_series _ hx
  have hGeq : G = 1 + (r : ℂ) • (S 1 * G) := by
    rw [sub_mul, one_mul, smul_mul_assoc] at h1
    exact sub_eq_iff_eq_add.mp h1
  have hSS : S (-1) * S 1 = 1 := by rw [← hS.add, neg_add_cancel, hS.zero]
  have hSG : S (-1) * G = S (-1) + (r : ℂ) • G := by
    conv_lhs => rw [hGeq]
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, hSS, one_mul]
  have htail : HasSum (fun n : ℕ ↦ ((primeTwistCoeff r (n + 1) : ℝ) : ℂ) •
      S (((n + 1 : ℕ) : ℤ) - 1)) (G - ((r ^ 2 : ℝ) : ℂ) • G) := by
    refine (hG.sub (hG.const_smul ((r ^ 2 : ℝ) : ℂ))).congr_fun fun n ↦ ?_
    rw [hS.smul_pow r n, primeTwistCoeff_succ, show (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) by
      push_cast; ring, smul_smul, ← sub_smul]
    push_cast
    congr 1
    ring
  have h := (hasSum_nat_add_iff (f := fun i : ℕ ↦ ((primeTwistCoeff r i : ℝ) : ℂ) •
    S ((i : ℤ) - 1)) 1).mp htail
  convert h using 1
  rw [twistOperator, ← hGdef, sub_mul, one_mul, smul_mul_assoc, hSG, Finset.sum_range_one,
    primeTwistCoeff_zero]
  push_cast
  simp only [smul_add, smul_smul]
  module

/-- The coefficients of the twist are absolutely summable. -/
theorem IsContractiveIntRep.summable_norm_twistCoeff {S : ℤ → R} (hS : IsContractiveIntRep S)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ → ℤ) :
    Summable fun i : ℕ ↦ ‖((primeTwistCoeff r i : ℝ) : ℂ) • S (k i)‖ := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    ((summable_geometric_of_lt_one hr0.le hr1).mul_left r⁻¹)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hS.norm_le _)).trans
    (abs_primeTwistCoeff_le hr0 hr1 i)

/-- Reconstruction: the expansion of a twisted element. For a family `M e`, `e ∈ ℤ`, with
`S k * M e = M (e - k) * S k`, the conjugate `U⁻¹ M 0 U` of `M 0` by the twist is the double
series of `d i d j M (i - 1) S (j - i)`, convergent in norm. For the dilation `T` by a prime and
the cutoffs `M e` to `[-L p ^ e, L p ^ e]` this is the expansion of `U⁻¹ M_L U`. -/
theorem IsContractiveIntRep.hasSum_twist_conj {S : ℤ → R} (hS : IsContractiveIntRep S)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (M : ℤ → R)
    (hM : ∀ k e, S k * M e = M (e - k) * S k) :
    HasSum (fun z : ℕ × ℕ ↦ ((primeTwistCoeff r z.1 * primeTwistCoeff r z.2 : ℝ) : ℂ) •
        (M ((z.1 : ℤ) - 1) * S ((z.2 : ℤ) - z.1)))
      (twistOperator (fun n ↦ S (-n)) r * M 0 * twistOperator S r) ∧
    Summable fun z : ℕ × ℕ ↦ ‖((primeTwistCoeff r z.1 * primeTwistCoeff r z.2 : ℝ) : ℂ) •
        (M ((z.1 : ℤ) - 1) * S ((z.2 : ℤ) - z.1))‖ := by
  let f : ℕ → R := fun i ↦ ((primeTwistCoeff r i : ℝ) : ℂ) • S (-((i : ℤ) - 1))
  let g : ℕ → R := fun j ↦ M 0 * (((primeTwistCoeff r j : ℝ) : ℂ) • S ((j : ℤ) - 1))
  have hf : Summable fun i ↦ ‖f i‖ := hS.summable_norm_twistCoeff hr0 hr1 _
  have hg : Summable fun j ↦ ‖g j‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ norm_mul_le _ _)
      ((hS.summable_norm_twistCoeff hr0 hr1 _).mul_left ‖M 0‖)
  have hfs : HasSum f (twistOperator (fun n ↦ S (-n)) r) :=
    hS.neg.hasSum_twistOperator hr0.le hr1
  have hgs : HasSum g (M 0 * twistOperator S r) :=
    (hS.hasSum_twistOperator hr0.le hr1).mul_left (M 0)
  have hterm : ∀ z : ℕ × ℕ, f z.1 * g z.2 =
      ((primeTwistCoeff r z.1 * primeTwistCoeff r z.2 : ℝ) : ℂ) •
        (M ((z.1 : ℤ) - 1) * S ((z.2 : ℤ) - z.1)) := by
    intro z
    change (((primeTwistCoeff r z.1 : ℝ) : ℂ) • S (-((z.1 : ℤ) - 1))) *
      (M 0 * (((primeTwistCoeff r z.2 : ℝ) : ℂ) • S ((z.2 : ℤ) - 1))) = _
    rw [mul_smul_comm, smul_mul_smul_comm, ← mul_assoc, hM, mul_assoc, ← hS.add,
      Complex.ofReal_mul]
    congr 3 <;> ring
  have hprod := summable_mul_of_summable_norm hf hg
  have hval := tsum_mul_tsum_of_summable_norm hf hg
  rw [hfs.tsum_eq, hgs.tsum_eq, ← mul_assoc] at hval
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact hprod.hasSum.congr_fun fun z ↦ (hterm z).symm
  · exact (hf.mul_norm hg).congr fun z ↦ by rw [hterm z]

end TwistSeries

section Reindex

/-- The pairs `(i, j)` of natural numbers, split into those with `i ≤ j`, indexed by
`(j - i, i)`, and those with `i > j`, indexed by `(i - j - 1, j)`. -/
def pairSplitEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun := Sum.elim (fun x ↦ (x.2, x.2 + x.1)) (fun x ↦ (x.2 + x.1 + 1, x.2))
  invFun y := if y.1 ≤ y.2 then Sum.inl (y.2 - y.1, y.1) else Sum.inr (y.1 - y.2 - 1, y.2)
  left_inv x := by
    rcases x with ⟨k, m⟩ | ⟨k, m⟩
    · simp
    · have h : ¬ (m + k + 1 ≤ m) := by omega
      simp only [Sum.elim_inr, h, ↓reduceIte]
      congr 2
      omega
  right_inv y := by
    obtain ⟨i, j⟩ := y
    by_cases h : i ≤ j
    · simp only [h, ↓reduceIte, Sum.elim_inl]
      congr 1
      omega
    · simp only [h, ↓reduceIte, Sum.elim_inr]
      congr 1
      omega

/-- A summable double series is the sum of its part over `i ≤ j` and its part over `i > j`. -/
theorem hasSum_eq_upper_add_lower {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    {F : ℕ × ℕ → G} {a : G} (h : HasSum F a) :
    a = (∑' x : ℕ × ℕ, F (x.2, x.2 + x.1)) + ∑' x : ℕ × ℕ, F (x.2 + x.1 + 1, x.2) := by
  have h' : HasSum (F ∘ pairSplitEquiv) a := (pairSplitEquiv.hasSum_iff).mpr h
  have hl : Summable ((F ∘ pairSplitEquiv) ∘ Sum.inl) :=
    h'.summable.comp_injective Sum.inl_injective
  have hr : Summable ((F ∘ pairSplitEquiv) ∘ Sum.inr) :=
    h'.summable.comp_injective Sum.inr_injective
  exact h'.unique (HasSum.sum hl.hasSum hr.hasSum)

end Reindex

section Operators

theorem memLp_mask_mul {μ : Measure ℝ} (X : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun x ↦ sharpIntervalMask X x * f x) 2 μ := by
  have e : (fun x ↦ sharpIntervalMask X x * f x) = (Icc (-X) X).indicator f := by
    funext x
    by_cases hx : x ∈ Icc (-X) X <;> simp [sharpIntervalMask, hx]
  rw [e]
  exact hf.indicator measurableSet_Icc.nullMeasurableSet

/-- The cutoff to `[-X, X]` as a linear map of `L²`. -/
def lpCutoffLinear (μ : Measure ℝ) (X : ℝ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_mask_mul X (Lp.memLp f)).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_mask_mul X (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_mask_mul X (Lp.memLp f)).toLp _)
        ((memLp_mask_mul X (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_mask_mul X (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_mask_mul X (Lp.memLp g)), Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_mask_mul X (Lp.memLp (c • f))),
      Lp.coeFn_smul c ((memLp_mask_mul X (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_mask_mul X (Lp.memLp f)), Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

theorem norm_lpCutoffLinear_le (μ : Measure ℝ) (X : ℝ) (f : Lp ℂ 2 μ) :
    ‖lpCutoffLinear μ X f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  change ‖(memLp_mask_mul X (Lp.memLp f)).toLp _‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_ae (memLp_mask_mul X (Lp.memLp f)).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_))
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (sharpIntervalMask_norm_le_one X x)

/-- The cutoff to `[-X, X]` on `L²` of the line: multiplication by the sharp mask. -/
def lpCutoff (μ : Measure ℝ) (X : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lpCutoffLinear μ X).mkContinuous 1 (norm_lpCutoffLinear_le μ X)

theorem lpCutoff_apply (μ : Measure ℝ) (X : ℝ) (f : Lp ℂ 2 μ) :
    lpCutoff μ X f = (memLp_mask_mul X (Lp.memLp f)).toLp _ := rfl

theorem lpCutoff_apply_ae (μ : Measure ℝ) (X : ℝ) (f : Lp ℂ 2 μ) :
    lpCutoff μ X f =ᵐ[μ] fun x ↦ sharpIntervalMask X x * f x := by
  rw [lpCutoff_apply]
  exact MemLp.coeFn_toLp (memLp_mask_mul X (Lp.memLp f))

/-- The half-density dilation of a function: `x ↦ √c f (c x)`. -/
def dilateFun (c : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ((√c : ℝ) : ℂ) * f (c * x)

theorem quasiMeasurePreserving_mul_left {c : ℝ} (hc : c ≠ 0) :
    QuasiMeasurePreserving (fun x : ℝ ↦ c * x) volume volume :=
  ⟨(measurable_const_mul c).aemeasurable, by
    rw [Real.map_volume_mul_left hc]
    exact Measure.smul_absolutelyContinuous⟩

theorem dilateFun_congr_ae {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    {f g : ℝ → ℂ} (h : f =ᵐ[μ] g) : dilateFun c f =ᵐ[μ] dilateFun c g := by
  subst hμ
  have h' : ∀ᵐ x : ℝ, f (c * x) = g (c * x) := (quasiMeasurePreserving_mul_left hc.ne').ae h
  filter_upwards [h'] with x hx
  rw [dilateFun, dilateFun, hx]

theorem memLp_dilateFun {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c) {f : ℝ → ℂ}
    (hf : MemLp f 2 μ) : MemLp (dilateFun c f) 2 μ := by
  subst hμ
  have hm : AEStronglyMeasurable (fun x ↦ f (c * x)) volume :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_mul_left hc.ne')
  have hi : Integrable (fun x ↦ ‖f (c * x)‖ ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).comp_mul_left' hc.ne'
  refine (memLp_two_iff_integrable_sq_norm (hm.const_mul _)).2
    ((hi.const_mul c).congr (ae_of_all _ fun x ↦ ?_))
  change c * ‖f (c * x)‖ ^ 2 = ‖((√c : ℝ) : ℂ) * f (c * x)‖ ^ 2
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c), mul_pow,
    Real.sq_sqrt hc.le]

theorem integral_sq_norm_dilateFun {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℂ) : ∫ x, ‖dilateFun c f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  subst hμ
  have h := Measure.integral_comp_mul_left (fun y ↦ ‖f y‖ ^ 2) c
  have e : (fun x ↦ ‖dilateFun c f x‖ ^ 2) = fun x ↦ c * ‖f (c * x)‖ ^ 2 := by
    funext x
    rw [dilateFun, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c),
      mul_pow, Real.sq_sqrt hc.le]
  rw [e, integral_const_mul, h, abs_of_pos (inv_pos.mpr hc), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul]

/-- The half-density dilation `f ↦ √c f (c ·)` as a linear map of `L²`. -/
def lpDilationLinear {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_dilateFun hμ hc (Lp.memLp f)).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_dilateFun hμ hc (Lp.memLp f)).toLp _)
        ((memLp_dilateFun hμ hc (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp g)),
      dilateFun_congr_ae hμ hc (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    simp only [dilateFun, Pi.add_apply, mul_add]
  map_smul' a f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp (a • f))),
      Lp.coeFn_smul a ((memLp_dilateFun hμ hc (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp f)),
      dilateFun_congr_ae hμ hc (Lp.coeFn_smul a f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4]
    simp only [dilateFun, Pi.smul_apply, smul_eq_mul]
    ring

theorem lpDilationLinear_apply {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    (f : Lp ℂ 2 μ) :
    lpDilationLinear hμ hc f = (memLp_dilateFun hμ hc (Lp.memLp f)).toLp _ := rfl

/-- The half-density dilation preserves the norm of `L²`. -/
theorem norm_lpDilationLinear {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    (f : Lp ℂ 2 μ) : ‖lpDilationLinear hμ hc f‖ = ‖f‖ := by
  have h1 : ‖lpDilationLinear hμ hc f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ), ← L2.integral_sq_norm (𝕜 := ℂ) f,
      ← integral_sq_norm_dilateFun hμ hc (⇑f), lpDilationLinear_apply]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp f))] with x hx
    rw [hx]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

theorem norm_lpDilationLinear_le {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    (f : Lp ℂ 2 μ) : ‖lpDilationLinear hμ hc f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul, norm_lpDilationLinear hμ hc f]

open Classical in
/-- The half-density dilation `f ↦ √c f (c ·)` on `L²` of the line, for `c > 0`. It is zero
when `c ≤ 0`, and when the measure is not the Lebesgue measure. -/
def lpDilation (μ : Measure ℝ) (c : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  if h : μ = volume ∧ 0 < c then
    (lpDilationLinear h.1 h.2).mkContinuous 1 (norm_lpDilationLinear_le h.1 h.2)
  else 0

theorem lpDilation_apply_ae {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    (f : Lp ℂ 2 μ) : lpDilation μ c f =ᵐ[μ] dilateFun c f := by
  unfold lpDilation
  split_ifs with h
  · exact MemLp.coeFn_toLp (memLp_dilateFun hμ hc (Lp.memLp f))
  · exact absurd ⟨hμ, hc⟩ h

theorem norm_lpDilation_le (μ : Measure ℝ) (c : ℝ) : ‖lpDilation μ c‖ ≤ 1 := by
  rw [lpDilation]
  split_ifs with h
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · rw [norm_zero]
    exact zero_le_one

theorem lpDilation_one {μ : Measure ℝ} (hμ : μ = volume) : lpDilation μ 1 = 1 := by
  refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
  filter_upwards [lpDilation_apply_ae hμ zero_lt_one f] with x hx
  rw [hx, dilateFun, Real.sqrt_one, Complex.ofReal_one, one_mul, one_mul]
  rfl

theorem lpDilation_mul {μ : Measure ℝ} (hμ : μ = volume) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 < c') : lpDilation μ c * lpDilation μ c' = lpDilation μ (c * c') := by
  refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
  filter_upwards [lpDilation_apply_ae hμ hc (lpDilation μ c' f),
    dilateFun_congr_ae hμ hc (lpDilation_apply_ae hμ hc' f),
    lpDilation_apply_ae hμ (mul_pos hc hc') f] with x h1 h2 h3
  change (lpDilation μ c (lpDilation μ c' f)) x = _
  rw [h1, h2, h3]
  simp only [dilateFun]
  rw [Real.sqrt_mul hc.le, Complex.ofReal_mul, mul_comm c c', mul_assoc c' c x]
  ring

/-- A dilation moves a cutoff to the cutoff of the dilated interval. -/
theorem lpDilation_mul_lpCutoff {μ : Measure ℝ} (hμ : μ = volume) {c : ℝ} (hc : 0 < c)
    (X : ℝ) : lpDilation μ c * lpCutoff μ X = lpCutoff μ (X / c) * lpDilation μ c := by
  refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
  filter_upwards [lpDilation_apply_ae hμ hc (lpCutoff μ X f),
    dilateFun_congr_ae hμ hc (lpCutoff_apply_ae μ X f),
    lpCutoff_apply_ae μ (X / c) (lpDilation μ c f), lpDilation_apply_ae hμ hc f]
    with x h1 h2 h3 h4
  change (lpDilation μ c (lpCutoff μ X f)) x = (lpCutoff μ (X / c) (lpDilation μ c f)) x
  rw [h1, h2, h3, h4]
  simp only [dilateFun]
  rw [sharpIntervalMask_mul_left hc]
  ring

end Operators

section TestAction

/-- The action of a test function `ψ` of the dilation on a function `F`, at a point:
`∫ ψ g g ^ (-1/2) F (x / g) dg`. -/
def testActionFun (ψ : ℝ → ℂ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (g⁻¹ * x))

/-- The dilation of the action of `ψ` is the action of the rescaled test function: the
substitution `g = c u` in the integral. -/
theorem dilateFun_testActionFun {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (F : ℝ → ℂ) :
    dilateFun c (testActionFun ψ F) = testActionFun (scaleTest ψ c) F := by
  funext x
  have h := Measure.integral_comp_mul_left
    (fun g ↦ ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (g⁻¹ * (c * x)))) c
  have e3 : ((√c : ℝ) : ℂ) * ((c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', Complex.ofReal_one]
  have hpt : ∀ u : ℝ, scaleTest ψ c u * (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (u⁻¹ * x)) =
      ((c : ℂ) * ((√c : ℝ) : ℂ)) * (ψ (c * u) *
        ((((c * u) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F ((c * u)⁻¹ * (c * x)))) := by
    intro u
    by_cases hu : c * u ∈ Icc a b
    · have hu0 : 0 < u := pos_of_mul_pos_right (ha0.trans_le hu.1) hc.le
      have e1 : (c * u)⁻¹ * (c * x) = u⁻¹ * x := by
        field_simp
      rw [scaleTest, e1, Real.mul_rpow hc.le hu0.le, Complex.ofReal_mul]
      linear_combination (-((c : ℂ) * ψ (c * u) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        F (u⁻¹ * x))) * e3
    · rw [scaleTest, hψ0 _ hu]
      simp
  change ((√c : ℝ) : ℂ) * ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (g⁻¹ * (c * x))) =
    ∫ u, scaleTest ψ c u * (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (u⁻¹ * x))
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul, h, abs_of_pos (inv_pos.mpr hc),
    Complex.real_smul]
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  push_cast
  field_simp

/-- Reconstruction: the action of a test function maps a bounded continuous square-integrable
function to a square-integrable function. This is the Schur estimate: by Cauchy–Schwarz
`|A_ψ F (x)|² ≤ ‖ψ‖₁ ∫ |ψ g| g⁻¹ |F (x / g)|² dg`, and the right side is integrable in `x`
with integral `‖ψ‖₁ ‖F‖₂²`. -/
theorem memLp_testActionFun {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {F : ℝ → ℂ} (hFc : Continuous F) {B : ℝ}
    (hFb : ∀ y, ‖F y‖ ≤ B) (hF2 : Integrable fun y ↦ ‖F y‖ ^ 2) :
    MemLp (testActionFun ψ F) 2 := by
  have hψm := hψc.measurable
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (K := Icc a b) isCompact_Icc hψ0)
  let N : ℝ := ∫ y, ‖F y‖ ^ 2
  let K : ℝ × ℝ → ℝ := fun q ↦ ‖ψ q.2‖ * (q.2⁻¹ * ‖F (q.2⁻¹ * q.1)‖ ^ 2)
  have hKm : Measurable K :=
    (hψm.norm.comp measurable_snd).mul (measurable_snd.inv.mul
      ((hFc.measurable.comp (measurable_snd.inv.mul measurable_fst)).norm.pow_const 2))
  have hK0 : ∀ x g, g ∉ Icc a b → K (x, g) = 0 := fun x g hg ↦ by
    change ‖ψ g‖ * (g⁻¹ * ‖F (g⁻¹ * x)‖ ^ 2) = 0
    rw [hψ0 g hg, norm_zero, zero_mul]
  have hKx : ∀ g, Integrable fun x ↦ K (x, g) := by
    intro g
    by_cases hg : g ∈ Icc a b
    · have hg0 : g⁻¹ ≠ 0 := inv_ne_zero (ha0.trans_le hg.1).ne'
      exact ((hF2.comp_mul_left' hg0).const_mul g⁻¹).const_mul ‖ψ g‖
    · have e : (fun x ↦ K (x, g)) = fun _ ↦ (0 : ℝ) := funext fun x ↦ hK0 x g hg
      rw [e]
      exact integrable_zero _ _ _
  have hKint : ∀ g, ∫ x, ‖K (x, g)‖ = ‖ψ g‖ * N := by
    intro g
    by_cases hg : g ∈ Icc a b
    · have hg0 : 0 < g := ha0.trans_le hg.1
      have hnn : (fun x ↦ ‖K (x, g)‖) = fun x ↦ ‖ψ g‖ * (g⁻¹ * ‖F (g⁻¹ * x)‖ ^ 2) :=
        funext fun x ↦ Real.norm_of_nonneg
          (mul_nonneg (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hg0.le) (sq_nonneg _)))
      rw [hnn, integral_const_mul, integral_const_mul,
        Measure.integral_comp_mul_left (fun y ↦ ‖F y‖ ^ 2) g⁻¹, inv_inv, abs_of_pos hg0,
        smul_eq_mul, ← mul_assoc g⁻¹, inv_mul_cancel₀ hg0.ne', one_mul]
    · have e : (fun x ↦ ‖K (x, g)‖) = fun _ ↦ (0 : ℝ) := funext fun x ↦ by
        rw [hK0 x g hg, norm_zero]
      rw [e, integral_zero, hψ0 g hg, norm_zero, zero_mul]
  have hKprod : Integrable K ((volume : Measure ℝ).prod volume) := by
    refine (integrable_prod_iff' hKm.aestronglyMeasurable).2 ⟨ae_of_all _ hKx, ?_⟩
    rw [funext hKint]
    exact hψi.norm.mul_const N
  have hh : Integrable fun x ↦ ∫ g, K (x, g) := hKprod.integral_prod_left
  have hpt : ∀ x, ‖testActionFun ψ F x‖ ^ 2 ≤ (∫ g, ‖ψ g‖) * ∫ g, K (x, g) := by
    intro x
    let u : ℝ → ℝ := fun g ↦ √‖ψ g‖
    let v : ℝ → ℝ := fun g ↦ √‖ψ g‖ * (g ^ (-(1 / 2 : ℝ)) * ‖F (g⁻¹ * x)‖)
    have hu : MemLp u 2 := (Real.continuous_sqrt.comp hψc.norm).memLp_of_hasCompactSupport
      (HasCompactSupport.intro (K := Icc a b) isCompact_Icc fun g hg ↦ by simp [hψ0 g hg])
    have hv2 : ∀ g, v g ^ 2 = K (x, g) := by
      intro g
      change (√‖ψ g‖ * (g ^ (-(1 / 2 : ℝ)) * ‖F (g⁻¹ * x)‖)) ^ 2 =
        ‖ψ g‖ * (g⁻¹ * ‖F (g⁻¹ * x)‖ ^ 2)
      by_cases hg : g ∈ Icc a b
      · have hg0 : 0 < g := ha0.trans_le hg.1
        have e : (g ^ (-(1 / 2 : ℝ))) ^ 2 = g⁻¹ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hg0.le, ← Real.rpow_neg_one]
          norm_num
        rw [mul_pow, mul_pow, Real.sq_sqrt (norm_nonneg _), e]
      · rw [hψ0 g hg]
        simp
    have hvm : Measurable v :=
      (Real.continuous_sqrt.measurable.comp hψm.norm).mul ((measurable_id.pow_const _).mul
        (hFc.measurable.comp (measurable_inv.mul_const x)).norm)
    have hvi : Integrable fun g ↦ ‖v g‖ ^ 2 := by
      have hdom : Integrable fun g ↦ ‖ψ g‖ * (a⁻¹ * B ^ 2) := hψi.norm.mul_const _
      refine hdom.mono' (hvm.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun g ↦ ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs, hv2 g]
      by_cases hg : g ∈ Icc a b
      · have hg0 : 0 < g := ha0.trans_le hg.1
        have h1 : g⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hg.1
        have h2 : ‖F (g⁻¹ * x)‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hFb _) 2
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul h1 h2 (sq_nonneg _) (inv_nonneg.mpr ha0.le)) (norm_nonneg _)
      · rw [hK0 x g hg, hψ0 g hg, norm_zero, zero_mul]
    have hv : MemLp v 2 := (memLp_two_iff_integrable_sq_norm hvm.aestronglyMeasurable).2 hvi
    have he : ENNReal.ofReal 2 = 2 := by simp
    have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (he ▸ hu) (he ▸ hv)
    simp only [← Real.sqrt_eq_rpow, Real.rpow_two] at hH
    have hu2 : ∫ g, ‖u g‖ ^ 2 = ∫ g, ‖ψ g‖ := integral_congr_ae (ae_of_all _ fun g ↦ by
      change ‖√‖ψ g‖‖ ^ 2 = ‖ψ g‖
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)])
    have hv2' : ∫ g, ‖v g‖ ^ 2 = ∫ g, K (x, g) := integral_congr_ae (ae_of_all _ fun g ↦ by
      change ‖v g‖ ^ 2 = K (x, g)
      rw [Real.norm_eq_abs, sq_abs, hv2 g])
    have hnorm : ∀ g, ‖ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (g⁻¹ * x))‖ =
        ‖u g‖ * ‖v g‖ := by
      intro g
      change _ = ‖√‖ψ g‖‖ * ‖√‖ψ g‖ * (g ^ (-(1 / 2 : ℝ)) * ‖F (g⁻¹ * x)‖)‖
      by_cases hg : g ∈ Icc a b
      · have hg0 : 0 < g := ha0.trans_le hg.1
        have hr : 0 ≤ g ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hg0.le _
        have e : √‖ψ g‖ * (√‖ψ g‖ * (g ^ (-(1 / 2 : ℝ)) * ‖F (g⁻¹ * x)‖)) =
            ‖ψ g‖ * (g ^ (-(1 / 2 : ℝ)) * ‖F (g⁻¹ * x)‖) := by
          rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
          Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg
            (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hr (norm_nonneg _))), e]
      · rw [hψ0 g hg]
        simp
    have hK0' : 0 ≤ ∫ g, K (x, g) := by
      rw [← hv2']
      exact integral_nonneg fun g ↦ sq_nonneg _
    have hψ0' : 0 ≤ ∫ g, ‖ψ g‖ := integral_nonneg fun g ↦ norm_nonneg _
    have h1 : ‖testActionFun ψ F x‖ ≤ √(∫ g, ‖ψ g‖) * √(∫ g, K (x, g)) := by
      calc ‖testActionFun ψ F x‖
          ≤ ∫ g, ‖ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (g⁻¹ * x))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ g, ‖u g‖ * ‖v g‖ := integral_congr_ae (ae_of_all _ hnorm)
        _ ≤ √(∫ g, ‖ψ g‖) * √(∫ g, K (x, g)) := by
            rw [← hu2, ← hv2']
            exact hH
    calc ‖testActionFun ψ F x‖ ^ 2 ≤ (√(∫ g, ‖ψ g‖) * √(∫ g, K (x, g))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (∫ g, ‖ψ g‖) * ∫ g, K (x, g) := by
          rw [mul_pow, Real.sq_sqrt hψ0', Real.sq_sqrt hK0']
  have hmeas : AEStronglyMeasurable (testActionFun ψ F) := by
    have hjm : Measurable fun q : ℝ × ℝ ↦
        ψ q.2 * (((q.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (q.2⁻¹ * q.1)) :=
      (hψm.comp measurable_snd).mul ((Complex.measurable_ofReal.comp
        (measurable_snd.pow_const _)).mul
        (hFc.measurable.comp (measurable_snd.inv.mul measurable_fst)))
    exact (hjm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2
    ((hh.const_mul (∫ g, ‖ψ g‖)).mono' (hmeas.norm.pow 2) (ae_of_all _ fun x ↦ ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hpt x

end TestAction

section Band

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀

/-- The action of a test function on a band vector is square integrable. -/
theorem memLp_testActionFun_evaluation (hY : 0 ≤ Y) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (f : V₀) :
    MemLp (testActionFun ψ fun y ↦ ev y f) 2 μ₀ := by
  obtain ⟨hI, -⟩ := integral_sq_norm_evaluation Y hs f
  have h := memLp_testActionFun ha0 hψc hψ0 (continuous_evaluation_apply Y hs f)
    (B := √(2 * Y) * ‖f‖) (fun y ↦ ((ev y).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (RealPWBand.norm_evaluation_le Y hY hμ₀ y) (norm_nonneg _))) hI
  have key : ∀ G : ℝ → ℂ, MemLp G 2 → MemLp G 2 μ₀ := fun G hG ↦ by
    rw [realPWIntervalMeasure_zero_zero]
    exact hG
  exact key _ h

open Classical in
/-- The action `A_ψ f` of a test function of the dilation on a band vector, as an element of
`L²` of the line: the class of `x ↦ ∫ ψ g g ^ (-1/2) f (x / g) dg`. -/
def bandTestAction (ψ : ℝ → ℂ) (f : V₀) : Lp ℂ 2 μ₀ :=
  if h : MemLp (testActionFun ψ fun y ↦ ev y f) 2 μ₀ then h.toLp _ else 0

theorem bandTestAction_ae (hY : 0 ≤ Y) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (f : V₀) :
    bandTestAction Y hs ψ f =ᵐ[μ₀] testActionFun ψ fun y ↦ ev y f := by
  unfold bandTestAction
  split_ifs with h
  · exact MemLp.coeFn_toLp h
  · exact absurd (memLp_testActionFun_evaluation Y hs hY ha0 hψc hψ0 f) h

/-- The dilation of `A_ψ f` is the action of the rescaled test function: `T ^ k A_ψ = A_{ψ_c}`
for `c = p ^ k`. -/
theorem lpDilation_bandTestAction (hY : 0 ≤ Y) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {c : ℝ} (hc : 0 < c) (f : V₀) :
    lpDilation μ₀ c (bandTestAction Y hs ψ f) = bandTestAction Y hs (scaleTest ψ c) f := by
  refine Lp.ext ?_
  have hμ : μ₀ = volume := realPWIntervalMeasure_zero_zero
  filter_upwards [lpDilation_apply_ae hμ hc (bandTestAction Y hs ψ f),
    dilateFun_congr_ae hμ hc (bandTestAction_ae Y hs hY ha0 hψc hψ0 f),
    bandTestAction_ae Y hs hY (div_pos ha0 hc) (continuous_scaleTest hψc c)
      (fun _ hg ↦ scaleTest_eq_zero hψ0 hc hg) f] with x h1 h2 h3
  rw [h1, h2, h3, dilateFun_testActionFun hc ha0 hψ0]

/-- A block applied to a band vector: the projection onto the band of the cutoff of the action
of the test function. -/
theorem IsBandBlock.apply_eq (hY : 0 ≤ Y) {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {T : V₀ →L[ℂ] V₀} {X : ℝ}
    (h : IsBandBlock Y hs T φ X) (f : V₀) :
    T f = (V₀).orthogonalProjectionOnto (lpCutoff μ₀ X (bandTestAction Y hs φ f)) := by
  obtain ⟨ρ, hρ, hT⟩ := h f
  have hρ' : ρ = lpCutoff μ₀ X (bandTestAction Y hs φ f) := Lp.ext (by
    filter_upwards [hρ, lpCutoff_apply_ae μ₀ X (bandTestAction Y hs φ f),
      bandTestAction_ae Y hs hY ha0 hφc hφ0 f] with t h1 h2 h3
    rw [h1, h2, h3]
    rfl)
  rw [hT, hρ']

/-- The dilation `T ^ k` on `L²` of the line, for `T f (x) = √p f (p x)`. -/
def primeDilation (p : ℝ) (k : ℤ) : Lp ℂ 2 μ₀ →L[ℂ] Lp ℂ 2 μ₀ := lpDilation μ₀ (p ^ k)

theorem isContractiveIntRep_primeDilation {p : ℝ} (hp : 0 < p) :
    IsContractiveIntRep (primeDilation p) where
  zero := by
    rw [primeDilation, zpow_zero]
    exact lpDilation_one realPWIntervalMeasure_zero_zero
  add m n := by
    rw [primeDilation, primeDilation, primeDilation,
      lpDilation_mul realPWIntervalMeasure_zero_zero (zpow_pos hp m) (zpow_pos hp n),
      zpow_add₀ hp.ne']
  norm_le n := norm_lpDilation_le _ _

/-- `T ^ k M_{L p ^ e} = M_{L p ^ (e - k)} T ^ k`. -/
theorem primeDilation_mul_lpCutoff {p : ℝ} (hp : 0 < p) (L : ℝ) (k e : ℤ) :
    primeDilation p k * lpCutoff μ₀ (L * p ^ e) =
      lpCutoff μ₀ (L * p ^ (e - k)) * primeDilation p k := by
  rw [primeDilation, lpDilation_mul_lpCutoff realPWIntervalMeasure_zero_zero (zpow_pos hp k),
    zpow_sub₀ hp.ne', mul_div_assoc]

/-- The cutoff twisted at a prime, `U⁻¹ M_L U` on `L²` of the line, where
`U = (1 - r T⁻¹) (1 - r T)⁻¹` and `T f (x) = √p f (p x)`. -/
def primeTwistedCutoff (p r L : ℝ) : Lp ℂ 2 μ₀ →L[ℂ] Lp ℂ 2 μ₀ :=
  twistOperator (fun n ↦ primeDilation p (-n)) r * lpCutoff μ₀ L *
    twistOperator (primeDilation p) r

/-- One term of the expansion of the twisted cutoff, applied to `A_ψ f` and projected onto the
band, is the block with its coefficient. -/
theorem orthogonalProjectionOnto_twistTerm (hY : 0 ≤ Y) {p : ℝ} (hp : 0 < p) {a b : ℝ}
    (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {L : ℝ}
    {T : V₀ →L[ℂ] V₀} (i : ℕ) (e : ℤ) (c₀ : ℂ) {X c : ℝ}
    (hX : X = L * p ^ ((i : ℤ) - 1)) (hce : c = p ^ e)
    (hT : IsBandBlock Y hs T (scaleTest ψ c) X) (f : V₀) :
    (V₀).orthogonalProjectionOnto
        ((c₀ • (lpCutoff μ₀ (L * p ^ ((i : ℤ) - 1)) * primeDilation p e))
          (bandTestAction Y hs ψ f)) = (c₀ • T) f := by
  subst hX hce
  have hc : 0 < p ^ e := zpow_pos hp e
  change (V₀).orthogonalProjectionOnto (c₀ • lpCutoff μ₀ (L * p ^ ((i : ℤ) - 1))
    (lpDilation μ₀ (p ^ e) (bandTestAction Y hs ψ f))) = c₀ • T f
  rw [map_smul, lpDilation_bandTestAction Y hs hY ha0 hψc hψ0 hc f,
    hT.apply_eq Y hs hY (div_pos ha0 hc) (continuous_scaleTest hψc _)
      (fun _ hg ↦ scaleTest_eq_zero hψ0 hc hg) f]

/-- Reconstruction: the sum of the blocks is the compression of the twisted cutoff. An
operator on the band that is the sum of the blocks in the sense of `IsPrimeTwistedCutoff`
sends `f` to the orthogonal projection onto the band of `U⁻¹ M_L U A_ψ f`. The proof expands
`U` and `U⁻¹` in powers of `T`, moves the powers of `T` through the cutoff, which rescales the
interval, and through `A_ψ`, which rescales the test function. -/
theorem IsPrimeTwistedCutoff.apply_eq (hY : 0 < Y) {p r : ℝ} (hp : 1 < p) (hr0 : 0 < r)
    (hr1 : r < 1) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {L : ℝ} {T : V₀ →L[ℂ] V₀}
    (hT : IsPrimeTwistedCutoff Y hs T r p ψ L) (f : V₀) :
    T f = (V₀).orthogonalProjectionOnto
      (primeTwistedCutoff p r L (bandTestAction Y hs ψ f)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨Tu, Tl, hTu, hTl, hsu, hsl, rfl⟩ := hT
  have hS := isContractiveIntRep_primeDilation hp0
  obtain ⟨hsum, -⟩ := hS.hasSum_twist_conj hr0 hr1 (fun e ↦ lpCutoff μ₀ (L * p ^ e))
    (primeDilation_mul_lpCutoff hp0 L)
  simp only [zpow_zero, mul_one] at hsum
  let w : Lp ℂ 2 μ₀ := bandTestAction Y hs ψ f
  let F : ℕ × ℕ → Lp ℂ 2 μ₀ := fun z ↦
    (((primeTwistCoeff r z.1 * primeTwistCoeff r z.2 : ℝ) : ℂ) •
      (lpCutoff μ₀ (L * p ^ ((z.1 : ℤ) - 1)) * primeDilation p ((z.2 : ℤ) - z.1))) w
  have hw : HasSum F (primeTwistedCutoff p r L w) :=
    hsum.mapL (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ₀) w)
  have hsplit : primeTwistedCutoff p r L w =
      (∑' x : ℕ × ℕ, F (x.2, x.2 + x.1)) + ∑' x : ℕ × ℕ, F (x.2 + x.1 + 1, x.2) :=
    hasSum_eq_upper_add_lower hw
  have hinjU : Function.Injective fun x : ℕ × ℕ ↦ (x.2, x.2 + x.1) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  have hinjL : Function.Injective fun x : ℕ × ℕ ↦ (x.2 + x.1 + 1, x.2) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  have hsU : Summable fun x : ℕ × ℕ ↦ F (x.2, x.2 + x.1) :=
    hw.summable.comp_injective hinjU
  have hsL : Summable fun x : ℕ × ℕ ↦ F (x.2 + x.1 + 1, x.2) :=
    hw.summable.comp_injective hinjL
  have hopU : Summable fun x : ℕ × ℕ ↦ ((primeUpperCoeff r x : ℝ) : ℂ) • (Tu x).val :=
    Summable.of_norm_bounded hsu fun x ↦ by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_val_le_traceNorm _) (abs_nonneg _)
  have hopL : Summable fun x : ℕ × ℕ ↦ ((primeLowerCoeff r x : ℝ) : ℂ) • (Tl x).val :=
    Summable.of_norm_bounded hsl fun x ↦ by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_val_le_traceNorm _) (abs_nonneg _)
  have hU : ∀ x : ℕ × ℕ, (V₀).orthogonalProjectionOnto (F (x.2, x.2 + x.1)) =
      (((primeUpperCoeff r x : ℝ) : ℂ) • (Tu x).val) f := by
    intro x
    have hX : L * p ^ x.2 / p = L * p ^ (((x.2 : ℕ) : ℤ) - 1) := by
      rw [zpow_sub_one₀ hp0.ne', zpow_natCast]
      ring
    have hce : p ^ x.1 = p ^ (((x.2 + x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ)) := by
      rw [← zpow_natCast]
      congr 1
      push_cast
      ring
    change (V₀).orthogonalProjectionOnto ((((primeUpperCoeff r x : ℝ) : ℂ) •
      (lpCutoff μ₀ (L * p ^ (((x.2 : ℕ) : ℤ) - 1)) *
        primeDilation p (((x.2 + x.1 : ℕ) : ℤ) - ((x.2 : ℕ) : ℤ)))) w) = _
    exact orthogonalProjectionOnto_twistTerm Y hs hY.le hp0 ha0 hψc hψ0 x.2 _ _ hX hce
      (hTu x) f
  have hL : ∀ x : ℕ × ℕ, (V₀).orthogonalProjectionOnto (F (x.2 + x.1 + 1, x.2)) =
      (((primeLowerCoeff r x : ℝ) : ℂ) • (Tl x).val) f := by
    intro x
    have hX : L * p ^ (x.2 + x.1 + 1) / p = L * p ^ (((x.2 + x.1 + 1 : ℕ) : ℤ) - 1) := by
      rw [zpow_sub_one₀ hp0.ne', zpow_natCast]
      ring
    have hce : (p ^ (x.1 + 1))⁻¹ = p ^ (((x.2 : ℕ) : ℤ) - ((x.2 + x.1 + 1 : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    change (V₀).orthogonalProjectionOnto ((((primeLowerCoeff r x : ℝ) : ℂ) •
      (lpCutoff μ₀ (L * p ^ (((x.2 + x.1 + 1 : ℕ) : ℤ) - 1)) *
        primeDilation p (((x.2 : ℕ) : ℤ) - ((x.2 + x.1 + 1 : ℕ) : ℤ)))) w) = _
    exact orthogonalProjectionOnto_twistTerm Y hs hY.le hp0 ha0 hψc hψ0 (x.2 + x.1 + 1) _ _
      hX hce (hTl x) f
  have hTf : ((∑' x, ((primeUpperCoeff r x : ℝ) : ℂ) • (Tu x).val) +
      ∑' x, ((primeLowerCoeff r x : ℝ) : ℂ) • (Tl x).val) f =
      (∑' x, (((primeUpperCoeff r x : ℝ) : ℂ) • (Tu x).val) f) +
        ∑' x, (((primeLowerCoeff r x : ℝ) : ℂ) • (Tl x).val) f := by
    exact congrArg₂ (· + ·) ((ContinuousLinearMap.apply ℂ V₀ f).map_tsum hopU)
      ((ContinuousLinearMap.apply ℂ V₀ f).map_tsum hopL)
  change _ = (V₀).orthogonalProjectionOnto (primeTwistedCutoff p r L w)
  rw [hTf, hsplit, map_add, ContinuousLinearMap.map_tsum _ hsU,
    ContinuousLinearMap.map_tsum _ hsL]
  congr 1
  · exact tsum_congr fun x ↦ (hU x).symm
  · exact tsum_congr fun x ↦ (hL x).symm

/-- Reconstruction: the trace of the cutoff twisted at a prime, as a product of operators. For
`r² p ≤ 1` and each `L > 0`, the compression to the band of `U⁻¹ M_L U A_ψ` is a nuclear
operator `T L`, and as the cutoff is removed its trace less `ψ 1 log (2πY L)` converges to the
real-place limit plus `log p` times the sum over `n ≥ 1` of `r ^ n (φ (p ^ n) + φ (p ^ (-n)))`,
`φ g = g ψ g`. Here `T f (x) = √p f (p x)` and `U = (1 - r T⁻¹) (1 - r T)⁻¹`. This joins
`exists_primeTwistedCutoff_trace_limit` and `IsPrimeTwistedCutoff.apply_eq`.
Paper: for `r = p ^ (-1/2)` this is the term of the place `p` in Theorem 12.4.1.1,
(12.4.1.1), p. 514, for `F = ℚ`, and the statement is the case `k = ℚ`, `S = {∞, p}` of
A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
function*, §VII, Theorem 4, p. 31, on the functions invariant under the units of `ℚ_p`.
Deviation: that `Q U⁻¹ M_L U A_ψ Q` is the cutoff operator of Connes on that sector of
`L²(X_S)` is not formalized. The band has a fixed width `Y`, where Connes cuts both variables
at the same `Λ`. The test function is assumed Lipschitz. -/
theorem exists_primeTwistedCutoff_compression_trace_limit (hY : 0 < Y) {p r : ℝ} (hp : 1 < p)
    (hr0 : 0 < r) (hrp : r ^ 2 * p ≤ 1) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L, 0 < L → ∀ f : V₀, (T L).val f = (V₀).orthogonalProjectionOnto
        (primeTwistedCutoff p r L (bandTestAction Y hs ψ f))) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) -
          ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop
        (𝓝 (ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
          (∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ)) +
          ((Real.log p : ℝ) : ℂ) * ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) *
            (((p ^ (n + 1) : ℝ) : ℂ) * ψ (p ^ (n + 1)) +
              (((p ^ (n + 1))⁻¹ : ℝ) : ℂ) * ψ ((p ^ (n + 1))⁻¹)))) := by
  obtain ⟨T, hT, hlim⟩ :=
    exists_primeTwistedCutoff_trace_limit Y hs hY hp hr0 hrp ha0 hψc hψ0 hK
  exact ⟨T, fun L hL f ↦ (hT L hL).apply_eq Y hs hY hp hr0 (lt_one_of_sq_mul_le hp hrp) ha0
    hψc hψ0 f, hlim⟩

end Band

end RiemannMasullo.Isolated
