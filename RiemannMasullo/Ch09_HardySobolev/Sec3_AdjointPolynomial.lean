module

public import RiemannMasullo.Ch09_HardySobolev.Sec3_Adjoint
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # The adjoint of a weighted convolution for a polynomial density

On the weighted space of §9.2 the Hilbert adjoint of convolution by a test is convolution by the
reflected conjugate test, conjugated by the density (`hardySobolevTestAction_compact_kernels` of
`Sec3_Adjoint`). When the density is the polynomial `(1 + t ^ 2) ^ n` of the logarithm of the
modulation, as it is on the base interval `{0}` at the even Sobolev order `s = 2 n`, the
translate of the density is the density times a polynomial in the shift with bounded
coefficients (`one_add_sq_add_pow`). The adjoint is then an exact finite sum
(`hardySobolevTestAction_adjoint_eq_sum_polyWeight`): convolutions by the test times powers of
minus the logarithm of the modulation, each followed by multiplication by a bounded function.

`Ch10_TraceSpectral/Sec4b_GeometricRecursion` uses this to write the geometric part of
Theorem 10.4.3.5 on the line as such a sum. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace Pointwise ComplexConjugate ContDiff

namespace RiemannMasullo.WeightedConvolution

section PolynomialWeight

/-- The pairs `(k, l)` with `l ≤ k ≤ n`, which index the terms of
`(1 + p r + q r ^ 2) ^ n`. -/
def polyWeightIndex (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (n + 1)).sigma fun k ↦ Finset.range (k + 1)

/-- The coefficient of the term `(k, l)` of `(1 + p r + q r ^ 2) ^ n`. -/
def polyWeightCoeff (n : ℕ) (i : Σ _ : ℕ, ℕ) : ℕ := n.choose i.1 * i.1.choose i.2

/-- The bounded factor of the term `(k, l)`: with `p = 2 t / (1 + t ^ 2)` and
`q = 1 / (1 + t ^ 2)` it is `p ^ (k - l) q ^ l`. -/
def polyWeightMask (i : Σ _ : ℕ, ℕ) (t : ℝ) : ℝ :=
  (2 * t / (1 + t ^ 2)) ^ (i.1 - i.2) * (1 / (1 + t ^ 2)) ^ i.2

theorem abs_polyWeightMask_le_one (i : Σ _ : ℕ, ℕ) (t : ℝ) : |polyWeightMask i t| ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hp : |2 * t / (1 + t ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_mul, abs_two]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hq : |1 / (1 + t ^ 2)| ≤ 1 := by
    rw [abs_div, abs_one, abs_of_pos hpos, div_le_one hpos]
    nlinarith [sq_nonneg t]
  unfold polyWeightMask
  rw [abs_mul, abs_pow, abs_pow]
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) hp) (pow_le_one₀ (abs_nonneg _) hq)
    (pow_nonneg (abs_nonneg _) _) zero_le_one).trans (one_mul 1).le

private theorem sum_polyWeightIndex (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ polyWeightIndex n, F i.1 i.2 =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1), F k l :=
  Finset.sum_sigma (Finset.range (n + 1)) (fun k ↦ Finset.range (k + 1)) (fun i ↦ F i.1 i.2)

private theorem one_add_mul_add_mul_sq_pow (n : ℕ) (P Q r : ℝ) :
    (1 + P * r + Q * r ^ 2) ^ n = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
      ((n.choose k * k.choose l : ℕ) : ℝ) * (P ^ (k - l) * Q ^ l) * r ^ (k + l) := by
  rw [show 1 + P * r + Q * r ^ 2 = (Q * r ^ 2 + P * r) + 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [one_pow, mul_one, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hr : (r ^ 2) ^ l * r ^ (k - l) = r ^ (k + l) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← hr]
  push_cast
  ring

/-- The translate of the polynomial weight `(1 + t ^ 2) ^ n` is the weight times a polynomial
in the shift whose coefficients are bounded functions of `t`. -/
theorem one_add_sq_add_pow (n : ℕ) (t r : ℝ) :
    (1 + (t + r) ^ 2) ^ n = (1 + t ^ 2) ^ n *
      ∑ i ∈ polyWeightIndex n,
        (polyWeightCoeff n i : ℝ) * polyWeightMask i t * r ^ (i.1 + i.2) := by
  have hq : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h1 : 1 + (t + r) ^ 2 =
      (1 + t ^ 2) * (1 + 2 * t / (1 + t ^ 2) * r + 1 / (1 + t ^ 2) * r ^ 2) := by
    field_simp
    ring
  rw [h1, mul_pow, one_add_mul_add_mul_sq_pow]
  congr 1
  exact (sum_polyWeightIndex n fun k l ↦ ((n.choose k * k.choose l : ℕ) : ℝ) *
    ((2 * t / (1 + t ^ 2)) ^ (k - l) * (1 / (1 + t ^ 2)) ^ l) * r ^ (k + l)).symm

/-- The sum of the coefficients against powers of `δ`. -/
theorem sum_polyWeightCoeff_mul_pow (n : ℕ) (δ : ℝ) :
    ∑ i ∈ polyWeightIndex n, (polyWeightCoeff n i : ℝ) * δ ^ (i.1 + i.2) =
      (1 + δ + δ ^ 2) ^ n := by
  have h := one_add_mul_add_mul_sq_pow n 1 1 δ
  rw [one_mul, one_mul] at h
  rw [h]
  refine (sum_polyWeightIndex n fun k l ↦ ((n.choose k * k.choose l : ℕ) : ℝ) * δ ^ (k + l)).trans
    (Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_)
  rw [one_pow, one_pow, mul_one, mul_one]

end PolynomialWeight

section Tests

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Bruhat differentiability of a fixed order is preserved by the reflected conjugate.
A copy of the private `isBruhatContDiff_conj_inv` of `Sec3_AdjointSymbols`. -/
private theorem isBruhatContDiff_conj_inv' {f : G → ℂ} {p : ℕ} (h : IsBruhatContDiff p f) :
    IsBruhatContDiff p (fun x ↦ star (f x⁻¹)) := by
  obtain ⟨k, hk, hinv, hdesc⟩ := h
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · exact congrArg star (by simpa only [mul_inv_rev, Subgroup.coe_inv, mul_comm] using hinv h⁻¹ x⁻¹)
  · obtain ⟨f₀, hf₀, hd⟩ := hdesc a ha
    refine ⟨fun x ↦ star (f₀ x⁻¹), fun x ↦ ?_, fun e z b ↦ ?_⟩
    · exact congrArg star (hf₀ x⁻¹)
    · have hcov (t) : (e.equiv.symm (Multiplicative.ofAdd (elementaryCover t z b)))⁻¹ =
          e.equiv.symm (Multiplicative.ofAdd (elementaryCover (-t) (-z) (-b))) := by
        rw [← map_inv]
        apply congrArg e.equiv.symm
        apply congrArg Multiplicative.ofAdd
        exact Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_neg (1 : ℝ)).symm) rfl)
      simp only [hcov]
      exact Complex.conjCLE.contDiff.comp ((hd e (-z) (-b)).comp contDiff_neg)

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- The reflected conjugate `g ↦ conj (φ g⁻¹)` of a compact Bruhat test is a compact Bruhat
test. Convolution by it is the adjoint, for Haar measure, of convolution by `φ`. -/
theorem exists_bruhatCompactSupport_conjInv (φ : BruhatCompactSupport G) :
    ∃ φ' : BruhatCompactSupport G, ∀ g, φ'.val g = star (φ.val g⁻¹) := by
  have hφ := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc : HasCompactSupport φ.val := φ.property.2
  exact ⟨⟨fun x ↦ star (φ.val x⁻¹),
    (mem_bruhatSmoothSubmodule_iff _).mpr (fun p ↦ isBruhatContDiff_conj_inv' (hφ p)),
    (hc.comp_homeomorph (Homeomorph.inv G)).comp_left (star_zero ℂ)⟩, fun _ ↦ rfl⟩

/-- A compact Bruhat test times a power of minus the logarithm of the modulation is a compact
Bruhat test. -/
theorem exists_bruhatCompactSupport_logPow (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G) :
    ∃ Φ : ℕ → BruhatCompactSupport G, ∀ e g,
      (Φ e).val g = (((-Real.log ((m g).val : ℝ)) ^ e : ℝ) : ℂ) * φ.val g := by
  have hr (e : ℕ) : ContDiff ℝ ∞ (fun t : ℝ ↦ (((-t) ^ e : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_neg.pow e)
  exact ⟨fun e ↦ ⟨fun g ↦ (((-Real.log ((m g).val : ℝ)) ^ e : ℝ) : ℂ) * φ.val g,
    (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
      isBruhatContDiff_mul (isBruhatSmooth_logProfile m (hr e) p)
        ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (show HasCompactSupport φ.val from φ.property.2).mul_left⟩, fun _ _ ↦ rfl⟩

end Tests

section AdjointIdentity

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "L" => (fun x ↦ Real.log ((m x).val : ℝ))
local notation "ν" => (fun a b s ↦ intervalSobolevMeasure μ L a b s)

/-- The norm closure of the continuous compactly supported representatives is all of weighted
L². A copy of the private `dense_compactCore` of `Sec3_Adjoint`. -/
private theorem dense_compactCore' (ν₀ : Measure G) [IsLocallyFiniteMeasure ν₀] :
    Dense {u : Lp ℂ 2 ν₀ | ∃ f : G → ℂ,
      Continuous f ∧ HasCompactSupport f ∧ (u : G → ℂ) =ᵐ[ν₀] f} := by
  intro u
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨f, hc, he, hf, hm⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδ.ne'
  refine ⟨hm.toLp f, ⟨f, hf, hc, hm.coeFn_toLp⟩, ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
  exact he.trans_lt hδε

/-- A finite sum of square-integrable classes is represented by the sum of representatives. -/
private theorem coeFn_finset_sum_ae {ι : Type*} (ν₀ : Measure G) (s : Finset ι)
    (F : ι → Lp ℂ 2 ν₀) (f : ι → G → ℂ) (h : ∀ i ∈ s, (F i : G → ℂ) =ᵐ[ν₀] f i) :
    ((∑ i ∈ s, F i : Lp ℂ 2 ν₀) : G → ℂ) =ᵐ[ν₀] fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 ν₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), h a (Finset.mem_insert_self a s),
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert ha]

theorem continuous_polyWeightMask (i : Σ _ : ℕ, ℕ) : Continuous (polyWeightMask i) := by
  have hne (t : ℝ) : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  unfold polyWeightMask
  exact (((continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) hne).pow _).mul
    ((continuous_const.div (continuous_const.add (continuous_id.pow 2)) hne).pow _)

/-- Multiplication by a bounded factor `polyWeightMask i` of the logarithm of the modulation is
a contraction of the weighted space. -/
theorem exists_polyWeightMask_multiplier (a b s : ℝ) (i : Σ _ : ℕ, ℕ) :
    ∃ T : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s, ‖T‖ ≤ 1 ∧
      ∀ u, (T u : G → ℂ) =ᵐ[ν a b s] fun x ↦ ((polyWeightMask i (L x) : ℝ) : ℂ) * u x := by
  have hL : Continuous L := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    m.continuous)).log fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  let σ : G → ℂ := fun x ↦ ((polyWeightMask i (L x) : ℝ) : ℂ)
  have hσ : Continuous σ := Complex.continuous_ofReal.comp ((continuous_polyWeightMask i).comp hL)
  have hb (x : G) : ‖σ x‖ ≤ 1 := by
    simpa [σ, Complex.norm_real] using abs_polyWeightMask_le_one i (L x)
  let h : MemLp σ ∞ (ν a b s) := memLp_top_of_bound hσ.aestronglyMeasurable 1 (.of_forall hb)
  let mul := ContinuousLinearMap.mul ℂ ℂ
  let T : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    mul.holderL (ν a b s) ∞ 2 2 (h.toLp σ)
  have hT (u : CompactIntervalSobolev μ L a b s) :
      (T u : G → ℂ) =ᵐ[ν a b s] fun x ↦ σ x * u x :=
    (mul.coeFn_holder (r := 2) (h.toLp σ) u).trans
      (h.coeFn_toLp.mono fun x hx ↦ congrArg (· * u x) hx)
  refine ⟨T, T.opNorm_le_bound zero_le_one fun u ↦ ?_, hT⟩
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hT u] with x hx
  rw [hx, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

/-- For the polynomial density `(1 + t ^ 2) ^ n`, the Hilbert adjoint of convolution by the
reflected conjugate of a test `φ` is a finite sum of convolutions by `φ` times powers of minus
the logarithm of the modulation, each followed by multiplication by a bounded function of that
logarithm. The term of the pair `(0, 0)` is convolution by `φ` itself. The identity is the
expansion of the translated weight (`one_add_sq_add_pow`) inside the kernel of the adjoint
(`hardySobolevTestAction_compact_kernels`), checked on continuous compactly supported inputs. -/
theorem hardySobolevTestAction_adjoint_eq_sum_polyWeight (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (n : ℕ) (hw : ∀ t, intervalSobolevDensity a b s t = (1 + t ^ 2) ^ n)
    (φ φ' : BruhatCompactSupport G) (hφ' : ∀ g, φ'.val g = star (φ.val g⁻¹))
    (Φ : ℕ → BruhatCompactSupport G)
    (hΦ : ∀ e g, (Φ e).val g = (((-Real.log ((m g).val : ℝ)) ^ e : ℝ) : ℂ) * φ.val g)
    (T : (Σ _ : ℕ, ℕ) →
      (CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s))
    (hT : ∀ i u, (T i u : G → ℂ) =ᵐ[ν a b s] fun x ↦ ((polyWeightMask i (L x) : ℝ) : ℂ) * u x) :
    ContinuousLinearMap.adjoint (hardySobolevTestAction μ m a b s hab hs φ' :
        CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s) =
      ∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) •
        (T i).comp (hardySobolevTestAction μ m a b s hab hs (Φ (i.1 + i.2))) := by
  let A' : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs φ'
  let B (e : ℕ) : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs (Φ e)
  let w (x : G) : ℝ := intervalSobolevDensity a b s (L x)
  have hL : Continuous L := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    m.continuous)).log fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hD : Continuous (intervalSobolevDensity a b s) := by
    rw [show intervalSobolevDensity a b s = fun t ↦ (1 + t ^ 2) ^ n from funext hw]
    fun_prop
  have hwc : Continuous w := hD.comp hL
  have hwx (x : G) : w x = (1 + L x ^ 2) ^ n := hw (L x)
  have hwpos (x : G) : 0 < w x := by rw [hwx]; positivity
  have hν : ν a b s = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := rfl
  let : IsLocallyFiniteMeasure (ν a b s) := hν ▸ IsLocallyFiniteMeasure.withDensity_ofReal hwc
  have hLmul (g h : G) : L (g * h) = L g + L h := by
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m g).ne_zero) (NNReal.coe_ne_zero.2 (m h).ne_zero)]
  have hLinv (g : G) : L g⁻¹ = -L g := by
    dsimp only
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  change A'.adjoint = ∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) •
    (T i).comp (B (i.1 + i.2))
  apply DFunLike.coe_injective
  apply Continuous.ext_on (dense_compactCore' (ν a b s)) A'.adjoint.continuous
    (ContinuousLinearMap.continuous _)
  rintro u ⟨f, hf, hfc, hu⟩
  apply Lp.ext
  have h1 := (hardySobolevTestAction_compact_kernels μ m a b s hab hs φ' u f hf hfc hu).2
  have h2 (e : ℕ) := (hardySobolevTestAction_compact_kernels μ m a b s hab hs (Φ e) u f hf hfc hu).1
  have hR : (((∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) •
      (T i).comp (B (i.1 + i.2))) u : CompactIntervalSobolev μ L a b s) : G → ℂ) =ᵐ[ν a b s]
      fun x ↦ ∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) *
        (((polyWeightMask i (L x) : ℝ) : ℂ) *
          ∫ y, (Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y ∂(ν a b s)) := by
    rw [FunLike.coe_sum, Finset.sum_apply]
    refine coeFn_finset_sum_ae (ν a b s) _ _ _ fun i _ ↦ ?_
    change ((((polyWeightCoeff n i : ℕ) : ℂ) • (T i (B (i.1 + i.2) u)) :
      CompactIntervalSobolev μ L a b s) : G → ℂ) =ᵐ[ν a b s] _
    filter_upwards [Lp.coeFn_smul ((polyWeightCoeff n i : ℕ) : ℂ) (T i (B (i.1 + i.2) u)),
      hT i (B (i.1 + i.2) u), h2 (i.1 + i.2)] with x hx1 hx2 hx3
    rw [hx1, Pi.smul_apply, smul_eq_mul, hx2, hx3]
  refine h1.trans (EventuallyEq.trans (.of_forall fun x ↦ ?_) hR.symm)
  have hint (e : ℕ) : Integrable (fun y ↦ (Φ e).val (x * y⁻¹) / (w y : ℂ) * f y) (ν a b s) := by
    have hΦc : Continuous (Φ e).val :=
      continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp (Φ e).property.1)
    have hcont : Continuous (fun y ↦ (Φ e).val (x * y⁻¹) / (w y : ℂ) * f y) :=
      ((hΦc.comp (continuous_const.mul continuous_inv)).div
        (Complex.continuous_ofReal.comp hwc)
        fun y ↦ Complex.ofReal_ne_zero.mpr (hwpos y).ne').mul hf
    exact hcont.integrable_of_hasCompactSupport hfc.mul_left
  change (∫ y, star (φ'.val (y * x⁻¹)) / (w x : ℂ) * f y ∂(ν a b s)) = _
  have hsum : (∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) *
      (((polyWeightMask i (L x) : ℝ) : ℂ) *
        ∫ y, (Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y ∂(ν a b s))) =
      ∫ y, ∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) *
        (((polyWeightMask i (L x) : ℝ) : ℂ) *
          ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y)) ∂(ν a b s) := by
    rw [integral_finsetSum _ fun i _ ↦ ((hint (i.1 + i.2)).const_mul _).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, integral_const_mul]
  rw [hsum]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  dsimp only
  have hstar : star (φ'.val (y * x⁻¹)) = φ.val (x * y⁻¹) := by
    rw [hφ', star_star, mul_inv_rev, inv_inv]
  have hLy : L x + -L (x * y⁻¹) = L y := by
    rw [hLmul, hLinv]
    ring
  have hexp := one_add_sq_add_pow n (L x) (-L (x * y⁻¹))
  rw [hLy, ← hwx y, ← hwx x] at hexp
  have hwxne : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos x).ne'
  have hwyne : (w y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos y).ne'
  have hterm (i : Σ _ : ℕ, ℕ) : ((polyWeightCoeff n i : ℕ) : ℂ) *
      (((polyWeightMask i (L x) : ℝ) : ℂ) * ((Φ (i.1 + i.2)).val (x * y⁻¹) / (w y : ℂ) * f y)) =
      (φ.val (x * y⁻¹) / (w y : ℂ) * f y) *
        (((polyWeightCoeff n i : ℝ) * polyWeightMask i (L x) *
          (-L (x * y⁻¹)) ^ (i.1 + i.2) : ℝ) : ℂ) := by
    rw [hΦ]
    push_cast
    ring
  rw [hstar, Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have hratio : (∑ i ∈ polyWeightIndex n, (polyWeightCoeff n i : ℝ) * polyWeightMask i (L x) *
      (-L (x * y⁻¹)) ^ (i.1 + i.2)) = w y / w x := by
    rw [eq_div_iff (hwpos x).ne', mul_comm, ← hexp]
  rw [hratio, Complex.ofReal_div]
  field_simp

/-- The identity of `hardySobolevTestAction_adjoint_eq_sum_polyWeight` solved for convolution by
`φ`: it is the adjoint of convolution by the reflected conjugate, minus the terms of the pairs
other than `(0, 0)`. -/
theorem hardySobolevTestAction_eq_adjoint_sub_sum_polyWeight (a b s : ℝ) (hab : a ≤ b)
    (hs : 0 ≤ s) (n : ℕ) (hw : ∀ t, intervalSobolevDensity a b s t = (1 + t ^ 2) ^ n)
    (φ φ' : BruhatCompactSupport G) (hφ' : ∀ g, φ'.val g = star (φ.val g⁻¹))
    (Φ : ℕ → BruhatCompactSupport G)
    (hΦ : ∀ e g, (Φ e).val g = (((-Real.log ((m g).val : ℝ)) ^ e : ℝ) : ℂ) * φ.val g)
    (T : (Σ _ : ℕ, ℕ) →
      (CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s))
    (hT : ∀ i u, (T i u : G → ℂ) =ᵐ[ν a b s] fun x ↦ ((polyWeightMask i (L x) : ℝ) : ℂ) * u x) :
    (hardySobolevTestAction μ m a b s hab hs φ :
        CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s) =
      ContinuousLinearMap.adjoint (hardySobolevTestAction μ m a b s hab hs φ' :
        CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s) -
      ∑ i ∈ (polyWeightIndex n).erase ⟨0, 0⟩, ((polyWeightCoeff n i : ℕ) : ℂ) •
        (T i).comp (hardySobolevTestAction μ m a b s hab hs (Φ (i.1 + i.2))) := by
  let Aφ : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs φ
  let A' : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs φ'
  let B (e : ℕ) : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    hardySobolevTestAction μ m a b s hab hs (Φ e)
  let rest : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
    ∑ i ∈ (polyWeightIndex n).erase ⟨0, 0⟩, ((polyWeightCoeff n i : ℕ) : ℂ) •
      (T i).comp (B (i.1 + i.2))
  have hadj : A'.adjoint = ∑ i ∈ polyWeightIndex n, ((polyWeightCoeff n i : ℕ) : ℂ) •
      (T i).comp (B (i.1 + i.2)) :=
    hardySobolevTestAction_adjoint_eq_sum_polyWeight μ m a b s hab hs n hw φ φ' hφ' Φ hΦ T hT
  have h00 : (⟨0, 0⟩ : Σ _ : ℕ, ℕ) ∈ polyWeightIndex n := by
    simp [polyWeightIndex]
  have hT0 : T ⟨0, 0⟩ = ContinuousLinearMap.id ℂ (CompactIntervalSobolev μ L a b s) := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    refine (hT ⟨0, 0⟩ u).trans (.of_forall fun x ↦ ?_)
    simp [polyWeightMask]
  have hΦ0 : Φ (0 + 0) = φ := Subtype.ext (funext fun g ↦ by rw [hΦ]; simp)
  have hc0 : polyWeightCoeff n ⟨0, 0⟩ = 1 := by simp [polyWeightCoeff]
  have hB0 : B (0 + 0) = Aφ := congrArg (fun ψ ↦
    (hardySobolevTestAction μ m a b s hab hs ψ :
      CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s)) hΦ0
  have hfirst : ((polyWeightCoeff n ⟨0, 0⟩ : ℕ) : ℂ) • (T ⟨0, 0⟩).comp (B (0 + 0)) = Aφ := by
    rw [hc0, Nat.cast_one, one_smul, hT0, hB0]
    exact ContinuousLinearMap.id_comp Aφ
  rw [← Finset.add_sum_erase _ _ h00] at hadj
  have h2 : A'.adjoint = Aφ + rest := hadj.trans (congrArg (fun X ↦ X + rest) hfirst)
  exact eq_sub_of_add_eq h2.symm

/-- Convolutions by a test times powers of minus the logarithm of the modulation have norms at
most a constant times the powers of a bound `δ` for the logarithm on the support of the test.
The convolution is the Bochner integral of the translations, and the translations are bounded
uniformly on the compact support, by the Banach–Steinhaus theorem. -/
theorem exists_hardySobolevTestAction_logPow_norm_le (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (Φ : ℕ → BruhatCompactSupport G)
    (hΦ : ∀ e g, (Φ e).val g = (((-Real.log ((m g).val : ℝ)) ^ e : ℝ) : ℂ) * φ.val g)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsupp : ∀ g, φ.val g ≠ 0 → |Real.log ((m g).val : ℝ)| ≤ δ) :
    ∃ M₀ : ℝ, ∀ e,
      let A : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
        hardySobolevTestAction μ m a b s hab hs (Φ e)
      ‖A‖ ≤ M₀ * δ ^ e := by
  let τ := hardySobolevTranslation μ m a b s hab hs
  have hτ : Continuous (fun p : G × CompactIntervalSobolev μ L a b s ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2
  have hφc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨C, hC⟩ : ∃ C, ∀ g : tsupport φ.val, ‖τ g‖ ≤ C := by
    apply banach_steinhaus
    intro u
    have hcont : Continuous (fun g : G ↦ τ g u) := hτ.comp (Continuous.prodMk_left u)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨C, fun g ↦ hC g g.property⟩
  have hi : Integrable φ.val μ := hφc.integrable_of_hasCompactSupport φ.property.2
  refine ⟨max C 0 * ∫ g, ‖φ.val g‖ ∂μ, fun e ↦ ?_⟩
  intro A
  refine A.opNorm_le_bound (mul_nonneg (mul_nonneg (le_max_right _ _)
    (integral_nonneg fun _ ↦ norm_nonneg _)) (pow_nonneg hδ e)) fun u ↦ ?_
  have hΦc : Continuous (Φ e).val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp (Φ e).property.1)
  have hie : Integrable (Φ e).val μ := hΦc.integrable_of_hasCompactSupport (Φ e).property.2
  rw [hardySobolev_eq_integral_translation_of_convolution μ m a b s hab hs hie (Φ e).property.2 A
    (hardySobolevTestAction_apply μ m a b s hab hs (Φ e)) u]
  refine (norm_integral_le_of_norm_le (hi.norm.const_mul (max C 0 * δ ^ e * ‖u‖))
    (.of_forall fun g ↦ ?_)).trans_eq ?_
  · by_cases hg : φ.val g = 0
    · simp [hΦ, hg]
    · have hmem : g ∈ tsupport φ.val := subset_tsupport _ hg
      have h1 : |Real.log ((m g).val : ℝ)| ^ e ≤ δ ^ e :=
        pow_le_pow_left₀ (abs_nonneg _) (hsupp g hg) e
      have h2 : ‖τ g u‖ ≤ max C 0 * ‖u‖ := ((τ g).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right ((hC ⟨g, hmem⟩).trans (le_max_left _ _)) (norm_nonneg _))
      rw [norm_smul, hΦ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg]
      calc |Real.log ((m g).val : ℝ)| ^ e * ‖φ.val g‖ * ‖τ g u‖
          ≤ δ ^ e * ‖φ.val g‖ * (max C 0 * ‖u‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (norm_nonneg _)
              (mul_nonneg (pow_nonneg hδ e) (norm_nonneg _))
        _ = max C 0 * δ ^ e * ‖u‖ * ‖φ.val g‖ := by ring
  · rw [integral_const_mul]
    ring

end AdjointIdentity

end RiemannMasullo.WeightedConvolution
