module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.SeparatedTaylor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite masked kernels for the weighted adjoint of compact test convolution

The density in (9.2.1.30), p. 410, on the symmetric interval is an exponential
in the absolute log norm times a polynomial weight. Two compact tests on each tail
realize the constant and linear terms of the ratio of the two densities. The scalar Taylor defect
has a finite expansion into products of square-integrable functions on the log line.
Lifting each factor by the inverse square root of the density places the actual masks
in the Hardy–Sobolev space. The part where the signs of the log norms can differ has
compact support in both variables.

For (10.4.3.45), p. 473, the pointwise identity is relative to the weighted measure.
Each of the four correction terms applies a bounded multiplier after the adjoint convolution.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators ContDiff

namespace RiemannMasullo.WeightedConvolution

private theorem normalized_identity (a b u v e : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    1 / (b * v) ^ 2 - (a / b) ^ 2 * (1 + e) / (a * u) ^ 2 =
      (a / b) / ((a * u) * (b * v)) * ((u ^ 2 - v ^ 2 - e * v ^ 2) / (u * v)) := by
  field_simp
  ring

/-- On one logarithmic end the weighted residual is the normalized
polynomial Taylor defect between two reciprocal square-root density factors. -/
private theorem end_density_identity (p w : ℝ → ℝ) (x y c d : ℝ)
    (hpx : 0 < p x) (hpy : 0 < p y)
    (hwx : w x = Real.exp (2 * c * x) * p x)
    (hwy : w y = Real.exp (2 * c * y) * p y) :
    1 / w y - Real.exp (2 * c * (x - y)) * (1 + d * (x - y)) / w x =
      Real.exp (c * (x - y)) / (Real.sqrt (w x) * Real.sqrt (w y)) *
        ((p x - p y - d * (x - y) * p y) / Real.sqrt (p x * p y)) := by
  let a := Real.exp (c * x)
  let b := Real.exp (c * y)
  let u := Real.sqrt (p x)
  let v := Real.sqrt (p y)
  have hpolyX : u ^ 2 = p x := Real.sq_sqrt hpx.le
  have hpolyY : v ^ 2 = p y := Real.sq_sqrt hpy.le
  have hX : (a * u) ^ 2 = w x := by
    rw [mul_pow, hpolyX, hwx]
    congr 1
    dsimp only [a]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hY : (b * v) ^ 2 = w y := by
    rw [mul_pow, hpolyY, hwy]
    congr 1
    dsimp only [b]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsx : Real.sqrt (w x) = a * u := by
    rw [← hX, Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))]
  have hsy : Real.sqrt (w y) = b * v := by
    rw [← hY, Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))]
  have he : Real.exp (c * (x - y)) = a / b := by rw [mul_sub, Real.exp_sub]
  have he₂ : Real.exp (2 * c * (x - y)) = (a / b) ^ 2 := by
    rw [← he, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, he₂, hsx, hsy, ← hX, ← hY, Real.sqrt_mul hpx.le]
  change 1 / (b * v) ^ 2 - (a / b) ^ 2 * (1 + d * (x - y)) / (a * u) ^ 2 =
    (a / b) / ((a * u) * (b * v)) * ((p x - p y - d * (x - y) * p y) / (u * v))
  rw [← hpolyX, ← hpolyY]
  exact normalized_identity a b u v _ (Real.exp_pos _).ne' (Real.exp_pos _).ne'
    (Real.sqrt_pos.2 hpx).ne' (Real.sqrt_pos.2 hpy).ne'

/-- A finite separated expansion of the polynomial defect produces the
weighted end kernel, including both adjoint corrections and the complex test. -/
private theorem end_kernel_finite {ι : Type*} [Fintype ι]
    (p w : ℝ → ℝ) (x y c d : ℝ) (φ : ℂ) (A B : ι → ℝ)
    (hpx : 0 < p x) (hpy : 0 < p y)
    (hwx : w x = Real.exp (2 * c * x) * p x) (hwy : w y = Real.exp (2 * c * y) * p y)
    (hsum : ∑ i, A i * B i = (p x - p y - d * (x - y) * p y) / Real.sqrt (p x * p y)) :
    φ / (w y : ℂ) -
      (((Real.exp (2 * c * (x - y)) : ℝ) : ℂ) * φ / (w x : ℂ) +
        (d : ℂ) * ((((x - y) * Real.exp (2 * c * (x - y)) : ℝ) : ℂ) * φ) / (w x : ℂ)) =
      ∑ i, (((A i / Real.sqrt (w x) : ℝ) : ℂ) *
        (((Real.exp (c * (x - y)) : ℝ) : ℂ) * φ) *
        ((B i / Real.sqrt (w y) : ℝ) : ℂ)) := by
  have h := end_density_identity p w x y c d hpx hpy hwx hwy
  rw [← hsum] at h
  calc
    _ = ((1 / w y - Real.exp (2 * c * (x - y)) * (1 + d * (x - y)) / w x : ℝ) : ℂ) * φ := by
      push_cast
      ring
    _ = ((Real.exp (c * (x - y)) / (Real.sqrt (w x) * Real.sqrt (w y)) *
        (∑ i, A i * B i) : ℝ) : ℂ) * φ := by rw [h]
    _ = _ := by
      rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring

/-- Positive or negative exponential rate on the corresponding logarithmic end. -/
private def sideRate (positive : Bool) (α : ℝ) : ℝ := if positive then α else -α

/-- Characteristic function of one of the two tails. -/
private def tailCut (positive : Bool) (R x : ℝ) : ℝ :=
  if positive then if R < x then 1 else 0 else if x < -R then 1 else 0

/-- Characteristic function of a compact central interval. -/
private def centerCut (R x : ℝ) : ℝ := if |x| ≤ R then 1 else 0

/-- Scalar correction multiplying the adjoint of the constant or linear paired test. -/
private def adjointCoefficient (R : ℝ) (d : ℝ → ℝ) (i : Bool × Bool) (x : ℝ) : ℝ :=
  tailCut i.1 R x * (if i.2 then d x else 1)

/-- Logarithmic profile of the paired compact test after reflection and conjugation. -/
private def pairedProfile (α : ℝ) (i : Bool × Bool) (t : ℝ) : ℝ :=
  (if i.2 then t else 1) * Real.exp (2 * sideRate i.1 α * t)

/-- Left multiplier in each of the masked convolutions on the tails. -/
private def tailLeft {ι : Type*} (R : ℝ) (w : ℝ → ℝ) (A : ι → ℝ → ℝ)
    (i : Bool × ι) (x : ℝ) : ℝ := tailCut i.1 R x * (A i.2 x / Real.sqrt (w x))

/-- Right multiplier in each of the masked convolutions on the tails. -/
private def tailRight {ι : Type*} (w : ℝ → ℝ) (B : ι → ℝ → ℝ)
    (i : Bool × ι) (y : ℝ) : ℝ := B i.2 y / Real.sqrt (w y)

/-- Exact scalar identity including the compact center and both boundary points. The test
value can be complex and can have arbitrary angular dependence. -/
private theorem finite_kernel_radial {ι : Type*} [Fintype ι] (R α : ℝ) (hR : 0 ≤ R)
    (p w d : ℝ → ℝ) (hp : ∀ z, 0 < p z)
    (hw : ∀ z, w z = Real.exp (2 * α * |z|) * p z) (A B : ι → ℝ → ℝ)
    (hsum : ∀ x y, |x - y| ≤ R → ∑ i, A i x * B i y =
      (p x - p y - d x * (x - y) * p y) / Real.sqrt (p x * p y))
    (x y : ℝ) (φ : ℂ) (hφ : φ ≠ 0 → |x - y| ≤ R) :
    φ / (w y : ℂ) -
      ∑ i : Bool × Bool, (adjointCoefficient R d i x : ℂ) *
        ((pairedProfile α i (x - y) : ℂ) * φ) / (w x : ℂ) =
      (centerCut R x : ℂ) * φ * ((centerCut (2 * R) y / w y : ℝ) : ℂ) +
      ∑ i : Bool × ι, (tailLeft R w A i x : ℂ) *
        ((Real.exp (sideRate i.1 α * (x - y)) : ℂ) * φ) * (tailRight w B i y : ℂ) := by
  classical
  by_cases hz : φ = 0
  · simp [hz]
  have hxy := hφ hz
  obtain ⟨hmin, hmax⟩ := abs_le.mp hxy
  by_cases hplus : R < x
  · have hx : 0 ≤ x := hR.trans hplus.le
    have hy : 0 ≤ y := by linarith
    have hn : ¬ x < -R := by linarith
    have hc : ¬ |x| ≤ R := by simpa [abs_of_nonneg hx] using hplus.not_ge
    have he := end_kernel_finite p w x y α (d x) φ (fun i ↦ A i x) (fun i ↦ B i y)
      (hp x) (hp y) (by simpa [abs_of_nonneg hx] using hw x)
      (by simpa [abs_of_nonneg hy] using hw y) (hsum x y hxy)
    simpa [Fintype.sum_prod_type, Fintype.sum_bool, adjointCoefficient, pairedProfile,
      tailLeft, tailRight, sideRate, tailCut, centerCut, hplus, hn, hc, add_comm] using he
  by_cases hminus : x < -R
  · have hx : x ≤ 0 := by linarith
    have hy : y ≤ 0 := by linarith
    have hc : ¬ |x| ≤ R := by rw [abs_of_nonpos hx]; linarith
    have her (z : ℝ) (hz' : z ≤ 0) :
        w z = Real.exp (2 * (-α) * z) * p z := by
      rw [hw, abs_of_nonpos hz']
      ring_nf
    have he := end_kernel_finite p w x y (-α) (d x) φ (fun i ↦ A i x) (fun i ↦ B i y)
      (hp x) (hp y) (her x hx) (her y hy) (hsum x y hxy)
    simpa [Fintype.sum_prod_type, Fintype.sum_bool, adjointCoefficient, pairedProfile,
      tailLeft, tailRight, sideRate, tailCut, centerCut, hplus, hminus, hc, add_comm] using he
  have hc : |x| ≤ R := abs_le.mpr ⟨le_of_not_gt hminus, le_of_not_gt hplus⟩
  have hcy : |y| ≤ 2 * R := abs_le.mpr ⟨by linarith [(abs_le.mp hc).1], by linarith [(abs_le.mp hc).2]⟩
  simp [adjointCoefficient, tailLeft, tailCut,
    centerCut, hplus, hminus, hc, hcy, div_eq_mul_inv]

private theorem tailCut_measurable (σ : Bool) (R : ℝ) : Measurable (tailCut σ R) := by
  cases σ
  · change Measurable (fun x : ℝ ↦ if x < -R then (1 : ℝ) else 0)
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  · change Measurable (fun x : ℝ ↦ if R < x then (1 : ℝ) else 0)
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

private theorem abs_tailCut_le_one (σ : Bool) (R x : ℝ) : |tailCut σ R x| ≤ 1 := by
  cases σ <;> simp only [tailCut, Bool.false_eq_true, ↓reduceIte] <;>
    split <;> norm_num

private theorem coefficient_measurable (R : ℝ) (d : ℝ → ℝ) (hd : Measurable d)
    (i : Bool × Bool) : Measurable (adjointCoefficient R d i) := by
  rcases i with ⟨σ, j⟩
  cases j
  · exact (tailCut_measurable σ R).mul measurable_const
  · exact (tailCut_measurable σ R).mul hd

private theorem coefficient_bound (R : ℝ) (d : ℝ → ℝ) (K : ℝ)
    (hb : ∀ z, |d z| ≤ K) (i : Bool × Bool) (z : ℝ) :
    |adjointCoefficient R d i z| ≤ max 1 K := by
  rcases i with ⟨σ, j⟩
  cases j
  · simpa [adjointCoefficient] using (abs_tailCut_le_one σ R z).trans (le_max_left 1 K)
  · simp only [adjointCoefficient, ↓reduceIte, abs_mul]
    exact ((mul_le_mul_of_nonneg_right (abs_tailCut_le_one σ R z) (abs_nonneg (d z))).trans_eq
      (one_mul _)).trans ((hb z).trans (le_max_right 1 K))

/-- A bounded measurable complex function acts on weighted L² by multiplication. -/
private theorem exists_complexMultiplier {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (s : X → ℂ) (hs : AEStronglyMeasurable s ν) (C : ℝ) (hb : ∀ x, ‖s x‖ ≤ C) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ u, (T u : X → ℂ) =ᵐ[ν] fun x ↦ s x * u x := by
  let h : MemLp s ∞ ν := memLp_top_of_bound hs C (.of_forall hb)
  let mul := ContinuousLinearMap.mul ℂ ℂ
  exact ⟨mul.holderL ν ∞ 2 2 (h.toLp s), fun u ↦
    (mul.coeFn_holder (r := 2) (h.toLp s) u).trans
      (h.coeFn_toLp.mono fun x hx ↦ congrArg (· * u x) hx)⟩

private theorem isBruhatContDiff_conj_inv {G : Type*} [CommGroup G] [TopologicalSpace G]
    {f : G → ℂ} {p : ℕ} (h : IsBruhatContDiff p f) :
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

/-- The same compact Bruhat test can be multiplied by any smooth logarithmic
profile. Only the support of the original test is required to be compact. -/
private def bruhatCompactSupport_mul_logProfile {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G) (r : ℝ → ℂ) (hr : ContDiff ℝ ∞ r) :
    BruhatCompactSupport G :=
  ⟨fun g ↦ r (Real.log ((m g).val : ℝ)) * φ.val g, (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
    isBruhatContDiff_mul (isBruhatSmooth_logProfile m hr p) ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (show HasCompactSupport φ.val from φ.property.2).mul_left⟩

/-- The compact Bruhat test paired with a smooth logarithmic multiplier under
the Haar adjoint. Inversion preserves the compact support and descends to
negation in each elementary real/torus chart. -/
private theorem exists_bruhatCompactSupport_conj_inv_logProfile {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G) (r : ℝ → ℂ) (hr : ContDiff ℝ ∞ r) :
    ∃ ψ : BruhatCompactSupport G, ∀ g, star (ψ.val g⁻¹) = r (Real.log ((m g).val : ℝ)) * φ.val g := by
  let v := bruhatCompactSupport_mul_logProfile m φ r hr
  have hv := (mem_bruhatSmoothSubmodule_iff _).mp v.property.1
  have hc : HasCompactSupport v.val := v.property.2
  let ψ : BruhatCompactSupport G := ⟨fun x ↦ star (v.val x⁻¹),
    (mem_bruhatSmoothSubmodule_iff _).mpr (fun p ↦ isBruhatContDiff_conj_inv (hv p)),
    (hc.comp_homeomorph (Homeomorph.inv G)).comp_left (star_zero ℂ)⟩
  refine ⟨ψ, fun g ↦ ?_⟩
  change star (star (v.val (g⁻¹)⁻¹)) = v.val g
  simp only [inv_inv, star_star]

/-- In particular the paired tests exist for the factors $t^k \exp(bt)$, including
the constant and linear Taylor coefficients on either logarithmic tail. -/
private theorem exists_bruhatCompactSupport_conj_inv_logPow_exp {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G) (k : ℕ) (b : ℝ) :
    ∃ ψ : BruhatCompactSupport G, ∀ g,
      star (ψ.val g⁻¹) =
        ((Real.log ((m g).val : ℝ) ^ k * Real.exp (b * Real.log ((m g).val : ℝ)) : ℝ) : ℂ) * φ.val g := by
  apply exists_bruhatCompactSupport_conj_inv_logProfile m φ
    (fun t ↦ ((t ^ k * Real.exp (b * t) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow k).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The logarithm of a surjective modulation is proper and pushes Haar measure forward
to a scalar multiple of Lebesgue measure. -/
private theorem proper_measurePreserving_logModulation
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] :
    IsProperMap (fun x : G ↦ Real.log ((m x).val : ℝ)) ∧
      ∃ c : ℝ≥0, MeasurePreserving (fun x ↦ Real.log ((m x).val : ℝ))
      μ (c • (volume : Measure ℝ)) := by
  let ν : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : ν.IsHaarMeasure := by
    let : IsFiniteMeasureOnCompacts ν :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    let : Measure.IsOpenPosMeasure ν :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    let : ν.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  let φ : G →* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (e (m x))
      map_one' := by change e (m 1) = 0; simp [he]
      map_mul' := fun x y ↦ by
        change e (m (x * y)) = e (m x) + e (m y)
        rw [he, map_mul, Units.val_mul, NNReal.coe_mul, he, he]
        exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' }
  have hproper : IsProperMap φ := e.isProperMap.comp hm.1
  let : (μ.map φ).IsHaarMeasure := Measure.isHaarMeasure_map μ φ hproper.continuous
    (e.surjective.comp hms) (isProperMap_iff_tendsto_cocompact.mp hproper).2
  have hφ : (φ : G → ℝ) = fun x ↦ Real.log ((m x).val : ℝ) := funext fun x ↦ he (m x)
  rw [← hφ]
  exact ⟨hproper, Measure.haarScalarFactor (μ.map φ) ν, hproper.continuous.measurable,
    Measure.isMulLeftInvariant_eq_smul (μ.map φ) ν⟩

private theorem squared_profile_memLp
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) {c : ℝ≥0}
    (hL : MeasurePreserving (fun x : G ↦ Real.log ((m x).val : ℝ)) μ (c • (volume : Measure ℝ)))
    (w : ℝ → ℝ) (hw : Continuous w) (hp : ∀ t, 0 < w t)
    (A : ℝ → ℝ) (hA : Measurable A) (hmem : MemLp A 2 volume) :
    let L := fun x : G ↦ Real.log ((m x).val : ℝ)
    MemLp (fun x ↦ ((A (L x) / Real.sqrt (w (L x)) : ℝ) : ℂ)) 2
      (μ.withDensity (fun x ↦ ENNReal.ofReal (w (L x)))) := by
  intro L
  have hm : Measurable L := hL.measurable
  have hmeas : Measurable (fun x ↦ ((A (L x) / Real.sqrt (w (L x)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((hA.comp hm).div
      (Real.continuous_sqrt.measurable.comp (hw.measurable.comp hm)))
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr
  apply (integrable_withDensity_iff_integrable_smul' (hw.measurable.comp hm).ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  have hi : Integrable (fun x ↦ A (L x) ^ 2) μ :=
    hL.integrable_comp_of_integrable hmem.integrable_sq.smul_measure_nnreal
  refine hi.congr (.of_forall fun x ↦ ?_)
  change A (L x) ^ 2 = (ENNReal.ofReal (w (L x))).toReal • ‖((A (L x) / Real.sqrt (w (L x)) : ℝ) : ℂ)‖^2
  rw [ENNReal.toReal_ofReal (hp _).le, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, div_pow, Real.sq_sqrt (hp _).le]
  field_simp [(hp _).ne']

private theorem memLp_compact_indicator {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    {S : Set X} (hS : IsCompact S) (f : X → ℂ) (hf : Continuous f) :
    MemLp (S.indicator f) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm
    (hf.measurable.indicator hS.isClosed.measurableSet).aestronglyMeasurable).mpr
  have heq : (fun x ↦ ‖S.indicator f x‖^2) = S.indicator (fun x ↦ ‖f x‖^2) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [heq]
  exact ((hf.norm.pow 2).continuousOn.integrableOn_compact hS).integrable_indicator hS.isClosed.measurableSet

private theorem exists_expTest (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G) (c : ℝ) :
    ∃ θ : BruhatCompactSupport G, ∀ g,
      θ.val g = (Real.exp (c * Real.log ((m g).val : ℝ)) : ℂ) * φ.val g := by
  let η (t : ℝ) : ℂ := (Real.exp (c * t) : ℝ)
  have hη : ContDiff ℝ ∞ η := Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact ⟨bruhatCompactSupport_mul_logProfile m φ η hη, fun _ ↦ rfl⟩

private theorem exists_pairedTest (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G)
    (α : ℝ) (i : Bool × Bool) :
    ∃ ψ : BruhatCompactSupport G, ∀ g, star (ψ.val g⁻¹) =
      (pairedProfile α i (Real.log ((m g).val : ℝ)) : ℂ) * φ.val g := by
  rcases i with ⟨σ, j⟩
  cases j
  · obtain ⟨ψ, hψ⟩ := exists_bruhatCompactSupport_conj_inv_logPow_exp m φ 0 (2 * sideRate σ α)
    exact ⟨ψ, fun g ↦ by simpa [pairedProfile] using hψ g⟩
  · obtain ⟨ψ, hψ⟩ := exists_bruhatCompactSupport_conj_inv_logPow_exp m φ 1 (2 * sideRate σ α)
    exact ⟨ψ, fun g ↦ by simpa [pairedProfile] using hψ g⟩

/-- Any finite separated expansion of the normalized scalar Taylor defect on the
propagation band produces an exact finite expansion of the actual weighted convolution
kernel, with four paired compact tests and square-integrable masks on both sides. -/
private theorem exists_finite_masked_symbols_of_scalar {ι : Type} [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
    (hm : IsModulation m) (hms : Surjective m) (φ : BruhatCompactSupport G)
    (R α : ℝ) (hR : 0 ≤ R)
    (hprop : ∀ g, φ.val g ≠ 0 → |Real.log ((m g).val : ℝ)| ≤ R)
    (p w d : ℝ → ℝ) (hp : ∀ z, 0 < p z) (hwc : Continuous w) (hwp : ∀ z, 0 < w z)
    (hw : ∀ z, w z = Real.exp (2 * α * |z|) * p z)
    (hd : Measurable d) (K : ℝ) (hdK : ∀ z, |d z| ≤ K)
    (A B : ι → ℝ → ℝ) (hABm : ∀ i, Measurable (A i) ∧ Measurable (B i))
    (hAB : ∀ i, MemLp (A i) 2 volume ∧ MemLp (B i) 2 volume)
    (hsum : ∀ x y, |x - y| ≤ R → ∑ i, A i x * B i y =
      (p x - p y - d x * (x - y) * p y) / Real.sqrt (p x * p y)) :
    let L := fun g : G ↦ Real.log ((m g).val : ℝ)
    let ν := μ.withDensity (fun g ↦ ENNReal.ofReal (w (L g)))
    ∃ (b : Bool × Bool → G → ℂ) (ψ : Bool × Bool → BruhatCompactSupport G)
      (M : Bool × Bool → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
      (θ : Option (Bool × ι) → BruhatCompactSupport G)
      (l r : Option (Bool × ι) → G → ℂ),
      (∀ i u, (M i u : G → ℂ) =ᵐ[ν] fun x ↦ b i x * u x) ∧
      (∀ j, MemLp (l j) 2 ν ∧ MemLp (r j) 2 ν) ∧
      ∀ x y, φ.val (x * y⁻¹) / (w (L y) : ℂ) -
        ∑ i, b i x * star ((ψ i).val (y * x⁻¹)) / (w (L x) : ℂ) =
        ∑ j, l j x * (θ j).val (x * y⁻¹) * star (r j y) := by
  classical
  intro L ν
  obtain ⟨hproper, c, hpres⟩ := proper_measurePreserving_logModulation m hm hms μ
  have hL : Continuous L := hproper.continuous
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal (hwc.comp hL)
  have hcompact (r : ℝ) : IsCompact {g : G | |L g| ≤ r} := by
    have hset : {g : G | |L g| ≤ r} = L ⁻¹' Icc (-r) r :=
      Set.ext (fun x ↦ by change |L x| ≤ r ↔ -r ≤ L x ∧ L x ≤ r; exact abs_le)
    rw [hset]
    exact hproper.isCompact_preimage isCompact_Icc
  have hLdiv (x y : G) : L (x * y⁻¹) = L x - L y := by
    dsimp only [L]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m x).ne_zero) (NNReal.coe_ne_zero.2 (m y⁻¹).ne_zero)]
    simp [sub_eq_add_neg]
  choose ψ hψ using exists_pairedTest m φ α
  choose η hη using fun σ ↦ exists_expTest m φ (sideRate σ α)
  let b (i : Bool × Bool) (x : G) : ℂ := adjointCoefficient R d i (L x)
  have hM (i : Bool × Bool) := exists_complexMultiplier ν (b i)
    (Complex.measurable_ofReal.comp ((coefficient_measurable R d hd i).comp hL.measurable)).aestronglyMeasurable
    (max 1 K)
    (fun x ↦ by simpa [b, Real.norm_eq_abs] using coefficient_bound R d K hdK i (L x))
  choose M hMb using hM
  let θ : Option (Bool × ι) → BruhatCompactSupport G := fun j ↦ j.elim φ (fun i ↦ η i.1)
  let l : Option (Bool × ι) → G → ℂ := fun j x ↦
    j.elim ((centerCut R (L x) : ℝ) : ℂ) (fun i ↦ (tailLeft R w A i (L x) : ℂ))
  let r : Option (Bool × ι) → G → ℂ := fun j y ↦
    j.elim ((centerCut (2 * R) (L y) / w (L y) : ℝ) : ℂ) (fun i ↦ (tailRight w B i (L y) : ℂ))
  refine ⟨b, ψ, M, θ, l, r, hMb, ?_, ?_⟩
  · rintro (_ | ⟨σ, i⟩)
    · have hleft := memLp_compact_indicator ν (hcompact R) (fun _ ↦ (1 : ℂ)) continuous_const
      have hright := memLp_compact_indicator ν (hcompact (2 * R)) (fun g ↦ (((w (L g))⁻¹ : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp ((hwc.comp hL).inv₀ fun g ↦ (hwp _).ne'))
      constructor
      · refine MemLp.ae_eq ?_ hleft
        refine .of_forall fun g ↦ ?_
        change {x : G | |L x| ≤ R}.indicator (fun _ ↦ (1 : ℂ)) g = (centerCut R (L g) : ℂ)
        by_cases h : |L g| ≤ R <;> simp [Set.indicator, centerCut, h]
      · refine MemLp.ae_eq ?_ hright
        refine .of_forall fun g ↦ ?_
        change {x : G | |L x| ≤ 2 * R}.indicator (fun z ↦ (((w (L z))⁻¹ : ℝ) : ℂ)) g =
          ((centerCut (2 * R) (L g) / w (L g) : ℝ) : ℂ)
        by_cases h : |L g| ≤ 2 * R <;> simp [Set.indicator, centerCut, h]
    · constructor
      · have hmA : Measurable (fun t ↦ tailCut σ R t * A i t) := (tailCut_measurable σ R).mul (hABm i).1
        have hsize (t : ℝ) : ‖tailCut σ R t * A i t‖ ≤ ‖A i t‖ := by
          rw [norm_mul, Real.norm_eq_abs (tailCut σ R t)]
          exact (mul_le_mul_of_nonneg_right (abs_tailCut_le_one σ R t) (norm_nonneg _)).trans_eq (one_mul _)
        have hmem := (hAB i).1.mono hmA.aestronglyMeasurable (.of_forall hsize)
        refine MemLp.ae_eq ?_ (squared_profile_memLp μ m hpres w hwc hwp _ hmA hmem)
        exact .of_forall fun x ↦ by simp [l, tailLeft, L, mul_div_assoc]
      · exact squared_profile_memLp μ m hpres w hwc hwp (B i) (hABm i).2 (hAB i).2
  · intro x y
    have hval (i : Bool × Bool) : star ((ψ i).val (y * x⁻¹)) =
        (pairedProfile α i (L x - L y) : ℂ) * φ.val (x * y⁻¹) := by
      have hi := hψ i (x * y⁻¹)
      change star ((ψ i).val (x * y⁻¹)⁻¹) = (pairedProfile α i (L (x * y⁻¹)) : ℂ) * _ at hi
      simpa only [mul_inv_rev, inv_inv, hLdiv] using hi
    have hvalη (σ : Bool) : (η σ).val (x * y⁻¹) =
        (Real.exp (sideRate σ α *(L x - L y)) : ℂ) * φ.val (x * y⁻¹) := by
      rw [← hLdiv]
      exact hη σ (x * y⁻¹)
    have hr := finite_kernel_radial R α hR p w d hp hw A B hsum (L x) (L y) (φ.val (x * y⁻¹))
      (fun ht ↦ (hLdiv x y) ▸ hprop _ ht)
    rw [Fintype.sum_option]
    simp only [hval, θ, l, r, Option.elim_none, Option.elim_some, hvalη,
      Complex.star_def, Complex.conj_ofReal]
    exact hr

private theorem symmetric_density (α s : ℝ) (hα : 0 ≤ α) (x : ℝ) :
    intervalSobolevDensity (-α) α s x =
      Real.exp (2 * α * |x|) * TranslationWeight.polynomialWeight s x := by
  unfold intervalSobolevDensity TranslationWeight.polynomialWeight
  congr 1
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα hx])
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx']))]
    congr 1
    ring

private theorem abs_logSlope_le (s z : ℝ) : |s * z / (1 + z ^ 2)| ≤ |s| := by
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + z ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 1 + z ^ 2)).mpr
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_abs z, sq_nonneg (|z| - 1)]) (abs_nonneg s)

/-- Every compact Bruhat test admits four compact paired tests and a finite family of genuine
square-integrable masks for the symmetric compact-interval Sobolev density. The four bounded
multipliers act on the output. The identity holds pointwise against weighted measure. -/
theorem exists_finite_weighted_adjoint_data (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m) (α s : ℝ) (hα : 0 ≤ α)
    (φ : BruhatCompactSupport G) :
    let L := fun g : G ↦ Real.log ((m g).val : ℝ)
    let w := intervalSobolevDensity (-α) α s
    let ν := intervalSobolevMeasure μ L (-α) α s
    ∃ (J : Type) (_ : Fintype J) (b : Bool × Bool → G → ℂ)
      (ψ : Bool × Bool → BruhatCompactSupport G)
      (M : Bool × Bool → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
      (θ : J → BruhatCompactSupport G) (l r : J → G → ℂ),
      (∀ i u, (M i u : G → ℂ) =ᵐ[ν] fun x ↦ b i x * u x) ∧
      (∀ j, MemLp (l j) 2 ν ∧ MemLp (r j) 2 ν) ∧
      ∀ x y, φ.val (x * y⁻¹) / (w (L y) : ℂ) -
        ∑ i, b i x * star ((ψ i).val (y * x⁻¹)) / (w (L x) : ℂ) =
        ∑ j, l j x * (θ j).val (x * y⁻¹) * star (r j y) := by
  classical
  intro L w ν
  have hL : Continuous L := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun g ↦ NNReal.coe_ne_zero.mpr (m g).ne_zero
  obtain ⟨C, hC⟩ := φ.property.2.exists_bound_of_continuousOn hL.continuousOn
  let R := max 0 C
  have hprop (g : G) (hg : φ.val g ≠ 0) : |L g| ≤ R := by
    have h := hC g (subset_tsupport φ.val hg)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  obtain ⟨ι, hι, A, B, hABm, hAB, -, hsum⟩ := TranslationWeight.exists_finite_polynomialWeight_masks s R
  have hwc : Continuous w := by
    unfold w intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
    positivity
  have hwp (z : ℝ) : 0 < w z :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hk := exists_finite_masked_symbols_of_scalar μ m hm hms φ R α (le_max_left _ _) hprop
    (TranslationWeight.polynomialWeight s) w (fun z ↦ s * z / (1 + z ^ 2))
    (fun z ↦ Real.rpow_pos_of_pos (by positivity : 0 < 1 + z ^ 2) _) hwc hwp (symmetric_density α s hα)
    (by fun_prop) |s| (abs_logSlope_le s) A B hABm hAB hsum
  exact ⟨Option (Bool × ι), inferInstance, hk⟩

end RiemannMasullo.WeightedConvolution
