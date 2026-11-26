module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2_RatActualThetaEulerLogL2
public import Mathlib.Analysis.Normed.Ring.Units

/-! # Invertibility of the rational finite-place Euler operator on logarithmic L²

Each local Euler subtraction is a strict-contraction Neumann inverse. The
reindexed cone obeys the Euler recurrence on every Hilbert vector, so its
finite product inverse needs no restriction to a test-function image. -/

public noncomputable section

namespace RiemannMasullo.RatFiniteEulerLogLpSeries

open MeasureTheory NumberField IsDedekindDomain RatUnramifiedThetaLattice RatActualThetaEulerPointwise
open scoped Classical NumberField.AdeleRing

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "LogL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "EndL2" => LogL2 →L[ℂ] LogL2

/-- The complex-linear realization of positive log translation, `P(t) ↦ P(t+h)`. -/
def logTranslateCLM (h : ℝ) : EndL2 where
  toFun := Measure.translateLp volume 2 h
  map_add' := (Measure.translateLp volume 2 h).map_add
  map_smul' := translate_complex_smul h
  cont := (Measure.translateLp volume 2 h).continuous

@[simp] theorem logTranslateCLM_apply (h : ℝ) (P : LogL2) :
    logTranslateCLM h P = Measure.translateLp volume 2 h P := by
  unfold logTranslateCLM
  rfl

theorem norm_logTranslateCLM_le (h : ℝ) : ‖logTranslateCLM h‖ ≤ 1 :=
  (logTranslateCLM h).opNorm_le_bound zero_le_one fun P ↦ by simp

/-- The contraction whose geometric series inverts a single Euler subtraction. -/
def primeShift (v : V) : EndL2 :=
  (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ)⁻¹ • logTranslateCLM (Real.log (v.asIdeal.absNorm : ℝ))

theorem norm_primeShift_le (v : V) : ‖primeShift v‖ ≤ (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹ := by
  rw [primeShift, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa using mul_le_mul_of_nonneg_left (norm_logTranslateCLM_le (Real.log (v.asIdeal.absNorm : ℝ)))
    (inv_nonneg.mpr (Real.sqrt_nonneg (v.asIdeal.absNorm : ℝ)))

theorem norm_primeShift_lt_one (v : V) : ‖primeShift v‖ < 1 :=
  (norm_primeShift_le v).trans_lt (primeRadiusInvSqrt_lt_one v)

/-- `I - q⁻¹ᐟ² U_log(q)` as a unit of the bounded complex-linear endomorphism ring. -/
def primeEulerUnit (v : V) : EndL2ˣ := Units.oneSub (primeShift v) (norm_primeShift_lt_one v)

@[simp] theorem primeEulerUnit_val (v : V) : (primeEulerUnit v : EndL2) = 1 - primeShift v := by
  unfold primeEulerUnit
  rfl

theorem norm_primeEulerUnit_le (v : V) :
    ‖(primeEulerUnit v : EndL2)‖ ≤ 1 + (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹ :=
  (norm_sub_le (1 : EndL2) (primeShift v)).trans
    (add_le_add ContinuousLinearMap.norm_id_le (norm_primeShift_le v))

/-- Operator-norm convergence, not merely convergence on individual profiles. -/
theorem primeEulerUnit_inv_hasSum (v : V) :
    HasSum (fun n : ℕ ↦ primeShift v ^ n) (↑(primeEulerUnit v)⁻¹ : EndL2) :=
  (summable_geometric_of_norm_lt_one (norm_primeShift_lt_one v)).hasSum

theorem primeEulerUnit_inv_eq_tsum (v : V) :
    (↑(primeEulerUnit v)⁻¹ : EndL2) = ∑' n : ℕ, primeShift v ^ n :=
  (primeEulerUnit_inv_hasSum v).tsum_eq.symm

theorem norm_primeEulerUnit_inv_le (v : V) :
    ‖(↑(primeEulerUnit v)⁻¹ : EndL2)‖ ≤ (1 - (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹)⁻¹ := by
  rw [primeEulerUnit_inv_eq_tsum]
  have hid : ‖(1 : EndL2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h := tsum_geometric_le_of_norm_lt_one (primeShift v) (norm_primeShift_lt_one v)
  have hmono := inv_anti₀ (sub_pos.mpr (primeRadiusInvSqrt_lt_one v))
    (sub_le_sub_left (norm_primeShift_le v) 1)
  change (1 - ‖primeShift v‖)⁻¹ ≤ (1 - (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹)⁻¹ at hmono
  linarith

/-- With no finite places the cone has just the identity summand. -/
@[simp] theorem chartOperator_empty : chartOperator (∅ : Finset V) = ContinuousLinearMap.id ℂ LogL2 := by
  classical
  apply ContinuousLinearMap.ext
  intro P
  rw [chartOperator_apply, ← (chartSeries_hasSum _ P).tsum_eq, tsum_eq_single (0 : (∅ : Finset V) → ℕ)]
  · simp [coneTerm_apply, latticeRadius_empty, Measure.translateLp_zero]
  · intro n hn
    exact (hn (funext fun w ↦ (Finset.notMem_empty _ w.property).elim)).elim

/-- Deleting the geometric tail at a new place on the entire logarithmic Hilbert space. -/
theorem chartOperator_insert_euler (T : Finset V) (v : V) (hv : v ∉ T) (P : LogL2) :
    chartOperator (insert v T) P - (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ)⁻¹ •
      Measure.translateLp volume 2 (Real.log (v.asIdeal.absNorm : ℝ)) (chartOperator (insert v T) P) =
      chartOperator T P := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  have hq : 0 < q := Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  let U := Measure.translateLp (F := ℂ) volume 2 (Real.log q)
  let a : ℂ := (Real.sqrt q : ℂ)⁻¹
  let H (r : ℝ) : LogL2 := (Real.sqrt r : ℂ)⁻¹ • Measure.translateLp volume 2 (Real.log r) P
  have hshift {r : ℝ} (hr : 0 < r) : H (q * r) = a • U (H r) := by
    dsimp only [H, a, U]
    rw [Real.sqrt_mul hq.le, Complex.ofReal_mul, mul_inv_rev, Real.log_mul hq.ne' hr.ne',
      Measure.translateLp_add, LinearIsometryEquiv.trans_apply, translate_complex_smul, smul_smul,
      mul_comm ((Real.sqrt r : ℂ)⁻¹) ((Real.sqrt q : ℂ)⁻¹)]
  let term (k : ℕ) (n : T → ℕ) := H (q ^ k * latticeRadius n)
  let row (k : ℕ) := ∑' n, term k n
  let F := chartOperator (insert v T) P
  have hpair : HasSum (fun kn : ℕ × (T → ℕ) ↦ term kn.1 kn.2) F := by
    dsimp only [F]
    rw [chartOperator_apply]
    refine ((insertIndexEquiv v hv).hasSum_iff.mpr (chartSeries_hasSum (insert v T) P)).congr_fun ?_
    intro kn
    simp only [Function.comp_apply, coneTerm_apply, latticeRadius_insertIndex, term, H, q]
  have hfiber (k : ℕ) : HasSum (term k) (row k) :=
    (hpair.summable.comp_injective (i := fun n : T → ℕ ↦ (k, n))
      (fun _ _ e ↦ congrArg Prod.snd e)).hasSum
  have hrows : HasSum row F := hpair.prod_fiberwise hfiber
  have hnext (k : ℕ) : row (k + 1) = a • U (row k) := by
    apply (hfiber (k + 1)).unique
    refine ((U.toContinuousLinearEquiv.toContinuousLinearMap.hasSum (hfiber k)).const_smul a).congr_fun ?_
    intro n
    change H (q ^ (k + 1) * latticeRadius n) = a • U (H (q ^ k * latticeRadius n))
    rw [pow_succ', mul_assoc, hshift (mul_pos (pow_pos hq _) (cone_pos n))]
  have htail : HasSum (fun k ↦ row (k + 1)) (a • U F) :=
    ((U.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hrows).const_smul a).congr_fun hnext
  have he := ((hasSum_nat_add_iff' 1).mpr hrows).unique htail
  rw [Finset.sum_range_one] at he
  have hzero : row 0 = chartOperator T P := by
    rw [chartOperator_apply, ← (chartSeries_hasSum T P).tsum_eq]
    simp only [row, term, pow_zero, one_mul, H, coneTerm_apply]
  change F - a • U F = chartOperator T P
  rw [← he, ← hzero]
  abel

/-- The all-vector Euler cancellation as an identity of bounded complex operators. -/
theorem primeEulerUnit_mul_chartOperator (T : Finset V) (v : V) (hv : v ∉ T) :
    (primeEulerUnit v : EndL2) * chartOperator (insert v T) = chartOperator T := by
  ext1 P
  change (primeEulerUnit v : EndL2) (chartOperator (insert v T) P) = chartOperator T P
  rw [primeEulerUnit_val]
  simpa only [sub_apply, one_apply_eq_self, primeShift,
    smul_apply, logTranslateCLM_apply] using chartOperator_insert_euler T v hv P

/-- The whole Euler cone is invertible, with a product bound for its inverse. -/
theorem exists_chartOperator_unit (S : Finset V) :
    ∃ u : EndL2ˣ, (u : EndL2) = chartOperator S ∧ ‖(↑u⁻¹ : EndL2)‖ ≤
      ∏ v ∈ S, (1 + (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, chartOperator_empty.symm, ?_⟩
    rw [inv_one, Finset.prod_empty]
    exact ContinuousLinearMap.norm_id_le
  | @insert v T hv ih =>
    obtain ⟨u, hu, hb⟩ := ih
    refine ⟨(primeEulerUnit v)⁻¹ * u, ?_, ?_⟩
    · rw [Units.val_mul, hu, ← primeEulerUnit_mul_chartOperator T v hv, ← mul_assoc,
        Units.inv_mul, one_mul]
    · rw [Finset.prod_insert hv, mul_inv_rev, inv_inv, Units.val_mul]
      refine (norm_mul_le _ _).trans ?_
      calc
        ‖(↑u⁻¹ : EndL2)‖ * ‖(primeEulerUnit v : EndL2)‖
            ≤ (∏ w ∈ T, (1 + (Real.sqrt (w.asIdeal.absNorm : ℝ))⁻¹)) *
              (1 + (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹) :=
          mul_le_mul hb (norm_primeEulerUnit_le v) (norm_nonneg _) (by positivity)
        _ = _ := mul_comm _ _

end RiemannMasullo.RatFiniteEulerLogLpSeries
