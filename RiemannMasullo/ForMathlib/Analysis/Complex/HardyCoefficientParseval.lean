module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyCoefficientTable
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Parseval identities for Hardy coefficient residuals

Identify the boundary mean square of a disk-algebra function and of its polynomial
residuals with their coefficient energies. Interior radial expansions suffice.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric HardyTable Finset
open scoped Topology

namespace HardyBoundary

/-- The given Hilbert vector represents the power series on the unit circle. -/
def Expands (c : H) (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z)

/-- The polynomial represented by the actual finite vector in a Hardy table. -/
def tablePolynomial {d : ℕ} (p : Coeff d) : Polynomial ℂ :=
  ∑ k : Fin (d+1), Polynomial.C (p k) * Polynomial.X^k.val

theorem tablePolynomial_eval {d : ℕ} (p : Coeff d) (z : ℂ) :
    (tablePolynomial p).eval z = ∑ k : Fin (d+1), p k*z^k.val := by
  simp [tablePolynomial,Polynomial.eval_finsetSum]

private theorem shift_expands {c : H} {F : ℂ → ℂ} (hf : Expands c F) (k : ℕ) :
    Expands (shift c k) (fun z ↦ F z*z^k) := by
  intro z hz
  apply (hasSum_nat_add_iff' k).mp
  have hpre : ∑ i ∈ range k, shift c k i*z^i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [shift,not_le.mpr (Finset.mem_range.mp hi)]
  rw [hpre,sub_zero]
  convert! (hf z hz).mul_right (z^k) using 1
  funext j
  simp [shift,pow_add,mul_assoc]

theorem residual_expands {c : H} {F : ℂ → ℂ} (hf : Expands c F) {d : ℕ} (p : Coeff d) :
    Expands (unitVector-product c p) (fun z ↦ 1-F z*(tablePolynomial p).eval z) := by
  intro z hz
  have hu : HasSum (fun j : ℕ ↦ unitVector j*z^j) 1 := by
    convert! hasSum_ite_eq (0:ℕ) (1:ℂ) using 1
    funext j
    by_cases hj : j = 0 <;> simp [unitVector_apply,hj]
  have hs (k : Fin (d+1)) := (shift_expands hf k z hz).mul_left (p k)
  have hp : HasSum (fun j : ℕ ↦ product c p j*z^j) (F z*(tablePolynomial p).eval z) := by
    convert! hasSum_sum (s := (univ : Finset (Fin (d+1)))) (fun k _ ↦ hs k) using 1
    · funext j
      rw [product_apply,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      change (p k*(_ : ℂ))*z^j = p k*(_*z^j)
      rw [mul_assoc]
      rfl
    · rw [tablePolynomial_eval,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
  simpa only [lp.coeFn_sub,Pi.sub_apply,sub_mul] using hu.sub hp

private theorem fourier_arg (θ : ℝ) : fourier 1 (θ : AddCircle (2*Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_apply,circleMap_zero,Complex.ofReal_one,one_mul]
  congr 1
  push_cast
  field_simp

/-- Literal Parseval with normalized circle average and the complex coefficient-space norm. -/
theorem parseval_of_expands {c : H} {F : ℂ → ℂ} (hf : Expands c F)
    (hc : ContinuousOn F (sphere 0 1)) :
    Real.circleAverage (fun z ↦ ‖F z‖^2) 0 1 = ‖c‖^2 := by
  let : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩
  let G (x : AddCircle (2*Real.pi)) := F (fourier 1 x)
  let a : ℤ → ℂ := Int.rec (fun j ↦ c j) (fun _ ↦ 0)
  have fn (x : AddCircle (2*Real.pi)) (j : ℕ) : fourier (j:ℤ) x = (fourier 1 x)^j := by
    induction j with
    | zero => simp
    | succ j hj => rw [Nat.cast_succ,fourier_add,hj,pow_succ]
  have hG : fourierCoeff G = a := by
    apply fourierCoeff_eq_of_hasSum
    intro x
    have hnat : HasSum (fun j : ℕ ↦ fourier (j:ℤ) x • a j) (G x) := by
      apply (hf (fourier 1 x) (Circle.norm_coe _)).congr_fun
      intro j
      change fourier (j:ℤ) x * c j = c j*(fourier 1 x)^j
      rw [fn,mul_comm]
    have hneg : HasSum (fun j : ℕ ↦ fourier (-(j+1):ℤ) x • a (-(j+1):ℤ)) 0 := by
      convert! hasSum_zero (β := ℕ) (α := ℂ) using 1
      funext j
      change fourier (Int.negSucc j) x • (0:ℂ) = 0
      simp
    simpa using (hnat.of_nat_of_neg_add_one (f := fun i : ℤ ↦ fourier i x • a i) hneg)
  let u (θ : ℝ) := F (circleMap 0 1 θ)
  have hu : Continuous u := hc.comp_continuous (continuous_circleMap _ _) (fun θ ↦ by simp)
  have hu2 : MemLp u 2 (volume.restrict (Ioc (0:ℝ) (2*Real.pi))) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp ((hu.norm.pow 2).intervalIntegrable ..))
  have heq (j : ℤ) : fourierCoeffOn Real.two_pi_pos u j = a j := by
    rw [← hG,fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral G j 0]
    simp only [sub_zero,zero_add,one_div]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [u,G]
    rw [fourier_arg]
    simp only [fourier_coe_apply,sub_zero,smul_eq_mul]
  have ht := (hasSum_sq_fourierCoeffOn Real.two_pi_pos hu2).nat_add_neg_add_one
  have hs : HasSum (fun j : ℕ ↦ ‖c j‖^2) (Real.circleAverage (fun z ↦ ‖F z‖^2) 0 1) := by
    convert! ht using 1
    · funext j
      simp only [heq]
      change _ = ‖c j‖^2 + ‖(0:ℂ)‖^2
      simp
    · simp [Real.circleAverage,u]
  exact hs.tsum_eq.symm.trans (HardyTable.norm_sq c).symm

theorem table_residual_parseval {c : H} {F : ℂ → ℂ} (hf : Expands c F)
    (hc : ContinuousOn F (sphere 0 1)) {d : ℕ} (p : Coeff d) :
    Real.circleAverage (fun z ↦ ‖1-F z*(tablePolynomial p).eval z‖^2) 0 1 =
      ‖unitVector-product c p‖^2 := by
  apply parseval_of_expands (residual_expands hf p)
  exact continuousOn_const.sub (hc.mul (tablePolynomial p).continuous.continuousOn)

end HardyBoundary

end

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real HardyBoundary HardyTable
open scoped Topology

namespace HardySzego

private theorem radial_parseval {F : ℂ → ℂ} {b : ℕ → ℂ}
    (hc : ContinuousOn F (closedBall 0 1))
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ b j*z^j) (F z))
    {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasSum (fun j : ℕ ↦ ‖b j‖^2*r^(2*j)) (circleAverage (fun z ↦ ‖F z‖^2) 0 r) := by
  have hl1 : Memℓp (fun j : ℕ ↦ b j*(r:ℂ)^j) 1 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ENNReal).toReal)).2
    simpa using (hi (r:ℂ) (by simpa [abs_of_pos hr.1] using hr.2)).summable.norm
  let d : H := ⟨fun j ↦ b j*(r:ℂ)^j,hl1.of_exponent_ge (by norm_num)⟩
  have hexp : Expands d (fun z ↦ F ((r:ℂ)*z)) := by
    intro z hz
    apply (hi ((r:ℂ)*z) (by simpa [norm_mul,hz,abs_of_pos hr.1] using hr.2)).congr_fun
    intro j
    change (b j*(r:ℂ)^j)*z^j = b j*((r:ℂ)*z)^j
    rw [mul_pow,mul_assoc]
  have hcont : ContinuousOn (fun z ↦ F ((r:ℂ)*z)) (sphere 0 1) := by
    apply hc.comp ((continuous_const.mul continuous_id).continuousOn)
    intro z hz
    simp only [mem_sphere_zero_iff_norm] at hz
    simpa [mem_closedBall_zero_iff,norm_mul,hz,abs_of_pos hr.1] using hr.2.le
  have hP := parseval_of_expands hexp hcont
  have hE : circleAverage (fun z ↦ ‖F ((r:ℂ)*z)‖^2) 0 1 = circleAverage (fun z ↦ ‖F z‖^2) 0 r := by
    simp only [circleAverage_def,circleMap_zero,Complex.ofReal_one,one_mul]
  rw [hE,norm_sq] at hP
  have hs := (summable_sq d).hasSum
  rw [← hP] at hs
  apply hs.congr_fun
  intro j
  change ‖b j‖^2*r^(2*j) = ‖b j*(r:ℂ)^j‖^2
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr.1,mul_pow,← pow_mul]
  rw [Nat.mul_comm]

/-- The disk-algebra norm identity for arbitrary Taylor data, including the existence of
the coefficient square sum. The power expansion is only assumed at open-disk points. -/
theorem hasSum_sq_of_inner {F : ℂ → ℂ} {b : ℕ → ℂ}
    (hc : ContinuousOn F (closedBall 0 1))
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ b j*z^j) (F z)) :
    HasSum (fun j : ℕ ↦ ‖b j‖^2) (circleAverage (fun z ↦ ‖F z‖^2) 0 1) := by
  let r (n : ℕ) : ℝ := 1-(1/2:ℝ)^(n+1)
  have hrn (n : ℕ) : r n ∈ Ioo 0 1 := by
    constructor
    · exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n))
    · exact sub_lt_self _ (by positivity)
  have hdec := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_const (1/2:ℝ)
  have hrt : Tendsto r atTop (𝓝 1) := by
    dsimp [r]
    simpa only [pow_succ,mul_zero,zero_mul,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub hdec
  have hrad : Tendsto r atTop (𝓝[Icc 0 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrt,Eventually.of_forall fun n ↦ ⟨(hrn n).1.le,(hrn n).2.le⟩⟩
  have h1 : (1:ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hcircle : ContinuousOn (circleAverage (fun z ↦ ‖F z‖^2) 0) (Icc 0 1) :=
    Real.ContinuousOn.circleAverage ((hc.norm.pow 2).mono (by
      intro z hz
      simpa [Metric.mem_closedBall,dist_eq_norm] using hz.2)) (fun _ h ↦ h.1)
  have hE := (hcircle 1 h1).tendsto.comp hrad
  have hw (n : ℕ) := radial_parseval hc hi (hrn n)
  let w (j : ℕ) (x : ℝ) := ‖b j‖^2*x^(2*j)
  have hs : Summable (fun j : ℕ ↦ ‖b j‖^2) := by
    apply summable_of_sum_le (fun j ↦ sq_nonneg _) (c := circleAverage (fun z ↦ ‖F z‖^2) 0 1)
    intro S
    have hf : Tendsto (fun n ↦ ∑ j ∈ S, w j (r n)) atTop (𝓝 (∑ j ∈ S, ‖b j‖^2)) := by
      apply tendsto_finsetSum
      intro j _
      simpa [w] using (hrt.pow (2*j)).const_mul (‖b j‖^2)
    apply le_of_tendsto_of_tendsto hf hE
    apply Eventually.of_forall
    intro n
    exact ((hw n).summable.sum_le_tsum S (fun j _ ↦ mul_nonneg (sq_nonneg _) (pow_nonneg (hrn n).1.le _))).trans (hw n).tsum_eq.le
  have hseries : ContinuousOn (fun x ↦ ∑' j, w j x) (Icc 0 1) := by
    apply continuousOn_tsum (fun j ↦ (continuous_const.mul (continuous_id.pow _)).continuousOn) hs
    intro j x hx
    change ‖‖b j‖^2*x^(2*j)‖ ≤ ‖b j‖^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hx.1 _))]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hx.1 hx.2)
  have ht := (hseries 1 h1).tendsto.comp hrad
  have he : (∑' j, ‖b j‖^2) = circleAverage (fun z ↦ ‖F z‖^2) 0 1 := by
    apply tendsto_nhds_unique _ hE
    have hsame (n : ℕ) : (∑' j, w j (r n)) = circleAverage (fun z ↦ ‖F z‖^2) 0 (r n) := (hw n).tsum_eq
    simpa [Function.comp_def,w] using ht.congr (fun n ↦ hsame n)
  exact he ▸ hs.hasSum

end HardySzego

end
