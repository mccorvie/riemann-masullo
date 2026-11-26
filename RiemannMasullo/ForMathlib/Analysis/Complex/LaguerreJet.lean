module

public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Tactic

/-! # Finite Taylor coefficients of the Cayley exponential and its Euler tail -/

@[expose] public noncomputable section

open Complex Filter Finset Metric Set Topology
namespace RiemannMasullo.LaguerreJet

/-- Taylor coefficient of order `n` at the origin. -/
def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The generalized Laguerre polynomial of parameter `-1` at `-c`, evaluated
by a finite sum of binomial coefficients, powers and factorials. -/
def laguerre (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | k+1 => ∑ j ∈ range (k+1), (k.choose j:ℂ)*c^(j+1)/((j+1).factorial:ℂ)

theorem laguerre_succ_eq_sum (c : ℂ) (k : ℕ) :
    laguerre c (k+1) = ∑ j ∈ range (k+1), (k.choose j:ℂ)*c^(j+1)/((j+1).factorial:ℂ) := rfl

private def coord (z : ℂ) : ℂ := (1-z)⁻¹

private theorem coord_deriv {z : ℂ} (hz : z ≠ 1) : HasDerivAt coord (coord z ^ 2) z := by
  have h : 1-z ≠ 0 := sub_ne_zero.mpr hz.symm
  convert ((hasDerivAt_id z).const_sub (1:ℂ)).inv h using 1 <;> first | rfl | simp [coord, div_eq_inv_mul, inv_pow]

/-- The coefficient of a partial fraction with pole away from the origin. -/
theorem coeff_simple (a : ℂ) (ha : a ≠ 0) (n : ℕ) :
    coeff (fun z : ℂ ↦ 1/(z+a)) n = (-1)^n/a^(n+1) := by
  have h := congrFun (iteratedDeriv_comp_add_const n (fun z : ℂ ↦ 1/z) a) 0
  have hinv := iteratedDerivWithin_one_div (𝕜 := ℂ) n isOpen_univ (x := a) (by simp)
  rw [iteratedDerivWithin_univ] at hinv
  simp only [zero_add] at h
  rw [coeff, h, hinv]
  simp only [show -1-(n:ℤ) = -((n+1:ℕ):ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  field_simp [ha, Nat.factorial_ne_zero]

/-- Euler's integral estimate for the tail after the last included norm `X`. -/
theorem tail_three_halves {X : ℕ} (hX : 0 < X) :
    (∑' k : ℕ, ((k+X+1 : ℕ):ℝ)^(-(3/2):ℝ)) ≤ 2/Real.sqrt X := by
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have ha : AntitoneOn (fun x : ℝ ↦ x^(-(3/2):ℝ)) (Ici (X:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hXr.trans_le hx) hxy (by norm_num)
  have h := ha.tsum_comp_add_le_integral X (integrableOn_Ioi_rpow_of_lt (by norm_num) hXr)
    (fun t ht ↦ Real.rpow_nonneg (hXr.trans ht).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num) hXr] at h
  convert h using 1
  norm_num
  rw [show (-(1/2):ℝ) = -(1/(2:ℝ)) by ring, Real.rpow_neg hXr.le, ← Real.sqrt_eq_rpow]
  ring

/-- A bounded Dirichlet coefficient sequence has a uniform tail on the closed
half-plane to the right of three halves. The last included index is `X`. -/
theorem norm_LSeries_sub_partial {w : ℕ → ℂ} {D : ℝ} (hw : ∀ m ≠ 0, ‖w m‖ ≤ D)
    {s : ℂ} (hs : 3/2 ≤ s.re) {X : ℕ} (hX : 0 < X) :
    ‖LSeries w s - ∑ m ∈ range (X+1), LSeries.term w s m‖ ≤ 2*D/Real.sqrt X := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hw 1 one_ne_zero)
  have hS := LSeriesSummable_of_bounded_of_one_lt_re hw (show 1 < s.re by linarith)
  have hT := (summable_nat_add_iff (X+1)).mpr hS
  have hP := (summable_nat_add_iff (X+1)).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2):ℝ) < -1))
  change ‖(∑' m, LSeries.term w s m) - _‖ ≤ _
  rw [← hS.sum_add_tsum_nat_add (X+1), add_sub_cancel_left]
  have hterm (k : ℕ) : ‖LSeries.term w s (k+(X+1))‖ ≤ D*((k+(X+1):ℕ):ℝ)^(-(3/2):ℝ) := by
    let m := k+(X+1)
    have hm : m ≠ 0 := by dsimp [m]; omega
    have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hm₀ : (0:ℝ) < m := zero_lt_one.trans_le hm₁
    rw [LSeries.term_of_ne_zero hm, norm_div, ← Complex.ofReal_natCast m,
      Complex.norm_cpow_eq_rpow_re_of_pos hm₀, div_eq_mul_inv, ← Real.rpow_neg hm₀.le]
    exact mul_le_mul (hw m hm) (Real.rpow_le_rpow_of_exponent_le hm₁ (neg_le_neg hs))
      (Real.rpow_nonneg hm₀.le _) hD
  calc
    _ ≤ _ := norm_tsum_le_tsum_norm hT.norm
    _ ≤ ∑' k : ℕ, D*((k+(X+1):ℕ):ℝ)^(-(3/2):ℝ) := hT.norm.tsum_le_tsum hterm (hP.mul_left D)
    _ = D * ∑' k : ℕ, ((k+X+1:ℕ):ℝ)^(-(3/2):ℝ) := by rw [tsum_mul_left]; simp only [Nat.add_assoc]
    _ ≤ D * (2/Real.sqrt X) := mul_le_mul_of_nonneg_left (tail_three_halves hX) hD
    _ = _ := by ring

/-- Cauchy's bound for the difference between two normalized Taylor coefficients. -/
theorem norm_coeff_sub_le {f g : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hB : ∀ z ∈ sphere 0 R, ‖f z-g z‖ ≤ C) (n : ℕ) : ‖coeff f n - coeff g n‖ ≤ C/R^n := by
  have h0 : (0:ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := fun z ↦ f z - g z)
    n hR ((hf.sub hg).differentiableOn.diffContOnCl_ball (by rfl)) hB
  rw [coeff, coeff, ← sub_div, ← iteratedDeriv_fun_sub ((hf 0 h0).contDiffAt) ((hg 0 h0).contDiffAt),
    norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hd (Nat.cast_nonneg _)).trans_eq
  field_simp [Nat.factorial_ne_zero]

private theorem analytic_coord : AnalyticAt ℂ coord 0 := by
  unfold coord
  fun_prop (disch := norm_num)

private theorem jet_pow_mul {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (j n : ℕ) :
    coeff (fun z ↦ z^j*g z) n = if j ≤ n then coeff g (n-j) else 0 := by
  rw [coeff,iteratedDeriv_fun_mul (f := fun z : ℂ ↦ z^j) (by fun_prop) hg.contDiffAt]
  simp only [iteratedDeriv_fun_pow_zero]
  by_cases h : j ≤ n
  · rw [ite_eq_left h, Finset.sum_eq_single j]
    · simp only [ite_true, coeff, Nat.cast_choose _ h]
      field_simp [Nat.factorial_ne_zero]
    · intro b _ hb
      simp [hb]
    · intro hh
      exact (hh (Finset.mem_range.mpr (by omega))).elim
  · rw [ite_eq_right h, Finset.sum_eq_zero, zero_div]
    intro i hi
    have : i ≠ j := by have := Finset.mem_range.mp hi; omega
    simp [this]

private theorem jet_coord_pow (j n : ℕ) {z : ℂ} (hz : z ≠ 1) :
    iteratedDeriv n (fun u ↦ coord u ^ j) z = (j.ascFactorial n:ℂ)*coord z^(j+n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have h : iteratedDeriv n (fun u ↦ coord u ^ j) =ᶠ[𝓝 z]
      (fun u ↦ (j.ascFactorial n:ℂ)*coord u^(j+n)) :=
      (eventually_ne_nhds hz).mono fun _ hu ↦ ih hu
    rw [iteratedDeriv_succ,h.deriv_eq,(((coord_deriv hz).fun_pow (j+n)).const_mul (j.ascFactorial n:ℂ)).deriv]
    rw [Nat.ascFactorial_succ]
    push_cast
    by_cases h0 : j+n = 0
    · obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp h0
      norm_num
    · have he : (j+n-1)+2 = j+(n+1) := by omega
      rw [show (j.ascFactorial n:ℂ)*(((j:ℂ)+n)*coord z^(j+n-1)*coord z^2) =
        (((j:ℂ)+n)*(j.ascFactorial n:ℂ))*(coord z^(j+n-1)*coord z^2) by ring, ← pow_add, he]

private theorem coeff_coord_pow (j n : ℕ) :
    coeff (fun z ↦ coord z ^ j) n = ((j+n-1).choose n:ℂ) := by
  rw [coeff,jet_coord_pow j n zero_ne_one,Nat.ascFactorial_eq_factorial_mul_choose']
  simp [coord,Nat.factorial_ne_zero]

/-- Closed binomial formula for the order-`n+1` generalized Laguerre
polynomial of parameter `-1`, with the sign of its argument reversed. -/
theorem coeff_exp_coord_succ (c : ℂ) (k : ℕ) :
    coeff (fun z : ℂ ↦ Complex.exp (c*((1-z)⁻¹-1))) (k+1) =
      ∑ j ∈ range (k+1), (k.choose j:ℂ)*c^(j+1)/((j+1).factorial:ℂ) := by
  let n := k+1
  let y (z : ℂ) := z*coord z
  have hy : AnalyticAt ℂ y 0 := analyticAt_id.fun_mul analytic_coord
  have hy₀ : y 0 = 0 := by simp [y]
  have hF : AnalyticAt ℂ (fun u : ℂ ↦ Complex.exp (c*u)) 0 := by fun_prop
  obtain ⟨G,hG,hT⟩ := hF.exists_eventuallyEq_sum_add_pow_mul (n+1)
  have ht : Tendsto y (𝓝 0) (𝓝 0) := by simpa only [hy₀] using hy.continuousAt.tendsto
  let Q (i : ℕ) (z : ℂ) := (c^i/(i.factorial:ℂ))*(z^i*coord z^i)
  let rem (z : ℂ) := coord z^(n+1)*G (y z)
  have hQ (i : ℕ) : AnalyticAt ℂ (Q i) 0 :=
    analyticAt_const.fun_mul ((analyticAt_id.pow _).fun_mul (analytic_coord.pow _))
  have hrem : AnalyticAt ℂ rem 0 :=
    (analytic_coord.pow _).fun_mul ((show AnalyticAt ℂ G (y 0) by rwa [hy₀]).comp hy)
  have H : (fun z : ℂ ↦ Complex.exp (c*((1-z)⁻¹-1))) =ᶠ[𝓝 0]
      (fun z ↦ (∑ i ∈ range (n+1), Q i z) + z^(n+1)*rem z) := by
    filter_upwards [ht.eventually hT,eventually_ne_nhds (zero_ne_one : (0:ℂ) ≠ 1)] with z hz hz₁
    have hyz : (1-z)⁻¹-1 = y z := by
      dsimp [y,coord]; field_simp [sub_ne_zero.mpr hz₁.symm]; ring
    rw [hyz,hz]
    simp only [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one, smul_eq_mul]
    congr 1
    · apply sum_congr rfl
      intro i hi
      simp [y,Q,mul_pow]
      ring
    · simp [y,rem,mul_pow]; ring
  have hcoeff (i : ℕ) (hi : i ∈ range (n+1)) :
      coeff (Q i) n = c^i/(i.factorial:ℂ)*((k.choose (n-i)):ℂ) := by
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    change iteratedDeriv n (fun z ↦ (c^i/(i.factorial:ℂ))*(z^i*coord z^i)) 0 / _ = _
    rw [iteratedDeriv_const_mul_field, mul_div_assoc]
    change _ * coeff (fun z ↦ z^i*coord z^i) n = _
    rw [jet_pow_mul (g := fun z ↦ coord z^i) (analytic_coord.fun_pow i) i n,ite_eq_left hin,coeff_coord_pow]
    congr 3
    dsimp [n] at *
    omega
  have he : coeff (fun z : ℂ ↦ Complex.exp (c*((1-z)⁻¹-1))) n = ∑ i ∈ range (n+1), c^i/(i.factorial:ℂ)*((k.choose (n-i)):ℂ) := by
    rw [coeff, H.iteratedDeriv_eq n, iteratedDeriv_fun_add
      (f := fun z ↦ ∑ i ∈ range (n+1), Q i z) (g := fun z ↦ z^(n+1)*rem z)
      (Finset.analyticAt_fun_sum _ (fun i _ ↦ hQ i)).contDiffAt
      ((analyticAt_id.fun_pow (n+1)).fun_mul hrem).contDiffAt,add_div,
      iteratedDeriv_fun_sum (fun i _ ↦ (hQ i).contDiffAt), Finset.sum_div]
    change (∑ i ∈ range (n+1), coeff (Q i) n) + coeff (fun z ↦ z^(n+1)*rem z) n = _
    rw [jet_pow_mul hrem,ite_eq_right (Nat.not_succ_le_self _),add_zero]
    exact sum_congr rfl hcoeff
  rw [he,Finset.sum_range_succ']
  have hn0 : k.choose (n-0)=0 := Nat.choose_eq_zero_of_lt k.lt_succ_self
  rw [hn0,Nat.cast_zero,mul_zero,add_zero]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n-(j+1) = k-j by dsimp [n]; omega, Nat.choose_symm hjk]
  ring

/-- The finite binomial polynomial is the exact Taylor coefficient of the Cayley exponential. -/
theorem coeff_exp_coord (c : ℂ) (n : ℕ) :
    coeff (fun z : ℂ ↦ Complex.exp (c*((1-z)⁻¹-1))) n = laguerre c n := by
  cases n with
  | zero => simp [coeff,laguerre]
  | succ k => exact coeff_exp_coord_succ c k

end RiemannMasullo.LaguerreJet
