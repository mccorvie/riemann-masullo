module

public import Mathlib.Analysis.Meromorphic.Order
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.ZetaMollifiedMean
import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalJensen
import RiemannMasullo.Ch13_ZerosHecke.Targets
import Mathlib.Tactic

/-! # A sublinear zero-density bound for each fixed right substrip of the Riemann zeta function -/

@[expose] public noncomputable section

open Classical Filter Complex Metric MeasureTheory Real Set MeromorphicOn
open scoped Topology
namespace RiemannMasullo.ZetaZeroDensity

open ConductorCylinder

set_option quotPrecheck false

local notation "M(" K ")" => mobiusMollifier (1 : DirichletCharacter ℂ 1) K
local notation "ord(" z ")" => ((meromorphicOrderAt riemannZeta z).untop₀.toNat : ℝ)
local notation "ctr(" t ")" => (⟨2,t⟩ : ℂ)

private theorem continuous_vertical (σ : ℝ) : Continuous (fun t : ℝ ↦ (⟨σ,t⟩ : ℂ)) := by
  have he : (fun t : ℝ ↦ (⟨σ,t⟩:ℂ)) = fun t : ℝ ↦ (σ:ℂ)+(t:ℂ)*Complex.I := funext fun _ ↦ (Complex.re_add_im _).symm
  rw [he]; fun_prop

private theorem continuous_moving_circle {F : ℂ → ℝ} (hF : Continuous F) (R : ℝ) :
    Continuous (fun t : ℝ ↦ Real.circleAverage F ctr(t) R) := by
  simp only [Real.circleAverage_def,smul_eq_mul]
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : ℝ × ℝ ↦ F (ctr(p.1)+(R:ℂ)*Complex.exp ((p.2:ℂ)*Complex.I)))
  apply hF.comp
  exact ((continuous_vertical 2).comp continuous_fst).add (continuous_const.mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))

/-- At a fixed
positive distance from the critical line the total ordinary zero order in
a dyadic height band saves a positive power. -/
theorem zeta_dyadic_order_saving {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ S : Finset ℂ,
      (∀ z ∈ S, 1/2+2*d ≤ z.re ∧ z.re ≤ 1 ∧ (m:ℝ) ≤ z.im ∧ z.im ≤ 2*m ∧ riemannZeta z = 0) →
      ∑ z ∈ S, ord(z) ≤ C*(m:ℝ)^(1-d^2/4) := by
  obtain ⟨B,hB,h⟩ := exists_time_mollifier hd hd'
  let h₀ := d/2
  let R := 3/2-d
  let r := 3/2-3*d/2
  let l := Real.log (R/r)
  have hh : 0 < h₀ := by dsimp [h₀]; positivity
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r,R]; linarith
  have hR := hr.trans hrR
  have hl : 0 < l := Real.log_pos ((lt_div_iff₀ hr).mpr (by linarith))
  refine ⟨3*B/(2*h₀*l),by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop 8] with m hK hm
  obtain ⟨K,hcenter,hmean⟩ := hK
  intro S hS
  let T := (m:ℝ)
  let a := T-1
  let b := 2*T+1
  let V := B*T^(1-d^2/4)
  have hT : 8 ≤ T := by dsimp [T]; exact_mod_cast hm
  have hab : a ≤ b := by dsimp [a,b]; linarith
  let up (z : ℂ) := (z.re:ℂ) + ((max (T/2) z.im : ℝ) : ℂ)*Complex.I
  have hup : Continuous up := Complex.continuous_ofReal.comp Complex.continuous_re |>.add
    ((Complex.continuous_ofReal.comp (continuous_const.max Complex.continuous_im)).mul continuous_const)
  have hup' (z : ℂ) (hz : T/2 ≤ z.im) : up z = z := by
    dsimp only [up]; rw [max_eq_right hz,Complex.re_add_im]
  have hup₀ (z : ℂ) : up z ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [up,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,mul_one,mul_zero,zero_add,add_zero,Complex.one_im] at hi
    linarith [le_max_left (T/2) z.im]
  let E (z : ℂ) := ‖riemannZeta z*M(K) z-1‖
  let F (z : ℂ) := E (up z)
  have hF : Continuous F := by
    apply Continuous.norm
    apply Continuous.sub _ continuous_const
    apply Continuous.mul _ ((differentiable_time_mollifier K).continuous.comp hup)
    exact continuous_iff_continuousAt.mpr fun z ↦ (differentiableAt_riemannZeta (hup₀ z)).continuousAt.comp hup.continuousAt
  have hFE (z : ℂ) (hz : T/2 ≤ z.im) : F z = E z := by dsimp only [F]; rw [hup' z hz]
  have hstrip (t : ℝ) (ht : t ∈ Icc a b) (z : ℂ) (hz : z ∈ closedBall ctr(t) R) :
      T/2 ≤ z.im ∧ z.im ≤ 3*T := by
    have hn : ‖z-ctr(t)‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hi := (abs_le.mp ((Complex.abs_im_le_norm (z-ctr(t))).trans hn))
    simp only [Complex.sub_im] at hi
    change T-1 ≤ t ∧ t ≤ 2*T+1 at ht
    dsimp only [R] at hi
    constructor <;> linarith [hi.1,hi.2,ht.1,ht.2]
  have hct (t : ℝ) (ht : t ∈ Icc a b) : T/2 ≤ t ∧ t ≤ 3*T :=
    hstrip t ht ctr(t) (mem_closedBall_self hR.le)
  have hcircle : (∫ t in a..b, circleAverage F ctr(t) R) ≤ V := by
    apply vertical_circle_mean_le hF hab
    intro θ
    let z := circleMap 0 R θ
    have hn : ‖z‖ = R := (norm_circleMap_zero R θ).trans (abs_of_pos hR)
    have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hn.le)
    have him := abs_le.mp ((Complex.abs_im_le_norm z).trans hn.le)
    have hleft : T/2 ≤ a+z.im := by dsimp only [a,R] at *; linarith [him.1]
    have hright : b+z.im ≤ 3*T := by dsimp only [b,R] at *; linarith [him.2]
    have hσ : 1/2+d ≤ 2+z.re := by dsimp only [R] at hre; linarith [hre.1]
    have hσ' : 2+z.re ≤ 4 := by dsimp only [R] at hre; linarith [hre.2]
    change (∫ t in (a+z.im)..(b+z.im), F ⟨2+z.re,t⟩) ≤ _
    rw [intervalIntegral.integral_congr (g := fun t ↦ E ⟨2+z.re,t⟩) (fun t ht ↦ by
      rw [uIcc_of_le (by linarith : a+z.im ≤ b+z.im)] at ht; exact hFE _ (hleft.trans ht.1))]
    exact hmean _ hσ hσ' _ _ (by linarith) hleft hright
  have hcent : (∫ t in a..b, F ctr(t)) ≤ V := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ E ctr(t)) (fun t ht ↦ by
      rw [uIcc_of_le hab] at ht; exact hFE _ (hct t ht).1)]
    exact hmean 2 (by linarith) (by norm_num) a b hab (hct a ⟨le_rfl,hab⟩).1 (hct b ⟨hab,le_rfl⟩).2
  let W (z : ℂ) := (Ioc (z.im-h₀) (z.im+h₀)).indicator (fun _ : ℝ ↦ ord(z))
  have hw (z : ℂ) : IntervalIntegrable (W z) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (((integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (by simp [Real.volume_Ioc]))).integrableOn)
  have hg (t : ℝ) (ht : t ∈ Icc a b) :
      (∑ z ∈ S, W z t)*l ≤ circleAverage F ctr(t) R + 2*F ctr(t) := by
    have ht' := hct t ht
    have hzeta : AnalyticOnNhd ℂ riemannZeta (closedBall ctr(t) R) := analyticOn_riemannZeta.mono (fun z hz ↦ by
      intro he; have he' : z = 1 := he; subst z; have hv := (hstrip t ht 1 hz).1; simp at hv; linarith)
    let U := S.filter (fun z ↦ t ∈ Ioc (z.im-h₀) (z.im+h₀))
    have hU (z : ℂ) (hz : z ∈ U) : z ∈ closedBall ctr(t) r ∧ riemannZeta z = 0 := by
      obtain ⟨hm,hw⟩ := Finset.mem_filter.mp hz
      obtain ⟨hβ,hβ',_,_,hzero⟩ := hS z hm
      refine ⟨?_,hzero⟩
      change dist z ctr(t) ≤ r
      rw [dist_eq_norm]
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      simp only [Complex.sub_re,Complex.sub_im]
      rw [abs_of_nonpos (by linarith : z.re-2 ≤ 0)]
      have hi : |z.im-t| ≤ h₀ := abs_le.mpr ⟨by linarith [hw.2],by linarith [hw.1]⟩
      dsimp only [r,h₀] at *; linarith
    have hJ := sum_orders_le_circleAverage_error hr hrR hzeta
      (fun z _ ↦ (differentiable_time_mollifier K).analyticAt z) (hcenter t ht'.1 ht'.2) U hU
    have he : (∑ z ∈ S, W z t) = ∑ z ∈ U, ord(z) := by
      simp only [U,Finset.sum_filter,W,Set.indicator_apply]
    have hEq : circleAverage F ctr(t) R = circleAverage E ctr(t) R := circleAverage_congr_sphere (fun z hz ↦ by
      rw [abs_of_pos hR] at hz; exact hFE _ (hstrip t ht z (sphere_subset_closedBall hz)).1)
    rw [he,hEq,hFE _ ht'.1]
    exact hJ
  have hInt : (∫ t in a..b, (∑ z ∈ S, W z t)*l) ≤ ∫ t in a..b, circleAverage F ctr(t) R+2*F ctr(t) :=
    intervalIntegral.integral_mono_on hab (by simpa only [Finset.sum_apply] using ((IntervalIntegrable.sum S (fun z _ ↦ hw z)).mul_const l))
      (((continuous_moving_circle hF R).add (continuous_const.mul (hF.comp (continuous_vertical 2)))).intervalIntegrable a b) hg
  have hW := integral_window_sum (S := S) (fun z ↦ ord(z)) hh.le hab (fun z hz ↦ by
    obtain ⟨_,_,h1,h2,_⟩ := hS z hz
    change T ≤ z.im at h1; change z.im ≤ 2*T at h2
    dsimp only [a,b,h₀]; constructor <;> linarith)
  change (∫ t in a..b, ∑ z ∈ S, W z t) = _ at hW
  rw [intervalIntegral.integral_mul_const,hW,intervalIntegral.integral_add (f := fun t ↦ circleAverage F ctr(t) R)
    (g := fun t ↦ 2*F ctr(t)) ((continuous_moving_circle hF R).intervalIntegrable a b)
    ((hF.comp (continuous_vertical 2)).intervalIntegrable a b |>.const_mul 2),intervalIntegral.integral_const_mul] at hInt
  have hnum : (∑ z ∈ S, ord(z))*(2*h₀*l) ≤ 3*V := by linarith only [hInt,hcircle,hcent]
  apply (le_div_iff₀ (by positivity : 0 < 2*h₀*l)).mpr hnum |>.trans_eq
  dsimp only [V,T]; ring

end RiemannMasullo.ZetaZeroDensity

open Classical Filter Complex Metric Set MeromorphicOn
open scoped Topology
namespace RiemannMasullo.ZetaZeroDensity

set_option quotPrecheck false
local notation "ord(" z ")" => ((meromorphicOrderAt riemannZeta z).untop₀.toNat : ℝ)

private theorem finite_box_order (X : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : Finset ℂ,
      (∀ z ∈ S, 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ X) → ∑ z ∈ S, ord(z) ≤ B := by
  let K := closedBall (0:ℂ) (1+X)
  let D := divisor riemannZeta K
  let F := (D.finiteSupport (isCompact_closedBall ..)).toFinset
  have hzeta : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  refine ⟨∑ z ∈ F, ord(z),Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _),?_⟩
  intro S hS
  have hz (z : ℂ) (hm : z ∈ S) (hn : z ∉ F) : ord(z) = 0 := by
    obtain ⟨hr,hr',hi,hi'⟩ := hS z hm
    have hK : z ∈ K := by
      change dist z 0 ≤ 1+X
      rw [dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [abs_of_nonneg hr,abs_of_nonneg hi]; linarith)
    have he : D z = 0 := by simpa [F,Function.mem_support] using hn
    dsimp only [D] at he
    have hμ : MeromorphicOn riemannZeta K := fun z _ ↦ hzeta z (mem_univ z)
    rw [hμ.divisor_apply hK] at he
    rw [he]; norm_num
  calc _ = ∑ z ∈ S.filter (· ∈ F), ord(z) := by
          rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun z hm ↦ by by_cases h : z ∈ F <;> simp [h,hz z hm]
       _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun z hz ↦ (Finset.mem_filter.mp hz).2) (fun _ _ _ ↦ Nat.cast_nonneg _)

/-- An unconditional positive-height zero-density bound sufficient for any
fixed open strip. The exponent is weaker than Ingham's, and it counts the
actual meromorphic multiplicities at the closed horizontal threshold. -/
theorem positiveHeightZetaDensity_power {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ S : Finset ℂ,
      (∀ z ∈ S, z.re ∈ Ioo (0:ℝ) 1 ∧ riemannZeta z = 0 ∧ 1/2+2*d ≤ z.re ∧ z.im ∈ Ioc 0 T) →
      ∑ z ∈ S, ord(z) ≤ C*T^(1-d^2/4) := by
  obtain ⟨B,hB,h⟩ := zeta_dyadic_order_saving hd hd'
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨C,hC,hsmall⟩ := finite_box_order (2*(N:ℝ)+2)
  let u := 1-d^2/4
  have hu : 0 < u := by dsimp [u]; nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 1/4-d)]
  let D := B+C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrow (m : ℕ) (hm : 1 ≤ m) (S : Finset ℂ)
      (hs : ∀ z ∈ S, 1/2+2*d ≤ z.re ∧ z.re ≤ 1 ∧ (m:ℝ) ≤ z.im ∧ z.im ≤ 2*m ∧ riemannZeta z = 0) :
      ∑ z ∈ S, ord(z) ≤ D*(m:ℝ)^u := by
    have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    by_cases hmn : N ≤ m
    · exact (hN m hmn S hs).trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    · refine (hsmall S (fun z hz ↦ ?_)).trans ?_
      · obtain ⟨h1,h2,h3,h4,_⟩ := hs z hz
        have hmn' : (m:ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
        exact ⟨by linarith,h2,by linarith,by linarith⟩
      · exact (show C ≤ D by dsimp [D]; linarith).trans (le_mul_of_one_le_right hD (Real.one_le_rpow hm' hu.le))
  let g := (2:ℝ)^u
  have hg : 1 < g := Real.one_lt_rpow (by norm_num) hu
  let A := C+D/(g-1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCA : C ≤ A := le_add_of_nonneg_right (div_nonneg hD (sub_nonneg.mpr hg.le))
  have hstep : A+D ≤ A*g := by
    have h := (div_mul_cancel₀ D (sub_ne_zero.mpr hg.ne'))
    dsimp only [A]; nlinarith only [h,mul_nonneg hC (sub_nonneg.mpr hg.le)]
  have hall (n : ℕ) : ∀ S : Finset ℂ,
      (∀ z ∈ S, 1/2+2*d ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ (2:ℝ)^n ∧ riemannZeta z = 0) →
      ∑ z ∈ S, ord(z) ≤ A*((2:ℝ)^n)^u := by
    induction n with
    | zero =>
      intro S hS
      rw [pow_zero,Real.one_rpow,mul_one]
      apply (hsmall S ?_).trans hCA
      intro z hz; obtain ⟨h1,h2,h3,h4,_⟩ := hS z hz
      rw [pow_zero] at h4
      exact ⟨by linarith,h2,h3.le,by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]⟩
    | succ n ih =>
      intro S hS
      let L := S.filter (fun z ↦ z.im ≤ (2:ℝ)^n)
      let U := S.filter (fun z ↦ ¬z.im ≤ (2:ℝ)^n)
      have hs : (∑ z ∈ L, ord(z)) + ∑ z ∈ U, ord(z) = ∑ z ∈ S, ord(z) := Finset.sum_filter_add_sum_filter_not ..
      have hL := ih L (fun z hz ↦ by
        obtain ⟨hm,ht⟩ := Finset.mem_filter.mp hz
        obtain ⟨h1,h2,h3,_,h4⟩ := hS z hm
        exact ⟨h1,h2,h3,ht,h4⟩)
      have hU := hrow (2^n) (Nat.one_le_pow _ _ (by norm_num)) U (fun z hz ↦ by
        obtain ⟨hm,ht⟩ := Finset.mem_filter.mp hz
        obtain ⟨h1,h2,_,h3,h4⟩ := hS z hm
        rw [pow_succ] at h3
        push_cast
        exact ⟨h1,h2,(lt_of_not_ge ht).le,by linarith,h4⟩)
      push_cast at hU
      rw [← hs,pow_succ,Real.mul_rpow (by positivity) (by norm_num)]
      exact (add_le_add hL hU).trans (by
        have h := mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg (by positivity : 0 ≤ (2:ℝ)^n) u)
        dsimp only [g] at h; linarith only [h])
  refine ⟨A*g,by positivity,?_⟩
  intro T hT S hS
  obtain ⟨n,hl,hu'⟩ := exists_nat_pow_near (show 1 ≤ T by linarith) (by norm_num : (1:ℝ) < 2)
  have hc := hall (n+1) S (fun z hz ↦ by
    obtain ⟨h1,h2,h3,h4⟩ := hS z hz
    exact ⟨h3,h1.2.le,h4.1,h4.2.trans hu'.le,h2⟩)
  have he : A*((2:ℝ)^(n+1))^u ≤ A*g*T^u := by
    rw [pow_succ,Real.mul_rpow (by positivity) (by norm_num)]
    have hb := Real.rpow_le_rpow (by positivity) hl hu.le
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by norm_num) u)) hA).trans_eq (by dsimp [g];ring)
  exact hc.trans he

end RiemannMasullo.ZetaZeroDensity
