module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannMasullo.External.HardyCriticalLine.ZetaFirstApproximation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Tactic

/-! # Uniform first approximation to zeta on the right half of a bounded strip -/

@[expose] public noncomputable section

open Classical Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

/-- A decreasing nonnegative multiplier transfers an improper tail estimate
to the weighted tail. The input is required at every endpoint beyond `a`. -/
private theorem norm_weighted_tail_le {g : ℝ → ℂ} {w : ℝ → ℝ} {a B : ℝ}
    (hg : IntegrableOn g (Ioi a)) (hG : IntegrableOn (fun x ↦ w x • g x) (Ioi a))
    (hw : AntitoneOn w (Ici a)) (hw₀ : ∀ x ∈ Ici a, 0 ≤ w x)
    (hb : ∀ x ∈ Ici a, ‖∫ u in Ioi x, g u‖ ≤ B) :
    ‖∫ u in Ioi a, w u • g u‖ ≤ w a*(2*B) := by
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi a hG tendsto_id).norm
  filter_upwards [eventually_ge_atTop a] with b hab
  have hinterval : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hg.mono_set Ioc_subset_Ioi_self)
  obtain ⟨ξ,hξ,hi⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    hab (hw₀ b hab) (hw.mono Icc_subset_Ici_self) hinterval
  have he := intervalIntegral.integral_interval_add_Ioi hg (hg.mono_set (Ioi_subset_Ioi hξ.1))
  have hsub := eq_sub_of_add_eq he
  rw [hsub] at hi
  refine hi.trans (mul_le_mul_of_nonneg_left ?_ (hw₀ a (mem_Ici.mpr le_rfl)))
  linarith [norm_sub_le (∫ u in Ioi a, g u) (∫ u in Ioi ξ, g u),hb a (mem_Ici.mpr le_rfl),hb ξ hξ.1]

open HardyCriticalLine

private theorem hardy_sawtooth_tail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T t x : ℝ}, 1 ≤ T → 0 < t → t ≤ 3*T → 3*T ≤ x →
      ‖∫ u in Ioi x, zetaFirstApproximationSawtoothTailIntegrand t u‖ ≤ C*T^(-(3/2):ℝ) := by
  let A := 3/(4*Real.pi^2) * ∑' n : ℤ, 1 / |(n:ℝ)|^2
  let B := 9/(80*Real.pi^3) * ∑' n : ℤ, 1 / |(n:ℝ)|^3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A+3*B,by positivity,?_⟩
  intro T t x hT ht ht' hx
  have hT₀ : 0 < T := by linarith
  have hxT : T ≤ x := by linarith
  have h := norm_integral_Ioi_zetaFirstApproximationSawtoothTailIntegrand_le_separated
    (T := t) (a := x) ht ht.le (by linarith) (by rw [div_le_iff₀ Real.pi_pos]; nlinarith [mul_nonneg (show 0 ≤ x by linarith) (sub_nonneg.mpr Real.pi_gt_three.le)])
  have he (p : ℝ) (hp : p ≤ 0) : x^p ≤ T^p := Real.rpow_le_rpow_of_nonpos hT₀ hxT hp
  have hw : T*T^(-(5/2):ℝ) = T^(-(3/2):ℝ) := by
    calc T*T^(-(5/2):ℝ) = T^((1:ℝ)+(-(5/2):ℝ)) := by rw [Real.rpow_add hT₀,Real.rpow_one]
         _ = _ := by norm_num
  calc _ ≤ A*x^(-(3/2):ℝ) + B*(t*x^(-(5/2):ℝ)) := h.trans_eq (by dsimp [A,B]; ring)
       _ ≤ A*T^(-(3/2):ℝ) + B*((3*T)*T^(-(5/2):ℝ)) := by
         exact add_le_add (mul_le_mul_of_nonneg_left (he (-(3/2):ℝ) (by norm_num)) hA)
           (mul_le_mul_of_nonneg_left (mul_le_mul ht' (he (-(5/2):ℝ) (by norm_num))
             (Real.rpow_nonneg (by linarith : 0 ≤ x) _) (by positivity)) hB)
       _ = _ := by rw [mul_assoc 3 T _,hw]; ring

private theorem shifted_sawtooth_eq {s : ℂ} {u : ℝ} (hu : 0 < u) :
    zetaFirstApproximationRealSawtooth u * (u:ℂ)^(-(s+1)) =
      u^(1/2-s.re) • zetaFirstApproximationSawtoothTailIntegrand s.im u := by
  rw [zetaFirstApproximationSawtoothTailIntegrand_eq_cpow _ hu,Complex.real_smul,
    Complex.ofReal_cpow hu.le, mul_left_comm,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
  congr 2
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]; ring

private theorem shifted_sawtooth_tail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T a : ℝ} {s : ℂ}, 1 ≤ T → 1/2 ≤ s.re →
      0 < s.im → s.im ≤ 3*T → 3*T ≤ a →
      ‖∫ u in Ioi a, zetaFirstApproximationRealSawtooth u*(u:ℂ)^(-(s+1))‖ ≤ C*T^(-(3/2):ℝ) := by
  obtain ⟨B,hB,h⟩ := hardy_sawtooth_tail
  refine ⟨2*B,by positivity,?_⟩
  intro T a s hT hσ ht ht' ha
  have ha₀ : 0 < a := by linarith
  let g := zetaFirstApproximationSawtoothTailIntegrand s.im
  let w (u : ℝ) := u^(1/2-s.re)
  have hid : EqOn (fun u : ℝ ↦ zetaFirstApproximationRealSawtooth u*(u:ℂ)^(-(s+1))) (fun u ↦ w u • g u) (Ioi a) :=
    fun _ hu ↦ shifted_sawtooth_eq (ha₀.trans hu)
  let z : ℂ := ((1/2:ℝ):ℂ) + s.im*Complex.I
  have hg : IntegrableOn g (Ioi a) := by
    apply (integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow (s := z) (by norm_num [z]) ha₀).congr_fun _ measurableSet_Ioi
    intro u hu
    change _ = zetaFirstApproximationSawtoothTailIntegrand s.im u
    rw [zetaFirstApproximationSawtoothTailIntegrand_eq_cpow s.im (ha₀.trans hu), neg_add]
    rfl
  have hG := (integrableOn_zetaFirstApproximationRealSawtooth_mul_cpow (s := s) (by linarith) ha₀).congr_fun hid measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi hid]
  have hw : AntitoneOn w (Ici a) := fun u hu v _ huv ↦
    Real.rpow_le_rpow_of_nonpos (ha₀.trans_le hu) huv (by linarith)
  have hw₀ (u : ℝ) (hu : u ∈ Ici a) : 0 ≤ w u := Real.rpow_nonneg (ha₀.le.trans hu) _
  have hb := norm_weighted_tail_le hg hG hw hw₀ (fun x hx ↦ h hT ht ht' (ha.trans hx))
  exact hb.trans ((mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos (show 1 ≤ a by linarith)
    (show 1/2-s.re ≤ 0 by linarith)) (by positivity)).trans_eq (by ring))

set_option maxHeartbeats 600000 in
/-- A length proportional to the height suffices uniformly throughout the
half strip. Abel transfer from the critical-line sawtooth bound avoids
a length loss in the mean square of the mollified Dirichlet polynomial. -/
theorem zeta_linearTruncation_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 4 →
      (m:ℝ)/2 ≤ s.im → s.im ≤ 3*m →
      ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 (4*m), (n:ℂ)^(-s)‖ ≤ C*(m:ℝ)^(-(1/2):ℝ) := by
  obtain ⟨B,hB,h⟩ := shifted_sawtooth_tail
  refine ⟨11+7*B,by positivity,?_⟩
  intro m hm s hσ hσ' ht ht'
  let T := (m:ℝ)
  let a := (((4*m+1:ℕ):ℝ))
  have hT : 1 ≤ T := by dsimp [T]; exact_mod_cast hm
  have hT₀ : 0 < T := by linarith
  have ha : a = 4*T+1 := by dsimp [a,T]; push_cast; ring
  have ha₀ : 0 < a := by linarith
  have ht₀ : 0 < s.im := by dsimp only [T] at hT₀; linarith
  have hx : 1 ≤ a := by linarith
  have h1 (z : ℂ) : ‖(a:ℂ)^z‖ = a^z.re := Complex.norm_cpow_eq_rpow_re_of_pos ha₀ _
  have hhalf : T^((1/2):ℝ)/T = T^(-(1/2):ℝ) := by
    rw [show -(1/2:ℝ) = (1/2:ℝ)-1 by ring,Real.rpow_sub hT₀,Real.rpow_one]
  have hnum : a^(1-s.re) ≤ 5*T^(1/2:ℝ) := by
    calc _ ≤ a^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
         _ ≤ (5*T)^(1/2:ℝ) := Real.rpow_le_rpow ha₀.le (by linarith) (by norm_num)
         _ ≤ _ := by
           rw [Real.mul_rpow (by norm_num) hT₀.le]
           gcongr
           exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hden : T/2 ≤ ‖s-1‖ := by
    refine ht.trans ?_
    have h := Complex.im_le_norm (s-1)
    simpa only [Complex.sub_im,Complex.one_im,sub_zero] using h
  have hPole : ‖(a:ℂ)^(1-s)/(s-1)‖ ≤ 10*T^(-(1/2):ℝ) := by
    rw [norm_div,h1,Complex.sub_re,Complex.one_re,← hhalf]
    exact (div_le_div₀ (by positivity) hnum (by positivity) hden).trans_eq (by ring)
  have hEnd : ‖(1/2:ℂ)*(a:ℂ)^(-s)‖ ≤ T^(-(1/2):ℝ) := by
    rw [norm_mul,h1,Complex.neg_re]
    norm_num
    calc _ ≤ 1*a^(-(1/2):ℝ) := mul_le_mul (by norm_num) (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
           (Real.rpow_nonneg ha₀.le _) zero_le_one
         _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_nonpos hT₀ (by linarith) (by norm_num)
  have hs : ‖s‖ ≤ 7*T := by
    have he := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re),abs_of_pos ht₀] at he
    change s.im ≤ 3*T at ht'
    linarith
  have hTail : ‖s * ∫ u in Ioi a, zetaFirstApproximationRealSawtooth u*(u:ℂ)^(-(s+1))‖ ≤
      7*B*T^(-(1/2):ℝ) := by
    rw [norm_mul]
    refine (mul_le_mul hs (h hT hσ ht₀ ht' (by linarith)) (norm_nonneg _) (by positivity)).trans_eq ?_
    have hp : T*T^(-(3/2):ℝ) = T^(-(1/2):ℝ) := by
      calc _ = T^((1:ℝ)+(-(3/2):ℝ)) := by rw [Real.rpow_add hT₀,Real.rpow_one]
           _ = _ := by norm_num
    rw [← hp]; ring
  have he := riemannZeta_eq_sum_Icc_add_eulerSawtoothTail_succ (s := s) (by linarith) ht₀ (4*m)
  let U := ∑ n ∈ Finset.Icc 1 (4*m), (n:ℂ)^(-s)
  let P := (a:ℂ)^(1-s)/(s-1)
  let E := (1/2:ℂ)*(a:ℂ)^(-s)
  let V := s * ∫ u in Ioi a, zetaFirstApproximationRealSawtooth u*(u:ℂ)^(-(s+1))
  change riemannZeta s = U+P+E-V at he
  change ‖riemannZeta s-U‖ ≤ _
  rw [show riemannZeta s - U = (P+E)-V by rw [he]; ring]
  calc _ ≤ (‖P‖+‖E‖)+‖V‖ := (norm_sub_le _ _).trans (add_le_add_left (norm_add_le P E) _)
       _ ≤ (10*T^(-(1/2):ℝ)+T^(-(1/2):ℝ))+7*B*T^(-(1/2):ℝ) := add_le_add (add_le_add hPole hEnd) hTail
       _ = (11+7*B)*T^(-(1/2):ℝ) := by ring

end RiemannMasullo
