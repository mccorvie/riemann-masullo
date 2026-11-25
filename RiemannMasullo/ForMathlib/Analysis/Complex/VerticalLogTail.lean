module

public import RiemannMasullo.ForMathlib.Analysis.Complex.LogModulusSublevel
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Dyadic distribution bounds from unit height windows -/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace RiemannMasullo.LogTail

/-- Cover the portion below height `2^n` by unit intervals about the integer heights. -/
theorem measure_split_dyadic (μ : Measure ℝ) (E : Set ℝ) (n : ℕ) {A B : ℝ≥0∞}
    (htail : μ {t : ℝ | (2:ℝ)^n < |t|} ≤ A)
    (hlocal : ∀ j : ℤ, |j| ≤ (2:ℤ)^n+1 →
      μ ({t : ℝ | |t-(j:ℝ)|≤1/2} ∩ E) ≤ B) :
    μ E ≤ A + ((2*(2:ℕ)^n+3 : ℕ) : ℝ≥0∞) * B := by
  classical
  let J : Finset ℤ := Finset.Icc (-(2:ℤ)^n-1) ((2:ℤ)^n+1)
  let W (j : ℤ) := {t : ℝ | |t-(j:ℝ)|≤1/2} ∩ E
  have hsub : E ⊆ {t : ℝ | (2:ℝ)^n < |t|} ∪ ⋃ j ∈ J, W j := by
    intro t ht
    by_cases H : (2:ℝ)^n < |t|
    · exact Or.inl H
    · apply Or.inr
      have hround := abs_sub_round t
      have ha : |(round t :ℝ)| ≤ (2:ℝ)^n+1 := by
        have htr' := abs_sub_le (round t:ℝ) t 0
        rw [sub_zero,sub_zero,abs_sub_comm (round t:ℝ) t] at htr'
        linarith [le_of_not_gt H]
      have ha' : |round t| ≤ (2:ℤ)^n+1 := by exact_mod_cast ha
      have hj : round t ∈ J := by
        simp only [J,Finset.mem_Icc]
        convert abs_le.mp ha' using 1
        ring_nf
      exact mem_iUnion₂.mpr ⟨round t,hj,hround,ht⟩
  have hj (j : ℤ) (hj : j ∈ J) : |j|≤(2:ℤ)^n+1 := by
    rw [abs_le]
    have := Finset.mem_Icc.mp hj
    constructor <;> linarith
  have hcard : J.card = 2*(2:ℕ)^n+3 := by
    dsimp [J]
    rw [Int.card_Icc]
    have he : ((2:ℤ)^n+1+1-(-(2:ℤ)^n-1)) = ((2*(2:ℕ)^n+3:ℕ):ℤ) := by
      push_cast
      ring
    rw [he,Int.toNat_natCast]
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ A+ ∑ j ∈ J, μ (W j) := add_le_add htail (measure_biUnion_finset_le J W)
    _ ≤ A+ ∑ _j ∈ J,B := by gcongr with j hj'; exact hlocal j (hj j hj')
    _ = _ := by simp [hcard,nsmul_eq_mul]

/-- The polynomial factor in a short-window disk bound is absorbed by the chosen
exponential parameter. This estimate is independent of the number field. -/
theorem local_factor (n : ℕ) :
    ((2*(2:ℕ)^n+3 : ℕ) : ℝ) * (n+1:ℝ) * Real.exp (-(6:ℝ)*(n+1)) ≤
      5*(1/2:ℝ)^n := by
  have hpow : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hn : (n:ℝ)+1 ≤ 2^n := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=n)))
  have hfac : ((2*(2:ℕ)^n+3:ℕ):ℝ) ≤ 5*(2:ℝ)^n := by push_cast; linarith
  have h8 : Real.exp (-6:ℝ) ≤ 1/8 := by
    rw [Real.exp_neg,inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have hh := Real.add_one_le_exp (3:ℝ)
    rw [show (6:ℝ)=3+3 by norm_num,Real.exp_add]
    nlinarith [Real.exp_pos 3]
  have hscale : Real.exp (-(6:ℝ)*(n+1)) ≤ (1/8:ℝ)^n := by
    rw [show -(6:ℝ)*(n+1)=(n:ℝ)*(-6)+(-6) by ring,Real.exp_add,Real.exp_nat_mul]
    exact (mul_le_of_le_one_right (by positivity) (h8.trans (by norm_num))).trans
      (pow_le_pow_left₀ (Real.exp_pos _).le h8 n)
  calc
    _ ≤ (5*(2:ℝ)^n) * (2:ℝ)^n * (1/8:ℝ)^n := by gcongr
    _ = _ := by rw [mul_assoc, mul_assoc, ← mul_pow,← mul_pow]; norm_num

end RiemannMasullo.LogTail

open Complex Metric Set Filter MeasureTheory
open scoped Topology ENNReal
namespace RiemannMasullo.LogTail
open DiskSmallValues

/-- A fixed logarithmic height bound on the integer centres is linear in the dyadic index. -/
theorem log_height_of_abs_le {j : ℤ} {n : ℕ} (hj : |j| ≤ (2:ℤ)^n+1) :
    1 + Real.log (2+|(j:ℝ)|) ≤ 3*((n:ℝ)+1) := by
  have haj : |(j:ℝ)| ≤ (2:ℝ)^n+1 := by exact_mod_cast hj
  have hpow : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hlog := Real.log_le_log (by positivity : 0<2+|(j:ℝ)|)
    (show 2+|(j:ℝ)|≤(2:ℝ)^n*4 by linarith)
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
    show Real.log 4 = 2*Real.log 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num] at hlog
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n)]

/-- If analytic Euler-centred disks have polynomial upper bounds and a uniform lower bound
at their centres, the absolute critical logarithm has a square-exponential tail on the
dyadic height scale. This uses the full actual zero orders on each disk. -/
theorem dyadic_log_tail_of_windows (μ : Measure ℝ) (u : ℝ → ℝ)
    (f : ℤ → ℂ → ℂ) (M : ℤ → ℝ) {K V W : ℝ} (hK : 0<K) (hV : 0≤V) (hW : 0≤W)
    (hDom : ∀ E : Set ℝ, μ E ≤ ENNReal.ofReal V * volume E)
    (hHeight : ∀ n : ℕ, μ {t : ℝ | (2:ℝ)^n < |t|} ≤ ENNReal.ofReal (W*(1/2:ℝ)^n))
    (hM : ∀ j, 1 ≤ M j)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) (closedBall 0 (19/18)))
    (hc : ∀ j, f j 0≠0)
    (hb : ∀ j, ∀ z ∈ closedBall (0:ℂ) (19/18), ‖f j z‖ ≤ M j)
    (hMlog : ∀ j, Real.log (M j) ≤ K * (1+Real.log (2+|(j:ℝ)|)))
    (hratio : ∀ j, Real.log (M j / ‖f j 0‖) ≤ K * (1+Real.log (2+|(j:ℝ)|)))
    (hval : ∀ j : ℤ, ∀ t : ℝ, |t-(j:ℝ)|≤1/2 → u t =
      Real.log ‖f j ((-5/6:ℂ)+(((t-j)/(9/5):ℝ):ℂ)*I)‖) :
    ∃ A K' : ℝ, 0<A ∧ 0<K' ∧ ∀ n : ℕ,
      μ {t : ℝ | A*((n:ℝ)+1)^2 < |u t|} ≤ ENNReal.ofReal (K'*(1/2:ℝ)^n) := by
  have hrp : 0 < Real.log (19/18) := Real.log_pos (by norm_num)
  have hρ : Real.log (19/18) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<19/18)]
  let B := 3*K/Real.log (19/18)
  have hB : 0<B := div_pos (by positivity) hrp
  have hB3 : 3*K ≤ B := by
    dsimp [B]
    rw [le_div_iff₀ hrp]
    have := mul_le_mul_of_nonneg_left hρ (show 0≤3*K by positivity)
    linarith
  refine ⟨46*B,1+W+40*V*B,by positivity,by positivity,?_⟩
  intro n
  let s := (n:ℝ)+1
  have hs : 1≤s := by dsimp [s]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hs' : 0<s := by linarith
  let E := {t : ℝ | (46*B)*s^2 < |u t|}
  have hloc (j : ℤ) (hj : |j|≤(2:ℤ)^n+1) :
      μ ({t : ℝ | |t-(j:ℝ)|≤1/2} ∩ E) ≤ ENNReal.ofReal (8*V*B*s*Real.exp (-6*s)) := by
    have hJ : 1+Real.log (2+|(j:ℝ)|) ≤ 3*s := log_height_of_abs_le hj
    have hM' := (hMlog j).trans (mul_le_mul_of_nonneg_left hJ hK.le)
    have hR' := (hratio j).trans (mul_le_mul_of_nonneg_left hJ hK.le)
    have hLin : 3*K*s ≤ B*s := mul_le_mul_of_nonneg_right hB3 hs'.le
    have hcount : Real.log (M j/‖f j 0‖)/Real.log (19/18) ≤ B*s := by
      dsimp [B]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hrp]
      linarith
    have hwindow := window_log_tail (hM j) (mul_pos hB hs') (show 0≤6*B*s^2 by positivity)
      (hf j) (hc j) (hb j) (by nlinarith [mul_pos hB hs']) (by linarith) hcount (T:=(j:ℝ))
    let F := {t : ℝ | |t-(j:ℝ)|≤1/2 ∧ 40*(B*s)+6*B*s^2 <
          |Real.log ‖f j ((-5/6:ℂ)+(((t-j)/(9/5):ℝ):ℂ)*I)‖|}
    have hEF : {t : ℝ | |t-(j:ℝ)|≤1/2} ∩ E ⊆ F := by
      intro t ht
      refine ⟨ht.1,?_⟩
      rw [←hval j t ht.1]
      have HH : 40*(B*s)+6*B*s^2 ≤ 46*B*s^2 := by
        have := mul_le_mul_of_nonneg_left (show s≤s^2 by nlinarith) (show 0≤40*B by positivity)
        linarith
      exact HH.trans_lt ht.2
    have he : -(6*B*s^2)/(B*s) = -6*s := by field_simp
    rw [he] at hwindow
    calc
      _ ≤ μ F := measure_mono hEF
      _ ≤ _ := hDom _
      _ ≤ ENNReal.ofReal V * ENNReal.ofReal (8*(B*s)*Real.exp (-6*s)) :=
        mul_le_mul_right hwindow _
      _ ≤ _ := by
        rw [←ENNReal.ofReal_mul hV]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hV hB.le) hs'.le) (Real.exp_pos (-6*s)).le]
  have hcov := measure_split_dyadic μ E n (hHeight n) hloc
  refine hcov.trans ?_
  have hV' : 0≤8*V*B := by positivity
  have hp : 0 < (1/2:ℝ)^n := by positivity
  have hnum := mul_le_mul_of_nonneg_left (local_factor n) hV'
  change _ * (((2*(2:ℕ)^n+3:ℕ):ℝ)*s*Real.exp (-6*s)) ≤ _ at hnum
  rw [show (((2*(2:ℕ)^n+3:ℕ):ℝ≥0∞)) = ENNReal.ofReal ((2*(2:ℕ)^n+3:ℕ):ℝ) from (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith

end RiemannMasullo.LogTail
