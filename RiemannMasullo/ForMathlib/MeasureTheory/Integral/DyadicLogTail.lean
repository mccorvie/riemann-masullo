module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ClippedLogQuadrature
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic

/-! # From geometric bounds at square thresholds to integrated logarithmic tails -/

@[expose] public noncomputable section

open Real Filter MeasureTheory Set Function
open scoped Topology ENNReal

namespace RiemannMasullo.LogQuadrature

private theorem eventually_quadratic_mul_geometric {A K q r : ℝ} (hA : 0 < A) (hK : 0 < K)
    (hq : 0 ≤ q) (hqr : q < r) :
    ∀ᶠ m : ℕ in atTop, A*((m:ℝ)+2)^2 * (K*q^m) ≤ r^m := by
  have hr := hq.trans_lt hqr
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 2 (div_nonneg hq hr.le)
    ((div_lt_one hr).2 hqr)).const_mul (9*A*K)
  have he : ∀ᶠ m : ℕ in atTop, (9*A*K)*((m:ℝ)^2*(q/r)^m) < 1 :=
    ht.eventually_lt_const (by simp)
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with m hm hm1
  have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hsq : ((m:ℝ)+2)^2 ≤ 9*(m:ℝ)^2 := by
    nlinarith [sq_nonneg ((m:ℝ)-1)]
  have hq0 : 0 ≤ (q/r)^m := pow_nonneg (div_nonneg hq hr.le) _
  have hb : A*((m:ℝ)+2)^2*K*(q/r)^m ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hA.le) hK.le) hq0]
  have hh := mul_le_mul_of_nonneg_right hb (pow_nonneg hr.le m)
  rw [mul_assoc,← mul_pow,div_mul_cancel₀ _ hr.ne',one_mul] at hh
  nlinarith

private theorem integrated_above_square (μ : Measure ℝ) {f : ℝ → ℝ}
    (hm : Measurable f) (hi : Integrable f μ) {A K q r : ℝ} (hA : 0 < A) (hK : 0 < K)
    (hq : 0 ≤ q) (hr : 0 < r) (hr1 : r < 1)
    (ht : ∀ n : ℕ, μ {x | A*((n:ℝ)+1)^2 < |f x|} ≤ ENNReal.ofReal (K*q^n))
    {N : ℕ} (hB : ∀ m ≥ N, A*((m:ℝ)+2)^2 * (K*q^m) ≤ r^m) :
    (∫ x in {x | A*((N:ℝ)+1)^2 < |f x|}, |f x| ∂μ) ≤ r^N * (1-r)⁻¹ := by
  let g := fun j : ℕ ↦ A*((N:ℝ)+j+1)^2
  let B := fun j : ℕ ↦ (fun x ↦ |f x|) ⁻¹' Ioc (g j) (g (j+1))
  have hg : Monotone g := by
    intro i j hij
    dsimp [g]
    gcongr
  have hu : ¬ BddAbove (range g) := by
    rintro ⟨b,hb⟩
    obtain ⟨j,hj⟩ := exists_nat_gt (b/A)
    have hgr := hb (mem_range_self j)
    have h₁ := (div_lt_iff₀ hA).1 hj
    have h₂ : (j:ℝ) ≤ ((N:ℝ)+j+1)^2 := by
      nlinarith [sq_nonneg ((N:ℝ)+j),Nat.cast_nonneg (α:=ℝ) N,Nat.cast_nonneg (α:=ℝ) j]
    dsimp [g] at hgr
    nlinarith [mul_le_mul_of_nonneg_left h₂ hA.le]
  have hall : ⋃ j, B j = {x | A*((N:ℝ)+1)^2 < |f x|} := by
    have hU := iUnion_Ioc_map_succ_eq_Ioi (f:=g) (fun j ↦ hg (bot_le (a:=j))) hu
    change (⋃ j : ℕ, (fun x ↦ |f x|) ⁻¹' Ioc (g j) (g (j+1))) = _
    rw [← preimage_iUnion]
    have hU' : (⋃ j : ℕ, Ioc (g j) (g (j+1))) = Ioi (A*((N:ℝ)+1)^2) := by
      simpa [g] using hU
    rw [hU']
    rfl
  have hmB (j : ℕ) : MeasurableSet (B j) := (continuous_abs.measurable.comp hm) measurableSet_Ioc
  have hd : Pairwise (Disjoint on B) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (Set.Ioc_disjoint_Ioc_of_le (hg h)).preimage _
    · exact ((Set.Ioc_disjoint_Ioc_of_le (hg h)).preimage _).symm
  have hs := hasSum_integral_iUnion hmB hd (hi.abs.integrableOn (s:=⋃ j, B j))
  rw [hall] at hs
  have htSum := (hasSum_geometric_of_lt_one hr.le hr1).mul_left (r^N)
  refine hasSum_le (g := fun j : ℕ ↦ r^N*r^j) (fun j ↦ ?_) hs htSum
  have hsub : B j ⊆ {x | A*(((N+j:ℕ):ℝ)+1)^2 < |f x|} := by
    intro x hx
    change A*(((N+j:ℕ):ℝ)+1)^2 < |f x|
    simpa only [Nat.cast_add,g] using hx.1
  have hmeasure := (measure_mono hsub).trans (ht (N+j))
  have hfin : μ (B j) < ⊤ := hmeasure.trans_lt ENNReal.ofReal_lt_top
  have hreal : μ.real (B j) ≤ K*q^(N+j) := by
    change (μ (B j)).toReal ≤ K*q^(N+j)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hbound := norm_setIntegral_le_of_norm_le_const (f:=fun x ↦ |f x|) hfin
    (C:=g (j+1)) (fun x hx ↦ by simpa only [Real.norm_eq_abs,abs_abs] using hx.2)
  calc
    (∫ x in B j, |f x| ∂μ) ≤ ‖∫ x in B j, |f x| ∂μ‖ := le_abs_self _
    _ ≤ g (j+1) * μ.real (B j) := hbound
    _ ≤ g (j+1) * (K*q^(N+j)) := mul_le_mul_of_nonneg_left hreal (by dsimp [g]; positivity)
    _ ≤ r^(N+j) := by
      convert hB (N+j) (Nat.le_add_right N j) using 1
      push_cast
      dsimp [g]
      push_cast
      ring
    _ = r^N*r^j := pow_add _ _ _

/-- A geometric distribution bound at all square thresholds implies the integrated
root-exponential tail used by logarithmic quadrature. The measure may be infinite. -/
theorem hasIntegratedLogTail_of_geometric_sq (μ : Measure ℝ) {f : ℝ → ℝ}
    (hm : Measurable f) (hi : Integrable f μ) {A K q : ℝ} (hA : 0 < A) (hK : 0 < K)
    (hq : 0 < q) (hq1 : q < 1)
    (ht : ∀ n : ℕ, μ {x | A*((n:ℝ)+1)^2 < |f x|} ≤ ENNReal.ofReal (K*q^n)) :
    HasIntegratedLogTail μ f := by
  let r := (1+q)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hqr : q < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_quadratic_mul_geometric hA hK hq.le hqr)
  let c := -log r/(4*√A)
  have hc : 0 < c := div_pos (neg_pos.mpr (log_neg hr hr1)) (by positivity)
  refine ⟨(1-r)⁻¹,inv_pos.mpr (sub_pos.mpr hr1),c,hc,?_⟩
  filter_upwards [eventually_ge_atTop (A*(4*((M:ℝ)+1))^2)] with Y hY
  let x := √(Y/A)
  have hAb : 0 < √A := sqrt_pos.mpr hA
  have hx0 : 0 ≤ x := sqrt_nonneg _
  have hY0 : 0 ≤ Y := by exact (mul_nonneg hA.le (sq_nonneg _)).trans hY
  have hx : 4*((M:ℝ)+1) ≤ x := by
    have hh : (4*((M:ℝ)+1))^2 ≤ Y/A := (le_div_iff₀ hA).2 (by linarith)
    exact (le_sqrt (by positivity) (div_nonneg hY0 hA.le)).2 hh
  have hxsq : x^2 = Y/A := sq_sqrt (div_nonneg hY0 hA.le)
  let n := ⌊x/2⌋₊
  have hfloor : (n:ℝ) ≤ x/2 := Nat.floor_le (by positivity)
  have hceil : x/2 < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hn : M ≤ n := by
    exact_mod_cast (show (M:ℝ) ≤ n by nlinarith [Nat.cast_nonneg (α:=ℝ) M])
  have hlow : A*((n:ℝ)+1)^2 < Y := by
    have hlt : (n:ℝ)+1 < x := by linarith [Nat.cast_nonneg (α:=ℝ) M]
    have hh : ((n:ℝ)+1)^2 < x^2 := by gcongr
    rw [hxsq,lt_div_iff₀ hA] at hh
    linarith
  have hgeom := integrated_above_square μ hm hi hA hK hq.le hr hr1 ht
    (N:=n) (fun m hmn ↦ hM m (hn.trans hmn))
  have hlog : log r < 0 := log_neg hr hr1
  have hroot : √Y = √A*x := by
    dsimp [x]
    rw [←sqrt_mul hA.le, show A*(Y/A)=Y by field_simp]
  have hh : r^n ≤ exp (-c*√Y) := by
    rw [←exp_log (pow_pos hr n),log_pow]
    apply exp_monotone
    rw [hroot]
    have hx4 : x/4 ≤ (n:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) M]
    have hmono := mul_le_mul_of_nonpos_right hx4 hlog.le
    calc (n:ℝ)*log r ≤ (x/4)*log r := hmono
      _ = -c*(√A*x) := by dsimp [c]; field_simp
  calc
    (∫ t in {t | Y ≤ |f t|}, |f t| ∂μ) ≤ ∫ t in {t | A*((n:ℝ)+1)^2 < |f t|}, |f t| ∂μ :=
      setIntegral_mono_set hi.abs.integrableOn (ae_of_all _ fun t ↦ abs_nonneg _)
        (ae_of_all _ fun t ht ↦ hlow.trans_le ht)
    _ ≤ r^n*(1-r)⁻¹ := hgeom
    _ ≤ (1-r)⁻¹*exp (-c*√Y) := by
      rw [mul_comm ((1-r)⁻¹)]
      exact mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (sub_nonneg.mpr hr1.le))

/-- The dyadic square estimate in the form produced by the unit-interval logarithm bound. -/
theorem hasIntegratedLogTail_of_dyadic_sq (μ : Measure ℝ) {f : ℝ → ℝ}
    (hm : Measurable f) (hi : Integrable f μ)
    (h : ∃ A > 0, ∃ K > 0, ∀ n : ℕ, μ {x | A*((n:ℝ)+1)^2 < |f x|} ≤
      ENNReal.ofReal (K*(1/2:ℝ)^n)) :
    HasIntegratedLogTail μ f := by
  obtain ⟨A,hA,K,hK,ht⟩ := h
  exact hasIntegratedLogTail_of_geometric_sq μ hm hi hA hK (by norm_num) (by norm_num) ht

end RiemannMasullo.LogQuadrature
