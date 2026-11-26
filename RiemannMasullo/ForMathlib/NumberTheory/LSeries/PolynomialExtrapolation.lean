module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.FiniteTaylor
public import RiemannMasullo.ForMathlib.Analysis.Complex.WeightedVerticalStrip
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # Polynomial-length Dirichlet extrapolation from growing Taylor disks

The real part of the expansion center increases with the height bound. A finite
Dirichlet polynomial there has a tail proportional to a large inverse power of its
length. This compensates for extrapolation from the small disk to the critical line.
-/

@[expose] public noncomputable section
open Complex Filter Finset Metric Set
open Filter Function
open scoped Topology Asymptotics

namespace RiemannMasullo.PolynomialIdealSamples
open FiniteTaylor

/-- Absolute coefficient mass on the line of real part two. -/
def coefficientMass (b : ArithmeticFunction ℂ) : ℝ := ∑' m : ℕ, ‖LSeries.term b 2 m‖

/-- Moving the center far to the right gains an arbitrary integer inverse power
of the polynomial length, using only convergence at two. -/
theorem dirichlet_tail (b : ArithmeticFunction ℂ) (hb : LSeriesSummable b 2)
    {M : ℕ} (hM : 0 < M) (k : ℕ) (s : ℂ) (hs : 2+(k:ℝ) ≤ s.re) :
    ‖LSeries b s - dirichletPolynomial b M s‖ ≤ coefficientMass b/(M:ℝ)^k := by
  let g (m : ℕ) := ‖LSeries.term b 2 m‖
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hS := hb.of_re_le_re (s' := s) (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) k])
  have hterm (m : ℕ) (h : M ≤ m) : ‖LSeries.term b s m‖ ≤ ((M:ℝ)^k)⁻¹*g m := by
    have hm : 0 < m := hM.trans_le h
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hpow : (M:ℝ)^k*(m:ℝ)^(2:ℝ) ≤ (m:ℝ)^s.re := by
      calc _ ≤ (m:ℝ)^k*(m:ℝ)^(2:ℝ) := by gcongr
           _ = (m:ℝ)^(2+(k:ℝ)) := by rw [Real.rpow_add hm', Real.rpow_natCast]; ring
           _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h₁ hs
    have ht := div_le_div_of_nonneg_left (norm_nonneg (b m))
      (mul_pos (pow_pos hM' _) (Real.rpow_pos_of_pos hm' 2)) hpow
    dsimp only [g]
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hm.ne', ite_eq_right hm.ne']
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using ht
  have he : LSeries b s-dirichletPolynomial b M s = ∑' j : ℕ, LSeries.term b s (j+M) := by
    rw [LSeries, dirichletPolynomial_eq_partial_LSeries, ← hS.sum_add_tsum_nat_add M, add_sub_cancel_left]
  have htail : Summable (fun j : ℕ ↦ g (j+M)) := (summable_nat_add_iff _).mpr hb.norm
  have hsumg : Summable g := hb.norm
  have hsub : ∑' j : ℕ, g (j+M) ≤ ∑' j, g j :=
    (le_add_of_nonneg_left (Finset.sum_nonneg (s := range M) (f := g) fun _ _ ↦ norm_nonneg _)).trans_eq
      (hsumg.sum_add_tsum_nat_add M)
  rw [he]
  calc _ ≤ ∑' j : ℕ, ‖LSeries.term b s (j+M)‖ := norm_tsum_le_tsum_norm ((summable_nat_add_iff _).mpr hS).norm
       _ ≤ ∑' j : ℕ, ((M:ℝ)^k)⁻¹*g (j+M) :=
         (((summable_nat_add_iff _).mpr hS).norm).tsum_le_tsum (fun j ↦ hterm _ (by omega)) (htail.mul_left _)
       _ ≤ _ := by rw [tsum_mul_left, div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hsub (by positivity)

/-- Two moving Taylor disks. Their radii are `4r` and `r`, with target at distance `2r`. -/
theorem two_disks {f p : ℂ → ℂ} {c z : ℂ} {r U V : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4*r))) (hp : AnalyticOnNhd ℂ p (closedBall c r))
    (hU : ∀ w ∈ sphere c (4*r), ‖f w‖ ≤ U) (hV : ∀ w ∈ sphere c r, ‖f w-p w‖ ≤ V)
    (hV₀ : 0 ≤ V) (hz : ‖z-c‖ = 2*r) (K : ℕ) :
    ‖f z-taylorSum p c z K‖ ≤ 2*U/(2:ℝ)^K + V*(2:ℝ)^K := by
  have hbig := norm_sub_partial_le (by positivity : 0 < 4*r) hf hU (by rw [hz]; linarith) K
  rw [hz, show 2*r/(4*r) = (2:ℝ)⁻¹ by field_simp; ring, inv_pow] at hbig
  have he : U*((2:ℝ)^K)⁻¹/(1-(2:ℝ)⁻¹) = 2*U/(2:ℝ)^K := by ring
  rw [he] at hbig
  have hfc := hf c (mem_closedBall_self (by positivity))
  have hpc := hp c (mem_closedBall_self hr.le)
  have hs : AnalyticOnNhd ℂ (f-p) (closedBall c r) :=
    (hf.mono (closedBall_subset_closedBall (by linarith))).sub hp
  have hdiff : taylorSum f c z K-taylorSum p c z K = taylorSum (f-p) c z K := by
    rw [taylorSum, taylorSum, taylorSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [term, term, term, iteratedDeriv_sub hfc.contDiffAt hpc.contDiffAt, mul_sub]
  have hgeom (k : ℕ) : ∑ j ∈ range k, (2:ℝ)^j ≤ 2^k := by
    induction k with
    | zero => norm_num
    | succ k h => rw [Finset.sum_range_succ, pow_succ]; linarith
  have hsmall : ‖taylorSum f c z K-taylorSum p c z K‖ ≤ V*(2:ℝ)^K := by
    rw [hdiff, taylorSum]
    calc _ ≤ ∑ j ∈ range K, ‖term (f-p) c z j‖ := norm_sum_le _ _
         _ ≤ ∑ j ∈ range K, V*(2:ℝ)^j := Finset.sum_le_sum fun j _ ↦ by
           have h := norm_term_le (z := z) hr hs hV j
           simpa only [hz, mul_div_cancel_right₀ _ hr.ne'] using h
         _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hgeom _) hV₀
  exact (norm_sub_le_norm_sub_add_norm_sub (f z) (taylorSum f c z K) (taylorSum p c z K)).trans
    (add_le_add hbig hsmall)

def scale (j : ℕ) : ℕ := 2^j

def meshBlock (n : ℕ) : ℕ := Nat.log 2 (n+2)+1

/-- The rightmost successor of the consecutive grid also belongs to this height block. -/
theorem meshBlock_bounds (n : ℕ) :
    n+1 ≤ scale (meshBlock n) ∧ scale (meshBlock n) ≤ 2*(n+2) := by
  have hu := Nat.lt_pow_succ_log_self (by decide : 1<2) (n+2)
  have hl := Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  constructor
  · unfold scale meshBlock
    omega
  · unfold scale meshBlock
    rw [pow_succ]
    omega

def degree (D j : ℕ) : ℕ := (D+3)*(j+1)*scale j

def length (D j : ℕ) : ℕ := (2^(j+1))^(D+6)

theorem length_meshBlock_le (D n : ℕ) : length D (meshBlock n) ≤ (4*(n+2))^(D+6) := by
  apply Nat.pow_le_pow_left
  rw [pow_succ]
  have h := (meshBlock_bounds n).2
  unfold scale at h
  omega

def center (j : ℕ) (t : ℝ) : ℂ := ⟨4*(scale j : ℝ)+1/2,t⟩

def point (t : ℝ) : ℂ := ⟨1/2,t⟩

/-- A finite linear combination of the ordinary Dirichlet frequencies. -/
def sample (b : ArithmeticFunction ℂ) (D j : ℕ) (t : ℝ) : ℂ :=
  extrapolate b (degree D j) (length D j) (center j t) (point t-center j t)

/-- The required quantitative datum is a bound on the growing disks, with an
absolute constant in their `O(R log R)` logarithmic growth. -/
def DiskBound (G : ℂ → ℂ) (D j : ℕ) : Prop :=
  ∀ t : ℝ, |t| ≤ scale j → ∀ w ∈ sphere (center j t) (8*(scale j : ℝ)),
    ‖G w‖ ≤ (2:ℝ)^(D*(j+1)*scale j)

theorem norm_sub_sample (b : ArithmeticFunction ℂ) (hb : LSeriesSummable b 2)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 1 < w.re → G w = LSeries b w)
    (D j : ℕ) (hj : 2 ≤ scale j) (hbound : DiskBound G D j) (t : ℝ) (ht : |t| ≤ scale j) :
    ‖G (point t)-sample b D j t‖ ≤ (2+coefficientMass b)/(2:ℝ)^(3*(j+1)*scale j) := by
  let u := scale j
  let M := length D j
  let K := degree D j
  let U := (2:ℝ)^(D*(j+1)*u)
  let P := dirichletPolynomial b M
  have hu : (2:ℝ) ≤ u := by exact_mod_cast hj
  have hM : 0 < M := by dsimp [M,length]; positivity
  have hT : ‖point t-center j t‖ = 2*(2*(u:ℝ)) := by
    have he : point t-center j t = ((-(4*(u:ℝ)) : ℝ):ℂ) := by
      apply Complex.ext <;> simp [point,center,u,Complex.sub_re,Complex.sub_im]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    ring
  have hS (w : ℂ) (hw : w ∈ sphere (center j t) (2*(u:ℝ))) :
      ‖G w-P w‖ ≤ coefficientMass b/(M:ℝ)^u := by
    have hr := (Complex.abs_re_le_norm (w-center j t)).trans (mem_closedBall_iff_norm.mp (sphere_subset_closedBall hw))
    change |w.re-(4*(u:ℝ)+1/2)| ≤ 2*(u:ℝ) at hr
    have hs : 2+(u:ℝ) ≤ w.re := by linarith [(abs_le.mp hr).1]
    rw [hseries w (by linarith)]
    exact dirichlet_tail b hb hM u w hs
  have h := two_disks (U := U) (hV₀ := show 0 ≤ coefficientMass b/(M:ℝ)^u by
      unfold coefficientMass; positivity) (by positivity : 0 < 2*(u:ℝ))
      (fun w _ ↦ hG.analyticAt w) (fun w _ ↦ analytic_dirichletPolynomial b M w)
      (fun w hw ↦ hbound t ht w (by simpa only [show 4*(2*(u:ℝ)) = 8*(scale j:ℝ) by dsimp [u]; ring] using hw))
      hS hT K
  rw [taylorSum_dirichletPolynomial] at h
  have eK : (2:ℝ)^K = U * (2:ℝ)^(3*(j+1)*u) := by
    rw [← pow_add]
    congr 1
    dsimp [K,degree,u]
    ring
  have eM : (M:ℝ)^u = (2:ℝ)^K * (2:ℝ)^(3*(j+1)*u) := by
    dsimp [M,length]
    push_cast
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    dsimp [K,degree,u]
    ring
  refine h.trans ?_
  rw [eM, eK]
  dsimp only [U,u]
  apply le_of_eq
  field_simp

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- Width-dependent constants have exponential cost in the width. Once the
mesh is large enough they cost just one additional power in its logarithmic growth. -/
theorem diskBound_of_boundaries (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hpoly : ∀ a b : ℝ, a<b → ∃ M : ℝ,
      G =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|^M)
    (d : ℕ) (B K : ℝ) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hr : ∀ s : ℂ, 2 ≤ s.re → ‖G s‖ ≤ K)
    (hl : ∀ m : ℕ, 1 ≤ m → ∀ s : ℂ, s.re = 1/2-(m:ℝ) →
      ‖G s‖ ≤ K^(m+1)*(B+3*(m:ℝ)+|s.im|)^(d*m))
    (j : ℕ) (hj : K^5*(2*(B+40))^(4*d) ≤ scale j) : DiskBound G (4*d+1) j := by
  let u := scale j
  let m := 4*u
  let a : ℝ := 1/2-(m:ℝ)
  let h : ℝ := B+4*(m:ℝ)
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by decide : 0 < 2)
  have hur : (1:ℝ) ≤ u := by exact_mod_cast hu
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmr : (m:ℝ) = 4*(u:ℝ) := by dsimp [m]; push_cast; rfl
  have hab : a<2 := by dsimp only [a]; linarith
  have hh : 0 ≤ h := by dsimp only [h]; linarith
  have hbase : 1 ≤ a+h := by dsimp only [h,a]; linarith
  have hK₀ := zero_le_one.trans hK
  have hKr : K ≤ K^(m+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ m+1 by omega)
  have hconst : 1 ≤ (B+40)*(u:ℝ) := one_le_mul_of_one_le_of_one_le (by linarith) hur
  intro t ht w hw
  have hn : ‖w-center j t‖ = 8*(u:ℝ) := mem_sphere_iff_norm.mp hw
  have ha : a ≤ w.re := by
    have h₁ := Complex.abs_re_le_norm (w-center j t)
    change |w.re-(4*(u:ℝ)+1/2)| ≤ _ at h₁
    rw [hn] at h₁
    dsimp only [a]
    linarith [(abs_le.mp h₁).1]
  have hnwh : ‖w+(h:ℂ)‖ ≤ (B+40)*(u:ℝ) := by
    have h₀ := norm_add_le (w-center j t) (center j t)
    rw [sub_add_cancel,hn] at h₀
    have hc := Complex.norm_le_abs_re_add_abs_im (center j t)
    change _ ≤ |4*(u:ℝ)+1/2|+|t| at hc
    rw [abs_of_nonneg (by positivity)] at hc
    have hwadd := norm_add_le w (h:ℂ)
    rw [Complex.norm_real,Real.norm_of_nonneg hh] at hwadd
    dsimp only [h] at hwadd
    change |t| ≤ (u:ℝ) at ht
    have hbu : B ≤ B*(u:ℝ) := le_mul_of_one_le_right (zero_le_one.trans hB) hur
    linarith
  have hb : ‖G w‖ ≤ K^(m+1)*2^(d*m)*((B+40)*(u:ℝ))^(d*m) := by
    by_cases hw₂ : w.re ≤ 2
    · have left (s : ℂ) (hs : s.re=a) : ‖G s‖ ≤ K^(m+1)*(2*‖s+(h:ℂ)‖)^(d*m) := by
        refine (hl m hm s hs).trans ?_
        have hx := Complex.re_le_norm (s+(h:ℂ))
        have hy := Complex.abs_im_le_norm (s+(h:ℂ))
        simp only [Complex.add_re,Complex.ofReal_re,hs] at hx
        simp only [Complex.add_im,Complex.ofReal_im,add_zero] at hy
        have hcoef : B+3*(m:ℝ)+|s.im| ≤ 2*‖s+(h:ℂ)‖ := by dsimp only [a,h] at hx; linarith
        gcongr
      refine (weighted_vertical_strip G hG hab hbase (pow_nonneg hK₀ _) (d*m)
        (hpoly a 2 hab) left (fun s hs ↦ (hr s hs.ge).trans hKr) w ha hw₂).trans ?_
      gcongr
    · refine (hr w (le_of_not_ge hw₂)).trans (hKr.trans ?_)
      exact (le_mul_of_one_le_right (pow_nonneg hK₀ _) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hconst))
  have hku : K^(m+1) ≤ (K^5)^u := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hK (by dsimp [m]; omega)
  have hde : d*m = 4*d*u := by dsimp [m]; ring
  have hu2 : (u:ℝ) = (2:ℝ)^j := by dsimp [u,scale]; push_cast; rfl
  refine hb.trans ?_
  rw [hde]
  calc _ ≤ (K^5)^u*2^(4*d*u)*((B+40)*(u:ℝ))^(4*d*u) := by gcongr
       _ = (K^5*(2*(B+40))^(4*d))^u * (u:ℝ)^((4*d)*u) := by
            simp only [mul_pow,pow_mul]; ring
       _ ≤ (u:ℝ)^u * (u:ℝ)^((4*d)*u) := by
            gcongr
       _ = (2:ℝ)^(j*((4*d+1)*u)) := by
            rw [← pow_add,hu2,← pow_mul]; congr 1; ring
       _ ≤ _ := by
            apply pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
            change j*((4*d+1)*u) ≤ (4*d+1)*(j+1)*u
            nlinarith

end RiemannMasullo.PolynomialIdealSamples
