module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyCoefficientTable
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Approximation of the Hardy distance by finite least squares

Finite polynomial constraint sets exhaust all polynomials. Uniform estimates for the two
truncation errors then give convergence to the distance from the unit vector to the closed
polynomial multiples. The weighted ellipsoid uses only `2 * n + 2` input coefficients.
-/

@[expose] public noncomputable section

open Filter Finset Set
open scoped Topology BigOperators

namespace HardyTable

/-- The exact polynomial multiples, represented by their finite coefficient lists. -/
def multiples (c : H) : Set H := {y | ∃ (d : ℕ) (p : Coeff d), y = product c p}

def distance (c : H) : ℝ := Metric.infDist unitVector (closure (multiples c))

/-- The polynomial coefficient, extended by zero beyond its degree bound. -/
def coefficientAt {d : ℕ} (p : Coeff d) (i : ℕ) : ℂ := if h : i < d+1 then p ⟨i,h⟩ else 0

/-- Zero extension of a finite coefficient list. -/
def pad {d : ℕ} (p : Coeff d) (n : ℕ) : Coeff n := WithLp.toLp 2 fun k ↦ coefficientAt p k

private theorem sum_pad {G : Type*} [AddCommMonoid G] {d n : ℕ} (hd : d ≤ n)
    (p : Coeff d) (w : ℕ → ℂ → G) (hw : ∀ k, w k 0 = 0) :
    ∑ k : Fin (n+1), w k ((pad p n) k) = ∑ k : Fin (d+1), w k (p k) := by
  let a (k : ℕ) := w k (coefficientAt p k)
  change (∑ k : Fin (n+1), a k) = _
  calc
    _ = ∑ k ∈ range (n+1), a k := Fin.sum_univ_eq_sum_range a _
    _ = ∑ k ∈ range (d+1), a k := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hk
      simp only [Finset.mem_range] at hk
      simp only [a, coefficientAt, dite_eq_right hk, hw]
    _ = ∑ k : Fin (d+1), a k := (Fin.sum_univ_eq_sum_range a _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [a,coefficientAt,dite_eq_left k.isLt]

theorem product_pad {d n : ℕ} (hd : d ≤ n) (c : H) (p : Coeff d) :
    product c (pad p n) = product c p := sum_pad hd p (fun k a ↦ a • shift c k) (by simp)

theorem norm_pad {d n : ℕ} (hd : d ≤ n) (p : Coeff d) : ‖pad p n‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  exact sum_pad hd p (fun _ a ↦ ‖a‖^2) (by simp)

theorem weightedEnergy_pad {d n : ℕ} (hd : d ≤ n) (p : Coeff d) :
    weightedEnergy (pad p n) = weightedEnergy p :=
  sum_pad hd p (fun k a ↦ (((k:ℝ)+1)*‖a‖)^2) (by simp)

/-- The minimum squared residual. Compact nonempty constraints guarantee attainment below. -/
def leastSquares {n : ℕ} (M : ℕ) (a : ℕ → ℂ) (S : Set (Coeff n)) : ℝ :=
  sInf ((fun p ↦ ‖visible M a p‖^2) '' S)

/-- Arbitrary changes beyond the observed coefficient cutoff leave the finite measurement identical. -/
theorem leastSquares_congr {n M : ℕ} {a b : ℕ → ℂ} (hab : ∀ j ≤ M, a j = b j)
    (S : Set (Coeff n)) : leastSquares M a S = leastSquares M b S := by
  have h : visible M a = (visible M b : Coeff n → Coeff M) := by
    funext p
    have hn := visible_perturb_le (d := n) (M := M) (ε := 0) (by norm_num)
      (a := a) (b := b) (fun j hj ↦ by simp [hab j hj]) p
    apply sub_eq_zero.mp
    apply norm_le_zero_iff.mp
    simpa using hn
  simp only [leastSquares,h]

theorem exists_leastSquares {n M : ℕ} (a : ℕ → ℂ) {S : Set (Coeff n)}
    (hc : IsCompact S) (hne : S.Nonempty) :
    ∃ p ∈ S, leastSquares M a S = ‖visible M a p‖^2 ∧
      ∀ q ∈ S, ‖visible M a p‖ ≤ ‖visible M a q‖ := by
  have hcont : Continuous (fun p : Coeff n ↦ ‖visible M a p‖^2) := by
    simp_rw [visible_norm_sq]
    fun_prop
  obtain ⟨p,hp,hm⟩ := hc.exists_isMinOn hne hcont.continuousOn
  refine ⟨p,hp,IsLeast.csInf_eq ?_,fun q hq ↦ (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hm hq)⟩
  exact ⟨⟨p,hp,rfl⟩,fun y ⟨q,hq,hy⟩ ↦ hy ▸ hm hq⟩

/-- Any compact finite-dimensional constraint exhaustion works with uniform vanishing norm error.
The observed rows and their coefficient approximations may vary independently with the stage. -/
theorem tendsto_leastSquares {c : H} (M : ℕ → ℕ) (a : ℕ → ℕ → ℂ) (S : (n : ℕ) → Set (Coeff n))
    (hc : ∀ n, IsCompact (S n)) (hne : ∀ n, (S n).Nonempty)
    (hexh : ∀ d (p : Coeff d), ∀ᶠ n in atTop, pad p n ∈ S n)
    {E : ℕ → ℝ} (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ p ∈ S n,
      |‖visible (M n) (a n) p‖ - ‖unitVector - product c p‖| ≤ E n) :
    Tendsto (fun n ↦ leastSquares (M n) (a n) (S n)) atTop (𝓝 ((distance c)^2)) := by
  choose best hS hv hmin using fun n ↦ exists_leastSquares (M := M n) (a n) (hc n) (hne n)
  suffices h : Tendsto (fun n ↦ ‖visible (M n) (a n) (best n)‖) atTop (𝓝 (distance c)) by
    simpa only [hv] using h.pow 2
  have hne' : (multiples c).Nonempty := ⟨product c (0 : Coeff 0), 0, 0, rfl⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : 0 < ε/2 := half_pos hε
  have hdist : Metric.infDist unitVector (multiples c) < distance c + ε/2 := by
    rw [distance, Metric.infDist_closure]; linarith
  obtain ⟨_,⟨d,q,rfl⟩,hq⟩ := (Metric.infDist_lt_iff hne').mp hdist
  rw [dist_eq_norm] at hq
  filter_upwards [hbound,hexh d q,eventually_ge_atTop d,hE.eventually_lt_const hpos] with n hb ha hd he
  have hl := Metric.infDist_le_dist_of_mem (x := unitVector)
    (show product c (best n) ∈ multiples c from ⟨n,best n,rfl⟩)
  rw [dist_eq_norm, ← Metric.infDist_closure] at hl
  change distance c ≤ _ at hl
  have hbest := abs_le.mp (hb _ (hS n))
  have hp := (abs_le.mp (hb _ ha)).2
  rw [product_pad hd] at hp
  have hm := hmin n _ ha
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end HardyTable

end

@[expose] public noncomputable section

open Filter Set Finset
open scoped Topology BigOperators

namespace HardyTable

/-- A row-specific certified uniform bound at the measured coefficient indices. -/
def Accurate (c : H) (M : ℕ → ℕ) (a : ℕ → ℕ → ℂ) (C : ℝ) : Prop :=
  ∀ n j, j ≤ M n → ‖a n j-c j‖ ≤ C * (1/2:ℝ)^(M n)

def cubicCut (n : ℕ) := (n+1)^3
def linearCut (n : ℕ) := 2*n+1

def ballBudget (n : ℕ) : Set (Coeff n) := Metric.closedBall 0 (n:ℝ)

def ellipsoid (n : ℕ) : Set (Coeff n) := {p | weightedEnergy p ≤ (n:ℝ)+1}

theorem ellipsoid_compact (n : ℕ) : IsCompact (ellipsoid n) := by
  apply (isCompact_closedBall (0 : Coeff n) (Real.sqrt (n+1))).of_isClosed_subset
  · apply isClosed_le _ continuous_const
    unfold weightedEnergy
    fun_prop
  · intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
    rw [EuclideanSpace.norm_sq_eq]
    refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) hp
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k.val) (norm_nonneg (p k))]

theorem ellipsoid_nonempty (n : ℕ) : (ellipsoid n).Nonempty := by
  refine ⟨0, ?_⟩
  simp [ellipsoid,weightedEnergy]
  positivity

/-- The two explicit error bounds for one admissible polynomial on a cubic table. -/
theorem ball_errors {c : H} {D C : ℝ} (hD : DerivativeBound c D) (hC : 0 ≤ C)
    {a : ℕ → ℕ → ℂ} (ha : Accurate c cubicCut a C) (n : ℕ) (p : Coeff n)
    (hp : p ∈ ballBudget n) :
    ‖tail (unitVector-product c p) (cubicCut n+1)‖ ≤
        n * Real.sqrt (n+1) * D / ((cubicCut n:ℝ)-n) ∧
    ‖visible (cubicCut n) (a n) p - visible (cubicCut n) c p‖ ≤
        n * Real.sqrt (((n:ℝ)+1)*((cubicCut n:ℝ)+1)) * (C*(1/2:ℝ)^(cubicCut n)) := by
  have hR : 0 < (cubicCut n:ℝ) - n := by unfold cubicCut; push_cast; ring_nf; positivity
  have hl : coeffOneNorm p ≤ n*Real.sqrt (n+1) := by
    have hn : ‖p‖ ≤ n := by simpa [ballBudget] using hp
    calc
      _ ≤ Real.sqrt (n+1) * ‖p‖ := coeffOneNorm_le_sqrt p
      _ ≤ Real.sqrt (n+1) * n := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := mul_comm _ _
  have he : 0 ≤ C*(1/2:ℝ)^(cubicCut n) := by positivity
  constructor
  · calc
      _ ≤ coeffOneNorm p * (D/((cubicCut n:ℝ)-n)) := hidden_le hD p hR le_rfl
      _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hl (div_nonneg hD.1 hR.le)
  · calc
      _ ≤ Real.sqrt ((cubicCut n:ℝ)+1) * (coeffOneNorm p * _) :=
        visible_perturb_le he (ha n) p
      _ ≤ Real.sqrt ((cubicCut n:ℝ)+1) * ((n*Real.sqrt (n+1))*(C*(1/2:ℝ)^(cubicCut n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hl he) (by positivity)
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)+1)]; ring

/-- Both errors for a table of coefficients 0 through 2n+1. -/
theorem ellipsoid_errors {c : H} {D C : ℝ} (hD : DerivativeBound c D) (hC : 0 ≤ C)
    {a : ℕ → ℕ → ℂ} (ha : Accurate c linearCut a C) (n : ℕ) (p : Coeff n)
    (hp : p ∈ ellipsoid n) :
    ‖tail (unitVector-product c p) (linearCut n+1)‖ ≤ 2*D/Real.sqrt (n+1) ∧
    ‖visible (linearCut n) (a n) p - visible (linearCut n) c p‖ ≤
        2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1)) * (C*(1/2:ℝ)^(linearCut n)) := by
  have hl := (coeffOneNorm_le_weighted p).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp) (by norm_num))
  have hR : (n:ℝ)+1 ≤ (linearCut n:ℝ)-n := by unfold linearCut; push_cast; linarith
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hs : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.2 hn
  have he : 0 ≤ C*(1/2:ℝ)^(linearCut n) := by positivity
  constructor
  · calc
      _ ≤ coeffOneNorm p * (D/((n:ℝ)+1)) := hidden_le hD p hn hR
      _ ≤ 2*Real.sqrt (n+1)*(D/(n+1)) :=
        mul_le_mul_of_nonneg_right hl (div_nonneg hD.1 hn.le)
      _ = _ := by field_simp; rw [Real.sq_sqrt hn.le]
  · calc
      _ ≤ Real.sqrt ((linearCut n:ℝ)+1) * (coeffOneNorm p * _) :=
        visible_perturb_le he (ha n) p
      _ ≤ Real.sqrt ((linearCut n:ℝ)+1) * ((2*Real.sqrt (n+1))*(C*(1/2:ℝ)^(linearCut n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hl he) (by positivity)
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)+1)]; ring

private theorem dyadic_tendsto (M : ℕ → ℕ) (hM : ∀ n, n ≤ M n) {C : ℝ} (hC : 0 ≤ C)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hscale : ∀ n, b n ≤ 2*((M n:ℝ)+1)^2) :
    Tendsto (fun n ↦ b n * (C*(1/2:ℝ)^(M n))) atTop (𝓝 0) := by
  have hM' : Tendsto M atTop atTop := tendsto_atTop_mono hM tendsto_id
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one 2
    (r := (1/2:ℝ)) (by norm_num) (by norm_num)).comp hM'
  apply squeeze_zero' (Eventually.of_forall fun n ↦ mul_nonneg (hb n) (by positivity)) _
    (by simpa only [mul_zero] using (hlim.const_mul (8*C)))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1:ℝ) ≤ M n := by exact_mod_cast (hn.trans (hM n))
  have hscale' : b n ≤ 8*(M n:ℝ)^2 := (hscale n).trans (by nlinarith [sq_nonneg ((M n:ℝ)-1)])
  change _ ≤ 8*C*((M n:ℝ)^2*(1/2:ℝ)^(M n))
  calc
    _ ≤ 8*(M n:ℝ)^2*(C*(1/2:ℝ)^(M n)) := mul_le_mul_of_nonneg_right hscale' (by positivity)
    _ = _ := by ring

private theorem norm_error_from_parts {d M : ℕ} {c : H} {a : ℕ → ℂ} {p : Coeff d}
    {v t : ℝ} (hv : ‖visible M a p - visible M c p‖ ≤ v)
    (ht : ‖tail (unitVector-product c p) (M+1)‖ ≤ t) :
    |‖visible M a p‖ - ‖unitVector-product c p‖| ≤ v+t := by
  have h := (abs_norm_sub_norm_le (visible M a p) (visible M c p)).trans hv
  rw [visible_eq_head,abs_le] at h
  have hh := head_le (unitVector-product c p) M
  have hfull := le_head_add_tail (unitVector-product c p) M
  have ht0 := (norm_nonneg _).trans ht
  rw [abs_le]
  constructor <;> linarith

private theorem add_one_tendsto : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
  tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop

private theorem sqrt_le_self' {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x, sq_nonneg (x-1)]

/-- With only 2n+2 measured coefficients, the true squared distance is the limit of finite
ellipsoid-constrained least squares. There is no inter-row compatibility assumption. -/
theorem linear_ellipsoid_tendsto {c : H} {D C : ℝ} (hD : DerivativeBound c D) (hC : 0 ≤ C)
    (a : ℕ → ℕ → ℂ) (ha : Accurate c linearCut a C) :
    Tendsto (fun n ↦ leastSquares (linearCut n) (a n) (ellipsoid n))
      atTop (𝓝 ((distance c)^2)) := by
  let b (n : ℕ) := 2 * Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))
  have hnM (n : ℕ) : n ≤ linearCut n := by unfold linearCut; omega
  have hlim := dyadic_tendsto linearCut hnM hC b (fun _ ↦ by dsimp [b]; positivity) (by
    intro n
    have hM : (1:ℝ) ≤ (linearCut n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) (linearCut n)]
    have hnm : (n:ℝ)+1 ≤ (linearCut n:ℝ)+1 := by exact_mod_cast (Nat.succ_le_succ (hnM n))
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hnm (by positivity : 0 ≤ (linearCut n:ℝ)+1))
    rw [← sq,Real.sqrt_sq (by positivity)] at hs
    dsimp [b]
    nlinarith [sq_nonneg ((linearCut n:ℝ)+1-1)])
  have htail := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp add_one_tendsto)).const_mul (2*D)
  have htail' : Tendsto (fun n : ℕ ↦ 2*D/Real.sqrt (n+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def,div_eq_mul_inv] using htail
  have hE := hlim.add htail'
  rw [zero_add] at hE
  refine tendsto_leastSquares linearCut a ellipsoid ellipsoid_compact ellipsoid_nonempty ?_ hE ?_
  · intro d p
    filter_upwards [eventually_ge_atTop d, add_one_tendsto.eventually_ge_atTop (weightedEnergy p)] with n hd hn
    change weightedEnergy (pad p n) ≤ _
    rwa [weightedEnergy_pad hd]
  · exact Eventually.of_forall fun n p hp ↦
      norm_error_from_parts (ellipsoid_errors hD hC ha n p hp).2 (ellipsoid_errors hD hC ha n p hp).1

/-- Cubic sampling with the Euclidean coefficient radius n has the same limit. -/
theorem cubic_ball_tendsto {c : H} {D C : ℝ} (hD : DerivativeBound c D) (hC : 0 ≤ C)
    (a : ℕ → ℕ → ℂ) (ha : Accurate c cubicCut a C) :
    Tendsto (fun n ↦ leastSquares (cubicCut n) (a n) (ballBudget n))
      atTop (𝓝 ((distance c)^2)) := by
  let b (n : ℕ) := (n:ℝ) * Real.sqrt (((n:ℝ)+1)*((cubicCut n:ℝ)+1))
  have hnM (n : ℕ) : n ≤ cubicCut n := by unfold cubicCut; nlinarith only [Nat.zero_le (n^3), Nat.zero_le (n^2)]
  have hlim := dyadic_tendsto cubicCut hnM hC b (fun _ ↦ by dsimp [b]; positivity) (by
    intro n
    have hn : (n:ℝ) ≤ (cubicCut n:ℝ) := by exact_mod_cast hnM n
    have hnm : (n:ℝ)+1 ≤ (cubicCut n:ℝ)+1 := by linarith
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hnm (by positivity : 0 ≤ (cubicCut n:ℝ)+1))
    rw [← sq,Real.sqrt_sq (by positivity)] at hs
    dsimp [b]
    have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) n)
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ (cubicCut n:ℝ)+1 by positivity),
      sq_nonneg ((cubicCut n:ℝ)+1)])
  have htail : Tendsto (fun n : ℕ ↦ D/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,Function.comp_def] using (tendsto_inv_atTop_zero.comp add_one_tendsto).const_mul D
  have hE := hlim.add htail
  rw [zero_add] at hE
  refine tendsto_leastSquares cubicCut a ballBudget (fun n ↦ isCompact_closedBall _ _) ?_ ?_ hE ?_
  · intro n
    exact ⟨0,by simp [ballBudget]⟩
  · intro d p
    filter_upwards [eventually_ge_atTop d, tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖p‖] with n hd hn
    simp [ballBudget, norm_pad hd, hn]
  · refine Eventually.of_forall fun n p hp ↦ norm_error_from_parts (ball_errors hD hC ha n p hp).2 ?_
    apply (ball_errors hD hC ha n p hp).1.trans
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hR : 0 < (cubicCut n:ℝ)-n := by unfold cubicCut; push_cast; ring_nf; positivity
    have hs := sqrt_le_self' (x := (n:ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hratio : (n:ℝ)*Real.sqrt (n+1)*((n:ℝ)+1) ≤ (cubicCut n:ℝ)-n := by
      have hstep := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) n)
      have hmul := mul_le_mul_of_nonneg_right hstep hn.le
      unfold cubicCut
      push_cast
      nlinarith [sq_nonneg (n:ℝ)]
    rw [div_le_div_iff₀ hR hn]
    nlinarith [mul_le_mul_of_nonneg_right hratio hD.1]

/-- Extend a supplied finite row by zero for use with the coefficient-table interface. -/
def extendRow {M : ℕ} (u : Fin (M+1) → ℂ) (j : ℕ) : ℂ :=
  if h : j < M+1 then u ⟨j,h⟩ else 0

/-- The linear schedule directly consumes finite rows of length 2n+2. -/
theorem linear_finiteRows_tendsto {c : H} {D C : ℝ} (hD : DerivativeBound c D) (hC : 0 ≤ C)
    (a : (n : ℕ) → Fin (linearCut n+1) → ℂ)
    (ha : ∀ n (j : Fin (linearCut n+1)), ‖a n j-c j‖ ≤ C*(1/2:ℝ)^(linearCut n)) :
    Tendsto (fun n ↦ leastSquares (linearCut n) (extendRow (a n)) (ellipsoid n))
      atTop (𝓝 ((distance c)^2)) := by
  apply linear_ellipsoid_tendsto hD hC
  intro n j hj
  simpa only [extendRow,dite_eq_left (Nat.lt_succ_of_le hj)] using ha n ⟨j,Nat.lt_succ_of_le hj⟩

end HardyTable

end

@[expose] public noncomputable section

open Filter Finset Set
open scoped Topology

namespace HardyTable

theorem norm_unitVector : ‖unitVector‖ = 1 := by
  rw [unitVector,lp.norm_single (by norm_num)]
  exact norm_one

private theorem product_zero (d : ℕ) (c : H) : product c (0 : Coeff d) = 0 := by
  simp [product]

private theorem zero_mem_multiples (c : H) : 0 ∈ multiples c :=
  ⟨0,0,(product_zero 0 c).symm⟩

/-- Every observed least-squares minimum lies in [0,1] as soon as the zero polynomial is feasible. -/
theorem leastSquares_mem_Icc {n M : ℕ} (a : ℕ → ℂ) {S : Set (Coeff n)} (hc : IsCompact S)
    (hz : 0 ∈ S) : leastSquares M a S ∈ Set.Icc 0 1 := by
  obtain ⟨p,hp,hval,hm⟩ := exists_leastSquares (M := M) a hc ⟨0,hz⟩
  have hzero : visible M a (0 : Coeff n) = head unitVector M := by
    ext j
    change _ = unitVector j
    simp [visible,unitVector_apply]
  have hle := hm 0 hz
  rw [hzero] at hle
  have hnorm := (head_le unitVector M).trans_eq norm_unitVector
  rw [hval]
  exact ⟨sq_nonneg _,by nlinarith [norm_nonneg (visible M a p)]⟩

/-- When the constant coefficient is zero, the distance equals one for every multiplier. -/
theorem distance_of_constant_zero {c : H} (hc : c 0 = 0) : distance c = 1 := by
  rw [distance,Metric.infDist_closure]
  apply le_antisymm
  · simpa [norm_unitVector] using Metric.infDist_le_dist_of_mem (x := unitVector) (zero_mem_multiples c)
  · apply (Metric.le_infDist ⟨0,zero_mem_multiples c⟩).2
    rintro y ⟨d,p,rfl⟩
    have hp : product c p 0 = 0 := by
      rw [product_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k.val ≤ 0
      · simp [hk,hc]
      · simp [hk]
    have h := lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (unitVector-product c p) 0
    simpa [dist_eq_norm,unitVector_apply,hp] using h

/-- The constant sequence of the function 1 generates the unit vector with a constant polynomial. -/
theorem distance_unit : distance unitVector = 0 := by
  have hm : unitVector ∈ multiples unitVector := by
    refine ⟨0,WithLp.toLp 2 (fun _ ↦ (1:ℂ)),?_⟩
    ext j
    simp [product_apply, unitVector_apply]
  rw [distance, Metric.infDist_closure]
  exact le_antisymm (by simpa using Metric.infDist_le_dist_of_mem (x := unitVector) hm)
    Metric.infDist_nonneg

end HardyTable

end
