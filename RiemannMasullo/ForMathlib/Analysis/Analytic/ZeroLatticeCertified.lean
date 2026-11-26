module

public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLattice
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Certified consecutive-magnitude lattice comparisons

Each magnitude table carries a fixed absolute error at every sampled node. Conservative
endpoint comparisons can discard only boundedly many exact acceptances on a compact set
of analytic finite-order germs. For a signed compact continuous test the resulting error in the normalized sums is
bounded by a constant divided by `n`.
-/

public noncomputable section

open Filter Set Topology
open scoped NNReal
namespace RiemannMasullo.AnalyticLattice

/-- Absolute error at resolution `n`. -/
def sampleError (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- Physical mesh coordinate at an integer index. -/
def samplePoint (n : ℕ) (k : ℤ) : ℝ := (k : ℝ) / (n : ℝ) ^ 2

/-- The needed finite input table includes the successor of the final index. -/
def AccurateMagnitudes (f : ℝ → ℂ) (A : ℕ → ℤ → ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ k ∈ Finset.Icc (-(n : ℤ) ^ 3) ((n : ℤ) ^ 3 + 1),
    |A n k - ‖f (samplePoint n k)‖| ≤ sampleError n

private def scope (n : ℕ) := Finset.Icc (-(n : ℤ) ^ 3) ((n : ℤ) ^ 3)

private def exactNodes (f : ℝ → ℂ) (n : ℕ) : Finset ℤ := by
  classical
  exact (scope n).filter fun k ↦ ((n : ℝ)+1) * ‖f (samplePoint n k)‖ <
    n * ‖f (samplePoint n (k+1))‖

/-- Finite indices whose lower successor magnitude exceeds the strict threshold applied
to the upper current magnitude. -/
def certifiedNodes (A : ℕ → ℤ → ℝ) (n : ℕ) : Finset ℤ := by
  classical
  exact (scope n).filter fun k ↦ ((n : ℝ)+1) * (A n k + sampleError n) <
    n * max 0 (A n (k+1) - sampleError n)

/-- Finite sum using only magnitude approximations and the prescribed absolute error. -/
def certifiedSum (A : ℕ → ℤ → ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ certifiedNodes A n, g (samplePoint n k)) / n

/-- Closed form of the fixed absolute error. -/
theorem sampleError_eq_pow (n : ℕ) : sampleError n = (1 / 2 : ℝ) ^ n := by rw [sampleError]

/-- Closed form of the mesh coordinate. -/
theorem samplePoint_eq_div (n : ℕ) (k : ℤ) : samplePoint n k = (k : ℝ) / (n : ℝ)^2 := by
  rw [samplePoint]

/-- The error bound is required at every grid point and its final successor. -/
theorem accurateMagnitudes_iff {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} :
    AccurateMagnitudes f A ↔ ∀ n : ℕ, 0 < n → ∀ k ∈ Finset.Icc (-(n : ℤ)^3) ((n : ℤ)^3+1),
      |A n k - ‖f (samplePoint n k)‖| ≤ sampleError n := by rw [AccurateMagnitudes]

/-- Expand the conservative sum into its finite comparison on consecutive integer indices. -/
theorem certifiedSum_eq_sum (A : ℕ → ℤ → ℝ) (g : ℝ → ℝ) (n : ℕ) :
    certifiedSum A g n =
      (∑ k ∈ (Finset.Icc (-(n : ℤ)^3) ((n : ℤ)^3)).filter (fun k : ℤ ↦
        ((n : ℝ)+1) * (A n k + sampleError n) <
          n * max 0 (A n (k+1) - sampleError n)), g (samplePoint n k)) / n := by
  classical
  rfl

private lemma exactSum_eq (f : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) :
    sampleSum f g n = (∑ k ∈ exactNodes f n, g (samplePoint n k)) / n := by
  classical
  rw [sampleSum_eq_sum]
  unfold exactNodes scope samplePoint
  push_cast
  rfl

private lemma errors {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ scope n) :
    |A n k - ‖f (samplePoint n k)‖| ≤ sampleError n ∧
      |A n (k+1) - ‖f (samplePoint n (k+1))‖| ≤ sampleError n := by
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
  exact ⟨hA n hn k (Finset.mem_Icc.mpr ⟨hl, by omega⟩),
    hA n hn (k+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)⟩

/-- A certified strict comparison of two approximate magnitudes certifies the corresponding
exact comparison using just the two error bounds. -/
theorem lt_of_certifiedComparison {a b x y ε : ℝ} (hy : 0 ≤ y) (ha : |a-x| ≤ ε) (hb : |b-y| ≤ ε)
    (n : ℕ) (h : ((n : ℝ)+1)*(a+ε) < n*max 0 (b-ε)) : ((n : ℝ)+1)*x < n*y := by
  have hx : x ≤ a+ε := by linarith [(abs_le.mp ha).1]
  have hlow : max 0 (b-ε) ≤ y := max_le hy (by linarith [(abs_le.mp hb).2])
  exact (mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ (n : ℝ)+1)).trans_lt
    (h.trans_le (mul_le_mul_of_nonneg_left hlow n.cast_nonneg))

private lemma certified_subset {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {n : ℕ} (hn : 0 < n) : certifiedNodes A n ⊆ exactNodes f n := by
  classical
  intro k hk
  obtain ⟨hs, htest⟩ := Finset.mem_filter.mp hk
  obtain ⟨he, he'⟩ := errors hA hn hs
  exact Finset.mem_filter.mpr ⟨hs, lt_of_certifiedComparison (norm_nonneg _) he he' n htest⟩

/-- Increasing the weight increases its certified finite sum. -/
theorem certifiedSum_mono (A : ℕ → ℤ → ℝ) {g h : ℝ → ℝ} (hgh : ∀ t, g t ≤ h t) (n : ℕ) :
    certifiedSum A g n ≤ certifiedSum A h n :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ ↦ hgh (samplePoint n k)) n.cast_nonneg

/-- The certified finite sum of a nonnegative weight is nonnegative. -/
theorem certifiedSum_nonneg (A : ℕ → ℤ → ℝ) {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (n : ℕ) :
    0 ≤ certifiedSum A g n :=
  div_nonneg (Finset.sum_nonneg fun k _ ↦ hg (samplePoint n k)) n.cast_nonneg

/-- Every certified finite sum is a lower bound for the exact strict sum of a
nonnegative weight, with no asymptotic hypothesis. -/
theorem certifiedSum_le {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) {n : ℕ} (hn : 0 < n) :
    certifiedSum A g n ≤ sampleSum f g n := by
  rw [certifiedSum, exactSum_eq]
  apply div_le_div_of_nonneg_right _ n.cast_nonneg
  exact Finset.sum_le_sum_of_subset_of_nonneg (certified_subset hA hn) fun k _ _ ↦ hg _

private lemma certify_of_margin {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ scope n)
    (hgap : (4*(n : ℝ)+2)*sampleError n <
      n * ‖f (samplePoint n (k+1))‖ - ((n : ℝ)+1)*‖f (samplePoint n k)‖) :
    k ∈ certifiedNodes A n := by
  classical
  obtain ⟨h₁, h₂⟩ := errors hA hn hk
  have hl : A n k + sampleError n ≤ ‖f (samplePoint n k)‖ + 2*sampleError n := by
    linarith [(abs_le.mp h₁).2]
  have hu : ‖f (samplePoint n (k+1))‖ - 2*sampleError n ≤ max 0 (A n (k+1)-sampleError n) :=
    (show _ ≤ A n (k+1) - sampleError n by linarith [(abs_le.mp h₂).1]).trans (le_max_right _ _)
  apply Finset.mem_filter.mpr ⟨hk, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (n : ℝ)+1),
    mul_le_mul_of_nonneg_left hu n.cast_nonneg]

private lemma factor_ratio {m : ℕ} {n y U V c K : ℝ} (hn : 0 < n) (hy : 1 ≤ y)
    (hc : 0 < c) (hcU : c ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K) (hΔ : |V - U| ≤ K / n^2) :
    1 + (m : ℝ)/y - ((m : ℝ)+1) * (K/c) / n^2 ≤ (1+1/y)^m * (V/U) := by
  have hy₀ : 0 < y := by linarith
  have hU := hc.trans_le hcU
  have hn₂ := sq_pos_of_pos hn
  have hunit : 1 - (K/c)/n^2 ≤ V/U := by
    apply (le_div_iff₀ hU).mpr
    have hle := mul_le_mul_of_nonneg_left hcU (div_nonneg (div_nonneg hK hc.le) hn₂.le)
    have heq : K/c/n^2*c = K/n^2 := by field_simp
    rw [heq] at hle
    linarith [(abs_le.mp hΔ).1]
  have hBern : 1+(m : ℝ)/y ≤ (1+1/y)^m := by
    rw [div_eq_mul_one_div (m : ℝ) y]
    exact one_add_mul_le_pow (by linarith [one_div_pos.mpr hy₀]) m
  have hsmall : (m : ℝ)/y ≤ m := (div_le_iff₀ hy₀).mpr (by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hy)])
  calc
    _ ≤ (1 + (m : ℝ)/y) * (1 - (K/c)/n^2) := by
      rw [mul_div_assoc]
      nlinarith [mul_le_mul_of_nonneg_right hsmall (div_nonneg (div_nonneg hK hc.le) hn₂.le)]
    _ ≤ (1+(m : ℝ)/y)*(V/U) := mul_le_mul_of_nonneg_left hunit (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hBern (div_nonneg hV hU.le)

private lemma eventually_error_lt (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (4*(n : ℝ)+2)*sampleError n < c/((n : ℝ)^(2*m+1)) := by
  have he := tendsto_pow_const_mul_const_pow_of_lt_one (2*m+2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  filter_upwards [he.eventually_lt_const (show 0 < c/6 by linarith),
    eventually_ge_atTop (1 : ℕ)] with n he hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  rw [lt_div_iff₀ (pow_pos hn₀ _)]
  change (n : ℝ) ^ (2*m+2) * sampleError n < c/6 at he
  have hp : (n : ℝ) ^ (2*m+2) = (n : ℝ)^(2*m+1) * n := pow_succ _ _
  rw [hp] at he
  have he₀ : 0 ≤ sampleError n := by dsimp [sampleError]; positivity
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hn₁) he₀) (pow_nonneg hn₀.le (2*m+1))]

private lemma factor_mesh_growth {f : ℝ → ℂ} {a : ℝ} {m : ℕ} (hf : AnalyticAt ℝ f a)
    (ho : analyticOrderAt f a = m) :
    ∃ c > 0, ∃ Q ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, 1 ≤ y → y ≤ (m : ℝ)*n →
      c*(y/(n : ℝ)^2)^m ≤ ‖f (a+y/(n : ℝ)^2)‖ ∧
      (1+(m : ℝ)/y-Q/(n : ℝ)^2)*‖f (a+y/(n : ℝ)^2)‖ ≤ ‖f (a+(y+1)/(n : ℝ)^2)‖ := by
  obtain ⟨u, hu, hu₀, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  let c := ‖u a‖ / 2
  have hp := norm_pos_iff.mpr hu₀
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨K, s, hs, hK⟩ := (show ContDiffAt ℝ 1 u a from hu.contDiffAt).exists_lipschitzOnWith
  have hnear := (hfac.and (hu.continuousAt.norm.tendsto.eventually_const_lt
    (show c < ‖u a‖ by dsimp [c]; linarith))).and hs
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨c, hc, ((m : ℝ)+1)*((K : ℝ)/c), by positivity, ?_⟩
  have large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
  filter_upwards [large 1, large (((m : ℝ)+1)/d)] with n hn hn' y hy hy'
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hn₂ := sq_pos_of_pos hn₀
  let T (v : ℝ) := a+v/(n : ℝ)^2
  have inside (v : ℝ) (hv : y ≤ v ∧ v ≤ y+1) : T v ∈ Metric.ball a d := by
    have hv₀ : 0 ≤ v := by linarith [hv.1]
    rw [Metric.mem_ball, Real.dist_eq, show T v - a = v / (n : ℝ)^2 by dsimp [T]; ring,
      abs_of_nonneg (div_nonneg hv₀ hn₂.le), div_lt_iff₀ hn₂]
    have hh := mul_lt_mul_of_pos_right ((div_lt_iff₀ hd).mp hn') hn₀
    nlinarith [hv.2]
  have i₁ := hball (inside y ⟨le_rfl, by linarith⟩)
  have i₂ := hball (inside (y+1) ⟨by linarith, le_rfl⟩)
  let U := ‖u (T y)‖
  let V := ‖u (T (y+1))‖
  have hU : c ≤ U := i₁.1.2.le
  have hV : 0 ≤ V := norm_nonneg _
  have hdist := hK.dist_le_mul _ i₂.2 _ i₁.2
  have hΔ : |V-U| ≤ K/(n : ℝ)^2 := by
    have hdist' : dist (T (y+1)) (T y) = 1/(n : ℝ)^2 := by
      rw [Real.dist_eq, show T (y+1) - T y = 1/(n : ℝ)^2 by dsimp [T]; ring,
        abs_of_pos (one_div_pos.mpr hn₂)]
    rw [hdist', ← div_eq_mul_one_div, dist_eq_norm] at hdist
    exact (abs_norm_sub_norm_le (u (T (y+1))) (u (T y))).trans hdist
  have hcoeff := factor_ratio (m := m) hn₀ hy hc hU hV K.coe_nonneg hΔ
  have hy₀ : 0 < y := by linarith
  have value (v : ℝ) (iv : y ≤ v ∧ v ≤ y+1) :
      ‖f (T v)‖ = (v/(n : ℝ)^2)^m * ‖u (T v)‖ := by
    rw [(hball (inside v iv)).1.1, norm_smul, Real.norm_eq_abs, abs_pow,
      show T v - a = v/(n : ℝ)^2 by dsimp [T]; ring,
      abs_of_nonneg (div_nonneg (by linarith [iv.1]) hn₂.le)]
  have v₁ := value y ⟨le_rfl, by linarith⟩
  have v₂ := value (y+1) ⟨by linarith, le_rfl⟩
  have hrat : (1+1/y)^m*(V/U)*‖f (T y)‖ = ‖f (T (y+1))‖ := by
    rw [v₁, v₂]
    change (1+1/y)^m*(V/U)*((y/(n : ℝ)^2)^m*U) = ((y+1)/(n : ℝ)^2)^m*V
    calc
      _ = ((1+1/y)*(y/(n : ℝ)^2))^m*V := by rw [mul_pow]; field_simp [(hc.trans_le hU).ne']
      _ = _ := by rw [show (1+1/y)*(y/(n : ℝ)^2) = (y+1)/(n : ℝ)^2 by field_simp]
  refine ⟨?_, (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans_eq hrat⟩
  rw [v₁,mul_comm c]
  exact mul_le_mul_of_nonneg_left hU (pow_nonneg (div_nonneg hy₀.le hn₂.le) _)

/-- At an order-`m` zero, outside a bounded number of end nodes the unrounded
comparison has a polynomially positive margin, uniform over the mesh phase. -/
theorem exists_factor_margin {f : ℝ → ℂ} {a : ℝ} {m : ℕ} (hf : AnalyticAt ℝ f a)
    (hm : 0 < m) (ho : analyticOrderAt f a = m) :
    ∃ B > 0, ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, 1 ≤ y → y < (m : ℝ)*n-B →
      c/(n : ℝ)^(2*m+1) ≤ n*‖f (a+(y+1)/(n : ℝ)^2)‖ -
        ((n : ℝ)+1)*‖f (a+y/(n : ℝ)^2)‖ := by
  obtain ⟨c,hc,Q,hQ,hg⟩ := factor_mesh_growth hf ho
  let D := Q+1
  let B := (m : ℝ)*D+2
  have hD : 0 < D := by dsimp [D]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  refine ⟨B,hB,c,hc,?_⟩
  filter_upwards [hg,eventually_gt_atTop (0 : ℕ)] with n h hn y hy hy'
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₂ := sq_pos_of_pos hn₀
  have hy₀ : 0 < y := by linarith
  have hyb : y < m*((n : ℝ)-D) := by dsimp [B] at hy'; linarith
  have hxy : 1/(n : ℝ) + D/(n : ℝ)^2 < (m : ℝ)/y := by
    rw [show 1/(n : ℝ) + D/(n : ℝ)^2 = ((n : ℝ)+D)/(n : ℝ)^2 by field_simp,
      div_lt_div_iff₀ hn₂ hy₀]
    nlinarith [mul_lt_mul_of_pos_right hyb (add_pos hn₀ hD), mul_nonneg hmp.le (sq_nonneg D)]
  obtain ⟨hl,hu⟩ := h y hy (by linarith)
  let X := ‖f (a+y/(n : ℝ)^2)‖
  have hscale : 1+1/(n : ℝ)+1/(n : ℝ)^2 ≤ 1+(m : ℝ)/y-Q/(n : ℝ)^2 := by
    dsimp only [D] at hxy
    rw [add_div] at hxy
    linarith
  have hgap := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hscale (norm_nonneg _)).trans hu) hn₀.le
  rw [← mul_assoc, show (n : ℝ)*(1+1/(n : ℝ)+1/(n : ℝ)^2) = n+1+1/(n : ℝ) by field_simp] at hgap
  have hlow : c/(n : ℝ)^(2*m) ≤ X := by
    apply le_trans _ hl
    rw [div_pow, ← pow_mul, ← mul_div_assoc, div_le_div_iff_of_pos_right (pow_pos hn₀ _)]
    exact le_mul_of_one_le_right hc.le (one_le_pow₀ hy)
  rw [pow_succ, ← div_div]
  apply (div_le_div_of_nonneg_right hlow hn₀.le).trans
  dsimp only [X]
  rw [div_eq_mul_one_div]
  linarith

/-- On a fixed interior range of the coordinate `v = n(t-a)`, the margin in the true
comparison is at least a positive constant times `n⁻ᵐ`. -/
theorem exists_interior_margin {f : ℝ → ℂ} {a δ : ℝ} {m : ℕ} (hf : AnalyticAt ℝ f a)
    (hm : 0 < m) (ho : analyticOrderAt f a = m) (hδ : 0 < δ) :
    ∃ d > 0, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ, δ ≤ v → v ≤ (m : ℝ)-δ →
      d/(n : ℝ)^m ≤ n*‖f (a+v/n+1/(n : ℝ)^2)‖ - ((n : ℝ)+1)*‖f (a+v/n)‖ := by
  obtain ⟨c,hc,Q,hQ,hg⟩ := factor_mesh_growth hf ho
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  let slack := δ/(2*m)
  have hslack : 0 < slack := by dsimp [slack]; positivity
  refine ⟨slack*c*δ^m,by positivity,?_⟩
  have large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
  filter_upwards [hg,large (1/δ),large (Q/slack)] with n h hn hQn v hv hv'
  have hn₀ : 0 < (n : ℝ) := by linarith [one_div_pos.mpr hδ]
  have hv₀ := hδ.trans_le hv
  have hvm : v ≤ m := by linarith
  have hvlarge : 1 ≤ (n : ℝ)*v := by
    nlinarith [(div_lt_iff₀ hδ).mp hn, mul_le_mul_of_nonneg_left hv hn₀.le]
  obtain ⟨hl,hu⟩ := h (n*v) hvlarge (by nlinarith [mul_le_mul_of_nonneg_left hvm hn₀.le])
  rw [show (n : ℝ)*v/(n : ℝ)^2 = v/n by field_simp] at hl hu
  rw [show a+((n : ℝ)*v+1)/(n : ℝ)^2 = a+v/n+1/(n : ℝ)^2 by field_simp; ring] at hu
  let X := ‖f (a+v/n)‖
  have h1 : 2*slack + 1 ≤ (m : ℝ)/v := by
    apply (le_div_iff₀ hv₀).mpr
    have hmul := mul_le_mul_of_nonneg_left hvm (div_nonneg hδ.le hmp.le)
    rw [div_mul_cancel₀ _ hmp.ne'] at hmul
    have he : 2*slack = δ/m := by dsimp [slack]; field_simp
    rw [he]
    linarith
  have h2 : Q/n ≤ slack := (div_le_iff₀ hn₀).mpr (by linarith [(div_lt_iff₀ hslack).mp hQn])
  have hcoef : (n : ℝ)+1+slack ≤ n*(1+(m : ℝ)/(n*v)-Q/(n : ℝ)^2) := by
    rw [show (n : ℝ)*(1+(m : ℝ)/(n*v)-Q/(n : ℝ)^2) = n+(m : ℝ)/v-Q/n by field_simp]
    linarith
  have hgap := mul_le_mul_of_nonneg_left hu hn₀.le
  rw [← mul_assoc] at hgap
  have hG := (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans hgap
  have hlow : c*(δ/n)^m ≤ X := (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg hδ.le hn₀.le) (div_le_div_of_nonneg_right hv hn₀.le) m) hc.le).trans hl
  have hscaled := mul_le_mul_of_nonneg_left hlow hslack.le
  change _ ≤ (n : ℝ)*‖f (a+v/n+1/(n : ℝ)^2)‖ - (n+1)*X
  rw [show slack*c*δ^m/(n : ℝ)^m = slack*(c*(δ/n)^m) by rw [div_pow]; ring]
  dsimp only [X] at *
  linarith

private def missing (f : ℝ → ℂ) (A : ℕ → ℤ → ℝ) (n : ℕ) (s : Set ℝ) : Finset ℤ := by
  classical
  exact ((exactNodes f n) \ (certifiedNodes A n)).filter (fun k ↦ samplePoint n k ∈ s)

private def inner (a b : ℝ) : Finset ℤ := Finset.Ioo ⌊a⌋ ⌈b⌉

private lemma inner_mem {a b : ℝ} {k : ℤ} : k ∈ inner a b ↔ a < (k : ℝ) ∧ (k : ℝ) < b := by
  simp [inner, Int.floor_lt, Int.lt_ceil]

private lemma inner_card {a b : ℝ} (hab : a < b) :
    b-a-1 ≤ ((inner a b).card : ℝ) := by
  have hi := Int.card_Ioo_of_lt _ _ (Int.floor_lt_ceil_of_lt hab)
  have he : ((inner a b).card : ℝ) = (⌈b⌉ : ℝ) - (⌊a⌋ : ℝ) - 1 := by exact_mod_cast hi
  rw [he]
  linarith [Int.floor_le a, Int.le_ceil b]

private lemma mem_true_local {f : ℝ → ℂ} {n : ℕ} (hn : 0 < (n : ℝ)) {a r : ℝ} {k : ℤ} :
    k ∈ accepted f a r n (-(a*(n : ℝ)^2)) ↔
      samplePoint n k ∈ Metric.ball a r ∧
      ((n : ℝ)+1)*‖f (samplePoint n k)‖ < n*‖f (samplePoint n (k+1))‖ := by
  have hp := sq_pos_of_pos hn
  have h₁ : a+((k : ℝ) + -(a*(n : ℝ)^2))/(n : ℝ)^2 = samplePoint n k := by
    dsimp [samplePoint]; field_simp; ring
  have h₂ : a+((k : ℝ) + -(a*(n : ℝ)^2)+1)/(n : ℝ)^2 = samplePoint n (k+1) := by
    dsimp [samplePoint]; push_cast; field_simp; ring
  rw [mem_accepted_iff, h₁, h₂]
  apply and_congr_left
  intro _
  rw [Metric.mem_ball, Real.dist_eq, abs_lt, samplePoint, lt_sub_iff_add_lt,
    sub_lt_iff_lt_add, lt_div_iff₀ hp, div_lt_iff₀ hp]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

private lemma bounded_missing_at_zero {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {a : ℝ} {m : ℕ} (hf : AnalyticAt ℝ f a) (hm : 0 < m) (ho : analyticOrderAt f a = m) :
    ∃ r > 0, ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ((missing f A n (Metric.ball a r)).card : ℝ) ≤ M := by
  classical
  obtain ⟨r, hr, H, hH, hupper⟩ := exists_accepted_card_bound hf hm ho
  obtain ⟨B,hB,c,hc,margin⟩ := exists_factor_margin hf hm ho
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨r, hr, H+B+2, ?_⟩
  have large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
  filter_upwards [large (m/r), large (|a|+r), large ((B+1)/m), margin,
    eventually_error_lt m hc, hupper r hr le_rfl] with n hw hclip hnlen hmar herr hup
  have hn₀ : 0 < (n : ℝ) := by linarith [abs_nonneg a]
  have hn : 0 < n := by exact_mod_cast hn₀
  have hn₂ := sq_pos_of_pos hn₀
  let phase := -(a*(n : ℝ)^2)
  let L := accepted f a r n phase
  let I := inner (1+a*(n : ℝ)^2) (m*(n : ℝ)-B+a*(n : ℝ)^2)
  have hinside (k : ℤ) (hk : k ∈ I) : k ∈ L ∧ k ∈ certifiedNodes A n := by
    let y := (k : ℝ)-a*(n : ℝ)^2
    obtain ⟨hl, hu⟩ := inner_mem.mp hk
    have hyl : 1 ≤ y := by dsimp [y]; linarith
    have hyu : y < m*(n : ℝ)-B := by dsimp [y]; linarith
    have hleft : a+y/(n : ℝ)^2 = samplePoint n k := by dsimp [samplePoint,y]; field_simp; ring
    have hright : a+(y+1)/(n : ℝ)^2 = samplePoint n (k+1) := by
      dsimp [samplePoint,y]; push_cast; field_simp; ring
    have hywidth : y/(n : ℝ)^2 < r := by
      rw [div_lt_iff₀ hn₂]
      nlinarith [mul_lt_mul_of_pos_right ((div_lt_iff₀ hr).mp hw) hn₀]
    have hx : samplePoint n k ∈ Metric.ball a r := by
      rw [← hleft, Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_nonneg (div_nonneg (by linarith) hn₂.le)]
      exact hywidth
    have hscope : k ∈ scope n := by
      have ht : |samplePoint n k| < (n : ℝ) := by
        calc
          _ = |(samplePoint n k-a)+a| := by rw [sub_add_cancel]
          _ ≤ |samplePoint n k-a|+|a| := abs_add_le _ _
          _ < n := by linarith [show |samplePoint n k-a| < r from hx]
      rw [samplePoint, abs_div, abs_of_pos hn₂, div_lt_iff₀ hn₂] at ht
      have hpow : (n : ℝ)*(n : ℝ)^2 = (n : ℝ)^3 := by ring
      rw [hpow] at ht
      exact Finset.mem_Icc.mpr (by exact_mod_cast And.intro (abs_lt.mp ht).1.le (abs_lt.mp ht).2.le)
    have hmarg := hmar y hyl hyu
    rw [hleft, hright] at hmarg
    have hcert := certify_of_margin hA hn hscope (herr.trans_le hmarg)
    exact ⟨(mem_true_local hn₀).mpr ⟨hx, (Finset.mem_filter.mp (certified_subset hA hn hcert)).2⟩, hcert⟩
  have hIL : I ⊆ L := fun k hk ↦ (hinside k hk).1
  have hsub : missing f A n (Metric.ball a r) ⊆ L \ I := by
    intro k hk
    obtain ⟨hmiss, hx⟩ := Finset.mem_filter.mp hk
    obtain ⟨hacc, hnot⟩ := Finset.mem_sdiff.mp hmiss
    exact Finset.mem_sdiff.mpr ⟨(mem_true_local hn₀).mpr
      ⟨hx, (Finset.mem_filter.mp hacc).2⟩, fun hi ↦ hnot (hinside k hi).2⟩
  have hcounts : (missing f A n (Metric.ball a r)).card + I.card ≤ L.card :=
    (Nat.add_le_add_right (Finset.card_le_card hsub) I.card).trans_eq (Finset.card_sdiff_add_card_eq_card hIL)
  have hcounts' : ((missing f A n (Metric.ball a r)).card : ℝ) + I.card ≤ L.card := by exact_mod_cast hcounts
  have hi := inner_card (a := 1+a*(n : ℝ)^2) (b := m*(n : ℝ)-B+a*(n : ℝ)^2) (by
    linarith [(div_lt_iff₀ hmp).mp hnlen])
  change _ ≤ (I.card : ℝ) at hi
  have hu : (L.card : ℝ) - m*(n : ℝ) ≤ H := (abs_le.mp (hup phase).1).2
  linarith

private lemma bounded_missing_at_regular {f : ℝ → ℂ} (A : ℕ → ℤ → ℝ)
    {a : ℝ} (hf : AnalyticAt ℝ f a) (ha : f a ≠ 0) :
    ∃ r > 0, ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ((missing f A n (Metric.ball a r)).card : ℝ) ≤ M := by
  classical
  have hp := norm_pos_iff.mpr ha
  let c := ‖f a‖ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨K, s, hs, hK⟩ := (show ContDiffAt ℝ 1 f a from hf.contDiffAt).exists_lipschitzOnWith
  have hnear := (show ∀ᶠ t in 𝓝 a, t ∈ s from hs).and (hf.continuousAt.norm.tendsto.eventually_const_lt
    (show c < ‖f a‖ by dsimp [c]; linarith))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨d/2, by positivity, 0, ?_⟩
  have large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
  filter_upwards [large 1, large (2/d), large ((K : ℝ)/c)] with n hn hd' hK'
  suffices he : missing f A n (Metric.ball a (d/2)) = ∅ by simp [he]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨hm, ht⟩ := Finset.mem_filter.mp hk
  have hp := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2
  let x := samplePoint n k
  let x' := samplePoint n (k+1)
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hstep : dist x' x = 1/(n : ℝ)^2 := by
    rw [Real.dist_eq]
    have hsub : x'-x = 1/(n : ℝ)^2 := by dsimp [x',x,samplePoint]; push_cast; ring
    rw [hsub, abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hn₀))]
  have hxd : x ∈ Metric.ball a d := (Metric.ball_subset_ball (by linarith) : Metric.ball a (d/2) ⊆ _) ht
  have hxd' : x' ∈ Metric.ball a d := by
    apply (dist_triangle x' x a).trans_lt
    rw [hstep]
    have hh : 1/(n : ℝ)^2 < d/2 := by
      rw [div_lt_iff₀ (sq_pos_of_pos hn₀)]
      nlinarith [(div_lt_iff₀ hd).mp hd', mul_nonneg (mul_nonneg hd.le hn₀.le) (by linarith : 0 ≤ (n : ℝ)-1)]
    linarith [Metric.mem_ball.mp ht]
  have hdiff := hK.dist_le_mul _ (hball hxd').1 _ (hball hxd).1
  rw [hstep, ← div_eq_mul_one_div, dist_eq_norm] at hdiff
  have hm := mul_le_mul_of_nonneg_left ((norm_sub_norm_le _ _).trans hdiff) hn₀.le
  have hred : (n : ℝ)*(K/(n : ℝ)^2) = K/(n : ℝ) := by field_simp
  rw [hred] at hm
  have hKc : (K : ℝ)/n < c := (div_lt_iff₀ hn₀).mpr (by linarith [(div_lt_iff₀ hc).mp hK'])
  change ((n : ℝ)+1)*‖f x‖ < n*‖f x'‖ at hp
  linarith [(hball hxd).2]

private lemma bounded_missing_on_compact {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {K : Set ℝ} (hK : IsCompact K) (hf : ∀ x ∈ K, AnalyticAt ℝ f x)
    (hfin : ∀ x ∈ K, analyticOrderAt f x ≠ ⊤) :
    ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ((missing f A n K).card : ℝ) ≤ M := by
  classical
  apply hK.induction_on (p := fun s ↦ ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ((missing f A n s).card : ℝ) ≤ M)
  · exact ⟨0, Eventually.of_forall fun n ↦ by simp [missing]⟩
  · intro s t hst ht
    obtain ⟨M, hM⟩ := ht
    refine ⟨M, hM.mono (fun n hn ↦ le_trans ?_ hn)⟩
    exact_mod_cast Finset.card_le_card (show missing f A n s ⊆ missing f A n t from
      fun k hk ↦ Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hst (Finset.mem_filter.mp hk).2⟩)
  · intro s t hs ht
    obtain ⟨M, hM⟩ := hs
    obtain ⟨N, hN⟩ := ht
    refine ⟨M+N, ?_⟩
    filter_upwards [hM,hN] with n hn hn'
    have he : missing f A n (s ∪ t) = missing f A n s ∪ missing f A n t := by
      ext k
      simp only [missing, Finset.mem_filter, Finset.mem_union, Set.mem_union]
      tauto
    rw [he]
    have hle : (((missing f A n s) ∪ (missing f A n t)).card : ℝ) ≤
        (missing f A n s).card + (missing f A n t).card := by exact_mod_cast Finset.card_union_le _ _
    linarith
  · intro a ha
    have localBound : ∃ r > 0, ∃ M : ℝ, ∀ᶠ n : ℕ in atTop,
        ((missing f A n (Metric.ball a r)).card : ℝ) ≤ M := by
      by_cases hz : f a = 0
      · have ho := (Nat.cast_analyticOrderNatAt (hfin a ha)).symm
        have hpos : 0 < analyticOrderNatAt f a := Nat.pos_of_ne_zero fun h ↦ by
          have hz' : analyticOrderAt f a = 0 := by rw [ho, h, Nat.cast_zero]
          exact (analyticOrderAt_eq_zero.mp hz').elim (fun h ↦ h (hf a ha)) (fun h ↦ h hz)
        exact bounded_missing_at_zero hA (hf a ha) hpos ho
      · exact bounded_missing_at_regular A (hf a ha) hz
    obtain ⟨r, hr, h⟩ := localBound
    exact ⟨Metric.ball a r, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr), h⟩

/-- Exponentially accurate conservative tests can miss only boundedly many exact
acceptances in the closed support of a compact continuous weight. Their weighted
sums therefore differ by at most a constant divided by `n`. -/
theorem exists_certified_error_bound {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {g : ℝ → ℝ} (hg : Continuous g) (hK : HasCompactSupport g)
    (hf : ∀ x ∈ tsupport g, AnalyticAt ℝ f x) (hfin : ∀ x ∈ tsupport g, analyticOrderAt f x ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, |sampleSum f g n - certifiedSum A g n| ≤ C / n := by
  classical
  obtain ⟨M,hM⟩ := bounded_missing_on_compact hA hK hf hfin
  obtain ⟨V,hV⟩ := hK.bddAbove_image hg.abs.continuousOn
  refine ⟨max M 0 * max V 0, mul_nonneg (le_max_right _ _) (le_max_right _ _), ?_⟩
  filter_upwards [hM,eventually_gt_atTop (0 : ℕ)] with n hM hn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  let T := missing f A n (tsupport g)
  have heq : (∑ k ∈ T, g (samplePoint n k)) =
      ∑ k ∈ exactNodes f n \ certifiedNodes A n, g (samplePoint n k) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs ↦ hnot (Finset.mem_filter.mpr ⟨hk,hs⟩)
  rw [exactSum_eq, certifiedSum, ← sub_div, ← Finset.sum_sdiff_eq_sub (certified_subset hA hn), ← heq,
    abs_div, abs_of_pos hn₀]
  apply div_le_div_of_nonneg_right _ hn₀.le
  calc
    _ ≤ ∑ k ∈ T, |g (samplePoint n k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ T, max V 0 := Finset.sum_le_sum fun k hk ↦
      (hV (mem_image_of_mem _ (Finset.mem_filter.mp hk).2)).trans (le_max_left _ _)
    _ = (T.card : ℝ)*max V 0 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hM.trans (le_max_left _ _)) (le_max_right _ _)

/-- The conservative finite data have the same signed compact limit as the exact
test, with the full analytic order at each real zero. -/
theorem tendsto_certifiedSum {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ} (hA : AccurateMagnitudes f A)
    {g : ℝ → ℝ} (hg : Continuous g) (hK : HasCompactSupport g)
    (hf : ∀ x ∈ tsupport g, AnalyticAt ℝ f x) (hfin : ∀ x ∈ tsupport g, analyticOrderAt f x ≠ ⊤) :
    Tendsto (certifiedSum A g) atTop
      (𝓝 (∑' z : {x : ℝ // f x = 0}, (analyticOrderNatAt f (z : ℝ) : ℝ) * g z)) := by
  obtain ⟨C, _, hbound⟩ := exists_certified_error_bound hA hg hK hf hfin
  have herr : Tendsto (fun n ↦ sampleSum f g n - certifiedSum A g n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hbound,(tendsto_const_div_atTop_nhds_zero_nat C).eventually_lt_const hε] with n hn hεn
    simpa only [Real.dist_eq, sub_zero] using hn.trans_lt hεn
  have h := (tendsto_sampleSum hg hK hf hfin).sub herr
  simpa only [sub_sub_cancel, sub_zero] using h

end RiemannMasullo.AnalyticLattice
