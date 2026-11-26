module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Residue
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # The extrapolation argument: Baker Lemmas 6 and 7, analytic part

Ported from HOL Light, Baker/extrap.ml (jrh13/hol-light, commit 1a0c0e6).

For an abstract family `f m` of entire functions indexed by multi-indices `m : ℕ → ℕ` and closed
under differentiation with coefficients, `D (f m) = ∑ i < n, c m i * f (m + e_i) + c0 m * f m`:
bounds for the derivatives from bounds for the family, the interpolation bound for the nodes
`1, …, R` of multiplicity `S + 1` with explicit constants, one extrapolation step and the
induction over a sequence of steps (Lemma 6), and the bound at the rational points `l / k` from
smallness at the nodes `1, …, X` (Lemma 7, analytic part).

Conventions of this file (the same in every statement): HOL's `Cx(&l)` for a natural number `l`
is the cast `(l : ℂ)`; `complex_derivative g = \z. …` is `deriv g = fun z => …`; a hypothesis
`A /\ B ==> C` under a quantifier is curried to `A → B → C`; HOL's `a * b / c`, which HOL parses
as `a * (b / c)`, is written with the same tokens and Lean's parse `(a * b) / c`. -/

@[expose] public section

namespace RiemannMasullo.Baker

open Finset
open scoped Nat

/-! ### Higher derivatives of a family closed under differentiation -/

/-- HOL Light: Baker/extrap.ml, HIGHER_COMPLEX_DERIVATIVE_VSUM. The higher derivative of a finite
sum of functions holomorphic on an open set is the sum of the higher derivatives. -/
theorem higher_complex_derivative_vsum {A : Type*} (f : A → ℂ → ℂ) (s : Set ℂ) (t : Finset A)
    (n : ℕ) (z : ℂ) (hs : IsOpen s) (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) s) (hz : z ∈ s) :
    iteratedDeriv n (fun w => ∑ i ∈ t, f i w) z = ∑ i ∈ t, iteratedDeriv n (f i) z :=
  iteratedDeriv_fun_sum fun i hi => ((hf i hi).contDiffOn hs).contDiffAt (hs.mem_nhds hz)

/-- HOL Light: Baker/extrap.ml, HIGHER_COMPLEX_DERIVATIVE_LINCOMB. The higher derivative of a
linear combination `∑ i ∈ s, a i * g i + b * h` of entire functions. -/
theorem higher_complex_derivative_lincomb {A : Type*} (g : A → ℂ → ℂ) (h : ℂ → ℂ) (a : A → ℂ)
    (b : ℂ) (s : Finset A) (j : ℕ) (z : ℂ) (hg : ∀ i ∈ s, Differentiable ℂ (g i))
    (hh : Differentiable ℂ h) :
    iteratedDeriv j (fun w => ∑ i ∈ s, a i * g i w + b * h w) z =
      ∑ i ∈ s, a i * iteratedDeriv j (g i) z + b * iteratedDeriv j h z := by
  have hcd : ∀ {u : ℂ → ℂ}, Differentiable ℂ u → ContDiffAt ℂ j u z := fun hu =>
    (hu.differentiableOn.contDiffOn isOpen_univ).contDiffAt (isOpen_univ.mem_nhds (Set.mem_univ z))
  have h1 : ContDiffAt ℂ j (fun w => ∑ i ∈ s, a i * g i w) z :=
    hcd (Differentiable.fun_sum fun i hi => (differentiable_const _).mul (hg i hi))
  have h2 : ContDiffAt ℂ j (fun w => b * h w) z := hcd ((differentiable_const _).mul hh)
  rw [iteratedDeriv_fun_add h1 h2,
    higher_complex_derivative_vsum (fun i w => a i * g i w) Set.univ s j z isOpen_univ
      (fun i hi => ((differentiable_const _).mul (hg i hi)).differentiableOn) (Set.mem_univ z)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp
  · simp

/-- HOL Light: Baker/extrap.ml, NSUM_INCREMENT. Raising one entry `i ∈ s` of a multi-index by one
raises its sum over `s` by one. -/
theorem nsum_increment (s : Finset ℕ) (m : ℕ → ℕ) (i : ℕ) (hi : i ∈ s) :
    ∑ r ∈ s, (if r = i then m r + 1 else m r) = ∑ r ∈ s, m r + 1 := by
  have h : ∀ r ∈ s, (if r = i then m r + 1 else m r) = m r + if r = i then 1 else 0 :=
    fun r _ => by split_ifs <;> rfl
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq' s i]
  simp [hi]

/-- HOL Light: Baker/extrap.ml, DERIVATIVE_FAMILY_BOUND_COEFF. If the family is closed under
differentiation with coefficients of norm sum at most `N` and all members with `|m| ≤ S` are at
most `eps` at `z`, then the `j`-th derivative of `f m` at `z` is at most `N ^ j * eps` whenever
`|m| + j ≤ S`.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses). -/
theorem derivative_family_bound_coeff (f : (ℕ → ℕ) → ℂ → ℂ) (c : (ℕ → ℕ) → ℕ → ℂ)
    (c0 : (ℕ → ℕ) → ℂ) (n S N : ℕ) (eps : ℝ) (z : ℂ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun w =>
      ∑ i ∈ Finset.range (n - 1 + 1), c m i * f (fun r => if r = i then m r + 1 else m r) w +
        c0 m * f m w)
    (hN : ∀ m, ∑ r ∈ Finset.range (n - 1 + 1), m r < S →
      ∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ + ‖c0 m‖ ≤ (N : ℝ))
    (he : ∀ m, ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S → ‖f m z‖ ≤ eps) :
    ∀ j m, ∑ r ∈ Finset.range (n - 1 + 1), m r + j ≤ S →
      ‖iteratedDeriv j (f m) z‖ ≤ (N : ℝ) ^ j * eps := by
  have _ := hn
  have heps : 0 ≤ eps := (norm_nonneg _).trans (he (fun _ => 0) (by simp))
  intro j
  induction j with
  | zero =>
    intro m hm
    simpa using he m (by omega)
  | succ j ih =>
    intro m hm
    rw [iteratedDeriv_succ', hD m,
      higher_complex_derivative_lincomb _ _ _ _ _ _ _ (fun i _ => hf _) (hf m)]
    have hNm := hN m (by omega)
    have hpos : 0 ≤ (N : ℝ) ^ j * eps := by positivity
    calc ‖∑ i ∈ Finset.range (n - 1 + 1),
            c m i * iteratedDeriv j (f (fun r => if r = i then m r + 1 else m r)) z +
          c0 m * iteratedDeriv j (f m) z‖
        ≤ ∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ * ((N : ℝ) ^ j * eps) +
          ‖c0 m‖ * ((N : ℝ) ^ j * eps) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i hi => ?_)) ?_)
          · rw [norm_mul]
            refine mul_le_mul_of_nonneg_left (ih _ ?_) (norm_nonneg _)
            rw [nsum_increment _ m i hi]
            omega
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (ih m (by omega)) (norm_nonneg _)
      _ = (∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ + ‖c0 m‖) * ((N : ℝ) ^ j * eps) := by
          rw [add_mul, Finset.sum_mul]
      _ ≤ (N : ℝ) * ((N : ℝ) ^ j * eps) := mul_le_mul_of_nonneg_right hNm hpos
      _ = (N : ℝ) ^ (j + 1) * eps := by ring

/-! ### Elementary estimates -/

private theorem extrap_real_abs_sub_num_ge_1 (m n : ℕ) (h : m ≠ n) :
    (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by linarith))
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by linarith))

private theorem extrap_norm_natCast_sub (x y : ℕ) :
    ‖(x : ℂ) - (y : ℂ)‖ = |(x : ℝ) - (y : ℝ)| := by
  have : (x : ℂ) - (y : ℂ) = (((x : ℝ) - (y : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]

private theorem extrap_nproduct_shift_binom (s h : ℕ) :
    ∏ j ∈ Finset.Icc 1 h, (s + j) = h ! * (s + h).choose h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, ← add_assoc]
    have := Nat.add_one_mul_choose_eq (s + h) h
    calc h ! * (s + h).choose h * (s + h + 1) = h ! * ((s + h + 1) * (s + h).choose h) := by ring
      _ = h ! * ((s + h + 1).choose (h + 1) * (h + 1)) := by rw [this]
      _ = (h + 1) * h ! * (s + h + 1).choose (h + 1) := by ring

private theorem extrap_nproduct_shift_delete_bound (W R r : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hRW : R ≤ W) :
    (∏ b ∈ Finset.Icc 1 R, (W + b)) * 2 ^ (R - 1) ≤ W * 16 ^ W * (r - 1)! * (R - r)! := by
  rw [extrap_nproduct_shift_binom]
  have hfact : R ! = R * ((R - 1).choose (R - r) * (R - r)! * (r - 1)!) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := R - 1) (k := R - r) (by omega)
    rw [show R - 1 - (R - r) = r - 1 by omega] at h
    rw [h]
    cases R with
    | zero => omega
    | succ k => simp [Nat.factorial_succ]
  have hc1 : (R - 1).choose (R - r) ≤ 2 ^ (R - 1) := Nat.choose_le_two_pow _ _
  have hc2 : (W + R).choose R ≤ 2 ^ (W + R) := Nat.choose_le_two_pow _ _
  have hpow : 2 ^ (R - 1) * 2 ^ (W + R) * 2 ^ (R - 1) ≤ 16 ^ W := by
    rw [← pow_add, ← pow_add, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hfact]
  calc R * ((R - 1).choose (R - r) * (R - r)! * (r - 1)!) * (W + R).choose R * 2 ^ (R - 1)
      ≤ R * (2 ^ (R - 1) * (R - r)! * (r - 1)!) * 2 ^ (W + R) * 2 ^ (R - 1) := by gcongr
    _ = (2 ^ (R - 1) * 2 ^ (W + R) * 2 ^ (R - 1)) * (R * ((r - 1)! * (R - r)!)) := by ring
    _ ≤ 16 ^ W * (W * ((r - 1)! * (R - r)!)) := by gcongr
    _ = W * 16 ^ W * (r - 1)! * (R - r)! := by ring

private theorem extrap_prod_cast_Icc (k : ℕ) : ∏ c ∈ Finset.Icc 1 k, (c : ℝ) = (k ! : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    push_cast
    ring

private theorem extrap_product_abs_diff_delete (r R : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R) :
    ∏ b ∈ (Finset.Icc 1 R).erase r, |(r : ℝ) - (b : ℝ)| =
      ((r - 1)! : ℝ) * ((R - r)! : ℝ) := by
  have hsplit : (Finset.Icc 1 R).erase r = Finset.Icc 1 (r - 1) ∪ Finset.Icc (r + 1) R := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (r - 1)) (Finset.Icc (r + 1) R) :=
    Finset.disjoint_left.2 fun x h1 h2 => by
      simp only [Finset.mem_Icc] at h1 h2
      omega
  rw [hsplit, Finset.prod_union hdisj, ← extrap_prod_cast_Icc, ← extrap_prod_cast_Icc]
  congr 1
  · refine Finset.prod_nbij' (fun b => r - b) (fun c => r - c) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      have hbr : (b : ℝ) ≤ r := by exact_mod_cast (by omega : b ≤ r)
      rw [Nat.cast_sub (by omega), abs_of_nonneg (by linarith)]
  · refine Finset.prod_nbij' (fun b => b - r) (fun c => c + r) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      have hbr : (r : ℝ) ≤ b := by exact_mod_cast (by omega : r ≤ b)
      rw [Nat.cast_sub (by omega), abs_sub_comm, abs_of_nonneg (by linarith)]

private theorem extrap_real_pow_ratio_inv_le (x y c e : ℝ) (k : ℕ) (hx : 0 ≤ x)
    (hxc : x ≤ c * y) (hy : 0 < y) (he : 0 < e) :
    x ^ k * (e⁻¹ * y ^ k)⁻¹ ≤ e * c ^ k := by
  have hyk : 0 < y ^ k := pow_pos hy k
  have h1 : x ^ k ≤ c ^ k * y ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx hxc k
  have e1 : x ^ k * (e⁻¹ * y ^ k)⁻¹ = e * (x ^ k / y ^ k) := by
    rw [mul_inv, inv_inv]
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hyk).2 h1) he.le

/-! ### Interpolation bound for a finite set of nodes of multiplicity `S + 1` -/

private theorem extrap_circle_nodes_lower_bound (s : Finset ℂ) (w z : ℂ) (t : ℕ) (rho : ℝ)
    (hw : ‖w‖ ≤ rho / 2) (hs : ∀ a ∈ s, ‖a‖ ≤ rho / 2) (hz : ‖z‖ = rho) :
    (rho / 2) * (rho / 2) ^ (s.card * (t + 1)) ≤
      ‖(z - w) * ∏ a ∈ s, (z - a) ^ (t + 1)‖ := by
  have h0 : 0 ≤ rho / 2 := (norm_nonneg _).trans hw
  have hsub : ∀ a : ℂ, ‖a‖ ≤ rho / 2 → rho / 2 ≤ ‖z - a‖ := fun a ha => by
    have := norm_sub_norm_le z a
    linarith
  rw [norm_mul, norm_prod]
  have hpow : (rho / 2) ^ (s.card * (t + 1)) = ∏ _a ∈ s, (rho / 2) ^ (t + 1) := by
    rw [Finset.prod_const, ← pow_mul, mul_comm]
  rw [hpow]
  refine mul_le_mul (hsub w hw) (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun a ha => ?_)
    (Finset.prod_nonneg fun _ _ => by positivity) (norm_nonneg _)
  rw [norm_pow]
  exact pow_le_pow_left₀ h0 (hsub a (hs a ha)) _

private theorem extrap_small_circle_nodes_upper_bound (s : Finset ℂ) (w a z : ℂ) (d : ℝ)
    (t : ℕ) (hd : 0 < d) (hwa : 2 * d ≤ ‖w - a‖)
    (hab : ∀ b ∈ s, b ≠ a → 2 * d ≤ ‖a - b‖) (hz : ‖z - a‖ = d) :
    ‖((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹‖ ≤
      (d * (∏ b ∈ s.erase a, ‖a - b‖ / 2) ^ (t + 1))⁻¹ := by
  have hQ : 0 < ∏ b ∈ s.erase a, ‖a - b‖ / 2 := Finset.prod_pos fun b hb => by
    have := hab b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
    linarith
  rw [norm_inv, norm_mul, norm_prod]
  simp only [norm_pow]
  rw [Finset.prod_pow]
  refine inv_anti₀ (mul_pos hd (pow_pos hQ _)) ?_
  have h1 : d ≤ ‖z - w‖ := by
    have h := norm_add_le (w - z) (z - a)
    rw [show w - z + (z - a) = w - a by ring, norm_sub_rev w z] at h
    linarith
  have h2 : ∏ b ∈ s.erase a, ‖a - b‖ / 2 ≤ ∏ b ∈ s.erase a, ‖z - b‖ :=
    Finset.prod_le_prod₀ (fun _ _ => by positivity) fun b hb => by
      have hb' := hab b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
      have h := norm_add_le (a - z) (z - b)
      rw [show a - z + (z - b) = a - b by ring, norm_sub_rev a z] at h
      linarith
  exact mul_le_mul h1 (pow_le_pow_left₀ hQ.le h2 _) (pow_nonneg hQ.le _) (norm_nonneg _)

private theorem extrap_taylor_coeff_sum_bound (g : ℕ → ℝ) (n S : ℕ) (eps u d : ℝ)
    (heps : 0 ≤ eps) (hu : 0 ≤ u) (hd : 0 < d) (hd1 : d ≤ 1)
    (hg : ∀ j, j ≤ S → g j ≤ (n : ℝ) ^ j * eps) :
    ∑ j ∈ Finset.range (S + 1), g j / (j ! : ℝ) * u / d ^ (S - j) ≤
      eps * u * d⁻¹ ^ S * Real.exp n := by
  have hdi : 1 ≤ d⁻¹ := (one_le_inv₀ hd).2 hd1
  have hdi0 : 0 ≤ d⁻¹ := by positivity
  calc ∑ j ∈ Finset.range (S + 1), g j / (j ! : ℝ) * u / d ^ (S - j)
      ≤ ∑ j ∈ Finset.range (S + 1), (n : ℝ) ^ j / (j ! : ℝ) * (eps * u * d⁻¹ ^ S) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ S := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hfac : (0 : ℝ) < (j ! : ℝ) := by positivity
        have h1 : g j / (j ! : ℝ) ≤ (n : ℝ) ^ j * eps / (j ! : ℝ) :=
          div_le_div_of_nonneg_right (hg j hj') hfac.le
        have h2 : d⁻¹ ^ (S - j) ≤ d⁻¹ ^ S := pow_le_pow_right₀ hdi (Nat.sub_le _ _)
        calc g j / (j ! : ℝ) * u / d ^ (S - j) = g j / (j ! : ℝ) * (u * d⁻¹ ^ (S - j)) := by
              rw [inv_pow]
              ring
          _ ≤ (n : ℝ) ^ j * eps / (j ! : ℝ) * (u * d⁻¹ ^ S) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hu)
                (mul_nonneg hu (pow_nonneg hdi0 _)) (by positivity)
          _ = (n : ℝ) ^ j / (j ! : ℝ) * (eps * u * d⁻¹ ^ S) := by ring
    _ = (∑ j ∈ Finset.range (S + 1), (n : ℝ) ^ j / (j ! : ℝ)) * (eps * u * d⁻¹ ^ S) := by
        rw [Finset.sum_mul]
    _ ≤ Real.exp n * (eps * u * d⁻¹ ^ S) :=
        mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) _)
          (by positivity)
    _ = eps * u * d⁻¹ ^ S * Real.exp n := by ring

private theorem extrap_interpolation_nodes_bound (f : ℂ → ℂ) (s : Finset ℂ) (S : ℕ) (w : ℂ)
    (rho d M eps : ℝ) (n : ℕ) (hf : Differentiable ℂ f) (hrho : 0 < rho)
    (hw : ‖w‖ ≤ rho / 2) (hs : ∀ a ∈ s, ‖a‖ ≤ rho / 2) (hd : 0 < d) (hd1 : d ≤ 1)
    (hwa : ∀ a ∈ s, 2 * d ≤ ‖w - a‖)
    (hab : ∀ a ∈ s, ∀ b ∈ s, b ≠ a → 2 * d ≤ ‖a - b‖)
    (hM : ∀ z, ‖z‖ = rho → ‖f z‖ ≤ M) (heps : 0 ≤ eps)
    (hder : ∀ a ∈ s, ∀ j, j ≤ S → ‖iteratedDeriv j f a‖ ≤ (n : ℝ) ^ j * eps) :
    ‖f w‖ ≤ ‖∏ a ∈ s, (w - a) ^ (S + 1)‖ *
        (rho * M / ((rho / 2) * (rho / 2) ^ (s.card * (S + 1)))) +
      eps * d⁻¹ ^ S * Real.exp n *
        ∑ a ∈ s, ‖∏ b ∈ s, (w - b) ^ (S + 1)‖ *
          (d * (∏ b ∈ s.erase a, ‖a - b‖ / 2) ^ (S + 1))⁻¹ := by
  have hws : w ∉ s := fun h => by
    have := hwa w h
    rw [sub_self, norm_zero] at this
    linarith
  have hU0 : ∀ a : ℂ, 0 ≤ (d * (∏ b ∈ s.erase a, ‖a - b‖ / 2) ^ (S + 1))⁻¹ := fun a =>
    inv_nonneg.2 (mul_nonneg hd.le (pow_nonneg (Finset.prod_nonneg fun _ _ => by positivity) _))
  have hmu : 0 < (rho / 2) * (rho / 2) ^ (s.card * (S + 1)) := by positivity
  have key := interpolation_residue_bound f s S w 0 rho d M
    ((rho / 2) * (rho / 2) ^ (s.card * (S + 1)))
    (fun a => (d * (∏ b ∈ s.erase a, ‖a - b‖ / 2) ^ (S + 1))⁻¹) hf hws
    (by rw [sub_zero]; linarith)
    (fun a ha => by rw [sub_zero]; linarith [hs a ha]) hd
    (fun a ha => ⟨by linarith [hwa a ha], fun b hb hne => by
      have := hab a ha b hb hne
      rw [norm_sub_rev] at this
      linarith⟩)
    hmu
    (fun z hz => by
      rw [sub_zero] at hz
      exact ⟨hM z hz, extrap_circle_nodes_lower_bound s w z S rho hw hs hz⟩)
    (fun a z ha hz => extrap_small_circle_nodes_upper_bound s w a z d S hd (hwa a ha)
      (fun b hb hne => hab a ha b hb hne) hz)
  refine key.trans ?_
  rw [mul_add]
  refine add_le_add le_rfl ?_
  calc ‖∏ a ∈ s, (w - a) ^ (S + 1)‖ *
        ∑ a ∈ s, ∑ j ∈ Finset.range (S + 1), ‖iteratedDeriv j f a‖ / (j ! : ℝ) *
          (d * (∏ b ∈ s.erase a, ‖a - b‖ / 2) ^ (S + 1))⁻¹ / d ^ (S - j)
      ≤ ‖∏ a ∈ s, (w - a) ^ (S + 1)‖ *
        ∑ a ∈ s, eps * (d * (∏ b ∈ s.erase a, ‖a - b‖ / 2) ^ (S + 1))⁻¹ * d⁻¹ ^ S *
          Real.exp n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) (norm_nonneg _)
        exact extrap_taylor_coeff_sum_bound (fun j => ‖iteratedDeriv j f a‖) n S eps _ d heps
          (hU0 a) hd hd1 (fun j hj => hder a ha j hj)
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring

/-! ### Integer nodes `1, …, R` -/

private theorem extrap_integer_nodes_product_ratio (w : ℂ) (R r W : ℕ) (hr : 1 ≤ r)
    (hrR : r ≤ R) (hRW : R ≤ W) (hw : ‖w‖ ≤ W) :
    ∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖ ≤
      ((W : ℝ) * 16 ^ W) * ∏ b ∈ (Finset.Icc 1 R).erase r, (|(r : ℝ) - (b : ℝ)| / 2) := by
  have h1 : ∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖ ≤ ∏ b ∈ Finset.Icc 1 R, ((W : ℝ) + b) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b _ => by
      calc ‖w - (b : ℂ)‖ ≤ ‖w‖ + ‖(b : ℂ)‖ := norm_sub_le _ _
        _ ≤ W + b := by rw [Complex.norm_natCast]; linarith
  have h2 := extrap_nproduct_shift_delete_bound W R r hr hrR hRW
  have h2' : (∏ b ∈ Finset.Icc 1 R, ((W : ℝ) + b)) * 2 ^ (R - 1) ≤
      W * 16 ^ W * ((r - 1)! : ℝ) * ((R - r)! : ℝ) := by exact_mod_cast h2
  have hcard : ((Finset.Icc 1 R).erase r).card = R - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_Icc.2 ⟨hr, hrR⟩), Nat.card_Icc, Nat.add_sub_cancel]
  rw [Finset.prod_div_distrib, Finset.prod_const, hcard,
    extrap_product_abs_diff_delete r R hr hrR]
  have hy : (0 : ℝ) < 2 ^ (R - 1) := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hy]
  calc (∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖) * 2 ^ (R - 1)
      ≤ (∏ b ∈ Finset.Icc 1 R, ((W : ℝ) + b)) * 2 ^ (R - 1) :=
        mul_le_mul_of_nonneg_right h1 hy.le
    _ ≤ W * 16 ^ W * ((r - 1)! : ℝ) * ((R - r)! : ℝ) := h2'
    _ = _ := by ring

private theorem extrap_interpolation_main_term_bound (x rho M : ℝ) (W R S : ℕ) (hx : 0 ≤ x)
    (hxW : x ≤ (2 * (W : ℝ)) ^ R) (hM : 0 ≤ M) (hrho : 0 < rho) :
    x ^ (S + 1) * (rho * M / ((rho / 2) * (rho / 2) ^ (R * (S + 1)))) ≤
      2 * M * (4 * (W : ℝ) / rho) ^ (R * (S + 1)) := by
  have hX : x ^ (S + 1) ≤ (2 * (W : ℝ)) ^ (R * (S + 1)) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ hx hxW _
  have hA : 0 < (rho / 2) ^ (R * (S + 1)) := by positivity
  have h4 : (4 * (W : ℝ) / rho) ^ (R * (S + 1)) =
      (2 * (W : ℝ)) ^ (R * (S + 1)) / (rho / 2) ^ (R * (S + 1)) := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  have key : ∀ A B X : ℝ, 0 < A → X ≤ B →
      X * (rho * M / ((rho / 2) * A)) ≤ 2 * M * (B / A) := by
    intro A B X hA hXB
    have e : X * (rho * M / ((rho / 2) * A)) = 2 * M * (X / A) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hXB hA.le) (by positivity)
  rw [h4]
  exact key _ _ _ hA hX

private theorem extrap_norm_cproduct_integer_nodes (w : ℂ) (R S : ℕ) :
    ‖∏ a ∈ (Finset.Icc 1 R).image (fun r : ℕ => (r : ℂ)), (w - a) ^ S‖ =
      (∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖) ^ S := by
  rw [Finset.prod_image fun x _ y _ h => Nat.cast_injective h, norm_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun b _ => norm_pow _ _

private theorem extrap_product_integer_nodes_delete (R r : ℕ) :
    ∏ b ∈ ((Finset.Icc 1 R).image (fun x : ℕ => (x : ℂ))).erase (r : ℂ), ‖(r : ℂ) - b‖ / 2 =
      ∏ b ∈ (Finset.Icc 1 R).erase r, (|(r : ℝ) - (b : ℝ)| / 2) := by
  rw [← Finset.image_erase (f := fun x : ℕ => (x : ℂ)) Nat.cast_injective,
    Finset.prod_image fun x _ y _ h => Nat.cast_injective h]
  exact Finset.prod_congr rfl fun b _ => by rw [extrap_norm_natCast_sub]

/-- HOL Light: Baker/extrap.ml, INTEGER_NODES_INTERPOLATION_BOUND. The interpolation bound for an
entire `f` at a point `w` with `‖w‖ ≤ W` at distance at least `1 / q` from the nodes `1, …, R`,
in terms of the supremum `M` of `f` on the circle of radius `rho ≥ 4 W` and of the bound
`n ^ j * eps` for the derivatives of order `j ≤ S` at the nodes.

Deviation: see the conventions in the file header (curried hypotheses, `(r : ℂ)`). -/
theorem integer_nodes_interpolation_bound (f : ℂ → ℂ) (n R S q W : ℕ) (w : ℂ) (rho M eps : ℝ)
    (hf : Differentiable ℂ f) (hR : 1 ≤ R) (hRW : R ≤ W) (hq : 1 ≤ q) (hw : ‖w‖ ≤ (W : ℝ))
    (hsep : ∀ r : ℕ, 1 ≤ r → r ≤ R → (q : ℝ)⁻¹ ≤ ‖w - (r : ℂ)‖)
    (hrho : 4 * (W : ℝ) ≤ rho)
    (hM : ∀ z : ℂ, ‖z‖ = rho → ‖f z‖ ≤ M)
    (hd : ∀ r j : ℕ, 1 ≤ r → r ≤ R → j ≤ S →
      ‖iteratedDeriv j f (r : ℂ)‖ ≤ (n : ℝ) ^ j * eps) :
    ‖f w‖ ≤ 2 * M * (4 * (W : ℝ) / rho) ^ (R * (S + 1)) +
      eps * 2 * (q : ℝ) * (R : ℝ) * (2 * (q : ℝ)) ^ S * Real.exp n *
        ((W : ℝ) * 16 ^ W) ^ (S + 1) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hR.trans hRW
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrho0 : 0 < rho := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM (rho : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho0]))
  have heps : 0 ≤ eps := by
    have h := hd 1 0 le_rfl hR (Nat.zero_le _)
    rw [pow_zero, one_mul] at h
    exact (norm_nonneg _).trans h
  have hd0 : 0 < (2 * (q : ℝ))⁻¹ := by positivity
  have hd1 : (2 * (q : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2d : 2 * (2 * (q : ℝ))⁻¹ = (q : ℝ)⁻¹ := by
    field_simp
  have hmem : ∀ a ∈ (Finset.Icc 1 R).image (fun r : ℕ => (r : ℂ)),
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ (r : ℂ) = a := fun a ha => by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ha
    exact ⟨r, (Finset.mem_Icc.1 hr).1, (Finset.mem_Icc.1 hr).2, rfl⟩
  have key := extrap_interpolation_nodes_bound f
    ((Finset.Icc 1 R).image (fun r : ℕ => (r : ℂ))) S w rho (2 * (q : ℝ))⁻¹ M eps n hf hrho0
    (by linarith)
    (fun a ha => by
      obtain ⟨r, _, hr2, rfl⟩ := hmem a ha
      have : (r : ℝ) ≤ W := by exact_mod_cast hr2.trans hRW
      rw [Complex.norm_natCast]
      linarith)
    hd0 hd1
    (fun a ha => by
      obtain ⟨r, hr1, hr2, rfl⟩ := hmem a ha
      rw [h2d]
      exact hsep r hr1 hr2)
    (fun a ha b hb hne => by
      obtain ⟨x, _, _, rfl⟩ := hmem a ha
      obtain ⟨y, _, _, rfl⟩ := hmem b hb
      have hxy : x ≠ y := fun h => hne (by rw [h])
      rw [h2d, extrap_norm_natCast_sub]
      exact (inv_le_one_of_one_le₀ hq1).trans (extrap_real_abs_sub_num_ge_1 x y hxy))
    hM heps
    (fun a ha j hj => by
      obtain ⟨r, hr1, hr2, rfl⟩ := hmem a ha
      exact hd r j hr1 hr2 hj)
  have hcard : ((Finset.Icc 1 R).image (fun r : ℕ => (r : ℂ))).card = R := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc, Nat.add_sub_cancel]
  rw [Finset.sum_image fun x _ y _ h => Nat.cast_injective h, hcard, inv_inv] at key
  simp only [extrap_norm_cproduct_integer_nodes, extrap_product_integer_nodes_delete] at key
  have hPw0 : 0 ≤ ∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hPwW : ∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖ ≤ (2 * (W : ℝ)) ^ R := by
    calc ∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖ ≤ ∏ _b ∈ Finset.Icc 1 R, (2 * (W : ℝ)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b hb => by
            have : (b : ℝ) ≤ W := by exact_mod_cast (Finset.mem_Icc.1 hb).2.trans hRW
            calc ‖w - (b : ℂ)‖ ≤ ‖w‖ + ‖(b : ℂ)‖ := norm_sub_le _ _
              _ ≤ 2 * W := by rw [Complex.norm_natCast]; linarith
      _ = (2 * (W : ℝ)) ^ R := by
          rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hterm1 := extrap_interpolation_main_term_bound _ rho M W R S hPw0 hPwW hM0 hrho0
  have hterm2 : ∀ r ∈ Finset.Icc 1 R,
      (∏ b ∈ Finset.Icc 1 R, ‖w - (b : ℂ)‖) ^ (S + 1) *
        ((2 * (q : ℝ))⁻¹ *
          (∏ b ∈ (Finset.Icc 1 R).erase r, (|(r : ℝ) - (b : ℝ)| / 2)) ^ (S + 1))⁻¹ ≤
      (2 * (q : ℝ)) * ((W : ℝ) * 16 ^ W) ^ (S + 1) := by
    intro r hr
    have hr' := Finset.mem_Icc.1 hr
    have hQ : 0 < ∏ b ∈ (Finset.Icc 1 R).erase r, (|(r : ℝ) - (b : ℝ)| / 2) :=
      Finset.prod_pos fun b hb => by
        have := extrap_real_abs_sub_num_ge_1 r b (Finset.ne_of_mem_erase hb).symm
        linarith
    exact extrap_real_pow_ratio_inv_le _ _ ((W : ℝ) * 16 ^ W) (2 * (q : ℝ)) (S + 1) hPw0
      (extrap_integer_nodes_product_ratio w R r W hr'.1 hr'.2 hRW hw) hQ (by positivity)
  have hcoef : 0 ≤ eps * (2 * (q : ℝ)) ^ S * Real.exp n := by positivity
  calc ‖f w‖ ≤ _ := key
    _ ≤ 2 * M * (4 * (W : ℝ) / rho) ^ (R * (S + 1)) +
        eps * (2 * (q : ℝ)) ^ S * Real.exp n *
          ∑ _r ∈ Finset.Icc 1 R, (2 * (q : ℝ)) * ((W : ℝ) * 16 ^ W) ^ (S + 1) :=
        add_le_add hterm1 (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm2) hcoef)
    _ = _ := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

/-! ### Baker Lemma 6: the extrapolation step and the induction -/

/-- HOL Light: Baker/extrap.ml, EXTRAPOLATION_STEP_COEFF. One extrapolation step (Baker Lemma 6,
with coefficients): if all members with `|m| ≤ 2 S` are at most `eps` at the nodes `1, …, R`, and
each member with `|m| ≤ S` is at a point `l` with `R < l ≤ R'` either at most `eps` or larger
than `V`, where `V` dominates the interpolation bound, then it is at most `eps` there.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem extrapolation_step_coeff (f : (ℕ → ℕ) → ℂ → ℂ) (c : (ℕ → ℕ) → ℕ → ℂ)
    (c0 : (ℕ → ℕ) → ℂ) (n R R' S : ℕ) (rho M V eps : ℝ) (N : ℕ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), c m i * f (fun r => if r = i then m r + 1 else m r) z +
        c0 m * f m z)
    (hN : ∀ m, ∑ r ∈ Finset.range (n - 1 + 1), m r < 2 * S →
      ∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ + ‖c0 m‖ ≤ (N : ℝ))
    (hR : 1 ≤ R) (hRR : R ≤ R') (hrho : 4 * (R' : ℝ) ≤ rho)
    (he : ∀ (m : ℕ → ℕ) (r : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ 2 * S → 1 ≤ r → r ≤ R →
      ‖f m (r : ℂ)‖ ≤ eps)
    (hM : ∀ (m : ℕ → ℕ) (z : ℂ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S → ‖z‖ = rho →
      ‖f m z‖ ≤ M)
    (hV : ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S → R < l → l ≤ R' →
      ‖f m (l : ℂ)‖ ≤ eps ∨ V < ‖f m (l : ℂ)‖)
    (hbound : 2 * M * (4 * (R' : ℝ) / rho) ^ (R * (S + 1)) +
      eps * 2 * (R : ℝ) * 2 ^ S * Real.exp N * ((R' : ℝ) * 16 ^ R') ^ (S + 1) ≤ V) :
    ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S → R < l → l ≤ R' →
      ‖f m (l : ℂ)‖ ≤ eps := by
  intro m l hm hl1 hl2
  rcases hV m l hm hl1 hl2 with h | h
  · exact h
  exfalso
  have hb := integer_nodes_interpolation_bound (f m) N R S 1 R' (l : ℂ) rho M eps (hf m) hR hRR
    le_rfl (by rw [Complex.norm_natCast]; exact_mod_cast hl2)
    (fun r hr1 hr2 => by
      rw [extrap_norm_natCast_sub, Nat.cast_one, inv_one]
      exact extrap_real_abs_sub_num_ge_1 l r (by omega))
    hrho (fun z hz => hM m z hm hz)
    (fun r j hr1 hr2 hj =>
      derivative_family_bound_coeff f c c0 n (2 * S) N eps (r : ℂ) hn hf hD hN
        (fun m' hm' => he m' r hm' hr1 hr2) j m (by omega))
  rw [Nat.cast_one, mul_one, mul_one] at hb
  linarith

/-- HOL Light: Baker/extrap.ml, EXTRAPOLATION_INDUCTION_COEFF. Baker Lemma 6 with coefficients:
the induction over a sequence of `J` extrapolation steps with nodes `1, …, R K`, orders `S K` and
circles of radius `rho K`.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem extrapolation_induction_coeff (f : (ℕ → ℕ) → ℂ → ℂ) (c : (ℕ → ℕ) → ℕ → ℂ)
    (c0 : (ℕ → ℕ) → ℂ) (n : ℕ) (R S : ℕ → ℕ) (rho M V : ℕ → ℝ) (eps : ℝ) (J N : ℕ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), c m i * f (fun r => if r = i then m r + 1 else m r) z +
        c0 m * f m z)
    (hN : ∀ m, ∑ r ∈ Finset.range (n - 1 + 1), m r < S 0 →
      ∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ + ‖c0 m‖ ≤ (N : ℝ))
    (hR0 : 1 ≤ R 0)
    (hstep : ∀ K, K < J →
      R K ≤ R (K + 1) ∧ 2 * S (K + 1) ≤ S K ∧
      4 * (R (K + 1) : ℝ) ≤ rho K ∧
      (∀ (m : ℕ → ℕ) (z : ℂ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S (K + 1) → ‖z‖ = rho K →
        ‖f m z‖ ≤ M K) ∧
      (∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S (K + 1) → R K < l →
        l ≤ R (K + 1) → ‖f m (l : ℂ)‖ ≤ eps ∨ V K < ‖f m (l : ℂ)‖) ∧
      2 * M K * (4 * (R (K + 1) : ℝ) / rho K) ^ (R K * (S (K + 1) + 1)) +
        eps * 2 * (R K : ℝ) * 2 ^ S (K + 1) * Real.exp N *
          ((R (K + 1) : ℝ) * 16 ^ R (K + 1)) ^ (S (K + 1) + 1) ≤ V K)
    (h0 : ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S 0 → 1 ≤ l → l ≤ R 0 →
      ‖f m (l : ℂ)‖ ≤ eps) :
    ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S J → 1 ≤ l → l ≤ R J →
      ‖f m (l : ℂ)‖ ≤ eps := by
  have main : ∀ K, K ≤ J → 1 ≤ R K ∧ S K ≤ S 0 ∧
      ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S K → 1 ≤ l → l ≤ R K →
        ‖f m (l : ℂ)‖ ≤ eps := by
    intro K
    induction K with
    | zero => exact fun _ => ⟨hR0, le_rfl, h0⟩
    | succ K ih =>
      intro hK
      obtain ⟨hRK, hSK, hK0⟩ := ih (by omega)
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hstep K (by omega)
      refine ⟨by omega, by omega, ?_⟩
      have step := extrapolation_step_coeff f c c0 n (R K) (R (K + 1)) (S (K + 1)) (rho K) (M K)
        (V K) eps N hn hf hD (fun m hm => hN m (by omega)) hRK h1 h3
        (fun m r hm hr1 hr2 => hK0 m r (by omega) hr1 hr2) h4 h5 h6
      intro m l hm hl1 hl2
      by_cases hl : l ≤ R K
      · exact hK0 m l (by omega) hl1 hl
      · exact step m l hm (by omega) hl2
  exact (main J le_rfl).2.2

/-- HOL Light: Baker/extrap.ml, EXTRAPOLATION_INDUCTION. Baker Lemma 6: the induction over `J`
extrapolation steps for a family with `D (f m) = ∑ i < n, f (m + e_i)`.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem extrapolation_induction (f : (ℕ → ℕ) → ℂ → ℂ) (n : ℕ) (R S : ℕ → ℕ)
    (rho M V : ℕ → ℝ) (eps : ℝ) (J : ℕ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), f (fun r => if r = i then m r + 1 else m r) z)
    (hR0 : 1 ≤ R 0)
    (hstep : ∀ K, K < J →
      R K ≤ R (K + 1) ∧ 2 * S (K + 1) ≤ S K ∧
      4 * (R (K + 1) : ℝ) ≤ rho K ∧
      (∀ (m : ℕ → ℕ) (z : ℂ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S (K + 1) → ‖z‖ = rho K →
        ‖f m z‖ ≤ M K) ∧
      (∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S (K + 1) → R K < l →
        l ≤ R (K + 1) → ‖f m (l : ℂ)‖ ≤ eps ∨ V K < ‖f m (l : ℂ)‖) ∧
      2 * M K * (4 * (R (K + 1) : ℝ) / rho K) ^ (R K * (S (K + 1) + 1)) +
        eps * 2 * (R K : ℝ) * 2 ^ S (K + 1) * Real.exp n *
          ((R (K + 1) : ℝ) * 16 ^ R (K + 1)) ^ (S (K + 1) + 1) ≤ V K)
    (h0 : ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S 0 → 1 ≤ l → l ≤ R 0 →
      ‖f m (l : ℂ)‖ ≤ eps) :
    ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S J → 1 ≤ l → l ≤ R J →
      ‖f m (l : ℂ)‖ ≤ eps := by
  have hnn : n - 1 + 1 = n := Nat.sub_add_cancel hn
  refine extrapolation_induction_coeff f (fun _ _ => 1) (fun _ => 0) n R S rho M V eps J n hn hf
    (fun m => ?_) (fun m _ => ?_) hR0 hstep h0
  · rw [hD m]
    funext z
    simp
  · simp [hnn]

/-! ### Baker Lemma 7, analytic part: the rational points `l / k` -/

/-- HOL Light: Baker/extrap.ml, RATIONAL_EXTRAPOLATION_COEFF_GEN. Baker Lemma 7 with coefficients,
analytic part: the bound for the member `f m0` at a rational point `l / q` with `l ≤ q X` that is
not one of the nodes `1, …, X` (also at `l = 0`), from smallness of the members with
`|m| ≤ |m0| + Y` at the nodes.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem rational_extrapolation_coeff_gen (f : (ℕ → ℕ) → ℂ → ℂ) (c : (ℕ → ℕ) → ℕ → ℂ)
    (c0 : (ℕ → ℕ) → ℂ) (n X Y : ℕ) (m0 : ℕ → ℕ) (q l : ℕ) (rho M eps : ℝ) (N : ℕ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), c m i * f (fun r => if r = i then m r + 1 else m r) z +
        c0 m * f m z)
    (hN : ∀ m, ∑ r ∈ Finset.range (n - 1 + 1), m r < ∑ r ∈ Finset.range (n - 1 + 1), m0 r + Y →
      ∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ + ‖c0 m‖ ≤ (N : ℝ))
    (hX : 1 ≤ X) (hq : 1 ≤ q) (hl : l ≤ q * X) (hdiv : ¬ q ∣ l ∨ l = 0)
    (hrho : 4 * (X : ℝ) ≤ rho)
    (hM : ∀ z : ℂ, ‖z‖ = rho → ‖f m0 z‖ ≤ M)
    (he : ∀ (m : ℕ → ℕ) (r : ℕ),
      ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ ∑ r ∈ Finset.range (n - 1 + 1), m0 r + Y →
      1 ≤ r → r ≤ X → ‖f m (r : ℂ)‖ ≤ eps) :
    ‖f m0 ((l : ℂ) / (q : ℂ))‖ ≤ 2 * M * (4 * (X : ℝ) / rho) ^ (X * (Y + 1)) +
      eps * 2 * (q : ℝ) * (X : ℝ) * (2 * (q : ℝ)) ^ Y * Real.exp N *
        ((X : ℝ) * 16 ^ X) ^ (Y + 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  refine integer_nodes_interpolation_bound (f m0) N X Y q X ((l : ℂ) / (q : ℂ)) rho M eps
    (hf m0) hX le_rfl hq ?_ ?_ hrho hM ?_
  · rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ hq0]
    exact_mod_cast (by rw [mul_comm]; exact hl : l ≤ X * q)
  · intro r hr1 _
    have hne : l ≠ q * r := by
      rintro rfl
      rcases hdiv with h | h
      · exact h (dvd_mul_right _ _)
      · rcases Nat.mul_eq_zero.1 h with h | h <;> omega
    have e : (l : ℂ) / (q : ℂ) - (r : ℂ) =
        ((((l : ℝ) - ((q * r : ℕ) : ℝ)) / (q : ℝ) : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hq0, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (extrap_real_abs_sub_num_ge_1 l (q * r) hne) hq0.le
  · intro r j hr1 hr2 hj
    exact derivative_family_bound_coeff f c c0 n (∑ r ∈ Finset.range (n - 1 + 1), m0 r + Y) N
      eps (r : ℂ) hn hf hD hN (fun m hm => he m r hm hr1 hr2) j m0 (by omega)

/-- HOL Light: Baker/extrap.ml, RATIONAL_EXTRAPOLATION_COEFF. The case of
`rational_extrapolation_coeff_gen` where `q` does not divide `l`.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem rational_extrapolation_coeff (f : (ℕ → ℕ) → ℂ → ℂ) (c : (ℕ → ℕ) → ℕ → ℂ)
    (c0 : (ℕ → ℕ) → ℂ) (n X Y : ℕ) (m0 : ℕ → ℕ) (q l : ℕ) (rho M eps : ℝ) (N : ℕ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), c m i * f (fun r => if r = i then m r + 1 else m r) z +
        c0 m * f m z)
    (hN : ∀ m, ∑ r ∈ Finset.range (n - 1 + 1), m r < ∑ r ∈ Finset.range (n - 1 + 1), m0 r + Y →
      ∑ i ∈ Finset.range (n - 1 + 1), ‖c m i‖ + ‖c0 m‖ ≤ (N : ℝ))
    (hX : 1 ≤ X) (hq : 1 ≤ q) (hl : l ≤ q * X) (hdiv : ¬ q ∣ l)
    (hrho : 4 * (X : ℝ) ≤ rho)
    (hM : ∀ z : ℂ, ‖z‖ = rho → ‖f m0 z‖ ≤ M)
    (he : ∀ (m : ℕ → ℕ) (r : ℕ),
      ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ ∑ r ∈ Finset.range (n - 1 + 1), m0 r + Y →
      1 ≤ r → r ≤ X → ‖f m (r : ℂ)‖ ≤ eps) :
    ‖f m0 ((l : ℂ) / (q : ℂ))‖ ≤ 2 * M * (4 * (X : ℝ) / rho) ^ (X * (Y + 1)) +
      eps * 2 * (q : ℝ) * (X : ℝ) * (2 * (q : ℝ)) ^ Y * Real.exp N *
        ((X : ℝ) * 16 ^ X) ^ (Y + 1) :=
  rational_extrapolation_coeff_gen f c c0 n X Y m0 q l rho M eps N hn hf hD hN hX hq hl
    (Or.inl hdiv) hrho hM he

/-- HOL Light: Baker/extrap.ml, RATIONAL_EXTRAPOLATION. Baker Lemma 7, analytic part: the bound
for `f 0` at a rational point `l / k`, `l ≤ k X`, that is not one of the nodes `1, …, X`, for a
family with `D (f m) = ∑ i < n, f (m + e_i)`.

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem rational_extrapolation (f : (ℕ → ℕ) → ℂ → ℂ) (n X Y k l : ℕ) (rho M eps : ℝ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), f (fun r => if r = i then m r + 1 else m r) z)
    (hX : 1 ≤ X) (hk : 1 ≤ k) (hl : l ≤ k * X) (hdiv : ¬ k ∣ l ∨ l = 0)
    (hrho : 4 * (X : ℝ) ≤ rho)
    (hM : ∀ z : ℂ, ‖z‖ = rho → ‖f (fun _ => 0) z‖ ≤ M)
    (he : ∀ (m : ℕ → ℕ) (r : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ Y → 1 ≤ r → r ≤ X →
      ‖f m (r : ℂ)‖ ≤ eps) :
    ‖f (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ ≤ 2 * M * (4 * (X : ℝ) / rho) ^ (X * (Y + 1)) +
      eps * 2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
        ((X : ℝ) * 16 ^ X) ^ (Y + 1) := by
  have hnn : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h0 : ∑ r ∈ Finset.range (n - 1 + 1), (fun _ : ℕ => (0 : ℕ)) r = 0 :=
    Finset.sum_const_zero
  refine rational_extrapolation_coeff_gen f (fun _ _ => 1) (fun _ => 0) n X Y (fun _ => 0) k l
    rho M eps n hn hf (fun m => ?_) (fun m _ => ?_) hX hk hl hdiv hrho hM
    (fun m r hm hr1 hr2 => he m r (by rw [h0, zero_add] at hm; exact hm) hr1 hr2)
  · rw [hD m]
    funext z
    simp
  · simp [hnn]

/-- HOL Light: Baker/extrap.ml, RATIONAL_EXTRAPOLATION_ALL. Baker Lemma 7, analytic part, at every
rational point `l / k` with `l ≤ k X` (the nodes included).

Deviation: see the conventions in the file header (`deriv`, curried hypotheses, `(l : ℂ)`). -/
theorem rational_extrapolation_all (f : (ℕ → ℕ) → ℂ → ℂ) (n X Y k l : ℕ) (rho M eps : ℝ)
    (hn : 1 ≤ n) (hf : ∀ m, Differentiable ℂ (f m))
    (hD : ∀ m, deriv (f m) = fun z =>
      ∑ i ∈ Finset.range (n - 1 + 1), f (fun r => if r = i then m r + 1 else m r) z)
    (hX : 1 ≤ X) (hk : 1 ≤ k) (hl : l ≤ k * X)
    (hrho : 4 * (X : ℝ) ≤ rho)
    (hM : ∀ z : ℂ, ‖z‖ = rho → ‖f (fun _ => 0) z‖ ≤ M)
    (he : ∀ (m : ℕ → ℕ) (r : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ Y → 1 ≤ r → r ≤ X →
      ‖f m (r : ℂ)‖ ≤ eps) :
    ‖f (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ ≤ 2 * M * (4 * (X : ℝ) / rho) ^ (X * (Y + 1)) +
      eps * 2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
        ((X : ℝ) * 16 ^ X) ^ (Y + 1) := by
  by_cases hdiv : ¬ k ∣ l ∨ l = 0
  · exact rational_extrapolation f n X Y k l rho M eps hn hf hD hX hk hl hdiv hrho hM he
  rw [not_or, not_not] at hdiv
  obtain ⟨⟨x, rfl⟩, hl0⟩ := hdiv
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.2 fun h => hl0 (by rw [h, mul_zero])
  have hxX : x ≤ X := Nat.le_of_mul_le_mul_left hl (by omega)
  have hrho0 : 0 ≤ rho := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM (rho : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrho0]))
  have h0 : ∑ r ∈ Finset.range (n - 1 + 1), (fun _ : ℕ => (0 : ℕ)) r ≤ Y := by
    rw [Finset.sum_const_zero]
    exact Nat.zero_le _
  have hnode : ‖f (fun _ => 0) (((k * x : ℕ) : ℂ) / (k : ℂ))‖ ≤ eps := by
    rw [Nat.cast_mul, mul_div_cancel_left₀ _ hkc]
    exact he (fun _ => 0) x h0 hx1 hxX
  have heps : 0 ≤ eps := (norm_nonneg _).trans hnode
  have hfac : (1 : ℝ) ≤ 2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
      ((X : ℝ) * 16 ^ X) ^ (Y + 1) := by
    have h16 : (1 : ℝ) ≤ 16 ^ X := one_le_pow₀ (by norm_num)
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hk1) hX1) (one_le_pow₀ (by linarith)))
      (Real.one_le_exp (Nat.cast_nonneg n)))
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hX1 h16))
  have hfirst : 0 ≤ 2 * M * (4 * (X : ℝ) / rho) ^ (X * (Y + 1)) := by positivity
  calc ‖f (fun _ => 0) (((k * x : ℕ) : ℂ) / (k : ℂ))‖ ≤ eps := hnode
    _ ≤ eps * (2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
        ((X : ℝ) * 16 ^ X) ^ (Y + 1)) := le_mul_of_one_le_right heps hfac
    _ ≤ 2 * M * (4 * (X : ℝ) / rho) ^ (X * (Y + 1)) +
        eps * 2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
          ((X : ℝ) * 16 ^ X) ^ (Y + 1) := by
        have e : eps * 2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
            ((X : ℝ) * 16 ^ X) ^ (Y + 1) =
          eps * (2 * (k : ℝ) * (X : ℝ) * (2 * (k : ℝ)) ^ Y * Real.exp n *
            ((X : ℝ) * 16 ^ X) ^ (Y + 1)) := by ring
        rw [e]
        linarith

end RiemannMasullo.Baker
