module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Bounds
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.IntPoly
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Degrees and heights at a point with `m` extra algebraic coordinates

Ported from HOL Light, Baker/heights.ml (jrh13/hol-light, commit 1a0c0e6).

Besides `theta 1, ..., theta n` (degrees `d r`, heights `H r`) the point `theta` has the
coordinates `theta r`, `r ∈ Finset.Icc (n + 1) (n + m)`, of degrees `dx r ≤ Dx` and heights at
most `B`. On the whole range `Finset.Icc 1 (n + m)` the merged degrees and heights are
`if r ≤ n then d r else dx r` and `if r ≤ n then H r else B`. `baker_extra_bounds` collects the
bounds for integer polynomials in the `n + m` variables at such a point.

Products and sums are bracketed as HOL Light parses them (to the right). -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### Splitting products and sums over `1..n + m` at `n` -/

private theorem heights_prod_split {M : Type*} [CommMonoid M] (n m : ℕ) (f : ℕ → M) :
    ∏ r ∈ Finset.Icc 1 (n + m), f r =
      (∏ r ∈ Finset.Icc 1 n, f r) * ∏ r ∈ Finset.Icc (n + 1) (n + m), f r := by
  have hU : Finset.Icc 1 (n + m) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (n + m) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hD : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (n + m)) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  rw [hU, Finset.prod_union hD]

private theorem heights_sum_split (n m : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 (n + m), f r =
      (∑ r ∈ Finset.Icc 1 n, f r) + ∑ r ∈ Finset.Icc (n + 1) (n + m), f r :=
  heights_prod_split (M := Multiplicative ℝ) n m f

/-- HOL Light: Baker/heights.ml, BAKER_EXTRA_NPRODUCT_LE. The product of the merged degrees over
`1..n + m` is at most `(∏ d r) * Dx ^ m`. -/
theorem baker_extra_nproduct_le (n m : ℕ) (d dx : ℕ → ℕ) (Dx : ℕ)
    (hdx : ∀ r ∈ Finset.Icc (n + 1) (n + m), dx r ≤ Dx) :
    ∏ r ∈ Finset.Icc 1 (n + m), (if r ≤ n then d r else dx r) ≤
      (∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m := by
  rw [heights_prod_split]
  refine Nat.mul_le_mul (le_of_eq (Finset.prod_congr rfl fun r hr => ?_)) ?_
  · rw [ite_eq_left (Finset.mem_Icc.mp hr).2]
  · calc ∏ r ∈ Finset.Icc (n + 1) (n + m), (if r ≤ n then d r else dx r)
        ≤ ∏ _r ∈ Finset.Icc (n + 1) (n + m), Dx := by
          refine Finset.prod_le_prod fun r hr => ?_
          rw [ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)]
          exact hdx r hr
      _ = Dx ^ m := by simp

/-- HOL Light: Baker/heights.ml, PRODUCT_POW_COND_SPLIT. A product of powers over `1..n + m` whose
base is constant beyond `n` splits at `n`. -/
theorem product_pow_cond_split (n m : ℕ) (f : ℕ → ℝ) (c : ℝ) (e : ℕ → ℕ) :
    ∏ r ∈ Finset.Icc 1 (n + m), (if r ≤ n then f r else c) ^ e r =
      (∏ r ∈ Finset.Icc 1 n, f r ^ e r) * c ^ (∑ r ∈ Finset.Icc (n + 1) (n + m), e r) := by
  rw [heights_prod_split, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  · exact Finset.prod_congr rfl fun r hr => by rw [ite_eq_left (Finset.mem_Icc.mp hr).2]
  · refine Finset.prod_congr rfl fun r hr => ?_
    rw [ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)]

/-- HOL Light: Baker/heights.ml, BAKER_EXTRA_LOGSUM_LE. The height sum of the merged family over
`1..n + m` is at most the height sum over `1..n` plus `E (log (Dx + 1) + 3 log B)`. -/
theorem baker_extra_logsum_le (n m : ℕ) (d dx : ℕ → ℕ) (H : ℕ → ℝ) (e : ℕ → ℕ) (Dx : ℕ) (B : ℝ)
    (hB : 0 < B) (hdx : ∀ r ∈ Finset.Icc (n + 1) (n + m), dx r ≤ Dx) :
    ∑ r ∈ Finset.Icc 1 (n + m),
        (e r : ℝ) * Real.log ((((if r ≤ n then d r else dx r) + 1 : ℕ) : ℝ) *
          (if r ≤ n then H r else B) ^ 3) ≤
      (∑ r ∈ Finset.Icc 1 n, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)) +
        ((∑ r ∈ Finset.Icc (n + 1) (n + m), e r : ℕ) : ℝ) *
          (Real.log ((Dx : ℝ) + 1) + 3 * Real.log B) := by
  rw [heights_sum_split]
  refine add_le_add (le_of_eq (Finset.sum_congr rfl fun r hr => ?_)) ?_
  · rw [ite_eq_left (Finset.mem_Icc.mp hr).2, ite_eq_left (Finset.mem_Icc.mp hr).2]
  · rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrn : ¬ r ≤ n := by have := (Finset.mem_Icc.mp hr).1; omega
    rw [ite_eq_right hrn, ite_eq_right hrn]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 : (0 : ℝ) < ((dx r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have h2 : ((dx r + 1 : ℕ) : ℝ) ≤ (Dx : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (hdx r hr)
    rw [Real.log_mul h1.ne' (pow_pos hB 3).ne', Real.log_pow]
    have := Real.log_le_log h1 h2
    push_cast at this ⊢
    linarith

/-! ### The Liouville lower bound in exp form with enlarged degree product and height sum -/

/-- HOL Light: Baker/heights.ml, LIOUVILLE_EXP_ENLARGE. The exponential lower bound
`exp (-(D (log D + log b + S)))` decreases when `D` and `S` increase. -/
theorem liouville_exp_enlarge (D0 D : ℕ) (b S0 S : ℝ) (hD0 : 1 ≤ D0) (hD : D0 ≤ D) (hb : 1 ≤ b)
    (hS0 : 0 ≤ S0) (hS : S0 ≤ S) :
    Real.exp (-((D : ℝ) * (Real.log (D : ℝ) + (Real.log b + S)))) ≤
      Real.exp (-((D0 : ℝ) * (Real.log (D0 : ℝ) + (Real.log b + S0)))) := by
  have h1 : (1 : ℝ) ≤ D0 := by exact_mod_cast hD0
  have h2 : (D0 : ℝ) ≤ D := by exact_mod_cast hD
  have h3 : 0 ≤ Real.log (D0 : ℝ) := Real.log_nonneg h1
  have h4 : Real.log (D0 : ℝ) ≤ Real.log (D : ℝ) := Real.log_le_log (by linarith) h2
  have h5 : 0 ≤ Real.log b := Real.log_nonneg hb
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul h2 (by linarith) (by linarith) (by linarith)

/-- HOL Light: Baker/heights.ml, INTPOLY_LIOUVILLE_EXP_MONO. The Liouville lower bound for a
nonzero value of an `intpoly` at an algebraic point, in exp form, with an upper bound `D` for the
degree product and an upper bound `S` for the height sum.

Deviation: HOL's hypothesis `FINITE v` is dropped, `v` being a `Finset`; the coefficients `a r j`
are integers (HOL: reals with `integer (a r j)`), so that conjunct is dropped. -/
theorem intpoly_liouville_exp_mono (v : Finset ℕ) (nn : ℕ → ℕ) (b : ℝ) (g : (ℕ → ℂ) → ℂ)
    (theta : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (h : ℕ → ℝ) (D : ℕ) (S : ℝ)
    (hg : intpoly v nn b g) (hb : 1 ≤ b)
    (ha : ∀ r ∈ v, 1 ≤ d r ∧ 1 ≤ h r ∧ (∀ j, |(a r j : ℝ)| ≤ h r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hD : ∏ r ∈ v, d r ≤ D)
    (hS : ∑ r ∈ v, (nn r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * h r ^ 3) ≤ S)
    (hne : g theta ≠ 0) :
    Real.exp (-((D : ℝ) * (Real.log (D : ℝ) + (Real.log b + S)))) ≤ ‖g theta‖ := by
  have hL := intpoly_liouville theta a d h hg
    (fun r hr => ⟨(ha r hr).2.2.1, (ha r hr).2.2.2.1, (ha r hr).2.2.2.2⟩) hne
  have hE := liouville_exp_lower v d h nn b (fun r hr => ⟨(ha r hr).1, (ha r hr).2.1⟩) hb
  refine le_trans (le_trans ?_ hE) hL
  refine liouville_exp_enlarge _ _ b _ _
    (Finset.one_le_prod fun r hr => (ha r hr).1) hD hb ?_ hS
  refine Finset.sum_nonneg fun r hr => mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg ?_)
  refine real_le_1_mul _ _ ?_ (one_le_pow₀ (ha r hr).2.1)
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)

/-! ### The merged family -/

/-- HOL Light: Baker/heights.ml, BAKER_EXTRA_MERGE. The merged family on `1..n + m`: degrees,
heights and vanishing integer polynomials of `theta r`, the root bounds, and `dx r ≤ Dx`.

Deviation: the coefficients `a r j`, `ax r j` are integers (HOL: reals with `integer`), so the
`integer` conjuncts are dropped. -/
theorem baker_extra_merge (n m : ℕ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ) (Dx : ℕ) (B : ℝ)
    (theta : ℕ → ℂ) (dx : ℕ → ℕ) (ax : ℕ → ℕ → ℤ) (hB : 1 ≤ B)
    (ha : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hax : ∀ r ∈ Finset.Icc (n + 1) (n + m), 1 ≤ dx r ∧ dx r ≤ Dx ∧
      (∀ j, |(ax r j : ℝ)| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
      ∑ j ∈ Finset.range (dx r + 1), (ax r j : ℂ) * theta r ^ j = 0) :
    (∀ r ∈ Finset.Icc 1 (n + m),
        1 ≤ (if r ≤ n then d r else dx r) ∧
        1 ≤ (if r ≤ n then H r else B) ∧
        (∀ j, |((if r ≤ n then a r else ax r) j : ℝ)| ≤ (if r ≤ n then H r else B)) ∧
        (if r ≤ n then a r else ax r) (if r ≤ n then d r else dx r) ≠ 0 ∧
        ∑ j ∈ Finset.range ((if r ≤ n then d r else dx r) + 1),
          ((if r ≤ n then a r else ax r) j : ℂ) * theta r ^ j = 0) ∧
      (∀ r ∈ Finset.Icc 1 (n + m),
        ‖theta r‖ ≤ (if r ≤ n then 1 + (d r : ℝ) * H r else (1 + (Dx : ℝ)) * B) ∧
        1 ≤ (if r ≤ n then 1 + (d r : ℝ) * H r else (1 + (Dx : ℝ)) * B)) ∧
      ∀ r ∈ Finset.Icc (n + 1) (n + m), dx r ≤ Dx := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => (hax r hr).2.1⟩
  · have hr' := Finset.mem_Icc.mp hr
    by_cases hrn : r ≤ n
    · simp only [ite_eq_left hrn]
      exact ha r (Finset.mem_Icc.mpr ⟨hr'.1, hrn⟩)
    · simp only [ite_eq_right hrn]
      obtain ⟨h1, -, h3, h4, h5⟩ := hax r (Finset.mem_Icc.mpr ⟨by omega, hr'.2⟩)
      exact ⟨h1, hB, h3, h4, h5⟩
  · have hr' := Finset.mem_Icc.mp hr
    by_cases hrn : r ≤ n
    · simp only [ite_eq_left hrn]
      obtain ⟨-, h2, h3, h4, h5⟩ := ha r (Finset.mem_Icc.mpr ⟨hr'.1, hrn⟩)
      have h0 : 0 ≤ (d r : ℝ) * H r := mul_nonneg (Nat.cast_nonneg _) (by linarith)
      exact ⟨integer_poly_root_bound (a r) (d r) (H r) (theta r) h4 h3 h5, by linarith⟩
    · simp only [ite_eq_right hrn]
      obtain ⟨-, h2, h3, h4, h5⟩ := hax r (Finset.mem_Icc.mpr ⟨by omega, hr'.2⟩)
      have hroot := integer_poly_root_bound (ax r) (dx r) B (theta r) h4 h3 h5
      have h6 : (dx r : ℝ) * B ≤ (Dx : ℝ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (by linarith)
      have h7 : 0 ≤ (Dx : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) (by linarith)
      constructor <;> nlinarith

/-! ### The bounds for the point `theta` with `m` extra coordinates -/

/-- HOL Light: Baker/heights.ml, BAKER_EXTRA_BOUNDS. For integer polynomials `g j` (`j ≤ n`) in
the `n + m` variables, at a point whose first `n` coordinates have degrees `d r` and heights
`H r` and whose `m` extra coordinates have degrees at most `Dx` and heights at most `B`: the bound
for the product of the merged degrees, the upper bound for `‖g j theta‖`, the Liouville lower
bound for `‖g n theta‖` in exp form, and the bound for the merged height sum.

Deviation: the coefficients `a r j`, `ax r j` are integers (HOL: reals with `integer`), so the
`integer` conjuncts are dropped; the hypotheses are separate arguments in HOL's order. -/
theorem baker_extra_bounds (n m : ℕ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ) (e : ℕ → ℕ)
    (G0 : ℝ) (Dx : ℕ) (B : ℝ) (theta : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ)
    (ax : ℕ → ℕ → ℤ) (_hn : 1 ≤ n) (_hDx : 1 ≤ Dx) (hG0 : 1 ≤ G0) (hB : 2 ≤ B)
    (ha : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hax : ∀ r ∈ Finset.Icc (n + 1) (n + m), 1 ≤ dx r ∧ dx r ≤ Dx ∧
      (∀ j, |(ax r j : ℝ)| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
      ∑ j ∈ Finset.range (dx r + 1), (ax r j : ℂ) * theta r ^ j = 0)
    (hg : ∀ j, j ≤ n → intpoly (Finset.Icc 1 (n + m)) e G0 (g j))
    (hne : g n theta ≠ 0) :
    ∏ r ∈ Finset.Icc 1 (n + m), (if r ≤ n then d r else dx r) ≤
        (∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m ∧
      (∀ j, j ≤ n → ‖g j theta‖ ≤
        G0 * ((∏ r ∈ Finset.Icc 1 n, (1 + (d r : ℝ) * H r) ^ e r) *
          ((1 + (Dx : ℝ)) * B) ^ (∑ r ∈ Finset.Icc (n + 1) (n + m), e r))) ∧
      Real.exp (-((((∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m : ℕ) : ℝ) *
          (Real.log (((∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m : ℕ) : ℝ) + (Real.log G0 +
            ((∑ r ∈ Finset.Icc 1 n, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)) +
              ((∑ r ∈ Finset.Icc (n + 1) (n + m), e r : ℕ) : ℝ) *
                (Real.log ((Dx : ℝ) + 1) + 3 * Real.log B)))))) ≤ ‖g n theta‖ ∧
      ∑ r ∈ Finset.Icc 1 (n + m),
          (e r : ℝ) * Real.log ((((if r ≤ n then d r else dx r) + 1 : ℕ) : ℝ) *
            (if r ≤ n then H r else B) ^ 3) ≤
        (∑ r ∈ Finset.Icc 1 n, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)) +
          ((∑ r ∈ Finset.Icc (n + 1) (n + m), e r : ℕ) : ℝ) *
            (Real.log ((Dx : ℝ) + 1) + 3 * Real.log B) := by
  obtain ⟨hmerge, hroot, hdx⟩ :=
    baker_extra_merge n m a d H Dx B theta dx ax (by linarith) ha hax
  have hprod := baker_extra_nproduct_le n m d dx Dx hdx
  have hlog := baker_extra_logsum_le n m d dx H e Dx B (by linarith) hdx
  refine ⟨hprod, fun j hj => ?_, ?_, hlog⟩
  · rw [← product_pow_cond_split n m (fun r => 1 + (d r : ℝ) * H r) ((1 + (Dx : ℝ)) * B) e]
    exact intpoly_bound (m := fun r => if r ≤ n then 1 + (d r : ℝ) * H r else (1 + (Dx : ℝ)) * B)
      (hg j hj) hroot
  · exact intpoly_liouville_exp_mono (Finset.Icc 1 (n + m)) e G0 (g n) theta
      (fun r => if r ≤ n then a r else ax r) (fun r => if r ≤ n then d r else dx r)
      (fun r => if r ≤ n then H r else B) _ _ (hg n le_rfl) hG0 hmerge hprod hlog hne

end RiemannMasullo.Baker
