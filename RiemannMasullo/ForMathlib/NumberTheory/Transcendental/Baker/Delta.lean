module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Chebyshev

/-! # Feldman Delta-functions, basis polynomials and common multiples

Ported from HOL Light, Baker/delta.ml (jrh13/hol-light, commit 1a0c0e6). -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### Elementary arithmetic -/

/-- HOL Light: Baker/delta.ml, NPRODUCT_SHIFT_BINOM. The product `(s + 1) ⋯ (s + h)` equals
`h ! * choose (s + h) h`. -/
theorem nproduct_shift_binom (s h : ℕ) :
    ∏ j ∈ Finset.Icc 1 h, (s + j) = h.factorial * (s + h).choose h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, ← Nat.add_assoc, mul_assoc,
      mul_comm ((s + h).choose h), Nat.add_one_mul_choose_eq]
    ring

/-- HOL Light: Baker/delta.ml, BINOM_LE_EXP. A binomial coefficient `choose n k` is at most
`2 ^ n`. -/
theorem binom_le_exp (n k : ℕ) : n.choose k ≤ 2 ^ n :=
  Nat.choose_le_two_pow n k

/-- HOL Light: Baker/delta.ml, FACT_DIVIDES_NPRODUCT_AP. -/
private theorem delta_fact_dvd_nproduct_ap (q r h : ℕ) :
    h.factorial ∣ q ^ h * ∏ j ∈ Finset.Icc 1 h, (r + q * j) := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  by_cases hpq : p ∣ q
  · have hk : k ≤ h := by
      have h1 := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero h)).1 hpk
      have h2 := Nat.factorization_factorial_le_div_pred hp h
      have h3 : h / (p - 1) ≤ h := Nat.div_le_self _ _
      omega
    exact Dvd.dvd.mul_right ((pow_dvd_pow p hk).trans (pow_dvd_pow_of_dvd hpq h)) _
  · apply Dvd.dvd.mul_left
    have hcop : Nat.Coprime q (p ^ k) :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm.pow_right k
    have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [← ZMod.natCast_eq_zero_iff]
    set s : ℕ := ((r : ZMod (p ^ k)) * (q : ZMod (p ^ k))⁻¹).val with hs
    have hs' : ((s : ℕ) : ZMod (p ^ k)) = r * (q : ZMod (p ^ k))⁻¹ := ZMod.natCast_zmod_val _
    have hqi : (q : ZMod (p ^ k)) * (q : ZMod (p ^ k))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hcop
    have hprod : ((∏ j ∈ Finset.Icc 1 h, (r + q * j) : ℕ) : ZMod (p ^ k)) =
        (q : ZMod (p ^ k)) ^ h * ((∏ j ∈ Finset.Icc 1 h, (s + j) : ℕ) : ZMod (p ^ k)) := by
      push_cast
      rw [show (q : ZMod (p ^ k)) ^ h = ∏ j ∈ Finset.Icc 1 h, (q : ZMod (p ^ k)) by simp,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hs']
      linear_combination (-(r : ZMod (p ^ k))) * hqi
    rw [hprod, nproduct_shift_binom]
    push_cast
    rw [(ZMod.natCast_eq_zero_iff _ _).2 hpk]
    simp

/-! ### Higher derivatives of products with a linear factor and of multiples -/

/-- HOL Light: Baker/delta.ml, HIGHER_COMPLEX_DERIVATIVE_ID_SUB_CONST. -/
private theorem delta_iteratedDeriv_sub_const (a : ℂ) (i : ℕ) (z : ℂ) :
    iteratedDeriv i (fun w : ℂ => w - a) z =
      if i = 0 then z - a else if i = 1 then 1 else 0 := by
  obtain (_ | _ | i) := i
  · simp
  · simp [iteratedDeriv_succ']
  · simp [iteratedDeriv_succ', iteratedDeriv_const]

/-- HOL Light: Baker/delta.ml, HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR. The `(n + 1)`-st
derivative of `(w - a) * g w` at a point of an open set on which `g` is holomorphic. -/
theorem higher_complex_derivative_mul_sub_factor (g : ℂ → ℂ) (s : Set ℂ) (a : ℂ) (n : ℕ) (z : ℂ)
    (hs : IsOpen s) (hg : DifferentiableOn ℂ g s) (hz : z ∈ s) :
    iteratedDeriv (n + 1) (fun w => (w - a) * g w) z =
      (z - a) * iteratedDeriv (n + 1) g z + ((n + 1 : ℕ) : ℂ) * iteratedDeriv n g z := by
  have hg' : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) g z :=
    (hg.analyticAt (hs.mem_nhds hz)).contDiffAt
  have hf : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun w : ℂ => w - a) z := by fun_prop
  rw [iteratedDeriv_fun_mul hf hg', Finset.sum_range_succ', Finset.sum_range_succ']
  simp [delta_iteratedDeriv_sub_const]
  ring

/-- HOL Light: Baker/delta.ml, HIGHER_COMPLEX_DERIVATIVE_MUL_LINEAR_FACTOR. The `m`-th derivative
of `(w + c) * g w` for an entire function `g`. -/
theorem higher_complex_derivative_mul_linear_factor (g : ℂ → ℂ) (c : ℂ) (m : ℕ) (z : ℂ)
    (hg : Differentiable ℂ g) :
    iteratedDeriv m (fun w => (w + c) * g w) z =
      (z + c) * iteratedDeriv m g z + (m : ℂ) * iteratedDeriv (m - 1) g z := by
  rcases m with _ | n
  · simp
  · have h := higher_complex_derivative_mul_sub_factor g Set.univ (-c) n z isOpen_univ
      hg.differentiableOn (Set.mem_univ z)
    simpa [sub_neg_eq_add] using h

/-- HOL Light: Baker/delta.ml, HIGHER_COMPLEX_DERIVATIVE_LMUL. A constant factor comes out of a
higher derivative. The hypotheses are those of HOL Light; Mathlib needs none of them. -/
theorem higher_complex_derivative_lmul (f : ℂ → ℂ) (c : ℂ) (s : Set ℂ) (n : ℕ) (z : ℂ)
    (_hs : IsOpen s) (_hf : DifferentiableOn ℂ f s) (_hz : z ∈ s) :
    iteratedDeriv n (fun w => c * f w) z = c * iteratedDeriv n f z :=
  iteratedDeriv_const_mul_field c f

/-! ### Integrality of normalized derivatives of products of linear factors -/

/-- HOL Light: Baker/delta.ml, CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN. If every `M / (x + c u)`
is an integer, then `M ^ m` times the `m`-th derivative at `x` of the product of the `z + c u`,
divided by `m !` and by the value of the product at `x`, is an integer. -/
theorem cproduct_linear_derivative_integer_gen {A : Type*} (U : Finset A) (c : A → ℕ) (x M : ℂ)
    (h : ∀ u ∈ U, x + (c u : ℂ) ≠ 0 ∧ ∃ k : ℤ, M / (x + (c u : ℂ)) = (k : ℂ)) (m : ℕ) :
    ∃ k : ℤ, M ^ m * (iteratedDeriv m (fun z : ℂ => ∏ u ∈ U, (z + (c u : ℂ))) x /
      ((m.factorial : ℂ) * ∏ u ∈ U, (x + (c u : ℂ)))) = (k : ℂ) := by
  induction U using Finset.cons_induction generalizing m with
  | empty =>
    rcases m with _ | m
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [iteratedDeriv_const]⟩
  | cons a U ha ih =>
    have hU : ∀ u ∈ U, x + (c u : ℂ) ≠ 0 ∧ ∃ k : ℤ, M / (x + (c u : ℂ)) = (k : ℂ) :=
      fun u hu => h u (Finset.mem_cons_of_mem hu)
    obtain ⟨hy, q, hq⟩ := h a (Finset.mem_cons_self a U)
    have hP : ∏ u ∈ U, (x + (c u : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun u hu => (hU u hu).1
    have hd : Differentiable ℂ (fun z : ℂ => ∏ u ∈ U, (z + (c u : ℂ))) := by fun_prop
    simp only [Finset.prod_cons]
    rw [higher_complex_derivative_mul_linear_factor _ (c a : ℂ) m x hd]
    rcases m with _ | m
    · obtain ⟨k0, hk0⟩ := ih hU 0
      refine ⟨k0, ?_⟩
      rw [← hk0]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
        add_zero]
      field_simp
    · obtain ⟨k0, hk0⟩ := ih hU (m + 1)
      obtain ⟨k1, hk1⟩ := ih hU m
      refine ⟨k0 + q * k1, ?_⟩
      have hm : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      push_cast
      rw [← hk0, ← hk1, ← hq, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- HOL Light: Baker/delta.ml, CPRODUCT_LINEAR_DERIVATIVE_INTEGER. The case of a natural number
`x` and a common multiple `N` of the `x + c u`. -/
theorem cproduct_linear_derivative_integer {A : Type*} (U : Finset A) (c : A → ℕ) (x N : ℕ)
    (h : ∀ u ∈ U, x + c u ≠ 0 ∧ (x + c u) ∣ N) (m : ℕ) :
    ∃ k : ℤ, (N : ℂ) ^ m * (iteratedDeriv m (fun z : ℂ => ∏ u ∈ U, (z + (c u : ℂ))) (x : ℂ) /
      ((m.factorial : ℂ) * ∏ u ∈ U, ((x : ℂ) + (c u : ℂ)))) = (k : ℂ) := by
  refine cproduct_linear_derivative_integer_gen U c (x : ℂ) (N : ℂ) (fun u hu => ?_) m
  obtain ⟨h0, q, rfl⟩ := h u hu
  have h0' : (x : ℂ) + (c u : ℂ) ≠ 0 := by exact_mod_cast h0
  refine ⟨h0', q, ?_⟩
  push_cast
  field_simp

/-! ### The Feldman Delta-functions -/

/-- HOL Light: Baker/delta.ml, feldman_delta. The Feldman function
`Δ(z; k) = (z + 1) ⋯ (z + k) / k !`. -/
noncomputable def feldmanDelta (k : ℕ) (z : ℂ) : ℂ :=
  (∏ j ∈ Finset.Icc 1 k, (z + (j : ℂ))) / (k.factorial : ℂ)

/-- HOL Light: Baker/delta.ml, HOLOMORPHIC_ON_FELDMAN_DELTA. -/
private theorem delta_differentiable_feldmanDelta (k : ℕ) : Differentiable ℂ (feldmanDelta k) := by
  unfold feldmanDelta
  fun_prop

/-- HOL Light: Baker/delta.ml, FELDMAN_DELTA_NUM. At a natural number `x` the value of
`Δ(·; k)` is the binomial coefficient `choose (x + k) k`. -/
theorem feldman_delta_num (k x : ℕ) : feldmanDelta k (x : ℂ) = ((x + k).choose k : ℂ) := by
  have h2 : (∏ j ∈ Finset.Icc 1 k, ((x : ℂ) + (j : ℂ))) =
      (k.factorial : ℂ) * ((x + k).choose k : ℂ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (nproduct_shift_binom x k)
  rw [feldmanDelta, h2, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))]

/-- HOL Light: Baker/delta.ml, FELDMAN_DELTA_BOUND. -/
private theorem delta_feldman_delta_bound (k : ℕ) (z : ℂ) (n : ℕ) (hz : ‖z‖ ≤ n) :
    ‖feldmanDelta k z‖ ≤ 2 ^ (n + k) := by
  rw [feldmanDelta, norm_div, norm_prod, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ∏ j ∈ Finset.Icc 1 k, ‖z + (j : ℂ)‖ ≤ ∏ j ∈ Finset.Icc 1 k, ((n : ℝ) + (j : ℝ)) :=
        by
        gcongr with j hj
        exact (norm_add_le _ _).trans (by simpa using hz)
    _ = (k.factorial : ℝ) * ((n + k).choose k : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (nproduct_shift_binom n k)
    _ ≤ 2 ^ (n + k) * (k.factorial : ℝ) := by
        rw [mul_comm]
        gcongr
        exact_mod_cast Nat.choose_le_two_pow (n + k) k

/-- HOL Light: Baker/delta.ml, FELDMAN_DELTA_RATIONAL. -/
private theorem delta_feldman_delta_rational (h q r : ℕ) (hq : q ≠ 0) :
    ∃ k : ℤ, (q : ℂ) ^ (2 * h) * feldmanDelta h ((r : ℂ) / (q : ℂ)) = (k : ℂ) := by
  obtain ⟨d, hd⟩ := delta_fact_dvd_nproduct_ap q r h
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hf : (h.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero h)
  have h1 : (q : ℂ) ^ h * ∏ j ∈ Finset.Icc 1 h, ((r : ℂ) / (q : ℂ) + (j : ℂ)) =
      ((∏ j ∈ Finset.Icc 1 h, (r + q * j) : ℕ) : ℂ) := by
    rw [show (q : ℂ) ^ h = ∏ j ∈ Finset.Icc 1 h, (q : ℂ) by simp, ← Finset.prod_mul_distrib]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp
  have h2 : (q : ℂ) ^ h * ((∏ j ∈ Finset.Icc 1 h, (r + q * j) : ℕ) : ℂ) =
      (h.factorial : ℂ) * (d : ℂ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hd
  refine ⟨d, ?_⟩
  rw [feldmanDelta, two_mul, pow_add, mul_assoc, ← mul_div_assoc, h1, ← mul_div_assoc, h2,
    mul_div_cancel_left₀ _ hf]
  simp

/-! ### The basis polynomials -/

/-- HOL Light: Baker/delta.ml, feldman_basis. The basis polynomial
`Δ(z; a) * Δ(z; h) ^ (b + 1)`. -/
noncomputable def feldmanBasis (h a b : ℕ) (z : ℂ) : ℂ :=
  feldmanDelta a z * feldmanDelta h z ^ (b + 1)

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_CPRODUCT. The basis polynomial as a product of
linear factors `w + j` over an index set of pairs, divided by `a ! * h ! ^ (b + 1)`. -/
theorem feldman_basis_cproduct (h a b : ℕ) (w : ℂ) :
    feldmanBasis h a b w =
      (∏ u ∈ (({0} : Finset ℕ) ×ˢ Finset.Icc 1 a) ∪ (Finset.Icc 1 (b + 1) ×ˢ Finset.Icc 1 h),
        (w + (u.2 : ℂ))) / ((a.factorial * h.factorial ^ (b + 1) : ℕ) : ℂ) := by
  have hdisj : Disjoint (({0} : Finset ℕ) ×ˢ Finset.Icc 1 a)
      (Finset.Icc 1 (b + 1) ×ˢ Finset.Icc 1 h) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Icc] at h1 h2
    omega
  rw [Finset.prod_union hdisj, Finset.prod_product, Finset.prod_product]
  simp only [Finset.card_singleton, pow_one, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel,
    feldmanBasis, feldmanDelta, div_pow]
  push_cast
  rw [div_mul_div_comm]

/-- HOL Light: Baker/delta.ml, HOLOMORPHIC_ON_FELDMAN_BASIS. The basis polynomials are holomorphic
on every set. -/
theorem holomorphic_on_feldman_basis (h a b : ℕ) (s : Set ℂ) :
    DifferentiableOn ℂ (feldmanBasis h a b) s := by
  have : Differentiable ℂ (feldmanBasis h a b) := by
    unfold feldmanBasis
    exact (delta_differentiable_feldmanDelta a).mul ((delta_differentiable_feldmanDelta h).pow _)
  exact this.differentiableOn

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_NUM. -/
private theorem delta_feldman_basis_num (h a b x : ℕ) :
    feldmanBasis h a b (x : ℂ) = (((x + a).choose a * (x + h).choose h ^ (b + 1) : ℕ) : ℂ) := by
  simp [feldmanBasis, feldman_delta_num]

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_DERIV_INTEGER. If `a ≤ h` and `N` is a common
multiple of `x + 1, …, x + h`, then `N ^ m` times the `m`-th derivative of the basis polynomial at
`x`, divided by `m !`, is an integer. -/
theorem feldman_basis_deriv_integer (h a b x N : ℕ) (hah : a ≤ h)
    (hN : ∀ i, 1 ≤ i → i ≤ h → (x + i) ∣ N) (m : ℕ) :
    ∃ k : ℤ, (N : ℂ) ^ m * (iteratedDeriv m (feldmanBasis h a b) (x : ℂ) / (m.factorial : ℂ)) =
      (k : ℂ) := by
  set U : Finset (ℕ × ℕ) :=
    (({0} : Finset ℕ) ×ˢ Finset.Icc 1 a) ∪ (Finset.Icc 1 (b + 1) ×ˢ Finset.Icc 1 h) with hUdef
  set K : ℕ := a.factorial * h.factorial ^ (b + 1) with hKdef
  have hfun : feldmanBasis h a b = fun w => (∏ u ∈ U, (w + (u.2 : ℂ))) / (K : ℂ) :=
    funext (feldman_basis_cproduct h a b)
  have hmem : ∀ u ∈ U, 1 ≤ u.2 ∧ u.2 ≤ h := by
    rintro ⟨i, j⟩ hu
    simp only [hUdef, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_Icc] at hu
    omega
  have hU : ∀ u ∈ U, x + u.2 ≠ 0 ∧ (x + u.2) ∣ N := fun u hu =>
    ⟨by have := (hmem u hu).1; omega, hN u.2 (hmem u hu).1 (hmem u hu).2⟩
  obtain ⟨k, hk⟩ := cproduct_linear_derivative_integer U (fun u => u.2) x N hU m
  have hP : ∏ u ∈ U, ((x : ℂ) + (u.2 : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun u hu => by exact_mod_cast (hU u hu).1
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hnum : (∏ u ∈ U, ((x : ℂ) + (u.2 : ℂ))) / (K : ℂ) =
      (((x + a).choose a * (x + h).choose h ^ (b + 1) : ℕ) : ℂ) := by
    rw [← delta_feldman_basis_num, feldman_basis_cproduct]
  refine ⟨k * ((x + a).choose a * (x + h).choose h ^ (b + 1) : ℕ), ?_⟩
  rw [hfun, iteratedDeriv_div_const, Int.cast_mul, Int.cast_natCast, ← hk, ← hnum]
  field_simp

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_RATIONAL. The value of the basis polynomial at a
rational `r / q` becomes an integer after multiplication by `q ^ (2 a + 2 h (b + 1))`. -/
theorem feldman_basis_rational (h a b q r : ℕ) (hq : q ≠ 0) :
    ∃ k : ℤ, (q : ℂ) ^ (2 * a + 2 * h * (b + 1)) * feldmanBasis h a b ((r : ℂ) / (q : ℂ)) =
      (k : ℂ) := by
  obtain ⟨ka, hka⟩ := delta_feldman_delta_rational a q r hq
  obtain ⟨kh, hkh⟩ := delta_feldman_delta_rational h q r hq
  refine ⟨ka * kh ^ (b + 1), ?_⟩
  push_cast
  rw [← hka, ← hkh, feldmanBasis]
  ring

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_POLYFUN. The basis polynomial is a polynomial
function of exact degree `a + h * (b + 1)`. -/
theorem feldman_basis_polyfun (h a b : ℕ) :
    ∃ e : ℕ → ℂ, e (a + h * (b + 1)) ≠ 0 ∧
      ∀ z, feldmanBasis h a b z = ∑ i ∈ Finset.range (a + h * (b + 1) + 1), e i * z ^ i := by
  open Polynomial in
  have key : ∀ k : ℕ, (∏ j ∈ Finset.Icc 1 k, (X + C (j : ℂ))).Monic ∧
      (∏ j ∈ Finset.Icc 1 k, (X + C (j : ℂ))).natDegree = k := by
    intro k
    refine ⟨monic_prod_of_monic _ _ fun j _ => monic_X_add_C _, ?_⟩
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_add_C _]
    simp only [natDegree_X_add_C]
    simp
  open Polynomial in
  set Q : ℂ[X] := (∏ j ∈ Finset.Icc 1 a, (X + C (j : ℂ))) *
    (∏ j ∈ Finset.Icc 1 h, (X + C (j : ℂ))) ^ (b + 1) with hQ
  have hmonic : Q.Monic := (key a).1.mul ((key h).1.pow _)
  have hdeg : Q.natDegree = a + h * (b + 1) := by
    rw [hQ, ((key a).1).natDegree_mul ((key h).1.pow _), ((key h).1).natDegree_pow, (key a).2,
      (key h).2, mul_comm]
  set K : ℂ := (a.factorial : ℂ) * (h.factorial : ℂ) ^ (b + 1) with hK
  have hK0 : K ≠ 0 := by
    have h1 : (a.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero a)
    have h2 : (h.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero h)
    exact mul_ne_zero h1 (pow_ne_zero _ h2)
  refine ⟨fun i => Q.coeff i / K, ?_, fun z => ?_⟩
  · have : Q.coeff (a + h * (b + 1)) = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
    simp [this, hK0]
  · have heval : Q.eval z = ∑ i ∈ Finset.range (a + h * (b + 1) + 1), Q.coeff i * z ^ i := by
      rw [← hdeg]; exact Polynomial.eval_eq_sum_range z
    have hQz : Q.eval z = (∏ j ∈ Finset.Icc 1 a, (z + (j : ℂ))) *
        (∏ j ∈ Finset.Icc 1 h, (z + (j : ℂ))) ^ (b + 1) := by
      simp [hQ, Polynomial.eval_prod]
    have : feldmanBasis h a b z = Q.eval z / K := by
      rw [hQz, hK, feldmanBasis, feldmanDelta, feldmanDelta, div_pow, div_mul_div_comm]
    rw [this, heval, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_DERIV_BOUND_UNIFORM. A uniform bound for the
normalized derivatives of the basis polynomials with `a < h` and `b ≤ L` on a disc. -/
theorem feldman_basis_deriv_bound_uniform (h L a b j : ℕ) (z : ℂ) (N : ℕ)
    (hah : a < h) (hbL : b ≤ L) (hz : ‖z‖ + 1 ≤ N) :
    ‖iteratedDeriv j (feldmanBasis h a b) z / (j.factorial : ℂ)‖ ≤ 2 ^ ((L + 2) * (N + h)) := by
  have hC : ∀ w ∈ Metric.sphere z 1,
      ‖feldmanBasis h a b w‖ ≤ 2 ^ ((N + a) + (b + 1) * (N + h)) := by
    intro w hw
    have hw' : ‖w‖ ≤ N := by
      have h1 : ‖w - z‖ = 1 := by simpa [dist_eq_norm] using hw
      calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ N := by linarith
    rw [feldmanBasis, norm_mul, norm_pow, pow_add (2 : ℝ) (N + a), pow_mul' (2 : ℝ)]
    gcongr <;> exact delta_feldman_delta_bound _ _ _ hw'
  have hd : Differentiable ℂ (feldmanBasis h a b) := fun w =>
    (holomorphic_on_feldman_basis h a b Set.univ).differentiableAt Filter.univ_mem
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j one_pos
    hd.diffContOnCl hC
  have hexp : (N + a) + (b + 1) * (N + h) ≤ (L + 2) * (N + h) := by
    have := Nat.mul_le_mul_right (N + h) (show b + 1 ≤ L + 1 by omega)
    nlinarith
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖iteratedDeriv j (feldmanBasis h a b) z‖
      ≤ (j.factorial : ℝ) * 2 ^ ((N + a) + (b + 1) * (N + h)) / 1 ^ j := hcauchy
    _ = 2 ^ ((N + a) + (b + 1) * (N + h)) * (j.factorial : ℝ) := by simp [mul_comm]
    _ ≤ 2 ^ ((L + 2) * (N + h)) * (j.factorial : ℝ) := by
        gcongr
        norm_num

/-! ### Common multiples of consecutive integers -/

/-- HOL Light: Baker/delta.ml, NUMSEG_COMMON_MULTIPLE. There is a nonzero common multiple of
`1, …, n` of size at most `exp (18 n)`. -/
theorem numseg_common_multiple (n : ℕ) :
    ∃ M : ℕ, M ≠ 0 ∧ (∀ i, 1 ≤ i → i ≤ n → i ∣ M) ∧ (M : ℝ) ≤ Real.exp (18 * (n : ℝ)) := by
  refine ⟨Nat.lcmUpto n, Nat.lcmUpto_ne_zero n, fun i h1 h2 => ?_, ?_⟩
  · exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  · have hpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
    rw [← Real.exp_log hpos, Real.exp_le_exp, ← Chebyshev.psi_eq_log_lcmUpto]
    have h1 := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (Nat.cast_nonneg n)
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- HOL Light: Baker/delta.ml, SHIFTED_COMMON_MULTIPLE (with NAIR_DIVIDES and
BINOM_SHIFT_PRODUCT). -/
private theorem delta_shifted_common_multiple (x k L : ℕ) (hL : ∀ i, 1 ≤ i → i ≤ k → i ∣ L)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ k) : (x + j) ∣ L * (x + k).choose k := by
  have hlcm : Nat.lcmUpto k ∣ L :=
    Finset.lcm_dvd fun i hi => hL i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
  have hnair : j * k.choose j ∣ L := (Chebyshev.mul_choose_dvd_lcmUpto (by omega) h2).trans hlcm
  refine Dvd.dvd.trans ?_ (Nat.mul_dvd_mul_right hnair _)
  obtain ⟨J, rfl⟩ : ∃ J, j = J + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = J + 1 + m := ⟨k - (J + 1), by omega⟩
  have hA : (x + (J + 1 + m)).choose (J + 1 + m) * (J + 1 + m).choose (J + 1) =
      (x + (J + 1 + m)).choose (J + 1) * (x + m).choose m := by
    rw [Nat.choose_mul (show J + 1 ≤ J + 1 + m by omega)]
    congr 2 <;> omega
  have hB : (x + (J + 1 + m)).choose (x + (J + 1)) * (x + (J + 1)).choose (J + 1) =
      (x + (J + 1 + m)).choose (J + 1) * (x + m).choose x := by
    rw [Nat.choose_mul (show J + 1 ≤ x + (J + 1) by omega)]
    congr 2 <;> omega
  have hs1 : (x + (J + 1 + m)).choose (x + (J + 1)) = (x + (J + 1 + m)).choose m :=
    Nat.choose_symm_of_eq_add (by omega)
  have hs2 : (x + m).choose x = (x + m).choose m := Nat.choose_symm_add
  have hC : (x + J + 1) * (x + J).choose J = (x + (J + 1)).choose (J + 1) * (J + 1) :=
    Nat.add_one_mul_choose_eq (x + J) J
  rw [hs1, hs2] at hB
  refine ⟨(x + J).choose J * (x + (J + 1 + m)).choose m, ?_⟩
  calc (J + 1) * (J + 1 + m).choose (J + 1) * (x + (J + 1 + m)).choose (J + 1 + m)
      = (J + 1) * ((x + (J + 1 + m)).choose (J + 1 + m) * (J + 1 + m).choose (J + 1)) := by ring
    _ = (J + 1) * ((x + (J + 1 + m)).choose m * (x + (J + 1)).choose (J + 1)) := by
        rw [hA, ← hB]
    _ = ((x + (J + 1)).choose (J + 1) * (J + 1)) * (x + (J + 1 + m)).choose m := by ring
    _ = (x + (J + 1)) * ((x + J).choose J * (x + (J + 1 + m)).choose m) := by
        rw [← hC]; ring

/-- HOL Light: Baker/delta.ml, BINOM_UPPER_BOUND_EXP. -/
private theorem delta_binom_upper_bound_exp (x k : ℕ) (hk : 1 ≤ k) :
    ((x + k).choose k : ℝ) ≤ (Real.exp 1 * (((x : ℝ) + (k : ℝ)) / (k : ℝ))) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h1 : ((x + k).choose k : ℝ) ≤ (((x + k : ℕ) : ℝ)) ^ k / (k.factorial : ℝ) :=
    Nat.choose_le_pow_div k (x + k)
  have h2 : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp _ hk0.le k
  have h3 : Real.exp 1 ^ k = Real.exp k := by rw [← Real.exp_nat_mul, mul_one]
  calc ((x + k).choose k : ℝ) ≤ (((x + k : ℕ) : ℝ)) ^ k / (k.factorial : ℝ) := h1
    _ = (((x : ℝ) + (k : ℝ)) / (k : ℝ)) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by
        push_cast
        rw [div_pow]
        field_simp
    _ ≤ (((x : ℝ) + (k : ℝ)) / (k : ℝ)) ^ k * Real.exp k := by gcongr
    _ = (Real.exp 1 * (((x : ℝ) + (k : ℝ)) / (k : ℝ))) ^ k := by rw [mul_pow, h3, mul_comm]

/-- HOL Light: Baker/delta.ml, SHIFTED_COMMON_MULTIPLE_BOUND. For `1 ≤ k` there is a nonzero
common multiple of `x + 1, …, x + k` of size at most `(exp 19 * (x + k) / k) ^ k`. -/
theorem shifted_common_multiple_bound (x k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, N ≠ 0 ∧ (∀ j, 1 ≤ j → j ≤ k → (x + j) ∣ N) ∧
      (N : ℝ) ≤ (Real.exp 19 * (((x : ℝ) + (k : ℝ)) / (k : ℝ))) ^ k := by
  obtain ⟨L, hL0, hLdvd, hLle⟩ := numseg_common_multiple k
  refine ⟨L * (x + k).choose k, mul_ne_zero hL0 (Nat.choose_pos (by omega)).ne',
    delta_shifted_common_multiple x k L hLdvd, ?_⟩
  have hb := delta_binom_upper_bound_exp x k hk
  have h19 : Real.exp 19 ^ k = Real.exp (18 * (k : ℝ)) * Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc ((L * (x + k).choose k : ℕ) : ℝ) = (L : ℝ) * ((x + k).choose k : ℝ) := by push_cast; ring
    _ ≤ Real.exp (18 * (k : ℝ)) * (Real.exp 1 * (((x : ℝ) + (k : ℝ)) / (k : ℝ))) ^ k := by
        gcongr
    _ = (Real.exp 19 * (((x : ℝ) + (k : ℝ)) / (k : ℝ))) ^ k := by
        rw [mul_pow, mul_pow, h19]
        ring

end RiemannMasullo.Baker
