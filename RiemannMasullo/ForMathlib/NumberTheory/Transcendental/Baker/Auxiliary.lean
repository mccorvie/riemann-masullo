module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Delta
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.IntPoly
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # The auxiliary function of Baker in single-variable form

Ported from HOL Light, Baker/auxiliary.ml (jrh13/hol-light, commit 1a0c0e6), with
`CARD_BAKER_INDEX` from Baker/aux_arith.ml.

For a multi-index `m = (m 0, …, m (n - 1))` the auxiliary function is
`F_m(z) = ∑_λ p(λ) D^(m 0) G_λ(z) ∏_{r=1}^{n-1} (γ_r lg_r)^(m r) exp(z ∑_{r=1}^{n-1} γ_r lg_r)`,
with `λ = (a, b, mu)`, `a < h`, `b ≤ L`, `mu r ≤ L` for `1 ≤ r ≤ n`, `γ_r = mu r + mu n * beta r`
and `G_λ(w) = feldmanBasis h a b w * exp(mu n * beta 0 * w)`.

Products and sums are bracketed as HOL Light parses them (to the right). -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### Definitions -/

/-- HOL Light: Baker/auxiliary.ml, baker_index. The index set of the auxiliary function: the
triples `(a, b, mu)` with `a < h`, `b ≤ L` and `mu` in the cartesian product of `n` copies of
`0..L` (indexed by `1..n`, and `0` outside `1..n`). -/
def bakerIndex (h L n : ℕ) : Finset (ℕ × ℕ × (ℕ → ℕ)) :=
  Finset.range h ×ˢ
    (Finset.range (L + 1) ×ˢ cartesianProduct (Finset.Icc 1 n) (fun _ => Finset.range (L + 1)))

/-- HOL Light: Baker/auxiliary.ml, baker_gamma. The number `γ_r = mu r + mu n * beta r`. -/
noncomputable def bakerGamma (n : ℕ) (beta : ℕ → ℂ) (mu : ℕ → ℕ) (r : ℕ) : ℂ :=
  (mu r : ℂ) + (mu n : ℂ) * beta r

/-- HOL Light: Baker/auxiliary.ml, baker_term. The term of the auxiliary function belonging to
the index `x = (a, b, mu)`.

Deviation: HOL defines it by pattern matching on the triple `(a, b, mu)`; here it is a function
of `x` with `a = x.1`, `b = x.2.1`, `mu = x.2.2`. The coefficient family `p` is integer-valued
(HOL: real-valued, and an integer in every use). -/
noncomputable def bakerTerm (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (x : ℕ × ℕ × (ℕ → ℕ)) (z : ℂ) : ℂ :=
  ((p x : ℤ) : ℂ) *
    (iteratedDeriv (m 0)
        (fun w => feldmanBasis h x.1 x.2.1 w * Complex.exp (((x.2.2 n : ℂ) * beta 0) * w)) z *
      ((∏ r ∈ Finset.Icc 1 (n - 1), (bakerGamma n beta x.2.2 r * lg r) ^ m r) *
        Complex.exp (z * ∑ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta x.2.2 r * lg r)))

/-- HOL Light: Baker/auxiliary.ml, baker_aux. The auxiliary function `F_m` of Baker as a function
of one variable. -/
noncomputable def bakerAux (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (z : ℂ) : ℂ :=
  ∑ x ∈ bakerIndex h L n, bakerTerm n h p beta lg m x z

/-- HOL Light: Baker/auxiliary.ml, baker_omega. The exponent
`mu n * beta 0 + ∑_{r=1}^{n-1} γ_r lg_r` of a term. -/
noncomputable def bakerOmega (n : ℕ) (beta lg : ℕ → ℂ) (mu : ℕ → ℕ) : ℂ :=
  (mu n : ℂ) * beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta mu r * lg r

/-- HOL Light: Baker/auxiliary.ml, baker_algterm. The term of the algebraic counterpart of the
auxiliary function: the true logarithm `lg n` in the exponent, and no factor `∏ lg r ^ m r`.

Deviation: a function of `x` with `a = x.1`, `b = x.2.1`, `mu = x.2.2`, and `p` integer-valued,
as for `bakerTerm`. -/
noncomputable def bakerAlgterm (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (x : ℕ × ℕ × (ℕ → ℕ)) (z : ℂ) : ℂ :=
  ((p x : ℤ) : ℂ) *
    ((∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
        (iteratedDeriv j (feldmanBasis h x.1 x.2.1) z * ((x.2.2 n : ℂ) * beta 0) ^ (m 0 - j))) *
      ((∏ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta x.2.2 r ^ m r) *
        Complex.exp (z * ∑ r ∈ Finset.Icc 1 n, (x.2.2 r : ℂ) * lg r)))

/-- HOL Light: Baker/auxiliary.ml, baker_alg. The algebraic counterpart of the auxiliary
function. -/
noncomputable def bakerAlg (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (z : ℂ) : ℂ :=
  ∑ x ∈ bakerIndex h L n, bakerAlgterm n h p beta lg m x z

/-! ### The index set -/

/-- Membership in `bakerIndex` (HOL Light unfolds `baker_index`, `IN_CROSS` and
`cartesian_product` for this). -/
theorem mem_bakerIndex {h L n a b : ℕ} {mu : ℕ → ℕ} :
    (a, b, mu) ∈ bakerIndex h L n ↔
      a < h ∧ b ≤ L ∧ (∀ r ∈ Finset.Icc 1 n, mu r ≤ L) ∧ ∀ r, r ∉ Finset.Icc 1 n → mu r = 0 := by
  simp only [bakerIndex, Finset.mem_product, Finset.mem_range, mem_cartesianProduct,
    Nat.lt_succ_iff, Nat.default_eq_zero]

/-- HOL Light: Baker/aux_arith.ml, CARD_BAKER_INDEX. The number of indices is
`h * (L + 1) * (L + 1) ^ n`. -/
theorem card_baker_index (h L n : ℕ) :
    (bakerIndex h L n).card = h * ((L + 1) * (L + 1) ^ n) := by
  simp [bakerIndex, card_cartesian_product]

/-! ### The derivative relation -/

/-- HOL Light: Baker/auxiliary.ml, CPRODUCT_POW_INCREMENT. Raising one exponent of a product of
powers by one multiplies the product by the corresponding base. -/
theorem cproduct_pow_increment (s : Finset ℕ) (x : ℕ → ℂ) (m : ℕ → ℕ) (i : ℕ) (hi : i ∈ s) :
    ∏ r ∈ s, x r ^ (if r = i then m r + 1 else m r) = x i * ∏ r ∈ s, x r ^ m r := by
  have h1 : ∏ r ∈ s.erase i, x r ^ (if r = i then m r + 1 else m r) =
      ∏ r ∈ s.erase i, x r ^ m r :=
    Finset.prod_congr rfl fun r hr => by rw [ite_eq_right (Finset.ne_of_mem_erase hr)]
  rw [← Finset.mul_prod_erase s _ hi, ← Finset.mul_prod_erase s (fun r => x r ^ m r) hi, h1]
  simp only [↓reduceIte]
  ring

private theorem auxiliary_differentiable_feldmanBasis (h a b : ℕ) :
    Differentiable ℂ (feldmanBasis h a b) :=
  differentiableOn_univ.mp (holomorphic_on_feldman_basis h a b Set.univ)

private theorem auxiliary_differentiable_baker_g (h a b : ℕ) (c : ℂ) :
    Differentiable ℂ (fun w => feldmanBasis h a b w * Complex.exp (c * w)) :=
  (auxiliary_differentiable_feldmanBasis h a b).mul
    ((differentiable_id.const_mul c).cexp)

/-- HOL Light: Baker/auxiliary.ml, HOLOMORPHIC_ON_BAKER_G. The functions
`w ↦ feldmanBasis h a b w * exp (c * w)` are holomorphic on every set. -/
theorem holomorphic_on_baker_g (h a b : ℕ) (c : ℂ) (s : Set ℂ) :
    DifferentiableOn ℂ (fun w => feldmanBasis h a b w * Complex.exp (c * w)) s :=
  (auxiliary_differentiable_baker_g h a b c).differentiableOn

private theorem auxiliary_hasDerivAt (c P s : ℂ) (G : ℂ → ℂ) (hG : Differentiable ℂ G) (k : ℕ)
    (z : ℂ) :
    HasDerivAt (fun z => c * (iteratedDeriv k G z * (P * Complex.exp (z * s))))
      (c * (iteratedDeriv (k + 1) G z * (P * Complex.exp (z * s))) +
        c * (iteratedDeriv k G z * ((s * P) * Complex.exp (z * s)))) z := by
  have hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G z) z := by
    rw [iteratedDeriv_succ]
    exact ((ContDiff.differentiable_iteratedDeriv' k hG.contDiff) z).hasDerivAt
  have hE : HasDerivAt (fun y : ℂ => Complex.exp (y * s)) (Complex.exp (z * s) * s) z := by
    simpa using ((hasDerivAt_id z).mul_const s).cexp
  exact ((hD.mul (hE.const_mul P)).const_mul c).congr_deriv (by ring)

/-- HOL Light: Baker/auxiliary.ml, BAKER_TERM_HAS_DERIVATIVE. The derivative of a term is the
sum of the terms with one exponent `m i`, `i = 0, 1, …, n - 1`, raised by one. -/
theorem baker_term_has_derivative (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (a b : ℕ) (mu : ℕ → ℕ) (z : ℂ) :
    HasDerivAt (fun z => bakerTerm n h p beta lg m (a, b, mu) z)
      (bakerTerm n h p beta lg (fun r => if r = 0 then m r + 1 else m r) (a, b, mu) z +
        ∑ i ∈ Finset.Icc 1 (n - 1),
          bakerTerm n h p beta lg (fun r => if r = i then m r + 1 else m r) (a, b, mu) z) z := by
  have key := auxiliary_hasDerivAt ((p (a, b, mu) : ℤ) : ℂ)
    (∏ r ∈ Finset.Icc 1 (n - 1), (bakerGamma n beta mu r * lg r) ^ m r)
    (∑ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta mu r * lg r)
    (fun w => feldmanBasis h a b w * Complex.exp (((mu n : ℂ) * beta 0) * w))
    (auxiliary_differentiable_baker_g h a b _) (m 0) z
  refine HasDerivAt.congr_deriv key ?_
  have hP0 : ∀ r ∈ Finset.Icc 1 (n - 1),
      (bakerGamma n beta mu r * lg r) ^ (if r = 0 then m r + 1 else m r) =
        (bakerGamma n beta mu r * lg r) ^ m r := fun r hr => by
    rw [ite_eq_right (by have := Finset.mem_Icc.mp hr; omega)]
  have hsum : ∑ i ∈ Finset.Icc 1 (n - 1),
      bakerTerm n h p beta lg (fun r => if r = i then m r + 1 else m r) (a, b, mu) z =
      ∑ i ∈ Finset.Icc 1 (n - 1), ((p (a, b, mu) : ℤ) : ℂ) *
        (iteratedDeriv (m 0)
            (fun w => feldmanBasis h a b w * Complex.exp (((mu n : ℂ) * beta 0) * w)) z *
          (((bakerGamma n beta mu i * lg i) *
              ∏ r ∈ Finset.Icc 1 (n - 1), (bakerGamma n beta mu r * lg r) ^ m r) *
            Complex.exp (z * ∑ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta mu r * lg r))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi0 : ¬ 0 = i := by have := Finset.mem_Icc.mp hi; omega
    simp only [bakerTerm, ite_eq_right hi0]
    rw [cproduct_pow_increment _ (fun r => bakerGamma n beta mu r * lg r) m i hi]
  rw [hsum]
  simp only [bakerTerm, ↓reduceIte]
  rw [Finset.prod_congr rfl hP0]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- HOL Light: Baker/auxiliary.ml, BAKER_AUX_HAS_DERIVATIVE. The derivative relation
`D F_m = ∑_{i<n} F_{m + e_i}`. The hypothesis `1 ≤ n` is HOL's; with the range written as
`Finset.range (n - 1 + 1)` it is not used. -/
theorem baker_aux_has_derivative (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (z : ℂ) (_hn : 1 ≤ n) :
    HasDerivAt (bakerAux n h L p beta lg m)
      (∑ i ∈ Finset.range (n - 1 + 1),
        bakerAux n h L p beta lg (fun r => if r = i then m r + 1 else m r) z) z := by
  have hI : Finset.Ico (0 + 1) (n - 1 + 1) = Finset.Icc 1 (n - 1) := by
    ext r
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simp only [bakerAux]
  rw [Finset.sum_comm]
  refine HasDerivAt.fun_sum fun x _ => ?_
  obtain ⟨a, b, mu⟩ := x
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hI]
  exact baker_term_has_derivative n h p beta lg m a b mu z

/-- HOL Light: Baker/auxiliary.ml, BAKER_AUX_HOLOMORPHIC. The auxiliary function is holomorphic
on every set. -/
theorem baker_aux_holomorphic (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (s : Set ℂ) (hn : 1 ≤ n) :
    DifferentiableOn ℂ (bakerAux n h L p beta lg m) s := fun z _ =>
  (baker_aux_has_derivative n h L p beta lg m z hn).differentiableAt.differentiableWithinAt

/-- HOL Light: Baker/auxiliary.ml, BAKER_AUX_DERIVATIVE. The derivative of the auxiliary
function as a function. -/
theorem baker_aux_derivative (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (hn : 1 ≤ n) :
    deriv (bakerAux n h L p beta lg m) = fun z => ∑ i ∈ Finset.range (n - 1 + 1),
      bakerAux n h L p beta lg (fun r => if r = i then m r + 1 else m r) z :=
  funext fun z => (baker_aux_has_derivative n h L p beta lg m z hn).deriv

/-! ### Explicit form of the terms and the upper bound -/

/-- HOL Light: Baker/auxiliary.ml, HIGHER_COMPLEX_DERIVATIVE_CEXP_LINEAR. The higher derivatives
of `w ↦ exp (c * w)`. -/
theorem higher_complex_derivative_cexp_linear (c : ℂ) (k : ℕ) :
    iteratedDeriv k (fun w => Complex.exp (c * w)) = fun w => c ^ k * Complex.exp (c * w) :=
  iteratedDeriv_cexp_const_mul k c

/-- HOL Light: Baker/auxiliary.ml, FACT_LE_POW. `j ! ≤ m ^ j` for `j ≤ m`. -/
theorem fact_le_pow (j m : ℕ) (hjm : j ≤ m) : j.factorial ≤ m ^ j :=
  (Nat.factorial_le_pow j).trans (Nat.pow_le_pow_left hjm j)

/-- HOL Light: Baker/auxiliary.ml, SUM_BINOM_FACT_POW_LE. -/
private theorem auxiliary_sum_binom_fact_pow_le (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * j.factorial * x ^ (m - j) ≤
      ((m : ℝ) + x) ^ m := by
  rw [add_pow]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hf : (j.factorial : ℝ) ≤ (m : ℝ) ^ j := by exact_mod_cast fact_le_pow j m hjm
  calc (m.choose j : ℝ) * j.factorial * x ^ (m - j)
      ≤ (m.choose j : ℝ) * (m : ℝ) ^ j * x ^ (m - j) := by gcongr
    _ = (m : ℝ) ^ j * x ^ (m - j) * (m.choose j : ℝ) := by ring

/-- HOL Light: Baker/auxiliary.ml, BAKER_TERM_EXPLICIT. The term with the derivative of the
product expanded by the Leibniz rule. -/
theorem baker_term_explicit (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (a b : ℕ) (mu : ℕ → ℕ) (z : ℂ) :
    bakerTerm n h p beta lg m (a, b, mu) z =
      ((p (a, b, mu) : ℤ) : ℂ) *
        ((∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
            (iteratedDeriv j (feldmanBasis h a b) z * ((mu n : ℂ) * beta 0) ^ (m 0 - j))) *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (bakerGamma n beta mu r * lg r) ^ m r) *
            Complex.exp (z * bakerOmega n beta lg mu))) := by
  have hB : ContDiffAt ℂ ((m 0 : ℕ) : WithTop ℕ∞) (feldmanBasis h a b) z :=
    (auxiliary_differentiable_feldmanBasis h a b).contDiff.contDiffAt
  have hE : ContDiffAt ℂ ((m 0 : ℕ) : WithTop ℕ∞)
      (fun w : ℂ => Complex.exp (((mu n : ℂ) * beta 0) * w)) z := by fun_prop
  simp only [bakerTerm, bakerOmega]
  rw [iteratedDeriv_fun_mul hB hE]
  simp only [iteratedDeriv_cexp_const_mul]
  have hS : ∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
        iteratedDeriv j (feldmanBasis h a b) z *
        (((mu n : ℂ) * beta 0) ^ (m 0 - j) * Complex.exp (((mu n : ℂ) * beta 0) * z)) =
      (∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
        (iteratedDeriv j (feldmanBasis h a b) z * ((mu n : ℂ) * beta 0) ^ (m 0 - j))) *
        Complex.exp (((mu n : ℂ) * beta 0) * z) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hS, mul_add z, Complex.exp_add, mul_comm z ((mu n : ℂ) * beta 0)]
  ring

/-- HOL Light: Baker/auxiliary.ml, BAKER_DPART_BOUND. The bound for the Leibniz sum of a term on
the disc `‖z‖ + 1 ≤ N`. -/
theorem baker_dpart_bound (h L a b m : ℕ) (z : ℂ) (N : ℕ) (c : ℂ) (X : ℝ)
    (hah : a < h) (hbL : b ≤ L) (hz : ‖z‖ + 1 ≤ N) (hc : ‖c‖ ≤ X) :
    ‖∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
        (iteratedDeriv j (feldmanBasis h a b) z * c ^ (m - j))‖ ≤
      2 ^ ((L + 2) * (N + h)) * ((m : ℝ) + X) ^ m := by
  have hX : 0 ≤ X := (norm_nonneg c).trans hc
  have hD : ∀ j, ‖iteratedDeriv j (feldmanBasis h a b) z‖ ≤
      j.factorial * 2 ^ ((L + 2) * (N + h)) := by
    intro j
    have h1 := feldman_basis_deriv_bound_uniform h L a b j z N hah hbL hz
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)] at h1
    linarith
  calc ‖∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
        (iteratedDeriv j (feldmanBasis h a b) z * c ^ (m - j))‖
      ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          ((j.factorial * 2 ^ ((L + 2) * (N + h))) * X ^ (m - j)) := by
        refine norm_sum_le_of_le _ fun j _ => ?_
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
        gcongr
        exact hD j
    _ = 2 ^ ((L + 2) * (N + h)) *
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * j.factorial * X ^ (m - j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 2 ^ ((L + 2) * (N + h)) * ((m : ℝ) + X) ^ m := by
        gcongr
        exact auxiliary_sum_binom_fact_pow_le m X hX

/-- HOL Light: Baker/auxiliary.ml, BAKER_GAMMA_BOUND. `‖γ_r‖ ≤ L * (1 + ‖beta r‖)`. -/
theorem baker_gamma_bound (n : ℕ) (beta : ℕ → ℂ) (mu : ℕ → ℕ) (r L : ℕ)
    (hr : mu r ≤ L) (hn : mu n ≤ L) :
    ‖bakerGamma n beta mu r‖ ≤ L * (1 + ‖beta r‖) := by
  have h1 : (mu r : ℝ) ≤ L := by exact_mod_cast hr
  have h2 : (mu n : ℝ) ≤ L := by exact_mod_cast hn
  calc ‖bakerGamma n beta mu r‖ ≤ ‖(mu r : ℂ)‖ + ‖(mu n : ℂ) * beta r‖ := norm_add_le _ _
    _ = (mu r : ℝ) + (mu n : ℝ) * ‖beta r‖ := by
        rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    _ ≤ L + L * ‖beta r‖ := by gcongr
    _ = L * (1 + ‖beta r‖) := by ring

/-- HOL Light: Baker/auxiliary.ml, BAKER_OMEGA_SPLIT. The exponent of a term as the algebraic
exponent plus `mu n` times `beta 0 + ∑_{r<n} beta r * lg r - lg n`. -/
theorem baker_omega_split (n : ℕ) (beta lg : ℕ → ℂ) (mu : ℕ → ℕ) (hn : 1 ≤ n) :
    bakerOmega n beta lg mu =
      ∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r +
        (mu n : ℂ) * (beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : ∑ r ∈ Finset.Icc 1 k, ((mu r : ℂ) + (mu (k + 1) : ℂ) * beta r) * lg r =
      ∑ r ∈ Finset.Icc 1 k, (mu r : ℂ) * lg r +
        (mu (k + 1) : ℂ) * ∑ r ∈ Finset.Icc 1 k, beta r * lg r := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp only [bakerOmega, bakerGamma, Nat.add_sub_cancel]
  rw [h1, Finset.sum_Icc_succ_top (by omega)]
  ring

/-- HOL Light: Baker/auxiliary.ml, BAKER_OMEGA_BOUND_DELTA. The bound for the exponent of a
term. -/
theorem baker_omega_bound_delta (n : ℕ) (beta lg : ℕ → ℂ) (mu : ℕ → ℕ) (L : ℕ)
    (hmu : ∀ r ∈ Finset.Icc 1 n, mu r ≤ L) (hn : 1 ≤ n) :
    ‖bakerOmega n beta lg mu‖ ≤
      L * (∑ r ∈ Finset.Icc 1 n, ‖lg r‖ +
        ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖) := by
  rw [baker_omega_split n beta lg mu hn, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Finset.mul_sum]
    refine norm_sum_le_of_le _ fun r hr => ?_
    rw [norm_mul, Complex.norm_natCast]
    gcongr
    exact hmu r hr
  · rw [norm_mul, Complex.norm_natCast]
    gcongr
    exact hmu n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)

/-- HOL Light: Baker/auxiliary.ml, NORM_CEXP_LE. `‖exp z‖ ≤ exp ‖z‖`. -/
theorem norm_cexp_le (z : ℂ) : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ :=
  Complex.norm_exp_le_exp_norm z

/-- HOL Light: Baker/auxiliary.ml, BAKER_TERM_BOUND. The upper bound for one term of the
auxiliary function on the disc `‖z‖ + 1 ≤ N` (Baker, Lemma 5, first part). -/
theorem baker_term_bound (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (a b : ℕ) (mu : ℕ → ℕ) (z : ℂ) (N : ℕ) (P : ℝ)
    (hn : 1 ≤ n) (hah : a < h) (hbL : b ≤ L) (hmu : ∀ r ∈ Finset.Icc 1 n, mu r ≤ L)
    (hp : |(p (a, b, mu) : ℝ)| ≤ P) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerTerm n h p beta lg m (a, b, mu) z‖ ≤
      P * (2 ^ ((L + 2) * (N + h)) *
        (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) *
            Real.exp (N * (L * (∑ r ∈ Finset.Icc 1 n, ‖lg r‖ +
              ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖)))))) := by
  have hP : 0 ≤ P := (abs_nonneg _).trans hp
  have hmun : mu n ≤ L := hmu n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hmun' : (mu n : ℝ) ≤ L := by exact_mod_cast hmun
  have hzN : ‖z‖ ≤ N := by linarith
  have h1 := baker_dpart_bound h L a b (m 0) z N ((mu n : ℂ) * beta 0) (L * ‖beta 0‖) hah hbL hz
    (by rw [norm_mul, Complex.norm_natCast]; gcongr)
  have h2 : ∏ r ∈ Finset.Icc 1 (n - 1), ‖(bakerGamma n beta mu r * lg r) ^ m r‖ ≤
      ∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r := by
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r hr => ?_
    have hg := baker_gamma_bound n beta mu r L
      (hmu r (by have := Finset.mem_Icc.mp hr; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩)) hmun
    rw [norm_pow, norm_mul, ← mul_assoc]
    gcongr
  have h3 : ‖Complex.exp (z * bakerOmega n beta lg mu)‖ ≤
      Real.exp (N * (L * (∑ r ∈ Finset.Icc 1 n, ‖lg r‖ +
        ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖))) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    exact mul_le_mul hzN (baker_omega_bound_delta n beta lg mu L hmu hn) (norm_nonneg _)
      (Nat.cast_nonneg _)
  rw [baker_term_explicit, norm_mul, norm_mul, norm_mul, norm_prod, Complex.norm_intCast]
  calc |(p (a, b, mu) : ℝ)| * (‖∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
          (iteratedDeriv j (feldmanBasis h a b) z * ((mu n : ℂ) * beta 0) ^ (m 0 - j))‖ *
        ((∏ r ∈ Finset.Icc 1 (n - 1), ‖(bakerGamma n beta mu r * lg r) ^ m r‖) *
          ‖Complex.exp (z * bakerOmega n beta lg mu)‖))
      ≤ P * ((2 ^ ((L + 2) * (N + h)) * ((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0) *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) *
            Real.exp (N * (L * (∑ r ∈ Finset.Icc 1 n, ‖lg r‖ +
              ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖))))) := by
        gcongr
    _ = _ := by ring

private theorem auxiliary_sum_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ) (C : ℝ)
    (hf : ∀ x ∈ s, ‖f x‖ ≤ C) : ‖∑ x ∈ s, f x‖ ≤ s.card * C :=
  (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hf).trans_eq (nsmul_eq_mul _ _))

/-- HOL Light: Baker/auxiliary.ml, BAKER_AUX_BOUND. The upper bound for the auxiliary function on
the disc `‖z‖ + 1 ≤ N` (Baker, Lemma 5, first part). -/
theorem baker_aux_bound (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (z : ℂ) (N : ℕ) (P : ℝ)
    (hn : 1 ≤ n) (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAux n h L p beta lg m z‖ ≤
      ((bakerIndex h L n).card : ℝ) *
        (P * (2 ^ ((L + 2) * (N + h)) *
          (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
            ((∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) *
              Real.exp (N * (L * (∑ r ∈ Finset.Icc 1 n, ‖lg r‖ +
                ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖))))))) := by
  refine auxiliary_sum_bound _ _ _ fun x hx => ?_
  obtain ⟨a, b, mu⟩ := x
  obtain ⟨hah, hbL, hmu, -⟩ := mem_bakerIndex.mp hx
  exact baker_term_bound n h L p beta lg m a b mu z N P hn hah hbL hmu (hp _ hx) hz

/-! ### The algebraic counterpart -/

/-- HOL Light: Baker/auxiliary.ml, NORM_CEXP_SUB_1_LE. `‖exp z - 1‖ ≤ ‖z‖ * exp ‖z‖`. -/
theorem norm_cexp_sub_1_le (z : ℂ) : ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Complex.exp)
    (f' := Complex.exp) (s := Metric.closedBall (0 : ℂ) ‖z‖) (C := Real.exp ‖z‖) (x := 0) (y := z)
    (fun w _ => (Complex.hasDerivAt_exp w).hasDerivWithinAt)
    (fun w hw => (Complex.norm_exp_le_exp_norm w).trans
      (Real.exp_le_exp.mpr (by simpa using hw)))
    (convex_closedBall _ _) (by simp) (by simp)
  simpa [mul_comm] using h

/-- HOL Light: Baker/auxiliary.ml, BAKER_TERM_ALGTERM. A term of the auxiliary function is the
algebraic term times `∏ lg r ^ m r` and an exponential factor that is close to `1`. -/
theorem baker_term_algterm (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (a b : ℕ) (mu : ℕ → ℕ) (z : ℂ) (hn : 1 ≤ n) :
    bakerTerm n h p beta lg m (a, b, mu) z =
      (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) *
        (bakerAlgterm n h p beta lg m (a, b, mu) z *
          Complex.exp (z * ((mu n : ℂ) *
            (beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n)))) := by
  have hprod : ∏ r ∈ Finset.Icc 1 (n - 1), (bakerGamma n beta mu r * lg r) ^ m r =
      (∏ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta mu r ^ m r) *
        ∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun r _ => mul_pow _ _ _
  rw [baker_term_explicit, baker_omega_split n beta lg mu hn, hprod, mul_add z, Complex.exp_add]
  simp only [bakerAlgterm]
  ring

/-- HOL Light: Baker/auxiliary.ml, BAKER_ALGTERM_BOUND. The upper bound for one algebraic term on
the disc `‖z‖ + 1 ≤ N`. -/
theorem baker_algterm_bound (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (a b : ℕ) (mu : ℕ → ℕ) (z : ℂ) (N : ℕ) (P : ℝ)
    (hn : 1 ≤ n) (hah : a < h) (hbL : b ≤ L) (hmu : ∀ r ∈ Finset.Icc 1 n, mu r ≤ L)
    (hp : |(p (a, b, mu) : ℝ)| ≤ P) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAlgterm n h p beta lg m (a, b, mu) z‖ ≤
      P * (2 ^ ((L + 2) * (N + h)) *
        (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (L * (1 + ‖beta r‖)) ^ m r) *
            Real.exp (N * (L * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖))))) := by
  have hP : 0 ≤ P := (abs_nonneg _).trans hp
  have hmun : mu n ≤ L := hmu n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hmun' : (mu n : ℝ) ≤ L := by exact_mod_cast hmun
  have hzN : ‖z‖ ≤ N := by linarith
  have h1 := baker_dpart_bound h L a b (m 0) z N ((mu n : ℂ) * beta 0) (L * ‖beta 0‖) hah hbL hz
    (by rw [norm_mul, Complex.norm_natCast]; gcongr)
  have h2 : ∏ r ∈ Finset.Icc 1 (n - 1), ‖bakerGamma n beta mu r ^ m r‖ ≤
      ∏ r ∈ Finset.Icc 1 (n - 1), (L * (1 + ‖beta r‖)) ^ m r := by
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r hr => ?_
    have hg := baker_gamma_bound n beta mu r L
      (hmu r (by have := Finset.mem_Icc.mp hr; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩)) hmun
    rw [norm_pow]
    gcongr
  have h3 : ‖Complex.exp (z * ∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r)‖ ≤
      Real.exp (N * (L * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖)) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    refine mul_le_mul hzN ?_ (norm_nonneg _) (Nat.cast_nonneg _)
    rw [Finset.mul_sum]
    refine norm_sum_le_of_le _ fun r hr => ?_
    rw [norm_mul, Complex.norm_natCast]
    gcongr
    exact hmu r hr
  simp only [bakerAlgterm]
  rw [norm_mul, norm_mul, norm_mul, norm_prod, Complex.norm_intCast]
  calc |(p (a, b, mu) : ℝ)| * (‖∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
          (iteratedDeriv j (feldmanBasis h a b) z * ((mu n : ℂ) * beta 0) ^ (m 0 - j))‖ *
        ((∏ r ∈ Finset.Icc 1 (n - 1), ‖bakerGamma n beta mu r ^ m r‖) *
          ‖Complex.exp (z * ∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r)‖))
      ≤ P * ((2 ^ ((L + 2) * (N + h)) * ((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0) *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (L * (1 + ‖beta r‖)) ^ m r) *
            Real.exp (N * (L * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖)))) := by
        gcongr
    _ = _ := by ring

/-- HOL Light: Baker/auxiliary.ml, BAKER_AUX_ALG_APPROX. The auxiliary function differs from
`∏ lg r ^ m r` times its algebraic counterpart by a quantity bounded in terms of
`beta 0 + ∑_{r<n} beta r * lg r - lg n`. -/
theorem baker_aux_alg_approx (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (z : ℂ) (N : ℕ) (P : ℝ)
    (hn : 1 ≤ n) (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAux n h L p beta lg m z -
        (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlg n h L p beta lg m z‖ ≤
      ((bakerIndex h L n).card : ℝ) *
        ((P * (2 ^ ((L + 2) * (N + h)) *
          (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
            ((∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) *
              Real.exp (N * (L * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖)))))) *
          (N * (L * (‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ *
            Real.exp (N * (L *
              ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖)))))) := by
  simp only [bakerAux, bakerAlg]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine auxiliary_sum_bound _ _ _ fun x hx => ?_
  obtain ⟨a, b, mu⟩ := x
  obtain ⟨hah, hbL, hmu, -⟩ := mem_bakerIndex.mp hx
  have hmun : (mu n : ℝ) ≤ L := by
    exact_mod_cast hmu n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hzN : ‖z‖ ≤ N := by linarith
  have hP : 0 ≤ P := (abs_nonneg _).trans (hp _ hx)
  rw [baker_term_algterm n h p beta lg m a b mu z hn]
  generalize beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n = d
  have hA := baker_algterm_bound n h L p beta lg m a b mu z N P hn hah hbL hmu (hp _ hx) hz
  have hprod : ∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r =
      (∏ r ∈ Finset.Icc 1 (n - 1), (L * (1 + ‖beta r‖)) ^ m r) *
        ∏ r ∈ Finset.Icc 1 (n - 1), ‖lg r‖ ^ m r := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun r _ => by rw [← mul_pow, mul_assoc]
  have hw : ‖z * ((mu n : ℂ) * d)‖ ≤ N * (L * ‖d‖) := by
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    gcongr
  have hE : ‖Complex.exp (z * ((mu n : ℂ) * d)) - 1‖ ≤
      N * (L * (‖d‖ * Real.exp (N * (L * ‖d‖)))) :=
    calc ‖Complex.exp (z * ((mu n : ℂ) * d)) - 1‖
        ≤ ‖z * ((mu n : ℂ) * d)‖ * Real.exp ‖z * ((mu n : ℂ) * d)‖ := norm_cexp_sub_1_le _
      _ ≤ (N * (L * ‖d‖)) * Real.exp (N * (L * ‖d‖)) := by gcongr
      _ = N * (L * (‖d‖ * Real.exp (N * (L * ‖d‖)))) := by ring
  have hl : ‖∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r‖ =
      ∏ r ∈ Finset.Icc 1 (n - 1), ‖lg r‖ ^ m r := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun r _ => norm_pow _ _
  have hfac : (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) *
        (bakerAlgterm n h p beta lg m (a, b, mu) z * Complex.exp (z * ((mu n : ℂ) * d))) -
      (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlgterm n h p beta lg m (a, b, mu) z =
      ((∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlgterm n h p beta lg m (a, b, mu) z) *
        (Complex.exp (z * ((mu n : ℂ) * d)) - 1) := by ring
  rw [hfac, norm_mul, norm_mul, hl, hprod]
  refine mul_le_mul ?_ hE (norm_nonneg _) (by positivity)
  calc (∏ r ∈ Finset.Icc 1 (n - 1), ‖lg r‖ ^ m r) * ‖bakerAlgterm n h p beta lg m (a, b, mu) z‖
      ≤ (∏ r ∈ Finset.Icc 1 (n - 1), ‖lg r‖ ^ m r) *
          (P * (2 ^ ((L + 2) * (N + h)) *
            (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
              ((∏ r ∈ Finset.Icc 1 (n - 1), (L * (1 + ‖beta r‖)) ^ m r) *
                Real.exp (N * (L * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖)))))) := by
        gcongr
    _ = _ := by ring

end RiemannMasullo.Baker
