module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Auxiliary
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Siegel

/-! # Arithmetic of the auxiliary function: Baker Lemmas 4, 5 and 7

Ported from HOL Light, Baker/aux_arith.ml (jrh13/hol-light, commit 1a0c0e6).

The algebraic counterpart of the auxiliary function at an integer point `l`, multiplied by the
denominators `N ^ m 0 * g_n ^ |m|`, is an integer polynomial expression (`intpoly`) in the
algebraic numbers involved, with explicit bounds. The Siegel lemma then gives Lemma 4, and the
Liouville inequality gives the second parts of Lemma 5 and of Lemma 7.

Products of real and complex numbers are written as the HOL text reads, with Lean's
association (to the left), as in `CoreBounds.lean`. `CARD_BAKER_INDEX` of the HOL file is
`card_baker_index` in `Auxiliary.lean`. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### Rearranging the algebraic term -/

/-- HOL Light: Baker/aux_arith.ml, CEXP_LINEAR_COMBINATION_NUM. The exponential of a natural
multiple of a linear combination with natural coefficients is a product of powers. -/
theorem cexp_linear_combination_num (s : Finset ℕ) (lg : ℕ → ℂ) (mu : ℕ → ℕ) (l : ℕ) :
    Complex.exp ((l : ℂ) * ∑ r ∈ s, (mu r : ℂ) * lg r) =
      ∏ r ∈ s, Complex.exp (lg r) ^ (mu r * l) := by
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem auxArith_sum_range (n : ℕ) (m : ℕ → ℕ) :
    ∑ i ∈ Finset.range (n - 1 + 1), m i = m 0 + ∑ i ∈ Finset.Icc 1 (n - 1), m i := by
  have hI : Finset.Ico (0 + 1) (n - 1 + 1) = Finset.Icc 1 (n - 1) := by
    ext r
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hI]

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALGTERM_REARRANGE. The algebraic term at an integer
point, multiplied by `N ^ m 0 * gg n ^ |m|`, written with the numbers `gg j` that clear the
denominators of the `beta j`. -/
theorem baker_algterm_rearrange (n h : ℕ) (beta lg theta gg : ℕ → ℂ) (N l : ℕ) (m : ℕ → ℕ)
    (a b : ℕ) (mu : ℕ → ℕ) (hn : 1 ≤ n)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hbeta : ∀ j, j < n → beta j * gg n = -(gg j)) :
    (N : ℂ) ^ m 0 * gg n ^ (∑ i ∈ Finset.range (n - 1 + 1), m i) *
        bakerAlgterm n h (fun _ => 1) beta lg m (a, b, mu) (l : ℂ) =
      (∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) * (N : ℂ) ^ (m 0 - j) *
          (j.factorial : ℂ) *
          ((N : ℂ) ^ j * iteratedDeriv j (feldmanBasis h a b) (l : ℂ) / (j.factorial : ℂ)) *
          gg n ^ j * (-((mu n : ℂ) * gg 0)) ^ (m 0 - j)) *
        (∏ r ∈ Finset.Icc 1 (n - 1), ((mu r : ℂ) * gg n - (mu n : ℂ) * gg r) ^ m r) *
        ∏ r ∈ Finset.Icc 1 n, theta r ^ (mu r * l) := by
  have hexp : Complex.exp ((l : ℂ) * ∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r) =
      ∏ r ∈ Finset.Icc 1 n, theta r ^ (mu r * l) := by
    rw [cexp_linear_combination_num]
    exact Finset.prod_congr rfl fun r hr => by rw [htheta r hr]
  have hprod : gg n ^ (∑ i ∈ Finset.Icc 1 (n - 1), m i) *
      ∏ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta mu r ^ m r =
      ∏ r ∈ Finset.Icc 1 (n - 1), ((mu r : ℂ) * gg n - (mu n : ℂ) * gg r) ^ m r := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [← mul_pow]
    congr 1
    have := hbeta r (by have := Finset.mem_Icc.mp hr; omega)
    simp only [bakerGamma]
    linear_combination (mu n : ℂ) * this
  have hD : (N : ℂ) ^ m 0 * gg n ^ m 0 *
      ∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) *
        (iteratedDeriv j (feldmanBasis h a b) (l : ℂ) * ((mu n : ℂ) * beta 0) ^ (m 0 - j)) =
      ∑ j ∈ Finset.range (m 0 + 1), ((m 0).choose j : ℂ) * (N : ℂ) ^ (m 0 - j) *
          (j.factorial : ℂ) *
          ((N : ℂ) ^ j * iteratedDeriv j (feldmanBasis h a b) (l : ℂ) / (j.factorial : ℂ)) *
          gg n ^ j * (-((mu n : ℂ) * gg 0)) ^ (m 0 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ m 0 := by have := Finset.mem_range.mp hj; omega
    have hf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have h0 := hbeta 0 (by omega)
    have e1 : (N : ℂ) ^ m 0 = (N : ℂ) ^ (m 0 - j) * (N : ℂ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj']
    have e2 : gg n ^ m 0 = gg n ^ j * gg n ^ (m 0 - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj']
    have e3 : (-((mu n : ℂ) * gg 0)) ^ (m 0 - j) =
        ((mu n : ℂ) * beta 0) ^ (m 0 - j) * gg n ^ (m 0 - j) := by
      rw [← mul_pow]
      congr 1
      linear_combination -(mu n : ℂ) * h0
    rw [e1, e2, e3]
    field_simp
  simp only [bakerAlgterm, Int.cast_one, one_mul]
  rw [hexp, auxArith_sum_range, pow_add, ← hD, ← hprod]
  ring

/-! ### The factors as integer polynomial expressions -/

private theorem auxArith_sum_binom_fact_le (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (j.factorial : ℝ) ≤ ((m : ℝ) + 1) ^ m := by
  rw [add_pow]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hf : (j.factorial : ℝ) ≤ (m : ℝ) ^ j := by exact_mod_cast fact_le_pow j m hjm
  calc (m.choose j : ℝ) * j.factorial ≤ (m.choose j : ℝ) * (m : ℝ) ^ j := by gcongr
    _ = (m : ℝ) ^ j * 1 ^ (m - j) * (m.choose j : ℝ) := by rw [one_pow]; ring

/-- HOL Light: Baker/aux_arith.ml, BAKER_DSUM_INTPOLY. The Leibniz sum of the algebraic term,
with denominators cleared, is an `intpoly`. -/
theorem baker_dsum_intpoly (h L : ℕ) (g : ℕ → (ℕ → ℂ) → ℂ) (V : Finset ℕ) (e : ℕ → ℕ) (G : ℝ)
    (N l m0 a b nn mun : ℕ) (hL : 1 ≤ L) (hG : 1 ≤ G)
    (hgnn : intpoly V e G (g nn)) (hg0 : intpoly V e G (g 0))
    (hah : a < h) (hbL : b ≤ L) (hmun : mun ≤ L)
    (hdiv : ∀ i, 1 ≤ i → i ≤ h → (l + i) ∣ N) :
    intpoly V (fun r => m0 * e r)
      ((N : ℝ) ^ m0 * 2 ^ ((L + 2) * ((l + 1) + h)) * ((m0 : ℝ) + 1) ^ m0 *
        (2 * (L : ℝ) * G) ^ m0)
      (fun x => ∑ j ∈ Finset.range (m0 + 1), (m0.choose j : ℂ) * (N : ℂ) ^ (m0 - j) *
        (j.factorial : ℂ) *
        ((N : ℂ) ^ j * iteratedDeriv j (feldmanBasis h a b) (l : ℂ) / (j.factorial : ℂ)) *
        g nn x ^ j * (-((mun : ℂ) * g 0 x)) ^ (m0 - j)) := by
  have hG0 : 0 ≤ G := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hmun' : (mun : ℝ) ≤ L := by exact_mod_cast hmun
  have hGle : G ≤ 2 * (L : ℝ) * G := by nlinarith
  have hmG : (mun : ℝ) * G ≤ 2 * (L : ℝ) * G := by nlinarith
  have hmG0 : 0 ≤ (mun : ℝ) * G := by positivity
  have hex : ∀ j, ∃ kap : ℤ,
      (N : ℂ) ^ j * iteratedDeriv j (feldmanBasis h a b) (l : ℂ) / (j.factorial : ℂ) =
        (kap : ℂ) := by
    intro j
    obtain ⟨q, hq⟩ := feldman_basis_deriv_integer h a b l N hah.le hdiv j
    exact ⟨q, by rw [mul_div_assoc, hq]⟩
  choose kap hkap using hex
  have hkb : ∀ j, |(kap j : ℝ)| ≤ (N : ℝ) ^ j * 2 ^ ((L + 2) * ((l + 1) + h)) := by
    intro j
    have h1 := feldman_basis_deriv_bound_uniform h L a b j (l : ℂ) (l + 1) hah hbL (by simp)
    rw [← Complex.norm_intCast, ← hkap j, mul_div_assoc, norm_mul, norm_pow,
      Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hterm : ∀ j ∈ Finset.range (m0 + 1), intpoly V (fun r => m0 * e r)
      (|((m0.choose j * (N : ℤ) ^ (m0 - j) * j.factorial * kap j : ℤ) : ℝ)| *
        (G ^ j * ((mun : ℝ) * G) ^ (m0 - j)))
      (fun x => ((m0.choose j * (N : ℤ) ^ (m0 - j) * j.factorial * kap j : ℤ) : ℂ) *
        (g nn x ^ j * (-((mun : ℂ) * g 0 x)) ^ (m0 - j))) := by
    intro j hj
    have hj' : j ≤ m0 := by have := Finset.mem_range.mp hj; omega
    refine intpoly_cmul _ (intpoly_mono (intpoly_mul (intpoly_pow hgnn j)
      (intpoly_pow (intpoly_neg (intpoly_num_mul mun hg0)) (m0 - j))) (fun r _ => ?_) le_rfl)
    rw [← Nat.add_mul, Nat.add_sub_cancel' hj']
  have hsumI := intpoly_vsum (V := V) (n := fun r => m0 * e r) (t := Finset.range (m0 + 1))
    (b := fun j => |((m0.choose j * (N : ℤ) ^ (m0 - j) * j.factorial * kap j : ℤ) : ℝ)| *
      (G ^ j * ((mun : ℝ) * G) ^ (m0 - j)))
    (g := fun j x => ((m0.choose j * (N : ℤ) ^ (m0 - j) * j.factorial * kap j : ℤ) : ℂ) *
      (g nn x ^ j * (-((mun : ℂ) * g 0 x)) ^ (m0 - j))) hterm
  refine intpoly_eq (intpoly_mono hsumI (fun _ _ => le_rfl) ?_) ?_
  · calc ∑ j ∈ Finset.range (m0 + 1),
          |((m0.choose j * (N : ℤ) ^ (m0 - j) * j.factorial * kap j : ℤ) : ℝ)| *
            (G ^ j * ((mun : ℝ) * G) ^ (m0 - j))
        ≤ ∑ j ∈ Finset.range (m0 + 1), ((m0.choose j : ℝ) * (j.factorial : ℝ)) *
            ((N : ℝ) ^ m0 * 2 ^ ((L + 2) * ((l + 1) + h)) * (2 * (L : ℝ) * G) ^ m0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ m0 := by have := Finset.mem_range.mp hj; omega
          have e1 : (N : ℝ) ^ m0 = (N : ℝ) ^ (m0 - j) * (N : ℝ) ^ j := by
            rw [← pow_add, Nat.sub_add_cancel hj']
          have e2 : (2 * (L : ℝ) * G) ^ m0 =
              (2 * (L : ℝ) * G) ^ j * (2 * (L : ℝ) * G) ^ (m0 - j) := by
            rw [← pow_add, Nat.add_sub_cancel' hj']
          have e3 : |((m0.choose j * (N : ℤ) ^ (m0 - j) * j.factorial * kap j : ℤ) : ℝ)| =
              (m0.choose j : ℝ) * (N : ℝ) ^ (m0 - j) * (j.factorial : ℝ) * |(kap j : ℝ)| := by
            push_cast
            rw [abs_mul, abs_of_nonneg (by positivity)]
          have h1 : G ^ j ≤ (2 * (L : ℝ) * G) ^ j := pow_le_pow_left₀ hG0 hGle j
          have h2 : ((mun : ℝ) * G) ^ (m0 - j) ≤ (2 * (L : ℝ) * G) ^ (m0 - j) :=
            pow_le_pow_left₀ hmG0 hmG _
          rw [e1, e2, e3]
          calc (m0.choose j : ℝ) * (N : ℝ) ^ (m0 - j) * (j.factorial : ℝ) * |(kap j : ℝ)| *
                (G ^ j * ((mun : ℝ) * G) ^ (m0 - j))
              ≤ (m0.choose j : ℝ) * (N : ℝ) ^ (m0 - j) * (j.factorial : ℝ) *
                  ((N : ℝ) ^ j * 2 ^ ((L + 2) * ((l + 1) + h))) *
                  ((2 * (L : ℝ) * G) ^ j * (2 * (L : ℝ) * G) ^ (m0 - j)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hkb j) (by positivity))
                  (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
                  (by positivity)
            _ = _ := by ring
      _ = (∑ j ∈ Finset.range (m0 + 1), (m0.choose j : ℝ) * (j.factorial : ℝ)) *
            ((N : ℝ) ^ m0 * 2 ^ ((L + 2) * ((l + 1) + h)) * (2 * (L : ℝ) * G) ^ m0) := by
          rw [Finset.sum_mul]
      _ ≤ ((m0 : ℝ) + 1) ^ m0 *
            ((N : ℝ) ^ m0 * 2 ^ ((L + 2) * ((l + 1) + h)) * (2 * (L : ℝ) * G) ^ m0) :=
          mul_le_mul_of_nonneg_right (auxArith_sum_binom_fact_le m0) (by positivity)
      _ = _ := by ring
  · intro x
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hkap j]
    push_cast
    ring

/-- HOL Light: Baker/aux_arith.ml, BAKER_GAMMAPROD_INTPOLY. The product of the powers of the
`γ_r`, with denominators cleared, is an `intpoly`. -/
theorem baker_gammaprod_intpoly (L : ℕ) (g : ℕ → (ℕ → ℂ) → ℂ) (V : Finset ℕ) (e : ℕ → ℕ)
    (G : ℝ) (n : ℕ) (m mu : ℕ → ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) (hG : 1 ≤ G)
    (hg : ∀ j, j ≤ n → intpoly V e G (g j)) (hmu : ∀ r ∈ Finset.Icc 1 n, mu r ≤ L) :
    intpoly V (fun r => (∑ i ∈ Finset.Icc 1 (n - 1), m i) * e r)
      ((2 * (L : ℝ) * G) ^ (∑ i ∈ Finset.Icc 1 (n - 1), m i))
      (fun x => ∏ r ∈ Finset.Icc 1 (n - 1),
        ((mu r : ℂ) * g n x - (mu n : ℂ) * g r x) ^ m r) := by
  have hG0 : 0 ≤ G := by linarith
  have _hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hmun : (mu n : ℝ) ≤ L := by
    exact_mod_cast hmu n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hP := intpoly_cproduct (V := V) (t := Finset.Icc 1 (n - 1))
    (n := fun i r => m i * e r)
    (b := fun i => ((mu i : ℝ) * G + (mu n : ℝ) * G) ^ m i)
    (g := fun i x => ((mu i : ℂ) * g n x - (mu n : ℂ) * g i x) ^ m i)
    (fun i hi => intpoly_pow (intpoly_sub (intpoly_num_mul (mu i) (hg n le_rfl))
      (intpoly_num_mul (mu n) (hg i (by have := Finset.mem_Icc.mp hi; omega)))) (m i))
  refine intpoly_mono hP (fun r _ => le_of_eq (Finset.sum_mul _ _ _).symm) ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
  have hmui : (mu i : ℝ) ≤ L := by
    exact_mod_cast hmu i (by
      have := Finset.mem_Icc.mp hi
      exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have h1 : (mu i : ℝ) * G ≤ L * G := mul_le_mul_of_nonneg_right hmui hG0
  have h2 : (mu n : ℝ) * G ≤ L * G := mul_le_mul_of_nonneg_right hmun hG0
  linarith

/-! ### `N ^ m 0 * g_n ^ |m|` times the algebraic term is an `intpoly` in `theta` -/

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALGTERM_INTPOLY. The algebraic term at an integer point
`l`, multiplied by `N ^ m 0 * g_n ^ |m|`, is the value at `theta` of an `intpoly` of controlled
degrees and size. -/
theorem baker_algterm_intpoly (n h L : ℕ) (beta lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (N l : ℕ) (m : ℕ → ℕ) (a b : ℕ) (mu : ℕ → ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hG : 1 ≤ G) (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (hdiv : ∀ i, 1 ≤ i → i ≤ h → (l + i) ∣ N)
    (hx : (a, b, mu) ∈ bakerIndex h L n) :
    ∃ psi : (ℕ → ℂ) → ℂ,
      intpoly V (fun r => (if r ∈ Finset.Icc 1 n then L * l else 0) +
          (∑ i ∈ Finset.range (n - 1 + 1), m i) * e r)
        ((N : ℝ) ^ m 0 * 2 ^ ((L + 2) * ((l + 1) + h)) * ((m 0 : ℝ) + 1) ^ m 0 *
          (2 * (L : ℝ) * G) ^ (∑ i ∈ Finset.range (n - 1 + 1), m i)) psi ∧
      psi theta = (N : ℂ) ^ m 0 * g n theta ^ (∑ i ∈ Finset.range (n - 1 + 1), m i) *
        bakerAlgterm n h (fun _ => 1) beta lg m (a, b, mu) (l : ℂ) := by
  obtain ⟨hah, hbL, hmu, -⟩ := mem_bakerIndex.mp hx
  have hmun := hmu n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have h1 := baker_dsum_intpoly h L g V e G N l (m 0) a b n (mu n) hL hG (hg n le_rfl)
    (hg 0 (Nat.zero_le _)) hah hbL hmun hdiv
  have h2 := baker_gammaprod_intpoly L g V e G n m mu hn hL hG hg hmu
  have h3 := intpoly_monomial (V := V) (s := Finset.Icc 1 n) (fun r => mu r * l) hV
  refine ⟨_, intpoly_mono (intpoly_mul (intpoly_mul h1 h2) h3) (fun r _ => ?_) ?_, ?_⟩
  · rw [auxArith_sum_range, Nat.add_mul]
    split_ifs with hr
    · have := Nat.mul_le_mul_right l (hmu r hr)
      omega
    · omega
  · rw [auxArith_sum_range, pow_add]
    apply le_of_eq
    ring
  · exact (baker_algterm_rearrange n h beta lg theta (fun j => g j theta) N l m a b mu hn htheta
      hbeta).symm

/-! ### Baker Lemma 4, arithmetic part -/

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALGTERM_LINEAR. The algebraic term is linear in the
coefficient `p x`. -/
theorem baker_algterm_linear (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (x : ℕ × ℕ × (ℕ → ℕ)) (z : ℂ) :
    bakerAlgterm n h p beta lg m x z =
      ((p x : ℤ) : ℂ) * bakerAlgterm n h (fun _ => 1) beta lg m x z := by
  simp only [bakerAlgterm, Int.cast_one, one_mul]

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALGTERM_RESTRICT. The algebraic term depends only on
`m 0, …, m (n - 1)`.

Deviation: HOL's `RESTRICTION (0..n-1) m` is `fun i => if i ∈ Finset.range (n - 1 + 1) then m i
else 0`. HOL's hypothesis `1 ≤ n` is not needed with the range written like this. -/
theorem baker_algterm_restrict (n h : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (x : ℕ × ℕ × (ℕ → ℕ)) (z : ℂ) :
    bakerAlgterm n h p beta lg (fun i => if i ∈ Finset.range (n - 1 + 1) then m i else 0) x z =
      bakerAlgterm n h p beta lg m x z := by
  have h0 : (0 : ℕ) ∈ Finset.range (n - 1 + 1) := Finset.mem_range.mpr (by omega)
  have hprod : ∏ r ∈ Finset.Icc 1 (n - 1),
        bakerGamma n beta x.2.2 r ^ (if r ∈ Finset.range (n - 1 + 1) then m r else 0) =
      ∏ r ∈ Finset.Icc 1 (n - 1), bakerGamma n beta x.2.2 r ^ m r :=
    Finset.prod_congr rfl fun r hr => by
      rw [ite_eq_left (Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hr; omega))]
  simp only [bakerAlgterm, ite_eq_left h0, hprod]

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALG_RESTRICT. The algebraic counterpart depends only on
`m 0, …, m (n - 1)`.

Deviation: as for `baker_algterm_restrict`. -/
theorem baker_alg_restrict (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (z : ℂ) :
    bakerAlg n h L p beta lg (fun i => if i ∈ Finset.range (n - 1 + 1) then m i else 0) z =
      bakerAlg n h L p beta lg m z := by
  simp only [bakerAlg, baker_algterm_restrict]

/-- HOL Light: Baker/aux_arith.ml, NSUM_RESTRICTION. The sum over `s` of the restriction of `m`
to `s` is the sum of `m`.

Deviation: HOL's `RESTRICTION s m` is `fun i => if i ∈ s then m i else 0`. -/
theorem nsum_restriction (s : Finset ℕ) (m : ℕ → ℕ) :
    ∑ i ∈ s, (if i ∈ s then m i else 0) = ∑ i ∈ s, m i :=
  Finset.sum_congr rfl fun i hi => by rw [ite_eq_left hi]

/-- HOL Light: Baker/aux_arith.ml, BAKER_LEMMA4_ARITH. Baker's Lemma 4, arithmetic part: there
are integers `p x`, not all zero and of controlled size, such that the algebraic counterpart of
the auxiliary function vanishes at `l = 1, …, h` for all `m` with `|m| ≤ k`.

Deviation: the witness `p` and the coefficients `a r j` are integer-valued (HOL: reals with
`integer`), so the conjunct `integer (p x)` disappears. -/
theorem baker_lemma4_arith (n h L k : ℕ) (beta lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (N : ℕ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ)
    (H : ℕ → ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hh : 1 ≤ h) (hG : 1 ≤ G) (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hgn : g n theta ≠ 0)
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hN : N ≠ 0) (hdiv : ∀ i, 1 ≤ i → i ≤ 2 * h → i ∣ N)
    (hcount : 2 * (∏ r ∈ V, d r) * (k + 1) ^ n ≤ (L + 1) * (L + 1) ^ n) :
    ∃ p : ℕ × ℕ × (ℕ → ℕ) → ℤ,
      (∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ ((bakerIndex h L n).card : ℝ) *
        max 1 (((N : ℝ) ^ k * 2 ^ ((L + 2) * ((h + 1) + h)) * ((k : ℝ) + 1) ^ k *
            (2 * (L : ℝ) * G) ^ k) *
          ∏ r ∈ V, (2 * H r) ^ ((if r ∈ Finset.Icc 1 n then L * h else 0) + k * e r))) ∧
      ¬ (∀ x ∈ bakerIndex h L n, p x = 0) ∧
      ∀ (l : ℕ) (m : ℕ → ℕ), 1 ≤ l → l ≤ h → ∑ i ∈ Finset.range (n - 1 + 1), m i ≤ k →
        bakerAlg n h L p beta lg m (l : ℂ) = 0 := by
  classical
  obtain ⟨Mset, hMset⟩ : ∃ Mset : Finset (ℕ → ℕ), Mset =
      (cartesianProduct (Finset.range (n - 1 + 1)) fun _ => Finset.range (k + 1)).filter
        fun m => ∑ i ∈ Finset.range (n - 1 + 1), m i ≤ k := ⟨_, rfl⟩
  have hMcard : Mset.card ≤ (k + 1) ^ n := by
    rw [hMset]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [card_cartesian_product]
    simp [Nat.sub_add_cancel hn]
  obtain ⟨eqs, heqs⟩ : ∃ eqs : Finset (ℕ × (ℕ → ℕ)), eqs = Finset.Icc 1 h ×ˢ Mset := ⟨_, rfl⟩
  have hecard : eqs.card ≤ h * (k + 1) ^ n := by
    rw [heqs, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.mul_le_mul_left h hMcard
  obtain ⟨nexp, hnexp⟩ : ∃ nexp : ℕ → ℕ, nexp =
      fun r => (if r ∈ Finset.Icc 1 n then L * h else 0) + k * e r := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (N : ℝ) ^ k * 2 ^ ((L + 2) * ((h + 1) + h)) *
      ((k : ℝ) + 1) ^ k * (2 * (L : ℝ) * G) ^ k := ⟨_, rfl⟩
  have hex : ∀ (i : ℕ × (ℕ → ℕ)) (x : ℕ × ℕ × (ℕ → ℕ)), ∃ psi : (ℕ → ℂ) → ℂ,
      i ∈ eqs → x ∈ bakerIndex h L n →
        intpoly V nexp B psi ∧
        psi theta = (N : ℂ) ^ i.2 0 * g n theta ^ (∑ j ∈ Finset.range (n - 1 + 1), i.2 j) *
          bakerAlgterm n h (fun _ => 1) beta lg i.2 x (i.1 : ℂ) := by
    rintro ⟨l, m⟩ ⟨a', b', mu⟩
    by_cases hc : (l, m) ∈ eqs ∧ (a', b', mu) ∈ bakerIndex h L n
    · obtain ⟨hi, hx⟩ := hc
      rw [heqs] at hi
      obtain ⟨hl, hm⟩ := Finset.mem_product.mp hi
      obtain ⟨hl1, hlh⟩ := Finset.mem_Icc.mp hl
      rw [hMset] at hm
      have hmk : ∑ i ∈ Finset.range (n - 1 + 1), m i ≤ k := (Finset.mem_filter.mp hm).2
      obtain ⟨psi, hpsi1, hpsi2⟩ := baker_algterm_intpoly n h L beta lg theta V g e G N l m
        a' b' mu hn hL hG hV htheta hg hbeta
        (fun i hi1 hih => hdiv (l + i) (by omega) (by omega)) hx
      refine ⟨psi, fun _ _ => ⟨intpoly_mono hpsi1 (fun r _ => ?_) ?_, hpsi2⟩⟩
      · rw [hnexp]
        change (if r ∈ Finset.Icc 1 n then L * l else 0) +
            (∑ i ∈ Finset.range (n - 1 + 1), m i) * e r ≤
          (if r ∈ Finset.Icc 1 n then L * h else 0) + k * e r
        have h1 : L * l ≤ L * h := Nat.mul_le_mul_left L hlh
        have h2 := Nat.mul_le_mul_right (e r) hmk
        split_ifs <;> omega
      · have hm0 : m 0 ≤ k :=
          (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))).trans hmk
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
        have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
        have hLG : (1 : ℝ) ≤ 2 * (L : ℝ) * G := by nlinarith
        have hm0' : (m 0 : ℝ) ≤ k := by exact_mod_cast hm0
        have hm00 : (0 : ℝ) ≤ m 0 := Nat.cast_nonneg _
        have i1 : (N : ℝ) ^ m 0 ≤ (N : ℝ) ^ k := pow_le_pow_right₀ hN1 hm0
        have i2 : (2 : ℝ) ^ ((L + 2) * ((l + 1) + h)) ≤ 2 ^ ((L + 2) * ((h + 1) + h)) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (by omega))
        have i3 : ((m 0 : ℝ) + 1) ^ m 0 ≤ ((k : ℝ) + 1) ^ k :=
          (pow_le_pow_right₀ (by linarith) hm0).trans
            (pow_le_pow_left₀ (by linarith) (by linarith) k)
        have i4 : (2 * (L : ℝ) * G) ^ (∑ i ∈ Finset.range (n - 1 + 1), m i) ≤
            (2 * (L : ℝ) * G) ^ k := pow_le_pow_right₀ hLG hmk
        rw [hB]
        exact mul_le_mul (mul_le_mul (mul_le_mul i1 i2 (by positivity) (by positivity)) i3
          (by positivity) (by positivity)) i4 (by positivity) (by positivity)
    · exact ⟨fun _ => 0, fun hi hx => absurd ⟨hi, hx⟩ hc⟩
  choose psi hpsi using hex
  have hunk : bakerIndex h L n ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨(0, 0, fun _ => 0),
      mem_bakerIndex.mpr ⟨by omega, Nat.zero_le _, fun _ _ => Nat.zero_le _, fun _ _ => rfl⟩⟩
  have hcard : 2 * ((∏ r ∈ V, d r) * eqs.card) ≤ (bakerIndex h L n).card := by
    rw [card_baker_index]
    calc 2 * ((∏ r ∈ V, d r) * eqs.card)
        ≤ 2 * ((∏ r ∈ V, d r) * (h * (k + 1) ^ n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hecard)
      _ = h * (2 * (∏ r ∈ V, d r) * (k + 1) ^ n) := by ring
      _ ≤ h * ((L + 1) * (L + 1) ^ n) := Nat.mul_le_mul_left h hcount
  obtain ⟨p, hp1, hp2, hp3⟩ := algebraic_siegel (V := V) (n := nexp) (b := B)
    (fun i x => psi i x) eqs (bakerIndex h L n) theta a d H hunk ha
    (fun i hi x hx => (hpsi i x hi hx).1) hcard
  refine ⟨p, ?_, hp2, fun l m hl1 hlh hmk => ?_⟩
  · subst hB hnexp
    exact hp1
  rw [← baker_alg_restrict n h L p beta lg m (l : ℂ)]
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ → ℕ, m' =
      fun i => if i ∈ Finset.range (n - 1 + 1) then m i else 0 := ⟨_, rfl⟩
  rw [← hm']
  have hsm : ∑ i ∈ Finset.range (n - 1 + 1), m' i = ∑ i ∈ Finset.range (n - 1 + 1), m i := by
    rw [hm']
    exact nsum_restriction _ m
  have hmem : (l, m') ∈ eqs := by
    rw [heqs, hMset, hm']
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hl1, hlh⟩, Finset.mem_filter.mpr
      ⟨restriction_mem_cartesianProduct fun i hi => Finset.mem_range.mpr ?_, ?_⟩⟩
    · exact Nat.lt_succ_of_le ((Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
        hi).trans hmk)
    · rw [← hm']
      exact hsm.le.trans hmk
  have key := hp3 (l, m') hmem
  have hsum : ∑ x ∈ bakerIndex h L n, ((p x : ℤ) : ℂ) * psi (l, m') x theta =
      ((N : ℂ) ^ m' 0 * g n theta ^ (∑ j ∈ Finset.range (n - 1 + 1), m' j)) *
        bakerAlg n h L p beta lg m' (l : ℂ) := by
    simp only [bakerAlg]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(hpsi (l, m') x hmem hx).2, baker_algterm_linear n h p]
    ring
  rw [hsum] at key
  exact (mul_eq_zero.mp key).resolve_left
    (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN)) (pow_ne_zero _ hgn))

/-! ### Baker Lemma 5, arithmetic part -/

private theorem auxArith_sum_intpoly {J : Type*} (idx : Finset J) (V : Finset ℕ) (nexp : ℕ → ℕ)
    (B : ℝ) (theta : ℕ → ℂ) (p : J → ℤ) (P : ℝ) (c : ℂ) (f : J → ℂ) (hB0 : 0 ≤ B)
    (hp : ∀ x ∈ idx, |(p x : ℝ)| ≤ P)
    (hex : ∀ x ∈ idx, ∃ psi : (ℕ → ℂ) → ℂ, intpoly V nexp B psi ∧ psi theta = c * f x) :
    ∃ psi : (ℕ → ℂ) → ℂ, intpoly V nexp ((idx.card : ℝ) * P * B) psi ∧
      psi theta = c * ∑ x ∈ idx, (p x : ℂ) * f x := by
  classical
  have hex' : ∀ x, ∃ psi : (ℕ → ℂ) → ℂ, x ∈ idx → intpoly V nexp B psi ∧ psi theta = c * f x := by
    intro x
    by_cases hx : x ∈ idx
    · obtain ⟨psi, hpsi⟩ := hex x hx
      exact ⟨psi, fun _ => hpsi⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx⟩
  choose psi hpsi using hex'
  refine ⟨fun x => ∑ y ∈ idx, (p y : ℂ) * psi y x,
    intpoly_mono (intpoly_vsum (b := fun y => |(p y : ℝ)| * B)
      (g := fun y x => (p y : ℂ) * psi y x) fun y hy => intpoly_cmul (p y) (hpsi y hy).1)
      (fun _ _ => le_rfl) ?_, ?_⟩
  · calc ∑ y ∈ idx, |(p y : ℝ)| * B ≤ ∑ _y ∈ idx, P * B :=
          Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hp y hy) hB0
      _ = (idx.card : ℝ) * P * B := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · change ∑ y ∈ idx, (p y : ℂ) * psi y theta = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(hpsi y hy).2]
    ring

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALG_INTPOLY. The algebraic counterpart at an integer
point `l`, multiplied by `N ^ m 0 * g_n ^ |m|`, is the value at `theta` of an `intpoly` of
controlled degrees and size.

Deviation: `p` is integer-valued, so the conjunct `integer (p x)` disappears. -/
theorem baker_alg_intpoly (n h L : ℕ) (beta lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (N l : ℕ) (m : ℕ → ℕ)
    (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (P : ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hG : 1 ≤ G) (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (hdiv : ∀ i, 1 ≤ i → i ≤ h → (l + i) ∣ N)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P) :
    ∃ psi : (ℕ → ℂ) → ℂ,
      intpoly V (fun r => (if r ∈ Finset.Icc 1 n then L * l else 0) +
          (∑ i ∈ Finset.range (n - 1 + 1), m i) * e r)
        (((bakerIndex h L n).card : ℝ) * P *
          ((N : ℝ) ^ m 0 * 2 ^ ((L + 2) * ((l + 1) + h)) * ((m 0 : ℝ) + 1) ^ m 0 *
            (2 * (L : ℝ) * G) ^ (∑ i ∈ Finset.range (n - 1 + 1), m i))) psi ∧
      psi theta = (N : ℂ) ^ m 0 * g n theta ^ (∑ i ∈ Finset.range (n - 1 + 1), m i) *
        bakerAlg n h L p beta lg m (l : ℂ) := by
  have hG0 : 0 ≤ G := by linarith
  have hsum : bakerAlg n h L p beta lg m (l : ℂ) = ∑ x ∈ bakerIndex h L n,
      ((p x : ℤ) : ℂ) * bakerAlgterm n h (fun _ => 1) beta lg m x (l : ℂ) := by
    simp only [bakerAlg]
    exact Finset.sum_congr rfl fun x _ => baker_algterm_linear n h p beta lg m x _
  rw [hsum]
  exact auxArith_sum_intpoly (bakerIndex h L n) V _ _ theta p P _
    (fun x => bakerAlgterm n h (fun _ => 1) beta lg m x (l : ℂ)) (by positivity) hp
    fun x hx => baker_algterm_intpoly n h L beta lg theta V g e G N l m x.1 x.2.1 x.2.2 hn hL hG
      hV htheta hg hbeta hdiv hx

/-- HOL Light: Baker/aux_arith.ml, BAKER_LEMMA5_ARITH. Baker's Lemma 5, arithmetic part: a
nonzero value of the algebraic counterpart of the auxiliary function at an integer point is
bounded below (Liouville inequality).

Deviation: `p` and the coefficients `a r j` are integer-valued (HOL: reals with `integer`), so
the conjuncts `integer (p x)` and `integer (a r j)` disappear. -/
theorem baker_lemma5_arith (n h L : ℕ) (beta lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (N l : ℕ) (m : ℕ → ℕ)
    (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (P : ℝ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hG : 1 ≤ G) (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (hdiv : ∀ i, 1 ≤ i → i ≤ h → (l + i) ∣ N)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (ha : ∀ r ∈ V, (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hN : N ≠ 0) (hgn : g n theta ≠ 0)
    (hne : bakerAlg n h L p beta lg m (l : ℂ) ≠ 0) :
    (((∏ r ∈ V, d r).factorial : ℝ) *
        max 1 (((bakerIndex h L n).card : ℝ) * P *
            ((N : ℝ) ^ m 0 * 2 ^ ((L + 2) * ((l + 1) + h)) * ((m 0 : ℝ) + 1) ^ m 0 *
              (2 * (L : ℝ) * G) ^ (∑ i ∈ Finset.range (n - 1 + 1), m i)) *
          (∏ r ∈ V, H r ^ ((if r ∈ Finset.Icc 1 n then L * l else 0) +
            (∑ i ∈ Finset.range (n - 1 + 1), m i) * e r)) *
          ∏ r ∈ V, (H r * (1 + (d r : ℝ) * H r)) ^
            ((if r ∈ Finset.Icc 1 n then L * l else 0) +
              (∑ i ∈ Finset.range (n - 1 + 1), m i) * e r)) ^ ((∏ r ∈ V, d r) - 1) *
        ∏ r ∈ V, H r ^ ((if r ∈ Finset.Icc 1 n then L * l else 0) +
          (∑ i ∈ Finset.range (n - 1 + 1), m i) * e r))⁻¹ ≤
      ‖(N : ℂ) ^ m 0 * g n theta ^ (∑ i ∈ Finset.range (n - 1 + 1), m i) *
        bakerAlg n h L p beta lg m (l : ℂ)‖ := by
  obtain ⟨psi, hpsi1, hpsi2⟩ := baker_alg_intpoly n h L beta lg theta V g e G N l m p P hn hL hG
    hV htheta hg hbeta hdiv hp
  have hne' : psi theta ≠ 0 := by
    rw [hpsi2]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN))
      (pow_ne_zero _ hgn)) hne
  have key := intpoly_liouville theta a d H hpsi1 ha hne'
  rw [hpsi2] at key
  simp only [mul_assoc] at key ⊢
  exact key

/-! ### Baker Lemma 7, arithmetic part -/

/-- HOL Light: Baker/aux_arith.ml, VSUM_POLY_POW_SUBST. Substituting `w ^ k` into a polynomial:
the polynomial `∑ a i * X ^ (k * i)` has the coefficient `a (j / k)` at `X ^ j` when `k ∣ j`,
and `0` otherwise.

Deviation: integer coefficients `a i` (HOL: reals). -/
theorem vsum_poly_pow_subst (a : ℕ → ℤ) (d k : ℕ) (w : ℂ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k * d + 1), ((if k ∣ j then a (j / k) else 0 : ℤ) : ℂ) * w ^ j =
      ∑ i ∈ Finset.range (d + 1), (a i : ℂ) * (w ^ k) ^ i := by
  have hk0 : 0 < k := hk
  have hsub : (Finset.range (d + 1)).image (fun i => k * i) ⊆ Finset.range (k * d + 1) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.mul_le_mul_left k (by omega)))
  rw [← Finset.sum_subset hsub,
    Finset.sum_image fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hk0 hxy]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ hk0, pow_mul]
  · intro j hj hnj
    have hkj : ¬ k ∣ j := by
      rintro ⟨i, rfl⟩
      refine hnj (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr ?_, rfl⟩)
      have h1 := Finset.mem_range.mp hj
      have h2 : i ≤ d := Nat.le_of_mul_le_mul_left (by omega) hk0
      omega
    rw [ite_eq_right hkj]
    simp

/-- HOL Light: Baker/aux_arith.ml, BAKER_ALG_ZERO. The algebraic counterpart of the auxiliary
function for `m = 0`.

Deviation: HOL sums `\(a,b,mu). ...` over the index set; here the summand is a function of `x`
with `a = x.1`, `b = x.2.1`, `mu = x.2.2`, as in `bakerAlgterm`. -/
theorem baker_alg_zero (n h L : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ) (z : ℂ) :
    bakerAlg n h L p beta lg (fun _ => 0) z =
      ∑ x ∈ bakerIndex h L n, ((p x : ℤ) : ℂ) * feldmanBasis h x.1 x.2.1 z *
        Complex.exp (z * ∑ r ∈ Finset.Icc 1 n, (x.2.2 r : ℂ) * lg r) := by
  simp only [bakerAlg, bakerAlgterm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_assoc]

/-- HOL Light: Baker/aux_arith.ml, CEXP_LINEAR_COMBINATION_RATIONAL. The exponential of a
rational multiple `l / k` of a linear combination with natural coefficients is a product of
powers of the numbers `exp (lg r / k)`. -/
theorem cexp_linear_combination_rational (s : Finset ℕ) (lg : ℕ → ℂ) (mu : ℕ → ℕ) (l k : ℕ)
    (hk : 1 ≤ k) :
    Complex.exp ((l : ℂ) / (k : ℂ) * ∑ r ∈ s, (mu r : ℂ) * lg r) =
      ∏ r ∈ s, Complex.exp (lg r / (k : ℂ)) ^ (mu r * l) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- HOL Light: Baker/aux_arith.ml, CEXP_DIV_POW. `exp (z / k) ^ k = exp z` for `k ≥ 1`. -/
theorem cexp_div_pow (z : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    Complex.exp (z / (k : ℂ)) ^ k = Complex.exp z := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem auxArith_feldman_delta_bound (k : ℕ) (z : ℂ) (n : ℕ) (hz : ‖z‖ ≤ n) :
    ‖feldmanDelta k z‖ ≤ 2 ^ (n + k) := by
  have h1 : ‖feldmanDelta k z‖ ≤ ‖feldmanDelta k (n : ℂ)‖ := by
    simp only [feldmanDelta, norm_div, norm_prod]
    refine div_le_div_of_nonneg_right
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_) (norm_nonneg _)
    calc ‖z + (j : ℂ)‖ ≤ ‖z‖ + ‖(j : ℂ)‖ := norm_add_le _ _
      _ ≤ (n : ℝ) + (j : ℝ) := by rw [Complex.norm_natCast]; linarith
      _ = ‖(n : ℂ) + (j : ℂ)‖ := by
          rw [show (n : ℂ) + (j : ℂ) = ((n + j : ℕ) : ℂ) by push_cast; rfl,
            Complex.norm_natCast, Nat.cast_add]
  rw [feldman_delta_num, Complex.norm_natCast] at h1
  exact h1.trans (by exact_mod_cast binom_le_exp (n + k) k)

/-- HOL Light: Baker/delta.ml, FELDMAN_BASIS_BOUND. -/
private theorem auxArith_feldman_basis_bound (h a b : ℕ) (z : ℂ) (n : ℕ) (hz : ‖z‖ ≤ n) :
    ‖feldmanBasis h a b z‖ ≤ 2 ^ ((n + a) + (b + 1) * (n + h)) := by
  rw [feldmanBasis, norm_mul, norm_pow, pow_add (2 : ℝ) (n + a), pow_mul' (2 : ℝ)]
  gcongr <;> exact auxArith_feldman_delta_bound _ _ _ hz

/-- HOL Light: Baker/aux_arith.ml, BAKER_LEMMA7_ARITH. Baker's Lemma 7, arithmetic part: a
nonzero value of the algebraic counterpart with `m = 0` at a rational point `l / k` is bounded
below (Liouville inequality for the numbers `exp (lg r / k)`, roots of `a_r (X ^ k)`).

Deviation: `p` and the coefficients `a r j` are integer-valued (HOL: reals with `integer`), so
the conjuncts `integer (p x)` and `integer (a r j)` disappear. The hypotheses `1 ≤ n`, `1 ≤ h`
and `1 ≤ d r` are HOL's and are not used. -/
theorem baker_lemma7_arith (n h L : ℕ) (beta lg : ℕ → ℂ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (P : ℝ)
    (k l X : ℕ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (_hn : 1 ≤ n) (_hh : 1 ≤ h) (hk : 1 ≤ k) (hl : l ≤ k * X)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (ha : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0)
    (hne : bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ)) ≠ 0) :
    (((∏ r ∈ Finset.Icc 1 n, k * d r).factorial : ℝ) *
        max 1 (((bakerIndex h L n).card : ℝ) *
            (P * (k : ℝ) ^ (2 * h * (L + 2)) * 2 ^ ((L + 2) * (X + h))) *
          (∏ r ∈ Finset.Icc 1 n, H r ^ (L * l)) *
          ∏ r ∈ Finset.Icc 1 n, (H r * (1 + ((k * d r : ℕ) : ℝ) * H r)) ^ (L * l)) ^
          ((∏ r ∈ Finset.Icc 1 n, k * d r) - 1) *
        ∏ r ∈ Finset.Icc 1 n, H r ^ (L * l))⁻¹ ≤
      ‖(k : ℂ) ^ (2 * h * (L + 2)) *
        bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = 2 * h * (L + 2) := ⟨_, rfl⟩
  rw [← hE]
  have hex : ∀ x : ℕ × ℕ × (ℕ → ℕ), ∃ c : ℤ, x ∈ bakerIndex h L n →
      |(c : ℝ)| ≤ (k : ℝ) ^ E * 2 ^ ((L + 2) * (X + h)) ∧
      (c : ℂ) = (k : ℂ) ^ E * feldmanBasis h x.1 x.2.1 ((l : ℂ) / (k : ℂ)) := by
    rintro ⟨a', b', mu⟩
    by_cases hx : (a', b', mu) ∈ bakerIndex h L n
    · obtain ⟨hah, hbL, -, -⟩ := mem_bakerIndex.mp hx
      have hle : 2 * a' + 2 * h * (b' + 1) ≤ E := by
        have := Nat.mul_le_mul_left h (show b' + 1 ≤ L + 1 by omega)
        rw [hE]
        nlinarith
      obtain ⟨c0, hc0⟩ := feldman_basis_rational h a' b' k l hk0
      have hc : (((k : ℤ) ^ (E - (2 * a' + 2 * h * (b' + 1))) * c0 : ℤ) : ℂ) =
          (k : ℂ) ^ E * feldmanBasis h a' b' ((l : ℂ) / (k : ℂ)) := by
        push_cast
        rw [← hc0, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      refine ⟨_, fun _ => ⟨?_, hc⟩⟩
      rw [← Complex.norm_intCast, hc, norm_mul, norm_pow, Complex.norm_natCast]
      have hz : ‖(l : ℂ) / (k : ℂ)‖ ≤ X := by
        rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ hkR]
        exact_mod_cast (by rw [Nat.mul_comm]; exact hl : l ≤ X * k)
      have hfb := auxArith_feldman_basis_bound h a' b' _ X hz
      have hexp : (X + a') + (b' + 1) * (X + h) ≤ (L + 2) * (X + h) := by
        have := Nat.mul_le_mul_right (X + h) (show b' + 1 ≤ L + 1 by omega)
        nlinarith
      exact mul_le_mul_of_nonneg_left (hfb.trans (pow_le_pow_right₀ (by norm_num) hexp))
        (by positivity)
    · exact ⟨0, fun h => absurd h hx⟩
  choose c hc using hex
  obtain ⟨psi, hpsidef⟩ : ∃ psi : (ℕ → ℂ) → ℂ, ∀ x, psi x =
      ∑ y ∈ bakerIndex h L n, ((p y * c y : ℤ) : ℂ) *
        ∏ r ∈ Finset.Icc 1 n, x r ^ (y.2.2 r * l) := ⟨_, fun _ => rfl⟩
  have hpsi1 : intpoly (Finset.Icc 1 n) (fun _ => L * l)
      (((bakerIndex h L n).card : ℝ) * (P * (k : ℝ) ^ E * 2 ^ ((L + 2) * (X + h)))) psi := by
    refine intpoly_eq (intpoly_mono (intpoly_vsum (n := fun _ => L * l)
      (b := fun y => |((p y * c y : ℤ) : ℝ)| * 1)
      (g := fun y x => ((p y * c y : ℤ) : ℂ) * ∏ r ∈ Finset.Icc 1 n, x r ^ (y.2.2 r * l))
      fun y hy => intpoly_cmul _ (intpoly_mono (intpoly_monomial (V := Finset.Icc 1 n)
        (s := Finset.Icc 1 n) (fun r => y.2.2 r * l) subset_rfl) (fun r hr => ?_) le_rfl))
      (fun _ _ => le_rfl) ?_) hpsidef
    · have := (mem_bakerIndex.mp (show (y.1, y.2.1, y.2.2) ∈ bakerIndex h L n from hy)).2.2.1 r hr
      change (if r ∈ Finset.Icc 1 n then y.2.2 r * l else 0) ≤ L * l
      rw [ite_eq_left hr]
      exact Nat.mul_le_mul_right l this
    · calc ∑ y ∈ bakerIndex h L n, |((p y * c y : ℤ) : ℝ)| * 1
          ≤ ∑ _y ∈ bakerIndex h L n, P * ((k : ℝ) ^ E * 2 ^ ((L + 2) * (X + h))) := by
            refine Finset.sum_le_sum fun y hy => ?_
            rw [mul_one, Int.cast_mul, abs_mul]
            exact mul_le_mul (hp y hy) (hc y hy).1 (abs_nonneg _)
              ((abs_nonneg _).trans (hp y hy))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hpsi2 : psi (fun r => Complex.exp (lg r / (k : ℂ))) =
      (k : ℂ) ^ E * bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ)) := by
    rw [hpsidef, baker_alg_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [cexp_linear_combination_rational _ _ _ _ _ hk]
    push_cast
    rw [(hc y hy).2]
    ring
  have ha' : ∀ r ∈ Finset.Icc 1 n,
      (∀ j, |((if k ∣ j then a r (j / k) else 0 : ℤ) : ℝ)| ≤ H r) ∧
      (if k ∣ k * d r then a r (k * d r / k) else 0) ≠ 0 ∧
      ∑ j ∈ Finset.range (k * d r + 1), ((if k ∣ j then a r (j / k) else 0 : ℤ) : ℂ) *
        Complex.exp (lg r / (k : ℂ)) ^ j = 0 := by
    intro r hr
    obtain ⟨-, h1, h2, h3⟩ := ha r hr
    refine ⟨fun j => ?_, ?_, ?_⟩
    · split_ifs
      · exact h1 _
      · simpa using (abs_nonneg _).trans (h1 0)
    · rw [ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by omega)]
      exact h2
    · rw [vsum_poly_pow_subst (a r) (d r) k _ hk, cexp_div_pow _ k hk]
      exact h3
  have hne' : psi (fun r => Complex.exp (lg r / (k : ℂ))) ≠ 0 := by
    rw [hpsi2]
    exact mul_ne_zero (pow_ne_zero _ hkC) hne
  have key := intpoly_liouville (fun r => Complex.exp (lg r / (k : ℂ)))
    (fun r j => if k ∣ j then a r (j / k) else 0) (fun r => k * d r) H hpsi1 ha' hne'
  rw [hpsi2] at key
  simp only [mul_assoc] at key ⊢
  exact key

end RiemannMasullo.Baker
