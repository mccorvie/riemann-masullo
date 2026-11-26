module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.CoreBounds
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.IntPoly
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.AuxArith
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Extrap
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Bounds
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Sec4
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Delta

/-! # The parametric core of the Baker method

Ported from HOL Light, Baker/parametric_core.ml (jrh13/hol-light, commit 1a0c0e6): Lemmas 4–7
and section 4 of Baker, *Transcendental Number Theory*, Ch. 3, assembled into one parametric
contradiction. The bound functions are in `CoreBounds.lean`. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- The number of indices of the auxiliary function is at least `1`. -/
private theorem parametricCore_card_ge_one (h L n : ℕ) (hh : 1 ≤ h) :
    (1 : ℝ) ≤ ((bakerIndex h L n).card : ℝ) := by
  rw [card_baker_index]
  exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos hh (by positivity))

/-- `baker_aux_exp_bound` with the bound written as `bakerUb`. -/
private theorem parametricCore_aux_ub (n h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (z : ℂ) (N : ℕ) (P Bb Lam : ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hBb : 1 ≤ Bb) (hLam : 1 ≤ Lam) (hP : 0 ≤ P)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (hbeta : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hlg : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsum : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hlin : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ 1)
    (hm : ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAux n h L p beta lg m z‖ ≤ bakerUb n h L k P Bb Lam N := by
  have := baker_aux_exp_bound n h L k p beta lg m z N P Bb Lam hn hL hLk hBb hLam hP hp hbeta
    hlg hsum hlin hm hz
  simpa only [bakerUb, mul_assoc, add_assoc] using this

/-- `baker_approx_exp_bound` with the bound written as `bakerErr`. -/
private theorem parametricCore_aux_err (n h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ)
    (beta lg : ℕ → ℂ) (m : ℕ → ℕ) (z : ℂ) (N : ℕ) (P Bb Lam d0 : ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hBb : 1 ≤ Bb) (hLam : 1 ≤ Lam) (hP : 0 ≤ P)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (hbeta : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hlg : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsum : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam) (hd0 : 0 ≤ d0)
    (hlin : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ d0)
    (hm : ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAux n h L p beta lg m z -
        (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlg n h L p beta lg m z‖ ≤
      bakerErr n h L k P Bb Lam d0 N := by
  have := baker_approx_exp_bound n h L k p beta lg m z N P Bb Lam d0 hn hL hLk hBb hLam hP hp
    hbeta hlg hsum hd0 hlin hm hz
  simpa only [bakerErr, mul_assoc, add_assoc] using this

/-- HOL Light: Baker/parametric_core.ml, CPRODUCT_LG_POW_LOWER. A product of powers of the
logarithms, with exponents of sum at most `k`, has norm at least `lmin ^ k`. -/
theorem cproduct_lg_pow_lower (n : ℕ) (lg : ℕ → ℂ) (m : ℕ → ℕ) (k : ℕ) (lmin : ℝ)
    (_hn : 1 ≤ n) (hlmin : 0 < lmin) (hlmin1 : lmin ≤ 1)
    (hlg : ∀ r ∈ Finset.Icc 1 n, lmin ≤ ‖lg r‖)
    (hm : ∑ i ∈ Finset.range (n - 1 + 1), m i ≤ k) :
    lmin ^ k ≤ ‖∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r‖ := by
  rw [norm_prod]
  simp only [norm_pow]
  have hsub : ∑ r ∈ Finset.Icc 1 (n - 1), m r ≤ k := by
    refine le_trans (Finset.sum_le_sum_of_subset ?_) hm
    intro r hr
    simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
    omega
  calc lmin ^ k ≤ lmin ^ (∑ r ∈ Finset.Icc 1 (n - 1), m r) :=
        pow_le_pow_of_le_one hlmin.le hlmin1 hsub
    _ = ∏ r ∈ Finset.Icc 1 (n - 1), lmin ^ m r := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun r _ => pow_nonneg hlmin.le _) (fun r hr => by
        refine pow_le_pow_left₀ hlmin.le (hlg r ?_) _
        simp only [Finset.mem_Icc] at hr ⊢
        omega)

/-- HOL Light: Baker/parametric_core.ml, NORM_LOWER_FROM_APPROX. A lower bound for `‖u‖` and an
upper bound for `‖f - u‖` give a lower bound for `‖f‖`. -/
theorem norm_lower_from_approx (A er : ℝ) (f u : ℂ) (hA : A ≤ ‖u‖) (hf : ‖f - u‖ ≤ er) :
    A - er ≤ ‖f‖ := by
  have := norm_sub_norm_le u f
  rw [norm_sub_rev] at this
  linarith

/-- HOL Light: Baker/parametric_core.ml, BAKER_DICHOTOMY. Lemma 5 as a dichotomy: at an integer
point `l ≤ Rm` the auxiliary function is either at most `bakerErr` (its algebraic counterpart
vanishes) or at least `bakerVb` (Liouville applied to the nonzero algebraic counterpart).

Deviation: `V` is a `Finset ℕ` (HOL: `FINITE V`), and `a`, `p` are integer-valued (HOL: real
with `integer`), as in the files this one uses. -/
theorem baker_dichotomy (n : ℕ) (lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (beta : ℕ → ℂ) (h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (P Bb Lam d0 lmin Gn : ℝ)
    (Rm l : ℕ) (m : ℕ → ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hh : 1 ≤ h) (hG : 1 ≤ G)
    (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hgn : g n theta ≠ 0) (hGn : ‖g n theta‖ ≤ Gn) (hGn1 : 1 ≤ Gn)
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (hP : 1 ≤ P)
    (hBb : 1 ≤ Bb) (hbetaB : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hLam : 1 ≤ Lam) (hlgLam : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsumLam : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hlmin : 0 < lmin) (hlmin1 : lmin ≤ 1) (hlglmin : ∀ r ∈ Finset.Icc 1 n, lmin ≤ ‖lg r‖)
    (hd0 : 0 ≤ d0)
    (hdelta : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ d0)
    (hlRm : l ≤ Rm) (hm : ∑ i ∈ Finset.range (n - 1 + 1), m i ≤ k) :
    ‖bakerAux n h L p beta lg m (l : ℂ)‖ ≤ bakerErr n h L k P Bb Lam d0 (Rm + 1) ∨
      bakerVb n h L k V G H e d P Bb Lam d0 lmin Gn Rm ≤ ‖bakerAux n h L p beta lg m (l : ℂ)‖ := by
  have hP0 : 0 ≤ P := by linarith
  have hG0 : 0 ≤ G := by linarith
  have approx := parametricCore_aux_err n h L k p beta lg m (l : ℂ) (Rm + 1) P Bb Lam d0 hn hL hLk
    hBb hLam hP0 hp hbetaB hlgLam hsumLam hd0 hdelta hm
    (by rw [Complex.norm_natCast]; exact_mod_cast Nat.succ_le_succ hlRm)
  by_cases halg : bakerAlg n h L p beta lg m (l : ℂ) = 0
  · left
    rwa [halg, mul_zero, sub_zero] at approx
  right
  obtain ⟨Nl, hNl0, hNldiv, hNlle⟩ := shifted_common_multiple_bound l h hh
  have hNl1 : (1 : ℝ) ≤ Nl := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hNl0
  have hNlmax : (Nl : ℝ) ≤ bakerNmax h Rm := by
    refine hNlle.trans ?_
    unfold bakerNmax
    have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
    have hlR : (l : ℝ) ≤ Rm := by exact_mod_cast hlRm
    rw [mul_div_assoc]
    gcongr
  have hnmax0 : 0 ≤ bakerNmax h Rm := by linarith
  have l5 := baker_lemma5_arith n h L beta lg theta V g e G Nl l m p P a d H hn hL hG hV htheta
    hg hbeta hNldiv hp (fun r hr => ⟨(ha r hr).2.2.1, (ha r hr).2.2.2.1, (ha r hr).2.2.2.2⟩)
    hNl0 hgn halg
  have hm0s : m 0 ≤ ∑ i ∈ Finset.range (n - 1 + 1), m i :=
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.succ_pos _))
  have hcp := cproduct_lg_pow_lower n lg m k lmin hn hlmin hlmin1 hlglmin hm
  obtain ⟨s, hs⟩ : ∃ s, s = ∑ i ∈ Finset.range (n - 1 + 1), m i := ⟨_, rfl⟩
  rw [← hs] at l5 hm hm0s
  have hm0k : m 0 ≤ k := hm0s.trans hm
  obtain ⟨b5, hb5def⟩ : ∃ b5 : ℝ, b5 = ((bakerIndex h L n).card : ℝ) * P *
      ((Nl : ℝ) ^ m 0 * 2 ^ ((L + 2) * ((l + 1) + h)) * ((m 0 : ℝ) + 1) ^ m 0 *
        (2 * (L : ℝ) * G) ^ s) := ⟨_, rfl⟩
  rw [← hb5def] at l5
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2LG : 1 ≤ 2 * (L : ℝ) * G := by nlinarith
  have hcard1 := parametricCore_card_ge_one h L n hh
  have hb5 : 1 ≤ b5 := by
    rw [hb5def]
    refine real_le_1_mul _ _ (real_le_1_mul _ _ hcard1 hP) (real_le_1_mul _ _ (real_le_1_mul _ _
      (real_le_1_mul _ _ (one_le_pow₀ hNl1) (one_le_pow₀ (by norm_num))) (one_le_pow₀ ?_))
      (one_le_pow₀ h2LG))
    linarith [(Nat.cast_nonneg (m 0) : (0 : ℝ) ≤ m 0)]
  have h1 : (Nl : ℝ) ^ m 0 ≤ bakerNmax h Rm ^ k :=
    (pow_le_pow_right₀ hNl1 hm0k).trans (pow_le_pow_left₀ (by linarith) hNlmax k)
  have h2 : (2 : ℝ) ^ ((L + 2) * ((l + 1) + h)) ≤ 2 ^ ((L + 2) * ((Rm + 1) + h)) :=
    pow_le_pow_right₀ (by norm_num) (by gcongr)
  have h3 : ((m 0 : ℝ) + 1) ^ m 0 ≤ ((k : ℝ) + 1) ^ k := by
    have hm0k' : (m 0 : ℝ) ≤ k := by exact_mod_cast hm0k
    have hm00 : (0 : ℝ) ≤ m 0 := Nat.cast_nonneg _
    exact (pow_le_pow_right₀ (by linarith) hm0k).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) k)
  have h4 : (2 * (L : ℝ) * G) ^ s ≤ (2 * (L : ℝ) * G) ^ k := pow_le_pow_right₀ h2LG hm
  have hbb' : b5 ≤ ((bakerIndex h L n).card : ℝ) * P *
      (bakerNmax h Rm ^ k * 2 ^ ((L + 2) * ((Rm + 1) + h)) * ((k : ℝ) + 1) ^ k *
        (2 * (L : ℝ) * G) ^ k) := by
    rw [hb5def]
    have hm00 : (0 : ℝ) ≤ m 0 := Nat.cast_nonneg _
    gcongr
  have lel := liouville_exp_lower V d H
    (fun r => (if r ∈ Finset.Icc 1 n then L * l else 0) + s * e r) b5
    (fun r hr => ⟨(ha r hr).1, (ha r hr).2.1⟩) hb5
  have mono := liouville_exp_lower_mono V d H H
    (fun r => (if r ∈ Finset.Icc 1 n then L * l else 0) + s * e r)
    (fun r => (if r ∈ Finset.Icc 1 n then L * Rm else 0) + k * e r) b5 _
    (fun r hr => (ha r hr).1) hb5 hbb' (fun r hr => ⟨by
      refine Nat.add_le_add ?_ (Nat.mul_le_mul_right _ hm)
      split_ifs
      · exact Nat.mul_le_mul_left _ hlRm
      · exact le_rfl, (ha r hr).2.1, le_rfl⟩)
  have hliou : bakerLiou5 n h L k V G H e d P Rm ≤
      ‖(Nl : ℂ) ^ m 0 * g n theta ^ s * bakerAlg n h L p beta lg m (l : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (mono.trans (lel.trans (le_trans (le_of_eq ?_) l5)))
    · simp only [bakerLiou5, add_assoc]
    · simp only [mul_assoc]
  have hGn0 : 0 ≤ Gn := by linarith
  have hg2 : ‖g n theta‖ ^ s ≤ Gn ^ k :=
    (pow_le_pow_left₀ (norm_nonneg _) hGn s).trans (pow_le_pow_right₀ hGn1 hm)
  have hnb : ‖(Nl : ℂ) ^ m 0 * g n theta ^ s * bakerAlg n h L p beta lg m (l : ℂ)‖ ≤
      (bakerNmax h Rm ^ k * Gn ^ k) * ‖bakerAlg n h L p beta lg m (l : ℂ)‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul h1 hg2 (pow_nonneg (norm_nonneg _) _) (pow_nonneg hnmax0 _)) (norm_nonneg _)
  have hpos : 0 < bakerNmax h Rm ^ k * Gn ^ k :=
    mul_pos (pow_pos (by linarith) k) (pow_pos (by linarith) k)
  have hdiv : bakerLiou5 n h L k V G H e d P Rm / (bakerNmax h Rm ^ k * Gn ^ k) ≤
      ‖bakerAlg n h L p beta lg m (l : ℂ)‖ := by
    rw [div_le_iff₀ hpos, mul_comm]
    exact hliou.trans hnb
  have hliou0 : 0 ≤ bakerLiou5 n h L k V G H e d P Rm := by
    unfold bakerLiou5
    exact (Real.exp_pos _).le
  have hprod : lmin ^ k * (bakerLiou5 n h L k V G H e d P Rm /
        (bakerNmax h Rm ^ k * Gn ^ k)) ≤
      ‖(∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlg n h L p beta lg m (l : ℂ)‖ := by
    rw [norm_mul]
    exact mul_le_mul hcp hdiv (div_nonneg hliou0 hpos.le) (norm_nonneg _)
  rw [bakerVb, mul_div_assoc]
  exact norm_lower_from_approx _ _ _ _ hprod approx

/-- HOL Light: Baker/parametric_core.ml, BAKER_CORE_PARAMETRIC. The parametric contradiction of
the Baker method: data and parameters satisfying the numeric inequalities stated with the bound
functions cannot exist. -/
theorem baker_core_parametric (n : ℕ) (lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (beta : ℕ → ℂ) (h L k : ℕ) (R S rho : ℕ → ℕ) (J X7 rhoX : ℕ)
    (eps Bb Lam d0 lmin Gn : ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hh : 1 ≤ h) (hG : 1 ≤ G)
    (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hgn : g n theta ≠ 0) (hGn : ‖g n theta‖ ≤ Gn) (hGn1 : 1 ≤ Gn)
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hind : ∀ b : ℕ → ℤ, (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ L) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0)
    (hBb : 1 ≤ Bb) (hbetaB : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hLam : 1 ≤ Lam) (hlgLam : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsumLam : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hlmin : 0 < lmin) (hlmin1 : lmin ≤ 1) (hlglmin : ∀ r ∈ Finset.Icc 1 n, lmin ≤ ‖lg r‖)
    (hd0 : 0 ≤ d0) (hd01 : d0 ≤ 1)
    (hdelta : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ d0)
    (hcount : 2 * (∏ r ∈ V, d r) * (k + 1) ^ n ≤ (L + 1) * (L + 1) ^ n)
    (herr0 : bakerErr n h L k (bakerPbound n h L k V G H e) Bb Lam d0 (h + 1) ≤ eps)
    (hR0 : R 0 = h) (hS0 : S 0 = k)
    (hRmono : ∀ K, K < J → R K ≤ R (K + 1))
    (hShalf : ∀ K, K < J → 2 * S (K + 1) ≤ S K)
    (hrho : ∀ K, K < J → 4 * R (K + 1) ≤ rho K)
    (herr : ∀ K, K < J →
      bakerErr n h L k (bakerPbound n h L k V G H e) Bb Lam d0 (R (K + 1) + 1) ≤ eps)
    (hvbpos : ∀ K, K < J →
      0 < bakerVb n h L k V G H e d (bakerPbound n h L k V G H e) Bb Lam d0 lmin Gn (R (K + 1)))
    (hstep : ∀ K, K < J →
      2 * bakerUb n h L k (bakerPbound n h L k V G H e) Bb Lam (rho K + 1) *
          (4 * (R (K + 1) : ℝ) / (rho K : ℝ)) ^ (R K * (S (K + 1) + 1)) +
        eps * 2 * (R K : ℝ) * 2 ^ S (K + 1) * Real.exp n *
          ((R (K + 1) : ℝ) * 16 ^ R (K + 1)) ^ (S (K + 1) + 1) ≤
        bakerVb n h L k V G H e d (bakerPbound n h L k V G H e) Bb Lam d0 lmin Gn (R (K + 1)) / 2)
    (hX7 : h * (L + 2) * (L + 1) ^ n ≤ k * X7) (hX7R : X7 ≤ R J) (hrhoX : 4 * R J ≤ rhoX)
    (hlem7 : (k : ℝ) ^ (2 * h * (L + 2)) *
        (2 * bakerUb n h L k (bakerPbound n h L k V G H e) Bb Lam (rhoX + 1) *
            (4 * (R J : ℝ) / (rhoX : ℝ)) ^ (R J * (S J + 1)) +
          eps * 2 * (k : ℝ) * (R J : ℝ) * (2 * (k : ℝ)) ^ S J * Real.exp n *
            ((R J : ℝ) * 16 ^ R J) ^ (S J + 1) +
          bakerErr n h L k (bakerPbound n h L k V G H e) Bb Lam d0 (X7 + 1)) <
        bakerLiou7 n h L k d H (bakerPbound n h L k V G H e) X7 (h * (L + 2) * (L + 1) ^ n))
    (hLLam : (L : ℝ) * Lam < 2 * Real.pi * (k : ℝ)) : False := by
  have hG0 : 0 ≤ G := by linarith
  have hk1 : 1 ≤ k := hL.trans hLk
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hcard1 := parametricCore_card_ge_one h L n hh
  set P := bakerPbound n h L k V G H e with hPdef
  obtain ⟨N, hN0, hNdiv, hNle⟩ := numseg_common_multiple (2 * h)
  have hNle' : (N : ℝ) ≤ Real.exp (36 * (h : ℝ)) := by
    refine hNle.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  obtain ⟨p, hpb, hpne, hpvan⟩ := baker_lemma4_arith n h L k beta lg theta V g e G N a d H hn hL
    hh hG hV htheta hg hgn hbeta
    (fun r hr => ⟨(ha r hr).1, (ha r hr).2.2.1, (ha r hr).2.2.2.1, (ha r hr).2.2.2.2⟩)
    hN0 hNdiv hcount
  have hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P := by
    intro x hx
    refine (hpb x hx).trans ?_
    rw [hPdef, bakerPbound]
    refine mul_le_mul_of_nonneg_left
      (max_le_max le_rfl (mul_le_mul_of_nonneg_right ?_ ?_)) (Nat.cast_nonneg _)
    · gcongr
    · exact Finset.prod_nonneg fun r hr => pow_nonneg (by linarith [(ha r hr).2.1]) _
  have hP1 : 1 ≤ P := by
    rw [hPdef, bakerPbound]
    exact real_le_1_mul _ _ hcard1 (le_max_left _ _)
  have hP0 : 0 ≤ P := by linarith
  have hf : ∀ m, Differentiable ℂ (bakerAux n h L p beta lg m) := fun m =>
    differentiableOn_univ.1 (baker_aux_holomorphic n h L p beta lg m Set.univ hn)
  have hD := fun m => baker_aux_derivative n h L p beta lg m hn
  have ub : ∀ (m : ℕ → ℕ) (z : ℂ) (N : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k →
      ‖z‖ + 1 ≤ N → ‖bakerAux n h L p beta lg m z‖ ≤ bakerUb n h L k P Bb Lam N :=
    fun m z N hm hz => parametricCore_aux_ub n h L k p beta lg m z N P Bb Lam hn hL hLk hBb hLam
      hP0 hp hbetaB hlgLam hsumLam (hdelta.trans hd01) hm hz
  have err : ∀ (m : ℕ → ℕ) (z : ℂ) (N : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k →
      ‖z‖ + 1 ≤ N → ‖bakerAux n h L p beta lg m z -
        (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlg n h L p beta lg m z‖ ≤
      bakerErr n h L k P Bb Lam d0 N :=
    fun m z N hm hz => parametricCore_aux_err n h L k p beta lg m z N P Bb Lam d0 hn hL hLk hBb
      hLam hP0 hp hbetaB hlgLam hsumLam hd0 hdelta hm hz
  have h0 : ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S 0 → 1 ≤ l →
      l ≤ R 0 → ‖bakerAux n h L p beta lg m (l : ℂ)‖ ≤ eps := by
    intro m l hm hl1 hlR
    rw [hS0] at hm
    rw [hR0] at hlR
    have := err m (l : ℂ) (h + 1) hm
      (by rw [Complex.norm_natCast]; exact_mod_cast Nat.succ_le_succ hlR)
    rw [hpvan l m hl1 hlR hm, mul_zero, sub_zero] at this
    exact this.trans herr0
  have hSR : ∀ K, K ≤ J → S K ≤ k ∧ h ≤ R K := by
    intro K
    induction K with
    | zero => intro _; exact ⟨hS0.le, hR0.ge⟩
    | succ K ih =>
      intro hK
      have hK' : K < J := hK
      obtain ⟨h1, h2⟩ := ih hK'.le
      have := hShalf K hK'
      have := hRmono K hK'
      constructor <;> omega
  have hJ : ∀ (m : ℕ → ℕ) (l : ℕ), ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ S J → 1 ≤ l →
      l ≤ R J → ‖bakerAux n h L p beta lg m (l : ℂ)‖ ≤ eps := by
    refine extrapolation_induction (fun m => bakerAux n h L p beta lg m) n R S
      (fun K => (rho K : ℝ)) (fun K => bakerUb n h L k P Bb Lam (rho K + 1))
      (fun K => bakerVb n h L k V G H e d P Bb Lam d0 lmin Gn (R (K + 1)) / 2) eps J hn hf hD
      (hR0 ▸ hh) (fun K hK => ⟨hRmono K hK, hShalf K hK, by exact_mod_cast hrho K hK, ?_, ?_,
        hstep K hK⟩) h0
    · intro m z hm hz
      refine ub m z (rho K + 1) (hm.trans (hSR (K + 1) hK).1) ?_
      rw [hz]
      push_cast
      exact le_rfl
    · intro m l hm _ hl
      have hvb := hvbpos K hK
      rcases baker_dichotomy n lg theta V g e G a d H beta h L k p P Bb Lam d0 lmin Gn (R (K + 1))
        l m hn hL hLk hh hG hV htheta hg hgn hGn hGn1 hbeta ha hp hP1 hBb hbetaB hLam hlgLam
        hsumLam hlmin hlmin1 hlglmin hd0 hdelta hl (hm.trans (hSR (K + 1) hK).1) with h1 | h1
      · exact Or.inl (h1.trans (herr K hK))
      · exact Or.inr (by linarith)
  obtain ⟨hSJ, hRJ⟩ := hSR J le_rfl
  have halg : ∀ l : ℕ, l < h * (L + 2) * (L + 1) ^ n →
      bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ)) = 0 := by
    intro l hl
    by_contra hne
    have hlX7 : l ≤ k * X7 := hl.le.trans hX7
    have hlRJ : l ≤ k * R J := hlX7.trans (Nat.mul_le_mul_left k hX7R)
    have hrat := rational_extrapolation_all (fun m => bakerAux n h L p beta lg m) n (R J) (S J)
      k l (rhoX : ℝ) (bakerUb n h L k P Bb Lam (rhoX + 1)) eps hn hf hD (hh.trans hRJ) hk1 hlRJ
      (by exact_mod_cast hrhoX)
      (fun z hz => ub (fun _ => 0) z (rhoX + 1) (by simp)
        (by rw [hz]; push_cast; exact le_rfl))
      hJ
    have l7 := baker_lemma7_arith n h L beta lg p P k l X7 a d H hn hh hk1 hlX7 hp
      (fun r hr => by
        have := ha r (hV hr)
        rw [htheta r hr] at this
        exact ⟨this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩) hne
    have hb7 : 1 ≤ ((bakerIndex h L n).card : ℝ) *
        (P * (k : ℝ) ^ (2 * h * (L + 2)) * 2 ^ ((L + 2) * (X7 + h))) :=
      real_le_1_mul _ _ hcard1 (real_le_1_mul _ _ (real_le_1_mul _ _ hP1 (one_le_pow₀ hk1R))
        (one_le_pow₀ (by norm_num)))
    have lel7 := liouville_exp_lower (Finset.Icc 1 n) (fun r => k * d r) H (fun _ => L * l) _
      (fun r hr => ⟨Nat.succ_le_of_lt (Nat.mul_pos hk1 (ha r (hV hr)).1), (ha r (hV hr)).2.1⟩)
      hb7
    have mono7 := liouville_exp_lower_mono (Finset.Icc 1 n) (fun r => k * d r) H H
      (fun _ => L * l) (fun _ => L * (h * (L + 2) * (L + 1) ^ n)) _ _
      (fun r hr => Nat.succ_le_of_lt (Nat.mul_pos hk1 (ha r (hV hr)).1)) hb7 le_rfl
      (fun r hr => ⟨Nat.mul_le_mul_left L hl.le, (ha r (hV hr)).2.1, le_rfl⟩)
    have hliou : bakerLiou7 n h L k d H P X7 (h * (L + 2) * (L + 1) ^ n) ≤
        ‖(k : ℂ) ^ (2 * h * (L + 2)) *
          bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ := by
      refine le_trans (le_of_eq ?_) (mono7.trans (lel7.trans (le_trans (le_of_eq ?_) l7)))
      · simp only [bakerLiou7, add_assoc]
      · simp only [mul_assoc]
    have err7 := err (fun _ => 0) ((l : ℂ) / (k : ℂ)) (X7 + 1) (by simp) (by
      rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
      push_cast
      have hk0 : (0 : ℝ) < k := by linarith
      have : (l : ℝ) ≤ X7 * k := by rw [mul_comm]; exact_mod_cast hlX7
      linarith [(div_le_iff₀ hk0).2 this])
    simp only [pow_zero, Finset.prod_const_one, one_mul] at err7
    have htri := norm_sub_norm_le (bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ)))
      (bakerAux n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ)))
    rw [norm_sub_rev] at htri
    have halg_le := (show ‖bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ ≤
        ‖bakerAux n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ +
          ‖bakerAux n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ)) -
            bakerAlg n h L p beta lg (fun _ => 0) ((l : ℂ) / (k : ℂ))‖ by linarith).trans
      (add_le_add hrat err7)
    have hmul := mul_le_mul_of_nonneg_left halg_le
      (pow_nonneg (Nat.cast_nonneg k) (2 * h * (L + 2)) : (0 : ℝ) ≤ (k : ℝ) ^ (2 * h * (L + 2)))
    rw [norm_mul, norm_pow, Complex.norm_natCast] at hliou
    exact lt_irrefl _ (hlem7.trans_le (hliou.trans hmul))
  obtain ⟨b, hb, hbne, hbsum⟩ := baker_integer_relation n h L k p lg hn hh hk1 hpne
    (fun l hl => by
      have := halg l hl
      rw [baker_alg_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_assoc]
      congr 3
      ring)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsumLam (Nat.cast_nonneg L)) hLLam)
  exact hbne fun r hr => by exact_mod_cast hind b hb hbsum r hr

end RiemannMasullo.Baker
