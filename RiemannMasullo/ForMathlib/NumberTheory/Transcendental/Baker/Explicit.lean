module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Heights
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.NumericDmax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The core lower bound: explicit and existential versions

Ported from HOL Light, Baker/explicit.ml (jrh13/hol-light, commit 1a0c0e6).

The core lower bound of Baker, Transcendental Number Theory, Ch. 3, Thm 3.1, for fixed data:
`Complex.exp (lg r)` are roots of integer polynomials (degrees `d r`, heights `H r`), there are `m`
extra variables of degree at most `Dx` and height at most `B`, and the coefficients `g 0, ..., g n`
are integer polynomials (`intpoly`) of degrees `e` and coefficient bound `G0`. The numeric core
`baker_core_numeric_dmax` is applied with `q` fixed (huge, depending on the data) and `h` of the
size of `log B`.

Main results: `baker_core_explicit` (explicit lower bounds `bakerQreq` for `q` and `bakerCexp` for
the exponent `C`) and `baker_core_exists` (logarithms without any nontrivial integer relation:
there is an exponent `C` with `(B ^ C)⁻¹ ≤ ‖g 0 theta + ∑ g r theta * lg r‖`). -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- HOL Light: Baker/explicit.ml, baker_qreq. The explicit lower bound for the base `q`. -/
noncomputable def bakerQreq (n Dm : ℕ) (M : ℝ) : ℝ :=
  max (Real.exp 112)
    (max (2176 * M ^ 3 * 2 ^ bakerJ n Dm)
      (((bakerC Dm * (n + 1) : ℕ) : ℝ) * (8 * M + 75) * (6 * M) ^ (n + 3) *
        2 ^ (bakerJ n Dm + 1)))

/-- HOL Light: Baker/explicit.ml, baker_cexp. The explicit lower bound for the exponent `C`. -/
noncomputable def bakerCexp (n Dm E Ex : ℕ) (G0 : ℝ) (Dx : ℕ) (Mb : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ) ^ (bakerE1 n Dm + 1) *
      (2 * ((4 * Mb + (n : ℝ) + (Dm : ℝ) + 2) + Real.log (bakerKpar n Dm q) + Real.log G0 +
            1 + (Real.log G0 + (E : ℝ) * Mb + (Ex : ℝ) * Real.log (1 + (Dx : ℝ))) +
            (Dm : ℝ) * (Real.log (Dm : ℝ) + Real.log G0 + (E : ℝ) * Mb +
              (Ex : ℝ) * Real.log ((Dx : ℝ) + 1)) +
            (E : ℝ) * Mb + (Ex : ℝ) * Real.log ((Dx : ℝ) + 1)) +
        ((Ex : ℝ) + 3 * (Dm : ℝ) * (Ex : ℝ) + 3 * (Ex : ℝ))) +
    3 * (Dm : ℝ) * (Ex : ℝ) + 2 * (q : ℝ) ^ (bakerE1 n Dm + 1) +
    2 * ((Dm : ℝ) * (Real.log (Dm : ℝ) + Real.log G0 + (E : ℝ) * Mb +
      (Ex : ℝ) * Real.log ((Dx : ℝ) + 1)))

/-- HOL Light: Baker/explicit.ml, LOG_CA_LE_SA. The logarithm of the product of the root bounds
`(1 + d r * H r) ^ e r` is at most the weighted height sum. -/
theorem log_ca_le_sa (n : ℕ) (e d : ℕ → ℕ) (H : ℕ → ℝ)
    (h : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r) :
    Real.log (∏ r ∈ Finset.Icc 1 n, (1 + (d r : ℝ) * H r) ^ e r) ≤
      ∑ r ∈ Finset.Icc 1 n, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) := by
  have hpos : ∀ r ∈ Finset.Icc 1 n, 0 < 1 + (d r : ℝ) * H r := fun r hr => by
    have h1 := (h r hr).2
    have h2 : 0 ≤ (d r : ℝ) * H r := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  rw [Real.log_prod]
  · refine Finset.sum_le_sum fun r hr => ?_
    rw [Real.log_pow]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    obtain ⟨-, hH⟩ := h r hr
    refine Real.log_le_log (hpos r hr) ?_
    have h3 : H r ≤ H r ^ 3 := le_self_pow₀ hH (by norm_num)
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ (d r : ℝ) + 1 by positivity)
    push_cast
    linarith
  · exact fun r hr => (pow_pos (hpos r hr) _).ne'

/-- The core with explicit parameters, for a general upper bound `Dm` of `(∏ d r) * Dx ^ m` and
with the data `B`, `theta`, `g`, `dx`, `ax` fixed. -/
private theorem explicit_core_aux (n m : ℕ) (lg : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ)
    (H : ℕ → ℝ) (e : ℕ → ℕ) (G0 : ℝ) (Dx Dm E Ex : ℕ) (Mb : ℝ) (q C : ℕ)
    (hn : 1 ≤ n) (hDx : 1 ≤ Dx) (hG0 : 1 ≤ G0) (hMb : 1 ≤ Mb)
    (hPD : (∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m ≤ Dm)
    (hE : E = ∑ r ∈ Finset.Icc 1 n, e r)
    (hEx : Ex = ∑ r ∈ Finset.Icc (n + 1) (n + m), e r)
    (ha : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0)
    (hind : ∀ b : ℕ → ℤ, (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ bakerLpar n Dm q) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0)
    (hlmin : ∀ r ∈ Finset.Icc 1 n, Real.exp (-Mb) ≤ ‖lg r‖)
    (hsum : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Mb)
    (hH : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ Mb)
    (hq : bakerQreq n Dm (4 * Mb + (n : ℝ) + (Dm : ℝ) + 2) ≤ (q : ℝ))
    (hC : bakerCexp n Dm E Ex G0 Dx Mb q ≤ (C : ℝ))
    (B : ℝ) (theta : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ) (ax : ℕ → ℕ → ℤ)
    (hB : 2 ≤ B) (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hax : ∀ r ∈ Finset.Icc (n + 1) (n + m), 1 ≤ dx r ∧ dx r ≤ Dx ∧
      (∀ j, |(ax r j : ℝ)| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
      ∑ j ∈ Finset.range (dx r + 1), (ax r j : ℂ) * theta r ^ j = 0)
    (hg : ∀ j, j ≤ n → intpoly (Finset.Icc 1 (n + m)) e G0 (g j))
    (hgn : g n theta ≠ 0) :
    (B ^ C)⁻¹ ≤ ‖g 0 theta + ∑ r ∈ Finset.Icc 1 n, g r theta * lg r‖ := by
  classical
  have ha' : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0 :=
    fun r hr => by rw [htheta r hr]; exact ha r hr
  have hlogH : ∀ r ∈ Finset.Icc 1 n, 0 ≤ Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) :=
    fun r hr => Real.log_nonneg (one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)) (one_le_pow₀ (ha r hr).2.1))
  -- the height sum and the product of the root bounds
  obtain ⟨SA, hSA⟩ : ∃ SA : ℝ, SA =
      ∑ r ∈ Finset.Icc 1 n, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) := ⟨_, rfl⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, CA = ∏ r ∈ Finset.Icc 1 n, (1 + (d r : ℝ) * H r) ^ e r :=
    ⟨_, rfl⟩
  have hSA0 : 0 ≤ SA := by
    rw [hSA]
    exact Finset.sum_nonneg fun r hr => mul_nonneg (Nat.cast_nonneg _) (hlogH r hr)
  have hCA1 : 1 ≤ CA := by
    rw [hCA]
    refine product_ge_1 _ _ fun r hr => one_le_pow₀ ?_
    have h1 := (ha r hr).2.1
    have h2 : 0 ≤ (d r : ℝ) * H r := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hCApos : 0 < CA := by linarith
  have hSAE : SA ≤ (E : ℝ) * Mb := by
    rw [hSA, hE, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact (Finset.single_le_sum
      (f := fun r => Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)) hlogH hr).trans hH
  have hlogCA : Real.log CA ≤ SA := by
    rw [hCA, hSA]
    exact log_ca_le_sa n e d H fun r hr => ⟨(ha r hr).1, (ha r hr).2.1⟩
  have hlCA0 : 0 ≤ Real.log CA := Real.log_nonneg hCA1
  -- the degree product
  have hP1 : 1 ≤ (∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun r hr => by have := (ha r hr).1; omega)
      (pow_ne_zero _ (by omega)))
  obtain ⟨PD, hPDdef⟩ : ∃ PD : ℕ, PD = (∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m := ⟨_, rfl⟩
  rw [← hPDdef] at hPD hP1
  have hDm1 : 1 ≤ Dm := hP1.trans hPD
  -- the size parameter `M`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 4 * Mb + (n : ℝ) + (Dm : ℝ) + 2 := ⟨_, rfl⟩
  rw [← hM] at hq
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDmR : (1 : ℝ) ≤ Dm := by exact_mod_cast hDm1
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  -- the base `q`
  rw [bakerQreq, max_le_iff, max_le_iff] at hq
  obtain ⟨hq0, hq1, hq2⟩ := hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq0
  have hlq : 112 ≤ Real.log q := by
    have h1 := Real.log_le_log (Real.exp_pos _) hq0
    rwa [Real.log_exp] at h1
  have hq1' : 1 ≤ q := Nat.cast_pos.mp hqpos
  have hk1 : (1 : ℝ) ≤ (bakerKpar n Dm q : ℝ) := by
    rw [bakerKpar]
    exact_mod_cast Nat.one_le_pow _ _ hq1'
  have hlk0 : 0 ≤ Real.log (bakerKpar n Dm q) := Real.log_nonneg hk1
  have hlG0 : 0 ≤ Real.log G0 := Real.log_nonneg hG0
  have hDx0 : (0 : ℝ) ≤ Dx := Nat.cast_nonneg _
  have hlDx : 0 ≤ Real.log ((Dx : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlDm : 0 ≤ Real.log (Dm : ℝ) := Real.log_nonneg hDmR
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hEx0 : (0 : ℝ) ≤ Ex := Nat.cast_nonneg _
  have hEMb : 0 ≤ (E : ℝ) * Mb := mul_nonneg hE0 (by linarith)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (Ex : ℝ) * Real.log ((Dx : ℝ) + 1) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg hEx0 hlDx
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) ^ (bakerE1 n Dm + 1) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact pow_nonneg hqpos.le _
  obtain ⟨cL, hcL⟩ : ∃ cL : ℝ, cL =
      (Dm : ℝ) * (Real.log (Dm : ℝ) + Real.log G0 + (E : ℝ) * Mb + u) := ⟨_, rfl⟩
  have hcL0 : 0 ≤ cL := by rw [hcL]; exact mul_nonneg (by linarith) (by linarith)
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = M + Real.log (bakerKpar n Dm q) + Real.log G0 + 1 +
      (Real.log G0 + (E : ℝ) * Mb + u) + cL + (E : ℝ) * Mb + u := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = (Ex : ℝ) + 3 * (Dm : ℝ) * (Ex : ℝ) + 3 * (Ex : ℝ) :=
    ⟨_, rfl⟩
  have hCC : Q * (2 * K0 + K1) + 3 * (Dm : ℝ) * (Ex : ℝ) + 2 * Q + 2 * cL ≤ (C : ℝ) := by
    refine le_trans (le_of_eq ?_) hC
    rw [bakerCexp, hK0, hK1, hcL, hQ, hM, hu, add_comm (1 : ℝ) (Dx : ℝ)]
  have hK01 : 1 ≤ K0 := by rw [hK0]; linarith
  have hDmEx : 0 ≤ (Dm : ℝ) * (Ex : ℝ) := mul_nonneg (by linarith) hEx0
  have hK10 : 0 ≤ K1 := by rw [hK1]; linarith
  -- the height `B`
  have hB0 : 0 < B := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log B := ⟨_, rfl⟩
  have hLhalf : 1 / 2 ≤ L := by
    rw [hL]
    have h2 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
    have h3 := Real.log_two_gt_d9
    linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hprod, hGb, hLiou, hlogsum⟩ := baker_extra_bounds n m a d H e G0 Dx B theta g dx ax
    hn hDx hG0 hB ha' hax hg hgn
  rw [← hEx, ← hSA, ← hPDdef, ← hL] at hLiou
  rw [← hEx, ← hSA, ← hL] at hlogsum
  rw [← hPDdef] at hprod
  obtain ⟨Gn, hGn⟩ : ∃ Gn : ℝ, Gn = G0 * (CA * ((1 + (Dx : ℝ)) * B) ^ Ex) := ⟨_, rfl⟩
  rw [← hEx, ← hCA, ← hGn] at hGb
  have hDx1 : (0 : ℝ) < 1 + (Dx : ℝ) := by linarith
  have hDxB : 1 ≤ (1 + (Dx : ℝ)) * B :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hGn1 : 1 ≤ Gn := by
    rw [hGn]
    exact one_le_mul_of_one_le_of_one_le hG0
      (one_le_mul_of_one_le_of_one_le hCA1 (one_le_pow₀ hDxB))
  have hlGn : Real.log Gn = Real.log G0 + Real.log CA + (u + (Ex : ℝ) * L) := by
    have hp : 0 < ((1 + (Dx : ℝ)) * B) ^ Ex := pow_pos (mul_pos hDx1 hB0) _
    rw [hGn, Real.log_mul (by linarith) (mul_pos hCApos hp).ne',
      Real.log_mul hCApos.ne' hp.ne', Real.log_pow, Real.log_mul hDx1.ne' hB0.ne', hu, hL,
      add_comm (1 : ℝ) (Dx : ℝ)]
    ring
  -- the Liouville lower bound for `g n theta`
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = cL + 3 * (Dm : ℝ) * (Ex : ℝ) * L := ⟨_, rfl⟩
  have hx1 : 0 ≤ (Ex : ℝ) * L := mul_nonneg hEx0 hL0
  have hx2 : 0 ≤ (Dm : ℝ) * (Ex : ℝ) * L := mul_nonneg hDmEx hL0
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  have hLB : Real.exp (-T) ≤ ‖g n theta‖ := by
    refine le_trans (Real.exp_le_exp.2 (neg_le_neg ?_)) hLiou
    have hPDR : (PD : ℝ) ≤ Dm := by exact_mod_cast hPD
    have hPD1 : (1 : ℝ) ≤ PD := by exact_mod_cast hP1
    have h1 : Real.log (PD : ℝ) ≤ Real.log (Dm : ℝ) := Real.log_le_log (by linarith) hPDR
    have h0 : 0 ≤ Real.log (PD : ℝ) := Real.log_nonneg hPD1
    have hx3 : 0 ≤ (Ex : ℝ) * (Real.log ((Dx : ℝ) + 1) + 3 * L) :=
      mul_nonneg hEx0 (by linarith)
    have hT' : T = (Dm : ℝ) * (Real.log (Dm : ℝ) + (Real.log G0 + ((E : ℝ) * Mb +
        (u + 3 * ((Ex : ℝ) * L))))) := by rw [hT, hcL]; ring
    rw [hT']
    refine mul_le_mul hPDR ?_ (by linarith) (by linarith)
    linarith
  have hgnpos : 0 < ‖g n theta‖ := norm_pos_iff.mpr hgn
  have hinv : ‖g n theta‖⁻¹ ≤ Real.exp T := by
    have h1 := inv_anti₀ (Real.exp_pos _) hLB
    rwa [Real.exp_neg, inv_inv] at h1
  -- the bound for the coefficients `beta j = -(g j theta) / g n theta`
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℝ, Bb = 1 + Gn * Real.exp T := ⟨_, rfl⟩
  have hexpT1 : 1 ≤ Real.exp T := Real.one_le_exp hT0
  have hGE1 : 1 ≤ Gn * Real.exp T := one_le_mul_of_one_le_of_one_le hGn1 hexpT1
  have hBb1 : 1 ≤ Bb := by rw [hBb]; linarith
  have hbetaB : ∀ j, j < n → ‖-(g j theta) / g n theta‖ ≤ Bb := fun j hj => by
    rw [norm_div, norm_neg, div_eq_mul_inv, hBb]
    have h1 := mul_le_mul (hGb j hj.le) hinv (inv_nonneg.2 (norm_nonneg _)) (by linarith)
    linarith
  -- the height parameter `h`
  obtain ⟨h, hh1, hh2⟩ := real_num_ceil ((2 * K0 + K1) * L)
    (mul_nonneg (by linarith) hL0)
  have hK1L : K1 * L = (Ex : ℝ) * L + 3 * ((Dm : ℝ) * (Ex : ℝ) * L) + 3 * ((Ex : ℝ) * L) := by
    rw [hK1]; ring
  have hKh : K0 + K1 * L ≤ (h : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hLhalf (show 0 ≤ K0 by linarith)
    linarith
  have hlBb : Real.log Bb ≤ 1 + Real.log Gn + T := by
    have h2 : Bb ≤ 2 * (Gn * Real.exp T) := by rw [hBb]; linarith
    have h3 := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (by linarith), Real.log_mul (by linarith) (Real.exp_pos T).ne',
      Real.log_exp] at h3
    have h4 := Real.log_two_lt_d9
    linarith
  -- the contradiction with the numeric core
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℂ, Lf = g 0 theta + ∑ r ∈ Finset.Icc 1 n, g r theta * lg r :=
    ⟨_, rfl⟩
  rw [← hLf] at hcon
  have hident : -(g 0 theta) / g n theta +
      ∑ r ∈ Finset.Icc 1 (n - 1), -(g r theta) / g n theta * lg r - lg n =
        -Lf / g n theta := by
    have hsplit : ∑ r ∈ Finset.Icc 1 n, g r theta * lg r =
        ∑ r ∈ Finset.Icc 1 (n - 1), g r theta * lg r + g n theta * lg n := by
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]
    have h1 : ∑ r ∈ Finset.Icc 1 (n - 1), -(g r theta) / g n theta * lg r =
        -(∑ r ∈ Finset.Icc 1 (n - 1), g r theta * lg r) / g n theta := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1, hLf, hsplit]
    field_simp
    ring
  have hd0 : ‖Lf‖ / ‖g n theta‖ ≤ Real.exp (-(Q * (h : ℝ))) := by
    have hBC : (B ^ C)⁻¹ = Real.exp (-((C : ℝ) * L)) := by
      rw [hL, Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hB0, Real.rpow_natCast]
    calc ‖Lf‖ / ‖g n theta‖ ≤ (B ^ C)⁻¹ * Real.exp T := by
          rw [div_eq_mul_inv]
          exact mul_le_mul hcon.le hinv (inv_nonneg.2 (norm_nonneg _))
            (inv_pos.2 (pow_pos hB0 C)).le
      _ = Real.exp (-((C : ℝ) * L) + T) := by rw [hBC, Real.exp_add]
      _ ≤ Real.exp (-(Q * (h : ℝ))) := by
          rw [Real.exp_le_exp]
          have h1 : Q * (h : ℝ) ≤ Q * ((2 * K0 + K1) * L + 1) :=
            mul_le_mul_of_nonneg_left hh2.le hQ0
          have h2 := mul_le_mul_of_nonneg_right hCC hL0
          have h3 := mul_le_mul_of_nonneg_left hLhalf (show 0 ≤ 2 * Q + 2 * cL by linarith)
          rw [hT]
          linarith
  obtain ⟨hmerge, -, -⟩ := baker_extra_merge n m a d H Dx B theta dx ax (by linarith) ha' hax
  have hK1L0 : 0 ≤ K1 * L := mul_nonneg hK10 hL0
  have hsum0 : 0 ≤ ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ := Finset.sum_nonneg fun r _ => norm_nonneg _
  refine baker_core_numeric_dmax n lg theta (Finset.Icc 1 (n + m)) g e G0
    (fun r => if r ≤ n then a r else ax r) (fun r => if r ≤ n then d r else dx r)
    (fun r => if r ≤ n then H r else B) (fun j => -(g j theta) / g n theta) Bb
    (1 + ∑ r ∈ Finset.Icc 1 n, ‖lg r‖) (‖Lf‖ / ‖g n theta‖) (Real.exp (-Mb)) Gn M q h Dm
    hn hG0 (Finset.Icc_subset_Icc le_rfl (Nat.le_add_right _ _)) htheta hg hgn (hGb n le_rfl)
    hGn1 (fun j _ => div_mul_cancel₀ _ hgn) hmerge hind hBb1 hbetaB (by linarith)
    (fun r hr => ?_) (by linarith) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
    hlmin (by rw [hM]; linarith) (hprod.trans hPD) (by rw [hM]; linarith)
    (by rw [hM]; linarith) ?_ ?_ hlq hq1 hq2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [← hQ]; exact hd0)
  · have h1 : ‖lg r‖ ≤ ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ :=
      Finset.single_le_sum (f := fun r => ‖lg r‖) (fun r _ => norm_nonneg _) hr
    linarith
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun r hr => ?_)) (hH.trans ?_)
    · have hrn := (Finset.mem_Icc.mp hr).2
      simp only [ite_eq_left hrn]
    · rw [hM]; linarith
  · rw [← Real.exp_neg, neg_neg, Real.log_exp, hM]; linarith
  · have h1 : (1 : ℝ) ≤ (h : ℝ) := by linarith
    exact_mod_cast h1
  · rw [hK0] at hKh; linarith
  · rw [hK0] at hKh; linarith
  · rw [hK0] at hKh; linarith
  · rw [hK0] at hKh; linarith
  · rw [hK0] at hKh; linarith
  · refine hlogsum.trans ?_
    rw [hK0] at hKh
    linarith
  · exact le_of_eq (by rw [hident, norm_div, norm_neg])

/-- HOL Light: Baker/explicit.ml, BAKER_CORE_EXPLICIT. The core lower bound with explicit
parameters: if `Mb` bounds `∑ ‖lg r‖`, `log (1 / ‖lg r‖)` and the height sum, the logarithms have
no nontrivial integer relation with coefficients at most `bakerLpar`, `q ≥ bakerQreq` and
`C ≥ bakerCexp`, then `(B ^ C)⁻¹ ≤ ‖g 0 theta + ∑ g r theta * lg r‖`.

Deviation: the integer-constrained reals `a r j`, `b r`, `ax r j` are `ℤ`-valued, so the `integer`
conjuncts are dropped; the hypotheses are separate arguments in HOL's order. -/
theorem baker_core_explicit (n m : ℕ) (lg : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (e : ℕ → ℕ) (G0 : ℝ) (Dx Dmax : ℕ) (Mb : ℝ) (q C : ℕ)
    (hn : 1 ≤ n) (hDx : 1 ≤ Dx) (hG0 : 1 ≤ G0) (hMb : 1 ≤ Mb)
    (hDmax : ∏ r ∈ Finset.Icc 1 n, d r ≤ Dmax)
    (ha : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0)
    (hind : ∀ b : ℕ → ℤ,
      (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ bakerLpar n (Dmax * Dx ^ m) q) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0)
    (hlmin : ∀ r ∈ Finset.Icc 1 n, Real.exp (-Mb) ≤ ‖lg r‖)
    (hsum : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Mb)
    (hH : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ Mb)
    (hq : bakerQreq n (Dmax * Dx ^ m)
      (4 * Mb + (n : ℝ) + ((Dmax * Dx ^ m : ℕ) : ℝ) + 2) ≤ (q : ℝ))
    (hC : bakerCexp n (Dmax * Dx ^ m) (∑ r ∈ Finset.Icc 1 n, e r)
      (∑ r ∈ Finset.Icc (n + 1) (n + m), e r) G0 Dx Mb q ≤ (C : ℝ)) :
    ∀ (B : ℝ) (theta : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ) (ax : ℕ → ℕ → ℤ),
      2 ≤ B →
      (∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r)) →
      (∀ r ∈ Finset.Icc (n + 1) (n + m), 1 ≤ dx r ∧ dx r ≤ Dx ∧
        (∀ j, |(ax r j : ℝ)| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
        ∑ j ∈ Finset.range (dx r + 1), (ax r j : ℂ) * theta r ^ j = 0) →
      (∀ j, j ≤ n → intpoly (Finset.Icc 1 (n + m)) e G0 (g j)) →
      g n theta ≠ 0 →
      (B ^ C)⁻¹ ≤ ‖g 0 theta + ∑ r ∈ Finset.Icc 1 n, g r theta * lg r‖ :=
  fun B theta g dx ax hB htheta hax hg hgn =>
    explicit_core_aux n m lg a d H e G0 Dx (Dmax * Dx ^ m) _ _ Mb q C hn hDx hG0 hMb
      (Nat.mul_le_mul_right _ hDmax) rfl rfl ha hind hlmin hsum hH hq hC B theta g dx ax hB
      htheta hax hg hgn

/-- HOL Light: Baker/explicit.ml, INDEPENDENT_IMP_SMALL. If the logarithms have no nontrivial
integer relation at all, they have none with coefficients of size at most `X`.

Deviation: the integer-constrained reals `b r` are `ℤ`-valued. -/
theorem independent_imp_small (n : ℕ) (lg : ℕ → ℂ) (X : ℝ)
    (h : ∀ b : ℕ → ℤ, ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 →
      ∀ r ∈ Finset.Icc 1 n, b r = 0) :
    ∀ b : ℕ → ℤ, (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ X) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0 :=
  fun b _ hs => h b hs

/-- HOL Light: Baker/explicit.ml, LOGS_NONZERO_OF_INDEPENDENT. Logarithms without a nontrivial
integer relation are nonzero.

Deviation: the integer-constrained reals `b r` are `ℤ`-valued. -/
theorem logs_nonzero_of_independent (n : ℕ) (lg : ℕ → ℂ)
    (h : ∀ b : ℕ → ℤ, ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 →
      ∀ r ∈ Finset.Icc 1 n, b r = 0) :
    ∀ r ∈ Finset.Icc 1 n, lg r ≠ 0 := by
  intro s hs h0
  have h1 := h (fun r => if r = s then 1 else 0) (Finset.sum_eq_zero fun r _ => by
    by_cases hr : r = s
    · simp [hr, h0]
    · simp [hr]) s hs
  simp at h1

/-- HOL Light: Baker/explicit.ml, LMIN_EXISTS. Finitely many nonzero logarithms have a positive
lower bound `lmin ≤ 1` for their absolute values. -/
theorem lmin_exists (n : ℕ) (lg : ℕ → ℂ) (hn : 1 ≤ n)
    (h : ∀ r ∈ Finset.Icc 1 n, lg r ≠ 0) :
    ∃ lmin : ℝ, 0 < lmin ∧ lmin ≤ 1 ∧ ∀ r ∈ Finset.Icc 1 n, lmin ≤ ‖lg r‖ := by
  obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 n) (fun r => ‖lg r‖)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  exact ⟨min 1 ‖lg r0‖, lt_min one_pos (norm_pos_iff.mpr (h r0 hr0)), min_le_left _ _,
    fun r hr => (min_le_right _ _).trans (hmin r hr)⟩

/-- HOL Light: Baker/explicit.ml, BAKER_CORE_EXISTS. The core lower bound with an existential
exponent: for logarithms `lg 1, ..., lg n` without any nontrivial integer relation whose
exponentials are algebraic, there is `C` such that for all `B ≥ 2` and all values `theta` of the
`m` extra variables that are roots of integer polynomials of degree at most `Dx` and height at
most `B`, if `g n theta ≠ 0` then `(B ^ C)⁻¹ ≤ ‖g 0 theta + ∑ g r theta * lg r‖`.

Deviation: the integer-constrained reals `a r j`, `b r`, `ax r j` are `ℤ`-valued, so the `integer`
conjuncts are dropped; the hypotheses are separate arguments in HOL's order. -/
theorem baker_core_exists (n m : ℕ) (lg : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (e : ℕ → ℕ) (G0 : ℝ) (Dx : ℕ)
    (hn : 1 ≤ n) (hDx : 1 ≤ Dx) (hG0 : 1 ≤ G0)
    (ha : ∀ r ∈ Finset.Icc 1 n, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧
      a r (d r) ≠ 0 ∧ ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * Complex.exp (lg r) ^ j = 0)
    (hind : ∀ b : ℕ → ℤ, ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 →
      ∀ r ∈ Finset.Icc 1 n, b r = 0) :
    ∃ C : ℕ, ∀ (B : ℝ) (theta : ℕ → ℂ) (g : ℕ → (ℕ → ℂ) → ℂ) (dx : ℕ → ℕ)
      (ax : ℕ → ℕ → ℤ),
      2 ≤ B →
      (∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r)) →
      (∀ r ∈ Finset.Icc (n + 1) (n + m), 1 ≤ dx r ∧ dx r ≤ Dx ∧
        (∀ j, |(ax r j : ℝ)| ≤ B) ∧ ax r (dx r) ≠ 0 ∧
        ∑ j ∈ Finset.range (dx r + 1), (ax r j : ℂ) * theta r ^ j = 0) →
      (∀ j, j ≤ n → intpoly (Finset.Icc 1 (n + m)) e G0 (g j)) →
      g n theta ≠ 0 →
      (B ^ C)⁻¹ ≤ ‖g 0 theta + ∑ r ∈ Finset.Icc 1 n, g r theta * lg r‖ := by
  obtain ⟨lmin, hlmin0, hlmin1, hlmin⟩ :=
    lmin_exists n lg hn (logs_nonzero_of_independent n lg hind)
  have hcH : 0 ≤ ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) :=
    Finset.sum_nonneg fun r hr => Real.log_nonneg (one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)) (one_le_pow₀ (ha r hr).2.1))
  have hLam : 0 ≤ ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ := Finset.sum_nonneg fun r _ => norm_nonneg _
  have hll : 0 ≤ Real.log lmin⁻¹ := Real.log_nonneg ((one_le_inv₀ hlmin0).2 hlmin1)
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = 1 + ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ +
      ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) + Real.log lmin⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := exists_nat_ge (bakerQreq n ((∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m)
    (4 * Mb + (n : ℝ) + (((∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m : ℕ) : ℝ) + 2))
  obtain ⟨C, hC⟩ := exists_nat_ge (bakerCexp n ((∏ r ∈ Finset.Icc 1 n, d r) * Dx ^ m)
    (∑ r ∈ Finset.Icc 1 n, e r) (∑ r ∈ Finset.Icc (n + 1) (n + m), e r) G0 Dx Mb q)
  refine ⟨C, baker_core_explicit n m lg a d H e G0 Dx (∏ r ∈ Finset.Icc 1 n, d r) Mb q C hn hDx
    hG0 (by rw [hMb]; linarith) le_rfl ha (independent_imp_small n lg _ hind) (fun r hr => ?_)
    (by rw [hMb]; linarith) (by rw [hMb]; linarith) hq hC⟩
  refine le_trans ?_ (hlmin r hr)
  have h1 : Real.exp (-Mb) ≤ Real.exp (Real.log lmin) := by
    rw [Real.exp_le_exp, hMb, Real.log_inv]
    rw [Real.log_inv] at hll
    linarith
  rwa [Real.exp_log hlmin0] at h1

end RiemannMasullo.Baker
