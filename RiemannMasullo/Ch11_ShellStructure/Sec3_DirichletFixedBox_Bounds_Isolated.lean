module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3a
public import RiemannMasullo.ForMathlib.NumberTheory.LinearFormsInLogarithms
public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import RiemannMasullo.Ch13_ZerosHecke.Targets
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Bounds)

Analytic and arithmetic reciprocal bounds and twisted Poisson summation for primitive `χ`.

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

/-! ### Section 1: Analytic and arithmetic reciprocal bounds -/

section AnalyticAndArithmeticBounds

/-- For a primitive Dirichlet character of conductor `N > 1`, the character is nontrivial. -/
theorem dirichlet_ne_one_of_isPrimitive_of_one_lt {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N) : χ ≠ 1 := by
  intro h1
  have hc : χ.conductor = 1 := by
    rw [h1]
    exact DirichletCharacter.conductor_one
  change χ.conductor = N at hχ
  rw [hχ] at hc
  omega

/-- The inverse of a primitive nontrivial Dirichlet character is primitive and nontrivial. -/
theorem dirichlet_inv_isPrimitive_ne_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N) :
    χ⁻¹.IsPrimitive ∧ χ⁻¹ ≠ 1 :=
  ⟨hχ.inv, fun h ↦ dirichlet_ne_one_of_isPrimitive_of_one_lt hχ hN (inv_eq_one.mp h)⟩

private theorem lfunction_meromorphicNFOn {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    MeromorphicNFOn (DirichletCharacter.LFunction χ) univ := by
  have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  intro z _
  exact (hd.analyticAt z).meromorphicNFAt

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496; cf. Theorem B.6.1.6, p. 640.
For a primitive nontrivial Dirichlet character `χ` of conductor `N > 1`, the reciprocal of
`L(1 - i t, χ⁻¹)` grows at most polynomially over the entire real line `t : ℝ` (including
`t = 0`, where `L(1, χ⁻¹) ≠ 0`).
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletLFunction_inv_poly_bound_oneLine {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N) :
    ∃ C > (0 : ℝ), ∃ A : ℕ, ∀ t : ℝ,
      ‖(DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I))⁻¹‖ ≤
        C * (1 + |t|) ^ A := by
  obtain ⟨hχinv_prim, hχinv_ne⟩ := dirichlet_inv_isPrimitive_ne_one hχ hN
  obtain ⟨ψ, -, hψL⟩ :=
    RiemannMasullo.DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq hχinv_prim
  have hSeries : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ),
      DirichletCharacter.LFunction χ⁻¹ s = finiteHeckeL ψ s := fun s ↦ by
    rw [hψL s.val s.property, DirichletCharacter.LFunction_eq_LSeries χ⁻¹ s.property]
  obtain ⟨-, A, -, hBigO⟩ := finiteHeckeL_inv_isBigO_oneLine ψ
    (DirichletCharacter.LFunction χ⁻¹) (lfunction_meromorphicNFOn hχinv_ne) hSeries
  rw [Asymptotics.isBigO_iff] at hBigO
  obtain ⟨C₁, hC₁⟩ := hBigO
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hC₁
  obtain ⟨T, hT⟩ := hC₁
  let T₀ := max T 0
  let g : ℝ → ℂ := fun t ↦ (DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I))⁻¹
  have hg_cont : Continuous g := by
    have hLcont : Continuous (fun t : ℝ ↦ DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I)) :=
      (DirichletCharacter.differentiable_LFunction hχinv_ne).continuous.comp (by fun_prop)
    refine hLcont.inv₀ fun t ↦ ?_
    refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv_ne) ?_
    simp [Complex.sub_re, Complex.mul_re]
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (show -T₀ ≤ T₀ by linarith [le_max_right T 0]))
    hg_cont.norm.continuousOn
  let C := max (max C₁ 0 + 1) (‖g t₀‖ + 1)
  refine ⟨C, by positivity, A, fun t ↦ ?_⟩
  have hC₁_le : C₁ ≤ C := (le_max_left C₁ 0).trans ((lt_add_one _).le.trans (le_max_left _ _))
  have hC₂_le : ‖g t₀‖ ≤ C := (lt_add_one _).le.trans (le_max_right _ _)
  have hpow_ge : (1 : ℝ) ≤ (1 + |t|) ^ A := one_le_pow₀ (by linarith [abs_nonneg t])
  by_cases ht : T₀ ≤ |t|
  · have htT : T ≤ |-t| := by rw [abs_neg]; exact (le_max_left T 0).trans ht
    have hbd := hT |-t| htT (-t) rfl
    have hL_eq : DirichletCharacter.LFunction χ⁻¹ ⟨1, -t⟩ =
        DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I) := by
      congr 1
      apply Complex.ext <;> simp
    change ‖(DirichletCharacter.LFunction χ⁻¹ ⟨1, -t⟩)⁻¹‖ ≤ C₁ * ‖|-t| ^ A‖ at hbd
    rw [hL_eq, abs_neg, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg t) A)] at hbd
    calc ‖g t‖ ≤ C₁ * |t| ^ A := hbd
      _ ≤ C * |t| ^ A := mul_le_mul_of_nonneg_right hC₁_le (pow_nonneg (abs_nonneg t) A)
      _ ≤ C * (1 + |t|) ^ A := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg t) (by linarith) A) (by positivity)
  · have hmem : t ∈ Icc (-T₀) T₀ := abs_le.mp (not_le.mp ht).le
    calc ‖g t‖ ≤ ‖g t₀‖ := ht₀ hmem
      _ ≤ C := hC₂_le
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (1 + |t|) ^ A := mul_le_mul_of_nonneg_left hpow_ge (by positivity)

/-- Base frequency `arg(χ p) / log p` for the shifted prime lattice of `p` under `χ`. -/
def dirichletPrimeBaseFreq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) : ℝ :=
  Complex.arg (χ p) / Real.log p

/-- The `j`-th lattice point `(arg(χ p) + 2 π j) / log p` where `χ p * p ^ (-i t) = 1`. -/
def dirichletPrimeFreq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) (j : ℤ) : ℝ :=
  (Complex.arg (χ p) + 2 * Real.pi * j) / Real.log p

private theorem dirichlet_pow_orderOf_eq_one_of_coprime {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {r : ℕ} (hr : r.Coprime N) :
    χ r ^ orderOf χ = 1 := by
  have hu : IsUnit (r : ZMod N) := (ZMod.isUnit_iff_coprime r N).mpr hr
  have hpow : ∀ k : ℕ, (χ ^ k) r = χ r ^ k := fun k ↦ by
    induction k with
    | zero => simp [pow_zero, MulChar.one_apply hu]
    | succ k ih => simp [pow_succ, ih]
  rw [← hpow (orderOf χ), pow_orderOf_eq_one, MulChar.one_apply hu]

theorem dirichlet_norm_apply_eq_one_of_coprime {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Coprime N) : ‖χ p‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (dirichlet_pow_orderOf_eq_one_of_coprime χ hp) χ.orderOf_pos.ne'

theorem dirichlet_mul_cpow_primeFreq_eq_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hcop : p.Coprime N) (j : ℤ) :
    χ p * (p : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I) = 1 := by
  have hnorm : ‖χ p‖ = 1 := dirichlet_norm_apply_eq_one_of_coprime χ hcop
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hχ_exp : χ p = Complex.exp (Complex.arg (χ p) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (χ p)
    rw [hnorm, Complex.ofReal_one, one_mul] at h
    exact h.symm
  have hcpow : (p : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I) =
      Complex.exp (-(Complex.arg (χ p) + 2 * Real.pi * j) * Complex.I) := by
    rw [← Complex.ofReal_natCast p,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp_pos.ne'),
      ← Complex.ofReal_log hp_pos.le]
    congr 1
    rw [← mul_assoc, mul_neg, neg_mul, ← Complex.ofReal_mul]
    dsimp [dirichletPrimeFreq]
    rw [mul_div_cancel₀ _ hlog]
    push_cast
    ring
  rw [hχ_exp, hcpow, ← Complex.exp_add]
  have harg : (Complex.arg (χ p) : ℂ) * Complex.I +
      (-(Complex.arg (χ p) + 2 * Real.pi * j) : ℂ) * Complex.I =
      ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg]
  simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I (-j)

theorem dirichlet_exp_orderOf_eq_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hcop : p.Coprime N) (j : ℤ) :
    Complex.exp ((orderOf χ : ℕ) *
      (-(Real.log p : ℂ) * ((dirichletPrimeFreq χ p j : ℂ) * Complex.I))) = 1 := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmul := dirichlet_mul_cpow_primeFreq_eq_one χ hp hcop j
  have hpow := congrArg (fun z : ℂ ↦ z ^ orderOf χ) hmul
  rw [mul_pow, one_pow, dirichlet_pow_orderOf_eq_one_of_coprime χ hcop, one_mul,
    ← Complex.ofReal_natCast p,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp_pos.ne'),
    ← Complex.ofReal_log hp_pos.le, ← Complex.exp_nat_mul] at hpow
  simpa [mul_assoc] using hpow

private theorem shifted_prime_pow_eq_one_imp_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p.Coprime N) (hqN : q.Coprime N) (hpq : p ≠ q) {t : ℝ}
    (htp : χ p * (p : ℂ) ^ (-(t : ℂ) * Complex.I) = 1)
    (htq : χ q * (q : ℂ) ^ (-(t : ℂ) * Complex.I) = 1) : t = 0 := by
  by_contra ht0
  let M : ℕ := orderOf χ
  have hMpos : 0 < M := χ.orderOf_pos
  have hexp_eq_one (r : ℕ) (hr : r.Prime) (hrN : r.Coprime N)
      (htr : χ r * (r : ℂ) ^ (-(t : ℂ) * Complex.I) = 1) :
      ∃ k : ℤ, (M : ℝ) * t * Real.log r = 2 * Real.pi * k := by
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr.pos
    have hpow := congrArg (fun z : ℂ ↦ z ^ M) htr
    rw [mul_pow, one_pow, dirichlet_pow_orderOf_eq_one_of_coprime χ hrN, one_mul,
      ← Complex.ofReal_natCast r,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr_pos.ne'),
      ← Complex.ofReal_log hr_pos.le, ← Complex.exp_nat_mul] at hpow
    rw [Complex.exp_eq_one_iff] at hpow
    obtain ⟨k, hk⟩ := hpow
    have him := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, add_zero, sub_zero, mul_one] at him
    refine ⟨-k, ?_⟩
    push_cast
    linarith
  obtain ⟨k, hk⟩ := hexp_eq_one p hp hpN htp
  obtain ⟨l, hl⟩ := hexp_eq_one q hq hqN htq
  have hp_gt : 1 < p := hp.one_lt
  have hq_gt : 1 < q := hq.one_lt
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp_gt)
  have hlogq_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq_gt)
  have hk_ne : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero] at hk
    have hMt : (M : ℝ) * t = 0 := (mul_eq_zero.mp hk).resolve_right hlogp_pos.ne'
    exact ht0 ((mul_eq_zero.mp hMt).resolve_left (by exact_mod_cast hMpos.ne'))
  have hlin : (l : ℝ) * Real.log p = (k : ℝ) * Real.log q := by
    have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
    have h2pi_ne : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have h1 : (M : ℝ) * t * Real.log p * (2 * Real.pi * l) =
        (M : ℝ) * t * Real.log q * (2 * Real.pi * k) := by
      rw [← hl, ← hk]; ring
    have h2 : (M : ℝ) * t * (2 * Real.pi) * ((l : ℝ) * Real.log p) =
        (M : ℝ) * t * (2 * Real.pi) * ((k : ℝ) * Real.log q) := by
      linarith [h1]
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hM_ne ht0) h2pi_ne) h2
  have hpow_real : ((p : ℝ) ^ l) = ((q : ℝ) ^ k) := by
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlog_eq : Real.log ((p : ℝ) ^ l) = Real.log ((q : ℝ) ^ k) := by
      rw [Real.log_zpow, Real.log_zpow, hlin]
    exact Real.log_injOn_pos (zpow_pos hp_pos l) (zpow_pos hq_pos k) hlog_eq
  have hl_ne : l ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul] at hlin
    exact hk_ne (Int.cast_eq_zero.mp ((mul_eq_zero.mp hlin.symm).resolve_right hlogq_pos.ne'))
  have hpow_abs : p ^ l.natAbs = q ^ k.natAbs := by
    have hsign : l * k > 0 := by
      by_contra hle
      push Not at hle
      have : (l : ℝ) * k ≤ 0 := by exact_mod_cast hle
      have hp_lin : (l : ℝ) * Real.log p * ((k : ℝ) * Real.log q) > 0 := by
        rw [hlin]
        exact mul_self_pos.mpr (mul_ne_zero (Int.cast_ne_zero.mpr hk_ne) hlogq_pos.ne')
      have hfac : (l : ℝ) * Real.log p * ((k : ℝ) * Real.log q) =
          ((l : ℝ) * k) * (Real.log p * Real.log q) := by ring
      rw [hfac] at hp_lin
      nlinarith [mul_pos hlogp_pos hlogq_pos]
    have hl_neg : (p : ℝ) ^ l.natAbs = (q : ℝ) ^ k.natAbs := by
      rcases Int.lt_or_gt_of_ne hl_ne with hl_lt | hl_gt
      · have hk_lt : k < 0 := by nlinarith
        have hinv : ((p : ℝ) ^ (-l))⁻¹ = ((q : ℝ) ^ (-k))⁻¹ := by
          simpa [zpow_neg] using hpow_real
        have hpos_eq : (p : ℝ) ^ (-l) = (q : ℝ) ^ (-k) := inv_inj.mp hinv
        have hl' : (-l : ℤ) = (l.natAbs : ℤ) := (Int.ofNat_natAbs_of_nonpos hl_lt.le).symm
        have hk' : (-k : ℤ) = (k.natAbs : ℤ) := (Int.ofNat_natAbs_of_nonpos hk_lt.le).symm
        rw [hl', hk', zpow_natCast, zpow_natCast] at hpos_eq
        exact hpos_eq
      · have hk_gt : 0 < k := by nlinarith
        rw [← Int.natAbs_of_nonneg hl_gt.le, ← Int.natAbs_of_nonneg hk_gt.le,
          zpow_natCast, zpow_natCast] at hpow_real
        exact hpow_real
    exact_mod_cast hl_neg
  have hdvd : p ∣ q ^ k.natAbs := hpow_abs ▸ dvd_pow_self p (Int.natAbs_ne_zero.mpr hl_ne)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- Shifted prime lattices `χ(p) p^(-i t) = 1` and `χ(q) q^(-i t) = 1` for distinct primes
`p ≠ q` coprime to `N` can intersect only at `t = 0` (which happens precisely when `χ(p) = χ(q) = 1`).
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichlet_shifted_lattice_disjoint_nonzero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p.Coprime N) (hqN : q.Coprime N) (hpq : p ≠ q) {t : ℝ}
    (htp : χ p * (p : ℂ) ^ (-(t : ℂ) * Complex.I) = 1)
    (htq : χ q * (q : ℂ) ^ (-(t : ℂ) * Complex.I) = 1) :
    t = 0 ∧ χ p = 1 ∧ χ q = 1 := by
  have ht0 : t = 0 := shifted_prime_pow_eq_one_imp_zero χ hp hq hpN hqN hpq htp htq
  subst ht0
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one] at htp htq
  exact ⟨rfl, htp, htq⟩

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496; cf. Theorem 7.3.1.1, p. 346.
For distinct primes `p ≠ q` coprime to `N`, along the shifted `p`-lattice `t_j` with `t_j ≠ 0`,
the reciprocal `(1 - χ(q) q^(-i t_j))⁻¹` grows at most polynomially in `|t_j|`, proved from
`polynomial_bound_inv_one_sub_of_exp_eq_one` with common root-of-unity order `orderOf χ`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichlet_shifted_two_log_inv_poly_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p.Coprime N) (hqN : q.Coprime N) :
    ∃ d : ℕ, ∃ C ≥ (0 : ℝ), ∀ j : ℤ, dirichletPrimeFreq χ p j ≠ 0 →
      ‖(1 - χ q * (q : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I))⁻¹‖ ≤
        C * (1 + |dirichletPrimeFreq χ p j|) ^ d := by
  let M : ℕ := orderOf χ
  obtain ⟨d, C, hC, hbak⟩ := polynomial_bound_inv_one_sub_of_exp_eq_one p q M
    hp.one_lt hq.one_lt χ.orderOf_pos
  refine ⟨d, C, hC, fun j _ ↦ ?_⟩
  let s : ℂ := (dirichletPrimeFreq χ p j : ℂ) * Complex.I
  let z : ℂ := χ q * (q : ℂ) ^ (-s)
  have h₁ : Complex.exp ((M : ℕ) * (-(Real.log p : ℂ) * s)) = 1 :=
    dirichlet_exp_orderOf_eq_one χ hp hpN j
  have h₂ : z ^ M = Complex.exp ((M : ℕ) * (-(Real.log q : ℂ) * s)) := by
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hχq : χ q ^ M = 1 := dirichlet_pow_orderOf_eq_one_of_coprime χ hqN
    dsimp [z]
    rw [mul_pow, hχq, one_mul, ← Complex.ofReal_natCast q,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq_pos.ne'),
      ← Complex.ofReal_log hq_pos.le, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hres := hbak s z h₁ h₂
  have hsnorm : ‖s‖ = |dirichletPrimeFreq χ p j| := by simp [s, Complex.norm_I]
  simpa only [z, s, neg_mul, hsnorm] using hres

/-- The finite Euler multiplier `B_T(z) = ∏_{q ∈ T} (1 - χ(q) q^(-z))` for a finite set `T` of
earlier primes. -/
def dirichletStageMultiplier {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : Finset ℕ)
    (z : ℂ) : ℂ :=
  ∏ q ∈ T, (1 - χ q * (q : ℂ) ^ (-z))

/-- The vanishing order `|{q ∈ T | χ(q) = 1}|` of `B_T(z)` at `z = 0`. -/
def dirichletStageZeroOrder {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : Finset ℕ) : ℕ :=
  (T.filter fun q : ℕ ↦ χ q = 1).card

private theorem dirichletStageMultiplier_factor_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p.Coprime N) (hqN : q.Coprime N) (hpq : p ≠ q) {j : ℤ}
    (hj : dirichletPrimeFreq χ p j ≠ 0) :
    1 - χ q * (q : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I) ≠ 0 := by
  intro hz
  have htq : χ q * (q : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I) = 1 :=
    (sub_eq_zero.mp hz).symm
  have htp := dirichlet_mul_cpow_primeFreq_eq_one χ hp hpN j
  exact hj (dirichlet_shifted_lattice_disjoint_nonzero χ hp hq hpN hqN hpq htp htq).1

/-- For any finite set `T` of primes coprime to `N` with `p ∉ T`, `B_T(i t_j)` is nonzero for
all nonzero lattice points `t_j` and its reciprocal has at most polynomial growth in `|t_j|`. -/
theorem dirichletStageMultiplier_inv_poly_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T) :
    ∃ D : ℕ, ∃ C > (0 : ℝ), ∀ j : ℤ, dirichletPrimeFreq χ p j ≠ 0 →
      dirichletStageMultiplier χ T ((dirichletPrimeFreq χ p j : ℂ) * Complex.I) ≠ 0 ∧
        ‖(dirichletStageMultiplier χ T ((dirichletPrimeFreq χ p j : ℂ) * Complex.I))⁻¹‖ ≤
          C * (1 + |dirichletPrimeFreq χ p j|) ^ D := by
  classical
  have hfac : ∀ q ∈ T, ∃ d : ℕ, ∃ C ≥ (0 : ℝ), ∀ j : ℤ, dirichletPrimeFreq χ p j ≠ 0 →
      1 - χ q * (q : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I) ≠ 0 ∧
        ‖(1 - χ q * (q : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I))⁻¹‖ ≤
          C * (1 + |dirichletPrimeFreq χ p j|) ^ d := by
    intro q hq
    obtain ⟨d, C, hC, hbd⟩ := dirichlet_shifted_two_log_inv_poly_bound χ hp (hT q hq).1
      hpN (hT q hq).2
    refine ⟨d, C, hC, fun j hj ↦ ⟨?_, hbd j hj⟩⟩
    exact dirichletStageMultiplier_factor_ne_zero χ hp (hT q hq).1 hpN (hT q hq).2
      (fun h ↦ hpT (h ▸ hq)) hj
  choose dfun Cfun hCfun hbdd using fun q : T ↦ hfac q.1 q.2
  have hposC : (0 : ℝ) < (∏ q : T, (Cfun q + 1)) + 1 := by
    have hp0 : 0 ≤ ∏ q : T, (Cfun q + 1) :=
      Finset.prod_nonneg fun q _ ↦ by linarith [hCfun q]
    linarith
  refine ⟨∑ q : T, dfun q, (∏ q : T, (Cfun q + 1)) + 1, hposC, fun j hj ↦ ?_⟩
  have hne : dirichletStageMultiplier χ T ((dirichletPrimeFreq χ p j : ℂ) * Complex.I) ≠ 0 := by
    rw [dirichletStageMultiplier, Finset.prod_ne_zero_iff]
    intro q hq
    simpa only [neg_mul] using (hbdd ⟨q, hq⟩ j hj).1
  refine ⟨hne, ?_⟩
  have hinv_prod :
      ‖(dirichletStageMultiplier χ T ((dirichletPrimeFreq χ p j : ℂ) * Complex.I))⁻¹‖ =
        ∏ q : T, ‖(1 - χ q.1 * (q.1 : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I))⁻¹‖ := by
    rw [dirichletStageMultiplier, ← Finset.prod_attach (s := T),
      ← Finset.prod_inv_distrib, norm_prod]
    simp [neg_mul]
  rw [hinv_prod]
  let w : ℝ := 1 + |dirichletPrimeFreq χ p j|
  have hw0 : 0 ≤ w := by dsimp [w]; linarith [abs_nonneg (dirichletPrimeFreq χ p j)]
  have hle_prod :
      ∏ q : T, ‖(1 - χ q.1 * (q.1 : ℂ) ^ (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I))⁻¹‖ ≤
        ∏ q : T, ((Cfun q + 1) * w ^ dfun q) := by
    have hprod_mono : ∀ (s : Finset T) (f g : T → ℝ), (∀ x ∈ s, 0 ≤ f x) → (∀ x ∈ s, f x ≤ g x) →
        ∏ x ∈ s, f x ≤ ∏ x ∈ s, g x := by
      intro s f g hf0 hfg
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
          (ih (fun x hx ↦ hf0 x (Finset.mem_insert_of_mem hx))
            (fun x hx ↦ hfg x (Finset.mem_insert_of_mem hx)))
          (Finset.prod_nonneg fun x hx ↦ hf0 x (Finset.mem_insert_of_mem hx))
          (le_trans (hf0 a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))
    refine hprod_mono Finset.univ _ _ (fun _ _ ↦ norm_nonneg _) fun q _ ↦ ?_
    refine (hbdd q j hj).2.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hw0 _)
  refine hle_prod.trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hw0 _)

private theorem hasDerivAt_stageFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ 1 - χ q * (q : ℂ) ^ (-w))
      ((Real.log q : ℂ) * χ q * (q : ℂ) ^ (-z)) z := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hc : HasDerivAt (fun w : ℂ ↦ (q : ℂ) ^ (-w))
      (-(Complex.log (q : ℂ) * (q : ℂ) ^ (-z))) z := by
    have := (hasDerivAt_neg z).const_cpow (Or.inl hq0)
    simpa [mul_comm, mul_neg] using this
  have hclog : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg q)]
  convert (hasDerivAt_const z (1 : ℂ)).sub (hc.const_mul (χ q)) using 1
  rw [hclog]
  ring

private theorem contDiff_stageFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q) :
    ContDiff ℂ ∞ (fun z : ℂ ↦ 1 - χ q * (q : ℂ) ^ (-z)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have harg : (fun z : ℂ ↦ (q : ℂ) ^ (-z)) =
      fun z : ℂ ↦ Complex.exp (Complex.log (q : ℂ) * (-z)) := funext fun z ↦
    Complex.cpow_def_of_ne_zero hq0 _
  exact contDiff_const.sub (contDiff_const.mul (harg ▸ (contDiff_const.mul contDiff_neg).cexp))

theorem smooth_stageMultiplier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) :
    (∀ q ∈ T, 0 < q) → ContDiff ℂ ∞ (dirichletStageMultiplier χ T) := by
  refine Finset.induction_on T ?_ ?_
  · intro _
    have h0 : dirichletStageMultiplier χ ∅ = fun _ ↦ (1 : ℂ) := by
      ext
      simp [dirichletStageMultiplier]
    rw [h0]
    exact contDiff_const
  · intro q S hqS ih hT
    have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hmul : dirichletStageMultiplier χ (insert q S) =
        fun z : ℂ ↦ (1 - χ q * (q : ℂ) ^ (-z)) * dirichletStageMultiplier χ S z := by
      ext z
      simp [dirichletStageMultiplier, Finset.prod_insert hqS]
    rw [hmul]
    exact (contDiff_stageFactor χ hq0).mul (ih hS)

private theorem iteratedDeriv_insert_stageFactor_vanish {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q) (hq1 : χ q = 1)
    (g : ℂ → ℂ) (hg : ContDiff ℂ ∞ g) (n : ℕ)
    (hvan : ∀ k < n, iteratedDeriv k g 0 = 0) :
    ∀ k < n + 1,
      iteratedDeriv k (fun z : ℂ ↦ (1 - χ q * (q : ℂ) ^ (-z)) * g z) 0 = 0 := by
  let f : ℂ → ℂ := fun z ↦ 1 - χ q * (q : ℂ) ^ (-z)
  have hf : ContDiff ℂ ∞ f := contDiff_stageFactor χ hq
  intro k hk
  change iteratedDeriv k (f * g) 0 = 0
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
  rcases eq_or_ne i 0 with rfl | hi0
  · have hf0 : iteratedDeriv 0 f 0 = 0 := by simp [f, hq1]
    simp [hf0]
  · have hki : k - i < n := by omega
    simp [hvan (k - i) hki]

private theorem iteratedDeriv_insert_stageFactor_lead {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q) (hq1 : χ q = 1)
    (g : ℂ → ℂ) (hg : ContDiff ℂ ∞ g) (n : ℕ)
    (hvan : ∀ k < n, iteratedDeriv k g 0 = 0) :
    iteratedDeriv (n + 1) (fun z : ℂ ↦ (1 - χ q * (q : ℂ) ^ (-z)) * g z) 0 =
      ((n + 1 : ℕ) : ℂ) * (Real.log q : ℂ) * iteratedDeriv n g 0 := by
  let f : ℂ → ℂ := fun z ↦ 1 - χ q * (q : ℂ) ^ (-z)
  have hf : ContDiff ℂ ∞ f := contDiff_stageFactor χ hq
  change iteratedDeriv (n + 1) (f * g) 0 = _
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp)),
    Finset.sum_eq_single_of_mem 1 (Finset.mem_range_succ_iff.mpr (by omega))]
  · have hf1 : iteratedDeriv 1 f 0 = (Real.log q : ℂ) := by
      rw [iteratedDeriv_one, (hasDerivAt_stageFactor χ hq 0).deriv]
      simp [hq1]
    simp only [Nat.choose_one_right, Nat.add_sub_cancel, hf1, Nat.cast_add, Nat.cast_one]
  · intro i hi hi1
    have hi_le : i ≤ n + 1 := Finset.mem_range_succ_iff.mp hi
    rcases eq_or_ne i 0 with rfl | hi0
    · have hf0 : iteratedDeriv 0 f 0 = 0 := by simp [f, hq1]
      simp [hf0]
    · have hsub : n + 1 - i < n := by omega
      simp [hvan (n + 1 - i) hsub]

private theorem iteratedDeriv_insert_nonzeroFactor_vanish {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q)
    (g : ℂ → ℂ) (hg : ContDiff ℂ ∞ g) (n : ℕ)
    (hvan : ∀ k < n, iteratedDeriv k g 0 = 0) :
    ∀ k < n,
      iteratedDeriv k (fun z : ℂ ↦ (1 - χ q * (q : ℂ) ^ (-z)) * g z) 0 = 0 := by
  let f : ℂ → ℂ := fun z ↦ 1 - χ q * (q : ℂ) ^ (-z)
  have hf : ContDiff ℂ ∞ f := contDiff_stageFactor χ hq
  intro k hk
  change iteratedDeriv k (f * g) 0 = 0
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
  have hki : k - i < n := by omega
  simp [hvan (k - i) hki]

private theorem iteratedDeriv_insert_nonzeroFactor_lead {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q)
    (g : ℂ → ℂ) (hg : ContDiff ℂ ∞ g) (n : ℕ)
    (hvan : ∀ k < n, iteratedDeriv k g 0 = 0) :
    iteratedDeriv n (fun z : ℂ ↦ (1 - χ q * (q : ℂ) ^ (-z)) * g z) 0 =
      (1 - χ q) * iteratedDeriv n g 0 := by
  let f : ℂ → ℂ := fun z ↦ 1 - χ q * (q : ℂ) ^ (-z)
  have hf : ContDiff ℂ ∞ f := contDiff_stageFactor χ hq
  change iteratedDeriv n (f * g) 0 = _
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp)),
    Finset.sum_eq_single 0]
  · simp [f]
  · intro i hi hi0
    have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
    have hsub : n - i < n := by omega
    simp [hvan (n - i) hsub]
  · intro h0
    exfalso
    exact h0 (Finset.mem_range_succ_iff.mpr (Nat.zero_le n))

/-- Exact derivatives of `B_T(z) = ∏_{q ∈ T} (1 - χ(q) q^(-z))` at `z = 0`:
all derivatives of order `< b := |{q ∈ T | χ(q) = 1}|` vanish at `0`, and the `b`-th derivative at
`0` is nonzero and equals `b! * (∏_{q ∈ T, χ(q) = 1} log q) * (∏_{q ∈ T, χ(q) ≠ 1} (1 - χ(q)))`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletStageMultiplier_iteratedDeriv_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 < q) :
    let b := dirichletStageZeroOrder χ T
    (∀ k < b, iteratedDeriv k (dirichletStageMultiplier χ T) 0 = 0) ∧
      iteratedDeriv b (dirichletStageMultiplier χ T) 0 =
        (b.factorial : ℂ) * (∏ q ∈ (T.filter fun q : ℕ ↦ χ q = 1), (Real.log q : ℂ)) *
          (∏ q ∈ (T.filter fun q : ℕ ↦ χ q ≠ 1), (1 - χ q)) ∧
      iteratedDeriv b (dirichletStageMultiplier χ T) 0 ≠ 0 := by
  classical
  have hmain : ∀ S : Finset ℕ, (∀ q ∈ S, 1 < q) →
      (∀ k < dirichletStageZeroOrder χ S, iteratedDeriv k (dirichletStageMultiplier χ S) 0 = 0) ∧
      iteratedDeriv (dirichletStageZeroOrder χ S) (dirichletStageMultiplier χ S) 0 =
        ((dirichletStageZeroOrder χ S).factorial : ℂ) *
          (∏ q ∈ (S.filter fun q : ℕ ↦ χ q = 1), (Real.log q : ℂ)) *
          (∏ q ∈ (S.filter fun q : ℕ ↦ χ q ≠ 1), (1 - χ q)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp [dirichletStageZeroOrder, dirichletStageMultiplier]
    · intro q S hqS ih hq_gt
      have hS_gt : ∀ r ∈ S, 1 < r := fun r hr ↦ hq_gt r (Finset.mem_insert_of_mem hr)
      obtain ⟨ih_van, ih_lead⟩ := ih hS_gt
      have hq1 : 1 < q := hq_gt q (Finset.mem_insert_self q S)
      have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq1
      have hg_smooth : ContDiff ℂ ∞ (dirichletStageMultiplier χ S) :=
        smooth_stageMultiplier χ S fun r hr ↦ lt_trans Nat.zero_lt_one (hS_gt r hr)
      have hfun_eq : dirichletStageMultiplier χ (insert q S) =
          fun z : ℂ ↦ (1 - χ q * (q : ℂ) ^ (-z)) * dirichletStageMultiplier χ S z := by
        ext z
        simp [dirichletStageMultiplier, Finset.prod_insert hqS]
      rw [hfun_eq]
      by_cases hχq : χ q = 1
      · have hord : dirichletStageZeroOrder χ (insert q S) = dirichletStageZeroOrder χ S + 1 := by
          unfold dirichletStageZeroOrder
          simp only [Finset.filter_insert, hχq, ↓reduceIte]
          rw [Finset.card_insert_of_notMem (by simp [hqS])]
        have hf1 : (Finset.filter (fun r : ℕ ↦ χ r = 1) (insert q S)) =
            insert q (Finset.filter (fun r : ℕ ↦ χ r = 1) S) := by
          simp only [Finset.filter_insert, hχq, ↓reduceIte]
        have hf2 : (Finset.filter (fun r : ℕ ↦ χ r ≠ 1) (insert q S)) =
            Finset.filter (fun r : ℕ ↦ χ r ≠ 1) S := by
          simp only [Finset.filter_insert, ne_eq, hχq, not_true_eq_false, ↓reduceIte]
        rw [hord]
        refine ⟨iteratedDeriv_insert_stageFactor_vanish χ hq0 hχq _ hg_smooth _ ih_van, ?_⟩
        rw [iteratedDeriv_insert_stageFactor_lead χ hq0 hχq _ hg_smooth _ ih_van, ih_lead,
          hf1, hf2, Finset.prod_insert (by simp [hqS]), Nat.factorial_succ]
        push_cast
        ring
      · have hord : dirichletStageZeroOrder χ (insert q S) = dirichletStageZeroOrder χ S := by
          unfold dirichletStageZeroOrder
          simp only [Finset.filter_insert, hχq, ↓reduceIte]
        have hf1 : (Finset.filter (fun r : ℕ ↦ χ r = 1) (insert q S)) =
            Finset.filter (fun r : ℕ ↦ χ r = 1) S := by
          simp only [Finset.filter_insert, hχq, ↓reduceIte]
        have hf2 : (Finset.filter (fun r : ℕ ↦ χ r ≠ 1) (insert q S)) =
            insert q (Finset.filter (fun r : ℕ ↦ χ r ≠ 1) S) := by
          simp only [Finset.filter_insert, ne_eq, hχq, not_false_eq_true, ↓reduceIte]
        rw [hord]
        refine ⟨iteratedDeriv_insert_nonzeroFactor_vanish χ hq0 _ hg_smooth _ ih_van, ?_⟩
        rw [iteratedDeriv_insert_nonzeroFactor_lead χ hq0 _ hg_smooth _ ih_van, ih_lead,
          hf1, hf2, Finset.prod_insert (by simp [hqS])]
        ring
  obtain ⟨hvan, hlead⟩ := hmain T hT
  refine ⟨hvan, hlead, ?_⟩
  rw [hlead]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  · rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact Complex.ofReal_ne_zero.mpr
      (Real.log_pos (by exact_mod_cast hT q (Finset.mem_filter.mp hq).1)).ne'
  · rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hq).2)

end AnalyticAndArithmeticBounds

/-! ### Section 2: Twisted Poisson summation, fixed-box support, and Mellin coordinates -/

section TwistedPoissonAndMellin

/-- Continuous linear dilation `x ↦ c * x` on `ℝ` for `c ≠ 0`. -/
def realScaleCLE (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun := fun x ↦ c * x
  invFun := fun x ↦ c⁻¹ * x
  left_inv := fun x ↦ by simp [← mul_assoc, inv_mul_cancel₀ hc]
  right_inv := fun x ↦ by simp [← mul_assoc, mul_inv_cancel₀ hc]
  map_add' := fun x y ↦ mul_add c x y
  map_smul' := fun r x ↦ by simp only [smul_eq_mul, RingHom.id_apply]; ring
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- Dilation on Schwartz functions `𝓢(ℝ, ℂ)` sending `f` to `x ↦ f (c * x)`. -/
def schwartzScale (c : ℝ) (hc : c ≠ 0) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realScaleCLE c hc)

@[simp]
theorem schwartzScale_apply (c : ℝ) (hc : c ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzScale c hc f x = f (c * x) := rfl

theorem fourier_schwartzScale (c : ℝ) (hc : c ≠ 0) (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    (𝓕 (schwartzScale c hc f)) w = ((|c|⁻¹ : ℝ) : ℂ) * (𝓕 f) (w / c) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [schwartzScale_apply, smul_eq_mul]
  have heq : (fun v : ℝ ↦ Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) * f (c * v)) =
      fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * (c * v) * (w / c)) * Complex.I) * f (c * v) := by
    ext v
    have harg : -2 * Real.pi * v * w = -2 * Real.pi * (c * v) * (w / c) := by
      field_simp [hc]
    rw [harg]
  rw [heq, MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ ↦ Complex.exp (↑(-2 * Real.pi * y * (w / c)) * Complex.I) * f y) c]
  simp [Complex.real_smul]

/-- Parity condition `f (-x) = χ (-1) * f x` matched to a Dirichlet character `χ`. -/
def HasDirichletParity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ x : ℝ, f (-x) = χ (-1) * f x

theorem dirichlet_eval_neg_one_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ (-1) * χ (-1) = 1 := by
  rw [← map_mul]
  norm_num

theorem dirichlet_inv_eval_neg_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  have hinv : Ring.inverse (-1 : ZMod N) = -1 := by
    calc Ring.inverse (-1 : ZMod N) = ((-1 : ZMod N) * (-1)) * Ring.inverse (-1 : ZMod N) := by
          rw [neg_one_mul, neg_neg, one_mul]
      _ = (-1 : ZMod N) * ((-1 : ZMod N) * Ring.inverse (-1 : ZMod N)) := mul_assoc _ _ _
      _ = (-1 : ZMod N) * 1 := by rw [Ring.mul_inverse_cancel _ isUnit_one.neg]
      _ = -1 := mul_one _
  rw [hinv]

theorem HasDirichletParity.fourier {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {f : 𝓢(ℝ, ℂ)} (hf : HasDirichletParity χ f) (ξ : ℝ) :
    (𝓕 f) (-ξ) = χ (-1) * (𝓕 f) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have hsub : (fun v : ℝ ↦ Complex.exp (↑(-2 * Real.pi * v * (-ξ)) * Complex.I) • f v) =
      fun v : ℝ ↦ χ (-1) * (Complex.exp (↑(-2 * Real.pi * (-v) * ξ) * Complex.I) • f (-v)) := by
    ext v
    have hfv : f v = χ (-1) * f (-v) := by simpa only [neg_neg] using hf (-v)
    rw [hfv]
    have hexp : (-2 : ℝ) * Real.pi * v * (-ξ) = (-2) * Real.pi * (-v) * ξ := by ring
    simp only [smul_eq_mul, hexp]
    ring
  rw [hsub, integral_const_mul, ← integral_neg_eq_self
    (fun v : ℝ ↦ Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • f v)]

/-- A real Schwartz test `f` of parity `χ(-1)` whose Fourier transform is supported in `[-X, X]`. -/
def IsDirichletFixedBoxTest {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ)
    (f : 𝓢(ℝ, ℂ)) : Prop :=
  HasDirichletParity χ f ∧ tsupport (fun x : ℝ ↦ (𝓕 f) x) ⊆ Set.Icc (-X) X

theorem IsDirichletFixedBoxTest.mono {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {X Y : ℝ} (hXY : X ≤ Y) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) :
    IsDirichletFixedBoxTest χ Y f :=
  ⟨hf.1, hf.2.trans (Set.Icc_subset_Icc (neg_le_neg hXY) hXY)⟩

theorem IsDirichletFixedBoxTest.sub {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {X : ℝ} {f g : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    (hg : IsDirichletFixedBoxTest χ X g) : IsDirichletFixedBoxTest χ X (f - g) := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · simp [hf.1 x, hg.1 x, mul_sub]
  · have hsum : (fun x : ℝ ↦ (𝓕 (f - g)) x) =
        (fun x : ℝ ↦ (𝓕 f) x) - (fun x : ℝ ↦ (𝓕 g) x) := by
      ext x
      simp
    rw [hsum]
    exact (tsupport_sub (fun x : ℝ ↦ (𝓕 f) x) (fun x : ℝ ↦ (𝓕 g) x)).trans
      (Set.union_subset hf.2 hg.2)

theorem IsDirichletFixedBoxTest.smul {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {X : ℝ} (c : ℂ) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) :
    IsDirichletFixedBoxTest χ X (c • f) := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · simp [hf.1 x, mul_left_comm]
  · have hs : (fun x : ℝ ↦ (𝓕 (c • f)) x) = (fun _ : ℝ ↦ c) • (fun x : ℝ ↦ (𝓕 f) x) := by
      ext x
      simp
    rw [hs]
    exact (tsupport_smul_subset_right (fun _ : ℝ ↦ c) (fun x : ℝ ↦ (𝓕 f) x)).trans hf.2

/-- Twisted radial theta series `Θ_χ(f, r) = ∑' m : ℤ, χ(m) f(m r)`. -/
def twistedRadialTheta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (f : 𝓢(ℝ, ℂ)) (r : ℝ) : ℂ :=
  ∑' m : ℤ, χ (m : ZMod N) * f (m * r)

/-- Half-twisted logarithmic profile `U_χ(f, x) = e^(x/2) Θ_χ(f, e^x)`. -/
def twistedHalfLogProfile {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * twistedRadialTheta χ f (Real.exp x)

theorem norm_dirichletChar_le_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a : ZMod N) : ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · have hpow : χ a ^ orderOf χ = 1 := by
      have hp : ∀ k : ℕ, (χ ^ k) a = χ a ^ k := fun k ↦ by
        induction k with
        | zero => simp [pow_zero, MulChar.one_apply ha]
        | succ k ih => simp [pow_succ, ih]
      rw [← hp (orderOf χ), pow_orderOf_eq_one, MulChar.one_apply ha]
    exact (Complex.norm_eq_one_of_pow_eq_one hpow χ.orderOf_pos.ne').le
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    exact zero_le_one

theorem summable_twistedRadialTheta {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (f : 𝓢(ℝ, ℂ)) {r : ℝ} (hr : r ≠ 0) :
    Summable (fun m : ℤ ↦ χ (m : ZMod N) * f (m * r)) := by
  let g := schwartzScale r hr f
  have hbig : (fun m : ℤ ↦ ‖χ (m : ZMod N) * f (m * r)‖) =O[cofinite]
      (fun m : ℤ ↦ |(m : ℝ)| ^ (-2 : ℝ)) := by
    have hg₀ := (g.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite
    have hg : (fun m : ℤ ↦ ‖g (m : ℝ)‖) =O[cofinite] (fun m : ℤ ↦ |(m : ℝ)| ^ (-2 : ℝ)) :=
      hg₀.congr (fun _ ↦ rfl) (fun m ↦ by simp [Real.norm_eq_abs])
    refine Asymptotics.IsBigO.trans ?_ hg
    refine Asymptotics.isBigO_of_le _ fun m ↦ ?_
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _), norm_mul]
    calc ‖χ (m : ZMod N)‖ * ‖f (m * r)‖
        ≤ 1 * ‖f (m * r)‖ := mul_le_mul_of_nonneg_right (norm_dirichletChar_le_one χ m) (norm_nonneg _)
      _ = ‖g (m : ℝ)‖ := by simp [g, mul_comm]
  exact (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hbig).of_norm

private theorem summable_twistedFourier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (f : 𝓢(ℝ, ℂ)) {r : ℝ} (hr : 0 < r) :
    Summable (fun m : ℤ ↦ χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * r))) := by
  have hNr : ((N : ℝ) * r)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)) hr.ne')
  let g := schwartzScale (((N : ℝ) * r)⁻¹) hNr (𝓕 f)
  have hbig : (fun m : ℤ ↦ ‖χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * r))‖) =O[cofinite]
      (fun m : ℤ ↦ |(m : ℝ)| ^ (-2 : ℝ)) := by
    have hg₀ := (g.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite
    have hg : (fun m : ℤ ↦ ‖g (m : ℝ)‖) =O[cofinite] (fun m : ℤ ↦ |(m : ℝ)| ^ (-2 : ℝ)) :=
      hg₀.congr (fun _ ↦ rfl) (fun m ↦ by simp [Real.norm_eq_abs])
    refine Asymptotics.IsBigO.trans ?_ hg
    refine Asymptotics.isBigO_of_le _ fun m ↦ ?_
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _), norm_mul]
    calc ‖χ⁻¹ (m : ZMod N)‖ * ‖(𝓕 f) ((m : ℝ) / ((N : ℝ) * r))‖
        ≤ 1 * ‖(𝓕 f) ((m : ℝ) / ((N : ℝ) * r))‖ :=
          mul_le_mul_of_nonneg_right (norm_dirichletChar_le_one χ⁻¹ m) (norm_nonneg _)
      _ = ‖g (m : ℝ)‖ := by simp [g, div_eq_inv_mul]
  exact (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hbig).of_norm

private def modResEquiv (N : ℕ) (hNpos : 0 < N) : Fin N × ℤ ≃ ℤ where
  toFun := fun p ↦ (p.1 : ℤ) + (N : ℤ) * p.2
  invFun := fun m ↦ (⟨(m % (N : ℤ)).toNat, by
    have h1 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg m (by exact_mod_cast hNpos.ne')
    have h2 : m % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hNpos)
    omega⟩, m / (N : ℤ))
  left_inv := fun ⟨a, k⟩ ↦ by
    ext
    · have ha : 0 ≤ (a : ℤ) ∧ (a : ℤ) < (N : ℤ) :=
        ⟨Int.natCast_nonneg _, by exact_mod_cast a.isLt⟩
      have hmod : ((a : ℤ) + (N : ℤ) * k) % (N : ℤ) = (a : ℤ) := by
        rw [add_comm, Int.mul_add_emod_self_left, Int.emod_eq_of_lt ha.1 ha.2]
      simp [hmod]
    · have hdiv : ((a : ℤ) + (N : ℤ) * k) / (N : ℤ) = k := by
        rw [add_comm, Int.mul_add_ediv_left _ _ (by exact_mod_cast hNpos.ne'),
          Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast a.isLt), add_zero]
      simp [hdiv]
  right_inv := fun m ↦ by
    have h1 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg m (by exact_mod_cast hNpos.ne')
    simp only [Int.toNat_of_nonneg h1]
    exact Int.emod_add_mul_ediv m N

private theorem sum_fin_fourier_eq_gaussSum {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (m : ℤ) :
    (∑ a : Fin N, χ ((a : ℤ) : ZMod N) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle)) =
      χ⁻¹ (m : ZMod N) * gaussSum χ ZMod.stdAddChar := by
  let eqv : Fin N ≃ ZMod N :=
    { toFun := fun a ↦ (a.val : ZMod N)
      invFun := fun x ↦ ⟨x.val, ZMod.val_lt x⟩
      left_inv := fun a ↦ Fin.ext (ZMod.val_natCast_of_lt a.isLt)
      right_inv := fun x ↦ ZMod.natCast_zmod_val x }
  have heqv_sum : (∑ a : Fin N, χ ((a : ℤ) : ZMod N) *
        fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle)) =
      ∑ x : ZMod N, χ x * ZMod.stdAddChar ((m : ZMod N) * x) := by
    refine Fintype.sum_equiv eqv _ _ fun a ↦ ?_
    have hxa : ((a : ℤ) : ZMod N) = eqv a := by
      dsimp [eqv]
      norm_cast
    rw [hxa]
    congr 1
    rw [fourier_coe_apply, Complex.ofReal_one, div_one]
    have harg : (eqv a : ZMod N) = ((a.val : ℤ) : ZMod N) := by
      dsimp [eqv]; norm_cast
    rw [harg, ← Int.cast_mul, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [heqv_sum]
  simpa [gaussSum, AddChar.mulShift_apply] using
    gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (m : ZMod N)

private theorem twistedRadialTheta_split {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (f : 𝓢(ℝ, ℂ)) {r : ℝ} (hr : 0 < r)
    (hNr_ne : (N : ℝ) * r ≠ 0) :
    twistedRadialTheta χ f r =
      ∑ a : Fin N, χ ((a : ℤ) : ZMod N) *
        ∑' k : ℤ, schwartzScale ((N : ℝ) * r) hNr_ne f ((a : ℝ) / N + k) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  let e : Fin N × ℤ ≃ ℤ := modResEquiv N hNpos
  have hsum_all := summable_twistedRadialTheta χ f hr.ne'
  have hsum_prod : Summable (fun p : Fin N × ℤ ↦
      χ ((e p : ℤ) : ZMod N) * f ((e p : ℝ) * r)) :=
    (e.summable_iff).mpr hsum_all
  rw [twistedRadialTheta, ← e.tsum_eq (fun m ↦ χ (m : ZMod N) * f (m * r)),
    Summable.tsum_prod' hsum_prod (fun a ↦ hsum_prod.comp_injective fun k₁ k₂ h ↦ by simpa using h),
    tsum_fintype]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  have heval : χ ((e (a, k) : ℤ) : ZMod N) = χ ((a : ℤ) : ZMod N) := by
    dsimp [e, modResEquiv]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  have harg : (e (a, k) : ℝ) * r = (N : ℝ) * r * ((a : ℝ) / N + k) := by
    dsimp [e, modResEquiv]
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
    push_cast
    field_simp [hNne]
  rw [heval, harg, schwartzScale_apply]

private theorem twisted_poisson_sum_swap {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (g : 𝓢(ℝ, ℂ)) :
    (∑ a : Fin N, χ ((a : ℤ) : ZMod N) *
        ∑' m : ℤ, (𝓕 g) (m : ℝ) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle)) =
      ∑' m : ℤ, (𝓕 g) (m : ℝ) *
        ∑ a : Fin N, χ ((a : ℤ) : ZMod N) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle) := by
  have hsum_fourier_a (a : Fin N) :
      Summable (fun m : ℤ ↦ χ ((a : ℤ) : ZMod N) *
        ((𝓕 g) (m : ℝ) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle))) := by
    have hg₀ := ((𝓕 g).isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite
    have hbig : (fun m : ℤ ↦ ‖(𝓕 g) (m : ℝ)‖) =O[cofinite] (fun m : ℤ ↦ |(m : ℝ)| ^ (-2 : ℝ)) :=
      hg₀.congr (fun _ ↦ rfl) (fun m ↦ by simp [Real.norm_eq_abs])
    have hgf : Summable (fun m : ℤ ↦ ‖(𝓕 g) (m : ℝ)‖) :=
      summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hbig
    refine (hgf.mul_left ‖χ ((a : ℤ) : ZMod N)‖).of_norm_bounded fun m ↦ ?_
    rw [norm_mul, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  calc (∑ a : Fin N, χ ((a : ℤ) : ZMod N) *
          ∑' m : ℤ, (𝓕 g) (m : ℝ) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle))
      = ∑ a : Fin N, ∑' m : ℤ, χ ((a : ℤ) : ZMod N) *
          ((𝓕 g) (m : ℝ) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle)) :=
        Finset.sum_congr rfl fun a _ ↦ tsum_mul_left.symm
    _ = ∑' m : ℤ, ∑ a : Fin N, χ ((a : ℤ) : ZMod N) *
          ((𝓕 g) (m : ℝ) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle)) :=
        (Summable.tsum_finsetSum fun a _ ↦ hsum_fourier_a a).symm
    _ = ∑' m : ℤ, (𝓕 g) (m : ℝ) *
          ∑ a : Fin N, χ ((a : ℤ) : ZMod N) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle) := by
        refine tsum_congr fun m ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        ring

/-- Twisted Poisson summation on `ℝ` for a primitive Dirichlet character `χ` of conductor `N`.
In particular `m = 0` vanishes automatically when `1 < N`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem twisted_poisson_summation {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) {r : ℝ} (hr : 0 < r) :
    twistedRadialTheta χ f r =
      (gaussSum χ ZMod.stdAddChar / ((N : ℂ) * (r : ℂ))) *
        ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * r)) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr_pos : 0 < (N : ℝ) * r := mul_pos (Nat.cast_pos.mpr hNpos) hr
  have hNr_ne : (N : ℝ) * r ≠ 0 := hNr_pos.ne'
  let g : 𝓢(ℝ, ℂ) := schwartzScale ((N : ℝ) * r) hNr_ne f
  have hpoiss (a : Fin N) :
      ∑' k : ℤ, g ((a : ℝ) / N + k) =
        ∑' m : ℤ, (𝓕 g) m * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle) :=
    SchwartzMap.tsum_eq_tsum_fourier g ((a : ℝ) / N)
  have hsplit : twistedRadialTheta χ f r =
      ∑ a : Fin N, χ ((a : ℤ) : ZMod N) * ∑' k : ℤ, g ((a : ℝ) / N + k) :=
    twistedRadialTheta_split χ f hr hNr_ne
  rw [hsplit]
  simp_rw [hpoiss]
  rw [twisted_poisson_sum_swap χ g]
  have hterm (m : ℤ) :
      (𝓕 g) (m : ℝ) * ∑ a : Fin N, χ ((a : ℤ) : ZMod N) * fourier m (((a : ℝ) / N : ℝ) : UnitAddCircle) =
        (gaussSum χ ZMod.stdAddChar / ((N : ℂ) * (r : ℂ))) *
          (χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * r))) := by
    rw [sum_fin_fourier_eq_gaussSum hχ m]
    dsimp [g]
    rw [fourier_schwartzScale _ hNr_ne f m, abs_of_pos hNr_pos]
    push_cast
    ring
  simp_rw [hterm]
  exact tsum_mul_left

theorem dirichletChar_inv_zero_of_one_lt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) : χ⁻¹ (0 : ZMod N) = 0 := by
  apply MulChar.map_nonunit
  rintro ⟨u, hu⟩
  have h1 : (u : ZMod N) * (u⁻¹ : (ZMod N)ˣ) = 1 := u.mul_inv
  have hne : (1 : ZMod N) ≠ 0 := by
    have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr (by omega)
    exact one_ne_zero
  rw [hu, zero_mul] at h1
  exact hne h1.symm

/-- Paper: (11.3.1.3), p. 494.
For a fixed-box test `f` of parity `χ(-1)` and Fourier support in `[-X, X]` (`X > 0`),
the half-twisted profile `U_χ(f, x)` vanishes identically for `x < -Real.log (N * X)`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_support_lower_bound {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    {x : ℝ} (hx : x < -Real.log ((N : ℝ) * X)) :
    twistedHalfLogProfile χ f x = 0 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNX : 0 < (N : ℝ) * X := mul_pos hNpos hX
  have hexp_lt : Real.exp x < ((N : ℝ) * X)⁻¹ := by
    calc Real.exp x < Real.exp (-Real.log ((N : ℝ) * X)) := Real.exp_lt_exp.mpr hx
      _ = (Real.exp (Real.log ((N : ℝ) * X)))⁻¹ := Real.exp_neg _
      _ = ((N : ℝ) * X)⁻¹ := by rw [Real.exp_log hNX]
  rw [twistedHalfLogProfile, twisted_poisson_summation hχ f (Real.exp_pos x)]
  have hterm (m : ℤ) : χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp x)) = 0 := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp [dirichletChar_inv_zero_of_one_lt χ hN]
    · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      have hden_pos : 0 < (N : ℝ) * Real.exp x := mul_pos hNpos (Real.exp_pos x)
      have hgt : X < |(m : ℝ) / ((N : ℝ) * Real.exp x)| := by
        rw [abs_div, abs_of_pos hden_pos]
        have hNx : (N : ℝ) * Real.exp x < X⁻¹ := by
          have := mul_lt_mul_of_pos_left hexp_lt hNpos
          rw [mul_inv_rev, mul_comm X⁻¹ _, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at this
          exact this
        have hlt1 : X < ((N : ℝ) * Real.exp x)⁻¹ :=
          (lt_inv_comm₀ hX hden_pos).mpr hNx
        exact hlt1.trans_le ((le_div_iff₀ hden_pos).mpr (by
          calc ((N : ℝ) * Real.exp x)⁻¹ * ((N : ℝ) * Real.exp x) = 1 := inv_mul_cancel₀ hden_pos.ne'
            _ ≤ |(m : ℝ)| := hm1))
      have hnot : (m : ℝ) / ((N : ℝ) * Real.exp x) ∉ tsupport (fun y : ℝ ↦ (𝓕 f) y) := fun hmem ↦
        hgt.not_ge (abs_le.mpr (hf.2 hmem))
      have hval0 : (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp x)) = 0 := by
        by_contra hne
        exact hnot (subset_tsupport _ hne)
      simp [hval0]
  simp [hterm]

/-- Forward logarithmic dilation operator `D_q U(x) = q ^ (-1/2) * U (x + log q)` (`0` when `q = 0`). -/
def halfTwistLogDilate (q : ℕ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun := fun U x ↦ if q = 0 then 0 else ((q : ℂ) ^ (-(1 / 2 : ℂ))) * U (x + Real.log q)
  map_add' := fun U V ↦ by ext x; split_ifs <;> simp [mul_add]
  map_smul' := fun c U ↦ by ext x; split_ifs <;> simp [mul_left_comm]

private theorem halfTwistLogDilate_comm (q r : ℕ) :
    (halfTwistLogDilate q).comp (halfTwistLogDilate r) =
      (halfTwistLogDilate r).comp (halfTwistLogDilate q) := by
  ext U x
  simp only [LinearMap.comp_apply, halfTwistLogDilate, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hq : q = 0 <;> by_cases hr : r = 0
  · simp [hq, hr]
  · simp [hq, hr]
  · simp [hq, hr]
  · simp only [hq, ↓reduceIte, hr]
    rw [add_assoc, add_comm (Real.log q) (Real.log r), ← add_assoc]
    ring

/-- Single-prime depletion step `I - χ(q) D_q` on logarithmic profiles `ℝ → ℂ`. -/
def depleteStepFun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (q : ℕ) :
    (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  LinearMap.id - χ (q : ZMod N) • halfTwistLogDilate q

theorem depleteStepFun_comm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (q r : ℕ) :
    Commute (depleteStepFun χ q) (depleteStepFun χ r) := by
  show (depleteStepFun χ q).comp (depleteStepFun χ r) =
    (depleteStepFun χ r).comp (depleteStepFun χ q)
  ext U x
  by_cases hq : q = 0 <;> by_cases hr : r = 0
  · simp [depleteStepFun, halfTwistLogDilate, hq, hr]
  · simp [depleteStepFun, halfTwistLogDilate, hq, hr]
  · simp [depleteStepFun, halfTwistLogDilate, hq, hr]
  · simp only [LinearMap.comp_apply, depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, halfTwistLogDilate, LinearMap.coe_mk, AddHom.coe_mk,
      hq, ↓reduceIte, hr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show x + Real.log r + Real.log q = x + Real.log q + Real.log r by ring]
    ring

/-- Depletion operator `∏_{q ∈ T} (I - χ(q) D_q)` on logarithmic profiles `ℝ → ℂ`. -/
def dirichletDeplete {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : Finset ℕ) :
    (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  T.noncommProd (depleteStepFun χ) fun q _ r _ _ ↦ depleteStepFun_comm χ q r

@[simp]
theorem dirichletDeplete_empty {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    dirichletDeplete χ ∅ = LinearMap.id :=
  Finset.noncommProd_empty _ _

theorem dirichletDeplete_insert {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {q : ℕ} {T : Finset ℕ} (hq : q ∉ T) :
    dirichletDeplete χ (insert q T) =
      (depleteStepFun χ q).comp (dirichletDeplete χ T) :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hq

/-- Single-prime depletion step `I - χ(q) · dilate_q` on Schwartz tests `𝓢(ℝ, ℂ)`. -/
def testDepleteStep {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (q : ℕ) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  if hq : q = 0 then ContinuousLinearMap.id ℂ _
  else ContinuousLinearMap.id ℂ _ - χ (q : ZMod N) • schwartzScale (q : ℝ) (Nat.cast_ne_zero.mpr hq)

theorem testDepleteStep_comm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (q r : ℕ) :
    Commute (testDepleteStep χ q) (testDepleteStep χ r) := by
  show (testDepleteStep χ q).comp (testDepleteStep χ r) =
    (testDepleteStep χ r).comp (testDepleteStep χ q)
  by_cases hq : q = 0 <;> by_cases hr : r = 0
  · simp [testDepleteStep, hq, hr]
  · simp [testDepleteStep, hq, hr]
  · simp [testDepleteStep, hq, hr]
  · simp only [testDepleteStep, hq, ↓reduceDIte, hr]
    ext f x
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, smul_apply, schwartzScale_apply,
      smul_eq_mul]
    ring_nf

/-- Depletion operator `∏_{q ∈ T} (I - χ(q) · dilate_q)` on Schwartz tests `𝓢(ℝ, ℂ)`. -/
def dirichletTestDeplete {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : Finset ℕ) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  T.noncommProd (testDepleteStep χ) fun q _ r _ _ ↦ testDepleteStep_comm χ q r

@[simp]
theorem dirichletTestDeplete_empty {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    dirichletTestDeplete χ ∅ = ContinuousLinearMap.id ℂ _ :=
  Finset.noncommProd_empty _ _

theorem dirichletTestDeplete_insert {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {q : ℕ} {T : Finset ℕ} (hq : q ∉ T) :
    dirichletTestDeplete χ (insert q T) =
      (testDepleteStep χ q).comp (dirichletTestDeplete χ T) :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hq

theorem twistedHalfLogProfile_schwartzScale {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q) (f : 𝓢(ℝ, ℂ)) :
    twistedHalfLogProfile χ (schwartzScale (q : ℝ) (Nat.cast_ne_zero.mpr hq.ne') f) =
      halfTwistLogDilate q (twistedHalfLogProfile χ f) := by
  ext x
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [twistedHalfLogProfile, twistedRadialTheta, halfTwistLogDilate, hq.ne', ↓reduceIte,
    LinearMap.coe_mk, AddHom.coe_mk, schwartzScale_apply]
  have hcpow : ((q : ℂ) ^ (-(1 / 2 : ℂ))) = (((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast,
      show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hqp.le]
  have hexp_eq : Real.exp (x / 2) = (q : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp ((x + Real.log q) / 2) := by
    rw [add_div, Real.exp_add]
    have hlogq : Real.exp (Real.log q / 2) = (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hqp, mul_one_div]
    rw [hlogq, mul_comm (Real.exp (x / 2)), ← mul_assoc, ← Real.rpow_add hqp]
    simp
  have hsum_eq : (∑' m : ℤ, χ (m : ZMod N) * f ((q : ℝ) * (m * Real.exp x))) =
      ∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp (x + Real.log q)) := by
    refine tsum_congr fun m ↦ ?_
    rw [Real.exp_add, Real.exp_log hqp]
    ring_nf
  rw [hcpow, hexp_eq, hsum_eq, Complex.ofReal_mul, mul_assoc]

theorem twistedHalfLogProfile_sub {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (f g : 𝓢(ℝ, ℂ)) :
    twistedHalfLogProfile χ (f - g) = twistedHalfLogProfile χ f - twistedHalfLogProfile χ g := by
  ext x
  simp only [twistedHalfLogProfile, twistedRadialTheta, sub_apply,
    mul_sub]
  rw [Summable.tsum_sub (summable_twistedRadialTheta χ f (Real.exp_pos x).ne')
    (summable_twistedRadialTheta χ g (Real.exp_pos x).ne'), mul_sub]
  rfl

theorem twistedHalfLogProfile_smul {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    twistedHalfLogProfile χ (c • f) = c • twistedHalfLogProfile χ f := by
  ext x
  simp only [twistedHalfLogProfile, twistedRadialTheta, Pi.smul_apply, smul_apply,
    smul_eq_mul]
  have hlin : (∑' m : ℤ, χ (m : ZMod N) * (c * f (m * Real.exp x))) =
      c * ∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp x) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun m ↦ ?_
    ring
  rw [hlin]
  ring

/-- `twistedHalfLogProfile` intertwines `dirichletTestDeplete` with `dirichletDeplete`. -/
theorem twistedHalfLogProfile_dirichletTestDeplete {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q) (f : 𝓢(ℝ, ℂ)) :
    twistedHalfLogProfile χ (dirichletTestDeplete χ T f) =
      dirichletDeplete χ T (twistedHalfLogProfile χ f) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert q S hqS ih =>
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    rw [dirichletTestDeplete_insert χ hqS, dirichletDeplete_insert χ hqS,
      ContinuousLinearMap.comp_apply, LinearMap.comp_apply]
    simp only [testDepleteStep, hq0.ne', ↓reduceDIte, sub_apply,
      ContinuousLinearMap.id_apply, smul_apply,
      depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
    rw [twistedHalfLogProfile_sub, twistedHalfLogProfile_smul,
      twistedHalfLogProfile_schwartzScale χ hq0, ih hS]

/-- `testDepleteStep` scales the Fourier box radius by `q`. -/
theorem isDirichletFixedBoxTest_testDepleteStep {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 ≤ R)
    {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ R f) :
    IsDirichletFixedBoxTest χ ((q : ℝ) * R) (testDepleteStep χ q f) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := hqp.ne'
  have hstep : testDepleteStep χ q f =
      f - χ (q : ZMod N) • schwartzScale (q : ℝ) hqne f := by
    simp [testDepleteStep, hq.ne']
  rw [hstep]
  exact IsDirichletFixedBoxTest.sub (hf.mono (le_mul_of_one_le_left hR (by exact_mod_cast hq)))
    (IsDirichletFixedBoxTest.smul _ ⟨fun x ↦ by simp [hf.1 (q * x), mul_neg], by
      have hfs : (fun x : ℝ ↦ (𝓕 (schwartzScale (q : ℝ) hqne f)) x) =
          fun x : ℝ ↦ ((|q|⁻¹ : ℝ) : ℂ) * (𝓕 f) (x / q) :=
        funext (fourier_schwartzScale (q : ℝ) hqne f)
      rw [hfs]
      refine (closure_mono ?_).trans isClosed_Icc.closure_eq.subset
      intro x hx
      simp only [Function.mem_support, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, inv_eq_zero,
        abs_eq_zero, hqne, false_or] at hx
      have hmem := hf.2 (subset_tsupport _ hx)
      rw [Set.mem_Icc] at hmem ⊢
      constructor <;> [nlinarith [hmem.1, div_mul_cancel₀ x hqne];
        nlinarith [hmem.2, div_mul_cancel₀ x hqne]]⟩)

/-- A box-`X / ∏_{q ∈ T} q` test maps under `dirichletTestDeplete χ T` into the fixed outer box `X`. -/
theorem isDirichletFixedBoxTest_dirichletTestDeplete {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {X : ℝ} (hX : 0 ≤ X) {f₀ : 𝓢(ℝ, ℂ)}
    (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀) :
    IsDirichletFixedBoxTest χ X (dirichletTestDeplete χ T f₀) := by
  induction T using Finset.induction_on generalizing X with
  | empty => simpa using hf₀
  | insert q S hqS ih =>
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    have hqp : (0 : ℝ) < q := by exact_mod_cast hq0
    have hdiv : X / ∏ r ∈ insert q S, (r : ℝ) = (X / q) / ∏ r ∈ S, (r : ℝ) := by
      rw [Finset.prod_insert hqS, ← div_div, div_right_comm]
    have hfS : IsDirichletFixedBoxTest χ (X / q) (dirichletTestDeplete χ S f₀) :=
      ih hS (div_nonneg hX hqp.le) (by rwa [← hdiv])
    rw [dirichletTestDeplete_insert χ hqS, ContinuousLinearMap.comp_apply]
    have hstep := isDirichletFixedBoxTest_testDepleteStep hq0 (div_nonneg hX hqp.le) hfS
    rwa [mul_div_cancel₀ _ hqp.ne'] at hstep

end TwistedPoissonAndMellin

end RiemannMasullo.Isolated
