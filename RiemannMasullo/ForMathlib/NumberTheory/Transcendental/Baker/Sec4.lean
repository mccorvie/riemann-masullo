module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.ExpPoly
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Auxiliary
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # The final step of Baker, Ch. 3, sec. 4: an integer relation

Ported from HOL Light, Baker/sec4.ml (jrh13/hol-light, commit 1a0c0e6).

If the auxiliary exponential polynomial
`∑_(a,b,mu) p(a,b,mu) B_{a,b}(l/k) exp(l (∑_r mu_r lg_r) / k)` (`B_{a,b} = feldmanBasis h a b`,
`a < h`, `b ≤ L`, `0 ≤ mu_r ≤ L`) vanishes at `l = 0, …, h (L+2) (L+1)^n - 1` and `p` is not
identically zero, then two distinct nodes `exp((∑_r mu_r lg_r) / k)` coincide, and if moreover
`L (|lg_1| + ⋯ + |lg_n|) < 2 π k` there are integers `b_r`, `|b_r| ≤ L`, not all zero, with
`b_1 lg_1 + ⋯ + b_n lg_n = 0` (Baker, *Transcendental Number Theory*, Ch. 3, sec. 4).

Products and quotients are bracketed as HOL Light parses them. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- HOL Light: Baker/sec4.ml, COMPLEX_POLYFUN_VSUM. A finite sum of polynomial functions of degree
at most `d` is a polynomial function of degree at most `d`.

Deviation: `s` is a `Finset` (no `FINITE s`). -/
theorem complex_polyfun_vsum {A : Type*} (s : Finset A) (f : A → ℂ → ℂ) (d : ℕ)
    (hf : ∀ i ∈ s, ∃ c : ℕ → ℂ, ∀ z, f i z = ∑ t ∈ Finset.range (d + 1), c t * z ^ t) :
    ∃ c : ℕ → ℂ, ∀ z, ∑ i ∈ s, f i z = ∑ t ∈ Finset.range (d + 1), c t * z ^ t := by
  choose! c hc using hf
  refine ⟨fun t => ∑ i ∈ s, c i t, fun z => ?_⟩
  rw [Finset.sum_congr rfl fun i hi => hc i hi z, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (Finset.sum_mul _ _ _).symm

/-- HOL Light: Baker/sec4.ml, COMPLEX_POLYFUN_SCALE_ARG. If `f` is a polynomial function of degree
at most `d ≤ D`, then so is `x ↦ u * f (x / w)`, with degree bound `D`.

Deviation: hypotheses are curried. -/
theorem complex_polyfun_scale_arg (f : ℂ → ℂ) (e : ℕ → ℂ) (d D : ℕ) (u w : ℂ) (hdD : d ≤ D)
    (hf : ∀ z, f z = ∑ i ∈ Finset.range (d + 1), e i * z ^ i) :
    ∃ c : ℕ → ℂ, ∀ x, u * f (x / w) = ∑ t ∈ Finset.range (D + 1), c t * x ^ t := by
  refine ⟨fun t => if t ≤ d then u * (e t / w ^ t) else 0, fun x => ?_⟩
  rw [complex_polyfun_truncate D d (fun t => u * (e t / w ^ t)) x hdD, hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [div_pow]
  ring

/-- HOL Light: Baker/sec4.ml, FELDMAN_BASIS_DEGREE_INJ. The degrees `a + h * (b + 1)` with `a < h`
determine `a` and `b`.

Deviation: hypotheses are curried. -/
theorem feldman_basis_degree_inj (h a b a' b' : ℕ) (ha : a < h) (ha' : a' < h)
    (heq : a + h * (b + 1) = a' + h * (b' + 1)) : a = a' ∧ b = b' := by
  have h1 : (a + h * (b + 1)) % h = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h2 : (a' + h * (b' + 1)) % h = a' := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
  have haa : a = a' := by rw [← h1, ← h2, heq]
  subst haa
  have hpos : 0 < h := by omega
  have := Nat.eq_of_mul_eq_mul_left hpos (Nat.add_left_cancel heq)
  exact ⟨rfl, by omega⟩

/-- HOL Light: Baker/sec4.ml, FELDMAN_BASIS_DEGREE_BOUND. The degrees `a + h * (b + 1)` with
`a < h`, `b ≤ L` are at most `h * (L + 2) - 1`.

Deviation: hypotheses are curried. -/
theorem feldman_basis_degree_bound (h L a b : ℕ) (ha : a < h) (hb : b ≤ L) :
    a + h * (b + 1) ≤ h * (L + 2) - 1 := by
  have h1 : h * (b + 1) ≤ h * (L + 1) := Nat.mul_le_mul_left h (by omega)
  have h2 : h * (L + 2) = h * (L + 1) + h := by ring
  omega

/-- HOL Light: Baker/sec4.ml, BAKER_NODES_COINCIDE. If the auxiliary exponential polynomial with
coefficients `p`, not all zero on `bakerIndex h L n`, vanishes at `l = 0, …, h (L+2) (L+1)^n - 1`,
then two distinct exponent vectors `mu`, `mu'` give the same node `exp((∑_r mu_r lg_r) / k)`.

Deviation: hypotheses are curried; `p` is integer-valued (as in `Auxiliary.lean`; HOL: real-valued)
and the summand is a function of the triple `x` with `a = x.1`, `b = x.2.1`, `mu = x.2.2`. -/
theorem baker_nodes_coincide (n h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (lg : ℕ → ℂ)
    (_hn : 1 ≤ n) (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hp : ¬ ∀ x ∈ bakerIndex h L n, p x = 0)
    (hvan : ∀ l : ℕ, l < h * (L + 2) * (L + 1) ^ n →
      ∑ x ∈ bakerIndex h L n,
        (p x : ℂ) * (feldmanBasis h x.1 x.2.1 ((l : ℂ) / (k : ℂ)) *
          Complex.exp ((l : ℂ) * ((∑ r ∈ Finset.Icc 1 n, (x.2.2 r : ℂ) * lg r) / (k : ℂ)))) = 0) :
    ∃ mu mu' : ℕ → ℕ,
      mu ∈ cartesianProduct (Finset.Icc 1 n) (fun _ => Finset.range (L + 1)) ∧
      mu' ∈ cartesianProduct (Finset.Icc 1 n) (fun _ => Finset.range (L + 1)) ∧
      mu ≠ mu' ∧
      Complex.exp ((∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r) / (k : ℂ)) =
        Complex.exp ((∑ r ∈ Finset.Icc 1 n, (mu' r : ℂ) * lg r) / (k : ℂ)) := by
  classical
  by_contra hno
  apply hp
  set T : Finset (ℕ → ℕ) := cartesianProduct (Finset.Icc 1 n) (fun _ => Finset.range (L + 1))
    with hT
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hmemT : ∀ x ∈ bakerIndex h L n, x.2.2 ∈ T := by
    intro x hx
    simp only [bakerIndex, Finset.mem_product] at hx
    exact hx.2.2
  have hmem : ∀ x ∈ bakerIndex h L n, x.1 < h ∧ x.2.1 ≤ L := by
    intro x hx
    simp only [bakerIndex, Finset.mem_product, Finset.mem_range] at hx
    exact ⟨hx.1, by omega⟩
  have hzero : ∀ mu ∈ T, ∀ x : ℂ,
      ∑ y ∈ (bakerIndex h L n).filter (fun y => y.2.2 = mu),
        (p y : ℂ) * feldmanBasis h y.1 y.2.1 (x / (k : ℂ)) = 0 := by
    refine expoly_uniqueness_polyfun T
      (fun mu => Complex.exp ((∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r) / (k : ℂ)))
      (fun _ => h * (L + 2) - 1)
      (fun mu x => ∑ y ∈ (bakerIndex h L n).filter (fun y => y.2.2 = mu),
        (p y : ℂ) * feldmanBasis h y.1 y.2.1 (x / (k : ℂ)))
      (fun _ _ => Complex.exp_ne_zero _) ?_ ?_ ?_
    · intro i hi j hj hij
      by_contra hne
      exact hno ⟨i, j, hi, hj, hne, hij⟩
    · intro mu _
      refine complex_polyfun_vsum _ _ _ fun y hy => ?_
      have hy' := hmem y (Finset.mem_filter.1 hy).1
      obtain ⟨e, -, he⟩ := feldman_basis_polyfun h y.1 y.2.1
      exact complex_polyfun_scale_arg _ e _ _ _ _
        (feldman_basis_degree_bound h L y.1 y.2.1 hy'.1 hy'.2) he
    · intro l hl
      have hcard : ∑ _i ∈ T, (h * (L + 2) - 1 + 1) = h * (L + 2) * (L + 1) ^ n := by
        have hpos : 1 ≤ h * (L + 2) := Nat.mul_pos (by omega) (by omega)
        rw [Finset.sum_const, hT, card_cartesian_product, Finset.prod_const, Finset.card_range,
          Nat.card_Icc, Nat.add_sub_cancel, Nat.sub_add_cancel hpos, smul_eq_mul, mul_comm]
      rw [hcard] at hl
      rw [← hvan l hl, ← Finset.sum_fiberwise_of_maps_to hmemT]
      refine Finset.sum_congr rfl fun mu _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.1 hy).2, ← Complex.exp_nat_mul, mul_assoc]
  intro x hx
  have hx' := hmem x hx
  have key := complex_polyfun_distinct_degrees_fun
    ((bakerIndex h L n).filter (fun y => y.2.2 = x.2.2))
    (fun y z => feldmanBasis h y.1 y.2.1 z) (fun y => y.1 + h * (y.2.1 + 1))
    (fun y => (p y : ℂ)) (fun y _ => feldman_basis_polyfun h y.1 y.2.1) ?_ ?_ x
    (Finset.mem_filter.2 ⟨hx, rfl⟩)
  · exact_mod_cast key
  · intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    obtain ⟨h1, h2⟩ := feldman_basis_degree_inj h i.1 i.2.1 j.1 j.2.1 (hmem i hi.1).1
      (hmem j hj.1).1 hij
    exact Prod.ext h1 (Prod.ext h2 (hi.2.trans hj.2.symm))
  · intro z
    have := hzero x.2.2 (hmemT x hx) ((k : ℂ) * z)
    rwa [mul_div_cancel_left₀ z hk0] at this

private theorem sec4_vsum_num_comb_sub_norm_le (n L : ℕ) (mu mu' : ℕ → ℕ) (lg : ℕ → ℂ)
    (hmu : ∀ r ∈ Finset.Icc 1 n, mu r ≤ L ∧ mu' r ≤ L) :
    ‖∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r - ∑ r ∈ Finset.Icc 1 n, (mu' r : ℂ) * lg r‖ ≤
      (L : ℝ) * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine norm_sum_le_of_le _ fun r hr => ?_
  rw [← sub_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1 : ((mu r : ℂ) - (mu' r : ℂ)) = (((mu r : ℝ) - (mu' r : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h2 : (mu r : ℝ) ≤ L := by exact_mod_cast (hmu r hr).1
  have h3 : (mu' r : ℝ) ≤ L := by exact_mod_cast (hmu r hr).2
  have h4 : (0 : ℝ) ≤ mu r := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ mu' r := Nat.cast_nonneg _
  constructor <;> linarith

/-- HOL Light: Baker/sec4.ml, BAKER_INTEGER_RELATION. If the auxiliary exponential polynomial with
coefficients `p`, not all zero on `bakerIndex h L n`, vanishes at `l = 0, …, h (L+2) (L+1)^n - 1`
and `L * ∑_r ‖lg r‖ < 2 π k`, then there are integers `b r` with `|b r| ≤ L`, not all zero, such
that `∑_r b r * lg r = 0`.

Deviation: hypotheses are curried; `p` is integer-valued (as in `Auxiliary.lean`; HOL: real-valued)
and the summand is a function of the triple `x` with `a = x.1`, `b = x.2.1`, `mu = x.2.2`; the
coefficients `b r` are integers (HOL: reals with `integer (b r)`). -/
theorem baker_integer_relation (n h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (lg : ℕ → ℂ)
    (hn : 1 ≤ n) (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hp : ¬ ∀ x ∈ bakerIndex h L n, p x = 0)
    (hvan : ∀ l : ℕ, l < h * (L + 2) * (L + 1) ^ n →
      ∑ x ∈ bakerIndex h L n,
        (p x : ℂ) * (feldmanBasis h x.1 x.2.1 ((l : ℂ) / (k : ℂ)) *
          Complex.exp ((l : ℂ) * ((∑ r ∈ Finset.Icc 1 n, (x.2.2 r : ℂ) * lg r) / (k : ℂ)))) = 0)
    (hL : (L : ℝ) * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ < 2 * Real.pi * (k : ℝ)) :
    ∃ b : ℕ → ℤ,
      (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ (L : ℝ)) ∧
      (¬ ∀ r ∈ Finset.Icc 1 n, (b r : ℝ) = 0) ∧
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 := by
  obtain ⟨mu, mu', hmu, hmu', hne, hexp⟩ := baker_nodes_coincide n h L k p lg hn hh hk hp hvan
  rw [mem_cartesianProduct] at hmu hmu'
  have hle : ∀ r ∈ Finset.Icc 1 n, mu r ≤ L ∧ mu' r ≤ L := fun r hr =>
    ⟨Nat.lt_succ_iff.1 (Finset.mem_range.1 (hmu.1 r hr)),
      Nat.lt_succ_iff.1 (Finset.mem_range.1 (hmu'.1 r hr))⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  have hdiff : ∑ r ∈ Finset.Icc 1 n, (mu r : ℂ) * lg r - ∑ r ∈ Finset.Icc 1 n, (mu' r : ℂ) * lg r =
      (k : ℂ) * ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    field_simp at hj
    linear_combination hj
  have hnorm := sec4_vsum_num_comb_sub_norm_le n L mu mu' lg hle
  rw [hdiff] at hnorm
  have hjnorm : ‖(k : ℂ) * ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))‖ =
      (k : ℝ) * (|(j : ℝ)| * (2 * Real.pi)) := by
    simp [abs_of_pos Real.pi_pos]
  rw [hjnorm] at hnorm
  have hj0 : j = 0 := by
    by_contra hj0
    have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
    have h2 : (k : ℝ) * (1 * (2 * Real.pi)) ≤ (k : ℝ) * (|(j : ℝ)| * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h1 (by positivity)) hkpos.le
    linarith
  rw [hj0] at hdiff
  refine ⟨fun r => (mu r : ℤ) - (mu' r : ℤ), fun r hr => ?_, fun hall => hne ?_, ?_⟩
  · have h2 : (mu r : ℝ) ≤ L := by exact_mod_cast (hle r hr).1
    have h3 : (mu' r : ℝ) ≤ L := by exact_mod_cast (hle r hr).2
    have h4 : (0 : ℝ) ≤ mu r := Nat.cast_nonneg _
    have h5 : (0 : ℝ) ≤ mu' r := Nat.cast_nonneg _
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · funext r
    by_cases hr : r ∈ Finset.Icc 1 n
    · have := hall r hr
      push_cast at this
      exact_mod_cast sub_eq_zero.1 this
    · rw [hmu.2 r hr, hmu'.2 r hr]
  · have : ∀ r ∈ Finset.Icc 1 n, (((mu r : ℤ) - (mu' r : ℤ) : ℤ) : ℂ) * lg r =
        (mu r : ℂ) * lg r - (mu' r : ℂ) * lg r := fun r _ => by push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hdiff]
    simp

end RiemannMasullo.Baker
