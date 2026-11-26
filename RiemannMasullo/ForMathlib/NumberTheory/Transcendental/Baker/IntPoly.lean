module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Integer polynomial expressions in several complex variables and the Liouville inequality

Ported from HOL Light, Baker/intpoly.ml and Baker/liouville_inequality.ml, with what they need from
Baker/algebraic.ml (jrh13/hol-light, commit 1a0c0e6). -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- HOL Light: Baker/intpoly.ml, intpoly. `intpoly V n b g` says that `g` is a polynomial with
integer coefficients in the variables `x r`, `r ∈ V`, of degree at most `n r` in `x r`, whose
coefficients have absolute sum at most `b`; the terms are indexed by a finite set of naturals.

Deviation: `V` is a `Finset ℕ` (every HOL lemma that uses the product assumes `FINITE v`), and the
coefficients `c k` are integers, cast to `ℝ` and `ℂ` where used, for HOL's `integer (c k)`. -/
def intpoly (V : Finset ℕ) (n : ℕ → ℕ) (b : ℝ) (g : (ℕ → ℂ) → ℂ) : Prop :=
  ∃ (s : Finset ℕ) (c : ℕ → ℤ) (e : ℕ → ℕ → ℕ),
    (∀ k ∈ s, ∀ r ∈ V, e k r ≤ n r) ∧
    ∑ k ∈ s, |(c k : ℝ)| ≤ b ∧
    ∀ x, g x = ∑ k ∈ s, (c k : ℂ) * ∏ r ∈ V, x r ^ e k r

/-- The terms of an `intpoly` may be indexed by a finite set of any type. -/
private theorem intpoly_of_finset {ι : Type*} {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ}
    {g : (ℕ → ℂ) → ℂ} (s : Finset ι) (c : ι → ℤ) (e : ι → ℕ → ℕ)
    (he : ∀ k ∈ s, ∀ r ∈ V, e k r ≤ n r) (hc : ∑ k ∈ s, |(c k : ℝ)| ≤ b)
    (hg : ∀ x, g x = ∑ k ∈ s, (c k : ℂ) * ∏ r ∈ V, x r ^ e k r) : intpoly V n b g := by
  classical
  let f := s.equivFin
  have key : ∀ {M : Type} [AddCommMonoid M] (F : ι → M),
      ∑ k ∈ Finset.range s.card, (if h : k < s.card then F (f.symm ⟨k, h⟩) else 0) =
        ∑ k ∈ s, F k := by
    intro M _ F
    rw [Finset.sum_range (fun k => if h : k < s.card then F (f.symm ⟨k, h⟩) else 0)]
    rw [← Finset.sum_coe_sort s F, ← Equiv.sum_comp f.symm]
    exact Finset.sum_congr rfl fun i _ => by simp
  refine ⟨Finset.range s.card, fun k => if h : k < s.card then c (f.symm ⟨k, h⟩) else 0,
    fun k => if h : k < s.card then e (f.symm ⟨k, h⟩) else fun _ => 0, ?_, ?_, ?_⟩
  · intro k hk r hr
    have hk' : k < s.card := Finset.mem_range.mp hk
    simp only [hk', ↓reduceDIte]
    exact he _ (f.symm ⟨k, hk'⟩).2 r hr
  · rw [← key (fun k => |(c k : ℝ)|)] at hc
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) hc
    have hk' : k < s.card := Finset.mem_range.mp hk
    simp [hk']
  · intro x
    rw [hg x, ← key (fun k => (c k : ℂ) * ∏ r ∈ V, x r ^ e k r)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < s.card := Finset.mem_range.mp hk
    simp [hk']

/-- HOL Light: Baker/intpoly.ml, INTPOLY_EQ. A function equal to an `intpoly` is one. -/
theorem intpoly_eq {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g g' : (ℕ → ℂ) → ℂ}
    (hg : intpoly V n b g) (h : ∀ x, g' x = g x) : intpoly V n b g' := by
  rwa [show g' = g from funext h]

/-- HOL Light: Baker/intpoly.ml, INTPOLY_MONO. The degree bounds and the size bound of an
`intpoly` may be increased. -/
theorem intpoly_mono {V : Finset ℕ} {n n' : ℕ → ℕ} {b b' : ℝ} {g : (ℕ → ℂ) → ℂ}
    (hg : intpoly V n b g) (hn : ∀ r ∈ V, n r ≤ n' r) (hb : b ≤ b') : intpoly V n' b' g := by
  obtain ⟨s, c, e, he, hc, hgx⟩ := hg
  exact ⟨s, c, e, fun k hk r hr => (he k hk r hr).trans (hn r hr), hc.trans hb, hgx⟩

/-- HOL Light: Baker/intpoly.ml, INTPOLY_EQ_ON. An `intpoly` depends only on the variables in
`V`. -/
theorem intpoly_eq_on {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ} {x y : ℕ → ℂ}
    (hg : intpoly V n b g) (h : ∀ r ∈ V, x r = y r) : g x = g y := by
  obtain ⟨s, c, e, -, -, hgx⟩ := hg
  rw [hgx, hgx]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun r hr => by rw [h r hr]

/-- HOL Light: Baker/intpoly.ml, INTPOLY_BOUND_POS. The size bound of an `intpoly` is
nonnegative. -/
theorem intpoly_bound_pos {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (hg : intpoly V n b g) : 0 ≤ b := by
  obtain ⟨s, c, e, -, hc, -⟩ := hg
  exact (Finset.sum_nonneg fun k _ => abs_nonneg _).trans hc

/-- HOL Light: Baker/intpoly.ml, INTPOLY_CONST. An integer constant of absolute value at most `b`
is an `intpoly` of size `b`. -/
theorem intpoly_const (V : Finset ℕ) (n : ℕ → ℕ) {b : ℝ} (c : ℤ) (hc : |(c : ℝ)| ≤ b) :
    intpoly V n b (fun _ => (c : ℂ)) := by
  refine ⟨{0}, fun _ => c, fun _ _ => 0, fun _ _ r _ => Nat.zero_le _, by simpa using hc, ?_⟩
  intro x
  simp

/-- HOL Light: Baker/intpoly.ml, INTPOLY_VAR. A variable `x r` with `r ∈ V` is an `intpoly`. -/
theorem intpoly_var {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {r : ℕ}
    (hr : r ∈ V) (hn : 1 ≤ n r) (hb : 1 ≤ b) : intpoly V n b (fun x => x r) := by
  refine ⟨{0}, fun _ => 1, fun _ i => if i = r then 1 else 0, ?_, by simpa using hb, ?_⟩
  · intro k _ i _
    by_cases h : i = r
    · simp [h, hn]
    · simp [h]
  · intro x
    simp [Finset.prod_ite_eq', hr, pow_ite]

/-- HOL Light: Baker/intpoly.ml, INTPOLY_ADD. The sum of two `intpoly`s. -/
theorem intpoly_add {V : Finset ℕ} {n : ℕ → ℕ} {b1 b2 : ℝ} {g1 g2 : (ℕ → ℂ) → ℂ}
    (h1 : intpoly V n b1 g1) (h2 : intpoly V n b2 g2) :
    intpoly V n (b1 + b2) (fun x => g1 x + g2 x) := by
  obtain ⟨s1, c1, e1, he1, hc1, hg1⟩ := h1
  obtain ⟨s2, c2, e2, he2, hc2, hg2⟩ := h2
  refine intpoly_of_finset (s1.disjSum s2) (Sum.elim c1 c2) (Sum.elim e1 e2) ?_ ?_ ?_
  · intro k hk r hr
    rcases Finset.mem_disjSum.mp hk with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact he1 a ha r hr
    · exact he2 a ha r hr
  · rw [Finset.sum_disjSum]
    exact add_le_add hc1 hc2
  · intro x
    rw [Finset.sum_disjSum, hg1, hg2]
    rfl

/-- HOL Light: Baker/intpoly.ml, INTPOLY_MUL. The product of two `intpoly`s. -/
theorem intpoly_mul {V : Finset ℕ} {n1 n2 : ℕ → ℕ} {b1 b2 : ℝ} {g1 g2 : (ℕ → ℂ) → ℂ}
    (h1 : intpoly V n1 b1 g1) (h2 : intpoly V n2 b2 g2) :
    intpoly V (fun r => n1 r + n2 r) (b1 * b2) (fun x => g1 x * g2 x) := by
  have hb2 := intpoly_bound_pos h2
  obtain ⟨s1, c1, e1, he1, hc1, hg1⟩ := h1
  obtain ⟨s2, c2, e2, he2, hc2, hg2⟩ := h2
  refine intpoly_of_finset (s1 ×ˢ s2) (fun p => c1 p.1 * c2 p.2)
    (fun p r => e1 p.1 r + e2 p.2 r) ?_ ?_ ?_
  · intro k hk r hr
    obtain ⟨hk1, hk2⟩ := Finset.mem_product.mp hk
    exact add_le_add (he1 _ hk1 r hr) (he2 _ hk2 r hr)
  · rw [Finset.sum_product]
    have : ∑ i ∈ s1, ∑ j ∈ s2, |((c1 i * c2 j : ℤ) : ℝ)| =
        (∑ i ∈ s1, |(c1 i : ℝ)|) * ∑ j ∈ s2, |(c2 j : ℝ)| := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [Int.cast_mul, abs_mul]
    rw [this]
    exact mul_le_mul hc1 hc2 (Finset.sum_nonneg fun k _ => abs_nonneg _)
      ((Finset.sum_nonneg fun k _ => abs_nonneg _).trans hc1)
  · intro x
    rw [Finset.sum_product, hg1, hg2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [pow_add, Finset.prod_mul_distrib, Int.cast_mul]
    ring

/-- HOL Light: Baker/intpoly.ml, INTPOLY_NEG. The negative of an `intpoly`. -/
theorem intpoly_neg {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (hg : intpoly V n b g) : intpoly V n b (fun x => -g x) := by
  obtain ⟨s, c, e, he, hc, hgx⟩ := hg
  refine ⟨s, fun k => -c k, e, he, by simpa using hc, fun x => ?_⟩
  change -g x = _
  rw [hgx, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by push_cast; ring

/-- HOL Light: Baker/intpoly.ml, INTPOLY_SUB. The difference of two `intpoly`s. -/
theorem intpoly_sub {V : Finset ℕ} {n : ℕ → ℕ} {b1 b2 : ℝ} {g1 g2 : (ℕ → ℂ) → ℂ}
    (h1 : intpoly V n b1 g1) (h2 : intpoly V n b2 g2) :
    intpoly V n (b1 + b2) (fun x => g1 x - g2 x) := by
  simpa only [sub_eq_add_neg] using intpoly_add h1 (intpoly_neg h2)

/-- HOL Light: Baker/intpoly.ml, INTPOLY_POW. A power of an `intpoly`. -/
theorem intpoly_pow {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (hg : intpoly V n b g) (k : ℕ) :
    intpoly V (fun r => k * n r) (b ^ k) (fun x => g x ^ k) := by
  induction k with
  | zero => simpa using intpoly_const V (fun r => 0 * n r) (b := 1) 1 (by simp)
  | succ k ih =>
    refine intpoly_eq (intpoly_mono (intpoly_mul ih hg) (n' := fun r => (k + 1) * n r)
      (b' := b ^ (k + 1)) (fun r _ => by simp [Nat.succ_mul]) (by rw [pow_succ])) ?_
    intro x
    rw [pow_succ]

/-- HOL Light: Baker/intpoly.ml, INTPOLY_VSUM. A finite sum of `intpoly`s. -/
theorem intpoly_vsum {A : Type*} {V : Finset ℕ} {n : ℕ → ℕ} {b : A → ℝ}
    {g : A → (ℕ → ℂ) → ℂ} {t : Finset A} (h : ∀ i ∈ t, intpoly V n (b i) (g i)) :
    intpoly V n (∑ i ∈ t, b i) (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using intpoly_const V n (b := 0) 0 (by simp)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact intpoly_add (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- HOL Light: Baker/intpoly.ml, INTPOLY_CPRODUCT. A finite product of `intpoly`s. -/
theorem intpoly_cproduct {A : Type*} {V : Finset ℕ} {n : A → ℕ → ℕ} {b : A → ℝ}
    {g : A → (ℕ → ℂ) → ℂ} {t : Finset A} (h : ∀ i ∈ t, intpoly V (n i) (b i) (g i)) :
    intpoly V (fun r => ∑ i ∈ t, n i r) (∏ i ∈ t, b i) (fun x => ∏ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using intpoly_const V (fun _ => 0) (b := 1) 1 (by simp)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact intpoly_mul (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- HOL Light: Baker/intpoly.ml, INTPOLY_BOUND. The upper bound `‖g x‖ ≤ b ∏ m r ^ n r` for an
`intpoly` at a point with `‖x r‖ ≤ m r`. -/
theorem intpoly_bound {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ} {x : ℕ → ℂ}
    {m : ℕ → ℝ} (hg : intpoly V n b g) (hx : ∀ r ∈ V, ‖x r‖ ≤ m r ∧ 1 ≤ m r) :
    ‖g x‖ ≤ b * ∏ r ∈ V, m r ^ n r := by
  obtain ⟨s, c, e, he, hc, hgx⟩ := hg
  have hP : 0 ≤ ∏ r ∈ V, m r ^ n r :=
    Finset.prod_nonneg fun r hr => pow_nonneg (zero_le_one.trans (hx r hr).2) _
  rw [hgx]
  calc ‖∑ k ∈ s, (c k : ℂ) * ∏ r ∈ V, x r ^ e k r‖
      ≤ ∑ k ∈ s, |(c k : ℝ)| * ∏ r ∈ V, m r ^ n r := by
        refine norm_sum_le_of_le _ fun k hk => ?_
        rw [norm_mul, norm_prod, Complex.norm_intCast]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine Finset.prod_le_prod₀ (fun r _ => norm_nonneg _) ?_
        intro r hr
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (hx r hr).1 _).trans
          (pow_le_pow_right₀ (hx r hr).2 (he k hk r hr))
    _ = (∑ k ∈ s, |(c k : ℝ)|) * ∏ r ∈ V, m r ^ n r := by rw [Finset.sum_mul]
    _ ≤ b * ∏ r ∈ V, m r ^ n r := mul_le_mul_of_nonneg_right hc hP

/-- HOL Light: Baker/intpoly.ml, INTPOLY_MONOMIAL. A monomial in variables from `s ⊆ V`. -/
theorem intpoly_monomial {V s : Finset ℕ} (k : ℕ → ℕ) (hs : s ⊆ V) :
    intpoly V (fun r => if r ∈ s then k r else 0) 1 (fun x => ∏ r ∈ s, x r ^ k r) := by
  refine ⟨{0}, fun _ => 1, fun _ r => if r ∈ s then k r else 0, fun _ _ _ _ => le_rfl,
    by simp, fun x => ?_⟩
  simp only [Finset.sum_singleton, Int.cast_one, one_mul]
  rw [← Finset.prod_subset hs fun r _ hr => by simp [hr]]
  exact Finset.prod_congr rfl fun r hr => by simp [hr]

/-- HOL Light: Baker/intpoly.ml, INTPOLY_CMUL. An integer multiple of an `intpoly`. -/
theorem intpoly_cmul {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ} (a : ℤ)
    (hg : intpoly V n b g) : intpoly V n (|(a : ℝ)| * b) (fun x => (a : ℂ) * g x) := by
  obtain ⟨s, c, e, he, hc, hgx⟩ := hg
  refine ⟨s, fun k => a * c k, e, he, ?_, fun x => ?_⟩
  · simp only [Int.cast_mul, abs_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  · change (a : ℂ) * g x = _
    rw [hgx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring

/-- HOL Light: Baker/intpoly.ml, INTPOLY_NUM_MUL. A natural multiple of an `intpoly`. -/
theorem intpoly_num_mul {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ} (k : ℕ)
    (hg : intpoly V n b g) : intpoly V n ((k : ℝ) * b) (fun x => (k : ℂ) * g x) := by
  simpa using intpoly_cmul (k : ℤ) hg

/-- HOL Light: Baker/intpoly.ml, INTPOLY_LINEAR. A linear form with integer coefficients in
variables from `V`. -/
theorem intpoly_linear {V : Finset ℕ} (c : ℕ → ℤ) (p : ℕ → ℕ) {t : Finset ℕ}
    (h : ∀ j ∈ t, p j ∈ V) :
    intpoly V (fun _ => 1) (∑ j ∈ t, |(c j : ℝ)|) (fun x => ∑ j ∈ t, (c j : ℂ) * x (p j)) := by
  refine intpoly_vsum (b := fun j => |(c j : ℝ)|) (g := fun j x => (c j : ℂ) * x (p j))
    fun j hj => ?_
  simpa using intpoly_cmul (c j) (intpoly_var (n := fun _ => 1) (b := 1) (h j hj) le_rfl le_rfl)

/-! ### Cartesian products -/

/-- HOL Light: sets.ml, cartesian_product. The dependent cartesian product of the finite sets
`s i`, `i ∈ k`, as a finite set of functions `K → A` that take the value `default` outside `k`.

Deviation: HOL's `cartesian_product k s` consists of the functions that are `ARB` outside `k`
(`EXTENSIONAL k`); here `ARB` is `default`, so for `A = ℕ` the functions are `0` outside `k`. The
membership rule is `mem_cartesianProduct`. -/
def cartesianProduct {K A : Type*} [DecidableEq K] [Inhabited A] (k : Finset K)
    (s : K → Finset A) : Finset (K → A) :=
  (k.pi s).map ⟨fun f i => if h : i ∈ k then f i h else default, by
    intro f f' hff'
    funext i hi
    simpa [hi] using congrFun hff' i⟩

/-- HOL Light: sets.ml, IN_CARTESIAN_PRODUCT. Membership in a cartesian product. -/
theorem mem_cartesianProduct {K A : Type*} [DecidableEq K] [Inhabited A] {k : Finset K}
    {s : K → Finset A} {x : K → A} :
    x ∈ cartesianProduct k s ↔ (∀ i ∈ k, x i ∈ s i) ∧ ∀ i, i ∉ k → x i = default := by
  constructor
  · intro hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hx
    rw [Finset.mem_pi] at hf
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · change (if h : i ∈ k then f i h else default) ∈ s i
      simpa only [hi, ↓reduceDIte] using hf i hi
    · change (if h : i ∈ k then f i h else default) = default
      simp only [hi, ↓reduceDIte]
  · rintro ⟨h1, h2⟩
    refine Finset.mem_map.mpr ⟨fun i _ => x i, Finset.mem_pi.mpr fun i hi => h1 i hi, ?_⟩
    funext i
    change (if h : i ∈ k then x i else default) = x i
    by_cases hi : i ∈ k
    · simp only [hi, ↓reduceDIte]
    · simp only [hi, ↓reduceDIte, h2 i hi]

/-- HOL Light: sets.ml, RESTRICTION_IN_CARTESIAN_PRODUCT. The restriction of a function to `k`
lies in the cartesian product when its values on `k` do. -/
theorem restriction_mem_cartesianProduct {K A : Type*} [DecidableEq K] [Inhabited A]
    {k : Finset K} {s : K → Finset A} {f : K → A} (h : ∀ i ∈ k, f i ∈ s i) :
    (fun i => if i ∈ k then f i else default) ∈ cartesianProduct k s :=
  mem_cartesianProduct.mpr ⟨fun i hi => by simpa [hi] using h i hi, fun i hi => by simp [hi]⟩

/-- HOL Light: Baker/intpoly.ml, VSUM_CPRODUCT_CARTESIAN_PRODUCT. A sum of products over a
(dependent) cartesian product is the product of the sums.

Deviation: stated in any commutative semiring, not only `ℂ`. -/
theorem vsum_cproduct_cartesian_product {K A R : Type*} [DecidableEq K] [Inhabited A]
    [CommSemiring R] (k : Finset K) (s : K → Finset A) (f : K → A → R) :
    ∑ x ∈ cartesianProduct k s, ∏ i ∈ k, f i (x i) = ∏ i ∈ k, ∑ a ∈ s i, f i a := by
  rw [Finset.prod_sum, cartesianProduct, Finset.sum_map]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_attach]
  refine Finset.prod_congr rfl fun i _ => ?_
  change f i.1 (if h : i.1 ∈ k then p i.1 h else default) = f i.1 (p i.1 i.2)
  simp only [i.2, ↓reduceDIte]

/-- HOL Light: Baker/intpoly.ml, CARD_CARTESIAN_PRODUCT. The cardinality of a cartesian
product. -/
theorem card_cartesian_product {K A : Type*} [DecidableEq K] [Inhabited A] (k : Finset K)
    (s : K → Finset A) : (cartesianProduct k s).card = ∏ i ∈ k, (s i).card := by
  rw [cartesianProduct, Finset.card_map, Finset.card_pi]

/-- HOL Light: Baker/intpoly.ml, CARD_CARTESIAN_PRODUCT_NUMSEG. The number of tuples `t` with
`1 ≤ t r ≤ d r`. -/
theorem card_cartesian_product_numseg (V : Finset ℕ) (d : ℕ → ℕ) :
    (cartesianProduct V fun r => Finset.Icc 1 (d r)).card = ∏ r ∈ V, d r := by
  simp [card_cartesian_product]

/-! ### Newton identities and power sums (Baker/algebraic.ml) -/

section Newton

private theorem intpoly_aux_esymm {A : Type*} (s : Finset A) (z : A → ℂ) (k : ℕ) :
    MvPolynomial.eval (fun i : s => z i) (MvPolynomial.esymm s ℂ k) =
      ∑ t ∈ s.powersetCard k, ∏ i ∈ t, z i := by
  have h := MvPolynomial.aeval_esymm_eq_multiset_esymm (R := ℂ) s k (fun i : s => z i)
  rw [MvPolynomial.aeval_eq_eval] at h
  rw [h, ← Finset.esymm_map_val]
  exact congrArg (fun M : Multiset ℂ => M.esymm k) (Multiset.attach_map_val' s.val z)

private theorem intpoly_aux_psum {A : Type*} (s : Finset A) (z : A → ℂ) (m : ℕ) :
    MvPolynomial.eval (fun i : s => z i) (MvPolynomial.psum s ℂ m) = ∑ i ∈ s, z i ^ m := by
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X]
  exact Finset.sum_coe_sort s (fun i => z i ^ m)

/-- Newton identities: integer elementary symmetric functions give integer power sums. -/
private theorem intpoly_aux_newton_psum {A : Type*} (S : Subring ℂ) (s : Finset A) (z : A → ℂ)
    (h : ∀ k, ∑ t ∈ s.powersetCard k, ∏ i ∈ t, z i ∈ S) (m : ℕ) : ∑ i ∈ s, z i ^ m ∈ S := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have key := congrArg (MvPolynomial.eval fun i : s => z i)
      (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ m hm)
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
      intpoly_aux_esymm, intpoly_aux_psum] at key
    rw [key]
    refine S.sub_mem (S.mul_mem (S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _)
      (natCast_mem S m)) (h m)) (S.sum_mem fun a ha => ?_)
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp ha1
    exact S.mul_mem (S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) (h _))
      (ih _ (by have := ha2.1; omega))

/-- Newton identities: integer power sums give integer `k! e_k`. -/
private theorem intpoly_aux_newton_esymm {A : Type*} (S : Subring ℂ) (s : Finset A) (z : A → ℂ)
    (h : ∀ m, 1 ≤ m → ∑ i ∈ s, z i ^ m ∈ S) (k : ℕ) :
    (k.factorial : ℂ) * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, z i ∈ S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have key := congrArg (MvPolynomial.eval fun i : s => z i)
      (MvPolynomial.mul_esymm_eq_sum s ℂ k)
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
      intpoly_aux_esymm, intpoly_aux_psum] at key
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((j + 1 : ℕ) : ℂ), mul_assoc, key,
      mul_left_comm, Finset.mul_sum]
    refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) (S.sum_mem fun a ha => ?_)
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp ha1
    have hdvd : a.1.factorial ∣ j.factorial := Nat.factorial_dvd_factorial (by omega)
    obtain ⟨q, hq⟩ := hdvd
    have : (j.factorial : ℂ) * ((-1) ^ a.1 * (∑ t ∈ s.powersetCard a.1, ∏ i ∈ t, z i) *
        ∑ i ∈ s, z i ^ a.2) = (q : ℂ) * (-1) ^ a.1 *
        ((a.1.factorial : ℂ) * ∑ t ∈ s.powersetCard a.1, ∏ i ∈ t, z i) * ∑ i ∈ s, z i ^ a.2 := by
      rw [hq]; push_cast; ring
    rw [this]
    exact S.mul_mem (S.mul_mem (S.mul_mem (natCast_mem S q) (S.pow_mem (S.neg_mem S.one_mem) _))
      (ih _ (by omega))) (h _ (by omega))

end Newton

/-- HOL Light: Baker/algebraic.ml, POWER_SUMS_INTEGER_LOWER_BOUND. A nonzero member of a finite
family of complex numbers of norm at most `b` whose power sums are all integers has norm at least
`1 / (N! b ^ (N - 1))`, where `N` is the size of the family. -/
theorem power_sums_integer_lower_bound {A : Type*} (s : Finset A) (z : A → ℂ) (a : A) (b : ℝ)
    (ha : a ∈ s) (hza : z a ≠ 0) (hb : 1 ≤ b) (hz : ∀ i ∈ s, ‖z i‖ ≤ b)
    (hint : ∀ m, 1 ≤ m → ∃ k : ℤ, ∑ i ∈ s, z i ^ m = (k : ℂ)) :
    ((s.card.factorial : ℝ) * b ^ (s.card - 1))⁻¹ ≤ ‖z a‖ := by
  classical
  set T := s.filter fun i => z i ≠ 0 with hT
  have haT : a ∈ T := Finset.mem_filter.mpr ⟨ha, hza⟩
  have hTs : T ⊆ s := Finset.filter_subset _ _
  have hcard : T.card ≤ s.card := Finset.card_le_card hTs
  have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, haT⟩
  -- the elementary symmetric function of degree `T.card` is the product over `T`
  have hes : ∑ t ∈ s.powersetCard T.card, ∏ i ∈ t, z i = ∏ i ∈ T, z i := by
    refine Finset.sum_eq_single T (fun t ht hne => ?_) fun h => ?_
    · obtain ⟨hts, htc⟩ := Finset.mem_powersetCard.mp ht
      have : ¬ t ⊆ T := fun hsub => hne (Finset.eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨i, hit, hiT⟩ := Finset.not_subset.mp this
      refine Finset.prod_eq_zero hit ?_
      by_contra hzi
      exact hiT (Finset.mem_filter.mpr ⟨hts hit, hzi⟩)
    · exact absurd (Finset.mem_powersetCard.mpr ⟨hTs, rfl⟩) h
  have hmem := intpoly_aux_newton_esymm (Int.castRingHom ℂ).range s z
    (fun m hm => by obtain ⟨k, hk⟩ := hint m hm; exact ⟨k, hk.symm⟩) T.card
  obtain ⟨q, hq⟩ := hmem
  rw [hes] at hq
  have hprod : ∏ i ∈ T, z i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (Finset.mem_filter.mp hi).2
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, eq_intCast, zero_eq_mul, Nat.cast_eq_zero] at hq
    exact hq.elim (Nat.factorial_ne_zero _) hprod
  have h1 : (1 : ℝ) ≤ (T.card.factorial : ℝ) * ‖∏ i ∈ T, z i‖ := by
    have := congrArg norm hq
    simp only [eq_intCast, Complex.norm_intCast, norm_mul, Complex.norm_natCast] at this
    rw [← this]
    exact_mod_cast Int.one_le_abs hq0
  have hb0 : (0 : ℝ) ≤ b := zero_le_one.trans hb
  have h2 : ‖∏ i ∈ T, z i‖ ≤ ‖z a‖ * b ^ (s.card - 1) := by
    rw [← Finset.mul_prod_erase T z haT, norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ∏ i ∈ T.erase a, ‖z i‖ ≤ ∏ _i ∈ T.erase a, b :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi =>
            hz i (hTs (Finset.mem_of_mem_erase hi))
      _ = b ^ (T.card - 1) := by rw [Finset.prod_const, Finset.card_erase_of_mem haT]
      _ ≤ b ^ (s.card - 1) := pow_le_pow_right₀ hb (by omega)
  have hfact : (T.card.factorial : ℝ) ≤ (s.card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hcard
  have hpos : (0 : ℝ) < (s.card.factorial : ℝ) * b ^ (s.card - 1) :=
    mul_pos (by exact_mod_cast Nat.factorial_pos _) (pow_pos (zero_lt_one.trans_le hb) _)
  rw [inv_le_iff_one_le_mul₀ hpos]
  calc (1 : ℝ) ≤ (T.card.factorial : ℝ) * ‖∏ i ∈ T, z i‖ := h1
    _ ≤ (s.card.factorial : ℝ) * (‖z a‖ * b ^ (s.card - 1)) :=
        mul_le_mul hfact h2 (norm_nonneg _) (by positivity)
    _ = ‖z a‖ * ((s.card.factorial : ℝ) * b ^ (s.card - 1)) := by ring

/-- HOL Light: Baker/intpoly.ml, INTPOLY_CARTESIAN_SUM_INTEGER. The sum of an `intpoly` over all
tuples of conjugates is an integer when each family of conjugates has integer power sums. -/
theorem intpoly_cartesian_sum_integer {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (d : ℕ → ℕ) (rho : ℕ → ℕ → ℂ) (hg : intpoly V n b g)
    (hrho : ∀ r m, r ∈ V → ∃ k : ℤ, ∑ i ∈ Finset.Icc 1 (d r), rho r i ^ m = (k : ℂ)) :
    ∃ k : ℤ, ∑ t ∈ cartesianProduct V fun r => Finset.Icc 1 (d r), g (fun r => rho r (t r)) =
      (k : ℂ) := by
  obtain ⟨s, c, e, -, -, hgx⟩ := hg
  suffices h : ∑ t ∈ cartesianProduct V fun r => Finset.Icc 1 (d r), g (fun r => rho r (t r)) ∈
      (Int.castRingHom ℂ).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, hk.symm⟩
  simp only [hgx]
  rw [Finset.sum_comm]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [← Finset.mul_sum,
    vsum_cproduct_cartesian_product V (fun r => Finset.Icc 1 (d r)) (fun r i => rho r i ^ e k r)]
  refine Subring.mul_mem _ ⟨c k, rfl⟩ (Subring.prod_mem _ fun r hr => ?_)
  obtain ⟨q, hq⟩ := hrho r (e k r) hr
  exact ⟨q, hq.symm⟩

/-- HOL Light: Baker/intpoly.ml, INTPOLY_LIOUVILLE_MONIC. The Liouville inequality for a nonzero
`intpoly` at roots of monic integer polynomials, each given by the family `rho r i`,
`1 ≤ i ≤ d r`, of all its roots (with integer power sums).

Deviation: HOL's `!r i. r IN v /\ i IN 1..d r ==> ...` is curried as
`∀ r ∈ V, ∀ i ∈ Finset.Icc 1 (d r), ...`; the index set of tuples is `cartesianProduct`. -/
theorem intpoly_liouville_monic {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (d : ℕ → ℕ) (rho : ℕ → ℕ → ℂ) (t0 : ℕ → ℕ) (m : ℕ → ℝ) (hg : intpoly V n b g)
    (hrho : ∀ r k, r ∈ V → ∃ q : ℤ, ∑ i ∈ Finset.Icc 1 (d r), rho r i ^ k = (q : ℂ))
    (hnorm : ∀ r ∈ V, ∀ i ∈ Finset.Icc 1 (d r), ‖rho r i‖ ≤ m r)
    (hm : ∀ r ∈ V, 1 ≤ m r)
    (ht0 : t0 ∈ cartesianProduct V fun r => Finset.Icc 1 (d r))
    (hne : g (fun r => rho r (t0 r)) ≠ 0) :
    (((∏ r ∈ V, d r).factorial : ℝ) *
      max 1 (b * ∏ r ∈ V, m r ^ n r) ^ ((∏ r ∈ V, d r) - 1))⁻¹ ≤
      ‖g (fun r => rho r (t0 r))‖ := by
  have h := power_sums_integer_lower_bound (cartesianProduct V fun r => Finset.Icc 1 (d r))
    (fun t => g (fun r => rho r (t r))) t0 (max 1 (b * ∏ r ∈ V, m r ^ n r)) ht0 hne
    (le_max_left _ _) (fun t ht => le_max_of_le_right (intpoly_bound hg fun r hr =>
      ⟨hnorm r hr (t r) ((mem_cartesianProduct.mp ht).1 r hr), hm r hr⟩))
    (fun k _ => intpoly_cartesian_sum_integer d rho (intpoly_pow hg k) hrho)
  rwa [card_cartesian_product_numseg] at h

/-! ### The Liouville inequality (Baker/liouville_inequality.ml) -/

private theorem intpoly_aux_enum (M : Multiset ℂ) :
    ∃ rho : ℕ → ℂ, (Finset.Icc 1 (Multiset.card M)).val.map rho = M := by
  induction M using Quotient.inductionOn with
  | _ l =>
    refine ⟨fun i => l.getD (i - 1) 0, ?_⟩
    change Multiset.map _ ((List.range' 1 (l.length + 1 - 1) : List ℕ) : Multiset ℕ) =
      (l : Multiset ℂ)
    rw [Multiset.map_coe]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [List.getElem_range', List.getElem?_eq_getElem h2]

/-- HOL Light: Baker/liouville_inequality.ml, INTEGER_POLY_ROOTS_SCALED. The roots of an integer
polynomial of degree `d`, scaled by the leading coefficient, have integer power sums. -/
theorem integer_poly_roots_scaled (a : ℕ → ℤ) (d : ℕ) (had : a d ≠ 0) :
    ∃ rho : ℕ → ℂ,
      (∀ x : ℂ, ∑ j ∈ Finset.range (d + 1), (a j : ℂ) * x ^ j =
        (a d : ℂ) * ∏ i ∈ Finset.Icc 1 d, (x - rho i)) ∧
      ∀ k : ℕ, ∃ q : ℤ, ∑ i ∈ Finset.Icc 1 d, ((a d : ℂ) * rho i) ^ k = (q : ℂ) := by
  classical
  open Polynomial in
  set P : ℂ[X] := ∑ j ∈ Finset.range (d + 1), C (a j : ℂ) * X ^ j with hP
  have hcoeff : ∀ j, j ≤ d → P.coeff j = (a j : ℂ) := by
    intro j hj
    simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j (fun i _ hij => by simp only [Ne.symm hij, ↓reduceIte])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    simp
  have had' : (a d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr had
  have hdeg : P.natDegree = d := by
    refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff d le_rfl]; exact had'))
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      (by have := Finset.mem_range.mp hj; omega)
  have hlead : P.leadingCoeff = (a d : ℂ) := by
    rw [Polynomial.leadingCoeff, hdeg, hcoeff d le_rfl]
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : Multiset.card P.roots = d := by
    rw [← hdeg]; exact hsplit.natDegree_eq_card_roots.symm
  obtain ⟨rho, hrho⟩ := intpoly_aux_enum P.roots
  rw [hcard] at hrho
  refine ⟨rho, fun x => ?_, fun k => ?_⟩
  · have h1 : P.eval x = ∑ j ∈ Finset.range (d + 1), (a j : ℂ) * x ^ j := by
      simp [hP, Polynomial.eval_finsetSum]
    rw [← h1, hsplit.eval_eq_prod_roots, hlead, ← hrho, Multiset.map_map]
    rfl
  · suffices h : ∑ i ∈ Finset.Icc 1 d, ((a d : ℂ) * rho i) ^ k ∈ (Int.castRingHom ℂ).range by
      obtain ⟨q, hq⟩ := h
      exact ⟨q, hq.symm⟩
    refine intpoly_aux_newton_psum _ (Finset.Icc 1 d) (fun i => (a d : ℂ) * rho i) (fun j => ?_) k
    have hes : ∑ t ∈ (Finset.Icc 1 d).powersetCard j, ∏ i ∈ t, ((a d : ℂ) * rho i) =
        (a d : ℂ) ^ j * P.roots.esymm j := by
      rw [← hrho, Finset.esymm_map_val, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
    rw [hes]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    rcases Nat.lt_or_ge d j with hdj | hdj
    · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard]; exact hdj)]
      simp
    · have hv := Polynomial.coeff_eq_esymm_roots_of_card (p := P) (by rw [hcard, hdeg])
        (k := d - j) (by rw [hdeg]; omega)
      rw [hdeg, hlead, hcoeff _ (Nat.sub_le _ _), show d - (d - j) = j by omega] at hv
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have : (a d : ℂ) ^ (i + 1) * P.roots.esymm (i + 1) =
          (a d : ℂ) ^ i * (-1) ^ (i + 1) * (a (d - (i + 1)) : ℂ) := by
        rw [hv]
        have hsq : ((-1 : ℂ) ^ (i + 1)) * ((-1 : ℂ) ^ (i + 1)) = 1 := by
          rw [← mul_pow]; simp
        linear_combination (-(a d : ℂ) ^ (i + 1) * P.roots.esymm (i + 1)) * hsq
      rw [this]
      exact ⟨a d ^ i * (-1) ^ (i + 1) * a (d - (i + 1)), by simp⟩

/-- HOL Light: Baker/liouville_inequality.ml, INTEGER_POLY_ROOT_BOUND. A root `z` of an integer
polynomial of degree `d` with coefficients bounded by `h` satisfies `‖z‖ ≤ 1 + d h`. -/
theorem integer_poly_root_bound (a : ℕ → ℤ) (d : ℕ) (h : ℝ) (z : ℂ) (had : a d ≠ 0)
    (hah : ∀ j, |(a j : ℝ)| ≤ h)
    (hz : ∑ j ∈ Finset.range (d + 1), (a j : ℂ) * z ^ j = 0) : ‖z‖ ≤ 1 + (d : ℝ) * h := by
  have hh : 0 ≤ h := (abs_nonneg _).trans (hah 0)
  have hdh : 0 ≤ (d : ℝ) * h := mul_nonneg (Nat.cast_nonneg d) hh
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
      Int.cast_eq_zero] at hz
    exact absurd hz had
  have hA : (1 : ℝ) ≤ |(a d : ℝ)| := by exact_mod_cast Int.one_le_abs had
  rw [Finset.sum_range_succ] at hz
  have hz' : (a d : ℂ) * z ^ d = -∑ j ∈ Finset.range d, (a j : ℂ) * z ^ j := by
    linear_combination hz
  have hz0 : 0 < ‖z‖ := zero_lt_one.trans h1
  have h2 : ‖z‖ ^ d ≤ d * h * ‖z‖ ^ (d - 1) := by
    calc ‖z‖ ^ d ≤ |(a d : ℝ)| * ‖z‖ ^ d := le_mul_of_one_le_left (pow_nonneg hz0.le _) hA
      _ = ‖(a d : ℂ) * z ^ d‖ := by rw [norm_mul, norm_pow, Complex.norm_intCast]
      _ = ‖∑ j ∈ Finset.range d, (a j : ℂ) * z ^ j‖ := by rw [hz', norm_neg]
      _ ≤ ∑ _j ∈ Finset.range d, h * ‖z‖ ^ (d - 1) := by
          refine norm_sum_le_of_le _ fun j hj => ?_
          rw [norm_mul, norm_pow, Complex.norm_intCast]
          exact mul_le_mul (hah j) (pow_le_pow_right₀ h1.le
            (by have := Finset.mem_range.mp hj; omega)) (pow_nonneg hz0.le _) hh
      _ = d * h * ‖z‖ ^ (d - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have h3 : ‖z‖ ^ d = ‖z‖ * ‖z‖ ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h3] at h2
  have := le_of_mul_le_mul_right h2 (pow_pos hz0 _)
  linarith

/-- HOL Light: Baker/liouville_inequality.ml, INTPOLY_SCALE. Clearing denominators: substituting
`y r / a r` into an `intpoly` and multiplying by `∏ a r ^ n r` gives an `intpoly`. -/
theorem intpoly_scale {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ} (a : ℕ → ℤ)
    (hg : intpoly V n b g) (ha : ∀ r ∈ V, a r ≠ 0) :
    intpoly V n (b * ∏ r ∈ V, |(a r : ℝ)| ^ n r)
      (fun y => (∏ r ∈ V, (a r : ℂ) ^ n r) * g (fun r => y r / (a r : ℂ))) := by
  obtain ⟨s, c, e, he, hc, hgx⟩ := hg
  refine ⟨s, fun k => c k * ∏ r ∈ V, a r ^ (n r - e k r), e, he, ?_, fun y => ?_⟩
  · calc ∑ k ∈ s, |((c k * ∏ r ∈ V, a r ^ (n r - e k r) : ℤ) : ℝ)|
        ≤ ∑ k ∈ s, |(c k : ℝ)| * ∏ r ∈ V, |(a r : ℝ)| ^ n r := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Int.cast_mul, abs_mul, Int.cast_prod, Finset.abs_prod]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine Finset.prod_le_prod₀ (fun r _ => abs_nonneg _) fun r hr => ?_
          rw [Int.cast_pow, abs_pow]
          exact pow_le_pow_right₀ (by exact_mod_cast Int.one_le_abs (ha r hr)) (Nat.sub_le _ _)
      _ = (∑ k ∈ s, |(c k : ℝ)|) * ∏ r ∈ V, |(a r : ℝ)| ^ n r := by rw [Finset.sum_mul]
      _ ≤ b * ∏ r ∈ V, |(a r : ℝ)| ^ n r :=
          mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg fun r _ => pow_nonneg (abs_nonneg _) _)
  · change (∏ r ∈ V, (a r : ℂ) ^ n r) * g (fun r => y r / (a r : ℂ)) = _
    rw [hgx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Int.cast_mul, Int.cast_prod, mul_left_comm, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    have har : (a r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (ha r hr)
    have hsplit : (a r : ℂ) ^ n r = (a r : ℂ) ^ (n r - e k r) * (a r : ℂ) ^ e k r := by
      rw [← pow_add, Nat.sub_add_cancel (he k hk r hr)]
    rw [hsplit, div_pow, Int.cast_pow]
    field_simp

/-- HOL Light: Baker/liouville_inequality.ml, LIOUVILLE_INEQ_LEMMA. -/
private theorem intpoly_aux_liouville_ineq {f m1 m2 p1 p2 y : ℝ} {k : ℕ} (hf : 1 ≤ f)
    (hm1 : 1 ≤ m1) (hm : m1 ≤ m2) (hp1 : 0 < p1) (hp : p1 ≤ p2)
    (h : (f * m1 ^ k)⁻¹ ≤ p1 * y) : (f * (m2 ^ k * p2))⁻¹ ≤ y := by
  have hf0 : 0 < f := zero_lt_one.trans_le hf
  have hm10 : 0 < m1 := zero_lt_one.trans_le hm1
  have hy : 0 < y := by
    have : 0 < p1 * y := lt_of_lt_of_le (inv_pos.mpr (mul_pos hf0 (pow_pos hm10 _))) h
    by_contra hy
    exact absurd this (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hp1.le (not_lt.mp hy)))
  rw [inv_le_iff_one_le_mul₀ (mul_pos hf0 (pow_pos hm10 _))] at h
  rw [inv_le_iff_one_le_mul₀ (mul_pos hf0 (mul_pos (pow_pos (hm10.trans_le hm) _)
    (hp1.trans_le hp)))]
  calc (1 : ℝ) ≤ p1 * y * (f * m1 ^ k) := h
    _ ≤ p2 * y * (f * m2 ^ k) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hp hy.le)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm10.le hm _) hf0.le)
          (mul_nonneg hf0.le (pow_nonneg hm10.le _)) (mul_nonneg (hp1.trans_le hp).le hy.le)
    _ = y * (f * (m2 ^ k * p2)) := by ring

/-- HOL Light: Baker/liouville_inequality.ml, INTPOLY_LIOUVILLE. The Liouville inequality: a
nonzero value `g theta` of an `intpoly` at numbers `theta r`, each a root of an integer polynomial
`∑ j ≤ d r, a r j * X ^ j` of degree `d r` with coefficients bounded by `h r`, is bounded below
explicitly.

Deviation: the coefficients `a r j` are integers (HOL: reals with `integer (a r j)`). -/
theorem intpoly_liouville {V : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (theta : ℕ → ℂ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (h : ℕ → ℝ)
    (hg : intpoly V n b g)
    (ha : ∀ r ∈ V, (∀ j, |(a r j : ℝ)| ≤ h r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hne : g theta ≠ 0) :
    (((∏ r ∈ V, d r).factorial : ℝ) *
      (max 1 (b * ((∏ r ∈ V, h r ^ n r) *
          ∏ r ∈ V, (h r * (1 + (d r : ℝ) * h r)) ^ n r)) ^ ((∏ r ∈ V, d r) - 1) *
        ∏ r ∈ V, h r ^ n r))⁻¹ ≤ ‖g theta‖ := by
  classical
  have hex : ∀ r, ∃ rho : ℕ → ℂ, r ∈ V →
      (∀ x : ℂ, ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * x ^ j =
        (a r (d r) : ℂ) * ∏ i ∈ Finset.Icc 1 (d r), (x - rho i)) ∧
      ∀ k : ℕ, ∃ q : ℤ, ∑ i ∈ Finset.Icc 1 (d r), ((a r (d r) : ℂ) * rho i) ^ k = (q : ℂ) := by
    intro r
    by_cases hr : r ∈ V
    · obtain ⟨rho, h1, h2⟩ := integer_poly_roots_scaled (a r) (d r) (ha r hr).2.1
      exact ⟨rho, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hr⟩
  choose rho hrho using hex
  have hA0 : ∀ r ∈ V, (a r (d r) : ℂ) ≠ 0 := fun r hr => Int.cast_ne_zero.mpr (ha r hr).2.1
  have hex2 : ∀ r, ∃ i, r ∈ V → i ∈ Finset.Icc 1 (d r) ∧ rho r i = theta r := by
    intro r
    by_cases hr : r ∈ V
    · have h0 := (hrho r hr).1 (theta r)
      rw [(ha r hr).2.2] at h0
      have hp : ∏ i ∈ Finset.Icc 1 (d r), (theta r - rho r i) = 0 :=
        (mul_eq_zero.mp h0.symm).resolve_left (hA0 r hr)
      obtain ⟨i, hi, hi0⟩ := Finset.prod_eq_zero_iff.mp hp
      exact ⟨i, fun _ => ⟨hi, (sub_eq_zero.mp hi0).symm⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose t ht using hex2
  have hA1 : ∀ r ∈ V, (1 : ℝ) ≤ |(a r (d r) : ℝ)| := fun r hr => by
    exact_mod_cast Int.one_le_abs (ha r hr).2.1
  have hh1 : ∀ r ∈ V, 1 ≤ h r := fun r hr => (hA1 r hr).trans ((ha r hr).1 _)
  have hs := intpoly_scale (fun r => a r (d r)) hg fun r hr => (ha r hr).2.1
  set t0 : ℕ → ℕ := fun r => if r ∈ V then t r else default with ht0
  have ht0V : ∀ r ∈ V, t0 r = t r := fun r hr => by simp [ht0, hr]
  have hval : g (fun r => (a r (d r) : ℂ) * rho r (t0 r) / (a r (d r) : ℂ)) = g theta := by
    refine intpoly_eq_on hg fun r hr => ?_
    rw [ht0V r hr, (ht r hr).2, mul_div_cancel_left₀ _ (hA0 r hr)]
  have hmon := intpoly_liouville_monic d (fun r i => (a r (d r) : ℂ) * rho r i) t0
    (fun r => h r * (1 + (d r : ℝ) * h r)) hs
    (fun r k hr => (hrho r hr).2 k)
    (fun r hr i hi => by
      rw [norm_mul, Complex.norm_intCast]
      have hroot : ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * rho r i ^ j = 0 := by
        rw [(hrho r hr).1 (rho r i), Finset.prod_eq_zero hi (sub_self _), mul_zero]
      exact mul_le_mul ((ha r hr).1 _)
        (integer_poly_root_bound (a r) (d r) (h r) (rho r i) (ha r hr).2.1 (ha r hr).1 hroot)
        (norm_nonneg _) (zero_le_one.trans (hh1 r hr)))
    (fun r hr => by
      have := hh1 r hr
      have h2 : 0 ≤ (d r : ℝ) * h r := mul_nonneg (Nat.cast_nonneg _) (by linarith)
      nlinarith)
    (restriction_mem_cartesianProduct fun r hr => (ht r hr).1)
    (by
      change (∏ r ∈ V, (a r (d r) : ℂ) ^ n r) *
        g (fun r => (a r (d r) : ℂ) * rho r (t0 r) / (a r (d r) : ℂ)) ≠ 0
      rw [hval]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun r hr => pow_ne_zero _ (hA0 r hr)) hne)
  change _ ≤ ‖(∏ r ∈ V, (a r (d r) : ℂ) ^ n r) *
    g (fun r => (a r (d r) : ℂ) * rho r (t0 r) / (a r (d r) : ℂ))‖ at hmon
  rw [hval, norm_mul, norm_prod] at hmon
  simp only [norm_pow, Complex.norm_intCast] at hmon
  have hPle : ∏ r ∈ V, |(a r (d r) : ℝ)| ^ n r ≤ ∏ r ∈ V, h r ^ n r :=
    Finset.prod_le_prod₀ (fun r _ => pow_nonneg (abs_nonneg _) _) fun r hr =>
      pow_le_pow_left₀ (abs_nonneg _) ((ha r hr).1 _) _
  have hPpos : 0 < ∏ r ∈ V, |(a r (d r) : ℝ)| ^ n r :=
    Finset.prod_pos fun r hr => pow_pos (zero_lt_one.trans_le (hA1 r hr)) _
  have hQ : 0 ≤ ∏ r ∈ V, (h r * (1 + (d r : ℝ) * h r)) ^ n r :=
    Finset.prod_nonneg fun r hr => by
      have := hh1 r hr
      have h2 : 0 ≤ (d r : ℝ) * h r := mul_nonneg (Nat.cast_nonneg _) (by linarith)
      exact pow_nonneg (mul_nonneg (by linarith) (by linarith)) _
  refine intpoly_aux_liouville_ineq (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _))
    (le_max_left _ _) (max_le_max le_rfl ?_) hPpos hPle hmon
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPle hQ) (intpoly_bound_pos hg)

end RiemannMasullo.Baker
