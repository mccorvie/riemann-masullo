module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.MittagLefflerLift

/-! # Jets of exponential multiples, and their simultaneous realization

Functions `u ↦ exp (c u) P(u)` on `ℝ` with distinct `c` and polynomials `P` are linearly
independent: each lies in a generalized eigenspace of differentiation. Consequently, finitely
many jets at distinct points, of a function `Z` that does not vanish there, are linearly
independent on the family `s ↦ exp (u s) Z(s)`, `u ∈ ℝ`.

If translations `ρ w` of a complete locally convex space multiply a transform `Z` by
`κ w * exp (w s)`, with `|κ w| = 1`, then every array of jets at a discrete set of centers whose
real parts tend to `-∞` is the array of jets of one element, provided the seminorms of the
translates of one element `e₀`, with `Z e₀` nonzero at the centers, grow at most exponentially
as `w → -∞`. The proof combines the finite independence with the Borel–Mittag-Leffler lift
`surjective_coeff_of_eventually_small`: a jet at a center far to the left is realized by a
translate far to the left, which is small.
-/

public section

open Polynomial
open scoped ContDiff

namespace RiemannMasullo

/-- The derivative of `u ↦ exp (c u) P(u)` on the real line. -/
theorem hasDerivAt_cexp_mul_eval (c : ℂ) (P : ℂ[X]) (u : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Complex.exp (c * u) * P.eval (u : ℂ))
      (c * (Complex.exp (c * u) * P.eval (u : ℂ)) +
        Complex.exp (c * u) * (derivative P).eval (u : ℂ)) u := by
  have h1 : HasDerivAt (fun u : ℝ ↦ Complex.exp (c * u)) (Complex.exp (c * u) * c) u := by
    have := (((hasDerivAt_id (u : ℂ)).const_mul c).cexp).comp_ofReal (z := u)
    simpa only [id, mul_one] using this
  have h2 : HasDerivAt (fun u : ℝ ↦ P.eval (u : ℂ)) ((derivative P).eval (u : ℂ)) u :=
    (P.hasDerivAt (u : ℂ)).comp_ofReal
  exact (h1.mul h2).congr_deriv (by ring)

/-- `u ↦ exp (c u) P(u)` is smooth on the real line. -/
theorem contDiff_cexp_mul_eval (c : ℂ) (P : ℂ[X]) :
    ContDiff ℝ ∞ (fun u : ℝ ↦ Complex.exp (c * u) * P.eval (u : ℂ)) := by
  have h1 : ContDiff ℝ ∞ (fun u : ℝ ↦ Complex.exp (c * u)) :=
    ((contDiff_const (c := c)).mul Complex.ofRealCLM.contDiff).cexp
  have hP : ContDiff ℝ ∞ (fun z : ℂ ↦ P.eval z) :=
    ContDiff.restrict_scalars (𝕜 := ℝ) (P.differentiable.contDiff (n := ∞))
  exact h1.mul (hP.comp Complex.ofRealCLM.contDiff)

/-- Exponential polynomials with distinct exponents are linearly independent: if
`∑ c ∈ s, exp (c u) P_c(u) = 0` for every real `u`, every `P_c` vanishes. -/
theorem eq_zero_of_sum_cexp_mul_eval_eq_zero (s : Finset ℂ) (P : ℂ → ℂ[X])
    (h : ∀ u : ℝ, ∑ c ∈ s, Complex.exp (c * u) * (P c).eval (u : ℂ) = 0) :
    ∀ c ∈ s, P c = 0 := by
  classical
  -- Smooth functions form a module on which differentiation acts.
  let smooth : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {f | ContDiff ℝ ∞ f}
      add_mem' := fun {a b} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) ↦
        (show ContDiff ℝ ∞ (a + b) from ha.add hb)
      zero_mem' := (show ContDiff ℝ ∞ (0 : ℝ → ℂ) from contDiff_const)
      smul_mem' := fun c f (hf : ContDiff ℝ ∞ f) ↦ (show ContDiff ℝ ∞ (c • f) from hf.const_smul c) }
  have hdiff (f : smooth) : Differentiable ℝ (f : ℝ → ℂ) :=
    (show ContDiff ℝ ∞ (f : ℝ → ℂ) from f.2).differentiable (by simp)
  let D : Module.End ℂ smooth :=
    { toFun := fun f ↦ ⟨deriv f.1,
        (contDiff_infty_iff_deriv.mp (show ContDiff ℝ ∞ (f : ℝ → ℂ) from f.2)).2⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ deriv_add (hdiff f x) (hdiff g x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ deriv_const_smul c (hdiff f x)) }
  let v (c : ℂ) (P : ℂ[X]) : smooth :=
    ⟨fun u ↦ Complex.exp (c * u) * P.eval (u : ℂ), contDiff_cexp_mul_eval c P⟩
  have hv (c : ℂ) (P : ℂ[X]) : (D - c • 1) (v c P) = v c (derivative P) := by
    ext u
    change deriv (fun u : ℝ ↦ Complex.exp (c * u) * P.eval (u : ℂ)) u -
      c * (Complex.exp (c * u) * P.eval (u : ℂ)) = _
    rw [(hasDerivAt_cexp_mul_eval c P u).deriv]
    ring
  have hmem (c : ℂ) (P : ℂ[X]) : v c P ∈ D.genEigenspace c ⊤ := by
    have hk (k : ℕ) : ((D - c • 1) ^ k) (v c P) = v c (derivative^[k] P) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, hv, Function.iterate_succ_apply']
    have hn : v c P ∈ D.genEigenspace c (P.natDegree + 1 : ℕ) := by
      rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker, hk,
        iterate_derivative_eq_zero (Nat.lt_succ_self _)]
      ext u
      simp [v]
    exact (D.genEigenspace c).mono le_top hn
  have hsum : ∑ c ∈ s, v c (P c) = 0 := by
    ext u
    simpa [v, Submodule.coe_sum] using h u
  intro c hc
  let w : Π₀ c, D.genEigenspace c ⊤ := ∑ c ∈ s, DFinsupp.single c ⟨v c (P c), hmem c (P c)⟩
  have hw : DFinsupp.lsum ℕ (fun c ↦ (D.genEigenspace c ⊤).subtype) w = 0 := by
    simp [w, map_sum, hsum]
  have hw0 : w = 0 := (D.independent_genEigenspace ⊤).dfinsupp_lsum_injective (by rw [hw, map_zero])
  have hwc := DFunLike.congr_fun hw0 c
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single c
    (fun b _ hb ↦ DFinsupp.single_eq_of_ne hb.symm) (fun h ↦ absurd hc h),
    DFinsupp.single_eq_same, DFinsupp.coe_zero, Pi.zero_apply] at hwc
  have hc0 : v c (P c) = 0 := congrArg Subtype.val hwc
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem (f := fun u : ℝ ↦ (u : ℂ)) Complex.ofReal_injective
    fun u ↦ ?_
  have := congrArg (fun f : smooth ↦ (f : ℝ → ℂ) u) hc0
  simp only [v, ZeroMemClass.coe_zero, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero,
    false_or] at this
  exact this

/-- The iterated derivative of `exp (u s) * Z s` at `c`, by the Leibniz rule. -/
theorem iteratedDeriv_exp_mul (u : ℂ) (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z) (n : ℕ) (c : ℂ) :
    iteratedDeriv n (fun s ↦ Complex.exp (u * s) * Z s) c =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (u ^ i * Complex.exp (u * c)) *
        iteratedDeriv (n - i) Z c := by
  have h1 : ContDiffAt ℂ n (fun s ↦ Complex.exp (u * s)) c :=
    (contDiff_const.mul contDiff_id).cexp.contDiffAt
  have h2 : ContDiffAt ℂ n Z c := (hZ.contDiff (n := n)).contDiffAt
  rw [iteratedDeriv_fun_mul h1 h2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_cexp_const_mul]

/-- A combination of jets at distinct points that vanishes on every exponential multiple of a
function that does not vanish at those points is trivial. -/
theorem jets_eq_zero (C : Finset ℂ) (m : ℂ → ℕ) (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (hZc : ∀ c ∈ C, Z c ≠ 0) (a : ℂ → ℕ → ℂ)
    (h : ∀ u : ℝ, ∑ c ∈ C, ∑ n ∈ Finset.range (m c),
      a c n * iteratedDeriv n (fun s ↦ Complex.exp (u * s) * Z s) c = 0) :
    ∀ c ∈ C, ∀ n < m c, a c n = 0 := by
  classical
  let P (c : ℂ) : ℂ[X] := ∑ n ∈ Finset.range (m c), ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (a c n * (n.choose i : ℂ) * iteratedDeriv (n - i) Z c) * X ^ i
  have hP (u : ℝ) (c : ℂ) : ∑ n ∈ Finset.range (m c),
      a c n * iteratedDeriv n (fun s ↦ Complex.exp (u * s) * Z s) c = Complex.exp (c * u) * (P c).eval (u : ℂ) := by
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      Finset.mul_sum, iteratedDeriv_exp_mul (u : ℂ) Z hZ]
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_comm c (u : ℂ)]
    ring
  have hzero := eq_zero_of_sum_cexp_mul_eval_eq_zero C P fun u ↦ by
    rw [← h u]
    exact Finset.sum_congr rfl fun c _ ↦ (hP u c).symm
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨n₀, hn₀, ha₀⟩ := hne
  -- the largest order with a nonzero coefficient
  let T := (Finset.range (m c)).filter fun n ↦ a c n ≠ 0
  have hT : T.Nonempty := ⟨n₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn₀, ha₀⟩⟩
  let N := T.max' hT
  have hNT : N ∈ T := T.max'_mem hT
  have hNa : a c N ≠ 0 := (Finset.mem_filter.mp hNT).2
  have hcoeff := congrArg (fun p : ℂ[X] ↦ p.coeff N) (hzero c hc)
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hcoeff
  rw [Finset.sum_eq_single N] at hcoeff
  · rw [Finset.sum_eq_single N] at hcoeff
    · simp only [coeff_C_mul_X_pow, ↓reduceIte, Nat.choose_self, Nat.cast_one, mul_one,
        Nat.sub_self, iteratedDeriv_zero] at hcoeff
      exact mul_ne_zero hNa (hZc c hc) hcoeff
    · intro i _ hi
      simp [coeff_C_mul_X_pow, Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) h
  · intro n hn hnN
    by_cases hnT : a c n = 0
    · simp [hnT, coeff_C_mul_X_pow]
    have hle : n ≤ N := T.le_max' n (Finset.mem_filter.mpr ⟨hn, hnT⟩)
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have : i ≠ N := by
      rw [Finset.mem_range] at hi
      omega
    simp [coeff_C_mul_X_pow, this.symm]
  · intro h
    exact absurd (Finset.mem_filter.mp hNT).1 h



/-- If no nontrivial combination of finitely many linear functionals vanishes on a family of
vectors, then the span of the family realizes every value vector. -/
theorem exists_mem_span_eval {M ι α : Type*} [AddCommGroup M] [Module ℂ M] [Fintype ι]
    (ℓ : ι → M →ₗ[ℂ] ℂ) (v : α → M)
    (h : ∀ a : ι → ℂ, (∀ x, ∑ i, a i * ℓ i (v x) = 0) → a = 0) (d : ι → ℂ) :
    ∃ x ∈ Submodule.span ℂ (Set.range v), ∀ i, ℓ i x = d i := by
  classical
  let Φ : M →ₗ[ℂ] (ι → ℂ) := LinearMap.pi ℓ
  let W := (Submodule.span ℂ (Set.range v)).map Φ
  suffices hW : W = ⊤ by
    obtain ⟨x, hx, hxd⟩ := (Submodule.mem_map).mp (hW ▸ Submodule.mem_top : d ∈ W)
    exact ⟨x, hx, fun i ↦ congrFun hxd i⟩
  by_contra hne
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
    inferInstance
  let a : ι → ℂ := fun i ↦ f (Pi.single i 1)
  have hfa (y : ι → ℂ) : f y = ∑ i, a i * y i := by
    conv_lhs => rw [show y = ∑ i, y i • Pi.single i (1 : ℂ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, a, mul_comm]
  have ha : a = 0 := h a fun x ↦ by
    have hx : Φ (v x) ∈ W := Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, rfl⟩)
    have : f (Φ (v x)) = 0 := by
      have := Submodule.mem_map_of_mem (f := f) hx
      rw [hfW, Submodule.mem_bot] at this
      exact this
    rw [hfa] at this
    simpa [Φ] using this
  apply hf
  refine LinearMap.ext fun y ↦ ?_
  rw [hfa]
  simp [ha]



/-- Leibniz for `exp (w s) * g s` when the jets of `g` below order `n` vanish at `c`. -/
theorem iteratedDeriv_exp_mul_of_lower (w : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) (c : ℂ)
    (n : ℕ) (h : ∀ k < n, iteratedDeriv k g c = 0) :
    iteratedDeriv n (fun s ↦ Complex.exp (w * s) * g s) c =
      Complex.exp (w * c) * iteratedDeriv n g c := by
  rw [iteratedDeriv_exp_mul w g hg n c, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [Finset.mem_range] at hi
    rw [h (n - i) (by omega), mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0



/-- `jets_eq_zero` for a combination indexed by a finite set of (center, order) pairs. -/
theorem jets_combo_eq_zero (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z) (T : Finset (ℂ × ℕ))
    (hZc : ∀ j ∈ T, Z j.1 ≠ 0) (a : ℂ × ℕ → ℂ)
    (h : ∀ u : ℝ, ∑ j ∈ T, a j * iteratedDeriv j.2 (fun s ↦ Complex.exp (u * s) * Z s) j.1 = 0) :
    ∀ j ∈ T, a j = 0 := by
  classical
  let C := T.image Prod.fst
  let M := T.sup Prod.snd + 1
  let A (c : ℂ) (n : ℕ) : ℂ := if (c, n) ∈ T then a (c, n) else 0
  have hsub : T ⊆ C ×ˢ Finset.range M := fun j hj ↦ Finset.mem_product.mpr
    ⟨Finset.mem_image_of_mem _ hj, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hj))⟩
  have key := jets_eq_zero C (fun _ ↦ M) Z hZ
    (fun c hc ↦ by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      exact hZc j hj) A
    (fun u ↦ by
      rw [← h u, ← Finset.sum_product' (f := fun c n ↦ A c n *
        iteratedDeriv n (fun s ↦ Complex.exp (u * s) * Z s) c)]
      simp only [A, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub])
  intro j hj
  have := key j.1 (Finset.mem_image_of_mem _ hj) j.2
    (Finset.mem_range.mp (Finset.mem_product.mp (hsub hj)).2)
  simpa [A, hj] using this



open Filter Topology

/-- Finite realization from translates: any values on a finite set of jets are attained in the
span of the translates of `e₀`. -/
theorem exists_span_translates {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ℝ → E →ₗ[ℂ] E) (Z : E → ℂ → ℂ) (jet : ℂ → ℕ → E →ₗ[ℂ] ℂ)
    (hjet : ∀ c n x, jet c n x = iteratedDeriv n (Z x) c)
    (κ : ℝ → ℂ) (hκ : ∀ w, κ w ≠ 0)
    (hZρ : ∀ w x s, Z (ρ w x) s = κ w * (Complex.exp (w * s) * Z x s))
    (e₀ : E) (he₀d : Differentiable ℂ (Z e₀)) {J : Type*} (val : J → ℂ × ℕ)
    (hval : Function.Injective val) (he₀ : ∀ j, Z e₀ (val j).1 ≠ 0) (T : Finset J) (d : J → ℂ) :
    ∃ x ∈ Submodule.span ℂ (Set.range fun u : ℝ ↦ ρ u e₀),
      ∀ j ∈ T, jet (val j).1 (val j).2 x = d j := by
  classical
  obtain ⟨x, hx, hxd⟩ := exists_mem_span_eval (ι := T)
    (fun t ↦ jet (val t.1).1 (val t.1).2) (fun u : ℝ ↦ ρ u e₀)
    (fun a ha ↦ by
      let D (u : ℝ) (p : ℂ × ℕ) := iteratedDeriv p.2 (fun s ↦ Complex.exp (u * s) * Z e₀ s) p.1
      have hjρ (u : ℝ) (p : ℂ × ℕ) : jet p.1 p.2 (ρ u e₀) = κ u * D u p := by
        rw [hjet]
        have : Z (ρ u e₀) = fun s ↦ κ u * (Complex.exp (u * s) * Z e₀ s) :=
          funext (hZρ u e₀)
        rw [this, iteratedDeriv_const_mul_field]
      let a' (p : ℂ × ℕ) : ℂ := ∑ t ∈ T.attach.filter (fun t ↦ val t.1 = p), a t
      have hsum (u : ℝ) : ∑ p ∈ T.image val, a' p * D u p = 0 := by
        have h1 := ha u
        simp only [hjρ] at h1
        have h2 : ∑ t : T, a t * D u (val t.1) = 0 := by
          have := congrArg (fun z ↦ (κ u)⁻¹ * z) h1
          simp only [mul_zero, Finset.mul_sum] at this
          rw [← this]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          field_simp [hκ u]
        rw [← h2, ← Finset.attach_eq_univ, ← Finset.sum_fiberwise_of_maps_to
          (s := T.attach) (t := T.image val) (g := fun t ↦ val t.1)
          (fun t _ ↦ Finset.mem_image_of_mem _ t.2)]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        simp only [a', Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht ↦ ?_
        rw [(Finset.mem_filter.mp ht).2]
      have hz := jets_combo_eq_zero (Z e₀) he₀d (T.image val)
        (fun p hp ↦ by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
          exact he₀ j) a' hsum
      funext t
      show a t = 0
      have := hz (val t.1) (Finset.mem_image_of_mem _ t.2)
      simp only [a'] at this
      rw [Finset.sum_eq_single t (fun b hb hbt ↦ absurd
        (Subtype.ext (hval (Finset.mem_filter.mp hb).2)) hbt)
        (fun h ↦ absurd (Finset.mem_filter.mpr ⟨Finset.mem_attach T t, rfl⟩ :
          t ∈ T.attach.filter fun b ↦ val b.1 = val t.1) h)] at this
      exact this) (fun t ↦ d t.1)
  exact ⟨x, hx, fun j hj ↦ hxd ⟨j, hj⟩⟩



/-- Simultaneous realization of all jets from translates of one element, by the
Borel–Mittag-Leffler lift. -/
theorem realize_of_translates {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [CompleteSpace E] [FirstCountableTopology E] [PolynormableSpace ℂ E]
    (ρ : ℝ → E →L[ℂ] E) (hρ : ∀ u w x, ρ w (ρ u x) = ρ (w + u) x)
    (Z : E → ℂ → ℂ) (hZd : ∀ x, Differentiable ℂ (Z x))
    (jet : ℂ → ℕ → E →L[ℂ] ℂ) (hjet : ∀ c n x, jet c n x = iteratedDeriv n (Z x) c)
    (κ : ℝ → ℂ) (hκ : ∀ w, ‖κ w‖ = 1)
    (hZρ : ∀ w x s, Z (ρ w x) s = κ w * (Complex.exp (w * s) * Z x s))
    (m : ℂ → ℕ) (M : ℕ) (hM : ∀ c, m c ≤ M)
    (hfin : ∀ R : ℝ, {c : ℂ | 0 < m c ∧ R ≤ c.re}.Finite)
    (e₀ : E) (he₀ : ∀ c, 0 < m c → Z e₀ c ≠ 0)
    (hgrowth : ∀ q : Seminorm ℂ E, Continuous q → ∃ N C : ℝ, ∀ v ≤ (0 : ℝ),
      q (ρ v e₀) ≤ C * Real.exp (-(N * v)))
    (y : {j : ℂ × ℕ // j.2 < m j.1} → ℂ) :
    ∃ x : E, ∀ j : {j : ℂ × ℕ // j.2 < m j.1}, jet j.1.1 j.1.2 x = y j := by
  classical
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  have hκ0 (w : ℝ) : κ w ≠ 0 := fun h ↦ by simpa [h] using hκ w
  have hpos (j : J) : 0 < m j.1.1 := lt_of_le_of_lt (Nat.zero_le _) j.2
  -- The centers are countable.
  have hcount : {c : ℂ | 0 < m c}.Countable := by
    have : {c : ℂ | 0 < m c} = ⋃ n : ℕ, {c : ℂ | 0 < m c ∧ (-(n : ℝ)) ≤ c.re} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge (-c.re)
        exact ⟨n, h, by linarith⟩
      · rintro ⟨n, h, -⟩
        exact h
    rw [this]
    exact Set.countable_iUnion fun n ↦ (hfin _).countable
  have := hcount.to_subtype
  obtain ⟨idx, hidx⟩ := exists_injective_nat {c : ℂ | 0 < m c}
  let key : J → ℕ := fun j ↦ idx ⟨j.1.1, hpos j⟩ * (M + 1) + j.1.2
  have hord (j : J) : j.1.2 < M + 1 := Nat.lt_succ_of_le ((j.2.le).trans (hM _))
  have hkey : Function.Injective key := by
    intro j j' h
    have hd := congrArg (· / (M + 1)) h
    have hm := congrArg (· % (M + 1)) h
    simp only [key] at hd hm
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.succ_pos M), Nat.div_eq_of_lt (hord j), add_zero,
      Nat.mul_comm, Nat.mul_add_div (Nat.succ_pos M), Nat.div_eq_of_lt (hord j'),
      add_zero] at hd
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (hord j), Nat.mul_comm,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (hord j')] at hm
    have hc := congrArg Subtype.val (hidx hd)
    exact Subtype.ext (Prod.ext hc hm)
  -- Lower orders at the same center come first.
  have hkey_lt (j : J) (n : ℕ) (hn : n < j.1.2) :
      key ⟨(j.1.1, n), hn.trans j.2⟩ < key j := by
    simp only [key]
    omega
  let ι : ℕ → Type _ := fun k ↦ {j : J // key j = k}
  let L : (k : ℕ) → ι k → E →L[ℂ] ℂ := fun k i ↦ jet i.1.1.1 i.1.1.2
  have hfinT (k : ℕ) : {j : J | key j ≤ k}.Finite :=
    (Set.finite_Iic k).preimage hkey.injOn
  -- finite realization on all levels up to `k`
  have real (k : ℕ) (d : J → ℂ) : ∃ x ∈ Submodule.span ℂ (Set.range fun u : ℝ ↦ ρ u e₀),
      ∀ j : J, key j ≤ k → jet j.1.1 j.1.2 x = d j := by
    obtain ⟨x, hx, hxd⟩ := exists_span_translates (fun u ↦ (ρ u).toLinearMap) Z
      (fun c n ↦ (jet c n).toLinearMap) hjet κ hκ0 hZρ e₀ (hZd e₀) (fun j : J ↦ j.1)
      Subtype.val_injective (fun j ↦ he₀ _ (hpos j)) (hfinT k).toFinset d
    exact ⟨x, hx, fun j hj ↦ hxd j ((hfinT k).mem_toFinset.mpr hj)⟩
  have h1 : ∀ k (d : ι k → ℂ), ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ ∀ i, L k i x = d i := by
    intro k d
    obtain ⟨x, -, hx⟩ := real k fun j ↦ if h : key j = k then d ⟨j, h⟩ else 0
    refine ⟨x, fun j hj i ↦ ?_, fun i ↦ ?_⟩
    · have h1 : key i.1 ≤ k := by rw [i.2]; exact hj.le
      have h2 : key i.1 ≠ k := by rw [i.2]; exact hj.ne
      rw [show L j i x = _ from hx i.1 h1, dite_eq_right h2]
    · rw [show L k i x = _ from hx i.1 i.2.le, dite_eq_left i.2]
  have h2 : ∀ q : Seminorm ℂ E, Continuous q → ∃ K, ∀ k ≥ K, ∀ (d : ι k → ℂ) (ε : ℝ), 0 < ε →
      ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ (∀ i, L k i x = d i) ∧ q x < ε := by
    intro q hq
    obtain ⟨N, C, hC⟩ := hgrowth q hq
    have hB : {j : J | -(N + 1) < j.1.1.re}.Finite := by
      have hS := (hfin (-(N + 1))).prod (Set.finite_Iio (M + 1))
      refine (hS.preimage Subtype.val_injective.injOn).subset fun j hj ↦ ?_
      exact ⟨⟨hpos j, le_of_lt hj⟩, hord j⟩
    obtain ⟨K0, hK0⟩ := (hB.image key).bddAbove
    refine ⟨K0 + 1, fun k hk d ε hε ↦ ?_⟩
    by_cases hk' : ∃ j : J, key j = k
    swap
    · exact ⟨0, fun j _ i ↦ map_zero _, fun i ↦ absurd ⟨i.1, i.2⟩ hk', by simpa using hε⟩
    obtain ⟨j0, hj0⟩ := hk'
    have hre : j0.1.1.re ≤ -(N + 1) := by
      by_contra h
      push Not at h
      have := hK0 ⟨j0, h, hj0⟩
      omega
    obtain ⟨y0, hy0, hy⟩ := real k fun j ↦ if key j = k then 1 else 0
    have hZy (w : ℝ) : Z (ρ w y0) = fun s ↦ κ w * (Complex.exp (w * s) * Z y0 s) :=
      funext (hZρ w y0)
    have hlow (j : J) (hj : key j < k) (w : ℝ) : jet j.1.1 j.1.2 (ρ w y0) = 0 := by
      rw [hjet, hZy, iteratedDeriv_const_mul_field,
        iteratedDeriv_exp_mul_of_lower _ _ (hZd y0) _ _ (fun n hn ↦ ?_)]
      · rw [← hjet, hy j hj.le, ite_eq_right hj.ne, mul_zero, mul_zero]
      · have hlt := hkey_lt j n hn
        rw [← hjet, hy ⟨(j.1.1, n), hn.trans j.2⟩ (hlt.trans hj).le, ite_eq_right (hlt.trans hj).ne]
    have htop (w : ℝ) : jet j0.1.1 j0.1.2 (ρ w y0) = κ w * Complex.exp (w * j0.1.1) := by
      rw [hjet, hZy, iteratedDeriv_const_mul_field,
        iteratedDeriv_exp_mul_of_lower _ _ (hZd y0) _ _ (fun n hn ↦ ?_)]
      · rw [← hjet, hy j0 hj0.le, ite_eq_left hj0, mul_one]
      · have hlt := hkey_lt j0 n hn
        rw [← hjet, hy ⟨(j0.1.1, n), hn.trans j0.2⟩ (hlt.trans_eq hj0).le,
          ite_eq_right (hlt.trans_eq hj0).ne]
    let i0 : ι k := ⟨j0, hj0⟩
    obtain ⟨lam, hlam⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy0
    let U := lam.support
    let S : ℝ := ∑ u ∈ U, ‖lam u‖ * Real.exp (-(N * u))
    let A : ℝ := ‖d i0‖ * |C| * S
    have hA : 0 ≤ A := by positivity
    let w : ℝ := min (min 0 (-(∑ u ∈ U, |u|))) (Real.log (ε / (A + 1)))
    have hw0 : w ≤ 0 := (min_le_left _ _).trans (min_le_left _ _)
    have hwu (u : ℝ) (hu : u ∈ U) : w + u ≤ 0 := by
      have h1 : w ≤ -(∑ u ∈ U, |u|) := (min_le_left _ _).trans (min_le_right _ _)
      have h2 : u ≤ ∑ u ∈ U, |u| := (le_abs_self u).trans
        (Finset.single_le_sum (f := fun u ↦ |u|) (fun _ _ ↦ abs_nonneg _) hu)
      linarith
    have hwlog : Real.exp w ≤ ε / (A + 1) := by
      calc Real.exp w ≤ Real.exp (Real.log (ε / (A + 1))) :=
            Real.exp_le_exp.mpr (min_le_right _ _)
        _ = ε / (A + 1) := Real.exp_log (by positivity)
    let coef : ℂ := d i0 / (κ w * Complex.exp (w * j0.1.1))
    have hden : κ w * Complex.exp (w * j0.1.1) ≠ 0 := mul_ne_zero (hκ0 w) (Complex.exp_ne_zero _)
    refine ⟨coef • ρ w y0, fun j hj i ↦ ?_, fun i ↦ ?_, ?_⟩
    · have hi : key i.1 < k := by rw [i.2]; exact hj
      change jet i.1.1.1 i.1.1.2 (coef • ρ w y0) = 0
      rw [map_smul, hlow i.1 hi w, smul_zero]
    · have hi : i.1 = j0 := hkey (i.2.trans hj0.symm)
      change jet i.1.1.1 i.1.1.2 (coef • ρ w y0) = d i
      rw [map_smul, hi, htop, smul_eq_mul, show d i = d i0 from congrArg d (Subtype.ext hi)]
      exact div_mul_cancel₀ (d i0) hden
    · have hy0' : ρ w y0 = ∑ u ∈ U, lam u • ρ (w + u) e₀ := by
        rw [← hlam, Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [map_smul, hρ]
      have hq1 : q (ρ w y0) ≤ ∑ u ∈ U, ‖lam u‖ * (C * Real.exp (-(N * (w + u)))) := by
        rw [hy0']
        refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans
          (Finset.sum_le_sum fun u hu ↦ ?_)
        rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hC _ (hwu u hu)) (norm_nonneg _)
      have hsumC : ∑ u ∈ U, ‖lam u‖ * (C * Real.exp (-(N * (w + u)))) ≤
          |C| * Real.exp (-(N * w)) * S := by
        simp only [S, Finset.mul_sum]
        refine Finset.sum_le_sum fun u _ ↦ ?_
        have he : Real.exp (-(N * (w + u))) = Real.exp (-(N * w)) * Real.exp (-(N * u)) := by
          rw [← Real.exp_add]
          ring_nf
        rw [he]
        have h4 : 0 ≤ ‖lam u‖ * (Real.exp (-(N * w)) * Real.exp (-(N * u))) := by positivity
        nlinarith [le_abs_self C]
      have hnorm : ‖coef‖ = ‖d i0‖ * Real.exp (-(w * j0.1.1.re)) := by
        simp only [coef, norm_div, norm_mul, hκ, one_mul, Complex.norm_exp,
          Complex.re_ofReal_mul]
        rw [Real.exp_neg, div_eq_mul_inv]
      have hexp : -(w * (j0.1.1.re + N)) ≤ w := by nlinarith
      calc q (coef • ρ w y0) = ‖coef‖ * q (ρ w y0) := map_smul_eq_mul _ _ _
        _ ≤ ‖coef‖ * (|C| * Real.exp (-(N * w)) * S) :=
          mul_le_mul_of_nonneg_left (hq1.trans hsumC) (norm_nonneg _)
        _ = A * Real.exp (-(w * (j0.1.1.re + N))) := by
          rw [hnorm, show -(w * (j0.1.1.re + N)) = -(w * j0.1.1.re) + -(N * w) by ring,
            Real.exp_add]
          simp only [A]
          ring
        _ ≤ A * Real.exp w := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hA
        _ ≤ A * (ε / (A + 1)) := mul_le_mul_of_nonneg_left hwlog hA
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨x, hx⟩ := surjective_coeff_of_eventually_small L h1 h2
    (fun k i ↦ y i.1)
  exact ⟨x, fun j ↦ congrFun (congrFun hx (key j)) ⟨j, rfl⟩⟩


end RiemannMasullo
