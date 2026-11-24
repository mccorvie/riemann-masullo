module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# §§14.2–14.3: Global function fields and higher rank

Masullo, pp. 534–536. The Euler product (14.2.0.1) uses every closed point of
the smooth projective curve, including those above infinity for a map to the
projective line.
-/

@[expose] public section

namespace RiemannMasullo

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Paper: (14.2.0.1), p. 534. The local factor at a closed point, in the
complex parameter on the covering plane. -/
noncomputable def curveZetaEulerFactor (x : closedPoints X) (s : ℂ) : ℂ :=
  (1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s))⁻¹

/-- Paper: (14.2.0.1), p. 534. The zeta Euler product of a smooth projective
geometrically connected curve over a finite field multiplies the reciprocal
factors determined by the sizes of the residue fields of its closed points.
Deviation: The product is defined on `Re(s) > 1`, its half-plane of absolute
convergence. A smooth proper curve over a field is projective. -/
noncomputable def curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' x : closedPoints X, curveZetaEulerFactor x s.val

/-- Paper: (14.2.0.1), p. 534. On `Re(s) > 1` the finite products over closed
points converge to the zeta Euler product.
Deviation: `HasProd` asserts convergence of the product in the display. -/
theorem hasProd_curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun x : closedPoints X ↦ curveZetaEulerFactor x s.val)
      (curveZetaEulerProduct f s) := by sorry

/-- Paper: (14.2.0.1), p. 534. The product converges absolutely on its
half-plane of definition. -/
theorem summable_curveZetaEulerFactor_sub_one (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    Summable (fun x : closedPoints X ↦ ‖curveZetaEulerFactor x s.val - 1‖) := by sorry

/-- The order of `exp w - 1` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_exp_sub_one (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => Complex.exp s - 1) w = 1 := by
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ) (f := fun x : ℂ => x)
    (g := fun s : ℂ => Complex.exp s - 1) (x := w)
    (analyticAt_cexp.sub analyticAt_const) (by simp [Complex.deriv_exp, hw])
  simp only [Function.comp_def] at hcomp
  rw [hcomp, show Complex.exp w - 1 = 0 from by rw [hw]; ring]
  exact meromorphicOrderAt_id (𝕜 := ℂ)

/-- The order of `1 - exp w` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_one_sub_exp (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => 1 - Complex.exp s) w = 1 := by
  have h := meromorphicOrderAt_exp_sub_one w hw
  have hneg : meromorphicOrderAt (fun s : ℂ => -(Complex.exp s - 1)) w = 1 := by
    rw [← meromorphicOrderAt_fun_neg (f := fun s : ℂ => Complex.exp s - 1) (x := w)]
    exact h
  rw [show (fun s : ℂ => 1 - Complex.exp s) = fun s : ℂ => -(Complex.exp s - 1) from by
    funext s; ring]
  exact hneg

/-- The reciprocal local factor `(1 - exp w)⁻¹` has a simple pole at `w`. -/
private lemma meromorphicOrderAt_one_sub_exp_inv (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp s)⁻¹) w = -1 := by
  have h := meromorphicOrderAt_one_sub_exp w hw
  have hfun : (fun s : ℂ => (1 - Complex.exp s)⁻¹) = (fun s : ℂ => 1 - Complex.exp s)⁻¹ := rfl
  rw [hfun, meromorphicOrderAt_inv, h]

/-- Composing with the affine substitution `s ↦ -(s * L)` (`L ≠ 0`) transports the pole. -/
private lemma meromorphicOrderAt_one_sub_exp_inv_affine (L : ℝ) (hL : L ≠ 0) (z : ℂ)
    (hz : Complex.exp (-(z * (L : ℂ))) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp (-(s * (L : ℂ))))⁻¹) z = -1 := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ)
    (f := fun s : ℂ => (1 - Complex.exp s)⁻¹) (g := fun s : ℂ => -(s * (L : ℂ))) (x := z)
    (by fun_prop) (by simp [hL])
  simp only [Function.comp_def] at h
  rw [h]
  exact meromorphicOrderAt_one_sub_exp_inv _ hz

/-- The complex power of a positive natural number, written through the exponential. -/
private lemma natCast_cpow_eq_exp (c : ℕ) (hc : c ≠ 0) (z : ℂ) :
    (c : ℂ) ^ (-z) = Complex.exp (-(z * (Real.log c : ℂ))) := by
  have hc0 : (c : ℂ) ≠ 0 := by simpa using hc
  rw [Complex.cpow_def_of_ne_zero hc0, Complex.natCast_log]
  ring_nf

/-- A single local factor `(1 - c ^ (-s))⁻¹` with `c ≥ 2` has a simple pole at every `z`
where `c ^ (-z) = 1`. -/
private lemma meromorphicOrderAt_cpow_factor (c : ℕ) (hc : 2 ≤ c) (z : ℂ)
    (hz : (c : ℂ) ^ (-z) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) z = -1 := by
  have hc0 : c ≠ 0 := by omega
  have hL : Real.log c ≠ 0 := by
    have h1 : (1 : ℝ) < c := by exact_mod_cast hc
    exact ne_of_gt (Real.log_pos h1)
  have hz' : Complex.exp (-(z * (Real.log c : ℂ))) = 1 := by
    rw [← natCast_cpow_eq_exp c hc0 z]
    exact hz
  have hfun : (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) =
      fun s : ℂ => (1 - Complex.exp (-(s * (Real.log c : ℂ))))⁻¹ := by
    funext s
    rw [natCast_cpow_eq_exp c hc0 s]
  rw [hfun]
  exact meromorphicOrderAt_one_sub_exp_inv_affine _ hL z hz'

/-- The residue field of a closed point of a curve over a finite field is a finite extension
of the base field, so its cardinality is a positive power of `Nat.card k`. -/
private theorem closedPoint_residueField_card_pow (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : x ∈ closedPoints X) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card (X.residueField x) = Nat.card k ^ m := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (f := f) (n := 1)
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hclosed : IsClosed ({x} : Set X) := hx
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_locallyOfFiniteType (X := X)).mp hclosed
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (X.fromSpecResidueField x ≫ f)
  have h2' : LocallyOfFiniteType (Spec.homEquiv.symm φ) := hφ ▸ h2
  have h3 : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp h2'
  algebraize [φ.hom]
  haveI : Algebra.FiniteType k (X.residueField x) := h3
  haveI : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing k (X.residueField x)
  haveI : Finite (X.residueField x) := Module.finite_of_finite k (M := X.residueField x)
  have hcard : Nat.card (X.residueField x) = Nat.card k ^ Module.finrank k (X.residueField x) :=
    Module.natCard_eq_pow_finrank (K := k) (V := X.residueField x)
  refine ⟨Module.finrank k (X.residueField x), ?_, hcard⟩
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (X.residueField x) := Fintype.ofFinite _
  have hq : 2 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hc : 2 ≤ Nat.card (X.residueField x) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hlt
  have h0 : Module.finrank k (X.residueField x) = 0 := by omega
  rw [h0, pow_zero] at hcard
  omega

/-- Paper: §14.2, p. 534. For a finite set of closed points every local
factor has a simple pole at each integral multiple of the imaginary period.
The product has pole order equal to the number of places. -/
theorem curveZetaEulerFactor_prod_order (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (S : Finset (closedPoints X)) (n : ℤ) :
    meromorphicOrderAt (fun s : ℂ ↦ ∏ x ∈ S, curveZetaEulerFactor x s)
      (2 * Real.pi * Complex.I * n / Real.log (Nat.card k)) = -(S.card : ℤ) := by
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hlogk : Real.log (Nat.card k) ≠ 0 := by
    have h1 : (1 : ℝ) < Nat.card k := by exact_mod_cast hq
    exact ne_of_gt (Real.log_pos h1)
  set s0 : ℂ := 2 * Real.pi * Complex.I * n / Real.log (Nat.card k) with hs0
  have hkey : ∀ x ∈ S, meromorphicOrderAt (curveZetaEulerFactor x) s0 = -1 := by
    intro x _
    obtain ⟨m, hm1, hm⟩ := closedPoint_residueField_card_pow f x.2
    have hc2 : 2 ≤ Nat.card (X.residueField x.val) := by
      rw [hm]
      exact le_trans hq (le_self_pow (by omega) (by omega))
    have hval : (Nat.card (X.residueField x.val) : ℂ) ^ (-s0) = 1 := by
      have hc0 : Nat.card (X.residueField x.val) ≠ 0 := by omega
      have hlogc : Real.log (Nat.card (X.residueField x.val)) =
          (m : ℝ) * Real.log (Nat.card k) := by
        rw [hm, Nat.cast_pow, Real.log_pow]
      rw [natCast_cpow_eq_exp _ hc0, hlogc, hs0]
      push_cast
      have hlk : Complex.log ((Nat.card k : ℕ) : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        exact_mod_cast hlogk
      have harg : -((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / Complex.log ((Nat.card k : ℕ) : ℂ)) *
            ((m : ℂ) * Complex.log ((Nat.card k : ℕ) : ℂ))) =
          ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
        push_cast
        ring
      rw [harg]
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(n * (m : ℤ)))
    exact meromorphicOrderAt_cpow_factor _ hc2 s0 hval
  rw [meromorphicOrderAt_fun_prod fun x hx =>
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hkey x hx]; norm_num)]
  rw [Finset.sum_congr rfl hkey, Finset.sum_const]
  norm_num

-- TODO(paper-gap): Page 534 does not construct the function-field Sobolev
-- quotient or show that the trace approximation requires one Mellin test to
-- cancel all finite-stage poles. Under T = q^(-s) these lifts give one point.

/-- Paper: §14.2, last paragraph, p. 534. For each degree there are finitely
many closed points whose residue field has that degree over the base field.
Deviation: Page 534 says that the factors repeat "infinitely many times". The
number at each fixed degree is finite, and p. 535 estimates it; it grows as the
degree tends to infinity. -/
theorem curveZeta_closedPointsOfDegree_finite (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Finite := by sorry

/-- Paper: §14.2, p. 535. The number of closed points of degree m over k. -/
noncomputable def curveZetaClosedPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) : ℕ :=
  {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ m}.ncard

/-- Paper: §14.2, p. 535. A closed point of degree d contributes d rational
points over an extension of degree m exactly when d divides m.
Deviation: Uses the exact counting identity behind the printed upper bound. -/
theorem curveZeta_extensionPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (K : Type u) [Field K] [Algebra k K] [Finite K] :
    Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by sorry

/-- Paper: §14.2, p. 535. The number of degree-m closed points is
q^m/m with error O(q^(m/2)/m) as m tends to infinity.
Deviation: The Big-O constant here is for the given curve. The paper also
specifies uniformity in the curve through its genus. -/
theorem curveZeta_closedPointsOfDegree_asymptotic (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    let q : ℝ := Nat.card k
    (fun m : ℕ ↦ (curveZetaClosedPointCount f m : ℝ) - q ^ m / m) =O[Filter.atTop]
      (fun m : ℕ ↦ Real.sqrt (q ^ m) / m) := by sorry

/-- A geometric sum in the base `q ≥ 2` is at most twice its last term. -/
private theorem curveZeta_closedPointsOfDegree_bound_of_weil_geom (q : ℝ) (hq : 2 ≤ q) (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, q ^ b ≤ 2 * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    have h0 : 0 ≤ q ^ n := by positivity
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hq)]

/-- The sum of `√(q^b)` for `b ≤ n` is at most `2 q^n` when `q ≥ 2`. -/
private theorem curveZeta_closedPointsOfDegree_bound_of_weil_geom_sqrt (q : ℝ) (hq : 2 ≤ q)
    (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, Real.sqrt (q ^ b) ≤ 2 * q ^ n := by
  have hs := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hs0 := Real.sqrt_nonneg q
  have hs1 : 1 ≤ Real.sqrt q := by nlinarith
  have hc : 2 + Real.sqrt q ≤ 2 * q := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ, Real.sqrt_mul (by positivity)]
    have h1 : 1 ≤ q ^ n := one_le_pow₀ (by linarith)
    have hX : Real.sqrt (q ^ n) ≤ q ^ n := by
      calc Real.sqrt (q ^ n) ≤ Real.sqrt ((q ^ n) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = q ^ n := Real.sqrt_sq (by positivity)
    calc ∑ b ∈ Finset.Icc 1 n, Real.sqrt (q ^ b) + Real.sqrt (q ^ n) * Real.sqrt q
        ≤ 2 * q ^ n + q ^ n * Real.sqrt q := add_le_add ih (mul_le_mul_of_nonneg_right hX hs0)
      _ = q ^ n * (2 + Real.sqrt q) := by ring
      _ ≤ q ^ n * (2 * q) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 * (q ^ n * q) := by ring

/-- Möbius inversion of the point counts, with the Weil bound as a hypothesis. -/
private theorem curveZeta_closedPointsOfDegree_bound_of_weil_aux (q g : ℝ) (P : ℕ → ℝ)
    (hq : 2 ≤ q) (hg : 0 ≤ g)
    (hW : ∀ r : ℕ, 0 < r →
      |∑ d ∈ r.divisors, (d : ℝ) * P d - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r))
    (m : ℕ) (hm : 0 < m) :
    |P m - q ^ m / m| ≤ (5 + 6 * g) * Real.sqrt (q ^ m) / m := by
  classical
  let N : ℕ → ℝ := fun r ↦ ∑ d ∈ r.divisors, (d : ℝ) * P d
  let E : ℕ → ℝ := fun r ↦ N r - (q ^ r + 1)
  have hEb : ∀ r, 0 < r → |E r| ≤ 2 * g * Real.sqrt (q ^ r) := hW
  have hsum : ∀ r > 0, ∑ i ∈ r.divisors, (((i : ℕ) : ℝ) * P i - if i = 1 then 1 else 0) =
      N r - 1 := by
    intro r hr
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp [hr.ne', N]
  have hinv := ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mp hsum m hm
  have h2 : ∑ i ∈ m.divisors, ((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ) * (N i - 1) =
      (m : ℝ) * P m - if m = 1 then 1 else 0 := by
    rw [← hinv]
    simp only [zsmul_eq_mul]
    exact (Nat.sum_divisorsAntidiagonal'
      (fun a b ↦ ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (N b - 1))).symm
  rw [← Nat.cons_self_properDivisors hm.ne', Finset.sum_cons, Nat.div_self hm,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul] at h2
  set T := ∑ i ∈ m.properDivisors, ((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ) * (N i - 1)
    with hTdef
  have hmain : (m : ℝ) * P m - q ^ m = (if m = 1 then 1 else 0) + E m + T := by
    simp only [E]
    linarith
  have hsub : m.properDivisors ⊆ Finset.Icc 1 (m / 2) := by
    intro i hi
    obtain ⟨⟨c, hc⟩, hlt⟩ := Nat.mem_properDivisors.mp hi
    have hi0 : 0 < i := Nat.pos_of_mem_properDivisors hi
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc
        omega
      · simp at hc
        omega
      · omega
    rw [Finset.mem_Icc, Nat.le_div_iff_mul_le (by norm_num)]
    exact ⟨hi0, hc ▸ Nat.mul_le_mul_left i hc2⟩
  have hhalf : q ^ (m / 2) ≤ Real.sqrt (q ^ m) := by
    calc q ^ (m / 2) = Real.sqrt ((q ^ (m / 2)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (q ^ m) := Real.sqrt_le_sqrt (by
          rw [← pow_mul]
          exact pow_le_pow_right₀ (by linarith) (by omega))
  have hT : |T| ≤ ∑ i ∈ m.properDivisors, (q ^ i + 2 * g * Real.sqrt (q ^ i)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    have hi0 : 0 < i := Nat.pos_of_mem_properDivisors hi
    have hμ : |((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hN : |N i - 1| ≤ q ^ i + 2 * g * Real.sqrt (q ^ i) := by
      have h := hEb i hi0
      calc |N i - 1| = |q ^ i + E i| := by
            congr 1
            simp only [E]
            ring
        _ ≤ |q ^ i| + |E i| := abs_add_le _ _
        _ ≤ q ^ i + 2 * g * Real.sqrt (q ^ i) := by
            rw [abs_of_nonneg (by positivity)]
            linarith
    rw [abs_mul]
    calc |((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ)| * |N i - 1|
        ≤ 1 * (q ^ i + 2 * g * Real.sqrt (q ^ i)) :=
          mul_le_mul hμ hN (abs_nonneg _) zero_le_one
      _ = q ^ i + 2 * g * Real.sqrt (q ^ i) := one_mul _
  have hS1 : ∑ i ∈ m.properDivisors, q ^ i ≤ 2 * Real.sqrt (q ^ m) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans
      ((curveZeta_closedPointsOfDegree_bound_of_weil_geom q hq _).trans (by linarith))
  have hS2 : ∑ i ∈ m.properDivisors, Real.sqrt (q ^ i) ≤ 2 * Real.sqrt (q ^ m) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Real.sqrt_nonneg _).trans
      ((curveZeta_closedPointsOfDegree_bound_of_weil_geom_sqrt q hq _).trans (by linarith))
  have hsplit : ∑ i ∈ m.properDivisors, (q ^ i + 2 * g * Real.sqrt (q ^ i)) =
      ∑ i ∈ m.properDivisors, q ^ i + 2 * g * ∑ i ∈ m.properDivisors, Real.sqrt (q ^ i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hone : 1 ≤ Real.sqrt (q ^ m) := Real.one_le_sqrt.mpr (one_le_pow₀ (by linarith))
  have hite : |(if m = 1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have key : |(m : ℝ) * P m - q ^ m| ≤ (5 + 6 * g) * Real.sqrt (q ^ m) := by
    rw [hmain]
    have h3 := abs_add_three (if m = 1 then (1 : ℝ) else 0) (E m) T
    have hE := hEb m hm
    nlinarith [mul_le_mul_of_nonneg_left hS2 (by linarith : (0 : ℝ) ≤ 2 * g)]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [show P m - q ^ m / m = ((m : ℝ) * P m - q ^ m) / m by field_simp, abs_div,
    abs_of_pos hm']
  exact div_le_div_of_nonneg_right key hm'.le

/-- Paper: §14.2, p. 535. The Weil point-count estimate with genus g gives
an error constant depending only on g in the closed-point count.
Deviation: Uses the numerical Weil hypothesis and the closed-point expression
for the extension-field counts. The displayed constant is an explicit bound. -/
theorem curveZeta_closedPointsOfDegree_bound_of_weil (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (g : ℕ) :
    let q : ℝ := Nat.card k
    let N (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (d : ℝ) * curveZetaClosedPointCount f d
    (∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r)) →
    ∀ m : ℕ, 0 < m → |(curveZetaClosedPointCount f m : ℝ) - q ^ m / m| ≤
      (5 + 6 * (g : ℝ)) * Real.sqrt (q ^ m) / m := by
  intro q N hW m hm
  have hq : (2 : ℝ) ≤ q := by
    have h := Finite.one_lt_card (α := k)
    show (2 : ℝ) ≤ (Nat.card k : ℝ)
    exact_mod_cast h
  exact curveZeta_closedPointsOfDegree_bound_of_weil_aux q g
    (fun d ↦ (curveZetaClosedPointCount f d : ℝ)) hq (Nat.cast_nonneg g) hW m hm

-- TODO(paper-gap): The comparison on p. 535 refers to the missing Theorem
-- 13.3.1.2. Equation (5.3.1.5) supplies a finite-place principal-value
-- operator. The function-field completion, convergence in the topology of
-- uniform convergence on bounded sets, and trace identity are unspecified.

-- TODO(paper-gap): The gonality equality on p. 535 fails for the Hermitian
-- quartic y³ + y = x⁴ over 𝔽₉. Its genus is three and projection to x has
-- degree three. It is maximal and its sole Frobenius eigenvalue has
-- multiplicity six. For g ≥ 2 the general bound gon_k(X) ≤ g + 1 < 2g
-- follows by Riemann–Roch at a rational point. For g = 1 the strict
-- inequality also fails, since gon_k(E) = 2 = 2g. The printed equality
-- and strict inequality need curve-genus and gonality interfaces.

-- TODO(paper-gap): The supersingular example on p. 536 needs a choice of
-- curve with equal Frobenius eigenvalues. Over 𝔽₉, y² = x³ − x has numerator
-- (1 + 3T)². The supersingular curve y² = x³ + (1 + i)x with i² = −1 has
-- numerator 1 + 9T² and gives simple zeros for the quadratic cover's L-function.

-- TODO(paper-gap): §14.3, p. 536 gives n[F : ℚ] as a proposed multiplicity
-- bound for generic zeros. Page 533 identifies these as non-central zeros.
-- A unitary imaginary norm twist translates the zeros in the s-plane.
-- The higher-rank centering convention and argument need to be supplied
-- before stating the bound (ERRATA R24 and M43).

end RiemannMasullo
