module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.Convex
import RiemannMasullo.ForMathlib.Analysis.Complex.BlaschkeFactorization

/-!
# Displacement of zeros of a nonprincipal Dirichlet L-function

For a nonprincipal character modulo `q`, Abel summation bounds `L(s)/s` by
`B / s.re` on the open right half-plane whenever `B` bounds the absolute
values of the partial character sums. Periodicity gives the elementary choice
`B = q/2`. In the half-plane to the right of the critical line, removing any
finite set of zeros gives a product estimate at any nonzero value of the
L-function. Taking logarithms bounds the sum of the displacements of all
such zeros with their analytic multiplicities.
-/

open Set Filter Function MeasureTheory Metric
open scoped Topology BigOperators Asymptotics ComplexConjugate

public noncomputable section
namespace RiemannMasullo

/-- The partial sums of a nonprincipal Dirichlet character have period its level. -/
theorem dirichletCharacter_partial_sum_mod {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)) = ∑ j ∈ Finset.Icc 1 (n%q), χ (j : ZMod q) := by
  let a (j : ℕ) := χ ((j : ZMod q) + 1)
  let S (n : ℕ) := ∑ j ∈ Finset.range n, a j
  have hs (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q) = S n := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [S, a, add_comm]
  have hq : S q = 0 := by
    rw [show S q = ∑ i : Fin q, a i from (Fin.sum_univ_eq_sum_range a q).symm]
    have hh (i : Fin q) : a i = χ (ZMod.finEquiv q i + 1) := by
      have he : ((ZMod.finEquiv q i).val : ℕ) = i.val := by
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q => rfl
      rw [← ZMod.natCast_zmod_val (ZMod.finEquiv q i), he]
    simp only [hh]
    exact ((ZMod.finEquiv q).toEquiv.sum_comp (fun x ↦ χ (x + 1))).trans
      ((Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) (fun z ↦ χ z)).trans (χ.sum_eq_zero_of_ne_one hχ))
  have hper : Periodic S q := by
    intro j
    change (∑ i ∈ Finset.range (j + q), a i) = S j
    rw [add_comm j q, Finset.sum_range_add]
    change S q + _ = _
    simp [hq, S, a]
  let r := n % q
  have hr : r < q := Nat.mod_lt _ (NeZero.pos q)
  have hSr : S n = S r := by
    have h := (hper.nat_mul (n / q)) r
    change S (r + n / q * q) = S r at h
    rwa [show r + n / q * q = n by rw [Nat.mul_comm (n / q) q]; exact Nat.mod_add_div n q] at h
  exact (hs n).trans (hSr.trans (hs r).symm)

private theorem dirichletZero_partial_sum_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ (q : ℝ) / 2 := by
  let a (j : ℕ) := χ ((j : ZMod q) + 1)
  let S (n : ℕ) := ∑ j ∈ Finset.range n, a j
  have hs (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q) = S n := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [S, a, add_comm]
  have hq : S q = 0 := by rw [← hs, dirichletCharacter_partial_sum_mod χ hχ q]; simp
  let r := n % q
  have hr : r < q := Nat.mod_lt _ (NeZero.pos q)
  have hSr : S n = S r := (hs n).symm.trans ((dirichletCharacter_partial_sum_mod χ hχ n).trans (hs r))
  have hbd (t l : ℕ) : ‖∑ j ∈ Finset.range l, a (t + j)‖ ≤ (l : ℝ) := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ ↦ χ.norm_le_one _)).trans_eq (by simp))
  have hleft : ‖S r‖ ≤ (r : ℝ) := by simpa [S] using hbd 0 r
  have hright : ‖S r‖ ≤ ((q - r : ℕ) : ℝ) := by
    have hsum : S r + ∑ j ∈ Finset.range (q - r), a (r + j) = 0 := by
      rw [← hq]
      change _ = ∑ j ∈ Finset.range q, a j
      conv_rhs => rw [← Nat.add_sub_of_le hr.le, Finset.sum_range_add]
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
    exact hbd _ _
  rw [hs n, hSr]
  rw [Nat.cast_sub hr.le] at hright
  linarith

/-- Abel summation gives the integral of the partial character sums throughout
  the open right half-plane for every nonprincipal character. -/
theorem dirichletLFunction_eq_abelIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {B : ℝ}
    (hB : ∀ n : ℕ, ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : χ.LFunction s = s * ∫ x in Ioi (1 : ℝ), (∑ j ∈ Finset.Icc 1 ⌊x⌋₊, χ (j : ZMod q)) * (x : ℂ)^(-(s+1)) := by
  let P (n : ℕ) := ∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)
  let A : ℝ → ℂ := (Ioi 1).indicator (fun x : ℝ ↦ P ⌊x⌋₊)
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hbd (x : ℝ) : ‖A x‖ ≤ B := by
    by_cases h : x ∈ Ioi (1 : ℝ)
    · simpa [A, h, P] using hB ⌊x⌋₊
    · simp [A, h, hB₀]
  have hmeas : Measurable A :=
    ((measurable_of_countable P).comp measurable_id.nat_floor).indicator measurableSet_Ioi
  have hloc : LocallyIntegrableOn A (Ioi 0) :=
    (locallyIntegrableOn_const B).mono hmeas.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (hbd x).trans (Real.le_norm_self _))
  have htop : A =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
    exact Asymptotics.isBigO_iff.mpr ⟨B, Eventually.of_forall fun x ↦ by simpa using hbd x⟩
  have hbot (b : ℝ) : A =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨0, ?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [A, not_lt.mpr (le_of_lt hx)]
  let G (z : ℂ) := z * mellin A (-z)
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGa : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have hM := mellin_differentiableAt_of_isBigO_rpow hloc htop (by simpa using hz : (-z).re < 0)
      (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.fun_mul (hM.comp z differentiableAt_id.neg)).differentiableWithinAt
  have hI (z : ℂ) : mellin A (-z) =
      ∫ x in Ioi (1 : ℝ), P ⌊x⌋₊ * (x : ℂ) ^ (-(z + 1)) := by
    have he (x : ℝ) : (x : ℂ) ^ (-z - 1) • A x =
        (Ioi 1).indicator (fun y : ℝ ↦ P ⌊y⌋₊ * (y : ℂ) ^ (-(z+1))) x := by
      by_cases hx : x ∈ Ioi (1 : ℝ)
      · simp only [A, indicator_of_mem hx, smul_eq_mul]
        rw [show -z - 1 = -(z+1) by ring, mul_comm]
      · simp [A, hx]
    simp only [mellin, he, integral_indicator measurableSet_Ioi]
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  have hO : (fun n : ℕ ↦ P n) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    exact Asymptotics.isBigO_iff.mpr ⟨B, Eventually.of_forall fun n ↦ by simpa using hB n⟩
  have hEq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    change 1 < z.re at hz
    rw [χ.LFunction_eq_LSeries hz, LSeries_eq_mul_integral _ le_rfl (by linarith : 0 < z.re)
      (ZMod.LSeriesSummable_of_one_lt_re χ hz) hO]
    exact congrArg (z * ·) (hI z).symm
  have hLa : AnalyticOnNhd ℂ χ.LFunction {z : ℂ | 0 < z.re} :=
    fun z _ ↦ (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hall := hLa.eqOn_of_preconnected_of_eventuallyEq
    hGa (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) hEq
  exact (hall hs).trans (congrArg (s * ·) (hI s))

private theorem dirichletZero_abel_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {B : ℝ}
    (hB : ∀ n : ℕ, ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : ‖χ.LFunction s / s‖ ≤ B / s.re := by
  let P (n : ℕ) := ∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)
  have hz : s ≠ 0 := fun e ↦ by simp [e] at hs
  rw [dirichletLFunction_eq_abelIntegral χ hχ hB hs, mul_div_cancel_left₀ _ hz]
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ), ‖P ⌊x⌋₊ * (x : ℂ) ^ (-(s + 1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (1 : ℝ), B * x ^ (-(s.re + 1)) := by
      have h (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
          ‖P ⌊x⌋₊ * (x : ℂ) ^ (-(s + 1))‖ ≤ B * x ^ (-(s.re + 1)) := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx)]
        simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
        exact mul_le_mul_of_nonneg_right (hB _) (Real.rpow_nonneg (by linarith [show 1 < x from hx]) _)
      apply setIntegral_mono_on _ (hi.const_mul B) measurableSet_Ioi h
      have hmP : Measurable (fun x : ℝ ↦ P ⌊x⌋₊) := (measurable_of_countable P).comp measurable_id.nat_floor
      have hmK : Measurable (fun x : ℝ ↦ (x : ℂ) ^ (-(s+1))) := by fun_prop
      apply (hi.const_mul B).mono' (hmP.mul hmK).norm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [Pi.mul_apply, Real.norm_of_nonneg (norm_nonneg _)] using h x hx
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one]
      simp
      ring

private theorem dirichletZero_norm_sq_sub (u : ℝ) (c s : ℂ) :
    ‖s + conj c - u‖ ^ 2 - ‖s - c‖ ^ 2 = (2 * s.re - u) * (2 * c.re - u) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.conj_re,
    Complex.ofReal_re, Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.ofReal_im]
  ring

private theorem dirichletZero_disk_chart (u : ℝ) (c : ℂ) (hc : u / 2 < c.re) :
    let a (s : ℂ) := (s - c) / (s + conj c - u)
    let D (z : ℂ) := (c + conj c - u) / (1 - z) - (conj c - u)
    D 0 = c ∧ (∀ z ∈ ball (0 : ℂ) 1, u/2 < (D z).re ∧ AnalyticAt ℂ D z ∧ deriv D z ≠ 0) ∧
      ∀ s : ℂ, u/2 < s.re → ‖a s‖ < 1 ∧ D (a s) = s := by
  intro a D
  have hn : c + conj c - u ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.ofReal_re, Complex.zero_re] at hh
    linarith
  refine ⟨by dsimp [D]; ring, ?_, ?_⟩
  · intro z hzb
    have hz := mem_ball_zero_iff.mp hzb
    have hnz : 1 - z ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hz
    have hden : D z + conj c - u = (c + conj c - u) / (1 - z) := by dsimp [D]; ring
    have hnum : D z - c = z * (D z + conj c - u) := by
      rw [hden]; dsimp only [D]; field_simp; ring
    have hnd : 0 < ‖D z + conj c - u‖ := norm_pos_iff.mpr (hden ▸ div_ne_zero hn hnz)
    have hlt : ‖D z - c‖ < ‖D z + conj c - u‖ := by
      rw [hnum, norm_mul]; exact mul_lt_of_lt_one_left hnd hz
    have hpos : 0 < (2 * (D z).re - u) * (2 * c.re - u) := by
      rw [← dirichletZero_norm_sq_sub]
      exact sub_pos.mpr (pow_lt_pow_left₀ hlt (norm_nonneg _) (by decide))
    have hder := ((hasDerivAt_const z (c + conj c - u)).div
      ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) hnz).sub_const (conj c - u)
    refine ⟨by nlinarith [pos_of_mul_pos_left hpos (by linarith : 0 ≤ 2 * c.re - u)], ?_, ?_⟩
    · dsimp only [D]; fun_prop (disch := assumption)
    · have hd : deriv D z = (c + conj c - u) / (1 - z) ^ 2 := by
        simpa only [D, Pi.div_apply, Pi.sub_apply, id_eq, zero_mul, zero_sub, mul_neg, mul_one, neg_neg] using hder.deriv
      rw [hd]
      exact div_ne_zero hn (pow_ne_zero _ hnz)
  · intro s hs
    have hden : s + conj c - u ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.ofReal_re, Complex.zero_re] at hh
      linarith
    have ha : ‖a s‖ < 1 := by
      rw [show ‖a s‖ = ‖s - c‖ / ‖s + conj c - u‖ from norm_div .., div_lt_one (norm_pos_iff.mpr hden)]
      nlinarith [dirichletZero_norm_sq_sub u c s, mul_pos (by linarith : 0 < 2 * s.re - u) (by linarith : 0 < 2 * c.re - u),
        norm_nonneg (s + conj c - u), norm_nonneg (s - c)]
    have he : 1 - a s = (c + conj c - u) / (s + conj c - u) := by dsimp [a]; field_simp; ring
    refine ⟨ha, ?_⟩
    dsimp only [D]
    rw [he]
    field_simp
    ring

/-- The finite Blaschke product on the half-plane of real part greater than
`u/2` bounds the normalized L-value at an interior anchor. Every zero
contributes its full analytic multiplicity. -/
theorem dirichletLFunction_finite_zero_product_of_boundary {u : ℝ} (hu : 0 < u) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {B : ℝ} (hB : ∀ n : ℕ, ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ B)
    (c : ℂ) (hc : u / 2 < c.re) (hv : χ.LFunction c ≠ 0)
    (S : Finset {ρ : ℂ // u / 2 < ρ.re ∧ χ.LFunction ρ = 0}) :
    ‖χ.LFunction c / c‖ ≤ (2 * B / u) * ∏ ρ ∈ S,
      (‖ρ.val - c‖ / ‖ρ.val + conj c - u‖) ^ analyticOrderNatAt χ.LFunction ρ.val := by
  let Z := {ρ : ℂ // u / 2 < ρ.re ∧ χ.LFunction ρ = 0}
  let a (s : ℂ) := (s - c) / (s + conj c - u)
  let D (z : ℂ) := (c + conj c - u) / (1 - z) - (conj c - u)
  have ⟨h0, hD, ha⟩ := dirichletZero_disk_chart u c hc
  change D 0 = c at h0
  change ∀ z ∈ ball (0 : ℂ) 1, u/2 < (D z).re ∧ AnalyticAt ℂ D z ∧ deriv D z ≠ 0 at hD
  change ∀ s : ℂ, u/2 < s.re → ‖a s‖ < 1 ∧ D (a s) = s at ha
  let α (ρ : Z) := a ρ.val
  let m (ρ : Z) := analyticOrderNatAt χ.LFunction ρ.val
  have he (ρ : Z) : D (α ρ) = ρ.val := (ha _ ρ.property.1).2
  have hz (ρ : Z) : α ρ ≠ 0 := by
    intro h
    have heq : ρ.val = c := (he ρ).symm.trans ((congrArg D h).trans h0)
    exact hv (heq ▸ ρ.property.2)
  have hmem (ρ : Z) : ‖α ρ‖ < 1 := (ha _ ρ.property.1).1
  let G (z : ℂ) := χ.LFunction (D z) / D z
  have hn (z : ℂ) (h : z ∈ ball 0 1) : D z ≠ 0 := by
    intro h0
    have hu := (hD z h).1
    simp [h0] at hu
    linarith
  have hLa (s : ℂ) : AnalyticAt ℂ χ.LFunction s := (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hG : AnalyticOnNhd ℂ G (ball 0 1) := fun z h ↦
    ((hLa _).comp (hD z h).2.1).div (hD z h).2.1 (hn z h)
  have horder (ρ : Z) : (m ρ : ℕ∞) ≤ analyticOrderAt G (α ρ) := by
    let z := α ρ
    have hzb := mem_ball_zero_iff.mpr (hmem ρ)
    have hs := (hD _ hzb).2.1
    have hc' := analyticOrderAt_comp_of_deriv_ne_zero (f := χ.LFunction) hs (hD _ hzb).2.2
    have hunit := (hs.inv (hn _ hzb)).analyticOrderAt_eq_zero.mpr (inv_ne_zero (hn _ hzb))
    have hmul := analyticOrderAt_fun_mul ((hLa _).comp hs) (hs.inv (hn _ hzb))
    change (m ρ : ℕ∞) ≤ analyticOrderAt (fun t ↦ χ.LFunction (D t) / D t) z
    simp only [div_eq_mul_inv]
    change (m ρ : ℕ∞) ≤ analyticOrderAt (fun i ↦ (χ.LFunction ∘ D) i * D⁻¹ i) (α ρ)
    rw [hmul, hunit, add_zero, hc', he]
    exact ENat.natCast_toNat_le_self _
  have hgb (z : ℂ) (h : z ∈ ball (0 : ℂ) 1) : ‖G z‖ ≤ 2 * B / u := by
    have hr := (hD _ h).1
    have hB₀ := (norm_nonneg _).trans (hB 0)
    apply (dirichletZero_abel_bound χ hχ hB (by linarith : 0 < (D z).re)).trans
    rw [div_le_div_iff₀ (by linarith) hu]
    nlinarith [mul_nonneg hB₀ (by linarith : 0 ≤ 2 * (D z).re - u)]
  obtain ⟨N, -, hbN, hfac⟩ := Blaschke.exists_bounded_finite_blaschke_quotient α m S
    (fun i j hij ↦ Subtype.ext ((he i).symm.trans ((congrArg D hij).trans (he j)))) hz hmem
    G hG (fun ρ _ ↦ horder ρ) _ hgb
  have hbase := congrArg norm (hfac 0 (by simp))
  simp only [Blaschke.finiteProduct, norm_mul, norm_prod, norm_pow, Blaschke.normalizedFactor_apply,
    mul_zero, sub_zero, div_one, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hbase
  calc
    ‖χ.LFunction c / c‖ = ‖G 0‖ := by simp only [G, h0]
    _ = (∏ i ∈ S, ‖α i‖ ^ m i) * ‖N 0‖ := hbase.symm
    _ ≤ (∏ i ∈ S, ‖α i‖ ^ m i) * (2 * B / u) := mul_le_mul_of_nonneg_left (hbN _ (by simp)) (by positivity)
    _ = _ := by simp only [α, a, m, norm_div]; ring

/-- The half-plane displacement estimate with any positive boundary
`u/2`, weighted by the kernel based at an interior nonzero L-value. -/
theorem dirichletLFunction_zero_displacement_of_boundary {u : ℝ} (hu : 0 < u) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℂ) (hc : u / 2 < c.re) (hv : χ.LFunction c ≠ 0) :
    let Z := {ρ : ℂ // u / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - u) * (2 * c.re - u) / ‖ρ.val + conj c - u‖ ^ 2)
    Summable w ∧ ∑' ρ, w ρ ≤ 2 * Real.log ((q : ℝ) / u / ‖χ.LFunction c / c‖) := by
  intro Z w
  let b (ρ : Z) := ‖ρ.val - c‖ / ‖ρ.val + conj c - u‖
  let m (ρ : Z) := analyticOrderNatAt χ.LFunction ρ.val
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hc₀ : c ≠ 0 := fun e ↦ by norm_num [e] at hc; linarith
  have hv₀ : 0 < ‖χ.LFunction c / c‖ := norm_pos_iff.mpr (div_ne_zero hv hc₀)
  have hd (ρ : Z) : 0 < ‖ρ.val + conj c - u‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.ofReal_re, Complex.zero_re] at he
    linarith [ρ.property.1]
  have hb (ρ : Z) : 0 < b ρ := by
    refine div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) (hd ρ)
    intro e
    exact hv (e ▸ ρ.property.2)
  have hn (ρ : Z) : 0 ≤ w ρ := by
    dsimp only [w]
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (by linarith [ρ.property.1]) (by linarith)) (sq_nonneg _))
  have hweight (ρ : Z) : w ρ = (m ρ : ℝ) * (1 - b ρ ^ 2) := by
    dsimp only [w, m, b]
    rw [← dirichletZero_norm_sq_sub, div_pow, sub_div, div_self (pow_ne_zero _ (hd ρ).ne')]
  have hf (S : Finset Z) : ∑ ρ ∈ S, w ρ ≤ 2 * Real.log ((q : ℝ) / u / ‖χ.LFunction c / c‖) := by
    have hp := dirichletLFunction_finite_zero_product_of_boundary hu χ hχ (dirichletZero_partial_sum_bound χ hχ) c hc hv S
    change ‖χ.LFunction c / c‖ ≤ (2 * ((q : ℝ) / 2) / u) * ∏ ρ ∈ S, b ρ ^ m ρ at hp
    rw [show 2 * ((q : ℝ) / 2) = (q : ℝ) by ring] at hp
    have hpn (ρ : Z) (_ : ρ ∈ S) := pow_ne_zero (m ρ) (hb ρ).ne'
    have hlog := Real.log_le_log hv₀ hp
    rw [Real.log_mul (div_pos hq hu).ne' (Finset.prod_ne_zero_iff.mpr hpn), Real.log_prod hpn] at hlog
    simp only [Real.log_pow] at hlog
    have hcomp : ∑ ρ ∈ S, w ρ ≤ ∑ ρ ∈ S, (-2) * ((m ρ : ℝ) * Real.log (b ρ)) := by
      apply Finset.sum_le_sum
      intro ρ _
      have h := Real.log_le_sub_one_of_pos (sq_pos_of_pos (hb ρ))
      rw [Real.log_pow, Nat.cast_ofNat] at h
      rw [hweight]
      calc
        _ ≤ (m ρ : ℝ) * (-(2 * Real.log (b ρ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = _ := by ring
    rw [← Finset.mul_sum] at hcomp
    rw [Real.log_div (div_pos hq hu).ne' hv₀.ne']
    linarith
  exact ⟨summable_of_sum_le hn hf, Real.tsum_le_of_sum_le hn hf⟩

/-- Every finite set of zeros to the right of the critical line bounds the normalized
L-value at an interior anchor. Each zero contributes its full analytic multiplicity. -/
theorem dirichletLFunction_finite_zero_product {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {B : ℝ} (hB : ∀ n : ℕ, ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ B)
    (c : ℂ) (hc : 1 / 2 < c.re) (hv : χ.LFunction c ≠ 0)
    (S : Finset {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}) :
    ‖χ.LFunction c / c‖ ≤ (2 * B) * ∏ ρ ∈ S,
      (‖ρ.val - c‖ / ‖ρ.val + conj c - 1‖) ^ analyticOrderNatAt χ.LFunction ρ.val := by
  simpa using dirichletLFunction_finite_zero_product_of_boundary (u := 1) (by norm_num) χ hχ hB c hc hv S

/-- For a nonprincipal character, the displacements of the zeros to the right of the critical
line, weighted by the half-plane kernel at any interior nonzero L-value, have bounded sum. -/
theorem dirichletLFunction_right_zero_displacement {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℂ) (hc : 1 / 2 < c.re) (hv : χ.LFunction c ≠ 0) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - 1) * (2 * c.re - 1) / ‖ρ.val + conj c - 1‖ ^ 2)
    Summable w ∧ ∑' ρ, w ρ ≤ 2 * Real.log ((q : ℝ) / ‖χ.LFunction c / c‖) := by
  simpa using dirichletLFunction_zero_displacement_of_boundary (u := 1) (by norm_num) χ hχ c hc hv

/-- At the anchor `1`, Dirichlet nonvanishing gives the displacement bound unconditionally
for every nonprincipal character, including imprimitive characters. -/
theorem dirichletLFunction_right_zero_displacement_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) * ((2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2)
    Summable w ∧ ∑' ρ, w ρ ≤ 2 * Real.log ((q : ℝ) / ‖χ.LFunction 1‖) := by
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using dirichletLFunction_right_zero_displacement χ hχ 1 (by norm_num) (DirichletCharacter.LFunction_apply_one_ne_zero hχ)

private theorem dirichletZero_norm_lower_bound_at_two {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c : ℂ} (hc : c.re = 2) :
    1 / 4 ≤ ‖χ.LFunction c‖ := by
  let f := LSeries.term (fun n : ℕ ↦ χ (n : ZMod q)) c
  have hs : 1 < c.re := by linarith
  have hsum : HasSum f (χ.LFunction c) := by
    rw [χ.LFunction_eq_LSeries hs]
    exact (ZMod.LSeriesSummable_of_one_lt_re χ hs).hasSum
  have hterm (n : ℕ) (hn : 0 < n) : ‖f n‖ ≤ 1 / (n : ℝ)^2 := by
    rw [show ‖f n‖ = _ from LSeries.norm_term_eq _ _ _, ite_eq_right hn.ne', hc, Real.rpow_two]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (sq_nonneg _)
  have htail (N : ℕ) :
      ‖∑ k ∈ Finset.range N, f (k+3)‖ ≤ 1/2 - 1/((N:ℝ)+2) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ]
      have hk := hterm (N+3) (by omega)
      push_cast at hk
      have ht : 1 / ((N:ℝ)+3)^2 ≤ 1/((N:ℝ)+2) - 1/((N:ℝ)+3) := by
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      calc
        _ ≤ _ := norm_add_le _ _
        _ ≤ (1/2 - 1/((N:ℝ)+2)) + (1/((N:ℝ)+2) - 1/((N:ℝ)+3)) := add_le_add ih (hk.trans ht)
        _ = _ := by ring
  have hlim := (hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 3))
  have hall (N : ℕ) : 1/4 ≤ ‖∑ k ∈ Finset.range (N+3), f k‖ := by
    rw [Nat.add_comm, Finset.sum_range_add]
    have hfirst : ∑ k ∈ Finset.range 3, f k = 1 + f 2 := by
      simp [Finset.sum_range_succ, f, LSeries.term]
    rw [hfirst]
    have hh := norm_sub_norm_le (1 : ℂ) (1 + f 2 + ∑ k ∈ Finset.range N, f (3+k))
    rw [show (1 : ℂ) - (1 + f 2 + ∑ k ∈ Finset.range N, f (3+k)) =
      -(f 2 + ∑ k ∈ Finset.range N, f (3+k)) by ring, norm_neg] at hh
    have ht := htail N
    simp only [Nat.add_comm 3] at *
    have h₂ := hterm 2 (by decide)
    norm_num at h₂
    simp only [norm_one] at hh
    linarith [norm_add_le (f 2) (∑ k ∈ Finset.range N, f (k+3)), one_div_nonneg.mpr
      (by positivity : 0 ≤ (N : ℝ) + 2)]
  exact ge_of_tendsto hlim.norm (Eventually.of_forall hall)

/-- Anchoring on the vertical line of real part two gives a displacement bound in terms of
the modulus and height alone, uniformly for all nonprincipal characters. -/
theorem dirichletLFunction_right_zero_displacement_at_height {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℂ) (hc : c.re = 2) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - 1) * 3 / ‖ρ.val + conj c - 1‖ ^ 2)
    Summable w ∧ ∑' ρ, w ρ ≤ 2 * Real.log (4 * (q : ℝ) * ‖c‖) := by
  intro Z w
  have hl := dirichletZero_norm_lower_bound_at_two χ hc
  have hv : χ.LFunction c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hc₀ : c ≠ 0 := fun e ↦ by simp [e] at hc
  obtain ⟨hs, hb⟩ := dirichletLFunction_right_zero_displacement χ hχ c (by linarith) hv
  have he : 2*c.re - 1 = 3 := by rw [hc]; norm_num
  rw [he] at hs hb
  refine ⟨hs, hb.trans (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) (by norm_num))⟩
  · exact div_pos (Nat.cast_pos.mpr (NeZero.pos q)) (norm_pos_iff.mpr (div_ne_zero hv hc₀))
  · rw [norm_div, div_div_eq_mul_div, div_le_iff₀ (norm_pos_iff.mpr hv)]
    nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4 * (q:ℝ) * ‖c‖)]

/-- The half-plane with boundary at real part 1/4 includes the critical line
in its interior. At the anchor 2 this gives a logarithmic bound, uniform in the
character, for the inverse-square height mass on the closed right half-strip. -/
theorem dirichletLFunction_right_halfStrip_height_mass {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    let Z := {ρ : ℂ // 1/2 ≤ ρ.re ∧ ρ.re < 1 ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) / (1+|ρ.val.im|)^2
    Summable w ∧ ∑' ρ, w ρ ≤ 16 * Real.log (16 * (q:ℝ)) := by
  intro Z w
  have hL := dirichletZero_norm_lower_bound_at_two χ (c := 2) (by norm_num)
  have hv : χ.LFunction 2 ≠ 0 := norm_pos_iff.mp (by linarith)
  let Y := {ρ : ℂ // (1/2:ℝ)/2 < ρ.re ∧ χ.LFunction ρ = 0}
  let W (ρ : Y) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
    ((2*ρ.val.re-1/2)*(2*(2:ℂ).re-1/2) / ‖ρ.val + conj 2 - ((1/2:ℝ):ℂ)‖^2)
  obtain ⟨hs,hb⟩ := dirichletLFunction_zero_displacement_of_boundary (u := 1/2)
    (by norm_num) χ hχ 2 (by norm_num) hv
  change Summable W at hs
  change ∑' z, W z ≤ _ at hb
  let e (ρ : Z) : Y := ⟨ρ.val, by linarith [ρ.property.1], ρ.property.2.2⟩
  have hi : Injective e := fun x y he ↦ Subtype.ext (congrArg (fun y : Y ↦ y.val) he)
  have hn (ρ : Y) : 0 ≤ W ρ := by
    have hx := ρ.property.1
    dsimp only [W]
    apply mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (by linarith) (by norm_num)) (sq_nonneg _))
  have hcomp (ρ : Z) : w ρ ≤ 8 * W (e ρ) := by
    let D := ‖ρ.val + conj 2 - ((1/2:ℝ):ℂ)‖ ^ 2
    have hx := ρ.property.1
    have hX := ρ.property.2.1
    have hd : D = (ρ.val.re+3/2)^2+ρ.val.im^2 := by
      simp [D, Complex.sq_norm, Complex.normSq_apply]; ring
    have ht := abs_nonneg ρ.val.im
    have ht2 : |ρ.val.im|^2 = ρ.val.im^2 := sq_abs _
    have hD : 0 < D := by rw [hd]; nlinarith [sq_nonneg ρ.val.im]
    have hd' : D ≤ 7*(1+|ρ.val.im|)^2 := by
      rw [hd]; nlinarith [sq_nonneg ρ.val.im, mul_nonneg (by linarith : 0 ≤ 1-ρ.val.re)
        (by linarith : 0 ≤ 4+ρ.val.re)]
    have h1 : 1 / (1+|ρ.val.im|)^2 ≤ 8 * ((2*ρ.val.re-1/2)*(2*(2:ℂ).re-1/2)/D) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hD]
      norm_num
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2*ρ.val.re-1) (sq_nonneg (1+|ρ.val.im|))]
    dsimp only [w,W,e]
    calc _ = (analyticOrderNatAt χ.LFunction ρ.val : ℝ) * (1/(1+|ρ.val.im|)^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
         _ = _ := by dsimp only [D]; ring
  have hmajor := (hs.comp_injective hi).mul_left 8
  have hw : Summable w := hmajor.of_nonneg_of_le (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hcomp
  refine ⟨hw,?_⟩
  have hre : (q:ℝ)/(1/2)/‖χ.LFunction 2 / 2‖ ≤ 16*(q:ℝ) := by
    rw [norm_div, show ‖(2:ℂ)‖ = 2 by norm_num, div_div_eq_mul_div, div_le_iff₀ (norm_pos_iff.mpr hv)]
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 16*(q:ℝ))]
  calc ∑' z, w z ≤ ∑' z, 8*W (e z) := hw.tsum_le_tsum hcomp hmajor
       _ = 8 * ∑' z, W (e z) := tsum_mul_left
       _ ≤ 8 * ∑' z, W z := mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hs hn hi) (by norm_num)
       _ ≤ _ := by
         have hh := Real.log_le_log (show 0 < (q:ℝ)/(1/2)/‖χ.LFunction 2/2‖ from
           div_pos (div_pos (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num))
             (norm_pos_iff.mpr (div_ne_zero hv (by norm_num)))) hre
         linarith

end RiemannMasullo
