module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Binomial acceleration of the alternating series on the Riemann critical line -/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology ComplexConjugate

namespace RiemannMasullo

/-- The exact rational upper-tail mass at `k` of a binomial variable with success
probability two thirds and `M` trials. -/
def binomialZetaWeight (M k : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (M + 1), if k ≤ j then (M.choose j : ℚ) * 2 ^ j else 0) / 3 ^ M

/-- The coefficient is the binomial tail from `k` through `M`, including both ends. -/
theorem binomialZetaWeight_eq_sum_Icc (M k : ℕ) :
    binomialZetaWeight M k =
      (∑ j ∈ Finset.Icc k M, (M.choose j : ℚ) * 2 ^ j) / 3 ^ M := by
  unfold binomialZetaWeight
  rw [← Finset.sum_filter]
  have hs : (Finset.range (M + 1)).filter (k ≤ ·) = Finset.Icc k M := by
    ext j
    simp
    omega
  rw [hs]

private theorem binomialZeta_mgf {R : Type*} [CommSemiring R] (M : ℕ) (x : R) :
    (∑ j ∈ Finset.range (M + 1), (M.choose j : R) * x ^ j) = (1 + x) ^ M := by
  simpa [add_comm, mul_comm] using (add_pow x (1 : R) M).symm

/-- Every rational binomial coefficient weight lies in the closed unit interval. -/
theorem binomialZetaWeight_mem_Icc (M k : ℕ) : binomialZetaWeight M k ∈ Icc (0 : ℚ) 1 := by
  have ha (j : ℕ) : 0 ≤ (M.choose j : ℚ) * 2 ^ j := by positivity
  constructor
  · apply div_nonneg _ (by positivity)
    apply Finset.sum_nonneg
    intro j _
    split <;> simp [ha]
  · unfold binomialZetaWeight
    apply (div_le_iff₀ (by positivity : 0 < (3 : ℚ) ^ M)).mpr
    rw [one_mul, show (3 : ℚ) = 1 + 2 by norm_num, ← binomialZeta_mgf]
    apply Finset.sum_le_sum
    intro j _
    split <;> simp [ha]

private theorem binomialZetaWeight_cast (M k : ℕ) :
    (binomialZetaWeight M k : ℝ) =
    (∑ j ∈ Finset.range (M + 1), if k ≤ j then (M.choose j : ℝ) * 2 ^ j else 0) / 3 ^ M := by
  unfold binomialZetaWeight
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split <;> push_cast <;> rfl

/-- The polynomial whose coefficients form the weighted alternating Dirichlet sum. -/
noncomputable def binomialZetaKernel (M : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range M, (binomialZetaWeight M (k + 1) : ℝ) * (-u) ^ k

/-- Multiplying the averaged finite geometric series by its denominator gives a
single binomial power. This identity holds at every real argument. -/
theorem binomialZetaKernel_mul (M : ℕ) (u : ℝ) :
    binomialZetaKernel M u * (1 + u) = 1 - ((1 - 2 * u) / 3) ^ M := by
  let a (j : ℕ) : ℝ := M.choose j * 2 ^ j
  have hsum : binomialZetaKernel M u =
      (∑ j ∈ Finset.range (M + 1), a j * ∑ k ∈ Finset.range j, (-u) ^ k) / 3 ^ M := by
    calc
      _ = (∑ k ∈ Finset.range M, ∑ j ∈ Finset.range (M + 1),
          if k < j then a j * (-u) ^ k else 0) / 3 ^ M := by
        rw [binomialZetaKernel, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        rw [binomialZetaWeight_cast, div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : k < j <;> simp [a, h]
      _ = _ := by
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hset : (Finset.range M).filter (· < j) = Finset.range j := by
          ext k
          simp
          omega
        rw [← Finset.sum_filter, hset, Finset.mul_sum]
  rw [hsum, div_mul_eq_mul_div, Finset.sum_mul]
  have hgeo (j : ℕ) : (a j * ∑ k ∈ Finset.range j, (-u) ^ k) * (1 + u) =
      a j - (M.choose j : ℝ) * (-(2 * u)) ^ j := by
    have hg := geom_sum_mul_neg (-u) j
    rw [sub_neg_eq_add] at hg
    rw [mul_assoc, hg]
    dsimp [a]
    rw [show -(2 * u) = 2 * (-u) by ring, mul_pow]
    ring
  simp_rw [hgeo]
  rw [Finset.sum_sub_distrib]
  change ((∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * 2 ^ j) - _) / 3 ^ M = _
  rw [binomialZeta_mgf, binomialZeta_mgf, div_pow, ← sub_eq_add_neg]
  norm_num1
  field_simp

/-- The binomial polynomial uniformly approximates the geometric kernel on `[0,1]`. -/
theorem abs_binomialZetaKernel_sub (M : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |binomialZetaKernel M u - (1 + u)⁻¹| ≤ (3 ^ M : ℝ)⁻¹ := by
  have hden : 0 < 1 + u := by linarith [hu.1]
  have hpoly := (eq_div_iff hden.ne').mpr (binomialZetaKernel_mul M u)
  have ha : |1 - 2 * u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [hpoly, ← one_div, ← sub_div, sub_sub_cancel_left, abs_div, abs_neg,
    abs_pow, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_pow, abs_of_pos hden,
    div_div]
  apply (div_le_iff₀ (mul_pos (by positivity) hden)).mpr
  have hb := pow_le_one₀ (n := M) (abs_nonneg _) ha
  calc
    _ ≤ 1 := hb
    _ ≤ _ := by field_simp; linarith [hu.1]

/-- The Fermi kernel in the classical Mellin representation of the alternating
zeta function, written in terms of the decaying exponential. -/
noncomputable def binomialZetaEtaKernel (x : ℝ) : ℂ :=
  ((Real.exp (-x) / (1 + Real.exp (-x)) : ℝ) : ℂ)

private theorem binomialZeta_exp_nat (n : ℕ) (x : ℝ) :
    Real.exp (-((n : ℝ) + 1) * x) = Real.exp (-x) ^ n * Real.exp (-x) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem binomialZeta_eta_geometric {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ n * (Real.exp (-((n : ℝ) + 1) * x) : ℂ))
      (binomialZetaEtaKernel x) := by
  let u : ℂ := Real.exp (-x)
  have hu : ‖-u‖ < 1 := by
    rw [norm_neg, show ‖u‖ = Real.exp (-x) by
      rw [show u = (Real.exp (-x) : ℂ) by rfl, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have h := (hasSum_geometric_of_norm_lt_one hu).mul_right u
  convert h using 1
  · funext n
    rw [binomialZeta_exp_nat]
    rw [neg_eq_neg_one_mul u, mul_pow]
    dsimp [u]
    push_cast
    ring
  · simp [binomialZetaEtaKernel, u, div_eq_inv_mul]

private theorem binomialZeta_eta_dirichlet {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s)
      ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  let f (n : ℕ) : ℂ := 1 / (n + 1 : ℂ) ^ s
  have hf : Summable f := by
    simpa [f] using (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  have hfz : HasSum f (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hf.hasSum
  have ho : HasSum (fun k : ℕ ↦ f (2 * k + 1)) (((2 : ℂ) ^ s)⁻¹ * riemannZeta s) := by
    convert hfz.mul_left (((2 : ℂ) ^ s)⁻¹) using 1
    funext k
    have hm := Complex.mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (by positivity : 0 ≤ (k : ℝ) + 1) s
    dsimp [f]
    push_cast at hm ⊢
    rw [show 2 * (k : ℂ) + 1 + 1 = 2 * (k + 1) by ring, hm]
    field
  have he := (hf.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))).hasSum
  have hsume := (he.even_add_odd ho).unique hfz
  have he' : HasSum (fun k : ℕ ↦ (-1 : ℂ) ^ (2*k) / (↑(2*k) + 1 : ℂ) ^ s)
      (∑' k : ℕ, f (2*k)) := by simpa [Function.comp_def, f, pow_mul] using he
  have ho' : HasSum (fun k : ℕ ↦ (-1 : ℂ) ^ (2*k+1) / (↑(2*k+1) + 1 : ℂ) ^ s)
      (-(((2 : ℂ) ^ s)⁻¹ * riemannZeta s)) := by
    simpa [f, pow_succ, pow_mul, div_eq_mul_inv] using ho.neg
  have h := he'.even_add_odd (f := fun n : ℕ ↦ (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) ho'
  convert h using 1
  rw [Complex.cpow_sub 1 s (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one, div_eq_mul_inv]
  simp only [Function.comp_apply] at hsume
  linear_combination -hsume

private theorem binomialZeta_mellin_eta_right {s : ℂ} (hs : 1 < s.re) :
    mellin binomialZetaEtaKernel s = Gamma s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  have ha := hasSum_mellin (a := fun n : ℕ ↦ (-1 : ℂ) ^ n) (p := fun n ↦ (n : ℝ) + 1)
    (F := binomialZetaEtaKernel) (s := s) (fun _ ↦ Or.inr (by positivity))
    (zero_lt_one.trans hs) (fun _ hx ↦ binomialZeta_eta_geometric hx) (by
      simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs))
  have hb := (binomialZeta_eta_dirichlet hs).mul_left (Gamma s)
  apply ha.unique
  convert hb using 1
  funext n
  push_cast
  ring

private theorem binomialZeta_eta_holomorphic {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin binomialZetaEtaKernel) s := by
  have hc : Continuous binomialZetaEtaKernel := by
    unfold binomialZetaEtaKernel
    exact Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_neg).div
      (continuous_const.add (Real.continuous_exp.comp continuous_neg)) (fun _ ↦ by positivity))
  have hn (x : ℝ) : ‖binomialZetaEtaKernel x‖ = Real.exp (-x) / (1 + Real.exp (-x)) := by
    rw [binomialZetaEtaKernel, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  apply mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := 0) zero_lt_one
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) _ _ hs
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with x
    rw [hn]
    simpa [Real.norm_eq_abs, Real.abs_exp] using
      (div_le_self (Real.exp_pos (-x)).le (by linarith [Real.exp_pos (-x)] :
        1 ≤ 1 + Real.exp (-x)))
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with x
    rw [hn]
    simp only [neg_zero, Real.rpow_zero, norm_one, one_mul]
    apply (div_le_iff₀ (by positivity : 0 < 1 + Real.exp (-x))).mpr
    linarith

/-- Mellin representation of the actual analytically continued Riemann zeta function
in the open critical strip (DLMF 25.5.3), with its eta and Gamma factors. -/
theorem mellin_binomialZetaEtaKernel {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    mellin binomialZetaEtaKernel s = Gamma s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  let S : Set ℂ := {z | 0 < z.re} ∩ {z | z.re < 1}
  let T : Set ℂ := {z | 0 < z.re} ∩ {z | 0 < z.im}
  have hS : Convex ℝ S := (convex_halfSpace_gt Complex.reLm.isLinear 0).inter
    (convex_halfSpace_lt Complex.reLm.isLinear 1)
  have hT : Convex ℝ T := (convex_halfSpace_gt Complex.reLm.isLinear 0).inter
    (convex_halfSpace_gt Complex.imLm.isLinear 0)
  have hconn := hS.isPreconnected.union (x := (⟨1/2, 1⟩ : ℂ))
    (by norm_num [S]) (by norm_num [T]) hT.isPreconnected
  have hopen : IsOpen (S ∪ T) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).union
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hpos {z} (hz : z ∈ S ∪ T) : 0 < z.re := hz.elim And.left And.left
  have hne {z} (hz : z ∈ S ∪ T) : z ≠ 1 := by
    rintro rfl
    simp [S, T] at hz
  have ha : AnalyticOnNhd ℂ (mellin binomialZetaEtaKernel) (S ∪ T) :=
    (show DifferentiableOn ℂ _ (S ∪ T) from fun z hz ↦
      (binomialZeta_eta_holomorphic (hpos hz)).differentiableWithinAt).analyticOnNhd hopen
  have hb : AnalyticOnNhd ℂ (fun z ↦ Gamma z * ((1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z)) (S ∪ T) := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have hg := Complex.differentiableAt_Gamma z (fun n h ↦ by
      have h0 := hpos hz
      rw [h] at h0
      simp at h0
      linarith)
    apply DifferentiableAt.differentiableWithinAt
    have he : DifferentiableAt ℂ (fun v : ℂ ↦ (2 : ℂ) ^ (1 - v)) z :=
      (differentiable_const_cpow_of_neZero (2 : ℂ)).differentiableAt.comp z (by fun_prop)
    exact hg.mul (((differentiableAt_const _).sub he).mul (differentiableAt_riemannZeta (hne hz)))
  let b : ℂ := ⟨2,1⟩
  refine ha.eqOn_of_preconnected_of_eventuallyEq hb hconn (z₀ := b) (Or.inr (by norm_num [T, b])) ?_
    (Or.inl ⟨hs₀,hs₁⟩)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num [b] : (1 : ℝ) < b.re)] with z hz
  exact binomialZeta_mellin_eta_right hz

/-- The cross-multiplied eta--zeta identity holds on the positive real half-plane
away from the pole of Mathlib's zeta function. -/
theorem mellin_binomialZetaEtaKernel_of_re_pos {s : ℂ} (hs : 0 < s.re) (h₁ : s ≠ 1) :
    mellin binomialZetaEtaKernel s = Gamma s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  rcases lt_trichotomy s.re 1 with h | h | h
  · exact mellin_binomialZetaEtaKernel hs h
  · let p (x : ℝ) : ℂ := s + x
    have hp : Tendsto p (𝓝[>] 0) (𝓝 s) := by
      have hp₀ : Tendsto (fun x : ℝ ↦ s + (x : ℂ)) (𝓝 0) (𝓝 (s + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa [p] using hp₀.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hg := Complex.differentiableAt_Gamma s (fun n he ↦ by
      have hn := hs
      rw [he] at hn
      simp at hn
      linarith)
    have he : DifferentiableAt ℂ (fun z : ℂ ↦ (2 : ℂ) ^ (1 - z)) s :=
      (differentiable_const_cpow_of_neZero (2 : ℂ)).differentiableAt.comp s (by fun_prop)
    have hc : ContinuousAt (fun z : ℂ ↦ Gamma z * ((1 - (2 : ℂ) ^ (1-z)) * riemannZeta z)) s :=
      (hg.mul (((differentiableAt_const _).sub he).mul (differentiableAt_riemannZeta h₁))).continuousAt
    apply tendsto_nhds_unique_of_eventuallyEq ((binomialZeta_eta_holomorphic hs).continuousAt.tendsto.comp hp)
      (hc.tendsto.comp hp)
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
    apply binomialZeta_mellin_eta_right
    change 1 < (s + x).re
    simpa [Complex.add_re, h] using hx
  · exact binomialZeta_mellin_eta_right h

/-- A uniform additive error against the exponential envelope gives a Gamma-weighted
error on the Mellin transform in its right half-plane of absolute convergence. -/
theorem norm_mellin_sub_le_gamma_of_exp_bound {f g : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hg : MellinConvergent g s) (hf : Measurable f) (δ : ℝ)
    (hb : ∀ x : ℝ, 0 < x → ‖f x - g x‖ ≤ δ * Real.exp (-x)) :
    ‖mellin f s - mellin g s‖ ≤ δ * Real.Gamma s.re := by
  let F (x : ℝ) := (x : ℂ) ^ (s - 1) • f x
  let G (x : ℝ) := (x : ℂ) ^ (s - 1) • g x
  let B (x : ℝ) := δ * (Real.exp (-x) * x ^ (s.re - 1))
  have hG : IntegrableOn G (Ioi 0) := hg
  have hB : IntegrableOn B (Ioi 0) := (Real.GammaIntegral_convergent hs).const_mul δ
  have hm : Measurable F := by dsimp [F]; fun_prop
  have hdom : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), ‖F x - G x‖ ≤ B x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [F,G,B]
    rw [← mul_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb x hx) (Real.rpow_nonneg hx.le _)
      _ = _ := by ring
  have hdiff : IntegrableOn (fun x ↦ F x - G x) (Ioi 0) :=
    hB.mono' (hm.aestronglyMeasurable.sub hG.1) hdom
  have hF : IntegrableOn F (Ioi 0) := by
    exact (hdiff.add hG).congr (ae_of_all _ fun x ↦ sub_add_cancel (F x) (G x))
  change ‖(∫ x in Ioi 0, F x) - ∫ x in Ioi 0, G x‖ ≤ _
  rw [← integral_sub hF hG]
  calc
    _ ≤ _ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi 0, B x := integral_mono_ae hdiff.norm hB hdom
    _ = _ := by simp only [B, integral_const_mul, ← Real.Gamma_eq_integral hs]

/-- A finite Dirichlet numerator with exactly `M` positive integer bases. -/
noncomputable def binomialZetaNumerator (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * (binomialZetaWeight M (k+1) : ℂ) / (k + 1 : ℂ) ^ s

/-- Finite rationally weighted approximation to Mathlib's Riemann zeta function. -/
noncomputable def binomialZetaApprox (M : ℕ) (s : ℂ) : ℂ :=
  binomialZetaNumerator M s / (1 - (2 : ℂ) ^ (1 - s))

private noncomputable def binomialZetaExpKernel (M : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (-x) * binomialZetaKernel M (Real.exp (-x)) : ℝ) : ℂ)

private theorem binomialZeta_mellin_finite (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (binomialZetaExpKernel M) s = Gamma s * binomialZetaNumerator M s := by
  let a (k : Fin M) : ℂ := (-1 : ℂ) ^ (k : ℕ) * (binomialZetaWeight M ((k : ℕ) + 1) : ℂ)
  let p (k : Fin M) : ℝ := ((k : ℕ) : ℝ) + 1
  have hF (x : ℝ) : (∑ i : Fin M, a i * (Real.exp (-p i * x) : ℂ)) = binomialZetaExpKernel M x := by
    rw [show (∑ i : Fin M, a i * (Real.exp (-p i * x) : ℂ)) =
      ∑ k ∈ Finset.range M, ((-1 : ℂ) ^ k * (binomialZetaWeight M (k+1) : ℂ)) *
        (Real.exp (-((k:ℝ)+1) * x) : ℂ) from Fin.sum_univ_eq_sum_range
          (fun k : ℕ ↦ ((-1 : ℂ) ^ k * (binomialZetaWeight M (k+1) : ℂ)) *
            (Real.exp (-((k:ℝ)+1) * x) : ℂ)) M]
    unfold binomialZetaExpKernel binomialZetaKernel
    rw [Finset.mul_sum]
    simp_rw [binomialZeta_exp_nat]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_eq_neg_one_mul (cexp (-↑x)), mul_pow]
    ring
  have h := hasSum_mellin (a := a) (p := p) (F := binomialZetaExpKernel M) (s := s)
    (fun k ↦ Or.inr (by dsimp [p]; positivity)) hs
    (fun x _ ↦ (hF x) ▸ hasSum_fintype _) (hasSum_fintype _).summable
  rw [← h.tsum_eq, tsum_fintype, binomialZetaNumerator, Finset.mul_sum]
  convert Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Gamma s *
    ((-1 : ℂ) ^ k * (binomialZetaWeight M (k+1) : ℂ) / (k+1 : ℂ) ^ s)) M using 1
  apply Finset.sum_congr rfl
  intro k _
  dsimp [a,p]
  push_cast
  ring

/-- The numerator error in the entire open critical strip, before division by Gamma
and the eta factor. -/
theorem norm_gamma_mul_binomialZetaNumerator_sub (M : ℕ) {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    ‖Gamma s * (binomialZetaNumerator M s - (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)‖ ≤
      (3 ^ M : ℝ)⁻¹ * Real.Gamma s.re := by
  have hη : MellinConvergent binomialZetaEtaKernel s := by
    apply (Real.GammaIntegral_convergent h₀).mono'
    · unfold binomialZetaEtaKernel
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re,
        binomialZetaEtaKernel, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [mul_comm (Real.exp (-x))]
      exact mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le (by linarith [Real.exp_pos (-x)]))
        (Real.rpow_nonneg hx.le _)
  have hm : Measurable (binomialZetaExpKernel M) := by
    unfold binomialZetaExpKernel binomialZetaKernel
    fun_prop
  have h := norm_mellin_sub_le_gamma_of_exp_bound h₀ hη hm (3 ^ M : ℝ)⁻¹ (fun x hx ↦ by
    let u := Real.exp (-x)
    have hu : u ∈ Icc (0 : ℝ) 1 := ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
    change ‖((u * binomialZetaKernel M u : ℝ) : ℂ) - ((u / (1 + u) : ℝ) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, ← mul_sub,
      abs_mul, abs_of_nonneg hu.1, mul_comm (3 ^ M : ℝ)⁻¹]
    exact mul_le_mul_of_nonneg_left (abs_binomialZetaKernel_sub M hu) hu.1)
  rw [binomialZeta_mellin_finite M h₀, mellin_binomialZetaEtaKernel h₀ h₁, ← mul_sub] at h
  exact h

local notation "line(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * Complex.I)

private theorem binomialZeta_line_re (t : ℝ) : (line(t)).re = 1 / 2 := by simp

/-- Euler's reflection formula on the critical line, in squared norm form
(DLMF 5.4.4). -/
theorem norm_gamma_critical_sq (t : ℝ) :
    ‖Gamma (line(t))‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hc : 1 - line(t) = conj line(t) := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
    ring
  have hs : Complex.sin (Real.pi * line(t)) = (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * line(t) = Real.pi / 2 + ((Real.pi * t : ℝ) : ℂ) * I by
      push_cast; ring]
    rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      one_mul, zero_mul, add_zero, Complex.ofReal_cosh]
  have h := congrArg norm (Complex.Gamma_mul_Gamma_one_sub line(t))
  rw [hc, Complex.Gamma_conj, norm_mul, Complex.norm_conj, hs, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos _).le] at h
  simpa [sq] using h

private theorem binomialZeta_denom_lower (t : ℝ) :
    √2 - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - line(t))‖ := by
  have hnorm : ‖(2 : ℂ) ^ (1 - line(t))‖ = √2 := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - line(t))
    rw [Complex.sub_re, Complex.one_re, binomialZeta_line_re,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at h
    simpa only [Complex.ofReal_ofNat] using h
  calc
    _ = ‖(2 : ℂ) ^ (1 - line(t))‖ - ‖(1 : ℂ)‖ := by rw [hnorm, norm_one]
    _ ≤ ‖(2 : ℂ) ^ (1 - line(t)) - 1‖ := norm_sub_norm_le _ _
    _ = _ := norm_sub_rev _ _

/-- Explicit absolute error of the rational binomial acceleration on the whole
critical line, with the exact Gamma factor. -/
theorem norm_binomialZetaApprox_sub_riemannZeta (M : ℕ) (t : ℝ) :
    ‖binomialZetaApprox M line(t) - riemannZeta line(t)‖ ≤
      (√2 + 1) * √(Real.cosh (Real.pi * t)) * (3 ^ M : ℝ)⁻¹ := by
  let c := Real.cosh (Real.pi * t)
  let den := 1 - (2 : ℂ) ^ (1 - line(t))
  have hc : 0 < c := Real.cosh_pos _
  have h₀ : 0 < (line(t)).re := by rw [binomialZeta_line_re]; norm_num
  have h₁ : (line(t)).re < 1 := by rw [binomialZeta_line_re]; norm_num
  have hg : 0 < ‖Gamma line(t)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos h₀)
  have hprod : ‖Gamma line(t)‖ * √c = √Real.pi := by
    have hsq : (‖Gamma line(t)‖ * √c) ^ 2 = (√Real.pi) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt Real.pi_pos.le, norm_gamma_critical_sq]
      exact div_mul_cancel₀ _ hc.ne'
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  have hd₀ : √2 - 1 ≤ ‖den‖ := binomialZeta_denom_lower t
  have hd : 0 < ‖den‖ := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hb : 1 ≤ (√2 + 1) * ‖den‖ := by
    have hs := mul_le_mul_of_nonneg_left hd₀ (show 0 ≤ √2 + 1 by positivity)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have herr := norm_gamma_mul_binomialZetaNumerator_sub M h₀ h₁
  rw [norm_mul, binomialZeta_line_re, Real.Gamma_one_half_eq, ← hprod] at herr
  have hnum : ‖binomialZetaNumerator M line(t) - den * riemannZeta line(t)‖ ≤ (3 ^ M : ℝ)⁻¹ * √c := by
    apply le_of_mul_le_mul_left _ hg
    convert herr using 1
    ring
  have hi : binomialZetaApprox M line(t) - riemannZeta line(t) =
      (binomialZetaNumerator M line(t) - den * riemannZeta line(t)) / den := by
    change _ / den - _ = _
    field_simp [(norm_pos_iff.mp hd)]
  rw [hi, norm_div]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ (3 ^ M : ℝ)⁻¹ * √c := hnum
    _ = ((3 ^ M : ℝ)⁻¹ * √c) * 1 := (mul_one _).symm
    _ ≤ ((3 ^ M : ℝ)⁻¹ * √c) * ((√2 + 1) * ‖den‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by dsimp [c]; ring

/-- Every ordinate in the height window has a dyadic-error approximation based on the
first `3 * (n + 1)` integers, including at `n = 0`. -/
theorem norm_binomialZetaApprox_sub_riemannZeta_lt_dyadic (n : ℕ) {t : ℝ} (ht : |t| ≤ n + 1) :
    ‖binomialZetaApprox (3 * (n + 1)) line(t) - riemannZeta line(t)‖ < (2 ^ n : ℝ)⁻¹ := by
  have hpi : |Real.pi * t| ≤ 4 * (n + 1 : ℝ) := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul Real.pi_lt_four.le ht (abs_nonneg _) (by norm_num)
  have hcosh : Real.cosh (Real.pi * t) ≤ Real.exp (4 * (n + 1 : ℝ)) := by
    rw [Real.cosh_eq]
    have h1 := Real.exp_le_exp.mpr (abs_le.mp hpi).2
    have h2 := Real.exp_le_exp.mpr (neg_le.mp (abs_le.mp hpi).1)
    linarith
  have hsqrt : √(Real.cosh (Real.pi * t)) ≤ Real.exp (2 * (n + 1 : ℝ)) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le, hcosh.trans_eq ?_⟩
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h9 : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    exact (mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three.le).trans_eq (by norm_num)
  have hgt : √(Real.cosh (Real.pi * t)) ≤ (9 : ℝ) ^ (n + 1) := by
    apply hsqrt.trans
    rw [mul_comm, ← Nat.cast_add_one, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h9 _
  have hratio : (9 : ℝ) ^ (n + 1) * (3 ^ (3 * (n + 1)) : ℝ)⁻¹ = (1 / 3 : ℝ) ^ (n + 1) := by
    rw [pow_mul, ← inv_pow, ← mul_pow]
    norm_num
  apply (norm_binomialZetaApprox_sub_riemannZeta (3 * (n + 1)) t).trans_lt
  calc
    _ ≤ (√2 + 1) * 9 ^ (n + 1) * (3 ^ (3 * (n + 1)) : ℝ)⁻¹ := by gcongr
    _ = (√2 + 1) * (1 / 3 : ℝ) ^ (n + 1) := by rw [mul_assoc, hratio]
    _ < 3 * (1 / 3 : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right
      (by linarith [Real.sqrt_two_lt_three_halves]) (by positivity)
    _ = (1 / 3 : ℝ) ^ n := by rw [pow_succ]; ring
    _ ≤ _ := by rw [← inv_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

private theorem binomialZeta_cpow_phase (r a t : ℝ) (hr : 0 < r) :
    (r : ℂ) ^ ((a : ℂ) - (t : ℂ) * I) =
    ((r ^ a : ℝ) : ℂ) * Complex.exp (-((t * Real.log r : ℝ) : ℂ) * I) := by
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hn, ← Complex.ofReal_cpow hr.le,
    Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log hr.le]
  congr 2
  push_cast
  ring

/-- Positive integer powers in the approximation can be evaluated with real square
roots, real logarithms and elementary circular phases. -/
theorem binomialZetaApprox_critical_eq_phases (M : ℕ) (t : ℝ) :
    binomialZetaApprox M line(t) =
      (∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * (binomialZetaWeight M (k + 1) : ℂ) *
        Complex.exp (-((t * Real.log (k + 1 : ℝ) : ℝ) : ℂ) * I) /
          (√(k + 1 : ℝ) : ℂ)) /
      (1 - (√2 : ℂ) * Complex.exp (-((t * Real.log 2 : ℝ) : ℂ) * I)) := by
  have hd : (2 : ℂ) ^ (1 - line(t)) =
      (√2 : ℂ) * Complex.exp (-((t * Real.log 2 : ℝ) : ℂ) * I) := by
    have h := binomialZeta_cpow_phase 2 (1 / 2) t (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    convert h using 2
    push_cast
    ring
  have hi (r : ℝ) (hr : 0 < r) : ((r : ℂ) ^ line(t))⁻¹ =
      ((√r : ℂ)⁻¹) * Complex.exp (-((t * Real.log r : ℝ) : ℂ) * I) := by
    have h := binomialZeta_cpow_phase r (-(1 / 2)) t hr
    rw [Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv] at h
    rw [← Complex.cpow_neg]
    convert h using 2
    push_cast
    ring
  unfold binomialZetaApprox binomialZetaNumerator
  rw [hd]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h := hi (k + 1 : ℝ) (by positivity)
  rw [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] at h
  rw [div_eq_mul_inv, h, div_eq_mul_inv]
  ring

end RiemannMasullo
