module

public import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Probability.Distributions.Cauchy
import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace

/-! # Finite Blaschke products and boundary Poisson estimates for a vertical strip

The logarithmic derivative on the circle is the sum of the Poisson kernels of the zeros.
Pulling this identity back to the strip gives the positive boundary integrand in the
order-one Dirichlet formula. For the order-zero Hardy estimate, the strip Poisson kernel has
uniformly bounded polynomial moments about the pole's height, even as it approaches the boundary.
-/

@[expose] public noncomputable section

open Complex Metric MeasureTheory Filter Set
open scoped Topology NNReal
open scoped ComplexConjugate

namespace RiemannMasullo.Blaschke

private theorem normalizedFactor_eq_const_mul {a : ℂ} (ha : a ≠ 0) :
    normalizedFactor a = fun z ↦ -(conj a / (‖a‖ : ℂ)) * ((z - a) / (1 - conj a * z)) := by
  have hr : (‖a‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hrot : (conj a / (‖a‖ : ℂ)) * a = (‖a‖ : ℂ) := by
    rw [div_mul_eq_mul_div, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, ofReal_pow]
    field_simp
  funext z
  rw [normalizedFactor_apply]
  dsimp only
  rw [← mul_assoc, show (‖a‖ : ℂ) * (conj a / (‖a‖ : ℂ)) = conj a by field_simp, ← mul_div_assoc]
  congr 1
  linear_combination -hrot

private theorem normalizedFactor_boundary {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1)
    (hz : ‖z‖ = 1) :
    DifferentiableAt ℂ (normalizedFactor a) z ∧ normalizedFactor a z ≠ 0 ∧
      z * logDeriv (normalizedFactor a) z = (poissonKernel 0 a z : ℂ) := by
  have hn : z - a ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [← h, hz] at ha')
  have hd : 1 - conj a * z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh := congrArg norm h
    simp [hz] at hh
    linarith
  have hc : -(conj a / (‖a‖ : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by simpa using ha) (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)))
  have hz' : z * conj z = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hz]
    norm_num
  have he : z * (conj z - conj a) = 1 - conj a * z := by rw [mul_sub, hz', mul_comm z]
  have hnum : (1 - conj a * z) + conj a * (z - a) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [ofReal_sub, ofReal_one, ← normSq_eq_norm_sq, normSq_eq_conj_mul_self]
    ring
  have hden : (z-a) * (1 - conj a * z) = z * ((‖z-a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← normSq_eq_norm_sq, normSq_eq_conj_mul_self, map_sub, ← he]
    ring
  rw [normalizedFactor_eq_const_mul ha]
  refine ⟨by fun_prop (disch := assumption), mul_ne_zero hc (div_ne_zero hn hd), ?_⟩
  rw [logDeriv_const_mul _ _ hc, logDeriv_fun_div (f := fun w ↦ w - a) (g := fun w ↦ 1 - conj a * w) z hn hd (by fun_prop) (by fun_prop)]
  have hDn : HasDerivAt (fun w : ℂ ↦ w - a) 1 z := (hasDerivAt_id z).sub_const a
  have hDd : HasDerivAt (fun w : ℂ ↦ 1 - conj a * w) (-conj a) z := by
    simpa only [mul_one] using ((hasDerivAt_id' z).const_mul (conj a)).const_sub (1 : ℂ)
  rw [logDeriv_apply, logDeriv_apply, hDn.deriv, hDd.deriv, neg_div, sub_neg_eq_add,
    div_add_div _ _ hn hd, one_mul, mul_comm (z - a) (conj a), hnum, hden, poissonKernel_def, sub_zero, sub_zero, hz,
    one_pow, ofReal_div, ← mul_div_assoc]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mp (by simpa only [hz] using one_ne_zero : ‖z‖ ≠ 0))

/-- On the unit circle the logarithmic derivative in the outward radial direction is the
sum of the disk Poisson kernels of all the zeros, counted with multiplicity. -/
theorem finiteProduct_logDeriv_sphere {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι)
    (ha : ∀ i ∈ S, a i ≠ 0) (ha' : ∀ i ∈ S, ‖a i‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    z * logDeriv (finiteProduct a m S) z =
      ((∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) z : ℝ) : ℂ) := by
  have h i (hi : i ∈ S) := normalizedFactor_boundary (ha i hi) (ha' i hi) hz
  unfold finiteProduct
  rw [logDeriv_fun_prod (f := fun i w ↦ normalizedFactor (a i) w ^ m i)
    (fun i hi ↦ pow_ne_zero _ (h i hi).2.1) (fun i hi ↦ (h i hi).1.pow _), Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [logDeriv_fun_pow (h i hi).1, mul_left_comm, (h i hi).2.2]

private def stripExp (w₀ : ℂ) (k : ℝ) (z : ℂ) :=
  exp ((k : ℂ) * (I * (z - w₀)))

private theorem stripExp_norm (w₀ : ℂ) (k : ℝ) (z : ℂ) :
    ‖stripExp w₀ k z‖ = Real.exp (-(k * (z.im - w₀.im))) := by
  simp [stripExp, norm_exp]
  ring

private theorem stripExp_boundary {w₀ w : ℂ} {k n : ℝ} (hn : n = 1 ∨ n = -1)
    (hw : k * (w.re - w₀.re) = n * (Real.pi / 2)) :
    stripExp w₀ k w = ((n * Real.exp (-(k * (w.im - w₀.im))) : ℝ) : ℂ) * I := by
  rcases hn with rfl | rfl <;> apply Complex.ext <;>
    simp [stripExp, exp_re, exp_im, hw] <;> ring

private theorem stripExp_re_pos {w₀ ρ : ℂ} {k : ℝ} (hk : 0 < k)
    (hρ : |ρ.re - w₀.re| < (Real.pi / 2) / k) : 0 < (stripExp w₀ k ρ).re := by
  have hphase : |k * (ρ.re - w₀.re)| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hk, mul_comm]
    exact (lt_div_iff₀ hk).mp hρ
  rw [stripExp, exp_re, im_ofReal_mul, I_mul_im, sub_re]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hphase))

private theorem stripChart_boundary {w₀ w : ℂ} {k n : ℝ} (hk : 0 < k)
    (hn : n = 1 ∨ n = -1) (hw : k * (w.re - w₀.re) = n * (Real.pi / 2)) :
    let Z := stripBlaschkeToDisk w₀ k
    let t := Real.exp (-(k * (w.im - w₀.im)))
    let q := 2 * k * t / (1 + t ^ 2)
    ‖Z w‖ = 1 ∧ 0 < q ∧ HasDerivAt Z (((n * q : ℝ) : ℂ) * Z w) w := by
  let u := stripExp w₀ k
  let t := Real.exp (-(k * (w.im - w₀.im)))
  have hu : u w = ((n * t : ℝ) : ℂ) * I := stripExp_boundary hn hw
  have hre : (u w).re = 0 := by rw [hu]; simp
  have hd : u w + 1 ≠ 0 := fun h ↦ by simpa [hre] using congrArg re h
  have hnorm : ‖u w - 1‖ = ‖u w + 1‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [← normSq_eq_norm_sq, normSq_apply, hre]
  have hu' : HasDerivAt u (u w * ((k : ℂ) * I)) w := by
    change HasDerivAt (fun x : ℂ ↦ exp ((k : ℂ) * (I * (x - w₀)))) _ w
    simpa only [u, stripExp, mul_one] using
      ((((hasDerivAt_id' w).sub_const w₀).const_mul I).const_mul (k : ℂ)).cexp
  change ‖(u w - 1) / (u w + 1)‖ = 1 ∧
    0 < 2 * k * t / (1 + t ^ 2) ∧
    HasDerivAt (fun x ↦ (u x - 1) / (u x + 1))
      (((n * (2 * k * t / (1 + t ^ 2)) : ℝ) : ℂ) * ((u w - 1) / (u w + 1))) w
  refine ⟨by rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hd)], by dsimp [t]; positivity,
    ((hu'.sub_const 1).div (hu'.add_const 1) hd).congr_deriv ?_⟩
  have hp : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + t ^ 2 ≠ 0 by positivity)
  push_cast
  field_simp [hd, hp]
  rw [hu]
  rcases hn with rfl | rfl <;> push_cast <;> ring_nf <;> simp [I_sq]

private theorem norm_deriv_stripChart_boundary {w₀ w : ℂ} {k n : ℝ} (hk : 0 < k)
    (hn : n = 1 ∨ n = -1) (hw : k * (w.re - w₀.re) = n * (Real.pi / 2)) :
    let t := Real.exp (-(k * (w.im - w₀.im)))
    ‖deriv (stripBlaschkeToDisk w₀ k) w‖ = 2 * k * t / (1 + t ^ 2) := by
  obtain ⟨hZ, hc, hZ'⟩ := stripChart_boundary hk hn hw
  rw [hZ'.deriv, norm_mul, hZ, mul_one, norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
  rcases hn with rfl | rfl <;> simp

private theorem disk_boundary_deriv {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι)
    (d : ℕ) (ha : ∀ i ∈ S, a i ≠ 0) (ha' : ∀ i ∈ S, ‖a i‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    let B := fun v : ℂ ↦ v ^ d * finiteProduct a m S v
    let p := (d : ℝ) + ∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) z
    ‖B z‖ = 1 ∧ 0 ≤ p ∧ HasDerivAt B ((p : ℂ) * B z / z) z := by
  let B := fun v : ℂ ↦ v ^ d * finiteProduct a m S v
  let p := (d : ℝ) + ∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) z
  have hz' : z ≠ 0 := norm_ne_zero_iff.mp (hz ▸ one_ne_zero)
  have hf : ‖finiteProduct a m S z‖ = 1 := by
    classical
    rw [finiteProduct, ← Finset.prod_coe_sort]
    exact (finiteProduct_inner (fun j : S ↦ a j) (fun j ↦ m j) Finset.univ
      (fun j ↦ ha j j.property) (fun j ↦ ha' j j.property)).2 z (mem_sphere_zero_iff_norm.mpr hz)
  have hb : ‖B z‖ = 1 := by simp [B, hf, hz]
  have hdf : DifferentiableAt ℂ (finiteProduct a m S) z :=
    DifferentiableAt.fun_finsetProd fun i hi ↦ ((normalizedFactor_boundary (ha i hi) (ha' i hi) hz).1.pow _)
  have hdb : DifferentiableAt ℂ B z := (differentiableAt_id.pow d).mul hdf
  have hlog : z * logDeriv B z = (p : ℂ) := by
    rw [show B = (fun v : ℂ ↦ v ^ d * finiteProduct a m S v) from rfl,
      logDeriv_fun_mul (f := fun v : ℂ ↦ v ^ d) z (pow_ne_zero d hz')
        (norm_ne_zero_iff.mp (hf ▸ one_ne_zero)) (differentiableAt_id.pow d) hdf,
      mul_add, logDeriv_pow, finiteProduct_logDeriv_sphere a m S ha ha' hz]
    simp [p, ← mul_div_assoc, mul_div_cancel_left₀ _ hz']
  have hp : 0 ≤ p := by
    refine add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i hi ↦ mul_nonneg (Nat.cast_nonneg _) ?_)
    simp only [poissonKernel_def, sub_zero, hz, one_pow]
    exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (ha' i hi).le)) (sq_nonneg _)
  refine ⟨hb, hp, hdb.hasDerivAt.congr_deriv ?_⟩
  have hbn : B z ≠ 0 := norm_ne_zero_iff.mp (hb ▸ one_ne_zero)
  rw [logDeriv_apply, ← mul_div_assoc, div_eq_iff hbn, mul_comm] at hlog
  exact (eq_div_iff hz').mpr hlog

/-- On either boundary line of the vertical strip, the outward derivative of the pulled-back
finite Blaschke product is its boundary value times the nonnegative Poisson density. The
conformal change of arclength contributes the factor `‖deriv Z w‖`. The exponent `d` counts
zeros at the center of the disk chart. -/
theorem stripFiniteProduct_hasDerivAt_outward {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (S : Finset ι) (d : ℕ) (ha : ∀ i ∈ S, a i ≠ 0) (ha' : ∀ i ∈ S, ‖a i‖ < 1)
    {w₀ w : ℂ} {k n : ℝ} (hk : 0 < k) (hn : n = 1 ∨ n = -1)
    (hw : k * (w.re - w₀.re) = n * (Real.pi / 2)) :
    let Z := stripBlaschkeToDisk w₀ k
    let B := fun v : ℂ ↦ v ^ d * finiteProduct a m S v
    let p := ‖deriv Z w‖ * ((d : ℝ) + ∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) (Z w))
    ‖B (Z w)‖ = 1 ∧ 0 ≤ p ∧
      HasDerivAt (fun r : ℝ ↦ B (Z (w + (n : ℂ) * r))) ((p : ℂ) * B (Z w)) 0 := by
  let Z := stripBlaschkeToDisk w₀ k
  let B := fun v : ℂ ↦ v ^ d * finiteProduct a m S v
  let q := (d : ℝ) + ∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) (Z w)
  let t := Real.exp (-(k * (w.im - w₀.im)))
  let c := 2 * k * t / (1 + t ^ 2)
  obtain ⟨hZ, _, hZ'⟩ := stripChart_boundary hk hn hw
  obtain ⟨hB, hq, hB'⟩ := disk_boundary_deriv a m S d ha ha' hZ
  have hc' : ‖deriv Z w‖ = c := norm_deriv_stripChart_boundary hk hn hw
  have hz0 : Z w ≠ 0 := norm_ne_zero_iff.mp (hZ ▸ one_ne_zero)
  have hline : HasDerivAt (fun r : ℝ ↦ w + (n : ℂ) * r) (n : ℂ) 0 := by
    simpa only [ofReal_one, mul_one] using (((hasDerivAt_id' (0 : ℝ)).ofReal_comp.const_mul (n : ℂ)).const_add w)
  refine ⟨hB, mul_nonneg (norm_nonneg _) hq, ?_⟩
  change HasDerivAt (fun r : ℝ ↦ B (Z (w + (n : ℂ) * r)))
    (((‖deriv Z w‖ * q : ℝ) : ℂ) * B (Z w)) 0
  rw [hc']
  apply ((hB'.comp w hZ').comp_of_eq 0 hline (by simp)).congr_deriv
  change (↑q * B (Z w) / Z w * (↑(n * c) * Z w)) * ↑n = ↑(c * q) * B (Z w)
  push_cast
  field_simp [hz0]
  rcases hn with rfl | rfl <;> push_cast <;> ring

/-- The boundary integrand in the unweighted Dirichlet energy formula on a strip. At either
boundary line the outward derivative of `‖Bg‖² − ‖g‖²` is twice the pulled-back Poisson
density times `‖g‖²`. This gives the positive boundary term for the order-one case of the
argument for Theorem 10.4.2.1 (p. 459) on #7405. -/
theorem stripFiniteProduct_hasDerivAt_norm_sq_gap {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (S : Finset ι) (d : ℕ) (ha : ∀ i ∈ S, a i ≠ 0) (ha' : ∀ i ∈ S, ‖a i‖ < 1)
    {w₀ w : ℂ} {k n : ℝ} (hk : 0 < k) (hn : n = 1 ∨ n = -1)
    (hw : k * (w.re - w₀.re) = n * (Real.pi / 2)) {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g w) :
    let Z := stripBlaschkeToDisk w₀ k
    let B := fun v : ℂ ↦ v ^ d * finiteProduct a m S v
    let p := ‖deriv Z w‖ * ((d : ℝ) + ∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) (Z w))
    let l := fun r : ℝ ↦ w + (n : ℂ) * r
    HasDerivAt (fun r : ℝ ↦ ‖B (Z (l r)) * g (l r)‖ ^ 2 - ‖g (l r)‖ ^ 2)
      (2 * p * ‖g w‖ ^ 2) 0 := by
  let Z := stripBlaschkeToDisk w₀ k
  let B := fun v : ℂ ↦ v ^ d * finiteProduct a m S v
  let p := ‖deriv Z w‖ * ((d : ℝ) + ∑ i ∈ S, (m i : ℝ) * poissonKernel 0 (a i) (Z w))
  let l := fun r : ℝ ↦ w + (n : ℂ) * r
  obtain ⟨hb, _, hB⟩ := stripFiniteProduct_hasDerivAt_outward a m S d ha ha' hk hn hw
  change ‖B (Z w)‖ = 1 at hb
  have hl : HasDerivAt l (n : ℂ) 0 := by
    simpa only [ofReal_one, mul_one] using
      (((hasDerivAt_id' (0 : ℝ)).ofReal_comp.const_mul (n : ℂ)).const_add w)
  have hl0 : l 0 = w := by simp [l]
  have hgg := (hg.hasDerivAt.comp_of_eq 0 hl hl0.symm).norm_sq
  change HasDerivAt (fun r : ℝ ↦ B (Z (l r))) ((p : ℂ) * B (Z w)) 0 at hB
  have hbb : HasDerivAt (fun r : ℝ ↦ ‖B (Z (l r))‖ ^ 2) (2 * p) 0 := by
    apply hB.norm_sq.congr_deriv
    rw [hl0, ← real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq, hb]
    ring
  convert! ((hbb.sub_const 1).mul hgg) using 1
  · funext r
    change ‖B (Z (l r)) * g (l r)‖ ^ 2 - ‖g (l r)‖ ^ 2 =
      (‖B (Z (l r))‖ ^ 2 - 1) * ‖g (l r)‖ ^ 2
    rw [norm_mul, mul_pow]
    ring
  · simp [Function.comp_apply, hl0, hb, p, Z]

private theorem poissonKernel_cayley_boundary {u v : ℂ} (hu : u.re = 0) (hv : 0 < v.re) :
    poissonKernel 0 ((v - 1) / (v + 1)) ((u - 1) / (u + 1)) =
      (1 + ‖u‖ ^ 2) * v.re / ‖u - v‖ ^ 2 := by
  have hu1 : u + 1 ≠ 0 := fun h ↦ by simpa [hu] using congrArg re h
  have hv1 : v + 1 ≠ 0 := by
    intro h
    have hh := congrArg re h
    simp at hh
    linarith
  have huv : u - v ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [← h, hu] at hv)
  have hdiff : (u - 1) / (u + 1) - (v - 1) / (v + 1) = 2 * (u - v) / ((u + 1) * (v + 1)) := by
    field_simp [hu1, hv1]
    ring
  have hdiff' : (u - 1) / (u + 1) - (v - 1) / (v + 1) ≠ 0 := by
    rw [hdiff]
    exact div_ne_zero (mul_ne_zero two_ne_zero huv) (mul_ne_zero hu1 hv1)
  have hC : (((u - 1) / (u + 1) + (v - 1) / (v + 1)) /
      ((u - 1) / (u + 1) - (v - 1) / (v + 1))) = (u * v - 1) / (u - v) := by
    rw [div_eq_div_iff hdiff' huv]
    field_simp [hu1, hv1]
    ring
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def,
    sub_zero, sub_zero, hC, div_re, ← add_div, normSq_eq_norm_sq]
  congr 1
  simp [← normSq_eq_norm_sq, normSq_apply, hu, mul_re, mul_im]
  ring

private theorem strip_poissonKernel_eq_halfPlane {w₀ w ρ : ℂ} {k n : ℝ} (hk : 0 < k)
    (hn : n = 1 ∨ n = -1) (hw : k * (w.re - w₀.re) = n * (Real.pi / 2))
    (hρ : |ρ.re - w₀.re| < (Real.pi / 2) / k) :
    let Z := stripBlaschkeToDisk w₀ k
    let U := stripExp w₀ k
    ‖deriv Z w‖ * poissonKernel 0 (Z ρ) (Z w) =
      2 * k * ‖U w‖ * (U ρ).re / ‖U w - U ρ‖ ^ 2 := by
  let U := stripExp w₀ k
  have hu : (U w).re = 0 := by
    rw [show U w = _ from stripExp_boundary hn hw, mul_I_re, ofReal_im, neg_zero]
  have hC := poissonKernel_cayley_boundary hu (stripExp_re_pos hk hρ)
  change poissonKernel 0 (stripBlaschkeToDisk w₀ k ρ) (stripBlaschkeToDisk w₀ k w) = _ at hC
  dsimp only
  rw [hC, norm_deriv_stripChart_boundary hk hn hw, ← stripExp_norm w₀ k w, div_mul_div_comm,
    div_eq_mul_inv]
  change _ = 2 * k * ‖U w‖ * (U ρ).re / ‖U w - U ρ‖ ^ 2
  field_simp [U, show 1 + ‖stripExp w₀ k w‖ ^ 2 ≠ 0 by positivity]
  ring

private theorem kernel_bound_of_separated_radii {k x y D : ℝ} (hk : 0 < k) (hx : 0 < x)
    (hy : 0 < y) (hxy : 2 * x ≤ y) (hD : |x - y| ≤ D) :
    2 * k * x * y / D ^ 2 ≤ 8 * k * (x / y) := by
  have hhalf : y / 2 ≤ D := by
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)] at hD
    linarith
  calc
    _ ≤ 2 * k * x * y / (y / 2) ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) hhalf 2)
    _ = _ := by field_simp; ring

/-- The boundary Poisson density of the vertical strip decays exponentially away from the
height of its pole. The constant is uniform up to either boundary line: the horizontal
coordinate of the pole can approach that line arbitrarily closely. -/
theorem strip_poissonKernel_le_exp_height {w₀ w ρ : ℂ} {k n : ℝ} (hk : 0 < k)
    (hn : n = 1 ∨ n = -1) (hw : k * (w.re - w₀.re) = n * (Real.pi / 2))
    (hρ : |ρ.re - w₀.re| < (Real.pi / 2) / k)
    (hfar : Real.log 2 ≤ k * |w.im - ρ.im|) :
    let Z := stripBlaschkeToDisk w₀ k
    ‖deriv Z w‖ * poissonKernel 0 (Z ρ) (Z w) ≤
      8 * k * Real.exp (-(k * |w.im - ρ.im|)) := by
  let U := stripExp w₀ k
  have hnormpos (z : ℂ) : 0 < ‖U z‖ := norm_pos_iff.mpr (exp_ne_zero _)
  dsimp only
  rw [strip_poissonKernel_eq_halfPlane hk hn hw hρ]
  have htail : Real.exp (-(k * |w.im - ρ.im|)) ≤ 2⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by norm_num) (by
      simpa only [Real.exp_log (by norm_num : 0 < (2 : ℝ))] using Real.exp_le_exp.mpr hfar)
  have hratio (z z' : ℂ) : ‖U z‖ / ‖U z'‖ = Real.exp (-(k * (z.im - z'.im))) := by
    rw [show U = stripExp w₀ k from rfl, stripExp_norm, stripExp_norm, ← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ 2 * k * ‖U w‖ * ‖U ρ‖ / ‖U w - U ρ‖ ^ 2 := by
      gcongr
      exact re_le_norm _
    _ ≤ _ := by
      rcases le_total ρ.im w.im with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h), ← hratio] at htail ⊢
        apply kernel_bound_of_separated_radii hk (hnormpos w) (hnormpos ρ) _
          (abs_norm_sub_norm_le (U w) (U ρ))
        have hh := (div_le_iff₀ (hnormpos ρ)).mp htail
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, ← hratio] at htail ⊢
        rw [mul_right_comm (2*k) ‖U w‖ ‖U ρ‖, norm_sub_rev]
        apply kernel_bound_of_separated_radii hk (hnormpos ρ) (hnormpos w) _
          (abs_norm_sub_norm_le (U ρ) (U w))
        have hh := (div_le_iff₀ (hnormpos w)).mp htail
        linarith

/-- The arclength density on one boundary line for a pole in the strip, with the convention
that both lines together have mass `2π`. The sign `n = ±1` selects the boundary line. -/
def stripBoundaryPoissonKernel (w₀ : ℂ) (k n : ℝ) (ρ : ℂ) (y : ℝ) : ℝ :=
  let w : ℂ := ⟨w₀.re + n * ((Real.pi / 2) / k), y⟩
  let Z := stripBlaschkeToDisk w₀ k
  ‖deriv Z w‖ * poissonKernel 0 (Z ρ) (Z w)

private theorem stripBoundaryPoissonKernel_eq {w₀ ρ : ℂ} {k n : ℝ} (hk : 0 < k)
    (hn : n = 1 ∨ n = -1) (hρ : |ρ.re - w₀.re| < (Real.pi / 2) / k) (y : ℝ) :
    let v := stripExp w₀ k ρ
    let t := Real.exp (-(k * (y - w₀.im)))
    stripBoundaryPoissonKernel w₀ k n ρ y = 2 * k * t * v.re / (v.re ^ 2 + (t - n * v.im) ^ 2) := by
  let w : ℂ := ⟨w₀.re + n * ((Real.pi / 2) / k), y⟩
  have hw : k * (w.re - w₀.re) = n * (Real.pi / 2) := by dsimp [w]; field_simp; ring
  rw [stripBoundaryPoissonKernel, strip_poissonKernel_eq_halfPlane hk hn hw hρ, stripExp_norm]
  dsimp only
  congr 1
  rw [← normSq_eq_norm_sq, stripExp_boundary hn hw, normSq_apply]
  simp only [sub_re, sub_im, mul_I_re, mul_I_im, ofReal_re, ofReal_im, neg_zero]
  rcases hn with rfl | rfl <;> dsimp [w] <;> ring

/-- The density on either boundary line is nonnegative, integrable, and has mass at most `2π`. -/
theorem stripBoundaryPoissonKernel_mass_bound {w₀ ρ : ℂ} {k n : ℝ} (hk : 0 < k)
    (hn : n = 1 ∨ n = -1) (hρ : |ρ.re - w₀.re| < (Real.pi / 2) / k) :
    let P := stripBoundaryPoissonKernel w₀ k n ρ
    Integrable P ∧ (∀ y, 0 ≤ P y) ∧ ∫ y, P y ≤ 2 * Real.pi := by
  let v := stripExp w₀ k ρ
  have ha : 0 < v.re := stripExp_re_pos hk hρ
  let a : ℝ≥0 := ⟨v.re, ha.le⟩
  have ha0 : a ≠ 0 := fun h ↦ ha.ne' (congrArg NNReal.toReal h)
  let C := ProbabilityTheory.cauchyPDFReal (n * v.im) a
  let G := fun x : ℝ ↦ Real.exp x * C (Real.exp x)
  let P := stripBoundaryPoissonKernel w₀ k n ρ
  have hC : Integrable C := ProbabilityTheory.integrable_cauchyPDFReal _
  have hG : Integrable G := (integrable_comp_exp C).2 hC.integrableOn
  have hcp : ∀ t, 0 ≤ C t := fun t ↦ (ProbabilityTheory.cauchyPDF_pos _ ha0 t).le
  have hP : P = fun y ↦ (2 * Real.pi * k) * G ((-k) * (y - w₀.im)) := by
    funext y
    rw [show P y = _ from stripBoundaryPoissonKernel_eq hk hn hρ y]
    dsimp only [G, C]
    rw [ProbabilityTheory.cauchyPDFReal_def, show (a : ℝ) = v.re by rfl]
    dsimp only [v]
    rw [neg_mul, add_comm ((Real.exp _ - _) ^ 2), div_eq_mul_inv]
    field_simp [Real.pi_ne_zero]
  have hmass : (∫ t in Ioi (0:ℝ), C t) ≤ 1 := by
    exact (setIntegral_le_integral hC (.of_forall hcp)).trans_eq
      (ProbabilityTheory.integral_cauchyPDFReal_eq_one _ ha0)
  change Integrable P ∧ (∀ y, 0 ≤ P y) ∧ ∫ y, P y ≤ 2 * Real.pi
  rw [hP]
  refine ⟨((hG.comp_mul_left' (neg_ne_zero.mpr hk.ne')).comp_sub_right w₀.im).const_mul _, ?_, ?_⟩
  · intro y
    dsimp [G]
    exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (hcp _))
  · rw [integral_const_mul, integral_sub_right_eq_self (fun y : ℝ ↦ G (-k * y)) w₀.im,
      Measure.integral_comp_mul_left G (-k)]
    have he : (∫ x, G x) = ∫ t in Ioi (0 : ℝ), C t := integral_comp_exp C
    rw [he, abs_inv, abs_neg, abs_of_pos hk, smul_eq_mul, ← mul_assoc, mul_assoc (2 * Real.pi),
      mul_inv_cancel₀ hk.ne', mul_one]
    exact mul_le_of_le_one_right (by positivity) hmass

private theorem integrable_poly_exp_abs {k : ℝ} (hk : 0 < k) (N : ℕ) :
    Integrable (fun x : ℝ ↦ (1 + |x|) ^ N * Real.exp (-(k * |x|))) := by
  let h := k / 2
  have hh : 0 < h := half_pos hk
  let A := (N.factorial : ℝ) / h ^ N
  refine ((integrable_exp_neg_mul_abs hh).const_mul (A * Real.exp h)).mono'
    (by fun_prop) (.of_forall fun x ↦ ?_)
  have hp : (1 + |x|) ^ N ≤ A * Real.exp (h * (1 + |x|)) := by
    have H := Real.pow_div_factorial_le_exp _ (mul_nonneg hh.le (by positivity : 0 ≤ 1 + |x|)) N
    rw [mul_pow, div_le_iff₀ (by positivity)] at H
    dsimp [A]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith only [H]
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (A * Real.exp (h * (1 + |x|))) * Real.exp (-(k * |x|)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [h]
      ring

/-- Every centered polynomial moment of the strip's boundary Poisson density is bounded,
uniformly over all interior poles and over both boundary lines. -/
theorem stripBoundaryPoissonKernel_moment_bound {k : ℝ} (hk : 0 < k) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w₀ ρ : ℂ} {n : ℝ}, n = 1 ∨ n = -1 →
      |ρ.re - w₀.re| < (Real.pi / 2) / k →
      let P := stripBoundaryPoissonKernel w₀ k n ρ
      let M := fun y : ℝ ↦ (1 + |y - ρ.im|) ^ N * P y
      Integrable M ∧ ∫ y, M y ≤ C := by
  let R := Real.log 2 / k
  have hR : 0 ≤ R := div_nonneg (Real.log_nonneg (by norm_num)) hk.le
  let D := (1 + R) ^ N
  have hD : 0 ≤ D := pow_nonneg (by linarith) _
  let E := fun x : ℝ ↦ (1 + |x|) ^ N * Real.exp (-(k * |x|))
  have hE : Integrable E := integrable_poly_exp_abs hk N
  have hEpos (x : ℝ) : 0 ≤ E x := by dsimp [E]; positivity
  refine ⟨D * (2 * Real.pi) + 8 * k * ∫ x, E x,
    add_nonneg (mul_nonneg hD (by positivity)) (mul_nonneg (by positivity) (integral_nonneg hEpos)), ?_⟩
  intro w₀ ρ n hn hρ
  let P := stripBoundaryPoissonKernel w₀ k n ρ
  obtain ⟨hP, hPpos, hPmass⟩ := stripBoundaryPoissonKernel_mass_bound hk hn hρ
  let M := fun y : ℝ ↦ (1 + |y - ρ.im|) ^ N * P y
  let H := fun y : ℝ ↦ D * P y + (8 * k) * E (y - ρ.im)
  have hH : Integrable H := (hP.const_mul D).add ((hE.comp_sub_right ρ.im).const_mul _)
  have hMpos (y : ℝ) : 0 ≤ M y := mul_nonneg (by positivity) (hPpos _)
  have hMH (y : ℝ) : M y ≤ H y := by
    by_cases h : |y - ρ.im| ≤ R
    · apply le_add_of_le_of_nonneg _ (mul_nonneg (by positivity) (hEpos _))
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (hPpos y)
    · have hf : Real.log 2 ≤ k * |y - ρ.im| := by
        rw [mul_comm]
        exact (div_le_iff₀ hk).mp (le_of_not_ge h)
      let w : ℂ := ⟨w₀.re + n * ((Real.pi / 2) / k), y⟩
      have hw : k * (w.re - w₀.re) = n * (Real.pi / 2) := by dsimp [w]; field_simp; ring
      have ht : P y ≤ 8 * k * Real.exp (-(k * |y - ρ.im|)) :=
        strip_poissonKernel_le_exp_height hk hn hw hρ hf
      apply le_add_of_nonneg_of_le (mul_nonneg hD (hPpos y))
      calc
        M y ≤ (1 + |y - ρ.im|) ^ N * (8 * k * Real.exp (-(k * |y - ρ.im|))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by dsimp [E]; ring
  have hM : Integrable M := hH.mono'
    ((show Continuous (fun y : ℝ ↦ (1 + |y - ρ.im|) ^ N) by fun_prop).aestronglyMeasurable.mul
      hP.aestronglyMeasurable) (.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hMpos _)]; exact hMH y)
  refine ⟨hM, (integral_mono hM hH hMH).trans ?_⟩
  dsimp only [H]
  rw [integral_add (hP.const_mul D) ((hE.comp_sub_right ρ.im).const_mul _), integral_const_mul,
    integral_const_mul, integral_sub_right_eq_self E ρ.im]
  exact add_le_add (mul_le_mul_of_nonneg_left hPmass hD) le_rfl

/-- A test bounded by `A * (1 + |y − Im ρ|)^N` has squared boundary integral at most
`C * A²` against the strip Poisson density of `ρ`. This is the one-site Hardy estimate at
order zero on the boundary route to Theorem 10.4.2.1, p. 459. The constant depends only on
the width and the exponent, including when the pole approaches either boundary. -/
theorem stripBoundaryPoissonKernel_test_bound {k : ℝ} (hk : 0 < k) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w₀ ρ : ℂ} {n : ℝ}, n = 1 ∨ n = -1 →
      |ρ.re - w₀.re| < (Real.pi / 2) / k → ∀ {A : ℝ} {f : ℝ → ℂ},
      AEStronglyMeasurable f → (∀ y, ‖f y‖ ≤ A * (1 + |y - ρ.im|) ^ N) →
      let Q := fun y : ℝ ↦ ‖f y‖ ^ 2 * stripBoundaryPoissonKernel w₀ k n ρ y
      Integrable Q ∧ ∫ y, Q y ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hm⟩ := stripBoundaryPoissonKernel_moment_bound hk (N + N)
  refine ⟨C, hC, ?_⟩
  intro w₀ ρ n hn hρ A f hf hbound
  let P := stripBoundaryPoissonKernel w₀ k n ρ
  let M := fun y : ℝ ↦ (1 + |y - ρ.im|) ^ (N + N) * P y
  let Q := fun y : ℝ ↦ ‖f y‖ ^ 2 * P y
  obtain ⟨hP, hPpos, _⟩ := stripBoundaryPoissonKernel_mass_bound hk hn hρ
  obtain ⟨hM, hmass⟩ := hm hn hρ
  have hQpos (y : ℝ) : 0 ≤ Q y := mul_nonneg (sq_nonneg _) (hPpos y)
  have hQM (y : ℝ) : Q y ≤ A ^ 2 * M y := by
    calc
      Q y ≤ (A * (1 + |y - ρ.im|) ^ N) ^ 2 * P y :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbound y) _) (hPpos y)
      _ = _ := by dsimp [M]; rw [mul_pow, pow_add]; ring
  have hQ : Integrable Q := (hM.const_mul (A ^ 2)).mono'
    ((hf.norm.pow _).mul hP.aestronglyMeasurable)
    (.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hQpos _)]; exact hQM y)
  refine ⟨hQ, (integral_mono hQ (hM.const_mul _) hQM).trans ?_⟩
  rw [integral_const_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left hmass (sq_nonneg _)

end RiemannMasullo.Blaschke