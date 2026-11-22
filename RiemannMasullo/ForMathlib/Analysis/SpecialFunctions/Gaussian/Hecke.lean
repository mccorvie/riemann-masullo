module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Mellin and Fourier transforms of Gaussian monomials

A complex character of angular weight `m` pairs with the monomial of weight `-m`.
For the trace pairing the Fourier transform exchanges the two monomials. Differentiating a
two-variable Gaussian generating function computes the multiplier for all integer weights.
-/

open Set MeasureTheory Filter Function Real Complex
open scoped Topology FourierTransform ContDiff
@[expose] public noncomputable section

namespace RiemannMasullo.HeckeGaussian

/-- A Schwartz function on the line that agrees with the negative exponential on the positive half-line. -/
private theorem exists_schwartz_exp_neg :
    ∃ f : SchwartzMap ℝ ℂ, ∀ x : ℝ, 0 ≤ x → f x = (Real.exp (-x) : ℂ) := by
  let g (x : ℝ) := Real.smoothTransition (x + 1) * Real.exp (-x)
  have hs : ContDiff ℝ ∞ g := (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (Real.contDiff_exp.comp contDiff_id.neg)
  have hpos (x : ℝ) (hx : 0 ≤ x) : g x = Real.exp (-x) := by
    simp [g, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x + 1)]
  have hneg (x : ℝ) (hx : x ≤ -1) : g x = 0 := by
    simp [g, Real.smoothTransition.zero_of_nonpos (by linarith : x + 1 ≤ 0)]
  have hd (n : ℕ) : iteratedDeriv n (fun x : ℝ ↦ Real.exp (-x)) =
      fun x : ℝ ↦ (-1 : ℝ) ^ n * Real.exp (-x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have d := ((hasDerivAt_id x).neg.exp.const_mul ((-1 : ℝ) ^ n)).deriv
      simpa [pow_succ, mul_assoc] using d
  let f : SchwartzMap ℝ ℝ :=
    { toFun := g, smooth' := hs
      decay' := by
        intro k n
        let w (x : ℝ) := ‖x‖ ^ k * ‖iteratedDeriv n g x‖
        have hw : Continuous w := (continuous_norm.pow _).mul
          (hs.continuous_iteratedDeriv n (by simp)).norm
        obtain ⟨M, hM⟩ := (isCompact_Icc (α := ℝ) (a := -1) (b := 0)).bddAbove_image hw.continuousOn
        refine ⟨max 0 (max M k.factorial), fun x ↦ ?_⟩
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        rcases lt_or_ge x (-1) with hx | hx
        · have h : g =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
            (gt_mem_nhds hx).mono fun y hy ↦ hneg y hy.le
          rw [(h.iteratedDeriv n).eq_of_nhds]
          simp
        rcases le_or_gt x 0 with hx' | hx'
        · exact (hM ⟨x, ⟨hx, hx'⟩, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
        · have h : g =ᶠ[𝓝 x] fun y ↦ Real.exp (-y) :=
            (lt_mem_nhds hx').mono fun y hy ↦ hpos y hy.le
          rw [(h.iteratedDeriv n).eq_of_nhds, hd]
          simp only [Real.norm_eq_abs, abs_of_pos hx', Real.exp_neg, ← div_eq_mul_inv]
          apply le_trans _ ((le_max_right _ _).trans (le_max_right _ _))
          rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (Real.exp_pos _), mul_one_div]
          apply (div_le_iff₀ (Real.exp_pos _)).mpr
          exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _))).mp
            (Real.pow_div_factorial_le_exp x hx'.le k) |>.trans_eq (mul_comm _ _) }
  exact ⟨f.postcompCLM Complex.ofRealCLM, fun x hx ↦ congrArg Complex.ofReal (hpos x hx)⟩

/-- A finite product of functions of temperate growth has temperate growth. -/
private theorem temperate_fintype_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} (h : ∀ i, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i, f i x).HasTemperateGrowth := by
  classical
  generalize (Finset.univ : Finset ι) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simpa [Finset.prod_insert hi] using! (h i).mul ih

/-- Multiplying weighted real and complex Gaussians by temperate coordinate factors gives a
Schwartz function on the mixed space. -/
theorem mixedGaussian_schwartz {R C : Type*} [Fintype R] [Fintype C]
    (p : R → ℝ → ℂ) (q : C → ℂ → ℂ) (hp : ∀ i, (p i).HasTemperateGrowth)
    (hq : ∀ j, (q j).HasTemperateGrowth) :
    ∃ f : SchwartzMap ((R → ℝ) × (C → ℂ)) ℂ, ∀ x,
      f x = (∏ i, p i (x.1 i) * (Real.exp (-(Real.pi * ‖x.1 i‖ ^ 2)) : ℂ)) *
        (∏ j, q j (x.2 j) * (Real.exp (-(2 * Real.pi * ‖x.2 j‖ ^ 2)) : ℂ)) := by
  let E := (R → ℝ) × (C → ℂ)
  let r (i : R) : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  let c (j : C) : E →L[ℝ] ℂ := (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ _ _)
  let Q (x : E) := (∑ i, Real.pi * ‖r i x‖ ^ 2) + ∑ j, 2 * Real.pi * ‖c j x‖ ^ 2
  let P (x : E) := (∏ i, p i (r i x)) * ∏ j, q j (c j x)
  have hP : P.HasTemperateGrowth := (temperate_fintype_prod (fun i ↦ (hp i).comp (r i).hasTemperateGrowth)).mul
    (temperate_fintype_prod (fun j ↦ (hq j).comp (c j).hasTemperateGrowth))
  have hQ : Q.HasTemperateGrowth := by
    apply HasTemperateGrowth.add <;> apply HasTemperateGrowth.sum <;> intro i _
    · exact (HasTemperateGrowth.const _).mul ((hasTemperateGrowth_norm_sq ℝ).comp (r i).hasTemperateGrowth)
    · exact (HasTemperateGrowth.const _).mul ((hasTemperateGrowth_norm_sq ℂ).comp (c i).hasTemperateGrowth)
  have hQ0 (x : E) : 0 ≤ Q x := by dsimp only [Q]; positivity
  have hsize (x : E) : ‖x‖ ≤ 1 + ‖Q x‖ := by
    have hp' := Real.pi_gt_three
    rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 x)]
    change max ‖x.1‖ ‖x.2‖ ≤ _
    apply max_le <;> apply (pi_norm_le_iff_of_nonneg (by linarith [hQ0 x])).mpr <;> intro i
    · have hi := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ Real.pi * ‖r i x‖ ^ 2)
          (fun i _ ↦ by positivity) (Finset.mem_univ i)
      have h₂ : 0 ≤ ∑ j, 2 * Real.pi * ‖c j x‖ ^ 2 := by positivity
      change ‖r i x‖ ≤ _
      dsimp only [Q]
      nlinarith [sq_nonneg (‖r i x‖ - 1), mul_nonneg (sub_nonneg.mpr (by linarith : 1 ≤ Real.pi))
        (sq_nonneg ‖r i x‖)]
    · have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ 2 * Real.pi * ‖c j x‖ ^ 2)
          (fun j _ ↦ by positivity) (Finset.mem_univ i)
      have h₁ : 0 ≤ ∑ i, Real.pi * ‖r i x‖ ^ 2 := by positivity
      change ‖c i x‖ ≤ _
      dsimp only [Q]
      nlinarith [sq_nonneg (‖c i x‖ - 1), mul_nonneg (sub_nonneg.mpr (by linarith : 1 ≤ 2 * Real.pi))
        (sq_nonneg ‖c i x‖)]
  obtain ⟨g, hg⟩ := exists_schwartz_exp_neg
  let s := SchwartzMap.compCLM ℂ hQ ⟨1, 1, fun x ↦ by simpa using hsize x⟩ g
  refine ⟨SchwartzMap.smulLeftCLM ℂ P s, fun x ↦ ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hP]
  change P x * g (Q x) = _
  rw [hg _ (hQ0 _)]
  simp only [P, Q, Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum,
    ← Finset.sum_neg_distrib, neg_add, Real.exp_add, Complex.ofReal_mul]
  exact mul_mul_mul_comm _ _ _ _

/-- A complex linear form in the two real Gaussian coordinates. -/
private theorem planeGaussianGenerating (b : ℝ) (hb : 0 < b) (A B : ℂ) :
    (∫ z : ℂ, Complex.exp (-(b : ℂ) * (‖z‖ : ℂ) ^ 2 + A * z.re + B * z.im)) =
      ((Real.pi / b : ℝ) : ℂ) * Complex.exp ((A ^ 2 + B ^ 2) / (4 * b)) := by
  let q (c : ℂ) (r : ℝ) := Complex.exp (-(b : ℂ) * (r : ℂ) ^ 2 + c * r + 0)
  have hq (c : ℂ) : (∫ r : ℝ, q c r) =
      ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * Complex.exp (c ^ 2 / (4 * b)) := by
    dsimp only [q]
    rw [integral_cexp_quadratic (b := -(b : ℂ)) (by simpa)]
    simp [div_neg]
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫ p : ℝ × ℝ, _) = _
  have hform (p : ℝ × ℝ) :
      Complex.exp (-(b : ℂ) * (‖Complex.measurableEquivRealProd.symm p‖ : ℂ) ^ 2 +
        A * (Complex.measurableEquivRealProd.symm p).re + B * (Complex.measurableEquivRealProd.symm p).im)
      = q A p.1 * q B p.2 := by
    rw [show ((‖Complex.measurableEquivRealProd.symm p‖ : ℝ) : ℂ) ^ 2 =
        (p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2 by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]
      change ((p.1 * p.1 + p.2 * p.2 : ℝ) : ℂ) = _
      push_cast
      ring]
    dsimp only [q]
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    change _ + A * (p.1 : ℂ) + B * (p.2 : ℂ) = _
    ring
  rw [show (fun p : ℝ × ℝ ↦ Complex.exp (-(b : ℂ) * (‖Complex.measurableEquivRealProd.symm p‖ : ℂ) ^ 2 +
    A * (Complex.measurableEquivRealProd.symm p).re + B * (Complex.measurableEquivRealProd.symm p).im)) = _
      from funext hform, Measure.volume_eq_prod, integral_prod_mul, hq, hq, mul_mul_mul_comm, ← Complex.exp_add]
  have hpb : (Real.pi : ℂ) / b ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (Complex.ofReal_ne_zero.mpr hb.ne')
  rw [← Complex.cpow_add _ _ hpb, show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num,
    Complex.cpow_one, ← add_div, Complex.ofReal_div]

/-- With Gaussian decay one may differentiate the exponential generating function
of power moments under the integral sign at every complex parameter. -/
private theorem planeMoment_from_generating {F p : ℂ → ℂ} (hF : Continuous F) (hp : Continuous p)
    (hpn : ∀ z, ‖p z‖ ≤ ‖z‖) {b : ℝ} (hb : 0 < b)
    (hdec : ∀ z, ‖F z‖ ≤ Real.exp (-b * ‖z‖ ^ 2))
    (K c : ℂ) (hG : ∀ w : ℂ, (∫ z, Complex.exp (w * p z) * F z) = K * Complex.exp (w * c)) :
    ∀ n : ℕ, (∫ z, p z ^ n * F z) = K * c ^ n := by
  let G (n : ℕ) (w z : ℂ) := p z ^ n * Complex.exp (w * p z) * F z
  have hbound (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
      ∃ B : ℂ → ℝ, Integrable B ∧ ∀ w z, ‖w‖ ≤ R → ‖G n w z‖ ≤ B z := by
    let C := (n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (2 * b))
    let B (z : ℂ) := C * Real.exp (-(b / 2) * ‖z‖ ^ 2)
    have hhalf := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := ℂ) (b := ((b / 2 : ℝ) : ℂ)) (by simpa using half_pos hb) 0 0
    have hB : Integrable B := by
      apply Integrable.const_mul _ (μ := volume)
      convert! hhalf.norm using 1
      funext z
      simp [Complex.norm_exp, Complex.mul_re, sq]
    refine ⟨B, hB, fun w z hw ↦ ?_⟩
    let r := ‖z‖
    have hn : ‖p z‖ ^ n ≤ (n.factorial : ℝ) * Real.exp r :=
      (pow_le_pow_left₀ (norm_nonneg _) (hpn z) _).trans (by
        simpa only [mul_comm] using (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _))).mp
          (Real.pow_div_factorial_le_exp r (norm_nonneg z) n))
    have hre : (w * p z).re ≤ R * r := (Complex.re_le_norm _).trans
      (by rw [norm_mul]; exact mul_le_mul hw (hpn z) (norm_nonneg _) hR)
    have hsq : (R + 1) * r - b * r ^ 2 ≤ (R + 1) ^ 2 / (2 * b) - b / 2 * r ^ 2 := by
      have hh := sq_nonneg (R + 1 - b * r)
      have hb' : 0 < 2 * b := by positivity
      rw [le_sub_iff_add_le, le_div_iff₀ hb']
      nlinarith
    dsimp only [G]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    calc
      _ ≤ ((n.factorial : ℝ) * Real.exp r) * Real.exp (R * r) * Real.exp (-b * r ^ 2) :=
        mul_le_mul (mul_le_mul hn (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity))
          (hdec z) (norm_nonneg _) (by positivity)
      _ = (n.factorial : ℝ) * Real.exp ((R + 1) * r - b * r ^ 2) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ n.factorial * Real.exp ((R + 1) ^ 2 / (2 * b) - b / 2 * r ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq) (Nat.cast_nonneg _)
      _ = _ := by dsimp [B, C, r]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hcont (n : ℕ) (w : ℂ) : Continuous (G n w) := by dsimp [G]; fun_prop
  have hI (n : ℕ) (w : ℂ) : Integrable (G n w) := by
    obtain ⟨B, hB, h⟩ := hbound n ‖w‖ (norm_nonneg _)
    exact hB.mono' (hcont n w).aestronglyMeasurable (ae_of_all _ fun z ↦ h w z le_rfl)
  have hd (n : ℕ) (w : ℂ) :
      HasDerivAt (fun u ↦ ∫ z, G n u z) (∫ z, G (n + 1) w z) w := by
    obtain ⟨B, hB, h⟩ := hbound (n + 1) (‖w‖+1) (by positivity)
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w one_pos)
      (.of_forall (fun u ↦ (hcont n u).aestronglyMeasurable)) (hI n w)
      (hcont (n + 1) w).aestronglyMeasurable _ hB _).2
    · refine ae_of_all _ fun z u hu ↦ h u z ?_
      have ht := dist_triangle u w 0
      rw [dist_zero_right, dist_zero_right] at ht
      linarith [Metric.mem_ball.mp hu]
    · refine ae_of_all _ fun z u _ ↦ ?_
      convert ((((hasDerivAt_id u).mul_const (p z)).cexp.const_mul (p z ^ n)).mul_const (F z)) using 1 <;> first | rfl | (simp only [G, pow_succ, id_eq, one_mul]; ring)
  have he (n : ℕ) : ∀ w : ℂ, (∫ z, G n w z) = K * c ^ n * Complex.exp (w * c) := by
    induction n with
    | zero => simpa [G] using hG
    | succ n ih =>
      intro w
      have d := hd n w
      rw [funext ih] at d
      have d' := (((hasDerivAt_id w).mul_const c).cexp.const_mul (K * c ^ n))
      rw [d.unique d']
      simp [pow_succ]
      ring
  intro n
  simpa [G] using he n 0

/-- Select the identity or the complex conjugate as the angular coordinate. -/
private def angularCoord (e : Bool) (z : ℂ) : ℂ := if e then star z else z

/-- Gaussian integration for a holomorphic or antiholomorphic monomial and the trace pairing. -/
private theorem planeGaussianMoments (b : ℝ) (hb : 0 < b) (e : Bool) (n : ℕ) (y : ℂ) :
    (∫ z : ℂ, angularCoord e z ^ n *
      Complex.exp (-(b : ℂ) * (‖z‖ : ℂ) ^ 2 - 2 * b * Complex.I * (z * y).re)) =
      ((Real.pi / b : ℝ) : ℂ) * Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2) *
        (-Complex.I * angularCoord (!e) y) ^ n := by
  let phase (z : ℂ) := Complex.exp (-(b : ℂ) * (‖z‖ : ℂ) ^ 2 - 2 * b * Complex.I * (z * y).re)
  let k : ℂ := if e then -Complex.I else Complex.I
  have hcoord (z : ℂ) : angularCoord e z = z.re + k * z.im := by
    cases e <;> apply Complex.ext <;> simp [angularCoord, k, Complex.mul_re, Complex.mul_im]
  have hdual : angularCoord (!e) y = y.re - k * y.im := by
    cases e <;> apply Complex.ext <;> simp [angularCoord, k, Complex.mul_re, Complex.mul_im]
  have hdec (z : ℂ) : ‖phase z‖ ≤ Real.exp (-b * ‖z‖ ^ 2) := by
    simp [phase, Complex.norm_exp, Complex.mul_re, sq]
  apply planeMoment_from_generating (F := phase) (p := angularCoord e)
    (by dsimp [phase]; fun_prop) (by cases e; exact continuous_id; exact Complex.continuous_conj)
    (by intro z; cases e <;> simp [angularCoord]) hb hdec _ _ _ n
  intro w
  let A := w - 2 * b * Complex.I * y.re
  let B := k * w + 2 * b * Complex.I * y.im
  have hmul (z : ℂ) : Complex.exp (w * angularCoord e z) * phase z =
      Complex.exp (-(b : ℂ) * (‖z‖ : ℂ) ^ 2 + A * z.re + B * z.im) := by
    dsimp only [phase]
    rw [← Complex.exp_add, hcoord, Complex.mul_re, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul]
    congr 1
    dsimp [A, B]
    ring
  rw [show (fun z : ℂ ↦ Complex.exp (w * angularCoord e z) * phase z) = _ from funext hmul,
    planeGaussianGenerating b hb, mul_assoc, ← Complex.exp_add, hdual]
  congr 2
  have hk : k ^ 2 = -1 := by cases e <;> simp [k, Complex.I_sq]
  have hn : (‖y‖ : ℂ) ^ 2 = (y.re : ℂ) ^ 2 + (y.im : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  dsimp [A, B]
  rw [hn]
  field_simp [(Complex.ofReal_ne_zero.mpr hb.ne')]
  linear_combination (w ^ 2) * hk + (4 * (b : ℂ) ^ 2 * ((y.re : ℂ) ^ 2 + (y.im : ℂ) ^ 2)) * Complex.I_sq

/-- The Mellin transform of a Gaussian on the positive half-line. -/
private theorem radialMellin (b : ℝ) (hb : 0 < b) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun x : ℝ ↦ (Real.exp (-(b * x ^ 2)) : ℂ)) s =
      (2 : ℂ)⁻¹ * ((b : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)) := by
  let f (x : ℝ) := (Real.exp (-x) : ℂ)
  have h := mellin_comp_rpow (fun x ↦ f (b * x)) s (2 : ℝ)
  simp only [Real.rpow_two, abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.ofReal_ofNat,
    Complex.real_smul, Complex.ofReal_inv, mellin_comp_mul_left f _ hb, smul_eq_mul] at h
  rw [← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral] at h
  · exact h
  · simpa using hs

/-- Absorb the radial powers from the character and the monomial into the Mellin parameter. -/
private theorem radialMellin_power (b : ℝ) (hb : 0 < b) (d n : ℕ) (s : ℂ)
    (hs : 0 < ((d : ℂ) * s + n).re) :
    (∫ r in Ioi (0 : ℝ), r⁻¹ • ((r : ℂ) ^ n * (Real.exp (-(b * r ^ 2)) : ℂ) *
      ((r ^ d : ℝ) : ℂ) ^ s)) =
      (2 : ℂ)⁻¹ * ((b : ℂ) ^ (-(((d : ℂ) * s + n) / 2)) * Complex.Gamma (((d : ℂ) * s + n) / 2)) := by
  rw [← radialMellin b hb _ hs]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hp : ((r ^ d : ℝ) : ℂ) ^ s = (r : ℂ) ^ ((d : ℂ) * s) := by
    rw [Complex.ofReal_pow, Complex.cpow_nat_mul']
    · simp [Complex.arg_ofReal_of_nonneg (le_of_lt hr), Real.pi_pos]
    · simp [Complex.arg_ofReal_of_nonneg (le_of_lt hr), Real.pi_pos.le]
  dsimp only
  rw [hp, Complex.cpow_sub _ _ hr', Complex.cpow_add _ _ hr', Complex.cpow_natCast, Complex.cpow_one]
  simp [Complex.real_smul, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]

/-- The radial integral for a real Gaussian of parity weight `n` gives the real gamma factor. -/
theorem realMellin_gamma (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (2 : ℝ) • (∫ r in Ioi (0 : ℝ), r⁻¹ • ((r : ℂ) ^ n * (Real.exp (-(Real.pi * r ^ 2)) : ℂ) *
      ((r ^ 1 : ℝ) : ℂ) ^ s)) = Complex.Gammaℝ (s + n) := by
  rw [radialMellin_power _ Real.pi_pos]
  · simp [Complex.Gammaℝ, Complex.real_smul]
    left
    congr 1
    ring
  · simp only [Nat.cast_one, one_mul, Complex.add_re, Complex.natCast_re]
    positivity

/-- The radial integral with the doubled plane measure gives half the complex gamma factor. -/
theorem complexMellin_gamma (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (4 * Real.pi : ℝ) • (∫ r in Ioi (0 : ℝ), r⁻¹ •
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((r : ℂ) ^ n * (Real.exp (-(2 * Real.pi * r ^ 2)) : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ s))) =
      Complex.Gammaℂ (s + n / 2) / 2 := by
  have bpos : 0 < 2 * Real.pi := by positivity
  simp only [Complex.real_smul]
  have h : (fun r : ℝ ↦ (↑r⁻¹ : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((r : ℂ) ^ n *
      (Real.exp (-(2 * Real.pi * r ^ 2)) : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ s))) =
      (fun r : ℝ ↦ (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (r⁻¹ • ((r : ℂ) ^ n *
      (Real.exp (-(2 * Real.pi * r ^ 2)) : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ s)))) := by
    funext r
    simp [Complex.real_smul, mul_left_comm]
  rw [h, integral_const_mul, radialMellin_power _ bpos]
  · rw [show ((2 : ℕ) : ℂ) * s + n = 2 * (s + n / 2) by push_cast; ring]
    simp [Complex.Gammaℂ, Complex.ofReal_mul, field]
    ring_nf
    simp
  · simp [Complex.add_re, Complex.mul_re]
    positivity

/-- The Fourier transforms of the even and odd Gaussians for the real trace pairing. -/
theorem realGaussianFourier (n : Fin 2) (y : ℝ) :
    (∫ x : ℝ, (x : ℂ) ^ n.val * (Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℂ) *
      star (Circle.exp (2 * Real.pi * (x * y)) : ℂ)) =
    (-Complex.I) ^ n.val * ((y : ℂ) ^ n.val * (Real.exp (-(Real.pi * ‖y‖ ^ 2)) : ℂ)) := by
  let g (x : ℝ) : ℂ := Real.exp (-(Real.pi * x ^ 2))
  have hg : 𝓕 g = g := by
    have h := fourier_gaussian_pi (b := 1) (by norm_num)
    simpa [g, Complex.ofReal_exp] using h
  have hnorm (x : ℝ) : (Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℂ) = g x := by simp [g, Real.norm_eq_abs, sq_abs]
  have hformula (p : ℝ → ℂ) :
      (∫ x : ℝ, p x * star (Circle.exp (2 * Real.pi * (x * y)) : ℂ)) = 𝓕 p y := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext x
    simp [Circle.coe_exp, ← Complex.exp_conj, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, map_ofNat]
  simp_rw [hnorm, hformula]
  fin_cases n
  · simp [hg]
  · simp only [pow_one]
    have hgint : Integrable g := by simpa only [g, neg_mul] using! (integrable_exp_neg_mul_sq Real.pi_pos).ofReal
    have hxint : Integrable (fun x : ℝ ↦ x • g x) := by
      have h : Integrable (fun x : ℝ ↦ ((x ^ (1 : ℝ) * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ)) := (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := 1) (by norm_num)).ofReal
      simpa [g, neg_mul, Complex.real_smul] using h
    have hd (y : ℝ) : deriv g y = -2 * Real.pi * y * g y := by
      have d := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y
        ((((hasDerivAt_id y).pow 2).const_mul Real.pi).neg.exp))).deriv
      change deriv (Complex.ofRealCLM ∘ fun x : ℝ ↦ Real.exp (-(Real.pi * x ^ 2))) y = _
      convert! d using 1
      simp [g, mul_comm, mul_left_comm, mul_assoc]
    let k : ℂ := -2 * Real.pi * Complex.I
    have hk : k ≠ 0 := by dsimp [k]; exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have h := congrFun (Real.deriv_fourier hgint hxint) y
    rw [hg, hd] at h
    have hfn : (fun x : ℝ ↦ (-2 * Real.pi * Complex.I * x) • g x) =
        k • (fun x : ℝ ↦ (x : ℂ) * g x) := by
      funext x
      simp [k, smul_eq_mul, mul_assoc]
    have hFour (p : ℝ → ℂ) : 𝓕 (k • p) y = k * 𝓕 p y := by
      rw [← hformula, ← hformula]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    rw [hfn, hFour] at h
    apply mul_left_cancel₀ hk
    change k * 𝓕 (fun x : ℝ ↦ (x : ℂ) * g x) y = _
    rw [← h]
    dsimp [k]
    linear_combination -(2 * (Real.pi : ℂ) * y * g y) * Complex.I_sq

/-- The real Gaussian with its parity monomial.

This and `complexTest` are explicit test functions used inside proofs of §3.2, which cannot
import §3.4. They are not the formalization of an object of the paper: the paper's standard
Gaussians, Equations (3.4.3.3)–(3.4.3.6), p. 152, are `infiniteStandardGaussian` in
`Ch03_IdelicZeta/Sec4.lean`, and that definition is the one to compare with the print. -/
def realTest (n : Fin 2) (x : ℝ) : ℂ :=
  (x : ℂ) ^ n.val * (Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℂ)

/-- The normalized complex monomial of angular weight opposite to `m`. -/
def complexTestPoly (m : ℤ) (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (if 0 ≤ m then star z else z) ^ m.natAbs

/-- The complex Gaussian with its normalized angular monomial. A proof device, like `realTest`:
the paper's object is `infiniteStandardGaussian` in §3.4. -/
def complexTest (m : ℤ) (z : ℂ) : ℂ :=
  complexTestPoly m z * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ)

/-- The trace-pairing Fourier transform exchanges the Gaussian tests of opposite angular weights. -/
theorem complexGaussianFourier (m : ℤ) (y : ℂ) :
    (2 : ℝ) • (∫ x : ℂ, complexTest m x * star (Circle.exp (2 * Real.pi * (2 * (x * y).re)) : ℂ)) =
      (-Complex.I) ^ m.natAbs * complexTest (-m) y := by
  let b := 2 * Real.pi
  let e := decide (0 ≤ m)
  have h (x : ℂ) : complexTest m x * star (Circle.exp (2 * Real.pi * (2 * (x * y).re)) : ℂ) =
      (b : ℂ)⁻¹ * (angularCoord e x ^ m.natAbs * Complex.exp (-(b : ℂ) * (‖x‖:ℂ) ^ 2 - 2 * b * Complex.I * (x * y).re)) := by
    simp only [complexTest, complexTestPoly, b, e, angularCoord, decide_eq_true_eq, Circle.coe_exp,
      star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_pow, map_ofNat]
    rw [show -(2 * (Real.pi : ℂ)) * (‖x‖:ℂ) ^ 2 - 2 *(2 * (Real.pi : ℂ)) * Complex.I * (x * y).re =
      -(2 * (Real.pi : ℂ) * (‖x‖:ℂ) ^ 2) + (2 * (Real.pi : ℂ) * (2 * (x * y).re)* -Complex.I) by ring]
    rw [Complex.exp_add]
    ring
  rw [show (fun x ↦ complexTest m x * _) = _ from funext h, integral_const_mul,
    planeGaussianMoments b (by dsimp [b]; positivity)]
  have hc : angularCoord (!e) y ^ m.natAbs =
      (if 0 ≤ -m then star y else y) ^ (-m).natAbs := by
    rcases lt_trichotomy m 0 with hm | hm | hm
    · simp [angularCoord, e, not_le.mpr hm, hm.le]
    · subst m; simp
    · simp [angularCoord, e, hm.le, not_le.mpr hm]
  rw [mul_pow, hc]
  simp only [complexTest, complexTestPoly, b, Int.natAbs_neg, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [neg_mul]
  field_simp

end RiemannMasullo.HeckeGaussian
