module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The first Riesz mean of the Hecke logarithmic derivative

The Mellin transform of the finite ideal sum weighted by the ramp `max (x - N I) 0`
recovers the negative logarithmic derivative with denominator `s * (s + 1)`.
This is the arithmetic transform for the one-sided comparison for Theorem 12.5.1.1,
pp. 519–520, with the Hecke Euler series of equation (B.6.1.12), p. 638.
-/

@[expose] public noncomputable section

open Set MeasureTheory NumberField

namespace RiemannMasullo

local notation "K(" q ", " s ", " x ")" =>
  Complex.ofReal (max ((x : ℝ) - (q : ℝ)) 0) * (x : ℂ) ^ (-(s : ℂ) - 2)

private theorem riesz_kernel_indicator {q : ℝ} (hq : 0 < q) (s : ℂ) (x : ℝ) :
    K(q, s, x) = (Ioi q).indicator
      (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) - (q : ℂ) * (t : ℂ) ^ (-s - 2)) x := by
  by_cases h : q < x
  · rw [indicator_of_mem (show x ∈ Ioi q from h), max_eq_left (sub_nonneg.mpr h.le), Complex.ofReal_sub,
      sub_mul, show -s - 1 = 1 + (-s - 2) by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hq.trans h).ne'), Complex.cpow_one]
  · rw [indicator_of_notMem (show x ∉ Ioi q from h),
      max_eq_right (sub_nonpos.mpr (le_of_not_gt h)), Complex.ofReal_zero, zero_mul]

private theorem riesz_kernel_integrable {q : ℝ} (hq : 1 ≤ q) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ K(q, s, x)) (Ioi 1) := by
  simp_rw [riesz_kernel_indicator (zero_lt_one.trans_le hq)]
  have h₁ : (-s - 1).re < -1 := by simp; linarith
  have h₂ : (-s - 2).re < -1 := by simp; linarith
  exact ((integrableOn_Ioi_cpow_of_lt h₁ zero_lt_one).sub
    ((integrableOn_Ioi_cpow_of_lt h₂ zero_lt_one).const_mul (q : ℂ))).indicator measurableSet_Ioi

private theorem riesz_kernel_integral {q : ℝ} (hq : 1 ≤ q) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), K(q, s, x)) = (q : ℂ) ^ (-s) / (s * (s + 1)) := by
  have hq₀ := zero_lt_one.trans_le hq
  have hqℂ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have h₁ : (-s - 1).re < -1 := by simp; linarith
  have h₂ : (-s - 2).re < -1 := by simp; linarith
  have hs₀ : s ≠ 0 := fun e ↦ (ne_of_gt hs) (congrArg Complex.re e)
  have hs₁ : s + 1 ≠ 0 := by
    intro e
    have hh := congrArg Complex.re e
    simp at hh
    linarith
  simp_rw [riesz_kernel_indicator hq₀]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hq,
    integral_sub (integrableOn_Ioi_cpow_of_lt h₁ hq₀)
      ((integrableOn_Ioi_cpow_of_lt h₂ hq₀).const_mul _), integral_const_mul,
    integral_Ioi_cpow_of_lt h₁ hq₀, integral_Ioi_cpow_of_lt h₂ hq₀,
    show -s - 1 + 1 = -s by ring, show -s - 2 + 1 = -s - 1 by ring,
    Complex.cpow_sub _ _ hqℂ, Complex.cpow_one, show -s - 1 = -(s + 1) by ring]
  simp only [div_neg, neg_div, neg_neg]
  field_simp
  ring

private theorem riesz_kernel_norm_integral_le {q : ℝ} (hq : 1 ≤ q) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ‖K(q, s, x)‖) ≤ (q ^ s.re)⁻¹ / s.re := by
  have hq₀ := zero_lt_one.trans_le hq
  have hd : -s.re - 1 < -1 := by linarith
  let f := (Ioi q).indicator (fun x : ℝ ↦ x ^ (-s.re - 1))
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ), f x := by
      apply setIntegral_mono_on (riesz_kernel_integrable hq hs).norm
        ((integrableOn_Ioi_rpow_of_lt hd zero_lt_one).indicator measurableSet_Ioi) measurableSet_Ioi
      intro x hx
      by_cases h : q < x
      · have hx₀ := hq₀.trans h
        rw [indicator_of_mem (show x ∈ Ioi q from h),
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _),
          max_eq_left (sub_nonneg.mpr h.le), Complex.norm_cpow_eq_rpow_re_of_pos hx₀]
        have he : (-s - 2).re = -s.re - 2 := by simp
        rw [he, show -s.re - 1 = 1 + (-s.re - 2) by ring, Real.rpow_add hx₀, Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx₀.le _)
      · simp [indicator_of_notMem (show x ∉ Ioi q from h), max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]
    _ = _ := by
      dsimp only [f]
      rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hq,
        integral_Ioi_rpow_of_lt hd hq₀, show -s.re - 1 + 1 = -s.re by ring,
        Real.rpow_neg hq₀.le, neg_div_neg_eq]

/-- Mellin transform of a first Riesz mean on a locally finite family of real norms.
Absolute convergence of the Dirichlet series at `s` justifies summing the ramp integrals. -/
theorem mellin_firstRieszMean {ι : Type*} (q : ι → ℝ) (a : ι → ℂ)
    (hq : ∀ i, 1 ≤ q i) (hfin : ∀ x : ℝ, {i | q i ≤ x}.Finite) {s : ℂ} (hs : 0 < s.re)
    {A : ℂ} (hA : HasSum (fun i ↦ a i / (q i : ℂ) ^ s) A) :
    (∫ x in Ioi (1 : ℝ), (∑ᶠ i, a i * (max (x - q i) 0 : ℝ)) *
      (x : ℂ) ^ (-s - 2)) = A / (s * (s + 1)) := by
  classical
  let _ : Countable ι := by
    apply countable_univ_iff.mp
    apply (countable_iUnion (fun n : ℕ ↦ (hfin n).countable)).mono
    exact fun i _ ↦ mem_iUnion.mpr ⟨⌈q i⌉₊, (show q i ≤ (⌈q i⌉₊ : ℝ) from Nat.le_ceil (q i))⟩
  let f (i : ι) (x : ℝ) := a i * K(q i, s, x)
  have hi (i : ι) : IntegrableOn (f i) (Ioi 1) := (riesz_kernel_integrable (hq i) hs).const_mul _
  have hn : Summable (fun i ↦ ∫ x in Ioi (1 : ℝ), ‖f i x‖) := by
    apply (hA.summable.norm.div_const s.re).of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    intro i
    have hnrm (x : ℝ) : ‖f i x‖ = ‖a i‖ * ‖K(q i, s, x)‖ := norm_mul ..
    simp_rw [hnrm]
    rw [integral_const_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (hq i))]
    calc
      _ ≤ ‖a i‖ * ((q i ^ s.re)⁻¹ / s.re) :=
        mul_le_mul_of_nonneg_left (riesz_kernel_norm_integral_le (hq i) hs) (norm_nonneg (a i))
      _ = _ := by ring
  have he (x : ℝ) : (∑' i, f i x) = (∑ᶠ i, a i * (max (x - q i) 0 : ℝ)) * (x : ℂ) ^ (-s - 2) := by
    let g (i : ι) : ℂ := a i * (max (x - q i) 0 : ℝ)
    have hgf : (Function.support g).Finite := (hfin x).subset fun i hi ↦ by
      change q i ≤ x
      by_contra! h
      apply hi
      simp [g, max_eq_right (sub_nonpos.mpr h.le)]
    calc
      _ = ∑' i, g i * (x : ℂ) ^ (-s - 2) := tsum_congr fun i ↦ by dsimp [f, g]; ring
      _ = _ := by rw [tsum_mul_right, tsum_eq_finsum hgf]
  have he' (i : ι) : (∫ x in Ioi (1 : ℝ), f i x) = (a i / (q i : ℂ) ^ s) / (s * (s + 1)) := by
    dsimp only [f]
    rw [integral_const_mul, riesz_kernel_integral (hq i) hs, Complex.cpow_neg]
    ring
  simpa only [he] using ((hasSum_integral_of_summable_integral_norm hi hn).congr_fun
    (fun i ↦ (he' i).symm)).unique (hA.div_const _)

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "I₀" => {I : Ideal (𝓞 F) // I ≠ ⊥}
local notation "Λ(" χ ", " I ")" => heckeIdealVonMangoldt (ideleClassNormTwist χ 0) (Subtype.val (I : I₀))

/-- The first Riesz mean of the finite Hecke logarithmic derivative, summed over ideals
with absolute norm below the real cutoff. -/
def heckeFirstRieszMean (χ : U) (x : ℝ) : ℂ :=
  ∑ᶠ I : I₀, Λ(χ, I) * (max (x - (I.val.absNorm : ℝ)) 0 : ℝ)

private theorem heckeFirstRieszMean_finite (x : ℝ) :
    {I : I₀ | (I.val.absNorm : ℝ) ≤ x}.Finite := by
  apply ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌈x⌉₊).preimage
    (Subtype.val_injective (p := fun I : Ideal (𝓞 F) ↦ I ≠ ⊥)).injOn).subset
  intro I hI
  change I.val.absNorm ≤ ⌈x⌉₊
  exact_mod_cast (show (I.val.absNorm : ℝ) ≤ x from hI).trans (Nat.le_ceil x)

/-- The Mellin transform of the actual finite Hecke Riesz mean on the Euler half-plane.
The same continuation and Euler-series hypotheses are used in Appendix B.6. -/
theorem heckeFirstRieszMean_mellin (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), heckeFirstRieszMean χ x * (x : ℂ) ^ (-s - 2)) =
      -logDeriv L s / (s * (s + 1)) := by
  have hq (I : I₀) : (1 : ℝ) ≤ I.val.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  apply mellin_firstRieszMean (fun I : I₀ ↦ (I.val.absNorm : ℝ)) (fun I ↦ Λ(χ, I)) hq
    (heckeFirstRieszMean_finite (F := F)) (zero_lt_one.trans hs)
  simpa only [Complex.ofReal_natCast, neg_div, neg_neg] using
    (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨s, hs⟩).2.2.neg

private theorem riesz_ramp_interp (n m : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    max ((n : ℝ) + t - m) 0 =
      (1 - t) * max ((n : ℝ) - m) 0 + t * max ((n : ℝ) + 1 - m) 0 := by
  by_cases h : m ≤ n
  · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [max_eq_left (by linarith [ht.1]), max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge h)
    rw [max_eq_right (by linarith [ht.2]), max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

/-- Between consecutive integers the first Hecke Riesz mean is exactly affine. This
allows the continuous statistic to be recovered from the integer cutoffs. -/
theorem heckeFirstRieszMean_interp (χ : U) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    heckeFirstRieszMean χ ((n : ℝ) + t) =
      (1 - (t : ℂ)) * heckeFirstRieszMean χ n + t * heckeFirstRieszMean χ (n + 1 : ℕ) := by
  classical
  let S := (heckeFirstRieszMean_finite (F := F) ((n : ℝ) + 1)).toFinset
  have hcut (x : ℝ) (hx : x ≤ n + 1) :
      heckeFirstRieszMean χ x = ∑ I ∈ S, Λ(χ, I) * (max (x - I.val.absNorm) 0 : ℝ) := by
    unfold heckeFirstRieszMean
    apply finsum_eq_sum_of_support_subset
    intro I hI
    apply (Set.Finite.mem_toFinset _).mpr
    change (I.val.absNorm : ℝ) ≤ n + 1
    by_contra! h
    exact hI (by simp [max_eq_right (sub_nonpos.mpr (hx.trans h.le))])
  rw [hcut _ (by linarith [ht.2]), hcut _ (by linarith), hcut _ (by norm_num),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  rw [riesz_ramp_interp _ _ ht]
  push_cast
  ring

/-- After subtracting a real quadratic main term, the interpolation correction is
exactly `c * t * (1-t) / 2`. It is nonnegative for the trivial-character main term. -/
theorem heckeFirstRieszMean_centered_interp (χ : U) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) (c : ℝ) :
    (heckeFirstRieszMean χ ((n : ℝ) + t)).re - c * ((n : ℝ) + t) ^ 2 / 2 =
      (1 - t) * ((heckeFirstRieszMean χ n).re - c * (n : ℝ) ^ 2 / 2) +
      t * ((heckeFirstRieszMean χ (n + 1 : ℕ)).re - c * ((n : ℝ) + 1) ^ 2 / 2) +
      c * t * (1 - t) / 2 := by
  rw [heckeFirstRieszMean_interp χ n ht]
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul]
  ring

/-- Group the ideal Riesz mean by its rational integer norm. -/
theorem heckeFirstRieszMean_eq_norm_sum (χ : U) {x : ℝ} (hx : 0 ≤ x) :
    heckeFirstRieszMean χ x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n * (x - n : ℝ) := by
  classical
  let T := (heckeFirstRieszMean_finite (F := F) x).toFinset
  have hT (I : I₀) : I ∈ T ↔ (I.val.absNorm : ℝ) ≤ x := Set.Finite.mem_toFinset _
  let f (I : I₀) := Λ(χ, I) * (x - I.val.absNorm : ℝ)
  have hbase : heckeFirstRieszMean χ x = ∑ I ∈ T, f I := by
    unfold heckeFirstRieszMean
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · exact Finset.sum_congr rfl fun I hi ↦ by simp [f, max_eq_left (sub_nonneg.mpr ((hT I).mp hi))]
    · intro I hi
      apply (hT I).mpr
      by_contra! h
      exact hi (by simp [max_eq_right (sub_nonpos.mpr h.le)])
  rw [hbase, ← Finset.sum_fiberwise_of_maps_to (t := Finset.Ioc 0 ⌊x⌋₊)
    (g := fun I : I₀ ↦ I.val.absNorm) (fun I hi ↦ Finset.mem_Ioc.mpr
      ⟨Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property), Nat.le_floor ((hT I).mp hi)⟩) f]
  apply Finset.sum_congr rfl
  intro n hn
  let V := T.filter (fun I : I₀ ↦ I.val.absNorm = n)
  let A := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}
  let e : (V : Type _) ≃ A :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property, (Finset.mem_filter.mp I.property).2⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, Finset.mem_filter.mpr
        ⟨(hT _).mpr (by change (I.val.absNorm : ℝ) ≤ x; rw [I.property.2]; exact
          (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2), I.property.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  change (∑ I ∈ V, f I) = (∑ᶠ I : A, heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val) * _
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Finset.sum_mul, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I _
  dsimp [f, e]
  rw [(Finset.mem_filter.mp I.property).2]

/-- Keeping only the rational-prime norms in the first Riesz mean costs at most a universal
constant times the degree and `x * sqrt x`. -/
theorem heckeFirstRieszMean_sub_prime_le :
    ∃ C : ℝ, ∀ (F : Type*) [Field F] [NumberField F]
      (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {x : ℝ}, 0 ≤ x →
      ‖heckeFirstRieszMean χ x - ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime,
        heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p * (x - p : ℝ)‖ ≤
        Module.finrank ℚ F * x * (C * Real.sqrt x) := by
  obtain ⟨C, hC⟩ := heckeLogDerivCoefficient_sum_sub_sum_prime_le_mul_sqrt
  refine ⟨C, fun F _ _ χ x hx ↦ ?_⟩
  let b (n : ℕ) : ℂ := (max (x - n) 0 : ℝ)
  have hb (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) : b n = (x - n : ℝ) := by
    exact congrArg Complex.ofReal (max_eq_left (sub_nonneg.mpr ((Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2)))
  have hb' (n : ℕ) : ‖b n‖ ≤ x := by
    rw [show ‖b n‖ = |max (x - n) 0| from Complex.norm_real _, abs_of_nonneg (le_max_right ..)]
    exact max_le (sub_le_self _ (Nat.cast_nonneg n)) hx
  rw [heckeFirstRieszMean_eq_norm_sum χ hx]
  convert hC F χ x b x hb' using 2
  congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn
  all_goals first | rw [hb n hn] | rw [hb n (Finset.mem_filter.mp hn).1]

/-- The discrete derivative of the Riesz mean is exactly the unsmoothed Hecke sum.
A rational-norm atom at `n` is included in this forward difference. -/
theorem heckeFirstRieszMean_forward_sub (χ : U) (n : ℕ) :
    heckeFirstRieszMean χ (n + 1 : ℕ) - heckeFirstRieszMean χ n =
      ∑ k ∈ Finset.Ioc 0 n, heckeLogDerivCoefficient (ideleClassNormTwist χ 0) k := by
  rw [heckeFirstRieszMean_eq_norm_sum _ (Nat.cast_nonneg _), heckeFirstRieszMean_eq_norm_sum _ (Nat.cast_nonneg _)]
  simp only [Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  simp only [Nat.cast_add, Nat.cast_one,
    sub_self, Complex.ofReal_zero, mul_zero, add_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private theorem heckeFirstRieszMean_re_eq (χ : U) (x : ℝ) :
    ((heckeFirstRieszMean χ x).re : ℂ) =
      ∑ᶠ I : I₀, ((Λ(χ, I)).re : ℂ) * (max (x - I.val.absNorm) 0 : ℝ) := by
  classical
  let S := (heckeFirstRieszMean_finite (F := F) x).toFinset
  have hm (I : I₀) (hi : I ∉ S) : max (x - (I.val.absNorm : ℝ)) 0 = 0 := by
    apply max_eq_right
    exact sub_nonpos.mpr (le_of_not_ge (fun h ↦ hi ((Set.Finite.mem_toFinset _).mpr h)))
  have he (f : I₀ → ℂ) : (∑ᶠ I : I₀, f I * (max (x - I.val.absNorm) 0 : ℝ)) =
      ∑ I ∈ S, f I * (max (x - I.val.absNorm) 0 : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro I hi
    by_contra hn
    exact hi (by simp [hm I hn])
  rw [heckeFirstRieszMean, he, he, Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro I _
  simp [Complex.mul_re]

/-- The readout from a single real arithmetic inequality averages the logarithmic derivative
at `s` with the conjugate of its value at the reflected argument. Thus coincident zero
residues in the two terms have the same sign. -/
theorem heckeFirstRieszMean_re_mellin (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2)) =
      ((-logDeriv L s - star (logDeriv L (star s))) / 2) / (s * (s + 1)) := by
  have hq (I : I₀) : (1 : ℝ) ≤ I.val.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  have hsum (w : ℂ) (hw : 1 < w.re) : HasSum (fun I : I₀ ↦ Λ(χ, I) / (I.val.absNorm : ℂ) ^ w)
      (-logDeriv L w) := by
    simpa only [neg_div, neg_neg] using (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨w, hw⟩).2.2.neg
  simp_rw [heckeFirstRieszMean_re_eq]
  apply mellin_firstRieszMean (fun I : I₀ ↦ (I.val.absNorm : ℝ)) (fun I ↦ ((Λ(χ, I)).re : ℂ)) hq
    (heckeFirstRieszMean_finite (F := F)) (zero_lt_one.trans hs)
  have h := ((hsum s hs).add (Complex.hasSum_conj'.mpr (hsum (star s) hs))).div_const 2
  rw [map_neg] at h
  apply h.congr_fun
  intro I
  have harg : (I.val.absNorm : ℂ).arg ≠ Real.pi := by
    simpa only [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)] using
      Real.pi_pos.ne
  have hv := Complex.conj_cpow (I.val.absNorm : ℂ) s harg
  simp only [map_natCast] at hv
  have hv' : (starRingEnd ℂ) ((I.val.absNorm : ℂ) ^ star s) = (I.val.absNorm : ℂ) ^ s := hv.symm
  simp only [Complex.ofReal_natCast, map_div₀, hv']
  rw [← add_div, show Λ(χ, I) + (starRingEnd ℂ) (Λ(χ, I)) = 2 * ((Λ(χ, I)).re : ℂ) from
    RCLike.add_conj _]
  ring

end RiemannMasullo
