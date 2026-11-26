module

public import RiemannMasullo.ForMathlib.Analysis.Complex.StripReciprocal
public import RiemannMasullo.ForMathlib.Analysis.Complex.BlaschkeFactorization
public import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma
import Mathlib.Tactic

/-! # A lower modulus bound on a compact disk away from its zero ordinates -/

@[expose] public noncomputable section

open Complex Metric Set Function Filter Topology
open scoped ComplexConjugate BigOperators
namespace RiemannMasullo.DiskSmallValues
open Blaschke

/-- The divisor sites of the analytic function inside the open unit disk. -/
abbrev Root (f : ℂ → ℂ) := {a : ℂ // a ∈ ball 0 1 ∧ f a = 0}

private theorem finite_root {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hc : f 0 ≠ 0) :
    Finite (Root f) := by
  have hs := finite_zeros_closedBall zero_le_one (hf.mono (closedBall_subset_closedBall hR.le)) hc
  have hS : {a : ℂ | a ∈ ball 0 1 ∧ f a = 0}.Finite := hs.subset (fun a ha ↦ ⟨ball_subset_closedBall ha.1, ha.2⟩)
  exact hS.to_subtype

private theorem normalizedFactor_norm {a z : ℂ} (ha : a ≠ 0) :
    ‖normalizedFactor a z‖ = ‖z - a‖ / ‖1 - conj a * z‖ := by
  let u := conj a / (‖a‖ : ℂ)
  have hU : ‖u‖ = 1 := by simp [u, norm_ne_zero_iff.mpr ha]
  have hn : (‖a‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hua : u * a = (‖a‖ : ℂ) := by
    dsimp [u]
    rw [div_mul_eq_mul_div, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, ofReal_pow]
    field_simp
  have hau : (‖a‖ : ℂ) * u = conj a := by dsimp [u]; field_simp
  rw [normalizedFactor_apply, norm_div]
  change ‖(‖a‖ : ℂ) - u * z‖ / ‖1 - (‖a‖ : ℂ) * (u * z)‖ = _
  rw [← mul_assoc, hau, ← hua, ← mul_sub, norm_mul, hU, one_mul, norm_sub_rev]

private theorem factor_lower {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖z-a‖ / 2 ≤ ‖normalizedFactor a z‖ := by
  have hp : ‖conj a * z‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha'.le) (norm_nonneg z)]
  have hc : 1-conj a*z ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [← h] at hp)
  have hd : ‖1-conj a*z‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1+‖conj a*z‖≤2 by linarith))
  rw [normalizedFactor_norm ha]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (norm_pos_iff.mpr hc) hd

private theorem factor_zero {a : ℂ} (ha : a ≠ 0) : ‖normalizedFactor a 0‖ = ‖a‖ := by
  rw [normalizedFactor_norm ha]
  simp

/-- Jensen bounds the total multiplicity in the unit disk from one larger disk. -/
theorem rootOrderSum_le {f : ℂ → ℂ} {R B : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hc : f 0 ≠ 0)
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z / f 0‖ ≤ B) [Fintype (Root f)] :
    (∑ a : Root f, (analyticOrderNatAt f a.val : ℝ)) ≤ Real.log B / Real.log R := by
  classical
  let g (a : ℂ) : ℝ := analyticOrderNatAt f a
  have hfin := finite_zeros_closedBall zero_le_one (hf.mono (closedBall_subset_closedBall hR.le)) hc
  let T := hfin.toFinset
  have heq : (∑ᶠ a ∈ closedBall (0:ℂ) 1, g a) = ∑ a ∈ T, g a := by
    rw [← finsum_mem_coe_finset]
    apply finsum_mem_inter_support_eq'
    intro a hne
    have hzero : f a = 0 := by
      by_contra hh
      simp [g, analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hh)] at hne
    simp [T, hzero]
  have hbound := landau_sum_analyticOrderNatAt_le zero_lt_one hR hf hc hb
  rw [div_one, ← show (∑ᶠ a ∈ closedBall (0:ℂ) 1, g a) = _ from rfl, heq] at hbound
  refine le_trans ?_ hbound
  apply Finset.sum_le_sum_of_injOn (fun a : Root f ↦ a.val)
  · exact Subtype.val_injective.injOn
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    simpa [T] using (show a.val ∈ closedBall (0:ℂ) 1 ∧ f a.val = 0 from
      ⟨ball_subset_closedBall a.property.1, a.property.2⟩)
  · exact fun _ _ ↦ le_rfl
  · exact fun _ _ _ ↦ Nat.cast_nonneg _


/-- At any nonzero value on a smaller disk, the lower modulus is controlled by
the product of the distances to the true unit-disk zeros. The count includes multiplicities. -/
theorem log_lower_of_separated {f : ℂ → ℂ} {R M r d : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hc : f 0 ≠ 0)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hr : r < 1) (hd : 0 < d) {z : ℂ} (hz : ‖z‖ ≤ r)
    (hsep : ∀ a : Root f, d ≤ ‖z-a.val‖) [Fintype (Root f)] :
    Real.log M - 4/(1-r) * (Real.log M - Real.log ‖f 0‖) +
      (∑ a : Root f, (analyticOrderNatAt f a.val : ℝ)) * Real.log (d/2) ≤ Real.log ‖f z‖ := by
  classical
  let m (a : Root f) := analyticOrderNatAt f a.val
  have hAO := hf.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hR.le))
  obtain ⟨Q,hQ,hqn,hQb,hF⟩ := exists_canonical_disk_factorization f hAO hc M hb
  have hA (a : Root f) : a.val ≠ 0 := by
    intro he
    exact hc ((congrArg f he.symm).trans a.property.2)
  have hA' (a : Root f) : ‖a.val‖ < 1 := mem_ball_zero_iff.mp a.property.1
  have hz' : ‖z‖ < 1 := hz.trans_lt hr
  have hprod (w : ℂ) (hw : ‖w‖<1) : (∏ a : Root f, ‖normalizedFactor a.val w‖^m a) * ‖Q w‖ = ‖f w‖ := by
    have h := congrArg norm (hF w (mem_ball_zero_iff.mpr hw))
    simpa [zeroProduct, product, m, norm_mul] using h
  have h0 : ‖f 0‖ ≤ ‖Q 0‖ := by
    rw [← hprod 0 (by simp)]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply Finset.prod_le_one₀ (fun _ _ ↦ by positivity)
    intro a _
    rw [factor_zero (hA a)]
    exact pow_le_one₀ (norm_nonneg _) (hA' a).le
  have hlog0 := Real.log_le_log (norm_pos_iff.mpr hc) h0
  have hH := disk_log_norm_deficit_le Q M hQ hqn hQb hz'
  have H0 : 0 ≤ Real.log M - Real.log ‖Q 0‖ :=
    sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr (hqn 0 (by simp))) (hQb _ (by simp)))
  have hC : 4/(1-‖z‖) ≤ 4/(1-r) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hL : Real.log M - 4/(1-r)*(Real.log M-Real.log ‖f 0‖) ≤ Real.log ‖Q z‖ := by
    have h := hH.trans ((mul_le_mul_of_nonneg_right hC H0).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hlog0 _) (by positivity)))
    linarith
  have hpol : (∏ a : Root f, (d/2)^m a) ≤ ∏ a : Root f, ‖normalizedFactor a.val z‖^m a := by
    apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
    exact fun a _ ↦ pow_le_pow_left₀ (by positivity)
      (((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr (hsep a)).trans
        (factor_lower (hA a) (hA' a) hz')) _
  have hpow : (d/2)^(∑ a : Root f,m a) * ‖Q z‖ ≤ ‖f z‖ := by
    rw [← hprod z hz', ← Finset.prod_pow_eq_pow_sum]
    exact mul_le_mul_of_nonneg_right hpol (norm_nonneg _)
  have hzp := norm_pos_iff.mpr (hqn z (mem_ball_zero_iff.mpr hz'))
  have hlog := Real.log_le_log (mul_pos (pow_pos (by positivity) _) hzp) hpow
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  push_cast at hlog
  linarith

open MeasureTheory

/-- A lower-tail event on any vertical disk chord is covered by short intervals
about its actual zero ordinates. Here the real logarithm is totalized at zero. -/
theorem vertical_small_value_measure {f : ℂ → ℂ} {R M r L Y : ℝ}
    (hR : 1 < R) (hM : 1 ≤ M) (hr : r < 1) (hL : 0 < L) (hY : 0 ≤ Y)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hc : f 0 ≠ 0)
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ M)
    (hJL : Real.log (M / ‖f 0‖) / Real.log R ≤ L) (x : ℝ) :
    volume {t : ℝ | ‖(x:ℂ) + (t:ℂ)*I‖ ≤ r ∧
      Real.log ‖f ((x:ℂ) + (t:ℂ)*I)‖ < - (4/(1-r))*Real.log (M/‖f 0‖) - Y}
    ≤ ENNReal.ofReal (4 * L * Real.exp (-Y/L)) := by
  classical
  let := finite_root hR hf hc
  let := Fintype.ofFinite (Root f)
  let d := 2 * Real.exp (-Y/L)
  have hd : 0 < d := by positivity
  let v (t : ℝ) : ℂ := x+(t:ℂ)*I
  let E (a : Root f) := Ioo (a.val.im-d) (a.val.im+d)
  have hball (u : ℂ) (hu : u ∈ ball (0:ℂ) 1) : ‖f u‖ ≤ M :=
    hb u (closedBall_subset_closedBall hR.le (ball_subset_closedBall hu))
  have horder := rootOrderSum_le hR hf hc (B:=M/‖f 0‖) (by
    intro u hu
    rw [norm_div]
    exact div_le_div_of_nonneg_right (hb _ hu) (norm_nonneg _))
  have hcpos := norm_pos_iff.mpr hc
  have hlog := Real.log_nonneg hM
  have hMd : M ≠ 0 := by linarith
  have hlogR : Real.log (M/‖f 0‖) = Real.log M - Real.log ‖f 0‖ :=
    Real.log_div hMd hcpos.ne'
  have hsub : {t : ℝ | ‖v t‖≤r ∧ Real.log ‖f (v t)‖ <
      -(4/(1-r))*Real.log (M/‖f 0‖) - Y} ⊆ ⋃ a : Root f, E a := by
    intro t ht
    rcases ht with ⟨ht, hsmall⟩
    by_contra hn
    have hsep (a : Root f) : d ≤ ‖v t-a.val‖ := by
      have hna : t ∉ E a := fun he ↦ hn (mem_iUnion.mpr ⟨a,he⟩)
      have hdist : d ≤ |t-a.val.im| := by
        by_contra! h
        exact hna (by dsimp [E]; exact ⟨by linarith [(abs_lt.mp h).1],by linarith [(abs_lt.mp h).2]⟩)
      exact hdist.trans (by simpa [v] using Complex.abs_im_le_norm (v t-a.val))
    have hlow := log_lower_of_separated hR hf hc hball hr hd ht hsep
    have hv : Real.log (d/2) = -Y/L := by
      rw [show d/2 = Real.exp (-Y/L) by dsimp [d]; ring, Real.log_exp]
    have hnY : -Y/L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le
    have hs := mul_le_mul_of_nonpos_right (horder.trans hJL) hnY
    rw [hv] at hlow
    rw [hlogR] at hsmall
    have hcancel : L*(-Y/L) = -Y := by field_simp
    linarith
  have hcard : (Fintype.card (Root f) : ℝ) ≤ L := by
    have hAO := hf.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hR.le))
    have hm := (disk_zero_orders_and_summability hAO hc hball).1
    calc (Fintype.card (Root f) : ℝ) = ∑ _a : Root f, (1:ℝ) := by simp
         _ ≤ _ := Finset.sum_le_sum (fun a _ ↦ (show (1:ℝ) ≤ analyticOrderNatAt f a.val by
           exact_mod_cast (hm a).1))
         _ ≤ L := horder.trans hJL
  have hmE (a : Root f) : volume (E a) = ENNReal.ofReal (2*d) := by
    dsimp only [E]
    rw [Real.volume_Ioo]
    congr 1
    ring
  calc
    _ ≤ volume (⋃ a : Root f, E a) := measure_mono hsub
    _ ≤ ∑ a : Root f, volume (E a) := measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal ((Fintype.card (Root f):ℝ)*(2*d)) := by
      simp [hmE, ENNReal.ofReal_mul]
    _ ≤ ENNReal.ofReal (4*L*Real.exp (-Y/L)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right hcard (show 0≤2*d by positivity)
      dsimp [d] at hh
      linarith

end RiemannMasullo.DiskSmallValues

open Complex MeasureTheory Metric Set Filter Topology

namespace RiemannMasullo.DiskSmallValues

/-- Lebesgue volume changes by the positive spatial scale under this translation and dilation. -/
theorem volume_scaled_preimage (E : Set ℝ) (T a : ℝ) (ha : 0<a) :
    volume ((fun t : ℝ ↦ (t-T)/a) ⁻¹' E) = ENNReal.ofReal a * volume E := by
  have he : ((fun t : ℝ ↦ (t-T)/a) ⁻¹' E) =
      ((fun t : ℝ ↦ t + (-T)) ⁻¹' ((fun u : ℝ ↦ u * a⁻¹) ⁻¹' E)) := by
    ext t
    simp only [mem_preimage, div_eq_mul_inv, sub_eq_add_neg]
  rw [he, measure_preimage_add_right, Real.volume_preimage_mul_right (inv_ne_zero ha.ne'), inv_inv,
    abs_of_pos ha]

/-- A complete unit interval on the critical line lies inside the smaller comparison disk
when the Euler centre is 2 and the affine disk has radius 9/5. -/
theorem chart_norm_le {t T : ℝ} (ht : |t-T|≤1/2) :
    ‖(-5/6:ℂ) + (((t-T)/(9/5) : ℝ) : ℂ)*I‖ ≤ 9/10 := by
  have ht' : |(t-T)/(9/5)|≤5/18 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<9/5),div_le_iff₀ (by norm_num)]
    linarith
  have hs : ((t-T)/(9/5))^2 ≤ (5/18:ℝ)^2 := by
    rw [← sq_abs ((t-T)/(9/5))]
    exact pow_le_pow_left₀ (abs_nonneg _) ht' 2
  let z := (-5/6:ℂ) + (((t-T)/(9/5) : ℝ) : ℂ)*I
  have hsq : ‖z‖^2 = (-5/6:ℝ)^2 + ((t-T)/(9/5))^2 := by
    dsimp only [z]
    generalize (t-T)/(9/5:ℝ) = u
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    norm_num [Complex.mul_re,Complex.mul_im]
    ring
  change ‖z‖ ≤ 9/10
  nlinarith [norm_nonneg z]

/-- A common logarithmic upper and a lower bound at one Euler centre give an absolute-log
exceptional set with exponentially small Lebesgue measure on the actual unit height window. -/
theorem window_log_tail {f : ℂ → ℂ} {M L Y T : ℝ} (hM : 1≤M) (hL : 0<L) (hY : 0≤Y)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (19/18))) (hc : f 0≠0)
    (hb : ∀ z ∈ closedBall (0:ℂ) (19/18), ‖f z‖≤M)
    (hupper : Real.log M ≤ 40*L)
    (hratio : Real.log (M/‖f 0‖) ≤ L)
    (hcount : Real.log (M/‖f 0‖)/Real.log (19/18) ≤ L) :
    volume {t : ℝ | |t-T|≤1/2 ∧ 40*L+Y <
      |Real.log ‖f ((-5/6:ℂ)+(((t-T)/(9/5):ℝ):ℂ)*I)‖|}
    ≤ ENNReal.ofReal (8 * L * Real.exp (-Y/L)) := by
  let x := (-5/6:ℝ)
  let z (u : ℝ) : ℂ := x + (u:ℂ)*I
  let E := {u : ℝ | ‖z u‖ ≤ 9/10 ∧ Real.log ‖f (z u)‖ <
        -(4/(1-9/10))*Real.log (M/‖f 0‖)-Y}
  have hE : volume E ≤ ENNReal.ofReal (4 * L * Real.exp (-Y/L)) := by
    exact vertical_small_value_measure (by norm_num) hM (by norm_num) hL hY hf hc hb hcount x
  have htrans := volume_scaled_preimage E T (9/5) (by norm_num)
  have hz (t : ℝ) : z ((t-T)/(9/5)) = (-5/6:ℂ)+(((t-T)/(9/5):ℝ):ℂ)*I := by
    simp [z,x]
  have hsub : {t : ℝ | |t-T|≤1/2 ∧ 40*L+Y < |Real.log ‖f (z ((t-T)/(9/5)))‖|} ⊆
      (fun t : ℝ ↦ (t-T)/(9/5)) ⁻¹' E := by
    intro t ht
    rcases ht with ⟨hwin,habs⟩
    have hzball : ‖z ((t-T)/(9/5))‖ ≤ 9/10 := by rw [hz]; exact chart_norm_le hwin
    refine ⟨hzball,?_⟩
    have hM0 := Real.log_nonneg hM
    have hu : Real.log ‖f (z ((t-T)/(9/5)))‖ ≤ Real.log M := by
      by_cases hh : f (z ((t-T)/(9/5))) = 0
      · simpa [hh] using hM0
      · exact Real.log_le_log (norm_pos_iff.mpr hh) (hb _ (mem_closedBall_zero_iff.mpr (by linarith)))
    have hlow : Real.log ‖f (z ((t-T)/(9/5)))‖ < -(40*L+Y) := by
      rcases lt_abs.mp habs with h | h <;> linarith
    norm_num
    linarith
  simp_rw [←hz]
  calc
    _ ≤ _ := measure_mono hsub
    _ = _ := htrans
    _ ≤ ENNReal.ofReal (9/5) * ENNReal.ofReal (4*L*Real.exp (-Y/L)) := mul_le_mul_right hE _
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤9/5)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_pos hL (Real.exp_pos (-Y/L))]

end RiemannMasullo.DiskSmallValues
