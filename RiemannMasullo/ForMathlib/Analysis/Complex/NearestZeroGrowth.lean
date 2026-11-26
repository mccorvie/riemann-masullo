module

public import RiemannMasullo.ForMathlib.Analysis.Complex.SignedFrequency
public import RiemannMasullo.ForMathlib.Analysis.Complex.LogDerivativeCoefficients
import Mathlib.Tactic

/-! # The nearest zero and both signs of logarithmic Taylor coefficients

For a holomorphic function on the unit disk with no zero on the nonnegative real radius,
the positive and negative prefix sums of its real logarithmic Taylor coefficients have the
same exponential growth rate. The first pole circle determines the rate. -/

@[expose] public noncomputable section

open Complex Filter Function Metric Set
open scoped Topology

namespace RiemannMasullo.DiskLogCoefficient
open SignedFrequency

/-- Positive indices are conventional logarithmic Taylor coefficients; the unused index zero
keeps the respective signed prefix range 1 through N. -/
def signedCoeff (f : ℂ → ℂ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (coeff (logDeriv f) n).re

private theorem coeffEnvelope_of_empty {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hz : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    ∀ A : ℝ, 1 < A → ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |signedCoeff f n| ≤ B*A^n := by
  intro A hA
  have hA0 := zero_lt_one.trans hA
  have ha : A⁻¹ < 1 := (inv_lt_one₀ hA0).mpr hA
  have hD : AnalyticOnNhd ℂ (logDeriv f) (closedBall 0 A⁻¹) := by
    intro z hz'
    have hi := (closedBall_subset_ball ha) hz'
    exact (hf z hi).deriv.div (hf z hi) (hz z hi)
  obtain ⟨C, hC, h⟩ := cauchy_coeff (inv_pos.mpr hA0) hD
  refine ⟨C, hC, ?_⟩
  rintro (_|n)
  · simpa [signedCoeff] using hC
  · calc
      |signedCoeff f (n+1)| ≤ ‖coeff (logDeriv f) n‖ := Complex.abs_re_le_norm _
      _ ≤ C/A⁻¹^n := h n
      _ = C*A^n := by simp [div_eq_mul_inv]
      _ ≤ C*A^(n+1) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA.le (by omega)) hC

/-- A zero-free disk gives rate zero for each orientation. -/
theorem both_prefix_rate_zero_of_no_roots {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hz : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (signedCoeff f) N)/(N:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -signedCoeff f n) N)/(N:ℝ)) atTop (𝓝 0) :=
  tendsto_both_log_prefixes_of_subexponential (coeffEnvelope_of_empty hf hz)

private theorem divisor_pos_iff {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0) {a : ℂ} (ha : a ∈ closedBall 0 R) :
    0 < MeromorphicOn.divisor f (closedBall 0 R) a ↔ f a = 0 := by
  have hB : 0 ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have htop : meromorphicOrderAt f a ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall (0 : ℂ) R).isPreconnected
      hB ha (by rw [(hf 0 hB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]; simp)
  have hnonneg := (hf a ha).meromorphicOrderAt_nonneg
  have hzero := (hf a ha).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff
  rw [hf.meromorphicOn.divisor_apply ha]
  generalize hg : meromorphicOrderAt f a = q at htop hnonneg hzero ⊢
  lift q to ℤ using htop with k
  simp only [WithTop.coe_nonneg, WithTop.untop₀_coe, WithTop.coe_eq_zero] at *
  constructor
  · intro hk
    by_contra hv
    have := hzero.mpr hv
    omega
  · intro hv
    have hn : k ≠ 0 := fun hk ↦ (hzero.mp hk) hv
    omega

private theorem phase_term {r : ℝ} (hr : 0 < r) (a : ℂ) (m : ℤ) (n : ℕ) :
    r⁻¹^n * ((m:ℝ) * (((r:ℂ)/a)^n).re) = ((m:ℂ)/a^n).re := by
  rw [← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul]
  congr 1
  push_cast
  rw [div_pow, inv_pow]
  have h : (r:ℂ)^n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
  field_simp

private theorem nearest_error {f : ℂ → ℂ} {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {S : Finset ℂ} {D : ℂ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, ‖coeff (logDeriv f) n + ∑ a ∈ S, (D a : ℂ)/a^(n+1)‖ ≤ C/R^n)
    (hmin : ∀ a ∈ S, r ≤ ‖a‖) (hrR : r < R) :
    let E := S.filter fun a ↦ ‖a‖=r
    ∃ R₂ C₂ : ℝ, r < R₂ ∧ ∀ᶠ n : ℕ in atTop,
      |signedCoeff f n + r⁻¹^n * (∑ a ∈ E, (D a : ℝ)*(((r:ℂ)/a)^n).re)| ≤ C₂*R₂⁻¹^n := by
  classical
  let E := S.filter fun a ↦ ‖a‖=r
  let T := S.filter fun a ↦ ‖a‖≠r
  let V := insert R (T.image norm)
  have hne : V.Nonempty := Finset.insert_nonempty _ _
  let R₂ := V.min' hne
  have hR2 : r < R₂ := by
    obtain h | h := Finset.mem_insert.mp (V.min'_mem hne)
    · simpa only [R₂, h] using hrR
    · obtain ⟨a, ha, e⟩ := Finset.mem_image.mp h
      change r < V.min' hne
      rw [← e]
      exact lt_of_le_of_ne (hmin a ((Finset.mem_filter.mp ha).1)) (Finset.mem_filter.mp ha).2.symm
  have hR2R : R₂ ≤ R := V.min'_le R (Finset.mem_insert_self _ _)
  have hR2a (a : ℂ) (ha : a ∈ T) : R₂ ≤ ‖a‖ := V.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem norm ha))
  let C₂ := C*R + ∑ a ∈ T, ‖(D a:ℂ)‖
  refine ⟨R₂,C₂,hR2,?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hRR := hr.trans hR2
  have hci := hcoeff k
  let Vn (a : ℂ) := (D a : ℂ)/a^(k+1)
  have hsum : ∑ a ∈ E, Vn a + ∑ a ∈ T, Vn a = ∑ a ∈ S, Vn a := by
    exact Finset.sum_filter_add_sum_filter_not S _ Vn
  have hphase : r⁻¹^(k+1) * (∑ a ∈ E, (D a : ℝ) * (((r:ℂ)/a)^(k+1)).re) =
      (∑ a ∈ E, Vn a).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _ ↦ phase_term hr a (D a) _)
  have htail (a : ℂ) (ha : a ∈ T) : ‖Vn a‖ ≤ ‖(D a:ℂ)‖*R₂⁻¹^(k+1) := by
    rw [show ‖Vn a‖ = ‖(D a:ℂ)‖/‖a‖^(k+1) by simp [Vn], inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hRR _) (pow_le_pow_left₀ hRR.le (hR2a a ha) _)
  have hrem : C / R^k ≤ C*R*R₂⁻¹^(k+1) := by
    rw [inv_pow, ← div_eq_mul_inv]
    calc
      C / R^k = C*R / R^(k+1) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC hR.le) (pow_pos hRR _) (pow_le_pow_left₀ hRR.le hR2R _)
  rw [hphase]
  change |(coeff (logDeriv f) k).re + (∑ a ∈ E, Vn a).re| ≤ _
  rw [← Complex.add_re]
  calc
    _ ≤ ‖coeff (logDeriv f) k + ∑ a ∈ E, Vn a‖ := Complex.abs_re_le_norm _
    _ = ‖(coeff (logDeriv f) k + ∑ a ∈ S, Vn a) - ∑ a ∈ T, Vn a‖ := by rw [← hsum]; abel_nf
    _ ≤ ‖coeff (logDeriv f) k + ∑ a ∈ S, Vn a‖ + ‖∑ a ∈ T, Vn a‖ := norm_sub_le _ _
    _ ≤ C*R*R₂⁻¹^(k+1) + ∑ a ∈ T, ‖(D a:ℂ)‖*R₂⁻¹^(k+1) :=
      add_le_add (hci.trans hrem) ((norm_sum_le _ _).trans (Finset.sum_le_sum htail))
    _ = _ := by rw [← Finset.sum_mul]; dsimp [C₂]; ring

/-- A single zero in the disk forces the ordinary exponential rates of both signed Taylor
prefixes. The minimizing root can have any multiplicity and can share its circle with others. -/
theorem exists_nearest_both_prefix_rates {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (h0 : f 0 ≠ 0) (hreal : ∀ x : ℝ, 0 ≤ x → x < 1 → f (x:ℂ) ≠ 0)
    (w : ℂ) (hw : ‖w‖ < 1) (hwf : f w = 0) :
    ∃ a : ℂ, 0 < ‖a‖ ∧ ‖a‖ < 1 ∧ f a = 0 ∧
      (∀ z : ℂ, ‖z‖ < 1 → f z = 0 → ‖a‖ ≤ ‖z‖) ∧
      Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (signedCoeff f) N)/(N:ℝ))
        atTop (𝓝 (Real.log ‖a‖⁻¹)) ∧
      Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -signedCoeff f n) N)/(N:ℝ))
        atTop (𝓝 (Real.log ‖a‖⁻¹)) := by
  classical
  let R := (‖w‖ + 1)/2
  have hwR : ‖w‖ < R := by dsimp [R]; linarith
  have hR0 : 0 < R := (norm_nonneg _).trans_lt hwR
  have hR1 : R < 1 := by dsimp [R]; linarith
  let B := closedBall (0 : ℂ) R
  have hfB : AnalyticOnNhd ℂ f B := hf.mono (closedBall_subset_ball hR1)
  let D := MeromorphicOn.divisor f B
  let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  have hS (z : ℂ) : z ∈ S ↔ D z ≠ 0 := Set.Finite.mem_toFinset _
  have hD (z : ℂ) (hz : z ∈ B) : 0 < D z ↔ f z=0 := divisor_pos_iff hR0 hfB h0 hz
  have hnonneg (z : ℂ) : 0 ≤ D z := (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfB) z
  have hwmem : w ∈ S := (hS w).mpr ((hD w (mem_closedBall_zero_iff.mpr hwR.le)).mpr hwf).ne'
  obtain ⟨a, has, hmin⟩ := S.exists_min_image norm ⟨w,hwmem⟩
  have hab : a ∈ B := D.supportWithinDomain ((hS a).mp has)
  have haord : 0 < D a := lt_of_le_of_ne (hnonneg a) ((hS a).mp has).symm
  have hfa := (hD a hab).mp haord
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr (fun he ↦ h0 (he ▸ hfa))
  let r := ‖a‖
  have hrR : r < R := (hmin w hwmem).trans_lt hwR
  have hr1 : r < 1 := hrR.trans hR1
  refine ⟨a,hapos,hr1,hfa,?_,?_⟩
  · intro z _ hz
    by_cases he : ‖z‖ ≤ R
    · exact hmin z ((hS z).mpr ((hD z (mem_closedBall_zero_iff.mpr he)).mpr hz).ne')
    · exact hrR.le.trans (le_of_not_ge he)
  let E := S.filter fun z ↦ ‖z‖=r
  obtain ⟨C,hC,hb⟩ := logDeriv_coeff_principalParts hR0 hfB h0
  obtain ⟨R₂,C₂,hgap,herr⟩ := nearest_error (S := S) (D := D) hR0 hapos hC hb hmin hrR
  have hunit : ∀ z ∈ E, ‖(r:ℂ)/z‖=1 := by
    intro z hz
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hapos.le, (Finset.mem_filter.mp hz).2,
      div_self hapos.ne']
  have hnotone : ∀ z ∈ E, (r:ℂ)/z ≠ 1 := by
    intro z hz he
    have hze := Finset.mem_filter.mp hz
    have hzn : z ≠ 0 := norm_pos_iff.mp (hze.2.trans_gt hapos)
    have hex : (r:ℂ)=z := (div_eq_one_iff_eq hzn).mp he
    have ho := lt_of_le_of_ne (hnonneg z) ((hS z).mp hze.1).symm
    have hfz := (hD z (D.supportWithinDomain ((hS z).mp hze.1))).mp ho
    exact hreal r hapos.le hr1 (hex ▸ hfz)
  have hi : a ∈ E := Finset.mem_filter.mpr ⟨has,rfl⟩
  have he_nat : ∀ z : ℂ, ((D z).toNat : ℝ) = (D z : ℝ) := by
    intro z
    exact_mod_cast Int.toNat_of_nonneg (hnonneg z)
  apply tendsto_both_log_prefixes_of_nearest_circle (s := E) (m := fun z ↦ (D z).toNat)
    (z := fun z ↦ (r:ℂ)/z) hunit hnotone hi (by omega) hapos hr1 hgap (C := C₂)
  simpa only [he_nat] using herr


end RiemannMasullo.DiskLogCoefficient
