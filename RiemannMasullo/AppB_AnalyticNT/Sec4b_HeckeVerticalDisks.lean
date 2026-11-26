module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_NormalizedHeckeDisk
import RiemannMasullo.AppB_AnalyticNT.Sec6
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Uniform disk bounds for the ordinary pole-cleared Hecke L-function -/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped Asymptotics NNReal Topology

namespace RiemannMasullo.HeckeVerticalDisk
open HeckeDiskNormalization

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- The affine disk coordinate centered at height `T` on the line of real part two. -/
def chart (T : ℝ) (z : ℂ) : ℂ := 2 + (T:ℂ)*I + (9/5:ℂ)*z

/-- The actual pole-cleared ordinary Hecke continuation in the translated disk. -/
def translated (χ : U𝔽) (L : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ := cleared χ L (chart T z)

private theorem halfFactor_le_two (χ : U𝔽) {s : ℂ} (ht : 1 ≤ |s.im|) :
    ‖halfFactor χ s‖ ≤ 2 := by
  classical
  by_cases hc : χ = 1
  · have h : 1 ≤ ‖s‖ := ht.trans (abs_im_le_norm s)
    rw [halfFactor, ite_eq_left hc, norm_div, div_le_iff₀ (zero_lt_one.trans_le h)]
    have hn := norm_sub_le s (1:ℂ)
    rw [norm_one] at hn
    linarith
  · simp [halfFactor,hc]

/-- Polynomial growth on every fixed closed substrip of positive real parts,
including the filled point at one in the principal case. -/
theorem cleared_strip_polynomial_bound (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) {a b : ℝ} (ha : 0<a) (hab : a<b) :
    ∃ (N : ℕ) (K : ℝ), 0 < N ∧ 1 ≤ K ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖cleared χ L s‖ ≤ K * ‖s+1‖^N := by
  let S := Icc a b
  let ℓ := comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' S)
  obtain ⟨E,hE,hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL he a b hab
  have hsmall : cleared χ L =O[ℓ] L := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    have ht : Tendsto (abs ∘ Complex.im) ℓ atTop := tendsto_inf_left tendsto_comap
    have hin : ∀ᶠ s : ℂ in ℓ, s.re∈S := eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
    filter_upwards [ht.eventually_ge_atTop 1,hin] with s ht hs
    have hn : s ≠ 1 := by rintro rfl; norm_num [Function.comp_def] at ht
    rw [cleared_agrees τ hτ χ hχ L hL he (ha.trans_le hs.1) (fun h ↦ hn h.2),norm_mul]
    exact mul_le_mul_of_nonneg_right (halfFactor_le_two χ ht) (norm_nonneg _)
  have hcont : ContinuousOn (cleared χ L) (Complex.re ⁻¹' S) := fun s hs ↦
    (cleared_analytic τ hτ χ hχ L hL he (ha.trans_le hs.1)).continuousAt.continuousWithinAt
  obtain ⟨C,hC,hbound⟩ := exists_norm_le_mul_norm_sub_rpow (K:=S) isCompact_Icc hcont hE.le
    (hsmall.trans hO) (x0 := -1) (fun σ hσ ↦ by linarith [hσ.1])
  obtain ⟨n,hn⟩ := exists_nat_ge E
  refine ⟨n+1,max 1 C, by omega, le_max_left _ _,fun s hs ↦ ?_⟩
  have hx : 1 ≤ ‖s+1‖ := calc
    1 ≤ (s+1).re := by simp; linarith [hs.1]
    _ ≤ |(s+1).re| := le_abs_self _
    _ ≤ ‖s+1‖ := abs_re_le_norm _
  have hpow : ‖s+1‖^E ≤ ‖s+1‖^(n+1) := by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx
    push_cast
    linarith
  have H := hbound s hs
  simp only [ofReal_neg,ofReal_one,sub_neg_eq_add] at H
  exact H.trans (mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity))

/-- The lower bound at real part at least two depends only on the field. -/
def eulerFloor (F : Type*) [Field F] [NumberField F] : ℝ := 1/(2*‖dedekindZeta F (2:ℂ)‖)

private theorem zeta_two_norm_pos (F : Type*) [Field F] [NumberField F] :
    0 < ‖dedekindZeta F (2:ℂ)‖ := by
  have h := (finiteHeckeL_zeroFreeRegion_euler F (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    ⟨(2:ℂ), by norm_num⟩ (y:=2) (by norm_num) (by norm_num)).2
  norm_num only [Complex.ofReal_ofNat] at h
  by_contra! hn
  rw [le_antisymm hn (norm_nonneg _),mul_zero] at h
  norm_num at h

theorem eulerFloor_pos (F : Type*) [Field F] [NumberField F] : 0 < eulerFloor F := by
  exact one_div_pos.mpr (mul_pos (by norm_num) (zeta_two_norm_pos F))

private theorem half_le_halfFactor (χ : U𝔽) {s : ℂ} (hs : 2 ≤ s.re) : 1/2 ≤ ‖halfFactor χ s‖ := by
  classical
  by_cases hc : χ = 1
  · have hs0 : 0 < ‖s‖ := lt_of_lt_of_le (by linarith : 0 < s.re) (re_le_norm _)
    have hx : 1 ≤ ‖s-1‖ := calc
      1 ≤ (s-1).re := by simp; linarith
      _ ≤ ‖s-1‖ := re_le_norm _
    have hb : ‖s‖ ≤ ‖s-1‖+1 := by simpa using norm_add_le (s-1) (1:ℂ)
    rw [halfFactor,ite_eq_left hc,norm_div,le_div_iff₀ hs0]
    linarith
  · norm_num [halfFactor,hc]

/-- Uniform Euler lower bound, including the possible principal clearing factor. -/
theorem eulerFloor_le_norm_cleared (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) {s : ℂ} (hs : 2 ≤ s.re) :
    eulerFloor F ≤ ‖cleared χ L s‖ := by
  have hEuler : 1 < s.re := by linarith
  have heul := (finiteHeckeL_zeroFreeRegion_euler F χ ⟨s,hEuler⟩ (y:=2) (by norm_num) hs).2
  rw [← he ⟨s,hEuler⟩] at heul
  norm_num only [Complex.ofReal_ofNat] at heul
  have hfac : 1 ≤ 2*‖halfFactor χ s‖ := by linarith [half_le_halfFactor χ hs]
  have hn : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [eulerFloor,div_le_iff₀ (mul_pos (by norm_num) (zeta_two_norm_pos F)),
    cleared_agrees τ hτ χ hχ L hL he (by linarith) (fun h ↦ hn h.2), norm_mul]
  calc
    (1:ℝ) ≤ ‖L s‖ * ‖dedekindZeta F (2:ℂ)‖ := heul
    _ ≤ (2 * ‖halfFactor χ s‖) * (‖L s‖ * ‖dedekindZeta F (2:ℂ)‖) :=
      le_mul_of_one_le_left (by positivity) hfac
    _ = _ := by ring

/-- On the entire critical line the pole-clearing factor has norm one. -/
theorem norm_halfFactor_of_re_half (χ : U𝔽) {s : ℂ} (hs : s.re=1/2) : ‖halfFactor χ s‖=1 := by
  classical
  by_cases hc : χ=1
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have he : ‖s-1‖^2=‖s‖^2 := by
      simp [Complex.sq_norm,Complex.normSq_apply,hs]
      ring
    have hn : ‖s-1‖ = ‖s‖ := by nlinarith [norm_nonneg s,norm_nonneg (s-1)]
    rw [halfFactor,ite_eq_left hc,norm_div,hn,div_self (norm_ne_zero_iff.mpr hs0)]
  · simp [halfFactor,hc]

/-- Exact critical-line boundary equality, valid also at zeros of the continuation. -/
theorem norm_cleared_of_re_half (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) {s : ℂ} (hs : s.re=1/2) :
    ‖cleared χ L s‖ = ‖L s‖ := by
  have hn : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [cleared_agrees τ hτ χ hχ L hL he (by linarith) (fun h ↦ hn h.2),
    norm_mul,norm_halfFactor_of_re_half χ hs,one_mul]

theorem chart_zero (T : ℝ) : chart T 0 = 2+(T:ℂ)*I := by simp [chart]

/-- The larger disk has physical radius 19/10 and stays in the closed strip
from 1/10 through 39/10 uniformly in its real center height. -/
theorem chart_re_mem (T : ℝ) {z : ℂ} (hz : z ∈ closedBall 0 (19/18)) :
    (chart T z).re ∈ Icc (1/10) (39/10) := by
  have h : ‖z‖ ≤ 19/18 := by simpa using hz
  have hr := abs_le.mp ((abs_re_le_norm z).trans h)
  norm_num [chart,Complex.add_re,Complex.mul_re]
  constructor <;> linarith

private theorem chart_growth (T : ℝ) {z : ℂ} (hz : z ∈ closedBall 0 (19/18)) :
    ‖chart T z+1‖ ≤ 3*(2+|T|) := by
  have h : ‖z‖ ≤ 19/18 := by simpa using hz
  have hmid : ‖(2:ℂ)+(T:ℂ)*I‖ ≤ 2+|T| := by
    simpa [norm_mul,Real.norm_eq_abs] using norm_add_le (2:ℂ) ((T:ℂ)*I)
  have hrad : ‖(9/5:ℂ)*z‖ ≤ 19/10 := by
    rw [norm_mul]
    norm_num [norm_div]
    linarith
  calc
    ‖chart T z+1‖ ≤ ‖(2:ℂ)+(T:ℂ)*I+(9/5:ℂ)*z‖+1 := by
      simpa only [chart,norm_one] using norm_add_le (chart T z) (1:ℂ)
    _ ≤ 3*(2+|T|) := by linarith [norm_add_le ((2:ℂ)+(T:ℂ)*I) ((9/5:ℂ)*z),abs_nonneg T]

/-- Each closed translated disk has an analytic neighborhood. -/
theorem translated_analytic (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) (T : ℝ) :
    AnalyticOnNhd ℂ (translated χ L T) (closedBall 0 (19/18)) := by
  intro z hz
  have ha := cleared_analytic τ hτ χ hχ L hL he
    (show 0 < (chart T z).re by linarith [(chart_re_mem T hz).1])
  exact ha.comp (show AnalyticAt ℂ (chart T) z by unfold chart; fun_prop)

/-- The center lower bound is simultaneous in the height and character. -/
theorem eulerFloor_le_norm_center (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) (T : ℝ) :
    eulerFloor F ≤ ‖translated χ L T 0‖ := by
  apply eulerFloor_le_norm_cleared τ hτ χ hχ L hL he
  norm_num [chart_zero,Complex.mul_re]

/-- Polynomial upper bound uniform in the center height and the point of the disk. -/
theorem exists_disk_polynomial_bound (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) :
    ∃ (N : ℕ) (C : ℝ), 0<N ∧ Real.exp 1 ≤ C ∧ ∀ T : ℝ, ∀ z ∈ closedBall 0 (19/18),
      ‖translated χ L T z‖ ≤ C*(2+|T|)^N := by
  obtain ⟨N,K,hN,hK,hbound⟩ := cleared_strip_polynomial_bound τ hτ χ hχ L hL he
    (a:=1/10) (b:=39/10) (by norm_num) (by norm_num)
  refine ⟨N,max (Real.exp 1) (K*3^N),hN,le_max_left _ _,fun T z hz ↦ ?_⟩
  calc
    ‖translated χ L T z‖ ≤ K*‖chart T z+1‖^N := hbound _ (chart_re_mem T hz)
    _ ≤ K*(3*(2+|T|))^N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (chart_growth T hz) _) (by linarith)
    _ ≤ _ := by
      rw [mul_pow,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private theorem log_ratio_polynomial {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (N : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T y : ℝ), c ≤ y →
      Real.log (C*(2+|T|)^N/y) ≤ A*Real.log (2+|T|) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a := |Real.log (C/c)| / Real.log 2
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hl2.le
  refine ⟨a+N+1, by positivity, fun T y hy ↦ ?_⟩
  have hH : 0 < 2+|T| := by positivity
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith [abs_nonneg T] : 2≤2+|T|)
  have ha₂ : a*Real.log 2 = |Real.log (C/c)| := div_mul_cancel₀ _ hl2.ne'
  have hu : Real.log (C/c) ≤ a * Real.log (2+|T|) := calc
    _ ≤ |Real.log (C/c)| := le_abs_self _
    _ = a*Real.log 2 := ha₂.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hl ha
  apply (Real.log_le_log (div_pos (mul_pos hC (pow_pos hH _)) (hc.trans_le hy))
    (div_le_div_of_nonneg_left (mul_nonneg hC.le (pow_nonneg hH.le _)) hc hy)).trans
  rw [show C*(2+|T|)^N/c = (C/c)*(2+|T|)^N by ring,Real.log_mul (div_pos hC hc).ne' (pow_pos hH _).ne',
    Real.log_pow,add_mul,add_mul,one_mul]
  linarith

/-- Real supremum of the norm on the enlarged unit disk. -/
def diskSup (g : ℂ → ℂ) : ℝ := sSup ((fun z ↦ ‖g z‖) '' closedBall 0 (19/18))

private theorem diskSup_bounds (g : ℂ → ℂ) {M : ℝ}
    (h : ∀ z ∈ closedBall 0 (19/18), ‖g z‖ ≤ M) : ‖g 0‖ ≤ diskSup g ∧ diskSup g ≤ M := by
  have h0 : (0:ℂ) ∈ closedBall 0 (19/18) := mem_closedBall_self (by norm_num)
  have hb : ∀ y ∈ (fun z ↦ ‖g z‖) '' closedBall 0 (19/18), y ≤ M := by
    rintro _ ⟨z,hz,rfl⟩
    exact h z hz
  have hc := mem_image_of_mem (fun z ↦ ‖g z‖) h0
  exact ⟨le_csSup ⟨M,hb⟩ hc,csSup_le ⟨_,hc⟩ hb⟩

/-- Local analytic, Euler and norm data for every real height. Both the explicit
envelope ratio and the actual disk-maximum ratio have logarithmic growth. -/
theorem exists_uniform_disk_data (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) :
    ∃ (N : ℕ) (C A : ℝ), 0 < N ∧ Real.exp 1 ≤ C ∧ 0 < A ∧ 0 < eulerFloor F ∧
      ∀ T : ℝ, let g := translated χ L T
        let M := C*(2+|T|)^N
        AnalyticOnNhd ℂ g (closedBall 0 (19/18)) ∧ eulerFloor F ≤ ‖g 0‖ ∧ Real.exp 1 ≤ M ∧
        (∀ z ∈ closedBall 0 (19/18), ‖g z‖ ≤ M) ∧ diskSup g ≤ M ∧
        Real.log (M/‖g 0‖) ∈ Icc 0 (A*Real.log (2+|T|)) ∧
        Real.log (diskSup g/‖g 0‖) ∈ Icc 0 (A*Real.log (2+|T|)) := by
  obtain ⟨N,C,hN,hC,hu⟩ := exists_disk_polynomial_bound τ hτ χ hχ L hL he
  obtain ⟨A,hA,ha⟩ := log_ratio_polynomial ((Real.exp_pos _).trans_le hC) (eulerFloor_pos F) N
  refine ⟨N,C,A,hN,hC,hA,eulerFloor_pos F,fun T ↦ ?_⟩
  dsimp only
  have hd := eulerFloor_le_norm_center τ hτ χ hχ L hL he T
  have hp := (eulerFloor_pos F).trans_le hd
  obtain ⟨hsc,hsm⟩ := diskSup_bounds (translated χ L T) (hu T)
  have hl := ha T _ hd
  have hM : Real.exp 1 ≤ C*(2+|T|)^N := hC.trans (le_mul_of_one_le_right ((Real.exp_pos _).trans_le hC).le
    (one_le_pow₀ (show (1:ℝ) ≤ 2+|T| by linarith [abs_nonneg T])))
  exact ⟨translated_analytic τ hτ χ hχ L hL he T,hd,hM,hu T,hsm,
    ⟨Real.log_nonneg ((one_le_div hp).mpr (hsc.trans hsm)),hl⟩,
    ⟨Real.log_nonneg ((one_le_div hp).mpr hsc),
      (Real.log_le_log (div_pos (hp.trans_le hsc) hp) (div_le_div_of_nonneg_right hsm hp.le)).trans hl⟩⟩

/-- Disk coordinate of the point with real part one half and imaginary part `t`. -/
def criticalCoordinate (T t : ℝ) : ℂ := ⟨-(5/6), (5/9)*(t-T)⟩

theorem chart_criticalCoordinate (T t : ℝ) : chart T (criticalCoordinate T t) = ⟨1/2,t⟩ := by
  apply Complex.ext <;> norm_num [chart,criticalCoordinate,Complex.mul_re,Complex.mul_im]
  ring

/-- A full unit interval of the critical line belongs to the smaller disk of
normalized radius 9/10 and physical radius 81/50. -/
theorem criticalCoordinate_mem_inner {T t : ℝ} (ht : |t-T| ≤ 1/2) :
    criticalCoordinate T t ∈ ball 0 (9/10) := by
  rw [mem_ball_zero_iff]
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (9/10:ℝ))).mp
  rw [Complex.sq_norm,Complex.normSq_apply]
  have hs : (t-T)^2 ≤ (1/2:ℝ)^2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mpr ht
  dsimp [criticalCoordinate]
  nlinarith

/-- The translated modulus agrees exactly with the true critical-line modulus,
even when the ordinary continuation vanishes at this point. -/
theorem norm_translated_criticalCoordinate (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) (T t : ℝ) :
    ‖translated χ L T (criticalCoordinate T t)‖ = ‖L ⟨1/2,t⟩‖ := by
  rw [translated,chart_criticalCoordinate]
  exact norm_cleared_of_re_half τ hτ χ hχ L hL he rfl

/-- Simultaneous disk data and critical-line identification for the canonical
finite Hecke continuation. Only the normalized character and norm section are inputs. -/
theorem canonical_jensen_input (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∃ (N : ℕ) (C A : ℝ), 0<N ∧ Real.exp 1 ≤ C ∧ 0<A ∧ 0<eulerFloor F ∧
      (∀ t : ℝ, ‖cleared χ L ⟨1/2,t⟩‖ = ‖L ⟨1/2,t⟩‖) ∧
      ∀ T : ℝ, let g := translated χ L T
        let M := C*(2+|T|)^N
        AnalyticOnNhd ℂ g (closedBall 0 (19/18)) ∧ eulerFloor F ≤ ‖g 0‖ ∧ Real.exp 1 ≤ M ∧
        (∀ z ∈ closedBall 0 (19/18), ‖g z‖ ≤ M) ∧ diskSup g ≤ M ∧
        Real.log (M/‖g 0‖) ∈ Icc 0 (A*Real.log (2+|T|)) ∧
        Real.log (diskSup g/‖g 0‖) ∈ Icc 0 (A*Real.log (2+|T|)) := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨N,C,A,hN,hC,hA,hc,H⟩ := exists_uniform_disk_data τ hτ χ hχ _ hL he
  exact ⟨N,C,A,hN,hC,hA,hc,fun t ↦ norm_cleared_of_re_half τ hτ χ hχ _ hL he rfl,H⟩

/-- The actual input for the vertical small-value estimate, with one logarithmic
constant for the envelope and its ratio to the center. The height window lies
in radius 9/10, and analyticity and the envelope hold through radius 19/18. -/
theorem canonical_window_input (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∃ K : ℝ, 1 ≤ K ∧ ∃ M : ℝ → ℝ,
      (∀ t : ℝ, ‖cleared χ L ⟨1/2,t⟩‖ = ‖L ⟨1/2,t⟩‖) ∧
      ∀ T : ℝ, let g := translated χ L T
        AnalyticOnNhd ℂ g (closedBall 0 (19/18)) ∧ 1 ≤ M T ∧ 0 < ‖g 0‖ ∧
        (∀ z ∈ closedBall 0 (19/18), ‖g z‖ ≤ M T) ∧
        Real.log (M T) ≤ K*(1+Real.log (2+|T|)) ∧
        Real.log (M T/‖g 0‖) ≤ K*(1+Real.log (2+|T|)) ∧
        ∀ t : ℝ, |t-T| ≤ 1/2 → criticalCoordinate T t ∈ ball 0 (9/10) ∧
          ‖g (criticalCoordinate T t)‖ = ‖L ⟨1/2,t⟩‖ := by
  obtain ⟨N,C,A,_,hC,hA,hc,hline,H⟩ := canonical_jensen_input τ hτ χ hχ
  have hCpos := (Real.exp_pos _).trans_le hC
  let K := 1+A+|Real.log C|+N
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log C),Nat.cast_nonneg (α:=ℝ) N]
  have hAK : A ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log C),Nat.cast_nonneg (α:=ℝ) N]
  have hNK : (N:ℝ) ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log C)]
  have hCK : Real.log C ≤ K := by dsimp [K]; linarith [le_abs_self (Real.log C),Nat.cast_nonneg (α:=ℝ) N]
  refine ⟨K,hK,fun T ↦ C*(2+|T|)^N,hline,fun T ↦ ?_⟩
  obtain ⟨hAn,hcent,hM,hbound,_,hr,_⟩ := H T
  have hT : 0 < 2+|T| := by positivity
  have hlog : 0 ≤ Real.log (2+|T|) := Real.log_nonneg (by linarith [abs_nonneg T])
  have hilog : Real.log (C*(2+|T|)^N) ≤ K*(1+Real.log (2+|T|)) := by
    rw [Real.log_mul hCpos.ne' (pow_pos hT _).ne',Real.log_pow,mul_add,mul_one]
    exact add_le_add hCK (mul_le_mul_of_nonneg_right hNK hlog)
  have hiratio := hr.2.trans (mul_le_mul_of_nonneg_right hAK hlog)
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact ⟨hAn,(Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hM,hc.trans_le hcent,hbound,hilog,
    hiratio.trans (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hK)),
    fun t ht ↦ ⟨criticalCoordinate_mem_inner ht,norm_translated_criticalCoordinate τ hτ χ hχ _ hL he T t⟩⟩

end RiemannMasullo.HeckeVerticalDisk
