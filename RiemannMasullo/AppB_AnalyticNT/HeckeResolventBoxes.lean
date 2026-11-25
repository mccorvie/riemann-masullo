module

public import RiemannMasullo.AppB_AnalyticNT.ResolventRectangle
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeReflection
public import RiemannMasullo.AppB_AnalyticNT.FiniteHeckeHorizontal
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeOuterLogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Sublinear regular boundary rectangles for the completed Hecke logarithmic derivative -/

public noncomputable section

open Classical Complex Filter NumberField Set
open scoped ComplexConjugate Topology

namespace RiemannMasullo.ResolventRectangle

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "Λ(" χ ")" => continuedCompletedHeckeL χ
local notation "Q(" χ ")" => (heckeLogDiscriminantConductor χ : ℂ)

/-- At a nonzero value of the finite continuation in the positive half-plane, the
completed continuation agrees locally with its ordinary gamma-times-finite product. -/
private theorem completed_regular_product (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ w : {w : ℂ // 1 < w.re}, L w = finiteHeckeL χ w)
    {s : ℂ} (hs : 0 < s.re) (hLs : L s ≠ 0) :
    meromorphicOrderAt Λ(χ) s = 0 ∧
      logDeriv Λ(χ) s = logDeriv (heckeGammaFactor χ) s + logDeriv L s := by
  let P (w : ℂ) := heckeGammaFactor χ w * L w
  have hΛ := continuedCompletedHeckeL_spec χ
  have hP : MeromorphicOn P univ := fun w hw ↦
    (meromorphic_heckeGammaFactor χ w).mul (hL hw).meromorphicAt
  have hglob := heckeEulerProductOutside_eq_finite_nf_eq Λ(χ) P hΛ.1.meromorphicOn hP (fun w hw ↦ by
    change Λ(χ) w = heckeGammaFactor χ w * L w
    rw [show L w = finiteHeckeL χ ⟨w, hw⟩ from hSeries ⟨w, hw⟩]
    exact hΛ.2 ⟨w, hw⟩)
  rw [toMeromorphicNFOn_eq_self.mpr hΛ.1] at hglob
  have hA : AnalyticAt ℂ L s := (hL (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hLs).ge
  have hG : AnalyticAt ℂ (heckeGammaFactor χ) s :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hw).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  have hPA : AnalyticAt ℂ P s := hG.mul hA
  have he : Λ(χ) =ᶠ[𝓝 s] P := by
    filter_upwards [hPA.eventually_analyticAt] with w hw
    rw [hglob, toMeromorphicNFOn_eq_toMeromorphicNFAt hP (mem_univ w),
      toMeromorphicNFAt_eq_self.mpr hw.meromorphicNFAt]
  have hG0 := heckeGammaFactor_ne_zero_of_re_pos χ hs
  refine ⟨(hΛ.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr (?_ : Λ(χ) s ≠ 0), ?_⟩
  · rw [he.eq_of_nhds]
    exact mul_ne_zero hG0 hLs
  · exact (logDeriv_congr_nhds he).eq_of_nhds.trans
      (logDeriv_fun_mul s hG0 hLs hG.differentiableAt hA.differentiableAt)

private theorem reflected_order_zero (χ : U𝔽) {s : ℂ} (hs : meromorphicOrderAt Λ(χ) s = 0) :
    meromorphicOrderAt Λ(χ) (1 - conj s) = 0 := by
  have hχ := continuedCompletedHeckeL_spec χ
  have hI := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨C, hC, hFE⟩ := completedHeckeL_functionalEquation_conductorScale χ _ _ hχ.1 hχ.2 hI.1 hI.2
  have hne := (hχ.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp hs
  have hdual : Λ(χ⁻¹) (1 - s) ≠ 0 := by
    rw [hFE]
    exact mul_ne_zero (mul_ne_zero hC (Complex.exp_ne_zero _)) hne
  apply (hχ.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
  intro h
  apply hdual
  simp only [completed_inv_eq_conj χ, Function.comp_apply, map_sub, map_one, h, map_zero]

private theorem euler_order_zero (χ : U𝔽) {s : ℂ} (hs : 2 ≤ s.re) :
    meromorphicOrderAt Λ(χ) s = 0 := by
  have hz := one_lt_two.trans_le hs
  have h := continuedCompletedHeckeL_spec χ
  apply (h.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
  rw [h.2 ⟨s, hz⟩]
  change heckeGammaFactor χ s * finiteHeckeL χ ⟨s, hz⟩ ≠ 0
  exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))
    (finiteHeckeL_ne_zero_of_one_lt_re χ _)

private theorem raw_outer (χ : U𝔽) :
    ∃ C > (0 : ℝ), ∀ s : ℂ, s.re ≤ -1 ∨ 2 ≤ s.re →
      meromorphicOrderAt Λ(χ) s = 0 ∧ ‖logDeriv Λ(χ) s‖ ≤ C * (1 + Real.log (2 + ‖s‖)) := by
  obtain ⟨D, hD, hd⟩ := completedHeckeL_poleCleared_logDeriv_bound_outer χ
  refine ⟨D + 2, by linarith, ?_⟩
  intro s hs
  constructor
  · rcases hs with h | h
    · have hz : 2 ≤ (1 - conj s).re := by rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
      simpa only [map_sub, map_one, Complex.conj_conj, sub_sub_cancel] using
        reflected_order_zero χ (euler_order_zero χ hz)
    · exact euler_order_zero χ h
  · have inv_bound (z : ℂ) (hz : 1 ≤ |z.re|) : ‖1 / z‖ ≤ 1 := by
      have hn := hz.trans (Complex.abs_re_le_norm z)
      rw [norm_div, norm_one]
      exact (div_le_one (zero_lt_one.trans_le hn)).mpr hn
    have h1 : 1 ≤ |s.re| := by
      rcases hs with h | h <;> linarith [neg_le_abs s.re, le_abs_self s.re]
    have h2 : 1 ≤ |(s - 1).re| := by
      rw [Complex.sub_re, Complex.one_re]
      rcases hs with h | h <;> linarith [neg_le_abs (s.re - 1), le_abs_self (s.re - 1)]
    let P : ℂ := if χ = 1 then 1 / s + 1 / (s - 1) else 0
    have hP : ‖P‖ ≤ 2 := by
      dsimp only [P]
      split_ifs
      · linarith [norm_add_le (1/s) (1/(s-1)), inv_bound s h1, inv_bound (s-1) h2]
      · norm_num
    have ht : ‖logDeriv Λ(χ) s‖ ≤ ‖logDeriv Λ(χ) s + P‖ + ‖P‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (logDeriv Λ(χ) s + P) P
    have hlog := Real.log_nonneg (by linarith [norm_nonneg s] : 1 ≤ 2 + ‖s‖)
    have hc : ‖logDeriv Λ(χ) s + P‖ ≤ D * (1 + Real.log (2 + ‖s‖)) := hd s hs
    linarith [ht, hP, hc, show (D + 2) * (1 + Real.log (2 + ‖s‖)) =
      D * (1 + Real.log (2 + ‖s‖)) + 2 + 2 * Real.log (2 + ‖s‖) by ring]

private def regularBound (L : ℂ → ℂ) (z : ℂ) (M : ℝ) : Prop :=
  meromorphicOrderAt L z = 0 ∧ ‖logDeriv L z‖ ≤ M

private theorem of_bound_on_edges {L : ℂ → ℂ} {R A B M : ℝ}
    (ha : A ∈ Icc (-R-1) (-R)) (hb : B ∈ Icc R (R+1)) (hm : 0 ≤ M)
    (hH : ∀ x ∈ Icc (-R) R, ∀ y ∈ ({A, B} : Set ℝ), regularBound L ⟨x,y⟩ M)
    (hV : ∀ y ∈ Icc A B, ∀ x ∈ ({-R, R} : Set ℝ), regularBound L ⟨x,y⟩ M) :
    RegularLogDerivBox L R A B M := by
  refine ⟨ha, hb, hm, ?_, ?_, ?_⟩
  · rintro ⟨x,y⟩ hclosed hnot
    change x ∈ Icc (-R) R ∧ y ∈ Icc A B at hclosed
    change ¬ (x ∈ Ioo (-R) R ∧ y ∈ Ioo A B) at hnot
    by_cases hx : x = -R ∨ x = R
    · exact (hV y hclosed.2 x (by simpa only [mem_insert_iff, mem_singleton_iff] using hx)).1
    by_cases hy : y = A ∨ y = B
    · exact (hH x hclosed.1 y (by simpa only [mem_insert_iff, mem_singleton_iff] using hy)).1
    push Not at hx hy
    exact (hnot ⟨⟨lt_of_le_of_ne hclosed.1.1 (Ne.symm hx.1), lt_of_le_of_ne hclosed.1.2 hx.2⟩,
      ⟨lt_of_le_of_ne hclosed.2.1 (Ne.symm hy.1), lt_of_le_of_ne hclosed.2.2 hy.2⟩⟩).elim
  · intro x hx y hy
    rw [← Complex.mk_eq_add_mul_I]
    exact (hH x hx y hy).2
  · intro y hy x hx
    rw [← Complex.mk_eq_add_mul_I]
    exact (hV y hy x hx).2

/-- The linear-logarithmic bound on a box is absorbed by a squared logarithm in its width. -/
private theorem log_bound_on_box {R : ℝ} (hu : 1 ≤ Real.log (R+3))
    {z : ℂ} (hx : |z.re| ≤ R) (hy : |z.im| ≤ R+1) :
    1 + Real.log (2 + ‖z‖) ≤ 3 * Real.log (R+3)^2 := by
  have hm : 2 + ‖z‖ ≤ (R+3)^2 := by
    nlinarith only [Complex.norm_le_abs_re_add_abs_im z, hx, hy, (abs_nonneg z.re).trans hx, sq_nonneg R]
  have hl := Real.log_le_log (by positivity) hm
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith only [hl, hu, mul_nonneg (sub_nonneg.mpr hu) (zero_le_one.trans hu)]

private theorem tendsto_log_sq_height_div (K : ℝ) :
    Tendsto (fun n : ℕ ↦ (K * Real.log ((n : ℝ)+3)^2) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := 1) 2 zero_lt_one).tendsto_div_nhds_zero
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ ↦ ((n : ℝ)+3) / n) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using (tendsto_natCast_div_add_atTop (3 : ℝ)).inv₀ one_ne_zero
  have hc : Tendsto (fun n : ℕ ↦ K * ((Real.log ((n : ℝ)+3)^2 / ((n : ℝ)+3)) *
      (((n : ℝ)+3) / n))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul, mul_zero] using ((hlog.comp hx).mul hr).const_mul K
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hne' : (n : ℝ)+3 ≠ 0 := by positivity
  field_simp

private def boundaryConstant (E G H Q : ℝ) : ℝ :=
  max (3*E) (3*G + H + Q)

/-- A pair of simultaneous good finite segments controls the full horizontal edges
by gamma multiplication and same-height reflection. The Euler bounds cover the vertical edges. -/
private theorem box_of_good_segments (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ w : {w : ℂ // 1 < w.re}, L w = finiteHeckeL χ w)
    {E G H R A B : ℝ} (hE : 0 < E) (hG : 0 < G) (hR : 2 ≤ R) (hu : 1 ≤ Real.log (R+3))
    (ha : A ∈ Ioo (-R-1) (-R)) (hb : B ∈ Ioo R (R+1))
    (houter : ∀ z : ℂ, z.re ≤ -1 ∨ 2 ≤ z.re →
      meromorphicOrderAt Λ(χ) z = 0 ∧ ‖logDeriv Λ(χ) z‖ ≤ E * (1 + Real.log (2 + ‖z‖)))
    (hgamma : ∀ z : ℂ, 1/2 ≤ z.re →
      ‖logDeriv (heckeGammaFactor χ) z‖ ≤ G * (1 + Real.log (2 + ‖z‖)))
    (hfinite : ∀ y ∈ ({A, B} : Set ℝ), ∀ x ∈ Icc (1/2 : ℝ) 2,
      L ⟨x,y⟩ ≠ 0 ∧ ‖logDeriv L ⟨x,y⟩‖ ≤ H * Real.log (R+3)^2) :
    RegularLogDerivBox Λ(χ) R A B (boundaryConstant E G H ‖Q(χ)‖ * Real.log (R+3)^2) := by
  let u := Real.log (R+3)
  let D := ‖Q(χ)‖
  let K := boundaryConstant E G H D
  have hu2 : 1 ≤ u^2 := by
    change 1 ≤ Real.log (R+3)^2
    nlinarith [sq_nonneg (Real.log (R+3) - 1)]
  have hOE : 3*E ≤ K := le_max_left _ _
  have hMID : 3*G+H+D ≤ K := le_max_right _ _
  have hR0 : 0 ≤ R := by linarith
  have hab : A ≤ B := by linarith [ha.2, hb.1]
  have hya (y : ℝ) (hy : y ∈ Icc A B) : |y| ≤ R+1 :=
    abs_le.mpr ⟨by linarith [hy.1, ha.1], by linarith [hy.2, hb.2]⟩
  have hyi (y : ℝ) (hy : y ∈ ({A,B} : Set ℝ)) : y ∈ Icc A B := by
    rcases (show y=A ∨ y=B by simpa only [mem_insert_iff, mem_singleton_iff] using hy) with rfl | rfl
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  have outside (x y : ℝ) (hx : |x| ≤ R) (hy : y ∈ Icc A B) (hs : x ≤ -1 ∨ 2 ≤ x) :
      regularBound Λ(χ) ⟨x,y⟩ (K*u^2) := by
    obtain ⟨ho, hg⟩ := houter ⟨x,y⟩ hs
    have hw := log_bound_on_box (z := ⟨x,y⟩) hu hx (hya y hy)
    refine ⟨ho, ?_⟩
    calc
      _ ≤ E * (3*u^2) := hg.trans (mul_le_mul_of_nonneg_left hw hE.le)
      _ = (3*E)*u^2 := by ring
      _ ≤ K*u^2 := mul_le_mul_of_nonneg_right hOE (sq_nonneg _)
  have half (x y : ℝ) (hx : x ∈ Icc (1/2 : ℝ) 2) (hy : y ∈ ({A,B} : Set ℝ)) :
      regularBound Λ(χ) ⟨x,y⟩ ((3*G+H)*u^2) := by
    have hf := hfinite y hy x hx
    have hx0 : 0 < x := (by norm_num : (0:ℝ) < 1/2).trans_le hx.1
    obtain ⟨ho, hd⟩ := completed_regular_product χ L hL hSeries (s := ⟨x,y⟩) hx0 hf.1
    have hxR : |x| ≤ R := by rw [abs_of_pos hx0]; exact hx.2.trans hR
    have hw := log_bound_on_box (z := ⟨x,y⟩) hu hxR (hya y (hyi y hy))
    have hg := hgamma ⟨x,y⟩ hx.1
    refine ⟨ho, ?_⟩
    rw [hd]
    calc
      _ ≤ ‖logDeriv (heckeGammaFactor χ) ⟨x,y⟩‖ + ‖logDeriv L ⟨x,y⟩‖ := norm_add_le _ _
      _ ≤ G*(3*u^2) + H*u^2 := add_le_add (hg.trans (mul_le_mul_of_nonneg_left hw hG.le)) hf.2
      _ = (3*G+H)*u^2 := by ring
  apply of_bound_on_edges (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)
    (mul_nonneg (le_trans (by positivity : 0 ≤ 3*E) hOE) (sq_nonneg _))
  · intro x hx y hy
    by_cases he : x ≤ -1 ∨ 2 ≤ x
    · exact outside x y (abs_le.mpr hx) (hyi y hy) he
    push Not at he
    by_cases hr : 1/2 ≤ x
    · have hh := half x y ⟨hr, he.2.le⟩ hy
      have hle : 3*G+H ≤ K := (le_add_of_nonneg_right (norm_nonneg Q(χ))).trans hMID
      exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _))⟩
    · let z : ℂ := ⟨1-x, y⟩
      have hh := half (1-x) y ⟨by linarith, by linarith [he.1]⟩ hy
      have hm : 1 - conj z = (⟨x,y⟩ : ℂ) := by apply Complex.ext <;> simp [z]
      change regularBound Λ(χ) ⟨x,y⟩ (K*u^2)
      rw [← hm]
      refine ⟨reflected_order_zero χ hh.1, ?_⟩
      rw [completed_logDeriv_reflection_regular χ z hh.1]
      calc
        _ ≤ ‖logDeriv Λ(χ) z‖ + D := by
          simpa only [norm_neg, Complex.norm_conj] using norm_sub_le (-conj (logDeriv Λ(χ) z)) Q(χ)
        _ ≤ (3*G+H)*u^2 + D*u^2 := add_le_add hh.2 (le_mul_of_one_le_right (norm_nonneg _) hu2)
        _ = (3*G+H+D)*u^2 := (add_mul _ _ _).symm
        _ ≤ K*u^2 := mul_le_mul_of_nonneg_right hMID (sq_nonneg _)
  · intro y hy x hx
    rcases (show x = -R ∨ x=R by simpa only [mem_insert_iff, mem_singleton_iff] using hx) with he | he
    · rw [he]
      exact outside (-R) y (by rw [abs_neg, abs_of_nonneg hR0]) hy (Or.inl (by linarith))
    · rw [he]
      exact outside R y (by rw [abs_of_nonneg hR0]) hy (Or.inr hR)

/-- In every signed height window choose an interior ordinate. At all sufficiently large
integer widths both chosen horizontal edges, together with the two verticals, are regular
for the raw completed logarithmic derivative and have a common squared-logarithmic bound. -/
theorem exists_strict_log_sq_regularHeckeBoxes (χ : U𝔽) :
    ∃ A B : ℕ → ℝ, ∃ K > (0 : ℝ),
      (∀ n : ℕ, A n ∈ Ioo (-(n : ℝ)-1) (-(n : ℝ)) ∧ B n ∈ Ioo (n : ℝ) ((n : ℝ)+1)) ∧
      ∀ᶠ n : ℕ in atTop, RegularLogDerivBox Λ(χ) n (A n) (B n) (K * Real.log ((n : ℝ)+3)^2) := by
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨H, hH, J, _, hselect⟩ :=
    finiteHeckeL_continuation_exists_horizontal_logDeriv_le_log_sq χ L hL hSeries
  have pick (j : ℝ) : ∃ t ∈ Ioo j (j+1), J ≤ |j| →
      ∀ x ∈ Icc (1/2 : ℝ) 2, L ⟨x,t⟩ ≠ 0 ∧ ‖logDeriv L ⟨x,t⟩‖ ≤ H * Real.log (2+|j|)^2 := by
    by_cases hj : J ≤ |j|
    · obtain ⟨t, ht, _, hseg⟩ := hselect j hj
      exact ⟨t, ht, fun _ x hx ↦ (hseg x hx).2⟩
    · exact ⟨j+1/2, ⟨by linarith, by linarith⟩, fun h ↦ (hj h).elim⟩
  choose t ht hgood using pick
  let A (n : ℕ) := t (-(n : ℝ)-1)
  let B (n : ℕ) := t (n : ℝ)
  have ha (n : ℕ) : A n ∈ Ioo (-(n : ℝ)-1) (-(n : ℝ)) := by
    simpa only [A, sub_add_cancel] using ht (-(n : ℝ)-1)
  have hb (n : ℕ) : B n ∈ Ioo (n : ℝ) ((n : ℝ)+1) := ht n
  obtain ⟨E, hE, he⟩ := raw_outer χ
  obtain ⟨G, hG, hg⟩ := heckeGammaFactor_logDeriv_bound_of_re_ge χ (1/2) (by norm_num)
  let K := boundaryConstant E G H ‖Q(χ)‖
  have hK : 0 < K := (by positivity : 0 < 3*E).trans_le (le_max_left _ _)
  refine ⟨A, B, K, hK, fun n ↦ ⟨ha n, hb n⟩, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop J,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 : ℝ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1)] with n hnJ hn hexp
  have hu : 1 ≤ Real.log ((n : ℝ)+3) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (n : ℝ)+3)
  apply box_of_good_segments χ L hL hSeries hE hG hn hu (ha n) (hb n) he hg
  have line (j : ℝ) (hj : J ≤ |j|) (hj' : 2+|j| ≤ (n : ℝ)+3) (x : ℝ) (hx : x ∈ Icc (1/2 : ℝ) 2) :
      L ⟨x,t j⟩ ≠ 0 ∧ ‖logDeriv L ⟨x,t j⟩‖ ≤ H * Real.log ((n : ℝ)+3)^2 := by
    have hm := hgood j hj x hx
    have hnon : 0 ≤ Real.log (2+|j|) := Real.log_nonneg (by linarith [abs_nonneg j])
    have hlog := Real.log_le_log (by positivity) hj'
    exact ⟨hm.1, hm.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hlog 2) hH.le)⟩
  intro y hy x hx
  rcases (show y = A n ∨ y = B n by simpa only [mem_insert_iff, mem_singleton_iff] using hy) with rfl | rfl
  · have hneg : |-(n : ℝ)-1| = (n : ℝ)+1 := by
      rw [abs_of_nonpos (by linarith : -(n : ℝ)-1 ≤ 0)]
      ring
    exact line (-(n : ℝ)-1) (by rw [hneg]; linarith) (by rw [hneg]; linarith) x hx
  · exact line n (by rw [abs_of_nonneg (Nat.cast_nonneg n)]; exact hnJ)
      (by rw [abs_of_nonneg (Nat.cast_nonneg n)]; linarith) x hx

/-- The raw completed continuation of every unitary idèle class character has regular
rectangles with sublinear boundary bounds at integer widths. -/
theorem exists_sublinear_regularHeckeBoxes (χ : U𝔽) :
    ∃ A B M : ℕ → ℝ,
      (∀ᶠ n : ℕ in atTop, RegularLogDerivBox (continuedCompletedHeckeL χ) n (A n) (B n) (M n)) ∧
      Tendsto (fun n : ℕ ↦ M n / n) atTop (𝓝 0) := by
  obtain ⟨A, B, K, _, _, hboxes⟩ := exists_strict_log_sq_regularHeckeBoxes χ
  exact ⟨A, B, fun n ↦ K * Real.log ((n : ℝ)+3)^2, hboxes, tendsto_log_sq_height_div K⟩

end RiemannMasullo.ResolventRectangle
