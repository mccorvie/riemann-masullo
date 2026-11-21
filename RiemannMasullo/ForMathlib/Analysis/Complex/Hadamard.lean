module

public import Mathlib.Analysis.Complex.Hadamard

/-! # Polynomial growth and the Hadamard three-lines theorem -/

public section

open Filter Function Set
open scoped Asymptotics Topology

namespace RiemannMasullo

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- A polynomial growth bound on a closed strip extends to all heights by continuity. -/
private theorem norm_le_rpow_on_closedStrip {f : ℂ → ℂ} {l u k : ℝ} (hk : 0 ≤ k)
    (hf : ContinuousOn f (Complex.re ⁻¹' Icc l u))
    (h : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc l u)] fun z ↦ |z.im| ^ k) :
    ∃ C > (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc l u → ‖f z‖ ≤ C * (1 + |z.im|) ^ k := by
  obtain ⟨C, hC, h⟩ := Asymptotics.isBigO_iff'.mp h
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h
  obtain ⟨T, hT⟩ := h
  let K := Metric.closedBall (0 : ℂ) (|l| + |u| + T) ∩ Complex.re ⁻¹' Icc l u
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_Icc.preimage Complex.continuous_re)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hf.norm.mono inter_subset_right)
  refine ⟨max C M, hC.trans_le (le_max_left ..), fun z hz ↦ ?_⟩
  have hbase : 1 ≤ 1 + |z.im| := le_add_of_nonneg_right (abs_nonneg _)
  by_cases ht : T ≤ |z.im|
  · have hb := hT _ ht z rfl hz
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hb
    exact hb.trans (mul_le_mul (le_max_left ..)
      (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hk)
      (Real.rpow_nonneg (abs_nonneg _) _) (hC.le.trans (le_max_left ..)))
  · have hzK : z ∈ K := by
      refine ⟨?_, hz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hre : |z.re| ≤ |l| + |u| :=
        abs_le.mpr ⟨by linarith [hz.1, neg_abs_le l, abs_nonneg u],
          by linarith [hz.2, le_abs_self u, abs_nonneg l]⟩
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    have hM' : ‖f z‖ ≤ M := hM (mem_image_of_mem (norm ∘ f) hzK)
    calc
      ‖f z‖ ≤ max C M := hM'.trans (le_max_right ..)
      _ ≤ _ := le_mul_of_one_le_right (hC.le.trans (le_max_left ..))
        (Real.one_le_rpow hbase hk)

/-- Nonnegative polynomial growth exponents on the two edges of a vertical strip
interpolate linearly at each interior real part under a uniform polynomial bound. -/
theorem isBigO_rpow_verticalStrip_interpolate {f : ℂ → ℂ} {l u K k₀ k₁ p q : ℝ}
    (hlu : l < u) (hK : 0 ≤ K) (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Icc l u))
    (h : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc l u)] fun z ↦ |z.im| ^ K)
    (h₀ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {l})] fun z ↦ |z.im| ^ k₀)
    (h₁ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})] fun z ↦ |z.im| ^ k₁) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {p * l + q * u})]
      fun z ↦ |z.im| ^ (p * k₀ + q * k₁) := by
  obtain ⟨C, hC, hStrip⟩ := norm_le_rpow_on_closedStrip hK hf.continuousOn h
  obtain ⟨C₀, hC₀, hLeft⟩ := norm_le_rpow_on_closedStrip hk₀
    (hf.continuousOn.mono (preimage_mono (Icc_subset_Icc_right hlu.le))) (by simpa using h₀)
  obtain ⟨C₁, hC₁, hRight⟩ := norm_le_rpow_on_closedStrip hk₁
    (hf.continuousOn.mono (preimage_mono (Icc_subset_Icc_left hlu.le))) (by simpa using h₁)
  obtain ⟨n, hn⟩ := exists_nat_ge (max K (max k₀ k₁))
  have hnK : K ≤ (n : ℝ) := (le_max_left ..).trans hn
  have hn₀ : k₀ ≤ (n : ℝ) := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hn₁ : k₁ ≤ (n : ℝ) := (le_max_right ..).trans ((le_max_right ..).trans hn)
  let k := p * k₀ + q * k₁
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  refine Asymptotics.IsBigO.of_bound
    ((1 + (u - l)) ^ n * ((C₀ * 2 ^ k₀) ^ p * (C₁ * 2 ^ k₁) ^ q) * 2 ^ k) ?_
  rw [eventually_inf_principal]
  filter_upwards [hHeight.eventually_ge_atTop 1] with z hzHeight hz
  have hzRe : z.re = p * l + q * u := hz
  have hzIcc : z.re ∈ Icc l u := by
    rw [hzRe]
    constructor
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr hlu.le), congrArg (fun x : ℝ ↦ x * l) hpq]
    · nlinarith [mul_nonneg hp (sub_nonneg.mpr hlu.le), congrArg (fun x : ℝ ↦ x * u) hpq]
  let R := 1 + |z.im|
  let S := R + (u - l)
  let d := fun w : ℂ ↦ (S : ℂ) + (w - z)
  let F := fun w : ℂ ↦ f w * ((R : ℂ) / d w) ^ n
  have hR : 1 ≤ R := le_add_of_nonneg_right (abs_nonneg _)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hS : 0 < S := add_pos hRpos (sub_pos.mpr hlu)
  have hD (w : ℂ) (hw : w.re ∈ Icc l u) : R ≤ ‖d w‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    dsimp [d, S]
    linarith [hw.1, hzIcc.2]
  have hDpos (w : ℂ) (hw : w.re ∈ Icc l u) : 0 < ‖d w‖ := hRpos.trans_le (hD w hw)
  have hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc l u) :=
    hf.mul (((differentiableOn_const (c := (R : ℂ))).div (by dsimp [d]; fun_prop)
      (fun w hw ↦ norm_pos_iff.mp (hDpos w hw))).pow n)
  -- A rational factor centered at the ordinate of z absorbs all three polynomial bounds.
  have hBound (m A : ℝ) (hm : 0 ≤ m) (hmn : m ≤ n) (hA : 0 ≤ A)
      (w : ℂ) (hw : w.re ∈ Icc l u) (hwf : ‖f w‖ ≤ A * (1 + |w.im|) ^ m) :
      ‖F w‖ ≤ (A * 2 ^ m) * R ^ m := by
    let D := ‖d w‖
    have hD' : R ≤ D := hD w hw
    have hD₀ : 0 < D := hDpos w hw
    have hin : 1 + |w.im| ≤ 2 * D := by
      have him : |w.im - z.im| ≤ D := by
        simpa [D, d] using Complex.abs_im_le_norm (d w)
      have ht : |w.im| ≤ |w.im - z.im| + |z.im| := by
        simpa using abs_add_le (w.im - z.im) z.im
      dsimp [R] at hD'
      linarith
    have hratio : 1 ≤ D / R := (one_le_div hRpos).2 hD'
    have hpow : (D / R) ^ m ≤ (D / R) ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hratio hmn
    have hcancel : D ^ m * (R / D) ^ n ≤ R ^ m := by
      rw [← inv_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      rw [Real.div_rpow hD₀.le hRpos.le] at hpow
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hRpos _)).mp hpow |>.trans_eq (mul_comm ..)
    simp only [F, norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
    change ‖f w‖ * (R / D) ^ n ≤ _
    calc
      _ ≤ (A * (2 * D) ^ m) * (R / D) ^ n :=
        mul_le_mul_of_nonneg_right
          (hwf.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hin hm) hA))
          (by positivity)
      _ = (A * 2 ^ m) * (D ^ m * (R / D) ^ n) := by
        rw [Real.mul_rpow (by norm_num) hD₀.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcancel (by positivity)
  have hFstrip : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip l u) := by
    apply DifferentiableOn.diffContOnCl
    simpa only [Complex.HadamardThreeLines.verticalStrip, Complex.closure_preimage_re,
      closure_Ioo hlu.ne] using hF
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨(C * 2 ^ K) * R ^ K, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hBound K C hK hnK hC.le w hw (hStrip w hw)
  have hL (w : ℂ) (hw : w ∈ Complex.re ⁻¹' {l}) : ‖F w‖ ≤ (C₀ * 2 ^ k₀) * R ^ k₀ := by
    have hw' : w.re = l := hw
    exact hBound k₀ C₀ hk₀ hn₀ hC₀.le w (by simpa [hw'] using hlu.le)
      (hLeft w (by simp [hw']))
  have hU (w : ℂ) (hw : w ∈ Complex.re ⁻¹' {u}) : ‖F w‖ ≤ (C₁ * 2 ^ k₁) * R ^ k₁ := by
    have hw' : w.re = u := hw
    exact hBound k₁ C₁ hk₁ hn₁ hC₁.le w (by simpa [hw'] using hlu.le)
      (hRight w (by simp [hw']))
  have hInterp := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlu hzIcc hFstrip hB hL hU
  have hq' : (z.re - l) / (u - l) = q := by
    rw [div_eq_iff (sub_ne_zero.mpr hlu.ne.symm), hzRe]
    nlinarith [congrArg (fun x : ℝ ↦ x * l) hpq]
  rw [hq', show 1 - q = p by linarith,
    Real.mul_rpow (show 0 ≤ C₀ * 2 ^ k₀ by positivity) (show 0 ≤ R ^ k₀ by positivity),
    Real.mul_rpow (show 0 ≤ C₁ * 2 ^ k₁ by positivity) (show 0 ≤ R ^ k₁ by positivity),
    ← Real.rpow_mul hRpos.le, ← Real.rpow_mul hRpos.le] at hInterp
  have hInterp' : ‖F z‖ ≤ ((C₀ * 2 ^ k₀) ^ p * (C₁ * 2 ^ k₁) ^ q) * R ^ k := by
    convert hInterp using 1
    dsimp [k]
    rw [Real.rpow_add hRpos, mul_comm p k₀, mul_comm q k₁]
    ring
  have hSz : S ≤ (1 + (u - l)) * R := by
    dsimp [S]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlu.le) (sub_nonneg.mpr hR)]
  have hfactor : (S / R) ^ n ≤ (1 + (u - l)) ^ n := by
    gcongr
    exact (div_le_iff₀ hRpos).2 hSz
  have hRk : R ^ k ≤ 2 ^ k * |z.im| ^ k := by
    rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
    exact Real.rpow_le_rpow hRpos.le (by dsimp [R]; linarith) hk
  have hFz : ‖f z‖ = ‖F z‖ * (S / R) ^ n := by
    simp only [F, d, sub_self, add_zero, norm_mul, norm_pow, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hRpos.le, Real.norm_of_nonneg hS.le, mul_assoc, ← mul_pow]
    rw [div_mul_div_cancel₀ hS.ne', div_self hRpos.ne', one_pow, mul_one]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hFz]
  calc
    _ ≤ (((C₀ * 2 ^ k₀) ^ p * (C₁ * 2 ^ k₁) ^ q) * (2 ^ k * |z.im| ^ k)) *
        (1 + (u - l)) ^ n := by
      exact mul_le_mul (hInterp'.trans (mul_le_mul_of_nonneg_left hRk (by positivity)))
        hfactor (by positivity) (by positivity)
    _ = _ := by ring

end RiemannMasullo
