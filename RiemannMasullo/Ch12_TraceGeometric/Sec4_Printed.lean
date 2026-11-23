module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-! # Printed cutoff claims in §12.4 -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Padic SchwartzMap

namespace RiemannMasullo

/-- Paper: Step II, p. 516. In the model F = ℚ with only the real place, the
printed spatial multiplier sends all Schwartz functions to the flat subspace.
Deviation: State this specialization with a smooth even profile, a unit plateau,
and support in the closed outer ball. -/
def Printed.sLocalSpatialCutoff_realFlatRange : Prop :=
  ∀ (L ε : ℝ), 0 < ε → ε < L →
    ∀ (ρ : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → (∀ x, ρ (-x) = ρ x) →
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1) → tsupport ρ ⊆ Icc (-L) L →
      EqOn ρ 1 (Icc (-(L - ε)) (L - ε)) →
      ∀ f : 𝓢(ℝ, ℂ), ∃ h : 𝓢(ℝ, ℂ), h ∈ realSchwartzFlatAtOrigin ∧
        ∀ x : ℝ, h x = (ρ x : ℂ) * f x

/-- Paper: Step II, p. 516. Take outer radius two, transition width one,
a smooth even cutoff equal to one on [−1,1], and the Gaussian exp(−x²).
The product has value one at zero, so it fails even the zeroth flatness condition. -/
theorem Printed.sLocalSpatialCutoff_realFlatRange_false :
    ¬ Printed.sLocalSpatialCutoff_realFlatRange := by
  intro hall
  let B : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let f : 𝓢(ℝ, ℂ) := (B.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  have hout : tsupport B ⊆ Icc (-2 : ℝ) 2 := by
    rw [B.tsupport_eq, Real.closedBall_eq_Icc]
    simp [B]
  have hin : EqOn (B : ℝ → ℝ) 1 (Icc (-(2 - 1)) (2 - 1)) := by
    intro x hx
    apply B.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    change 0 - 1 ≤ x ∧ x ≤ 0 + 1
    obtain ⟨hl, hr⟩ := hx
    constructor <;> linarith
  obtain ⟨g, hg, he⟩ := hall 2 1 (by norm_num) (by norm_num) B B.contDiff B.neg
    (fun _ ↦ ⟨B.nonneg, B.le_one⟩) hout hin f
  have h0 := (mem_realSchwartzFlatAtOrigin_iff g).mp hg 0
  have hb : B 0 = 1 := B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)
  have hf : f 0 = 1 := by change (B 0 : ℂ) = 1; rw [hb, Complex.ofReal_one]
  simp [iteratedDeriv_zero, he 0, hb, hf] at h0

local notation "adelicModel" => Multiplicative (ℝ × ℚ_[2])

/-- Paper: Step II, pp. 516–517. In the model F = ℚ, S = {∞, 2}, the
product-norm cutoff is used to multiply the additive Schwartz–Bruhat space into itself.
Deviation: State the multiplication claim for this model and for smooth real
profiles with a unit plateau and a finite outer radius. -/
def Printed.sLocalProductCutoff_preservesSchwartzBruhat : Prop :=
  ∀ (L ε : ℝ), 0 < ε → ε < L →
    ∀ (ρ : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) →
      (∀ t ≥ L, ρ t = 0) → EqOn ρ 1 (Icc 0 (L - ε)) →
      ∀ f : SchwartzBruhat adelicModel,
        (fun x : adelicModel ↦ (ρ (‖x.toAdd.1‖ * ‖x.toAdd.2‖) : ℂ) * f x) ∈
          schwartzBruhatSubmodule (G := adelicModel)

/-- Paper: Step II, pp. 516–517. Take the product of exp(−x²) and the indicator
of ℤ₂, with a smooth profile equal to one up to radius one and zero from radius two.
For every n choose h = 2ⁿ and x = 2ⁿ⁺². The product is nonzero at (x,0) and
zero at (x,h). No common open subgroup of translations in ℚ₂ fixes the product. -/
theorem Printed.sLocalProductCutoff_preservesSchwartzBruhat_false :
    ¬ Printed.sLocalProductCutoff_preservesSchwartzBruhat := by sorry

/-- Paper: (12.4.1.22), p. 518. The smoothed identity orbital mass is set
equal to the integral over the two sharp intervals.
Deviation: State the real part in the rational real model for lifts supported
on the positive reals. The positive half-line is the S-unit fundamental domain. -/
def Printed.sLocalSmoothMass_eq_sharp_real : Prop :=
  ∀ (L L' ε : ℝ), 0 < ε → ε < L → ε < L' →
    ∀ (ρ σ f : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → ContDiff ℝ (∞ : ℕ∞ω) σ →
      (∀ x, ρ (-x) = ρ x ∧ σ (-x) = σ x) →
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1 ∧ 0 ≤ σ x ∧ σ x ≤ 1) →
      tsupport ρ ⊆ Icc (-L) L → tsupport σ ⊆ Icc (-L') L' →
      EqOn ρ 1 (Icc (-(L - ε)) (L - ε)) → EqOn σ 1 (Icc (-(L' - ε)) (L' - ε)) →
      ContDiff ℝ (∞ : ℕ∞ω) f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
      let m := fun x u : ℝ ↦ ∫ g in Ioi (0 : ℝ),
        f g / (g * Real.sqrt g) * Real.cos (2 * Real.pi * (g⁻¹ - 1) * x * u)
      (∫ x in Ioi (0 : ℝ), ρ x * ∫ u : ℝ, σ u * m x u) =
        ∫ x in Ioc (0 : ℝ) L, ∫ u in Icc (-L') L', m x u

/-- A continuous function, nonnegative on a nondegenerate closed interval and positive at one
of its points, has positive integral over the interval. -/
private theorem Printed.sLocalSmoothMass_eq_sharp_real_false_pos (g : ℝ → ℝ) (hg : Continuous g)
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b) (h0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hpos : 0 < g c) : 0 < ∫ x in Icc a b, g x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Icc h0)
    hg.integrableOn_Icc]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hg.isOpen_support c (ne_of_gt hpos)
  have hlr : max a (c - ε) < min b (c + ε) :=
    max_lt (lt_min hab (by linarith [hc.1])) (lt_min (by linarith [hc.2]) (by linarith))
  have hsub : Ioo (max a (c - ε)) (min b (c + ε)) ⊆ Function.support g ∩ Icc a b := by
    intro x hx
    refine ⟨hball ?_, ?_, ?_⟩
    · rw [Real.ball_eq_Ioo]
      exact ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
    · exact (lt_of_le_of_lt (le_max_left _ _) hx.1).le
    · exact (lt_of_lt_of_le hx.2 (min_le_left _ _)).le
  calc (0 : ENNReal) < volume (Ioo (max a (c - ε)) (min b (c + ε))) := by
        rw [Real.volume_Ioo]; simpa using hlr
    _ ≤ _ := measure_mono hsub

/-- The comparison of the smooth and sharp masses for an abstract kernel that is continuous,
nonnegative on the square and positive on the edge x = 1, and a cutoff vanishing off (−1, 1). -/
private theorem Printed.sLocalSmoothMass_eq_sharp_real_false_lt (Φ : ℝ → ℝ → ℝ)
    (hΦ : Continuous (Function.uncurry Φ))
    (hΦ0 : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ Φ x u)
    (hΦ1 : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < Φ 1 u)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hρ01 : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1)
    (hρout : ∀ x, x ∉ Ioo (-1 : ℝ) 1 → ρ x = 0) :
    (∫ x in Ioi (0 : ℝ), ρ x * ∫ u, ρ u * Φ x u) <
      ∫ x in Ioc (0 : ℝ) 1, ∫ u in Icc (-1 : ℝ) 1, Φ x u := by
  let s : ℝ → ℝ := fun x ↦ ∫ u in Icc (-1 : ℝ) 1, ρ u * Φ x u
  let t : ℝ → ℝ := fun x ↦ ∫ u in Icc (-1 : ℝ) 1, Φ x u
  have hs_eq (x : ℝ) : (∫ u, ρ u * Φ x u) = s x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu ↦ by
      rw [hρout u (fun h ↦ hu (Ioo_subset_Icc_self h)), zero_mul]).symm
  have hs_cont : Continuous s := continuous_parametric_integral_of_continuous
    ((hρ.comp continuous_snd).mul hΦ) isCompact_Icc
  have ht_cont : Continuous t := continuous_parametric_integral_of_continuous hΦ isCompact_Icc
  have hΦx (x : ℝ) : Continuous (Φ x) := hΦ.comp (Continuous.prodMk_right x)
  have hst (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ s x ∧ s x ≤ t x := by
    refine ⟨setIntegral_nonneg measurableSet_Icc fun u hu ↦
      mul_nonneg (hρ01 u).1 (hΦ0 x hx u hu), ?_⟩
    exact setIntegral_mono_on ((hρ.mul (hΦx x)).integrableOn_Icc) (hΦx x).integrableOn_Icc
      measurableSet_Icc fun u hu ↦ mul_le_of_le_one_left (hΦ0 x hx u hu) (hρ01 u).2
  have hL : (∫ x in Ioi (0 : ℝ), ρ x * ∫ u, ρ u * Φ x u) = ∫ x in Icc (0 : ℝ) 1, ρ x * s x := by
    simp_rw [hs_eq]
    rw [integral_Icc_eq_integral_Ioc]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self fun x hx ↦ ?_)
    rw [hρout x fun h ↦ hx.2 ⟨hx.1, h.2.le⟩, zero_mul]
  have hR : (∫ x in Ioc (0 : ℝ) 1, ∫ u in Icc (-1 : ℝ) 1, Φ x u) = ∫ x in Icc (0 : ℝ) 1, t x :=
    integral_Icc_eq_integral_Ioc.symm
  have hρs : Continuous fun x ↦ ρ x * s x := hρ.mul hs_cont
  rw [hL, hR, ← sub_pos, ← integral_sub ht_cont.integrableOn_Icc hρs.integrableOn_Icc]
  refine Printed.sLocalSmoothMass_eq_sharp_real_false_pos _ (ht_cont.sub hρs)
    zero_lt_one (right_mem_Icc.mpr zero_le_one) (fun x hx ↦ ?_) ?_
  · have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    obtain ⟨h0, h1⟩ := hst x hx'
    exact sub_nonneg.mpr ((mul_le_of_le_one_left h0 (hρ01 x).2).trans h1)
  · change 0 < t 1 - ρ 1 * s 1
    rw [hρout 1 fun h ↦ lt_irrefl _ h.2, zero_mul, sub_zero]
    exact Printed.sLocalSmoothMass_eq_sharp_real_false_pos _ (hΦx 1) (by norm_num : (-1 : ℝ) < 1)
      (right_mem_Icc.mpr (by norm_num)) (fun u hu ↦ (hΦ1 u hu).le) (hΦ1 1 ⟨by norm_num, le_rfl⟩)


/-- For a log-norm parameter near one and coordinates in the unit square, the cosine
in the orbital mass is positive. -/
private theorem Printed.sLocalSmoothMass_eq_sharp_real_false_cos {g x u : ℝ}
    (hg : g ∈ Icc (15 / 16 : ℝ) (17 / 16)) (hx : x ∈ Icc (-1 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1) :
    0 < Real.cos (2 * Real.pi * (g⁻¹ - 1) * x * u) := by
  have hg0 : 0 < g := by linarith [hg.1]
  have h1 : g⁻¹ ≤ 16 / 15 := by
    rw [inv_le_comm₀ hg0 (by norm_num)]; linarith [hg.1]
  have h2 : 16 / 17 ≤ g⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hg0]; linarith [hg.2]
  have hv : |g⁻¹ - 1| ≤ 1 / 15 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hxu : |(g⁻¹ - 1) * x * u| ≤ 1 / 15 := by
    rw [abs_mul, abs_mul]
    calc |g⁻¹ - 1| * |x| * |u| ≤ 1 / 15 * 1 * 1 := by
          gcongr
          · exact abs_le.mpr hx
          · exact abs_le.mpr hu
      _ = 1 / 15 := by norm_num
  have hθ : 2 * Real.pi * (g⁻¹ - 1) * x * u = 2 * Real.pi * ((g⁻¹ - 1) * x * u) := by ring
  rw [hθ]
  obtain ⟨hl, hr⟩ := abs_le.mp hxu
  have hπ := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith

/-- Paper: (12.4.1.22), p. 518. Set both radii to one and the width to one half.
Use smooth even cutoffs that taper from one to zero on (1/2,1) and a nonzero
nonnegative smooth lift supported in (15/16,17/16). The cosine is strictly
positive on the sharp integration region, so tapering strictly decreases the mass. -/
theorem Printed.sLocalSmoothMass_eq_sharp_real_false :
    ¬ Printed.sLocalSmoothMass_eq_sharp_real := by
  intro hall
  let B : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let B' : ContDiffBump (1 : ℝ) := ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩
  have hBout (x : ℝ) (hx : x ∉ Ioo (-1 : ℝ) 1) : B x = 0 := by
    apply Function.notMem_support.mp
    rw [B.support_eq, Real.ball_eq_Ioo]
    simpa [B] using hx
  have hB'out (g : ℝ) (hg : g ∉ Icc (15 / 16 : ℝ) (17 / 16)) : B' g = 0 := by
    apply Function.notMem_support.mp
    rw [B'.support_eq, Real.ball_eq_Ioo]
    intro h
    apply hg
    simp only [B'] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hout : tsupport B ⊆ Icc (-1 : ℝ) 1 := by
    rw [B.tsupport_eq, Real.closedBall_eq_Icc]
    simp [B]
  have hin : EqOn (B : ℝ → ℝ) 1 (Icc (-(1 - 1 / 2)) (1 - 1 / 2)) := by
    intro x hx
    apply B.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    change 0 - 1 / 2 ≤ x ∧ x ≤ 0 + 1 / 2
    obtain ⟨hl, hr⟩ := hx
    constructor <;> linarith
  have hfsupp : tsupport B' ⊆ Ioi 0 := by
    rw [B'.tsupport_eq, Real.closedBall_eq_Icc]
    intro g hg
    simp only [B', mem_Icc] at hg
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 - 1 / 16) hg.1
  have h := hall 1 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) B B B'
    B.contDiff B.contDiff (fun x ↦ ⟨B.neg x, B.neg x⟩)
    (fun _ ↦ ⟨B.nonneg, B.le_one, B.nonneg, B.le_one⟩) hout hout hin hin B'.contDiff
    B'.hasCompactSupport hfsupp
  -- the kernel, with a weight that is continuous on all of ℝ
  let G : ℝ → ℝ := fun g ↦ max g (1 / 2)
  have hG : Continuous G := continuous_id.max continuous_const
  have hG0 (g : ℝ) : 0 < G g := lt_of_lt_of_le (by norm_num) (le_max_right g (1 / 2))
  let F : ℝ × ℝ → ℝ → ℝ := fun p g ↦ B' g / (G g * Real.sqrt (G g)) *
    Real.cos (2 * Real.pi * ((G g)⁻¹ - 1) * p.1 * p.2)
  have hF : Continuous (Function.uncurry F) := by
    have hw : Continuous fun g ↦ B' g / (G g * Real.sqrt (G g)) :=
      B'.continuous.div (hG.mul hG.sqrt) fun g ↦
        (mul_pos (hG0 g) (Real.sqrt_pos.mpr (hG0 g))).ne'
    have hv : Continuous fun g ↦ (G g)⁻¹ - 1 := (hG.inv₀ fun g ↦ (hG0 g).ne').sub continuous_const
    exact (hw.comp continuous_snd).mul (Real.continuous_cos.comp
      ((((continuous_const.mul (hv.comp continuous_snd)).mul
        (continuous_fst.comp continuous_fst))).mul (continuous_snd.comp continuous_fst)))
  let Φ : ℝ → ℝ → ℝ := fun x u ↦ ∫ g in Icc (15 / 16 : ℝ) (17 / 16), F (x, u) g
  have hm (x u : ℝ) : (∫ g in Ioi (0 : ℝ),
      B' g / (g * Real.sqrt g) * Real.cos (2 * Real.pi * (g⁻¹ - 1) * x * u)) = Φ x u := by
    have hsub : Icc (15 / 16 : ℝ) (17 / 16) ⊆ Ioi 0 :=
      fun g hg ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 16) hg.1
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      fun g hg ↦ ?_).trans ?_
    · rw [hB'out g hg.2, zero_div, zero_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun g hg ↦ ?_
    have : G g = g := max_eq_left (by linarith [hg.1])
    simp only [F, this]
  have hΦ : Continuous (Function.uncurry Φ) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  have hFpos (x u : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1) (g : ℝ)
      (hg : g ∈ Icc (15 / 16 : ℝ) (17 / 16)) : 0 ≤ F (x, u) g := by
    have : G g = g := max_eq_left (by linarith [hg.1])
    simp only [F, this]
    have hg0 : 0 < g := by linarith [hg.1]
    exact mul_nonneg (div_nonneg B'.nonneg (mul_pos hg0 (Real.sqrt_pos.mpr hg0)).le)
      (Printed.sLocalSmoothMass_eq_sharp_real_false_cos hg hx hu).le
  have hΦ0 (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      0 ≤ Φ x u := setIntegral_nonneg measurableSet_Icc (hFpos x u hx hu)
  have hΦ1 (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : 0 < Φ 1 u := by
    refine Printed.sLocalSmoothMass_eq_sharp_real_false_pos _
      (hF.comp (Continuous.prodMk_right (1, u))) (by norm_num) (c := 1) ⟨by norm_num, by norm_num⟩
      (hFpos 1 u ⟨by norm_num, le_rfl⟩ hu) ?_
    have h1 : B' 1 = 1 := B'.one_of_mem_closedBall (Metric.mem_closedBall_self B'.rIn_pos.le)
    have hG1 : G 1 = 1 := max_eq_left (by norm_num)
    simp [F, hG1, h1]
  have hlt := Printed.sLocalSmoothMass_eq_sharp_real_false_lt Φ hΦ hΦ0 hΦ1 B B.continuous
    (fun _ ↦ ⟨B.nonneg, B.le_one⟩) hBout
  simp only [hm] at h
  exact (ne_of_lt hlt) h

end RiemannMasullo
