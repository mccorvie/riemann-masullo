module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Signed Abel means on the positive half-line

A pointwise lower bound on a tail controls the lower Abel limit. When a full Abel
mean tends to zero, subtracting the lower-bounded contribution gives a negative
upper limit for its signed complement.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.AbelEdge

open Filter MeasureTheory Set
open scoped Topology

/-- The real signed Abel mean on the positive half-line. -/
noncomputable def signedAbelMean (f : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ε * ∫ y in Ici (0 : ℝ), f y * Real.exp (-ε * y)

/-- A lower bound on the tail gives a uniform linear-in-damping error. The one fixed
damping `ε = 1` supplies the integrable majorant on the initial interval. -/
theorem signedAbelMean_lower_error {n : ℝ → ℝ} {δ : ℝ}
    (hn : ∀ ε > 0, IntegrableOn (fun y ↦ n y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hδ : ∀ᶠ y in atTop, δ ≤ n y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε > 0, δ - ε * M ≤ signedAbelMean n ε := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hδ
  let g (y : ℝ) := Real.exp Y * ((|n y| + |δ|) * Real.exp (-y))
  have habs : IntegrableOn (fun y ↦ |n y| * Real.exp (-y)) (Ici (0 : ℝ)) := by
    simpa only [IntegrableOn, neg_one_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      using (hn 1 zero_lt_one).norm
  have hk : IntegrableOn (fun y : ℝ ↦ Real.exp (-y)) (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (integrableOn_exp_neg_Ioi 0)
  have hg : IntegrableOn g (Ici (0 : ℝ)) := by
    simpa only [IntegrableOn, g, add_mul, Pi.add_apply] using
      (habs.add (hk.const_mul |δ|)).const_mul (Real.exp Y)
  have hg₀ (y : ℝ) : 0 ≤ g y := by dsimp [g]; positivity
  refine ⟨∫ y in Ici (0 : ℝ), g y, integral_nonneg hg₀, ?_⟩
  intro ε hε
  have hker : IntegrableOn (fun y : ℝ ↦ Real.exp (-ε * y)) (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0)
  have hpt (y : ℝ) (hy : 0 ≤ y) : (δ - n y) * Real.exp (-ε * y) ≤ g y := by
    by_cases h : Y ≤ y
    · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hY y h))
        (Real.exp_pos _).le).trans (hg₀ y)
    · have hsum : δ - n y ≤ |n y| + |δ| := by linarith [le_abs_self δ, neg_le_abs (n y)]
      have hfac : 1 ≤ Real.exp Y * Real.exp (-y) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      calc
        _ ≤ (|n y| + |δ|) * Real.exp (-ε * y) :=
          mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
        _ ≤ (|n y| + |δ|) * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hy)) (by positivity)
        _ ≤ (|n y| + |δ|) * (Real.exp Y * Real.exp (-y)) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = _ := by dsimp [g]; ring
  have hc := setIntegral_mono_on ((hker.const_mul δ).sub hg) (hn ε hε) measurableSet_Ici
    (fun y hy ↦ show δ * Real.exp (-ε * y) - g y ≤ n y * Real.exp (-ε * y) by
      have h := hpt y hy
      rwa [sub_mul, sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add] at h)
  simp only [Pi.sub_apply] at hc
  rw [integral_sub (hker.const_mul δ) hg] at hc
  have hunit : ε * (∫ y in Ici (0 : ℝ), δ * Real.exp (-ε * y)) = δ := by
    rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (neg_lt_zero.mpr hε)]
    simp [hε.ne', mul_comm ε]
  have hscaled := mul_le_mul_of_nonneg_left hc hε.le
  rw [mul_sub, hunit] at hscaled
  exact hscaled

/-- Every level strictly below an eventual pointwise lower bound is eventually a
strict lower bound for the Abel means as the positive damping tends to zero. -/
private theorem eventually_lt_signedAbelMean {n : ℝ → ℝ} {d δ : ℝ}
    (hn : ∀ ε > 0, IntegrableOn (fun y ↦ n y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hδ : ∀ᶠ y in atTop, δ ≤ n y) (hd : d < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), d < signedAbelMean n ε := by
  obtain ⟨M, _, hM⟩ := signedAbelMean_lower_error hn hδ
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun ε : ℝ ↦ δ - ε * M) (𝓝[>] 0) (𝓝 δ) := by
    simpa using (hid.mul_const M).const_sub δ
  filter_upwards [self_mem_nhdsWithin, hlim.eventually_const_lt hd] with ε hε hdε
  exact hdε.trans_le (hM ε hε)

/-- Linearity for an integrable signed difference at a fixed damping. -/
private theorem signedAbelMean_sub {t n : ℝ → ℝ} {ε : ℝ}
    (ht : IntegrableOn (fun y ↦ t y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hn : IntegrableOn (fun y ↦ n y * Real.exp (-ε * y)) (Ici (0 : ℝ))) :
    signedAbelMean (fun y ↦ t y - n y) ε = signedAbelMean t ε - signedAbelMean n ε := by
  simp only [signedAbelMean, sub_mul, integral_sub ht hn, mul_sub]

/-- If the full Abel mean tends to zero, the signed complement has extended-real
upper limit at most minus the tail lower bound. Integrability of the full mean is
required only for sufficiently small positive damping. -/
theorem limsup_signedAbelMean_sub_le {t n : ℝ → ℝ} {δ : ℝ}
    (hn : ∀ ε > 0, IntegrableOn (fun y ↦ n y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hδ : ∀ᶠ y in atTop, δ ≤ n y)
    (ht : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntegrableOn (fun y ↦ t y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hzero : Tendsto (signedAbelMean t) (𝓝[>] 0) (𝓝 0)) :
    limsup (fun ε ↦ (signedAbelMean (fun y ↦ t y - n y) ε : EReal)) (𝓝[>] 0) ≤ ((-δ : ℝ) : EReal) := by
  obtain ⟨M, _, hM⟩ := signedAbelMean_lower_error hn hδ
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun ε : ℝ ↦ signedAbelMean t ε - δ + ε * M) (𝓝[>] 0) (𝓝 (-δ)) := by
    simpa using (hzero.sub_const δ).add (hid.mul_const M)
  have hcoe := continuous_coe_real_ereal.continuousAt.tendsto.comp hu
  refine (limsup_le_limsup ?_).trans_eq hcoe.limsup_eq
  filter_upwards [ht, self_mem_nhdsWithin] with ε hεt (hε : 0 < ε)
  apply EReal.coe_le_coe_iff.mpr
  rw [signedAbelMean_sub hεt (hn ε hε)]
  linarith [hM ε hε]

/-- A pointwise lower limit also transfers to the Abel lower limit. -/
theorem le_liminf_signedAbelMean {n : ℝ → ℝ} {δ : ℝ}
    (hn : ∀ ε > 0, IntegrableOn (fun y ↦ n y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hδ : ∀ d < δ, ∀ᶠ y in atTop, d ≤ n y) :
    (δ : EReal) ≤ liminf (fun ε ↦ (signedAbelMean n ε : EReal)) (𝓝[>] 0) := by
  have he (d : ℝ) (hd : d < δ) :
      (d : EReal) ≤ liminf (fun ε ↦ (signedAbelMean n ε : EReal)) (𝓝[>] 0) := by
    obtain ⟨b, hdb, hbδ⟩ := exists_between hd
    exact le_liminf_of_le (h := (eventually_lt_signedAbelMean hn (hδ b hbδ) hdb).mono
      fun ε hε ↦ EReal.coe_le_coe_iff.mpr hε.le)
  have hu : Tendsto ((↑) : ℝ → EReal) (𝓝[<] δ) (𝓝 (δ : EReal)) :=
    continuous_coe_real_ereal.continuousWithinAt
  exact le_of_tendsto hu (eventually_of_mem self_mem_nhdsWithin fun d hd ↦ he d hd)

/-- A pointwise lower limit `δ` for the near contribution forces the full constant
`-δ` as an upper bound for the signed complement's extended-real upper limit. -/
theorem limsup_signedAbelMean_sub_le_of_forall_lt {t n : ℝ → ℝ} {δ : ℝ}
    (hn : ∀ ε > 0, IntegrableOn (fun y ↦ n y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hδ : ∀ d < δ, ∀ᶠ y in atTop, d ≤ n y)
    (ht : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntegrableOn (fun y ↦ t y * Real.exp (-ε * y)) (Ici (0 : ℝ)))
    (hzero : Tendsto (signedAbelMean t) (𝓝[>] 0) (𝓝 0)) :
    limsup (fun ε ↦ (signedAbelMean (fun y ↦ t y - n y) ε : EReal)) (𝓝[>] 0) ≤ ((-δ : ℝ) : EReal) := by
  have hu : Tendsto (fun d : ℝ ↦ ((-d : ℝ) : EReal)) (𝓝[<] δ) (𝓝 ((-δ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp continuous_neg).continuousWithinAt
  exact ge_of_tendsto hu (eventually_of_mem self_mem_nhdsWithin fun d hd ↦
    limsup_signedAbelMean_sub_le hn (hδ d hd) ht hzero)

end RiemannMasullo.AbelEdge
