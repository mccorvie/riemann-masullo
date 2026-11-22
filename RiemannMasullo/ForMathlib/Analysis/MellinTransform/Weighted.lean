module

public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Convergence and holomorphy of weighted Mellin integrals -/

public noncomputable section

open Filter MeasureTheory Set Topology

namespace RiemannMasullo

/-- A weighted Mellin integral is holomorphic on any open strip on which it
converges absolutely. The two nearby real powers dominate its logarithmic derivative. -/
theorem analyticOnNhd_integral_mul_cpow {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (r : X → ℝ) (hf : Measurable f) (hr : Measurable r) (hp : ∀ x, 0 < r x)
    {U : Set ℝ} (ho : IsOpen U) (hi : ∀ a ∈ U, Integrable (fun x ↦ ‖f x‖ * r x ^ a) μ) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ x, f x * (r x : ℂ) ^ s ∂μ) (Complex.re ⁻¹' U) := by
  apply DifferentiableOn.analyticOnNhd _ (ho.preimage Complex.continuous_re)
  intro s hs
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hs)
  let ε := δ / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  let lo := s.re - 2 * ε
  let up := s.re + 2 * ε
  have h2 : 2 * ε < δ := by dsimp [ε]; linarith
  have hl : lo ∈ U := hd (by
    rw [Metric.mem_ball, Real.dist_eq]
    change |s.re - 2 * ε - s.re| < δ
    rw [show s.re - 2 * ε - s.re = -(2 * ε) by ring, abs_neg, abs_of_pos (by positivity)]
    exact h2)
  have hu : up ∈ U := hd (by
    rw [Metric.mem_ball, Real.dist_eq]
    change |s.re + 2 * ε - s.re| < δ
    rwa [add_sub_cancel_left, abs_of_pos (by positivity)])
  let W (z : ℂ) (x : X) := f x * (r x : ℂ) ^ z
  let D (z : ℂ) (x : X) := W z x * Complex.log (r x : ℂ)
  have hW (z : ℂ) : Measurable (W z) := hf.mul (hr.complex_ofReal.pow_const _)
  have hN (z : ℂ) (x : X) : ‖W z x‖ = ‖f x‖ * r x ^ z.re := by
    dsimp only [W]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hp x)]
  let M (x : X) := (‖f x‖ * r x ^ lo + ‖f x‖ * r x ^ up) * ε⁻¹
  have hM : Integrable M μ := ((hi lo hl).add (hi up hu)).mul_const _
  have hbound (x : X) (z : ℂ) (hz : z ∈ Metric.ball s ε) : ‖D z x‖ ≤ M x := by
    have hz' : |z.re - s.re| < ε := (Complex.abs_re_le_norm (z - s)).trans_lt
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
    have hlog : ‖Complex.log (r x : ℂ)‖ = |Real.log (r x)| := by
      rw [← Complex.ofReal_log (hp x).le, Complex.norm_real, Real.norm_eq_abs]
    dsimp only [D, M]
    rw [norm_mul, hN, hlog, ← div_eq_mul_inv]
    apply (le_div_iff₀ hε).2
    let t := Real.log (r x)
    have he : |t| * ε ≤ Real.exp (ε * |t|) := by
      rw [mul_comm]
      linarith [Real.add_one_le_exp (ε * |t|)]
    have hpow (a : ℝ) : r x ^ a = Real.exp (t * a) := Real.rpow_def_of_pos (hp x) a
    have hrange := abs_lt.mp hz'
    rcases le_total 0 t with ht | ht
    · apply le_add_of_nonneg_of_le (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
      rw [hpow, hpow]
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ Real.exp (t * z.re) * Real.exp (ε * |t|) := mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
        _ ≤ _ := by
          rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonneg ht]
          dsimp [up]
          nlinarith [mul_nonneg ht (show 0 ≤ s.re + ε - z.re by linarith [hrange.2])]
    · apply le_add_of_le_of_nonneg _ (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
      rw [hpow, hpow]
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ Real.exp (t * z.re) * Real.exp (ε * |t|) := mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
        _ ≤ _ := by
          rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonpos ht]
          dsimp [lo]
          nlinarith [mul_nonpos_of_nonpos_of_nonneg ht (show 0 ≤ z.re - s.re + ε by linarith [hrange.1])]
  have hder (x : X) (z : ℂ) : HasDerivAt (fun w ↦ W w x) (D z x) z := by
    simpa only [W, D, id_eq, mul_assoc, mul_one] using
      (((hasDerivAt_id z).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hp x).ne'))).const_mul (f x))
  have hI : Integrable (W s) μ :=
    (hi s.re hs).mono' (hW s).aestronglyMeasurable (.of_forall fun x ↦ (hN s x).le)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hε)
    (.of_forall fun z ↦ (hW z).aestronglyMeasurable) hI
    ((hW s).mul (Complex.measurable_log.comp hr.complex_ofReal)).aestronglyMeasurable
    (.of_forall hbound) hM (.of_forall fun x z _ ↦ hder x z)).2.differentiableAt.differentiableWithinAt

/-- An integrable Mellin family is uniformly approximated by norm bands when
the abscissa ranges over a compact set. Its two endpoint integrands dominate
the two tails on opposite sides of norm one. -/
theorem tendstoUniformlyOn_mellinBands {X P : Type*} [MeasurableSpace X]
    [TopologicalSpace P] (μ : Measure X) (r : X → ℝ) (hr : ∀ x, 0 < r x) (hm : Measurable r)
    (A : X → ℝ) (hA : ∀ x, 0 ≤ A x) (σ : P → ℝ) (H : P → X → ℂ)
    (K : Set P) (hK : IsCompact K) (hσ : ContinuousOn σ K)
    (hI : ∀ p ∈ K, Integrable (H p) μ)
    (hN : ∀ p ∈ K, ∀ x, ‖H p x‖ = A x * r x ^ σ p) :
    TendstoUniformlyOn (fun (n : ℕ) p ↦ ∫ x in {x | r x ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}, H p x ∂μ)
      (fun p ↦ ∫ x, H p x ∂μ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hσ
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hσ
  let M (x : X) := ‖H a x‖ + ‖H b x‖
  have hM : Integrable M μ := (hI a ha).norm.add (hI b hb).norm
  have hle {p : P} (hp : p ∈ K) (x : X) : ‖H p x‖ ≤ M x := by
    dsimp only [M]
    rcases le_total (r x) 1 with hx | hx
    · apply le_add_of_le_of_nonneg _ (norm_nonneg _)
      rw [hN p hp, hN a ha]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hr x) hx (hmin hp)) (hA x)
    · apply le_add_of_nonneg_of_le (norm_nonneg _) _
      rw [hN p hp, hN b hb]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (hmax hp)) (hA x)
  let B (n : ℕ) := {x | r x ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}
  have hB (n : ℕ) : MeasurableSet (B n) := hm measurableSet_Icc
  have hmono : Monotone B := by
    intro i j hij x hx
    have h : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact ⟨((inv_le_inv₀ (by positivity) (by positivity)).mpr h).trans hx.1, hx.2.trans h⟩
  have hexhaust : (⋂ n, (B n)ᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max (r x) (r x)⁻¹)
    have h : max (r x) (r x)⁻¹ ≤ (n : ℝ) + 1 := hn.le.trans (by linarith)
    exact (mem_iInter.mp hx n) ⟨(inv_le_comm₀ (by positivity) (hr x)).2 ((le_max_right _ _).trans h),
      (le_max_left _ _).trans h⟩
  have hlim : Tendsto (fun n ↦ ∫ x in (B n)ᶜ, M x ∂μ) atTop (𝓝 0) := by
    simpa only [hexhaust, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (μ := μ) (f := M) (fun n ↦ (hB n).compl)
        (fun _ _ hij ↦ compl_subset_compl.mpr (hmono hij)) ⟨0, hM.integrableOn⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn p hp
  change dist (∫ x, H p x ∂μ) (∫ x in B n, H p x ∂μ) < ε
  rw [dist_eq_norm, ← integral_add_compl (hB n) (hI p hp), add_sub_cancel_left]
  exact (norm_integral_le_integral_norm _).trans_lt ((setIntegral_mono_on
    (hI p hp).norm.integrableOn hM.integrableOn (hB n).compl (fun x _ ↦ hle hp x)).trans_lt hn)

end RiemannMasullo
