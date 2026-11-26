module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.DiscreteSubset

/-!
# Measuring real analytic zero orders by a weak limit

For a complex-valued real analytic function, integrate its regularized logarithmic-derivative
density against a signed compactly supported continuous function. The limit is the sum of its
values at the real zeros with their full analytic orders.
-/

public noncomputable section

open Filter Function MeasureTheory Set Topology
namespace RiemannMasullo

/-- The rescaled Cauchy kernel with variable complex coefficient has mass `1 / ‖b a‖`
at the center. Continuity and the bounds are needed only inside the integration set. -/
theorem tendsto_integral_variableCauchy {s : Set ℝ} {a c M : ℝ} {b : ℝ → ℂ} {g : ℝ → ℝ}
    (hs : MeasurableSet s) (ha : s ∈ 𝓝 a) (hb : ContinuousOn b s) (hg : ContinuousOn g s)
    (hc : 0 < c) (hbc : ∀ x ∈ s, c ≤ ‖b x‖) (hM : ∀ x ∈ s, |g x| ≤ M) :
    Tendsto (fun η : ℝ ↦ ∫ x in s,
      g x * (η / Real.pi) / (η ^ 2 + (‖b x‖ * (x - a)) ^ 2))
      (𝓝[>] 0) (𝓝 (g a / ‖b a‖)) := by
  classical
  let T (η v : ℝ) := a + η * v
  let A (η : ℝ) := T η ⁻¹' s
  let F (η : ℝ) := (A η).indicator
    (fun v ↦ g (T η v) / Real.pi * (1 + (‖b (T η v)‖ * v) ^ 2)⁻¹)
  let k (v : ℝ) := g a / Real.pi * (1 + (‖b a‖ * v) ^ 2)⁻¹
  let bound (v : ℝ) := M / Real.pi * (1 + (c * v) ^ 2)⁻¹
  have Mnonneg := (abs_nonneg (g a)).trans (hM a (mem_of_mem_nhds ha))
  have contT (η : ℝ) : Continuous (T η) := by dsimp [T]; fun_prop
  have hmeas (η : ℝ) : AEStronglyMeasurable (F η) volume := by
    have hA : MeasurableSet (A η) := hs.preimage (contT η).measurable
    have hm : MapsTo (T η) (A η) s := fun _ hx ↦ hx
    have cg := hg.comp (contT η).continuousOn hm
    have cb := hb.comp (contT η).continuousOn hm
    have hcont : ContinuousOn (fun v ↦
        g (T η v) / Real.pi * (1 + (‖b (T η v)‖ * v) ^ 2)⁻¹) (A η) :=
      (cg.div_const _).mul ((continuousOn_const.add ((cb.norm.mul continuousOn_id).pow 2)).inv₀
        (fun x _ ↦ show (1 : ℝ) + (‖b (T η x)‖ * x) ^ 2 ≠ 0 from by positivity))
    exact (aestronglyMeasurable_indicator_iff hA).2 (hcont.aestronglyMeasurable hA)
  have hbound (η v : ℝ) : ‖F η v‖ ≤ bound v := by
    by_cases hx : v ∈ A η
    · have hv : c ≤ ‖b (T η v)‖ := hbc _ hx
      have hsq : (c * v) ^ 2 ≤ (‖b (T η v)‖ * v) ^ 2 := by
        rw [mul_pow, mul_pow]
        exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ hc.le (norm_nonneg _)).2 hv) (sq_nonneg _)
      simp only [F, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_div,
        abs_of_pos Real.pi_pos, abs_inv, abs_of_pos (by positivity : 0 < 1 + (‖b (T η v)‖ * v) ^ 2)]
      exact mul_le_mul (div_le_div_of_nonneg_right (hM _ hx) Real.pi_pos.le)
        (inv_anti₀ (by positivity) (by linarith)) (by positivity) (by positivity)
    · simp only [F, Set.indicator_of_notMem hx, norm_zero, bound]
      positivity
  have hpoint (v : ℝ) : Tendsto (fun η ↦ F η v) (𝓝[>] 0) (𝓝 (k v)) := by
    have hscale : Tendsto (fun η : ℝ ↦ T η v) (𝓝[>] 0) (𝓝 a) := by
      simpa [T] using (tendsto_const_nhds (x := a)).add
        ((tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul_const v)
    have hge := (hg.continuousAt ha).tendsto.comp hscale
    have hbe := (hb.continuousAt ha).tendsto.comp hscale
    have hlim := (hge.div_const Real.pi).mul
      (((tendsto_const_nhds (x := (1 : ℝ))).add ((hbe.norm.mul_const v).pow 2)).inv₀
        (by positivity : (1 : ℝ) + (‖b a‖ * v) ^ 2 ≠ 0))
    apply Tendsto.congr' _ hlim
    filter_upwards [hscale ha] with η hη
    have hv : v ∈ A η := hη
    simp [F, hv]
  have hlim := tendsto_integral_filter_of_dominated_convergence (F := F) (f := k) bound
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun η ↦ Eventually.of_forall (hbound η))
    ((integrable_inv_one_add_mul_sq hc.ne').const_mul (M / Real.pi))
    (Eventually.of_forall hpoint)
  have hmass : (∫ v, k v) = g a / ‖b a‖ := by
    rw [show (∫ v, k v) = g a / Real.pi * ∫ v : ℝ, (1 + (‖b a‖ * v) ^ 2)⁻¹ from
      integral_const_mul _ _, integral_univ_inv_one_add_mul_sq, abs_of_nonneg (norm_nonneg _)]
    field_simp [Real.pi_ne_zero, (hc.trans_le (hbc _ (mem_of_mem_nhds ha))).ne']
  rw [hmass] at hlim
  apply Tendsto.congr' _ hlim
  filter_upwards [show ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η from self_mem_nhdsWithin] with η hη
  let H := s.indicator (fun x ↦ g x * (η / Real.pi) / (η ^ 2 + (‖b x‖ * (x - a)) ^ 2))
  have hscale : (∫ v, H (T η v)) = η⁻¹ * ∫ x, H x := by
    change (∫ v : ℝ, (fun y ↦ H (a + y)) (η * v)) = _
    rw [Measure.integral_comp_mul_left (fun v ↦ H (a + v)) η, abs_of_pos (inv_pos.mpr hη), smul_eq_mul,
      integral_add_left_eq_self]
  calc
    (∫ v, F η v) = ∫ v, η * H (T η v) := by
      apply integral_congr_ae
      filter_upwards with v
      by_cases h : T η v ∈ s
      · have hx : v ∈ A η := h
        have he : η ^ 2 + (‖b (T η v)‖ * (T η v - a)) ^ 2 =
            η ^ 2 * (1 + (‖b (T η v)‖ * v) ^ 2) := by dsimp only [T]; ring
        simp only [H, F, Set.indicator_of_mem h, Set.indicator_of_mem hx, he]
        field_simp [hη.ne', Real.pi_ne_zero,
          (by positivity : 1 + (‖b (T η v)‖ * v) ^ 2 ≠ 0)]
      · have hx : v ∉ A η := h
        simp [H, F, h, hx]
    _ = η * (η⁻¹ * ∫ x, H x) := by rw [integral_const_mul, hscale]
    _ = ∫ x in s, g x * (η / Real.pi) / (η ^ 2 + (‖b x‖ * (x - a)) ^ 2) := by
      rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]
      exact integral_indicator hs

/-- The regularized density built from a complex-valued function and its real derivative.
The quotient has value zero at common zeros of the function and its derivative. -/
@[expose] def analyticZeroDensity (f : ℝ → ℂ) (η x : ℝ) : ℝ :=
  (η / Real.pi) * ‖deriv f x‖ ^ 2 / (‖f x‖ ^ 2 + η ^ 2 * ‖deriv f x‖ ^ 2)

private lemma density_of_factor {f : ℝ → ℂ} {t a η : ℝ} {b : ℂ}
    (hd : deriv f t ≠ 0) (he : f t = deriv f t * ((t - a : ℝ) : ℂ) * b) :
    analyticZeroDensity f η t =
      (η / Real.pi) / (η ^ 2 + (‖b‖ * (t - a)) ^ 2) := by
  have hn : ‖f t‖ ^ 2 = ‖deriv f t‖ ^ 2 * (‖b‖ * (t - a)) ^ 2 := by
    rw [he, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow,
      mul_pow, sq_abs]
    ring
  have he' : ‖deriv f t‖ ^ 2 * (‖b‖ * (t - a)) ^ 2 + η ^ 2 * ‖deriv f t‖ ^ 2 =
      (η ^ 2 + (‖b‖ * (t - a)) ^ 2) * ‖deriv f t‖ ^ 2 := by ring
  rw [analyticZeroDensity, hn, he']
  exact mul_div_mul_right _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))

/-- At a zero of analytic order `m + 1`, every small neighborhood carries precisely
`m + 1` times the value of a continuous signed test at the zero. -/
theorem exists_nhds_integral_analyticZeroDensity {f : ℝ → ℂ} {a : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f a) (ho : analyticOrderAt f a = ((m + 1 : ℕ) : ℕ∞)) :
    ∃ W : Set ℝ, IsOpen W ∧ a ∈ W ∧ ∀ (s : Set ℝ), MeasurableSet s → s ∈ 𝓝 a → s ⊆ W →
      ∀ (g : ℝ → ℝ), ContinuousOn g s → (∃ M : ℝ, ∀ x ∈ s, |g x| ≤ M) →
        Tendsto (fun η : ℝ ↦ ∫ x in s, g x * analyticZeroDensity f η x)
          (𝓝[>] 0) (𝓝 (((m + 1 : ℕ) : ℝ) * g a)) := by
  classical
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  have hfu' : f =ᶠ[𝓝 a] fun t ↦ (t - a) ^ (m + 1) • u t := hfu
  let d (t : ℝ) := (t - a) • deriv u t + ((m + 1 : ℕ) : ℝ) • u t
  let b (t : ℝ) := u t / d t
  have hn : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hnc : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hd0 : d a ≠ 0 := by simpa [d, Complex.real_smul] using mul_ne_zero hnc hu0
  have hb0 : b a = (((m + 1 : ℕ) : ℂ))⁻¹ := by
    have hda : d a = ((m + 1 : ℕ) : ℂ) * u a := by simp [d, Complex.real_smul]
    change u a / d a = _
    rw [hda]
    field_simp [hu0, hnc]
  have hnorm : ‖b a‖ = (((m + 1 : ℕ) : ℝ))⁻¹ := by rw [hb0, norm_inv, Complex.norm_natCast]
  have hc : 0 < ‖b a‖ / 2 := by rw [hnorm]; positivity
  have hdcont : ∀ᶠ t in 𝓝 a, ContinuousAt d t := by
    filter_upwards [hu.eventually_analyticAt, hu.deriv.eventually_analyticAt] with t ht hder
    exact ((continuousAt_id.sub_const a).smul hder.continuousAt).add
      (ht.continuousAt.const_smul ((m + 1 : ℕ) : ℝ))
  have hdne := hdcont.self_of_nhds.eventually_ne hd0
  have hbcont : ∀ᶠ t in 𝓝 a, ContinuousAt b t := by
    filter_upwards [hu.eventually_analyticAt, hdcont, hdne] with t ht hc' hn'
    exact ht.continuousAt.div hc' hn'
  have hlow : ∀ᶠ t in 𝓝 a, ‖b a‖ / 2 ≤ ‖b t‖ :=
    (hbcont.self_of_nhds.norm.tendsto.eventually_const_lt (by linarith : ‖b a‖ / 2 < ‖b a‖)).mono
      (fun _ h ↦ h.le)
  have hdu : ∀ᶠ t in 𝓝 a, deriv f t = (t - a) ^ m • d t := by
    filter_upwards [hfu'.deriv, hu.eventually_analyticAt] with t he ht
    have hp := (((hasDerivAt_id t).sub_const a).pow (m + 1)).smul ht.differentiableAt.hasDerivAt
    rw [he]
    refine hp.deriv.trans ?_
    simp [d, Complex.real_smul, pow_succ]
    ring
  have hlocal : ∀ᶠ t in 𝓝 a, ContinuousAt b t ∧ ‖b a‖ / 2 ≤ ‖b t‖ ∧
      (t ≠ a → ∀ η > 0, analyticZeroDensity f η t =
        (η / Real.pi) / (η ^ 2 + (‖b t‖ * (t - a)) ^ 2)) := by
    filter_upwards [hbcont, hlow, hfu, hdu, hdne] with t ht hl hv hd hvd
    refine ⟨ht, hl, fun hta η _ ↦ density_of_factor ?_ ?_⟩
    · rw [hd]
      exact smul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hta)) hvd
    · rw [hv, hd]
      simp only [Complex.real_smul, b, Complex.ofReal_pow, pow_succ]
      field_simp [hvd]
      push_cast
      ring
  obtain ⟨W, hW, hWo, ha⟩ := mem_nhds_iff.mp hlocal
  refine ⟨W, hWo, ha, fun s hs hs0 hsW g hg ⟨M, hM⟩ ↦ ?_⟩
  have hb : ContinuousOn b s := fun t ht ↦ (hW (hsW ht)).1.continuousWithinAt
  have hlim := tendsto_integral_variableCauchy hs hs0 hb hg hc
    (fun t ht ↦ (hW (hsW ht)).2.1) hM
  have hm : g a / ‖b a‖ = ((m + 1 : ℕ) : ℝ) * g a := by rw [hnorm, div_inv_eq_mul, mul_comm]
  rw [hm] at hlim
  apply Tendsto.congr' _ hlim
  filter_upwards [show ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η from self_mem_nhdsWithin] with η hη
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hs, ae_restrict_of_ae (volume.ae_ne a)]
    with t ht hta
  rw [(hW (hsW ht)).2.2 hta η hη, mul_div_assoc]

private lemma density_nonneg (f : ℝ → ℂ) {η : ℝ} (hη : 0 ≤ η) (x : ℝ) :
    0 ≤ analyticZeroDensity f η x := by unfold analyticZeroDensity; positivity

private lemma density_le_inv (f : ℝ → ℂ) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    analyticZeroDensity f η x ≤ 1 / (Real.pi * η) := by
  unfold analyticZeroDensity
  by_cases hd : deriv f x = 0
  · simp only [hd, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, zero_div]
    positivity
  have hD : 0 < ‖deriv f x‖ ^ 2 := by positivity
  have hP : 0 < η ^ 2 * ‖deriv f x‖ ^ 2 := by positivity
  calc
    _ ≤ (η / Real.pi) * ‖deriv f x‖ ^ 2 / (η ^ 2 * ‖deriv f x‖ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hP (le_add_of_nonneg_left (sq_nonneg _))
    _ = 1 / (Real.pi * η) := by field_simp [Real.pi_ne_zero, hη.ne', norm_ne_zero_iff.mpr hd]

private lemma zeroSetOnCompact_finite {f : ℝ → ℂ} {K : Set ℝ} (hK : IsCompact K)
    (hfa : ∀ x ∈ K, AnalyticAt ℝ f x) (hord : ∀ x ∈ K, analyticOrderAt f x ≠ ⊤) :
    (K ∩ {x | f x = 0}).Finite := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z := K ∩ {x | f x = 0}
  have hfK : ContinuousOn f K := fun x hx ↦ (hfa x hx).continuousAt.continuousWithinAt
  have hclosed : IsClosed {x : K | f x = 0} :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hfK) continuous_const
  have hcompact : IsCompact Z := by
    convert hclosed.isCompact.image continuous_subtype_val using 1
    ext x
    simp [Z, and_comm]
  apply hcompact.finite
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [inf_principal_eq_bot]
  have hne := (hfa x hx.1).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun hv ↦ hord x hx.1 (analyticOrderAt_eq_top.mpr hv))
  exact hne.mono fun t ht hz ↦ ht hz.2

/-- A signed compact continuous test detects the full real analytic order at each zero.
The function need only be analytic with finite order at the points of the test's closed
support. Only finitely many terms of the sum are nonzero. -/
theorem tendsto_integral_analyticZeroDensity {f : ℝ → ℂ} {g : ℝ → ℝ} (hg : Continuous g)
    (hK : HasCompactSupport g) (hfa : ∀ x ∈ tsupport g, AnalyticAt ℝ f x)
    (hord : ∀ x ∈ tsupport g, analyticOrderAt f x ≠ ⊤) :
    Tendsto (fun η : ℝ ↦ ∫ x, g x * analyticZeroDensity f η x) (𝓝[>] 0)
      (𝓝 (∑' z : {x : ℝ // f x = 0}, (analyticOrderNatAt f (z : ℝ) : ℝ) * g z)) := by
  classical
  let K := tsupport g
  let Z := K ∩ {x | f x = 0}
  have hcompact : IsCompact K := hK
  have hZ : Z.Finite := zeroSetOnCompact_finite hK hfa hord
  let S := hZ.toFinset
  have hS (x : ℝ) : x ∈ S ↔ x ∈ K ∧ f x = 0 := hZ.mem_toFinset
  have hfg : ContinuousOn f K := fun x hx ↦ (hfa x hx).continuousAt.continuousWithinAt
  have hfd : ContinuousOn (deriv f) K := fun x hx ↦ (hfa x hx).deriv.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hg.abs.continuousOn
  have hMg (t : ℝ) : |g t| ≤ max M 0 := by
    by_cases ht : t ∈ K
    · exact (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ht, abs_zero]
      exact le_max_right _ _
  have hnh (a : ℝ) (ha : a ∈ S) :
      ∃ W : Set ℝ, IsOpen W ∧ a ∈ W ∧ ∀ s : Set ℝ, MeasurableSet s → s ∈ 𝓝 a → s ⊆ W →
        Tendsto (fun η : ℝ ↦ ∫ x in s, g x * analyticZeroDensity f η x) (𝓝[>] 0)
          (𝓝 ((analyticOrderNatAt f a : ℝ) * g a)) := by
    obtain ⟨hak, haz⟩ := (hS a).mp ha
    have hn : analyticOrderNatAt f a ≠ 0 := by
      intro h
      have h' : analyticOrderAt f a = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (hord a hak), h, Nat.cast_zero]
      exact (analyticOrderAt_eq_zero.mp h').elim (fun hn ↦ hn (hfa a hak)) (fun hn ↦ hn haz)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hh : analyticOrderAt f a = ((m + 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_analyticOrderNatAt (hord a hak), hm]
    obtain ⟨W, hw, haW, hw'⟩ := exists_nhds_integral_analyticZeroDensity (hfa a hak) hh
    refine ⟨W, hw, haW, fun s hs hs0 hss ↦ ?_⟩
    rw [hm]
    exact hw' s hs hs0 hss _ hg.continuousOn ⟨_, fun t _ ↦ hMg t⟩
  choose W hoW haW hlimW using hnh
  obtain ⟨O, hO, hdis⟩ := S.finite_toSet.t2_separation
  let B (a : ℝ) := if ha : a ∈ S then W a ha ∩ O a else ∅
  have hBo (a : ℝ) (ha : a ∈ S) : IsOpen (B a) := by
    simpa only [B, dite_eq_left ha] using (hoW a ha).inter (hO a).2
  have hBa (a : ℝ) (ha : a ∈ S) : a ∈ B a := by
    simpa only [B, dite_eq_left ha] using (show a ∈ W a ha ∩ O a from ⟨haW a ha, (hO a).1⟩)
  have hBi (a : ℝ) (ha : a ∈ S) : B a ⊆ O a := by
    simpa only [B, dite_eq_left ha] using (inter_subset_right : W a ha ∩ O a ⊆ _)
  have hBp : (S : Set ℝ).PairwiseDisjoint B :=
    fun x hx y hy hxy ↦ (hdis hx hy hxy).mono (hBi x hx) (hBi y hy)
  let U := ⋃ a ∈ S, B a
  have hUo : IsOpen U := isOpen_biUnion hBo
  let E := K \ U
  have hE : IsCompact E := hcompact.inter_right hUo.isClosed_compl
  have hEf (x : ℝ) (hx : x ∈ E) : f x ≠ 0 := by
    intro hz
    have hs := (hS x).mpr ⟨hx.1, hz⟩
    exact hx.2 (mem_iUnion₂.mpr ⟨x, hs, hBa x hs⟩)
  let G (η x : ℝ) := g x * analyticZeroDensity f η x
  have hsG (η : ℝ) : support (G η) ⊆ K := by
    intro x hx
    by_contra h
    exact hx (by simp [G, image_eq_zero_of_notMem_tsupport (f := g) h])
  have hmG (η : ℝ) : AEStronglyMeasurable (G η) (volume.restrict K) := by
    have mf := (hfg.aemeasurable (μ := volume) hcompact.measurableSet)
    have md := (hfd.aemeasurable (μ := volume) hcompact.measurableSet)
    exact (hg.measurable.aemeasurable.mul ((aemeasurable_const.mul (md.norm.pow_const 2)).div
      ((mf.norm.pow_const 2).add (aemeasurable_const.mul (md.norm.pow_const 2))))).aestronglyMeasurable
  have hiG (η : ℝ) (hη : 0 < η) : Integrable (G η) := by
    apply (integrableOn_iff_integrable_of_support_subset (hsG η)).mp
    apply ((hg.integrable_of_hasCompactSupport hK).norm.mul_const
      (1 / (Real.pi * η))).integrableOn.mono' (hmG η)
    filter_upwards with t
    simp only [G, Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg f hη.le t)]
    exact mul_le_mul_of_nonneg_left (density_le_inv f hη t) (abs_nonneg _)
  let Q (x : ℝ) := |g x| * ((1 / Real.pi) * ‖deriv f x‖ ^ 2 / ‖f x‖ ^ 2)
  have hEQ : ContinuousOn Q E := hg.abs.continuousOn.mul
    ((continuousOn_const.mul (((hfd.mono sdiff_subset).norm).pow 2)).div
      (((hfg.mono sdiff_subset).norm).pow 2) (fun t ht ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hEf _ ht))))
  have away : Tendsto (fun η : ℝ ↦ ∫ x in E, G η x) (𝓝[>] 0) (𝓝 0) := by
    have hη0 : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hηb : ∀ᶠ η : ℝ in 𝓝[>] 0, η ≤ 1 := hη0.eventually_le_const (by norm_num)
    have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
    suffices h : Tendsto (fun η : ℝ ↦ ∫ x in E, G η x) (𝓝[>] 0)
        (𝓝 (∫ _x : ℝ in E, (0 : ℝ))) by simpa using h
    apply tendsto_integral_filter_of_dominated_convergence (F := G) (μ := volume.restrict E)
      (f := fun _ ↦ (0 : ℝ)) Q
    · filter_upwards [hpos] with η hη
      exact (hiG η hη).integrableOn.aestronglyMeasurable
    · filter_upwards [hpos, hηb] with η hη hη1
      filter_upwards [ae_restrict_mem (μ := volume) hE.measurableSet] with x hx
      have hf0 : 0 < ‖f x‖ ^ 2 := pow_pos (norm_pos_iff.mpr (hEf _ hx)) _
      simp only [G, Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg f hη.le x), Q]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ (η / Real.pi) * ‖deriv f x‖ ^ 2 / ‖f x‖ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hf0 (le_add_of_nonneg_right (by positivity))
        _ ≤ _ := by gcongr
    · exact hEQ.integrableOn_compact hE
    · filter_upwards [ae_restrict_mem (μ := volume) hE.measurableSet] with x hx
      have hz : ‖f x‖ ^ 2 + 0 ^ 2 * ‖deriv f x‖ ^ 2 ≠ 0 := by simp [hEf _ hx]
      have hl := ((hη0.div_const Real.pi).mul_const (‖deriv f x‖ ^ 2)).div
        ((tendsto_const_nhds (x := ‖f x‖ ^ 2)).add ((hη0.pow 2).mul_const (‖deriv f x‖ ^ 2))) hz
      simpa [G, analyticZeroDensity] using (tendsto_const_nhds (x := g x)).mul hl
  have complement (η : ℝ) : (∫ x in Uᶜ, G η x) = ∫ x in E, G η x := by
    rw [← integral_indicator hUo.measurableSet.compl, ← integral_indicator hE.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ K
    · by_cases hu : x ∈ U <;> simp [E, hx, hu]
    · have hg0 := image_eq_zero_of_notMem_tsupport (f := g) hx
      by_cases hu : x ∈ U <;> simp [E, hx, hu, G, hg0]
  have hnear := tendsto_finsetSum S (fun a (ha : a ∈ S) ↦ hlimW a ha (B a)
    (hBo a ha).measurableSet ((hBo a ha).mem_nhds (hBa a ha))
    (by simpa only [B, dite_eq_left ha] using (inter_subset_left : W a ha ∩ O a ⊆ _)))
  have hmass : (∑' x : ℝ, (analyticOrderNatAt f x : ℝ) * g x) =
      ∑ a ∈ S, (analyticOrderNatAt f a : ℝ) * g a := by
    apply tsum_eq_sum
    intro x hx
    by_cases hk : x ∈ K
    · have hf0 : f x ≠ 0 := fun h ↦ hx ((hS x).mpr ⟨hk, h⟩)
      simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hf0)]
    · simp [image_eq_zero_of_notMem_tsupport (f := g) hk]
  have hzeros : (∑' z : {x : ℝ // f x = 0}, (analyticOrderNatAt f (z : ℝ) : ℝ) * g z) =
      ∑' x : ℝ, (analyticOrderNatAt f x : ℝ) * g x := by
    refine tsum_subtype_eq_of_support_subset (s := {x : ℝ | f x = 0})
      (f := fun x : ℝ ↦ (analyticOrderNatAt f x : ℝ) * g x) ?_
    intro x hx
    by_contra h
    exact hx (by simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h)])
  rw [hzeros, hmass]
  have htotal := hnear.add away
  rw [add_zero] at htotal
  apply Tendsto.congr' _ htotal
  filter_upwards [show ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η from self_mem_nhdsWithin] with η hη
  calc
    (∑ a ∈ S, ∫ x in B a, G η x) + ∫ x in E, G η x =
        (∫ x in U, G η x) + ∫ x in Uᶜ, G η x := by
      rw [complement, ← integral_biUnion_finset S (fun a ha ↦ (hBo a ha).measurableSet) hBp
        (fun _ _ ↦ (hiG η hη).integrableOn)]
    _ = _ := integral_add_compl hUo.measurableSet (hiG η hη)

end RiemannMasullo
