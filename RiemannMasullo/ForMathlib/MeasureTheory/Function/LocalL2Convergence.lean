module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! # Local square-integral convergence and bounded pairings -/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace RiemannMasullo

private theorem norm_integral_mul_le_sqrt_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  calc
    _ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
    _ ≤ _ := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two] using integral_mul_norm_le_Lp_mul_Lq hp hf' hg'

/-- A family bounded in L² and tending to zero in L² on each set of a measurable
exhaustion pairs to zero with every family of kernels dominated by one L² function. -/
theorem tendsto_integral_mul_zero_of_localL2
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hsMono : Monotone s)
    (hsCover : (⋃ n, s n) = univ)
    {f g : ι → X → ℂ} {G : X → ℝ} {C : ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hfBound : ∀ i, (∫ x, ‖f i x‖ ^ 2 ∂μ) ≤ C)
    (hfLocal : ∀ n, Tendsto (fun i ↦ ∫ x in s n, ‖f i x‖ ^ 2 ∂μ) l (𝓝 0))
    (hG : MemLp G 2 μ) (hgMeas : ∀ i, AEStronglyMeasurable (g i) μ)
    (hgBound : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ G x) :
    Tendsto (fun i ↦ ∫ x, f i x * g i x ∂μ) l (𝓝 0) := by
  have hg (i : ι) : MemLp (g i) 2 μ := hG.mono' (hgMeas i) (hgBound i)
  have hGsq : Integrable (fun x ↦ G x ^ 2) μ := hG.integrable_sq
  have hgSq (i : ι) : Integrable (fun x ↦ ‖g i x‖ ^ 2) μ :=
    (hg i).integrable_norm_pow (by norm_num)
  have hfg (i : ι) : Integrable (fun x ↦ f i x * g i x) μ :=
    (hf i).integrable_mul (hg i)
  have hfSq (i : ι) : Integrable (fun x ↦ ‖f i x‖ ^ 2) μ :=
    (hf i).integrable_norm_pow (by norm_num)
  have hgSqLe (i : ι) (t : Set X) :
      (∫ x in t, ‖g i x‖ ^ 2 ∂μ) ≤ ∫ x in t, G x ^ 2 ∂μ := by
    refine integral_mono_ae (hgSq i).integrableOn hGsq.integrableOn ?_
    filter_upwards [(hgBound i).filter_mono ae_restrict_le] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hEmpty : (⋂ n, (s n)ᶜ) = ∅ := by rw [← compl_iUnion, hsCover, compl_univ]
  have hTailSq : Tendsto (fun n ↦ ∫ x in (s n)ᶜ, G x ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [hEmpty, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (f := fun x ↦ G x ^ 2)
        (s := fun n ↦ (s n)ᶜ) (fun n ↦ (hs n).compl)
        (fun _ _ h ↦ compl_subset_compl.mpr (hsMono h))
        ⟨0, hGsq.integrableOn⟩)
  have hTail : Tendsto
      (fun n ↦ Real.sqrt C * Real.sqrt (∫ x in (s n)ᶜ, G x ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds (x := Real.sqrt C)).mul
        (Real.continuous_sqrt.continuousAt.tendsto.comp hTailSq)
  have hWindow (n : ℕ) : Tendsto
      (fun i ↦ Real.sqrt (∫ x in s n, ‖f i x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, G x ^ 2 ∂μ))
      l (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp (hfLocal n)).mul
        (tendsto_const_nhds (x := Real.sqrt (∫ x, G x ^ 2 ∂μ)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hTail).2 (ε / 2) (by positivity)).exists
  filter_upwards [(tendsto_order.mp (hWindow n)).2 (ε / 2) (by positivity)] with i hi
  rw [dist_zero_right, ← integral_add_compl (hs n) (hfg i)]
  calc
    _ ≤ ‖∫ x in s n, f i x * g i x ∂μ‖ + ‖∫ x in (s n)ᶜ, f i x * g i x ∂μ‖ :=
      norm_add_le _ _
    _ ≤
        Real.sqrt (∫ x in s n, ‖f i x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, G x ^ 2 ∂μ) +
        Real.sqrt C * Real.sqrt (∫ x in (s n)ᶜ, G x ^ 2 ∂μ) := by
      refine add_le_add ?_ ?_
      · refine (norm_integral_mul_le_sqrt_sq ((hf i).restrict _) ((hg i).restrict _)).trans ?_
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
        exact (hgSqLe i _).trans (setIntegral_le_integral hGsq (ae_of_all _ fun x ↦ sq_nonneg (G x)))
      · refine (norm_integral_mul_le_sqrt_sq ((hf i).restrict _) ((hg i).restrict _)).trans ?_
        refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt (hgSqLe i _))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact (setIntegral_le_integral (hfSq i) (ae_of_all _ fun x ↦ sq_nonneg ‖f i x‖)).trans
          (hfBound i)
    _ < ε / 2 + ε / 2 := add_lt_add hi hn
    _ = ε := by ring

/-- If every sequence tending to infinity has a subsequence with limiting tail masses
that tend to zero as the window grows, the original family is eventually concentrated.
The tail masses are antitone in the radius of the window. -/
theorem eventually_lt_of_subsequence_tailMass
    {mass : ℝ → ℕ → ℝ} (hAnti : ∀ x, Antitone (mass x))
    (hSub : ∀ u : ℕ → ℝ, Tendsto u atTop atTop →
      ∃ (σ : ℕ → ℕ), StrictMono σ ∧ ∃ limit : ℕ → ℝ,
        Tendsto limit atTop (𝓝 0) ∧ ∀ R,
          Tendsto (fun n ↦ mass (u (σ n)) R) atTop (𝓝 (limit R))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ᶠ x in atTop, mass x R < ε := by
  intro ε hε
  by_contra h
  have hfreq (R : ℕ) : ∃ᶠ x in atTop, ε ≤ mass x R := by
    intro h'
    exact h ⟨R, by simpa only [not_le] using h'⟩
  choose x hx hmass using fun n : ℕ ↦ frequently_atTop.mp (hfreq n) (n : ℝ)
  have hxTop : Tendsto x atTop atTop := tendsto_atTop_mono hx tendsto_natCast_atTop_atTop
  obtain ⟨σ, hσ, limit, hLimit, hConv⟩ := hSub x hxTop
  obtain ⟨R, hR⟩ := ((tendsto_order.mp hLimit).2 ε hε).exists
  have hσR : ∀ᶠ n in atTop, R ≤ σ n := hσ.tendsto_atTop.eventually (eventually_ge_atTop R)
  obtain ⟨n, hnR, hn⟩ := (hσR.and ((tendsto_order.mp (hConv R)).2 ε hR)).exists
  exact (not_lt_of_ge ((hmass (σ n)).trans (hAnti (x (σ n)) hnR))) hn

/-- If the squared mass is eventually concentrated in two moving windows, a translated
pairing at a center escaping both windows tends to zero. The kernels may depend on the
translation provided their norms are dominated by one square-integrable function. -/
theorem tendsto_integral_translate_mul_zero_of_twoWindows
    {ι : Type*} {l : Filter ι} {a b y : ι → ℝ} {f g : ι → ℝ → ℂ} {G : ℝ → ℝ}
    {C : ℝ} (hf : ∀ i, MemLp (f i) 2 volume)
    (hfBound : ∀ i, (∫ x, ‖f i x‖ ^ 2) ≤ C)
    (hfConcentrates : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ i in l,
      (∫ x in (Metric.closedBall (a i) R ∪ Metric.closedBall (b i) R)ᶜ,
        ‖f i x‖ ^ 2) < ε)
    (ha : Tendsto (fun i ↦ dist (y i) (a i)) l atTop)
    (hb : Tendsto (fun i ↦ dist (y i) (b i)) l atTop)
    (hG : MemLp G 2 volume) (hgMeas : ∀ i, AEStronglyMeasurable (g i) volume)
    (hgBound : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ G x) :
    Tendsto (fun i ↦ ∫ x, f i (y i + x) * g i x) l (𝓝 0) := by
  let s (n : ℕ) := Metric.closedBall (0 : ℝ) (n : ℝ)
  have hPres (i : ι) : MeasurePreserving (fun x ↦ y i + x) volume volume :=
    measurePreserving_add_left volume (y i)
  have hEmb (i : ι) : MeasurableEmbedding (fun x ↦ y i + x) :=
    (MeasurableEquiv.addLeft (y i)).measurableEmbedding
  have hfSq (i : ι) : Integrable (fun x ↦ ‖f i x‖ ^ 2) volume :=
    (hf i).integrable_norm_pow (by norm_num)
  refine tendsto_integral_mul_zero_of_localL2 (s := s) (C := C)
    (fun _ ↦ Metric.isClosed_closedBall.measurableSet)
    (fun _ _ h ↦ Metric.closedBall_subset_closedBall (Nat.cast_le.mpr h)) ?_
    (fun i ↦ (hf i).comp_measurePreserving (hPres i)) ?_ ?_ hG hgMeas hgBound
  · refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨n, Metric.mem_closedBall.2 hn.le⟩
  · intro i
    change (∫ x, (fun z ↦ ‖f i z‖ ^ 2) (y i + x)) ≤ C
    rw [(hPres i).integral_comp (hEmb i) (fun z ↦ ‖f i z‖ ^ 2)]
    exact hfBound i
  · intro n
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := hfConcentrates ε hε
    filter_upwards [hR, ha.eventually (eventually_gt_atTop ((n : ℝ) + R)),
      hb.eventually (eventually_gt_atTop ((n : ℝ) + R))] with i hi hia hib
    have hsub : (fun x ↦ y i + x) '' s n ⊆
        (Metric.closedBall (a i) R ∪ Metric.closedBall (b i) R)ᶜ := by
      rintro _ ⟨x, hx, rfl⟩
      have hdist : dist (y i) (y i + x) ≤ (n : ℝ) := calc
        dist (y i) (y i + x) = dist x 0 := by
          simp only [Real.dist_eq, sub_zero, show y i - (y i + x) = -x by ring, abs_neg]
        _ ≤ _ := Metric.mem_closedBall.1 hx
      intro hm
      rcases hm with hm | hm
      · exact (not_le.mpr hia) ((dist_triangle _ (y i + x) _).trans
          (add_le_add hdist (Metric.mem_closedBall.1 hm)))
      · exact (not_le.mpr hib) ((dist_triangle _ (y i + x) _).trans
          (add_le_add hdist (Metric.mem_closedBall.1 hm)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
    change (∫ x in s n, (fun z ↦ ‖f i z‖ ^ 2) (y i + x)) < ε
    rw [← (hPres i).setIntegral_image_emb (hEmb i) (fun z ↦ ‖f i z‖ ^ 2) (s n)]
    exact (setIntegral_mono_set (hfSq i).integrableOn
      (ae_of_all _ fun x ↦ sq_nonneg ‖f i x‖) (ae_of_all _ hsub)).trans_lt hi

/-- Weighted evaluations tend to zero at a center escaping both concentration windows.
The weighted translate of the reproducing kernel is allowed to vary, but its norm must
be dominated by one square-integrable envelope. -/
theorem tendsto_weighted_eval_zero_of_twoWindows
    {ι : Type*} {l : Filter ι} {a b y : ι → ℝ} {f : ι → ℝ → ℂ} {φ : ℝ → ℂ}
    {w G : ℝ → ℝ} {C : ℝ} (hw : ∀ x, 0 < w x) (hwMeas : Measurable w)
    (hf : ∀ i, MemLp (fun x ↦ (Real.sqrt (w x) : ℂ) * f i x) 2 volume)
    (hfBound : ∀ i, (∫ x, w x * ‖f i x‖ ^ 2) ≤ C)
    (hfConcentrates : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ i in l,
      (∫ x in (Metric.closedBall (a i) R ∪ Metric.closedBall (b i) R)ᶜ,
        w x * ‖f i x‖ ^ 2) < ε)
    (ha : Tendsto (fun i ↦ dist (y i) (a i)) l atTop)
    (hb : Tendsto (fun i ↦ dist (y i) (b i)) l atTop)
    (hφ : AEStronglyMeasurable φ volume)
    (hReproduce : ∀ i, f i (y i) = ∫ x, f i (y i + x) * φ x)
    (hG : MemLp G 2 volume)
    (hDom : ∀ᶠ i in l, ∀ᵐ x ∂volume,
      Real.sqrt (w (y i)) / Real.sqrt (w (y i + x)) * ‖φ x‖ ≤ G x) :
    Tendsto (fun i ↦ (Real.sqrt (w (y i)) : ℂ) * f i (y i)) l (𝓝 0) := by
  classical
  let F (i : ι) (x : ℝ) := (Real.sqrt (w x) : ℂ) * f i x
  let good (i : ι) := ∀ᵐ x ∂volume, Real.sqrt (w (y i)) / Real.sqrt (w (y i + x)) * ‖φ x‖ ≤ G x
  let K (i : ι) (x : ℝ) :=
    if good i then ((Real.sqrt (w (y i)) / Real.sqrt (w (y i + x)) : ℝ) : ℂ) * φ x else 0
  have hSq (i : ι) (x : ℝ) : ‖F i x‖ ^ 2 = w x * ‖f i x‖ ^ 2 := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw x).le]
  have hKMeas (i : ι) : AEStronglyMeasurable (K i) volume := by
    have hRatio : Measurable
        (fun x ↦ ((Real.sqrt (w (y i)) / Real.sqrt (w (y i + x)) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (measurable_const.div
        (Real.continuous_sqrt.measurable.comp (hwMeas.comp (measurable_const.add measurable_id))))
    dsimp only [K]
    split
    · exact hRatio.aestronglyMeasurable.mul hφ
    · exact aestronglyMeasurable_zero
  have hKDom (i : ι) : ∀ᵐ x ∂volume, ‖K i x‖ ≤ |G x| := by
    by_cases hi : good i
    · filter_upwards [hi] with x hx
      dsimp only [K]
      rw [ite_eq_left hi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hx.trans (le_abs_self _)
    · exact ae_of_all _ fun x ↦ by simp only [K, ite_eq_right hi, norm_zero, abs_nonneg]
  have hG' : MemLp (fun x ↦ |G x|) 2 volume := by
    simpa only [Real.norm_eq_abs] using hG.norm
  have hTend := tendsto_integral_translate_mul_zero_of_twoWindows
    (f := F) (g := K) (C := C) hf
    (by simpa only [hSq] using hfBound) (by simpa only [hSq] using hfConcentrates)
    ha hb hG' hKMeas hKDom
  refine hTend.congr' ?_
  filter_upwards [hDom] with i hi
  have hi' : good i := hi
  rw [hReproduce i, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have hden : (Real.sqrt (w (y i + x)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (hw (y i + x))).ne'
  dsimp only [F, K]
  rw [ite_eq_left hi', Complex.ofReal_div]
  field_simp

/-- For a fixed nontrivial contraction, the weighted evaluation of a family concentrated
near the two symmetric centers tends to zero along the positive real ray. -/
theorem tendsto_weighted_eval_dilation_zero_of_twoWindows
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {w G : ℝ → ℝ} {C : ℝ} (hw : ∀ x, 0 < w x) (hwMeas : Measurable w)
    (hf : ∀ i, MemLp (fun x ↦ (Real.sqrt (w x) : ℂ) * f i x) 2 volume)
    (hfBound : ∀ i, (∫ x, w x * ‖f i x‖ ^ 2) ≤ C)
    (hfConcentrates : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ i in atTop,
      (∫ x in (Metric.closedBall i R ∪ Metric.closedBall (-i) R)ᶜ,
        w x * ‖f i x‖ ^ 2) < ε)
    (hφ : AEStronglyMeasurable φ volume)
    (hReproduce : ∀ i, f i (q * i) = ∫ x, f i (q * i + x) * φ x)
    (hG : MemLp G 2 volume)
    (hDom : ∀ᶠ i in atTop, ∀ᵐ x ∂volume,
      Real.sqrt (w (q * i)) / Real.sqrt (w (q * i + x)) * ‖φ x‖ ≤ G x) :
    Tendsto (fun i ↦ (Real.sqrt (w (q * i)) : ℂ) * f i (q * i)) atTop (𝓝 0) := by
  have hminus : 0 < 1 - q := sub_pos.mpr hq1
  have hplus : 0 < 1 + q := by positivity
  have ha : Tendsto (fun i ↦ dist (q * i) i) atTop atTop := by
    refine ((tendsto_const_mul_atTop_of_pos hminus).2 tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
    change (1 - q) * i = dist (q * i) i
    rw [Real.dist_eq, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by simpa using mul_le_mul_of_nonneg_right hq1.le hi)
  have hb : Tendsto (fun i ↦ dist (q * i) (-i)) atTop atTop := by
    refine ((tendsto_const_mul_atTop_of_pos hplus).2 tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
    change (1 + q) * i = dist (q * i) (-i)
    rw [Real.dist_eq, abs_of_nonneg]
    · ring
    · rw [sub_neg_eq_add]
      positivity
  exact tendsto_weighted_eval_zero_of_twoWindows (C := C) hw hwMeas hf hfBound hfConcentrates
    ha hb hφ hReproduce hG hDom

/-- The actual even dilation density decays on both tails if the band evaluation
extremizers concentrate at the symmetric centers. The density factorization uses the
norm of the unnormalized evaluation vector and the ratio of the weights at the two
arguments of the reproducing kernel. -/
theorem weighted_dilation_density_decay_of_twoWindows
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ → ℂ} {φ d : ℝ → ℂ}
    {w G eNorm : ℝ → ℝ} {C : ℝ} (hw : ∀ x, 0 < w x) (hwMeas : Measurable w)
    (hf : ∀ i, MemLp (fun x ↦ (Real.sqrt (w x) : ℂ) * f i x) 2 volume)
    (hfBound : ∀ i, (∫ x, w x * ‖f i x‖ ^ 2) ≤ C)
    (hfConcentrates : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ i in atTop,
      (∫ x in (Metric.closedBall i R ∪ Metric.closedBall (-i) R)ᶜ,
        w x * ‖f i x‖ ^ 2) < ε)
    (hφ : AEStronglyMeasurable φ volume)
    (hReproduce : ∀ i, f i (q * i) = ∫ x, f i (q * i + x) * φ x)
    (hG : MemLp G 2 volume)
    (hDom : ∀ᶠ i in atTop, ∀ᵐ x ∂volume,
      Real.sqrt (w (q * i)) / Real.sqrt (w (q * i + x)) * ‖φ x‖ ≤ G x)
    (hDiag : ∃ A ≥ 0, ∀ᶠ x in atTop, |Real.sqrt (w x) * eNorm x| ≤ A)
    (hRatio : ∃ B ≥ 0, ∀ᶠ x in atTop, Real.sqrt (w x) / Real.sqrt (w (q * x)) ≤ B)
    (hdEven : Function.Even d)
    (hdFactor : ∀ᶠ x in atTop,
      d x = (((Real.sqrt (w x) * eNorm x) *
        (Real.sqrt (w x) / Real.sqrt (w (q * x))) : ℝ) : ℂ) *
        ((Real.sqrt (w (q * x)) : ℂ) * f x (q * x))) :
    ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R, ‖d x‖ ≤ ε := by
  let c (x : ℝ) : ℂ :=
    (((Real.sqrt (w x) * eNorm x) * (Real.sqrt (w x) / Real.sqrt (w (q * x)))) : ℝ)
  have hc : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (norm ∘ c) := by
    obtain ⟨A, hA, hA'⟩ := hDiag
    obtain ⟨B, hB, hB'⟩ := hRatio
    refine ⟨A * B, eventually_map.mpr ?_⟩
    filter_upwards [hA', hB'] with x hx hy
    have hr : 0 ≤ Real.sqrt (w x) / Real.sqrt (w (q * x)) := by positivity
    dsimp only [Function.comp_apply, c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul hx hy hr hA
  have hEval := tendsto_weighted_eval_dilation_zero_of_twoWindows hq0 hq1 hw hwMeas
    hf hfBound hfConcentrates hφ hReproduce hG hDom
  have hD : Tendsto d atTop (𝓝 0) := (Filter.isBoundedUnder_le_mul_tendsto_zero hc hEval).congr'
    (hdFactor.mono fun _ h ↦ h.symm)
  intro ε hε
  obtain ⟨S, hS⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hD ε hε)
  refine ⟨max 0 S, le_max_left _ _, fun x hx ↦ ?_⟩
  have hTail (t : ℝ) (ht : max 0 S ≤ t) : ‖d t‖ ≤ ε := by
    have h := hS t ((le_max_right _ _).trans ht)
    rw [dist_zero_right] at h
    exact h.le
  by_cases hx' : max 0 S ≤ x
  · exact hTail x hx'
  · have hneg : max 0 S ≤ -x := by
      by_contra! hn
      exact hx ⟨by linarith, (lt_of_not_ge hx').le⟩
    rw [← hdEven x]
    exact hTail (-x) hneg

end RiemannMasullo
