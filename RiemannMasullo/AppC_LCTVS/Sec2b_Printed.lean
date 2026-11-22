module

public import RiemannMasullo.AppC_LCTVS.Sec2b
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries

/-! # Appendix C.1.5: the printed implication from Schwartz to nuclear Fréchet spaces -/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Paper: Paragraph after Theorem C.1.5.11, p. 668. As printed: a Schwartz Fréchet
stage is nuclear. `isSchwartzTVS_of_isNuclearTVS` gives the implication in Example C.1.5.10,
and `limitSubspaceTopology_eq_iff_liftsBoundedSets` uses Schwartz stages. See ERRATA F3. -/
def Printed.isNuclearTVS_of_isSchwartzFrechet : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E],
    IsFrechetTVS E → IsSchwartzTVS E → IsNuclearTVS.{0} E

section KotheCounterexample

open Filter Topology Set

private abbrev KL2 := lp (fun _ : ℕ ↦ ℂ) 2

private def kw (n : ℕ) : ℝ := Real.log (n + 3)

private theorem one_le_kw (n : ℕ) : 1 ≤ kw n := by
  unfold kw
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_three
  have : (3 : ℝ) ≤ n + 3 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

private def kotheSub : Submodule ℂ (ℕ → KL2) where
  carrier := {y | ∀ k n, (y k : ℕ → ℂ) n = (kw n : ℂ) ^ k * (y 0 : ℕ → ℂ) n}
  add_mem' := by
    intro a b ha hb k n
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [Pi.add_apply, lp.coeFn_add, ha k n, hb k n]
    ring
  zero_mem' := by
    intro k n
    simp
  smul_mem' := by
    intro c a ha k n
    simp only [Set.mem_ofPred_eq] at ha
    simp only [Pi.smul_apply, lp.coeFn_smul, smul_eq_mul, ha k n]
    ring

private abbrev KE := ↥kotheSub

private theorem kotheSub_isClosed : IsClosed (kotheSub : Set (ℕ → KL2)) := by
  have : (kotheSub : Set (ℕ → KL2)) =
      ⋂ k, ⋂ n, {y : ℕ → KL2 | (y k : ℕ → ℂ) n = (kw n : ℂ) ^ k * (y 0 : ℕ → ℂ) n} := by
    ext y; simp only [Set.mem_iInter, Set.mem_ofPred_eq]; rfl
  rw [this]
  refine isClosed_iInter fun k ↦ isClosed_iInter fun n ↦ isClosed_eq ?_ ?_
  · exact ((lp.lipschitzWith_one_eval 2 n).continuous).comp (continuous_apply k)
  · exact continuous_const.mul (((lp.lipschitzWith_one_eval 2 n).continuous).comp (continuous_apply 0))

private theorem kotheE_frechet : IsFrechetTVS KE := by
  have : IsUniformAddGroup KE := IsUniformAddGroup.comap kotheSub.subtype
  refine ⟨inferInstance, inferInstance,
    TopologicalSpace.MetrizableSpace.subtype (kotheSub : Set (ℕ → KL2)), ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := KE)]
  exact kotheSub_isClosed.completeSpace_coe

private theorem kotheE_norm_le (y : KE) {k K : ℕ} (h : k ≤ K) : ‖(y : ℕ → KL2) k‖ ≤ ‖(y : ℕ → KL2) K‖ := by
  refine lp.norm_mono (by norm_num) fun n ↦ ?_
  rw [y.2 k n, y.2 K n, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (by linarith [one_le_kw n])]
  gcongr
  · exact one_le_kw n

private theorem kothe_dom (p : Seminorm ℂ KE) (hp : Continuous p) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : KE, p y ≤ C * ‖(y : ℕ → KL2) K‖ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (LinearMap.withSeminorms_induced (withSeminorms_pi fun _ : ℕ ↦ norm_withSeminorms ℂ KL2)
      kotheSub.subtype) p hp
  refine ⟨s.sup Sigma.fst, C, C.2, fun y ↦ (hC y).trans ?_⟩
  change (C : ℝ) * _ ≤ _
  gcongr
  refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi ↦ ?_
  change ‖(y : ℕ → KL2) i.1‖ ≤ _
  exact kotheE_norm_le y (Finset.le_sup (f := Sigma.fst) hi)

private theorem kothe_tail (y : KE) (K N : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ n ≥ N, 1 ≤ c * kw n) :
    ‖(y : ℕ → KL2) K - ∑ i ∈ Finset.range N, lp.single 2 i (((y : ℕ → KL2) K : ℕ → ℂ) i)‖
      ≤ c * ‖(y : ℕ → KL2) (K+1)‖ := by
  calc _ ≤ ‖(c : ℂ) • (y : ℕ → KL2) (K+1)‖ := lp.norm_mono (by norm_num) fun n ↦ ?_
    _ = c * ‖(y : ℕ → KL2) (K+1)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
  simp only [lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_smul, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, lp.coeFn_single, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hn : n < N
  · simp [hn]; positivity
  · simp only [hn, ite_false, sub_zero]
    rw [y.2 K n, y.2 (K+1) n, smul_eq_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc,
      Real.norm_of_nonneg (by linarith [one_le_kw n]), pow_succ]
    have h1 := hN n (not_lt.mp hn)
    have h2 : 0 ≤ kw n ^ K * ‖((y : ℕ → KL2) 0 : ℕ → ℂ) n‖ := by
      have := one_le_kw n; positivity
    nlinarith

private theorem kw_tendsto : Tendsto kw atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)

private theorem kothe_tb (K : ℕ) :
    TotallyBounded ((fun y : KE ↦ (y : ℕ → KL2) K) '' {y | ‖(y : ℕ → KL2) (K+1)‖ < 1}) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (kw_tendsto.eventually_ge_atTop (2 / ε))
  let R : (Fin N → ℂ) → KL2 := fun a ↦ ∑ i : Fin N, lp.single 2 (i : ℕ) (a i)
  have hR : Continuous R := continuous_finsetSum _ fun i _ ↦
    (lp.isometry_single (E := fun _ : ℕ ↦ ℂ) (p := 2) (i : ℕ)).continuous.comp (continuous_apply i)
  have hT : TotallyBounded (R '' Metric.closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image hR).totallyBounded
  obtain ⟨t, -, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded hT (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  let f := (y : ℕ → KL2) K
  have hf : ‖f‖ < 1 := (kotheE_norm_le y (Nat.le_succ K)).trans_lt hy
  have ha : (fun i : Fin N ↦ (f : ℕ → ℂ) i) ∈ Metric.closedBall (0 : Fin N → ℂ) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦
      ((lp.norm_apply_le_norm (by norm_num) f i).trans hf.le)
  obtain ⟨z, hz, hdz⟩ := Set.mem_iUnion₂.mp (hcover ⟨_, ha, rfl⟩)
  refine Set.mem_iUnion₂.mpr ⟨z, hz, ?_⟩
  have htail := kothe_tail y K N (ε / 2) (by positivity) fun n hn ↦ by
    calc (1 : ℝ) = (ε / 2) * (2 / ε) := by field_simp
      _ ≤ ε / 2 * kw n := by gcongr; exact hN n hn
  have hRa : R (fun i : Fin N ↦ (f : ℕ → ℂ) i) =
      ∑ i ∈ Finset.range N, lp.single 2 i ((f : ℕ → ℂ) i) :=
    Fin.sum_univ_eq_sum_range (fun i ↦ lp.single 2 i ((f : ℕ → ℂ) i)) N
  rw [Metric.mem_ball] at hdz ⊢
  have h1 : dist f (R (fun i : Fin N ↦ (f : ℕ → ℂ) i)) ≤ ε / 2 := by
    rw [dist_eq_norm, hRa]
    refine htail.trans ?_
    have : 0 ≤ ‖(y : ℕ → KL2) (K+1)‖ := norm_nonneg _
    have hy' : ‖(y : ℕ → KL2) (K+1)‖ < 1 := hy
    nlinarith
  linarith [dist_triangle f (R (fun i : Fin N ↦ (f : ℕ → ℂ) i)) z]

private theorem kotheE_schwartz : IsSchwartzTVS KE := by
  refine ⟨inferInstance, fun p hp ↦ ?_⟩
  obtain ⟨K, C, hC0, hC⟩ := kothe_dom p hp
  refine ⟨{y | ‖(y : ℕ → KL2) (K+1)‖ < 1}, ?_, ?_⟩
  · exact (isOpen_lt (continuous_norm.comp ((continuous_apply (K+1)).comp continuous_subtype_val))
      continuous_const).mem_nhds (by simp)
  · refine (@Metric.totallyBounded_iff KE p.toSeminormedAddCommGroup.toPseudoMetricSpace _).mpr ?_
    intro ε hε
    obtain ⟨t, hts, ht, hcov⟩ :=
      Metric.finite_approx_of_totallyBounded (kothe_tb K) (ε / (C + 1)) (by positivity)
    choose g hg using fun z : t ↦ hts z.2
    have : Finite t := ht.to_subtype
    refine ⟨Set.range g, Set.finite_range g, ?_⟩
    intro y hy
    obtain ⟨z, hz, hdz⟩ := Set.mem_iUnion₂.mp (hcov ⟨y, hy, rfl⟩)
    refine Set.mem_iUnion₂.mpr ⟨g ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
    rw [@Metric.mem_ball KE p.toSeminormedAddCommGroup.toPseudoMetricSpace,
      @dist_eq_norm KE p.toSeminormedAddCommGroup]
    change p (y - g ⟨z, hz⟩) < ε
    rw [Metric.mem_ball, dist_eq_norm] at hdz
    have hk : ((y - g ⟨z, hz⟩ : KE) : ℕ → KL2) K = (y : ℕ → KL2) K - z := by
      have h2 : ((g ⟨z, hz⟩ : KE) : ℕ → KL2) K = z := (hg ⟨z, hz⟩).2
      rw [Submodule.coe_sub, Pi.sub_apply, h2]
    calc p (y - g ⟨z, hz⟩) ≤ C * ‖(y : ℕ → KL2) K - z‖ := hk ▸ hC _
      _ ≤ C * (ε / (C + 1)) := by gcongr
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

private def kb (i : ℕ) : KE := ⟨fun k ↦ lp.single 2 i ((kw i : ℂ) ^ k), fun k n ↦ by
  change (lp.single 2 i ((kw i : ℂ) ^ k) : ℕ → ℂ) n =
    (kw n : ℂ) ^ k * (lp.single 2 i ((kw i : ℂ) ^ 0) : ℕ → ℂ) n
  rw [lp.coeFn_single, lp.coeFn_single]
  by_cases h : n = i
  · subst h; simp
  · simp [h]⟩

private theorem kb_smul_apply (a : ℂ) (i k : ℕ) :
    ((a • kb i : KE) : ℕ → KL2) k = lp.single 2 i (a * (kw i : ℂ) ^ k) := by
  change a • lp.single (E := fun _ : ℕ ↦ ℂ) 2 i ((kw i : ℂ) ^ k) = _
  rw [← lp.single_smul]; rfl

private theorem kb_sum_norm_sq (a : ℕ → ℂ) (n K : ℕ) :
    ‖((∑ j ∈ Finset.range n, a j • kb j : KE) : ℕ → KL2) K‖ ^ 2 =
      ∑ j ∈ Finset.range n, ‖a j‖ ^ 2 * kw j ^ (2 * K) := by
  have h1 : ((∑ j ∈ Finset.range n, a j • kb j : KE) : ℕ → KL2) K =
      ∑ j ∈ Finset.range n, lp.single 2 j (a j * (kw j : ℂ) ^ K) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ kb_smul_apply _ _ _
  have h2 := lp.norm_sum_single (E := fun _ : ℕ ↦ ℂ) (p := 2) (by norm_num)
    (fun j ↦ a j * (kw j : ℂ) ^ K) (Finset.range n)
  have h3 : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [h3, Real.rpow_natCast] at h2
  rw [h1, h2]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith [one_le_kw j])]
  ring

private theorem kw_not_summable (K : ℕ) : ¬ Summable (fun j : ℕ ↦ (kw j ^ (2 * K))⁻¹) := by
  intro hs
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 2 * K)).bound one_pos
  have hev : ∀ᶠ j : ℕ in atTop, ‖(1 : ℝ) / ((j + 3 : ℕ) : ℝ)‖ ≤ (kw j ^ (2 * K))⁻¹ := by
    have ht : Tendsto (fun j : ℕ ↦ (j : ℝ) + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually hlo] with j hj
    simp only [id, one_mul, norm_pow, Real.norm_eq_abs] at hj
    have hk : 0 < kw j ^ (2 * K) := by have := one_le_kw j; positivity
    have hj' : kw j ^ (2 * K) ≤ (j : ℝ) + 3 := by
      have h1 := one_le_kw j
      unfold kw at h1 ⊢
      rwa [abs_of_pos (show (0 : ℝ) < (j : ℝ) + 3 by positivity),
        abs_of_nonneg (show 0 ≤ Real.log ((j : ℝ) + 3) by linarith)] at hj
    rw [Real.norm_of_nonneg (by positivity), one_div]
    push_cast
    exact inv_anti₀ hk hj'
  have := Summable.of_norm_bounded_eventually_nat hs hev
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 3).mp this)

private def kbW (p : Seminorm ℂ KE) (j : ℕ) : WithLocalSeminorm p := kb j

private def ofW {p : Seminorm ℂ KE} (v : WithLocalSeminorm p) : KE := v

private theorem kothe_not_nuclear (h : IsNuclearTVS.{0} KE) : False := by
  have : ContinuousSMul ℝ KE :=
    MulAction.continuousSMul_compHom (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal
  let π0 : KE →ₗ[ℂ] KL2 := (LinearMap.proj 0).comp kotheSub.subtype
  let q0 : Seminorm ℂ KE := (normSeminorm ℂ KL2).comp π0
  have hq0 : Continuous q0 := by
    change Continuous (fun y : KE ↦ ‖(y : ℕ → KL2) 0‖)
    exact continuous_norm.comp ((continuous_apply 0).comp continuous_subtype_val)
  have hU : q0.ball 0 1 ∈ 𝓝 (0 : KE) := q0.ball_mem_nhds hq0 one_pos
  obtain ⟨V, hV, bV, cV, hVU, hAS⟩ := exists_localBanachMap_absolutelySumming KE h _ hU
    (q0.balanced_ball_zero 1) (q0.convex_ball 0 1)
  obtain ⟨C, hC0, hC⟩ := hAS
  set p := gaugeSeminorm bV cV (absorbent_nhds_zero hV) with hp_def
  set q := gaugeSeminorm (q0.balanced_ball_zero 1) (q0.convex_ball 0 1)
    (absorbent_nhds_zero hU) with hq_def
  have hq : ∀ x : KE, q x = ‖(x : ℕ → KL2) 0‖ := fun x ↦ by
    change gauge (q0.ball 0 1) x = _
    rw [show q0.ball 0 1 = (q0.restrictScalars ℝ).ball 0 1 from rfl, Seminorm.gauge_ball]
    rfl
  obtain ⟨K, D, hD0, hD⟩ := kothe_dom p (continuous_gauge cV hV)
  let c : ℕ → ℝ := fun j ↦ (kw j ^ (2 * K))⁻¹
  have hc0 : ∀ j, 0 ≤ c j := fun j ↦ by have := one_le_kw j; positivity
  have hcc : ∀ j, c j ^ 2 * kw j ^ (2 * K) = c j := fun j ↦ by
    have : kw j ^ (2 * K) ≠ 0 := by have := one_le_kw j; positivity
    simp only [c]
    field_simp
  let S : ℕ → ℝ := fun n ↦ ∑ j ∈ Finset.range n, c j
  have hS0 : ∀ n, 0 ≤ S n := fun n ↦ Finset.sum_nonneg fun j _ ↦ hc0 j
  let ιp : WithLocalSeminorm p →L[ℂ] LocalBanach p := UniformSpace.Completion.toComplL
  let x : ℕ → LocalBanach p := fun j ↦ (c j : ℂ) • ιp (kbW p j)
  have hweak : ∀ n, ∀ φ : LocalBanach p →L[ℂ] ℂ, ‖φ‖ ≤ 1 →
      ∑ j : Fin n, ‖φ (x j)‖ ≤ D * Real.sqrt (S n) := by
    intro n φ hφ
    let z : ℕ → ℂ := fun j ↦ φ (x j)
    let σ : ℕ → ℂ := fun j ↦ starRingEnd ℂ (z j) / (‖z j‖ : ℂ)
    have hσz : ∀ j, σ j * z j = (‖z j‖ : ℂ) := by
      intro j
      by_cases hz : z j = 0
      · simp [σ, hz]
      · have : (‖z j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
        simp only [σ]
        rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff this]
        ring
    have hσ : ∀ j, ‖σ j‖ ≤ 1 := by
      intro j
      simp only [σ, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
      exact div_self_le_one _
    let w' : WithLocalSeminorm p :=
      ∑ j ∈ Finset.range n, (σ j * c j) • kbW p j
    have hw' : ofW w' = ∑ j ∈ Finset.range n, (σ j * c j) • kb j := rfl
    have hφw : φ (ιp w') = ((∑ j ∈ Finset.range n, ‖z j‖ : ℝ) : ℂ) := by
      push_cast
      rw [← Finset.sum_congr rfl fun j _ ↦ hσz j]
      simp only [w', map_sum, map_smul, smul_eq_mul, z, x]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    calc ∑ j : Fin n, ‖φ (x j)‖ = ∑ j ∈ Finset.range n, ‖z j‖ :=
          Fin.sum_univ_eq_sum_range (fun j ↦ ‖z j‖) n
      _ = ‖φ (ιp w')‖ := by
          rw [hφw, Complex.norm_real, Real.norm_of_nonneg
            (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)]
      _ ≤ ‖φ‖ * ‖ιp w'‖ := φ.le_opNorm _
      _ ≤ 1 * ‖ιp w'‖ := by gcongr
      _ = p (ofW w') := by rw [one_mul]; exact localBanach_norm_coe p w'
      _ ≤ D * ‖((ofW w' : KE) : ℕ → KL2) K‖ := hD (ofW w')
      _ ≤ D * Real.sqrt (S n) := by
          gcongr
          rw [Real.le_sqrt (norm_nonneg _) (hS0 n), hw', kb_sum_norm_sq]
          refine Finset.sum_le_sum fun j _ ↦ ?_
          refine le_of_le_of_eq ?_ (hcc j)
          have hk : 0 ≤ kw j ^ (2 * K) := by have := one_le_kw j; positivity
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 j)]
          exact mul_le_of_le_one_left (hc0 j) (hσ j)
  have hstrong : ∀ (hh : q ≤ p) j, ‖localBanachMap p q hh (x j)‖ = c j := by
    intro hh j
    show ‖localBanachMap p q hh ((c j : ℂ) • ιp (kbW p j))‖ = c j
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hc0 j)]
    rw [show ιp (kbW p j) =
      (kbW p j : LocalBanach p) from rfl]
    erw [localBanachMap_coe p q hh (kbW p j), localBanach_norm_coe]
    change c j * q (kb j) = c j
    rw [hq]
    change c j * ‖lp.single (E := fun _ : ℕ ↦ ℂ) 2 j ((kw j : ℂ) ^ 0)‖ = c j
    rw [lp.norm_single (by norm_num)]
    simp
  have key : ∀ n, S n ≤ C * (D * Real.sqrt (S n)) := by
    intro n
    have := hC n (fun j : Fin n ↦ x j) (D * Real.sqrt (S n)) (by positivity) (hweak n)
    calc S n = ∑ i : Fin n, c i := (Fin.sum_univ_eq_sum_range (fun j ↦ c j) n).symm
      _ = ∑ i : Fin n, ‖localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU) (x i)‖ :=
          Finset.sum_congr rfl fun j _ ↦ (hstrong _ j).symm
      _ ≤ C * (D * Real.sqrt (S n)) := this
  have hbound : ∀ n, S n ≤ (C * D) ^ 2 := fun n ↦ by
    have h1 := key n
    have hs := Real.sq_sqrt (hS0 n)
    have hs0 := Real.sqrt_nonneg (S n)
    have hr : Real.sqrt (S n) ≤ C * D := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_lt_mul_of_pos_right hcon (lt_of_le_of_lt (mul_nonneg hC0 hD0) hcon)]
    rw [← hs]
    exact pow_le_pow_left₀ hs0 hr 2
  exact kw_not_summable K (summable_of_sum_range_le hc0 hbound)

end KotheCounterexample

/-- Paper: Paragraph after Theorem C.1.5.11, p. 668. Take the Fréchet space of
complex sequences x with `∑ₙ (log (n + 3))^(2k) |xₙ|² < ∞` for every k ≥ 0, with
the corresponding weighted ℓ² norms. Between two successive Hilbert completions
the inclusion has diagonal entries `1 / log (n + 3)`, which tend to zero, so the space
is Schwartz. No inclusion from a higher completion to unweighted ℓ² is Hilbert–Schmidt,
since `∑ₙ (log (n + 3))^(-2k)` diverges for every k. A nuclear connecting map to the
unweighted completion would factor such an inclusion through a continuous map from
some weighted completion, making that inclusion nuclear and hence Hilbert–Schmidt. -/
theorem Printed.isNuclearTVS_of_isSchwartzFrechet_false :
    ¬ Printed.isNuclearTVS_of_isSchwartzFrechet := fun hP ↦
  kothe_not_nuclear (hP KE kotheE_frechet kotheE_schwartz)

end RiemannMasullo
