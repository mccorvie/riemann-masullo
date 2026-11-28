module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshRecursion_Isolated
import RiemannMasullo.Ch10_TraceSpectral.Sec3_MellinDecay
import RiemannMasullo.Ch10_TraceSpectral.Sec3_ArchimedeanFlows
import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-!
# Uniform Mellin decay and conductor bounds for radial multipliers (`#7406`)

1. `bruhatFirstOrder_compact`: compactly supported first-order directional derivative on
   `BruhatCompactSupport C𝔽`, with `tsupport` preserved.
2. `integral_bruhatFirstOrder_mul_ideleClassNormTwist` and its `N`-fold iteration.
3. `bruhatFirstOrder_compact_radialMul_ker` and `bruhatFirstOrder_compact_radialMul_normSection`.
4. `exists_uniform_radialMul_spectralLevel`: spectral level `κ`, uniform conductor bound `A₀`,
   compact period subgroup `kg`, and polynomial decay uniform over all radial multipliers `T` in
   terms of `∑ r ≤ N, sup_{|t| ≤ δ} ‖iteratedDeriv r T t‖`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing Pointwise

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section UniformMellinDecay

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => logIdeleClassNorm F

lemma tsupport_bruhatDirectionalDeriv_subset (b : Multiplicative ℝ →ₜ* C𝔽)
    (φ : BruhatCompactSupport C𝔽) :
    tsupport (bruhatDirectionalDeriv b φ.val) ⊆ tsupport φ.val := by
  refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
  by_contra hnot
  have hopen : IsOpen (tsupport φ.val)ᶜ := isClosed_closure.isOpen_compl
  have hcont : ContinuousAt (fun t : ℝ ↦ x * b (Multiplicative.ofAdd t)) 0 :=
    continuousAt_const.mul (b.continuous.continuousAt.comp continuous_ofAdd.continuousAt)
  have h0 : x * b (Multiplicative.ofAdd 0) ∈ (tsupport φ.val)ᶜ := by
    simpa [ofAdd_zero, map_one, mul_one] using hnot
  have hev : (fun t : ℝ ↦ φ.val (x * b (Multiplicative.ofAdd t))) =ᶠ[𝓝 (0 : ℝ)]
      fun _ : ℝ ↦ (0 : ℂ) := by
    filter_upwards [hcont.preimage_mem_nhds (hopen.mem_nhds h0)] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hd : deriv (fun t : ℝ ↦ φ.val (x * b (Multiplicative.ofAdd t))) 0 = 0 := by
    rw [hev.deriv_eq, deriv_const]
  exact hx hd

/-- First-order directional derivative `bruhatFirstOrder b` restricted to `BruhatCompactSupport C𝔽`. -/
def bruhatFirstOrder_compact (b : Multiplicative ℝ →ₜ* C𝔽) (φ : BruhatCompactSupport C𝔽) :
    BruhatCompactSupport C𝔽 :=
  ⟨bruhatDirectionalDeriv b φ.val,
    bruhatDirectionalDeriv_mem_smooth b ⟨φ.val, φ.property.1⟩,
    φ.property.2.of_isClosed_subset isClosed_closure (tsupport_bruhatDirectionalDeriv_subset b φ)⟩

@[simp]
lemma bruhatFirstOrder_compact_apply (b : Multiplicative ℝ →ₜ* C𝔽) (φ : BruhatCompactSupport C𝔽)
    (x : C𝔽) :
    (bruhatFirstOrder_compact b φ).val x = bruhatDirectionalDeriv b φ.val x := rfl

lemma bruhatFirstOrder_compact_add (b : Multiplicative ℝ →ₜ* C𝔽)
    (φ₁ φ₂ : BruhatCompactSupport C𝔽) :
    bruhatFirstOrder_compact b (φ₁ + φ₂) =
      bruhatFirstOrder_compact b φ₁ + bruhatFirstOrder_compact b φ₂ := by
  refine Subtype.ext (funext fun x ↦ ?_)
  have h1 := ((mem_bruhatSmoothSubmodule_iff _).mp φ₁.property.1) 1
  have h2 := ((mem_bruhatSmoothSubmodule_iff _).mp φ₂.property.1) 1
  exact congrFun (bruhatDirectionalDeriv_add b ⟨φ₁.val, h1⟩ ⟨φ₂.val, h2⟩) x

lemma bruhatFirstOrder_compact_smul (b : Multiplicative ℝ →ₜ* C𝔽) (c : ℂ)
    (φ : BruhatCompactSupport C𝔽) :
    bruhatFirstOrder_compact b (c • φ) = c • bruhatFirstOrder_compact b φ := by
  refine Subtype.ext (funext fun x ↦ ?_)
  have h1 := ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1) 1
  exact congrFun (bruhatDirectionalDeriv_smul b ⟨φ.val, h1⟩ c) x

lemma tsupport_bruhatFirstOrder_iter_subset (b : Multiplicative ℝ →ₜ* C𝔽)
    (φ : BruhatCompactSupport C𝔽) (n : ℕ) :
    tsupport ((bruhatFirstOrder_compact b)^[n] φ).val ⊆ tsupport φ.val := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (tsupport_bruhatDirectionalDeriv_subset b _).trans ih

private lemma continuous_addMonoidHom_eq_mul {g : ℝ → ℝ} (hg : Continuous g)
    (hadd : ∀ x y : ℝ, g (x + y) = g x + g y) (x : ℝ) :
    g x = g 1 * x := by
  let h : ℝ →+ ℝ := ⟨⟨g, by
    have h0 : g 0 = g 0 + g 0 := by simpa using hadd 0 0
    linarith⟩, hadd⟩
  have hrat : ∀ q : ℚ, g q = g 1 * (q : ℝ) := by
    intro q
    have hden_ne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    have hq_eq : (q.den : ℕ) • (q : ℝ) = (q.num : ℤ) • (1 : ℝ) := by
      simp only [nsmul_eq_mul, zsmul_eq_mul, mul_one]
      have hq : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
        exact_mod_cast Rat.mul_den_eq_num (q := q)
      linarith
    have h1 : (q.den : ℕ) • g (q : ℝ) = (q.num : ℤ) • g 1 := by
      calc (q.den : ℕ) • g (q : ℝ) = h ((q.den : ℕ) • (q : ℝ)) := (map_nsmul h q.den (q : ℝ)).symm
        _ = h ((q.num : ℤ) • (1 : ℝ)) := by rw [hq_eq]
        _ = (q.num : ℤ) • g 1 := map_zsmul h q.num (1 : ℝ)
    simp only [nsmul_eq_mul, zsmul_eq_mul] at h1
    have h2 : g q = ((q.num : ℝ) / (q.den : ℝ)) * g 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff hden_ne]
      linarith
    rw [h2, Rat.cast_def, mul_comm]
  have h_eq : g = fun t : ℝ ↦ g 1 * t :=
    Rat.denseRange_cast.equalizer hg (continuous_const.mul continuous_id) (funext fun q ↦ hrat q)
  exact congrFun h_eq x

private lemma ideleClassNormTwist_orbit_hasDerivAt_zero (b : Multiplicative ℝ →ₜ* C𝔽)
    (ψ : PontryaginDual C𝔽) (w : ℂ) :
    HasDerivAt (fun u : ℝ ↦ ideleClassNormTwist (F := F) ψ w (b (Multiplicative.ofAdd u)))
      (bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1) 0 := by
  have hψ_sm : IsBruhatContDiff 1 (fun g : C𝔽 ↦ (ψ g : ℂ)) :=
    (mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth ψ) 1
  have hψ0 : HasDerivAt (fun u : ℝ ↦ (ψ (b (Multiplicative.ofAdd u)) : ℂ))
      (bruhatDirectionalDeriv b (fun g : C𝔽 ↦ (ψ g : ℂ)) 1) 0 := by
    simpa only [one_mul] using hasDerivAt_bruhatDirectionalDeriv b hψ_sm 1
  let logf (u : ℝ) : ℝ := Real.log ((ideleClassNorm F (b (Multiplicative.ofAdd u))).val : ℝ)
  have hlogf_cont : Continuous logf :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      ((isProperMap_ideleClassNorm F).continuous.comp
        (b.continuous.comp continuous_ofAdd)))).log fun u ↦
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  have hlogf_add (u₁ u₂ : ℝ) : logf (u₁ + u₂) = logf u₁ + logf u₂ := by
    dsimp only [logf]
    rw [ofAdd_add, map_mul, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ u : ℝ, logf u = c * u :=
    ⟨logf 1, continuous_addMonoidHom_eq_mul hlogf_cont hlogf_add⟩
  have hnorm_eq (u : ℝ) :
      ((((ideleClassNorm F (b (Multiplicative.ofAdd u))).val : ℝ) : ℂ) ^ w) =
        Complex.exp (((c : ℂ) * w) * (u : ℂ)) := by
    have hp : 0 < ((ideleClassNorm F (b (Multiplicative.ofAdd u))).val : ℝ) :=
      NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
    change Complex.exp ((logf u : ℂ) * w) = _
    rw [hc u, Complex.ofReal_mul]
    congr 1; ring
  have hnorm_d : HasDerivAt
      (fun u : ℝ ↦ ((((ideleClassNorm F (b (Multiplicative.ofAdd u))).val : ℝ) : ℂ) ^ w))
      ((c : ℂ) * w) 0 := by
    simp_rw [hnorm_eq]
    have hlin : HasDerivAt (fun u : ℝ ↦ ((c : ℂ) * w) * (u : ℂ)) (((c : ℂ) * w) * 1) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul ((c : ℂ) * w))
    simpa using hlin.cexp
  have hprod : HasDerivAt
      (fun u : ℝ ↦ ideleClassNormTwist (F := F) ψ w (b (Multiplicative.ofAdd u)))
      (bruhatDirectionalDeriv b (fun g : C𝔽 ↦ (ψ g : ℂ)) 1 * 1 + 1 * ((c : ℂ) * w)) 0 := by
    have h0_ψ : (ψ (b (Multiplicative.ofAdd 0)) : ℂ) = 1 := by simp
    have h0_n : ((((ideleClassNorm F (b (Multiplicative.ofAdd 0))).val : ℝ) : ℂ) ^ w) = 1 := by
      simp
    have hmul := hψ0.mul hnorm_d
    change HasDerivAt (fun u : ℝ ↦ (ψ (b (Multiplicative.ofAdd u)) : ℂ) *
      (((ideleClassNorm F (b (Multiplicative.ofAdd u))).val : ℝ) : ℂ) ^ w) _ 0
    convert hmul using 1
    simp
  have heq_deriv :
      bruhatDirectionalDeriv b (fun g : C𝔽 ↦ (ψ g : ℂ)) 1 * 1 + 1 * ((c : ℂ) * w) =
        bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1 := by
    have hd := hprod.deriv
    simpa [bruhatDirectionalDeriv, one_mul] using hd.symm
  rwa [← heq_deriv]

lemma integral_bruhatFirstOrder_mul_ideleClassNormTwist (b : Multiplicative ℝ →ₜ* C𝔽)
    (φ : BruhatCompactSupport C𝔽) (ψ : PontryaginDual C𝔽) (w : ℂ) :
    ∫ g : C𝔽, (bruhatFirstOrder_compact b φ).val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽 =
      -(bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1) *
        ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽 := by
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hφ_cont : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hφ_sm : IsBruhatContDiff 1 φ.val :=
    (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 1
  have htw_cont : Continuous (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) := by
    have hρc : Continuous (fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
    have hexp : Continuous (fun g : C𝔽 ↦ (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w) := by
      have heq : (fun g : C𝔽 ↦ (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w) =
          fun g : C𝔽 ↦ Complex.exp ((Real.log ((ideleClassNorm F g).val : ℝ) : ℂ) * w) := by
        ext g
        have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), Complex.ofReal_log hp.le]
      rw [heq]
      exact ((Complex.continuous_ofReal.comp
        (hρc.log fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')).mul continuous_const).cexp
    exact (continuous_subtype_val.comp ψ.continuous).mul hexp
  let F_int (t : ℝ) (g : C𝔽) : ℂ :=
    φ.val (g * b (Multiplicative.ofAdd t)) * ideleClassNormTwist (F := F) ψ w g
  let F'_int (t : ℝ) (g : C𝔽) : ℂ :=
    bruhatDirectionalDeriv b φ.val (g * b (Multiplicative.ofAdd t)) * ideleClassNormTwist (F := F) ψ w g
  let K₁ : Set C𝔽 := tsupport φ.val
  let K₂ : Set C𝔽 := (fun t : ℝ ↦ (b (Multiplicative.ofAdd t))⁻¹) '' Metric.closedBall 0 1
  let K : Set C𝔽 := K₁ * K₂
  have hK₁ : IsCompact K₁ := φ.property.2.isCompact
  have hK₂ : IsCompact K₂ :=
    (isCompact_closedBall (0 : ℝ) 1).image
      (b.continuous.comp continuous_ofAdd).inv
  have hK : IsCompact K := hK₁.mul hK₂
  have hK_prod : IsCompact (K ×ˢ Metric.closedBall (0 : ℝ) 1) :=
    hK.prod (isCompact_closedBall (0 : ℝ) 1)
  have hF'_cont : Continuous (fun p : C𝔽 × ℝ ↦ ‖F'_int p.2 p.1‖) := by
    have hd_cont : Continuous (bruhatDirectionalDeriv b φ.val) :=
      bruhatDirectionalDeriv_continuous b hφ_sm
    have hmul_cont : Continuous (fun p : C𝔽 × ℝ ↦ p.1 * b (Multiplicative.ofAdd p.2)) :=
      continuous_fst.mul (b.continuous.comp (continuous_ofAdd.comp continuous_snd))
    exact ((hd_cont.comp hmul_cont).mul (htw_cont.comp continuous_fst)).norm
  obtain ⟨M₀, hM₀⟩ := hK_prod.exists_bound_of_continuousOn hF'_cont.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  let bound : C𝔽 → ℝ := K.indicator fun _ ↦ M
  have h_bound : ∀ g : C𝔽, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F'_int t g‖ ≤ bound g := by
    intro g t ht
    by_cases hg : g ∈ K
    · simp only [bound, Set.indicator_of_mem hg]
      have hmem : (g, t) ∈ K ×ˢ Metric.closedBall (0 : ℝ) 1 :=
        ⟨hg, Metric.ball_subset_closedBall ht⟩
      have hbd := hM₀ (g, t) hmem
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hbd
      exact hbd.trans (le_max_left _ _)
    · simp only [bound, Set.indicator_of_notMem hg]
      have hnot_tsupp : g * b (Multiplicative.ofAdd t) ∉ K₁ := by
        intro hmem
        apply hg
        exact Set.mem_mul.mpr ⟨g * b (Multiplicative.ofAdd t), hmem, (b (Multiplicative.ofAdd t))⁻¹,
          ⟨t, Metric.ball_subset_closedBall ht, rfl⟩, by simp [mul_assoc]⟩
      have hnot_d : bruhatDirectionalDeriv b φ.val (g * b (Multiplicative.ofAdd t)) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hd ↦
          hnot_tsupp (tsupport_bruhatDirectionalDeriv_subset b φ hd)
      simp [F'_int, hnot_d]
  have hbound_int : Integrable bound μ𝔽 :=
    (integrableOn_const (C := M) (s := K) hK.measure_lt_top.ne).integrable_indicator
      hK.isClosed.measurableSet
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F_int t) μ𝔽 := by
    refine Filter.Eventually.of_forall fun t ↦ ?_
    exact ((hφ_cont.comp (continuous_id.mul continuous_const)).mul htw_cont).aestronglyMeasurable
  have hF_int0 : Integrable (F_int 0) μ𝔽 := by
    have heq0 : F_int 0 = fun g ↦ φ.val g * ideleClassNormTwist (F := F) ψ w g := by
      ext g; simp [F_int, ofAdd_zero, map_one, mul_one]
    rw [heq0]
    exact (hφ_cont.mul htw_cont).integrable_of_hasCompactSupport φ.property.2.mul_right
  have hF'_meas0 : AEStronglyMeasurable (F'_int 0) μ𝔽 :=
    ((bruhatDirectionalDeriv_continuous b hφ_sm).comp
      (continuous_id.mul continuous_const)).mul htw_cont |>.aestronglyMeasurable
  have h_diff : ∀ᵐ g ∂μ𝔽, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ ↦ F_int u g) (F'_int t g) t := by
    refine ae_of_all _ fun g t _ ↦ ?_
    have h0 := hasDerivAt_bruhatDirectionalDeriv b hφ_sm (g * b (Multiplicative.ofAdd t))
    have hs : HasDerivAt (fun u : ℝ ↦ u - t) 1 t := (hasDerivAt_id t).sub_const t
    have hcomp := h0.scomp_of_eq t hs (sub_self t).symm
    rw [one_smul] at hcomp
    have hfn : (fun u : ℝ ↦ φ.val (g * b (Multiplicative.ofAdd t) * b (Multiplicative.ofAdd (u - t)))) =
        fun u : ℝ ↦ φ.val (g * b (Multiplicative.ofAdd u)) := by
      ext u
      rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
    dsimp only [Function.comp_def] at hcomp
    rw [hfn] at hcomp
    exact hcomp.mul_const _
  obtain ⟨_, h_lhs⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one) hF_meas hF_int0 hF'_meas0
    (ae_of_all _ h_bound) hbound_int h_diff
  have h_lhs' : HasDerivAt (fun t : ℝ ↦ ∫ g : C𝔽, F_int t g ∂μ𝔽)
      (∫ g : C𝔽, (bruhatFirstOrder_compact b φ).val g *
        ideleClassNormTwist (F := F) ψ w g ∂μ𝔽) 0 := by
    convert h_lhs using 2
    ext g
    simp [F'_int, bruhatFirstOrder_compact_apply, ofAdd_zero, map_one, mul_one]
  let I : ℂ := ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽
  let θ (t : ℝ) : ℂ := ideleClassNormTwist (F := F) ψ w (b (Multiplicative.ofAdd t))
  have h_eq_shift (t : ℝ) : (∫ g : C𝔽, F_int t g ∂μ𝔽) = (θ t)⁻¹ * I := by
    have hc := integral_mul_left_eq_self (μ := μ𝔽) (fun g ↦ φ.val g *
      ideleClassNormTwist (F := F) ψ w (g * (b (Multiplicative.ofAdd t))⁻¹))
      (b (Multiplicative.ofAdd t))
    calc ∫ g : C𝔽, F_int t g ∂μ𝔽
        = ∫ g : C𝔽, φ.val (b (Multiplicative.ofAdd t) * g) *
            ideleClassNormTwist (F := F) ψ w g ∂μ𝔽 := by
          refine integral_congr_ae (.of_forall fun g ↦ ?_)
          dsimp only [F_int]
          rw [mul_comm g (b (Multiplicative.ofAdd t))]
      _ = ∫ g : C𝔽, φ.val (b (Multiplicative.ofAdd t) * g) *
            ideleClassNormTwist (F := F) ψ w
              ((b (Multiplicative.ofAdd t) * g) * (b (Multiplicative.ofAdd t))⁻¹) ∂μ𝔽 := by
          refine integral_congr_ae (.of_forall fun g ↦ ?_)
          dsimp only
          rw [mul_comm (b (Multiplicative.ofAdd t)) g, mul_inv_cancel_right]
      _ = ∫ g : C𝔽, φ.val g *
            ideleClassNormTwist (F := F) ψ w (g * (b (Multiplicative.ofAdd t))⁻¹) ∂μ𝔽 := hc
      _ = ∫ g : C𝔽, (θ t)⁻¹ * (φ.val g * ideleClassNormTwist (F := F) ψ w g) ∂μ𝔽 := by
          refine integral_congr_ae (.of_forall fun g ↦ ?_)
          have htw_mul (x y : C𝔽) : ideleClassNormTwist (F := F) ψ w (x * y⁻¹) =
              ideleClassNormTwist (F := F) ψ w x * (ideleClassNormTwist (F := F) ψ w y)⁻¹ := by
            have hny : 0 < ((ideleClassNorm F y).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
            have hnx : 0 < ((ideleClassNorm F x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
            have hnxy : 0 < ((ideleClassNorm F (x * y⁻¹)).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
            have hρ_eq : ((ideleClassNorm F (x * y⁻¹)).val : ℝ) =
                ((ideleClassNorm F x).val : ℝ) / ((ideleClassNorm F y).val : ℝ) := by
              rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul,
                NNReal.coe_inv, div_eq_mul_inv]
            have hc_pow : (((ideleClassNorm F (x * y⁻¹)).val : ℝ) : ℂ) ^ w =
                ((((ideleClassNorm F x).val : ℝ) : ℂ) ^ w) *
                  ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ w)⁻¹ := by
              rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hnxy.ne'),
                Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hnx.ne'),
                Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hny.ne'),
                ← Complex.exp_neg, ← Complex.exp_add, hρ_eq,
                ← Complex.ofReal_log (div_pos hnx hny).le, Real.log_div hnx.ne' hny.ne',
                ← Complex.ofReal_log hnx.le, ← Complex.ofReal_log hny.le, Complex.ofReal_sub]
              congr 1; ring
            have hψ_inv : (((ψ y)⁻¹ : Circle) : ℂ) = (ψ y : ℂ)⁻¹ := by
              have h1 : (ψ y : ℂ) * (((ψ y)⁻¹ : Circle) : ℂ) = ((ψ y * (ψ y)⁻¹ : Circle) : ℂ) :=
                (Circle.coe_mul (ψ y) (ψ y)⁻¹).symm
              rw [mul_inv_cancel, Circle.coe_one] at h1
              exact (eq_inv_of_mul_eq_one_right h1).symm
            change ((ψ (x * y⁻¹) : ℂ) * (((ideleClassNorm F (x * y⁻¹)).val : ℝ) : ℂ) ^ w) =
              ((ψ x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ w) *
                ((ψ y : ℂ) * (((ideleClassNorm F y).val : ℝ) : ℂ) ^ w)⁻¹
            rw [map_mul, map_inv, Circle.coe_mul, hψ_inv, hc_pow, mul_inv]
            ring
          change φ.val g * ideleClassNormTwist (F := F) ψ w (g * (b (Multiplicative.ofAdd t))⁻¹) = _
          rw [htw_mul g (b (Multiplicative.ofAdd t))]
          change φ.val g * (ideleClassNormTwist (F := F) ψ w g * (θ t)⁻¹) = _
          ring
      _ = (θ t)⁻¹ * I := integral_const_mul _ _
  have hθ0 : θ 0 = 1 := by
    change ((ψ (b (Multiplicative.ofAdd 0)) : ℂ) *
      (((ideleClassNorm F (b (Multiplicative.ofAdd 0))).val : ℝ) : ℂ) ^ w) = 1
    simp
  have hθ_d := ideleClassNormTwist_orbit_hasDerivAt_zero (F := F) b ψ w
  have hθ_inv_d : HasDerivAt (fun t : ℝ ↦ (θ t)⁻¹ * I)
      ((-(bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1) / (θ 0) ^ 2) * I) 0 :=
    (hθ_d.inv (by change θ 0 ≠ 0; rw [hθ0]; exact one_ne_zero)).mul_const I
  rw [hθ0, one_pow, div_one] at hθ_inv_d
  have h_rhs : HasDerivAt (fun t : ℝ ↦ ∫ g : C𝔽, F_int t g ∂μ𝔽)
      (-(bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1) * I) 0 := by
    simpa only [h_eq_shift] using hθ_inv_d
  exact h_lhs'.unique h_rhs

lemma norm_iterated_bruhatFirstOrder_mul_ideleClassNormTwist (b : Multiplicative ℝ →ₜ* C𝔽)
    (N : ℕ) (φ : BruhatCompactSupport C𝔽) (ψ : PontryaginDual C𝔽) (w : ℂ) :
    ‖bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1‖ ^ N *
        ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ =
      ‖∫ g : C𝔽, ((bruhatFirstOrder_compact b)^[N] φ).val g *
        ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ := by
  induction N generalizing φ with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', pow_succ', mul_assoc, ih φ,
        integral_bruhatFirstOrder_mul_ideleClassNormTwist, norm_mul, norm_neg]

lemma bruhatFirstOrder_compact_radialMul_ker (b : Multiplicative ℝ →ₜ* C𝔽)
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (φ : BruhatCompactSupport C𝔽) :
    bruhatFirstOrder_compact b (radialMul T hT φ) = radialMul T hT (bruhatFirstOrder_compact b φ) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  have hT_sm : IsBruhatContDiff 1 (fun g : C𝔽 ↦ T (logNorm g)) :=
    isBruhatSmooth_logProfile (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ) hT 1
  have hφ_sm : IsBruhatContDiff 1 φ.val :=
    (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 1
  have h0 : bruhatDirectionalDeriv b (fun g : C𝔽 ↦ T (logNorm g)) x = 0 := by
    have hconst : (fun t : ℝ ↦ T (logNorm (x * b (Multiplicative.ofAdd t)))) =
        fun _ : ℝ ↦ T (logNorm x) := by
      ext t
      have hk : ideleClassNorm F (b (Multiplicative.ofAdd t)) = 1 := hb _
      change T (Real.log ((continuousIdeleClassNorm F (x * b (Multiplicative.ofAdd t))).val : ℝ)) = _
      rw [map_mul, show continuousIdeleClassNorm F (b (Multiplicative.ofAdd t)) = 1 from hk, mul_one]
      rfl
    change deriv (fun t : ℝ ↦ T (logNorm (x * b (Multiplicative.ofAdd t)))) 0 = 0
    rw [hconst, deriv_const]
  have hmul := congrFun (bruhatDirectionalDeriv_mul b hT_sm hφ_sm) x
  change bruhatDirectionalDeriv b (fun g : C𝔽 ↦ T (logNorm g) * φ.val g) x =
    T (logNorm x) * bruhatDirectionalDeriv b φ.val x
  have heq : (fun g : C𝔽 ↦ T (logNorm g) * φ.val g) =
      (fun g : C𝔽 ↦ T (logNorm g)) * φ.val := rfl
  rw [heq, hmul]
  simp only [Pi.add_apply, Pi.mul_apply, h0, mul_zero, add_zero]

lemma bruhatFirstOrder_compact_iter_radialMul_ker (b : Multiplicative ℝ →ₜ* C𝔽)
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (φ : BruhatCompactSupport C𝔽) (n : ℕ) :
    (bruhatFirstOrder_compact b)^[n] (radialMul T hT φ) =
      radialMul T hT ((bruhatFirstOrder_compact b)^[n] φ) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        bruhatFirstOrder_compact_radialMul_ker b hb T hT φ, ih]

private lemma contDiff_iteratedDeriv_top {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (q : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv q f) := by
  induction q with
  | zero => simpa using hf
  | succ q ih =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2

lemma bruhatFirstOrder_compact_radialMul_normSection (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (φ : BruhatCompactSupport C𝔽) :
    let b : Multiplicative ℝ →ₜ* C𝔽 := τ.comp positiveRealLogEquiv.symm
    bruhatFirstOrder_compact b (radialMul T hT φ) =
      radialMul (deriv T) ((contDiff_infty_iff_deriv.mp hT).2) φ +
        radialMul T hT (bruhatFirstOrder_compact b φ) := by
  intro b
  refine Subtype.ext (funext fun x ↦ ?_)
  have hT_sm : IsBruhatContDiff 1 (fun g : C𝔽 ↦ T (logNorm g)) :=
    isBruhatSmooth_logProfile (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ) hT 1
  have hφ_sm : IsBruhatContDiff 1 φ.val :=
    (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 1
  have hdT : bruhatDirectionalDeriv b (fun g : C𝔽 ↦ T (logNorm g)) x = deriv T (logNorm x) := by
    have hlog (t : ℝ) : logNorm (x * b (Multiplicative.ofAdd t)) = logNorm x + t := by
      have h1 : ideleClassNorm F (b (Multiplicative.ofAdd t)) =
          positiveRealLogEquiv.symm (Multiplicative.ofAdd t) := hτ _
      have h2 := positiveRealLogEquiv_apply (positiveRealLogEquiv.symm (Multiplicative.ofAdd t))
      rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h2
      change Real.log ((continuousIdeleClassNorm F (x * b (Multiplicative.ofAdd t))).val : ℝ) = _
      rw [map_mul, show continuousIdeleClassNorm F (b (Multiplicative.ofAdd t)) =
          positiveRealLogEquiv.symm (Multiplicative.ofAdd t) from h1,
        Units.val_mul, NNReal.coe_mul, Real.log_mul
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
      exact congrArg (logNorm x + ·) h2.symm
    change deriv (fun t : ℝ ↦ T (logNorm (x * b (Multiplicative.ofAdd t)))) 0 = deriv T (logNorm x)
    simp_rw [hlog]
    rw [deriv_comp_const_add, add_zero]
  have hmul := congrFun (bruhatDirectionalDeriv_mul b hT_sm hφ_sm) x
  have heq : (fun g : C𝔽 ↦ T (logNorm g) * φ.val g) =
      (fun g : C𝔽 ↦ T (logNorm g)) * φ.val := rfl
  change bruhatDirectionalDeriv b (fun g : C𝔽 ↦ T (logNorm g) * φ.val g) x =
    deriv T (logNorm x) * φ.val x + T (logNorm x) * bruhatDirectionalDeriv b φ.val x
  rw [heq, hmul]
  simp only [Pi.add_apply, Pi.mul_apply, hdT]
  ring

private lemma bruhatFirstOrder_compact_iter_add (b : Multiplicative ℝ →ₜ* C𝔽) (n : ℕ)
    (φ₁ φ₂ : BruhatCompactSupport C𝔽) :
    (bruhatFirstOrder_compact b)^[n] (φ₁ + φ₂) =
      (bruhatFirstOrder_compact b)^[n] φ₁ + (bruhatFirstOrder_compact b)^[n] φ₂ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, bruhatFirstOrder_compact_add]

private lemma binom_sum_shift (a b : ℕ → ℂ) (n : ℕ) :
    (∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * a (q + 1) * b (n + 1 - (q + 1))) +
        (∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * a q * b (n + 1 - q)) =
      ∑ q ∈ Finset.range (n + 2), ((n + 1).choose q : ℂ) * a q * b (n + 1 - q) := by
  let f (q : ℕ) : ℂ := a q * b (n + 1 - q)
  have h1 : (∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * a (q + 1) * b (n + 1 - (q + 1))) =
      (∑ q ∈ Finset.range n, (n.choose q : ℂ) * f (q + 1)) + f (n + 1) := by
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
    simp only [f, mul_assoc]
  have h2 : (∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * a q * b (n + 1 - q)) =
      f 0 + ∑ q ∈ Finset.range n, (n.choose (q + 1) : ℂ) * f (q + 1) := by
    rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul]
    simp only [f, mul_assoc]
    rw [add_comm]
  have h3 : (∑ q ∈ Finset.range (n + 2), ((n + 1).choose q : ℂ) * a q * b (n + 1 - q)) =
      f 0 + (∑ q ∈ Finset.range n, ((n.choose q : ℂ) + (n.choose (q + 1) : ℂ)) * f (q + 1)) +
        f (n + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, one_mul, one_mul]
    have hmid : (∑ q ∈ Finset.range n, ((n + 1).choose (q + 1) : ℂ) * a (q + 1) *
          b (n + 1 - (q + 1))) =
        ∑ q ∈ Finset.range n, ((n.choose q : ℂ) + (n.choose (q + 1) : ℂ)) * f (q + 1) := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Nat.choose_succ_succ n q, Nat.cast_add, add_comm (n.choose q : ℂ)]
      simp only [f, mul_assoc]
    simp only [f, mul_assoc] at hmid ⊢
    rw [hmid]
    ring
  rw [h1, h2, h3]
  have hsum : (∑ q ∈ Finset.range n, (n.choose q : ℂ) * f (q + 1)) +
        ∑ q ∈ Finset.range n, (n.choose (q + 1) : ℂ) * f (q + 1) =
      ∑ q ∈ Finset.range n, ((n.choose q : ℂ) + (n.choose (q + 1) : ℂ)) * f (q + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    ring
  rw [← hsum]
  ring

lemma bruhatFirstOrder_compact_iter_radialMul_normSection (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (φ : BruhatCompactSupport C𝔽) (n : ℕ) (g : C𝔽) :
    let b : Multiplicative ℝ →ₜ* C𝔽 := τ.comp positiveRealLogEquiv.symm
    ((bruhatFirstOrder_compact b)^[n] (radialMul T hT φ)).val g =
      ∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * iteratedDeriv q T (logNorm g) *
        ((bruhatFirstOrder_compact b)^[n - q] φ).val g := by
  intro b
  induction n generalizing T hT φ with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, bruhatFirstOrder_compact_radialMul_normSection τ hτ T hT φ,
        bruhatFirstOrder_compact_iter_add b n]
      change ((bruhatFirstOrder_compact b)^[n]
          (radialMul (deriv T) ((contDiff_infty_iff_deriv.mp hT).2) φ)).val g +
        ((bruhatFirstOrder_compact b)^[n]
          (radialMul T hT (bruhatFirstOrder_compact b φ))).val g = _
      rw [ih (deriv T) ((contDiff_infty_iff_deriv.mp hT).2) φ,
        ih T hT (bruhatFirstOrder_compact b φ)]
      have h_shift_left :
          ∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * iteratedDeriv q (deriv T) (logNorm g) *
              ((bruhatFirstOrder_compact b)^[n - q] φ).val g =
            ∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * iteratedDeriv (q + 1) T (logNorm g) *
              ((bruhatFirstOrder_compact b)^[n + 1 - (q + 1)] φ).val g := by
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [← iteratedDeriv_succ', show n + 1 - (q + 1) = n - q by omega]
      have h_shift_right :
          ∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * iteratedDeriv q T (logNorm g) *
              ((bruhatFirstOrder_compact b)^[n - q] (bruhatFirstOrder_compact b φ)).val g =
            ∑ q ∈ Finset.range (n + 1), (n.choose q : ℂ) * iteratedDeriv q T (logNorm g) *
              ((bruhatFirstOrder_compact b)^[n + 1 - q] φ).val g := by
        refine Finset.sum_congr rfl fun q hq ↦ ?_
        have hqn : q ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
        rw [← Function.iterate_succ_apply, show (n - q).succ = n + 1 - q by omega]
      rw [h_shift_left, h_shift_right]
      exact binom_sum_shift (fun q ↦ iteratedDeriv q T (logNorm g))
        (fun k ↦ ((bruhatFirstOrder_compact b)^[k] φ).val g) n

private lemma uniform_one_add_sum_pow_mul_le' {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (N : ℕ) {g K₀ : ℝ} (K : ι → ℝ) (hg : 0 ≤ g) (h0 : g ≤ K₀)
    (hK : ∀ i, x i ^ N * g ≤ K i) :
    (1 + ∑ i, x i) ^ N * g ≤ ((Fintype.card ι : ℝ) + 1) ^ N * (K₀ + ∑ i, K i) := by
  have hK0 (i : ι) : 0 ≤ K i := (mul_nonneg (pow_nonneg (hx i) N) hg).trans (hK i)
  have hK₀ : 0 ≤ K₀ := hg.trans h0
  have hsumK : 0 ≤ ∑ i, K i := Finset.sum_nonneg fun i _ ↦ hK0 i
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hs : ∑ i, x i = 0 := Finset.sum_eq_zero fun i _ ↦ (hι.false i).elim
    rw [hs, add_zero, one_pow, one_mul]
    calc g ≤ K₀ := h0
      _ ≤ 1 * (K₀ + ∑ i, K i) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_pow₀ hcard) (by linarith)
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max x
    have hsum : ∑ i, x i ≤ Fintype.card ι * x i₀ := by
      calc ∑ i, x i ≤ ∑ _i : ι, x i₀ := Finset.sum_le_sum fun i _ ↦ hi₀ i
        _ = Fintype.card ι * x i₀ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases le_or_gt (x i₀) 1 with h1 | h1
    · have hbase : 1 + ∑ i, x i ≤ (Fintype.card ι : ℝ) + 1 := by
        have : (Fintype.card ι : ℝ) * x i₀ ≤ Fintype.card ι :=
          mul_le_of_le_one_right (Nat.cast_nonneg _) h1
        linarith
      have hnn : 0 ≤ 1 + ∑ i, x i := add_nonneg zero_le_one (Finset.sum_nonneg fun i _ ↦ hx i)
      calc (1 + ∑ i, x i) ^ N * g ≤ ((Fintype.card ι : ℝ) + 1) ^ N * g :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hbase N) hg
        _ ≤ ((Fintype.card ι : ℝ) + 1) ^ N * (K₀ + ∑ i, K i) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have hbase : 1 + ∑ i, x i ≤ ((Fintype.card ι : ℝ) + 1) * x i₀ := by linarith
      have hnn : 0 ≤ 1 + ∑ i, x i := add_nonneg zero_le_one (Finset.sum_nonneg fun i _ ↦ hx i)
      have hKi : K i₀ ≤ K₀ + ∑ i, K i := by
        have := Finset.single_le_sum (f := K) (fun i _ ↦ hK0 i) (Finset.mem_univ i₀)
        linarith
      calc (1 + ∑ i, x i) ^ N * g ≤ (((Fintype.card ι : ℝ) + 1) * x i₀) ^ N * g :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hbase N) hg
        _ = ((Fintype.card ι : ℝ) + 1) ^ N * (x i₀ ^ N * g) := by rw [mul_pow, mul_assoc]
        _ ≤ ((Fintype.card ι : ℝ) + 1) ^ N * (K₀ + ∑ i, K i) :=
            mul_le_mul_of_nonneg_left ((hK i₀).trans hKi) (by positivity)

private lemma norm_ideleClassNormTwist_le_wt (ψ : PontryaginDual C𝔽) {W : ℝ} {w : ℂ}
    (hw : |w.re| ≤ W) (g : C𝔽) :
    ‖ideleClassNormTwist (F := F) ψ w g‖ ≤
      ((ideleClassNorm F g).val : ℝ) ^ W + ((ideleClassNorm F g).val : ℝ) ^ (-W) := by
  let ρ : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hρ : 0 < ρ := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnorm : ‖ideleClassNormTwist (F := F) ψ w g‖ = ρ ^ w.re := by
    change ‖((ψ g : Circle) : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ w)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hρ]
  rw [hnorm]
  have hw1 : -W ≤ w.re ∧ w.re ≤ W := abs_le.mp hw
  by_cases h1 : 1 ≤ ρ
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hw1.2)
      (le_add_of_nonneg_right (Real.rpow_nonneg hρ.le _))
  · have hlt : ρ ≤ 1 := le_of_not_ge h1
    exact le_trans (Real.rpow_le_rpow_of_exponent_ge hρ hlt hw1.1)
      (le_add_of_nonneg_left (Real.rpow_nonneg hρ.le _))

private lemma abs_logNorm_le_of_mem_tsupport (φ : BruhatCompactSupport C𝔽) {δ : ℝ}
    (hsupp : ∀ y, φ.val y ≠ 0 → |logNorm y| ≤ δ) {y : C𝔽} (hy : y ∈ tsupport φ.val) :
    |logNorm y| ≤ δ := by
  have hclosed : IsClosed {g : C𝔽 | |logNorm g| ≤ δ} :=
    isClosed_le continuous_logNorm.abs continuous_const
  exact closure_minimal (fun g hg ↦ hsupp g hg) hclosed hy

private lemma exists_uniform_ker_flow_decay (φ : BruhatCompactSupport C𝔽) {δ : ℝ}
    (hsupp : ∀ y, φ.val y ≠ 0 → |logNorm y| ≤ δ) (b : Multiplicative ℝ →ₜ* C𝔽)
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (W : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (M : ℕ → ℝ),
      (∀ r ≤ N, 0 ≤ M r) → (∀ r ≤ N, ∀ t, |t| ≤ δ → ‖iteratedDeriv r T t‖ ≤ M r) →
      ∀ (ψ : PontryaginDual C𝔽) (w : ℂ), |w.re| ≤ W →
        ‖bruhatDirectionalDeriv b (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1‖ ^ N *
          ‖∫ g : C𝔽, (radialMul T hT φ).val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ ≤
            C * ∑ r ∈ Finset.range (N + 1), M r := by
  let Wt (g : C𝔽) : ℝ := ((ideleClassNorm F g).val : ℝ) ^ W + ((ideleClassNorm F g).val : ℝ) ^ (-W)
  have hρc : Continuous (fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hWt : Continuous Wt :=
    (hρc.rpow_const fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').add
      (hρc.rpow_const fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  let φN := (bruhatFirstOrder_compact b)^[N] φ
  have hφN_c : Continuous φN.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φN.property.1)
  let C : ℝ := ∫ g : C𝔽, ‖φN.val g‖ * Wt g ∂μ𝔽
  have hC0 : 0 ≤ C := integral_nonneg fun g ↦
    mul_nonneg (norm_nonneg _) (add_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
  refine ⟨C, hC0, fun T hT M hM0 hMb ψ w hw ↦ ?_⟩
  rw [norm_iterated_bruhatFirstOrder_mul_ideleClassNormTwist b N (radialMul T hT φ) ψ w,
    bruhatFirstOrder_compact_iter_radialMul_ker b hb T hT φ N]
  have hint_wt : Integrable (fun g : C𝔽 ↦ M 0 * (‖φN.val g‖ * Wt g)) μ𝔽 :=
    (((hφN_c.norm.mul hWt).integrable_of_hasCompactSupport φN.property.2.norm.mul_right).const_mul _)
  have hbd (g : C𝔽) : ‖(radialMul T hT φN).val g * ideleClassNormTwist (F := F) ψ w g‖ ≤
      M 0 * (‖φN.val g‖ * Wt g) := by
    rw [radialMul_apply, norm_mul, norm_mul]
    by_cases hg : φN.val g = 0
    · simp [hg]
    · have hlog : |logNorm g| ≤ δ :=
        abs_logNorm_le_of_mem_tsupport φ hsupp (tsupport_bruhatFirstOrder_iter_subset b φ N (subset_tsupport _ hg))
      have hT0 := hMb 0 (Nat.zero_le N) (logNorm g) hlog
      rw [iteratedDeriv_zero] at hT0
      have htw := norm_ideleClassNormTwist_le_wt (F := F) ψ hw g
      calc ‖T (logNorm g)‖ * ‖φN.val g‖ * ‖ideleClassNormTwist (F := F) ψ w g‖
          ≤ M 0 * ‖φN.val g‖ * Wt g :=
            mul_le_mul (mul_le_mul_of_nonneg_right hT0 (norm_nonneg _)) htw (norm_nonneg _)
              (mul_nonneg (hM0 0 (Nat.zero_le N)) (norm_nonneg _))
        _ = M 0 * (‖φN.val g‖ * Wt g) := by ring
  have h_le : ‖∫ g : C𝔽, (radialMul T hT φN).val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ ≤
      C * M 0 := by
    refine (norm_integral_le_of_norm_le hint_wt (ae_of_all _ hbd)).trans_eq ?_
    rw [integral_const_mul, mul_comm]
  have hM_single : M 0 ≤ ∑ r ∈ Finset.range (N + 1), M r :=
    Finset.single_le_sum (f := M) (fun r hr ↦ hM0 r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
      (Finset.mem_range.mpr (Nat.zero_lt_succ N))
  exact h_le.trans (mul_le_mul_of_nonneg_left hM_single hC0)

private lemma exists_uniform_rad_flow_decay (φ : BruhatCompactSupport C𝔽) {δ : ℝ}
    (hsupp : ∀ y, φ.val y ≠ 0 → |logNorm y| ≤ δ) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (W : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (M : ℕ → ℝ),
      (∀ r ≤ N, 0 ≤ M r) → (∀ r ≤ N, ∀ t, |t| ≤ δ → ‖iteratedDeriv r T t‖ ≤ M r) →
      ∀ (ψ : PontryaginDual C𝔽) (w : ℂ), |w.re| ≤ W →
        ‖bruhatDirectionalDeriv (τ.comp positiveRealLogEquiv.symm)
            (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) ψ w g) 1‖ ^ N *
          ‖∫ g : C𝔽, (radialMul T hT φ).val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ ≤
            C * ∑ r ∈ Finset.range (N + 1), M r := by
  let b : Multiplicative ℝ →ₜ* C𝔽 := τ.comp positiveRealLogEquiv.symm
  let Wt (g : C𝔽) : ℝ := ((ideleClassNorm F g).val : ℝ) ^ W + ((ideleClassNorm F g).val : ℝ) ^ (-W)
  have hρc : Continuous (fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hWt : Continuous Wt :=
    (hρc.rpow_const fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').add
      (hρc.rpow_const fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  let c (q : ℕ) : ℝ := (N.choose q : ℝ) *
    ∫ g : C𝔽, ‖((bruhatFirstOrder_compact b)^[N - q] φ).val g‖ * Wt g ∂μ𝔽
  have hc_nn (q : ℕ) : 0 ≤ c q := mul_nonneg (Nat.cast_nonneg _)
    (integral_nonneg fun g ↦ mul_nonneg (norm_nonneg _)
      (add_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
        (Real.rpow_nonneg (NNReal.coe_nonneg _) _)))
  let C : ℝ := ∑ q ∈ Finset.range (N + 1), c q
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun q _ ↦ hc_nn q
  refine ⟨C, hC0, fun T hT M hM0 hMb ψ w hw ↦ ?_⟩
  rw [norm_iterated_bruhatFirstOrder_mul_ideleClassNormTwist b N (radialMul T hT φ) ψ w]
  let bound_g (g : C𝔽) : ℝ := ∑ q ∈ Finset.range (N + 1),
    (N.choose q : ℝ) * M q * ‖((bruhatFirstOrder_compact b)^[N - q] φ).val g‖ * Wt g
  have hint_q (q : ℕ) : Integrable (fun g : C𝔽 ↦
      (N.choose q : ℝ) * M q * ‖((bruhatFirstOrder_compact b)^[N - q] φ).val g‖ * Wt g) μ𝔽 := by
    let φq := (bruhatFirstOrder_compact b)^[N - q] φ
    have hφq_c : Continuous φq.val :=
      continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φq.property.1)
    have heq : (fun g : C𝔽 ↦ (N.choose q : ℝ) * M q * ‖φq.val g‖ * Wt g) =
        fun g ↦ ((N.choose q : ℝ) * M q) * (‖φq.val g‖ * Wt g) := by ext g; ring
    rw [heq]
    exact ((hφq_c.norm.mul hWt).integrable_of_hasCompactSupport φq.property.2.norm.mul_right).const_mul _
  have hint_bound : Integrable bound_g μ𝔽 := by
    have hint_fin : ∀ S : Finset ℕ, Integrable (fun g : C𝔽 ↦
        ∑ q ∈ S, (N.choose q : ℝ) * M q *
          ‖((bruhatFirstOrder_compact b)^[N - q] φ).val g‖ * Wt g) μ𝔽 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          exact (hint_q a).add ih
    exact hint_fin (Finset.range (N + 1))
  have hbd (g : C𝔽) : ‖((bruhatFirstOrder_compact b)^[N] (radialMul T hT φ)).val g *
      ideleClassNormTwist (F := F) ψ w g‖ ≤ bound_g g := by
    rw [bruhatFirstOrder_compact_iter_radialMul_normSection τ hτ T hT φ N g, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq ↦ ?_)
    have hqN : q ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
    by_cases hg : ((bruhatFirstOrder_compact b)^[N - q] φ).val g = 0
    · have hb_eq : (τ.comp positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* C𝔽) = b := rfl
      rw [hb_eq, hg]
      simp
    · have hlog : |logNorm g| ≤ δ :=
        abs_logNorm_le_of_mem_tsupport φ hsupp
          (tsupport_bruhatFirstOrder_iter_subset b φ (N - q) (subset_tsupport _ hg))
      have hTq := hMb q hqN (logNorm g) hlog
      have htw := norm_ideleClassNormTwist_le_wt (F := F) ψ hw g
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTq (Nat.cast_nonneg _)) (norm_nonneg _))
        htw (norm_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM0 q hqN)) (norm_nonneg _))
  refine (norm_integral_le_of_norm_le hint_bound (ae_of_all _ hbd)).trans ?_
  have hint_eq : ∫ g : C𝔽, bound_g g ∂μ𝔽 = ∑ q ∈ Finset.range (N + 1), c q * M q := by
    dsimp only [bound_g]
    rw [integral_finsetSum _ fun q _ ↦ hint_q q]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have heq : (fun g : C𝔽 ↦ (N.choose q : ℝ) * M q * ‖((bruhatFirstOrder_compact b)^[N - q] φ).val g‖ * Wt g) =
        fun g ↦ M q * ((N.choose q : ℝ) * (‖((bruhatFirstOrder_compact b)^[N - q] φ).val g‖ * Wt g)) := by
      ext g; ring
    rw [heq, integral_const_mul, mul_comm (M q)]
    dsimp only [c]
    rw [integral_const_mul]
  rw [hint_eq]
  have hterm (q : ℕ) (hq : q ∈ Finset.range (N + 1)) : c q * M q ≤ C * M q :=
    mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := c) (fun r _ ↦ hc_nn r) hq)
      (hM0 q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)))
  exact (Finset.sum_le_sum hterm).trans_eq (Finset.mul_sum _ _ _).symm

section
open Classical

/-- Uniform spectral level, period subgroup, conductor bound, and uniform polynomial Mellin decay
over all smooth radial multipliers `T` of a fixed test `ψ` supported in `|logNorm y| ≤ δ`. -/
theorem exists_uniform_radialMul_spectralLevel (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) {δ : ℝ} (_hδ : 0 ≤ δ) (ψ : BruhatCompactSupport C𝔽)
    (hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ) :
    ∃ (κ : PontryaginDual C𝔽 → ℝ) (A₀ : ℝ) (kg : Subgroup C𝔽),
      IsBruhatGoodSubgroup kg ∧
      (∀ χ, 0 ≤ κ χ) ∧
      (∀ χ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, χ (τ t) = 1) →
        ∀ w : InfinitePlace F, if hw : w.IsReal then
            ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ 1 + κ χ
          else
            let p := (complexHeckeCharacter_parameters χ w
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
            ‖p.1‖ ≤ 1 + κ χ ∧ (p.2.natAbs : ℝ) ≤ 1 + κ χ) ∧
      (∃ C d : ℕ, ∀ T_cnt : ℕ, {χ : PontryaginDual C𝔽 | (∀ t : ℝ≥0ˣ, χ (τ t) = 1) ∧
          (∀ u ∈ kg, χ u = 1) ∧ κ χ ≤ (T_cnt : ℝ)}.encard ≤ ((C * (T_cnt + 1) ^ d : ℕ) : ℕ∞)) ∧
      (∀ (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (χ : PontryaginDual C𝔽) (w : ℂ),
        (∫ g : C𝔽, (radialMul T hT ψ).val g * ideleClassNormTwist (F := F) χ w g ∂μ𝔽) ≠ 0 →
          (∀ u ∈ kg, χ u = 1) ∧ heckeLogDiscriminantConductor χ ≤ A₀) ∧
      ∀ (W : ℝ) (N : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (M : ℕ → ℝ),
        (∀ r ≤ N, 0 ≤ M r) → (∀ r ≤ N, ∀ t, |t| ≤ δ → ‖iteratedDeriv r T t‖ ≤ M r) →
        ∀ χ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, χ (τ t) = 1) → ∀ w : ℂ, |w.re| ≤ W →
          (1 + ‖w‖ + κ χ) ^ N *
            ‖∫ g : C𝔽, (radialMul T hT ψ).val g * ideleClassNormTwist (F := F) χ w g ∂μ𝔽‖ ≤
              K * ∑ r ∈ Finset.range (N + 1), M r := by
  obtain ⟨kg, hkg, hinv, -⟩ := (mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1 0
  obtain ⟨r, b, hb, C, d, hcount⟩ := idelicExplicitFormula_normOneFourier_count τ hτ kg hkg
  obtain ⟨m, Yf, hYf, hlink⟩ := exists_flows_archimedean_parameters_le τ hτ
  obtain ⟨N_cond, hN_fin, hlevel⟩ := bruhatCompactSupport_radial_conductor_level ψ μ𝔽
  let A₀ : ℝ := Real.log (Int.natAbs (NumberField.discr F)) +
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Real.log (v.asIdeal.absNorm : ℝ) * (N_cond v : ℝ)
  let fb (j : Fin r) (χ : PontryaginDual C𝔽) : ℝ :=
    ‖bruhatDirectionalDeriv (b j) (fun x : C𝔽 ↦ (χ x : ℂ)) 1‖
  let fY (i : Fin m) (χ : PontryaginDual C𝔽) : ℝ :=
    ‖bruhatDirectionalDeriv (Yf i) (fun x : C𝔽 ↦ (χ x : ℂ)) 1‖
  let κ (χ : PontryaginDual C𝔽) : ℝ := ∑ j, fb j χ + ∑ i, fY i χ
  have hfb0 (χ : PontryaginDual C𝔽) : 0 ≤ ∑ j, fb j χ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hfY0 (χ : PontryaginDual C𝔽) : 0 ≤ ∑ i, fY i χ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hfb (χ : PontryaginDual C𝔽) (j : Fin r) : fb j χ ≤ κ χ := by
    have := Finset.single_le_sum (f := fun j ↦ fb j χ) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
    linarith [hfY0 χ]
  have hfY (χ : PontryaginDual C𝔽) (i : Fin m) : fY i χ ≤ κ χ := by
    have := Finset.single_le_sum (f := fun i ↦ fY i χ) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    linarith [hfb0 χ]
  refine ⟨κ, A₀, kg, hkg, fun χ ↦ add_nonneg (hfb0 χ) (hfY0 χ),
    fun χ hχ ↦ hlink χ hχ (1 + κ χ) (fun i ↦ by linarith [hfY χ i]), ⟨C, d, fun T_cnt ↦ ?_⟩,
    fun T hT χ w hw ↦ ⟨?_, ?_⟩, fun W N ↦ ?_⟩
  · refine le_trans ?_ (hcount T_cnt)
    refine le_trans (Set.encard_mono ?_) (Subtype.val_injective.injOn.encard_image).le
    rintro χ ⟨hχ, hper, hκ⟩
    exact ⟨⟨χ, hχ⟩, ⟨fun u hu ↦ hper u.val hu, fun j ↦ (hfb χ j).trans hκ⟩, rfl⟩
  · intro u hu
    let mod : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    have hn : ideleClassNorm F u = 1 :=
      MonoidHom.mem_ker.mp (compactSubgroup_le_modulation_ker mod kg hkg.isCompact hu)
    have htw : ideleClassNormTwist (F := F) χ w u = (χ u : ℂ) := by
      change ((χ u : Circle) : ℂ) * (((ideleClassNorm F u).val : ℝ) : ℂ) ^ w = _
      rw [hn]; simp
    have hlog_u (g : C𝔽) : logNorm (u * g) = logNorm g := by
      change Real.log ((ideleClassNorm F (u * g)).val : ℝ) = Real.log ((ideleClassNorm F g).val : ℝ)
      rw [map_mul, hn, one_mul]
    let f (g : C𝔽) := (radialMul T hT ψ).val g * ideleClassNormTwist (F := F) χ w g
    have hm (g : C𝔽) : f (u * g) = (χ u : ℂ) * f g := by
      dsimp only [f]
      rw [radialMul_apply, radialMul_apply, hlog_u g, hinv ⟨u, hu⟩ g, map_mul, htw]
      ring
    have he := integral_mul_left_eq_self (μ := μ𝔽) f u
    simp_rw [hm, integral_const_mul] at he
    exact Circle.ext ((mul_eq_right₀ hw).mp he)
  · let w_rad (t : ℝ≥0ˣ) : ℂ := T (Real.log (t.val : ℝ)) * ((t.val : ℝ) : ℂ) ^ w
    have hw_rad : (∫ g : C𝔽, ψ.val g * (χ g : ℂ) * w_rad (ideleClassNorm F g) ∂μ𝔽) ≠ 0 := by
      refine fun h0 ↦ hw (h0 ▸ integral_congr_ae (.of_forall fun g ↦ ?_))
      change T (logNorm g) * ψ.val g *
        ((χ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w) = _
      dsimp only [w_rad, logIdeleClassNorm]
      ring
    have hlev := hlevel χ w_rad hw_rad
    have hlog_v (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
        0 ≤ Real.log (v.asIdeal.absNorm : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le)
    have support_weight (b_fn : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ)
        (hb_le : ∀ v, b_fn v ≤ N_cond v) :
        (Function.support (fun v ↦ Real.log (v.asIdeal.absNorm : ℝ) * (b_fn v : ℝ))).Finite :=
      hN_fin.subset fun v hv hn ↦ hv (by simp [Nat.eq_zero_of_le_zero ((hb_le v).trans_eq hn)])
    unfold heckeLogDiscriminantConductor
    dsimp only [A₀]
    refine add_le_add_right (finsum_le_finsum (support_weight _ fun v ↦ Nat.sInf_le (hlev v))
      (support_weight N_cond fun _ ↦ le_rfl) fun v ↦ ?_) _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sInf_le (hlev v)) (hlog_v v)
  · obtain ⟨K0, hK0nn, hK0⟩ := exists_uniform_rad_flow_decay ψ hsupp τ hτ W 0
    obtain ⟨Krad, hKrad_nn, hKrad⟩ := exists_uniform_rad_flow_decay ψ hsupp τ hτ W N
    choose Kb hKb_nn hKb using fun j ↦ exists_uniform_ker_flow_decay ψ hsupp (b j) (hb j) W N
    choose KY hKY_nn hKY using fun i ↦ exists_uniform_ker_flow_decay ψ hsupp (Yf i) (hYf i) W N
    let Kall : Option (Fin r ⊕ Fin m) → ℝ := fun o ↦ o.elim Krad (Sum.elim Kb KY)
    have hKall_nn (o : Option (Fin r ⊕ Fin m)) : 0 ≤ Kall o := by
      rcases o with _ | (j | i) <;> simp [Kall, hKrad_nn, hKb_nn, hKY_nn]
    let Ktotal : ℝ := ((Fintype.card (Option (Fin r ⊕ Fin m)) : ℝ) + 1) ^ N * (K0 + ∑ o, Kall o)
    have hKtotal_nn : 0 ≤ Ktotal :=
      mul_nonneg (pow_nonneg (by positivity) N) (add_nonneg hK0nn (Finset.sum_nonneg fun o _ ↦ hKall_nn o))
    refine ⟨Ktotal, hKtotal_nn, fun T hT M hM0 hMb χ hχ w hw ↦ ?_⟩
    let x : Option (Fin r ⊕ Fin m) → ℝ := fun o ↦ o.elim ‖w‖ (Sum.elim (fun j ↦ fb j χ) (fun i ↦ fY i χ))
    have hsum : 1 + ‖w‖ + κ χ = 1 + ∑ o, x o := by
      simp only [x, Fintype.sum_option, Fintype.sum_sum_type, Option.elim_none, Option.elim_some,
        Sum.elim_inl, Sum.elim_inr, κ]
      ring
    rw [hsum]
    let MS : ℝ := ∑ r ∈ Finset.range (N + 1), M r
    have hM0_le : M 0 ≤ MS := Finset.single_le_sum (f := M)
      (fun r hr ↦ hM0 r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
      (Finset.mem_range.mpr (Nat.zero_lt_succ N))
    have h0_bd : ‖∫ g : C𝔽, (radialMul T hT ψ).val g * ideleClassNormTwist (F := F) χ w g ∂μ𝔽‖ ≤
        K0 * MS := by
      have h := hK0 T hT M (fun r hr ↦ hM0 r (hr.trans (Nat.zero_le N)))
        (fun r hr ↦ hMb r (hr.trans (Nat.zero_le N))) χ w hw
      rw [pow_zero, one_mul, Finset.range_one, Finset.sum_singleton] at h
      exact h.trans (mul_le_mul_of_nonneg_left hM0_le hK0nn)
    have hres := uniform_one_add_sum_pow_mul_le' x (fun o ↦ by
      rcases o with _ | (j | i) <;> exact norm_nonneg _) N (fun o ↦ Kall o * MS) (norm_nonneg _)
      h0_bd fun o ↦ by
        rcases o with _ | (j | i)
        · have h := hKrad T hT M hM0 hMb χ w hw
          rwa [bruhatDirectionalDeriv_ideleClassNormTwist_normSection τ hτ χ hχ w] at h
        · have h := hKb j T hT M hM0 hMb χ w hw
          rwa [bruhatDirectionalDeriv_ideleClassNormTwist_of_mem_ker (b j) (hb j) χ w] at h
        · have h := hKY i T hT M hM0 hMb χ w hw
          rwa [bruhatDirectionalDeriv_ideleClassNormTwist_of_mem_ker (Yf i) (hYf i) χ w] at h
    refine hres.trans_eq ?_
    have hsum_k : K0 * MS + ∑ o, Kall o * MS = (K0 + ∑ o, Kall o) * MS := by
      rw [← Finset.sum_mul, ← add_mul]
    rw [hsum_k]
    dsimp only [Ktotal, MS]
    ring

end

end UniformMellinDecay

end RiemannMasullo.Isolated.CoshPositiveWidth

