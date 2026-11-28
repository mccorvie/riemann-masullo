module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalLevelIdentification
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWJetTrials

/-!
# Main's polar-free level for the rationals at every Sobolev order

`Sec4_RationalLevelIdentification` identifies `main`'s polar-free level for `ℚ` with no finite
place, at twist `1/2` and Sobolev order zero, with the level of the unweighted even
Paley–Wiener band. This file does the same at every Sobolev order `s ≥ 0`. The weight of `main`'s
local space, `intervalSobolevDensity 0 0 s` of the log-norm, is the weight
`realPWIntervalWeight 0 s` of the model band (`realPWIntervalWeight_zero_eq`), so the same map
`v ↦ N ^ (1/2) · 2 · v(N)`, normalized, is an isometry from the weighted model band into `main`'s
space at order `s` (`ratLevelIsometryOrder`), and `main`'s level is the image of the model level of
band vectors vanishing at the origin (`ratLevelOrder_eq_map`).

The model's level traces at order `s` then transfer to `main`'s level. For a test whose folded
form `ψ` vanishes outside `[a, b]` with `1 < a`, the trace on `main`'s level at order `s` less the
summed sharp orbital masses tends to minus the polar term (`ratMainLevelOrder_trace_tendsto`), as
at order zero. The sharp masses are compared through the order-zero identity `tsum_ratSharpMass`
and the order-zero limit, since the weighted limit `realPWSharpTraceLimit 0` does not depend on the
order.

Not covered: tests whose folded form meets `(0, 1]`, finite places, and other twists.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Topology NumberField ENNReal NNReal InnerProductSpace FourierTransform SchwartzMap

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

section Weight

/-- At base interval `{0}` the model weight at `t > 0` is `main`'s Sobolev density at `log t`. -/
theorem realPWIntervalWeight_zero_eq (s : ℝ) {t : ℝ} (ht : 0 < t) :
    realPWIntervalWeight 0 s t = intervalSobolevDensity 0 0 s (Real.log t) := by
  have hpos : 0 < 1 + Real.log t ^ 2 := by positivity
  simp only [realPWIntervalWeight, intervalSobolevDensity, abs_of_pos ht, mul_zero, zero_mul,
    neg_zero, Real.exp_zero, max_self, one_mul, Real.rpow_def_of_pos hpos]
  ring_nf

theorem realPWIntervalWeight_zero_neg (s x : ℝ) :
    realPWIntervalWeight 0 s (-x) = realPWIntervalWeight 0 s x := by
  simp only [realPWIntervalWeight, abs_neg]

theorem intervalSobolevDensity_zero_nonneg (s x : ℝ) : 0 ≤ intervalSobolevDensity 0 0 s x := by
  unfold intervalSobolevDensity
  positivity

theorem continuous_intervalSobolevDensity_zero (s : ℝ) :
    Continuous (intervalSobolevDensity 0 0 s) := by
  unfold intervalSobolevDensity
  refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul ?_
  exact (continuous_const.add (continuous_pow 2)).rpow_const fun x ↦ Or.inl (by positivity)

end Weight

section RatOrder

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instMeasurableSpaceInfiniteAdeleRing_riemannMasullo
  instRatSIdeleT2 instRatSAdeleT2

attribute [-instance] Quotient.instMeasurableSpace

local notation "Sq" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Jq" => SIdeleQuotient ℚ Sq
local notation "Hq" => sProjectedDiagonal ℚ Sq
local notation "eq" => ratRealCoordEquiv
local notation "μJq" => sLocalQuotientTamagawaMeasure ℚ Sq
local notation "Bq" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ Sq))
local notation "volume₁" => ((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal
local notation "mₛq" => (continuousSIdeleQuotientNorm ℚ Sq : SIdeleQuotient ℚ Sq →ₜ* ℝ≥0ˣ)
local notation "μs(" s ")" => realPWIntervalMeasure 0 s
local notation "Vs(" Y ", " hs ")" => RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)
local notation "evs(" Y ", " hs ")" =>
  RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 s hs)
local notation "lwμs(" s ")" => (sLocalQuotientTamagawaMeasure ℚ Sq).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s ((fun g ↦ Real.log (((mₛq) g).val : ℝ)) g)))
local notation "mainLevels(" Y ", " χ ", " hs ")" =>
  sLocalInvariantPWSobolev (F := ℚ) (S := Sq) hs (a := 1 / 2) (by norm_num) χ Y
local notation "testsq(" Y ")" =>
  sLocalPWTests (F := ℚ) (S := Sq) (T := Sq) le_rfl (sLocalPWProductRegion Sq Y)

variable {s : ℝ}

theorem measurable_ratOrderDensity (s : ℝ) :
    Measurable fun g : Jq ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s
      ((fun g ↦ Real.log (((mₛq) g).val : ℝ)) g)) :=
  ENNReal.measurable_ofReal.comp ((continuous_intervalSobolevDensity_zero s).measurable.comp
    (Real.measurable_log.comp continuous_ratQuotNorm.measurable))

/-- Reconstruction: a function of the norm is integrable for `main`'s weighted quotient measure at
order `s` exactly when `t⁻¹` times the weight times it is integrable on the positive reals. -/
theorem ratQuotNorm_integrable_order_iff {G : ℝ → ℝ} (hG : Measurable G) :
    Integrable (fun c ↦ G (ratQuotNorm c)) lwμs(s) ↔
      IntegrableOn (fun t ↦ t⁻¹ * (intervalSobolevDensity 0 0 s (Real.log t) * G t)) (Ioi 0) := by
  rw [integrable_withDensity_iff_integrable_smul' (measurable_ratOrderDensity s)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hF : Measurable fun t : ℝ ↦ intervalSobolevDensity 0 0 s (Real.log t) * G t :=
    ((continuous_intervalSobolevDensity_zero s).measurable.comp Real.measurable_log).mul hG
  refine (integrable_congr (ae_of_all _ fun c ↦ ?_)).trans (ratQuotNorm_integrable_iff hF)
  change (ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (ratQuotNorm c)))).toReal •
    G (ratQuotNorm c) = intervalSobolevDensity 0 0 s (Real.log (ratQuotNorm c)) * G (ratQuotNorm c)
  rw [ENNReal.toReal_ofReal (intervalSobolevDensity_zero_nonneg _ _), smul_eq_mul]

/-- Reconstruction: the integral of a function of the norm for `main`'s weighted quotient measure
at order `s` is the integral of `t⁻¹` times the weight times it over the positive reals. -/
theorem ratQuotNorm_integral_order {G : ℝ → ℝ} (hG : Measurable G) :
    ∫ c, G (ratQuotNorm c) ∂lwμs(s) =
      ∫ t in Ioi 0, t⁻¹ * (intervalSobolevDensity 0 0 s (Real.log t) * G t) := by
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_ratOrderDensity s)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hF : Measurable fun t : ℝ ↦ intervalSobolevDensity 0 0 s (Real.log t) * G t :=
    ((continuous_intervalSobolevDensity_zero s).measurable.comp Real.measurable_log).mul hG
  refine (integral_congr_ae (ae_of_all _ fun c ↦ ?_)).trans (ratQuotNorm_integral hF)
  change (ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (ratQuotNorm c)))).toReal •
    G (ratQuotNorm c) = intervalSobolevDensity 0 0 s (Real.log (ratQuotNorm c)) * G (ratQuotNorm c)
  rw [ENNReal.toReal_ofReal (intervalSobolevDensity_zero_nonneg _ _), smul_eq_mul]

/-- The weighted square of a band vector's evaluation is integrable on the line. -/
theorem ratBandOrder_integrable (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    Integrable fun x ↦ realPWIntervalWeight 0 s x * ‖evs(Y, hs) x v‖ ^ 2 := by
  have hm : MemLp (fun x ↦ evs(Y, hs) x v) 2 μs(s) :=
    (Lp.memLp (v.val : Lp ℂ 2 μs(s))).ae_eq (RealPWBand.evaluation_ae Y
      (volume_le_realPWIntervalMeasure 0 s hs) (realPWIntervalMeasure_absolutelyContinuous 0 s)
        v).symm
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).1 hm
  rw [realPWIntervalMeasure, integrable_withDensity_iff_integrable_smul'
    (ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight 0 s))
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hi
  refine hi.congr (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (zero_le_one.trans (one_le_realPWIntervalWeight 0 s hs x))]

/-- The squared norm of a weighted band vector is the weighted integral of its evaluation. -/
theorem ratBandOrder_norm_sq (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    ‖v‖ ^ 2 = ∫ x, realPWIntervalWeight 0 s x * ‖evs(Y, hs) x v‖ ^ 2 := by
  rw [norm_sq_realPWBand_of_evaluation_eq hs v _ rfl, realPWIntervalMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight 0 s))
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (zero_le_one.trans (one_le_realPWIntervalWeight 0 s hs x))]

/-- The function on the S-idele quotient attached to a weighted band vector:
`N ^ (1/2)` times twice its evaluation at the norm `N`. -/
def ratLevelFunOrder (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) (c : Jq) : ℂ :=
  ((ratQuotNorm c ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * evs(Y, hs) (ratQuotNorm c) v)

theorem continuous_ratLevelFunOrder (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    Continuous (ratLevelFunOrder Y hs v) := by
  refine (Complex.continuous_ofReal.comp (continuous_ratQuotNorm.rpow_const fun c ↦
    Or.inl (ratQuotNorm_pos c).ne')).mul (continuous_const.mul ?_)
  exact ((RealPWBand.continuous_evaluation Y _).clm_apply continuous_const).comp
    continuous_ratQuotNorm

theorem measurable_ratLevelProfileOrder (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    Measurable fun t : ℝ ↦ ‖((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * evs(Y, hs) t v)‖ ^ 2 :=
  (((Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))).mul
    (continuous_const.mul ((RealPWBand.continuous_evaluation Y _).clm_apply
      continuous_const))).norm.pow 2).measurable

theorem ratLevelFunOrder_profile_eq (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) {t : ℝ} (ht : 0 < t) :
    t⁻¹ * (intervalSobolevDensity 0 0 s (Real.log t) *
        ‖((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * evs(Y, hs) t v)‖ ^ 2) =
      4 * (realPWIntervalWeight 0 s t * ‖evs(Y, hs) t v‖ ^ 2) := by
  have ht2 : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt ht.le]
  rw [realPWIntervalWeight_zero_eq s ht, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Complex.norm_two, mul_pow, mul_pow, ht2]
  field_simp
  ring

/-- The function attached to a weighted band vector is square integrable for `main`'s weighted
quotient measure at order `s`. -/
theorem ratLevelFunOrder_memLp (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    MemLp (ratLevelFunOrder Y hs v) 2 lwμs(s) := by
  have : BorelSpace Jq := ⟨rfl⟩
  rw [memLp_two_iff_integrable_sq_norm (continuous_ratLevelFunOrder Y hs v).aestronglyMeasurable]
  have h4 : IntegrableOn (fun t ↦ 4 * (realPWIntervalWeight 0 s t * ‖evs(Y, hs) t v‖ ^ 2))
      (Ioi 0) := ((ratBandOrder_integrable Y hs v).const_mul 4).integrableOn
  exact (ratQuotNorm_integrable_order_iff (measurable_ratLevelProfileOrder Y hs v)).2
    (h4.congr_fun (fun t ht ↦ (ratLevelFunOrder_profile_eq Y hs v ht).symm) measurableSet_Ioi)

/-- The integral of the squared modulus of the function attached to a weighted band vector is
twice its squared norm. -/
theorem integral_ratLevelFunOrder_sq (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    ∫ c, ‖ratLevelFunOrder Y hs v c‖ ^ 2 ∂lwμs(s) = 2 * ‖v‖ ^ 2 := by
  have h := ratQuotNorm_integral_order (s := s) (measurable_ratLevelProfileOrder Y hs v)
  change ∫ c, (fun t : ℝ ↦ ‖((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * evs(Y, hs) t v)‖ ^ 2)
    (ratQuotNorm c) ∂lwμs(s) = _
  rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ratLevelFunOrder_profile_eq Y hs v ht),
    integral_const_mul, ratBandOrder_norm_sq,
    integral_eq_two_mul_integral_Ioi_of_even (ratBandOrder_integrable Y hs v)
      (fun x ↦ by rw [realPWIntervalWeight_zero_neg, RealPWBand.evaluation_even])]
  ring

/-- The linear map from the weighted model band to `main`'s local Sobolev space at order `s`,
`v ↦ N ^ (1/2) · 2 · v(N)`. -/
def ratLevelMapOrder (Y : ℝ) (hs : 0 ≤ s) : Vs(Y, hs) →ₗ[ℂ] Lp ℂ 2 lwμs(s) where
  toFun v := (ratLevelFunOrder_memLp Y hs v).toLp
  map_add' v w := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun c ↦ ?_)
    simp only [ratLevelFunOrder, map_add, Pi.add_apply]
    ring
  map_smul' a v := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun c ↦ ?_)
    simp only [ratLevelFunOrder, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem ratLevelMapOrder_ae (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    (ratLevelMapOrder Y hs v : Jq → ℂ) =ᵐ[lwμs(s)] ratLevelFunOrder Y hs v :=
  (ratLevelFunOrder_memLp Y hs v).coeFn_toLp

theorem norm_ratLevelMapOrder (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    ‖ratLevelMapOrder Y hs v‖ = Real.sqrt 2 * ‖v‖ := by
  have hsq : ‖ratLevelMapOrder Y hs v‖ ^ 2 = 2 * ‖v‖ ^ 2 := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ),
      integral_congr_ae (g := fun c ↦ ‖ratLevelFunOrder Y hs v c‖ ^ 2)
        ((ratLevelMapOrder_ae Y hs v).mono fun c hc ↦ by simp only [hc]),
      integral_ratLevelFunOrder_sq]
  rw [← Real.sqrt_sq (norm_nonneg (ratLevelMapOrder Y hs v)), hsq, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg v)]

/-- Reconstruction: the weighted even band of `Sec4_RealPWLevelTrace` at base interval `{0}` and
Sobolev order `s` embeds isometrically in `main`'s local Sobolev space of `ℚ` with no finite place
at order `s`, by `v ↦ 2 ^ (-1/2) · N ^ (1/2) · 2 · v(N)`. -/
def ratLevelIsometryOrder (Y : ℝ) (hs : 0 ≤ s) : Vs(Y, hs) →ₗᵢ[ℂ] Lp ℂ 2 lwμs(s) where
  toLinearMap := ((Real.sqrt 2)⁻¹ : ℂ) • ratLevelMapOrder Y hs
  norm_map' v := by
    change ‖((Real.sqrt 2)⁻¹ : ℂ) • ratLevelMapOrder Y hs v‖ = ‖v‖
    rw [norm_smul, norm_ratLevelMapOrder, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by norm_num)), one_mul]

theorem ratLevelMapOrder_eq_smul_isometry (Y : ℝ) (hs : 0 ≤ s) (v : Vs(Y, hs)) :
    ratLevelMapOrder Y hs v = ((Real.sqrt 2 : ℝ) : ℂ) • ratLevelIsometryOrder Y hs v := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
  change ratLevelMapOrder Y hs v =
    ((Real.sqrt 2 : ℝ) : ℂ) • (((Real.sqrt 2)⁻¹ : ℂ) • ratLevelMapOrder Y hs v)
  rw [smul_smul, mul_inv_cancel₀ h2, one_smul]

/-- Reconstruction: at order `s`, `main`'s weighted theta vector of a test `f` is `volume₁` times
the image under `ratLevelMapOrder` of any band vector whose evaluation is the even part of the
Schwartz function of `f`. -/
theorem ratFullThetaOrder_eq_smul {Y : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (f : Bq)
    (g : 𝓢(ℝ, ℂ)) (hg : ∀ x, g (eq x.toAdd) = f x) (v : Vs(Y, hs))
    (hv : ∀ t, evs(Y, hs) t v = (g t + g (-t)) / 2) :
    (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2) (by norm_num) χ f :
      Lp ℂ 2 lwμs(s)) = (volume₁ : ℂ) • ratLevelMapOrder Y hs v := by
  have h1 : (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2) (by norm_num)
      χ f : Jq → ℂ) =ᵐ[lwμs(s)] modulationWeight mₛq (1 / 2)
        (sLocalHomogeneousAdelicThetaLinearMap ℚ Sq χ f) :=
    (sLocalFullPWTheta_memLp (F := ℚ) (S := Sq) (s := s) (by norm_num : (0 : ℝ) < 1 / 2) χ
      f).coeFn_toLp
  refine Lp.ext ?_
  filter_upwards [h1, Lp.coeFn_smul (volume₁ : ℂ) (ratLevelMapOrder Y hs v),
    ratLevelMapOrder_ae Y hs v] with c hc1 hc2 hc3
  rw [hc1, hc2, Pi.smul_apply, hc3, smul_eq_mul]
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hN : ratQuotNorm (QuotientGroup.mk x) = |eq x.val| := ratQuotNorm_mk x
  have hf1 : f (Multiplicative.ofAdd x.val) = g (eq x.val) := (hg _).symm
  have hf2 : f (Multiplicative.ofAdd (-x.val)) = g (-eq x.val) := by
    rw [← hg, toAdd_ofAdd, map_neg]
  have hev : evs(Y, hs) |eq x.val| v = (g (eq x.val) + g (-eq x.val)) / 2 := by
    rw [hv]
    rcases abs_choice (eq x.val) with h | h <;> rw [h]
    · rw [neg_neg, add_comm]
  change ((ratQuotNorm (QuotientGroup.mk x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap ℚ Sq χ f (QuotientGroup.mk x) = _
  rw [ratHomogeneousTheta_apply, hf1, hf2]
  unfold ratLevelFunOrder
  rw [hN, hev]
  ring

/-- For a test of `main`'s band, a weighted band vector of the model whose image is `volume₁⁻¹`
times its weighted theta vector at order `s`. It lies in the model level when the test is
polar-free. -/
theorem ratFullThetaOrder_mem {Y : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (f : Bq) (hf : f ∈ testsq(Y)) :
    ∃ v : Vs(Y, hs), (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2)
        (by norm_num) χ f : Lp ℂ 2 lwμs(s)) = (volume₁ : ℂ) • ratLevelMapOrder Y hs v ∧
      (f ∈ sAdelePolarSubspace ℚ Sq → v ∈ realPWZeroLevel Y 0 s hs) := by
  obtain ⟨g₀, hg₀, hb⟩ := ratBandTest_spec f hf
  obtain ⟨g, hg, he, hgb⟩ := exists_evenPart g₀ hb
  have hm : MemLp (g : ℝ → ℂ) 2 μs(s) :=
    memLp_realPWIntervalMeasure_of_evenSchwartz_order le_rfl hs g he 0 (by norm_num)
      ⟨(SchwartzMap.seminorm ℂ 0 0) g, fun x _ ↦ by
        simpa using SchwartzMap.norm_le_seminorm ℂ g x⟩
  obtain ⟨v, hv⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y g he hgb
    (volume_le_realPWIntervalMeasure 0 s hs) hm
  refine ⟨v, ratFullThetaOrder_eq_smul hs χ f g₀ hg₀ v (fun t ↦ by rw [congrFun hv t, hg]),
    fun hpol ↦ ?_⟩
  rw [mem_realPWZeroLevel_iff, congrFun hv 0, hg, neg_zero]
  have h0 : g₀ 0 = 0 := by
    have h := hg₀ (Multiplicative.ofAdd 0)
    rw [toAdd_ofAdd, map_zero] at h
    rw [h]
    exact ((mem_sAdelePolarSubspace f).1 hpol).1
  rw [h0]
  simp

set_option maxHeartbeats 800000 in
/-- The image of a core vector of the weighted model band lies in `main`'s level at order `s`. -/
theorem ratLevelIsometryOrder_core_mem {Y : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker)
    (u : Vs(Y, hs)) (hu : u ∈ realPWBandPolarFreeCore Y 0 hs) :
    ratLevelIsometryOrder Y hs u ∈
      ((testsq(Y) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := ℚ) (S := Sq))).map
        (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2) (by norm_num) χ)
          ).topologicalClosure := by
  obtain ⟨g, he, hb, h0, hi, hug⟩ := hu
  obtain ⟨f, hfg, htest, hpol⟩ := ratCore_test g hb h0 hi
  have hθ := ratFullThetaOrder_eq_smul (Y := Y) hs χ f g (fun x ↦ (hfg x).symm) u
    (fun t ↦ by rw [congrFun hug t, he t]; ring)
  have hmem := Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem
    (f := sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2) (by norm_num) χ)
    (show f ∈ testsq(Y) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := ℚ) (S := Sq)) from
      ⟨htest, hpol⟩))
  have hvol : ((volume₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ratNormOneMass_pos.ne'
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
  have hW : ratLevelIsometryOrder Y hs u = (((Real.sqrt 2)⁻¹ : ℂ) * ((volume₁ : ℝ) : ℂ)⁻¹) •
      sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2) (by norm_num) χ f := by
    rw [hθ, smul_smul, mul_assoc, inv_mul_cancel₀ hvol, mul_one,
      ratLevelMapOrder_eq_smul_isometry, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hW]
  exact Submodule.smul_mem _ _ hmem

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488, for `ℚ` with no finite place, twist
`1/2` and every Sobolev order `s ≥ 0`.
Reconstruction: `main`'s polar-free level `sLocalInvariantPWSobolev` at order `s` is the image,
under the isometry `ratLevelIsometryOrder`, of the level of the weighted even band of
`Sec4_RealPWLevelTrace` at base interval `{0}` and order `s`, the band vectors that vanish at the
origin. -/
theorem ratLevelOrder_eq_map {Y : ℝ} (hY : 0 < Y) (hs : 0 ≤ s)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    mainLevels(Y, χ, hs) = (realPWZeroLevel Y 0 s hs).map (ratLevelIsometryOrder Y hs).toLinearMap := by
  have : CompleteSpace Vs(Y, hs) :=
    (RealPWBand.isClosed_space Y (volume_le_realPWIntervalMeasure 0 s hs)).completeSpace_coe
  have hlevcl : IsClosed (realPWZeroLevel Y 0 s hs : Set Vs(Y, hs)) := by
    unfold realPWZeroLevel
    exact Submodule.isClosed_orthogonal _
  have hcl : IsClosed (((realPWZeroLevel Y 0 s hs).map (ratLevelIsometryOrder Y hs).toLinearMap :
      Submodule ℂ (Lp ℂ 2 lwμs(s))) : Set (Lp ℂ 2 lwμs(s))) := by
    rw [Submodule.map_coe]
    exact (ratLevelIsometryOrder Y hs).isometry.isClosedEmbedding.isClosedMap _ hlevcl
  rw [sLocalInvariantPWSobolev_eq_closure_map]
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_ hcl
    rintro _ ⟨f, ⟨htest, hpol⟩, rfl⟩
    obtain ⟨v, hθ, hlev⟩ := ratFullThetaOrder_mem hs χ f htest
    rw [hθ, ratLevelMapOrder_eq_smul_isometry, smul_smul]
    exact Submodule.smul_mem _ _ ⟨v, hlev hpol, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hvcl : v ∈ closure (realPWBandPolarFreeCore Y 0 hs) := by
      rw [closure_realPWBandPolarFreeCore_eq le_rfl (by norm_num) hs hY]
      exact (mem_realPWZeroLevel_iff Y 0 s hs v).1 hv
    have key := map_mem_closure (ratLevelIsometryOrder Y hs).continuous hvcl
      (t := ((((testsq(Y) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := ℚ) (S := Sq))).map
        (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := s) (a := 1 / 2) (by norm_num) χ)
          ).topologicalClosure : Submodule ℂ (Lp ℂ 2 lwμs(s))) : Set (Lp ℂ 2 lwμs(s))))
      (fun u hu ↦ ratLevelIsometryOrder_core_mem hs χ u hu)
    rwa [(Submodule.isClosed_topologicalClosure _).closure_eq] at key

/-- Reconstruction: at Sobolev order `s`, for a test whose folded form `ψ` vanishes outside
`[a, b]` with `1 < a`, the compressed cutoffs of the weighted model on its level have traces whose
difference from the summed sharp orbital masses at radius `L Y` tends to minus the polar term.
The model trace limit at order `s` is `exists_realPWTestCutoff_level_trace_limit`, and the sharp
masses are compared with the order-zero model through `tsum_ratSharpMass`. -/
theorem ratLevelOrder_trace_sub_sharpMass_tendsto (f : BruhatCompactSupport Iq) {Y : ℝ}
    (hY : 0 < Y) (hs : 0 ≤ s) {a b : ℝ} (ha1 : 1 < a) (hsupp : ∀ g ∉ Icc a b, ratFold f g = 0) :
    ∃ T : ℝ → nuclearEndomorphisms Vs(Y, hs),
      (∀ L (v : Vs(Y, hs)), ∃ r : Lp ℂ 2 μs(s),
        (∀ᵐ x ∂μs(s), r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            evs(Y, hs) (g⁻¹ * x) ((realPWZeroLevel Y 0 s hs).starProjection v))) ∧
        (T L).val v =
          (realPWZeroLevel Y 0 s hs).starProjection ((Vs(Y, hs)).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
        (𝓝 (-ratPolarTerm f)) := by
  obtain ⟨T, hT, hlim⟩ := exists_realPWTestCutoff_level_trace_limit Y 0 s hs hY le_rfl
    (by norm_num) ha1 (ratFold f) (continuous_ratFold f) hsupp
  refine ⟨T, hT, ?_⟩
  have hint : Integrable (ratFold f) :=
    (continuous_ratFold f).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc hsupp)
  have hmass : Tendsto (fun L ↦ ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
      (𝓝 (∫ g, ratFold f g * realPWSharpTraceLimit 0 g)) := by
    have h := tendsto_integral_realPWSharpTrace (Y := Y) (α := 0) (s := 0) hY le_rfl le_rfl ha1
      (ratFold f) hint hsupp
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact (tsum_ratSharpMass f hL hY).symm
  have hpol : ratPolarTerm f = ∫ g, ratFold f g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [ratPolarTerm]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Icc a b
    · have hmin : min g 1 = 1 := min_eq_right (by linarith [hg.1])
      simp only [hmin, one_mul]
    · simp only [hsupp g hg, zero_mul]
  rw [hpol]
  convert hlim.sub hmass using 2
  ring

/-- The conjugates of the weighted model operators take values in `main`'s level at order `s`. -/
theorem conjNuclear_mem_mainLevelOrder {Y : ℝ} (hY : 0 < Y) (hs : 0 ≤ s)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (T : nuclearEndomorphisms Vs(Y, hs))
    (hT : ∀ v : Vs(Y, hs), T.val v ∈ realPWZeroLevel Y 0 s hs) (x : Lp ℂ 2 lwμs(s)) :
    (conjNuclear (ratLevelIsometryOrder Y hs) T).val x ∈ mainLevels(Y, χ, hs) := by
  refine (ratLevelOrder_eq_map hY hs χ).ge ?_
  rw [conjNuclear_apply]
  exact Submodule.mem_map_of_mem (hT _)

set_option maxHeartbeats 4000000 in
/-- Paper: Theorem 12.4.1.1, Step III, p. 517, and the subtraction on p. 520, on `main`'s
polar-free level for `ℚ` with no finite place, at twist `1/2` and every Sobolev order `s ≥ 0`.
Reconstruction: for a test whose folded form `ψ` vanishes outside `[a, b]` with `1 < a`, the
operators of `ratLevelOrder_trace_sub_sharpMass_tendsto`, conjugated by `ratLevelIsometryOrder`,
take values in `main`'s level at order `s` and keep their traces. So on `main`'s level the trace
less the summed sharp masses tends to minus the polar term `∫ ψ(g) g ^ (-1/2) dg`, at every order.
Deviation: The bandwidth `Y` is fixed. The operators are the model's cutoff operators transported
by the isometry, not an operator printed in the paper. -/
theorem ratMainLevelOrder_trace_tendsto (f : BruhatCompactSupport Iq) {Y : ℝ} (hY : 0 < Y)
    (hs : 0 ≤ s) {a b : ℝ} (ha1 : 1 < a) (hsupp : ∀ g ∉ Icc a b, ratFold f g = 0)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms Vs(Y, hs),
      (∀ L (v : Vs(Y, hs)), ∃ r : Lp ℂ 2 μs(s),
        (∀ᵐ x ∂μs(s), r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            evs(Y, hs) (g⁻¹ * x) ((realPWZeroLevel Y 0 s hs).starProjection v))) ∧
        (T L).val v =
          (realPWZeroLevel Y 0 s hs).starProjection ((Vs(Y, hs)).orthogonalProjectionOnto r)) ∧
      (∀ L x, (conjNuclear (ratLevelIsometryOrder Y hs) (T L)).val x ∈ mainLevels(Y, χ, hs)) ∧
      Tendsto (fun L ↦ hilbertTrace (conjNuclear (ratLevelIsometryOrder Y hs) (T L)) -
          ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop (𝓝 (-ratPolarTerm f)) := by
  obtain ⟨T, hT, hlim⟩ := ratLevelOrder_trace_sub_sharpMass_tendsto f hY hs ha1 hsupp
  refine ⟨T, hT, fun L x ↦ conjNuclear_mem_mainLevelOrder hY hs χ (T L) (fun v ↦ ?_) x, ?_⟩
  · obtain ⟨r, -, hr⟩ := hT L v
    rw [hr]
    exact Submodule.starProjection_apply_mem _ _
  · simp only [hilbertTrace_conjNuclear]
    exact hlim

end RatOrder

end RiemannMasullo.Isolated
