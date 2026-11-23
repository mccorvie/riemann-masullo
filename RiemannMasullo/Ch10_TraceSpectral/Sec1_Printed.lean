module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian

/-! # §10.1 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing

namespace RiemannMasullo

local instance instSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (SIdeleQuotient F S) := borel _

local instance instIdeleClassMeasurableSpaceSec1Printed (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance instNormOneSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (sIdeleQuotientNorm F S).ker := borel _

/-- Paper: Before (10.1.1.2), p. 434. The interval norm is finite on every
weighted global polar-free theta function for every closed interval with interior. -/
def Printed.globalThetaSobolev_closedIntervals_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 ≤ s →
    ∀ I : Set ℝ, IsClosed I → OrdConnected I → (interior I).Nonempty →
    ∀ f : adelePolarSubspace F,
      let m := (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
        IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ)
      intervalSobolevENorm (ideleClassTamagawaMeasure F) (fun g ↦ Real.log ((m g).val : ℝ))
        I s (modulationWeight m a (adelicTheta f.val)) ≠ ⊤

/-- Paper: Before (10.1.1.2), p. 434. Take ℚ, I = [0,∞), a = s = 0, finite
integer indicators and the real test (3x² − 2πx⁴) exp(-πx²). It is the derivative
of x³ exp(-πx²) and vanishes at zero. Its theta is strictly negative on [2,3].
The integral over that shell grows at least as a positive constant times 2^(2b)
when the subinterval is [0,b]. -/
theorem Printed.globalThetaSobolev_closedIntervals_finite_false :
    ¬ Printed.globalThetaSobolev_closedIntervals_finite := by sorry

/-- Paper: Before Lemma 10.1.1.4, p. 435. A positive twist of every local theta
test is asserted to belong to the Sobolev space for the whole half-line (-a,∞). -/
def Printed.sLocalThetaSobolev_openHalfLine_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a s : ℝ), 0 < a → 0 ≤ s → ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      let m := (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
        SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
      intervalSobolevENorm (sLocalQuotientTamagawaMeasure F S)
        (fun g ↦ Real.log ((m g).val : ℝ)) (Ioi (-a)) s
        (modulationWeight m a (sLocalAdelicThetaOnClasses F S f)) ≠ ⊤

/-- Paper: Before Lemma 10.1.1.4, p. 435. For ℚ, S = {∞}, a = 1, s = 0,
and the real Gaussian, the weighted theta is positive throughout [2,3].
Already the intervals [0,b] give unbounded norms as b tends to infinity. -/
theorem Printed.sLocalThetaSobolev_openHalfLine_finite_false :
    ¬ Printed.sLocalThetaSobolev_openHalfLine_finite := by sorry

/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434. As printed,
the integral defining the local norm is finite at every positive weight and
every compact nonempty interval. -/
def Printed.sLocalThetaSobolev_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      Integrable (fun g : SIdeleQuotient F S ↦ ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((sIdeleQuotientNorm F S g).val : ℝ))) (sLocalQuotientTamagawaMeasure F S)

private theorem sLocalThetaSobolev_integrable_false_measure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (N : G →* ℝ≥0ˣ) (hN : Continuous N) (hs : Function.Surjective N) :
    μ {g | ((N g : ℝ≥0) : ℝ) < 1} = ⊤ := by
  obtain ⟨t, ht⟩ := hs (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  obtain ⟨g₀, hg₀⟩ := hs (Units.mk0 (3 / 4 : ℝ≥0) (by norm_num))
  have hcont : Continuous fun g ↦ ((N g : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hN)
  let A : Set G := {g | 1 / 2 < ((N g : ℝ≥0) : ℝ) ∧ ((N g : ℝ≥0) : ℝ) < 1}
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hg₀A : g₀ ∈ A := by
    simp only [A, mem_setOf_eq, hg₀, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
  have hA0 : μ A ≠ 0 := (hAo.measure_pos μ ⟨g₀, hg₀A⟩).ne'
  let B (k : ℕ) : Set G := (fun g ↦ t ^ k * g) ⁻¹' A
  have hB (k : ℕ) (g : G) : g ∈ B k ↔
      1 / 2 < 2 ^ k * ((N g : ℝ≥0) : ℝ) ∧ 2 ^ k * ((N g : ℝ≥0) : ℝ) < 1 := by
    show (1 / 2 < ((N (t ^ k * g) : ℝ≥0) : ℝ) ∧ ((N (t ^ k * g) : ℝ≥0) : ℝ) < 1) ↔ _
    rw [map_mul, map_pow, ht]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, NNReal.coe_mul,
      NNReal.coe_pow, NNReal.coe_ofNat]
  have hmeas (k : ℕ) : μ (B k) = μ A := measure_preimage_mul μ (t ^ k) A
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    have key (k l : ℕ) (h : k < l) (g : G) (h1 : g ∈ B k) (h2 : g ∈ B l) : False := by
      rw [hB] at h1 h2
      have h2l : (2 : ℝ) * 2 ^ k ≤ 2 ^ l := by
        calc (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro g h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h g h1 h2
    · exact key l k h g h2 h1
  have hsub : (⋃ k, B k) ⊆ {g | ((N g : ℝ≥0) : ℝ) < 1} := by
    intro g hg
    obtain ⟨k, hk⟩ := mem_iUnion.mp hg
    rw [hB] at hk
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    simp only [mem_setOf_eq]
    nlinarith
  refine eq_top_mono (measure_mono hsub) ?_
  rw [measure_iUnion hdisj (fun k ↦ (measurable_const_mul (t ^ k)) hAo.measurableSet)]
  simp only [hmeas]
  exact ENNReal.tsum_const_eq_top_of_ne_zero hA0


private theorem sLocalThetaSobolev_integrable_false_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sLocalThetaSobolev_integrable_false_theta
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) ≤
      ‖sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x)‖ := by
  have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ f {x} isCompact_singleton).hasSum
    rfl).summable
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  simp only [hf] at hs ⊢
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have hr := Complex.summable_ofReal.mp hs
  refine le_trans (le_of_eq ?_) (hr.le_tsum 1 fun _ _ ↦ (Real.exp_pos _).le)
  simp

/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434.
For ℚ with S consisting of the real place, take f(x) = exp(-πx²), a = 1,
I = {-1} and s = 0. The two S-units give theta(t) = 2 exp(-πt²), whose
square is not integrable near zero against dt/t. -/
theorem Printed.sLocalThetaSobolev_integrable_false :
    ¬ Printed.sLocalThetaSobolev_integrable := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  let φ : SchwartzMap ℝ ℂ := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hf : ∀ x : SAdeleRing ℚ ∅, E φ (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    rw [hE]
    have hn (z : Rat.infinitePlace.Completion) : ‖InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace z‖ = ‖z‖ := by
      rw [← dist_zero_right, ← dist_zero_right z,
        ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        Rat.isReal_infinitePlace).dist_eq z 0
    have hφ (y : ℝ) : φ y = ((Real.exp (-‖y‖ ^ 2) : ℝ) : ℂ) := by
      change Complex.ofRealCLM (SchwartzMap.gaussian 1 one_pos y) = _
      rw [SchwartzMap.gaussian_apply, Complex.ofRealCLM_apply, neg_mul, one_mul]
    rw [hφ, hn]
  have hint := h ℚ ∅ 1 (-1) (-1) 0 one_pos le_rfl le_rfl (E φ)
  let θ := sLocalAdelicThetaOnClasses ℚ ∅ (E φ)
  have hint' : Integrable (fun g ↦ ‖θ g‖ ^ 2) (sLocalQuotientTamagawaMeasure ℚ ∅) :=
    hint.congr (Eventually.of_forall fun g ↦ by simp only [θ]; norm_num [intervalSobolevDensity])
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)
  have : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure := hW.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  have hNc : Continuous (sIdeleQuotientNorm ℚ ∅) := (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  have hB := sLocalThetaSobolev_integrable_false_measure (sLocalQuotientTamagawaMeasure ℚ ∅)
    (sIdeleQuotientNorm ℚ ∅) hNc hσ.surjective
  let B := {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1}
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  have hlow : ∀ g ∈ B, ENNReal.ofReal (Real.exp (-1) ^ 2) ≤ ‖‖θ g‖ ^ 2‖ₑ := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hx : ‖x.val.1 Rat.infinitePlace‖ < 1 := by
      rw [← sLocalThetaSobolev_integrable_false_norm]
      exact hg
    have h1 := sLocalThetaSobolev_integrable_false_theta (E φ) hf x
    have h2 : Real.exp (-1) ≤ Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) := by
      gcongr
      nlinarith [norm_nonneg (x.val.1 Rat.infinitePlace)]
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.exp_pos _).le (h2.trans h1) 2)
  have hfin : (∫⁻ g, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅) < ⊤ :=
    hint'.hasFiniteIntegral
  have hBdef : B = {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1} := rfl
  have hge : ⊤ ≤ ∫⁻ g, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-1) ^ 2) * sLocalQuotientTamagawaMeasure ℚ ∅ B := by
          rw [hBdef, hB, ENNReal.mul_top (by positivity)]
      _ = ∫⁻ _ in B, ENNReal.ofReal (Real.exp (-1) ^ 2) ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
          (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
          setLIntegral_mono' hBm hlow
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)


/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. As printed, the density of
the weighted S-idele measure vanishes at infinity. -/
def Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α β s : ℝ), α ≤ β → 0 ≤ s →
    Tendsto (fun g : (SAdeleRing F S)ˣ ↦
      intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)))
      (cocompact _) (nhds 0)

private theorem sIdeleNorm_vanishesAtInfinity_false_cont (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (sIdeleNorm F S) := by
  suffices H : Continuous (fun g ↦ sIdeleNorm F S g) from H
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun w _ ↦ ?_
    refine Continuous.pow ?_ _
    exact (continuous_nnNorm.units_map _).comp
      ((((continuous_apply w).comp continuous_fst).units_map _))
  · refine continuous_finsetProd _ fun v _ ↦ ?_
    exact (continuous_nnNorm.units_map _).comp
      ((((continuous_apply v).comp continuous_snd).units_map _))

private theorem sIdeleNorm_vanishesAtInfinity_false_diag :
    ((sIdeleNorm ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (Units.map ((algebraMap ℚ (InfiniteAdeleRing ℚ)).prod
        (RingHom.pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
          algebraMap ℚ (v.val.adicCompletion ℚ))).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero))).val : ℝ) = 2 := by
  simp only [sIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [Units.coe_prod, NNReal.coe_prod]
  have h2 := InfinitePlace.prod_eq_abs_norm (K := ℚ) 2
  rw [show (|(Algebra.norm ℚ) (2:ℚ)| : ℚ) = 2 by simp [Algebra.norm_self]] at h2
  rw [← (by norm_num : (((2:ℚ)) : ℝ) = 2), ← h2]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.val_pow_eq_pow_val, NNReal.coe_pow]
  congr 1
  change ‖(algebraMap ℚ (InfiniteAdeleRing ℚ) 2) w‖ = _
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact AbsoluteValue.Completion.norm_coe (2 : WithAbs w.1)

private theorem sIdeleNorm_vanishesAtInfinity_false_noncompact :
    ¬ CompactSpace (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ := by
  intro hc
  let u := Units.map ((algebraMap ℚ (InfiniteAdeleRing ℚ)).prod
        (RingHom.pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
          algebraMap ℚ (v.val.adicCompletion ℚ))).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero)
  have hu := sIdeleNorm_vanishesAtInfinity_false_diag
  have hcont : Continuous fun g : (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ ↦
      ((sIdeleNorm ℚ ∅ g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (sIdeleNorm_vanishesAtInfinity_false_cont ℚ ∅))
  obtain ⟨C, hC⟩ := (isCompact_range hcont).isBounded.subset_closedBall 0
  have hn : ∀ n : ℕ, ((sIdeleNorm ℚ ∅ (u ^ n)).val : ℝ) = 2 ^ n := fun n ↦ by
    rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, hu]
  obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  have : ((sIdeleNorm ℚ ∅ (u ^ n)).val : ℝ) ∈ Metric.closedBall 0 C := hC ⟨u ^ n, rfl⟩
  rw [hn n] at this
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ n)] at this
  linarith


/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. For ℚ with S the real place,
I = {1} and s = 0, the density is t² on the positive ideles t, so it
grows without bound as t tends to infinity. -/
theorem Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity_false :
    ¬ Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity := by
  intro h
  have h1 := h ℚ ∅ 0 0 0 le_rfl le_rfl
  have hconst : (fun g : (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ ↦
      intervalSobolevDensity 0 0 0 (Real.log ((sIdeleNorm ℚ ∅ g).val : ℝ))) = fun _ ↦ 1 := by
    funext g
    simp [intervalSobolevDensity]
  rw [hconst] at h1
  have : NoncompactSpace (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ :=
    not_compactSpace_iff.mp sIdeleNorm_vanishesAtInfinity_false_noncompact
  exact one_ne_zero (tendsto_nhds_unique h1 tendsto_const_nhds).symm

/-- Paper: Proposition 10.1.1.5, pp. 436–437. As printed, the global Sobolev
completion in the proposition uses theta functions of all Schwartz–Bruhat tests.
The proposed completion requires their weighted square integrability. -/
def Printed.globalThetaSobolev_allTests_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)),
      Integrable (fun g : IdeleClassGroup (𝓞 F) F ↦ ‖adelicTheta f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((ideleClassNorm F g).val : ℝ))) (ideleClassTamagawaMeasure F)

/-- Paper: Proposition 10.1.1.5, pp. 436–437. For ℚ, set a = s = 0
and I = {0}. The real Gaussian times the characteristic functions of the finite
integer rings has theta(t) = Σ_{n ≠ 0} exp(-πn²t²), asymptotic to 1/t at zero
on each norm-one fibre, so its square is not integrable. -/
theorem Printed.globalThetaSobolev_allTests_integrable_false :
    ¬ Printed.globalThetaSobolev_allTests_integrable := by sorry

/-- A test quotient completes in its weighted function norm when its evaluation on
representatives gives an injective dense map to a closed subspace of the ambient L². -/
def Printed.IsFunctionCompletionMap {G B X W : Type*} [MeasurableSpace G]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure G) (rep : W → G → ℂ) (H : Submodule ℂ W)
    (q : B → X) (θ : B → G → ℂ) (j : X →L[ℂ] H) : Prop :=
  IsClosed (H : Set W) ∧ Function.Injective j ∧ DenseRange j ∧
    ∀ f, rep (j (q f)).val =ᵐ[μ] θ f

/-- The product of the test quotient maps extends to a continuous injection of
the function-norm completions and factors through a surjective Hilbert-sum isometry.
The completions are quantified so the statement also makes sense when a proposed
test function fails to belong to the ambient L². -/
def Printed.HasHomogeneousSobolevFactorization {G B X W Ω : Type*} {Y : Ω → Type*}
    [MeasurableSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure G) (rep : W → G → ℂ) (q : B → X) (qω : ∀ i, B → Y i)
    (θ : B → G → ℂ) (θω : Ω → B → G → ℂ) : Prop :=
  ∃ (H : Submodule ℂ W) (K : Ω → Submodule ℂ W)
    (j : X →L[ℂ] H) (k : ∀ i, Y i →L[ℂ] K i)
    (Q : H →L[ℂ] (∀ i, K i)) (T : H ≃ₗᵢ[ℂ] lp (fun i ↦ ↥(K i)) 2),
    Printed.IsFunctionCompletionMap μ rep H q θ j ∧
    (∀ i, Printed.IsFunctionCompletionMap μ rep (K i) (qω i) (θω i) (k i)) ∧
    Function.Injective Q ∧ (∀ f i, Q (j (q f)) i = k i (qω i f)) ∧
    ∀ u i, Q u i = T u i

/-- Paper: Proposition 10.1.1.5(2), p. 437, (10.1.1.14). The product of the
global homogeneous quotient maps factors isometrically through the Hilbert sum.
The factors carry the norm of their weighted homogeneous functions. -/
def Printed.globalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    let G := IdeleClassGroup (𝓞 F) F
    let m : G →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) α β s
    Printed.HasHomogeneousSobolevFactorization (X := GlobalAdelicThetaSpace F)
      (Y := GlobalHomogeneousThetaSpace F) μ (fun u : W ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight m a (adelicTheta f))
      (fun ω f ↦ modulationWeight m a (homogeneousAdelicTheta ω f))

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(i), a = s = 0 and I = {0}.
Use the finite integer indicators and a radial smooth archimedean bump equal to 1
at radius 1 and supported in (0.9, 1.1). Subtract a radial bump supported in (0.4, 0.6)
scaled to cancel the integral. Both zero terms vanish and theta at the identity is 4.
This theta lies in the trivial isotype. The norm-one mass π/4 scales its only
nonzero coordinate and prevents an isometry. -/
theorem Printed.globalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.globalThetaSobolev_rawIsotypeDecomposition := by sorry

/-- Paper: Proposition 10.1.1.5(2), p. 437, (10.1.1.15). The product of the
S-local homogeneous quotient maps factors isometrically through the Hilbert sum.
The factors carry the norm of their weighted homogeneous functions. -/
def Printed.sLocalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s → 0 < α →
    let G := SIdeleQuotient F S
    let m : G →ₜ* ℝ≥0ˣ := ⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩
    let μ := sLocalQuotientTamagawaMeasure F S
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) α β s
    Printed.HasHomogeneousSobolevFactorization (X := SLocalAdelicThetaSpace F S)
      (Y := SLocalHomogeneousThetaSpace F S) μ (fun u : W ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight m a (sLocalAdelicThetaOnClasses F S f))
      (fun ω f ↦ modulationWeight m a (sLocalHomogeneousAdelicThetaLinearMap F S ω f))

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(i), S consisting of the
complex place, a = 1, I = {1}, and s = 0. A nonzero radial Gaussian theta
function lies in the trivial isotype. Its raw average is π/2 times itself
and every other character average is zero, so the Hilbert sum norm grows by π/2. -/
theorem Printed.sLocalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.sLocalThetaSobolev_rawIsotypeDecomposition := by sorry

/-- Paper: Theorem 10.1.2.1, p. 437. As printed, inversion in the idele class
group defines a continuous linear automorphism of the same ambient Sobolev space
for every compact nonempty interval. -/
def Printed.ideleClassSobolev_inversion_automorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α β s : ℝ), α ≤ β → 0 ≤ s →
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ
      (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) α β s
    ∃ J : W ≃L[ℂ] W, ∀ u : W,
      (J u : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ] fun g ↦ u g⁻¹

open scoped ENNReal in
/-- On the weighted L² space with weight |x|² (I = {1}, s = 0) over a commutative group with a
module taking a value above one, inversion is not a bounded automorphism. It would conjugate
translation by g⁻¹ into translation by g, so its norm would be at most |g|⁻² times itself. -/
private theorem Printed.ideleClassSobolev_inversion_automorphism_false_aux {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (g : G) (hg : 1 < ((m g).val : ℝ))
    (J : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0 ≃L[ℂ]
      CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] fun x ↦ u x⁻¹) : False := by
  set d : G → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (if (false : Bool) then (intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)))⁻¹
     else intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ))) with hd_def
  have hνμ : μ.withDensity d ≪ μ := withDensity_absolutelyContinuous μ d
  let T := hardySobolevTranslation μ m 1 1 0 le_rfl le_rfl
  have hinv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ :=
    quasiMeasurePreserving_inv μ
  have hmul : QuasiMeasurePreserving (fun x : G ↦ g * x) μ μ :=
    (measurePreserving_mul_left μ g).quasiMeasurePreserving
  -- Inversion turns translation by g⁻¹ into translation by g.
  have hconj (u : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0) :
      J u = T g⁻¹ (J (T g⁻¹ u)) := by
    apply Lp.ext
    apply hνμ.ae_eq
    have h1 : (T g⁻¹ (J (T g⁻¹ u)) : G → ℂ) =ᵐ[μ] fun x ↦ (J (T g⁻¹ u) : G → ℂ) (g * x) := by
      simpa only [inv_inv] using hardySobolevTranslation_apply μ m 1 1 0 le_rfl le_rfl g⁻¹ _
    have h2 : (fun x ↦ (J (T g⁻¹ u) : G → ℂ) (g * x)) =ᵐ[μ]
        fun x ↦ (T g⁻¹ u : G → ℂ) (g * x)⁻¹ :=
      hmul.ae_eq_comp (hJ _)
    have h3 : (fun x ↦ (T g⁻¹ u : G → ℂ) (g * x)⁻¹) =ᵐ[μ]
        fun x ↦ (u : G → ℂ) (g * (g * x)⁻¹) := by
      have h := hardySobolevTranslation_apply μ m 1 1 0 le_rfl le_rfl g⁻¹ u
      simp only [inv_inv] at h
      exact (hinv.comp hmul).ae_eq_comp h
    filter_upwards [hJ u, h1, h2, h3] with x hx h1 h2 h3
    rw [hx, h1, h2, h3, mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  -- Translation by g⁻¹ has norm at most |g|⁻¹ < 1.
  set L := Real.log ((m g).val : ℝ)
  have hL : 0 < L := Real.log_pos hg
  have hTnorm : ‖T g⁻¹‖ ≤ Real.exp (-L) := by
    have h := norm_hardySobolevTranslation_le μ m 1 1 0 le_rfl le_rfl g⁻¹
    have hlog : Real.log ((m g⁻¹).val : ℝ) = -L := by
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
    simpa only [hlog, one_mul, max_self, zero_div, Real.rpow_zero, mul_one] using h
  have hq : Real.exp (-L) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hL)
  have hq0 : 0 ≤ Real.exp (-L) := (Real.exp_pos _).le
  have hJop : J.toContinuousLinearMap = (T g⁻¹).comp (J.toContinuousLinearMap.comp (T g⁻¹)) :=
    ContinuousLinearMap.ext hconj
  have hJn : ‖J.toContinuousLinearMap‖ ≤ Real.exp (-L) ^ 2 * ‖J.toContinuousLinearMap‖ := by
    calc ‖J.toContinuousLinearMap‖ = ‖(T g⁻¹).comp (J.toContinuousLinearMap.comp (T g⁻¹))‖ :=
          congrArg norm hJop
      _ ≤ ‖T g⁻¹‖ * (‖J.toContinuousLinearMap‖ * ‖T g⁻¹‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ Real.exp (-L) * (‖J.toContinuousLinearMap‖ * Real.exp (-L)) := by
          gcongr
      _ = Real.exp (-L) ^ 2 * ‖J.toContinuousLinearMap‖ := by ring
  have hJ0 : ‖J.toContinuousLinearMap‖ = 0 := by
    have hq2 : Real.exp (-L) ^ 2 < 1 := by nlinarith
    by_contra hne
    have hpos := lt_of_le_of_ne (norm_nonneg J.toContinuousLinearMap) (Ne.symm hne)
    nlinarith [mul_pos hpos (sub_pos.mpr hq2)]
  -- The space is nonzero: the indicator of a compact neighbourhood of 1 has positive norm.
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hKm : MeasurableSet K := hKc.measurableSet
  have hdc : Continuous fun x : G ↦ intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)) := by
    have hl : Continuous fun x : G ↦ Real.log ((m x).val : ℝ) :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
        fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    unfold intervalSobolevDensity
    fun_prop
  have hdpos (x : G) : 0 < intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)) := by
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have : IsLocallyFiniteMeasure (μ.withDensity d) := by
    simp only [hd_def, Bool.false_eq_true, ite_false]
    exact IsLocallyFiniteMeasure.withDensity_ofReal hdc
  have hfin : μ.withDensity d K ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.withDensity d K ≠ 0 := by
    intro h0
    have hμν : μ ≪ μ.withDensity d := by
      refine withDensity_absolutelyContinuous' ?_ (.of_forall fun x ↦ ?_)
      · simp only [hd_def, Bool.false_eq_true, ite_false]
        exact hdc.measurable.ennreal_ofReal.aemeasurable
      · simp only [hd_def, Bool.false_eq_true, ite_false]
        exact (ENNReal.ofReal_pos.mpr (hdpos x)).ne'
    exact (Measure.measure_pos_of_mem_nhds μ hK1).ne' (hμν h0)
  let v : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0 :=
    indicatorConstLp 2 hKm hfin (1 : ℂ)
  have hv : v ≠ 0 := by
    intro h
    have hn := congrArg norm h
    rw [norm_zero, norm_indicatorConstLp' (by norm_num) hpos, norm_one, one_mul] at hn
    exact (Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos hfin) _).ne' hn
  apply hv
  have hJv : J v = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm ?_ (norm_nonneg _)
    calc ‖J v‖ = ‖J.toContinuousLinearMap v‖ := rfl
      _ ≤ ‖J.toContinuousLinearMap‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = 0 := by rw [hJ0, zero_mul]
  have h := congrArg J.symm hJv
  rwa [ContinuousLinearEquiv.symm_apply_apply, map_zero] at h

/-- Paper: Theorem 10.1.2.1, p. 437. Take ℚ, I = {1} and s = 0. The indicator
of |g| < 1 is square integrable for t² dt/t in the norm coordinate t, while its
inverse pullback is the indicator of |g| > 1, which has infinite squared integral. -/
theorem Printed.ideleClassSobolev_inversion_automorphism_false :
    ¬ Printed.ideleClassSobolev_inversion_automorphism := by
  intro h
  obtain ⟨J, hJ⟩ := h ℚ 1 1 0 le_rfl le_rfl
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  let : T2Space (IdeleClassGroup (𝓞 ℚ) ℚ) := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.1
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.1
  let : SecondCountableTopology (IdeleClassGroup (𝓞 ℚ) ℚ) := by
    let := idele_secondCountable ℚ
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 ℚ) ℚ ⧸ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ))
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let m : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let g : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hg : m g = t := canonicalIdeleNormSection_rightInverse ℚ t
  exact Printed.ideleClassSobolev_inversion_automorphism_false_aux
    (ideleClassTamagawaMeasure ℚ) m g (by rw [hg]; norm_num [t]) J hJ

/-- Paper: Announcement before Lemma 10.1.1.3, p. 435. In the a-line
notation the local Fourier transform extends at precisely the half weight. -/
def Printed.sLocalThetaSobolev_fourier_on_line : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s),
    let hp : 0 < a + 0 := by simpa using ha
    let H := ↥(sLocalThetaSobolev F S ha (le_refl (0 : ℝ)) hs hp)
    let j := sLocalThetaSobolevInclusion F S ha (le_refl (0 : ℝ)) hs hp
    (∃ T : H →L[ℂ] H, ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      T (j (Submodule.Quotient.mk f)) =
        j (Submodule.Quotient.mk (sAdeleSchwartzFourier (F := F) (S := S) f))) ↔ a = 1 / 2

/-- Paper: Announcement before Lemma 10.1.1.3, p. 435. Take ℚ, S = {∞},
a = 1/2 and s = 2. For the even tests exp(-πx²) cos(2πNx) the input
norms are bounded, while the Fourier Gaussian peak at N gives a squared
norm growing at least as fast as (log N)². -/
theorem Printed.sLocalThetaSobolev_fourier_on_line_false :
    ¬ Printed.sLocalThetaSobolev_fourier_on_line := by sorry

end RiemannMasullo
