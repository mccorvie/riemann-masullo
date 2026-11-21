/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The translation, strong measurability, and averaging arguments adapt the Apache-2.0 Tau Ceti
port in jonhanke/algebraic-number-theory-lean at 5ea368e03a066197d53114efa8be66d351a9f060.
They use NumberFieldKB/TauCetiPort modules RepresentationTheory/Continuous/LeftRegular.lean,
MeasureTheory/Function/StronglyMeasurable/InnerRegular.lean, and
RepresentationTheory/Continuous/Integrated/Basic.lean, specialized to complex Hilbert
spaces and multiplicative groups.
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.UrysohnsLemma

/-!
# Separation by continuous characters

The left regular representation detects every nonidentity element. In its commutative
double commutant, Haar averaging gives operators whose translates vary continuously in
operator norm. A character of the double commutant that detects a moved average then
restricts to a continuous circle-valued character of the group.
-/

noncomputable section

open MeasureTheory Topology Filter Set WeakDual
open scoped ENNReal

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

section Translation

variable [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]

/-- The left regular action on `Lᵖ` by precomposition with inverse translation. -/
private def haarTranslation (p : ℝ≥0∞) [Fact (1 ≤ p)] : G →* (Lp ℂ p μ →L[ℂ] Lp ℂ p μ) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (g⁻¹ * ·)
    (measurePreserving_mul_left μ g⁻¹)).toContinuousLinearMap
  map_one' := ContinuousLinearMap.ext fun f ↦ by
    change Lp.compMeasurePreserving ((1 : G)⁻¹ * ·) _ f = f
    simpa only [inv_one, one_mul, ← Function.id_def] using Lp.compMeasurePreserving_id_apply f
  map_mul' g h := ContinuousLinearMap.ext fun f ↦ by
    have hcomp : (fun x : G ↦ (g * h)⁻¹ * x) = (h⁻¹ * ·) ∘ (g⁻¹ * ·) := by
      ext x
      simp [mul_inv_rev, mul_assoc]
    change Lp.compMeasurePreserving ((g * h)⁻¹ * ·) _ f =
      Lp.compMeasurePreserving (g⁻¹ * ·) _ (Lp.compMeasurePreserving (h⁻¹ * ·) _ f)
    simp only [hcomp]
    exact Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left μ h⁻¹) (measurePreserving_mul_left μ g⁻¹)

omit [T2Space G] [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] in
private theorem haarTranslation_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : G) (f : Lp ℂ p μ) :
    ‖haarTranslation μ p g f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

omit [T2Space G] in
private theorem haarTranslation_continuous (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp ℂ p μ) : Continuous fun g : G ↦ haarTranslation μ p g f := by
  have hg : Continuous fun g : G ↦ ContinuousMap.mulLeft (X := G) g⁻¹ :=
    (ContinuousMap.curry
      ⟨fun q : G × G ↦ q.1⁻¹ * q.2, continuous_fst.inv.mul continuous_snd⟩).continuous
  exact continuous_const.compMeasurePreservingLp hg _ hp

omit [μ.InnerRegularCompactLTTop] in
private theorem haarTranslation_ne_one {g : G} (hg : g ≠ 1) :
    haarTranslation μ 2 g ≠ 1 := by
  obtain ⟨f, h1, hcomp, hsupp, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (X := G) (K := {1}) isCompact_singleton (V := {g⁻¹}ᶜ) isOpen_compl_singleton
    (by simpa [eq_comm] using hg)
  let u : G → ℂ := fun x ↦ (f x : ℂ)
  have huc : Continuous u := Complex.continuous_ofReal.comp f.continuous
  have hu := huc.memLp_of_hasCompactSupport (μ := μ) (p := 2)
    ((show HasCompactSupport f from hcomp).comp_left Complex.ofReal_zero : HasCompactSupport u)
  intro h
  have heq : (fun x : G ↦ u (g⁻¹ * x)) =ᵐ[μ] u := by
    have hcoe : (haarTranslation μ 2 g (hu.toLp u)) =ᵐ[μ] fun x ↦ u (g⁻¹ * x) :=
      (Lp.coeFn_compMeasurePreserving _ _).trans
        ((measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp hu.coeFn_toLp)
    rw [h, one_apply_eq_self] at hcoe
    exact hcoe.symm.trans hu.coeFn_toLp
  have hzero : f g⁻¹ = 0 := image_eq_zero_of_notMem_tsupport (fun hx ↦ (hsupp hx) rfl)
  have hone : f 1 = 1 := h1 rfl
  have hp := congrFun (Measure.eq_of_ae_eq heq (huc.comp (continuous_const.mul continuous_id)) huc) 1
  simp [u, hzero, hone] at hp

end Translation

section Averaging

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [μ.InnerRegularCompactLTTop]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
  (hc : ∀ v, Continuous fun g ↦ U g v)

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure]
  [InnerProductSpace ℂ H] [CompleteSpace H] in
private theorem aestronglyMeasurableOn_of_finite_measure {f : G → H} (hf : Continuous f)
    {s : Set G} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    AEStronglyMeasurable f (μ.restrict s) := by
  choose K hKs hKc hKcl hμK using fun n : ℕ ↦
    hs.exists_isCompact_isClosed_sdiff_lt hμs (ε := (n + 1 : ℝ≥0∞)⁻¹) (by simp)
  have hnull : μ (s \ ⋃ n, K n) = 0 := by
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n ↦ ?_)
    calc
      μ (s \ ⋃ n, K n) ≤ μ (s \ K n) :=
        measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))
      _ ≤ (n + 1 : ℝ≥0∞)⁻¹ := (hμK n).le
      _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
  have hae : (⋃ n, K n : Set G) =ᵐ[μ] s := by
    have hsub : s ≤ᵐ[μ] ⋃ n, K n := ae_subset.2 hnull
    filter_upwards [hsub] with g hg
    exact ⟨fun h ↦ iUnion_subset hKs h, hg⟩
  rw [← Measure.restrict_congr_set hae, aestronglyMeasurable_iUnion_iff]
  exact fun n ↦ hf.continuousOn.aestronglyMeasurable_of_isCompact (hKc n) (hKcl n).measurableSet

include hU hc in
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [CompleteSpace H] in
private theorem integrable_weighted_orbit (f : Lp ℂ 1 μ) (v : H) :
    Integrable (fun g ↦ f g • U g v) μ := by
  have hf := L1.integrable_coeFn f
  have hfinite := hf.aefinStronglyMeasurable
  let s := hfinite.sigmaFiniteSet
  have horbit : AEStronglyMeasurable (fun g ↦ U g v) (μ.restrict s) := by
    let ν := μ.restrict s
    have : SigmaFinite ν := inferInstance
    have hspan (n : ℕ) : AEStronglyMeasurable (fun g ↦ U g v)
        (ν.restrict (spanningSets ν n)) :=
      aestronglyMeasurableOn_of_finite_measure ν (hc v)
        (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top ν n).ne
    change AEStronglyMeasurable _ ν
    rw [← Measure.restrict_univ (μ := ν), ← iUnion_spanningSets ν,
      aestronglyMeasurable_iUnion_iff]
    exact hspan
  refine (hf.norm.mul_const ‖v‖).mono' ?_ (.of_forall fun g ↦ by rw [norm_smul, hU])
  have hzero : AEStronglyMeasurable (fun g ↦ f g • U g v) (μ.restrict sᶜ) := by
    refine (aestronglyMeasurable_const (b := (0 : H))).congr ?_
    filter_upwards [hfinite.ae_eq_zero_compl] with g hg
    change (f : G → ℂ) g = 0 at hg
    rw [hg, zero_smul]
  change AEStronglyMeasurable ((f : G → ℂ) • fun g ↦ U g v) μ
  have hm := aestronglyMeasurable_union_iff.mpr
    ⟨hf.aestronglyMeasurable.restrict.smul horbit, hzero⟩
  simpa only [union_compl_self, Measure.restrict_univ] using hm

/-- Averaging the orbit of each vector gives a bounded operator depending continuously on
the integrable weight. -/
private def averageOrbit : Lp ℂ 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun f v ↦ ∫ g, f g • U g v ∂μ)
      (fun f₁ f₂ v ↦ by
        rw [← integral_add (integrable_weighted_orbit μ U hU hc f₁ v)
          (integrable_weighted_orbit μ U hU hc f₂ v)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f₁ f₂] with g hg
        rw [hg, Pi.add_apply, add_smul])
      (fun c f v ↦ by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with g hg
        rw [hg, Pi.smul_apply, smul_eq_mul, mul_smul])
      (fun f v w ↦ by
        rw [← integral_add (integrable_weighted_orbit μ U hU hc f v)
          (integrable_weighted_orbit μ U hU hc f w)]
        simp_rw [map_add, smul_add])
      (fun c f v ↦ by rw [← integral_smul]; simp_rw [map_smul, smul_comm c]))
    1 fun f v ↦ by
      simp only [one_mul, L1.norm_eq_integral_norm, ← integral_mul_const]
      apply norm_integral_le_of_norm_le
      · exact (L1.integrable_coeFn f).norm.mul_const _
      · exact .of_forall fun g ↦ by rw [norm_smul, hU]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [CompleteSpace H] in
private theorem averageOrbit_apply (f : Lp ℂ 1 μ) (v : H) :
    averageOrbit μ U hU hc f v = ∫ g, f g • U g v ∂μ := rfl

omit [LocallyCompactSpace G] in
private theorem averageOrbit_translate (f : Lp ℂ 1 μ) (g : G) :
    U g * averageOrbit μ U hU hc f = averageOrbit μ U hU hc (haarTranslation μ 1 g f) := by
  ext v
  rw [mul_apply_eq_comp, averageOrbit_apply, averageOrbit_apply,
    ← (U g).integral_comp_comm (integrable_weighted_orbit μ U hU hc f v)]
  calc
    _ = ∫ k, f (g⁻¹ * (g * k)) • U (g * k) v ∂μ := by
      simp [map_mul, mul_apply_eq_comp]
    _ = ∫ k, f (g⁻¹ * k) • U k v ∂μ :=
      integral_mul_left_eq_self (fun k ↦ f (g⁻¹ * k) • U k v) g
    _ = _ := integral_congr_ae <| by
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)]
        with k hk
      exact congrArg (· • U k v) hk.symm

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] in
private theorem averageOrbit_commutes (f : Lp ℂ 1 μ) (T : H →L[ℂ] H)
    (hT : ∀ g, U g * T = T * U g) :
    T * averageOrbit μ U hU hc f = averageOrbit μ U hU hc f * T := by
  ext v
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    averageOrbit_apply, averageOrbit_apply,
    ← T.integral_comp_comm (integrable_weighted_orbit μ U hU hc f v)]
  simp only [map_smul]
  exact integral_congr_ae <| .of_forall fun g ↦
    congrArg (fun S : H →L[ℂ] H ↦ f g • S v) (hT g).symm

omit [IsTopologicalGroup G] in
/-- Averages of norm at most one approximate each vector. -/
private theorem exists_averageOrbit_close (v : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Lp ℂ 1 μ, ‖f‖ ≤ 1 ∧ dist (averageOrbit μ U hU hc f v) v < ε := by
  let s : Set G := {g | ‖U g v - v‖ < ε / 2}
  have hs : s ∈ 𝓝 (1 : G) := by
    have ht : ContinuousAt (fun g ↦ ‖U g v - v‖) (1 : G) :=
      ((hc v).sub continuous_const).norm.continuousAt
    exact ht (by simpa using Iio_mem_nhds (half_pos hε))
  obtain ⟨K, ⟨hKnhds, hK⟩, hKs⟩ := (compact_basis_nhds (1 : G)).mem_iff.mp hs
  have hKpos : 0 < μ.real K := ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds hKnhds).ne'
    hK.measure_lt_top.ne
  let f : G → ℂ := K.indicator (fun _ ↦ 1)
  have hf : Integrable f μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hfi : ∫ g in K, U g v ∂μ = averageOrbit μ U hU hc (hf.toL1 f) v := by
    rw [averageOrbit_apply, ← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toL1] with g hg
    change K.indicator (fun x ↦ U x v) g = (hf.toL1 f : G → ℂ) g • U g v
    rw [hg]
    by_cases hgK : g ∈ K <;> simp [f, hgK]
  let a : ℂ := (μ.real K : ℂ)⁻¹
  have hfNorm : ‖hf.toL1 f‖ = μ.real K := by
    rw [L1.norm_eq_integral_norm]
    have h : (fun g ↦ ‖hf.toL1 f g‖) =ᵐ[μ] K.indicator (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hf.coeFn_toL1] with g hg
      change hf.toL1 f g = f g at hg
      rw [hg]
      by_cases hgK : g ∈ K <;> simp [f, hgK]
    rw [integral_congr_ae h]
    exact integral_indicator_one hK.measurableSet
  refine ⟨a • hf.toL1 f, ?_, ?_⟩
  · rw [norm_smul, hfNorm]
    simp [a, abs_of_pos hKpos, hKpos.ne']
  have hint : IntegrableOn (fun g ↦ U g v) K μ := by
    apply (integrableOn_const (C := ‖v‖) hK.measure_lt_top.ne).mono'
      ((hc v).continuousOn.aestronglyMeasurable_of_isCompact hK hK.measurableSet)
    exact .of_forall fun g ↦ (hU g v).le
  have hnorm : ‖∫ g in K, U g v - v ∂μ‖ ≤ μ.real K * (ε / 2) :=
    (mul_comm (ε / 2) (μ.real K)) ▸
      norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun g hg ↦ (hKs hg).le)
  have havg : averageOrbit μ U hU hc (a • hf.toL1 f) v - v =
      a • (∫ g in K, U g v - v ∂μ) := by
    rw [map_smul, smul_apply, ← hfi, integral_sub hint
      (integrableOn_const hK.measure_lt_top.ne), setIntegral_const, smul_sub,
      ← Complex.coe_smul, smul_smul]
    simp [a, hKpos.ne']
  rw [dist_eq_norm, havg, norm_smul]
  refine (mul_le_mul_of_nonneg_left hnorm (norm_nonneg a)).trans_lt ?_
  simp [a, abs_of_pos hKpos, hKpos.ne', half_lt_self hε]

omit [IsTopologicalGroup G] in
private theorem averageOrbit_dense (v : H) :
    v ∈ closure (range fun f ↦ averageOrbit μ U hU hc f v) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f, -, hf⟩ := exists_averageOrbit_close μ U hU hc v hε
  exact ⟨_, mem_range_self f, by rwa [dist_comm]⟩

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] in
/-- Haar averaging is contractive as a map from integrable weights to operators. -/
private theorem norm_averageOrbit_le (f : Lp ℂ 1 μ) : ‖averageOrbit μ U hU hc f‖ ≤ ‖f‖ := by
  have h : ‖averageOrbit μ U hU hc‖ ≤ 1 := by
    unfold averageOrbit
    exact LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  simpa using (averageOrbit μ U hU hc).le_of_opNorm_le h f

end Averaging

section Spectrum

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [μ.InnerRegularCompactLTTop]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
  (hc : ∀ v, Continuous fun g ↦ U g v)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Spectral characters on a compact level set of the average control its translates. -/
private theorem exists_compact_test_of_gelfand {A : Type*} [CommCStarAlgebra A]
    (V : G →* A) (hVstar : ∀ g, star (V g) = V g⁻¹) (a : A)
    (hTranslate : Continuous fun g ↦ V g * a) {r ε : ℝ}
    (hr : 0 < r) (ha : ‖a‖ ≤ r) (hε : 0 < ε) :
    ∃ K : Set (PontryaginDual G), IsCompact K ∧
      ∀ x : G, (∀ χ ∈ K, dist (χ x) 1 ≤ ε) → ‖V x * a - a‖ ≤ ε * r := by
  let Φ := gelfandTransform ℂ A
  have hΦ := gelfandTransform_isometry A
  have hNorm (b : A) : ‖Φ b‖ = ‖b‖ := hΦ.norm_map_of_map_zero (map_zero Φ) b
  -- On this spectral level set we can divide by the value of the average.
  let Sε : Set (characterSpace ℂ A) := {ω | ε * r / 2 ≤ ‖ω a‖}
  have hSε : IsCompact Sε := (isClosed_le continuous_const (Φ a).continuous.norm).isCompact
  have hNonzero (ω : Sε) : (ω.1 : characterSpace ℂ A) a ≠ 0 :=
    norm_pos_iff.mp ((by positivity : 0 < ε * r / 2).trans_le ω.2)
  have hχ (ω : characterSpace ℂ A) (g : G) : ‖ω (V g)‖ = 1 := by
    have heq : star (ω (V g)) * ω (V g) = 1 := by
      rw [← map_star, ← map_mul, hVstar, ← map_mul, inv_mul_cancel, map_one, map_one]
    have habs := congrArg norm heq
    rw [norm_mul, norm_star, norm_one, ← sq] at habs
    nlinarith [norm_nonneg (ω (V g))]
  let test (ω : Sε) (g : G) : ℂ := (ω.1 : characterSpace ℂ A) (V g)
  have hTest : Continuous (Function.uncurry test) := by
    have hEval : Continuous fun p : Sε × G ↦ Φ (V p.2 * a) p.1.1 :=
      continuous_eval.comp ((hΦ.continuous.comp (hTranslate.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp continuous_fst))
    refine (hEval.div ((Φ a).continuous.comp
      (continuous_subtype_val.comp continuous_fst)) (fun p ↦ hNonzero p.1)).congr ?_
    intro p
    change (p.1.1 : characterSpace ℂ A) (V p.2 * a) / (p.1.1 : characterSpace ℂ A) a =
      (p.1.1 : characterSpace ℂ A) (V p.2)
    rw [map_mul, mul_div_cancel_right₀ _ (hNonzero p.1)]
  let χ (ω : Sε) : PontryaginDual G :=
    { toFun g := ⟨test ω g, mem_sphere_zero_iff_norm.mpr (hχ ω.1 g)⟩
      map_one' := Subtype.ext (by
        change (ω.1 : characterSpace ℂ A) (V 1) = 1
        rw [map_one, map_one])
      map_mul' g k := Circle.ext (by
        change (ω.1 : characterSpace ℂ A) (V (g * k)) =
          (ω.1 : characterSpace ℂ A) (V g) * (ω.1 : characterSpace ℂ A) (V k)
        rw [map_mul, map_mul])
      continuous_toFun := (hTest.comp (continuous_const.prodMk continuous_id)).subtype_mk _ }
  have hContinuous : Continuous χ :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry χ (hTest.subtype_mk _)
  let : CompactSpace Sε := isCompact_iff_compactSpace.mp hSε
  refine ⟨range χ, isCompact_range hContinuous, fun x hx ↦ ?_⟩
  rw [← hNorm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro ω
  change ‖ω (V x * a - a)‖ ≤ ε * r
  rw [map_sub, map_mul, ← sub_one_mul, norm_mul]
  by_cases hω : ω ∈ Sε
  · have hDist : ‖ω (V x) - 1‖ ≤ ε := by
      have h := hx (χ ⟨ω, hω⟩) (mem_range_self (⟨ω, hω⟩ : Sε))
      change dist (ω (V x)) (1 : ℂ) ≤ ε at h
      simpa only [dist_eq_norm] using h
    have haNorm : ‖ω a‖ ≤ r :=
      (ContinuousMap.norm_coe_le_norm (Φ a) ω).trans
        ((hNorm a).trans_le ha)
    exact mul_le_mul hDist haNorm (norm_nonneg _) hε.le
  · calc
      _ ≤ 2 * ‖ω a‖ := by
        gcongr
        simpa [hχ, one_add_one_eq_two] using norm_sub_le (ω (V x)) 1
      _ ≤ ε * r := by
        exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 2)).mp (le_of_not_ge hω)

include hU in
/-- The adjoint of a unitary group action is the action of the inverse. -/
private theorem unitary_apply_star (g : G) : star (U g) = U g⁻¹ := by
  have hh := (U g).norm_map_iff_adjoint_comp_self.mp (hU g)
  change star (U g) * U g = 1 at hh
  calc
    star (U g) = (star (U g) * U g) * U g⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = U g⁻¹ := by rw [hh, one_mul]

include μ hU hc in
open scoped IsMulCommutative Pointwise in
/-- The double commutant of the representation is commutative and contains
the representation and all its Haar averages. -/
private theorem exists_commutative_algebra_with_averages :
    ∃ A : StarSubalgebra ℂ (H →L[ℂ] H), IsClosed (A : Set (H →L[ℂ] H)) ∧
      IsMulCommutative A ∧ (∀ g, U g ∈ A) ∧
      (∀ f, averageOrbit μ U hU hc f ∈ A) := by
  let B := H →L[ℂ] H
  let S : Set B := range U
  let A := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set B)
  have hS : S ∪ star S = S := by
    apply union_eq_self_of_subset_right
    intro T hT
    obtain ⟨g, hg⟩ : star T ∈ range U := hT
    exact ⟨g⁻¹, by rw [← unitary_apply_star U hU, hg, star_star]⟩
  have hA : (A : Set B) = S.centralizer.centralizer := by
    rw [StarSubalgebra.coe_centralizer_centralizer, hS]
  have hcomm : S.Pairwise Commute := .of_forall₂ fun _ ha _ hb ↦ by
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hb
    change U g * U k = U k * U g
    rw [← map_mul, ← map_mul, mul_comm g k]
  have hCommA : IsMulCommutative A := .of_setLike_mul_comm fun a ha b hb ↦ by
    change a ∈ (A : Set B) at ha
    change b ∈ (A : Set B) at hb
    rw [hA] at ha hb
    exact Set.centralizer_centralizer_comm_of_comm hcomm _ ha _ hb
  refine ⟨A, hA ▸ Set.isClosed_centralizer _, hCommA, fun g ↦ ?_, fun f ↦ ?_⟩
  · change U g ∈ (A : Set B)
    rw [hA]
    exact Set.subset_centralizer_centralizer (mem_range_self _)
  · change averageOrbit μ U hU hc f ∈ (A : Set B)
    rw [hA]
    intro T hT
    exact averageOrbit_commutes μ U hU hc f T (fun g ↦ hT (U g) (mem_range_self g))

include μ hU hc in
open scoped IsMulCommutative Pointwise in
/-- A compact family of characters controls the norm of a translated Haar average. -/
private theorem exists_compact_test_of_averageOrbit (f : Lp ℂ 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (PontryaginDual G), IsCompact K ∧
      ∀ x : G, (∀ χ ∈ K, dist (χ x) 1 ≤ ε) →
        ‖U x * averageOrbit μ U hU hc f - averageOrbit μ U hU hc f‖ ≤ ε * ‖f‖ := by
  by_cases hf : f = 0
  · exact ⟨∅, isCompact_empty, by simp [hf]⟩
  obtain ⟨A, hClosed, hComm, hGroup, hAverage⟩ :=
    exists_commutative_algebra_with_averages μ U hU hc
  let : IsClosed (A : Set (H →L[ℂ] H)) := hClosed
  let : IsMulCommutative A := hComm
  let : CommCStarAlgebra A := { }
  let V : G →* A := U.codRestrict A.toSubmonoid hGroup
  have hVstar (g : G) : star (V g) = V g⁻¹ := Subtype.ext (unitary_apply_star U hU g)
  let a : A := ⟨averageOrbit μ U hU hc f, hAverage f⟩
  have hTranslate : Continuous fun g ↦ V g * a := by
    have h : Continuous fun g ↦ U g * averageOrbit μ U hU hc f := by
      simp_rw [averageOrbit_translate]
      exact (averageOrbit μ U hU hc).continuous.comp
        (haarTranslation_continuous μ 1 ENNReal.one_ne_top f)
    exact h.subtype_mk _
  exact exists_compact_test_of_gelfand V hVstar a hTranslate
    (norm_pos_iff.mpr hf) (norm_averageOrbit_le μ U hU hc f) hε

include μ hU hc in
/-- A strongly continuous unitary representation of an abelian group yields a continuous
character detecting any element that acts nontrivially. -/
private theorem exists_character_of_rep_ne_one {x : G} (hx : U x ≠ 1) :
    ∃ χ : PontryaginDual G, χ x ≠ 1 := by
  by_contra! hall
  obtain ⟨f, hf⟩ : ∃ f : Lp ℂ 1 μ,
      U x * averageOrbit μ U hU hc f ≠ averageOrbit μ U hU hc f := by
    by_contra! hall
    apply hx
    apply ContinuousLinearMap.ext
    intro v
    have heq : IsClosed {w : H | U x w = w} := isClosed_eq (U x).continuous continuous_id
    apply closure_minimal _ heq (averageOrbit_dense μ U hU hc v)
    rintro _ ⟨f, rfl⟩
    exact congrArg (fun T : H →L[ℂ] H ↦ T v) (hall f)
  let d := ‖U x * averageOrbit μ U hU hc f - averageOrbit μ U hU hc f‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hf)
  let ε := d / (‖f‖ + 1)
  obtain ⟨K, -, hK⟩ := exists_compact_test_of_averageOrbit μ U hU hc f (ε := ε) (by positivity)
  have h := hK x fun χ _ ↦ by simp [hall, show 0 ≤ ε by positivity]
  change d ≤ ε * ‖f‖ at h
  rw [show ε * ‖f‖ = d * ‖f‖ / (‖f‖ + 1) by dsimp [ε]; ring] at h
  have := (le_div_iff₀ (by positivity : 0 < ‖f‖ + 1)).mp h
  nlinarith

end Spectrum

/-- Each nonidentity element of a locally compact Hausdorff abelian group is detected by a
continuous circle-valued character. -/
public theorem exists_pontryaginDual_apply_ne_one {x : G} (hx : x ≠ 1) :
    ∃ χ : PontryaginDual G, χ x ≠ 1 := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  exact exists_character_of_rep_ne_one μ (haarTranslation μ 2) (haarTranslation_norm μ 2)
    (haarTranslation_continuous μ 2 (by simp)) (haarTranslation_ne_one μ hx)

open scoped Pointwise in
/-- A compact family of continuous characters detects membership in an identity neighborhood. -/
public theorem exists_compact_pontryaginDual_test {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : Set (PontryaginDual G), IsCompact K ∧
      ∀ x : G, (∀ χ ∈ K, dist (χ x) 1 < 1 / 4) → x ∈ U := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  obtain ⟨V, hV, -, hInv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨D, ⟨hD, hDc⟩, hDV⟩ := (compact_basis_nhds (1 : G)).mem_iff.mp hV
  let v := indicatorConstLp (μ := μ) 2 hDc.isClosed.measurableSet hDc.measure_lt_top.ne (1 : ℂ)
  have hμD : 0 < μ.real D :=
    ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds hD).ne' hDc.measure_lt_top.ne
  have hv : 0 < ‖v‖ := by
    dsimp [v]
    rw [norm_indicatorConstLp (by norm_num) (by simp), norm_one, one_mul]
    exact Real.rpow_pos_of_pos hμD _
  let T := haarTranslation μ 2
  have hT := haarTranslation_norm μ 2
  have hc := haarTranslation_continuous μ 2 (by simp)
  obtain ⟨f, hf, hfv⟩ := exists_averageOrbit_close μ T hT hc v (ε := ‖v‖ / 4) (by positivity)
  let a := averageOrbit μ T hT hc f
  have hav : ‖a v - v‖ < ‖v‖ / 4 := by
    simpa only [dist_eq_norm] using hfv
  obtain ⟨K, hK, hTest⟩ := exists_compact_test_of_averageOrbit μ T hT hc f
    (ε := 1 / 4) (by norm_num)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  by_contra hxU
  -- Away from the neighborhood, the translate of the indicator vanishes on D.
  have hLower : ‖v‖ ≤ ‖T x v - v‖ := by
    let m : MeasurePreserving (x⁻¹ * ·) μ μ := measurePreserving_mul_left μ x⁻¹
    let ind : G → ℂ := D.indicator (fun _ ↦ 1)
    have hvD : ⇑v =ᵐ[μ] ind := indicatorConstLp_coeFn
    have hTx : ⇑(T x v) =ᵐ[μ] ind ∘ (x⁻¹ * ·) := by
      change ⇑(Lp.compMeasurePreserving (x⁻¹ * ·) m v) =ᵐ[μ] _
      exact (Lp.coeFn_compMeasurePreserving v m).trans
        (m.quasiMeasurePreserving.ae_eq_comp hvD)
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (T x v) v, hTx, hvD] with y hsub hTy hvy
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hTy, hvy]
    by_cases hy : y ∈ D
    · have hnot : x⁻¹ * y ∉ D := by
        intro h
        apply hxU
        apply hVV
        refine ⟨y, hDV hy, (x⁻¹ * y)⁻¹, ?_, by simp⟩
        rw [← hInv]
        exact Set.inv_mem_inv.mpr (hDV h)
      simp [ind, hy, hnot]
    · simp [ind, hy]
  have hUpper : ‖T x * a - a‖ ≤ 1 / 4 :=
    (hTest x fun χ hχ ↦ (hx χ hχ).le).trans (by linarith)
  have hOp : ‖(T x * a - a) v‖ ≤ ‖v‖ / 4 := by
    simpa [div_eq_mul_inv, mul_comm] using
      (T x * a - a).le_of_opNorm_le hUpper v
  have hErr : ‖T x (v - a v)‖ < ‖v‖ / 4 := by
    rwa [hT, norm_sub_rev]
  have hdecomp : T x v - v = T x (v - a v) + (T x * a - a) v + (a v - v) := by
    rw [map_sub, sub_apply, mul_apply_eq_comp]
    abel
  rw [hdecomp] at hLower
  have hTriangle := (norm_add_le (T x (v - a v) + (T x * a - a) v) (a v - v)).trans
    (add_le_add (norm_add_le (T x (v - a v)) ((T x * a - a) v)) le_rfl)
  linarith

open scoped CompactlySupported in
/-- A positive functional on complex continuous functions on a compact space is integrated
against a finite regular measure. Apply real Riesz–Markov to its real part. -/
private theorem exists_measure_of_positive_functional
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (L : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ q, 0 ≤ (L (star q * q)).re)
    (hStar : ∀ q, L (star q) = star (L q)) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧ σ.Regular ∧
      ∀ q : C(X, ℂ), (∫ x, q x ∂σ) = L q := by
  let toComplex (f : C_c(X, ℝ)) : C(X, ℂ) :=
    ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ (L (toComplex f)).re
      map_add' := fun f g ↦ by
        have h : toComplex (f + g) = toComplex f + toComplex g := by
          ext x
          exact Complex.ofReal_add _ _
        rw [h, map_add, Complex.add_re]
      map_smul' := fun r f ↦ by
        have h : toComplex (r • f) = (r : ℂ) • toComplex f := by
          ext x
          exact Complex.ofReal_mul _ _
        rw [h, map_smul, smul_eq_mul]
        simp [Complex.mul_re, smul_eq_mul]
      monotone' := fun f g hfg ↦ by
        let root : C(X, ℂ) := ⟨fun x ↦ (Real.sqrt (g x - f x) : ℂ),
          Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
            (g.continuous.sub f.continuous))⟩
        have h : toComplex g - toComplex f = star root * root := by
          ext x
          change (g x : ℂ) - (f x : ℂ) =
            star ((Real.sqrt (g x - f x) : ℝ) : ℂ) * (Real.sqrt (g x - f x) : ℂ)
          rw [Complex.star_def, Complex.conj_ofReal, ← sq, ← Complex.ofReal_pow,
            Real.sq_sqrt (sub_nonneg.mpr (hfg x)), Complex.ofReal_sub]
        have hpos := hL root
        rw [← h, map_sub, Complex.sub_re] at hpos
        exact sub_nonneg.mp hpos }
  let σ := RealRMK.rieszMeasure Λ
  have hfinite : IsFiniteMeasure σ := ⟨isCompact_univ.measure_lt_top⟩
  refine ⟨σ, hfinite, inferInstance, fun q ↦ ?_⟩
  have hRe (q : C(X, ℂ)) : (∫ x, q x ∂σ).re = (L q).re := by
    let f : C_c(X, ℝ) := ⟨⟨fun x ↦ (q x).re, Complex.continuous_re.comp q.continuous⟩,
      HasCompactSupport.of_compactSpace _⟩
    have hInt := Complex.reCLM.integral_comp_comm
      (q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        (μ := σ))
    calc
      _ = ∫ x, f x ∂σ := hInt.symm
      _ = (L (toComplex f)).re := RealRMK.integral_rieszMeasure Λ f
      _ = _ := by
        have h : (2 : ℂ) • toComplex f = star q + q := by
          ext x
          change 2 * ((q x).re : ℂ) = star (q x) + q x
          simpa only [Complex.star_def, add_comm, Complex.ofReal_mul, Complex.ofReal_ofNat]
            using (Complex.add_conj (q x)).symm
        have hh := congrArg (fun p ↦ (L p).re) h
        simp [map_smul, smul_eq_mul, Complex.mul_re, hStar] at hh
        linarith
  apply Complex.ext (hRe q)
  have h := hRe (Complex.I • q)
  simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, map_smul,
    Complex.I_mul_re, neg_inj] at h
  exact h

open scoped InnerProductSpace in
/-- The vector functional on a commutative algebra of operators has a finite regular
representing measure on its Gelfand spectrum. -/
private theorem exists_spectral_measure {A H : Type*} [CommCStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace (characterSpace ℂ A)] [BorelSpace (characterSpace ℂ A)]
    (j : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ∃ σ : Measure (characterSpace ℂ A), IsFiniteMeasure σ ∧ σ.Regular ∧
      ∀ a : A, (∫ ω, ω a ∂σ) = ⟪v, j a v⟫_ℂ := by
  let Φ := gelfandStarTransform A
  let T := j.comp Φ.symm.toStarAlgHom
  let L : C(characterSpace ℂ A, ℂ) →ₗ[ℂ] ℂ :=
    (innerSL ℂ v).toLinearMap.comp
      ((ContinuousLinearMap.apply ℂ H v).toLinearMap.comp T.toLinearMap)
  have hL (q : C(characterSpace ℂ A, ℂ)) : L q = ⟪v, T q v⟫_ℂ := rfl
  obtain ⟨σ, hFinite, hRegular, hσ⟩ := exists_measure_of_positive_functional L
    (fun q ↦ by
      rw [hL, map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      change 0 ≤ (((‖T q v‖ : ℝ) : ℂ) ^ 2).re
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      positivity)
    (fun q ↦ by
      rw [hL, hL, map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, Complex.star_def, inner_conj_symm])
  refine ⟨σ, hFinite, hRegular, fun a ↦ ?_⟩
  change (∫ ω, Φ a ω ∂σ) = _
  rw [hσ, hL]
  change ⟪v, j (Φ.symm (Φ a)) v⟫_ℂ = _
  rw [StarAlgEquiv.symm_apply_apply]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- On the union of the sets where at least one norm-continuous translate is nonzero,
the spectral characters restrict continuously to characters of the group. -/
private theorem exists_continuous_dual_of_spectrum {A : Type*} [CommCStarAlgebra A]
    (V : G →* A) (hStar : ∀ g, star (V g) = V g⁻¹) {ι : Type*}
    (a : ι → A) (hTranslate : ∀ i, Continuous fun g ↦ V g * a i) :
    ∃ χ : {ω : characterSpace ℂ A | ∃ i, ω (a i) ≠ 0} → PontryaginDual G,
      Continuous χ ∧ ∀ ω g, (χ ω g : ℂ) = ω.1 (V g) := by
  let S : Set (characterSpace ℂ A) := {ω | ∃ i, ω (a i) ≠ 0}
  let Φ := gelfandTransform ℂ A
  let z (ω : S) (g : G) := ω.1 (V g)
  have hn (ω : S) (g : G) : ‖z ω g‖ = 1 := by
    have h : star (ω.1 (V g)) * ω.1 (V g) = 1 := by
      rw [← map_star, ← map_mul, hStar, ← map_mul, inv_mul_cancel, map_one, map_one]
    have hNorm := congrArg norm h
    rw [norm_mul, norm_star, norm_one, ← sq] at hNorm
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hNorm.trans (by norm_num))
  have hz : Continuous (Function.uncurry z) := by
    rw [continuous_iff_continuousAt]
    intro p
    obtain ⟨i, hi⟩ := p.1.2
    have hden : Continuous fun q : S × G ↦ Φ (a i) q.1.1 :=
      (Φ (a i)).continuous.comp (continuous_subtype_val.comp continuous_fst)
    have hnum : Continuous fun q : S × G ↦ Φ (V q.2 * a i) q.1.1 :=
      continuous_eval.comp (((gelfandTransform_isometry A).continuous.comp
        ((hTranslate i).comp continuous_snd)).prodMk
        (continuous_subtype_val.comp continuous_fst))
    refine (hnum.continuousAt.div hden.continuousAt hi).congr_of_eventuallyEq ?_
    filter_upwards [hden.continuousAt.eventually_ne hi] with q hq
    change q.1.1 (V q.2) = q.1.1 (V q.2 * a i) / q.1.1 (a i)
    change q.1.1 (a i) ≠ 0 at hq
    rw [map_mul, mul_div_cancel_right₀ _ hq]
  let χ (ω : S) : PontryaginDual G :=
    { toFun g := ⟨z ω g, mem_sphere_zero_iff_norm.mpr (hn ω g)⟩
      map_one' := Subtype.ext (by change ω.1 (V 1) = 1; rw [map_one, map_one])
      map_mul' g k := Circle.ext (by
        change ω.1 (V (g * k)) = ω.1 (V g) * ω.1 (V k)
        rw [map_mul, map_mul])
      continuous_toFun := (hz.comp (continuous_const.prodMk continuous_id)).subtype_mk _ }
  exact ⟨χ, ContinuousMonoidHom.continuous_of_continuous_uncurry χ (hz.subtype_mk _),
    fun _ _ ↦ rfl⟩

open scoped InnerProductSpace in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- If the operators with norm-continuous translates approximate the vector,
its spectral measure is carried by the open set on which they detect continuous
characters of the group. -/
private theorem exists_dual_measure_of_operators {A H : Type*} [CommCStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (j : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (V : G →* A) (hStar : ∀ g, star (V g) = V g⁻¹)
    {ι : Type*} (a : ι → A) (hTranslate : ∀ i, Continuous fun g ↦ V g * a i)
    (hApprox : ∀ ε > 0, ∃ i, ‖j (a i) v - v‖ < ε) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ g, (∫ χ, (χ g : ℂ) ∂ρ) = ⟪v, j (V g) v⟫_ℂ := by
  let X := characterSpace ℂ A
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let S : Set X := {ω | ∃ i, ω (a i) ≠ 0}
  have hOpen : IsOpen S := by
    rw [show S = ⋃ i, {ω : X | ω (a i) ≠ 0} by ext; simp [S]]
    exact isOpen_iUnion fun i ↦ isOpen_ne_fun (gelfandTransform ℂ A (a i)).continuous continuous_const
  obtain ⟨σ, hFinite, hRegular, hσ⟩ := exists_spectral_measure j v
  have hBound (b : A) : (∫ ω, ‖ω b‖ ^ 2 ∂σ) = ‖j b v‖ ^ 2 := by
    have hInt : Integrable (fun ω : X ↦ ω (star b * b)) σ :=
      (gelfandTransform ℂ A (star b * b)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      _ = ∫ ω, (ω (star b * b)).re ∂σ := by
        apply integral_congr_ae
        exact .of_forall fun ω ↦ by
          change ‖ω b‖ ^ 2 = (ω (star b * b)).re
          rw [map_mul, map_star, mul_comm, Complex.star_def, Complex.mul_conj,
            Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = (⟪v, j (star b * b) v⟫_ℂ).re := by
        change (∫ ω, Complex.reCLM (ω (star b * b)) ∂σ) = _
        rw [Complex.reCLM.integral_comp_comm hInt, hσ, Complex.reCLM_apply]
      _ = _ := by
        rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
        change (((‖j b v‖ : ℝ) : ℂ) ^ 2).re = _
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hMass : σ.real Sᶜ ≤ 0 := by
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    obtain ⟨i, hi⟩ := hApprox (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    let b := a i - 1
    have hInt : Integrable (fun ω : X ↦ ‖ω b‖ ^ 2) σ :=
      ((gelfandTransform ℂ A b).continuous.norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hInd : Sᶜ.indicator (fun _ ↦ (1 : ℝ)) ≤ fun ω : X ↦ ‖ω b‖ ^ 2 := by
      intro ω
      by_cases hω : ω ∈ Sᶜ
      · have hz : ω (a i) = 0 := by
          by_contra hn
          exact hω ⟨i, hn⟩
        simp [hω, b, map_sub, hz]
      · simp [hω]
    have hle := integral_mono
      ((integrableOn_const (C := (1 : ℝ)) (measure_ne_top σ Sᶜ)).integrable_indicator
        hOpen.measurableSet.compl) hInt hInd
    change (∫ ω, Sᶜ.indicator (1 : X → ℝ) ω ∂σ) ≤ _ at hle
    rw [integral_indicator_one hOpen.measurableSet.compl, hBound] at hle
    refine hle.trans ?_
    rw [show j b v = j (a i) v - v by simp [b], zero_add, ← Real.sq_sqrt hε.le]
    gcongr
  have hFull : σ.restrict S = σ := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    exact ((ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hMass ENNReal.toReal_nonneg)).resolve_right (measure_ne_top σ _)
  obtain ⟨χ, hχ, hEval⟩ := exists_continuous_dual_of_spectrum V hStar a hTranslate
  let τ : Measure S := σ.comap Subtype.val
  have hτ : IsFiniteMeasure τ := ⟨by
    rw [hOpen.isOpenEmbedding_subtypeVal.measurableEmbedding.comap_apply]
    exact measure_lt_top σ _⟩
  let : σ.InnerRegular := inferInstance
  let : τ.InnerRegular := Measure.InnerRegular.comap' σ hOpen.isOpenEmbedding_subtypeVal
  let ρ := Measure.map χ τ
  let : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map τ χ
  let : ρ.InnerRegular := Measure.InnerRegular.map_of_continuous hχ
  let : ρ.WeaklyRegular :=
    Measure.InnerRegularWRT.weaklyRegular_of_finite ρ
      Measure.InnerRegular.innerRegularWRT_isClosed_isOpen
  refine ⟨ρ, inferInstance, ⟨Measure.InnerRegular.innerRegular.mono
    (fun _ h ↦ h.measurableSet) (fun _ h ↦ h)⟩, fun g ↦ ?_⟩
  have hCont : Continuous fun ψ : PontryaginDual G ↦ (ψ g : ℂ) :=
    continuous_subtype_val.comp
      ((continuous_eval_const (F := C(G, Circle)) g).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous)
  calc
    _ = ∫ ω : S, ω.1 (V g) ∂τ := by
      rw [integral_map hχ.measurable.aemeasurable hCont.aestronglyMeasurable]
      exact integral_congr_ae (.of_forall fun ω ↦ hEval ω g)
    _ = ∫ ω, ω (V g) ∂σ := by
      exact (integral_subtype_comap hOpen.measurableSet (fun ω : X ↦ ω (V g))).trans
        (by rw [hFull])
    _ = _ := hσ (V g)

open scoped IsMulCommutative InnerProductSpace in
/-- Haar averaging supplies the norm-continuous translates needed by the spectral
representation of a coefficient of a strongly continuous unitary action. -/
private theorem exists_dual_measure_of_unitary
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
    (hc : ∀ v, Continuous fun g ↦ U g v) (v : H) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ g, (∫ χ, (χ g : ℂ) ∂ρ) = ⟪v, U g v⟫_ℂ := by
  obtain ⟨A, hClosed, hComm, hGroup, hAverage⟩ :=
    exists_commutative_algebra_with_averages μ U hU hc
  let : IsClosed (A : Set (H →L[ℂ] H)) := hClosed
  let : IsMulCommutative A := hComm
  let : CommCStarAlgebra A := { }
  let V : G →* A := U.codRestrict A.toSubmonoid hGroup
  let a (f : Lp ℂ 1 μ) : A := ⟨averageOrbit μ U hU hc f, hAverage f⟩
  have hTranslate (f : Lp ℂ 1 μ) : Continuous fun g ↦ V g * a f := by
    have h : Continuous fun g ↦ U g * averageOrbit μ U hU hc f := by
      simp_rw [averageOrbit_translate]
      exact (averageOrbit μ U hU hc).continuous.comp
        (haarTranslation_continuous μ 1 ENNReal.one_ne_top f)
    exact h.subtype_mk _
  have hApprox (ε : ℝ) (hε : 0 < ε) : ∃ f, ‖A.subtype (a f) v - v‖ < ε := by
    obtain ⟨f, -, hf⟩ := exists_averageOrbit_close μ U hU hc v hε
    refine ⟨f, ?_⟩
    change ‖averageOrbit μ U hU hc f v - v‖ < ε
    simpa only [dist_eq_norm] using hf
  exact exists_dual_measure_of_operators A.subtype v V
    (fun g ↦ Subtype.ext (unitary_apply_star U hU g)) a hTranslate hApprox

/-- The autocorrelation of a square-integrable function is the Fourier–Stieltjes
transform of a finite regular positive measure on the Pontryagin dual. -/
public theorem exists_haar_autocorrelation_measure
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] {f : G → ℂ} (hf : MemLp f 2 μ) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ x, (∫ χ, (χ x : ℂ) ∂ρ) = ∫ y, f y * star (f (x⁻¹ * y)) ∂μ := by
  let T := haarTranslation μ 2
  let U := T.comp (invMonoidHom (α := G))
  let v := hf.toLp f
  obtain ⟨ρ, hFinite, hRegular, hρ⟩ := exists_dual_measure_of_unitary μ U
    (fun g w ↦ haarTranslation_norm μ 2 g⁻¹ w)
    (fun w ↦ (haarTranslation_continuous μ 2 (by simp) w).comp continuous_inv) v
  refine ⟨ρ, hFinite, hRegular, fun x ↦ (hρ x).trans ?_⟩
  have hTx : ⇑(U x v) =ᵐ[μ] fun y ↦ f ((x⁻¹)⁻¹ * y) :=
    (Lp.coeFn_compMeasurePreserving v (measurePreserving_mul_left μ (x⁻¹)⁻¹)).trans
      ((measurePreserving_mul_left μ (x⁻¹)⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)
  rw [L2.inner_def, ← integral_mul_left_eq_self (μ := μ)
    (fun y ↦ f y * star (f (x⁻¹ * y))) x]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hTx] with y hy hxy
  rw [hy, hxy, inv_inv, inv_mul_cancel_left]
  exact RCLike.inner_apply (f y) (f (x * y))

end RiemannMasullo
