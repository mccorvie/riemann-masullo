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
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
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
private theorem averageOrbit_dense (v : H) :
    v ∈ closure (range fun f ↦ averageOrbit μ U hU hc f v) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
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
  refine ⟨_, ⟨a • hf.toL1 f, rfl⟩, ?_⟩
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
  rw [dist_comm, dist_eq_norm, havg, norm_smul]
  refine (mul_le_mul_of_nonneg_left hnorm (norm_nonneg a)).trans_lt ?_
  simp [a, abs_of_pos hKpos, hKpos.ne', half_lt_self hε]

end Averaging

section Spectrum

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [μ.InnerRegularCompactLTTop]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
  (hc : ∀ v, Continuous fun g ↦ U g v)

include μ hU hc in
open scoped IsMulCommutative Pointwise in
/-- A strongly continuous unitary representation of an abelian group yields a continuous
character detecting any element that acts nontrivially. -/
private theorem exists_character_of_rep_ne_one {x : G} (hx : U x ≠ 1) :
    ∃ χ : PontryaginDual G, χ x ≠ 1 := by
  let B := H →L[ℂ] H
  have hstar (g : G) : star (U g) = U g⁻¹ := by
    have hh := (U g).norm_map_iff_adjoint_comp_self.mp (hU g)
    change star (U g) * U g = 1 at hh
    calc
      star (U g) = (star (U g) * U g) * U g⁻¹ := by
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = U g⁻¹ := by rw [hh, one_mul]
  let S : Set B := range U
  let A := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set B)
  have hS : S ∪ star S = S := by
    apply union_eq_self_of_subset_right
    intro T hT
    obtain ⟨g, hg⟩ : star T ∈ range U := hT
    exact ⟨g⁻¹, by rw [← hstar, hg, star_star]⟩
  have hA : (A : Set B) = S.centralizer.centralizer := by
    rw [StarSubalgebra.coe_centralizer_centralizer, hS]
  let : IsClosed (A : Set B) := hA ▸ Set.isClosed_centralizer _
  have hcomm : S.Pairwise Commute := .of_forall₂ fun _ ha _ hb ↦ by
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hb
    change U g * U k = U k * U g
    rw [← map_mul, ← map_mul, mul_comm g k]
  let : IsMulCommutative A := .of_setLike_mul_comm fun a ha b hb ↦ by
    change a ∈ (A : Set B) at ha
    change b ∈ (A : Set B) at hb
    rw [hA] at ha hb
    exact Set.centralizer_centralizer_comm_of_comm hcomm _ ha _ hb
  let : CommCStarAlgebra A := { }
  let V : G →* A := U.codRestrict A.toSubmonoid fun g ↦ by
    change U g ∈ (A : Set B)
    rw [hA]
    exact Set.subset_centralizer_centralizer (mem_range_self _)
  have hVstar (g : G) : star (V g) = V g⁻¹ := Subtype.ext (hstar g)
  -- Some averaged vector is still moved by x, since the averages approximate each vector.
  obtain ⟨f, hf⟩ : ∃ f : Lp ℂ 1 μ,
      U x * averageOrbit μ U hU hc f ≠ averageOrbit μ U hU hc f := by
    by_contra! hall
    apply hx
    apply ContinuousLinearMap.ext
    intro v
    have heq : IsClosed {w : H | U x w = w} := isClosed_eq (U x).continuous continuous_id
    apply closure_minimal _ heq (averageOrbit_dense μ U hU hc v)
    rintro _ ⟨f, rfl⟩
    exact congrArg (fun T : B ↦ T v) (hall f)
  let a : A := ⟨averageOrbit μ U hU hc f, by
    change averageOrbit μ U hU hc f ∈ (A : Set B)
    rw [hA]
    intro T hT
    exact averageOrbit_commutes μ U hU hc f T (fun g ↦ hT (U g) (mem_range_self g))⟩
  have hne : V x * a ≠ a := fun h ↦ hf (congrArg Subtype.val h)
  obtain ⟨ω, hω⟩ : ∃ ω : characterSpace ℂ A, ω (V x * a) ≠ ω a := by
    by_contra! hall
    exact hne ((gelfandTransform_isometry A).injective (ContinuousMap.ext hall))
  have ha : ω a ≠ 0 := by
    intro h
    apply hω
    rw [map_mul, h, mul_zero]
  have hχ (g : G) : ‖ω (V g)‖ = 1 := by
    have heq : star (ω (V g)) * ω (V g) = 1 := by
      rw [← map_star, ← map_mul, hVstar, ← map_mul, inv_mul_cancel, map_one, map_one]
    have habs := congrArg norm heq
    rw [norm_mul, norm_star, norm_one, ← sq] at habs
    nlinarith [norm_nonneg (ω (V g))]
  have hcont : Continuous fun g ↦ ω (V g) := by
    have ht : Continuous fun g ↦ V g * a := by
      have ht : Continuous fun g ↦ U g * averageOrbit μ U hU hc f := by
        simp_rw [averageOrbit_translate]
        exact (averageOrbit μ U hU hc).continuous.comp
          (haarTranslation_continuous μ 1 ENNReal.one_ne_top f)
      exact ht.subtype_mk _
    refine (((CharacterSpace.toCLM ω).continuous.comp ht).div_const (ω a)).congr fun g ↦ ?_
    change ω (V g * a) / ω a = ω (V g)
    rw [map_mul, mul_div_cancel_right₀ _ ha]
  let χ : PontryaginDual G :=
    { toFun g := ⟨ω (V g), mem_sphere_zero_iff_norm.mpr (hχ g)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' g k := Circle.ext (by
        change ω (V (g * k)) = ω (V g) * ω (V k)
        rw [map_mul, map_mul])
      continuous_toFun := hcont.subtype_mk _ }
  refine ⟨χ, fun h ↦ hω ?_⟩
  have hh : ω (V x) = 1 := congrArg (fun z : Circle ↦ (z : ℂ)) h
  rw [map_mul, hh, one_mul]

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

end RiemannMasullo
