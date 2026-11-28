module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch03_IdelicZeta.Sec1_RatSLocalUnitRepresentative
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # The genuine rational finite-box quotient norm has Haar measure `dr/r`

Count the unique normalized representative on the strip of norms `[1,2]`
in the Weil formula. Its finite coordinates are integer units. The rational
local different factors are all one, so the compact norm-one factor has mass
one with the actual Tamagawa normalization. -/

public noncomputable section
open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo
namespace RatFiniteHaarFromUnitSection
variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "A" => SAdeleRing ℚ S
local notation "G" => Aˣ
local notation "H" => sProjectedDiagonal ℚ S
local notation "J" => SIdeleQuotient ℚ S
local notation "N" => sIdeleQuotientNorm ℚ S
local notation "μ" => sMultiplicativeTamagawaMeasure ℚ S
local notation "ν" => sLocalQuotientTamagawaMeasure ℚ S
local notation "η" => sLocalNormOneQuotientMeasure ℚ S
local notation "E" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
private local instance (v : InfinitePlace ℚ) : MeasurableSpace v.Completion := borel _
private local instance (v : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSpace (v.adicCompletion ℚ) := borel _
private local instance : MeasurableSpace (InfiniteAdeleRing ℚ) := inferInstanceAs (MeasurableSpace ((v : InfinitePlace ℚ) → v.Completion))
private local instance : MeasurableSpace A := inferInstanceAs (MeasurableSpace (InfiniteAdeleRing ℚ × ((v : S) → v.val.adicCompletion ℚ)))
private local instance : MeasurableSpace J := borel _
private local instance : MeasurableSpace (N).ker := borel _
private local instance : BorelSpace J := ⟨rfl⟩
private local instance : BorelSpace (N).ker := ⟨rfl⟩
private local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
private local instance : BorelSpace G := sIdeleGroup_borelSpace
private def coord : A →+* ℝ := (E).toRingHom.comp ((Pi.evalRingHom InfinitePlace.Completion Rat.infinitePlace).comp (RingHom.fst _ _))
private theorem coord_cont : Continuous (coord S) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp ((continuous_apply Rat.infinitePlace).comp continuous_fst)
private def band : Set ℝ≥0ˣ := {t | (t.val : ℝ) ∈ Icc 1 2}
private def finiteCoord (v : S) : G →* (v.val.adicCompletion ℚ)ˣ :=
  Units.map ((Pi.evalRingHom (fun u : S ↦ u.val.adicCompletion ℚ) v).comp
    (RingHom.snd _ _)).toMonoidHom

private def unitStrip : Set G := {g | coord S g.val ∈ Icc 1 2 ∧
  ∀ v : S, finiteCoord S v g ∈ (v.val.adicCompletionIntegers ℚ).units}

/-- In the norm band there is exactly one positive unit-strip lift, and outside it none. -/
private def ExactUnitSection : Prop := ∀ g : G,
  (sIdeleNorm ℚ S g ∈ band → ∃! h : H, g * h.val ∈ unitStrip S) ∧
  (sIdeleNorm ℚ S g ∉ band → ∀ h : H, g * h.val ∉ unitStrip S)

private theorem band_meas : MeasurableSet band := (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
set_option maxHeartbeats 800000 in
private theorem strip_meas : MeasurableSet (unitStrip S) := by
  rw [show unitStrip S = (fun g : G ↦ coord S g.val) ⁻¹' Icc 1 2 ∩
      (⋂ v : S, (finiteCoord S v) ⁻¹' (v.val.adicCompletionIntegers ℚ).units) by
    ext g
    simp only [unitStrip, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter, SetLike.mem_coe]]
  apply MeasurableSet.inter ((coord_cont S |>.comp Units.continuous_val).measurable measurableSet_Icc)
  apply MeasurableSet.iInter
  intro v
  have ho : IsOpen ((v.val.adicCompletionIntegers ℚ).units : Set (v.val.adicCompletion ℚ)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  exact (ho.preimage (((continuous_apply v).comp continuous_snd).units_map _)).measurableSet

/-- Local different factor in the integer-unit Tamagawa mass. -/
private def differentMass (v : HeightOneSpectrum (𝓞 ℚ)) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
    multiplicity v.asIdeal (differentIdeal ℤ (𝓞 ℚ)))))⁻¹

private theorem positive_strip_mass : μ (unitStrip S) = (∏ v : S, differentMass v.val) * ENNReal.ofReal (Real.log 2) := by
  classical
  let _ : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let h (w : InfinitePlace ℚ) : w.IsReal := by
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    exact Rat.isReal_infinitePlace
  let B (w : InfinitePlace ℚ) := {x : w.Completionˣ | InfinitePlace.Completion.ringEquivRealOfIsReal (h w) x.val ∈ Icc 1 2}
  have hm (w : InfinitePlace ℚ) : MeasurableSet (B w) := by
    let _ : BorelSpace w.Completion := ⟨rfl⟩
    let _ : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal (h w)).continuous.comp Units.continuous_val).measurable measurableSet_Icc
  have Hm := sMultiplicativeTamagawaMeasure_integerUnits ℚ S B hm
  rw [Fintype.prod_unique] at Hm
  refine (congrArg μ ?_).trans (Hm.trans ?_)
  · ext g
    constructor
    · intro hg
      refine ⟨?_, hg.2⟩
      intro w
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      exact hg.1
    · exact fun hg ↦ ⟨hg.1 Rat.infinitePlace, hg.2⟩
  · change infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace (B Rat.infinitePlace) *
        (∏ v : S, differentMass v.val) = _
    have hB : infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace (B Rat.infinitePlace) =
        ENNReal.ofReal (Real.log 2) :=
      infiniteLocalMultiplicativeTamagawaMeasure_real_interval ℚ Rat.infinitePlace Rat.isReal_infinitePlace
    rw [hB, mul_comm]

private theorem fiber (hsec : ExactUnitSection S) (g : G) :
    (Measure.count : Measure H) {h | g * h.val ∈ unitStrip S} =
      band.indicator (fun _ ↦ (1 : ℝ≥0∞)) (sIdeleNorm ℚ S g) := by
  classical
  let _ : T2Space G := (sIdeleGroup_description ℚ S).2.1
  by_cases hb : sIdeleNorm ℚ S g ∈ band
  · obtain ⟨k, hk, hu⟩ := (hsec g).1 hb
    have hs : {l : H | g * l.val ∈ unitStrip S} = {k} := by
      ext l; exact ⟨hu l, fun e ↦ e ▸ hk⟩
    rw [hs, Measure.count_singleton, indicator_of_mem hb]
  · have hs : {h : H | g * h.val ∈ unitStrip S} = ∅ := eq_empty_iff_forall_notMem.mpr ((hsec g).2 hb)
    rw [hs, measure_empty, indicator_of_notMem hb]

/-- Counting Weil assigns the quotient norm band the mass of its positive lift. -/
private theorem quotient_band_mass (hsec : ExactUnitSection S) : ν (N ⁻¹' band) = (∏ v : S, differentMass v.val) * ENNReal.ofReal (Real.log 2) := by
  let _ : T2Space G := (sIdeleGroup_description ℚ S).2.1
  let _ : LocallyCompactSpace G := (sIdeleGroup_description ℚ S).2.2.1
  let _ (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let _ (v : S) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let _ : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let _ : SecondCountableTopology G := (sIdeleGroup_description ℚ S).1.secondCountableTopology
  let _ := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := ℚ) (S := S)
  let _ := sMultiplicativeTamagawaMeasure_regular (F := ℚ) (S := S)
  let _ : DiscreteTopology H := discreteTopology_sProjectedDiagonal
  let _ : (Measure.count : Measure H).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let _ : (Measure.count : Measure H).Regular := count_regular_of_discreteTopology
  obtain ⟨hκ, hμ⟩ := weilMeasure_eq_bind H isClosed_sProjectedDiagonal μ Measure.count ν (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := S))
  refine Eq.trans ?_ (positive_strip_mass S)
  rw [← hμ, Measure.bind_apply (strip_meas S) hκ.aemeasurable, ← lintegral_indicator_one ((isProperMap_sIdeleQuotientNorm ℚ S).continuous.measurable band_meas)]
  apply lintegral_congr
  intro q
  have ht : Measurable (fun h : H ↦ q.out * (h : G)) := (continuous_const.mul continuous_subtype_val).measurable
  rw [Measure.map_apply ht (strip_meas S)]
  change _ = Measure.count {h : H | q.out * h.val ∈ unitStrip S}
  rw [fiber S hsec]
  have hn : N q = sIdeleNorm ℚ S q.out := (congrArg N (QuotientGroup.out_eq' q)).symm.trans (sIdeleQuotientNorm_mk ℚ S _)
  by_cases hb : N q ∈ band
  · have hb' : sIdeleNorm ℚ S q.out ∈ band := hn ▸ hb
    rw [indicator_of_mem (show q ∈ N ⁻¹' band from hb), indicator_of_mem hb']
    rfl
  · have hb' : sIdeleNorm ℚ S q.out ∉ band := hn ▸ hb
    rw [indicator_of_notMem (show q ∉ N ⁻¹' band from hb), indicator_of_notMem hb']

/-- The norm marginal records precisely the total mass of the norm-one factor. -/
private theorem norm_map_factor : (ν).map N = η univ • positiveRealHaar := by
  let _ (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let _ (v : S) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let _ : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let _ : SecondCountableTopology G := (sIdeleGroup_description ℚ S).1.secondCountableTopology
  let _ : SecondCountableTopology J := inferInstance
  let p := Units.map (adeleProjection ℚ S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦ (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* G := ⟨p.comp (canonicalIdeleNormSection ℚ), hp.comp (canonicalIdeleNormSection_continuous ℚ)⟩
  have hτ : RightInverse τ (sIdeleNorm ℚ S) := sIdeleNorm_project_canonicalSection ℚ S
  let f (x : (N).ker × ℝ≥0ˣ) : J := (x.1 : J) * QuotientGroup.mk (τ x.2)
  have hf₁ : Measurable (fun k : (N).ker ↦ (k : J)) := continuous_subtype_val.measurable
  have hf₂ : Measurable (fun t ↦ (QuotientGroup.mk (τ t) : J)) :=
    (QuotientGroup.continuous_mk.comp τ.continuous).measurable
  have hf : Measurable f := (hf₁.comp measurable_fst).mul (hf₂.comp measurable_snd)
  have hm : Measurable N := (isProperMap_sIdeleQuotientNorm ℚ S).continuous.measurable
  have hcomp : N ∘ f = Prod.snd := by
    funext x
    change N ((x.1 : J) * QuotientGroup.mk (τ x.2)) = x.2
    rw [map_mul, MonoidHom.mem_ker.mp x.1.property, one_mul, sIdeleQuotientNorm_mk, hτ]
  let _ : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let _ : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure_of_lebesgue
  have hprod : ((η).prod positiveRealHaar).map f = ν := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := S)).2 τ hτ
  rw [← hprod, Measure.map_map hm hf, hcomp, Measure.map_snd_prod]

/-- The quotient measure, not a freely chosen probability Haar, fixes the kernel mass. -/
private theorem norm_one_mass (hsec : ExactUnitSection S) : η univ = ∏ v : S, differentMass v.val := by
  have hb : positiveRealHaar band = ENNReal.ofReal (Real.log 2) := positiveRealHaar_interval (Units.mk0 (2 : ℝ≥0) two_ne_zero) (by norm_num)
  have hm : Measurable N := (isProperMap_sIdeleQuotientNorm ℚ S).continuous.measurable
  have h := congrArg (fun ρ : Measure ℝ≥0ˣ ↦ ρ band) (norm_map_factor S)
  change (ν).map N band = (η univ • positiveRealHaar) band at h
  rw [Measure.map_apply hm band_meas, quotient_band_mass S hsec, smul_apply, smul_eq_mul, hb] at h
  apply (ENNReal.mul_left_inj (ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num : (1:ℝ) < 2))).ne' ENNReal.ofReal_ne_top).mp
  simpa using h.symm

private theorem mem_strip_iff (g : G) :
    g ∈ unitStrip S ↔ RatFinitePositiveUnitRep.Normalized S g ∧ sIdeleNorm ℚ S g ∈ band := by
  have hval (v : S) : finiteCoord S v g ∈ (v.val.adicCompletionIntegers ℚ).units ↔
      Valued.v (g.val.2 v) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
  have hc : coord S g.val = RatFinitePositiveUnitRep.realCoord S g := rfl
  constructor
  · intro h
    have hn : RatFinitePositiveUnitRep.Normalized S g :=
      ⟨zero_lt_one.trans_le (hc ▸ h.1.1), fun v ↦ (hval v).mp (h.2 v)⟩
    refine ⟨hn, ?_⟩
    change ((sIdeleNorm ℚ S g).val : ℝ) ∈ Icc 1 2
    rw [RatFinitePositiveUnitRep.norm_normalized S hn, ← hc]
    exact h.1
  · rintro ⟨hn, hb⟩
    refine ⟨?_, fun v ↦ (hval v).mpr (hn.2 v)⟩
    rw [hc, ← RatFinitePositiveUnitRep.norm_normalized S hn]
    exact hb

private theorem exactUnitSection : ExactUnitSection S := by
  intro g
  have hn (h : H) : sIdeleNorm ℚ S (g * h.val) = sIdeleNorm ℚ S g := by
    have hq : (QuotientGroup.mk (g * h.val) : J) = QuotientGroup.mk g := by
      change ((QuotientGroup.mk' H) (g * h.val) : J) = (QuotientGroup.mk' H) g
      have hh : (QuotientGroup.mk' H) h.val = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
      rw [map_mul, hh]
      exact mul_one ((QuotientGroup.mk' H) g)
    exact (congrArg N hq)
  have Hstrip (h : H) :
      g * h.val ∈ unitStrip S ↔
        RatFinitePositiveUnitRep.Normalized S (h.val * g) ∧ sIdeleNorm ℚ S g ∈ band := by
    rw [mem_strip_iff S, hn, mul_comm g h.val]
  constructor
  · intro hg
    obtain ⟨h, hh, hu⟩ := RatFinitePositiveUnitRep.existsUnique_compensation S g
    exact ⟨h, (Hstrip h).mpr ⟨hh, hg⟩, fun d hd ↦ hu d ((Hstrip d).mp hd).1⟩
  · intro hg h hh
    exact hg ((Hstrip h).mp hh).2

/-- The local different factor in both rational finite Tamagawa measures. -/
theorem ratFiniteDifferentMass_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 ℚ)))))⁻¹ = 1 := by
  classical
  have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
    rw [Ideal.one_eq_top, ← Ideal.absNorm_eq_one_iff,
      NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ), NumberField.discr_rat]
    rfl
  rw [hd, multiplicity_one_right]
  simp

/-- The genuine norm-one quotient has Tamagawa mass one for every finite rational box. -/
theorem rat_norm_one_mass : η univ = 1 := by
  rw [norm_one_mass S (exactUnitSection S)]
  exact Finset.prod_eq_one fun v _ ↦ ratFiniteDifferentMass_eq_one v.val

/-- The actual finite-S rational quotient norm sends counting-Weil Haar to `dr/r`. -/
theorem rat_map_norm : (@Measure.map J ℝ≥0ˣ (borel J) inferInstance N ν) =
    positiveRealHaar := by
  rw [norm_map_factor S, rat_norm_one_mass S, one_smul]
end RatFiniteHaarFromUnitSection
end RiemannMasullo
