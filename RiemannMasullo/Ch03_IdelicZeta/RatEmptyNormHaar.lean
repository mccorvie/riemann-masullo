module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # The rational empty-finite-place norm marginal

The quotient Weil normalization gives exactly `dt/t` on the positive norm ray.
The calculation uses the positive real interval `[1,2]` upstairs and counts one
sign in each fiber, rather than substituting a probability Haar. -/

public noncomputable section
open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo
namespace RatEmptyNormHaar
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "A" => SAdeleRing ℚ S₀
local notation "G" => Aˣ
local notation "H" => sProjectedDiagonal ℚ S₀
local notation "J" => SIdeleQuotient ℚ S₀
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "μ" => sMultiplicativeTamagawaMeasure ℚ S₀
local notation "ν" => sLocalQuotientTamagawaMeasure ℚ S₀
local notation "η" => sLocalNormOneQuotientMeasure ℚ S₀
local notation "E" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
private local instance (v : InfinitePlace ℚ) : MeasurableSpace v.Completion := borel _
private local instance (v : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSpace (v.adicCompletion ℚ) := borel _
private local instance : MeasurableSpace (InfiniteAdeleRing ℚ) := inferInstanceAs (MeasurableSpace ((v : InfinitePlace ℚ) → v.Completion))
private local instance : MeasurableSpace A := inferInstanceAs (MeasurableSpace (InfiniteAdeleRing ℚ × ((v : S₀) → v.val.adicCompletion ℚ)))
private local instance : MeasurableSpace J := borel _
private local instance : MeasurableSpace (N).ker := borel _
private local instance : BorelSpace J := ⟨rfl⟩
private local instance : BorelSpace (N).ker := ⟨rfl⟩
private local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
private local instance : BorelSpace G := sIdeleGroup_borelSpace
private def coord : A →+* ℝ := (E).toRingHom.comp ((Pi.evalRingHom InfinitePlace.Completion Rat.infinitePlace).comp (RingHom.fst _ _))
private theorem coord_inj : Injective coord := by
  intro x y h
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  exact (E).injective h
private theorem coord_cont : Continuous coord :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp ((continuous_apply Rat.infinitePlace).comp continuous_fst)
private def band : Set ℝ≥0ˣ := {t | (t.val : ℝ) ∈ Icc 1 2}
private def strip : Set G := {g | coord g.val ∈ Icc 1 2}
private theorem band_meas : MeasurableSet band := (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
private theorem strip_meas : MeasurableSet strip := (coord_cont.comp Units.continuous_val).measurable measurableSet_Icc
private theorem abs_coord (g : G) : |coord g.val| = ((sIdeleNorm ℚ S₀ g).val : ℝ) := by
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  have h := e.isometry.norm_map_of_map_zero (map_zero E) (g.val.1 Rat.infinitePlace)
  change |e (g.val.1 Rat.infinitePlace)| = _
  rw [← Real.norm_eq_abs, h]
  symm
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

/-- The positive lift, unlike the full inverse image of the norm band, has mass log 2. -/
private theorem positive_strip_mass : μ strip = ENNReal.ofReal (Real.log 2) := by
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
  have Hm := sMultiplicativeTamagawaMeasure_integerUnits ℚ S₀ B hm
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one] at Hm
  refine (congrArg μ ?_).trans (Hm.trans (infiniteLocalMultiplicativeTamagawaMeasure_real_interval ℚ Rat.infinitePlace Rat.isReal_infinitePlace))
  ext g
  constructor
  · intro hg
    exact ⟨fun w ↦ by obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _; exact hg, fun v ↦ isEmptyElim v⟩
  · exact fun hg ↦ hg.1 Rat.infinitePlace

private theorem fiber (g : G) : (Measure.count : Measure H) {h | g * (h : G) ∈ strip} = band.indicator (fun _ ↦ (1 : ℝ≥0∞)) (sIdeleNorm ℚ S₀ g) := by
  classical
  let _ : T2Space G := (sIdeleGroup_description ℚ S₀).2.1
  have hn (k : H) : sIdeleNorm ℚ S₀ (g * k.val) = sIdeleNorm ℚ S₀ g := by
    have hk : (QuotientGroup.mk k.val : J) = 1 := (QuotientGroup.eq_one_iff _).mpr k.property
    rw [map_mul, ← sIdeleQuotientNorm_mk ℚ S₀ k.val, hk, map_one, mul_one]
  have he (k : H) : |coord (g * k.val).val| = |coord g.val| := by rw [abs_coord, abs_coord, hn]
  have hu {k l : H} (hk : g * k.val ∈ strip) (hl : g * l.val ∈ strip) : k = l := by
    change coord _ ∈ Icc 1 2 at hk hl
    apply Subtype.ext
    apply mul_left_cancel (a := g)
    apply Units.ext
    apply coord_inj
    exact (abs_of_pos (zero_lt_one.trans_le hk.1)).symm.trans (((he k).trans (he l).symm).trans (abs_of_pos (zero_lt_one.trans_le hl.1)))
  by_cases hb : sIdeleNorm ℚ S₀ g ∈ band
  · have ha : |coord g.val| ∈ Icc 1 2 := by rw [abs_coord]; exact hb
    have hex : ∃ k : H, g * k.val ∈ strip := by
      by_cases hs : 0 ≤ coord g.val
      · refine ⟨1, ?_⟩
        simpa [strip, abs_of_nonneg hs] using ha
      · have hm : (-1 : G) ∈ H := by
          apply (QuotientGroup.eq_one_iff _).mp
          apply (sIdeleQuotient_mk_eq_one ℚ S₀ _).mpr
          refine ⟨-1, Units.ext ?_⟩
          simp
        refine ⟨⟨-1, hm⟩, ?_⟩
        change coord (g.val * (-1)) ∈ Icc 1 2
        simpa [abs_of_neg (lt_of_not_ge hs)] using ha
    obtain ⟨k, hk⟩ := hex
    have hs : {l : H | g * l.val ∈ strip} = {k} := by ext l; exact ⟨fun hl ↦ hu hl hk, fun e ↦ e ▸ hk⟩
    rw [hs, Measure.count_singleton, indicator_of_mem hb]
  · have hs : {l : H | g * l.val ∈ strip} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      apply hb
      change coord _ ∈ Icc 1 2 at hk
      change ((sIdeleNorm ℚ S₀ g).val : ℝ) ∈ Icc 1 2
      rwa [← hn k, ← abs_coord, abs_of_pos (zero_lt_one.trans_le hk.1)]
    rw [hs, measure_empty, indicator_of_notMem hb]

/-- Counting Weil assigns the quotient norm band the mass of its positive lift. -/
private theorem quotient_band_mass : ν (N ⁻¹' band) = ENNReal.ofReal (Real.log 2) := by
  let _ : T2Space G := (sIdeleGroup_description ℚ S₀).2.1
  let _ : LocallyCompactSpace G := (sIdeleGroup_description ℚ S₀).2.2.1
  let _ (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let _ (v : S₀) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let _ : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology (((w : InfinitePlace ℚ) → w.Completion) × ((v : S₀) → v.val.adicCompletion ℚ)))
  let _ : SecondCountableTopology G := (sIdeleGroup_description ℚ S₀).1.secondCountableTopology
  let _ := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := ℚ) (S := S₀)
  let _ := sMultiplicativeTamagawaMeasure_regular (F := ℚ) (S := S₀)
  let _ : DiscreteTopology H := discreteTopology_sProjectedDiagonal
  let _ : (Measure.count : Measure H).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let _ : (Measure.count : Measure H).Regular := count_regular_of_discreteTopology
  obtain ⟨hκ, hμ⟩ := weilMeasure_eq_bind H isClosed_sProjectedDiagonal μ Measure.count ν (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := S₀))
  refine Eq.trans ?_ positive_strip_mass
  rw [← hμ, Measure.bind_apply strip_meas hκ.aemeasurable, ← lintegral_indicator_one ((isProperMap_sIdeleQuotientNorm ℚ S₀).continuous.measurable band_meas)]
  apply lintegral_congr
  intro q
  have ht : Measurable (fun h : H ↦ q.out * (h : G)) := (continuous_const.mul continuous_subtype_val).measurable
  rw [Measure.map_apply ht strip_meas]
  change _ = Measure.count {h : H | q.out * h.val ∈ strip}
  rw [fiber]
  have hn : N q = sIdeleNorm ℚ S₀ q.out := (congrArg N (QuotientGroup.out_eq' q)).symm.trans (sIdeleQuotientNorm_mk ℚ S₀ _)
  by_cases hb : N q ∈ band
  · have hb' : sIdeleNorm ℚ S₀ q.out ∈ band := hn ▸ hb
    rw [indicator_of_mem (show q ∈ N ⁻¹' band from hb), indicator_of_mem hb']
    rfl
  · have hb' : sIdeleNorm ℚ S₀ q.out ∉ band := hn ▸ hb
    rw [indicator_of_notMem (show q ∉ N ⁻¹' band from hb), indicator_of_notMem hb']

/-- The norm marginal records precisely the total mass of the norm-one factor. -/
private theorem norm_map_factor : (ν).map N = η univ • positiveRealHaar := by
  let _ (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let _ (v : S₀) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let _ : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology (((w : InfinitePlace ℚ) → w.Completion) × ((v : S₀) → v.val.adicCompletion ℚ)))
  let _ : SecondCountableTopology G := (sIdeleGroup_description ℚ S₀).1.secondCountableTopology
  let _ : SecondCountableTopology J := inferInstance
  let p := Units.map (adeleProjection ℚ S₀).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S₀ ↦ (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* G := ⟨p.comp (canonicalIdeleNormSection ℚ), hp.comp (canonicalIdeleNormSection_continuous ℚ)⟩
  have hτ : RightInverse τ (sIdeleNorm ℚ S₀) := sIdeleNorm_project_canonicalSection ℚ S₀
  let f (x : (N).ker × ℝ≥0ˣ) : J := (x.1 : J) * QuotientGroup.mk (τ x.2)
  have hf₁ : Measurable (fun k : (N).ker ↦ (k : J)) := continuous_subtype_val.measurable
  have hf₂ : Measurable (fun t ↦ (QuotientGroup.mk (τ t) : J)) :=
    (QuotientGroup.continuous_mk.comp τ.continuous).measurable
  have hf : Measurable f := (hf₁.comp measurable_fst).mul (hf₂.comp measurable_snd)
  have hm : Measurable N := (isProperMap_sIdeleQuotientNorm ℚ S₀).continuous.measurable
  have hcomp : N ∘ f = Prod.snd := by
    funext x
    change N ((x.1 : J) * QuotientGroup.mk (τ x.2)) = x.2
    rw [map_mul, MonoidHom.mem_ker.mp x.1.property, one_mul, sIdeleQuotientNorm_mk, hτ]
  let _ : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let _ : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure_of_lebesgue
  have hprod : ((η).prod positiveRealHaar).map f = ν := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := S₀)).2 τ hτ
  rw [← hprod, Measure.map_map hm hf, hcomp, Measure.map_snd_prod]

/-- The quotient measure, not a freely chosen probability Haar, fixes the kernel mass. -/
theorem norm_one_mass : η univ = 1 := by
  have hb : positiveRealHaar band = ENNReal.ofReal (Real.log 2) := positiveRealHaar_interval (Units.mk0 (2 : ℝ≥0) two_ne_zero) (by norm_num)
  have hm : Measurable N := (isProperMap_sIdeleQuotientNorm ℚ S₀).continuous.measurable
  have h := congrArg (fun ρ : Measure ℝ≥0ˣ ↦ ρ band) norm_map_factor
  change (ν).map N band = (η univ • positiveRealHaar) band at h
  rw [Measure.map_apply hm band_meas, quotient_band_mass, smul_apply, smul_eq_mul, hb] at h
  apply (ENNReal.mul_left_inj (ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num : (1:ℝ) < 2))).ne' ENNReal.ofReal_ne_top).mp
  simpa using h.symm

/-- Under the rational empty-level norm the actual Weil quotient measure is `dt/t`. -/
theorem map_norm : (@Measure.map J ℝ≥0ˣ (borel J) inferInstance N ν) = positiveRealHaar := by
  rw [norm_map_factor, norm_one_mass, one_smul]
end RatEmptyNormHaar
end RiemannMasullo
