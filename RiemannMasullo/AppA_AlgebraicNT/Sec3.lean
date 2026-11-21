module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Topology.Algebra.Group.Units

import all RiemannMasullo.AppA_AlgebraicNT.Sec2  -- for the diagonal adelic basis
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import RiemannMasullo.ForMathlib.Analysis.Fourier.LpSpace
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Extension
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.RingTheory.Trace.Defs
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real

/-! # Haar measures

Masullo, §A.3, pp. 555–562.
-/

@[expose] public noncomputable section

set_option maxSynthPendingDepth 8

namespace RiemannMasullo

open Function MeasureTheory NumberField IsDedekindDomain InfinitePlace.Completion Set
open scoped Classical ENNReal NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "P[" F "]" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "A[" F "]" => AddSubgroup.toSubgroup (AdeleRing.principalSubgroup (𝓞 F) F)
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)

local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((v : InfinitePlace F) → v.Completion))
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
  locallyCompactSpace_adicCompletion v
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
local instance : MeasurableSpace 𝔸[F] := borel _
local instance : MeasurableSpace (Multiplicative 𝔸[F] ⧸ A[F]) := borel _
local instance : MeasurableSpace 𝕀[F] := borel _
local instance : MeasurableSpace C[F] := borel _
local instance : MeasurableSpace (C[F] ⧸ C₁[F]) := borel _
local instance : MeasurableSpace (𝕀[F] ⧸ N[F]) := borel _

variable (S : Finset (Primes(F)))

local notation "dₛ" => RingHom.comp (adeleProjection F S)
  (RingHom.comp (Subring.subtype (integralAdelesOutside F S)) (integralAdeleDiagonal F S))
local notation "Aₛ" => AddSubgroup.toSubgroup (AddMonoidHom.range (RingHom.toAddMonoidHom dₛ))
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)

local instance : MeasurableSpace (SAdeleRing F S) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
local instance : MeasurableSpace (Multiplicative (SAdeleRing F S) ⧸ Aₛ) := borel _
local instance : MeasurableSpace (𝕀ₛ ⧸ Nₛ) := borel _

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition A.3.1.1, p. 555. Exactly one regular additive Haar measure on
the adeles gives the additive quotient mass one when the diagonal has counting measure. -/
theorem additiveTamagawaMeasure_existsUnique :
    ∃! μ : Measure 𝔸[F], μ.IsAddHaarMeasure ∧ μ.Regular ∧
      ∃ ν : Measure (Multiplicative 𝔸[F] ⧸ A[F]),
        IsWeilQuotientMeasure A[F] (show Measure (Multiplicative 𝔸[F]) from μ)
          Measure.count ν ∧ ν univ = 1 := by
  classical
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let Q := G ⧸ H
  obtain ⟨-, hclosed, hdiscrete, -, -, hcompact, -, -⟩ := adele_additive_quotient.{_, 0} F
  let : CompactSpace Q := hcompact
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace 𝔸ᶠ[𝓞 F, F] := by
    change LocallyCompactSpace (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F])
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : IsClosed (H : Set G) := hclosed
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace Q := ⟨rfl⟩
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hclosed
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure := inferInstanceAs (Measure.count : Measure H).IsHaarMeasure
  -- Normalize Haar measure on the compact quotient using the whole space.
  let K : TopologicalSpace.PositiveCompacts Q := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν : Measure Q := Measure.haarMeasure K
  have hν : ν univ = 1 := Measure.haarMeasure_self (K₀ := K)
  let μ := ses.inducedMeasure count ν
  let : μ.Regular := ses.inducedMeasure_regular count ν
  have hμ : ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H count f q ∂ν := by
    intro f hf
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    have hfiber (q : Q) : ses.pushforward count fc q = lcaCosetIntegral H count f q := by
      calc
        ses.pushforward count fc q =
            ses.pushforward count fc (QuotientGroup.mk' H q.out) :=
          congrArg (ses.pushforward count fc) (QuotientGroup.out_eq' q).symm
        _ = lcaCosetIntegral H count f q := ses.pushforward_apply_apply count fc q.out
    -- The induced measure formula for real functions applies to both complex coordinates.
    have hcoord (L : ℂ →L[ℝ] ℝ) :
        L (∫ x, f x ∂μ) = L (∫ q, ses.pushforward count fc q ∂ν) := by
      let g : CompactlySupportedContinuousMap G ℝ :=
        ⟨⟨fun x ↦ L (f x), L.continuous.comp f.continuous⟩, hf.comp_left L.map_zero⟩
      change L (∫ x, fc x ∂μ) = _
      rw [← L.integral_comp_comm (fc.integrable (μ := μ)),
        ← L.integral_comp_comm ((ses.pushforward count fc).integrable (μ := ν))]
      change (∫ x, g x ∂μ) = ∫ q, L (ses.pushforward count fc q) ∂ν
      rw [ses.integral_inducedMeasure, ses.integrate_apply]
      congr with q
      obtain ⟨x, rfl⟩ := ses.isOpenQuotientMap.surjective q
      rw [ses.pushforward_apply_apply, ses.pushforward_apply_apply,
        ← L.integral_comp_comm (ses.pullback fc x).integrable]
      rfl
    simp_rw [← hfiber]
    exact Complex.ext (hcoord Complex.reCLM) (hcoord Complex.imCLM)
  refine ⟨μ, ⟨?_, ses.inducedMeasure_regular count ν, ν, ⟨inferInstance, inferInstance, hμ⟩, hν⟩,
    ?_⟩
  · have hhaar := ses.isHaarMeasure_inducedMeasure count ν
    exact
      { toIsFiniteMeasureOnCompacts := hhaar.toIsFiniteMeasureOnCompacts
        toIsOpenPosMeasure := hhaar.toIsOpenPosMeasure
        map_add_left_eq_self := fun x ↦ hhaar.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  rintro μ' ⟨-, hregular, ν', ⟨hhaar', hregular', hweil⟩, hν'⟩
  let : (show Measure G from μ').Regular := hregular
  let : ν'.IsHaarMeasure := hhaar'
  let : ν'.Regular := hregular'
  have heq : ν' = ν := by
    have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
    have hmass := congrArg (fun m : Measure Q ↦ m univ) hscale
    change ν' univ = (ν'.haarScalarFactor ν : ℝ≥0∞) * ν univ at hmass
    have hfactor : ν'.haarScalarFactor ν = 1 := by
      rw [hν', hν, mul_one] at hmass
      exact ENNReal.coe_inj.mp hmass.symm
    rw [hscale, hfactor, one_smul]
  subst ν'
  apply Measure.ext_of_integral_eq_on_compactlySupported (X := G)
  intro f
  let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have heq := (hweil fc hc).trans (hμ fc hc).symm
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ x : G, f x ∂(show Measure G from μ')) =
        ∫ x : G, (f x : ℂ) ∂(show Measure G from μ') := integral_complex_ofReal.symm
    _ = ∫ x : G, (f x : ℂ) ∂μ := heq
    _ = Complex.ofReal (∫ x : G, f x ∂μ) := integral_complex_ofReal

/-- Paper: Definition A.3.1.1, p. 555. The additive Tamagawa measure is the
adelic Haar measure normalized to give the quotient by the diagonal mass one. -/
def additiveTamagawaMeasure : Measure 𝔸[F] :=
  (additiveTamagawaMeasure_existsUnique F).exists.choose

/-- Paper: Definition A.3.1.1, p. 555. The adelic measure has a Weil quotient
of mass one with counting measure on the diagonal. -/
theorem additiveTamagawaMeasure_quotientVolume :
    ∃ ν : Measure (Multiplicative 𝔸[F] ⧸ A[F]),
      IsWeilQuotientMeasure A[F] (show Measure (Multiplicative 𝔸[F]) from
        additiveTamagawaMeasure F) Measure.count ν ∧ ν univ = 1 :=
  (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists).2.2

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance instMeasurableSpaceWeilQuotientForFundamentalDomain (H : Subgroup G) :
    MeasurableSpace (G ⧸ H) := borel _

/-- For a closed discrete subgroup with counting measure, the mass of a precompact
fundamental domain meeting every coset is the mass of the Weil quotient measure. -/
private theorem weilQuotientMeasure_univ_eq_measure_fundamentalDomain
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {H : Subgroup G} [Countable H] [DiscreteTopology H] (hH : IsClosed (H : Set G))
    {μ : Measure G} [μ.IsHaarMeasure] {ν : Measure (G ⧸ H)}
    (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    (hνfinite : ν univ ≠ ⊤)
    {D : Set G} (hD : IsFundamentalDomain H.op D μ) (hcompact : IsCompact (closure D))
    (hcover : ∀ a : G, ∃ h : H.op, h • a ∈ D) :
    ν univ = μ D := by
  let π := QuotientGroup.mk' H
  let νD := (μ.restrict D).map π
  let : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hπ : Continuous π := QuotientGroup.continuous_mk
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hsum (f : CompactlySupportedContinuousMap G ℝ) :
      QuotientGroup.automorphize (Γ := H) f = ses.pushforward count f := by
    funext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    rw [ses.pushforward_apply_apply, integral_countable (ses.pullback f x).integrable]
    simp only [count, count_real_singleton, one_smul]
    change (∑' h : H.op, f (x * (h.val.unop : G))) = ∑' h : H, f (x * (h : G))
    exact (H.equivOp.tsum_eq (fun h : H.op ↦ f (x * h.val.unop))).symm
  -- A compactly supported function equal to one on the domain has positive periodization.
  obtain ⟨f, hf, -, hfc, hf₀⟩ :=
    exists_continuous_one_zero_of_isCompact hcompact isClosed_empty (disjoint_empty _)
  let f₀ : CompactlySupportedContinuousMap G ℝ := ⟨f, hfc⟩
  let c := ses.pushforward count f₀
  have hc (q : G ⧸ H) : 0 < c q := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨h, hd⟩ := hcover a
    let d : G := h • a
    have hdq : π d = π a := QuotientGroup.mk_mul_of_mem a (H.equivOp.symm h).property
    change 0 < ses.pushforward count f₀ (π a)
    rw [← hdq, ses.pushforward_apply_apply]
    apply (integral_pos_iff_support_of_nonneg (fun _ ↦ (hf₀ _).1)
      (ses.pullback f₀ d).integrable).mpr
    apply pos_iff_ne_zero.mpr ∘ Measure.count_ne_zero
    exact ⟨1, by simpa only [Function.mem_support, ses.pullback_def, Subgroup.coe_subtype,
      Subgroup.coe_one, mul_one] using
        (show f d ≠ 0 from (hf (subset_closure hd)).trans_ne one_ne_zero)⟩
  -- Divide by the periodization so both quotient integrals test the constant one.
  let g : CompactlySupportedContinuousMap G ℝ :=
    ⟨⟨fun x ↦ (c (π x))⁻¹ • f₀ x,
      ((c.continuous.comp hπ).inv₀ fun x ↦ (hc (π x)).ne').smul f₀.continuous⟩,
      by
        change HasCompactSupport ((fun x : G ↦ (c (π x))⁻¹) • ⇑f₀)
        exact f₀.hasCompactSupport.smul_left⟩
  have hg : QuotientGroup.automorphize (Γ := H) g = fun _ ↦ 1 := by
    calc
      _ = (fun q ↦ (c q)⁻¹) • QuotientGroup.automorphize (Γ := H) f₀ :=
        QuotientGroup.automorphize_smul_left (⇑f₀) (fun q ↦ (c q)⁻¹)
      _ = _ := by
        rw [hsum f₀]
        funext q
        exact inv_mul_cancel₀ (hc q).ne'
  let fc : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩,
      g.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  have hcoset (q : G ⧸ H) :
      lcaCosetIntegral H count fc q = (ses.pushforward count g q : ℂ) := by
    have hp := ses.pushforward_apply_apply count g q.out
    have hq : π q.out = q := QuotientGroup.out_eq' q
    change ses.pushforward count g (π q.out) = _ at hp
    rw [hq] at hp
    rw [hp, lcaCosetIntegral]
    exact integral_complex_ofReal
  have hweil : (∫ x, g x ∂μ) = ∫ _q : G ⧸ H, (1 : ℝ) ∂ν := by
    have h := hν.2.2 fc.toContinuousMap fc.hasCompactSupport
    change (∫ x, (g x : ℂ) ∂μ) = ∫ q, lcaCosetIntegral H count fc q ∂ν at h
    simp_rw [hcoset, ← hsum g, hg, integral_complex_ofReal] at h
    exact Complex.ofReal_injective h
  have hmeas : AEStronglyMeasurable (QuotientGroup.automorphize (Γ := H) g) νD :=
    hg ▸ aestronglyMeasurable_const
  have hunfold := QuotientGroup.integral_eq_integral_automorphize hD g.integrable hmeas
  rw [hg] at hunfold
  have hmass : νD univ = μ D := by
    rw [Measure.map_apply hπ.measurable MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have heq := hweil.symm.trans hunfold
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def] at heq
  change (ν univ).toReal = (νD univ).toReal at heq
  rw [hmass] at heq
  exact (ENNReal.toReal_eq_toReal_iff' hνfinite
    ((measure_mono subset_closure).trans_lt hcompact.measure_lt_top).ne).mp heq

end

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition A.3.1.1, p. 555. The additive Tamagawa measure of the
chosen adelic fundamental domain equals the mass of the additive quotient, namely one. -/
theorem additiveTamagawaMeasure_fundamentalDomain :
    additiveTamagawaMeasure F (adeleFundamentalDomain F (RingOfIntegers.basis F)) = 1 := by
  classical
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let μ : Measure G := additiveTamagawaMeasure F
  let b := RingOfIntegers.basis F
  let D : Set G := adeleFundamentalDomain F b
  obtain ⟨-, hclosed, hdiscrete, -⟩ := adele_additive_quotient.{_, 0} F
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable H := (Set.countable_range (algebraMap F 𝔸[F])).to_subtype
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hμ := (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists)
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  have hmeas : MeasurableSet D := by
    have hinf : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
      change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
      simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
        (continuous_apply v.1)).prodMk
        (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
          (continuous_apply v.1))
    have hIntegral : IsOpen (integralAdelesOutside F ∅ : Set 𝔸[F]) := by
      simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred, Finset.notMem_empty,
        not_false_eq_true, true_implies]
      exact (RestrictedProduct.isOpen_forall_mem (fun v : Primes(F) ↦
        Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd
    let : BorelSpace 𝔸[F] := ⟨rfl⟩
    have hfst : Continuous (Prod.fst : 𝔸[F] → InfiniteAdeleRing F) := continuous_fst
    have hm : Measurable (fun a : 𝔸[F] ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) :=
      Continuous.measurable (α := 𝔸[F]) (hinf.comp hfst)
    have hInt : MeasurableSet (integralAdelesOutside F ∅ : Set 𝔸[F]) := hIntegral.measurableSet
    exact ((ZSpan.fundamentalDomain_measurableSet _).preimage hm).inter hInt
  have hcover (a : G) : ∃ h : H.op, h • a ∈ D := by
    have ha : a.toAdd ∈ ⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b :=
      (adeleFundamentalDomain_cover F b).symm ▸ mem_univ _
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp ha
    obtain ⟨d, hd, hda⟩ := Set.mem_vadd_set.mp hx
    let h : H := ⟨Multiplicative.ofAdd (algebraMap F 𝔸[F] x), ⟨x, rfl⟩⟩
    refine ⟨H.equivOp h⁻¹, ?_⟩
    change a * (h : G)⁻¹ ∈ D
    have ha : Multiplicative.ofAdd d * (h : G) = a := (add_comm _ _).trans hda
    rwa [← ha, mul_inv_cancel_right]
  have hD : IsFundamentalDomain H.op D μ := by
    refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet (Filter.Eventually.of_forall hcover) ?_
      (fun h ↦ (measurePreserving_smul h μ).quasiMeasurePreserving)
    · intro h hh
      obtain ⟨x, hx⟩ := (H.equivOp.symm h).property
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply hh
        apply H.equivOp.symm.injective
        exact Subtype.ext (by simpa using hx.symm)
      have htranslate : (h • D : Set G) =
          (algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b : Set 𝔸[F]) := by
        ext d
        simp only [Set.mem_smul_set]
        change (∃ a ∈ D, a.toAdd + (H.equivOp.symm h).val.toAdd = d.toAdd) ↔
          (∃ a ∈ D, algebraMap F 𝔸[F] x + a.toAdd = d.toAdd)
        change algebraMap F 𝔸[F] x = (H.equivOp.symm h).val.toAdd at hx
        simp only [hx, add_comm]
      rw [htranslate]
      exact (adeleFundamentalDomain_disjoint F b x hx0).aedisjoint
  have hcompact : IsCompact (closure D) := adeleFundamentalDomain_precompact F b
  obtain ⟨ν, hν, hmass⟩ := additiveTamagawaMeasure_quotientVolume F
  have hνfinite : ν univ ≠ ⊤ := hmass.trans_ne ENNReal.one_ne_top
  exact (weilQuotientMeasure_univ_eq_measure_fundamentalDomain hclosed hν hνfinite hD
    hcompact hcover).symm.trans hmass

/-- Paper: Definition A.3.1.1, p. 555. Exactly one regular additive Haar measure on
the S-adeles gives the quotient by the diagonal S-integers mass one. -/
theorem sAdditiveCovolumeOneMeasure_existsUnique :
    ∃! μ : Measure (SAdeleRing F S), μ.IsAddHaarMeasure ∧ μ.Regular ∧
      ∃ ν : Measure (Multiplicative (SAdeleRing F S) ⧸ Aₛ),
        IsWeilQuotientMeasure Aₛ (show Measure (Multiplicative (SAdeleRing F S)) from μ)
          Measure.count ν ∧ ν univ = 1 := by
  let G := Multiplicative (SAdeleRing F S)
  let H := Aₛ
  let Q := G ⧸ H
  obtain ⟨-, hclosed, hdiscrete, -, -, hcompact, -, -⟩ := sAdele_additive_quotient F S
  let : IsClosed (H : Set G) := hclosed
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : CompactSpace Q := hcompact
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace G := by
    change BorelSpace (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : BorelSpace Q := ⟨rfl⟩
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hclosed
  -- Start with Haar probability measure on the quotient and lift it using counting measure.
  let K : TopologicalSpace.PositiveCompacts Q := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν : Measure Q := Measure.haarMeasure K
  have hν : ν univ = 1 := Measure.haarMeasure_self (K₀ := K)
  let μ := ses.inducedMeasure count ν
  have hweil : IsWeilQuotientMeasure H μ count ν := by
    refine ⟨inferInstance, inferInstance, fun f hf ↦ ?_⟩
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    change (∫ x, fc x ∂μ) = _
    rw [integral_inducedMeasure_complex ses count ν fc, ses.integrate_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q ↦ ?_)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact ses.pushforward_apply_apply count fc q.out
  refine ⟨μ, ⟨?_, ses.inducedMeasure_regular count ν, ν, hweil, hν⟩, ?_⟩
  · have hhaar := ses.isHaarMeasure_inducedMeasure count ν
    exact
      { toIsFiniteMeasureOnCompacts := hhaar.toIsFiniteMeasureOnCompacts
        toIsOpenPosMeasure := hhaar.toIsOpenPosMeasure
        map_add_left_eq_self := fun x ↦ hhaar.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  rintro μ' ⟨-, hregular, ν', ⟨hhaar', hregular', hweil'⟩, hν'⟩
  let : (show Measure G from μ').Regular := hregular
  let : ν'.IsHaarMeasure := hhaar'
  let : ν'.Regular := hregular'
  have heq : ν' = ν := by
    have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
    have hmass := congrArg (fun m : Measure Q ↦ m univ) hscale
    change ν' univ = (ν'.haarScalarFactor ν : ℝ≥0∞) * ν univ at hmass
    rw [hν', hν, mul_one] at hmass
    rw [hscale, ENNReal.coe_inj.mp hmass.symm, one_smul]
  subst ν'
  apply Measure.ext_of_integral_eq_on_compactlySupported (X := G)
  intro f
  let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ x : G, f x ∂(show Measure G from μ')) =
        ∫ x : G, (f x : ℂ) ∂(show Measure G from μ') := integral_complex_ofReal.symm
    _ = ∫ x : G, (f x : ℂ) ∂μ := (hweil' fc hc).trans (hweil.2.2 fc hc).symm
    _ = Complex.ofReal (∫ x : G, f x ∂μ) := integral_complex_ofReal

/-- Paper: Definition A.3.1.1, p. 555. This normalization gives the additive
quotient by the diagonal S-integers mass one.
Deviation: The notation distinguishes it from the product measure of Definition A.3.4.1. -/
def sAdditiveCovolumeOneMeasure : Measure (SAdeleRing F S) :=
  (sAdditiveCovolumeOneMeasure_existsUnique F S).exists.choose

/-- Paper: Definition A.3.1.1, p. 555. An S-adelic fundamental domain has mass one
for the additive measure normalized by the quotient. -/
theorem sAdditiveCovolumeOneMeasure_fundamentalDomain :
    sAdditiveCovolumeOneMeasure F S
      (sAdeleFundamentalDomain F S (RingOfIntegers.basis F)) = 1 := by
  classical
  let G := Multiplicative (SAdeleRing F S)
  let H := Aₛ
  let μ : Measure G := sAdditiveCovolumeOneMeasure F S
  let b := RingOfIntegers.basis F
  let D : Set G := sAdeleFundamentalDomain F S b
  let I := integralAdelesOutside F S
  let p := adeleProjection F S
  obtain ⟨-, hclosed, hdiscrete, -⟩ := sAdele_additive_quotient F S
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable ((S : Set (Primes(F))).integer F) := inferInstance
  let : Countable H := (Set.countable_range dₛ).to_subtype
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
  let : BorelSpace G := by
    change BorelSpace (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  obtain ⟨hμ, -, ν, hν, hmass⟩ :=
    Classical.choose_spec (sAdditiveCovolumeOneMeasure_existsUnique F S).exists
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  obtain ⟨e, -, -, he⟩ := integralAdelesOutside_factors F S
  have hlift (a : SAdeleRing F S) : ∃ c : I, p c.val = a :=
    ⟨e.symm (a, 0), (he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _))⟩
  have hIntegral (a : 𝔸[F]) (ha : a ∈ adeleFundamentalDomain F b) : a ∈ I := by
    have h := ha.2
    simp only [I, integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies] at h ⊢
    exact fun v _ ↦ h v
  -- On adeles integral outside S, membership in the two domains agrees under projection.
  have hproject (a : I) : p a.val ∈ D ↔ a.val ∈ adeleFundamentalDomain F b := by
    change (_ ∧ ∀ v : S, a.val.2 v.val ∈ v.val.adicCompletionIntegers F) ↔
      (_ ∧ a.val ∈ integralAdelesOutside F ∅)
    refine and_congr_right fun _ ↦ ?_
    have houtside := a.property
    simp only [I, integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies] at houtside ⊢
    refine ⟨fun h v ↦ ?_, fun h v ↦ h v.val⟩
    by_cases hv : v ∈ S
    · exact h ⟨v, hv⟩
    · exact houtside v hv
  have hmeas : MeasurableSet D := by
    have hinf : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
      change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
      simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
        (continuous_apply v.1)).prodMk
        (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
          (continuous_apply v.1))
    have hinfMeas : MeasurableSet (infiniteAdeleFundamentalDomain F b) :=
      (ZSpan.fundamentalDomain_measurableSet _).preimage hinf.measurable
    have hfinMeas : MeasurableSet {x : ∀ v : S, v.val.adicCompletion F |
        ∀ v : S, x v ∈ v.val.adicCompletionIntegers F} :=
      MeasurableSet.univ_pi' fun _ ↦ (Valued.isClosed_integer _).measurableSet
    exact hinfMeas.prod hfinMeas
  have hcompact : IsCompact (closure D) := by
    have hp : Continuous p :=
      continuous_fst.prodMk (continuous_pi fun v ↦
        (RestrictedProduct.continuous_eval v.val).comp continuous_snd)
    refine ((adeleFundamentalDomain_precompact F b).image hp).closure_of_subset ?_
    intro a ha
    obtain ⟨c, hc⟩ := hlift a
    exact ⟨c.val, subset_closure ((hproject c).mp (hc.symm ▸ ha)), hc⟩
  have hcover (a : G) : ∃ h : H.op, h • a ∈ D := by
    obtain ⟨c, hc⟩ := hlift a.toAdd
    have hcu : c.val ∈ ⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b :=
      (adeleFundamentalDomain_cover F b).symm ▸ mem_univ _
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hcu
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hx
    change algebraMap F 𝔸[F] x + y = c.val at hxy
    have hxI : algebraMap F 𝔸[F] x ∈ I := by
      have h := I.sub_mem c.property (hIntegral y hy)
      rwa [← hxy, add_sub_cancel_right] at h
    let xS : (S : Set (Primes(F))).integer F :=
      ⟨x, (diagonal_mem_integralAdelesOutside F S x).mp hxI⟩
    let h : H := ⟨Multiplicative.ofAdd (dₛ xS), ⟨xS, rfl⟩⟩
    have hd : Multiplicative.ofAdd (p y) * (h : G) = a := by
      change p y + p (algebraMap F 𝔸[F] x) = a.toAdd
      rw [add_comm, ← map_add, hxy, hc]
    refine ⟨H.equivOp h⁻¹, ?_⟩
    change a * (h : G)⁻¹ ∈ D
    rw [← hd, mul_inv_cancel_right]
    exact (hproject ⟨y, hIntegral y hy⟩).mpr hy
  have hD : IsFundamentalDomain H.op D μ := by
    refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet (Filter.Eventually.of_forall hcover) ?_
      (fun h ↦ (measurePreserving_smul h μ).quasiMeasurePreserving)
    intro h hh
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro a ha haD
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp ha
    obtain ⟨x, hx⟩ := (H.equivOp.symm h).property
    change dₛ x = (H.equivOp.symm h).val.toAdd at hx
    have hx0 : (x : F) ≠ 0 := by
      intro hzero
      have : x = 0 := Subtype.ext hzero
      subst x
      apply hh
      apply H.equivOp.symm.injective
      exact Subtype.ext (by simpa using hx.symm)
    obtain ⟨c, hc⟩ := hlift y.toAdd
    let a₀ : I := integralAdeleDiagonal F S x + c
    have ha₀ : p a₀.val ∈ D := by
      change p (algebraMap F 𝔸[F] (x : F) + c.val) ∈ D
      rw [map_add, hc, show p (algebraMap F 𝔸[F] (x : F)) = dₛ x from rfl, hx, add_comm]
      exact haD
    refine Set.disjoint_left.mp (adeleFundamentalDomain_disjoint F b (x : F) hx0)
      (Set.mem_vadd_set.mpr ⟨c.val, (hproject c).mp (hc.symm ▸ hy), rfl⟩)
      ((hproject a₀).mp ha₀)
  exact (weilQuotientMeasure_univ_eq_measure_fundamentalDomain (μ := μ) hclosed hν
    (hmass.trans_ne ENNReal.one_ne_top) hD hcompact hcover).symm.trans hmass

/-- Paper: Definition A.3.1.2(1)–(2), p. 556. Transfer Lebesgue measure from the
real line or twice plane Lebesgue measure from the complex line to the completion. -/
def infiniteLocalAdditiveTamagawaMeasure (v : InfinitePlace F) : Measure v.Completion :=
  if h : v.IsReal then
    Measure.map (ringEquivRealOfIsReal h).symm (volume : Measure ℝ)
  else
    Measure.map (ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm
      (2 • (volume : Measure ℂ))

/-- Paper: Definition A.3.1.2(1)–(2), p. 556. The local archimedean additive measure
assigns mass one to the real unit interval and mass two to the complex unit square. -/
theorem infiniteLocalAdditiveTamagawaMeasure_unitBox (v : InfinitePlace F) :
    (∀ h : v.IsReal, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivRealOfIsReal h).symm '' Icc (0 : ℝ) 1) = 1) ∧
    (∀ h : v.IsComplex, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivComplexOfIsComplex h).symm '' {z : ℂ | z.re ∈ Icc 0 1 ∧ z.im ∈ Icc 0 1}) = 2) :=
  by
    let : BorelSpace v.Completion := ⟨rfl⟩
    constructor
    · intro h
      rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
      let e := (isometryEquivRealOfIsReal h).symm.toHomeomorph.toMeasurableEquiv
      change (volume : Measure ℝ).map e (e '' Icc 0 1) = 1
      rw [e.map_apply, e.injective.preimage_image]
      simp [Real.volume_Icc]
    · intro h
      rw [infiniteLocalAdditiveTamagawaMeasure,
        dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr h)]
      let e := (isometryEquivComplexOfIsComplex h).symm.toHomeomorph.toMeasurableEquiv
      let square := Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      change Measure.map e (2 • (volume : Measure ℂ)) (e '' square) = 2
      rw [e.map_apply, e.injective.preimage_image]
      have hvolume : volume square = 1 := by
        dsimp only [square]
        rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
          Measure.volume_eq_prod, Measure.prod_prod]
        simp [Real.volume_Icc]
      rw [two_nsmul, add_apply, hvolume]
      norm_num

-- The exponent of v in the global different is the exponent of the local different.
local notation "differentExp(" F ", " v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "differentMass(" F ", " v ")" =>
  Inv.inv (ENNReal.ofReal (Real.sqrt (Nat.cast (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) ^
    differentExp(F, v))))

/-- Paper: Definition A.3.1.2(3), p. 556. Scale additive Haar measure so that the
integer ring has mass equal to the inverse square root of the norm of the local different.
Deviation: The norm is computed using the corresponding exponent in the global different. -/
def finiteLocalAdditiveTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F) :=
  let μ := Measure.addHaar (G := v.adicCompletion F)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) • μ

/-- Paper: Definition A.3.1.2(3), p. 556. The mass of the local integer ring is
the inverse square root of the local different norm. -/
theorem finiteLocalAdditiveTamagawaMeasure_integers (v : Primes(F)) :
    finiteLocalAdditiveTamagawaMeasure F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      differentMass(F, v) := by
  let O := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hK : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  let μ := Measure.addHaar (G := v.adicCompletion F)
  have hpos := hO.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  exact ENNReal.div_mul_cancel hpos.ne' (hK.measure_ne_top (μ := μ))

/-- Paper: Definition A.3.1.2, p. 556. The local additive Tamagawa measures
are additive Haar measures on their completions. -/
theorem finiteLocalAdditiveTamagawaMeasure_isAddHaar (v : Primes(F)) :
    (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  let μ := Measure.addHaar (G := v.adicCompletion F)
  let O := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hK : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  have hmass := hO.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hnorm : 0 < (v.asIdeal.absNorm : ℝ) :=
    Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hsqrt := Real.sqrt_pos_of_pos (pow_pos hnorm (differentExp(F, v)))
  change ((differentMass(F, v) / μ O) • μ).IsAddHaarMeasure
  exact Measure.IsAddHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      hK.measure_ne_top (μ := μ)⟩)
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne') hmass.ne')

/-- Paper: §A.3.1, p. 556. The local different contributes mass one at
all but finitely many places, so the finite-tail products have finite support. -/
theorem finiteLocalTamagawaMass_finite :
    {v : Primes(F) | differentMass(F, v) ≠ 1}.Finite := by
  have hDifferent : differentIdeal ℤ (𝓞 F) ≠ (0 : Ideal (𝓞 F)) := differentIdeal_ne_bot
  refine (Ideal.finite_factors hDifferent).subset ?_
  intro v hv
  by_contra h
  exact hv (by simp [multiplicity_eq_zero_of_not_dvd h])

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
section

omit [NumberField F] in
/-- The archimedean factors are additive Haar measures by transport from the real and
complex lines. -/
private theorem infiniteLocalAdditiveTamagawaMeasure_haar (v : InfinitePlace F) :
    (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  let : BorelSpace v.Completion := ⟨rfl⟩
  by_cases h : v.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

/-- In mixed real and complex coordinates, the archimedean product measure is Lebesgue
measure multiplied by two for each complex place. -/
private theorem infiniteLocalAdditiveTamagawaMeasure_map_mixedSpace :
    (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      ((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F) • (volume : Measure (mixedEmbedding.mixedSpace F)) := by
  let μ := infiniteLocalAdditiveTamagawaMeasure F
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : (μ v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F v
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ (fun v ↦ v.IsReal)
  let reindex : {v : InfinitePlace F // ¬ v.IsReal} ≃ {v : InfinitePlace F // v.IsComplex} :=
    Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex
  have hr (v : {v : InfinitePlace F // v.IsReal}) :
      MeasurePreserving (ringEquivRealOfIsReal v.2) (μ v) volume := by
    let e := (isometryEquivRealOfIsReal v.2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left v.2]
    change (volume.map e.symm).map e = _
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hc (v : {v : InfinitePlace F // ¬ v.IsReal}) :
      MeasurePreserving (ringEquivComplexOfIsComplex (reindex v).2)
        (μ v) ((2 : ℝ≥0) • (volume : Measure ℂ)) := by
    let e := (isometryEquivComplexOfIsComplex (reindex v).2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right v.2]
    change (Measure.map e.symm (2 • (volume : Measure ℂ))).map e = _
    rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0) • volume by simp [two_smul]]
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hright := (measurePreserving_piCongrLeft
    (fun _ : {v : InfinitePlace F // v.IsComplex} ↦ (2 : ℝ≥0) • (volume : Measure ℂ)) reindex).comp
      (measurePreserving_pi (ι := {v : InfinitePlace F // ¬ v.IsReal}) _ _ hc)
  let μreal := fun v : {v : InfinitePlace F // v.IsReal} ↦ μ v
  let μcomplex := fun v : {v : InfinitePlace F // ¬ v.IsReal} ↦ μ v
  let (v : {v : InfinitePlace F // v.IsReal}) : SigmaFinite (μreal v) :=
    inferInstanceAs (SigmaFinite (μ v.val))
  let (v : {v : InfinitePlace F // ¬ v.IsReal}) : SigmaFinite (μcomplex v) :=
    inferInstanceAs (SigmaFinite (μ v.val))
  let : SigmaFinite (Measure.pi μreal) := Measure.pi.sigmaFinite μreal
  let : SigmaFinite (Measure.pi μcomplex) := Measure.pi.sigmaFinite μcomplex
  have hleft := measurePreserving_pi μreal (fun _ ↦ volume) hr
  let hreal : SFinite (Measure.pi μreal) := inferInstance
  let hcomplex : SFinite (Measure.pi μcomplex) := inferInstance
  have hmap := (hleft.prod (μc := Measure.pi μcomplex) hright).comp hsplit
  let μr : Measure ({v : InfinitePlace F // v.IsReal} → ℝ) := volume
  let μc : Measure ({v : InfinitePlace F // v.IsComplex} → ℂ) := volume
  let k : ℝ≥0 := 2 ^ InfinitePlace.nrComplexPlaces F
  have hpow : (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
      (2 : ℝ≥0) • (volume : Measure ℂ)) = k • μc := by
    apply Measure.pi_eq
    intro T hT
    rw [Measure.coe_nnreal_smul_apply, show μc = Measure.pi (fun _ ↦ volume) from volume_pi,
      Measure.pi_pi]
    simp only [Measure.coe_nnreal_smul_apply, k, ENNReal.coe_pow, ENNReal.coe_ofNat,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, InfinitePlace.nrComplexPlaces]
  have hmap' : (Measure.pi μ).map (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      μr.prod (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
        (2 : ℝ≥0) • (volume : Measure ℂ)) := by
    rw [show μr = Measure.pi (fun _ ↦ volume) from volume_pi]
    exact hmap.map_eq
  rw [hmap', hpow]
  have hk : (k : ℝ≥0∞) = (2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F := by simp [k]
  rw [← hk, ← ENNReal.smul_def]
  change μr.prod (k • μc) = k • μr.prod μc
  refine Measure.prod_eq fun U V _ _ ↦ ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.coe_nnreal_smul_apply,
    mul_left_comm]

/-- The archimedean fundamental domain has local product mass the square root of the
absolute discriminant. -/
private theorem infiniteAdeleFundamentalDomain_tamagawaMass :
    let B := infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)
    MeasurableSet B ∧
      Measure.pi (infiniteLocalAdditiveTamagawaMeasure F) B =
        ENNReal.ofReal (Real.sqrt (↑(discr F).natAbs : ℝ)) := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let D := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
  have he : Continuous e := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  have hD : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
  have hB : infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F) = e ⁻¹' D := by
    unfold infiniteAdeleFundamentalDomain
    dsimp only [D]
    congr 2
    apply DFunLike.ext
    intro i
    rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply,
      mixedEmbedding.latticeBasis_apply, integralBasis_apply]
    rfl
  dsimp only
  rw [hB, ← Measure.map_apply he.measurable hD, infiniteLocalAdditiveTamagawaMeasure_map_mixedSpace,
    smul_apply, smul_eq_mul, mixedEmbedding.volume_fundamentalDomain_latticeBasis]
  refine ⟨hD.preimage he.measurable, ?_⟩
  rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, one_mul]
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnNorm, Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

/-- The product of the local integer masses is the reciprocal square root of the
absolute discriminant. -/
private theorem finiteLocalTamagawaMass_finprod :
    (∏ᶠ v : Primes(F), differentMass(F, v)) =
      (ENNReal.ofReal (Real.sqrt (↑(discr F).natAbs : ℝ)))⁻¹ := by
  let J := differentIdeal ℤ (𝓞 F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hJ).toFinset
  have hout (v : Primes(F)) (hv : v ∉ T) : differentExp(F, v) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    simpa [T, J] using hv
  have hfactor : ∏ v ∈ T, v.asIdeal ^ differentExp(F, v) = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset
      (f := fun v : Primes(F) ↦ v.asIdeal ^ differentExp(F, v))]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ
    · intro v hv
      by_contra hn
      exact hv (by simp [hout v hn])
  have hnorm : (∏ v ∈ T, (↑(Ideal.absNorm v.asIdeal) : ℝ) ^ differentExp(F, v)) =
      (↑(discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hfactor :
      (∏ v ∈ T, Ideal.absNorm v.asIdeal ^ differentExp(F, v)) = (discr F).natAbs)
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := T)]
  · rw [← ENNReal.prod_inv_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.sqrt_nonneg _),
      ← Real.sqrt_prod T (fun _ _ ↦ by positivity), hnorm]
    exact fun v _ w _ _ ↦ Or.inr ENNReal.ofReal_ne_top
  · intro v hv
    by_contra hn
    exact hv (by simp [hout v hn])

/-- On the open subring of adeles integral outside S, restriction followed by projection
to the S-adeles preserves the Haar property. The omitted local integer factors are compact. -/
private theorem additiveTamagawaMeasure_projected_haar :
    let I := integralAdelesOutside F S
    ∃ μ : Measure (SAdeleRing F S), μ.IsAddHaarMeasure ∧
      ∀ W : Set (SAdeleRing F S), MeasurableSet W →
        μ W = additiveTamagawaMeasure F {a | a ∈ I ∧ adeleProjection F S a ∈ W} := by
  let I := integralAdelesOutside F S
  let p := (adeleProjection F S).comp I.subtype
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace (SAdeleRing F S) :=
    inferInstanceAs (BorelSpace (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (SAdeleRing F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : T2Space (SAdeleRing F S) :=
    inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let hAdd : MeasurableAdd 𝔸[F] := by
    let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
    exact ContinuousAdd.measurableAdd
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  have hopen : IsOpen (I : Set 𝔸[F]) := by
    change IsOpen (integralAdelesOutside F S : Set 𝔸[F])
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
    exact (isOpen_restrictedProduct_forall_mem
      (G := fun v : Primes(F) ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F) (S : Set (Primes(F)))ᶜ
      (fun _ _ ↦ Valued.isOpen_valuationSubring _)).preimage continuous_snd
  let μ := additiveTamagawaMeasure F
  let : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists).1
  let μI := μ.comap I.subtype
  let : μI.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := hAdd) (f := I.subtype.toAddMonoidHom) μ
      hopen.isOpenEmbedding_subtypeVal
  obtain ⟨e, he, he', hcoord⟩ := integralAdelesOutside_factors F S
  let E : I ≃ₜ _ := ⟨e.toEquiv, he, he'⟩
  have hp : (p : I → SAdeleRing F S) = Prod.fst ∘ E := funext fun a ↦ (hcoord a).1.symm
  have hproper : IsProperMap (p : I → SAdeleRing F S) :=
    hp ▸ (isProperMap_fst_of_compactSpace.comp E.isProperMap)
  have hsurj : Surjective p := hp ▸ Prod.fst_surjective.comp E.surjective
  refine ⟨μI.map p, Measure.isAddHaarMeasure_map μI p.toAddMonoidHom hproper.continuous hsurj
    (isProperMap_iff_tendsto_cocompact.mp hproper).2, ?_⟩
  intro W hW
  rw [Measure.map_apply hproper.continuous.measurable hW]
  change (μ.comap (Subtype.val : I → 𝔸[F])) (p ⁻¹' W) = _
  have hi : MeasurableEmbedding (Subtype.val : I → 𝔸[F]) :=
    hopen.isOpenEmbedding_subtypeVal.measurableEmbedding
  rw [hi.comap_apply]
  congr 1
  ext a
  exact ⟨fun ⟨x, hx, hxa⟩ ↦ ⟨hxa ▸ x.property, hxa ▸ hx⟩,
    fun ⟨ha, hWa⟩ ↦ ⟨⟨a, ha⟩, hWa, rfl⟩⟩

/-- Paper: Lemma A.3.1.3, p. 556. The global additive measure is the restricted
product of the local measures, expressed on rectangles with integral tails.
Deviation: The infinite places are grouped into a finite product measure. -/
theorem additiveTamagawaMeasure_restrictedProduct
    (B : Set (InfiniteAdeleRing F)) (hB : MeasurableSet B)
    (U : (v : S) → Set (v.val.adicCompletion F)) (hU : ∀ v, MeasurableSet (U v)) :
    additiveTamagawaMeasure F
        {a | a.1 ∈ B ∧ (∀ v : S, a.2 v.val ∈ U v) ∧ a ∈ integralAdelesOutside F S} =
      Measure.pi (infiniteLocalAdditiveTamagawaMeasure F) B *
        (∏ v : S, finiteLocalAdditiveTamagawaMeasure F v.val (U v)) *
          ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val) := by
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace (SAdeleRing F S) :=
    inferInstanceAs (BorelSpace (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S) :=
    inferInstanceAs (SecondCountableTopology (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (SAdeleRing F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let μarch := infiniteLocalAdditiveTamagawaMeasure F
  let μf (v : S) := finiteLocalAdditiveTamagawaMeasure F v.val
  let (v : InfinitePlace F) : (μarch v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F v
  have hfinite (v : S) : (μf v).IsAddHaarMeasure := by
    let O := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
    let μ := Measure.addHaar (G := v.val.adicCompletion F)
    have hO : IsOpen O := Valued.isOpen_valuationSubring _
    have hK : IsCompact O := isCompact_iff_compactSpace.mpr inferInstance
    have hpos : μ O ≠ 0 := (hO.measure_pos μ ⟨0, (v.val.adicCompletionIntegers F).zero_mem⟩).ne'
    have htop : μ O ≠ ⊤ := hK.measure_ne_top
    have hnorm : 0 < Ideal.absNorm v.val.asIdeal :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.val.ne_bot)
    change ((differentMass(F, v.val) / μ O) • μ).IsAddHaarMeasure
    rw [div_eq_mul_inv]
    apply Measure.IsAddHaarMeasure.smul
    · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
        (ENNReal.inv_ne_zero.mpr htop)
    · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)).ne')
        (ENNReal.inv_ne_top.mpr hpos)
  let (v : S) : (μf v).IsAddHaarMeasure := hfinite v
  let μ : Measure (SAdeleRing F S) := (Measure.pi μarch).prod (Measure.pi μf)
  let : BorelSpace ((v : InfinitePlace F) → v.Completion) := inferInstance
  let : BorelSpace ((v : S) → v.val.adicCompletion F) := inferInstance
  let : (Measure.pi μarch).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (Measure.pi μf).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨ν, hν, hrect⟩ := additiveTamagawaMeasure_projected_haar F S
  let : ν.IsAddHaarMeasure := hν
  let c := ν.addHaarScalarFactor μ
  have hscale : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have happly (B' : Set (InfiniteAdeleRing F)) (hB' : MeasurableSet B')
      (U' : (v : S) → Set (v.val.adicCompletion F)) (hU' : ∀ v, MeasurableSet (U' v)) :
      additiveTamagawaMeasure F
          {a | a.1 ∈ B' ∧ (∀ v : S, a.2 v.val ∈ U' v) ∧ a ∈ integralAdelesOutside F S} =
        (c : ℝ≥0∞) * (Measure.pi μarch B' * ∏ v : S, μf v (U' v)) := by
    let W : Set (SAdeleRing F S) := B' ×ˢ Set.univ.pi U'
    have hW : MeasurableSet W := hB'.prod (MeasurableSet.pi (Set.to_countable _) fun v _ ↦ hU' v)
    have hset : {a : 𝔸[F] | a ∈ integralAdelesOutside F S ∧ adeleProjection F S a ∈ W} =
        {a | a.1 ∈ B' ∧ (∀ v : S, a.2 v.val ∈ U' v) ∧ a ∈ integralAdelesOutside F S} := by
      ext a
      change (a ∈ integralAdelesOutside F S ∧ (a.1 ∈ B' ∧ (fun v : S ↦ a.2 v.val) ∈
        Set.univ.pi U')) ↔ _
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_ofPred_eq]
      tauto
    rw [← hset, ← hrect W hW, hscale, smul_apply]
    change (c : ℝ≥0∞) * ((Measure.pi μarch).prod (Measure.pi μf)) (B' ×ˢ Set.univ.pi U') = _
    rw [Measure.prod_prod, Measure.pi_pi]
  let D := infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)
  let O (v : S) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
  let d := ENNReal.ofReal (Real.sqrt (↑(discr F).natAbs : ℝ))
  obtain ⟨hD, hmassD⟩ := infiniteAdeleFundamentalDomain_tamagawaMass F
  have hO (v : S) : MeasurableSet (O v) := (Valued.isOpen_valuationSubring _).measurableSet
  have hdomain : {a : 𝔸[F] | a.1 ∈ D ∧ (∀ v : S, a.2 v.val ∈ O v) ∧
      a ∈ integralAdelesOutside F S} = adeleFundamentalDomain F (RingOfIntegers.basis F) := by
    ext a
    change (_ ∧ (∀ v : S, a.2 v.val ∈ O v) ∧ a ∈ integralAdelesOutside F S) ↔
      (_ ∧ a ∈ integralAdelesOutside F ∅)
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies]
    refine and_congr_right fun _ ↦ ⟨fun ⟨hin, hout⟩ v ↦ ?_, fun hall ↦ ⟨fun v ↦ hall v.val,
      fun v _ ↦ hall v⟩⟩
    by_cases hv : v ∈ S
    · exact hin ⟨v, hv⟩
    · exact hout v hv
  have hnormalize := happly D hD O hO
  rw [hdomain, additiveTamagawaMeasure_fundamentalDomain, hmassD] at hnormalize
  simp only [μf, O, finiteLocalAdditiveTamagawaMeasure_integers] at hnormalize
  let tail := ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val)
  have hsplit : (∏ v : S, differentMass(F, v.val)) * tail = d⁻¹ := by
    rw [show d⁻¹ = _ from (finiteLocalTamagawaMass_finprod F).symm]
    rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun v ↦ differentMass(F, v)),
      ← finprod_mem_coe_finset,
      show tail = ∏ᶠ v ∈ (S : Set (Primes(F)))ᶜ, differentMass(F, v) from
        finprod_set_coe_eq_finprod_mem (f := fun v ↦ differentMass(F, v))
          (S : Set (Primes(F)))ᶜ]
    have hpartition := finprod_mem_inter_mul_sdiff'
      (f := fun v : Primes(F) ↦ differentMass(F, v)) (s := Set.univ) (S : Set (Primes(F)))
      ((finiteLocalTamagawaMass_finite F).subset Set.inter_subset_right)
    rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff, finprod_mem_univ] at hpartition
    exact hpartition
  have hdisc : 0 < (discr F).natAbs := Int.natAbs_pos.mpr (discr_ne_zero F)
  have hcancel : d * d⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
  have hc : (c : ℝ≥0∞) = tail := calc
    (c : ℝ≥0∞) = (c : ℝ≥0∞) * (d * d⁻¹) := by rw [hcancel, mul_one]
    _ = ((c : ℝ≥0∞) * (d * ∏ v : S, differentMass(F, v.val))) * tail := by
      rw [← hsplit, ← mul_assoc d, ← mul_assoc]
    _ = tail := by rw [← hnormalize, one_mul]
  rw [happly B hB U hU, hc, mul_comm tail]

end

-- TODO(paper-gap): The S-local equality in (A.3.1.3) fails for the quotient-volume-one
-- measure of Definition A.3.1.1. For F = ℚ(i) and S archimedean, the product has
-- quotient mass 2, since the Gaussian integers have Euclidean covolume 1 and ν∞ = 2 dx dy.

section AdeleHaarScaling

open Filter Topology
open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "AI" => InfiniteAdeleRing F
local notation:max "𝒪[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v

private local instance (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
private local instance (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
private local instance (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
  compactSpace_adicCompletionIntegers v
private local instance :
    Fact (∀ v : Primes(F), IsOpen (𝒪[v] : Set (v.adicCompletion F))) :=
  ⟨fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
private local instance : BorelSpace AI :=
  inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
private local instance : SecondCountableTopology AI :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
private local instance : T2Space AI :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
private local instance : LocallyCompactSpace AF := by
  change LocallyCompactSpace (Πʳ v : Primes(F), [v.adicCompletion F, 𝒪[v]])
  infer_instance
private local instance : T2Space AF := by
  change T2Space (Πʳ v : Primes(F), [v.adicCompletion F, 𝒪[v]])
  infer_instance
private local instance : MeasurableSpace AF := borel _
private local instance : BorelSpace AF := ⟨rfl⟩
private local instance : BorelSpace 𝔸[F] := ⟨rfl⟩
private local instance : LocallyCompactSpace 𝔸[F] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × AF))
private local instance : T2Space 𝔸[F] := inferInstanceAs (T2Space (AI × AF))

/-- Principal translates of the precompact adelic fundamental domain give a countable compact cover. -/
private theorem adeleHaar_sigmaCompactSpace : SigmaCompactSpace 𝔸[F] := by
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let b := RingOfIntegers.basis F
  let D := adeleFundamentalDomain F b
  let K (q : F) := algebraMap F 𝔸[F] q +ᵥ closure D
  refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact IsCompact.vadd _ (adeleFundamentalDomain_precompact F b)
  · rw [Set.sUnion_range]
    exact eq_top_mono (Set.iUnion_mono fun _ ↦ Set.vadd_set_mono (subset_closure (s := D)))
      (adeleFundamentalDomain_cover F b)

omit [NumberField F] in
/-- The archimedean local measure is Haar, by transport from the real or complex line. -/
private theorem infiniteLocalAdditiveTamagawaMeasure_isAddHaar (v : InfinitePlace F) :
    (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  by_cases h : v.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    let e : ℝ ≃ₜ+ v.Completion :=
      { (ringEquivRealOfIsReal h).symm.toAddEquiv,
        (isometryEquivRealOfIsReal h).symm.toHomeomorph with }
    exact e.isAddHaarMeasure_map volume
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    let h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    let e : ℂ ≃ₜ+ v.Completion :=
      { (ringEquivComplexOfIsComplex h').symm.toAddEquiv,
        (isometryEquivComplexOfIsComplex h').symm.toHomeomorph with }
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      have heq : (2 : ℕ) • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume := by
        rw [two_nsmul, ← one_add_one_eq_two, add_smul, one_smul]
      rw [heq]
      exact Measure.IsAddHaarMeasure.smul volume (by norm_num) (by simp)
    exact e.isAddHaarMeasure_map (2 • volume)

/-- Archimedean multiplication scales the measure of the closed unit polydisc by the product
of the real absolute values and the squares of the complex absolute values. -/
private theorem infiniteAdeleHaar_unitPolydisc (u : AIˣ) :
    let D : Set AI := Set.univ.pi (fun _ ↦ Metric.closedBall 0 1)
    let ν := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
    ν ((fun a : AI ↦ u.val * a) '' D) =
      ENNReal.ofReal (∏ w : InfinitePlace F, ‖u.val w‖ ^ w.mult) * ν D := by
  let (v : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_isAddHaar F v
  dsimp only
  rw [show (fun a : AI ↦ u.val * a) =
    Pi.map (fun v ↦ (u.val v * ·)) from rfl, Set.piMap_image_univ_pi, Measure.pi_pi, Measure.pi_pi]
  have hl (v : InfinitePlace F) :
      (fun x : v.Completion ↦ u.val v * x) '' Metric.closedBall 0 1 =
        Metric.closedBall 0 ‖u.val v‖ := by
    have hne : u.val v ≠ 0 := by
      have hprod : u.val v * u.inv v = 1 := congrFun u.val_inv v
      intro h
      simp [h] at hprod
    change u.val v • Metric.closedBall 0 1 = _
    simpa only [smul_zero, mul_one] using smul_closedBall' hne (0 : v.Completion) 1
  have hlocal (v : InfinitePlace F) (r : ℝ) :
      infiniteLocalAdditiveTamagawaMeasure F v (Metric.closedBall 0 r) =
        ENNReal.ofReal r ^ v.mult *
          infiniteLocalAdditiveTamagawaMeasure F v (Metric.closedBall 0 1) := by
    by_cases h : v.IsReal
    · rw [h.mult_eq_one, pow_one, infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
      let e := isometryEquivRealOfIsReal h
      let em := e.toHomeomorph.toMeasurableEquiv
      change Measure.map em.symm volume (Metric.closedBall 0 r) =
        _ * Measure.map em.symm volume (Metric.closedBall 0 1)
      have hpre (s : ℝ) : em.symm ⁻¹' Metric.closedBall 0 s = Metric.closedBall 0 s := by
        rw [← em.image_eq_preimage_symm]
        change e '' Metric.closedBall 0 s = _
        rw [e.image_closedBall]
        exact congrArg (Metric.closedBall · s) ((ringEquivRealOfIsReal h).map_zero)
      rw [em.symm.map_apply, em.symm.map_apply, hpre, hpre, Real.volume_closedBall,
        Real.volume_closedBall, mul_one, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm]
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
      rw [hc.mult_eq_two, infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
      let e := isometryEquivComplexOfIsComplex hc
      let em := e.toHomeomorph.toMeasurableEquiv
      change Measure.map em.symm (2 • volume) (Metric.closedBall 0 r) =
        _ * Measure.map em.symm (2 • volume) (Metric.closedBall 0 1)
      have hpre (s : ℝ) : em.symm ⁻¹' Metric.closedBall 0 s = Metric.closedBall 0 s := by
        rw [← em.image_eq_preimage_symm]
        change e '' Metric.closedBall 0 s = _
        rw [e.image_closedBall]
        exact congrArg (Metric.closedBall · s) ((ringEquivComplexOfIsComplex hc).map_zero)
      rw [em.symm.map_apply, em.symm.map_apply, hpre, hpre]
      simp only [two_nsmul, add_apply, Complex.volume_closedBall,
        ENNReal.ofReal_one, one_pow, one_mul, mul_add]
  simp_rw [hl, hlocal _ ‖u.val _‖]
  rw [Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

/-- The product of all local integer rings. -/
private abbrev finiteAdeleIntegersProduct := ∀ v : Primes(F), 𝒪[v]

/-- Finite adeles integral at all finite places. -/
private def integralFiniteAdeles : Set AF := {a | ∀ v : Primes(F), a v ∈ 𝒪[v]}

/-- The pointwise inclusion of the product of integer rings into the finite adeles. -/
private def finiteAdeleIntegerEmbedding : finiteAdeleIntegersProduct F →+ AF where
  toFun := RestrictedProduct.structureMap (fun v : Primes(F) ↦ v.adicCompletion F)
    (fun v ↦ (𝒪[v] : Set (v.adicCompletion F))) cofinite
  map_zero' := by ext v; rfl
  map_add' x y := by ext v; rfl

/-- The integral finite adeles form a compact open subgroup. -/
private theorem finiteAdeleIntegerEmbedding_isOpenEmbedding :
    IsOpenEmbedding (finiteAdeleIntegerEmbedding F) :=
  RestrictedProduct.isOpenEmbedding_structureMap
    (fun v : Primes(F) ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))

/-- A unit at a single finite place gives a unit in the restricted product. -/
private def finiteAdeleSingleUnit (v : Primes(F)) : (v.adicCompletion F)ˣ →* AFˣ :=
  Units.map (RestrictedProduct.mulSingleMonoidHom (fun w : Primes(F) ↦ 𝒪[w]) v)

/-- Evaluation at the selected place gives the original unit. -/
private theorem finiteAdeleSingleUnit_val_same (v : Primes(F)) (u : (v.adicCompletion F)ˣ) :
    (finiteAdeleSingleUnit F v u).val v = u.val :=
  RestrictedProduct.mulSingle_eq_same _ _ _

/-- At every other place a unit supported at one place has coordinate one. -/
private theorem finiteAdeleSingleUnit_val_ne {v w : Primes(F)} (h : w ≠ v)
    (u : (v.adicCompletion F)ˣ) :
    (finiteAdeleSingleUnit F v u).val w = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne _ _ h

/-- The integral finite adeles have positive mass because they are open and contain zero. -/
private theorem finiteAdeleInteger_volume_pos :
    0 < (Measure.addHaar (G := AF)) (integralFiniteAdeles F) := by
  let ν : Measure AF := Measure.addHaar
  have hopen : IsOpen (integralFiniteAdeles F) :=
    RestrictedProduct.isOpen_forall_mem
      (fun v : Primes(F) ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))
  exact hopen.measure_pos ν ⟨0, fun v ↦ 𝒪[v].zero_mem⟩

/-- The integral finite adeles are compact as the image of the product of the local integer rings. -/
private theorem finiteAdeleInteger_isCompact : IsCompact (integralFiniteAdeles F) := by
  have hr : Set.range (finiteAdeleIntegerEmbedding F) = integralFiniteAdeles F :=
    RestrictedProduct.range_structureMap _ _
  rw [← hr]
  have (v : Primes(F)) : CompactSpace ↥(𝒪[v] : Set (v.adicCompletion F)) :=
    compactSpace_adicCompletionIntegers v
  exact isCompact_range (finiteAdeleIntegerEmbedding_isOpenEmbedding F).continuous

/-- A finite idele with local absolute value one everywhere preserves the integral open subgroup. -/
private theorem finiteAdeleHaar_char_eq_one (u : AFˣ)
    (hu : ∀ v : Primes(F), Valued.v (u.val v) = 1) :
    distribHaarChar AF u = 1 := by
  let ν : Measure AF := Measure.addHaar
  have hmem (v : Primes(F)) (x : AF) :
      (u.val * x) v ∈ 𝒪[v] ↔ x v ∈ 𝒪[v] := by
    change Valued.v (u.val v * x v) ≤ 1 ↔ Valued.v (x v) ≤ 1
    rw [map_mul, hu, one_mul]
  have heq : u • integralFiniteAdeles F = integralFiniteAdeles F := by
    ext x
    change x ∈ (fun a : AF ↦ u.val * a) '' (integralFiniteAdeles F) ↔ _
    constructor
    · rintro ⟨a, ha, rfl⟩ v
      exact (hmem v a).2 (ha v)
    · intro hx
      refine ⟨u.inv * x, fun v ↦ (hmem v _).1 ?_, ?_⟩
      · rw [← mul_assoc, u.val_inv, one_mul]
        exact hx v
      · change u.val * (u.inv * x) = x
        rw [← mul_assoc, u.val_inv, one_mul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν)
    (finiteAdeleInteger_volume_pos F).ne' (finiteAdeleInteger_isCompact F).measure_ne_top
  rw [heq, ENNReal.coe_one, one_mul]

/-- At one finite place, multiplication by a uniformizer replaces its integer ring by its
maximal ideal. The resulting subgroup has index equal to the residue field cardinality. -/
private theorem finiteAdeleHaar_char_uniformizer (v : Primes(F)) (π : 𝒪[v])
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) :
    distribHaarChar AF (finiteAdeleSingleUnit F v (Units.mk0 (π : v.adicCompletion F) hπ.ne_zero)) =
      ‖(π : v.adicCompletion F)‖₊ := by
  let u := finiteAdeleSingleUnit F v (Units.mk0 (π : v.adicCompletion F) hπ.ne_zero)
  let e := finiteAdeleIntegerEmbedding F
  let : MeasurableSpace (finiteAdeleIntegersProduct F) := borel _
  let : BorelSpace (finiteAdeleIntegersProduct F) := ⟨rfl⟩
  let ν : Measure AF := Measure.addHaar
  let νO := ν.comap e
  have he := (finiteAdeleIntegerEmbedding_isOpenEmbedding F).measurableEmbedding
  have : νO.IsAddLeftInvariant := ⟨fun x ↦ by
    ext s hs
    have hcont : Continuous (x + ·) := continuous_const.add continuous_id
    rw [Measure.map_apply hcont.measurable hs, he.comap_apply, he.comap_apply]
    have hpre : e '' ((x + ·) ⁻¹' s) = (e x + ·) ⁻¹' (e '' s) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨x + b, hb, map_add e x b⟩
      · rintro ⟨b, hb, h⟩
        refine ⟨b - x, ?_, ?_⟩
        · show x + (b - x) ∈ s
          simpa [add_comm x] using hb
        · rw [map_sub, h]
          exact add_sub_cancel_left (e x) a
    have hm : Measurable (e x + ·) := (continuous_const.add continuous_id).measurable
    rw [hpre, ← Measure.map_apply hm (he.measurableSet_image.mpr hs), map_add_left_eq_self]⟩
  let f : finiteAdeleIntegersProduct F →+ IsLocalRing.ResidueField (𝒪[v]) :=
    (IsLocalRing.residue 𝒪[v]).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w : Primes(F) ↦ 𝒪[w]) v)
  have hf : Surjective f := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨Function.update (0 : finiteAdeleIntegersProduct F) v b, ?_⟩
    change IsLocalRing.residue (𝒪[v]) (Function.update (0 : finiteAdeleIntegersProduct F) v b v) = _
    rw [Function.update_self]
  have hindex : f.ker.index = v.asIdeal.absNorm := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf, AddSubgroup.card_top,
      card_residueField_adicCompletion]
  have hindexpos := zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  have : f.ker.FiniteIndex := ⟨by simp [hindex, hindexpos.ne']⟩
  have hk (a : finiteAdeleIntegersProduct F) : a ∈ f.ker ↔ ∃ b : 𝒪[v], π * b = a v := by
    change IsLocalRing.residue (𝒪[v]) (a v) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff]
    have hg : IsLocalRing.maximalIdeal (𝒪[v]) = Ideal.span {π} := hπ.is_generator
    rw [hg, Ideal.mem_span_singleton]
    exact dvd_def.trans (exists_congr fun b ↦ eq_comm)
  have hmeas : MeasurableSet (f.ker : Set (finiteAdeleIntegersProduct F)) := by
    have hcont : Continuous (fun a : finiteAdeleIntegersProduct F ↦ (a v : v.adicCompletion F)) :=
      continuous_subtype_val.comp (continuous_apply v)
    let val : Valuation (v.adicCompletion F) _ := Valued.v
    have hop := (Valued.isOpen_ball (v.adicCompletion F) 1).preimage hcont
    have hs : (f.ker : Set (finiteAdeleIntegersProduct F)) =
        {a | val.restrict (a v : v.adicCompletion F) < 1} := by
      ext a
      change IsLocalRing.residue (𝒪[v]) (a v) = 0 ↔ _
      rw [IsLocalRing.residue_eq_zero_iff]
      have hlt : a v ∈ IsLocalRing.maximalIdeal (𝒪[v]) ↔ val (a v : v.adicCompletion F) < 1 :=
        Valuation.mem_maximalIdeal_iff _ val
      rw [hlt]
      change val (a v : v.adicCompletion F) < 1 ↔ val.restrict _ < 1
      rw [Valuation.restrict_lt_iff_lt_embedding, map_one]
    rw [hs]
    exact hop.measurableSet
  have himage : e '' (f.ker : Set (finiteAdeleIntegersProduct F)) = u • integralFiniteAdeles F := by
    ext a
    change a ∈ e '' (f.ker : Set (finiteAdeleIntegersProduct F)) ↔
      a ∈ (fun x : AF ↦ u.val * x) '' integralFiniteAdeles F
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨c, hc⟩ := (hk b).1 hb
      let d := Function.update b v c
      refine ⟨e d, fun w ↦ (d w).property, ?_⟩
      apply Subtype.ext
      funext w
      change u.val w * (d w : w.adicCompletion F) = b w
      by_cases h : w = v
      · subst w
        rw [show u.val v = (π : v.adicCompletion F) from finiteAdeleSingleUnit_val_same F v _]
        have hd : d v = c := Function.update_self _ _ _
        rw [hd]
        exact congrArg Subtype.val hc
      · rw [show u.val w = 1 from finiteAdeleSingleUnit_val_ne F h _, one_mul,
          show d w = b w from Function.update_of_ne h _ _]
    · rintro ⟨a, ha, rfl⟩
      let b (w : Primes(F)) : 𝒪[w] := ⟨a w, ha w⟩
      let d := Function.update b v (π * b v)
      have hd : d v = π * b v := Function.update_self _ _ _
      refine ⟨d, (hk d).2 ⟨b v, hd.symm⟩, ?_⟩
      apply Subtype.ext
      funext w
      change (d w : w.adicCompletion F) = u.val w * a w
      by_cases h : w = v
      · subst w
        rw [show u.val v = (π : v.adicCompletion F) from finiteAdeleSingleUnit_val_same F v _,
          hd]
        rfl
      · rw [show u.val w = 1 from finiteAdeleSingleUnit_val_ne F h _, one_mul,
          show d w = b w from Function.update_of_ne h _ _]
  have hmass := f.ker.index_mul_measure hmeas νO
  change (f.ker.index : ℝ≥0∞) * ν.comap e f.ker = ν.comap e univ at hmass
  rw [hindex, he.comap_apply, he.comap_apply, himage, Set.image_univ,
    show range e = integralFiniteAdeles F from RestrictedProduct.range_structureMap _ _] at hmass
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν)
    (finiteAdeleInteger_volume_pos F).ne' (finiteAdeleInteger_isCompact F).measure_ne_top
  change ν (u • integralFiniteAdeles F) =
    (↑‖(π : v.adicCompletion F)‖₊ : ℝ≥0∞) * ν (integralFiniteAdeles F)
  rw [← hmass, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, norm_uniformizer_adicCompletion v _ hπ,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hindexpos), ENNReal.ofReal_natCast,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hindexpos.ne') (ENNReal.natCast_ne_top _),
    one_mul]

/-- On units supported at one finite place, the Haar character is the normalized local
absolute value. A uniformizer and the local integral units generate the local unit group. -/
private theorem finiteAdeleHaar_char_single (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    distribHaarChar AF (finiteAdeleSingleUnit F v x) = ‖x.val‖₊ := by
  let val : Valuation (v.adicCompletion F) _ := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : (v.adicCompletion F)ˣ := Units.mk0 π.val hπ.ne_zero
  let ι := Units.map 𝒪[v].subtype.toMonoidHom
  obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p
    (norm_uniformizer_adicCompletion v _ hπ)
  let k := (e x).1.toAdd
  let t := (e x).2
  have hx : x = p ^ k * ι t := by
    apply e.injective
    rw [map_mul, map_zpow, hep, heι]
    apply Prod.ext
    · change (e x).1 = Multiplicative.ofAdd (k * 1) * 1
      simp [k]
    · change t = (1 : (𝒪[v])ˣ) ^ k * t
      simp
  have hval : Valued.v ((ι t).val) = 1 :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := ι t)).mp
      ⟨t.val.prop, t.inv.prop⟩
  have hn : ‖(ι t).val‖₊ = 1 := by
    apply NNReal.eq
    exact Valued.toNormedField.norm_eq_one_iff.mpr hval
  have hunit : distribHaarChar AF (finiteAdeleSingleUnit F v (ι t)) = 1 := by
    apply finiteAdeleHaar_char_eq_one
    intro w
    by_cases h : w = v
    · subst w
      exact (congrArg Valued.v (finiteAdeleSingleUnit_val_same F v (ι t))).trans hval
    · rw [finiteAdeleSingleUnit_val_ne F h, map_one]
  conv_lhs => rw [hx, map_mul, map_mul, map_zpow, map_zpow,
    finiteAdeleHaar_char_uniformizer F v π hπ, hunit, mul_one]
  conv_rhs => rw [hx, Units.val_mul, nnNorm_mul, Units.val_zpow_eq_zpow_val,
    nnNorm_zpow, hn, mul_one]
  rfl

/-- The compact open subgroup of integral finite adeles acquires the product of the normalized
finite-place norms as its volume ratio under multiplication by a finite idele. -/
private theorem finiteAdeleHaar_integralImage (u : AFˣ) :
    let D := integralFiniteAdeles F
    let ν : Measure AF := Measure.addHaar
    ν ((fun a : AF ↦ u.val * a) '' D) =
      ENNReal.ofReal (∏ᶠ v : Primes(F), ‖u.val v‖) * ν D := by
  dsimp only
  let χ : AFˣ →* ℝ≥0 := distribHaarChar AF
  let hs := FiniteAdeleRing.hasFiniteMulSupport_norm u
  let s := hs.toFinset
  let ev (v : Primes(F)) : AFˣ →* (v.adicCompletion F)ˣ :=
    Units.map (RestrictedProduct.evalMonoidHom (fun w : Primes(F) ↦ w.adicCompletion F) v)
  let p : AFˣ := ∏ v ∈ s, finiteAdeleSingleUnit F v (ev v u)
  have hp (w : Primes(F)) :
      p.val w = if w ∈ s then u.val w else 1 := by
    let e := (Units.coeHom _).comp (ev w)
    change e p = _
    rw [map_prod]
    by_cases hw : w ∈ s
    · rw [ite_eq_left hw, Finset.prod_eq_single_of_mem w hw]
      · exact finiteAdeleSingleUnit_val_same F w _
      · intro v _ hv
        exact finiteAdeleSingleUnit_val_ne F (Ne.symm hv) _
    · rw [ite_eq_right hw, Finset.prod_eq_one]
      intro v hv
      exact finiteAdeleSingleUnit_val_ne F (v := v) (w := w) (fun h ↦ hw (h.symm ▸ hv)) _
  have hunit : χ (u / p) = 1 := by
    apply finiteAdeleHaar_char_eq_one
    intro v
    change Valued.v ((ev v (u / p)).val) = 1
    rw [map_div, Units.val_div_eq_div_val]
    change Valued.v (u.val v / p.val v) = 1
    rw [hp]
    split_ifs with hv
    · have hu : u.val v ≠ 0 := (ev v u).ne_zero
      rw [div_self hu, map_one]
    · rw [div_one]
      apply Valued.toNormedField.norm_eq_one_iff.mp
      exact not_not.mp (fun h ↦ hv (hs.mem_toFinset.mpr h))
  have hχ : χ u = ∏ v ∈ s, ‖u.val v‖₊ := by
    calc
      χ u = χ ((u / p) * p) := congrArg χ (by simp)
      _ = χ p := by rw [map_mul, hunit, one_mul]
      _ = _ := ?_
    change χ (∏ v ∈ s, finiteAdeleSingleUnit F v (ev v u)) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact finiteAdeleHaar_char_single F v (ev v u)
  change Measure.addHaar (u • integralFiniteAdeles F) =
    _ * Measure.addHaar (integralFiniteAdeles F)
  rw [← distribHaarChar_mul, hχ,
    finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun _ h ↦ hs.mem_toFinset.mpr h),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _)]
  push_cast
  simp only [← coe_nnNorm, ENNReal.ofReal_coe_nnreal]

/-- Paper: Lemma A.3.1.4, p. 556. Multiplication of a Borel set by an idele
scales any additive Haar measure by the idelic norm. -/
theorem adeleHaar_mul_image (μ : Measure 𝔸[F]) [μ.IsAddHaarMeasure]
    (g : 𝕀[F]) (B : Set 𝔸[F]) (hB : MeasurableSet B) :
    μ ((fun a : 𝔸[F] ↦ g.val * a) '' B) = (↑(ideleNorm F g).val : ℝ≥0∞) * μ B := by
  let : SigmaCompactSpace 𝔸[F] := adeleHaar_sigmaCompactSpace F
  let : SigmaCompactSpace (AI × AF) := ‹SigmaCompactSpace 𝔸[F]›
  let : SigmaCompactSpace AF := by
    have h : IsSigmaCompact (Set.range (Prod.snd : AI × AF → AF)) :=
      isSigmaCompact_range continuous_snd
    have hsurj : Surjective (Prod.snd : AI × AF → AF) := Prod.snd_surjective
    exact ⟨hsurj.range_eq ▸ h⟩
  let νinf : Measure AI := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let νf : Measure AF := Measure.addHaar
  let (v : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : νinf.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  -- Compute the Haar character using the product of Haar measures on the two factors.
  let ν := νinf.prod νf
  have : ν.IsAddHaarMeasure :=
    { toIsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
      toIsFiniteMeasureOnCompacts := Measure.prod.instIsFiniteMeasureOnCompacts _ _
      map_add_left_eq_self := fun a ↦ by
        change Measure.map (Prod.map (a.1 + ·) (a.2 + ·)) (νinf.prod νf) = _
        have hai : Measurable (a.1 + ·) := (continuous_const.add continuous_id).measurable
        have haf : Measurable (a.2 + ·) := (continuous_const.add continuous_id).measurable
        rw [← Measure.map_prod_map _ _ hai haf,
          map_add_left_eq_self, map_add_left_eq_self] }
  have hνprod (U : Set AI) (V : Set AF) : ν (U ×ˢ V) = νinf U * νf V := Measure.prod_prod U V
  let U : Set AI := univ.pi (fun _ ↦ Metric.closedBall 0 1)
  let V := integralFiniteAdeles F
  have hucompact : IsCompact U := by
    apply isCompact_univ_pi
    intro v
    by_cases h : v.IsReal
    · let e := isometryEquivRealOfIsReal h
      apply e.toHomeomorph.isEmbedding.isCompact_iff.mpr
      rw [show ⇑e.toHomeomorph = ⇑e from rfl, e.image_closedBall]
      exact isCompact_closedBall _ _
    · let e := isometryEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)
      apply e.toHomeomorph.isEmbedding.isCompact_iff.mpr
      rw [show ⇑e.toHomeomorph = ⇑e from rfl, e.image_closedBall]
      exact isCompact_closedBall _ _
  have hupos : 0 < νinf U := by
    let W : Set AI := univ.pi (fun _ ↦ Metric.ball 0 1)
    have hWopen : IsOpen W := isOpen_set_pi finite_univ fun _ _ ↦ Metric.isOpen_ball
    have hWne : W.Nonempty := ⟨0, by
      intro v _
      change (0 : v.Completion) ∈ Metric.ball 0 1
      exact Metric.mem_ball_self (by norm_num)⟩
    exact (hWopen.measure_pos νinf hWne).trans_le
      (measure_mono (Set.pi_mono fun _ _ ↦ Metric.ball_subset_closedBall))
  have hpos : ν (U ×ˢ V) ≠ 0 := by
    rw [hνprod]
    exact mul_ne_zero hupos.ne' (finiteAdeleInteger_volume_pos F).ne'
  have htop : ν (U ×ˢ V) ≠ ∞ := (hucompact.prod (finiteAdeleInteger_isCompact F)).measure_ne_top
  let ui : AIˣ := (MulEquiv.prodUnits g).1
  let uf : AFˣ := (MulEquiv.prodUnits g).2
  let g' : (AI × AF)ˣ := g
  have himage :
      g' • (U ×ˢ V) =
        ((fun x : AI ↦ ui.val * x) '' U) ×ˢ ((fun x : AF ↦ uf.val * x) '' V) := by
    exact Set.prodMap_image_prod _ _ _ _
  have hscale : ν (g' • (U ×ˢ V)) = (↑(ideleNorm F g).val : ℝ≥0∞) * ν (U ×ˢ V) := by
    rw [himage, hνprod, hνprod]
    change νinf ((fun a : AI ↦ ui.val * a) '' U) * νf ((fun a : AF ↦ uf.val * a) '' V) = _
    rw [infiniteAdeleHaar_unitPolydisc F ui, finiteAdeleHaar_integralImage F uf]
    rw [← ENNReal.ofReal_coe_nnreal, ((ideleNorm_spec F).1 g).2,
      ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _)]
    change (ENNReal.ofReal (∏ v : InfinitePlace F, ‖g.val.1 v‖ ^ v.mult) * νinf U) *
      (ENNReal.ofReal (∏ᶠ v : Primes(F), ‖g.val.2 v‖) * νf V) = _
    ac_rfl
  have : ν.Regular := addHaar_regular_of_sigmaCompactSpace ν
  have : μ.Regular := addHaar_regular_of_sigmaCompactSpace μ
  have hchar : distribHaarChar 𝔸[F] g = (ideleNorm F g).val :=
    show distribHaarChar (AI × AF) g' = _ from
      distribHaarChar_eq_of_measure_smul_eq_mul hpos htop hscale
  have hmeasure : DomMulAct.mk g • μ = (ideleNorm F g).val • μ := by
    rw [Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk g • μ) μ,
      addHaarScalarFactor_smul_eq_distribHaarChar, hchar]
  have hmass := congrArg (fun m : Measure 𝔸[F] ↦ m B) hmeasure
  have hinv : Measurable (fun a : 𝔸[F] ↦ g⁻¹ • a) := measurable_const_smul g⁻¹
  change μ.map (g⁻¹ • ·) B = _ at hmass
  rw [Measure.map_apply hinv hB, Set.preimage_smul_inv] at hmass
  exact hmass

end AdeleHaarScaling


section SelfDuality

variable {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace R]

local instance : MeasurableSpace (PontryaginDual (Multiplicative R)) := borel _

/-- Paper: §A.3.1.1, p. 557. After identifying a ring's additive group with its dual
by the pairing `(x,y) ↦ ψ (x*y)`, the Fourier transform uses the conjugate character. -/
def tamagawaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ) (y : R) : ℂ :=
  ∫ x, f x * star (ψ (x * y) : ℂ) ∂μ

/-- Paper: §A.3.1.1, p. 557. Under the character pairing, the Fourier integral is
the transform of §D.1.1 evaluated at the character attached to the frequency. -/
theorem tamagawaFourier_eq_lcaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ)
    (y : R) (χ : PontryaginDual (Multiplicative R))
    (hχ : ∀ x : R, χ (Multiplicative.ofAdd x) = ψ (x * y)) :
    tamagawaFourier μ ψ f y = lcaFourier (G := Multiplicative R) μ
      (fun x ↦ f x.toAdd) χ := by
  unfold tamagawaFourier lcaFourier
  congr 1
  funext x
  rw [← hχ]
  rfl

/-- Paper: §A.3.1.1, p. 557. A measure is self-dual when the pairing identifies the
additive group with its Pontryagin dual and transports the measure to its Plancherel measure. -/
def IsTamagawaSelfDual (μ : Measure R) (ψ : R → Circle) : Prop :=
  ∃ e : Multiplicative R ≃ₜ* PontryaginDual (Multiplicative R),
    (∀ x y : R, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) = ψ (x * y)) ∧
      IsLCAPlancherelMeasure (G := Multiplicative R) μ
        (Measure.map e (show Measure (Multiplicative R) from μ))

end SelfDuality

open scoped FourierTransform in
/-- Paper: Example A.3.1.5, p. 557. Lebesgue measure is self-dual for the real
character with phase `2πx`. -/
theorem realTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (volume : Measure ℝ) (fun x ↦ Circle.exp (2 * Real.pi * x)) := by
  obtain ⟨e, he⟩ := exists_realPontryaginDualEquiv
  refine ⟨e, he, ?_⟩
  let μ : Measure (Multiplicative ℝ) := volume (α := ℝ)
  let : MeasurableSpace (PontryaginDual (Multiplicative ℝ)) := borel _
  let : BorelSpace (PontryaginDual (Multiplicative ℝ)) := ⟨rfl⟩
  let hvol : (volume : Measure ℝ).IsAddHaarMeasure := inferInstance
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hvol.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hvol.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hvol.map_add_left_eq_self x.toAdd }
  let : μ.Regular := inferInstanceAs (volume : Measure ℝ).Regular
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  let g : ℝ → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
  have hFourier : lcaFourier μ f ∘ e = 𝓕 g := by
    funext y
    change lcaFourier μ f (e y) = 𝓕 g y.toAdd
    rw [lcaFourier, Real.fourier_eq]
    change (∫ x : ℝ, g x * star (e y (Multiplicative.ofAdd x) : ℂ)) =
      ∫ x : ℝ, Real.fourierChar (-inner ℝ x y.toAdd) • g x
    congr 1
    funext x
    have hPair : e y (Multiplicative.ofAdd x) = Real.fourierChar (x * y.toAdd) := by
      change e (Multiplicative.ofAdd y.toAdd) (Multiplicative.ofAdd x) = _
      rw [he, Real.fourierChar_apply', mul_comm x y.toAdd]
    rw [hPair, Circle.star_addChar, Real.inner_apply, Circle.smul_def, smul_eq_mul, mul_comm]
  have h := memLp_two_fourier_and_eLpNorm_eq (f := g) hf₁ hf₂
  have hEmb := e.toHomeomorph.measurableEmbedding
  refine ⟨hEmb.memLp_map_measure_iff.mpr (hFourier ▸ h.1), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ e) 2 μ := hEmb.eLpNorm_map_measure
    _ = eLpNorm (𝓕 g) 2 volume :=
      congrArg (fun k : Multiplicative ℝ → ℂ ↦ eLpNorm k 2 μ) hFourier
    _ = _ := h.2

/-- Paper: Example A.3.1.5, p. 557. The complex Tamagawa pairing identifies the
additive complex plane with its Pontryagin dual. -/
private theorem exists_complexTamagawaDualEquiv :
    ∃ e : Multiplicative ℂ ≃ₜ* PontryaginDual (Multiplicative ℂ),
      ∀ x y : ℂ, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        Circle.exp (4 * Real.pi * (x * y).re) := by
  let G := Multiplicative ℂ
  let phase : ℂ → Circle := fun z ↦ Circle.exp (4 * Real.pi * z.re)
  have hzero : phase 0 = 1 := by simp [phase]
  have hadd (x y : ℂ) : phase (x + y) = phase x * phase y := by
    simp only [phase, Complex.add_re, mul_add, Circle.exp_add]
  have hcont : Continuous phase := Circle.exp.continuous.comp (by fun_prop)
  let pairing : G →* PontryaginDual G :=
    { toFun := fun x ↦
        { toFun := fun y ↦ phase (x.toAdd * y.toAdd)
          map_one' := by change phase (x.toAdd * 0) = 1; rw [mul_zero, hzero]
          map_mul' := fun y z ↦ by
            change phase (x.toAdd * (y.toAdd + z.toAdd)) = _
            rw [mul_add, hadd]
          continuous_toFun := hcont.comp (continuous_const.mul continuous_id) }
      map_one' := PontryaginDual.ext fun y ↦ by
        change phase (0 * y.toAdd) = 1
        rw [zero_mul, hzero]
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change phase ((x.toAdd + y.toAdd) * z.toAdd) =
          phase (x.toAdd * z.toAdd) * phase (y.toAdd * z.toAdd)
        rw [add_mul, hadd] }
  have hpcont : Continuous pairing :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry
      (show G → (G →ₜ* Circle) from pairing)
      (hcont.comp (continuous_fst.mul continuous_snd))
  obtain ⟨eR, heR⟩ := exists_realPontryaginDualEquiv
  let axis (u : ℂ) : Multiplicative ℝ →ₜ* G :=
    let l := (1 : ℝ →L[ℝ] ℝ).smulRight u
    ⟨l.toLinearMap.toAddMonoidHom.toMultiplicative, l.continuous⟩
  -- Restrict a character to each coordinate axis to use real Pontryagin duality.
  have haxis (u : ℂ) (x : G) :
      PontryaginDual.map (axis u) (pairing x) =
        eR (Multiplicative.ofAdd (2 * (x.toAdd * u).re)) := by
    apply PontryaginDual.ext
    intro t
    change phase (x.toAdd * (t.toAdd • u)) =
      eR (Multiplicative.ofAdd (2 * (x.toAdd * u).re)) (Multiplicative.ofAdd t.toAdd)
    rw [heR _ t.toAdd]
    apply congrArg Circle.exp
    rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]
    ring
  have hreal (x : G) :
      PontryaginDual.map (axis 1) (pairing x) = eR (Multiplicative.ofAdd (2 * x.toAdd.re)) := by
    simpa only [mul_one] using haxis 1 x
  have himag (x : G) :
      PontryaginDual.map (axis Complex.I) (pairing x) =
        eR (Multiplicative.ofAdd (-(2 * x.toAdd.im))) := by
    simpa only [Complex.mul_I_re, mul_neg] using haxis Complex.I x
  have hinj : Injective pairing := by
    intro x y hxy
    have hre := eR.injective <| (hreal x).symm.trans <|
      (congrArg (PontryaginDual.map (axis 1)) hxy).trans (hreal y)
    have him := eR.injective <| (himag x).symm.trans <|
      (congrArg (PontryaginDual.map (axis Complex.I)) hxy).trans (himag y)
    change 2 * x.toAdd.re = 2 * y.toAdd.re at hre
    change -(2 * x.toAdd.im) = -(2 * y.toAdd.im) at him
    change x.toAdd = y.toAdd
    exact Complex.ext (by linarith) (by linarith)
  have hsurj : Surjective pairing := by
    intro χ
    let a := (eR.symm (PontryaginDual.map (axis 1) χ)).toAdd
    let b := (eR.symm (PontryaginDual.map (axis Complex.I) χ)).toAdd
    let x : G := Multiplicative.ofAdd (⟨a / 2, -(b / 2)⟩ : ℂ)
    have hre : PontryaginDual.map (axis 1) (pairing x) = PontryaginDual.map (axis 1) χ := by
      rw [hreal, show 2 * x.toAdd.re = a by change 2 * (a / 2) = a; ring]
      exact eR.apply_symm_apply _
    have him : PontryaginDual.map (axis Complex.I) (pairing x) =
        PontryaginDual.map (axis Complex.I) χ := by
      rw [himag, show -(2 * x.toAdd.im) = b by change -(2 * -(b / 2)) = b; ring]
      exact eR.apply_symm_apply _
    refine ⟨x, PontryaginDual.ext fun y ↦ ?_⟩
    have hy : y = axis 1 (Multiplicative.ofAdd y.toAdd.re) *
        axis Complex.I (Multiplicative.ofAdd y.toAdd.im) := by
      change y.toAdd = y.toAdd.re • (1 : ℂ) + y.toAdd.im • Complex.I
      apply Complex.ext <;> simp
    rw [hy, map_mul, map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hre _) (DFunLike.congr_fun him _)
  let equiv := MulEquiv.ofBijective pairing ⟨hinj, hsurj⟩
  exact ⟨{ equiv with
    continuous_toFun := hpcont
    continuous_invFun := (Equiv.continuous_symm_iff equiv.toEquiv).mpr
      (pairing.isOpenMap_of_sigmaCompact hsurj hpcont) }, fun _ _ ↦ rfl⟩

open scoped FourierTransform in
/-- Paper: Example A.3.1.5, p. 557. Twice plane Lebesgue measure is self-dual
for the complex character with phase `4π Re(z)`. -/
theorem complexTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (2 • (volume : Measure ℂ)) (fun z ↦ Circle.exp (4 * Real.pi * z.re)) := by
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞]
  norm_num only [Nat.cast_ofNat]
  obtain ⟨e, he⟩ := exists_complexTamagawaDualEquiv
  refine ⟨e, he, ?_⟩
  let μ : Measure (Multiplicative ℂ) := (2 : ℝ≥0∞) • (volume : Measure ℂ)
  let : MeasurableSpace (PontryaginDual (Multiplicative ℂ)) := borel _
  let : BorelSpace (PontryaginDual (Multiplicative ℂ)) := ⟨rfl⟩
  have hvol : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hvol.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hvol.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hvol.map_add_left_eq_self x.toAdd }
  let : μ.Regular := Measure.Regular.smul (μ := (volume : Measure ℂ)) (by norm_num)
  change IsLCAPlancherelMeasure (G := Multiplicative ℂ) μ (Measure.map e μ)
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  let g : ℂ → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
  -- The trace pairing is the Euclidean pairing with the frequency doubled and conjugated.
  let T : ℂ ≃ₜ ℂ :=
    (Units.mk0 (2 : ℝ) two_ne_zero • Complex.conjCLE).toHomeomorph
  have hT (y : ℂ) : T y = (2 : ℝ) • star y := rfl
  have hmap : Measure.map T (volume : Measure ℂ) = (4 : ℝ≥0∞)⁻¹ • volume := by
    change Measure.map ((fun z : ℂ ↦ (2 : ℝ) • z) ∘ Complex.conjLIE) volume = _
    rw [← Measure.map_map (by fun_prop) Complex.conjLIE.measurePreserving.measurable,
      Complex.conjLIE.measurePreserving.map_eq, Measure.map_addHaar_smul _ two_ne_zero,
      Complex.finrank_real_complex]
    rw [show |((2 : ℝ) ^ (2 : ℕ))⁻¹| = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hFourier : lcaFourier μ f ∘ e = (2 : ℝ) • ((𝓕 g) ∘ T) := by
    funext y
    change lcaFourier μ f (e y) = (2 : ℝ) • 𝓕 g (T y.toAdd)
    rw [lcaFourier, Real.fourier_eq]
    change (∫ x : ℂ, g x * star (e y (Multiplicative.ofAdd x) : ℂ)
      ∂((2 : ℝ≥0∞) • (volume : Measure ℂ))) = _
    rw [integral_smul_measure]
    norm_num only [ENNReal.toReal_ofNat]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    have hPair : e y (Multiplicative.ofAdd x) = Real.fourierChar (inner ℝ x (T y.toAdd)) := by
      change e (Multiplicative.ofAdd y.toAdd) (Multiplicative.ofAdd x) = _
      rw [he, Real.fourierChar_apply', hT, real_inner_smul_right]
      have hInner : inner ℝ x (star y.toAdd) = (y.toAdd * x).re := by
        change (star y.toAdd * star x).re = _
        rw [← star_mul, mul_comm x y.toAdd]
        exact Complex.conj_re _
      rw [hInner]
      apply congrArg Circle.exp
      ring
    rw [hPair, Circle.star_addChar, Circle.smul_def, smul_eq_mul, mul_comm]
  have hle : (volume : Measure ℂ) ≤ (2 : ℝ≥0∞) • volume := by
    rw [two_smul]
    exact Measure.le_add_right le_rfl
  have h := memLp_two_fourier_and_eLpNorm_eq (f := g) (Integrable.mono_measure hf₁ hle)
    (MemLp.mono_measure hle hf₂)
  have hTEmb := T.measurableEmbedding
  have hLp : MemLp ((2 : ℝ) • ((𝓕 g) ∘ T)) 2 (volume : Measure ℂ) := by
    apply MemLp.const_smul
    apply hTEmb.memLp_map_measure_iff.mp
    rw [hmap]
    exact h.1.smul_measure (by norm_num)
  -- The Jacobian contributes a factor of one half to the L² norm.
  have hNorm : eLpNorm ((2 : ℝ) • ((𝓕 g) ∘ T)) 2 (volume : Measure ℂ) =
      eLpNorm g 2 volume := by
    rw [eLpNorm_const_smul, ← hTEmb.eLpNorm_map_measure, hmap,
      eLpNorm_smul_measure_of_ne_zero (by norm_num), h.2]
    rw [show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) by norm_num [← ofReal_norm]]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    rw [ENNReal.inv_rpow, show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℝ) by
      rw [ENNReal.rpow_ofNat]; norm_num]
    rw [ENNReal.rpow_rpow_inv two_ne_zero, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hEmb := e.toHomeomorph.measurableEmbedding
  refine ⟨hEmb.memLp_map_measure_iff.mpr (hFourier ▸ hLp.smul_measure (by norm_num)), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ e) 2 μ := hEmb.eLpNorm_map_measure
    _ = eLpNorm g 2 ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := ?_
  rw [hFourier]
  change eLpNorm ((2 : ℝ) • ((𝓕 g) ∘ T)) 2 ((2 : ℝ≥0∞) • (volume : Measure ℂ)) =
    eLpNorm g 2 ((2 : ℝ≥0∞) • (volume : Measure ℂ))
  simp only [eLpNorm_smul_measure_of_ne_zero (by norm_num : (2 : ℝ≥0∞) ≠ 0), hNorm]

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance instPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Paper: Example A.3.1.6, p. 557. Multiplying by the power of p that clears
the negative valuation places the result in the p-adic integer ring. -/
theorem padicStandardCharacter_integral (x : ℚ_[p]) :
    ‖(p : ℚ_[p]) ^ (-x.valuation).toNat * x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀]
  · apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : p.Prime).one_lt.le
    · have := Int.self_le_toNat (-x.valuation)
      omega
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Paper: Example A.3.1.6, p. 557. The standard character exponentiates
the rational representative of the coset modulo the p-adic integers.
The representative uses the residue of the cleared integer modulo the clearing power.
Deviation: the sign is opposite to the printed `exp(2πit)`. With the printed sign at the real
place (Example A.3.1.5) and at the p-adic places, the product character of Example A.3.1.8 takes
the value `exp(4πi/3)` on the rational number 1/3. It must be trivial on the rationals for
Theorem 2.2.3.2 and Theorem 3.2.2.1, as in Tate's thesis, where the two kinds of place carry
opposite signs. The real character keeps the printed sign. -/
def padicStandardCharacter (x : ℚ_[p]) : Circle :=
  let n := (-x.valuation).toNat
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, padicStandardCharacter_integral p x⟩
  Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n))

/-- Paper: Example A.3.1.6, p. 557. On a fraction with denominator a power of p,
the p-adic character has the phase opposite to the real exponential of that fraction.
Deviation: the sign, as in `padicStandardCharacter`. -/
theorem padicStandardCharacter_div_pow (a : ℤ) (n : ℕ) :
    padicStandardCharacter p ((a : ℚ_[p]) / (p : ℚ_[p]) ^ n) =
      Circle.exp (-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ n))) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set x : ℚ_[p] := (a : ℚ_[p]) / (p : ℚ_[p]) ^ n with hx
  set m := (-x.valuation).toNat with hm
  -- The cleared element `p ^ m * x` is an integer `b` with `b / p ^ m = a / p ^ n`.
  obtain ⟨b, hb, hbR⟩ : ∃ b : ℤ, (p : ℚ_[p]) ^ m * x = b ∧
      (b : ℝ) / (p : ℝ) ^ m = (a : ℝ) / (p : ℝ) ^ n := by
    rcases le_or_gt n m with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      refine ⟨a * p ^ k, ?_, ?_⟩
      · rw [hx, hk, pow_add]
        push_cast
        field_simp
      · rw [hk, pow_add]
        push_cast
        field_simp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h.le
      have hint := padicStandardCharacter_integral p x
      have hxk : (p : ℚ_[p]) ^ m * x = (a : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
        rw [hx, hk, pow_add]
        field_simp
      rw [← hm, hxk, norm_div, div_le_one (norm_pos_iff.mpr (pow_ne_zero _ hp0)), Padic.norm_p_pow] at hint
      obtain ⟨c, rfl⟩ := (Padic.norm_int_le_pow_iff_dvd a k).mp hint
      refine ⟨c, ?_, ?_⟩
      · rw [hxk]
        push_cast
        field_simp
      · rw [hk, pow_add]
        push_cast
        field_simp
  have hA : (⟨(p : ℚ_[p]) ^ m * x, padicStandardCharacter_integral p x⟩ : ℤ_[p]) = (b : ℤ_[p]) :=
    Subtype.ext (by
      change (p : ℚ_[p]) ^ m * x = ((b : ℤ_[p]) : ℚ_[p])
      rw [hb]
      simp)
  have hval : (((PadicInt.toZModPow m (b : ℤ_[p])).val : ℕ) : ℝ) = ((b % (p ^ m : ℕ) : ℤ) : ℝ) := by
    rw [map_intCast]
    have := NeZero.of_pos (pow_pos (Fact.out : p.Prime).pos m)
    exact_mod_cast ZMod.val_intCast (n := p ^ m) b
  have hdiv := Int.emod_add_mul_ediv b (p ^ m : ℕ)
  change Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow m
    (⟨(p : ℚ_[p]) ^ m * x, padicStandardCharacter_integral p x⟩ : ℤ_[p])).val : ℝ) /
      (p : ℝ) ^ m)) = _
  rw [hA, hval, Circle.exp_eq_exp]
  refine ⟨b / (p ^ m : ℕ), ?_⟩
  rw [← hbR]
  have hdivR : ((b % (p ^ m : ℕ) : ℤ) : ℝ) = b - (p : ℝ) ^ m * ((b / (p ^ m : ℕ) : ℤ) : ℝ) := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast hdiv
  rw [hdivR]
  field_simp
  ring

local notation "ℤₚ" => Metric.closedBall (0 : ℚ_[p]) 1

/-- Paper: Example A.3.1.7, p. 557. The standard additive measure on the
p-adic field is Haar measure with the integer ring assigned volume one. -/
theorem padicTamagawaMeasure_existsUnique :
    ∃! μ : Measure ℚ_[p], μ.IsAddHaarMeasure ∧ μ.Regular ∧ μ (ℤₚ) = 1 := by
  let K : TopologicalSpace.PositiveCompacts ℚ_[p] :=
    ⟨⟨ℤₚ, isCompact_closedBall _ _⟩,
      ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)⟩⟩
  refine ⟨Measure.addHaarMeasure K,
    ⟨inferInstance, inferInstance, Measure.addHaarMeasure_self⟩, ?_⟩
  rintro μ ⟨hhaar, -, hμ⟩
  let : μ.IsAddHaarMeasure := hhaar
  exact ((Measure.addHaarMeasure_eq_iff K μ).2 hμ).symm

/-- Paper: Example A.3.1.7, p. 557. Use the unique regular additive Haar
measure on the p-adic field for which the integer ring has mass one. -/
def padicTamagawaMeasure : Measure ℚ_[p] :=
  (padicTamagawaMeasure_existsUnique p).exists.choose

/-- The phase defining the standard character can be computed with any clearing power. -/
private theorem padicStandardCharacter_of_clear (x : ℚ_[p]) (m : ℕ)
    (h : ‖(p : ℚ_[p]) ^ m * x‖ ≤ 1) :
    let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    padicStandardCharacter p x =
      (ZMod.toCircle (PadicInt.toZModPow m ⟨_, h⟩))⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hp).ne'
  let k := (-x.valuation).toNat
  have hkm : k ≤ m := by
    by_cases hx : x = 0
    · simp [k, hx, Padic.valuation_zero]
    · rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀ hp0,
        ← zpow_zero (p : ℝ), zpow_le_zpow_iff_right₀ hp] at h
      dsimp [k]
      omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let : NeZero (p ^ (k + d)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let a : ℤ_[p] := ⟨_, padicStandardCharacter_integral p x⟩
  let r := (PadicInt.toZModPow k a).val
  -- An extra clearing factor multiplies both the residue representative and the modulus.
  have hr : a - (r : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast]
    simp [r]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hr
  have hscaled : (⟨_, h⟩ : ℤ_[p]) = (p : ℤ_[p]) ^ d * a := by
    ext
    change (p : ℚ_[p]) ^ (k + d) * x = _
    push_cast
    change _ = (p : ℚ_[p]) ^ d * ((p : ℚ_[p]) ^ k * x)
    rw [pow_add, mul_comm ((p : ℚ_[p]) ^ k), mul_assoc]
  have hres : PadicInt.toZModPow (k + d) (⟨_, h⟩ : ℤ_[p]) = (p ^ d * r : ℕ) := by
    rw [hscaled, ← sub_eq_zero, ← map_natCast (PadicInt.toZModPow (k + d)),
      ← map_sub (PadicInt.toZModPow (k + d)), ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    refine ⟨b, ?_⟩
    push_cast
    rw [← mul_sub, hb, pow_add]
    ac_rfl
  have hlt : p ^ d * r < p ^ (k + d) := by
    rw [pow_add, mul_comm (p ^ k)]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (pow_pos (Fact.out : p.Prime).pos _)
  change Circle.exp (-(2 * Real.pi * (r : ℝ) / (p : ℝ) ^ k)) = _
  rw [ZMod.toCircle_eq_circleExp, ← Circle.exp_neg, hres, ZMod.val_natCast_of_lt hlt]
  congr 2
  push_cast
  rw [pow_add]
  field_simp

/-- The standard character is multiplicative on sums of p-adic numbers. -/
private theorem padicStandardCharacter_add (x y : ℚ_[p]) :
    padicStandardCharacter p (x + y) =
      padicStandardCharacter p x * padicStandardCharacter p y := by
  let m := max (-x.valuation).toNat (-y.valuation).toNat
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have clearPower (z : ℚ_[p]) (hz : (-z.valuation).toNat ≤ m) :
      ‖(p : ℚ_[p]) ^ m * z‖ ≤ 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hz
    rw [hd, pow_add, mul_comm ((p : ℚ_[p]) ^ (-z.valuation).toNat), mul_assoc, norm_mul,
      Padic.norm_p_pow]
    exact (mul_le_mul_of_nonneg_right (zpow_le_one_of_nonpos₀ hp.le (by omega))
      (norm_nonneg _)).trans (by simpa only [one_mul] using padicStandardCharacter_integral p z)
  have hx := clearPower x (le_max_left _ _)
  have hy := clearPower y (le_max_right _ _)
  have hxy : ‖(p : ℚ_[p]) ^ m * (x + y)‖ ≤ 1 := by
    rw [mul_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [padicStandardCharacter_of_clear p _ m hxy, padicStandardCharacter_of_clear p _ m hx,
    padicStandardCharacter_of_clear p _ m hy]
  let a : ℤ_[p] := ⟨_, hx⟩
  let b : ℤ_[p] := ⟨_, hy⟩
  have hsum : (⟨_, hxy⟩ : ℤ_[p]) = a + b := Subtype.ext (mul_add ..)
  change (ZMod.toCircle (PadicInt.toZModPow m ⟨_, hxy⟩))⁻¹ =
    (ZMod.toCircle (PadicInt.toZModPow m a))⁻¹ * (ZMod.toCircle (PadicInt.toZModPow m b))⁻¹
  rw [hsum, map_add, AddChar.map_add_eq_mul, mul_inv]

/-- The kernel of the standard character is precisely the unit ball. -/
private theorem padicStandardCharacter_eq_one_iff (x : ℚ_[p]) :
    padicStandardCharacter p x = 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    let m := (-x.valuation).toNat
    let a : ℤ_[p] := ⟨_, padicStandardCharacter_integral p x⟩
    let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [padicStandardCharacter_of_clear p _ m a.property] at h
    change (ZMod.toCircle (PadicInt.toZModPow m a))⁻¹ = 1 at h
    rw [inv_eq_one, ← (ZMod.toCircle (N := p ^ m)).map_zero_eq_one,
      ZMod.injective_toCircle.eq_iff] at h
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    have hval : (p : ℚ_[p]) ^ m * x = (p : ℚ_[p]) ^ m * (b : ℚ_[p]) := by
      exact congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hb
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [mul_right_inj' (pow_ne_zero _ hp0)] at hval
    exact hval ▸ b.property
  · intro h
    have hx : ‖(p : ℚ_[p]) ^ (0 : ℕ) * x‖ ≤ 1 := by simpa using h
    rw [padicStandardCharacter_of_clear p _ 0 hx]
    have hz : PadicInt.toZModPow 0 (⟨_, hx⟩ : ℤ_[p]) = 0 := by
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    rw [hz, AddChar.map_zero_eq_one, inv_one]

/-- The `p` residue classes in the integer ball have equal Haar mass. -/
private theorem padicTamagawaMeasure_mul_prime :
    padicTamagawaMeasure p (((p : ℚ_[p]) * ·) '' ℤₚ) = (p : ℝ≥0∞)⁻¹ := by
  let μ := padicTamagawaMeasure p
  obtain ⟨hμ, -, hmass⟩ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  change μ.IsAddHaarMeasure at hμ
  change μ ℤₚ = 1 at hmass
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let B (i : Fin p) := Metric.closedBall (i.val : ℚ_[p]) (p : ℝ)⁻¹
  have hsubset (i : Fin p) : B i ⊆ ℤₚ := by
    intro x hx
    have hnorm : ‖x - (i.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
      simpa only [B, Metric.mem_closedBall, dist_eq_norm] using hx
    have hi : ‖(i.val : ℚ_[p])‖ ≤ 1 := (i.val : ℤ_[p]).property
    rw [Metric.mem_closedBall, dist_zero_right, ← sub_add_cancel x (i.val : ℚ_[p])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hnorm.trans (inv_le_one_of_one_le₀ hp.le)) hi)
  have hrepr (x : ℤ_[p]) (i : Fin p) :
      (x : ℚ_[p]) ∈ B i ↔ x.zmodRepr = i.val := by
    change dist (x : ℚ_[p]) _ ≤ _ ↔ _
    rw [dist_eq_norm]
    have hnorm : ‖(x : ℚ_[p]) - (i.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ↔
        x - (i.val : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      simpa [PadicInt.norm_def] using
        ((x - (i.val : ℤ_[p])).norm_le_pow_iff_mem_span_pow 1)
    rw [hnorm]
    exact ⟨fun h ↦ x.zmodRepr_unique _ i.isLt h,
      fun h ↦ h ▸ x.sub_zmodRepr_mem⟩
  have hcover : (⋃ i, B i) = ℤₚ := by
    refine Set.Subset.antisymm (Set.iUnion_subset hsubset) ?_
    intro x hx
    let z : ℤ_[p] := ⟨x, by
      change ‖x‖ ≤ 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx⟩
    exact Set.mem_iUnion.mpr ⟨⟨z.zmodRepr, z.zmodRepr_lt_p⟩, (hrepr z _).mpr rfl⟩
  have hdisjoint : Pairwise (Disjoint on B) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj ↦ hij (Fin.ext ?_)
    let z : ℤ_[p] := ⟨x, by
      change ‖x‖ ≤ 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hsubset i hi⟩
    exact ((hrepr z i).mp hi).symm.trans ((hrepr z j).mp hj)
  have hball (i : Fin p) : μ (B i) = μ (((p : ℚ_[p]) * ·) '' ℤₚ) := by
    change μ (B i) = μ (((p : ℚ_[p]) • ·) '' ℤₚ)
    rw [Metric.smul_image_closedBall hp0, smul_zero, mul_one, Padic.norm_p]
    exact Measure.addHaar_closedBall_center μ _ _
  have hsum := measure_iUnion (μ := μ) hdisjoint
    (fun i ↦ (Metric.isClosed_closedBall : IsClosed (B i)).measurableSet)
  rw [hcover, hmass, tsum_fintype] at hsum
  simp only [hball, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpn : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← ENNReal.mul_inv_cancel hpn hpt, ENNReal.mul_right_inj hpn hpt] at hsum
  exact hsum.symm

/-- Multiplication by a power of p scales the Haar mass of the integer ball by its norm. -/
private theorem padicTamagawaMeasure_scaledIntegers_real (n : ℤ) :
    (padicTamagawaMeasure p).real (((p : ℚ_[p]) ^ n * ·) '' ℤₚ) = (p : ℝ) ^ (-n) := by
  let μ := padicTamagawaMeasure p
  obtain ⟨hμ, hreg, hmass⟩ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  change μ.IsAddHaarMeasure at hμ
  change μ.Regular at hreg
  change μ ℤₚ = 1 at hmass
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let u := Units.mk0 (p : ℚ_[p]) hp0
  have hu (j : ℤ) :
      u ^ j • ℤₚ = (((p : ℚ_[p]) ^ j * ·) '' ℤₚ) := by
    change ((fun x : ℚ_[p] ↦ (↑(u ^ j) : ℚ_[p]) * x) '' ℤₚ) = _
    simp [u]
  have hprime : μ (u • ℤₚ) = (p : ℝ≥0∞)⁻¹ := by
    have h := hu 1
    simp only [zpow_one] at h
    rw [h]
    exact padicTamagawaMeasure_mul_prime p
  have hpN : (p : ℝ≥0) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hchar : distribHaarChar ℚ_[p] u = (p : ℝ≥0)⁻¹ := by
    apply ENNReal.coe_injective
    have h := distribHaarChar_mul μ u ℤₚ
    rw [hmass, mul_one, hprime] at h
    simpa [ENNReal.coe_inv hpN] using h
  have h := distribHaarChar_mul μ (u ^ n) ℤₚ
  rw [hmass, mul_one, map_zpow, hchar, hu] at h
  rw [measureReal_def, ← h, ENNReal.coe_toReal, NNReal.coe_zpow, NNReal.coe_inv,
    NNReal.coe_natCast, inv_zpow, zpow_neg]

-- TODO(paper-gap): In (A.3.1.5) the scaling step inserts an incorrect frequency
-- shift, and the translation phase needs conjugation under (D.1.1.4).
-- The zero-translation specialization and the unit formula are unaffected.

/-- Paper: Example A.3.1.6, p. 557. The Fourier transform of the indicator of
the scaled p-adic integer ring is the reciprocal-scale indicator times the scaling factor.
Deviation: This is the valid zero-translation specialization of (A.3.1.5). -/
theorem padicTamagawaFourier_scaledIntegers (n : ℤ) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ((((p : ℚ_[p]) ^ n * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
      ((p : ℝ) ^ (-n) : ℂ) • ((((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
  let μ := padicTamagawaMeasure p
  have hμ : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let a := (p : ℚ_[p]) ^ n
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha : a ≠ 0 := zpow_ne_zero _ hp0
  let H := ((PadicInt.subring p).toAddSubgroup).map (AddMonoidHom.mulLeft a)
  let s := (a * ·) '' ℤₚ
  have hs : (H : Set ℚ_[p]) = s := by
    change (a * ·) '' {x : ℚ_[p] | ‖x‖ ≤ 1} = _
    simp only [s, Metric.closedBall, dist_zero_right]
  have haH : a ∈ H := by
    refine AddSubgroup.mem_map.mpr ⟨1, (PadicInt.subring p).one_mem, ?_⟩
    exact mul_one a
  have hsmeas : MeasurableSet s := by
    change MeasurableSet ((a • ·) '' ℤₚ)
    rw [Metric.smul_image_closedBall ha]
    exact Metric.isClosed_closedBall.measurableSet
  funext y
  let f (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x * y) : ℂ)
  let g := s.indicator f
  change (∫ x, s.indicator (fun _ ↦ (1 : ℂ)) x * f x ∂μ) =
    ((p : ℝ) ^ (-n) : ℂ) * (((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ).indicator (fun _ ↦ 1) y
  simp_rw [← Set.indicator_mul_left, one_mul]
  have hymem : y ∈ (((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ) ↔ ‖a * y‖ ≤ 1 := by
    rw [zpow_neg]
    change y ∈ a⁻¹ • ℤₚ ↔ _
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha), inv_inv]
    simp only [smul_eq_mul, Metric.mem_closedBall, dist_zero_right]
  by_cases hy : y ∈ (((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ)
  · rw [Set.indicator_of_mem hy, mul_one, integral_indicator hsmeas]
    calc
      (∫ x in s, f x ∂μ) = ∫ _ in s, (1 : ℂ) ∂μ := by
        refine setIntegral_congr_fun hsmeas ?_
        rintro _ ⟨z, hz, rfl⟩
        have hz' : ‖z‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hz
        have hzy : ‖a * z * y‖ ≤ 1 := by
          rw [show a * z * y = z * (a * y) by ac_rfl, norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) hz').trans (hymem.mp hy)
        simp [f, (padicStandardCharacter_eq_one_iff p _).mpr hzy]
      _ = ((p : ℝ) ^ (-n) : ℂ) := by
        rw [setIntegral_const, Complex.real_smul, mul_one]
        have h := congrArg Complex.ofReal (padicTamagawaMeasure_scaledIntegers_real p n)
        simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast] using h
  · -- Translation by `a ∈ p ^ n ℤₚ` leaves the integral invariant and multiplies it by `f a`.
    rw [Set.indicator_of_notMem hy, mul_zero]
    change (∫ x, g x ∂μ) = 0
    have hne : f a ≠ 1 := by
      intro h
      apply hy
      apply hymem.mpr
      apply (padicStandardCharacter_eq_one_iff p _).mp
      exact Subtype.ext (by simpa [f] using congrArg star h)
    have htranslate (x : ℚ_[p]) : g (a + x) = f a * g x := by
      have hmem : a + x ∈ s ↔ x ∈ s := by
        rw [← hs]
        exact H.add_mem_cancel_left haH
      by_cases hx : x ∈ s
      · simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx), f,
          add_mul, padicStandardCharacter_add, Circle.coe_mul, star_mul']
      · rw [show g (a + x) = 0 from Set.indicator_of_notMem (mt hmem.mp hx) _,
          show g x = 0 from Set.indicator_of_notMem hx _, mul_zero]
    have h : f a * (∫ x, g x ∂μ) = 1 * (∫ x, g x ∂μ) := by
      rw [one_mul, ← integral_const_mul, ← integral_add_left_eq_self (μ := μ) g a]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (htranslate x).symm)
    exact (mul_eq_mul_right_iff.mp h).resolve_left hne

/-- The defining phase with the clearing exponent and its integrality proof supplied explicitly. -/
private theorem padicStandardCharacter_eq_exp_of_clearingPower (x : ℚ_[p]) (n : ℕ) (hn : (-x.valuation).toNat = n)
    (hx : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    padicStandardCharacter p x =
      Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n
        (⟨(p : ℚ_[p]) ^ n * x, hx⟩ : ℤ_[p])).val : ℝ) / (p : ℝ) ^ n)) := by
  subst n
  rfl

/-- The standard character is trivial on the p-adic integers. -/
private theorem padicStandardCharacter_eq_one_of_norm_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    padicStandardCharacter p x = 1 := by
  have hn : (-x.valuation).toNat = 0 := by
    have := (Padic.norm_le_one_iff_val_nonneg x).mp hx
    omega
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ (0 : ℕ) * x, by
    change ‖(p : ℚ_[p]) ^ (0 : ℕ) * x‖ ≤ 1
    simpa using hx⟩
  rw [padicStandardCharacter_eq_exp_of_clearingPower p x 0 hn a.property]
  change Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow 0 a).val : ℝ) / (p : ℝ) ^ (0 : ℕ))) = 1
  have : Subsingleton (ZMod (p ^ (0 : ℕ))) := by
    simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
  have hzero (a : ℤ_[p]) : (PadicInt.toZModPow 0 a).val = 0 := by
    have heq : PadicInt.toZModPow 0 a = 0 := Subsingleton.elim _ _
    exact (congrArg ZMod.val heq).trans ZMod.val_zero
  simp only [hzero, Nat.cast_zero, mul_zero, zero_div, neg_zero, Circle.exp_zero]

/-- Adding an integral element preserves the clearing residue of a nonintegral element,
and hence preserves the character. -/
private theorem padicStandardCharacter_add_of_norm_le_one (x z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    padicStandardCharacter p (x + z) = padicStandardCharacter p x := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [padicStandardCharacter_eq_one_of_norm_le_one p hx, padicStandardCharacter_eq_one_of_norm_le_one p ((Padic.nonarchimedean x z).trans (max_le hx hz))]
  have hnorm : ‖x + z‖ = ‖x‖ := by
    have hlt := hz.trans_lt (lt_of_not_ge hx)
    rw [Padic.add_eq_max_of_ne hlt.ne', max_eq_left hlt.le]
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  have hxz0 : x + z ≠ 0 := by
    intro h
    have := norm_pos_iff.mpr hx0
    rw [← hnorm, h, norm_zero] at this
    exact (lt_irrefl _ this)
  have hval : (x + z).valuation = x.valuation := by
    rw [Padic.norm_eq_zpow_neg_valuation hxz0, Padic.norm_eq_zpow_neg_valuation hx0,
      (zpow_right_strictMono₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt : (1 : ℝ) < p)).injective.eq_iff,
      neg_inj] at hnorm
    exact hnorm
  let n := (-x.valuation).toNat
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, padicStandardCharacter_integral p x⟩
  let b : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * (x + z), by
    change ‖(p : ℚ_[p]) ^ n * (x + z)‖ ≤ 1
    simpa only [hval] using padicStandardCharacter_integral p (x + z)⟩
  let c : ℤ_[p] := ⟨z, hz⟩
  have hb : b = a + (p : ℤ_[p]) ^ n * c := by
    apply Subtype.ext
    change (p : ℚ_[p]) ^ n * (x + z) = _
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    exact mul_add _ _ _
  have hc : PadicInt.toZModPow n ((p : ℤ_[p]) ^ n * c) = 0 := by
    change (p : ℤ_[p]) ^ n * c ∈ RingHom.ker (PadicInt.toZModPow n)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hres : PadicInt.toZModPow n b = PadicInt.toZModPow n a := by
    rw [hb, map_add, hc, add_zero]
  rw [padicStandardCharacter_eq_exp_of_clearingPower p (x + z) n (by rw [hval]) b.property,
    padicStandardCharacter_eq_exp_of_clearingPower p x n rfl a.property]
  change Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n b).val : ℝ) / (p : ℝ) ^ n)) =
    Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n))
  rw [hres]

/-- The standard character is locally constant on translates of the p-adic integers. -/
private theorem padicStandardCharacter_continuous : Continuous (padicStandardCharacter p) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ Metric.continuousAt_iff.mpr ?_
  intro ε hε
  refine ⟨1, zero_lt_one, fun {y} hy ↦ ?_⟩
  rw [dist_eq_norm] at hy
  have h := padicStandardCharacter_add_of_norm_le_one p x (y - x) hy.le
  rw [add_comm x, sub_add_cancel] at h
  simpa [h]

/-- The inverse of p has a nontrivial standard character value. -/
private theorem padicStandardCharacter_inv_prime_ne_one :
    padicStandardCharacter p ((p : ℚ_[p])⁻¹) ≠ 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hphase : padicStandardCharacter p ((p : ℚ_[p])⁻¹) =
      Circle.exp (-(2 * Real.pi * (p : ℝ)⁻¹)) := by
    simpa [one_div] using padicStandardCharacter_div_pow p 1 1
  rw [hphase]
  intro h
  obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp h
  have heq : -((p : ℝ)⁻¹) = (k : ℝ) := by
    apply mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
    nlinarith only [hk]
  have hlo : (-1 : ℝ) < (k : ℝ) := by
    rw [← heq]
    linarith [inv_lt_one_of_one_lt₀ hp]
  have hhi : (k : ℝ) < 0 := by
    rw [← heq]
    exact neg_lt_zero.mpr (inv_pos.mpr (zero_lt_one.trans hp))
  have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hhi' : k < 0 := by exact_mod_cast hhi
  omega

/-- Scaling the p-adic integer ring by a nonzero scalar gives the closed ball
with radius equal to the norm of that scalar. -/
private theorem padicScaledIntegers_eq_closedBall (c : ℚ_[p]) (hc : c ≠ 0) :
    (c * ·) '' ℤₚ = Metric.closedBall 0 ‖c‖ := by
  have hnorm (x : ℚ_[p]) : x ∈ ℤₚ ↔ ‖c * x‖ ≤ ‖c‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, mul_le_iff_le_one_right (norm_pos_iff.mpr hc)]
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hnorm z).mp hz
  · intro hx
    have heq : c * (x / c) = x := by rw [mul_comm, div_mul_cancel₀ _ hc]
    exact ⟨x / c, (hnorm _).mpr (by rw [heq]; exact hx), heq⟩

/-- The multiples of p in the p-adic integer ring form the open unit ball. -/
private theorem padicPrimeMulIntegers_eq_ball (hp : (p : ℚ_[p]) ≠ 0) :
    ((p : ℚ_[p]) * ·) '' ℤₚ = Metric.ball 0 1 := by
  rw [padicScaledIntegers_eq_closedBall p _ hp, Padic.norm_p]
  ext x
  simpa only [Metric.mem_ball, dist_zero_right, mem_closedBall_zero_iff, zpow_zero, zero_sub,
    zpow_neg_one] using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x 0).symm

/-- The open unit ball has Tamagawa mass 1/p because it is the kernel of
reduction of the integer ring modulo p. -/
private theorem padicTamagawaMeasure_real_primeMulIntegers (hp : (p : ℚ_[p]) ≠ 0) :
    (padicTamagawaMeasure p).real (((p : ℚ_[p]) * ·) '' ℤₚ) = (p : ℝ)⁻¹ := by
  let μ := padicTamagawaMeasure p
  have hμ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  have : μ.IsAddHaarMeasure := hμ.1
  let : MeasurableSpace ℤ_[p] := MeasurableSpace.comap (fun x : ℤ_[p] ↦ (x : ℚ_[p])) inferInstance
  have : BorelSpace ℤ_[p] := ⟨borel_comap.symm⟩
  let e : ℤ_[p] →+ ℚ_[p] :=
    { toFun := fun x ↦ (x : ℚ_[p])
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have he : MeasurableEmbedding e := by
    change MeasurableEmbedding (Subtype.val : (PadicInt.subring p) → ℚ_[p])
    exact MeasurableEmbedding.subtype_coe (by
      change MeasurableSet {x : ℚ_[p] | ‖x‖ ≤ 1}
      exact isClosed_le continuous_norm continuous_const |>.measurableSet)
  have : (μ.comap e).IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ he
  let f : ℤ_[p] →+ ZMod p := PadicInt.toZMod.toAddMonoidHom
  have hf : Surjective f := fun a ↦ ⟨(a.val : ℤ_[p]), by
    change PadicInt.toZMod (a.val : ℤ_[p]) = a
    rw [map_natCast, ZMod.natCast_zmod_val]⟩
  have hindex : f.ker.index = p := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf, AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]
  have : f.ker.FiniteIndex := ⟨hindex.trans_ne (Fact.out : p.Prime).ne_zero⟩
  have hker (a : ℤ_[p]) : a ∈ f.ker ↔ ‖a‖ < 1 := by
    change a ∈ RingHom.ker PadicInt.toZMod ↔ _
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      PadicInt.norm_lt_one_iff_dvd]
  have hmeas : MeasurableSet (f.ker : Set ℤ_[p]) := by
    have heq : (f.ker : Set ℤ_[p]) = {a | ‖a‖ < 1} := by
      ext a
      exact hker a
    rw [heq]
    exact (isOpen_lt continuous_norm continuous_const).measurableSet
  have himage : e '' (f.ker : Set ℤ_[p]) = ((p : ℚ_[p]) * ·) '' ℤₚ := by
    rw [padicPrimeMulIntegers_eq_ball p hp]
    ext x
    rw [Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hker a).mp ha
    · intro hx
      exact ⟨⟨x, hx.le⟩, (hker _).mpr hx, rfl⟩
  have hrange : Set.range e = ℤₚ := by
    ext x
    rw [mem_closedBall_zero_iff]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.norm_le_one, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hone : μ ℤₚ = 1 := hμ.2.2
  have hm := f.ker.index_mul_measure hmeas (μ.comap e)
  rw [hindex, he.comap_apply, he.comap_apply, himage, Set.image_univ, hrange, hone] at hm
  have hm' := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hm'
  change (μ (((p : ℚ_[p]) * ·) '' ℤₚ)).toReal = _
  rw [← one_div, eq_div_iff (by exact_mod_cast (Fact.out : p.Prime).ne_zero), mul_comm]
  exact hm'

/-- The transform of the indicator of a scaled p-adic integer ball is its mass
times the indicator of the reciprocal ball. -/
private theorem padicTamagawaFourier_scaledIntegers_eq_measure (c : ℚ_[p]) (hc : c ≠ 0) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
      (((c * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
    ((padicTamagawaMeasure p).real ((c * ·) '' ℤₚ) : ℂ) •
      (((c⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
  let μ := padicTamagawaMeasure p
  have : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let B := Metric.closedBall (0 : ℚ_[p]) ‖c‖
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  rw [padicScaledIntegers_eq_closedBall p c hc, padicScaledIntegers_eq_closedBall p c⁻¹ (inv_ne_zero hc)]
  funext y
  let g (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x * y) : ℂ)
  change (∫ x, B.indicator (fun _ ↦ (1 : ℂ)) x * g x ∂μ) = _
  simp only [← Set.indicator_mul_left, one_mul, integral_indicator hB]
  have hy : y ∈ Metric.closedBall (0 : ℚ_[p]) ‖c⁻¹‖ ↔ ‖y‖ * ‖c‖ ≤ 1 := by
    rw [mem_closedBall_zero_iff, norm_inv, ← one_div, le_div_iff₀ (norm_pos_iff.mpr hc)]
  by_cases hyc : y ∈ Metric.closedBall (0 : ℚ_[p]) ‖c⁻¹‖
  · have hg : EqOn g (fun _ ↦ (1 : ℂ)) B := fun x hx ↦ by
      have hx' : ‖x‖ ≤ ‖c‖ := mem_closedBall_zero_iff.mp hx
      have hnorm : ‖x * y‖ ≤ 1 := by
        rw [norm_mul, mul_comm]
        exact (mul_le_mul_of_nonneg_left hx' (norm_nonneg _)).trans (hy.mp hyc)
      simp [g, padicStandardCharacter_eq_one_of_norm_le_one p hnorm]
    rw [setIntegral_congr_fun hB hg]
    rw [Pi.smul_apply, indicator_of_mem hyc]
    simp [Complex.real_smul, B, μ]
  · have hy' := lt_of_not_ge (mt hy.mpr hyc)
    have hy0 : y ≠ 0 := by
      intro h
      exact (not_lt_of_ge (by simp [h])) hy'
    have hge : (p : ℝ) ≤ ‖y‖ * ‖c‖ := by
      by_contra! h
      have hlt : ‖y * c‖ < (p : ℝ) ^ (1 : ℤ) := by simpa [norm_mul] using h
      have hle := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (y * c) 1).mp hlt
      exact (not_le_of_gt hy') (by simpa [norm_mul] using hle)
    -- Translation by this point stays in the ball and multiplies the integral by a nontrivial value.
    let t : ℚ_[p] := (p : ℚ_[p])⁻¹ / y
    have ht : ‖t‖ ≤ ‖c‖ := by
      change ‖(p : ℚ_[p])⁻¹ / y‖ ≤ ‖c‖
      rw [norm_div, norm_inv, Padic.norm_p, inv_inv, div_le_iff₀ (norm_pos_iff.mpr hy0), mul_comm]
      exact hge
    have hmem (x : ℚ_[p]) : x + t ∈ B ↔ x ∈ B := by
      simp only [B, mem_closedBall_zero_iff]
      refine ⟨fun h ↦ ?_, fun h ↦ (Padic.nonarchimedean x t).trans (max_le h ht)⟩
      have h' := (Padic.nonarchimedean (x + t) (-t)).trans (max_le h (by simpa using ht))
      simpa using h'
    have ht_mul : t * y = (p : ℚ_[p])⁻¹ := div_mul_cancel₀ _ hy0
    have hnontrivial : g t ≠ 1 := by
      intro h
      apply padicStandardCharacter_inv_prime_ne_one p
      apply Subtype.ext
      exact star_injective (by simpa only [g, ht_mul, Circle.coe_one, star_one] using h)
    have hshift : (fun x ↦ B.indicator g (x + t)) =
        fun x ↦ B.indicator g x * g t := by
      funext x
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).mpr hx)]
        simp only [g, add_mul, padicStandardCharacter_add, Circle.coe_mul, star_mul]
        exact mul_comm _ _
      · simp [hx, mt (hmem x).mp hx]
    have h := integral_add_right_eq_self (μ := μ) (B.indicator g) t
    rw [show (fun x ↦ B.indicator g (x + t)) = _ from hshift, integral_mul_const,
      integral_indicator hB] at h
    have hzero : (∫ x in B, g x ∂μ) = 0 := by
      by_contra hne
      exact hnontrivial ((mul_eq_left₀ hne).mp h)
    rw [hzero, Pi.smul_apply, indicator_of_notMem hyc, smul_zero]

/-- Paper: Example A.3.1.6, p. 557. The Fourier transform of the indicator of the
p-adic integer units is the difference in (A.3.1.6). -/
theorem padicTamagawaFourier_integerUnits :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ({x : ℚ_[p] | ‖x‖ = 1}.indicator (fun _ ↦ (1 : ℂ))) =
      ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) - ((p : ℂ)⁻¹) • ((((p : ℚ_[p])⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
  let μ := padicTamagawaMeasure p
  have hμ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  have : μ.IsAddHaarMeasure := hμ.1
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let P := ((p : ℚ_[p]) * ·) '' ℤₚ
  have hP : P = Metric.ball 0 1 := padicPrimeMulIntegers_eq_ball p hp
  have hsub : P ⊆ ℤₚ := hP ▸ Metric.ball_subset_closedBall
  have hdiff : {x : ℚ_[p] | ‖x‖ = 1} = ℤₚ \ P := by
    ext x
    simp only [hP, mem_ofPred_eq, mem_sdiff, mem_closedBall_zero_iff, Metric.mem_ball, dist_zero_right,
      not_lt]
    exact le_antisymm_iff
  have h0 : tamagawaFourier μ (padicStandardCharacter p) ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
      (ℤₚ).indicator (fun _ ↦ (1 : ℂ)) := by
    have hone : (padicTamagawaMeasure p) ℤₚ = 1 := hμ.2.2
    have hmass : (padicTamagawaMeasure p).real ℤₚ = 1 := by
      rw [measureReal_def, hone, ENNReal.toReal_one]
    simpa [hmass] using padicTamagawaFourier_scaledIntegers_eq_measure p 1 one_ne_zero
  have h1 : tamagawaFourier μ (padicStandardCharacter p) (P.indicator (fun _ ↦ (1 : ℂ))) =
      ((p : ℂ)⁻¹) • ((((p : ℚ_[p])⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
    simpa [P, padicTamagawaMeasure_real_primeMulIntegers p hp, Complex.ofReal_inv] using padicTamagawaFourier_scaledIntegers_eq_measure p p hp
  rw [hdiff, Set.indicator_sdiff hsub]
  conv_rhs => rw [← h0, ← h1]
  funext y
  let g (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x * y) : ℂ)
  have hg : Continuous g :=
    (continuous_subtype_val.comp ((padicStandardCharacter_continuous p).comp (continuous_id.mul continuous_const))).star
  have hInt (s : Set ℚ_[p]) (hs : IsCompact s) : Integrable (s.indicator g) μ :=
    (integrable_indicator_iff hs.measurableSet).mpr (hg.continuousOn.integrableOn_compact hs)
  unfold tamagawaFourier
  change (∫ x, ((ℤₚ).indicator (fun _ ↦ (1 : ℂ)) x - P.indicator (fun _ ↦ (1 : ℂ)) x) * g x ∂μ) =
    (∫ x, (ℤₚ).indicator (fun _ ↦ (1 : ℂ)) x * g x ∂μ) -
      ∫ x, P.indicator (fun _ ↦ (1 : ℂ)) x * g x ∂μ
  simp only [sub_mul, ← indicator_mul_left, one_mul]
  exact integral_sub (hInt _ (isCompact_closedBall _ _))
    (hInt _ (by
      change IsCompact (((p : ℚ_[p]) * ·) '' ℤₚ)
      rw [padicScaledIntegers_eq_closedBall p _ hp]
      exact isCompact_closedBall _ _))

/-- Paper: Example A.3.1.6, p. 557. Multiplication followed by the standard character
identifies the additive group of the p-adic field with its Pontryagin dual. -/
theorem exists_padicPontryaginDualEquiv :
    ∃ e : Multiplicative ℚ_[p] ≃ₜ* PontryaginDual (Multiplicative ℚ_[p]),
      ∀ x y : ℚ_[p], e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        padicStandardCharacter p (x * y) := by
  sorry

/-- Paper: Example A.3.1.7, p. 558. The standard additive measure on the p-adic field
is self-dual under the standard character. -/
theorem padicTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (padicTamagawaMeasure p) (padicStandardCharacter p) := by
  obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
  refine ⟨e, he, ?_⟩
  let G := Multiplicative ℚ_[p]
  let μ : Measure G := padicTamagawaMeasure p
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨hHaar, hRegular, hMass⟩ :=
    Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hRegular
  let ν₀ : Measure (PontryaginDual G) := μ.map e
  let : ν₀.IsHaarMeasure := e.isHaarMeasure_map μ
  let : ν₀.Regular := Measure.Regular.map e.toHomeomorph
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  let K : Set G := ℤₚ
  let f : G → ℂ := K.indicator (fun _ ↦ 1)
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hKMass : μ K = 1 := hMass
  have hKFinite : μ K ≠ ⊤ := by rw [hKMass]; exact ENNReal.one_ne_top
  have hf₁ : Integrable f μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hK.nullMeasurableSet 1 (Or.inr hKFinite))
  have hf₂ : MemLp f 2 μ := memLp_indicator_const 2 hK.nullMeasurableSet 1 (Or.inr hKFinite)
  -- The unit ball indicator is fixed by Fourier transform in the pairing coordinates.
  have hFourier : lcaFourier μ f ∘ e = f := by
    have h := padicTamagawaFourier_scaledIntegers p 0
    simp only [zpow_zero, neg_zero, one_mul, image_id', one_smul] at h
    funext y
    change lcaFourier μ f (e y) = f y
    have hy := tamagawaFourier_eq_lcaFourier (padicTamagawaMeasure p)
      (padicStandardCharacter p) ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) y.toAdd (e y)
      (fun x ↦ (he y.toAdd x).trans (congrArg _ (mul_comm _ _)))
    exact hy.symm.trans (congrFun h y.toAdd)
  have hScale := Measure.isMulLeftInvariant_eq_smul_of_regular ν ν₀
  have hNorm := (hν.2.2 f hf₁ hf₂).2
  have hMeas : StronglyMeasurable (lcaFourier μ f) := by
    have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hK
    convert hf.comp_measurable e.symm.continuous.measurable using 1
    funext χ
    change lcaFourier μ f χ = f (e.symm χ)
    simpa only [Function.comp_apply, e.apply_symm_apply] using congrFun hFourier (e.symm χ)
  have hEmb : MeasurableEmbedding (e : G → PontryaginDual G) :=
    e.toHomeomorph.measurableEmbedding
  have hMap : eLpNorm (lcaFourier μ f) 2 ν₀ = eLpNorm f 2 μ := by
    exact (hEmb.eLpNorm_map_measure).trans (congrArg (fun g ↦ eLpNorm g 2 μ) hFourier)
  rw [hScale, eLpNorm_smul_measure_of_ne_top' (by simp : (2 : ℝ≥0∞) ≠ ⊤) _ _
      hMeas.aestronglyMeasurable, hMap] at hNorm
  have hfNorm : eLpNorm f 2 μ = 1 := by
    rw [eLpNorm_indicator_const hK.nullMeasurableSet (by simp) (by simp), hKMass]
    simp
  rw [hfNorm] at hNorm
  change (↑(ν.haarScalarFactor ν₀ ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * 1 = 1 at hNorm
  rw [mul_one] at hNorm
  have hFactor : ν.haarScalarFactor ν₀ = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa [ENNReal.coe_rpow_of_nonneg] using hNorm
  rw [hFactor, one_smul] at hScale
  change IsLCAPlancherelMeasure μ ν₀
  exact hScale ▸ hν

end Padic

/-- Paper: Example A.3.1.8, p. 558. The rational adelic character multiplies the real
character and all the p-adic characters, only finitely many of which contribute. -/
def ratAdeleStandardCharacter (a : 𝔸[ℚ]) : Circle :=
  Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    (a.1 Rat.infinitePlace)) *
    ∏ᶠ v : Primes(ℚ),
      let p := Rat.HeightOneSpectrum.primesEquiv v
      letI : Fact p.val.Prime := ⟨p.property⟩
      padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a.2 v))

/-- Paper: Example A.3.1.8, p. 558. On an adele supported at the real place, the
global rational character takes the value of the standard real character. -/
theorem ratAdeleStandardCharacter_real (a : 𝔸[ℚ]) (ha : a.2 = 0) :
    ratAdeleStandardCharacter a =
      Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (a.1 Rat.infinitePlace)) := by
  have h0 (q : ℕ) [Fact q.Prime] : padicStandardCharacter q 0 = 1 := by
    have hval (n : ℕ) (hn : n = 0) (x : ZMod (q ^ n)) : x.val = 0 := by
      subst hn
      exact Nat.lt_one_iff.mp (by simpa using x.val_lt)
    simp only [padicStandardCharacter]
    rw [hval _ (by simp) _]
    simp
  have h0' (v : Primes(ℚ)) : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 0 := rfl
  rw [ratAdeleStandardCharacter, ha]
  simp [h0', h0]

/-- Paper: Example A.3.1.8, p. 558. The global rational character is trivial on the
diagonally embedded rational numbers. The paper uses this without stating it; it is what
Poisson summation over the rationals needs, and it fails for the signs as printed. -/
theorem ratAdeleStandardCharacter_algebraMap (q : ℚ) :
    ratAdeleStandardCharacter (algebraMap ℚ 𝔸[ℚ] q) = 1 := by sorry

section RatAdeleSelfDuality

local instance : BorelSpace 𝔸[ℚ] := ⟨rfl⟩

/-- The real coordinate of a rational adele in the unique real completion. -/
private def ratRealPart (a : 𝔸[ℚ]) : ℝ :=
  extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace)

local notation "ratIntegralAdeles" => (integralAdelesOutside ℚ ∅ : Set 𝔸[ℚ])

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The adeles integral at every finite place form an open subring. -/
private theorem isOpen_ratIntegralAdeles : IsOpen ratIntegralAdeles := by
  simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred, Finset.notMem_empty,
    not_false_eq_true, true_implies]
  exact (RestrictedProduct.isOpen_forall_mem (fun v : Primes(ℚ) ↦
    Valued.isOpen_integer (v.adicCompletion ℚ))).preimage continuous_snd

/-- Projecting the restriction to integral finite components onto the real coordinate
gives Lebesgue measure. The finite integral factors have product mass one. -/
private theorem ratTamagawaMeasurePreserving_realPart :
    MeasurePreserving ratRealPart ((additiveTamagawaMeasure ℚ).restrict ratIntegralAdeles)
      (volume : Measure ℝ) := by
  let t : InfiniteAdeleRing ℚ → ℝ := fun a ↦
    extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a Rat.infinitePlace)
  have ht : Continuous t :=
    (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp (continuous_apply _)
  let μ := infiniteLocalAdditiveTamagawaMeasure ℚ
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let (v : InfinitePlace ℚ) : BorelSpace v.Completion := ⟨rfl⟩
  let (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let : BorelSpace (InfiniteAdeleRing ℚ) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace ℚ) → v.Completion))
  let e := (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e (μ Rat.infinitePlace) volume := by
    refine ⟨e.measurable, ?_⟩
    change (infiniteLocalAdditiveTamagawaMeasure ℚ Rat.infinitePlace).map e = _
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace]
    change (Measure.map e.symm volume).map e = _
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hπ : MeasurePreserving t (Measure.pi μ) volume :=
    he.comp (measurePreserving_piUnique μ)
  have hm : Measurable ratRealPart :=
    Continuous.measurable (α := 𝔸[ℚ]) (ht.comp continuous_fst)
  refine ⟨hm, Measure.ext fun B hB ↦ ?_⟩
  rw [Measure.map_apply hm hB, Measure.restrict_apply (hm hB)]
  have hset : ratRealPart ⁻¹' B ∩ ratIntegralAdeles =
      {a : 𝔸[ℚ] | a.1 ∈ t ⁻¹' B ∧
        (∀ v : (∅ : Finset (Primes(ℚ))), a.2 v.val ∈ (Set.univ : Set (v.val.adicCompletion ℚ))) ∧
        a ∈ integralAdelesOutside ℚ ∅} := by
    ext a
    simp [t, ratRealPart]
  rw [hset, additiveTamagawaMeasure_restrictedProduct ℚ ∅ _ (ht.measurable hB) _
    (fun _ ↦ MeasurableSet.univ)]
  have htail : (∏ᶠ v : {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))},
      differentMass(ℚ, v.val)) = 1 := by
    rw [finprod_subtype_eq_finprod_cond (f := fun v : Primes(ℚ) ↦ differentMass(ℚ, v))
      (fun v ↦ v ∉ (∅ : Finset (Primes(ℚ))))]
    simp only [Finset.notMem_empty, not_false_eq_true, finprod_true,
      finiteLocalTamagawaMass_finprod]
    simp
  simp only [htail, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact hπ.measure_preimage hB.nullMeasurableSet

/-- Paper: Example A.3.1.8, p. 558. The adelic Gaussian is the real Gaussian times
the indicator of the adeles integral at every finite place. -/
private def ratAdeleGaussian : 𝔸[ℚ] → ℂ :=
  Set.indicator ratIntegralAdeles (fun a ↦ (Real.exp (-Real.pi * (ratRealPart a) ^ 2) : ℂ))

/-- The adelic Gaussian is integrable and square-integrable. -/
private theorem ratAdeleGaussian_integrable_memLp :
    Integrable ratAdeleGaussian (additiveTamagawaMeasure ℚ) ∧
      MemLp ratAdeleGaussian 2 (additiveTamagawaMeasure ℚ) := by
  let g : ℝ → ℂ := fun x ↦ (Real.exp (-Real.pi * x ^ 2) : ℂ)
  have hg : Integrable g volume := (integrable_exp_neg_mul_sq Real.pi_pos).ofReal
  have hg₂ : MemLp g 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
    convert integrable_exp_neg_mul_sq (b := 2 * Real.pi) (by positivity) using 1
    funext x
    dsimp [g]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hI := isOpen_ratIntegralAdeles.measurableSet
  exact ⟨(integrable_indicator_iff hI).2
    (ratTamagawaMeasurePreserving_realPart.integrable_comp_of_integrable hg),
    (memLp_indicator_iff_restrict hI.nullMeasurableSet).2
      (hg₂.comp_measurePreserving ratTamagawaMeasurePreserving_realPart)⟩

/-- The standard character on the completion at a finite rational place. -/
private def ratLocalCharacter (v : Primes(ℚ)) (x : v.adicCompletion ℚ) : Circle :=
  let p := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact p.val.Prime := ⟨p.property⟩
  padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x)

/-- At each finite rational place, the local character has kernel the local integers. -/
private theorem ratLocalCharacter_eq_one (v : Primes(ℚ)) (x : v.adicCompletion ℚ) :
    ratLocalCharacter v x = 1 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let : Fact p.val.Prime := ⟨p.property⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  change padicStandardCharacter p.val (e x) = 1 ↔ _
  rw [padicStandardCharacter_eq_one_iff]
  have h := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  refine ⟨fun hx ↦ ?_, fun hx ↦ h.mapsTo hx⟩
  obtain ⟨z, hz, he⟩ := h.surjOn hx
  exact e.injective he ▸ hz

/-- Membership in the integral subring amounts to integrality in each finite coordinate. -/
private theorem mem_ratIntegralAdeles (a : 𝔸[ℚ]) :
    a ∈ ratIntegralAdeles ↔ ∀ v : Primes(ℚ), a.2 v ∈ v.adicCompletionIntegers ℚ := by
  change a ∈ integralAdelesOutside ℚ ∅ ↔ _
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
    true_implies]
  rfl

/-- On integral finite components the global character is its real factor. -/
private theorem ratAdeleStandardCharacter_of_integral (a : 𝔸[ℚ]) (ha : a ∈ ratIntegralAdeles) :
    ratAdeleStandardCharacter a = Circle.exp (2 * Real.pi * ratRealPart a) := by
  change Circle.exp (2 * Real.pi * ratRealPart a) *
    (∏ᶠ v : Primes(ℚ), ratLocalCharacter v (a.2 v)) = _
  rw [finprod_eq_one_of_forall_eq_one (fun v ↦
    (ratLocalCharacter_eq_one v (a.2 v)).2 ((mem_ratIntegralAdeles a).1 ha v)), mul_one]

/-- The global character is multiplicative on sums of rational adeles. -/
private theorem ratAdeleStandardCharacter_add (a b : 𝔸[ℚ]) :
    ratAdeleStandardCharacter (a + b) =
      ratAdeleStandardCharacter a * ratAdeleStandardCharacter b := by
  let f (x : 𝔸[ℚ]) (v : Primes(ℚ)) := ratLocalCharacter v (x.2 v)
  have hfinite (x : 𝔸[ℚ]) : (f x).HasFiniteMulSupport := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [x.2.2] with v hv
    exact (ratLocalCharacter_eq_one v _).2 hv
  have hsum : f (a + b) = f a * f b := by
    funext v
    let p := Rat.HeightOneSpectrum.primesEquiv v
    let : Fact p.val.Prime := ⟨p.property⟩
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
    change padicStandardCharacter p.val (e (a.2 v + b.2 v)) =
      padicStandardCharacter p.val (e (a.2 v)) * padicStandardCharacter p.val (e (b.2 v))
    rw [map_add, padicStandardCharacter_add]
  have hreal : ratRealPart (a + b) = ratRealPart a + ratRealPart b :=
    map_add (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _
  change Circle.exp (2 * Real.pi * ratRealPart (a + b)) * (∏ᶠ v, f (a + b) v) =
    (Circle.exp (2 * Real.pi * ratRealPart a) * (∏ᶠ v, f a v)) *
      (Circle.exp (2 * Real.pi * ratRealPart b) * (∏ᶠ v, f b v))
  rw [hreal, mul_add, Circle.exp_add, hsum]
  simp only [Pi.mul_apply, finprod_mul_distrib (hfinite a) (hfinite b)]
  ac_rfl

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- A frequency with a nonintegral finite component gives a nontrivial character
on some integral adele supported at one finite place. -/
private theorem exists_ratIntegralAdeles_character_ne_one (y : 𝔸[ℚ]) (hy : y ∉ ratIntegralAdeles) :
    ∃ b : 𝔸[ℚ], b ∈ ratIntegralAdeles ∧ b.1 = 0 ∧ ratAdeleStandardCharacter (b * y) ≠ 1 := by
  classical
  rw [mem_ratIntegralAdeles, not_forall] at hy
  obtain ⟨v, hv⟩ := hy
  let O := fun w : Primes(ℚ) ↦ w.adicCompletionIntegers ℚ
  let b : 𝔸[ℚ] := (0, RestrictedProduct.single O v 1)
  refine ⟨b, (mem_ratIntegralAdeles b).2 ?_, rfl, ?_⟩
  · intro w
    change RestrictedProduct.single O v 1 w ∈ O w
    by_cases hw : w = v
    · subst w
      rw [RestrictedProduct.single_eq_same]
      exact (O v).one_mem
    · rw [RestrictedProduct.single_eq_of_ne O _ hw]
      exact (O w).zero_mem
  have hval : ratAdeleStandardCharacter (b * y) = ratLocalCharacter v (y.2 v) := by
    change Circle.exp (2 * Real.pi * ratRealPart (b * y)) *
      (∏ᶠ w : Primes(ℚ), ratLocalCharacter w (RestrictedProduct.single O v 1 w * y.2 w)) = _
    have hz : ratRealPart (b * y) = 0 := by
      change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        ((0 : Rat.infinitePlace.Completion) * y.1 Rat.infinitePlace) = 0
      rw [zero_mul, map_zero]
    rw [hz, mul_zero, Circle.exp_zero, one_mul, finprod_eq_single _ v]
    · rw [RestrictedProduct.single_eq_same, one_mul]
    · intro w hw
      rw [RestrictedProduct.single_eq_of_ne O _ hw, zero_mul]
      exact (ratLocalCharacter_eq_one w 0).2 (O w).zero_mem
  rw [hval]
  exact fun h ↦ hv ((ratLocalCharacter_eq_one v _).1 h)

open scoped FourierTransform in
/-- Paper: Example A.3.1.8, p. 558. The real Gaussian times the indicator of the
integral finite adeles is fixed by the rational adelic Fourier transform. -/
private theorem tamagawaFourier_ratAdeleGaussian :
    tamagawaFourier (additiveTamagawaMeasure ℚ) ratAdeleStandardCharacter ratAdeleGaussian =
      ratAdeleGaussian := by
  funext y
  let I := integralAdelesOutside ℚ ∅
  let μ := additiveTamagawaMeasure ℚ
  by_cases hy : y ∈ I
  · let g : ℝ → ℂ := fun t ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ)
    let k : ℝ → ℂ := fun t ↦
      g t * star (Circle.exp (2 * Real.pi * (t * ratRealPart y)) : ℂ)
    have hK : AEStronglyMeasurable k (volume : Measure ℝ) := by
      apply Continuous.aestronglyMeasurable
      dsimp [k, g]
      fun_prop
    have hIntegrand (x : 𝔸[ℚ]) :
        ratAdeleGaussian x * star (ratAdeleStandardCharacter (x * y) : ℂ) =
          (I : Set 𝔸[ℚ]).indicator (k ∘ ratRealPart) x := by
      by_cases hx : x ∈ I
      · rw [ratAdeleGaussian, indicator_of_mem hx, indicator_of_mem hx,
          ratAdeleStandardCharacter_of_integral _ (I.mul_mem hx hy)]
        have hmul : ratRealPart (x * y) = ratRealPart x * ratRealPart y :=
          map_mul (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _
        rw [hmul]
        rfl
      · rw [ratAdeleGaussian, indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    rw [tamagawaFourier]
    simp_rw [hIntegrand]
    rw [integral_indicator isOpen_ratIntegralAdeles.measurableSet]
    have hMap := integral_map ratTamagawaMeasurePreserving_realPart.measurable.aemeasurable
      (f := k) (ratTamagawaMeasurePreserving_realPart.map_eq.symm ▸ hK)
    rw [ratTamagawaMeasurePreserving_realPart.map_eq] at hMap
    change (∫ x, k (ratRealPart x) ∂μ.restrict I) = ratAdeleGaussian y
    rw [← hMap]
    have hFourier : (∫ t, k t) = 𝓕 g (ratRealPart y) := by
      rw [Real.fourier_eq]
      congr 1
      funext t
      dsimp only [k]
      rw [← Real.fourierChar_apply', Circle.star_addChar, Real.inner_apply,
        Circle.smul_def, smul_eq_mul, mul_comm t (ratRealPart y), mul_comm (g t)]
    have hg : 𝓕 g = g := by
      have hg' : (fun t : ℝ ↦ Complex.exp (-(Real.pi : ℂ) * 1 * (t : ℂ) ^ 2)) = g := by
        funext t
        dsimp only [g]
        rw [Complex.ofReal_exp]
        push_cast
        rw [mul_one]
      rw [← hg']
      simpa using fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)
    rw [hFourier, hg]
    rw [ratAdeleGaussian, indicator_of_mem hy]
  · obtain ⟨b, hb, hreal, hchar⟩ := exists_ratIntegralAdeles_character_ne_one y hy
    let h : 𝔸[ℚ] → ℂ := fun x ↦ ratAdeleGaussian x *
      star (ratAdeleStandardCharacter (x * y) : ℂ)
    have hμ : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec.1
    have htranslate (x : 𝔸[ℚ]) :
        h (b + x) = h x * star (ratAdeleStandardCharacter (b * y) : ℂ) := by
      have hI : b + x ∈ I ↔ x ∈ I := ⟨fun hx ↦ by
        simpa only [add_comm b x, add_sub_cancel_right] using I.sub_mem hx hb, I.add_mem hb⟩
      have hg : ratAdeleGaussian (b + x) = ratAdeleGaussian x := by
        have hx : ratRealPart (b + x) = ratRealPart x := by
          change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
            (b.1 Rat.infinitePlace + x.1 Rat.infinitePlace) = _
          rw [hreal, Pi.zero_apply, zero_add]
          rfl
        unfold ratAdeleGaussian
        by_cases hmem : x ∈ I
        · rw [indicator_of_mem (hI.2 hmem), indicator_of_mem hmem, hx]
        · rw [indicator_of_notMem (hI.not.2 hmem), indicator_of_notMem hmem]
      simp only [h, hg, add_mul, ratAdeleStandardCharacter_add, Circle.coe_mul, star_mul']
      ring
    have hJ : (∫ x, h x ∂μ) =
        (∫ x, h x ∂μ) * star (ratAdeleStandardCharacter (b * y) : ℂ) := by
      rw [← integral_mul_const]
      simp_rw [← htranslate]
      exact (integral_add_left_eq_self h b).symm
    have hne : star (ratAdeleStandardCharacter (b * y) : ℂ) ≠ 1 := by
      intro hc
      apply hchar
      apply Circle.coe_injective
      rw [Circle.coe_one]
      exact star_injective (hc.trans (star_one ℂ).symm)
    change (∫ x, h x ∂μ) = ratAdeleGaussian y
    rw [ratAdeleGaussian, indicator_of_notMem hy]
    by_contra hn
    exact hne (mul_left_cancel₀ hn (hJ.symm.trans (mul_one _).symm))

/-- Paper: Example A.3.1.8, p. 558. The product character pairing identifies
the additive rational adeles with their Pontryagin dual as topological groups.
The local integer rings are their own annihilators for the finite-place pairings. -/
theorem exists_ratAdeleDualEquiv :
    ∃ e : Multiplicative 𝔸[ℚ] ≃ₜ* PontryaginDual (Multiplicative 𝔸[ℚ]),
      ∀ x y : 𝔸[ℚ], e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        ratAdeleStandardCharacter (x * y) := by
  sorry

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Example A.3.1.8, p. 558. The additive Tamagawa measure on the rational
adeles is self-dual under the product of the standard local characters. -/
theorem ratAdditiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (additiveTamagawaMeasure ℚ) ratAdeleStandardCharacter := by
  obtain ⟨e, he⟩ := exists_ratAdeleDualEquiv
  refine ⟨e, he, ?_⟩
  let G := Multiplicative 𝔸[ℚ]
  let μ : Measure G := additiveTamagawaMeasure ℚ
  let (v : Primes(ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(ℚ), IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing ℚ ×
      (Πʳ v : Primes(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : Primes(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  obtain ⟨ν, hν, _⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  let η := μ.map e.toHomeomorph
  let : η.IsHaarMeasure := e.isHaarMeasure_map μ
  let : η.Regular := Measure.Regular.map e.toHomeomorph
  let c := ν.haarScalarFactor η
  have hc : ν = c • η := Measure.isMulLeftInvariant_eq_smul_of_regular ν η
  let f : G → ℂ := fun x ↦ ratAdeleGaussian x.toAdd
  obtain ⟨hf₁, hf₂⟩ := ratAdeleGaussian_integrable_memLp
  have hFourier : lcaFourier μ f ∘ e.toHomeomorph = f := by
    funext x
    have hx := congrFun tamagawaFourier_ratAdeleGaussian x.toAdd
    rw [tamagawaFourier_eq_lcaFourier _ _ _ _ _ (fun y ↦ by
      rw [he x.toAdd y, mul_comm])] at hx
    exact hx
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 hzero
    have hI : IsClopen ratIntegralAdeles :=
      ⟨(integralAdelesOutside ℚ ∅).toAddSubgroup.isClosed_of_isOpen isOpen_ratIntegralAdeles,
        isOpen_ratIntegralAdeles⟩
    have hfun : Continuous ratAdeleGaussian := by
      unfold ratAdeleGaussian
      apply hI.continuous_indicator
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (((isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
          ((continuous_apply Rat.infinitePlace).comp continuous_fst)).pow 2)))
    have heq : f = 0 := Measure.eq_of_ae_eq hae hfun continuous_const
    have h1 := congrFun heq (1 : G)
    change ratAdeleGaussian 0 = 0 at h1
    simp [ratAdeleGaussian, ratRealPart, (integralAdelesOutside ℚ ∅).zero_mem] at h1
  have hLp : MemLp (lcaFourier μ f) 2 η := by
    apply e.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.mpr
    rw [hFourier]
    exact hf₂
  have hScale := (hν.2.2 f hf₁ hf₂).2
  have hMap : eLpNorm (lcaFourier μ f) 2 η =
      eLpNorm (lcaFourier μ f ∘ e.toHomeomorph) 2 μ :=
    e.toHomeomorph.measurableEmbedding.eLpNorm_map_measure
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp) _
    _ hLp.aestronglyMeasurable, hMap, hFourier] at hScale
  change (↑(c ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * eLpNorm f 2 μ = eLpNorm f 2 μ at hScale
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)] at hScale
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 :=
    (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp (hScale.trans (one_mul _).symm)
  have hc₁ : c = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos
      (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot
  change IsLCAPlancherelMeasure μ η
  simpa only [hc, hc₁, one_smul] using hν

end RatAdeleSelfDuality

/-- Paper: Example A.3.1.9, p. 558. In (A.3.1.7) the standard adelic character is
the rational adelic character composed with the adelic trace.
Deviation: The displayed field trace is extended to the adele algebra as required by its domain. -/
def adeleStandardCharacter (a : 𝔸[F]) : Circle :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  ratAdeleStandardCharacter (Algebra.trace 𝔸[ℚ] 𝔸[F] a)

/-- Paper: Example A.3.1.9, p. 558. The standard adelic character is trivial on the
diagonally embedded field, which is what Theorem 2.2.3.2 and Theorem 3.2.2.1 need. -/
theorem adeleStandardCharacter_algebraMap (x : F) :
    adeleStandardCharacter F (algebraMap F 𝔸[F] x) = 1 := by sorry

/-- Paper: Example A.3.1.9, p. 558. The standard adelic character reduces to the
rational adelic character for the rational field. -/
theorem adeleStandardCharacter_rat (a : 𝔸[ℚ]) :
    adeleStandardCharacter ℚ a = ratAdeleStandardCharacter a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, extensions⟩ := adele_additive_quotient ℚ
  have h : rationalAdeleEmbedding ℚ = RingHom.id 𝔸[ℚ] :=
    (extensions ℚ (RingHom.id ℚ)).1.unique
      (rationalAdeleEmbedding_spec ℚ) (isAdeleExtension_id ℚ)
  unfold adeleStandardCharacter
  rw [h]
  exact congrArg ratAdeleStandardCharacter (Algebra.trace_self_apply a)

section AdeleSelfDuality

local instance : BorelSpace 𝔸[F] := ⟨rfl⟩

local instance : BorelSpace (Multiplicative 𝔸[F]) := ⟨rfl⟩

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The rational adeles are second countable by the countable open cover obtained by
allowing a finite set of primes to have nonintegral components. -/
private theorem ratAdele_secondCountable : SecondCountableTopology (Multiplicative 𝔸[ℚ]) := by
  let I := Primes(ℚ)
  let K (v : I) := v.adicCompletion ℚ
  let O (v : I) : Set (K v) := v.adicCompletionIntegers ℚ
  let : Countable I := Rat.HeightOneSpectrum.primesEquiv.injective.countable
  let (v : I) : SecondCountableTopology (K v) := by
    let p := Rat.HeightOneSpectrum.primesEquiv v
    let : Fact p.val.Prime := ⟨p.property⟩
    let : TopologicalSpace.SeparableSpace ℚ_[p.val] :=
      ⟨⟨range ((↑) : ℚ → ℚ_[p.val]), countable_range _, Padic.denseRange_ratCast _⟩⟩
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding
      |>.secondCountableTopology
  let U := fun s : Finset I ↦ {a : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v ∉ s, a v ∈ O v}
  have hopen (v : I) : IsOpen (O v) := Valued.isOpen_integer (K v)
  let (s : Finset I) : SecondCountableTopology (U s) := by
    have hs : Filter.cofinite ≤ Filter.principal (s : Set I)ᶜ :=
      Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have he := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := K) (A := O) hopen hs
    let : SecondCountableTopology (Πʳ v : I, [K v, O v]_[Filter.principal (s : Set I)ᶜ]) :=
      (RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := O)).secondCountableTopology
    have hrange : range (RestrictedProduct.inclusion K O hs) = U s := by
      rw [RestrictedProduct.range_inclusion]
      rfl
    exact hrange ▸ he.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
      (fun _ ↦ RestrictedProduct.isOpen_forall_imp_mem hopen) (eq_univ_of_forall fun a ↦ ?_)
    have he := Filter.eventually_cofinite.mp a.2
    exact mem_iUnion.mpr ⟨he.toFinset, fun v hv ↦ by
      by_contra h
      exact hv (he.mem_toFinset.mpr h)⟩
  let (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  change SecondCountableTopology (((v : InfinitePlace ℚ) → v.Completion) ×
    FiniteAdeleRing (𝓞 ℚ) ℚ)
  infer_instance

attribute [local instance] ratAdele_secondCountable

open scoped RestrictedProduct in
/-- The product of the infinite adeles and the locally compact restricted product of
the finite completions is locally compact. -/
private theorem adele_locallyCompact : LocallyCompactSpace (Multiplicative 𝔸[F]) := by
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  change LocallyCompactSpace (InfiniteAdeleRing F ×
    (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

attribute [local instance] adele_locallyCompact

open scoped RestrictedProduct in
local instance : T2Space (Multiplicative 𝔸[F]) := by
  change T2Space (((v : InfinitePlace F) → v.Completion) ×
    (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

/-- The covolume-one measure is Haar on the multiplicative synonym of the
additive group of adeles. -/
private theorem additiveTamagawaMeasure_isHaar :
    (show Measure (Multiplicative 𝔸[F]) from additiveTamagawaMeasure F).IsHaarMeasure := by
  have h := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  exact { toIsFiniteMeasureOnCompacts := h.toIsFiniteMeasureOnCompacts
          toIsOpenPosMeasure := h.toIsOpenPosMeasure
          map_mul_left_eq_self := fun x ↦ h.map_add_left_eq_self x.toAdd }

attribute [local instance] additiveTamagawaMeasure_isHaar

open scoped TensorProduct in
/-- Paper: Example A.3.1.9, p. 558. A rational basis of `F` and its trace-dual basis
give adelic coordinates in which the trace character pairing is coordinatewise. Both
coordinate maps carry the diagonal rational vectors onto the diagonal copy of `F`. -/
theorem exists_adeleTrace_dualCoordinates :
    let ι := Fin (Module.finrank ℚ F)
    let d := fun q : ι → ℚ ↦ fun i ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (q i))
    ∃ u v : (ι → Multiplicative 𝔸[ℚ]) ≃ₜ* Multiplicative 𝔸[F],
      u '' range d = (A[F] : Set (Multiplicative 𝔸[F])) ∧
      v '' range d = (A[F] : Set (Multiplicative 𝔸[F])) ∧
      ∀ x y, adeleStandardCharacter F ((u x).toAdd * (v y).toAdd) =
        ∏ i, ratAdeleStandardCharacter ((x i).toAdd * (y i).toAdd) := by
  classical
  let ι := Fin (Module.finrank ℚ F)
  let dQ := algebraMap ℚ 𝔸[ℚ]
  let dF := algebraMap F 𝔸[F]
  let : Algebra 𝔸[ℚ] 𝔸[F] := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b₀, hb₀⟩ := exists_adelicIntegralBasis F
  let reindex : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ ι :=
    (Fintype.equivFin _).trans (finCongr (Module.finrank_eq_card_basis (integralBasis F)).symm)
  let c := (integralBasis F).reindex reindex
  let b := b₀.reindex reindex
  have hb (i : ι) : b i = dF (c i) := by
    simpa only [b, c, Module.Basis.reindex_apply] using hb₀ (reindex.symm i)
  have hdiag (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) (C : Module.Basis ι ℚ F)
      (hB : ∀ i, B i = dF (C i)) (q : ι → ℚ) :
      B.equivFun.symm (dQ ∘ q) = dF (C.equivFun.symm q) := by
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hB, Function.comp_apply, Algebra.smul_def, map_mul]
    exact congrArg (· * dF (C i)) ((rationalAdeleEmbedding_spec F).2.1 (q i))
  have hrepr (x : F) (i : ι) : b.repr (dF x) i = dQ (c.repr x i) := by
    have h := hdiag b c hb (c.equivFun x)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  let tr := Algebra.trace 𝔸[ℚ] 𝔸[F]
  have htrace (x : F) : tr (dF x) = dQ (Algebra.trace ℚ F x) := by
    change Algebra.trace 𝔸[ℚ] 𝔸[F] (dF x) = _
    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace c, AddMonoidHom.map_trace]
    congr 1
    ext i j
    change (Algebra.leftMulMatrix b (dF x)) i j = dQ ((Algebra.leftMulMatrix c x) i j)
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul, hrepr]
  let lift : (𝔸[ℚ] ⊗[ℚ] F) ≃ₗ[𝔸[ℚ]] 𝔸[F] :=
    (c.baseChange 𝔸[ℚ]).equivFun.trans b.equivFun.symm
  have hlift (x : F) : lift ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x) = dF x := by
    have hcoords : (c.baseChange 𝔸[ℚ]).equivFun ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x) = dQ ∘ c.equivFun x := by
      funext i
      change (c.baseChange 𝔸[ℚ]).repr ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x) i = dQ (c.repr x i)
      rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    change b.equivFun.symm ((c.baseChange 𝔸[ℚ]).equivFun ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x)) = _
    rw [hcoords, hdiag b c hb, LinearEquiv.symm_apply_apply]
  let b' := (c.traceDual.baseChange 𝔸[ℚ]).map lift
  have hb' (i : ι) : b' i = dF (c.traceDual i) := by
    simp only [b', Module.Basis.map_apply, Module.Basis.baseChange_apply, hlift]
  have hδ (i j : ι) : tr (b i * b' j) = if i = j then 1 else 0 := by
    rw [hb, hb', ← map_mul, htrace, c.trace_mul_traceDual]
    split_ifs <;> simp
  let P := ι → Multiplicative 𝔸[ℚ]
  let G := Multiplicative 𝔸[F]
  let coords (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) : P ≃ₜ* G := by
    let L := B.equivFun.symm
    have hL : Continuous L := by
      change Continuous (fun a ↦ L a)
      simp only [L, Module.Basis.equivFun_symm_apply, Algebra.smul_def]
      exact continuous_finsetSum _ fun i _ ↦
        ((rationalAdeleEmbedding_spec F).1.comp (continuous_apply i)).mul continuous_const
    let : SigmaCompactSpace (Multiplicative 𝔸[ℚ]) := inferInstance
    let : SigmaCompactSpace 𝔸[ℚ] := ‹SigmaCompactSpace (Multiplicative 𝔸[ℚ])›
    let : LocallyCompactSpace 𝔸[F] := adele_locallyCompact F
    let : T2Space 𝔸[F] := inferInstanceAs (T2Space (Multiplicative 𝔸[F]))
    have hinv : Continuous L.symm := L.toEquiv.continuous_symm_iff.mpr
      (L.toAddMonoidHom.isOpenMap_of_sigmaCompact L.surjective hL)
    exact { L.toAddEquiv.toMultiplicative with
      continuous_toFun := hL
      continuous_invFun := hinv }
  have hcoords (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) (x : P) :
      (coords B x).toAdd = B.equivFun.symm (fun i ↦ (x i).toAdd) := rfl
  let d (q : ι → ℚ) : P := fun i ↦ Multiplicative.ofAdd (dQ (q i))
  have himage (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) (C : Module.Basis ι ℚ F)
      (hB : ∀ i, B i = dF (C i)) : coords B '' range d = (A[F] : Set G) := by
    ext x
    change x ∈ coords B '' range d ↔ ∃ z : F, dF z = x.toAdd
    rw [← range_comp]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨C.equivFun.symm q, ?_⟩
      exact (hdiag B C hB q).symm.trans ((hcoords B (d q)).symm.trans
        (congrArg Multiplicative.toAdd hq))
    · rintro ⟨z, hz⟩
      refine ⟨C.equivFun z, ?_⟩
      apply Multiplicative.toAdd.injective
      change (coords B (d (C.equivFun z))).toAdd = x.toAdd
      rw [hcoords]
      exact (hdiag B C hB (C.equivFun z)).trans (by rw [LinearEquiv.symm_apply_apply, hz])
  refine ⟨coords b, coords b', himage b c hb, himage b' c.traceDual hb', ?_⟩
  intro x y
  rw [hcoords, hcoords]
  change ratAdeleStandardCharacter (tr (b.equivFun.symm (fun i ↦ (x i).toAdd) *
    b'.equivFun.symm (fun i ↦ (y i).toAdd))) = _
  have hPair (a z : ι → 𝔸[ℚ]) :
      tr (b.equivFun.symm a * b'.equivFun.symm z) = ∑ i, a i * z i := by
    simp only [Module.Basis.equivFun_symm_apply, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hδ,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (z i) (a i)
  rw [hPair]
  let ψ : 𝔸[ℚ] →+ Additive Circle :=
    { toFun := fun a ↦ Additive.ofMul (ratAdeleStandardCharacter a)
      map_zero' := by
        have h := ratAdeleStandardCharacter_add 0 0
        rw [zero_add] at h
        have hzero : ratAdeleStandardCharacter 0 = 1 :=
          mul_left_cancel (h.symm.trans (mul_one _).symm)
        exact hzero
      map_add' := ratAdeleStandardCharacter_add }
  exact congrArg Additive.toMul (map_sum ψ (fun i ↦ (x i).toAdd * (y i).toAdd) Finset.univ)

/-- Paper: Definition A.3.1.1, p. 555. An adelic coordinate map carrying the diagonal
rational vectors onto the diagonal field transports the product of rational Tamagawa
measures to the covolume-one measure. The product of rational fundamental domains
has mass one and its image is a fundamental domain for the diagonal field. -/
theorem adeleTamagawaMeasurePreserving_of_diagonal
    (u : (Fin (Module.finrank ℚ F) → Multiplicative 𝔸[ℚ]) ≃ₜ* Multiplicative 𝔸[F])
    (hu : u '' range (fun q : Fin (Module.finrank ℚ F) → ℚ ↦
      fun i ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (q i))) =
        (A[F] : Set (Multiplicative 𝔸[F]))) :
    MeasurePreserving u (Measure.pi fun _ ↦ additiveTamagawaMeasure ℚ)
      (additiveTamagawaMeasure F) := by
  classical
  let ι := Fin (Module.finrank ℚ F)
  let P := ι → Multiplicative 𝔸[ℚ]
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let mRat : Measure (Multiplicative 𝔸[ℚ]) := additiveTamagawaMeasure ℚ
  let ν : Measure P := Measure.pi fun _ ↦ mRat
  let μ : Measure G := additiveTamagawaMeasure F
  let m : Measure G := ν.map u
  let : SecondCountableTopology G := u.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : mRat.IsHaarMeasure := additiveTamagawaMeasure_isHaar ℚ
  let : SigmaFinite mRat := inferInstance
  let : ν.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : μ.IsHaarMeasure := additiveTamagawaMeasure_isHaar F
  let : m.IsHaarMeasure := u.isHaarMeasure_map ν
  let d (q : ι → ℚ) : P := fun i ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (q i))
  let E₀ : Set (Multiplicative 𝔸[ℚ]) := ratAdeleFundamentalDomain
  let E : Set P := univ.pi fun _ ↦ E₀
  let D : Set G := u '' E
  have hrat : MeasurableSet ratAdeleFundamentalDomain :=
    (ratTamagawaMeasurePreserving_realPart.measurable measurableSet_Ico).inter
      isOpen_ratIntegralAdeles.measurableSet
  have hE : MeasurableSet E := MeasurableSet.pi countable_univ (fun _ _ ↦ hrat)
  have huemb : MeasurableEmbedding (u : P → G) := u.toHomeomorph.measurableEmbedding
  have hD : MeasurableSet D := huemb.measurableSet_image.mpr hE
  have hνE : ν E = 1 := by
    have hmass : additiveTamagawaMeasure ℚ ratAdeleFundamentalDomain = 1 := by
      have h := ratTamagawaMeasurePreserving_realPart.measure_preimage
        (measurableSet_Ico.nullMeasurableSet (s := Ico (0 : ℝ) 1))
      rwa [Measure.restrict_apply (ratTamagawaMeasurePreserving_realPart.measurable measurableSet_Ico),
        Real.volume_Ico, sub_zero, ENNReal.ofReal_one] at h
    change Measure.pi (fun _ : ι ↦ mRat) (univ.pi fun _ ↦ E₀) = 1
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ ↦ hmass
  have hprecompact : IsCompact (closure D) := by
    have hK : IsCompact (closure ratAdeleFundamentalDomain) := by
      simpa using ratAdeleFundamentalDomain_precompact_translate 0
    have hC : IsCompact (u '' (univ.pi fun _ : ι ↦
        (show Set (Multiplicative 𝔸[ℚ]) from closure ratAdeleFundamentalDomain))) :=
      (isCompact_univ_pi fun _ ↦ hK).image u.continuous
    exact hC.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.image_mono (Set.pi_mono fun _ _ ↦ subset_closure)) hC.isClosed)
  have hu' : u '' range d = (H : Set G) := hu
  let j : (ι → ℚ) → H := fun q ↦ ⟨u (d q), by
    change u (d q) ∈ (H : Set G)
    rw [← hu']
    exact Set.mem_image_of_mem u (mem_range_self q)⟩
  have hj : Bijective j := by
    have hinj := (adele_additive_quotient.{0, 0} ℚ).1
    refine ⟨fun x y h ↦ funext fun i ↦ ?_, fun a ↦ ?_⟩
    · exact hinj (congrFun (u.injective (congrArg Subtype.val h)) i)
    · have ha : a.val ∈ (H : Set G) := a.property
      rw [← hu'] at ha
      obtain ⟨_, ⟨q, rfl⟩, hq⟩ := ha
      exact ⟨q, Subtype.ext hq⟩
  let e : (ι → ℚ) ≃ H.op := ((Equiv.ofBijective j hj).trans (Equiv.inv H)).trans H.equivOp
  have htiles (a : G) : ∃! h : H.op, h • a ∈ D := by
    have hmem (q : ι → ℚ) : e q • a ∈ D ↔ ∀ i,
        (u.symm a i).toAdd ∈ algebraMap ℚ 𝔸[ℚ] (q i) +ᵥ ratAdeleFundamentalDomain := by
      change a * (u (d q))⁻¹ ∈ u '' E ↔ _
      have hx : u ((d q)⁻¹ * u.symm a) = a * (u (d q))⁻¹ := by
        rw [map_mul, map_inv, u.apply_symm_apply, mul_comm]
      rw [← hx, u.injective.mem_set_image]
      simp only [E, Set.mem_univ_pi, Set.mem_vadd_set_iff_neg_vadd_mem]
      rfl
    choose q hq huniq using fun i ↦ ratAdeleFundamentalDomain_unique_translate (u.symm a i).toAdd
    refine ⟨e q, (hmem q).mpr hq, fun h hh ↦ ?_⟩
    obtain ⟨r, rfl⟩ := e.surjective h
    exact congrArg e (funext fun i ↦ huniq i (r i) ((hmem r).mp hh i))
  have hFund : IsFundamentalDomain H.op D μ := IsFundamentalDomain.mk' hD.nullMeasurableSet htiles
  obtain ⟨-, hclosed, hdiscrete, -⟩ := adele_additive_quotient.{_, 0} F
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable H := (Set.countable_range (algebraMap F 𝔸[F])).to_subtype
  obtain ⟨η, hη, hηmass⟩ := additiveTamagawaMeasure_quotientVolume F
  have hμD : μ D = 1 := (weilQuotientMeasure_univ_eq_measure_fundamentalDomain hclosed hη
    (hηmass.trans_ne ENNReal.one_ne_top) hFund hprecompact (fun a ↦ (htiles a).exists)).symm.trans hηmass
  have hmD : m D = 1 := (huemb.map_apply ν D).trans (by
    rw [show u ⁻¹' D = E from Set.preimage_image_eq _ u.injective, hνE])
  have hscale := Measure.isMulLeftInvariant_eq_smul m μ
  have hc : (m.haarScalarFactor μ : ℝ≥0∞) = 1 := by
    have h := congrArg (fun η : Measure G ↦ η D) hscale
    change m D = (m.haarScalarFactor μ : ℝ≥0∞) * μ D at h
    rw [hmD, hμD, mul_one] at h
    exact h.symm
  refine ⟨huemb.measurable, ?_⟩
  change m = μ
  rw [hscale, ENNReal.coe_eq_one.mp hc, one_smul]

/-- Paper: Example A.3.1.9, p. 558. For a finite power of the rational adeles, the
product of the rational pairings identifies the power with its Pontryagin dual and
sends the product Haar measure to the Plancherel measure. -/
theorem ratAdeleProduct_plancherel (n : ℕ) :
    let G := Fin n → Multiplicative 𝔸[ℚ]
    let μ : Measure G := Measure.pi fun _ ↦ additiveTamagawaMeasure ℚ
    letI : MeasurableSpace (PontryaginDual G) := borel _
    ∃ e : G ≃ₜ* PontryaginDual G,
      (∀ x y, e x y = ∏ i, ratAdeleStandardCharacter ((x i).toAdd * (y i).toAdd)) ∧
        IsLCAPlancherelMeasure μ (μ.map e) := by
  classical
  let G := Multiplicative 𝔸[ℚ]
  let P := Fin n → G
  let m : Measure G := additiveTamagawaMeasure ℚ
  let : m.IsHaarMeasure := additiveTamagawaMeasure_isHaar ℚ
  let : SigmaFinite m := inferInstance
  let μ : Measure P := Measure.pi fun _ ↦ m
  let : μ.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : μ.Regular := inferInstance
  let : MeasurableSpace (PontryaginDual P) := borel _
  let : BorelSpace (PontryaginDual P) := ⟨rfl⟩
  obtain ⟨e₀, he₀⟩ := exists_ratAdeleDualEquiv
  let pr (i : Fin n) : P →ₜ* G := ⟨Pi.evalMonoidHom (fun _ ↦ G) i, continuous_apply i⟩
  let j (i : Fin n) : G →ₜ* P :=
    ⟨MonoidHom.mulSingle (fun _ ↦ G) i, continuous_mulSingle (A := fun _ ↦ G) i⟩
  let χ (x : P) : PontryaginDual P := ∏ i, PontryaginDual.map (pr i) (e₀ (x i))
  have hχ (x y : P) : χ x y = ∏ i, e₀ (x i) (y i) := by
    let ev : PontryaginDual P →* Circle := ⟨⟨fun ψ ↦ ψ y, rfl⟩, fun _ _ ↦ rfl⟩
    exact map_prod ev _ _
  let coords (ψ : PontryaginDual P) : P := fun i ↦ e₀.symm (PontryaginDual.map (j i) ψ)
  let e : P ≃ₜ* PontryaginDual P :=
    { toFun := χ
      invFun := coords
      left_inv := by
        intro x
        funext i
        apply e₀.injective
        change e₀ (e₀.symm (PontryaginDual.map (j i) (χ x))) = e₀ (x i)
        rw [e₀.apply_symm_apply]
        apply PontryaginDual.ext
        intro y
        change χ x (Pi.mulSingle i y) = _
        rw [hχ, Finset.prod_eq_single i]
        · rw [Pi.mulSingle_eq_same]
        · intro k _ hk
          rw [Pi.mulSingle_eq_of_ne' hk.symm, map_one]
        · simp
      right_inv := fun ψ ↦ PontryaginDual.ext fun x ↦ by
        rw [hχ]
        simp only [coords, e₀.apply_symm_apply, PontryaginDual.map_apply]
        change (∏ i, ψ (Pi.mulSingle i (x i))) = ψ x
        rw [← map_prod, Finset.univ_prod_mulSingle]
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change χ (x * y) z = χ x z * χ y z
        rw [hχ, hχ, hχ, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        change e₀ (x i * y i) (z i) = _
        rw [map_mul]
        rfl
      continuous_toFun := continuous_finsetProd _ fun i _ ↦
        (PontryaginDual.map (pr i)).continuous.comp (e₀.continuous.comp (continuous_apply i))
      continuous_invFun := continuous_pi fun i ↦
        e₀.symm.continuous.comp (PontryaginDual.map (j i)).continuous }
  have hp (x y : P) : e x y = ∏ i, ratAdeleStandardCharacter ((x i).toAdd * (y i).toAdd) := by
    change χ x y = _
    rw [hχ]
    exact Finset.prod_congr rfl fun i _ ↦ he₀ (x i).toAdd (y i).toAdd
  refine ⟨e, hp, ?_⟩
  let g : G → ℂ := fun x ↦ ratAdeleGaussian x.toAdd
  let f : P → ℂ := fun x ↦ ∏ i, g (x i)
  obtain ⟨hg₁, hg₂⟩ := ratAdeleGaussian_integrable_memLp
  have hg₁' : Integrable g m := hg₁
  have hg₂' : MemLp g 2 m := hg₂
  have hf₁ : Integrable f μ := Integrable.fintype_prod (fun _ ↦ hg₁')
  have hf₂ : MemLp f 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hf₁.aestronglyMeasurable).mpr
    have hsq : Integrable (fun x ↦ ‖g x‖ ^ 2) m :=
      (memLp_two_iff_integrable_sq_norm hg₁'.aestronglyMeasurable).mp hg₂'
    simpa only [f, Complex.norm_prod, Finset.prod_pow] using
      (Integrable.fintype_prod (ι := Fin n) (fun _ ↦ hsq))
  have hfourier : lcaFourier μ f ∘ e = f := by
    funext y
    let k (i : Fin n) (x : G) := g x *
      star (ratAdeleStandardCharacter (x.toAdd * (y i).toAdd) : ℂ)
    calc
      _ = ∫ x : P, ∏ i, k i (x i) ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x ↦ ?_
        change (∏ i, g (x i)) * star (Circle.coeHom (e y x)) = _
        simp only [hp, map_prod, star_prod, k, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [mul_comm (y i).toAdd]
        rfl
      _ = ∏ i, ∫ x, k i x ∂m := integral_fintype_prod_eq_prod k
      _ = _ := Finset.prod_congr rfl fun i _ ↦
        congrFun tamagawaFourier_ratAdeleGaussian (y i).toAdd
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
    have hg : g 1 = 1 := by
      change ratAdeleGaussian 0 = 1
      have hz : ratRealPart 0 = 0 :=
        map_zero (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
      simp [ratAdeleGaussian, hz, (integralAdelesOutside ℚ ∅).zero_mem]
    have hf : f (1 : P) = 1 := Finset.prod_eq_one fun _ _ ↦ hg
    have h := congrFun hfourier (1 : P)
    change lcaFourier μ f (e 1) = f 1 at h
    rw [hf, lcaFourier, integral_congr_ae (hae.mono fun x hx ↦ by
      change f x = 0 at hx
      rw [hx, zero_mul]), integral_zero] at h
    exact zero_ne_one h
  obtain ⟨η, hη, _⟩ := lcaPlancherelMeasure_existsUnique μ
  let : η.IsHaarMeasure := hη.1
  let : η.Regular := hη.2.1
  let ν := μ.map e
  let : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map e.toHomeomorph
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, η = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul_of_regular η ν⟩
  have he : MeasurableEmbedding (e : P → PontryaginDual P) := e.toHomeomorph.measurableEmbedding
  have hLp : MemLp (lcaFourier μ f) 2 ν := by
    apply he.memLp_map_measure_iff.mpr
    rw [hfourier]
    exact hf₂
  have hNorm := (hη.2.2 f hf₁ hf₂).2
  have hMap : eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ :=
    he.eLpNorm_map_measure.trans (congrArg (fun k ↦ eLpNorm k 2 μ) hfourier)
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp) _ _ hLp.aestronglyMeasurable, hMap] at hNorm
  have hr : 0 < ((2 : ℝ≥0∞).toReal)⁻¹ := by norm_num
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 := by
    apply (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp
    rw [one_mul, ← ENNReal.coe_rpow_of_nonneg _ hr.le]
    exact hNorm
  have hc₁ : c = 1 := ENNReal.coe_injective (by
    apply (ENNReal.strictMono_rpow_of_pos hr).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot)
  change IsLCAPlancherelMeasure μ ν
  simpa only [hc, hc₁, one_smul] using hη

/-- Paper: Example A.3.1.9, p. 558. The global additive Tamagawa measure is self-dual
under the pairing from the trace character. -/
theorem additiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (additiveTamagawaMeasure F) (adeleStandardCharacter F) := by
  let P := Fin (Module.finrank ℚ F) → Multiplicative 𝔸[ℚ]
  let G := Multiplicative 𝔸[F]
  let ν : Measure P := Measure.pi fun _ ↦ additiveTamagawaMeasure ℚ
  let μ : Measure G := additiveTamagawaMeasure F
  let : MeasurableSpace (PontryaginDual P) := borel _
  let : BorelSpace (PontryaginDual P) := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨u, v, hu, hv, hpair⟩ := exists_adeleTrace_dualCoordinates F
  have huμ : MeasurePreserving u ν μ := adeleTamagawaMeasurePreserving_of_diagonal F u hu
  have hvμ : MeasurePreserving v ν μ := adeleTamagawaMeasurePreserving_of_diagonal F v hv
  obtain ⟨d, hd, hν⟩ := ratAdeleProduct_plancherel (Module.finrank ℚ F)
  let u₁ : P →ₜ* G := ⟨u.toMulEquiv.toMonoidHom, u.continuous⟩
  let u₂ : G →ₜ* P := ⟨u.symm.toMulEquiv.toMonoidHom, u.symm.continuous⟩
  let t : PontryaginDual P ≃ₜ* PontryaginDual G :=
    { toFun := PontryaginDual.map u₂
      invFun := PontryaginDual.map u₁
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (u.symm_apply_apply x)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (u.apply_symm_apply x)
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := (PontryaginDual.map u₂).continuous
      continuous_invFun := (PontryaginDual.map u₁).continuous }
  let e := v.symm.trans (d.trans t)
  refine ⟨e, fun x y ↦ ?_, ?_⟩
  · change d (v.symm (Multiplicative.ofAdd x)) (u.symm (Multiplicative.ofAdd y)) = _
    rw [hd]
    simp_rw [mul_comm ((v.symm (Multiplicative.ofAdd x) _) : Multiplicative 𝔸[ℚ]).toAdd]
    rw [← hpair, u.apply_symm_apply, v.apply_symm_apply, mul_comm]
    rfl
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure := additiveTamagawaMeasure_isHaar F
  let : μ.Regular := hμ.2.1
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  have hFourier : lcaFourier μ f ∘ t = lcaFourier ν (f ∘ u) := by
    funext χ
    let k : G → ℂ := fun x ↦ f x * star (t χ x : ℂ)
    change (∫ x, k x ∂μ) = _
    calc
      _ = ∫ x : P, k (u x) ∂ν :=
        (huμ.integral_comp u.toHomeomorph.measurableEmbedding k).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        congrArg (fun z : P ↦ f (u x) * star (χ z : ℂ)) (u.symm_apply_apply x))
  have hmap : μ.map e = (ν.map d).map t := by
    have he : Measurable (e : G → PontryaginDual G) := e.continuous.measurable
    have ht : Measurable (t : PontryaginDual P → PontryaginDual G) := t.continuous.measurable
    have hd' : Measurable (d : P → PontryaginDual P) := d.continuous.measurable
    rw [← hvμ.map_eq, Measure.map_map he hvμ.measurable, Measure.map_map ht hd']
    congr 1
    funext x
    change t (d (v.symm (v x))) = t (d x)
    rw [v.symm_apply_apply]
  have h := hν.2.2 (f ∘ u) (huμ.integrable_comp_of_integrable hf₁)
    (hf₂.comp_measurePreserving huμ)
  have ht : MeasurableEmbedding (t : PontryaginDual P → PontryaginDual G) :=
    t.toHomeomorph.measurableEmbedding
  rw [hmap]
  refine ⟨ht.memLp_map_measure_iff.mpr (hFourier ▸ h.1), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ t) 2 (ν.map d) := ht.eLpNorm_map_measure
    _ = eLpNorm (f ∘ u) 2 ν := hFourier.symm ▸ h.2
    _ = _ := eLpNorm_comp_measurePreserving hf₂.aestronglyMeasurable huμ

end AdeleSelfDuality

/-- Paper: Example A.3.1.10, p. 558. The local character is the finite component
of the adelic trace character, evaluated on an adele supported at the given place.
Deviation: It is expressed by restriction of the adelic trace, whose component is the local trace. -/
def finiteLocalStandardCharacter (v : Primes(F)) (x : v.adicCompletion F) : Circle :=
  adeleStandardCharacter F (0, RestrictedProduct.single (fun w : Primes(F) ↦
    w.adicCompletionIntegers F) v x)

section FiniteLocalTrace

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct

local notation "O(" F ")" => (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletionIntegers F w)
local notation "K(" F ")" => (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletion F w)

/-- Projection to a finite coordinate of the adele ring. -/
private def finiteAdeleEval (v : Primes(F)) : 𝔸[F] →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (K(F)) v).comp (RingHom.snd _ _)

/-- Inclusion of a finite completion as the adeles supported at its place. -/
private def finiteAdeleSingle (v : Primes(F)) : v.adicCompletion F →+ 𝔸[F] where
  toFun x := (0, RestrictedProduct.single (O(F)) v x)
  map_zero' := Prod.ext rfl (RestrictedProduct.single_zero (O(F)) v)
  map_add' x y := Prod.ext (zero_add _).symm (RestrictedProduct.single_add (O(F)) v x y)

/-- Inserting an element at one finite place is continuous for the restricted product topology. -/
private theorem continuous_finiteAdeleSingle (v : Primes(F)) :
    Continuous (finiteAdeleSingle F v) := by
  let S : Set Primes(F) := {v}ᶜ
  let hS : Filter.cofinite ≤ Filter.principal S := by simp [S, Filter.le_principal_iff]
  let s (x : v.adicCompletion F) : Πʳ w, [K(F) w, O(F) w]_[Filter.principal S] :=
    ⟨Pi.single v x, by
      rw [Filter.eventually_principal]
      intro w hw
      exact (Pi.single_eq_of_ne hw x).symm ▸ (O(F) w).zero_mem⟩
  have hs : Continuous s := RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hs)

/-- Multiplying an adele supported at one finite place uses only that coordinate of the multiplier. -/
private theorem finiteAdeleSingle_mul (v : Primes(F)) (a : 𝔸[F]) (x : v.adicCompletion F) :
    finiteAdeleSingle F v (finiteAdeleEval F v a * x) = a * finiteAdeleSingle F v x :=
  Prod.ext (mul_zero _).symm (RestrictedProduct.mul_single (O(F)) v x a.2)

/-- The rational adelic embedding induces the local embedding on a finite coordinate. -/
private theorem exists_finiteAdeleEmbedding (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
    ∃ j : u.adicCompletion ℚ →+* v.adicCompletion F,
      Continuous j ∧ (∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) ∧
      ∀ a : 𝔸[ℚ], finiteAdeleEval F v (rationalAdeleEmbedding F a) =
        j (finiteAdeleEval ℚ u a) := by
  let p := finiteAdeleEval ℚ u
  let s := finiteAdeleSingle ℚ u
  let f := (finiteAdeleEval F v).comp (rationalAdeleEmbedding F)
  have hps (x) : p (s x) = x := RestrictedProduct.single_eq_same (O(ℚ)) u x
  have hfactor (a) : f a = f (s (p a)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (rationalAdeleEmbedding_spec F).2.2.2 u v hu
    change p (a - s (p a)) = 0
    rw [map_sub, hps, sub_self]
  let j : u.adicCompletion ℚ →+* v.adicCompletion F :=
    { toFun := fun x ↦ f (s x)
      map_zero' := by rw [map_zero, map_zero]
      map_one' := by rw [← (map_one p), ← hfactor, map_one]
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_mul' := fun x y ↦ by
        have hm := finiteAdeleSingle_mul ℚ u (s x) y
        change s (p (s x) * y) = s x * s y at hm
        rw [hps] at hm
        rw [hm, map_mul] }
  have hj : Continuous j := ((RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (rationalAdeleEmbedding_spec F).1)).comp
      (continuous_finiteAdeleSingle ℚ u)
  refine ⟨j, hj, ?_, hfactor⟩
  intro r
  have ha := hfactor (algebraMap ℚ 𝔸[ℚ] r)
  rw [show f (algebraMap ℚ 𝔸[ℚ] r) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F r) from
    congrArg (finiteAdeleEval F v) ((rationalAdeleEmbedding_spec F).2.1 r)] at ha
  exact ha.symm

/-- Paper: Example A.3.1.10, p. 558. At a finite place the trace character
agrees with the standard p-adic character composed with the local field trace. -/
theorem finiteLocalStandardCharacter_trace (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
    let p := Rat.HeightOneSpectrum.primesEquiv u
    letI : Fact p.val.Prime := ⟨p.property⟩
    ∃ j : u.adicCompletion ℚ →+* v.adicCompletion F,
      Continuous j ∧ (∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) ∧
      letI := j.toAlgebra
      Module.Finite (u.adicCompletion ℚ) (v.adicCompletion F) ∧
        ∀ x : v.adicCompletion F, finiteLocalStandardCharacter F v x =
          padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv u
            (Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) x)) := by
  dsimp only
  obtain ⟨j, hj, hdiag, hlocal⟩ := exists_finiteAdeleEmbedding F v u hu
  let := (rationalAdeleEmbedding F).toAlgebra
  let := j.toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  let p := finiteAdeleEval ℚ u
  let s := finiteAdeleSingle F v
  have hp : Surjective p := fun z ↦
    ⟨finiteAdeleSingle ℚ u z, RestrictedProduct.single_eq_same (O(ℚ)) u z⟩
  obtain ⟨hfinite, htrace⟩ := trace_of_algebra_projection b p hp (finiteAdeleEval F v) s
    (fun z ↦ RestrictedProduct.single_eq_same (O(F)) v z) hlocal (finiteAdeleSingle_mul F v)
  refine ⟨j, hj, hdiag, hfinite, fun x ↦ ?_⟩
  let e := finiteAdeleSingle ℚ u 1
  let t := Algebra.trace 𝔸[ℚ] 𝔸[F] (s x)
  -- The scalar adele supported at u acts as the identity on the summand at v.
  have he : e • s x = s x := by
    change rationalAdeleEmbedding F e * s x = s x
    rw [← finiteAdeleSingle_mul, hlocal]
    have hp₁ : p e = 1 := RestrictedProduct.single_eq_same (O(ℚ)) u 1
    change s (j (p e) * x) = s x
    rw [hp₁, map_one, one_mul]
  have ht : e * t = t := by
    change e • Algebra.trace 𝔸[ℚ] 𝔸[F] (s x) = t
    rw [← map_smul, he]
  have ht_single : finiteAdeleSingle ℚ u (p t) = t := by
    have h := finiteAdeleSingle_mul ℚ u t 1
    change finiteAdeleSingle ℚ u (p t * 1) = t * e at h
    rwa [mul_one, mul_comm t e, ht] at h
  change ratAdeleStandardCharacter t = ratLocalCharacter u
    (Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) x)
  rw [← htrace x]
  conv_lhs => rw [← ht_single]
  change Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace 0) *
    (∏ᶠ w : Primes(ℚ), ratLocalCharacter w (RestrictedProduct.single (O(ℚ)) u (p t) w)) =
      ratLocalCharacter u (p t)
  rw [map_zero, mul_zero, Circle.exp_zero, one_mul, finprod_eq_single _ u]
  · rw [RestrictedProduct.single_eq_same]
  · intro w hw
    rw [RestrictedProduct.single_eq_of_ne (O(ℚ)) _ hw]
    exact (ratLocalCharacter_eq_one w 0).2 ((O(ℚ) w).zero_mem)

end FiniteLocalTrace

/-- Paper: Example A.3.1.10, p. 558. The local measure is self-dual under
the local trace character. -/
theorem finiteLocalAdditiveTamagawaMeasure_selfDual (v : Primes(F)) :
    IsTamagawaSelfDual (finiteLocalAdditiveTamagawaMeasure F v)
      (finiteLocalStandardCharacter F v) := by sorry

/-- Paper: Example A.3.1.10, p. 558. The Fourier transform of the local integer-ring
indicator is the inverse-different indicator multiplied by the mass of the integer ring.
Deviation: The inverse different is the closed ball of normalized radius `qᵥ^dᵥ`. -/
theorem finiteLocalTamagawaFourier_integers (v : Primes(F)) :
    tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v)
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) =
      (differentMass(F, v).toReal : ℂ) •
        ({x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)}.indicator
          (fun _ ↦ (1 : ℂ))) :=
  by sorry

/-- Paper: Example A.3.1.11, p. 559. The standard S-local character is the product
over all archimedean places and the finite places in S, as in (A.3.1.9).
Deviation: Each local character is expressed as a restriction of the global trace character. -/
def sAdeleStandardCharacter (a : SAdeleRing F S) : Circle :=
  (∏ w : InfinitePlace F, adeleStandardCharacter F (Pi.single w (a.1 w), 0)) *
    ∏ v : S, finiteLocalStandardCharacter F v.val (a.2 v)

/-- The standard p-adic character is trivial at zero. -/
theorem padicStandardCharacter_zero (p : ℕ) [Fact p.Prime] : padicStandardCharacter p 0 = 1 := by
  have h (n : ℕ) (hx : ‖(p : ℚ_[p]) ^ n * 0‖ ≤ 1) :
      PadicInt.toZModPow n (⟨(p : ℚ_[p]) ^ n * 0, hx⟩ : ℤ_[p]) = 0 := by
    rw [show (⟨(p : ℚ_[p]) ^ n * 0, hx⟩ : ℤ_[p]) = (0 : ℤ_[p]) from Subtype.ext (mul_zero _)]
    exact map_zero _
  simp only [padicStandardCharacter]
  rw [h]
  simp

/-- The rational adelic character is trivial at zero. -/
theorem ratAdeleStandardCharacter_zero : ratAdeleStandardCharacter 0 = 1 := by
  have h₁ : (0 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 0 := rfl
  have h₂ (v : Primes(ℚ)) : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 0 := rfl
  simp [ratAdeleStandardCharacter, h₁, h₂, padicStandardCharacter_zero]

/-- The standard adelic character is trivial at zero. -/
theorem adeleStandardCharacter_zero : adeleStandardCharacter F 0 = 1 := by
  simp [adeleStandardCharacter, ratAdeleStandardCharacter_zero]

/-- The local character at a finite place is trivial at zero. -/
theorem finiteLocalStandardCharacter_zero (v : Primes(F)) :
    finiteLocalStandardCharacter F v 0 = 1 := by
  have h : (RestrictedProduct.single (fun w : Primes(F) ↦ w.adicCompletionIntegers F) v
      (0 : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F) = 0 :=
    RestrictedProduct.single_zero _ _
  simp only [finiteLocalStandardCharacter, h]
  exact adeleStandardCharacter_zero F

/-- Paper: Example A.3.1.11, p. 559. On an S-adele supported at a single finite
place, the product character restricts to the trace character at that place. -/
theorem sAdeleStandardCharacter_single_finite (v : S) (x : v.val.adicCompletion F) :
    sAdeleStandardCharacter F S (0, Pi.single v x) = finiteLocalStandardCharacter F v.val x := by
  have h₀ (w : InfinitePlace F) : (0 : InfiniteAdeleRing F) w = 0 := rfl
  have h₁ (w : InfinitePlace F) :
      adeleStandardCharacter F (Pi.single w ((0 : InfiniteAdeleRing F) w), 0) = 1 := by
    rw [h₀, Pi.single_zero]
    exact adeleStandardCharacter_zero F
  unfold sAdeleStandardCharacter
  dsimp only
  rw [Finset.prod_eq_one fun w _ ↦ h₁ w, one_mul, Finset.prod_eq_single v]
  · rw [Pi.single_eq_same]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, finiteLocalStandardCharacter_zero]
  · simp

-- TODO(paper-gap): In Example A.3.1.11, the lattice fails to annihilate itself
-- under (A.3.1.10) with the real and p-adic signs as printed. For F = ℚ and
-- S = {∞, 3}, the pairing of 1/3 with 1 is exp(4πi/3).
-- The proof also reverses the ambient group of the annihilator for (A.3.1.11).

/-- Paper: Example A.3.1.11, p. 559. The standard S-local character takes the
value one on every diagonally embedded S-integer.
Deviation: This consequence of the lattice pairing holds for every finite S with the
finite-place sign correction of ERRATA F13. -/
theorem sAdeleStandardCharacter_sInteger (x : (S : Set (Primes(F))).integer F) :
    sAdeleStandardCharacter F S (adeleProjection F S (integralAdeleDiagonal F S x).val) = 1 :=
  by sorry

/-- Paper: Example A.3.1.11, p. 559. The diagonal S-integers are their own annihilator
for the standard character pairing when S contains every finite prime dividing the different.
Deviation: The pairing uses the finite-place sign correction of ERRATA F13. -/
theorem sInteger_annihilator_iff
    (hS : ∀ v : Primes(F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (y : SAdeleRing F S) :
    (∀ x : (S : Set (Primes(F))).integer F,
        sAdeleStandardCharacter F S
          (adeleProjection F S (integralAdeleDiagonal F S x).val * y) = 1) ↔
      ∃ x : (S : Set (Primes(F))).integer F,
        y = adeleProjection F S (integralAdeleDiagonal F S x).val := by sorry

/-- Paper: Definition A.3.2.1, p. 559. The measure `dt/t` on the positive
reals is the pushforward of real Lebesgue measure along the exponential. -/
def positiveRealHaar : Measure ℝ≥0ˣ :=
  Measure.map (fun x : ℝ ↦
    Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) volume

/-- Paper: §A.3.3.1, p. 561. The mass of the interval with endpoints 1 and T
under `dt/t` is the logarithm of T for T at least 1. -/
theorem positiveRealHaar_interval (T : ℝ≥0ˣ) (hT : 1 ≤ (T.val : ℝ)) :
    positiveRealHaar {t | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} =
      ENNReal.ofReal (Real.log (T.val : ℝ)) := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hset : MeasurableSet {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} :=
    measurableSet_Icc.preimage (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  change (volume.map e) _ = _
  rw [Measure.map_apply he hset]
  have hpre : e ⁻¹' {t | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} = Icc 0 (Real.log (T.val : ℝ)) := by
    ext x
    change (1 ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) ≤ _) ↔ _
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.one_le_exp_iff,
      ← Real.le_log_iff_exp_le (zero_lt_one.trans_le hT)]
    rfl
  rw [hpre, Real.volume_Icc, sub_zero]

local notation "classVolume(" F ")" =>
  ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Nat.cast (NumberField.classNumber F) *
    Units.regulator F / (Real.sqrt (Nat.cast (Int.natAbs (NumberField.discr F))) *
      Nat.cast (Units.torsionOrder F)))

/-- Paper: Definition A.3.2.1, pp. 559–560. There is a unique compatible triple
of regular Haar measures on the ideles, the idele classes and the norm-one
classes. The quotient normalizations use counting measure and `dt/t`, respectively. -/
theorem multiplicativeTamagawaMeasures_existsUnique :
    ∃! m : Measure 𝕀[F] × Measure C[F] × Measure C₁[F],
      m.1.IsHaarMeasure ∧ m.1.Regular ∧
        IsWeilQuotientMeasure P[F] m.1 Measure.count m.2.1 ∧
        m.2.2.IsHaarMeasure ∧ m.2.2.Regular ∧ m.2.2 univ = classVolume(F) ∧
        IsWeilQuotientMeasure C₁[F] m.2.1 m.2.2
          (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) :=
  by sorry

/-- Paper: Definition A.3.2.1, pp. 559–560. The global multiplicative Tamagawa
measure uses the prescribed mass on the norm-one idele classes. -/
def multiplicativeTamagawaMeasure : Measure 𝕀[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.1

/-- Paper: Definition A.3.2.1, pp. 559–560. The class measure is the quotient
of the idelic Tamagawa measure by counting measure on the principal ideles. -/
def ideleClassTamagawaMeasure : Measure C[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.2.1

/-- Paper: Definition A.3.2.1, pp. 559–560. Disintegrating the class measure
against `dt/t` gives the Tamagawa measure on the norm-one classes. -/
def normOneIdeleClassTamagawaMeasure : Measure C₁[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.2.2

/-- Paper: Definition A.3.2.1, pp. 559–560. The global idelic and class measures
satisfy Weil's formula with counting measure on the principal ideles. -/
theorem ideleClassTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure P[F] (multiplicativeTamagawaMeasure F)
      Measure.count (ideleClassTamagawaMeasure F) := by sorry

/-- Paper: Definition A.3.2.1, p. 560. The norm-one idele classes have the
mass in (A.3.2.1), expressed with Mathlib's regulator and class number. -/
theorem normOneIdeleClassTamagawaMeasure_volume :
    normOneIdeleClassTamagawaMeasure F univ = classVolume(F) := by sorry

/-- Paper: Definition A.3.2.1, pp. 559–560. The class and norm-one class measures
satisfy Weil's formula with `dt/t` on the norm quotient. -/
theorem normOneIdeleClassTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure C₁[F] (ideleClassTamagawaMeasure F)
      (normOneIdeleClassTamagawaMeasure F)
      (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) := by sorry

/-- Paper: Definition A.3.2.2(1), p. 560. The multiplicative measure at an infinite
place is the additive measure weighted by the reciprocal normalized absolute value. -/
def infiniteLocalMultiplicativeTamagawaMeasure (v : InfinitePlace F) : Measure v.Completionˣ :=
  ((infiniteLocalAdditiveTamagawaMeasure F v).withDensity
    (fun x ↦ (↑(‖x‖₊ ^ v.mult) : ℝ≥0∞)⁻¹)).comap Units.val

/-- Paper: Definition A.3.2.2(1), p. 560. On units at a real place with coordinate
between 1 and 2 the measure is the integral of `dt/t`, namely `log 2`. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_real_interval (v : InfinitePlace F)
    (h : v.IsReal) :
    infiniteLocalMultiplicativeTamagawaMeasure F v
      {x | ringEquivRealOfIsReal h x.val ∈ Icc 1 2} = ENNReal.ofReal (Real.log 2) := by sorry

/-- Paper: Definition A.3.2.2(2), p. 560. Scale local multiplicative Haar
measure so that the integer units have the inverse square root different-norm mass. -/
def finiteLocalMultiplicativeTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F)ˣ :=
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F).units) • μ

/-- Paper: Definition A.3.2.2(2), p. 560. The local multiplicative measure assigns
the mass in (A.3.2.2) to the integer units. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_integerUnits (v : Primes(F)) :
    finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units =
      differentMass(F, v) := by sorry

/-- Paper: Lemma A.3.2.3, p. 560. At a finite place the multiplicative
measure is the weighted additive measure times `qᵥ / (qᵥ - 1)`. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity (v : Primes(F)) :
    finiteLocalMultiplicativeTamagawaMeasure F v =
      (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ℝ≥0∞) •
        ((finiteLocalAdditiveTamagawaMeasure F v).withDensity
          (fun x ↦ (↑‖x‖₊ : ℝ≥0∞)⁻¹)).comap Units.val := by sorry

local notation "∞unitAt" => fun w : InfinitePlace F ↦
  Units.map (RingHom.toMonoidHom (RingHom.comp (Pi.evalRingHom InfinitePlace.Completion w)
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))))
local notation "finiteUnitAt" => fun v : Primes(F) ↦
  Units.map (RingHom.toMonoidHom (RingHom.comp
    (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletion F w) v)
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))))

/-- Paper: Lemma A.3.2.4, p. 560. The global multiplicative measure is the
restricted product of the local measures, evaluated on rectangles with integer-unit tails. -/
theorem multiplicativeTamagawaMeasure_restrictedProduct
    (B : (w : InfinitePlace F) → Set w.Completionˣ) (hB : ∀ w, MeasurableSet (B w))
    (U : (v : S) → Set (v.val.adicCompletion F)ˣ) (hU : ∀ v, MeasurableSet (U v)) :
    multiplicativeTamagawaMeasure F
        {g | (∀ w, (∞unitAt) w g ∈ B w) ∧ (∀ v : S, (finiteUnitAt) v.val g ∈ U v) ∧
          ∀ v : Primes(F), v ∉ S → (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} =
      (∏ w : InfinitePlace F, infiniteLocalMultiplicativeTamagawaMeasure F w (B w)) *
        (∏ v : S, finiteLocalMultiplicativeTamagawaMeasure F v.val (U v)) *
          ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val) := by sorry

/-- Paper: §A.3.3.1, p. 561. Weil's formula for the idelic norm and `dt/t`
determines a unique regular Haar measure on the norm-one ideles. -/
theorem normOneIdeleTamagawaMeasure_existsUnique :
    ∃! ν : Measure N[F], ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure N[F] (multiplicativeTamagawaMeasure F) ν
        (positiveRealHaar.comap (QuotientGroup.kerLift (ideleNorm F))) := by sorry

/-- Paper: §A.3.3.1, p. 561. Normalize the Haar measure on the norm-one
ideles by the global multiplicative Tamagawa measure and `dt/t`. -/
def normOneIdeleTamagawaMeasure : Measure N[F] :=
  (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose

/-- Paper: §A.3.3.1, p. 561. Under any continuous homomorphic section, the
idelic decomposition transports the product of `dt/t` and the norm-one idele measure. -/
theorem multiplicativeTamagawaMeasure_normProduct (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s)
    (hn : RightInverse s (ideleNorm F)) :
    (positiveRealHaar.prod (normOneIdeleTamagawaMeasure F)).map
        (fun tg : ℝ≥0ˣ × N[F] ↦ s tg.1 * tg.2.val) =
      multiplicativeTamagawaMeasure F := by sorry

/-- Paper: §A.3.3.1, p. 561. A section strip over the idelic fundamental domain
has volume `log T` times the volume of the norm-one idele classes.
Deviation: The formula uses `T ≥ 1` so that the logarithm equals the interval mass. -/
theorem multiplicativeTamagawaMeasure_sectionStrip
    (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s) (hn : RightInverse s (ideleNorm F))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (r : CommRing.Pic (𝓞 F) → N[F]) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c) (T : ℝ≥0ˣ) (hT : 1 ≤ (T.val : ℝ)) :
    multiplicativeTamagawaMeasure F
      {g | ∃ t : ℝ≥0ˣ, (t.val : ℝ) ∈ Icc 1 (T.val : ℝ) ∧
        ∃ x ∈ ideleFundamentalDomain F b v₀ σ r, g = s t * (x : N[F]).val} =
      ENNReal.ofReal (Real.log (T.val : ℝ)) * normOneIdeleClassTamagawaMeasure F univ := by sorry

/-- Paper: Definition A.3.4.1(1), p. 561. The S-local additive Tamagawa
measure is the product of all archimedean and the selected finite local measures. -/
def sAdditiveTamagawaMeasure : Measure (SAdeleRing F S) :=
  (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
    (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa
measure is the finite product of the local measures on the unit groups. -/
def sMultiplicativeTamagawaMeasure : Measure 𝕀ₛ :=
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val))).map
    (fun x ↦ e.symm (eArch.symm x.1, eS.symm x.2))

/-- Paper: Definition A.3.4.1(2), p. 561. The mass of an S-local unit rectangle
is the product of the archimedean coordinate masses and the finite integer-unit masses. -/
theorem sMultiplicativeTamagawaMeasure_integerUnits
    (B : (w : InfinitePlace F) → Set w.Completionˣ) (hB : ∀ w, MeasurableSet (B w)) :
    sMultiplicativeTamagawaMeasure F S
        {g | (∀ w, Units.map ((Pi.evalRingHom InfinitePlace.Completion w).comp
          (RingHom.fst _ _)).toMonoidHom g ∈ B w) ∧
            ∀ v : S, Units.map ((Pi.evalRingHom (fun u : S ↦ u.val.adicCompletion F) v).comp
              (RingHom.snd _ _)).toMonoidHom g ∈ (v.val.adicCompletionIntegers F).units} =
      (∏ w : InfinitePlace F, infiniteLocalMultiplicativeTamagawaMeasure F w (B w)) *
        ∏ v : S, differentMass(F, v.val) := by sorry

/-- Paper: Definition A.3.4.1(3)(1), p. 561. The Haar measure on the norm-one
S-ideles is uniquely determined by Weil's formula using the product and `dt/t`. -/
theorem sNormOneIdeleTamagawaMeasure_existsUnique :
    ∃! ν : Measure Nₛ, ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure Nₛ (sMultiplicativeTamagawaMeasure F S) ν
        (positiveRealHaar.comap (QuotientGroup.kerLift (sIdeleNorm F S))) := by sorry

/-- Paper: Definition A.3.4.1(3)(1), p. 561. Use the Weil normalization of
the product measure on the norm-one S-ideles. -/
def sNormOneIdeleTamagawaMeasure : Measure Nₛ :=
  (sNormOneIdeleTamagawaMeasure_existsUnique F S).exists.choose

/-- Paper: Definition A.3.4.1(3)(1), p. 561. The chosen norm-one measure
satisfies Weil's formula with `dt/t` on the norm quotient. -/
theorem sNormOneIdeleTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure Nₛ (sMultiplicativeTamagawaMeasure F S)
      (sNormOneIdeleTamagawaMeasure F S)
      (positiveRealHaar.comap (QuotientGroup.kerLift (sIdeleNorm F S))) := by sorry

-- TODO(paper-gap): Definition A.3.4.1(3)(2)–(3) prescribes a measure on the
-- local S-ideles but takes the quotient of the larger group in (A.1.5.7).
-- The latter includes the product of the integer-unit groups outside S.

/-- Paper: Example A.3.1.11, p. 559, and Remark A.3.4.2, p. 562. The S-local
product is self-dual under the pairing from the product character. -/
theorem sAdditiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S) := by sorry

-- TODO(paper-gap): The last sentence of Remark A.3.4.2 reverses the criterion
-- for mass one. The preceding prime-to-S volume is one precisely when S contains
-- all the ramified finite places.

/-- Paper: Remark A.3.4.2, p. 562. The additive quotient mass of the product
measure is the square root of the part of the different norm outside S.
Deviation: The prime-to-S part is taken over places of the number field. -/
theorem sAdditiveTamagawaMeasure_quotientVolume :
    ∃ ν : Measure (Multiplicative (SAdeleRing F S) ⧸ Aₛ),
      IsWeilQuotientMeasure Aₛ (show Measure (Multiplicative (SAdeleRing F S)) from
        sAdditiveTamagawaMeasure F S) Measure.count ν ∧
      ν univ = ∏ᶠ v : {v : Primes(F) // v ∉ S}, (differentMass(F, v.val))⁻¹ := by sorry

/-- Paper: Example A.3.1.11, p. 558. If every prime dividing the different
is in S, the S-local additive product has the quotient-volume-one normalization. -/
theorem sAdditiveTamagawaMeasure_eq_covolumeOne
    (hS : ∀ v : Primes(F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    sAdditiveTamagawaMeasure F S = sAdditiveCovolumeOneMeasure F S := by sorry

/-- Paper: Remark A.3.4.2, p. 562. The local integer-ring indicator is fixed
by the Fourier transform exactly at places unramified over their residue prime.
Deviation: Unramifiedness is expressed by nondivisibility of the global different. -/
theorem finiteLocalTamagawaFourier_fixes_integers_iff (v : Primes(F)) :
    tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v)
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) ↔
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by sorry

end RiemannMasullo
