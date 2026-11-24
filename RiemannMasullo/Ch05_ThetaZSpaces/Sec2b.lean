module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b_IsotypicAverages

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2

import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.AutomaticContinuity
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Separable
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import RiemannMasullo.ForMathlib.Topology.ContinuousMap.Sigma
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

import Mathlib.MeasureTheory.Integral.Pi

import RiemannMasullo.AppC_LCTVS.Sec1

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.ContinuousOfBounded

/-! # Homogeneous theta spaces and Fourier descent

Masullo, §5.2.2–5.2.4, pp. 232–239. Every S-local space includes all archimedean places.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
variable {S T U : Finset (HeightOneSpectrum (𝓞 F))}
local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ(" S ")" => SIdeleQuotient F S
local notation "m𝔽" => ideleClassNorm F
local notation "mₛ(" S ")" => sIdeleQuotientNorm F S
local notation "C₁" => MonoidHom.ker m𝔽
local notation "J₁(" S ")" => MonoidHom.ker (mₛ(S))
local notation "Θ𝔽ω(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "Θₛω(" S ", " ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Kₛω(" S ", " ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose
local notation "ρₛ(" S ")" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
local notation "ρ𝔽₁" => (ρ𝔽).comp (MonoidHom.ker m𝔽).subtype
local notation "ρₛ₁(" S ")" => (ρₛ(S)).comp (MonoidHom.ker (mₛ(S))).subtype
local notation "E𝔽ω(" ω ")" => actionIsotype ρ𝔽₁ ω
local notation "Eₛω(" S ", " ω ")" => actionIsotype (ρₛ₁(S)) ω
local notation "μ𝔽₁" => normOneIdeleClassTamagawaMeasure F
local notation "μₛ₁(" S ")" => sLocalNormOneQuotientMeasure F S


local notation "P𝔽(" ω ")" => (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
local notation "Pₛ(" S ", " χ ")" =>
  (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose

/-- A normalized character average splits the inclusion of its isotype. Transposing
the splitting realizes the strong dual of any equivalent space inside the ambient strong dual. -/
private theorem strongDual_nuclear_of_compact_isotype.{test} {G E Q : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (ω : PontryaginDual G) (P : E →L[ℂ] E) (hP : IsPettisIsotypicAverageOn μ Set.univ ρ ω P)
    (e : Q ≃L[ℂ] actionIsotype ρ ω) (hE : IsNuclearTVS.{test} (StrongDual ℂ E)) :
    IsNuclearTVS.{test} (StrongDual ℂ Q) := by
  let V := actionIsotype ρ ω
  let c : ℂ := μ.real Set.univ
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ)).ne'
  let A := P.codRestrict V (compactActionAverage_mem_isotype μ ρ ω P hP)
  let q := e.symm.toContinuousLinearMap.comp A
  let i := c⁻¹ • (V.subtypeL.comp e.toContinuousLinearMap)
  have hretract (y : Q) : q (i y) = y := by
    apply e.injective
    change e (e.symm _) = e y
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change P (c⁻¹ • (e y : E)) = (e y : E)
    rw [map_smul, compactActionAverage_apply_isotype μ ρ ω P hP (e y).property]
    exact inv_smul_smul₀ hc _
  let pull := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ q
  let back := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ i
  have hleft : Function.LeftInverse back pull := fun φ ↦
    ContinuousLinearMap.ext fun y ↦ congrArg φ (hretract y)
  exact nuclear_of_linear_embedding pull (hleft.isEmbedding back.continuous pull.continuous) hE

/-- Compose the homogeneous-to-coinvariant identification with the compact average's
identification of its kernel quotient with the isotype. -/
private theorem globalThetaIsotypicAverage_equiv_of_coinvariants {G E T : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
    [CompactSpace N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    [AddCommGroup T] [Module ℂ T] [TopologicalSpace T] (H : Submodule ℂ T) (q : T → E)
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (ω : PontryaginDual N) (P : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ Set.univ (ρ.comp N.subtype) ω P)
    (h : let D := (Submodule.span ℂ (Set.range (fun p : N × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
      ∃ e : (T ⧸ H) ≃L[ℂ] (E ⧸ D), ∀ f : T, e (Submodule.Quotient.mk f) = D.mkQ (q f)) :
    IsClosed (actionIsotype (ρ.comp N.subtype) ω : Set E) ∧
      ∃ e : (T ⧸ H) ≃L[ℂ] actionIsotype (ρ.comp N.subtype) ω, ∀ f, (e (H.mkQ f) : E) = P (q f) := by
  have hc : Continuous (fun p : N × E ↦ (ρ.comp N.subtype) p.1 p.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hker := compactActionAverage_ker μ (ρ.comp N.subtype) hc ω P hP
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at hker
  dsimp only at h
  rw [← hker] at h
  obtain ⟨e, he⟩ := h
  obtain ⟨a, ha⟩ := compactActionAverage_quotient_equiv μ (ρ.comp N.subtype) hc ω P hP
  exact ⟨isClosed_actionIsotype _ ω, e.trans a, fun f ↦
    (congrArg (fun v ↦ (a v : E)) (he f)).trans (ha (q f))⟩

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The global average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem globalThetaIsotypicAverage_equiv (ω : PontryaginDual C₁) :
    IsClosed (E𝔽ω(ω) : Set Θ𝔽) ∧
      ∃ e : Θ𝔽ω(ω) ≃L[ℂ] E𝔽ω(ω), ∀ f : ℬ𝔽,
        (e ((K𝔽ω(ω)).mkQ f) : Θ𝔽) = P𝔽(ω) ((K𝔽).mkQ f) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (F := F) adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  let : Module ℝ Θ𝔽 := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ Θ𝔽 := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ Θ𝔽 := (PolynormableSpace.withSeminorms ℂ Θ𝔽).toLocallyConvexSpace
  with_reducible_and_instances
    exact globalThetaIsotypicAverage_equiv_of_coinvariants (G := C𝔽) (E := Θ𝔽) (T := ℬ𝔽)
      C₁ (K𝔽ω(ω)) (K𝔽).mkQ μ𝔽₁ ρ𝔽 (existsUnique_globalThetaAction (F := F)).exists.choose_spec.1
      ω (P𝔽(ω)) (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec
      (globalHomogeneousThetaSpace_equiv_coinvariants (F := F) ω)

section
variable {ω : PontryaginDual (ideleClassNorm F).ker}

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_strongDual_nuclear :
    IsNuclearTVS (StrongDual ℂ Θ𝔽ω(ω)) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (F := F) adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  let : Module ℝ Θ𝔽 := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ Θ𝔽 := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ Θ𝔽 := (PolynormableSpace.withSeminorms ℂ Θ𝔽).toLocallyConvexSpace
  with_reducible_and_instances
    exact strongDual_nuclear_of_compact_isotype μ𝔽₁ ρ𝔽₁ ω (P𝔽(ω))
      (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec
      (globalThetaIsotypicAverage_equiv (F := F) ω).2.choose
      (globalAdelicThetaSpace_strongDual_nuclear (F := F))

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_strongDual_montel :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) ∧ MontelSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) := by
  have hN : IsNuclearTVS.{0} Θ𝔽ω(ω) :=
    globalHomogeneousThetaSpace_nuclear (F := F) (ω := ω)
  let : T2Space Θ𝔽ω(ω) := hN.1
  let : PolynormableSpace ℂ Θ𝔽ω(ω) := hN.2.1
  let : MontelSpace ℂ Θ𝔽ω(ω) := (globalHomogeneousThetaSpace_montel (F := F) (ω := ω)).2
  let : CompleteSpace (StrongDual ℂ Θ𝔽ω(ω)) :=
    globalHomogeneousThetaSpace_strongDual_complete (F := F) (ω := ω)
  have hdual : IsNuclearTVS.{0} (StrongDual ℂ Θ𝔽ω(ω)) :=
    globalHomogeneousThetaSpace_strongDual_nuclear (F := F) (ω := ω)
  let : PolynormableSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) := hdual.2.1
  refine ⟨barrelled_strongDual_of_montel, ⟨fun B hc hb ↦ ?_⟩⟩
  simpa only [hc.closure_eq] using
    isCompact_closure_of_isNuclearTVS (StrongDual ℂ Θ𝔽ω(ω)) hdual hb

end

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The S-local average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem sLocalThetaIsotypicAverage_equiv (χ : PontryaginDual (J₁(S))) :
    IsClosed (Eₛω(S, χ) : Set (Θₛ(S))) ∧
      ∃ e : Θₛω(S, χ) ≃L[ℂ] Eₛω(S, χ), ∀ f : ℬₛ(S),
        (e ((Kₛω(S, χ)).mkQ f) : Θₛ(S)) = Pₛ(S, χ) ((Kₛ(S)).mkQ f) := by
  let E := SLocalAdelicThetaSpace F S
  let G := J₁(S)
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : (μₛ₁(S)).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  with_reducible_and_instances
    exact globalThetaIsotypicAverage_equiv_of_coinvariants (G := Jₛ(S)) (E := E) (T := ℬₛ(S))
      G (Kₛω(S, χ)) (Kₛ(S)).mkQ (μₛ₁(S)) (ρₛ(S))
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1 χ (Pₛ(S, χ))
      (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec
      (sLocalHomogeneousThetaSpace_equiv_coinvariants (F := F) (S := S) χ)

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_strongDual_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (StrongDual ℂ (Θₛω(S, χ))) := by
  let E := SLocalAdelicThetaSpace F S
  let G := J₁(S)
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : (μₛ₁(S)).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  with_reducible_and_instances
    exact strongDual_nuclear_of_compact_isotype (μₛ₁(S)) (ρₛ₁(S)) χ (Pₛ(S, χ))
      (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec
      (sLocalThetaIsotypicAverage_equiv (F := F) (S := S) χ).2.choose
      (sLocalAdelicThetaSpace_strongDual_nuclear (F := F) (S := S))

-- TODO(paper-gap): The global L² argument on p. 237 fails at norm zero for
-- the rational Gaussian. Apply character uniqueness on each compact norm-one fibre.

set_option linter.overlappingInstances false in
/-- A continuous function on a compact abelian group whose integrals against all characters
vanish is zero. -/
private theorem exists_globalThetaToHomogeneousProduct_charUnique {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (φ : C(G, ℂ))
    (hz : ∀ χ : PontryaginDual G, ∫ x, φ x * (χ x : ℂ) ∂μ = 0) : φ = 0 := by
  let ev (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ h ↦
    pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun h))
  have hi : Integrable φ μ :=
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun χ ↦ χ.continuous) hsep hi hz
  have heq := Measure.eq_of_ae_eq hae φ.continuous continuous_const
  exact ContinuousMap.ext fun g ↦ congrFun heq g

private theorem exists_globalThetaToHomogeneousProduct_pi {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] {ι : Type*} (K : Submodule ℂ E) (L : ι → Submodule ℂ E)
    (hKL : ∀ i, K ≤ L i) (hinj : ∀ f, (∀ i, f ∈ L i) → f ∈ K) :
    ∃ P : (E ⧸ K) →L[ℂ] (∀ i, E ⧸ L i),
      Injective P ∧ ∀ (f : E) i, P (K.mkQ f) i = (L i).mkQ f := by
  let P : (E ⧸ K) →ₗ[ℂ] (∀ i, E ⧸ L i) :=
    LinearMap.pi fun i ↦ K.mapQ (L i) LinearMap.id (hKL i)
  have hc : Continuous P :=
    K.isQuotientMap_mkQ.continuous_iff.mpr
      (continuous_pi fun i ↦ (L i).isQuotientMap_mkQ.continuous)
  refine ⟨⟨P, hc⟩, ?_, fun f i ↦ rfl⟩
  change Injective P
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun q hq ↦ ?_)
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    refine (Submodule.Quotient.mk_eq_zero K).mpr (hinj f fun i ↦ ?_)
    exact (Submodule.Quotient.mk_eq_zero (L i)).mp (congrFun hq i)

private theorem exists_sLocalThetaToHomogeneousProduct_le (χ : PontryaginDual (J₁(S))) :
    Kₛ(S) ≤ Kₛω(S, χ) := by
  intro f hf
  have hθ (g : Jₛ(S)) : sLocalAdelicThetaOnClasses F S f g = 0 := by
    induction g using QuotientGroup.induction_on with | H x => ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f x).trans
      (DFunLike.congr_fun (LinearMap.mem_ker.mp hf) x)
  refine LinearMap.mem_ker.mpr (ContinuousMap.ext fun g ↦ ?_)
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp [hθ]

private theorem exists_globalThetaToHomogeneousProduct_le (ω : PontryaginDual C₁) :
    K𝔽 ≤ K𝔽ω(ω) := by
  intro f hf
  have hθ : adelicTheta f = 0 := hf
  refine LinearMap.mem_ker.mpr (ContinuousMap.ext fun g ↦ ?_)
  change homogeneousAdelicTheta ω f g = 0
  simp [homogeneousAdelicTheta, hθ]

private theorem exists_sLocalThetaToHomogeneousProduct_ker (f : ℬₛ(S))
    (hf : ∀ χ : PontryaginDual (J₁(S)), f ∈ Kₛω(S, χ)) : f ∈ Kₛ(S) := by
  let : MeasurableSpace (J₁(S)) := borel _
  have : BorelSpace (J₁(S)) := ⟨rfl⟩
  have : CompactSpace (J₁(S)) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : T2Space (Jₛ(S)) :=
    letI := isClosed_sProjectedDiagonal (F := F) (S := S)
    inferInstance
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S)ˣ :=
    (sIdeleGroup_description F S).1.secondCountableTopology
  let : SecondCountableTopology (Jₛ(S)) := inferInstance
  let : SecondCountableTopology (J₁(S)) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ := sLocalNormOneQuotientMeasure F S
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have : μ.Regular := Measure.regular_of_isMulLeftInvariant isCompact_univ
    (by simp) (measure_ne_top μ _)
  have hθ : sLocalAdelicThetaOnClasses F S f = 0 := by
    ext g
    let φ : C(J₁(S), ℂ) := ⟨fun h ↦ sLocalAdelicThetaOnClasses F S f (g * h.val),
      (sLocalAdelicThetaOnClasses F S f).continuous.comp
        (continuous_const.mul continuous_subtype_val)⟩
    have hφ : φ = 0 := exists_globalThetaToHomogeneousProduct_charUnique μ φ fun χ ↦ by
      have h := DFunLike.congr_fun (LinearMap.mem_ker.mp (hf χ)) g
      rw [sLocalHomogeneousAdelicThetaLinearMap_apply] at h
      exact h
    simpa [φ] using DFunLike.congr_fun hφ 1
  refine LinearMap.mem_ker.mpr (ContinuousMap.ext fun x ↦ ?_)
  refine (sLocalAdelicThetaOnClasses_mk F S f x).symm.trans ?_
  rw [hθ]
  rfl

private theorem exists_globalThetaToHomogeneousProduct_ker (f : ℬ𝔽)
    (hf : ∀ ω : PontryaginDual C₁, f ∈ K𝔽ω(ω)) : f ∈ K𝔽 := by
  let : MeasurableSpace C𝔽 := borel _
  have : BorelSpace C𝔽 := ⟨rfl⟩
  have : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  have : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let μ := normOneIdeleClassTamagawaMeasure F
  have hspec := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  have : μ.IsHaarMeasure := hspec.2.2.2.1
  have : μ.Regular := hspec.2.2.2.2.1
  have hθ : adelicTheta f = 0 := by
    ext g
    let φ : C(C₁, ℂ) := ⟨fun h ↦ adelicTheta f (h.val * g),
      (adelicTheta f).continuous.comp (continuous_subtype_val.mul continuous_const)⟩
    have hφ : φ = 0 := exists_globalThetaToHomogeneousProduct_charUnique μ φ fun ω ↦ by
      have h := DFunLike.congr_fun (LinearMap.mem_ker.mp (hf ω)) g
      exact h
    simpa [φ] using DFunLike.congr_fun hφ 1
  exact hθ

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical global map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_globalThetaToHomogeneousProduct :
    ∃ P : Θ𝔽 →L[ℂ] (∀ ω : PontryaginDual C₁, Θ𝔽ω(ω)),
      Injective P ∧ ∀ (f : ℬ𝔽) ω, P ((K𝔽).mkQ f) ω = (K𝔽ω(ω)).mkQ f :=
  exists_globalThetaToHomogeneousProduct_pi (K𝔽) (fun ω ↦ K𝔽ω(ω))
    exists_globalThetaToHomogeneousProduct_le exists_globalThetaToHomogeneousProduct_ker

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical S-local map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_sLocalThetaToHomogeneousProduct :
    ∃ P : Θₛ(S) →L[ℂ] (∀ χ : PontryaginDual (J₁(S)), Θₛω(S, χ)),
      Injective P ∧ ∀ (f : ℬₛ(S)) χ, P ((Kₛ(S)).mkQ f) χ = (Kₛω(S, χ)).mkQ f :=
  exists_globalThetaToHomogeneousProduct_pi (Kₛ(S)) (fun χ ↦ Kₛω(S, χ))
    exists_sLocalThetaToHomogeneousProduct_le exists_sLocalThetaToHomogeneousProduct_ker

local notation "M𝔽ω(" ω ")" => meromorphicNormOneComponent m𝔽
  (isProperMap_ideleClassNorm F).continuous ω (globalIdelicOrderBound (F := F))
local notation "Mₛω(" S ", " ω ")" => meromorphicNormOneComponent (mₛ(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous ω (sLocalIdelicOrderBound (F := F) (S := S))

/-- Restriction to a norm-one component is continuous for compact convergence, and
restricting a continuation preserves its pole bound. -/
private theorem exists_globalHomogeneousThetaMellin_restriction {G : Type*}
    [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (ω : PontryaginDual m.ker) (b : QuasiCharacter G → WithTop ℤ) :
    ∃ R : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b) →L[ℂ]
        ↥(meromorphicNormOneComponent m hm ω b),
      ∀ u c, (R u).val c = u.val ⟨c.val.val, c.property⟩ := by
  let Ω := {c : QuasiCharacter G // ∀ h : m.ker, c h.val = (ω h : ℂ)}
  let i : C({c : Ω // 0 ≤ b c.val}, {c : QuasiCharacter G // 0 ≤ b c}) :=
    ⟨fun c ↦ ⟨c.val.val, c.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let M := meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b
  let A := (ContinuousMap.compCLM ℂ ℂ i).comp M.subtypeL
  refine ⟨A.codRestrict _ ?_, fun _ _ ↦ rfl⟩
  intro u
  obtain ⟨Z, hZ, hgerm⟩ := u.property
  exact ⟨fun c ↦ Z c.val, fun c ↦ hZ (i c), fun c ↦ hgerm c.val⟩

/-- Paper: (5.2.3.14), p. 236.
The global Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the global Mellin transform in (5.2.2.2). -/
theorem exists_globalHomogeneousThetaMellin (ω : PontryaginDual C₁) :
    ∃ Z : Θ𝔽ω(ω) →L[ℂ] ↥(M𝔽ω(ω)), Injective Z ∧
      ∀ (f : ℬ𝔽) c,
        (Z ((K𝔽ω(ω)).mkQ f)).val c =
          (globalIdelicMellin (F := F) f).val ⟨c.val.val, c.property⟩ := by
  refine (exists_globalHomogeneousThetaMellin_restriction m𝔽
    (isProperMap_ideleClassNorm F).continuous ω (globalIdelicOrderBound (F := F))).elim fun R hR ↦ ?_
  let L : ℬ𝔽 →L[ℂ] _ := ⟨globalIdelicMellin (F := F), globalIdelicMellin_continuous⟩
  let T : ℬ𝔽 →L[ℂ] ↥(M𝔽ω(ω)) := R.comp L
  have hT (f : ℬ𝔽) c : (T f).val c =
      (globalIdelicMellin (F := F) f).val ⟨c.val.val, c.property⟩ := hR _ c
  have hker : K𝔽ω(ω) = T.ker := by
    apply SetLike.ext
    intro f
    constructor
    · intro hf
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact ContinuousMap.ext fun c ↦ (hT f c).trans
        ((mem_homogeneousAdelicTheta_ker_iff ω f).mp hf _ c.val.property)
    · intro hf
      apply (mem_homogeneousAdelicTheta_ker_iff ω f).mpr
      intro c hc
      exact (hT f ⟨⟨c.val, hc⟩, c.property⟩).symm.trans
        (congrArg (fun v : ↥(M𝔽ω(ω)) ↦ v.val ⟨⟨c.val, hc⟩, c.property⟩)
          (LinearMap.mem_ker.mp hf))
  exact ⟨(K𝔽ω(ω)).liftQL T hker.le,
    LinearMap.ker_eq_bot.mp ((K𝔽ω(ω)).ker_liftQ_eq_bot T.toLinearMap hker.le hker.ge), hT⟩

/-- Restrict a bounded-pole continuation and its regular values along the component inclusion. -/
private theorem exists_sLocalHomogeneousThetaMellin_restrict {G : Type*} [CommGroup G]
    [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m) (χ : PontryaginDual m.ker)
    (b : QuasiCharacter G → WithTop ℤ) :
    ∃ R : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b) →L[ℂ]
        ↥(meromorphicNormOneComponent m hm χ b),
      ∀ u c, (R u).val c = u.val ⟨c.val.val, c.property⟩ := by
  let X := {c : QuasiCharacter G // ∀ h : m.ker, c h.val = (χ h : ℂ)}
  let i : C({c : X // 0 ≤ b c.val}, {c // 0 ≤ b c}) :=
    ⟨fun c ↦ ⟨c.val.val, c.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hmem (u : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b)) :
      u.val.comp i ∈ meromorphicNormOneComponent m hm χ b := by
    obtain ⟨Z, hZ, hgerm⟩ := u.property
    exact ⟨fun c ↦ Z c.val, fun c ↦ hZ (i c), fun c ↦ hgerm c.val⟩
  exact ⟨{ toFun := fun u ↦ ⟨u.val.comp i, hmem u⟩
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl
           cont := ((ContinuousMap.continuous_precomp i).comp continuous_subtype_val).subtype_mk hmem },
    fun _ _ ↦ rfl⟩

/-- Descend the component restriction when vanishing on its regular locus characterizes the kernel. -/
private theorem exists_sLocalHomogeneousThetaMellin_of_ker {G : Type*} [CommGroup G]
    [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m) (χ : PontryaginDual m.ker)
    (b : QuasiCharacter G → WithTop ℤ) {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (K : Submodule ℂ E)
    (M : E →L[ℂ] ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b))
    (hK : ∀ f, f ∈ K ↔ ∀ c : {c // 0 ≤ b c},
      (∀ h : m.ker, c.val h.val = (χ h : ℂ)) → (M f).val c = 0) :
    ∃ Z : (E ⧸ K) →L[ℂ] ↥(meromorphicNormOneComponent m hm χ b), Injective Z ∧
      ∀ f c, (Z (K.mkQ f)).val c = (M f).val ⟨c.val.val, c.property⟩ := by
  obtain ⟨R, hR⟩ := exists_sLocalHomogeneousThetaMellin_restrict m hm χ b
  let L := R.comp M
  have hker : K = L.ker := by
    refine Submodule.ext fun f ↦ (hK f).trans ?_
    change _ ↔ R (M f) = 0
    constructor
    · intro hf
      exact Subtype.ext (ContinuousMap.ext fun c ↦ (hR (M f) c).trans
        (hf ⟨c.val.val, c.property⟩ c.val.property))
    · intro hf c hc
      let d : {x : {x : QuasiCharacter G // ∀ h : m.ker, x h.val = (χ h : ℂ)} //
          0 ≤ b x.val} := ⟨⟨c.val, hc⟩, c.property⟩
      exact (hR (M f) d).symm.trans
        (congrArg (fun u : ↥(meromorphicNormOneComponent m hm χ b) ↦ u.val d) hf)
  refine ⟨K.liftQL L hker.le, ?_, fun f c ↦ hR (M f) c⟩
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ L.toLinearMap hker)

/-- Paper: (5.2.3.14), p. 236.
The S-local Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the S-local Mellin transform in (5.2.2.2). -/
theorem exists_sLocalHomogeneousThetaMellin (χ : PontryaginDual (J₁(S))) :
    ∃ Z : Θₛω(S, χ) →L[ℂ] ↥(Mₛω(S, χ)), Injective Z ∧
      ∀ (f : ℬₛ(S)) c,
        (Z ((Kₛω(S, χ)).mkQ f)).val c =
          (sLocalIdelicMellin (F := F) (S := S) f).val ⟨c.val.val, c.property⟩ := by
  exact exists_sLocalHomogeneousThetaMellin_of_ker (mₛ(S))
    (isProperMap_sIdeleQuotientNorm F S).continuous χ (sLocalIdelicOrderBound (F := F) (S := S))
    (Kₛω(S, χ)) ⟨sLocalIdelicMellin (F := F) (S := S), sLocalIdelicMellin_continuous⟩
    (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) χ)

-- TODO(paper-gap): Ordinary insertion does not in general intertwine isotype
-- projections onto subspaces. Normalizing the averages does not fix this.

/-- Paper: (5.2.3.15), p. 236.
Global insertion commutes with passage to homogeneous theta quotients.
Deviation: The vertical arrows are the canonical quotients. The averages implement
these arrows via the respective identifications of the quotients with the isotypes. -/
theorem sLocalThetaToHomogeneous_commutes {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (x : Θₛ(S)) :
    let P := (exists_globalThetaToHomogeneousProduct (F := F)).choose
    let Q := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
    P (sLocalThetaToGlobal F S x) ω =
      sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω
        (Q x (sLocalNormOneCharacter (F := F) S ω hω)) := by
  intro P Q
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    exact ((exists_globalThetaToHomogeneousProduct (F := F)).choose_spec.2
      (sAdeleSchwartzToGlobal F S f) ω).trans
      ((congrArg (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω)
        ((exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose_spec.2 f
          (sLocalNormOneCharacter (F := F) S ω hω))).trans
        (sLocalHomogeneousThetaToGlobal_mk (F := F) (ω := ω) hω f)).symm

section TranslationRelations

local notation "diag𝔽" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "diagₛ(" S ")" => Units.map
  (((adeleProjection F S).comp (integralAdelesOutside F S).subtype).comp
    (integralAdeleDiagonal F S)).toMonoidHom

local notation "V𝔽" => Submodule.span ℂ (Set.range (fun p : Fˣ × ℬ𝔽 ↦
  p.2 - schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 p.1) p.2))
local notation "Vₛ(" S ")" => Submodule.span ℂ (Set.range (fun
  p : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ × ℬₛ(S) ↦
    p.2 - schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) p.1) p.2))

-- TODO(paper-gap): The pullback topologies below identify the whole theta kernel
-- with zero. For example, an odd rational Schwartz function with even finite part
-- is in the global kernel. The bornological closure assertion on p. 238 needs a
-- separate argument and the bornological quotient and module constructions.

/-- For a closed submodule `K` and a submodule `V ≤ K`, the closure of `V` in the topology
pulled back along the quotient map by `K` is `K`: the image of `V` is `{0}`, which is closed
in the quotient, and its preimage is `K`. -/
private theorem sLocalThetaKernel_eq_induced_closure_of_le {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (K V : Submodule ℂ E) (hK : IsClosed (K : Set E))
    (hV : V ≤ K) :
    @closure E (TopologicalSpace.induced K.mkQ inferInstance) (V : Set E) = (K : Set E) := by
  have h0 : K.mkQ '' (V : Set E) = {0} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨0, V.zero_mem, map_zero _⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero K).mpr (hV hv)
  have hc : IsClosed ({0} : Set (E ⧸ K)) := by
    refine K.isQuotientMap_mkQ.isCoinducing.isClosed_preimage.mp ?_
    convert hK using 1
    ext f
    exact Submodule.Quotient.mk_eq_zero K
  ext f
  rw [closure_induced, h0, hc.closure_eq, Set.mem_singleton_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, SetLike.mem_coe]

/-- S-local theta of a translate is S-local theta evaluated at the inverse-translated idele. -/
private theorem sLocalThetaKernel_eq_induced_closure_translate_apply
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g x : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x =
      sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp
    (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (d t).val x.val)

/-- S-local theta is unchanged when a test function is translated by a diagonal S-unit,
since S-local theta factors through the S-idele quotient. -/
private theorem sLocalThetaKernel_eq_induced_closure_translate
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) u) f) =
      sLocalAdelicTheta F S f := by
  refine ContinuousMap.ext fun x ↦
    (sLocalThetaKernel_eq_induced_closure_translate_apply S _ x f).trans
      (sLocalAdelicTheta_factorsThrough F S f ?_)
  refine QuotientGroup.eq.mpr ?_
  rw [mul_inv_rev, inv_inv, mul_comm _ x, mul_inv_cancel_left]
  exact ⟨Units.map (integralAdeleDiagonal F S).toMonoidHom u, ⟨u, rfl⟩, Units.ext rfl⟩

/-- Paper: Remark 5.2.3.4(1), p. 237.
The S-local theta kernel is the closure of the span of S-unit translation differences
for the topology pulled back from the theta quotient.
Deviation: This topology on test functions need not be Hausdorff. -/
theorem sLocalThetaKernel_eq_induced_closure (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let q : ℬₛ(S) → Θₛ(S) := (Kₛ(S)).mkQ
    let t : TopologicalSpace (ℬₛ(S)) := TopologicalSpace.induced q inferInstance
    let V := Vₛ(S)
    let K : Set (ℬₛ(S)) := (Kₛ(S) : Set (ℬₛ(S)))
    @closure _ t V.carrier = K := by
  refine sLocalThetaKernel_eq_induced_closure_of_le (Kₛ(S)) _
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S)) (Submodule.span_le.mpr ?_)
  rintro _ ⟨p, rfl⟩
  exact LinearMap.sub_mem_ker_iff.mpr
    (sLocalThetaKernel_eq_induced_closure_translate S p.1 p.2).symm

/-- Global theta of a translate is global theta evaluated at the inverse-translated class. -/
private theorem globalThetaKernel_eq_induced_closure_translate_apply (g : IdeleGroup (𝓞 F) F)
    (f : ℬ𝔽) (a : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate g f) a =
      adelicTheta f ((QuotientGroup.mk g)⁻¹ * a) := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  change _ = adelicTheta f (QuotientGroup.mk (g⁻¹ * x))
  rw [adelicTheta_mk (schwartzBruhatUnitTranslate g f) x, adelicTheta_mk f (g⁻¹ * x)]
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (algebraMap F 𝔸[F] (t : F)) x.val)

/-- Global theta is unchanged when a test function is translated by a principal idele,
since principal ideles are trivial in the idele class group. -/
private theorem globalThetaKernel_eq_induced_closure_translate (a : Fˣ) (f : ℬ𝔽) (c : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 a) f) c = adelicTheta f c := by
  have h1 : (QuotientGroup.mk (diag𝔽 a) : C𝔽) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have h2 : (QuotientGroup.mk (diag𝔽 a) : C𝔽)⁻¹ * c = c := by
    rw [h1, inv_one, one_mul]
  exact (globalThetaKernel_eq_induced_closure_translate_apply (diag𝔽 a) f c).trans
    (congrArg (adelicTheta f) h2)

/-- Paper: Remark 5.2.3.4(2), p. 237.
The global theta kernel is the closure of the span of principal translation differences
for the topology pulled back from the theta quotient.
Deviation: This topology on test functions need not be Hausdorff. -/
theorem globalThetaKernel_eq_induced_closure :
    let q : ℬ𝔽 → Θ𝔽 := (K𝔽).mkQ
    let t := TopologicalSpace.induced q inferInstance
    let V : Set ℬ𝔽 := (V𝔽).carrier
    @closure _ t V = (K𝔽 : Set ℬ𝔽) := by
  refine sLocalThetaKernel_eq_induced_closure_of_le (K𝔽) _ (adelicTheta_ker_isClosed (F := F))
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨p, rfl⟩
  exact LinearMap.sub_mem_ker_iff.mpr ((adelicThetaLinearMap_apply (F := F) p.2).trans
    ((ContinuousMap.ext fun c ↦
      (globalThetaKernel_eq_induced_closure_translate p.1 p.2 c).symm).trans
        (adelicThetaLinearMap_apply (F := F) _).symm))

local notation "unitAtₛ(" S ")" => sUnitEmbedding F S

/-- A quotient by a smaller submodule maps onto the quotient by a larger one, compatibly
with the quotient maps. -/
private theorem exists_quotient_to_quotient_of_le {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {V K : Submodule R M} (h : V ≤ K) :
    ∃ q : (M ⧸ V) →ₗ[R] (M ⧸ K), Surjective q ∧ q.comp V.mkQ = K.mkQ :=
  ⟨V.liftQ K.mkQ (by rwa [Submodule.ker_mkQ]),
    fun y ↦ by obtain ⟨x, rfl⟩ := K.mkQ_surjective y; exact ⟨V.mkQ x, rfl⟩,
    V.liftQ_mkQ _ _⟩

/-- S-local theta is invariant under translation by a diagonal S-unit. -/
private theorem sLocalAdelicTheta_translate_diag
    (u : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) u) f) =
      sLocalAdelicTheta F S f := by
  refine ContinuousMap.ext fun g ↦ ?_
  change ∑' ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ,
      schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) u) f
        (Multiplicative.ofAdd (Units.val (unitAtₛ(S) ξ * g))) =
    ∑' ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ,
      f (Multiplicative.ofAdd (Units.val (unitAtₛ(S) ξ * g)))
  refine ((Equiv.mulLeft u).tsum_eq _).symm.trans (tsum_congr fun ξ ↦ ?_)
  rw [Equiv.coe_mulLeft, schwartzBruhatUnitTranslate_apply]
  refine congrArg (fun x : SAdeleRing F S ↦ f (Multiplicative.ofAdd x)) ?_
  exact congrArg Units.val (show (diagₛ(S) u)⁻¹ * (unitAtₛ(S) (u * ξ) * g) =
      unitAtₛ(S) ξ * g by
    rw [map_mul, mul_assoc]; exact inv_mul_cancel_left (diagₛ(S) u) _)

/-- The S-unit translation differences lie in the S-local theta kernel. -/
private theorem sLocalSpan_le_ker : Vₛ(S) ≤ Kₛ(S) :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr fun p ↦ LinearMap.mem_ker.mpr
    (((sLocalAdelicTheta F S).map_sub _ _).trans
      (sub_eq_zero.mpr (sLocalAdelicTheta_translate_diag p.1 p.2).symm)))

/-- Global theta is invariant under translation by a principal idele. -/
private theorem adelicThetaLinearMap_translate_diag (u : Fˣ) (f : ℬ𝔽) :
    adelicThetaLinearMap F (schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 u) f) =
      adelicThetaLinearMap F f := by
  change adelicTheta (schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 u) f) = adelicTheta f
  refine ContinuousMap.ext fun c ↦ ?_
  induction c using QuotientGroup.induction_on with | H g => ?_
  refine (adelicTheta_mk _ g).trans (Eq.trans ?_ (adelicTheta_mk f g).symm)
  refine ((Equiv.mulLeft u).tsum_eq _).symm.trans (tsum_congr fun ξ ↦ ?_)
  rw [Equiv.coe_mulLeft, schwartzBruhatUnitTranslate_apply]
  refine congrArg (fun x : 𝔸[F] ↦ f (Multiplicative.ofAdd x)) ?_
  exact congrArg Units.val (show (diag𝔽 u)⁻¹ * (diag𝔽 (u * ξ) * g) = diag𝔽 ξ * g by
    rw [map_mul, mul_assoc, inv_mul_cancel_left])

/-- The principal translation differences lie in the global theta kernel. -/
private theorem globalSpan_le_ker : V𝔽 ≤ K𝔽 :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr fun p ↦ LinearMap.mem_ker.mpr
    (((adelicThetaLinearMap F).map_sub _ _).trans
      (sub_eq_zero.mpr (adelicThetaLinearMap_translate_diag p.1 p.2).symm)))

/-- Paper: Remark 5.2.3.4, p. 238.
The algebraic S-unit coinvariants surject canonically onto the S-local theta quotient.
Deviation: The source is the quotient by the relation span. -/
theorem exists_sLocalAlgebraicCoinvariants_to_theta (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let V := Vₛ(S)
    ∃ q : (ℬₛ(S) ⧸ V) →ₗ[ℂ] Θₛ(S),
      Surjective q ∧ q.comp V.mkQ = (Kₛ(S)).mkQ := by
  intro V
  exact exists_quotient_to_quotient_of_le (sLocalSpan_le_ker (S := S))

/-- Paper: Remark 5.2.3.4, p. 238.
The algebraic principal coinvariants surject canonically onto the global theta quotient.
Deviation: The source is the quotient by the relation span. -/
theorem exists_globalAlgebraicCoinvariants_to_theta :
    let V : Submodule ℂ ℬ𝔽 := V𝔽
    ∃ q : (ℬ𝔽 ⧸ V) →ₗ[ℂ] Θ𝔽, Surjective q ∧ q.comp V.mkQ = (K𝔽).mkQ := by
  intro V
  have h := globalSpan_le_ker (F := F)
  exact exists_quotient_to_quotient_of_le h

private theorem sLocalBornologicalOfQuotient {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (K : Submodule ℂ E)
    (hE : ∀ p : Seminorm ℂ E,
      (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (p : Seminorm ℂ (E ⧸ K))
    (hp : ∀ B : Set (E ⧸ K), IsVonNBounded ℂ B → BddAbove (p '' B)) :
    Continuous p := by
  apply K.isQuotientMap_mkQL.continuous_iff.mpr
  refine hE (p.comp K.mkQ) ?_
  intro B hB
  change BddAbove ((fun x : E ↦ p (K.mkQL x)) '' B)
  simpa only [Set.image_image] using hp (K.mkQL '' B) (hB.image K.mkQL)

/-- Paper: Remark 5.2.3.4, pp. 237–238.
The S-local theta quotient is bornological. Every seminorm bounded on all of its
von Neumann bounded sets is continuous. -/
theorem sLocalTheta_bornological :
    ∀ p : Seminorm ℂ (Θₛ(S)),
      (∀ B : Set (Θₛ(S)), IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p :=
  sLocalBornologicalOfQuotient (LinearMap.ker (sLocalAdelicTheta F S))
    (sAdeleSchwartz_bornological F S)

private theorem bornological_quotient {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (K : Submodule ℂ E)
    (hE : ∀ p : Seminorm ℂ E,
      (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (p : Seminorm ℂ (E ⧸ K))
    (hp : ∀ B : Set (E ⧸ K), IsVonNBounded ℂ B → BddAbove (p '' B)) :
    Continuous p := by
  apply K.isQuotientMap_mkQL.continuous_iff.mpr
  refine hE (p.comp K.mkQ) ?_
  intro B hB
  change BddAbove ((fun x : E ↦ p (K.mkQL x)) '' B)
  simpa only [Set.image_image] using hp (K.mkQL '' B) (hB.image K.mkQL)

/-- Paper: Remark 5.2.3.4, pp. 237–238.
The global theta quotient is bornological. Every seminorm bounded on all of its
von Neumann bounded sets is continuous. -/
theorem globalTheta_bornological :
    ∀ p : Seminorm ℂ Θ𝔽, (∀ B : Set Θ𝔽, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p :=
  bornological_quotient (K𝔽) (adeleSchwartz_bornological (F := F))

end TranslationRelations

section IsotypicMellin

attribute [local instance] ideleClassGroupMeasurableSpaceSec2b normOneSIdeleQuotientMeasurableSpaceSec2b

/-- A Pettis isotypic average multiplies by the Haar mass at any evaluation of a continuous
linear map into continuous functions on which the action is the character. -/
private theorem globalThetaMellin_isotypicAverage_eval {G E X : Type*} [Monoid G]
    [TopologicalSpace G] [MeasurableSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [TopologicalSpace X] (M : Submodule ℂ C(X, ℂ)) (L : E →ₗ[ℂ] M) (hL : Continuous L) (x0 : X)
    (μ : Measure G) (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) (P : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ Set.univ ρ ω P) (u : E)
    (hu : ∀ g, (L (ρ g u)).val x0 = (ω g : ℂ) * (L u).val x0) :
    (L (P u)).val x0 = (μ.real Set.univ : ℂ) * (L u).val x0 := by
  let φ : StrongDual ℂ E :=
    { toFun := fun y ↦ (L y).val x0
      map_add' := fun a b ↦ by simp
      map_smul' := fun a b ↦ by simp
      cont := (continuous_eval_const x0).comp (continuous_subtype_val.comp hL) }
  obtain ⟨_, he⟩ := hP u
  have h := LinearMap.congr_fun he φ
  change φ (P u) = ∫ g, φ (star (ω g : ℂ) • ρ g u) ∂(μ.restrict Set.univ) at h
  refine h.trans ?_
  have hg : ∀ g, φ (star (ω g : ℂ) • ρ g u) = φ u := fun g ↦ by
    rw [map_smul, smul_eq_mul]
    change star (ω g : ℂ) * (L (ρ g u)).val x0 = (L u).val x0
    rw [hu g, ← mul_assoc]
    have h1 : star (ω g : ℂ) * (ω g : ℂ) = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe,
        Complex.ofReal_one]
    rw [h1, one_mul]
  simp only [hg, Measure.restrict_univ, integral_const]
  rfl

/-- A functional that scales translates of representatives by a character scales the
induced action on the quotient by the same character. -/
private theorem globalThetaMellin_isotypicAverage_translate {IG CG Q B : Type*} (q : B → Q)
    (hq : Surjective q) (π : IG → CG) (hπ : Surjective π) (ρ : CG → Q → Q) (T : IG → B → B)
    (hρ : ∀ g f, ρ (π g) (q f) = q (T g f)) (φ : Q → ℂ) (χ : CG → ℂ)
    (hT : ∀ g f, φ (q (T g f)) = χ (π g) * φ (q f)) (g : CG) (x : Q) :
    φ (ρ g x) = χ g * φ x := by
  obtain ⟨f, rfl⟩ := hq x
  obtain ⟨g, rfl⟩ := hπ g
  rw [hρ, hT]

/-- A map induced on a quotient by a continuous linear map is continuous. -/
private theorem globalThetaMellin_isotypicAverage_continuous {E Y : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (K : Submodule ℂ E) (L : E →ₗ[ℂ] Y) (h : K ≤ LinearMap.ker L) (hL : Continuous L) :
    Continuous (K.liftQ L h) :=
  K.isQuotientMap_mkQ.continuous_iff.mpr hL

/-- Paper: Remark 5.2.3.5, p. 238.
On each component the global Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the norm-one Haar mass. -/
theorem globalThetaMellin_isotypicAverage (ω : PontryaginDual C₁) (x : Θ𝔽)
    (c : {c : QuasiCharacter C𝔽 // 0 ≤ globalIdelicOrderBound c})
    (hc : ∀ g : C₁, c.val g.val = (ω g : ℂ)) :
    (globalThetaMellin (F := F) (P𝔽(ω) x)).val c =
      ((μ𝔽₁).real Set.univ : ℂ) * (globalThetaMellin (F := F) x).val c :=
  globalThetaMellin_isotypicAverage_eval _ (globalThetaMellin (F := F))
    (globalThetaMellin_isotypicAverage_continuous _ _
      (globalIdelicMellin_vanishes_on_theta_kernel (F := F))
      (globalIdelicMellin_continuous (F := F))) c _ _ ω _
    (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec x
    (fun g ↦ (globalThetaMellin_isotypicAverage_translate Submodule.Quotient.mk
      (Submodule.mkQ_surjective _) QuotientGroup.mk QuotientGroup.mk_surjective
      (fun g y ↦ (existsUnique_globalThetaAction (F := F)).exists.choose g y)
      schwartzBruhatUnitTranslate
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
      (fun y ↦ (globalThetaMellin (F := F) y).val c) (fun g ↦ c.val g)
      (fun g f ↦ globalIdelicMellin_unitTranslate g f c) g.val x).trans
      (congrArg (· * _) (hc g)))

/-- Paper: Remark 5.2.3.5, p. 238.
On each S-local component the Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the S-local norm-one Haar mass. -/
theorem sLocalThetaMellin_isotypicAverage (χ : PontryaginDual (J₁(S))) (x : Θₛ(S))
    (c : {c : QuasiCharacter (Jₛ(S)) // 0 ≤ sLocalIdelicOrderBound c})
    (hc : ∀ g : J₁(S), c.val g.val = (χ g : ℂ)) :
    (sLocalThetaMellin (F := F) (S := S) (Pₛ(S, χ) x)).val c =
      ((μₛ₁(S)).real Set.univ : ℂ) * (sLocalThetaMellin (F := F) (S := S) x).val c :=
  globalThetaMellin_isotypicAverage_eval _ (sLocalThetaMellin (F := F) (S := S))
    (globalThetaMellin_isotypicAverage_continuous _ _
      (sLocalIdelicMellin_vanishes_on_theta_kernel (F := F) (S := S))
      (sLocalIdelicMellin_continuous (F := F) (S := S))) c _ _ χ _
    (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec x
    (fun g ↦ (globalThetaMellin_isotypicAverage_translate Submodule.Quotient.mk
      (Submodule.mkQ_surjective _) QuotientGroup.mk QuotientGroup.mk_surjective
      (fun g y ↦ (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose g y)
      schwartzBruhatUnitTranslate
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
      (fun y ↦ (sLocalThetaMellin (F := F) (S := S) y).val c) (fun g ↦ c.val g)
      (fun g f ↦ sLocalIdelicMellin_unitTranslate g f c) g.val x).trans
      (congrArg (· * _) (hc g)))

end IsotypicMellin

section Fourier

-- TODO(paper-gap): The global map is described as inversion on p. 238.
-- The identity on theta functions has a norm factor and two zero terms,
-- as in adelicTheta_riemannRoch.

/-- Testing a weighted continuous function against all characters recovers the function. -/
private theorem existsUnique_sLocalThetaFourier_weighted {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (θ : C(G, ℂ)) (w : QuasiCharacter G) (hi : Integrable (fun x ↦ θ x * w x) μ)
    (hz : ∀ χ : PontryaginDual G, ∫ x, θ x * w x * (χ x : ℂ) ∂μ = 0) : θ = 0 := by
  let ev (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ h ↦
    pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun h))
  have hae := ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun χ ↦ χ.continuous) hsep hi hz
  have heq := Measure.eq_of_ae_eq hae (θ.continuous.mul w.continuous) continuous_const
  exact ContinuousMap.ext fun g ↦ (mul_eq_zero.mp (congrFun heq g)).resolve_right
    ((Group.isUnit g).map w).ne_zero

/-- Duality in a norm chart reflects the exponent in one. -/
private theorem existsUnique_sLocalThetaFourier_dual {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (χ : PontryaginDual G) (s : ℂ) :
    let u : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    dualQuasiCharacter m hm (quasiCharacterNormTwist m hm (u.comp χ) s) =
      quasiCharacterNormTwist m hm (u.comp χ⁻¹) (1 - s) := by
  intro u
  ext1 g
  have hp : 0 < ((m g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change (((m g : ℝ≥0) : ℝ) : ℂ) * (quasiCharacterNormTwist m hm (u.comp χ) s) g⁻¹ =
    ((χ⁻¹ g : Circle) : ℂ) * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (1 - s)
  rw [map_inv]
  change _ * ((χ g : ℂ) * (((m g : ℝ≥0) : ℝ) : ℂ) ^ s)⁻¹ = (χ g : ℂ)⁻¹ * _
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hp.ne'), Complex.cpow_one, mul_inv_rev,
    div_eq_mul_inv]
  ring

/-- The double S-adelic Fourier transform is reflection, and minus one is an `S`-unit,
so it has the same theta function. -/
private theorem existsUnique_sLocalThetaFourier_inv (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (sAdeleSchwartzFourier (sAdeleSchwartzFourier f)) =
      sLocalAdelicTheta F S f := by
  ext g
  have hneg : sLocalAdelicTheta F S f (-g) = sLocalAdelicTheta F S f g := by
    refine sLocalAdelicTheta_factorsThrough F S f ?_
    have hm1 : (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ(S)) = 1 := by
      refine (sIdeleQuotient_mk_eq_one F S _).2 ⟨-1, ?_⟩
      apply Units.ext
      simp
    rw [show -g = (-1) * g by simp, QuotientGroup.mk_mul, hm1, one_mul]
  rw [← hneg]
  simp only [sLocalAdelicTheta_apply]
  refine tsum_congr fun ξ ↦ ?_
  rw [sLocal_fourier_inversion]
  simp [mul_neg]

/-- The S-adelic Fourier transform preserves the S-local theta kernel. At the center of
the critical strip the functional equation sends each weighted theta integral of the
transform to one of the double transform, which has the original theta function. -/
private theorem existsUnique_sLocalThetaFourier_ker (f : ℬₛ(S))
    (hf : sLocalAdelicTheta F S f = 0) :
    sLocalAdelicTheta F S (sAdeleSchwartzFourier f) = 0 := by
  let : MeasurableSpace (Jₛ(S)) := borel _
  let : BorelSpace (Jₛ(S)) := ⟨rfl⟩
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let μ := sLocalQuotientTamagawaMeasure F S
  have : μ.IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  have : μ.Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.1
  let u : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let chart (χ : PontryaginDual (Jₛ(S))) : QuasiCharacter (Jₛ(S)) :=
    quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (u.comp χ) (1 / 2)
  have hpos (χ : PontryaginDual (Jₛ(S))) :
      ∃ (ψ : PontryaginDual (Jₛ(S))) (s : ℂ), 0 < s.re ∧ chart χ = quasiCharacterNormTwist
        (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous (u.comp ψ) s :=
    ⟨χ, 1 / 2, by norm_num, rfl⟩
  have hclasses (h : ℬₛ(S)) (hh : sLocalAdelicTheta F S h = 0) :
      sLocalAdelicThetaOnClasses F S h = 0 := by
    ext g
    induction g using QuotientGroup.induction_on with
    | H x => rw [sLocalAdelicThetaOnClasses_mk, hh]; rfl
  have hθff := hclasses _ ((existsUnique_sLocalThetaFourier_inv f).trans hf)
  have hθ : sLocalAdelicThetaOnClasses F S (sAdeleSchwartzFourier f) = 0 := by
    refine existsUnique_sLocalThetaFourier_weighted μ _ (chart 1)
      (sLocalThetaMellinIntegral_integrable _ _ (hpos 1)) fun χ ↦ ?_
    have hfe := sLocalIdelicZetaIntegral_functionalEquation (sAdeleSchwartzFourier f) χ (1 / 2)
      (by norm_num)
    dsimp only at hfe
    rw [existsUnique_sLocalThetaFourier_dual, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hfe
    have hc : sLocalThetaMellinIntegral (sAdeleSchwartzFourier f) (chart χ) = 0 := by
      rw [sLocalThetaMellinIntegral_eq_zeta _ (hpos χ)]
      change sLocalIdelicZetaIntegral _ (quasiCharacterNormTwist _ _ (u.comp χ) (1 / 2)) = 0
      have h2 := sLocalThetaMellinIntegral_eq_zeta
        (sAdeleSchwartzFourier (sAdeleSchwartzFourier f)) (hpos χ⁻¹)
      rw [hfe]
      change _ * sLocalIdelicZetaIntegral _ (chart χ⁻¹) = 0
      rw [← h2]
      simp [sLocalThetaMellinIntegral, hθff]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)).trans hc
    change sLocalAdelicThetaOnClasses F S _ g * (1 * _ ^ (1 / 2 : ℂ)) * (χ g : ℂ) =
      sLocalAdelicThetaOnClasses F S _ g * ((χ g : ℂ) * _ ^ (1 / 2 : ℂ))
    rw [one_mul, mul_right_comm, mul_assoc]
  ext g
  rw [← sLocalAdelicThetaOnClasses_mk, hθ]
  rfl

/-- Paper: Theorem 5.2.4.1(1), pp. 238–239.
S-adelic Fourier transform descends to a unique continuous linear involution
on the S-local theta quotient. -/
theorem existsUnique_sLocalThetaFourier :
    ∃! e : Θₛ(S) ≃L[ℂ] Θₛ(S),
      Involutive e ∧ ∀ f : ℬₛ(S),
        e ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ (sAdeleSchwartzFourier (F := F) (S := S) f) := by
  obtain ⟨P, hP⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  have hK : Kₛ(S) ≤ (Kₛ(S)).comap P.toLinearMap := fun f hf ↦ by
    rw [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hP]
    exact existsUnique_sLocalThetaFourier_ker f (LinearMap.mem_ker.mp hf)
  let E₀ : Θₛ(S) →ₗ[ℂ] Θₛ(S) := (Kₛ(S)).mapQ (Kₛ(S)) P.toLinearMap hK
  have hE₀ (f : ℬₛ(S)) : E₀ ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ (sAdeleSchwartzFourier f) := by
    rw [← hP]
    rfl
  have hcont : Continuous E₀ := by
    refine (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr ?_
    have : (E₀ ∘ (Kₛ(S)).mkQ) = (Kₛ(S)).mkQ ∘ P :=
      funext fun f ↦ (hE₀ f).trans (by simp only [Function.comp_apply, hP])
    rw [this]
    exact (Kₛ(S)).isQuotientMap_mkQ.continuous.comp P.continuous
  let E : Θₛ(S) →L[ℂ] Θₛ(S) := ⟨E₀, hcont⟩
  have hEE (x : Θₛ(S)) : E (E x) = x := by
    obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective x
    change E₀ (E₀ _) = _
    rw [hE₀, hE₀]
    refine (sLocalAdelicThetaSpace_mk_eq_iff _ _).mpr (ContinuousMap.ext fun g ↦ ?_)
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk,
        existsUnique_sLocalThetaFourier_inv]
  refine ⟨ContinuousLinearEquiv.equivOfInverse E E hEE hEE, ⟨hEE, hE₀⟩, ?_⟩
  rintro e' ⟨-, he'⟩
  ext x
  obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective x
  exact (he' f).trans (hE₀ f).symm


open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The adelic Fourier transform is a continuous linear operator on the global tests. It is
linear because it is the Pontryagin-dual transform read through self-duality, and continuous
because it maps bounded sets to bounded sets. -/
private theorem existsUnique_globalThetaFourier_clm :
    ∃ P : ℬ𝔽 →L[ℂ] ℬ𝔽, ∀ f, P f = adeleSchwartzFourier f := by
  let : MeasurableSpace 𝔸[F] := borel _
  let G := Multiplicative 𝔸[F]
  let : MeasurableSpace G := borel G
  let μ : Measure G := additiveTamagawaMeasure F
  let (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F) :=
    locallyCompactSpace_adicCompletion v
  let (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  obtain ⟨e, he⟩ := additiveTamagawaMeasure_selfDual F
  obtain ⟨Fo, hFo⟩ := schwartzBruhat_fourier_equiv μ
  have hpt (f : ℬ𝔽) (y : G) : adeleSchwartzFourier f y = Fo f (e y) := by
    refine (tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ ?_)).trans ((hFo f).2 _).symm
    rw [mul_comm x y.toAdd]
    exact he.1 y.toAdd x
  let L : ℬ𝔽 →ₗ[ℂ] ℬ𝔽 :=
    { toFun := adeleSchwartzFourier
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦ by
        change adeleSchwartzFourier (f + g) y =
          adeleSchwartzFourier f y + adeleSchwartzFourier g y
        rw [hpt, hpt, hpt, map_add]
        rfl)
      map_smul' := fun c f ↦ Subtype.ext (funext fun y ↦ by
        change adeleSchwartzFourier (c • f) y = c * adeleSchwartzFourier f y
        rw [hpt, hpt, map_smul]
        rfl) }
  exact ⟨⟨L, continuous_of_bornological_image schwartzBruhat_bornological L
    adeleSchwartzFourier_image_isVonNBounded⟩, fun _ ↦ rfl⟩

/-- There are idele classes of every norm `n + 1`. -/
private theorem existsUnique_globalThetaFourier_seq :
    ∃ g : ℕ → IdeleClassGroup (𝓞 F) F,
      ∀ n, ((ideleClassNorm F (g n) : ℝ≥0) : ℝ) = n + 1 := by
  refine ⟨fun n ↦ QuotientGroup.mk (canonicalIdeleNormSection F
    (Units.mk0 ((n : ℝ≥0) + 1) (Nat.cast_add_one_ne_zero n))), fun n ↦ ?_⟩
  change ((ideleNorm F (canonicalIdeleNormSection F _) : ℝ≥0) : ℝ) = _
  rw [canonicalIdeleNormSection_rightInverse F]
  simp

/-- Global theta decays faster than the inverse norm along classes of norm `n + 1`. -/
private theorem existsUnique_globalThetaFourier_tendsto (h : ℬ𝔽)
    (g : ℕ → IdeleClassGroup (𝓞 F) F) (hg : ∀ n, ((ideleClassNorm F (g n) : ℝ≥0) : ℝ) = n + 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1) * adelicTheta h (g n)) atTop (𝓝 0) := by
  obtain ⟨C, T, hC, -, hdec⟩ := adelicTheta_decay_large h 2
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_gt_atTop ⌈T⌉₊, eventually_ge_atTop 1] with n hn hn1
  have hT : T < ((ideleClassNorm F (g n) : ℝ≥0) : ℝ) := by
    rw [hg]
    have := Nat.lt_of_ceil_lt hn
    linarith
  have hb := hdec (g n) hT
  simp only [hg] at hb
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [norm_mul, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1) * ‖adelicTheta h (g n)‖ ≤ ((n : ℝ) + 1) * (C * (((n : ℝ) + 1) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C / ((n : ℝ) + 1) := by field_simp
    _ ≤ C / n := div_le_div_of_nonneg_left hC.le hpos (by linarith)

/-- A constant whose multiples by `n + 1` converge is zero. -/
private theorem existsUnique_globalThetaFourier_const {z w : ℂ}
    (h : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1) * z) atTop (𝓝 w)) : z = 0 := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using this
  have hz := h.mul hinv
  rw [mul_zero] at hz
  refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n ↦ ?_) hz
  field_simp [Nat.cast_add_one_ne_zero n]

/-- A test with vanishing theta function vanishes at zero, and so does its Fourier transform.
By Riemann–Roch the Fourier theta is `a / ‖g‖ - b` with `a`, `b` the two values at zero,
and theta decays at infinity. -/
private theorem existsUnique_globalThetaFourier_zero (f : ℬ𝔽) (hf : adelicTheta f = 0) :
    f (Multiplicative.ofAdd 0) = 0 ∧ adeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 := by
  obtain ⟨g, hg⟩ := existsUnique_globalThetaFourier_seq (F := F)
  set a := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set b := adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F]))
  have hval (n : ℕ) :
      ((n : ℂ) + 1) * adelicTheta (adeleSchwartzFourier f) (g n) = a - ((n : ℂ) + 1) * b := by
    have h := adelicTheta_riemannRoch f (g n)⁻¹
    simp only [hf, ContinuousMap.zero_apply, inv_inv, map_inv, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, hg, Complex.real_smul] at h
    push_cast at h
    linear_combination (-1 : ℂ) * h
  have ht := existsUnique_globalThetaFourier_tendsto (adeleSchwartzFourier f) g hg
  simp_rw [hval] at ht
  have hb : b = 0 := by
    have h2 : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1) * (-b)) atTop (𝓝 (0 - a)) :=
      (ht.sub (tendsto_const_nhds (x := a))).congr fun n ↦ by ring
    exact neg_eq_zero.mp (existsUnique_globalThetaFourier_const h2)
  simp only [hb, mul_zero, sub_zero] at ht
  exact ⟨tendsto_nhds_unique tendsto_const_nhds ht, hb⟩

/-- The adelic Fourier transform preserves the global theta kernel. -/
private theorem existsUnique_globalThetaFourier_ker (f : ℬ𝔽) (hf : adelicTheta f = 0) :
    adelicTheta (adeleSchwartzFourier f) = 0 := by
  obtain ⟨h0, h1⟩ := existsUnique_globalThetaFourier_zero f hf
  ext g
  have h := adelicTheta_riemannRoch f g⁻¹
  have hn : ((ideleClassNorm F g⁻¹ : ℝ≥0) : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (NNReal.coe_ne_zero.mpr (ideleClassNorm F g⁻¹).ne_zero)
  simp only [hf, ContinuousMap.zero_apply, inv_inv, h0, h1, smul_zero, add_zero,
    sub_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hn

/-- The double adelic Fourier transform has the same theta function. Riemann–Roch twice
shows the two theta functions differ by a constant, and both decay at infinity. -/
private theorem existsUnique_globalThetaFourier_inv (f : ℬ𝔽) :
    adelicTheta (adeleSchwartzFourier (adeleSchwartzFourier f)) = adelicTheta f := by
  set a := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set b := adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set c := adeleSchwartzFourier (adeleSchwartzFourier f) (Multiplicative.ofAdd (0 : 𝔸[F]))
  have hrr (g : IdeleClassGroup (𝓞 F) F) :
      adelicTheta f g = adelicTheta (adeleSchwartzFourier (adeleSchwartzFourier f)) g + c - a := by
    have h1 := adelicTheta_riemannRoch f g
    have h2 := adelicTheta_riemannRoch (adeleSchwartzFourier f) g⁻¹
    have hn : ((ideleClassNorm F g : ℝ≥0) : ℝ) ≠ 0 :=
      NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero
    simp only [inv_inv, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv,
      Complex.real_smul] at h1 h2
    rw [h1, h2]
    have hn' : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    push_cast
    field_simp
    ring
  obtain ⟨g, hg⟩ := existsUnique_globalThetaFourier_seq (F := F)
  have hca : c - a = 0 := by
    refine existsUnique_globalThetaFourier_const (w := 0 - 0) ?_
    refine ((existsUnique_globalThetaFourier_tendsto f g hg).sub
      (existsUnique_globalThetaFourier_tendsto
        (adeleSchwartzFourier (adeleSchwartzFourier f)) g hg)).congr fun n ↦ ?_
    rw [hrr]
    ring
  ext g
  rw [hrr]
  linear_combination -hca

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Adelic Fourier transform descends to a unique continuous linear involution
on the global theta quotient.
Deviation: The descent identity is tested on global test functions, as in the proof. -/
theorem existsUnique_globalThetaFourier :
    ∃! e : Θ𝔽 ≃L[ℂ] Θ𝔽,
      Involutive e ∧ ∀ f : ℬ𝔽,
        e ((K𝔽).mkQ f) = (K𝔽).mkQ (adeleSchwartzFourier (F := F) f) := by
  obtain ⟨P, hP⟩ := existsUnique_globalThetaFourier_clm (F := F)
  have hK : K𝔽 ≤ (K𝔽).comap P.toLinearMap := fun f hf ↦ by
    rw [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hP]
    exact existsUnique_globalThetaFourier_ker f (LinearMap.mem_ker.mp hf)
  let E₀ : Θ𝔽 →ₗ[ℂ] Θ𝔽 := (K𝔽).mapQ K𝔽 P.toLinearMap hK
  have hE₀ (f : ℬ𝔽) : E₀ ((K𝔽).mkQ f) = (K𝔽).mkQ (adeleSchwartzFourier f) := by
    rw [← hP]
    rfl
  have hcont : Continuous E₀ := by
    refine (K𝔽).isQuotientMap_mkQ.continuous_iff.mpr ?_
    have : (E₀ ∘ (K𝔽).mkQ) = (K𝔽).mkQ ∘ P :=
      funext fun f ↦ (hE₀ f).trans (by simp only [Function.comp_apply, hP])
    rw [this]
    exact (K𝔽).isQuotientMap_mkQ.continuous.comp P.continuous
  let E : Θ𝔽 →L[ℂ] Θ𝔽 := ⟨E₀, hcont⟩
  have hEE (x : Θ𝔽) : E (E x) = x := by
    obtain ⟨f, rfl⟩ := (K𝔽).mkQ_surjective x
    change E₀ (E₀ _) = _
    rw [hE₀, hE₀]
    exact (globalAdelicThetaSpace_mk_eq_iff _ _).mpr (existsUnique_globalThetaFourier_inv f)
  refine ⟨ContinuousLinearEquiv.equivOfInverse E E hEE hEE, ⟨hEE, hE₀⟩, ?_⟩
  rintro e' ⟨-, he'⟩
  ext x
  obtain ⟨f, rfl⟩ := (K𝔽).mkQ_surjective x
  exact (he' f).trans (hE₀ f).symm


-- TODO(paper-gap): The unrestricted compatibility assertions on p. 239 fail.
-- For ℚ(i) above 2 the Fourier image of the integer indicator is half the inverse-
-- different indicator. An archimedean bump supported near 1/2 detects the difference.

set_option maxSynthPendingDepth 8 in
open Classical in
/-- Integrating a stage function times one factor at each new place separates over the
additive Tamagawa measure, without a pure-tensor hypothesis on the old stage function. -/
private theorem sLocalThetaFourier_transition_integral
    {D : Finset (HeightOneSpectrum (𝓞 F))} (hD : Disjoint S D)
    (g : SAdeleRing F S → ℂ) (k : (v : D) → v.val.adicCompletion F → ℂ) :
    (∫ z : SAdeleRing F (S ∪ D),
      g (z.1, fun v ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩) *
        ∏ v : D, k v (z.2 ⟨v.val, Finset.mem_union_right S v.property⟩)
        ∂sAdditiveTamagawaMeasure F (S ∪ D)) =
      (∫ z, g z ∂sAdditiveTamagawaMeasure F S) *
        ∏ v : D, ∫ x, k v x ∂finiteLocalAdditiveTamagawaMeasure F v.val := by
  classical
  let V := HeightOneSpectrum (𝓞 F)
  let K (v : V) := v.adicCompletion F
  let (v : V) : MeasurableSpace (K v) := borel (v.adicCompletion F)
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let μ (v : V) : Measure (K v) := finiteLocalAdditiveTamagawaMeasure F v
  let (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : V) : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let (v : V) : SigmaFinite (μ v) :=
    inferInstanceAs (SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let μa := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let η (A : Finset V) := Measure.pi (fun v : A ↦ μ v.val)
  let e := MeasurableEquiv.piFinsetUnion K hD
  let E := MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl (InfiniteAdeleRing F)).prodCongr e)
  have hE : MeasurePreserving E ((μa.prod (η S)).prod (η D)) (μa.prod (η (S ∪ D))) :=
    ((MeasurePreserving.id μa).prod (measurePreserving_piFinsetUnion hD μ)).comp
      (measurePreserving_prodAssoc μa (η S) (η D))
  let H (z : SAdeleRing F (S ∪ D)) :=
    g (z.1, fun v ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩) *
      ∏ v : D, k v (z.2 ⟨v.val, Finset.mem_union_right S v.property⟩)
  change (∫ z, H z ∂μa.prod (η (S ∪ D))) = _
  refine (hE.integral_comp' H).symm.trans ?_
  have h (p : SAdeleRing F S × ((v : D) → K v.val)) :
      H (E p) = g p.1 * ∏ v : D, k v (p.2 v) := by
    change g (p.1.1, fun v ↦ Equiv.piFinsetUnion K hD (p.1.2, p.2) ⟨v.val, Finset.mem_union_left D v.property⟩) *
      ∏ v : D, k v (Equiv.piFinsetUnion K hD (p.1.2, p.2) ⟨v.val, Finset.mem_union_right S v.property⟩) = _
    simp only [Equiv.piFinsetUnion_left K hD (Subtype.property _),
      Equiv.piFinsetUnion_right K hD (Subtype.property _)]
    rfl
  simp_rw [h]
  exact (integral_prod_mul (μ := μa.prod (η S)) (ν := η D) g (fun x ↦ ∏ v : D, k v (x v))).trans
    (congrArg (_ * ·) (integral_fintype_prod_eq_prod k (μ := fun v : D ↦ μ v.val)))

open Classical in
/-- Extending to a disjoint union multiplies by the integer indicators on its second summand. -/
private theorem sLocalThetaFourier_transition_apply
    {D : Finset (HeightOneSpectrum (𝓞 F))} (hD : Disjoint S D)
    (f : ℬₛ(S)) (z : SAdeleRing F (S ∪ D)) :
    sAdeleSchwartzTransition F (Finset.subset_union_left (s₁ := S) (s₂ := D)) f
        (Multiplicative.ofAdd z) =
      f (Multiplicative.ofAdd (z.1, fun v : S ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩)) *
        ∏ v : D, (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
          (fun _ ↦ (1 : ℂ)) (z.2 ⟨v.val, Finset.mem_union_right S v.property⟩) := by
  classical
  rw [sAdeleSchwartzTransition_apply]
  split_ifs with h
  · rw [Finset.prod_eq_one (fun v _ ↦ Set.indicator_of_mem
      (h ⟨v.val, Finset.mem_union_right S v.property⟩
        (fun hv ↦ Finset.disjoint_left.mp hD hv v.property)) _), mul_one]
  · push Not at h
    obtain ⟨v, hv, hz⟩ := h
    have hvD := (Finset.mem_union.mp v.property).resolve_left hv
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨v.val, hvD⟩ : D))
      (Set.indicator_of_notMem hz _), mul_zero]

open Classical in
/-- The Fourier integral for an enlarged test function factors into its stage transform
and the local transforms of the newly inserted integer indicators. -/
private theorem sLocalThetaFourier_transition_union
    {D : Finset (HeightOneSpectrum (𝓞 F))} (hD : Disjoint S D)
    (hgood : ∀ v ∈ D, ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) (f : ℬₛ(S)) :
    let i := sAdeleSchwartzTransition F (Finset.subset_union_left (s₁ := S) (s₂ := D))
    sAdeleSchwartzFourier (i f) = i (sAdeleSchwartzFourier f) := by
  classical
  intro i
  apply Subtype.ext
  funext y
  let p (z : SAdeleRing F (S ∪ D)) : SAdeleRing F S :=
    (z.1, fun v ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩)
  let j (v : D) : ↥(S ∪ D) := ⟨v.val, Finset.mem_union_right S v.property⟩
  let I (v : D) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
    (fun _ ↦ (1 : ℂ))
  let C := (starRingEnd ℂ).toMonoidHom.comp Circle.coeHom
  let g (x : SAdeleRing F S) := f (Multiplicative.ofAdd x) * C (sAdeleStandardCharacter F S (x * p y.toAdd))
  let k (v : D) (x : v.val.adicCompletion F) :=
    I v x * C (finiteLocalStandardCharacter F v.val (x * y.toAdd.2 (j v)))
  have hψ (z : SAdeleRing F (S ∪ D)) : sAdeleStandardCharacter F (S ∪ D) (z * y.toAdd) =
      sAdeleStandardCharacter F S (p z * p y.toAdd) *
        ∏ v : D, finiteLocalStandardCharacter F v.val (z.2 (j v) * y.toAdd.2 (j v)) := by
    let b (v : ↥(S ∪ D)) := finiteLocalStandardCharacter F v.val (z.2 v * y.toAdd.2 v)
    change _ * (∏ v, b v) = (_ * _) * _
    rw [← (Equiv.Finset.union S D hD).prod_comp b, Fintype.prod_sum_type, ← mul_assoc]
    rfl
  have hInt (z : SAdeleRing F (S ∪ D)) :
      i f (Multiplicative.ofAdd z) * C (sAdeleStandardCharacter F (S ∪ D) (z * y.toAdd)) =
        g (p z) * ∏ v : D, k v (z.2 (j v)) := by
    rw [show i f (Multiplicative.ofAdd z) = _ from sLocalThetaFourier_transition_apply hD f z,
      hψ, map_mul, map_prod]
    simp only [g, k, Finset.prod_mul_distrib]
    ring
  have hfix (v : D) : (∫ x, k v x ∂finiteLocalAdditiveTamagawaMeasure F v.val) =
      I v (y.toAdd.2 (j v)) :=
    congrFun ((finiteLocalTamagawaFourier_fixes_integers_iff F v.val).mpr (hgood v.val v.property)) _
  change (∫ z, i f (Multiplicative.ofAdd z) * C (sAdeleStandardCharacter F (S ∪ D) (z * y.toAdd))
      ∂sAdditiveTamagawaMeasure F (S ∪ D)) = _
  simp_rw [hInt]
  exact (sLocalThetaFourier_transition_integral hD g k).trans
    ((congrArg (_ * ·) (Finset.prod_congr rfl fun v _ ↦ hfix v)).trans
      (sLocalThetaFourier_transition_apply hD (sAdeleSchwartzFourier f) y.toAdd).symm)

/-- Paper: Theorem 5.2.4.1(1), p. 239.
The S-local Fourier involutions commute with stage enlargement away from the different.
Deviation: Every added place is required to have a Fourier-fixed integer indicator. -/
theorem sLocalThetaFourier_transition (hST : S ⊆ T)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ T → v ∉ S → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F))
    (x : Θₛ(S)) :
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourierT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
    let transition := sLocalThetaTransition (F := F) (S := S) (T := T) hST
    fourierT (transition x) = transition (fourierS x) := by
  classical
  intro fourierS fourierT transition
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    let P (A : Finset (HeightOneSpectrum (𝓞 F))) := ∀ h : S ⊆ A,
      let i := sAdeleSchwartzTransition F h
      sAdeleSchwartzFourier (i f) = i (sAdeleSchwartzFourier f)
    have hu : P (S ∪ (T \ S)) := fun _ ↦
      sLocalThetaFourier_transition_union Finset.disjoint_sdiff
        (fun v hv ↦ hgood v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2) f
    have hT : P T := (Finset.union_sdiff_of_subset hST) ▸ hu
    exact ((existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose_spec.2
      (sAdeleSchwartzTransition F hST f)).trans
      ((congrArg (Kₛ(T)).mkQ (hT hST)).trans (congrArg transition
        ((existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f).symm))

set_option maxSynthPendingDepth 8 in
/-- Paper: (5.2.4.4), p. 239.
The local and global Fourier involutions commute with insertion once S contains
every place dividing the different.
Deviation: The places outside S must have Fourier-fixed integer indicators. -/
theorem sLocalThetaFourier_toGlobal
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (x : Θₛ(S)) :
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x) := by
  intro fourierS fourier
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have hS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f
  have hF := (existsUnique_globalThetaFourier (F := F)).exists.choose_spec.2
    (sAdeleSchwartzToGlobal F S f)
  calc
    _ = (K𝔽).mkQ (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f)) := hF
    _ = (K𝔽).mkQ (sAdeleSchwartzToGlobal F S (sAdeleSchwartzFourier f)) :=
      congrArg (K𝔽).mkQ
        (adeleSchwartzFourier_sAdeleSchwartzToGlobal_of_different F S hgood f (sAdeleSchwartzFourier f) rfl)
    _ = _ := (congrArg (sLocalThetaToGlobal F S) hS).symm

section

local instance sLocalThetaFourier_mem_isotype_measurableSpace :
    MeasurableSpace (SAdeleRing F S) := by
  letI (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  letI (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  exact inferInstanceAs (MeasurableSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))

/-- Paper: Theorem 5.2.4.1(1), p. 239.
Multiplication by a norm-one S-idele preserves additive Tamagawa measure.
This isolates the change of variables needed to exchange character isotypes:
the product of the local additive Haar scaling factors is the S-idele norm. -/
private theorem sLocalThetaFourier_mem_isotype_measurePreserving (u : (SAdeleRing F S)ˣ)
    (hu : sIdeleNorm F S u = 1) :
    MeasurePreserving (fun z : SAdeleRing F S ↦ u.val * z)
      (sAdditiveTamagawaMeasure F S) (sAdditiveTamagawaMeasure F S) := by
  classical
  let := sAdeleRing_borelSpace (F := F) (S := S)
  letI : MeasurableSpace 𝔸[F] := borel _
  letI : BorelSpace 𝔸[F] := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  letI : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let g := sIdeleInsertion F S u
  have hgn : ideleNorm F g = 1 := (ideleNorm_sIdeleInsertion F S u).trans hu
  have hg : MeasurePreserving (fun a : 𝔸[F] ↦ g.val * a) μ μ := by
    refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply (show Measurable (fun a : 𝔸[F] ↦ g.val * a) from
      (continuous_const.mul continuous_id).measurable) hB]
    have hpre : (fun a : 𝔸[F] ↦ g.val * a) ⁻¹' B =
        (fun a : 𝔸[F] ↦ g⁻¹.val * a) '' B := by
      ext a
      constructor
      · intro ha
        refine ⟨g.val * a, ha, ?_⟩
        exact Units.inv_mul_cancel_left g a
      · rintro ⟨b, hb, rfl⟩
        change g.val * (g⁻¹.val * b) ∈ B
        simpa only [Units.mul_inv_cancel_left] using hb
    rw [hpre, adeleHaar_mul_image F μ g⁻¹ B hB]
    simp [map_inv, hgn]
  let U : Set 𝔸[F] := integralAdelesOutside F S
  have hi := sIdeleInsertion_apply F S u
  have hpre : (fun a : 𝔸[F] ↦ g.val * a) ⁻¹' U = U := by
    ext a
    change g.val * a ∈ integralAdelesOutside F S ↔ a ∈ integralAdelesOutside F S
    simp only [integralAdelesOutside, Subring.mem_iInf, Subring.mem_comap]
    change (∀ v, v ∉ S → g.val.2 v * a.2 v ∈ v.adicCompletionIntegers F) ↔
      ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F
    constructor <;> intro h v hv
    · simpa only [g, hi.2.2 v hv, one_mul] using h v hv
    · simpa only [g, hi.2.2 v hv, one_mul] using h v hv
  have hgU := hg.restrict_preimage_emb (measurableEmbedding_const_smul g) U
  rw [hpre] at hgU
  obtain ⟨c, hc, _, hp, _⟩ := sAdeleProjection_dual_masses F S
  have hproj : adeleProjection F S g.val = u.val := by
    apply Prod.ext
    · exact hi.1
    · funext v
      exact hi.2.1 v
  have hcomm : Semiconj (adeleProjection F S) (fun a : 𝔸[F] ↦ g.val * a)
      (fun z : SAdeleRing F S ↦ u.val * z) := by
    intro a
    rw [map_mul, hproj]
  have hs := hp.of_semiconj hgU hcomm (continuous_const.mul continuous_id).measurable
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs.smul_measure c⁻¹

private theorem sLocalThetaFourier_mem_isotype_unitTranslate (u : (SAdeleRing F S)ˣ)
    (hu : sIdeleNorm F S u = 1) (f : ℬₛ(S)) :
    sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) =
      schwartzBruhatUnitTranslate u⁻¹ (sAdeleSchwartzFourier f) := by
  let := sAdeleRing_borelSpace (F := F) (S := S)
  apply Subtype.ext
  funext y
  change (∫ z : SAdeleRing F S, f (Multiplicative.ofAdd (u⁻¹.val * z)) *
    star (sAdeleStandardCharacter F S (z * y.toAdd) : ℂ)
    ∂sAdditiveTamagawaMeasure F S) =
    ∫ z : SAdeleRing F S, f (Multiplicative.ofAdd z) *
      star (sAdeleStandardCharacter F S (z * (u.val * y.toAdd)) : ℂ)
      ∂sAdditiveTamagawaMeasure F S
  have h := (sLocalThetaFourier_mem_isotype_measurePreserving u hu).integral_comp
    (measurableEmbedding_const_smul u)
    (fun z : SAdeleRing F S ↦ f (Multiplicative.ofAdd (u⁻¹.val * z)) *
      star (sAdeleStandardCharacter F S (z * y.toAdd) : ℂ))
  refine h.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with z
  rw [Units.inv_mul_cancel_left]
  have hm : (u.val * z) * y.toAdd = z * (u.val * y.toAdd) := by ring
  rw [hm]

end

section

private theorem sLocalThetaFourier_mem_isotype_descend
    {A E : Type*} (q : A → E) (hq : Surjective q)
    (e r r' : E → E) (f t t' : A → A)
    (he : ∀ a, e (q a) = q (f a))
    (hr : ∀ a, r (q a) = q (t a))
    (hr' : ∀ a, r' (q a) = q (t' a))
    (hft : ∀ a, f (t a) = t' (f a)) (x : E) : e (r x) = r' (e x) := by
  obtain ⟨a, rfl⟩ := hq x
  rw [hr, he, he, hr', hft]

private theorem sLocalThetaFourier_mem_isotype_of_intertwining
    {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (ρ : G →* (E →L[ℂ] E)) (e : E ≃L[ℂ] E) (he : Involutive e)
    (hρ : ∀ (g : G) (x : E), e (ρ g x) = ρ g⁻¹ (e x))
    (χ : PontryaginDual G) (x : E) :
    e x ∈ actionIsotype ρ χ⁻¹ ↔ x ∈ actionIsotype ρ χ := by
  have forward (ω : PontryaginDual G) (y : E) (hy : y ∈ actionIsotype ρ ω) :
      e y ∈ actionIsotype ρ ω⁻¹ := by
    rw [mem_actionIsotype] at hy ⊢
    intro g
    rw [← inv_inv g, ← hρ, hy, map_smul]
    simp only [map_inv, inv_inv]
    change (↑(ω g) : ℂ)⁻¹ • e y = (↑((ω g)⁻¹) : ℂ) • e y
    rw [Circle.coe_inv]
  constructor
  · intro hx
    simpa only [he x, inv_inv] using forward χ⁻¹ (e x) hx
  · exact forward χ x

end

private theorem sLocalThetaFourier_mem_isotype_unit_intertwines
    (u : (SAdeleRing F S)ˣ) (hu : sIdeleNorm F S u = 1) (y : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier (ρₛ(S) (QuotientGroup.mk u) y) =
      ρₛ(S) (QuotientGroup.mk u⁻¹) (fourier y) := by
  let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  have hf := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec
  have ha := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
  exact sLocalThetaFourier_mem_isotype_descend
    (A := ℬₛ(S)) (E := Θₛ(S)) (Kₛ(S)).mkQ (Kₛ(S)).mkQ_surjective
    fourier (ρₛ(S) (QuotientGroup.mk u)) (ρₛ(S) (QuotientGroup.mk u⁻¹))
    sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u) (schwartzBruhatUnitTranslate u⁻¹)
    hf.2 (ha u) (ha u⁻¹) (sLocalThetaFourier_mem_isotype_unitTranslate u hu) y

private theorem sLocalThetaFourier_mem_isotype_intertwines
    (g : J₁(S)) (y : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier (ρₛ(S) g.val y) = ρₛ(S) g.val⁻¹ (fourier y) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective g.val
  have hn : sIdeleNorm F S u = 1 :=
    (sIdeleQuotientNorm_mk F S u).symm.trans ((congrArg (mₛ(S)) hu).trans g.property)
  have h := sLocalThetaFourier_mem_isotype_unit_intertwines u hn y
  simpa only [QuotientGroup.mk_inv, hu] using h

/-- Paper: Theorem 5.2.4.1(1), p. 239.
S-local Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem sLocalThetaFourier_mem_isotype (χ : PontryaginDual (J₁(S))) (x : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier x ∈ Eₛω(S, χ⁻¹) ↔ x ∈ Eₛω(S, χ) := by
  let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  exact sLocalThetaFourier_mem_isotype_of_intertwining
    (G := J₁(S)) (E := Θₛ(S)) (ρₛ₁(S)) fourier
    (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.1
    (sLocalThetaFourier_mem_isotype_intertwines (F := F) (S := S)) χ x

/-- Norm-one dilations preserve additive Tamagawa measure, so Fourier transform
intertwines translation by such an idele with translation by its inverse. -/
private theorem globalThetaFourier_mem_isotype_translate (g : IdeleGroup (𝓞 F) F)
    (hg : ideleNorm F g = 1) (f : ℬ𝔽) :
    adeleSchwartzFourier (schwartzBruhatUnitTranslate g f) =
      schwartzBruhatUnitTranslate g⁻¹ (adeleSchwartzFourier f) := by
  let : MeasurableSpace 𝔸[F] := borel _
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let d := Homeomorph.smul (α := 𝔸[F]) g⁻¹
  have hd : MeasurePreserving d μ μ := by
    refine ⟨d.continuous.measurable, Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply d.continuous.measurable hs]
    change μ ((fun x : 𝔸[F] ↦ g⁻¹ • x) ⁻¹' s) = μ s
    rw [Set.preimage_smul_inv]
    change μ ((fun a : 𝔸[F] ↦ g.val * a) '' s) = μ s
    simpa only [hg, Units.val_one, ENNReal.coe_one, one_mul] using adeleHaar_mul_image F μ g s hs
  apply Subtype.ext
  funext y
  let k (z : 𝔸[F]) := f (Multiplicative.ofAdd z) *
    star (adeleStandardCharacter F (z * (g.val * y.toAdd)) : ℂ)
  refine Eq.trans ?_ (hd.integral_comp d.toMeasurableEquiv.measurableEmbedding k)
  apply integral_congr_ae
  refine Eventually.of_forall fun z ↦ ?_
  change _ * star (adeleStandardCharacter F (z * y.toAdd) : ℂ) =
    _ * star (adeleStandardCharacter F ((g⁻¹.val * z) * (g.val * y.toAdd)) : ℂ)
  rw [mul_mul_mul_comm, show g⁻¹.val * g.val = (1 : 𝔸[F]) from g.inv_val, one_mul]
  rfl

/-- On theta classes, norm-one translation therefore passes through the Fourier
involution as inverse translation. -/
private theorem globalThetaFourier_mem_isotype_intertwine (g : C₁) (x : Θ𝔽) :
    let e := (existsUnique_globalThetaFourier (F := F)).exists.choose
    e (ρ𝔽₁ g x) = ρ𝔽₁ g⁻¹ (e x) := by
  intro e
  obtain ⟨a, ha⟩ := g
  induction a using QuotientGroup.induction_on with | H u => ?_
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have hρ := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have he := (existsUnique_globalThetaFourier (F := F)).exists.choose_spec.2
  calc
    _ = e ((K𝔽).mkQ (schwartzBruhatUnitTranslate u f)) := congrArg e (hρ u f)
    _ = (K𝔽).mkQ (adeleSchwartzFourier (schwartzBruhatUnitTranslate u f)) := he _
    _ = (K𝔽).mkQ (schwartzBruhatUnitTranslate u⁻¹ (adeleSchwartzFourier f)) :=
      congrArg (K𝔽).mkQ (globalThetaFourier_mem_isotype_translate u ha f)
    _ = ρ𝔽 (QuotientGroup.mk u⁻¹) ((K𝔽).mkQ (adeleSchwartzFourier f)) := (hρ u⁻¹ _).symm
    _ = _ := congrArg (ρ𝔽 (QuotientGroup.mk u⁻¹)) (he f).symm

/-- An invertible linear intertwiner for an action and the inverse action
exchanges the eigenspaces for a character and its inverse. -/
private theorem globalThetaFourier_mem_isotype_of_intertwine {G E : Type*}
    [CommGroup G] [TopologicalSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (ρ : G →* (E →L[ℂ] E)) (e : E ≃L[ℂ] E)
    (he : ∀ g x, e (ρ g x) = ρ g⁻¹ (e x)) (ω : PontryaginDual G) (x : E) :
    e x ∈ actionIsotype ρ ω⁻¹ ↔ x ∈ actionIsotype ρ ω := by
  rw [mem_actionIsotype, mem_actionIsotype]
  have hχ (g : G) : ω⁻¹ g = ω g⁻¹ := (map_inv ω g).symm
  constructor
  · intro h g
    apply e.injective
    rw [he, h, hχ, inv_inv, map_smul]
  · intro h g
    calc
      ρ g (e x) = e (ρ g⁻¹ x) := by simpa only [inv_inv] using (he g⁻¹ x).symm
      _ = _ := by rw [h, hχ, map_smul]

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Global Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem globalThetaFourier_mem_isotype (ω : PontryaginDual C₁) (x : Θ𝔽) :
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier x ∈ E𝔽ω(ω⁻¹) ↔ x ∈ E𝔽ω(ω) := by
  exact globalThetaFourier_mem_isotype_of_intertwine ρ𝔽₁ _
    globalThetaFourier_mem_isotype_intertwine ω x

end Fourier

end RiemannMasullo
