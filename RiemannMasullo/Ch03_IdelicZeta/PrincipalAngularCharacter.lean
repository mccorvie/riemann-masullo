module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.SUnitPrimeExpansion
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Angular characters with principal finite places

A local integral unit has additive order zero and a normalized uniformizer has order one.
An angular character trivial on the global units can therefore be compensated at each
principal finite place by the inverse angular value of its generator.
-/

public section

noncomputable section

namespace RiemannMasullo

open Filter IsDedekindDomain NumberField Topology
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

private def finiteOrderCharacter (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →ₜ* Multiplicative ℤ := by
  let O := v.adicCompletionIntegers F
  let V := Units.map (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).toMonoidHom
  let ord := (WithZero.unitsWithZeroEquiv.toMonoidHom.comp V)⁻¹
  have hlog (x : (v.adicCompletion F)ˣ) : (ord x).toAdd = -WithZero.log (Valued.v x.val) :=
    congrArg Neg.neg (WithZero.logEquiv_apply (V x))
  refine ⟨ord, continuous_of_continuousAt_one ord ?_⟩
  apply Filter.EventuallyEq.continuousAt (y := 1)
  filter_upwards [(Submonoid.isOpen_units (Valued.isOpen_valuationSubring
    (v.adicCompletion F))).mem_nhds O.units.one_mem] with x hx
  have h := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx)
  change (ord x).toAdd = 0
  rw [hlog, h, WithZero.log_one, neg_zero]

private theorem finiteOrderCharacter_apply (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (finiteOrderCharacter v x).toAdd = -WithZero.log (Valued.v x.val) :=
  congrArg Neg.neg (WithZero.logEquiv_apply (Units.map
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).toMonoidHom x))

private def finiteAngularCharacter (v : HeightOneSpectrum (𝓞 F)) (b : Circle) :
    (v.adicCompletion F)ˣ →ₜ* Circle :=
  let power : Multiplicative ℤ →ₜ* Circle :=
    ⟨{ toFun := fun k ↦ b ^ k.toAdd, map_one' := zpow_zero _, map_mul' := fun _ _ ↦ zpow_add _ _ _ },
      continuous_of_discreteTopology⟩
  power.comp (finiteOrderCharacter v)

private def complexUnitPhase : ℂˣ →ₜ* Circle where
  toFun z := ⟨z.val / (‖z.val‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    simp [norm_ne_zero_iff.mpr z.ne_zero])⟩
  map_one' := Circle.ext (by simp)
  map_mul' a b := Circle.ext (by
    change ((a : ℂ) * (b : ℂ)) / (‖(a : ℂ) * b‖ : ℂ) =
      ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) * ((b : ℂ) / (‖(b : ℂ)‖ : ℂ))
    rw [norm_mul, Complex.ofReal_mul, div_mul_div_comm])
  continuous_toFun := Continuous.subtype_mk (by
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun x ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))) _

private def complexPlacePhase (w : InfinitePlace F) : w.Completionˣ →ₜ* Circle :=
  complexUnitPhase.comp
    ⟨Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom,
      (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.units_map _⟩

set_option quotPrecheck false

local notation "JP" => SIdeleQuotient F S
local notation "Sep" => ContinuousMulEquiv.prodUnits
  (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)
local notation "Arch" => ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
local notation "FinU" => ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
local notation "unitChart(" χ ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) 0

local notation "AtA(" w ")" => fun x : (InfinitePlace.Completion w)ˣ ↦
  (Sep).symm ((Arch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1)
local notation "AtF(" v ")" => fun x : (HeightOneSpectrum.adicCompletion F (Subtype.val v))ˣ ↦
  (Sep).symm (1, (FinU).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))

private theorem angular_localProduct_exists (w : InfinitePlace F) (A : w.Completionˣ →ₜ* Circle)
    (b : S → Circle)
    (hdiag : ∀ x : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ,
      A (Arch (Sep (sUnitEmbedding F S x)).1 w) *
        ∏ v : S, finiteAngularCharacter v.val (b v) (FinU (Sep (sUnitEmbedding F S x)).2 v) = 1) :
    ∃ χ : PontryaginDual JP,
      (∀ z, sLocalInfiniteRestriction w (unitChart(χ)) z = (A z : ℂ)) ∧
      ∀ (v : S) z, sLocalFiniteRestriction v (unitChart(χ)) z =
        (finiteAngularCharacter v.val (b v) z : ℂ) := by
  classical
  let f : (SAdeleRing F S)ˣ →ₜ* Circle :=
    { toFun := fun x ↦ A (Arch (Sep x).1 w) * ∏ v : S, finiteAngularCharacter v.val (b v) (FinU (Sep x).2 v)
      map_one' := by simp
      map_mul' := fun x y ↦ by
        simp only [map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Finset.prod_mul_distrib]
        ac_rfl
      continuous_toFun := by
        apply Continuous.mul
        · exact A.continuous.comp ((continuous_apply w).comp ((Arch).continuous.comp (Sep).continuous.fst))
        · exact continuous_finsetProd _ (fun v _ ↦ (finiteAngularCharacter v.val (b v)).continuous.comp
            ((continuous_apply v).comp ((FinU).continuous.comp (Sep).continuous.snd))) }
  have hk : sProjectedDiagonal F S ≤ f.toMonoidHom.ker := by
    rw [sProjectedDiagonal, MonoidHom.map_range]
    rintro _ ⟨x, rfl⟩
    exact hdiag x
  let c := QuotientGroup.lift (sProjectedDiagonal F S) f.toMonoidHom hk
  let χ : PontryaginDual JP :=
    ⟨c, (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr f.continuous⟩
  refine ⟨χ, fun z ↦ ?_, fun v z ↦ ?_⟩
  · change (f (AtA(w) z) : ℂ) * _ ^ (0 : ℂ) = (A z : ℂ)
    rw [Complex.cpow_zero, mul_one]
    apply congrArg ((↑) : Circle → ℂ)
    change A (Arch (Sep (AtA(w) z)).1 w) * ∏ v : S, finiteAngularCharacter v.val (b v) (FinU (Sep (AtA(w) z)).2 v) = A z
    simp
  · change (f (AtF(v) z) : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
    apply congrArg ((↑) : Circle → ℂ)
    change A (Arch (Sep (AtF(v) z)).1 w) *
      ∏ u : S, finiteAngularCharacter u.val (b u) (FinU (Sep (AtF(v) z)).2 u) = _
    simp only [ContinuousMulEquiv.apply_symm_apply, map_one, Pi.one_apply, one_mul]
    rw [Finset.prod_eq_single v]
    · simp
    · intro u _ huv
      simp [Pi.mulSingle, huv]
    · simp

private def fieldUnitPhase (w : InfinitePlace F) : Fˣ →* Circle :=
  complexUnitPhase.toMonoidHom.comp (Units.map w.embedding.toMonoidHom)

private theorem complexPlacePhase_diagonal (w : InfinitePlace F) (x : Fˣ) :
    complexPlacePhase w (Units.map (algebraMap F w.Completion).toMonoidHom x) = fieldUnitPhase w x := by
  apply congrArg complexUnitPhase
  apply Units.ext
  change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x.val) = w.embedding x.val
  rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbedding_coe]
  rfl

/-- For principal finite places, the fourth angular power at one infinite place descends to
the idèle quotient when every global unit has fourth power one. Each chosen prime generator
is a normalized local uniformizer with the inverse angular value, and the finite character
is trivial on the local integer units. -/
theorem exists_sLocal_fourthAngularCharacter (w : InfinitePlace F) (π : S → 𝓞 F)
    (hπ : ∀ v : S, v.val.asIdeal = Ideal.span {π v}) (hu : ∀ u : (𝓞 F)ˣ, u ^ 4 = 1) :
    ∃ χ : PontryaginDual JP,
      (∀ z : w.Completionˣ, sLocalInfiniteRestriction w (unitChart(χ)) z =
        (InfinitePlace.Completion.extensionEmbedding w z.val /
          (‖InfinitePlace.Completion.extensionEmbedding w z.val‖ : ℂ)) ^ 4) ∧
      ∀ v : S, (∀ t ∈ (v.val.adicCompletionIntegers F).units,
        sLocalFiniteRestriction v (unitChart(χ)) t = 1) ∧
        ∃ p : (v.val.adicCompletion F)ˣ,
          p.val = algebraMap F (v.val.adicCompletion F) (π v : F) ∧
          ‖p.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ ∧
          sLocalFiniteRestriction v (unitChart(χ)) p =
            ((w.embedding (π v : F) / (‖w.embedding (π v : F)‖ : ℂ)) ^ 4)⁻¹ := by
  classical
  let A := complexPlacePhase w ^ 4
  let G := fieldUnitPhase w ^ 4
  let P (v : S) : Fˣ := Units.mk0 (π v : F)
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (primeGenerator_ne_zero v.val _ (hπ v)))
  let b (v : S) := (G (P v))⁻¹
  have hdiag (x : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) :
      A (Arch (Sep (sUnitEmbedding F S x)).1 w) *
        ∏ v : S, finiteAngularCharacter v.val (b v) (FinU (Sep (sUnitEmbedding F S x)).2 v) = 1 := by
    let X : Fˣ := Units.map ((S : Set (HeightOneSpectrum (𝓞 F))).integer F).val.toMonoidHom x
    let ord (v : S) := -WithZero.log (v.val.valuation F (x.val : F))
    obtain ⟨u, he⟩ := sUnit_exists_eq_unit_mul_prod_primeGenerator_zpow F S π hπ x
    let U := Units.map (algebraMap (𝓞 F) F).toMonoidHom
    have hX : X = U u * ∏ v : S, P v ^ ord v := by
      apply Units.ext
      change (x.val : F) = algebraMap (𝓞 F) F (u : 𝓞 F) * (Units.coeHom F) (∏ v : S, P v ^ ord v)
      rw [map_prod]
      simpa only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, P, ord, Units.val_mk0] using he
    have hgu : G (U u) = 1 := by
      change fieldUnitPhase w (U u) ^ 4 = 1
      rw [← map_pow, ← map_pow, hu, map_one, map_one]
    have ha : A (Arch (Sep (sUnitEmbedding F S x)).1 w) = G X := by
      change complexPlacePhase w (Units.map (algebraMap F w.Completion).toMonoidHom X) ^ 4 =
        fieldUnitPhase w X ^ 4
      rw [complexPlacePhase_diagonal]
    have hf (v : S) :
        finiteAngularCharacter v.val (b v) (FinU (Sep (sUnitEmbedding F S x)).2 v) = (b v) ^ ord v := by
      change (b v) ^ (finiteOrderCharacter v.val _).toAdd = _
      rw [finiteOrderCharacter_apply]
      change (b v) ^ (-WithZero.log (Valued.v ((x.val : F) : v.val.adicCompletion F))) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simp_rw [ha, hf, hX, map_mul, map_prod, hgu, one_mul, map_zpow]
    simp only [b, inv_zpow, Finset.prod_inv_distrib, mul_inv_cancel]
  obtain ⟨χ, hA, hfin⟩ := angular_localProduct_exists w A b hdiag
  refine ⟨χ, fun z ↦ (hA z).trans ?_, fun v ↦ ⟨?_, ?_⟩⟩
  · rfl
  · intro t ht
    rw [hfin]
    have hv := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ht
    change (((b v) ^ (finiteOrderCharacter v.val t).toAdd : Circle) : ℂ) = 1
    rw [finiteOrderCharacter_apply, hv, WithZero.log_one, neg_zero, zpow_zero, Circle.coe_one]
  · let p := Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom (P v)
    have hp : Valued.v p.val = WithZero.exp (-1 : ℤ) := by
      change Valued.v ((π v : F) : v.val.adicCompletion F) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (valuation_primeGenerator F v.val v.val _ (hπ v)).trans (ite_eq_left rfl)
    refine ⟨p, rfl, ?_, ?_⟩
    · rw [FinitePlace.norm_def, hp, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
      simp
    · rw [hfin]
      change (((b v) ^ (finiteOrderCharacter v.val p).toAdd : Circle) : ℂ) = _
      rw [finiteOrderCharacter_apply, hp]
      simp only [WithZero.log_exp, neg_neg, zpow_one, b, Circle.coe_inv, G, MonoidHom.pow_apply, Circle.coe_pow]
      rfl

/-- Paper: Lemma 3.1.2.2, p. 121. A unitary S-idèle quotient character extends to a
unitary global Hecke character unramified outside its finite stage.
Deviation: Radial normalization provides a unitary extension of the given unitary restriction. -/
theorem exists_unitary_unramifiedOutside_extension (χ : PontryaginDual JP) :
    ∃ ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      ∃ hψ : (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ ∈ unramifiedOutside F S,
        sIdeleRestriction F S ⟨_, hψ⟩ = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ := by
  let i : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨c, hc⟩ := sIdeleRestriction_surjective F S (i.comp χ)
  let p : IdeleClassGroup (𝓞 F) F →* ℂˣ := c.val.toMonoidHom.toHomUnits
  let ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F) :=
    ⟨complexUnitPhase.toMonoidHom.comp p, by
      apply Continuous.subtype_mk
      exact c.val.continuous.div (Complex.continuous_ofReal.comp c.val.continuous.norm)
        (fun x ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit x).map c.val).ne_zero))⟩
  have hp (x : IdeleClassGroup (𝓞 F) F) : (ψ x : ℂ) = c.val x / (‖c.val x‖ : ℂ) := rfl
  have hψ : i.comp ψ ∈ unramifiedOutside F S := by
    apply (mem_unramifiedOutside_iff F S _).mpr
    intro v hv u
    let x := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
    have hu : c.val x = 1 := (mem_unramifiedOutside_iff F S _).mp c.property v hv u
    change (ψ x : ℂ) = 1
    rw [hp, hu]
    simp
  refine ⟨ψ, hψ, ?_⟩
  ext1 x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have h := DFunLike.congr_fun hc (QuotientGroup.mk g)
  rw [sIdeleRestriction_mk] at h ⊢
  change (ψ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) = (χ (QuotientGroup.mk g) : ℂ)
  rw [hp]
  change c.val (QuotientGroup.mk (sIdeleInsertion F S g)) = (χ (QuotientGroup.mk g) : ℂ) at h
  rw [h]
  simp

end RiemannMasullo
