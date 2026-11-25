module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.AppA_AlgebraicNT.Sec5a_DPrimeOpenModel
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Measurable D′-sequences for the idèle class group

At the infinite places, exponentiate balls in the full mixed real and complex space. At the
finite places, use compact open subgroups of the product of integral units. Their images
under the open quotient map give a basis for the idèle class group.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F]
local notation "V∞" => mixedEmbedding.mixedSpace F
local notation "I∞" => (InfiniteAdeleRing F)ˣ
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "𝕀" => IdeleGroup (𝓞 F) F
local notation "P𝔽" => HeightOneSpectrum (𝓞 F)

private theorem exists_isOpenMap_archimedeanExp :
    ∃ f : Multiplicative V∞ →ₜ* I∞, IsOpenMap f := by
  classical
  let E := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
  let A (x : V∞) : V∞ := (fun v ↦ Real.exp (x.1 v), fun v ↦ Complex.exp (x.2 v))
  have a0 : A 0 = 1 := by ext v <;> simp [A]
  have am (x y : V∞) : A (x + y) = A x * A y := by
    apply Prod.ext
    · exact funext fun v ↦ Real.exp_add _ _
    · exact funext fun v ↦ Complex.exp_add _ _
  have ac : Continuous A :=
    (continuous_pi fun v ↦
      Real.continuous_exp.comp ((continuous_apply v).comp continuous_fst)).prodMk
        (continuous_pi fun v ↦
          Complex.continuous_exp.comp ((continuous_apply v).comp continuous_snd))
  have ao : IsOpenMap A := by
    let r : ({w : InfinitePlace F // w.IsReal} → ℝ) → ({w : InfinitePlace F // w.IsReal} → ℝ) :=
      Pi.map fun _ ↦ Real.exp
    let c : ({w : InfinitePlace F // w.IsComplex} → ℂ) →
        ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.map fun _ ↦ Complex.exp
    have hr : IsOpenMap r := IsOpenMap.piMap (fun _ ↦ Real.isOpenEmbedding_exp.isOpenMap) (by simp)
    have hc : IsOpenMap c := IsOpenMap.piMap (fun _ ↦ Complex.isOpenMap_exp) (by simp)
    exact hr.prodMap hc
  let u (x : V∞) : I∞ := ⟨E (A x), E (A (-x)),
    by rw [← map_mul, ← am, add_neg_cancel, a0, map_one],
    by rw [← map_mul, ← am, neg_add_cancel, a0, map_one]⟩
  have ec : Continuous E := continuous_infiniteAdeleRingEquivMixedSpace_symm F
  let f : Multiplicative V∞ →ₜ* I∞ :=
    { toFun := fun x ↦ u x.toAdd
      map_one' := Units.ext (by change E (A 0) = 1; rw [a0, map_one])
      map_mul' := fun x y ↦ Units.ext (by
        change E (A (x.toAdd + y.toAdd)) = E (A x.toAdd) * E (A y.toAdd)
        rw [am, map_mul])
      continuous_toFun := Units.continuous_iff.mpr ⟨(ec.comp ac).comp continuous_toAdd,
        ((ec.comp ac).comp (continuous_neg : Continuous (fun x : V∞ ↦ -x))).comp continuous_toAdd⟩ }
  refine ⟨f, fun S hS ↦ ?_⟩
  have hO : IsOpen ((fun x : Multiplicative V∞ ↦ E (A x.toAdd)) '' S) :=
    ((infiniteAdeleHomeomorphMixedSpace F).symm.isOpenMap.comp ao) _ hS
  have heq : f '' S = Units.val ⁻¹' ((fun x : Multiplicative V∞ ↦ E (A x.toAdd)) '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, Units.ext he⟩
  rw [heq]
  exact hO.preimage Units.continuous_val

/-- Every number-field idèle class group has a D′-sequence of Borel sets for its Tamagawa measure.
Reconstruction: To obtain the existence used in Appendix A.5.2 (pp. 576–578), use shrinking
neighborhoods in both the absolute value and angular coordinates at the complex places. -/
theorem exists_measurable_ideleClassDPrimeSequence :
    letI : MeasurableSpace C𝔽 := borel _
    ∃ U : ℕ → Set C𝔽, IsDPrimeSequence (ideleClassTamagawaMeasure F) U ∧
      ∀ n, MeasurableSet (U n) := by
  classical
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hcomp_v (v : P𝔽) : CompactSpace ↥((v.adicCompletionIntegers F).units) := by
    have : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
    exact isCompact_iff_compactSpace.mp
      (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr this))
  have htd_v (v : P𝔽) : TotallyDisconnectedSpace ↥((v.adicCompletionIntegers F).units) := by
    have : TotallyDisconnectedSpace (v.adicCompletion F)ˣ :=
      ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
        Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
    infer_instance
  let K := (v : P𝔽) → ↥((v.adicCompletionIntegers F).units)
  have : CompactSpace K := Pi.compactSpace
  have : TotallyDisconnectedSpace K := inferInstance
  have ho (v : P𝔽) : IsOpen ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  let emb := RestrictedProduct.structureMap (fun v : P𝔽 ↦ (v.adicCompletion F)ˣ)
    (fun v ↦ ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ)) cofinite
  have hemb : IsOpenEmbedding emb := RestrictedProduct.isOpenEmbedding_structureMap ho
  let fin : K →ₜ* (Πʳ v : P𝔽, [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]) :=
    { toFun := emb, map_one' := by ext v; rfl, map_mul' := fun x y ↦ by ext v; rfl,
      continuous_toFun := hemb.continuous }
  obtain ⟨arch, harch⟩ := exists_isOpenMap_archimedeanExp F
  let ep : I∞ ≃ₜ* ((v : InfinitePlace F) → v.Completionˣ) :=
    ContinuousMulEquiv.piUnits (M := fun v : InfinitePlace F ↦ v.Completion)
  let arch' : Multiplicative V∞ →ₜ* ((v : InfinitePlace F) → v.Completionˣ) :=
    ⟨ep.toMonoidHom.comp arch.toMonoidHom, ep.continuous.comp arch.continuous⟩
  obtain ⟨e, -⟩ := (ideleGroup_topology F).2.2.2.1
  let q : 𝕀 →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  have hq : IsOpenMap q := QuotientGroup.isOpenMap_coe
  let f := q.comp ((e.symm : _ →ₜ* _).comp (arch'.prodMap fin))
  have hf : IsOpenMap f := hq.comp (e.symm.isOpenMap.comp
    ((ep.isOpenMap.comp harch).prodMap hemb.isOpenMap))
  obtain ⟨U, hU, hopen⟩ :=
    exists_openDPrimeSequence_of_openMap_normedProd f hf (ideleClassTamagawaMeasure F)
  exact ⟨U, hU, fun n ↦ (hopen n).measurableSet⟩

end RiemannMasullo
