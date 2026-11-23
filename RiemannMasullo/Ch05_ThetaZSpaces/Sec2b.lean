module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import RiemannMasullo.ForMathlib.Topology.ContinuousMap.Sigma

import all RiemannMasullo.AppC_LCTVS.Sec1

import all RiemannMasullo.AppC_LCTVS.Sec1

/-! # Homogeneous theta spaces and Fourier descent

Masullo, §5.2.2–5.2.4, pp. 232–239. Every S-local space includes all archimedean places.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

set_option quotPrecheck false

section MeromorphicComponents

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ) (hm : Continuous m) (ω : PontryaginDual m.ker)

local notation "Ωω(" χ ")" => {c : QuasiCharacter G // ∀ g : m.ker, c g.val = (χ g : ℂ)}

/-- Paper: (5.2.2.1), p. 232.
Twisting a quasi-character by a complex power of the norm preserves its norm-one restriction. -/
theorem quasiCharacterNormTwist_mem_component (c : Ωω(ω)) (z : ℂ) :
    ∀ g : m.ker, quasiCharacterNormTwist m hm c.val z g.val = (ω g : ℂ) := by
  intro g
  change c.val g.val * ((((m g.val : ℝ≥0) : ℝ) : ℂ)) ^ z = _
  rw [MonoidHom.mem_ker.mp g.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  exact c.property g

/-- Paper: (5.2.2.2), p. 232.
The meromorphic space on a component uses the pole bounds restricted to that component.
Its topology is compact convergence on the component's regular locus. -/
def meromorphicNormOneComponent (orderBound : QuasiCharacter G → WithTop ℤ) :
    Submodule ℂ C({c : Ωω(ω) // 0 ≤ orderBound c.val}, ℂ) :=
  meromorphicWithPoleBound (X := Ωω(ω))
    (fun c z ↦ ⟨quasiCharacterNormTwist m hm c.val z,
      quasiCharacterNormTwist_mem_component m hm ω c z⟩)
    (fun c ↦ orderBound c.val)

/-- Restriction and gluing for meromorphic functions on a disjoint open partition
preserved by the charts. The pole bound need not make the regular locus open. -/
private theorem meromorphicWithPoleBound_equiv_openPartition {X I : Type*} [TopologicalSpace X]
    (chart : X → ℂ → X) (b : X → WithTop ℤ) (U : I → Set X)
    (ho : ∀ i, IsOpen (U i)) (hu : ∀ x, ∃! i, x ∈ U i)
    (ht : ∀ i (x : U i) z, chart x z ∈ U i) :
    let V := fun i ↦ meromorphicWithPoleBound (X := U i)
      (fun x z ↦ ⟨chart x z, ht i x z⟩) (fun x ↦ b x.val)
    ∃ e : ↥(meromorphicWithPoleBound chart b) ≃L[ℂ] (∀ i, ↥(V i)),
      ∀ f i x, (e f i).val x = f.val ⟨x.val.val, x.property⟩ := by
  classical
  intro V
  let M := meromorphicWithPoleBound chart b
  let R := {x : X // 0 ≤ b x}
  let S := fun i ↦ {x : U i // 0 ≤ b x.val}
  let inc (i) : C(S i, R) := ⟨fun x ↦ ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let idx (x : X) := (hu x).exists.choose
  have hidx (x : X) : x ∈ U (idx x) := (hu x).exists.choose_spec
  -- The regular locus itself is the topological sum of its pieces.
  let forget (p : Σ i, S i) : R := inc p.1 p.2
  have bij : Bijective forget := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      have he : x.val.val = y.val.val := congrArg Subtype.val h
      have hij := (hu x.val.val).unique x.val.property (he ▸ y.val.property)
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext (Subtype.ext he))
    · intro x
      exact ⟨⟨idx x, ⟨⟨x, hidx x⟩, x.property⟩⟩, rfl⟩
  let D : (Σ i, S i) ≃ₜ R := (Equiv.ofBijective forget bij).toHomeomorphOfContinuousOpen
    (continuous_sigma fun i ↦ (inc i).continuous)
    (isOpenMap_sigma.mpr fun i ↦ (ho i).isOpenMap_subtype_val.restrictPreimage {x | 0 ≤ b x})
  let res (f : M) (i : I) : V i := ⟨f.val.comp (inc i), by
    obtain ⟨Z, hreg, hchart⟩ := f.property
    exact ⟨fun x ↦ Z x.val, fun x ↦ hreg (inc i x), fun x ↦ hchart x.val⟩⟩
  let onSum (f : ∀ i, V i) : C((Σ i, S i), ℂ) :=
    ⟨fun p ↦ (f p.1).val p.2, continuous_sigma fun i ↦ (f i).val.continuous⟩
  let assemble (f : ∀ i, V i) := (onSum f).comp (D.symm : C(R, (Σ i, S i)))
  have hpart (f : ∀ i, V i) (i : I) (x : S i) : assemble f (inc i x) = (f i).val x := by
    change onSum f (D.symm (D ⟨i, x⟩)) = _
    rw [D.symm_apply_apply]
    rfl
  let inv (f : ∀ i, V i) : M := ⟨assemble f, by
    -- Choose one continuation per piece. At any center, the entire germ stays
    -- in that piece, so the glued continuation inherits exactly the same order.
    choose Z hreg hchart using fun i ↦ (f i).property
    let glue (x : X) := Z (idx x) ⟨x, hidx x⟩
    have hg (i : I) (x : U i) : glue x.val = Z i x := by
      rcases x with ⟨x, hx⟩
      obtain rfl : i = idx x := (hu x).unique hx (hidx x)
      rfl
    refine ⟨glue, fun x ↦ ?_, fun x ↦ ?_⟩
    · let y : S (idx x.val) := ⟨⟨x.val, hidx x.val⟩, x.property⟩
      exact (hg _ y.val).trans ((hreg _ y).trans (hpart f _ y).symm)
    · let i := idx x
      let y : U i := ⟨x, hidx x⟩
      have he : (fun z ↦ glue (chart x z)) = fun z ↦ Z i ⟨chart x z, ht i y z⟩ :=
        funext fun z ↦ hg i ⟨chart x z, ht i y z⟩
      dsimp only
      rw [he]
      exact hchart i y⟩
  refine ⟨{ toFun := res
            invFun := inv
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ _ ↦ rfl⟩
  · intro f
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    obtain ⟨⟨i, y⟩, rfl⟩ := bij.surjective x
    exact hpart (res f) i y
  · intro f
    funext i
    exact Subtype.ext (ContinuousMap.ext (hpart f i))
  · exact continuous_pi fun i ↦ ((ContinuousMap.continuous_precomp (inc i)).comp
      continuous_subtype_val).subtype_mk _
  · have hsum : Continuous onSum := continuous_continuousMap_sigma_of_components _ fun i ↦
      show Continuous (fun f : ∀ i, V i ↦ (f i).val) from
        continuous_subtype_val.comp (continuous_apply i)
    exact ((ContinuousMap.continuous_precomp _).comp hsum).subtype_mk _


/-- Paper: (5.2.2.2), p. 232.
Restriction to the norm-one components identifies the meromorphic space with the product
of its component spaces, with their compact-convergence topologies.
Deviation: The two idelic instances are expressed by the common norm-chart statement.
The formula on regular values specifies the restriction map. -/
theorem meromorphicWithPoleBound_equiv_components [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (hproper : IsProperMap m) (hn : ∃ g, m g ≠ 1)
    (orderBound : QuasiCharacter G → WithTop ℤ) :
    ∃ e : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) orderBound) ≃L[ℂ]
        (∀ χ : PontryaginDual m.ker, ↥(meromorphicNormOneComponent m hm χ orderBound)),
      ∀ f χ c, (e f χ).val c = f.val ⟨c.val.val, c.property⟩ := by
  let U (χ : PontryaginDual m.ker) : Set (QuasiCharacter G) :=
    {c | ∀ g : m.ker, c g.val = (χ g : ℂ)}
  apply meromorphicWithPoleBound_equiv_openPartition (quasiCharacterNormTwist m hm) orderBound U
    _ _ (quasiCharacterNormTwist_mem_component m hm)
  · intro χ
    apply isOpen_iff_mem_nhds.mpr
    intro c hc
    obtain ⟨e, he, -, htwist⟩ := hasNormTwistCharts_of_proper m hproper hn c
    filter_upwards [e.open_source.mem_nhds he] with d hd
    intro g
    have h := htwist (e d) (e.map_source hd) g.val
    simp only [e.left_inv hd, show m g.val = 1 from g.property, Units.val_one, NNReal.coe_one,
      Complex.ofReal_one, Complex.one_cpow, mul_one] at h
    exact h.trans (hc g)
  · intro c
    obtain ⟨χ, hχ⟩ := (range_normOneRestriction m hproper hn ▸
      (Set.mem_range_self c : normOneRestriction m c ∈ Set.range (normOneRestriction m)))
    refine ⟨χ, fun g ↦ (DFunLike.congr_fun hχ g).symm, ?_⟩
    intro ψ hψ
    exact ContinuousMonoidHom.ext fun g ↦
      Circle.ext ((hψ g).symm.trans (DFunLike.congr_fun hχ g).symm)

end MeromorphicComponents

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

section StructureTheorem

-- TODO(paper-gap): Footnotes 4–6 on pp. 233–235 request revisions or flag unfinished
-- work. The proof invokes a descended stage projection through "(??)" on p. 234.
-- Equation (5.2.3.4) also omits the local Haar masses; see ERRATA I96.

/-- Paper: Theorem 5.2.3.1, p. 233.
A norm-one character is unramified outside S if it extends to an idelic quasi-character
unramified outside S. Norm twists are trivial on every local integer unit. -/
def NormOneCharacterUnramifiedOutside (ω : PontryaginDual C₁)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∃ c : unramifiedOutside F S, ∀ x : C₁, c.val x.val = (ω x : ℂ)

/-- Paper: Remark 5.2.3.3, p. 236.
Unramifiedness is equivalent to unique descent to the norm-one S-idele quotient.
Deviation: The descent identity is tested on norm-one ideles integral outside S. -/
theorem normOneCharacterUnramifiedOutside_iff (ω : PontryaginDual C₁) :
    NormOneCharacterUnramifiedOutside (F := F) ω S ↔
      ∃! χ : PontryaginDual (J₁(S)),
        ∀ (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S)),
          let g := integralIdeleInsertion F S u
          x.val = QuotientGroup.mk g →
          y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom g) →
          χ y = ω x := by sorry

variable (S) in
/-- Paper: Theorem 5.2.3.1, p. 233.
The descended S-local character is determined on the norm-one S-idele classes. -/
def sLocalNormOneCharacter (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) : PontryaginDual (J₁(S)) :=
  ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp hω).exists.choose

/-- Paper: Theorem 5.2.3.1, p. 233.
The descended character agrees with the global character on representatives. -/
theorem sLocalNormOneCharacter_apply (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S))
    (hx : x.val = QuotientGroup.mk (integralIdeleInsertion F S u))
    (hy : y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom
      (integralIdeleInsertion F S u))) :
    sLocalNormOneCharacter (F := F) S ω hω y = ω x :=
  ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp hω).exists.choose_spec
    u x y hx hy

/-- Paper: Remark 5.2.3.3, p. 236.
The descended character agrees on norm-one classes with the S-idelic restriction
of any unramified extension from §3.1.2. -/
theorem sLocalNormOneCharacter_eq_sIdeleRestriction
    (ω : PontryaginDual C₁) (c : unramifiedOutside F S)
    (hc : ∀ x : C₁, c.val x.val = (ω x : ℂ)) (y : J₁(S)) :
    (sLocalNormOneCharacter (F := F) S ω ⟨c, hc⟩ y : ℂ) = sIdeleRestriction F S c y.val := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
  -- Insert ones off S to lift this representative to both norm-one groups.
  let a := sIdeleInsertion F S g
  have ha : a ∈ Set.range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S a).2
    intro v hv
    have hi : a⁻¹ = sIdeleInsertion F S g⁻¹ := (map_inv _ _).symm
    change a.val.2 v ∈ _ ∧ (a⁻¹).val.2 v ∈ _
    rw [hi, (sIdeleInsertion_apply F S g).2.2 v hv, (sIdeleInsertion_apply F S g⁻¹).2.2 v hv]
    exact ⟨one_mem _, one_mem _⟩
  obtain ⟨u, hu⟩ := ha
  have hp : Units.map (adeleProjection F S).toMonoidHom a = g :=
    Units.ext (Prod.ext (sIdeleInsertion_apply F S g).1
      (funext (sIdeleInsertion_apply F S g).2.1))
  have hn : ideleNorm F a = 1 := by
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, hg]
    exact y.property
  let x : C₁ := ⟨QuotientGroup.mk a, hn⟩
  have hdesc := ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp
    ⟨c, hc⟩).exists.choose_spec u x y (by rw [hu]) (by rw [hu, hp, hg])
  rw [← hg, sIdeleRestriction_mk]
  exact (congrArg (fun t : Circle ↦ (t : ℂ)) hdesc).trans (hc x).symm

/-- Paper: Theorem 5.2.3.1, p. 233.
Unramifiedness outside S implies unramifiedness outside every larger set of places. -/
theorem NormOneCharacterUnramifiedOutside.mono {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    NormOneCharacterUnramifiedOutside (F := F) ω T := by
  obtain ⟨c, hc⟩ := hω
  exact ⟨⟨c.val, fun v hv ↦ c.property v fun h ↦ hv (hST h)⟩, hc⟩

variable {ω : PontryaginDual (ideleClassNorm F).ker}

local notation "ωₛ(" S ", " h ")" => sLocalNormOneCharacter (F := F) S ω h

/-- Extend a representative of a norm-one S-class by one. Its projections to S and T
represent classes on which the two descended characters agree. -/
private theorem sLocalHomogeneousThetaTransition_preserves_kernel_lift
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) (a : J₁(S)) :
    ∃ (u : (integralAdelesOutside F S)ˣ) (b : J₁(T)),
      a.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom
        (integralIdeleInsertion F S u)) ∧
      b.val = QuotientGroup.mk (Units.map (adeleProjection F T).toMonoidHom
        (integralIdeleInsertion F S u)) ∧
      ωₛ(S, hω) a = ωₛ(T, hω.mono hST) b := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective a.val
  let j := sIdeleInsertion F S g
  let gT := Units.map (adeleProjection F T).toMonoidHom j
  obtain ⟨hinf, hin, hout⟩ := sIdeleInsertion_apply F S g
  have hS : Units.map (adeleProjection F S).toMonoidHom j = g :=
    Units.ext (Prod.ext hinf (funext hin))
  have hTj : sIdeleInsertion F T gT = j := by
    obtain ⟨hinf', hin', hout'⟩ := sIdeleInsertion_apply F T gT
    apply Units.ext
    refine Prod.ext hinf' ?_
    apply RestrictedProduct.ext
    intro v
    by_cases hv : v ∈ T
    · exact hin' ⟨v, hv⟩
    · exact (hout' v hv).trans (hout v (fun h ↦ hv (hST h))).symm
  have hn : ideleNorm F j = 1 := by
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, hg]
    exact a.property
  let x : C₁ := ⟨QuotientGroup.mk j, hn⟩
  let b : J₁(T) := ⟨QuotientGroup.mk gT, (ideleNorm_sIdeleInsertion F T gT).symm.trans
    ((congrArg (ideleNorm F) hTj).trans hn)⟩
  have hj : j ∈ Set.range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S j).2
    intro v hv
    have hi : j⁻¹.val.2 v = 1 := by
      change ((sIdeleInsertion F S g)⁻¹).val.2 v = 1
      rw [← map_inv]
      exact (sIdeleInsertion_apply F S g⁻¹).2.2 v hv
    exact ⟨(hout v hv) ▸ (v.adicCompletionIntegers F).one_mem,
      hi ▸ (v.adicCompletionIntegers F).one_mem⟩
  obtain ⟨uT, huT⟩ := (integralIdeleInsertion_exhaustive F).1 hST hj
  obtain ⟨u, hu⟩ := hj
  have ha : a.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom j) := by
    rw [hS, hg]
  refine ⟨u, b, ?_, ?_, ?_⟩
  · simpa only [hu] using ha
  · simp only [hu]; rfl
  · exact (sLocalNormOneCharacter_apply ω hω u x a (by rw [hu]) (by simpa only [hu] using ha)).trans
      (sLocalNormOneCharacter_apply ω (hω.mono hST) uT x b (by rw [huT]) (by rw [huT])).symm

/-- Paper: (5.2.3.1), p. 233.
The stage map of test functions preserves the homogeneous theta kernels. -/
theorem sLocalHomogeneousThetaTransition_preserves_kernel
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    Kₛω(S, ωₛ(S, hω)) ≤ (Kₛω(T, ωₛ(T, hT))).comap
      (sAdeleSchwartzTransition F hST) := by
  intro hT
  let ρ (U : Finset (HeightOneSpectrum (𝓞 F))) :=
    (existsUnique_sLocalThetaAction (F := F) (S := U)).exists.choose
  have action (U : Finset (HeightOneSpectrum (𝓞 F))) (g : (SAdeleRing F U)ˣ) (k : ℬₛ(U))
      (a : SIdeleQuotient F U) (ha : a = QuotientGroup.mk g) :
      ρ U a (Submodule.Quotient.mk k) = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g k) := by
    subst a
    unfold ρ
    with_reducible exact (existsUnique_sLocalThetaAction (F := F) (S := U)).exists.choose_spec.2 g k
  let rel (U : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (J₁(U)))
      (p : J₁(U) × Θₛ(U)) := p.2 - star (χ p.1 : ℂ) • ρ U p.1.val p.2
  let D (U : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (J₁(U))) :=
    (Submodule.span ℂ (Set.range (rel U χ))).topologicalClosure
  -- In the coinvariant description, the kernel is the preimage of the closed relation span.
  have hmem (U : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (J₁(U))) (f : ℬₛ(U)) :
      f ∈ Kₛω(U, χ) ↔ (Kₛ(U)).mkQ f ∈ D U χ := by
    have h : ∃ e : SLocalHomogeneousThetaSpace F U χ ≃L[ℂ] (Θₛ(U) ⧸ D U χ),
        ∀ k : ℬₛ(U), e (Submodule.Quotient.mk k) = (D U χ).mkQ ((Kₛ(U)).mkQ k) := by
      unfold D rel ρ
      with_reducible exact sLocalHomogeneousThetaSpace_equiv_coinvariants (F := F) (S := U) χ
    refine h.elim fun e he ↦ ?_
    have he' := congrArg (fun z : Θₛ(U) ⧸ D U χ ↦ z = 0) (he f)
    have hz := ContinuousLinearEquiv.map_eq_zero_iff e (x := Submodule.Quotient.mk f)
    exact (Submodule.Quotient.mk_eq_zero (Kₛω(U, χ))).symm.trans
      (hz.symm.trans (he'.to_iff.trans (Submodule.Quotient.mk_eq_zero (D U χ))))
  let π := sLocalThetaTransition (F := F) hST
  have hmap : D S (ωₛ(S, hω)) ≤ (D T (ωₛ(T, hT))).comap π := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, y⟩, rfl⟩
      refine (Submodule.Quotient.mk_surjective (Kₛ(S)) y).elim fun f hy ↦ ?_
      rw [← hy]
      have lift := sLocalHomogeneousThetaTransition_preserves_kernel_lift
        (F := F) (ω := ω) (S := S) (T := T) hω hST a
      refine lift.elim fun u hu ↦ hu.elim fun b hb ↦ ?_
      let j := integralIdeleInsertion F S u
      let gS := Units.map (adeleProjection F S).toMonoidHom j
      let gT := Units.map (adeleProjection F T).toMonoidHom j
      let fT := sAdeleSchwartzTransition F hST f
      have hρS := action S gS f a.val hb.1
      have hρT := action T gT fT b.val hb.2.1
      let yS : Θₛ(S) := Submodule.Quotient.mk f
      let yT : Θₛ(T) := Submodule.Quotient.mk fT
      -- The ordinary transition intertwines translations by this common representative.
      have heq : π (ρ S a.val yS) = ρ T b.val yT :=
        (congrArg π hρS).trans ((sLocalThetaTransition_equivariant hST u f).trans hρT.symm)
      have hπ : π yS = yT := by
        unfold π yS yT fT sLocalThetaTransition
        exact Submodule.mapQ_apply _ _ _ f
      have hχ := congrArg (fun z : Circle ↦ star (z : ℂ)) hb.2.2
      have hs := congrArg₂ (fun (c : ℂ) (z : Θₛ(T)) ↦ c • z) hχ heq
      have hrel := (map_sub π yS (star (ωₛ(S, hω) a : ℂ) • ρ S a.val yS)).trans
        (congrArg₂ (fun v w : Θₛ(T) ↦ v - w) hπ ((map_smul π _ _).trans hs))
      have he : π (rel S (ωₛ(S, hω)) (a, yS)) = rel T (ωₛ(T, hT)) (b, yT) := by
        with_reducible exact hrel
      have hm : rel T (ωₛ(T, hT)) (b, yT) ∈ D T (ωₛ(T, hT)) :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self (b, yT)))
      have h := (congrArg (fun z ↦ z ∈ D T (ωₛ(T, hT))) he).mpr hm
      apply Submodule.mem_comap.mpr
      with_reducible exact h
    · have hc : IsClosed (D T (ωₛ(T, hT)) : Set Θₛ(T)) :=
        (Submodule.span ℂ (Set.range (rel T (ωₛ(T, hT))))).isClosed_topologicalClosure
      exact hc.preimage (sLocalThetaTransition_isClosedEmbedding (F := F) hST).continuous
  intro f hf
  exact (hmem T (ωₛ(T, hT)) _).mpr (hmap ((hmem S (ωₛ(S, hω)) f).mp hf))

/-- Paper: (5.2.3.1), p. 233.
The homogeneous theta transition is induced by adjoining integer indicators. -/
def sLocalHomogeneousThetaTransition (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (hST : S ⊆ T) : Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ]
      Θₛω(T, ωₛ(T, NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST)) :=
  let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
  (Kₛω(S, ωₛ(S, hω))).mapQ (Kₛω(T, ωₛ(T, hT))) (sAdeleSchwartzTransition F hST)
    (sLocalHomogeneousThetaTransition_preserves_kernel (F := F) (ω := ω) hω hST)

/-- Paper: (5.2.3.1), p. 233.
The transition is the unique linear map induced on homogeneous theta classes
by the test function transition. -/
theorem sLocalHomogeneousThetaTransition_spec
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    let descends := fun π : Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ] Θₛω(T, ωₛ(T, hT)) ↦
      π.comp (Kₛω(S, ωₛ(S, hω))).mkQ =
        (Kₛω(T, ωₛ(T, hT))).mkQ.comp (sAdeleSchwartzTransition F hST)
    descends (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) ∧
      ∀ π, descends π → π = sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST := by
  intro hT descends
  have h : descends (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) :=
    Submodule.mapQ_mkQ _ _ _
      (h := sLocalHomogeneousThetaTransition_preserves_kernel (F := F) (ω := ω) hω hST)
  exact ⟨h, fun π hπ ↦ Submodule.linearMap_qext _ (Eq.trans hπ (Eq.symm h))⟩

/-- Paper: Theorem 5.2.3.1(1), p. 233.
Each homogeneous stage is embedded as a closed subspace of a larger stage. -/
theorem sLocalHomogeneousThetaTransition_isClosedEmbedding
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) := by sorry

/-- Paper: Theorem 5.2.3.1(1), p. 233.
The S-idele quotient acts jointly continuously on each homogeneous theta quotient.
Translation by a representative induces the action on its test-function class. -/
theorem existsUnique_sLocalHomogeneousThetaAction (χ : PontryaginDual (J₁(S))) :
    ∃! ρ : Jₛ(S) →* (Θₛω(S, χ) →L[ℂ] Θₛω(S, χ)),
      Continuous (fun p : Jₛ(S) × Θₛω(S, χ) ↦ ρ p.1 p.2) ∧
      ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)),
        ρ (QuotientGroup.mk g) ((Kₛω(S, χ)).mkQ f) =
          (Kₛω(S, χ)).mkQ (schwartzBruhatUnitTranslate g f) := by sorry

/-- Paper: Theorem 5.2.3.1(1), p. 233.
The homogeneous transition intertwines the descended actions on theta classes.
Deviation: The acting class is represented by an idele integral and invertible outside S. -/
theorem sLocalHomogeneousThetaTransition_equivariant
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (x : Θₛω(S, ωₛ(S, hω))) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    let ρS := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) (ωₛ(S, hω))).exists.choose
    let ρT := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) (ωₛ(T, hT))).exists.choose
    let π := sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    π (ρS (QuotientGroup.mk gS) x) = ρT (QuotientGroup.mk gT) (π x) := by sorry

/-- Paper: Theorem 5.2.3.1(1), pp. 233–234.
Insertion of test functions into the adeles preserves the homogeneous theta kernels. -/
theorem sLocalHomogeneousThetaToGlobal_preserves_kernel
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Kₛω(S, ωₛ(S, hω)) ≤ (K𝔽ω(ω)).comap (sAdeleSchwartzToGlobal F S) := by sorry

/-- Paper: (5.2.3.2), p. 233.
The stage insertion into the global homogeneous quotient is induced by extension
of test functions with integer indicators outside S. -/
def sLocalHomogeneousThetaToGlobal (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ] Θ𝔽ω(ω) :=
  (Kₛω(S, ωₛ(S, hω))).mapQ (K𝔽ω(ω)) (sAdeleSchwartzToGlobal F S)
    (sLocalHomogeneousThetaToGlobal_preserves_kernel (F := F) (ω := ω) hω)

/-- Paper: (5.2.3.2), p. 233.
The global homogeneous insertion agrees with test function insertion on representatives. -/
theorem sLocalHomogeneousThetaToGlobal_mk (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (f : ℬₛ(S)) :
    sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω ((Kₛω(S, ωₛ(S, hω))).mkQ f) =
      (K𝔽ω(ω)).mkQ (sAdeleSchwartzToGlobal F S f) :=
  rfl

/-- Paper: Theorem 5.2.3.1(1), pp. 233–234.
The stages form a strict system under the transition maps and identify the global
homogeneous space with its locally convex inductive limit.
Deviation: The compatible closed embeddings and exhaustion realize the algebraic
colimit inside the global space. The topology is specified by the final topology. -/
theorem sLocalHomogeneousTheta_inductiveLimit (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    let I := {T : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ T}
    let h := fun T : I ↦ NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property
    let i := fun T : I ↦ sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) (h T)
    (∀ T, IsClosedEmbedding (i T)) ∧
    (∀ (T U : I) (hTU : T.val ⊆ U.val),
      (i U).comp (sLocalHomogeneousThetaTransition (F := F) (ω := ω) (h T) hTU) = i T) ∧
    (∀ x : Θ𝔽ω(ω), ∃ T y, i T y = x) ∧
    (inferInstance : TopologicalSpace Θ𝔽ω(ω)) = locallyConvexFinalTopology i := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
A Hausdorff space admits a countable locally convex inductive presentation whose
stages, with their own topologies, are nuclear Fréchet spaces. -/
def HasNuclearFrechetPresentation.{v,u} (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ (X : ℕ → Type u) (_ : ∀ k, AddCommGroup (X k)) (_ : ∀ k, Module ℂ (X k))
    (_ : ∀ k, TopologicalSpace (X k)), (∀ k, IsFrechetTVS (X k) ∧ IsNuclearTVS.{v} (X k)) ∧
      ∃ (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E), IsInjectiveLCLimit j i

/-- Paper: Theorem 5.2.3.1(2), p. 233.
A countable nuclear Fréchet presentation gives an LF presentation. -/
theorem HasNuclearFrechetPresentation.isLFSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasNuclearFrechetPresentation E) : IsLFSpace E := by
  obtain ⟨hE, X, a, m, t, hX, hlim⟩ := h
  exact ⟨hE, X, a, m, t, fun k ↦ (hX k).1, hlim⟩

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous theta quotient is a locally convex inductive limit of nuclear
Fréchet spaces. The test-function stages can be quotiented by the restricted kernel. -/
theorem globalHomogeneousThetaSpace_nuclearFrechetPresentation :
    HasNuclearFrechetPresentation Θ𝔽ω(ω) := by sorry

/-- A closed quotient of a nuclear strict LF-space has nuclear Fréchet quotient stages. -/
private theorem sLocalHomogeneousThetaSpace_nuclearFrechetPresentation_quotient.{v}
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) (hE : IsStrictLFSpace E) (hN : IsNuclearTVS.{v} E) :
    HasNuclearFrechetPresentation.{v} (E ⧸ M) := by
  obtain ⟨_, X, hmono, hFrechet, hcover, htop⟩ := hE
  let : T2Space (E ⧸ M) := inferInstance
  let i (k : ℕ) : X k →L[ℂ] E := (X k).subtypeL
  let j (k : ℕ) : X k →L[ℂ] X (k+1) :=
    (X k).subtypeL.codRestrict (X (k+1)) fun x ↦ hmono k.le_succ x.property
  have h : IsInjectiveLCLimit j i :=
    ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ by
      obtain ⟨k, hk⟩ := hcover x
      exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩, htop⟩
  have hNstage (k : ℕ) : IsNuclearTVS (X k) := isNuclearTVS_submodule hN (X k)
  let f (k : ℕ) := M.mkQL.comp (i k)
  let K (k : ℕ) := (f k).ker
  have hf (k : ℕ) (x : X k) : f (k+1) (j k x) = f k x :=
    congrArg M.mkQ (DFunLike.congr_fun (h.compatible k) x)
  let iQ (k : ℕ) : X k ⧸ K k →L[ℂ] E ⧸ M := (K k).liftQL (f k) le_rfl
  let jQ (k : ℕ) : X k ⧸ K k →L[ℂ] X (k+1) ⧸ K (k+1) :=
    (K k).liftQL ((K (k+1)).mkQL.comp (j k)) (by
      intro x hx
      change (K (k+1)).mkQ (j k x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change f (k+1) (j k x) = 0
      rwa [hf])
  have hiQ (k : ℕ) (x : X k) : iQ k ((K k).mkQ x) = f k x := rfl
  have hjQ (k : ℕ) (x : X k) : jQ k ((K k).mkQ x) = (K (k+1)).mkQ (j k x) := rfl
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} →
        Seminorm ℂ E) := ⟨h.topology_eq⟩
  have hlim : IsInjectiveLCLimit jQ iQ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      apply (LinearMap.ker_eq_bot (f := (iQ k).toLinearMap)).mp
      exact (K k).ker_liftQ_eq_bot' (f k).toLinearMap rfl
    · intro k
      ext y
      obtain ⟨x, rfl⟩ := (K k).mkQ_surjective y
      change iQ (k+1) (jQ k ((K k).mkQ x)) = iQ k ((K k).mkQ x)
      rw [hjQ, hiQ, hiQ, hf]
    · intro y
      obtain ⟨x, rfl⟩ := M.mkQ_surjective y
      obtain ⟨k, z, rfl⟩ := h.exhaustive x
      exact ⟨k, (K k).mkQ z, hiQ k z⟩
    · let : PolynormableSpace ℂ E := hP.toPolynormableSpace
      let : PolynormableSpace ℂ (E ⧸ M) := (isNuclearTVS_quotient hN M).2.1
      have hseminorms : (fun p : Seminorm ℂ (E ⧸ M) ↦
          ∀ k, Continuous (p ∘ (iQ k).toLinearMap)) =
          (fun p : Seminorm ℂ (E ⧸ M) ↦ Continuous p) := by
        funext p
        apply propext
        refine ⟨fun hp ↦ M.isQuotientMap_mkQL.continuous_iff.mpr ?_,
          fun hp k ↦ hp.comp (iQ k).continuous⟩
        apply hP.continuous_seminorm (⟨p.comp M.mkQ, fun k ↦ ?_⟩ : _)
        change Continuous (fun x : X k ↦ p (f k x))
        simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, Submodule.coe_mkQL, hiQ] using
          (hp k).comp (K k).mkQL.continuous
      change (inferInstance : TopologicalSpace (E ⧸ M)) =
        (SeminormFamily.moduleFilterBasis
          (Subtype.val : {p : Seminorm ℂ (E ⧸ M) // ∀ k, Continuous (p ∘ (iQ k).toLinearMap)} →
            Seminorm ℂ (E ⧸ M))).topology
      rw [hseminorms]
      exact (PolynormableSpace.withSeminorms ℂ (E ⧸ M)).withSeminorms_eq
  have : T2Space (E ⧸ M) := inferInstance
  refine ⟨inferInstance, fun k ↦ X k ⧸ K k, _, _, _, ?_, jQ, iQ, hlim⟩
  intro k
  have : IsClosed (K k : Set (X k)) := (f k).isClosed_ker
  let : IsTopologicalAddGroup (X k) := (hFrechet k).1
  let : T2Space (X k ⧸ K k) := inferInstance
  exact ⟨isFrechetTVS_quotient (hFrechet k) (K k) (f k).isClosed_ker,
    isNuclearTVS_quotient (hNstage k) (K k)⟩

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous theta quotient is a locally convex inductive limit of nuclear
Fréchet spaces. The test-function stages can be quotiented by the restricted kernel. -/
theorem sLocalHomogeneousThetaSpace_nuclearFrechetPresentation (χ : PontryaginDual (J₁(S))) :
    HasNuclearFrechetPresentation (Θₛω(S, χ)) := by
  exact sLocalHomogeneousThetaSpace_nuclearFrechetPresentation_quotient _
    (sLocalHomogeneousAdelicTheta_ker_isClosed χ) (sAdeleSchwartz_strictLF F S)
    (sAdeleSchwartz_nuclear F S)

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous theta space is an LF-space. -/
theorem globalHomogeneousThetaSpace_lf : IsLFSpace Θ𝔽ω(ω) := by
  have h : HasNuclearFrechetPresentation.{0} Θ𝔽ω(ω) :=
    globalHomogeneousThetaSpace_nuclearFrechetPresentation
  exact h.isLFSpace

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous theta space is an LF-space. -/
theorem sLocalHomogeneousThetaSpace_lf (χ : PontryaginDual (J₁(S))) :
    IsLFSpace (Θₛω(S, χ)) := by
  have h : HasNuclearFrechetPresentation.{0} (Θₛω(S, χ)) :=
    sLocalHomogeneousThetaSpace_nuclearFrechetPresentation χ
  exact h.isLFSpace

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is complete for its additive uniformity. -/
theorem globalHomogeneousThetaSpace_complete :
    @CompleteSpace Θ𝔽ω(ω) (IsTopologicalAddGroup.rightUniformSpace _) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is complete for its additive uniformity. -/
theorem sLocalHomogeneousThetaSpace_complete (χ : PontryaginDual (J₁(S))) :
    @CompleteSpace (Θₛω(S, χ)) (IsTopologicalAddGroup.rightUniformSpace _) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_nuclear : IsNuclearTVS Θ𝔽ω(ω) := by
  have : IsClosed (K𝔽ω(ω) : Set ℬ𝔽) := homogeneousAdelicTheta_ker_isClosed ω
  let : T2Space Θ𝔽ω(ω) := inferInstance
  exact isNuclearTVS_quotient (adeleSchwartz_nuclear (F := F)).2 (K𝔽ω(ω))

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (Θₛω(S, χ)) := by
  have : IsClosed (Kₛω(S, χ) : Set (SchwartzBruhat (Multiplicative (SAdeleRing F S)))) :=
    sLocalHomogeneousAdelicTheta_ker_isClosed χ
  let : T2Space (Θₛω(S, χ)) := inferInstance
  exact isNuclearTVS_quotient (sAdeleSchwartz_nuclear F S) (Kₛω(S, χ))

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_montel :
    BarrelledSpace ℂ Θ𝔽ω(ω) ∧ MontelSpace ℂ Θ𝔽ω(ω) := by
  have hN : IsNuclearTVS.{0} Θ𝔽ω(ω) := globalHomogeneousThetaSpace_nuclear (F := F) (ω := ω)
  let : T2Space Θ𝔽ω(ω) := hN.1
  let : PolynormableSpace ℂ Θ𝔽ω(ω) := hN.2.1
  let : UniformSpace Θ𝔽ω(ω) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽ω(ω) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Θ𝔽ω(ω) := globalHomogeneousThetaSpace_complete (F := F) (ω := ω)
  refine ⟨IsLFSpace.barrelled (E := Θ𝔽ω(ω)) (globalHomogeneousThetaSpace_lf (F := F) (ω := ω)), ⟨fun B hc hb ↦ ?_⟩⟩
  simpa only [hc.closure_eq] using isCompact_closure_of_isNuclearTVS Θ𝔽ω(ω) hN hb

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is Montel. -/
theorem sLocalHomogeneousThetaSpace_montel (χ : PontryaginDual (J₁(S))) :
    BarrelledSpace ℂ (Θₛω(S, χ)) ∧ MontelSpace ℂ (Θₛω(S, χ)) := by
  have hN : IsNuclearTVS.{0} (Θₛω(S, χ)) := sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) χ
  let : T2Space (Θₛω(S, χ)) := hN.1
  let : PolynormableSpace ℂ (Θₛω(S, χ)) := hN.2.1
  let : UniformSpace (Θₛω(S, χ)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛω(S, χ)) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (Θₛω(S, χ)) := sLocalHomogeneousThetaSpace_complete (F := F) (S := S) χ
  refine ⟨IsLFSpace.barrelled (E := (Θₛω(S, χ))) (sLocalHomogeneousThetaSpace_lf (F := F) (S := S) χ), ⟨fun B hc hb ↦ ?_⟩⟩
  simpa only [hc.closure_eq] using isCompact_closure_of_isNuclearTVS (Θₛω(S, χ)) hN hb

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is complete. -/
theorem globalHomogeneousThetaSpace_strongDual_complete :
    CompleteSpace (StrongDual ℂ Θ𝔽ω(ω)) := by
  let : CompleteSpace (StrongDual ℂ (SchwartzBruhat (Multiplicative (𝔸[F])))) :=
    (adeleSchwartz_strongDual_complete (F := F)).2
  exact completeSpace_strongDual_quotient _

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is complete. -/
theorem sLocalHomogeneousThetaSpace_strongDual_complete (χ : PontryaginDual (J₁(S))) :
    CompleteSpace (StrongDual ℂ (Θₛω(S, χ))) := by
  let : CompleteSpace (StrongDual ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F S)))) :=
    sAdeleSchwartz_strongDual_complete F S
  exact completeSpace_strongDual_quotient _

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_strongDual_nuclear :
    IsNuclearTVS (StrongDual ℂ Θ𝔽ω(ω)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_strongDual_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (StrongDual ℂ (Θₛω(S, χ))) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_strongDual_montel :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) ∧ MontelSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is Montel. -/
theorem sLocalHomogeneousThetaSpace_strongDual_montel (χ : PontryaginDual (J₁(S))) :
    BarrelledSpace ℂ (StrongDual ℂ (Θₛω(S, χ))) ∧ MontelSpace ℂ (StrongDual ℂ (Θₛω(S, χ))) := by sorry

/-- Paper: Theorem 5.2.3.1(3), p. 233.
There are continuous idempotents onto the stage images. The net of these idempotents
converges to the identity uniformly on von Neumann bounded sets. -/
theorem sLocalHomogeneousTheta_projections (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    let I := {T : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ T}
    let E := Θ𝔽ω(ω)
    let e := UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (F := E)
      {B : Set E | IsVonNBounded ℂ B}
    ∃ P : I → E →L[ℂ] E,
      (∀ T : I,
        let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property
        let i := sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hT
        (P T).toLinearMap.comp i = i ∧ LinearMap.range (P T).toLinearMap = LinearMap.range i) ∧
      Tendsto (fun T ↦ e (P T)) atTop (𝓝 (e (ContinuousLinearMap.id ℂ E))) := by sorry

end StructureTheorem

local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose
local notation "ρₛ(" S ")" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
local notation "ρ𝔽₁" => (ρ𝔽).comp (MonoidHom.ker m𝔽).subtype
local notation "ρₛ₁(" S ")" => (ρₛ(S)).comp (MonoidHom.ker (mₛ(S))).subtype
local notation "E𝔽ω(" ω ")" => actionIsotype ρ𝔽₁ ω
local notation "Eₛω(" S ", " ω ")" => actionIsotype (ρₛ₁(S)) ω

local notation "μ𝔽₁" => normOneIdeleClassTamagawaMeasure F
local notation "μₛ₁(" S ")" => sLocalNormOneQuotientMeasure F S

section IsotypicAverages

local instance ideleClassGroupMeasurableSpaceSec2b (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance normOneSIdeleQuotientMeasurableSpaceSec2b (F : Type*) [Field F]
    [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

-- TODO(paper-gap): The proof on pp. 236–237 gives no quotient-topology argument for
-- equicontinuity. Use the jointly continuous action on the theta quotient and compactness.
-- The Tamagawa averages act on their isotypes by Haar mass.

/-- Paper: Proposition 5.2.3.2(1), p. 236.
There is a unique continuous linear global Pettis average with the norm-one
Tamagawa measure and the conjugate character weight. -/
theorem existsUnique_globalThetaIsotypicAverage (ω : PontryaginDual C₁) :
    ∃! P : Θ𝔽 →L[ℂ] Θ𝔽,
      IsPettisIsotypicAverageOn μ𝔽₁ Set.univ ρ𝔽₁ ω P := by sorry

/-- Paper: Proposition 5.2.3.2(1), p. 236.
There is a unique continuous linear S-local Pettis average with the norm-one
quotient measure and the conjugate character weight. -/
theorem existsUnique_sLocalThetaIsotypicAverage (χ : PontryaginDual (J₁(S))) :
    ∃! P : Θₛ(S) →L[ℂ] Θₛ(S),
      IsPettisIsotypicAverageOn (μₛ₁(S)) Set.univ (ρₛ₁(S)) χ P := by sorry

end IsotypicAverages

local notation "P𝔽(" ω ")" => (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
local notation "Pₛ(" S ", " χ ")" =>
  (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The global average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem globalThetaIsotypicAverage_equiv (ω : PontryaginDual C₁) :
    IsClosed (E𝔽ω(ω) : Set Θ𝔽) ∧
      ∃ e : Θ𝔽ω(ω) ≃L[ℂ] E𝔽ω(ω), ∀ f : ℬ𝔽,
        (e ((K𝔽ω(ω)).mkQ f) : Θ𝔽) = P𝔽(ω) ((K𝔽).mkQ f) := by sorry

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The S-local average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem sLocalThetaIsotypicAverage_equiv (χ : PontryaginDual (J₁(S))) :
    IsClosed (Eₛω(S, χ) : Set (Θₛ(S))) ∧
      ∃ e : Θₛω(S, χ) ≃L[ℂ] Eₛω(S, χ), ∀ f : ℬₛ(S),
        (e ((Kₛω(S, χ)).mkQ f) : Θₛ(S)) = Pₛ(S, χ) ((Kₛ(S)).mkQ f) := by sorry

-- TODO(paper-gap): The global L² argument on p. 237 fails at norm zero for
-- the rational Gaussian. Apply character uniqueness on each compact norm-one fibre.

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical global map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_globalThetaToHomogeneousProduct :
    ∃ P : Θ𝔽 →L[ℂ] (∀ ω : PontryaginDual C₁, Θ𝔽ω(ω)),
      Injective P ∧ ∀ (f : ℬ𝔽) ω, P ((K𝔽).mkQ f) ω = (K𝔽ω(ω)).mkQ f := by sorry

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical S-local map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_sLocalThetaToHomogeneousProduct :
    ∃ P : Θₛ(S) →L[ℂ] (∀ χ : PontryaginDual (J₁(S)), Θₛω(S, χ)),
      Injective P ∧ ∀ (f : ℬₛ(S)) χ, P ((Kₛ(S)).mkQ f) χ = (Kₛω(S, χ)).mkQ f := by sorry

local notation "M𝔽ω(" ω ")" => meromorphicNormOneComponent m𝔽
  (isProperMap_ideleClassNorm F).continuous ω (globalIdelicOrderBound (F := F))
local notation "Mₛω(" S ", " ω ")" => meromorphicNormOneComponent (mₛ(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous ω (sLocalIdelicOrderBound (F := F) (S := S))

/-- Paper: (5.2.3.14), p. 236.
The global Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the global Mellin transform in (5.2.2.2). -/
theorem exists_globalHomogeneousThetaMellin (ω : PontryaginDual C₁) :
    ∃ Z : Θ𝔽ω(ω) →L[ℂ] ↥(M𝔽ω(ω)), Injective Z ∧
      ∀ (f : ℬ𝔽) c,
        (Z ((K𝔽ω(ω)).mkQ f)).val c =
          (globalIdelicMellin (F := F) f).val ⟨c.val.val, c.property⟩ := by sorry

/-- Paper: (5.2.3.14), p. 236.
The S-local Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the S-local Mellin transform in (5.2.2.2). -/
theorem exists_sLocalHomogeneousThetaMellin (χ : PontryaginDual (J₁(S))) :
    ∃ Z : Θₛω(S, χ) →L[ℂ] ↥(Mₛω(S, χ)), Injective Z ∧
      ∀ (f : ℬₛ(S)) c,
        (Z ((Kₛω(S, χ)).mkQ f)).val c =
          (sLocalIdelicMellin (F := F) (S := S) f).val ⟨c.val.val, c.property⟩ := by sorry

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

local notation "unitAtₛ(" S ")" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))

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

/-- Paper: Remark 5.2.3.5, p. 238.
On each component the global Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the norm-one Haar mass. -/
theorem globalThetaMellin_isotypicAverage (ω : PontryaginDual C₁) (x : Θ𝔽)
    (c : {c : QuasiCharacter C𝔽 // 0 ≤ globalIdelicOrderBound c})
    (hc : ∀ g : C₁, c.val g.val = (ω g : ℂ)) :
    (globalThetaMellin (F := F) (P𝔽(ω) x)).val c =
      ((μ𝔽₁).real Set.univ : ℂ) * (globalThetaMellin (F := F) x).val c := by sorry

/-- Paper: Remark 5.2.3.5, p. 238.
On each S-local component the Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the S-local norm-one Haar mass. -/
theorem sLocalThetaMellin_isotypicAverage (χ : PontryaginDual (J₁(S))) (x : Θₛ(S))
    (c : {c : QuasiCharacter (Jₛ(S)) // 0 ≤ sLocalIdelicOrderBound c})
    (hc : ∀ g : J₁(S), c.val g.val = (χ g : ℂ)) :
    (sLocalThetaMellin (F := F) (S := S) (Pₛ(S, χ) x)).val c =
      ((μₛ₁(S)).real Set.univ : ℂ) * (sLocalThetaMellin (F := F) (S := S) x).val c := by sorry

end IsotypicMellin

section Fourier

-- TODO(paper-gap): The global map is described as inversion on p. 238.
-- The identity on theta functions has a norm factor and two zero terms,
-- as in adelicTheta_riemannRoch.

/-- Paper: Theorem 5.2.4.1(1), pp. 238–239.
S-adelic Fourier transform descends to a unique continuous linear involution
on the S-local theta quotient. -/
theorem existsUnique_sLocalThetaFourier :
    ∃! e : Θₛ(S) ≃L[ℂ] Θₛ(S),
      Involutive e ∧ ∀ f : ℬₛ(S),
        e ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ (sAdeleSchwartzFourier (F := F) (S := S) f) :=
  by sorry

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Adelic Fourier transform descends to a unique continuous linear involution
on the global theta quotient.
Deviation: The descent identity is tested on global test functions, as in the proof. -/
theorem existsUnique_globalThetaFourier :
    ∃! e : Θ𝔽 ≃L[ℂ] Θ𝔽,
      Involutive e ∧ ∀ f : ℬ𝔽,
        e ((K𝔽).mkQ f) = (K𝔽).mkQ (adeleSchwartzFourier (F := F) f) :=
  by sorry

-- TODO(paper-gap): The unrestricted compatibility assertions on p. 239 fail.
-- For ℚ(i) above 2 the Fourier image of the integer indicator is half the inverse-
-- different indicator. An archimedean bump supported near 1/2 detects the difference.

set_option maxSynthPendingDepth 8 in
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
    fourierT (transition x) = transition (fourierS x) := by sorry

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
    fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x) := by sorry

/-- Paper: Theorem 5.2.4.1(1), p. 239.
S-local Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem sLocalThetaFourier_mem_isotype (χ : PontryaginDual (J₁(S))) (x : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier x ∈ Eₛω(S, χ⁻¹) ↔ x ∈ Eₛω(S, χ) := by sorry

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Global Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem globalThetaFourier_mem_isotype (ω : PontryaginDual C₁) (x : Θ𝔽) :
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier x ∈ E𝔽ω(ω⁻¹) ↔ x ∈ E𝔽ω(ω) := by sorry

end Fourier

end RiemannMasullo
